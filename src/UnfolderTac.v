Require Import Coq.Lists.List Coq.Bool.Bool.
Require Import ExtLib.Tactics.Consider.
Require Import MirrorShard.Expr MirrorShard.SepExpr.
Require Import MirrorShard.Prover.
Require Import MirrorShard.Tactics.
Require MirrorShard.Unfolder.
Require MirrorShard.SepHeap.

Set Implicit Arguments.
Set Strict Implicit.

Module UnfolderTac (ST : SepTheory.SepTheory)
                   (SE : SepExpr ST)
                   (SH : SepHeap.SepHeap ST SE)
                   (LEM : SepLemma.SepLemmaType ST SE)
                   (UNF : Unfolder.Unfolder ST SE SH LEM).
  Module SH_UTIL := SepHeap.SepHeapFacts ST SE SH.
  Module SE_EXT := SepExpr.SepExprFacts ST SE.

Section unfolder.
  Variable types : list type.
  Variable funcs : functions types.
  Variable preds : SE.predicates types.
  Variable prover : ProverT types.
  Variable facts : Facts prover.
  Variable hintsFwd : UNF.hintSide types.
  Variable hintsBwd : UNF.hintSide types.

  Record unfolderResult : Type :=
  { Alls : list tvar
  ; Exs  : list tvar
  ; Lhs  : SH.SHeap types
  ; Rhs  : SH.SHeap types
  ; Know : Facts prover
  }.

  Definition unfold (uvars : list tvar)
    (ql : list tvar) (lhs rhs : SH.SHeap types) : unfolderResult * bool :=
    let pre :=
      {| UNF.Vars  := ql
       ; UNF.UVars := uvars
       ; UNF.Heap  := lhs
      |}
    in
    match UNF.refineForward prover hintsFwd 10 facts pre with
      | ({| UNF.Vars := vars' ; UNF.UVars := uvars' ; UNF.Heap := lhs |}, fprog) =>
        let post :=
          {| UNF.Vars  := vars'
           ; UNF.UVars := uvars'
           ; UNF.Heap  := rhs
          |}
        in
        let facts' := Learn _ facts (SH.pures lhs) in
        match UNF.refineBackward prover hintsBwd 10 facts' post with
          | ({| UNF.Vars := vars' ; UNF.UVars := uvars' ; UNF.Heap := rhs |}, bprog) =>
            let new_vars  := skipn (length ql) vars' in
            let new_uvars := skipn (length uvars) uvars' in
            let bound := length uvars' in
            ({| Alls := new_vars
              ; Exs  := new_uvars
              ; Lhs  := lhs
              ; Rhs  := rhs
              ; Know := facts'
              |}, fprog || bprog)
        end
    end.

  Lemma WellTyped_env_app : forall ts a b c d,
    WellTyped_env a c ->
    WellTyped_env b d ->
    WellTyped_env (types := ts) (a ++ b) (c ++ d).
  Proof. clear.
    intros. unfold WellTyped_env in *. unfold typeof_env in *. subst. 
    rewrite map_app. reflexivity.
  Qed.
  Ltac t_list_length := repeat (rewrite typeof_env_length || rewrite rev_length || rewrite map_length || rewrite app_length).
  Hint Extern 1 (_ = _) => t_list_length; auto : list_length.

  Ltac env_resolution :=
    repeat (rewrite typeof_env_app || unfold typeof_env || rewrite map_app || rewrite map_rev || (f_equal; []) || assumption).

  Hypothesis prover_Correct : ProverT_correct prover funcs.
  Hypothesis hintsFwd_Correct : UNF.hintSideD funcs preds hintsFwd.
  Hypothesis hintsBwd_Correct : UNF.hintSideD funcs preds hintsBwd.

  Lemma ApplyUnfold_with_eq' : 
    forall (var_env meta_env : env types),
    Valid prover_Correct meta_env var_env facts ->
    forall (l r : SH.SHeap types) res,
    forall (WTR : SH.WellTyped_sheap (typeof_funcs funcs) (SE.typeof_preds preds) (typeof_env meta_env) (typeof_env var_env) r = true) b,
    unfold (typeof_env meta_env) (typeof_env var_env) l r = (res, b) ->
    match res with
      | {| Alls := new_vars
         ; Exs  := new_uvars
         ; Lhs  := lhs'
         ; Rhs  := rhs'
         ; Know := facts'
         |} =>
      SH.WellTyped_sheap (typeof_funcs funcs) (SE.typeof_preds preds)
        (typeof_env meta_env) (typeof_env var_env ++ new_vars) lhs' = true ->
      SH.WellTyped_sheap (typeof_funcs funcs) (SE.typeof_preds preds)
        (typeof_env meta_env ++ new_uvars) (typeof_env var_env ++ new_vars) rhs' = true ->
      Expr.forallEach new_vars (fun nvs : Expr.env types =>
        let var_env := var_env ++ nvs in
          Valid prover_Correct meta_env var_env facts' ->
          Expr.AllProvable_impl funcs meta_env var_env
          (ST.himp
            (SE.sexprD funcs preds meta_env var_env
              (SH.sheapD (SH.Build_SHeap (SH.impures lhs') nil (SH.other lhs'))))
            (UNF.ST_EXT.existsEach (typeD := tvarD types) new_uvars (fun menv : Expr.env types =>
              let meta_env := meta_env ++ menv in
              SE.sexprD funcs preds meta_env var_env
              (SH.sheapD rhs'))))
          (SH.pures lhs'))
    end ->
    ST.himp (@SE.sexprD _ funcs preds meta_env var_env (SH.sheapD l))
                      (@SE.sexprD _ funcs preds meta_env var_env (SH.sheapD r)).
  Proof.
    Opaque Env.repr.
    intros. unfold unfold in *.
    destruct res.

    match goal with
      | [ H : match ?X with _ => _ end = _ |- _ ] => consider X
    end; intros.
    destruct u.
    match goal with
      | [ H : match ?X with _ => _ end = _ |- _ ] => consider X
    end; intros.
    destruct u.
    inversion H3; clear H3. subst Heap Heap0 b.

    eapply SH_UTIL.SEP_FACTS.himp_WellTyped_sexpr; intros.

    assert (UVars = typeof_env meta_env /\ 
      typeof_env var_env = firstn (length var_env) Vars /\
    ST.himp 
      (SE.sexprD funcs preds meta_env var_env (SH.sheapD l))
      (UNF.ST_EXT.existsEach (skipn (length var_env) Vars)
        (fun vars_ext : list {t : tvar & tvarD types t} =>
          SE.sexprD funcs preds meta_env 
          (var_env ++ vars_ext) (SH.sheapD Lhs0)))).
    { clear H2 H1. 
      generalize (UNF.refineForward_Length H0).
      eapply UNF.refineForward_Ok in H0; eauto using typeof_env_WellTyped_env.
      intro. destruct H1. destruct H1. simpl in *. split; auto. split; auto.
      subst.
      rewrite ListFacts.firstn_app_exact; auto. unfold typeof_env. rewrite map_length. auto.
      simpl; rewrite SH.WellTyped_sheap_WellTyped_sexpr; eassumption. }
    destruct H4. destruct H7. rewrite H8; clear H8.
    rewrite UNF.ST_EXT.himp_existsEach_p; [ reflexivity | intros ].

    { assert (Vars = typeof_env var_env ++ skipn (length var_env) Vars); intros.
      rewrite <- firstn_skipn with (n := length var_env) (l := Vars) at 1.
      rewrite <- H8. rewrite H7. reflexivity.

      generalize (UNF.refineBackward_Length H2); intros.
      destruct H11; simpl in *. destruct H11. subst Vars.

      apply SH_UTIL.himp_pull_pures; intros.

      generalize (UNF.refineBackward_WellTyped hintsBwd_Correct prover_Correct H2); simpl. intro.
      eapply UNF.refineBackward_Ok in H2.
      2: eassumption.
      2: eassumption.
      Focus 2. simpl. rewrite H4. eapply typeof_env_WellTyped_env.
      Focus 2. simpl. instantiate (1 := var_env ++ G). unfold WellTyped_env, typeof_env.
      rewrite map_app. rewrite H10. rewrite <- H8. reflexivity.

      Focus 2. simpl. rewrite H10; clear H10. subst; simpl.
      clear - WTR.
      repeat rewrite SH.WellTyped_sheap_WellTyped_sexpr in *.
      eapply SH_UTIL.SEP_FACTS.WellTyped_sexpr_weaken with (U' := nil) in WTR. rewrite app_nil_r in WTR. eauto.
      
      { simpl in *.
        rewrite SH_UTIL.SEP_FACTS.sexprD_weaken_wt with (U' := nil) (G' := G) (s := SH.sheapD r).
        rewrite app_nil_r.
        rewrite <- H2; clear H2. subst UVars0 Alls0.
        eapply forallEach_sem in H1.
        Focus 4.
        unfold typeof_env in *. rewrite map_length. eassumption.
        apply SH_UTIL.himp_pull_pures; intro.
        eapply AllProvable_impl_sem in H1; eauto.
        eapply SH_UTIL.sheapD_remove_pures_p. 
        rewrite H1; clear H1. subst Exs0. unfold typeof_env. rewrite map_length.
        eapply UNF.ST_EXT.himp_existsEach; intros. reflexivity.

        subst Know0. eapply Learn_correct; eauto. rewrite <- app_nil_r with (l := meta_env). eapply Valid_weaken. auto.

        Focus 3.
        rewrite <- SH.WellTyped_sheap_WellTyped_sexpr. eassumption. 

        Focus 2.
        revert H13. intro. cutrewrite (length (typeof_env var_env) = length var_env).
        rewrite <- H10. rewrite <- H13. f_equal.
        rewrite <- H6. rewrite <- H4. f_equal. rewrite ListFacts.rw_skipn_app; auto.
        rewrite H10. rewrite H4. rewrite <- app_nil_r with (l := typeof_env meta_env).
        repeat rewrite SH.WellTyped_sheap_WellTyped_sexpr in *.
        eapply SH_UTIL.SEP_FACTS.WellTyped_sexpr_weaken. eassumption.
        unfold typeof_env. rewrite map_length. auto.

        eapply UNF.refineForward_WellTyped in H0; simpl in *; try eassumption.
        Focus 2.
        repeat rewrite SH.WellTyped_sheap_WellTyped_sexpr in *. eassumption.
        rewrite H10 in *. rewrite H4 in H0.
        rewrite SH.WellTyped_sheap_WellTyped_sexpr in *.
        rewrite ListFacts.rw_skipn_app by reflexivity. 
        eassumption. }

      eapply Valid_weaken with (ue := nil) (ge := G) in H.
      rewrite app_nil_r in *; eauto.
      eapply Learn_correct; eassumption. }
  Qed.

End unfolder.
End UnfolderTac.
