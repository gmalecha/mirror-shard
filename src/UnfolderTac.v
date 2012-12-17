Require Import List Bool.
Require Import Expr SepExpr.
Require Import Prover.
Require Import Tactics Reflection.
Require Unfolder.
Require SepHeap.

Set Implicit Arguments.
Set Strict Implicit.

Module UnfolderTac (UNF : Unfolder.Unfolder).
  Module SH_UTIL := SepHeap.SepHeapFacts UNF.SH.
  Module SE_EXT := SepExpr.SepExprFacts UNF.SH.SE.

Section unfolder.
  Variable types : list type.
  Variable funcs : functions types.
  Variable preds : UNF.SH.SE.predicates types.
  Variable prover : ProverT types.
  Variable facts : Facts prover.
  Variable hintsFwd : option (UNF.hintSide types).
  Variable hintsBwd : option (UNF.hintSide types).

  Record unfolderResult : Type :=
  { Alls : list tvar
  ; Exs  : list tvar
  ; Lhs  : UNF.SH.SHeap types
  ; Rhs  : UNF.SH.SHeap types
  }.

  Definition unfold (uvars : list tvar)
    (ql : list tvar) (lhs rhs : UNF.SH.SHeap types) : unfolderResult * bool :=
    let pre :=
      {| UNF.Vars  := ql
       ; UNF.UVars := uvars
       ; UNF.Heap  := lhs
      |}
    in
    match match hintsFwd with
            | None => (pre, false)
            | Some hints => UNF.refineForward prover hints 10 facts pre 
          end
      with
      | ({| UNF.Vars := vars' ; UNF.UVars := uvars' ; UNF.Heap := lhs |}, fprog) =>
        let post :=
          {| UNF.Vars  := vars'
           ; UNF.UVars := uvars'
           ; UNF.Heap  := rhs
          |}
        in
        match match hintsBwd with
                | None => (post, false)
                | Some hints => 
                  let facts' := Learn _ facts (UNF.SH.pures lhs) in
                  UNF.refineBackward prover hints 10 facts' post
              end
        with
          | ({| UNF.Vars := vars' ; UNF.UVars := uvars' ; UNF.Heap := rhs |}, bprog) =>
            let new_vars  := skipn (length ql) vars' in
            let new_uvars := skipn (length uvars) uvars' in
            let bound := length uvars' in
            ({| Alls := new_vars
              ; Exs  := new_uvars
              ; Lhs  := lhs
              ; Rhs  := rhs
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
  Hypothesis hintsFwd_Correct : match hintsFwd with
                                  | Some hints => UNF.hintSideD funcs preds hints
                                  | None => True
                                end.
  Hypothesis hintsBwd_Correct : match hintsBwd with
                                  | Some hints => UNF.hintSideD funcs preds hints
                                  | None => True
                                end.

  Lemma ApplyUnfold_with_eq' : 
    forall (var_env meta_env : env types),
    Valid prover_Correct meta_env var_env facts ->
    forall (l r : UNF.SH.SHeap types) res,
    forall (WTR : UNF.SH.WellTyped_sheap (typeof_funcs funcs) (UNF.SH.SE.typeof_preds preds) (typeof_env meta_env) (typeof_env var_env) r = true) b,
    unfold (typeof_env meta_env) (typeof_env var_env) l r = (res, b) ->
    match res with
      | {| Alls := new_vars
         ; Exs  := new_uvars
         ; Lhs  := lhs'
         ; Rhs  := rhs'
         |} =>
        Expr.forallEach new_vars (fun nvs : Expr.env types =>
          let var_env := var_env ++ nvs in
          Expr.AllProvable_impl funcs meta_env var_env
          (Expr.existsEach new_uvars (fun menv : Expr.env types =>
            let meta_env := meta_env ++ menv in
                (Expr.AllProvable_and funcs meta_env var_env
                  (UNF.SH.SE.ST.himp
                    (UNF.SH.SE.sexprD funcs preds meta_env var_env
                      (UNF.SH.sheapD (UNF.SH.Build_SHeap (UNF.SH.impures lhs') nil (UNF.SH.other lhs'))))
                    (UNF.SH.SE.sexprD funcs preds meta_env var_env
                      (UNF.SH.sheapD (UNF.SH.Build_SHeap (UNF.SH.impures rhs') nil (UNF.SH.other rhs')))))
                  (UNF.SH.pures rhs')) ))
            (UNF.SH.pures lhs'))
    end ->
    UNF.SH.SE.ST.himp (@UNF.SH.SE.sexprD _ funcs preds meta_env var_env (UNF.SH.sheapD l))
                      (@UNF.SH.SE.sexprD _ funcs preds meta_env var_env (UNF.SH.sheapD r)).
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
    UNF.SH.SE.ST.himp 
      (UNF.SH.SE.sexprD funcs preds meta_env var_env (UNF.SH.sheapD l))
      (UNF.ST_EXT.existsEach (skipn (length var_env) Vars)
        (fun vars_ext : list {t : tvar & tvarD types t} =>
          UNF.SH.SE.sexprD funcs preds meta_env 
          (var_env ++ vars_ext) (UNF.SH.sheapD Lhs0)))).
    { clear H2 H1. destruct hintsFwd. 
      { generalize (UNF.refineForward_Length H0).
        eapply UNF.refineForward_Ok in H0; eauto using typeof_env_WellTyped_env.
        intro. destruct H1. destruct H1. simpl in *. split; auto. split; auto.
        subst.
        rewrite ListFacts.firstn_app_exact; auto. unfold typeof_env. rewrite map_length. auto.
        simpl; rewrite UNF.SH.WellTyped_sheap_WellTyped_sexpr; eassumption. }
      { inversion H0; clear H0; subst. split; auto.
        split. rewrite <- app_nil_r with (l := typeof_env var_env).
        rewrite ListFacts.firstn_app_exact. rewrite app_nil_r. auto. unfold typeof_env. rewrite map_length; auto.
        unfold typeof_env.
        erewrite ListFacts.skipn_length_all by reflexivity.
        rewrite UNF.ST_EXT.existsEach_nil. rewrite app_nil_r. reflexivity. } }
    destruct H4. destruct H7. rewrite H8; clear H8.
    rewrite UNF.ST_EXT.himp_existsEach_p; [ reflexivity | intros ].

    destruct hintsBwd.
    { assert (Vars = typeof_env var_env ++ skipn (length var_env) Vars); intros.
      rewrite <- firstn_skipn with (n := length var_env) (l := Vars) at 1.
      rewrite <- H8. rewrite H7. reflexivity.

      generalize (UNF.refineBackward_Length H2); intros.
      destruct H10; simpl in *. destruct H10. subst Vars0.

      apply SH_UTIL.himp_pull_pures; intros.

      eapply UNF.refineBackward_Ok in H2.
      2: eassumption.
      2: eassumption.
      Focus 2. simpl. rewrite H4. eapply typeof_env_WellTyped_env.
      Focus 2. simpl. instantiate (1 := var_env ++ G). unfold WellTyped_env, typeof_env.
      rewrite map_app. rewrite H9. rewrite <- H8. reflexivity.

      Focus 2. simpl. rewrite H9; clear H9. subst; simpl.
      clear - WTR.
      repeat rewrite UNF.SH.WellTyped_sheap_WellTyped_sexpr in *.
      eapply SH_UTIL.SEP_FACTS.WellTyped_sexpr_weaken with (U' := nil) in WTR. rewrite app_nil_r in WTR. eauto.
      
      { simpl in *.
        rewrite SH_UTIL.SEP_FACTS.sexprD_weaken_wt with (U' := nil) (G' := G) (s := UNF.SH.sheapD r).
        rewrite app_nil_r.
        rewrite <- H2; clear H2. subst UVars0 Alls0.
        eapply forallEach_sem in H1.
        Focus 2.
        unfold typeof_env in *. rewrite map_length. eassumption.
        apply SH_UTIL.himp_pull_pures; intro.
        eapply AllProvable_impl_AllProvable in H1; eauto.
        eapply existsEach_sem in H1. destruct H1. destruct H1.
        eapply AllProvable_and_sem in H5. destruct H5.
        eapply SH_UTIL.sheapD_remove_pures_p. 
        eapply UNF.ST_EXT.himp_existsEach_c. exists x0. split. subst UVars Exs0.
        unfold typeof_env in *.
        rewrite <- H6. rewrite map_length. reflexivity.

        eapply SH_UTIL.sheapD_remove_pures_c; eauto. rewrite <- H11; clear H11.

        eapply SH_UTIL.SEP_FACTS.himp_WellTyped_sexpr; intros.
        rewrite SH_UTIL.SEP_FACTS.sexprD_weaken_wt with (U' := x0) (G' := nil) by eassumption.
        rewrite app_nil_r. reflexivity.  

        rewrite <- UNF.SH.WellTyped_sheap_WellTyped_sexpr. eassumption. }

      eapply Valid_weaken with (ue := nil) (ge := G) in H.
      rewrite app_nil_r in *; eauto.
      eapply Learn_correct; eassumption. }
    { inversion H2; clear H2; subst.
      eapply forallEach_sem in H1. 
      2: unfold typeof_env; rewrite map_length; eassumption.
      apply SH_UTIL.himp_pull_pures; intro.
      eapply AllProvable_impl_AllProvable in H1; eauto.
      apply existsEach_sem in H1. destruct H1. destruct H1.
      eapply AllProvable_and_sem in H4. destruct H4.

      rewrite SH_UTIL.SEP_FACTS.sexprD_weaken_wt with (U' := x) (G' := G) (s := UNF.SH.sheapD Rhs0).
      2: rewrite <- UNF.SH.WellTyped_sheap_WellTyped_sexpr; eassumption.

      eapply SH_UTIL.SEP_FACTS.himp_WellTyped_sexpr; intros.
      rewrite SH_UTIL.SEP_FACTS.sexprD_weaken_wt with (U' := x) (G' := nil) (s := UNF.SH.sheapD Lhs0) by eassumption.
      clear H7.
      rewrite app_nil_r.

      eapply SH_UTIL.sheapD_remove_pures_p.
      eapply SH_UTIL.sheapD_remove_pures_c; eauto. } 
  Qed.

(*
  Lemma ApplyCancelSep_with_eq : 
    forall (algos_correct : ILAlgoTypes.AllAlgos_correct funcs preds algos),
    forall (meta_env : env (Env.repr BedrockCoreEnv.core types)) (hyps : Expr.exprs (_)),

    forall (l r : SEP.sexpr types BedrockCoreEnv.pc BedrockCoreEnv.st) res,
    unfolder (typeof_env meta_env) hyps l r = Some res ->
    Expr.AllProvable funcs meta_env nil hyps ->
    forall (WTR : SEP.WellTyped_sexpr (typeof_funcs funcs) (SEP.typeof_preds preds) (typeof_env meta_env) nil r = true) cs,

    match res with
      | {| AllExt := new_vars
         ; ExExt  := new_uvars
         ; Lhs    := lhs'
         ; Rhs    := rhs'
         ; Subst  := subst
         |} =>
        Expr.forallEach new_vars (fun nvs : Expr.env types =>
          let var_env := nvs in
          Expr.AllProvable_impl funcs meta_env var_env
          (existsSubst funcs var_env subst 0 
            (map (fun x => existT (fun t => option (tvarD types t)) (projT1 x) (Some (projT2 x))) meta_env ++
             map (fun x => existT (fun t => option (tvarD types t)) x None) new_uvars)
            (fun meta_env : Expr.env types =>
                (Expr.AllProvable_and funcs meta_env var_env
                  (himp cs 
                    (SEP.sexprD funcs preds meta_env var_env
                      (SH.sheapD (SH.Build_SHeap _ _ (SH.impures lhs') nil (SH.other lhs'))))
                    (SEP.sexprD funcs preds meta_env var_env
                      (SH.sheapD (SH.Build_SHeap _ _ (SH.impures rhs') nil (SH.other rhs')))))
                  (SH.pures rhs')) ))
            (SH.pures lhs'))
    end ->
    himp cs (@SEP.sexprD _ _ _ funcs preds meta_env nil l)
            (@SEP.sexprD _ _ _ funcs preds meta_env nil r).
  Proof. intros. eapply ApplyCancelSep_with_eq'; eauto. Qed.

  Lemma ApplyCancelSep : 
    forall (algos_correct : ILAlgoTypes.AllAlgos_correct funcs preds algos),
    forall (meta_env : env (Env.repr BedrockCoreEnv.core types)) (hyps : Expr.exprs (_)),
    forall (l r : SEP.sexpr types BedrockCoreEnv.pc BedrockCoreEnv.st),
      Expr.AllProvable funcs meta_env nil hyps ->
    forall (WTR : SEP.WellTyped_sexpr (typeof_funcs funcs) (SEP.typeof_preds preds) (typeof_env meta_env) nil r = true) cs,
    match unfolder (typeof_env meta_env) hyps l r with
      | Some {| AllExt := new_vars
         ; ExExt  := new_uvars
         ; Lhs    := lhs'
         ; Rhs    := rhs'
         ; Subst  := subst
         |} =>
        Expr.forallEach new_vars (fun nvs : Expr.env types =>
          let var_env := nvs in
          Expr.AllProvable_impl funcs meta_env var_env
          (existsSubst funcs var_env subst 0 
            (map (fun x => existT (fun t => option (tvarD types t)) (projT1 x) (Some (projT2 x))) meta_env ++
             map (fun x => existT (fun t => option (tvarD types t)) x None) new_uvars)
            (fun meta_env : Expr.env types =>
                (Expr.AllProvable_and funcs meta_env var_env
                  (himp cs 
                    (SEP.sexprD funcs preds meta_env var_env
                      (SH.sheapD (SH.Build_SHeap _ _ (SH.impures lhs') nil (SH.other lhs'))))
                    (SEP.sexprD funcs preds meta_env var_env
                      (SH.sheapD (SH.Build_SHeap _ _ (SH.impures rhs') nil (SH.other rhs')))))
                  (SH.pures rhs')) ))
            (SH.pures lhs'))
      | None => 
        himp cs (@SEP.sexprD _ _ _ funcs preds meta_env nil l)
                (@SEP.sexprD _ _ _ funcs preds meta_env nil r)
    end ->
    himp cs (@SEP.sexprD _ _ _ funcs preds meta_env nil l)
            (@SEP.sexprD _ _ _ funcs preds meta_env nil r).
  Proof. 
    intros. consider (unfolder (typeof_env meta_env) hyps l r); intros; auto.
    eapply ApplyCancelSep_with_eq; eauto.
  Qed.
*)

End unfolder.
End UnfolderTac.
