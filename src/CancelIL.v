Require Import List.
Require Import IL SepIL.
Require Import Expr SepExpr SepCancel.
Require Import Prover.
Require Import Tactics Reflection.
Require ExprUnify.

Set Implicit Arguments.
Set Strict Implicit.

Require UnfolderTac CancelTac.

Module SE := SepExpr.Make SepIL.ST.
Module SH := SepHeap.Make SE.

Module UNF := Unfolder.Make SH ExprUnify.UNIFIER.
Module UNF_TAC := UnfolderTac.UnfolderTac UNF.

Module CANCEL := SepCancel.Make ExprUnify.UNIFIER SH.
Module CANCEL_TAC := CancelTac.CancellerTac CANCEL.

Section parametric.
  Variable ts : list type.
  Variable tpreds : SE.tpredicates.
  Variable prover : ProverT ts.
  
  Inductive cancelResult : Type :=
  | Done : forall (lhs rhs : SH.SHeap ts), cancelResult
  | Quant : forall (alls : list tvar) (pures : exprs ts) (exs : list tvar) (sub : ExprUnify.UNIFIER.Subst ts),
    cancelResult -> cancelResult.

  Variable fs : functions ts.
  Variable ps : SE.predicates ts.

  Fixpoint cancelResultD (U G : env ts) (cr : cancelResult) {struct cr} : Prop :=
    match cr with
      | Done l r =>
        (** TODO: Should I perform the substitution now? *)
        AllProvable_and fs U G 
          (SE.himp fs ps U G (SH.sheapD l) 
                             (SH.sheapD (SH.Build_SHeap (SH.impures r) nil (SH.other r))))
          (SH.pures r)
      | Quant alls pures exs sub r =>
        forallEach alls (fun Aext => 
          let G := G ++ Aext in
          AllProvable_impl fs U G
            (@CANCEL_TAC.existsSubst ts fs G sub 0 
              (map (fun x => @existT _ (fun tv => option (tvarD ts tv)) (projT1 x) (Some (projT2 x))) U ++
               map (fun x => @existT _ _ x None) exs)
              (fun U => cancelResultD U G r))
          pures)
    end.

  Require Import Bool.

  Variables hintsFwd hintsBwd : UNF.hintSide ts.

  (** This will implement a loop of unfolding and cancellation **)
  Fixpoint cancelLoop (n : nat) (facts : Facts prover) (uvars vars : list tvar)
    (l r : SH.SHeap ts) (sub : ExprUnify.UNIFIER.Subst ts) (prog : bool) {struct n}
    : cancelResult * bool :=
    match n with 
      | 0 => 
        let Lhs' := SH.Build_SHeap (SH.impures l) nil (SH.other l) in
        (Quant nil (SH.pures l) nil sub (Done Lhs' r), true)
      | S n =>
        (** Start by doing refinement **)
        let '(unf, prog') := @UNF_TAC.unfold ts prover facts hintsFwd hintsBwd uvars vars l r in
        @UNF_TAC.unfolderResult_rect ts prover _ 
          (fun alls exs lhs rhs know =>
            let '(cncl, prog'') := @CANCEL_TAC.canceller ts prover tpreds know lhs rhs sub in
            if prog' || prog'' then
              match cncl with
                | {| CANCEL_TAC.Lhs := Lhs; CANCEL_TAC.Rhs := Rhs; CANCEL_TAC.Subst := Subst |} =>
                  let Lhs' := SH.Build_SHeap (SH.impures Lhs) nil (SH.other Lhs) in
                  let '(res, p) := cancelLoop n know (uvars ++ exs) (vars ++ alls) Lhs' Rhs Subst true in
                  (Quant alls (SH.pures Lhs) exs Subst res, p)
              end
            else
              (Done l r, prog))
          unf
    end.

End parametric.

Theorem AllProvable_impl_sem : forall ts (funcs : functions ts)  U G P ps,
  AllProvable_impl funcs U G P ps <-> (AllProvable funcs U G ps -> P).
Proof.
  induction ps; simpl in *; unfold Basics.impl; intuition.
Qed.

Lemma cancelLoop_ind_pf : forall 
  types (funcs : functions types) (preds : SE.predicates types) 
  prover hintsFwd hintsBwd
  (bound : nat) uvars vars (lhs rhs : SH.SHeap types) (facts : Facts prover) sub_init
  cr prog b,
  forall (PC : ProverT_correct prover funcs),
  UNF.SH.WellTyped_sheap (typeof_funcs funcs) (UNF.SH.SE.typeof_preds preds)
    (typeof_env uvars) (typeof_env vars) rhs = true ->
  CANCEL.U.Subst_equations funcs uvars vars sub_init ->
  Valid PC uvars vars facts ->
  UNF.hintSideD funcs preds hintsFwd ->
  UNF.hintSideD funcs preds hintsBwd ->
  cancelLoop (SE.typeof_preds preds) prover hintsFwd hintsBwd bound facts (typeof_env uvars) (typeof_env vars) lhs rhs
    sub_init b = (cr, prog) ->
  (cancelResultD funcs preds uvars vars cr) ->
  SE.himp funcs preds uvars vars (SH.sheapD lhs) (SH.sheapD rhs).
Proof.
  induction bound; simpl; intros.
  { inversion H4; clear H4; subst.
    simpl in *.
    eapply UNF.HEAP_FACTS.himp_pull_pures; intros.
    repeat rewrite app_nil_r in *.
    eapply AllProvable_impl_AllProvable in H5; eauto.
    eapply CANCEL_TAC.existsSubst_sem in H5.
    rewrite map_map in *; simpl in *.
    eapply existsEach_sem in H5. destruct H5. intuition.
    eapply CANCEL_TAC.consistent_Some in H5. subst.
    eapply AllProvable_and_sem in H9. intuition.
    eapply UNF_TAC.SH_UTIL.sheapD_remove_pures_p.
    eapply UNF_TAC.SH_UTIL.sheapD_remove_pures_c; eauto. }
  { consider (UNF_TAC.unfold prover facts hintsFwd hintsBwd 
              (typeof_env uvars) (typeof_env vars) lhs rhs); intros.
    destruct u; simpl in *.
    consider (CANCEL_TAC.canceller prover (SE.typeof_preds preds) Know Lhs Rhs sub_init); intros.
    destruct (b0 || b1).
    { destruct c.
      match goal with
        | [ H : match ?X with _ => _ end = _ |- _ ] =>
          consider X
      end; intros.
      inversion H8; clear H8; subst.
      simpl in *.
      eapply CANCEL_TAC.SH_FACTS.SEP_FACTS.himp_WellTyped_sexpr; intro.
      eapply UNF_TAC.ApplyUnfold_with_eq' in H4; try eassumption. intros.
      eapply forallEach_sem; intros.

      eapply AllProvable_impl_sem; intros.
      generalize (CANCEL_TAC.canceller_PuresPrem _ _ _ _ _ _ _ _ _ H6 H13). simpl; intro.

      eapply forallEach_sem in H5; try eassumption.
      eapply AllProvable_impl_sem in H5; try eassumption.
      eapply CANCEL_TAC.existsSubst_sem in H5.
      eapply existsEach_sem in H5. destruct H5; intuition.

      eapply UNF.ST_EXT.himp_existsEach_c.
      eapply CANCEL_TAC.consistent_app in H5. intuition.
      rewrite map_length in *.
      rewrite map_app in *; repeat rewrite map_map in *; simpl in *.
      rewrite map_id in *. exists (skipn (length uvars) x).
      rewrite <- firstn_skipn with (l := x) (n := length uvars) in H15.
      unfold typeof_env in H15; rewrite map_app in H15.
      eapply ListFacts.app_inj_length in H15.
      intuition.

      eapply CANCEL_TAC.ApplyCancelSep_with_eq' with (funcs := funcs)
        (meta_env := (uvars ++ skipn (length uvars) x)) (var_env := var_env) in H6.
      intuition.
      rewrite <- H6.
      eapply UNF_TAC.SH_UTIL.sheapD_remove_pures_c.
      rewrite <- app_nil_r with (l := var_env). eapply AllProvable_weaken. eassumption.
      rewrite <- app_nil_r with (l := var_env) at 2.
      eapply UNF.HEAP_FACTS.SEP_FACTS.sexprD_weaken.
      rewrite <- app_nil_r with (l := var_env). eapply Valid_weaken. eassumption.
      subst var_env.
      eapply CANCEL_TAC.consistent_Some in H17. rewrite H17.
      rewrite <- H17 at 2. rewrite firstn_skipn.

      { clear - H0 H17. 
        rewrite <- firstn_skipn with (l := x) (n := length uvars).        
        simpl in *. cutrewrite (firstn (length uvars) x ++ skipn (length uvars) x = uvars ++ skipn (length uvars) x).
        eapply ExprUnify.UNIFIER.Subst_equations_weaken; eauto.
        f_equal. symmetry. apply H17. }

      unfold typeof_env in *. rewrite map_app. rewrite H20.
      unfold var_env. rewrite map_app. rewrite H11.
      eassumption.

      unfold typeof_env in *. rewrite map_app. rewrite H20.
      unfold var_env. rewrite map_app. rewrite H11.
      rewrite SH.WellTyped_sheap_WellTyped_sexpr. 
      rewrite <- app_nil_r with (l := map (projT1 (P:=tvarD types)) vars ++ Alls).
      eapply UNF.HEAP_FACTS.SEP_FACTS.WellTyped_sexpr_weaken.
      rewrite <- SH.WellTyped_sheap_WellTyped_sexpr. eassumption.

      rewrite <- H20 in H7. rewrite <- H11 in H7.
      change (map (projT1 (P:=tvarD types)) (skipn (length uvars) x)) with (typeof_env (skipn (length uvars) x)) in H7.
      repeat rewrite <- typeof_env_app in H7.

      simpl; intros.
      eapply IHbound in H7; try eassumption.
      { simpl; intros. 
        eapply CANCEL_TAC.existsSubst_sem.
        rewrite map_map. simpl.
        eapply existsEach_sem.
        exists (uvars ++ skipn (length uvars) x).
        { intuition.
          eapply CANCEL_TAC.consistent_Some; reflexivity.
          { assert (x = uvars ++ skipn (length uvars) x).
            { rewrite <- firstn_skipn with (l := x) (n := length uvars) at 1.
              f_equal. eapply CANCEL_TAC.consistent_Some in H17. auto. }
            rewrite <- H23 in *. eassumption. }
          unfold SE.himp in H7.
          subst var_env. rewrite <- H7.
          eapply UNF_TAC.SH_UTIL.sheapD_remove_pures_p. reflexivity. } }
      { assert (x = uvars ++ skipn (length uvars) x).
        { rewrite <- firstn_skipn with (l := x) (n := length uvars) at 1.
          f_equal. eapply CANCEL_TAC.consistent_Some in H17. auto. }
        rewrite <- H23 in *.
        eapply CANCEL.U.Subst_equations_to_Subst_equations; eauto.
        eapply CANCEL_TAC.canceller_PureFacts in H6.
        simpl in *. intuition. eapply H24.
        rewrite H23. 
        eapply CANCEL.U.Subst_equations_weaken in H0.
        eapply CANCEL.U.Subst_equations_WellTyped in H0.
        eassumption.

        rewrite H23. rewrite <- H11 in *. repeat rewrite typeof_env_app.
        rewrite <- app_nil_r with (l := typeof_env vars ++ typeof_env env).
        repeat rewrite SH.WellTyped_sheap_WellTyped_sexpr in *.
        rewrite UNF.HEAP_FACTS.SEP_FACTS.WellTyped_sexpr_weaken by eassumption. reflexivity.

        rewrite H23. rewrite <- H11 in *. rewrite <- H20 in *. repeat rewrite typeof_env_app.
        repeat rewrite SH.WellTyped_sheap_WellTyped_sexpr in *.
        unfold typeof_env in *. eassumption. }

      rewrite <- app_nil_r with (l := vars ++ env).
      eapply Valid_weaken; eauto.

      eapply CANCEL_TAC.consistent_Some in H17.
      rewrite H17 at 1. rewrite firstn_skipn. eassumption. 

      repeat rewrite map_length. rewrite firstn_length.
      rewrite Min.min_l; auto.
      clear - H15.
      rewrite <- map_app in H15. rewrite firstn_skipn in H15.
      assert (length (map (projT1 (P:=tvarD types)) x) =
        length (map (fun x : sigT (tvarD types) => projT1 x) uvars ++ Exs)).
      { rewrite H15; auto. }
      repeat rewrite map_length in *. rewrite app_length in *.
      rewrite map_length in *. omega. }
    { inversion H7; clear H7; subst. simpl in *.
      eapply AllProvable_and_sem in H5. destruct H5.
      eapply UNF_TAC.SH_UTIL.sheapD_remove_pures_c; eauto. } }
Qed.


