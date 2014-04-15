Require Import Coq.Lists.List.
Require Import MirrorShard.ExprUnify.
Require Import MirrorShard.SepHeap.
Require Import MirrorShard.Expr.


Set Implicit Arguments.
Set Strict Implicit.

Module Make (SUBST : Instantiation.Subst)
            (ST : SepTheory.SepTheory) (SE : SepExpr.SepExpr ST)
            (SH : SepHeap ST SE).
  Module SH_FACTS := SepHeapFacts ST SE SH.
  Import SH_FACTS.

  Section typed.
    Variable types : list type.
    Variable s : SUBST.Subst types.

    Definition impuresInstantiate : MM.mmap (exprs types) -> MM.mmap (exprs types) :=
      MM.mmap_map (map (@SUBST.exprInstantiate _ s)).

    Definition sheapInstantiate (h : SH.SHeap types) : SH.SHeap types :=
      {| SH.impures := impuresInstantiate (SH.impures h)
       ; SH.pures   := map (@SUBST.exprInstantiate _ s) (SH.pures h)
       ; SH.other   := SH.other h
       |}.

    Variable funcs : functions types.
    Variable preds : SE.predicates types.

    Variables U G : env types.

    Lemma impuresInstantiate_mmap_add : forall n e acc, SE.heq funcs preds U G
        (SH.impuresD (impuresInstantiate (MM.mmap_add n e acc)))
        (SH.impuresD
          (MM.mmap_add n (map (@SUBST.exprInstantiate _ s) e)
                         (impuresInstantiate acc))).
    Proof.
      clear. intros. eapply MM.PROPS.map_induction with (m := acc); intros.
      { unfold MM.mmap_add, impuresInstantiate, MM.mmap_map.
        repeat rewrite MF.find_Empty by auto using MF.map_Empty.
        rewrite SH.impuresD_Equiv. reflexivity.
        rewrite MF.map_add. simpl.
        reflexivity. }
      { unfold MM.mmap_add, impuresInstantiate, MM.mmap_map.
        rewrite MF.FACTS.map_o. simpl in *. unfold exprs in *. case_eq (FM.find n m'); simpl; intros.
        { rewrite SH.impuresD_Equiv. reflexivity.
          rewrite MF.map_add. reflexivity. }
        { rewrite SH.impuresD_Equiv. reflexivity.
          rewrite MF.map_add. simpl. reflexivity. } }
    Qed.

    Lemma sheapInstantiate_Equiv : forall a b,
      MM.mmap_Equiv a b ->
      MM.mmap_Equiv (impuresInstantiate a) (impuresInstantiate b).
    Proof.
      clear. unfold impuresInstantiate, MM.mmap_Equiv, MM.mmap_map, FM.Equiv; intuition;
      try solve [ repeat match goal with
                           | [ H : FM.In _ (FM.map _ _) |- _ ] => apply MF.FACTS.map_in_iff in H
                           | [ |- FM.In _ (FM.map _ _) ] => apply MF.FACTS.map_in_iff
                         end; firstorder ].
      repeat match goal with
               | [ H : FM.MapsTo _ _ (FM.map _ _) |- _ ] =>
                 apply MF.FACTS.map_mapsto_iff in H; destruct H; intuition; subst
             end.
      apply Permutation.Permutation_map. firstorder.
    Qed.

    Lemma sheapInstantiate_add : forall n e m m',
      ~FM.In n m ->
      MM.PROPS.Add n e m m' ->
      SE.heq funcs preds U G
        (SH.impuresD (impuresInstantiate m'))
        (SH.starred (fun v => SE.Func n (map (SUBST.exprInstantiate s) v)) e
          (SH.impuresD (impuresInstantiate m))).
    Proof.
      clear. intros.
        unfold impuresInstantiate, MM.mmap_map.
        rewrite SH.impuresD_Add with (i := FM.map (map (map (SUBST.exprInstantiate s))) m) (f := n) (argss := map (map (SUBST.exprInstantiate s)) e).
        symmetry; rewrite SH.starred_base. heq_canceler.
        repeat rewrite SH.starred_def.
        match goal with
          | [ |- context [ @SE.Emp ?X ] ] => generalize (@SE.Emp X)
        end.
        clear. induction e; simpl; intros; try reflexivity.
        rewrite IHe. heq_canceler.

        red. intros. specialize (H0 y). repeat (rewrite MM.FACTS.add_o in * || rewrite MM.FACTS.map_o in * ).
        unfold exprs in *. rewrite H0. unfold MM.FACTS.option_map. destruct (MF.FACTS.eq_dec n y); auto.

        intro. apply H. apply MM.FACTS.map_in_iff in H1. auto.
    Qed.

    Lemma applyD_forget_exprInstantiate :
      SUBST.Subst_equations funcs U G s ->
      forall D R F l,
        applyD (exprD funcs U G) D (map (SUBST.exprInstantiate s) l) R F =
        applyD (exprD funcs U G) D l R F.
    Proof.
      clear. induction D; destruct l; simpl; auto.
      rewrite SUBST.Subst_equations_exprInstantiate; eauto.
      destruct (exprD funcs U G e a); eauto.
    Qed.

    Lemma starred_forget_exprInstantiate : forall x P,
      SUBST.Subst_equations funcs U G s ->
      forall e,
      SE.heq funcs preds U G
        (SH.starred (fun v : list (expr types) => SE.Func x (map (SUBST.exprInstantiate s) v)) e P)
        (SH.starred (SE.Func x) e P).
    Proof.
      clear. induction e; intros; repeat rewrite SH.starred_def; simpl; repeat rewrite <- SH.starred_def; SEP_FACTS.heq_canceler.
        rewrite IHe. SEP_FACTS.heq_canceler. unfold SE.heq. simpl.
        match goal with
                 | [ |- context [ match ?X with _ => _ end ] ] =>
                   case_eq X; intros; try reflexivity
               end.
        erewrite applyD_forget_exprInstantiate with (D := SE.SDomain p) (F := SE.SDenotation p); eauto.
        reflexivity.
    Qed.

    Lemma impuresD_forget_impuresInstantiate : forall h,
      SUBST.Subst_equations funcs U G s ->
      SE.heq funcs preds U G
        (SH.impuresD (impuresInstantiate h))
        (SH.impuresD h).
    Proof.
      clear. intros. eapply MM.PROPS.map_induction with (m := h); intros.
      { unfold sheapInstantiate, MM.mmap_map. repeat rewrite SH.impuresD_Empty; eauto using MF.map_Empty. reflexivity. }
      { rewrite sheapInstantiate_add; eauto. rewrite SH.starred_base. symmetry.
        rewrite SH.impuresD_Add; eauto. rewrite <- H0. SEP_FACTS.heq_canceler.
        rewrite starred_forget_exprInstantiate; auto. reflexivity. }
    Qed.

    Lemma Func_forget_exprInstantiate : forall n e,
      SUBST.Subst_equations funcs U G s ->
      SE.heq funcs preds U G (SE.Func n (map (SUBST.exprInstantiate s) e)) (SE.Func n e).
    Proof. clear.
      unfold SE.heq. simpl. intros.
      destruct (nth_error preds n); try reflexivity.
      rewrite applyD_forget_exprInstantiate; auto. reflexivity.
    Qed.

  End typed.

End Make.