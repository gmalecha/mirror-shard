Require Import Coq.Lists.List.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Core.EquivDec.
Require Import MirrorShard.Instantiation.
Require Import MirrorShard.Expr.
Require Import MirrorShard.Tactics.
Require MirrorShard.UnfolderTac.
Require MirrorShard.ExprUnify.

Set Implicit Arguments.
Set Strict Implicit.

Lemma ex_iff : forall T (P P' : T -> Prop),
  (forall x, P x <-> P' x) ->
  ((exists x, P x) <-> (exists x, P' x)).
Proof. split; intuition; destruct H0 as [ x ? ]; exists x; firstorder. Qed.

Theorem existsEach_iff : forall ts a P Q,
  (forall x, map (@projT1 _ _) x = a ->
    (P x <-> Q x)) ->
  (@existsEach ts a P <-> existsEach a Q).
Proof.
  induction a; simpl; intros.
  { specialize (H nil refl_equal). auto. }
  { apply ex_iff. intros. rewrite IHa. reflexivity.
    intros. simpl. eapply H. simpl. f_equal. auto. }
Qed.

Module Make (SUBST : Subst).

  Section existsSubst.
    Variable types : list type.
    Variable funcs : functions types.
    Variable sub : SUBST.Subst types.

    Fixpoint existsSubst (meta vars : env types) (from : nat) (vals : list tvar)
      (ret : env types -> Prop) : Prop :=
      match vals with
        | nil => ret meta
        | t :: ts =>
          match SUBST.Subst_lookup from sub with
            | None =>
              exists x : tvarD types t,
                existsSubst (meta ++ existT _ _ x :: nil) vars (S from) ts ret
            | Some v =>
              match exprD funcs meta vars v t with
                | None =>
                  exists x : tvarD types t,
                    existsSubst (meta ++ existT _ _ x :: nil) vars (S from) ts
                    (fun g => match exprD funcs g vars v t with
                                | None => False
                                | Some y => x = y /\ ret g
                              end)
                | Some v => existsSubst (meta ++ existT _ _ v :: nil) vars (S from) ts ret
              end
          end
      end.

  End existsSubst.


  Theorem existsSubst_sem : forall ts (funcs : functions ts) sub vals meta_env vars_env from ret,
    existsSubst funcs sub meta_env vars_env from vals ret <->
    existsEach vals (fun meta_ext =>
         SUBST.Subst_equations_to funcs (meta_env ++ meta_ext) vars_env sub from meta_ext
      /\ ret (meta_env ++ meta_ext)).
  Proof.
    induction vals; simpl; intros.
    { rewrite app_nil_r. intuition. }
    { consider (SUBST.Subst_lookup from sub); intros.
      { consider (exprD funcs meta_env vars_env e a); intros.
        { rewrite IHvals; intuition.
          { exists t. eapply existsEach_sem in H1. eapply existsEach_sem.
            destruct H1. exists x. destruct H1. split; try assumption.
            eapply exprD_weaken with (vars' := nil) (uvars' := existT (tvarD ts) a t :: x) in H0.
            rewrite app_nil_r in H0. rewrite H0. simpl in *.
            rewrite app_ass in *; simpl in *. intuition. }
          { destruct H1.
            apply existsEach_sem in H1. apply existsEach_sem.
            destruct H1. destruct H1. exists x0. split; auto.
            consider (exprD funcs (meta_env ++ existT (tvarD ts) a x :: x0) vars_env e a); intros.
            2: intuition.
            rewrite app_ass in *; simpl in *.
            eapply exprD_weaken with (vars' := nil) (uvars' := existT (tvarD ts) a x :: x0) in H0.
            rewrite app_nil_r in H0. rewrite H0 in H2. inversion H2; clear H2; subst.
            intuition subst; intuition. } }
        { apply ex_iff; intros.
          rewrite IHvals.
          apply existsEach_iff; intros.
          rewrite app_ass; simpl.
          destruct (exprD funcs (meta_env ++ existT (tvarD ts) a x :: x0) vars_env e a); intuition. } }
      { apply ex_iff; intros.
        rewrite IHvals. apply existsEach_iff; intros. rewrite app_ass; simpl.
        intuition. } }
    Qed.

End Make.