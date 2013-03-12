Require Import List.
Require Import Expr.

Set Implicit Arguments.
Set Strict Implicit.

Section over_types.
  Variable types : list type.

  Inductive Quant : Type := 
  | QAll  : variables -> Quant -> Quant
  | QEx   : variables -> Quant -> Quant
  | QBase : Quant.

  (** NOTE: For efficiency, the outer-most quantifier should be
   ** the deepest quantifier
   **)
  (** NOTE: 
   ** For forward reasoning we need to invert the quantifiers.
   ** i.e. All quantifiers should become uvar and 
   **      Ex quantifiers should become var
   **)
  Fixpoint quantD (ex_env all_env : env types) (qs : Quant) (k : env types -> env types -> Prop) : Prop :=
    match qs with
      | QBase => k ex_env all_env
      | QAll vs qs => quantD ex_env all_env qs (fun ex_env all_env => forallEach vs (fun all_ext => k ex_env (all_env ++ all_ext)))
      | QEx vs qs => quantD ex_env all_env qs (fun ex_env all_env => existsEach vs (fun ex_ext => k (ex_env ++ ex_ext) all_env))
    end.

  Fixpoint appendQ (q1 q2 : Quant) : Quant :=
    match q1 with 
      | QBase => q2
      | QAll vs q1 => QAll vs (appendQ q1 q2)
      | QEx vs q1 => QEx vs (appendQ q1 q2)
    end.

  Theorem quantD_app : forall qs' qs meta_env vars_env k, 
    quantD meta_env vars_env (appendQ qs qs') k <->
    quantD meta_env vars_env qs' (fun meta_env vars_env => quantD meta_env vars_env qs k).
  Proof.
    clear; induction qs; simpl; intros; try rewrite IHqs; try reflexivity.
  Qed.

  Fixpoint gatherEx (qs : Quant) : variables :=
    match qs with
      | QBase => nil
      | QAll _ qs => gatherEx qs
      | QEx vs qs => gatherEx qs ++ vs
    end.

  Fixpoint gatherAll (qs : Quant) : variables :=
    match qs with
      | QBase => nil
      | QAll vs qs => gatherAll qs ++ vs
      | QEx _ qs => gatherAll qs
    end.

  Theorem quantD_impl : forall qs meta_env vars_env (k k' : _ -> _ -> Prop),
    quantD meta_env vars_env qs k ->
    (forall a b,
      typeof_env a = gatherEx qs -> 
      typeof_env b = gatherAll qs -> 
      k (meta_env ++ a) (vars_env ++ b) ->
      k' (meta_env ++ a) (vars_env ++ b)) ->
    quantD meta_env vars_env qs k'.
  Proof.
    clear. induction qs; simpl; intros; try (eapply IHqs; [ eauto | ]); simpl in *; intros; instantiate; simpl in *;
    repeat match goal with 
             | [ |- existsEach _ _ ] => eapply existsEach_sem
             | [ |- forallEach _ _ ] => eapply forallEach_sem; intros
             | [ H : existsEach _ _ |- _ ] =>
               eapply existsEach_sem in H; destruct H
             | [ H : forallEach _ _ |- _ ] =>
               eapply forallEach_sem in H; [ | solve [ eauto ] ]
             | [ H : _ /\ _ |- _ ] => destruct H
             | [ |- exists x, _ /\ _ ] =>
               eexists; split; [ solve [ eauto ] | ]                   
             | [ |- _ ] => rewrite app_ass in *
           end.
    { eapply H0; eauto. subst. rewrite <- H2. unfold typeof_env. rewrite map_app. auto. }
    { eapply H0; eauto. subst. rewrite <- H1. unfold typeof_env. rewrite map_app. auto. }
    { specialize (H0 nil nil). repeat rewrite app_nil_r in *. auto. }
  Qed.

  Require Import Tactics.

  Theorem gatherEx_appendQ : forall q1 q2, 
    gatherEx (appendQ q1 q2) = gatherEx q2 ++ gatherEx q1.
  Proof.
    induction q1; simpl; intros; think; repeat (rewrite app_nil_r || rewrite app_ass); auto.
  Qed.

  Theorem gatherAll_appendQ : forall q1 q2, 
    gatherAll (appendQ q1 q2) = gatherAll q2 ++ gatherAll q1.
  Proof.
    induction q1; simpl; intros; think; repeat (rewrite app_nil_r || rewrite app_ass); auto.
  Qed.

  Definition qex (ls : list tvar) (q : Quant) : Quant :=
    match ls with
      | nil => q
      | _ => QEx ls q
    end.

  Definition qall (ls : list tvar) (q : Quant) : Quant :=
    match ls with
      | nil => q
      | _ => QAll ls q
    end.

  Lemma quantD_qex_QEx : forall U G a b P,
    quantD U G (QEx a b) P <-> quantD U G (qex a b) P.
  Proof. clear.
    destruct a; simpl in *; split; intros; auto.
    { eapply quantD_impl; eauto; intros. simpl in *. rewrite app_nil_r in *. auto. }
    { eapply quantD_impl; eauto; intros. simpl in *. rewrite app_nil_r in *. auto. }
  Qed.

  Lemma quantD_qall_QAll : forall U G a b P,
    quantD U G (QAll a b) P <-> quantD U G (qall a b) P.
  Proof. clear.
    destruct a; simpl in *; split; intros; auto.
    { eapply quantD_impl; eauto; intros. simpl in *. rewrite app_nil_r in *. auto. }
    { eapply quantD_impl; eauto; intros. simpl in *. rewrite app_nil_r in *. auto. }
  Qed.

  Lemma appendQ_assoc : forall a b c,
    appendQ (appendQ a b) c = appendQ a (appendQ b c).
  Proof.
    clear. induction a; simpl; intros; try f_equal; eauto.
  Qed.

  Lemma appendQ_QAll : forall a b v,
    appendQ a (QAll v b) = appendQ (appendQ a (QAll v QBase)) b.
  Proof. clear.
    induction a; simpl; intros; try rewrite IHa; eauto.
  Qed.
  Lemma appendQ_QEx : forall a b v,
    appendQ a (QEx v b) = appendQ (appendQ a (QEx v QBase)) b.
  Proof. clear.
    induction a; simpl; intros; try rewrite IHa; eauto.
  Qed.

  Lemma QAll_inj_False : forall a b,
    QAll a b = b -> False.
  Proof. clear.
    induction b; simpl; intros; try congruence; auto.
  Qed.

  Lemma QEx_inj_False : forall a b,
    QEx a b = b -> False.
  Proof. clear.
    induction b; simpl; intros; try congruence; auto.
  Qed.

  Fixpoint qsize (q : Quant) : nat :=
    match q with
      | QBase => 0
      | QAll _ q              
      | QEx _ q => S (qsize q)
    end.

  Lemma qsize_appendQ : forall a b,
    qsize (appendQ a b) = qsize a + qsize b.
  Proof.
    clear; induction a; simpl in *; auto.
  Qed.

  Ltac apply_eq f H :=
    match type of H with
      | ?X = ?Y =>
        assert (f X = f Y); [ f_equal; apply H | ] 
    end.

  Lemma appendQ_proper : forall a b c,
    appendQ a b = appendQ c b ->
    a = c.
  Proof.
    clear. induction a; destruct c; simpl; intros; try congruence;
    repeat match goal with
             | [ H : QAll _ _ = QAll _ _ |- _ ] => inversion H; clear H; subst
             | [ H : QEx _ _ = QEx _ _ |- _ ] => inversion H; clear H; subst
           end; try solve [ f_equal; eauto ]; exfalso.
    { apply_eq qsize H. simpl in *; rewrite qsize_appendQ in H0. omega. }
    { apply_eq qsize H. simpl in *; rewrite qsize_appendQ in H0. omega. }
    { apply_eq qsize H. simpl in *; rewrite qsize_appendQ in H0. omega. }
    { apply_eq qsize H. simpl in *; rewrite qsize_appendQ in H0. omega. }
  Qed.

End over_types.