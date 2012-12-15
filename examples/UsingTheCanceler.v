Require Import Bedrock.SepTheory.
Require Import RelationClasses.

Module SimpleSepLog <: SepTheory_Kernel.
  Require Import FunctionalExtensionality.

  Definition heap := nat -> option nat.

  Definition hprop := heap -> Prop.

  Definition himp (l r : hprop) : Prop :=
    forall h, l h -> r h.

  Definition heq (l r : hprop) : Prop :=
    forall h, l h <-> r h.

  Global Instance Refl_himp : Reflexive himp.
  Proof. repeat red; intuition. Qed.

  Global Instance Trans_himp : Transitive himp.
  Proof. repeat red; intuition. Qed.

  Global Instance Refl_heq : Reflexive heq.
  Proof. repeat red; intuition. Qed.

  Global Instance Sym_heq : Symmetric heq.
  Proof. repeat red; firstorder. Qed.

  Global Instance Trans_heq : Transitive heq.
  Proof. repeat red; firstorder. Qed.

  Theorem heq_defn : forall l r, (himp l r /\ himp r l) <-> heq l r.
  Proof. unfold himp, heq; firstorder. Qed.

  Definition inj (p : Prop) : hprop := fun m => p /\ forall p, m p = None.

  Definition emp : hprop := inj True.

  Definition split (h hl hr : heap) : Prop :=
    forall p, (hl p = None \/ hr p = None) /\
      h p = match hl p with
              | None => hr p
              | Some x => Some x
            end.
              
  Definition star (l r : hprop) : hprop :=
    fun h => 
      exists h1 h2, split h h1 h2 /\
        l h1 /\ r h2.
      
  Definition ex (T : Type) (p : T -> hprop) : hprop :=
    fun h => exists x, p x h.

  Ltac doIt := 
    unfold heq, himp, star, emp, split, ex, inj; intros;
    repeat match goal with 
             | [ H : exists x, _ |- _ ] => destruct H
             | [ H : _ /\ _ |- _ ] => destruct H
           end.
  
  Theorem himp_star_comm : forall P Q : hprop, himp (star P Q) (star Q P).
  Proof.
    doIt. do 2 eexists; doIt. split. 2: eauto.
    intro. specialize (H p). intuition; rewrite H in *.
    destruct (x0 p); auto.
    destruct (x p); auto.
  Qed.

  Theorem heq_star_assoc :
    forall P Q R : hprop, heq (star (star P Q) R) (star P (star Q R)).
  Proof. 
    doIt; intuition; doIt.
    exists x1. exists (fun p => match x2 p with
                                  | None => x0 p
                                  | Some x => Some x
                                end); intuition.
    specialize (H p); specialize (H0 p); intuition; doIt.
    rewrite H0 in *. rewrite H4 in *. destruct (x1 p); eauto.
    rewrite H0 in *; rewrite H4 in *. auto.
    specialize (H p); specialize (H0 p); intuition;
    rewrite H0 in *; rewrite H4 in *; eauto.
    rewrite <- H6 in *; auto.
    destruct (x1 p); auto; congruence.
    rewrite H6 in *; auto.
    destruct (x1 p); auto. destruct (x p); eauto; try congruence.
    rewrite H6 in *; auto.
    
    exists x2. exists x0. intuition.
    specialize (H p); specialize (H0 p); intuition; doIt.
    rewrite H0 in *; rewrite H4 in *; auto.

    { exists (fun p => match x p with
                         | Some x => Some x
                         | None => x1 p 
                       end). exists x2.
      intuition; doIt; try specialize (H p); try specialize (H1 p); intuition;
        try rewrite H1 in *; try rewrite H4 in *; auto; try congruence.
      destruct (x p); eauto; congruence.
      destruct (x p); eauto; congruence.
      exists x; exists x1; intuition; doIt.
      specialize (H p); specialize (H1 p); intuition.
      rewrite H1 in *; rewrite H4 in *.
      destruct (x1 p); auto. }
  Qed.

  Theorem heq_star_emp_l : forall P : hprop, heq (star emp P) P.
  Proof.
    doIt. intuition; doIt.
    cutrewrite (h = x0); auto.

    eapply functional_extensionality; intros.
    specialize (H x1). specialize (H2 x1). rewrite H2 in *. intuition.
    exists (fun _ => None). exists h. intuition.
  Qed.

   Theorem himp_subst_p :
     forall P Q R S : hprop,
     himp P S -> himp (star S Q) R -> himp (star P Q) R.
   Proof.
     doIt. eapply H0; clear H0. do 2 eexists. split; [ | eauto ].
     intuition.
   Qed.

   Theorem himp_subst_c :
     forall P Q R S : hprop,
     himp S Q -> himp P (star S R) -> himp P (star Q R).
   Proof.
     doIt. eapply H0 in H1; clear H0. doIt.
     do 2 eexists; split; [ | eauto ]. intuition.
   Qed.

   Theorem himp_star_pure_p :
     forall (P Q : hprop) (F : Prop),
     himp (star (inj F) P) Q -> F -> himp P Q.
   Proof.
     doIt. eapply H. exists (fun _ => None). exists h.
     intuition.
   Qed.

   Theorem himp_star_pure_c :
     forall (P Q : hprop) (F : Prop),
     (F -> himp P Q) -> himp (star (inj F) P) Q.
   Proof.
     doIt. eapply H; auto.
     cutrewrite (h = x0); auto.
     eapply functional_extensionality; intros.
     specialize (H3 x1). specialize (H0 x1).
     rewrite H3 in *. intuition.
   Qed.

   Theorem himp_star_pure_cc :
     forall (P Q : hprop) (p : Prop),
     p -> himp P Q -> himp P (star (inj p) Q).
   Proof.
     doIt. eapply H0 in H1; clear H0.
     exists (fun _ => None). exists h.
     intuition.
   Qed.

   Theorem himp_ex_p :
     forall (T : Type) (P : T -> hprop) (Q : hprop),
     (forall v : T, himp (P v) Q) -> himp (ex T P) Q.
   Proof.
     doIt. eauto.
   Qed.
       
   Theorem himp_ex_c :
     forall (T : Type) (P : T -> hprop) (Q : hprop),
     (exists v : T, himp Q (P v)) -> himp Q (ex T P).
   Proof.
     doIt; eauto.
   Qed.
     
   Theorem heq_ex_star :
     forall (T : Type) (P : T -> hprop) (Q : hprop),
     heq (star (ex T P) Q) (ex T (fun x : T => star (P x) Q)).
   Proof.
     doIt; intuition; doIt. exists x1.
     exists x. exists x0. intuition.
     exists x0. exists x1. intuition. eauto.
   Qed.

End SimpleSepLog.