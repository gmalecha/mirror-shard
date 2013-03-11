(** SimpleSepTheory.v
 **
 ** A simple implementation of a separation theory based on functional
 ** extensionality.
 **)
Require Import MirrorShard.SepTheory.
Require Import RelationClasses.

Set Implicit Arguments.
Set Strict Implicit.

Module SimpleSepLog_Kernel <: SepTheory_Kernel.
  Require Import FunctionalExtensionality.

  Definition heap := nat -> option nat.

  Definition hprop := heap -> Prop.

  Definition himp (l r : hprop) : Prop :=
    forall h, l h -> r h.

  Global Instance Refl_himp : Reflexive himp.
  Proof. repeat red; intuition. Qed.

  Global Instance Trans_himp : Transitive himp.
  Proof. repeat red; intuition. Qed.

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
    unfold himp, star, emp, split, ex, inj; intros;
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

  Theorem himp_star_assoc :
    forall P Q R : hprop, himp (star (star P Q) R) (star P (star Q R)).
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
  Qed.

  Theorem himp_star_emp_p : forall P : hprop, himp (star emp P) P.
  Proof.
    doIt.
    cutrewrite (h = x0); auto.

    eapply functional_extensionality; intros.
    specialize (H x1). specialize (H2 x1). rewrite H2 in *. intuition.
  Qed.

  Theorem himp_star_emp_c : forall P : hprop, himp P (star emp P).
  Proof.
    doIt. exists (fun _ => None). exists h. intuition.
  Qed.

  Theorem himp_star_frame : forall P Q R S, 
    himp P Q -> himp R S -> himp (star P R) (star Q S).
  Proof.
    doIt. exists x; exists x0. intuition.
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
      (forall v : T, himp (P v) Q) -> himp (ex P) Q.
  Proof.
    doIt. eauto.
  Qed.
  
  Theorem himp_ex_c :
    forall (T : Type) (P : T -> hprop) (Q : hprop),
      (exists v : T, himp Q (P v)) -> himp Q (ex P).
  Proof.
    doIt; eauto.
  Qed.

  Theorem himp_ex_star : forall T (P : T -> _) Q,
    himp (star (ex P) Q) (ex (fun x => star (P x) Q)).
  Proof.
    doIt. exists x1. exists x. exists x0. intuition.
  Qed.

  Theorem himp_star_ex : forall T (P : T -> _) Q,
    himp (ex (fun x => star (P x) Q)) (star (ex P) Q).
  Proof.
    doIt. exists x0; exists x1. intuition eauto.
  Qed.

End SimpleSepLog_Kernel.

Module SimpleSepLog := SepTheory_From_Kernel SimpleSepLog_Kernel.
