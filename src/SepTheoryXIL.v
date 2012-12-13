Require Import Heaps.
Require Import PropX PropXTac PropXRel.
Require Import SepTheory.
Require IL.

Require Import RelationClasses.

Set Implicit Arguments.
Set Strict Implicit.

Module SepTheoryXIL_Kernel (SM : SeparationMemory)
  <: SepTheory_Kernel.
  Definition memType := SM.smem.
  Definition pcType := IL.W.
  Definition stateType := (IL.settings * IL.state)%type.

  Definition hprop' sos := 
    IL.settings -> memType -> propX pcType stateType sos.

  Definition hprop := hprop' nil.

  Definition himp (l r : hprop) : Prop :=
    forall cs stn m, interp cs (l stn m) -> interp cs (r stn m).
  
  Definition heq (l r : hprop) : Prop :=
    forall cs stn m, interp cs (l stn m) <-> interp cs (r stn m).

  Global Instance  Refl_himp : Reflexive himp.
  Proof. repeat red. intuition. Qed.
    
  Global Instance Trans_himp : Transitive himp.
  Proof. repeat red. intuition. Qed.

  Global Instance Refl_heq : Reflexive heq.
  Proof. repeat red; intuition. Qed.
  
  Global Instance Sym_heq : Symmetric heq.
  Proof. repeat red; intuition; firstorder. Qed.

  Global Instance Trans_heq : Transitive heq.
  Proof. 
    repeat red; unfold heq in *; intuition. 
    eapply H0. eapply H. auto.
    eapply H. eapply H0. auto.
  Qed.

  Local Notation "a ===> b" := (himp a b) (at level 60).
  Local Notation "a <===> b" := (heq a b) (at level 60).

  Definition heq_defn : forall a b, (a ===> b /\ b ===> a) <-> a <===> b.
  Proof.
    unfold himp, heq; intuition; firstorder.
  Qed.
  
  (* Definitions *)
  Definition injX' {sos} (p : propX pcType stateType sos) : hprop' sos :=
    fun _ mem => PropX.And p (PropX.Inj (mem = SM.smem_emp)).

  Definition injX : propX pcType stateType nil -> hprop := @injX' nil.

  Definition inj' {sos} (p : Prop) : hprop' sos :=
    injX' (PropX.Inj p).

  Definition inj : Prop -> hprop := @inj' nil.

  Definition emp' {sos} : hprop' sos := inj' True.

  Definition emp : hprop := @emp' nil.

  Definition star' {sos} (l r : hprop' sos) : hprop' sos :=
    fun stn m =>
      PropX.Exists (fun ml : memType => PropX.Exists (fun mr : memType =>
        PropX.And (PropX.Inj (SM.split m ml mr)) (And (l stn ml) (r stn mr)))).

  Definition star : hprop -> hprop -> hprop := @star' nil.

  Definition ex' {sos} (T : Type) (p : T -> hprop' sos) : hprop' sos :=
    fun stn m =>
      PropX.Exists (fun x : T => p x stn m).

  Definition ex : forall (T : Type), (T -> hprop) -> hprop := @ex' nil.

  (* himp/heq lemmas *)
  Theorem himp_star_comm : forall P Q, (star P Q) ===> (star Q P).
  Proof.
    unfold star, himp; simpl; intros. propxIntuition.
    propxFo. apply simplify_fwd in H. apply simplify_fwd in H2.
    do 2 eexists; intuition; [ apply SM.split_comm; eassumption | | ]; eassumption.
  Qed.

  Theorem heq_star_assoc : forall P Q R, 
    heq (star (star P Q) R) (star P (star Q R)).
  Proof.
    unfold star, heq, himp; simpl; intros.
    propxFo.
    { destruct (SM.split_assoc _ _ _ _ _ H0 H1); eauto; intuition.
      repeat match goal with
               | [ |- exists x , _ ] => eexists
               | [ |- _ /\ _ ] => split
               | [ |- _ ] => apply simplify_fwd'; try eassumption
             end; eassumption. }
    { apply SM.split_comm in H0. apply SM.split_comm in H2. destruct (SM.split_assoc _ _ _ _ _ H0 H2); eauto; intuition.
      repeat match goal with
               | [ |- exists x , _ ] => eexists
               | [ |- _ /\ _ ] => split
               | [ |- _ ] => apply simplify_fwd'; try eassumption
             end; eauto using SM.split_comm. }
  Qed.

  Theorem heq_star_emp_l : forall P, heq (star emp P) P.
  Proof.
    intros. unfold heq, star in *; intuition; propxFo; subst.
    eapply SM.split_emp in H0. subst. auto.
    exists SM.smem_emp. exists m. intuition.
    2: propxFo. eapply SM.split_emp. reflexivity.
  Qed.

  Theorem himp_subst_p : forall P Q R S,
    himp P S -> himp (star S Q) R ->
    himp (star P Q) R.
  Proof. 
    unfold himp, star, interp; intros; propxFo; propxIntuition.
    eapply H0; clear H0. propxFo.
    eapply simplify_fwd in H1. simpl in H1. destruct H1. destruct H0.
    do 2 eexists; intuition eauto.
    eapply simplify_fwd'. eapply H. apply simplify_bwd in H0. apply H0.
  Qed.

  Theorem himp_subst_c : forall P Q R S,
    himp S Q -> himp P (star S R) ->
    himp P (star Q R).
  Proof.
    unfold himp, star, interp; intros. eapply H0 in H1; clear H0. propxFo.
    eapply simplify_fwd in H1. simpl in H1. destruct H1. destruct H0.
    do 2 eexists; intuition eauto.
    eapply simplify_fwd'. eapply H. apply simplify_bwd in H0. apply H0.
  Qed.

  Theorem himp_star_pure_p : forall P Q F,
    himp (star (inj F) P) Q -> (F -> himp P Q).
  Proof.
    unfold himp, star, inj; intros.
    apply H. propxFo. exists SM.smem_emp. exists m.
    intuition. apply SM.split_emp; reflexivity.
    apply simplify_fwd. assumption.
  Qed.

  Theorem himp_star_pure_c : forall P Q (F : Prop),
    (F -> himp P Q) -> himp (star (inj F) P) Q.
  Proof.
    unfold himp, star, inj; intros.
    apply H; clear H. propxFo. propxFo. subst.
    apply SM.split_emp in H0. subst; assumption.
  Qed.

  Theorem himp_star_pure_cc : forall P Q (p : Prop),
    p ->
    himp P Q ->
    himp P (star (inj p) Q).
  Proof.
    unfold himp, star, inj; intros.
    apply H0 in H1; clear H0.
    propxFo. exists SM.smem_emp. exists m. intuition.
    apply SM.split_emp; reflexivity. apply simplify_fwd'. assumption.
  Qed.

  Theorem himp_ex_p : forall T (P : T -> _) Q, 
    (forall v, himp (P v) Q) -> himp (ex P) Q.
  Proof.
    unfold himp, ex; intros. apply simplify_fwd in H0. simpl in *.
    destruct H0. propxFo. eapply H; eauto.
  Qed.

  Theorem himp_ex_c : forall T (P : T -> _) Q, 
    (exists v, himp Q (P v)) -> himp Q (ex P).
  Proof.
    unfold himp, ex; intros. apply simplify_fwd in H0. simpl in *.
    propxFo. exists x. propxFo.
  Qed.

  Theorem heq_ex_star : forall T (P : T -> _) Q,
    heq (star (ex P) Q) (ex (fun x => star (P x) Q)).
  Proof.
    unfold heq, himp, star, ex; intuition; propxIntuition; propxFo.
    { exists x1. do 2 eexists. intuition eauto using simplify_fwd. }
    { do 2 eexists. intuition eauto using simplify_fwd. }
  Qed.

End SepTheoryXIL_Kernel.

(*
Module SepTheoryXIL := SepTheory_From_Kernel SepTheoryXIL_Kernel.
*)