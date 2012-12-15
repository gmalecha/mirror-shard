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
    forall cs stn m, interp cs (l stn m ---> r stn m).
  
  Definition heq (l r : hprop) : Prop :=
    himp l r /\ himp r l.

  Global Instance  Refl_himp : Reflexive himp.
  Proof. 
    repeat red. propxFo. apply PropX.Imply_I.
    constructor. firstorder.
  Qed.
    
  Global Instance Trans_himp : Transitive himp.
  Proof. 
    repeat red. intuition.
    specialize (H cs stn m).
    specialize (H0 cs stn m).
    propxFo.
    eapply Imply_I.
    eapply Imply_E. 
    2: eapply Imply_E. 3: econstructor; firstorder.
    2: eapply valid_weaken. 2: eassumption. 2: firstorder.
    eapply valid_weaken. eassumption. firstorder.
  Qed.

  Global Instance Refl_heq : Reflexive heq.
  Proof. repeat red; intuition. Qed.
  
  Global Instance Sym_heq : Symmetric heq.
  Proof. repeat red; intuition; firstorder. Qed.

  Global Instance Trans_heq : Transitive heq.
  Proof. 
    repeat red; unfold heq in *; intuition; etransitivity; eassumption.
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
    unfold star, star', himp, interp; simpl; intros. propxIntuition.
    auto using SM.split_comm.
  Qed.

  Theorem heq_star_assoc : forall P Q R, 
    heq (star (star P Q) R) (star P (star Q R)).
  Proof.
    unfold star, star', heq, himp, interp; simpl; intros; intuition. 
    { propxIntuition'. destruct (SM.split_assoc _ _ _ _ _ H H0); eauto; intuition.
      propxIntuition; try eassumption. }
    { propxIntuition'. apply SM.split_comm in H. apply SM.split_comm in H0.
      destruct (SM.split_assoc _ _ _ _ _ H H0); eauto; intuition.
      propxIntuition; try eauto using SM.split_comm. }
  Qed.

  Theorem heq_star_emp_l : forall P, heq (star emp P) P.
  Proof.
    intros. unfold heq, himp, star, star', emp, emp', inj', injX' in *; intuition; propxFo; subst; unfold interp. 
    { propxIntuition. subst. eapply SM.split_emp in H. subst. propxIntuition. }
    { propxIntuition; eauto using SM.split_emp. apply SM.split_emp; auto. }
  Qed.

  Theorem himp_subst_p : forall P Q R S,
    himp P S -> himp (star S Q) R ->
    himp (star P Q) R.
  Proof.
    intros. etransitivity. 2: eassumption.
    unfold himp, star, star', interp; intros; propxIntuition. eassumption.
    eapply Imply_E. eapply valid_weaken. eapply H. firstorder. propxIntuition.
  Qed.

  Theorem himp_subst_c : forall P Q R S,
    himp S Q -> himp P (star S R) ->
    himp P (star Q R).
  Proof.
    intros; etransitivity; try eassumption. clear - H.
    unfold himp, star, star', interp; intros; propxIntuition. eassumption.
    eapply Imply_E. eapply valid_weaken. eapply H. firstorder. propxIntuition.
  Qed.

  Theorem himp_star_pure_p : forall P Q F,
    himp (star (inj F) P) Q -> (F -> himp P Q).
  Proof.
    unfold himp, star, star', inj, inj', injX'; intros.
    eapply Imply_I. eapply Imply_E. eapply valid_weaken.
    eapply H. firstorder.
    propxIntuition; eauto. eapply SM.split_emp; auto.
  Qed.

  Theorem himp_star_pure_c : forall P Q (F : Prop),
    (F -> himp P Q) -> himp (star (inj F) P) Q.
  Proof.
    unfold himp, star, star', inj, inj', injX', interp; intros.
    propxIntuition. eapply Imply_E.
    eapply valid_weaken. eapply H; auto. firstorder.
    subst. apply SM.split_emp in H0. subst.
    propxIntuition.
  Qed.

  Theorem himp_star_pure_cc : forall P Q (p : Prop),
    p ->
    himp P Q ->
    himp P (star (inj p) Q).
  Proof.
    unfold himp, star, star', inj, inj', injX', interp; intros.
    propxIntuition; eauto. 
    apply SM.split_emp. reflexivity.
    eapply Imply_E. eapply valid_weaken. eapply H0; auto. firstorder.
    propxIntuition.
  Qed.

  Theorem himp_ex_p : forall T (P : T -> _) Q, 
    (forall v, himp (P v) Q) -> himp (ex P) Q.
  Proof.
    unfold himp, star, star', inj, inj', injX', ex, ex', interp; intros.
    propxIntuition; eauto. 
    eapply Imply_E. eapply valid_weaken. eapply H; auto. firstorder.
    propxIntuition.
  Qed.

  Theorem himp_ex_c : forall T (P : T -> _) Q, 
    (exists v, himp Q (P v)) -> himp Q (ex P).
  Proof.
    unfold himp, star, star', inj, inj', injX', ex, ex', interp; intros.
    destruct H. propxIntuition. eapply Imply_E. 
    eapply valid_weaken. eapply H; auto. firstorder.
    propxIntuition.
  Qed.

  Theorem heq_ex_star : forall T (P : T -> _) Q,
    heq (star (ex P) Q) (ex (fun x => star (P x) Q)).
  Proof.
    unfold heq, himp, star, star', inj, inj', injX', ex, ex', interp; intuition;
      propxIntuition; eauto.
  Qed.

End SepTheoryXIL_Kernel.
