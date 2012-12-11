Require Import Heaps Memory.
Require Import PropX PropXTac.
Require Import SepTheory.
Require IL.

Require Import RelationClasses.

Set Implicit Arguments.
Set Strict Implicit.

Module SepStateIL <: SepState.
  Definition memType := W -> option W.

  Record State' :=
  { 
  mem      : memType
  }.

  Definition State := State'.

  Definition disjoint_mem (l r : W -> option W) : Prop :=
    forall p, l p = None \/ r p = None.

  Definition join_mem (l r : W -> option W) : W -> option W :=
    fun p => match l p with
               | None => r p
               | Some w => Some w
             end.

  Definition split (t l r : State) : Prop :=
(*    t.(settings) = l.(settings) /\ t.(settings) = r.(settings) /\ *)
    disjoint_mem l.(mem) r.(mem) /\
    forall p, t.(mem) p = (join_mem l.(mem) r.(mem)) p.

End SepStateIL.

Module SepTheoryX <: SepTheory_Kernel with Module SS := SepStateIL.
  Module SS := SepStateIL.

  Import SS.

  Let pcType := W.
  Let stateType := IL.state.

  Definition hprop := IL.settings -> memType -> propX pcType stateType nil.

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

  Notation "a ===> b" := (himp a b) (at level 60).
  Notation "a <===> b" := (heq a b) (at level 60).

  Definition heq_defn : forall a b, (a ===> b /\ b ===> a) <-> a <===> b.
  Proof.
    unfold himp, heq; intuition; firstorder.
  Qed.
  
  (* Definitions *)
  Definition injX (p : propX pcType stateType nil) : hprop :=
    fun _ mem => PropX.And p (PropX.Inj (forall p, mem p = None)).

  Definition inj (p : Prop) : hprop :=
    injX (PropX.Inj p).

  Definition emp : hprop :=
    inj True.

  Definition star (l r : hprop) : hprop :=
    fun stn m =>
      let s := {| mem := m |} in
      PropX.Exists (fun ml : State => PropX.Exists (fun mr : State =>
        PropX.And (PropX.Inj (split s ml mr)) (And (l stn ml.(mem)) (r stn mr.(mem))))).

  Definition ex (T : Type) (p : T -> hprop) : hprop :=
    fun stn m =>
      PropX.Exists (fun x : T => p x stn m).

  (* himp/heq lemmas *)
  Theorem himp_star_comm : forall P Q, (star P Q) ===> (star Q P).
  Proof.
  Admitted.

  Theorem heq_star_assoc : forall P Q R, 
    heq (star (star P Q) R) (star P (star Q R)).
  Proof.
  Admitted.

  Theorem heq_star_emp_l : forall P, heq (star emp P) P.
  Proof.
    intros. unfold heq in *; intuition. (*
    eapply himp_star_emp_p. reflexivity.
    eapply himp_star_emp_c. reflexivity.
*)
  Admitted.

  Theorem himp_subst_p : forall P Q R S,
    himp P S -> himp (star S Q) R ->
    himp (star P Q) R.
  Proof. 
(*
    unfold himp, star, interp; intros; propxIntuition.
    specialize (H s x). specialize (H0 s m).
    eapply Imply_E. eapply valid_weaken. eapply H0. firstorder.
    propxIntuition. eauto. eapply Imply_E. eapply valid_weaken.
    eauto. firstorder. econstructor; firstorder.
*)
  Admitted.

  Theorem himp_subst_c : forall P Q R S,
    himp S Q -> himp P (star S R) ->
    himp P (star Q R).
  Proof.
(*
    unfold himp, star, interp; intros.
    eapply Imply_I. eapply valid_extend.
    eapply Imply_E. eapply valid_weaken. 
    specialize (H0 s m). eassumption. firstorder. eauto.
    propxIntuition; eauto.
    eapply Imply_E. eapply valid_weaken. eapply H. firstorder.
    econstructor; firstorder.
*)
  Admitted.

  Theorem himp_star_pure_p : forall P Q F,
    himp (star (inj F) P) Q -> (F -> himp P Q).
  Proof.
(*
    unfold himp, star, inj; intros.
    specialize (H s m).
    unfold interp in *. propxIntuition.
    eapply Imply_E. eapply valid_weaken. eapply H. firstorder.
    eapply Exists_I. instantiate (1 := HT.smem_emp).
    eapply Exists_I. instantiate (1 := m). propxIntuition.
    eapply HT.split_a_semp_a.
    eapply valid_weaken. eassumption. firstorder. eapply HT.semp_smem_emp.
*)
  Admitted.

  Theorem himp_star_pure_c : forall P Q (F : Prop),
    (F -> himp P Q) -> himp (star (inj F) P) Q.
  Proof.
(*
    unfold himp, star, inj, interp; intros. propxIntuition.
    specialize (H H1). eapply PropX.Imply_E. eapply valid_weaken. eauto. firstorder.
    apply HT.split_semp in H0; auto. subst.
    constructor. firstorder.
*)
  Admitted.

  Theorem himp_star_pure_cc : forall P Q (p : Prop),
    p ->
    himp P Q ->
    himp P (star (inj p) Q).
  Proof.
(*
    unfold himp, star, inj, interp; intros. propxIntuition; eauto using HT.semp_smem_emp, HT.split_a_semp_a.
    eapply Imply_E. eapply valid_weaken; eauto. firstorder.
    econstructor. firstorder.
*)
  Admitted.

  Theorem himp_ex_p : forall T (P : T -> _) Q, 
    (forall v, himp (P v) Q) -> himp (ex P) Q.
  Proof.
(*
    intros. unfold himp, ex in *; simpl in *; intros. unfold interp in *. propxIntuition.
    eapply Imply_E. eapply valid_weaken; eauto. firstorder. econstructor; firstorder.
*)
  Admitted.

  Theorem himp_ex_c : forall T (P : T -> _) Q, 
    (exists v, himp Q (P v)) -> himp Q (ex P).
  Proof.
(*
    intros. unfold himp, ex in *; simpl in *; intros. unfold interp in *.
    destruct H. propxIntuition. instantiate (1 := x).
    eapply Imply_E. eapply valid_weaken; eauto. firstorder. eauto.
*)
  Admitted.

  Theorem heq_ex_star : forall T (P : T -> _) Q,
    heq (star (ex P) Q) (ex (fun x => star (P x) Q)).
  Proof.
(*
    unfold heq, himp, star, ex, interp; intuition; propxIntuition; eauto.
*)
  Admitted.

End SepTheoryX.
