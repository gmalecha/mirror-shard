Require Import Heaps Memory.
Require Import RelationClasses.

Set Implicit Arguments.
Set Strict Implicit.

Module Type SepState.
  Parameter State : Type.
End SepState.

Module Type SepTheory.
  Declare Module SS : SepState.

  Parameter hprop : Type.
 
  Parameter himp : hprop -> hprop -> Prop.
  
  Parameter heq : hprop -> hprop -> Prop.

  Parameter Refl_himp : Reflexive himp.
  Parameter Trans_himp : Transitive himp.

  Parameter Refl_heq : Reflexive heq.
  Parameter Sym_heq : Symmetric heq.
  Parameter Trans_heq : Transitive heq.

  Notation "a ===> b" := (himp a b) (at level 60).
  Notation "a <===> b" := (heq a b) (at level 60).

  Parameter heq_defn : forall a b, (a ===> b /\ b ===> a) <-> a <===> b.

  Parameter heq_himp : forall a b, a <===> b -> a ===> b.

  (* Definitions *)
  Parameter emp : hprop.

  Parameter inj : Prop -> hprop.

  Parameter star : hprop -> hprop -> hprop.

  Parameter ex : forall (T : Type) (p : T -> hprop), hprop.

  (* star lemmas *)
  Parameter himp_star_comm : forall P Q, 
    (star P Q) ===> (star Q P).

  Parameter heq_star_comm : forall P Q, 
    (star P Q) <===> (star Q P).

  Parameter heq_star_assoc : forall P Q R, 
    (star (star P Q) R) <===> (star P (star Q R)).

  Parameter heq_star_emp_l : forall P, (star emp P) <===> P.

  Parameter heq_star_emp_r : forall P, (star P emp) <===> P.

  Parameter himp_star_frame : forall P Q R S, 
    P ===> Q -> R ===> S -> (star P R) ===> (star Q S).

  Parameter heq_star_frame : forall P Q R S, 
    P <===> Q -> R <===> S -> (star P R) <===> (star Q S).

  Parameter himp_subst_p : forall P Q R S,
    P ===> S -> (star S Q) ===> R ->
    (star P Q) ===> R.

  Parameter himp_subst_c : forall P Q R S,
    S ===> Q -> P ===> (star S R) ->
    P ===> (star Q R).

  Parameter heq_subst : forall P Q R S,
    P <===> S -> (star S Q) <===> R ->
    (star P Q) <===> R.

  Parameter himp_star_cancel : forall P Q R,
    Q ===> R -> (star P Q) ===> (star P R).

  Parameter heq_star_cancel : forall P Q R, 
    Q <===> R -> (star P Q) <===> (star P R).

  (** pure lemmas **)
  Parameter himp_star_pure_p : forall P Q F,
    (star (inj F) P) ===> Q -> (F -> P ===> Q).
  
  Parameter himp_star_pure_c : forall P Q (F : Prop),
    (F -> P ===> Q) -> (star (inj F) P) ===> Q.

  Parameter himp_star_pure_cc : forall P Q (p : Prop),
    p ->
    P ===> Q ->
    P ===> (star (inj p) Q).

  (** ex lemmas **)
  Parameter himp_ex_p : forall T (P : T -> _) Q, 
    (forall v, (P v) ===> Q) -> (ex P) ===> Q.

  Parameter himp_ex_c : forall T (P : T -> _) Q, 
    (exists v, Q ===> (P v)) -> Q ===> (ex P).

  Parameter heq_ex : forall T (P Q : T -> _), 
    (forall v, P v <===> Q v) ->
    ex P <===> ex Q.

  Parameter himp_ex : forall T (P Q : T -> _), 
    (forall v, P v ===> Q v) ->
    ex P ===> ex Q.

  Parameter heq_ex_star : forall T (P : T -> _) Q,
    (star (ex P) Q) <===> (ex (fun x => star (P x) Q)).

  Parameter himp_ex_star : forall T (P : T -> _) Q,
    (star (ex P) Q) ===> (ex (fun x => star (P x) Q)).

  Existing Instance Refl_himp. 
  Existing Instance Trans_himp. 
  Existing Instance Refl_heq.
  Existing Instance Sym_heq. 
  Existing Instance Trans_heq. 

End SepTheory.

Module Type SepTheory_Kernel.
  Declare Module SS : SepState.

  Parameter hprop : Type.
 
  Parameter himp : hprop -> hprop -> Prop.
  
  Parameter heq : hprop -> hprop -> Prop.

  Parameter Refl_himp : Reflexive himp.
  Parameter Trans_himp : Transitive himp.

  Parameter Refl_heq : Reflexive heq.
  Parameter Sym_heq : Symmetric heq.
  Parameter Trans_heq : Transitive heq.

  Notation "a ===> b" := (himp a b) (at level 60).
  Notation "a <===> b" := (heq a b) (at level 60).

  Parameter heq_defn : forall a b, (a ===> b /\ b ===> a) <-> a <===> b.
  
  (* Definitions *)
  Parameter emp : hprop.

  Parameter inj : Prop -> hprop.

  Parameter star : hprop -> hprop -> hprop.

  Parameter ex : forall (T : Type) (p : T -> hprop), hprop.

  (* star lemmas *)
  Parameter himp_star_comm : forall P Q, 
    (star P Q) ===> (star Q P).

  Parameter heq_star_assoc : forall P Q R, 
    (star (star P Q) R) <===> (star P (star Q R)).

  Parameter heq_star_emp_l : forall P, (star emp P) <===> P.

  Parameter himp_subst_p : forall P Q R S,
    P ===> S -> (star S Q) ===> R ->
    (star P Q) ===> R.

  Parameter himp_subst_c : forall P Q R S,
    S ===> Q -> P ===> (star S R) ->
    P ===> (star Q R).

  (** pure lemmas **)
  Parameter himp_star_pure_p : forall P Q F,
    (star (inj F) P) ===> Q -> (F -> P ===> Q).
  
  Parameter himp_star_pure_c : forall P Q (F : Prop),
    (F -> P ===> Q) -> (star (inj F) P) ===> Q.

  Parameter himp_star_pure_cc : forall P Q (p : Prop),
    p ->
    P ===> Q ->
    P ===> (star (inj p) Q).

  (** ex lemmas **)
  Parameter himp_ex_p : forall T (P : T -> _) Q, 
    (forall v, (P v) ===> Q) -> (ex P) ===> Q.

  Parameter himp_ex_c : forall T (P : T -> _) Q, 
    (exists v, Q ===> (P v)) -> Q ===> (ex P).

  Parameter heq_ex_star : forall T (P : T -> _) Q,
    (star (ex P) Q) <===> (ex (fun x => star (P x) Q)).

End SepTheory_Kernel.

Module SepTheory_From_Kernel (Import K : SepTheory_Kernel) <: 
  SepTheory with Module SS := K.SS.

  Include K.

  Theorem heq_himp : forall a b, a <===> b -> a ===> b.
  Proof.
    intros. apply heq_defn in H. intuition.
  Qed.
  
  Theorem heq_star_comm : forall P Q, 
    (star P Q) <===> (star Q P).
  Proof.
    intros; apply heq_defn. intuition; apply himp_star_comm.
  Qed.

  Theorem heq_star_emp_r : forall a, (star a emp) <===> a.
  Proof.
    intros. etransitivity. apply heq_star_comm.
    apply heq_star_emp_l.
  Qed.

  Ltac break_heq := 
    intros;
      repeat match goal with
               | [ H : _ <===> _ |- _ ] => apply heq_defn in H
               | [ |- _ <===> _ ] => apply heq_defn
             end; intuition.

  Theorem himp_star_frame : forall P Q R S, 
    P ===> Q -> R ===> S -> (star P R) ===> (star Q S).
  Proof.
    intros.
    eapply himp_subst_p; try eassumption.
    etransitivity.
    eapply himp_star_comm.
    etransitivity. 2: eapply himp_star_comm.
    eapply himp_subst_p; try eassumption.
    reflexivity.
  Qed.

  Theorem heq_star_frame : forall P Q R S, 
    P <===> Q -> R <===> S -> (star P R) <===> (star Q S).
  Proof.
    break_heq; apply himp_star_frame; eauto.
  Qed.

  Theorem heq_subst : forall P Q R S,
    P <===> S -> (star S Q) <===> R ->
    (star P Q) <===> R.
  Proof.
    break_heq.
    eapply himp_subst_p; try eassumption.
    eapply himp_subst_c; try eassumption.
  Qed.

  Theorem himp_star_cancel : forall P Q R,
    Q ===> R -> (star P Q) ===> (star P R).
  Proof.
    intros. etransitivity. apply himp_star_comm.
    eapply himp_subst_p. eassumption.
    apply himp_star_comm.
  Qed.

  Theorem heq_star_cancel : forall P Q R, 
    Q <===> R -> (star P Q) <===> (star P R).
  Proof.
    break_heq.
    apply himp_star_cancel; try eassumption.
    apply himp_star_cancel; try eassumption.
  Qed.

  Theorem heq_ex : forall T (P Q : T -> _), 
    (forall v, P v <===> Q v) ->
    ex P <===> ex Q.
  Proof.
    break_heq;
    apply himp_ex_p; intros; apply himp_ex_c; exists v;
    specialize (H v); break_heq; auto.
  Qed.    

  Theorem himp_ex_star : forall T (P : T -> _) Q,
    (star (ex P) Q) ===> (ex (fun x => star (P x) Q)).
  Proof.
    intros. generalize (heq_ex_star P Q).
    break_heq.
  Qed.

  Theorem himp_ex : forall T (P Q : T -> _), 
    (forall v, P v ===> Q v) ->
    ex P ===> ex Q.
  Proof.
    intros. 
    apply himp_ex_p; intros; apply himp_ex_c; exists v;
    specialize (H v); break_heq; auto.
  Qed.

End SepTheory_From_Kernel.

Module SepTheory_Rewrites (Import ST : SepTheory).
  
  Require Import Setoid Classes.Morphisms.
  
  Add Parametric Relation : hprop himp
    reflexivity proved by Refl_himp
    transitivity proved by Trans_himp
  as himp_rel.

  Add Parametric Relation : hprop heq
    reflexivity proved by Refl_heq
    symmetry proved by Sym_heq
    transitivity proved by Trans_heq
  as heq_rel.

  Global Add Parametric Morphism : star with
    signature (himp ==> himp ==> himp)
  as star_himp_mor.
    intros. eapply himp_star_frame; eauto.
  Qed.

  Global Add Parametric Morphism : star with
    signature (heq ==> heq ==> heq)
  as star_heq_mor.
    intros. eapply heq_star_frame; eauto.
  Qed.

  Global Add Parametric Morphism T : (@ex T) with 
    signature (pointwise_relation T (heq) ==> heq)
  as ex_heq_mor.
    intros. eapply heq_ex. eauto.
  Qed.

  Global Add Parametric Morphism T : (@ex T) with 
    signature (pointwise_relation T (himp) ==> himp)
  as ex_himp_mor.
    intros. eapply himp_ex. auto.
  Qed.

  Global Add Parametric Morphism : (himp) with 
    signature (heq ==> heq ==> Basics.impl)
  as himp_heq_mor.
    intros. intro. etransitivity.
    symmetry in H. eapply heq_defn in H. eapply (proj1 H).
    etransitivity. eassumption. eapply heq_defn in H0. intuition.
  Qed.

  Global Add Parametric Morphism : (himp) with 
    signature (himp --> himp ++> Basics.impl)
  as himp_himp_mor.
    intros. intro. repeat (etransitivity; eauto).
  Qed.

  Global Add Parametric Morphism : inj with 
    signature (Basics.impl ==> himp)
  as inj_himp_mor.
    intros.
    intros. rewrite <- heq_star_emp_r. 
    eapply himp_star_pure_c. intros.
    rewrite <- heq_star_emp_r with (P := inj y).
    eapply himp_star_pure_cc. eauto.
    reflexivity.
  Qed.

  Global Instance subrelation_heq_himp : subrelation heq himp.
  Proof. repeat red. apply heq_himp. Qed.

  Hint Rewrite heq_star_emp_l heq_star_emp_r : hprop.
  Existing Instance himp_rel_relation.
  Existing Instance heq_rel_relation.

End SepTheory_Rewrites.

Module SepTheory_Ext (ST : SepTheory).
  Require Import List.
  Module Import ST_RW := SepTheory_Rewrites ST.
  Fixpoint functionTypeD (domain : list Type) (range : Type) : Type :=
    match domain with
      | nil => range
      | d :: domain' => d -> functionTypeD domain' range
    end.

  Section param.
    Variable type : Type.
    Variable typeD : type -> Type.

    Definition existsEach (ts : list type) (f : list (@sigT _ typeD) -> ST.hprop ) 
      : ST.hprop :=
      @ST.ex (list (@sigT _ typeD)) (fun env => ST.star (ST.inj (map (@projT1 _ _) env = ts)) (f env)).

    Ltac thinker := 
      repeat match goal with
               | [ H : forall f, ST.himp _ _ _ |- _ ] => rewrite H
               | [ |- _ ] => reflexivity
               | [ |- ST.himp (ST.star (ST.inj _) _) _ ] => 
                 apply ST.himp_star_pure_c ; intros
               | [ |- ST.himp (ST.ex _) _ ] => 
                 apply ST.himp_ex_p ; intros
               | [ |- ST.himp _ (ST.ex (fun x => ST.star (ST.inj (?X = _)) _)) ] => 
                 apply ST.himp_ex_c ; exists nil ; eapply ST.himp_star_pure_cc; [ solve [ eauto ] | ]
               | [ |- ST.himp _ (ST.ex (fun x => ST.star (ST.inj (?X = _)) _)) ] => 
                 apply ST.himp_ex_c ; eexists; eapply ST.himp_star_pure_cc; [ solve [ eauto ] | ]
             end.

    Lemma existsEach_perm : forall (F : list (@sigT _ typeD) -> _) x x',
        ST.heq (existsEach x (fun e => existsEach x' (fun e' => F (e ++ e'))))
               (existsEach x' (fun e' => existsEach x (fun e => F (e ++ e')))).
    Proof.
      intros. eapply ST.heq_defn. split; unfold existsEach;
      revert F; revert x'; induction x; simpl; intros;
        repeat match goal with
                 | [ H : forall f, ST.himp _ _ |- _ ] => rewrite H
                 | [ |- _ ] => reflexivity
                 | [ |- ST.himp (ST.star (ST.inj _) _) _ ] => 
                   apply ST.himp_star_pure_c ; intros
                 | [ |- ST.himp (ST.ex _) _ ] => 
                   apply ST.himp_ex_p ; intros
                 | [ |- ST.himp _ (ST.ex (fun x => ST.star (ST.inj (?X = _)) _)) ] => 
                   apply ST.himp_ex_c ; eexists; eapply ST.himp_star_pure_cc; [ solve [ eauto ] | ]
               end.
    Qed.

    Lemma map_eq_app : forall T U (F : T -> U) ls x y,
      map F ls = x ++ y ->
      exists x' y', ls = x' ++ y' /\ map F x' = x /\ map F y' = y.
    Proof.
      clear. induction ls; destruct x; simpl in *; intros; subst; try congruence.
      exists nil; exists nil; simpl; auto.
      exists nil. simpl. eexists; eauto.
      inversion H; clear H; subst. eapply IHls in H2.
      destruct H2. destruct H. intuition. subst. exists (a :: x0). exists x1. simpl; eauto.
    Qed.
    
    Lemma existsEach_app : forall x x' (F : list (@sigT _ typeD) -> _) ,
      ST.heq (existsEach (x ++ x') F)
             (existsEach x (fun e => existsEach x' (fun e' => F (e ++ e')))).
    Proof.
      intros. eapply ST.heq_defn. split; unfold existsEach;
      revert F; revert x'; induction x; simpl; intros; thinker.
      Focus 2. destruct v; simpl in *; try congruence; reflexivity.
      Focus 2. apply ST.himp_ex_c ; eexists (v ++ v0); eapply ST.himp_star_pure_cc. rewrite map_app. rewrite H. rewrite H0. auto.
      reflexivity.
      change (a :: x ++ x') with ((a :: x) ++ x') in H.
      eapply map_eq_app in H. do 2 destruct H. intuition; subst. thinker.
    Qed.

    Lemma existsEach_nil : forall (F : list (@sigT _ typeD) -> _) ,
      ST.heq (existsEach nil F) (F nil).
    Proof.
      intros. eapply ST.heq_defn. unfold existsEach; split; thinker.
      destruct v; try reflexivity. simpl in *; congruence.
    Qed.

    Lemma heq_existsEach : forall x (F F' : list (@sigT _ typeD) -> _) ,
      (forall G, map (@projT1 _ _) G = x -> ST.heq (F G) (F' G)) ->
      ST.heq (existsEach x F) (existsEach x F').
    Proof.
      intros. eapply ST.heq_ex. intros. apply ST.heq_defn. split; thinker;
      eapply ST.himp_star_pure_cc; eauto; specialize (H _ H0); apply ST.heq_defn in H; intuition.
    Qed.

    Lemma himp_existsEach : forall x (F F' : list (@sigT _ typeD) -> _) ,
      (forall G, map (@projT1 _ _) G = x -> ST.himp (F G) (F' G)) ->
      ST.himp (existsEach x F) (existsEach x F').
    Proof.
      intros. eapply ST.himp_ex. intros. thinker;
      eapply ST.himp_star_pure_cc; eauto; specialize (H _ H0); apply ST.heq_defn in H; intuition.
    Qed.

    Lemma himp_existsEach_p : forall x (F : list (@sigT _ typeD) -> _) F',
      (forall G, map (@projT1 _ _) G = x -> ST.himp (F G) F') ->
      ST.himp (existsEach x F) F'.
    Proof.
      intros. eapply ST.himp_ex_p. intros. eapply ST.himp_star_pure_c. intros.
      eapply H; eauto.
    Qed.

    Lemma himp_existsEach_c : forall x (F : list (@sigT _ typeD) -> _) F',
      (exists G, map (@projT1 _ _) G = x /\ ST.himp F' (F G)) ->
      ST.himp F' (existsEach x F).
    Proof.
      intros. eapply ST.himp_ex_c. intros. destruct H.
      exists x0. intuition. rewrite H1. eapply ST.himp_star_pure_cc; auto. reflexivity. 
    Qed.

    Lemma heq_pushIn : forall P x (F : list (@sigT _ typeD) -> _) ,
      ST.heq (ST.star P (existsEach x F)) (existsEach x (fun e => ST.star P (F e))).
    Proof.
      intros. unfold existsEach; intros.
      rewrite ST.heq_star_comm. rewrite ST.heq_ex_star. eapply ST.heq_ex. intros. 
      repeat rewrite ST.heq_star_assoc. eapply ST.heq_defn; split; thinker; eapply ST.himp_star_pure_cc; eauto.
      rewrite ST.heq_star_comm. reflexivity.
      rewrite ST.heq_star_comm. reflexivity.
    Qed.
    
    Lemma existsEach_cons : forall v vs P,
      ST.heq (existsEach (v :: vs) P)
             (ST.ex (fun x => existsEach vs (fun env => P (@existT _ _ v x :: env)))).
    Proof.
      intros. change (v :: vs) with ((v :: nil) ++ vs). rewrite existsEach_app.
      eapply ST.heq_defn. simpl. split; unfold existsEach; thinker. eapply ST.himp_ex_c. 
      destruct v0; simpl in *; try congruence.
      inversion H; clear H; subst. exists (projT2 s). destruct v0; simpl in *; try congruence.
      eapply ST.himp_ex_c. exists v1. eapply ST.himp_star_pure_cc; eauto. destruct s; simpl; reflexivity.

      eapply ST.himp_ex_c. exists (existT typeD v v0 :: nil). simpl. eapply ST.himp_star_pure_cc; eauto. 
      eapply ST.himp_ex_c. exists v1. eapply ST.himp_star_pure_cc; eauto. reflexivity.
    Qed.

    Lemma existsEach_rev : forall v F,
      ST.heq (existsEach v F) (existsEach (rev v) (fun e => F (rev e))).
    Proof.
      intros; eapply ST.heq_defn; split; revert F; induction v; simpl; intros;
        repeat (rewrite existsEach_nil || rewrite existsEach_cons || rewrite existsEach_app); unfold existsEach; thinker; auto.
      { apply ST.himp_ex_c. exists (rev v1). apply ST.himp_star_pure_cc. subst. rewrite map_rev. reflexivity.
        apply ST.himp_ex_c. exists (@existT _ _ a v0 :: nil). apply ST.himp_star_pure_cc. reflexivity.
        rewrite rev_app_distr. rewrite rev_involutive. reflexivity. }
      { eapply ST.himp_ex_c. destruct v1. simpl in *; congruence. simpl in *. destruct s; simpl in *.
        inversion H0; clear H0; subst. exists t. rewrite rev_app_distr. simpl. rewrite app_ass. simpl.
        apply ST.himp_ex_c. exists (rev v0). apply ST.himp_star_pure_cc. rewrite map_rev. rewrite H. apply rev_involutive.
        destruct v1; try reflexivity. simpl in *; congruence. }
    Qed.

(*
    Lemma interp_existsEach : forall vs P stn st,
      ST.satisfies (existsEach vs P) stn st ->
      exists G, map (@projT1 _ _) G = vs /\ ST.satisfies cs (P G) stn st. 
    Proof.
      intros. apply ST.satisfies_ex in H. destruct H. exists x.
      apply ST.satisfies_star in H. 
      repeat match goal with
               | [ H : exists x, _ |- _ ] => destruct H
               | [ H : _ /\ _ |- _ ] => destruct H
             end.
      apply ST.satisfies_pure in H0. intuition.
      PropXTac.propxFo. eapply ST.HT.split_semp in H; eauto. subst; auto.
    Qed.
*)

  End param.
End SepTheory_Ext.

