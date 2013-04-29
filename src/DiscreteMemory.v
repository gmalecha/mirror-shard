Require Import Heaps.
Require Import Setoid.
Require Import ExtLib.Data.HList.
Require Import List.

Module Type DiscreteMemory.
  Parameter addr : Type.
  
  Parameter all_addr : list addr.
  
  Parameter NoDup_all_addr : NoDup all_addr.
End DiscreteMemory.

(** A permission-like view on top of concrete memories **)
Module DiscreteHeap (B : Memory)
                    (BD : DiscreteMemory with Definition addr := B.addr) 
                 <: SeparationMemory with Module M := B.
  Module Import M := B.

  Instance EqDec_addr : EquivDec.EqDec addr (@eq addr) := addr_dec.

  Definition smem' dom : Type := hlist (fun _ : addr => option value)%type dom.

  Fixpoint smem_emp' (ls : list addr) : smem' ls :=
    match ls with
      | nil => Hnil
      | a :: b => Hcons None (smem_emp' b)
    end.
  Fixpoint disjoint' dom : smem' dom -> smem' dom -> Prop :=
    match dom with
      | nil => fun _ _ => True
      | a :: b => fun m1 m2 => 
           (hlist_hd m1 = None \/ hlist_hd m2 = None) 
        /\ disjoint' _ (hlist_tl m1) (hlist_tl m2)
    end.
  Fixpoint join' dom : smem' dom -> smem' dom -> smem' dom :=
    match dom with
      | nil => fun _ _ => Hnil
      | a :: b => fun m1 m2 => 
        Hcons 
        match hlist_hd m1 with
          | None => hlist_hd m2
          | Some x => Some x
        end
        (join' _ (hlist_tl m1) (hlist_tl m2))
    end.

  Fixpoint relevant' (ls : list addr) : smem' ls -> list addr :=
    match ls with
      | nil => fun _ => nil
      | a :: b => fun x => 
        match hlist_hd x with
          | None => relevant' _ (hlist_tl x)
          | Some _ => a :: relevant' _ (hlist_tl x)
        end
    end.
  
  Fixpoint smem_get' dom : addr -> smem' dom -> option value :=
    match dom as dom return addr -> smem' dom -> option value with 
      | nil => fun _ _ => None
      | a :: b => fun a' m =>
        if addr_dec a a' then 
          hlist_hd m
        else
          smem_get' b a' (hlist_tl m)
    end.

  Fixpoint smem_set' dom : addr -> value -> smem' dom -> option (smem' dom) :=
    match dom as dom return addr -> value -> smem' dom -> option (smem' dom) with 
      | nil => fun _ _ _ => None
      | a :: b => fun p v m =>
        if addr_dec a p then
          match hlist_hd m with
            | None => None
            | Some _ => Some (Hcons (Some v) (hlist_tl m))
          end
        else
          match smem_set' b p v (hlist_tl m) with
            | None => None
            | Some tl => Some (Hcons (hlist_hd m) tl)
          end
    end.

  Fixpoint models' dom (sm : smem' dom) (m : B.mem) : Prop :=
    match sm with
      | Hnil => True
      | Hcons p _ a b =>
        match a with
          | None => True
          | Some x => 
            B.mem_get m p = Some x
        end /\ models' _ b m
    end.

  Definition smem : Type := smem' BD.all_addr.

  Definition smem_eqv : smem -> smem -> Prop := @eq smem.

  Definition smem_emp : smem := smem_emp' BD.all_addr.

  Definition smem_get := @smem_get' BD.all_addr.

  Definition smem_set := @smem_set' BD.all_addr.

  Definition disjoint (m1 m2 : smem) : Prop :=
    disjoint' _ m1 m2.

  Definition join (m1 m2 : smem) : smem := 
    join' _ m1 m2.

  Definition split (m ml mr : smem) : Prop :=
    disjoint ml mr /\ m = join ml mr.

  Definition semp (m : smem) : Prop :=
    m = smem_emp.

  Definition models (m : smem) (m' : B.mem) : Prop :=
    models' _ m m'.

  Definition in_domain p m : Prop :=
    (smem_get p m = None) -> False.

  Definition same_domain m1 m2 : Prop :=
    forall p, in_domain p m1 <-> in_domain p m2.

  Theorem Reflexive_eqv : Reflexive smem_eqv.
  Proof. intuition. Qed.

  Theorem Symmetric_eqv : Symmetric smem_eqv.
  Proof. intuition. Qed.

  Theorem Transitive_eqv : Transitive smem_eqv.
  Proof. unfold smem_eqv; intuition. Qed.

  Theorem models_respects : forall s s' m,
    smem_eqv s s' ->
    (models s m <-> models s' m).
  Proof. unfold smem_eqv; intuition subst; auto. Qed.
 
  Theorem smem_get_respects : forall a s s',
    smem_eqv s s' -> smem_get a s = smem_get a s'.
  Proof. unfold smem_eqv; intuition subst; auto. Qed.    

  Theorem smem_set_respects : forall a v s s',
    smem_eqv s s' -> smem_set a v s = smem_set a v s'.
  Proof. unfold smem_eqv; intuition subst; auto. Qed.    

  Theorem split_respects : forall s1 s1' s2 s2' s3 s3',
    smem_eqv s1 s1' -> smem_eqv s2 s2' -> smem_eqv s3 s3' ->
    (split s1 s2 s3 <-> split s1' s2' s3').
  Proof. unfold smem_eqv; intuition subst; auto. Qed.

  Theorem split_emp : forall a c,
    split a smem_emp c <-> smem_eqv a c.
  Proof.
    unfold split, smem_emp, smem_eqv, disjoint, join, smem.
    generalize dependent BD.all_addr.
    induction l; simpl in *; intros.
    { intuition; subst; auto; rewrite hlist_nil_eta with (h := c); eauto with typeclass_instances. }
    { intuition subst; rewrite hlist_eta with (h := c); eauto with typeclass_instances; f_equal;
      eapply IHl; intuition. }
  Qed.
 
  Theorem split_comm : forall a b c,
    split a b c -> split a c b.
  Proof. 
    unfold split, join, disjoint, smem.
    generalize dependent BD.all_addr.
    induction l; simpl in *; intros; auto.
    destruct H. destruct H. subst.
    destruct (IHl _ _ _ (conj H1 eq_refl)). 
    rewrite H2. intuition; rewrite H3; try f_equal.
    destruct (hlist_hd c); auto.
    destruct (hlist_hd b); auto.
  Qed.

  Theorem split_assoc : forall a b c d e,
    split a b c -> split b d e ->
    exists f, split a d f /\ split f e c.
  Proof.
    unfold split, join, disjoint, smem.
    generalize dependent BD.all_addr.
    induction l; simpl in *; intros; auto.
    { intuition subst. exists Hnil; intuition. }
    { repeat match goal with
               | [ H : _ /\ _ |- _ ] => destruct H
               | [ H : _ = _ |- _ ] => rewrite H
             end; subst; simpl in *.
      destruct (IHl _ _ _ _ _ (conj H4 eq_refl) (conj H2 eq_refl)); clear IHl.
      repeat match goal with
               | [ H : _ /\ _ |- _ ] => destruct H
               | [ H : _ = _ |- _ ] => rewrite H
             end; subst; simpl in *.
      intuition; eexists; intuition; repeat match goal with
                          | [ H : _ /\ _ |- _ ] => destruct H
                          | [ H : _ = _ |- _ ] => rewrite H in *
                        end; subst; simpl in *; eauto.
      destruct (hlist_hd d); auto.
      destruct (hlist_hd d); auto; try congruence.
      destruct (hlist_hd d); auto. }
  Qed.

  Theorem split_in_domain : forall a b c,
    split a b c ->
      forall p, in_domain p a <-> (in_domain p b \/ in_domain p c).
  Proof.
    unfold split, join, disjoint, in_domain, smem_get, smem.
    generalize BD.all_addr; induction l; simpl in *; intros.
    intuition.
    destruct (addr_dec a p); subst.
    { intuition. rewrite H0 in *. subst; simpl in *; auto. 
      rewrite H0 in *. subst. simpl in *; auto.
      rewrite H0 in *; subst. destruct (hlist_hd b); auto.
      destruct (hlist_hd b); auto. subst; simpl in *; auto. }
    { destruct H. destruct H. subst. simpl in *. eauto. }
  Qed.      

  Theorem split_disjoint : forall a b c,
    split a b c ->
      (forall p, in_domain p b -> ~in_domain p c).
  Proof.
    unfold split, disjoint, join, smem, in_domain, smem_get.
    generalize BD.all_addr. induction l; simpl; intros; auto.
    destruct (addr_dec a p); subst; intuition; subst; eauto.
  Qed.

  Theorem smem_get_sound : forall s m,
    models s m ->
    forall a v, smem_get a s = Some v ->
                M.mem_get m a = Some v.
  Proof.
    unfold models, smem_get, mem_get, smem.
    generalize BD.all_addr. induction l; simpl in *; intros; try congruence.
    rewrite hlist_eta with (h := s) in H; eauto with typeclass_instances.
    simpl in *; intuition.
    destruct (addr_dec a a0); subst.
    rewrite H0 in *; auto.
    intuition eauto.
  Qed.

  Ltac simp ext :=
    intros; simpl in *;
    repeat (instantiate; 
      match goal with
        | [ H : prod _ _ |- _ ] => destruct H
        | [ H : Some _ = Some _ |- _ ] =>
          inversion H; clear H; try subst
        | [ H : _ = _ |- _ ] => rewrite H in *
        | [ H : NoDup (_ :: _) |- _ ] =>
          inversion H; clear H; subst
        | [ H : context [ addr_dec ?A ?B ] |- _ ] => 
          destruct (addr_dec A B); subst
        | [ |- context [ addr_dec ?A ?B ] ] => 
          destruct (addr_dec A B); subst
        | [ H : match ?X with 
                  | Some _ => _
                  | None => _
                end = _ |- _ ] => 
          generalize dependent H; case_eq X; intros
        | [ H : match ?X with 
                  | Some _ => _
                  | None => _
                end |- _ ] => 
          generalize dependent H; case_eq X; intros
        | [ H : models' (_ :: _) ?M _ |- _ ] =>
          match M with
            | Hcons _ _ => fail 1
            | _ => rewrite (hlist_eta M) in H
          end
        | [ |- models' (_ :: _) ?M _ ] =>
          match M with
            | Hcons _ _ => fail 1
            | _ => rewrite (hlist_eta M)
          end
        | [ H : smem' nil |- _ ] => 
          rewrite (hlist_eta H) in *
        | [ H : exists x, _ |- _ ] => destruct H
        | [ H : _ /\ _ |- _ ] => destruct H
        | [ |- _ ] => congruence
        | [ |- _ ] => ext
      end; simpl in * ).


  Lemma models_set_not_in : forall l m sm p v,
    models' l sm m ->
    ~In p l ->
    forall m', mem_set m p v = Some m' ->
    models' l sm m'.
  Proof.
    induction l; try solve [ simp intuition ].
      simp auto.
      destruct (addr_dec a p); destruct (in_dec addr_dec p l); subst; try solve [ intuition ].
      split; eauto. erewrite B.mem_get_set_neq; eauto. 
      split; eauto. 
  Qed.

  Lemma smem_set_same_domain : forall s,
    forall a v s', smem_set a v s = Some s' ->
    same_domain s s'.
  Proof.
    generalize BD.NoDup_all_addr.
    unfold models, same_domain, in_domain, smem_set, smem_get, smem.
    generalize BD.all_addr. induction l; simpl in *; intros; try congruence.
    destruct (addr_dec a a0); subst.
    { destruct (hlist_hd s); try congruence. inversion H0; clear H0; subst; simpl in *.
      destruct (addr_dec a0 p); auto. intuition try congruence. intuition. }
    { revert H0. case_eq (smem_set' l a0 v (hlist_tl s)); intros; try congruence.
      inversion H1; clear H1; subst; simpl in *.
      destruct (addr_dec a p). intuition. eapply IHl. inversion H; auto. eauto. }
  Qed.

  Theorem smem_set_sound' : forall s m,
    models s m ->
    forall a v s', smem_set a v s = Some s' ->
    exists m', M.mem_set m a v = Some m' /\ models s' m'. 
  Proof.
    generalize BD.NoDup_all_addr.
    unfold models, smem_set, mem_get, smem.
    generalize BD.all_addr. induction l; simpl in *; intros; try congruence.
    rewrite hlist_eta with (h := s) in H0; eauto with typeclass_instances.
    simpl in *; intuition.
    destruct (addr_dec a a0); subst.
    { destruct (hlist_hd s); try congruence.
      inversion H1; clear H1; subst.
      simpl in *.
      case_eq (mem_set m a0 v); intros. eexists; split; eauto.
      intuition; eauto using B.mem_get_set_eq.
      eapply models_set_not_in; eauto.
      inversion H; auto.
      
      exfalso. eapply mem_get_mem_set; eauto. congruence. }

    { revert H1.
      case_eq (smem_set' l a0 v (hlist_tl s)); intros.
      inversion H1; clear H1; subst. eapply IHl in H0; eauto.
      destruct H0. simpl. eexists; intuition eauto. 
      destruct (hlist_hd s); auto.
      erewrite mem_get_set_neq; eauto. inversion H; auto. 
      
      congruence. }
  Qed.

  Theorem smem_set_sound : forall s m,
    models s m ->
    forall a v s', smem_set a v s = Some s' ->
    same_domain s s' /\
    exists m', M.mem_set m a v = Some m' /\ models s' m'. 
  Proof.
    intuition eauto using smem_set_sound', smem_set_same_domain.
  Qed.


  Theorem split_smem_get : forall a b c p v,
    split a b c ->
      smem_get p b = Some v ->
      smem_get p a = Some v.
  Proof.
    unfold models, smem_get, mem_get, smem, split, disjoint, join, smem.
    generalize BD.all_addr. induction l; simpl in *; intros; try congruence.
    destruct (addr_dec a p); subst.
    { intuition; subst; simpl; rewrite H0; auto. }
    { intuition; subst; simpl; try rewrite H1; eauto. }
  Qed.

  Theorem split_smem_set : forall a b c p v b',
    split a b c ->
      smem_set p v b = Some b' ->
      exists a', split a' b' c /\
        smem_set p v a = Some a'.
  Proof.
    unfold models, smem_set, mem_set, smem, split, disjoint, join, smem.
    generalize BD.all_addr. induction l; simpl in *; intros; try congruence.
    destruct (addr_dec a p); subst.
    { intuition; subst; simpl in *; rewrite H1 in *; try congruence.
      destruct (hlist_hd b); try congruence; simpl in *. inversion H0; clear H0; subst; simpl in *.
      eexists. intuition eauto. }
    { revert H0; case_eq (smem_set' l p v (hlist_tl b)); intros; try congruence.
      inversion H1; clear H1; subst. simpl in *.
      intuition; subst; simpl in *; try rewrite H1 in *.
      eapply IHl in H0; eauto.
      destruct H0; intuition; subst. rewrite H2. eexists; eauto.

      eapply IHl in H0; eauto. destruct H0. intuition.
      subst. rewrite H2. eexists; intuition eauto. }
  Qed.

  Global Instance Symetric_same_domain : Symmetric same_domain.
  Proof. clear; red; firstorder. Qed.

  Global Instance Trans_same_domain : Transitive same_domain.
  Proof.
    clear.
    red. unfold same_domain. firstorder.
  Qed.
      
  (** memoryIn **)
  Section memoryIn.
    Variable m : mem.

    Fixpoint memoryIn' (ls : list addr) : smem' ls :=
      match ls with 
        | nil => Hnil
        | l :: ls => Hcons (mem_get m l) (memoryIn' ls)
      end. 

    Definition memoryIn : smem := memoryIn' BD.all_addr.
  End memoryIn.

  Theorem memoryIn_sound : forall m, 
    models (memoryIn m) m.
  Proof.
    unfold models, memoryIn. generalize BD.all_addr.
    induction l; simpl; auto.
    intuition. destruct (mem_get m a); auto.
  Qed.

  Theorem smem_set_get_eq : forall m p v' m', 
    smem_set p v' m = Some m' ->
    smem_get p m' = Some v'.
  Proof.
    unfold smem_set, smem_get, smem.
    generalize BD.all_addr. induction l; simpl in *; intros; try congruence.
    
    destruct (addr_dec a p); subst; auto. destruct (hlist_hd m); try congruence.
    inversion H; clear H; subst. auto.
    eapply IHl.
    instantiate (1 := hlist_tl m).
    destruct (smem_set' l p v' (hlist_tl m)); try congruence.
    inversion H; clear H; subst. auto.
  Qed.


  Theorem smem_set_get_neq : forall m p v' m', 
    smem_set p v' m = Some m' ->
    forall p', p <> p' ->
      smem_get p' m' = smem_get p' m.
  Proof.
    unfold smem_set, smem_get, smem.
    generalize BD.all_addr. induction l; simpl in *; intros; try congruence.
    
    destruct (addr_dec a p); subst; auto. destruct (hlist_hd m); try congruence.
    inversion H; clear H; subst. destruct (addr_dec p p'); auto; try congruence.

    revert H.
    case_eq (smem_set' l p v' (hlist_tl m)); intros; try congruence.
    inversion H1; clear H1; subst. simpl in *.
    eapply IHl in H; eauto. rewrite H. auto.
  Qed.

  Theorem smem_get_set_valid : forall m p v,
    smem_get p m <> None ->
    smem_set p v m <> None.
  Proof.
    unfold smem_get, smem_set, smem.
    generalize (BD.all_addr); induction l; simpl; intros; auto.
    destruct (addr_dec a p); subst; auto.
    destruct (hlist_hd m); congruence.
    eapply IHl with (v := v) in H.
    destruct (smem_set' l p v (hlist_tl m)); congruence.
  Qed.

End DiscreteHeap.

Export Heaps.
