Require Import Heaps.
Require Import Setoid.
Require Import DepList.
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

  Definition smem' dom : Type := hlist (fun _ : addr => option value) dom.

  Fixpoint smem_emp' (ls : list addr) : smem' ls :=
    match ls with
      | nil => HNil
      | a :: b => HCons None (smem_emp' b)
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
      | nil => fun _ _ => HNil
      | a :: b => fun m1 m2 => 
        HCons 
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
            | Some _ => Some (HCons (Some v) (hlist_tl m))
          end
        else
          match smem_set' b p v (hlist_tl m) with
            | None => None
            | Some tl => Some (HCons (hlist_hd m) tl)
          end
    end.

  Fixpoint models' dom (sm : smem' dom) (m : B.mem) : Prop :=
    match sm with
      | HNil => True
      | HCons p _ a b =>
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
(*
  Definition relevant (sm : smem) := relevant' _ sm.
*)

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
    { intuition; subst; auto; rewrite hlist_nil_only with (h := c); eauto with typeclass_instances. }
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
    { intuition subst. exists HNil; intuition. }
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

  Theorem smem_get_sound : forall s m,
    models s m ->
    forall a v, smem_get a s = Some v ->
                M.mem_get m a = Some v.
  Proof.
  Admitted.

  Theorem smem_set_sound : forall s m,
    models s m ->
    forall a v s', smem_set a v s = Some s' ->
    exists m', M.mem_set m a v = Some m' /\ models s' m'. 
  Proof.
  Admitted.

  (** memoryIn **)
  Section memoryIn.
    Variable m : mem.

    Fixpoint memoryIn' (ls : list addr) : smem' ls :=
      match ls with 
        | nil => HNil
        | l :: ls => HCons (mem_get m l) (memoryIn' ls)
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

End DiscreteHeap.

Export Heaps.

(*
  Local Hint Resolve mem_get_set_eq mem_get_set_neq : memory.

  Lemma smem_set_not_in : forall l m p v,
    ~In p l -> smem_set' l p v m = None.
  Proof.
    induction l; simpl; auto.
      intros.
      destruct (addr_dec a p); subst; intuition.
      rewrite IHl; auto.
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
            | HCons _ _ => fail 1
            | _ => rewrite (hlist_eta _ M) in H
          end
        | [ |- models' (_ :: _) ?M _ ] =>
          match M with
            | HCons _ _ => fail 1
            | _ => rewrite (hlist_eta _ M)
          end
        | [ H : smem' nil |- _ ] => 
          rewrite (hlist_nil_only _ H) in *
        | [ H : exists x, _ |- _ ] => destruct H
        | [ H : _ /\ _ |- _ ] => destruct H
        | [ |- _ ] => congruence
        | [ |- _ ] => ext
      end; simpl in * ); eauto 10 with memory.

  Theorem satisfies_get : forall m m',
    models m m' ->
    forall p v, 
      smem_get p m = Some v ->
      mem_get m' p = Some v.
  Proof.
    unfold models, smem_get, smem.
    induction BD.all_addr; simp intuition. 
  Qed.

  Lemma models_set_not_in : forall l m sm p v,
    models' l sm m ->
    ~In p l ->
    forall m', mem_set m p v = Some m' ->
    models' l sm m'.
  Proof.
    induction l; try solve [ simp intuition ].
      simp auto.
      destruct (addr_dec a p); destruct (in_dec addr_dec p l); subst; try solve [ intuition ].

      split; eauto. rewrite <- H3. eapply B.mem_get_set_neq; eauto.
  Qed.

  Local Hint Resolve models_set_not_in : memory.

  Theorem models_set : forall sm m,
    models sm m ->
    forall p v sm',
      smem_set p v sm = Some sm' ->
      exists m',
      mem_set m p v = Some m' /\ models sm' m'.
  Proof.
    unfold models, smem_set, smem_get, smem.
    generalize BD.NoDup_all_addr.
    induction BD.all_addr; simp auto.
    { 


      destruct (proj1 (mem_set_acc _ _) H2 v). rewrite H3. eexists; split; eauto.        
      erewrite mem_get_set_eq; eauto with memory.

      Focus.
      eapply IHl in H1; eauto.
      destruct H1; eexists; intuition; eauto with memory.
      erewrite mem_get_set_neq; eauto.

      Focus.
      eapply IHl in H1; eauto. destruct H1; eexists; intuition eauto.
  Qed.

  Lemma smem_set_get_neq : forall p m m' a b,
    smem_set a b m = Some m' ->
    a <> p ->
    smem_get p m' = smem_get p m.
  Proof.
    unfold smem, smem_get, smem_set.
    induction BD.all_addr; simp intuition.
  Qed.

  Lemma smem_set_get_eq : forall m m' a b,
    smem_set a b m = Some m' ->
    smem_get a m' = Some b.
  Proof.
    unfold smem, smem_get, smem_set.
    induction BD.all_addr; simp intuition.
  Qed.

  Lemma split_smem_get : forall a b c p v,
    split a b c ->
      (smem_get p b = Some v \/ smem_get p c = Some v) ->
      smem_get p a = Some v.
  Proof.
    unfold smem, split, disjoint, join, smem_get, smem.
    induction BD.all_addr; simp intuition.
  Qed.

  Lemma smem_set_get_valid : forall m p v v',
    smem_get p m = Some v' ->
    smem_set p v m <> None.
  Proof.
    unfold smem_get, smem_set, smem.
    induction BD.all_addr; simp intuition.
  Qed.

  Lemma split_set : forall a b,
    disjoint a b ->
    forall p v a',
    smem_set p v a = Some a' ->
      disjoint a' b /\ 
      smem_set p v (join a b) = Some (join a' b).
  Proof.
    unfold smem, disjoint, join, smem_set, smem.
    induction BD.all_addr; simpl; intros; try congruence.
      destruct (addr_dec a p); subst.
      destruct H. destruct H; rewrite H in *; try congruence.
        destruct (hlist_hd a0); try congruence.
        inversion H0; auto.

      generalize dependent H0.
      case_eq (smem_set' l p v (hlist_tl a0)); intros; try congruence.
        inversion H1; clear H1; subst.
        eapply IHl in H0. 2: destruct H; eauto.
        simp intuition.
  Qed.


  Ltac unfold_all :=
    unfold smem, split, join, disjoint, smem_emp, semp; 
    unfold smem, split, join, disjoint, smem_emp, semp.
  Ltac break :=
    simpl; intros; try reflexivity;
      repeat (simpl in *; match goal with
                            | [ H : HCons _ _ = HCons _ _ |- _ ] =>
                              inversion H; clear H
                            | [ H : _ /\ _ |- _ ] => destruct H
                            | [ H : @existT _ _ _ _ = @existT _ _ _ _ |- _ ] => 
                              eapply (@Eqdep_dec.inj_pair2_eq_dec _ (list_eq_dec B.addr_dec)) in H
                            | [ H : @existT _ _ _ _ = @existT _ _ _ _ |- _ ] => 
                              eapply (@Eqdep_dec.inj_pair2_eq_dec _ B.addr_dec) in H
                            | [ H : _ = _ |- _ ] => rewrite H in *
                          end).
  
  Lemma disjoint_join : forall a b, disjoint a b -> join a b = join b a.
  Proof.
    unfold_all; induction a; break; f_equal; intuition; subst.
      destruct (hlist_hd b0); reflexivity.
      rewrite H1. destruct b; reflexivity.
  Qed.
    
  Lemma disjoint_comm : forall ml mr, disjoint ml mr -> disjoint mr ml.
  Proof.
    unfold_all; induction ml; break; intuition.
  Qed.

  Hint Resolve disjoint_join disjoint_comm : disjoint.

  Lemma split_assoc' : forall b a c d e, split a b c -> split c d e ->
    split a (join d b) e.
  Proof.
    unfold_all; induction b; break; eauto.
    edestruct IHb. split; try eassumption. reflexivity. split; try eassumption.
    reflexivity.
    intuition; break; auto. destruct (hlist_hd d); auto.
    destruct (hlist_hd d); try congruence.
  Qed.

  Lemma split_comm : forall m ml mr, split m ml mr -> split m mr ml.
  Proof.
    unfold_all. induction ml; break; eauto. edestruct IHml.
    split; try eassumption. reflexivity. 
    intuition; subst. rewrite H3. destruct (hlist_hd mr); auto.
    rewrite H4. rewrite H3. destruct b; auto.
  Qed.

  Lemma disjoint_split_join : forall a b, disjoint a b -> split (join a b) a b.
  Proof.
    unfold split, disjoint; intros; intuition.
  Qed.

  Lemma split_split_disjoint : forall b a c d e,
    split a b c -> split b d e -> disjoint c d.
  Proof.
    unfold_all. induction b; break. subst. split.
    intuition; destruct (hlist_hd c); eauto. destruct (hlist_hd d); auto.
    eapply IHb. split; auto. split; auto. auto.
  Qed.

  Lemma hlist_destruct : forall T (F : T -> Type) a b (m : hlist F (a :: b)),
    exists A, exists B, m = HCons A B.
  Proof.
    intros.
    refine (match m as m in hlist _ ls return
              match ls as ls return hlist _ ls -> Type with
                | nil => fun _ => unit
                | a :: b => fun m => exists A : F a, exists B : hlist F b, m = HCons A B
              end m
              with
              | HNil => tt
              | HCons _ _ _ _ => _
            end).
    do 2 eexists; reflexivity.
  Qed.
  Lemma hlist_nil : forall T (F : T -> Type) (m : hlist F nil), m = HNil.
  Proof.
    intros. 
    refine (match m as m in hlist _ ls return
              match ls as ls return hlist _ ls -> Type with
                | nil => fun m => m = HNil
                | _ :: _ => fun _ => unit
              end m
              with
              | HNil => _ 
              | _ => tt
            end). reflexivity.
  Qed.

  Lemma split_semp : forall b a c, 
    split a b c -> semp b -> a = c.
  Proof.
    unfold_all. unfold semp, smem_emp. unfold_all.
    induction b; simpl; intros; subst; auto.
    rewrite hlist_nil. rewrite (hlist_nil _ _ a). reflexivity.
    destruct (hlist_destruct _ _ _ _ a).
    destruct (hlist_destruct _ _ _ _ c).
    destruct H1. destruct H2. subst. specialize (IHb x2 x3).
    rewrite IHb; break; intuition; auto.
  Qed.

  Lemma semp_smem_emp : semp smem_emp.
  Proof.
    unfold semp, smem_emp; auto.
  Qed.

  Lemma split_a_semp_a : forall a, 
    split a smem_emp a.
  Proof.
    unfold_all. induction a; simpl; intuition. rewrite <- H0. reflexivity.
  Qed.
     
  Lemma cons_not_in : forall T (a : T) b ls,
    a :: b = ls ->
    ~ In a ls ->
    forall P, P.
  Proof.
    intros; subst. exfalso; eapply H0. firstorder.
  Qed.
  
  Lemma relevant_in : forall a l b,
    In a (relevant' l b) ->
    In a l.
  Proof.
    induction l; auto; intros.
      rewrite (hlist_eta _ b) in H. simpl in H.
      destruct (hlist_hd b). destruct H. subst. firstorder.
      simpl in *. right. eapply IHl; eauto.
      right. eapply IHl; eauto.
  Qed.

  Lemma relevant_not_in : forall a l b,
    ~In a l ->
    ~In a (relevant' l b).
  Proof.
    intros. intro. eapply H. eapply relevant_in; eauto.
  Qed.

  Lemma relevant_eq : forall a b c,
    relevant a = relevant b ->
    models a c ->
    models b c ->
    a = b.
  Proof.
    unfold relevant, models, smem. generalize BD.NoDup_all_addr.
    induction BD.all_addr; simpl; intros.
      rewrite (hlist_nil_only _ a). rewrite (hlist_nil_only _ b); auto.

      rewrite (hlist_eta _ a0) in *. rewrite (hlist_eta _ a0) in H1.
      rewrite (hlist_eta _ b) in *. rewrite (hlist_eta _ b) in H2.
      simpl in *.
      destruct (hlist_hd a0); destruct (hlist_hd b); intuition.
        rewrite H2 in H3. inversion H3; subst. inversion H0;  f_equal. eapply IHl; eauto.
          inversion H; auto.

        eapply cons_not_in. eassumption.
        eapply relevant_not_in. inversion H; auto.

        eapply cons_not_in. symmetry. eassumption.
        eapply relevant_not_in. inversion H; auto.
        
        f_equal; eauto. inversion H. eapply IHl; eauto.
  Qed.

  (** memoryIn **)
  Section memoryIn.
    Variable m : mem.

    Fixpoint memoryIn' (ls : list addr) : smem' ls :=
      match ls with 
        | nil => HNil
        | l :: ls => HCons (mem_get m l) (memoryIn' ls)
      end. 

    Definition memoryIn : smem := memoryIn' BD.all_addr.
  End memoryIn.

  Theorem smem_set_relevant : forall p v sm sm',
    smem_set p v sm = Some sm' ->
    relevant sm = relevant sm'.
  Proof.
    unfold relevant, smem_set.
    induction BD.all_addr; simpl; intros; auto.
      destruct (addr_dec a p); subst; auto.
      destruct (hlist_hd sm); try congruence.
      inversion H; clear H; subst. simpl. reflexivity.

      revert H. case_eq (smem_set' l p v (hlist_tl sm)); intros; try congruence.
      inversion H0; clear H0; subst; simpl in *.
      destruct (hlist_hd sm); eauto. f_equal; eauto.
  Qed.


  Theorem models_memoryIn : forall m, 
    models (memoryIn m) m.
  Proof.
    unfold models, memoryIn. generalize BD.all_addr.
    induction l; simpl; auto.
    intuition. destruct (mem_acc_dec m a).
    generalize (proj1 (mem_get_acc _ _) H). intro. destruct H0. rewrite H0. auto.
    case_eq (mem_get m a); intuition; auto.
    eapply mem_get_acc. eauto.
  Qed.

  



(*
  Theorem smem_set_word_relevant : forall ex p v sm sm',
    smem_set_word ex p v sm = Some sm' ->
    relevant sm = relevant sm'.
  Proof.
    unfold smem_set_word; intros.
    destruct (footprint_w p) as [ [ [ ? ? ] ? ] ? ].
    destruct (ex v) as [ [ [ ? ? ] ? ] ? ].
    repeat match goal with
             | [ H : match ?X with 
                       | Some _ => _
                       | None => _ 
                     end = Some _ |- _ ] => revert H; case_eq X; intros; try congruence
             | [ H : smem_set _ _ _ = Some _ |- _ ] => 
               eapply smem_set_relevant in H
           end.
    congruence.
  Qed.
*)


(*
  Definition smem_get_word (implode : B * B * B * B -> W) (p : addr) (m : smem)
    : option W :=
    let '(a,b,c,d) := footprint_w p in
    match smem_get a m , smem_get b m , smem_get c m , smem_get d m with
      | Some a , Some b , Some c , Some d =>
        Some (implode (a,b,c,d))
      | _ , _ , _ , _ => None
    end.

  Definition smem_set_word (explode : W -> B * B * B * B) (p : addr) (v : W)
    (m : smem) : option smem :=
    let '(a,b,c,d) := footprint_w p in
    let '(av,bv,cv,dv) := explode v in
    match smem_set d dv m with
      | None => None 
      | Some m => match smem_set c cv m with
                    | None => None
                    | Some m => match smem_set b bv m with
                                  | None => None
                                  | Some m => smem_set a av m
                                end
                  end
    end.
*)

(*
  Lemma split_set_word : forall a b,
    disjoint a b ->
    forall i p v a',
    smem_set_word i p v a = Some a' ->
      disjoint a' b /\ 
      smem_set_word i p v (join a b) = Some (join a' b).
  Proof.
    unfold smem_set_word.
    intros. destruct (i v); simp fail. 
    repeat match goal with
      | [ H : smem_set _ _ _ = Some _ |- _ ] =>
        eapply split_set in H; [ rewrite (proj2 H) | eauto ]
    end; tauto.
  Qed.
*)


(*
  Lemma smem_set_get_word_eq : forall i e m m' a b,
    (forall x, i (e x) = x) ->
    smem_set_word e a b m = Some m' ->
    smem_get_word i a m' = Some b.
  Proof.
    unfold smem_get_word, smem_set_word; intros.
    generalize (footprint_disjoint a).
    generalize dependent H0. case_eq (e b). simp intuition.
    specialize (H2 _ _ _ _ (refl_equal _)). simp intuition.
    repeat ((erewrite smem_set_get_eq; [ | repeat rewrite smem_set_get_neq by auto; eassumption ])
      || (erewrite smem_set_get_neq by eauto)). simp intuition.
  Qed.
*)

(*
  Lemma split_smem_get_word : forall i a b c p v,
    split a b c ->
      (smem_get_word i p b = Some v \/ smem_get_word i p c = Some v) ->
      smem_get_word i p a = Some v.
  Proof.
    unfold smem_get_word. simp intuition;
    repeat (erewrite split_smem_get by eauto); auto.
  Qed.

  Theorem models_set_word : forall sm m,
    models sm m ->
    forall e p v sm',
      smem_set_word e p v sm = Some sm' ->
      exists m',
           mem_set_word addr mem footprint_w mem_set e p v m = Some m' 
        /\ models sm' m'.
  Proof.
    unfold smem_set_word, mem_set_word, smem_get_word; intros.
    simp intuition. destruct (e v); simp intuition.
    repeat match goal with
             | [ H : models _ _ |- _ ] => 
               eapply models_set in H; eauto; destruct H as [ ? [ ? ? ] ]
             | [ H : _ = _ |- _ ] => rewrite H
           end.
    exists x2. intuition eauto.
  Qed.
*)

(*
  Lemma smem_set_get_valid_word : forall i e m p v v',
    smem_get_word i p m = Some v' ->
    smem_set_word e p v m <> None.
  Proof.
    unfold smem_get_word, smem_set_word.
    intros. generalize (footprint_disjoint p).
    intros; destruct (e v); simp intuition;
    specialize (H0 _ _ _ _ (refl_equal _)); simp intuition;
    (eapply smem_set_get_valid; [ | eauto ];
      repeat (erewrite smem_set_get_neq; [ | solve [ eauto ] | solve [ eauto ] ]); eauto).
  Qed.
*)

(*
  Theorem models_get_word : forall i m m',
    models m m' ->
    forall p v, 
      smem_get_word i p m = Some v ->
      mem_get_word addr mem footprint_w mem_get i p m' = Some v.
  Proof.
    unfold mem_get_word, smem_get_word; simp intuition.
    repeat erewrite models_get by eauto. auto.
  Qed.
*)
*)
