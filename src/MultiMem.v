Require Import List.
Require Import Heaps.

Set Implicit Arguments.
Set Strict Implicit.

Section parametric.
  Variable T : Type.

  Fixpoint vector (n : nat) : Type :=
    match n with
      | 0 => unit
      | S n => prod T (vector n)
    end.

  Fixpoint to_list (n : nat) : vector n -> list T :=
    match n as n return vector n -> list T with
      | 0 => fun _ => nil
      | S n => fun x => fst x :: to_list _ (snd x)
    end.

  Definition NoDup_v (n : nat) (v : vector n) : Prop :=
    NoDup (to_list _ v).

  Definition disjoint_v (n n' : nat) (v : vector n) (v' : vector n') : Prop :=
    forall x, In x (to_list _ v) -> ~In x (to_list _ v').

End parametric.

Section multi_mem.
  Variable T : Type.
  Variables mem addr val : Type.

  Section read.
    Variable read : addr -> mem -> option val.
    Variable m : mem.
  
    Fixpoint multi_read_addrs (n : nat) : vector addr n -> (vector val n -> T) -> option T :=
      match n as n return vector addr n -> (vector val n -> T) -> option T with
        | 0 => fun _ k => Some (k tt)
        | S n => fun a k =>
          match read (fst a) m with
            | None => None
            | Some v => multi_read_addrs n (snd a) (fun vs => k (v,vs))
          end
      end.
  End read.
  
  Section write.
    Variable write : addr -> val -> mem -> option mem.

    Fixpoint multi_write_addrs (n : nat) : vector addr n -> vector val n -> mem -> option mem :=
      match n as n return vector addr n -> vector val n -> mem -> option mem with
        | 0 => fun _ _ m => Some m
        | S n => fun a v m =>
          match write (fst a) (fst v) m with
            | None => None
            | Some m => multi_write_addrs n (snd a) (snd v) m
          end
      end.
  End write.

  Variable N : nat.
  Variable footprint : addr -> vector addr N.
  Variable implode : vector val N -> T.
  Variable explode : T -> vector val N.

  Definition multi_read (read : addr -> mem -> option val) (a : addr) (m : mem) : option T :=
    multi_read_addrs read m N (footprint a) implode.

  Definition multi_write (write : addr -> val -> mem -> option mem) (a : addr) (v : T) : mem -> option mem :=
    multi_write_addrs write N (footprint a) (explode v).
  
End multi_mem.

Module MultiSepMemFacts (SM : SeparationMemory).
  
  Require Import Reflection.

  Lemma smem_multi_write_footprint : forall (N : nat) b b' addrs vals,
    @multi_write_addrs SM.smem SM.M.addr SM.M.value SM.smem_set N addrs vals b = Some b' ->
    (forall a, ~In a (to_list _ _ addrs) -> SM.smem_get a b = SM.smem_get a b').
  Proof.
    induction N; simpl; intros.
    { inversion H; auto. }
    { match goal with
      | [ H : match ?X with _ => _ end = Some _ |- _ ] =>
        consider X; intros; try congruence
      end.
      eapply IHN in H1; eauto.
      rewrite <- H1.
      symmetry. eapply SM.smem_set_get_neq; eauto. }
  Qed.

  Lemma smem_multi_read_footprint : forall T (N : nat) b b' addrs k,
    (forall a, In a (to_list _ _ addrs) -> SM.smem_get a b = SM.smem_get a b') ->
    @multi_read_addrs T SM.smem SM.M.addr SM.M.value SM.smem_get b N addrs k = 
    @multi_read_addrs T SM.smem SM.M.addr SM.M.value SM.smem_get b' N addrs k.
  Proof.
    induction N; simpl; intros; auto.
    { rewrite H; eauto.
      match goal with
      | [ |- match ?X with _ => _ end = _ ] =>
        consider X; intros; try congruence
      end. eauto. }
  Qed.

  Lemma smem_read_write_eq_multi' : forall T (N : nat) k b b' addrs vals,
    NoDup_v _ _ addrs ->
    @multi_write_addrs SM.smem SM.M.addr SM.M.value SM.smem_set N addrs vals b = Some b' ->
    @multi_read_addrs T SM.smem SM.M.addr SM.M.value SM.smem_get b' N addrs k = Some (k vals).
  Proof.
    induction N; simpl; intros.
    { inversion H0; destruct vals; intuition auto. }
    { match goal with
      | [ H : match ?X with _ => _ end = Some _ |- _ ] =>
        consider X; intros; try congruence
      end.
      inversion H; clear H; subst.
      match goal with
        | [ |- match ?X with _ => _ end = Some _ ] =>
        consider X; intros; try congruence
      end.
      { generalize (smem_multi_write_footprint _ _ _ _ H1 (fst addrs) H4). 
        eapply IHN with (k := fun vs => k (v, vs)) in H1; eauto.
        generalize (SM.smem_set_get_eq _ _ _ _ H0).
        intros. rewrite H1. f_equal. f_equal. destruct vals; simpl; f_equal.
        simpl in *.
        clear - H H2 H3. unfold vector in *.
        rewrite H in H3. rewrite H2 in H3. inversion H3; auto. }
      { exfalso.
        generalize (smem_multi_write_footprint _ _ _ _ H1 (fst addrs) H4). 
        eapply IHN with (k := fun vs => k (fst vals,vs)) in H1; eauto.
        intuition.        
        generalize (SM.smem_set_get_eq _ _ _ _ H0). unfold vector in *.
        rewrite H2. rewrite H. congruence. } }
  Qed.

  Lemma smem_read_write_neq_multi' : forall T (N : nat) k b b' addrs addrs' vals,
    disjoint_v _ _ _ addrs addrs' ->    
    @multi_write_addrs SM.smem SM.M.addr SM.M.value SM.smem_set N addrs vals b = Some b' ->
    @multi_read_addrs T SM.smem SM.M.addr SM.M.value SM.smem_get b' N addrs' k = 
      @multi_read_addrs T SM.smem SM.M.addr SM.M.value SM.smem_get b N addrs' k.
  Proof.
    induction N; simpl; intros.
    { inversion H0; destruct vals; intuition auto. }
    { match goal with
      | [ H : match ?X with _ => _ end = Some _ |- _ ] =>
        consider X; intros; try congruence
      end.
      match goal with
        | [ |- match ?X with _ => _ end = _ ] =>
        consider X; intros; try congruence
      end.
      { generalize (smem_multi_write_footprint _ _ _ _ H1); intro.
        eapply IHN with (addrs' := snd addrs') (k := fun vs => k (v, vs)) in H1; eauto.
        { match goal with
          | [ |- _ = match ?X with _ => _ end ] =>
            replace X with (Some v)
          end.
          etransitivity. eapply H1.
          eapply smem_multi_read_footprint.
          { intros.
            eapply (SM.smem_set_get_neq _ _ _ _ H0 a).
            red in H. simpl in H. intro.
            eapply H; eauto. }
          { rewrite <- H3 in H2.
            generalize (SM.smem_set_get_neq _ _ _ _ H0 (fst addrs')).
            rewrite <- H2. intro. apply H4. 
            intro. eapply H. left. reflexivity.
            exfalso. eapply H. left. reflexivity. left; auto.
            intro. eapply H. right. eapply H4. left. auto. } }
        { red; intros. intro. eapply H.
          right; eassumption. right; eassumption. } }
      { generalize (smem_multi_write_footprint _ _ _ _ H1).
        eapply SM.smem_set_get_neq in H0. rewrite <- H0.
        intro. rewrite H3. rewrite H2; auto.
        { intro. eapply H. right; eapply H4. left; reflexivity. }
        { intro. eapply H. left; reflexivity. left. auto. } } }
  Qed.

  Lemma split_smem_read_multi' : forall T (N : nat) k a b c addrs v,
    SM.split a b c ->
      @multi_read_addrs T SM.smem SM.M.addr SM.M.value SM.smem_get b N addrs k = Some v ->
      @multi_read_addrs T SM.smem SM.M.addr SM.M.value SM.smem_get a N addrs k = Some v.
  Proof.
    induction N; simpl; intros; auto.
    revert H0.
    match goal with
      | [ |- match ?X with _ => _ end = _ -> _ ] =>
        case_eq X; intros; try congruence
    end.
    eapply SM.split_smem_get in H0; eauto.
    rewrite H0. eauto.
  Qed.

  Lemma split_smem_write_multi' : forall (N : nat) addrs vals a b c b',
    SM.split a b c ->
      @multi_write_addrs SM.smem SM.M.addr SM.M.value SM.smem_set N addrs vals b = Some b' ->
      exists a', SM.split a' b' c /\
        @multi_write_addrs SM.smem SM.M.addr SM.M.value SM.smem_set N addrs vals a = Some a'.
  Proof.
    induction N; simpl; intros; auto.
    { inversion H0; subst; eauto. }
    { revert H0.
      match goal with
        | [ |- match ?X with _ => _ end = _ -> _ ] =>
          case_eq X; intros; try congruence
      end.
      eapply SM.split_smem_set in H0; eauto.
      destruct H0. intuition. rewrite H3.
      eauto. }
  Qed.

  Section exposed.
    Variable T : Type.
    Variable N : nat.
    Variable footprint : SM.M.addr -> vector SM.M.addr N.
    Variable implode : vector SM.M.value N -> T.
    Variable explode : T -> vector SM.M.value N.

    Theorem split_multi_read_write_eq : forall b b' p v,
      implode (explode v) = v ->
      NoDup_v _ _ (footprint p) ->
      @multi_write T SM.smem SM.M.addr SM.M.value N footprint explode SM.smem_set p v b = Some b' ->
      @multi_read T SM.smem SM.M.addr SM.M.value N footprint implode SM.smem_get p b' = Some v.
    Proof.
      unfold multi_read, multi_write; intros.
      eapply smem_read_write_eq_multi' with (k := implode) in H1; eauto. intuition.
      rewrite H1. rewrite H; auto.
    Qed.

    Theorem split_multi_read_write_neq : forall b b' p p' v,
      implode (explode v) = v ->
      disjoint_v _ _ _ (footprint p) (footprint p') ->
      @multi_write T SM.smem SM.M.addr SM.M.value N footprint explode SM.smem_set p v b = Some b' ->
      @multi_read T SM.smem SM.M.addr SM.M.value N footprint implode SM.smem_get p' b' = 
      @multi_read T SM.smem SM.M.addr SM.M.value N footprint implode SM.smem_get p' b. 
    Proof.
      unfold multi_read, multi_write; intros.
      eapply smem_read_write_neq_multi' with (k := implode) in H1; eauto. 
    Qed.

    Theorem split_multi_read : forall a b c p v,
      SM.split a b c ->
        @multi_read T SM.smem SM.M.addr SM.M.value N footprint implode SM.smem_get p b = Some v ->
        @multi_read T SM.smem SM.M.addr SM.M.value N footprint implode SM.smem_get p a = Some v.
    Proof.
      intros. eapply split_smem_read_multi'; eauto.
    Qed.

    Theorem split_multi_write : forall p v a b c b',
    SM.split a b c ->
      @multi_write T SM.smem SM.M.addr SM.M.value N footprint explode SM.smem_set p v b = Some b' ->
      exists a', SM.split a' b' c /\
        @multi_write T SM.smem SM.M.addr SM.M.value N footprint explode SM.smem_set p v a = Some a'.
    Proof.
      intros. eapply split_smem_write_multi'; eauto.
    Qed.
  End exposed.

End MultiSepMemFacts.