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