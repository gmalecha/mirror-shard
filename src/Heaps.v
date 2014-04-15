Require Import Coq.Setoids.Setoid.

(** Separation Heaps **)
Module Type Memory.

  Parameters addr value : Type.

  Parameter mem : Type.

  Parameter mem_get : mem -> addr -> option value.
  Parameter mem_set : mem -> addr -> value -> option mem.

  (** mem writes persist **)
  Parameter mem_get_set_eq : forall m p v' m',
    mem_set m p v' = Some m' ->
    mem_get m' p = Some v'.

  (** mem_set only modifies p **)
  Parameter mem_get_set_neq : forall m p v m',
    mem_set m p v = Some m' ->
    forall p', p <> p' ->
      mem_get m' p' = mem_get m p'.

  Parameter mem_get_mem_set : forall m p,
    mem_get m p <> None -> forall v, mem_set m p v <> None.

  Parameter addr_dec : forall a b : addr, {a = b} + {a <> b}.

End Memory.

Module Type SeparationMemory.
  Declare Module M : Memory.

  Parameter smem : Type.

  Parameter models : smem -> M.mem -> Prop.

  Parameter memoryIn : M.mem -> smem.

  Parameter smem_emp : smem.

  Parameter smem_get : M.addr -> smem -> option M.value.

  Parameter smem_set : M.addr -> M.value -> smem -> option smem.

  Parameter in_domain : M.addr -> smem -> Prop.

  Definition same_domain (l r : smem) : Prop :=
    forall p, in_domain p l <-> in_domain p r.

  Parameter split : smem -> smem -> smem -> Prop.

  Parameter split_comm : forall a b c,
    split a b c -> split a c b.

  Parameter split_emp : forall a c,
    split a smem_emp c <-> a = c.

  Parameter split_assoc : forall a b c d e,
    split a b c -> split b d e ->
    exists f, split a d f /\ split f e c.

  Parameter split_in_domain : forall a b c,
    split a b c ->
    forall p, in_domain p a <-> (in_domain p b \/ in_domain p c).

  Parameter split_disjoint : forall a b c,
    split a b c ->
      (forall p, in_domain p b -> ~in_domain p c).

  Parameter memoryIn_sound : forall m,
    models (memoryIn m) m.

  Parameter smem_get_sound : forall s m,
    models s m ->
    forall a v, smem_get a s = Some v ->
                M.mem_get m a = Some v.

  Parameter smem_set_sound : forall s m,
    models s m ->
    forall a v s', smem_set a v s = Some s' ->
    same_domain s s' /\
    exists m', M.mem_set m a v = Some m' /\ models s' m'.

  Parameter smem_set_get_eq : forall m p v' m',
    smem_set p v' m = Some m' ->
    smem_get p m' = Some v'.

  Parameter smem_get_set_valid : forall m p v,
    smem_get p m <> None ->
    smem_set p v m <> None.

  Parameter smem_set_get_neq : forall m p v' m',
    smem_set p v' m = Some m' ->
    forall p', p <> p' ->
      smem_get p' m' = smem_get p' m.

  Parameter split_smem_get : forall a b c p v,
    split a b c ->
      smem_get p b = Some v ->
      smem_get p a = Some v.

  Parameter split_smem_set : forall a b c p v b',
    split a b c ->
      smem_set p v b = Some b' ->
      exists a', split a' b' c /\
        smem_set p v a = Some a'.

End SeparationMemory.
