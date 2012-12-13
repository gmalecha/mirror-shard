Require Import Setoid.

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

  Parameter addr_dec : forall a b : addr, {a = b} + {a <> b}.

End Memory.

Module Type SeparationMemory.
  Declare Module M : Memory.

  Parameter smem : Type.

(*
  Parameter smem_eqv : smem -> smem -> Prop.

  Parameter Reflexive_eqv : Reflexive smem_eqv.
  Parameter Symmetric_eqv : Symmetric smem_eqv.
  Parameter Transitive_eqv : Transitive smem_eqv.
*)

  Parameter models : smem -> M.mem -> Prop.

  Parameter memoryIn : M.mem -> smem.

(*
  Parameter models_respects : forall s s' m,
    smem_eqv s s' -> (models s m <-> models s' m).
*)

  Parameter smem_emp : smem.

  Parameter smem_get : M.addr -> smem -> option M.value.

(*
  Parameter smem_get_respects : forall a s s',
    smem_eqv s s' -> smem_get a s = smem_get a s'.
*)

  Parameter smem_set : M.addr -> M.value -> smem -> option smem.

(*
  Parameter smem_set_respects : forall a v s s',
    smem_eqv s s' -> smem_set a v s = smem_set a v s'.
*)

  Parameter split : smem -> smem -> smem -> Prop.

(*
  Parameter split_respects : forall s1 s1' s2 s2' s3 s3',
    smem_eqv s1 s1' -> smem_eqv s2 s2' -> smem_eqv s3 s3' ->
    (split s1 s2 s3 <-> split s1' s2' s3').
*)

  Parameter split_comm : forall a b c,
    split a b c -> split a c b.

  Parameter split_emp : forall a c,
    split a smem_emp c <-> a = c.

  Parameter split_assoc : forall a b c d e,
    split a b c -> split b d e ->
    exists f, split a d f /\ split f e c.

  Parameter memoryIn_sound : forall m,
    models (memoryIn m) m.

  Parameter smem_get_sound : forall s m,
    models s m ->
    forall a v, smem_get a s = Some v ->
                M.mem_get m a = Some v.

  Parameter smem_set_sound : forall s m,
    models s m ->
    forall a v s', smem_set a v s = Some s' ->
    exists m', M.mem_set m a v = Some m' /\ models s' m'.

End SeparationMemory.

