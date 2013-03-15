Require Import RelationClasses.
Require Import SepTheory.
Require Import Heaps.

Set Implicit Arguments.
Set Strict Implicit.

Module Type SepModels (M : SeparationMemory) (ST : SepTheory).
  Parameter aux : Type.

  Parameter models : ST.hprop -> aux -> M.smem -> Prop.

  Parameter models_pure : forall P a m,
    models (ST.inj P) a m ->
    P /\ models ST.emp a m.

  Parameter models_star : forall P Q a m,
    models (ST.star P Q) a m ->
    exists m1 m2, M.split m m1 m2 /\
        models P a m1 /\ models Q a m2.

  Parameter models_ex : forall T (P : T -> ST.hprop) a m,
    models (ST.ex P) a m ->
    exists x : T, models (P x) a m.

End SepModels.

Module Type Foo (M : Memory) (SM : SeparationMemory with Module M := M).

  Parameter models : SM.smem -> M.mem -> Prop.

  Parameter memoryIn : M.mem -> SM.smem.

  Parameter memoryIn_sound : forall m,
    models (memoryIn m) m.

  Parameter smem_get_sound : forall a v m sm,
    models sm m ->
    SM.smem_get a sm = Some v ->
    M.mem_get m a = Some v.
  
  