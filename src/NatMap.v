Require Import Coq.Structures.OrderedType.
Require Import Coq.FSets.FMapAVL.

Module Ordered_nat <: OrderedType with Definition t := nat.
  Definition t := nat.
  Definition eq := @eq nat.
  Definition lt := @lt.

  Theorem eq_refl : forall x, eq x x.
    reflexivity.
  Qed.

  Theorem eq_sym : forall a b, eq a b -> eq b a.
    intros; symmetry; auto.
  Qed.

  Theorem eq_trans : forall a b c, eq a b -> eq b c -> eq a c.
    intros; etransitivity; eauto.
  Qed.

  Require Import Omega.
  Theorem lt_trans : forall a b c, lt a b -> lt b c -> lt a c.
    intros. unfold lt in *. omega.
  Qed.

  Theorem lt_not_eq : forall a b, lt a b -> ~(eq a b).
    unfold eq, lt. intros; omega.
  Qed.

  Definition compare (x y : t) : OrderedType.Compare lt eq x y :=
    match Compare_dec.nat_compare x y as r return
      Compare_dec.nat_compare x y = r -> OrderedType.Compare lt eq x y
      with
      | Lt => fun pf => OrderedType.LT (lt:=lt) (nat_compare_Lt_lt _ _ pf)
      | Eq => fun pf => OrderedType.EQ (lt:=lt) (Compare_dec.nat_compare_eq _ _ pf)
      | Gt => fun pf => OrderedType.GT (lt:=lt) (nat_compare_Gt_gt _ _ pf)
    end (refl_equal _).

  Definition eq_dec (x y : nat) : {x = y} + {x <> y} :=
    match beq_nat x y as r return
      beq_nat x y = r -> {x = y} + {x <> y} with
      | true => fun pf => left (beq_nat_true _ _ pf)
      | false => fun pf => right (beq_nat_false _ _ pf)
    end (refl_equal _).

End Ordered_nat.

Module IntMap := FMapAVL.Make Ordered_nat.