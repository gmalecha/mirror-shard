Require Import List.
Require Import Omega.
Require Compare_dec.

Set Implicit Arguments.
Set Strict Implicit.

(* Some tactics for automation of later proofs *)
Ltac caseDestruct t := destruct t; try solve [ simpl in *; discriminate ].

Ltac dintuition := repeat (intuition;
  match goal with
    | [ H : exists _, _ |- _ ] => destruct H
  end).

Ltac unlet := repeat match goal with
                       | [ x := ?y |- _ ] => subst x
                     end.

Ltac hypRewriter := repeat match goal with
                              | [ H : ?x = _ |- context [ ?x ] ] => rewrite H
                              | [ H1 : ?x = _, H2 : context [ ?x ] |- _ ] => rewrite H1 in H2
                            end.

Ltac loop := repeat (repeat (hypRewriter; autorewrite with provers in *); simpl in *; subst; dintuition).

Ltac provers := intuition; loop; unlet; loop; try congruence; firstorder.

(** This is representation 
 ** 1) avoids nats (including comparison)
 ** 2) is canonical
 ** 3) optimizes the common case of prefixes
 **)
Section Repr2.
  Section parametric.
    Variable T : Type.
    Record Repr : Type :=
    { footprint : list (option T)
    ; default : T 
    }.

    Definition nil_Repr (d : T) : Repr :=
      {| footprint := nil
       ; default := d
      |}.

    Definition listToRepr (ls : list T) (d : T) : Repr :=
      {| footprint := map (@Some _) ls
       ; default := d
      |}.

    Definition listOptToRepr (ls : list (option T)) (d : T) : Repr :=
      {| footprint := ls
       ; default := d
      |}.

    Fixpoint repr' (d : T) (ls : list (option T)) : list T -> list T :=
      match ls with 
        | nil => fun x => x
        | None :: ls => fun x =>
          match x with
            | nil => d
            | a :: _ => a
          end :: repr' d ls (tl x)
        | Some v :: ls => fun x =>
          v :: repr' d ls (tl x)
      end.

    Definition repr (l : Repr) : list T -> list T :=
      Eval cbv delta [ repr' ] in 
        match l with 
          | {| footprint := f ; default := d |} =>
            repr' d f
        end.

    Fixpoint join (ls rs : list (option T)) : list (option T) :=
      match ls , rs with
        | nil , rs => rs
        | ls , nil => ls
        | l :: ls , r :: rs =>
          match l with
            | Some _ => l
            | None => r
          end :: join ls rs
      end.       

    Definition repr_combine (l r : Repr) : Repr :=
      Eval cbv delta [ join ] in 
        match l , r with
          | {| footprint := lf ; default := ld |} ,
            {| footprint := rf ; default := rd |} =>
            {| footprint := join lf rf ; default := ld |}
        end.

    Lemma repr_idempotent : forall a b,
      repr a (repr a b) = repr a b.
    Proof.
      clear. destruct a.
      simpl. induction footprint0; simpl; intros; auto.
      destruct a; simpl; auto. f_equal. rewrite IHfootprint0. auto.
      destruct b; auto. rewrite IHfootprint0; auto. simpl.
      rewrite IHfootprint0. auto.
    Qed.

    Section updateAt.
      Variable new : T.

      Fixpoint updateAt (ls : list (option T)) (n : nat) : list (option T) :=
        match n with
          | 0 => Some new :: tail ls
          | S n => match head ls with
                     | None => None
                     | Some v => v 
                   end :: updateAt (tail ls) n
        end.
    End updateAt.

    Fixpoint assocToList (ls : list (nat * T)) (acc : list (option T)) {struct ls} : list (option T) :=
      match ls with
        | nil => acc
        | (n,v) :: ls => assocToList ls (updateAt v acc n)
      end.

    Definition assocToRepr (ls : list (nat * T)) (d : T) : Repr :=
      {| footprint := assocToList ls nil
       ; default := d
       |}.

  End parametric.
End Repr2.

Ltac reduce_repr_list ls :=
  eval cbv beta zeta delta [ 
    repr_combine repr listOptToRepr listToRepr nil_Repr
    map 
  ] in ls.
