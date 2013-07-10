Require Import List.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Core.RelDec.
Require Import MirrorShard.Expr.
Require Import MirrorShard.Env.

Set Implicit Arguments.
Set Strict Implicit.

Fixpoint footprint_set T (n : nat) (v : T) (ls : list (option T)) : list (option T) :=
  match n with
    | 0 => Some v :: tl ls
    | S n => hd None ls :: footprint_set n v (tl ls)
  end.

Definition repr_require T (n : nat) (v : T) (r : Repr T) : Repr T :=
  {| footprint := footprint_set n v r.(footprint)
   ; default := r.(default)
   |}.


Section asConst_nat.
  Let nat_idx : nat := 0.
  Let O_idx : func := 0.
  Let S_idx : func := 1.
  
  Fixpoint asConst_nat (e : expr) : option nat :=
    match e with
      | Func i args =>
        if i ?[ eq ] O_idx then Some 0
        else if i ?[ eq ] S_idx then 
               match args with
                 | e :: nil =>
                   match asConst_nat e with
                     | Some r => Some (S r)
                     | None => None
                   end
                 | _ => None
               end
             else
               None
      | _ => None
    end.

  Variable nat_cmp : nat -> nat -> bool.
  Variable nat_cmp_correct : forall a b, nat_cmp a b = true -> a = b.
  Variable def_type : type.
  Let tvNat := tvType nat_idx.
  Variable ts' : list type.
  Print type.
  Let ts := repr (repr_require nat_idx {| Expr.Impl := nat ; Eqb := nat_cmp ; Eqb_correct := nat_cmp_correct |} (nil_Repr def_type)) ts'.
  Variable fs' : functions ts.
  Variable def_func : signature ts.
  Print signature.
  Let fs := repr (repr_require O_idx (@Sig ts nil (tvType nat_idx) 0)
                               (repr_require S_idx (@Sig ts (tvType nat_idx :: nil) (tvType nat_idx) S) (nil_Repr def_func))) fs'.

  Theorem asConst_nat_ok : forall e n U V , 
                             is_well_typed (typeof_funcs fs) (typeof_env U) (typeof_env V) e tvNat = true ->
                             asConst_nat e = Some n ->
                             exprD fs U V e tvNat = Some n.
  Proof.
    induction e; simpl; intros; try congruence.
    consider (EqNat.beq_nat f O_idx); intros; subst; simpl in *.
    { inversion H2; clear H2; subst.
      destruct l; simpl in *; try congruence. }
    { consider (EqNat.beq_nat f S_idx); intros; subst; try congruence.
      simpl in *.
      repeat (destruct l; try congruence; []); simpl in *.
      inversion H; clear H; subst.
      consider (asConst_nat e); intros; subst; try congruence.
      match goal with
        | _ : (if ?X then _ else _) = true |- _ =>
          consider X; intros
      end.
      erewrite H5; eauto. }
  Qed.
   
End asConst_nat.
