Require Import List.
Require Import Expr.
Require Import Coq.Classes.EquivDec.

Section abstracted.
  Variable not : Prop -> Prop.
  Variables (types : list type) 
            (funcs : functions types)
            (meta_env var_env : env types).

  Fixpoint nexprD (e : expr) (t : tvar) {struct e} : 
    option (tvarD types t) :=
    match e with
      | Var x => lookupAs var_env t x
      | Func f xs =>
        match nth_error funcs f with
          | Some f0 =>
            match equiv_dec (Range f0) t with
              | left pf =>
                match pf in (_ = t0) return (option (tvarD types t0)) with
                  | eq_refl =>
                    applyD types nexprD (Domain f0) xs (tvarD types (Range f0))
                    (Denotation f0)
                end
              | right _ => None
            end
          | None => None
        end
      | Equal t' e1 e2 =>
        match t as t0 return (option (tvarD types t0)) with
          | tvProp =>
            match nexprD e1 t' with
              | Some v1 =>
                match nexprD e2 t' with
                  | Some v2 => Some (v1 = v2)
                  | None => None
                end
              | None => None
            end
          | tvType n => None
        end
      | Not e1 =>
        match t as t0 return (option (tvarD types t0)) with
          | tvProp =>
            match nexprD e1 tvProp with
              | Some p => Some (not p)
              | None => None
            end
          | tvType n => None
        end
      | UVar x => lookupAs meta_env t x
    end.

  Fixpoint nAllProvable_impl (k : Prop) (es : list expr) : Prop :=
    match es with
      | nil => k
      | e :: es =>
        match nexprD e tvProp with
          | None => False
          | Some v => v 
        end -> nAllProvable_impl k es
    end.

  Fixpoint nAllProvable_and (k : Prop) (es : list expr) : Prop :=
    match es with
      | nil => k
      | e :: es =>
        match nexprD e tvProp with
          | None => False
          | Some v => v
        end /\ nAllProvable_and k es
    end.

End abstracted.

Theorem nexprD_exprD : nexprD not = exprD.
Proof. reflexivity. Qed.

Theorem nAllProvable_impl_AllProvable_impl : forall a b c d e f, 
  @nAllProvable_impl not a b c d e f <-> @AllProvable_impl a b c d e f.
Proof. 
  induction f; simpl.
  reflexivity.
  rewrite <- IHf. unfold Provable in *.
  rewrite nexprD_exprD. reflexivity. 
Qed.

Theorem nAllProvable_and_AllProvable_and : forall a b c d e f, 
  @nAllProvable_and not a b c d e f <-> @AllProvable_and a b c d e f.
Proof. 
  induction f; simpl.
  reflexivity.
  rewrite <- IHf. unfold Provable in *.
  rewrite nexprD_exprD. reflexivity. 
Qed.
