Require Import List.
Require Import Expr.

Section abstracted.
  Variable not : Prop -> Prop.
  Variables (types : list type) 
            (funcs : functions types)
            (meta_env var_env : env types).

  Fixpoint nexprD (e : expr types) (t : tvar) {struct e} : 
    option (tvarD types t) :=
    match e with
      | Const t' c =>
        match equiv_dec t' t with
          | left pf =>
            Some
            match pf in (_ = t0) return (tvarD types t0) with
              | eq_refl => c
            end
          | right _ => None
        end
      | Var x => lookupAs var_env t x
      | Func f xs =>
        match nth_error funcs f with
          | Some f0 =>
            match equiv_dec (Range f0) t with
              | left pf =>
                match pf in (_ = t0) return (option (tvarD types t0)) with
                  | eq_refl =>
                    applyD nexprD (Domain f0) xs (tvarD types (Range f0))
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
End abstracted.

Theorem nexprD_exprD : nexprD not = exprD.
Proof. reflexivity. Qed.