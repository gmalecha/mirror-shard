Require Import List.
Require Import SepExpr.
Require Import ExprTac.

Module Make (ST : SepTheory.SepTheory) (SE : SepExpr ST).

  Section abstracted.
    Variables (not : Prop -> Prop) 
              (emp : ST.hprop)
              (star : ST.hprop -> ST.hprop -> ST.hprop)
              (ex : forall T : Type, (T -> ST.hprop) -> ST.hprop)
              (inj : Prop -> ST.hprop).
    Variables (types : list Expr.type) (funcs : Expr.functions types)
      (sfuncs : SE.predicates types) (meta_env : Expr.env types).

    Fixpoint nsexprD (var_env : Expr.env types) (s : SE.sexpr)
      {struct s} : ST.hprop :=
      match s with
        | SE.Emp => emp
        | SE.Inj p =>
          match nexprD not types funcs meta_env var_env p Expr.tvProp with
            | Some p0 => inj p0
            | None => inj (SepExpr.BadInj p)
          end
        | SE.Star l r =>
          star (nsexprD var_env l) (nsexprD var_env r)
        | SE.Exists t b =>
          ex _
          (fun x : Expr.tvarD types t =>
            nsexprD (@existT _ (Expr.tvarD types) t x :: var_env) b)
        | SE.Func f b =>
          match nth_error sfuncs f with
            | Some f' =>
              match
                Expr.applyD types (nexprD not types funcs meta_env var_env) 
                (SE.SDomain f') b ST.hprop (SE.SDenotation f')
                with
                | Some p => p
                | None => inj (SepExpr.BadPredApply f b var_env)
              end
            | None => inj (SepExpr.BadPred f)
          end
        | SE.Const p => p
      end.
  End abstracted.
  
  Theorem nsexprD_sexprD : nsexprD not ST.emp ST.star ST.ex ST.inj = SE.sexprD.
  Proof. reflexivity. Qed.
End Make.
    
      