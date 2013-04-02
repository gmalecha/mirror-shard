Require Import Expr SepExpr.
Require Import Lemma.

Set Implicit Arguments.
Set Strict Implicit.

Module Type SepLemmaType (ST : SepTheory.SepTheory) (SE : SepExpr ST).

  Section typed.
    Variable types : list type.
    
    Definition sepConcl : Type :=
      (SE.sexpr types * SE.sexpr types)%type.

    Definition Lhs (l : lemma types sepConcl) : SE.sexpr types :=
      fst (Concl l).
    Definition Rhs (l : lemma types sepConcl) : SE.sexpr types :=
      snd (Concl l).
    
    Definition WellTyped_sepConcl tfuncs tpreds (vars : list tvar) (c : sepConcl) : bool :=
      if SE.WellTyped_sexpr tfuncs tpreds nil vars (fst c)
      then 
        SE.WellTyped_sexpr tfuncs tpreds nil vars (snd c)
      else false.

    Definition sepConclD funcs preds (uvars vars : env types) (c : sepConcl) : Prop :=
      SE.himp funcs preds uvars vars (fst c) (snd c).

    Definition sepLemma : Type := lemma types sepConcl.

    Definition WellTyped_sepLemma tfuncs tpreds (l : sepLemma) : bool :=
      WellTyped_lemma (WellTyped_sepConcl tfuncs tpreds) tfuncs l.

    Definition sepLemmaD (funcs : functions types) (preds : SE.predicates types) 
      (meta_base var_base : env types) (lem : sepLemma) : Prop :=
      lemmaD (WellTyped_sepConcl (typeof_funcs funcs) (SE.typeof_preds preds)) 
             (sepConclD funcs preds) funcs meta_base var_base lem.
  End typed.

End SepLemmaType.

Module SepLemma (ST : SepTheory.SepTheory) (SE : SepExpr ST) <: SepLemmaType ST SE.

  Section typed.
    Variable types : list type.
    
    Definition sepConcl : Type :=
      (SE.sexpr types * SE.sexpr types)%type.

    Definition Lhs (l : lemma types sepConcl) : SE.sexpr types :=
      fst (Concl l).
    Definition Rhs (l : lemma types sepConcl) : SE.sexpr types :=
      snd (Concl l).
    
    Definition WellTyped_sepConcl tfuncs tpreds (vars : list tvar) (c : sepConcl) : bool :=
      if SE.WellTyped_sexpr tfuncs tpreds nil vars (fst c)
      then 
        SE.WellTyped_sexpr tfuncs tpreds nil vars (snd c)
      else false.

    Definition sepConclD funcs preds (uvars vars : env types) (c : sepConcl) : Prop :=
      SE.himp funcs preds uvars vars (fst c) (snd c).

    Definition sepLemma : Type := lemma types sepConcl.

    Definition WellTyped_sepLemma tfuncs tpreds (l : sepLemma) : bool :=
      WellTyped_lemma (WellTyped_sepConcl tfuncs tpreds) tfuncs l.

    Definition sepLemmaD (funcs : functions types) (preds : SE.predicates types) 
      (meta_base var_base : env types) (lem : sepLemma) : Prop :=
      lemmaD (WellTyped_sepConcl (typeof_funcs funcs) (SE.typeof_preds preds)) 
             (sepConclD funcs preds) funcs meta_base var_base lem.
  End typed.

End SepLemma.