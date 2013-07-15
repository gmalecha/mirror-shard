Require Import List.
Require Reify ReifySepExpr.
Require Import Expr.
Require Import SepExpr SepLemma.
Require Import Env.

Module Make (ST : SepTheory.SepTheory) (SE : SepExpr.SepExpr ST) 
            (SL : SepLemmaType ST SE).
  Module SEP_REIFY := ReifySepExpr.ReifySepExpr ST SE.

  (* This tactic processes the part of a lemma statement after the quantifiers. *)
  Ltac collectTypes_hint' isConst P types k :=
    match P with
      | fun x => @?H x -> @?P x =>
         ReifyExpr.collectTypes_expr ltac:(isConst) H types ltac:(fun types => 
          collectTypes_hint' ltac:(isConst) P types k)
      | fun x => forall cs, @ST.himp (@?L x) (@?R x) =>
        SEP_REIFY.collectTypes_sexpr ltac:(isConst) L types ltac:(fun types =>
          SEP_REIFY.collectTypes_sexpr ltac:(isConst) R types k)
      | fun x => _ (@?L x) (@?R x) =>
        SEP_REIFY.collectTypes_sexpr ltac:(isConst) L types ltac:(fun types =>
          SEP_REIFY.collectTypes_sexpr ltac:(isConst) R types k)
    end.

  (* This tactic adds quantifier processing. *)
  Ltac collectTypes_hint isConst P types k :=
    match P with
      | fun xs : ?T => forall x : ?T', @?f xs x =>
        match T' with
          | _ => match type of T' with
                   | Prop => fail 1
                   | _ => let P := eval simpl in (fun x : ReifyExpr.VarType (T * T') =>
                     f (@ReifyExpr.openUp _ T (@fst _ _) x) (@ReifyExpr.openUp _ T' (@snd _ _) x)) in
                   let types := Reify.cons_uniq T' types in
                     collectTypes_hint ltac:(isConst) P types k
                 end
        end
      | _ => collectTypes_hint' ltac:(isConst) P types k
    end.

  (* Finally, this tactic adds a loop over all hints. *)
  Ltac collectTypes_hints unfoldTac isConst Ps types k :=
    match Ps with
      | tt => k types
      | (?P1, ?P2) =>
        collectTypes_hints unfoldTac ltac:(isConst) P1 types ltac:(fun types =>
          collectTypes_hints unfoldTac ltac:(isConst) P2 types k)
      | _ =>
        let T := type of Ps in
        let T := eval simpl in T in
        let T := unfoldTac T in
          collectTypes_hint ltac:(isConst) (fun _ : ReifyExpr.VarType unit => T) types k
    end.

  (* Now we repeat this sequence of tactics for reflection itself. *)
  
  Ltac reify_hint' pcType stateType isConst P types funcs preds vars k :=
    match P with
      | fun x => @?H x -> @?P x =>
        ReifyExpr.reify_expr isConst H types funcs (@nil tvar) vars ltac:(fun _ funcs H =>
          reify_hint' pcType stateType isConst P types funcs preds vars ltac:(fun funcs preds P =>
            let lem := eval simpl in (@Lemma.Build_lemma SL.sepConcl vars (H :: Lemma.Hyps P) (Lemma.Concl P)) in
            k funcs preds lem))
      | fun x => @ST.himp (@?L x) (@?R x) =>
        SEP_REIFY.reify_sexpr isConst L types funcs pcType stateType preds (@nil tvar) vars ltac:(fun _uvars funcs preds L =>
          SEP_REIFY.reify_sexpr isConst R types funcs pcType stateType preds (@nil tvar) vars ltac:(fun _uvars funcs preds R =>
            let lem := constr:(@Lemma.Build_lemma SL.sepConcl vars nil (L, R)) in
            k funcs preds lem))
      | fun x => ?Z (@?L x) (@?R x) =>
        SEP_REIFY.reify_sexpr isConst L types funcs pcType stateType preds (@nil tvar) vars ltac:(fun _ funcs preds L =>
          SEP_REIFY.reify_sexpr isConst R types funcs pcType stateType preds (@nil tvar) vars ltac:(fun _ funcs preds R =>
            let lem := constr:(@Lemma.Build_lemma SL.sepConcl vars nil (L, R)) in
            k funcs preds lem))
    end.

  Ltac reify_hint pcType stateType isConst P types funcs preds vars k :=
    match P with
      | fun xs : ?T => forall x : ?T', @?f xs x =>
        match T' with
          | _ => match type of T' with
                   | Prop => fail 1
                   | _ =>
                     let P := eval simpl in (fun x : ReifyExpr.VarType (T' * T) =>
                       f (@ReifyExpr.openUp _ T (@snd _ _) x) (@ReifyExpr.openUp _ T' (@fst _ _) x)) in
                     let T' := ReifyExpr.reflectType types T' in
                     reify_hint pcType stateType isConst P types funcs preds (T' :: vars) k
                   | _ => fail 3
                 end
          | _ => fail 2
        end
      | _ => reify_hint' pcType stateType isConst P types funcs preds vars k
    end.

  (* Main entry point tactic, to generate a hint database *)
  Ltac reify_hints unfoldTac pcType stateType isConst Ps types funcs preds k :=
    match Ps with
      | tt => k funcs preds (@nil (Lemma.lemma types (@SL.sepConcl types))) || fail 2
      | (?P1, ?P2) =>
        reify_hints unfoldTac pcType stateType isConst P1 types funcs preds ltac:(fun funcs preds P1 =>
          reify_hints unfoldTac pcType stateType isConst P2 types funcs preds ltac:(fun funcs preds P2 =>
            k funcs preds (P1 ++ P2)))
        || fail 2
      | _ =>
        let T := type of Ps in
        let T := eval simpl in T in
        let T := unfoldTac T in
        reify_hint pcType stateType isConst (fun _ : ReifyExpr.VarType unit => T) types funcs preds (@nil tvar) ltac:(fun funcs preds P =>
          k funcs preds (P :: nil))
    end.

  (* Build proofs of combined lemma statements *)
  Ltac prove Ps :=
    match Ps with
      | tt => constructor
      | (?P1, ?P2) => 
           (apply Folds.Forall_app; [ prove P1 | prove P2 ])
        || (constructor; [ split; [ reflexivity | exact P1 ] | prove P2 ])
      | _ => constructor; [ split; [ reflexivity | exact Ps ] | constructor ]
    end.


  (* Unfold definitions in a list of types *)
  Ltac unfoldTypes types :=
    match eval hnf in types with
      | nil => types
      | ?T :: ?types =>
        let T := eval hnf in T in
          let types := unfoldTypes types in
            constr:(T :: types)
    end.

  Ltac lift_signature_over_repr s rp :=
    let d := eval simpl Domain in (Domain s) in
    let r := eval simpl Range in (Range s) in
    let den := eval simpl Denotation in (Denotation s) in
    constr:(fun ts' => @Sig (Env.repr rp ts') d r den).
  
  Ltac lift_signatures_over_repr fs rp :=
    match eval hnf in fs with
      | nil => constr:(fun ts' => @nil (signature (repr rp ts')))
      | ?f :: ?fs => 
        let f := lift_signature_over_repr f rp in
        let fs := lift_signatures_over_repr fs rp in
        constr:(fun ts' => (f ts') :: (fs ts'))
    end.
  
  Ltac lift_ssignature_over_repr s rp :=
    let d := eval simpl SE.SDomain in (SE.SDomain s) in
    let den := eval simpl SE.SDenotation in (SE.SDenotation s) in
    constr:(fun ts' => @SE.PSig (repr rp ts') d den).
  
  Ltac lift_ssignatures_over_repr fs rp :=
    match eval hnf in fs with
      | nil => constr:(fun ts' => @nil (SE.predicate (repr rp ts')))
      | ?f :: ?fs => 
        let f := lift_ssignature_over_repr f rp in
        let fs := lift_ssignatures_over_repr fs rp in
        constr:(fun ts' => (f ts') :: (fs ts'))
    end.

(*
  Module TESTS.
    Section Tests.
    Variables pc state : Type.

    Variable f : nat -> ST.hprop.
    Variable h : bool -> unit -> ST.hprop.
    Variable g : bool -> nat -> nat -> nat.

    Ltac isConst e :=
      match e with
        | true => true
        | false => true
        | O => true
        | S ?e => isConst e
        | _ => false
      end.

    Theorem cmp_false T : forall (x y : T), (fun x y => false) x y = true -> x = y.
    Proof. inversion 1. Qed.

    Definition nat_type := {|
      Impl := nat;
      Eqb := fun x y => false ;
      Eqb_correct := cmp_false _
      |}.

    Definition bool_type := {|
      Impl := bool;
      Eqb := fun x y => false ;
      Eqb_correct := cmp_false _
      |}.

    Definition unit_type := {|
      Impl := unit;
      Eqb := fun x y => false ;
      Eqb_correct := cmp_false _
      |}.

    Definition types0 := nat_type :: bool_type :: unit_type :: nil.

    Definition env0 : PACK.TypeEnv  :=
      {| PACK.Types := listToRepr 
           ({| Impl := pc ; Eq := fun _ _ => None |} :: 
            {| Impl := state ; Eq := fun _ _ => None |} :: nil) EmptySet_type
       ; PACK.Funcs := fun ts => nil_Repr (Default_signature _)
       ; PACK.Preds := fun ts => nil_Repr (SE.Default_predicate _ _ _)
      |}.

    Fixpoint assumptionProver (types : list type) (Hs : list (expr types)) (P : expr types) :=
      match Hs with
        | nil => false
        | H :: Hs' => match expr_seq_dec H P with
                        | Some _ => true
                        | None => assumptionProver Hs' P
                      end
      end.

    Hypothesis Hemp : forall cs, ST.himp cs (ST.emp pc state) (ST.emp pc state).
    Hypothesis Hf : forall cs, ST.himp cs (f 0) (ST.emp _ _).
    Hypothesis Hh : forall cs, ST.himp cs (h true tt) (ST.star (h true tt) (f 13)).

    Hypothesis Hf0 : forall n cs, ST.himp cs (f n) (ST.emp _ _).
    Hypothesis Hh0 : forall b u cs, ST.himp cs (h b u) (ST.star (h (negb b) tt) (f 13)).

    Hypothesis Hf1 : forall n, n <> 0 -> forall cs, ST.himp cs (f n) (ST.emp _ _).
    Hypothesis Hh1 : forall b u, b = false -> u <> tt -> forall cs, ST.himp cs (h b u) (ST.star (h b tt) (f 13)).


    (** * Creating hint databases *)

    Ltac prepare := prepareHints ltac:(fun x => x) pc state isConst env0.

    Definition hints_emp : hints.
      prepare (Hemp, Hf) (Hemp, Hf, Hh) ltac:(fun x => refine x).
    Defined.

    Definition hints_tt : hints.
      prepare tt tt ltac:(fun x => refine x).
    Defined.
    End Tests.
  End TESTS.
*)

End Make.