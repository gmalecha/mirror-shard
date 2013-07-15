Require Import List.
Require Import Folds Tactics.
Require Import ExtLib.Tactics.Consider.
Require Import Instantiation ExprUnify.
Require Import Expr SepExpr SepHeap SepCancel.
Require Import Prover.

Set Implicit Arguments.
Set Strict Implicit.

Module Type Ordering (ST : SepTheory.SepTheory)
                     (SE : SepExpr ST)
                     (SH : SepHeap ST SE).

  Section typed.
    Variable types : list type.

    Parameter order_impures : MM.mmap exprs -> list (exprs * nat).

    Parameter meta_order_args : exprs -> exprs -> Datatypes.comparison.
    
    Parameter meta_order_funcs : (exprs * func) -> (exprs * func) -> Datatypes.comparison.
    
    Axiom order_impures_D : forall (funcs : functions types) preds U G imps,
      SE.heq funcs preds U G 
            (SH.impuresD imps)
            (SH.starred (fun v => (SE.Func (snd v) (fst v))) (order_impures imps) SE.Emp).

    Axiom order_impures_WellTyped : forall tf tp tU tG imp,
      SH.WellTyped_impures tf tp tU tG imp = true ->
      allb (fun v : list expr * func => SE.WellTyped_sexpr tf tp tU tG
        (SE.Func (snd v) (fst v))) (order_impures imp) = true.
  End typed.
End Ordering.

Lemma allb_permutation : forall T F (a b : list T),
  Permutation.Permutation a b ->
  allb F a = allb F b.
Proof. clear.
  induction 1; simpl; auto.
  destruct (F x); auto.
  destruct (F x); destruct (F y); auto.
  rewrite IHPermutation1; auto.
Qed.

Module DefaultOrdering (ST : SepTheory.SepTheory)
                       (SE : SepExpr ST)
                       (SH : SepHeap ST SE) <: Ordering ST SE SH.

  Module HEAP_FACTS := SepHeapFacts ST SE SH.
  Module Import SEP_FACTS := HEAP_FACTS.SEP_FACTS.
  
  Section typed.
    Variable types : list type.

    (** This function determines whether an expression [l] is more "defined"
     ** than an expression [r]. An expression is more defined if it "uses UVars later".
     ** NOTE: This is a "fuzzy property" but correctness doesn't depend on it.
     **)
    Fixpoint expr_count_meta (e : expr) : nat :=
      match e with
        | Var _ => 0
        | UVar _ => 1
        | Not l => expr_count_meta l
        | Equal _ l r => expr_count_meta l + expr_count_meta r
        | Expr.Func _ args =>
          fold_left plus (map expr_count_meta args) 0
      end.

    Fixpoint exprs_count_meta (es : exprs) : nat :=
      match es with
        | nil => O
        | e :: es' => expr_count_meta e + exprs_count_meta es'
      end.

    (** When expressions have the same number of uvars, we want to favor the larger
     ** expressions first, since they are less likely to match spuriously. *)
    Fixpoint expr_size (e : expr) : nat :=
      match e with
        | Var _
        | UVar _ => 0
        | Not l => S (expr_size l)
        | Equal _ l r => S (expr_size l + expr_size r)
        | Expr.Func _ args => fold_left plus (map expr_size args) 1
      end.

    Definition meta_order_args (l r : exprs) : Datatypes.comparison :=
      match Compare_dec.nat_compare (exprs_count_meta l) (exprs_count_meta r) with
        | Datatypes.Eq =>
          Ordering.list_lex_cmp _ (fun l r => Compare_dec.nat_compare (expr_size l) (expr_size r)) l r
        | v => v
      end.

    Definition meta_order_funcs (l r : exprs * func) : Datatypes.comparison :=
      match snd l, snd r with
        | 2, 0 => Datatypes.Lt
        | 2, 1 => Datatypes.Lt
        | 2, S (S (S _)) => Datatypes.Lt
        | _, _ =>
          match meta_order_args (fst l) (fst r) with
            | Datatypes.Eq => Compare_dec.nat_compare (snd l) (snd r)
            | x => x
          end
      end.

    Definition order_impures (imps : MM.mmap exprs) : list (exprs * nat) :=
      FM.fold (fun k => fold_left (fun (acc : list (exprs * nat)) (args : exprs) => 
        Ordering.insert_in_order _ meta_order_funcs (args, k) acc)) imps nil.

    Lemma impuresD'_flatten : forall (funcs : functions types) preds U G imps,
      SE.heq funcs preds U G
        (SH.impuresD imps)
        (SH.starred (fun v => SE.Func (snd v) (fst v)) 
          (FM.fold (fun f argss acc => 
            map (fun args => (args, f)) argss ++ acc) imps nil) SE.Emp).
    Proof.
      clear. intros. eapply MM.PROPS.fold_rec; intros.
      { rewrite (SH.impuresD_Empty funcs preds U G H).
        rewrite SH.starred_def. simpl. reflexivity. }

      { rewrite SH.impuresD_Add; eauto. rewrite SH.starred_app. 
        rewrite H2. symmetry. rewrite SH.starred_base. heq_canceler.
        repeat rewrite SH.starred_def.
        clear; induction e; simpl; intros; try reflexivity.
        rewrite IHe. reflexivity. }
    Qed.

    Lemma fold_Permutation : forall imps L R,
      Permutation.Permutation L R ->
      Permutation.Permutation
      (FM.fold (fun (f : FM.key) (argss : list exprs) (acc : list (exprs * FM.key)) =>
        map (fun args : exprs => (args, f)) argss ++ acc) imps L)
      (FM.fold
        (fun k : FM.key =>
         fold_left
           (fun (acc : list (exprs * nat)) (args : exprs) =>
            Ordering.insert_in_order (exprs * nat) meta_order_funcs
              (args, k) acc)) imps R).
    Proof.
      clear. intros.
      eapply @MM.PROPS.fold_rel; simpl; intros; auto.
        revert H1; clear. revert a; revert b; induction e; simpl; intros; auto.
        rewrite <- IHe; eauto.
        
        destruct (@Ordering.insert_in_order_inserts (exprs * nat) meta_order_funcs (a,k) b) as [ ? [ ? [ ? ? ] ] ].
        subst. rewrite H.
        rewrite <- app_ass.
        eapply Permutation.Permutation_cons_app.
        rewrite app_ass. eapply Permutation.Permutation_app; eauto.
    Qed.

    Lemma order_impures_D : forall (funcs : functions types) preds U G imps,
      SE.heq funcs preds U G 
        (SH.impuresD imps)
        (SH.starred (fun v => (SE.Func (snd v) (fst v))) (order_impures imps) SE.Emp).
    Proof.
      clear. intros. rewrite impuresD'_flatten. unfold order_impures.
      eapply SH.starred_perm. eapply fold_Permutation. reflexivity.
    Qed.

    Lemma fold_left_insert_perm : forall e a k,
      Permutation.Permutation (map (fun x => (x,k)) e ++ a)
      (fold_left
        (fun (acc : list (exprs * nat)) (args : exprs) =>
          Ordering.insert_in_order (exprs * func) meta_order_funcs
          (args, k) acc) e a).
    Proof.
      clear. induction e; simpl.
      eauto.
      intros. rewrite <- IHe; clear IHe.
      destruct (@Ordering.insert_in_order_inserts _ meta_order_funcs (a,k) a0). destruct H.
      intuition subst. rewrite H0.
      rewrite <- app_ass. rewrite <- app_ass.
      eapply Permutation.Permutation_middle.
    Qed.

    Lemma fold_left_fold_left_insert_perm : forall l (B : list (exprs * nat)),
      Permutation.Permutation 
      (B ++ fold_left (fun (a : list (exprs * nat)) (p : FM.key * list (list expr)) =>
        fold_left (fun (acc : list (exprs * nat)) (args : list expr) =>
          Ordering.insert_in_order (list expr * func) meta_order_funcs (args, fst p) acc) (snd p) a) l nil)
      (fold_left (fun (a : list (exprs * nat)) (p : FM.key * list (list expr)) =>
        fold_left (fun (acc : list (exprs * nat)) (args : list expr) =>
          Ordering.insert_in_order (list expr * func) meta_order_funcs (args, fst p) acc) (snd p) a) l B).
    Proof.
      induction l; simpl; intros. 
      rewrite app_nil_r; reflexivity.
      etransitivity. 2: eapply IHl. destruct a; simpl. 
      symmetry. 
      rewrite Permutation.Permutation_app_tail.
      2: symmetry; apply (@fold_left_insert_perm l0 B k).
      rewrite Permutation.Permutation_app_tail.
      2: apply Permutation.Permutation_app_comm with (l' := B). rewrite app_ass.
      apply Permutation.Permutation_app_head.
      etransitivity. 2: eapply IHl. apply Permutation.Permutation_app_tail.
      etransitivity. 2: apply fold_left_insert_perm. rewrite app_nil_r; auto.
    Qed.

    Lemma order_impures_WellTyped : forall tf tp tU tG imp,
      SH.WellTyped_impures tf tp tU tG imp = true ->
      allb (fun v : list expr * func => SE.WellTyped_sexpr tf tp tU tG
        (SE.Func (snd v) (fst v))) (order_impures imp) = true.
    Proof. clear.
      intros. unfold order_impures.
      rewrite SH.WellTyped_impures_spec_eq in H.
      rewrite FM.fold_1 in *. revert H. unfold exprs in *. generalize true at 2 4.
      induction (FM.elements (elt:=list (list expr)) imp); auto; intros.
      simpl in *. 
      assert (fold_left
        (fun (a : bool) (p : FM.key * list (list expr)) =>
          (a &&
            match snd p with
              | nil => true
              | _ :: _ =>
                match nth_error tp (fst p) with
                  | Some ts =>
                    allb
                    (fun args : list expr =>
                      all2
                      (is_well_typed tf
                        tU tG) args ts) 
                    (snd p)
                  | None => false
                end
            end)%bool) l false = false).
      { clear. induction l; simpl; auto. } 
      destruct b; simpl in H; try congruence.
      destruct a. destruct l0; simpl in *. eauto.
      consider (nth_error tp k); intros; try congruence.
      consider (all2 (is_well_typed tf tU tG) l0 t); intros; try congruence.
      consider (allb
        (fun args : list expr =>
          all2
          (is_well_typed tf tU tG) args t) l1); intros; try congruence.
      rewrite <- IHl by assumption.
      erewrite allb_permutation. 
      2: symmetry; apply fold_left_fold_left_insert_perm.
      rewrite allb_app. erewrite <- allb_permutation.
      2: eapply fold_left_insert_perm.
      rewrite allb_app. rewrite allb_map. simpl. unfold exprs in *.
      think. simpl. auto. 
    Qed.

  End typed.
End DefaultOrdering.

Module Make (SUBST : Subst)
            (U : SyntacticUnifier SUBST)
            (ST : SepTheory.SepTheory)
            (Import SE : SepExpr ST)
            (SH : SepHeap ST SE)
            (O : Ordering ST SE SH)
  <: Canceller SUBST ST SE SH.

  Module HEAP_FACTS := SepHeapFacts ST SE SH.
  Module Import SEP_FACTS := HEAP_FACTS.SEP_FACTS.
  Import HEAP_FACTS.
  Module Import SEP_UFACTS := SepUnify.Make SUBST ST SE SH.

  Section env.
    Variable types : list type.

    Variable funcs : functions types.
    Variable preds : SE.predicates types.

    (** The actual tactic code **)
    Variable Prover : ProverT.
    Variable Prover_correct : ProverT_correct Prover funcs.

    Definition unifyArgs (bound : nat) (summ : Facts Prover) (l r : list expr) (ts : list tvar) (sub : SUBST.Subst)
      : option SUBST.Subst :=
      Folds.fold_left_3_opt 
        (fun l r t (acc : SUBST.Subst) =>
          if Prove Prover summ (Expr.Equal t (SUBST.exprInstantiate acc l) (SUBST.exprInstantiate acc r))
            then Some acc
            else U.exprUnify bound l r acc)
        l r ts sub.

    Fixpoint unify_remove (bound : nat) (summ : Facts Prover) (l : exprs) (ts : list tvar) (r : list exprs)
      (sub : SUBST.Subst)
      : option (list (list expr) * SUBST.Subst) :=
        match r with 
          | nil => None
          | a :: b => 
            match unifyArgs bound summ l a ts sub with
              | None => 
                match unify_remove bound summ l ts b sub with
                  | None => None
                  | Some (x,sub) => Some (a :: x, sub)
                end
              | Some sub => Some (b, sub)
            end
        end.
    
    Section with_typing.
      Variable tfuncs : tfunctions.
      Variables tU tG : tenv.
      Variables U G : env types.

      Hypothesis WT_funcs : WellTyped_funcs tfuncs funcs.
      Hypothesis WT_env_U : WellTyped_env tU U.
      Hypothesis WT_env_G : WellTyped_env tG G.

      Lemma unifyArgs_Extends_WellTyped : forall bound summ l r ts S S',
        SUBST.Subst_WellTyped tfuncs tU tG S ->
        all2 (is_well_typed tfuncs tU tG) l ts = true ->
        all2 (is_well_typed tfuncs tU tG) r ts = true ->
        unifyArgs bound summ l r ts S = Some S' ->
        SUBST.Subst_Extends S' S /\
        SUBST.Subst_WellTyped tfuncs tU tG S'.
      Proof.
        unfold unifyArgs; induction l; destruct r; destruct ts; simpl; intros; try congruence.
        { inversion H2. subst; intuition; auto. }
        { repeat match goal with
          | [ H : (if ?X then _ else _) = true |- _ ] =>
            revert H; case_eq X; intros; [ | congruence ]
                   | [ |- context [ exprD ?A ?B ?C ?D ?E ] ] =>
                     case_eq (exprD A B C D E); intros
                 end; simpl in *;
        try solve [ 
          match goal with
            | [ H : is_well_typed _ _ _ ?e _ = true , H' : exprD _ _ _ (SUBST.exprInstantiate ?S' ?e) _ = None |- _ ] =>
              exfalso; revert H; revert H'; clear; intros H' H;
                eapply WellTyped_exprInstantiate with (S := S') in H;
                  eapply is_well_typed_correct in H;
                    rewrite H' in H ; destruct H; congruence
          end ].
          consider (Prove Prover summ (Equal t (SUBST.exprInstantiate S a) (SUBST.exprInstantiate S e))); simpl; eauto.
          consider (U.exprUnify bound a e S); intros; try congruence.
          eapply IHl in H6; eauto using U.exprUnify_WellTyped.
          intuition. etransitivity; eauto using U.exprUnify_Extends. }
      Qed.          

      Lemma unifyArgs_bad_cases : forall summ bound S S' ts t e a l r,
        SUBST.Subst_WellTyped tfuncs tU tG S ->
        all2 (is_well_typed tfuncs tU tG) l ts = true ->
        all2 (is_well_typed tfuncs tU tG) r ts = true ->
        is_well_typed tfuncs tU tG a t = true ->
        is_well_typed tfuncs tU tG e t = true ->
        match
          (if Prove Prover summ
            (Equal t (SUBST.exprInstantiate S a) (SUBST.exprInstantiate S e))
            then Some S
            else U.exprUnify bound a e S)
          with
          | Some acc =>
            fold_left_3_opt
            (fun (l r : expr) (t : tvar) (acc0 : SUBST.Subst) =>
              if Prove Prover summ
                (Equal t (SUBST.exprInstantiate acc0 l)
                  (SUBST.exprInstantiate acc0 r))
                then Some acc0
                else U.exprUnify bound l r acc0) l r ts acc
          | None => None
        end = Some S' ->
        SUBST.Subst_Extends S' S /\ SUBST.Subst_WellTyped tfuncs tU tG S'.
      Proof.
        intros. destruct (Prove Prover summ (Equal t (SUBST.exprInstantiate S a) (SUBST.exprInstantiate S e))).
        apply unifyArgs_Extends_WellTyped in H4; eauto; intuition.
        revert H4. case_eq (U.exprUnify bound a e S); intros; eauto.
        generalize H4. eapply U.exprUnify_Extends in H4.
        intro. eapply U.exprUnify_WellTyped in H6; eauto.
        eapply unifyArgs_Extends_WellTyped in H5; eauto; intuition.
        etransitivity; eauto. 
        congruence.
      Qed.

      Lemma unifyArgsOk : forall bound summ R l r ts f S S',
        SUBST.Subst_WellTyped tfuncs tU tG S ->
        Valid Prover_correct U G summ ->
        all2 (is_well_typed tfuncs tU tG) l ts = true ->
        all2 (is_well_typed tfuncs tU tG) r ts = true ->
        unifyArgs bound summ l r ts S = Some S' ->
        SUBST.Subst_equations funcs U G S' ->
        @applyD types (exprD funcs U G) ts (map (SUBST.exprInstantiate S') l) R f =
        @applyD types (exprD funcs U G) ts (map (SUBST.exprInstantiate S') r) R f /\
        SUBST.Subst_Extends S' S /\
        SUBST.Subst_WellTyped tfuncs tU tG S'.
      Proof.
        unfold unifyArgs; induction l; destruct r; destruct ts; simpl; intros; try congruence.
        { inversion H2. inversion H3; subst; intuition; auto. }
        { repeat match goal with
          | [ H : (if ?X then _ else _) = true |- _ ] =>
            revert H; case_eq X; intros; [ | congruence ]
                   | [ |- context [ exprD ?A ?B ?C ?D ?E ] ] =>
                     case_eq (exprD A B C D E); intros
                 end; simpl in *;
        try solve [ 
          match goal with
            | [ H : is_well_typed _ _ _ ?e _ = true , H' : exprD _ _ _ (SUBST.exprInstantiate ?S' ?e) _ = None |- _ ] =>
              exfalso; revert H; revert H'; clear; intros H' H;
                eapply WellTyped_exprInstantiate with (S := S') in H;
                  eapply is_well_typed_correct in H;
                    rewrite H' in H ; destruct H; congruence
          end ].
          revert H3. case_eq (Prove Prover summ (Equal t (SUBST.exprInstantiate S a) (SUBST.exprInstantiate S e))); intros.
          { eapply Prove_correct in H3; eauto.
            erewrite SUBST.exprInstantiate_WellTyped in H2 by eauto.
            erewrite SUBST.exprInstantiate_WellTyped in H1 by eauto.
            eapply is_well_typed_correct in H2; eauto.
            eapply is_well_typed_correct in H1; eauto.
            destruct H2; destruct H1.
            unfold ValidProp, Provable in *. simpl in *.
            repeat match goal with 
                     | [ H : _ = _ |- _ ] => rewrite H in *
                     | [ H : ?X -> ?Y |- _ ] => 
                       let H' := fresh in assert (H':X) by eauto; specialize (H H')
                   end.
            subst.
            eapply IHl with (f := f t0) in H9; eauto.
            intuition. rewrite H3. f_equal. f_equal.
            erewrite <- SUBST.Subst_equations_exprInstantiate in H2 by eauto.
            erewrite <- SUBST.Subst_equations_exprInstantiate in H1 by eauto.
            rewrite SUBST.exprInstantiate_Extends in H2 by eauto.
            rewrite SUBST.exprInstantiate_Extends in H1 by eauto.
            rewrite H2 in H8. rewrite H1 in H7. inversion H7; inversion H8; subst; auto. }
          { clear H3. revert H9. case_eq (U.exprUnify bound a e S); intros; try congruence.
            eapply IHl with (f := f t0) in H9; eauto using U.exprUnify_WellTyped.
            intuition.
            rewrite H10. f_equal. f_equal.
            eapply U.exprUnify_sound_sem with (funcs := funcs) (U := U) (G := G) (t := t) in H3.
            generalize H9. 
            eapply SUBST.exprInstantiate_Extends with (t := a) in H9.
            intro.
            eapply SUBST.exprInstantiate_Extends with (t := e) in H11.
            rewrite <- H9 in H7.
            rewrite <- H11 in H8.
            rewrite SUBST.Subst_equations_exprInstantiate in H7 by eassumption.
            rewrite SUBST.Subst_equations_exprInstantiate in H8 by eassumption.
            rewrite H3 in H7. rewrite H7 in H8. inversion H8; auto.

            etransitivity; eauto using U.exprUnify_Extends. }
          { exfalso.
            eapply unifyArgs_bad_cases in H3; eauto; intuition.
            do 2 match goal with
              | [ H : is_well_typed _ _ _ ?E _ = true ,
                  H' : exprD _ _ _ ?E _ = None |- _ ] =>
              (eapply is_well_typed_correct in H ; eauto) ; destruct H; congruence
              | [ H : exprD _ _ _ ?E _ = None |- _ ] =>
                assert (is_well_typed tfuncs tU tG E t = true) by 
                  (rewrite <- SUBST.exprInstantiate_WellTyped; eauto)
            end. }
          { exfalso.
            eapply unifyArgs_bad_cases in H3; eauto; intuition.
            do 2 match goal with
              | [ H : is_well_typed _ _ _ ?E _ = true ,
                  H' : exprD _ _ _ ?E _ = None |- _ ] =>
              (eapply is_well_typed_correct in H ; eauto) ; destruct H; congruence
              | [ H : exprD _ _ _ ?E _ = None |- _ ] =>
                assert (is_well_typed tfuncs tU tG E t = true) by 
                  (rewrite <- SUBST.exprInstantiate_WellTyped; eauto)
            end. }
          { exfalso.
            eapply unifyArgs_bad_cases in H3; eauto; intuition.
            do 2 match goal with
              | [ H : is_well_typed _ _ _ ?E _ = true ,
                  H' : exprD _ _ _ ?E _ = None |- _ ] =>
              (eapply is_well_typed_correct in H ; eauto) ; destruct H; congruence
              | [ H : exprD _ _ _ ?E _ = None |- _ ] =>
                assert (is_well_typed tfuncs tU tG E t = true) by 
                  (rewrite <- SUBST.exprInstantiate_WellTyped; eauto)
            end. } }
      Qed.
      
      Lemma unify_removeOk : forall bound summ f p l S,
        SUBST.Subst_WellTyped tfuncs tU tG S ->
        Valid Prover_correct U G summ ->
        nth_error preds f = Some p ->
        all2 (is_well_typed tfuncs tU tG) l (SE.SDomain p) = true ->
        forall r r' S' P,
          List.Forall (fun r => all2 (is_well_typed tfuncs tU tG) r (SE.SDomain p) = true) r ->
          unify_remove bound summ l (SE.SDomain p) r S = Some (r', S') ->
          SUBST.Subst_equations funcs U G S' ->
          forall Q,
          SE.himp funcs preds U G (SH.starred (SE.Func f) r' Q) P ->
          SE.himp funcs preds U G
            (SH.starred (SE.Func f) r Q) (SE.Star (SE.Func f l) P) /\
          SUBST.Subst_Extends S' S.
      Proof.
        induction r; simpl; intros; try congruence.
        revert H4. case_eq (unifyArgs bound summ l a (SDomain p) S); intros; try congruence.
        { inversion H7; clear H7; subst.
          inversion H3; clear H3; subst.
          rewrite SH.starred_def. simpl. rewrite <- SH.starred_def.
          eapply unifyArgsOk with (R := ST.hprop) (f := SDenotation p) in H4;
            eauto. 
          intuition.
          apply himp_star_frame; auto. unfold himp; simpl. rewrite H1.
          match goal with
            | [ |- ST.himp match ?X with _ => _ end match ?Y with _ => _ end ] =>
              cutrewrite (X = Y)
          end. reflexivity.
          revert H3. repeat rewrite applyD_forget_exprInstantiate by eauto; eauto. }
        { revert H7. case_eq (unify_remove bound summ l (SDomain p) r S); intros; try congruence.
          destruct p0. inversion H8; clear H8; subst. clear H4.
          inversion H3; clear H3; subst.
          rewrite SH.starred_def in H6. simpl in H6. rewrite <- SH.starred_def in H6.
          eapply IHr in H7; eauto.
          Focus 2. instantiate (2 := (SE.Star (Func f a) Q)). instantiate (1 := P).
          etransitivity; [ | eapply H6 ].
          rewrite SH.starred_base. rewrite heq_star_assoc. 
          rewrite SH.starred_base with (base := Q). reflexivity.
          intuition. rewrite starred_cons. rewrite <- H3. 
          rewrite SH.starred_base. rewrite SH.starred_base with (base := SE.Star (Func f a) Q). 
          rewrite heq_star_assoc. reflexivity. }
      Qed.

      Lemma unify_remove_PureFacts : forall bound summ f p l S,
        SUBST.Subst_WellTyped tfuncs tU tG S ->
        nth_error preds f = Some p ->
        all2 (is_well_typed tfuncs tU tG) l (SDomain p) = true ->
        forall r r' S',
          List.Forall (fun r => all2 (is_well_typed tfuncs tU tG) r (SDomain p) = true) r ->
          unify_remove bound summ l (SDomain p) r S = Some (r', S') ->
             SUBST.Subst_Extends S' S
          /\ SUBST.Subst_WellTyped tfuncs tU tG S'
          /\ List.Forall (fun r => all2 (is_well_typed tfuncs tU tG) r (SDomain p) = true) r'.
      Proof.
        induction r; simpl; intros; try congruence.
        consider (unifyArgs bound summ l a (SDomain p) S); intros.
        { inversion H4; clear H4; subst. inversion H2; clear H2; subst.
          eapply unifyArgs_Extends_WellTyped in H3; eauto. intuition eauto. }
        { consider (unify_remove bound summ l (SDomain p) r S); intros.
          { destruct p0. inversion H5; clear H5; subst. inversion H2; clear H2; subst.
            eapply IHr in H8; intuition. eauto. eauto. eauto. }
          { congruence. } }
      Qed.

    End with_typing.

    Definition cancel_list : Type := list (exprs * nat).
    
    (** NOTE : l and r are reversed here **)
    (** cancel_in_order ls acc rem = (l,r,sub) ->
     ** r ===> l ->
     ** rem ===> ls * acc
     **)
    Fixpoint cancel_in_order (bound : nat) (summ : Facts Prover) (tpreds : SE.tpredicates)
      (ls : cancel_list) (acc rem : MM.mmap exprs) (sub : SUBST.Subst)
      (progress : bool)
      : option (MM.mmap exprs * MM.mmap exprs * SUBST.Subst) :=
      match ls with
        | nil => 
          if progress then Some (acc, rem, sub) else None
        | (args,f) :: ls => 
          match FM.find f rem with
            | None => cancel_in_order bound summ tpreds ls (MM.mmap_add f args acc) rem sub progress
            | Some argss =>
              match nth_error tpreds f with
                | None => cancel_in_order bound summ tpreds ls (MM.mmap_add f args acc) rem sub progress (** Unused! **)
                | Some ts => 
                  match unify_remove bound summ args ts argss sub with
                    | None => cancel_in_order bound summ tpreds ls (MM.mmap_add f args acc) rem sub progress
                    | Some (rem', sub) =>
                      cancel_in_order bound summ tpreds ls acc (FM.add f rem' rem) sub true
                  end
              end                      
          end
      end.

    Lemma cancel_in_order_equiv : forall bound summ tpreds ls acc rem sub L R S acc' progress,
      MM.mmap_Equiv acc acc' ->
      cancel_in_order bound summ tpreds ls acc rem sub progress = Some (L, R, S) ->
      exists L' R' S',
        cancel_in_order bound summ tpreds ls acc' rem sub progress = Some (L', R', S') /\
        MM.mmap_Equiv L L' /\
        MM.mmap_Equiv R R' /\
        SUBST.Subst_Equal S S'.
    Proof.
      clear. induction ls; simpl; intros.
      { inversion H0; subst; auto. 
        destruct progress; try congruence. inversion H0; clear H0; subst.
        do 3 eexists. split; [ reflexivity | intuition ]. }
      { repeat match goal with
                 | [ H : match ?X with 
                           | (_,_) => _
                         end = _ |- _ ] => destruct X
                 | [ H : match ?X with
                           | Some _ => _ | None => _ 
                         end = _ |- _ ] =>
                 revert H; case_eq X; intros
               end;
        (eapply IHls; [ eauto using MM.mmap_add_mor | eassumption ]). }
    Qed.

    Lemma cancel_in_order_mmap_add_acc : forall bound summ tpreds ls n e acc rem sub L R S progress,
      cancel_in_order bound summ tpreds ls (MM.mmap_add n e acc) rem sub progress = Some (L, R, S) ->
      exists L' R' S',
        cancel_in_order bound summ tpreds ls acc rem sub progress = Some (L', R', S') /\
        MM.mmap_Equiv (MM.mmap_add n e L') L /\
        MM.mmap_Equiv R R' /\
        SUBST.Subst_Equal S S'.
    Proof.
      clear. induction ls; simpl; intros.
      { inversion H; subst.
        destruct progress; try congruence. inversion H; clear H; subst.
        do 3 eexists; split. 
        reflexivity. split; try reflexivity. split; try reflexivity. }
      { repeat match goal with
                 | [ H : match ?X with 
                           | (_,_) => _
                         end = _ |- _ ] => destruct X
                 | [ H : match ?X with
                           | Some _ => _ | None => _ 
                         end = _ |- _ ] =>
                 revert H; case_eq X; intros
               end;
        try solve [ eapply IHls; eauto ];
        match goal with
          | [ H : cancel_in_order _ _ _ _ _ _ _ _ = _ |- _ ] =>
            eapply cancel_in_order_equiv in H; [ | eapply MM.mmap_add_comm ]
        end;
        repeat match goal with
                 | [ H : exists x, _ |- _ ] => destruct H
                 | [ H : _ /\ _ |- _ ] => destruct H
               end;
        match goal with
          | [ H : cancel_in_order _ _ _ _ _ _ _ _ = _ |- _ ] =>
            eapply IHls in H
        end;
        repeat match goal with
                 | [ H : exists x, _ |- _ ] => destruct H
                 | [ H : _ /\ _ |- _ ] => destruct H
                 | [ |- exists x, _ /\ _ ] => eexists; split; [ eassumption | ]
                 | [ |- exists x, _ ] => eexists
                 | [ H : MM.mmap_Equiv _ _ |- _ ] => rewrite H
                 | [ H : SUBST.Subst_Equal _ _ |- _ ] => rewrite H
               end; try intuition reflexivity. }
    Qed.

    Lemma nth_error_typeof_preds : forall p n,
      nth_error (typeof_preds p) n = option_map (@typeof_pred types) (nth_error p n).
    Proof.
      clear. unfold typeof_preds. intros. rewrite Tactics.map_nth_error_full. reflexivity.
    Qed.

    Lemma WellTyped_impures_add : forall tf tp tU tG f l m,
      SH.WellTyped_impures tf tp tU tG m = true ->
      match nth_error tp f with
        | None => false
        | Some p => allb (fun l => all2 (is_well_typed tf tU tG) l p) l
      end = true ->
      SH.WellTyped_impures tf tp tU tG (FM.add f l m) = true.
    Proof. clear.
      intros. eapply SH.WellTyped_impures_eq. intros.
      consider (nth_error tp f); try congruence; intros.
      rewrite MF.FACTS.add_o in H1. destruct (MF.FACTS.eq_dec f k); think.
      destruct v; auto.
      eapply SH.WellTyped_impures_eq in H; eauto.
    Qed.

    Lemma WellTyped_impures_mmap_add : forall tf tp tU tG f l m,
      SH.WellTyped_impures tf tp tU tG m = true ->
      match nth_error tp f with
        | None => false
        | Some p => all2 (is_well_typed tf tU tG) l p
      end = true ->
      SH.WellTyped_impures tf tp tU tG (MM.mmap_add f l m) = true.
    Proof. clear.
      intros. eapply SH.WellTyped_impures_eq. intros.
      consider (nth_error tp f); try congruence; intros.
      unfold MM.mmap_add in *. consider (FM.find (elt:=list (list expr)) f m); intros.
      rewrite MF.FACTS.add_o in H3. destruct (MF.FACTS.eq_dec f k).
      { inversion H3; clear H3; subst. rewrite H0. simpl. rewrite H2.
        eapply SH.WellTyped_impures_eq in H. 2: eauto. destruct l0; auto. rewrite H0 in *. assumption. }
      { eapply SH.WellTyped_impures_eq; eauto. }
      { rewrite MF.FACTS.add_o in H3. destruct (MF.FACTS.eq_dec f k).
        inversion H3; clear H3; subst. rewrite H0. simpl; rewrite H2; auto.
        eapply SH.WellTyped_impures_eq; eauto. }
    Qed.

    Lemma cancel_in_order_PureFacts_weak : forall tU tG bound summ,
      let tf := typeof_funcs funcs in
      let tp := SE.typeof_preds preds in
(*
      let tU := typeof_env U in
      let tG := typeof_env G in *)
      forall ls acc rem sub L R S progress,
      SUBST.Subst_WellTyped tf tU tG sub ->
      allb (fun v => SE.WellTyped_sexpr tf tp tU tG 
        (Func (snd v) (fst v))) ls = true ->
      SH.WellTyped_impures tf tp tU tG acc = true ->
      SH.WellTyped_impures tf tp tU tG rem = true ->
(*      Valid Prover_correct U G summ ->  *)
      cancel_in_order bound summ tp ls acc rem sub progress = Some (L, R, S) ->
         SUBST.Subst_Extends S sub 
      /\ SUBST.Subst_WellTyped tf tU tG S
      /\ SH.WellTyped_impures tf tp tU tG L = true 
      /\ SH.WellTyped_impures tf tp tU tG R = true.
    Proof.
      induction ls; simpl; intros.
      { destruct progress; try congruence. inversion H3; clear H3; subst; intuition. }
      { subst tp. rewrite nth_error_typeof_preds in H0. destruct a; simpl in *. 
        repeat match goal with
                 | H : context [ option_map _ ?X ] |- _ =>
                   (consider X; simpl in *; try congruence); [ intros ]
                 | [ H : match ?X with _ => _ end = _ |- _ ] =>
                   (consider X; intros; try congruence); [ intros ]
                 | [ H : match ?X with
                           | Some _ => _ | None => _ 
                         end = _ |- _ ] =>
                 consider X; intros
               end; simpl in *; subst.
        { assert (List.Forall
          (fun r : list expr =>
            all2 (is_well_typed tf tU tG) r (SDomain p) = true) l0).
          { eapply SH.WellTyped_impures_eq in H2; try eassumption.
            destruct l0. constructor. rewrite nth_error_typeof_preds in H2.
            rewrite H0 in H2. generalize dependent (e :: l0); simpl; intros.
            unfold typeof_pred in H2. clear - H2.
            induction l2; simpl in *; constructor; think; auto. }
          eapply unify_remove_PureFacts in H7.
          2: eauto. 2: eauto. 2: eauto.
          Focus 2. cutrewrite (SDomain p = t); eauto.
          unfold typeof_preds in H6.
          rewrite map_nth_error_full in H6. rewrite H0 in *.
          inversion H6. auto.
          { eapply IHls in H9; eauto. intuition.
            etransitivity. eapply H10. eapply H9.
            intuition. intuition.
            eapply SH.WellTyped_impures_eq. intros. rewrite MF.FACTS.add_o in H11.
            destruct (MF.FACTS.eq_dec f k); auto. inversion H11; clear H11; subst. 
            rewrite nth_error_typeof_preds in *. rewrite H0 in *. simpl. destruct v; intuition.
            generalize dependent (e :: v); intros.
            clear - H12. unfold typeof_pred. induction H12; simpl; auto. rewrite H. auto.
            eapply SH.WellTyped_impures_eq; eauto. } }
        { clear H6. eapply IHls in H8; eauto.
          eapply WellTyped_impures_mmap_add; auto. rewrite nth_error_typeof_preds.
          rewrite H0. simpl. auto. }
        { eapply IHls in H7; eauto.
          eapply WellTyped_impures_mmap_add; auto. rewrite nth_error_typeof_preds.
          rewrite H0. simpl. auto. }
        { eapply IHls in H6; eauto.
          eapply WellTyped_impures_mmap_add; auto. rewrite nth_error_typeof_preds.
          rewrite H0. simpl. auto. } }
    Qed.

    Lemma cancel_in_order_PureFacts : forall U G bound summ,
      let tf := typeof_funcs funcs in
      let tp := SE.typeof_preds preds in
      let tU := typeof_env U in
      let tG := typeof_env G in
      forall ls acc rem sub L R S progress,
      SUBST.Subst_WellTyped tf tU tG sub ->
      SUBST.Subst_equations funcs U G S ->
      allb (fun v => SE.WellTyped_sexpr tf tp tU tG 
        (Func (snd v) (fst v))) ls = true ->
      SH.WellTyped_impures tf tp tU tG acc = true ->
      SH.WellTyped_impures tf tp tU tG rem = true ->
      cancel_in_order bound summ tp ls acc rem sub progress = Some (L, R, S) ->
         SUBST.Subst_equations funcs U G sub 
      /\ SUBST.Subst_WellTyped (typeof_funcs funcs) (typeof_env U) (typeof_env G) S
      /\ SH.WellTyped_impures tf tp tU tG L = true 
      /\ SH.WellTyped_impures tf tp tU tG R = true.
    Proof.
      intros.
      eapply cancel_in_order_PureFacts_weak in H4; try eassumption. intuition.
      eapply SUBST.Subst_equations_Extends. 2: eassumption. eauto. 
    Qed.

    Lemma impuresD_mmap_add : forall U G f args m,
      heq funcs preds U G 
          (SH.impuresD (MM.mmap_add f args m))
          (Star (Func f args) (SH.impuresD m)).
    Proof. clear.
      intros. unfold MM.mmap_add. consider (FM.find (elt:=list exprs) f m); intros.
      { rewrite SH.impuresD_Add with (f := f) (argss := args :: l) (i := FM.remove f m).
        rewrite starred_cons. 
        rewrite SH.impuresD_Add with (f := f) (argss := l) (i := FM.remove f m) (i' := m).
        heq_canceler.
        intro. repeat (rewrite MF.FACTS.add_o || rewrite MF.FACTS.remove_o). destruct (MF.FACTS.eq_dec f y); subst; auto.
        rewrite MF.FACTS.remove_in_iff. intro. intuition; congruence.
        intro. repeat (rewrite MF.FACTS.add_o || rewrite MF.FACTS.remove_o). destruct (MF.FACTS.eq_dec f y); subst; auto.
        rewrite MF.FACTS.remove_in_iff. intro. intuition; congruence. }
      { rewrite SH.impuresD_Add with (f := f) (argss := args :: nil) (i := m).
        rewrite starred_cons. 
        heq_canceler.
        intro. repeat (rewrite MF.FACTS.add_o || rewrite MF.FACTS.remove_o). destruct (MF.FACTS.eq_dec f y); subst; auto.
        intro. destruct H0. apply MF.FACTS.find_mapsto_iff in H0; congruence. }
    Qed.

    Lemma cancel_in_order_common : forall 
      (U G : env types)
      (bound : nat) (summ : Facts Prover) (e : exprs) 
      (n : nat) (ls : list (exprs * nat)),
      (forall (acc rem : MM.mmap exprs) (sub : SUBST.Subst)
        (L R : MM.mmap exprs) (S : SUBST.Subst) progress,
        SUBST.Subst_WellTyped (typeof_funcs funcs) (typeof_env U) (typeof_env G) sub ->
        SUBST.Subst_WellTyped (typeof_funcs funcs) (typeof_env U) (typeof_env G) S ->
        SUBST.Subst_equations funcs U G S ->
        Valid Prover_correct U G summ ->
        cancel_in_order bound summ (SE.typeof_preds preds) ls acc rem sub progress = Some (L, R, S) ->
        allb
        (fun v : list expr * func =>
          match nth_error (typeof_preds preds) (snd v) with
            | Some ts =>
              all2
              (is_well_typed (typeof_funcs funcs) (typeof_env U)
                (typeof_env G)) (map (SUBST.exprInstantiate S) (fst v)) ts
            | None => false
          end) ls = true ->
        SH.WellTyped_impures (typeof_funcs funcs) (typeof_preds preds)
        (typeof_env U) (typeof_env G) acc = true ->
        SH.WellTyped_impures (typeof_funcs funcs) (typeof_preds preds)
        (typeof_env U) (typeof_env G) rem = true ->
        forall P Q,
          himp funcs preds U G
          (Star (SH.impuresD (impuresInstantiate S R)) P)
          (Star (SH.impuresD (impuresInstantiate S L)) Q) ->
          himp funcs preds U G
          (Star (SH.impuresD (impuresInstantiate S rem)) P)
          (Star
            (Star
              (SH.starred
                (fun v : list expr * func =>
                  Func (snd v) (map (SUBST.exprInstantiate S) (fst v))) ls Emp)
              (SH.impuresD (impuresInstantiate S acc))) Q)) ->
      forall (acc rem : MM.mmap exprs) (sub : SUBST.Subst)
        (L R : MM.mmap exprs) (S : SUBST.Subst) progress,
        SUBST.Subst_WellTyped (typeof_funcs funcs) (typeof_env U) (typeof_env G) sub ->
        SUBST.Subst_WellTyped (typeof_funcs funcs) (typeof_env U) (typeof_env G) S ->
        SUBST.Subst_equations funcs U G S ->
        Valid Prover_correct U G summ ->
        SH.WellTyped_impures (typeof_funcs funcs) (typeof_preds preds)
        (typeof_env U) (typeof_env G) acc = true ->
        SH.WellTyped_impures (typeof_funcs funcs) (typeof_preds preds)
        (typeof_env U) (typeof_env G) rem = true ->
        forall P Q,
          himp funcs preds U G
          (Star (SH.impuresD (impuresInstantiate S R)) P)
          (Star (SH.impuresD (impuresInstantiate S L)) Q) ->
          forall p : predicate types,
            nth_error preds n = Some p ->
            all2 (is_well_typed (typeof_funcs funcs) (typeof_env U) (typeof_env G))
            (map (SUBST.exprInstantiate S) e) (typeof_pred p) = true ->
            allb
            (fun v : list expr * func =>
              match nth_error (typeof_preds preds) (snd v) with
                | Some ts =>
                  all2
                  (is_well_typed (typeof_funcs funcs) (typeof_env U) (typeof_env G))
                  (map (SUBST.exprInstantiate S) (fst v)) ts
                | None => false
              end) ls = true ->
            cancel_in_order bound summ (SE.typeof_preds preds) ls (MM.mmap_add n e acc) rem sub progress = Some (L, R, S) ->
            himp funcs preds U G
            (Star (SH.impuresD (impuresInstantiate S rem)) P)
            (Star (Star
              (SE.Star (Func n (map (SUBST.exprInstantiate S) e))
                (SH.starred
                  (fun v : list expr * func =>
                    Func (snd v) (map (SUBST.exprInstantiate S) (fst v))) ls Emp))
              (SH.impuresD (impuresInstantiate S acc))) Q).
    Proof.
      intros. 
      assert (allb (fun v : list expr * func => WellTyped_sexpr (typeof_funcs funcs) (typeof_preds preds) 
        (typeof_env U) (typeof_env G) (Func (snd v) (fst v))) ls = true).
      { eapply allb_impl. eauto. simpl. intros. destruct (nth_error (typeof_preds preds) (snd x)); auto.
        rewrite all2_map_1 in H11. eapply all2_impl; try eassumption. intros.
        simpl in *. rewrite <- SUBST.exprInstantiate_WellTyped in H12; eauto. }
      assert (SH.WellTyped_impures (typeof_funcs funcs) (typeof_preds preds)
        (typeof_env U) (typeof_env G) (MM.mmap_add n e acc) = true).
      { eapply WellTyped_impures_mmap_add. eauto. rewrite nth_error_typeof_preds. rewrite H7. simpl.
        unfold typeof_pred. rewrite all2_map_1 in H8. eapply all2_impl. eauto. simpl.
        intros. rewrite <- SUBST.exprInstantiate_WellTyped in H12; eauto. }
      generalize H10. eapply cancel_in_order_PureFacts in H10; eauto. intro.
      eapply H in H13; eauto. intuition.
      rewrite H13.
      do 2 rewrite SEP_UFACTS.impuresD_forget_impuresInstantiate by eassumption.
      rewrite impuresD_mmap_add. rewrite Func_forget_exprInstantiate by eassumption.
      rewrite heq_star_comm with (Q := SH.starred
        (fun v : list expr * func =>
          Func (snd v) (map (SUBST.exprInstantiate S) (fst v))) ls Emp).
      repeat rewrite heq_star_assoc. reflexivity.
    Qed.

    (** cancel_in_order ls acc rem = (l,r,sub) ->
     ** r ===> l ->
     ** rem ===> ls * acc
     **)
    Lemma cancel_in_orderOk : forall U G bound summ ls acc rem sub L R S progress,
      let tf := typeof_funcs funcs in
      let tp := SE.typeof_preds preds in
      let tU := typeof_env U in
      let tG := typeof_env G in
      SUBST.Subst_WellTyped tf tU tG sub ->
      SUBST.Subst_WellTyped tf tU tG S ->
      SUBST.Subst_equations funcs U G S ->
      Valid Prover_correct U G summ ->
      cancel_in_order bound summ tp ls acc rem sub progress = Some (L, R, S) ->
      allb (fun v => SE.WellTyped_sexpr tf tp tU tG 
        (Func (snd v) (map (SUBST.exprInstantiate S) (fst v)))) ls = true ->
      SH.WellTyped_impures tf tp tU tG acc = true ->
      SH.WellTyped_impures tf tp tU tG rem = true ->
      forall P Q,
      himp funcs preds U G 
        (Star (SH.impuresD (impuresInstantiate S R)) P)
        (Star (SH.impuresD (impuresInstantiate S L)) Q) ->
      himp funcs preds U G 
        (Star (SH.impuresD (impuresInstantiate S rem)) P)
        (Star (Star (SH.starred (fun v => (Func (snd v) (map (SUBST.exprInstantiate S) (fst v)))) ls Emp)
                    (SH.impuresD (impuresInstantiate S acc))) Q).
    Proof.
      induction ls; simpl; intros.
      { destruct progress; try congruence. inversion H3; clear H3; subst. 
        repeat rewrite starred_nil. rewrite heq_star_emp_l. auto. }
      { rewrite starred_cons. rewrite nth_error_typeof_preds in H4. destruct a; simpl in *.
        repeat match goal with
                 | H : context [ option_map _ ?X ] |- _ =>
                   (consider X; simpl in *; try congruence); [ intros ]
                 | [ H : match ?X with _ => _ end = _ |- _ ] =>
                   (consider X; intros; try congruence); [ intros ]
                 | [ H : match ?X with
                           | Some _ => _ | None => _ 
                         end = _ |- _ ] =>
                 consider X; intros
               end; simpl in *; subst.
        { assert (all2 (is_well_typed (typeof_funcs funcs) (typeof_env U) (typeof_env G)) e (SDomain p) = true).
          { rewrite all2_map_1 in H8. eapply all2_impl. eapply H8. intros. simpl in *.
            rewrite <- SUBST.exprInstantiate_WellTyped in H11; eauto. }
          assert (List.Forall (fun r : list expr =>
            all2 (is_well_typed (typeof_funcs funcs) (typeof_env U) (typeof_env G)) r (SDomain p) = true) l).
          { eapply SH.WellTyped_impures_eq in H6; eauto. destruct l. constructor.
            rewrite nth_error_typeof_preds in *. rewrite H4 in H6. revert H6.
            generalize (e0 :: l). simpl. clear. induction l; simpl; intros; auto.
            consider (all2 (is_well_typed (typeof_funcs funcs) (typeof_env U) (typeof_env G)) a (typeof_pred p)); intros.
            constructor; auto. }
          assert (t = SDomain p).
          { clear - H4 H10. unfold typeof_preds, typeof_pred in *. rewrite map_nth_error_full in *.
            rewrite H4 in *. inversion H10; auto. }
          generalize H11. eapply unify_remove_PureFacts in H11. 
          5: subst t; eassumption. 2: solve [ eauto ]. 2: solve [ eauto ].
(* eauto using typeof_env_WellTyped_env, typeof_funcs_WellTyped_funcs. *)
          intuition.
          assert (allb (fun v : list expr * func =>
            WellTyped_sexpr (typeof_funcs funcs) (typeof_preds preds)
            (typeof_env U) (typeof_env G) (Func (snd v) (fst v))) ls = true).
          { eapply allb_impl. eassumption. simpl. intros.
            destruct (nth_error (typeof_preds preds) (snd x)); auto.
            rewrite all2_map_1 in H18. eapply all2_impl. eauto. simpl. intros.
            rewrite <- SUBST.exprInstantiate_WellTyped in H20; eauto. }
          assert (SH.WellTyped_impures (typeof_funcs funcs) (typeof_preds preds)
            (typeof_env U) (typeof_env G) (FM.add n l0 rem) = true).
          { eapply WellTyped_impures_add; eauto. 
            rewrite nth_error_typeof_preds in *. rewrite H4. simpl. revert H19. clear.
            unfold typeof_pred in *. induction 1; simpl; think; auto. }
          Focus 2. eapply H14.
          generalize H13. eapply cancel_in_order_PureFacts in H13; eauto.
          intuition.
          do 2 rewrite SEP_UFACTS.impuresD_forget_impuresInstantiate by eassumption.
          assert (MM.PROPS.Add n l (FM.remove (elt:=list exprs) n rem) rem).
          { red. intro. rewrite MF.FACTS.add_o. rewrite MF.FACTS.remove_o.
            destruct (MF.FACTS.eq_dec n y); subst; auto. }
          assert (~FM.In (elt:=list exprs) n (FM.remove (elt:=list exprs) n rem)).
          { rewrite MF.FACTS.remove_in_iff. intro. intuition; congruence. }
          rewrite SH.impuresD_Add with (i := FM.remove n rem) (i' := rem) (f := n) (argss := l) by eassumption.
          rewrite heq_star_assoc.          
          rewrite Func_forget_exprInstantiate by eassumption.
          subst t.
          eapply unify_removeOk in H12; [ | | | | eassumption | | | | | | ];
            eauto using typeof_env_WellTyped_env, typeof_funcs_WellTyped_funcs.
          destruct H12. repeat rewrite heq_star_assoc. rewrite <- H12. rewrite heq_star_comm. rewrite <- SH.starred_base. 
          reflexivity.
          eapply IHls in H21; eauto.
          do 2 rewrite SEP_UFACTS.impuresD_forget_impuresInstantiate in H21 by eassumption.
          rewrite heq_star_assoc in H21. rewrite <- H21.
          rewrite SH.impuresD_Add with (i := FM.remove n rem) (i' := FM.add n l0 rem) (f := n) (argss := l0).
          rewrite SH.starred_base. rewrite heq_star_comm. rewrite heq_star_assoc. reflexivity.
          { intro. repeat (rewrite MF.FACTS.add_o || rewrite MF.FACTS.remove_o). destruct (MF.FACTS.eq_dec n y); auto. }
          { rewrite MF.FACTS.remove_in_iff. intro. intuition; congruence. } }
        { eapply cancel_in_order_common in H12; eauto. }
        { eapply cancel_in_order_common in H11; eauto. } 
      { eapply cancel_in_order_common in H10; eauto. } }
    Qed.


    (** NOTE: return None if we don't make progress
     **)
    Definition sepCancel (bound : nat) (tpreds : SE.tpredicates) (summ : Facts Prover) (l r : SH.SHeap) (s : SUBST.Subst) 
      : option (SH.SHeap * SH.SHeap * SUBST.Subst) :=
      let ordered_r := O.order_impures (SH.impures r) in
      let sorted_l := FM.map (fun v => Ordering.sort _ (O.meta_order_args) v) (SH.impures l) in 
      match 
        cancel_in_order bound summ tpreds ordered_r (MM.empty _) sorted_l s false
        with
        | None => None 
        | Some (rf, lf, sub) =>
          Some ({| SH.impures := lf ; SH.pures := SH.pures l ; SH.other := SH.other l |},
                {| SH.impures := rf ; SH.pures := SH.pures r ; SH.other := SH.other r |},
                sub)
      end.

    Theorem sepCancel_PuresPrem : forall tp U G bound summ l r l' r' s s',
      sepCancel bound tp summ l r s = Some (l', r', s') ->
      AllProvable funcs U G (SH.pures l) ->
      AllProvable funcs U G (SH.pures l').
    Proof.
      unfold sepCancel. intros.
      destruct (cancel_in_order bound summ tp (O.order_impures (SH.impures r))
              (MM.empty exprs)
              (FM.map
                 (fun v : list exprs =>
                  Ordering.sort exprs (O.meta_order_args) v)
                 (SH.impures l)) s). destruct p. destruct p. inversion H.
      auto. congruence.
    Qed.

    Lemma starred_ext : forall T U G F F' (ls : list T) B,
      (forall x, heq funcs preds U G (F x) (F' x)) -> 
      heq funcs preds U G (SH.starred F ls B) (SH.starred F' ls B).
    Proof. clear.
      induction ls; intros; repeat (rewrite starred_nil || rewrite starred_cons).
      reflexivity. rewrite H. rewrite IHls; auto. reflexivity.
    Qed.

    Lemma Equiv_map : forall T (E : T -> T -> Prop) (F : T -> T) a,
      (forall x, E (F x) x) ->
      FM.Equiv E (FM.map F a) a.
    Proof. clear.
      red; intros. split; intros.
      rewrite MF.PROPS.F.map_in_iff. tauto.
      apply MF.FACTS.map_mapsto_iff in H0. destruct H0. intuition; subst.
      apply MF.FACTS.find_mapsto_iff in H1. apply MF.FACTS.find_mapsto_iff in H3. 
      rewrite H1 in H3; inversion H3; auto.
    Qed.


    Lemma WellTyped_empty : forall tf tp tU tG,
      SH.WellTyped_impures tf tp tU tG (MM.empty exprs) = true.
    Proof. clear.
      intros. rewrite SH.WellTyped_impures_spec_eq. rewrite MF.PROPS.fold_Empty; auto with typeclass_instances.
      apply FM.empty_1.
    Qed.

    

    Lemma map_sort_WellTyped : forall C tf tp tU tG imp,
      SH.WellTyped_impures tf tp tU tG imp = true ->
      SH.WellTyped_impures tf tp tU tG
      (FM.map (fun v : list exprs => Ordering.sort exprs C v) imp) = true.
    Proof. clear.
      intros. eapply SH.WellTyped_impures_eq; intros. rewrite MF.FACTS.map_o in H0.
      consider (FM.find (elt:=list exprs) k imp); simpl in *; try congruence; intros.
      inversion H1; clear H1; subst.
      eapply SH.WellTyped_impures_eq in H0. 2: eassumption.
      destruct l; auto. destruct (nth_error tp k); try contradiction.
      erewrite allb_permutation in H0. 2: symmetry; eapply Ordering.sort_permutation.
      rewrite H0. destruct (Ordering.sort exprs C (e :: l)); auto. 
    Qed.

    Theorem sepCancel_PureFacts : forall tU tG bound summ l r l' r' s s',
      let tf := typeof_funcs funcs in
      let tp := typeof_preds preds in
      sepCancel bound tp summ l r s = Some (l', r', s') ->
      SUBST.Subst_WellTyped tf tU tG s ->
      SH.WellTyped_sheap tf tp tU tG l = true ->
      SH.WellTyped_sheap tf tp tU tG r = true ->
         SUBST.Subst_WellTyped tf tU tG s' 
      /\ SH.WellTyped_sheap tf tp tU tG l' = true
      /\ SH.WellTyped_sheap tf tp tU tG r' = true
      /\ SUBST.Subst_Extends s' s.
    Proof. 
      unfold sepCancel. intros.
      consider (cancel_in_order bound summ (typeof_preds preds) (O.order_impures (SH.impures r))
              (MM.empty exprs)
              (FM.map
                 (fun v : list exprs =>
                  Ordering.sort exprs (O.meta_order_args) v)
                 (SH.impures l)) s false); intros.
      destruct p. destruct p. inversion H3; clear H3; subst.
      rewrite SH.WellTyped_sheap_eq in H1.
      rewrite SH.WellTyped_sheap_eq in H2. think.
      eapply cancel_in_order_PureFacts_weak in H; try eassumption; 
        eauto using O.order_impures_WellTyped, WellTyped_empty, map_sort_WellTyped.
      intuition.
      rewrite SH.WellTyped_sheap_eq; simpl; think; auto.
      rewrite SH.WellTyped_sheap_eq; simpl; think; auto.
      congruence.
    Qed.

    Theorem sepCancel_correct : forall U G bound summ l r l' r' sub sub',
      SUBST.Subst_WellTyped (typeof_funcs funcs) (typeof_env U) (typeof_env G) sub' ->
      SH.WellTyped_sheap (typeof_funcs funcs) (typeof_preds preds) (typeof_env U) (typeof_env G) l = true ->
      SH.WellTyped_sheap (typeof_funcs funcs) (typeof_preds preds) (typeof_env U) (typeof_env G) r = true ->
      Valid Prover_correct U G summ ->
      sepCancel bound (typeof_preds preds) summ l r sub' = Some (l', r', sub) ->
      himp funcs preds U G (SH.sheapD l') (SH.sheapD r') ->
      SUBST.Subst_equations funcs U G sub ->
      himp funcs preds U G (SH.sheapD l) (SH.sheapD r).
    Proof.
      destruct l; destruct r. unfold sepCancel. simpl. intros.
      repeat match goal with 
               | [ H : match ?X with _ => _ end = _ |- _ ] => 
                 revert H; case_eq X; intros; try congruence
               | [ H : prod _ _ |- _ ] => destruct H
               | [ H : (_,_) = (_,_) |- _ ] => inversion H; clear H; subst
               | [ H : Some _ = Some _ |- _ ] => inversion H; clear H; subst
             end.
      do 2 rewrite SH.sheapD_def. simpl. 
      eapply cancel_in_orderOk with (U := U) (G := G) 
        (P := Star (SH.starred (SE.Inj) pures SE.Emp)
                   (SH.starred (SE.Const) other SE.Emp)) 
        (Q := Star (SH.starred (SE.Inj) pures0 SE.Emp)
                   (SH.starred (SE.Const) other0 SE.Emp)) in H3;
        eauto using typeof_env_WellTyped_env, typeof_funcs_WellTyped_funcs, SUBST.Subst_empty_WellTyped.
      { clear H4.
        do 2 rewrite impuresD_forget_impuresInstantiate in H3 by eassumption. 
        rewrite SH.impuresD_Empty with (i := MM.empty _) in H3.
        rewrite starred_ext with (ls := O.order_impures impures0) in H3. 2: intro; apply Func_forget_exprInstantiate; auto.
        rewrite SH.impuresD_Equiv with (b := impures) in H3.
        rewrite H3. repeat rewrite heq_star_assoc. apply himp_star_frame.
        rewrite <- O.order_impures_D. reflexivity.
        rewrite heq_star_emp_l. reflexivity.

        red.
        symmetry. erewrite Equiv_map. reflexivity. intros. eapply Ordering.sort_permutation.
        apply FM.empty_1. }
      { eapply SUBST.Subst_equations_WellTyped; auto. }
      { rewrite SH.WellTyped_sheap_eq in H1. think. simpl in *.
        eapply O.order_impures_WellTyped in H1.
        eapply allb_impl; try eassumption. simpl; intros.
        destruct (nth_error (typeof_preds preds) (snd x)); auto.
        rewrite all2_map_1. erewrite all2_impl. 2: eauto. auto.        
        simpl; intros.
        rewrite <- SUBST.exprInstantiate_WellTyped; auto using SUBST.Subst_equations_WellTyped. }
      { apply WellTyped_empty. }
      { apply map_sort_WellTyped. rewrite SH.WellTyped_sheap_eq in H0. think. simpl in *. auto. }
      { do 2 (rewrite SH.sheapD_def in H4; simpl in H4). 
        do 2 rewrite impuresD_forget_impuresInstantiate by eassumption. eapply H4. }
    Qed.

  End env.

End Make.
