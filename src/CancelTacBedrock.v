(** This is the cancellation algorithm/interface used in Bedrock
 **)
Require Import List.
Require Import ExtLib.Tactics.Consider.
Require Import ExtLib.Core.EquivDec.
Require Import Expr SepExpr SepHeap SepCancel SepLemma.
Require Import Prover.
Require Import Tactics.
Require UnfolderTac.
Require ExprUnify.

Set Implicit Arguments.
Set Strict Implicit.

Module Make (ST : SepTheory.SepTheory)
            (SE : SepExpr ST)
            (SH : SepHeap ST SE)
            (SL : SepLemma.SepLemmaType ST SE)
            (SUBST : Instantiation.Subst)
            (UNIFY : ExprUnify.SyntacticUnifier SUBST)
            (UNF : Unfolder.Unfolder ST SE SH SL).

  Require OrderedCanceler.
  
  Module ORDER := OrderedCanceler.DefaultOrdering ST SE SH.
  Module CANCEL := OrderedCanceler.Make SUBST UNIFY ST SE SH ORDER.

  Module ST_EXT := SepTheory.SepTheory_Ext ST.
  Module SEP_FACTS := SepExpr.SepExprFacts ST SE.
  Module SH_FACTS := SepHeap.SepHeapFacts ST SE SH.
  Module UTAC := UnfolderTac.UnfolderTac ST SE SH SL UNF.
  Module SUBST_FACTS := Instantiation.SubstFacts SUBST.
  
  Require SimpleBlockInstantiation.
  Module INS := SimpleBlockInstantiation.Make SUBST.

  Lemma ex_iff : forall T (P P' : T -> Prop),
    (forall x, P x <-> P' x) ->
    ((exists x, P x) <-> (exists x, P' x)).
  Proof. split; intuition; destruct H0 as [ x ? ]; exists x; firstorder. Qed.

  Lemma AllProvable_impl_AllProvable : forall ts (funcs : functions ts) U G P ps,
    AllProvable funcs U G ps ->
    AllProvable_impl funcs U G P ps ->
    P.
  Proof. clear. induction ps; simpl; intros; eauto. intuition. Qed.    

  Section canceller.
    Variable types : list type.
    Variable tfuncs : tfunctions.
    Variable tpreds : SE.tpredicates.
    Variables hintsFwd hintsBwd : UNF.hintSide types.
    Variable prover : ProverT types.

    Record CancellerResult : Type :=
    { AllExt : variables
    ; ExExt  : variables
    ; Lhs    : SH.SHeap types
    ; Rhs    : SH.SHeap types
    ; Subst  : SUBST.Subst types
    }.

    Require Import Bool.

    Definition canceller (boundf boundb : nat) (uvars : list tvar) (hyps : Expr.exprs types)
      (lhs rhs : SE.sexpr types) : option CancellerResult :=
      let (ql, lhs) := SH.hash lhs in
      let facts := Summarize prover (map (liftExpr 0 0 0 (length ql)) hyps ++ SH.pures lhs) in
      let pre :=
        {| UNF.Vars  := rev ql
         ; UNF.UVars := uvars
         ; UNF.Heap  := lhs
        |}
      in
      match UNF.refineForward prover hintsFwd boundf facts pre with
        | ({| UNF.Vars := vars' ; UNF.UVars := uvars' ; UNF.Heap := lhs |}, n_forward) =>
          let (qr, rhs) := SH.hash rhs in
          let rhs :=
            SH_FACTS.sheapSubstU 0 (length qr) (length uvars') rhs
          in
          let post :=
            {| UNF.Vars  := vars'
             ; UNF.UVars := uvars' ++ rev qr
             ; UNF.Heap  := rhs
            |}
          in
          match UNF.refineBackward prover hintsBwd boundb facts post with
            | ({| UNF.Vars := vars' ; UNF.UVars := uvars' ; UNF.Heap := rhs |}, n_backward) =>
              let new_vars  := vars' in
              let new_uvars := skipn (length uvars) uvars' in
              let bound := length uvars' in
              match CANCEL.sepCancel prover bound tpreds facts lhs rhs (SUBST.Subst_empty _) with
                | Some (l,r,s) =>
                  Some {| AllExt := new_vars
                        ; ExExt  := new_uvars
                        ; Lhs    := 
                          (** TODO: this is a hack for the moment to ensure that
                           ** the pure premises are well typed without the new
                           ** unification variables
                           **)
                          {| SH.impures := SH.impures l
                           ; SH.pures   := SH.pures lhs
                           ; SH.other   := SH.other l
                          |}
                        ; Rhs    := r
                        ; Subst  := s
                        |}
                | None =>
                  if match ql , qr with
                       | nil , nil =>
                         match SH.pures lhs , SH.pures rhs with
                           | nil, nil => n_forward || n_backward
                           | _ , _ => false
                         end
                       | _ , _ => false 
                     end
                  then None
                  else 
                    Some {| AllExt := new_vars
                          ; ExExt  := new_uvars
                          ; Lhs    := lhs
                          ; Rhs    := rhs
                          ; Subst  := SUBST.Subst_empty _
                         |}
              end
          end
      end.

    Variable funcs : functions types.
    Variable preds : SE.predicates types.

    Lemma AllProvable_and_sem : forall U G P Ps,
      AllProvable_and funcs U G P Ps <-> (AllProvable funcs U G Ps /\ P).
    Proof. induction Ps; simpl; intros; intuition auto. Qed.
    Lemma app_inj_length : forall T (a b c d : list T),
      a ++ b = c ++ d ->
      length a = length c ->
      a = c /\ b = d.
    Proof.
      induction a; destruct c; simpl; intros; think; try solve [ intuition ].
      inversion H; subst.  eapply IHa in H3. intuition; subst; auto. omega.
    Qed.
    Lemma WellTyped_env_app : forall ts a b c d,
      WellTyped_env a c ->
      WellTyped_env b d ->
      WellTyped_env (types := ts) (a ++ b) (c ++ d).
    Proof. clear.
      intros. unfold WellTyped_env in *. unfold typeof_env in *. subst. 
      rewrite map_app. reflexivity.
    Qed.
    Ltac t_list_length := repeat (rewrite typeof_env_length || rewrite rev_length || rewrite map_length || rewrite app_length).
    Hint Extern 1 (_ = _) => t_list_length; auto : list_length.

    Ltac env_resolution :=
      repeat (rewrite typeof_env_app || unfold typeof_env || rewrite map_app || rewrite map_rev || (f_equal; []) || assumption).

    Lemma skipn_length : forall T a (b : list T),
      length (skipn a b) = length b - a.
    Proof. induction a; destruct b; simpl; intros; auto. Qed.

    Lemma himp_remove_pure_p : forall U G p P Q,
      (Provable funcs U G p ->
        SE.himp funcs preds U G P Q) ->
      SE.himp funcs preds U G (SE.Star (SE.Inj p) P) Q.
    Proof. clear.
      intros. unfold SE.himp. simpl. unfold Provable in *. 
      destruct (exprD funcs U G p tvProp); eapply ST.himp_star_pure_c; intuition.
    Qed.
    Lemma himp_remove_pures_p : forall U G ps P Q,
      (AllProvable funcs U G ps ->
        SE.himp funcs preds U G P Q) ->
      SE.himp funcs preds U G (SH.starred (@SE.Inj _) ps P) Q.
    Proof. clear.
      induction ps; intros.
      { rewrite SH_FACTS.starred_nil. apply H. exact I. }
      { rewrite SH_FACTS.starred_cons. apply himp_remove_pure_p. intros.
        eapply IHps. intro. apply H; simpl; auto. }
    Qed.
    Lemma himp_remove_pure_c : forall U G p P Q,
      Provable funcs U G p ->
      SE.himp funcs preds U G P Q ->
      SE.himp funcs preds U G P (SE.Star (SE.Inj p) Q).
    Proof. clear.
      intros. unfold SE.himp. simpl. unfold Provable in *. 
      destruct (exprD funcs U G p tvProp); eapply ST.himp_star_pure_cc; intuition.
    Qed.
    Lemma himp_remove_pures_c : forall U G ps P Q,
      AllProvable funcs U G ps ->
      SE.himp funcs preds U G P Q ->
      SE.himp funcs preds U G P (SH.starred (@SE.Inj _) ps Q).
    Proof. clear.
      induction ps; intros.
      { rewrite SH_FACTS.starred_nil. apply H0. }
      { rewrite SH_FACTS.starred_cons. simpl in *. apply himp_remove_pure_c; intuition. }
    Qed.

    Variable fwdOk : UNF.hintSideD funcs preds hintsFwd.
    Variable bwdOk : UNF.hintSideD funcs preds hintsBwd.
    Variable proverOk : ProverT_correct prover funcs.

    Hypothesis WT_funcs : WellTyped_funcs tfuncs funcs.
    Hypothesis WT_preds : tpreds = SE.typeof_preds preds.

    Theorem tfuncs_is_typeof_funcs : tfuncs = typeof_funcs funcs.
    Proof.
      clear - WT_funcs. revert WT_funcs. revert tfuncs.
      unfold WellTyped_funcs. 
      induction funcs; simpl; intros.
      { inversion WT_funcs. auto. }
      { inversion WT_funcs; clear WT_funcs; subst.
        f_equal; eauto. unfold WellTyped_sig in *.
        unfold typeof_sig.
        destruct a; destruct l; simpl in *; intuition; subst; auto. }
    Qed.

    Lemma ApplyCancelSep_with_eq (boundf boundb : nat) : 
      forall (meta_env : env types) (hyps : Expr.exprs types),
      Expr.AllProvable funcs meta_env nil hyps ->
      forall (l r : SE.sexpr types) res,
      forall (WTR : SE.WellTyped_sexpr tfuncs tpreds (typeof_env meta_env) nil r = true),
      canceller boundf boundb (typeof_env meta_env) hyps l r = Some res ->
      match res with
        | {| AllExt := new_vars
           ; ExExt  := new_uvars
           ; Lhs    := lhs'
           ; Rhs    := rhs'
           ; Subst  := subst
          |} =>
        Expr.forallEach new_vars (fun nvs : Expr.env types =>
          let var_env := nvs in
          Expr.AllProvable_impl funcs meta_env var_env
          (INS.existsSubst funcs subst meta_env var_env (length meta_env) new_uvars 
            (fun meta_ext : Expr.env types =>
              SUBST.Subst_equations_to funcs meta_env var_env subst 0 meta_env /\
              let meta_env := meta_ext in
                (Expr.AllProvable_and funcs meta_env var_env
                  (ST.himp
                    (SE.sexprD funcs preds meta_env var_env
                      (SH.sheapD (SH.Build_SHeap (SH.impures lhs') nil (SH.other lhs'))))
                    (SE.sexprD funcs preds meta_env var_env
                      (SH.sheapD (SH.Build_SHeap (SH.impures rhs') nil (SH.other rhs')))))
                  (SH.pures rhs')) ))
            (SH.pures lhs'))
      end ->
      ST.himp (@SE.sexprD _ funcs preds meta_env nil l)
              (@SE.sexprD _ funcs preds meta_env nil r).
    Proof.
      rewrite tfuncs_is_typeof_funcs in *. subst.
      intros. unfold canceller in *.
      consider (SH.hash l); intros.
      rewrite SH.hash_denote. rewrite H0; clear H0; simpl.
      consider (SH.hash r); intros.
      rewrite SH.hash_denote with (s := r). rewrite H0; simpl.
      
      rewrite SEP_FACTS.himp_existsEach_ST_EXT_existsEach.
      rewrite UNF.ST_EXT.himp_existsEach_p; [ reflexivity | intros ].
      rewrite app_nil_r.
      apply SH_FACTS.himp_pull_pures; intro.
      match goal with 
        | [ H : context [ Summarize ?P ?ps ] |- _ ] => 
          assert (Valid proverOk meta_env (rev G) (Summarize P ps)); [ | generalize dependent (Summarize P ps); intros ]
      end.
      { eapply Summarize_correct.
        apply AllProvable_app; auto.
        revert H; clear - H3. induction hyps; simpl; intros; auto.
        intuition. clear - H0 H3. unfold Provable in *.
        generalize (liftExpr_ext funcs meta_env nil nil nil (rev G) nil a tvProp); simpl.
        rewrite app_nil_r. rewrite rev_length. subst. rewrite map_length.
        intro. rewrite H in *. auto. }
      match goal with
        | [ H : match ?X with _ => _ end = _ |- _ ] => consider X
      end; intros.
      apply SEP_FACTS.himp_WellTyped_sexpr; intro.

    (** Forward **)
      destruct (UNF.refineForward_Length H2).
      assert (SH.WellTyped_sheap (typeof_funcs funcs) (SE.typeof_preds preds) (typeof_env meta_env) (rev v) s = true).
      { rewrite SH.WellTyped_sheap_WellTyped_sexpr. rewrite <- H3. rewrite <- map_rev. apply H7. }

      generalize (@UNF.refineForward_WellTyped _ _ _ _ _ _ _ _ _ _ fwdOk proverOk H2 H9); intro.
      simpl in *.
      assert (WellTyped_env (rev v) (rev G)).
      { unfold WellTyped_env. subst. rewrite <- map_rev. auto. }
      eapply UNF.refineForward_Ok in H2; simpl; eauto using typeof_env_WellTyped_env.
      simpl in H2. etransitivity; [ eapply H2 | clear H11; simpl in * ].
      rewrite UNF.ST_EXT.himp_existsEach_p; [ reflexivity | intros ].
      destruct H8.
    (** NOTE: I can't shift s0 around until I can witness the existential **)
      
    (** Open up everything **)
      destruct u. 
      consider (UNF.refineBackward prover hintsBwd boundb f
        {| UNF.Vars := Vars
          ; UNF.UVars := UVars ++ rev v0
          ; UNF.Heap := SH_FACTS.sheapSubstU 0 (length v0) (length UVars) s0 |}); intros.
      destruct (UNF.refineBackward_Length H6); simpl in *.
      destruct u.

      assert (AllExt res = Vars0 /\ ExExt res = skipn (length (typeof_env meta_env)) UVars0
        /\ SH.pures (Lhs res) = SH.pures Heap).
      { clear - H13. 
        match goal with
          | [ H : match ?X with _ => _ end = _ |- _ ] => destruct X
        end; intros. destruct p; destruct p. inversion H13; auto.
        match goal with
          | [ H : match ?X with _ => _ end = _ |- _ ] => destruct X
        end; try congruence. inversion H13; auto. }
        intuition; subst.

        rewrite ListFacts.rw_skipn_app in H11 by (auto with list_length).

        destruct res. simpl in *. subst AllExt0; subst ExExt0.
        eapply forallEach_sem with (env := rev G ++ G0) in H1; [ | solve [ env_resolution ] ]. 

        eapply (@SH_FACTS.himp_pull_pures types funcs preds meta_env (rev G ++ G0) Heap). intro.
        eapply AllProvable_impl_AllProvable in H1; [ clear H3 | rewrite H19; assumption ].

        apply INS.existsSubst_sem in H1. apply existsEach_sem in H1.
        destruct H1. intuition.

        assert (
          typeof_env (skipn (length (rev v0)) x1) = x0 /\ 
          typeof_env (firstn (length (rev v0)) x1) = rev v0).
        { subst. clear - H3.
          generalize (typeof_env_length x1). rewrite H3; intros. 
          repeat (rewrite map_app in *  || rewrite map_map in * || rewrite map_id in * || rewrite app_ass in *
            || rewrite ListFacts.rw_skipn_app in * by eauto || rewrite typeof_env_app in * ).
          simpl in *. 
          rewrite <- firstn_skipn with (n := length (rev v0)) (l := x1) in H3.
          rewrite typeof_env_app in *. 
          eapply app_inj_length in H3. destruct H3. intuition.
          revert H. t_list_length. intro. rewrite firstn_length; rewrite min_l; auto.
          omega. }
        intuition. clear H3.

        eapply AllProvable_and_sem in H14. destruct H14.

        subst UVars0.

        assert (SH.WellTyped_sheap (typeof_funcs funcs) (SE.typeof_preds preds)
          (typeof_env meta_env ++ rev v0)
          (rev (map (projT1 (P:=tvarD types)) G) ++ x)
          (SH_FACTS.sheapSubstU 0 (length v0) (length (typeof_env meta_env))
            s0) = true).
        { rewrite <- SH.WellTyped_sheap_WellTyped_sexpr in H7.
          generalize (@SH_FACTS.sheapSubstU_WellTyped types (typeof_funcs funcs) (SE.typeof_preds preds) (typeof_env meta_env) nil (rev v0) nil s0); simpl.   
          rewrite app_nil_r. intro XX.
          rewrite SH.WellTyped_hash in WTR. rewrite H0 in WTR. simpl in WTR. rewrite app_nil_r in WTR.
          apply XX in WTR. clear XX.
          eapply SH.WellTyped_sheap_weaken with (tU' := nil) (tG := nil) (tG' := (rev (map (projT1 (P:=tvarD types)) G) ++ x)) in WTR. 
          simpl in WTR. rewrite app_nil_r in WTR.  
          rewrite Plus.plus_0_r in *. rewrite rev_length in WTR. apply WTR. }

        generalize (@UNF.refineBackward_WellTyped _ _ _ _ _ _ _ _ _ _ bwdOk proverOk H6 H14); simpl.
        eapply UNF.refineBackward_Ok in H6; simpl in *.
        2: eassumption.
        2: eassumption.
        2: solve [ rewrite <- H16; eapply WellTyped_env_app; eauto using typeof_env_WellTyped_env ].
        Focus 2.
        rewrite <- map_rev.
        eapply WellTyped_env_app. eapply typeof_env_WellTyped_env.
        instantiate (1 := G0). symmetry. apply H11. 
        2: eassumption.
        2: solve [ eapply Valid_weaken; eassumption ].
        intro.

    (** **)
        rewrite SEP_FACTS.himp_existsEach_ST_EXT_existsEach.
        eapply ST_EXT.himp_existsEach_c. exists (rev (firstn (length (rev v0)) x1)); split.
        { rewrite map_rev. unfold typeof_env in H16. rewrite H16. apply rev_involutive. }
        rewrite rev_involutive.
        
    (** In order to call the canceller, they must have the same environments. **)
        assert (ST.heq 
          (SE.sexprD funcs preds meta_env (rev G ++ G0) (SH.sheapD Heap))
          (SE.sexprD funcs preds (meta_env ++ x1) (rev G ++ G0) (SH.sheapD Heap))).
        { (* rewrite <- firstn_skipn with (l := x1) (n := length meta_env).
          rewrite <- H15. *)
          generalize (@SEP_FACTS.sexprD_weaken_wt types funcs preds meta_env x1 nil 
            (SH.sheapD Heap) (rev G ++ G0)).
          rewrite app_nil_r. intro XX; apply XX; clear XX.
          rewrite <- SH.WellTyped_sheap_WellTyped_sexpr. rewrite <- H10. f_equal.
          rewrite typeof_env_app. f_equal. rewrite <- map_rev. reflexivity.
          rewrite <- H11. reflexivity. }
        rewrite H18; clear H18.

        assert (ST.heq
          (SE.sexprD funcs preds (meta_env ++ firstn (length (rev v0)) x1) (rev G ++ G0) (SH.sheapD (SH_FACTS.sheapSubstU 0 (length v0)
            (length (typeof_env meta_env)) s0)))
          (SE.sexprD funcs preds meta_env
            (firstn (length (rev v0)) x1 ++ nil)
            (SH.sheapD s0))).
        { generalize (@SH_FACTS.sheapSubstU_sheapD types funcs preds
          meta_env nil (firstn (length (rev v0)) x1) nil s0).
          simpl. repeat rewrite app_nil_r. intros XX; rewrite XX; clear XX.
          generalize (@SEP_FACTS.sexprD_weaken_wt types funcs preds 
            (meta_env ++ firstn (length (rev v0)) x1)
            nil (rev G ++ G0)
            (SH.sheapD (SH_FACTS.sheapSubstU 0
              (length (firstn (length (rev v0)) x1) +
                0) (length meta_env) s0)) nil).
          simpl. t_list_length.
          intro XX; rewrite XX; clear XX.
          rewrite app_ass; rewrite app_nil_r.
          cutrewrite (length (firstn (length v0) x1) + 0 = length v0).
          reflexivity.
          rewrite Plus.plus_0_r. rewrite <- rev_length with (l := v0). 
          rewrite <- H16 at 2. t_list_length. reflexivity.
          rewrite <- SH.WellTyped_sheap_WellTyped_sexpr.
          rewrite SH.WellTyped_hash in WTR.
          rewrite SH.WellTyped_sheap_WellTyped_sexpr in WTR. rewrite H0 in *. simpl in WTR.
          rewrite <- SH.WellTyped_sheap_WellTyped_sexpr in WTR.
          generalize (@SH_FACTS.sheapSubstU_WellTyped_eq types (typeof_funcs funcs) (SE.typeof_preds preds)
            (typeof_env meta_env) nil (rev v0) nil s0). simpl. t_list_length. rewrite app_nil_r in *.
          intro XX; rewrite XX in WTR; clear XX.
          rewrite <- WTR. rewrite <- H16. t_list_length. rewrite typeof_env_app. repeat rewrite Plus.plus_0_r.
          f_equal. f_equal. rewrite <- rev_length with (l := v0). rewrite <- H16 at 2.
          t_list_length. reflexivity. }
        rewrite <- H18; clear H18.
        revert H6. t_list_length.
        intro H6. etransitivity; [ clear H6 | eapply H6 ].


    (** witness the conclusion **)
        eapply UNF.ST_EXT.himp_existsEach_c. 
        exists (skipn (length (rev v0)) x1). split. 
        { t_list_length. rewrite ListFacts.rw_skipn_app.
          rewrite <- H15. t_list_length. reflexivity.
          t_list_length. f_equal. rewrite <- (rev_length v0).
          etransitivity. 
          rewrite <- H16. reflexivity. unfold typeof_env; t_list_length. reflexivity. }
        rewrite app_ass. 
        t_list_length. repeat rewrite firstn_skipn.
        clear H2. 

        assert (SUBST.Subst_WellTyped (typeof_funcs funcs) (typeof_env meta_env ++ typeof_env x1)
          (typeof_env (rev G ++ G0)) (SUBST.Subst_empty types)).
        { eapply SUBST.Subst_empty_WellTyped. }
        assert (SH.WellTyped_sheap (typeof_funcs funcs) (SE.typeof_preds preds)
          (typeof_env meta_env ++ typeof_env x1) (typeof_env (rev G ++ G0)) Heap0 = true).
        { rewrite <- H17. f_equal.
          rewrite app_ass. f_equal. rewrite <- (@firstn_skipn _ (length (rev v0)) x1).
          rewrite typeof_env_app. f_equal; auto. 
          rewrite typeof_env_app. f_equal. rewrite typeof_env_rev. reflexivity. apply H11. }
        assert (SH.WellTyped_sheap (typeof_funcs funcs) (SE.typeof_preds preds)
          (typeof_env meta_env ++ typeof_env x1) (typeof_env (rev G ++ G0)) Heap = true).
        { eapply SH.WellTyped_sheap_weaken with (tG' := nil) (tU' := typeof_env x1) in H10. 
          clear - H15 H10 H11.
          rewrite <- H10. f_equal. rewrite typeof_env_app. rewrite app_nil_r.
          f_equal. rewrite typeof_env_rev. reflexivity. apply H11. }
        rewrite app_ass in H13.
        consider (CANCEL.sepCancel prover (length (typeof_env meta_env ++ rev v0 ++ x0)) (SE.typeof_preds preds) f Heap Heap0 (SUBST.Subst_empty _));
        intros; try congruence.
        { destruct p. destruct p. inversion H20; clear H20. subst s3. subst s1.
          subst Lhs0. clear H19. simpl in *.
          repeat rewrite <- typeof_env_app in *.
          eapply CANCEL.sepCancel_correct with (funcs := funcs) (U := meta_env ++ x1) (G := rev G ++ G0) in H13; try eassumption.
          { instantiate (1 := proverOk). 
            eapply Valid_weaken with (ue := x1) (ge := G0) in H5. assumption. }
          { match type of H12 with
              | ST.himp (SE.sexprD ?F ?P ?U ?G ?L) (SE.sexprD ?F ?P ?U ?G ?R) =>
                change (SE.himp F P U G L R) in H12
            end. 
            do 2 rewrite SH.sheapD_def. do 2 rewrite SH.sheapD_def in H12. simpl in *.
            rewrite SH_FACTS.starred_nil in H12.
            do 2 rewrite SEP_FACTS.heq_star_emp_l in H12.
            rewrite SEP_FACTS.heq_star_comm 
              with (P := SH.starred (@SE.Inj _) (SH.pures s2) SE.Emp).
            rewrite SEP_FACTS.heq_star_comm 
              with (P := SH.starred (@SE.Inj _) (SH.pures Rhs0) SE.Emp).
            do 2 rewrite <- SEP_FACTS.heq_star_assoc.
            apply SEP_FACTS.himp_star_frame. assumption.
            eapply himp_remove_pures_p; intros.
            eapply himp_remove_pures_c; auto. reflexivity. } 
          { eapply CANCEL.sepCancel_PureFacts in H13. 4: eapply H6. 
            eapply SUBST.Subst_equations_to_Subst_equations; intuition.
            rewrite SUBST_FACTS.Subst_equations_to_app. intuition. clear - H8.            
            eapply SUBST_FACTS.Subst_equations_to_weaken with (m' := x1) (v' := nil) in H8.
            rewrite app_nil_r in *. auto.
            intuition. intuition. } }
        { match goal with
          | [ H : (if ?X then _ else _) = _ |- _ ] =>
            destruct X; try congruence
          end.
          inversion H20; clear H20.
          destruct Lhs0; destruct Rhs0; simpl in *.
          clear - H12 H3.
          etransitivity. etransitivity; [ | eapply H12 ].
          { do 2 rewrite SH.sheapD_def. simpl. repeat apply ST.himp_star_frame; try reflexivity.
            rewrite SH_FACTS.starred_nil.
            clear. eapply CANCEL.HEAP_FACTS.himp_remove_pures_p. reflexivity. }
          { do 2 rewrite SH.sheapD_def; simpl.
            repeat (eapply ST.himp_star_frame; try reflexivity).
            eapply CANCEL.HEAP_FACTS.himp_remove_pures_c; auto.
            rewrite SH_FACTS.starred_nil. reflexivity. } }
    Qed.

  End canceller.

End Make.
