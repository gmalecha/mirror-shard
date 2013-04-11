(** This is the cancellation algorithm/interface used in Bedrock
 **)
Require Import List.
Require Import Expr SepExpr SepHeap SepCancel SepLemma.
Require Import Prover.
Require Import Tactics Reflection.
Require UnfolderTac.
Require ExprUnify.

Set Implicit Arguments.
Set Strict Implicit.

Module Make (ST : SepTheory.SepTheory)
            (SE : SepExpr ST)
            (SH : SepHeap ST SE)
            (SL : SepLemma.SepLemmaType ST SE)
            (UNIFY : ExprUnify.Unifier)
            (UNF : Unfolder.Unfolder ST SE SH SL).

  Module CANCEL := SepCancel.Make UNIFY ST SE SH.

  Module ST_EXT := SepTheory.SepTheory_Ext ST.
  Module SEP_FACTS := SepExpr.SepExprFacts ST SE.
  Module SH_FACTS := SepHeap.SepHeapFacts ST SE SH.
  Module UTAC := UnfolderTac.UnfolderTac ST SE SH SL UNF.


  Section existsSubst.
    Variable types : list type.
    Variable funcs : functions types.
    Variable meta_base : env types.
    Variable var_env : env types.
    Variable sub : UNIFY.Subst types.
    
    Definition ExistsSubstNone (_ : tvar) (_ : expr types) := 
      False.

    Fixpoint substInEnv (from : nat) (vals : env types) (ret : env types -> Prop) : Prop :=
      match vals with 
        | nil => ret nil
        | val :: vals =>
          match UNIFY.Subst_lookup from sub with
            | None => substInEnv (S from) vals (fun e => ret (val :: e))
            | Some v => 
              match exprD funcs meta_base var_env v (projT1 val) with
                | None => ExistsSubstNone (projT1 val) v
                | Some v' => projT2 val = v' /\ substInEnv (S from) vals (fun e => ret (existT _ (projT1 val) v' :: e))
              end
          end
      end.

    Fixpoint existsMaybe (vals : list { t : tvar & option (tvarD types t) }) (ret : env types -> Prop) : Prop :=
      match vals with
        | nil => ret nil
        | existT t None :: vals => exists x : tvarD types t, existsMaybe vals (fun e => ret (existT _ t x :: e))
        | existT t (Some v) :: vals => existsMaybe vals (fun e => ret (existT _ t v :: e))
      end.

  End existsSubst.

  Definition existsSubst types funcs var_env sub (from : nat) (vals : list { t : tvar & option (tvarD types t) }) (ret : env types -> Prop) :=
    existsMaybe vals (fun e => @substInEnv types funcs e var_env sub from e ret).

  Fixpoint consistent {ts} (vals : list { x : tvar & option (tvarD ts x) }) (e : list { x : tvar & tvarD ts x }) : Prop :=
    match vals , e with
      | nil , nil => True
      | existT t None :: vals , existT t' _ :: e =>
        t = t' /\ @consistent _ vals e
      | existT t (Some v) :: vals , existT t' v' :: e =>
        match equiv_dec t t' return Prop with
          | left pf => 
            v' = match (pf : t = t') in _ = t return tvarD ts t with
                   | refl_equal => v
                 end /\ @consistent _ vals e
          | right _ => False
        end
      | _ , _ => False
    end.

  Lemma ex_iff : forall T (P P' : T -> Prop),
    (forall x, P x <-> P' x) ->
    ((exists x, P x) <-> (exists x, P' x)).
  Proof. split; intuition; destruct H0 as [ x ? ]; exists x; firstorder. Qed.

  Theorem existsMaybe_sem : forall types vals (ret : env types -> Prop),
    existsMaybe vals ret <->
    existsEach (map (@projT1 _ _) vals) (fun e => consistent vals e /\ ret e).
  Proof.
    induction vals; simpl; intros.
    { intuition. }
    { destruct a. destruct o.
      { rewrite IHvals. intuition. exists t. apply existsEach_sem. apply existsEach_sem in H.
        destruct H. exists x0. simpl in *. rewrite EquivDec_refl_left. intuition.
        destruct H. apply existsEach_sem. apply existsEach_sem in H. destruct H.
        exists x1. simpl in *. rewrite EquivDec_refl_left in H. intuition; subst; auto. }
      { simpl. eapply ex_iff. intros. rewrite IHvals.
        intuition; apply existsEach_sem in H; apply existsEach_sem; destruct H; exists x1; intuition. } }
  Qed.

  Lemma substInEnv_sem : forall types funcs meta_env var_env sub vals from ret,
    @substInEnv types funcs meta_env var_env sub from vals ret <-> 
    (UNIFY.Subst_equations_to funcs meta_env var_env sub from vals /\ ret vals).
  Proof.
    induction vals; simpl; intros.
    { intuition. }
    { destruct a; simpl in *.
      consider (UNIFY.Subst_lookup from sub); simpl; intros.
      consider (exprD funcs meta_env var_env e x); simpl; intros.
      { rewrite IHvals. intuition; subst; auto. } 
      { intuition. }
      { rewrite IHvals. intuition. } }
  Qed.

  Lemma existsSubst_sem : forall ts (funcs : functions ts) vals sub vars_env from ret,
    existsSubst funcs vars_env sub from vals ret <->
    existsEach (map (@projT1 _ _) vals) (fun meta_env =>
      consistent vals meta_env /\ UNIFY.Subst_equations_to funcs meta_env vars_env sub from meta_env /\ ret meta_env).
  Proof.
    intros. unfold existsSubst.
    rewrite existsMaybe_sem. rewrite existsEach_sem. rewrite existsEach_sem.
    apply ex_iff. intros. rewrite substInEnv_sem. intuition.
  Qed.

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
    ; Subst  : UNIFY.Subst types
    }.

    Require Import Bool.

    Definition canceller (uvars : list tvar) (hyps : Expr.exprs types)
      (lhs rhs : SE.sexpr types) : option CancellerResult :=
      let (ql, lhs) := SH.hash lhs in
      let facts := Summarize prover (map (liftExpr 0 0 0 (length ql)) hyps ++ SH.pures lhs) in
      let pre :=
        {| UNF.Vars  := rev ql
         ; UNF.UVars := uvars
         ; UNF.Heap  := lhs
        |}
      in
      match UNF.refineForward prover hintsFwd 10 facts pre with
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
          match UNF.refineBackward prover hintsBwd 10 facts post with
            | ({| UNF.Vars := vars' ; UNF.UVars := uvars' ; UNF.Heap := rhs |}, n_backward) =>
              let new_vars  := vars' in
              let new_uvars := skipn (length uvars) uvars' in
              let bound := length uvars' in
              match CANCEL.sepCancel prover bound tpreds facts lhs rhs (UNIFY.Subst_empty _) with
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
                          ; Subst  := UNIFY.Subst_empty _
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

    Lemma consistent_app : forall ts a b c,
      consistent (ts := ts) (a ++ b) c ->
      consistent a (firstn (length a) c) /\ consistent b (skipn (length a) c).
    Proof. clear.
      induction a; simpl; intros; auto.
      destruct a. destruct o. destruct c; try contradiction. destruct s. destruct (equiv_dec x x0); try contradiction.
      destruct H. eapply IHa in H0. intuition.
      destruct c; try contradiction. destruct s. destruct H. apply IHa in H0. intuition.
    Qed.
    Lemma consistent_Some : forall ts a c,
      consistent (ts := ts) (map (fun x => existT _ (projT1 x) (Some (projT2 x))) a) c ->
      a = c.
    Proof.
      induction a; destruct c; simpl; intros; try contradiction; auto.
      destruct s. destruct a; simpl in *. destruct (equiv_dec x0 x); try contradiction.
      unfold equiv in e. intuition; subst. f_equal; eauto.
    Qed.
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

    Lemma ApplyCancelSep_with_eq : 
      forall (meta_env : env types) (hyps : Expr.exprs types),
      Expr.AllProvable funcs meta_env nil hyps ->
      forall (l r : SE.sexpr types) res,
      forall (WTR : SE.WellTyped_sexpr tfuncs tpreds (typeof_env meta_env) nil r = true),
      canceller (typeof_env meta_env) hyps l r = Some res ->
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
          (existsSubst funcs var_env subst 0 
            (map (fun x => existT (fun t => option (tvarD types t)) (projT1 x) (Some (projT2 x))) meta_env ++
             map (fun x => existT (fun t => option (tvarD types t)) x None) new_uvars)
            (fun meta_env : Expr.env types =>
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
      consider (UNF.refineBackward prover hintsBwd 10 f
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

        apply existsSubst_sem in H1. apply existsEach_sem in H1.
        destruct H1. intuition.
        assert (meta_env = firstn (length meta_env) x1 /\
          typeof_env (skipn (length (rev v0)) (skipn (length meta_env) x1)) = x0 /\ 
          typeof_env (firstn (length (rev v0)) (skipn (length meta_env) x1)) = rev v0).
        { subst. clear - H3 H1.
          generalize (typeof_env_length x1). rewrite H3; intros.
          rewrite <- firstn_skipn with (n := length meta_env) (l := x1) in H3.
          repeat (rewrite map_app in *  || rewrite map_map in * || rewrite map_id in * || rewrite app_ass in *
            || rewrite ListFacts.rw_skipn_app in * by eauto || rewrite typeof_env_app in * ).
          simpl in *. rewrite typeof_env_app in *. eapply app_inj_length in H3.
          Focus 2. revert H. t_list_length. rewrite firstn_length. intro. rewrite min_l; omega.
          destruct H3.
          rewrite <- firstn_skipn with (n := length (rev v0)) (l := skipn (length meta_env) x1) in H2.
          rewrite typeof_env_app in *. 
          eapply app_inj_length in H2. destruct H2. intuition.
          { eapply consistent_app in H1. destruct H1; clear - H1.
            revert H1. t_list_length. intros.
            eapply consistent_Some in H1. auto. }
          revert H. t_list_length. intro. rewrite firstn_length; rewrite min_l; auto.
          rewrite skipn_length. omega. }
        intuition. clear H3 H1.

        eapply AllProvable_and_sem in H14. destruct H14.
        rewrite app_ass in *.

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
        2: solve [ rewrite <- H18; eapply WellTyped_env_app; eauto using typeof_env_WellTyped_env ].
        Focus 2.
        rewrite <- map_rev.
        eapply WellTyped_env_app. eapply typeof_env_WellTyped_env.
        instantiate (1 := G0). symmetry. apply H11. 
        2: eassumption.
        2: solve [ eapply Valid_weaken; eassumption ].
        intro.

    (** **)
        rewrite SEP_FACTS.himp_existsEach_ST_EXT_existsEach.
        eapply ST_EXT.himp_existsEach_c. exists (rev (firstn (length (rev v0)) (skipn (length meta_env) x1))); split.
        { rewrite map_rev. unfold typeof_env in H18. rewrite H18. apply rev_involutive. }
        rewrite rev_involutive.
        
    (** In order to call the canceller, they must have the same environments. **)
        assert (ST.heq 
          (SE.sexprD funcs preds meta_env (rev G ++ G0) (SH.sheapD Heap))
          (SE.sexprD funcs preds x1 (rev G ++ G0) (SH.sheapD Heap))).
        { rewrite <- firstn_skipn with (l := x1) (n := length meta_env).
          rewrite <- H15.
          generalize (@SEP_FACTS.sexprD_weaken_wt types funcs preds meta_env (skipn (length meta_env) x1) nil 
            (SH.sheapD Heap) (rev G ++ G0)).
          rewrite app_nil_r. intro XX; apply XX; clear XX.
          rewrite <- SH.WellTyped_sheap_WellTyped_sexpr. rewrite <- H10. f_equal.
          rewrite typeof_env_app. f_equal. rewrite <- map_rev. reflexivity.
          rewrite <- H11. reflexivity. }
        rewrite H17; clear H17.

        assert (ST.heq
          (SE.sexprD funcs preds (meta_env ++ firstn (length (rev v0)) (skipn (length meta_env) x1)) (rev G ++ G0) (SH.sheapD (SH_FACTS.sheapSubstU 0 (length v0)
            (length (typeof_env meta_env)) s0)))
          (SE.sexprD funcs preds meta_env
            (firstn (length (rev v0)) (skipn (length meta_env) x1) ++ nil)
            (SH.sheapD s0))).
        { generalize (@SH_FACTS.sheapSubstU_sheapD types funcs preds
          meta_env nil (firstn (length (rev v0)) (skipn (length meta_env) x1)) nil s0).
          simpl. repeat rewrite app_nil_r. intros XX; rewrite XX; clear XX.
          generalize (@SEP_FACTS.sexprD_weaken_wt types funcs preds 
            (meta_env ++ firstn (length (rev v0)) (skipn (length meta_env) x1))
            nil (rev G ++ G0)
            (SH.sheapD (SH_FACTS.sheapSubstU 0
              (length (firstn (length (rev v0)) (skipn (length meta_env) x1)) +
                0) (length meta_env) s0)) nil).
          simpl. t_list_length.
          intro XX; rewrite XX; clear XX.
          rewrite H15. rewrite app_ass. 
          cutrewrite (length (firstn (length meta_env) x1) = length meta_env).
          rewrite app_nil_r.
          cutrewrite (length (firstn (length v0) (skipn (length meta_env) x1)) + 0 = length v0).
          reflexivity.
          rewrite Plus.plus_0_r. rewrite <- rev_length with (l := v0). 
          rewrite <- H18 at 2. t_list_length. reflexivity.
          rewrite <- H15. reflexivity.
          rewrite <- SH.WellTyped_sheap_WellTyped_sexpr.
          rewrite SH.WellTyped_hash in WTR.
          rewrite SH.WellTyped_sheap_WellTyped_sexpr in WTR. rewrite H0 in *. simpl in WTR.
          clear - WTR H15 H12 H18 H11.
          rewrite <- SH.WellTyped_sheap_WellTyped_sexpr in WTR.
          generalize (@SH_FACTS.sheapSubstU_WellTyped_eq types (typeof_funcs funcs) (SE.typeof_preds preds)
            (typeof_env meta_env) nil (rev v0) nil s0). simpl. t_list_length. rewrite app_nil_r in *.
          intro XX; rewrite XX in WTR; clear XX.
          rewrite <- WTR. rewrite <- H18. t_list_length. rewrite typeof_env_app. repeat rewrite Plus.plus_0_r.
          f_equal. f_equal. rewrite <- rev_length with (l := v0). rewrite <- H18 at 2.
          t_list_length. reflexivity. }
        rewrite <- H17; clear H17.
        revert H6. t_list_length.
        intro H6. etransitivity; [ clear H6 | eapply H6 ].


    (** witness the conclusion **)
        eapply UNF.ST_EXT.himp_existsEach_c. 
        exists (skipn (length (rev v0)) (skipn (length meta_env) x1)). split. 
        { t_list_length. rewrite firstn_length; rewrite skipn_length. rewrite <- app_ass. rewrite ListFacts.rw_skipn_app.
          rewrite <- H12. t_list_length. reflexivity.
          env_resolution. t_list_length. f_equal. rewrite min_l; auto.
          clear - H18 H15 H12.
          assert (x1 = firstn (length meta_env) x1 ++ (firstn (length (rev v0)) (skipn (length meta_env) x1)) ++ 
            (skipn (length (rev v0)) (skipn (length meta_env) x1))).
          repeat rewrite firstn_skipn. reflexivity. 
          generalize dependent (firstn (length meta_env) x1).
          generalize dependent (skipn (length (rev v0)) (skipn (length meta_env) x1)).
          generalize dependent (firstn (length (rev v0)) (skipn (length meta_env) x1)).
          intros. subst. rewrite <- rev_length. rewrite <- H18. t_list_length. omega. }
        rewrite app_ass. rewrite H15 at 1.
        t_list_length. repeat rewrite firstn_skipn.
        clear H2. 

        assert (UNIFY.Subst_WellTyped (typeof_funcs funcs) (typeof_env x1)
          (typeof_env (rev G ++ G0)) (UNIFY.Subst_empty types)).
        { eapply UNIFY.Subst_empty_WellTyped. }
        assert (SH.WellTyped_sheap (typeof_funcs funcs) (SE.typeof_preds preds)
          (typeof_env x1) (typeof_env (rev G ++ G0)) Heap0 = true).
        { rewrite <- H16. f_equal.
          rewrite H15. rewrite <- H18. rewrite <- H12. t_list_length. 
          repeat rewrite <- typeof_env_app. repeat rewrite firstn_skipn. reflexivity.
          rewrite typeof_env_app. f_equal. rewrite typeof_env_rev. reflexivity. apply H11. }
        assert (SH.WellTyped_sheap (typeof_funcs funcs) (SE.typeof_preds preds)
          (typeof_env x1) (typeof_env (rev G ++ G0)) Heap = true).
        { eapply SH.WellTyped_sheap_weaken with (tG' := nil) (tU' := typeof_env (skipn (length meta_env) x1)) in H10.
          rewrite H15 in H10 at 1. rewrite <- typeof_env_app in H10. rewrite firstn_skipn in H10.
          rewrite app_nil_r in H10. rewrite <- H10. f_equal.
          rewrite typeof_env_app. rewrite typeof_env_rev. f_equal. apply H11. }
        consider (CANCEL.sepCancel prover (length (typeof_env meta_env ++ rev v0 ++ x0)) (SE.typeof_preds preds) f Heap Heap0 (UNIFY.Subst_empty _));
        intros; try congruence.
        { destruct p. destruct p. inversion H20; clear H20. subst s3. subst s1.
          subst Lhs0. clear H19. simpl in *.
          eapply CANCEL.sepCancel_correct with (funcs := funcs) (U := x1) (G := rev G ++ G0) in H13; try eassumption.
          { instantiate (1 := proverOk). eapply Valid_weaken with (ue := skipn (length meta_env) x1) (ge := G0) in H5.
            rewrite <- firstn_skipn with (n := length meta_env) (l := x1). rewrite <- H15. assumption. }
          { (* eapply CANCEL.sepCancel_PuresPrem in H13; try eassumption. *)
            match type of H3 with
              | ST.himp (SE.sexprD ?F ?P ?U ?G ?L) (SE.sexprD ?F ?P ?U ?G ?R) =>
                change (SE.himp F P U G L R) in H3
            end. 
            do 2 rewrite SH.sheapD_def. do 2 rewrite SH.sheapD_def in H3. simpl in *.
            rewrite SH_FACTS.starred_nil in H3.
            do 2 rewrite SEP_FACTS.heq_star_emp_l in H3.
            rewrite SEP_FACTS.heq_star_comm 
              with (P := SH.starred (@SE.Inj _) (SH.pures s2) SE.Emp).
            rewrite SEP_FACTS.heq_star_comm 
              with (P := SH.starred (@SE.Inj _) (SH.pures Rhs0) SE.Emp).
            do 2 rewrite <- SEP_FACTS.heq_star_assoc.
            apply SEP_FACTS.himp_star_frame. assumption.
            eapply himp_remove_pures_p; intros.
            eapply himp_remove_pures_c; auto. reflexivity. } 
          { eapply CANCEL.sepCancel_PureFacts in H13. 4: eapply H6. 
            eapply UNIFY.Subst_equations_to_Subst_equations; intuition.
            intuition. intuition. } }
        { match goal with
          | [ H : (if ?X then _ else _) = _ |- _ ] =>
            destruct X; try congruence
          end.
          inversion H20; clear H20.
          destruct Lhs0; destruct Rhs0; simpl in *.
          etransitivity. etransitivity; [ | eapply H3 ].
          { do 2 rewrite SH.sheapD_def. simpl. repeat apply ST.himp_star_frame; try reflexivity.
            rewrite SH_FACTS.starred_nil.
            clear. induction pures. 
            { rewrite SH_FACTS.starred_nil. reflexivity. }
            { rewrite SH_FACTS.starred_cons.
              destruct (exprD funcs x1 (rev G ++ G0) a tvProp);
                eapply himp_remove_pure_p; unfold SE.himp; simpl; intros; auto. } }
              { repeat rewrite SH.sheapD_def; simpl; repeat apply ST.himp_star_frame; try reflexivity.
                rewrite SH_FACTS.starred_nil.
                clear - H1. induction pures0. 
                { rewrite SH_FACTS.starred_nil. reflexivity. }
                { rewrite SH_FACTS.starred_cons.
                  simpl in *; intuition.
                  rewrite <- H1 by assumption.
                  unfold Provable in *. destruct (exprD funcs x1 (rev G ++ G0) a tvProp).
                  eapply ST.himp_star_pure_cc; auto. reflexivity.
                  eapply ST.himp_star_pure_cc; auto. reflexivity. } } }
    Qed.

  End canceller.

End Make.
