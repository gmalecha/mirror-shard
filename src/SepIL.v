Require Import Arith NArith Eqdep_dec List.
Require Import Nomega Word DiscreteMemory.
Require Import PropX PropXTac IL DepList SepTheoryXIL.
Require Import Reflection.

Set Implicit Arguments.

Fixpoint allWordsUpto (width init : nat) : list (word width) :=
  match init with
    | O => nil
    | S init' => natToWord width init' :: allWordsUpto width init'
  end.

Definition allWords_def (width : nat) :=
  allWordsUpto width (pow2 width).

Fixpoint memoryInUpto (width init : nat) (m : word width -> option B)
  : hlist (fun _ => option B) (allWordsUpto width init) :=
  match init with
    | O => HNil
    | S init' =>
      let w := natToWord width init' in
      let v := m w in
      HCons v (memoryInUpto (width := width) init' m)
  end.

Definition memoryIn_def (width : nat) :=
  memoryInUpto (width := width) (pow2 width).

Theorem fcong : forall A (B : A -> Type) (f g : forall x, B x) x,
  f = g
  -> f x = g x.
  congruence.
Defined.

Module Type ALL_WORDS.
  Parameter allWords : forall width : nat, list (word width).

  Axiom allWords_eq : allWords = allWords_def.

  Parameter memoryIn : forall width, (word width -> option B) -> hlist (fun _ : word width => option B) (allWords width).

  Axiom memoryIn_eq : forall width,
    memoryIn (width := width)
    = match fcong (fun width => list (word width)) width (sym_eq allWords_eq) in _ = L return _ -> hlist _ L with
        | refl_equal => memoryIn_def (width := width)
      end.
End ALL_WORDS.

Module AllWords : ALL_WORDS.
  Definition allWords := allWords_def.

  Theorem allWords_eq : allWords = allWords_def.
    reflexivity.
  Defined.

  Definition memoryIn := memoryIn_def.

  Theorem memoryIn_eq : forall width,
    memoryIn (width := width)
    = match fcong (fun width => list (word width)) width (sym_eq allWords_eq) in _ = L return _ -> hlist _ L with
        | refl_equal => memoryIn_def (width := width)
      end.
    reflexivity.
  Qed.
End AllWords.

Import AllWords.
Export AllWords.

Lemma natToWord_injective : forall width n n',
  (n < pow2 width)%nat
  -> (n' < pow2 width)%nat
  -> natToWord width n = natToWord width n'
  -> n = n'.
Proof.
  intros.
  destruct (wordToNat_natToWord width n);
    destruct (wordToNat_natToWord width n');
      intuition.
  rewrite H1 in H4.
  rewrite H4 in H2.
  assert (x = 0).
  destruct x; simpl in *.
  omega.
  generalize dependent (x * pow2 width).
  intros.
  omega.
  assert (x0 = 0).
  destruct x0; simpl in *.
  omega.
  generalize dependent (x0 * pow2 width).
  intros.
  omega.
  subst.
  omega.
Qed.

Local Hint Constructors NoDup.

Lemma NoDup_allWordsUpto' : forall width init' init,
  init <= init' < pow2 width
  -> ~In (natToWord width init') (allWordsUpto width init).
Proof.
  induction init; simpl; intuition;
    match goal with
      | [ H : _ |- _ ] => apply natToWord_injective in H; omega
    end.
Qed.

Local Hint Resolve NoDup_allWordsUpto'.

Theorem NoDup_allWordsUpto : forall width init,
  (init <= pow2 width)%nat
  -> NoDup (allWordsUpto width init).
Proof.
  induction init; simpl; intuition.
Qed.

Theorem NoDup_allWords : forall width,
  NoDup (allWords width).
Proof.
  rewrite allWords_eq; intros; apply NoDup_allWordsUpto; omega.
Qed.

Module BedrockHeap <: Memory.
  Definition addr := W.
  Definition value := B.

  Definition mem := mem.

  Definition mem_get := ReadByte.

  Definition mem_set := WriteByte.
    
  Theorem mem_get_set_eq : forall m p v' m', 
    mem_set m p v' = Some m' ->
    mem_get m' p = Some v'.
  Proof.
    unfold mem_set, mem_get, ReadByte, WriteByte. intros.
    destruct (m p); try congruence.
    inversion H; clear H; subst.
    destruct (weq p p); auto. congruence.
  Qed.
    
  Theorem mem_get_set_neq : forall m p v m', 
    mem_set m p v = Some m' ->
    forall p', p <> p' ->
      mem_get m' p' = mem_get m p'.
  Proof.
    unfold mem_set, mem_get, ReadByte, WriteByte; intros.
    destruct (m p); try congruence.
    inversion H; subst.
    destruct (weq p' p); auto. congruence.
  Qed.

  Definition addr_dec := @weq 32.

  Theorem mem_get_mem_set : forall m p,
    mem_get m p <> None -> forall v, mem_set m p v <> None.
  Proof.
    unfold mem_get, mem_set, ReadByte, WriteByte; intros.
    destruct (m p); auto. congruence.
  Qed.

End BedrockHeap.

Module DiscreteBedrockHeap : DiscreteMemory with Definition addr := BedrockHeap.addr.
  Definition addr := BedrockHeap.addr.

  Definition all_addr := allWords 32.

  Theorem NoDup_all_addr : NoDup all_addr.
    apply NoDup_allWords.
  Qed.
End DiscreteBedrockHeap.

Module BedrockSepHeap := DiscreteHeap BedrockHeap DiscreteBedrockHeap.

Module BedrockSepKernel := SepTheoryXIL_Kernel BedrockSepHeap.

Module ST := SepTheory.SepTheory_From_Kernel BedrockSepKernel.
Import ST.
Export ST.
Import BedrockSepHeap.
Export BedrockSepHeap.

(** * Define some convenient connectives, etc. for specs *)

Definition memoryIn : mem -> smem := BedrockSepHeap.memoryIn.

Definition hpropB sos := BedrockSepKernel.hprop' sos. 
Definition HProp := hpropB nil.

Definition empB sos : hpropB sos := BedrockSepKernel.emp'.
Notation "'Emp'" := (empB _) : Sep_scope.

Definition injB sos (P : Prop) : hpropB sos := BedrockSepKernel.inj' P.

Notation "[| P |]" := (injB _ P) : Sep_scope.

Definition injBX sos (P : propX W (settings * state) sos) : hpropB sos := BedrockSepKernel.injX' P.

Notation "[|| P ||]" := (injBX P) : Sep_scope.

Definition hptsto {sos} (p : W) (b : B) : hpropB sos :=
  fun _ m => [| smem_get p m = Some b /\ 
    forall p', p <> p' -> smem_get p' m = None |]%PropX.

Definition ptsto8 sos : W -> B -> hpropB sos :=
  @hptsto sos.

Notation "a =8> v" := (ptsto8 _ a v) (no associativity, at level 39) : Sep_scope.

Definition smem_set_word (explode : W -> B * B * B * B) (p : W) (v : W) (m : smem) : option smem :=
  let '(v1,v2,v3,v4) := explode v in
  match  smem_set (p ^+ $3) v4 m with
    | Some m => match smem_set (p ^+ $2) v3 m with
                  | Some m => match smem_set (p ^+ $1) v2 m with
                                | Some m => smem_set p v1 m
                                | None => None
                              end
                  | None => None
                end
    | None => None
  end.

Definition smem_get_word (implode : B * B * B * B -> W) (p : W) (m : smem) : option W :=
  match smem_get p m , smem_get (p ^+ $1) m , smem_get (p ^+ $2) m , smem_get (p ^+ $3) m with
    | Some a , Some b , Some c , Some d => Some (implode (a,b,c,d))
    | _ , _ , _ , _ => None
  end.

(* This breaks the hprop abstraction because it needs access to 'settings' *)
Definition ptsto32 sos (a v : W) : hpropB sos :=
  (fun stn sm => [| smem_get_word (implode stn) a sm = Some v
    /\ forall a', a' <> a /\ a' <> (a ^+ $1) /\ a' <> (a ^+ $2) /\ a' <> (a ^+ $3)
      -> smem_get a' sm = None |])%PropX.

Notation "a =*> v" := (ptsto32 _ a v) (no associativity, at level 39) : Sep_scope.

Definition starB sos : hpropB sos -> hpropB sos -> hpropB sos :=
  @BedrockSepKernel.star' sos.

Infix "*" := starB : Sep_scope.

Delimit Scope Sep_scope with Sep.

Fixpoint ptsto32m sos (a : W) (offset : nat) (vs : list W) : hpropB sos :=
  match vs with
    | nil => Emp
    | v :: nil => (match offset with
                     | O => a
                     | _ => a ^+ $(offset)
                   end) =*> v
    | v :: vs' => (match offset with
                     | O => a
                     | _ => a ^+ $(offset)
                   end) =*> v * ptsto32m sos a (4 + offset) vs'
  end%Sep.

Notation "a ==*> v1 , .. , vn" := (ptsto32m _ a O (cons v1 .. (cons vn nil) ..)) (no associativity, at level 39) : Sep_scope.

Definition exB sos T (p : T -> hpropB sos) : hpropB sos := BedrockSepKernel.ex' p.

Notation "'Ex' x , p" := (exB (fun x => p)) : Sep_scope.
Notation "'Ex' x : A , p" := (exB (fun x : A => p)) : Sep_scope.

Definition hvarB sos (x : settings * smem -> propX W (settings * state) sos) : hpropB sos :=
  fun stn sm => x (stn, sm).

Notation "![ x ]" := (hvarB x) : Sep_scope.

Fixpoint arrayOf sos (p : W) (c : list W) : hpropB sos :=
  match c with 
    | nil => [| True |]
    | a :: b => p =*> a * arrayOf sos (p ^+ $4) b
  end%Sep.

Notation "#0" := (![ #0%PropX ])%Sep : Sep_scope.
Notation "#1" := (![ #1%PropX ])%Sep : Sep_scope.
Notation "#2" := (![ #2%PropX ])%Sep : Sep_scope.
Notation "#3" := (![ #3%PropX ])%Sep : Sep_scope.
Notation "#4" := (![ #4%PropX ])%Sep : Sep_scope.

Definition lift1 t sos (p : hpropB sos) : hpropB (t :: sos) :=
  fun a b => Lift (p a b).

Fixpoint lift sos (p : HProp) : hpropB sos :=
  match sos with
    | nil => p
    | _ :: sos' => lift1 _ (lift sos' p)
  end.

Notation "^[ p ]" := (lift _ p) : Sep_scope.

Definition Himp (p1 p2 : HProp) : Prop :=
  BedrockSepKernel.himp p1 p2.

Notation "p1 ===> p2" := (Himp p1%Sep p2%Sep) (no associativity, at level 90).

(** Satisfies lemmas **)
Theorem satisfies_star : forall cs P Q stn sm, 
  interp cs (ST.star P Q stn sm) <->
  exists sm1 sm2, split sm sm1 sm2 /\
    interp cs (P stn sm1) /\ interp cs (Q stn sm2).
Proof.
  clear. unfold ST.star, BedrockSepKernel.star'; intros.

  propxFo; eauto. exists x; exists x0. intuition; eapply simplify_fwd; auto.
Qed.

Theorem satisfies_ex : forall T cs stn sm P,
  interp cs (ST.ex P stn sm) ->
  exists x : T, interp cs (P x stn sm).
Proof.
  unfold ex, BedrockSepKernel.ex'; intros.
  propxFo. eauto.
Qed.

Theorem same_domain_memoryIn : forall a d,
  same_domain a (memoryIn d) ->
  models a d ->
  a = memoryIn d.
Proof.
  clear. unfold smem, models, same_domain, in_domain, smem_get, memoryIn, BedrockSepHeap.memoryIn, smem, BedrockSepHeap.memoryIn, memoryIn.
  generalize (DiscreteBedrockHeap.all_addr).
  induction l; simpl in *; intros; auto.
  rewrite DepList.hlist_nil_only with (h := a); eauto with typeclass_instances.
  { rewrite DepList.hlist_eta with (h := a0) in *; eauto with typeclass_instances.
    simpl in *. intuition.
    f_equal.
    specialize (H a). destruct (M.addr_dec a a); try congruence.
    destruct (DepList.hlist_hd a0). destruct (M.mem_get d a); try congruence.
    destruct (M.mem_get d a); auto. exfalso. eapply H; congruence. 
    
    eapply IHl; eauto. 
Admitted.

Theorem same_domain_memoryIn_mem_set : forall p v m1 m2,
  WriteByte m1 p v = Some m2 ->
  same_domain (memoryIn m1) (memoryIn m2).
Proof.
  clear. unfold same_domain, in_domain, memoryIn, BedrockSepHeap.memoryIn, smem_get, WriteByte, smem.
  generalize DiscreteBedrockHeap.all_addr. induction l; simpl; intros.
  intuition.
  destruct (M.addr_dec a p0); subst; eauto.
  revert H; case_eq (m1 p); try congruence.
  intros; inversion H0; clear H0; subst; simpl in *.
  unfold M.mem_get, ReadByte. destruct (weq p0 p).
  subst. rewrite H in *. intuition congruence.
  firstorder.
Qed.

Theorem satisfies_get_word : forall sm m p t stn,
  models sm m ->
  smem_get_word (implode stn) p sm = Some t ->
  Memory.mem_get_word W mem footprint_w ReadByte (implode stn) p m = Some t.
Proof.
  clear. unfold smem_get_word, Memory.mem_get_word, footprint_w, ReadByte; intros.
  repeat match goal with
           | [ |- context [ ?m ?p ] ] => 
             change (m p) with (M.mem_get m p)
         end.
  repeat match goal with
           | [ H : match ?X with _ => _ end = _ |- _ ] => consider X; try congruence; intros
         end.
  repeat erewrite smem_get_sound by eassumption. auto.
Qed.

Theorem satisfies_set_word : forall sm sm' m p v stn,
  models sm m ->
  smem_set_word (explode stn) p v sm = Some sm' ->
  same_domain sm sm' /\
  exists m', models sm' m' /\
    Memory.mem_set_word W mem footprint_w WriteByte (explode stn) p v m = Some m'.
Proof.
  clear. unfold smem_set_word, Memory.mem_set_word, footprint_w; intros.
  destruct (explode stn v). destruct p0. destruct p0.
  repeat match goal with
           | [ H : match ?X with _ => _ end = _ |- _ ] => consider X; try congruence; intros
         end.
  repeat match goal with
           | [ H : exists x , _ |- _ ] => destruct H
           | [ H : _ /\ _ |- _ ] => destruct H
           | [ H : smem_set _ _ _ = _ |- _ ] =>
             (eapply smem_set_sound in H; try eassumption) ; [] 
           | [ H : _ = _ |- _ ] => rewrite H
           | [ |- _ ] => unfold M.mem_set in *
         end.
  intuition eauto.
  repeat (etransitivity; [ eassumption | eauto ]).
Qed.

Theorem smem_get_set_word_eq : forall e i m p v' m', 
  (forall x, i (e x) = x) ->
  smem_set_word e p v' m = Some m' ->
  smem_get_word i p m' = Some v'.
Proof.
  unfold smem_set_word, smem_get_word; intros.
  specialize (H v'). destruct (e v') as [ [ [ ? ? ] ? ] ? ].
  repeat match goal with
           | [ H : match ?X with _ => _ end = _ |- _ ] => consider X; try congruence; intros
           | [ |- _ ] => erewrite smem_set_get_eq by eassumption
           | [ |- _ ] => erewrite smem_set_get_neq; [ | eassumption | word_neq ]
         end.
  subst; auto.
Qed.

Theorem split_smem_get_word : forall a b c p v i,
  split a b c -> 
    smem_get_word i p b = Some v -> 
    smem_get_word i p a = Some v.
Proof.
  clear.
  unfold smem_get_word, Memory.mem_get_word, footprint_w, ReadByte; intros.
  repeat match goal with
           | [ H : match ?X with _ => _ end = _ |- _ ] => consider X; try congruence; intros
         end.
  repeat erewrite split_smem_get by eassumption. auto.
Qed.

Theorem split_smem_set_word : forall a b b' c p v i,
  split a b c -> 
    smem_set_word i p v b = Some b' -> 
    exists a', split a' b' c /\ 
      smem_set_word i p v a = Some a'.
Proof.
  clear. unfold smem_set_word, Memory.mem_set_word, footprint_w; intros.
  repeat match goal with
           | [ H : match ?X with _ => _ end = _ |- _ ] => consider X; try congruence; intros
           | [ H : exists x, _ |- _ ] => destruct H
           | [ H : _ /\ _ |- _ ] => destruct H
           | [ H : _ = _ |- _ ] => rewrite H
           | [ H : smem_set _ _ _ = _ |- _ ] => 
             (eapply split_smem_set in H; try eassumption); []
         end; subst.
  eapply split_smem_set; eauto.
Qed.

Theorem same_domain_memoryIn_mem_set_word : forall p v m1 m2 e,
  Memory.mem_set_word W mem footprint_w WriteByte 
  e p v m1 = Some m2 ->
  same_domain (memoryIn m1) (memoryIn m2).
Proof.
  clear. unfold Memory.mem_set_word; intros.
  destruct (footprint_w p) as [ [ [ ? ? ] ? ] ? ].
  destruct (e v) as [ [ [ ? ? ] ? ] ? ].
  repeat match goal with
           | [ H : WriteByte _ _ _ = _ |- _ ] => 
             apply same_domain_memoryIn_mem_set in H
           | [ H : match ?X with _ => _ end = _ |- _ ] => 
             revert H; case_eq X; intros; try congruence
         end.
  repeat (etransitivity; [ eassumption | eauto ]).
Qed.

Theorem smem_get_set_word_valid : forall m p v i e,
  smem_get_word i p m <> None ->
  smem_set_word e p v m <> None.
Proof.
  unfold smem_set_word, smem_get_word; intros.
  destruct (e v) as [ [ [ ] ] ].
  intro. eapply H; clear H.
  repeat match goal with
           | [ |- match ?X with _ => _ end = _ ] =>
             case_eq X; intros; try congruence
         end; exfalso.
  repeat match goal with
           | [ H' : smem_get ?P ?M = Some _ 
             , H : smem_set ?P ?V ?M = None |- _ ] =>
           eapply smem_get_set_valid with (p := P) (v := V) (m := M); eauto; try congruence
           | [ H : smem_set _ _ _ = Some _ 
             , H' : _ |- _ ] =>
           erewrite <- (@smem_set_get_neq _ _ _ _ H) in H' by word_neq
           | [ H : match ?X with _ => _ end = _ |- _ ] => revert H; case_eq X; intros
  end.
Qed.

(** * The main injector of separation formulas into PropX *)
Definition sepFormula_def sos (p : hpropB sos) (st : settings * state) : propX W (settings * state) sos :=
  p (fst st) (memoryIn (Mem (snd st))).

Module Type SEP_FORMULA.
  Parameter sepFormula : forall sos, hpropB sos -> settings * state -> propX W (settings * state) sos.

  Axiom sepFormula_eq : sepFormula = sepFormula_def.
End SEP_FORMULA.

Module SepFormula : SEP_FORMULA.
  Definition sepFormula := sepFormula_def.

  Theorem sepFormula_eq : sepFormula = sepFormula_def.
    reflexivity.
  Qed.
End SepFormula.

Import SepFormula.

Require Import RelationClasses Setoid.

Global Add Parametric Morphism cs : (@sepFormula nil) with
  signature (himp ==> @eq (settings * state) ==> @PropXRel.PropX_imply _ _ cs)
as sepFormula_himp_imply.
  unfold himp. rewrite sepFormula_eq.
  unfold sepFormula_def.
  unfold PropXRel.PropX_imply.
  intros. unfold interp. eapply H.
Qed.
Global Add Parametric Morphism cs : (@sepFormula nil) with
  signature (@heq ==> @eq (settings * state) ==> @PropXRel.PropX_eq _ _ cs)
as sepFormula_himp_eq.
  rewrite sepFormula_eq. unfold heq, himp, sepFormula_def, PropXRel.PropX_eq, PropXRel.PropX_imply.
  intros. unfold interp in *. intuition; PropXRel.propxIntuition; eauto. 
Qed.

Export SepFormula.

Definition substH sos (p1 : hpropB sos) (p2 : last sos -> PropX W (settings * state)) : hpropB (eatLast sos) :=
  fun st m => subst (p1 st m) p2.

Theorem subst_sepFormula : forall sos (p1 : hpropB sos) p2 st,
  subst (sepFormula p1 st) p2 = sepFormula (substH p1 p2) st.
  rewrite sepFormula_eq; reflexivity.
Qed.

Hint Rewrite subst_sepFormula : sepFormula.

Theorem substH_inj : forall sos P p,
  substH (injB sos P) p = injB _ P.
  reflexivity.
Qed.

Theorem substH_injX : forall sos P p,
  substH (injBX (sos := sos) P) p = injBX (subst P p).
  reflexivity.
Qed.

Theorem substH_ptsto8 : forall sos a v p,
  substH (ptsto8 sos a v) p = ptsto8 _ a v.
  reflexivity.
Qed.

Theorem substH_ptsto32 : forall sos a v p,
  substH (ptsto32 sos a v) p = ptsto32 _ a v.
  reflexivity.
Qed.

Theorem substH_star : forall sos (p1 p2 : hpropB sos) p3,
  substH (starB p1 p2) p3 = starB (substH p1 p3) (substH p2 p3).
  reflexivity.
Qed.

Theorem substH_ex : forall sos A (p1 : A -> hpropB sos) p2,
  substH (exB p1) p2 = exB (fun x => substH (p1 x) p2).
  reflexivity.
Qed.

Theorem substH_hvar : forall sos (x : settings * smem -> propX W (settings * state) sos) p,
  substH (hvarB x) p = hvarB (fun m => subst (x m) p).
  reflexivity.
Qed.

Definition HProp_extensional (p : HProp) :=
  p = fun st sm => p st sm.

Hint Extern 1 (HProp_extensional _ ) => reflexivity.

Theorem substH_lift1 : forall p' t p,
  HProp_extensional p'
  -> substH (lift (t :: nil) p') p = p'.
  intros; rewrite H; reflexivity.
Qed.

Theorem substH_lift2 : forall p' t1 t2 p,
  substH (lift (t1 :: t2 :: nil) p') p = lift (t1 :: nil) p'.
  reflexivity.
Qed.

Theorem substH_lift3 : forall p' t1 t2 t3 p,
  substH (lift (t1 :: t2 :: t3 :: nil) p') p = lift (t1 :: t2 :: nil) p'.
  reflexivity.
Qed.

Theorem substH_lift4 : forall p' t1 t2 t3 t4 p,
  substH (lift (t1 :: t2 :: t3 :: t4 :: nil) p') p = lift (t1 :: t2 :: t3 :: nil) p'.
  reflexivity.
Qed.

Theorem substH_lift1_eatLast : forall T U P p,
  HProp_extensional P ->
  substH (sos := eatLast (T :: U :: nil)) (^[P])%Sep p = P.
Proof.
  intros. simpl eatLast. rewrite substH_lift1; auto.
Qed.

Theorem star_eta1 : forall sos (p1 p2 : hpropB sos),
  starB (fun st m => p1 st m) p2 = starB p1 p2.
  reflexivity.
Qed.

Theorem star_eta2 : forall sos (p1 p2 : hpropB sos),
  starB p1 (fun st m => p2 st m) = starB p1 p2.
  reflexivity.
Qed.


Hint Rewrite substH_inj substH_injX substH_ptsto8 substH_ptsto32 substH_star substH_ex substH_hvar
  substH_lift1 substH_lift2 substH_lift3 substH_lift4
  substH_lift1_eatLast star_eta1 star_eta2
  using solve [ auto ] : sepFormula.

Global Opaque lift.

Notation "![ p ]" := (sepFormula p%Sep) : PropX_scope.

Definition natToByte (n : nat) : B := natToWord _ n.

Coercion natToByte : nat >-> B.

(* *)
Require SepExpr SepHeap.
Module SEP := SepExpr.Make ST.
Module SH := SepHeap.Make SEP.

Theorem natToW_plus : forall n m, natToW (n + m) = natToW n ^+ natToW m.
  apply natToWord_plus.
Qed.

Lemma natToW_S : forall n, natToW (S n) = $1 ^+ natToW n.
  apply natToWord_S.
Qed.

Hint Rewrite <- natToW_plus : sepFormula.

Lemma natToW_minus : forall n m, (m <= n)%nat
  -> natToW (n - m) = natToW n ^- natToW m.
  intros; apply wplus_cancel with (natToW m).
  rewrite <- natToWord_plus.
  replace (n - m + m) with n by omega.
  unfold natToW.
  W_eq.
Qed.

Lemma natToW_times4 : forall n, natToW (n * 4) = natToW n ^* natToW 4.
  intros.
  replace (natToW n ^* natToW 4) with (natToW n ^+ (natToW n ^+ (natToW n ^+ (natToW n ^+ natToW 0)))).
  autorewrite with sepFormula.
  intros; rewrite mult_comm; simpl.
  reflexivity.
  W_eq.
Qed.

Lemma Himp_trans : forall p q r,
  p ===> q
  -> q ===> r
  -> p ===> r.
  unfold Himp, himp; eauto using Imply_trans.
Qed.

(*
Lemma himp_star_frame_comm : forall (P Q R S : hprop),
    himp P Q -> himp R S -> himp (star P R) (star S Q).
Proof.
  intros; eapply Trans_himp; [ | apply himp_star_comm ].
  apply himp_star_frame; auto.
Qed.
*)

(** * [goodSize] *)

Hint Extern 1 (goodSize _) => reflexivity.

Lemma goodSize_plus_l : forall n m sz, (N.of_nat (n + m) < sz)%N -> (N.of_nat n < sz)%N.
  unfold goodSize; intros; nomega.
Qed.
