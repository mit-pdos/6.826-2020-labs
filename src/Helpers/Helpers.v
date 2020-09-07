Require Import Arith.
Require Import Lia.
Require Import Bool.
Require Import List.
Require Import EquivDec.
Require Import Omega.

Set Implicit Arguments.


(** * Decidable equality.

    [EqualDec] defines a notion of decidable equality for things
    of type [A].  This means that there is a function, called
    [equal_dec], which, given two things of type [A], will return
    whether they are equal or not.
  *)

Class EqualDec A :=
  equal_dec : forall x y : A, { x = y } + { x <> y }.

(**
    We define the notation [x == y] to mean our decidable equality
    between [x] and [y].
  *)

Notation " x == y " := (equal_dec (x :>) (y :>)) (no associativity, at level 70).

(**
    Here, we define some types for which we know how to compute
    decidable equality (namely, equality for [nat]s, and equality
    for [bool]s).
  *)

Instance nat_equal_dec : EqualDec nat := eq_nat_dec.
Instance bool_equal_dec : EqualDec bool := bool_dec.


(** * [maybe_holds] predicate.

    One pattern that shows up in our lab assignments is that we
    want to say something about an optional value.  That is, we
    have something of type [option T], which is either [Some x]
    where [x] is of type [T], or is [None].  We want to make
    staements of the form ``if it's [Some x], then something is
    true about [x]''.  This shows up when we talk about a disk
    that might or might not have failed, or when we talk about
    the contents of a disk block that might or might not be there
    (e.g., because it's out of bounds).

    We define [maybe_holds] to formalize this notion.  [maybe_holds]
    takes a predicate, [T -> Prop], and an [option T].
  *)

Definition maybe_holds T (p:T -> Prop) : option T -> Prop :=
  fun mt => match mt with
         | Some t => p t
         | None => True
         end.

Theorem holds_in_none_eq : forall T (p:T -> Prop) mt,
    mt = None ->
    maybe_holds p mt.
Proof.
  intros; subst.
  simpl; auto.
Qed.

Theorem holds_in_some : forall T (p:T -> Prop) (v:T),
    p v ->
    maybe_holds p (Some v).
Proof.
  simpl; auto.
Qed.

Theorem holds_in_some_eq : forall T (p:T -> Prop) (v:T) mt,
    mt = Some v ->
    p v ->
    maybe_holds p mt.
Proof.
  intros; subst.
  simpl; auto.
Qed.

Theorem holds_some_inv_eq : forall T (p: T -> Prop) mt v,
    mt = Some v ->
    maybe_holds p mt ->
    p v.
Proof.
  intros; subst.
  auto.
Qed.

Theorem pred_weaken : forall T (p p': T -> Prop) mt,
    maybe_holds p mt ->
    (forall t, p t -> p' t) ->
    maybe_holds p' mt.
Proof.
  unfold maybe_holds; destruct mt; eauto.
Qed.

(** To reflect the expected usage of this primitive, we define
    two notations:

    - [mv ?|= p] states that [p] holds on [mv], if [mv] is present.
      This notation simply translates to [maybe_holds p mv].

    - To state that an optional value is definitely missing,
      we provide a predicate [missing], so that [mv ?|= missing]
      implies that [mv] is [None].  The [missing] predicate is simply
      [False], which allows us to conclude by contradiction that
      there's no way the optional value could be [Some x].
  *)

Notation "m ?|= F" := (maybe_holds F m) (at level 20, F at level 50).

Definition missing {T} : T -> Prop := fun _ => False.

Theorem pred_missing : forall T (p: T -> Prop) mt,
    mt ?|= missing ->
    mt ?|= p.
Proof.
  unfold missing; intros.
  eapply pred_weaken; eauto.
  contradiction.
Qed.


(** * [maybe_eq] predicate for equality.

    We also define a specialized version of [maybe_holds] that
    is used to specify an equality predicate about an optional
    value: [maybe_eq].  [maybe_eq mv v] says that [mv] is either
    [None] or [Some v].  The notation for this is [mv =?= v].
  *)

Definition maybe_eq T (mv : option T) (v : T) : Prop :=
  maybe_holds (eq v) mv.

Notation "mv =?= v" := (maybe_eq mv v) (at level 20, v at level 50).


(** * [maybe_eq_list] for equality of lists.

    [maybe_eq_list] is a version of [maybe_eq] that applies
    to a list of optional values: given a list of optional values,
    and a list of values, [maybe_eq_list] says that each
    value is [maybe_eq] equal to the corresponding optional value.

    We use the notation [mvs =??= vs] for [maybe_eq_list mvs vs].
  *)

Fixpoint maybe_eq_list T (ml : list (option T)) (l:list T) : Prop :=
  match ml, l with
  | nil, nil => True
  | ml0::ml', l0::l' =>
    maybe_eq ml0 l0 /\
    maybe_eq_list ml' l'
  | _, _ => False
  end.

Notation "mvs =??= vs" := (maybe_eq_list mvs vs) (at level 20, vs at level 50).

Theorem maybe_eq_list_first :
  forall T p0 l0 p l,
    @maybe_eq_list T (p0::p) (l0::l) <->
    maybe_eq p0 l0 /\ maybe_eq_list p l.
Proof.
  firstorder.
Qed.

Theorem maybe_eq_list_len :
  forall T p l,
    @maybe_eq_list T p l -> length p = length l.
Proof.
  induction p; simpl; intros.
  - destruct l; intuition.
  - destruct l; simpl; intuition.
Qed.

Theorem maybe_eq_list_last_helper :
  forall T p0 l0 p l,
    length p = length l ->
    @maybe_eq_list T (p ++ (p0::nil)) (l ++ (l0::nil)) <->
    maybe_eq_list p l /\ maybe_eq p0 l0.
Proof.
  induction p; simpl; intros.
  - destruct l; simpl in *; try congruence.
    intuition.
  - destruct l; simpl in *; try congruence.
    inversion H; clear H.
    specialize (IHp l).
    split; intuition.
Qed.

Theorem maybe_eq_list_last :
  forall T p0 l0 p l,
    @maybe_eq_list T (p ++ (p0::nil)) (l ++ (l0::nil)) <->
    maybe_eq_list p l /\ maybe_eq p0 l0.
Proof.
  split; intros.
  - apply maybe_eq_list_last_helper; auto.
    apply maybe_eq_list_len in H.
    repeat rewrite app_length in H; simpl in *.
    lia.
  - apply maybe_eq_list_last_helper; auto.
    intuition.
    apply maybe_eq_list_len; auto.
Qed.

Theorem maybe_eq_list_app :
  forall T p0 p1 l0 l1,
    @maybe_eq_list T p0 l0 ->
    maybe_eq_list p1 l1 ->
    maybe_eq_list (p0++p1) (l0++l1).
Proof.
  induction p0; simpl; intros.
  - destruct l0; intuition.
  - destruct l0; intuition.
    simpl; auto.
Qed.

Theorem maybe_eq_list_map_some :
  forall T (l : list T),
    maybe_eq_list (map Some l) l.
Proof.
  induction l; simpl; auto.
Qed.


(** * Proof automation.

    To help prove various theorems, we provide some basic automation.
    This automation takes the form of Ltac scripts that are designed
    to solve certain types of goals, or simplify the goal in some way.
    We also use hints (using various [Hint] statements), which is a
    way to tell Coq which theorems should be used by tactics like
    [auto], [eauto], [autorewrite], and so on.
  *)

(** ** Simplify matches when possible *)

Ltac simpl_match :=
  let repl_match_goal d d' :=
      replace d with d';
      lazymatch goal with
      | [ |- context[match d' with _ => _ end] ] => fail
      | _ => idtac
      end in
  let repl_match_hyp H d d' :=
      replace d with d' in H;
      lazymatch type of H with
      | context[match d' with _ => _ end] => fail
      | _ => idtac
      end in
  match goal with
  | [ Heq: ?d = ?d' |- context[match ?d with _ => _ end] ] =>
    repl_match_goal d d'
  | [ Heq: ?d' = ?d |- context[match ?d with _ => _ end] ] =>
    repl_match_goal d d'
  | [ Heq: ?d = ?d', H: context[match ?d with _ => _ end] |- _ ] =>
    repl_match_hyp H d d'
  | [ Heq: ?d' = ?d, H: context[match ?d with _ => _ end] |- _ ] =>
    repl_match_hyp H d d'
  end.

Module SimplMatchTests.

  (** test simpl_match failure when match does not go away *)
  Theorem fails_if_match_not_removed :
    forall (vd m: nat -> option nat) a,
      vd a = m a ->
      vd a = match (m a) with
             | Some v => Some v
             | None => None
             end.
  Proof.
    intros.
    (simpl_match; fail "should not work here")
    || idtac.
    rewrite H.
    destruct (m a); auto.
  Qed.

  Theorem removes_match :
    forall (vd m: nat -> option nat) a v v',
      vd a = Some v ->
      m a = Some v' ->
      vd a = match (m a) with
             | Some _ => Some v
             | None => None
             end.
  Proof.
    intros.
    simpl_match; now auto.
  Qed.

  (** hypothesis replacement should remove the match or fail *)
  Theorem fails_on_hyp_if_match_not_removed :
    forall (vd m: nat -> option nat) a,
      vd a = m a ->
      m a = match (m a) with
            | Some v => Some v
            | None => None
            end ->
      True.
  Proof.
    intros.
    (simpl_match; fail "should not work here")
    || idtac.
    trivial.
  Qed.

End SimplMatchTests.

(** ** Find and destruct matches *)

Ltac destruct_matches_in e :=
  lazymatch e with
  | context[match ?d with | _ => _ end] =>
    destruct_matches_in d
  | _ => destruct e eqn:?; intros
  end.

Ltac destruct_all_matches :=
  repeat (try simpl_match;
          try match goal with
              | [ |- context[match ?d with | _ => _ end] ] =>
                destruct_matches_in d
              | [ H: context[match ?d with | _ => _ end] |- _ ] =>
                destruct_matches_in d
              end);
  subst;
  try congruence;
  auto.

Ltac destruct_nongoal_matches :=
  repeat (try simpl_match;
           try match goal with
           | [ H: context[match ?d with | _ => _ end] |- _ ] =>
             destruct_matches_in d
               end);
  subst;
  try congruence;
  auto.

Ltac destruct_goal_matches :=
  repeat (try simpl_match;
           match goal with
           | [ |- context[match ?d with | _ => _ end] ] =>
              destruct_matches_in d
           end);
  try congruence;
  auto.

Module DestructMatchesTests.

  Theorem removes_absurdities :
    forall b1 b2,
      b1 = b2 ->
      match b1 with
      | true => match b2 with
               | true => True
               | false => False
               end
      | false => match b2 with
                | true => False
                | false => True
                end
      end.
  Proof.
    intros.
    destruct_all_matches.
  Qed.

  Theorem destructs_innermost_match :
    forall b1 b2,
      match (match b2 with
             | true => b1
             | false => false
             end) with
      | true => b1 = true
      | false => b1 = false \/ b2 = false
      end.
  Proof.
    intros.
    destruct_goal_matches.
  Qed.

End DestructMatchesTests.

Ltac destruct_tuple :=
  match goal with
  | [ H: context[let '(a, b) := ?p in _] |- _ ] =>
    let a := fresh a in
    let b := fresh b in
    destruct p as [a b]
  | [ |- context[let '(a, b) := ?p in _] ] =>
    let a := fresh a in
    let b := fresh b in
    destruct p as [a b]
  end.

Tactic Notation "destruct" "matches" "in" "*" := destruct_all_matches.
Tactic Notation "destruct" "matches" "in" "*|-" := destruct_nongoal_matches.
Tactic Notation "destruct" "matches" := destruct_goal_matches.


(** ** Variants of intuition that do not split the goal. *)

Ltac safe_intuition_then t :=
  repeat match goal with
         | [ H: _ /\ _ |- _ ] =>
           destruct H
         | [ H: ?P -> _ |- _ ] =>
           lazymatch type of P with
           | Prop => specialize (H ltac:(t))
           | _ => fail
           end
         | _ => progress t
         end.

Tactic Notation "safe_intuition" := safe_intuition_then ltac:(auto).
Tactic Notation "safe_intuition" tactic(t) := safe_intuition_then t.


(** * Instantiate existentials (deex) *)

Ltac destruct_ands :=
  repeat match goal with
         | [ H: _ /\ _ |- _ ] =>
           destruct H
         end.

Ltac deex :=
  match goal with
  | [ H : exists (varname : _), _ |- _ ] =>
    let newvar := fresh varname in
    destruct H as [newvar ?]; destruct_ands; subst
  end.

Module DeexTests.

  Theorem chooses_name :
    (exists (foo:unit), foo=foo) ->
    True.
  Proof.
    intros.
    deex.
    destruct foo.
    trivial.
  Qed.

  Theorem chooses_fresh_name :
    forall (foo:bool),
      (exists (foo:unit), foo=foo) -> True.
  Proof.
    intros.
    deex.
    (* fresh name for exists witness *)
    destruct foo0.
    trivial.
  Qed.

End DeexTests.

(** ** Other proof automation helpers *)

Ltac descend :=
  repeat match goal with
         | |- exists _, _ => eexists
         end.

Ltac propositional_with t :=
  repeat match goal with
         | |- forall _, _ => intros
         | [ H: _ /\ _ |- _ ] => destruct H
         | [ H: _ <-> _ |- _ ] => destruct H
         | [ H: False |- _ ] => solve [ destruct H ]
         | [ |- True ] => exact I
         | [ H: True |- _ ] => clear H
         | [ H: ?P -> _ |- _ ] =>
           lazymatch type of P with
           | Prop => match goal with
                 | [ H': P |- _ ] => specialize (H H')
                 | _ => specialize (H ltac:(try t))
                 end
           end
         | [ H: forall x, x = _ -> _ |- _ ] =>
           specialize (H _ eq_refl)
         | [ H: forall x, _ = x -> _ |- _ ] =>
           specialize (H _ eq_refl)
         | [ H: exists (varname : _), _ |- _ ] =>
           let newvar := fresh varname in
           destruct H as [newvar ?]
         | [ H: ?P |- ?P ] => exact H
         | _ => progress subst
         | _ => solve [ t ]
         end.

Tactic Notation "propositional" := propositional_with auto.
Tactic Notation "propositional" tactic(t) := propositional_with t.

Ltac split_or :=
  repeat match goal with
         | [ H: _ \/ _ |- _ ] => destruct H
         end.

Ltac intuition_with t :=
  repeat match goal with
         | [ H: _ \/ _ |- _ ] => destruct H
         | _ => progress propositional_with t
         | |- _ /\ _ => split
         | |- _ <-> _ => split
         | _ => t
         end.

Tactic Notation "intuition" := intuition_with auto.
Tactic Notation "intuition" tactic(t) := intuition_with t.

Tactic Notation "omega" := fail "don't use omega".

Ltac lia :=
  repeat match goal with
         | [ H: ?a <> ?a |- _ ] =>
           exfalso; apply (H eq_refl)
         | |- _ <> _ => let H := fresh in
                     intro H;
                     try rewrite H in *
         | [ n: ?t |- _ ] => progress change t with nat
         | [ H: @eq ?t _ _ |- _ ] =>
           progress change t with nat in H
         | [ H: ~ (@eq ?t _ _) |- _ ] =>
           progress change t with nat in H
         | [ |- @eq ?t _ _ ] =>
           progress change t with nat
         | [ |- ~ (@eq ?t _ _) ] =>
           progress change t with nat
         end; Lia.lia.

Ltac sigT_eq :=
  match goal with
  | [ H: existT ?P ?a _ = existT ?P ?a _ |- _ ] =>
    apply Eqdep.EqdepTheory.inj_pair2 in H; subst
  end.

(** substitute variables that are let bindings (these can be created with [set
(x:=value)] and appear in the context as [v := def]) *)
Ltac subst_var :=
  repeat match goal with
  | [ v := _ |- _ ] => subst v
  end.

Create HintDb false.

Ltac solve_false :=
  solve [ exfalso; eauto with false ].

(* use lemmas that prove false during ordinary calls to [auto] (copies a hint
from [Coq.Program.Equality]) *)
Hint Extern 10 => Equality.is_ground_goal; progress exfalso : core.

Ltac especialize H :=
  match type of H with
  | forall (x:?T), _ =>
    let x := fresh x in
    evar (x:T);
    specialize (H x);
    subst x
  end.

Ltac rename_by_type type name :=
  match goal with | x : type |- _ => rename x into name end.
