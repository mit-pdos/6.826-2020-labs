Require Import Helpers.Helpers.
Require Import Proc.
Require Import Abstraction.
Require Import List.
Import ListNotations.


(** * Looping combinators.

    Reasoning about loops in code requires special handling because
    it is not just a matter of stepping through the code in sequence:
    the number of loop iterations might not be known ahead of time!
    For instance, the loop body might be iterated N times:

<<
    loop body iteration 0
    loop body iteration 1
    ..
    loop body iteration N-1
>>

    The typical approach for reasoning about loops is to define a
    loop invariant: a predicate that holds before and after each
    iteration of the loop.  This invariant holds at the boundaries
    of the loop iterations in the above diagram, including just before
    the first loop iteration, and just after the last loop iteration.
    To make the loop invariant useful, the invariant itself is a function
    of how far along we are in the loop.  Annotating the above
    diagram with the loop invariant, we get the following:

<<
     * starting state: loop invariant holds for 0 iterations
    loop body iteration 0
     * intermediate state: loop invariant holds for 1 iterations
    loop body iteration 1
     * intermediate state: loop invariant holds for 2 iterations
    ..
     * intermediate state: loop invariant holds for N-1 iterations
    loop body iteration N-1
     * final state: loop invariant holds for N iterations
>>

    Once we have defined such a loop invariant, we can reason about
    an arbitrary number of iterations of the loop, by proving just
    three facts: that the starting state satisfies the loop invariant
    (at 0 iterations); that the loop invariant after N iterations implies
    whatever final state we are looking for; and that each execution of the
    loop body moves the loop invariant from K iterations to K+1 iterations.
    In diagram form:

<<
    Starting state
          |
          V
    Loop invariant(0)

         ...

    Loop invariant(K)
          |
     [loop body]
          |
          V
    Loop invariant(K+1)

         ...

    Loop invariant(N)
          |
          V
     Final state
>>
  *)

(** ** Combinator for list iteration.

    The first combinator we will define in the above style is for iterating
    over a list, which we call [foreach].  The [foreach] combinator takes a
    list of items, [l], to iterate over, and a [body] procedure to invoke on
    each list element.

    In some cases, we will want to accumulate results as we execute.  This
    is done by passing an accumulator value, of type [T] here, through each
    iteration of the [body].  The [foreach] combinator takes the initial
    value of this accumulator, [acc], and the overall combinator returns the
    final value of this accumulator after all loop iterations are done.
  *)

Fixpoint foreach `(l: list V) `(body: V -> T -> proc T) (acc: T) : proc T :=
  match l with
  | nil =>
    Ret acc
  | v :: l' =>
    acc <- body v acc;
    foreach l' body acc
  end.

(** In the case of list iteration, our loop invariant, [loop_inv], is a
    function of the list we have processed so far, the accumulated value
    of type [T], the ghost state [A], and the current state of the system,
    [State].  A common pattern will be to store the starting state for the
    entire loop in the ghost state, if the loop invariant wants to relate
    the starting state to the current state.

    Given a loop invariant, we can synthesize a spec for the entire invocation
    of [foreach], defined by [foreach_spec] below.  It captures the intuition
    that was laid out at the top of this file: the precondition for [foreach]
    is that the loop invariant holds with an initial [prefix] (which will be
    [nil] in the common case), and the postcondition is that the loop invariant
    now holds with the entire list [l] being processed. The recovered
    condition says that, when we crash, we executed some number of
    iterations of the loop body.
  *)

Definition foreach_spec {R} `(loop_inv: list V -> T -> A -> State -> Prop)
                        (wipe: State -> State -> Prop)
                        (prefix: list V) (l: list V) (acc: T) : Specification A T R State :=
  fun (a : A) state => {|
    pre := loop_inv prefix acc a state;
    post := fun r state' => loop_inv (prefix ++ l) r a state';
    recovered := fun _ state' =>
      exists r n pre_wipe,
        loop_inv (prefix ++ (firstn n l)) r a pre_wipe /\
        wipe pre_wipe state'
  |}.

(** The following theorem, [foreach_ok_helper], proves that [foreach_spec]
    is correct.  It uses induction over the iterations of [foreach], but the
    benefit is that other code that needs to reason about loops no longer
    needs to do low-level Coq induction.  It assumes that the loop body is
    correct in a particularly induction-friendly way, which we will clean up
    below.
  *)

Theorem foreach_ok_helper :
  forall `(loopinv: list V -> T -> A -> State -> Prop)
         (wipe: State -> State -> Prop)
         body `(recover: proc R) abstr l prefix acc,
    rec_wipe recover abstr wipe ->
    ( forall v acc prefix',
      proc_spec (foreach_spec loopinv wipe (prefix++prefix') [v] acc) (body v acc) recover abstr ) ->
    proc_spec (foreach_spec loopinv wipe prefix l acc) (foreach l body acc) recover abstr.
Proof.
  induction l.
  - intros.
    simpl.
    step_proc.
    + rewrite app_nil_r.
      auto.
    + exists acc, 0, state.
      simpl.
      rewrite app_nil_r.
      auto.

  - intros.
    simpl.
    step_proc.
    exists a'.
    intuition idtac.

    + rewrite app_nil_r.
      auto.

    + destruct n.
      * exists r0, 0, pre_wipe.
        simpl in *.
        repeat rewrite app_nil_r in *.
        eauto.

      * exists r0, 1, pre_wipe.
        simpl in *.
        repeat rewrite app_nil_r in *.
        rewrite firstn_nil in *.
        auto.

    + specialize (IHl (prefix ++ [a])).
      eapply proc_spec_implication; intros.
      { eapply IHl; eauto.
        intros.
        rewrite <- app_assoc.
        eauto.
      }

      exists a'.
      simpl in *.
      rewrite app_nil_r in *.

      intuition eauto.
      * rewrite <- app_assoc in *.
        eauto.

      * exists r0, (S n), pre_wipe.
        simpl.
        rewrite <- app_assoc in *.
        intuition eauto.
Qed.

(** In order to reason about [foreach], we need to prove that each
    iteration of the [body] preserves the loop invariant.  The following
    definition, [foreach_body_spec], captures what we expect to be true
    about a single execution of the loop body: starting with a precondition
    that the loop invariant holds for some [prefix] of the list, the
    postcondition must be that the loop invariant holds with one more element
    added to the list, and the recovery condition is that either we processed
    one more element, or we did nothing.
  *)

Definition foreach_body_spec {R} `(loop_inv: list V -> T -> A -> State -> Prop)
                             (wipe: State -> State -> Prop)
                             (prefix: list V) (v: V) (acc: T) : Specification A T R State :=
  fun (a : A) state => {|
    pre := loop_inv prefix acc a state;
    post := fun r state' => loop_inv (prefix ++ [v]) r a state';
    recovered := fun _ state' =>
      exists pre_wipe,
        ( loop_inv prefix acc a pre_wipe \/
          exists r', loop_inv (prefix ++ [v]) r' a pre_wipe ) /\
        wipe pre_wipe state'
  |}.

(** The final theorem, [foreach_ok], simply re-states [foreach_ok_helper]
    using a more friendly definition for what must be true about the loop
    body, with the help of the [foreach_body_spec].
  *)

Theorem foreach_ok :
  forall `(loopinv: list V -> T -> A -> State -> Prop)
         (wipe: State -> State -> Prop)
         body `(recover: proc R) abstr l acc,
    rec_wipe recover abstr wipe ->
    ( forall v acc prefix,
      proc_spec (foreach_body_spec loopinv wipe prefix v acc) (body v acc) recover abstr ) ->
    proc_spec (foreach_spec loopinv wipe nil l acc) (foreach l body acc) recover abstr.
Proof.
  intros.
  eapply foreach_ok_helper.
  { eauto. }

  intros.
  simpl.
  eapply proc_spec_implication.
  { intros.
    eauto. }

  intros.
  simpl in *.
  exists a.
  intuition eauto.

  - exists acc0, 0, pre_wipe.
    simpl.
    rewrite app_nil_r.
    intuition eauto.

  - exists r', 1, pre_wipe.
    simpl.
    intuition eauto.
Qed.


(** ** Combinator for nat iteration.

    A second variant of looping construct that you will find useful
    in the labs is to iterate over [nat] values in some range.  The
    combinator below, [for_range], does exactly that: it invokes the
    [body] code for each [nat] starting with [start] and going up
    [count] from there.

    The accumulator support is analogous to what we defined in [foreach] above.
  *)


Fixpoint for_range (start: nat) (count: nat) `(body: nat -> T -> proc T) (acc: T) : proc T :=
  match count with
  | O =>
    Ret acc
  | S count' =>
    acc <- body start acc;
    for_range (start + 1) count' body acc
  end.

(** The definitions of [for_range_spec] and [for_range_ok] mirror the
    definitions of [foreach_spec] and [foreach_ok] above.  There is no
    analogue of [foreach_ok_helper] and [foreach_body_spec], because the
    [for_range_spec] is usable enough as-is for the body correctness
    condition, without re-phrasing it like we did in [foreach_body_spec].
  *)

Definition for_range_spec {R} `(loop_inv: nat -> T -> A -> State -> Prop)
                          (wipe: State -> State -> Prop)
                          (count: nat) (base: nat) (acc: T) : Specification A T R State :=
  fun (a : A) state => {|
    pre := loop_inv base acc a state;
    post := fun r state' => loop_inv (base+count) r a state';
    recovered := fun _ state' =>
      exists r n pre_wipe,
        loop_inv (base+n) r a pre_wipe /\
        n <= count /\
        wipe pre_wipe state'
  |}.

Theorem for_range_ok :
  forall `(loopinv: nat -> T -> A -> State -> Prop)
         (wipe: State -> State -> Prop)
         body `(recover: proc R) abstr count start acc,
    rec_wipe recover abstr wipe ->
    ( forall n acc,
      n < start+count ->
      proc_spec (for_range_spec loopinv wipe 1 n acc) (body n acc) recover abstr ) ->
    proc_spec (for_range_spec loopinv wipe count start acc) (for_range start count body acc) recover abstr.
Proof.
  induction count.
  - intros.
    simpl.
    step_proc.
    + replace (start + 0) with start by lia.
      eauto.
    + exists acc, 0, state.
      replace (start + 0) with start by lia.
      intuition eauto.

  - intros.
    simpl.
    specialize (H0 start acc ltac:(lia)) as H0'.
    step_proc.
    exists a'.
    intuition idtac.

    + exists r0, n, pre_wipe.
      intuition eauto.
      lia.

    + eapply proc_spec_implication.
      { intros. apply IHcount; eauto.
        intros. eapply H0. lia. }

      intros.
      exists a'.
      simpl.
      intuition eauto.

      * replace (start + S count) with (start + 1 + count) by lia.
        eauto.

      * exists r0, (n+1), pre_wipe.
        intuition eauto.
        { replace (start + (n+1)) with (start + 1 + n) by lia. eauto. }
        { lia. }
Qed.
