Require Import Helpers.Helpers.
Require Import Proc.
Require Import ProcTheorems.

(** The Coq standard library requires us to explicitly import support
    for printing strings.  This is used to display hints in the proof
    context about where the proof goal came from.
  *)

Require Import String.
Export String.StringSyntax.


(** * Specification style: Abstractions with pre- and post-conditions

 In POCS you will often write specifications that abstract away
 the state manipulated by the lower-level code into a higher-level
 representation of the state, which we will call a "spec state".
 This style of specification, for a given procedure, consists of
 two parts: (1) the type of the abstract state, and (2) a description
 of how this abstract state can change as a result of running a procedure.

 To prove that an implementation (code) meets its specification
 (spec), which puts the following obligations on you:

 - You need to define an abstraction relation that connects code
   states and spec states;

 - Whenever the code runs from state [w] to state [w'] and the abstraction
   relation holds between [w] and [state], you must show that there exists
   a spec state [state'] for which the abstraction relation holds between
   [w'] and [state'], and that the specification allows the procedure to
   change the abstract state from [state] to [state'].

 Here's a picture representing these proof obligations:

<<
                     spec semantics
     forall state ===================> exists state'
              ^                                 ^^
         absR |                            absR ||
              V   semantics of code             VV
       forall w  -----------------------> forall w'
>>

 Single lines are what the proof assumes, and double lines are what you
 must show in your proof.

 The rest of this file defines what it means to construct an abstraction
 relation between code states and spec states, what it means to define a
 specification, and how we can structure these proofs.
 *)

(** ** Abstraction relation and composition *)

(** A LayerAbstraction is a record with one field, [abstraction],
  which relates two states: one of type [State1] and another of type [State2].
  Think of [State1] as being the type of code states whereas [State2] is the
  type for specification states.  The abstraction relation links these two
  states together.

  For example, in StatDB lab, the spec state is a list of
  integers and the implementation state is is a pair of variables.  In the
  StatDB lab, the
  [abstraction] function must state what must be true of the relationship between
  the list of integers and the pair of variables.
 *)

Record LayerAbstraction State1 State2 :=
  { abstraction : State1 -> State2 -> Prop; }.

(**
  The above definition of [LayerAbstraction] helps us connect two
  layers, such as the layer of variables and the layer of the StatDB
  specification.

  A particular kind of abstraction is one that connects the bottom-most
  type of state, [world], with some abstract state above the world.
  (Recall that our model of execution is that, at the lowest level,
  procedures (code) always manipulates the "real world", whose state
  is of type [world].)

  We define [Abstraction] to be this particular kind of abstraction:
  it is a relation between [world] states and some other type of states,
  [State].
 *)

Definition Abstraction State := LayerAbstraction world State.

(**
  We can compose abstractions, by layering one abstraction on top
  of another.  In our case, since everything is ultimately connected
  to [world] states at the bottom, we define a composition of two
  kinds of abstraction: one that goes from [world] states to [State1],
  and another that goes from [State1] to [State2], to produce an
  abstraction from [world] to [State2].

  [abstraction_compose] makes this connection precise, by saying
  that [world] and [State2] states are connected by the fact that
  there exists some intermediate [State1] state that matches the
  two abstractions being composed.
  *)

Definition abstraction_compose
           `(abs1: Abstraction State1)
           `(abs2: LayerAbstraction State1 State2) :=
  {| abstraction := fun w state' => exists state, abstraction abs2 state state' /\
                                  abstraction abs1 w state; |}.

(**
  In some situations, we will want to keep the same level of abstraction
  (i.e., have the code and spec states be the same).  [IdAbstraction]
  defines this "identity" kind of abstraction: it is a relation between
  states of the same type [State], and the relation says that the two
  states must be equal.
 *)

Definition IdAbstraction State : LayerAbstraction State State :=
  {| abstraction := fun state state' => state' = state; |}.


(** ** Specification *)

(** Our specifications describe how a procedure can change the
  state of the system, at some level of abstraction.  We describe
  the allowed state changes using pre- and post-conditions, as
  captured by the following structure, [SpecProps].

  [SpecProps] is parametrized by three types: [T], [R], and [State].

  [State] is the type of states that this specification uses.
  For instance, in the StatDB example, [State] would be [list nat].

  [T] is the type of the return value of the procedure being
  specified.  Note that the [post] condition is a function of
  two arguments: one of type [T] (the returned value), and another
  of type [State] (the resulting state).

  In addition to pre- and post-conditions, our specifications include
  recovery conditions, which help reason about crashes during the
  execution of a procedure.  After a crash, a recovery procedure will
  run to recover any state from the crash.  The recovery procedure may
  also return some result; this result's type is [R], and the recovery
  condition, [recovered], takes two arguments: the return value from
  recovery, [R], and the state after recovery, [State].
 *)

Record SpecProps T R State :=
  Spec {
    pre: Prop;
    post: T -> State -> Prop;
    recovered: R -> State -> Prop;
  }.

(**
  One obvious part missing from the [SpecProps] specification is any
  reference to the starting state.  The reason we didn't pass it as
  an argument to the precondition, [pre], is that it's useful to refer
  to the starting state inside the [post] and [recovered] conditions
  as well, in order to connect the final state to the starting state.

  Another part which is not so obviously missing is a way to talk about
  existential variables in the specification (sometimes called "ghost
  variables" in the PL literature).  This is a bit hard to
  grasp in an abstract sense; we will use this in lab 4, and it's safe
  to ignore it until then.

  We add these two missing parts to a specification by defining the
  actual type of specifications, [Specification], as a function from
  a ghost variable [A] and a starting state [State] to a [SpecProps].
  This allows the pre-, post-, and recovered conditions in [SpecProps]
  to refer to the starting state (and the ghost variable).
 *)

Definition Specification A T R State := A -> State -> SpecProps T R State.


(** ** Correctness of a procedure

  [proc_spec] defines when a specification holds for a procedure
  [p] and a recovery procedure [rec].  (The recovery procedure
  will become important in labs 3 and 4, when we reason about
  crashes.)  [proc_spec] formalizes our intuition of what it
  might mean to satisfy a pre- and post-condition specification.

  The general shape of what [proc_spec] says, ignoring recovery
  for now, is:

<<
            pre                      post
             |                        ||
             V                        VV
           state                    state'
             ^                        ^^
        absR |                   absR ||
             V                        VV
             w ---[procedure p]-----> w'
>>

  The single arrows indicate the assumptions (that there exists
  some starting abstract state [state], corresponding to a world
  state [w], where the precondition [pre] holds, and that running
  the procedure [p] gives us state [w'].)

  The double arrows indicate what [proc_spec] concludes: that there
  is an abstract state [state'] corresponding to [w'], and that the
  postcondition holds in that resulting state [state'].

  This picture should look familiar; it is quite similar to the
  proof obligations described at the top of this file, with the
  extra detail of how we describe the allowed transitions (namely,
  using pre- and post-conditions).

  In more detail, [proc_spec] states that for all ghost variables
  [a], starting states [w], and spec states [state]:

  - assume that the abstraction relation holds between [w] and [state]

  - assume that the precondition holds for [a] and [state]

  - if the procedure [p] starts from code state [w], then one of the
    following must be true:

    - (1) if execution finishes without crashes in code state [w'] and
      returns [v], then there exists a spec state [state'] in which the
      abstraction relation holds between [w'] and [state'] and the
      postcondition holds in [state'] with return value [v], OR

    - (2) if execution finishes in code state [w'] and returns [v]
      (after perhaps several crashes and running the recovery
      procedure [r] on each crash), then there exists a spec state
      [state'] and some return value [v] from the recovery procedure,
      in which the abstraction relation holds
      between [w'] and [state'] and the recovered condition holds in [state']
      with return value [v].

  The [rexec] relation describes how procedures execute, and
  is defined in [Spec.Proc].
 *)

Definition proc_spec `(spec: Specification A T R State) `(p: proc T)
           `(rec: proc R)
           `(abs: Abstraction State) :=
  forall a w state,
    abstraction abs w state ->
    pre (spec a state) ->
    forall r, rexec p rec w r ->
         match r with
         | RFinished v w' => exists state',
                            abstraction abs w' state' /\
                            post (spec a state) v state'
         | Recovered v w' => exists state',
                            abstraction abs w' state' /\
                            recovered (spec a state) v state'
         end.

(** ** Proving correctness *)

(** To help us construct proofs about procedures satisfying
  a specification, it helps to have a notion of when one
  specification implies another specification.  Here, we
  define what it means for [spec1] to imply [spec2] (the
  two specifications must be at the same level of abstraction
  and must talk about the same types of return values):

   - for all ghost variables and all states [state] for which [spec2]'s
     precondition holds,

   - there exists a ghost variable for which [spec1]'s precondition
     holds in [state]

   - for all states [state'] in which the postcondition of [spec1]
     holds, then the post condition of [spec2] also holds

   - for all states [state'] in which the recovered condition of
     [spec1] holds, then the recovered condition of [spec2] also holds.
  *)

Definition spec_impl
           `(spec1: Specification A' T R State)
           `(spec2: Specification A T R State) :=
  forall a state, pre (spec2 a state) ->
         exists a', pre (spec1 a' state) /\
               (forall v state', post (spec1 a' state) v state' ->
                        post (spec2 a state) v state') /\
               (forall rv state', recovered (spec1 a' state) rv state' ->
                         recovered (spec2 a state) rv state').

(** We now prove that the above definition of what it means for
  one specification to imply another one is actually correct.
  This means that, if a procedure satisfies [spec1], and [spec1]
  implies [spec2], then the same procedure must also satisfy [spec2].
 *)

Theorem proc_spec_weaken : forall `(spec1: Specification A T R State)
                              `(spec2: Specification A' T R State)
                              `(p: proc T) `(rec: proc R)
                              (abs: Abstraction State),
    proc_spec spec1 p rec abs ->
    spec_impl spec1 spec2 ->
    proc_spec spec2 p rec abs.
Proof.
  unfold proc_spec at 2; intros.
  eapply H0 in H2; eauto; repeat deex.
  eapply H in H3; eauto.
  destruct r; simpl in *; repeat deex; intuition eauto.
Qed.

Hint Resolve tt : core.

(** We are about to introduce machinery for constructing proofs of
    correctness by considering a procedure one step at a time.  This will
    generate multiple sub-goals for you to prove.  To help you keep track
    of where these goals are coming from, we introduce the [Marker] type.

    A [Marker] is a logical statement that's always true (it has exactly
    one constructor, [mark], that has no additional requirements), so
    formally speaking, it carries no new logical facts.  [Marker] takes two
    arguments: a string [s] and a procedure [p].  The reason the [Marker]
    is useful is that it allows the lab infrastructure to introduce [Marker]
    statements in the proof context, where the string [s] and procedure
    [p] provide a hint about what led to any particular sub-goal.
  *)

Inductive Marker (s:string) {T} (p: proc T) : Prop :=
| mark.

Hint Resolve mark : core.

(* re-state proc_spec_weaken in a more automation-friendly way *)
Theorem proc_spec_implication : forall `(spec1: Specification A T R State)
                              `(spec2: Specification A' T R State)
                              `(p: proc T) `(rec: proc R)
                              (abs: Abstraction State),
    (forall (L: Marker "using spec for" p), proc_spec spec1 p rec abs) ->
    ltac:(let x := eval red in (spec_impl spec1 spec2)
            in exact x) ->
    proc_spec spec2 p rec abs.
Proof.
  intros.
  fold (spec_impl spec1 spec2) in *.
  eapply proc_spec_weaken; eauto.
Qed.

(** This is a crucial step for constructing proofs of correctness.
  We will decompose proofs about a [Bind] operation (i.e.,
  combining two procedures, [p] and [rx], with a semicolon) into
  smaller proofs about the individual procedures [p] and [rx].

  Specifically, in order to prove that [p; rx] satisfies [spec'],
  it suffices to have some specification [spec] for [p], and to
  prove that the precondition of [spec'] implies the precondition
  of [spec], and that [rx] meets a specification that, informally,
  fixes up the postcondition of [spec] to match the postcondition
  of [spec'].

  More precisely:
 *)

Theorem proc_spec_rx : forall `(spec: Specification A T R State)
                         `(p: proc T) `(rec: proc R)
                         `(rx: T -> proc T')
                         `(spec': Specification A' T' R State)
                         `(abs: Abstraction State),
    proc_spec spec p rec abs ->
    (forall a' state, pre (spec' a' state) ->
             exists a, (forall (L: Marker "precondition" p), pre (spec a state)) /\
                  (forall r state', recovered (spec a state) r state' ->
                           forall (L: Marker "recovered condition" p),
                           recovered (spec' a' state) r state') /\
                  (forall r,
                      forall (Lexec: Marker "after" p),
                      proc_spec
                        (fun (_:unit) state' =>
                           {| pre :=
                               post (spec a state) r state';
                              post :=
                                fun r' state'' =>
                                  post (spec' a' state) r' state'';
                              recovered :=
                                fun r state'' =>
                                  recovered (spec' a' state) r state'' |})
                        (rx r) rec abs)
                  ) ->
    proc_spec spec' (Bind p rx) rec abs.
Proof.
  unfold proc_spec at 3; intros.
  inv_rexec.
  - inv_exec.
    match goal with
    | [ Hexec: exec p _ _ |- _ ] =>
      eapply RExec in Hexec
    end.
    eapply H0 in H2; repeat deex.
    eapply H in H9; simpl in *; intuition eauto.
    match goal with
    | [ Hexec: exec (rx _) _ _ |- _ ] =>
      eapply RExec in Hexec;
        eapply H4 in Hexec; eauto
    end.
  - inv_exec.
    + (* p finished, rx crashed *)
      match goal with
      | [ Hexec: exec p _ _ |- _ ] =>
        eapply RExec in Hexec
      end.
      eapply H0 in H2; repeat deex.
      eapply H in H10; simpl in *; safe_intuition (repeat deex; eauto).
      match goal with
      | [ Hexec: exec (rx _) _ _ |- _ ] =>
        eapply RExecCrash in Hexec; eauto;
          eapply H4 in Hexec; eauto
      end.
    + (* p crashed before running *)
      assert (exec p w' (Crashed w')) as Hexec by ( constructor; eauto ).
      eapply RExecCrash in Hexec; eauto.
      eapply H0 in H2; repeat deex.
      eapply H in Hexec; simpl in *; safe_intuition (repeat deex; eauto).
    + (* p crashed immediately after finishing *)
      inv_exec.
      match goal with
      | [ Hexec: exec p _ _ |- _ ] =>
        eapply RExec in Hexec
      end.
      eapply H0 in H2; repeat deex.
      eapply H in H10; simpl in *; safe_intuition (repeat deex; eauto).
      match goal with
      | [ Hexec: exec (rx _) _ _ |- _ ] =>
        apply ExecCrashEnd in Hexec;
          eapply RExecCrash in Hexec; eauto;
          eapply H4 in Hexec; eauto
      end.
    + (* p itself crashed *)
      match goal with
      | [ Hexec: exec p _ _ |- _ ] =>
        eapply RExecCrash in Hexec; eauto
      end.
      eapply H0 in H2; repeat deex.
      eapply H in H10; simpl in *; safe_intuition (repeat deex; eauto).
Qed.

(** In some situations, the precondition of a specification
  may define variables or facts that you want to [intros].
  Here we define several helper theorems and an Ltac tactic, [spec_intros],
  that does so.  This is done by changing the specification's precondition
  from an arbitrary Prop (i.e., [pre]) into a statement that there's
  some state [state0] such that [state = state0], and [intros]ing the
  arbitrary Prop in question as a hypothesis about [state0].
*)

Theorem spec_intros : forall `(spec: Specification A T R State)
                       `(p: proc T) `(rec: proc R)
                       `(abs: Abstraction State),
    (forall a state0,
        pre (spec a state0) ->
        proc_spec
          (fun (_:unit) state =>
             {| pre := state = state0;
                post :=
                  fun r state' => post (spec a state) r state';
                recovered :=
                  fun r state' => recovered (spec a state) r state';
             |}) p rec abs) ->
    proc_spec spec p rec abs.
Proof.
  unfold proc_spec at 2; intros.
  apply H in H1.
  eapply H1 in H2; eauto.
  simpl in *; eauto.
Qed.

Ltac spec_intros := intros; eapply spec_intros; intros;
                    cbn [pre post recovered] in *.

Ltac spec_case pf :=
  eapply proc_spec_weaken; [ solve [ apply pf ] |
                             unfold spec_impl ].

(** Finally, we prove that our notion of equivalent procedures,
  [exec_equiv], is actually correct: if [p] and [p'] are equivalent,
  then they meet the same specifications.

  We will use this next to reason about procedure transformations
  that shouldn't change the behavior of a procedure.
 *)

Theorem spec_exec_equiv : forall `(spec: Specification A T R State)
                            (p p': proc T) `(rec: proc R)
                            `(abs: Abstraction State),
    exec_equiv p p' ->
    proc_spec spec p' rec abs ->
    proc_spec spec p rec abs.
Proof.
  unfold proc_spec; intros.
  eapply H0; eauto.
  eapply rexec_equiv; eauto.
  symmetry; auto.
Qed.

(** ** Reasoning about the [Ret] return operation.

  The simplest procedure we can construct in our model is
  the return operation, [Ret].  Writing a specification for
  [Ret] should be intuitively straightforward, but turns out
  to be slightly complicated by the possibility of crashes.
  The [rec_wipe] definition below captures this notion: a
  [Ret v] procedure has no precondition, and has a simple
  postcondition (the state does not change and the return
  value is [v]), but in case of a crash, the state is wiped
  according to some [wipe] relation.

  [rec_wipe] is a theorem that states that [Ret v] actually
  meets this specification.  Proving [rec_wipe] will be a
  proof obligation, and boils down to showing that the recovery
  procedure [rec] corresponds to the wipe relation [wipe].
 *)

Definition rec_wipe `(rec: proc R) `(abs: Abstraction State) (wipe: State -> State -> Prop) :=
  forall T (v:T),
    proc_spec
      (fun (_:unit) state =>
         {| pre := True;
            post := fun r state' => r = v /\
                             state' = state;
            recovered := fun _ state' => wipe state state'; |})
      (Ret v) rec abs.

(** A more general theorem about specifications for [Ret], which
  we will use as part of our proof automation, says
  that [Ret v] meets a specification [spec] if the [rec_wipe]
  theorem holds (i.e., the recovery procedure is correctly
  described by a wipe relation [wipe]), and the specification
  [spec] matches the [wipe] relation:
 *)

Theorem ret_spec : forall `(abs: Abstraction State)
                     (wipe: State -> State -> Prop)
                     `(spec: Specification A T R State)
                     (v:T) (rec: proc R),
    rec_wipe rec abs wipe ->
    (forall a state, pre (spec a state) ->
            forall (Lexec: Marker "post" (Ret v)),
            post (spec a state) v state /\
            forall state', wipe state state' ->
                  forall r, recovered (spec a state) r state') ->
    proc_spec spec (Ret v) rec abs.
Proof.
  intros.
  unfold proc_spec; intros.
  eapply H in H3; simpl in *; eauto.
  eapply H0 in H2; eauto.
  destruct r; intuition eauto.
Qed.

(** ** Proof automation

  We will now define some Ltac tactics to help us prove
  the correctness of procedures.  We start with a simple
  tactic that will eliminate unnecessary [Ret] return
  statements and will re-order semicolons into a consistent
  order.

  This tactic, [monad_simpl], makes use of the [monad_left_id]
  and [monad_assoc] theorems to manipulate procedures, simplifying
  their return statements and semicolons, together with the theorem
  we proved above, [spec_exec_equiv], about specifications of
  equivalent procedures.
 *)

Ltac monad_simpl :=
  repeat match goal with
         | |- proc_spec _ (Bind (Ret _) _) _ _ =>
           eapply spec_exec_equiv; [ apply monad_left_id | ]
         | |- proc_spec _ (Bind (Bind _ _) _) _ _ =>
           eapply spec_exec_equiv; [ apply monad_assoc | ]
         end.

(** ** step_proc

  To simplify proofs, we automate reasoning about [proc_spec].
  Consider a proof for a [proc_spec] about "a ; b". What do
  we need to prove?

<<
      pre                             post
       |                               |
       V                               V
     state0 --[a]--> state1 --[b]--> state2
>>

  We need to find a [proc_spec] for [a] and line up our precondition with
  that spec's, then reduce to proving a [proc_spec] for b, with [a]'s post
  as the new pre.  Keep doing this repeatedly.

  There are two requirements to make this plan work:
    - a [proc_spec] for the [a] procedure
    - a way to line up our current state's precondition with
      [a]'s [proc_spec] precondition

  The following Ltac, [step_proc], implements this plan.
  It compares Coq's current goal to:

  - a [proc_spec] with a procedure that invokes a [Ret] operation:
    if so, apply the [ret_spec] theorem to consume the [Ret].  This
    will generate some proof obligations, corresponding to the premises
    of the [ret_spec] theorem.

  - a [proc_spec] with a procedure that sequences two operations [a] and [b]
    (with [Bind]): if so, apply the [proc_spec_rx] theorem to consume the
    [Bind].  This will generate some proof obligations, corresponding to
    the premises of the [proc_spec_rx] theorem.

    A common pattern is that we have already proven that [a] already meets
    some specification.  To automate this case, [step_proc] calls [eauto]
    to find such a theorem.  We tell Coq about these theorems using
    [Hint Resolve] statements that you will see throughout our lab code.

    Proving the correctness of the [b] procedure will remain as a proof
    obligation.

  - a [proc_spec] that is implied by a [proc_spec] that is already in
    context: if so, apply the [proc_spec_weaken] theorem and try to
    prove that one spec implies the other.
 *)

Ltac step_proc_basic :=
  intros;
  monad_simpl;
  match goal with
  | |- proc_spec _ (Ret _) _ _ =>
    eapply ret_spec
  | |- proc_spec _ _ _ _ =>
    eapply proc_spec_implication; [ solve [eauto] | ]
  | |- proc_spec _ _ _ _ =>
    eapply proc_spec_rx; [ solve [ eauto ] | ]
  end;
  cbn [pre post recovered] in *.

Ltac simplify :=
  simpl;
  repeat match goal with
         | [ H: _ /\ _ |- _ ] => destruct H
         | [ |- forall _, _ ] => intros
         | [ |- rec_wipe _ _ _ ] => solve [ eauto ]
         | [ |- exists (_:unit), _ ] => exists tt
         | [ H: pre ((match ?a with
                      | (x, y) => _
                      end) _) |- _ ] =>
           let x := fresh x in
           let y := fresh y in
           destruct a as [x y];
           cbn [pre post recovered] in *
         | _ => progress subst
         | _ => progress autounfold in *
         | |- _ /\ _ => split
         end.

Ltac split_all :=
  repeat match goal with
         | |- _ /\ _ => split
         end.

Ltac finish :=
  repeat match goal with
         | _ => solve [ trivial ]
         end.

Ltac step_proc :=
  step_proc_basic; simplify; finish.

(** ** Initialization

  Initialization is special because, when the initialization
  procedure starts running, the system may be in a
  state that does not correspond to ANY abstract state yet.
  This means that we will need to write a stylized kind of
  specification about initialization procedures.

  As a common pattern, initialization can succeed or fail.
  If it fails, we typically do not promise anything.
 *)

Inductive InitResult :=
| Initialized
| InitFailed.

(** When we compose multiple layers together, a common pattern
  that emerges is trying to initialize the lower level first,
  and then initializing the higher level.  The reason we don't
  just combine the procedures using semicolon (i.e., [Bind])
  is that if the lower-level initialization fails, we should
  return failure right away, instead of continuing to run the
  higher-level initialization.
 *)

Definition then_init (init1 init2: proc InitResult) : proc InitResult :=
  r <- init1;
  match r with
  | Initialized => init2
  | Failed => Ret Failed
  end.

(** ** Initialization specs

  To specify what it means for the initialization procedure to
  be correct, it suffices to simply write a predicate describing
  the initialized states that will be produced by the initialization
  procedure.  A common description of these states is "any state
  that satisfies the abstraction relation", which we can define
  using [inited_any]:
 *)

Definition inited_any `(s : State) : Prop := True.

(** We define this shorthand for the specification of an initialization
  procedure.  Given a description of the states that initialization
  should produce (e.g., [inited_any] above), [init_abstraction] produces
  a full-fledged pre- and post-condition-style specification, which
  says that, if initialization returns success, the resulting state
  is one of the allowed states:
 *)

Definition init_abstraction
           (init: proc InitResult) (rec: proc unit)
           `(abs: Abstraction State) (init_sem: State -> Prop) :=
  proc_spec
    (fun (_:unit) w =>
       {| pre := True;
          post :=
            fun r w' => match r with
                     | Initialized =>
                       exists state, abstraction abs w' state /\ init_sem state
                     | InitFailed => True
                     end;
          recovered :=
            fun _ w' => True;
       |}) init rec (IdAbstraction world).

(** Since the [init_abstraction] specification above does not
  place any requirements in case we crash during initialization,
  the specific recovery procedure doesn't matter:
 *)

Theorem init_abstraction_any_rec : forall (init: proc InitResult)
                                   (rec rec': proc unit)
                                   `(abs: Abstraction State)
                                   (init_sem: State -> Prop),
    init_abstraction init rec abs init_sem ->
    init_abstraction init rec' abs init_sem.
Proof.
  unfold init_abstraction, proc_spec; simpl; intros.
  destruct matches; subst; eauto.
  eapply rexec_finish_any_rec in H2.
  eapply H in H2; eauto.
Qed.

(** Finally, we prove a specialized theorem about how to compose
  two initialization procedures using the [then_init] composition
  operator defined above:
 *)

Theorem then_init_compose : forall (init1 init2: proc InitResult)
                              (rec rec': proc unit)
                              `(abs1: Abstraction State1)
                              `(abs2: LayerAbstraction State1 State2)
                              (init1_sem: State1 -> Prop)
                              (init2_sem: State2 -> Prop),
    init_abstraction init1 rec abs1 init1_sem ->
    proc_spec
      (fun (_:unit) state =>
         {| pre := init1_sem state;
            post :=
              fun r state' => match r with
                       | Initialized =>
                         exists state'', abstraction abs2 state' state'' /\ init2_sem state''
                       | InitFailed => True
                       end;
            recovered :=
              fun _ state' => True; |}) init2 rec abs1 ->
    init_abstraction (then_init init1 init2) rec' (abstraction_compose abs1 abs2) init2_sem.
Proof.
  intros.
  eapply init_abstraction_any_rec with rec.
  unfold init_abstraction; intros.
  step_proc; intuition; simpl in *.
  descend; intuition eauto.
  destruct r.
  - clear H.
    unfold proc_spec in *; intuition; simpl in *; intuition eauto.
    eapply H0 in H2; eauto.
    destruct matches in *; safe_intuition (repeat deex; eauto).
    descend; intuition eauto.
  - unfold proc_spec; simpl; intros.
    destruct matches; subst; eauto.
    eexists; intuition eauto.
    inv_rexec; inv_exec.
    congruence.
Qed.

(** This theorem allows converting between abstraction layers:
 to prove the correctness of procedure [p] at a higher level of
 abstraction, it suffices to drop down to the lower level of
 abstraction, and prove that there exists a connection to the
 higher level in the postcondition. *)

Theorem spec_abstraction_compose :
  forall `(spec: Specification A T R State2)
    `(p: proc T) `(rec: proc R)
    `(abs2: LayerAbstraction State1 State2)
    `(abs1: Abstraction State1),
    proc_spec
      (fun '(a, state2) state =>
         {| pre := pre (spec a state2) /\
                   abstraction abs2 state state2;
            post :=
              fun v state' =>
                exists state2',
                  post (spec a state2) v state2' /\
                  abstraction abs2 state' state2';
            recovered :=
              fun v state' =>
                exists state2',
                  recovered (spec a state2) v state2' /\
                  abstraction abs2 state' state2'; |}) p rec abs1 ->
    proc_spec spec p rec (abstraction_compose abs1 abs2).
Proof.
  intros.
  unfold proc_spec, abstraction_compose;
    simpl; intros; safe_intuition (repeat deex).
  eapply (H (a, state)) in H2; simpl in *; eauto.
  destruct r; intuition (repeat deex; eauto).
Qed.
