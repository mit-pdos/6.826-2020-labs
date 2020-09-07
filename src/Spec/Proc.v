Global Set Implicit Arguments.
Global Generalizable All Variables.
(* turn this on to enforce strict bulleting and braces (every tactic must apply
to a single goal) *)
Global Set Default Goal Selector "!".
Global Set Default Proof Using "Type".

(** * Model of sequential procedures with mutable state.

    In our labs, we want to reason about procedures that have side-effects,
    such as modifying the contents of memory or writing to disk.  This is
    in contrast to the kinds of procedures that one can naturally write in
    Coq's Gallina language, which are purely functional; they have no
    built-in notion of mutable state.

    To reason about procedures that manipulate mutable state,
    we need to construct an explicit Coq model of:

    - What a procedure looks like.
    - How a procedure executes.

    Our procedures will eventually be extracted from Coq into Haskell, and
    execute as Haskell programs (by compiling their Coq-generated Haskell
    source code using a Haskell compiler to produce an executable binary).

    First, we need a type to represent procedures, which will be an inductive type
    [proc] after some preliminaries. This type is a generic model of sequential
    procedures, allowing chaining procedures together. We will implement some basic
    operations in Haskell to do I/O where needed and, using extraction, link our procedures with the
    Haskell primitives and run them.

  *)

(** At the lowest level, operations are implemented in terms of some machine
    primitives that we don't directly model. We group together the assumptions
    related to these primitives here, so that we can assume them in one go.

    Alluding to the Haskell IO monad, which is where our procedures actually
    run, we call this model [IO.Model].
*)
Module IO.
  Inductive Model :=
    { baseOpT : Type -> Type;
      world : Type;
      world_crash : world -> world;
      base_step: forall T, baseOpT T -> world -> T -> world -> Prop;
    }.
End IO.

Axiom baseModel : IO.Model.

(** As a technical detail, we let procedures include arbitrary operations of types
    [baseOpT T] (which will produce a T-typed result). These will tell Coq that
    a [proc] can contain outside code that we don't care to represent here.
  *)

Definition baseOpT : Type -> Type := IO.baseOpT baseModel.

(** Our minimal, generic model of sequential procedures.

    The only detail we expose about our opaque procedures is that it's possible
    to combine procedures together, using [Ret] and [Bind]. If you're familiar
    with Haskell, these are the same as [return] and [(>>=)] for the [IO] monad.

    Procedures are parametrized by type [T], which is the type of value
    that will be returned by the procedure.  For example, a procedure
    that returns a [nat] has type [proc nat], and a procedure that returns
    nothing ("void", in C terminology) has type [proc unit].

    As a technical detail, we include a constructor [BaseOp] to include
    arbitrary external operations. Without this constructor, Coq would think
    that every [proc] consists only of [Ret] and [Bind] and thus can't have side
    effects.
  *)

CoInductive proc (T : Type) : Type :=
| BaseOp (op : baseOpT T)
| Ret (v : T)
| Bind (T1 : Type) (p1 : proc T1) (p2 : T1 -> proc T).

(** Here we connect our definition of the procedure language, [proc],
    to Haskell's built-in implementations of [Bind] and [Ret], which are
    [return] and [(>>=)] respectively.  We instruct Coq to extract any
    use of [BaseOp] to an error expression, since we do not expect any
    legitimate use of [BaseOp] in Gallina.  We also instruct Coq to
    extract any attempts to pattern-match a procedure to an error, since
    we do not expect any legitimate code to pattern-match the contents of
    a [proc] procedure.
  *)

Require Extraction.
Extraction Language Haskell.

Extract Inductive proc => "Proc"
                           ["error 'accessing BaseOp'" "return" "(>>=)"]
                           "(\fprim fret fbind -> error 'pattern match on proc')".


(** * Execution model.

    Next, we define our model of execution.

    The model will specify how Bind chains operations together. Importantly, our
    semantics will allow a [proc] to execute to a crashed state at any any
    intermediate point in its execution. Later we'll also bring recovery
    execution into this picture.

  *)

(** When we define how procedures execute, we will say they manipulate some state
    of this opaque type [world]. We won't ever define this type in Coq, but it will
    show up later to capture the idea that procedures move from one world state to
    another in sequence.

 *)

Definition world : Type := IO.world baseModel.


(** We start by defining the possible outcomes of executing a procedure [proc
    T]: either the procedure finishes and returns something of type T, or the
    procedure crashes. Because we are explicitly modeling the effect of
    procedures on the state of our system, both of these outcomes also include
    the resulting world state.
*)

Inductive Result T :=
| Finished (v:T) (w:world)
| Crashed (w:world).

Arguments Crashed {T} w.

(** To define the execution of procedures, we need to state an axiom about how our
    opaque [baseOpT] primitives execute. This axiom is [base_step]. This is
    just another technicality.
  *)

Definition base_step : forall T, baseOpT T -> world -> T -> world -> Prop :=
  IO.base_step baseModel.

(** Finally, we define the [exec] relation to represent the execution semantics
    of a procedure, leveraging the [step] and [world_crash] definitions from
    above. The interpretation is that when [exec p w r] holds, procedure [p]
    when executed in state [w] can end up with the result [r]. Recall that the
    [Result T] type always includes the final world state, and includes a return
    value of type [T] if the execution finishes successfully without crashing.
  *)

Inductive exec : forall T, proc T -> world -> Result T -> Prop :=

(** There are three interesting aspects of this definition:

    - First, it defines how [Bind] and [Ret] work, in the [ExecRet]
      and [ExecBindFinished] constructors.
  *)

| ExecRet : forall T (v:T) w,
    exec (Ret v) w (Finished v w)
| ExecBindFinished : forall T T' (p: proc T) (p': T -> proc T')
                       w v w' r,
    exec p w (Finished v w') ->
    exec (p' v) w' r ->
    exec (Bind p p') w r

(** - Second, it incorporates the opaque way base operations step.
  *)

| ExecOp : forall T (op: baseOpT T) w v w',
    base_step op w v w' ->
    exec (BaseOp _ op) w (Finished v w')

(** - And finally, it defines how procedures can crash.  Any procedure
      can crash just before it starts running or just after it finishes.
      [Bind] can crash in the middle of running the first sub-procedure.
      Crashes during the second sub-procedure of a [Bind] are covered by
      the [ExecBindFinished] constructor above.
  *)

| ExecCrashBegin : forall T (p: proc T) w,
    exec p w (Crashed w)
| ExecCrashEnd : forall T (p: proc T) w v w',
    exec p w (Finished v w') ->
    exec p w (Crashed w')
| ExecBindCrashed : forall T T' (p: proc T) (p': T -> proc T')
                      w w',
    exec p w (Crashed w') ->
    exec (Bind p p') w (Crashed w').


(** * Execution model with recovery

    We also define a model of how our system executes procedures in the
    presence of recovery after a crash.  What we want to model is a system
    that, after a crash, reboots and starts running some recovery procedure
    (like [fsck] in a Unix system to fix up the state of a file system).
    If the system crashes again while running the recovery procedure, it
    starts running the same recovery procedure again after reboot.

  *)

(** When we talk about recovery, we need to capture one more property of
    crashes. Above, a crash just stops execution. In practice, however, some
    parts of the state are volatile and are lost after a crash, such as memory
    contents or disk write buffers. Our model is that, on a crash, the world
    state is modified according to the opaque [world_crash] function, which we
    define as an axiom. This relation is meant to capture the computer losing
    volatile state, such as memory contents or disk write buffers.
 *)

Definition world_crash : world -> world := IO.world_crash baseModel.

(** Before we talk about the whole execution, we first just model executing the
    recovery procedure, including repeated attempts in the case of a crash
    during recovery. [exec_recover rec w rv w'] means the procedure [rec] can
    execute from [w] to [w'], ultimately returning [rv] (a "recovery value"),
    and possibly crashing and restarting multiple times along the way.
  *)

Inductive exec_recover R (rec:proc R) (w:world) : R -> world -> Prop :=

(** The first constructor, [ExecRecoverExec], says that if the recovery
    procedure [rec] executes and finishes normally, then that's a possible
    outcome for [exec_recover].
  *)

| ExecRecoverExec : forall v w',
    exec rec w (Finished v w') ->
    exec_recover rec w v w'

(** The second constructor, [ExecRecoverCrashDuringRecovery], allows repeated
    crashes by referring to [exec_recover] recursively. In between crashes, the
    world state is transformed according to [world_crash].
  *)

| ExecRecoverCrashDuringRecovery : forall w' v w'',
    exec rec w (Crashed w') ->
    exec_recover rec (world_crash w') v w'' ->
    exec_recover rec w v w''.

(** * Chaining normal execution with recovery *)

(** [RResult] ("recovery result") is the outcome of running a procedure with
    recovery. It is similar to the [Result] type defined above, except that in
    the case of a crash, we run a recovery procedure and get both a final state
    _and_ a return value from the recovery procedure.
*)
Inductive RResult T R :=
| RFinished (v:T) (w:world)
| Recovered (v:R) (w:world).

Arguments RFinished {T R} v w.
Arguments Recovered {T R} v w.

(** Finally, [rexec] defines what it means to run a procedure and use
    some recovery procedure on crashes, including crashes during recovery.
    [rexec] says that:

    - either the original procedure [p] finishes and returns a [RFinished]
      outcome, or
    - [p] crashes, and after running the recovery procedure [rec] one or
      more times, the system eventually stops crashing, [rec] finishes,
      and produces a [Recovered] outcome.

    Note that there is no recursion in this definition; it merely combines
    normal execution with crash execution followed by recovery execution, each
    of which is defined above.
  *)

Inductive rexec T R : proc T -> proc R -> world -> RResult T R -> Prop :=
| RExec : forall (p:proc T) (rec:proc R) w v w',
    exec p w (Finished v w') ->
    rexec p rec w (RFinished v w')
| RExecCrash : forall (p:proc T) (rec:proc R) w w' rv w'',
    exec p w (Crashed w') ->
    exec_recover rec (world_crash w') rv w'' ->
    rexec p rec w (Recovered rv w'').

(** * Notation for composing procedures.

    To help us write procedures in our [proc] language, we define the
    following Haskell-like notation for [Bind].  This allows us to say:

      [[
      x <- firstProcedure;
      secondProcedure (x+1)
      ]]

    to assign the result of [firstProcedure] to [x], and then use [x]
    in an argument to [secondProcedure].  We can even use [x] inside of
    a Gallina expression before passing it to [secondProcedure], such as
    adding 1 in the example above.

    This notation does not permit silently discarding the return value of the
    first procedure. In order to run two procedures where the first one returns
    nothing (e.g., [unit]), or we want to otherwise ignore the result of the
    first procedure, we have to explicitly discard the return value by writing:

      [[
      _ <- firstProcedure;
      secondProcedure
      ]]
  *)

Notation "x <- p1 ; p2" := (Bind p1 (fun x => p2))
                            (at level 60, right associativity).

Arguments Ret {T} v.
