Require Import POCS.

(** * Specification of Variables.

    This layer describes mutable variables.  In this lab assignment,
    we will be assuming that this layer is already provided for us,
    and that its implementation meets its specification.  Your job
    will be to familiarize yourself with the lab infrastructure by
    writing procedures, specifications, and proofs for code on top
    of these mutable variables.
 *)

(** There are three variables, which we will call [x], [y], and [z].
    To refer to a particular variable name, we use this type.
  *)
Inductive var :=
| VarX
| VarY
| VarZ.

Instance var_eq : EqualDec var.
Proof.
  hnf.
  destruct x, y; simpl;
    (left; congruence) || (right; congruence).
Defined.

(** The values of these variables are the spec state: *)
Record State := mkState {
  StateX : nat;
  StateY : nat;
  StateZ : nat;
}.

(** [StateVar] extracts a particular variable by its [var] name
    from a [State].
  *)
Definition StateVar (v:var) (state:State) : nat :=
  match v with
  | VarX => StateX state
  | VarY => StateY state
  | VarZ => StateZ state
  end.

(** * Operations on variables.

    We provide two operations for dealing with variables:
    reading a variable and writing a value to a variable.

    To meaningfully write code on top of these variables,
    it's important to know what reading and writing a variable
    does.  We will capture this with the following specifications.
  *)

(** The specification for reading a variable, [read_spec], is
    parametrized by the variable that we are reading, [v].
  *)

Definition read_spec v : Specification _ _ unit _ :=
  fun (_ : unit) state => {|

(** The precondition is [True], reflecting the fact that it's
    always OK to read any variable [v]. *)
    pre := True;

(** The postcondition has two parts to it.  First, it says
    that the resulting state after reading a variable, [state'],
    is the same as the state before reading the variable, [state].
    In other words, reading a variable doesn't change the state. *)
    post := fun r state' =>
            state' = state /\

(** The second part of the postcondition says that the return
    value [r] is the value of the variable [v] in the [state]. *)
            r = StateVar v state;

(** Since our framework supports reasoning about crashes, we must
    supply a recovered condition, but here we will ignore crashes
    by saying that recovery can never occur, by stating [False]. *)
    recovered := fun _ _ => False
  |}.

(** The specification for writing a variable, [write_spec] is
    parametrized by two things: the variable being modified, [v],
    and the value being written to that variable, [val].
    The precondition and recovery condition are the same as for
    reading ([True] and [False] respectively).
  *)
Definition write_spec v val : Specification _ _ unit _ :=
  fun (_ : unit) state => {|
    pre := True;

(** The postcondition says that the return value is always equal
    to [tt] (a way of representing a procedure that has no return
    value), and *)
    post := fun r state' =>
      r = tt /\

(** the new state, [state'], is updated based on which variable
    we were trying to modify. *)
      match v with
      | VarX => state' = mkState val (StateY state) (StateZ state)
      | VarY => state' = mkState (StateX state) val (StateZ state)
      | VarZ => state' = mkState (StateX state) (StateY state) val
      end;
    recovered := fun _ _ => False
  |}.

(** * Variables module

    An implementation of variables must implement the following module type and
    must prove that that its code implements the spec correctly using refinement.

    If we were to implement this module in Haskell, we would provide Haskell code
    for [read] and [write], and ensure that this code meets the required specification.

    For this lab assignment, we will simply assume that such an implementation exists,
    and focus on writing code, specs, and proofs in the lab infrastructure.

    In the next lab assignment, you will use a similar variables layer that supports
    extraction to Haskell, and allows you to really run your programs.
  *)

Module Type VarsAPI.

  Axiom init : proc InitResult.
  Axiom read : var -> proc nat.
  Axiom write : var -> nat -> proc unit.
  Axiom recover : proc unit.

  Axiom abstr : Abstraction State.

  Axiom init_ok : init_abstraction init recover abstr inited_any.
  Axiom read_ok : forall v, proc_spec (read_spec v) (read v) recover abstr.
  Axiom write_ok : forall v val, proc_spec (write_spec v val) (write v val) recover abstr.
  Axiom recover_wipe : rec_wipe recover abstr no_crash.

  Hint Resolve init_ok : core.
  Hint Resolve read_ok : core.
  Hint Resolve write_ok : core.
  Hint Resolve recover_wipe : core.

End VarsAPI.
