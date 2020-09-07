Require Import POCS.

(** * Specification for StatDB

    An implementation of StatDB will have to prove that its implementation meets
    the specification stated in this file.  The specification for StatDB
    contains three parts:

    - The state of the StatDB: a list of integers

    - An initial state: the list of integers is nil

    - Two operations: add and mean. The specification for each operation is
    stated in terms of a precondition and a postcondition.  (Each operation also
    has a recovered condition, but we will ignore crash conditions in this lab.)

*)



(** ** The state of StatDB

  We will often refer to the abstract state the specification refers to as the
  "spec state".
 *)

Definition State := list nat.

(** ** The initial value of the spec state:
 *)

Definition inited (s : State) : Prop :=
  s = nil.

(** ** The specification of the StatDB operations

  The specifications are of type [Specification], which is defined in
  [POCS.Spec.Abstraction]. A specification is a record with 3 fields: [pre],
  [post], and [recovered] (which we will ignore in this lab). For both
  operations the precondition is just [True] (i.e., we prove the postconditions in
  any initial state). The postconditions describe the effects of the operations
  [add] and [mean]:

  - [add_spec]'s post condition states that [add v] adds [v] to the spec state
    of StatDB and that [add] returns [tt].

  - [mean_spec]'s post condition states that [mean] doesn't modify the spec
    state of StatDB, and that its return value is one of two values: (1) if
    state is [nil], then the return value is [None]; (2) if state is not [nil],
    then the return value is the average of the numbers in StatDB's state.

 *)

Definition add_spec v : Specification unit unit unit State :=
  fun (_ : unit) state => {|
    pre := True;
    post := fun r state' =>
      r = tt /\ state' = v :: state;
    recovered := fun _ _ => False
  |}.

Definition mean_spec : Specification unit (option nat) unit State :=
  fun (_ : unit) state => {|
    pre := True;
    post := fun r state' =>
      state' = state /\
      (state = nil /\ r = None \/
       state <> nil /\ r = Some (fold_right plus 0 state / length state));
    recovered := fun _ _ => False
  |}.


(** * StatDB module

   An implementation of StatDB is a Coq Module that implements the StatDbAPI
   module type. The implementation must provide code for [init], [add], [mean],
   and [recovery] (which will be a NOOP). In addition, the module must provide
   proofs showing, for example, that its implementation for [add] meets the
   [add_spec]. The proof approach POCS uses is based on refinement. This
   approach requires the implementation to define [abstr], which abstracts the
   code state to the spec state (the list of integers that StatDB maintains).
   [abstr] is of type [Spec.Abstraction.Abstraction].

*)


Module Type StatDbAPI.

  (** The implementation must provide the following methods: *)
  Axiom init : proc InitResult.
  Axiom add : nat -> proc unit.
  Axiom mean : proc (option nat).
  Axiom recover : proc unit.

  (** The abstraction relation between spec and code state *)
  Axiom abstr : Abstraction State.

  (** The proofs that the implementation methods meet their specs: *)
  Axiom init_ok : init_abstraction init recover abstr inited.
  Axiom add_ok : forall v, proc_spec (add_spec v) (add v) recover abstr.
  Axiom mean_ok : proc_spec mean_spec mean recover abstr.
  Axiom recover_wipe : rec_wipe recover abstr no_crash.

  (** Hints to proof automation to apply the following proofs when "stepping"
  through a procedure: e.g., if Coq has a [add] goal, it will try to apply
  [add_ok] to resolve that goal. The implementation doesn't have to be concerned
  with these hints. *)
  Hint Resolve init_ok : core.
  Hint Resolve add_ok : core.
  Hint Resolve mean_ok : core.
  Hint Resolve recover_wipe : core.

End StatDbAPI.
