Require Import POCS.


(** * Logging API *)

(** This file defines the desired API for an append-only durable log.
    A log like the one defined here is widely used in storage systems,
    such as a file system or a database, to make atomic crash-safe
    updates.  In this lab, you will implement and prove correct the
    log itself, though the lab does not involve building anything on
    top of this log (like a file system).
  *)

(** Logically, the state of the log is a list of blocks: *)
Definition State : Type := list block.

(** The log provides three operations: [get], [append], and [reset].
    The [get] retrieves all of the blocks currently in the log: *)
Definition get_spec : Specification unit (list block) unit State :=
  fun (_ : unit) state => {|
    pre := True;
    post := fun r state' => r = state /\ state' = state;
    recovered := fun _ state' => state' = state
  |}.

(** [append] adds blocks to the log.  The [append] is the most interesting
    part of the log, because [append] must be atomic with respect to crashes.
    That means that, if the system crashes in the middle of an [append],
    either all of the blocks should be present (i.e., returned by [get]),
    or none of them should be present.

    [append] returns a boolean to indicate whether it succeeded
    or not.  The intent is that [append] might fail if the log
    has grown too big on disk, and there's no room for the new
    blocks. *)
Definition append_spec v : Specification unit bool unit State :=
  fun (_ : unit) state => {|
    pre := True;
    post := fun r state' => r = true /\ state' = state ++ v \/
                            r = false /\ state' = state;
    recovered := fun _ state' => state' = state \/ state' = state ++ v
  |}.

(** Finally, [reset] logically clears the log, removing all entries.  This
    also must be crash-safe: if the system crashes in the middle of clearing
    the log, either the log contents should still be there, or the log should
    appear to be empty (according to [get]).
  *)
Definition reset_spec : Specification unit unit unit State :=
  fun (_ : unit) state => {|
    pre := True;
    post := fun r state' => r = tt /\ state' = nil;
    recovered := fun _ state' => state' = state \/ state' = nil
  |}.


Module Type LogAPI.

  Axiom init : proc InitResult.
  Axiom get : proc (list block).
  Axiom append : list block -> proc bool.
  Axiom reset : proc unit.
  Axiom recover : proc unit.

  Axiom abstr : Abstraction State.

  Axiom init_ok : init_abstraction init recover abstr inited_any.
  Axiom get_ok : proc_spec get_spec get recover abstr.
  Axiom append_ok : forall v, proc_spec (append_spec v) (append v) recover abstr.
  Axiom reset_ok : proc_spec reset_spec reset recover abstr.
  Axiom recover_wipe : rec_wipe recover abstr no_wipe.

  Hint Resolve init_ok : core.
  Hint Resolve get_ok : core.
  Hint Resolve append_ok : core.
  Hint Resolve reset_ok : core.
  Hint Resolve recover_wipe : core.

End LogAPI.
