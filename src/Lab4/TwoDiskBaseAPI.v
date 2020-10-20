Require Import POCS.

(**
TwoDiskBaseAPI supports reading and writing to two disks. It also allows one
disk to fail at any time (just before any operation). Note that disk failure is
separate from procedure crashes: procedures can still crash and recover. In this
model, there is no way to recover from a disk failure (that is, we have a
fail-stop model).

We provide a more convenient set of specifications (for the same operations) in
TwoDiskAPI.
*)

Inductive diskId :=
| d0
| d1.

Inductive DiskResult T :=
| Working (v:T)
| Failed.

Arguments Failed {T}.

Inductive State :=
| BothDisks (d_0:disk) (d_1:disk)
| OnlyDisk0 (d_0:disk)
| OnlyDisk1 (d_1:disk).

Definition disk0 (state:State) : option disk :=
  match state with
  | BothDisks d_0 _ => Some d_0
  | OnlyDisk0 d => Some d
  | OnlyDisk1 _ => None
  end.

Definition disk1 (state:State) : option disk :=
  match state with
  | BothDisks _ d_1 => Some d_1
  | OnlyDisk0 _ => None
  | OnlyDisk1 d => Some d
  end.

Definition get_disk (i:diskId) (state:State) : option disk :=
  match i with
  | d0 => disk0 state
  | d1 => disk1 state
  end.

Definition set_disk (i:diskId) (state:State) (d:disk) : State :=
  match i with
  | d0 => match state with
         | BothDisks _ d_1 => BothDisks d d_1
         | OnlyDisk0 _ => OnlyDisk0 d
         | OnlyDisk1 d_1 => BothDisks d d_1
         end
  | d1 => match state with
         | BothDisks d_0 _ => BothDisks d_0 d
         | OnlyDisk0 d_0 => BothDisks d_0 d
         | OnlyDisk1 _ => OnlyDisk1 d
         end
  end.

Inductive Op : Type -> Type :=
| op_read (i : diskId) (a : addr) : Op (DiskResult block)
| op_write (i : diskId) (a : addr) (b : block) : Op (DiskResult unit)
| op_size (i : diskId) : Op (DiskResult nat).

Inductive op_step : forall `(op: Op T), Semantics State T :=
| step_read : forall a i r state,
    match get_disk i state with
    | Some d => match diskGet d a with
               | Some b0 => r = Working b0
               | None => exists b, r = Working b
               end
    | None => r = Failed
    end ->
    op_step (op_read i a) state r state
| step_write : forall a i b state r state',
    match get_disk i state with
    | Some d => state' = set_disk i state (diskUpd d a b) /\
               r = Working tt
    | None => r = Failed /\ state' = state
    end ->
    op_step (op_write i a b) state r state'
| step_size : forall i state r,
    match get_disk i state with
    | Some d => r = Working (diskSize d)
    | None => r = Failed
    end ->
    op_step (op_size i) state r state.

Inductive bg_failure : State -> State -> Prop :=
| step_id : forall (state: State), bg_failure state state
| step_fail0 : forall d_0 d_1,
    bg_failure (BothDisks d_0 d_1) (OnlyDisk1 d_1)
| step_fail1 : forall d_0 d_1,
    bg_failure (BothDisks d_0 d_1) (OnlyDisk0 d_0).

Definition combined_step := pre_step bg_failure (@op_step).


Module Type TwoDiskBaseAPI.

  Axiom init : proc InitResult.
  Axiom read : diskId -> addr -> proc (DiskResult block).
  Axiom write : diskId -> addr -> block -> proc (DiskResult unit).
  Axiom size : diskId -> proc (DiskResult nat).
  Axiom recover : proc unit.

  Axiom abstr : Abstraction State.

  Axiom init_ok : init_abstraction init recover abstr inited_any.
  Axiom read_ok : forall i a, proc_spec (op_spec (combined_step (op_read i a))) (read i a) recover abstr.
  Axiom write_ok : forall i a b, proc_spec (op_spec (combined_step (op_write i a b))) (write i a b) recover abstr.
  Axiom size_ok : forall i, proc_spec (op_spec (combined_step (op_size i))) (size i) recover abstr.
  Axiom recover_wipe : rec_wipe recover abstr no_wipe.

  Hint Resolve init_ok : core.
  Hint Resolve read_ok : core.
  Hint Resolve write_ok : core.
  Hint Resolve size_ok : core.
  Hint Resolve recover_wipe : core.

End TwoDiskBaseAPI.
