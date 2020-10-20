Require Import POCS.
Require Export TwoDiskBaseAPI.

(**
TwoDiskAPI supports reading and writing to two disks, with the possibility for a
disk to fail at any time. This layer provides easier-to-use specifications
written in terms of [maybe_holds] (the ?|= notation). The fact that at least one
disk is always functioning is encoded in the inductive type [TwoDiskBaseAPI.State]
itself; it has only three cases, for both disks, only disk 0, and only disk 1.
*)

Definition two_disks_are (s : State) (p0 : disk -> Prop) (p1 : disk -> Prop) :=
  get_disk d0 s ?|= p0 /\
  get_disk d1 s ?|= p1.

Definition read0_spec (a : addr) : Specification _ _ unit _ :=
  fun '(d, F) state => {|
    pre := two_disks_are state (eq d) F;
    post := fun r state' =>
      match r with
      | Working v => two_disks_are state' (eq d) F /\
                     diskGet d a ?|= eq v
      | Failed    => two_disks_are state' missing F
      end;
    recovered := fun _ state' => two_disks_are state' (eq d) F;
  |}.

Definition read1_spec (a : addr) : Specification _ _ unit _ :=
  fun '(d, F) state => {|
    pre := two_disks_are state F (eq d);
    post := fun r state' =>
      match r with
      | Working v => two_disks_are state' F (eq d) /\
                     diskGet d a ?|= eq v
      | Failed    => two_disks_are state' F missing
      end;
    recovered := fun _ state' => two_disks_are state' F (eq d);
  |}.

Definition write0_spec (a : addr) (b : block) : Specification _ (DiskResult unit) unit _ :=
  fun '(d, F) state => {|
    pre := two_disks_are state (eq d) F;
    post := fun r state' =>
      match r with
      | Working _ => two_disks_are state' (eq (diskUpd d a b)) F
      | Failed    => two_disks_are state' missing F
      end;
    recovered := fun _ state' =>
      (two_disks_are state' (eq (diskUpd d a b)) F /\ a < diskSize d) \/
      two_disks_are state' (eq d) F;
  |}.

Definition write1_spec (a : addr) (b : block) : Specification _ (DiskResult unit) unit _ :=
  fun '(d, F) state => {|
    pre := two_disks_are state F (eq d);
    post := fun r state' =>
      match r with
      | Working _ => two_disks_are state' F (eq (diskUpd d a b))
      | Failed    => two_disks_are state' F missing
      end;
    recovered := fun _ state' =>
      (two_disks_are state' F (eq (diskUpd d a b)) /\ a < diskSize d) \/
      two_disks_are state' F (eq d);
  |}.

Definition size0_spec : Specification _ _ unit _ :=
  fun '(d, F) state => {|
    pre := two_disks_are state (eq d) F;
    post := fun r state' =>
      match r with
      | Working n => two_disks_are state' (eq d) F /\ n = diskSize d
      | Failed    => two_disks_are state' missing F
      end;
    recovered := fun _ state' => two_disks_are state' (eq d) F;
  |}.

Definition size1_spec : Specification _ _ unit _ :=
  fun '(d, F) state => {|
    pre := two_disks_are state F (eq d);
    post := fun r state' =>
      match r with
      | Working n => two_disks_are state' F (eq d) /\ n = diskSize d
      | Failed    => two_disks_are state' F missing
      end;
    recovered := fun _ state' => two_disks_are state' F (eq d);
  |}.


Module Type TwoDiskAPI.

  Axiom init : proc InitResult.
  Axiom read : diskId -> addr -> proc (DiskResult block).
  Axiom write : diskId -> addr -> block -> proc (DiskResult unit).
  Axiom size : diskId -> proc (DiskResult nat).
  Axiom recover : proc unit.

  Axiom abstr : Abstraction State.

  Axiom init_ok : init_abstraction init recover abstr inited_any.
  Axiom read0_ok : forall a, proc_spec (read0_spec a) (read d0 a) recover abstr.
  Axiom read1_ok : forall a, proc_spec (read1_spec a) (read d1 a) recover abstr.
  Axiom write0_ok : forall a v, proc_spec (write0_spec a v) (write d0 a v) recover abstr.
  Axiom write1_ok : forall a v, proc_spec (write1_spec a v) (write d1 a v) recover abstr.
  Axiom size0_ok : proc_spec size0_spec (size d0) recover abstr.
  Axiom size1_ok : proc_spec size1_spec (size d1) recover abstr.
  Axiom recover_wipe : rec_wipe recover abstr no_wipe.

  Hint Resolve init_ok : core.
  Hint Resolve read0_ok : core.
  Hint Resolve read1_ok : core.
  Hint Resolve write0_ok : core.
  Hint Resolve write1_ok : core.
  Hint Resolve size0_ok : core.
  Hint Resolve size1_ok : core.
  Hint Resolve recover_wipe : core.

End TwoDiskAPI.
