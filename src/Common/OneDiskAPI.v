Require Import POCS.


Definition State := disk.

Definition read_spec (a : addr) : Specification _ block unit State :=
  fun (_ : unit) state => {|
    pre := True;
    post := fun r state' =>
      state' = state /\
      diskGet state a =?= r;
    recovered := fun _ state' =>
      state' = state
  |}.

Definition write_spec (a : addr) (v : block) : Specification _ _ unit State :=
  fun (_ : unit) state => {|
    pre := True;
    post := fun r state' =>
      r = tt /\ state' = diskUpd state a v;
    recovered := fun _ state' =>
      state' = state \/ state' = diskUpd state a v
  |}.

Definition size_spec : Specification _ nat unit State :=
  fun (_ : unit) state => {|
    pre := True;
    post := fun r state' =>
      state' = state /\ r = diskSize state;
    recovered := fun _ state' =>
      state' = state
  |}.


Module Type OneDiskAPI.

  Axiom init : proc InitResult.
  Axiom read : addr -> proc block.
  Axiom write : addr -> block -> proc unit.
  Axiom size : proc nat.
  Axiom recover : proc unit.

  Axiom abstr : Abstraction State.

  Axiom init_ok : init_abstraction init recover abstr inited_any.
  Axiom read_ok : forall a, proc_spec (read_spec a) (read a) recover abstr.
  Axiom write_ok : forall a v, proc_spec (write_spec a v) (write a v) recover abstr.
  Axiom size_ok : proc_spec size_spec size recover abstr.
  Axiom recover_wipe : rec_wipe recover abstr no_wipe.

  Hint Resolve init_ok : core.
  Hint Resolve read_ok : core.
  Hint Resolve write_ok : core.
  Hint Resolve size_ok : core.
  Hint Resolve recover_wipe : core.

End OneDiskAPI.
