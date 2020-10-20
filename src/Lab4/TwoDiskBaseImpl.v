Require Import POCS.
Require Import TwoDiskBaseAPI.


Extraction Language Haskell.

Module TwoDiskBase <: TwoDiskBaseAPI.

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

End TwoDiskBase.

Extract Constant TwoDiskBase.init => "Replication.TwoDiskOps.init".
Extract Constant TwoDiskBase.read => "Replication.TwoDiskOps.read".
Extract Constant TwoDiskBase.write => "Replication.TwoDiskOps.write".
Extract Constant TwoDiskBase.size => "Replication.TwoDiskOps.size".
Extract Constant TwoDiskBase.recover => "Replication.TwoDiskOps.recover".
