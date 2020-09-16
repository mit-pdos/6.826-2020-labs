Require Import POCS.
Require Import BadBlockAPI.


Extraction Language Haskell.

Module BadBlockDisk <: BadBlockAPI.

  Axiom init : proc InitResult.
  Axiom read : addr -> proc block.
  Axiom write : addr -> block -> proc unit.
  Axiom getBadBlock : proc addr.
  Axiom size : proc nat.
  Axiom recover : proc unit.

  Axiom abstr : Abstraction State.

  Axiom init_ok : init_abstraction init recover abstr inited_any.
  Axiom read_ok : forall a, proc_spec (read_spec a) (read a) recover abstr.
  Axiom write_ok : forall a v, proc_spec (write_spec a v) (write a v) recover abstr.
  Axiom getBadBlock_ok : proc_spec getBadBlock_spec getBadBlock recover abstr.
  Axiom size_ok : proc_spec size_spec size recover abstr.
  Axiom recover_wipe : rec_wipe recover abstr no_wipe.

End BadBlockDisk.

Extract Constant BadBlockDisk.init => "BadBlockDisk.Ops.init".
Extract Constant BadBlockDisk.read => "BadBlockDisk.Ops.read".
Extract Constant BadBlockDisk.write => "BadBlockDisk.Ops.write".
Extract Constant BadBlockDisk.getBadBlock => "BadBlockDisk.Ops.getBadBlock".
Extract Constant BadBlockDisk.size => "BadBlockDisk.Ops.size".
Extract Constant BadBlockDisk.recover => "BadBlockDisk.Ops.recover".
