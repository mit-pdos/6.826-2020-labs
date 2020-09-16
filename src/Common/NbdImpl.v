Require Import POCS.
Require Import NbdAPI.


Extraction Language Haskell.

Module NbdImpl <: NbdAPI.

  Axiom init: proc InitResult.
  Axiom getRequest : proc Request.
  Axiom sendResponse : Response -> proc unit.
  Axiom recover : proc unit.

  Axiom abstr : Abstraction State.

  Axiom init_ok : init_abstraction init recover abstr inited.
  Axiom getRequest_ok : proc_spec (getRequest_spec) (getRequest) recover abstr.
  Axiom sendResponse_ok : forall resp, proc_spec (sendResponse_spec resp) (sendResponse resp) recover abstr.
  Axiom recover_wipe : rec_wipe recover abstr wipe_req.

End NbdImpl.

Extract Constant Handle => "Data.Word.Word64".
Extract Constant NbdImpl.init => "Network.ServerOps.init".
Extract Constant NbdImpl.getRequest => "Network.ServerOps.getRequestFromQueue".
Extract Constant NbdImpl.sendResponse => "Network.ServerOps.sendResponseOnQueue".
Extract Constant NbdImpl.recover => "Network.ServerOps.recover".
