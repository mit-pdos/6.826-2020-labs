Require Import POCS.


Axiom Handle : Type.

Inductive Request :=
| Read (h:Handle) (off:addr) (blocks:nat)
| Write (h:Handle) (off:addr) (len:nat) (dat:bytes (len*blockbytes))
| Flush (h:Handle)
| Disconnect
| UnknownOp (h:Handle).

Inductive ErrorCode :=
| ESuccess
| EInvalid
| ENospc.

Record Response :=
  { rhandle: Handle;
    error: ErrorCode;
    data_len: nat;
    data: bytes data_len; }.

Record State := mkState {
  StateDisk : disk;
  StateReq : option Request
}.


Definition inited (s : State) : Prop :=
  StateReq s = None.

Fixpoint read_match (d : disk) (off : addr) (blocks : nat) : bytes (blocks * blockbytes) -> Prop :=
  match blocks with
  | O => fun data => True
  | S blocks' =>
    fun (data : bytes ((S blocks') * blockbytes)) =>
    let (thisdata, otherdata) := bsplit data in
    (diskGet d off = Some thisdata \/ diskGet d off = None) /\
    read_match d (S off) blocks' otherdata
  end.

Fixpoint write_upd (d : disk) (off : addr) (blocks : list (bytes blockbytes)) : disk :=
  match blocks with
  | nil => d
  | b :: blocks' =>
    write_upd (diskUpd d off b) (S off) blocks'
  end.

Definition read_match' (d : disk) (off : addr) (blocks : nat) (len : nat)
                       (H : len = blocks * blockbytes) (data : bytes len) : Prop.
  rewrite H in data.
  exact (read_match d off blocks data).
Defined.


Definition getRequest_spec : Specification _ Request unit State :=
  fun (_ : unit) state => {|
    pre := True;
    post := fun r state' =>
      state' = mkState (StateDisk state) (Some r);
    recovered := fun _ state' =>
      state' = mkState (StateDisk state) None
  |}.

Definition sendResponse_spec (resp : Response) : Specification _ unit unit State :=
  fun '(disk, disk', req) state => {|
    pre :=
      let '(@Build_Response rhandle error data_len data) := resp in
      state = mkState disk (Some req) /\
      match req with
      | Read h off blocks => h = rhandle /\ disk' = disk /\
        (error = ESuccess /\ exists Hlen,
         @read_match' disk off blocks data_len Hlen data) \/
        (error <> ESuccess /\ data_len = 0)
      | Write h off len data => h = rhandle /\ data_len = 0 /\
        (error = ESuccess /\ disk' = write_upd disk off (bsplit_list data)) \/
        (error <> ESuccess /\ disk' = disk)
      | Flush h => h = rhandle /\ data_len = 0 /\ disk' = disk
      | Disconnect => False
      | UnknownOp h => h = rhandle /\ error = EInvalid /\ data_len = 0 /\ disk' = disk
      end;
    post := fun r state' =>
      state' = mkState disk' None;
    recovered := fun _ state' =>
      state' = mkState disk None \/ state' = mkState disk' None
  |}.

Definition wipe_req (state state' : State) := state' = mkState (StateDisk state) None.
Hint Unfold wipe_req : core.


Module Type NbdAPI.

  Axiom init : proc InitResult.
  Axiom getRequest : proc Request.
  Axiom sendResponse : Response -> proc unit.
  Axiom recover : proc unit.

  Axiom abstr : Abstraction State.

  Axiom init_ok : init_abstraction init recover abstr inited.
  Axiom getRequest_ok : proc_spec (getRequest_spec) (getRequest) recover abstr.
  Axiom sendResponse_ok : forall resp, proc_spec (sendResponse_spec resp) (sendResponse resp) recover abstr.
  Axiom recover_wipe : rec_wipe recover abstr wipe_req.

  Hint Resolve init_ok : core.
  Hint Resolve getRequest_ok : core.
  Hint Resolve sendResponse_ok : core.
  Hint Resolve recover_wipe : core.

End NbdAPI.
