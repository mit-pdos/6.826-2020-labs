Require Import POCS.
Require Import VariablesAPI.
Require Import StatDbAPI.

(** * An implementation of StatDB

   StatDB is built on top of the Variables API, which maintains variables
   X, Y, and Z.  StatDB reads and writes these variables using the API
   provided in the VarsAPI module.  Here, we use [VarX] to store the number
   of integers seen so far, and [VarY] to store their sum.  The mean is
   then just [VarY]/[VarX], as long as [VarX] is not zero.
  *)


Module StatDB (v : VarsAPI) <: StatDbAPI.

  Import ListNotations.

  Definition add (v : nat) : proc unit :=
    sum <- v.read VarY;
    count <- v.read VarX;
    _ <- v.write VarY (sum + v);
    _ <- v.write VarX (count + 1);
    Ret tt.

  (** ** Exercise : complete the implementation of mean *)
  Definition mean : proc (option nat) :=
    Ret None.

  Definition init' : proc InitResult :=
    _ <- v.write VarX 0;
    _ <- v.write VarY 0;
    Ret Initialized.

  Definition init := then_init v.init init'.

  Definition recover : proc unit :=
    v.recover.

  (** ** Exercise : complete the implementation of the abstraction function: *)
  Definition statdb_abstraction (vars_state : VariablesAPI.State) (statdb_state : StatDbAPI.State) : Prop :=
    True.

  Definition abstr : Abstraction StatDbAPI.State :=
    abstraction_compose
      v.abstr
      {| abstraction := statdb_abstraction |}.

  Example abstr_1_ok : statdb_abstraction (VariablesAPI.mkState 1 3 0) [3].
  Proof.
    unfold statdb_abstraction; simpl.
    lia. (* this works for our abstraction relation *)
  Qed.

  (** ** Exercise : complete the proof for the following admitted examples *)
  Example abstr_2_ok : statdb_abstraction (VariablesAPI.mkState 2 3 0) [1; 2].
  Proof.
    unfold statdb_abstraction; simpl.
  Admitted.

  Example abstr_3_ok : statdb_abstraction (VariablesAPI.mkState 0 0 0) nil.
  Proof.
  Admitted.

  Example abstr_4_nok : ~ statdb_abstraction (VariablesAPI.mkState 1 0 0) [2].
  Proof.
    unfold statdb_abstraction; simpl.
  Admitted.

  Example abstr_5_nok : ~ statdb_abstraction (VariablesAPI.mkState 1 0 0) nil.
  Proof.
    unfold statdb_abstraction; simpl.
  Admitted.

  Theorem init_ok : init_abstraction init recover abstr inited.
  Proof.
    eapply then_init_compose; eauto.
    unfold init'.

    step_proc.
    step_proc.
    step_proc.
    exists nil.
    unfold statdb_abstraction, inited.
    intuition.
  Qed.

  (** ** Exercise : complete the proof of [add] *)
  Theorem add_ok : forall v, proc_spec (add_spec v) (add v) recover abstr.
  Proof.
    unfold add.
    intros.

    apply spec_abstraction_compose; simpl.
  Admitted.

  Opaque Nat.div.

  (** ** Exercise : complete the proof of [mean] *)
  Theorem mean_ok : proc_spec mean_spec mean recover abstr.
  Proof.
    unfold mean.
    intros.

    apply spec_abstraction_compose; simpl.

  Admitted.


  Theorem recover_wipe : rec_wipe recover abstr no_crash.
  Proof.
    unfold rec_wipe.
    intros.

    apply spec_abstraction_compose; simpl.
    step_proc.
    { exists state2. eauto. }
    { exfalso. eauto. }
  Qed.

End StatDB.


Require Import VariablesImpl.
Module StatDBImpl := StatDB Vars.
Print Assumptions StatDBImpl.abstr_2_ok.
Print Assumptions StatDBImpl.abstr_3_ok.
Print Assumptions StatDBImpl.abstr_4_nok.
Print Assumptions StatDBImpl.abstr_5_nok.
Print Assumptions StatDBImpl.add_ok.
Print Assumptions StatDBImpl.mean_ok.
