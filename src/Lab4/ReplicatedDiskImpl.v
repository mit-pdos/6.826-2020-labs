Require Import POCS.

Require Import TwoDiskAPI.
Require Import Common.OneDiskAPI.

(**
ReplicatedDisk provides a single-disk API on top of two disks, handling disk
failures with replication.

Your job will be to implement the core of the recovery procedure for the
replicated disk, and prove that the entire implementation is correct using your
recovery procedure. This lab is split into several parts. Unlike in previous
labs, the exercises do not proceed in order in the file; you'll first write
specifications and admit the correctness proof, and then you'll come back and
finish the proof.
*)


Module ReplicatedDisk (td : TwoDiskAPI) <: OneDiskAPI.

  (* EXERCISE (4a): implement read *)
  Definition read (a:addr) : proc block :=
    Ret block0.

  Definition write (a:addr) (b:block) : proc unit :=
    _ <- td.write d0 a b;
    _ <- td.write d1 a b;
    Ret tt.

  Definition size : proc nat :=
    msz <- td.size d0;
    match msz with
    | Working sz => Ret sz
    | Failed =>
      msz <- td.size d1;
      match msz with
      | Working sz => Ret sz
      | Failed => Ret 0
      end
    end.

  (** [sizeInit] computes the size during initialization; it may return None if
  the sizes of the underlying disks differ. *)
  Definition sizeInit : proc (option nat) :=
    sz1 <- td.size d0;
    sz2 <- td.size d1;
    match sz1 with
    | Working sz1 =>
      match sz2 with
      | Working sz2 =>
        if sz1 == sz2 then Ret (Some sz1) else Ret None
      | Failed => Ret (Some sz1)
      end
    | Failed =>
      match sz2 with
      | Working sz2 => Ret (Some sz2)
      | Failed => Ret None
      end
    end.

  (* Recursively initialize block a and below. For simplicity, we make the disks
  match by setting every block to [block0]. *)
  Fixpoint init_at (a:nat) : proc unit :=
    match a with
    | 0 => Ret tt
    | S a =>
      _ <- td.write d0 a block0;
      _ <- td.write d1 a block0;
      init_at a
    end.

  (* Initialize every disk block *)
  Definition init' : proc InitResult :=
    size <- sizeInit;
    match size with
    | Some sz =>
      _ <- init_at sz;
      Ret Initialized
    | None =>
      Ret InitFailed
    end.

  Definition init := then_init td.init init'.


  (**
   * Helper theorems and tactics for proofs.
   *)

  Theorem exists_tuple2 : forall A B (P: A * B -> Prop),
      (exists a b, P (a, b)) ->
      (exists p, P p).
  Proof.
    intros.
    repeat deex; eauto.
  Qed.

  (* The [simplify] tactic performs a number of steps that should simplify and
  clean up your goals. *)
  Ltac simplify :=
    repeat match goal with
           | |- forall _, _ => intros
           | _ => deex
           | _ => destruct_tuple
           | [ u: unit |- _ ] => destruct u
           | |- _ /\ _ => split; [ solve [auto] | ]
           | |- _ /\ _ => split; [ | solve [auto] ]
           | |- exists (_: disk*_), _ => apply exists_tuple2
           | _ => progress simpl in *
           | _ => progress safe_intuition
           | _ => progress subst
           | _ => progress autorewrite with upd in *
           end.

  (* The [finish] tactic tries a number of techniques to solve the goal. *)
  Ltac finish :=
    repeat match goal with
           | _ => solve_false
           | _ => congruence
           | _ => solve [ intuition ]
           | _ =>
             (* if we can solve all the side conditions automatically, then it's
             safe to run descend and create existential variables *)
             descend; (intuition eauto);
             lazymatch goal with
             | |- proc_spec _ _ _ _ => idtac
             | _ => fail
             end
           end.

  Ltac step :=
    step_proc; simplify; finish.

  (**
   * Specifications and proofs about our implementation of the replicated disk API,
   * without considering our recovery.
   *
   * These intermediate specifications separate reasoning about the
   * implementations from recovery behavior.
   *)

  Theorem both_disks_not_missing : forall (state: TwoDiskBaseAPI.State),
      two_disks_are state missing missing ->
      False.
  Proof.
    unfold two_disks_are.
    destruct state; unfold missing; simpl; intuition auto.
  Qed.

  Hint Resolve both_disks_not_missing : false.

  Theorem missing0_implies_any : forall (state: TwoDiskBaseAPI.State) P F,
      two_disks_are state missing F ->
      two_disks_are state P F.
  Proof.
    unfold two_disks_are.
    destruct state; unfold missing; simpl; intuition auto.
  Qed.

  Theorem missing1_implies_any : forall (state: TwoDiskBaseAPI.State) P F,
      two_disks_are state F missing ->
      two_disks_are state F P.
  Proof.
    unfold two_disks_are.
    destruct state; unfold missing; simpl; intuition auto.
  Qed.

  Hint Resolve missing0_implies_any : core.
  Hint Resolve missing1_implies_any : core.

  (* EXERCISE (4a): prove this specification for read *)
  Theorem read_int_ok : forall a,
      proc_spec
        (fun d state =>
           {|
             pre := two_disks_are state (eq d) (eq d);
             post :=
               fun r state' =>
                 two_disks_are state' (eq d) (eq d) /\
                 diskGet d a =?= r;
             recovered :=
               fun _ state' =>
                 two_disks_are state' (eq d) (eq d);
           |})
        (read a)
        td.recover
        td.abstr.
  Proof.
    unfold read.

    (* Hint: use step instead of step_proc to take advantage of the new
    automation in this lab. *)

    step.
  Admitted.

  Hint Resolve read_int_ok : core.

  (* EXERCISE (4a): complete and prove this specification for write *)
  Theorem write_int_ok : forall a b,
      proc_spec
        (fun d state =>
           {|
             pre := two_disks_are state (eq d) (eq d);
             post :=
               fun r state' =>
                 r = tt /\
                 two_disks_are state' (eq (diskUpd d a b)) (eq (diskUpd d a b));
             recovered :=
               fun _ state' =>
                 (* EXERCISE (4a): write the recovered condition for write. Note
                 that this is the two-disk API's recovery, not the replicated
                 disk's recovery, so it should cover all the crash cases for
                 write *)
             True;
           |})
        (write a b)
        td.recover
        td.abstr.
  Proof.
    unfold write.

  Admitted.

  Hint Resolve write_int_ok : core.

  (* EXERCISE (4a): prove this specification for size *)
  Theorem size_int_ok :
    proc_spec
      (fun '(d_0, d_1) state =>
         {|
           pre := two_disks_are state (eq d_0) (eq d_1) /\
             diskSize d_0 = diskSize d_1;
           post :=
             fun r state' =>
               r = diskSize d_0 /\
               r = diskSize d_1 /\
               two_disks_are state' (eq d_0) (eq d_1);
           recovered :=
             fun _ state' =>
               two_disks_are state' (eq d_0) (eq d_1);
         |})
      (size)
      td.recover
      td.abstr.
  Proof.
    unfold size.

  Admitted.

  Hint Resolve size_int_ok : core.

  (* We provide a proof for [init]. *)

  Definition equal_after a (d_0 d_1: disk) :=
    diskSize d_0 = diskSize d_1 /\
    forall a', a <= a' -> diskGet d_0 a' = diskGet d_1 a'.

  Theorem le_eq_or_S_le : forall n m,
      n <= m ->
      n = m \/
      S n <= m /\ n <> m.
  Proof.
    intros.
    lia.
  Qed.

  Theorem equal_after_diskUpd : forall a d_0 d_1 b,
      equal_after (S a) d_0 d_1 ->
      equal_after a (diskUpd d_0 a b) (diskUpd d_1 a b).
  Proof.
    unfold equal_after; intuition.
    - autorewrite with upd; eauto.
    - apply le_eq_or_S_le in H1; intuition subst.
      { destruct (lt_dec a' (diskSize d_0)); autorewrite with upd.
        + assert (a' < diskSize d_1) by congruence; autorewrite with upd; auto.
        + assert (~a' < diskSize d_1) by congruence; autorewrite with upd; auto.
      }
      autorewrite with upd; eauto.
  Qed.

  Hint Resolve equal_after_diskUpd : core.

  Theorem init_at_ok : forall a,
      proc_spec
        (fun '(d_0, d_1) state =>
           {| pre :=
                two_disks_are state (eq d_0) (eq d_1) /\
                equal_after a d_0 d_1;
              post :=
                fun _ state' =>
                  exists d_0' d_1': disk,
                    two_disks_are state' (eq d_0') (eq d_1') /\
                    equal_after 0 d_0' d_1';
              recovered :=
                fun _ state' => True;
           |})
        (init_at a)
        td.recover
        td.abstr.
  Proof.
    induction a; simpl; intros.
    - step.
    - step.

      step.
      destruct r; finish.
      + step.
        destruct r; simplify; finish.
      + step.
        destruct r; simplify.
        * exists (diskUpd d_0 a block0).
          exists (diskUpd d_1 a block0).
          finish.
        * finish.
  Qed.

  Hint Resolve init_at_ok : core.

  Theorem sizeInit_ok :
    proc_spec
      (fun '(d_0, d_1) state =>
         {| pre :=
              two_disks_are state (eq d_0) (eq d_1);
            post :=
              fun r state' =>
                exists d_0' d_1',
                  two_disks_are state' (eq d_0') (eq d_1') /\
                  match r with
                  | Some sz => diskSize d_0' = sz /\ diskSize d_1' = sz
                  | None => True
                  end;
            recovered :=
              fun _ state' => True;
         |})
      (sizeInit)
      td.recover
      td.abstr.
  Proof.
    unfold sizeInit.
    step.
    destruct r.
    - step.
      destruct r.
      + destruct (diskSize d_0 == v).
        * step.
        * step.
      + step.
    - step.
      destruct r.
      + step.
      + step.
  Qed.

  Hint Resolve sizeInit_ok : core.


  Theorem equal_after_0_to_eq : forall d_0 d_1,
      equal_after 0 d_0 d_1 ->
      d_0 = d_1.
  Proof.
    unfold equal_after; intuition.
    eapply disk_ext_eq; intros.
    eapply H0; lia.
  Qed.

  Theorem equal_after_size : forall d_0 d_1,
      diskSize d_0 = diskSize d_1 ->
      equal_after (diskSize d_0) d_0 d_1.
  Proof.
    unfold equal_after; intuition.
    assert (~a' < diskSize d_0) by lia.
    assert (~a' < diskSize d_1) by congruence.
    autorewrite with upd; eauto.
  Qed.

  Hint Resolve equal_after_size : core.
  Hint Resolve equal_after_0_to_eq : core.

  Theorem init'_ok :
    proc_spec
      (fun '(d_0, d_1) state =>
         {| pre :=
              two_disks_are state (eq d_0) (eq d_1);
            post :=
              fun r state' =>
                match r with
                | Initialized =>
                  exists d_0' d_1',
                  two_disks_are state' (eq d_0') (eq d_1') /\
                  d_0' = d_1'
                | InitFailed =>
                  True
                end;
            recovered :=
              fun _ state' => True;
         |})
      (init')
      td.recover
      td.abstr.
  Proof.
    unfold init'.
    step.
    destruct r; step.
    step.
  Qed.

  Hint Resolve init'_ok : core.

  (**
   * Recovery implementation.
   *
   * We provide the general structure for recovery: essentially, it consists of
   * a loop around [fixup] that terminates after either fixing an out-of-sync
   * disk block or when a disk has failed.
  *)

  (* [fixup] returns a [RecStatus] to implement early termination in [recovery_at]. *)
  Inductive RecStatus :=
  (* continue working, nothing interesting has happened *)
  | Continue
  (* some address has been repaired (or the recovery has exhausted the
     addresses) - only one address can be out of sync and thus only it must be
     recovered. *)
  (* OR, one of the disks has failed, so don't bother continuing recovery since
     the invariant is now trivially satisfied *)
  | RepairDoneOrFailed.

  (* EXERCISE (4c): implement [fixup], which should perform recovery for a
  single address and indicate whether to continue or not. *)
  Definition fixup (a:addr) : proc RecStatus :=
    Ret Continue.

  (* recursively performs recovery at [a-1], [a-2], down to 0 *)
  Fixpoint recover_at (a:addr) : proc unit :=
    match a with
    | 0 => Ret tt
    | S n =>
      s <- fixup n;
      match s with
      | Continue => recover_at n
      | RepairDoneOrFailed => Ret tt
      end
    end.

  Definition Recover : proc unit :=
    sz <- size;
    _ <- recover_at sz;
    Ret tt.


  (**
   * Theorems and recovery proofs.
   *)

  Theorem if_lt_dec : forall A n m (a a':A),
      n < m ->
      (if lt_dec n m then a else a') = a.
  Proof.
    intros.
    destruct (lt_dec n m); auto.
  Qed.

  Theorem disks_eq_inbounds : forall (d: disk) a v v',
      a < diskSize d ->
      diskGet d a =?= v ->
      diskGet d a =?= v' ->
      v = v'.
  Proof.
    intros.
    case_eq (diskGet d a); intros.
    - rewrite H2 in *. simpl in *. congruence.
    - exfalso.
      eapply disk_inbounds_not_none; eauto.
  Qed.

  (* To make these specifications precise while also covering both the already
   * synced and diverged disks cases, we keep track of which input state we're
   * in from the input and use it to give an exact postcondition. *)
  Inductive DiskStatus :=
  | FullySynced
  | OutOfSync (a:addr) (b:block).

  Theorem diskUpd_maybe_same : forall (d:disk) a b,
      diskGet d a =?= b ->
      diskUpd d a b = d.
  Proof.
    intros.
    destruct (diskGet d a) eqn:?; simpl in *; subst;
      autorewrite with upd;
      auto.
  Qed.

  Hint Rewrite diskUpd_maybe_same using (solve [ auto ]) : upd.
  Hint Resolve PeanoNat.Nat.lt_neq : core.
  Hint Resolve disks_eq_inbounds : core.


  (* EXERCISE (4c): write and admit a specification for [fixup]. *)
  Theorem fixup_ok : forall a,
      proc_spec
        (fun '(d, s) state =>
           {|
             pre :=
               a < diskSize d /\
               match s with
               | FullySynced => True
               | OutOfSync a' b => True
               end;
             post :=
               fun r state' =>
                 match s with
                 | FullySynced => True
                 | OutOfSync a' b => True
                 end;
             recovered :=
               fun _ state' =>
                 match s with
                 | FullySynced => True
                 | OutOfSync a' b => True
                 end;
           |})
        (fixup a)
        td.recover
        td.abstr.
  Proof.
    (* EXERCISE (4d): prove [fixup_ok] *)
  Admitted.

  Hint Resolve fixup_ok : core.

  (* Hint Resolve Lt.lt_n_Sm_le. *)

  (* EXERCISE (4c): specify and prove recover_at *)
  (* Hint: use [induction a] *)
  Theorem recover_at_ok : forall a,
      proc_spec
        (fun (_:unit) state =>
           {|
             pre := True;
             post :=
               fun r state' => True;
             recovered :=
               fun _ state' => True
           |})
        (recover_at a)
        td.recover
        td.abstr.
  Proof.
  Admitted.

  Hint Resolve recover_at_ok : core.

  (* EXERCISE (4b): write a spec for recovery *)
  Definition Recover_spec : Specification _ unit unit TwoDiskBaseAPI.State :=
    fun (_:unit) state =>
      {|
        pre := True;
        post := fun _ state' => True;
        recovered := fun _ state' => True;
      |}.

  (* EXERCISE (4c): prove recovery correct *)
  Theorem Recover_rok :
    proc_spec
      Recover_spec
      (Recover)
      td.recover
      td.abstr.
  Proof.
  Admitted.

  (* EXERCISE (4b): prove that your recovery specification is idempotent; that
  is, its recovered condition implies its precondition. *)
  Theorem Recover_spec_idempotent :
    idempotent Recover_spec.
  Proof.
    unfold idempotent.
    intuition; simplify.
  Admitted.

  (* This proof combines your proof that recovery is correct and that its
  specification is idempotent to show recovery is correct even if re-run on
  every crash. *)
  Theorem Recover_ok :
    proc_loopspec
      Recover_spec
      (Recover)
      td.recover
      td.abstr.
  Proof.
    eapply idempotent_loopspec; simpl.
    - apply Recover_rok.
    - apply Recover_spec_idempotent.
  Qed.

  Hint Resolve Recover_ok : core.

  Definition recover: proc unit :=
    _ <- td.recover;
    Recover.

  (* As the final step in giving the correctness of the replicated disk
  operations, we prove recovery specs that include the replicated disk Recover
  function. *)

  Definition rd_abstraction (state: TwoDiskBaseAPI.State) (d:OneDiskAPI.State) : Prop :=
    two_disks_are state (eq d) (eq d).

  Definition abstr : Abstraction OneDiskAPI.State :=
    abstraction_compose td.abstr {| abstraction := rd_abstraction; |}.

  Theorem init_ok : init_abstraction init recover abstr inited_any.
  Proof.
    intros.
    eapply then_init_compose; eauto.
    eapply proc_spec_weaken; eauto.
    unfold spec_impl; intros.
    destruct state; simpl in *.

    - exists (d_0, d_1); simpl; intuition.
      { unfold two_disks_are; simpl; intuition. }
      unfold rd_abstraction.
      destruct v; simplify; finish.
    - exists (d_0, d_0); simplify; intuition.
      { unfold two_disks_are; simpl; intuition. }
      unfold rd_abstraction.
      destruct v; simplify; finish.
    - exists (d_1, d_1); simplify; finish; intuition.
      { unfold two_disks_are; simpl; intuition. }
      unfold rd_abstraction.
      destruct v; simplify; finish.
  Qed.

  (* EXERCISE (4b): prove that read, write, and size are correct when combined
  with your recovery (using your specification but admitted proof). *)

  Theorem read_ok : forall a, proc_spec (read_spec a) (read a) recover abstr.
  Proof.
    intros.
    apply spec_abstraction_compose; simpl.
    eapply compose_recovery; eauto; simplify.
  Admitted.

  Theorem write_ok : forall a v, proc_spec (write_spec a v) (write a v) recover abstr.
  Proof.
    intros.
    apply spec_abstraction_compose; simpl.
    eapply compose_recovery; eauto; simplify.
  Admitted.

  Theorem size_ok : proc_spec size_spec size recover abstr.
  Proof.
    intros.
    apply spec_abstraction_compose; simpl.
    (* simplify is a bit too aggressive about existential variables here, so we
    provide some manual simplification here *)
    eapply compose_recovery; eauto.
    intros; apply exists_tuple2.
    destruct a; simpl in *.
  Admitted.

  (* This theorem shows that Ret does not modify the abstract state exposed by
  the replicated disk; the interesting part is that if recovery runs, then the
  only effect should be the wipe relation (the trivial relation [no_wipe] in
  this case) *)
  (* EXERCISE (4b): prove this theorem using your recovery spec *)
  Theorem recover_wipe : rec_wipe recover abstr no_wipe.
  Proof.
    eapply rec_wipe_compose; eauto; simpl.
    autounfold; unfold rd_abstraction, Recover_spec; simplify.
  Admitted.

End ReplicatedDisk.
