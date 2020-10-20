Require Import POCS.
Require Import TwoDiskAPI.
Require Import TwoDiskBaseAPI.


Module TwoDisk (b : TwoDiskBaseAPI) <: TwoDiskAPI.

  Definition init := b.init.
  Definition read := b.read.
  Definition write := b.write.
  Definition size := b.size.
  Definition recover:= b.recover.

  Definition abstr := b.abstr.

  Ltac inv_step :=
    match goal with
    | [ H: op_step _ _ _ _ |- _ ] =>
      inversion H; subst; clear H;
      repeat sigT_eq;
      safe_intuition
    end.

  Ltac inv_bg :=
    match goal with
    | [ H: bg_failure _ _ |- _ ] =>
      inversion H; subst; clear H
    end.

  Theorem maybe_holds_stable : forall state state' F0 F1,
    disk0 state ?|= F0 ->
    disk1 state ?|= F1 ->
    bg_failure state state' ->
    disk0 state' ?|= F0 /\
    disk1 state' ?|= F1.
  Proof.
    intros.
    inv_bg; simpl in *; eauto.
  Qed.

  Ltac cleanup :=
    repeat match goal with
           | [ |- forall _, _ ] => intros
           | |- _ /\ _ => split; [ solve [ eauto || congruence ] | ]
           | |- _ /\ _ => split; [ | solve [ eauto || congruence ] ]
           | [ H: Working _ = Working _ |- _ ] => inversion H; subst; clear H
           | [ H: bg_failure _ _ |- _ ] =>
             eapply maybe_holds_stable in H;
             [ | solve [ eauto ] | solve [ eauto ] ]; destruct_ands
           | [ H: _ ?|= eq _, H': _ = Some _ |- _ ] =>
                    pose proof (holds_some_inv_eq _ H' H); clear H
           | [ H: ?A * ?B |- _ ] => destruct H
           | [ H: DiskResult _ |- _ ] => destruct H
           | _ => deex
           | _ => destruct_tuple
           | _ => progress unfold pre_step in *
           | _ => progress autounfold in *
           | _ => progress simpl in *
           | _ => progress subst
           | _ => progress safe_intuition
           | _ => solve [ eauto ]
           | _ => congruence
           | _ => inv_step
           | H: context[match ?expr with _ => _ end] |- _ =>
             destruct expr eqn:?; [ | solve [ repeat cleanup ] ]
           | H: context[match ?expr with _ => _ end] |- _ =>
             destruct expr eqn:?; [ solve [ repeat cleanup ] | ]
           end.

  Ltac prim :=
    intros;
    eapply proc_spec_weaken; [ eauto | unfold spec_impl ]; exists tt;
    intuition eauto; cleanup;
    intuition eauto; cleanup.

  Hint Resolve holds_in_some_eq : core.
  Hint Resolve holds_in_none_eq : core.
  Hint Resolve pred_missing : core.

  Hint Unfold combined_step : core.


  Theorem init_ok : init_abstraction init recover abstr inited_any.
  Proof.
    eauto.
  Qed.

  Theorem read0_ok : forall a, proc_spec (read0_spec a) (read d0 a) recover abstr.
  Proof.
    unfold read0_spec.
    unfold two_disks_are.
    prim.
  Qed.

  Theorem read1_ok : forall a, proc_spec (read1_spec a) (read d1 a) recover abstr.
  Proof.
    unfold read1_spec.
    unfold two_disks_are.
    prim.
  Qed.

  Ltac destruct_all :=
    repeat match goal with
           | _ => solve [ auto ]
           | [ i: diskId |- _ ] => destruct i
           | [ |- context[match ?s with
                         | BothDisks _ _ => _
                         | OnlyDisk0 _ => _
                         | OnlyDisk1 _ => _
                         end] ] => destruct s
           | _ => simpl in *
           end.

  Theorem write0_ok : forall a v, proc_spec (write0_spec a v) (write d0 a v) recover abstr.
  Proof.
    unfold write0_spec.
    unfold two_disks_are.
    prim; try solve [ destruct_all ].
    destruct (le_dec (S a) (diskSize d0)).
    * destruct_all.
    * rewrite diskUpd_oob_noop by lia.
      destruct_all.
  Qed.

  Theorem write1_ok : forall a v, proc_spec (write1_spec a v) (write d1 a v) recover abstr.
  Proof.
    unfold write1_spec.
    unfold two_disks_are.
    prim; try solve [ destruct_all ].
    destruct (le_dec (S a) (diskSize d0)).
    * destruct_all.
    * rewrite diskUpd_oob_noop by lia.
      destruct_all.
  Qed.

  Theorem size0_ok : proc_spec size0_spec (size d0) recover abstr.
  Proof.
    unfold size0_spec.
    unfold two_disks_are.
    prim.
  Qed.

  Theorem size1_ok : proc_spec size1_spec (size d1) recover abstr.
  Proof.
    unfold size1_spec.
    unfold two_disks_are.
    prim.
  Qed.

  Theorem recover_wipe : rec_wipe recover abstr no_wipe.
  Proof.
    eauto.
  Qed.

End TwoDisk.
