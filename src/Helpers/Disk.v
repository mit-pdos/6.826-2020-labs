Require Import Arith.
Require Import RelationClasses.
Require Import List.
Require Import Helpers.

Set Implicit Arguments.


(** * Disk model.

    This file defines our model of a disk. We represent a disk as a list
    of 1KB blocks and provide functions to read and update disks, as
    well as theorems about these operations. In order to describe disks,
    we first provide a model of byte sequences.
 *)

(** * Model of bytes.

    In our lab assignments, we will model disks as consisting of
    blocks, which are in turn composed of bytes.  Here, we define
    a notion of a byte array: the type of an array of [n] bytes
    will be [bytes n].

    There's one unusual aspect of how we model bytes: instead of
    defining the bytes type in Coq, we simply add it as an [Axiom]. This
    means we are not providing a Coq (Gallina) implementation of bytes,
    and instead we are telling Coq to assume that there exists something
    called [bytes], and there exist other functions that manipulate
    bytes that we define here as well (like [bytes_dec] to decide if two
    byte arrays are equal).

    When we generate executable code by extracting our Coq (Gallina)
    code into Haskell, we will be required to provide a Haskell
    implementation of any such [Axiom].  This correspondence is
    made below, using [Extract Constant], and we (as developers)
    are responsible for making sure any axioms we state (like
    [bsplit_bappend]) are true of our Haskell implementations.
  *)

Axiom bytes : nat -> Type.

Axiom bytes_dec : forall n, EqualDec (bytes n).
Existing Instance bytes_dec.

(**
    Two "initial" byte values: an all-zero array, [bytes0], and
    an all-ones array, [bytes1].  We also promise that all-zero
    and all-ones arrays are different, as long as there's at least
    one element.
  *)

Axiom bytes0 : forall n, bytes n.
Axiom bytes1 : forall n, bytes n.
Axiom bytes_differ : forall n, n > 0 -> bytes0 n <> bytes1 n.

Definition bnull : bytes 0 := bytes0 0.

Axiom bappend : forall n1 n2, bytes n1 -> bytes n2 -> bytes (n1+n2).
Axiom bsplit : forall n1 n2, bytes (n1+n2) -> bytes n1 * bytes n2.
Arguments bsplit {n1 n2} bs.

Axiom bsplit_bappend : forall n1 n2 (b1 : bytes n1) (b2 : bytes n2), bsplit (bappend b1 b2) = (b1, b2).

Fixpoint bsplit_list {n} {m} : bytes (n * m) -> list (bytes m) :=
  match n with
  | O => fun _ => nil
  | S n' => fun (bs : bytes ((S n') * m)) =>
    let (this, rest) := bsplit bs in
    this :: bsplit_list rest
  end.

Extraction Language Haskell.

Extract Constant bytes => "Data.ByteString.ByteString".
Extract Constant bytes_dec => "(\n b1 b2 -> b1 Prelude.== b2)".
Extract Constant bytes0 => "(\n -> Data.ByteString.replicate (Prelude.fromIntegral n) 0)".

Extract Constant bappend => "(\_ _ bs1 bs2 -> Data.ByteString.append bs1 bs2)".
Extract Constant bsplit => "(\n1 _ bs -> Data.ByteString.splitAt (Prelude.fromIntegral n1) bs)".


(** * Model of blocks.

    We represent blocks as a byte array of a fixed size.

    We define the block size as a separate constant, [blockbytes], to avoid the
    literal constant [1024] reducing performance of proofs.
  *)

Definition blockbytes := 1024.

Definition block := bytes blockbytes.
Definition block0 : block := bytes0 _.
Definition block1 : block := bytes1 _.

Theorem block0_block1_differ : block0 <> block1.
Proof.
  apply bytes_differ.
  unfold blockbytes.
  lia.
Qed.

Hint Resolve block0_block1_differ : core.

(** Mark [blockbytes] as opaque so that Coq doesn't expand it too eagerly.
  *)

Opaque blockbytes.


(** * Disk as a list of blocks.

    Now we can define our model of a disk: a list of blocks.
    A disk with zero blocks is an empty list, [nil].
  *)

Definition disk := list block.

Definition empty_disk : disk := nil.

(** We define three main operations on disks:

    - [diskGet d a] gets the contents of an address [a] in disk [d].
      It returns an [option block], which is either a block value [b]
      (represented by [Some b]), or [None] if [a] is past the end of
      the disk.

    - [diskSize] returns the size of the disk, which is just the length
      of the list representing the disk.

    - [diskUpd] writes to a disk.  Since Gallina is a functional language,
      we cannot update a disk "in-place", so instead [diskUpd] returns a
      new disk reflecting the write.  Specifically, [diskUpd d a b] returns
      a new disk with address [a] updated to block value [b], if [a] is
      in-bounds, or the original disk unchanged if [a] is out-of-bounds.
  *)

(** We address into disks with [addr], which is simply a [nat]. *)
Definition addr := nat.

Definition diskGet (d : disk) (a : addr) : option block :=
  nth_error d a.

Definition diskSize (d : disk) : nat := length d.

Fixpoint diskUpd d (a: addr) b : disk :=
  match d with
  | nil => nil
  | db :: drest =>
    match a with
    | O => b :: drest
    | S a' => db :: diskUpd drest a' b
    end
  end.

(** We define another helper operation, [diskShrink], which takes
    a disk and drops the last block.  This will be helpful in the
    bad-block-remapping lab assignment.
  *)

Definition diskShrink (d : disk) : disk :=
  firstn (length d - 1) d.

(** We also define variants of [diskGet] and [diskUpd] that operate
    on multiple blocks at a time.  These may be helpful in the
    logging lab assignment, but not required in any sense.
  *)

Fixpoint diskGets (d : disk) (a : addr) (count : nat) : list (option block) :=
  match count with
  | O =>
    nil
  | S count' =>
    diskGet d a :: diskGets d (a+1) count'
  end.

Fixpoint diskUpds (d : disk) (a : addr) (blocks : list block) : disk :=
  match blocks with
  | nil =>
    d
  | b :: blocks' =>
    diskUpd (diskUpds d (a+1) blocks') a b
  end.

(** Finally, we prove a variety of theorems about the behavior of these
    disk operations.
  *)

(** ** Theorems about diskGet *)

Theorem disk_inbounds_exists : forall a d,
    a < diskSize d ->
    exists b, diskGet d a = Some b.
Proof.
  unfold diskSize.
  intros.
  case_eq (diskGet d a); intros; eauto.
  apply nth_error_None in H0.
  lia.
Qed.

Theorem disk_inbounds_not_none : forall a d,
    a < diskSize d ->
    diskGet d a = None ->
    False.
Proof.
  unfold diskSize.
  intros.
  apply nth_error_None in H0.
  lia.
Qed.

Theorem disk_none_oob : forall a d,
    diskGet d a = None ->
    ~a < diskSize d.
Proof.
  intros.
  destruct (lt_dec a (diskSize d)); eauto.
  exfalso; eapply disk_inbounds_not_none; eauto.
Qed.

Theorem disk_oob_eq : forall d a,
    ~a < diskSize d ->
    diskGet d a = None.
Proof.
  unfold diskSize.
  induction d; simpl; intros.
  - induction a; eauto.
  - destruct a0; simpl.
    + lia.
    + eapply IHd. lia.
Qed.

(* this rule allows autorewrite to simplify maybe_eq *)
Theorem maybe_eq_None_is_True T (v:T) :
  maybe_eq None v = True.
Proof.
  reflexivity.
Qed.

Hint Rewrite maybe_eq_None_is_True : upd.

Theorem maybe_eq_None_holds T (v:T) : maybe_eq None v.
Proof.
  exact I.
Qed.

Hint Resolve maybe_eq_None_holds : core.

Theorem nth_error_ext_eq A : forall (l1 l2: list A),
    (forall a, nth_error l1 a = nth_error l2 a) ->
    l1 = l2.
Proof.
  induction l1; simpl; intros.
  - destruct l2; simpl; intros; eauto.
    specialize (H 0); simpl in *.
    congruence.
  - destruct l2; simpl; intros.
    + specialize (H 0); simpl in *.
      congruence.
    + specialize (H 0) as H'; simpl in H'.
      f_equal; try congruence.
      eapply IHl1; intros.
      specialize (H (S a1)); simpl in H.
      eauto.
Qed.

Theorem nth_error_ext_inbounds_eq A : forall (l1 l2: list A),
    length l1 = length l2 ->
    (forall a, a < length l1 -> nth_error l1 a = nth_error l2 a) ->
    l1 = l2.
Proof.
  intros.
  apply nth_error_ext_eq; intros.
  destruct (lt_dec a (length l1)); eauto.
  Search nth_error.
  assert (nth_error l1 a = None).
  apply nth_error_None; lia.
  assert (nth_error l2 a = None).
  apply nth_error_None; lia.
  congruence.
Qed.

Theorem disk_ext_eq : forall d d',
    (forall a, diskGet d a = diskGet d' a) ->
    d = d'.
Proof.
  intros.
  apply nth_error_ext_eq; auto.
Qed.

Theorem disk_ext_inbounds_eq : forall d d',
    diskSize d = diskSize d' ->
    (forall a, a < diskSize d -> diskGet d a = diskGet d' a) ->
    d = d'.
Proof.
  intros.
  apply nth_error_ext_inbounds_eq; auto.
Qed.

(** ** Theorems about diskUpd *)

Theorem diskUpd_eq_some : forall d a b0 b,
    diskGet d a = Some b0 ->
    diskGet (diskUpd d a b) a = Some b.
Proof.
  induction d; simpl; eauto.
  - destruct a; simpl; intros; congruence.
  - destruct a0; simpl; intros; eauto.
Qed.

Theorem diskUpd_eq : forall d a b,
    a < diskSize d ->
    diskGet (diskUpd d a b) a = Some b.
Proof.
  intros.
  apply disk_inbounds_exists in H; deex.
  eauto using diskUpd_eq_some.
Qed.

Theorem diskUpd_size : forall d a b,
    diskSize (diskUpd d a b) = diskSize d.
Proof.
  induction d; simpl; eauto.
  destruct a0; simpl; intros; eauto.
Qed.

Theorem diskUpd_oob_eq : forall d a b,
    ~a < diskSize d ->
    diskGet (diskUpd d a b) a = None.
Proof.
  intros.
  apply disk_oob_eq.
  rewrite diskUpd_size; auto.
Qed.

Theorem diskUpd_neq : forall d a b a',
    a <> a' ->
    diskGet (diskUpd d a b) a' = diskGet d a'.
Proof.
  induction d; simpl; intros; auto.
  destruct a0; simpl.
  - destruct a'; simpl; try lia; auto.
  - destruct a'; simpl; auto.
Qed.

Theorem diskUpd_none : forall d a b,
    diskGet d a = None ->
    diskUpd d a b = d.
Proof.
  induction d; simpl; intros; auto.
  destruct a0; simpl in *; try congruence.
  rewrite IHd; eauto.
Qed.

Theorem diskUpd_same : forall d a b,
    diskGet d a = Some b ->
    diskUpd d a b = d.
Proof.
  induction d; simpl; intros; auto.
  destruct a0; simpl in *.
  - congruence.
  - rewrite IHd; eauto.
Qed.

Theorem diskUpd_twice : forall d a b b',
    diskUpd (diskUpd d a b) a b' = diskUpd d a b'.
Proof.
  induction d; simpl; intros; auto.
  destruct a0; simpl in *.
  - congruence.
  - rewrite IHd; eauto.
Qed.

Theorem diskUpd_comm : forall d a a' b b',
    a <> a' ->
    diskUpd (diskUpd d a b) a' b' = diskUpd (diskUpd d a' b') a b.
Proof.
  induction d; simpl; intros; auto.
  destruct a0; destruct a'; simpl in *.
  - lia.
  - congruence.
  - congruence.
  - rewrite IHd; eauto.
Qed.

Theorem diskUpd_comm_lt : forall d a a' b b',
    a < a' ->
    diskUpd (diskUpd d a b) a' b' = diskUpd (diskUpd d a' b') a b.
Proof.
  intros.
  apply diskUpd_comm.
  lia.
Qed.

Theorem diskUpd_oob_noop : forall d a b,
    ~a < diskSize d ->
    diskUpd d a b = d.
Proof.
  induction d; simpl; intros; auto.
  destruct a0; simpl in *.
  - lia.
  - rewrite IHd; auto; lia.
Qed.

(** ** Theorems about diskShrink *)

Theorem diskShrink_size : forall d,
    diskSize d <> 0 ->
    diskSize (diskShrink d) = diskSize d - 1.
Proof.
  unfold diskSize, diskShrink; intros.
  rewrite firstn_length.
  rewrite min_l; lia.
Qed.

Theorem diskShrink_preserves : forall d a,
    a <> diskSize (diskShrink d) ->
    diskGet (diskShrink d) a = diskGet d a.
Proof.
  unfold diskShrink.
  induction d; simpl; intros; auto.
  destruct d; simpl in *.
  - destruct a0; try lia; simpl.
    destruct a0; auto.
  - destruct a0; simpl; auto.
    replace (length d - 0) with (length d) in * by lia.
    rewrite <- IHd; auto.
Qed.

Theorem diskShrink_diskUpd_last : forall d a b,
    a >= diskSize d - 1 ->
    diskShrink (diskUpd d a b) = diskShrink d.
Proof.
  unfold diskShrink; intros.
  destruct (eq_nat_dec a (diskSize d - 1)); subst.
  - clear H.
    rewrite diskUpd_size; unfold diskSize.
    induction d; simpl; auto.
    destruct d; simpl in *; auto.
    replace (length d - 0) with (length d) in * by lia.
    f_equal; auto.
  - rewrite diskUpd_oob_noop by lia; auto.
Qed.

Theorem diskShrink_diskUpd_notlast : forall d a b,
    a < diskSize d - 1 ->
    diskShrink (diskUpd d a b) = diskUpd (diskShrink d) a b.
Proof.
  unfold diskShrink.
  induction d; simpl; auto; intros.
  destruct a0; simpl; auto.
  - destruct d; simpl; auto.
  - destruct d; simpl in *; auto.
    replace (length d - 0) with (length d) in * by lia.
    rewrite <- IHd by lia.
    destruct a0; simpl; try rewrite diskUpd_size; unfold diskSize;
      replace (length d - 0) with (length d) by lia; auto.
Qed.

Hint Rewrite diskUpd_size : disk_size.
Hint Rewrite diskShrink_size using solve [ auto || lia ] : disk_size.

(** ** Theorems about diskUpds *)

Theorem diskUpds_neq : forall blocks d a a',
  a' < a \/ a' >= a + length blocks ->
  diskGet (diskUpds d a blocks) a' = diskGet d a'.
Proof.
  induction blocks; simpl; auto; intros.
  rewrite diskUpd_neq by lia.
  rewrite IHblocks; auto.
  lia.
Qed.

Theorem diskUpds_size : forall blocks d a,
    diskSize (diskUpds d a blocks) = diskSize d.
Proof.
  induction blocks; simpl; eauto; intros.
  rewrite diskUpd_size; auto.
Qed.

Theorem diskUpds_diskUpd_comm : forall blocks d a a' b,
  a' < a \/ a' >= a + length blocks ->
  diskUpd (diskUpds d a blocks) a' b = diskUpds (diskUpd d a' b) a blocks.
Proof.
  induction blocks; simpl; auto; intros.
  rewrite diskUpd_comm by lia.
  rewrite IHblocks; auto.
  lia.
Qed.

Theorem diskUpds_diskUpd_after : forall blocks d a b,
  diskUpd (diskUpds d a blocks) (a + length blocks) b =
  diskUpds d a (blocks ++ (b :: nil)).
Proof.
  induction blocks; simpl; auto; intros.
  - replace (a + 0) with a; auto.
  - rewrite diskUpd_comm by lia.
    rewrite <- IHblocks.
    replace (a0 + S (length blocks)) with (a0 + 1 + length blocks) by lia.
    reflexivity.
Qed.

Theorem diskUpds_diskUpd_before : forall blocks d a b,
  diskUpd (diskUpds d (a + 1) blocks) a b =
  diskUpds d a (b :: blocks).
Proof.
  reflexivity.
Qed.

(** ** Theorems about diskGets *)

Theorem diskGets_first : forall count d a,
  diskGets d a (count+1) = diskGet d a :: diskGets d (a+1) count.
Proof.
  intros.
  replace (count+1) with (S count) by lia.
  reflexivity.
Qed.

Theorem diskGets_last : forall count d a,
  diskGets d a (count+1) = diskGets d a count ++ (diskGet d (a+count) :: nil).
Proof.
  induction count; simpl; intros.
  - replace (a+0) with a by lia; auto.
  - rewrite IHcount.
    replace (a+1+count) with (a+S count) by lia; auto.
Qed.

Theorem diskGets_app : forall count0 count1 d a,
  diskGets d a (count0+count1) = diskGets d a count0 ++ diskGets d (a+count0) count1.
Proof.
  induction count0; simpl; auto; intros.
  rewrite IHcount0.
  replace (a+1+count0) with (a+S count0) by lia.
  auto.
Qed.

Theorem diskGets_length : forall d a count,
    length (diskGets d a count) = count.
Proof.
  intros.
  revert a.
  induction count; simpl; auto.
Qed.

Theorem diskGets_index : forall d a count i,
    i < count ->
    nth_error (diskGets d a count) i = Some (diskGet d (a+i)).
Proof.
  intros.
  generalize dependent i.
  revert a.
  induction count; simpl; intros.
  - lia.
  - destruct i; simpl.
    replace (a+0) with a by lia; auto.
    rewrite IHcount by lia.
    replace (a+1+i) with (a+S i) by lia; auto.
Qed.

Hint Rewrite diskGets_length : disk_size.
Section diskGets_proof.
Hint Rewrite nth_error_app1 using (autorewrite with disk_size in *; lia) : upd.
Hint Rewrite nth_error_app2 using (autorewrite with disk_size in *; lia) : upd.
Hint Rewrite diskGets_index using lia : upd.

Theorem diskGets_app_disk : forall d1 d2 a count,
    count >= length d1-a ->
    a < length d1 ->
    diskGets (d1 ++ d2) a count =
    diskGets d1 a (length d1 - a) ++ diskGets d2 0 (count - (length d1-a)).
Proof.
  intros.
  apply nth_error_ext_inbounds_eq.
  { repeat rewrite ?diskGets_length, ?app_length.
    lia. }
  intros i **.
  autorewrite with disk_size upd in *.
  rewrite diskGets_index by lia.
  destruct (lt_dec i (length d1 - a));
    unfold diskGet;
    autorewrite with disk_size upd in *.
  - auto.
  - unfold diskGet.
    do 2 f_equal.
    lia.
Qed.
End diskGets_proof.

Theorem diskGets_append_one : forall d1 a x count,
    a < length d1 ->
    a + count = S (length d1) ->
    diskGets (d1 ++ x::nil) a count =
    diskGets d1 a (length d1 - a) ++ (Some x::nil).
Proof.
  intros.
  rewrite diskGets_app_disk by lia.
  replace (count - (length d1 - a)) with 1 by lia; simpl; auto.
Qed.

Theorem diskUpd_diskGets_neq : forall count d a a0 v0,
  (a0 < a \/ a0 > a + count) ->
  diskGets (diskUpd d a0 v0) a count = diskGets d a count.
Proof.
  induction count; simpl; intros; auto.
  rewrite diskUpd_neq by lia.
  rewrite IHcount by lia.
  auto.
Qed.

Theorem diskUpds_diskGets_neq : forall count d a a0 vs,
  (a0 + length vs < a \/ a0 >= a + count) ->
  diskGets (diskUpds d a0 vs) a count = diskGets d a count.
Proof.
  induction count; simpl; intros; auto.
  rewrite diskUpds_neq by lia.
  rewrite IHcount by lia.
  auto.
Qed.

Theorem diskUpds_diskGets_eq : forall vs d a,
  a + length vs <= diskSize d ->
  diskGets (diskUpds d a vs) a (length vs) = map Some vs.
Proof.
  induction vs; simpl; intros; auto.
  rewrite diskUpd_eq.
  - rewrite diskUpd_diskGets_neq by lia.
    rewrite IHvs by lia.
    auto.
  - rewrite diskUpds_size. lia.
Qed.

Theorem append_size : forall d1 d2,
    diskSize (d1 ++ d2) = diskSize d1 + diskSize d2.
Proof.
  apply app_length.
Qed.

Hint Rewrite append_size : disk_size.
Hint Rewrite diskUpds_size : disk_size.

Theorem diskUpd_app1 : forall d1 d2 a v,
    a < length d1 ->
    diskUpd (d1 ++ d2) a v = diskUpd d1 a v ++ d2.
Proof.
  induction d1; simpl; intros.
  - lia.
  - destruct a0; simpl; auto.
    rewrite IHd1 by lia; auto.
Qed.

Theorem diskUpd_app2 : forall d1 d2 a v,
    a >= length d1 ->
    diskUpd (d1 ++ d2) a v = d1 ++ diskUpd d2 (a - length d1) v.
Proof.
  induction d1; simpl; intros.
  - replace (a-0) with a by lia; auto.
  - destruct a0; simpl; try lia.
    rewrite IHd1 by lia; auto.
Qed.

Theorem diskUpds_app1 : forall d1 d2 n v,
    n+length v < length d1 ->
  diskUpds (d1 ++ d2) n v = diskUpds d1 n v ++ d2.
Proof.
  intros.
  generalize dependent n.
  induction v; simpl; auto; intros.
  rewrite IHv by lia.
  rewrite diskUpd_app1; auto.
  autorewrite with disk_size.
  unfold diskSize; lia.
Qed.

Theorem diskUpds_app2 : forall d1 d2 n v,
  length d1 <= n ->
  diskUpds (d1 ++ d2) n v = d1 ++ diskUpds d2 (n - length d1) v.
Proof.
  intros.
  generalize dependent n.
  induction v; simpl; auto; intros.
  rewrite IHv by lia.
  rewrite diskUpd_app2 by lia.
  replace (n + 1 - length d1) with (n - length d1 + 1) by lia; auto.
Qed.

Theorem firstn_app_one : forall A (l: list A) n r,
    nth_error l n = Some r ->
    firstn (S n) l = firstn n l ++ r::nil.
Proof.
  intros.
  generalize dependent l.
  induction n; destruct l; simpl in *; intros; try congruence.
  f_equal.
  rewrite IHn; auto.
Qed.

Theorem firstn_log_app_one : forall (log: list block) n r,
    diskGet log n = Some r ->
    firstn (S n) log = firstn (n) log ++ r::nil.
Proof.
  intros.
  generalize dependent log.
  induction n; destruct log; simpl in *; intros; try congruence.
  f_equal.
  rewrite IHn; auto.
Qed.

(** We combine all of the above theorems into a hint database called "upd".
    This means that, when you type [autorewrite with upd] in some Coq proof,
    Coq will try to rewrite using all of the hints in that database.

    The [using] part of the hint tells Coq that all of the side conditions
    associated with the rewrite must be solved using the tactic specified
    in the [using] clause.  This prevents Coq from applying a rewrite rule
    if some side condition (like an address being out-of-bounds) cannot be
    immediately proven.
  *)

Local Ltac solve_disk_size :=
  solve [ autorewrite with disk_size; (auto || lia) ].

Hint Rewrite diskUpd_eq using solve_disk_size : upd.
Hint Rewrite disk_oob_eq using solve_disk_size : upd.
Hint Rewrite diskUpd_oob_eq using solve_disk_size : upd.
Hint Rewrite diskUpd_size : upd.
Hint Rewrite diskUpd_neq using (solve [ auto ]) : upd.
Hint Rewrite diskUpd_comm_lt using solve_disk_size : upd.
Hint Rewrite diskUpd_none using (solve [ auto ]) : upd.

Hint Rewrite diskUpd_same using (solve [ auto ]) : upd.
Hint Rewrite diskUpd_oob_noop using solve_disk_size : upd.
Hint Rewrite diskUpd_twice : upd.

Hint Rewrite diskUpds_neq using solve_disk_size : upd.
Hint Rewrite diskUpds_diskUpd_comm using solve_disk_size : upd.
Hint Rewrite diskUpds_size : upd.

Hint Rewrite diskUpd_diskGets_neq using solve_disk_size : upd.
Hint Rewrite diskUpds_diskGets_neq using solve_disk_size : upd.
Hint Rewrite diskUpds_diskGets_eq using solve_disk_size : upd.

Hint Rewrite diskShrink_size using solve_disk_size : upd.
Hint Rewrite diskShrink_preserves using solve_disk_size : upd.
Hint Rewrite diskShrink_diskUpd_last using solve_disk_size : upd.
Hint Rewrite diskShrink_diskUpd_notlast using solve_disk_size : upd.
