# 6.826 POCS Labs

[![Build Status](https://travis-ci.com/mit-pdos/6.826-labs.svg?token=1SPwqpqUkmsUej6KT47u&branch=master)](https://travis-ci.com/mit-pdos/6.826-labs)

## Lab 1: StatDB

In this lab, you will familiarize yourself with the lab infrastructure,
in the context of simple procedures that use variables.  The first part
of the lab exposes you to writing code, specifications, and proofs,
as well as dealing with loop invariants.

In the second part of the lab, you will get experience with abstraction
relations, by implementing a simple "database" that supports adding
numbers and getting the mean of the numbers added so far. Your proof
will connect the implementation (which only tracks the count and the sum)
to a specification that tracks all the input numbers.

To run your code, compile with `make bin/statdb-cli` and then run
`./bin/statdb-cli`. Exit by pressing `Ctrl-c`.

## Lab 2: Remapping a bad sector

In this lab, you will implement an interface to a disk that remaps addresses to
avoid a bad sector. We provide a specification
[BadBlockAPI](src/Lab2/BadBlockAPI.v) that has one bad sector in a known
location and a specification [OneDiskAPI](src/Common/OneDiskAPI.v) for a normal
disk. You will implement the clean one disk API on top of the bad block API (for
a disk that is one block smaller).

You can run your code as a Linux block device using NBD. If you're on macOS,
you'll need a Linux VM to try this out (you won't need to install Coq or Haskell
on it, though). **Running your code is optional** in this lab - we're only
checking your proofs. You should still run `make` to compile the Coq code and
make sure your proofs check.

### Overview of NBD

[Network Block Device (NBD)](https://nbd.sourceforge.io/) is a Linux kernel
feature that lets you use a remote server as a block device. Every time the
client reads or writes `/dev/nbd0`, nbd will make a request over TCP to the
server.

Ordinarily this lets you use disk space or devices from remote machines. We use
it to _implement_ a block device as a userspace program, then export it by
implementing the NBD protocol.

### Running the remapped disk as an NBD server

The high-level overview is that you'll run `remap-nbd` to start an NBD server
with your code, then connect to it from Linux with the standard Linux client,
`nbd-client`. Then reads and writes to the special block device `/dev/nbd0` will
be implemented using `remap-nbd` by running code extracted from Coq.

First, run `make bin/remap-nbd` to compile the Coq code and `bin/remap-nbd`.

Once you've compiled, initialize the disk image (defaults to a 100MB disk):

```
./bin/remap-nbd init
```

And then run the server:

```
./bin/remap-nbd start [--debug]
```

The disk's contents are stored in `disk0.img` in the current directory.

First, load the `nbd` kernel module.

```
sudo modprobe nbd
```

Connect to it from a client:

```
sudo nbd-client localhost /dev/nbd0
```

Use it a bit (you can do this without sudo by adding yourself to the disk group:
`sudo usermod -a -G disk $USER`):

```
mkfs.ext4 -E root_owner /dev/nbd0
sudo mkdir /mnt/nbd
sudo mount /dev/nbd0 /mnt/nbd
mkdir /mnt/nbd/dir
echo "some text" > /mnt/nbd/foo
ls /mnt/nbd
sudo umount /mnt/nbd
```

Disconnect the block device:

```
sudo nbd-client -d /dev/nbd0
```

The `remap-nbd` server won't exit since it continually accepts new connections,
but you can send an interrupt signal with `Ctrl-C`.

## Lab 3: Write-ahead logging

In this lab, you'll implement a simple API and prove that it is atomic
with respect to crashes.

Your job is to implement an append-only log that allows the caller to add
several blocks to this log at the same time.  If a crash occurs in the
middle of adding the blocks to the log, either the log should have its
old contents, or the new contents (with all of the new blocks present),
but no other intermediate state.

The implementation uses a regular disk with a header and the log blocks
stored directly on disk.  You will have to ensure crash-safety by updating
the log blocks and the header in the right order.

## Lab 4: Replicated Disk

In this lab, you'll prove a disk replication system correct. The API we provide you gives access to disks and allows one (but not both) to fail at any time. On top of these disks, you'll support a straightforward one-disk API without failures. The disk replication should work even if the computer crashes, though for this lab you'll need a recovery procedure to make this work out.

This lab introduces two big ideas:

- Concurrency. The replicated disk needs to handle one of the two disks failing at any time, which is a form of concurrency.
- Recovery. In lab 3, the implementation was atomic on its own. The replicated disk has the right behavior under crashes only after running a recovery procedure to fix up discrepancies that can be caused by crashes at inopportune moments.

## Notes

Please do not post your solutions publicly. We plan to use this material for
future editions of 6.826.
