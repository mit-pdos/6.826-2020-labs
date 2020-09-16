# Replicated NBD server

A Network Block Device server that uses the replicated disk implementation from Coq.

## Overview of NBD

[Network Block Device (NBD)](https://nbd.sourceforge.io/) is a Linux kernel feature that lets you use a remote server as a block device. Every time the client reads or writes `/dev/nbd0`, nbd will make a request over TCP to the server.

Ordinarily this lets you use disk space or devices from remote machines. We use it to _implement_ a block device as a userspace program, then export it by implementing the NBD protocol.

## Running the replicated disk as an nbd server

The high-level overview is that you run a Haskell binary `replicate-nbd` for the nbd server, then connect to it from Linux using the standard Linux client, `nbd-client`. You can then use `/dev/nbd0` has a regular block device, but its operations will be implemented by `replicate-nbd` using the extracted Coq code.

The only tools you need are `stack` for building the server and `nbd-client` for
connecting to it. If you're not familiar
with [Stack](https://docs.haskellstack.org/en/stable/GUIDE/), it's a build tool
for Haskell aiming for reproducible, local builds. Using Stack, compiling will
fetch, build, and use stable versions of all dependencies (including GHC
itself), independent of the rest of your Haskell setup.

We first compile the Coq code, which also extracts to Haskell, then we can compile this Haskell project with `stack`:

```
make
cd replicate-nbd
stack setup # one-time download of compiler
stack build
```

Once you've compiled, initialize the disks:

```
stack exec -- replicate-nbd init
```

And then run the server:

```
stack exec -- replicate-nbd start [--debug]
```

The underlying disks will be `disk0.img` and `disk1.img` in the current
directory, which are initialized to two empty 100MB files if they don't exist.
Run with `--help` to see how to customize these.

First, load the `nbd` kernel module (TODO: is this Arch-specific? what happens
on Ubuntu?). On Arch, you can do this on boot by creating a file
`/etc/modules-load.d/nbd.conf` with just 'nbd' (see
https://wiki.archlinux.org/index.php/kernel_modules).

```
sudo modprobe nbd
```

Connect to it from a client:

```
sudo nbd-client localhost /dev/nbd0
```

Note that you can use `nbd` over the network (this is what it's intended for). I
use this to run the server from my Mac but mount it in a Linux virtual machine,
by accessing the host machine over a VirtualBox NAT. I believe this just entails
using 10.0.2.2 as the hostname for `nbd-client` rather than `localhost` (this is
with the default networking configuration, where under "Network" the adapter has
"Attached to:" set to "NAT").

Use it a bit (you can do this without sudo by adding yourself to the disk
group: `sudo usermod -a -G disk $USER`) (TODO: possibly Arch-specific):

```
mkfs.ext4 -E root_owner /dev/nbd0
sudo mkdir /mnt/nbd
sudo mount /dev/nbd0 /mnt/nbd
mkdir /mnt/nbd/dir
ls /mnt/nbd
sudo umount /mnt/nbd
```

Disconnect the block device:

```
sudo nbd-client -d /dev/nbd0
```

The server won't exit since it continually accepts new connections, but you can
send an interrupt signal with `Ctrl-C`.
