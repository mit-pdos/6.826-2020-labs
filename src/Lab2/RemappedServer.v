Require Import POCS.

Require Import RemappedDiskImpl.
Require Import BadBlockImpl.
Require Import Common.NbdServer.


Module d := RemappedDisk BadBlockDisk.
Module s := NBDServer d.

Definition serverLoop := s.serverLoop.
Definition size := s.size.
Definition init := s.init.
