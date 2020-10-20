Require Import POCS.

Require Import ReplicatedDiskImpl.
Require Import TwoDiskImpl.
Require Import TwoDiskBaseImpl.
Require Import Common.NbdServer.


Module td := TwoDisk TwoDiskBase.
Module rd := ReplicatedDisk td.
Module s := NBDServer rd.

Definition serverLoop := s.serverLoop.
Definition size := s.size.
Definition init := s.init.
