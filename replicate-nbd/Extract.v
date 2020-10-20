Cd "replicate-nbd/extract/".

Require Import ExtrHaskellNatInteger.
Require Import ExtrHaskellBasic.

Extraction Language Haskell.

Require Import Lab4.ReplicatedServer.

Separate Extraction size serverLoop init.

Cd "../../".
