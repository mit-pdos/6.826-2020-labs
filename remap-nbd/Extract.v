Cd "remap-nbd/extract/".

Require Import ExtrHaskellBasic.
Require Import ExtrHaskellNatInteger.

Extraction Language Haskell.

Require Import Lab2.RemappedServer.

Extract Inlined Constant Compare_dec.lt_dec => "((Prelude.<) :: Prelude.Integer -> Prelude.Integer -> Prelude.Bool)".

Separate Extraction serverLoop init size.

Cd "../../".
