Require Import POCS.
Require Import StatDbImpl.
Require Import VariablesImpl.


Module statdb := StatDB Vars.

Axiom get_new_item : proc nat.
Axiom report_mean : option nat -> proc unit.


CoFixpoint loop : proc unit :=
  m <- statdb.mean;
  _ <- report_mean m;
  x <- get_new_item;
  _ <- statdb.add x;
  loop.

Definition cli : proc unit :=
  init_ok <- statdb.init;
  match init_ok with
  | Initialized =>
    loop
  | InitFailed =>
    Ret tt
  end.

Extract Constant get_new_item => "CLI.Stubs.getNewItem".
Extract Constant report_mean => "CLI.Stubs.reportMean".
