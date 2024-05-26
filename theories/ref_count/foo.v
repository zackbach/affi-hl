From iris.program_logic Require Export weakestpre.
From iris.base_logic.lib Require Export invariants.
From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Import proofmode.
From iris.heap_lang Require Import notation lang.
From iris.algebra Require Import numbers csum excl gmap.
From iris.prelude Require Import options.

Definition cellR (A : ofe) : cmra := 
  csumR (exclR (leibnizO val)) (prodR positiveR (agreeR A)).

(* Inductive resR := 
| Res : gmapR loc (cellR (leibnizO resR)) -> resR. *)

Definition assoc_map A B := list (A * B).

Inductive bar := 
| Bar : gmapR nat (exclR (leibnizO bar)) -> bar.

(* Inductive baz := 
| Baz : gmapR nat (agreeR (leibnizO baz)) -> baz. *)

(* Print agree. *)


Inductive res :=
| Res : gmap loc cell -> res
with cell :=
| Own : val -> cell
| Shr : positive -> res -> cell.
