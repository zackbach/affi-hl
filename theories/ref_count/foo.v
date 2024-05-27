From iris.program_logic Require Export weakestpre.
From iris.base_logic.lib Require Export invariants.
From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Import proofmode.
From iris.heap_lang Require Import notation lang.
From iris.algebra Require Import numbers csum excl gmap.
From iris.prelude Require Import options.
From affi.ref_count Require Import dagree_eqd.

(* FAIL: cellR needs resR to be EqDecision to define,
   but it can't be EqDecision until it is actually defined... *)

Definition cellR (A : Type) `{EqDecision A} : cmra := 
  csumR (exclR (leibnizO val)) (prodR positiveR (dagreeR A)).

(* FAILS:
  Inductive resR := 
  | Res : gmapR loc (cellR resR) -> resR.
*)

(* Therefore, we need to try something that doesn't use EqDecision *)

(* IDEA: try to use the gset version from Semantics notes
   - FAILS: they also need EqDecision for non-empty check
   IDEA: try to use standard list version
   - FAILS: due to positivity 
   IDEA: use standard list version, but _without_ non-empty restriction? 
   - FAILS: literally not a resource algebra: ✓ (emp ⋅ good) but NOT ✓ emp 
   IDEA: use a jank list version for non-empty... 
*)

(* FAILS:
  Inductive baz := 
  | Baz : gmap nat (agree (leibnizO baz)) -> baz.
*)


Inductive res :=
| Res : gmap loc cell -> res
with cell :=
| Own : val -> cell
| Shr : positive -> res -> cell.