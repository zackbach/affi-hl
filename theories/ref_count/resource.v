From affi.ref_count Require Import dagree.
From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Import proofmode.
From iris.heap_lang Require Import notation lang.
From iris.algebra Require Import numbers csum excl gmap.
From iris.prelude Require Import options.

(* IDEA: define a new version of `agree` that uses `option`
   FAILS: requires {EqDecision A} to define composition, preventing
   us from using it inductively: 

Definition cellR (A : Type) `{EqDecision A} : cmra := 
  csumR (exclR (leibnizO val)) (prodR positiveR (dagreeR A)).

Inductive resR := 
| Res : gmapR loc (cellR resR) -> resR. *)

(* Therefore, we need to try something that doesn't use EqDecision *)

(* IDEA: try to use standard list version
   - FAILS: due to positivity 

   IDEA: try to use the gset version from Semantics notes
   - FAILS: they also need EqDecision for non-empty check

   IDEA: use standard list version, but _without_ non-empty restriction? 
   - FAILS: literally not a resource algebra: ✓ (emp ⋅ good) but NOT ✓ emp 
*)

(* CURRENT VERSION: use a new version of agree that still has non-empty
   list underlying, but uses a different, strictly positive definition *)

Definition cellR (A : Type) : cmra := 
  csumR (exclR (leibnizO val)) (prodR positiveR (dagreeR A)).

Inductive resR := 
  | Res : gmapR loc (cellR resR) -> resR.

(* Now, the notion of validity here is lacking, so we need to define
   our own. Luckily, we can easily augment resR with a new notion
   using iso_cmra_mixin_restrict_validity *)

(* ANOTHER OPTION (probably easiest...): just define everything
   directly over the inductive carrier, optionally picking 
   definitions up from pre-existing combinators 

Inductive res :=
| Res : gmap loc cell -> res
with cell :=
| Own : val -> cell
| Shr : positive -> res -> cell. 
*)