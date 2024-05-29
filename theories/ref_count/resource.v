From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Import proofmode.
From iris.heap_lang Require Import notation lang.
From iris.algebra Require Import numbers csum excl gmap.
From iris.prelude Require Import options.
From affi.ref_count Require Import agree.

(* GOAL: define a resource algebra over an inductively defined
   carrier in an ergonomic way, using Iris built-ins when possible. *)

(* FIRST PROBLEM: the naive definition does not go through due
   to strict positivity requirement: 
  
Definition cellR (A : Type) `{EqDecision A} : cmra := 
  csumR (exclR (leibnizO val)) (prodR positiveR (agreeR A)).

Inductive res := 
| Res : gmapR loc (cellR res) -> res. *)

(* IDEA: define a new version of `agree` that uses `option`
   FAILS: requires {EqDecision A} to define composition, preventing
   us from using it inductively: 

Definition cellR (A : Type) `{EqDecision A} : cmra := 
  csumR (exclR (leibnizO val)) (prodR positiveR (dagreeR A)).

Inductive res := 
| Res : gmapR loc (cellR res) -> res. *)

(* Therefore, we need to try something that doesn't use EqDecision *)

(* IDEA: try to use standard list version
   FAILS: due to positivity 

   IDEA: try to use the gset version from Semantics notes
   FAILS: they also need EqDecision for non-empty check

   IDEA: use standard list version, but _without_ non-empty restriction? 
   FAILS: literally not a resource algebra: ✓ (emp ⋅ good) but NOT ✓ emp 
*)

(* CURRENT VERSION: use a new version of agree that still has non-empty
   list underlying, but uses a different, strictly positive definition *)

Definition cellR (A : ofe) : cmra := 
  csumR (exclR (leibnizO val)) (prodR positiveR (agreeR A)).

Inductive res := Res {
  res_car :> gmapR loc (cellR (leibnizO res))
}.

(* NEXT PROBLEM: this is not actually a `cmra`, and we cannot just use
   it as such. I tried to define some like coercion stuff, which didn't
   work properly.
   
   ATTEMPT: lift from `res_car` to `res` itself pointwise *)

Local Instance res_dist : Dist res := λ n x y,
  res_car x ≡{n}≡ res_car y.

Local Instance res_equiv : Equiv res := λ x y,
  res_car x ≡ res_car y.

(* Manual version (discovered to be unnecessary):

Definition res_ofe_mixin : OfeMixin res.
Proof.
  split; rewrite /dist /res_dist /equiv /res_equiv; intros *.
  - apply equiv_dist.
  - split; auto. intros ? y ?; by transitivity (res_car y); done.
  - apply dist_lt.
Qed. *)

Definition res_ofe_mixin : OfeMixin res.
Proof. by apply iso_ofe_mixin with res_car. Qed.

Canonical Structure resO := Ofe res res_ofe_mixin.

(* If this needs to be made into a Cofe, this is where it can be lifted,
   alongside other properties from the gmap RA like discrete, equality *)

(* Q: will this _suck_ to use (aka to look things up, etc)? I hope
   not, since the coercion above should turn into gmap for us *)

Local Instance gmap_unit_instance : Unit res := Res ∅.
Local Instance gmap_op_instance : Op res := λ x y,
  Res (res_car x ⋅ res_car y).
Local Instance gmap_pcore_instance : PCore res := λ x,
  pcore (res_car x) ≫= (λ x, Some (Res x)).

(* If we were to define a richer notion of validity, this is where
   we would do it. We omit this, and defer to store satisfaction, as
   that is what the borrowing model will be doing. To enrich, we could
   start from here, and use iso_cmra_mixin_restrict_validity *)
Local Instance gmap_valid_instance : Valid res := λ x,
  ✓ (res_car x).
Local Instance gmap_validN_instance : ValidN res := λ n x, 
  ✓{n} (res_car x).

Definition res_cmra_mixin : CmraMixin res.
Proof. by apply iso_cmra_mixin with Res res_car. Qed.

Canonical Structure resR : cmra := Cmra res res_cmra_mixin.

(* Again, more things could go in here (lifting) *)

Class resG Σ := { res_inG : inG Σ resR }.
Local Existing Instances res_inG.

Definition resΣ : gFunctors := #[GFunctor resR].
Instance subG_resΣ {Σ} : subG resΣ Σ → resG Σ.
Proof. solve_inG. Qed.

(* ANOTHER OPTION (probably easiest...): just define everything
   directly over the inductive carrier, optionally picking 
   definitions up from pre-existing combinators 

Inductive res :=
| Res : gmap loc cell -> res
with cell :=
| Own : val -> cell
| Shr : positive -> res -> cell. 

Note that this would be very annoying for the borrowing resource,
since it is higher-order (and relies on iProp) *)