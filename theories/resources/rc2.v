From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Import proofmode.
From iris.heap_lang Require Import notation lang.
From iris.algebra Require Import numbers csum excl gmap.
From iris.prelude Require Import options.
From affi.resources Require Import agree.

(* I'm not sure what to do about this one...
   since now Σ will be needed before getting any of resO, resR, etc
   however I think it can still work? it's more a question of morality
   
   EDIT: I am less and less sure about this one...
   Maybe we can make it take in a COFE and later fill it with either
   a hole or (iProp Σ) ??? See cellR' and res' below *)
(* Variable Σ : gFunctors. *)

(* Definition cellR (A: ofe) : cmra := 
  csumR (agreeR A) (agreeR (laterO (iPropO Σ))). *)

Definition cellR' (A B : ofe) `{!Cofe B} : cmra := 
  csumR (agreeR A) (agreeR (laterO B)).

(* NOTE: I feel less sure about the presence of this leibnizO,
   and I'm not sure how something like this would be done if not discrete.

   It feels like this works "by chance" since we turn res from Type -> OFE.
   And if we didn't want it to be discrete (aka use the cmra itself that we
   are defining), that would break due to circularity / wrapping stuff.
   
   I think that's the problem that we run into with the functor stuff: we
   can't turn an arbitrary Type into the functor we need *)

(* Inductive res := Res {
  res_car :> gmapR loc (cellR (leibnizO res))
}. *)

Inductive res_pre (B : ofe) `{!Cofe B} := ResPre {
  res_pre_car :> gmapR loc (cellR' (leibnizO (res_pre B)) B)
}.
Global Arguments ResPre {_} {_}.
Global Arguments res_pre_car {_} {_}.

(*

res := gmapR loc (csumR (agreeR (leibnizO res)) (agreeR (laterO (iPropO Σ))))
F (X, X⁻) := gmapUR loc (csumR (agreeR resR) (agreeR (laterO X)))

We want to be able to define things, but I don't think we will be able to
use the built-in combinators really. Or at least not everywhere... since
we won't be able to refer to itself in the combinator definition. IDK!

A possible bigger problem is that for a manual construction, we would need
to use resR or similar. BUT that runs into issues, because we need Σ for 
resR, but _cannot_ use Σ when defining the functor (that's the whole point
of the hole).

*)

Section res.
Context {B : ofe} `{!Cofe B}.

Local Instance res_dist : Dist (res_pre B) := λ n x y,
  res_pre_car x ≡{n}≡ res_pre_car y.

Local Instance res_equiv : Equiv (res_pre B) := λ x y,
  res_pre_car x ≡ res_pre_car y.

Definition res_ofe_mixin : OfeMixin (res_pre B).
Proof. by apply iso_ofe_mixin with res_pre_car. Qed.

Canonical Structure resO := Ofe (res_pre B) res_ofe_mixin.

Local Instance gmap_unit_instance : Unit (res_pre B) := ResPre ∅.
Local Instance gmap_op_instance : Op (res_pre B) := λ x y,
  ResPre (res_pre_car x ⋅ res_pre_car y).
Local Instance gmap_pcore_instance : PCore (res_pre B) := λ x,
  pcore (res_pre_car x) ≫= (λ x, Some (ResPre x)).

Local Instance gmap_valid_instance : Valid (res_pre B) := λ x,
  ✓ (res_pre_car x).
Local Instance gmap_validN_instance : ValidN (res_pre B) := λ n x, 
  ✓{n} (res_pre_car x).

Definition res_cmra_mixin : CmraMixin (res_pre B).
Proof. by apply iso_cmra_mixin with ResPre res_pre_car. Qed.

Canonical Structure resR : cmra := Cmra (res_pre B) res_cmra_mixin.
End res.

(* Really we want the typeclass instance to be implicit *)
Global Arguments resR : clear implicits.

(* We probably would want to change the definitons above to be pre,
   and then turn things into _the real_ res or something. 
   Or maybe just keep this implicit, it's more for proof-of-concept
Definition res' := res_pre (iPropO Σ).  *)

Class resG Σ := { res_inG : inG Σ (resR (iProp Σ) _) }.
Local Existing Instances res_inG.

(* This shows that at least we can get the definition working
   without having to depend on Σ *)

(* Definition resΣ : gFunctors := #[GFunctor ].
Instance subG_resΣ {Σ} : subG resΣ Σ → resG Σ.
Proof. solve_inG. Qed. *)

(* I don't know if this would even work. It doesn't depend on Σ directly
   any more, but will we be able to fill this in with the hole??
   
   We would have to prove that res_pre gives us a cmra for any B,
   then we specialize for res' *)

Definition cellRF (A : oFunctor) : rFunctor := 
  csumRF (agreeRF A) (agreeRF (▶ ∙)).
