From affi Require Import source.
From iris.program_logic Require Import weakestpre.
From iris.proofmode Require Import proofmode tactics.
From iris.heap_lang Require Import proofmode.
From iris.heap_lang Require Import primitive_laws metatheory.
From iris.heap_lang Require Import lang notation.
From iris.prelude Require Import options.

(* From here on, heapGS (from primitive_laws) is one of the functors in Σ *)
Context `{heapGS Σ}.

Notation ER := (expr -> iProp Σ).
Notation VR := (val -> iProp Σ).

(* We supply the value relation that must hold of the result,
   instead of being parameterized by the type like normal *)
Definition expr_interp (V : VR) : ER :=
  (λ e, WP e {{ V }})%I.
Notation ℰ := expr_interp.


Definition unit_interp : VR := 
  (λ v, ⌜v = #()⌝)%I.

Definition tensor_interp (V1i V2i : VR) : VR :=
  (λ v, (∃ v1 v2, ⌜v = (v1, v2)%V⌝ ∗ V1i v1 ∗ V2i v2))%I.

Definition fun_interp (V1i V2i : VR) : VR :=
  (λ v, (∀ w, (V1i w -∗ expr_interp V2i (v w))))%I.

Definition unq_interp (Vi : VR) : VR :=
  (λ v, ∃ (l : loc) vl, ⌜v = #l⌝ ∗ l ↦ vl ∗ Vi vl)%I.

Fixpoint type_interp (τ : ty) : VR :=
  match τ with
  | One => unit_interp
  | Tensor A B => tensor_interp (type_interp A) (type_interp B)
  | Fun A B => fun_interp (type_interp A) (type_interp B)
  | Unq A => unq_interp (type_interp A)
  end.
(* I copied the levels over from examples stlc logrel *)
Notation "𝒱⟦ τ ⟧" := (type_interp τ) (at level 0, τ at level 70).


(* I don't fully understand this [* map] concrete syntax *)
Definition context_interp (Γ : gmap string ty) γ : iProp Σ :=
  ([∗ map] x ↦ τ; v ∈ Γ; γ, 𝒱⟦ τ ⟧ v)%I.
Notation "𝒢⟦ Γ ⟧" := (context_interp Γ) (at level 0, Γ at level 70).

(* copied from other developments, IDK why *)
Global Opaque context_interp.

Definition sem_typed Γ e τ : Prop :=
  ⊢ ∀ γ, 𝒢⟦ Γ ⟧ γ -∗ ℰ (𝒱⟦ τ ⟧) (subst_map γ e).
Notation "Γ ⊨ e : τ" := (sem_typed Γ e τ) (at level 74, e, τ at next level).


(* Taken from Semantics notes *)
Lemma context_interp_insert Γ γ τ v x :
  𝒱⟦ τ ⟧ v -∗
  𝒢⟦ Γ ⟧ γ -∗
  𝒢⟦ (<[ x := τ ]> Γ) ⟧ (<[ x := v ]> γ).
Proof.
  iIntros "Hv Hγ". iApply (big_sepM2_insert_2 with "[Hv] [Hγ]"); done.
Qed.

Lemma context_interp_lookup Γ γ τ x :
  ⌜Γ !! x = Some τ⌝ -∗
  𝒢⟦ Γ ⟧ γ -∗
  ∃ v, ⌜γ !! x = Some v⌝ ∧ 𝒱⟦ τ ⟧ v.
Proof.
  iIntros (Hlook) "Hγ".
  iPoseProof (big_sepM2_lookup_l with "Hγ") as "Hτ"; done.
Qed.

(* This totally doesn't hold of my current definition *)
Lemma this_should_hold Γ1 Γ2 γ :
  𝒢⟦ Γ1 ∪ Γ2 ⟧ γ ⊣⊢ 𝒢⟦ Γ1 ⟧ γ ∗ 𝒢⟦ Γ2 ⟧ γ.
Proof.
  Admitted.


(* REDEFINITION IDEAS:
- I really only need ⊢ direction to hold for `this_should_hold`,
  but the bigsep list ++ stuff should give me enough for both.
- I can try to work back wards from `context_interp_lookup`
- Idea: still have `γ : gmap` but have `Γ` as a list of pairs:
  - For every pair (x, τ) in Γ, we need 𝒱⟦ τ ⟧ γ(x)
- Would require new `lookup` in `Γ` now, prob just like `!!`
- Problem: this makes adding to the context bad, 
  since we don't delete old one
  - We would have to have something like C-cons
  - Maybe just quantify over fresh names in the compile relation
*)