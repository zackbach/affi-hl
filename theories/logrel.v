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
Program Definition expr_interp (V : VR) : ER :=
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

Fixpoint type_interp (A : ty) : VR :=
  match A with
  | One => unit_interp
  | Tensor A B => tensor_interp (type_interp A) (type_interp B)
  | Fun A B => fun_interp (type_interp A) (type_interp B)
  | Unq A => unq_interp (type_interp A)
  end.
(* I copied the levels over from examples stlc logrel *)
Notation "𝒱⟦ τ ⟧" := (type_interp τ) (at level 0, τ at level 70).

(* I don't fully understand this [* map] concrete syntax *)
Program Definition context_interp (Γ : gmap string ty) γ : iProp Σ :=
  ([∗ map] x ↦ A; v ∈ Γ; γ, 𝒱⟦ A ⟧ v)%I.
Notation "𝒢⟦ Γ ⟧" := (context_interp Γ) (at level 0, Γ at level 70).

Definition sem_typed Γ e τ : Prop :=
  ⊢ ∀ γ, 𝒢⟦ Γ ⟧ γ -∗ ℰ (𝒱⟦ τ ⟧) (subst_map γ e).
Notation "Γ ⊨ e : τ" := (sem_typed Γ e τ) (at level 74, e, τ at next level).