From affi Require Import source.
From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Import metatheory.
From iris.prelude Require Import options.

Implicit Types
  (Γ : gmap string ty)
  (γ : gmap string val)
  (* Without this, I was getting inference errors,
     maybe bc missing imports. This is probably 
     related to the WP typeclass error below... *)
  (Σ : gFunctors)
.

(* From here on, heapGS is one of the functors in Σ *)
Context `{heapGS Σ}.

Notation ER := (expr -> iProp Σ).
Notation VR := (val -> iProp Σ).

Program Definition expr_interp (V : VR) : ER :=
  (λ e, WP e {{ V }})%I.

Definition unit_interp : VR := 
  (λ v, ⌜v = #()⌝)%I.

Definition tensor_interp (V1i V2i : VR) : VR :=
  (λ v, (∃ v1 v2, ⌜v = (v1, v2)%V⌝ ∗ V1i v1 ∗ V2i v2))%I.

Definition fun_interp (V1i V2i : VR) : VR :=
  (λ v, (∀ w, (V1i w -∗ expr_interp V2i (v w))))%I.

Fixpoint type_interp (A : ty) : VR :=
  match A with
  | One => unit_interp
  | Tensor A B => tensor_interp (type_interp A) (type_interp B)
  | Fun A B => fun_interp (type_interp A) (type_interp B)
  | Unq A => unq_interp (type_interp A)
  end.
(* Notation "𝒱⟦ τ ⟧" := (type_interp A). *)

Program Definition context_interp (Γ : gmap string type) (γ : gmap string val) : iPropO Σ :=
  (* ZACK NOTE: idk what [∗ map] is. I think it is saying "forall A;v in Γ; γ" ... *)
  ([∗ map] x ↦ A; v ∈ Γ; γ, 𝒱 A δ v)%I.


Definition sem_typed (n : nat) Γ e A : Prop :=
  (* ZACK: As a part of this, we specify the semtype for ℰ relation *)
  ⊢ ∀ δ γ, 𝒢 Γ γ δ -∗ ℰ (𝒱 A δ) (subst_map γ e).
Notation "'TY' Δ ;  Γ ⊨ e : A" := (sem_typed Δ Γ e A) (at level 74, e, A at next level).
