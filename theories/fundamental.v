From affi Require Import source.
From affi Require Import logrel.
From iris.heap_lang Require Import notation lang.

Lemma compat_unit Γ :
  Γ ⊨ #() : One.
Proof.
  Admitted.

Lemma compat_var Γ (x : string) τ :
  Γ !! x = Some τ →
  Γ ⊨ x : τ.
Proof.
  Admitted.

Lemma compat_lam Γ (x : string) e τ1 τ2 :
  (<[x := τ1]> Γ) ⊨ e : τ2 →
  Γ ⊨ (λ: x, e) : Fun τ1 τ2.
Proof.
  Admitted.

Lemma compat_app Γ1 Γ2 e1 e2 τ1 τ2 :
  Γ1 ⊨ e1 : Fun τ1 τ2 →
  Γ2 ⊨ e2 : τ1 →
  Γ1 ∪ Γ2 ⊨ e1 e2 : τ2.
Proof.
  Admitted.

Lemma compat_pair Γ1 Γ2 e1 e2 τ1 τ2 :
  Γ1 ⊨ e1 : τ1 →
  Γ2 ⊨ e2 : τ2 →
  Γ1 ∪ Γ2 ⊨ (e1, e2) : (Tensor τ1 τ2).
Proof.
  Admitted.

Lemma compat_split Γ1 Γ2 (x1 x2 : string) e1 e2 τ1 τ2 τ :
  Γ1 ⊨ e1 : Tensor τ1 τ2 →
  <[x2:=τ2]> (<[x1:=τ1]> Γ2) ⊨ e2 : τ →
  Γ1 ∪ Γ2 ⊨ (let: "tmp" := e1 in 
              let: x1 := Fst "tmp" in 
              let: x2 := Snd "tmp" in e2) : τ.
Proof.
  Admitted.

Lemma compat_new Γ e τ :
  Γ ⊨ e : τ →
  Γ ⊨ ref e : Unq τ.
Proof.
  Admitted.

Lemma compat_swap Γ1 Γ2 e1 e2 τ1 τ2 :
  Γ1 ⊨ e1 : Unq τ1 →
  Γ2 ⊨ e2 : τ2 →
  Γ1 ∪ Γ2 ⊨ (let: "l" := e1 in 
              let: "r" := ! "l" in 
              let: "_" := "l" <- e2 in 
                ("l", "r")) : Tensor (Unq τ2) τ1.
Proof.
  Admitted.

Local Hint Resolve compat_unit compat_var compat_lam compat_app
  compat_pair compat_split compat_new compat_swap : core.

Lemma fundamental Γ a τ e :
  Γ ⊢ a : τ ~~> e →
  Γ ⊨ e : τ.
Proof.
  induction 1; eauto.
Qed.