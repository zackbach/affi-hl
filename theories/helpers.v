From affi Require Import source logrel.
From iris.proofmode Require Import proofmode tactics.
From iris.heap_lang Require Import proofmode.
From iris.heap_lang Require Import primitive_laws metatheory.
From iris.prelude Require Import options.


(* From Semantics notes:
   The following tactic will be useful for applying bind:
   [smart_wp_bind e spat v "Hv" He] will bind the subexpression [e],
   using spat, then will apply the semantic typing assumption [He]
   for it, introducing the resulting value [v] and interpretation ["Hv"]
   
   I added in the spat thing since we have to split hypotheses,
   but I don't know what `constr` is: I just copied template lol
   Apparently it means to pass in the argument as a resolved Coq term?
 *)
Tactic Notation "smart_wp_bind"
    uconstr(e) constr(pat) ident(v) constr(Hv) uconstr(He) :=
  wp_bind e;
  iApply (wp_wand with pat); [iApply He; trivial|];
  simpl; iIntros (v) Hv.


Lemma subst_map_insert2 x1 v1 x2 v2 vs e : x1 ≠ x2 ->
  subst_map (<[x2:=v2]> (<[x1:=v1]>vs)) e = 
    subst x1 v1 (subst x2 v2 (subst_map (delete x1 (delete x2 vs)) e)).
Proof.
  intros Hneq.
  (* Room for streamlining *)
  rewrite subst_subst_ne; auto.
  rewrite -subst_map_insert.
  rewrite -delete_insert_ne; auto.
  rewrite -subst_map_insert; auto.
Qed.


(* Mostly inspired from Semantics notes *)
Section context_lemmas.
  Lemma ctx_lookup_contains (Γ : ctx) x τ : 
    Γ !! x = Some τ → CtxItem x τ ∈ Γ.
  Proof.
    (* By induction on Γ, using ctx_lookup definition
        Admitted for now because this is clearly true but annoying *)
    Admitted.

  Lemma ctx_interp_split Γ1 Γ2 γ :
    𝒢⟦ Γ1 ++ Γ2 ⟧ γ ⊣⊢ 𝒢⟦ Γ1 ⟧ γ ∗ 𝒢⟦ Γ2 ⟧ γ.
  Proof.
    iApply big_sepL_app.
  Qed.

  Lemma ctx_interp_lookup Γ γ τ x :
    ⌜Γ !! x = Some τ⌝ -∗
    𝒢⟦ Γ ⟧ γ -∗
    ∃ v, ⌜γ !! x = Some v⌝ ∗ 𝒱⟦ τ ⟧ v.
  Proof.
    iIntros (Hlook) "Hγ".
    apply ctx_lookup_contains in Hlook.
    iPoseProof (big_sepL_elem_of _ Γ _ with "Hγ") as "HΦ"; done.
  Qed.

  (* TODO: come back and prove this, in the case where x is not in Γ
  (Also prove the thing from the Swap compat lemma, where we add to γ only)

  Lemma ctx_interp_insert Γ γ τ v x :
    𝒱⟦ τ ⟧ v -∗
    𝒢⟦ Γ ⟧ γ -∗
    𝒢⟦ (<[ x := τ ]> Γ) ⟧ (<[ x := v ]> γ).
  Proof.
    iIntros "Hv Hγ". iApply (big_sepM2_insert_2 with "[Hv] [Hγ]"); done.
  Qed.
  *)
End context_lemmas.