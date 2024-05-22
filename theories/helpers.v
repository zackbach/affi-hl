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


Section subst.
  Lemma subst_map_insert2 x1 v1 x2 v2 vs e : x1 ≠ x2 →
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

  (* This is almost hilariously dinky *)
  Lemma subst_map_insert3 x1 v1 x2 v2 x3 v3 vs e : 
    x1 ≠ x2 → x2 ≠ x3 → x1 ≠ x3 →
    subst_map (<[x3:=v3]> (<[x2:=v2]> (<[x1:=v1]>vs))) e = 
      subst x1 v1 (subst x2 v2 (subst x3 v3 
        (subst_map (delete x1 (delete x2 (delete x3 vs))) e))).
  Proof.
    intros Hneq12 Hneq23 Hneq13.
    rewrite (subst_subst_ne _ x2 x3); auto.
    rewrite (subst_subst_ne _ x1 x3); auto.
    rewrite -subst_map_insert2; auto.
    rewrite -delete_insert_ne; auto.
    rewrite -delete_insert_ne; auto.
    rewrite -subst_map_insert; auto.
  Qed.

  Lemma binder_name_neq a b :
    a ≠ b ↔ (BNamed a) ≠ (BNamed b).
  Proof.
    split; intros H1 H2; [inversion H2 | subst]; contradiction.
  Qed.
End subst.


(* Mostly inspired from Semantics notes *)
Section context_lemmas.
  Lemma ctx_lookup_contains (Γ : ctx) x τ : 
    Γ !! x = Some τ → CtxItem x τ ∈ Γ.
  Proof.
    intros Hlook.
    induction Γ as [|item Γ].
    - discriminate.
    - destruct item as [x' τ'].
      rewrite /lookup /ctx_lookup in Hlook.
      destruct (decide (x = x')) as [Heq | Hneq].
      + rewrite decide_True in Hlook; auto.
        inversion Hlook; subst. left.
      + right. apply IHΓ. rewrite decide_False in Hlook; auto.
  Qed.

  Lemma ctx_contains_lookup (Γ : ctx) x τ : 
    CtxItem x τ ∈ Γ → ∃ τ', Γ !! x = Some τ'.
  Proof.
    intros Hin.
    induction Γ as [|item Γ].
    - apply not_elem_of_nil in Hin. contradiction.
    - apply elem_of_cons in Hin. destruct Hin as [Hfirst | Hrest].
    (* TODO: golf this, there is a ton of repeated logic here *)
      + exists τ. rewrite /lookup /ctx_lookup.
        rewrite <- Hfirst. rewrite decide_True; done.
      + apply IHΓ in Hrest.
        destruct item as [name τcur].
        destruct (decide (x = name)).
        * exists τcur. rewrite /lookup /ctx_lookup.
          rewrite decide_True; done.
        * destruct Hrest as [τlater Hfind].
          exists τlater. rewrite /lookup /ctx_lookup.
          rewrite decide_False; auto.
  Qed.

  (* Note that this actually holds as an ↔ as stated,
     but other direction is not needed for our purposes *)
  Lemma ctx_lookup_notin' (Γ : ctx) x τ : 
    Γ !! x = None → CtxItem x τ ∉ Γ.
  Proof.
    intros Hnone Hcontra.
    apply ctx_contains_lookup in Hcontra as [τ' Hsome].
    congruence.
  Qed.

  Lemma ctx_add_notin (Γ : ctx) x y τ :
    Γ !! y = None → x ≠ y → (CtxItem x τ :: Γ) !! y = None.
  Proof.
    intros Hnone Hneq.
    rewrite /lookup /ctx_lookup decide_False; auto.
  Qed.


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
    by iPoseProof (big_sepL_elem_of _ Γ _ with "Hγ") as "HΦ".
  Qed.

  (* This does get invoked directly sometimes; whenever it is invoked,
     that is a sign that using the "anomyzation" approach would not suffice *)
  Lemma ctx_subst_insert Γ γ v x :
    ⌜Γ !! x = None⌝ -∗
    𝒢⟦ Γ ⟧ γ -∗
    𝒢⟦ Γ ⟧ (<[ x := v ]> γ).
  Proof.
    iIntros (Hnone) "Hγ".
    iApply (big_sepL_mono with "Hγ").
    iIntros (k item Hlook) "[%val [%Hfind Hval]]".
    iExists val; iFrame; iPureIntro.
    apply lookup_insert_Some. right; split; auto.
    destruct item as [name τ]; simpl in *.
    apply elem_of_list_lookup_2 in Hlook.
    assert ({| ctx_item_name := x; ctx_item_type := τ |} ∉ Γ).
    - apply ctx_lookup_notin; done.
    - intros Hcontra. subst. contradiction.
  Qed.

  Lemma ctx_interp_insert Γ γ τ v x :
    ⌜Γ !! x = None⌝ -∗
    𝒱⟦ τ ⟧ v -∗
    𝒢⟦ Γ ⟧ γ -∗
    𝒢⟦ CtxItem x τ :: Γ ⟧ (<[ x := v ]> γ).
  Proof.
    iIntros (Hnone) "Hv Hγ".
    (* Unable to apply big_sepL_cons without marking as transparent.
       Note that other developments and proofs above don't have this problem
       not sure why there's only a problem here... *)
    Transparent ctx_interp. iApply big_sepL_cons; simpl.
    iSplitL "Hv".
    - iExists v. rewrite lookup_insert; auto.
    - by iPoseProof (ctx_subst_insert $! Hnone with "Hγ") as "Hγx".
  Qed.
End context_lemmas.