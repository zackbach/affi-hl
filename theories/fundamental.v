From affi Require Import source logrel helpers.
From iris.heap_lang Require Import notation lang.
From iris.proofmode Require Import proofmode tactics.
From iris.heap_lang Require Import primitive_laws metatheory.
From iris.heap_lang Require Import proofmode.
From iris.prelude Require Import options.

Lemma compat_unit Γ :
  Γ ⊨ #() : One.
Proof.
  iIntros (γ) "Hg/=".
  (* Looking at the intermediate proof state, this really should
     have ℰ unfolded due to `/=` aka `simpl`. issue w my def.s *)
  iApply wp_value. done.
Qed.

Lemma compat_var Γ (x : string) τ :
  Γ !! x = Some τ →
  Γ ⊨ x : τ.
Proof.
  iIntros (Hlook γ) "Hg/="; rewrite /expr_interp.
  (* [//] creates a goal for the premise (in this case Γ) with no
     spatial hypotheses, then uses // to call done and solve *)
  iPoseProof (ctx_interp_lookup with "[//] Hg") as "[%v [-> Hv]]".
  iApply wp_value; done. 
Qed.

Lemma compat_lam Γ (x : string) e τ1 τ2 :
  (CtxItem x τ1 :: Γ) ⊨ e : τ2 →
  Γ ⊨ (λ: x, e) : Fun τ1 τ2.
Proof.
  iIntros (He γ) "Hg/=". rewrite /expr_interp /fun_interp.
  (* In other sources, this iModIntro just happened... *)
  wp_pure; iModIntro. iIntros (w) "Hvw".
  rewrite /expr_interp. wp_pure.
  iPoseProof (He $! (<[ x := w ]> γ) with "[Hvw Hg]") as "He".
  - admit.
    (* iApply (context_interp_insert with "Hvw Hg"). *)
  (* rewrite -foo is like rewrite <- foo *)
  - rewrite -subst_map_insert.
  Admitted.

Lemma compat_app Γ1 Γ2 e1 e2 τ1 τ2 :
  Γ1 ⊨ e1 : Fun τ1 τ2 →
  Γ2 ⊨ e2 : τ1 →
  Γ1 ++ Γ2 ⊨ e1 e2 : τ2.
Proof.
  iIntros (He1 He2 γ) "Hg/="; rewrite /expr_interp.
  (* OLD: rewrite ctx_interp_split; iDestruct "Hg" as "[Hg1 Hg2]". *)
  iDestruct (ctx_interp_split with "Hg") as "[Hg1 Hg2]".
  smart_wp_bind (subst_map _ e2) "[Hg2]" v2 "Hv2" He2.
  (* Verbose: 
    wp_bind (subst_map _ e2).
    wp_apply (wp_wand with "[Hg2]").
    { iApply He2. done. }
    iIntros (v') "Hv'".
  *)
  smart_wp_bind (subst_map _ e1) "[Hg1]" v1 "Hv1" He1.
  rewrite /fun_interp.
  (* I guess this is smart enough to note w must be v2 *)
  iApply ("Hv1" with "Hv2").
Qed.

Lemma compat_pair Γ1 Γ2 e1 e2 τ1 τ2 :
  Γ1 ⊨ e1 : τ1 →
  Γ2 ⊨ e2 : τ2 →
  Γ1 ++ Γ2 ⊨ (e1, e2) : (Tensor τ1 τ2).
Proof.
  iIntros (He1 He2 γ) "Hg/="; rewrite /expr_interp /tensor_interp.
  iDestruct (ctx_interp_split with "Hg") as "[Hg1 Hg2]".
  smart_wp_bind (subst_map _ e2) "[Hg2]" v2 "Hv2" He2.
  smart_wp_bind (subst_map _ e1) "[Hg1]" v1 "Hv1" He1.
  wp_pures; iModIntro. eauto with iFrame.
Qed.

Lemma compat_split Γ1 Γ2 (x1 x2 : string) e1 e2 τ1 τ2 τ :
  Γ1 ⊨ e1 : Tensor τ1 τ2 →
  CtxItem x2 τ2 :: CtxItem x1 τ1 :: Γ2 ⊨ e2 : τ →
  Γ1 ++ Γ2 ⊨ (let: "tmp" := e1 in 
              let: x1 := Fst "tmp" in 
              let: x2 := Snd "tmp" in e2) : τ.
Proof.
  Admitted.

Lemma compat_new Γ e τ :
  Γ ⊨ e : τ →
  Γ ⊨ ref e : Unq τ.
Proof.
  iIntros (He γ) "Hg/="; rewrite /expr_interp /unq_interp.
  smart_wp_bind (subst_map _ _) "[Hg]" v "Hv" He.
  wp_alloc l as "Hl"; iModIntro. eauto with iFrame.
Qed.

Lemma compat_swap Γ1 Γ2 e1 e2 τ1 τ2 :
  Γ1 ⊨ e1 : Unq τ1 →
  Γ2 ⊨ e2 : τ2 →
  Γ1 ++ Γ2 ⊨ (let: "l" := e1 in 
              let: "r" := ! "l" in 
              let: "_" := "l" <- e2 in 
                ("l", "r")) : Tensor (Unq τ2) τ1.
Proof.
  iIntros (He1 He2 γ) "Hg/="; rewrite /expr_interp.
  iDestruct (ctx_interp_split with "Hg") as "[Hg1 Hg2]".
  smart_wp_bind (subst_map γ e1) "[Hg1]" l "[%loc [%v1 (-> & Hpt & Hv1)]]" He1.
  rewrite lookup_delete. wp_pures. wp_load. wp_pures.
  (* Surely there is a better way to do this *)
  rewrite lookup_delete_ne; auto.
  rewrite lookup_delete_ne; auto.
  rewrite lookup_delete. simpl.
  rewrite -subst_map_insert2; auto.
  wp_bind (Store _ _). wp_bind (subst_map _ _).
  (* Problem: we need 
    𝒢⟦ Γ2 ⟧ (<["l":=#loc]> (<["r":=v1]> γ)) in order to apply
    He2 to the term.
    technically this means we can't have l or r appear free in e2
    the way to enforce that is probably just to require that
    l and r are not in Γ2, then the proof should fall out
    I guess I should just update my compilation relation *)

  
  Admitted.

Local Hint Resolve compat_unit compat_var compat_lam compat_app
  compat_pair compat_split compat_new compat_swap : core.

Lemma fundamental Γ a τ e :
  compile Γ a τ e →
  Γ ⊨ e : τ.
Proof.
  induction 1; eauto.
Qed.