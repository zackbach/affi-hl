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
  (* Looking at the intermediate proof state, this really should have ℰ
     unfolded due to `/=` aka `simpl`. this happens automatically in other
     developments, might just be an issue w my definitions or opacity? *)
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
  Γ !! x = None →
  (CtxItem x τ1 :: Γ) ⊨ e : τ2 →
  Γ ⊨ (λ: x, e) : Fun τ1 τ2.
Proof.
  iIntros (Hfresh He γ) "Hg/=". rewrite /expr_interp /fun_interp.
  (* In other sources, this iModIntro just happened... *)
  wp_pure; iModIntro. iIntros (w) "Hvw".
  rewrite /expr_interp. wp_pure.
  iPoseProof (He $! (<[ x := w ]> γ) with "[Hvw Hg]") as "He".
  - iApply (ctx_interp_insert $! Hfresh with "Hvw Hg").
  - rewrite -subst_map_insert; done.
Qed.

Lemma compat_app Γ1 Γ2 e1 e2 τ1 τ2 :
  Γ1 ⊨ e1 : Fun τ1 τ2 →
  Γ2 ⊨ e2 : τ1 →
  Γ1 ++ Γ2 ⊨ e1 e2 : τ2.
Proof.
  iIntros (He1 He2 γ) "Hg/="; rewrite /expr_interp.
  iDestruct (ctx_interp_split with "Hg") as "[Hg1 Hg2]".
  smart_wp_bind (subst_map _ e2) "[Hg2]" v2 "Hv2" He2.
  (* Verbose (AKA what the little tactic is doing)
    wp_bind (subst_map _ e2).
    wp_apply (wp_wand with "[Hg2]").
    { iApply He2. done. }
    iIntros (v') "Hv'".
  *)
  smart_wp_bind (subst_map _ e1) "[Hg1]" v1 "Hv1" He1.
  rewrite /fun_interp.
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

Lemma compat_split Γ1 Γ2 (x1 x2 : string) e1 e2 τ1 τ2 τ (tmp : string) :
  Γ2 !! x1 = None → Γ2 !! x2 = None → Γ2 !! tmp = None →
  tmp ≠ x1 → tmp ≠ x2 → x1 ≠ x2 →
  Γ1 ⊨ e1 : Tensor τ1 τ2 →
  CtxItem x1 τ1 :: CtxItem x2 τ2 :: Γ2 ⊨ e2 : τ →
  Γ1 ++ Γ2 ⊨ (let: tmp := e1 in 
              let: x1 := Fst tmp in 
              let: x2 := Snd tmp in e2) : τ.
Proof.
  iIntros (Hx1 Hx2 Htmp Hneq1 Hneq2 Hneq He1 He2 γ) "Hg/=".
  (* unlike compat_swap, trying to do some rewriting first,
     which hopefully will be less painful later *)
  rewrite lookup_delete_ne; auto. rewrite lookup_delete /expr_interp.
  (* This totally shouldn't be necessary, but appears to be for decide *)
  assert (BNamed tmp ≠ BNamed x1) as Hneq1'. { apply binder_name_neq; done. }
  assert (BNamed tmp ≠ BNamed x2) as Hneq2'. { apply binder_name_neq; done. }
  assert (BNamed x1 ≠ BNamed x2) as Hneq'. { apply binder_name_neq; done. }
  iDestruct (ctx_interp_split with "Hg") as "[Hg1 Hg2]".
  smart_wp_bind (subst_map _ e1) "[Hg1]" v "[%v1 [%v2 (-> & Hv1 & Hv2)]]" He1.
  wp_pures; rewrite !decide_True; auto.
  wp_pures; rewrite !decide_True; auto.
  rewrite -subst_map_insert3; auto.
  (* TODO: golf this *)
  iPoseProof (ctx_interp_insert $! Hx2 with "Hv2 Hg2") as "Hγ2".
  assert ((CtxItem x2 τ2 :: Γ2) !! x1 = None) as Hnone1.
  { apply ctx_add_notin; done. }
  iPoseProof (ctx_interp_insert $! Hnone1 with "Hv1 Hγ2") as "Hγ1".
  assert ((CtxItem x1 τ1 :: (CtxItem x2 τ2 :: Γ2)) !! tmp = None) as Hnone2.
  { repeat apply ctx_add_notin; auto. }
  iPoseProof (ctx_subst_insert _ _ (v1, v2) $! Hnone2 with "Hγ1") as "Hγ".
  iPoseProof (He2 with "Hγ") as "He". done.
Qed.

Lemma compat_new Γ e τ :
  Γ ⊨ e : τ →
  Γ ⊨ ref e : Unq τ.
Proof.
  iIntros (He γ) "Hg/="; rewrite /expr_interp /unq_interp.
  smart_wp_bind (subst_map _ _) "[Hg]" v "Hv" He.
  wp_alloc l as "Hl"; iModIntro. eauto with iFrame.
Qed.

Lemma compat_swap Γ1 Γ2 e1 e2 τ1 τ2 (ltemp rtemp : string) :
  Γ2 !! ltemp = None → Γ2 !! rtemp = None → ltemp ≠ rtemp →
  Γ1 ⊨ e1 : Unq τ1 →
  Γ2 ⊨ e2 : τ2 →
  Γ1 ++ Γ2 ⊨ (let: ltemp := e1 in 
              let: rtemp := ! ltemp in 
              let: BAnon := ltemp <- e2 in 
                (ltemp, rtemp)) : Tensor (Unq τ2) τ1.
Proof.
  iIntros (Hlt Hrt Hneq He1 He2 γ) "Hg/="; rewrite /expr_interp.
  (* Some of the later decision obligations use inequality of binders *)
  assert (BNamed ltemp ≠ BNamed rtemp). { apply binder_name_neq; done. }
  iDestruct (ctx_interp_split with "Hg") as "[Hg1 Hg2]".
  smart_wp_bind (subst_map γ e1) "[Hg1]" l "[%loc [%v1 (-> & Hpt & Hv1)]]" He1.
  (* ! rewrites 1 or more times BTW, ? for 0 or more *)
  rewrite !lookup_delete. wp_pures.
  (* This became necessary when swapping from "l" and "r" to ltemp and rtemp
     since the decision stuff did not happen automatically.
     just using rewrite was rewriting one-by-one *)
  setoid_rewrite decide_True; auto.
  wp_load. wp_pures.
  (* Surely there is a better way to do this. To do this at any scale,
   much better automation / substitution reasoning would be needed. *)
  rewrite lookup_delete_ne; auto.
  rewrite lookup_delete. simpl.
  rewrite decide_True; auto.
  rewrite -subst_map_insert2; auto. simpl.
  (* back to actual proof stuff, not silly substitutions *)
  wp_bind (Store _ _). wp_bind (subst_map _ _).
  iPoseProof (ctx_subst_insert _ _ v1 $! Hrt with "Hg2") as "Hγr".
  iPoseProof (ctx_subst_insert _ _ #loc $! Hlt with "Hγr") as "Hγrl".
  iPoseProof (He2 with "Hγrl") as "He".
  rewrite /expr_interp.
  iApply (wp_wand with "He"); iIntros (v2) "Hv2".
  wp_store. wp_pures.
  (* Again, this is way more manual than it ought to be, especially since
     this would have been done automatically if literals were used *)
  rewrite decide_False; auto. simpl. rewrite decide_True; auto.
  wp_pure; iModIntro. 
  rewrite /tensor_interp /unq_interp.
  iExists #loc, v1; iFrame. eauto with iFrame.
Qed.

Local Hint Resolve compat_unit compat_var compat_lam compat_app
  compat_pair compat_split compat_new compat_swap : core.

Lemma fundamental Γ a τ e :
  compile Γ a τ e →
  Γ ⊨ e : τ.
Proof.
  induction 1; eauto.
Qed.