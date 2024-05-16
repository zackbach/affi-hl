From stdpp Require Export binders strings gmap.
From iris.heap_lang Require Export notation lang.

Inductive aexpr :=
  | Unit
  | Var (x : string)
  | Lam (x : binder) (a : aexpr)
  | App (a1 a2 : aexpr)
  | Pair (a1 a2 : aexpr)
  | Split (x1 x2 : binder) (a1 a2 : aexpr)
  | New (a : aexpr)
  | Swap (a1 a2 : aexpr)
.

Inductive ty :=
  | One
  | Tensor (τ1 τ2 : ty)
  | Fun (τ1 τ2 : ty)
  | Unq (τ : ty)
.

(* TODO: maybe add printing notation for types *)

Definition ctx := gmap string ty.

(* I literally just copied this from random STLC notation thing *)
Reserved Notation "Γ ⊢ a : τ '~~>' e" (at level 74, a, τ, e at next level).

(* NOTE: I fear that overriding with ∪ for merging contexts is actually bad *)

Inductive compile : ctx → aexpr → ty → expr → Prop :=
  | CUnit Γ :
      Γ ⊢ Unit : One ~~> #()
  | CVar Γ x τ :
    Γ !! x = Some τ →
      Γ ⊢ (Var x) : τ ~~> x
  | CLam Γ x a τ1 τ2 e :
    (<[ x := τ1 ]> Γ) ⊢ a : τ1 ~~> e →
      Γ ⊢ (Lam (BNamed x) a) : (Fun τ1 τ2) ~~> λ: x, e
  | CApp Γ1 Γ2 a1 a2 τ1 τ2 e1 e2 :
    Γ1 ⊢ a1 : (Fun τ1 τ2) ~~> e1 →
    Γ2 ⊢ a2 : τ1 ~~> e2 →
      (Γ1 ∪ Γ2) ⊢ (App a1 a2) : τ2 ~~> e1 e2
  | CPair Γ1 Γ2 a1 a2 τ1 τ2 e1 e2 :
    Γ1 ⊢ a1 : τ1 ~~> e1 →
    Γ2 ⊢ a2 : τ2 ~~> e2 →
      (Γ1 ∪ Γ2) ⊢ (Pair a1 a2) : (Tensor τ1 τ2) ~~> (e1, e2)
  | CSplit Γ1 Γ2 x1 x2 a1 a2 τ1 τ2 τ e1 e2 :
    Γ1 ⊢ a1 : (Tensor τ1 τ2) ~~> e1 →
    (<[ x2 := τ2 ]> (<[ x1 := τ1 ]> Γ2)) ⊢ a2 : τ ~~> e2 →
      (Γ1 ∪ Γ2) ⊢ (Split (BNamed x1) (BNamed x2) a1 a2) : τ ~~>
        let: "tmp" := e1 in
        let: x1 := Fst "tmp" in
        let: x2 := (Snd "tmp") in e2
  | CNew Γ a τ e :
    Γ ⊢ a : τ ~~> e →
      Γ ⊢ (New a) : (Unq τ) ~~> ref e
  | CSwap Γ1 Γ2 a1 a2 τ1 τ2 e1 e2 :
    Γ1 ⊢ a1 : (Unq τ1) ~~> e1 →
    Γ2 ⊢ a2 : τ2 ~~> e2 →
      (Γ1 ∪ Γ2) ⊢ (Swap a1 a2) : (Tensor (Unq τ2) τ1) ~~>
        let: "l" := e1 in
        let: "r" := !"l" in
        let: "_" := "l" <- e2 in ("l", "r")
where "Γ ⊢ a : τ '~~>' e" := (compile Γ a τ e).