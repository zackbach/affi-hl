From stdpp Require Import binders strings gmap.
From iris.heap_lang Require Import notation lang.

Section lang.
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
End lang.

(* Mostly from DFSL paper. They store names as `binding`s and use an
   anonymization when they cons on, but for now we instead have a requirement
   for names being fresh *)
(* I think that the anonymization thing with `BAnon` would work mostly, but I
   couldn't figure out a good way to get temp names to work without already
   quantifying + freshness constraint. At that point, why not do it all like
   that? Maybe restrictions about closedness could suffice, but annoying *)
Section context.
  Inductive ctx_item := CtxItem {
    ctx_item_name : string;
    ctx_item_type : ty;
  }.

  Definition ctx := list ctx_item.

  Global Instance ctx_lookup : Lookup string ty ctx := 
    fix f x Γ :=
      match Γ with
      | [] => None
      | CtxItem name τ :: rest => 
          if decide (name = x) then Some τ else f x rest
      end.
End context.

Section compile.
  (* I literally just copied this from random STLC notation thing *)
  Reserved Notation "Γ ⊢ a : τ '~~>' e" (at level 74, a, τ, e at next level).

  Inductive compile : ctx → aexpr → ty → expr → Prop :=
    | CUnit Γ :
        Γ ⊢ Unit : One ~~> #()
    | CVar Γ x τ :
      Γ !! x = Some τ →
        Γ ⊢ (Var x) : τ ~~> x
    | CLam Γ x a τ1 τ2 e :
      (* Requires freshness of `x`, which makes context things easier
         As noted above, could have consing onto Γ anonymize instead *)
      Γ !! x = None →
      (CtxItem x τ1 :: Γ) ⊢ a : τ2 ~~> e →
        Γ ⊢ (Lam (BNamed x) a) : (Fun τ1 τ2) ~~> λ: x, e
    | CApp Γ1 Γ2 a1 a2 τ1 τ2 e1 e2 :
      Γ1 ⊢ a1 : (Fun τ1 τ2) ~~> e1 →
      Γ2 ⊢ a2 : τ1 ~~> e2 →
        (Γ1 ++ Γ2) ⊢ (App a1 a2) : τ2 ~~> e1 e2
    | CPair Γ1 Γ2 a1 a2 τ1 τ2 e1 e2 :
      Γ1 ⊢ a1 : τ1 ~~> e1 →
      Γ2 ⊢ a2 : τ2 ~~> e2 →
        (Γ1 ++ Γ2) ⊢ (Pair a1 a2) : (Tensor τ1 τ2) ~~> (e1, e2)
    | CSplit Γ1 Γ2 x1 x2 a1 a2 τ1 τ2 τ e1 e2 :
      Γ1 ⊢ a1 : (Tensor τ1 τ2) ~~> e1 →
      (CtxItem x2 τ2 :: CtxItem x1 τ1 :: Γ2) ⊢ a2 : τ ~~> e2 →
        (Γ1 ++ Γ2) ⊢ (Split (BNamed x1) (BNamed x2) a1 a2) : τ ~~>
          let: "tmp" := e1 in
          let: x1 := Fst "tmp" in
          let: x2 := (Snd "tmp") in e2
    | CNew Γ a τ e :
      Γ ⊢ a : τ ~~> e →
        Γ ⊢ (New a) : (Unq τ) ~~> ref e
    | CSwap Γ1 Γ2 a1 a2 τ1 τ2 e1 e2 (ltemp rtemp : string) :
      (* requirement that ltemp and rtemp fresh *)
      Γ2 !! ltemp = None → Γ2 !! rtemp = None →
      Γ1 ⊢ a1 : (Unq τ1) ~~> e1 →
      Γ2 ⊢ a2 : τ2 ~~> e2 →
        (Γ1 ++ Γ2) ⊢ (Swap a1 a2) : (Tensor (Unq τ2) τ1) ~~>
          let: ltemp := e1 in
          let: rtemp := !ltemp in
          let: "_" := ltemp <- e2 in (ltemp, rtemp)
  where "Γ ⊢ a : τ '~~>' e" := (compile Γ a τ e).
End compile.

(* TODO:
    update relation to quantify over fresh names *)