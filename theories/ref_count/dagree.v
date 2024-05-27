From iris.algebra Require Export cmra.
From iris.prelude Require Import options.

(* ZACK NOTE: more `Local Arguments ...` would go here, prob *)

(* This is a common non-empty list pattern. For instance, see 
   https://github.com/coq-community/parseque/blob/master/src/NEList.v *)
Record dagree (A : Type) := Agree {
  dagree_head : A;
  dagree_tail : list A
}.
Global Arguments Agree {_}.
Global Arguments dagree_head {_}.
Global Arguments dagree_tail {_}.

Definition to_list {A} (xxs : dagree A) : list A :=
  dagree_head xxs :: dagree_tail xxs.
Local Coercion to_list : dagree >-> list.

(* More equality stuff would go here, as needed *)

Section dagree.
  Context {A : Type}.
  Implicit Types a b : A.
  Implicit Types x y : dagree A.

  (* Lifts (=) to Equiv, making (dagree A) an OFE *)
  Canonical Structure dagreeO := leibnizO (dagree A).

  Local Instance agree_op_instance : Op (dagree A) :=
    λ x y, Agree (dagree_head x) (dagree_tail x ++ y).

  Local Instance dagree_valid_instance : Valid (dagree A) := λ x,
    (* Alternative would be to lift more things like ∈ to dagree,
       or to inline. this can be changed to be more ergonomic *)
    let x := to_list x in 
      match x with
      | [a] => True
      | _ => ∀ a b, a ∈ x → b ∈ x → a = b
      end.

  Local Instance agree_pcore_instance : PCore (dagree A) := Some.

  Definition dagree_mixin : RAMixin (dagree A).
  Proof.
    (* Insert proof here (annoying, but should work with helpers) *)
    Admitted.

  Canonical Structure dagreeR := discreteR (dagree A) dagree_mixin.

  (* There may be more things in here that are needed, like certain
     associativity, injectivity, etc things, more helper lemmas ... *)
  Global Instance dagree_cmra_total : CmraTotal dagreeR.
  Proof. rewrite /CmraTotal; eauto. Qed.

  Global Instance dagree_core_id x : CoreId x.
  Proof. by constructor. Qed.

  Global Instance dagree_cmra_discrete : CmraDiscrete dagreeR.
  Proof. apply discrete_cmra_discrete. Qed.

  Definition to_agree (a : A) : dagree A :=
  {| dagree_head := a; dagree_tail := [] |}.

  Global Instance to_agree_injN : Inj (=) (=) (to_agree).
  Proof. intros x y Hxy. by inversion Hxy. Qed.
End dagree.

(* more goes here, for managing implicits easier *)
Global Arguments dagreeR : clear implicits.