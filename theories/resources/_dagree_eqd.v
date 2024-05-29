(* FAILED ATTEMPT: see `dagree.v` for proper implementation,
   and resource.v for commentary *)
From iris.algebra Require Export cmra.
From iris.prelude Require Import options.

(* discrete CMRA (aka RA) for agreement. using the built-in CMRA
   runs into positivity issues, since the carrier is non-empty lists *)

(* structure inspired by
  https://gitlab.mpi-sws.org/iris/iris/blob/master/iris/algebra/excl.v 
*)

Inductive dagree (A : Type) :=
  | Agree : A → dagree A
  | Disagree : dagree A.
(* A is implicit and can be inferred *)
Global Arguments Agree {_} _.
Global Arguments Disagree {_}.

(* specifies expected parameters through the Params typeclass,
   apparently @ allows explicit type arguments, implicits *)
Global Instance: Params (@Agree) 1 := {}.
Global Instance: Params (@Disagree) 1 := {}.

Global Instance maybe_Agree {A} : Maybe (@Agree A) := λ x,
  match x with Agree a => Some a | _ => None end.

Section dagree.
  Context {A : Type}.
  Context `{EqDecision A}.
  Implicit Types a b : A.
  Implicit Types x y : dagree A.

  (* Lifts (=) to Equiv, making (dagree A) an OFE *)
  Canonical Structure dagreeO := leibnizO (dagree A).

  Local Instance dagree_valid_instance : Valid (dagree A) := λ x,
    match x with Agree _ => True | Disagree => False end.

  (* This directly emulates Iris's PCore instance for `agree`,
     even though I'm not entirely convinced this is what we want *)
  Local Instance dagree_pcore_instance : PCore (dagree A) := Some.

  Local Instance dagree_op_instance : Op (dagree A) := λ x y,
    match x, y with 
    | Agree x, Agree y => if (decide (x = y)) then Agree x else Disagree
    | _, _ => Disagree
    end.

  Definition dagree_mixin : RAMixin (dagree A).
  Proof.
    Admitted.

  Canonical Structure dagreeR := discreteR (dagree A) dagree_mixin.

  (* https://gitlab.mpi-sws.org/iris/iris/blob/master/iris/algebra/agree.v *)
  (* There may be more things in here that are needed, like certain
     associativity, injectivity, etc things, more helper lemmas ... *)
  Global Instance dagree_cmra_total : CmraTotal dagreeR.
  Proof. rewrite /CmraTotal; eauto. Qed.

  Global Instance dagree_core_id x : CoreId x.
  Proof. by constructor. Qed.

  Global Instance dagree_cmra_discrete : CmraDiscrete dagreeR.
  Proof. apply discrete_cmra_discrete. Qed.
End dagree.

Global Arguments dagreeR _ {_}.