(* In this file we explain how to do the "parallel increment" example (Example
   8.4) from the lecture notes in Iris in Coq. *)

(* Contains definitions of the weakest precondition assertion, and its basic
   rules. *)
From iris.program_logic Require Export weakestpre.
(* Definition of invariants and their rules (expressed using the fancy update
   modality). *)
From iris.base_logic.lib Require Export invariants.

(* Files related to the interactive proof mode. The first import includes the 
   general tactics of the proof mode. The second provides some more specialized 
   tactics particular to the instantiation of Iris to a particular programming 
   language. *)
From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Import proofmode.

(* Instantiation of Iris with the particular language. The notation file
   contains many shorthand notations for the programming language constructs, and
   the lang file contains the actual language syntax. *)
From iris.heap_lang Require Import notation lang.

(* We also import the parallel composition construct. This is not a primitive of
   the language, but is instead derived. This file contains its definition, and
   the proof rule associated with it. *)
From iris.heap_lang.lib Require Import par.

(* The following line imports some Coq configuration we commonly use in Iris
   projects, mostly with the goal of catching common mistakes. *)
From iris.prelude Require Import options.


Lemma id_P (P : Prop) : P -> P.
Proof. done. Qed.