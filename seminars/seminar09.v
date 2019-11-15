From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Totality and termination *)

(** Define Ackermann's function without using
    the nested [fix] trick.
    Try several different approaches
*)


(** Implement the [interleave] function using
   [Fix_F_2] combinator *)
(**
Definition interleave_fix {A} (xs ys : seq A) : seq A :=
  Fix_F_2  ...
*)


(** Define a list sorting function using merge sort algorithm. *)




(** * Cast and John Major Equality via cast *)

From Coq Require Import Eqdep.

Section Cast.
Variable (C : Type) (interp : C -> Type).

Definition cast A B (pf : A = B) (v : interp B) : interp A :=
  ecast _ _ (esym pf) v.

(** You need to use [Streicher_K] axiom from [Eqdep] module *)
Lemma eqc A (pf : A = A) (v : interp A) : cast pf v = v.
Proof.
Admitted.

(** Heterogeneous equality via [cast] *)
Definition jmeq A B (v : interp A) (w : interp B) :=
  forall pf, v = cast pf w.

Lemma jmrefl A (v : interp A) : jmeq v v.
Proof.
Admitted.

Lemma jmsym A B (v : interp A) (w : interp B) :
  jmeq v w -> jmeq w v.
Proof.
Admitted.

Lemma jmE A (v w : interp A) : jmeq v w <-> v = w.
Proof.
Admitted.

Lemma castE A B (pf1 pf2 : A = B) (v1 v2 : interp B) :
  v1 = v2 <-> cast pf1 v1 = cast pf2 v2.
Proof.
Admitted.

End Cast.
