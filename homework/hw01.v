From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat.

(*** Exercise 1 *)

(** 1a. Define [orb_my] function implementing boolean disjunction *)

(** 1b. Figure out the implementation of [orb] function in the standard library
        using Coq's interactive query mechanism *)

(** 1c. What's the difference between the standard implementation and
        the following one? *)

Definition orb_table (b c : bool) : bool :=
  match b, c with
  | true,  true  => true
  | true,  false => true
  | false, true  => true
  | false, false => false
  end.

(** Note: the above translates into nested pattern-matching, check this *)


(** 1d. Define [addb_my] function implementing exclusive boolean disjunction.
        {The name [addb] comes from the fact this operation behaves like addition modulo 2}
        If you are already familiar with proofs in Coq, think of a prover friendly
        definition, if you are not -- experiment with how different implementations
        behave under symbolic execution. *)


(*** Exercise 2 *)

(** 2a. Implement power function of two arguments [x] and [n],
        raising [x] to the power of [n] *)


(*** Exercise 3 *)

(** 3a. Implement division on unary natural numbers *)

Fixpoint divn_my (n m : nat) : nat. Abort.

(* Unit tests: *)
Compute divn_my 0 0.  (* = 0 *)
Compute divn_my 1 0.  (* = 0 *)
Compute divn_my 0 3.  (* = 0 *)
Compute divn_my 1 3.  (* = 0 *)
Compute divn_my 2 3.  (* = 0 *)
Compute divn_my 3 3.  (* = 1 *)
Compute divn_my 8 3.  (* = 2 *)
Compute divn_my 42 1. (* = 42 *)
Compute divn_my 42 2. (* = 21 *)
Compute divn_my 42 3. (* = 14 *)
Compute divn_my 42 4. (* = 10 *)


(** 3b. Provide several unit tests using [Compute] vernacular command *)


(*** Exercise 4 *)

(** Use the [applyn] function defined during the lecture
    (or better its Mathcomp sibling called [iter]) define

    4a. addition on natural numbers

    4b. multiplication on natural numbers

    Important: don't use recursion, i.e. no [Fixpoint] / [fix] should be in your solution.
*)

(** Here is out definition of [applyn]: *)
Definition applyn (f : nat -> nat) :=
  fix rec (n : nat) (x : nat) :=
    if n is n'.+1 then rec n' (f x)
    else x.





