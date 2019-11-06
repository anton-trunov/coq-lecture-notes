From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** Properties of arbitrary binary relations (not necessarily decidable) *)
(** A functional or deterministic relation *)
Definition functional {X : Type} (R : X -> X -> Prop) : Prop :=
  forall (s s1 s2 : X), R s s1 -> R s s2 -> s1 = s2.

Lemma func1 :
  functional (fun x y => x.*2 == y).
Admitted.

Lemma func2 :
  ~ functional (fun x y => (x.*2 == y) || ((x, y) == (0,1))).
Admitted.


(** Define a notation such that {In C, functional R} restricts the domain of the relation like so:

  forall (s s1 s2 : X), C s -> R s s1 -> R s s2 -> s1 = s2

And prove the following lemma:
*)
(* Notation "{ 'In' C , P }" := *)
(*   (...) (at level 0). *)

Lemma func3 :
  {In (fun n => 0 < n), functional (fun x y => (x.*2 == y) || ((x, y) == (0,1)))}.
Admitted.


(* prove without using [case] or [elim] tactics *)
Lemma Peirce p q : ((p ==> q) ==> p) ==> p.
Admitted.


(* prove without using [case] or [elim] tactics *)
Lemma addb_neq12 p q :  ~~ p = q -> p (+) q.
Admitted.


Lemma div_fact_plus1 m p : 1 < p -> p %| m `! + 1 -> m < p.
Admitted.


(* Prove [8x = 6y + 1] has no solutions in [nat] *)
Lemma no_solution x y :
  8*x != 6*y + 1.
Admitted.



Lemma iota_add m n1 n2 :
  iota m (n1 + n2) = iota m n1 ++ iota (m + n1) n2.
Admitted.

Definition mysum m n F := (foldr (fun i a => F i + a) 0 (iota m (n - m))).

(* "big" operator *)
Notation "\mysum_ ( m <= i < n ) F" := (mysum m n (fun i => F))
  (at level 41, F at level 41, i, m, n at level 50,
           format "'[' \mysum_ ( m  <=  i  <  n ) '/  '  F ']'").

Lemma mysum_recl m n F :
  m <= n ->
  \mysum_(m <= i < n.+1) F i = \mysum_(m <= i < n) F i + F n.
Admitted.

Lemma sum_odds n :
  \mysum_(0 <= i < n) (2 * i + 1) = n ^ 2.
Admitted.


