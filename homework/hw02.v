From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section IntLogic.

Variables A B C : Prop.

Lemma notTrue_iff_False : (~ True) <-> False.
Proof.
Admitted.

Lemma dne_False : ~ ~ False -> False.
Proof.
Admitted.

Lemma dne_True : ~ ~ True -> True.
Proof.
Admitted.

Lemma weak_peirce : ((((A -> B) -> A) -> A) -> B) -> B.
Proof.
Admitted.

Lemma imp_trans : (A -> B) -> (B -> C) -> (A -> C).
Proof.
Admitted.

End IntLogic.


(** Let's get familiarize ourselves with some lemmas from [ssrbool] module.
    The proofs are very easy, so the lemma statements are more important here.
 *)
Section BooleanLogic.

Variables (A B : Type) (x : A) (f : A -> B) (a b : bool) (vT vF : A).

Lemma negbNE : ~~ ~~ b -> b.
Proof.
Admitted.

(** Figure out what [involutive] and [injective] mean
    using Coq's interactive queries. Prove the lemmas.
    Hint: to unfold a definition in the goal use [rewrite /definition] command.
*)
Lemma negbK : involutive negb.
Proof.
Admitted.

Lemma negb_inj : injective negb.
Proof.
Admitted.

Lemma ifT : b -> (if b then vT else vF) = vT.
Proof.
Admitted.

Lemma ifF : b = false -> (if b then vT else vF) = vF.
Proof.
Admitted.

Lemma if_same : (if b then vT else vT) = vT.
Proof.
Admitted.

Lemma if_neg : (if ~~ b then vT else vF) = if b then vF else vT.
Proof.
Admitted.

Lemma fun_if : f (if b then vT else vF) = if b then f vT else f vF.
Proof.
Admitted.

Lemma if_arg (fT fF : A -> B) :
  (if b then fT else fF) x = if b then fT x else fF x.
Proof.
Admitted.

Lemma andbK : a && b || a = a.
Proof.
Admitted.

(** Find out what [left_id], [right_id] mean
    using Coq's interactive queries. Prove the lemmas.
 *)
Lemma addFb : left_id false addb.    (* [addb] means XOR (eXclusive OR operation) *)
Proof.
Admitted.

Lemma addbF : right_id false addb.
Proof.
Admitted.

Lemma addbC : commutative addb.
Proof.
Admitted.

Lemma addbA : associative addb.
Proof.
Admitted.


(** Formulate analogous laws (left/right identity, commutativity, associativity)
    for boolean AND and OR and proove those.
    Find the names of corresponding lemmas in the standard library using
    [Search] command. For instance: [Search _ andb left_id.]
    Have you noticed the naming patterns?
 *)

End BooleanLogic.



Section NaturalNumbers.
(** Figure out what [cancel], [succn], [predn] mean
    using Coq's interactive queries. Prove the lemmas.
 *)
Lemma succnK : cancel succn predn.
Proof.
Admitted.

Lemma add0n : left_id 0 addn.
Proof.
Admitted.

Lemma addSn m n : m.+1 + n = (m + n).+1.
Proof.
Admitted.

Lemma add1n n : 1 + n = n.+1.
Proof.
Admitted.

Lemma add2n m : 2 + m = m.+2.
Proof.
Admitted.

Lemma subn0 : right_id 0 subn.
Proof.
Admitted.

End NaturalNumbers.
