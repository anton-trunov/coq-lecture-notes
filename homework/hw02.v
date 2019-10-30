From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section IntLogic.

Variables A B C : Prop.

Lemma notTrue_iff_False : (~ True) <-> False.
Proof.
(* step-wise solutiton *)
split.
- by apply.
move=> f _. apply: f.

Restart.

(* idiomatic solution *)
by [].
Qed.


Lemma dne_False : ~ ~ False -> False.
Proof.
move=> nnF; apply: nnF; apply.

Restart.

(* let's golf it a bit, just for fun *)
exact: (@^~ id).

Restart.
(* and then a bit more *)
exact.

Qed.

Lemma dne_True : ~ ~ True -> True.
Proof.
move=> _. exact: I.

Restart.

by [].
Qed.

Lemma weak_peirce : ((((A -> B) -> A) -> A) -> B) -> B.
Proof.
move=> H.
apply: (H).
apply.
move=> p.
apply: H.
move=> _.
exact: p.

Restart.

move=> abaab; apply: (abaab); apply=> a.
by apply: abaab.
Qed.

Lemma imp_trans : (A -> B) -> (B -> C) -> (A -> C).
Proof.
move=> pq qr p.
apply: qr.
apply: pq.
exact: p.

Restart.

by move=> pq qr /pq/qr.
Qed.


End IntLogic.


(** Let's familiarize ourselves with some lemmas from [ssrbool] module.
    The proofs are very easy, so the lemma statements are more important here.
 *)
Section BooleanLogic.

Variables (A B : Type) (x : A) (f : A -> B) (a b : bool) (vT vF : A).

Lemma negbNE : ~~ ~~ b -> b.
Proof. by case: b. Qed.

(** Figure out what [involutive] and [injective] mean
    using Coq's interactive queries. Prove the lemmas.
    Hint: to unfold a definition in the goal use [rewrite /definition] command.
*)
Lemma negbK : involutive negb.
Proof.
(* A step-by-step solution *)
rewrite /involutive.
rewrite /cancel.
case.
- done.
done.

Restart.

(* An idiomatic solution *)
by case.
Qed.

Lemma negb_inj : injective negb.
Proof.
(* A step-by-step solution *)
rewrite /injective.
case.
- case.
  + done.
  done.
case.
- done.
done.

Restart.

(* An idiomatic solution is based on the fact that each involutive function is
   injective *)
apply: inv_inj.
apply: negbK.

Restart.

(* or in one go: *)

exact: inv_inj negbK.
Qed.

Lemma ifT : b -> (if b then vT else vF) = vT.
Proof.
(* step-by-step *)
Set Printing Coercions.
rewrite /is_true.
Unset Printing Coercions.
move=> ->.
done.

Restart.

(* SSReflect can see under coercions (definitions) and use [b] with
   implicit coercion [is_true] as equation directly *)
by move=> ->.

Restart.

(* another option would be to use case analysis on [b] like so: *)
by case: b.
Qed.

Lemma ifF : b = false -> (if b then vT else vF) = vF.
Proof. by move=> ->. Qed.

Lemma if_same : (if b then vT else vT) = vT.
Proof.
case: b.
- by [].
by [].

Restart.

by case: b.
(* It's important to understand why just [by [].] wouldn't work here.
   We have to do case analysis on [b] if we want the to reduce the [if]-expression *)
Qed.

Lemma if_neg : (if ~~ b then vT else vF) = if b then vF else vT.
Proof. by case: b. Qed.

Lemma fun_if : f (if b then vT else vF) = if b then f vT else f vF.
Proof. by case: b. Qed.

Lemma if_arg (fT fF : A -> B) :
  (if b then fT else fF) x = if b then fT x else fF x.
Proof. by case: b. Qed.

Lemma andbK : a && b || a = a.
Proof.
(* (almost) step-wise solutiton *)
case: a.
- by case: b.
by [].

Restart.

(* idiomatic solution *)
by case: a; case: b. (* case analyze on [a] and then for each of the two new
                        subgoals do case analysis on [b] *)
Qed.

(** Find out what [left_id], [right_id] mean
    using Coq's interactive queries. Prove the lemmas.
 *)
Lemma addFb : left_id false addb.    (* [addb] means XOR (eXclusive OR operation) *)
Proof.
rewrite /left_id.
by case.

Restart.

(* idiomatic solution: don't have to unfold definitions, [case] will do it for us *)
by case.
Qed.

Lemma addbF : right_id false addb.
Proof. by case. Qed.

Lemma addbC : commutative addb.
Proof.
case.
- by case.
by case.

Restart.

(* idiomatic solution: *)
by do 2 case.  (* case-analyze on the head of the "goal stack" two times in a row *)
Qed.

Lemma addbA : associative addb.
Proof.
case.
- case.
  + by case.
  by case.
case.
- by case.
by case.

Restart.

by do 3 case.
Qed.


(** Formulate analogous laws (left/right identity, commutativity, associativity)
    for boolean AND and OR and prove those.
    Find the names of corresponding lemmas in the standard library using
    [Search] command. For instance: [Search _ andb left_id.]
    Have you noticed the naming patterns?
 *)

Lemma andFb : left_id true andb.
Proof. by case. Qed.

Lemma andbF : right_id true andb.
Proof. by case. Qed.

Lemma andbC : commutative andb.
Proof. by do 2 case. Qed.

Lemma andbA : associative andb.
Proof. by do 3 case. Qed.

Lemma orFb : left_id false orb.
Proof. by case. Qed.

Lemma orbF : right_id false orb.
Proof. by case. Qed.

Lemma orbC : commutative orb.
Proof. by do 2 case. Qed.

Lemma orbA : associative orb.
Proof. by do 3 case. Qed.

End BooleanLogic.



Section NaturalNumbers.
(** Figure out what [cancel], [succn], [predn] mean
    using Coq's interactive queries. Prove the lemmas.
 *)
Lemma succnK : cancel succn predn.
Proof.
rewrite /cancel.
move=> n.
by [].

Restart.
by [].
Qed.

Lemma add0n : left_id 0 addn.
Proof.
rewrite /left_id.
move=> n.
by [].

Restart.
by [].
Qed.

Lemma addSn m n : m.+1 + n = (m + n).+1.
Proof. by []. Qed.

Lemma add1n n : 1 + n = n.+1.
Proof. by []. Qed.

Lemma add2n m : 2 + m = m.+2.
Proof. by []. Qed.

Lemma subn0 : right_id 0 subn.
Proof.
rewrite /right_id.
move=> n.
Fail by [].
case: n.
- by [].
move=> n.
by [].

Restart.
by case.
Qed.

End NaturalNumbers.
