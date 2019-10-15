From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


From Coq Require Import Omega.

Section InductionExercises.

Fixpoint triple (n : nat) : nat :=
  if n is n'.+1 then (triple n').+3
  else n.

Lemma triple_mul3 n :
  triple n = 3 * n.
Proof.
by elim: n=> //= n ->; rewrite mulnS.
Qed.

Lemma double_inj m n :
  m + m = n + n -> m = n.
Proof.
elim: m n=> [| m IHm] [|n]=> //.
by rewrite !addnS !addSn => [[]] /IHm->.
Qed.


(** Write a tail-recursive variation of the [addn] function
    (let's call it [addn_iter]).
    See https://en.wikipedia.org/wiki/Tail_call
 *)
Fixpoint add_iter (n m : nat) {struct n}: nat :=
  if n is n'.+1 then add_iter n' m.+1
  else m.

Lemma add_iter_correct n m :
  add_iter n m = n + m.
Proof.
elim: n=> //= n IHn.
(* Cannot apply IHn here because it expects the second argument to be [m], and not [m.+1]
   Anyways, lets try and massage the goal to rewrite with [IHn] from right to left.
 *)
rewrite addSn.
rewrite -IHn.
Fail done.  (* Convince yourself that we are stuck *)

Restart.
(* To proceeded we needed the induction hypothesis to be general in its second argument.
   To do that we need to generalize our goal before applying induction.
 *)
move: m.
elim: n.
- move=> m. move=> /=. done.
move=> n IHn m.
move=> /=.
rewrite IHn. rewrite addnS. done.  (* and now we are properly done *)

Restart.

(* Idiomatic solution: *)
by elim: n m=> //= n IHn m; rewrite IHn addnS.
Qed.

Fixpoint fib (n : nat) : nat :=
  if n is (n''.+1 as n').+1 then fib n'' + fib n'
  else n.
Arguments fib n : simpl nomatch.

Lemma leq_add1l p m n :
  m <= n -> m <= p + n.
Proof. by move/(leq_add (leq0n _)); apply. Qed.

Lemma fib_monotone m n :
  m <= n -> fib m <= fib n.
Proof.
elim: n=> [|[|n] IHn]; first by case: m.
- by case: {IHn}m=> [|[]].
rewrite /= leq_eqVlt => /orP[/eqP->// | /IHn].
by apply: leq_add1l.
Qed.

Lemma fib_add_succ m n :
  fib (m + n).+1 = fib m.+1 * fib n.+1 + fib m * fib n.
Proof.
elim: m n=> [|m IHm] n; first by rewrite mul1n addn0.
rewrite addSnnS IHm /=.
by rewrite mulnDl mulnDr addnAC -addnA addnC.
Qed.

End InductionExercises.



(* Thanks to Mike Potanin for pointing me to this example *)
(* https://en.wikipedia.org/wiki/Eckmann–Hilton_argument *)

Section EckmannHilton.

Context {X : Type}.
Variables f1 f2 : X -> X -> X.

Variable e1 : X.
Hypothesis U1 : left_id e1 f1 * right_id e1 f1.

Variables e2 : X.
Hypothesis U2 : left_id e2 f2 * right_id e2 f2.

Hypothesis I : interchange f1 f2.

Lemma units_same :
  e1 = e2.
Proof. by move: (I e1 e2 e2 e1); rewrite !(U1, U2). Qed.

Lemma operations_equal :
  f1 =2 f2.
Proof. by move=> a b; move: (I a e1 e1 b); rewrite !U1 units_same !U2. Qed.

Lemma I1 : interchange f1 f1.
Proof. by move=> a b c d; move: (I a b c d); rewrite -!operations_equal. Qed.

Lemma operations_comm :
  commutative f1.
Proof. by move=> a b; move: (I1 e1 a b e1); rewrite !U1. Qed.

Lemma operations_assoc :
  associative f1.
Proof. by move=> a b c; move: (I1 a e1 b c); rewrite !U1. Qed.

End EckmannHilton.
