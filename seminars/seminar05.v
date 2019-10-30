From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



Section LeftPad.

(**
What is "leftpad"?

Leftpad is a function that takes a character, a length, and a string, and pads the string to that length.
It pads it by adding the character to the left.

Compute leftpad 0 5 [:: 1; 2; 3]. (* = [:: 0; 0; 1; 2; 3] *)
Compute leftpad 0 2 [:: 1; 2; 3]. (* = [:: 1; 2; 3]  *)
*)


(* [def] is the default value, i.e. type T is not empty *)
Variables (T : Type) (def : T).

(** Define the leftpad function, modeling strings as sequences of elements of type [T] *)

Definition leftpad (c : T) (n : nat) (s : seq T) : seq T :=
  ncons (n - size s) c s.

(** The following properties of the leftpad function *)

Lemma length_max_spec c n s :
  size (leftpad c n s) = maxn n (size s).
Proof. by rewrite size_ncons addnC maxnC maxnE. Qed.

(** Local alias for the [nth] function returning the n-th element of the input sequence *)
Local Notation nth := (nth def).

Lemma prefix_spec c n s :
  forall i, i < n - size s -> nth (leftpad c n s) i = c.
Proof. by move=> i; rewrite nth_ncons => ->. Qed.

Lemma suffix_spec c n s :
  forall i, i < size s -> nth (leftpad c n s) (n - size s + i) = nth s i.
Proof. by move=> i _; rewrite nth_ncons addKn ifN // -ltnNge leq_addr. Qed.

End LeftPad.



Section MoreInductionExercises.

(** Implement a recursive function performing integer division by 2 *)
Fixpoint div2 (n : nat) : nat :=
  if n is n''.+2 then (div2 n'').+1
  else n.-1.

(* You might want to uncomment the following: *)
Arguments div2 : simpl nomatch.

Lemma nat_ind2' (P : nat -> Prop) :
  P 0 ->
  P 1 ->
  (forall n, P n -> P n.+2) ->
  forall n, P n.
Proof.
move=> p0 p1 Istep n; suffices: P n /\ P n.+1 by case.
by elim: n=> // n [/Istep].
Qed.

Lemma div2_le n : div2 n <= n.
Proof.
by elim/nat_ind2': n => //= n /leqW IHn; rewrite ltnS.
Qed.

Lemma div2_correct n :
  div2 n = n./2.
Proof. by elim/nat_ind2': n=> //= n ->. Qed.



(** Strong induction principle *)
Lemma lt_wf_ind (P : nat -> Prop) :
  (forall m, (forall k : nat, (k < m) -> P k) -> P m) ->
  forall n, P n.
Proof.
move=> step n.
(* complete induction *)
elim: n {-2}n (leqnn n) => [[_|//] | n IHn k le_kSn]; first by apply: step.
apply: step => j /leq_trans - /(_ _ le_kSn); rewrite ltnS.
exact: IHn.
Qed.


Fixpoint divn_my (n m : nat) {struct n} : nat :=
  if m is m'.+1 then
    if n - m' is d.+1 then
      (divn_my d m).+1
    else 0
  else 0.

Lemma divn_my_correct2 n m :
  divn_my n m = divn n m.
Proof.
(* complete induction *)
elim: n {-2}n (leqnn n) m => [|n IHn]; first by case=> // _; case.
case=> [_ [] // | n' le_n'Sn [//| m /=]].
case eq_sub: (n'.+1 - m) => [|d]; first by rewrite divn_small // -subn_eq0 subSS eq_sub.
move: (congr1 predn eq_sub)=> /= <-; rewrite subSKn.
rewrite IHn ?(leq_trans (leq_subr m n')) //.
rewrite -[in RHS](@subnK m.+1 n'.+1) -1?subn_gt0 ?eq_sub //.
by rewrite addnC -{2}(mul1n m.+1) divnMDl.
Qed.


Fixpoint fib (n : nat) : nat :=
  if n is (n''.+1 as n').+1 then fib n'' + fib n'
  else n.
Arguments fib n : simpl nomatch.

(* proved in seminar 04, repeating the proofs here to bypass project management in Coq *)
Lemma fib_add_succ m n :
  fib (m + n).+1 = fib m.+1 * fib n.+1 + fib m * fib n.
Proof.
elim: m n=> [|m IHm] n; first by rewrite mul1n addn0.
rewrite addSnnS IHm /=.
by rewrite mulnDl mulnDr addnAC -addnA addnC.
Qed.

(* proved in seminar 04 *)
Lemma leq_add1l p m n :
  m <= n -> m <= p + n.
Proof. by move/(leq_add (leq0n _)); apply. Qed.

(* proved in seminar 04 *)
Lemma fib_monotone m n :
  m <= n -> fib m <= fib n.
Proof.
elim: n=> [|[|n] IHn]; first by case: m.
- by case: {IHn}m=> [|[]].
rewrite /= leq_eqVlt => /orP[/eqP->// | /IHn].
by apply: leq_add1l.
Qed.

From Coq Require Import Psatz.  (* to use [lia] tactic *)

Lemma fib3 n :
  fib (3*n).+1 = (fib n.+1)^3 + 3 * fib n.+1 * (fib n)^2 - (fib n)^3.
Proof.
rewrite ![in LHS]mulSnr mul0n add0n !fib_add_succ mulnDl !mulnn -expnSr.
rewrite -addnBA; last by rewrite -(mul1n (_ ^ 3)) -mulnA leq_mul ?expnS ?leq_mul ?fib_monotone.
case: n=> // n; rewrite addSn fib_add_succ /=.
(* optional step, it's here just to clarify the form of the goal for the human *)
move: (fib n) (fib n.+1) => x y.
(* massage the goal so the [lia] tactic is able to finish it off *)
rewrite !expnS !expn0 !muln1 -!plusE -!multE -!minusE; lia.
Qed.

End MoreInductionExercises.

