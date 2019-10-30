From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** Implement an instance of equality type for the [seq] datatype *)



(** Take apart the following proof: *)
Lemma size_eq0 (T : eqType) (s : seq T) :
  (size s == 0) = (s == [::]).
Proof. exact: (sameP nilP eqP). Qed.



Lemma filter_all T (a : pred T) s :
  all a (filter a s).
Admitted.

Lemma filter_id T (a : pred T) s :
  filter a (filter a s) = filter a s.
Admitted.

Lemma all_count T (a : pred T) s :
  all a s = (count a s == size s).
Admitted.

Lemma all_predI T (a1 a2 : pred T) s :
  all (predI a1 a2) s = all a1 s && all a2 s.
Admitted.

Lemma allP (T : eqType) {a : pred T} {s : seq T} :
  reflect {in s, forall x, a x} (all a s).
(* Hint 1: *)
(* rewrite /prop_in1. *)

(* Hint 2a and 2b: *)
(* Check erefl : 1 \in [:: 3; 2; 1; 0] = true. *)
(* Check erefl : 42 \in [:: 3; 2; 1; 0] = false. *)
Admitted.

Lemma sub_find T (a1 a2 : pred T) s :
  subpred a1 a2 ->
  find a2 s <= find a1 s.
Admitted.

Lemma take_nseq T n m (x : T) : take n (nseq m x) = nseq (minn n m) x.
Admitted.

Lemma rev_nseq A n (x : A) : rev (nseq n x) = nseq n x.
Admitted.

(* Hint: use mapP *)
Lemma mem_map (T1 T2 : eqType) (f : T1 -> T2) x s :
  injective f ->
  (f x \in map f s) = (x \in s).
Admitted.

(* Double induction principle *)
Lemma seq_ind2 {S T} (P : seq S -> seq T -> Type) :
    P [::] [::] ->
    (forall x y s t, size s = size t -> P s t -> P (x :: s) (y :: t)) ->
  forall s t, size s = size t -> P s t.
Admitted.

(* Hint: use seq_ind2 to prove the following *)
Lemma rev_zip S T (s : seq S) (t : seq T) :
  size s = size t -> rev (zip s t) = zip (rev s) (rev t).
Admitted.

Lemma last_ind T (P : seq T -> Prop) :
  P [::] -> (forall s x, P s -> P (rcons s x)) -> forall s, P s.
Admitted.

(* Hint: use last_ind to prove the following *)
Lemma nth_rev T (x0 : T) n (s : seq T) :
  n < size s -> nth x0 (rev s) n = nth x0 s (size s - n.+1).
Admitted.


