From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section BooleanReflection.

(** A spec for boolean equality *)
Variant eq_xor_neq (T : eqType) (x y : T) : bool -> bool -> Set :=
  | EqNotNeq of x = y : eq_xor_neq x y true true
  | NeqNotEq of x != y : eq_xor_neq x y false false.

Lemma eqVneq (T : eqType) (x y : T) :
  eq_xor_neq x y (y == x) (x == y).
Proof. by rewrite eq_sym; case: (altP eqP); constructor. Qed.

(* Use eqVneq to prove the following lemma.
   Hint: use [case: eqVneq] *)
Lemma eqVneq_example (T : eqType) (w x y z : T) :
  w == x -> z == y ->
  (x == w) /\ (y == z) /\ (z == y).
Proof. by case: eqVneq; case: eqVneq. Qed.

Lemma andX (a b : bool) : reflect (a * b) (a && b).
Proof. by case: a; case: b; constructor=> //; case. Qed.

Arguments andX {a b}.

(** Solve the following lemma using [andX] lemma
    and [rewrite] tactic *)
Lemma andX_example a b :
  a && b -> b && a && a && b.
Proof. by move=> ab; rewrite !(andX ab). Qed.

(* one can rewrite with andX *)

End BooleanReflection.




Section RecursionSchemes.

Lemma foldr_fusion {A B C} (f : A -> B -> B) (v : B)
      (g : A -> C -> C) (w : C) (h : C -> B) :
  h w = v ->
  (forall x y, h (g x y) = f x (h y)) ->
  (h \o foldr g w) =1 foldr f v.
Proof.
move=> h_acc h_gf.
elim => //= x xs IHxs; by rewrite h_gf IHxs.
Qed.

Definition flip {A B C} (f : A -> B -> C) := fun x y => f y x.

Lemma foldl_via_foldr A B (f : B -> A -> B) :
  flip (foldr (fun x rec => rec \o (flip f x)) id) =2 foldl f.
Proof. by rewrite /flip; move=> v xs; elim: xs v=> /=. Qed.


Lemma foldl_via_foldr2 {A B} (f : B -> A -> B) v :
  (foldr (flip f) v) \o rev =1 foldl f v.
Proof.
move=> xs; elim: xs v => //= x xs IH v.
by rewrite -cat1s rev_cat foldr_cat /= IH.
Qed.


(* Let's generalize left and right folds over lists.
   We do that by factoring out the recursive call.
   So, instead of the combining function of type
   A -> B -> B we use
   A -> B -> (B -> B) -> B,
   where (B -> B) represents the recursive calls.
   See a couple of lemmas below explaining how it works.
   *)
Definition foldk {A B : Type} (f : A -> B -> (B -> B) -> B) :=
  fix rec (acc : B) (xs : list A) :=
    if xs is x :: xs' then
      f x acc (fun acc2 => rec acc2 xs')
    else acc.
(* The "k" suffix suggests "continuation" here *)

Lemma foldr_via_foldk A B (f : A -> B -> B) :
  foldk (fun a b k => f a (k b)) =2 foldr f.
Proof. by move=> acc; elim=> //= x xs ->. Qed.

Lemma foldl_via_foldk A B (f : B -> A -> B) :
  foldk (fun a b k => k (f b a)) =2 foldl f.
Proof. by []. Qed.

End RecursionSchemes.



Section IntLogic.

(* Prove that having a general fixed-point combinator in Coq
   would be incosistent *)
Definition FIX := forall A : Type, (A -> A) -> A.

Lemma not_fix :
  FIX -> False.
Proof.
by move/(_ False id).

Restart.

exact.
Qed.

End IntLogic.


