From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section EqType.

Lemma eq_sym (T : eqType) (x y : T) :
  (x == y) = (y == x).
Proof.
Admitted.
(* ^ Hint: use apply/view1/view2 mechanism *)


(** Define equality type for the following datatype *)
Inductive tri :=
| Yes | No | Maybe.
(** This should not fail! *)
Fail Check (1, Yes) == (1, Maybe).


(** Define equality type for the [Empty_set] datatype *)
(** This should not fail! *)
Fail Check fun v : Empty_set => (1, v) == (1, v).


Lemma predU1P (T : eqType) (x y : T) (b : bool) :
  reflect (x = y \/ b) ((x == y) || b).
Proof.
Admitted.


Variables (A B : eqType) (f : A -> B) (g : B -> A).

Lemma inj_eq : injective f -> forall x y, (f x == f y) = (x == y).
Proof.
Admitted.


Lemma can_eq : cancel f g -> forall x y, (f x == f y) = (x == y).
Proof.
Admitted.


Lemma eqn_add2l p m n : (p + m == p + n) = (m == n).
Proof.
Admitted.


Lemma expn_eq0 m e : (m ^ e == 0) = (m == 0) && (e > 0).
Proof.
Admitted.


Lemma seq_last_notin (s : seq A) x :
        last x s \notin s = (s == [::]).
Proof.
Admitted.

End EqType.

