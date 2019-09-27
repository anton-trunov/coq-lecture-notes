From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section IntLogic.

(* Frobenius rule: existential quantifiers and conjunctions commute *)
Lemma frobenius A (P : A -> Prop) Q :
  (exists x, Q /\ P x) <-> Q /\ (exists x, P x).
Admitted.

Lemma exist_conj_commute A (P Q : A -> Prop) :
  (exists x, P x /\ Q x) -> (exists x, P x) /\ (exists x, Q x).
Proof.
Admitted.

Lemma conj_exist_does_not_commute :
  ~ (forall A (P Q : A -> Prop),
       (exists x, P x) /\ (exists x, Q x) -> (exists x, P x /\ Q x)).
Proof.
Admitted.

(* helper lemma *)
Lemma curry_dep A (P : A -> Prop) Q :
  ((exists x, P x) -> Q) -> (forall x, P x -> Q).
Proof. move=> f x px. exact: (f (ex_intro _ x px)). Qed.

Definition not_forall_exists :=
  forall A (P : A -> Prop),
    ~ (forall x, ~ P x) -> (exists x, P x).

(* Double negation elimination *)
Definition DNE := forall (P : Prop), ~ ~ P -> P.

Lemma not_for_all_is_exists_iff_dne :
  not_forall_exists <-> DNE.
Proof.
Admitted.

End IntLogic.



Section BooleanLogic.

(** [==] is decidable equality operation for types with dec. eq.
    In case of booleans it means [if and only if]. *)
Fixpoint mostowski_equiv (a : bool) (n : nat) :=
  if n is n'.+1 then mostowski_equiv a n' == a
  else a.

(* ((a == a ...) == a) == a *)

Lemma mostowski_equiv_even_odd a n :
  mostowski_equiv a n = a || odd n.
Proof.
Admitted.

End BooleanLogic.


Section Arithmetics.

Lemma addnCB m n : m + (n - m) = m - n + n.
Proof.
Admitted.

Lemma addnBC m n : n - m + m = m - n + n.
Proof.
Admitted.

Lemma addnBC' : commutative (fun m n => m - n + n).
Proof.
Admitted.

Lemma subn_sqr m n : m ^ 2 - n ^ 2 = (m - n) * (m + n).
Proof.
Admitted.

Lemma leq_sub_add n m p : n - m <= n + p.
Proof.
Admitted.

(* prove by induction *)
Lemma odd_exp m n : odd (m ^ n) = (n == 0) || odd m.
Proof.
Admitted.

End Arithmetics.



Section Misc.
(** Exlpain why the folloing statement is unprovable *)

Definition const {A B} : A -> B -> A := fun a _ => a.

Lemma const_eq A B (x y : A) :
  @const A B x = const y -> x = y.
Abort.

End Misc.
