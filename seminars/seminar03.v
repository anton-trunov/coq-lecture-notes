From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section IntLogic.

(* Frobenius rule: existential quantifiers and conjunctions commute *)
Lemma frobenius A (P : A -> Prop) Q :
  (exists x, Q /\ P x) <-> Q /\ (exists x, P x).
Proof.
split.
- case. move=> x. case. move=> q px. split.
  + exact: q.
  exists x. exact: px.
case. move=> q. case. move=> x px. exists x. split.
- exact: q.
exact: px.

Restart.

(* idiomatic solution *)
split.
- by case=> x [q px]; split=> //; exists x.
by case=> [q [x px]]; exists x.
Qed.

Lemma exist_conj_commute A (P Q : A -> Prop) :
  (exists x, P x /\ Q x) ->
  (exists x, P x) /\ (exists x, Q x).
Proof. by case=> [x [px qx]]; split; exists x. Qed.

(* Elegant solution by Vasiliy Yorkin *)
Lemma conj_exist_does_not_commute :
  ~ (forall A (P Q : A -> Prop),
        (exists x, P x) /\ (exists x, Q x) ->
        (exists x, P x /\ Q x)).
Proof.
move/(_ bool id not); case=> [|x [] //].
by split; [exists true | exists false].
Qed.

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
rewrite /not_forall_exists /DNE; split=> [nfe | dne].
- move=> P nnP. move: (nfe True (fun _ => P)).
  by case/(_ (fun t_notP => nnP (t_notP I))).
by move=> A P nAll; apply: dne=> /curry_dep/nAll.
Qed.

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
by elim: n=> [|n /= ->]; case: a=> //; rewrite eqbF_neg.
Qed.

End BooleanLogic.


Section Arithmetics.

Lemma addnCB m n : m + (n - m) = m - n + n.
Proof.
(* a step-wise solution *)
Search _ (?m + (?n - ?m)).
rewrite -maxnE.
rewrite maxnC.  (* we already know the "C" suffix stands for "commutative" *)
rewrite maxnE.
rewrite addnC.
done.

Restart.
(* idiomatic solution *)
by rewrite -maxnE maxnC maxnE addnC.
Qed.

Lemma addnBC m n : n - m + m = m - n + n.
Proof. by rewrite addnC addnCB. Qed.

Lemma addnBC' : commutative (fun m n => m - n + n).
Proof. by move=> m n; apply: addnBC. Qed.


Lemma example_for_rewrite_patterns m n :
  m * n + m * n + m * n + n * m
  =
  m * n + m * n + m * n + n * m.
Proof.
(*
  Parenthesized goal:
         X
  /--------------\
  ((m * n + m * n) + m * n) + n * m
  =
  ((m * n + m * n) + m * n) + n * m
    \___________/
         X
*)
rewrite [in X in X + _ + _]mulnC.
done.
Abort.

Lemma subn_sqr m n : m ^ 2 - n ^ 2 = (m - n) * (m + n).
Proof.
by rewrite mulnBl !mulnDr addnC mulnC subnDl.
Qed.

Lemma leq_sub_add n m p : n - m <= n + p.
Proof. by rewrite leq_subLR addnCA leq_addr. Qed.

(* prove by induction *)
Lemma odd_exp m n : odd (m ^ n) = (n == 0) || odd m.
Proof.
elim: n=> //= n IHn.
Search _ (_ ^ _.+1 = _ * _) in ssrnat.
rewrite expnS.
Search _ (odd (_ * _)).
rewrite odd_mul.
rewrite IHn.
Search _ (?b && (_ || ?b)).
rewrite orKb.
done.

Restart.

(* idiomatic solution: *)
by elim: n=> //= n IHn; rewrite expnS odd_mul IHn orKb.
Qed.

End Arithmetics.



Section Misc.
(** Exlpain why the following statement is unprovable *)

Definition const {A B} : A -> B -> A := fun a _ => a.
(* [/] means "allow simplification after all the arguments before the slash symbol are supplied" *)
Arguments const {A B} a b /.

Lemma const_eq A B (x y : A) :
  @const A B x = const y -> x = y.
Proof.
(** Explanation:
    If we had an inhabitant of type [B], i.e. some [b : B],
    we could apply [const x] and [const y] to [b], getting
    [x = y] after redusing the beta-redexes as follows: *)

have b: B by admit. (* assume we can construct [b] of type [B] *)

by move=> /(congr1 (@^~ b)).
(** [@^~ b] stands for (fun f => f b), i.e. application at [f].

    move/(congr1 (@^~ b))

turns an equality between two functions [f1] and [f2], i.e. [f1 = f2],
into the following equality [f1 b = f2 b] *)

(** Now, the problem here is that [B] is an arbitrary type, so
   it might be empty meaning we would never come up with a proof for the admitted goal. *)
Abort.


(** Yet another explanation of the above unprovability fact
    It is known that Coq's theory is compatible with the axiom of functional extensionality.
    This means that is we assume that axiom, then proving [const_eq] must not
    lead to a contradition.
    Let's show this is not the case here.
 *)

Axiom fext : forall A (B : A -> Type) (f1 f2 : forall x, B x),
               (forall x, f1 x = f2 x) -> f1 = f2.

Lemma not_const_eq : ~ (forall A B (x y : A),
  @const A B x = const y -> x = y).
Proof.
move=> /(_ bool Empty_set false true) H.
apply/notF/H.
by apply: fext.
Qed.

End Misc.
