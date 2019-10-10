From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Some basic functions *)

Definition const {A B} (a : A) :=
  fun _ : B => a.

Definition flip {A B C} (f : A -> B -> C) : B -> A -> C :=
  fun b a => f a b.

Arguments const {A B} a _ /.
Arguments flip {A B C} f b a /.


(* move to logic_exercises *)
Section IntLogic.

Variables A B C D : Prop.

Lemma axiomK :
  A -> B -> A.
Proof. exact: const. Qed.


(* note: flip is more general *)
Lemma contraposition :
  (A -> ~ B) -> (B -> ~ A).
Proof. exact: flip. Qed.


Lemma p_imp_np_iff_np : (A -> ~A)  <->  ~A.
Proof.
(* a step-by-step solution *)
split.
- rewrite /not. move=> a_na. move=> a. exact: (a_na a a).
move=> na _. exact: na.

Restart.
(* a more idiomatic solution *)
by split=> // a_na a; apply: a_na.
(**
Explanation: the proof of the last branch of the step-by-step proof
is trivial, so it can be handled with [//].
This leaves us with just the first subgoal.
[move=> a_na. move=> a.] can be merged into [move=> a_na a.]
which itself can be melded into the preceeding [split] tactic.

The [tac1; tac2] construction allows us to apply [tac2] tactic
to all the subgoals we are left with after applying [tac1] tactic.
 *)
Qed.


(* We can generalize the previous lemma into *)
Lemma p_p_q_iff_p_q :
  (A -> A -> B)  <->  (A -> B).
Proof. by split=> // a_na a; apply: a_na. Qed.


Lemma p_is_not_equal_not_p :
  ~ (A <-> ~ A).
Proof.
(** The "defective" form of [move] tactic brings the goal to
    the head normal form (hnf).
    Defective here means "not combined with anything else".
 *)
move.
(** Amounts to "unfold all definitions" in this case.
    The goal after applying [compute] tactic can be
    easier to understand, but this really depends on
    how much experience you have with unfolding those
    definitions mentally.
 *)
compute.
(** Now that we have conjunction as the top of the goal stack,
    we can have access to the individual conjuncts.
 *)
case. move=> aaf af_a.
(** Parentheses around a hypothesis let us reuse it later,
    had we omitted those, we would have it erased from the context.
 *)
apply: (aaf).
- apply: af_a. move=> a. exact: (aaf a a).
apply: af_a. move=> a. exact: (aaf a a).   (* duplication! *)

Restart.

(** A refactored version of the above proof *)
case=> aaf af_a.
(** We use [have ident : statement by tactic] form to prove [A] beforehand
    and call it [a] in the context.
  *)
have a: A by apply: af_a=> a; apply: aaf.
by apply: aaf.
Qed.


Lemma not_not_lem :
  ~ ~ (A \/ ~ A).
Proof.
move=> not_lem.
apply: (not_lem).
right.
move=> a.
apply: not_lem.
left.
exact: a.

Restart.

(** a shorter version *)
move=> not_lem; apply: (not_lem); right=> a.
by apply: not_lem; left.
Qed.

Lemma constructiveDNE :
  ~ ~ ~ A  ->  ~ A.
Proof.
move=> nnna.
move=> a.
apply: nnna.
move=> na.
apply: na.
exact: a.

Restart.

(** A shorter version *)
by move=> nnna a; apply: nnna.
Qed.

End IntLogic.




(* Boolean logic (decidable fragment enjoys classical laws) *)

Section BooleanLogic.

Lemma LEM_decidable a :
  a || ~~ a.
Proof.
by case: a.
(** the rest of the proof is by computation *)
Qed.

Lemma disj_implb a b :
  a || (a ==> b).
Proof.
by case: a.
(** Here we only need to case analyse on [a].
    Make sure you understand why.
    (Hint: look at the definitions and see if knowing the form
           of [b] is really needed here)
 *)
Qed.

Lemma iff_is_if_and_only_if a b :
  (a ==> b) && (b ==> a) = (a == b).
Proof. by case: a; case: b. Qed.

Lemma implb_trans : transitive implb.
Proof.
rewrite /transitive. move=> b a c. case: a.
- move=> /=. (* simplify goal *)
  (* The head of the goal is an (implicit) equation [b = true].
     How to check it? *)
  move->.  (* rewrite with the head of the goal stack *)
  move=> /=.
  by [].
by [].

Restart.

(** A more idiomatic version *)
by move=> b [] c //= ->.

(** Explanation:

[by move=> b [] c //= ->]
             ^    ^
             |    |
             |    solve trivial goals (//) and simplify (/=) combined
             |
             inplace case analysis ([case: a])
*)
Qed.

Lemma triple_compb (f : bool -> bool) :
  f \o f \o f =1 f.
Proof.
by case=> /=; case Et: (f true); case Ef: (f false); rewrite ?Ef ?Et.
Qed.



(* negb \o odd means "even" *)
Lemma even_add :
  {morph (negb \o odd) : x y / x + y >-> x == y}.
Proof.
move=> x y /=.
by rewrite odd_add negb_add eqb_negLR negbK.
Qed.

End BooleanLogic.


(* some properties of functional composition *)

Section eq_comp.
Variables A B C D : Type.

Lemma compA (f : A -> B) (g : B -> C) (h : C -> D) :
  h \o g \o f = h \o (g \o f).
Proof. by []. Qed.

Lemma eq_compl (f g : A -> B) (h : B -> C) :
  f =1 g -> h \o f =1 h \o g.
Proof. by move=> eq_fg; apply: eq_comp. Qed.

Lemma eq_compr (f g : B -> C) (h : A -> B) :
  f =1 g -> f \o h =1 g \o h.
Proof. by move=> eq_fg; apply: eq_comp. Qed.

Lemma eq_idl (g1 g2 : A -> B) (f : B -> B) :
  f =1 id -> f \o g1 =1 f \o g2 -> g1 =1 g2.
Proof.
move=> f_id g12f a.
move: (g12f a). move=> /=.
rewrite f_id. rewrite f_id.
done.

Restart.

(* idiomatic solution *)
by move=> f_id g12f a; move: (g12f a)=> /=; rewrite !f_id.
Qed.

Lemma eq_idr (f1 f2 : A -> B) (g : A -> A) :
  g =1 id -> f1 \o g =1 f2 \o g -> f1 =1 f2.
Proof.
by move=> g_id f12g a; move: (f12g a)=> /=; rewrite g_id.
Qed.

End eq_comp.



