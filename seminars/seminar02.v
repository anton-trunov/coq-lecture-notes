From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Some basic functions *)

Definition const {A B} (a : A) := fun _ : B => a.

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
Admitted.


(* We can generalize the previous lemma into *)
Lemma p_p_q_iff_p_q : (A -> A -> B)  <->  (A -> B).
Admitted.


Lemma p_is_not_equal_not_p :
  ~ (A <-> ~ A).
Admitted.


Lemma not_not_lem :
  ~ ~ (A \/ ~ A).
Admitted.


Lemma constructiveDNE :
  ~ ~ ~ A  ->  ~ A.
Admitted.

End IntLogic.




(* Boolean logic (decidable fragment enjoys classical laws) *)

Section BooleanLogic.

Lemma LEM_decidable a :
  a || ~~ a.
Admitted.

Lemma disj_implb a b :
  a || (a ==> b).
Admitted.

Lemma iff_is_if_and_only_if a b :
  (a ==> b) && (b ==> a) = (a == b).
Admitted.

Lemma implb_trans : transitive implb.
Admitted.

Lemma triple_compb (f : bool -> bool) :
  f \o f \o f =1 f.
Admitted.

(* negb \o odd means "even" *)
Lemma even_add :
  {morph (negb \o odd) : x y / x + y >-> x == y}.
Admitted.

End BooleanLogic.


(* some properties of functional composition *)

Section eq_comp.
Variables A B C D : Type.

Lemma compA (f : A -> B) (g : B -> C) (h : C -> D) :
  h \o g \o f = h \o (g \o f).
Admitted.

Lemma eq_compl (f g : A -> B) (h : B -> C) :
  f =1 g -> h \o f =1 h \o g.
Admitted.

Lemma eq_compr (f g : B -> C) (h : A -> B) :
  f =1 g -> f \o h =1 g \o h.
Admitted.

Lemma eq_idl (g1 g2 : A -> B) (f : B -> B) :
  f =1 id -> f \o g1 =1 f \o g2 -> g1 =1 g2.
Proof.
Admitted.

Lemma eq_idr (f1 f2 : A -> B) (g : A -> A) :
  g =1 id -> f1 \o g =1 f2 \o g -> f1 =1 f2.
Proof.
Admitted.

End eq_comp.



