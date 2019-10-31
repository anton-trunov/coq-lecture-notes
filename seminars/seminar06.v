From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section EqType.

Lemma eq_sym (T : eqType) (x y : T) :
  (x == y) = (y == x).
Proof.
  apply /eq_sym.
Qed.
(* ^ Hint: use apply/view1/view2 mechanism *)


(** Define equality type for the following datatype *)
Inductive tri :=
| Yes | No | Maybe.

Definition eq_tri (x y: tri) : bool :=
  match x, y with
  | Yes,Yes => true
  | No,No => true
  | Maybe,Maybe => true
  | _,_ => false
  end.

(* forall x y : tri, eq_tri x y = true <-> x = y. *)
Lemma eq_tri_correct : Equality.axiom eq_tri.
Proof.
  move=> x y.
  by case: x; case: y; constructor.
  (* - case x ; by case y. *)
  (* - move=> ->. by case y. *)
Qed.

Definition tri_eq_mixin := EqMixin eq_tri_correct.

Canonical tri_eqType := EqType tri tri_eq_mixin.
(** This should not fail! *)
Check (1, Yes) == (1, Maybe).
Compute (1, Yes) == (1, Maybe).

(** Define equality type for the [Empty_set] datatype *)
(** This should not fail! *)
Definition eq_Empty (x y: Empty_set) : bool :=
  false.

Lemma eq_empty_correct : Equality.axiom eq_Empty.
Proof.
  by [].
Qed.

Definition empty_eq_mixin := EqMixin eq_empty_correct.


Canonical empty_eqType := EqType Empty_set empty_eq_mixin.

Check fun v : Empty_set => (1, v) == (1, v).


Lemma predU1P (T : eqType) (x y : T) (b : bool) :
  reflect (x = y \/ b) ((x == y) || b).
Proof.
  case: b.
  (* Search _ (_ || true). *)
  - rewrite orbT. apply: ReflectT. by right.
    (* Search _ (true || _). *)
    case E: (x == y).
    + rewrite orTb. apply: ReflectT. left. move: E. by move /eqP.
      rewrite orbF. apply: ReflectF. move: E. move /eqP. move=> xny.
      case.
      * assumption.
      * done.
  Restart.
   case: b.
  (* Search _ (_ || true). *)
  - rewrite orbT. apply: ReflectT. by right.
    (* Search _ (true || _). *)
    case: eqP.
    move=> ->. apply: ReflectT.
    + by left. rewrite orbF. move=> Hxny. constructor. rewrite /not.
      move=> H. case: H.
      * exact Hxny.
        exact.
Qed.

Variables (A B : eqType) (f : A -> B) (g : B -> A).

(* Функция инъективна, когда
   forall a, b \in X, f(a) = f(b) -> a = b
 *)
(* Inductive reflect (P : Prop) : bool -> Set := *)
(*     ReflectT : P -> reflect P true *)
(*   | ReflectF : ~ P -> reflect P false *)
(* eqP *)
(*      : reflect (?x = ?y) (?x == ?y) *)

Lemma inj_eq : injective f -> forall x y, (f x == f y) = (x == y).
Proof.
  rewrite /injective. move=> Hinj x y. case: eqP.
  - move /Hinj.
    (* Как вместо этих 2-х команд применить Hinj к голове цели?
       move=> Hf. apply Hinj in Hf.
    *)
    case: eqP => //=.
  - rewrite /not. move=> Hf. case: eqP => //=. move=> Hxy.
    rewrite <- Hxy in Hf. case: (Hf (@erefl B (f x))).
Qed.


Lemma can_eq : cancel f g -> forall x y, (f x == f y) = (x == y).
Proof.
  rewrite /cancel. move=> HRevExists x y. case: eqP.
  - move=> Hf. case: eqP=> //=. rewrite /not. move=> Hxny.
    set (Ex := HRevExists x).
    rewrite <- Ex in Hxny.
    rewrite Hf in Hxny.
    rewrite HRevExists in Hxny.
    case: (Hxny erefl).
  - move=> Hf. case: eqP=> //=. move=> Hxy.
    (* rewrite <- Hxy in Hf. case: (Hf erefl).*)
     move: Hf. move: Hxy <-. by case.
Qed.

Search "addnI".

Lemma eqn_add2l p m n : (p + m == p + n) = (m == n).
Proof.
  case: eqP.
  - move=> H. apply addnI in H. move: H ->. by rewrite eq_refl.
    move=> H. case: eqP=> //=. move=> Eq. rewrite Eq in H. by case: H.
    Restart.
    case : (@eqP nat_eqType (p + m) (p + n)).
  - move => H.
    rewrite (addnI H).
    rewrite eq_refl.
    reflexivity.
  - case (@eqP nat_eqType m n).
    + move -> => contra.
      case (contra erefl).
    + reflexivity.
Restart.
  case (@eqP nat_eqType m n).
  - move ->. rewrite eq_refl. reflexivity.
  - move => H.
    case eqP => //.
    move => H1.
    rewrite (addnI H1) in H.
    case (H erefl).
Qed.

(* Set Printing All. *)
(* Print leq. *)
(* ltn0  forall n : nat, (n < 0) = false *)
(* exp0n  forall n : nat, 0 < n -> 0 ^ n = 0 *)
(* Lemma expn_m_n_plus_ne0: forall (n m : nat), (m <> 0) -> (m ^ n.+1 <> 0). *)
(* Proof. *)
(*   move=> n m. move: n. elim: (m). *)
(*   - move=> n contra. case: (contra erefl). *)
(*   - move=> n IH n0 H. rewrite expnS. *)
(*   Qed. *)

Lemma expn_eq0 m e : (m ^ e == 0) = (m == 0) && (e > 0).
Proof.
  case: (@eqP nat_eqType m 0).
  - move=> H. rewrite -> H. case: e=> //=. move=> n. rewrite -> exp0n => //.
  - move=> H. case: e.
    + rewrite expn0.
      rewrite -[eq_op (S O) O]/false.
      (* rewrite -/(false=false). *)
      (* rewrite -[RHS]/false. *)
      rewrite -[leq (S O) O]/false.
      rewrite -[false && false]/false. by [].
      (* expn_eq0  forall m e : nat, (m ^ e == 0) = (m == 0) && (0 < e) *)
    + move=> n. rewrite ltn0Sn. rewrite expn_eq0. rewrite ltn0Sn. rewrite Bool.andb_false_l. rewrite Bool.andb_true_r. case: eqP.
      * move=> Hm0. contradiction.
      * exact.
Qed.

(* Print in_mem. *)
Search _ (_ \notin _).
Lemma seq_last_notin (s : seq A) x :
        last x s \notin s = (s == [::]).
Proof.
  case: memPn=> H.
  elim: s=> /=.
  - apply: esym. apply: eq_refl.
  - move=> a l. case: l=> /=.
    + rewrite eq_refl=> _.


End EqType.
