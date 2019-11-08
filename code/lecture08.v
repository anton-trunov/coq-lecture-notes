From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



(** * Subtyping *)

(** A subtype extends another type by adding
    a property. The new type has a richer theory.
    The new type should inherit all the original
    theory. *)

(* Let's define the type of homogeneous tuples *)

(** ** Standard [sig] type *)

Print sig.
(**
  Inductive sig (A : Type) (P : A -> Prop) : Type :=
    | exist : forall x:A, P x -> sig P.

  Notation "{ x : A  |  P }" :=
    (sig (A:=A) (fun x => P)) : type_scope.
*)

(** [sig] type is almost the same as the [ex] type encoding
    existential quantifier *)
Print ex.
(**
  Inductive ex (A : Type) (P : A -> Prop) : Prop :=
    | ex_intro : forall x:A, P x -> ex P.
 *)

(** simple definition relying on the existing [pred] function *)
Definition predecessor (x : {n | 0 < n}) : nat :=
  let: (exist m prf_m_gt_0) := x in
  m.-1.

(** The _convoy pattern_ : *)
Definition pred_dep (x : {n | 0 < n}) : nat :=
  let: (exist n prf_n_gt_0) := x in
  match n as n return (0 < n -> nat) with
  | 0 =>
      fun prf : 0 < 0 => False_rect _ (notF prf)
  | n'.+1 =>
      fun _ => n'
  end prf_n_gt_0.


(** ** Some issues *)

(** Proof irrelevance *)

Lemma eq_sig T (P : T -> Prop) x (px : P x) (px' : P x) :
  (exist P x px) = (exist P x px').
Proof.
Fail by done.
(** we are stuck: we need proof irrelevance here *)
Abort.

Axiom proof_irrelevance :
  forall (P : Prop) (pf1 pf2 : P), pf1 = pf2.

Lemma eq_sig T (P : T -> Prop) x (px : P x) (px' : P x) :
  (exist P x px) = (exist P x px').
Proof.
rewrite [px]proof_irrelevance.
done.
Qed.

(** Decidable propositions _are_ proof irrelevant *)

Check eq_irrelevance.
(**
eq_irrelevance
     : forall (T : eqType) (x y : T)
         (e1 e2 : x = y),
         e1 = e2

This special case of proof irrelevance is called
_Unicity of Identity Proofs_ principle (UIP).
*)

(** [sval] projection is injective for decidable propositions : *)
Lemma eq_n_gt0 (m n : {n | 0 < n}) :
  sval m = sval n ->
  m = n.
Proof.
case: m=> [m pfm]; case: n=> [n pfn] /=.
Fail move=> ->.  (* because of the dependencies *)
move=> eq_mn; move: eq_mn pfm pfn.
move=> -> *.
congr exist.
exact: eq_irrelevance.
Qed.

(** We cannot define [proj1_sig] as a coercion *)

(**
This is because we cannot specify the target
class of this tentative coercion:
  Coercion proj1_sig : sig >-> ???.
 *)


(** ** Mathcomp's [subType]
       (defined in [eqtype] library) *)

Print subType.
(**
  Structure subType (T : Type) (P : pred T) : Type :=
    SubType {
      (* new type *)
      sub_sort : Type;

      (* projection, like proj_sig1 *)
      val : sub_sort -> T;

      (* constructor *)
      Sub : forall x : T, P x -> sub_sort;

      (* elimination principle *)
      _ : forall K : sub_sort -> Type,
          (forall (x : T) (Px : P x), K (Sub x Px)) ->
          forall u : sub_sort, K u;

      (* projection is injective *)
      _ : forall (x : T) (Px : P x),
          val (Sub x Px) = x
    }.
*)


(** An example of a [subType] *)
Section PosSubtype.

Inductive pos := Positive m of 0 < m.

Coercion nat_of_pos p :=
  let: Positive n _ := p in n.

Variables p1 p2 : pos.

(** This is something not possible with
    {n | 0 < n} type *)
Check p1.-1 + p2.
Set Printing Coercions.
Check p1.-1 + p2.
Unset Printing Coercions.

(** Register [pos] as a [subType] *)
Canonical pos_subType :=
  [subType for nat_of_pos].

(** Given that propositions are expressed as
    booleans, we can use the fact that proofs of
    these properties are irrelevant. *)

(** Hence we can build subtypes and prove that
    the projection to the supertype is injective,
    which lets us inherit all of the theory of
    the supertype. *)

(** E.g. we can make [pos] inherit [eqType]
    from [nat] type with a bit of boilerplate *)

Definition pos_eqMixin :=
  Eval hnf in [eqMixin of pos by <:].

Canonical pos_eqType :=
  Eval hnf in EqType pos pos_eqMixin.

Check p1 == p2.

End PosSubtype.


(** * Some standard [subType]s *)

(** ** [ordinal]: type of finite ordinals *)

(**
[ordinal n] = {0, 1, ... , n-1}

Inductive ordinal : predArgType :=
  | Ordinal m of m < n.

Notation "''I_' n" := (ordinal n)

 *)

From mathcomp Require Import fintype.

Definition i1 : 'I_2 :=
  Ordinal (erefl : 0 < 2).

Definition i2 : 'I_2 :=
  Ordinal (erefl : 1 < 2).

Compute i1 == i2.

(** Note: [ordinal] is also a [finType] *)


(** ** [tuple] type *)

From mathcomp Require Import tuple.

Definition t : 3.-tuple nat :=
  [tuple 5; 6; 7].

(** It's not possible to take an out-of-bounds
    element of a tuple, so there is no need
    of a default element as for [nth] on [seq]s *)
About tnth.

Compute [tnth t 0].
Compute [tnth t 1].
Compute [tnth t 2].
Fail Compute [tnth t 3].

About thead.
(**
thead :
  forall (n : nat) (T : Type),
    (n.+1).-tuple T -> T
*)

Compute thead t.  (** = 5 *)
(** [thead] of empty tuple
    does not even typecheck *)
Fail Check thead [tuple].

(**
  Structure tuple_of (n : nat) (T : Type) : Type :=
    Tuple {
    (* [:>] means "is a coercion" *)
      tval :> seq T;
      _ : size tval == n;
    }.
*)

Section TupleExample.
Variables (m n : nat) (T : Type).
Variable t1 : m.-tuple T.
Variable t2 : n.-tuple T.

Check [tuple of t1 ++ t2] : (m + n).-tuple T.
Fail Check [tuple of t1 ++ t2] : (n + m).-tuple T.
End TupleExample.


Example seq_on_tuple (n : nat) (t : n .-tuple nat) :
  size (rev [seq 2 * x | x <- rev t]) = size t.
Proof.

Set Printing Coercions.
by rewrite map_rev revK size_map.
Unset Printing Coercions.

Restart.

rewrite size_tuple.  (** this should work *)
Check size_tuple.
(**
  size_tuple : forall (n : nat) (T : Type)
               (t : n.-tuple T), size t = n
*)

(** Why does this not fail? *)
(** rev [seq 2 * x | x <- rev t] is a list,
    not a tuple *)
rewrite size_tuple.
Abort.

Print Canonical Projections.
(**
  ...
  map <- tval ( map_tuple )
  ...
  rev <- tval ( rev_tuple )
  ...
*)

(**
This works because Coq is instrumented
to automatically promote sequences to tuples
using the mechanism of Canonical Structures.

Lemma rev_tupleP n A (t : n .-tuple A) :
  size (rev t) == n.
Proof. by rewrite size_rev size_tuple. Qed.

Canonical rev_tuple n A (t : n .-tuple A) :=
  Tuple (rev_tupleP t).

Lemma map_tupleP n A B (f:A -> B) (t: n.-tuple A) :
   size (map f t) == n.
Proof. by rewrite size_map size_tuple. Qed.

Canonical
  map_tuple n A B (f:A -> B) (t: n.-tuple A) :=
    Tuple (map_tupleP f t).
 *)

(** Exercise: show in detail how
    [rewrite size_tuple] from above works *)



(**
Since tuples are a subtype of lists, we
can reuse the theory of lists over equality types.
*)

Example test_eqtype (x y : 3.-tuple nat) :
  x == y -> True.
Proof.
move=> /eqP.
Abort.



(** * Finite types *)

From mathcomp Require Import choice fintype finfun.

(**
Fig. 3 of "Packaging Mathematical Structures"
by F. Garillot, G. Gonthier, A. Mahboubi,
L. Rideau(2009)
*)



(** A [finType] structure is composed of
    a list of elements of an [eqType] structure,
    each element of the type being uniquely
    represented in the list:

(* simplified definition of [finType] *)
  Structure finType : Type :=
    FinType {
        sort :> countType;
        enum : seq sort;
        enumP : forall x,
                  count (pred1 x) enum = 1;
    }.
*)

(**
Finite sets are then sets taken in a [finType]
domain. In the library, the basic operations
are provided.
For example, given [A] a finite set,
[card A] (or #|A|) represents the cardinality
of A. All these operations come with their
basic properties. For example, we have:

  Lemma cardUI : ∀ (d: finType) (A B: {pred T}),
    #|A ∪ B| + #|A ∩ B| = #|A| + #|B|.

  Lemma card_image :
    ∀ (T T': finType) (f : T -> T')
      injective f -> forall A : {pred T},
      #|image f A| = #|A|.
*)



(** ** How [finType] is actually organized *)

Print Finite.type.
(**
  Structure type : Type :=
    Pack {
      sort : Type;
      _ : Finite.class_of sort
    }.
*)

(** [finType] extends [choiceType] with a mixin *)
Print Finite.class_of.
(**
  Structure class_of (T : Type) : Type :=
    Class {
      base : Choice.class_of T;
      mixin : Finite.mixin_of (EqType T base)
    }
*)

Print Finite.mixin_of.
(** we mix in countable and two specific fields:
    an enumeration and an axiom

  Structure mixin_of (T : eqType) : Type :=
    Mixin {
      mixin_base : Countable.mixin_of T;
      mixin_enum : seq T;
      _ : Finite.axiom mixin_enum
    }.
*)

Print Finite.axiom.
(**
  Finite.axiom =
    fun (T : eqType) (e : seq T) =>
      forall x : T, count_mem x e = 1

where
  Notation count_mem x := (count (pred1 x)).
*)

Eval cbv in count_mem 5 [:: 1; 5; 2; 5; 3; 5; 4].


Section FinTypeExample.

Variable T : finType.

(** Cardinality of a finite type *)
Check #| T |.

(** "bounded" quantification *)
Check [forall x : T, x == x] && false.
Fail Check (forall x : T, x == x) && false.

(** We recover classical reasoning for
    the bounded quantifiers: *)
Check negb_forall:
  forall (T : finType) (P : pred T),
    ~~ [forall x, P x] = [exists x, ~~ P x].

Check negb_exists:
  forall (T : finType) (P : pred T),
    ~~ [exists x, P x] = [forall x, ~~ P x].

(** [negb_forall] does not hold
    in intuitionistic setting *)

End FinTypeExample.



(** * Examples of interfaces *)

From mathcomp Require Import finset.

Section Interfaces.

Variable chT : choiceType.

Check (@sigW chT).

Check [eqType of chT].

Variable coT : countType.

Check [countType of nat].
Check [choiceType of coT].
Check [choiceType of nat * nat].
Check [choiceType of seq coT].

Variable fT : finType.

Check [finType of bool].
Check [finType of 'I_10].
Check [finType of {ffun 'I_10 -> fT}].
Check [finType of bool * bool].
Check [finType of 3.-tuple bool].
Fail Check [finType of 3.-tuple nat].

Check {set 'I_4} : Type.
Check forall a : {set 'I_4},
        (a == set0) || (1 < #|a| < 4).
Print set_type.
Check {ffun 'I_4 -> bool} : Type.
Print finfun_eqType.
Check [eqType of #| 'I_4 |.-tuple bool].
Check [finType of #| 'I_4 |.-tuple bool].

Check {ffun 'I_4 * 'I_6 -> nat} : Type.
Check [eqType of {ffun 'I_4 * 'I_6 -> nat}] : Type.

End Interfaces.



(** * Bonus *)

(* The following requires
   the coq-mathcomp-algebra package
   from opam package manager *)
From mathcomp Require Import all_algebra.
Open Scope ring_scope.

Print matrix.

Section Rings.

Variable R : ringType.

Check forall x : R, x * 1 == x.

(** Matrices of size 4x4 over an arbitrary ring [R] *)
Check forall m : 'M[R]_(4,4), m == m * m.

End Rings.



