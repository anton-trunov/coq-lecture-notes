From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** * Sorting algorithms *)

(** ** Insertion sort *)

Module Insertion.
Section InsertionSort.

Variable T : eqType.
Variable leT : rel T.
Implicit Types x y z : T.
Implicit Types s t u : seq T.

(** Insert an element [e] into a sorted list [s] *)
Fixpoint insert e s : seq T :=
  if s is x :: s' then
    if leT e x then e :: s
    else x :: (insert e s')
  else [:: e].

(** Sort input list [s] *)
Fixpoint sort s : seq T :=
  if s is x :: s' then
    insert x (sort s')
  else [::].


(** Now we'd like to prove [sort] correct.
    But what does mean for a sorting algorithm
    to be correct?

It could have been a requirement that the output
of the algorithm is _sorted_.
Let's give this notation a precise meaning.
We call the corresponding predicate [sorted']
because we will later refine the definition into
something more general that helps us a lot with
inductive proofs.
*)

(** This fails because [x2 :: s'] is not a
    structural subterm of [s] *)
Fail Fixpoint sorted' s : bool :=
  if s is x1 :: x2 :: s' then
    leT x1 x2 && (sorted' (x2 :: s'))
  else true.

Fixpoint sorted' s : bool :=
  if s is x1 :: ((x2 :: s') as tail) then
    leT x1 x2 && (sorted' tail)
  else true.

(** The obvious definition we came up with is not
    very easy to work with.
    We would see it later when trying to prove
    that [insert] function preserves sortedness. *)


(** So instead we are going to use Mathcomp's
    [sorted] predicate, which is based on the notion
    of [path]. *)
Print sorted.
(**
sorted =
fun (T : eqType) (leT : rel T) (s : seq T) =>
if s is x :: s' then path leT x s'
else true
: forall T : Type, rel T -> seq T -> bool
*)

Print path.
(**
path =
fun (T : Type) (e : rel T) =>
fix path (x : T) (p : seq T) {struct p} : bool :=
  if p is (y :: p') then e x y && path y p'
  else true
: forall T : Type, rel T -> T -> seq T -> bool
*)

(** With the modified definition the helper lemma
    is much easier to prove (exercise): *)
Lemma sorted_cons e s :
  sorted leT (e :: s) -> sorted leT s.
Admitted.





(**
It's easy to see that requiring just sortedness
of the output list is a rather weak specification --
a function always returning an empty list would
also be correct

Hence, our next observation --
the function should NOT forget about elements of
the input list:

  forall x : T, x \in s -> x \in (sort s)

A little thinking reveals this is a pretty weak spec:
a function may (in principle) add extra elements
to the output, so we need to disallow that:

  forall x : T, x \in s = x \in (sort s)

Remark:
  Since our implementations are going to be
  parametric (generic), the only way the extra
  elements may occur in the output list is by
  repeating some elements of the input list,
  so the above tweak of the spec does not
  actually buy us anything.

The current version of the spec is still not strong
enough: it does not take into account possible
duplicates in the input list, e.g. the following is
true, while this is not what we meant -- let's assume
s = [:: 0; 0; 0] and that (sort s) = [:: 0; 0],
then the spec above still holds:
  forall x, x \in [:: 0; 0; 0] = x \in [:: 0; 0]

What we actually care about is to keep the elements
together with their repective number of occurences.

  forall x : T,
    count (pred1 x) s = count (pred1 x) (sort s)

Question: what goes wrong if we add a precondition
that all the elements we count must come from the
input list?

  forall x : T,
    x \in s ->
    count (pred1 x) s = count (pred1 x) (sort s)


You may have recognized the proposition
  forall x : T,
    count (pred1 x) s = count (pred1 x) (sort s)

as expressing the notion of _permutation_.
 *)


(**
There is one more concern w.r.t. the spec we came up
with so far -- it's non-computable as it requires us
to compute [count]-expressions over a possibly
infinite type [T].
Intuitively we know that for any two lists we can
compute if one is a permutation of the other if we
have equality over the type of elements.

Mathcomp introduces a computable of notion of
equivalence up to permutation: [perm_eq] defined
as follows:
*)

Print perm_eq.
(**
perm_eq =
fun (T : eqType) (s1 s2 : seq T) =>
  all
    [pred x | (count_mem x) s1 == (count_mem x) s2]
    (s1 ++ s2)

is equivalent to

  all
    [pred x | (count_mem x) s1 == (count_mem x) s2]
    s1
  &&
  all
    [pred x | (count_mem x) s1 == (count_mem x) s2]
    s2

: forall T : eqType, seq T -> seq T -> bool

where
Notation count_mem x := (count (pred1 x))
*)


(**
Moreover, any two lists [s1] and [s2] that are
a permutation of each other, give us the following
property which is universal for _any_ predicate [p]:
  forall p : pred T,
    count p s1 = count p s2,
expressed as a [reflect]-predicate:
*)
About permP.
(**
permP :
   forall (T : eqType) (s1 s2 : seq T),
   reflect (count^~ s1 =1 count^~ s2)
           (perm_eq s1 s2)
*)


(**
Alternatively, the notion of permutation may be
expressed as a binary _inductive_ predicate:
 *)
Section InductivePermutations.
Variable A : Type.

Inductive perm : seq A -> seq A -> Prop :=
| permutation_nil : perm [::] [::]
| permutation_skip a v1 v2 of
    perm v1 v2 : perm (a :: v1) (a :: v2)
| permutation_swap a b v1 v2 of
    perm v1 v2 : perm [:: a, b & v1] [:: b, a & v2]
| permutation_trans v1 v2 v3 of
    perm v1 v2 & perm v2 v3 : perm v1 v3.


Inductive le : nat -> nat -> Prop :=
| leO n : le 0 n
| leS m n : le m n -> le m.+1 n.+1.

Definition le_3_4 : le 3 4 :=
  leS (leS (leS (leO _))).

Inductive le' : nat -> nat -> Prop :=
| le_refl n : le' n n
| leSr m n : le' m n -> le' m n.+1.

Definition le_3_4' : le' 3 4 :=
  leSr (le_refl _).

(**
The pros of this definition:
- it can be used to work in a more general setting
  where we don't have decidable equality;
- we can do induction on the proofs of two lists
  being a permutation of each other.

The cons is, of course, it does not compute.
 *)

Lemma pperm_sym v1 v2 :
  perm v1 v2 <-> perm v2 v1.
Proof.
suff {v1 v2} L : forall v1 v2,
  perm v1 v2 -> perm v2 v1 by split; apply: L.
move=> v1 v2; elim=> [*|*|*|].
- exact: permutation_nil.
- exact: permutation_skip.
- exact: permutation_swap.
move=> ??? _ P21 _ P32.
by apply: permutation_trans P32 P21.
(* Restart. *)
(* suff {v1 v2} L : forall v1 v2, *)
(*   perm v1 v2 -> perm v2 v1 by split; apply: L. *)
(* elim. *)
(* Undo 3. *)
Qed.

(** Exercise: try proving [pperm_sym]
    by induction a list.
 *)
End InductivePermutations.


(** * Upshot:
Our final notion of correctness of sorting algorithms
can be expressed semi-formally as follows
  sorted (sort s)  /\  perm_eq s (sort s)
*)




(** Let's try proving these properties for the
    insertion sort algorithm we implemented *)

(** * The output is sorted *)


(* Local Notation sorted := (sorted leT). *)

Lemma sort_sorted s :
  sorted leT (sort s).
Proof.
elim: s=> [//| x s IHs /=].
(** We need the fact that [insert] preserves
    sortedness. Let's prove it as a standalone lemma
 *)
Abort.

Lemma insert_sorted e s :
  sorted leT s ->
  sorted leT (insert e s).
Proof.
elim: s=> [//| x1 s IHs].
move=> /=.
move=> path_x1_s.
case: ifP=> [e_le_x1 | e_gt_x1].
- by rewrite /= e_le_x1 path_x1_s.
(** Notice that we lack one essential fact about
    [leT] -- totality *)
Abort.

Hypothesis leT_total : total leT.
Print total.
(**
total =
fun (T : Type) (R : rel T) =>
  forall x y : T, R x y || R y x
*)

Lemma insert_sorted e s :
  sorted leT s ->
  sorted leT (insert e s).
Proof.
elim: s=> [//| x1 s IHs].
move=> /= path_x1_s.
case: ifP=> [e_le_x1 | e_gt_x1].
- by rewrite /= e_le_x1 path_x1_s.
have:= leT_total e x1.
rewrite {}e_gt_x1.
move=> /= x1_le_e.
move: path_x1_s=> {}/path_sorted/IHs.
case: s=> [|x2 s]; first by rewrite /= x1_le_e.
move=> /=.
case: ifP.
- move=> /=.
  move=>-> /= ->.
  by rewrite x1_le_e.
  (** We are moving in circles here, let' steps back
      and generalize the problem. *)
Abort.

Lemma insert_path z e s :
  leT z e ->
  path leT z s ->
  path leT z (insert e s).
Proof.
move: z.
elim: s=> [/=| x1 s IHs] z.
- by move=>->.
move=> z_le_e.
move=> /=.
case/andP=> z_le_x1 path_x1_s.
case: ifP.
- by rewrite /= z_le_e path_x1_s => ->.
move=> /= e_gt_x1.
rewrite z_le_x1.
have:= leT_total e x1.
rewrite {}e_gt_x1 /= => x1_le_e.
exact: IHs.
Qed.


Lemma insert_sorted e s :
  sorted leT s ->
  sorted leT (insert e s).
Proof.
rewrite /sorted.
case: s=> // x s.
move=> /=.
case: ifP; first by move=> /= ->->.
move=> e_gt_x.
apply: insert_path.
have:= leT_total e x.
by rewrite e_gt_x /= => ->.
Qed.


(** exercise *)
Lemma sort_sorted s :
  sorted leT (sort s).
Proof.
Admitted.

End InsertionSort.

Arguments sort {T} _ _.
Arguments insert {T} _ _ _.




Section SortIsPermutation.

Variable T : eqType.
Variables leT : rel T.

(** a helper lemma (exercise) *)
Lemma count_insert p e s :
  count p (insert leT e s) = p e + count p s.
Admitted.

About perm_eql.
(**
Notation perm_eql s1 s2 :=
  (perm_eq s1 =1 perm_eq s2).
 *)

Print perm_eq.
(**
perm_eq =
fun (T : eqType) (s1 s2 : seq T) =>
all [pred x | count_mem x s1 == count_mem x s2]
    (s1 ++ s2)
     : forall T : eqType, seq T -> seq T -> bool
*)


Lemma perm_sort s : perm_eql (sort leT s) s.
Proof.
  (* Search _ perm_eq. *)
  Search _ (perm_eq ?s1 =1 perm_eq ?s2).
apply/permPl/permP.
elim: s=> //= x s IHs.
move=> p.
by rewrite count_insert IHs.
Qed.

(** This is why we state [perm_sort] lemma
    using [perm_eql] -- it can be used as
    an equation like so
 *)
Lemma mem_sort s : sort leT s =i s.
Proof. by apply: perm_mem; rewrite perm_sort. Qed.

Lemma sort_uniq s : uniq (sort leT s) = uniq s.
Proof. by apply: perm_uniq; rewrite perm_sort. Qed.

End SortIsPermutation.



Section SortProperties.

Variable T : eqType.
Variables leT : rel T.

Lemma sorted_sort s :
  sorted leT s -> sort leT s = s.
Proof.
elim: s=> // x1 s IHs S.
move: (S)=> {}/sorted_cons/IHs /= ->.
move: S=> /=.
case: s=> //= x2 s.
by case/andP=> ->.
Qed.

(** Insertion sort is stable (exercise) *)
Section Stability.

Variable leT' : rel T.
Implicit Types s : seq T.

(** Hint: you are free to assume e.g.
          [transitivity] of [leT] / [leT'] should
          you need that. E.g.
Hypothesis leT_tr : transitive leT.
 *)

Lemma sort_stable s :
  sorted leT' s ->
  sorted
    [rel x y | leT x y && (leT y x ==> leT' x y)]
    (sort leT s).
Proof.
Admitted.
End Stability.

End SortProperties.

End Insertion.



