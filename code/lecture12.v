From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq path fintype.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



(** ** Extraction intermezzo *)

From Coq Require Import Extraction.

Print sum.
(**
Inductive sum (A B : Type) : Type :=
| inl : A -> sum A B
| inr : B -> sum A B
*)

Extraction sum.
(**
type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b
*)

Print sumbool.
Extraction sumbool.
(**
Inductive sumbool (A B : Prop) : Set :=
| left : A -> sumbool A B
| right : B -> sumbool A B

type sumbool =
| Left
| Right
 *)

Print or.
Extraction or.
(**
Inductive or (A B : Prop) : Prop :=
| or_introl : A -> A \/ B
| or_intror : B -> A \/ B


(* or : logical inductive *)
(* with constructors : or_introl or_intror *)
 *)



Print sigT.
Extraction sigT.
(**
Inductive sigT (A : Type) (P : A -> Type) : Type :=
    existT : forall x : A, P x -> {x : A & P x}

type ('a, 'p) sigT =
| ExistT of 'a * 'p
*)

Print sig.
Extraction sig.
(**
Inductive sig (A : Type) (P : A -> Prop) : Type :=
    exist : forall x : A, P x -> sig P

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)
*)

Print ex.
Extraction ex.
(**
Inductive ex (A : Type) (P : A -> Prop) : Prop :=
    ex_intro : forall x : A, P x -> exists y, P y

(* ex : logical inductive *)
(* with constructors : ex_intro *)
*)


Print Equality.type.
(**
Record type : Type :=
Pack { sort : Type;  _ : Equality.mixin_of sort }
*)
Extraction eqType.
(**
type coq_type = __ mixin_of
  (* singleton inductive, whose constructor was Pack *)
*)
Extraction Equality.mixin_of.
(**
type 't mixin_of = { op : 't rel; mixin_of__1 : 't axiom }
*)

Definition b : bool_finType := true.
Extraction b.


(** ** Braun trees, revisited *)

Section BinaryTree.

Variable T : Type.

Inductive btree : Type :=
| BTempty
| BTnode
    (l : btree)
    (a : T)
    (r : btree).

Implicit Type bt : btree.

(** A generic binary tree size algorithm *)
Fixpoint bt_size bt : nat :=
  if bt is (BTnode l _ r) then
    (bt_size l +
     bt_size r).+1
  else
    0.

Variable leT : rel T.
Implicit Types (a e : T).

Fixpoint br_insert e bt : btree :=
  if bt is (BTnode l a r) then
    if leT e a then
      BTnode
        (br_insert a r) e l
    else
      BTnode
        (br_insert e r) a l
  else
    BTnode
      BTempty
      e
      BTempty.

Fixpoint brt_diff brt s : nat :=
  match brt with
  | BTempty => 0
  | BTnode l _ r =>
    if s == 0 then 1
    else if odd s then brt_diff l (s %/ 2)
    else brt_diff r (s.-1 %/ 2)
  end.

Fixpoint brt_size brt : nat :=
  if brt is (BTnode l _ r) then
    let: sr := brt_size r in
    (2 * sr + brt_diff l sr).+1
  else 0.

End BinaryTree.

Arguments BTempty {T}.
Arguments BTnode {T} l a r.
Arguments bt_size {T}.
Arguments brt_size {T}.


Module AlternativeIsBraunTreePredicate.
Section BraunTree.

Variable T : Type.
Implicit Type brt : btree T.
(** Let's change this predicate to try and make
    proofs easier *)
Fixpoint is_brtree brt : bool :=
  if brt is (BTnode l _ r) then
    [&& is_brtree l,
        is_brtree r &
        [exists b : bool, bt_size l == b + bt_size r]]
  else
    true.

Arguments is_brtree : simpl never.

(** As for the size, with Braun trees
    we can do better! *)

(** Rewrite multi-rule *)
Lemma is_brtree_node l x r :
  is_brtree (BTnode l x r) ->
  (is_brtree l * is_brtree r * (bt_size r <= bt_size l))
  /\ (exists b : bool, bt_size l = b + bt_size r).
Proof.
rewrite /is_brtree -/is_brtree.
by case/and3P=> ->-> /existsP[d /eqP->]; rewrite leq_addl; split; eexists.
Qed.

Lemma bt_size1 (bt : btree T) :
  bt_size bt = 1 ->
  exists x,
    bt = BTnode BTempty x BTempty.
Proof.
by case: bt=> // [[|//]] a [|//]; exists a.
Qed.

Lemma half_double n :
  (n.*2.+1./2 = n) * (n.*2./2 = n) *
  (0 < n -> (n.*2).-1./2 = n.-1).
Proof.
rewrite doubleK -add1n /= uphalf_double; do ! split.
by case: n=> //= n _; rewrite uphalf_double.
Qed.

Lemma half_bit (b : bool) : b./2 = 0. Proof. by case: b. Qed.

Lemma dup {A} : A -> A * A. Proof. by []. Qed.

Lemma uphalf_bit_half l r (b : bool) :
  l = b + r ->
  (l = uphalf (l + r)) * (r = (l + r)./2).
Proof.
move=> ->; split; rewrite -addnA addnn ?half_bit_double //.
by rewrite uphalf_half odd_add odd_double oddb addbF half_bit_double.
Qed.

(** Based on Okasaki's informal argument *)
Lemma brtree_node_size l x r :
  is_brtree (BTnode l x r) ->
  let: m := bt_size (BTnode l x r) in
  (bt_size l = uphalf m.-1) * (bt_size r = half m.-1).
Proof.
rewrite /is_brtree -/is_brtree; case/and3P=> _ _ /existsP[d /eqP] /=.
by move/uphalf_bit_half.
Qed.

Lemma brt_diff_correct brt (s : nat) :
  is_brtree brt ->
  (exists b : bool, bt_size brt = b + s) ->
  brt_diff brt s = bt_size brt - s.
Proof.
elim: brt s=> //= l IHl a r IHr s.
move=> /dup[/brtree_node_size /= S /is_brtree_node [Br_lr _]] => /=.
case: s => [|s] /=; first by case=> [[]].
case=> d; rewrite addnS; case=> Ssum.
rewrite !divn2 Ssum -addnS addnK; rewrite Ssum in S.
rewrite uphalf_half halfD odd_add oddb half_bit add0n in S.
rewrite S in IHl IHr.
case: ifPn; last first.
- by rewrite negbK => odd_s; rewrite IHr ?Br_lr // S odd_s andbT ?addnK //; exists d.
move=> /negbTE even_s; rewrite /= uphalf_half even_s /= add0n.
by rewrite IHl ?Br_lr // even_s addbF andbF ?addnK //; exists d.
Qed.

(** The spec of [brt_size] is [bt_size] *)
Lemma brt_size_correct brt :
  is_brtree brt ->
  brt_size brt = bt_size brt.
Proof.
elim: brt => // l _ x r IHr.
move=> /is_brtree_node [node ?] /=.
rewrite IHr ?node //.
rewrite brt_diff_correct ?node //.
rewrite mulSn mul1n -addnA.
by rewrite subnKC ?node // addnC.
Qed.

End BraunTree.

Arguments is_brtree {T} brt.
Arguments is_brtree_node {T l x r}.



Section BraunTreeInsert.

Variable T : Type.
Variable leT : rel T.
Implicit Types (a e : T).

Lemma br_insert_size e bt :
  bt_size (br_insert leT e bt) =
  (bt_size bt).+1.
Proof.
Admitted.

Lemma br_insert_is_brtree e bt :
  is_brtree bt ->
  is_brtree (br_insert leT e bt).
Proof.
elim: bt e=> //.
(**
Why didn't Coq discharge the first trivial subgoal?

This is because fintype's [exists b, ...] is protected
from reduction.
 *)

Abort.

End BraunTreeInsert.
End AlternativeIsBraunTreePredicate.



Section BraunTree.

Variable T : Type.
Implicit Type brt : btree T.
Fixpoint is_brtree brt : bool :=
  if brt is (BTnode l _ r) then
    [&& is_brtree l,
        is_brtree r &
        bt_size r <= bt_size l <= (bt_size r).+1]
  else
    true.

End BraunTree.
Arguments is_brtree : simpl never.


Section BraunTreeRemove.

Variable T : Type.
(** [def] is a default element we have
    to have since the type system
    does not prevent us from considering
    the case of empty tree *)
Variable (def : T).
Implicit Types (bt : btree T).

Fixpoint br_remove_min bt : T * btree T :=
  match bt with
  | BTempty => (def, BTempty)
  | BTnode BTempty a r => (a, BTempty)
  | BTnode l a r =>
      let: (min, l) := br_remove_min l in
      (min, BTnode r a l)
  end.

Lemma br_remove_min_is_brtree bt :
  is_brtree bt ->
  is_brtree (br_remove_min bt).2.
Proof.
Admitted.

End BraunTreeRemove.




(** Let's try a perhaps quicker way of checking
    If it makes sense to prove the properties of
    and algorithm. Proving might require a
    non-trivial amount of work, so we better have
    a way to filter out non-theorems or useless theorems
 *)

(**
Property-based randomized testing to the rescue!

Key ideas:
- Write specifications as _computable_ predicates
- Generate lots of random inputes to test your functions
- "Shrink" counterexamples

One could say that property-based randomized testing sits
in the middle between hand-written unit tests and
fully formal proofs.
 *)

(** * The QuickChick plugin

https://github.com/QuickChick/QuickChick,
    opam install coq-quickchick

QuickChick is a port of QuickCheck written around
the year 2000 by John Hughes for Haskell

For more detail about QuickChick see also
"Foundational Property-Based Testing" by
Paraskevopoulou, Hritcu, Denes, Lampropoulos, Pierce

Also, "QuickChick: Property-Based Testing in Coq"
by Lampropoulos and Pierce provides a gentle
introduction into the topic:
https://softwarefoundations.cis.upenn.edu/qc-current/index.html
 *)

From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Import GenLow GenHigh.
Set Warnings "-extraction-opaque-accessed,-extraction".


(** The user writes their generators and shrinkers,
    but luckily for us for sufficiently simple datatypes
    QuickChick can do it automatically *)
Derive Arbitrary for btree.
(**
GenSizedbtree is defined
Shrinkbtree is defined
*)

Derive Show for btree.
(** ShowTree is defined *)

QuickChick (fun bt => is_brtree ((br_remove_min 42 bt).2)).
(**
QuickChecking (fun bt => is_brtree (br_remove_min 42 bt).2)
/Users/anton/.opam/coq8.9/bin/ocamldep.opt -modules QuickChickab879a.ml > QuickChickab879a.ml.depends
/Users/anton/.opam/coq8.9/bin/ocamlc.opt -c -o QuickChickab879a.cmo QuickChickab879a.ml
/Users/anton/.opam/coq8.9/bin/ocamlopt.opt -c -o QuickChickab879a.cmx QuickChickab879a.ml
/Users/anton/.opam/coq8.9/bin/ocamlopt.opt QuickChickab879a.cmx -o QuickChickab879a.native
BTnode (BTnode BTempty 0 BTempty)
       0
       (BTnode (BTnode BTempty 0 BTempty) 0 BTempty)
*** Failed after 19 tests and 12 shrinks. (0 discards)
*)

(** This does not look like a valid counterexample because
    the right subtree is bigger than the left one.
    Oh, wait, we forgot to constraint the inputs to
    the [br_remove_min] function. *)

Time QuickChick (fun bt => is_brtree bt ==>
                      is_brtree ((br_remove_min 42 bt).2)).
(**
QuickChecking (fun bt => is_brtree bt ==> is_brtree (br_remove_min 100 bt).2)
/Users/anton/.opam/coq8.9/bin/ocamldep.opt -modules QuickChick93e386.ml > QuickChick93e386.ml.depends
/Users/anton/.opam/coq8.9/bin/ocamlc.opt -c -o QuickChick93e386.cmo QuickChick93e386.ml
/Users/anton/.opam/coq8.9/bin/ocamlopt.opt -c -o QuickChick93e386.cmx QuickChick93e386.ml
/Users/anton/.opam/coq8.9/bin/ocamlopt.opt QuickChick93e386.cmx -o QuickChick93e386.native
+++ Passed 10000 tests (0 discards)
*)


(** Using QuickChick can be a nice way of figuring out
    the precodintions to the lemmas of interest,
    i.e. testing helps proving!

    Moreover, since our testing code
    (and most of QuickChick itself) is written in Coq,
    we can also formally verify this code using Coq.
    That is, proving helps testing!
 *)

(** So we gain confidence in the statement and
    can continue proving it -- it's a nice exercise,
    but it's pointless because it's easy to see that
    [br_remove_min] does not always return a minumum.
    (you have probably spotted that it does not rely on
     a less-or-equal relation like [br_insert] does).
    Let's demonstrate it using QuickChick.
 *)

QuickChick (fun bt =>
              is_brtree bt ==>
              let: (min1, bt1) := (br_remove_min 42 bt) in
              let: (min2, _)   := (br_remove_min 42 bt1) in
              min1 <= min2).
(**
QuickChecking (fun bt =>
 is_brtree bt ==>
 (let '(min1, bt1) := br_remove_min 42 bt in
  let '(min2, _) := br_remove_min 42 bt1 in min1 <= min2))
/Users/anton/.opam/coq8.9/bin/ocamldep.opt -modules QuickChick1e72ee.ml > QuickChick1e72ee.ml.depends
/Users/anton/.opam/coq8.9/bin/ocamlc.opt -c -o QuickChick1e72ee.cmo QuickChick1e72ee.ml
/Users/anton/.opam/coq8.9/bin/ocamlopt.opt -c -o QuickChick1e72ee.cmx QuickChick1e72ee.ml
/Users/anton/.opam/coq8.9/bin/ocamlopt.opt QuickChick1e72ee.cmx -o QuickChick1e72ee.native
BTnode (BTnode BTempty 1 BTempty) 0 BTempty
*** Failed after 32 tests and 3 shrinks. (0 discards)
*)



(** * Some non-examples *)

(** Let's try to create a test generator for out subtype *)
Module Sub.
Section BraunTreeSubType.

Variable T : Type.

Inductive brtree :=
  BrTree (bt : btree T) of is_brtree bt.

Coercion tree_of_brtree (brt : brtree) :=
  let: @BrTree bt _ := brt in bt.

Canonical brtree_subType :=
  [subType for tree_of_brtree].

End BraunTreeSubType.
End Sub.


Fail Derive Arbitrary for Sub.brtree.
(* Error: nth failed: 1 *)




Fail QuickChick (fun bt =>
  AlternativeIsBraunTreePredicate.is_brtree bt ==>
  AlternativeIsBraunTreePredicate.is_brtree
    ((br_remove_min 42 bt).2)).
(** Error: Could not compile test program *)
(** QuickChick uses extraction to OCaml
    and then the OCaml compiler to compile and run the tests *)


QuickChick (fun bt =>
  is_brtree bt ==>
  is_brtree (br_insert ssrnat.leq 4 bt)).
(**
QuickChecking (fun bt => is_brtree bt ==> is_brtree (br_insert ssrnat.leq 4 bt))
/Users/anton/.opam/coq8.9/bin/ocamldep.opt -modules QuickChick4d55ef.ml > QuickChick4d55ef.ml.depends
/Users/anton/.opam/coq8.9/bin/ocamlc.opt -c -o QuickChick4d55ef.cmo QuickChick4d55ef.ml
/Users/anton/.opam/coq8.9/bin/ocamlopt.opt -c -o QuickChick4d55ef.cmx QuickChick4d55ef.ml
/Users/anton/.opam/coq8.9/bin/ocamlopt.opt QuickChick4d55ef.cmx -o QuickChick4d55ef.native
+++ Passed 10000 tests (0 discards)
*)


Section BraunTreeRemoveLeftMost.

Variable T : Type.
(** [def] is a default element we have
    to have since the type system
    does not prevent us from considering
    the case of empty tree *)
Variable (def : T).
Implicit Types (bt : btree T).
Variable leT : rel T.
Implicit Types (a e : T).

Definition le_root e bt :=
  if bt is BTnode _ x _ then leT e x
  else true.

Fixpoint is_heap bt : bool :=
  if bt is BTnode l x r then
    [&& le_root x l, le_root x r, is_heap l & is_heap r]
  else true.

Fixpoint br_remove_leftmost bt : T * btree T :=
  match bt with
  | BTempty => (def, BTempty)
  | BTnode BTempty a r => (a, BTempty)
  | BTnode l a r =>
      let: (min, l) := br_remove_leftmost l in
      (min, BTnode r a l)
  end.

End BraunTreeRemoveLeftMost.



QuickChick (fun bt def =>
  collect (is_brtree bt)
  [ ==>
     is_brtree bt =>
     is_brtree (br_remove_leftmost def bt).2]).

QuickChick (fun bt def =>
  [ ==>
     is_heap ssrnat.leq bt =>
     is_heap ssrnat.leq (br_remove_leftmost def bt).2]).

(** notice [brt_size] here -- we have proved it correct,
    so can use it in specs *)
(** Runs for a really long time *)
Time QuickChick (fun bt def =>
  [ ==>
     is_brtree bt =>
     brt_size (br_remove_leftmost def bt).2 ==
     (brt_size bt).-1]).

Time QuickChick (fun bt def =>
  [ ==>
     is_brtree bt,
     0 < brt_size bt =>
     (br_remove_leftmost def bt).1 == 0]).



(**
We have lots of tests, but surely many of those succeed
because of a failed precondition.
QuickChick supports user-defined random generators that
can produce inputs with the required properties.
Even more, the user can formally verify that the supplied
random generator is sound and complete
*)


(** So writing specs is a subtle business.
    And property-based randomized testing can help us
    with that.
    Are there any other tools / methodologies to help?
 *)


(** * Mutation Proving *)

(**
mCoq: Mutation Proving for Analysis of Verification Projects
by K. Palmskog et al.(2019)


This is related to Mutation Testing:
- make small changes resembling faults to software system
- execute accompanying test suite on changed system
- measure how well the test suite catches introduced faults
- improve test suite and repeat


Mutation Proving:
- a mutation operator [op] is applied to a Coq project
- [op] may generate a mutant where specifications are different
- an [op] mutant where a proof fails during checking is killed
- a [op] mutant where all proofs are successfully checked is live

Examples of operations
- Reorder branches of if-expressions
- Replace plus with minus
- Replase a list with its tail


A practical observation:
a high amount of live mutants might indicate weak specs


But sometimes it's just hard to come up
with a precise spec, e.g. this is often the case
when talking about time/space complexity:

The key but unstated invariant of [ss] is that
its [i]th item has size [2i] if it is not empty,
so that merge sort push only performs perfectly
balanced merges... without the [[::]] placeholder
the MathComp sort becomes two element-wise insertion sort.
—Georges Gonthier

A bit of context:

Section SortSeq.

Variables (T : Type) (leT : rel T).

Fixpoint merge_sort_push s1 ss :=
  match ss with
  | [::] :: ss' | [::] as ss' => s1 :: ss'
  | s2 :: ss' => [::] :: merge_sort_push (merge s2 s1) ss'
                 ^^^^
   this can be deleted, but proofs will still go through
  end.

Fixpoint merge_sort_pop s1 ss :=
  if ss is s2 :: ss' then merge_sort_pop (merge s2 s1) ss'
  else s1.

Fixpoint merge_sort_rec ss s :=
  if s is [:: x1, x2 & s'] then
    let s1 := if leT x1 x2 then [:: x1; x2]
              else [:: x2; x1] in
    merge_sort_rec (merge_sort_push s1 ss) s'
  else merge_sort_pop s ss.

Definition sort := merge_sort_rec [::].

*)

