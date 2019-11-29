From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq path.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** ** Braun trees *)

(** Three Algorithms on Braun Trees - C.
Okasaki(1997):

For any given node of a Braun tree, the
left subtree is either exactly the same
size as the right subtree, or one element
larger.

Braun trees always have minimum height,
and the shape of each Braun tree is
completely determined by its size.

In return for this rigor, algorithms that
manipulate Braun trees are often
exceptionally simple and elegant, and need
not maintain any explicit balance
information.
 *)

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

End BinaryTree.

Arguments BTempty {T}.
Arguments BTnode {T} l a r.
Arguments bt_size {T}.

Section BraunTree.

Variable T : Type.
Implicit Type brt : btree T.
Fixpoint is_brtree brt : bool :=
  if brt is (BTnode l _ r) then
    [&& is_brtree l,
        is_brtree r &
        (bt_size l == bt_size r)
        ||
        (bt_size l == (bt_size r).+1)]
  else
    true.

Arguments is_brtree : simpl never.

(** As for the size, with Braun trees
    we can do better! *)

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

(** Rewrite multi-rule *)
(** Exercise *)
Lemma is_brtree_node l x r :
  is_brtree (BTnode l x r) ->
  (is_brtree l * is_brtree r) *
  (bt_size r <= bt_size l) *
  ((bt_size l == bt_size r) ||
   (bt_size l == (bt_size r).+1)).
Proof.
Admitted.

(** Exercise *)
Lemma bt_size1 (bt : btree T) :
  bt_size bt = 1 ->
  exists x,
    bt = BTnode BTempty x BTempty.
Proof.
Admitted.

(** Exercise *)
Lemma brt_diff_correct brt s :
  is_brtree brt ->
  (bt_size brt == s) ||
  (bt_size brt == s.+1) ->
  brt_diff brt s = bt_size brt - s.
Proof.
Admitted.


(** The spec of [brt_size] is [bt_size] *)
Lemma brt_size_correct brt :
  is_brtree brt ->
  brt_size brt = bt_size brt.
Proof.
elim: brt => // l _ x r IHr.
move=> /is_brtree_node node /=.
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
Implicit Types (a e : T) (bt : btree T).

Fixpoint br_insert e bt : btree T :=
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

Lemma br_insert_size e bt :
  bt_size (br_insert e bt) =
  (bt_size bt).+1.
Proof.
Admitted.

Lemma dup {A} : A -> A * A.
Proof. by []. Qed.

Lemma br_insert_is_brtree e bt :
  is_brtree bt ->
  is_brtree (br_insert e bt).
Proof.
elim: bt e => // l IHl a r IHr e.
move=> /is_brtree_node Br.
move=> /=.
case: ifP=> [le | gt] /=.
- rewrite br_insert_size.
  rewrite IHr ?Br //.
  case: Br => _; case/orP=> /eqP->.
  - by rewrite eq_refl orbT.
  by rewrite eq_refl.
(** Exercise: remove proof duplication *)
rewrite br_insert_size.
rewrite IHr ?Br //.
case: Br => _; case/orP=> /eqP->.
- by rewrite eq_refl orbT.
by rewrite eq_refl.
Qed.

End BraunTreeInsert.


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


(** Packing it all together *)
Module Sub.
Section BraunTreeSubType.

Variable T : Type.

Inductive brtree :=
  BrTree (bt : btree T) of is_brtree bt.

Coercion tree_of_brtree (brt : brtree) :=
  let: BrTree bt _ := brt in bt.

Canonical brtree_subType :=
  [subType for tree_of_brtree].

End BraunTreeSubType.
End Sub.



(** Another take on Braun trees *)

(** Extrinsic vs intrinsic verification *)

From Coq Require Import Extraction Program.

Module BraunTreeIntrinsic.
Section BraunTreeIntrinsic.

Variable T : Type.

Inductive brtree : nat -> Type :=
| BrTempty : brtree 0
| BrTnode
    m (l : brtree m)
    (a : T)
    n (r : brtree n)
    of (m = n \/ m = n.+1)
  : brtree (m+n).+1.

Definition brt_size' {n} (brt : brtree n) :=
  n.

(** What's the problem with this definition? *)

End BraunTreeIntrinsic.

Arguments BrTempty {T}.

(** Let's talk about running verified
    algorithms. *)

Extraction brt_size'.

(**
val brt_size' : nat -> 'a1 brtree -> nat

let brt_size' n _ =
  n

But we do not want to keep the size
of the tree at run-time.
*)


Section BraunTree.
Variable T : Type.

Fixpoint brt_slow_size1
           {n} (brt : brtree T n)
  : nat :=
  if brt is (BrTnode _ l _ _ r _) then
    (brt_slow_size1 l +
     brt_slow_size1 r).+1
  else
    0.

Fixpoint brt_slow_size2
           {n} (brt : brtree T n)
  : {s | s = n}.
case: brt.
- by exists 0.
move=> m' l x n' r pf.
exists (sval (brt_slow_size2 _ l) +
        sval (brt_slow_size2 _ r)).+1.
case: (brt_slow_size2 _ _).
case: (brt_slow_size2 _ _).
move=>/=.
by move=> ? -> ? ->.
Defined.

Print brt_slow_size2.


Fail Program Fixpoint brt_slow_size3
           {n} (brt : brtree T n)
  : {s | s = n} :=
  if brt is (BrTnode _ l _ _ r _) then
      ((brt_slow_size3 l) +
       (brt_slow_size3 r)).+1
  else
    0.

Variable leT : rel T.

Fail Fixpoint br_insert {n} (e : T)
         (brt : brtree T n)
  : brtree T n.+1 :=
  if brt is (BrTnode _ l a _ r _) then
    if leT e a then
      BrTnode
        (br_insert a r) e l
    else
      BrTnode
        (br_insert e r) a l
  else
    BrTnode
      BrTempty
      e
      BrTempty
      (or_introl erefl).

(** But we can know express more
    in types, compare this to
    bt_remove_min *)
Fixpoint brt_remove_min {n}
         (bt : brtree T n.+1) :
  T * brtree T n.
Admitted.

End BraunTree.
