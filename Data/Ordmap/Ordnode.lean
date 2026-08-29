/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Order.Compare
public import Mathlib.Data.Nat.PSub
public import Batteries.Data.List.Lemmas
public import Mathlib.Data.Tree.Basic

/-!
# Ordered sets

This file defines a data structure for ordered sets, supporting a
variety of useful operations including insertion and deletion,
logarithmic time lookup, set operations, folds,
and conversion from lists.

The `Ordnode α` operations all assume that `α` has the structure of
a total preorder, meaning a `≤` operation that is

* Transitive: `x ≤ y → y ≤ z → x ≤ z`
* Reflexive: `x ≤ x`
* Total: `x ≤ y ∨ y ≤ x`

For example, in order to use this data structure as a map type, one
can store pairs `(k, v)` where `(k, v) ≤ (k', v')` is defined to mean
`k ≤ k'` (assuming that the key values are linearly ordered).

Two values `x,y` are equivalent if `x ≤ y` and `y ≤ x`. An `Ordnode α`
maintains the invariant that it never stores two equivalent nodes;
the insertion operation comes with two variants depending on whether
you want to keep the old value or the new value in case you insert a value
that is equivalent to one in the set.

The operations in this file are not verified, in the sense that they provide
"raw operations" that work for programming purposes but the invariants
are not explicitly in the structure. See `Ordset` for a verified version
of this data structure.

## Main definitions

* `Ordnode α`: A set of values of type `α`

## Implementation notes

Based on weight balanced trees:

* Stephen Adams, "Efficient sets: a balancing act",
  Journal of Functional Programming 3(4):553-562, October 1993,
  <http://www.swiss.ai.mit.edu/~adams/BB/>.
* J. Nievergelt and E.M. Reingold,
  "Binary search trees of bounded balance",
  SIAM journal of computing 2(1), March 1973.

Ported from Haskell's `Data.Set`.

## Tags

ordered map, ordered set, data structure

-/

@[expose] public section

universe u

/--
Inductive type `Ordnode` / 归纳类型 `Ordnode`

English:
inductive Ordnode
  parameters: (α : Type u)
  constructors (2):
    - nil: Ordnode α
    - node: (size : Nat) (l : Ordnode α) (x : α) (r : Ordnode α) : Ordnode α

中文:
归纳类型 Ordnode
  参数: (α : 类型u)
  构造子 (2 个):
    - nil: Ordnode α
    - node: (size : 自然数) (l : Ordnode α) (x : α) (r : Ordnode α) : Ordnode α

Depends on / 依赖: ExpChar
-/
inductive Ordnode (α : Type u) : Type u
  | nil : Ordnode α
  | node (size : Nat) (l : Ordnode α) (x : α) (r : Ordnode α) : Ordnode α
compile_inductive% Ordnode

namespace Ordnode

variable {α : Type*}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EmptyCollection (Ordnode α)
  body: ⟨nil⟩

中文:
实例 :
  签名: EmptyCollection (Ordnode α)
  定义体: ⟨nil⟩
-/
instance : EmptyCollection (Ordnode α) :=
  ⟨nil⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Ordnode α)
  body: ⟨nil⟩

中文:
实例 :
  签名: 可居 (Ordnode α)
  定义体: ⟨nil⟩
-/
instance : Inhabited (Ordnode α) :=
  ⟨nil⟩

/-- **Internal use only**

The maximal relative difference between the sizes of
two trees, it corresponds with the `w` in Adams' paper.

According to the Haskell comment, only `(delta, ratio)` settings
of `(3, 2)` and `(4, 2)` will work, and the proofs in
`Ordset.lean` assume `delta := 3` and `ratio := 2`. -/
@[inline]
/--
Definition of `delta` / `delta` 的定义

English:
definition delta
  body: 3

中文:
定义 delta
  定义体: 3
-/
def delta :=
  3

/-- **Internal use only**

The ratio between an outer and inner sibling of the
heavier subtree in an unbalanced setting. It determines
whether a double or single rotation should be performed
to restore balance. It is corresponds with the inverse
of `α` in Adam's article. -/
@[inline]
/--
Definition of `ratio` / `ratio` 的定义

English:
definition ratio
  body: 2

中文:
定义 ratio
  定义体: 2
-/
def ratio :=
  2

/-- O(1). Construct a singleton set containing value `a`.

```
singleton 3 = {3}
``` -/
@[inline]
/--
Definition of `singleton` / `singleton` 的定义

English:
definition singleton
  signature: (a : α)
  body: node 1 nil a nil

local prefix:arg "ι" => Ordnode.singleton

中文:
定义 singleton
  签名: (a : α)
  定义体: node 1 nil a nil

local prefix:arg "ι" => Ordnode.singleton
-/
protected def singleton (a : α) : Ordnode α :=
  node 1 nil a nil

local prefix:arg "ι" => Ordnode.singleton

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Singleton α (Ordnode α)
  body: ⟨Ordnode.singleton⟩

中文:
实例 :
  签名: 单例 α (Ordnode α)
  定义体: ⟨Ordnode.singleton⟩

Depends on / 依赖: Ordnode, Ordnode.singleton, singleton
-/
instance : Singleton α (Ordnode α) :=
  ⟨Ordnode.singleton⟩

/-- O(1). Get the size of the set.

```
size {2, 1, 1, 4} = 3
``` -/
@[inline]
/--
Definition of `size` / `size` 的定义

English:
definition size
  signature: : Ordnode α -> Nat

中文:
定义 size
  签名: : Ordnode α -> 自然数
-/
def size : Ordnode α -> Nat
  | nil => 0
  | node sz _ _ _ => sz

/--
theorem `size_nil` / 定理 `size_nil`

English:
theorem size_nil
  statement: size (nil : Ordnode α) = 0
  proof: rfl

中文:
定理 size_nil
  结论: size (nil : Ordnode α) = 0
  证明: rfl
-/
@[simp] theorem size_nil : size (nil : Ordnode α) = 0 :=
  rfl
/--
theorem `size_node` / 定理 `size_node`

English:
theorem size_node
  given: (sz : Nat) (l : Ordnode α) (x : α) (r : Ordnode α)
  proof: rfl

中文:
定理 size_node
  条件: (sz : 自然数) (l : Ordnode α) (x : α) (r : Ordnode α)
  证明: rfl
-/
@[simp] theorem size_node (sz : Nat) (l : Ordnode α) (x : α) (r : Ordnode α) :
    size (node sz l x r) = sz :=
  rfl

/-- O(1). Is the set empty?

```
empty ∅ = tt
empty {1, 2, 3} = ff
```
-/
@[inline]
/--
Definition of `empty` / `empty` 的定义

English:
definition empty
  signature: : Ordnode α -> Bool

中文:
定义 empty
  签名: : Ordnode α -> 布尔值
-/
def empty : Ordnode α -> Bool
  | nil => true
  | node _ _ _ _ => false

/-- **Internal use only**, because it violates the BST property on the original order.

O(n). The dual of a tree is a tree with its left and right sides reversed throughout.
The dual of a valid BST is valid under the dual order. This is convenient for exploiting
symmetries in the algorithms. -/
@[simp]
/--
Definition of `dual` / `dual` 的定义

English:
definition dual
  signature: : Ordnode α -> Ordnode α

中文:
定义 dual
  签名: : Ordnode α -> Ordnode α
-/
def dual : Ordnode α -> Ordnode α
  | nil => nil
  | node s l x r => node s (dual r) x (dual l)

/-- **Internal use only**

O(1). Construct a node with the correct size information, without rebalancing. -/
@[inline, reducible]
/--
Definition of `node'` / `node'` 的定义

English:
definition node'
  signature: (l : Ordnode α) (x : α) (r : Ordnode α)
  body: node (size l + size r + 1) l x r

中文:
定义 node'
  签名: (l : Ordnode α) (x : α) (r : Ordnode α)
  定义体: node (size l + size r + 1) l x r
-/
def node' (l : Ordnode α) (x : α) (r : Ordnode α) : Ordnode α :=
  node (size l + size r + 1) l x r

/-- Convert to an `OrdNode` by pre-computing the sizes. -/
@[simp]
/--
Definition of `_root_.BinaryTree.toOrdNode` / `_root_.BinaryTree.toOrdNode` 的定义

English:
definition _root_.BinaryTree.toOrdNode
  signature: : BinaryTree α -> Ordnode α

中文:
定义 _root_.BinaryTree.toOrdNode
  签名: : BinaryTree α -> Ordnode α
-/
def _root_.BinaryTree.toOrdNode : BinaryTree α -> Ordnode α
  | .nil => .nil
  | .node x l r => .node' l.toOrdNode x r.toOrdNode

@[simp]
/--
theorem `size_toOrdNode` / 定理 `size_toOrdNode`

English:
theorem size_toOrdNode
  given: (b : BinaryTree α)
  proof: by
  induction b with simp [BinaryTree.toOrdNode, *]

中文:
定理 size_toOrdNode
  条件: (b : BinaryTree α)
  证明: by
  induction b with simp [BinaryTree.toOrdNode, *]

Depends on / 依赖: BinaryTree, BinaryTree.toOrdNode, toOrdNode
-/
theorem size_toOrdNode (b : BinaryTree α) :
    b.toOrdNode.size = b.numNodes := by
  induction b with simp [BinaryTree.toOrdNode, *]

/-- Convert to an `BinaryTree`, discarding the cached size information. -/
@[simp]
/--
Definition of `toBinaryTree` / `toBinaryTree` 的定义

English:
definition toBinaryTree
  signature: : Ordnode α -> BinaryTree α

中文:
定义 toBinaryTree
  签名: : Ordnode α -> BinaryTree α
-/
def toBinaryTree : Ordnode α -> BinaryTree α
  | .nil => .nil
  | .node _ l x r => .node x l.toBinaryTree r.toBinaryTree

@[simp]
/--
theorem `toBinaryTree_toOrdNode` / 定理 `toBinaryTree_toOrdNode`

English:
theorem toBinaryTree_toOrdNode
  given: (b : BinaryTree α)
  proof: by
  induction b with simp [BinaryTree.toOrdNode, toBinaryTree, * ]

中文:
定理 toBinaryTree_toOrdNode
  条件: (b : BinaryTree α)
  证明: by
  induction b with simp [BinaryTree.toOrdNode, toBinaryTree, * ]

Depends on / 依赖: BinaryTree, BinaryTree.toOrdNode, toBinaryTree, toOrdNode
-/
theorem toBinaryTree_toOrdNode (b : BinaryTree α) :
    toBinaryTree b.toOrdNode = b := by
  induction b with simp [BinaryTree.toOrdNode, toBinaryTree, * ]

/--
Definition of `repr` / `repr` 的定义

English:
definition repr
  signature: {α} [Repr α] (o : Ordnode α) (n : Nat)
  body: match o with
  | nil => (Std.Format.text "∅")
  | node _ l x r =>
      let fmt := Std.Format.joinSep
        [repr l n, Repr.reprPrec x n, repr r n]
        " "
      Std.Format.paren fmt

中文:
定义 repr
  签名: {α} [Repr α] (o : Ordnode α) (n : 自然数)
  定义体: match o with
  | nil => (Std.Format.text "∅")
  | node _ l x r =>
      let fmt := Std.Format.joinSep
        [repr l n, Repr.reprPrec x n, repr r n]
        " "
      Std.Format.paren fmt

Depends on / 依赖: Format, Repr.reprPrec, Std.Format.joinSep, Std.Format.paren, Std.Format.text, joinSep, reprPrec
-/
def repr {α} [Repr α] (o : Ordnode α) (n : Nat) : Std.Format :=
  match o with
  | nil => (Std.Format.text "∅")
  | node _ l x r =>
      let fmt := Std.Format.joinSep
        [repr l n, Repr.reprPrec x n, repr r n]
        " "
      Std.Format.paren fmt

instance {α} [Repr α] : Repr (Ordnode α) :=
  ⟨repr⟩

-- Note: The function has been written with tactics to avoid extra junk
/--
Definition of `balanceL` / `balanceL` 的定义

English:
definition balanceL
  signature: (l : Ordnode α) (x : α) (r : Ordnode α)
  body: by
  rcases id r with _ | rs
  · rcases id l with _ | ⟨ls, ll, lx, lr⟩
    · exact ι x
    · rcases id ll with _ | lls
      · rcases lr with _ | ⟨_, _, lrx⟩
        · exact node 2 l x nil
        · exact node 3 (ι lx) lrx ι x
      · rcases id lr with _ | ⟨lrs, lrl, lrx, lrr⟩
        · exact node 3

中文:
定义 balanceL
  签名: (l : Ordnode α) (x : α) (r : Ordnode α)
  定义体: by
  rcases id r with _ | rs
  · rcases id l with _ | ⟨ls, ll, lx, lr⟩
    · exact ι x
    · rcases id ll with _ | lls
      · rcases lr with _ | ⟨_, _, lrx⟩
        · exact node 2 l x nil
        · exact node 3 (ι lx) lrx ι x
      · rcases id lr with _ | ⟨lrs, lrl, lrx, lrr⟩
        · exact node 3
-/
def balanceL (l : Ordnode α) (x : α) (r : Ordnode α) : Ordnode α := by
  rcases id r with _ | rs
  · rcases id l with _ | ⟨ls, ll, lx, lr⟩
    · exact ι x
    · rcases id ll with _ | lls
      · rcases lr with _ | ⟨_, _, lrx⟩
        · exact node 2 l x nil
        · exact node 3 (ι lx) lrx ι x
      · rcases id lr with _ | ⟨lrs, lrl, lrx, lrr⟩
        · exact node 3 ll lx ι x
        · exact
            if lrs < ratio * lls then node (ls + 1) ll lx (node (lrs + 1) lr x nil)
            else
              node (ls + 1) (node (lls + size lrl + 1) ll lx lrl) lrx
                (node (size lrr + 1) lrr x nil)
  · rcases id l with _ | ⟨ls, ll, lx, lr⟩
    · exact node (rs + 1) nil x r
    · refine if ls > delta * rs then ?_ else node (ls + rs + 1) l x r
      rcases id ll with _ | lls
      · exact nil
      --should not happen
      rcases id lr with _ | ⟨lrs, lrl, lrx, lrr⟩
      · exact nil
      --should not happen
      exact
        if lrs < ratio * lls then node (ls + rs + 1) ll lx (node (rs + lrs + 1) lr x r)
        else
          node (ls + rs + 1) (node (lls + size lrl + 1) ll lx lrl) lrx
            (node (size lrr + rs + 1) lrr x r)

/--
Definition of `balanceR` / `balanceR` 的定义

English:
definition balanceR
  signature: (l : Ordnode α) (x : α) (r : Ordnode α)
  body: by
  rcases id l with _ | ls
  · rcases id r with _ | ⟨rs, rl, rx, rr⟩
    · exact ι x
    · rcases id rr with _ | rrs
      · rcases rl with _ | ⟨_, _, rlx⟩
        · exact node 2 nil x r
        · exact node 3 (ι x) rlx ι rx
      · rcases id rl with _ | ⟨rls, rll, rlx, rlr⟩
        · exact node 3

中文:
定义 balanceR
  签名: (l : Ordnode α) (x : α) (r : Ordnode α)
  定义体: by
  rcases id l with _ | ls
  · rcases id r with _ | ⟨rs, rl, rx, rr⟩
    · exact ι x
    · rcases id rr with _ | rrs
      · rcases rl with _ | ⟨_, _, rlx⟩
        · exact node 2 nil x r
        · exact node 3 (ι x) rlx ι rx
      · rcases id rl with _ | ⟨rls, rll, rlx, rlr⟩
        · exact node 3
-/
def balanceR (l : Ordnode α) (x : α) (r : Ordnode α) : Ordnode α := by
  rcases id l with _ | ls
  · rcases id r with _ | ⟨rs, rl, rx, rr⟩
    · exact ι x
    · rcases id rr with _ | rrs
      · rcases rl with _ | ⟨_, _, rlx⟩
        · exact node 2 nil x r
        · exact node 3 (ι x) rlx ι rx
      · rcases id rl with _ | ⟨rls, rll, rlx, rlr⟩
        · exact node 3 (ι x) rx rr
        · exact
            if rls < ratio * rrs then node (rs + 1) (node (rls + 1) nil x rl) rx rr
            else
              node (rs + 1) (node (size rll + 1) nil x rll) rlx
                (node (size rlr + rrs + 1) rlr rx rr)
  · rcases id r with _ | ⟨rs, rl, rx, rr⟩
    · exact node (ls + 1) l x nil
    · refine if rs > delta * ls then ?_ else node (ls + rs + 1) l x r
      rcases id rr with _ | rrs
      · exact nil
      --should not happen
      rcases id rl with _ | ⟨rls, rll, rlx, rlr⟩
      · exact nil
      --should not happen
      exact
        if rls < ratio * rrs then node (ls + rs + 1) (node (ls + rls + 1) l x rl) rx rr
        else
          node (ls + rs + 1) (node (ls + size rll + 1) l x rll) rlx
            (node (size rlr + rrs + 1) rlr rx rr)

/--
Definition of `balance` / `balance` 的定义

English:
definition balance
  signature: (l : Ordnode α) (x : α) (r : Ordnode α)
  body: by
  rcases id l with _ | ⟨ls, ll, lx, lr⟩
  · rcases id r with _ | ⟨rs, rl, rx, rr⟩
    · exact ι x
    · rcases id rl with _ | ⟨rls, rll, rlx, rlr⟩
      · cases id rr
        · exact node 2 nil x r
        · exact node 3 (ι x) rx rr
      · rcases id rr with _ | rrs
        · exact node 3 (ι x) r

中文:
定义 balance
  签名: (l : Ordnode α) (x : α) (r : Ordnode α)
  定义体: by
  rcases id l with _ | ⟨ls, ll, lx, lr⟩
  · rcases id r with _ | ⟨rs, rl, rx, rr⟩
    · exact ι x
    · rcases id rl with _ | ⟨rls, rll, rlx, rlr⟩
      · cases id rr
        · exact node 2 nil x r
        · exact node 3 (ι x) rx rr
      · rcases id rr with _ | rrs
        · exact node 3 (ι x) r
-/
def balance (l : Ordnode α) (x : α) (r : Ordnode α) : Ordnode α := by
  rcases id l with _ | ⟨ls, ll, lx, lr⟩
  · rcases id r with _ | ⟨rs, rl, rx, rr⟩
    · exact ι x
    · rcases id rl with _ | ⟨rls, rll, rlx, rlr⟩
      · cases id rr
        · exact node 2 nil x r
        · exact node 3 (ι x) rx rr
      · rcases id rr with _ | rrs
        · exact node 3 (ι x) rlx ι rx
        · exact
            if rls < ratio * rrs then node (rs + 1) (node (rls + 1) nil x rl) rx rr
            else
              node (rs + 1) (node (size rll + 1) nil x rll) rlx
                (node (size rlr + rrs + 1) rlr rx rr)
  · rcases id r with _ | ⟨rs, rl, rx, rr⟩
    · rcases id ll with _ | lls
      · rcases lr with _ | ⟨_, _, lrx⟩
        · exact node 2 l x nil
        · exact node 3 (ι lx) lrx ι x
      · rcases id lr with _ | ⟨lrs, lrl, lrx, lrr⟩
        · exact node 3 ll lx ι x
        · exact
            if lrs < ratio * lls then node (ls + 1) ll lx (node (lrs + 1) lr x nil)
            else
              node (ls + 1) (node (lls + size lrl + 1) ll lx lrl) lrx
                (node (size lrr + 1) lrr x nil)
    · refine
        if delta * ls < rs then ?_ else if delta * rs < ls then ?_ else node (ls + rs + 1) l x r
      · rcases id rl with _ | ⟨rls, rll, rlx, rlr⟩
        · exact nil
        --should not happen
        rcases id rr with _ | rrs
        · exact nil
        --should not happen
        exact
          if rls < ratio * rrs then node (ls + rs + 1) (node (ls + rls + 1) l x rl) rx rr
          else
            node (ls + rs + 1) (node (ls + size rll + 1) l x rll) rlx
              (node (size rlr + rrs + 1) rlr rx rr)
      · rcases id ll with _ | lls
        · exact nil
        --should not happen
        rcases id lr with _ | ⟨lrs, lrl, lrx, lrr⟩
        · exact nil
        --should not happen
        exact
          if lrs < ratio * lls then node (ls + rs + 1) ll lx (node (lrs + rs + 1) lr x r)
          else
            node (ls + rs + 1) (node (lls + size lrl + 1) ll lx lrl) lrx
              (node (size lrr + rs + 1) lrr x r)

/--
Definition of `All` / `All` 的定义

English:
definition All
  signature: (P : α -> Prop)

中文:
定义 All
  签名: (P : α -> 命题)
-/
def All (P : α -> Prop) : Ordnode α -> Prop
  | nil => True
  | node _ l x r => All P l ∧ P x ∧ All P r

/--
Instance `All.decidable` / 实例 `All.decidable`

English:
instance All.decidable
  signature: {P : α -> Prop}
  body: All.decidable l
    have : Decidable (All P r) := All.decidable r
inferInstanceAs Decidable (All P l ∧ P m ∧ All P r)

中文:
实例 All.decidable
  签名: {P : α -> 命题}
  定义体: All.decidable l
    have : Decidable (All P r) := All.decidable r
inferInstanceAs Decidable (All P l ∧ P m ∧ All P r)

Depends on / 依赖: All.decidable, decidable
-/
instance All.decidable {P : α -> Prop} : (t : Ordnode α) -> [DecidablePred P] -> Decidable (All P t)
  | nil => isTrue trivial
  | node _ l m r =>
    have : Decidable (All P l) := All.decidable l
    have : Decidable (All P r) := All.decidable r
inferInstanceAs Decidable (All P l ∧ P m ∧ All P r)

/--
Definition of `Any` / `Any` 的定义

English:
definition Any
  signature: (P : α -> Prop)

中文:
定义 Any
  签名: (P : α -> 命题)
-/
def Any (P : α -> Prop) : Ordnode α -> Prop
  | nil => False
  | node _ l x r => Any P l ∨ P x ∨ Any P r

/--
Instance `Any.decidable` / 实例 `Any.decidable`

English:
instance Any.decidable
  signature: {P : α -> Prop}
  body: Any.decidable l
    have : Decidable (Any P r) := Any.decidable r
inferInstanceAs Decidable (Any P l ∨ P m ∨ Any P r)

中文:
实例 Any.decidable
  签名: {P : α -> 命题}
  定义体: Any.decidable l
    have : Decidable (Any P r) := Any.decidable r
inferInstanceAs Decidable (Any P l ∨ P m ∨ Any P r)

Depends on / 依赖: Any.decidable, decidable
-/
instance Any.decidable {P : α -> Prop} : (t : Ordnode α) -> [DecidablePred P] -> Decidable (Any P t)
  | nil => isFalse id
  | node _ l m r =>
    have : Decidable (Any P l) := Any.decidable l
    have : Decidable (Any P r) := Any.decidable r
inferInstanceAs Decidable (Any P l ∨ P m ∨ Any P r)

/--
Definition of `Emem` / `Emem` 的定义

English:
definition Emem
  signature: (x : α)
  body: Any (Eq x)

中文:
定义 Emem
  签名: (x : α)
  定义体: Any (Eq x)
-/
def Emem (x : α) : Ordnode α -> Prop :=
  Any (Eq x)

/--
Instance `Emem.decidable` / 实例 `Emem.decidable`

English:
instance Emem.decidable
  signature: (x : α) [DecidableEq α] (t : Ordnode α)
  body: inferInstanceAs Decidable (Any _ t)

中文:
实例 Emem.decidable
  签名: (x : α) [DecidableEq α] (t : Ordnode α)
  定义体: inferInstanceAs Decidable (Any _ t)

Depends on / 依赖: Decidable
-/
instance Emem.decidable (x : α) [DecidableEq α] (t : Ordnode α) : Decidable (Emem x t) :=
inferInstanceAs Decidable (Any _ t)

/--
Definition of `Amem` / `Amem` 的定义

English:
definition Amem
  signature: [LE α] (x : α)
  body: Any fun y => x <= y ∧ y <= x

中文:
定义 Amem
  签名: [LE α] (x : α)
  定义体: Any fun y => x <= y ∧ y <= x
-/
def Amem [LE α] (x : α) : Ordnode α -> Prop :=
  Any fun y => x <= y ∧ y <= x

/--
Instance `Amem.decidable` / 实例 `Amem.decidable`

English:
instance Amem.decidable
  signature: [LE α] [DecidableLE α] (x : α) (t : Ordnode α)
  body: inferInstanceAs Decidable (Any _ t)

中文:
实例 Amem.decidable
  签名: [LE α] [DecidableLE α] (x : α) (t : Ordnode α)
  定义体: inferInstanceAs Decidable (Any _ t)

Depends on / 依赖: Decidable
-/
instance Amem.decidable [LE α] [DecidableLE α] (x : α) (t : Ordnode α) : Decidable (Amem x t) :=
inferInstanceAs Decidable (Any _ t)

/--
Definition of `findMin'` / `findMin'` 的定义

English:
definition findMin'
  signature: : Ordnode α -> α -> α

中文:
定义 findMin'
  签名: : Ordnode α -> α -> α
-/
def findMin' : Ordnode α -> α -> α
  | nil, x => x
  | node _ l x _, _ => findMin' l x

/--
Definition of `findMin` / `findMin` 的定义

English:
definition findMin
  signature: : Ordnode α -> Option α

中文:
定义 findMin
  签名: : Ordnode α -> 选项类型 α
-/
def findMin : Ordnode α -> Option α
  | nil => none
  | node _ l x _ => some (findMin' l x)

/--
Definition of `findMax'` / `findMax'` 的定义

English:
definition findMax'
  signature: : α -> Ordnode α -> α

中文:
定义 findMax'
  签名: : α -> Ordnode α -> α
-/
def findMax' : α -> Ordnode α -> α
  | x, nil => x
  | _, node _ _ x r => findMax' x r

/--
Definition of `findMax` / `findMax` 的定义

English:
definition findMax
  signature: : Ordnode α -> Option α

中文:
定义 findMax
  签名: : Ordnode α -> 选项类型 α
-/
def findMax : Ordnode α -> Option α
  | nil => none
  | node _ _ x r => some (findMax' x r)

/--
Definition of `eraseMin` / `eraseMin` 的定义

English:
definition eraseMin
  signature: : Ordnode α -> Ordnode α

中文:
定义 eraseMin
  签名: : Ordnode α -> Ordnode α
-/
def eraseMin : Ordnode α -> Ordnode α
  | nil => nil
  | node _ nil _ r => r
  | node _ (node sz l' y r') x r => balanceR (eraseMin (node sz l' y r')) x r

/--
Definition of `eraseMax` / `eraseMax` 的定义

English:
definition eraseMax
  signature: : Ordnode α -> Ordnode α

中文:
定义 eraseMax
  签名: : Ordnode α -> Ordnode α
-/
def eraseMax : Ordnode α -> Ordnode α
  | nil => nil
  | node _ l _ nil => l
  | node _ l x (node sz l' y r') => balanceL l x (eraseMax (node sz l' y r'))

/--
Definition of `splitMin'` / `splitMin'` 的定义

English:
definition splitMin'
  signature: : Ordnode α -> α -> Ordnode α -> α × Ordnode α
  body: splitMin' ll lx lr
    (xm, balanceR l' x r)

中文:
定义 splitMin'
  签名: : Ordnode α -> α -> Ordnode α -> α × Ordnode α
  定义体: splitMin' ll lx lr
    (xm, balanceR l' x r)

Depends on / 依赖: splitMin
-/
def splitMin' : Ordnode α -> α -> Ordnode α -> α × Ordnode α
  | nil, x, r => (x, r)
  | node _ ll lx lr, x, r =>
    let (xm, l') := splitMin' ll lx lr
    (xm, balanceR l' x r)

/--
Definition of `splitMin` / `splitMin` 的定义

English:
definition splitMin
  signature: : Ordnode α -> Option (α × Ordnode α)

中文:
定义 splitMin
  签名: : Ordnode α -> 选项类型 (α × Ordnode α)
-/
def splitMin : Ordnode α -> Option (α × Ordnode α)
  | nil => none
  | node _ l x r => splitMin' l x r

/--
Definition of `splitMax'` / `splitMax'` 的定义

English:
definition splitMax'
  signature: : Ordnode α -> α -> Ordnode α -> Ordnode α × α
  body: splitMax' rl rx rr
    (balanceL l x r', xm)

中文:
定义 splitMax'
  签名: : Ordnode α -> α -> Ordnode α -> Ordnode α × α
  定义体: splitMax' rl rx rr
    (balanceL l x r', xm)

Depends on / 依赖: splitMax
-/
def splitMax' : Ordnode α -> α -> Ordnode α -> Ordnode α × α
  | l, x, nil => (l, x)
  | l, x, node _ rl rx rr =>
    let (r', xm) := splitMax' rl rx rr
    (balanceL l x r', xm)

/--
Definition of `splitMax` / `splitMax` 的定义

English:
definition splitMax
  signature: : Ordnode α -> Option (Ordnode α × α)

中文:
定义 splitMax
  签名: : Ordnode α -> 选项类型 (Ordnode α × α)
-/
def splitMax : Ordnode α -> Option (Ordnode α × α)
  | nil => none
  | node _ x l r => splitMax' x l r

/--
Definition of `glue` / `glue` 的定义

English:
definition glue
  signature: : Ordnode α -> Ordnode α -> Ordnode α
  body: splitMax' ll lx lr
      balanceR l' m r
    else
      let (m, r') := splitMin' rl rx rr
      balanceL l m r'

中文:
定义 glue
  签名: : Ordnode α -> Ordnode α -> Ordnode α
  定义体: splitMax' ll lx lr
      balanceR l' m r
    else
      let (m, r') := splitMin' rl rx rr
      balanceL l m r'

Depends on / 依赖: splitMax
-/
def glue : Ordnode α -> Ordnode α -> Ordnode α
  | nil, r => r
  | l@(node _ _ _ _), nil => l
  | l@(node sl ll lx lr), r@(node sr rl rx rr) =>
    if sl > sr then
      let (l', m) := splitMax' ll lx lr
      balanceR l' m r
    else
      let (m, r') := splitMin' rl rx rr
      balanceL l m r'

/--
Definition of `merge` / `merge` 的定义

English:
definition merge
  signature: (l : Ordnode α)
  body: (Ordnode.recOn (motive := fun _ => Ordnode α -> Ordnode α) l fun r => r)
    fun ls ll lx lr _ IHlr r =>
      (Ordnode.recOn (motive := fun _ => Ordnode α) r (node ls ll lx lr))
        fun rs rl rx rr IHrl _ =>
          if delta * ls < rs then balanceL IHrl rx rr
          else
            if del

中文:
定义 merge
  签名: (l : Ordnode α)
  定义体: (Ordnode.recOn (motive := fun _ => Ordnode α -> Ordnode α) l fun r => r)
    fun ls ll lx lr _ IHlr r =>
      (Ordnode.recOn (motive := fun _ => Ordnode α) r (node ls ll lx lr))
        fun rs rl rx rr IHrl _ =>
          if delta * ls < rs then balanceL IHrl rx rr
          else
            if del

Depends on / 依赖: Ordnode, Ordnode.recOn, balanceL, balanceR, motive
-/
def merge (l : Ordnode α) : Ordnode α -> Ordnode α :=
  (Ordnode.recOn (motive := fun _ => Ordnode α -> Ordnode α) l fun r => r)
    fun ls ll lx lr _ IHlr r =>
      (Ordnode.recOn (motive := fun _ => Ordnode α) r (node ls ll lx lr))
        fun rs rl rx rr IHrl _ =>
          if delta * ls < rs then balanceL IHrl rx rr
          else
            if delta * rs < ls then balanceR ll lx (IHlr <| node rs rl rx rr)
            else glue (node ls ll lx lr) (node rs rl rx rr)

/--
Definition of `insertMax` / `insertMax` 的定义

English:
definition insertMax
  signature: : Ordnode α -> α -> Ordnode α

中文:
定义 insertMax
  签名: : Ordnode α -> α -> Ordnode α
-/
def insertMax : Ordnode α -> α -> Ordnode α
  | nil, x => ι x
  | node _ l y r, x => balanceR l y (insertMax r x)

/--
Definition of `insertMin` / `insertMin` 的定义

English:
definition insertMin
  signature: (x : α)

中文:
定义 insertMin
  签名: (x : α)
-/
def insertMin (x : α) : Ordnode α -> Ordnode α
  | nil => ι x
  | node _ l y r => balanceR (insertMin x l) y r

/--
Definition of `link` / `link` 的定义

English:
definition link
  signature: (l : Ordnode α) (x : α)
  body: match l with
  | nil => insertMin x
  | node ls ll lx lr => fun r =>
    match r with
    | nil => insertMax l x
    | node rs rl rx rr =>
      if delta * ls < rs then balanceL (link ll x rl) rx rr
      else if delta * rs < ls then balanceR ll lx (link lr x rr)
      else node' l x r

中文:
定义 link
  签名: (l : Ordnode α) (x : α)
  定义体: match l with
  | nil => insertMin x
  | node ls ll lx lr => fun r =>
    match r with
    | nil => insertMax l x
    | node rs rl rx rr =>
      if delta * ls < rs then balanceL (link ll x rl) rx rr
      else if delta * rs < ls then balanceR ll lx (link lr x rr)
      else node' l x r

Depends on / 依赖: balanceL, balanceR, insertMax, insertMin
-/
def link (l : Ordnode α) (x : α) : Ordnode α -> Ordnode α :=
  match l with
  | nil => insertMin x
  | node ls ll lx lr => fun r =>
    match r with
    | nil => insertMax l x
    | node rs rl rx rr =>
      if delta * ls < rs then balanceL (link ll x rl) rx rr
      else if delta * rs < ls then balanceR ll lx (link lr x rr)
      else node' l x r

/--
Definition of `filter` / `filter` 的定义

English:
definition filter
  signature: (p : α -> Prop) [DecidablePred p]

中文:
定义 filter
  签名: (p : α -> 命题) [DecidablePred p]
-/
def filter (p : α -> Prop) [DecidablePred p] : Ordnode α -> Ordnode α
  | nil => nil
  | node _ l x r => if p x then
                      link (filter p l) x (filter p r) else
                      merge (filter p l) (filter p r)

/--
Definition of `partition` / `partition` 的定义

English:
definition partition
  signature: (p : α -> Prop) [DecidablePred p]
  body: partition p l
    let (r₁, r₂) := partition p r
    if p x then (link l₁ x r₁, merge l₂ r₂) else (merge l₁ r₁, link l₂ x r₂)

中文:
定义 partition
  签名: (p : α -> 命题) [DecidablePred p]
  定义体: partition p l
    let (r₁, r₂) := partition p r
    if p x then (link l₁ x r₁, merge l₂ r₂) else (merge l₁ r₁, link l₂ x r₂)

Depends on / 依赖: partition
-/
def partition (p : α -> Prop) [DecidablePred p] : Ordnode α -> Ordnode α × Ordnode α
  | nil => (nil, nil)
  | node _ l x r =>
    let (l₁, l₂) := partition p l
    let (r₁, r₂) := partition p r
    if p x then (link l₁ x r₁, merge l₂ r₂) else (merge l₁ r₁, link l₂ x r₂)

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: {β} (f : α -> β)

中文:
定义 map
  签名: {β} (f : α -> β)
-/
def map {β} (f : α -> β) : Ordnode α -> Ordnode β
  | nil => nil
  | node s l x r => node s (map f l) (f x) (map f r)

/--
Definition of `fold` / `fold` 的定义

English:
definition fold
  signature: {β} (z : β) (f : β -> α -> β -> β)

中文:
定义 fold
  签名: {β} (z : β) (f : β -> α -> β -> β)
-/
def fold {β} (z : β) (f : β -> α -> β -> β) : Ordnode α -> β
  | nil => z
  | node _ l x r => f (fold z f l) x (fold z f r)

/--
Definition of `foldl` / `foldl` 的定义

English:
definition foldl
  signature: {β} (f : β -> α -> β)

中文:
定义 foldl
  签名: {β} (f : β -> α -> β)
-/
def foldl {β} (f : β -> α -> β) : β -> Ordnode α -> β
  | z, nil => z
  | z, node _ l x r => foldl f (f (foldl f z l) x) r

/--
Definition of `foldr` / `foldr` 的定义

English:
definition foldr
  signature: {β} (f : α -> β -> β)

中文:
定义 foldr
  签名: {β} (f : α -> β -> β)
-/
def foldr {β} (f : α -> β -> β) : Ordnode α -> β -> β
  | nil, z => z
  | node _ l x r, z => foldr f l (f x (foldr f r z))

/--
Definition of `toList` / `toList` 的定义

English:
definition toList
  signature: (t : Ordnode α)
  body: foldr List.cons t []

中文:
定义 toList
  签名: (t : Ordnode α)
  定义体: foldr List.cons t []

Depends on / 依赖: List.cons
-/
def toList (t : Ordnode α) : List α :=
  foldr List.cons t []

/--
Definition of `toRevList` / `toRevList` 的定义

English:
definition toRevList
  signature: (t : Ordnode α)
  body: foldl (flip List.cons) [] t

中文:
定义 toRevList
  签名: (t : Ordnode α)
  定义体: foldl (flip List.cons) [] t

Depends on / 依赖: List.cons
-/
def toRevList (t : Ordnode α) : List α :=
  foldl (flip List.cons) [] t

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [ToString
  signature: α] : ToString (Ordnode α)
  body: ⟨fun t => "{" ++ String.intercalate ", " (t.toList.map toString) ++ "}"⟩

中文:
实例 [ToString
  签名: α] : ToString (Ordnode α)
  定义体: ⟨fun t => "{" ++ String.intercalate ", " (t.toList.map toString) ++ "}"⟩

Depends on / 依赖: String.intercalate, intercalate, t.toList.map, toList, toString
-/
instance [ToString α] : ToString (Ordnode α) :=
  ⟨fun t => "{" ++ String.intercalate ", " (t.toList.map toString) ++ "}"⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Std.ToFormat
  signature: α] : Std.ToFormat (Ordnode α) where
  body: fun t => Std.Format.joinSep (t.toList.map Std.ToFormat.format) (Std.Format.text ", ")

中文:
实例 [Std.ToFormat
  签名: α] : Std.ToFormat (Ordnode α) where
  定义体: fun t => Std.Format.joinSep (t.toList.map Std.ToFormat.format) (Std.Format.text ", ")

Depends on / 依赖: Format, Std.Format.joinSep, Std.Format.text, Std.ToFormat.format, ToFormat, format, joinSep, t.toList.map, toList
-/
instance [Std.ToFormat α] : Std.ToFormat (Ordnode α) where
  format := fun t => Std.Format.joinSep (t.toList.map Std.ToFormat.format) (Std.Format.text ", ")

/--
Definition of `Equiv` / `Equiv` 的定义

English:
definition Equiv
  signature: (t₁ t₂ : Ordnode α)
  body: t₁.size = t₂.size ∧ t₁.toList = t₂.toList

中文:
定义 等价
  签名: (t₁ t₂ : Ordnode α)
  定义体: t₁.size = t₂.size ∧ t₁.toList = t₂.toList

Depends on / 依赖: toList
-/
def Equiv (t₁ t₂ : Ordnode α) : Prop :=
  t₁.size = t₂.size ∧ t₁.toList = t₂.toList

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: α] : DecidableRel (@Equiv α)
  body: fun x y =>
  inferInstanceAs (Decidable (x.size = y.size ∧ x.toList = y.toList))

中文:
实例 [DecidableEq
  签名: α] : DecidableRel (@等价 α)
  定义体: fun x y =>
  inferInstanceAs (Decidable (x.size = y.size ∧ x.toList = y.toList))
-/
instance [DecidableEq α] : DecidableRel (@Equiv α) := fun x y =>
  inferInstanceAs (Decidable (x.size = y.size ∧ x.toList = y.toList))

/--
Definition of `powerset` / `powerset` 的定义

English:
definition powerset
  signature: (t : Ordnode α)
  body: insertMin nil foldr (fun x ts => glue (insertMin (ι x) (map (insertMin x) ts)) ts) t nil

中文:
定义 powerset
  签名: (t : Ordnode α)
  定义体: insertMin nil foldr (fun x ts => glue (insertMin (ι x) (map (insertMin x) ts)) ts) t nil

Depends on / 依赖: insertMin
-/
def powerset (t : Ordnode α) : Ordnode (Ordnode α) :=
insertMin nil foldr (fun x ts => glue (insertMin (ι x) (map (insertMin x) ts)) ts) t nil

/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: {β} (t₁ : Ordnode α) (t₂ : Ordnode β)
  body: fold nil (fun s₁ a s₂ => merge s₁ <| merge (map (Prod.mk a) t₂) s₂) t₁

中文:
定义 乘积
  签名: {β} (t₁ : Ordnode α) (t₂ : Ordnode β)
  定义体: fold nil (fun s₁ a s₂ => merge s₁ <| merge (map (Prod.mk a) t₂) s₂) t₁
-/
protected def prod {β} (t₁ : Ordnode α) (t₂ : Ordnode β) : Ordnode (α × β) :=
  fold nil (fun s₁ a s₂ => merge s₁ <| merge (map (Prod.mk a) t₂) s₂) t₁

/--
Definition of `copair` / `copair` 的定义

English:
definition copair
  signature: {β} (t₁ : Ordnode α) (t₂ : Ordnode β)
  body: merge (map Sum.inl t₁) (map Sum.inr t₂)

中文:
定义 copair
  签名: {β} (t₁ : Ordnode α) (t₂ : Ordnode β)
  定义体: merge (map Sum.inl t₁) (map Sum.inr t₂)
-/
protected def copair {β} (t₁ : Ordnode α) (t₂ : Ordnode β) : Ordnode (α oplus β) :=
  merge (map Sum.inl t₁) (map Sum.inr t₂)

/--
Definition of `pmap` / `pmap` 的定义

English:
definition pmap
  signature: {P : α -> Prop} {β} (f : forall a, P a -> β)

中文:
定义 pmap
  签名: {P : α -> 命题} {β} (f : 对任意 a, P a -> β)
-/
def pmap {P : α -> Prop} {β} (f : forall a, P a -> β) : forall t : Ordnode α, All P t -> Ordnode β
  | nil, _ => nil
  | node s l x r, ⟨hl, hx, hr⟩ => node s (pmap f l hl) (f x hx) (pmap f r hr)

/--
Definition of `attach'` / `attach'` 的定义

English:
definition attach'
  signature: {P : α -> Prop}
  body: pmap Subtype.mk

中文:
定义 attach'
  签名: {P : α -> 命题}
  定义体: pmap Subtype.mk

Depends on / 依赖: Subtype, Subtype.mk
-/
def attach' {P : α -> Prop} : forall t, All P t -> Ordnode { a // P a } :=
  pmap Subtype.mk

/--
Definition of `nth` / `nth` 的定义

English:
definition nth
  signature: : Ordnode α -> Nat -> Option α

中文:
定义 nth
  签名: : Ordnode α -> 自然数 -> 选项类型 α
-/
def nth : Ordnode α -> Nat -> Option α
  | nil, _ => none
  | node _ l x r, i =>
    match Nat.psub' i (size l) with
    | none => nth l i
    | some 0 => some x
    | some (j + 1) => nth r j

/--
Definition of `removeNth` / `removeNth` 的定义

English:
definition removeNth
  signature: : Ordnode α -> Nat -> Ordnode α

中文:
定义 removeNth
  签名: : Ordnode α -> 自然数 -> Ordnode α
-/
def removeNth : Ordnode α -> Nat -> Ordnode α
  | nil, _ => nil
  | node _ l x r, i =>
    match Nat.psub' i (size l) with
    | none => balanceR (removeNth l i) x r
    | some 0 => glue l r
    | some (j + 1) => balanceL l x (removeNth r j)

/--
Definition of `takeAux` / `takeAux` 的定义

English:
definition takeAux
  signature: : Ordnode α -> Nat -> Ordnode α

中文:
定义 takeAux
  签名: : Ordnode α -> 自然数 -> Ordnode α
-/
def takeAux : Ordnode α -> Nat -> Ordnode α
  | nil, _ => nil
  | node _ l x r, i =>
    if i = 0 then nil
    else
      match Nat.psub' i (size l) with
      | none => takeAux l i
      | some 0 => l
      | some (j + 1) => link l x (takeAux r j)

/--
Definition of `take` / `take` 的定义

English:
definition take
  signature: (i : Nat) (t : Ordnode α)
  body: if size t <= i then t else takeAux t i

中文:
定义 take
  签名: (i : 自然数) (t : Ordnode α)
  定义体: if size t <= i then t else takeAux t i

Depends on / 依赖: takeAux
-/
def take (i : Nat) (t : Ordnode α) : Ordnode α :=
  if size t <= i then t else takeAux t i

/--
Definition of `dropAux` / `dropAux` 的定义

English:
definition dropAux
  signature: : Ordnode α -> Nat -> Ordnode α

中文:
定义 dropAux
  签名: : Ordnode α -> 自然数 -> Ordnode α
-/
def dropAux : Ordnode α -> Nat -> Ordnode α
  | nil, _ => nil
  | t@(node _ l x r), i =>
    if i = 0 then t
    else
      match Nat.psub' i (size l) with
      | none => link (dropAux l i) x r
      | some 0 => insertMin x r
      | some (j + 1) => dropAux r j

/--
Definition of `drop` / `drop` 的定义

English:
definition drop
  signature: (i : Nat) (t : Ordnode α)
  body: if size t <= i then nil else dropAux t i

中文:
定义 drop
  签名: (i : 自然数) (t : Ordnode α)
  定义体: if size t <= i then nil else dropAux t i

Depends on / 依赖: dropAux
-/
def drop (i : Nat) (t : Ordnode α) : Ordnode α :=
  if size t <= i then nil else dropAux t i

/--
Definition of `splitAtAux` / `splitAtAux` 的定义

English:
definition splitAtAux
  signature: : Ordnode α -> Nat -> Ordnode α × Ordnode α
  body: splitAtAux l i
        (l₁, link l₂ x r)
      | some 0 => (glue l r, insertMin x r)
      | some (j + 1) =>
        let (r₁, r₂) := splitAtAux r j
        (link l x r₁, r₂)

中文:
定义 splitAtAux
  签名: : Ordnode α -> 自然数 -> Ordnode α × Ordnode α
  定义体: splitAtAux l i
        (l₁, link l₂ x r)
      | some 0 => (glue l r, insertMin x r)
      | some (j + 1) =>
        let (r₁, r₂) := splitAtAux r j
        (link l x r₁, r₂)

Depends on / 依赖: splitAtAux
-/
def splitAtAux : Ordnode α -> Nat -> Ordnode α × Ordnode α
  | nil, _ => (nil, nil)
  | t@(node _ l x r), i =>
    if i = 0 then (nil, t)
    else
      match Nat.psub' i (size l) with
      | none =>
        let (l₁, l₂) := splitAtAux l i
        (l₁, link l₂ x r)
      | some 0 => (glue l r, insertMin x r)
      | some (j + 1) =>
        let (r₁, r₂) := splitAtAux r j
        (link l x r₁, r₂)

/--
Definition of `splitAt` / `splitAt` 的定义

English:
definition splitAt
  signature: (i : Nat) (t : Ordnode α)
  body: if size t <= i then (t, nil) else splitAtAux t i

中文:
定义 splitAt
  签名: (i : 自然数) (t : Ordnode α)
  定义体: if size t <= i then (t, nil) else splitAtAux t i

Depends on / 依赖: splitAtAux
-/
def splitAt (i : Nat) (t : Ordnode α) : Ordnode α × Ordnode α :=
  if size t <= i then (t, nil) else splitAtAux t i

/--
Definition of `takeWhile` / `takeWhile` 的定义

English:
definition takeWhile
  signature: (p : α -> Prop) [DecidablePred p]

中文:
定义 takeWhile
  签名: (p : α -> 命题) [DecidablePred p]
-/
def takeWhile (p : α -> Prop) [DecidablePred p] : Ordnode α -> Ordnode α
  | nil => nil
  | node _ l x r => if p x then link l x (takeWhile p r) else takeWhile p l

/--
Definition of `dropWhile` / `dropWhile` 的定义

English:
definition dropWhile
  signature: (p : α -> Prop) [DecidablePred p]

中文:
定义 dropWhile
  签名: (p : α -> 命题) [DecidablePred p]
-/
def dropWhile (p : α -> Prop) [DecidablePred p] : Ordnode α -> Ordnode α
  | nil => nil
  | node _ l x r => if p x then dropWhile p r else link (dropWhile p l) x r

/--
Definition of `span` / `span` 的定义

English:
definition span
  signature: (p : α -> Prop) [DecidablePred p]
  body: span p r
      (link l x r₁, r₂)
    else
      let (l₁, l₂) := span p l
      (l₁, link l₂ x r)

中文:
定义 span
  签名: (p : α -> 命题) [DecidablePred p]
  定义体: span p r
      (link l x r₁, r₂)
    else
      let (l₁, l₂) := span p l
      (l₁, link l₂ x r)
-/
def span (p : α -> Prop) [DecidablePred p] : Ordnode α -> Ordnode α × Ordnode α
  | nil => (nil, nil)
  | node _ l x r =>
    if p x then
      let (r₁, r₂) := span p r
      (link l x r₁, r₂)
    else
      let (l₁, l₂) := span p l
      (l₁, link l₂ x r)

/--
Definition of `ofAscListAux₁` / `ofAscListAux₁` 的定义

English:
definition ofAscListAux₁
  signature: : forall l : List α, Nat -> Ordnode α × { l' : List α // l'.length <= l.length }
  body: Nat.le_succ_of_le h
        let (r, ⟨zs, h'⟩) := ofAscListAux₁ ys (s <<< 1)
        (link l y r, ⟨zs, le_trans h' (le_of_lt this)⟩)
        termination_by l => l.length

中文:
定义 ofAscListAux₁
  签名: : 对任意 l : 列表 α, 自然数 -> Ordnode α × { l' : 列表 α // l'.length <= l.length }
  定义体: Nat.le_succ_of_le h
        let (r, ⟨zs, h'⟩) := ofAscListAux₁ ys (s <<< 1)
        (link l y r, ⟨zs, le_trans h' (le_of_lt this)⟩)
        termination_by l => l.length

Depends on / 依赖: Nat.le_succ_of_le, le_succ_of_le
-/
def ofAscListAux₁ : forall l : List α, Nat -> Ordnode α × { l' : List α // l'.length <= l.length }
  | [] => fun _ => (nil, ⟨[], le_rfl⟩)
  | x :: xs => fun s =>
    if s = 1 then (ι x, ⟨xs, Nat.le_succ _⟩)
    else
      match ofAscListAux₁ xs (s <<< 1) with
      | (t, ⟨[], _⟩) => (t, ⟨[], Nat.zero_le _⟩)
      | (l, ⟨y :: ys, h⟩) =>
        have := Nat.le_succ_of_le h
        let (r, ⟨zs, h'⟩) := ofAscListAux₁ ys (s <<< 1)
        (link l y r, ⟨zs, le_trans h' (le_of_lt this)⟩)
        termination_by l => l.length

/--
Definition of `ofAscListAux₂` / `ofAscListAux₂` 的定义

English:
definition ofAscListAux₂
  signature: : List α -> Ordnode α -> Nat -> Ordnode α
  body: Nat.lt_succ_of_le h
      ofAscListAux₂ ys (link l x r) (s <<< 1)
      termination_by l => l.length

中文:
定义 ofAscListAux₂
  签名: : 列表 α -> Ordnode α -> 自然数 -> Ordnode α
  定义体: Nat.lt_succ_of_le h
      ofAscListAux₂ ys (link l x r) (s <<< 1)
      termination_by l => l.length

Depends on / 依赖: Nat.lt_succ_of_le, lt_succ_of_le
-/
def ofAscListAux₂ : List α -> Ordnode α -> Nat -> Ordnode α
  | [] => fun t _ => t
  | x :: xs => fun l s =>
    match ofAscListAux₁ xs s with
    | (r, ⟨ys, h⟩) =>
      have := Nat.lt_succ_of_le h
      ofAscListAux₂ ys (link l x r) (s <<< 1)
      termination_by l => l.length

/--
Definition of `ofAscList` / `ofAscList` 的定义

English:
definition ofAscList
  signature: : List α -> Ordnode α

中文:
定义 ofAscList
  签名: : 列表 α -> Ordnode α
-/
def ofAscList : List α -> Ordnode α
  | [] => nil
  | x :: xs => ofAscListAux₂ xs (ι x) 1

section

variable [LE α] [DecidableLE α]

/--
Definition of `mem` / `mem` 的定义

English:
definition mem
  signature: (x : α)

中文:
定义 mem
  签名: (x : α)
-/
def mem (x : α) : Ordnode α -> Bool
  | nil => false
  | node _ l y r =>
    match cmpLE x y with
    | Ordering.lt => mem x l
    | Ordering.eq => true
    | Ordering.gt => mem x r

/--
Definition of `find` / `find` 的定义

English:
definition find
  signature: (x : α)

中文:
定义 find
  签名: (x : α)
-/
def find (x : α) : Ordnode α -> Option α
  | nil => none
  | node _ l y r =>
    match cmpLE x y with
    | Ordering.lt => find x l
    | Ordering.eq => some y
    | Ordering.gt => find x r

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Membership α (Ordnode α)
  body: ⟨fun t x => t.mem x⟩

中文:
实例 :
  签名: Membership α (Ordnode α)
  定义体: ⟨fun t x => t.mem x⟩

Depends on / 依赖: t.mem
-/
instance : Membership α (Ordnode α) :=
  ⟨fun t x => t.mem x⟩

/--
Instance `mem.decidable` / 实例 `mem.decidable`

English:
instance mem.decidable
  signature: (x : α) (t : Ordnode α)
  body: Bool.decEq _ _

中文:
实例 mem.decidable
  签名: (x : α) (t : Ordnode α)
  定义体: Bool.decEq _ _

Depends on / 依赖: Bool.decEq
-/
instance mem.decidable (x : α) (t : Ordnode α) : Decidable (x in t) :=
  Bool.decEq _ _

/--
Definition of `insertWith` / `insertWith` 的定义

English:
definition insertWith
  signature: (f : α -> α) (x : α)

中文:
定义 insertWith
  签名: (f : α -> α) (x : α)
-/
def insertWith (f : α -> α) (x : α) : Ordnode α -> Ordnode α
  | nil => ι x
  | node sz l y r =>
    match cmpLE x y with
    | Ordering.lt => balanceL (insertWith f x l) y r
    | Ordering.eq => node sz l (f y) r
    | Ordering.gt => balanceR l y (insertWith f x r)

/--
Definition of `adjustWith` / `adjustWith` 的定义

English:
definition adjustWith
  signature: (f : α -> α) (x : α)

中文:
定义 adjustWith
  签名: (f : α -> α) (x : α)
-/
def adjustWith (f : α -> α) (x : α) : Ordnode α -> Ordnode α
  | nil => nil
  | _t@(node sz l y r) =>
    match cmpLE x y with
    | Ordering.lt => node sz (adjustWith f x l) y r
    | Ordering.eq => node sz l (f y) r
    | Ordering.gt => node sz l y (adjustWith f x r)

/--
Definition of `updateWith` / `updateWith` 的定义

English:
definition updateWith
  signature: (f : α -> Option α) (x : α)

中文:
定义 updateWith
  签名: (f : α -> 选项类型 α) (x : α)
-/
def updateWith (f : α -> Option α) (x : α) : Ordnode α -> Ordnode α
  | nil => nil
  | _t@(node sz l y r) =>
    match cmpLE x y with
    | Ordering.lt => balanceR (updateWith f x l) y r
    | Ordering.eq =>
      match f y with
      | none => glue l r
      | some a => node sz l a r
    | Ordering.gt => balanceL l y (updateWith f x r)

/--
Definition of `alter` / `alter` 的定义

English:
definition alter
  signature: (f : Option α -> Option α) (x : α)

中文:
定义 alter
  签名: (f : 选项类型 α -> 选项类型 α) (x : α)
-/
def alter (f : Option α -> Option α) (x : α) : Ordnode α -> Ordnode α
  | nil => Option.recOn (f none) nil Ordnode.singleton
  | _t@(node sz l y r) =>
    match cmpLE x y with
    | Ordering.lt => balance (alter f x l) y r
    | Ordering.eq =>
      match f (some y) with
      | none => glue l r
      | some a => node sz l a r
    | Ordering.gt => balance l y (alter f x r)

/--
Definition of `insert` / `insert` 的定义

English:
definition insert
  signature: (x : α)

中文:
定义 insert
  签名: (x : α)
-/
protected def insert (x : α) : Ordnode α -> Ordnode α
  | nil => ι x
  | node sz l y r =>
    match cmpLE x y with
    | Ordering.lt => balanceL (Ordnode.insert x l) y r
    | Ordering.eq => node sz l x r
    | Ordering.gt => balanceR l y (Ordnode.insert x r)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Insert α (Ordnode α)
  body: ⟨Ordnode.insert⟩

中文:
实例 :
  签名: Insert α (Ordnode α)
  定义体: ⟨Ordnode.insert⟩

Depends on / 依赖: Ordnode, Ordnode.insert, insert
-/
instance : Insert α (Ordnode α) :=
  ⟨Ordnode.insert⟩

/--
Definition of `insert'` / `insert'` 的定义

English:
definition insert'
  signature: (x : α)

中文:
定义 insert'
  签名: (x : α)
-/
def insert' (x : α) : Ordnode α -> Ordnode α
  | nil => ι x
  | t@(node _ l y r) =>
    match cmpLE x y with
    | Ordering.lt => balanceL (insert' x l) y r
    | Ordering.eq => t
    | Ordering.gt => balanceR l y (insert' x r)

/--
Definition of `split` / `split` 的定义

English:
definition split
  signature: (x : α)
  body: split x l
      (lt, link gt y r)
    | Ordering.eq => (l, r)
    | Ordering.gt =>
      let (lt, gt) := split x r
      (link l y lt, gt)

中文:
定义 split
  签名: (x : α)
  定义体: split x l
      (lt, link gt y r)
    | Ordering.eq => (l, r)
    | Ordering.gt =>
      let (lt, gt) := split x r
      (link l y lt, gt)
-/
def split (x : α) : Ordnode α -> Ordnode α × Ordnode α
  | nil => (nil, nil)
  | node _ l y r =>
    match cmpLE x y with
    | Ordering.lt =>
      let (lt, gt) := split x l
      (lt, link gt y r)
    | Ordering.eq => (l, r)
    | Ordering.gt =>
      let (lt, gt) := split x r
      (link l y lt, gt)

/--
Definition of `split3` / `split3` 的定义

English:
definition split3
  signature: (x : α)
  body: split3 x l
      (lt, f, link gt y r)
    | Ordering.eq => (l, some y, r)
    | Ordering.gt =>
      let (lt, f, gt) := split3 x r
      (link l y lt, f, gt)

中文:
定义 split3
  签名: (x : α)
  定义体: split3 x l
      (lt, f, link gt y r)
    | Ordering.eq => (l, some y, r)
    | Ordering.gt =>
      let (lt, f, gt) := split3 x r
      (link l y lt, f, gt)

Depends on / 依赖: split3
-/
def split3 (x : α) : Ordnode α -> Ordnode α × Option α × Ordnode α
  | nil => (nil, none, nil)
  | node _ l y r =>
    match cmpLE x y with
    | Ordering.lt =>
      let (lt, f, gt) := split3 x l
      (lt, f, link gt y r)
    | Ordering.eq => (l, some y, r)
    | Ordering.gt =>
      let (lt, f, gt) := split3 x r
      (link l y lt, f, gt)

/--
Definition of `erase` / `erase` 的定义

English:
definition erase
  signature: (x : α)

中文:
定义 erase
  签名: (x : α)
-/
def erase (x : α) : Ordnode α -> Ordnode α
  | nil => nil
  | _t@(node _ l y r) =>
    match cmpLE x y with
    | Ordering.lt => balanceR (erase x l) y r
    | Ordering.eq => glue l r
    | Ordering.gt => balanceL l y (erase x r)

/--
Definition of `findLtAux` / `findLtAux` 的定义

English:
definition findLtAux
  signature: (x : α)

中文:
定义 findLtAux
  签名: (x : α)
-/
def findLtAux (x : α) : Ordnode α -> α -> α
  | nil, best => best
  | node _ l y r, best => if x <= y then findLtAux x l best else findLtAux x r y

/--
Definition of `findLt` / `findLt` 的定义

English:
definition findLt
  signature: (x : α)

中文:
定义 findLt
  签名: (x : α)
-/
def findLt (x : α) : Ordnode α -> Option α
  | nil => none
  | node _ l y r => if x <= y then findLt x l else some (findLtAux x r y)

/--
Definition of `findGtAux` / `findGtAux` 的定义

English:
definition findGtAux
  signature: (x : α)

中文:
定义 findGtAux
  签名: (x : α)
-/
def findGtAux (x : α) : Ordnode α -> α -> α
  | nil, best => best
  | node _ l y r, best => if y <= x then findGtAux x r best else findGtAux x l y

/--
Definition of `findGt` / `findGt` 的定义

English:
definition findGt
  signature: (x : α)

中文:
定义 findGt
  签名: (x : α)
-/
def findGt (x : α) : Ordnode α -> Option α
  | nil => none
  | node _ l y r => if y <= x then findGt x r else some (findGtAux x l y)

/--
Definition of `findLeAux` / `findLeAux` 的定义

English:
definition findLeAux
  signature: (x : α)

中文:
定义 findLeAux
  签名: (x : α)
-/
def findLeAux (x : α) : Ordnode α -> α -> α
  | nil, best => best
  | node _ l y r, best =>
    match cmpLE x y with
    | Ordering.lt => findLeAux x l best
    | Ordering.eq => y
    | Ordering.gt => findLeAux x r y

/--
Definition of `findLe` / `findLe` 的定义

English:
definition findLe
  signature: (x : α)

中文:
定义 findLe
  签名: (x : α)
-/
def findLe (x : α) : Ordnode α -> Option α
  | nil => none
  | node _ l y r =>
    match cmpLE x y with
    | Ordering.lt => findLe x l
    | Ordering.eq => some y
    | Ordering.gt => some (findLeAux x r y)

/--
Definition of `findGeAux` / `findGeAux` 的定义

English:
definition findGeAux
  signature: (x : α)

中文:
定义 findGeAux
  签名: (x : α)
-/
def findGeAux (x : α) : Ordnode α -> α -> α
  | nil, best => best
  | node _ l y r, best =>
    match cmpLE x y with
    | Ordering.lt => findGeAux x l y
    | Ordering.eq => y
    | Ordering.gt => findGeAux x r best

/--
Definition of `findGe` / `findGe` 的定义

English:
definition findGe
  signature: (x : α)

中文:
定义 findGe
  签名: (x : α)
-/
def findGe (x : α) : Ordnode α -> Option α
  | nil => none
  | node _ l y r =>
    match cmpLE x y with
    | Ordering.lt => some (findGeAux x l y)
    | Ordering.eq => some y
    | Ordering.gt => findGe x r

/--
Definition of `findIndexAux` / `findIndexAux` 的定义

English:
definition findIndexAux
  signature: (x : α)

中文:
定义 findIndexAux
  签名: (x : α)
-/
def findIndexAux (x : α) : Ordnode α -> Nat -> Option Nat
  | nil, _ => none
  | node _ l y r, i =>
    match cmpLE x y with
    | Ordering.lt => findIndexAux x l i
    | Ordering.eq => some (i + size l)
    | Ordering.gt => findIndexAux x r (i + size l + 1)

/--
Definition of `findIndex` / `findIndex` 的定义

English:
definition findIndex
  signature: (x : α) (t : Ordnode α)
  body: findIndexAux x t 0

中文:
定义 findIndex
  签名: (x : α) (t : Ordnode α)
  定义体: findIndexAux x t 0

Depends on / 依赖: findIndexAux
-/
def findIndex (x : α) (t : Ordnode α) : Option Nat :=
  findIndexAux x t 0

/--
Definition of `isSubsetAux` / `isSubsetAux` 的定义

English:
definition isSubsetAux
  signature: : Ordnode α -> Ordnode α -> Bool
  body: split3 x t
    found.isSome && isSubsetAux l lt && isSubsetAux r gt

中文:
定义 isSubsetAux
  签名: : Ordnode α -> Ordnode α -> 布尔值
  定义体: split3 x t
    found.isSome && isSubsetAux l lt && isSubsetAux r gt

Depends on / 依赖: split3
-/
def isSubsetAux : Ordnode α -> Ordnode α -> Bool
  | nil, _ => true
  | _, nil => false
  | node _ l x r, t =>
    let (lt, found, gt) := split3 x t
    found.isSome && isSubsetAux l lt && isSubsetAux r gt

/--
Definition of `isSubset` / `isSubset` 的定义

English:
definition isSubset
  signature: (t₁ t₂ : Ordnode α)
  body: decide (size t₁ <= size t₂) && isSubsetAux t₁ t₂

中文:
定义 isSubset
  签名: (t₁ t₂ : Ordnode α)
  定义体: decide (size t₁ <= size t₂) && isSubsetAux t₁ t₂

Depends on / 依赖: isSubsetAux
-/
def isSubset (t₁ t₂ : Ordnode α) : Bool :=
  decide (size t₁ <= size t₂) && isSubsetAux t₁ t₂

/--
Definition of `disjoint` / `disjoint` 的定义

English:
definition disjoint
  signature: : Ordnode α -> Ordnode α -> Bool
  body: split3 x t
    found.isNone && disjoint l lt && disjoint r gt

中文:
定义 disjoint
  签名: : Ordnode α -> Ordnode α -> 布尔值
  定义体: split3 x t
    found.isNone && disjoint l lt && disjoint r gt

Depends on / 依赖: split3
-/
def disjoint : Ordnode α -> Ordnode α -> Bool
  | nil, _ => true
  | _, nil => true
  | node _ l x r, t =>
    let (lt, found, gt) := split3 x t
    found.isNone && disjoint l lt && disjoint r gt

/--
Definition of `union` / `union` 的定义

English:
definition union
  signature: : Ordnode α -> Ordnode α -> Ordnode α
  body: split x₁ t₂
        link (union l₁ l₂') x₁ (union r₁ r₂')

中文:
定义 union
  签名: : Ordnode α -> Ordnode α -> Ordnode α
  定义体: split x₁ t₂
        link (union l₁ l₂') x₁ (union r₁ r₂')
-/
def union : Ordnode α -> Ordnode α -> Ordnode α
  | t₁, nil => t₁
  | nil, t₂ => t₂
  | t₁@(node s₁ l₁ x₁ r₁), t₂@(node s₂ _ x₂ _) =>
    if s₂ = 1 then insert' x₂ t₁
    else
      if s₁ = 1 then insert x₁ t₂
      else
        let (l₂', r₂') := split x₁ t₂
        link (union l₁ l₂') x₁ (union r₁ r₂')

/--
Definition of `diff` / `diff` 的定义

English:
definition diff
  signature: : Ordnode α -> Ordnode α -> Ordnode α
  body: split x t₁
      let l₁₂ := diff l₁ l₂
      let r₁₂ := diff r₁ r₂
      if size l₁₂ + size r₁₂ = size t₁ then t₁ else merge l₁₂ r₁₂

中文:
定义 diff
  签名: : Ordnode α -> Ordnode α -> Ordnode α
  定义体: split x t₁
      let l₁₂ := diff l₁ l₂
      let r₁₂ := diff r₁ r₂
      if size l₁₂ + size r₁₂ = size t₁ then t₁ else merge l₁₂ r₁₂
-/
def diff : Ordnode α -> Ordnode α -> Ordnode α
  | t₁, nil => t₁
  | t₁, t₂@(node _ l₂ x r₂) =>
cond t₁.empty t₂
      let (l₁, r₁) := split x t₁
      let l₁₂ := diff l₁ l₂
      let r₁₂ := diff r₁ r₂
      if size l₁₂ + size r₁₂ = size t₁ then t₁ else merge l₁₂ r₁₂

/--
Definition of `inter` / `inter` 的定义

English:
definition inter
  signature: : Ordnode α -> Ordnode α -> Ordnode α
  body: split3 x t₂
      let l₁₂ := inter l₁ l₂
      let r₁₂ := inter r₁ r₂
      cond y.isSome (link l₁₂ x r₁₂) (merge l₁₂ r₁₂)

中文:
定义 inter
  签名: : Ordnode α -> Ordnode α -> Ordnode α
  定义体: split3 x t₂
      let l₁₂ := inter l₁ l₂
      let r₁₂ := inter r₁ r₂
      cond y.isSome (link l₁₂ x r₁₂) (merge l₁₂ r₁₂)

Depends on / 依赖: split3
-/
def inter : Ordnode α -> Ordnode α -> Ordnode α
  | nil, _ => nil
  | t₁@(node _ l₁ x r₁), t₂ =>
cond t₂.empty t₁
      let (l₂, y, r₂) := split3 x t₂
      let l₁₂ := inter l₁ l₂
      let r₁₂ := inter r₁ r₂
      cond y.isSome (link l₁₂ x r₁₂) (merge l₁₂ r₁₂)

/--
Definition of `ofList` / `ofList` 的定义

English:
definition ofList
  signature: (l : List α)
  body: l.foldr insert nil

中文:
定义 ofList
  签名: (l : 列表 α)
  定义体: l.foldr insert nil

Depends on / 依赖: insert, l.foldr
-/
def ofList (l : List α) : Ordnode α :=
  l.foldr insert nil

/--
Definition of `ofList'` / `ofList'` 的定义

English:
definition ofList'
  signature: : List α -> Ordnode α

中文:
定义 ofList'
  签名: : 列表 α -> Ordnode α
-/
def ofList' : List α -> Ordnode α
  | [] => nil
  | l@(_ :: _) => if List.IsChain (fun a b => ¬b <= a) l then ofAscList l else ofList l

/--
Definition of `image` / `image` 的定义

English:
definition image
  signature: {α β} [LE β] [DecidableLE β] (f : α -> β) (t : Ordnode α)
  body: ofList (t.toList.map f)

中文:
定义 像
  签名: {α β} [LE β] [DecidableLE β] (f : α -> β) (t : Ordnode α)
  定义体: ofList (t.toList.map f)

Depends on / 依赖: ofList, t.toList.map, toList
-/
def image {α β} [LE β] [DecidableLE β] (f : α -> β) (t : Ordnode α) : Ordnode β :=
  ofList (t.toList.map f)

end

end Ordnode
