/-
Copyright (c) 2019 mathlib community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Wojciech Nawrocki
-/
module

public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Util.CompileInductive
import Batteries.Tactic.Alias

/-!
# Binary tree

Provides binary tree storage for values of any type, with O(lg n) retrieval.
See also `Lean.Data.RBTree` for red-black trees - this version allows more operations
to be defined and is better suited for in-kernel computation.

We also specialize for `BinaryTree Unit`, which is a binary tree without any
additional data. We provide the notation `a △ b` for making a `BinaryTree Unit` with children
`a` and `b`.

## References

<https://leanprover-community.github.io/archive/stream/113488-general/topic/tactic.20question.html>
-/

@[expose] public section


/--
Inductive type `BinaryTree.` / 归纳类型 `BinaryTree.`

English:
inductive BinaryTree.{u}
  parameters: (α : Type u)
  constructors (2):
    - nil: BinaryTree α
    - node: (value : α) (left : BinaryTree α) (right : BinaryTree α) : BinaryTree α

中文:
归纳类型 BinaryTree.{u}
  参数: (α : 类型u)
  构造子 (2 个):
    - nil: BinaryTree α
    - node: (value : α) (left : BinaryTree α) (right : BinaryTree α) : BinaryTree α
-/
inductive BinaryTree.{u} (α : Type u) : Type u
  | nil : BinaryTree α
  | node (value : α) (left : BinaryTree α) (right : BinaryTree α) : BinaryTree α
  deriving DecidableEq, Repr
compile_inductive% BinaryTree

@[deprecated (since := "2026-06-07"), reducible]
alias Tree := BinaryTree

/-- **Alias** of `BinaryTree.nil`. -/
@[deprecated BinaryTree.nil (since := "2026-06-07")]
/--
Definition of `Tree.nil.` / `Tree.nil.` 的定义

English:
abbreviation Tree.nil.{u}
  signature: {α : Type u}
  body: BinaryTree.nil

中文:
缩写 Tree.nil.{u}
  签名: {α : 类型u}
  定义体: BinaryTree.nil

Depends on / 依赖: BinaryTree, BinaryTree.nil
-/
abbrev Tree.nil.{u} {α : Type u} : Tree α := BinaryTree.nil

/-- **Alias** of `BinaryTree.node`. -/
@[deprecated BinaryTree.node (since := "2026-06-07")]
/--
Definition of `Tree.node.` / `Tree.node.` 的定义

English:
abbreviation Tree.node.{u}
  signature: {α : Type u}
  body: BinaryTree.node value left right

中文:
缩写 Tree.node.{u}
  签名: {α : 类型u}
  定义体: BinaryTree.node value left right

Depends on / 依赖: BinaryTree, BinaryTree.node
-/
abbrev Tree.node.{u} {α : Type u}
    (value : α) (left : Tree α) (right : Tree α) : Tree α :=
  BinaryTree.node value left right

namespace BinaryTree

universe u

variable {α : Type u}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (BinaryTree α)
  body: ⟨nil⟩

中文:
实例 :
  签名: Inhabited (BinaryTree α)
  定义体: ⟨nil⟩
-/
instance : Inhabited (BinaryTree α) :=
  ⟨nil⟩

/--
Definition of `traverse` / `traverse` 的定义

English:
definition traverse

中文:
定义 traverse
-/
def traverse
    {m : Type* -> Type*} [Applicative m] {α β} (f : α -> m β) :
    BinaryTree α -> m (BinaryTree β)
  | .nil => pure nil
| .node a l r => .node < > f a <*> traverse f l <*> traverse f r

/-- **Alias** of `BinaryTree.traverse`. -/
@[deprecated BinaryTree.traverse (since := "2026-06-07")]
/--
Definition of `_root_.Tree.traverse` / `_root_.Tree.traverse` 的定义

English:
abbreviation _root_.Tree.traverse
  signature: {m : Type* -> Type*} [Applicative m] {α β} (f : α -> m β)
  body: BinaryTree.traverse f t

中文:
缩写 _root_.Tree.traverse
  签名: {m : 类型 -> 类型} [Applicative m] {α β} (f : α -> m β)
  定义体: BinaryTree.traverse f t

Depends on / 依赖: BinaryTree, BinaryTree.traverse, traverse
-/
abbrev _root_.Tree.traverse {m : Type* -> Type*} [Applicative m] {α β} (f : α -> m β)
(t : Tree α) : m (Tree β) :=
  BinaryTree.traverse f t

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: {β} (f : α -> β)

中文:
定义 map
  签名: {β} (f : α -> β)
-/
def map {β} (f : α -> β) : BinaryTree α -> BinaryTree β
  | nil => nil
  | node a l r => node (f a) (map f l) (map f r)

/-- **Alias** of `BinaryTree.map`. -/
@[deprecated BinaryTree.map (since := "2026-06-07")]
/--
Definition of `_root_.Tree.map` / `_root_.Tree.map` 的定义

English:
abbreviation _root_.Tree.map
  signature: {α β} (f : α -> β) (t : Tree α)
  body: BinaryTree.map f t

中文:
缩写 _root_.Tree.map
  签名: {α β} (f : α -> β) (t : Tree α)
  定义体: BinaryTree.map f t

Depends on / 依赖: BinaryTree, BinaryTree.map
-/
abbrev _root_.Tree.map {α β} (f : α -> β) (t : Tree α) : Tree β := BinaryTree.map f t

/--
theorem `id_map` / 定理 `id_map`

English:
theorem id_map
  given: (t : BinaryTree α)
  statement: t.map id = t
  proof: by
  induction t with
  | nil => rw [map]
  | node v l r hl hr => rw [map, hl, hr, id_eq]

中文:
定理 id_map
  条件: (t : BinaryTree α)
  结论: t.map id = t
  证明: by
  induction t with
  | nil => rw [map]
  | node v l r hl hr => rw [map, hl, hr, id_eq]

Depends on / 依赖: id_eq
-/
theorem id_map (t : BinaryTree α) : t.map id = t := by
  induction t with
  | nil => rw [map]
  | node v l r hl hr => rw [map, hl, hr, id_eq]

/--
theorem `comp_map` / 定理 `comp_map`

English:
theorem comp_map
  given: {β γ : Type*} (f : α -> β) (g : β -> γ) (t : BinaryTree α)
  proof: by
  induction t with
  | nil => rw [map, map, map]
  | node v l r hl hr => rw [map, map, map, hl, hr, Function.comp_apply]

中文:
定理 comp_map
  条件: {β γ : 类型} (f : α -> β) (g : β -> γ) (t : BinaryTree α)
  证明: by
  induction t with
  | nil => rw [map, map, map]
  | node v l r hl hr => rw [map, map, map, hl, hr, Function.comp_apply]

Depends on / 依赖: Function, Function.comp_apply, comp_apply
-/
theorem comp_map {β γ : Type*} (f : α -> β) (g : β -> γ) (t : BinaryTree α) :
    t.map (g ∘ f) = (t.map f).map g := by
  induction t with
  | nil => rw [map, map, map]
  | node v l r hl hr => rw [map, map, map, hl, hr, Function.comp_apply]

/--
theorem `traverse_pure` / 定理 `traverse_pure`

English:
theorem traverse_pure
  statement: (t : BinaryTree α) {m : Type u -> Type*}
  proof: by
  induction t with
  | nil => rw [traverse]
  | node v l r hl hr =>
    rw [traverse]; rw [hl]; rw [hr]; rw [map_pure]; rw [pure_seq]; rw [seq_pure]; rw [map_pure]; rw [map_pure]

中文:
定理 traverse_pure
  结论: (t : BinaryTree α) {m : 类型u -> 类型}
  证明: by
  induction t with
  | nil => rw [traverse]
  | node v l r hl hr =>
    rw [traverse]; rw [hl]; rw [hr]; rw [map_pure]; rw [pure_seq]; rw [seq_pure]; rw [map_pure]; rw [map_pure]

Depends on / 依赖: map_pure, pure_seq, seq_pure, traverse
-/
theorem traverse_pure (t : BinaryTree α) {m : Type u -> Type*}
    [Applicative m] [LawfulApplicative m] :
    t.traverse (pure : α -> m α) = pure t := by
  induction t with
  | nil => rw [traverse]
  | node v l r hl hr =>
    rw [traverse]; rw [hl]; rw [hr]; rw [map_pure]; rw [pure_seq]; rw [seq_pure]; rw [map_pure]; rw [map_pure]

/-- The number of internal nodes (i.e. not including leaves) of a binary tree -/
@[simp]
/--
Definition of `numNodes` / `numNodes` 的定义

English:
definition numNodes
  signature: : BinaryTree α -> Nat

中文:
定义 numNodes
  签名: : BinaryTree α -> 自然数
-/
def numNodes : BinaryTree α -> Nat
  | nil => 0
  | node _ a b => a.numNodes + b.numNodes + 1

/-- **Alias** of `BinaryTree.numNodes`. -/
@[deprecated BinaryTree.numNodes (since := "2026-06-07")]
/--
Definition of `_root_.Tree.numNodes` / `_root_.Tree.numNodes` 的定义

English:
abbreviation _root_.Tree.numNodes
  signature: {α} (t : Tree α)
  body: BinaryTree.numNodes t

中文:
缩写 _root_.Tree.numNodes
  签名: {α} (t : Tree α)
  定义体: BinaryTree.numNodes t

Depends on / 依赖: BinaryTree, BinaryTree.numNodes, numNodes
-/
abbrev _root_.Tree.numNodes {α} (t : Tree α) : Nat := BinaryTree.numNodes t

/-- The number of leaves of a binary tree -/
@[simp]
/--
Definition of `numLeaves` / `numLeaves` 的定义

English:
definition numLeaves
  signature: : BinaryTree α -> Nat

中文:
定义 numLeaves
  签名: : BinaryTree α -> 自然数
-/
def numLeaves : BinaryTree α -> Nat
  | nil => 1
  | node _ a b => a.numLeaves + b.numLeaves

/-- **Alias** of `BinaryTree.numLeaves`. -/
@[deprecated BinaryTree.numLeaves (since := "2026-06-07")]
/--
Definition of `_root_.Tree.numLeaves` / `_root_.Tree.numLeaves` 的定义

English:
abbreviation _root_.Tree.numLeaves
  signature: {α} (t : Tree α)
  body: BinaryTree.numLeaves t

中文:
缩写 _root_.Tree.numLeaves
  签名: {α} (t : Tree α)
  定义体: BinaryTree.numLeaves t

Depends on / 依赖: BinaryTree, BinaryTree.numLeaves, numLeaves
-/
abbrev _root_.Tree.numLeaves {α} (t : Tree α) : Nat := BinaryTree.numLeaves t

/-- The height - length of the longest path from the root - of a binary tree -/
@[simp]
/--
Definition of `height` / `height` 的定义

English:
definition height
  signature: : BinaryTree α -> Nat

中文:
定义 height
  签名: : BinaryTree α -> 自然数
-/
def height : BinaryTree α -> Nat
  | nil => 0
  | node _ a b => max a.height b.height + 1

/-- **Alias** of `BinaryTree.height`. -/
@[deprecated BinaryTree.height (since := "2026-06-07")]
/--
Definition of `_root_.Tree.height` / `_root_.Tree.height` 的定义

English:
abbreviation _root_.Tree.height
  signature: {α} (t : Tree α)
  body: BinaryTree.height t

中文:
缩写 _root_.Tree.height
  签名: {α} (t : Tree α)
  定义体: BinaryTree.height t

Depends on / 依赖: BinaryTree, BinaryTree.height, height
-/
abbrev _root_.Tree.height {α} (t : Tree α) : Nat := BinaryTree.height t

/--
theorem `numLeaves_eq_numNodes_succ` / 定理 `numLeaves_eq_numNodes_succ`

English:
theorem numLeaves_eq_numNodes_succ
  given: (x : BinaryTree α)
  statement: x.numLeaves = x.numNodes + 1
  proof: by
  induction x <;> simp [*, Nat.add_comm, Nat.add_assoc, Nat.add_left_comm]

中文:
定理 numLeaves_eq_numNodes_succ
  条件: (x : BinaryTree α)
  结论: x.numLeaves = x.numNodes + 1
  证明: by
  induction x <;> simp [*, Nat.add_comm, Nat.add_assoc, Nat.add_left_comm]

Depends on / 依赖: Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, add_assoc, add_comm, add_left_comm
-/
theorem numLeaves_eq_numNodes_succ (x : BinaryTree α) : x.numLeaves = x.numNodes + 1 := by
  induction x <;> simp [*, Nat.add_comm, Nat.add_assoc, Nat.add_left_comm]

/--
theorem `numLeaves_pos` / 定理 `numLeaves_pos`

English:
theorem numLeaves_pos
  given: (x : BinaryTree α)
  statement: 0 < x.numLeaves
  proof: by
  rw [numLeaves_eq_numNodes_succ]
  exact x.numNodes.zero_lt_succ

中文:
定理 numLeaves_pos
  条件: (x : BinaryTree α)
  结论: 0 < x.numLeaves
  证明: by
  rw [numLeaves_eq_numNodes_succ]
  exact x.numNodes.zero_lt_succ

Depends on / 依赖: numLeaves_eq_numNodes_succ, numNodes, x.numNodes.zero_lt_succ, zero_lt_succ
-/
theorem numLeaves_pos (x : BinaryTree α) : 0 < x.numLeaves := by
  rw [numLeaves_eq_numNodes_succ]
  exact x.numNodes.zero_lt_succ

/--
theorem `height_le_numNodes` / 定理 `height_le_numNodes`

English:
theorem height_le_numNodes
  statement: forall x : BinaryTree α, x.height <= x.numNodes

中文:
定理 height_le_numNodes
  结论: 对任意 x : BinaryTree α, x.height <= x.numNodes
-/
theorem height_le_numNodes : forall x : BinaryTree α, x.height <= x.numNodes
  | nil => Nat.le_refl _
| node _ a b => Nat.succ_le_succ
Nat.max_le.2 ⟨Nat.le_trans a.height_le_numNodes a.numNodes.le_add_right _,
Nat.le_trans b.height_le_numNodes b.numNodes.le_add_left _⟩

/-- The left child of the tree, or `nil` if the tree is `nil` -/
@[simp]
/--
Definition of `left` / `left` 的定义

English:
definition left
  signature: : BinaryTree α -> BinaryTree α

中文:
定义 left
  签名: : BinaryTree α -> BinaryTree α
-/
def left : BinaryTree α -> BinaryTree α
  | nil => nil
  | node _ l _r => l

/-- **Alias** of `BinaryTree.left`. -/
@[deprecated BinaryTree.left (since := "2026-06-07")]
/--
Definition of `_root_.Tree.left` / `_root_.Tree.left` 的定义

English:
abbreviation _root_.Tree.left
  signature: {α} (t : Tree α)
  body: BinaryTree.left t

中文:
缩写 _root_.Tree.left
  签名: {α} (t : Tree α)
  定义体: BinaryTree.left t

Depends on / 依赖: BinaryTree, BinaryTree.left
-/
abbrev _root_.Tree.left {α} (t : Tree α) : Tree α := BinaryTree.left t

/-- The right child of the tree, or `nil` if the tree is `nil` -/
@[simp]
/--
Definition of `right` / `right` 的定义

English:
definition right
  signature: : BinaryTree α -> BinaryTree α

中文:
定义 right
  签名: : BinaryTree α -> BinaryTree α
-/
def right : BinaryTree α -> BinaryTree α
  | nil => nil
  | node _ _l r => r

/-- **Alias** of `BinaryTree.right`. -/
@[deprecated BinaryTree.right (since := "2026-06-07")]
/--
Definition of `_root_.Tree.right` / `_root_.Tree.right` 的定义

English:
abbreviation _root_.Tree.right
  signature: {α} (t : Tree α)
  body: BinaryTree.right t

中文:
缩写 _root_.Tree.right
  签名: {α} (t : Tree α)
  定义体: BinaryTree.right t

Depends on / 依赖: BinaryTree, BinaryTree.right
-/
abbrev _root_.Tree.right {α} (t : Tree α) : Tree α := BinaryTree.right t

/-- A node with `Unit` data -/
scoped infixr:65 " △ " => BinaryTree.node ()

/-- Induction principle for `BinaryTree Unit`s -/
@[elab_as_elim]
/--
Definition of `unitRecOn` / `unitRecOn` 的定义

English:
definition unitRecOn
  signature: {motive : BinaryTree Unit -> Sort*} (t : BinaryTree Unit) (base : motive nil)
  body: t.recOn base fun _u => ind

中文:
定义 unitRecOn
  签名: {motive : BinaryTree Unit -> Sort*} (t : BinaryTree Unit) (base : motive nil)
  定义体: t.recOn base fun _u => ind

Depends on / 依赖: t.recOn
-/
def unitRecOn {motive : BinaryTree Unit -> Sort*} (t : BinaryTree Unit) (base : motive nil)
    (ind : forall x y, motive x -> motive y -> motive (x △ y)) : motive t :=
  t.recOn base fun _u => ind

/-- **Alias** of `BinaryTree.unitRecOn`. -/
@[deprecated BinaryTree.unitRecOn (since := "2026-06-07")]
/--
Definition of `_root_.Tree.unitRecOn` / `_root_.Tree.unitRecOn` 的定义

English:
abbreviation _root_.Tree.unitRecOn
  signature: {motive : Tree Unit -> Sort*} (t : Tree Unit) (base : motive nil)
  body: BinaryTree.unitRecOn t base ind

中文:
缩写 _root_.Tree.unitRecOn
  签名: {motive : Tree Unit -> Sort*} (t : Tree Unit) (base : motive nil)
  定义体: BinaryTree.unitRecOn t base ind

Depends on / 依赖: BinaryTree, BinaryTree.unitRecOn, unitRecOn
-/
abbrev _root_.Tree.unitRecOn {motive : Tree Unit -> Sort*} (t : Tree Unit) (base : motive nil)
    (ind : forall x y, motive x -> motive y -> motive (x △ y)) : motive t :=
  BinaryTree.unitRecOn t base ind

/--
theorem `left_node_right_eq_self` / 定理 `left_node_right_eq_self`

English:
theorem left_node_right_eq_self
  statement: forall {x : BinaryTree Unit} (_hx : x != nil), x.left △ x.right = x

中文:
定理 left_node_right_eq_self
  结论: 对任意 {x : BinaryTree Unit} (_hx : x != nil), x.left △ x.right = x
-/
theorem left_node_right_eq_self : forall {x : BinaryTree Unit} (_hx : x != nil), x.left △ x.right = x
  | nil, h => by trivial
  | node _ _ _, _ => rfl -- Porting note: `a △ b` no longer works in pattern matching

end BinaryTree
