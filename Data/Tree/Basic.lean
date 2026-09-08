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


/-- A binary tree with values stored in non-leaf nodes. -/
/-
**BinaryTree.** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A binary tree with values stored in non-leaf nodes.
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
/-
**Tree.nil.** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Alias** of `BinaryTree.nil`.
-/
abbrev Tree.nil.{u} {α : Type u} : Tree α := BinaryTree.nil

/-- **Alias** of `BinaryTree.node`. -/
@[deprecated BinaryTree.node (since := "2026-06-07")]
/-
**Tree.node.** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Alias** of `BinaryTree.node`.
-/
abbrev Tree.node.{u} {α : Type u}
    (value : α) (left : Tree α) (right : Tree α) : Tree α :=
  BinaryTree.node value left right

namespace BinaryTree

universe u

variable {α : Type u}

/-
**BinaryTree.** 是 Mathlib 中的一个实例，位于命名空间 `BinaryTree`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (BinaryTree α) :=
  ⟨nil⟩

/--
Do an action for every node of the tree.
Actions are taken in node -> left subtree -> right subtree recursive order.
This function is the `traverse` function for the `Traversable BinaryTree` instance.
-/
/-
**BinaryTree.traverse** 是 Mathlib 中的一个定义，位于命名空间 `BinaryTree`。
形式化陈述：{m : Type u_1 → Type u_2} →   [Applicative m] → {α : Type u_3} → {β : Type
 u_1} → (α → m β) → BinaryTree α → m (BinaryTree β)
参数：α → m β；BinaryTree β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Do an action for every node of the tree.
Actions are taken in node -> left subtree -> right subtree recursive order.
This function is the `traverse` function for the `Traversable BinaryTree` instan
ce.
-/
def traverse
    {m : Type* → Type*} [Applicative m] {α β} (f : α → m β) :
    BinaryTree α → m (BinaryTree β)
  | .nil => pure nil
  | .node a l r => .node <$> f a <*> traverse f l <*> traverse f r

/-- **Alias** of `BinaryTree.traverse`. -/
@[deprecated BinaryTree.traverse (since := "2026-06-07")]
/-
**BinaryTree._root_.Tree.traverse** 是 Mathlib 中的一个缩写定义，位于命名空间 `BinaryTree`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Alias** of `BinaryTree.traverse`.
-/
abbrev _root_.Tree.traverse {m : Type* → Type*} [Applicative m] {α β} (f : α → m β)
(t : Tree α) : m (Tree β) :=
  BinaryTree.traverse f t

/-- Apply a function to each value in the BinaryTree.
This is the `map` function for the `BinaryTree` functor.
-/
/-
**BinaryTree.map** 是 Mathlib 中的一个定义，位于命名空间 `BinaryTree`。
形式化陈述：{α : Type u} → {β : Type u_1} → (α → β) → BinaryTree α → BinaryTree β
参数：α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Apply a function to each value in the BinaryTree.
This is the `map` function for the `BinaryTree` functor.
-/
def map {β} (f : α → β) : BinaryTree α → BinaryTree β
  | nil => nil
  | node a l r => node (f a) (map f l) (map f r)

/-- **Alias** of `BinaryTree.map`. -/
@[deprecated BinaryTree.map (since := "2026-06-07")]
/-
**BinaryTree._root_.Tree.map** 是 Mathlib 中的一个缩写定义，位于命名空间 `BinaryTree`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Alias** of `BinaryTree.map`.
-/
abbrev _root_.Tree.map {α β} (f : α → β) (t : Tree α) : Tree β := BinaryTree.map f t
/-
**BinaryTree.id_map** 是 Mathlib 中的一个定理，位于命名空间 `BinaryTree`。
形式化陈述：id_map (t : BinaryTree α) : t.map id = t
参数：t : BinaryTree α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BinaryTree.map.eq_1`：∀ {α : Type u} {β : Type u_1} (f : α → β), BinaryTr
ee.map f BinaryTree.nil = BinaryTree.nil
· 使用定理 `BinaryTree.map.eq_2`：∀ {α : Type u} {β : Type u_1} (f : α → β) (a : α) (
l r : BinaryTree α),   BinaryTree.map f (BinaryTree.node a l r) = BinaryTree.nod
e (f a) (…
· 使用定理 `id_eq`：∀ {α : Sort u_1} (a : α), id a = a
-/
theorem id_map (t : BinaryTree α) : t.map id = t := by
  induction t with
  | nil => rw [map]
  | node v l r hl hr => rw [map, hl, hr, id_eq]
/-
**BinaryTree.comp_map** 是 Mathlib 中的一个定理，位于命名空间 `BinaryTree`。
形式化陈述：comp_map {β γ : Type*} (f : α -> β) (g : β -> γ) (t : BinaryTree α) : t.ma
p (g ∘ f) = (t.map f).map g
参数：f : α -> β；g : β -> γ；t : BinaryTree α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BinaryTree.map.eq_1`：∀ {α : Type u} {β : Type u_1} (f : α → β), BinaryTr
ee.map f BinaryTree.nil = BinaryTree.nil
· 使用定理 `BinaryTree.map.eq_2`：∀ {α : Type u} {β : Type u_1} (f : α → β) (a : α) (
l r : BinaryTree α),   BinaryTree.map f (BinaryTree.node a l r) = BinaryTree.nod
e (f a) (…
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
-/
theorem comp_map {β γ : Type*} (f : α → β) (g : β → γ) (t : BinaryTree α) :
    t.map (g ∘ f) = (t.map f).map g := by
  induction t with
  | nil => rw [map, map, map]
  | node v l r hl hr => rw [map, map, map, hl, hr, Function.comp_apply]
/-
**BinaryTree.traverse_pure** 是 Mathlib 中的一个定理，位于命名空间 `BinaryTree`。
形式化陈述：traverse_pure (t : BinaryTree α) {m : Type u -> Type*} [Applicative m] [La
wfulApplicative m] : t.traverse (pure : α -> m α) = pure t
参数：t : BinaryTree α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BinaryTree.traverse.eq_1`：∀ {m : Type u_1 → Type u_2} [inst : Applicativ
e m] {α : Type u_3} {β : Type u_1} (f : α → m β),   BinaryTree.traverse f Binary
Tree.nil = pur…
· 使用定理 `BinaryTree.traverse.eq_2`：∀ {m : Type u_1 → Type u_2} [inst : Applicativ
e m] {α : Type u_3} {β : Type u_1} (f : α → m β) (a : α)   (l r : BinaryTree α),
   BinaryTree.…
· 使用定理 `LawfulApplicative.map_pure`：∀ {f : Type u → Type v} {inst : Applicative 
f} [self : LawfulApplicative f] {α β : Type u} (g : α → β) (x : α),   g <$> pure
 x = pure (g x)
· 使用定理 `LawfulApplicative.pure_seq`：∀ {f : Type u → Type v} {inst : Applicative 
f} [self : LawfulApplicative f] {α β : Type u} (g : α → β) (x : f α),   pure g <
*> x = g <$> x
· 使用定理 `LawfulApplicative.seq_pure`：∀ {f : Type u → Type v} {inst : Applicative 
f} [self : LawfulApplicative f] {α β : Type u} (g : f (α → β)) (x : α),   g <*> 
pure x = (fun h …
-/
theorem traverse_pure (t : BinaryTree α) {m : Type u → Type*}
    [Applicative m] [LawfulApplicative m] :
    t.traverse (pure : α → m α) = pure t := by
  induction t with
  | nil => rw [traverse]
  | node v l r hl hr =>
    rw [traverse, hl, hr, map_pure, pure_seq, seq_pure, map_pure, map_pure]

/-- The number of internal nodes (i.e. not including leaves) of a binary tree -/
@[simp]
/-
**BinaryTree.numNodes** 是 Mathlib 中的一个定义，位于命名空间 `BinaryTree`。
形式化陈述：{α : Type u} → BinaryTree α → ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The number of internal nodes (i.e. not including leaves) of a binary tree
-/
def numNodes : BinaryTree α → ℕ
  | nil => 0
  | node _ a b => a.numNodes + b.numNodes + 1

/-- **Alias** of `BinaryTree.numNodes`. -/
@[deprecated BinaryTree.numNodes (since := "2026-06-07")]
/-
**BinaryTree._root_.Tree.numNodes** 是 Mathlib 中的一个缩写定义，位于命名空间 `BinaryTree`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Alias** of `BinaryTree.numNodes`.
-/
abbrev _root_.Tree.numNodes {α} (t : Tree α) : ℕ := BinaryTree.numNodes t

/-- The number of leaves of a binary tree -/
@[simp]
/-
**BinaryTree.numLeaves** 是 Mathlib 中的一个定义，位于命名空间 `BinaryTree`。
形式化陈述：{α : Type u} → BinaryTree α → ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The number of leaves of a binary tree
-/
def numLeaves : BinaryTree α → ℕ
  | nil => 1
  | node _ a b => a.numLeaves + b.numLeaves

/-- **Alias** of `BinaryTree.numLeaves`. -/
@[deprecated BinaryTree.numLeaves (since := "2026-06-07")]
/-
**BinaryTree._root_.Tree.numLeaves** 是 Mathlib 中的一个缩写定义，位于命名空间 `BinaryTree`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Alias** of `BinaryTree.numLeaves`.
-/
abbrev _root_.Tree.numLeaves {α} (t : Tree α) : ℕ := BinaryTree.numLeaves t

/-- The height - length of the longest path from the root - of a binary tree -/
@[simp]
/-
**BinaryTree.height** 是 Mathlib 中的一个定义，位于命名空间 `BinaryTree`。
形式化陈述：{α : Type u} → BinaryTree α → ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The height - length of the longest path from the root - of a binary tree
-/
def height : BinaryTree α → ℕ
  | nil => 0
  | node _ a b => max a.height b.height + 1

/-- **Alias** of `BinaryTree.height`. -/
@[deprecated BinaryTree.height (since := "2026-06-07")]
/-
**BinaryTree._root_.Tree.height** 是 Mathlib 中的一个缩写定义，位于命名空间 `BinaryTree`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Alias** of `BinaryTree.height`.
-/
abbrev _root_.Tree.height {α} (t : Tree α) : ℕ := BinaryTree.height t
/-
**BinaryTree.numLeaves_eq_numNodes_succ** 是 Mathlib 中的一个定理，位于命名空间 `BinaryTree`。
形式化陈述：numLeaves_eq_numNodes_succ (x : BinaryTree α) : x.numLeaves = x.numNodes +
 1
参数：x : BinaryTree α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.add_left_comm`：∀ (n m k : ℕ), n + (m + k) = m + (n + k)
· 使用定理 `Nat.add_comm`：∀ (n m : ℕ), n + m = m + n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.add_assoc`：∀ (n m k : ℕ), n + m + k = n + (m + k)
-/
theorem numLeaves_eq_numNodes_succ (x : BinaryTree α) : x.numLeaves = x.numNodes + 1 := by
  induction x <;> simp [*, Nat.add_comm, Nat.add_assoc, Nat.add_left_comm]
/-
**BinaryTree.numLeaves_pos** 是 Mathlib 中的一个定理，位于命名空间 `BinaryTree`。
形式化陈述：numLeaves_pos (x : BinaryTree α) : 0 < x.numLeaves
参数：x : BinaryTree α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BinaryTree.numLeaves_eq_numNodes_succ`：numLeaves_eq_numNodes_succ (x : B
inaryTree α) : x.numLeaves = x.numNodes + 1
· 使用定理 `Nat.zero_lt_succ`：∀ (n : ℕ), 0 < n.succ
-/
theorem numLeaves_pos (x : BinaryTree α) : 0 < x.numLeaves := by
  rw [numLeaves_eq_numNodes_succ]
  exact x.numNodes.zero_lt_succ
/-
**BinaryTree.height_le_numNodes** 是 Mathlib 中的一个定理，位于命名空间 `BinaryTree`。
形式化陈述：∀ {α : Type u} (x : BinaryTree α), x.height ≤ x.numNodes
参数：x : BinaryTree α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem height_le_numNodes : ∀ x : BinaryTree α, x.height ≤ x.numNodes
  | nil => Nat.le_refl _
  | node _ a b => Nat.succ_le_succ <|
    Nat.max_le.2 ⟨Nat.le_trans a.height_le_numNodes <| a.numNodes.le_add_right _,
      Nat.le_trans b.height_le_numNodes <| b.numNodes.le_add_left _⟩

/-- The left child of the tree, or `nil` if the tree is `nil` -/
@[simp]
/-
**BinaryTree.left** 是 Mathlib 中的一个定义，位于命名空间 `BinaryTree`。
形式化陈述：{α : Type u} → BinaryTree α → BinaryTree α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left child of the tree, or `nil` if the tree is `nil`
-/
def left : BinaryTree α → BinaryTree α
  | nil => nil
  | node _ l _r => l

/-- **Alias** of `BinaryTree.left`. -/
@[deprecated BinaryTree.left (since := "2026-06-07")]
/-
**BinaryTree._root_.Tree.left** 是 Mathlib 中的一个缩写定义，位于命名空间 `BinaryTree`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Alias** of `BinaryTree.left`.
-/
abbrev _root_.Tree.left {α} (t : Tree α) : Tree α := BinaryTree.left t

/-- The right child of the tree, or `nil` if the tree is `nil` -/
@[simp]
/-
**BinaryTree.right** 是 Mathlib 中的一个定义，位于命名空间 `BinaryTree`。
形式化陈述：{α : Type u} → BinaryTree α → BinaryTree α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The right child of the tree, or `nil` if the tree is `nil`
-/
def right : BinaryTree α → BinaryTree α
  | nil => nil
  | node _ _l r => r

/-- **Alias** of `BinaryTree.right`. -/
@[deprecated BinaryTree.right (since := "2026-06-07")]
/-
**BinaryTree._root_.Tree.right** 是 Mathlib 中的一个缩写定义，位于命名空间 `BinaryTree`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Alias** of `BinaryTree.right`.
-/
abbrev _root_.Tree.right {α} (t : Tree α) : Tree α := BinaryTree.right t

/-- A node with `Unit` data -/
scoped infixr:65 " △ " => BinaryTree.node ()

/-- Induction principle for `BinaryTree Unit`s -/
@[elab_as_elim]
/-
**BinaryTree.unitRecOn** 是 Mathlib 中的一个定义，位于命名空间 `BinaryTree`。
形式化陈述：unitRecOn {motive : BinaryTree Unit -> Sort*} (t : BinaryTree Unit) (base 
: motive nil) (ind : forall x y, motive x -> motive y -> motive (x △ y)) : motiv
e t
参数：t : BinaryTree Unit；base : motive nil；ind : forall x y, motive x -> motive y 
-> motive (x △ y)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Induction principle for `BinaryTree Unit`s
-/
def unitRecOn {motive : BinaryTree Unit → Sort*} (t : BinaryTree Unit) (base : motive nil)
    (ind : ∀ x y, motive x → motive y → motive (x △ y)) : motive t :=
  t.recOn base fun _u ↦ ind

/-- **Alias** of `BinaryTree.unitRecOn`. -/
@[deprecated BinaryTree.unitRecOn (since := "2026-06-07")]
/-
**BinaryTree._root_.Tree.unitRecOn** 是 Mathlib 中的一个缩写定义，位于命名空间 `BinaryTree`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Alias** of `BinaryTree.unitRecOn`.
-/
abbrev _root_.Tree.unitRecOn {motive : Tree Unit → Sort*} (t : Tree Unit) (base : motive nil)
    (ind : ∀ x y, motive x → motive y → motive (x △ y)) : motive t :=
  BinaryTree.unitRecOn t base ind
/-
**BinaryTree.left_node_right_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `BinaryTree`。
形式化陈述：∀ {x : BinaryTree Unit}, x ≠ BinaryTree.nil → BinaryTree.node () x.left x.
right = x
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem left_node_right_eq_self : ∀ {x : BinaryTree Unit} (_hx : x ≠ nil), x.left △ x.right = x
  | nil, h => by trivial
  | node _ _ _, _ => rfl  -- Porting note: `a △ b` no longer works in pattern matching

end BinaryTree

