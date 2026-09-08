/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Antoine Chambert-Loir
-/
module

public import Mathlib.Data.Prod.Lex
public import Mathlib.Order.SuccPred.Limit
public import Mathlib.Topology.Order.Basic
public import Mathlib.Order.UpperLower.CompleteLattice
public import Mathlib.Order.Completion

import Mathlib.Algebra.Order.Field.Basic

/-!
# Dense and continuous completion of a linear order

Let `α` be a linear order.

* `DedekindCut.continuous_principal`: the map `DedekindCut.principal : α → DedekindCut α`
  that embeds `α` in its Dedekind completion is continuous for the order topologies.
* `Order.Fill α`: this is a type with a dense linear order endowed
  with a continuous order-embedding `Order.Fill.some` of `α`.
  It is defined as a subtype of `α × ℚ` and its order is induced by the lexicographic order.
* `Order.Fill.some`: the order embedding `α ↪o Order.Fill α` given by `a ↦ (a, 0)`.
* `Order.Fill.continuous_some`: the map `⇑Order.Fill.some` is continuous for the order topologies.
* `Order.exists_dense_continuous_completion`: any linear order embeds continuously
  (for the order topologies) into a dense and complete linear order.
  The linearly ordered type provided by the proof is given by the Dedekind completion of
  `Order.Fill α`, although the user does not need to know that.
-/

@[expose] public section

open Set

variable {α : Type*} [LinearOrder α]

/-
**DedekindCut.continuous_principal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DedekindCut.continuous_principal [TopologicalSpace α] [OrderTopology α] [T
opologicalSpace (DedekindCut α)] [OrderTopology (DedekindCut α)] : Continuous (f
un a : α => principal a)
参数：DedekindCut α；DedekindCut α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderTopology.continuous_iff`：∀ {α : Type u} {β : Type v} [ts : Topologi
calSpace α] [inst : Preorder α] [OrderTopology α]   [inst_2 : TopologicalSpace β
] {f : β → α},   C…
· 使用定理 `isOpen_biUnion`：isOpen_biUnion {s : Set α} {f : α -> Set X} (h : forall 
i in s, IsOpen (f i)) : IsOpen (⋃ i in s, f i)
· 使用定理 `isOpen_Ioi`：isOpen_Ioi : IsOpen (Ioi a)
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `isOpen_Iio`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : LinearO
rder α] [ClosedIciTopology α] {a : α}, IsOpen (Set.Iio a)
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
-/
theorem DedekindCut.continuous_principal [TopologicalSpace α] [OrderTopology α]
    [TopologicalSpace (DedekindCut α)] [OrderTopology (DedekindCut α)] :
    Continuous (fun a : α ↦ principal a) := by
  rw [OrderTopology.continuous_iff]
  refine fun c ↦ ⟨?_, ?_⟩
  · have : IsOpen (⋃ a ∈ c.right, Ioi a) := isOpen_biUnion fun _ _ ↦ isOpen_Ioi
    convert this
    ext
    simp [lt_principal_iff]
  · have : IsOpen (⋃ a ∈ c.left, Iio a) := isOpen_biUnion fun _ _ ↦ isOpen_Iio
    convert this
    ext
    simp [principal_lt_iff]

namespace Order

/-- A dense linear order into which α embeds continuously, formed by "filling in" the blanks. -/
/-
**Order.Fill** 是 Mathlib 中的一个缩写定义，位于命名空间 `Order`。
形式化陈述：Fill (α : Type*) [LinearOrder α] : Type _
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A dense linear order into which α embeds continuously, formed by "filling in" th
e blanks.
-/
abbrev Fill (α : Type*) [LinearOrder α] : Type _ :=
  {x : α ×ₗ ℚ //
    (IsSuccPrelimit (ofLex x).1 → 0 ≤ (ofLex x).2) ∧
    (IsPredPrelimit (ofLex x).1 → (ofLex x).2 ≤ 0) }

namespace Fill

/-
**Order.Fill.** 是 Mathlib 中的一个实例，位于命名空间 `Order.Fill`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : TopologicalSpace (Fill α) := Preorder.topology _
/-
**Order.Fill.** 是 Mathlib 中的一个实例，位于命名空间 `Order.Fill`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OrderTopology (Fill α) := ⟨rfl⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- A continuous embedding of `α` into `Fill α`. -/
/-
**Order.Fill.some** 是 Mathlib 中的一个定义，位于命名空间 `Order.Fill`。
形式化陈述：some : α ↪o Fill α where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A continuous embedding of `α` into `Fill α`.
-/
def some : α ↪o Fill α where
  toFun x := ⟨toLex (x, 0), by simp⟩
  inj' _ := by simp
  map_rel_iff' := by simp [Prod.Lex.toLex_le_toLex']

set_option backward.isDefEq.respectTransparency.types false in
/-
**Order.Fill.** 是 Mathlib 中的一个实例，位于命名空间 `Order.Fill`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DenselyOrdered (Fill α) where
  dense := by
    simp only [ofLex_toLex, Subtype.forall, Prod.Lex.lt_iff, Subtype.mk_lt_mk,
      Lex.forall, Prod.forall]
    rintro x q ⟨hx₁, hx₂⟩ y r ⟨hy₁, hy₂⟩ (h | ⟨rfl, h⟩)
    · by_cases hx : IsPredPrelimit x
      · obtain ⟨z, hz, hz'⟩ := hx.lt_iff_exists_lt.1 h
        use some z
        simp [some, Prod.Lex.lt_iff, hz', hz]
      obtain ⟨s, hs⟩ := exists_gt (max 0 q)
      rw [max_lt_iff] at hs
      refine ⟨⟨toLex (x, s), ?_⟩, ?_⟩
      · simp [hx, hs.1.le]
      · simp [Prod.Lex.lt_iff, hs.2, h]
    · obtain ⟨s, hs, hs'⟩ := exists_between h
      refine ⟨⟨toLex (x, s), ?_⟩, ?_⟩
      · grind [ofLex_toLex]
      · simp [Prod.Lex.lt_iff, hs, hs']

set_option backward.isDefEq.respectTransparency.types false in
/-
**Order.Fill.continuous_some** 是 Mathlib 中的一个定理，位于命名空间 `Order.Fill`。
形式化陈述：continuous_some [TopologicalSpace α] [OrderTopology α] : Continuous (X
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Order.Fill.instOrderTopology`：∀ {α : Type u_1} [inst : LinearOrder α], O
rderTopology (Order.Fill α)
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `isOpen_Ioi`：isOpen_Ioi : IsOpen (Ioi a)
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Order.not_isSuccPrelimit_iff`：not_isSuccPrelimit_iff {a : α} : ¬IsSuccPr
elimit a ↔ exists b, b ⋖ a
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CovBy.le_iff_lt_right`：∀ {α : Type u_1} [inst : LinearOrder α] {x y : α}
, y ⋖ x → ∀ {z : α}, x ≤ z ↔ y < z
· 使用定理 `isOpen_Iio`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : LinearO
rder α] [ClosedIciTopology α] {a : α}, IsOpen (Set.Iio a)
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `Order.not_isPredPrelimit_iff`：∀ {α : Type u_1} [inst : LT α] {a : α}, ¬O
rder.IsPredPrelimit a ↔ ∃ b, a ⋖ b
· 使用定理 `CovBy.le_iff_lt_left`：∀ {α : Type u_1} [inst : LinearOrder α] {x y : α},
 x ⋖ y → ∀ {z : α}, z ≤ x ↔ z < y
-/
theorem continuous_some [TopologicalSpace α] [OrderTopology α] : Continuous (X := α) some := by
  simp only [OrderTopology.continuous_iff, ofLex_toLex, Subtype.forall, Lex.forall, Prod.forall]
  refine fun x q ⟨hx₁, hx₂⟩ ↦ ⟨?_, ?_⟩
  · obtain hq | hq := le_or_gt 0 q
    · convert isOpen_Ioi (a := x)
      ext
      simp [some, Prod.Lex.lt_iff, hq.not_gt]
    · obtain ⟨y, hy⟩ := not_isSuccPrelimit_iff.1 <| mt hx₁ hq.not_ge
      convert isOpen_Ioi (a := y)
      ext
      simpa [some, Prod.Lex.lt_iff, hq, le_iff_lt_or_eq] using hy.le_iff_lt_right
  · obtain hq | hq := le_or_gt q 0
    · convert isOpen_Iio (a := x)
      ext
      simp [some, Prod.Lex.lt_iff, hq.not_gt]
    · obtain ⟨y, hy⟩ := not_isPredPrelimit_iff.1 <| mt hx₂ hq.not_ge
      convert isOpen_Iio (a := y)
      ext
      simpa [some, Prod.Lex.lt_iff, hq, le_iff_lt_or_eq] using hy.le_iff_lt_left

end Fill

universe u

/-- Every linear order embeds continuously in a dense complete linear order. -/
/-
**Order.exists_dense_continuous_completion** 是 Mathlib 中的一个定理，位于命名空间 `Order`。
形式化陈述：exists_dense_continuous_completion (α : Type u) [LinearOrder α] [Topologic
alSpace α] [OrderTopology α] : exists (β : Type u) (_ : CompleteLinearOrder β) (
_ : DenselyOrdered β) (_ : TopologicalSpace β) (_ : OrderTopology β) (ι : α ↪o β
), Continuous ι
参数：α : Type u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DedekindCut.instDenselyOrdered`：∀ {α : Type u_1} [inst : LinearOrder α] 
[DenselyOrdered α], DenselyOrdered (DedekindCut α)
· 使用定理 `Order.Fill.instDenselyOrdered`：∀ {α : Type u_1} [inst : LinearOrder α], 
DenselyOrdered (Order.Fill α)
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `DedekindCut.continuous_principal`：DedekindCut.continuous_principal [Topo
logicalSpace α] [OrderTopology α] [TopologicalSpace (DedekindCut α)] [OrderTopol
ogy (DedekindCut α)] :…
· 使用定理 `Order.Fill.instOrderTopology`：∀ {α : Type u_1} [inst : LinearOrder α], O
rderTopology (Order.Fill α)
· 使用定理 `Order.Fill.continuous_some`：continuous_some [TopologicalSpace α] [OrderT
opology α] : Continuous (X

--- 原说明 ---
Every linear order embeds continuously in a dense complete linear order.
-/
theorem exists_dense_continuous_completion
    (α : Type u) [LinearOrder α] [TopologicalSpace α] [OrderTopology α] :
    ∃ (β : Type u) (_ : CompleteLinearOrder β) (_ : DenselyOrdered β) (_ : TopologicalSpace β)
      (_ : OrderTopology β) (ι : α ↪o β), Continuous ι :=
  let : TopologicalSpace (DedekindCut (Fill α)) := Preorder.topology _
  have : OrderTopology (DedekindCut (Fill α)) := ⟨rfl⟩
  ⟨_, inferInstance, inferInstance, inferInstance, inferInstance,
    Fill.some.trans DedekindCut.principalEmbedding,
    DedekindCut.continuous_principal.comp Fill.continuous_some⟩

end Order

