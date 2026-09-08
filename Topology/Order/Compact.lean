/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Yury Kudryashov
-/
module

public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Order.IsLUB
public import Mathlib.Topology.Order.LocalExtr

/-!
# Compactness of a closed interval

In this file we prove that a closed interval in a conditionally complete linear ordered type with
order topology (or a product of such types) is compact.

We prove the extreme value theorem (`IsCompact.exists_isMinOn`, `IsCompact.exists_isMaxOn`):
a continuous function on a compact set takes its minimum and maximum values. We provide many
variations of this theorem.

We also prove that the image of a closed interval under a continuous map is a closed interval, see
`ContinuousOn.image_Icc`.

## Tags

compact, extreme value theorem
-/

public section

open Filter OrderDual TopologicalSpace Function Set

open scoped Filter Topology

/-!
### Compactness of a closed interval

In this section we define a typeclass `CompactIccSpace α` saying that all closed intervals in `α`
are compact. Then we provide an instance for a `ConditionallyCompleteLinearOrder` and prove that
the product (both `α × β` and an indexed product) of spaces with this property inherits the
property.

We also prove some simple lemmas about spaces with this property.
-/


/-- This typeclass says that all closed intervals in `α` are compact. This is true for all
conditionally complete linear orders with order topology and products (finite or infinite)
of such spaces. -/
/-
**CompactIccSpace** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_1) → [TopologicalSpace α] → [Preorder α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This typeclass says that all closed intervals in `α` are compact. This is true f
or all
conditionally complete linear orders with order topology and products (finite or
 infinite)
of such spaces.
-/
class CompactIccSpace (α : Type*) [TopologicalSpace α] [Preorder α] : Prop where
  /-- A closed interval `Set.Icc a b` is a compact set for all `a` and `b`. -/
  isCompact_Icc : ∀ {a b : α}, IsCompact (Icc a b)

export CompactIccSpace (isCompact_Icc)
attribute [compactness .] isCompact_Icc

variable {α : Type*}

-- TODO: make it the definition
/-
**CompactIccSpace.mk'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CompactIccSpace.mk' [TopologicalSpace α] [Preorder α] (h : forall {a b : α
}, a <= b -> IsCompact (Icc a b)) : CompactIccSpace α where isCompact_Icc {a b}
参数：h : forall {a b : α}, a <= b -> IsCompact (Icc a b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `by_cases`：by_cases {p q : Prop} (hpq : p -> q) (hnpq : ¬p -> q) : q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Icc_eq_empty`：Icc_eq_empty (h : ¬a <= b) : Icc a b = ∅
· 使用定理 `isCompact_empty`：isCompact_empty : IsCompact (∅ : Set X)
-/
lemma CompactIccSpace.mk' [TopologicalSpace α] [Preorder α]
    (h : ∀ {a b : α}, a ≤ b → IsCompact (Icc a b)) : CompactIccSpace α where
  isCompact_Icc {a b} := by_cases h fun hab => by rw [Icc_eq_empty hab]; exact isCompact_empty

-- TODO: drop one `'`
/-
**CompactIccSpace.mk''** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CompactIccSpace.mk'' [TopologicalSpace α] [PartialOrder α] (h : forall {a 
b : α}, a < b -> IsCompact (Icc a b)) : CompactIccSpace α
参数：h : forall {a b : α}, a < b -> IsCompact (Icc a b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CompactIccSpace.mk'`：CompactIccSpace.mk' [TopologicalSpace α] [Preorder 
α] (h : forall {a b : α}, a <= b -> IsCompact (Icc a b)) : CompactIccSpace α whe
re isComp…
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Icc_self`：Icc_self (a : α) : Icc a a = {a}
-/
lemma CompactIccSpace.mk'' [TopologicalSpace α] [PartialOrder α]
    (h : ∀ {a b : α}, a < b → IsCompact (Icc a b)) : CompactIccSpace α :=
  .mk' fun hab => hab.eq_or_lt.elim (by rintro rfl; simp) h
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [TopologicalSpace α] [Preorder α] [CompactIccSpace α] : CompactIccSpace (αᵒᵈ) where
  isCompact_Icc := by
    intro a b
    convert! isCompact_Icc (α := α) (a := b) (b := a) using 1
    exact Icc_toDual (α := α)

/-- A closed interval in a conditionally complete linear order is compact. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A closed interval in a conditionally complete linear order is compact.
-/
instance (priority := 100) ConditionallyCompleteLinearOrder.toCompactIccSpace (α : Type*)
    [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α] :
    CompactIccSpace α := ⟨fun {_ _} ↦ ConditionallyCompleteLinearOrder.isCompact_Icc _ _⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {ι : Type*} {α : ι → Type*} [∀ i, Preorder (α i)] [∀ i, TopologicalSpace (α i)]
    [∀ i, CompactIccSpace (α i)] : CompactIccSpace (∀ i, α i) :=
  ⟨fun {a b} => (pi_univ_Icc a b ▸ isCompact_univ_pi) fun _ => isCompact_Icc⟩
/-
**Pi.compact_Icc_space'** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.compact_Icc_space' {α β : Type*} [Preorder β] [TopologicalSpace β] [Com
pactIccSpace β] : CompactIccSpace (α -> β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `instCompactIccSpaceForall`：∀ {ι : Type u_2} {α : ι → Type u_3} [inst : (
i : ι) → Preorder (α i)] [inst_1 : (i : ι) → TopologicalSpace (α i)]   [∀ (i : ι
), CompactIccSp…
-/
instance Pi.compact_Icc_space' {α β : Type*} [Preorder β] [TopologicalSpace β]
    [CompactIccSpace β] : CompactIccSpace (α → β) :=
  inferInstance
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α β : Type*} [Preorder α] [TopologicalSpace α] [CompactIccSpace α] [Preorder β]
    [TopologicalSpace β] [CompactIccSpace β] : CompactIccSpace (α × β) :=
  ⟨fun {a b} => (Icc_prod_eq a b).symm ▸ isCompact_Icc.prod isCompact_Icc⟩

/-- An unordered closed interval is compact. -/
@[compactness .]
/-
**isCompact_uIcc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCompact_uIcc {α : Type*} [LinearOrder α] [TopologicalSpace α] [CompactIc
cSpace α] {a b : α} : IsCompact (uIcc a b)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompactIccSpace.isCompact_Icc`：∀ {α : Type u_1} {inst : TopologicalSpace
 α} {inst_1 : Preorder α} [self : CompactIccSpace α] {a b : α},   IsCompact (Set
.Icc a b)

--- 原说明 ---
An unordered closed interval is compact.
-/
theorem isCompact_uIcc {α : Type*} [LinearOrder α] [TopologicalSpace α] [CompactIccSpace α]
    {a b : α} : IsCompact (uIcc a b) :=
  isCompact_Icc

-- See note [lower instance priority]
/-- A complete linear order is a compact space.

We do not register an instance for a `[CompactIccSpace α]` because this would only add instances
for products (indexed or not) of complete linear orders, and we have instances with higher priority
that cover these cases. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A complete linear order is a compact space.

We do not register an instance for a `[CompactIccSpace α]` because this would on
ly add instances
for products (indexed or not) of complete linear orders, and we have instances w
ith higher priority
that cover these cases.
-/
instance (priority := 100) compactSpace_of_completeLinearOrder {α : Type*} [CompleteLinearOrder α]
    [TopologicalSpace α] [OrderTopology α] : CompactSpace α :=
  ⟨by simp only [← Icc_bot_top, isCompact_Icc]⟩

section

variable {α : Type*} [Preorder α] [TopologicalSpace α] [CompactIccSpace α]

/-
**compactSpace_Icc** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：compactSpace_Icc (a b : α) : CompactSpace (Icc a b)
参数：a b : α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isCompact_iff_compactSpace`：isCompact_iff_compactSpace : IsCompact s ↔ C
ompactSpace s
· 使用定理 `CompactIccSpace.isCompact_Icc`：∀ {α : Type u_1} {inst : TopologicalSpace
 α} {inst_1 : Preorder α} [self : CompactIccSpace α] {a b : α},   IsCompact (Set
.Icc a b)
-/
instance compactSpace_Icc (a b : α) : CompactSpace (Icc a b) :=
  isCompact_iff_compactSpace.mp isCompact_Icc

end

section openIntervals
variable {α : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α]

/-- `Set.Ico a b` is only compact if it is empty. -/
@[simp]
/-
**isCompact_Ico_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCompact_Ico_iff {a b : α} : IsCompact (Set.Ico a b) ↔ b <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isClosed_Ico_iff`：isClosed_Ico_iff {a b : α} : IsClosed (Set.Ico a b) ↔ 
b <= a
· 使用定理 `IsCompact.isClosed`：IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsC
ompact s) : IsClosed s
· 使用定理 `OrderClosedTopology.to_t2Space`：∀ {α : Type u} [inst : TopologicalSpace 
α] [inst_1 : PartialOrder α] [t : OrderClosedTopology α], T2Space α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Ico_eq_empty`：Ico_eq_empty (h : ¬a < b) : Ico a b = ∅
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
`Set.Ico a b` is only compact if it is empty.
-/
theorem isCompact_Ico_iff {a b : α} : IsCompact (Set.Ico a b) ↔ b ≤ a :=
  ⟨fun h => isClosed_Ico_iff.mp h.isClosed, by simp_all⟩

/-- `Set.Ioc a b` is only compact if it is empty. -/
@[simp]
/-
**isCompact_Ioc_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCompact_Ioc_iff {a b : α} : IsCompact (Set.Ioc a b) ↔ b <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isClosed_Ioc_iff`：isClosed_Ioc_iff {a b : α} : IsClosed (Set.Ioc a b) ↔ 
b <= a
· 使用定理 `IsCompact.isClosed`：IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsC
ompact s) : IsClosed s
· 使用定理 `OrderClosedTopology.to_t2Space`：∀ {α : Type u} [inst : TopologicalSpace 
α] [inst_1 : PartialOrder α] [t : OrderClosedTopology α], T2Space α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Ioc_eq_empty`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, ¬b < a
 → Set.Ioc b a = ∅
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
`Set.Ioc a b` is only compact if it is empty.
-/
theorem isCompact_Ioc_iff {a b : α} : IsCompact (Set.Ioc a b) ↔ b ≤ a :=
  ⟨fun h => isClosed_Ioc_iff.mp h.isClosed, by simp_all⟩

/-- `Set.Ioo a b` is only compact if it is empty. -/
@[simp]
/-
**isCompact_Ioo_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCompact_Ioo_iff {a b : α} : IsCompact (Set.Ioo a b) ↔ b <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isClosed_Ioo_iff`：isClosed_Ioo_iff {a b : α} : IsClosed (Set.Ioo a b) ↔ 
b <= a
· 使用定理 `IsCompact.isClosed`：IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsC
ompact s) : IsClosed s
· 使用定理 `OrderClosedTopology.to_t2Space`：∀ {α : Type u} [inst : TopologicalSpace 
α] [inst_1 : PartialOrder α] [t : OrderClosedTopology α], T2Space α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Ioo_eq_empty`：Ioo_eq_empty (h : ¬a < b) : Ioo a b = ∅
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
`Set.Ioo a b` is only compact if it is empty.
-/
theorem isCompact_Ioo_iff {a b : α} : IsCompact (Set.Ioo a b) ↔ b ≤ a :=
  ⟨fun h => isClosed_Ioo_iff.mp h.isClosed, by simp_all⟩

end openIntervals

/-!
### Extreme value theorem
-/

section LinearOrder

variable {α β γ : Type*} [LinearOrder α] [TopologicalSpace α]
  [TopologicalSpace β] [TopologicalSpace γ]

/-
**IsCompact.exists_isLeast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.exists_isLeast [ClosedIicTopology α] {s : Set α} (hs : IsCompact
 s) (ne_s : s.Nonempty) : exists x, IsLeast s x
参数：hs : IsCompact s；ne_s : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.to_subtype`：∀ {α : Type u} {s : Set α}, s.Nonempty → Nonemp
ty ↑s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.biInter_eq_iInter`：biInter_eq_iInter (s : Set α) (t : forall x in s,
 Set β) : ⋂ x in s, t x ‹_› = ⋂ x : s, t x x.2
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `IsCompact.elim_directed_family_closed`：IsCompact.elim_directed_family_cl
osed {ι : Type v} [Nonempty ι] (hs : IsCompact s) (t : ι -> Set X) (htc : forall
 i, IsClosed (t i)) (hst : …
· 使用定理 `isClosed_Iic`：isClosed_Iic : IsClosed (Iic a)
· 使用定理 `Set.not_nonempty_iff_eq_empty`：not_nonempty_iff_eq_empty : ¬s.Nonempty ↔
 s = ∅
· 使用定理 `Monotone.directed_ge`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α
] [IsCodirectedOrder α] [inst_2 : Preorder β] {f : α → β},   Monotone f → Direct
ed (fun x1…
· 使用定理 `SemilatticeInf.instIsCodirectedOrder`：∀ {α : Type u_1} [inst : Semilatti
ceInf α], IsCodirectedOrder α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Iic_subset_Iic`：Iic_subset_Iic : Iic a subseteq Iic b ↔ a <= b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_iInter₂`：mem_iInter₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋂ (i) (j), s i j) ↔ forall i j, x in s i j
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IsCompact.exists_isLeast [ClosedIicTopology α] {s : Set α} (hs : IsCompact s)
    (ne_s : s.Nonempty) : ∃ x, IsLeast s x := by
  have : Nonempty s := ne_s.to_subtype
  suffices (s ∩ ⋂ x ∈ s, Iic x).Nonempty from
    ⟨this.choose, this.choose_spec.1, mem_iInter₂.mp this.choose_spec.2⟩
  rw [biInter_eq_iInter]
  by_contra H
  rw [not_nonempty_iff_eq_empty] at H
  rcases hs.elim_directed_family_closed (fun x : s => Iic ↑x) (fun x => isClosed_Iic) H
      (Monotone.directed_ge fun _ _ h => Iic_subset_Iic.mpr h) with ⟨x, hx⟩
  exact not_nonempty_iff_eq_empty.mpr hx ⟨x, x.2, le_rfl⟩
/-
**IsCompact.exists_isGreatest** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.exists_isGreatest [ClosedIciTopology α] {s : Set α} (hs : IsComp
act s) (ne_s : s.Nonempty) : exists x, IsGreatest s x
参数：hs : IsCompact s；ne_s : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.exists_isLeast`：IsCompact.exists_isLeast [ClosedIicTopology α]
 {s : Set α} (hs : IsCompact s) (ne_s : s.Nonempty) : exists x, IsLeast s x
· 使用定理 `instClosedIicTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpace 
α] [inst_1 : Preorder α] [ClosedIciTopology α], ClosedIicTopology αᵒᵈ
-/
theorem IsCompact.exists_isGreatest [ClosedIciTopology α] {s : Set α} (hs : IsCompact s)
    (ne_s : s.Nonempty) : ∃ x, IsGreatest s x :=
  IsCompact.exists_isLeast (α := αᵒᵈ) hs ne_s
/-
**IsCompact.exists_isGLB** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.exists_isGLB [ClosedIicTopology α] {s : Set α} (hs : IsCompact s
) (ne_s : s.Nonempty) : exists x in s, IsGLB s x
参数：hs : IsCompact s；ne_s : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `IsLeast.isGLB`：IsLeast.isGLB (h : IsLeast s a) : IsGLB s a
· 使用定理 `IsCompact.exists_isLeast`：IsCompact.exists_isLeast [ClosedIicTopology α]
 {s : Set α} (hs : IsCompact s) (ne_s : s.Nonempty) : exists x, IsLeast s x
-/
theorem IsCompact.exists_isGLB [ClosedIicTopology α] {s : Set α} (hs : IsCompact s)
    (ne_s : s.Nonempty) : ∃ x ∈ s, IsGLB s x :=
  (hs.exists_isLeast ne_s).imp (fun x (hx : IsLeast s x) => ⟨hx.1, hx.isGLB⟩)
/-
**IsCompact.exists_isLUB** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.exists_isLUB [ClosedIciTopology α] {s : Set α} (hs : IsCompact s
) (ne_s : s.Nonempty) : exists x in s, IsLUB s x
参数：hs : IsCompact s；ne_s : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.exists_isGLB`：IsCompact.exists_isGLB [ClosedIicTopology α] {s 
: Set α} (hs : IsCompact s) (ne_s : s.Nonempty) : exists x in s, IsGLB s x
· 使用定理 `instClosedIicTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpace 
α] [inst_1 : Preorder α] [ClosedIciTopology α], ClosedIicTopology αᵒᵈ
-/
theorem IsCompact.exists_isLUB [ClosedIciTopology α] {s : Set α} (hs : IsCompact s)
    (ne_s : s.Nonempty) : ∃ x ∈ s, IsLUB s x :=
  IsCompact.exists_isGLB (α := αᵒᵈ) hs ne_s
/-
**cocompact_le_atBot_atTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cocompact_le_atBot_atTop [CompactIccSpace α] : cocompact α <= atBot ⊔ atTo
p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.mem_cocompact`：mem_cocompact : s in cocompact X ↔ exists t, IsCom
pact t ∧ tᶜ subseteq s
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `isCompact_empty`：isCompact_empty : IsCompact (∅ : Set X)
· 使用定理 `IsEmpty.false`：∀ {α : Sort u} [self : IsEmpty α] (a : α), False
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.mem_atBot_sets`：∀ {α : Type u_3} [inst : Preorder α] [IsCodirecte
dOrder α] [Nonempty α] {s : Set α},   s ∈ Filter.atBot ↔ ∃ a, ∀ b ≤ a, b ∈ s
· 使用定理 `SemilatticeInf.instIsCodirectedOrder`：∀ {α : Type u_1} [inst : Semilatti
ceInf α], IsCodirectedOrder α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `Filter.mem_atTop_sets`：mem_atTop_sets {s : Set α} : s in (atTop : Filter
 α) ↔ exists a : α, forall b, a <= b -> b in s
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `CompactIccSpace.isCompact_Icc`：∀ {α : Type u_1} {inst : TopologicalSpace
 α} {inst_1 : Preorder α} [self : CompactIccSpace α] {a b : α},   IsCompact (Set
.Icc a b)
· 使用定理 `not_and_or`：not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b
· 使用定理 `le_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b 
→ b ≤ a
-/
theorem cocompact_le_atBot_atTop [CompactIccSpace α] :
    cocompact α ≤ atBot ⊔ atTop := by
  refine fun s hs ↦ mem_cocompact.mpr <| (isEmpty_or_nonempty α).casesOn ?_ ?_ <;> intro
  · exact ⟨∅, isCompact_empty, fun x _ ↦ (IsEmpty.false x).elim⟩
  · obtain ⟨t, ht⟩ := mem_atBot_sets.mp hs.1
    obtain ⟨u, hu⟩ := mem_atTop_sets.mp hs.2
    refine ⟨Icc t u, isCompact_Icc, fun x hx ↦ ?_⟩
    exact (not_and_or.mp hx).casesOn (fun h ↦ ht x (le_of_not_ge h)) fun h ↦ hu x (le_of_not_ge h)
/-
**cocompact_le_atBot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cocompact_le_atBot [OrderTop α] [CompactIccSpace α] : cocompact α <= atBot
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.mem_cocompact`：mem_cocompact : s in cocompact X ↔ exists t, IsCom
pact t ∧ tᶜ subseteq s
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `isCompact_empty`：isCompact_empty : IsCompact (∅ : Set X)
· 使用定理 `IsEmpty.false`：∀ {α : Sort u} [self : IsEmpty α] (a : α), False
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.mem_atBot_sets`：∀ {α : Type u_3} [inst : Preorder α] [IsCodirecte
dOrder α] [Nonempty α] {s : Set α},   s ∈ Filter.atBot ↔ ∃ a, ∀ b ≤ a, b ∈ s
· 使用定理 `SemilatticeInf.instIsCodirectedOrder`：∀ {α : Type u_1} [inst : Semilatti
ceInf α], IsCodirectedOrder α
· 使用定理 `CompactIccSpace.isCompact_Icc`：∀ {α : Type u_1} {inst : TopologicalSpace
 α} {inst_1 : Preorder α} [self : CompactIccSpace α] {a b : α},   IsCompact (Set
.Icc a b)
· 使用定理 `not_and_or`：not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b
· 使用定理 `le_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b 
→ b ≤ a
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem cocompact_le_atBot [OrderTop α] [CompactIccSpace α] :
    cocompact α ≤ atBot := by
  refine fun _ hs ↦ mem_cocompact.mpr <| (isEmpty_or_nonempty α).casesOn ?_ ?_ <;> intro
  · exact ⟨∅, isCompact_empty, fun x _ ↦ (IsEmpty.false x).elim⟩
  · obtain ⟨t, ht⟩ := mem_atBot_sets.mp hs
    refine ⟨Icc t ⊤, isCompact_Icc, fun _ hx ↦ ?_⟩
    exact (not_and_or.mp hx).casesOn (fun h ↦ ht _ (le_of_not_ge h)) (fun h ↦ (h le_top).elim)
/-
**cocompact_le_atTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cocompact_le_atTop [OrderBot α] [CompactIccSpace α] : cocompact α <= atTop
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `cocompact_le_atBot`：cocompact_le_atBot [OrderTop α] [CompactIccSpace α] 
: cocompact α <= atBot
· 使用定理 `instCompactIccSpaceOrderDual`：∀ {α : Type u_1} [inst : TopologicalSpace 
α] [inst_1 : Preorder α] [CompactIccSpace α], CompactIccSpace αᵒᵈ
-/
theorem cocompact_le_atTop [OrderBot α] [CompactIccSpace α] :
    cocompact α ≤ atTop :=
  cocompact_le_atBot (α := αᵒᵈ)
/-
**atBot_le_cocompact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：atBot_le_cocompact [NoMinOrder α] [ClosedIicTopology α] : atBot <= cocompa
ct α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.mem_cocompact`：mem_cocompact : s in cocompact X ↔ exists t, IsCom
pact t ∧ tᶜ subseteq s
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.univ_subset_iff`：univ_subset_iff {s : Set α} : univ subseteq s ↔ s =
 univ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.compl_univ_iff`：compl_univ_iff {s : Set α} : sᶜ = univ ↔ s = ∅
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
· 使用定理 `Exists.nonempty`：∀ {α : Sort u_1} {p : α → Prop}, (∃ x, p x) → Nonempty 
α
· 使用定理 `IsCompact.exists_isLeast`：IsCompact.exists_isLeast [ClosedIicTopology α]
 {s : Set α} (hs : IsCompact s) (ne_s : s.Nonempty) : exists x, IsLeast s x
· 使用定理 `NoMinOrder.exists_lt`：∀ {α : Type u_3} {inst : LT α} [self : NoMinOrder 
α] (a : α), ∃ b, b < a
· 使用定理 `Filter.mem_atBot_sets`：∀ {α : Type u_3} [inst : Preorder α] [IsCodirecte
dOrder α] [Nonempty α] {s : Set α},   s ∈ Filter.atBot ↔ ∃ a, ∀ b ≤ a, b ∈ s
· 使用定理 `SemilatticeInf.instIsCodirectedOrder`：∀ {α : Type u_1} [inst : Semilatti
ceInf α], IsCodirectedOrder α
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `LT.lt.false`：∀ {α : Type u_2} [inst : Preorder α] {a : α}, a < a → False
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.not_notMem`：not_notMem : ¬a ∉ s ↔ a in s
-/
theorem atBot_le_cocompact [NoMinOrder α] [ClosedIicTopology α] :
    atBot ≤ cocompact α := by
  refine fun s hs ↦ ?_
  obtain ⟨t, ht, hts⟩ := mem_cocompact.mp hs
  refine (Set.eq_empty_or_nonempty t).casesOn (fun h_empty ↦ ?_) (fun h_nonempty ↦ ?_)
  · rewrite [compl_univ_iff.mpr h_empty, univ_subset_iff] at hts
    convert! univ_mem
  · have := h_nonempty.nonempty
    obtain ⟨a, ha⟩ := ht.exists_isLeast h_nonempty
    obtain ⟨b, hb⟩ := exists_lt a
    exact Filter.mem_atBot_sets.mpr ⟨b, fun b' hb' ↦ hts <| Classical.byContradiction
      fun hc ↦ LT.lt.false <| hb'.trans_lt <| hb.trans_le <| ha.2 (not_notMem.mp hc)⟩
/-
**atTop_le_cocompact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：atTop_le_cocompact [NoMaxOrder α] [ClosedIciTopology α] : atTop <= cocompa
ct α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `atBot_le_cocompact`：atBot_le_cocompact [NoMinOrder α] [ClosedIicTopology
 α] : atBot <= cocompact α
· 使用定理 `instClosedIicTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpace 
α] [inst_1 : Preorder α] [ClosedIciTopology α], ClosedIicTopology αᵒᵈ
-/
theorem atTop_le_cocompact [NoMaxOrder α] [ClosedIciTopology α] :
    atTop ≤ cocompact α :=
  atBot_le_cocompact (α := αᵒᵈ)
/-
**atBot_atTop_le_cocompact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：atBot_atTop_le_cocompact [NoMinOrder α] [NoMaxOrder α] [OrderClosedTopolog
y α] : atBot ⊔ atTop <= cocompact α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `atBot_le_cocompact`：atBot_le_cocompact [NoMinOrder α] [ClosedIicTopology
 α] : atBot <= cocompact α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `atTop_le_cocompact`：atTop_le_cocompact [NoMaxOrder α] [ClosedIciTopology
 α] : atTop <= cocompact α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
-/
theorem atBot_atTop_le_cocompact [NoMinOrder α] [NoMaxOrder α]
    [OrderClosedTopology α] : atBot ⊔ atTop ≤ cocompact α :=
  sup_le atBot_le_cocompact atTop_le_cocompact

@[simp 900]
/-
**cocompact_eq_atBot_atTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cocompact_eq_atBot_atTop [NoMaxOrder α] [NoMinOrder α] [OrderClosedTopolog
y α] [CompactIccSpace α] : cocompact α = atBot ⊔ atTop
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `cocompact_le_atBot_atTop`：cocompact_le_atBot_atTop [CompactIccSpace α] :
 cocompact α <= atBot ⊔ atTop
· 使用定理 `atBot_atTop_le_cocompact`：atBot_atTop_le_cocompact [NoMinOrder α] [NoMax
Order α] [OrderClosedTopology α] : atBot ⊔ atTop <= cocompact α
-/
theorem cocompact_eq_atBot_atTop [NoMaxOrder α] [NoMinOrder α]
    [OrderClosedTopology α] [CompactIccSpace α] : cocompact α = atBot ⊔ atTop :=
  cocompact_le_atBot_atTop.antisymm atBot_atTop_le_cocompact

@[simp]
/-
**cocompact_eq_atBot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cocompact_eq_atBot [NoMinOrder α] [OrderTop α] [ClosedIicTopology α] [Comp
actIccSpace α] : cocompact α = atBot
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `cocompact_le_atBot`：cocompact_le_atBot [OrderTop α] [CompactIccSpace α] 
: cocompact α <= atBot
· 使用定理 `atBot_le_cocompact`：atBot_le_cocompact [NoMinOrder α] [ClosedIicTopology
 α] : atBot <= cocompact α
-/
theorem cocompact_eq_atBot [NoMinOrder α] [OrderTop α]
    [ClosedIicTopology α] [CompactIccSpace α] : cocompact α = atBot :=
  cocompact_le_atBot.antisymm atBot_le_cocompact

@[simp]
/-
**cocompact_eq_atTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cocompact_eq_atTop [NoMaxOrder α] [OrderBot α] [ClosedIciTopology α] [Comp
actIccSpace α] : cocompact α = atTop
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `cocompact_le_atTop`：cocompact_le_atTop [OrderBot α] [CompactIccSpace α] 
: cocompact α <= atTop
· 使用定理 `atTop_le_cocompact`：atTop_le_cocompact [NoMaxOrder α] [ClosedIciTopology
 α] : atTop <= cocompact α
-/
theorem cocompact_eq_atTop [NoMaxOrder α] [OrderBot α]
    [ClosedIciTopology α] [CompactIccSpace α] : cocompact α = atTop :=
  cocompact_le_atTop.antisymm atTop_le_cocompact

/-- The **extreme value theorem**: a continuous function realizes its minimum on a compact set. -/
/-
**IsCompact.exists_isMinOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.exists_isMinOn [ClosedIicTopology α] {s : Set β} (hs : IsCompact
 s) (ne_s : s.Nonempty) {f : β -> α} (hf : ContinuousOn f s) : exists x in s, Is
MinOn f s x
参数：hs : IsCompact s；ne_s : s.Nonempty；hf : ContinuousOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.exists_isLeast`：IsCompact.exists_isLeast [ClosedIicTopology α]
 {s : Set α} (hs : IsCompact s) (ne_s : s.Nonempty) : exists x, IsLeast s x
· 使用定理 `IsCompact.image_of_continuousOn`：IsCompact.image_of_continuousOn {f : X 
-> Y} (hs : IsCompact s) (hf : ContinuousOn f s) : IsCompact (f '' s)
· 使用定理 `Set.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set
 α}, s.Nonempty → (f '' s).Nonempty
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.forall_mem_image`：forall_mem_image {f : α -> β} {s : Set α} {p : β -
> Prop} : (forall y in f '' s, p y) ↔ forall ⦃x⦄, x in s -> p (f x)
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s

--- 原说明 ---
The **extreme value theorem**: a continuous function realizes its minimum on a c
ompact set.
-/
theorem IsCompact.exists_isMinOn [ClosedIicTopology α] {s : Set β} (hs : IsCompact s)
    (ne_s : s.Nonempty) {f : β → α} (hf : ContinuousOn f s) : ∃ x ∈ s, IsMinOn f s x := by
  rcases (hs.image_of_continuousOn hf).exists_isLeast (ne_s.image f) with ⟨_, ⟨x, hxs, rfl⟩, hx⟩
  refine ⟨x, hxs, forall_mem_image.1 (fun _ hb => hx <| mem_image_of_mem f ?_)⟩
  rwa [(image_id' s).symm]

/-- If a continuous function lies strictly above `a` on a compact set,
  it has a lower bound strictly above `a`. -/
/-
**IsCompact.exists_forall_le'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.exists_forall_le' [ClosedIicTopology α] [NoMaxOrder α] {f : β ->
 α} {s : Set β} (hs : IsCompact s) (hf : ContinuousOn f s) {a : α} (hf' : forall
 b in s, a < f b) : exists a', a < a' ∧ forall b in s, a' <= f b
参数：hs : IsCompact s；hf : ContinuousOn f s；hf' : forall b in s, a < f b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `NoMaxOrder.exists_gt`：∀ {α : Type u_3} {inst : LT α} [self : NoMaxOrder 
α] (a : α), ∃ b, a < b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsCompact.exists_isMinOn`：IsCompact.exists_isMinOn [ClosedIicTopology α]
 {s : Set β} (hs : IsCompact s) (ne_s : s.Nonempty) {f : β -> α} (hf : Continuou
sOn f s) : exi…

--- 原说明 ---
If a continuous function lies strictly above `a` on a compact set,
  it has a lower bound strictly above `a`.
-/
theorem IsCompact.exists_forall_le' [ClosedIicTopology α] [NoMaxOrder α] {f : β → α}
    {s : Set β} (hs : IsCompact s) (hf : ContinuousOn f s) {a : α} (hf' : ∀ b ∈ s, a < f b) :
    ∃ a', a < a' ∧ ∀ b ∈ s, a' ≤ f b := by
  rcases s.eq_empty_or_nonempty with (rfl | hs')
  · obtain ⟨a', ha'⟩ := exists_gt a
    exact ⟨a', ha', fun _ a ↦ a.elim⟩
  · obtain ⟨x, hx, hx'⟩ := hs.exists_isMinOn hs' hf
    exact ⟨f x, hf' x hx, hx'⟩

/-- The **extreme value theorem**: a continuous function realizes its maximum on a compact set. -/
/-
**IsCompact.exists_isMaxOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.exists_isMaxOn [ClosedIciTopology α] {s : Set β} (hs : IsCompact
 s) (ne_s : s.Nonempty) {f : β -> α} (hf : ContinuousOn f s) : exists x in s, Is
MaxOn f s x
参数：hs : IsCompact s；ne_s : s.Nonempty；hf : ContinuousOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.exists_isMinOn`：IsCompact.exists_isMinOn [ClosedIicTopology α]
 {s : Set β} (hs : IsCompact s) (ne_s : s.Nonempty) {f : β -> α} (hf : Continuou
sOn f s) : exi…
· 使用定理 `instClosedIicTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpace 
α] [inst_1 : Preorder α] [ClosedIciTopology α], ClosedIicTopology αᵒᵈ

--- 原说明 ---
The **extreme value theorem**: a continuous function realizes its maximum on a c
ompact set.
-/
theorem IsCompact.exists_isMaxOn [ClosedIciTopology α] {s : Set β} (hs : IsCompact s)
    (ne_s : s.Nonempty) {f : β → α} (hf : ContinuousOn f s) : ∃ x ∈ s, IsMaxOn f s x :=
  IsCompact.exists_isMinOn (α := αᵒᵈ) hs ne_s hf

/-- The **extreme value theorem**: if a function `f` is continuous on a closed set `s` and it is
larger than a value in its image away from compact sets, then it has a minimum on this set. -/
/-
**ContinuousOn.exists_isMinOn'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.exists_isMinOn' [ClosedIicTopology α] {s : Set β} {f : β -> α
} (hf : ContinuousOn f s) (hsc : IsClosed s) {x₀ : β} (h₀ : x₀ in s) (hc : foral
lᶠ x in cocompact β ⊓ 𝓟 s, f x₀ <= f x) : exists x in s, IsMinOn f s x
参数：hf : ContinuousOn f s；hsc : IsClosed s；h₀ : x₀ in s；hc : forallᶠ x in cocompa
ct β ⊓ 𝓟 s, f x₀ <= f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.eventually_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Fil
ter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ {q : α → Prop}, (∀ᶠ 
(x : α) in l, q x) ↔…
· 使用定理 `Filter.HasBasis.inf_principal`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filt
er α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ (s' : Set α), (l ⊓ Fi
lter.principal s').…
· 使用定理 `Filter.hasBasis_cocompact`：hasBasis_cocompact : (cocompact X).HasBasis I
sCompact compl
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.insert_subset_iff`：insert_subset_iff : insert a s subseteq t ↔ a in 
t ∧ s subseteq t
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `IsCompact.exists_isMinOn`：IsCompact.exists_isMinOn [ClosedIicTopology α]
 {s : Set β} (hs : IsCompact s) (ne_s : s.Nonempty) {f : β -> α} (hf : Continuou
sOn f s) : exi…
· 使用定理 `IsCompact.insert`：∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X}
, IsCompact s → ∀ (a : X), IsCompact (insert a s)
· 使用定理 `IsCompact.inter_right`：IsCompact.inter_right (hs : IsCompact s) (ht : Is
Closed t) : IsCompact (s inter t)
· 使用定理 `Set.insert_nonempty`：insert_nonempty (a : α) (s : Set α) : (insert a s).
Nonempty
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c

--- 原说明 ---
The **extreme value theorem**: if a function `f` is continuous on a closed set `
s` and it is
larger than a value in its image away from compact sets, then it has a minimum o
n this set.
-/
theorem ContinuousOn.exists_isMinOn' [ClosedIicTopology α] {s : Set β} {f : β → α}
    (hf : ContinuousOn f s) (hsc : IsClosed s) {x₀ : β} (h₀ : x₀ ∈ s)
    (hc : ∀ᶠ x in cocompact β ⊓ 𝓟 s, f x₀ ≤ f x) : ∃ x ∈ s, IsMinOn f s x := by
  rcases (hasBasis_cocompact.inf_principal _).eventually_iff.1 hc with ⟨K, hK, hKf⟩
  have hsub : insert x₀ (K ∩ s) ⊆ s := insert_subset_iff.2 ⟨h₀, inter_subset_right⟩
  obtain ⟨x, hx, hxf⟩ : ∃ x ∈ insert x₀ (K ∩ s), ∀ y ∈ insert x₀ (K ∩ s), f x ≤ f y :=
    ((hK.inter_right hsc).insert x₀).exists_isMinOn (insert_nonempty _ _) (hf.mono hsub)
  refine ⟨x, hsub hx, fun y hy => ?_⟩
  by_cases hyK : y ∈ K
  exacts [hxf _ (Or.inr ⟨hyK, hy⟩), (hxf _ (Or.inl rfl)).trans (hKf ⟨hyK, hy⟩)]

/-- The **extreme value theorem**: if a function `f` is continuous on a closed set `s` and it is
smaller than a value in its image away from compact sets, then it has a maximum on this set. -/
/-
**ContinuousOn.exists_isMaxOn'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.exists_isMaxOn' [ClosedIciTopology α] {s : Set β} {f : β -> α
} (hf : ContinuousOn f s) (hsc : IsClosed s) {x₀ : β} (h₀ : x₀ in s) (hc : foral
lᶠ x in cocompact β ⊓ 𝓟 s, f x <= f x₀) : exists x in s, IsMaxOn f s x
参数：hf : ContinuousOn f s；hsc : IsClosed s；h₀ : x₀ in s；hc : forallᶠ x in cocompa
ct β ⊓ 𝓟 s, f x <= f x₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.exists_isMinOn'`：ContinuousOn.exists_isMinOn' [ClosedIicTop
ology α] {s : Set β} {f : β -> α} (hf : ContinuousOn f s) (hsc : IsClosed s) {x₀
 : β} (h₀ : x₀ in …
· 使用定理 `instClosedIicTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpace 
α] [inst_1 : Preorder α] [ClosedIciTopology α], ClosedIicTopology αᵒᵈ

--- 原说明 ---
The **extreme value theorem**: if a function `f` is continuous on a closed set `
s` and it is
smaller than a value in its image away from compact sets, then it has a maximum 
on this set.
-/
theorem ContinuousOn.exists_isMaxOn' [ClosedIciTopology α] {s : Set β} {f : β → α}
    (hf : ContinuousOn f s) (hsc : IsClosed s) {x₀ : β} (h₀ : x₀ ∈ s)
    (hc : ∀ᶠ x in cocompact β ⊓ 𝓟 s, f x ≤ f x₀) : ∃ x ∈ s, IsMaxOn f s x :=
  ContinuousOn.exists_isMinOn' (α := αᵒᵈ) hf hsc h₀ hc

/-- The **extreme value theorem**: if a continuous function `f` is larger than a value in its range
away from compact sets, then it has a global minimum. -/
/-
**Continuous.exists_forall_le'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.exists_forall_le' [ClosedIicTopology α] {f : β -> α} (hf : Cont
inuous f) (x₀ : β) (h : forallᶠ x in cocompact β, f x₀ <= f x) : exists x : β, f
orall y : β, f x <= f y
参数：hf : Continuous f；x₀ : β；h : forallᶠ x in cocompact β, f x₀ <= f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.exists_isMinOn'`：ContinuousOn.exists_isMinOn' [ClosedIicTop
ology α] {s : Set β} {f : β -> α} (hf : ContinuousOn f s) (hsc : IsClosed s) {x₀
 : β} (h₀ : x₀ in …
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `isClosed_univ`：isClosed_univ : IsClosed (univ : Set X)
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.principal_univ`：∀ {α : Type u}, Filter.principal Set.univ = ⊤
· 使用定理 `inf_top_eq`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderTo
p α] (a : α), a ⊓ ⊤ = a

--- 原说明 ---
The **extreme value theorem**: if a continuous function `f` is larger than a val
ue in its range
away from compact sets, then it has a global minimum.
-/
theorem Continuous.exists_forall_le' [ClosedIicTopology α] {f : β → α} (hf : Continuous f)
    (x₀ : β) (h : ∀ᶠ x in cocompact β, f x₀ ≤ f x) : ∃ x : β, ∀ y : β, f x ≤ f y :=
  let ⟨x, _, hx⟩ := hf.continuousOn.exists_isMinOn' isClosed_univ (mem_univ x₀)
    (by rwa [principal_univ, inf_top_eq])
  ⟨x, fun y => hx (mem_univ y)⟩

/-- The **extreme value theorem**: if a continuous function `f` is smaller than a value in its range
away from compact sets, then it has a global maximum. -/
/-
**Continuous.exists_forall_ge'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.exists_forall_ge' [ClosedIciTopology α] {f : β -> α} (hf : Cont
inuous f) (x₀ : β) (h : forallᶠ x in cocompact β, f x <= f x₀) : exists x : β, f
orall y : β, f y <= f x
参数：hf : Continuous f；x₀ : β；h : forallᶠ x in cocompact β, f x <= f x₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.exists_forall_le'`：Continuous.exists_forall_le' [ClosedIicTop
ology α] {f : β -> α} (hf : Continuous f) (x₀ : β) (h : forallᶠ x in cocompact β
, f x₀ <= f x) : e…
· 使用定理 `instClosedIicTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpace 
α] [inst_1 : Preorder α] [ClosedIciTopology α], ClosedIicTopology αᵒᵈ

--- 原说明 ---
The **extreme value theorem**: if a continuous function `f` is smaller than a va
lue in its range
away from compact sets, then it has a global maximum.
-/
theorem Continuous.exists_forall_ge' [ClosedIciTopology α] {f : β → α} (hf : Continuous f)
    (x₀ : β) (h : ∀ᶠ x in cocompact β, f x ≤ f x₀) : ∃ x : β, ∀ y : β, f y ≤ f x :=
  Continuous.exists_forall_le' (α := αᵒᵈ) hf x₀ h

/-- The **extreme value theorem**: if a continuous function `f` tends to infinity away from compact
sets, then it has a global minimum. -/
/-
**Continuous.exists_forall_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.exists_forall_le [ClosedIicTopology α] [Nonempty β] {f : β -> α
} (hf : Continuous f) (hlim : Tendsto f (cocompact β) atTop) : exists x, forall 
y, f x <= f y
参数：hf : Continuous f；hlim : Tendsto f (cocompact β) atTop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.exists_forall_le'`：Continuous.exists_forall_le' [ClosedIicTop
ology α] {f : β -> α} (hf : Continuous f) (x₀ : β) (h : forallᶠ x in cocompact β
, f x₀ <= f x) : e…
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x

--- 原说明 ---
The **extreme value theorem**: if a continuous function `f` tends to infinity aw
ay from compact
sets, then it has a global minimum.
-/
theorem Continuous.exists_forall_le [ClosedIicTopology α] [Nonempty β] {f : β → α}
    (hf : Continuous f) (hlim : Tendsto f (cocompact β) atTop) : ∃ x, ∀ y, f x ≤ f y := by
  inhabit β
  exact hf.exists_forall_le' default (hlim.eventually <| eventually_ge_atTop _)

/-- The **extreme value theorem**: if a continuous function `f` tends to negative infinity away from
compact sets, then it has a global maximum. -/
/-
**Continuous.exists_forall_ge** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.exists_forall_ge [ClosedIciTopology α] [Nonempty β] {f : β -> α
} (hf : Continuous f) (hlim : Tendsto f (cocompact β) atBot) : exists x, forall 
y, f y <= f x
参数：hf : Continuous f；hlim : Tendsto f (cocompact β) atBot。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.exists_forall_le`：Continuous.exists_forall_le [ClosedIicTopol
ogy α] [Nonempty β] {f : β -> α} (hf : Continuous f) (hlim : Tendsto f (cocompac
t β) atTop) : exi…
· 使用定理 `instClosedIicTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpace 
α] [inst_1 : Preorder α] [ClosedIciTopology α], ClosedIicTopology αᵒᵈ

--- 原说明 ---
The **extreme value theorem**: if a continuous function `f` tends to negative in
finity away from
compact sets, then it has a global maximum.
-/
theorem Continuous.exists_forall_ge [ClosedIciTopology α] [Nonempty β] {f : β → α}
    (hf : Continuous f) (hlim : Tendsto f (cocompact β) atBot) : ∃ x, ∀ y, f y ≤ f x :=
  Continuous.exists_forall_le (α := αᵒᵈ) hf hlim

/-- A continuous function with compact support has a global minimum. -/
@[to_additive /-- A continuous function with compact support has a global minimum. -/]
/-
**Continuous.exists_forall_le_of_hasCompactMulSupport** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：Continuous.exists_forall_le_of_hasCompactMulSupport [ClosedIicTopology α] 
[Nonempty β] [One α] {f : β -> α} (hf : Continuous f) (h : HasCompactMulSupport 
f) : exists x : β, forall y : β, f x <= f y
参数：hf : Continuous f；h : HasCompactMulSupport f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.exists_isLeast`：IsCompact.exists_isLeast [ClosedIicTopology α]
 {s : Set α} (hs : IsCompact s) (ne_s : s.Nonempty) : exists x, IsLeast s x
· 使用定理 `HasCompactMulSupport.isCompact_range`：isCompact_range [TopologicalSpace 
β] (h : HasCompactMulSupport f) (hf : Continuous f) : IsCompact (range f)
· 使用定理 `Set.range_nonempty`：range_nonempty [h : Nonempty ι] (f : ι -> α) : (rang
e f).Nonempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
· 使用定理 `mem_lowerBounds`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α} {a : α
}, a ∈ lowerBounds s ↔ ∀ x ∈ s, a ≤ x

--- 原说明 ---
A continuous function with compact support has a global minimum.
-/
theorem Continuous.exists_forall_le_of_hasCompactMulSupport [ClosedIicTopology α] [Nonempty β]
    [One α] {f : β → α} (hf : Continuous f) (h : HasCompactMulSupport f) :
    ∃ x : β, ∀ y : β, f x ≤ f y := by
  obtain ⟨_, ⟨x, rfl⟩, hx⟩ := (h.isCompact_range hf).exists_isLeast (range_nonempty _)
  rw [mem_lowerBounds, forall_mem_range] at hx
  exact ⟨x, hx⟩

/-- A continuous function with compact support has a global maximum. -/
@[to_additive /-- A continuous function with compact support has a global maximum. -/]
/-
**Continuous.exists_forall_ge_of_hasCompactMulSupport** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：Continuous.exists_forall_ge_of_hasCompactMulSupport [ClosedIciTopology α] 
[Nonempty β] [One α] {f : β -> α} (hf : Continuous f) (h : HasCompactMulSupport 
f) : exists x : β, forall y : β, f y <= f x
参数：hf : Continuous f；h : HasCompactMulSupport f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.exists_forall_le_of_hasCompactMulSupport`：Continuous.exists_f
orall_le_of_hasCompactMulSupport [ClosedIicTopology α] [Nonempty β] [One α] {f :
 β -> α} (hf : Continuous f) (h : HasComp…
· 使用定理 `instClosedIicTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpace 
α] [inst_1 : Preorder α] [ClosedIciTopology α], ClosedIicTopology αᵒᵈ

--- 原说明 ---
A continuous function with compact support has a global maximum.
-/
theorem Continuous.exists_forall_ge_of_hasCompactMulSupport [ClosedIciTopology α] [Nonempty β]
    [One α] {f : β → α} (hf : Continuous f) (h : HasCompactMulSupport f) :
    ∃ x : β, ∀ y : β, f y ≤ f x :=
  Continuous.exists_forall_le_of_hasCompactMulSupport (α := αᵒᵈ) hf h

/-- A compact set is bounded below -/
/-
**IsCompact.bddBelow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.bddBelow [ClosedIicTopology α] [Nonempty α] {s : Set α} (hs : Is
Compact s) : BddBelow s
参数：hs : IsCompact s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `bddBelow_empty`：∀ {α : Type u_1} [inst : Preorder α] [Nonempty α], BddBe
low ∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsCompact.exists_isLeast`：IsCompact.exists_isLeast [ClosedIicTopology α]
 {s : Set α} (hs : IsCompact s) (ne_s : s.Nonempty) : exists x, IsLeast s x

--- 原说明 ---
A compact set is bounded below
-/
theorem IsCompact.bddBelow [ClosedIicTopology α] [Nonempty α] {s : Set α} (hs : IsCompact s) :
    BddBelow s := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · exact bddBelow_empty
  · obtain ⟨a, -, has⟩ := hs.exists_isLeast hne
    exact ⟨a, has⟩

/-- A compact set is bounded above -/
/-
**IsCompact.bddAbove** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.bddAbove [ClosedIciTopology α] [Nonempty α] {s : Set α} (hs : Is
Compact s) : BddAbove s
参数：hs : IsCompact s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.bddBelow`：IsCompact.bddBelow [ClosedIicTopology α] [Nonempty α
] {s : Set α} (hs : IsCompact s) : BddBelow s
· 使用定理 `instClosedIicTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpace 
α] [inst_1 : Preorder α] [ClosedIciTopology α], ClosedIicTopology αᵒᵈ
· 使用定理 `OrderDual.instNonempty`：∀ (α : Type u_2) [h : Nonempty α], Nonempty αᵒᵈ

--- 原说明 ---
A compact set is bounded above
-/
theorem IsCompact.bddAbove [ClosedIciTopology α] [Nonempty α] {s : Set α} (hs : IsCompact s) :
    BddAbove s :=
  IsCompact.bddBelow (α := αᵒᵈ) hs

/-- A continuous function is bounded below on a compact set. -/
/-
**IsCompact.bddBelow_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.bddBelow_image [ClosedIicTopology α] [Nonempty α] {f : β -> α} {
K : Set β} (hK : IsCompact K) (hf : ContinuousOn f K) : BddBelow (f '' K)
参数：hK : IsCompact K；hf : ContinuousOn f K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.bddBelow`：IsCompact.bddBelow [ClosedIicTopology α] [Nonempty α
] {s : Set α} (hs : IsCompact s) : BddBelow s
· 使用定理 `IsCompact.image_of_continuousOn`：IsCompact.image_of_continuousOn {f : X 
-> Y} (hs : IsCompact s) (hf : ContinuousOn f s) : IsCompact (f '' s)

--- 原说明 ---
A continuous function is bounded below on a compact set.
-/
theorem IsCompact.bddBelow_image [ClosedIicTopology α] [Nonempty α] {f : β → α} {K : Set β}
    (hK : IsCompact K) (hf : ContinuousOn f K) : BddBelow (f '' K) :=
  (hK.image_of_continuousOn hf).bddBelow

/-- A continuous function is bounded above on a compact set. -/
/-
**IsCompact.bddAbove_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.bddAbove_image [ClosedIciTopology α] [Nonempty α] {f : β -> α} {
K : Set β} (hK : IsCompact K) (hf : ContinuousOn f K) : BddAbove (f '' K)
参数：hK : IsCompact K；hf : ContinuousOn f K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.bddBelow_image`：IsCompact.bddBelow_image [ClosedIicTopology α]
 [Nonempty α] {f : β -> α} {K : Set β} (hK : IsCompact K) (hf : ContinuousOn f K
) : BddBelow (…
· 使用定理 `instClosedIicTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpace 
α] [inst_1 : Preorder α] [ClosedIciTopology α], ClosedIicTopology αᵒᵈ
· 使用定理 `OrderDual.instNonempty`：∀ (α : Type u_2) [h : Nonempty α], Nonempty αᵒᵈ

--- 原说明 ---
A continuous function is bounded above on a compact set.
-/
theorem IsCompact.bddAbove_image [ClosedIciTopology α] [Nonempty α] {f : β → α} {K : Set β}
    (hK : IsCompact K) (hf : ContinuousOn f K) : BddAbove (f '' K) :=
  IsCompact.bddBelow_image (α := αᵒᵈ) hK hf

/-- A continuous function with compact support is bounded below. -/
@[to_additive /-- A continuous function with compact support is bounded below. -/]
/-
**Continuous.bddBelow_range_of_hasCompactMulSupport** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：Continuous.bddBelow_range_of_hasCompactMulSupport [ClosedIicTopology α] [O
ne α] {f : β -> α} (hf : Continuous f) (h : HasCompactMulSupport f) : BddBelow (
range f)
参数：hf : Continuous f；h : HasCompactMulSupport f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.bddBelow`：IsCompact.bddBelow [ClosedIicTopology α] [Nonempty α
] {s : Set α} (hs : IsCompact s) : BddBelow s
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
· 使用定理 `HasCompactMulSupport.isCompact_range`：isCompact_range [TopologicalSpace 
β] (h : HasCompactMulSupport f) (hf : Continuous f) : IsCompact (range f)

--- 原说明 ---
A continuous function with compact support is bounded below.
-/
theorem Continuous.bddBelow_range_of_hasCompactMulSupport [ClosedIicTopology α] [One α]
    {f : β → α} (hf : Continuous f) (h : HasCompactMulSupport f) : BddBelow (range f) :=
  (h.isCompact_range hf).bddBelow

/-- A continuous function with compact support is bounded above. -/
@[to_additive /-- A continuous function with compact support is bounded above. -/]
/-
**Continuous.bddAbove_range_of_hasCompactMulSupport** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：Continuous.bddAbove_range_of_hasCompactMulSupport [ClosedIciTopology α] [O
ne α] {f : β -> α} (hf : Continuous f) (h : HasCompactMulSupport f) : BddAbove (
range f)
参数：hf : Continuous f；h : HasCompactMulSupport f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.bddBelow_range_of_hasCompactMulSupport`：Continuous.bddBelow_r
ange_of_hasCompactMulSupport [ClosedIicTopology α] [One α] {f : β -> α} (hf : Co
ntinuous f) (h : HasCompactMulSupport f…
· 使用定理 `instClosedIicTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpace 
α] [inst_1 : Preorder α] [ClosedIciTopology α], ClosedIicTopology αᵒᵈ

--- 原说明 ---
A continuous function with compact support is bounded above.
-/
theorem Continuous.bddAbove_range_of_hasCompactMulSupport [ClosedIciTopology α] [One α]
    {f : β → α} (hf : Continuous f) (h : HasCompactMulSupport f) : BddAbove (range f) :=
  Continuous.bddBelow_range_of_hasCompactMulSupport (α := αᵒᵈ) hf h

end LinearOrder

section ConditionallyCompleteLinearOrder

variable {α β γ : Type*} [ConditionallyCompleteLinearOrder α] [TopologicalSpace α]
  [TopologicalSpace β] [TopologicalSpace γ]

/-
**IsCompact.sSup_lt_iff_of_continuous** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.sSup_lt_iff_of_continuous [ClosedIciTopology α] {f : β -> α} {K 
: Set β} (hK : IsCompact K) (h0K : K.Nonempty) (hf : ContinuousOn f K) (y : α) :
 sSup (f '' K) < y ↔ forall x in K, f x < y
参数：hK : IsCompact K；h0K : K.Nonempty；hf : ContinuousOn f K；y : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `le_csSup`：le_csSup (h₁ : BddAbove s) (h₂ : a in s) : a <= sSup s
· 使用定理 `IsCompact.bddAbove_image`：IsCompact.bddAbove_image [ClosedIciTopology α]
 [Nonempty α] {f : β -> α} {K : Set β} (hK : IsCompact K) (hf : ContinuousOn f K
) : BddAbove (…
· 使用定理 `supSet_to_nonempty`：∀ (α : Type u_1) [SupSet α], Nonempty α
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `IsCompact.exists_isMaxOn`：IsCompact.exists_isMaxOn [ClosedIciTopology α]
 {s : Set β} (hs : IsCompact s) (ne_s : s.Nonempty) {f : β -> α} (hf : Continuou
sOn f s) : exi…
· 使用定理 `csSup_le`：csSup_le (h₁ : s.Nonempty) (h₂ : forall b in s, b <= a) : sSup
 s <= a
· 使用定理 `Set.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set
 α}, s.Nonempty → (f '' s).Nonempty
-/
theorem IsCompact.sSup_lt_iff_of_continuous [ClosedIciTopology α] {f : β → α} {K : Set β}
    (hK : IsCompact K) (h0K : K.Nonempty) (hf : ContinuousOn f K) (y : α) :
    sSup (f '' K) < y ↔ ∀ x ∈ K, f x < y := by
  refine ⟨fun h x hx => (le_csSup (hK.bddAbove_image hf) <| mem_image_of_mem f hx).trans_lt h,
    fun h => ?_⟩
  obtain ⟨x, hx, h2x⟩ := hK.exists_isMaxOn h0K hf
  refine (csSup_le (h0K.image f) ?_).trans_lt (h x hx)
  rintro _ ⟨x', hx', rfl⟩; exact h2x hx'
/-
**IsCompact.lt_sInf_iff_of_continuous** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.lt_sInf_iff_of_continuous [ClosedIicTopology α] {f : β -> α} {K 
: Set β} (hK : IsCompact K) (h0K : K.Nonempty) (hf : ContinuousOn f K) (y : α) :
 y < sInf (f '' K) ↔ forall x in K, y < f x
参数：hK : IsCompact K；h0K : K.Nonempty；hf : ContinuousOn f K；y : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.sSup_lt_iff_of_continuous`：IsCompact.sSup_lt_iff_of_continuous
 [ClosedIciTopology α] {f : β -> α} {K : Set β} (hK : IsCompact K) (h0K : K.None
mpty) (hf : ContinuousOn …
· 使用定理 `instClosedIciTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpace 
α] [inst_1 : Preorder α] [ClosedIicTopology α], ClosedIciTopology αᵒᵈ
-/
theorem IsCompact.lt_sInf_iff_of_continuous [ClosedIicTopology α] {f : β → α} {K : Set β}
    (hK : IsCompact K) (h0K : K.Nonempty) (hf : ContinuousOn f K) (y : α) :
    y < sInf (f '' K) ↔ ∀ x ∈ K, y < f x :=
  IsCompact.sSup_lt_iff_of_continuous (α := αᵒᵈ) hK h0K hf y

end ConditionallyCompleteLinearOrder

/-!
### Min and max elements of a compact set
-/

section InfSup

variable {α β : Type*} [ConditionallyCompleteLinearOrder α] [TopologicalSpace α]
  [TopologicalSpace β]

/-
**IsCompact.sInf_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.sInf_mem [ClosedIicTopology α] {s : Set α} (hs : IsCompact s) (n
e_s : s.Nonempty) : sInf s in s
参数：hs : IsCompact s；ne_s : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.exists_isLeast`：IsCompact.exists_isLeast [ClosedIicTopology α]
 {s : Set α} (hs : IsCompact s) (ne_s : s.Nonempty) : exists x, IsLeast s x
· 使用定理 `IsLeast.csInf_mem`：∀ {α : Type u_1} [inst : ConditionallyCompletePartial
OrderInf α] {s : Set α} {a : α}, IsLeast s a → sInf s ∈ s
-/
theorem IsCompact.sInf_mem [ClosedIicTopology α] {s : Set α} (hs : IsCompact s)
    (ne_s : s.Nonempty) : sInf s ∈ s :=
  let ⟨_a, ha⟩ := hs.exists_isLeast ne_s
  ha.csInf_mem
/-
**IsCompact.sSup_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.sSup_mem [ClosedIciTopology α] {s : Set α} (hs : IsCompact s) (n
e_s : s.Nonempty) : sSup s in s
参数：hs : IsCompact s；ne_s : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.sInf_mem`：IsCompact.sInf_mem [ClosedIicTopology α] {s : Set α}
 (hs : IsCompact s) (ne_s : s.Nonempty) : sInf s in s
· 使用定理 `instClosedIicTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpace 
α] [inst_1 : Preorder α] [ClosedIciTopology α], ClosedIicTopology αᵒᵈ
-/
theorem IsCompact.sSup_mem [ClosedIciTopology α] {s : Set α} (hs : IsCompact s)
    (ne_s : s.Nonempty) : sSup s ∈ s :=
  IsCompact.sInf_mem (α := αᵒᵈ) hs ne_s
/-
**IsCompact.isGLB_sInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.isGLB_sInf [ClosedIicTopology α] {s : Set α} (hs : IsCompact s) 
(ne_s : s.Nonempty) : IsGLB s (sInf s)
参数：hs : IsCompact s；ne_s : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isGLB_csInf`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s
 : Set α},   s.Nonempty → autoParam (BddBelow s) isGLB_csInf._auto_1 → IsGLB s (
s…
· 使用定理 `IsCompact.bddBelow`：IsCompact.bddBelow [ClosedIicTopology α] [Nonempty α
] {s : Set α} (hs : IsCompact s) : BddBelow s
· 使用定理 `supSet_to_nonempty`：∀ (α : Type u_1) [SupSet α], Nonempty α
-/
theorem IsCompact.isGLB_sInf [ClosedIicTopology α] {s : Set α} (hs : IsCompact s)
    (ne_s : s.Nonempty) : IsGLB s (sInf s) :=
  isGLB_csInf ne_s hs.bddBelow
/-
**IsCompact.isLUB_sSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.isLUB_sSup [ClosedIciTopology α] {s : Set α} (hs : IsCompact s) 
(ne_s : s.Nonempty) : IsLUB s (sSup s)
参数：hs : IsCompact s；ne_s : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.isGLB_sInf`：IsCompact.isGLB_sInf [ClosedIicTopology α] {s : Se
t α} (hs : IsCompact s) (ne_s : s.Nonempty) : IsGLB s (sInf s)
· 使用定理 `instClosedIicTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpace 
α] [inst_1 : Preorder α] [ClosedIciTopology α], ClosedIicTopology αᵒᵈ
-/
theorem IsCompact.isLUB_sSup [ClosedIciTopology α] {s : Set α} (hs : IsCompact s)
    (ne_s : s.Nonempty) : IsLUB s (sSup s) :=
  IsCompact.isGLB_sInf (α := αᵒᵈ) hs ne_s
/-
**IsCompact.isLeast_sInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.isLeast_sInf [ClosedIicTopology α] {s : Set α} (hs : IsCompact s
) (ne_s : s.Nonempty) : IsLeast s (sInf s)
参数：hs : IsCompact s；ne_s : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.sInf_mem`：IsCompact.sInf_mem [ClosedIicTopology α] {s : Set α}
 (hs : IsCompact s) (ne_s : s.Nonempty) : sInf s in s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `IsCompact.isGLB_sInf`：IsCompact.isGLB_sInf [ClosedIicTopology α] {s : Se
t α} (hs : IsCompact s) (ne_s : s.Nonempty) : IsGLB s (sInf s)
-/
theorem IsCompact.isLeast_sInf [ClosedIicTopology α] {s : Set α} (hs : IsCompact s)
    (ne_s : s.Nonempty) : IsLeast s (sInf s) :=
  ⟨hs.sInf_mem ne_s, (hs.isGLB_sInf ne_s).1⟩
/-
**IsCompact.isGreatest_sSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.isGreatest_sSup [ClosedIciTopology α] {s : Set α} (hs : IsCompac
t s) (ne_s : s.Nonempty) : IsGreatest s (sSup s)
参数：hs : IsCompact s；ne_s : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.isLeast_sInf`：IsCompact.isLeast_sInf [ClosedIicTopology α] {s 
: Set α} (hs : IsCompact s) (ne_s : s.Nonempty) : IsLeast s (sInf s)
· 使用定理 `instClosedIicTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpace 
α] [inst_1 : Preorder α] [ClosedIciTopology α], ClosedIicTopology αᵒᵈ
-/
theorem IsCompact.isGreatest_sSup [ClosedIciTopology α] {s : Set α} (hs : IsCompact s)
    (ne_s : s.Nonempty) : IsGreatest s (sSup s) :=
  IsCompact.isLeast_sInf (α := αᵒᵈ) hs ne_s
/-
**IsCompact.exists_sInf_image_eq_and_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.exists_sInf_image_eq_and_le [ClosedIicTopology α] {s : Set β} (h
s : IsCompact s) (ne_s : s.Nonempty) {f : β -> α} (hf : ContinuousOn f s) : exis
ts x in s, sInf (f '' s) = f x ∧ forall y in s, f x <= f y
参数：hs : IsCompact s；ne_s : s.Nonempty；hf : ContinuousOn f s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.sInf_mem`：IsCompact.sInf_mem [ClosedIicTopology α] {s : Set α}
 (hs : IsCompact s) (ne_s : s.Nonempty) : sInf s in s
· 使用定理 `IsCompact.image_of_continuousOn`：IsCompact.image_of_continuousOn {f : X 
-> Y} (hs : IsCompact s) (hf : ContinuousOn f s) : IsCompact (f '' s)
· 使用定理 `Set.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set
 α}, s.Nonempty → (f '' s).Nonempty
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `csInf_le`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s : 
Set α} {a : α}, BddBelow s → a ∈ s → sInf s ≤ a
· 使用定理 `IsCompact.bddBelow`：IsCompact.bddBelow [ClosedIicTopology α] [Nonempty α
] {s : Set α} (hs : IsCompact s) : BddBelow s
· 使用定理 `supSet_to_nonempty`：∀ (α : Type u_1) [SupSet α], Nonempty α
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
theorem IsCompact.exists_sInf_image_eq_and_le [ClosedIicTopology α] {s : Set β}
    (hs : IsCompact s) (ne_s : s.Nonempty) {f : β → α} (hf : ContinuousOn f s) :
    ∃ x ∈ s, sInf (f '' s) = f x ∧ ∀ y ∈ s, f x ≤ f y :=
  let ⟨x, hxs, hx⟩ := (hs.image_of_continuousOn hf).sInf_mem (ne_s.image f)
  ⟨x, hxs, hx.symm, fun _y hy =>
    hx.trans_le <| csInf_le (hs.image_of_continuousOn hf).bddBelow <| mem_image_of_mem f hy⟩
/-
**IsCompact.exists_sSup_image_eq_and_ge** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.exists_sSup_image_eq_and_ge [ClosedIciTopology α] {s : Set β} (h
s : IsCompact s) (ne_s : s.Nonempty) {f : β -> α} (hf : ContinuousOn f s) : exis
ts x in s, sSup (f '' s) = f x ∧ forall y in s, f y <= f x
参数：hs : IsCompact s；ne_s : s.Nonempty；hf : ContinuousOn f s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.exists_sInf_image_eq_and_le`：IsCompact.exists_sInf_image_eq_an
d_le [ClosedIicTopology α] {s : Set β} (hs : IsCompact s) (ne_s : s.Nonempty) {f
 : β -> α} (hf : Continuous…
· 使用定理 `instClosedIicTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpace 
α] [inst_1 : Preorder α] [ClosedIciTopology α], ClosedIicTopology αᵒᵈ
-/
theorem IsCompact.exists_sSup_image_eq_and_ge [ClosedIciTopology α] {s : Set β}
    (hs : IsCompact s) (ne_s : s.Nonempty) {f : β → α} (hf : ContinuousOn f s) :
    ∃ x ∈ s, sSup (f '' s) = f x ∧ ∀ y ∈ s, f y ≤ f x :=
  IsCompact.exists_sInf_image_eq_and_le (α := αᵒᵈ) hs ne_s hf
/-
**IsCompact.exists_sInf_image_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.exists_sInf_image_eq [ClosedIicTopology α] {s : Set β} (hs : IsC
ompact s) (ne_s : s.Nonempty) {f : β -> α} (hf : ContinuousOn f s) : exists x in
 s, sInf (f '' s) = f x
参数：hs : IsCompact s；ne_s : s.Nonempty；hf : ContinuousOn f s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.exists_sInf_image_eq_and_le`：IsCompact.exists_sInf_image_eq_an
d_le [ClosedIicTopology α] {s : Set β} (hs : IsCompact s) (ne_s : s.Nonempty) {f
 : β -> α} (hf : Continuous…
-/
theorem IsCompact.exists_sInf_image_eq [ClosedIicTopology α] {s : Set β} (hs : IsCompact s)
    (ne_s : s.Nonempty) {f : β → α} (hf : ContinuousOn f s) : ∃ x ∈ s, sInf (f '' s) = f x :=
  let ⟨x, hxs, hx, _⟩ := hs.exists_sInf_image_eq_and_le ne_s hf
  ⟨x, hxs, hx⟩
/-
**IsCompact.exists_sSup_image_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.exists_sSup_image_eq [ClosedIciTopology α] {s : Set β} (hs : IsC
ompact s) (ne_s : s.Nonempty) : forall {f : β -> α}, ContinuousOn f s -> exists 
x in s, sSup (f '' s) = f x
参数：hs : IsCompact s；ne_s : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.exists_sInf_image_eq`：IsCompact.exists_sInf_image_eq [ClosedIi
cTopology α] {s : Set β} (hs : IsCompact s) (ne_s : s.Nonempty) {f : β -> α} (hf
 : ContinuousOn f s)…
· 使用定理 `instClosedIicTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpace 
α] [inst_1 : Preorder α] [ClosedIciTopology α], ClosedIicTopology αᵒᵈ
-/
theorem IsCompact.exists_sSup_image_eq [ClosedIciTopology α] {s : Set β} (hs : IsCompact s)
    (ne_s : s.Nonempty) : ∀ {f : β → α}, ContinuousOn f s → ∃ x ∈ s, sSup (f '' s) = f x :=
  IsCompact.exists_sInf_image_eq (α := αᵒᵈ) hs ne_s

end InfSup

section ExistsExtr

variable {α β : Type*} [LinearOrder α] [TopologicalSpace α] [TopologicalSpace β]

/-
**IsCompact.exists_isMinOn_mem_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.exists_isMinOn_mem_subset [ClosedIicTopology α] {f : β -> α} {s 
t : Set β} {z : β} (ht : IsCompact t) (hf : ContinuousOn f t) (hz : z in t) (hfz
 : forall z' in t \ s, f z < f z') : exists x in s, IsMinOn f t x
参数：ht : IsCompact t；hf : ContinuousOn f t；hz : z in t；hfz : forall z' in t \ s, 
f z < f z'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.exists_isMinOn`：IsCompact.exists_isMinOn [ClosedIicTopology α]
 {s : Set β} (hs : IsCompact s) (ne_s : s.Nonempty) {f : β -> α} (hf : Continuou
sOn f s) : exi…
· 使用定理 `by_contra`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
-/
theorem IsCompact.exists_isMinOn_mem_subset [ClosedIicTopology α] {f : β → α} {s t : Set β}
    {z : β} (ht : IsCompact t) (hf : ContinuousOn f t) (hz : z ∈ t)
    (hfz : ∀ z' ∈ t \ s, f z < f z') : ∃ x ∈ s, IsMinOn f t x :=
  let ⟨x, hxt, hfx⟩ := ht.exists_isMinOn ⟨z, hz⟩ hf
  ⟨x, by_contra fun hxs => (hfz x ⟨hxt, hxs⟩).not_ge (hfx hz), hfx⟩
/-
**IsCompact.exists_isMaxOn_mem_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.exists_isMaxOn_mem_subset [ClosedIciTopology α] {f : β -> α} {s 
t : Set β} {z : β} (ht : IsCompact t) (hf : ContinuousOn f t) (hz : z in t) (hfz
 : forall z' in t \ s, f z' < f z) : exists x in s, IsMaxOn f t x
参数：ht : IsCompact t；hf : ContinuousOn f t；hz : z in t；hfz : forall z' in t \ s, 
f z' < f z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.exists_isMaxOn`：IsCompact.exists_isMaxOn [ClosedIciTopology α]
 {s : Set β} (hs : IsCompact s) (ne_s : s.Nonempty) {f : β -> α} (hf : Continuou
sOn f s) : exi…
· 使用定理 `by_contra`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
-/
theorem IsCompact.exists_isMaxOn_mem_subset [ClosedIciTopology α] {f : β → α} {s t : Set β}
    {z : β} (ht : IsCompact t) (hf : ContinuousOn f t) (hz : z ∈ t)
    (hfz : ∀ z' ∈ t \ s, f z' < f z) : ∃ x ∈ s, IsMaxOn f t x :=
  let ⟨x, hxt, hfx⟩ := ht.exists_isMaxOn ⟨z, hz⟩ hf
  ⟨x, by_contra fun hxs => (hfz x ⟨hxt, hxs⟩).not_ge (hfx hz), hfx⟩

-- TODO: we could assume `t ∈ 𝓝ˢ s` (a.k.a. `s ⊆ interior t`) instead of `s ⊆ t` and `IsOpen s`.
/-
**IsCompact.exists_isLocalMin_mem_open** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.exists_isLocalMin_mem_open [ClosedIicTopology α] {f : β -> α} {s
 t : Set β} {z : β} (ht : IsCompact t) (hst : s subseteq t) (hf : ContinuousOn f
 t) (hz : z in t) (hfz : forall z' in t \ s, f z < f z') (hs : IsOpen s) : exist
s x in s, IsLocalMin f x
参数：ht : IsCompact t；hst : s subseteq t；hf : ContinuousOn f t；hz : z in t；hfz : f
orall z' in t \ s, f z < f z'；hs : IsOpen s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.exists_isMinOn_mem_subset`：IsCompact.exists_isMinOn_mem_subset
 [ClosedIicTopology α] {f : β -> α} {s t : Set β} {z : β} (ht : IsCompact t) (hf
 : ContinuousOn f t) (hz …
· 使用定理 `IsMinOn.isLocalMin`：IsMinOn.isLocalMin (hf : IsMinOn f s a) (hs : s in 𝓝
 a) : IsLocalMin f a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists t subseteq s, IsOpen t ∧ 
x in t
-/
theorem IsCompact.exists_isLocalMin_mem_open [ClosedIicTopology α] {f : β → α} {s t : Set β}
    {z : β} (ht : IsCompact t) (hst : s ⊆ t) (hf : ContinuousOn f t) (hz : z ∈ t)
    (hfz : ∀ z' ∈ t \ s, f z < f z') (hs : IsOpen s) : ∃ x ∈ s, IsLocalMin f x :=
  let ⟨x, hxs, h⟩ := ht.exists_isMinOn_mem_subset hf hz hfz
  ⟨x, hxs, h.isLocalMin <| mem_nhds_iff.2 ⟨s, hst, hs, hxs⟩⟩
/-
**IsCompact.exists_isLocalMax_mem_open** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.exists_isLocalMax_mem_open [ClosedIciTopology α] {f : β -> α} {s
 t : Set β} {z : β} (ht : IsCompact t) (hst : s subseteq t) (hf : ContinuousOn f
 t) (hz : z in t) (hfz : forall z' in t \ s, f z' < f z) (hs : IsOpen s) : exist
s x in s, IsLocalMax f x
参数：ht : IsCompact t；hst : s subseteq t；hf : ContinuousOn f t；hz : z in t；hfz : f
orall z' in t \ s, f z' < f z；hs : IsOpen s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.exists_isMaxOn_mem_subset`：IsCompact.exists_isMaxOn_mem_subset
 [ClosedIciTopology α] {f : β -> α} {s t : Set β} {z : β} (ht : IsCompact t) (hf
 : ContinuousOn f t) (hz …
· 使用定理 `IsMaxOn.isLocalMax`：IsMaxOn.isLocalMax (hf : IsMaxOn f s a) (hs : s in 𝓝
 a) : IsLocalMax f a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists t subseteq s, IsOpen t ∧ 
x in t
-/
theorem IsCompact.exists_isLocalMax_mem_open [ClosedIciTopology α] {f : β → α} {s t : Set β}
    {z : β} (ht : IsCompact t) (hst : s ⊆ t) (hf : ContinuousOn f t) (hz : z ∈ t)
    (hfz : ∀ z' ∈ t \ s, f z' < f z) (hs : IsOpen s) : ∃ x ∈ s, IsLocalMax f x :=
  let ⟨x, hxs, h⟩ := ht.exists_isMaxOn_mem_subset hf hz hfz
  ⟨x, hxs, h.isLocalMax <| mem_nhds_iff.2 ⟨s, hst, hs, hxs⟩⟩

end ExistsExtr

variable {α β γ : Type*} [ConditionallyCompleteLinearOrder α] [TopologicalSpace α]
  [OrderTopology α] [TopologicalSpace β] [TopologicalSpace γ]

/-
**eq_Icc_of_connected_compact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_Icc_of_connected_compact {s : Set α} (h₁ : IsConnected s) (h₂ : IsCompa
ct s) : s = Icc (sInf s) (sSup s)
参数：h₁ : IsConnected s；h₂ : IsCompact s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_Icc_csInf_csSup_of_connected_bdd_closed`：eq_Icc_csInf_csSup_of_connec
ted_bdd_closed {s : Set α} (hc : IsConnected s) (hb : BddBelow s) (ha : BddAbove
 s) (hcl : IsClosed s) : s = Icc…
· 使用定理 `IsCompact.bddBelow`：IsCompact.bddBelow [ClosedIicTopology α] [Nonempty α
] {s : Set α} (hs : IsCompact s) : BddBelow s
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `supSet_to_nonempty`：∀ (α : Type u_1) [SupSet α], Nonempty α
· 使用定理 `IsCompact.bddAbove`：IsCompact.bddAbove [ClosedIciTopology α] [Nonempty α
] {s : Set α} (hs : IsCompact s) : BddAbove s
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `IsCompact.isClosed`：IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsC
ompact s) : IsClosed s
· 使用定理 `OrderClosedTopology.to_t2Space`：∀ {α : Type u} [inst : TopologicalSpace 
α] [inst_1 : PartialOrder α] [t : OrderClosedTopology α], T2Space α
-/
theorem eq_Icc_of_connected_compact {s : Set α} (h₁ : IsConnected s) (h₂ : IsCompact s) :
    s = Icc (sInf s) (sSup s) :=
  eq_Icc_csInf_csSup_of_connected_bdd_closed h₁ h₂.bddBelow h₂.bddAbove h₂.isClosed

/-- If `f : γ → β → α` is a function that is continuous as a function on `γ × β`, `α` is a
conditionally complete linear order, and `K : Set β` is a compact set, then
`fun x ↦ sSup (f x '' K)` is a continuous function. -/
/- TODO: generalize. The following version seems to be true:
```
theorem IsCompact.tendsto_sSup {f : γ → β → α} {g : β → α} {K : Set β} {l : Filter γ}
    (hK : IsCompact K) (hf : ∀ y ∈ K, Tendsto ↿f (l ×ˢ 𝓝[K] y) (𝓝 (g y)))
    (hgc : ContinuousOn g K) :
    Tendsto (fun x => sSup (f x '' K)) l (𝓝 (sSup (g '' K))) := _
```
Moreover, it seems that `hgc` follows from `hf` (Yury Kudryashov). -/
/-
**IsCompact.continuous_sSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.continuous_sSup {f : γ -> β -> α} {K : Set β} (hK : IsCompact K)
 (hf : Continuous ↿f) : Continuous fun x => sSup (f x '' K)
参数：hK : IsCompact K；hf : Continuous ↿f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.image_empty`：image_empty (f : α -> β) : f '' ∅ = ∅
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `IsCompact.exists_sSup_image_eq_and_ge`：IsCompact.exists_sSup_image_eq_an
d_ge [ClosedIciTopology α] {s : Set β} (hs : IsCompact s) (ne_s : s.Nonempty) {f
 : β -> α} (hf : Continuous…
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `Continuous.prodMk_right`：Continuous.prodMk_right (x : X) : Continuous fu
n y : Y => (x, y)
· 使用定理 `ContinuousAt.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSp
ace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (x : X),   ContinuousAt f x = F
ilter.T…
· 使用定理 `tendsto_order`：tendsto_order [OrderTopology α] {f : β -> α} {a : α} {x :
 Filter β} : Tendsto f x (𝓝 a) ↔ (forall a' < a, forallᶠ b in x, a' < f b) ∧ for
all…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `Continuous.prodMk_left`：Continuous.prodMk_left (y : Y) : Continuous fun 
x : X => (x, y)
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `le_csSup`：le_csSup (h₁ : BddAbove s) (h₂ : a in s) : a <= sSup s
· 使用定理 `IsCompact.bddAbove_image`：IsCompact.bddAbove_image [ClosedIciTopology α]
 [Nonempty α] {f : β -> α} {K : Set β} (hK : IsCompact K) (hf : ContinuousOn f K
) : BddAbove (…
· 使用定理 `supSet_to_nonempty`：∀ (α : Type u_1) [SupSet α], Nonempty α
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `generalized_tube_lemma`：generalized_tube_lemma (hs : IsCompact s) {t : S
et Y} (ht : IsCompact t) {n : Set (X × Y)} (hn : IsOpen n) (hp : s ×ˢ t subseteq
 n) : exists…
· 使用定理 `isCompact_singleton`：isCompact_singleton {x : X} : IsCompact ({x} : Set 
X)
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `isOpen_Iio`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : LinearO
rder α] [ClosedIciTopology α] {a : α}, IsOpen (Set.Iio a)
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
TODO: generalize. The following version seems to be true:
```
theorem IsCompact.tendsto_sSup {f : γ → β → α} {g : β → α} {K : Set β} {l : Filt
er γ}
    (hK : IsCompact K) (hf : ∀ y ∈ K, Tendsto ↿f (l ×ˢ 𝓝[K] y) (𝓝 (g y)))
    (hgc : ContinuousOn g K) :
    Tendsto (fun x => sSup (f x '' K)) l (𝓝 (sSup (g '' K))) := _
```
Moreover, it seems that `hgc` follows from `hf` (Yury Kudryashov).
-/
theorem IsCompact.continuous_sSup {f : γ → β → α} {K : Set β} (hK : IsCompact K)
    (hf : Continuous ↿f) : Continuous fun x => sSup (f x '' K) := by
  rcases eq_empty_or_nonempty K with (rfl | h0K)
  · simp_rw [image_empty]
    exact continuous_const
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨y, hyK, h2y, hy⟩ :=
    hK.exists_sSup_image_eq_and_ge h0K
      (show Continuous (f x) from hf.comp <| .prodMk_right x).continuousOn
  rw [ContinuousAt, h2y, tendsto_order]
  have := tendsto_order.mp ((show Continuous fun x => f x y
    from hf.comp <| .prodMk_left _).tendsto x)
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · refine (this.1 z hz).mono fun x' hx' =>
      hx'.trans_le <| le_csSup ?_ <| mem_image_of_mem (f x') hyK
    exact hK.bddAbove_image (hf.comp <| .prodMk_right x').continuousOn
  · have h : ({x} : Set γ) ×ˢ K ⊆ ↿f ⁻¹' Iio z := by
      rintro ⟨x', y'⟩ ⟨(rfl : x' = x), hy'⟩
      exact (hy y' hy').trans_lt hz
    obtain ⟨u, v, hu, _, hxu, hKv, huv⟩ :=
      generalized_tube_lemma isCompact_singleton hK (isOpen_Iio.preimage hf) h
    refine eventually_of_mem (hu.mem_nhds (singleton_subset_iff.mp hxu)) fun x' hx' => ?_
    rw [hK.sSup_lt_iff_of_continuous h0K
        (show Continuous (f x') from hf.comp <| .prodMk_right x').continuousOn]
    exact fun y' hy' => huv (mk_mem_prod hx' (hKv hy'))
/-
**IsCompact.continuous_sInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.continuous_sInf {f : γ -> β -> α} {K : Set β} (hK : IsCompact K)
 (hf : Continuous ↿f) : Continuous fun x => sInf (f x '' K)
参数：hK : IsCompact K；hf : Continuous ↿f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.continuous_sSup`：IsCompact.continuous_sSup {f : γ -> β -> α} {
K : Set β} (hK : IsCompact K) (hf : Continuous ↿f) : Continuous fun x => sSup (f
 x '' K)
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
-/
theorem IsCompact.continuous_sInf {f : γ → β → α} {K : Set β} (hK : IsCompact K)
    (hf : Continuous ↿f) : Continuous fun x => sInf (f x '' K) :=
  IsCompact.continuous_sSup (α := αᵒᵈ) hK hf

namespace ContinuousOn

/-!
### Image of a closed interval
-/

variable [DenselyOrdered α] [ConditionallyCompleteLinearOrder β] [OrderTopology β] {f : α → β}
  {a b c : α}

open scoped Interval

/-
**ContinuousOn.image_Icc** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousOn`。
形式化陈述：image_Icc (hab : a <= b) (h : ContinuousOn f <| Icc a b) : f '' Icc a b = 
Icc (sInf <| f '' Icc a b) (sSup <| f '' Icc a b)
参数：hab : a <= b；h : ContinuousOn f <| Icc a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_Icc_of_connected_compact`：eq_Icc_of_connected_compact {s : Set α} (h₁
 : IsConnected s) (h₂ : IsCompact s) : s = Icc (sInf s) (sSup s)
· 使用定理 `Set.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set
 α}, s.Nonempty → (f '' s).Nonempty
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.nonempty_Icc`：nonempty_Icc : (Icc a b).Nonempty ↔ a <= b
· 使用定理 `IsPreconnected.image`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpa
ce α] [inst_1 : TopologicalSpace β] {s : Set α},   IsPreconnected s → ∀ (f : α →
 β), Conti…
· 使用定理 `isPreconnected_Icc`：isPreconnected_Icc : IsPreconnected (Icc a b)
· 使用定理 `IsCompact.image_of_continuousOn`：IsCompact.image_of_continuousOn {f : X 
-> Y} (hs : IsCompact s) (hf : ContinuousOn f s) : IsCompact (f '' s)
· 使用定理 `CompactIccSpace.isCompact_Icc`：∀ {α : Type u_1} {inst : TopologicalSpace
 α} {inst_1 : Preorder α} [self : CompactIccSpace α] {a b : α},   IsCompact (Set
.Icc a b)
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
-/
theorem image_Icc (hab : a ≤ b) (h : ContinuousOn f <| Icc a b) :
    f '' Icc a b = Icc (sInf <| f '' Icc a b) (sSup <| f '' Icc a b) :=
  eq_Icc_of_connected_compact ⟨(nonempty_Icc.2 hab).image f, isPreconnected_Icc.image f h⟩
    (isCompact_Icc.image_of_continuousOn h)
/-
**ContinuousOn.image_uIcc_eq_Icc** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousOn`。
形式化陈述：image_uIcc_eq_Icc (h : ContinuousOn f [[a, b]]) : f '' [[a, b]] = Icc (sIn
f (f '' [[a, b]])) (sSup (f '' [[a, b]]))
参数：h : ContinuousOn f [[a, b]]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.image_Icc`：image_Icc (hab : a <= b) (h : ContinuousOn f <| 
Icc a b) : f '' Icc a b = Icc (sInf <| f '' Icc a b) (sSup <| f '' Icc a b)
· 使用定理 `min_le_max`：min_le_max : min a b <= max a b
-/
theorem image_uIcc_eq_Icc (h : ContinuousOn f [[a, b]]) :
    f '' [[a, b]] = Icc (sInf (f '' [[a, b]])) (sSup (f '' [[a, b]])) :=
  image_Icc min_le_max h
/-
**ContinuousOn.image_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousOn`。
形式化陈述：image_uIcc (h : ContinuousOn f <| [[a, b]]) : f '' [[a, b]] = [[sInf (f ''
 [[a, b]]), sSup (f '' [[a, b]])]]
参数：h : ContinuousOn f <| [[a, b]]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ContinuousOn.image_uIcc_eq_Icc`：image_uIcc_eq_Icc (h : ContinuousOn f [[
a, b]]) : f '' [[a, b]] = Icc (sInf (f '' [[a, b]])) (sSup (f '' [[a, b]]))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.uIcc_of_le`：uIcc_of_le (h : a <= b) : [[a, b]] = Icc a b
· 使用定理 `csInf_le_csSup`：csInf_le_csSup (ne : s.Nonempty) (hb : BddBelow s
· 使用定理 `Set.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set
 α}, s.Nonempty → (f '' s).Nonempty
· 使用定理 `Set.nonempty_uIcc`：∀ {α : Type u_1} [inst : Lattice α] {a b : α}, (Set.u
Icc a b).Nonempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `bddBelow_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, BddBelow (
Set.Icc b a)
· 使用引理 `bddAbove_Icc`：bddAbove_Icc : BddAbove (Icc a b)
-/
theorem image_uIcc (h : ContinuousOn f <| [[a, b]]) :
    f '' [[a, b]] = [[sInf (f '' [[a, b]]), sSup (f '' [[a, b]])]] := by
  refine h.image_uIcc_eq_Icc.trans (uIcc_of_le ?_).symm
  refine csInf_le_csSup (nonempty_uIcc.image _) ?_ ?_ <;> rw [h.image_uIcc_eq_Icc]
  exacts [bddBelow_Icc, bddAbove_Icc]
/-
**ContinuousOn.sInf_image_Icc_le** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousOn`。
形式化陈述：sInf_image_Icc_le (h : ContinuousOn f <| Icc a b) (hc : c in Icc a b) : sI
nf (f '' Icc a b) <= f c
参数：h : ContinuousOn f <| Icc a b；hc : c in Icc a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousOn.image_Icc`：image_Icc (hab : a <= b) (h : ContinuousOn f <| 
Icc a b) : f '' Icc a b = Icc (sInf <| f '' Icc a b) (sSup <| f '' Icc a b)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem sInf_image_Icc_le (h : ContinuousOn f <| Icc a b) (hc : c ∈ Icc a b) :
    sInf (f '' Icc a b) ≤ f c := by
  have := mem_image_of_mem f hc
  rw [h.image_Icc (hc.1.trans hc.2)] at this
  exact this.1
/-
**ContinuousOn.le_sSup_image_Icc** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousOn`。
形式化陈述：le_sSup_image_Icc (h : ContinuousOn f <| Icc a b) (hc : c in Icc a b) : f 
c <= sSup (f '' Icc a b)
参数：h : ContinuousOn f <| Icc a b；hc : c in Icc a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousOn.image_Icc`：image_Icc (hab : a <= b) (h : ContinuousOn f <| 
Icc a b) : f '' Icc a b = Icc (sInf <| f '' Icc a b) (sSup <| f '' Icc a b)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem le_sSup_image_Icc (h : ContinuousOn f <| Icc a b) (hc : c ∈ Icc a b) :
    f c ≤ sSup (f '' Icc a b) := by
  have := mem_image_of_mem f hc
  rw [h.image_Icc (hc.1.trans hc.2)] at this
  exact this.2

end ContinuousOn

