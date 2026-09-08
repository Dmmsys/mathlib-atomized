/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.Order.Basic

/-!
# Set neighborhoods of intervals

In this file we prove basic theorems about `𝓝ˢ s`,
where `s` is one of the intervals
`Set.Ici`, `Set.Iic`, `Set.Ioi`, `Set.Iio`, `Set.Ico`, `Set.Ioc`, `Set.Ioo`, and `Set.Icc`.

First, we prove lemmas in terms of filter equalities.
Then we prove lemmas about `s ∈ 𝓝ˢ t`, where both `s` and `t` are intervals.
Finally, we prove a few lemmas about filter bases of `𝓝ˢ (Iic a)` and `𝓝ˢ (Ici a)`.
-/

public section


open Set Filter OrderDual
open scoped Topology

section OrderClosedTopology

variable {α : Type*} [LinearOrder α] [TopologicalSpace α] [OrderClosedTopology α] {a b c d : α}

/-!
### Formulae for `𝓝ˢ` of intervals
-/

/-
**nhdsSet_Ioi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] [inst_1 : TopologicalSpace α] [Ord
erClosedTopology α] {a : α},   nhdsSet (Set.Ioi a) = Filter.principal (Set.Ioi a
)
参数：Set.Ioi a；Set.Ioi a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.nhdsSet_eq`：∀ {X : Type u_2} [inst : TopologicalSpace X] {s : Set
 X}, IsOpen s → nhdsSet s = Filter.principal s
· 使用定理 `isOpen_Ioi`：isOpen_Ioi : IsOpen (Ioi a)
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α

--- 原说明 ---
### Formulae for `𝓝ˢ` of intervals
-/
@[simp] theorem nhdsSet_Ioi : 𝓝ˢ (Ioi a) = 𝓟 (Ioi a) := isOpen_Ioi.nhdsSet_eq
/-
**nhdsSet_Iio** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] [inst_1 : TopologicalSpace α] [Ord
erClosedTopology α] {a : α},   nhdsSet (Set.Iio a) = Filter.principal (Set.Iio a
)
参数：Set.Iio a；Set.Iio a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.nhdsSet_eq`：∀ {X : Type u_2} [inst : TopologicalSpace X] {s : Set
 X}, IsOpen s → nhdsSet s = Filter.principal s
· 使用定理 `isOpen_Iio`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : LinearO
rder α] [ClosedIciTopology α] {a : α}, IsOpen (Set.Iio a)
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α

--- 原说明 ---
### Formulae for `𝓝ˢ` of intervals
-/
@[simp] theorem nhdsSet_Iio : 𝓝ˢ (Iio a) = 𝓟 (Iio a) := isOpen_Iio.nhdsSet_eq
/-
**nhdsSet_Ioo** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] [inst_1 : TopologicalSpace α] [Ord
erClosedTopology α] {a b : α},   nhdsSet (Set.Ioo a b) = Filter.principal (Set.I
oo a b)
参数：Set.Ioo a b；Set.Ioo a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.nhdsSet_eq`：∀ {X : Type u_2} [inst : TopologicalSpace X] {s : Set
 X}, IsOpen s → nhdsSet s = Filter.principal s
· 使用定理 `isOpen_Ioo`：isOpen_Ioo : IsOpen (Ioo a b)

--- 原说明 ---
### Formulae for `𝓝ˢ` of intervals
-/
@[simp] theorem nhdsSet_Ioo : 𝓝ˢ (Ioo a b) = 𝓟 (Ioo a b) := isOpen_Ioo.nhdsSet_eq
/-
**nhdsSet_Ici** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsSet_Ici : 𝓝ˢ (Ici a) = 𝓝 a ⊔ 𝓟 (Ioi a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Ioi_insert`：∀ {α : Type u_1} [inst : PartialOrder α] {a : α}, insert
 a (Set.Ioi a) = Set.Ici a
· 使用定理 `nhdsSet_insert`：nhdsSet_insert (x : X) (s : Set X) : 𝓝ˢ (insert x s) = 𝓝
 x ⊔ 𝓝ˢ s
· 使用定理 `nhdsSet_Ioi`：∀ {α : Type u_1} [inst : LinearOrder α] [inst_1 : Topologic
alSpace α] [OrderClosedTopology α] {a : α},   nhdsSet (Set.Ioi a) = Filter.princ
i…

--- 原说明 ---
### Formulae for `𝓝ˢ` of intervals
-/
theorem nhdsSet_Ici : 𝓝ˢ (Ici a) = 𝓝 a ⊔ 𝓟 (Ioi a) := by
  rw [← Ioi_insert, nhdsSet_insert, nhdsSet_Ioi]
/-
**nhdsSet_Iic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsSet_Iic : 𝓝ˢ (Iic a) = 𝓝 a ⊔ 𝓟 (Iio a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhdsSet_Ici`：nhdsSet_Ici : 𝓝ˢ (Ici a) = 𝓝 a ⊔ 𝓟 (Ioi a)
· 使用定理 `instOrderClosedTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpac
e α] [inst_1 : Preorder α] [t : OrderClosedTopology α], OrderClosedTopology αᵒᵈ
-/
theorem nhdsSet_Iic : 𝓝ˢ (Iic a) = 𝓝 a ⊔ 𝓟 (Iio a) := nhdsSet_Ici (α := αᵒᵈ)
/-
**nhdsSet_Ico** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsSet_Ico (h : a < b) : 𝓝ˢ (Ico a b) = 𝓝 a ⊔ 𝓟 (Ioo a b)
参数：h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Ioo_insert_left`：Ioo_insert_left (h : a < b) : insert a (Ioo a b) = 
Ico a b
· 使用定理 `nhdsSet_insert`：nhdsSet_insert (x : X) (s : Set X) : 𝓝ˢ (insert x s) = 𝓝
 x ⊔ 𝓝ˢ s
· 使用定理 `nhdsSet_Ioo`：∀ {α : Type u_1} [inst : LinearOrder α] [inst_1 : Topologic
alSpace α] [OrderClosedTopology α] {a b : α},   nhdsSet (Set.Ioo a b) = Filter.p
r…
-/
theorem nhdsSet_Ico (h : a < b) : 𝓝ˢ (Ico a b) = 𝓝 a ⊔ 𝓟 (Ioo a b) := by
  rw [← Ioo_insert_left h, nhdsSet_insert, nhdsSet_Ioo]
/-
**nhdsSet_Ioc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsSet_Ioc (h : a < b) : 𝓝ˢ (Ioc a b) = 𝓝 b ⊔ 𝓟 (Ioo a b)
参数：h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Ioo_insert_right`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}
, b < a → insert a (Set.Ioo b a) = Set.Ioc b a
· 使用定理 `nhdsSet_insert`：nhdsSet_insert (x : X) (s : Set X) : 𝓝ˢ (insert x s) = 𝓝
 x ⊔ 𝓝ˢ s
· 使用定理 `nhdsSet_Ioo`：∀ {α : Type u_1} [inst : LinearOrder α] [inst_1 : Topologic
alSpace α] [OrderClosedTopology α] {a b : α},   nhdsSet (Set.Ioo a b) = Filter.p
r…
-/
theorem nhdsSet_Ioc (h : a < b) : 𝓝ˢ (Ioc a b) = 𝓝 b ⊔ 𝓟 (Ioo a b) := by
  rw [← Ioo_insert_right h, nhdsSet_insert, nhdsSet_Ioo]
/-
**nhdsSet_Icc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsSet_Icc (h : a <= b) : 𝓝ˢ (Icc a b) = 𝓝 a ⊔ 𝓝 b ⊔ 𝓟 (Ioo a b)
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Icc_self`：Icc_self (a : α) : Icc a a = {a}
· 使用定理 `nhdsSet_singleton`：nhdsSet_singleton : 𝓝ˢ {x} = 𝓝 x
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `Set.Ioo_eq_empty`：Ioo_eq_empty (h : ¬a < b) : Ioo a b = ∅
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Filter.principal_empty`：principal_empty : 𝓟 (∅ : Set α) = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Ioc_insert_left`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α},
 b ≤ a → insert b (Set.Ioc b a) = Set.Icc b a
· 使用定理 `nhdsSet_insert`：nhdsSet_insert (x : X) (s : Set X) : 𝓝ˢ (insert x s) = 𝓝
 x ⊔ 𝓝ˢ s
· 使用定理 `nhdsSet_Ioc`：nhdsSet_Ioc (h : a < b) : 𝓝ˢ (Ioc a b) = 𝓝 b ⊔ 𝓟 (Ioo a b)
· 使用定理 `sup_assoc`：sup_assoc (a b c : α) : a ⊔ b ⊔ c = a ⊔ (b ⊔ c)
-/
theorem nhdsSet_Icc (h : a ≤ b) : 𝓝ˢ (Icc a b) = 𝓝 a ⊔ 𝓝 b ⊔ 𝓟 (Ioo a b) := by
  rcases h.eq_or_lt with rfl | hlt
  · simp
  · rw [← Ioc_insert_left h, nhdsSet_insert, nhdsSet_Ioc hlt, sup_assoc]

/-!
### Lemmas about `Ixi _ ∈ 𝓝ˢ (Set.Ici _)`
-/

@[simp]
/-
**Ioi_mem_nhdsSet_Ici_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ioi_mem_nhdsSet_Ici_iff : Ioi a in 𝓝ˢ (Ici b) ↔ a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOpen.mem_nhdsSet`：IsOpen.mem_nhdsSet (hU : IsOpen s) : s in 𝓝ˢ t ↔ t s
ubseteq s
· 使用定理 `isOpen_Ioi`：isOpen_Ioi : IsOpen (Ioi a)
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `Set.Ici_subset_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.
Ici a ⊆ Set.Ioi b ↔ b < a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
### Lemmas about `Ixi _ ∈ 𝓝ˢ (Set.Ici _)`
-/
theorem Ioi_mem_nhdsSet_Ici_iff : Ioi a ∈ 𝓝ˢ (Ici b) ↔ a < b := by
  rw [isOpen_Ioi.mem_nhdsSet, Ici_subset_Ioi]

alias ⟨_, Ioi_mem_nhdsSet_Ici⟩ := Ioi_mem_nhdsSet_Ici_iff
/-
**Ici_mem_nhdsSet_Ici** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ici_mem_nhdsSet_Ici (h : a < b) : Ici a in 𝓝ˢ (Ici b)
参数：h : a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Ioi_mem_nhdsSet_Ici`：∀ {α : Type u_1} [inst : LinearOrder α] [inst_1 : T
opologicalSpace α] [OrderClosedTopology α] {a b : α},   a < b → Set.Ioi a ∈ nhds
Set (Set.…
· 使用定理 `Set.Ioi_subset_Ici_self`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, S
et.Ioi a ⊆ Set.Ici a
-/
theorem Ici_mem_nhdsSet_Ici (h : a < b) : Ici a ∈ 𝓝ˢ (Ici b) :=
  mem_of_superset (Ioi_mem_nhdsSet_Ici h) Ioi_subset_Ici_self

/-!
### Lemmas about `Iix _ ∈ 𝓝ˢ (Set.Iic _)`
-/

/-
**Iio_mem_nhdsSet_Iic_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Iio_mem_nhdsSet_Iic_iff : Iio b in 𝓝ˢ (Iic a) ↔ a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ioi_mem_nhdsSet_Ici_iff`：Ioi_mem_nhdsSet_Ici_iff : Ioi a in 𝓝ˢ (Ici b) ↔
 a < b
· 使用定理 `instOrderClosedTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpac
e α] [inst_1 : Preorder α] [t : OrderClosedTopology α], OrderClosedTopology αᵒᵈ

--- 原说明 ---
### Lemmas about `Iix _ ∈ 𝓝ˢ (Set.Iic _)`
-/
theorem Iio_mem_nhdsSet_Iic_iff : Iio b ∈ 𝓝ˢ (Iic a) ↔ a < b :=
  Ioi_mem_nhdsSet_Ici_iff (α := αᵒᵈ)

alias ⟨_, Iio_mem_nhdsSet_Iic⟩ := Iio_mem_nhdsSet_Iic_iff
/-
**Iic_mem_nhdsSet_Iic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Iic_mem_nhdsSet_Iic (h : a < b) : Iic b in 𝓝ˢ (Iic a)
参数：h : a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ici_mem_nhdsSet_Ici`：Ici_mem_nhdsSet_Ici (h : a < b) : Ici a in 𝓝ˢ (Ici 
b)
· 使用定理 `instOrderClosedTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpac
e α] [inst_1 : Preorder α] [t : OrderClosedTopology α], OrderClosedTopology αᵒᵈ
-/
theorem Iic_mem_nhdsSet_Iic (h : a < b) : Iic b ∈ 𝓝ˢ (Iic a) :=
  Ici_mem_nhdsSet_Ici (α := αᵒᵈ) h

/-!
### Lemmas about `Ixx _ ?_ ∈ 𝓝ˢ (Set.Icc _ _)`
-/

/-
**Ioi_mem_nhdsSet_Icc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ioi_mem_nhdsSet_Icc (h : a < b) : Ioi a in 𝓝ˢ (Icc b c)
参数：h : a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhdsSet_mono`：nhdsSet_mono (h : s subseteq t) : 𝓝ˢ s <= 𝓝ˢ t
· 使用定理 `Set.Icc_subset_Ici_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Icc b a ⊆ Set.Ici b
· 使用定理 `Ioi_mem_nhdsSet_Ici`：∀ {α : Type u_1} [inst : LinearOrder α] [inst_1 : T
opologicalSpace α] [OrderClosedTopology α] {a b : α},   a < b → Set.Ioi a ∈ nhds
Set (Set.…

--- 原说明 ---
### Lemmas about `Ixx _ ?_ ∈ 𝓝ˢ (Set.Icc _ _)`
-/
theorem Ioi_mem_nhdsSet_Icc (h : a < b) : Ioi a ∈ 𝓝ˢ (Icc b c) :=
  nhdsSet_mono Icc_subset_Ici_self <| Ioi_mem_nhdsSet_Ici h
/-
**Ici_mem_nhdsSet_Icc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ici_mem_nhdsSet_Icc (h : a < b) : Ici a in 𝓝ˢ (Icc b c)
参数：h : a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Ioi_mem_nhdsSet_Icc`：Ioi_mem_nhdsSet_Icc (h : a < b) : Ioi a in 𝓝ˢ (Icc 
b c)
· 使用定理 `Set.Ioi_subset_Ici_self`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, S
et.Ioi a ⊆ Set.Ici a
-/
theorem Ici_mem_nhdsSet_Icc (h : a < b) : Ici a ∈ 𝓝ˢ (Icc b c) :=
  mem_of_superset (Ioi_mem_nhdsSet_Icc h) Ioi_subset_Ici_self
/-
**Iio_mem_nhdsSet_Icc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Iio_mem_nhdsSet_Icc (h : b < c) : Iio c in 𝓝ˢ (Icc a b)
参数：h : b < c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhdsSet_mono`：nhdsSet_mono (h : s subseteq t) : 𝓝ˢ s <= 𝓝ˢ t
· 使用定理 `Set.Icc_subset_Iic_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Icc a b ⊆ Set.Iic b
· 使用定理 `Iio_mem_nhdsSet_Iic`：∀ {α : Type u_1} [inst : LinearOrder α] [inst_1 : T
opologicalSpace α] [OrderClosedTopology α] {a b : α},   a < b → Set.Iio b ∈ nhds
Set (Set.…
-/
theorem Iio_mem_nhdsSet_Icc (h : b < c) : Iio c ∈ 𝓝ˢ (Icc a b) :=
  nhdsSet_mono Icc_subset_Iic_self <| Iio_mem_nhdsSet_Iic h
/-
**Iic_mem_nhdsSet_Icc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Iic_mem_nhdsSet_Icc (h : b < c) : Iic c in 𝓝ˢ (Icc a b)
参数：h : b < c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Iio_mem_nhdsSet_Icc`：Iio_mem_nhdsSet_Icc (h : b < c) : Iio c in 𝓝ˢ (Icc 
a b)
· 使用定理 `Set.Iio_subset_Iic_self`：Iio_subset_Iic_self : Iio a subseteq Iic a
-/
theorem Iic_mem_nhdsSet_Icc (h : b < c) : Iic c ∈ 𝓝ˢ (Icc a b) :=
  mem_of_superset (Iio_mem_nhdsSet_Icc h) Iio_subset_Iic_self
/-
**Ioo_mem_nhdsSet_Icc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ioo_mem_nhdsSet_Icc (h : a < b) (h' : c < d) : Ioo a d in 𝓝ˢ (Icc b c)
参数：h : a < b；h' : c < d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `Ioi_mem_nhdsSet_Icc`：Ioi_mem_nhdsSet_Icc (h : a < b) : Ioi a in 𝓝ˢ (Icc 
b c)
· 使用定理 `Iio_mem_nhdsSet_Icc`：Iio_mem_nhdsSet_Icc (h : b < c) : Iio c in 𝓝ˢ (Icc 
a b)
-/
theorem Ioo_mem_nhdsSet_Icc (h : a < b) (h' : c < d) : Ioo a d ∈ 𝓝ˢ (Icc b c) :=
  inter_mem (Ioi_mem_nhdsSet_Icc h) (Iio_mem_nhdsSet_Icc h')
/-
**Ico_mem_nhdsSet_Icc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ico_mem_nhdsSet_Icc (h : a < b) (h' : c < d) : Ico a d in 𝓝ˢ (Icc b c)
参数：h : a < b；h' : c < d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `Ici_mem_nhdsSet_Icc`：Ici_mem_nhdsSet_Icc (h : a < b) : Ici a in 𝓝ˢ (Icc 
b c)
· 使用定理 `Iio_mem_nhdsSet_Icc`：Iio_mem_nhdsSet_Icc (h : b < c) : Iio c in 𝓝ˢ (Icc 
a b)
-/
theorem Ico_mem_nhdsSet_Icc (h : a < b) (h' : c < d) : Ico a d ∈ 𝓝ˢ (Icc b c) :=
  inter_mem (Ici_mem_nhdsSet_Icc h) (Iio_mem_nhdsSet_Icc h')
/-
**Ioc_mem_nhdsSet_Icc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ioc_mem_nhdsSet_Icc (h : a < b) (h' : c < d) : Ioc a d in 𝓝ˢ (Icc b c)
参数：h : a < b；h' : c < d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `Ioi_mem_nhdsSet_Icc`：Ioi_mem_nhdsSet_Icc (h : a < b) : Ioi a in 𝓝ˢ (Icc 
b c)
· 使用定理 `Iic_mem_nhdsSet_Icc`：Iic_mem_nhdsSet_Icc (h : b < c) : Iic c in 𝓝ˢ (Icc 
a b)
-/
theorem Ioc_mem_nhdsSet_Icc (h : a < b) (h' : c < d) : Ioc a d ∈ 𝓝ˢ (Icc b c) :=
  inter_mem (Ioi_mem_nhdsSet_Icc h) (Iic_mem_nhdsSet_Icc h')
/-
**Icc_mem_nhdsSet_Icc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Icc_mem_nhdsSet_Icc (h : a < b) (h' : c < d) : Icc a d in 𝓝ˢ (Icc b c)
参数：h : a < b；h' : c < d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `Ici_mem_nhdsSet_Icc`：Ici_mem_nhdsSet_Icc (h : a < b) : Ici a in 𝓝ˢ (Icc 
b c)
· 使用定理 `Iic_mem_nhdsSet_Icc`：Iic_mem_nhdsSet_Icc (h : b < c) : Iic c in 𝓝ˢ (Icc 
a b)
-/
theorem Icc_mem_nhdsSet_Icc (h : a < b) (h' : c < d) : Icc a d ∈ 𝓝ˢ (Icc b c) :=
  inter_mem (Ici_mem_nhdsSet_Icc h) (Iic_mem_nhdsSet_Icc h')

/-!
### Lemmas about `Ixx _ ?_ ∈ 𝓝ˢ (Set.Ico _ _)`
-/

/-
**Ici_mem_nhdsSet_Ico** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ici_mem_nhdsSet_Ico (h : a < b) : Ici a in 𝓝ˢ (Ico b c)
参数：h : a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhdsSet_mono`：nhdsSet_mono (h : s subseteq t) : 𝓝ˢ s <= 𝓝ˢ t
· 使用定理 `Set.Ico_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ico b a ⊆ Set.Icc b a
· 使用定理 `Ici_mem_nhdsSet_Icc`：Ici_mem_nhdsSet_Icc (h : a < b) : Ici a in 𝓝ˢ (Icc 
b c)

--- 原说明 ---
### Lemmas about `Ixx _ ?_ ∈ 𝓝ˢ (Set.Ico _ _)`
-/
theorem Ici_mem_nhdsSet_Ico (h : a < b) : Ici a ∈ 𝓝ˢ (Ico b c) :=
  nhdsSet_mono Ico_subset_Icc_self <| Ici_mem_nhdsSet_Icc h
/-
**Ioi_mem_nhdsSet_Ico** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ioi_mem_nhdsSet_Ico (h : a < b) : Ioi a in 𝓝ˢ (Ico b c)
参数：h : a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhdsSet_mono`：nhdsSet_mono (h : s subseteq t) : 𝓝ˢ s <= 𝓝ˢ t
· 使用定理 `Set.Ico_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ico b a ⊆ Set.Icc b a
· 使用定理 `Ioi_mem_nhdsSet_Icc`：Ioi_mem_nhdsSet_Icc (h : a < b) : Ioi a in 𝓝ˢ (Icc 
b c)
-/
theorem Ioi_mem_nhdsSet_Ico (h : a < b) : Ioi a ∈ 𝓝ˢ (Ico b c) :=
  nhdsSet_mono Ico_subset_Icc_self <| Ioi_mem_nhdsSet_Icc h
/-
**Iio_mem_nhdsSet_Ico** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Iio_mem_nhdsSet_Ico (h : b <= c) : Iio c in 𝓝ˢ (Ico a b)
参数：h : b <= c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhdsSet_mono`：nhdsSet_mono (h : s subseteq t) : 𝓝ˢ s <= 𝓝ˢ t
· 使用定理 `Set.Ico_subset_Iio_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ico a b ⊆ Set.Iio b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsSet_Iio`：∀ {α : Type u_1} [inst : LinearOrder α] [inst_1 : Topologic
alSpace α] [OrderClosedTopology α] {a : α},   nhdsSet (Set.Iio a) = Filter.princ
i…
-/
theorem Iio_mem_nhdsSet_Ico (h : b ≤ c) : Iio c ∈ 𝓝ˢ (Ico a b) :=
  nhdsSet_mono Ico_subset_Iio_self <| by simpa
/-
**Iic_mem_nhdsSet_Ico** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Iic_mem_nhdsSet_Ico (h : b <= c) : Iic c in 𝓝ˢ (Ico a b)
参数：h : b <= c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Iio_mem_nhdsSet_Ico`：Iio_mem_nhdsSet_Ico (h : b <= c) : Iio c in 𝓝ˢ (Ico
 a b)
· 使用定理 `Set.Iio_subset_Iic_self`：Iio_subset_Iic_self : Iio a subseteq Iic a
-/
theorem Iic_mem_nhdsSet_Ico (h : b ≤ c) : Iic c ∈ 𝓝ˢ (Ico a b) :=
  mem_of_superset (Iio_mem_nhdsSet_Ico h) Iio_subset_Iic_self
/-
**Ioo_mem_nhdsSet_Ico** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ioo_mem_nhdsSet_Ico (h : a < b) (h' : c <= d) : Ioo a d in 𝓝ˢ (Ico b c)
参数：h : a < b；h' : c <= d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `Ioi_mem_nhdsSet_Ico`：Ioi_mem_nhdsSet_Ico (h : a < b) : Ioi a in 𝓝ˢ (Ico 
b c)
· 使用定理 `Iio_mem_nhdsSet_Ico`：Iio_mem_nhdsSet_Ico (h : b <= c) : Iio c in 𝓝ˢ (Ico
 a b)
-/
theorem Ioo_mem_nhdsSet_Ico (h : a < b) (h' : c ≤ d) : Ioo a d ∈ 𝓝ˢ (Ico b c) :=
  inter_mem (Ioi_mem_nhdsSet_Ico h) (Iio_mem_nhdsSet_Ico h')
/-
**Icc_mem_nhdsSet_Ico** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Icc_mem_nhdsSet_Ico (h : a < b) (h' : c <= d) : Icc a d in 𝓝ˢ (Ico b c)
参数：h : a < b；h' : c <= d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `Ici_mem_nhdsSet_Ico`：Ici_mem_nhdsSet_Ico (h : a < b) : Ici a in 𝓝ˢ (Ico 
b c)
· 使用定理 `Iic_mem_nhdsSet_Ico`：Iic_mem_nhdsSet_Ico (h : b <= c) : Iic c in 𝓝ˢ (Ico
 a b)
-/
theorem Icc_mem_nhdsSet_Ico (h : a < b) (h' : c ≤ d) : Icc a d ∈ 𝓝ˢ (Ico b c) :=
  inter_mem (Ici_mem_nhdsSet_Ico h) (Iic_mem_nhdsSet_Ico h')
/-
**Ioc_mem_nhdsSet_Ico** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ioc_mem_nhdsSet_Ico (h : a < b) (h' : c <= d) : Ioc a d in 𝓝ˢ (Ico b c)
参数：h : a < b；h' : c <= d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `Ioi_mem_nhdsSet_Ico`：Ioi_mem_nhdsSet_Ico (h : a < b) : Ioi a in 𝓝ˢ (Ico 
b c)
· 使用定理 `Iic_mem_nhdsSet_Ico`：Iic_mem_nhdsSet_Ico (h : b <= c) : Iic c in 𝓝ˢ (Ico
 a b)
-/
theorem Ioc_mem_nhdsSet_Ico (h : a < b) (h' : c ≤ d) : Ioc a d ∈ 𝓝ˢ (Ico b c) :=
  inter_mem (Ioi_mem_nhdsSet_Ico h) (Iic_mem_nhdsSet_Ico h')
/-
**Ico_mem_nhdsSet_Ico** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ico_mem_nhdsSet_Ico (h : a < b) (h' : c <= d) : Ico a d in 𝓝ˢ (Ico b c)
参数：h : a < b；h' : c <= d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `Ici_mem_nhdsSet_Ico`：Ici_mem_nhdsSet_Ico (h : a < b) : Ici a in 𝓝ˢ (Ico 
b c)
· 使用定理 `Iio_mem_nhdsSet_Ico`：Iio_mem_nhdsSet_Ico (h : b <= c) : Iio c in 𝓝ˢ (Ico
 a b)
-/
theorem Ico_mem_nhdsSet_Ico (h : a < b) (h' : c ≤ d) : Ico a d ∈ 𝓝ˢ (Ico b c) :=
  inter_mem (Ici_mem_nhdsSet_Ico h) (Iio_mem_nhdsSet_Ico h')

/-!
### Lemmas about `Ixx _ ?_ ∈ 𝓝ˢ (Set.Ioc _ _)`
-/

/-
**Ioi_mem_nhdsSet_Ioc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ioi_mem_nhdsSet_Ioc (h : a <= b) : Ioi a in 𝓝ˢ (Ioc b c)
参数：h : a <= b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhdsSet_mono`：nhdsSet_mono (h : s subseteq t) : 𝓝ˢ s <= 𝓝ˢ t
· 使用定理 `Set.Ioc_subset_Ioi_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc b a ⊆ Set.Ioi b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsSet_Ioi`：∀ {α : Type u_1} [inst : LinearOrder α] [inst_1 : Topologic
alSpace α] [OrderClosedTopology α] {a : α},   nhdsSet (Set.Ioi a) = Filter.princ
i…

--- 原说明 ---
### Lemmas about `Ixx _ ?_ ∈ 𝓝ˢ (Set.Ioc _ _)`
-/
theorem Ioi_mem_nhdsSet_Ioc (h : a ≤ b) : Ioi a ∈ 𝓝ˢ (Ioc b c) :=
  nhdsSet_mono Ioc_subset_Ioi_self <| by simpa
/-
**Iio_mem_nhdsSet_Ioc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Iio_mem_nhdsSet_Ioc (h : b < c) : Iio c in 𝓝ˢ (Ioc a b)
参数：h : b < c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhdsSet_mono`：nhdsSet_mono (h : s subseteq t) : 𝓝ˢ s <= 𝓝ˢ t
· 使用定理 `Set.Ioc_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc a b ⊆ Set.Icc a b
· 使用定理 `Iio_mem_nhdsSet_Icc`：Iio_mem_nhdsSet_Icc (h : b < c) : Iio c in 𝓝ˢ (Icc 
a b)
-/
theorem Iio_mem_nhdsSet_Ioc (h : b < c) : Iio c ∈ 𝓝ˢ (Ioc a b) :=
  nhdsSet_mono Ioc_subset_Icc_self <| Iio_mem_nhdsSet_Icc h
/-
**Ici_mem_nhdsSet_Ioc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ici_mem_nhdsSet_Ioc (h : a <= b) : Ici a in 𝓝ˢ (Ioc b c)
参数：h : a <= b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Ioi_mem_nhdsSet_Ioc`：Ioi_mem_nhdsSet_Ioc (h : a <= b) : Ioi a in 𝓝ˢ (Ioc
 b c)
· 使用定理 `Set.Ioi_subset_Ici_self`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, S
et.Ioi a ⊆ Set.Ici a
-/
theorem Ici_mem_nhdsSet_Ioc (h : a ≤ b) : Ici a ∈ 𝓝ˢ (Ioc b c) :=
  mem_of_superset (Ioi_mem_nhdsSet_Ioc h) Ioi_subset_Ici_self
/-
**Iic_mem_nhdsSet_Ioc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Iic_mem_nhdsSet_Ioc (h : b < c) : Iic c in 𝓝ˢ (Ioc a b)
参数：h : b < c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhdsSet_mono`：nhdsSet_mono (h : s subseteq t) : 𝓝ˢ s <= 𝓝ˢ t
· 使用定理 `Set.Ioc_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc a b ⊆ Set.Icc a b
· 使用定理 `Iic_mem_nhdsSet_Icc`：Iic_mem_nhdsSet_Icc (h : b < c) : Iic c in 𝓝ˢ (Icc 
a b)
-/
theorem Iic_mem_nhdsSet_Ioc (h : b < c) : Iic c ∈ 𝓝ˢ (Ioc a b) :=
  nhdsSet_mono Ioc_subset_Icc_self <| Iic_mem_nhdsSet_Icc h
/-
**Ioo_mem_nhdsSet_Ioc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ioo_mem_nhdsSet_Ioc (h : a <= b) (h' : c < d) : Ioo a d in 𝓝ˢ (Ioc b c)
参数：h : a <= b；h' : c < d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `Ioi_mem_nhdsSet_Ioc`：Ioi_mem_nhdsSet_Ioc (h : a <= b) : Ioi a in 𝓝ˢ (Ioc
 b c)
· 使用定理 `Iio_mem_nhdsSet_Ioc`：Iio_mem_nhdsSet_Ioc (h : b < c) : Iio c in 𝓝ˢ (Ioc 
a b)
-/
theorem Ioo_mem_nhdsSet_Ioc (h : a ≤ b) (h' : c < d) : Ioo a d ∈ 𝓝ˢ (Ioc b c) :=
  inter_mem (Ioi_mem_nhdsSet_Ioc h) (Iio_mem_nhdsSet_Ioc h')
/-
**Icc_mem_nhdsSet_Ioc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Icc_mem_nhdsSet_Ioc (h : a <= b) (h' : c < d) : Icc a d in 𝓝ˢ (Ioc b c)
参数：h : a <= b；h' : c < d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `Ici_mem_nhdsSet_Ioc`：Ici_mem_nhdsSet_Ioc (h : a <= b) : Ici a in 𝓝ˢ (Ioc
 b c)
· 使用定理 `Iic_mem_nhdsSet_Ioc`：Iic_mem_nhdsSet_Ioc (h : b < c) : Iic c in 𝓝ˢ (Ioc 
a b)
-/
theorem Icc_mem_nhdsSet_Ioc (h : a ≤ b) (h' : c < d) : Icc a d ∈ 𝓝ˢ (Ioc b c) :=
  inter_mem (Ici_mem_nhdsSet_Ioc h) (Iic_mem_nhdsSet_Ioc h')
/-
**Ioc_mem_nhdsSet_Ioc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ioc_mem_nhdsSet_Ioc (h : a <= b) (h' : c < d) : Ioc a d in 𝓝ˢ (Ioc b c)
参数：h : a <= b；h' : c < d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `Ioi_mem_nhdsSet_Ioc`：Ioi_mem_nhdsSet_Ioc (h : a <= b) : Ioi a in 𝓝ˢ (Ioc
 b c)
· 使用定理 `Iic_mem_nhdsSet_Ioc`：Iic_mem_nhdsSet_Ioc (h : b < c) : Iic c in 𝓝ˢ (Ioc 
a b)
-/
theorem Ioc_mem_nhdsSet_Ioc (h : a ≤ b) (h' : c < d) : Ioc a d ∈ 𝓝ˢ (Ioc b c) :=
  inter_mem (Ioi_mem_nhdsSet_Ioc h) (Iic_mem_nhdsSet_Ioc h')
/-
**Ico_mem_nhdsSet_Ioc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ico_mem_nhdsSet_Ioc (h : a <= b) (h' : c < d) : Ico a d in 𝓝ˢ (Ioc b c)
参数：h : a <= b；h' : c < d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `Ici_mem_nhdsSet_Ioc`：Ici_mem_nhdsSet_Ioc (h : a <= b) : Ici a in 𝓝ˢ (Ioc
 b c)
· 使用定理 `Iio_mem_nhdsSet_Ioc`：Iio_mem_nhdsSet_Ioc (h : b < c) : Iio c in 𝓝ˢ (Ioc 
a b)
-/
theorem Ico_mem_nhdsSet_Ioc (h : a ≤ b) (h' : c < d) : Ico a d ∈ 𝓝ˢ (Ioc b c) :=
  inter_mem (Ici_mem_nhdsSet_Ioc h) (Iio_mem_nhdsSet_Ioc h')

end OrderClosedTopology

/-!
### Filter bases of `𝓝ˢ (Iic a)` and `𝓝ˢ (Ici a)`
-/

variable {α : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]

/-
**hasBasis_nhdsSet_Iic_Iio** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasBasis_nhdsSet_Iic_Iio (a : α) [h : Nonempty (Ioi a)] : HasBasis (𝓝ˢ (Ii
c a)) (a < ·) Iio
参数：a : α；Ioi a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_Ico_subset_of_mem_nhds`：∀ {α : Type u} [inst : TopologicalSpace α
] [inst_1 : LinearOrder α] [OrderTopology α] {a : α} {s : Set α},   s ∈ nhds a →
 (∃ l, a < l) → ∃ l…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.mem_principal`：∀ {α : Type u_1} {s t : Set α}, s ∈ Filter.princip
al t ↔ t ⊆ s
· 使用定理 `Filter.mem_sup`：mem_sup {f g : Filter α} {s : Set α} : s in f ⊔ g ↔ s in
 f ∧ s in g
· 使用定理 `nhdsSet_Iic`：nhdsSet_Iic : 𝓝ˢ (Iic a) = 𝓝 a ⊔ 𝓟 (Iio a)
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.nonempty_coe_sort`：nonempty_coe_sort {s : Set α} : Nonempty ↥s ↔ s.N
onempty
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.Iio_subset_Iio_union_Ico`：Iio_subset_Iio_union_Ico : Iio b subseteq 
Iio a union Ico a b
· 使用定理 `Set.union_subset`：union_subset {s t r : Set α} (sr : s subseteq r) (tr :
 t subseteq r) : s union t subseteq r
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Iio_mem_nhdsSet_Iic`：∀ {α : Type u_1} [inst : LinearOrder α] [inst_1 : T
opologicalSpace α] [OrderClosedTopology α] {a b : α},   a < b → Set.Iio b ∈ nhds
Set (Set.…
-/
theorem hasBasis_nhdsSet_Iic_Iio (a : α) [h : Nonempty (Ioi a)] :
    HasBasis (𝓝ˢ (Iic a)) (a < ·) Iio := by
  refine ⟨fun s ↦ ⟨fun hs ↦ ?_, fun ⟨b, hab, hb⟩ ↦ mem_of_superset (Iio_mem_nhdsSet_Iic hab) hb⟩⟩
  rw [nhdsSet_Iic, mem_sup, mem_principal] at hs
  rcases exists_Ico_subset_of_mem_nhds hs.1 (Set.nonempty_coe_sort.1 h) with ⟨b, hab, hbs⟩
  exact ⟨b, hab, Iio_subset_Iio_union_Ico.trans (union_subset hs.2 hbs)⟩
/-
**hasBasis_nhdsSet_Iic_Iic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasBasis_nhdsSet_Iic_Iic (a : α) [NeBot (𝓝[>] a)] : HasBasis (𝓝ˢ (Iic a)) 
(a < ·) Iic
参数：a : α；𝓝[>] a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.to_subtype`：∀ {α : Type u} {s : Set α}, s.Nonempty → Nonemp
ty ↑s
· 使用定理 `Filter.nonempty_of_mem`：nonempty_of_mem {f : Filter α} [hf : NeBot f] {s
 : Set α} (hs : s in f) : s.Nonempty
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Filter.HasBasis.to_hasBasis`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort 
u_5} {l : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : ι' →
 Set α},   l.HasB…
· 使用定理 `hasBasis_nhdsSet_Iic_Iio`：hasBasis_nhdsSet_Iic_Iio (a : α) [h : Nonempty
 (Ioi a)] : HasBasis (𝓝ˢ (Iic a)) (a < ·) Iio
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Ioo_mem_nhdsGT`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Lin
earOrder α] [ClosedIciTopology α] {a b : α},   b < a → Set.Ioo b a ∈ nhdsWithin 
b (S…
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `Set.Iio_subset_Iic_self`：Iio_subset_Iic_self : Iio a subseteq Iic a
-/
theorem hasBasis_nhdsSet_Iic_Iic (a : α) [NeBot (𝓝[>] a)] :
    HasBasis (𝓝ˢ (Iic a)) (a < ·) Iic := by
  have : Nonempty (Ioi a) :=
    (Filter.nonempty_of_mem (self_mem_nhdsWithin : Ioi a ∈ 𝓝[>] a)).to_subtype
  refine (hasBasis_nhdsSet_Iic_Iio _).to_hasBasis
    (fun c hc ↦ ?_) (fun _ h ↦ ⟨_, h, Iio_subset_Iic_self⟩)
  simpa only [Iic_subset_Iio] using! Filter.nonempty_of_mem (Ioo_mem_nhdsGT hc)

@[simp]
/-
**Iic_mem_nhdsSet_Iic_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Iic_mem_nhdsSet_Iic_iff {a b : α} [NeBot (𝓝[>] b)] : Iic a in 𝓝ˢ (Iic b) ↔
 b < a
参数：𝓝[>] b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `hasBasis_nhdsSet_Iic_Iic`：hasBasis_nhdsSet_Iic_Iic (a : α) [NeBot (𝓝[>] 
a)] : HasBasis (𝓝ˢ (Iic a)) (a < ·) Iic
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.Iic_subset_Iic`：Iic_subset_Iic : Iic a subseteq Iic b ↔ a <= b
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
theorem Iic_mem_nhdsSet_Iic_iff {a b : α} [NeBot (𝓝[>] b)] : Iic a ∈ 𝓝ˢ (Iic b) ↔ b < a :=
  (hasBasis_nhdsSet_Iic_Iic b).mem_iff.trans
    ⟨fun ⟨_c, hbc, hca⟩ ↦ hbc.trans_le (Iic_subset_Iic.1 hca), fun h ↦ ⟨_, h, Subset.rfl⟩⟩
/-
**hasBasis_nhdsSet_Ici_Ioi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasBasis_nhdsSet_Ici_Ioi (a : α) [Nonempty (Iio a)] : HasBasis (𝓝ˢ (Ici a)
) (· < a) Ioi
参数：a : α；Iio a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasBasis_nhdsSet_Iic_Iio`：hasBasis_nhdsSet_Iic_Iio (a : α) [h : Nonempty
 (Ioi a)] : HasBasis (𝓝ˢ (Iic a)) (a < ·) Iio
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
-/
theorem hasBasis_nhdsSet_Ici_Ioi (a : α) [Nonempty (Iio a)] :
    HasBasis (𝓝ˢ (Ici a)) (· < a) Ioi :=
  have : Nonempty (Ioi (toDual a)) := ‹_›; hasBasis_nhdsSet_Iic_Iio (toDual a)
/-
**hasBasis_nhdsSet_Ici_Ici** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasBasis_nhdsSet_Ici_Ici (a : α) [NeBot (𝓝[<] a)] : HasBasis (𝓝ˢ (Ici a)) 
(· < a) Ici
参数：a : α；𝓝[<] a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasBasis_nhdsSet_Iic_Iic`：hasBasis_nhdsSet_Iic_Iic (a : α) [NeBot (𝓝[>] 
a)] : HasBasis (𝓝ˢ (Iic a)) (a < ·) Iic
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
-/
theorem hasBasis_nhdsSet_Ici_Ici (a : α) [NeBot (𝓝[<] a)] :
    HasBasis (𝓝ˢ (Ici a)) (· < a) Ici :=
  have : NeBot (𝓝[>] (toDual a)) := ‹_›; hasBasis_nhdsSet_Iic_Iic (toDual a)

@[simp]
/-
**Ici_mem_nhdsSet_Ici_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ici_mem_nhdsSet_Ici_iff {a b : α} [NeBot (𝓝[<] b)] : Ici a in 𝓝ˢ (Ici b) ↔
 a < b
参数：𝓝[<] b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iic_mem_nhdsSet_Iic_iff`：Iic_mem_nhdsSet_Iic_iff {a b : α} [NeBot (𝓝[>] 
b)] : Iic a in 𝓝ˢ (Iic b) ↔ b < a
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
-/
theorem Ici_mem_nhdsSet_Ici_iff {a b : α} [NeBot (𝓝[<] b)] : Ici a ∈ 𝓝ˢ (Ici b) ↔ a < b :=
  have : NeBot (𝓝[>] (toDual b)) := ‹_›; Iic_mem_nhdsSet_Iic_iff (a := toDual a) (b := toDual b)
