/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yury Kudryashov
-/
module

public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Order.Interval.Set.LinearOrder
public import Mathlib.Order.MinMax

/-!
# Extra lemmas about intervals

This file contains lemmas about intervals that cannot be included into
`Mathlib/Order/Interval/Set/Basic.lean` because this would create an `import` cycle. Namely, lemmas
in this file can use definitions from `Data.Set.Lattice`, including `Disjoint`.

We consider various intersections and unions of half infinite intervals.
-/

public section


universe u v w

variable {ι : Sort u} {α : Type v} {β : Type w}

open Set

open OrderDual (toDual)

namespace Set

section Preorder

variable [Preorder α] {a b c : α}

to_dual_name_hint Disjoint Disjoint, Left Right

@[to_dual (attr := simp)]
/-
**Set.Iic_disjoint_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iic_disjoint_Ioi (h : a <= b) : Disjoint (Iic a) (Ioi b)
参数：h : a <= b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
-/
theorem Iic_disjoint_Ioi (h : a ≤ b) : Disjoint (Iic a) (Ioi b) :=
  disjoint_left.mpr fun _ ha hb => (h.trans_lt hb).not_ge ha

@[to_dual (attr := simp)]
/-
**Set.Iio_disjoint_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iio_disjoint_Ici (h : a <= b) : Disjoint (Iio a) (Ici b)
参数：h : a <= b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `LE.le.trans_lt'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b ≤ a
 → c < b → c < a
-/
theorem Iio_disjoint_Ici (h : a ≤ b) : Disjoint (Iio a) (Ici b) :=
  disjoint_left.mpr fun _ ha hb => (h.trans_lt' ha).not_ge hb

@[simp]
/-
**Set.Iic_disjoint_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iic_disjoint_Ioc (h : a <= b) : Disjoint (Iic a) (Ioc b c)
参数：h : a <= b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.mono`：Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.s
upport <= f.support) (hg : y.support <= g.support) : Disjoint x y
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Set.Ioc_subset_Ioi_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc b a ⊆ Set.Ioi b
· 使用定理 `Set.Iic_disjoint_Ioi`：Iic_disjoint_Ioi (h : a <= b) : Disjoint (Iic a) (
Ioi b)
-/
theorem Iic_disjoint_Ioc (h : a ≤ b) : Disjoint (Iic a) (Ioc b c) :=
  (Iic_disjoint_Ioi h).mono le_rfl Ioc_subset_Ioi_self

@[simp]
/-
**Set.Ioc_disjoint_Ioc_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioc_disjoint_Ioc_of_le {d : α} (h : b <= c) : Disjoint (Ioc a b) (Ioc c d)
参数：h : b <= c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.mono`：Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.s
upport <= f.support) (hg : y.support <= g.support) : Disjoint x y
· 使用定理 `Set.Ioc_subset_Iic_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc a b ⊆ Set.Iic b
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Set.Iic_disjoint_Ioc`：Iic_disjoint_Ioc (h : a <= b) : Disjoint (Iic a) (
Ioc b c)
-/
theorem Ioc_disjoint_Ioc_of_le {d : α} (h : b ≤ c) : Disjoint (Ioc a b) (Ioc c d) :=
  (Iic_disjoint_Ioc h).mono Ioc_subset_Iic_self le_rfl

@[simp]
/-
**Set.Ico_disjoint_Ico_same** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ico_disjoint_Ico_same : Disjoint (Ico a b) (Ico b c)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem Ico_disjoint_Ico_same : Disjoint (Ico a b) (Ico b c) :=
  disjoint_left.mpr fun _ hab hbc => hab.2.not_ge hbc.1

@[to_dual (attr := simp)]
/-
**Set.Ici_disjoint_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ici_disjoint_Iic : Disjoint (Ici a) (Iic b) ↔ ¬a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.disjoint_iff_inter_eq_empty`：disjoint_iff_inter_eq_empty : Disjoint 
s t ↔ s inter t = ∅
· 使用定理 `Set.Ici_inter_Iic`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.I
ci a ∩ Set.Iic b = Set.Icc a b
· 使用定理 `Set.Icc_eq_empty_iff`：Icc_eq_empty_iff : Icc a b = ∅ ↔ ¬a <= b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Ici_disjoint_Iic : Disjoint (Ici a) (Iic b) ↔ ¬a ≤ b := by
  rw [Set.disjoint_iff_inter_eq_empty, Ici_inter_Iic, Icc_eq_empty_iff]

@[simp]
/-
**Set.Ioc_disjoint_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioc_disjoint_Ioi (h : b <= c) : Disjoint (Ioc a b) (Ioi c)
参数：h : b <= c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Ioc_disjoint_Ioi (h : b ≤ c) : Disjoint (Ioc a b) (Ioi c) :=
  disjoint_left.mpr (fun _ hx hy ↦ (hx.2.trans h).not_gt hy)
/-
**Set.Ioc_disjoint_Ioi_same** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioc_disjoint_Ioi_same : Disjoint (Ioc a b) (Ioi b)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Ioc_disjoint_Ioi`：Ioc_disjoint_Ioi (h : b <= c) : Disjoint (Ioc a b)
 (Ioi c)
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem Ioc_disjoint_Ioi_same : Disjoint (Ioc a b) (Ioi b) :=
  Ioc_disjoint_Ioi le_rfl

@[to_dual]
/-
**Set.Ioi_disjoint_Iio_of_not_lt** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioi_disjoint_Iio_of_not_lt (h : ¬a < b) : Disjoint (Ioi a) (Iio b)
参数：h : ¬a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
-/
theorem Ioi_disjoint_Iio_of_not_lt (h : ¬a < b) : Disjoint (Ioi a) (Iio b) :=
  disjoint_left.mpr fun _ hx hy ↦ h (hx.trans hy)

@[to_dual]
/-
**Set.Ioi_disjoint_Iio_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioi_disjoint_Iio_of_le (h : a <= b) : Disjoint (Ioi b) (Iio a)
参数：h : a <= b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Ioi_disjoint_Iio_of_not_lt`：Ioi_disjoint_Iio_of_not_lt (h : ¬a < b) 
: Disjoint (Ioi a) (Iio b)
· 使用定理 `not_lt_of_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
-/
theorem Ioi_disjoint_Iio_of_le (h : a ≤ b) : Disjoint (Ioi b) (Iio a) :=
  Ioi_disjoint_Iio_of_not_lt (not_lt_of_ge h)

@[to_dual]
/-
**Set.Ioi_disjoint_Iio_same** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioi_disjoint_Iio_same : Disjoint (Ioi a) (Iio a)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Ioi_disjoint_Iio_of_le`：Ioi_disjoint_Iio_of_le (h : a <= b) : Disjoi
nt (Ioi b) (Iio a)
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem Ioi_disjoint_Iio_same : Disjoint (Ioi a) (Iio a) :=
  Ioi_disjoint_Iio_of_le le_rfl

@[to_dual (attr := simp)]
/-
**Set.Ioi_disjoint_Iio_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioi_disjoint_Iio_iff [DenselyOrdered α] : Disjoint (Ioi a) (Iio b) ↔ ¬a < 
b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
· 使用定理 `Disjoint.notMem_of_mem_left`：∀ {α : Type u} {s t : Set α}, Disjoint s t 
→ ∀ ⦃a : α⦄, a ∈ s → a ∉ t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.Ioi_disjoint_Iio_of_not_lt`：Ioi_disjoint_Iio_of_not_lt (h : ¬a < b) 
: Disjoint (Ioi a) (Iio b)
-/
theorem Ioi_disjoint_Iio_iff [DenselyOrdered α] : Disjoint (Ioi a) (Iio b) ↔ ¬a < b :=
  ⟨fun h hab ↦ (exists_between hab).elim
    fun _ hc ↦ h.notMem_of_mem_left hc.left hc.right,
    Ioi_disjoint_Iio_of_not_lt⟩

@[to_dual (attr := simp)]
/-
**Set.iUnion_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_Iic : ⋃ a : α, Iic a = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.iUnion_eq_univ_iff`：iUnion_eq_univ_iff {f : ι -> Set α} : ⋃ i, f i =
 univ ↔ forall x, exists i, x in f i
· 使用定理 `Set.self_mem_Iic`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, a ∈ Set.
Iic a
-/
theorem iUnion_Iic : ⋃ a : α, Iic a = univ :=
  iUnion_eq_univ_iff.2 fun x => ⟨x, self_mem_Iic⟩

@[to_dual (attr := simp)]
/-
**Set.iUnion_Icc_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_Icc_right (a : α) : ⋃ b, Icc a b = Ici a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.iUnion_Iic`：iUnion_Iic : ⋃ a : α, Iic a = univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iUnion_Icc_right (a : α) : ⋃ b, Icc a b = Ici a := by
  simp only [← Ici_inter_Iic, ← inter_iUnion, iUnion_Iic, inter_univ]

@[to_dual (attr := simp)]
/-
**Set.iUnion_Ioc_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_Ioc_right (a : α) : ⋃ b, Ioc a b = Ioi a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.iUnion_Iic`：iUnion_Iic : ⋃ a : α, Iic a = univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iUnion_Ioc_right (a : α) : ⋃ b, Ioc a b = Ioi a := by
  simp only [← Ioi_inter_Iic, ← inter_iUnion, iUnion_Iic, inter_univ]

@[to_dual (attr := simp)]
/-
**Set.iUnion_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_Iio [NoMaxOrder α] : ⋃ a : α, Iio a = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.iUnion_eq_univ_iff`：iUnion_eq_univ_iff {f : ι -> Set α} : ⋃ i, f i =
 univ ↔ forall x, exists i, x in f i
· 使用定理 `NoMaxOrder.exists_gt`：∀ {α : Type u_3} {inst : LT α} [self : NoMaxOrder 
α] (a : α), ∃ b, a < b
-/
theorem iUnion_Iio [NoMaxOrder α] : ⋃ a : α, Iio a = univ :=
  iUnion_eq_univ_iff.2 exists_gt

@[to_dual (attr := simp)]
/-
**Set.iUnion_Ico_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_Ico_right [NoMaxOrder α] (a : α) : ⋃ b, Ico a b = Ici a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.iUnion_Iio`：iUnion_Iio [NoMaxOrder α] : ⋃ a : α, Iio a = univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iUnion_Ico_right [NoMaxOrder α] (a : α) : ⋃ b, Ico a b = Ici a := by
  simp only [← Ici_inter_Iio, ← inter_iUnion, iUnion_Iio, inter_univ]

@[to_dual (attr := simp)]
/-
**Set.iUnion_Ioo_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_Ioo_right [NoMaxOrder α] (a : α) : ⋃ b, Ioo a b = Ioi a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.iUnion_Iio`：iUnion_Iio [NoMaxOrder α] : ⋃ a : α, Iio a = univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iUnion_Ioo_right [NoMaxOrder α] (a : α) : ⋃ b, Ioo a b = Ioi a := by
  simp only [← Ioi_inter_Iio, ← inter_iUnion, iUnion_Iio, inter_univ]

end Preorder

section LinearOrder

variable [LinearOrder α] {a₁ a₂ b₁ b₂ : α}

@[simp]
/-
**Set.Ico_disjoint_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ico_disjoint_Ico : Disjoint (Ico a₁ a₂) (Ico b₁ b₂) ↔ min a₂ b₂ <= max a₁ 
b₁
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Ico_inter_Ico`：Ico_inter_Ico : Ico a₁ b₁ inter Ico a₂ b₂ = Ico (a₁ ⊔
 a₂) (b₁ ⊓ b₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Ico_disjoint_Ico : Disjoint (Ico a₁ a₂) (Ico b₁ b₂) ↔ min a₂ b₂ ≤ max a₁ b₁ := by
  simp_rw [Set.disjoint_iff_inter_eq_empty, Ico_inter_Ico, Ico_eq_empty_iff, not_lt]

@[simp]
/-
**Set.Ioc_disjoint_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioc_disjoint_Ioc : Disjoint (Ioc a₁ a₂) (Ioc b₁ b₂) ↔ min a₂ b₂ <= max a₁ 
b₁
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Ico_disjoint_Ico`：Ico_disjoint_Ico : Disjoint (Ico a₁ a₂) (Ico b₁ b₂
) ↔ min a₂ b₂ <= max a₁ b₁
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.Ico_toDual`：Ico_toDual : Ico (toDual a) (toDual b) = ofDual ⁻¹' Ioc 
b a
-/
theorem Ioc_disjoint_Ioc : Disjoint (Ioc a₁ a₂) (Ioc b₁ b₂) ↔ min a₂ b₂ ≤ max a₁ b₁ := by
  have h : _ ↔ min (toDual a₁) (toDual b₁) ≤ max (toDual a₂) (toDual b₂) := Ico_disjoint_Ico
  simpa only [Ico_toDual] using! h

@[simp]
/-
**Set.Ioo_disjoint_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioo_disjoint_Ioo [DenselyOrdered α] : Disjoint (Set.Ioo a₁ a₂) (Set.Ioo b₁
 b₂) ↔ min a₂ b₂ <= max a₁ b₁
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Ioo_inter_Ioo`：Ioo_inter_Ioo : Ioo a₁ b₁ inter Ioo a₂ b₂ = Ioo (a₁ ⊔
 a₂) (b₁ ⊓ b₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Ioo_disjoint_Ioo [DenselyOrdered α] :
    Disjoint (Set.Ioo a₁ a₂) (Set.Ioo b₁ b₂) ↔ min a₂ b₂ ≤ max a₁ b₁ := by
  simp_rw [Set.disjoint_iff_inter_eq_empty, Ioo_inter_Ioo, Ioo_eq_empty_iff, not_lt]

/-- If two half-open intervals are disjoint and the endpoint of one lies in the other,
  then it must be equal to the endpoint of the other. -/
/-
**Set.eq_of_Ico_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：eq_of_Ico_disjoint {x₁ x₂ y₁ y₂ : α} (h : Disjoint (Ico x₁ x₂) (Ico y₁ y₂)
) (hx : x₁ < x₂) (h2 : x₂ in Ico y₁ y₂) : y₁ = x₂
参数：h : Disjoint (Ico x₁ x₂) (Ico y₁ y₂)；hx : x₁ < x₂；h2 : x₂ in Ico y₁ y₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_max_iff`：le_max_iff : a <= max b c ↔ a <= b ∨ a <= c
· 使用引理 `min_eq_left`：min_eq_left (h : a <= b) : min a b = a
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.Ico_disjoint_Ico`：Ico_disjoint_Ico : Disjoint (Ico a₁ a₂) (Ico b₁ b₂
) ↔ min a₂ b₂ <= max a₁ b₁
· 使用定理 `not_lt_of_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a

--- 原说明 ---
If two half-open intervals are disjoint and the endpoint of one lies in the othe
r,
  then it must be equal to the endpoint of the other.
-/
theorem eq_of_Ico_disjoint {x₁ x₂ y₁ y₂ : α} (h : Disjoint (Ico x₁ x₂) (Ico y₁ y₂)) (hx : x₁ < x₂)
    (h2 : x₂ ∈ Ico y₁ y₂) : y₁ = x₂ := by
  rw [Ico_disjoint_Ico, min_eq_left (le_of_lt h2.2), le_max_iff] at h
  apply le_antisymm h2.1
  exact h.elim (fun h => absurd hx (not_lt_of_ge h)) id

@[simp]
/-
**Set.iUnion_Ico_eq_Iio_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_Ico_eq_Iio_self_iff {f : ι -> α} {a : α} : ⋃ i, Ico (f i) a = Iio a
 ↔ forall x < a, exists i, f i <= x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem iUnion_Ico_eq_Iio_self_iff {f : ι → α} {a : α} :
    ⋃ i, Ico (f i) a = Iio a ↔ ∀ x < a, ∃ i, f i ≤ x := by
  simp [← Ici_inter_Iio, ← iUnion_inter, subset_def]

@[simp]
/-
**Set.iUnion_Ioc_eq_Ioi_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_Ioc_eq_Ioi_self_iff {f : ι -> α} {a : α} : ⋃ i, Ioc a (f i) = Ioi a
 ↔ forall x, a < x -> exists i, x <= f i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem iUnion_Ioc_eq_Ioi_self_iff {f : ι → α} {a : α} :
    ⋃ i, Ioc a (f i) = Ioi a ↔ ∀ x, a < x → ∃ i, x ≤ f i := by
  simp [← Ioi_inter_Iic, ← inter_iUnion, subset_def]

@[to_dual (attr := simp)]
/-
**Set.iUnion_Icc_eq_Ici_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_Icc_eq_Ici_self_iff {f : ι -> α} {a : α} : ⋃ i, Icc a (f i) = Ici a
 ↔ forall x >= a, exists i, x <= f i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem iUnion_Icc_eq_Ici_self_iff {f : ι → α} {a : α} :
    ⋃ i, Icc a (f i) = Ici a ↔ ∀ x ≥ a, ∃ i, x ≤ f i := by
  simp [← Ici_inter_Iic, ← inter_iUnion, subset_def]

@[simp]
/-
**Set.biUnion_Ico_eq_Iio_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：biUnion_Ico_eq_Iio_self_iff {p : ι -> Prop} {f : forall i, p i -> α} {a : 
α} : ⋃ (i) (hi : p i), Ico (f i hi) a = Iio a ↔ forall x < a, exists i hi, f i h
i <= x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem biUnion_Ico_eq_Iio_self_iff {p : ι → Prop} {f : ∀ i, p i → α} {a : α} :
    ⋃ (i) (hi : p i), Ico (f i hi) a = Iio a ↔ ∀ x < a, ∃ i hi, f i hi ≤ x := by
  simp [← Ici_inter_Iio, ← iUnion_inter, subset_def]

@[simp]
/-
**Set.biUnion_Ioc_eq_Ioi_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：biUnion_Ioc_eq_Ioi_self_iff {p : ι -> Prop} {f : forall i, p i -> α} {a : 
α} : ⋃ (i) (hi : p i), Ioc a (f i hi) = Ioi a ↔ forall x, a < x -> exists i hi, 
x <= f i hi
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem biUnion_Ioc_eq_Ioi_self_iff {p : ι → Prop} {f : ∀ i, p i → α} {a : α} :
    ⋃ (i) (hi : p i), Ioc a (f i hi) = Ioi a ↔ ∀ x, a < x → ∃ i hi, x ≤ f i hi := by
  simp [← Ioi_inter_Iic, ← inter_iUnion, subset_def]

end LinearOrder

end Set

section UnionIxx

variable [LinearOrder α] {s : Set α} {a : α} {f : ι → α}

/-
**IsGLB.biUnion_Ioi_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsGLB.biUnion_Ioi_eq (h : IsGLB s a) : ⋃ x in s, Ioi x = Ioi a
参数：h : IsGLB s a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Set.iUnion₂_subset`：iUnion₂_subset {s : forall i, κ i -> Set α} {t : Set
 α} (h : forall i j, s i j subseteq t) : ⋃ (i) (j), s i j subseteq t
· 使用定理 `Set.Ioi_subset_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b ≤ 
a → Set.Ioi a ⊆ Set.Ioi b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `IsGLB.exists_between`：IsGLB.exists_between (h : IsGLB s a) (hb : a < b) 
: exists c in s, a <= c ∧ c < b
· 使用定理 `Set.mem_biUnion`：mem_biUnion {s : Set α} {t : α -> Set β} {x : α} {y : β
} (xs : x in s) (ytx : y in t x) : y in ⋃ x in s, t x
-/
theorem IsGLB.biUnion_Ioi_eq (h : IsGLB s a) : ⋃ x ∈ s, Ioi x = Ioi a := by
  refine (iUnion₂_subset fun x hx => ?_).antisymm fun x hx => ?_
  · exact Ioi_subset_Ioi (h.1 hx)
  · rcases h.exists_between hx with ⟨y, hys, _, hyx⟩
    exact mem_biUnion hys hyx
/-
**IsGLB.iUnion_Ioi_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsGLB.iUnion_Ioi_eq (h : IsGLB (range f) a) : ⋃ x, Ioi (f x) = Ioi a
参数：h : IsGLB (range f) a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.biUnion_range`：biUnion_range {f : ι -> α} {g : α -> Set β} : ⋃ x in 
range f, g x = ⋃ y, g (f y)
· 使用定理 `IsGLB.biUnion_Ioi_eq`：IsGLB.biUnion_Ioi_eq (h : IsGLB s a) : ⋃ x in s, I
oi x = Ioi a
-/
theorem IsGLB.iUnion_Ioi_eq (h : IsGLB (range f) a) : ⋃ x, Ioi (f x) = Ioi a :=
  biUnion_range.symm.trans h.biUnion_Ioi_eq
/-
**IsLUB.biUnion_Iio_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLUB.biUnion_Iio_eq (h : IsLUB s a) : ⋃ x in s, Iio x = Iio a
参数：h : IsLUB s a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGLB.biUnion_Ioi_eq`：IsGLB.biUnion_Ioi_eq (h : IsGLB s a) : ⋃ x in s, I
oi x = Ioi a
· 使用定理 `IsLUB.dual`：IsLUB.dual (h : IsLUB s a) : IsGLB (ofDual ⁻¹' s) (toDual a)
-/
theorem IsLUB.biUnion_Iio_eq (h : IsLUB s a) : ⋃ x ∈ s, Iio x = Iio a :=
  h.dual.biUnion_Ioi_eq
/-
**IsLUB.iUnion_Iio_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLUB.iUnion_Iio_eq (h : IsLUB (range f) a) : ⋃ x, Iio (f x) = Iio a
参数：h : IsLUB (range f) a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGLB.iUnion_Ioi_eq`：IsGLB.iUnion_Ioi_eq (h : IsGLB (range f) a) : ⋃ x, 
Ioi (f x) = Ioi a
· 使用定理 `IsLUB.dual`：IsLUB.dual (h : IsLUB s a) : IsGLB (ofDual ⁻¹' s) (toDual a)
-/
theorem IsLUB.iUnion_Iio_eq (h : IsLUB (range f) a) : ⋃ x, Iio (f x) = Iio a :=
  h.dual.iUnion_Ioi_eq
/-
**iUnion_Ioi_eq_Ioi_iInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iUnion_Ioi_eq_Ioi_iInf {R : Type*} [CompleteLinearOrder R] {f : ι -> R} : 
⋃ i : ι, Ioi (f i) = Ioi (⨅ i, f i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGLB.iUnion_Ioi_eq`：IsGLB.iUnion_Ioi_eq (h : IsGLB (range f) a) : ⋃ x, 
Ioi (f x) = Ioi a
· 使用定理 `isGLB_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {
f : ι → α}, IsGLB (Set.range f) (⨅ j, f j)
-/
theorem iUnion_Ioi_eq_Ioi_iInf {R : Type*} [CompleteLinearOrder R] {f : ι → R} :
    ⋃ i : ι, Ioi (f i) = Ioi (⨅ i, f i) :=
  isGLB_iInf.iUnion_Ioi_eq
/-
**iUnion_Iio_eq_Iio_iSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iUnion_Iio_eq_Iio_iSup {R : Type*} [CompleteLinearOrder R] {f : ι -> R} : 
⋃ i : ι, Iio (f i) = Iio (⨆ i, f i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLUB.iUnion_Iio_eq`：IsLUB.iUnion_Iio_eq (h : IsLUB (range f) a) : ⋃ x, 
Iio (f x) = Iio a
· 使用定理 `isLUB_iSup`：isLUB_iSup : IsLUB (range f) (⨆ j, f j)
-/
theorem iUnion_Iio_eq_Iio_iSup {R : Type*} [CompleteLinearOrder R] {f : ι → R} :
    ⋃ i : ι, Iio (f i) = Iio (⨆ i, f i) :=
  isLUB_iSup.iUnion_Iio_eq
/-
**IsGLB.biUnion_Ici_eq_Ioi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsGLB.biUnion_Ici_eq_Ioi (a_glb : IsGLB s a) (a_notMem : a ∉ s) : ⋃ x in s
, Ici x = Ioi a
参数：a_glb : IsGLB s a；a_notMem : a ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Set.iUnion₂_subset`：iUnion₂_subset {s : forall i, κ i -> Set α} {t : Set
 α} (h : forall i j, s i j subseteq t) : ⋃ (i) (j), s i j subseteq t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Ici_subset_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.
Ici a ⊆ Set.Ioi b ↔ b < a
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `IsGLB.exists_between`：IsGLB.exists_between (h : IsGLB s a) (hb : a < b) 
: exists c in s, a <= c ∧ c < b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_iUnion₂`：mem_iUnion₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋃ (i) (j), s i j) ↔ exists i j, x in s i j
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem IsGLB.biUnion_Ici_eq_Ioi (a_glb : IsGLB s a) (a_notMem : a ∉ s) :
    ⋃ x ∈ s, Ici x = Ioi a := by
  refine (iUnion₂_subset fun x hx => ?_).antisymm fun x hx => ?_
  · exact Ici_subset_Ioi.mpr (lt_of_le_of_ne (a_glb.1 hx) fun h => (h ▸ a_notMem) hx)
  · rcases a_glb.exists_between hx with ⟨y, hys, _, hyx⟩
    rw [mem_iUnion₂]
    exact ⟨y, hys, hyx.le⟩
/-
**IsGLB.biUnion_Ici_eq_Ici** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsGLB.biUnion_Ici_eq_Ici (a_glb : IsGLB s a) (a_mem : a in s) : ⋃ x in s, 
Ici x = Ici a
参数：a_glb : IsGLB s a；a_mem : a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Set.iUnion₂_subset`：iUnion₂_subset {s : forall i, κ i -> Set α} {t : Set
 α} (h : forall i j, s i j subseteq t) : ⋃ (i) (j), s i j subseteq t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Ici_subset_Ici`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.
Ici a ⊆ Set.Ici b ↔ b ≤ a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_lowerBounds`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α} {a : α
}, a ∈ lowerBounds s ↔ ∀ x ∈ s, a ≤ x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.mem_iUnion₂`：mem_iUnion₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋃ (i) (j), s i j) ↔ exists i j, x in s i j
-/
theorem IsGLB.biUnion_Ici_eq_Ici (a_glb : IsGLB s a) (a_mem : a ∈ s) :
    ⋃ x ∈ s, Ici x = Ici a := by
  refine (iUnion₂_subset fun x hx => ?_).antisymm fun x hx => ?_
  · exact Ici_subset_Ici.mpr (mem_lowerBounds.mp a_glb.1 x hx)
  · exact mem_iUnion₂.mpr ⟨a, a_mem, hx⟩
/-
**IsLUB.biUnion_Iic_eq_Iio** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLUB.biUnion_Iic_eq_Iio (a_lub : IsLUB s a) (a_notMem : a ∉ s) : ⋃ x in s
, Iic x = Iio a
参数：a_lub : IsLUB s a；a_notMem : a ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGLB.biUnion_Ici_eq_Ioi`：IsGLB.biUnion_Ici_eq_Ioi (a_glb : IsGLB s a) (
a_notMem : a ∉ s) : ⋃ x in s, Ici x = Ioi a
· 使用定理 `IsLUB.dual`：IsLUB.dual (h : IsLUB s a) : IsGLB (ofDual ⁻¹' s) (toDual a)
-/
theorem IsLUB.biUnion_Iic_eq_Iio (a_lub : IsLUB s a) (a_notMem : a ∉ s) :
    ⋃ x ∈ s, Iic x = Iio a :=
  a_lub.dual.biUnion_Ici_eq_Ioi a_notMem
/-
**IsLUB.biUnion_Iic_eq_Iic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLUB.biUnion_Iic_eq_Iic (a_lub : IsLUB s a) (a_mem : a in s) : ⋃ x in s, 
Iic x = Iic a
参数：a_lub : IsLUB s a；a_mem : a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGLB.biUnion_Ici_eq_Ici`：IsGLB.biUnion_Ici_eq_Ici (a_glb : IsGLB s a) (
a_mem : a in s) : ⋃ x in s, Ici x = Ici a
· 使用定理 `IsLUB.dual`：IsLUB.dual (h : IsLUB s a) : IsGLB (ofDual ⁻¹' s) (toDual a)
-/
theorem IsLUB.biUnion_Iic_eq_Iic (a_lub : IsLUB s a) (a_mem : a ∈ s) : ⋃ x ∈ s, Iic x = Iic a :=
  a_lub.dual.biUnion_Ici_eq_Ici a_mem
/-
**iUnion_Ici_eq_Ioi_iInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iUnion_Ici_eq_Ioi_iInf {R : Type*} [CompleteLinearOrder R] {f : ι -> R} (n
o_least_elem : ⨅ i, f i ∉ range f) : ⋃ i : ι, Ici (f i) = Ioi (⨅ i, f i)
参数：no_least_elem : ⨅ i, f i ∉ range f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsGLB.biUnion_Ici_eq_Ioi`：IsGLB.biUnion_Ici_eq_Ioi (a_glb : IsGLB s a) (
a_notMem : a ∉ s) : ⋃ x in s, Ici x = Ioi a
· 使用定理 `isGLB_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {
f : ι → α}, IsGLB (Set.range f) (⨅ j, f j)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_exists`：iUnion_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋃ x, f x = ⋃ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Set.iUnion_iUnion_eq'`：iUnion_iUnion_eq' {f : ι -> α} {g : α -> Set β} :
 ⋃ (x) (y) (_ : f y = x), g x = ⋃ y, g (f y)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iUnion_Ici_eq_Ioi_iInf {R : Type*} [CompleteLinearOrder R] {f : ι → R}
    (no_least_elem : ⨅ i, f i ∉ range f) : ⋃ i : ι, Ici (f i) = Ioi (⨅ i, f i) := by
  simp only [← IsGLB.biUnion_Ici_eq_Ioi (@isGLB_iInf _ _ _ f) no_least_elem, mem_range,
    iUnion_exists, iUnion_iUnion_eq']
/-
**iUnion_Iic_eq_Iio_iSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iUnion_Iic_eq_Iio_iSup {R : Type*} [CompleteLinearOrder R] {f : ι -> R} (n
o_greatest_elem : (⨆ i, f i) ∉ range f) : ⋃ i : ι, Iic (f i) = Iio (⨆ i, f i)
参数：no_greatest_elem : (⨆ i, f i) ∉ range f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iUnion_Ici_eq_Ioi_iInf`：iUnion_Ici_eq_Ioi_iInf {R : Type*} [CompleteLine
arOrder R] {f : ι -> R} (no_least_elem : ⨅ i, f i ∉ range f) : ⋃ i : ι, Ici (f i
) = Ioi (⨅ i…
-/
theorem iUnion_Iic_eq_Iio_iSup {R : Type*} [CompleteLinearOrder R] {f : ι → R}
    (no_greatest_elem : (⨆ i, f i) ∉ range f) : ⋃ i : ι, Iic (f i) = Iio (⨆ i, f i) :=
  @iUnion_Ici_eq_Ioi_iInf ι (OrderDual R) _ f no_greatest_elem
/-
**iUnion_Ici_eq_Ici_iInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iUnion_Ici_eq_Ici_iInf {R : Type*} [CompleteLinearOrder R] {f : ι -> R} (h
as_least_elem : (⨅ i, f i) in range f) : ⋃ i : ι, Ici (f i) = Ici (⨅ i, f i)
参数：has_least_elem : (⨅ i, f i) in range f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsGLB.biUnion_Ici_eq_Ici`：IsGLB.biUnion_Ici_eq_Ici (a_glb : IsGLB s a) (
a_mem : a in s) : ⋃ x in s, Ici x = Ici a
· 使用定理 `isGLB_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {
f : ι → α}, IsGLB (Set.range f) (⨅ j, f j)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_exists`：iUnion_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋃ x, f x = ⋃ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Set.iUnion_iUnion_eq'`：iUnion_iUnion_eq' {f : ι -> α} {g : α -> Set β} :
 ⋃ (x) (y) (_ : f y = x), g x = ⋃ y, g (f y)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iUnion_Ici_eq_Ici_iInf {R : Type*} [CompleteLinearOrder R] {f : ι → R}
    (has_least_elem : (⨅ i, f i) ∈ range f) : ⋃ i : ι, Ici (f i) = Ici (⨅ i, f i) := by
  simp only [← IsGLB.biUnion_Ici_eq_Ici (@isGLB_iInf _ _ _ f) has_least_elem, mem_range,
    iUnion_exists, iUnion_iUnion_eq']
/-
**iUnion_Iic_eq_Iic_iSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iUnion_Iic_eq_Iic_iSup {R : Type*} [CompleteLinearOrder R] {f : ι -> R} (h
as_greatest_elem : (⨆ i, f i) in range f) : ⋃ i : ι, Iic (f i) = Iic (⨆ i, f i)
参数：has_greatest_elem : (⨆ i, f i) in range f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iUnion_Ici_eq_Ici_iInf`：iUnion_Ici_eq_Ici_iInf {R : Type*} [CompleteLine
arOrder R] {f : ι -> R} (has_least_elem : (⨅ i, f i) in range f) : ⋃ i : ι, Ici 
(f i) = Ici …
-/
theorem iUnion_Iic_eq_Iic_iSup {R : Type*} [CompleteLinearOrder R] {f : ι → R}
    (has_greatest_elem : (⨆ i, f i) ∈ range f) : ⋃ i : ι, Iic (f i) = Iic (⨆ i, f i) :=
  @iUnion_Ici_eq_Ici_iInf ι (OrderDual R) _ f has_greatest_elem
/-
**iUnion_Iio_eq_univ_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iUnion_Iio_eq_univ_iff : ⋃ i, Iio (f i) = univ ↔ (¬ BddAbove (range f))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem iUnion_Iio_eq_univ_iff : ⋃ i, Iio (f i) = univ ↔ (¬ BddAbove (range f)) := by
  simp [not_bddAbove_iff, Set.eq_univ_iff_forall]
/-
**iUnion_Iic_of_not_bddAbove_range** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iUnion_Iic_of_not_bddAbove_range (hf : ¬ BddAbove (range f)) : ⋃ i, Iic (f
 i) = univ
参数：hf : ¬ BddAbove (range f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_univ_of_subset`：eq_univ_of_subset {s t : Set α} (h : s subseteq t
) (hs : s = univ) : t = univ
· 使用定理 `Set.iUnion_mono''`：iUnion_mono'' {s t : ι -> Set α} (h : forall i, s i s
ubseteq t i) : iUnion s subseteq iUnion t
· 使用定理 `Set.Iio_subset_Iic_self`：Iio_subset_Iic_self : Iio a subseteq Iic a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `iUnion_Iio_eq_univ_iff`：iUnion_Iio_eq_univ_iff : ⋃ i, Iio (f i) = univ ↔
 (¬ BddAbove (range f))
-/
theorem iUnion_Iic_of_not_bddAbove_range (hf : ¬ BddAbove (range f)) : ⋃ i, Iic (f i) = univ := by
  refine Set.eq_univ_of_subset ?_ (iUnion_Iio_eq_univ_iff.mpr hf)
  gcongr
  exact Iio_subset_Iic_self
/-
**iInter_Iic_eq_empty_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iInter_Iic_eq_empty_iff : ⋂ i, Iic (f i) = ∅ ↔ ¬ BddBelow (range f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem iInter_Iic_eq_empty_iff : ⋂ i, Iic (f i) = ∅ ↔ ¬ BddBelow (range f) := by
  simp [not_bddBelow_iff, Set.eq_empty_iff_forall_notMem]
/-
**iInter_Iio_of_not_bddBelow_range** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iInter_Iio_of_not_bddBelow_range (hf : ¬ BddBelow (range f)) : ⋂ i, Iio (f
 i) = ∅
参数：hf : ¬ BddBelow (range f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_of_subset_empty`：eq_empty_of_subset_empty {s : Set α} : s s
ubseteq ∅ -> s = ∅
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `iInter_Iic_eq_empty_iff`：iInter_Iic_eq_empty_iff : ⋂ i, Iic (f i) = ∅ ↔ 
¬ BddBelow (range f)
· 使用定理 `Set.iInter_mono''`：iInter_mono'' {s t : ι -> Set α} (h : forall i, s i s
ubseteq t i) : iInter s subseteq iInter t
· 使用定理 `Set.Iio_subset_Iic_self`：Iio_subset_Iic_self : Iio a subseteq Iic a
-/
theorem iInter_Iio_of_not_bddBelow_range (hf : ¬ BddBelow (range f)) : ⋂ i, Iio (f i) = ∅ := by
  refine eq_empty_of_subset_empty ?_
  rw [← iInter_Iic_eq_empty_iff.mpr hf]
  gcongr
  exact Iio_subset_Iic_self

end UnionIxx

