/-
Copyright (c) 2020 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton
-/
module

public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.Interval.Set.Basic

/-!
# Infinitude of intervals

Bounded intervals in dense orders are infinite, as are unbounded intervals
in orders that are unbounded on the appropriate side. We also prove that an unbounded
preorder is an infinite type.
-/

public section


variable {α : Type*} [Preorder α]

/-- A nonempty preorder with no maximal element is infinite. -/
/-
**NoMaxOrder.infinite** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：NoMaxOrder.infinite [Nonempty α] [NoMaxOrder α] : Infinite α
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.exists_strictMono`：exists_strictMono [Nonempty α] [NoMaxOrder α] : e
xists f : Nat -> α, StrictMono f
· 使用定理 `Infinite.of_injective`：of_injective {α β} [Infinite β] (f : β -> α) (hf 
: Injective f) : Infinite α
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f

--- 原说明 ---
A nonempty preorder with no maximal element is infinite.
-/
instance NoMaxOrder.infinite [Nonempty α] [NoMaxOrder α] : Infinite α :=
  let ⟨f, hf⟩ := Nat.exists_strictMono α
  Infinite.of_injective f hf.injective

/-- A nonempty preorder with no minimal element is infinite. -/
/-
**NoMinOrder.infinite** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：NoMinOrder.infinite [Nonempty α] [NoMinOrder α] : Infinite α
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderDual.instNonempty`：∀ (α : Type u_2) [h : Nonempty α], Nonempty αᵒᵈ
· 使用定理 `OrderDual.noMaxOrder`：∀ {α : Type u_1} [inst : LT α] [NoMinOrder α], NoM
axOrder αᵒᵈ

--- 原说明 ---
A nonempty preorder with no minimal element is infinite.
-/
instance NoMinOrder.infinite [Nonempty α] [NoMinOrder α] : Infinite α :=
  @NoMaxOrder.infinite αᵒᵈ _ _ _

namespace Set

section DenselyOrdered

variable [DenselyOrdered α] {a b : α} (h : a < b)
include h

/-
**Set.Ioo.infinite** 是 Mathlib 中的一个定理，位于命名空间 `Set.Ioo`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [DenselyOrdered α] {a b : α}, a < b →
 Infinite ↑(Set.Ioo a b)
参数：Set.Ioo a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.nonempty_Ioo_subtype`：nonempty_Ioo_subtype [DenselyOrdered α] (h : a
 < b) : Nonempty (Ioo a b)
· 使用定理 `Set.instNoMaxOrderElemIoo`：∀ (α : Type u_1) [inst : Preorder α] [Densely
Ordered α] {x y : α}, NoMaxOrder ↑(Set.Ioo y x)
-/
theorem Ioo.infinite : Infinite (Ioo a b) :=
  @NoMaxOrder.infinite _ _ (nonempty_Ioo_subtype h) _
/-
**Set.Ioo_infinite** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioo_infinite : (Ioo a b).Infinite
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.infinite_coe_iff`：infinite_coe_iff {s : Set α} : Infinite s ↔ s.Infi
nite
· 使用定理 `Set.Ioo.infinite`：∀ {α : Type u_1} [inst : Preorder α] [DenselyOrdered α
] {a b : α}, a < b → Infinite ↑(Set.Ioo a b)
-/
theorem Ioo_infinite : (Ioo a b).Infinite :=
  infinite_coe_iff.1 <| Ioo.infinite h
/-
**Set.Ico_infinite** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ico_infinite : (Ico a b).Infinite
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Infinite.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Infinite → t.
Infinite
· 使用定理 `Set.Ioo_subset_Ico_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo a b ⊆ Set.Ico a b
· 使用定理 `Set.Ioo_infinite`：Ioo_infinite : (Ioo a b).Infinite
-/
theorem Ico_infinite : (Ico a b).Infinite :=
  (Ioo_infinite h).mono Ioo_subset_Ico_self
/-
**Set.Ico.infinite** 是 Mathlib 中的一个定理，位于命名空间 `Set.Ico`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [DenselyOrdered α] {a b : α}, a < b →
 Infinite ↑(Set.Ico a b)
参数：Set.Ico a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.infinite_coe_iff`：infinite_coe_iff {s : Set α} : Infinite s ↔ s.Infi
nite
· 使用定理 `Set.Ico_infinite`：Ico_infinite : (Ico a b).Infinite
-/
theorem Ico.infinite : Infinite (Ico a b) :=
  infinite_coe_iff.2 <| Ico_infinite h
/-
**Set.Ioc_infinite** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioc_infinite : (Ioc a b).Infinite
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Infinite.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Infinite → t.
Infinite
· 使用定理 `Set.Ioo_subset_Ioc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo b a ⊆ Set.Ioc b a
· 使用定理 `Set.Ioo_infinite`：Ioo_infinite : (Ioo a b).Infinite
-/
theorem Ioc_infinite : (Ioc a b).Infinite :=
  (Ioo_infinite h).mono Ioo_subset_Ioc_self
/-
**Set.Ioc.infinite** 是 Mathlib 中的一个定理，位于命名空间 `Set.Ioc`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [DenselyOrdered α] {a b : α}, a < b →
 Infinite ↑(Set.Ioc a b)
参数：Set.Ioc a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.infinite_coe_iff`：infinite_coe_iff {s : Set α} : Infinite s ↔ s.Infi
nite
· 使用定理 `Set.Ioc_infinite`：Ioc_infinite : (Ioc a b).Infinite
-/
theorem Ioc.infinite : Infinite (Ioc a b) :=
  infinite_coe_iff.2 <| Ioc_infinite h
/-
**Set.Icc_infinite** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Icc_infinite : (Icc a b).Infinite
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Infinite.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Infinite → t.
Infinite
· 使用定理 `Set.Ioo_subset_Icc_self`：Ioo_subset_Icc_self : Ioo a b subseteq Icc a b
· 使用定理 `Set.Ioo_infinite`：Ioo_infinite : (Ioo a b).Infinite
-/
theorem Icc_infinite : (Icc a b).Infinite :=
  (Ioo_infinite h).mono Ioo_subset_Icc_self
/-
**Set.Icc.infinite** 是 Mathlib 中的一个定理，位于命名空间 `Set.Icc`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [DenselyOrdered α] {a b : α}, a < b →
 Infinite ↑(Set.Icc a b)
参数：Set.Icc a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.infinite_coe_iff`：infinite_coe_iff {s : Set α} : Infinite s ↔ s.Infi
nite
· 使用定理 `Set.Icc_infinite`：Icc_infinite : (Icc a b).Infinite
-/
theorem Icc.infinite : Infinite (Icc a b) :=
  infinite_coe_iff.2 <| Icc_infinite h

end DenselyOrdered

/-
**Set.** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NoMinOrder α] {a : α} : Infinite (Iio a) :=
  NoMinOrder.infinite
/-
**Set.Iio_infinite** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iio_infinite [NoMinOrder α] (a : α) : (Iio a).Infinite
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.infinite_coe_iff`：infinite_coe_iff {s : Set α} : Infinite s ↔ s.Infi
nite
· 使用定理 `Set.instInfiniteElemIioOfNoMinOrder`：∀ {α : Type u_1} [inst : Preorder α
] [NoMinOrder α] {a : α}, Infinite ↑(Set.Iio a)
-/
theorem Iio_infinite [NoMinOrder α] (a : α) : (Iio a).Infinite :=
  infinite_coe_iff.1 inferInstance
/-
**Set.** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NoMinOrder α] {a : α} : Infinite (Iic a) :=
  NoMinOrder.infinite
/-
**Set.Iic_infinite** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iic_infinite [NoMinOrder α] (a : α) : (Iic a).Infinite
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.infinite_coe_iff`：infinite_coe_iff {s : Set α} : Infinite s ↔ s.Infi
nite
· 使用定理 `Set.instInfiniteElemIicOfNoMinOrder`：∀ {α : Type u_1} [inst : Preorder α
] [NoMinOrder α] {a : α}, Infinite ↑(Set.Iic a)
-/
theorem Iic_infinite [NoMinOrder α] (a : α) : (Iic a).Infinite :=
  infinite_coe_iff.1 inferInstance
/-
**Set.** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NoMaxOrder α] {a : α} : Infinite (Ioi a) :=
  NoMaxOrder.infinite
/-
**Set.Ioi_infinite** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioi_infinite [NoMaxOrder α] (a : α) : (Ioi a).Infinite
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.infinite_coe_iff`：infinite_coe_iff {s : Set α} : Infinite s ↔ s.Infi
nite
· 使用定理 `Set.instInfiniteElemIoiOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α
] [NoMaxOrder α] {a : α}, Infinite ↑(Set.Ioi a)
-/
theorem Ioi_infinite [NoMaxOrder α] (a : α) : (Ioi a).Infinite :=
  infinite_coe_iff.1 inferInstance
/-
**Set.** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NoMaxOrder α] {a : α} : Infinite (Ici a) :=
  NoMaxOrder.infinite
/-
**Set.Ici_infinite** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ici_infinite [NoMaxOrder α] (a : α) : (Ici a).Infinite
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.infinite_coe_iff`：infinite_coe_iff {s : Set α} : Infinite s ↔ s.Infi
nite
· 使用定理 `Set.instInfiniteElemIciOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α
] [NoMaxOrder α] {a : α}, Infinite ↑(Set.Ici a)
-/
theorem Ici_infinite [NoMaxOrder α] (a : α) : (Ici a).Infinite :=
  infinite_coe_iff.1 inferInstance

end Set

