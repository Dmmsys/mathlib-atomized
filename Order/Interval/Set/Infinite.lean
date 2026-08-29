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

/--
Instance `NoMaxOrder.infinite` / 实例 `NoMaxOrder.infinite`

English:
instance NoMaxOrder.infinite
  signature: [Nonempty α] [NoMaxOrder α]
  body: let ⟨f, hf⟩ := Nat.exists_strictMono α
  Infinite.of_injective f hf.injective

中文:
实例 NoMaxOrder.infinite
  签名: [Nonempty α] [NoMaxOrder α]
  定义体: let ⟨f, hf⟩ := Nat.exists_strictMono α
  Infinite.of_injective f hf.injective

Depends on / 依赖: Infinite, Infinite.of_injective, Nat.exists_strictMono, exists_strictMono, hf.injective, injective, of_injective
-/
instance NoMaxOrder.infinite [Nonempty α] [NoMaxOrder α] : Infinite α :=
  let ⟨f, hf⟩ := Nat.exists_strictMono α
  Infinite.of_injective f hf.injective

/--
Instance `NoMinOrder.infinite` / 实例 `NoMinOrder.infinite`

English:
instance NoMinOrder.infinite
  signature: [Nonempty α] [NoMinOrder α]
  body: @NoMaxOrder.infinite αᵒᵈ _ _ _

中文:
实例 NoMinOrder.infinite
  签名: [Nonempty α] [NoMinOrder α]
  定义体: @NoMaxOrder.infinite αᵒᵈ _ _ _

Depends on / 依赖: NoMaxOrder, NoMaxOrder.infinite, infinite
-/
instance NoMinOrder.infinite [Nonempty α] [NoMinOrder α] : Infinite α :=
  @NoMaxOrder.infinite αᵒᵈ _ _ _

namespace Set

section DenselyOrdered

variable [DenselyOrdered α] {a b : α} (h : a < b)
include h

/--
theorem `Ioo.infinite` / 定理 `Ioo.infinite`

English:
theorem Ioo.infinite
  statement: Infinite (Ioo a b)
  proof: @NoMaxOrder.infinite _ _ (nonempty_Ioo_subtype h) _

中文:
定理 Ioo.infinite
  结论: Infinite (Ioo a b)
  证明: @NoMaxOrder.infinite _ _ (nonempty_Ioo_subtype h) _

Depends on / 依赖: NoMaxOrder, NoMaxOrder.infinite, infinite, nonempty_Ioo_subtype
-/
theorem Ioo.infinite : Infinite (Ioo a b) :=
  @NoMaxOrder.infinite _ _ (nonempty_Ioo_subtype h) _

/--
theorem `Ioo_infinite` / 定理 `Ioo_infinite`

English:
theorem Ioo_infinite
  statement: (Ioo a b).Infinite
  proof: infinite_coe_iff.1 Ioo.infinite h

中文:
定理 Ioo_infinite
  结论: (Ioo a b).Infinite
  证明: infinite_coe_iff.1 Ioo.infinite h

Depends on / 依赖: Ioo.infinite, infinite, infinite_coe_iff
-/
theorem Ioo_infinite : (Ioo a b).Infinite :=
infinite_coe_iff.1 Ioo.infinite h

/--
theorem `Ico_infinite` / 定理 `Ico_infinite`

English:
theorem Ico_infinite
  statement: (Ico a b).Infinite
  proof: (Ioo_infinite h).mono Ioo_subset_Ico_self

中文:
定理 Ico_infinite
  结论: (Ico a b).Infinite
  证明: (Ioo_infinite h).mono Ioo_subset_Ico_self

Depends on / 依赖: Ioo_infinite, Ioo_subset_Ico_self
-/
theorem Ico_infinite : (Ico a b).Infinite :=
  (Ioo_infinite h).mono Ioo_subset_Ico_self

/--
theorem `Ico.infinite` / 定理 `Ico.infinite`

English:
theorem Ico.infinite
  statement: Infinite (Ico a b)
  proof: infinite_coe_iff.2 Ico_infinite h

中文:
定理 Ico.infinite
  结论: Infinite (Ico a b)
  证明: infinite_coe_iff.2 Ico_infinite h

Depends on / 依赖: Ico_infinite, infinite_coe_iff
-/
theorem Ico.infinite : Infinite (Ico a b) :=
infinite_coe_iff.2 Ico_infinite h

/--
theorem `Ioc_infinite` / 定理 `Ioc_infinite`

English:
theorem Ioc_infinite
  statement: (Ioc a b).Infinite
  proof: (Ioo_infinite h).mono Ioo_subset_Ioc_self

中文:
定理 Ioc_infinite
  结论: (Ioc a b).Infinite
  证明: (Ioo_infinite h).mono Ioo_subset_Ioc_self

Depends on / 依赖: Ioo_infinite, Ioo_subset_Ioc_self
-/
theorem Ioc_infinite : (Ioc a b).Infinite :=
  (Ioo_infinite h).mono Ioo_subset_Ioc_self

/--
theorem `Ioc.infinite` / 定理 `Ioc.infinite`

English:
theorem Ioc.infinite
  statement: Infinite (Ioc a b)
  proof: infinite_coe_iff.2 Ioc_infinite h

中文:
定理 Ioc.infinite
  结论: Infinite (Ioc a b)
  证明: infinite_coe_iff.2 Ioc_infinite h

Depends on / 依赖: Ioc_infinite, infinite_coe_iff
-/
theorem Ioc.infinite : Infinite (Ioc a b) :=
infinite_coe_iff.2 Ioc_infinite h

/--
theorem `Icc_infinite` / 定理 `Icc_infinite`

English:
theorem Icc_infinite
  statement: (Icc a b).Infinite
  proof: (Ioo_infinite h).mono Ioo_subset_Icc_self

中文:
定理 Icc_infinite
  结论: (Icc a b).Infinite
  证明: (Ioo_infinite h).mono Ioo_subset_Icc_self

Depends on / 依赖: Ioo_infinite, Ioo_subset_Icc_self
-/
theorem Icc_infinite : (Icc a b).Infinite :=
  (Ioo_infinite h).mono Ioo_subset_Icc_self

/--
theorem `Icc.infinite` / 定理 `Icc.infinite`

English:
theorem Icc.infinite
  statement: Infinite (Icc a b)
  proof: infinite_coe_iff.2 Icc_infinite h

中文:
定理 Icc.infinite
  结论: Infinite (Icc a b)
  证明: infinite_coe_iff.2 Icc_infinite h

Depends on / 依赖: Icc_infinite, infinite_coe_iff
-/
theorem Icc.infinite : Infinite (Icc a b) :=
infinite_coe_iff.2 Icc_infinite h

end DenselyOrdered

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NoMinOrder
  signature: α] {a
  body: NoMinOrder.infinite

中文:
实例 [NoMinOrder
  签名: α] {a
  定义体: NoMinOrder.infinite

Depends on / 依赖: NoMinOrder, NoMinOrder.infinite, infinite
-/
instance [NoMinOrder α] {a : α} : Infinite (Iio a) :=
  NoMinOrder.infinite

/--
theorem `Iio_infinite` / 定理 `Iio_infinite`

English:
theorem Iio_infinite
  given: [NoMinOrder α] (a : α)
  statement: (Iio a).Infinite
  proof: infinite_coe_iff.1 inferInstance

中文:
定理 Iio_infinite
  条件: [NoMinOrder α] (a : α)
  结论: (Iio a).Infinite
  证明: infinite_coe_iff.1 inferInstance

Depends on / 依赖: infinite_coe_iff
-/
theorem Iio_infinite [NoMinOrder α] (a : α) : (Iio a).Infinite :=
  infinite_coe_iff.1 inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NoMinOrder
  signature: α] {a
  body: NoMinOrder.infinite

中文:
实例 [NoMinOrder
  签名: α] {a
  定义体: NoMinOrder.infinite

Depends on / 依赖: NoMinOrder, NoMinOrder.infinite, infinite
-/
instance [NoMinOrder α] {a : α} : Infinite (Iic a) :=
  NoMinOrder.infinite

/--
theorem `Iic_infinite` / 定理 `Iic_infinite`

English:
theorem Iic_infinite
  given: [NoMinOrder α] (a : α)
  statement: (Iic a).Infinite
  proof: infinite_coe_iff.1 inferInstance

中文:
定理 Iic_infinite
  条件: [NoMinOrder α] (a : α)
  结论: (Iic a).Infinite
  证明: infinite_coe_iff.1 inferInstance

Depends on / 依赖: infinite_coe_iff
-/
theorem Iic_infinite [NoMinOrder α] (a : α) : (Iic a).Infinite :=
  infinite_coe_iff.1 inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NoMaxOrder
  signature: α] {a
  body: NoMaxOrder.infinite

中文:
实例 [NoMaxOrder
  签名: α] {a
  定义体: NoMaxOrder.infinite

Depends on / 依赖: NoMaxOrder, NoMaxOrder.infinite, infinite
-/
instance [NoMaxOrder α] {a : α} : Infinite (Ioi a) :=
  NoMaxOrder.infinite

/--
theorem `Ioi_infinite` / 定理 `Ioi_infinite`

English:
theorem Ioi_infinite
  given: [NoMaxOrder α] (a : α)
  statement: (Ioi a).Infinite
  proof: infinite_coe_iff.1 inferInstance

中文:
定理 Ioi_infinite
  条件: [NoMaxOrder α] (a : α)
  结论: (Ioi a).Infinite
  证明: infinite_coe_iff.1 inferInstance

Depends on / 依赖: infinite_coe_iff
-/
theorem Ioi_infinite [NoMaxOrder α] (a : α) : (Ioi a).Infinite :=
  infinite_coe_iff.1 inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NoMaxOrder
  signature: α] {a
  body: NoMaxOrder.infinite

中文:
实例 [NoMaxOrder
  签名: α] {a
  定义体: NoMaxOrder.infinite

Depends on / 依赖: NoMaxOrder, NoMaxOrder.infinite, infinite
-/
instance [NoMaxOrder α] {a : α} : Infinite (Ici a) :=
  NoMaxOrder.infinite

/--
theorem `Ici_infinite` / 定理 `Ici_infinite`

English:
theorem Ici_infinite
  given: [NoMaxOrder α] (a : α)
  statement: (Ici a).Infinite
  proof: infinite_coe_iff.1 inferInstance

中文:
定理 Ici_infinite
  条件: [NoMaxOrder α] (a : α)
  结论: (Ici a).Infinite
  证明: infinite_coe_iff.1 inferInstance

Depends on / 依赖: infinite_coe_iff
-/
theorem Ici_infinite [NoMaxOrder α] (a : α) : (Ici a).Infinite :=
  infinite_coe_iff.1 inferInstance

end Set
