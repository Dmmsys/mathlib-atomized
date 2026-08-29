/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Finset.Finsupp
public import Mathlib.Data.Finsupp.Order
public import Mathlib.Order.Interval.Finset.Basic

/-!
# Finite intervals of finitely supported functions

This file provides the `LocallyFiniteOrder` instance for `ι →₀ α` when `α` itself is locally
finite and calculates the cardinality of its finite intervals.

## Main declarations

* `Finsupp.rangeSingleton`: Postcomposition with `Singleton.singleton` on `Finset` as a
  `Finsupp`.
* `Finsupp.rangeIcc`: Postcomposition with `Finset.Icc` as a `Finsupp`.

Both these definitions use the fact that `0 = {0}` to ensure that the resulting function is finitely
supported.
-/

@[expose] public section

noncomputable section

open Finset Finsupp Function Pointwise

variable {ι α : Type*}

namespace Finsupp

section RangeSingleton

variable [Zero α] {f : ι ->₀ α} {i : ι} {a : α}

/-- Pointwise `Singleton.singleton` bundled as a `Finsupp`. -/
@[simps]
/--
Definition of `rangeSingleton` / `rangeSingleton` 的定义

English:
definition rangeSingleton
  signature: (f : ι ->₀ α)
  body: {f i}
  support := f.support
  mem_support_toFun i := by
    rw [← not_iff_not]; rw [notMem_support_iff]; rw [not_ne_iff]
    exact singleton_injective.eq_iff.symm

中文:
定义 rangeSingleton
  签名: (f : ι ->₀ α)
  定义体: {f i}
  support := f.support
  mem_support_toFun i := by
    rw [← not_iff_not]; rw [notMem_support_iff]; rw [not_ne_iff]
    exact singleton_injective.eq_iff.symm
-/
def rangeSingleton (f : ι ->₀ α) : ι ->₀ Finset α where
  toFun i := {f i}
  support := f.support
  mem_support_toFun i := by
    rw [← not_iff_not]; rw [notMem_support_iff]; rw [not_ne_iff]
    exact singleton_injective.eq_iff.symm

/--
theorem `mem_rangeSingleton_apply_iff` / 定理 `mem_rangeSingleton_apply_iff`

English:
theorem mem_rangeSingleton_apply_iff
  statement: a in f.rangeSingleton i ↔ a = f i
  proof: mem_singleton

中文:
定理 mem_rangeSingleton_apply_iff
  结论: a in f.rangeSingleton i ↔ a = f i
  证明: mem_singleton

Depends on / 依赖: mem_singleton
-/
theorem mem_rangeSingleton_apply_iff : a in f.rangeSingleton i ↔ a = f i :=
  mem_singleton

end RangeSingleton

section RangeIcc

variable [Zero α] [PartialOrder α] [LocallyFiniteOrder α] [DecidableEq ι]
variable {f g : ι ->₀ α} {i : ι} {a : α}

/-- Pointwise `Finset.Icc` bundled as a `Finsupp`. -/
@[simps apply]
/--
Definition of `rangeIcc` / `rangeIcc` 的定义

English:
definition rangeIcc
  signature: (f g : ι ->₀ α)
  body: Icc (f i) (g i)
  support := f.support union g.support
  mem_support_toFun i := by
    rw [mem_union]; rw [← not_iff_not]; rw [not_or]; rw [notMem_support_iff]; rw [notMem_support_iff]; rw [not_ne_iff]
    exact Icc_eq_singleton_iff.symm

中文:
定义 rangeIcc
  签名: (f g : ι ->₀ α)
  定义体: Icc (f i) (g i)
  support := f.support union g.support
  mem_support_toFun i := by
    rw [mem_union]; rw [← not_iff_not]; rw [not_or]; rw [notMem_support_iff]; rw [notMem_support_iff]; rw [not_ne_iff]
    exact Icc_eq_singleton_iff.symm
-/
def rangeIcc (f g : ι ->₀ α) : ι ->₀ Finset α where
  toFun i := Icc (f i) (g i)
  support := f.support union g.support
  mem_support_toFun i := by
    rw [mem_union]; rw [← not_iff_not]; rw [not_or]; rw [notMem_support_iff]; rw [notMem_support_iff]; rw [not_ne_iff]
    exact Icc_eq_singleton_iff.symm

/--
lemma `coe_rangeIcc` / 引理 `coe_rangeIcc`

English:
lemma coe_rangeIcc
  given: (f g : ι ->₀ α)
  statement: rangeIcc f g i = Icc (f i) (g i)
  proof: rfl

@[simp]

中文:
引理 coe_rangeIcc
  条件: (f g : ι ->₀ α)
  结论: rangeIcc f g i = Icc (f i) (g i)
  证明: rfl

@[simp]
-/
lemma coe_rangeIcc (f g : ι ->₀ α) : rangeIcc f g i = Icc (f i) (g i) := rfl

@[simp]
/--
theorem `rangeIcc_support` / 定理 `rangeIcc_support`

English:
theorem rangeIcc_support
  given: (f g : ι ->₀ α)
  proof: rfl

中文:
定理 rangeIcc_support
  条件: (f g : ι ->₀ α)
  证明: rfl
-/
theorem rangeIcc_support (f g : ι ->₀ α) :
    (rangeIcc f g).support = f.support union g.support := rfl

/--
theorem `mem_rangeIcc_apply_iff` / 定理 `mem_rangeIcc_apply_iff`

English:
theorem mem_rangeIcc_apply_iff
  statement: a in f.rangeIcc g i ↔ f i <= a ∧ a <= g i
  proof: mem_Icc

中文:
定理 mem_rangeIcc_apply_iff
  结论: a in f.rangeIcc g i ↔ f i <= a ∧ a <= g i
  证明: mem_Icc

Depends on / 依赖: mem_Icc
-/
theorem mem_rangeIcc_apply_iff : a in f.rangeIcc g i ↔ f i <= a ∧ a <= g i := mem_Icc

end RangeIcc

section PartialOrder

variable [PartialOrder α] [Zero α] [LocallyFiniteOrder α] [DecidableEq ι] [DecidableEq α]
variable (f g : ι ->₀ α)

/--
Instance `instLocallyFiniteOrder` / 实例 `instLocallyFiniteOrder`

English:
instance instLocallyFiniteOrder
  signature: : LocallyFiniteOrder (ι ->₀ α)
  body: LocallyFiniteOrder.ofIcc (ι ->₀ α) (fun f g => (f.support union g.support).finsupp <| f.rangeIcc g)
    fun f g x => by
      refine
        (mem_finsupp_iff_of_support_subset <| Finset.subset_of_eq <| rangeIcc_support _ _).trans ?_
      simp_rw [mem_rangeIcc_apply_iff]
      exact forall_and

中文:
实例 instLocallyFiniteOrder
  签名: : LocallyFiniteOrder (ι ->₀ α)
  定义体: LocallyFiniteOrder.ofIcc (ι ->₀ α) (fun f g => (f.support union g.support).finsupp <| f.rangeIcc g)
    fun f g x => by
      refine
        (mem_finsupp_iff_of_support_subset <| Finset.subset_of_eq <| rangeIcc_support _ _).trans ?_
      simp_rw [mem_rangeIcc_apply_iff]
      exact forall_and

Depends on / 依赖: Finset, Finset.subset_of_eq, LocallyFiniteOrder, LocallyFiniteOrder.ofIcc, f.rangeIcc, f.support, finsupp, forall_and, g.support, mem_finsupp_iff_of_support_subset, mem_rangeIcc_apply_iff, rangeIcc, rangeIcc_support, simp_rw, subset_of_eq, support
-/
instance instLocallyFiniteOrder : LocallyFiniteOrder (ι ->₀ α) :=
  LocallyFiniteOrder.ofIcc (ι ->₀ α) (fun f g => (f.support union g.support).finsupp <| f.rangeIcc g)
    fun f g x => by
      refine
        (mem_finsupp_iff_of_support_subset <| Finset.subset_of_eq <| rangeIcc_support _ _).trans ?_
      simp_rw [mem_rangeIcc_apply_iff]
      exact forall_and

/--
theorem `Icc_eq` / 定理 `Icc_eq`

English:
theorem Icc_eq
  statement: Icc f g = (f.support union g.support).finsupp (f.rangeIcc g)
  proof: rfl

中文:
定理 Icc_eq
  结论: Icc f g = (f.support union g.support).finsupp (f.rangeIcc g)
  证明: rfl
-/
theorem Icc_eq : Icc f g = (f.support union g.support).finsupp (f.rangeIcc g) := rfl

/--
theorem `card_Icc` / 定理 `card_Icc`

English:
theorem card_Icc
  statement: #(Icc f g) = ∏ i in f.support union g.support, #(Icc (f i) (g i))
  proof: by
  simp_rw [Icc_eq, card_finsupp, coe_rangeIcc]

中文:
定理 card_Icc
  结论: #(Icc f g) = ∏ i in f.support union g.support, #(Icc (f i) (g i))
  证明: by
  simp_rw [Icc_eq, card_finsupp, coe_rangeIcc]

Depends on / 依赖: Icc_eq, card_finsupp, coe_rangeIcc, simp_rw
-/
theorem card_Icc : #(Icc f g) = ∏ i in f.support union g.support, #(Icc (f i) (g i)) := by
  simp_rw [Icc_eq, card_finsupp, coe_rangeIcc]

/--
theorem `card_Ico` / 定理 `card_Ico`

English:
theorem card_Ico
  statement: #(Ico f g) = ∏ i in f.support union g.support, #(Icc (f i) (g i)) - 1
  proof: by
  rw [card_Ico_eq_card_Icc_sub_one]; rw [card_Icc]

中文:
定理 card_Ico
  结论: #(Ico f g) = ∏ i in f.support union g.support, #(Icc (f i) (g i)) - 1
  证明: by
  rw [card_Ico_eq_card_Icc_sub_one]; rw [card_Icc]

Depends on / 依赖: card_Icc, card_Ico_eq_card_Icc_sub_one
-/
theorem card_Ico : #(Ico f g) = ∏ i in f.support union g.support, #(Icc (f i) (g i)) - 1 := by
  rw [card_Ico_eq_card_Icc_sub_one]; rw [card_Icc]

/--
theorem `card_Ioc` / 定理 `card_Ioc`

English:
theorem card_Ioc
  statement: #(Ioc f g) = ∏ i in f.support union g.support, #(Icc (f i) (g i)) - 1
  proof: by
  rw [card_Ioc_eq_card_Icc_sub_one]; rw [card_Icc]

中文:
定理 card_Ioc
  结论: #(Ioc f g) = ∏ i in f.support union g.support, #(Icc (f i) (g i)) - 1
  证明: by
  rw [card_Ioc_eq_card_Icc_sub_one]; rw [card_Icc]

Depends on / 依赖: card_Icc, card_Ioc_eq_card_Icc_sub_one
-/
theorem card_Ioc : #(Ioc f g) = ∏ i in f.support union g.support, #(Icc (f i) (g i)) - 1 := by
  rw [card_Ioc_eq_card_Icc_sub_one]; rw [card_Icc]

/--
theorem `card_Ioo` / 定理 `card_Ioo`

English:
theorem card_Ioo
  statement: #(Ioo f g) = ∏ i in f.support union g.support, #(Icc (f i) (g i)) - 2
  proof: by
  rw [card_Ioo_eq_card_Icc_sub_two]; rw [card_Icc]

中文:
定理 card_Ioo
  结论: #(Ioo f g) = ∏ i in f.support union g.support, #(Icc (f i) (g i)) - 2
  证明: by
  rw [card_Ioo_eq_card_Icc_sub_two]; rw [card_Icc]

Depends on / 依赖: card_Icc, card_Ioo_eq_card_Icc_sub_two
-/
theorem card_Ioo : #(Ioo f g) = ∏ i in f.support union g.support, #(Icc (f i) (g i)) - 2 := by
  rw [card_Ioo_eq_card_Icc_sub_two]; rw [card_Icc]

end PartialOrder

section Lattice
variable [Lattice α] [Zero α] [LocallyFiniteOrder α] (f g : ι ->₀ α)

open scoped Classical in
/--
theorem `card_uIcc` / 定理 `card_uIcc`

English:
theorem card_uIcc
  proof: by
  rw [← support_inf_union_support_sup]; exact card_Icc (_ : ι ->₀ α) _

中文:
定理 card_uIcc
  证明: by
  rw [← support_inf_union_support_sup]; exact card_Icc (_ : ι ->₀ α) _

Depends on / 依赖: card_Icc, support_inf_union_support_sup
-/
theorem card_uIcc :
    #(uIcc f g) = ∏ i in f.support union g.support, #(uIcc (f i) (g i)) := by
  rw [← support_inf_union_support_sup]; exact card_Icc (_ : ι ->₀ α) _

end Lattice

section IsBotZeroClass

variable [AddCommMonoid α] [PartialOrder α] [IsBotZeroClass α]
  [OrderBot α] [LocallyFiniteOrder α]
variable [DecidableEq ι] [DecidableEq α] (f : ι ->₀ α)

/--
theorem `card_Iic` / 定理 `card_Iic`

English:
theorem card_Iic
  statement: #(Iic f) = ∏ i in f.support, #(Iic (f i))
  proof: by
  simp [Iic_eq_Icc, card_Icc, bot_eq_zero]

中文:
定理 card_Iic
  结论: #(Iic f) = ∏ i in f.support, #(Iic (f i))
  证明: by
  simp [Iic_eq_Icc, card_Icc, bot_eq_zero]

Depends on / 依赖: Iic_eq_Icc, bot_eq_zero, card_Icc
-/
theorem card_Iic : #(Iic f) = ∏ i in f.support, #(Iic (f i)) := by
  simp [Iic_eq_Icc, card_Icc, bot_eq_zero]

/--
theorem `card_Iio` / 定理 `card_Iio`

English:
theorem card_Iio
  statement: #(Iio f) = ∏ i in f.support, #(Iic (f i)) - 1
  proof: by
  rw [card_Iio_eq_card_Iic_sub_one]; rw [card_Iic]

中文:
定理 card_Iio
  结论: #(Iio f) = ∏ i in f.support, #(Iic (f i)) - 1
  证明: by
  rw [card_Iio_eq_card_Iic_sub_one]; rw [card_Iic]

Depends on / 依赖: card_Iic, card_Iio_eq_card_Iic_sub_one
-/
theorem card_Iio : #(Iio f) = ∏ i in f.support, #(Iic (f i)) - 1 := by
  rw [card_Iio_eq_card_Iic_sub_one]; rw [card_Iic]

end IsBotZeroClass

end Finsupp
