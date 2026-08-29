/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Data.DFinsupp.Interval
public import Mathlib.Data.DFinsupp.Multiset
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Algebra.Order.Group.Nat

/-!
# Finite intervals of multisets

This file provides the `LocallyFiniteOrder` instance for `Multiset α` and calculates the
cardinality of its finite intervals.

## Implementation notes

We implement the intervals via the intervals on `DFinsupp`, rather than via filtering
`Multiset.Powerset`; this is because `(Multiset.replicate n x).Powerset` has `2^n` entries not `n+1`
entries as it contains duplicates. We do not go via `Finsupp` as this would be noncomputable, and
multisets are typically used computationally.

-/

public section


open Finset DFinsupp Function

open scoped Pointwise

variable {α : Type*}

namespace Multiset

variable [DecidableEq α] (s t : Multiset α)

/--
Instance `instLocallyFiniteOrder` / 实例 `instLocallyFiniteOrder`

English:
instance instLocallyFiniteOrder
  signature: : LocallyFiniteOrder (Multiset α)
  body: LocallyFiniteOrder.ofIcc (Multiset α)
    (fun s t => (Finset.Icc (toDFinsupp s) (toDFinsupp t)).map
      Multiset.equivDFinsupp.toEquiv.symm.toEmbedding)
    fun s t x => by simp

中文:
实例 instLocallyFiniteOrder
  签名: : 局部有限序 (Multiset α)
  定义体: LocallyFiniteOrder.ofIcc (Multiset α)
    (fun s t => (Finset.Icc (toDFinsupp s) (toDFinsupp t)).map
      Multiset.equivDFinsupp.toEquiv.symm.toEmbedding)
    fun s t x => by simp

Depends on / 依赖: Finset, Finset.Icc, LocallyFiniteOrder, LocallyFiniteOrder.ofIcc, Multiset, Multiset.equivDFinsupp.toEquiv.symm.toEmbedding, equivDFinsupp, toDFinsupp, toEmbedding, toEquiv
-/
instance instLocallyFiniteOrder : LocallyFiniteOrder (Multiset α) :=
  LocallyFiniteOrder.ofIcc (Multiset α)
    (fun s t => (Finset.Icc (toDFinsupp s) (toDFinsupp t)).map
      Multiset.equivDFinsupp.toEquiv.symm.toEmbedding)
    fun s t x => by simp

/--
theorem `Icc_eq` / 定理 `Icc_eq`

English:
theorem Icc_eq
  proof: rfl

中文:
定理 Icc_eq
  证明: rfl
-/
theorem Icc_eq :
    Finset.Icc s t = (Finset.Icc (toDFinsupp s) (toDFinsupp t)).map
      Multiset.equivDFinsupp.toEquiv.symm.toEmbedding :=
  rfl

/--
theorem `uIcc_eq` / 定理 `uIcc_eq`

English:
theorem uIcc_eq
  proof: (Icc_eq _ _).trans by simp [uIcc]

中文:
定理 uIcc_eq
  证明: (Icc_eq _ _).trans by simp [uIcc]

Depends on / 依赖: Icc_eq
-/
theorem uIcc_eq :
    uIcc s t =
      (uIcc (toDFinsupp s) (toDFinsupp t)).map Multiset.equivDFinsupp.toEquiv.symm.toEmbedding :=
(Icc_eq _ _).trans by simp [uIcc]

/--
theorem `card_Icc` / 定理 `card_Icc`

English:
theorem card_Icc
  proof: by
  simp_rw [Icc_eq, Finset.card_map, DFinsupp.card_Icc, Nat.card_Icc, Multiset.toDFinsupp_apply,
    toDFinsupp_support]

中文:
定理 card_Icc
  证明: by
  simp_rw [Icc_eq, Finset.card_map, DFinsupp.card_Icc, Nat.card_Icc, Multiset.toDFinsupp_apply,
    toDFinsupp_support]

Depends on / 依赖: DFinsupp, DFinsupp.card_Icc, Finset, Finset.card_map, Icc_eq, Multiset, Multiset.toDFinsupp_apply, Nat.card_Icc, card_Icc, card_map, simp_rw, toDFinsupp_apply, toDFinsupp_support
-/
theorem card_Icc :
    #(Finset.Icc s t) = ∏ i in s.toFinset union t.toFinset, (t.count i + 1 - s.count i) := by
  simp_rw [Icc_eq, Finset.card_map, DFinsupp.card_Icc, Nat.card_Icc, Multiset.toDFinsupp_apply,
    toDFinsupp_support]

/--
theorem `card_Ico` / 定理 `card_Ico`

English:
theorem card_Ico
  proof: by
  rw [Finset.card_Ico_eq_card_Icc_sub_one]; rw [card_Icc]

中文:
定理 card_Ico
  证明: by
  rw [Finset.card_Ico_eq_card_Icc_sub_one]; rw [card_Icc]

Depends on / 依赖: Finset, Finset.card_Ico_eq_card_Icc_sub_one, card_Icc, card_Ico_eq_card_Icc_sub_one
-/
theorem card_Ico :
    #(Finset.Ico s t) = ∏ i in s.toFinset union t.toFinset, (t.count i + 1 - s.count i) - 1 := by
  rw [Finset.card_Ico_eq_card_Icc_sub_one]; rw [card_Icc]

/--
theorem `card_Ioc` / 定理 `card_Ioc`

English:
theorem card_Ioc
  proof: by
  rw [Finset.card_Ioc_eq_card_Icc_sub_one]; rw [card_Icc]

中文:
定理 card_Ioc
  证明: by
  rw [Finset.card_Ioc_eq_card_Icc_sub_one]; rw [card_Icc]

Depends on / 依赖: Finset, Finset.card_Ioc_eq_card_Icc_sub_one, card_Icc, card_Ioc_eq_card_Icc_sub_one
-/
theorem card_Ioc :
    #(Finset.Ioc s t) = ∏ i in s.toFinset union t.toFinset, (t.count i + 1 - s.count i) - 1 := by
  rw [Finset.card_Ioc_eq_card_Icc_sub_one]; rw [card_Icc]

/--
theorem `card_Ioo` / 定理 `card_Ioo`

English:
theorem card_Ioo
  proof: by
  rw [Finset.card_Ioo_eq_card_Icc_sub_two]; rw [card_Icc]

中文:
定理 card_Ioo
  证明: by
  rw [Finset.card_Ioo_eq_card_Icc_sub_two]; rw [card_Icc]

Depends on / 依赖: Finset, Finset.card_Ioo_eq_card_Icc_sub_two, card_Icc, card_Ioo_eq_card_Icc_sub_two
-/
theorem card_Ioo :
    #(Finset.Ioo s t) = ∏ i in s.toFinset union t.toFinset, (t.count i + 1 - s.count i) - 2 := by
  rw [Finset.card_Ioo_eq_card_Icc_sub_two]; rw [card_Icc]

/--
theorem `card_uIcc` / 定理 `card_uIcc`

English:
theorem card_uIcc
  proof: by
  simp_rw [uIcc_eq, Finset.card_map, DFinsupp.card_uIcc, Nat.card_uIcc, Multiset.toDFinsupp_apply,
    toDFinsupp_support]

中文:
定理 card_uIcc
  证明: by
  simp_rw [uIcc_eq, Finset.card_map, DFinsupp.card_uIcc, Nat.card_uIcc, Multiset.toDFinsupp_apply,
    toDFinsupp_support]

Depends on / 依赖: DFinsupp, DFinsupp.card_uIcc, Finset, Finset.card_map, Multiset, Multiset.toDFinsupp_apply, Nat.card_uIcc, card_map, card_uIcc, simp_rw, toDFinsupp_apply, toDFinsupp_support, uIcc_eq
-/
theorem card_uIcc :
    (uIcc s t).card = ∏ i in s.toFinset union t.toFinset, ((t.count i - s.count i : Int).natAbs + 1) := by
  simp_rw [uIcc_eq, Finset.card_map, DFinsupp.card_uIcc, Nat.card_uIcc, Multiset.toDFinsupp_apply,
    toDFinsupp_support]

/--
theorem `card_Iic` / 定理 `card_Iic`

English:
theorem card_Iic
  statement: (Finset.Iic s).card = ∏ i in s.toFinset, (s.count i + 1)
  proof: by
  simp_rw [Iic_eq_Icc, card_Icc, bot_eq_zero, toFinset_zero, empty_union, count_zero, tsub_zero]

中文:
定理 card_Iic
  结论: (有限集.左无界右闭区间 s).card = ∏ i in s.toFinset, (s.count i + 1)
  证明: by
  simp_rw [Iic_eq_Icc, card_Icc, bot_eq_zero, toFinset_zero, empty_union, count_zero, tsub_zero]

Depends on / 依赖: Iic_eq_Icc, bot_eq_zero, card_Icc, count_zero, empty_union, simp_rw, toFinset_zero, tsub_zero
-/
theorem card_Iic : (Finset.Iic s).card = ∏ i in s.toFinset, (s.count i + 1) := by
  simp_rw [Iic_eq_Icc, card_Icc, bot_eq_zero, toFinset_zero, empty_union, count_zero, tsub_zero]

end Multiset
