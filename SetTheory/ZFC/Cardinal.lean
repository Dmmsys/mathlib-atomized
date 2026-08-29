/-
Copyright (c) 2025 Dexin Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dexin Zhang
-/
module

public import Mathlib.SetTheory.Cardinal.Basic
public import Mathlib.SetTheory.ZFC.Basic

/-!
# Cardinalities of ZFC sets

In this file, we define the cardinalities of ZFC sets as `ZFSet.{u} → Cardinal.{u}`.

## Definitions

* `ZFSet.card`: Cardinality of a ZFC set.
-/

@[expose] public section

universe u v

open Cardinal

namespace ZFSet

/--
Definition of `card` / `card` 的定义

English:
definition card
  signature: (x : ZFSet.{u})
  body: #(Shrink x)

中文:
定义 card
  签名: (x : ZFSet.{u})
  定义体: #(Shrink x)

Depends on / 依赖: Shrink
-/
def card (x : ZFSet.{u}) : Cardinal.{u} := #(Shrink x)

variable {x y : ZFSet.{u}}

/--
theorem `cardinalMk_coe_sort` / 定理 `cardinalMk_coe_sort`

English:
theorem cardinalMk_coe_sort
  statement: #x = lift.{u + 1, u} (card x)
  proof: by
  rw [card]; rw [lift_mk_shrink'']

@[gcongr]

中文:
定理 cardinalMk_coe_sort
  结论: #x = lift.{u + 1, u} (card x)
  证明: by
  rw [card]; rw [lift_mk_shrink'']

@[gcongr]

Depends on / 依赖: lift_mk_shrink
-/
theorem cardinalMk_coe_sort : #x = lift.{u + 1, u} (card x) := by
  rw [card]; rw [lift_mk_shrink'']

@[gcongr]
/--
theorem `card_mono` / 定理 `card_mono`

English:
theorem card_mono
  given: (h : x subseteq y)
  statement: card x <= card y
  proof: by
  simpa [cardinalMk_coe_sort] using mk_le_mk_of_subset (coe_subset_coe.2 h)

@[simp]

中文:
定理 card_mono
  条件: (h : x subseteq y)
  结论: card x <= card y
  证明: by
  simpa [cardinalMk_coe_sort] using mk_le_mk_of_subset (coe_subset_coe.2 h)

@[simp]

Depends on / 依赖: cardinalMk_coe_sort, coe_subset_coe, mk_le_mk_of_subset
-/
theorem card_mono (h : x subseteq y) : card x <= card y := by
  simpa [cardinalMk_coe_sort] using mk_le_mk_of_subset (coe_subset_coe.2 h)

@[simp]
/--
theorem `card_empty` / 定理 `card_empty`

English:
theorem card_empty
  statement: card ∅ = 0
  proof: by
  rw [← lift_inj]; rw [← cardinalMk_coe_sort]
  simp

中文:
定理 card_empty
  结论: card ∅ = 0
  证明: by
  rw [← lift_inj]; rw [← cardinalMk_coe_sort]
  simp

Depends on / 依赖: cardinalMk_coe_sort, lift_inj
-/
theorem card_empty : card ∅ = 0 := by
  rw [← lift_inj]; rw [← cardinalMk_coe_sort]
  simp

/--
theorem `card_insert_le` / 定理 `card_insert_le`

English:
theorem card_insert_le
  statement: card (insert x y) <= card y + 1
  proof: by
  rw [← lift_le.{u + 1}]
  simpa [← cardinalMk_coe_sort] using! mk_insert_le

中文:
定理 card_insert_le
  结论: card (insert x y) <= card y + 1
  证明: by
  rw [← lift_le.{u + 1}]
  simpa [← cardinalMk_coe_sort] using! mk_insert_le

Depends on / 依赖: cardinalMk_coe_sort, lift_le, mk_insert_le
-/
theorem card_insert_le : card (insert x y) <= card y + 1 := by
  rw [← lift_le.{u + 1}]
  simpa [← cardinalMk_coe_sort] using! mk_insert_le

/--
theorem `card_insert` / 定理 `card_insert`

English:
theorem card_insert
  given: (h : x ∉ y)
  statement: card (insert x y) = card y + 1
  proof: by
  rw [← lift_inj.{u]; rw [u + 1}]
  simpa [← cardinalMk_coe_sort] using! mk_insert (SetLike.mem_coe.not.2 h)

@[simp]

中文:
定理 card_insert
  条件: (h : x ∉ y)
  结论: card (insert x y) = card y + 1
  证明: by
  rw [← lift_inj.{u]; rw [u + 1}]
  simpa [← cardinalMk_coe_sort] using! mk_insert (SetLike.mem_coe.not.2 h)

@[simp]

Depends on / 依赖: SetLike, SetLike.mem_coe.not, cardinalMk_coe_sort, lift_inj, mem_coe, mk_insert
-/
theorem card_insert (h : x ∉ y) : card (insert x y) = card y + 1 := by
  rw [← lift_inj.{u]; rw [u + 1}]
  simpa [← cardinalMk_coe_sort] using! mk_insert (SetLike.mem_coe.not.2 h)

@[simp]
/--
theorem `card_singleton` / 定理 `card_singleton`

English:
theorem card_singleton
  statement: card {x} = 1
  proof: by
  simpa [notMem_singleton] using card_insert (notMem_empty x)

中文:
定理 card_singleton
  结论: card {x} = 1
  证明: by
  simpa [notMem_singleton] using card_insert (notMem_empty x)

Depends on / 依赖: card_insert, notMem_empty, notMem_singleton
-/
theorem card_singleton : card {x} = 1 := by
  simpa [notMem_singleton] using card_insert (notMem_empty x)

/--
theorem `card_pair_of_ne` / 定理 `card_pair_of_ne`

English:
theorem card_pair_of_ne
  given: (h : x != y)
  statement: card {x, y} = 2
  proof: by
  convert! card_insert (notMem_singleton.2 h)
  rw [card_singleton]; rw [one_add_one_eq_two]

中文:
定理 card_pair_of_ne
  条件: (h : x != y)
  结论: card {x, y} = 2
  证明: by
  convert! card_insert (notMem_singleton.2 h)
  rw [card_singleton]; rw [one_add_one_eq_two]

Depends on / 依赖: card_insert, card_singleton, convert, notMem_singleton, one_add_one_eq_two
-/
theorem card_pair_of_ne (h : x != y) : card {x, y} = 2 := by
  convert! card_insert (notMem_singleton.2 h)
  rw [card_singleton]; rw [one_add_one_eq_two]

/--
theorem `card_union_le` / 定理 `card_union_le`

English:
theorem card_union_le
  statement: card (x union y) <= card x + card y
  proof: by
  rw [← lift_le.{u + 1}]
  simpa [← cardinalMk_coe_sort] using! mk_union_le (x : Set ZFSet) y

@[simp]

中文:
定理 card_union_le
  结论: card (x union y) <= card x + card y
  证明: by
  rw [← lift_le.{u + 1}]
  simpa [← cardinalMk_coe_sort] using! mk_union_le (x : Set ZFSet) y

@[simp]

Depends on / 依赖: cardinalMk_coe_sort, lift_le, mk_union_le
-/
theorem card_union_le : card (x union y) <= card x + card y := by
  rw [← lift_le.{u + 1}]
  simpa [← cardinalMk_coe_sort] using! mk_union_le (x : Set ZFSet) y

@[simp]
/--
theorem `card_powerset` / 定理 `card_powerset`

English:
theorem card_powerset
  given: (x : ZFSet.{u})
  statement: card (powerset x) = 2 ^ card x
  proof: by
  rw [← lift_inj.{u]; rw [u + 1}]
  simpa [← cardinalMk_coe_sort] using mk_congr (powersetEquiv x)

中文:
定理 card_powerset
  条件: (x : ZFSet.{u})
  结论: card (powerset x) = 2 ^ card x
  证明: by
  rw [← lift_inj.{u]; rw [u + 1}]
  simpa [← cardinalMk_coe_sort] using mk_congr (powersetEquiv x)

Depends on / 依赖: cardinalMk_coe_sort, lift_inj, mk_congr, powersetEquiv
-/
theorem card_powerset (x : ZFSet.{u}) : card (powerset x) = 2 ^ card x := by
  rw [← lift_inj.{u]; rw [u + 1}]
  simpa [← cardinalMk_coe_sort] using mk_congr (powersetEquiv x)

/--
theorem `card_image_le` / 定理 `card_image_le`

English:
theorem card_image_le
  given: {f : ZFSet -> ZFSet} [Definable₁ f]
  proof: by
  simpa [cardinalMk_coe_sort, ← coe_image, -mem_image] using mk_image_le (f := f) (s := x)

中文:
定理 card_image_le
  条件: {f : ZFSet -> ZFSet} [Definable₁ f]
  证明: by
  simpa [cardinalMk_coe_sort, ← coe_image, -mem_image] using mk_image_le (f := f) (s := x)

Depends on / 依赖: cardinalMk_coe_sort, coe_image, mem_image, mk_image_le
-/
theorem card_image_le {f : ZFSet -> ZFSet} [Definable₁ f] :
    card (image f x) <= card x := by
  simpa [cardinalMk_coe_sort, ← coe_image, -mem_image] using mk_image_le (f := f) (s := x)

/--
theorem `lift_card_range_le` / 定理 `lift_card_range_le`

English:
theorem lift_card_range_le
  given: {α} [Small.{v, u} α] {f : α -> ZFSet.{v}}
  proof: by
  rw [← lift_le.{max u (v + 1)}]; rw [lift_lift.{v}]; rw [lift_umax.{u]; rw [v + 1}]
  simpa [cardinalMk_coe_sort, ← coe_range, -mem_range] using mk_range_le_lift (f := f)

中文:
定理 lift_card_range_le
  条件: {α} [Small.{v, u} α] {f : α -> ZFSet.{v}}
  证明: by
  rw [← lift_le.{max u (v + 1)}]; rw [lift_lift.{v}]; rw [lift_umax.{u]; rw [v + 1}]
  simpa [cardinalMk_coe_sort, ← coe_range, -mem_range] using mk_range_le_lift (f := f)

Depends on / 依赖: cardinalMk_coe_sort, coe_range, lift_le, lift_lift, lift_umax, mem_range, mk_range_le_lift
-/
theorem lift_card_range_le {α} [Small.{v, u} α] {f : α -> ZFSet.{v}} :
    lift.{u} (card (range f)) <= lift.{v} #α := by
  rw [← lift_le.{max u (v + 1)}]; rw [lift_lift.{v}]; rw [lift_umax.{u]; rw [v + 1}]
  simpa [cardinalMk_coe_sort, ← coe_range, -mem_range] using mk_range_le_lift (f := f)

/--
theorem `iSup_card_le_card_iUnion` / 定理 `iSup_card_le_card_iUnion`

English:
theorem iSup_card_le_card_iUnion
  given: {α} [Small.{v, u} α] {f : α -> ZFSet.{v}}
  proof: by
  simpa [cardinalMk_coe_sort, ← coe_iUnion, ← lift_iSup bddAbove_of_small, -mem_iUnion] using
    iSup_mk_le_mk_iUnion (f := SetLike.coe ∘ f)

中文:
定理 iSup_card_le_card_iUnion
  条件: {α} [Small.{v, u} α] {f : α -> ZFSet.{v}}
  证明: by
  simpa [cardinalMk_coe_sort, ← coe_iUnion, ← lift_iSup bddAbove_of_small, -mem_iUnion] using
    iSup_mk_le_mk_iUnion (f := SetLike.coe ∘ f)

Depends on / 依赖: SetLike, SetLike.coe, bddAbove_of_small, cardinalMk_coe_sort, coe_iUnion, iSup_mk_le_mk_iUnion, lift_iSup, mem_iUnion
-/
theorem iSup_card_le_card_iUnion {α} [Small.{v, u} α] {f : α -> ZFSet.{v}} :
    ⨆ i, card (f i) <= card (⋃ i, f i) := by
  simpa [cardinalMk_coe_sort, ← coe_iUnion, ← lift_iSup bddAbove_of_small, -mem_iUnion] using
    iSup_mk_le_mk_iUnion (f := SetLike.coe ∘ f)

/--
theorem `lift_card_iUnion_le_sum_card` / 定理 `lift_card_iUnion_le_sum_card`

English:
theorem lift_card_iUnion_le_sum_card
  given: {α} [Small.{v, u} α] {f : α -> ZFSet.{v}}
  proof: by
  rw [← lift_le.{max u (v + 1)}]; rw [lift_umax.{max u v]; rw [v + 1}]
  simpa [cardinalMk_coe_sort, ← coe_iUnion, -mem_iUnion] using
    mk_iUnion_le_sum_mk_lift (f := SetLike.coe ∘ f)

中文:
定理 lift_card_iUnion_le_sum_card
  条件: {α} [Small.{v, u} α] {f : α -> ZFSet.{v}}
  证明: by
  rw [← lift_le.{max u (v + 1)}]; rw [lift_umax.{max u v]; rw [v + 1}]
  simpa [cardinalMk_coe_sort, ← coe_iUnion, -mem_iUnion] using
    mk_iUnion_le_sum_mk_lift (f := SetLike.coe ∘ f)

Depends on / 依赖: SetLike, SetLike.coe, cardinalMk_coe_sort, coe_iUnion, lift_le, lift_umax, mem_iUnion, mk_iUnion_le_sum_mk_lift
-/
theorem lift_card_iUnion_le_sum_card {α} [Small.{v, u} α] {f : α -> ZFSet.{v}} :
    lift (card (⋃ i, f i)) <= sum fun i => card (f i) := by
  rw [← lift_le.{max u (v + 1)}]; rw [lift_umax.{max u v]; rw [v + 1}]
  simpa [cardinalMk_coe_sort, ← coe_iUnion, -mem_iUnion] using
    mk_iUnion_le_sum_mk_lift (f := SetLike.coe ∘ f)

end ZFSet
