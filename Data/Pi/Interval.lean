/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.Interval.Finset.Basic
public import Mathlib.Data.Fintype.BigOperators

/-!
# Intervals in a pi type

This file shows that (dependent) functions to locally finite orders equipped with the pointwise
order are locally finite and calculates the cardinality of their intervals.
-/

public section


open Finset Fintype

variable {ι : Type*} {α : ι -> Type*} [Fintype ι] [DecidableEq ι] [forall i, DecidableEq (α i)]

namespace Pi
section PartialOrder
variable [forall i, PartialOrder (α i)]

section LocallyFiniteOrder
variable [forall i, LocallyFiniteOrder (α i)]

/--
Instance `instLocallyFiniteOrder` / 实例 `instLocallyFiniteOrder`

English:
instance instLocallyFiniteOrder
  signature: : LocallyFiniteOrder (forall i, α i)
  body: LocallyFiniteOrder.ofIcc _ (fun a b => piFinset fun i => Icc (a i) (b i)) fun a b x => by
    simp_rw [mem_piFinset, mem_Icc, le_def, forall_and]

中文:
实例 instLocallyFiniteOrder
  签名: : LocallyFiniteOrder (对任意 i, α i)
  定义体: LocallyFiniteOrder.ofIcc _ (fun a b => piFinset fun i => Icc (a i) (b i)) fun a b x => by
    simp_rw [mem_piFinset, mem_Icc, le_def, forall_and]

Depends on / 依赖: LocallyFiniteOrder, LocallyFiniteOrder.ofIcc, forall_and, le_def, mem_Icc, mem_piFinset, piFinset, simp_rw
-/
instance instLocallyFiniteOrder : LocallyFiniteOrder (forall i, α i) :=
  LocallyFiniteOrder.ofIcc _ (fun a b => piFinset fun i => Icc (a i) (b i)) fun a b x => by
    simp_rw [mem_piFinset, mem_Icc, le_def, forall_and]

variable (a b : forall i, α i)

/--
theorem `Icc_eq` / 定理 `Icc_eq`

English:
theorem Icc_eq
  statement: Icc a b = piFinset fun i => Icc (a i) (b i)
  proof: rfl

中文:
定理 Icc_eq
  结论: Icc a b = piFinset fun i => Icc (a i) (b i)
  证明: rfl
-/
theorem Icc_eq : Icc a b = piFinset fun i => Icc (a i) (b i) :=
  rfl

/--
theorem `card_Icc` / 定理 `card_Icc`

English:
theorem card_Icc
  statement: #(Icc a b) = ∏ i, #(Icc (a i) (b i))
  proof: card_piFinset _

中文:
定理 card_Icc
  结论: #(Icc a b) = ∏ i, #(Icc (a i) (b i))
  证明: card_piFinset _

Depends on / 依赖: card_piFinset
-/
theorem card_Icc : #(Icc a b) = ∏ i, #(Icc (a i) (b i)) :=
  card_piFinset _

/--
theorem `card_Ico` / 定理 `card_Ico`

English:
theorem card_Ico
  statement: #(Ico a b) = ∏ i, #(Icc (a i) (b i)) - 1
  proof: by
  rw [card_Ico_eq_card_Icc_sub_one]; rw [card_Icc]

中文:
定理 card_Ico
  结论: #(Ico a b) = ∏ i, #(Icc (a i) (b i)) - 1
  证明: by
  rw [card_Ico_eq_card_Icc_sub_one]; rw [card_Icc]

Depends on / 依赖: card_Icc, card_Ico_eq_card_Icc_sub_one
-/
theorem card_Ico : #(Ico a b) = ∏ i, #(Icc (a i) (b i)) - 1 := by
  rw [card_Ico_eq_card_Icc_sub_one]; rw [card_Icc]

/--
theorem `card_Ioc` / 定理 `card_Ioc`

English:
theorem card_Ioc
  statement: #(Ioc a b) = ∏ i, #(Icc (a i) (b i)) - 1
  proof: by
  rw [card_Ioc_eq_card_Icc_sub_one]; rw [card_Icc]

中文:
定理 card_Ioc
  结论: #(Ioc a b) = ∏ i, #(Icc (a i) (b i)) - 1
  证明: by
  rw [card_Ioc_eq_card_Icc_sub_one]; rw [card_Icc]

Depends on / 依赖: card_Icc, card_Ioc_eq_card_Icc_sub_one
-/
theorem card_Ioc : #(Ioc a b) = ∏ i, #(Icc (a i) (b i)) - 1 := by
  rw [card_Ioc_eq_card_Icc_sub_one]; rw [card_Icc]

/--
theorem `card_Ioo` / 定理 `card_Ioo`

English:
theorem card_Ioo
  statement: #(Ioo a b) = ∏ i, #(Icc (a i) (b i)) - 2
  proof: by
  rw [card_Ioo_eq_card_Icc_sub_two]; rw [card_Icc]

中文:
定理 card_Ioo
  结论: #(Ioo a b) = ∏ i, #(Icc (a i) (b i)) - 2
  证明: by
  rw [card_Ioo_eq_card_Icc_sub_two]; rw [card_Icc]

Depends on / 依赖: card_Icc, card_Ioo_eq_card_Icc_sub_two
-/
theorem card_Ioo : #(Ioo a b) = ∏ i, #(Icc (a i) (b i)) - 2 := by
  rw [card_Ioo_eq_card_Icc_sub_two]; rw [card_Icc]

end LocallyFiniteOrder

section LocallyFiniteOrderBot
variable [forall i, LocallyFiniteOrderBot (α i)] (b : forall i, α i)

/--
Instance `instLocallyFiniteOrderBot` / 实例 `instLocallyFiniteOrderBot`

English:
instance instLocallyFiniteOrderBot
  signature: : LocallyFiniteOrderBot (forall i, α i)
  body: .ofIic _ (fun b => piFinset fun i => Iic (b i)) fun b x => by
    simp_rw [mem_piFinset, mem_Iic, le_def]

中文:
实例 instLocallyFiniteOrderBot
  签名: : LocallyFiniteOrderBot (对任意 i, α i)
  定义体: .ofIic _ (fun b => piFinset fun i => Iic (b i)) fun b x => by
    simp_rw [mem_piFinset, mem_Iic, le_def]

Depends on / 依赖: le_def, mem_Iic, mem_piFinset, piFinset, simp_rw
-/
instance instLocallyFiniteOrderBot : LocallyFiniteOrderBot (forall i, α i) :=
  .ofIic _ (fun b => piFinset fun i => Iic (b i)) fun b x => by
    simp_rw [mem_piFinset, mem_Iic, le_def]

/--
lemma `card_Iic` / 引理 `card_Iic`

English:
lemma card_Iic
  statement: #(Iic b) = ∏ i, #(Iic (b i))
  proof: card_piFinset _

中文:
引理 card_Iic
  结论: #(Iic b) = ∏ i, #(Iic (b i))
  证明: card_piFinset _

Depends on / 依赖: card_piFinset
-/
lemma card_Iic : #(Iic b) = ∏ i, #(Iic (b i)) := card_piFinset _
/--
lemma `card_Iio` / 引理 `card_Iio`

English:
lemma card_Iio
  statement: #(Iio b) = ∏ i, #(Iic (b i)) - 1
  proof: by rw [card_Iio_eq_card_Iic_sub_one, card_Iic]

中文:
引理 card_Iio
  结论: #(Iio b) = ∏ i, #(Iic (b i)) - 1
  证明: by rw [card_Iio_eq_card_Iic_sub_one, card_Iic]

Depends on / 依赖: card_Iic, card_Iio_eq_card_Iic_sub_one
-/
lemma card_Iio : #(Iio b) = ∏ i, #(Iic (b i)) - 1 := by rw [card_Iio_eq_card_Iic_sub_one, card_Iic]

end LocallyFiniteOrderBot

section LocallyFiniteOrderTop
variable [forall i, LocallyFiniteOrderTop (α i)] (a : forall i, α i)

/--
Instance `instLocallyFiniteOrderTop` / 实例 `instLocallyFiniteOrderTop`

English:
instance instLocallyFiniteOrderTop
  signature: : LocallyFiniteOrderTop (forall i, α i)
  body: LocallyFiniteOrderTop.ofIci _ (fun a => piFinset fun i => Ici (a i)) fun a x => by
    simp_rw [mem_piFinset, mem_Ici, le_def]

中文:
实例 instLocallyFiniteOrderTop
  签名: : LocallyFiniteOrderTop (对任意 i, α i)
  定义体: LocallyFiniteOrderTop.ofIci _ (fun a => piFinset fun i => Ici (a i)) fun a x => by
    simp_rw [mem_piFinset, mem_Ici, le_def]

Depends on / 依赖: LocallyFiniteOrderTop, LocallyFiniteOrderTop.ofIci, le_def, mem_Ici, mem_piFinset, piFinset, simp_rw
-/
instance instLocallyFiniteOrderTop : LocallyFiniteOrderTop (forall i, α i) :=
  LocallyFiniteOrderTop.ofIci _ (fun a => piFinset fun i => Ici (a i)) fun a x => by
    simp_rw [mem_piFinset, mem_Ici, le_def]

/--
lemma `card_Ici` / 引理 `card_Ici`

English:
lemma card_Ici
  statement: #(Ici a) = ∏ i, #(Ici (a i))
  proof: card_piFinset _

中文:
引理 card_Ici
  结论: #(Ici a) = ∏ i, #(Ici (a i))
  证明: card_piFinset _

Depends on / 依赖: card_piFinset
-/
lemma card_Ici : #(Ici a) = ∏ i, #(Ici (a i)) := card_piFinset _
/--
lemma `card_Ioi` / 引理 `card_Ioi`

English:
lemma card_Ioi
  statement: #(Ioi a) = ∏ i, #(Ici (a i)) - 1
  proof: by rw [card_Ioi_eq_card_Ici_sub_one, card_Ici]

中文:
引理 card_Ioi
  结论: #(Ioi a) = ∏ i, #(Ici (a i)) - 1
  证明: by rw [card_Ioi_eq_card_Ici_sub_one, card_Ici]

Depends on / 依赖: card_Ici, card_Ioi_eq_card_Ici_sub_one
-/
lemma card_Ioi : #(Ioi a) = ∏ i, #(Ici (a i)) - 1 := by rw [card_Ioi_eq_card_Ici_sub_one, card_Ici]

end LocallyFiniteOrderTop
end PartialOrder

section Lattice
variable [forall i, Lattice (α i)] [forall i, LocallyFiniteOrder (α i)] (a b : forall i, α i)

/--
theorem `uIcc_eq` / 定理 `uIcc_eq`

English:
theorem uIcc_eq
  statement: uIcc a b = piFinset fun i => uIcc (a i) (b i)
  proof: rfl

中文:
定理 uIcc_eq
  结论: uIcc a b = piFinset fun i => uIcc (a i) (b i)
  证明: rfl
-/
theorem uIcc_eq : uIcc a b = piFinset fun i => uIcc (a i) (b i) := rfl

/--
theorem `card_uIcc` / 定理 `card_uIcc`

English:
theorem card_uIcc
  statement: #(uIcc a b) = ∏ i, #(uIcc (a i) (b i))
  proof: card_Icc _ _

中文:
定理 card_uIcc
  结论: #(uIcc a b) = ∏ i, #(uIcc (a i) (b i))
  证明: card_Icc _ _

Depends on / 依赖: card_Icc
-/
theorem card_uIcc : #(uIcc a b) = ∏ i, #(uIcc (a i) (b i)) := card_Icc _ _

end Lattice
end Pi
