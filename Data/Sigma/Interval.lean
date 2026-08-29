/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Sigma.Order
public import Mathlib.Order.Interval.Finset.Defs

/-!
# Finite intervals in a sigma type

This file provides the `LocallyFiniteOrder` instance for the disjoint sum of orders `Σ i, α i` and
calculates the cardinality of its finite intervals.

## TODO

Do the same for the lexicographical order
-/

public section


open Finset Function

namespace Sigma

variable {ι : Type*} {α : ι -> Type*}

/-! ### Disjoint sum of orders -/


section Disjoint

section LocallyFiniteOrder
variable [DecidableEq ι] [forall i, Preorder (α i)] [forall i, LocallyFiniteOrder (α i)]

/--
Instance `instLocallyFiniteOrder` / 实例 `instLocallyFiniteOrder`

English:
instance instLocallyFiniteOrder
  signature: : LocallyFiniteOrder (Σ i, α i) where
  body: sigmaLift fun _ => Icc
  finsetIco := sigmaLift fun _ => Ico
  finsetIoc := sigmaLift fun _ => Ioc
  finsetIoo := sigmaLift fun _ => Ioo
  finset_mem_Icc := fun ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩ => by
    simp_rw [mem_sigmaLift, le_def, mem_Icc, exists_and_left, ← exists_and_right, ← exists_prop]
    exact exist

中文:
实例 instLocallyFiniteOrder
  签名: : 局部有限序 (Σ i, α i) where
  定义体: sigmaLift fun _ => Icc
  finsetIco := sigmaLift fun _ => Ico
  finsetIoc := sigmaLift fun _ => Ioc
  finsetIoo := sigmaLift fun _ => Ioo
  finset_mem_Icc := fun ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩ => by
    simp_rw [mem_sigmaLift, le_def, mem_Icc, exists_and_left, ← exists_and_right, ← exists_prop]
    exact exist

Depends on / 依赖: sigmaLift
-/
instance instLocallyFiniteOrder : LocallyFiniteOrder (Σ i, α i) where
  finsetIcc := sigmaLift fun _ => Icc
  finsetIco := sigmaLift fun _ => Ico
  finsetIoc := sigmaLift fun _ => Ioc
  finsetIoo := sigmaLift fun _ => Ioo
  finset_mem_Icc := fun ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩ => by
    simp_rw [mem_sigmaLift, le_def, mem_Icc, exists_and_left, ← exists_and_right, ← exists_prop]
    exact exists₂_congr fun _ _ => by constructor <;> rintro ⟨⟨⟩, ht⟩ <;> exact ⟨rfl, ht⟩
  finset_mem_Ico := fun ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩ => by
    simp_rw [mem_sigmaLift, le_def, lt_def, mem_Ico, exists_and_left, ← exists_and_right, ←
      exists_prop]
    exact exists₂_congr fun _ _ => by constructor <;> rintro ⟨⟨⟩, ht⟩ <;> exact ⟨rfl, ht⟩
  finset_mem_Ioc := fun ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩ => by
    simp_rw [mem_sigmaLift, le_def, lt_def, mem_Ioc, exists_and_left, ← exists_and_right, ←
      exists_prop]
    exact exists₂_congr fun _ _ => by constructor <;> rintro ⟨⟨⟩, ht⟩ <;> exact ⟨rfl, ht⟩
  finset_mem_Ioo := fun ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩ => by
    simp_rw [mem_sigmaLift, lt_def, mem_Ioo, exists_and_left, ← exists_and_right, ← exists_prop]
    exact exists₂_congr fun _ _ => by constructor <;> rintro ⟨⟨⟩, ht⟩ <;> exact ⟨rfl, ht⟩

section

variable (a b : Σ i, α i)

/--
theorem `card_Icc` / 定理 `card_Icc`

English:
theorem card_Icc
  statement: #(Icc a b) = if h : a.1 = b.1 then #(Icc (h.rec a.2) b.2) else 0
  proof: card_sigmaLift (fun _ => Icc) _ _

中文:
定理 card_Icc
  结论: #(闭区间 a b) = if h : a.1 = b.1 then #(闭区间 (h.rec a.2) b.2) else 0
  证明: card_sigmaLift (fun _ => Icc) _ _

Depends on / 依赖: card_sigmaLift
-/
theorem card_Icc : #(Icc a b) = if h : a.1 = b.1 then #(Icc (h.rec a.2) b.2) else 0 :=
  card_sigmaLift (fun _ => Icc) _ _

/--
theorem `card_Ico` / 定理 `card_Ico`

English:
theorem card_Ico
  statement: #(Ico a b) = if h : a.1 = b.1 then #(Ico (h.rec a.2) b.2) else 0
  proof: card_sigmaLift (fun _ => Ico) _ _

中文:
定理 card_Ico
  结论: #(左闭右开区间 a b) = if h : a.1 = b.1 then #(左闭右开区间 (h.rec a.2) b.2) else 0
  证明: card_sigmaLift (fun _ => Ico) _ _

Depends on / 依赖: card_sigmaLift
-/
theorem card_Ico : #(Ico a b) = if h : a.1 = b.1 then #(Ico (h.rec a.2) b.2) else 0 :=
  card_sigmaLift (fun _ => Ico) _ _

/--
theorem `card_Ioc` / 定理 `card_Ioc`

English:
theorem card_Ioc
  statement: #(Ioc a b) = if h : a.1 = b.1 then #(Ioc (h.rec a.2) b.2) else 0
  proof: card_sigmaLift (fun _ => Ioc) _ _

中文:
定理 card_Ioc
  结论: #(左开右闭区间 a b) = if h : a.1 = b.1 then #(左开右闭区间 (h.rec a.2) b.2) else 0
  证明: card_sigmaLift (fun _ => Ioc) _ _

Depends on / 依赖: card_sigmaLift
-/
theorem card_Ioc : #(Ioc a b) = if h : a.1 = b.1 then #(Ioc (h.rec a.2) b.2) else 0 :=
  card_sigmaLift (fun _ => Ioc) _ _

/--
theorem `card_Ioo` / 定理 `card_Ioo`

English:
theorem card_Ioo
  statement: #(Ioo a b) = if h : a.1 = b.1 then #(Ioo (h.rec a.2) b.2) else 0
  proof: card_sigmaLift (fun _ => Ioo) _ _

中文:
定理 card_Ioo
  结论: #(开区间 a b) = if h : a.1 = b.1 then #(开区间 (h.rec a.2) b.2) else 0
  证明: card_sigmaLift (fun _ => Ioo) _ _

Depends on / 依赖: card_sigmaLift
-/
theorem card_Ioo : #(Ioo a b) = if h : a.1 = b.1 then #(Ioo (h.rec a.2) b.2) else 0 :=
  card_sigmaLift (fun _ => Ioo) _ _

end

variable (i : ι) (a b : α i)

@[simp]
/--
theorem `Icc_mk_mk` / 定理 `Icc_mk_mk`

English:
theorem Icc_mk_mk
  statement: Icc (⟨i, a⟩ : Sigma α) ⟨i, b⟩ = (Icc a b).map (Embedding.sigmaMk i)
  proof: dif_pos rfl

@[simp]

中文:
定理 Icc_mk_mk
  结论: 闭区间 (⟨i, a⟩ : 依赖和类型 α) ⟨i, b⟩ = (闭区间 a b).map (嵌入.sigmaMk i)
  证明: dif_pos rfl

@[simp]

Depends on / 依赖: dif_pos
-/
theorem Icc_mk_mk : Icc (⟨i, a⟩ : Sigma α) ⟨i, b⟩ = (Icc a b).map (Embedding.sigmaMk i) :=
  dif_pos rfl

@[simp]
/--
theorem `Ico_mk_mk` / 定理 `Ico_mk_mk`

English:
theorem Ico_mk_mk
  statement: Ico (⟨i, a⟩ : Sigma α) ⟨i, b⟩ = (Ico a b).map (Embedding.sigmaMk i)
  proof: dif_pos rfl

@[simp]

中文:
定理 Ico_mk_mk
  结论: 左闭右开区间 (⟨i, a⟩ : 依赖和类型 α) ⟨i, b⟩ = (左闭右开区间 a b).map (嵌入.sigmaMk i)
  证明: dif_pos rfl

@[simp]

Depends on / 依赖: dif_pos
-/
theorem Ico_mk_mk : Ico (⟨i, a⟩ : Sigma α) ⟨i, b⟩ = (Ico a b).map (Embedding.sigmaMk i) :=
  dif_pos rfl

@[simp]
/--
theorem `Ioc_mk_mk` / 定理 `Ioc_mk_mk`

English:
theorem Ioc_mk_mk
  statement: Ioc (⟨i, a⟩ : Sigma α) ⟨i, b⟩ = (Ioc a b).map (Embedding.sigmaMk i)
  proof: dif_pos rfl

@[simp]

中文:
定理 Ioc_mk_mk
  结论: 左开右闭区间 (⟨i, a⟩ : 依赖和类型 α) ⟨i, b⟩ = (左开右闭区间 a b).map (嵌入.sigmaMk i)
  证明: dif_pos rfl

@[simp]

Depends on / 依赖: dif_pos
-/
theorem Ioc_mk_mk : Ioc (⟨i, a⟩ : Sigma α) ⟨i, b⟩ = (Ioc a b).map (Embedding.sigmaMk i) :=
  dif_pos rfl

@[simp]
/--
theorem `Ioo_mk_mk` / 定理 `Ioo_mk_mk`

English:
theorem Ioo_mk_mk
  statement: Ioo (⟨i, a⟩ : Sigma α) ⟨i, b⟩ = (Ioo a b).map (Embedding.sigmaMk i)
  proof: dif_pos rfl

中文:
定理 Ioo_mk_mk
  结论: 开区间 (⟨i, a⟩ : 依赖和类型 α) ⟨i, b⟩ = (开区间 a b).map (嵌入.sigmaMk i)
  证明: dif_pos rfl

Depends on / 依赖: dif_pos
-/
theorem Ioo_mk_mk : Ioo (⟨i, a⟩ : Sigma α) ⟨i, b⟩ = (Ioo a b).map (Embedding.sigmaMk i) :=
  dif_pos rfl

end LocallyFiniteOrder

section LocallyFiniteOrderBot
variable [forall i, Preorder (α i)] [forall i, LocallyFiniteOrderBot (α i)]

/--
Instance `instLocallyFiniteOrderBot` / 实例 `instLocallyFiniteOrderBot`

English:
instance instLocallyFiniteOrderBot
  signature: : LocallyFiniteOrderBot (Σ i, α i) where
  body: fun ⟨i, a⟩ ⟨j, b⟩ => by
    obtain rfl | hij := eq_or_ne i j
    · simp
    · simp [hij, le_def, hij.symm]
  finset_mem_Iio := fun ⟨i, a⟩ ⟨j, b⟩ => by
    obtain rfl | hij := eq_or_ne i j
    · simp
    · simp [hij, lt_def, hij.symm]

中文:
实例 instLocallyFiniteOrderBot
  签名: : LocallyFiniteOrderBot (Σ i, α i) where
  定义体: fun ⟨i, a⟩ ⟨j, b⟩ => by
    obtain rfl | hij := eq_or_ne i j
    · simp
    · simp [hij, le_def, hij.symm]
  finset_mem_Iio := fun ⟨i, a⟩ ⟨j, b⟩ => by
    obtain rfl | hij := eq_or_ne i j
    · simp
    · simp [hij, lt_def, hij.symm]

Depends on / 依赖: eq_or_ne, finset_mem_Iio, hij.symm, le_def, lt_def
-/
instance instLocallyFiniteOrderBot : LocallyFiniteOrderBot (Σ i, α i) where
  finsetIic | ⟨i, a⟩ => (Iic a).map (Embedding.sigmaMk i)
  finsetIio | ⟨i, a⟩ => (Iio a).map (Embedding.sigmaMk i)
  finset_mem_Iic := fun ⟨i, a⟩ ⟨j, b⟩ => by
    obtain rfl | hij := eq_or_ne i j
    · simp
    · simp [hij, le_def, hij.symm]
  finset_mem_Iio := fun ⟨i, a⟩ ⟨j, b⟩ => by
    obtain rfl | hij := eq_or_ne i j
    · simp
    · simp [hij, lt_def, hij.symm]

variable (i : ι) (a : α i)

/--
theorem `Iic_mk` / 定理 `Iic_mk`

English:
theorem Iic_mk
  statement: Iic (⟨i, a⟩ : Sigma α) = (Iic a).map (Embedding.sigmaMk i)
  proof: rfl

中文:
定理 Iic_mk
  结论: 左无界右闭区间 (⟨i, a⟩ : 依赖和类型 α) = (左无界右闭区间 a).map (嵌入.sigmaMk i)
  证明: rfl
-/
@[simp] theorem Iic_mk : Iic (⟨i, a⟩ : Sigma α) = (Iic a).map (Embedding.sigmaMk i) := rfl
/--
theorem `Iio_mk` / 定理 `Iio_mk`

English:
theorem Iio_mk
  statement: Iio (⟨i, a⟩ : Sigma α) = (Iio a).map (Embedding.sigmaMk i)
  proof: rfl

中文:
定理 Iio_mk
  结论: 左无界右开区间 (⟨i, a⟩ : 依赖和类型 α) = (左无界右开区间 a).map (嵌入.sigmaMk i)
  证明: rfl
-/
@[simp] theorem Iio_mk : Iio (⟨i, a⟩ : Sigma α) = (Iio a).map (Embedding.sigmaMk i) := rfl

end LocallyFiniteOrderBot

section LocallyFiniteOrderTop
variable [forall i, Preorder (α i)] [forall i, LocallyFiniteOrderTop (α i)]

/--
Instance `instLocallyFiniteOrderTop` / 实例 `instLocallyFiniteOrderTop`

English:
instance instLocallyFiniteOrderTop
  signature: : LocallyFiniteOrderTop (Σ i, α i) where
  body: fun ⟨i, a⟩ ⟨j, b⟩ => by
    obtain rfl | hij := eq_or_ne i j
    · simp
    · simp [hij, le_def]
  finset_mem_Ioi := fun ⟨i, a⟩ ⟨j, b⟩ => by
    obtain rfl | hij := eq_or_ne i j
    · simp
    · simp [hij, lt_def]

中文:
实例 instLocallyFiniteOrderTop
  签名: : LocallyFiniteOrderTop (Σ i, α i) where
  定义体: fun ⟨i, a⟩ ⟨j, b⟩ => by
    obtain rfl | hij := eq_or_ne i j
    · simp
    · simp [hij, le_def]
  finset_mem_Ioi := fun ⟨i, a⟩ ⟨j, b⟩ => by
    obtain rfl | hij := eq_or_ne i j
    · simp
    · simp [hij, lt_def]

Depends on / 依赖: eq_or_ne, finset_mem_Ioi, le_def, lt_def
-/
instance instLocallyFiniteOrderTop : LocallyFiniteOrderTop (Σ i, α i) where
  finsetIci | ⟨i, a⟩ => (Ici a).map (Embedding.sigmaMk i)
  finsetIoi | ⟨i, a⟩ => (Ioi a).map (Embedding.sigmaMk i)
  finset_mem_Ici := fun ⟨i, a⟩ ⟨j, b⟩ => by
    obtain rfl | hij := eq_or_ne i j
    · simp
    · simp [hij, le_def]
  finset_mem_Ioi := fun ⟨i, a⟩ ⟨j, b⟩ => by
    obtain rfl | hij := eq_or_ne i j
    · simp
    · simp [hij, lt_def]

variable (i : ι) (a : α i)

/--
theorem `Ici_mk` / 定理 `Ici_mk`

English:
theorem Ici_mk
  statement: Ici (⟨i, a⟩ : Sigma α) = (Ici a).map (Embedding.sigmaMk i)
  proof: rfl

中文:
定理 Ici_mk
  结论: 左闭右无界区间 (⟨i, a⟩ : 依赖和类型 α) = (左闭右无界区间 a).map (嵌入.sigmaMk i)
  证明: rfl
-/
@[simp] theorem Ici_mk : Ici (⟨i, a⟩ : Sigma α) = (Ici a).map (Embedding.sigmaMk i) := rfl
/--
theorem `Ioi_mk` / 定理 `Ioi_mk`

English:
theorem Ioi_mk
  statement: Ioi (⟨i, a⟩ : Sigma α) = (Ioi a).map (Embedding.sigmaMk i)
  proof: rfl

中文:
定理 Ioi_mk
  结论: 左开右无界区间 (⟨i, a⟩ : 依赖和类型 α) = (左开右无界区间 a).map (嵌入.sigmaMk i)
  证明: rfl
-/
@[simp] theorem Ioi_mk : Ioi (⟨i, a⟩ : Sigma α) = (Ioi a).map (Embedding.sigmaMk i) := rfl

end LocallyFiniteOrderTop

end Disjoint

end Sigma
