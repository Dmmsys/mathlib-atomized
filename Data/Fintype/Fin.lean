/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Data.Vector.Basic

/-!
# The structure of `Fintype (Fin n)`

This file contains some basic results about the `Fintype` instance for `Fin`,
especially properties of `Finset.univ : Finset (Fin n)`.
-/

public section

open List (Vector)

open Finset

open Fintype

namespace Fin

variable {α β : Type*} {n : Nat}

/--
theorem `map_valEmbedding_univ` / 定理 `map_valEmbedding_univ`

English:
theorem map_valEmbedding_univ
  proof: by
  ext
  simp [orderIsoSubtype.symm.surjective.exists, OrderIso.symm]

@[simp]

中文:
定理 map_valEmbedding_univ
  证明: by
  ext
  simp [orderIsoSubtype.symm.surjective.exists, OrderIso.symm]

@[simp]
-/
@[simp] theorem map_valEmbedding_univ :
    (Finset.univ : Finset (Fin n)).map Fin.valEmbedding = Iio n := by
  ext
  simp [orderIsoSubtype.symm.surjective.exists, OrderIso.symm]

@[simp]
/--
theorem `Ioi_zero_eq_map` / 定理 `Ioi_zero_eq_map`

English:
theorem Ioi_zero_eq_map
  statement: Ioi (0 : Fin n.succ) = univ.map (Fin.succEmb _)
  proof: coe_injective by ext; simp [pos_iff_ne_zero]

@[simp]

中文:
定理 Ioi_zero_eq_map
  结论: 左开右无界区间 (0 : 有限集 n.succ) = univ.map (有限集.succEmb _)
  证明: coe_injective by ext; simp [pos_iff_ne_zero]

@[simp]

Depends on / 依赖: Monotone, Monotone.map_bddAbove, Rat.cast_mono, cast_mono, coe_injective, map_bddAbove, pos_iff_ne_zero, ratLt_bddAbove
-/
theorem Ioi_zero_eq_map : Ioi (0 : Fin n.succ) = univ.map (Fin.succEmb _) :=
coe_injective by ext; simp [pos_iff_ne_zero]

@[simp]
/--
theorem `Iio_last_eq_map` / 定理 `Iio_last_eq_map`

English:
theorem Iio_last_eq_map
  statement: Iio (Fin.last n) = Finset.univ.map Fin.castSuccEmb
  proof: coe_injective by ext; simp [lt_def]

中文:
定理 Iio_last_eq_map
  结论: 左无界右开区间 (有限集.last n) = 有限集.univ.map 有限集.castSuccEmb
  证明: coe_injective by ext; simp [lt_def]

Depends on / 依赖: Set.image_nonempty.mpr, coe_injective, image_nonempty, lt_def, ratLt_nonempty
-/
theorem Iio_last_eq_map : Iio (Fin.last n) = Finset.univ.map Fin.castSuccEmb :=
coe_injective by ext; simp [lt_def]

/--
theorem `Ioi_succ` / 定理 `Ioi_succ`

English:
theorem Ioi_succ
  given: (i : Fin n)
  statement: Ioi i.succ = (Ioi i).map (Fin.succEmb _)
  proof: by simp

中文:
定理 Ioi_succ
  条件: (i : 有限集 n)
  结论: 左开右无界区间 i.succ = (左开右无界区间 i).map (有限集.succEmb _)
  证明: by simp

Depends on / 依赖: Set.image_add, image_add, ratLt_add
-/
theorem Ioi_succ (i : Fin n) : Ioi i.succ = (Ioi i).map (Fin.succEmb _) := by simp

/--
theorem `Iio_castSucc` / 定理 `Iio_castSucc`

English:
theorem Iio_castSucc
  given: (i : Fin n)
  statement: Iio (castSucc i) = (Iio i).map Fin.castSuccEmb
  proof: by simp

中文:
定理 Iio_castSucc
  条件: (i : 有限集 n)
  结论: 左无界右开区间 (castSucc i) = (左无界右开区间 i).map 有限集.castSuccEmb
  证明: by simp
-/
theorem Iio_castSucc (i : Fin n) : Iio (castSucc i) = (Iio i).map Fin.castSuccEmb := by simp

/--
theorem `card_filter_val_lt` / 定理 `card_filter_val_lt`

English:
theorem card_filter_val_lt
  given: {m : Nat}
  statement: #{i : Fin n | i < m} = min n m
  proof: by
  simp [← card_map valEmbedding, ← filter_filter, exists_iff, map_filter']

中文:
定理 card_filter_val_lt
  条件: {m : 自然数}
  结论: #{i : 有限集 n | i < m} = 最小值 n m
  证明: by
  simp [← card_map valEmbedding, ← filter_filter, exists_iff, map_filter']

Depends on / 依赖: card_map, exists_iff, filter_filter, map_filter, valEmbedding
-/
theorem card_filter_val_lt {m : Nat} : #{i : Fin n | i < m} = min n m := by
  simp [← card_map valEmbedding, ← filter_filter, exists_iff, map_filter']

/--
theorem `card_filter_univ_succ` / 定理 `card_filter_univ_succ`

English:
theorem card_filter_univ_succ
  given: (p : Fin (n + 1) -> Prop) [DecidablePred p]
  proof: by
  rw [Fin.univ_succ]; rw [filter_cons]; rw [apply_ite Finset.card]; rw [card_cons]; rw [filter_map]; rw [card_map]; rfl

中文:
定理 card_filter_univ_succ
  条件: (p : 有限集 (n + 1) -> 命题) [DecidablePred p]
  证明: by
  rw [Fin.univ_succ]; rw [filter_cons]; rw [apply_ite Finset.card]; rw [card_cons]; rw [filter_map]; rw [card_map]; rfl

Depends on / 依赖: Fin.univ_succ, Finset, Finset.card, apply_ite, card_cons, card_map, filter_cons, filter_map, univ_succ
-/
theorem card_filter_univ_succ (p : Fin (n + 1) -> Prop) [DecidablePred p] :
    #{x | p x} = if p 0 then #{x | p (.succ x)} + 1 else #{x | p (.succ x)} := by
  rw [Fin.univ_succ]; rw [filter_cons]; rw [apply_ite Finset.card]; rw [card_cons]; rw [filter_map]; rw [card_map]; rfl

/--
theorem `card_filter_univ_succ'` / 定理 `card_filter_univ_succ'`

English:
theorem card_filter_univ_succ'
  given: (p : Fin (n + 1) -> Prop) [DecidablePred p]
  proof: by
  rw [card_filter_univ_succ]; split_ifs <;> simp [add_comm]

中文:
定理 card_filter_univ_succ'
  条件: (p : 有限集 (n + 1) -> 命题) [DecidablePred p]
  证明: by
  rw [card_filter_univ_succ]; split_ifs <;> simp [add_comm]

Depends on / 依赖: add_comm, card_filter_univ_succ, split_ifs
-/
theorem card_filter_univ_succ' (p : Fin (n + 1) -> Prop) [DecidablePred p] :
    #{x | p x} = ite (p 0) 1 0 + #{x | p (.succ x)} := by
  rw [card_filter_univ_succ]; split_ifs <;> simp [add_comm]

/--
theorem `card_filter_univ_eq_vector_get_eq_count` / 定理 `card_filter_univ_eq_vector_get_eq_count`

English:
theorem card_filter_univ_eq_vector_get_eq_count
  given: [DecidableEq α] (a : α) (v : List.Vector α n)
  proof: by
  induction v with
  | nil => simp
  | @cons n x xs hxs =>
    simp_rw [card_filter_univ_succ', Vector.get_cons_zero, Vector.toList_cons, Vector.get_cons_succ,
      hxs, List.count_cons, add_comm (ite (x = a) 1 0), beq_iff_eq]

中文:
定理 card_filter_univ_eq_vector_get_eq_count
  条件: [DecidableEq α] (a : α) (v : 列表.Vector α n)
  证明: by
  induction v with
  | nil => simp
  | @cons n x xs hxs =>
    simp_rw [card_filter_univ_succ', Vector.get_cons_zero, Vector.toList_cons, Vector.get_cons_succ,
      hxs, List.count_cons, add_comm (ite (x = a) 1 0), beq_iff_eq]

Depends on / 依赖: List.count_cons, Vector, Vector.get_cons_succ, Vector.get_cons_zero, Vector.toList_cons, add_comm, beq_iff_eq, card_filter_univ_succ, count_cons, get_cons_succ, get_cons_zero, simp_rw, toList_cons
-/
theorem card_filter_univ_eq_vector_get_eq_count [DecidableEq α] (a : α) (v : List.Vector α n) :
    #{i | v.get i = a} = v.toList.count a := by
  induction v with
  | nil => simp
  | @cons n x xs hxs =>
    simp_rw [card_filter_univ_succ', Vector.get_cons_zero, Vector.toList_cons, Vector.get_cons_succ,
      hxs, List.count_cons, add_comm (ite (x = a) 1 0), beq_iff_eq]

/--
theorem `lt_card_filter_univ_iff_apply_of_imp` / 定理 `lt_card_filter_univ_iff_apply_of_imp`

English:
theorem lt_card_filter_univ_iff_apply_of_imp
  statement: {j : Fin n} (p : Fin n -> Prop) [DecidablePred p]
  proof: by
  have h1 (k : Fin n) (hk : ¬ p k) : #{i | p i} <= k := by
    rw [← Fin.card_Iio]
    exact card_le_card (by grind)
  refine ⟨by grind, fun h => ?_⟩
  by_contra! hc
  let q : Fin n -> Prop := (· < #{i | p i})
  have : univ.filter q = univ.filter p :=
    eq_of_subset_of_card_le (by grind) (by rw [card_filter_val_lt]; grind)
  have : j in univ.filter p := by grind
  grind

中文:
定理 lt_card_filter_univ_iff_apply_of_imp
  结论: {j : 有限集 n} (p : 有限集 n -> 命题) [DecidablePred p]
  证明: by
  have h1 (k : Fin n) (hk : ¬ p k) : #{i | p i} <= k := by
    rw [← Fin.card_Iio]
    exact card_le_card (by grind)
  refine ⟨by grind, fun h => ?_⟩
  by_contra! hc
  let q : Fin n -> Prop := (· < #{i | p i})
  have : univ.filter q = univ.filter p :=
    eq_of_subset_of_card_le (by grind) (by rw [card_filter_val_lt]; grind)
  have : j in univ.filter p := by grind
  grind

Depends on / 依赖: Fin.card_Iio, card_Iio, card_filter_val_lt, card_le_card, eq_of_subset_of_card_le, filter, univ.filter
-/
theorem lt_card_filter_univ_iff_apply_of_imp {j : Fin n} (p : Fin n -> Prop) [DecidablePred p]
    (hp : forall i j, j <= i -> p i -> p j) :
    j < #{i | p i} ↔ p j := by
  have h1 (k : Fin n) (hk : ¬ p k) : #{i | p i} <= k := by
    rw [← Fin.card_Iio]
    exact card_le_card (by grind)
  refine ⟨by grind, fun h => ?_⟩
  by_contra! hc
  let q : Fin n -> Prop := (· < #{i | p i})
  have : univ.filter q = univ.filter p :=
    eq_of_subset_of_card_le (by grind) (by rw [card_filter_val_lt]; grind)
  have : j in univ.filter p := by grind
  grind

/--
lemma `_root_.Finset.image_fin_univ` / 引理 `_root_.Finset.image_fin_univ`

English:
lemma _root_.Finset.image_fin_univ
  given: {n : Nat}
  proof: by
  ext
  simp [Fin.exists_iff]

@[simp]

中文:
引理 _root_.有限集.image_fin_univ
  条件: {n : 自然数}
  证明: by
  ext
  simp [Fin.exists_iff]

@[simp]

Depends on / 依赖: Fin.exists_iff, Fin.val, Finset, Finset.range, exists_iff
-/
lemma _root_.Finset.image_fin_univ {n : Nat} :
    (Finset.univ (α := Fin n)).image Fin.val = Finset.range n := by
  ext
  simp [Fin.exists_iff]

@[simp]
/--
lemma `_root_.Finset.sup_fin_univ` / 引理 `_root_.Finset.sup_fin_univ`

English:
lemma _root_.Finset.sup_fin_univ
  given: [SemilatticeSup α] [OrderBot α] {n : Nat} (f : Nat -> α)
  proof: by
  rw [← image_fin_univ]; rw [sup_image]; rw [Function.comp_def]

中文:
引理 _root_.有限集.sup_fin_univ
  条件: [SemilatticeSup α] [有底序 α] {n : 自然数} (f : 自然数 -> α)
  证明: by
  rw [← image_fin_univ]; rw [sup_image]; rw [Function.comp_def]

Depends on / 依赖: Finset, Finset.range, Function, Function.comp_def, comp_def, image_fin_univ, sup_image
-/
lemma _root_.Finset.sup_fin_univ [SemilatticeSup α] [OrderBot α] {n : Nat} (f : Nat -> α) :
    (Finset.univ (α := Fin n)).sup (fun n => f n) = (Finset.range n).sup f := by
  rw [← image_fin_univ]; rw [sup_image]; rw [Function.comp_def]

end Fin
