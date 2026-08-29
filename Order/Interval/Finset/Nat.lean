/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Embedding
public import Mathlib.Order.Interval.Multiset

/-!
# Finite intervals of naturals

This file proves that `ℕ` is a `LocallyFiniteOrder` and calculates the cardinality of its
intervals as finsets and fintypes.

## TODO

Some lemmas can be generalized using `IsOrderedAddMonoid`, `CanonicallyOrderedAdd` or `SuccOrder`
and subsequently be moved upstream to `Order.Interval.Finset`.
-/

public section

assert_not_exists Ring

open Finset Nat

variable (a b c : Nat)

namespace Nat

set_option backward.isDefEq.respectTransparency false in
/--
Instance `instLocallyFiniteOrder` / 实例 `instLocallyFiniteOrder`

English:
instance instLocallyFiniteOrder
  signature: : LocallyFiniteOrder Nat where
  body: ⟨List.range' a (b + 1 - a), List.nodup_range'⟩
  finsetIco a b := ⟨List.range' a (b - a), List.nodup_range'⟩
  finsetIoc a b := ⟨List.range' (a + 1) (b - a), List.nodup_range'⟩
  finsetIoo a b := ⟨List.range' (a + 1) (b - a - 1), List.nodup_range'⟩
  finset_mem_Icc a b x := by rw [Finset.mem_mk, Multiset.mem_coe, List.mem_range'_1]; lia
  finset_mem_Ico a b x := by rw [Finset.mem_mk, Multiset.mem_coe, List.mem_range'_1]; lia
  finset_mem_Ioc a b x := by rw [Finset.mem_mk, Multiset.mem_coe, List.mem_range'_1]; lia
  finset_mem_Ioo a b x := by rw [Finset.mem_mk, Multiset.mem_coe, List.mem_range'_1]; lia

中文:
实例 instLocallyFiniteOrder
  签名: : 局部有限序 自然数 where
  定义体: ⟨List.range' a (b + 1 - a), List.nodup_range'⟩
  finsetIco a b := ⟨List.range' a (b - a), List.nodup_range'⟩
  finsetIoc a b := ⟨List.range' (a + 1) (b - a), List.nodup_range'⟩
  finsetIoo a b := ⟨List.range' (a + 1) (b - a - 1), List.nodup_range'⟩
  finset_mem_Icc a b x := by rw [Finset.mem_mk, Multiset.mem_coe, List.mem_range'_1]; lia
  finset_mem_Ico a b x := by rw [Finset.mem_mk, Multiset.mem_coe, List.mem_range'_1]; lia
  finset_mem_Ioc a b x := by rw [Finset.mem_mk, Multiset.mem_coe, List.mem_range'_1]; lia
  finset_mem_Ioo a b x := by rw [Finset.mem_mk, Multiset.mem_coe, List.mem_range'_1]; lia

Depends on / 依赖: List.nodup_range, List.range, nodup_range
-/
instance instLocallyFiniteOrder : LocallyFiniteOrder Nat where
  finsetIcc a b := ⟨List.range' a (b + 1 - a), List.nodup_range'⟩
  finsetIco a b := ⟨List.range' a (b - a), List.nodup_range'⟩
  finsetIoc a b := ⟨List.range' (a + 1) (b - a), List.nodup_range'⟩
  finsetIoo a b := ⟨List.range' (a + 1) (b - a - 1), List.nodup_range'⟩
  finset_mem_Icc a b x := by rw [Finset.mem_mk, Multiset.mem_coe, List.mem_range'_1]; lia
  finset_mem_Ico a b x := by rw [Finset.mem_mk, Multiset.mem_coe, List.mem_range'_1]; lia
  finset_mem_Ioc a b x := by rw [Finset.mem_mk, Multiset.mem_coe, List.mem_range'_1]; lia
  finset_mem_Ioo a b x := by rw [Finset.mem_mk, Multiset.mem_coe, List.mem_range'_1]; lia

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Unique (Iic 0)
  body: by
  rw [← Nat.bot_eq_zero]
  infer_instance

中文:
实例 :
  签名: 唯一 (左无界右闭区间 0)
  定义体: by
  rw [← Nat.bot_eq_zero]
  infer_instance

Depends on / 依赖: Nat.bot_eq_zero, bot_eq_zero, infer_instance
-/
instance : Unique (Iic 0) := by
  rw [← Nat.bot_eq_zero]
  infer_instance

/--
theorem `Icc_eq_range'` / 定理 `Icc_eq_range'`

English:
theorem Icc_eq_range'
  statement: Icc a b = ⟨List.range' a (b + 1 - a), List.nodup_range'⟩
  proof: rfl

中文:
定理 Icc_eq_range'
  结论: 闭区间 a b = ⟨列表.range' a (b + 1 - a), 列表.nodup_range'⟩
  证明: rfl
-/
theorem Icc_eq_range' : Icc a b = ⟨List.range' a (b + 1 - a), List.nodup_range'⟩ :=
  rfl

/--
theorem `Ico_eq_range'` / 定理 `Ico_eq_range'`

English:
theorem Ico_eq_range'
  statement: Ico a b = ⟨List.range' a (b - a), List.nodup_range'⟩
  proof: rfl

中文:
定理 Ico_eq_range'
  结论: 左闭右开区间 a b = ⟨列表.range' a (b - a), 列表.nodup_range'⟩
  证明: rfl
-/
theorem Ico_eq_range' : Ico a b = ⟨List.range' a (b - a), List.nodup_range'⟩ :=
  rfl

/--
theorem `Ioc_eq_range'` / 定理 `Ioc_eq_range'`

English:
theorem Ioc_eq_range'
  statement: Ioc a b = ⟨List.range' (a + 1) (b - a), List.nodup_range'⟩
  proof: rfl

中文:
定理 Ioc_eq_range'
  结论: 左开右闭区间 a b = ⟨列表.range' (a + 1) (b - a), 列表.nodup_range'⟩
  证明: rfl
-/
theorem Ioc_eq_range' : Ioc a b = ⟨List.range' (a + 1) (b - a), List.nodup_range'⟩ :=
  rfl

/--
theorem `Ioo_eq_range'` / 定理 `Ioo_eq_range'`

English:
theorem Ioo_eq_range'
  statement: Ioo a b = ⟨List.range' (a + 1) (b - a - 1), List.nodup_range'⟩
  proof: rfl

中文:
定理 Ioo_eq_range'
  结论: 开区间 a b = ⟨列表.range' (a + 1) (b - a - 1), 列表.nodup_range'⟩
  证明: rfl
-/
theorem Ioo_eq_range' : Ioo a b = ⟨List.range' (a + 1) (b - a - 1), List.nodup_range'⟩ :=
  rfl

/--
theorem `uIcc_eq_range'` / 定理 `uIcc_eq_range'`

English:
theorem uIcc_eq_range'
  proof: rfl

中文:
定理 uIcc_eq_range'
  证明: rfl
-/
theorem uIcc_eq_range' :
    uIcc a b = ⟨List.range' (min a b) (max a b + 1 - min a b), List.nodup_range'⟩ := rfl

/--
theorem `Iio_eq_range` / 定理 `Iio_eq_range`

English:
theorem Iio_eq_range
  statement: Iio a = range a
  proof: by
  grind

@[simp]

中文:
定理 Iio_eq_range
  结论: 左无界右开区间 a = range a
  证明: by
  grind

@[simp]
-/
theorem Iio_eq_range : Iio a = range a := by
  grind

@[simp]
/--
theorem `Ico_zero_eq_range` / 定理 `Ico_zero_eq_range`

English:
theorem Ico_zero_eq_range
  statement: Ico 0 a = range a
  proof: by
  rw [← Nat.bot_eq_zero]; rw [← Iio_eq_Ico]; rw [Iio_eq_range]

中文:
定理 Ico_zero_eq_range
  结论: 左闭右开区间 0 a = range a
  证明: by
  rw [← Nat.bot_eq_zero]; rw [← Iio_eq_Ico]; rw [Iio_eq_range]

Depends on / 依赖: Iio_eq_Ico, Iio_eq_range, Nat.bot_eq_zero, bot_eq_zero
-/
theorem Ico_zero_eq_range : Ico 0 a = range a := by
  rw [← Nat.bot_eq_zero]; rw [← Iio_eq_Ico]; rw [Iio_eq_range]

/--
lemma `range_eq_Icc_zero_sub_one` / 引理 `range_eq_Icc_zero_sub_one`

English:
lemma range_eq_Icc_zero_sub_one
  given: (n : Nat) (hn : n != 0)
  statement: range n = Icc 0 (n - 1)
  proof: by
  grind

中文:
引理 range_eq_Icc_zero_sub_one
  条件: (n : 自然数) (hn : n != 0)
  结论: range n = 闭区间 0 (n - 1)
  证明: by
  grind
-/
lemma range_eq_Icc_zero_sub_one (n : Nat) (hn : n != 0) : range n = Icc 0 (n - 1) := by
  grind

/--
theorem `_root_.Finset.range_eq_Ico` / 定理 `_root_.Finset.range_eq_Ico`

English:
theorem _root_.Finset.range_eq_Ico
  statement: range a = Ico 0 a
  proof: (Ico_zero_eq_range a).symm

中文:
定理 _root_.有限集.range_eq_Ico
  结论: range a = 左闭右开区间 0 a
  证明: (Ico_zero_eq_range a).symm

Depends on / 依赖: Ico_zero_eq_range
-/
theorem _root_.Finset.range_eq_Ico : range a = Ico 0 a :=
  (Ico_zero_eq_range a).symm

/--
theorem `range_succ_eq_Icc_zero` / 定理 `range_succ_eq_Icc_zero`

English:
theorem range_succ_eq_Icc_zero
  given: (n : Nat)
  statement: range (n + 1) = Icc 0 n
  proof: by
  rw [range_eq_Icc_zero_sub_one _ (Nat.add_one_ne_zero _)]; rw [Nat.add_sub_cancel_right]

中文:
定理 range_succ_eq_Icc_zero
  条件: (n : 自然数)
  结论: range (n + 1) = 闭区间 0 n
  证明: by
  rw [range_eq_Icc_zero_sub_one _ (Nat.add_one_ne_zero _)]; rw [Nat.add_sub_cancel_right]

Depends on / 依赖: Nat.add_one_ne_zero, Nat.add_sub_cancel_right, add_one_ne_zero, add_sub_cancel_right, range_eq_Icc_zero_sub_one
-/
theorem range_succ_eq_Icc_zero (n : Nat) : range (n + 1) = Icc 0 n := by
  rw [range_eq_Icc_zero_sub_one _ (Nat.add_one_ne_zero _)]; rw [Nat.add_sub_cancel_right]

/--
theorem `range_succ_eq_Iic` / 定理 `range_succ_eq_Iic`

English:
theorem range_succ_eq_Iic
  given: (n : Nat)
  statement: range (n + 1) = Iic n
  proof: by
  rw [range_succ_eq_Icc_zero]
  rfl

中文:
定理 range_succ_eq_Iic
  条件: (n : 自然数)
  结论: range (n + 1) = 左无界右闭区间 n
  证明: by
  rw [range_succ_eq_Icc_zero]
  rfl

Depends on / 依赖: range_succ_eq_Icc_zero
-/
theorem range_succ_eq_Iic (n : Nat) : range (n + 1) = Iic n := by
  rw [range_succ_eq_Icc_zero]
  rfl

/--
lemma `card_Icc` / 引理 `card_Icc`

English:
lemma card_Icc
  statement: #(Icc a b) = b + 1 - a
  proof: List.length_range' ..

中文:
引理 card_Icc
  结论: #(闭区间 a b) = b + 1 - a
  证明: List.length_range' ..
-/
@[simp] lemma card_Icc : #(Icc a b) = b + 1 - a := List.length_range' ..
/--
lemma `card_Ico` / 引理 `card_Ico`

English:
lemma card_Ico
  statement: #(Ico a b) = b - a
  proof: List.length_range' ..

中文:
引理 card_Ico
  结论: #(左闭右开区间 a b) = b - a
  证明: List.length_range' ..
-/
@[simp] lemma card_Ico : #(Ico a b) = b - a := List.length_range' ..
/--
lemma `card_Ioc` / 引理 `card_Ioc`

English:
lemma card_Ioc
  statement: #(Ioc a b) = b - a
  proof: List.length_range' ..

中文:
引理 card_Ioc
  结论: #(左开右闭区间 a b) = b - a
  证明: List.length_range' ..
-/
@[simp] lemma card_Ioc : #(Ioc a b) = b - a := List.length_range' ..
/--
lemma `card_Ioo` / 引理 `card_Ioo`

English:
lemma card_Ioo
  statement: #(Ioo a b) = b - a - 1
  proof: List.length_range' ..

@[simp]

中文:
引理 card_Ioo
  结论: #(开区间 a b) = b - a - 1
  证明: List.length_range' ..

@[simp]
-/
@[simp] lemma card_Ioo : #(Ioo a b) = b - a - 1 := List.length_range' ..

@[simp]
/--
theorem `card_uIcc` / 定理 `card_uIcc`

English:
theorem card_uIcc
  statement: #(uIcc a b) = (b - a : Int).natAbs + 1
  proof: (card_Icc _ _).trans by rw [← Int.natCast_inj, Int.ofNat_sub] <;> omega

@[simp]

中文:
定理 card_uIcc
  结论: #(uIcc a b) = (b - a : 整数).natAbs + 1
  证明: (card_Icc _ _).trans by rw [← Int.natCast_inj, Int.ofNat_sub] <;> omega

@[simp]

Depends on / 依赖: Int.natCast_inj, Int.ofNat_sub, card_Icc, natCast_inj, ofNat_sub
-/
theorem card_uIcc : #(uIcc a b) = (b - a : Int).natAbs + 1 :=
(card_Icc _ _).trans by rw [← Int.natCast_inj, Int.ofNat_sub] <;> omega

@[simp]
/--
lemma `card_Iic` / 引理 `card_Iic`

English:
lemma card_Iic
  statement: #(Iic b) = b + 1
  proof: by rw [Iic_eq_Icc, card_Icc, Nat.bot_eq_zero, Nat.sub_zero]

@[simp]

中文:
引理 card_Iic
  结论: #(左无界右闭区间 b) = b + 1
  证明: by rw [Iic_eq_Icc, card_Icc, Nat.bot_eq_zero, Nat.sub_zero]

@[simp]

Depends on / 依赖: Iic_eq_Icc, Nat.bot_eq_zero, Nat.sub_zero, bot_eq_zero, card_Icc, sub_zero
-/
lemma card_Iic : #(Iic b) = b + 1 := by rw [Iic_eq_Icc, card_Icc, Nat.bot_eq_zero, Nat.sub_zero]

@[simp]
/--
theorem `card_Iio` / 定理 `card_Iio`

English:
theorem card_Iio
  statement: #(Iio b) = b
  proof: by rw [Iio_eq_Ico, card_Ico, Nat.bot_eq_zero, Nat.sub_zero]

中文:
定理 card_Iio
  结论: #(左无界右开区间 b) = b
  证明: by rw [Iio_eq_Ico, card_Ico, Nat.bot_eq_zero, Nat.sub_zero]

Depends on / 依赖: Iio_eq_Ico, Nat.bot_eq_zero, Nat.sub_zero, bot_eq_zero, card_Ico, sub_zero
-/
theorem card_Iio : #(Iio b) = b := by rw [Iio_eq_Ico, card_Ico, Nat.bot_eq_zero, Nat.sub_zero]

-- TODO: Generalise the following series of lemmas.

@[simp]
/--
theorem `Ico_succ_singleton` / 定理 `Ico_succ_singleton`

English:
theorem Ico_succ_singleton
  statement: Ico a (a + 1) = {a}
  proof: by grind

@[simp]

中文:
定理 Ico_succ_singleton
  结论: 左闭右开区间 a (a + 1) = {a}
  证明: by grind

@[simp]
-/
theorem Ico_succ_singleton : Ico a (a + 1) = {a} := by grind

@[simp]
/--
theorem `Ico_pred_singleton` / 定理 `Ico_pred_singleton`

English:
theorem Ico_pred_singleton
  given: {a : Nat} (h : 0 < a)
  statement: Ico (a - 1) a = {a - 1}
  proof: by
  ext x
  rw [mem_Ico]; rw [mem_singleton]
  lia

@[simp]

中文:
定理 Ico_pred_singleton
  条件: {a : 自然数} (h : 0 < a)
  结论: 左闭右开区间 (a - 1) a = {a - 1}
  证明: by
  ext x
  rw [mem_Ico]; rw [mem_singleton]
  lia

@[simp]

Depends on / 依赖: mem_Ico, mem_singleton
-/
theorem Ico_pred_singleton {a : Nat} (h : 0 < a) : Ico (a - 1) a = {a - 1} := by
  ext x
  rw [mem_Ico]; rw [mem_singleton]
  lia

@[simp]
/--
theorem `Ioc_succ_singleton` / 定理 `Ioc_succ_singleton`

English:
theorem Ioc_succ_singleton
  statement: Ioc b (b + 1) = {b + 1}
  proof: by grind

中文:
定理 Ioc_succ_singleton
  结论: 左开右闭区间 b (b + 1) = {b + 1}
  证明: by grind
-/
theorem Ioc_succ_singleton : Ioc b (b + 1) = {b + 1} := by grind

variable {a b c}

/--
lemma `mem_Ioc_succ` / 引理 `mem_Ioc_succ`

English:
lemma mem_Ioc_succ
  statement: a in Ioc b (b + 1) ↔ a = b + 1
  proof: by simp

中文:
引理 mem_Ioc_succ
  结论: a in 左开右闭区间 b (b + 1) ↔ a = b + 1
  证明: by simp
-/
lemma mem_Ioc_succ : a in Ioc b (b + 1) ↔ a = b + 1 := by simp

/--
lemma `mem_Ioc_succ'` / 引理 `mem_Ioc_succ'`

English:
lemma mem_Ioc_succ'
  given: (a : Ioc b (b + 1))
  statement: a = ⟨b + 1, mem_Ioc.2 (by lia)⟩
  proof: Subtype.val_inj.1 (mem_Ioc_succ.1 a.2)

中文:
引理 mem_Ioc_succ'
  条件: (a : 左开右闭区间 b (b + 1))
  结论: a = ⟨b + 1, mem_Ioc.2 (by lia)⟩
  证明: Subtype.val_inj.1 (mem_Ioc_succ.1 a.2)

Depends on / 依赖: Subtype, Subtype.val_inj, mem_Ioc_succ, val_inj
-/
lemma mem_Ioc_succ' (a : Ioc b (b + 1)) : a = ⟨b + 1, mem_Ioc.2 (by lia)⟩ :=
  Subtype.val_inj.1 (mem_Ioc_succ.1 a.2)

/--
theorem `image_sub_const_Ico` / 定理 `image_sub_const_Ico`

English:
theorem image_sub_const_Ico
  given: (h : c <= a)
  proof: by
  ext x
  simp_rw [mem_image, mem_Ico]
  refine ⟨?_, fun h => ⟨x + c, by lia⟩⟩
  rintro ⟨x, hx, rfl⟩
  lia

中文:
定理 image_sub_const_Ico
  条件: (h : c <= a)
  证明: by
  ext x
  simp_rw [mem_image, mem_Ico]
  refine ⟨?_, fun h => ⟨x + c, by lia⟩⟩
  rintro ⟨x, hx, rfl⟩
  lia

Depends on / 依赖: mem_Ico, mem_image, simp_rw
-/
theorem image_sub_const_Ico (h : c <= a) :
    ((Ico a b).image fun x => x - c) = Ico (a - c) (b - c) := by
  ext x
  simp_rw [mem_image, mem_Ico]
  refine ⟨?_, fun h => ⟨x + c, by lia⟩⟩
  rintro ⟨x, hx, rfl⟩
  lia

/--
theorem `Ico_image_const_sub_eq_Ico` / 定理 `Ico_image_const_sub_eq_Ico`

English:
theorem Ico_image_const_sub_eq_Ico
  given: (hac : a <= c)
  proof: by
  ext x
  simp_rw [mem_image, mem_Ico]
  refine ⟨?_, fun h => ⟨c - x, by lia⟩⟩
  rintro ⟨x, hx, rfl⟩
  lia

中文:
定理 Ico_image_const_sub_eq_Ico
  条件: (hac : a <= c)
  证明: by
  ext x
  simp_rw [mem_image, mem_Ico]
  refine ⟨?_, fun h => ⟨c - x, by lia⟩⟩
  rintro ⟨x, hx, rfl⟩
  lia

Depends on / 依赖: mem_Ico, mem_image, simp_rw
-/
theorem Ico_image_const_sub_eq_Ico (hac : a <= c) :
    ((Ico a b).image fun x => c - x) = Ico (c + 1 - b) (c + 1 - a) := by
  ext x
  simp_rw [mem_image, mem_Ico]
  refine ⟨?_, fun h => ⟨c - x, by lia⟩⟩
  rintro ⟨x, hx, rfl⟩
  lia

/--
theorem `Ico_succ_left_eq_erase_Ico` / 定理 `Ico_succ_left_eq_erase_Ico`

English:
theorem Ico_succ_left_eq_erase_Ico
  statement: Ico a.succ b = erase (Ico a b) a
  proof: by
  ext x
  simp_rw [mem_erase, mem_Ico]
  lia

中文:
定理 Ico_succ_left_eq_erase_Ico
  结论: 左闭右开区间 a.succ b = erase (左闭右开区间 a b) a
  证明: by
  ext x
  simp_rw [mem_erase, mem_Ico]
  lia

Depends on / 依赖: mem_Ico, mem_erase, simp_rw
-/
theorem Ico_succ_left_eq_erase_Ico : Ico a.succ b = erase (Ico a b) a := by
  ext x
  simp_rw [mem_erase, mem_Ico]
  lia

/--
theorem `Ico_succ_right_eq_insert_Ico` / 定理 `Ico_succ_right_eq_insert_Ico`

English:
theorem Ico_succ_right_eq_insert_Ico
  given: (h : a <= b)
  statement: Ico a b.succ = insert b (Ico a b)
  proof: by
  ext x
  simp_rw [mem_insert, mem_Ico]
  lia

中文:
定理 Ico_succ_right_eq_insert_Ico
  条件: (h : a <= b)
  结论: 左闭右开区间 a b.succ = insert b (左闭右开区间 a b)
  证明: by
  ext x
  simp_rw [mem_insert, mem_Ico]
  lia

Depends on / 依赖: mem_Ico, mem_insert, simp_rw
-/
theorem Ico_succ_right_eq_insert_Ico (h : a <= b) : Ico a b.succ = insert b (Ico a b) := by
  ext x
  simp_rw [mem_insert, mem_Ico]
  lia

/--
theorem `mod_injOn_Ico` / 定理 `mod_injOn_Ico`

English:
theorem mod_injOn_Ico
  given: (n a : Nat)
  statement: Set.InjOn (· % a) (Finset.Ico n (n + a))
  proof: by
  induction n with
  | zero =>
    simp only [zero_add, Ico_zero_eq_range]
    rintro k hk l hl (hkl : k % a = l % a)
    simp only [Finset.mem_range, Finset.mem_coe] at hk hl
    rwa [mod_eq_of_lt hk, mod_eq_of_lt hl] at hkl
  | succ n ih =>
    rw [Ico_succ_left_eq_erase_Ico]; rw [succ_add]; rw [succ_eq_add_one]; rw [Ico_succ_right_eq_insert_Ico (by lia)]
    rintro k hk l hl (hkl : k % a = l % a)
have ha : 0 < a := Nat.pos_iff_ne_zero.2 by rintro rfl; simp at hk
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_erase] at hk hl
    rcases hk with ⟨hkn, rfl | hk⟩ <;> rcases hl with ⟨hln, rfl | hl⟩
    · rfl
    · rw [add_mod_right] at hkl
      refine (hln <| ih hl ?_ hkl.symm).elim
      simpa using Nat.lt_add_of_pos_right (n := n) ha
    · rw [add_mod_right] at hkl
      suffices k = n by contradiction
      refine ih hk ?_ hkl
      simpa using Nat.lt_add_of_pos_right (n := n) ha
    · refine ih ?_ ?_ hkl <;> simp only [Finset.mem_coe, hk, hl]

中文:
定理 mod_injOn_Ico
  条件: (n a : 自然数)
  结论: 集合.单射限制 (· % a) (有限集.左闭右开区间 n (n + a))
  证明: by
  induction n with
  | zero =>
    simp only [zero_add, Ico_zero_eq_range]
    rintro k hk l hl (hkl : k % a = l % a)
    simp only [Finset.mem_range, Finset.mem_coe] at hk hl
    rwa [mod_eq_of_lt hk, mod_eq_of_lt hl] at hkl
  | succ n ih =>
    rw [Ico_succ_left_eq_erase_Ico]; rw [succ_add]; rw [succ_eq_add_one]; rw [Ico_succ_right_eq_insert_Ico (by lia)]
    rintro k hk l hl (hkl : k % a = l % a)
have ha : 0 < a := Nat.pos_iff_ne_zero.2 by rintro rfl; simp at hk
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_erase] at hk hl
    rcases hk with ⟨hkn, rfl | hk⟩ <;> rcases hl with ⟨hln, rfl | hl⟩
    · rfl
    · rw [add_mod_right] at hkl
      refine (hln <| ih hl ?_ hkl.symm).elim
      simpa using Nat.lt_add_of_pos_right (n := n) ha
    · rw [add_mod_right] at hkl
      suffices k = n by contradiction
      refine ih hk ?_ hkl
      simpa using Nat.lt_add_of_pos_right (n := n) ha
    · refine ih ?_ ?_ hkl <;> simp only [Finset.mem_coe, hk, hl]

Depends on / 依赖: Finset, Finset.mem_, Finset.mem_coe, Finset.mem_insert, Finset.mem_range, Ico_succ_left_eq_erase_Ico, Ico_succ_right_eq_insert_Ico, Ico_zero_eq_range, Nat.pos_iff_ne_zero, mem_, mem_coe, mem_insert, mem_range, mod_eq_of_lt, pos_iff_ne_zero, succ_add, succ_eq_add_one, zero_add
-/
theorem mod_injOn_Ico (n a : Nat) : Set.InjOn (· % a) (Finset.Ico n (n + a)) := by
  induction n with
  | zero =>
    simp only [zero_add, Ico_zero_eq_range]
    rintro k hk l hl (hkl : k % a = l % a)
    simp only [Finset.mem_range, Finset.mem_coe] at hk hl
    rwa [mod_eq_of_lt hk, mod_eq_of_lt hl] at hkl
  | succ n ih =>
    rw [Ico_succ_left_eq_erase_Ico]; rw [succ_add]; rw [succ_eq_add_one]; rw [Ico_succ_right_eq_insert_Ico (by lia)]
    rintro k hk l hl (hkl : k % a = l % a)
have ha : 0 < a := Nat.pos_iff_ne_zero.2 by rintro rfl; simp at hk
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_erase] at hk hl
    rcases hk with ⟨hkn, rfl | hk⟩ <;> rcases hl with ⟨hln, rfl | hl⟩
    · rfl
    · rw [add_mod_right] at hkl
      refine (hln <| ih hl ?_ hkl.symm).elim
      simpa using Nat.lt_add_of_pos_right (n := n) ha
    · rw [add_mod_right] at hkl
      suffices k = n by contradiction
      refine ih hk ?_ hkl
      simpa using Nat.lt_add_of_pos_right (n := n) ha
    · refine ih ?_ ?_ hkl <;> simp only [Finset.mem_coe, hk, hl]

/--
theorem `image_Ico_mod` / 定理 `image_Ico_mod`

English:
theorem image_Ico_mod
  given: (n a : Nat)
  statement: (Ico n (n + a)).image (· % a) = range a
  proof: by
  obtain rfl | ha := eq_or_ne a 0
  · rw [range_zero, add_zero, Ico_self, image_empty]
  ext i
  simp only [mem_image, mem_range, mem_Ico]
  constructor
  · rintro ⟨i, _, rfl⟩
    exact mod_lt i ha.bot_lt
  intro hia
  have hn := Nat.mod_add_div n a
  obtain hi | hi := lt_or_ge i (n % a)
  · refine ⟨i + a * (n / a + 1), ⟨?_, ?_⟩, ?_⟩
    · rw [add_comm (n / a), Nat.mul_add, mul_one, ← add_assoc]
      refine hn.symm.le.trans (Nat.add_le_add_right ?_ _)
      simpa only [zero_add] using add_le_add (zero_le i) (Nat.mod_lt n ha.bot_lt).le
    · refine lt_of_lt_of_le (Nat.add_lt_add_right hi (a * (n / a + 1))) ?_
      rw [Nat.mul_add]; rw [mul_one]; rw [← add_assoc]; rw [hn]
    · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hia]
  · refine ⟨i + a * (n / a), ⟨?_, ?_⟩, ?_⟩
    · lia
    · lia
    · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hia]

中文:
定理 image_Ico_mod
  条件: (n a : 自然数)
  结论: (左闭右开区间 n (n + a)).像 (· % a) = range a
  证明: by
  obtain rfl | ha := eq_or_ne a 0
  · rw [range_zero, add_zero, Ico_self, image_empty]
  ext i
  simp only [mem_image, mem_range, mem_Ico]
  constructor
  · rintro ⟨i, _, rfl⟩
    exact mod_lt i ha.bot_lt
  intro hia
  have hn := Nat.mod_add_div n a
  obtain hi | hi := lt_or_ge i (n % a)
  · refine ⟨i + a * (n / a + 1), ⟨?_, ?_⟩, ?_⟩
    · rw [add_comm (n / a), Nat.mul_add, mul_one, ← add_assoc]
      refine hn.symm.le.trans (Nat.add_le_add_right ?_ _)
      simpa only [zero_add] using add_le_add (zero_le i) (Nat.mod_lt n ha.bot_lt).le
    · refine lt_of_lt_of_le (Nat.add_lt_add_right hi (a * (n / a + 1))) ?_
      rw [Nat.mul_add]; rw [mul_one]; rw [← add_assoc]; rw [hn]
    · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hia]
  · refine ⟨i + a * (n / a), ⟨?_, ?_⟩, ?_⟩
    · lia
    · lia
    · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hia]

Depends on / 依赖: Ico_self, Nat.add_le_add_right, Nat.mod_add_div, Nat.mod_lt, Nat.mul_add, add_assoc, add_comm, add_le_add, add_le_add_right, add_zero, bot_lt, eq_or_ne, ha.bot_lt, hn.symm.le.trans, image_empty, lt_or_ge, mem_Ico, mem_image, mem_range, mod_add_div
-/
theorem image_Ico_mod (n a : Nat) : (Ico n (n + a)).image (· % a) = range a := by
  obtain rfl | ha := eq_or_ne a 0
  · rw [range_zero, add_zero, Ico_self, image_empty]
  ext i
  simp only [mem_image, mem_range, mem_Ico]
  constructor
  · rintro ⟨i, _, rfl⟩
    exact mod_lt i ha.bot_lt
  intro hia
  have hn := Nat.mod_add_div n a
  obtain hi | hi := lt_or_ge i (n % a)
  · refine ⟨i + a * (n / a + 1), ⟨?_, ?_⟩, ?_⟩
    · rw [add_comm (n / a), Nat.mul_add, mul_one, ← add_assoc]
      refine hn.symm.le.trans (Nat.add_le_add_right ?_ _)
      simpa only [zero_add] using add_le_add (zero_le i) (Nat.mod_lt n ha.bot_lt).le
    · refine lt_of_lt_of_le (Nat.add_lt_add_right hi (a * (n / a + 1))) ?_
      rw [Nat.mul_add]; rw [mul_one]; rw [← add_assoc]; rw [hn]
    · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hia]
  · refine ⟨i + a * (n / a), ⟨?_, ?_⟩, ?_⟩
    · lia
    · lia
    · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hia]

section Multiset

open Multiset

/--
theorem `multiset_Ico_map_mod` / 定理 `multiset_Ico_map_mod`

English:
theorem multiset_Ico_map_mod
  given: (n a : Nat)
  proof: by
  convert! congr_arg Finset.val (image_Ico_mod n a)
  refine ((nodup_map_iff_inj_on (Finset.Ico _ _).nodup).2 <| ?_).dedup.symm
  exact mod_injOn_Ico _ _

中文:
定理 multiset_Ico_map_mod
  条件: (n a : 自然数)
  证明: by
  convert! congr_arg Finset.val (image_Ico_mod n a)
  refine ((nodup_map_iff_inj_on (Finset.Ico _ _).nodup).2 <| ?_).dedup.symm
  exact mod_injOn_Ico _ _

Depends on / 依赖: Finset, Finset.Ico, Finset.val, congr_arg, convert, dedup.symm, image_Ico_mod, mod_injOn_Ico, nodup_map_iff_inj_on
-/
theorem multiset_Ico_map_mod (n a : Nat) :
    (Multiset.Ico n (n + a)).map (· % a) = Multiset.range a := by
  convert! congr_arg Finset.val (image_Ico_mod n a)
  refine ((nodup_map_iff_inj_on (Finset.Ico _ _).nodup).2 <| ?_).dedup.symm
  exact mod_injOn_Ico _ _

end Multiset

end Nat

namespace List

/--
lemma `toFinset_range'_1` / 引理 `toFinset_range'_1`

English:
lemma toFinset_range'_1
  given: (a b : Nat)
  statement: (List.range' a b).toFinset = Ico a (a + b)
  proof: by
  ext x
  rw [List.mem_toFinset]; rw [List.mem_range'_1]; rw [Finset.mem_Ico]

中文:
引理 toFinset_range'_1
  条件: (a b : 自然数)
  结论: (列表.range' a b).toFinset = 左闭右开区间 a (a + b)
  证明: by
  ext x
  rw [List.mem_toFinset]; rw [List.mem_range'_1]; rw [Finset.mem_Ico]

Depends on / 依赖: Finset, Finset.mem_Ico, List.mem_range, List.mem_toFinset, mem_Ico, mem_range, mem_toFinset
-/
lemma toFinset_range'_1 (a b : Nat) : (List.range' a b).toFinset = Ico a (a + b) := by
  ext x
  rw [List.mem_toFinset]; rw [List.mem_range'_1]; rw [Finset.mem_Ico]

/--
lemma `toFinset_range'_1_1` / 引理 `toFinset_range'_1_1`

English:
lemma toFinset_range'_1_1
  given: (a : Nat)
  statement: (List.range' 1 a).toFinset = Icc 1 a
  proof: by
  ext x
  rw [List.mem_toFinset]; rw [List.mem_range'_1]; rw [add_comm]; rw [Nat.lt_succ_iff]; rw [Finset.mem_Icc]

中文:
引理 toFinset_range'_1_1
  条件: (a : 自然数)
  结论: (列表.range' 1 a).toFinset = 闭区间 1 a
  证明: by
  ext x
  rw [List.mem_toFinset]; rw [List.mem_range'_1]; rw [add_comm]; rw [Nat.lt_succ_iff]; rw [Finset.mem_Icc]
-/
lemma toFinset_range'_1_1 (a : Nat) : (List.range' 1 a).toFinset = Icc 1 a := by
  ext x
  rw [List.mem_toFinset]; rw [List.mem_range'_1]; rw [add_comm]; rw [Nat.lt_succ_iff]; rw [Finset.mem_Icc]

/--
lemma `toFinset_range` / 引理 `toFinset_range`

English:
lemma toFinset_range
  given: (a : Nat)
  statement: (List.range a).toFinset = Finset.range a
  proof: by
  ext x
  rw [List.mem_toFinset]; rw [List.mem_range]; rw [Finset.mem_range]

中文:
引理 toFinset_range
  条件: (a : 自然数)
  结论: (列表.range a).toFinset = 有限集.range a
  证明: by
  ext x
  rw [List.mem_toFinset]; rw [List.mem_range]; rw [Finset.mem_range]

Depends on / 依赖: Finset, Finset.mem_range, List.mem_range, List.mem_toFinset, mem_range, mem_toFinset
-/
lemma toFinset_range (a : Nat) : (List.range a).toFinset = Finset.range a := by
  ext x
  rw [List.mem_toFinset]; rw [List.mem_range]; rw [Finset.mem_range]

end List

namespace Finset

/--
theorem `range_image_pred_top_sub` / 定理 `range_image_pred_top_sub`

English:
theorem range_image_pred_top_sub
  given: (n : Nat)
  proof: by
  cases n
  · rw [range_zero, image_empty]
  · rw [Finset.range_eq_Ico, Nat.Ico_image_const_sub_eq_Ico (Nat.zero_le _)]
    simp_rw [succ_sub_succ, Nat.sub_zero, Nat.sub_self]

中文:
定理 range_image_pred_top_sub
  条件: (n : 自然数)
  证明: by
  cases n
  · rw [range_zero, image_empty]
  · rw [Finset.range_eq_Ico, Nat.Ico_image_const_sub_eq_Ico (Nat.zero_le _)]
    simp_rw [succ_sub_succ, Nat.sub_zero, Nat.sub_self]

Depends on / 依赖: Finset, Finset.range_eq_Ico, Ico_image_const_sub_eq_Ico, Nat.Ico_image_const_sub_eq_Ico, Nat.sub_self, Nat.sub_zero, Nat.zero_le, image_empty, range_eq_Ico, range_zero, simp_rw, sub_self, sub_zero, succ_sub_succ, zero_le
-/
theorem range_image_pred_top_sub (n : Nat) :
    ((Finset.range n).image fun j => n - 1 - j) = Finset.range n := by
  cases n
  · rw [range_zero, image_empty]
  · rw [Finset.range_eq_Ico, Nat.Ico_image_const_sub_eq_Ico (Nat.zero_le _)]
    simp_rw [succ_sub_succ, Nat.sub_zero, Nat.sub_self]

/--
theorem `range_add_eq_union` / 定理 `range_add_eq_union`

English:
theorem range_add_eq_union
  statement: range (a + b) = range a union (range b).map (addLeftEmbedding a)
  proof: by
  simp_rw [Finset.range_eq_Ico, map_eq_image]
  convert! (Ico_union_Ico_eq_Ico a.zero_le (a.le_add_right b)).symm
  ext x
  simp only [Ico_zero_eq_range, mem_image, mem_range, addLeftEmbedding_apply, mem_Ico]
  constructor
  · lia
  · rintro h
    exact ⟨x - a, by lia⟩

中文:
定理 range_add_eq_union
  结论: range (a + b) = range a union (range b).map (addLeftEmbedding a)
  证明: by
  simp_rw [Finset.range_eq_Ico, map_eq_image]
  convert! (Ico_union_Ico_eq_Ico a.zero_le (a.le_add_right b)).symm
  ext x
  simp only [Ico_zero_eq_range, mem_image, mem_range, addLeftEmbedding_apply, mem_Ico]
  constructor
  · lia
  · rintro h
    exact ⟨x - a, by lia⟩

Depends on / 依赖: Finset, Finset.range_eq_Ico, Ico_union_Ico_eq_Ico, Ico_zero_eq_range, a.le_add_right, a.zero_le, addLeftEmbedding_apply, convert, le_add_right, map_eq_image, mem_Ico, mem_image, mem_range, range_eq_Ico, simp_rw, zero_le
-/
theorem range_add_eq_union : range (a + b) = range a union (range b).map (addLeftEmbedding a) := by
  simp_rw [Finset.range_eq_Ico, map_eq_image]
  convert! (Ico_union_Ico_eq_Ico a.zero_le (a.le_add_right b)).symm
  ext x
  simp only [Ico_zero_eq_range, mem_image, mem_range, addLeftEmbedding_apply, mem_Ico]
  constructor
  · lia
  · rintro h
    exact ⟨x - a, by lia⟩

end Finset

section Induction

variable {P : Nat -> Prop}

/--
theorem `Nat.decreasing_induction_of_not_bddAbove` / 定理 `Nat.decreasing_induction_of_not_bddAbove`

English:
theorem Nat.decreasing_induction_of_not_bddAbove
  statement: (h : forall n, P (n + 1) -> P n)
  proof: let ⟨_, hm, hl⟩ := not_bddAbove_iff.1 hP n
  decreasingInduction (fun _ _ => h _) hm hl.le

@[elab_as_elim]

中文:
定理 自然数.decreasing_induction_of_not_bddAbove
  结论: (h : 对任意 n, P (n + 1) -> P n)
  证明: let ⟨_, hm, hl⟩ := not_bddAbove_iff.1 hP n
  decreasingInduction (fun _ _ => h _) hm hl.le

@[elab_as_elim]

Depends on / 依赖: decreasingInduction, hl.le, not_bddAbove_iff
-/
theorem Nat.decreasing_induction_of_not_bddAbove (h : forall n, P (n + 1) -> P n)
    (hP : ¬BddAbove { x | P x }) (n : Nat) : P n :=
  let ⟨_, hm, hl⟩ := not_bddAbove_iff.1 hP n
  decreasingInduction (fun _ _ => h _) hm hl.le

@[elab_as_elim]
/--
lemma `Nat.strong_decreasing_induction` / 引理 `Nat.strong_decreasing_induction`

English:
lemma Nat.strong_decreasing_induction
  statement: (base : exists n, forall m > n, P m) (step : forall n, (forall m > n, P m) -> P n)
  proof: by
  apply Nat.decreasing_induction_of_not_bddAbove (P := fun n => forall m >= n, P m) _ _ n n le_rfl
  · intro n ih m hm
    rcases hm.eq_or_lt with rfl | hm
    · exact step n ih
    · exact ih m hm
  · rintro ⟨b, hb⟩
    rcases base with ⟨n, hn⟩
    specialize @hb (n + b + 1) (fun m hm => hn _ _)
    all_goals lia

中文:
引理 自然数.strong_decreasing_induction
  结论: (base : 存在 n, 对任意 m > n, P m) (step : 对任意 n, (对任意 m > n, P m) -> P n)
  证明: by
  apply Nat.decreasing_induction_of_not_bddAbove (P := fun n => forall m >= n, P m) _ _ n n le_rfl
  · intro n ih m hm
    rcases hm.eq_or_lt with rfl | hm
    · exact step n ih
    · exact ih m hm
  · rintro ⟨b, hb⟩
    rcases base with ⟨n, hn⟩
    specialize @hb (n + b + 1) (fun m hm => hn _ _)
    all_goals lia

Depends on / 依赖: Nat.decreasing_induction_of_not_bddAbove, all_goals, decreasing_induction_of_not_bddAbove, eq_or_lt, hm.eq_or_lt, le_rfl, specialize
-/
lemma Nat.strong_decreasing_induction (base : exists n, forall m > n, P m) (step : forall n, (forall m > n, P m) -> P n)
    (n : Nat) : P n := by
  apply Nat.decreasing_induction_of_not_bddAbove (P := fun n => forall m >= n, P m) _ _ n n le_rfl
  · intro n ih m hm
    rcases hm.eq_or_lt with rfl | hm
    · exact step n ih
    · exact ih m hm
  · rintro ⟨b, hb⟩
    rcases base with ⟨n, hn⟩
    specialize @hb (n + b + 1) (fun m hm => hn _ _)
    all_goals lia

/--
theorem `Nat.decreasing_induction_of_infinite` / 定理 `Nat.decreasing_induction_of_infinite`

English:
theorem Nat.decreasing_induction_of_infinite
  proof: Nat.decreasing_induction_of_not_bddAbove h (mt BddAbove.finite hP) n

中文:
定理 自然数.decreasing_induction_of_infinite
  证明: Nat.decreasing_induction_of_not_bddAbove h (mt BddAbove.finite hP) n

Depends on / 依赖: BddAbove, BddAbove.finite, Nat.decreasing_induction_of_not_bddAbove, decreasing_induction_of_not_bddAbove, finite
-/
theorem Nat.decreasing_induction_of_infinite
    (h : forall n, P (n + 1) -> P n) (hP : { x | P x }.Infinite) (n : Nat) : P n :=
  Nat.decreasing_induction_of_not_bddAbove h (mt BddAbove.finite hP) n

/--
theorem `Nat.cauchy_induction'` / 定理 `Nat.cauchy_induction'`

English:
theorem Nat.cauchy_induction'
  statement: (seed : Nat) (h : forall n, P (n + 1) -> P n) (hs : P seed)
  proof: by
  apply Nat.decreasing_induction_of_infinite h fun hf => _
  intro hf
  obtain ⟨m, hP, hm⟩ := hf.exists_maximal ⟨seed, hs⟩
  obtain ⟨y, hl, hy⟩ := hi m (le_of_not_gt <| not_lt_iff_le_imp_ge.2 <| hm hs) hP
  exact hl.not_ge (hm hy hl.le)

中文:
定理 自然数.cauchy_induction'
  结论: (seed : 自然数) (h : 对任意 n, P (n + 1) -> P n) (hs : P seed)
  证明: by
  apply Nat.decreasing_induction_of_infinite h fun hf => _
  intro hf
  obtain ⟨m, hP, hm⟩ := hf.exists_maximal ⟨seed, hs⟩
  obtain ⟨y, hl, hy⟩ := hi m (le_of_not_gt <| not_lt_iff_le_imp_ge.2 <| hm hs) hP
  exact hl.not_ge (hm hy hl.le)

Depends on / 依赖: Nat.decreasing_induction_of_infinite, decreasing_induction_of_infinite, exists_maximal, hf.exists_maximal, hl.le, hl.not_ge, le_of_not_gt, not_ge, not_lt_iff_le_imp_ge
-/
theorem Nat.cauchy_induction' (seed : Nat) (h : forall n, P (n + 1) -> P n) (hs : P seed)
    (hi : forall x, seed <= x -> P x -> exists y, x < y ∧ P y) (n : Nat) : P n := by
  apply Nat.decreasing_induction_of_infinite h fun hf => _
  intro hf
  obtain ⟨m, hP, hm⟩ := hf.exists_maximal ⟨seed, hs⟩
  obtain ⟨y, hl, hy⟩ := hi m (le_of_not_gt <| not_lt_iff_le_imp_ge.2 <| hm hs) hP
  exact hl.not_ge (hm hy hl.le)

/--
theorem `Nat.cauchy_induction` / 定理 `Nat.cauchy_induction`

English:
theorem Nat.cauchy_induction
  statement: (h : forall n, P (n + 1) -> P n) (seed : Nat) (hs : P seed) (f : Nat -> Nat)
  proof: seed.cauchy_induction' h hs (fun x hl hx => ⟨f x, hf x hl hx⟩) n

中文:
定理 自然数.cauchy_induction
  结论: (h : 对任意 n, P (n + 1) -> P n) (seed : 自然数) (hs : P seed) (f : 自然数 -> 自然数)
  证明: seed.cauchy_induction' h hs (fun x hl hx => ⟨f x, hf x hl hx⟩) n

Depends on / 依赖: cauchy_induction, seed.cauchy_induction
-/
theorem Nat.cauchy_induction (h : forall n, P (n + 1) -> P n) (seed : Nat) (hs : P seed) (f : Nat -> Nat)
    (hf : forall x, seed <= x -> P x -> x < f x ∧ P (f x)) (n : Nat) : P n :=
  seed.cauchy_induction' h hs (fun x hl hx => ⟨f x, hf x hl hx⟩) n

/--
theorem `Nat.cauchy_induction_mul` / 定理 `Nat.cauchy_induction_mul`

English:
theorem Nat.cauchy_induction_mul
  statement: (h : forall (n : Nat), P (n + 1) -> P n) (k seed : Nat) (hk : 1 < k)
  proof: by
  apply Nat.cauchy_induction h _ hs (k * ·) fun x hl hP => ⟨_, hm x hl hP⟩
  intro _ hl _
  convert! (Nat.mul_lt_mul_right <| seed.succ_pos.trans_le hl).2 hk
  rw [one_mul]

中文:
定理 自然数.cauchy_induction_mul
  结论: (h : 对任意 (n : 自然数), P (n + 1) -> P n) (k seed : 自然数) (hk : 1 < k)
  证明: by
  apply Nat.cauchy_induction h _ hs (k * ·) fun x hl hP => ⟨_, hm x hl hP⟩
  intro _ hl _
  convert! (Nat.mul_lt_mul_right <| seed.succ_pos.trans_le hl).2 hk
  rw [one_mul]

Depends on / 依赖: Nat.cauchy_induction, Nat.mul_lt_mul_right, cauchy_induction, convert, mul_lt_mul_right, one_mul, seed.succ_pos.trans_le, succ_pos, trans_le
-/
theorem Nat.cauchy_induction_mul (h : forall (n : Nat), P (n + 1) -> P n) (k seed : Nat) (hk : 1 < k)
    (hs : P seed.succ) (hm : forall x, seed < x -> P x -> P (k * x)) (n : Nat) : P n := by
  apply Nat.cauchy_induction h _ hs (k * ·) fun x hl hP => ⟨_, hm x hl hP⟩
  intro _ hl _
  convert! (Nat.mul_lt_mul_right <| seed.succ_pos.trans_le hl).2 hk
  rw [one_mul]

/--
theorem `Nat.cauchy_induction_two_mul` / 定理 `Nat.cauchy_induction_two_mul`

English:
theorem Nat.cauchy_induction_two_mul
  statement: (h : forall n, P (n + 1) -> P n) (seed : Nat) (hs : P seed.succ)
  proof: Nat.cauchy_induction_mul h 2 seed Nat.one_lt_two hs hm n

中文:
定理 自然数.cauchy_induction_two_mul
  结论: (h : 对任意 n, P (n + 1) -> P n) (seed : 自然数) (hs : P seed.succ)
  证明: Nat.cauchy_induction_mul h 2 seed Nat.one_lt_two hs hm n

Depends on / 依赖: Nat.cauchy_induction_mul, Nat.one_lt_two, cauchy_induction_mul, one_lt_two
-/
theorem Nat.cauchy_induction_two_mul (h : forall n, P (n + 1) -> P n) (seed : Nat) (hs : P seed.succ)
    (hm : forall x, seed < x -> P x -> P (2 * x)) (n : Nat) : P n :=
  Nat.cauchy_induction_mul h 2 seed Nat.one_lt_two hs hm n

/--
theorem `Nat.pow_imp_self_of_one_lt` / 定理 `Nat.pow_imp_self_of_one_lt`

English:
theorem Nat.pow_imp_self_of_one_lt
  statement: {M} [Monoid M] (k : Nat) (hk : 1 < k)
  proof: k.cauchy_induction_mul (fun n ih x hx => ih x <| (hmul _ x hx).elim
    (fun h => by rwa [_root_.pow_succ]) fun h => by rwa [_root_.pow_succ']) 0 hk
(fun x hx => pow_one x ▸ hx) fun n _ hn x hx => hpow x hn _ (pow_mul x k n).subst hx

中文:
定理 自然数.pow_imp_self_of_one_lt
  结论: {M} [幺半群 M] (k : 自然数) (hk : 1 < k)
  证明: k.cauchy_induction_mul (fun n ih x hx => ih x <| (hmul _ x hx).elim
    (fun h => by rwa [_root_.pow_succ]) fun h => by rwa [_root_.pow_succ']) 0 hk
(fun x hx => pow_one x ▸ hx) fun n _ hn x hx => hpow x hn _ (pow_mul x k n).subst hx

Depends on / 依赖: _root_, _root_.pow_succ, cauchy_induction_mul, k.cauchy_induction_mul, pow_mul, pow_one, pow_succ
-/
theorem Nat.pow_imp_self_of_one_lt {M} [Monoid M] (k : Nat) (hk : 1 < k)
    (P : M -> Prop) (hmul : forall x y, P x -> P (x * y) ∨ P (y * x))
    (hpow : forall x, P (x ^ k) -> P x) : forall n x, P (x ^ n) -> P x :=
  k.cauchy_induction_mul (fun n ih x hx => ih x <| (hmul _ x hx).elim
    (fun h => by rwa [_root_.pow_succ]) fun h => by rwa [_root_.pow_succ']) 0 hk
(fun x hx => pow_one x ▸ hx) fun n _ hn x hx => hpow x hn _ (pow_mul x k n).subst hx

end Induction
