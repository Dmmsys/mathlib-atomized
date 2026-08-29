/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Alex J. Best
-/
module

public import Mathlib.MeasureTheory.Group.Arithmetic

/-!
# Pointwise set operations on `MeasurableSet`s

In this file we prove several versions of the following fact: if `s` is a measurable set, then so is
`a • s`. Note that the pointwise product of two measurable sets need not be measurable, so there is
no `MeasurableSet.mul` etc.
-/

public section


open scoped Pointwise

open Set

@[to_additive]
/--
theorem `MeasurableSet.const_smul` / 定理 `MeasurableSet.const_smul`

English:
theorem MeasurableSet.const_smul
  statement: {G α : Type*} [Group G] [MulAction G α]
  proof: by
  rw [← preimage_smul_inv]
  exact measurable_const_smul _ hs

中文:
定理 MeasurableSet.const_smul
  结论: {G α : 类型} [Group G] [MulAction G α]
  证明: by
  rw [← preimage_smul_inv]
  exact measurable_const_smul _ hs

Depends on / 依赖: measurable_const_smul, preimage_smul_inv
-/
theorem MeasurableSet.const_smul {G α : Type*} [Group G] [MulAction G α]
    [MeasurableSpace α] [MeasurableConstSMul G α] {s : Set α} (hs : MeasurableSet s) (a : G) :
    MeasurableSet (a • s) := by
  rw [← preimage_smul_inv]
  exact measurable_const_smul _ hs

/--
theorem `MeasurableSet.const_smul_of_ne_zero` / 定理 `MeasurableSet.const_smul_of_ne_zero`

English:
theorem MeasurableSet.const_smul_of_ne_zero
  statement: {G₀ α : Type*} [GroupWithZero G₀] [MulAction G₀ α]
  proof: by
  rw [← preimage_smul_inv₀ ha]
  exact measurable_const_smul _ hs

中文:
定理 MeasurableSet.const_smul_of_ne_zero
  结论: {G₀ α : 类型} [GroupWithZero G₀] [MulAction G₀ α]
  证明: by
  rw [← preimage_smul_inv₀ ha]
  exact measurable_const_smul _ hs

Depends on / 依赖: measurable_const_smul
-/
theorem MeasurableSet.const_smul_of_ne_zero {G₀ α : Type*} [GroupWithZero G₀] [MulAction G₀ α]
    [MeasurableSpace α] [MeasurableConstSMul G₀ α] {s : Set α}
    (hs : MeasurableSet s) {a : G₀} (ha : a != 0) : MeasurableSet (a • s) := by
  rw [← preimage_smul_inv₀ ha]
  exact measurable_const_smul _ hs

/--
theorem `MeasurableSet.const_smul₀` / 定理 `MeasurableSet.const_smul₀`

English:
theorem MeasurableSet.const_smul₀
  statement: {G₀ α : Type*} [GroupWithZero G₀] [Zero α]
  proof: by
  rcases eq_or_ne a 0 with (rfl | ha)
  exacts [(subsingleton_zero_smul_set s).measurableSet, hs.const_smul_of_ne_zero ha]

中文:
定理 MeasurableSet.const_smul₀
  结论: {G₀ α : 类型} [GroupWithZero G₀] [Zero α]
  证明: by
  rcases eq_or_ne a 0 with (rfl | ha)
  exacts [(subsingleton_zero_smul_set s).measurableSet, hs.const_smul_of_ne_zero ha]

Depends on / 依赖: const_smul_of_ne_zero, eq_or_ne, exacts, hs.const_smul_of_ne_zero, measurableSet, subsingleton_zero_smul_set
-/
theorem MeasurableSet.const_smul₀ {G₀ α : Type*} [GroupWithZero G₀] [Zero α]
    [MulActionWithZero G₀ α] [MeasurableSpace α] [MeasurableConstSMul G₀ α]
    [MeasurableSingletonClass α] {s : Set α} (hs : MeasurableSet s) (a : G₀) :
    MeasurableSet (a • s) := by
  rcases eq_or_ne a 0 with (rfl | ha)
  exacts [(subsingleton_zero_smul_set s).measurableSet, hs.const_smul_of_ne_zero ha]
