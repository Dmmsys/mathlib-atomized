/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Eric Wieser
-/
module

public import Mathlib.Algebra.GroupWithZero.Action.Pointwise.Set
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Module.Pointwise
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed

/-!
# Pointwise operations on sets of reals

This file relates `sInf (a • s)`/`sSup (a • s)` with `a • sInf s`/`a • sSup s` for `s : Set ℝ`.

From these, it relates `⨅ i, a • f i` / `⨆ i, a • f i` with `a • (⨅ i, f i)` / `a • (⨆ i, f i)`,
and provides lemmas about distributing `*` over `⨅` and `⨆`.

## TODO

This is true more generally for conditionally complete linear order whose default value is `0`. We
don't have those yet.
-/

public section

assert_not_exists Finset

open Set

open scoped Pointwise

variable {ι : Sort*} {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

section MulActionWithZero

variable [MulActionWithZero α Real] [IsOrderedModule α Real] {a : α}

/--
theorem `Real.sInf_smul_of_nonneg` / 定理 `Real.sInf_smul_of_nonneg`

English:
theorem Real.sInf_smul_of_nonneg
  given: (ha : 0 <= a) (s : Set Real)
  statement: sInf (a • s) = a • sInf s
  proof: by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · rw [smul_set_empty, Real.sInf_empty, smul_zero]
  obtain rfl | ha' := ha.eq_or_lt
  · rw [zero_smul_set hs, zero_smul]
    exact csInf_singleton 0
  by_cases h : BddBelow s
  · exact ((OrderIso.smulRight ha').map_csInf' hs h).symm
  · rw [Real.sInf_

中文:
定理 实数.sInf_smul_of_nonneg
  条件: (ha : 0 <= a) (s : 集合 实数)
  结论: sInf (a • s) = a • sInf s
  证明: by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · rw [smul_set_empty, Real.sInf_empty, smul_zero]
  obtain rfl | ha' := ha.eq_or_lt
  · rw [zero_smul_set hs, zero_smul]
    exact csInf_singleton 0
  by_cases h : BddBelow s
  · exact ((OrderIso.smulRight ha').map_csInf' hs h).symm
  · rw [Real.sInf_

Depends on / 依赖: BddBelow, OrderIso, OrderIso.smulRight, Real.sInf_empty, Real.sInf_of_not_bddBelow, bddBelow_smul_iff_of_pos, csInf_singleton, eq_empty_or_nonempty, eq_or_lt, ha.eq_or_lt, map_csInf, s.eq_empty_or_nonempty, sInf_empty, sInf_of_not_bddBelow, smulRight, smul_set_empty, smul_zero, zero_smul, zero_smul_set
-/
theorem Real.sInf_smul_of_nonneg (ha : 0 <= a) (s : Set Real) : sInf (a • s) = a • sInf s := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · rw [smul_set_empty, Real.sInf_empty, smul_zero]
  obtain rfl | ha' := ha.eq_or_lt
  · rw [zero_smul_set hs, zero_smul]
    exact csInf_singleton 0
  by_cases h : BddBelow s
  · exact ((OrderIso.smulRight ha').map_csInf' hs h).symm
  · rw [Real.sInf_of_not_bddBelow (mt (bddBelow_smul_iff_of_pos ha').1 h),
        Real.sInf_of_not_bddBelow h, smul_zero]

/--
theorem `Real.smul_iInf_of_nonneg` / 定理 `Real.smul_iInf_of_nonneg`

English:
theorem Real.smul_iInf_of_nonneg
  given: (ha : 0 <= a) (f : ι -> Real)
  statement: (a • ⨅ i, f i) = ⨅ i, a • f i
  proof: (Real.sInf_smul_of_nonneg ha _).symm.trans congr_arg sInf (range_comp _ _).symm

中文:
定理 实数.smul_iInf_of_nonneg
  条件: (ha : 0 <= a) (f : ι -> 实数)
  结论: (a • ⨅ i, f i) = ⨅ i, a • f i
  证明: (Real.sInf_smul_of_nonneg ha _).symm.trans congr_arg sInf (range_comp _ _).symm

Depends on / 依赖: Real.sInf_smul_of_nonneg, congr_arg, range_comp, sInf_smul_of_nonneg, symm.trans
-/
theorem Real.smul_iInf_of_nonneg (ha : 0 <= a) (f : ι -> Real) : (a • ⨅ i, f i) = ⨅ i, a • f i :=
(Real.sInf_smul_of_nonneg ha _).symm.trans congr_arg sInf (range_comp _ _).symm

/--
theorem `Real.sSup_smul_of_nonneg` / 定理 `Real.sSup_smul_of_nonneg`

English:
theorem Real.sSup_smul_of_nonneg
  given: (ha : 0 <= a) (s : Set Real)
  statement: sSup (a • s) = a • sSup s
  proof: by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · rw [smul_set_empty, Real.sSup_empty, smul_zero]
  obtain rfl | ha' := ha.eq_or_lt
  · rw [zero_smul_set hs, zero_smul]
    exact csSup_singleton 0
  by_cases h : BddAbove s
  · exact ((OrderIso.smulRight ha').map_csSup' hs h).symm
  · rw [Real.sSup_

中文:
定理 实数.sSup_smul_of_nonneg
  条件: (ha : 0 <= a) (s : 集合 实数)
  结论: sSup (a • s) = a • sSup s
  证明: by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · rw [smul_set_empty, Real.sSup_empty, smul_zero]
  obtain rfl | ha' := ha.eq_or_lt
  · rw [zero_smul_set hs, zero_smul]
    exact csSup_singleton 0
  by_cases h : BddAbove s
  · exact ((OrderIso.smulRight ha').map_csSup' hs h).symm
  · rw [Real.sSup_

Depends on / 依赖: BddAbove, OrderIso, OrderIso.smulRight, Real.sSup_empty, Real.sSup_of_not_bddAbove, bddAbove_smul_iff_of_pos, csSup_singleton, eq_empty_or_nonempty, eq_or_lt, ha.eq_or_lt, map_csSup, s.eq_empty_or_nonempty, sSup_empty, sSup_of_not_bddAbove, smulRight, smul_set_empty, smul_zero, zero_smul, zero_smul_set
-/
theorem Real.sSup_smul_of_nonneg (ha : 0 <= a) (s : Set Real) : sSup (a • s) = a • sSup s := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · rw [smul_set_empty, Real.sSup_empty, smul_zero]
  obtain rfl | ha' := ha.eq_or_lt
  · rw [zero_smul_set hs, zero_smul]
    exact csSup_singleton 0
  by_cases h : BddAbove s
  · exact ((OrderIso.smulRight ha').map_csSup' hs h).symm
  · rw [Real.sSup_of_not_bddAbove (mt (bddAbove_smul_iff_of_pos ha').1 h),
        Real.sSup_of_not_bddAbove h, smul_zero]

/--
theorem `Real.smul_iSup_of_nonneg` / 定理 `Real.smul_iSup_of_nonneg`

English:
theorem Real.smul_iSup_of_nonneg
  given: (ha : 0 <= a) (f : ι -> Real)
  statement: (a • ⨆ i, f i) = ⨆ i, a • f i
  proof: (Real.sSup_smul_of_nonneg ha _).symm.trans congr_arg sSup (range_comp _ _).symm

中文:
定理 实数.smul_iSup_of_nonneg
  条件: (ha : 0 <= a) (f : ι -> 实数)
  结论: (a • ⨆ i, f i) = ⨆ i, a • f i
  证明: (Real.sSup_smul_of_nonneg ha _).symm.trans congr_arg sSup (range_comp _ _).symm

Depends on / 依赖: Real.sSup_smul_of_nonneg, congr_arg, range_comp, sSup_smul_of_nonneg, symm.trans
-/
theorem Real.smul_iSup_of_nonneg (ha : 0 <= a) (f : ι -> Real) : (a • ⨆ i, f i) = ⨆ i, a • f i :=
(Real.sSup_smul_of_nonneg ha _).symm.trans congr_arg sSup (range_comp _ _).symm

end MulActionWithZero

section Module

variable [Module α Real] [IsOrderedModule α Real] {a : α}

/--
theorem `Real.sInf_smul_of_nonpos` / 定理 `Real.sInf_smul_of_nonpos`

English:
theorem Real.sInf_smul_of_nonpos
  given: (ha : a <= 0) (s : Set Real)
  statement: sInf (a • s) = a • sSup s
  proof: by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · rw [smul_set_empty, Real.sInf_empty, Real.sSup_empty, smul_zero]
  obtain rfl | ha' := ha.eq_or_lt
  · rw [zero_smul_set hs, zero_smul]
    exact csInf_singleton 0
  by_cases h : BddAbove s
  · exact ((OrderIso.smulRightDual Real ha').map_csSup' hs 

中文:
定理 实数.sInf_smul_of_nonpos
  条件: (ha : a <= 0) (s : 集合 实数)
  结论: sInf (a • s) = a • sSup s
  证明: by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · rw [smul_set_empty, Real.sInf_empty, Real.sSup_empty, smul_zero]
  obtain rfl | ha' := ha.eq_or_lt
  · rw [zero_smul_set hs, zero_smul]
    exact csInf_singleton 0
  by_cases h : BddAbove s
  · exact ((OrderIso.smulRightDual Real ha').map_csSup' hs 

Depends on / 依赖: BddAbove, OrderIso, OrderIso.smulRightDual, Real.sInf_empty, Real.sInf_of_not_bddBelow, Real.sSup_empty, Real.sSup_of_not_bddAbove, bddBelow_smul_iff_of_neg, csInf_singleton, eq_empty_or_nonempty, eq_or_lt, ha.eq_or_lt, map_csSup, s.eq_empty_or_nonempty, sInf_empty, sInf_of_not_bddBelow, sSup_empty, sSup_of_not_bddAbove, smulRightDual, smul_set_empty
-/
theorem Real.sInf_smul_of_nonpos (ha : a <= 0) (s : Set Real) : sInf (a • s) = a • sSup s := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · rw [smul_set_empty, Real.sInf_empty, Real.sSup_empty, smul_zero]
  obtain rfl | ha' := ha.eq_or_lt
  · rw [zero_smul_set hs, zero_smul]
    exact csInf_singleton 0
  by_cases h : BddAbove s
  · exact ((OrderIso.smulRightDual Real ha').map_csSup' hs h).symm
  · rw [Real.sInf_of_not_bddBelow (mt (bddBelow_smul_iff_of_neg ha').1 h),
        Real.sSup_of_not_bddAbove h, smul_zero]

/--
theorem `Real.smul_iSup_of_nonpos` / 定理 `Real.smul_iSup_of_nonpos`

English:
theorem Real.smul_iSup_of_nonpos
  given: (ha : a <= 0) (f : ι -> Real)
  statement: (a • ⨆ i, f i) = ⨅ i, a • f i
  proof: (Real.sInf_smul_of_nonpos ha _).symm.trans congr_arg sInf (range_comp _ _).symm

中文:
定理 实数.smul_iSup_of_nonpos
  条件: (ha : a <= 0) (f : ι -> 实数)
  结论: (a • ⨆ i, f i) = ⨅ i, a • f i
  证明: (Real.sInf_smul_of_nonpos ha _).symm.trans congr_arg sInf (range_comp _ _).symm

Depends on / 依赖: Real.sInf_smul_of_nonpos, congr_arg, range_comp, sInf_smul_of_nonpos, symm.trans
-/
theorem Real.smul_iSup_of_nonpos (ha : a <= 0) (f : ι -> Real) : (a • ⨆ i, f i) = ⨅ i, a • f i :=
(Real.sInf_smul_of_nonpos ha _).symm.trans congr_arg sInf (range_comp _ _).symm

/--
theorem `Real.sSup_smul_of_nonpos` / 定理 `Real.sSup_smul_of_nonpos`

English:
theorem Real.sSup_smul_of_nonpos
  given: (ha : a <= 0) (s : Set Real)
  statement: sSup (a • s) = a • sInf s
  proof: by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · rw [smul_set_empty, Real.sSup_empty, Real.sInf_empty, smul_zero]
  obtain rfl | ha' := ha.eq_or_lt
  · rw [zero_smul_set hs, zero_smul]
    exact csSup_singleton 0
  by_cases h : BddBelow s
  · exact ((OrderIso.smulRightDual Real ha').map_csInf' hs 

中文:
定理 实数.sSup_smul_of_nonpos
  条件: (ha : a <= 0) (s : 集合 实数)
  结论: sSup (a • s) = a • sInf s
  证明: by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · rw [smul_set_empty, Real.sSup_empty, Real.sInf_empty, smul_zero]
  obtain rfl | ha' := ha.eq_or_lt
  · rw [zero_smul_set hs, zero_smul]
    exact csSup_singleton 0
  by_cases h : BddBelow s
  · exact ((OrderIso.smulRightDual Real ha').map_csInf' hs 

Depends on / 依赖: BddBelow, OrderIso, OrderIso.smulRightDual, Real.sInf_empty, Real.sInf_of_not_bddBelow, Real.sSup_empty, Real.sSup_of_not_bddAbove, bddAbove_smul_iff_of_neg, csSup_singleton, eq_empty_or_nonempty, eq_or_lt, ha.eq_or_lt, map_csInf, s.eq_empty_or_nonempty, sInf_empty, sInf_of_not_bddBelow, sSup_empty, sSup_of_not_bddAbove, smulRightDual, smul_set_empty
-/
theorem Real.sSup_smul_of_nonpos (ha : a <= 0) (s : Set Real) : sSup (a • s) = a • sInf s := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · rw [smul_set_empty, Real.sSup_empty, Real.sInf_empty, smul_zero]
  obtain rfl | ha' := ha.eq_or_lt
  · rw [zero_smul_set hs, zero_smul]
    exact csSup_singleton 0
  by_cases h : BddBelow s
  · exact ((OrderIso.smulRightDual Real ha').map_csInf' hs h).symm
  · rw [Real.sSup_of_not_bddAbove (mt (bddAbove_smul_iff_of_neg ha').1 h),
        Real.sInf_of_not_bddBelow h, smul_zero]

/--
theorem `Real.smul_iInf_of_nonpos` / 定理 `Real.smul_iInf_of_nonpos`

English:
theorem Real.smul_iInf_of_nonpos
  given: (ha : a <= 0) (f : ι -> Real)
  statement: (a • ⨅ i, f i) = ⨆ i, a • f i
  proof: (Real.sSup_smul_of_nonpos ha _).symm.trans congr_arg sSup (range_comp _ _).symm

中文:
定理 实数.smul_iInf_of_nonpos
  条件: (ha : a <= 0) (f : ι -> 实数)
  结论: (a • ⨅ i, f i) = ⨆ i, a • f i
  证明: (Real.sSup_smul_of_nonpos ha _).symm.trans congr_arg sSup (range_comp _ _).symm

Depends on / 依赖: Real.sSup_smul_of_nonpos, congr_arg, range_comp, sSup_smul_of_nonpos, symm.trans
-/
theorem Real.smul_iInf_of_nonpos (ha : a <= 0) (f : ι -> Real) : (a • ⨅ i, f i) = ⨆ i, a • f i :=
(Real.sSup_smul_of_nonpos ha _).symm.trans congr_arg sSup (range_comp _ _).symm

end Module

/-! ## Special cases for real multiplication -/


section Mul

variable {r : Real}

/--
theorem `Real.mul_iInf_of_nonneg` / 定理 `Real.mul_iInf_of_nonneg`

English:
theorem Real.mul_iInf_of_nonneg
  given: (ha : 0 <= r) (f : ι -> Real)
  statement: (r * ⨅ i, f i) = ⨅ i, r * f i
  proof: Real.smul_iInf_of_nonneg ha f

中文:
定理 实数.mul_iInf_of_nonneg
  条件: (ha : 0 <= r) (f : ι -> 实数)
  结论: (r * ⨅ i, f i) = ⨅ i, r * f i
  证明: Real.smul_iInf_of_nonneg ha f

Depends on / 依赖: Real.smul_iInf_of_nonneg, smul_iInf_of_nonneg
-/
theorem Real.mul_iInf_of_nonneg (ha : 0 <= r) (f : ι -> Real) : (r * ⨅ i, f i) = ⨅ i, r * f i :=
  Real.smul_iInf_of_nonneg ha f

/--
theorem `Real.mul_iSup_of_nonneg` / 定理 `Real.mul_iSup_of_nonneg`

English:
theorem Real.mul_iSup_of_nonneg
  given: (ha : 0 <= r) (f : ι -> Real)
  statement: (r * ⨆ i, f i) = ⨆ i, r * f i
  proof: Real.smul_iSup_of_nonneg ha f

中文:
定理 实数.mul_iSup_of_nonneg
  条件: (ha : 0 <= r) (f : ι -> 实数)
  结论: (r * ⨆ i, f i) = ⨆ i, r * f i
  证明: Real.smul_iSup_of_nonneg ha f

Depends on / 依赖: Real.smul_iSup_of_nonneg, smul_iSup_of_nonneg
-/
theorem Real.mul_iSup_of_nonneg (ha : 0 <= r) (f : ι -> Real) : (r * ⨆ i, f i) = ⨆ i, r * f i :=
  Real.smul_iSup_of_nonneg ha f

/--
theorem `Real.mul_iInf_of_nonpos` / 定理 `Real.mul_iInf_of_nonpos`

English:
theorem Real.mul_iInf_of_nonpos
  given: (ha : r <= 0) (f : ι -> Real)
  statement: (r * ⨅ i, f i) = ⨆ i, r * f i
  proof: Real.smul_iInf_of_nonpos ha f

中文:
定理 实数.mul_iInf_of_nonpos
  条件: (ha : r <= 0) (f : ι -> 实数)
  结论: (r * ⨅ i, f i) = ⨆ i, r * f i
  证明: Real.smul_iInf_of_nonpos ha f

Depends on / 依赖: Real.smul_iInf_of_nonpos, smul_iInf_of_nonpos
-/
theorem Real.mul_iInf_of_nonpos (ha : r <= 0) (f : ι -> Real) : (r * ⨅ i, f i) = ⨆ i, r * f i :=
  Real.smul_iInf_of_nonpos ha f

/--
theorem `Real.mul_iSup_of_nonpos` / 定理 `Real.mul_iSup_of_nonpos`

English:
theorem Real.mul_iSup_of_nonpos
  given: (ha : r <= 0) (f : ι -> Real)
  statement: (r * ⨆ i, f i) = ⨅ i, r * f i
  proof: Real.smul_iSup_of_nonpos ha f

中文:
定理 实数.mul_iSup_of_nonpos
  条件: (ha : r <= 0) (f : ι -> 实数)
  结论: (r * ⨆ i, f i) = ⨅ i, r * f i
  证明: Real.smul_iSup_of_nonpos ha f

Depends on / 依赖: Real.smul_iSup_of_nonpos, smul_iSup_of_nonpos
-/
theorem Real.mul_iSup_of_nonpos (ha : r <= 0) (f : ι -> Real) : (r * ⨆ i, f i) = ⨅ i, r * f i :=
  Real.smul_iSup_of_nonpos ha f

/--
theorem `Real.iInf_mul_of_nonneg` / 定理 `Real.iInf_mul_of_nonneg`

English:
theorem Real.iInf_mul_of_nonneg
  given: (ha : 0 <= r) (f : ι -> Real)
  statement: (⨅ i, f i) * r = ⨅ i, f i * r
  proof: by
  simp only [Real.mul_iInf_of_nonneg ha, mul_comm]

中文:
定理 实数.iInf_mul_of_nonneg
  条件: (ha : 0 <= r) (f : ι -> 实数)
  结论: (⨅ i, f i) * r = ⨅ i, f i * r
  证明: by
  simp only [Real.mul_iInf_of_nonneg ha, mul_comm]

Depends on / 依赖: Real.mul_iInf_of_nonneg, mul_comm, mul_iInf_of_nonneg
-/
theorem Real.iInf_mul_of_nonneg (ha : 0 <= r) (f : ι -> Real) : (⨅ i, f i) * r = ⨅ i, f i * r := by
  simp only [Real.mul_iInf_of_nonneg ha, mul_comm]

/--
theorem `Real.iSup_mul_of_nonneg` / 定理 `Real.iSup_mul_of_nonneg`

English:
theorem Real.iSup_mul_of_nonneg
  given: (ha : 0 <= r) (f : ι -> Real)
  statement: (⨆ i, f i) * r = ⨆ i, f i * r
  proof: by
  simp only [Real.mul_iSup_of_nonneg ha, mul_comm]

中文:
定理 实数.iSup_mul_of_nonneg
  条件: (ha : 0 <= r) (f : ι -> 实数)
  结论: (⨆ i, f i) * r = ⨆ i, f i * r
  证明: by
  simp only [Real.mul_iSup_of_nonneg ha, mul_comm]

Depends on / 依赖: Real.mul_iSup_of_nonneg, mul_comm, mul_iSup_of_nonneg
-/
theorem Real.iSup_mul_of_nonneg (ha : 0 <= r) (f : ι -> Real) : (⨆ i, f i) * r = ⨆ i, f i * r := by
  simp only [Real.mul_iSup_of_nonneg ha, mul_comm]

/--
theorem `Real.iInf_mul_of_nonpos` / 定理 `Real.iInf_mul_of_nonpos`

English:
theorem Real.iInf_mul_of_nonpos
  given: (ha : r <= 0) (f : ι -> Real)
  statement: (⨅ i, f i) * r = ⨆ i, f i * r
  proof: by
  simp only [Real.mul_iInf_of_nonpos ha, mul_comm]

中文:
定理 实数.iInf_mul_of_nonpos
  条件: (ha : r <= 0) (f : ι -> 实数)
  结论: (⨅ i, f i) * r = ⨆ i, f i * r
  证明: by
  simp only [Real.mul_iInf_of_nonpos ha, mul_comm]

Depends on / 依赖: Real.mul_iInf_of_nonpos, mul_comm, mul_iInf_of_nonpos
-/
theorem Real.iInf_mul_of_nonpos (ha : r <= 0) (f : ι -> Real) : (⨅ i, f i) * r = ⨆ i, f i * r := by
  simp only [Real.mul_iInf_of_nonpos ha, mul_comm]

/--
theorem `Real.iSup_mul_of_nonpos` / 定理 `Real.iSup_mul_of_nonpos`

English:
theorem Real.iSup_mul_of_nonpos
  given: (ha : r <= 0) (f : ι -> Real)
  statement: (⨆ i, f i) * r = ⨅ i, f i * r
  proof: by
  simp only [Real.mul_iSup_of_nonpos ha, mul_comm]

中文:
定理 实数.iSup_mul_of_nonpos
  条件: (ha : r <= 0) (f : ι -> 实数)
  结论: (⨆ i, f i) * r = ⨅ i, f i * r
  证明: by
  simp only [Real.mul_iSup_of_nonpos ha, mul_comm]

Depends on / 依赖: Real.mul_iSup_of_nonpos, mul_comm, mul_iSup_of_nonpos
-/
theorem Real.iSup_mul_of_nonpos (ha : r <= 0) (f : ι -> Real) : (⨆ i, f i) * r = ⨅ i, f i * r := by
  simp only [Real.mul_iSup_of_nonpos ha, mul_comm]

end Mul
