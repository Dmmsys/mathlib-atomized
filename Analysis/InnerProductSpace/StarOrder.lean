/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# Continuous linear maps on a Hilbert space are a `StarOrderedRing`

In this file we show that the continuous linear maps on a complex Hilbert space form a
`StarOrderedRing`. Note that they are already equipped with the Loewner partial order. We also
prove that, with respect to this partial order, a map is positive if every element of the
real spectrum is nonnegative. Consequently, when `H` is a Hilbert space, then `H →L[ℂ] H` is
equipped with all the usual instances of the continuous functional calculus.

-/

public section

namespace ContinuousLinearMap

open RCLike
open scoped NNReal

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable [Algebra Real (H ->L[𝕜] H)] [IsScalarTower Real 𝕜 (H ->L[𝕜] H)]

open scoped InnerProductSpace in
/--
lemma `IsPositive.spectrumRestricts` / 引理 `IsPositive.spectrumRestricts`

English:
lemma IsPositive.spectrumRestricts
  given: {f : H ->L[𝕜] H} (hf : f.IsPositive)
  proof: by
  rw [SpectrumRestricts.nnreal_iff]
  intro c hc
  contrapose! hc
  rw [spectrum.notMem_iff]; rw [IsUnit.sub_iff]; rw [sub_eq_add_neg]; rw [← map_neg]
  rw [← neg_pos] at hc
  set c := -c
  exact isUnit_of_forall_le_norm_inner_map _ (c := ⟨c, hc.le⟩) hc fun x => calc
    ‖x‖ ^ 2 * c = re ⟪algebra

中文:
引理 IsPositive.spectrumRestricts
  条件: {f : H ->L[𝕜] H} (hf : f.IsPositive)
  证明: by
  rw [SpectrumRestricts.nnreal_iff]
  intro c hc
  contrapose! hc
  rw [spectrum.notMem_iff]; rw [IsUnit.sub_iff]; rw [sub_eq_add_neg]; rw [← map_neg]
  rw [← neg_pos] at hc
  set c := -c
  exact isUnit_of_forall_le_norm_inner_map _ (c := ⟨c, hc.le⟩) hc fun x => calc
    ‖x‖ ^ 2 * c = re ⟪algebra

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, IsUnit, IsUnit.sub_iff, RCLike, RCLike.algebraMap_eq_ofReal, SpectrumRestricts, SpectrumRestricts.nnreal_iff, algebraMap, algebraMap_eq_ofReal, algebraMap_eq_smul_one, algebraMap_smul, conj_ofReal, contrapose, hc.le, inner_smul_left, isUnit_of_forall_le_norm_inner_map, map_neg, neg_pos, nnreal_iff
-/
lemma IsPositive.spectrumRestricts {f : H ->L[𝕜] H} (hf : f.IsPositive) :
    SpectrumRestricts f ContinuousMap.realToNNReal := by
  rw [SpectrumRestricts.nnreal_iff]
  intro c hc
  contrapose! hc
  rw [spectrum.notMem_iff]; rw [IsUnit.sub_iff]; rw [sub_eq_add_neg]; rw [← map_neg]
  rw [← neg_pos] at hc
  set c := -c
  exact isUnit_of_forall_le_norm_inner_map _ (c := ⟨c, hc.le⟩) hc fun x => calc
    ‖x‖ ^ 2 * c = re ⟪algebraMap Real (H ->L[𝕜] H) c x, x⟫_𝕜 := by
      rw [Algebra.algebraMap_eq_smul_one]; rw [← algebraMap_smul 𝕜 c (1 : (H ->L[𝕜] H)), smul_apply,
        one_apply_eq_self, inner_smul_left, RCLike.algebraMap_eq_ofReal, conj_ofReal, re_ofReal_mul,
        inner_self_eq_norm_sq, mul_comm]
    _ <= re ⟪(f + (algebraMap Real (H ->L[𝕜] H)) c) x, x⟫_𝕜 := by
      simpa only [add_apply, inner_add_left, map_add, le_add_iff_nonneg_left]
        using hf.re_inner_nonneg_left x
    _ <= ‖⟪(f + (algebraMap Real (H ->L[𝕜] H)) c) x, x⟫_𝕜‖ := RCLike.re_le_norm _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NonnegSpectrumClass Real (H ->L[𝕜] H)
  body: QuasispectrumRestricts.nnreal_iff.mp sub_zero f ▸ hf.spectrumRestricts

中文:
实例 :
  签名: NonnegSpectrumClass 实数 (H ->L[𝕜] H)
  定义体: QuasispectrumRestricts.nnreal_iff.mp sub_zero f ▸ hf.spectrumRestricts

Depends on / 依赖: QuasispectrumRestricts, QuasispectrumRestricts.nnreal_iff.mp, hf.spectrumRestricts, nnreal_iff, spectrumRestricts, sub_zero
-/
instance : NonnegSpectrumClass Real (H ->L[𝕜] H) where
  quasispectrum_nonneg_of_nonneg f hf :=
QuasispectrumRestricts.nnreal_iff.mp sub_zero f ▸ hf.spectrumRestricts

/--
lemma `instStarOrderedRingRCLike` / 引理 `instStarOrderedRingRCLike`

English:
lemma instStarOrderedRingRCLike
  proof: by
    constructor
    · intro h
      rw [le_def] at h
      obtain ⟨p, hp₁, -, hp₃⟩ := CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts
        h.isSelfAdjoint h.spectrumRestricts
      refine ⟨p ^ 2, ?_, by symm; rwa [add_comm, ← eq_sub_iff_add_eq]⟩
      exact AddSubmonoid.subset_closu

中文:
引理 instStarOrderedRingRCLike
  证明: by
    constructor
    · intro h
      rw [le_def] at h
      obtain ⟨p, hp₁, -, hp₃⟩ := CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts
        h.isSelfAdjoint h.spectrumRestricts
      refine ⟨p ^ 2, ?_, by symm; rwa [add_comm, ← eq_sub_iff_add_eq]⟩
      exact AddSubmonoid.subset_closu

Depends on / 依赖: AddSubmonoid, AddSubmonoid.closure_induction, AddSubmonoid.subset_closure, CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts, ContinuousLinearMap, ContinuousLinearMap.IsPositive.adjoin, IsPositive, add_comm, add_sub_cancel_left, adjoin, closure_induction, eq_sub_iff_add_eq, exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts, h.isSelfAdjoint, h.spectrumRestricts, isSelfAdjoint, le_def, spectrumRestricts, star_eq, subset_closure
-/
lemma instStarOrderedRingRCLike
    [ContinuousFunctionalCalculus Real (H ->L[𝕜] H) IsSelfAdjoint] :
    StarOrderedRing (H ->L[𝕜] H) where
  le_iff f g := by
    constructor
    · intro h
      rw [le_def] at h
      obtain ⟨p, hp₁, -, hp₃⟩ := CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts
        h.isSelfAdjoint h.spectrumRestricts
      refine ⟨p ^ 2, ?_, by symm; rwa [add_comm, ← eq_sub_iff_add_eq]⟩
      exact AddSubmonoid.subset_closure ⟨p, by simp only [hp₁.star_eq, sq]⟩
    · rintro ⟨p, hp, rfl⟩
      rw [le_def]; rw [add_sub_cancel_left]
      induction hp using AddSubmonoid.closure_induction with
      | mem _ hf =>
        obtain ⟨f, rfl⟩ := hf
        simpa using! ContinuousLinearMap.IsPositive.adjoint_conj isPositive_one f
      | zero => exact isPositive_zero
      | add f g _ _ hf hg => exact hf.add hg

/--
Instance `instStarOrderedRing` / 实例 `instStarOrderedRing`

English:
instance instStarOrderedRing
  signature: {H : Type*} [NormedAddCommGroup H]
  body: instStarOrderedRingRCLike

中文:
实例 instStarOrderedRing
  签名: {H : 类型} [NormedAddCommGroup H]
  定义体: instStarOrderedRingRCLike

Depends on / 依赖: instStarOrderedRingRCLike
-/
instance instStarOrderedRing {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace Complex H] [CompleteSpace H] : StarOrderedRing (H ->L[Complex] H) :=
  instStarOrderedRingRCLike

end ContinuousLinearMap
