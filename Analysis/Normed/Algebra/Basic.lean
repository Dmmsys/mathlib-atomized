/-
Copyright (c) 2022 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Topology.Algebra.Module.Spaces.CharacterSpace
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Analysis.Normed.Algebra.Spectrum

/-!
# Normed algebras

This file contains basic facts about normed algebras.

## Main results

* We show that the character space of a normed algebra is compact using the Banach-Alaoglu theorem.

## TODO

* Show compactness for topological vector spaces; this requires the TVS version of Banach-Alaoglu.

## Tags

normed algebra, character space, continuous functional calculus

-/

public section

namespace IntermediateField

variable {K L : Type*} [NontriviallyNormedField K] [NormedField L] [NormedAlgebra K L]

instance (F : IntermediateField K L) : NontriviallyNormedField F where
  __ := SubfieldClass.toNormedField F
  non_trivial := by
    obtain ⟨k, hk⟩ := @NontriviallyNormedField.non_trivial K _
    use algebraMap K F k
    simp [hk]

end IntermediateField

variable {𝕜 : Type*} {A : Type*}

namespace WeakDual

namespace CharacterSpace

variable [NontriviallyNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]

/--
theorem `norm_le_norm_one` / 定理 `norm_le_norm_one`

English:
theorem norm_le_norm_one
  given: (φ : characterSpace 𝕜 A)
  statement: ‖toStrongDual (φ : WeakDual 𝕜 A)‖ <= ‖(1 : A)‖
  proof: ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (1 : A)) fun a =>
    mul_comm ‖a‖ ‖(1 : A)‖ ▸ spectrum.norm_le_norm_mul_of_mem (apply_mem_spectrum φ a)

中文:
定理 norm_le_norm_one
  条件: (φ : characterSpace 𝕜 A)
  结论: ‖toStrongDual (φ : WeakDual 𝕜 A)‖ <= ‖(1 : A)‖
  证明: ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (1 : A)) fun a =>
    mul_comm ‖a‖ ‖(1 : A)‖ ▸ spectrum.norm_le_norm_mul_of_mem (apply_mem_spectrum φ a)

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.opNorm_le_bound, apply_mem_spectrum, mul_comm, norm_le_norm_mul_of_mem, norm_nonneg, opNorm_le_bound, spectrum, spectrum.norm_le_norm_mul_of_mem
-/
theorem norm_le_norm_one (φ : characterSpace 𝕜 A) : ‖toStrongDual (φ : WeakDual 𝕜 A)‖ <= ‖(1 : A)‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (1 : A)) fun a =>
    mul_comm ‖a‖ ‖(1 : A)‖ ▸ spectrum.norm_le_norm_mul_of_mem (apply_mem_spectrum φ a)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [ProperSpace
  signature: 𝕜] : CompactSpace (characterSpace 𝕜 A)
  body: by
  rw [← isCompact_iff_compactSpace]
  have h : characterSpace 𝕜 A subseteq toStrongDual ⁻¹' Metric.closedBall 0 ‖(1 : A)‖ := by
    intro φ hφ
    rw [Set.mem_preimage]; rw [mem_closedBall_zero_iff]
    exact (norm_le_norm_one ⟨φ, ⟨hφ.1, hφ.2⟩⟩ :)
  exact (isCompact_closedBall 0 _).of_isClosed_su

中文:
实例 [真空间
  签名: 𝕜] : 紧空间 (characterSpace 𝕜 A)
  定义体: by
  rw [← isCompact_iff_compactSpace]
  have h : characterSpace 𝕜 A subseteq toStrongDual ⁻¹' Metric.closedBall 0 ‖(1 : A)‖ := by
    intro φ hφ
    rw [Set.mem_preimage]; rw [mem_closedBall_zero_iff]
    exact (norm_le_norm_one ⟨φ, ⟨hφ.1, hφ.2⟩⟩ :)
  exact (isCompact_closedBall 0 _).of_isClosed_su

Depends on / 依赖: CharacterSpace, CharacterSpace.isClosed, Metric, Metric.closedBall, Set.mem_preimage, characterSpace, closedBall, isClosed, isCompact_closedBall, isCompact_iff_compactSpace, mem_closedBall_zero_iff, mem_preimage, norm_le_norm_one, of_isClosed_subset, subseteq, toStrongDual
-/
instance [ProperSpace 𝕜] : CompactSpace (characterSpace 𝕜 A) := by
  rw [← isCompact_iff_compactSpace]
  have h : characterSpace 𝕜 A subseteq toStrongDual ⁻¹' Metric.closedBall 0 ‖(1 : A)‖ := by
    intro φ hφ
    rw [Set.mem_preimage]; rw [mem_closedBall_zero_iff]
    exact (norm_le_norm_one ⟨φ, ⟨hφ.1, hφ.2⟩⟩ :)
  exact (isCompact_closedBall 0 _).of_isClosed_subset CharacterSpace.isClosed h

end CharacterSpace

end WeakDual
