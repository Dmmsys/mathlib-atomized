/-
Copyright (c) 2021 Yourong Zang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yourong Zang
-/
module

public import Mathlib.Analysis.Normed.Operator.Conformal
public import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Conformal maps between inner product spaces

In an inner product space, a map is conformal iff it preserves inner products up to a scalar factor.
-/

public section


variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [InnerProductSpace Real E] [InnerProductSpace Real F]

open LinearIsometry ContinuousLinearMap

open RealInnerProductSpace

/--
theorem `isConformalMap_iff` / 定理 `isConformalMap_iff`

English:
theorem isConformalMap_iff
  given: (f : E ->L[Real] F)
  proof: by
  constructor
  · rintro ⟨c₁, hc₁, li, rfl⟩
    refine ⟨c₁ * c₁, mul_self_pos.2 hc₁, fun u v => ?_⟩
    simp only [real_inner_smul_left, real_inner_smul_right, mul_assoc,
      coe_toContinuousLinearMap, smul_apply, inner_map_map]
  · rintro ⟨c₁, hc₁, huv⟩
    obtain ⟨c, hc, rfl⟩ : exists c : Rea

中文:
定理 isConformalMap_iff
  条件: (f : E ->L[实数] F)
  证明: by
  constructor
  · rintro ⟨c₁, hc₁, li, rfl⟩
    refine ⟨c₁ * c₁, mul_self_pos.2 hc₁, fun u v => ?_⟩
    simp only [real_inner_smul_left, real_inner_smul_right, mul_assoc,
      coe_toContinuousLinearMap, smul_apply, inner_map_map]
  · rintro ⟨c₁, hc₁, huv⟩
    obtain ⟨c, hc, rfl⟩ : exists c : Rea

Depends on / 依赖: Real.mul_self_sqrt, Real.sqrt_pos, coe_toContinuousLinearMap, hc.ne, inner_map_map, isometryOfInner, mul_assoc, mul_self_pos, mul_self_sqrt, real_inner_smul_left, real_inner_smul_right, smul_apply, sqrt_pos
-/
theorem isConformalMap_iff (f : E ->L[Real] F) :
    IsConformalMap f ↔ exists c : Real, 0 < c ∧ forall u v : E, ⟪f u, f v⟫ = c * ⟪u, v⟫ := by
  constructor
  · rintro ⟨c₁, hc₁, li, rfl⟩
    refine ⟨c₁ * c₁, mul_self_pos.2 hc₁, fun u v => ?_⟩
    simp only [real_inner_smul_left, real_inner_smul_right, mul_assoc,
      coe_toContinuousLinearMap, smul_apply, inner_map_map]
  · rintro ⟨c₁, hc₁, huv⟩
    obtain ⟨c, hc, rfl⟩ : exists c : Real, 0 < c ∧ c₁ = c * c :=
      ⟨√c₁, Real.sqrt_pos.2 hc₁, (Real.mul_self_sqrt hc₁.le).symm⟩
    refine ⟨c, hc.ne', (c⁻¹ • f : E ->ₗ[Real] F).isometryOfInner fun u v => ?_, ?_⟩
    · simp only [real_inner_smul_left, real_inner_smul_right, huv, mul_assoc,
        inv_mul_cancel_left₀ hc.ne', LinearMap.smul_apply, ContinuousLinearMap.coe_coe]
    · ext1 x
      exact (smul_inv_smul₀ hc.ne' (f x)).symm
