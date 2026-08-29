/-
Copyright (c) 2021 Yourong Zang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yourong Zang, Stefan Kebekus
-/
module

public import Mathlib.Analysis.Calculus.Conformal.NormedSpace
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.Complex.Module

/-!
# Conformal maps between complex vector spaces

We prove the sufficient and necessary conditions for a real-linear map between complex vector spaces
to be conformal.

## Main results

* `isConformalMap_complex_linear`: a nonzero complex linear map into an arbitrary complex normed
  space is conformal.

* `isConformalMap_complex_linear_conj`: the composition of a nonzero complex linear map with `conj`
  is complex linear.

* `isConformalMap_iff_is_complex_or_conj_linear`: a real linear map between the complex plane is
  conformal iff it's complex linear or the composition of some complex linear map and `conj`.

* `DifferentiableAt.conformalAt` states that a real-differentiable function with a nonvanishing
  differential from the complex plane into an arbitrary complex-normed space is conformal at a point
  if it's holomorphic at that point. This is a version of Cauchy-Riemann equations.

* `conformalAt_iff_differentiableAt_or_differentiableAt_comp_conj` proves that a real-differential
  function with a nonvanishing differential between the complex plane is conformal at a point if and
  only if it's holomorphic or antiholomorphic at that point.

* `differentiableWithinAt_complex_iff_differentiableWithinAt_real` and
  `differentiableAt_complex_iff_differentiableAt_real` characterize complex differentiability in
  terms of the classic Cauchy-Riemann equation.

## Warning

Antiholomorphic functions such as the complex conjugate are considered as conformal functions in
this file.

## TODO

* On a connected open set `u`, a function which is `ConformalAt` each point is either holomorphic
  throughout or antiholomorphic throughout.
-/

@[expose] public section


noncomputable section

open Complex ContinuousLinearMap ComplexConjugate

/--
theorem `isConformalMap_conj` / 定理 `isConformalMap_conj`

English:
theorem isConformalMap_conj
  statement: IsConformalMap (conjLIE : Complex ->L[Real] Complex)
  proof: conjLIE.toLinearIsometry.isConformalMap

中文:
定理 isConformalMap_conj
  结论: IsConformalMap (conjLIE : 复形 ->L[实数] 复形)
  证明: conjLIE.toLinearIsometry.isConformalMap

Depends on / 依赖: conjLIE, conjLIE.toLinearIsometry.isConformalMap, isConformalMap, toLinearIsometry
-/
theorem isConformalMap_conj : IsConformalMap (conjLIE : Complex ->L[Real] Complex) :=
  conjLIE.toLinearIsometry.isConformalMap

section ConformalIntoComplexNormed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [NormedSpace Complex E]

/--
theorem `isConformalMap_complex_linear` / 定理 `isConformalMap_complex_linear`

English:
theorem isConformalMap_complex_linear
  given: {map : Complex ->L[Complex] E} (nonzero : map != 0)
  proof: by
  have minor₁ : ‖map 1‖ != 0 := by
    simpa only [ContinuousLinearMap.ext_ring_iff, Ne, norm_eq_zero] using! nonzero
  refine ⟨‖map 1‖, minor₁, ⟨‖map 1‖⁻¹ • ((map : Complex ->ₗ[Complex] E) : Complex ->ₗ[Real] E), ?_⟩, ?_⟩
  · intro x
    simp only [LinearMap.smul_apply]
    have : x = x • (1 : Complex) := by rw [smul_eq_mul, mul_one]
    nth_rw 1 [this]
    rw [LinearMap.coe_restrictScalars]
    simp only [map.coe_coe, map.map_smul, norm_smul, norm_inv, norm_norm]
    field
  · ext1
    simp [minor₁]

中文:
定理 isConformalMap_complex_linear
  条件: {map : 复形 ->L[复形] E} (nonzero : map != 0)
  证明: by
  have minor₁ : ‖map 1‖ != 0 := by
    simpa only [ContinuousLinearMap.ext_ring_iff, Ne, norm_eq_zero] using! nonzero
  refine ⟨‖map 1‖, minor₁, ⟨‖map 1‖⁻¹ • ((map : Complex ->ₗ[Complex] E) : Complex ->ₗ[Real] E), ?_⟩, ?_⟩
  · intro x
    simp only [LinearMap.smul_apply]
    have : x = x • (1 : Complex) := by rw [smul_eq_mul, mul_one]
    nth_rw 1 [this]
    rw [LinearMap.coe_restrictScalars]
    simp only [map.coe_coe, map.map_smul, norm_smul, norm_inv, norm_norm]
    field
  · ext1
    simp [minor₁]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.ext_ring_iff, LinearMap, LinearMap.coe_restrictScalars, LinearMap.smul_apply, coe_coe, coe_restrictScalars, ext_ring_iff, map.coe_coe, map.map_smul, map_smul, mul_one, nonzero, norm_eq_zero, norm_inv, norm_norm, norm_smul, nth_rw, smul_apply, smul_eq_mul
-/
theorem isConformalMap_complex_linear {map : Complex ->L[Complex] E} (nonzero : map != 0) :
    IsConformalMap (map.restrictScalars Real) := by
  have minor₁ : ‖map 1‖ != 0 := by
    simpa only [ContinuousLinearMap.ext_ring_iff, Ne, norm_eq_zero] using! nonzero
  refine ⟨‖map 1‖, minor₁, ⟨‖map 1‖⁻¹ • ((map : Complex ->ₗ[Complex] E) : Complex ->ₗ[Real] E), ?_⟩, ?_⟩
  · intro x
    simp only [LinearMap.smul_apply]
    have : x = x • (1 : Complex) := by rw [smul_eq_mul, mul_one]
    nth_rw 1 [this]
    rw [LinearMap.coe_restrictScalars]
    simp only [map.coe_coe, map.map_smul, norm_smul, norm_inv, norm_norm]
    field
  · ext1
    simp [minor₁]

/--
theorem `isConformalMap_complex_linear_conj` / 定理 `isConformalMap_complex_linear_conj`

English:
theorem isConformalMap_complex_linear_conj
  given: {map : Complex ->L[Complex] E} (nonzero : map != 0)
  proof: (isConformalMap_complex_linear nonzero).comp isConformalMap_conj

中文:
定理 isConformalMap_complex_linear_conj
  条件: {map : 复形 ->L[复形] E} (nonzero : map != 0)
  证明: (isConformalMap_complex_linear nonzero).comp isConformalMap_conj

Depends on / 依赖: isConformalMap_complex_linear, isConformalMap_conj, nonzero
-/
theorem isConformalMap_complex_linear_conj {map : Complex ->L[Complex] E} (nonzero : map != 0) :
    IsConformalMap ((map.restrictScalars Real).comp (conjCLE : Complex ->L[Real] Complex)) :=
  (isConformalMap_complex_linear nonzero).comp isConformalMap_conj

end ConformalIntoComplexNormed

section ConformalIntoComplexPlane

open ContinuousLinearMap

variable {g : Complex ->L[Real] Complex}

/--
theorem `IsConformalMap.is_complex_or_conj_linear` / 定理 `IsConformalMap.is_complex_or_conj_linear`

English:
theorem IsConformalMap.is_complex_or_conj_linear
  given: (h : IsConformalMap g)
  proof: by
  rcases h with ⟨c, -, li, rfl⟩
  obtain ⟨li, rfl⟩ : exists li' : Complex ≃ₗᵢ[Real] Complex, li'.toLinearIsometry = li :=
    ⟨li.toLinearIsometryEquiv rfl, by ext1; rfl⟩
  rcases linear_isometry_complex li with ⟨a, rfl | rfl⟩
  -- let rot := c • (a : ℂ) • ContinuousLinearMap.id ℂ ℂ,
  · refine Or.inl ⟨c • (a : Complex) • ContinuousLinearMap.id Complex Complex, ?_⟩
    ext1
    simp
  · refine Or.inr ⟨c • (a : Complex) • ContinuousLinearMap.id Complex Complex, ?_⟩
    ext1
    simp

中文:
定理 IsConformalMap.is_complex_or_conj_linear
  条件: (h : IsConformalMap g)
  证明: by
  rcases h with ⟨c, -, li, rfl⟩
  obtain ⟨li, rfl⟩ : exists li' : Complex ≃ₗᵢ[Real] Complex, li'.toLinearIsometry = li :=
    ⟨li.toLinearIsometryEquiv rfl, by ext1; rfl⟩
  rcases linear_isometry_complex li with ⟨a, rfl | rfl⟩
  -- let rot := c • (a : ℂ) • ContinuousLinearMap.id ℂ ℂ,
  · refine Or.inl ⟨c • (a : Complex) • ContinuousLinearMap.id Complex Complex, ?_⟩
    ext1
    simp
  · refine Or.inr ⟨c • (a : Complex) • ContinuousLinearMap.id Complex Complex, ?_⟩
    ext1
    simp

Depends on / 依赖: li.toLinearIsometryEquiv, linear_isometry_complex, toLinearIsometry, toLinearIsometryEquiv
-/
theorem IsConformalMap.is_complex_or_conj_linear (h : IsConformalMap g) :
    (exists map : Complex ->L[Complex] Complex, map.restrictScalars Real = g) ∨
      exists map : Complex ->L[Complex] Complex, map.restrictScalars Real = g ∘L ↑conjCLE := by
  rcases h with ⟨c, -, li, rfl⟩
  obtain ⟨li, rfl⟩ : exists li' : Complex ≃ₗᵢ[Real] Complex, li'.toLinearIsometry = li :=
    ⟨li.toLinearIsometryEquiv rfl, by ext1; rfl⟩
  rcases linear_isometry_complex li with ⟨a, rfl | rfl⟩
  -- let rot := c • (a : ℂ) • ContinuousLinearMap.id ℂ ℂ,
  · refine Or.inl ⟨c • (a : Complex) • ContinuousLinearMap.id Complex Complex, ?_⟩
    ext1
    simp
  · refine Or.inr ⟨c • (a : Complex) • ContinuousLinearMap.id Complex Complex, ?_⟩
    ext1
    simp

/--
theorem `isConformalMap_iff_is_complex_or_conj_linear` / 定理 `isConformalMap_iff_is_complex_or_conj_linear`

English:
theorem isConformalMap_iff_is_complex_or_conj_linear
  proof: by
  constructor
  · exact fun h => ⟨h.is_complex_or_conj_linear, h.ne_zero⟩
  · rintro ⟨⟨map, rfl⟩ | ⟨map, hmap⟩, h₂⟩
    · refine isConformalMap_complex_linear ?_
      contrapose h₂ with w
      simp only [w, restrictScalars_zero]
    · have minor₁ : g = map.restrictScalars Real ∘L ↑conjCLE := by
        ext1
        simp only [hmap, ContinuousLinearEquiv.coe_coe, comp_apply, conjCLE_apply,
          starRingEnd_self_apply]
      rw [minor₁] at h₂ ⊢
      refine isConformalMap_complex_linear_conj ?_
      contrapose h₂ with w
      simp only [w, restrictScalars_zero, zero_comp]

中文:
定理 isConformalMap_iff_is_complex_or_conj_linear
  证明: by
  constructor
  · exact fun h => ⟨h.is_complex_or_conj_linear, h.ne_zero⟩
  · rintro ⟨⟨map, rfl⟩ | ⟨map, hmap⟩, h₂⟩
    · refine isConformalMap_complex_linear ?_
      contrapose h₂ with w
      simp only [w, restrictScalars_zero]
    · have minor₁ : g = map.restrictScalars Real ∘L ↑conjCLE := by
        ext1
        simp only [hmap, ContinuousLinearEquiv.coe_coe, comp_apply, conjCLE_apply,
          starRingEnd_self_apply]
      rw [minor₁] at h₂ ⊢
      refine isConformalMap_complex_linear_conj ?_
      contrapose h₂ with w
      simp only [w, restrictScalars_zero, zero_comp]

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe, coe_coe, comp_apply, conjCLE, conjCLE_apply, contrapose, h.is_complex_or_conj_linear, h.ne_zero, isConformalMap_complex_linear, isConformalMap_complex_linear_conj, is_complex_or_conj_linear, map.restrictScalars, ne_zero, restrictScalars, restrictScalars_zero, starRingEnd_self_apply
-/
theorem isConformalMap_iff_is_complex_or_conj_linear :
    IsConformalMap g ↔
      ((exists map : Complex ->L[Complex] Complex, map.restrictScalars Real = g) ∨
          exists map : Complex ->L[Complex] Complex, map.restrictScalars Real = g ∘L ↑conjCLE) ∧
        g != 0 := by
  constructor
  · exact fun h => ⟨h.is_complex_or_conj_linear, h.ne_zero⟩
  · rintro ⟨⟨map, rfl⟩ | ⟨map, hmap⟩, h₂⟩
    · refine isConformalMap_complex_linear ?_
      contrapose h₂ with w
      simp only [w, restrictScalars_zero]
    · have minor₁ : g = map.restrictScalars Real ∘L ↑conjCLE := by
        ext1
        simp only [hmap, ContinuousLinearEquiv.coe_coe, comp_apply, conjCLE_apply,
          starRingEnd_self_apply]
      rw [minor₁] at h₂ ⊢
      refine isConformalMap_complex_linear_conj ?_
      contrapose h₂ with w
      simp only [w, restrictScalars_zero, zero_comp]

end ConformalIntoComplexPlane

/-! ### Conformality of real-differentiable complex maps -/

section Conformality
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Complex E] {z : Complex} {f : Complex -> E}

/--
theorem `DifferentiableAt.conformalAt` / 定理 `DifferentiableAt.conformalAt`

English:
theorem DifferentiableAt.conformalAt
  given: (h : DifferentiableAt Complex f z) (hf' : deriv f z != 0)
  proof: by
  rw [conformalAt_iff_isConformalMap_fderiv]; rw [(h.hasFDerivAt.restrictScalars Real).fderiv]
  apply isConformalMap_complex_linear
  simpa only [Ne, ContinuousLinearMap.ext_ring_iff]

中文:
定理 DifferentiableAt.conformalAt
  条件: (h : DifferentiableAt 复形 f z) (hf' : deriv f z != 0)
  证明: by
  rw [conformalAt_iff_isConformalMap_fderiv]; rw [(h.hasFDerivAt.restrictScalars Real).fderiv]
  apply isConformalMap_complex_linear
  simpa only [Ne, ContinuousLinearMap.ext_ring_iff]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.ext_ring_iff, conformalAt_iff_isConformalMap_fderiv, ext_ring_iff, fderiv, h.hasFDerivAt.restrictScalars, hasFDerivAt, isConformalMap_complex_linear, restrictScalars
-/
theorem DifferentiableAt.conformalAt (h : DifferentiableAt Complex f z) (hf' : deriv f z != 0) :
    ConformalAt f z := by
  rw [conformalAt_iff_isConformalMap_fderiv]; rw [(h.hasFDerivAt.restrictScalars Real).fderiv]
  apply isConformalMap_complex_linear
  simpa only [Ne, ContinuousLinearMap.ext_ring_iff]

/--
theorem `conformalAt_iff_differentiableAt_or_differentiableAt_comp_conj` / 定理 `conformalAt_iff_differentiableAt_or_differentiableAt_comp_conj`

English:
theorem conformalAt_iff_differentiableAt_or_differentiableAt_comp_conj
  given: {f : Complex -> Complex} {z : Complex}
  proof: by
  rw [conformalAt_iff_isConformalMap_fderiv]
  rw [isConformalMap_iff_is_complex_or_conj_linear]
  apply and_congr_left
  intro h
  have h_diff := h.imp_symm fderiv_zero_of_not_differentiableAt
  apply or_congr
  · rw [differentiableAt_iff_restrictScalars Real h_diff]
  rw [← conj_conj z] at h_diff
  rw [differentiableAt_iff_restrictScalars Real (h_diff.comp _ conjCLE.differentiableAt)]
  refine exists_congr fun g => rfl.congr ?_
  have : fderiv Real conj (conj z) = _ := conjCLE.fderiv
  simp [fderiv_comp _ h_diff conjCLE.differentiableAt, this]

中文:
定理 conformalAt_iff_differentiableAt_or_differentiableAt_comp_conj
  条件: {f : 复形 -> 复形} {z : 复形}
  证明: by
  rw [conformalAt_iff_isConformalMap_fderiv]
  rw [isConformalMap_iff_is_complex_or_conj_linear]
  apply and_congr_left
  intro h
  have h_diff := h.imp_symm fderiv_zero_of_not_differentiableAt
  apply or_congr
  · rw [differentiableAt_iff_restrictScalars Real h_diff]
  rw [← conj_conj z] at h_diff
  rw [differentiableAt_iff_restrictScalars Real (h_diff.comp _ conjCLE.differentiableAt)]
  refine exists_congr fun g => rfl.congr ?_
  have : fderiv Real conj (conj z) = _ := conjCLE.fderiv
  simp [fderiv_comp _ h_diff conjCLE.differentiableAt, this]

Depends on / 依赖: and_congr_left, conformalAt_iff_isConformalMap_fderiv, conjCLE, conjCLE.differentiableAt, conjCLE.fderiv, conj_conj, differentiableAt, differentiableAt_iff_restrictScalars, exists_congr, fderiv, fderiv_comp, fderiv_zero_of_not_differentiableAt, h.imp_symm, h_diff, h_diff.comp, imp_symm, isConformalMap_iff_is_complex_or_conj_linear, or_congr, rfl.congr
-/
theorem conformalAt_iff_differentiableAt_or_differentiableAt_comp_conj {f : Complex -> Complex} {z : Complex} :
    ConformalAt f z ↔
      (DifferentiableAt Complex f z ∨ DifferentiableAt Complex (f ∘ conj) (conj z)) ∧ fderiv Real f z != 0 := by
  rw [conformalAt_iff_isConformalMap_fderiv]
  rw [isConformalMap_iff_is_complex_or_conj_linear]
  apply and_congr_left
  intro h
  have h_diff := h.imp_symm fderiv_zero_of_not_differentiableAt
  apply or_congr
  · rw [differentiableAt_iff_restrictScalars Real h_diff]
  rw [← conj_conj z] at h_diff
  rw [differentiableAt_iff_restrictScalars Real (h_diff.comp _ conjCLE.differentiableAt)]
  refine exists_congr fun g => rfl.congr ?_
  have : fderiv Real conj (conj z) = _ := conjCLE.fderiv
  simp [fderiv_comp _ h_diff conjCLE.differentiableAt, this]

end Conformality

/-!
### The Cauchy-Riemann Equation for Complex-Differentiable Functions
-/

section CauchyRiemann

open Complex

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace Complex E]
  {f : Complex -> E} {x : Complex} {s : Set Complex}

/--
lemma `real_linearMap_map_smul_complex` / 引理 `real_linearMap_map_smul_complex`

English:
lemma real_linearMap_map_smul_complex
  given: {ℓ : Complex ->ₗ[Real] E} (h : ℓ I = I • ℓ 1) (a b : Complex)
  proof: by
  rw [← re_add_im a]; rw [← re_add_im b]; rw [← smul_eq_mul _ I]; rw [← smul_eq_mul _ I]
  have t₀ : ((a.im : Complex) • I) • (b.re : Complex) = (↑(a.im * b.re) : Complex) • I := by
    simp only [smul_eq_mul, ofReal_mul, ← mul_assoc, mul_comm _ I]
  have t₁ : ((a.im : Complex) • I) • (b.im : Complex) • I = (↑(- a.im * b.im) : Complex) • (1 : Complex) := by
    simp [mul_mul_mul_comm _ I]
  simp only [add_smul, smul_add, ℓ.map_add, t₀, t₁]
  repeat rw [Complex.coe_smul, ℓ.map_smul]
  have t₂ {r : Real} : ℓ (r : Complex) = r • ℓ (1 : Complex) := by simp [← ℓ.map_smul]
  simp only [t₂, h]
  match_scalars
  simp [mul_mul_mul_comm _ I]
  ring

中文:
引理 real_linearMap_map_smul_complex
  条件: {ℓ : 复形 ->ₗ[实数] E} (h : ℓ I = I • ℓ 1) (a b : 复形)
  证明: by
  rw [← re_add_im a]; rw [← re_add_im b]; rw [← smul_eq_mul _ I]; rw [← smul_eq_mul _ I]
  have t₀ : ((a.im : Complex) • I) • (b.re : Complex) = (↑(a.im * b.re) : Complex) • I := by
    simp only [smul_eq_mul, ofReal_mul, ← mul_assoc, mul_comm _ I]
  have t₁ : ((a.im : Complex) • I) • (b.im : Complex) • I = (↑(- a.im * b.im) : Complex) • (1 : Complex) := by
    simp [mul_mul_mul_comm _ I]
  simp only [add_smul, smul_add, ℓ.map_add, t₀, t₁]
  repeat rw [Complex.coe_smul, ℓ.map_smul]
  have t₂ {r : Real} : ℓ (r : Complex) = r • ℓ (1 : Complex) := by simp [← ℓ.map_smul]
  simp only [t₂, h]
  match_scalars
  simp [mul_mul_mul_comm _ I]
  ring

Depends on / 依赖: Complex.coe_smul, a.im, add_smul, b.im, b.re, coe_smul, map_add, map_smul, mul_assoc, mul_comm, mul_mul_mul_comm, ofReal_mul, re_add_im, repeat, smul_add, smul_eq_mul
-/
lemma real_linearMap_map_smul_complex {ℓ : Complex ->ₗ[Real] E} (h : ℓ I = I • ℓ 1) (a b : Complex) :
    ℓ (a • b) = a • ℓ b := by
  rw [← re_add_im a]; rw [← re_add_im b]; rw [← smul_eq_mul _ I]; rw [← smul_eq_mul _ I]
  have t₀ : ((a.im : Complex) • I) • (b.re : Complex) = (↑(a.im * b.re) : Complex) • I := by
    simp only [smul_eq_mul, ofReal_mul, ← mul_assoc, mul_comm _ I]
  have t₁ : ((a.im : Complex) • I) • (b.im : Complex) • I = (↑(- a.im * b.im) : Complex) • (1 : Complex) := by
    simp [mul_mul_mul_comm _ I]
  simp only [add_smul, smul_add, ℓ.map_add, t₀, t₁]
  repeat rw [Complex.coe_smul, ℓ.map_smul]
  have t₂ {r : Real} : ℓ (r : Complex) = r • ℓ (1 : Complex) := by simp [← ℓ.map_smul]
  simp only [t₂, h]
  match_scalars
  simp [mul_mul_mul_comm _ I]
  ring

/--
Definition of `LinearMap.complexOfReal` / `LinearMap.complexOfReal` 的定义

English:
definition LinearMap.complexOfReal
  signature: (ℓ : Complex ->ₗ[Real] E) (h : ℓ I = I • ℓ 1)
  body: ℓ
  map_smul' := real_linearMap_map_smul_complex h

@[simp]

中文:
定义 线性映射.complexOf实数
  签名: (ℓ : 复形 ->ₗ[实数] E) (h : ℓ I = I • ℓ 1)
  定义体: ℓ
  map_smul' := real_linearMap_map_smul_complex h

@[simp]
-/
def LinearMap.complexOfReal (ℓ : Complex ->ₗ[Real] E) (h : ℓ I = I • ℓ 1) : Complex ->ₗ[Complex] E where
  __ := ℓ
  map_smul' := real_linearMap_map_smul_complex h

@[simp]
/--
lemma `LinearMap.coe_complexOfReal` / 引理 `LinearMap.coe_complexOfReal`

English:
lemma LinearMap.coe_complexOfReal
  given: {ℓ : Complex ->ₗ[Real] E} (h)
  statement: ℓ.complexOfReal h = (ℓ : Complex -> E)
  proof: rfl

中文:
引理 线性映射.coe_complexOf实数
  条件: {ℓ : 复形 ->ₗ[实数] E} (h)
  结论: ℓ.complexOf实数 h = (ℓ : 复形 -> E)
  证明: rfl
-/
lemma LinearMap.coe_complexOfReal {ℓ : Complex ->ₗ[Real] E} (h) : ℓ.complexOfReal h = (ℓ : Complex -> E) := rfl

/--
Definition of `ContinuousLinearMap.complexOfReal` / `ContinuousLinearMap.complexOfReal` 的定义

English:
definition ContinuousLinearMap.complexOfReal
  signature: (ℓ : Complex ->L[Real] E) (h : ℓ I = I • ℓ 1)
  body: ℓ
  map_smul' := real_linearMap_map_smul_complex h

@[simp]

中文:
定义 连续线性映射.complexOf实数
  签名: (ℓ : 复形 ->L[实数] E) (h : ℓ I = I • ℓ 1)
  定义体: ℓ
  map_smul' := real_linearMap_map_smul_complex h

@[simp]
-/
def ContinuousLinearMap.complexOfReal (ℓ : Complex ->L[Real] E) (h : ℓ I = I • ℓ 1) : Complex ->L[Complex] E where
  __ := ℓ
  map_smul' := real_linearMap_map_smul_complex h

@[simp]
/--
lemma `ContinuousLinearMap.coe_complexOfReal` / 引理 `ContinuousLinearMap.coe_complexOfReal`

English:
lemma ContinuousLinearMap.coe_complexOfReal
  given: {ℓ : Complex ->L[Real] E} (h)
  statement: ℓ.complexOfReal h = (ℓ : Complex -> E)
  proof: rfl

中文:
引理 连续线性映射.coe_complexOf实数
  条件: {ℓ : 复形 ->L[实数] E} (h)
  结论: ℓ.complexOf实数 h = (ℓ : 复形 -> E)
  证明: rfl
-/
lemma ContinuousLinearMap.coe_complexOfReal {ℓ : Complex ->L[Real] E} (h) : ℓ.complexOfReal h = (ℓ : Complex -> E) :=
  rfl

/--
theorem `differentiableWithinAt_complex_iff_differentiableWithinAt_real` / 定理 `differentiableWithinAt_complex_iff_differentiableWithinAt_real`

English:
theorem differentiableWithinAt_complex_iff_differentiableWithinAt_real
  proof: by
  refine ⟨fun h => ⟨h.restrictScalars Real, ?_⟩, fun ⟨h₁, h₂⟩ => ?_⟩
  · simp only [← h.restrictScalars_fderivWithin Real hs, ContinuousLinearMap.coe_restrictScalars']
    rw [(by simp : I = I • 1)]; rw [(fderivWithin Complex f s x).map_smul]
    simp
  · apply (differentiableWithinAt_iff_restrictScalars Real h₁ hs).2
    use (fderivWithin Real f s x).complexOfReal h₂
    rfl

中文:
定理 differentiableWithinAt_complex_iff_differentiableWithinAt_real
  证明: by
  refine ⟨fun h => ⟨h.restrictScalars Real, ?_⟩, fun ⟨h₁, h₂⟩ => ?_⟩
  · simp only [← h.restrictScalars_fderivWithin Real hs, ContinuousLinearMap.coe_restrictScalars']
    rw [(by simp : I = I • 1)]; rw [(fderivWithin Complex f s x).map_smul]
    simp
  · apply (differentiableWithinAt_iff_restrictScalars Real h₁ hs).2
    use (fderivWithin Real f s x).complexOfReal h₂
    rfl

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.coe_restrictScalars, coe_restrictScalars, complexOfReal, differentiableWithinAt_iff_restrictScalars, fderivWithin, h.restrictScalars, h.restrictScalars_fderivWithin, map_smul, restrictScalars, restrictScalars_fderivWithin
-/
theorem differentiableWithinAt_complex_iff_differentiableWithinAt_real
    (hs : UniqueDiffWithinAt Real s x) :
    DifferentiableWithinAt Complex f s x ↔ DifferentiableWithinAt Real f s x ∧
      (fderivWithin Real f s x I = I • fderivWithin Real f s x 1) := by
  refine ⟨fun h => ⟨h.restrictScalars Real, ?_⟩, fun ⟨h₁, h₂⟩ => ?_⟩
  · simp only [← h.restrictScalars_fderivWithin Real hs, ContinuousLinearMap.coe_restrictScalars']
    rw [(by simp : I = I • 1)]; rw [(fderivWithin Complex f s x).map_smul]
    simp
  · apply (differentiableWithinAt_iff_restrictScalars Real h₁ hs).2
    use (fderivWithin Real f s x).complexOfReal h₂
    rfl

/--
theorem `HasFDerivWithinAt.complexOfReal` / 定理 `HasFDerivWithinAt.complexOfReal`

English:
theorem HasFDerivWithinAt.complexOfReal
  statement: {f' : Complex ->L[Real] E} (h₁ : HasFDerivWithinAt f f' s x)
  proof: .of_restrictScalars Real h₁ rfl

中文:
定理 HasFDerivWithinAt.complexOf实数
  结论: {f' : 复形 ->L[实数] E} (h₁ : HasFDerivWithinAt f f' s x)
  证明: .of_restrictScalars Real h₁ rfl
-/
protected theorem HasFDerivWithinAt.complexOfReal {f' : Complex ->L[Real] E} (h₁ : HasFDerivWithinAt f f' s x)
    (h₂ : f' I = I • f' 1) :
    HasFDerivWithinAt f (f'.complexOfReal h₂) s x :=
  .of_restrictScalars Real h₁ rfl

/--
theorem `complexOfReal_fderivWithin` / 定理 `complexOfReal_fderivWithin`

English:
theorem complexOfReal_fderivWithin
  statement: (h₁ : DifferentiableWithinAt Real f s x)
  proof: by
  have := ((differentiableWithinAt_complex_iff_differentiableWithinAt_real hs).2
      ⟨h₁, h₂⟩).restrictScalars_fderivWithin Real hs
  simpa [DFunLike.ext_iff]

中文:
定理 complexOf实数_fderivWithin
  结论: (h₁ : DifferentiableWithinAt 实数 f s x)
  证明: by
  have := ((differentiableWithinAt_complex_iff_differentiableWithinAt_real hs).2
      ⟨h₁, h₂⟩).restrictScalars_fderivWithin Real hs
  simpa [DFunLike.ext_iff]

Depends on / 依赖: DFunLike, DFunLike.ext_iff, differentiableWithinAt_complex_iff_differentiableWithinAt_real, ext_iff, restrictScalars_fderivWithin
-/
theorem complexOfReal_fderivWithin (h₁ : DifferentiableWithinAt Real f s x)
    (h₂ : fderivWithin Real f s x I = I • fderivWithin Real f s x 1) (hs : UniqueDiffWithinAt Real s x) :
    fderivWithin Complex f s x = (fderivWithin Real f s x).complexOfReal h₂ := by
  have := ((differentiableWithinAt_complex_iff_differentiableWithinAt_real hs).2
      ⟨h₁, h₂⟩).restrictScalars_fderivWithin Real hs
  simpa [DFunLike.ext_iff]

/--
theorem `complexOfReal_hasDerivWithinAt` / 定理 `complexOfReal_hasDerivWithinAt`

English:
theorem complexOfReal_hasDerivWithinAt
  statement: (h₁ : DifferentiableWithinAt Real f s x)
  proof: by
  rw [hasDerivWithinAt_iff_hasFDerivWithinAt]; rw [toSpanSingleton_apply_map_one]
  exact h₁.hasFDerivWithinAt.complexOfReal h₂

中文:
定理 complexOf实数_hasDerivWithinAt
  结论: (h₁ : DifferentiableWithinAt 实数 f s x)
  证明: by
  rw [hasDerivWithinAt_iff_hasFDerivWithinAt]; rw [toSpanSingleton_apply_map_one]
  exact h₁.hasFDerivWithinAt.complexOfReal h₂

Depends on / 依赖: complexOfReal, hasDerivWithinAt_iff_hasFDerivWithinAt, hasFDerivWithinAt, hasFDerivWithinAt.complexOfReal, toSpanSingleton_apply_map_one
-/
theorem complexOfReal_hasDerivWithinAt (h₁ : DifferentiableWithinAt Real f s x)
    (h₂ : fderivWithin Real f s x I = I • fderivWithin Real f s x 1) :
    HasDerivWithinAt f ((fderivWithin Real f s x).complexOfReal h₂ 1) s x := by
  rw [hasDerivWithinAt_iff_hasFDerivWithinAt]; rw [toSpanSingleton_apply_map_one]
  exact h₁.hasFDerivWithinAt.complexOfReal h₂

/--
theorem `complexOfReal_derivWithin` / 定理 `complexOfReal_derivWithin`

English:
theorem complexOfReal_derivWithin
  statement: (h₁ : DifferentiableWithinAt Real f s x)
  proof: HasDerivWithinAt.derivWithin (complexOfReal_hasDerivWithinAt h₁ h₂) hs

中文:
定理 complexOf实数_derivWithin
  结论: (h₁ : DifferentiableWithinAt 实数 f s x)
  证明: HasDerivWithinAt.derivWithin (complexOfReal_hasDerivWithinAt h₁ h₂) hs

Depends on / 依赖: HasDerivWithinAt, HasDerivWithinAt.derivWithin, complexOfReal_hasDerivWithinAt, derivWithin
-/
theorem complexOfReal_derivWithin (h₁ : DifferentiableWithinAt Real f s x)
    (h₂ : fderivWithin Real f s x I = I • fderivWithin Real f s x 1) (hs : UniqueDiffWithinAt Complex s x) :
    derivWithin f s x = fderivWithin Real f s x 1 :=
  HasDerivWithinAt.derivWithin (complexOfReal_hasDerivWithinAt h₁ h₂) hs

/--
theorem `differentiableAt_complex_iff_differentiableAt_real` / 定理 `differentiableAt_complex_iff_differentiableAt_real`

English:
theorem differentiableAt_complex_iff_differentiableAt_real
  proof: ⟨fun h => by simp [h.restrictScalars Real, h.fderiv_restrictScalars Real],
    fun ⟨h₁, h₂⟩ => (differentiableAt_iff_restrictScalars Real h₁).2
    ⟨(fderiv Real f x).complexOfReal h₂, rfl⟩⟩

中文:
定理 differentiableAt_complex_iff_differentiableAt_real
  证明: ⟨fun h => by simp [h.restrictScalars Real, h.fderiv_restrictScalars Real],
    fun ⟨h₁, h₂⟩ => (differentiableAt_iff_restrictScalars Real h₁).2
    ⟨(fderiv Real f x).complexOfReal h₂, rfl⟩⟩

Depends on / 依赖: complexOfReal, differentiableAt_iff_restrictScalars, fderiv, fderiv_restrictScalars, h.fderiv_restrictScalars, h.restrictScalars, restrictScalars
-/
theorem differentiableAt_complex_iff_differentiableAt_real :
    DifferentiableAt Complex f x ↔ DifferentiableAt Real f x ∧
      fderiv Real f x I = I • fderiv Real f x 1 :=
  ⟨fun h => by simp [h.restrictScalars Real, h.fderiv_restrictScalars Real],
    fun ⟨h₁, h₂⟩ => (differentiableAt_iff_restrictScalars Real h₁).2
    ⟨(fderiv Real f x).complexOfReal h₂, rfl⟩⟩

/--
theorem `HasFDerivAt.complexOfReal_hasFDerivAt` / 定理 `HasFDerivAt.complexOfReal_hasFDerivAt`

English:
theorem HasFDerivAt.complexOfReal_hasFDerivAt
  statement: {f' : Complex ->L[Real] E}
  proof: hasFDerivAt_of_restrictScalars Real h₁ rfl

中文:
定理 在点处Fréchet可导.complexOf实数_hasFDerivAt
  结论: {f' : 复形 ->L[实数] E}
  证明: hasFDerivAt_of_restrictScalars Real h₁ rfl
-/
protected theorem HasFDerivAt.complexOfReal_hasFDerivAt {f' : Complex ->L[Real] E}
    (h₁ : HasFDerivAt f f' x) (h₂ : f' I = I • f' 1) :
    HasFDerivAt f (f'.complexOfReal h₂) x :=
  hasFDerivAt_of_restrictScalars Real h₁ rfl

/--
theorem `complexOfReal_hasDerivAt` / 定理 `complexOfReal_hasDerivAt`

English:
theorem complexOfReal_hasDerivAt
  statement: (h₁ : DifferentiableAt Real f x)
  proof: by
  rw [hasDerivAt_iff_hasFDerivAt]; rw [toSpanSingleton_apply_map_one]
  exact hasFDerivAt_of_restrictScalars Real h₁.hasFDerivAt rfl

中文:
定理 complexOf实数_hasDerivAt
  结论: (h₁ : DifferentiableAt 实数 f x)
  证明: by
  rw [hasDerivAt_iff_hasFDerivAt]; rw [toSpanSingleton_apply_map_one]
  exact hasFDerivAt_of_restrictScalars Real h₁.hasFDerivAt rfl

Depends on / 依赖: hasDerivAt_iff_hasFDerivAt, hasFDerivAt, hasFDerivAt_of_restrictScalars, toSpanSingleton_apply_map_one
-/
theorem complexOfReal_hasDerivAt (h₁ : DifferentiableAt Real f x)
    (h₂ : fderiv Real f x I = I • fderiv Real f x 1) :
    HasDerivAt f ((fderiv Real f x).complexOfReal h₂ 1) x := by
  rw [hasDerivAt_iff_hasFDerivAt]; rw [toSpanSingleton_apply_map_one]
  exact hasFDerivAt_of_restrictScalars Real h₁.hasFDerivAt rfl

/--
theorem `complexOfReal_deriv` / 定理 `complexOfReal_deriv`

English:
theorem complexOfReal_deriv
  statement: (h₁ : DifferentiableAt Real f x)
  proof: HasDerivAt.deriv (complexOfReal_hasDerivAt h₁ h₂)

中文:
定理 complexOf实数_deriv
  结论: (h₁ : DifferentiableAt 实数 f x)
  证明: HasDerivAt.deriv (complexOfReal_hasDerivAt h₁ h₂)

Depends on / 依赖: HasDerivAt, HasDerivAt.deriv, complexOfReal_hasDerivAt
-/
theorem complexOfReal_deriv (h₁ : DifferentiableAt Real f x)
    (h₂ : fderiv Real f x I = I • fderiv Real f x 1) :
    deriv f x = fderiv Real f x 1 :=
  HasDerivAt.deriv (complexOfReal_hasDerivAt h₁ h₂)

/--
theorem `complexOfReal_fderiv` / 定理 `complexOfReal_fderiv`

English:
theorem complexOfReal_fderiv
  statement: (h₁ : DifferentiableAt Real f x)
  proof: (h₁.hasFDerivAt.complexOfReal_hasFDerivAt h₂).fderiv.symm

中文:
定理 complexOf实数_fderiv
  结论: (h₁ : DifferentiableAt 实数 f x)
  证明: (h₁.hasFDerivAt.complexOfReal_hasFDerivAt h₂).fderiv.symm

Depends on / 依赖: complexOfReal_hasFDerivAt, fderiv, fderiv.symm, hasFDerivAt, hasFDerivAt.complexOfReal_hasFDerivAt
-/
theorem complexOfReal_fderiv (h₁ : DifferentiableAt Real f x)
    (h₂ : fderiv Real f x I = I • fderiv Real f x 1) :
    (fderiv Real f x).complexOfReal h₂ = fderiv Complex f x :=
  (h₁.hasFDerivAt.complexOfReal_hasFDerivAt h₂).fderiv.symm

end CauchyRiemann
