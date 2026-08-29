/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-! # Properties of C⋆-algebra homomorphisms

Here we collect properties of C⋆-algebra homomorphisms.

## Main declarations

+ `NonUnitalStarAlgHom.norm_map`: A non-unital star algebra monomorphism of complex C⋆-algebras
  is isometric.
-/

public section

open CStarAlgebra in
/--
lemma `IsSelfAdjoint.map_spectrum_real` / 引理 `IsSelfAdjoint.map_spectrum_real`

English:
lemma IsSelfAdjoint.map_spectrum_real
  statement: {F A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
  proof: by
  have h_spec := AlgHom.spectrum_apply_subset ((φ : A ->⋆ₐ[Complex] B).restrictScalars Real) a
  refine Set.eq_of_subset_of_subset h_spec fun x hx => ?_
  /- we prove the reverse inclusion by contradiction, so assume that `x ∈ spectrum ℝ a`, but
  `x ∉ spectrum ℝ (φ a)`. Then by Urysohn's lemma w

中文:
引理 IsSelfAdjoint.map_spectrum_real
  结论: {F A B : 类型} [CStar代数 A] [CStar代数 B]
  证明: by
  have h_spec := AlgHom.spectrum_apply_subset ((φ : A ->⋆ₐ[Complex] B).restrictScalars Real) a
  refine Set.eq_of_subset_of_subset h_spec fun x hx => ?_
  /- we prove the reverse inclusion by contradiction, so assume that `x ∈ spectrum ℝ a`, but
  `x ∉ spectrum ℝ (φ a)`. Then by Urysohn's lemma w

Depends on / 依赖: AlgHom, AlgHom.spectrum_apply_subset, Set.eq_of_subset_of_subset, eq_of_subset_of_subset, h_spec, restrictScalars, spectrum_apply_subset
-/
lemma IsSelfAdjoint.map_spectrum_real {F A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    [FunLike F A B] [AlgHomClass F Complex A B] [StarHomClass F A B]
    {a : A} (ha : IsSelfAdjoint a) (φ : F) (hφ : Function.Injective φ) :
    spectrum Real (φ a) = spectrum Real a := by
  have h_spec := AlgHom.spectrum_apply_subset ((φ : A ->⋆ₐ[Complex] B).restrictScalars Real) a
  refine Set.eq_of_subset_of_subset h_spec fun x hx => ?_
  /- we prove the reverse inclusion by contradiction, so assume that `x ∈ spectrum ℝ a`, but
  `x ∉ spectrum ℝ (φ a)`. Then by Urysohn's lemma we can get a function for which `f x = 1`, but
  `f = 0` on `spectrum ℝ a`. -/
  by_contra hx'
  obtain ⟨f, h_eqOn, h_eqOn_x, -⟩ := exists_continuous_zero_one_of_isClosed
(spectrum.isClosed (𝕜 := Real) (φ a)) (isClosed_singleton (x := x)) by simpa
  /- it suffices to show that `φ (f a) = 0`, for if so, then `f a = 0` by injectivity of `φ`, and
  hence `f = 0` on `spectrum ℝ a`, contradicting the fact that `f x = 1`. -/
  suffices φ (cfc f a) = 0 by
    rw [map_eq_zero_iff φ hφ]; rw [← cfc_zero Real a]; rw [cfc_eq_cfc_iff_eqOn] at this
exact zero_ne_one calc
      0 = f x := (this hx).symm
_ = 1 := h_eqOn_x Set.mem_singleton x
  /- Finally, `φ (f a) = f (φ a) = 0`, where the last equality follows since `f = 0` on
  `spectrum ℝ (φ a)`. -/
  calc φ (cfc f a) = cfc f (φ a) := StarAlgHomClass.map_cfc φ f a
    _ = cfc (0 : Real -> Real) (φ a) := cfc_congr h_eqOn
    _ = 0 := by simp

namespace NonUnitalStarAlgHom

variable {F A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
variable [FunLike F A B] [NonUnitalAlgHomClass F Complex A B] [StarHomClass F A B]

open CStarAlgebra Unitization in
/--
lemma `norm_map` / 引理 `norm_map`

English:
lemma norm_map
  given: (φ : F) (hφ : Function.Injective φ) (a : A)
  statement: ‖φ a‖ = ‖a‖
  proof: by
  /- Since passing to the unitization is functorial, and it is an isometric embedding, we may assume
  that `φ` is a unital star algebra monomorphism and that `A` and `B` are unital C⋆-algebras. -/
  suffices forall {ψ : Unitization Complex A ->⋆ₐ[Complex] Unitization Complex B} (_ : Function.Inj

中文:
引理 norm_map
  条件: (φ : F) (hφ : 函数.单射 φ) (a : A)
  结论: ‖φ a‖ = ‖a‖
  证明: by
  /- Since passing to the unitization is functorial, and it is an isometric embedding, we may assume
  that `φ` is a unital star algebra monomorphism and that `A` and `B` are unital C⋆-algebras. -/
  suffices forall {ψ : Unitization Complex A ->⋆ₐ[Complex] Unitization Complex B} (_ : Function.Inj
-/
lemma norm_map (φ : F) (hφ : Function.Injective φ) (a : A) : ‖φ a‖ = ‖a‖ := by
  /- Since passing to the unitization is functorial, and it is an isometric embedding, we may assume
  that `φ` is a unital star algebra monomorphism and that `A` and `B` are unital C⋆-algebras. -/
  suffices forall {ψ : Unitization Complex A ->⋆ₐ[Complex] Unitization Complex B} (_ : Function.Injective ψ)
      (a : Unitization Complex A), ‖ψ a‖ = ‖a‖ by
    simpa [norm_inr] using this (starMap_injective (φ := (φ : A ->⋆ₙₐ[Complex] B)) hφ) a
  intro ψ hψ a
  -- to show `‖ψ a‖ = ‖a‖`, by the C⋆-property it suffices to show `‖ψ (star a * a)‖ = ‖star a * a‖`
  rw [← sq_eq_sq₀ (by positivity) (by positivity)]
  simp only [sq, ← CStarRing.norm_star_mul_self, ← map_star, ← map_mul]
  /- since `star a * a` is selfadjoint, it has the same `ℝ`-spectrum as `ψ (star a * a)`.
  Since the spectral radius over `ℝ` coincides with the norm, `‖ψ (star a * a)‖ = ‖star a * a‖`. -/
  have ha : IsSelfAdjoint (star a * a) := .star_mul_self a
  calc ‖ψ (star a * a)‖ = (spectralRadius Real (ψ (star a * a))).toReal :=
.toReal_spectralRadius_eq_norm.symm ha.map ψ
    _ = (spectralRadius Real (star a * a)).toReal := by
      simp only [spectralRadius, ha.map_spectrum_real ψ hψ]
    _ = ‖star a * a‖ := ha.toReal_spectralRadius_eq_norm

/--
lemma `nnnorm_map` / 引理 `nnnorm_map`

English:
lemma nnnorm_map
  given: (φ : F) (hφ : Function.Injective φ) (a : A)
  statement: ‖φ a‖₊ = ‖a‖₊
  proof: Subtype.ext norm_map φ hφ a

中文:
引理 nnnorm_map
  条件: (φ : F) (hφ : 函数.单射 φ) (a : A)
  结论: ‖φ a‖₊ = ‖a‖₊
  证明: Subtype.ext norm_map φ hφ a

Depends on / 依赖: Subtype, Subtype.ext, norm_map
-/
lemma nnnorm_map (φ : F) (hφ : Function.Injective φ) (a : A) : ‖φ a‖₊ = ‖a‖₊ :=
Subtype.ext norm_map φ hφ a

/--
lemma `isometry` / 引理 `isometry`

English:
lemma isometry
  given: (φ : F) (hφ : Function.Injective φ)
  statement: Isometry φ
  proof: AddMonoidHomClass.isometry_of_norm φ (norm_map φ hφ)

中文:
引理 isometry
  条件: (φ : F) (hφ : 函数.单射 φ)
  结论: 等距 φ
  证明: AddMonoidHomClass.isometry_of_norm φ (norm_map φ hφ)

Depends on / 依赖: AddMonoidHomClass, AddMonoidHomClass.isometry_of_norm, isometry_of_norm, norm_map
-/
lemma isometry (φ : F) (hφ : Function.Injective φ) : Isometry φ :=
  AddMonoidHomClass.isometry_of_norm φ (norm_map φ hφ)

end NonUnitalStarAlgHom
