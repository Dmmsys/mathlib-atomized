/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.MDifferentiable
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform

/-!
# Derivatives of modular forms

This file defines normalized derivative $D = \frac{1}{2\pi i} \frac{d}{dz}$
and (Ramanujan-)Serre derivative $\partial_k := D - \frac{k}{12} E_2$ of modular forms.

## Main Definitions and Theorems

- `normalizedDerivOfComplex`: $D = \frac{1}{2\pi i} \frac{d}{dz}$
- `serreDerivative`: $\partial_k F := D F - \frac{k}{12} E_2 F$
- `serreDerivative_slash_equivariant`: Serre derivative is equivariant under the slash action.

TODO:
- Serre derivative preserves modularity, i.e. $\partial_k (M_k) \subseteq M_{k+2}$.
- Use above, prove Ramanujan's identities. See [here](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean/blob/main/SpherePacking/ModularForms/RamanujanIdentities.lean)
  for `sorry`-free proofs.
-/

open UpperHalfPlane hiding I
open Real Complex
open scoped Manifold MatrixGroups ModularForm Topology

namespace Derivative

@[expose] public noncomputable section

/--
Definition of `normalizedDerivOfComplex` / `normalizedDerivOfComplex` 的定义

English:
definition normalizedDerivOfComplex
  signature: (F : ℍ -> Complex) (z : ℍ)
  body: (2 * π * I)⁻¹ * deriv (F ∘ ofComplex) z

中文:
定义 normalizedDerivOfComplex
  签名: (F : ℍ -> 复形) (z : ℍ)
  定义体: (2 * π * I)⁻¹ * deriv (F ∘ ofComplex) z

Depends on / 依赖: ofComplex
-/
def normalizedDerivOfComplex (F : ℍ -> Complex) (z : ℍ) : Complex := (2 * π * I)⁻¹ * deriv (F ∘ ofComplex) z

/-- We denote the normalized derivative by `D`. -/
scoped notation "D" => normalizedDerivOfComplex

/--
theorem `normalizedDerivOfComplex_mdifferentiable` / 定理 `normalizedDerivOfComplex_mdifferentiable`

English:
theorem normalizedDerivOfComplex_mdifferentiable
  given: {F : ℍ -> Complex} (hF : MDiff F)
  statement: MDiff (D F)
  proof: by
  rw [UpperHalfPlane.mdifferentiable_iff] at hF ⊢
  let c : Complex := (2 * π * I)⁻¹
  have hDeriv : DifferentiableOn Complex (fun z => c * deriv (F ∘ ofComplex) z) upperHalfPlaneSet := by
    simpa [c] using (hF.deriv isOpen_upperHalfPlaneSet).const_mul ((2 * π * I)⁻¹)
  refine hDeriv.congr ?_
 

中文:
定理 normalizedDerivOfComplex_mdifferentiable
  条件: {F : ℍ -> 复形} (hF : MDiff F)
  结论: MDiff (D F)
  证明: by
  rw [UpperHalfPlane.mdifferentiable_iff] at hF ⊢
  let c : Complex := (2 * π * I)⁻¹
  have hDeriv : DifferentiableOn Complex (fun z => c * deriv (F ∘ ofComplex) z) upperHalfPlaneSet := by
    simpa [c] using (hF.deriv isOpen_upperHalfPlaneSet).const_mul ((2 * π * I)⁻¹)
  refine hDeriv.congr ?_
 

Depends on / 依赖: DifferentiableOn, Function, Function.comp_apply, UpperHalfPlane, UpperHalfPlane.mdifferentiable_iff, comp_apply, const_mul, hDeriv, hDeriv.congr, hF.deriv, isOpen_upperHalfPlaneSet, mdifferentiable_iff, normalizedDerivOfComplex, ofComplex, ofComplex_apply_of_im_pos, upperHalfPlaneSet
-/
theorem normalizedDerivOfComplex_mdifferentiable {F : ℍ -> Complex} (hF : MDiff F) : MDiff (D F) := by
  rw [UpperHalfPlane.mdifferentiable_iff] at hF ⊢
  let c : Complex := (2 * π * I)⁻¹
  have hDeriv : DifferentiableOn Complex (fun z => c * deriv (F ∘ ofComplex) z) upperHalfPlaneSet := by
    simpa [c] using (hF.deriv isOpen_upperHalfPlaneSet).const_mul ((2 * π * I)⁻¹)
  refine hDeriv.congr ?_
  intro z hz
  simp [normalizedDerivOfComplex, c, Function.comp_apply, ofComplex_apply_of_im_pos hz]

/-!
Basic properties of normalized derivative.
-/
@[simp]
/--
theorem `normalizedDerivOfComplex_add` / 定理 `normalizedDerivOfComplex_add`

English:
theorem normalizedDerivOfComplex_add
  given: (F G : ℍ -> Complex) (hF : MDiff F) (hG : MDiff G)
  proof: by
  ext z
  have hFz := UpperHalfPlane.mdifferentiableAt_iff.mp (hF z)
  have hGz := UpperHalfPlane.mdifferentiableAt_iff.mp (hG z)
  simp only [normalizedDerivOfComplex, Pi.add_apply]
  rw [show (F + G) ∘ ofComplex = F ∘ ofComplex + G ∘ ofComplex from rfl]; rw [deriv_add hFz hGz]; rw [mul_add]

@[

中文:
定理 normalizedDerivOfComplex_add
  条件: (F G : ℍ -> 复形) (hF : MDiff F) (hG : MDiff G)
  证明: by
  ext z
  have hFz := UpperHalfPlane.mdifferentiableAt_iff.mp (hF z)
  have hGz := UpperHalfPlane.mdifferentiableAt_iff.mp (hG z)
  simp only [normalizedDerivOfComplex, Pi.add_apply]
  rw [show (F + G) ∘ ofComplex = F ∘ ofComplex + G ∘ ofComplex from rfl]; rw [deriv_add hFz hGz]; rw [mul_add]

@[

Depends on / 依赖: Pi.add_apply, UpperHalfPlane, UpperHalfPlane.mdifferentiableAt_iff.mp, add_apply, deriv_add, mdifferentiableAt_iff, mul_add, normalizedDerivOfComplex, ofComplex
-/
theorem normalizedDerivOfComplex_add (F G : ℍ -> Complex) (hF : MDiff F) (hG : MDiff G) :
    D (F + G) = D F + D G := by
  ext z
  have hFz := UpperHalfPlane.mdifferentiableAt_iff.mp (hF z)
  have hGz := UpperHalfPlane.mdifferentiableAt_iff.mp (hG z)
  simp only [normalizedDerivOfComplex, Pi.add_apply]
  rw [show (F + G) ∘ ofComplex = F ∘ ofComplex + G ∘ ofComplex from rfl]; rw [deriv_add hFz hGz]; rw [mul_add]

@[simp]
/--
theorem `normalizedDerivOfComplex_sub` / 定理 `normalizedDerivOfComplex_sub`

English:
theorem normalizedDerivOfComplex_sub
  given: (F G : ℍ -> Complex) (hF : MDiff F) (hG : MDiff G)
  proof: by
  ext z
  have hFz := UpperHalfPlane.mdifferentiableAt_iff.mp (hF z)
  have hGz := UpperHalfPlane.mdifferentiableAt_iff.mp (hG z)
  simp only [normalizedDerivOfComplex, Pi.sub_apply]
  rw [show (F - G) ∘ ofComplex = F ∘ ofComplex - G ∘ ofComplex from rfl]; rw [deriv_sub hFz hGz]; rw [mul_sub]

@[

中文:
定理 normalizedDerivOfComplex_sub
  条件: (F G : ℍ -> 复形) (hF : MDiff F) (hG : MDiff G)
  证明: by
  ext z
  have hFz := UpperHalfPlane.mdifferentiableAt_iff.mp (hF z)
  have hGz := UpperHalfPlane.mdifferentiableAt_iff.mp (hG z)
  simp only [normalizedDerivOfComplex, Pi.sub_apply]
  rw [show (F - G) ∘ ofComplex = F ∘ ofComplex - G ∘ ofComplex from rfl]; rw [deriv_sub hFz hGz]; rw [mul_sub]

@[

Depends on / 依赖: Pi.sub_apply, UpperHalfPlane, UpperHalfPlane.mdifferentiableAt_iff.mp, deriv_sub, mdifferentiableAt_iff, mul_sub, normalizedDerivOfComplex, ofComplex, sub_apply
-/
theorem normalizedDerivOfComplex_sub (F G : ℍ -> Complex) (hF : MDiff F) (hG : MDiff G) :
    D (F - G) = D F - D G := by
  ext z
  have hFz := UpperHalfPlane.mdifferentiableAt_iff.mp (hF z)
  have hGz := UpperHalfPlane.mdifferentiableAt_iff.mp (hG z)
  simp only [normalizedDerivOfComplex, Pi.sub_apply]
  rw [show (F - G) ∘ ofComplex = F ∘ ofComplex - G ∘ ofComplex from rfl]; rw [deriv_sub hFz hGz]; rw [mul_sub]

@[simp]
/--
theorem `normalizedDerivOfComplex_const` / 定理 `normalizedDerivOfComplex_const`

English:
theorem normalizedDerivOfComplex_const
  given: (c : Complex)
  statement: D (fun _ => c) = 0
  proof: by
  ext z
  change (2 * π * I)⁻¹ * deriv (fun _ : Complex => c) (z : Complex) = 0
  simp [deriv_const]

@[simp]

中文:
定理 normalizedDerivOfComplex_const
  条件: (c : 复形)
  结论: D (fun _ => c) = 0
  证明: by
  ext z
  change (2 * π * I)⁻¹ * deriv (fun _ : Complex => c) (z : Complex) = 0
  simp [deriv_const]

@[simp]

Depends on / 依赖: deriv_const
-/
theorem normalizedDerivOfComplex_const (c : Complex) : D (fun _ => c) = 0 := by
  ext z
  change (2 * π * I)⁻¹ * deriv (fun _ : Complex => c) (z : Complex) = 0
  simp [deriv_const]

@[simp]
/--
theorem `normalizedDerivOfComplex_smul` / 定理 `normalizedDerivOfComplex_smul`

English:
theorem normalizedDerivOfComplex_smul
  given: (c : Complex) (F : ℍ -> Complex) (hF : MDiff F)
  statement: D (c • F) = c • D F
  proof: by
  ext z
  have hFz := UpperHalfPlane.mdifferentiableAt_iff.mp (hF z)
  simp only [normalizedDerivOfComplex, Pi.smul_apply, smul_eq_mul]
  rw [show (c • F) ∘ ofComplex = c • (F ∘ ofComplex) from rfl]; rw [deriv_const_smul c hFz]; rw [smul_eq_mul]
  ring

@[simp]

中文:
定理 normalizedDerivOfComplex_smul
  条件: (c : 复形) (F : ℍ -> 复形) (hF : MDiff F)
  结论: D (c • F) = c • D F
  证明: by
  ext z
  have hFz := UpperHalfPlane.mdifferentiableAt_iff.mp (hF z)
  simp only [normalizedDerivOfComplex, Pi.smul_apply, smul_eq_mul]
  rw [show (c • F) ∘ ofComplex = c • (F ∘ ofComplex) from rfl]; rw [deriv_const_smul c hFz]; rw [smul_eq_mul]
  ring

@[simp]

Depends on / 依赖: Pi.smul_apply, UpperHalfPlane, UpperHalfPlane.mdifferentiableAt_iff.mp, deriv_const_smul, mdifferentiableAt_iff, normalizedDerivOfComplex, ofComplex, smul_apply, smul_eq_mul
-/
theorem normalizedDerivOfComplex_smul (c : Complex) (F : ℍ -> Complex) (hF : MDiff F) : D (c • F) = c • D F := by
  ext z
  have hFz := UpperHalfPlane.mdifferentiableAt_iff.mp (hF z)
  simp only [normalizedDerivOfComplex, Pi.smul_apply, smul_eq_mul]
  rw [show (c • F) ∘ ofComplex = c • (F ∘ ofComplex) from rfl]; rw [deriv_const_smul c hFz]; rw [smul_eq_mul]
  ring

@[simp]
/--
theorem `normalizedDerivOfComplex_neg` / 定理 `normalizedDerivOfComplex_neg`

English:
theorem normalizedDerivOfComplex_neg
  given: (F : ℍ -> Complex) (hF : MDiff F)
  statement: D (-F) = -D F
  proof: by
  have : -F = (-1 : Complex) • F := by ext; simp
  rw [this]; rw [normalizedDerivOfComplex_smul _ _ hF]
  ext
  simp

@[simp]

中文:
定理 normalizedDerivOfComplex_neg
  条件: (F : ℍ -> 复形) (hF : MDiff F)
  结论: D (-F) = -D F
  证明: by
  have : -F = (-1 : Complex) • F := by ext; simp
  rw [this]; rw [normalizedDerivOfComplex_smul _ _ hF]
  ext
  simp

@[simp]

Depends on / 依赖: normalizedDerivOfComplex_smul
-/
theorem normalizedDerivOfComplex_neg (F : ℍ -> Complex) (hF : MDiff F) : D (-F) = -D F := by
  have : -F = (-1 : Complex) • F := by ext; simp
  rw [this]; rw [normalizedDerivOfComplex_smul _ _ hF]
  ext
  simp

@[simp]
/--
theorem `normalizedDerivOfComplex_mul` / 定理 `normalizedDerivOfComplex_mul`

English:
theorem normalizedDerivOfComplex_mul
  given: (F G : ℍ -> Complex) (hF : MDiff F) (hG : MDiff G)
  proof: by
  ext z
  have hFz := UpperHalfPlane.mdifferentiableAt_iff.mp (hF z)
  have hGz := UpperHalfPlane.mdifferentiableAt_iff.mp (hG z)
  simp only [normalizedDerivOfComplex, Pi.add_apply, Pi.mul_apply]
  rw [show (F * G) ∘ ofComplex = (F ∘ ofComplex) * (G ∘ ofComplex) from rfl]; rw [deriv_mul hFz hGz]

中文:
定理 normalizedDerivOfComplex_mul
  条件: (F G : ℍ -> 复形) (hF : MDiff F) (hG : MDiff G)
  证明: by
  ext z
  have hFz := UpperHalfPlane.mdifferentiableAt_iff.mp (hF z)
  have hGz := UpperHalfPlane.mdifferentiableAt_iff.mp (hG z)
  simp only [normalizedDerivOfComplex, Pi.add_apply, Pi.mul_apply]
  rw [show (F * G) ∘ ofComplex = (F ∘ ofComplex) * (G ∘ ofComplex) from rfl]; rw [deriv_mul hFz hGz]

Depends on / 依赖: Function, Function.comp_apply, Pi.add_apply, Pi.mul_apply, UpperHalfPlane, UpperHalfPlane.mdifferentiableAt_iff.mp, add_apply, comp_apply, deriv_mul, mdifferentiableAt_iff, mul_apply, normalizedDerivOfComplex, ofComplex, ofComplex_apply
-/
theorem normalizedDerivOfComplex_mul (F G : ℍ -> Complex) (hF : MDiff F) (hG : MDiff G) :
    D (F * G) = D F * G + F * D G := by
  ext z
  have hFz := UpperHalfPlane.mdifferentiableAt_iff.mp (hF z)
  have hGz := UpperHalfPlane.mdifferentiableAt_iff.mp (hG z)
  simp only [normalizedDerivOfComplex, Pi.add_apply, Pi.mul_apply]
  rw [show (F * G) ∘ ofComplex = (F ∘ ofComplex) * (G ∘ ofComplex) from rfl]; rw [deriv_mul hFz hGz]
  simp [Function.comp_apply, ofComplex_apply]
  ring

@[simp]
/--
theorem `normalizedDerivOfComplex_pow` / 定理 `normalizedDerivOfComplex_pow`

English:
theorem normalizedDerivOfComplex_pow
  given: (F : ℍ -> Complex) (n : Nat) (hF : MDiff F)
  proof: by
  ext z
  have hFz := UpperHalfPlane.mdifferentiableAt_iff.mp (hF z)
  simp only [normalizedDerivOfComplex, Pi.mul_apply, Pi.pow_apply]
  rw [show (F ^ n) ∘ ofComplex = (F ∘ ofComplex) ^ n from rfl]; rw [deriv_pow hFz n]
  simp [Function.comp_apply, ofComplex_apply]
  ring

中文:
定理 normalizedDerivOfComplex_pow
  条件: (F : ℍ -> 复形) (n : 自然数) (hF : MDiff F)
  证明: by
  ext z
  have hFz := UpperHalfPlane.mdifferentiableAt_iff.mp (hF z)
  simp only [normalizedDerivOfComplex, Pi.mul_apply, Pi.pow_apply]
  rw [show (F ^ n) ∘ ofComplex = (F ∘ ofComplex) ^ n from rfl]; rw [deriv_pow hFz n]
  simp [Function.comp_apply, ofComplex_apply]
  ring

Depends on / 依赖: Function, Function.comp_apply, Pi.mul_apply, Pi.pow_apply, UpperHalfPlane, UpperHalfPlane.mdifferentiableAt_iff.mp, comp_apply, deriv_pow, mdifferentiableAt_iff, mul_apply, normalizedDerivOfComplex, ofComplex, ofComplex_apply, pow_apply
-/
theorem normalizedDerivOfComplex_pow (F : ℍ -> Complex) (n : Nat) (hF : MDiff F) :
    D (F ^ n) = n * F ^ (n - 1) * D F := by
  ext z
  have hFz := UpperHalfPlane.mdifferentiableAt_iff.mp (hF z)
  simp only [normalizedDerivOfComplex, Pi.mul_apply, Pi.pow_apply]
  rw [show (F ^ n) ∘ ofComplex = (F ∘ ofComplex) ^ n from rfl]; rw [deriv_pow hFz n]
  simp [Function.comp_apply, ofComplex_apply]
  ring

/--
Definition of `serreDerivative` / `serreDerivative` 的定义

English:
definition serreDerivative
  signature: (k : Complex) (F : ℍ -> Complex) (z : ℍ)
  body: D F z - k * 12⁻¹ * EisensteinSeries.E2 z * F z

@[simp]

中文:
定义 serreDerivative
  签名: (k : 复形) (F : ℍ -> 复形) (z : ℍ)
  定义体: D F z - k * 12⁻¹ * EisensteinSeries.E2 z * F z

@[simp]

Depends on / 依赖: EisensteinSeries, EisensteinSeries.E2
-/
def serreDerivative (k : Complex) (F : ℍ -> Complex) (z : ℍ) : Complex :=
  D F z - k * 12⁻¹ * EisensteinSeries.E2 z * F z

@[simp]
/--
lemma `serreDerivative_apply` / 引理 `serreDerivative_apply`

English:
lemma serreDerivative_apply
  given: (k : Complex) (F : ℍ -> Complex) (z : ℍ)
  proof: rfl

@[simp]

中文:
引理 serreDerivative_apply
  条件: (k : 复形) (F : ℍ -> 复形) (z : ℍ)
  证明: rfl

@[simp]
-/
lemma serreDerivative_apply (k : Complex) (F : ℍ -> Complex) (z : ℍ) :
    serreDerivative k F z = D F z - k * 12⁻¹ * EisensteinSeries.E2 z * F z := rfl

@[simp]
/--
lemma `serreDerivative_eq` / 引理 `serreDerivative_eq`

English:
lemma serreDerivative_eq
  given: (k : Complex) (F : ℍ -> Complex)
  proof: rfl

中文:
引理 serreDerivative_eq
  条件: (k : 复形) (F : ℍ -> 复形)
  证明: rfl
-/
lemma serreDerivative_eq (k : Complex) (F : ℍ -> Complex) :
    serreDerivative k F = fun z => D F z - k * 12⁻¹ * EisensteinSeries.E2 z * F z := rfl

/--
theorem `serreDerivative_add` / 定理 `serreDerivative_add`

English:
theorem serreDerivative_add
  given: (k : Complex) (F G : ℍ -> Complex) (hF : MDiff F) (hG : MDiff G)
  proof: by
  ext z
  simp [serreDerivative, normalizedDerivOfComplex_add F G hF hG]
  ring_nf

中文:
定理 serreDerivative_add
  条件: (k : 复形) (F G : ℍ -> 复形) (hF : MDiff F) (hG : MDiff G)
  证明: by
  ext z
  simp [serreDerivative, normalizedDerivOfComplex_add F G hF hG]
  ring_nf

Depends on / 依赖: normalizedDerivOfComplex_add, ring_nf, serreDerivative
-/
theorem serreDerivative_add (k : Complex) (F G : ℍ -> Complex) (hF : MDiff F) (hG : MDiff G) :
    serreDerivative k (F + G) = serreDerivative k F + serreDerivative k G := by
  ext z
  simp [serreDerivative, normalizedDerivOfComplex_add F G hF hG]
  ring_nf

/--
theorem `serreDerivative_sub` / 定理 `serreDerivative_sub`

English:
theorem serreDerivative_sub
  given: (k : Complex) (F G : ℍ -> Complex) (hF : MDiff F) (hG : MDiff G)
  proof: by
  ext z
  simp [serreDerivative, normalizedDerivOfComplex_sub F G hF hG]
  ring_nf

中文:
定理 serreDerivative_sub
  条件: (k : 复形) (F G : ℍ -> 复形) (hF : MDiff F) (hG : MDiff G)
  证明: by
  ext z
  simp [serreDerivative, normalizedDerivOfComplex_sub F G hF hG]
  ring_nf

Depends on / 依赖: normalizedDerivOfComplex_sub, ring_nf, serreDerivative
-/
theorem serreDerivative_sub (k : Complex) (F G : ℍ -> Complex) (hF : MDiff F) (hG : MDiff G) :
    serreDerivative k (F - G) = serreDerivative k F - serreDerivative k G := by
  ext z
  simp [serreDerivative, normalizedDerivOfComplex_sub F G hF hG]
  ring_nf

/--
theorem `serreDerivative_smul` / 定理 `serreDerivative_smul`

English:
theorem serreDerivative_smul
  given: (k : Complex) (c : Complex) (F : ℍ -> Complex) (hF : MDiff F)
  proof: by
  ext z
  simp [serreDerivative, normalizedDerivOfComplex_smul c F hF, smul_eq_mul]
  ring_nf

中文:
定理 serreDerivative_smul
  条件: (k : 复形) (c : 复形) (F : ℍ -> 复形) (hF : MDiff F)
  证明: by
  ext z
  simp [serreDerivative, normalizedDerivOfComplex_smul c F hF, smul_eq_mul]
  ring_nf

Depends on / 依赖: normalizedDerivOfComplex_smul, ring_nf, serreDerivative, smul_eq_mul
-/
theorem serreDerivative_smul (k : Complex) (c : Complex) (F : ℍ -> Complex) (hF : MDiff F) :
    serreDerivative k (c • F) = c • (serreDerivative k F) := by
  ext z
  simp [serreDerivative, normalizedDerivOfComplex_smul c F hF, smul_eq_mul]
  ring_nf

/--
theorem `serreDerivative_mul` / 定理 `serreDerivative_mul`

English:
theorem serreDerivative_mul
  given: (k₁ k₂ : Complex) (F G : ℍ -> Complex) (hF : MDiff F) (hG : MDiff G)
  proof: by
  ext z
  simp [serreDerivative, normalizedDerivOfComplex_mul F G hF hG]
  ring_nf

中文:
定理 serreDerivative_mul
  条件: (k₁ k₂ : 复形) (F G : ℍ -> 复形) (hF : MDiff F) (hG : MDiff G)
  证明: by
  ext z
  simp [serreDerivative, normalizedDerivOfComplex_mul F G hF hG]
  ring_nf

Depends on / 依赖: normalizedDerivOfComplex_mul, ring_nf, serreDerivative
-/
theorem serreDerivative_mul (k₁ k₂ : Complex) (F G : ℍ -> Complex) (hF : MDiff F) (hG : MDiff G) :
    serreDerivative (k₁ + k₂) (F * G) =
      (serreDerivative k₁ F) * G + F * (serreDerivative k₂ G) := by
  ext z
  simp [serreDerivative, normalizedDerivOfComplex_mul F G hF hG]
  ring_nf

/--
theorem `serreDerivative_mdifferentiable` / 定理 `serreDerivative_mdifferentiable`

English:
theorem serreDerivative_mdifferentiable
  given: {F : ℍ -> Complex} (k : Complex) (hF : MDiff F)
  proof: by
  refine (normalizedDerivOfComplex_mdifferentiable hF).sub ?_
  convert!
    (MDifferentiable.mul mdifferentiable_const (E2_mdifferentiable.mul hF) :
      MDiff (fun z => (k * 12⁻¹) * (EisensteinSeries.E2 z * F z)))
  simp [Pi.mul_apply, mul_assoc, mul_left_comm, mul_comm]

中文:
定理 serreDerivative_mdifferentiable
  条件: {F : ℍ -> 复形} (k : 复形) (hF : MDiff F)
  证明: by
  refine (normalizedDerivOfComplex_mdifferentiable hF).sub ?_
  convert!
    (MDifferentiable.mul mdifferentiable_const (E2_mdifferentiable.mul hF) :
      MDiff (fun z => (k * 12⁻¹) * (EisensteinSeries.E2 z * F z)))
  simp [Pi.mul_apply, mul_assoc, mul_left_comm, mul_comm]

Depends on / 依赖: E2_mdifferentiable, E2_mdifferentiable.mul, EisensteinSeries, EisensteinSeries.E2, MDifferentiable, MDifferentiable.mul, Pi.mul_apply, convert, mdifferentiable_const, mul_apply, mul_assoc, mul_comm, mul_left_comm, normalizedDerivOfComplex_mdifferentiable
-/
theorem serreDerivative_mdifferentiable {F : ℍ -> Complex} (k : Complex) (hF : MDiff F) :
    MDiff (serreDerivative k F) := by
  refine (normalizedDerivOfComplex_mdifferentiable hF).sub ?_
  convert!
    (MDifferentiable.mul mdifferentiable_const (E2_mdifferentiable.mul hF) :
      MDiff (fun z => (k * 12⁻¹) * (EisensteinSeries.E2 z * F z)))
  simp [Pi.mul_apply, mul_assoc, mul_left_comm, mul_comm]

open ModularGroup

/--
lemma `normalizedDerivOfComplex_slash` / 引理 `normalizedDerivOfComplex_slash`

English:
lemma normalizedDerivOfComplex_slash
  statement: {k : Int} {F : ℍ -> Complex} (hF : MDiff F)
  proof: by
  have hdet : g.det.val = g.val.det := Matrix.GeneralLinearGroup.val_det_apply g
  have hdetComplex : (g.val.det : Complex) != 0 := Complex.ofReal_ne_zero.mpr hg.ne'
  have hσ (x) : σ g x = x := by grind [σ, ContinuousAlgEquiv.refl_apply]
  ext z
  simp only [normalizedDerivOfComplex, ModularForm

中文:
引理 normalizedDerivOfComplex_slash
  结论: {k : 整数} {F : ℍ -> 复形} (hF : MDiff F)
  证明: by
  have hdet : g.det.val = g.val.det := Matrix.GeneralLinearGroup.val_det_apply g
  have hdetComplex : (g.val.det : Complex) != 0 := Complex.ofReal_ne_zero.mpr hg.ne'
  have hσ (x) : σ g x = x := by grind [σ, ContinuousAlgEquiv.refl_apply]
  ext z
  simp only [normalizedDerivOfComplex, ModularForm

Depends on / 依赖: Complex.ofReal_ne_zero.mpr, ContinuousAlgEquiv, ContinuousAlgEquiv.refl_apply, GeneralLinearGroup, HasDerivAt, Matrix, Matrix.GeneralLinearGroup.val_det_apply, ModularForm, ModularForm.slash_apply, denom_ne_zero, g.det.val, g.val.det, h_smul, hasDerivAt, hasStrictDerivAt_smul, hdetComplex, hg.ne, normalizedDerivOfComplex, ofComplex, ofReal_ne_zero
-/
lemma normalizedDerivOfComplex_slash {k : Int} {F : ℍ -> Complex} (hF : MDiff F)
    {g : GL (Fin 2) Real} (hg : 0 < g.val.det) :
    D (F ∣[k] g) = fun z : ℍ => (g.val.det : Complex)⁻¹ * (D F ∣[k + 2] g) z -
      (k : Complex) * (2 * π * I)⁻¹ * (g 1 0 / denom g z) * (F ∣[k] g) z := by
  have hdet : g.det.val = g.val.det := Matrix.GeneralLinearGroup.val_det_apply g
  have hdetComplex : (g.val.det : Complex) != 0 := Complex.ofReal_ne_zero.mpr hg.ne'
  have hσ (x) : σ g x = x := by grind [σ, ContinuousAlgEquiv.refl_apply]
  ext z
  simp only [normalizedDerivOfComplex, ModularForm.slash_apply]
  have hz := denom_ne_zero g z
  have h_smul : HasDerivAt (fun w => ↑(g • ofComplex w) : Complex -> Complex)
      ((g.val.det : Complex) / denom g z ^ 2) ↑z := (hasStrictDerivAt_smul hg z).hasDerivAt
  have h_F : HasDerivAt (F ∘ ofComplex) (deriv (F ∘ ofComplex) ↑(g • ofComplex (z : Complex)))
      ↑(g • ofComplex (z : Complex)) :=
    (ofComplex_apply z).symm ▸ (mdifferentiableAt_iff.mp (hF (g • z))).hasDerivAt
  have h_denom : HasDerivAt (fun w => (denom g w) ^ (-k))
      (-k * (g 1 0 : Complex) * (denom g z) ^ (-k - 1)) ↑z := by
    simpa using hasDerivAt_denom_zpow g (-k) z
  have hcomp : ((F ∣[k] g) ∘ ofComplex) =ᶠ[𝓝 ↑z]
      fun w => (g.val.det : Complex) ^ (k - 1) *
        ((F ∘ ofComplex) ↑(g • ofComplex w) * (denom g w) ^ (-k)) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
    grind [ofComplex_apply_of_im_pos, ofComplex_apply, ModularForm.slash_apply]
  rw [((((h_F.comp (z : Complex) h_smul).mul h_denom).const_mul _).congr_of_eventuallyEq hcomp).deriv]
  simp only [hσ, hdet, abs_of_pos hg, ofComplex_apply, Function.comp_apply]
  rw [show k + 2 - 1 = (k - 1) + 2 by ring]; rw [show -(k + 2) = -k + -2 by ring]; rw [zpow_add₀ hdetComplex]; rw [zpow_add₀ hz]; rw [zpow_sub_one₀ hz]
  field

/--
lemma `normalizedDerivOfComplex_SL_slash` / 引理 `normalizedDerivOfComplex_SL_slash`

English:
lemma normalizedDerivOfComplex_SL_slash
  given: {k : Int} {F : ℍ -> Complex} (hF : MDiff F) {γ : SL(2, Int)}
  proof: by
  have hdet : (γ : GL (Fin 2) Real).val.det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]; simp
  ext z
  have := congrFun
    (normalizedDerivOfComplex_slash (k := k) hF (g := (γ : GL (Fin 2) Real)) (by grind)) z
  rw [hdet] at this
  simpa [ModularForm.SL_slash] using this

中文:
引理 normalizedDerivOfComplex_SL_slash
  条件: {k : 整数} {F : ℍ -> 复形} (hF : MDiff F) {γ : SL(2, 整数)}
  证明: by
  have hdet : (γ : GL (Fin 2) Real).val.det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]; simp
  ext z
  have := congrFun
    (normalizedDerivOfComplex_slash (k := k) hF (g := (γ : GL (Fin 2) Real)) (by grind)) z
  rw [hdet] at this
  simpa [ModularForm.SL_slash] using this

Depends on / 依赖: GeneralLinearGroup, Matrix, Matrix.GeneralLinearGroup.val_det_apply, ModularForm, ModularForm.SL_slash, SL_slash, normalizedDerivOfComplex_slash, val.det, val_det_apply
-/
lemma normalizedDerivOfComplex_SL_slash {k : Int} {F : ℍ -> Complex} (hF : MDiff F) {γ : SL(2, Int)} :
    D (F ∣[k] γ) = (D F ∣[k + 2] γ) -
      (fun z : ℍ => (k : Complex) * (2 * π * I)⁻¹ * (γ 1 0 / denom γ z) * (F ∣[k] γ) z) := by
  have hdet : (γ : GL (Fin 2) Real).val.det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]; simp
  ext z
  have := congrFun
    (normalizedDerivOfComplex_slash (k := k) hF (g := (γ : GL (Fin 2) Real)) (by grind)) z
  rw [hdet] at this
  simpa [ModularForm.SL_slash] using this

/--
theorem `serreDerivative_slash_equivariant` / 定理 `serreDerivative_slash_equivariant`

English:
theorem serreDerivative_slash_equivariant
  given: {k : Int} {F : ℍ -> Complex} (hF : MDiff F) {γ : SL(2, Int)}
  proof: by
  ext z
  have hLHS : (serreDerivative (k : Complex) F ∣[k + 2] γ) z =
      (D F ∣[k + 2] γ) z - ↑k * 12⁻¹ * ((EisensteinSeries.E2 ∣[(2 : Int)] γ) z * (F ∣[k] γ) z) := by
    grind [ModularForm.SL_slash_apply, serreDerivative_apply, Pi.mul_apply,
      congrFun (ModularForm.mul_slash_SL2 2 k γ E

中文:
定理 serreDerivative_slash_equivariant
  条件: {k : 整数} {F : ℍ -> 复形} (hF : MDiff F) {γ : SL(2, 整数)}
  证明: by
  ext z
  have hLHS : (serreDerivative (k : Complex) F ∣[k + 2] γ) z =
      (D F ∣[k + 2] γ) z - ↑k * 12⁻¹ * ((EisensteinSeries.E2 ∣[(2 : Int)] γ) z * (F ∣[k] γ) z) := by
    grind [ModularForm.SL_slash_apply, serreDerivative_apply, Pi.mul_apply,
      congrFun (ModularForm.mul_slash_SL2 2 k γ E

Depends on / 依赖: EisensteinSeries, EisensteinSeries.E2, ModularForm, ModularForm.SL_slash_apply, ModularForm.mul_slash_SL2, Pi.mul_apply, SL_slash_apply, mul_apply, mul_slash_SL2, normalizedDerivOfComplex_SL_slash, serreDerivative, serreDerivative_apply
-/
theorem serreDerivative_slash_equivariant {k : Int} {F : ℍ -> Complex} (hF : MDiff F) {γ : SL(2, Int)} :
    serreDerivative k F ∣[k + 2] γ = serreDerivative k (F ∣[k] γ) := by
  ext z
  have hLHS : (serreDerivative (k : Complex) F ∣[k + 2] γ) z =
      (D F ∣[k + 2] γ) z - ↑k * 12⁻¹ * ((EisensteinSeries.E2 ∣[(2 : Int)] γ) z * (F ∣[k] γ) z) := by
    grind [ModularForm.SL_slash_apply, serreDerivative_apply, Pi.mul_apply,
      congrFun (ModularForm.mul_slash_SL2 2 k γ EisensteinSeries.E2 F) z]
  have hDz : (D (F ∣[k] γ)) z = (D F ∣[k + 2] γ) z -
      (k * (2 * π * I)⁻¹ * (γ 1 0 / denom γ z) * (F ∣[k] γ) z) := by
    simp [normalizedDerivOfComplex_SL_slash hF]
  have hE2z : (EisensteinSeries.E2 ∣[(2 : Int)] γ) z =
      EisensteinSeries.E2 z - 1 / (2 * riemannZeta 2) * EisensteinSeries.D2 γ z := by
    simp [EisensteinSeries.E2_slash_action]
  grind [serreDerivative_apply, EisensteinSeries.D2, riemannZeta_two, I_sq]

/--
theorem `serreDerivative_slash_invariant` / 定理 `serreDerivative_slash_invariant`

English:
theorem serreDerivative_slash_invariant
  statement: {k : Int} {F : ℍ -> Complex} (hF : MDiff F) {γ : SL(2, Int)}
  proof: by
  grind [serreDerivative_slash_equivariant]

中文:
定理 serreDerivative_slash_invariant
  结论: {k : 整数} {F : ℍ -> 复形} (hF : MDiff F) {γ : SL(2, 整数)}
  证明: by
  grind [serreDerivative_slash_equivariant]

Depends on / 依赖: serreDerivative_slash_equivariant
-/
theorem serreDerivative_slash_invariant {k : Int} {F : ℍ -> Complex} (hF : MDiff F) {γ : SL(2, Int)}
    (h : F ∣[k] γ = F) :
    serreDerivative k F ∣[k + 2] γ = serreDerivative k F := by
  grind [serreDerivative_slash_equivariant]

end

end Derivative
