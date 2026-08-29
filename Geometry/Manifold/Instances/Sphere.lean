/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Module.Ball.Action
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Tactic.Module

/-!
# Manifold structure on the sphere

This file defines stereographic projection from the sphere in an inner product space `E`, and uses
it to put an analytic manifold structure on the sphere.

## Main results

For a unit vector `v` in `E`, the definition `stereographic` gives the stereographic projection
centred at `v`, an open partial homeomorphism from the sphere to `(ℝ ∙ v)ᗮ` (the orthogonal
complement of `v`).

For finite-dimensional `E`, we then construct an analytic manifold instance on the sphere; the
charts here are obtained by composing the open partial homeomorphisms `stereographic` with arbitrary
isometries from `(ℝ ∙ v)ᗮ` to Euclidean space.

We prove two lemmas about `C^n` maps:
* `contMDiff_coe_sphere` states that the coercion map from the sphere into `E` is analytic;
  this is a useful tool for constructing smooth maps *from* the sphere.
* `contMDiff.codRestrict_sphere` states that a map from a manifold into the sphere is
  `C^m` if its lift to a map to `E` is `C^m`; this is a useful tool for constructing `C^m` maps
  *to* the sphere.

As an application we prove `contMDiffNegSphere`, that the antipodal map is analytic.

Finally, we equip the `Circle` (defined in `Analysis.Complex.Circle` to be the sphere in `ℂ`
centred at `0` of radius `1`) with the following structure:
* a charted space with model space `EuclideanSpace ℝ (Fin 1)` (inherited from `Metric.Sphere`)
* an analytic Lie group with model with corners `𝓡 1`

We furthermore show that `Circle.exp` (defined in `Analysis.Complex.Circle` to be the natural
map `fun t ↦ exp (t * I)` from `ℝ` to `Circle`) is analytic.


## Implementation notes

The model space for the charted space instance is `EuclideanSpace ℝ (Fin n)`, where `n` is a
natural number satisfying the typeclass assumption `[Fact (finrank ℝ E = n + 1)]`. This may seem a
little awkward, but it is designed to circumvent the problem that the literal expression for the
dimension of the model space (up to definitional equality) determines the type. If one used the
naive expression `EuclideanSpace ℝ (Fin (finrank ℝ E - 1))` for the model space, then the sphere in
`ℂ` would be a manifold with model space `EuclideanSpace ℝ (Fin (2 - 1))` but not with model space
`EuclideanSpace ℝ (Fin 1)`.

## TODO

Relate the stereographic projection to the inversion of the space.
-/

@[expose] public section


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]

noncomputable section

open Metric Module Function

open scoped Manifold ContDiff RealInnerProductSpace

section StereographicProjection

variable (v : E)

/-! ### Construction of the stereographic projection -/


/--
Definition of `stereoToFun` / `stereoToFun` 的定义

English:
definition stereoToFun
  signature: (x : E)
  body: (2 / ((1 : Real) - innerSL Real v x)) • (Real ∙ v)ᗮ.orthogonalProjectionOnto x

中文:
定义 stereoToFun
  签名: (x : E)
  定义体: (2 / ((1 : Real) - innerSL Real v x)) • (Real ∙ v)ᗮ.orthogonalProjectionOnto x

Depends on / 依赖: innerSL, orthogonalProjectionOnto
-/
def stereoToFun (x : E) : (Real ∙ v)ᗮ :=
  (2 / ((1 : Real) - innerSL Real v x)) • (Real ∙ v)ᗮ.orthogonalProjectionOnto x

variable {v}

@[simp]
/--
theorem `stereoToFun_apply` / 定理 `stereoToFun_apply`

English:
theorem stereoToFun_apply
  given: (x : E)
  proof: rfl

中文:
定理 stereoToFun_apply
  条件: (x : E)
  证明: rfl
-/
theorem stereoToFun_apply (x : E) :
    stereoToFun v x = (2 / ((1 : Real) - innerSL Real v x)) • (Real ∙ v)ᗮ.orthogonalProjectionOnto x :=
  rfl

/--
theorem `contDiffOn_stereoToFun` / 定理 `contDiffOn_stereoToFun`

English:
theorem contDiffOn_stereoToFun
  given: {n : Nat∞ω}
  proof: by
  refine ContDiffOn.fun_smul ?_ (Real ∙ v)ᗮ.orthogonalProjectionOnto.contDiff.contDiffOn
  refine contDiff_const.contDiffOn.div ?_ ?_
  · exact (contDiff_const.sub (innerSL Real v).contDiff).contDiffOn
  · intro x h h'
    exact h (sub_eq_zero.mp h').symm

中文:
定理 contDiffOn_stereoToFun
  条件: {n : 自然数∞ω}
  证明: by
  refine ContDiffOn.fun_smul ?_ (Real ∙ v)ᗮ.orthogonalProjectionOnto.contDiff.contDiffOn
  refine contDiff_const.contDiffOn.div ?_ ?_
  · exact (contDiff_const.sub (innerSL Real v).contDiff).contDiffOn
  · intro x h h'
    exact h (sub_eq_zero.mp h').symm

Depends on / 依赖: ContDiffOn, ContDiffOn.fun_smul, contDiff, contDiffOn, contDiff_const, contDiff_const.contDiffOn.div, contDiff_const.sub, fun_smul, innerSL, orthogonalProjectionOnto, orthogonalProjectionOnto.contDiff.contDiffOn, sub_eq_zero, sub_eq_zero.mp
-/
theorem contDiffOn_stereoToFun {n : Nat∞ω} :
    ContDiffOn Real n (stereoToFun v) {x : E | innerSL _ v x != (1 : Real)} := by
  refine ContDiffOn.fun_smul ?_ (Real ∙ v)ᗮ.orthogonalProjectionOnto.contDiff.contDiffOn
  refine contDiff_const.contDiffOn.div ?_ ?_
  · exact (contDiff_const.sub (innerSL Real v).contDiff).contDiffOn
  · intro x h h'
    exact h (sub_eq_zero.mp h').symm

/--
theorem `continuousOn_stereoToFun` / 定理 `continuousOn_stereoToFun`

English:
theorem continuousOn_stereoToFun
  proof: (contDiffOn_stereoToFun (n := 0)).continuousOn

中文:
定理 continuousOn_stereoToFun
  证明: (contDiffOn_stereoToFun (n := 0)).continuousOn

Depends on / 依赖: contDiffOn_stereoToFun, continuousOn
-/
theorem continuousOn_stereoToFun :
    ContinuousOn (stereoToFun v) {x : E | innerSL _ v x != (1 : Real)} :=
  (contDiffOn_stereoToFun (n := 0)).continuousOn

variable (v) in
/--
Definition of `stereoInvFunAux` / `stereoInvFunAux` 的定义

English:
definition stereoInvFunAux
  signature: (w : E)
  body: (‖w‖ ^ 2 + 4)⁻¹ • ((4 : Real) • w + (‖w‖ ^ 2 - 4) • v)

@[simp]

中文:
定义 stereoInvFunAux
  签名: (w : E)
  定义体: (‖w‖ ^ 2 + 4)⁻¹ • ((4 : Real) • w + (‖w‖ ^ 2 - 4) • v)

@[simp]
-/
def stereoInvFunAux (w : E) : E :=
  (‖w‖ ^ 2 + 4)⁻¹ • ((4 : Real) • w + (‖w‖ ^ 2 - 4) • v)

@[simp]
/--
theorem `stereoInvFunAux_apply` / 定理 `stereoInvFunAux_apply`

English:
theorem stereoInvFunAux_apply
  given: (w : E)
  proof: rfl

中文:
定理 stereoInvFunAux_apply
  条件: (w : E)
  证明: rfl
-/
theorem stereoInvFunAux_apply (w : E) :
    stereoInvFunAux v w = (‖w‖ ^ 2 + 4)⁻¹ • ((4 : Real) • w + (‖w‖ ^ 2 - 4) • v) :=
  rfl

/--
theorem `stereoInvFunAux_mem` / 定理 `stereoInvFunAux_mem`

English:
theorem stereoInvFunAux_mem
  given: (hv : ‖v‖ = 1) {w : E} (hw : w in (Real ∙ v)ᗮ)
  proof: by
  have h₁ : (0 : Real) < ‖w‖ ^ 2 + 4 := by positivity
  suffices ‖(4 : Real) • w + (‖w‖ ^ 2 - 4) • v‖ = ‖w‖ ^ 2 + 4 by
    simp only [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_inv, this,
      abs_of_pos h₁, stereoInvFunAux_apply, inv_mul_cancel₀ h₁.ne']
  suffices ‖(4 : Real) • 

中文:
定理 stereoInvFunAux_mem
  条件: (hv : ‖v‖ = 1) {w : E} (hw : w in (实数 ∙ v)ᗮ)
  证明: by
  have h₁ : (0 : Real) < ‖w‖ ^ 2 + 4 := by positivity
  suffices ‖(4 : Real) • w + (‖w‖ ^ 2 - 4) • v‖ = ‖w‖ ^ 2 + 4 by
    simp only [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_inv, this,
      abs_of_pos h₁, stereoInvFunAux_apply, inv_mul_cancel₀ h₁.ne']
  suffices ‖(4 : Real) • 

Depends on / 依赖: Real.norm_eq_abs, Submodule, Submodule.mem_orthogonal_singleton_iff_inner_left, abs_inv, abs_norm, abs_of_pos, mem_orthogonal_singleton_iff_inner_left, mem_sphere_zero_iff_norm, norm_add_sq_real, norm_eq_abs, norm_smu, norm_smul, sq_eq_sq_iff_abs_eq_abs, stereoInvFunAux_apply
-/
theorem stereoInvFunAux_mem (hv : ‖v‖ = 1) {w : E} (hw : w in (Real ∙ v)ᗮ) :
    stereoInvFunAux v w in sphere (0 : E) 1 := by
  have h₁ : (0 : Real) < ‖w‖ ^ 2 + 4 := by positivity
  suffices ‖(4 : Real) • w + (‖w‖ ^ 2 - 4) • v‖ = ‖w‖ ^ 2 + 4 by
    simp only [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_inv, this,
      abs_of_pos h₁, stereoInvFunAux_apply, inv_mul_cancel₀ h₁.ne']
  suffices ‖(4 : Real) • w + (‖w‖ ^ 2 - 4) • v‖ ^ 2 = (‖w‖ ^ 2 + 4) ^ 2 by
    simpa only [sq_eq_sq_iff_abs_eq_abs, abs_norm, abs_of_pos h₁] using this
  rw [Submodule.mem_orthogonal_singleton_iff_inner_left] at hw
  simp [norm_add_sq_real, norm_smul, inner_smul_left, inner_smul_right, hw, mul_pow,
    Real.norm_eq_abs, hv]
  ring

/--
theorem `hasFDerivAt_stereoInvFunAux` / 定理 `hasFDerivAt_stereoInvFunAux`

English:
theorem hasFDerivAt_stereoInvFunAux
  given: (v : E)
  proof: by
  have h₀ : HasFDerivAt (fun w : E => ‖w‖ ^ 2) (0 : StrongDual Real E) 0 := by
    convert! (hasStrictFDerivAt_norm_sq (0 : E)).hasFDerivAt
    simp only [map_zero, smul_zero]
  have h₁ : HasFDerivAt (fun w : E => (‖w‖ ^ 2 + 4)⁻¹) (0 : StrongDual Real E) 0 := by
    convert! (hasFDerivAt_inv _).c

中文:
定理 hasFDerivAt_stereoInvFunAux
  条件: (v : E)
  证明: by
  have h₀ : HasFDerivAt (fun w : E => ‖w‖ ^ 2) (0 : StrongDual Real E) 0 := by
    convert! (hasStrictFDerivAt_norm_sq (0 : E)).hasFDerivAt
    simp only [map_zero, smul_zero]
  have h₁ : HasFDerivAt (fun w : E => (‖w‖ ^ 2 + 4)⁻¹) (0 : StrongDual Real E) 0 := by
    convert! (hasFDerivAt_inv _).c

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.id, HasFDerivAt, StrongDual, convert, hasFDerivAt, hasFDerivAt_const, hasFDerivAt_inv, hasStrictFDerivAt_norm_sq, map_zero, smul_zero
-/
theorem hasFDerivAt_stereoInvFunAux (v : E) :
    HasFDerivAt (stereoInvFunAux v) (ContinuousLinearMap.id Real E) 0 := by
  have h₀ : HasFDerivAt (fun w : E => ‖w‖ ^ 2) (0 : StrongDual Real E) 0 := by
    convert! (hasStrictFDerivAt_norm_sq (0 : E)).hasFDerivAt
    simp only [map_zero, smul_zero]
  have h₁ : HasFDerivAt (fun w : E => (‖w‖ ^ 2 + 4)⁻¹) (0 : StrongDual Real E) 0 := by
    convert! (hasFDerivAt_inv _).comp _ (h₀.add (hasFDerivAt_const 4 0)) <;> simp
  have h₂ : HasFDerivAt (fun w => (4 : Real) • w + (‖w‖ ^ 2 - 4) • v)
      ((4 : Real) • ContinuousLinearMap.id Real E) 0 := by
    convert!
      ((hasFDerivAt_const (4 : Real) 0).smul (hasFDerivAt_id 0)).add
        ((h₀.sub (hasFDerivAt_const (4 : Real) 0)).smul (hasFDerivAt_const v 0)) using 1
    ext w
    simp
  convert! h₁.smul h₂ using 1
  ext w
  simp

/--
theorem `hasFDerivAt_stereoInvFunAux_comp_coe` / 定理 `hasFDerivAt_stereoInvFunAux_comp_coe`

English:
theorem hasFDerivAt_stereoInvFunAux_comp_coe
  given: (v : E)
  proof: by
  have : HasFDerivAt (stereoInvFunAux v) (ContinuousLinearMap.id Real E) ((Real ∙ v)ᗮ.subtypeL 0) :=
    hasFDerivAt_stereoInvFunAux v
  refine this.comp (0 : (Real ∙ v)ᗮ) (by apply ContinuousLinearMap.hasFDerivAt)

中文:
定理 hasFDerivAt_stereoInvFunAux_comp_coe
  条件: (v : E)
  证明: by
  have : HasFDerivAt (stereoInvFunAux v) (ContinuousLinearMap.id Real E) ((Real ∙ v)ᗮ.subtypeL 0) :=
    hasFDerivAt_stereoInvFunAux v
  refine this.comp (0 : (Real ∙ v)ᗮ) (by apply ContinuousLinearMap.hasFDerivAt)

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.hasFDerivAt, ContinuousLinearMap.id, HasFDerivAt, hasFDerivAt, hasFDerivAt_stereoInvFunAux, stereoInvFunAux, subtypeL, this.comp
-/
theorem hasFDerivAt_stereoInvFunAux_comp_coe (v : E) :
    HasFDerivAt (stereoInvFunAux v ∘ ((↑) : (Real ∙ v)ᗮ -> E)) (Real ∙ v)ᗮ.subtypeL 0 := by
  have : HasFDerivAt (stereoInvFunAux v) (ContinuousLinearMap.id Real E) ((Real ∙ v)ᗮ.subtypeL 0) :=
    hasFDerivAt_stereoInvFunAux v
  refine this.comp (0 : (Real ∙ v)ᗮ) (by apply ContinuousLinearMap.hasFDerivAt)

/--
theorem `contDiff_stereoInvFunAux` / 定理 `contDiff_stereoInvFunAux`

English:
theorem contDiff_stereoInvFunAux
  given: {m : Nat∞ω}
  statement: ContDiff Real m (stereoInvFunAux v)
  proof: by
  have h₀ : ContDiff Real ω fun w : E => ‖w‖ ^ 2 := contDiff_norm_sq Real
  have h₁ : ContDiff Real ω fun w : E => (‖w‖ ^ 2 + 4)⁻¹ := by
    refine (h₀.add contDiff_const).inv ?_
    intro x
    nlinarith
  have h₂ : ContDiff Real ω fun w => (4 : Real) • w + (‖w‖ ^ 2 - 4) • v := by
    refine (co

中文:
定理 contDiff_stereoInvFunAux
  条件: {m : 自然数∞ω}
  结论: ContDiff 实数 m (stereoInvFunAux v)
  证明: by
  have h₀ : ContDiff Real ω fun w : E => ‖w‖ ^ 2 := contDiff_norm_sq Real
  have h₁ : ContDiff Real ω fun w : E => (‖w‖ ^ 2 + 4)⁻¹ := by
    refine (h₀.add contDiff_const).inv ?_
    intro x
    nlinarith
  have h₂ : ContDiff Real ω fun w => (4 : Real) • w + (‖w‖ ^ 2 - 4) • v := by
    refine (co

Depends on / 依赖: ContDiff, contDiff_const, contDiff_const.smul, contDiff_id, contDiff_norm_sq, le_top, of_le
-/
theorem contDiff_stereoInvFunAux {m : Nat∞ω} : ContDiff Real m (stereoInvFunAux v) := by
  have h₀ : ContDiff Real ω fun w : E => ‖w‖ ^ 2 := contDiff_norm_sq Real
  have h₁ : ContDiff Real ω fun w : E => (‖w‖ ^ 2 + 4)⁻¹ := by
    refine (h₀.add contDiff_const).inv ?_
    intro x
    nlinarith
  have h₂ : ContDiff Real ω fun w => (4 : Real) • w + (‖w‖ ^ 2 - 4) • v := by
    refine (contDiff_const.smul contDiff_id).add ?_
    exact (h₀.sub contDiff_const).smul contDiff_const
  exact (h₁.smul h₂).of_le le_top

/--
Definition of `stereoInvFun` / `stereoInvFun` 的定义

English:
definition stereoInvFun
  signature: (hv : ‖v‖ = 1) (w : (Real ∙ v)ᗮ)
  body: ⟨stereoInvFunAux v (w : E), stereoInvFunAux_mem hv w.2⟩

@[simp]

中文:
定义 stereoInvFun
  签名: (hv : ‖v‖ = 1) (w : (实数 ∙ v)ᗮ)
  定义体: ⟨stereoInvFunAux v (w : E), stereoInvFunAux_mem hv w.2⟩

@[simp]

Depends on / 依赖: stereoInvFunAux, stereoInvFunAux_mem
-/
def stereoInvFun (hv : ‖v‖ = 1) (w : (Real ∙ v)ᗮ) : sphere (0 : E) 1 :=
  ⟨stereoInvFunAux v (w : E), stereoInvFunAux_mem hv w.2⟩

@[simp]
/--
theorem `stereoInvFun_apply` / 定理 `stereoInvFun_apply`

English:
theorem stereoInvFun_apply
  given: (hv : ‖v‖ = 1) (w : (Real ∙ v)ᗮ)
  proof: rfl

中文:
定理 stereoInvFun_apply
  条件: (hv : ‖v‖ = 1) (w : (实数 ∙ v)ᗮ)
  证明: rfl
-/
theorem stereoInvFun_apply (hv : ‖v‖ = 1) (w : (Real ∙ v)ᗮ) :
    (stereoInvFun hv w : E) = (‖w‖ ^ 2 + 4)⁻¹ • ((4 : Real) • w + (‖w‖ ^ 2 - 4) • v) :=
  rfl

open scoped InnerProductSpace in
/--
theorem `stereoInvFun_ne_north_pole` / 定理 `stereoInvFun_ne_north_pole`

English:
theorem stereoInvFun_ne_north_pole
  given: (hv : ‖v‖ = 1) (w : (Real ∙ v)ᗮ)
  proof: by
  refine Subtype.coe_ne_coe.1 ?_
  rw [← inner_lt_one_iff_real_of_norm_eq_one _ hv]
  · have hw : ⟪v, w⟫_Real = 0 := Submodule.mem_orthogonal_singleton_iff_inner_right.mp w.2
    have hw' : (‖(w : E)‖ ^ 2 + 4)⁻¹ * (‖(w : E)‖ ^ 2 - 4) < 1 := by
      rw [inv_mul_lt_iff₀']
      · linarith
      po

中文:
定理 stereoInvFun_ne_north_pole
  条件: (hv : ‖v‖ = 1) (w : (实数 ∙ v)ᗮ)
  证明: by
  refine Subtype.coe_ne_coe.1 ?_
  rw [← inner_lt_one_iff_real_of_norm_eq_one _ hv]
  · have hw : ⟪v, w⟫_Real = 0 := Submodule.mem_orthogonal_singleton_iff_inner_right.mp w.2
    have hw' : (‖(w : E)‖ ^ 2 + 4)⁻¹ * (‖(w : E)‖ ^ 2 - 4) < 1 := by
      rw [inv_mul_lt_iff₀']
      · linarith
      po

Depends on / 依赖: Submodule, Submodule.mem_orthogonal_singleton_iff_inner_right.mp, Subtype, Subtype.coe_ne_coe, _Real, coe_ne_coe, inner_add_right, inner_lt_one_iff_real_of_norm_eq_one, inner_smul_right, mem_orthogonal_singleton_iff_inner_right, real_inner_comm, real_inner_self_eq_norm_mul_norm, stereoInvFunAux_mem
-/
theorem stereoInvFun_ne_north_pole (hv : ‖v‖ = 1) (w : (Real ∙ v)ᗮ) :
    stereoInvFun hv w != (⟨v, by simp [hv]⟩ : sphere (0 : E) 1) := by
  refine Subtype.coe_ne_coe.1 ?_
  rw [← inner_lt_one_iff_real_of_norm_eq_one _ hv]
  · have hw : ⟪v, w⟫_Real = 0 := Submodule.mem_orthogonal_singleton_iff_inner_right.mp w.2
    have hw' : (‖(w : E)‖ ^ 2 + 4)⁻¹ * (‖(w : E)‖ ^ 2 - 4) < 1 := by
      rw [inv_mul_lt_iff₀']
      · linarith
      positivity
    simpa [real_inner_comm, inner_add_right, inner_smul_right, real_inner_self_eq_norm_mul_norm, hw,
      hv] using hw'
  · simpa using stereoInvFunAux_mem hv w.2

/--
theorem `continuous_stereoInvFun` / 定理 `continuous_stereoInvFun`

English:
theorem continuous_stereoInvFun
  given: (hv : ‖v‖ = 1)
  statement: Continuous (stereoInvFun hv)
  proof: continuous_induced_rng.2
    ((contDiff_stereoInvFunAux (m := 0)).continuous.comp continuous_subtype_val)

中文:
定理 continuous_stereoInvFun
  条件: (hv : ‖v‖ = 1)
  结论: Continuous (stereoInvFun hv)
  证明: continuous_induced_rng.2
    ((contDiff_stereoInvFunAux (m := 0)).continuous.comp continuous_subtype_val)

Depends on / 依赖: contDiff_stereoInvFunAux, continuous, continuous.comp, continuous_induced_rng, continuous_subtype_val
-/
theorem continuous_stereoInvFun (hv : ‖v‖ = 1) : Continuous (stereoInvFun hv) :=
  continuous_induced_rng.2
    ((contDiff_stereoInvFunAux (m := 0)).continuous.comp continuous_subtype_val)

open scoped InnerProductSpace in
attribute [-simp] AddSubgroupClass.coe_norm Submodule.coe_norm in
/--
theorem `stereo_left_inv` / 定理 `stereo_left_inv`

English:
theorem stereo_left_inv
  given: (hv : ‖v‖ = 1) {x : sphere (0 : E) 1} (hx : (x : E) != v)
  proof: by
  ext
  simp only [stereoToFun_apply, stereoInvFun_apply, smul_add]
  -- name two frequently-occurring quantities and write down their basic properties
  set a : Real := innerSL _ v x
  set y := (Real ∙ v)ᗮ.orthogonalProjectionOnto x
  have split : ↑x = a • v + ↑y := by
    rw [← ((Real ∙ v).star

中文:
定理 stereo_left_inv
  条件: (hv : ‖v‖ = 1) {x : sphere (0 : E) 1} (hx : (x : E) != v)
  证明: by
  ext
  simp only [stereoToFun_apply, stereoInvFun_apply, smul_add]
  -- name two frequently-occurring quantities and write down their basic properties
  set a : Real := innerSL _ v x
  set y := (Real ∙ v)ᗮ.orthogonalProjectionOnto x
  have split : ↑x = a • v + ↑y := by
    rw [← ((Real ∙ v).star

Depends on / 依赖: smul_add, stereoInvFun_apply, stereoToFun_apply
-/
theorem stereo_left_inv (hv : ‖v‖ = 1) {x : sphere (0 : E) 1} (hx : (x : E) != v) :
    stereoInvFun hv (stereoToFun v x) = x := by
  ext
  simp only [stereoToFun_apply, stereoInvFun_apply, smul_add]
  -- name two frequently-occurring quantities and write down their basic properties
  set a : Real := innerSL _ v x
  set y := (Real ∙ v)ᗮ.orthogonalProjectionOnto x
  have split : ↑x = a • v + ↑y := by
    rw [← ((Real ∙ v).starProjection_add_starProjection_orthogonal x)]; rw [Submodule.starProjection_unit_singleton Real hv x]
    rfl
  have hvy : ⟪v, y⟫_Real = 0 := Submodule.mem_orthogonal_singleton_iff_inner_right.mp y.2
  have pythag : 1 = a ^ 2 + ‖y‖ ^ 2 := by
    have hvy' : ⟪a • v, y⟫_Real = 0 := by simp only [inner_smul_left, hvy, mul_zero]
    convert! norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hvy' using 2
    · simp [← split]
    · simp [norm_smul, hv, ← sq, sq_abs]
    · exact sq _
  -- a fact which will be helpful for clearing denominators in the main calculation
  have ha : 0 < 1 - a := by
    have : a < 1 := (inner_lt_one_iff_real_of_norm_eq_one hv (by simp)).mpr hx.symm
    linarith
  rw [split]; rw [Submodule.coe_smul_of_tower]
  simp only [norm_smul, norm_div, Real.norm_eq_abs, abs_of_nonneg ha.le]
  match_scalars
  · field_simp
    linear_combination 4 * pythag
  · field_simp
    linear_combination 4 * (a - 1) * pythag

/--
theorem `stereo_right_inv` / 定理 `stereo_right_inv`

English:
theorem stereo_right_inv
  given: (hv : ‖v‖ = 1) (w : (Real ∙ v)ᗮ)
  statement: stereoToFun v (stereoInvFun hv w) = w
  proof: by
  simp only [stereoToFun, stereoInvFun, stereoInvFunAux, smul_add, map_add, map_smul,
    innerSL_apply_apply, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
  have h₁ : (Real ∙ v)ᗮ.orthogonalProjectionOnto v = 0 :=
    Submodule.orthogonalProjectionOnto_orthogonalComplement_singleton_e

中文:
定理 stereo_right_inv
  条件: (hv : ‖v‖ = 1) (w : (实数 ∙ v)ᗮ)
  结论: stereoToFun v (stereoInvFun hv w) = w
  证明: by
  simp only [stereoToFun, stereoInvFun, stereoInvFunAux, smul_add, map_add, map_smul,
    innerSL_apply_apply, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
  have h₁ : (Real ∙ v)ᗮ.orthogonalProjectionOnto v = 0 :=
    Submodule.orthogonalProjectionOnto_orthogonalComplement_singleton_e

Depends on / 依赖: Submodule, Submodule.mem_orthogonal_singleton_iff_inner_right.mp, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self, Submodule.orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero, innerSL_apply_apply, map_add, map_smul, match_scalars, mem_orthogonal_singleton_iff_inner_right, orthogonalProjectionOnto, orthogonalProjectionOnto_mem_subspace_eq_self, orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero, smul_add, stereoInvFun, stereoInvFunAux, stereoToFun
-/
theorem stereo_right_inv (hv : ‖v‖ = 1) (w : (Real ∙ v)ᗮ) : stereoToFun v (stereoInvFun hv w) = w := by
  simp only [stereoToFun, stereoInvFun, stereoInvFunAux, smul_add, map_add, map_smul,
    innerSL_apply_apply, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
  have h₁ : (Real ∙ v)ᗮ.orthogonalProjectionOnto v = 0 :=
    Submodule.orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero v
  have h₂ : ⟪v, w⟫ = 0 := Submodule.mem_orthogonal_singleton_iff_inner_right.mp w.2
  have h₃ : ⟪v, v⟫ = 1 := by simp [hv]
  rw [h₁]; rw [h₂]; rw [h₃]
  match_scalars
  simp [field]
  ring

/--
Definition of `stereographic` / `stereographic` 的定义

English:
definition stereographic
  signature: (hv : ‖v‖ = 1)
  body: stereoToFun v ∘ (↑)
  invFun := stereoInvFun hv
  source := {⟨v, by simp [hv]⟩}ᶜ
  target := Set.univ
  map_source' := by simp
  map_target' {w} _ := fun h => (stereoInvFun_ne_north_pole hv w) (Set.eq_of_mem_singleton h)
  left_inv' x hx := stereo_left_inv hv fun h => hx (by
    rw [← h] at hv
    a

中文:
定义 stereographic
  签名: (hv : ‖v‖ = 1)
  定义体: stereoToFun v ∘ (↑)
  invFun := stereoInvFun hv
  source := {⟨v, by simp [hv]⟩}ᶜ
  target := Set.univ
  map_source' := by simp
  map_target' {w} _ := fun h => (stereoInvFun_ne_north_pole hv w) (Set.eq_of_mem_singleton h)
  left_inv' x hx := stereo_left_inv hv fun h => hx (by
    rw [← h] at hv
    a

Depends on / 依赖: stereoToFun
-/
def stereographic (hv : ‖v‖ = 1) : OpenPartialHomeomorph (sphere (0 : E) 1) (Real ∙ v)ᗮ where
  toFun := stereoToFun v ∘ (↑)
  invFun := stereoInvFun hv
  source := {⟨v, by simp [hv]⟩}ᶜ
  target := Set.univ
  map_source' := by simp
  map_target' {w} _ := fun h => (stereoInvFun_ne_north_pole hv w) (Set.eq_of_mem_singleton h)
  left_inv' x hx := stereo_left_inv hv fun h => hx (by
    rw [← h] at hv
    apply Subtype.ext
    dsimp
    exact h)
  right_inv' w _ := stereo_right_inv hv w
  open_source := isOpen_compl_singleton
  open_target := isOpen_univ
  continuousOn_toFun :=
    continuousOn_stereoToFun.comp continuous_subtype_val.continuousOn fun w h => by
      dsimp
      exact
        h ∘ Subtype.ext ∘ Eq.symm ∘ (inner_eq_one_iff_of_norm_eq_one hv (by simp)).mp
  continuousOn_invFun := (continuous_stereoInvFun hv).continuousOn

/--
theorem `stereographic_apply` / 定理 `stereographic_apply`

English:
theorem stereographic_apply
  given: (hv : ‖v‖ = 1) (x : sphere (0 : E) 1)
  proof: rfl

@[simp]

中文:
定理 stereographic_apply
  条件: (hv : ‖v‖ = 1) (x : sphere (0 : E) 1)
  证明: rfl

@[simp]
-/
theorem stereographic_apply (hv : ‖v‖ = 1) (x : sphere (0 : E) 1) :
    stereographic hv x = (2 / ((1 : Real) - ⟪v, x⟫)) • (Real ∙ v)ᗮ.orthogonalProjectionOnto x :=
  rfl

@[simp]
/--
theorem `stereographic_source` / 定理 `stereographic_source`

English:
theorem stereographic_source
  given: (hv : ‖v‖ = 1)
  statement: (stereographic hv).source = {⟨v, by simp [hv]⟩}ᶜ
  proof: rfl

@[simp]

中文:
定理 stereographic_source
  条件: (hv : ‖v‖ = 1)
  结论: (stereographic hv).source = {⟨v, by simp [hv]⟩}ᶜ
  证明: rfl

@[simp]
-/
theorem stereographic_source (hv : ‖v‖ = 1) : (stereographic hv).source = {⟨v, by simp [hv]⟩}ᶜ :=
  rfl

@[simp]
/--
theorem `stereographic_target` / 定理 `stereographic_target`

English:
theorem stereographic_target
  given: (hv : ‖v‖ = 1)
  statement: (stereographic hv).target = Set.univ
  proof: rfl

@[simp]

中文:
定理 stereographic_target
  条件: (hv : ‖v‖ = 1)
  结论: (stereographic hv).target = Set.univ
  证明: rfl

@[simp]
-/
theorem stereographic_target (hv : ‖v‖ = 1) : (stereographic hv).target = Set.univ :=
  rfl

@[simp]
/--
theorem `stereographic_apply_neg` / 定理 `stereographic_apply_neg`

English:
theorem stereographic_apply_neg
  given: (v : sphere (0 : E) 1)
  proof: by
  simp [stereographic_apply]

@[simp]

中文:
定理 stereographic_apply_neg
  条件: (v : sphere (0 : E) 1)
  证明: by
  simp [stereographic_apply]

@[simp]

Depends on / 依赖: stereographic_apply
-/
theorem stereographic_apply_neg (v : sphere (0 : E) 1) :
    stereographic (norm_eq_of_mem_sphere v) (-v) = 0 := by
  simp [stereographic_apply]

@[simp]
/--
theorem `stereographic_neg_apply` / 定理 `stereographic_neg_apply`

English:
theorem stereographic_neg_apply
  given: (v : sphere (0 : E) 1)
  proof: by
  convert! stereographic_apply_neg (-v)
  ext1
  simp

中文:
定理 stereographic_neg_apply
  条件: (v : sphere (0 : E) 1)
  证明: by
  convert! stereographic_apply_neg (-v)
  ext1
  simp

Depends on / 依赖: convert, stereographic_apply_neg
-/
theorem stereographic_neg_apply (v : sphere (0 : E) 1) :
    stereographic (norm_eq_of_mem_sphere (-v)) v = 0 := by
  convert! stereographic_apply_neg (-v)
  ext1
  simp

/--
theorem `surjective_stereographic` / 定理 `surjective_stereographic`

English:
theorem surjective_stereographic
  given: (hv : ‖v‖ = 1)
  proof: (stereographic hv).surjective_of_target_eq_univ rfl

@[simp]

中文:
定理 surjective_stereographic
  条件: (hv : ‖v‖ = 1)
  证明: (stereographic hv).surjective_of_target_eq_univ rfl

@[simp]

Depends on / 依赖: stereographic, surjective_of_target_eq_univ
-/
theorem surjective_stereographic (hv : ‖v‖ = 1) :
    Surjective (stereographic hv) :=
  (stereographic hv).surjective_of_target_eq_univ rfl

@[simp]
/--
theorem `range_stereographic_symm` / 定理 `range_stereographic_symm`

English:
theorem range_stereographic_symm
  given: (hv : ‖v‖ = 1) (hv' : v in sphere 0 1 := by simpa)
  proof: by
  refine le_antisymm ?_ (stereographic hv).symm.target_subset_range
  rintro x ⟨y, rfl⟩
  suffices y in (stereographic hv).target from (fun _ => (stereographic hv).map_target) y this
  simp

中文:
定理 range_stereographic_symm
  条件: (hv : ‖v‖ = 1) (hv' : v in sphere 0 1 := by simpa)
  证明: by
  refine le_antisymm ?_ (stereographic hv).symm.target_subset_range
  rintro x ⟨y, rfl⟩
  suffices y in (stereographic hv).target from (fun _ => (stereographic hv).map_target) y this
  simp

Depends on / 依赖: Set.range, le_antisymm, map_target, stereographic, symm.target_subset_range, target, target_subset_range
-/
theorem range_stereographic_symm (hv : ‖v‖ = 1) (hv' : v in sphere 0 1 := by simpa) :
    Set.range (stereographic hv).symm = {⟨v, hv'⟩}ᶜ := by
  refine le_antisymm ?_ (stereographic hv).symm.target_subset_range
  rintro x ⟨y, rfl⟩
  suffices y in (stereographic hv).target from (fun _ => (stereographic hv).map_target) y this
  simp

/--
lemma `isOpenEmbedding_stereographic_symm` / 引理 `isOpenEmbedding_stereographic_symm`

English:
lemma isOpenEmbedding_stereographic_symm
  given: (hv : ‖v‖ = 1)
  proof: (stereographic hv).symm.isOpenEmbedding (by simp)

中文:
引理 isOpenEmbedding_stereographic_symm
  条件: (hv : ‖v‖ = 1)
  证明: (stereographic hv).symm.isOpenEmbedding (by simp)

Depends on / 依赖: isOpenEmbedding, stereographic, symm.isOpenEmbedding
-/
lemma isOpenEmbedding_stereographic_symm (hv : ‖v‖ = 1) :
    Topology.IsOpenEmbedding (stereographic hv).symm :=
  (stereographic hv).symm.isOpenEmbedding (by simp)

end StereographicProjection

section ChartedSpace

/-!
### Charted space structure on the sphere

In this section we construct a charted space structure on the unit sphere in a finite-dimensional
real inner product space `E`; that is, we show that it is locally homeomorphic to the Euclidean
space of dimension one less than `E`.

The restriction to finite dimension is for convenience. The most natural `ChartedSpace`
structure for the sphere uses the stereographic projection from the antipodes of a point as the
canonical chart at this point. However, the codomain of the stereographic projection constructed
in the previous section is `(ℝ ∙ v)ᗮ`, the orthogonal complement of the vector `v` in `E` which is
the "north pole" of the projection, so a priori these charts all have different codomains.

So it is necessary to prove that these codomains are all continuously linearly equivalent to a
fixed normed space. This could be proved in general by a simple case of Gram-Schmidt
orthogonalization, but in the finite-dimensional case it follows more easily by dimension-counting.
-/

/--
Definition of `stereographic'` / `stereographic'` 的定义

English:
definition stereographic'
  signature: (n : Nat) [Fact (finrank Real E = n + 1)] (v : sphere (0 : E) 1)
  body: stereographic (norm_eq_of_mem_sphere v) ≫ₕ
    (OrthonormalBasis.fromOrthogonalSpanSingleton n
            (ne_zero_of_mem_unit_sphere v)).repr.toHomeomorph.toOpenPartialHomeomorph

@[simp]

中文:
定义 stereographic'
  签名: (n : 自然数) [Fact (finrank 实数 E = n + 1)] (v : sphere (0 : E) 1)
  定义体: stereographic (norm_eq_of_mem_sphere v) ≫ₕ
    (OrthonormalBasis.fromOrthogonalSpanSingleton n
            (ne_zero_of_mem_unit_sphere v)).repr.toHomeomorph.toOpenPartialHomeomorph

@[simp]

Depends on / 依赖: OrthonormalBasis, OrthonormalBasis.fromOrthogonalSpanSingleton, fromOrthogonalSpanSingleton, ne_zero_of_mem_unit_sphere, norm_eq_of_mem_sphere, repr.toHomeomorph.toOpenPartialHomeomorph, stereographic, toHomeomorph, toOpenPartialHomeomorph
-/
def stereographic' (n : Nat) [Fact (finrank Real E = n + 1)] (v : sphere (0 : E) 1) :
    OpenPartialHomeomorph (sphere (0 : E) 1) (EuclideanSpace Real (Fin n)) :=
  stereographic (norm_eq_of_mem_sphere v) ≫ₕ
    (OrthonormalBasis.fromOrthogonalSpanSingleton n
            (ne_zero_of_mem_unit_sphere v)).repr.toHomeomorph.toOpenPartialHomeomorph

@[simp]
/--
theorem `stereographic'_source` / 定理 `stereographic'_source`

English:
theorem stereographic'_source
  given: {n : Nat} [Fact (finrank Real E = n + 1)] (v : sphere (0 : E) 1)
  proof: by simp [stereographic']

@[simp]

中文:
定理 stereographic'_source
  条件: {n : 自然数} [Fact (finrank 实数 E = n + 1)] (v : sphere (0 : E) 1)
  证明: by simp [stereographic']

@[simp]
-/
theorem stereographic'_source {n : Nat} [Fact (finrank Real E = n + 1)] (v : sphere (0 : E) 1) :
    (stereographic' n v).source = {v}ᶜ := by simp [stereographic']

@[simp]
/--
theorem `stereographic'_target` / 定理 `stereographic'_target`

English:
theorem stereographic'_target
  given: {n : Nat} [Fact (finrank Real E = n + 1)] (v : sphere (0 : E) 1)
  proof: by simp [stereographic']

中文:
定理 stereographic'_target
  条件: {n : 自然数} [Fact (finrank 实数 E = n + 1)] (v : sphere (0 : E) 1)
  证明: by simp [stereographic']
-/
theorem stereographic'_target {n : Nat} [Fact (finrank Real E = n + 1)] (v : sphere (0 : E) 1) :
    (stereographic' n v).target = Set.univ := by simp [stereographic']

/--
Instance `EuclideanSpace.instChartedSpaceSphere` / 实例 `EuclideanSpace.instChartedSpaceSphere`

English:
instance EuclideanSpace.instChartedSpaceSphere
  signature: {n : Nat} [Fact (finrank Real E = n + 1)]
  body: {f | exists v : sphere (0 : E) 1, f = stereographic' n v}
  chartAt v := stereographic' n (-v)
  mem_chart_source v := by simpa using ne_neg_of_mem_unit_sphere Real v
  chart_mem_atlas v := ⟨-v, rfl⟩

中文:
实例 EuclideanSpace.instChartedSpaceSphere
  签名: {n : 自然数} [Fact (finrank 实数 E = n + 1)]
  定义体: {f | exists v : sphere (0 : E) 1, f = stereographic' n v}
  chartAt v := stereographic' n (-v)
  mem_chart_source v := by simpa using ne_neg_of_mem_unit_sphere Real v
  chart_mem_atlas v := ⟨-v, rfl⟩

Depends on / 依赖: sphere, stereographic
-/
instance EuclideanSpace.instChartedSpaceSphere {n : Nat} [Fact (finrank Real E = n + 1)] :
    ChartedSpace (EuclideanSpace Real (Fin n)) (sphere (0 : E) 1) where
  atlas := {f | exists v : sphere (0 : E) 1, f = stereographic' n v}
  chartAt v := stereographic' n (-v)
  mem_chart_source v := by simpa using ne_neg_of_mem_unit_sphere Real v
  chart_mem_atlas v := ⟨-v, rfl⟩

instance (n : Nat) :
    ChartedSpace (EuclideanSpace Real (Fin n)) (sphere (0 : EuclideanSpace Real (Fin (n + 1))) 1) :=
  have := Fact.mk (@finrank_euclideanSpace_fin Real _ (n + 1))
  EuclideanSpace.instChartedSpaceSphere

end ChartedSpace

section ContMDiffManifold

open scoped InnerProductSpace

/--
theorem `sphere_ext_iff` / 定理 `sphere_ext_iff`

English:
theorem sphere_ext_iff
  given: (u v : sphere (0 : E) 1)
  statement: u = v ↔ ⟪(u : E), v⟫_Real = 1
  proof: by
  simp [Subtype.ext_iff, inner_eq_one_iff_of_norm_eq_one]

中文:
定理 sphere_ext_iff
  条件: (u v : sphere (0 : E) 1)
  结论: u = v ↔ ⟪(u : E), v⟫_实数 = 1
  证明: by
  simp [Subtype.ext_iff, inner_eq_one_iff_of_norm_eq_one]

Depends on / 依赖: Subtype, Subtype.ext_iff, ext_iff, inner_eq_one_iff_of_norm_eq_one
-/
theorem sphere_ext_iff (u v : sphere (0 : E) 1) : u = v ↔ ⟪(u : E), v⟫_Real = 1 := by
  simp [Subtype.ext_iff, inner_eq_one_iff_of_norm_eq_one]

/--
theorem `stereographic'_symm_apply` / 定理 `stereographic'_symm_apply`

English:
theorem stereographic'_symm_apply
  statement: {n : Nat} [Fact (finrank Real E = n + 1)] (v : sphere (0 : E) 1)
  proof: (OrthonormalBasis.fromOrthogonalSpanSingleton n (ne_zero_of_mem_unit_sphere v)).repr
      (‖(U.symm x : E)‖ ^ 2 + 4)⁻¹ • (4 : Real) • (U.symm x : E) +
        (‖(U.symm x : E)‖ ^ 2 + 4)⁻¹ • (‖(U.symm x : E)‖ ^ 2 - 4) • v.val := by
  simp [stereographic, stereographic', ← Submodule.coe_norm]

中文:
定理 stereographic'_symm_apply
  结论: {n : 自然数} [Fact (finrank 实数 E = n + 1)] (v : sphere (0 : E) 1)
  证明: (OrthonormalBasis.fromOrthogonalSpanSingleton n (ne_zero_of_mem_unit_sphere v)).repr
      (‖(U.symm x : E)‖ ^ 2 + 4)⁻¹ • (4 : Real) • (U.symm x : E) +
        (‖(U.symm x : E)‖ ^ 2 + 4)⁻¹ • (‖(U.symm x : E)‖ ^ 2 - 4) • v.val := by
  simp [stereographic, stereographic', ← Submodule.coe_norm]
-/
theorem stereographic'_symm_apply {n : Nat} [Fact (finrank Real E = n + 1)] (v : sphere (0 : E) 1)
    (x : EuclideanSpace Real (Fin n)) :
    ((stereographic' n v).symm x : E) =
      let U : (Real ∙ (v : E))ᗮ ≃ₗᵢ[Real] EuclideanSpace Real (Fin n) :=
        (OrthonormalBasis.fromOrthogonalSpanSingleton n (ne_zero_of_mem_unit_sphere v)).repr
      (‖(U.symm x : E)‖ ^ 2 + 4)⁻¹ • (4 : Real) • (U.symm x : E) +
        (‖(U.symm x : E)‖ ^ 2 + 4)⁻¹ • (‖(U.symm x : E)‖ ^ 2 - 4) • v.val := by
  simp [stereographic, stereographic', ← Submodule.coe_norm]

/-! ### Analytic manifold structure on the sphere -/

/--
Instance `EuclideanSpace.instIsManifoldSphere` / 实例 `EuclideanSpace.instIsManifoldSphere`

English:
instance EuclideanSpace.instIsManifoldSphere
  body: isManifold_of_contDiffOn (𝓡 n) ω (sphere (0 : E) 1)
    (by
      rintro _ _ ⟨v, rfl⟩ ⟨v', rfl⟩
      let U :=
        (-- Removed type ascription, and this helped for some reason with timeout issues?
            OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := Real)
            n (ne_zero_of_mem_

中文:
实例 EuclideanSpace.instIsManifoldSphere
  定义体: isManifold_of_contDiffOn (𝓡 n) ω (sphere (0 : E) 1)
    (by
      rintro _ _ ⟨v, rfl⟩ ⟨v', rfl⟩
      let U :=
        (-- Removed type ascription, and this helped for some reason with timeout issues?
            OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := Real)
            n (ne_zero_of_mem_

Depends on / 依赖: OrthonormalBasis, OrthonormalBasis.fromOrthogonalSpanSingleton, Removed, ascription, comp_contDiffOn, contDiff, contDiff.comp_contDiffOn, fromOrthogonalSpanSingleton, helped, isManifold_of_contDiffOn, issues, ne_zero_of_mem_unit_sphere, reason, sphere, timeout
-/
instance EuclideanSpace.instIsManifoldSphere
    {n : Nat} [Fact (finrank Real E = n + 1)] :
    IsManifold (𝓡 n) ω (sphere (0 : E) 1) :=
  isManifold_of_contDiffOn (𝓡 n) ω (sphere (0 : E) 1)
    (by
      rintro _ _ ⟨v, rfl⟩ ⟨v', rfl⟩
      let U :=
        (-- Removed type ascription, and this helped for some reason with timeout issues?
            OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := Real)
            n (ne_zero_of_mem_unit_sphere v)).repr
      let U' :=
        (-- Removed type ascription, and this helped for some reason with timeout issues?
            OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := Real)
            n (ne_zero_of_mem_unit_sphere v')).repr
      have H₁ := U'.contDiff.comp_contDiffOn (contDiffOn_stereoToFun (n := ω))
      -- Porting note: need to help with implicit variables again
      have H₂ := (contDiff_stereoInvFunAux (m := ω) (v := v.val) |>.comp
        (Real ∙ (v : E))ᗮ.subtypeL.contDiff).comp U.symm.contDiff
      convert! H₁.comp_inter (H₂.contDiffOn : ContDiffOn Real ω _ Set.univ) using 1
        -- -- squeezed from `ext, simp [sphere_ext_iff, stereographic'_symm_apply, real_inner_comm]`

      -- -- squeezed from `ext, simp [sphere_ext_iff, stereographic'_symm_apply, real_inner_comm]`
      simp only [OpenPartialHomeomorph.trans_toPartialEquiv,
        OpenPartialHomeomorph.symm_toPartialEquiv, PartialEquiv.trans_source,
        PartialEquiv.symm_source, stereographic'_target, stereographic'_source]
      simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
        Set.range_id, Set.inter_univ, Set.univ_inter, Set.compl_singleton_eq,
        Set.preimage_ofPred_eq]
      simp only [id, comp_apply, OpenPartialHomeomorph.coe_toPartialEquiv_symm,
        innerSL_apply_apply, Ne, sphere_ext_iff, real_inner_comm (v' : E)]
      rfl)

instance (n : Nat) : IsManifold (𝓡 n) ω (sphere (0 : EuclideanSpace Real (Fin (n + 1))) 1) :=
  haveI := Fact.mk (@finrank_euclideanSpace_fin Real _ (n + 1))
  EuclideanSpace.instIsManifoldSphere

/--
theorem `contMDiff_coe_sphere` / 定理 `contMDiff_coe_sphere`

English:
theorem contMDiff_coe_sphere
  given: {m : Nat∞ω} {n : Nat} [Fact (finrank Real E = n + 1)]
  proof: by
  rw [contMDiff_iff]
  constructor
  · exact continuous_subtype_val
  · intro v _
    let U : _ ≃ₗᵢ[Real] _ :=
      (-- Again, partially removing type ascription...
          OrthonormalBasis.fromOrthogonalSpanSingleton
          n (ne_zero_of_mem_unit_sphere (-v))).repr
    exact
      ((contDi

中文:
定理 contMDiff_coe_sphere
  条件: {m : 自然数∞ω} {n : 自然数} [Fact (finrank 实数 E = n + 1)]
  证明: by
  rw [contMDiff_iff]
  constructor
  · exact continuous_subtype_val
  · intro v _
    let U : _ ≃ₗᵢ[Real] _ :=
      (-- Again, partially removing type ascription...
          OrthonormalBasis.fromOrthogonalSpanSingleton
          n (ne_zero_of_mem_unit_sphere (-v))).repr
    exact
      ((contDi

Depends on / 依赖: OrthonormalBasis, OrthonormalBasis.fromOrthogonalSpanSingleton, U.symm.contDiff, ascription, contDiff, contDiffOn, contDiff_stereoInvFunAux, contDiff_stereoInvFunAux.comp, contMDiff_iff, continuous_subtype_val, fromOrthogonalSpanSingleton, ne_zero_of_mem_unit_sphere, partially, removing, subtypeL, subtypeL.contDiff
-/
theorem contMDiff_coe_sphere {m : Nat∞ω} {n : Nat} [Fact (finrank Real E = n + 1)] :
    ContMDiff (𝓡 n) 𝓘(Real, E) m ((↑) : sphere (0 : E) 1 -> E) := by
  rw [contMDiff_iff]
  constructor
  · exact continuous_subtype_val
  · intro v _
    let U : _ ≃ₗᵢ[Real] _ :=
      (-- Again, partially removing type ascription...
          OrthonormalBasis.fromOrthogonalSpanSingleton
          n (ne_zero_of_mem_unit_sphere (-v))).repr
    exact
      ((contDiff_stereoInvFunAux.comp (Real ∙ (-v : E))ᗮ.subtypeL.contDiff).comp
          U.symm.contDiff).contDiffOn

variable {m : Nat∞ω} {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real F H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I m M]

/--
theorem `ContMDiff.codRestrict_sphere` / 定理 `ContMDiff.codRestrict_sphere`

English:
theorem ContMDiff.codRestrict_sphere
  statement: {n : Nat} [Fact (finrank Real E = n + 1)] {f : M -> E}
  proof: by
  rw [contMDiff_iff_target]
  refine ⟨continuous_induced_rng.2 hf.continuous, ?_⟩
  intro v
  let U : _ ≃ₗᵢ[Real] _ :=
    (-- Again, partially removing type ascription... Weird that this helps!
        OrthonormalBasis.fromOrthogonalSpanSingleton
        n (ne_zero_of_mem_unit_sphere (-v))).repr

中文:
定理 ContMDiff.codRestrict_sphere
  结论: {n : 自然数} [Fact (finrank 实数 E = n + 1)] {f : M -> E}
  证明: by
  rw [contMDiff_iff_target]
  refine ⟨continuous_induced_rng.2 hf.continuous, ?_⟩
  intro v
  let U : _ ≃ₗᵢ[Real] _ :=
    (-- Again, partially removing type ascription... Weird that this helps!
        OrthonormalBasis.fromOrthogonalSpanSingleton
        n (ne_zero_of_mem_unit_sphere (-v))).repr

Depends on / 依赖: CMDiff, ContDiffOn, OrthonormalBasis, OrthonormalBasis.fromOrthogonalSpanSingleton, Set.univ, U.contDiff.contDiffOn, ascription, comp_inter, contDiff, contDiffOn, contDiffOn_stereoToFun, contMDiffOn, contMDiff_iff_target, continuous, continuous_induced_rng, convert, fromOrthogonalSpanSingleton, h.comp_inter, hf.contMDiffOn, hf.continuous
-/
theorem ContMDiff.codRestrict_sphere {n : Nat} [Fact (finrank Real E = n + 1)] {f : M -> E}
    (hf : CMDiff m f) (hf' : forall x, f x in sphere (0 : E) 1) :
    CMDiff m (Set.codRestrict _ _ hf' : M -> sphere (0 : E) 1) := by
  rw [contMDiff_iff_target]
  refine ⟨continuous_induced_rng.2 hf.continuous, ?_⟩
  intro v
  let U : _ ≃ₗᵢ[Real] _ :=
    (-- Again, partially removing type ascription... Weird that this helps!
        OrthonormalBasis.fromOrthogonalSpanSingleton
        n (ne_zero_of_mem_unit_sphere (-v))).repr
  have h : ContDiffOn Real ω _ Set.univ := U.contDiff.contDiffOn
  have H₁ := (h.comp_inter contDiffOn_stereoToFun).contMDiffOn
  have H₂ : CMDiff[Set.univ] m f := hf.contMDiffOn
  convert! (H₁.of_le le_top).comp' H₂ using 1
  ext x
  have hfxv : f x = -↑v ↔ ⟪f x, -↑v⟫_Real = 1 := by
    have hfx : ‖f x‖ = 1 := by simpa using hf' x
    rw [inner_eq_one_iff_of_norm_eq_one hfx]
    exact norm_eq_of_mem_sphere (-v)
  simp [chartAt, ChartedSpace.chartAt, Subtype.ext_iff, hfxv, real_inner_comm]

/--
theorem `contMDiff_neg_sphere` / 定理 `contMDiff_neg_sphere`

English:
theorem contMDiff_neg_sphere
  given: {m : Nat∞ω} {n : Nat} [Fact (finrank Real E = n + 1)]
  proof: by
  -- this doesn't elaborate well in term mode
  apply ContMDiff.codRestrict_sphere
  apply contDiff_neg.contMDiff.comp _
  exact contMDiff_coe_sphere

中文:
定理 contMDiff_neg_sphere
  条件: {m : 自然数∞ω} {n : 自然数} [Fact (finrank 实数 E = n + 1)]
  证明: by
  -- this doesn't elaborate well in term mode
  apply ContMDiff.codRestrict_sphere
  apply contDiff_neg.contMDiff.comp _
  exact contMDiff_coe_sphere
-/
theorem contMDiff_neg_sphere {m : Nat∞ω} {n : Nat} [Fact (finrank Real E = n + 1)] :
    CMDiff m fun x : sphere (0 : E) 1 => -x := by
  -- this doesn't elaborate well in term mode
  apply ContMDiff.codRestrict_sphere
  apply contDiff_neg.contMDiff.comp _
  exact contMDiff_coe_sphere

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `stereographic'_neg` / 引理 `stereographic'_neg`

English:
lemma stereographic'_neg
  given: {n : Nat} [Fact (finrank Real E = n + 1)] (v : sphere (0 : E) 1)
  proof: by
  dsimp [stereographic']
  simp only [EmbeddingLike.map_eq_zero_iff]
  apply stereographic_neg_apply

中文:
引理 stereographic'_neg
  条件: {n : 自然数} [Fact (finrank 实数 E = n + 1)] (v : sphere (0 : E) 1)
  证明: by
  dsimp [stereographic']
  simp only [EmbeddingLike.map_eq_zero_iff]
  apply stereographic_neg_apply
-/
private lemma stereographic'_neg {n : Nat} [Fact (finrank Real E = n + 1)] (v : sphere (0 : E) 1) :
    stereographic' n (-v) v = 0 := by
  dsimp [stereographic']
  simp only [EmbeddingLike.map_eq_zero_iff]
  apply stereographic_neg_apply

-- Without this option, the lemmas `EmbeddingLike.map_eq_zero_iff` and `Submodule.range_subtype`
-- are not applied by simp below.
set_option backward.isDefEq.respectTransparency false in
/--
theorem `range_mvfderiv_subtypeVal` / 定理 `range_mvfderiv_subtypeVal`

English:
theorem range_mvfderiv_subtypeVal
  given: {n : Nat} [Fact (finrank Real E = n + 1)] (v : sphere (0 : E) 1)
  proof: by
  rw [((contMDiff_coe_sphere v).mdifferentiableAt one_ne_zero).mvfderiv]
  dsimp [chartAt]
  simp only [fderivWithin_univ, mfld_simps]
  let U := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := Real) n
    (ne_zero_of_mem_unit_sphere (-v))).repr
  suffices
      (fderiv Real ((stereoInvFunAux

中文:
定理 range_mvfderiv_subtypeVal
  条件: {n : 自然数} [Fact (finrank 实数 E = n + 1)] (v : sphere (0 : E) 1)
  证明: by
  rw [((contMDiff_coe_sphere v).mdifferentiableAt one_ne_zero).mvfderiv]
  dsimp [chartAt]
  simp only [fderivWithin_univ, mfld_simps]
  let U := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := Real) n
    (ne_zero_of_mem_unit_sphere (-v))).repr
  suffices
      (fderiv Real ((stereoInvFunAux

Depends on / 依赖: HasFDerivAt, OrthonormalBasis, OrthonormalBasis.fromOrthogonalSpanSingleton, Subtype, Subtype.val, U.symm, _neg, chartAt, contMDiff_coe_sphere, fderiv, fderivWithin_univ, fromOrthogonalSpanSingleton, mdifferentiableAt, mfld_simps, mvfderiv, ne_zero_of_mem_unit_sphere, one_ne_zero, stereoInvFunAux, stereographic
-/
theorem range_mvfderiv_subtypeVal {n : Nat} [Fact (finrank Real E = n + 1)] (v : sphere (0 : E) 1) :
    (mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 -> E) v).range = (Real ∙ (v : E))ᗮ := by
  rw [((contMDiff_coe_sphere v).mdifferentiableAt one_ne_zero).mvfderiv]
  dsimp [chartAt]
  simp only [fderivWithin_univ, mfld_simps]
  let U := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := Real) n
    (ne_zero_of_mem_unit_sphere (-v))).repr
  suffices
      (fderiv Real ((stereoInvFunAux (-v : E) ∘ (↑)) ∘ U.symm) 0).range = (Real ∙ (v : E))ᗮ by
    rw [← this]
    congr 3
    apply stereographic'_neg
  have :
    HasFDerivAt (stereoInvFunAux (-v : E) ∘ (Subtype.val : (Real ∙ (↑(-v) : E))ᗮ -> E))
      (Real ∙ (↑(-v) : E))ᗮ.subtypeL (U.symm 0) := by
    convert! hasFDerivAt_stereoInvFunAux_comp_coe (-v : E)
    simp
  convert! congr($((this.comp 0 U.symm.toContinuousLinearEquiv.hasFDerivAt).fderiv).range)
  symm
  convert!
    (U.symm : EuclideanSpace Real (Fin n) ≃ₗᵢ[Real] (Real ∙ (↑(-v) : E))ᗮ).range_comp
      (Real ∙ (↑(-v) : E))ᗮ.subtype using 1
  simp only [Submodule.range_subtype, coe_neg_sphere]
  congr 1
  -- we must show `Submodule.span ℝ {v} = Submodule.span ℝ {-v}`
  apply Submodule.span_eq_span
  · simp only [Set.singleton_subset_iff, SetLike.mem_coe]
    rw [← Submodule.neg_mem_iff]
    exact Submodule.mem_span_singleton_self (-v : E)
  · simp only [Set.singleton_subset_iff, SetLike.mem_coe]
    rw [Submodule.neg_mem_iff]
    exact Submodule.mem_span_singleton_self (v : E)

@[deprecated range_mvfderiv_subtypeVal (since := "2026-08-02")]
/--
theorem `range_mfderiv_coe_sphere` / 定理 `range_mfderiv_coe_sphere`

English:
theorem range_mfderiv_coe_sphere
  given: {n : Nat} [Fact (finrank Real E = n + 1)] (v : sphere (0 : E) 1)
  proof: by
  convert! range_mvfderiv_subtypeVal v

中文:
定理 range_mfderiv_coe_sphere
  条件: {n : 自然数} [Fact (finrank 实数 E = n + 1)] (v : sphere (0 : E) 1)
  证明: by
  convert! range_mvfderiv_subtypeVal v

Depends on / 依赖: convert, range_mvfderiv_subtypeVal
-/
theorem range_mfderiv_coe_sphere {n : Nat} [Fact (finrank Real E = n + 1)] (v : sphere (0 : E) 1) :
    (mfderiv (𝓡 n) 𝓘(Real, E) ((↑) : sphere (0 : E) 1 -> E) v : TangentSpace (𝓡 n) v ->L[Real] E).range =
      (Real ∙ (v : E))ᗮ := by
  convert! range_mvfderiv_subtypeVal v

/--
theorem `injective_mvfderiv_subtypeVal_sphere` / 定理 `injective_mvfderiv_subtypeVal_sphere`

English:
theorem injective_mvfderiv_subtypeVal_sphere
  statement: {n : Nat} [Fact (finrank Real E = n + 1)]
  proof: by
  rw [((contMDiff_coe_sphere v).mdifferentiableAt one_ne_zero).mvfderiv]
  simp only [chartAt, fderivWithin_univ, mfld_simps]
  let U := (OrthonormalBasis.fromOrthogonalSpanSingleton
      (𝕜 := Real) n (ne_zero_of_mem_unit_sphere (-v))).repr
  suffices Injective (fderiv Real ((stereoInvFunAux (-

中文:
定理 injective_mvfderiv_subtypeVal_sphere
  结论: {n : 自然数} [Fact (finrank 实数 E = n + 1)]
  证明: by
  rw [((contMDiff_coe_sphere v).mdifferentiableAt one_ne_zero).mvfderiv]
  simp only [chartAt, fderivWithin_univ, mfld_simps]
  let U := (OrthonormalBasis.fromOrthogonalSpanSingleton
      (𝕜 := Real) n (ne_zero_of_mem_unit_sphere (-v))).repr
  suffices Injective (fderiv Real ((stereoInvFunAux (-

Depends on / 依赖: HasFDerivAt, Injective, OrthonormalBasis, OrthonormalBasis.fromOrthogonalSpanSingleton, Subtype, Subtype.val, U.symm, _neg, chartAt, contMDiff_coe_sphere, convert, fderiv, fderivWithin_univ, fromOrthogonalSpanSingleton, mdifferentiableAt, mfld_simps, mvfderiv, ne_zero_of_mem_unit_sphere, one_ne_zero, stereoInvFunAux
-/
theorem injective_mvfderiv_subtypeVal_sphere {n : Nat} [Fact (finrank Real E = n + 1)]
    (v : sphere (0 : E) 1) :
    Injective (mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 -> E) v) := by
  rw [((contMDiff_coe_sphere v).mdifferentiableAt one_ne_zero).mvfderiv]
  simp only [chartAt, fderivWithin_univ, mfld_simps]
  let U := (OrthonormalBasis.fromOrthogonalSpanSingleton
      (𝕜 := Real) n (ne_zero_of_mem_unit_sphere (-v))).repr
  suffices Injective (fderiv Real ((stereoInvFunAux (-v : E) ∘ (↑)) ∘ U.symm) 0) by
    convert! this using 3
    congr 2
    apply stereographic'_neg (v := v)
  have : HasFDerivAt (stereoInvFunAux (-v : E) ∘ (Subtype.val : (Real ∙ (↑(-v) : E))ᗮ -> E))
      (Real ∙ (↑(-v) : E))ᗮ.subtypeL (U.symm 0) := by
    convert! hasFDerivAt_stereoInvFunAux_comp_coe (-v : E)
    -- Otherwise, the lemma `EmbeddingLike.map_eq_zero_iff` is not applied.
    set_option backward.isDefEq.respectTransparency false in
    simp
have := congr_arg DFunLike.coe (this.comp 0 U.symm.toContinuousLinearEquiv.hasFDerivAt).fderiv
  refine Eq.subst this.symm ?_
  rw [ContinuousLinearMap.coe_comp]; rw [ContinuousLinearEquiv.coe_coe]
  set_option backward.isDefEq.respectTransparency false in
  simpa [-Subtype.val_injective] using Subtype.val_injective

@[deprecated injective_mvfderiv_subtypeVal_sphere (since := "2026-08-02")]
/--
theorem `mfderiv_coe_sphere_injective` / 定理 `mfderiv_coe_sphere_injective`

English:
theorem mfderiv_coe_sphere_injective
  given: {n : Nat} [Fact (finrank Real E = n + 1)] (v : sphere (0 : E) 1)
  proof: by
  convert! injective_mvfderiv_subtypeVal_sphere v

中文:
定理 mfderiv_coe_sphere_injective
  条件: {n : 自然数} [Fact (finrank 实数 E = n + 1)] (v : sphere (0 : E) 1)
  证明: by
  convert! injective_mvfderiv_subtypeVal_sphere v

Depends on / 依赖: convert, injective_mvfderiv_subtypeVal_sphere
-/
theorem mfderiv_coe_sphere_injective {n : Nat} [Fact (finrank Real E = n + 1)] (v : sphere (0 : E) 1) :
    Injective (mfderiv (𝓡 n) 𝓘(Real, E) ((↑) : sphere (0 : E) 1 -> E) v) := by
  convert! injective_mvfderiv_subtypeVal_sphere v

end ContMDiffManifold

section Circle

open Complex

/--
theorem `finrank_real_complex_fact'` / 定理 `finrank_real_complex_fact'`

English:
theorem finrank_real_complex_fact'
  statement: Fact (finrank Real Complex = 1 + 1)
  proof: finrank_real_complex_fact

中文:
定理 finrank_real_complex_fact'
  结论: Fact (finrank 实数 Complex = 1 + 1)
  证明: finrank_real_complex_fact

Depends on / 依赖: finrank_real_complex_fact
-/
theorem finrank_real_complex_fact' : Fact (finrank Real Complex = 1 + 1) :=
  finrank_real_complex_fact

attribute [local instance] finrank_real_complex_fact'

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ChartedSpace (EuclideanSpace Real (Fin 1)) Circle
  body: inferInstanceAs ChartedSpace _ (sphere _ _)

中文:
实例 :
  签名: ChartedSpace (EuclideanSpace 实数 (Fin 1)) Circle
  定义体: inferInstanceAs ChartedSpace _ (sphere _ _)

Depends on / 依赖: ChartedSpace, sphere
-/
instance : ChartedSpace (EuclideanSpace Real (Fin 1)) Circle :=
inferInstanceAs ChartedSpace _ (sphere _ _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsManifold (𝓡 1) ω Circle
  body: EuclideanSpace.instIsManifoldSphere (E := Complex)

中文:
实例 :
  签名: IsManifold (𝓡 1) ω Circle
  定义体: EuclideanSpace.instIsManifoldSphere (E := Complex)

Depends on / 依赖: EuclideanSpace, EuclideanSpace.instIsManifoldSphere, instIsManifoldSphere
-/
instance : IsManifold (𝓡 1) ω Circle :=
  EuclideanSpace.instIsManifoldSphere (E := Complex)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LieGroup (𝓡 1) ω Circle
  body: by
    apply ContMDiff.codRestrict_sphere
    let c : Circle -> Complex := (↑)
    have h₂ : ContMDiff (𝓘(Real, Complex).prod 𝓘(Real, Complex)) 𝓘(Real, Complex) ω fun z : Complex × Complex => z.fst * z.snd := by
      rw [contMDiff_iff]
      exact ⟨continuous_mul, fun x y => contDiff_mul.contDiffOn

中文:
实例 :
  签名: LieGroup (𝓡 1) ω Circle
  定义体: by
    apply ContMDiff.codRestrict_sphere
    let c : Circle -> Complex := (↑)
    have h₂ : ContMDiff (𝓘(Real, Complex).prod 𝓘(Real, Complex)) 𝓘(Real, Complex) ω fun z : Complex × Complex => z.fst * z.snd := by
      rw [contMDiff_iff]
      exact ⟨continuous_mul, fun x y => contDiff_mul.contDiffOn

Depends on / 依赖: Circle, ContMDiff, ContMDiff.codRestrict_sphere, codRestrict_sphere, contDiffOn, contDiff_mul, contDiff_mul.contDiffOn, contMDiff_iff, continuous_mul, z.fst, z.snd
-/
instance : LieGroup (𝓡 1) ω Circle where
  contMDiff_mul := by
    apply ContMDiff.codRestrict_sphere
    let c : Circle -> Complex := (↑)
    have h₂ : ContMDiff (𝓘(Real, Complex).prod 𝓘(Real, Complex)) 𝓘(Real, Complex) ω fun z : Complex × Complex => z.fst * z.snd := by
      rw [contMDiff_iff]
      exact ⟨continuous_mul, fun x y => contDiff_mul.contDiffOn⟩
    -- TODO bug: filling in ω yields an error; expected type has metavariables...
    suffices h₁ : ContMDiff _ _ _ (Prod.map c c) from
      h₂.comp h₁
    apply ContMDiff.prodMap <;> exact contMDiff_coe_sphere
  contMDiff_inv := by
    apply ContMDiff.codRestrict_sphere
    simp only [← Circle.coe_inv, Circle.coe_inv_eq_conj]
    exact Complex.conjCLE.contDiff.contMDiff.comp contMDiff_coe_sphere

/--
theorem `contMDiff_circleExp` / 定理 `contMDiff_circleExp`

English:
theorem contMDiff_circleExp
  given: {m : Nat∞ω}
  statement: CMDiff m Circle.exp
  proof: (contDiff_exp.comp (contDiff_id.smul contDiff_const)).contMDiff.codRestrict_sphere _

中文:
定理 contMDiff_circleExp
  条件: {m : 自然数∞ω}
  结论: CMDiff m Circle.exp
  证明: (contDiff_exp.comp (contDiff_id.smul contDiff_const)).contMDiff.codRestrict_sphere _

Depends on / 依赖: codRestrict_sphere, contDiff_const, contDiff_exp, contDiff_exp.comp, contDiff_id, contDiff_id.smul, contMDiff, contMDiff.codRestrict_sphere
-/
theorem contMDiff_circleExp {m : Nat∞ω} : CMDiff m Circle.exp :=
  (contDiff_exp.comp (contDiff_id.smul contDiff_const)).contMDiff.codRestrict_sphere _

end Circle
