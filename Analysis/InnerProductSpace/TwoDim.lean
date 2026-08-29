/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.Orientation
public import Mathlib.LinearAlgebra.Alternating.Curry
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.Complex.Orientation
public import Mathlib.Tactic.LinearCombination

/-!
# Oriented two-dimensional real inner product spaces

This file defines constructions specific to the geometry of an oriented two-dimensional real inner
product space `E`.

## Main declarations

* `Orientation.areaForm`: an antisymmetric bilinear form `E →ₗ[ℝ] E →ₗ[ℝ] ℝ` (usual notation `ω`).
  Morally, when `ω` is evaluated on two vectors, it gives the oriented area of the parallelogram
  they span. (But mathlib does not yet have a construction of oriented area, and in fact the
  construction of oriented area should pass through `ω`.)

* `Orientation.rightAngleRotation`: an isometric automorphism `E ≃ₗᵢ[ℝ] E` (usual notation `J`).
  This automorphism squares to -1. In a later file, rotations (`Orientation.rotation`) are defined,
  in such a way that this automorphism is equal to rotation by 90 degrees.

* `Orientation.basisRightAngleRotation`: for a nonzero vector `x` in `E`, the basis `![x, J x]`
  for `E`.

* `Orientation.kahler`: a complex-valued real-bilinear map `E →ₗ[ℝ] E →ₗ[ℝ] ℂ`. Its real part is the
  inner product and its imaginary part is `Orientation.areaForm`. For vectors `x` and `y` in `E`,
  the complex number `o.kahler x y` has modulus `‖x‖ * ‖y‖`. In a later file, oriented angles
  (`Orientation.oangle`) are defined, in such a way that the argument of `o.kahler x y` is the
  oriented angle from `x` to `y`.

## Main results

* `Orientation.rightAngleRotation_rightAngleRotation`: the identity `J (J x) = - x`

* `Orientation.nonneg_inner_and_areaForm_eq_zero_iff_sameRay`: `x`, `y` are in the same ray, if
  and only if `0 ≤ ⟪x, y⟫` and `ω x y = 0`

* `Orientation.kahler_mul`: the identity `o.kahler x a * o.kahler a y = ‖a‖ ^ 2 * o.kahler x y`

* `Complex.areaForm`, `Complex.rightAngleRotation`, `Complex.kahler`: the concrete
  interpretations of `areaForm`, `rightAngleRotation`, `kahler` for the oriented real inner
  product space `ℂ`

* `Orientation.areaForm_map_complex`, `Orientation.rightAngleRotation_map_complex`,
  `Orientation.kahler_map_complex`: given an orientation-preserving isometry from `E` to `ℂ`,
  expressions for `areaForm`, `rightAngleRotation`, `kahler` as the pullback of their concrete
  interpretations on `ℂ`

## Implementation notes

Notation `ω` for `Orientation.areaForm` and `J` for `Orientation.rightAngleRotation` should be
defined locally in each file which uses them, since otherwise one would need a more cumbersome
notation which mentions the orientation explicitly (something like `ω[o]`). Write

```
local notation "ω" => o.areaForm
local notation "J" => o.rightAngleRotation
```

-/

@[expose] public section


noncomputable section

open scoped RealInnerProductSpace ComplexConjugate

open Module

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E] [Fact (finrank Real E = 2)]
  (o : Orientation Real E (Fin 2))

namespace Orientation

/-- An antisymmetric bilinear form on an oriented real inner product space of dimension 2 (usual
notation `ω`). When evaluated on two vectors, it gives the oriented area of the parallelogram they
span. -/
irreducible_def areaForm : E ->ₗ[Real] E ->ₗ[Real] Real := by
  let z : E [⋀^Fin 0]->ₗ[Real] Real ≃ₗ[Real] Real :=
    AlternatingMap.constLinearEquivOfIsEmpty.symm
  let y : E [⋀^Fin 1]->ₗ[Real] Real ->ₗ[Real] E ->ₗ[Real] Real :=
    LinearMap.llcomp Real E (E [⋀^Fin 0]->ₗ[Real] Real) Real z ∘ₗ AlternatingMap.curryLeftLinearMap
  exact y ∘ₗ AlternatingMap.curryLeftLinearMap o.volumeForm

local notation "ω" => o.areaForm

/--
theorem `areaForm_to_volumeForm` / 定理 `areaForm_to_volumeForm`

English:
theorem areaForm_to_volumeForm
  given: (x y : E)
  statement: ω x y = o.volumeForm ![x, y]
  proof: by simp [areaForm]

@[simp]

中文:
定理 areaForm_to_volumeForm
  条件: (x y : E)
  结论: ω x y = o.volumeForm ![x, y]
  证明: by simp [areaForm]

@[simp]

Depends on / 依赖: areaForm
-/
theorem areaForm_to_volumeForm (x y : E) : ω x y = o.volumeForm ![x, y] := by simp [areaForm]

@[simp]
/--
theorem `areaForm_apply_self` / 定理 `areaForm_apply_self`

English:
theorem areaForm_apply_self
  given: (x : E)
  statement: ω x x = 0
  proof: by
  rw [areaForm_to_volumeForm]
  refine o.volumeForm.map_eq_zero_of_eq ![x, x] ?_ (?_ : (0 : Fin 2) != 1)
  · simp
  · simp

中文:
定理 areaForm_apply_self
  条件: (x : E)
  结论: ω x x = 0
  证明: by
  rw [areaForm_to_volumeForm]
  refine o.volumeForm.map_eq_zero_of_eq ![x, x] ?_ (?_ : (0 : Fin 2) != 1)
  · simp
  · simp

Depends on / 依赖: areaForm_to_volumeForm, map_eq_zero_of_eq, o.volumeForm.map_eq_zero_of_eq, volumeForm
-/
theorem areaForm_apply_self (x : E) : ω x x = 0 := by
  rw [areaForm_to_volumeForm]
  refine o.volumeForm.map_eq_zero_of_eq ![x, x] ?_ (?_ : (0 : Fin 2) != 1)
  · simp
  · simp

/--
theorem `areaForm_swap` / 定理 `areaForm_swap`

English:
theorem areaForm_swap
  given: (x y : E)
  statement: ω x y = -ω y x
  proof: by
  simp only [areaForm_to_volumeForm]
  convert! o.volumeForm.map_swap ![y, x] (_ : (0 : Fin 2) != 1)
  · ext i
    fin_cases i <;> rfl
  · simp

@[simp]

中文:
定理 areaForm_swap
  条件: (x y : E)
  结论: ω x y = -ω y x
  证明: by
  simp only [areaForm_to_volumeForm]
  convert! o.volumeForm.map_swap ![y, x] (_ : (0 : Fin 2) != 1)
  · ext i
    fin_cases i <;> rfl
  · simp

@[simp]

Depends on / 依赖: areaForm_to_volumeForm, convert, fin_cases, map_swap, o.volumeForm.map_swap, volumeForm
-/
theorem areaForm_swap (x y : E) : ω x y = -ω y x := by
  simp only [areaForm_to_volumeForm]
  convert! o.volumeForm.map_swap ![y, x] (_ : (0 : Fin 2) != 1)
  · ext i
    fin_cases i <;> rfl
  · simp

@[simp]
/--
theorem `areaForm_neg_orientation` / 定理 `areaForm_neg_orientation`

English:
theorem areaForm_neg_orientation
  statement: (-o).areaForm = -o.areaForm
  proof: by
  ext x y
  simp [areaForm_to_volumeForm]

中文:
定理 areaForm_neg_orientation
  结论: (-o).areaForm = -o.areaForm
  证明: by
  ext x y
  simp [areaForm_to_volumeForm]

Depends on / 依赖: areaForm_to_volumeForm
-/
theorem areaForm_neg_orientation : (-o).areaForm = -o.areaForm := by
  ext x y
  simp [areaForm_to_volumeForm]

/--
Definition of `areaForm'` / `areaForm'` 的定义

English:
definition areaForm'
  signature: : E ->L[Real] E ->L[Real] Real
  body: LinearMap.toContinuousLinearMap
    (↑(LinearMap.toContinuousLinearMap : (E ->ₗ[Real] Real) ≃ₗ[Real] E ->L[Real] Real) ∘ₗ o.areaForm)

@[simp]

中文:
定义 areaForm'
  签名: : E ->L[实数] E ->L[实数] 实数
  定义体: LinearMap.toContinuousLinearMap
    (↑(LinearMap.toContinuousLinearMap : (E ->ₗ[Real] Real) ≃ₗ[Real] E ->L[Real] Real) ∘ₗ o.areaForm)

@[simp]

Depends on / 依赖: LinearMap, LinearMap.toContinuousLinearMap, areaForm, o.areaForm, toContinuousLinearMap
-/
def areaForm' : E ->L[Real] E ->L[Real] Real :=
  LinearMap.toContinuousLinearMap
    (↑(LinearMap.toContinuousLinearMap : (E ->ₗ[Real] Real) ≃ₗ[Real] E ->L[Real] Real) ∘ₗ o.areaForm)

@[simp]
/--
theorem `areaForm'_apply` / 定理 `areaForm'_apply`

English:
theorem areaForm'_apply
  given: (x : E)
  proof: rfl

中文:
定理 areaForm'_apply
  条件: (x : E)
  证明: rfl
-/
theorem areaForm'_apply (x : E) :
    o.areaForm' x = LinearMap.toContinuousLinearMap (o.areaForm x) :=
  rfl

/--
theorem `abs_areaForm_le` / 定理 `abs_areaForm_le`

English:
theorem abs_areaForm_le
  given: (x y : E)
  statement: |ω x y| <= ‖x‖ * ‖y‖
  proof: by
  simpa [areaForm_to_volumeForm, Fin.prod_univ_succ] using o.abs_volumeForm_apply_le ![x, y]

中文:
定理 abs_areaForm_le
  条件: (x y : E)
  结论: |ω x y| <= ‖x‖ * ‖y‖
  证明: by
  simpa [areaForm_to_volumeForm, Fin.prod_univ_succ] using o.abs_volumeForm_apply_le ![x, y]

Depends on / 依赖: Fin.prod_univ_succ, abs_volumeForm_apply_le, areaForm_to_volumeForm, o.abs_volumeForm_apply_le, prod_univ_succ
-/
theorem abs_areaForm_le (x y : E) : |ω x y| <= ‖x‖ * ‖y‖ := by
  simpa [areaForm_to_volumeForm, Fin.prod_univ_succ] using o.abs_volumeForm_apply_le ![x, y]

/--
theorem `areaForm_le` / 定理 `areaForm_le`

English:
theorem areaForm_le
  given: (x y : E)
  statement: ω x y <= ‖x‖ * ‖y‖
  proof: by
  simpa [areaForm_to_volumeForm, Fin.prod_univ_succ] using o.volumeForm_apply_le ![x, y]

中文:
定理 areaForm_le
  条件: (x y : E)
  结论: ω x y <= ‖x‖ * ‖y‖
  证明: by
  simpa [areaForm_to_volumeForm, Fin.prod_univ_succ] using o.volumeForm_apply_le ![x, y]

Depends on / 依赖: Fin.prod_univ_succ, areaForm_to_volumeForm, o.volumeForm_apply_le, prod_univ_succ, volumeForm_apply_le
-/
theorem areaForm_le (x y : E) : ω x y <= ‖x‖ * ‖y‖ := by
  simpa [areaForm_to_volumeForm, Fin.prod_univ_succ] using o.volumeForm_apply_le ![x, y]

/--
theorem `abs_areaForm_of_orthogonal` / 定理 `abs_areaForm_of_orthogonal`

English:
theorem abs_areaForm_of_orthogonal
  given: {x y : E} (h : ⟪x, y⟫ = 0)
  statement: |ω x y| = ‖x‖ * ‖y‖
  proof: by
  rw [o.areaForm_to_volumeForm]; rw [o.abs_volumeForm_apply_of_pairwise_orthogonal]
  · simp [Fin.prod_univ_succ]
  intro i j hij
  fin_cases i <;> fin_cases j
  · simp_all
  · simpa using h
  · simpa [real_inner_comm] using h
  · simp_all

中文:
定理 abs_areaForm_of_orthogonal
  条件: {x y : E} (h : ⟪x, y⟫ = 0)
  结论: |ω x y| = ‖x‖ * ‖y‖
  证明: by
  rw [o.areaForm_to_volumeForm]; rw [o.abs_volumeForm_apply_of_pairwise_orthogonal]
  · simp [Fin.prod_univ_succ]
  intro i j hij
  fin_cases i <;> fin_cases j
  · simp_all
  · simpa using h
  · simpa [real_inner_comm] using h
  · simp_all

Depends on / 依赖: Fin.prod_univ_succ, abs_volumeForm_apply_of_pairwise_orthogonal, areaForm_to_volumeForm, fin_cases, o.abs_volumeForm_apply_of_pairwise_orthogonal, o.areaForm_to_volumeForm, prod_univ_succ, real_inner_comm
-/
theorem abs_areaForm_of_orthogonal {x y : E} (h : ⟪x, y⟫ = 0) : |ω x y| = ‖x‖ * ‖y‖ := by
  rw [o.areaForm_to_volumeForm]; rw [o.abs_volumeForm_apply_of_pairwise_orthogonal]
  · simp [Fin.prod_univ_succ]
  intro i j hij
  fin_cases i <;> fin_cases j
  · simp_all
  · simpa using h
  · simpa [real_inner_comm] using h
  · simp_all

/--
theorem `areaForm_map` / 定理 `areaForm_map`

English:
theorem areaForm_map
  statement: {F : Type*} [NormedAddCommGroup F] [InnerProductSpace Real F]
  proof: by
  have : φ.symm ∘ ![x, y] = ![φ.symm x, φ.symm y] := by
    ext i
    fin_cases i <;> rfl
  simp [areaForm_to_volumeForm, volumeForm_map, this]

中文:
定理 areaForm_map
  结论: {F : 类型} [赋范交换加群 F] [内积空间 实数 F]
  证明: by
  have : φ.symm ∘ ![x, y] = ![φ.symm x, φ.symm y] := by
    ext i
    fin_cases i <;> rfl
  simp [areaForm_to_volumeForm, volumeForm_map, this]

Depends on / 依赖: areaForm_to_volumeForm, fin_cases, volumeForm_map
-/
theorem areaForm_map {F : Type*} [NormedAddCommGroup F] [InnerProductSpace Real F]
    [hF : Fact (finrank Real F = 2)] (φ : E ≃ₗᵢ[Real] F) (x y : F) :
    (Orientation.map (Fin 2) φ.toLinearEquiv o).areaForm x y =
    o.areaForm (φ.symm x) (φ.symm y) := by
  have : φ.symm ∘ ![x, y] = ![φ.symm x, φ.symm y] := by
    ext i
    fin_cases i <;> rfl
  simp [areaForm_to_volumeForm, volumeForm_map, this]

/--
theorem `areaForm_comp_linearIsometryEquiv` / 定理 `areaForm_comp_linearIsometryEquiv`

English:
theorem areaForm_comp_linearIsometryEquiv
  statement: (φ : E ≃ₗᵢ[Real] E)
  proof: by
  convert! o.areaForm_map φ (φ x) (φ y)
  · symm
    rwa [← o.map_eq_iff_det_pos φ.toLinearEquiv] at hφ
    rw [@Fact.out (finrank Real E = 2)]; rw [Fintype.card_fin]
  · simp
  · simp

中文:
定理 areaForm_comp_linearIsometryEquiv
  结论: (φ : E ≃ₗᵢ[实数] E)
  证明: by
  convert! o.areaForm_map φ (φ x) (φ y)
  · symm
    rwa [← o.map_eq_iff_det_pos φ.toLinearEquiv] at hφ
    rw [@Fact.out (finrank Real E = 2)]; rw [Fintype.card_fin]
  · simp
  · simp

Depends on / 依赖: Fact.out, Fintype, Fintype.card_fin, areaForm_map, card_fin, convert, finrank, map_eq_iff_det_pos, o.areaForm_map, o.map_eq_iff_det_pos, toLinearEquiv
-/
theorem areaForm_comp_linearIsometryEquiv (φ : E ≃ₗᵢ[Real] E)
    (hφ : 0 < LinearMap.det (φ.toLinearEquiv : E ->ₗ[Real] E)) (x y : E) :
    o.areaForm (φ x) (φ y) = o.areaForm x y := by
  convert! o.areaForm_map φ (φ x) (φ y)
  · symm
    rwa [← o.map_eq_iff_det_pos φ.toLinearEquiv] at hφ
    rw [@Fact.out (finrank Real E = 2)]; rw [Fintype.card_fin]
  · simp
  · simp

/-- Auxiliary construction for `Orientation.rightAngleRotation`, rotation by 90 degrees in an
oriented real inner product space of dimension 2. -/
irreducible_def rightAngleRotationAux₁ : E ->ₗ[Real] E :=
  let to_dual : E ≃ₗ[Real] E ->ₗ[Real] Real :=
    (InnerProductSpace.toDual Real E).toLinearEquiv ≪≫ₗ LinearMap.toContinuousLinearMap.symm
  ↑to_dual.symm ∘ₗ ω

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `inner_rightAngleRotationAux₁_left` / 定理 `inner_rightAngleRotationAux₁_left`

English:
theorem inner_rightAngleRotationAux₁_left
  given: (x y : E)
  statement: ⟪o.rightAngleRotationAux₁ x, y⟫ = ω x y
  proof: by
  simp only [rightAngleRotationAux₁, LinearEquiv.trans_symm, LinearEquiv.symm_symm,
    LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.trans_apply,
    LinearIsometryEquiv.coe_symm_toLinearEquiv]
  rw [InnerProductSpace.toDual_symm_apply]
  norm_cast

@[simp]

中文:
定理 inner_rightAngleRotationAux₁_left
  条件: (x y : E)
  结论: ⟪o.rightAngleRotationAux₁ x, y⟫ = ω x y
  证明: by
  simp only [rightAngleRotationAux₁, LinearEquiv.trans_symm, LinearEquiv.symm_symm,
    LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.trans_apply,
    LinearIsometryEquiv.coe_symm_toLinearEquiv]
  rw [InnerProductSpace.toDual_symm_apply]
  norm_cast

@[simp]

Depends on / 依赖: Function, Function.comp_apply, InnerProductSpace, InnerProductSpace.toDual_symm_apply, LinearEquiv, LinearEquiv.coe_coe, LinearEquiv.symm_symm, LinearEquiv.trans_apply, LinearEquiv.trans_symm, LinearIsometryEquiv, LinearIsometryEquiv.coe_symm_toLinearEquiv, LinearMap, LinearMap.coe_comp, coe_coe, coe_comp, coe_symm_toLinearEquiv, comp_apply, symm_symm, toDual_symm_apply, trans_apply
-/
theorem inner_rightAngleRotationAux₁_left (x y : E) : ⟪o.rightAngleRotationAux₁ x, y⟫ = ω x y := by
  simp only [rightAngleRotationAux₁, LinearEquiv.trans_symm, LinearEquiv.symm_symm,
    LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.trans_apply,
    LinearIsometryEquiv.coe_symm_toLinearEquiv]
  rw [InnerProductSpace.toDual_symm_apply]
  norm_cast

@[simp]
/--
theorem `inner_rightAngleRotationAux₁_right` / 定理 `inner_rightAngleRotationAux₁_right`

English:
theorem inner_rightAngleRotationAux₁_right
  given: (x y : E)
  proof: by
  rw [real_inner_comm]
  simp [o.areaForm_swap y x]

中文:
定理 inner_rightAngleRotationAux₁_right
  条件: (x y : E)
  证明: by
  rw [real_inner_comm]
  simp [o.areaForm_swap y x]

Depends on / 依赖: areaForm_swap, o.areaForm_swap, real_inner_comm
-/
theorem inner_rightAngleRotationAux₁_right (x y : E) :
    ⟪x, o.rightAngleRotationAux₁ y⟫ = -ω x y := by
  rw [real_inner_comm]
  simp [o.areaForm_swap y x]

/--
Definition of `rightAngleRotationAux₂` / `rightAngleRotationAux₂` 的定义

English:
definition rightAngleRotationAux₂
  signature: : E ->ₗᵢ[Real] E
  body: { o.rightAngleRotationAux₁ with
    norm_map' := fun x => by
      refine le_antisymm ?_ ?_
      · rcases eq_or_lt_of_le (norm_nonneg (o.rightAngleRotationAux₁ x)) with h | h
        · rw [← h]
          positivity
        refine le_of_mul_le_mul_right ?_ h
        rw [← real_inner_self_eq_norm_mul

中文:
定义 rightAngleRotationAux₂
  签名: : E ->ₗᵢ[实数] E
  定义体: { o.rightAngleRotationAux₁ with
    norm_map' := fun x => by
      refine le_antisymm ?_ ?_
      · rcases eq_or_lt_of_le (norm_nonneg (o.rightAngleRotationAux₁ x)) with h | h
        · rw [← h]
          positivity
        refine le_of_mul_le_mul_right ?_ h
        rw [← real_inner_self_eq_norm_mul

Depends on / 依赖: Finset, Finset.card, Nontrivial, Submodule, areaForm_le, eq_or_lt_of_le, finrank, le_antisymm, le_of_mul_le_mul_right, nontrivial_of_finrank_pos, norm_map, norm_nonneg, o.areaForm_le, o.inner_rightAngleRotationAux, o.rightAngleRotationAux, real_inner_self_eq_norm_mul_norm
-/
def rightAngleRotationAux₂ : E ->ₗᵢ[Real] E :=
  { o.rightAngleRotationAux₁ with
    norm_map' := fun x => by
      refine le_antisymm ?_ ?_
      · rcases eq_or_lt_of_le (norm_nonneg (o.rightAngleRotationAux₁ x)) with h | h
        · rw [← h]
          positivity
        refine le_of_mul_le_mul_right ?_ h
        rw [← real_inner_self_eq_norm_mul_norm]; rw [o.inner_rightAngleRotationAux₁_left]
        exact o.areaForm_le x (o.rightAngleRotationAux₁ x)
      · let K : Submodule Real E := Real ∙ x
        have : Nontrivial Kᗮ := by
          apply nontrivial_of_finrank_pos (R := Real)
          have : finrank Real K <= Finset.card {x} := by
            rw [← Set.toFinset_singleton]
            exact finrank_span_le_card ({x} : Set E)
          have : Finset.card {x} = 1 := Finset.card_singleton x
          have : finrank Real K + finrank Real Kᗮ = finrank Real E := K.finrank_add_finrank_orthogonal
          have : finrank Real E = 2 := Fact.out
          lia
        obtain ⟨w, hw₀⟩ : exists w : Kᗮ, w != 0 := exists_ne 0
        have hw' : ⟪x, (w : E)⟫ = 0 := Submodule.mem_orthogonal_singleton_iff_inner_right.mp w.2
        have hw : (w : E) != 0 := fun h => hw₀ (Submodule.coe_eq_zero.mp h)
        refine le_of_mul_le_mul_right ?_ (by rwa [norm_pos_iff] : 0 < ‖(w : E)‖)
        rw [← o.abs_areaForm_of_orthogonal hw']
        rw [← o.inner_rightAngleRotationAux₁_left x w]
        exact abs_real_inner_le_norm (o.rightAngleRotationAux₁ x) w }

@[simp]
/--
theorem `rightAngleRotationAux₁_rightAngleRotationAux₁` / 定理 `rightAngleRotationAux₁_rightAngleRotationAux₁`

English:
theorem rightAngleRotationAux₁_rightAngleRotationAux₁
  given: (x : E)
  proof: by
  apply ext_inner_left Real
  intro y
  have : ⟪o.rightAngleRotationAux₁ y, o.rightAngleRotationAux₁ x⟫ = ⟪y, x⟫ :=
    LinearIsometry.inner_map_map o.rightAngleRotationAux₂ y x
  rw [o.inner_rightAngleRotationAux₁_right]; rw [← o.inner_rightAngleRotationAux₁_left]; rw [this]; rw [inner_neg_right

中文:
定理 rightAngleRotationAux₁_rightAngleRotationAux₁
  条件: (x : E)
  证明: by
  apply ext_inner_left Real
  intro y
  have : ⟪o.rightAngleRotationAux₁ y, o.rightAngleRotationAux₁ x⟫ = ⟪y, x⟫ :=
    LinearIsometry.inner_map_map o.rightAngleRotationAux₂ y x
  rw [o.inner_rightAngleRotationAux₁_right]; rw [← o.inner_rightAngleRotationAux₁_left]; rw [this]; rw [inner_neg_right

Depends on / 依赖: LinearIsometry, LinearIsometry.inner_map_map, ext_inner_left, inner_map_map, inner_neg_right, o.inner_rightAngleRotationAux, o.rightAngleRotationAux
-/
theorem rightAngleRotationAux₁_rightAngleRotationAux₁ (x : E) :
    o.rightAngleRotationAux₁ (o.rightAngleRotationAux₁ x) = -x := by
  apply ext_inner_left Real
  intro y
  have : ⟪o.rightAngleRotationAux₁ y, o.rightAngleRotationAux₁ x⟫ = ⟪y, x⟫ :=
    LinearIsometry.inner_map_map o.rightAngleRotationAux₂ y x
  rw [o.inner_rightAngleRotationAux₁_right]; rw [← o.inner_rightAngleRotationAux₁_left]; rw [this]; rw [inner_neg_right]

/-- An isometric automorphism of an oriented real inner product space of dimension 2 (usual notation
`J`). This automorphism squares to -1. We will define rotations in such a way that this
automorphism is equal to rotation by 90 degrees. -/
irreducible_def rightAngleRotation : E ≃ₗᵢ[Real] E :=
  LinearIsometryEquiv.ofLinearIsometry o.rightAngleRotationAux₂ (-o.rightAngleRotationAux₁)
    (by ext; simp [rightAngleRotationAux₂]) (by ext; simp [rightAngleRotationAux₂])

local notation "J" => o.rightAngleRotation

@[simp]
/--
theorem `inner_rightAngleRotation_left` / 定理 `inner_rightAngleRotation_left`

English:
theorem inner_rightAngleRotation_left
  given: (x y : E)
  statement: ⟪J x, y⟫ = ω x y
  proof: by
  rw [rightAngleRotation]
  exact o.inner_rightAngleRotationAux₁_left x y

@[simp]

中文:
定理 inner_rightAngleRotation_left
  条件: (x y : E)
  结论: ⟪J x, y⟫ = ω x y
  证明: by
  rw [rightAngleRotation]
  exact o.inner_rightAngleRotationAux₁_left x y

@[simp]

Depends on / 依赖: o.inner_rightAngleRotationAux, rightAngleRotation
-/
theorem inner_rightAngleRotation_left (x y : E) : ⟪J x, y⟫ = ω x y := by
  rw [rightAngleRotation]
  exact o.inner_rightAngleRotationAux₁_left x y

@[simp]
/--
theorem `inner_rightAngleRotation_right` / 定理 `inner_rightAngleRotation_right`

English:
theorem inner_rightAngleRotation_right
  given: (x y : E)
  statement: ⟪x, J y⟫ = -ω x y
  proof: by
  rw [rightAngleRotation]
  exact o.inner_rightAngleRotationAux₁_right x y

@[simp]

中文:
定理 inner_rightAngleRotation_right
  条件: (x y : E)
  结论: ⟪x, J y⟫ = -ω x y
  证明: by
  rw [rightAngleRotation]
  exact o.inner_rightAngleRotationAux₁_right x y

@[simp]

Depends on / 依赖: o.inner_rightAngleRotationAux, rightAngleRotation
-/
theorem inner_rightAngleRotation_right (x y : E) : ⟪x, J y⟫ = -ω x y := by
  rw [rightAngleRotation]
  exact o.inner_rightAngleRotationAux₁_right x y

@[simp]
/--
theorem `rightAngleRotation_rightAngleRotation` / 定理 `rightAngleRotation_rightAngleRotation`

English:
theorem rightAngleRotation_rightAngleRotation
  given: (x : E)
  statement: J (J x) = -x
  proof: by
  rw [rightAngleRotation]
  exact o.rightAngleRotationAux₁_rightAngleRotationAux₁ x

@[simp]

中文:
定理 rightAngleRotation_rightAngleRotation
  条件: (x : E)
  结论: J (J x) = -x
  证明: by
  rw [rightAngleRotation]
  exact o.rightAngleRotationAux₁_rightAngleRotationAux₁ x

@[simp]

Depends on / 依赖: o.rightAngleRotationAux, rightAngleRotation
-/
theorem rightAngleRotation_rightAngleRotation (x : E) : J (J x) = -x := by
  rw [rightAngleRotation]
  exact o.rightAngleRotationAux₁_rightAngleRotationAux₁ x

@[simp]
/--
theorem `rightAngleRotation_symm` / 定理 `rightAngleRotation_symm`

English:
theorem rightAngleRotation_symm
  proof: by
  rw [rightAngleRotation]
  exact LinearIsometryEquiv.toLinearIsometry_injective rfl

中文:
定理 rightAngleRotation_symm
  证明: by
  rw [rightAngleRotation]
  exact LinearIsometryEquiv.toLinearIsometry_injective rfl

Depends on / 依赖: LinearIsometryEquiv, LinearIsometryEquiv.toLinearIsometry_injective, rightAngleRotation, toLinearIsometry_injective
-/
theorem rightAngleRotation_symm :
    LinearIsometryEquiv.symm J = LinearIsometryEquiv.trans J (LinearIsometryEquiv.neg Real) := by
  rw [rightAngleRotation]
  exact LinearIsometryEquiv.toLinearIsometry_injective rfl

/--
theorem `inner_rightAngleRotation_self` / 定理 `inner_rightAngleRotation_self`

English:
theorem inner_rightAngleRotation_self
  given: (x : E)
  statement: ⟪J x, x⟫ = 0
  proof: by simp

中文:
定理 inner_rightAngleRotation_self
  条件: (x : E)
  结论: ⟪J x, x⟫ = 0
  证明: by simp
-/
theorem inner_rightAngleRotation_self (x : E) : ⟪J x, x⟫ = 0 := by simp

/--
theorem `inner_rightAngleRotation_swap` / 定理 `inner_rightAngleRotation_swap`

English:
theorem inner_rightAngleRotation_swap
  given: (x y : E)
  statement: ⟪x, J y⟫ = -⟪J x, y⟫
  proof: by simp

中文:
定理 inner_rightAngleRotation_swap
  条件: (x y : E)
  结论: ⟪x, J y⟫ = -⟪J x, y⟫
  证明: by simp
-/
theorem inner_rightAngleRotation_swap (x y : E) : ⟪x, J y⟫ = -⟪J x, y⟫ := by simp

/--
theorem `inner_rightAngleRotation_swap'` / 定理 `inner_rightAngleRotation_swap'`

English:
theorem inner_rightAngleRotation_swap'
  given: (x y : E)
  statement: ⟪J x, y⟫ = -⟪x, J y⟫
  proof: by
  simp [o.inner_rightAngleRotation_swap x y]

中文:
定理 inner_rightAngleRotation_swap'
  条件: (x y : E)
  结论: ⟪J x, y⟫ = -⟪x, J y⟫
  证明: by
  simp [o.inner_rightAngleRotation_swap x y]

Depends on / 依赖: inner_rightAngleRotation_swap, o.inner_rightAngleRotation_swap
-/
theorem inner_rightAngleRotation_swap' (x y : E) : ⟪J x, y⟫ = -⟪x, J y⟫ := by
  simp [o.inner_rightAngleRotation_swap x y]

/--
theorem `inner_comp_rightAngleRotation` / 定理 `inner_comp_rightAngleRotation`

English:
theorem inner_comp_rightAngleRotation
  given: (x y : E)
  statement: ⟪J x, J y⟫ = ⟪x, y⟫
  proof: LinearIsometryEquiv.inner_map_map J x y

@[simp]

中文:
定理 inner_comp_rightAngleRotation
  条件: (x y : E)
  结论: ⟪J x, J y⟫ = ⟪x, y⟫
  证明: LinearIsometryEquiv.inner_map_map J x y

@[simp]

Depends on / 依赖: LinearIsometryEquiv, LinearIsometryEquiv.inner_map_map, inner_map_map
-/
theorem inner_comp_rightAngleRotation (x y : E) : ⟪J x, J y⟫ = ⟪x, y⟫ :=
  LinearIsometryEquiv.inner_map_map J x y

@[simp]
/--
theorem `areaForm_rightAngleRotation_left` / 定理 `areaForm_rightAngleRotation_left`

English:
theorem areaForm_rightAngleRotation_left
  given: (x y : E)
  statement: ω (J x) y = -⟪x, y⟫
  proof: by
  rw [← o.inner_comp_rightAngleRotation]; rw [o.inner_rightAngleRotation_right]; rw [neg_neg]

@[simp]

中文:
定理 areaForm_rightAngleRotation_left
  条件: (x y : E)
  结论: ω (J x) y = -⟪x, y⟫
  证明: by
  rw [← o.inner_comp_rightAngleRotation]; rw [o.inner_rightAngleRotation_right]; rw [neg_neg]

@[simp]

Depends on / 依赖: inner_comp_rightAngleRotation, inner_rightAngleRotation_right, neg_neg, o.inner_comp_rightAngleRotation, o.inner_rightAngleRotation_right
-/
theorem areaForm_rightAngleRotation_left (x y : E) : ω (J x) y = -⟪x, y⟫ := by
  rw [← o.inner_comp_rightAngleRotation]; rw [o.inner_rightAngleRotation_right]; rw [neg_neg]

@[simp]
/--
theorem `areaForm_rightAngleRotation_right` / 定理 `areaForm_rightAngleRotation_right`

English:
theorem areaForm_rightAngleRotation_right
  given: (x y : E)
  statement: ω x (J y) = ⟪x, y⟫
  proof: by
  rw [← o.inner_rightAngleRotation_left]; rw [o.inner_comp_rightAngleRotation]

中文:
定理 areaForm_rightAngleRotation_right
  条件: (x y : E)
  结论: ω x (J y) = ⟪x, y⟫
  证明: by
  rw [← o.inner_rightAngleRotation_left]; rw [o.inner_comp_rightAngleRotation]

Depends on / 依赖: inner_comp_rightAngleRotation, inner_rightAngleRotation_left, o.inner_comp_rightAngleRotation, o.inner_rightAngleRotation_left
-/
theorem areaForm_rightAngleRotation_right (x y : E) : ω x (J y) = ⟪x, y⟫ := by
  rw [← o.inner_rightAngleRotation_left]; rw [o.inner_comp_rightAngleRotation]

/--
theorem `areaForm_comp_rightAngleRotation` / 定理 `areaForm_comp_rightAngleRotation`

English:
theorem areaForm_comp_rightAngleRotation
  given: (x y : E)
  statement: ω (J x) (J y) = ω x y
  proof: by simp

@[simp]

中文:
定理 areaForm_comp_rightAngleRotation
  条件: (x y : E)
  结论: ω (J x) (J y) = ω x y
  证明: by simp

@[simp]
-/
theorem areaForm_comp_rightAngleRotation (x y : E) : ω (J x) (J y) = ω x y := by simp

@[simp]
/--
theorem `rightAngleRotation_trans_rightAngleRotation` / 定理 `rightAngleRotation_trans_rightAngleRotation`

English:
theorem rightAngleRotation_trans_rightAngleRotation
  proof: by ext; simp

中文:
定理 rightAngleRotation_trans_rightAngleRotation
  证明: by ext; simp
-/
theorem rightAngleRotation_trans_rightAngleRotation :
    LinearIsometryEquiv.trans J J = LinearIsometryEquiv.neg Real := by ext; simp

/--
theorem `rightAngleRotation_neg_orientation` / 定理 `rightAngleRotation_neg_orientation`

English:
theorem rightAngleRotation_neg_orientation
  given: (x : E)
  proof: by
  apply ext_inner_right Real
  intro y
  rw [inner_rightAngleRotation_left]
  simp

@[simp]

中文:
定理 rightAngleRotation_neg_orientation
  条件: (x : E)
  证明: by
  apply ext_inner_right Real
  intro y
  rw [inner_rightAngleRotation_left]
  simp

@[simp]

Depends on / 依赖: ext_inner_right, inner_rightAngleRotation_left
-/
theorem rightAngleRotation_neg_orientation (x : E) :
    (-o).rightAngleRotation x = -o.rightAngleRotation x := by
  apply ext_inner_right Real
  intro y
  rw [inner_rightAngleRotation_left]
  simp

@[simp]
/--
theorem `rightAngleRotation_trans_neg_orientation` / 定理 `rightAngleRotation_trans_neg_orientation`

English:
theorem rightAngleRotation_trans_neg_orientation
  proof: LinearIsometryEquiv.ext o.rightAngleRotation_neg_orientation

中文:
定理 rightAngleRotation_trans_neg_orientation
  证明: LinearIsometryEquiv.ext o.rightAngleRotation_neg_orientation

Depends on / 依赖: LinearIsometryEquiv, LinearIsometryEquiv.ext, o.rightAngleRotation_neg_orientation, rightAngleRotation_neg_orientation
-/
theorem rightAngleRotation_trans_neg_orientation :
    (-o).rightAngleRotation = o.rightAngleRotation.trans (LinearIsometryEquiv.neg Real) :=
LinearIsometryEquiv.ext o.rightAngleRotation_neg_orientation

/--
theorem `rightAngleRotation_map` / 定理 `rightAngleRotation_map`

English:
theorem rightAngleRotation_map
  statement: {F : Type*} [NormedAddCommGroup F] [InnerProductSpace Real F]
  proof: by
  apply ext_inner_right Real
  intro y
  rw [inner_rightAngleRotation_left]
  trans ⟪J (φ.symm x), φ.symm y⟫
  · simp [o.areaForm_map]
  trans ⟪φ (J (φ.symm x)), φ (φ.symm y)⟫
  · rw [φ.inner_map_map]
  · simp

中文:
定理 rightAngleRotation_map
  结论: {F : 类型} [赋范交换加群 F] [内积空间 实数 F]
  证明: by
  apply ext_inner_right Real
  intro y
  rw [inner_rightAngleRotation_left]
  trans ⟪J (φ.symm x), φ.symm y⟫
  · simp [o.areaForm_map]
  trans ⟪φ (J (φ.symm x)), φ (φ.symm y)⟫
  · rw [φ.inner_map_map]
  · simp

Depends on / 依赖: areaForm_map, ext_inner_right, inner_map_map, inner_rightAngleRotation_left, o.areaForm_map
-/
theorem rightAngleRotation_map {F : Type*} [NormedAddCommGroup F] [InnerProductSpace Real F]
    [hF : Fact (finrank Real F = 2)] (φ : E ≃ₗᵢ[Real] F) (x : F) :
    (Orientation.map (Fin 2) φ.toLinearEquiv o).rightAngleRotation x =
      φ (o.rightAngleRotation (φ.symm x)) := by
  apply ext_inner_right Real
  intro y
  rw [inner_rightAngleRotation_left]
  trans ⟪J (φ.symm x), φ.symm y⟫
  · simp [o.areaForm_map]
  trans ⟪φ (J (φ.symm x)), φ (φ.symm y)⟫
  · rw [φ.inner_map_map]
  · simp

/--
theorem `linearIsometryEquiv_comp_rightAngleRotation` / 定理 `linearIsometryEquiv_comp_rightAngleRotation`

English:
theorem linearIsometryEquiv_comp_rightAngleRotation
  statement: (φ : E ≃ₗᵢ[Real] E)
  proof: by
  convert! (o.rightAngleRotation_map φ (φ x)).symm
  · simp
  · symm
    rwa [← o.map_eq_iff_det_pos φ.toLinearEquiv] at hφ
    rw [@Fact.out (finrank Real E = 2)]; rw [Fintype.card_fin]

中文:
定理 linearIsometryEquiv_comp_rightAngleRotation
  结论: (φ : E ≃ₗᵢ[实数] E)
  证明: by
  convert! (o.rightAngleRotation_map φ (φ x)).symm
  · simp
  · symm
    rwa [← o.map_eq_iff_det_pos φ.toLinearEquiv] at hφ
    rw [@Fact.out (finrank Real E = 2)]; rw [Fintype.card_fin]

Depends on / 依赖: Fact.out, Fintype, Fintype.card_fin, card_fin, convert, finrank, map_eq_iff_det_pos, o.map_eq_iff_det_pos, o.rightAngleRotation_map, rightAngleRotation_map, toLinearEquiv
-/
theorem linearIsometryEquiv_comp_rightAngleRotation (φ : E ≃ₗᵢ[Real] E)
    (hφ : 0 < LinearMap.det (φ.toLinearEquiv : E ->ₗ[Real] E)) (x : E) : φ (J x) = J (φ x) := by
  convert! (o.rightAngleRotation_map φ (φ x)).symm
  · simp
  · symm
    rwa [← o.map_eq_iff_det_pos φ.toLinearEquiv] at hφ
    rw [@Fact.out (finrank Real E = 2)]; rw [Fintype.card_fin]

/--
theorem `rightAngleRotation_map'` / 定理 `rightAngleRotation_map'`

English:
theorem rightAngleRotation_map'
  statement: {F : Type*} [NormedAddCommGroup F] [InnerProductSpace Real F]
  proof: LinearIsometryEquiv.ext o.rightAngleRotation_map φ

中文:
定理 rightAngleRotation_map'
  结论: {F : 类型} [赋范交换加群 F] [内积空间 实数 F]
  证明: LinearIsometryEquiv.ext o.rightAngleRotation_map φ

Depends on / 依赖: LinearIsometryEquiv, LinearIsometryEquiv.ext, o.rightAngleRotation_map, rightAngleRotation_map
-/
theorem rightAngleRotation_map' {F : Type*} [NormedAddCommGroup F] [InnerProductSpace Real F]
    [Fact (finrank Real F = 2)] (φ : E ≃ₗᵢ[Real] F) :
    (Orientation.map (Fin 2) φ.toLinearEquiv o).rightAngleRotation =
      (φ.symm.trans o.rightAngleRotation).trans φ :=
LinearIsometryEquiv.ext o.rightAngleRotation_map φ

/--
theorem `linearIsometryEquiv_comp_rightAngleRotation'` / 定理 `linearIsometryEquiv_comp_rightAngleRotation'`

English:
theorem linearIsometryEquiv_comp_rightAngleRotation'
  statement: (φ : E ≃ₗᵢ[Real] E)
  proof: LinearIsometryEquiv.ext o.linearIsometryEquiv_comp_rightAngleRotation φ hφ

中文:
定理 linearIsometryEquiv_comp_rightAngleRotation'
  结论: (φ : E ≃ₗᵢ[实数] E)
  证明: LinearIsometryEquiv.ext o.linearIsometryEquiv_comp_rightAngleRotation φ hφ

Depends on / 依赖: LinearIsometryEquiv, LinearIsometryEquiv.ext, linearIsometryEquiv_comp_rightAngleRotation, o.linearIsometryEquiv_comp_rightAngleRotation
-/
theorem linearIsometryEquiv_comp_rightAngleRotation' (φ : E ≃ₗᵢ[Real] E)
    (hφ : 0 < LinearMap.det (φ.toLinearEquiv : E ->ₗ[Real] E)) :
    LinearIsometryEquiv.trans J φ = φ.trans J :=
LinearIsometryEquiv.ext o.linearIsometryEquiv_comp_rightAngleRotation φ hφ

/--
Definition of `basisRightAngleRotation` / `basisRightAngleRotation` 的定义

English:
definition basisRightAngleRotation
  signature: (x : E) (hx : x != 0)
  body: @basisOfLinearIndependentOfCardEqFinrank Real _ _ _ _ _ _ _ ![x, J x]
    (linearIndependent_of_ne_zero_of_inner_eq_zero (fun i => by fin_cases i <;> simp [hx])
      (by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all))
    (@Fact.out (finrank Real E = 2)).symm

@[simp]

中文:
定义 basisRightAngleRotation
  签名: (x : E) (hx : x != 0)
  定义体: @basisOfLinearIndependentOfCardEqFinrank Real _ _ _ _ _ _ _ ![x, J x]
    (linearIndependent_of_ne_zero_of_inner_eq_zero (fun i => by fin_cases i <;> simp [hx])
      (by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all))
    (@Fact.out (finrank Real E = 2)).symm

@[simp]

Depends on / 依赖: Fact.out, basisOfLinearIndependentOfCardEqFinrank, fin_cases, finrank, linearIndependent_of_ne_zero_of_inner_eq_zero
-/
def basisRightAngleRotation (x : E) (hx : x != 0) : Basis (Fin 2) Real E :=
  @basisOfLinearIndependentOfCardEqFinrank Real _ _ _ _ _ _ _ ![x, J x]
    (linearIndependent_of_ne_zero_of_inner_eq_zero (fun i => by fin_cases i <;> simp [hx])
      (by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all))
    (@Fact.out (finrank Real E = 2)).symm

@[simp]
/--
theorem `coe_basisRightAngleRotation` / 定理 `coe_basisRightAngleRotation`

English:
theorem coe_basisRightAngleRotation
  given: (x : E) (hx : x != 0)
  proof: coe_basisOfLinearIndependentOfCardEqFinrank _ _

中文:
定理 coe_basisRightAngleRotation
  条件: (x : E) (hx : x != 0)
  证明: coe_basisOfLinearIndependentOfCardEqFinrank _ _

Depends on / 依赖: coe_basisOfLinearIndependentOfCardEqFinrank
-/
theorem coe_basisRightAngleRotation (x : E) (hx : x != 0) :
    ⇑(o.basisRightAngleRotation x hx) = ![x, J x] :=
  coe_basisOfLinearIndependentOfCardEqFinrank _ _

/--
theorem `inner_mul_inner_add_areaForm_mul_areaForm'` / 定理 `inner_mul_inner_add_areaForm_mul_areaForm'`

English:
theorem inner_mul_inner_add_areaForm_mul_areaForm'
  given: (a x : E)
  proof: by
  by_cases ha : a = 0
  · simp [ha]
  apply (o.basisRightAngleRotation a ha).ext
  intro i
  fin_cases i
  · simp [mul_comm, real_inner_comm]
  · simp [mul_comm, o.areaForm_swap a x]

中文:
定理 inner_mul_inner_add_areaForm_mul_areaForm'
  条件: (a x : E)
  证明: by
  by_cases ha : a = 0
  · simp [ha]
  apply (o.basisRightAngleRotation a ha).ext
  intro i
  fin_cases i
  · simp [mul_comm, real_inner_comm]
  · simp [mul_comm, o.areaForm_swap a x]

Depends on / 依赖: areaForm_swap, basisRightAngleRotation, fin_cases, mul_comm, o.areaForm_swap, o.basisRightAngleRotation, real_inner_comm
-/
theorem inner_mul_inner_add_areaForm_mul_areaForm' (a x : E) :
    ⟪a, x⟫ • innerₛₗ Real a + ω a x • ω a = ‖a‖ ^ 2 • innerₛₗ Real x := by
  by_cases ha : a = 0
  · simp [ha]
  apply (o.basisRightAngleRotation a ha).ext
  intro i
  fin_cases i
  · simp [mul_comm, real_inner_comm]
  · simp [mul_comm, o.areaForm_swap a x]

/--
theorem `inner_mul_inner_add_areaForm_mul_areaForm` / 定理 `inner_mul_inner_add_areaForm_mul_areaForm`

English:
theorem inner_mul_inner_add_areaForm_mul_areaForm
  given: (a x y : E)
  proof: congr_arg (fun f : E ->ₗ[Real] Real => f y) (o.inner_mul_inner_add_areaForm_mul_areaForm' a x)

中文:
定理 inner_mul_inner_add_areaForm_mul_areaForm
  条件: (a x y : E)
  证明: congr_arg (fun f : E ->ₗ[Real] Real => f y) (o.inner_mul_inner_add_areaForm_mul_areaForm' a x)

Depends on / 依赖: congr_arg, inner_mul_inner_add_areaForm_mul_areaForm, o.inner_mul_inner_add_areaForm_mul_areaForm
-/
theorem inner_mul_inner_add_areaForm_mul_areaForm (a x y : E) :
    ⟪a, x⟫ * ⟪a, y⟫ + ω a x * ω a y = ‖a‖ ^ 2 * ⟪x, y⟫ :=
  congr_arg (fun f : E ->ₗ[Real] Real => f y) (o.inner_mul_inner_add_areaForm_mul_areaForm' a x)

/--
theorem `inner_sq_add_areaForm_sq` / 定理 `inner_sq_add_areaForm_sq`

English:
theorem inner_sq_add_areaForm_sq
  given: (a b : E)
  statement: ⟪a, b⟫ ^ 2 + ω a b ^ 2 = ‖a‖ ^ 2 * ‖b‖ ^ 2
  proof: by
  simpa [sq, real_inner_self_eq_norm_sq] using o.inner_mul_inner_add_areaForm_mul_areaForm a b b

中文:
定理 inner_sq_add_areaForm_sq
  条件: (a b : E)
  结论: ⟪a, b⟫ ^ 2 + ω a b ^ 2 = ‖a‖ ^ 2 * ‖b‖ ^ 2
  证明: by
  simpa [sq, real_inner_self_eq_norm_sq] using o.inner_mul_inner_add_areaForm_mul_areaForm a b b

Depends on / 依赖: inner_mul_inner_add_areaForm_mul_areaForm, o.inner_mul_inner_add_areaForm_mul_areaForm, real_inner_self_eq_norm_sq
-/
theorem inner_sq_add_areaForm_sq (a b : E) : ⟪a, b⟫ ^ 2 + ω a b ^ 2 = ‖a‖ ^ 2 * ‖b‖ ^ 2 := by
  simpa [sq, real_inner_self_eq_norm_sq] using o.inner_mul_inner_add_areaForm_mul_areaForm a b b

/--
theorem `inner_mul_areaForm_sub'` / 定理 `inner_mul_areaForm_sub'`

English:
theorem inner_mul_areaForm_sub'
  given: (a x : E)
  statement: ⟪a, x⟫ • ω a - ω a x • innerₛₗ Real a = ‖a‖ ^ 2 • ω x
  proof: by
  by_cases ha : a = 0
  · simp [ha]
  apply (o.basisRightAngleRotation a ha).ext
  intro i
  fin_cases i
  · simp [mul_comm, o.areaForm_swap a x]
  · simp [mul_comm, real_inner_comm]

中文:
定理 inner_mul_areaForm_sub'
  条件: (a x : E)
  结论: ⟪a, x⟫ • ω a - ω a x • innerₛₗ 实数 a = ‖a‖ ^ 2 • ω x
  证明: by
  by_cases ha : a = 0
  · simp [ha]
  apply (o.basisRightAngleRotation a ha).ext
  intro i
  fin_cases i
  · simp [mul_comm, o.areaForm_swap a x]
  · simp [mul_comm, real_inner_comm]

Depends on / 依赖: areaForm_swap, basisRightAngleRotation, fin_cases, mul_comm, o.areaForm_swap, o.basisRightAngleRotation, real_inner_comm
-/
theorem inner_mul_areaForm_sub' (a x : E) : ⟪a, x⟫ • ω a - ω a x • innerₛₗ Real a = ‖a‖ ^ 2 • ω x := by
  by_cases ha : a = 0
  · simp [ha]
  apply (o.basisRightAngleRotation a ha).ext
  intro i
  fin_cases i
  · simp [mul_comm, o.areaForm_swap a x]
  · simp [mul_comm, real_inner_comm]

/--
theorem `inner_mul_areaForm_sub` / 定理 `inner_mul_areaForm_sub`

English:
theorem inner_mul_areaForm_sub
  given: (a x y : E)
  statement: ⟪a, x⟫ * ω a y - ω a x * ⟪a, y⟫ = ‖a‖ ^ 2 * ω x y
  proof: congr_arg (fun f : E ->ₗ[Real] Real => f y) (o.inner_mul_areaForm_sub' a x)

中文:
定理 inner_mul_areaForm_sub
  条件: (a x y : E)
  结论: ⟪a, x⟫ * ω a y - ω a x * ⟪a, y⟫ = ‖a‖ ^ 2 * ω x y
  证明: congr_arg (fun f : E ->ₗ[Real] Real => f y) (o.inner_mul_areaForm_sub' a x)

Depends on / 依赖: congr_arg, inner_mul_areaForm_sub, o.inner_mul_areaForm_sub
-/
theorem inner_mul_areaForm_sub (a x y : E) : ⟪a, x⟫ * ω a y - ω a x * ⟪a, y⟫ = ‖a‖ ^ 2 * ω x y :=
  congr_arg (fun f : E ->ₗ[Real] Real => f y) (o.inner_mul_areaForm_sub' a x)

/--
theorem `nonneg_inner_and_areaForm_eq_zero_iff_sameRay` / 定理 `nonneg_inner_and_areaForm_eq_zero_iff_sameRay`

English:
theorem nonneg_inner_and_areaForm_eq_zero_iff_sameRay
  given: (x y : E)
  proof: by
  by_cases hx : x = 0
  · simp [hx]
  constructor
  · let a : Real := (o.basisRightAngleRotation x hx).repr y 0
    let b : Real := (o.basisRightAngleRotation x hx).repr y 1
    suffices ↑0 <= a * ‖x‖ ^ 2 ∧ b * ‖x‖ ^ 2 = 0 -> SameRay Real x (a • x + b • J x) by
      rw [← (o.basisRightAngleRotat

中文:
定理 nonneg_inner_and_areaForm_eq_zero_iff_sameRay
  条件: (x y : E)
  证明: by
  by_cases hx : x = 0
  · simp [hx]
  constructor
  · let a : Real := (o.basisRightAngleRotation x hx).repr y 0
    let b : Real := (o.basisRightAngleRotation x hx).repr y 1
    suffices ↑0 <= a * ‖x‖ ^ 2 ∧ b * ‖x‖ ^ 2 = 0 -> SameRay Real x (a • x + b • J x) by
      rw [← (o.basisRightAngleRotat

Depends on / 依赖: Fin.succ_zero_eq_one, Fin.sum_univ_succ, Finset, Finset.sum_empty, Finset.univ_eq_empty, Matrix, Matrix.cons_val_zero, SameRay, areaForm_apply_self, basisRightAngleRotation, coe_basisRightAngleRotation, cons_val_zero, map_add, map_smul, o.basisRightAngleRotation, real_inner_smul_, succ_zero_eq_one, sum_empty, sum_repr, sum_univ_succ
-/
theorem nonneg_inner_and_areaForm_eq_zero_iff_sameRay (x y : E) :
    0 <= ⟪x, y⟫ ∧ ω x y = 0 ↔ SameRay Real x y := by
  by_cases hx : x = 0
  · simp [hx]
  constructor
  · let a : Real := (o.basisRightAngleRotation x hx).repr y 0
    let b : Real := (o.basisRightAngleRotation x hx).repr y 1
    suffices ↑0 <= a * ‖x‖ ^ 2 ∧ b * ‖x‖ ^ 2 = 0 -> SameRay Real x (a • x + b • J x) by
      rw [← (o.basisRightAngleRotation x hx).sum_repr y]
      simp only [Fin.sum_univ_succ, coe_basisRightAngleRotation, Matrix.cons_val_zero,
        Fin.succ_zero_eq_one', Finset.univ_eq_empty, Finset.sum_empty, areaForm_apply_self,
        map_smul, map_add, real_inner_smul_right, inner_add_right, Matrix.cons_val_one,
        smul_eq_mul, areaForm_rightAngleRotation_right,
        mul_zero, add_zero, zero_add, neg_zero, inner_rightAngleRotation_right,
        real_inner_self_eq_norm_sq]
      exact this
    simp_all
  · intro h
    obtain ⟨r, hr, rfl⟩ := h.exists_nonneg_left hx
    simp only [inner_smul_right, real_inner_self_eq_norm_sq, map_smulₛₗ, areaForm_apply_self,
      smul_eq_mul, mul_zero, and_true]
    positivity

/--
Definition of `kahler` / `kahler` 的定义

English:
definition kahler
  signature: : E ->ₗ[Real] E ->ₗ[Real] Complex
  body: LinearMap.llcomp Real E Real Complex Complex.ofRealCLM ∘ₗ innerₛₗ Real +
    LinearMap.llcomp Real E Real Complex ((LinearMap.lsmul Real Complex).flip Complex.I) ∘ₗ ω

中文:
定义 kahler
  签名: : E ->ₗ[实数] E ->ₗ[实数] 复形
  定义体: LinearMap.llcomp Real E Real Complex Complex.ofRealCLM ∘ₗ innerₛₗ Real +
    LinearMap.llcomp Real E Real Complex ((LinearMap.lsmul Real Complex).flip Complex.I) ∘ₗ ω

Depends on / 依赖: Complex.I, Complex.ofRealCLM, LinearMap, LinearMap.llcomp, LinearMap.lsmul, llcomp, ofRealCLM
-/
def kahler : E ->ₗ[Real] E ->ₗ[Real] Complex :=
  LinearMap.llcomp Real E Real Complex Complex.ofRealCLM ∘ₗ innerₛₗ Real +
    LinearMap.llcomp Real E Real Complex ((LinearMap.lsmul Real Complex).flip Complex.I) ∘ₗ ω

/--
theorem `kahler_apply_apply` / 定理 `kahler_apply_apply`

English:
theorem kahler_apply_apply
  given: (x y : E)
  statement: o.kahler x y = ⟪x, y⟫ + ω x y • Complex.I
  proof: rfl

中文:
定理 kahler_apply_apply
  条件: (x y : E)
  结论: o.kahler x y = ⟪x, y⟫ + ω x y • 复形.I
  证明: rfl
-/
theorem kahler_apply_apply (x y : E) : o.kahler x y = ⟪x, y⟫ + ω x y • Complex.I :=
  rfl

/--
theorem `kahler_swap` / 定理 `kahler_swap`

English:
theorem kahler_swap
  given: (x y : E)
  statement: o.kahler x y = conj (o.kahler y x)
  proof: by
  simp only [kahler_apply_apply]
  rw [real_inner_comm]; rw [areaForm_swap]
  simp [Complex.conj_ofReal]

@[simp]

中文:
定理 kahler_swap
  条件: (x y : E)
  结论: o.kahler x y = conj (o.kahler y x)
  证明: by
  simp only [kahler_apply_apply]
  rw [real_inner_comm]; rw [areaForm_swap]
  simp [Complex.conj_ofReal]

@[simp]

Depends on / 依赖: Complex.conj_ofReal, areaForm_swap, conj_ofReal, kahler_apply_apply, real_inner_comm
-/
theorem kahler_swap (x y : E) : o.kahler x y = conj (o.kahler y x) := by
  simp only [kahler_apply_apply]
  rw [real_inner_comm]; rw [areaForm_swap]
  simp [Complex.conj_ofReal]

@[simp]
/--
theorem `kahler_apply_self` / 定理 `kahler_apply_self`

English:
theorem kahler_apply_self
  given: (x : E)
  statement: o.kahler x x = ‖x‖ ^ 2
  proof: by
  simp [kahler_apply_apply]

@[simp]

中文:
定理 kahler_apply_self
  条件: (x : E)
  结论: o.kahler x x = ‖x‖ ^ 2
  证明: by
  simp [kahler_apply_apply]

@[simp]

Depends on / 依赖: kahler_apply_apply
-/
theorem kahler_apply_self (x : E) : o.kahler x x = ‖x‖ ^ 2 := by
  simp [kahler_apply_apply]

@[simp]
/--
theorem `kahler_rightAngleRotation_left` / 定理 `kahler_rightAngleRotation_left`

English:
theorem kahler_rightAngleRotation_left
  given: (x y : E)
  proof: by
  simp only [o.areaForm_rightAngleRotation_left, o.inner_rightAngleRotation_left,
    o.kahler_apply_apply, Complex.ofReal_neg, Complex.real_smul]
  linear_combination ω x y * Complex.I_sq

@[simp]

中文:
定理 kahler_rightAngleRotation_left
  条件: (x y : E)
  证明: by
  simp only [o.areaForm_rightAngleRotation_left, o.inner_rightAngleRotation_left,
    o.kahler_apply_apply, Complex.ofReal_neg, Complex.real_smul]
  linear_combination ω x y * Complex.I_sq

@[simp]

Depends on / 依赖: Complex.I_sq, Complex.ofReal_neg, Complex.real_smul, I_sq, areaForm_rightAngleRotation_left, inner_rightAngleRotation_left, kahler_apply_apply, linear_combination, o.areaForm_rightAngleRotation_left, o.inner_rightAngleRotation_left, o.kahler_apply_apply, ofReal_neg, real_smul
-/
theorem kahler_rightAngleRotation_left (x y : E) :
    o.kahler (J x) y = -Complex.I * o.kahler x y := by
  simp only [o.areaForm_rightAngleRotation_left, o.inner_rightAngleRotation_left,
    o.kahler_apply_apply, Complex.ofReal_neg, Complex.real_smul]
  linear_combination ω x y * Complex.I_sq

@[simp]
/--
theorem `kahler_rightAngleRotation_right` / 定理 `kahler_rightAngleRotation_right`

English:
theorem kahler_rightAngleRotation_right
  given: (x y : E)
  proof: by
  simp only [o.areaForm_rightAngleRotation_right, o.inner_rightAngleRotation_right,
    o.kahler_apply_apply, Complex.ofReal_neg, Complex.real_smul]
  linear_combination -ω x y * Complex.I_sq

中文:
定理 kahler_rightAngleRotation_right
  条件: (x y : E)
  证明: by
  simp only [o.areaForm_rightAngleRotation_right, o.inner_rightAngleRotation_right,
    o.kahler_apply_apply, Complex.ofReal_neg, Complex.real_smul]
  linear_combination -ω x y * Complex.I_sq

Depends on / 依赖: Complex.I_sq, Complex.ofReal_neg, Complex.real_smul, I_sq, areaForm_rightAngleRotation_right, inner_rightAngleRotation_right, kahler_apply_apply, linear_combination, o.areaForm_rightAngleRotation_right, o.inner_rightAngleRotation_right, o.kahler_apply_apply, ofReal_neg, real_smul
-/
theorem kahler_rightAngleRotation_right (x y : E) :
    o.kahler x (J y) = Complex.I * o.kahler x y := by
  simp only [o.areaForm_rightAngleRotation_right, o.inner_rightAngleRotation_right,
    o.kahler_apply_apply, Complex.ofReal_neg, Complex.real_smul]
  linear_combination -ω x y * Complex.I_sq

-- `simp` normal form is `kahler_comp_rightAngleRotation'`
/--
theorem `kahler_comp_rightAngleRotation` / 定理 `kahler_comp_rightAngleRotation`

English:
theorem kahler_comp_rightAngleRotation
  given: (x y : E)
  statement: o.kahler (J x) (J y) = o.kahler x y
  proof: by
  simp only [kahler_rightAngleRotation_left, kahler_rightAngleRotation_right]
  linear_combination -o.kahler x y * Complex.I_sq

中文:
定理 kahler_comp_rightAngleRotation
  条件: (x y : E)
  结论: o.kahler (J x) (J y) = o.kahler x y
  证明: by
  simp only [kahler_rightAngleRotation_left, kahler_rightAngleRotation_right]
  linear_combination -o.kahler x y * Complex.I_sq

Depends on / 依赖: Complex.I_sq, I_sq, kahler, kahler_rightAngleRotation_left, kahler_rightAngleRotation_right, linear_combination, o.kahler
-/
theorem kahler_comp_rightAngleRotation (x y : E) : o.kahler (J x) (J y) = o.kahler x y := by
  simp only [kahler_rightAngleRotation_left, kahler_rightAngleRotation_right]
  linear_combination -o.kahler x y * Complex.I_sq

/--
theorem `kahler_comp_rightAngleRotation'` / 定理 `kahler_comp_rightAngleRotation'`

English:
theorem kahler_comp_rightAngleRotation'
  given: (x y : E)
  proof: by
  linear_combination -o.kahler x y * Complex.I_sq

@[simp]

中文:
定理 kahler_comp_rightAngleRotation'
  条件: (x y : E)
  证明: by
  linear_combination -o.kahler x y * Complex.I_sq

@[simp]

Depends on / 依赖: Complex.I_sq, I_sq, kahler, linear_combination, o.kahler
-/
theorem kahler_comp_rightAngleRotation' (x y : E) :
    -(Complex.I * (Complex.I * o.kahler x y)) = o.kahler x y := by
  linear_combination -o.kahler x y * Complex.I_sq

@[simp]
/--
theorem `kahler_neg_orientation` / 定理 `kahler_neg_orientation`

English:
theorem kahler_neg_orientation
  given: (x y : E)
  statement: (-o).kahler x y = conj (o.kahler x y)
  proof: by
  simp [kahler_apply_apply, Complex.conj_ofReal]

中文:
定理 kahler_neg_orientation
  条件: (x y : E)
  结论: (-o).kahler x y = conj (o.kahler x y)
  证明: by
  simp [kahler_apply_apply, Complex.conj_ofReal]

Depends on / 依赖: Complex.conj_ofReal, conj_ofReal, kahler_apply_apply
-/
theorem kahler_neg_orientation (x y : E) : (-o).kahler x y = conj (o.kahler x y) := by
  simp [kahler_apply_apply, Complex.conj_ofReal]

/--
theorem `kahler_mul` / 定理 `kahler_mul`

English:
theorem kahler_mul
  given: (a x y : E)
  statement: o.kahler x a * o.kahler a y = ‖a‖ ^ 2 * o.kahler x y
  proof: by
  trans ((‖a‖ ^ 2 :) : Complex) * o.kahler x y
  · apply Complex.ext
    · simp only [o.kahler_apply_apply, Complex.add_im, Complex.add_re, Complex.I_im, Complex.I_re,
        Complex.mul_im, Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re, Complex.real_smul]
      rw [real_inner_comm a x]; 

中文:
定理 kahler_mul
  条件: (a x y : E)
  结论: o.kahler x a * o.kahler a y = ‖a‖ ^ 2 * o.kahler x y
  证明: by
  trans ((‖a‖ ^ 2 :) : Complex) * o.kahler x y
  · apply Complex.ext
    · simp only [o.kahler_apply_apply, Complex.add_im, Complex.add_re, Complex.I_im, Complex.I_re,
        Complex.mul_im, Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re, Complex.real_smul]
      rw [real_inner_comm a x]; 

Depends on / 依赖: Complex.I_im, Complex.I_re, Complex.add_im, Complex.add_re, Complex.ext, Complex.mul_im, Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re, Complex.real_smul, I_im, I_re, add_im, add_re, areaForm_swap, inner_mul_inner_add_areaForm_mul_areaForm, kahler, kahler_apply_apply, linear_combination, mul_im
-/
theorem kahler_mul (a x y : E) : o.kahler x a * o.kahler a y = ‖a‖ ^ 2 * o.kahler x y := by
  trans ((‖a‖ ^ 2 :) : Complex) * o.kahler x y
  · apply Complex.ext
    · simp only [o.kahler_apply_apply, Complex.add_im, Complex.add_re, Complex.I_im, Complex.I_re,
        Complex.mul_im, Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re, Complex.real_smul]
      rw [real_inner_comm a x]; rw [o.areaForm_swap x a]
      linear_combination o.inner_mul_inner_add_areaForm_mul_areaForm a x y
    · simp only [o.kahler_apply_apply, Complex.add_im, Complex.add_re, Complex.I_im, Complex.I_re,
        Complex.mul_im, Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re, Complex.real_smul]
      rw [real_inner_comm a x]; rw [o.areaForm_swap x a]
      linear_combination o.inner_mul_areaForm_sub a x y
  · norm_cast

/--
theorem `normSq_kahler` / 定理 `normSq_kahler`

English:
theorem normSq_kahler
  given: (x y : E)
  statement: Complex.normSq (o.kahler x y) = ‖x‖ ^ 2 * ‖y‖ ^ 2
  proof: by
  simpa [kahler_apply_apply, Complex.normSq, sq] using o.inner_sq_add_areaForm_sq x y

中文:
定理 normSq_kahler
  条件: (x y : E)
  结论: 复形.normSq (o.kahler x y) = ‖x‖ ^ 2 * ‖y‖ ^ 2
  证明: by
  simpa [kahler_apply_apply, Complex.normSq, sq] using o.inner_sq_add_areaForm_sq x y

Depends on / 依赖: Complex.normSq, inner_sq_add_areaForm_sq, kahler_apply_apply, normSq, o.inner_sq_add_areaForm_sq
-/
theorem normSq_kahler (x y : E) : Complex.normSq (o.kahler x y) = ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
  simpa [kahler_apply_apply, Complex.normSq, sq] using o.inner_sq_add_areaForm_sq x y

/--
theorem `norm_kahler` / 定理 `norm_kahler`

English:
theorem norm_kahler
  given: (x y : E)
  statement: ‖o.kahler x y‖ = ‖x‖ * ‖y‖
  proof: by
  rw [← sq_eq_sq₀]; rw [Complex.sq_norm]
  · linear_combination o.normSq_kahler x y
  · positivity
  · positivity

中文:
定理 norm_kahler
  条件: (x y : E)
  结论: ‖o.kahler x y‖ = ‖x‖ * ‖y‖
  证明: by
  rw [← sq_eq_sq₀]; rw [Complex.sq_norm]
  · linear_combination o.normSq_kahler x y
  · positivity
  · positivity

Depends on / 依赖: Complex.sq_norm, linear_combination, normSq_kahler, o.normSq_kahler, sq_norm
-/
theorem norm_kahler (x y : E) : ‖o.kahler x y‖ = ‖x‖ * ‖y‖ := by
  rw [← sq_eq_sq₀]; rw [Complex.sq_norm]
  · linear_combination o.normSq_kahler x y
  · positivity
  · positivity

/--
theorem `eq_zero_or_eq_zero_of_kahler_eq_zero` / 定理 `eq_zero_or_eq_zero_of_kahler_eq_zero`

English:
theorem eq_zero_or_eq_zero_of_kahler_eq_zero
  given: {x y : E} (hx : o.kahler x y = 0)
  statement: x = 0 ∨ y = 0
  proof: by
  have : ‖x‖ * ‖y‖ = 0 := by simpa [hx] using (o.norm_kahler x y).symm
  rcases eq_zero_or_eq_zero_of_mul_eq_zero this with h | h
  · left
    simpa using h
  · right
    simpa using h

中文:
定理 eq_zero_or_eq_zero_of_kahler_eq_zero
  条件: {x y : E} (hx : o.kahler x y = 0)
  结论: x = 0 ∨ y = 0
  证明: by
  have : ‖x‖ * ‖y‖ = 0 := by simpa [hx] using (o.norm_kahler x y).symm
  rcases eq_zero_or_eq_zero_of_mul_eq_zero this with h | h
  · left
    simpa using h
  · right
    simpa using h

Depends on / 依赖: eq_zero_or_eq_zero_of_mul_eq_zero, norm_kahler, o.norm_kahler
-/
theorem eq_zero_or_eq_zero_of_kahler_eq_zero {x y : E} (hx : o.kahler x y = 0) : x = 0 ∨ y = 0 := by
  have : ‖x‖ * ‖y‖ = 0 := by simpa [hx] using (o.norm_kahler x y).symm
  rcases eq_zero_or_eq_zero_of_mul_eq_zero this with h | h
  · left
    simpa using h
  · right
    simpa using h

/--
theorem `kahler_eq_zero_iff` / 定理 `kahler_eq_zero_iff`

English:
theorem kahler_eq_zero_iff
  given: (x y : E)
  statement: o.kahler x y = 0 ↔ x = 0 ∨ y = 0
  proof: by
  refine ⟨o.eq_zero_or_eq_zero_of_kahler_eq_zero, ?_⟩
  rintro (rfl | rfl) <;> simp

中文:
定理 kahler_eq_zero_iff
  条件: (x y : E)
  结论: o.kahler x y = 0 ↔ x = 0 ∨ y = 0
  证明: by
  refine ⟨o.eq_zero_or_eq_zero_of_kahler_eq_zero, ?_⟩
  rintro (rfl | rfl) <;> simp

Depends on / 依赖: eq_zero_or_eq_zero_of_kahler_eq_zero, o.eq_zero_or_eq_zero_of_kahler_eq_zero
-/
theorem kahler_eq_zero_iff (x y : E) : o.kahler x y = 0 ↔ x = 0 ∨ y = 0 := by
  refine ⟨o.eq_zero_or_eq_zero_of_kahler_eq_zero, ?_⟩
  rintro (rfl | rfl) <;> simp

/--
theorem `kahler_ne_zero` / 定理 `kahler_ne_zero`

English:
theorem kahler_ne_zero
  given: {x y : E} (hx : x != 0) (hy : y != 0)
  statement: o.kahler x y != 0
  proof: by
  apply mt o.eq_zero_or_eq_zero_of_kahler_eq_zero
  tauto

中文:
定理 kahler_ne_zero
  条件: {x y : E} (hx : x != 0) (hy : y != 0)
  结论: o.kahler x y != 0
  证明: by
  apply mt o.eq_zero_or_eq_zero_of_kahler_eq_zero
  tauto

Depends on / 依赖: eq_zero_or_eq_zero_of_kahler_eq_zero, o.eq_zero_or_eq_zero_of_kahler_eq_zero
-/
theorem kahler_ne_zero {x y : E} (hx : x != 0) (hy : y != 0) : o.kahler x y != 0 := by
  apply mt o.eq_zero_or_eq_zero_of_kahler_eq_zero
  tauto

/--
theorem `kahler_ne_zero_iff` / 定理 `kahler_ne_zero_iff`

English:
theorem kahler_ne_zero_iff
  given: (x y : E)
  statement: o.kahler x y != 0 ↔ x != 0 ∧ y != 0
  proof: by
  refine ⟨?_, fun h => o.kahler_ne_zero h.1 h.2⟩
  contrapose
  simp only [not_and_or, Classical.not_not, kahler_apply_apply, Complex.real_smul]
  rintro (rfl | rfl) <;> simp

中文:
定理 kahler_ne_zero_iff
  条件: (x y : E)
  结论: o.kahler x y != 0 ↔ x != 0 ∧ y != 0
  证明: by
  refine ⟨?_, fun h => o.kahler_ne_zero h.1 h.2⟩
  contrapose
  simp only [not_and_or, Classical.not_not, kahler_apply_apply, Complex.real_smul]
  rintro (rfl | rfl) <;> simp

Depends on / 依赖: Classical, Classical.not_not, Complex.real_smul, contrapose, kahler_apply_apply, kahler_ne_zero, not_and_or, not_not, o.kahler_ne_zero, real_smul
-/
theorem kahler_ne_zero_iff (x y : E) : o.kahler x y != 0 ↔ x != 0 ∧ y != 0 := by
  refine ⟨?_, fun h => o.kahler_ne_zero h.1 h.2⟩
  contrapose
  simp only [not_and_or, Classical.not_not, kahler_apply_apply, Complex.real_smul]
  rintro (rfl | rfl) <;> simp

/--
theorem `kahler_map` / 定理 `kahler_map`

English:
theorem kahler_map
  statement: {F : Type*} [NormedAddCommGroup F] [InnerProductSpace Real F]
  proof: by
  simp [kahler_apply_apply, areaForm_map]

中文:
定理 kahler_map
  结论: {F : 类型} [赋范交换加群 F] [内积空间 实数 F]
  证明: by
  simp [kahler_apply_apply, areaForm_map]

Depends on / 依赖: areaForm_map, kahler_apply_apply
-/
theorem kahler_map {F : Type*} [NormedAddCommGroup F] [InnerProductSpace Real F]
    [hF : Fact (finrank Real F = 2)] (φ : E ≃ₗᵢ[Real] F) (x y : F) :
    (Orientation.map (Fin 2) φ.toLinearEquiv o).kahler x y = o.kahler (φ.symm x) (φ.symm y) := by
  simp [kahler_apply_apply, areaForm_map]

/--
theorem `kahler_comp_linearIsometryEquiv` / 定理 `kahler_comp_linearIsometryEquiv`

English:
theorem kahler_comp_linearIsometryEquiv
  statement: (φ : E ≃ₗᵢ[Real] E)
  proof: by
  simp [kahler_apply_apply, o.areaForm_comp_linearIsometryEquiv φ hφ]

中文:
定理 kahler_comp_linearIsometryEquiv
  结论: (φ : E ≃ₗᵢ[实数] E)
  证明: by
  simp [kahler_apply_apply, o.areaForm_comp_linearIsometryEquiv φ hφ]

Depends on / 依赖: areaForm_comp_linearIsometryEquiv, kahler_apply_apply, o.areaForm_comp_linearIsometryEquiv
-/
theorem kahler_comp_linearIsometryEquiv (φ : E ≃ₗᵢ[Real] E)
    (hφ : 0 < LinearMap.det (φ.toLinearEquiv : E ->ₗ[Real] E)) (x y : E) :
    o.kahler (φ x) (φ y) = o.kahler x y := by
  simp [kahler_apply_apply, o.areaForm_comp_linearIsometryEquiv φ hφ]

end Orientation

namespace Complex

attribute [local instance] Complex.finrank_real_complex_fact

@[simp]
/--
theorem `areaForm` / 定理 `areaForm`

English:
theorem areaForm
  given: (w z : Complex)
  statement: Complex.orientation.areaForm w z = (conj w * z).im
  proof: by
  let o := Complex.orientation
  simp only [o, o.areaForm_to_volumeForm,
    o.volumeForm_robust Complex.orthonormalBasisOneI rfl, Basis.det_apply, Matrix.det_fin_two,
    Basis.toMatrix_apply, toBasis_orthonormalBasisOneI, Matrix.cons_val_zero, coe_basisOneI_repr,
    Matrix.cons_val_one, mul_im

中文:
定理 areaForm
  条件: (w z : 复形)
  结论: 复形.orientation.areaForm w z = (conj w * z).im
  证明: by
  let o := Complex.orientation
  simp only [o, o.areaForm_to_volumeForm,
    o.volumeForm_robust Complex.orthonormalBasisOneI rfl, Basis.det_apply, Matrix.det_fin_two,
    Basis.toMatrix_apply, toBasis_orthonormalBasisOneI, Matrix.cons_val_zero, coe_basisOneI_repr,
    Matrix.cons_val_one, mul_im
-/
protected theorem areaForm (w z : Complex) : Complex.orientation.areaForm w z = (conj w * z).im := by
  let o := Complex.orientation
  simp only [o, o.areaForm_to_volumeForm,
    o.volumeForm_robust Complex.orthonormalBasisOneI rfl, Basis.det_apply, Matrix.det_fin_two,
    Basis.toMatrix_apply, toBasis_orthonormalBasisOneI, Matrix.cons_val_zero, coe_basisOneI_repr,
    Matrix.cons_val_one, mul_im, conj_re, conj_im]
  ring

@[simp]
/--
theorem `rightAngleRotation` / 定理 `rightAngleRotation`

English:
theorem rightAngleRotation
  given: (z : Complex)
  proof: by
  apply ext_inner_right Real
  intro w
  rw [Orientation.inner_rightAngleRotation_left]
  simp only [Complex.areaForm, Complex.inner, mul_re, mul_im, conj_re, conj_im, map_mul, conj_I,
    neg_re, neg_im, I_re, I_im]
  ring

@[simp]

中文:
定理 rightAngleRotation
  条件: (z : 复形)
  证明: by
  apply ext_inner_right Real
  intro w
  rw [Orientation.inner_rightAngleRotation_left]
  simp only [Complex.areaForm, Complex.inner, mul_re, mul_im, conj_re, conj_im, map_mul, conj_I,
    neg_re, neg_im, I_re, I_im]
  ring

@[simp]
-/
protected theorem rightAngleRotation (z : Complex) :
    Complex.orientation.rightAngleRotation z = I * z := by
  apply ext_inner_right Real
  intro w
  rw [Orientation.inner_rightAngleRotation_left]
  simp only [Complex.areaForm, Complex.inner, mul_re, mul_im, conj_re, conj_im, map_mul, conj_I,
    neg_re, neg_im, I_re, I_im]
  ring

@[simp]
/--
theorem `kahler` / 定理 `kahler`

English:
theorem kahler
  given: (w z : Complex)
  statement: Complex.orientation.kahler w z = z * conj w
  proof: by
  rw [Orientation.kahler_apply_apply]
  apply Complex.ext <;> simp [mul_comm]

中文:
定理 kahler
  条件: (w z : 复形)
  结论: 复形.orientation.kahler w z = z * conj w
  证明: by
  rw [Orientation.kahler_apply_apply]
  apply Complex.ext <;> simp [mul_comm]
-/
protected theorem kahler (w z : Complex) : Complex.orientation.kahler w z = z * conj w := by
  rw [Orientation.kahler_apply_apply]
  apply Complex.ext <;> simp [mul_comm]

end Complex

namespace Orientation

local notation "ω" => o.areaForm

local notation "J" => o.rightAngleRotation

open Complex

/--
theorem `areaForm_map_complex` / 定理 `areaForm_map_complex`

English:
theorem areaForm_map_complex
  statement: (f : E ≃ₗᵢ[Real] Complex)
  proof: by
  rw [← Complex.areaForm]; rw [← hf]; rw [areaForm_map]
  iterate 2 rw [LinearIsometryEquiv.symm_apply_apply]

中文:
定理 areaForm_map_complex
  结论: (f : E ≃ₗᵢ[实数] 复形)
  证明: by
  rw [← Complex.areaForm]; rw [← hf]; rw [areaForm_map]
  iterate 2 rw [LinearIsometryEquiv.symm_apply_apply]

Depends on / 依赖: Complex.areaForm, LinearIsometryEquiv, LinearIsometryEquiv.symm_apply_apply, areaForm, areaForm_map, iterate, symm_apply_apply
-/
theorem areaForm_map_complex (f : E ≃ₗᵢ[Real] Complex)
    (hf : Orientation.map (Fin 2) f.toLinearEquiv o = Complex.orientation) (x y : E) :
    ω x y = (conj (f x) * f y).im := by
  rw [← Complex.areaForm]; rw [← hf]; rw [areaForm_map]
  iterate 2 rw [LinearIsometryEquiv.symm_apply_apply]

/--
theorem `rightAngleRotation_map_complex` / 定理 `rightAngleRotation_map_complex`

English:
theorem rightAngleRotation_map_complex
  statement: (f : E ≃ₗᵢ[Real] Complex)
  proof: by
  rw [← Complex.rightAngleRotation]; rw [← hf]; rw [rightAngleRotation_map]; rw [LinearIsometryEquiv.symm_apply_apply]

中文:
定理 rightAngleRotation_map_complex
  结论: (f : E ≃ₗᵢ[实数] 复形)
  证明: by
  rw [← Complex.rightAngleRotation]; rw [← hf]; rw [rightAngleRotation_map]; rw [LinearIsometryEquiv.symm_apply_apply]

Depends on / 依赖: Complex.rightAngleRotation, LinearIsometryEquiv, LinearIsometryEquiv.symm_apply_apply, rightAngleRotation, rightAngleRotation_map, symm_apply_apply
-/
theorem rightAngleRotation_map_complex (f : E ≃ₗᵢ[Real] Complex)
    (hf : Orientation.map (Fin 2) f.toLinearEquiv o = Complex.orientation) (x : E) :
    f (J x) = I * f x := by
  rw [← Complex.rightAngleRotation]; rw [← hf]; rw [rightAngleRotation_map]; rw [LinearIsometryEquiv.symm_apply_apply]

/--
theorem `kahler_map_complex` / 定理 `kahler_map_complex`

English:
theorem kahler_map_complex
  statement: (f : E ≃ₗᵢ[Real] Complex)
  proof: by
  rw [← Complex.kahler]; rw [← hf]; rw [kahler_map]
  iterate 2 rw [LinearIsometryEquiv.symm_apply_apply]

中文:
定理 kahler_map_complex
  结论: (f : E ≃ₗᵢ[实数] 复形)
  证明: by
  rw [← Complex.kahler]; rw [← hf]; rw [kahler_map]
  iterate 2 rw [LinearIsometryEquiv.symm_apply_apply]

Depends on / 依赖: Complex.kahler, LinearIsometryEquiv, LinearIsometryEquiv.symm_apply_apply, iterate, kahler, kahler_map, symm_apply_apply
-/
theorem kahler_map_complex (f : E ≃ₗᵢ[Real] Complex)
    (hf : Orientation.map (Fin 2) f.toLinearEquiv o = Complex.orientation) (x y : E) :
    o.kahler x y = f y * conj (f x) := by
  rw [← Complex.kahler]; rw [← hf]; rw [kahler_map]
  iterate 2 rw [LinearIsometryEquiv.symm_apply_apply]

end Orientation
