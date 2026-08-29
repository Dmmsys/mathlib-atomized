/-
Copyright (c) 2025 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
module

public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange

/-!
# Weierstrass equations and the nonsingular condition in affine coordinates

Let `W` be a Weierstrass curve over a commutative ring `R` with coefficients `aᵢ`. An *affine point*
on `W` is a tuple `(x, y)` of elements in `R` satisfying the *Weierstrass equation* `W(X, Y) = 0` in
*affine coordinates*, where `W(X, Y) := Y² + a₁XY + a₃Y - (X³ + a₂X² + a₄X + a₆)`. It is
*nonsingular* if its partial derivatives `W_X(x, y)` and `W_Y(x, y)` do not vanish simultaneously.

This file defines polynomials associated to Weierstrass equations and the nonsingular condition in
affine coordinates. The group law on the actual type of nonsingular points in affine coordinates
will be defined in `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean`, based on the
formulae for group operations in `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Formula.lean`.

## Main definitions

* `WeierstrassCurve.Affine.Equation`: the Weierstrass equation in affine coordinates.
* `WeierstrassCurve.Affine.Nonsingular`: the nonsingular condition in affine coordinates.

## Main statements

* `WeierstrassCurve.Affine.equation_iff_nonsingular`: an elliptic curve in affine coordinates is
  nonsingular at every point.

## Implementation notes

All definitions and lemmas for Weierstrass curves in affine coordinates live in the namespace
`WeierstrassCurve.Affine` to distinguish them from those in other coordinates. This is simply an
abbreviation for `WeierstrassCurve` that can be converted using `WeierstrassCurve.toAffine`.

## References

[J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, affine, Weierstrass equation, nonsingular
-/

@[expose] public section

open Polynomial

open scoped Polynomial.Bivariate

local macro "eval_simp" : tactic =>
  `(tactic| simp only [eval_C, eval_X, eval_neg, eval_add, eval_sub, eval_mul, eval_pow, evalEval])

local macro "map_simp" : tactic =>
  `(tactic| simp only [map_ofNat, map_neg, map_add, map_sub, map_mul, map_pow, map_div₀,
    Polynomial.map_ofNat, map_C, map_X, Polynomial.map_neg, Polynomial.map_add, Polynomial.map_sub,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_div, coe_mapRingHom,
    WeierstrassCurve.map])

universe r s u v

variable {R : Type r}

namespace WeierstrassCurve

/-! ## Affine coordinates -/

variable (R) in
/--
Definition of `Affine` / `Affine` 的定义

English:
abbreviation Affine
  signature: : Type r
  body: WeierstrassCurve R

中文:
缩写 Affine
  签名: : Type r
  定义体: WeierstrassCurve R

Depends on / 依赖: WeierstrassCurve
-/
abbrev Affine : Type r :=
  WeierstrassCurve R

/--
Definition of `toAffine` / `toAffine` 的定义

English:
abbreviation toAffine
  signature: (W : WeierstrassCurve R)
  body: W

中文:
缩写 toAffine
  签名: (W : WeierstrassCurve R)
  定义体: W
-/
abbrev toAffine (W : WeierstrassCurve R) : Affine R :=
  W

variable [CommRing R] {W : Affine R}
  {S : Type s} [CommRing S] {A : Type u} [CommRing A] {B : Type v} [CommRing B]

namespace Affine

/-! ## Weierstrass equations in affine coordinates -/

variable (W) in
/--
Definition of `polynomial` / `polynomial` 的定义

English:
definition polynomial
  signature: : R[X][Y]
  body: Y ^ 2 + C (C W.a₁ * X + C W.a₃) * Y - C (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆)

中文:
定义 polynomial
  签名: : R[X][Y]
  定义体: Y ^ 2 + C (C W.a₁ * X + C W.a₃) * Y - C (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆)
-/
noncomputable def polynomial : R[X][Y] :=
  Y ^ 2 + C (C W.a₁ * X + C W.a₃) * Y - C (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆)

/--
lemma `polynomial_eq` / 引理 `polynomial_eq`

English:
lemma polynomial_eq
  statement: W.polynomial = Cubic.toPoly
  proof: by
  simp_rw [polynomial, Cubic.toPoly]
  map_simp
  simp only [C_0, C_1]
  ring1

中文:
引理 polynomial_eq
  结论: W.polynomial = Cubic.toPoly
  证明: by
  simp_rw [polynomial, Cubic.toPoly]
  map_simp
  simp only [C_0, C_1]
  ring1

Depends on / 依赖: Cubic.toPoly, map_simp, polynomial, simp_rw, toPoly
-/
lemma polynomial_eq : W.polynomial = Cubic.toPoly
    ⟨0, 1, Cubic.toPoly ⟨0, 0, W.a₁, W.a₃⟩, Cubic.toPoly ⟨-1, -W.a₂, -W.a₄, -W.a₆⟩⟩ := by
  simp_rw [polynomial, Cubic.toPoly]
  map_simp
  simp only [C_0, C_1]
  ring1

/--
lemma `polynomial_ne_zero` / 引理 `polynomial_ne_zero`

English:
lemma polynomial_ne_zero
  given: [Nontrivial R]
  statement: W.polynomial != 0
  proof: by
  rw [polynomial_eq]
  exact Cubic.ne_zero_of_b_ne_zero one_ne_zero

@[simp]

中文:
引理 polynomial_ne_zero
  条件: [Nontrivial R]
  结论: W.polynomial != 0
  证明: by
  rw [polynomial_eq]
  exact Cubic.ne_zero_of_b_ne_zero one_ne_zero

@[simp]

Depends on / 依赖: Cubic.ne_zero_of_b_ne_zero, ne_zero_of_b_ne_zero, one_ne_zero, polynomial_eq
-/
lemma polynomial_ne_zero [Nontrivial R] : W.polynomial != 0 := by
  rw [polynomial_eq]
  exact Cubic.ne_zero_of_b_ne_zero one_ne_zero

@[simp]
/--
lemma `degree_polynomial` / 引理 `degree_polynomial`

English:
lemma degree_polynomial
  given: [Nontrivial R]
  statement: W.polynomial.degree = 2
  proof: by
  rw [polynomial_eq]
  exact Cubic.degree_of_b_ne_zero' one_ne_zero

@[simp]

中文:
引理 degree_polynomial
  条件: [Nontrivial R]
  结论: W.polynomial.degree = 2
  证明: by
  rw [polynomial_eq]
  exact Cubic.degree_of_b_ne_zero' one_ne_zero

@[simp]

Depends on / 依赖: Cubic.degree_of_b_ne_zero, EffectiveEpimorphic, GrothendieckTopology, GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable, Precoverage, Precoverage.generate_mem_toGrothendieck, Presieve, Presieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda, Sieve.effectiveEpimorphic_singleton, Subcanonical, degree_of_b_ne_zero, effectiveEpimorphic_singleton, f.singleton_mem_fpqcPrecoverage, generate_mem_toGrothendieck, iff_forall_isSheafFor_yoneda, isSheafFor, isSheaf_of_isRepresentable, one_ne_zero, polynomial_eq, singleton_mem_fpqcPrecoverage
-/
lemma degree_polynomial [Nontrivial R] : W.polynomial.degree = 2 := by
  rw [polynomial_eq]
  exact Cubic.degree_of_b_ne_zero' one_ne_zero

@[simp]
/--
lemma `natDegree_polynomial` / 引理 `natDegree_polynomial`

English:
lemma natDegree_polynomial
  given: [Nontrivial R]
  statement: W.polynomial.natDegree = 2
  proof: by
  rw [polynomial_eq]
  exact Cubic.natDegree_of_b_ne_zero' one_ne_zero

中文:
引理 natDegree_polynomial
  条件: [Nontrivial R]
  结论: W.polynomial.natDegree = 2
  证明: by
  rw [polynomial_eq]
  exact Cubic.natDegree_of_b_ne_zero' one_ne_zero

Depends on / 依赖: Cubic.natDegree_of_b_ne_zero, EffectiveEpimorphic, GrothendieckTopology, GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable, Precoverage, Precoverage.generate_mem_toGrothendieck, Presieve, Presieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda, Sieve.effectiveEpimorphic_singleton, Subcanonical, effectiveEpimorphic_singleton, f.singleton_mem_fppfPrecoverage, generate_mem_toGrothendieck, iff_forall_isSheafFor_yoneda, isSheafFor, isSheaf_of_isRepresentable, natDegree_of_b_ne_zero, one_ne_zero, polynomial_eq, singleton_mem_fppfPrecoverage
-/
lemma natDegree_polynomial [Nontrivial R] : W.polynomial.natDegree = 2 := by
  rw [polynomial_eq]
  exact Cubic.natDegree_of_b_ne_zero' one_ne_zero

/--
lemma `monic_polynomial` / 引理 `monic_polynomial`

English:
lemma monic_polynomial
  statement: W.polynomial.Monic
  proof: by
  simpa only [polynomial_eq] using Cubic.monic_of_b_eq_one'

中文:
引理 monic_polynomial
  结论: W.polynomial.Monic
  证明: by
  simpa only [polynomial_eq] using Cubic.monic_of_b_eq_one'

Depends on / 依赖: Cubic.monic_of_b_eq_one, monic_of_b_eq_one, polynomial_eq
-/
lemma monic_polynomial : W.polynomial.Monic := by
  simpa only [polynomial_eq] using Cubic.monic_of_b_eq_one'

/--
lemma `irreducible_polynomial` / 引理 `irreducible_polynomial`

English:
lemma irreducible_polynomial
  given: [IsDomain R]
  statement: Irreducible W.polynomial
  proof: by
  by_contra h
  rcases (monic_polynomial.not_irreducible_iff_exists_add_mul_eq_coeff natDegree_polynomial).mp h
    with ⟨f, g, h0, h1⟩
  simp only [polynomial_eq, Cubic.coeff_eq_c, Cubic.coeff_eq_d] at h0 h1
  apply_fun degree at h0 h1
  rw [Cubic.degree_of_a_ne_zero' <| neg_ne_zero.mpr <| one_n

中文:
引理 irreducible_polynomial
  条件: [IsDomain R]
  结论: Irreducible W.polynomial
  证明: by
  by_contra h
  rcases (monic_polynomial.not_irreducible_iff_exists_add_mul_eq_coeff natDegree_polynomial).mp h
    with ⟨f, g, h0, h1⟩
  simp only [polynomial_eq, Cubic.coeff_eq_c, Cubic.coeff_eq_d] at h0 h1
  apply_fun degree at h0 h1
  rw [Cubic.degree_of_a_ne_zero' <| neg_ne_zero.mpr <| one_n

Depends on / 依赖: Cubic.coeff_eq_c, Cubic.coeff_eq_d, Cubic.degree_of_a_ne_zero, Cubic.degree_of_b_eq_zero, Nat.WithBot.add_eq_three_iff.mp, WithBot, add_eq_three_iff, apply_fun, coeff_eq_c, coeff_eq_d, degree, degree_add_eq_right_of_degree_lt, degree_mul, degree_of_a_ne_zero, degree_of_b_eq_zero, h0.symm, h1.symm.le.trans, iterate, monic_polynomial, monic_polynomial.not_irreducible_iff_exists_add_mul_eq_coeff
-/
lemma irreducible_polynomial [IsDomain R] : Irreducible W.polynomial := by
  by_contra h
  rcases (monic_polynomial.not_irreducible_iff_exists_add_mul_eq_coeff natDegree_polynomial).mp h
    with ⟨f, g, h0, h1⟩
  simp only [polynomial_eq, Cubic.coeff_eq_c, Cubic.coeff_eq_d] at h0 h1
  apply_fun degree at h0 h1
  rw [Cubic.degree_of_a_ne_zero' <| neg_ne_zero.mpr <| one_ne_zero' R]; rw [degree_mul] at h0
  apply (h1.symm.le.trans Cubic.degree_of_b_eq_zero').not_gt
  rcases Nat.WithBot.add_eq_three_iff.mp h0.symm with h | h | h | h
  iterate 2 rw [degree_add_eq_right_of_degree_lt] <;> simp only [h] <;> decide
  iterate 2 rw [degree_add_eq_left_of_degree_lt] <;> simp only [h] <;> decide

/--
lemma `evalEval_polynomial` / 引理 `evalEval_polynomial`

English:
lemma evalEval_polynomial
  given: (x y : R)
  statement: W.polynomial.evalEval x y =
  proof: by
  simp only [polynomial]
  eval_simp
  rw [add_mul]; rw [← add_assoc]

@[simp]

中文:
引理 evalEval_polynomial
  条件: (x y : R)
  结论: W.polynomial.evalEval x y =
  证明: by
  simp only [polynomial]
  eval_simp
  rw [add_mul]; rw [← add_assoc]

@[simp]

Depends on / 依赖: add_assoc, add_mul, eval_simp, polynomial
-/
lemma evalEval_polynomial (x y : R) : W.polynomial.evalEval x y =
    y ^ 2 + W.a₁ * x * y + W.a₃ * y - (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) := by
  simp only [polynomial]
  eval_simp
  rw [add_mul]; rw [← add_assoc]

@[simp]
/--
lemma `evalEval_polynomial_zero` / 引理 `evalEval_polynomial_zero`

English:
lemma evalEval_polynomial_zero
  statement: W.polynomial.evalEval 0 0 = -W.a₆
  proof: by
  simp only [evalEval_polynomial, zero_add, zero_sub, mul_zero, zero_pow <| Nat.succ_ne_zero _]

中文:
引理 evalEval_polynomial_zero
  结论: W.polynomial.evalEval 0 0 = -W.a₆
  证明: by
  simp only [evalEval_polynomial, zero_add, zero_sub, mul_zero, zero_pow <| Nat.succ_ne_zero _]

Depends on / 依赖: Nat.succ_ne_zero, evalEval_polynomial, mul_zero, succ_ne_zero, zero_add, zero_pow, zero_sub
-/
lemma evalEval_polynomial_zero : W.polynomial.evalEval 0 0 = -W.a₆ := by
  simp only [evalEval_polynomial, zero_add, zero_sub, mul_zero, zero_pow <| Nat.succ_ne_zero _]

variable (W) in
/--
Definition of `Equation` / `Equation` 的定义

English:
definition Equation
  signature: (x y : R)
  body: W.polynomial.evalEval x y = 0

中文:
定义 Equation
  签名: (x y : R)
  定义体: W.polynomial.evalEval x y = 0

Depends on / 依赖: W.polynomial.evalEval, evalEval, polynomial
-/
def Equation (x y : R) : Prop :=
  W.polynomial.evalEval x y = 0

/--
lemma `equation_iff'` / 引理 `equation_iff'`

English:
lemma equation_iff'
  given: (x y : R)
  statement: W.Equation x y ↔
  proof: by
  rw [Equation]; rw [evalEval_polynomial]

中文:
引理 equation_iff'
  条件: (x y : R)
  结论: W.Equation x y ↔
  证明: by
  rw [Equation]; rw [evalEval_polynomial]

Depends on / 依赖: Equation, evalEval_polynomial
-/
lemma equation_iff' (x y : R) : W.Equation x y ↔
    y ^ 2 + W.a₁ * x * y + W.a₃ * y - (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) = 0 := by
  rw [Equation]; rw [evalEval_polynomial]

/--
lemma `equation_iff` / 引理 `equation_iff`

English:
lemma equation_iff
  given: (x y : R)
  statement: W.Equation x y ↔
  proof: by
  rw [equation_iff']; rw [sub_eq_zero]

@[simp]

中文:
引理 equation_iff
  条件: (x y : R)
  结论: W.Equation x y ↔
  证明: by
  rw [equation_iff']; rw [sub_eq_zero]

@[simp]

Depends on / 依赖: equation_iff, sub_eq_zero
-/
lemma equation_iff (x y : R) : W.Equation x y ↔
    y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ := by
  rw [equation_iff']; rw [sub_eq_zero]

@[simp]
/--
lemma `equation_zero` / 引理 `equation_zero`

English:
lemma equation_zero
  statement: W.Equation 0 0 ↔ W.a₆ = 0
  proof: by
  rw [Equation]; rw [evalEval_polynomial_zero]; rw [neg_eq_zero]

中文:
引理 equation_zero
  结论: W.Equation 0 0 ↔ W.a₆ = 0
  证明: by
  rw [Equation]; rw [evalEval_polynomial_zero]; rw [neg_eq_zero]

Depends on / 依赖: Equation, evalEval_polynomial_zero, neg_eq_zero
-/
lemma equation_zero : W.Equation 0 0 ↔ W.a₆ = 0 := by
  rw [Equation]; rw [evalEval_polynomial_zero]; rw [neg_eq_zero]

/--
lemma `equation_iff_variableChange` / 引理 `equation_iff_variableChange`

English:
lemma equation_iff_variableChange
  given: (x y : R)
  proof: by
  rw [equation_iff']; rw [← neg_eq_zero]; rw [equation_zero]; rw [variableChange_a₆]; rw [inv_one]; rw [Units.val_one]
  congr! 1
  ring1

中文:
引理 equation_iff_variableChange
  条件: (x y : R)
  证明: by
  rw [equation_iff']; rw [← neg_eq_zero]; rw [equation_zero]; rw [variableChange_a₆]; rw [inv_one]; rw [Units.val_one]
  congr! 1
  ring1

Depends on / 依赖: Units.val_one, equation_iff, equation_zero, inv_one, neg_eq_zero, val_one
-/
lemma equation_iff_variableChange (x y : R) :
    W.Equation x y ↔ (VariableChange.mk 1 x 0 y • W).toAffine.Equation 0 0 := by
  rw [equation_iff']; rw [← neg_eq_zero]; rw [equation_zero]; rw [variableChange_a₆]; rw [inv_one]; rw [Units.val_one]
  congr! 1
  ring1

/-! ## The nonsingular condition in affine coordinates -/

variable (W) in
-- TODO: define this in terms of `Polynomial.derivative`.
/--
Definition of `polynomialX` / `polynomialX` 的定义

English:
definition polynomialX
  signature: : R[X][Y]
  body: C (C W.a₁) * Y - C (C 3 * X ^ 2 + C (2 * W.a₂) * X + C W.a₄)

中文:
定义 polynomialX
  签名: : R[X][Y]
  定义体: C (C W.a₁) * Y - C (C 3 * X ^ 2 + C (2 * W.a₂) * X + C W.a₄)
-/
noncomputable def polynomialX : R[X][Y] :=
  C (C W.a₁) * Y - C (C 3 * X ^ 2 + C (2 * W.a₂) * X + C W.a₄)

/--
lemma `evalEval_polynomialX` / 引理 `evalEval_polynomialX`

English:
lemma evalEval_polynomialX
  given: (x y : R)
  proof: by
  simp only [polynomialX]
  eval_simp

@[simp]

中文:
引理 evalEval_polynomialX
  条件: (x y : R)
  证明: by
  simp only [polynomialX]
  eval_simp

@[simp]

Depends on / 依赖: eval_simp, polynomialX
-/
lemma evalEval_polynomialX (x y : R) :
    W.polynomialX.evalEval x y = W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) := by
  simp only [polynomialX]
  eval_simp

@[simp]
/--
lemma `evalEval_polynomialX_zero` / 引理 `evalEval_polynomialX_zero`

English:
lemma evalEval_polynomialX_zero
  statement: W.polynomialX.evalEval 0 0 = -W.a₄
  proof: by
  simp only [evalEval_polynomialX, zero_add, zero_sub, mul_zero, zero_pow <| Nat.succ_ne_zero _]

中文:
引理 evalEval_polynomialX_zero
  结论: W.polynomialX.evalEval 0 0 = -W.a₄
  证明: by
  simp only [evalEval_polynomialX, zero_add, zero_sub, mul_zero, zero_pow <| Nat.succ_ne_zero _]

Depends on / 依赖: Nat.succ_ne_zero, evalEval_polynomialX, mul_zero, succ_ne_zero, zero_add, zero_pow, zero_sub
-/
lemma evalEval_polynomialX_zero : W.polynomialX.evalEval 0 0 = -W.a₄ := by
  simp only [evalEval_polynomialX, zero_add, zero_sub, mul_zero, zero_pow <| Nat.succ_ne_zero _]

variable (W) in
-- TODO: define this in terms of `Polynomial.derivative`.
/--
Definition of `polynomialY` / `polynomialY` 的定义

English:
definition polynomialY
  signature: : R[X][Y]
  body: C (C 2) * Y + C (C W.a₁ * X + C W.a₃)

中文:
定义 polynomialY
  签名: : R[X][Y]
  定义体: C (C 2) * Y + C (C W.a₁ * X + C W.a₃)
-/
noncomputable def polynomialY : R[X][Y] :=
  C (C 2) * Y + C (C W.a₁ * X + C W.a₃)

/--
lemma `evalEval_polynomialY` / 引理 `evalEval_polynomialY`

English:
lemma evalEval_polynomialY
  given: (x y : R)
  statement: W.polynomialY.evalEval x y = 2 * y + W.a₁ * x + W.a₃
  proof: by
  simp only [polynomialY]
  eval_simp
  rw [← add_assoc]

@[simp]

中文:
引理 evalEval_polynomialY
  条件: (x y : R)
  结论: W.polynomialY.evalEval x y = 2 * y + W.a₁ * x + W.a₃
  证明: by
  simp only [polynomialY]
  eval_simp
  rw [← add_assoc]

@[simp]

Depends on / 依赖: add_assoc, eval_simp, polynomialY
-/
lemma evalEval_polynomialY (x y : R) : W.polynomialY.evalEval x y = 2 * y + W.a₁ * x + W.a₃ := by
  simp only [polynomialY]
  eval_simp
  rw [← add_assoc]

@[simp]
/--
lemma `evalEval_polynomialY_zero` / 引理 `evalEval_polynomialY_zero`

English:
lemma evalEval_polynomialY_zero
  statement: W.polynomialY.evalEval 0 0 = W.a₃
  proof: by
  simp only [evalEval_polynomialY, zero_add, mul_zero]

中文:
引理 evalEval_polynomialY_zero
  结论: W.polynomialY.evalEval 0 0 = W.a₃
  证明: by
  simp only [evalEval_polynomialY, zero_add, mul_zero]

Depends on / 依赖: evalEval_polynomialY, mul_zero, zero_add
-/
lemma evalEval_polynomialY_zero : W.polynomialY.evalEval 0 0 = W.a₃ := by
  simp only [evalEval_polynomialY, zero_add, mul_zero]

variable (W) in
-- TODO: generalise this definition to be mathematically accurate for a larger class of rings.
/--
Definition of `Nonsingular` / `Nonsingular` 的定义

English:
definition Nonsingular
  signature: (x y : R)
  body: W.Equation x y ∧ (W.polynomialX.evalEval x y != 0 ∨ W.polynomialY.evalEval x y != 0)

中文:
定义 Nonsingular
  签名: (x y : R)
  定义体: W.Equation x y ∧ (W.polynomialX.evalEval x y != 0 ∨ W.polynomialY.evalEval x y != 0)

Depends on / 依赖: Equation, W.Equation, W.polynomialX.evalEval, W.polynomialY.evalEval, evalEval, polynomialX, polynomialY
-/
def Nonsingular (x y : R) : Prop :=
  W.Equation x y ∧ (W.polynomialX.evalEval x y != 0 ∨ W.polynomialY.evalEval x y != 0)

/--
lemma `nonsingular_iff'` / 引理 `nonsingular_iff'`

English:
lemma nonsingular_iff'
  given: (x y : R)
  statement: W.Nonsingular x y ↔ W.Equation x y ∧
  proof: by
  rw [Nonsingular]; rw [equation_iff']; rw [evalEval_polynomialX]; rw [evalEval_polynomialY]

中文:
引理 nonsingular_iff'
  条件: (x y : R)
  结论: W.Nonsingular x y ↔ W.Equation x y ∧
  证明: by
  rw [Nonsingular]; rw [equation_iff']; rw [evalEval_polynomialX]; rw [evalEval_polynomialY]

Depends on / 依赖: Nonsingular, equation_iff, evalEval_polynomialX, evalEval_polynomialY
-/
lemma nonsingular_iff' (x y : R) : W.Nonsingular x y ↔ W.Equation x y ∧
    (W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) != 0 ∨ 2 * y + W.a₁ * x + W.a₃ != 0) := by
  rw [Nonsingular]; rw [equation_iff']; rw [evalEval_polynomialX]; rw [evalEval_polynomialY]

/--
lemma `nonsingular_iff` / 引理 `nonsingular_iff`

English:
lemma nonsingular_iff
  given: (x y : R)
  statement: W.Nonsingular x y ↔ W.Equation x y ∧
  proof: by
  rw [nonsingular_iff']; rw [sub_ne_zero]; rw [← sub_ne_zero (a := y)]
  congr! 3
  ring1

@[simp]

中文:
引理 nonsingular_iff
  条件: (x y : R)
  结论: W.Nonsingular x y ↔ W.Equation x y ∧
  证明: by
  rw [nonsingular_iff']; rw [sub_ne_zero]; rw [← sub_ne_zero (a := y)]
  congr! 3
  ring1

@[simp]

Depends on / 依赖: nonsingular_iff, sub_ne_zero
-/
lemma nonsingular_iff (x y : R) : W.Nonsingular x y ↔ W.Equation x y ∧
    (W.a₁ * y != 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ ∨ y != -y - W.a₁ * x - W.a₃) := by
  rw [nonsingular_iff']; rw [sub_ne_zero]; rw [← sub_ne_zero (a := y)]
  congr! 3
  ring1

@[simp]
/--
lemma `nonsingular_zero` / 引理 `nonsingular_zero`

English:
lemma nonsingular_zero
  statement: W.Nonsingular 0 0 ↔ W.a₆ = 0 ∧ (W.a₃ != 0 ∨ W.a₄ != 0)
  proof: by
  rw [Nonsingular]; rw [equation_zero]; rw [evalEval_polynomialX_zero]; rw [neg_ne_zero]; rw [evalEval_polynomialY_zero]; rw [or_comm]

中文:
引理 nonsingular_zero
  结论: W.Nonsingular 0 0 ↔ W.a₆ = 0 ∧ (W.a₃ != 0 ∨ W.a₄ != 0)
  证明: by
  rw [Nonsingular]; rw [equation_zero]; rw [evalEval_polynomialX_zero]; rw [neg_ne_zero]; rw [evalEval_polynomialY_zero]; rw [or_comm]

Depends on / 依赖: Nonsingular, equation_zero, evalEval_polynomialX_zero, evalEval_polynomialY_zero, neg_ne_zero, or_comm
-/
lemma nonsingular_zero : W.Nonsingular 0 0 ↔ W.a₆ = 0 ∧ (W.a₃ != 0 ∨ W.a₄ != 0) := by
  rw [Nonsingular]; rw [equation_zero]; rw [evalEval_polynomialX_zero]; rw [neg_ne_zero]; rw [evalEval_polynomialY_zero]; rw [or_comm]

/--
lemma `nonsingular_iff_variableChange` / 引理 `nonsingular_iff_variableChange`

English:
lemma nonsingular_iff_variableChange
  given: (x y : R)
  proof: by
  rw [nonsingular_iff']; rw [equation_iff_variableChange]; rw [equation_zero]; rw [← neg_ne_zero]; rw [or_comm]; rw [nonsingular_zero]; rw [variableChange_a₃]; rw [variableChange_a₄]; rw [inv_one]; rw [Units.val_one]
  simp only [variableChange_def]
  congr! 3 <;> ring1

中文:
引理 nonsingular_iff_variableChange
  条件: (x y : R)
  证明: by
  rw [nonsingular_iff']; rw [equation_iff_variableChange]; rw [equation_zero]; rw [← neg_ne_zero]; rw [or_comm]; rw [nonsingular_zero]; rw [variableChange_a₃]; rw [variableChange_a₄]; rw [inv_one]; rw [Units.val_one]
  simp only [variableChange_def]
  congr! 3 <;> ring1

Depends on / 依赖: Units.val_one, equation_iff_variableChange, equation_zero, inv_one, neg_ne_zero, nonsingular_iff, nonsingular_zero, or_comm, val_one, variableChange_def
-/
lemma nonsingular_iff_variableChange (x y : R) :
    W.Nonsingular x y ↔ (VariableChange.mk 1 x 0 y • W).toAffine.Nonsingular 0 0 := by
  rw [nonsingular_iff']; rw [equation_iff_variableChange]; rw [equation_zero]; rw [← neg_ne_zero]; rw [or_comm]; rw [nonsingular_zero]; rw [variableChange_a₃]; rw [variableChange_a₄]; rw [inv_one]; rw [Units.val_one]
  simp only [variableChange_def]
  congr! 3 <;> ring1

/--
lemma `equation_zero_iff_nonsingular_zero_of_Δ_ne_zero` / 引理 `equation_zero_iff_nonsingular_zero_of_Δ_ne_zero`

English:
lemma equation_zero_iff_nonsingular_zero_of_Δ_ne_zero
  given: (hΔ : W.Δ != 0)
  proof: by
  simp only [equation_zero, nonsingular_zero, iff_self_and]
  contrapose! hΔ
  simp only [b₂, b₄, b₆, b₈, Δ, hΔ]
  ring1

中文:
引理 equation_zero_iff_nonsingular_zero_of_Δ_ne_zero
  条件: (hΔ : W.Δ != 0)
  证明: by
  simp only [equation_zero, nonsingular_zero, iff_self_and]
  contrapose! hΔ
  simp only [b₂, b₄, b₆, b₈, Δ, hΔ]
  ring1
-/
private lemma equation_zero_iff_nonsingular_zero_of_Δ_ne_zero (hΔ : W.Δ != 0) :
    W.Equation 0 0 ↔ W.Nonsingular 0 0 := by
  simp only [equation_zero, nonsingular_zero, iff_self_and]
  contrapose! hΔ
  simp only [b₂, b₄, b₆, b₈, Δ, hΔ]
  ring1

/--
lemma `equation_iff_nonsingular_of_Δ_ne_zero` / 引理 `equation_iff_nonsingular_of_Δ_ne_zero`

English:
lemma equation_iff_nonsingular_of_Δ_ne_zero
  given: {x y : R} (hΔ : W.Δ != 0)
  proof: by
  rw [equation_iff_variableChange]; rw [nonsingular_iff_variableChange]; rw [equation_zero_iff_nonsingular_zero_of_Δ_ne_zero by
      rwa [variableChange_Δ]; rw [inv_one]; rw [Units.val_one]; rw [one_pow]; rw [one_mul]]

中文:
引理 equation_iff_nonsingular_of_Δ_ne_zero
  条件: {x y : R} (hΔ : W.Δ != 0)
  证明: by
  rw [equation_iff_variableChange]; rw [nonsingular_iff_variableChange]; rw [equation_zero_iff_nonsingular_zero_of_Δ_ne_zero by
      rwa [variableChange_Δ]; rw [inv_one]; rw [Units.val_one]; rw [one_pow]; rw [one_mul]]

Depends on / 依赖: Units.val_one, equation_iff_variableChange, inv_one, nonsingular_iff_variableChange, one_mul, one_pow, val_one
-/
lemma equation_iff_nonsingular_of_Δ_ne_zero {x y : R} (hΔ : W.Δ != 0) :
    W.Equation x y ↔ W.Nonsingular x y := by
  rw [equation_iff_variableChange]; rw [nonsingular_iff_variableChange]; rw [equation_zero_iff_nonsingular_zero_of_Δ_ne_zero by
      rwa [variableChange_Δ]; rw [inv_one]; rw [Units.val_one]; rw [one_pow]; rw [one_mul]]

/--
lemma `equation_iff_nonsingular` / 引理 `equation_iff_nonsingular`

English:
lemma equation_iff_nonsingular
  given: [Nontrivial R] [W.IsElliptic] {x y : R}
  proof: W.equation_iff_nonsingular_of_Δ_ne_zero W.coe_Δ' ▸ W.Δ'.ne_zero

中文:
引理 equation_iff_nonsingular
  条件: [Nontrivial R] [W.IsElliptic] {x y : R}
  证明: W.equation_iff_nonsingular_of_Δ_ne_zero W.coe_Δ' ▸ W.Δ'.ne_zero

Depends on / 依赖: W.coe_, W.equation_iff_nonsingular_of_, ne_zero
-/
lemma equation_iff_nonsingular [Nontrivial R] [W.IsElliptic] {x y : R} :
    W.Equation x y ↔ W.Nonsingular x y :=
W.equation_iff_nonsingular_of_Δ_ne_zero W.coe_Δ' ▸ W.Δ'.ne_zero

/-! ### Maps and base changes -/

variable (W) (f : R ->+* S)

/--
Definition of `map` / `map` 的定义

English:
abbreviation map
  signature: : Affine S
  body: WeierstrassCurve.map W f

中文:
缩写 map
  签名: : Affine S
  定义体: WeierstrassCurve.map W f

Depends on / 依赖: WeierstrassCurve, WeierstrassCurve.map
-/
abbrev map : Affine S :=
  WeierstrassCurve.map W f

variable (S) in
/-- The Weierstrass curve in affine coordinates base changed to an algebra `S` over `R`. -/
@[simps!]
/--
Definition of `baseChange` / `baseChange` 的定义

English:
abbreviation baseChange
  signature: [Algebra R S]
  body: WeierstrassCurve.baseChange W S

中文:
缩写 baseChange
  签名: [Algebra R S]
  定义体: WeierstrassCurve.baseChange W S

Depends on / 依赖: WeierstrassCurve, WeierstrassCurve.baseChange, baseChange
-/
abbrev baseChange [Algebra R S] : Affine S :=
  WeierstrassCurve.baseChange W S

/-- The notation `\textf` for `WeierstrassCurve.Affine.baseChange W S`. -/
scoped notation:max W:max "⁄" S:max => baseChange W S

/--
lemma `map_polynomial` / 引理 `map_polynomial`

English:
lemma map_polynomial
  statement: (W.map f).polynomial = W.polynomial.map (mapRingHom f)
  proof: by
  simp only [polynomial]
  map_simp

中文:
引理 map_polynomial
  结论: (W.map f).polynomial = W.polynomial.map (mapRingHom f)
  证明: by
  simp only [polynomial]
  map_simp

Depends on / 依赖: map_simp, polynomial
-/
lemma map_polynomial : (W.map f).polynomial = W.polynomial.map (mapRingHom f) := by
  simp only [polynomial]
  map_simp

variable {W} in
/--
lemma `Equation.map` / 引理 `Equation.map`

English:
lemma Equation.map
  given: {x y : R} (h : W.Equation x y)
  statement: (W.map f).Equation (f x) (f y)
  proof: by
  rw [Equation]; rw [map_polynomial]; rw [map_mapRingHom_evalEval]; rw [h]; rw [map_zero]

中文:
引理 Equation.map
  条件: {x y : R} (h : W.Equation x y)
  结论: (W.map f).Equation (f x) (f y)
  证明: by
  rw [Equation]; rw [map_polynomial]; rw [map_mapRingHom_evalEval]; rw [h]; rw [map_zero]

Depends on / 依赖: Equation, map_mapRingHom_evalEval, map_polynomial, map_zero
-/
lemma Equation.map {x y : R} (h : W.Equation x y) : (W.map f).Equation (f x) (f y) := by
  rw [Equation]; rw [map_polynomial]; rw [map_mapRingHom_evalEval]; rw [h]; rw [map_zero]

variable {f} in
/--
lemma `map_equation` / 引理 `map_equation`

English:
lemma map_equation
  given: (hf : Function.Injective f) (x y : R)
  proof: by
  simp only [Equation, map_polynomial, map_mapRingHom_evalEval, map_eq_zero_iff f hf]

中文:
引理 map_equation
  条件: (hf : Function.Injective f) (x y : R)
  证明: by
  simp only [Equation, map_polynomial, map_mapRingHom_evalEval, map_eq_zero_iff f hf]

Depends on / 依赖: Equation, map_eq_zero_iff, map_mapRingHom_evalEval, map_polynomial
-/
lemma map_equation (hf : Function.Injective f) (x y : R) :
    (W.map f).Equation (f x) (f y) ↔ W.Equation x y := by
  simp only [Equation, map_polynomial, map_mapRingHom_evalEval, map_eq_zero_iff f hf]

/--
lemma `map_polynomialX` / 引理 `map_polynomialX`

English:
lemma map_polynomialX
  statement: (W.map f).polynomialX = W.polynomialX.map (mapRingHom f)
  proof: by
  simp only [polynomialX]
  map_simp

中文:
引理 map_polynomialX
  结论: (W.map f).polynomialX = W.polynomialX.map (mapRingHom f)
  证明: by
  simp only [polynomialX]
  map_simp

Depends on / 依赖: map_simp, polynomialX
-/
lemma map_polynomialX : (W.map f).polynomialX = W.polynomialX.map (mapRingHom f) := by
  simp only [polynomialX]
  map_simp

/--
lemma `map_polynomialY` / 引理 `map_polynomialY`

English:
lemma map_polynomialY
  statement: (W.map f).polynomialY = W.polynomialY.map (mapRingHom f)
  proof: by
  simp only [polynomialY]
  map_simp

中文:
引理 map_polynomialY
  结论: (W.map f).polynomialY = W.polynomialY.map (mapRingHom f)
  证明: by
  simp only [polynomialY]
  map_simp

Depends on / 依赖: map_simp, polynomialY
-/
lemma map_polynomialY : (W.map f).polynomialY = W.polynomialY.map (mapRingHom f) := by
  simp only [polynomialY]
  map_simp

variable {f} in
/--
lemma `map_nonsingular` / 引理 `map_nonsingular`

English:
lemma map_nonsingular
  given: (hf : Function.Injective f) (x y : R)
  proof: by
  simp only [Nonsingular, evalEval, W.map_equation hf, map_polynomialX, map_polynomialY,
    map_mapRingHom_evalEval, map_ne_zero_iff f hf]

中文:
引理 map_nonsingular
  条件: (hf : Function.Injective f) (x y : R)
  证明: by
  simp only [Nonsingular, evalEval, W.map_equation hf, map_polynomialX, map_polynomialY,
    map_mapRingHom_evalEval, map_ne_zero_iff f hf]

Depends on / 依赖: Nonsingular, W.map_equation, evalEval, map_equation, map_mapRingHom_evalEval, map_ne_zero_iff, map_polynomialX, map_polynomialY
-/
lemma map_nonsingular (hf : Function.Injective f) (x y : R) :
    (W.map f).Nonsingular (f x) (f y) ↔ W.Nonsingular x y := by
  simp only [Nonsingular, evalEval, W.map_equation hf, map_polynomialX, map_polynomialY,
    map_mapRingHom_evalEval, map_ne_zero_iff f hf]

variable [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A] [Algebra R B] [Algebra S B]
  [IsScalarTower R S B] (f : A ->ₐ[S] B)

/--
lemma `map_baseChange` / 引理 `map_baseChange`

English:
lemma map_baseChange
  statement: (W⁄A).map f = W⁄B
  proof: WeierstrassCurve.map_baseChange W f

中文:
引理 map_baseChange
  结论: (W⁄A).map f = W⁄B
  证明: WeierstrassCurve.map_baseChange W f

Depends on / 依赖: WeierstrassCurve, WeierstrassCurve.map_baseChange, map_baseChange
-/
lemma map_baseChange : (W⁄A).map f = W⁄B :=
  WeierstrassCurve.map_baseChange W f

/--
lemma `baseChange_polynomial` / 引理 `baseChange_polynomial`

English:
lemma baseChange_polynomial
  statement: (W⁄B).polynomial = (W⁄A).polynomial.map (mapRingHom f)
  proof: by
  rw [← map_polynomial]; rw [map_baseChange]

中文:
引理 baseChange_polynomial
  结论: (W⁄B).polynomial = (W⁄A).polynomial.map (mapRingHom f)
  证明: by
  rw [← map_polynomial]; rw [map_baseChange]

Depends on / 依赖: map_baseChange, map_polynomial
-/
lemma baseChange_polynomial : (W⁄B).polynomial = (W⁄A).polynomial.map (mapRingHom f) := by
  rw [← map_polynomial]; rw [map_baseChange]

variable {W} in
/--
lemma `Equation.baseChange` / 引理 `Equation.baseChange`

English:
lemma Equation.baseChange
  given: {x y : A} (h : (W⁄A).Equation x y)
  statement: (W⁄B).Equation (f x) (f y)
  proof: by
  convert! Equation.map f.toRingHom h using 1
  rw [AlgHom.toRingHom_eq_coe]; rw [map_baseChange]

中文:
引理 Equation.baseChange
  条件: {x y : A} (h : (W⁄A).Equation x y)
  结论: (W⁄B).Equation (f x) (f y)
  证明: by
  convert! Equation.map f.toRingHom h using 1
  rw [AlgHom.toRingHom_eq_coe]; rw [map_baseChange]

Depends on / 依赖: AlgHom, AlgHom.toRingHom_eq_coe, Equation, Equation.map, convert, f.toRingHom, map_baseChange, toRingHom, toRingHom_eq_coe
-/
lemma Equation.baseChange {x y : A} (h : (W⁄A).Equation x y) : (W⁄B).Equation (f x) (f y) := by
  convert! Equation.map f.toRingHom h using 1
  rw [AlgHom.toRingHom_eq_coe]; rw [map_baseChange]

variable {f} in
/--
lemma `baseChange_equation` / 引理 `baseChange_equation`

English:
lemma baseChange_equation
  given: (hf : Function.Injective f) (x y : A)
  proof: by
  rw [← map_equation _ hf]; rw [AlgHom.toRingHom_eq_coe]; rw [map_baseChange]; rw [RingHom.coe_coe]

中文:
引理 baseChange_equation
  条件: (hf : Function.Injective f) (x y : A)
  证明: by
  rw [← map_equation _ hf]; rw [AlgHom.toRingHom_eq_coe]; rw [map_baseChange]; rw [RingHom.coe_coe]

Depends on / 依赖: AlgHom, AlgHom.toRingHom_eq_coe, RingHom, RingHom.coe_coe, coe_coe, map_baseChange, map_equation, toRingHom_eq_coe
-/
lemma baseChange_equation (hf : Function.Injective f) (x y : A) :
    (W⁄B).Equation (f x) (f y) ↔ (W⁄A).Equation x y := by
  rw [← map_equation _ hf]; rw [AlgHom.toRingHom_eq_coe]; rw [map_baseChange]; rw [RingHom.coe_coe]

/--
lemma `baseChange_polynomialX` / 引理 `baseChange_polynomialX`

English:
lemma baseChange_polynomialX
  statement: (W⁄B).polynomialX = (W⁄A).polynomialX.map (mapRingHom f)
  proof: by
  rw [← map_polynomialX]; rw [map_baseChange]

中文:
引理 baseChange_polynomialX
  结论: (W⁄B).polynomialX = (W⁄A).polynomialX.map (mapRingHom f)
  证明: by
  rw [← map_polynomialX]; rw [map_baseChange]

Depends on / 依赖: map_baseChange, map_polynomialX
-/
lemma baseChange_polynomialX : (W⁄B).polynomialX = (W⁄A).polynomialX.map (mapRingHom f) := by
  rw [← map_polynomialX]; rw [map_baseChange]

/--
lemma `baseChange_polynomialY` / 引理 `baseChange_polynomialY`

English:
lemma baseChange_polynomialY
  statement: (W⁄B).polynomialY = (W⁄A).polynomialY.map (mapRingHom f)
  proof: by
  rw [← map_polynomialY]; rw [map_baseChange]

中文:
引理 baseChange_polynomialY
  结论: (W⁄B).polynomialY = (W⁄A).polynomialY.map (mapRingHom f)
  证明: by
  rw [← map_polynomialY]; rw [map_baseChange]

Depends on / 依赖: map_baseChange, map_polynomialY
-/
lemma baseChange_polynomialY : (W⁄B).polynomialY = (W⁄A).polynomialY.map (mapRingHom f) := by
  rw [← map_polynomialY]; rw [map_baseChange]

variable {f} in
/--
lemma `baseChange_nonsingular` / 引理 `baseChange_nonsingular`

English:
lemma baseChange_nonsingular
  given: (hf : Function.Injective f) (x y : A)
  proof: by
  rw [← map_nonsingular _ hf]; rw [AlgHom.toRingHom_eq_coe]; rw [map_baseChange]; rw [RingHom.coe_coe]

中文:
引理 baseChange_nonsingular
  条件: (hf : Function.Injective f) (x y : A)
  证明: by
  rw [← map_nonsingular _ hf]; rw [AlgHom.toRingHom_eq_coe]; rw [map_baseChange]; rw [RingHom.coe_coe]

Depends on / 依赖: AlgHom, AlgHom.toRingHom_eq_coe, RingHom, RingHom.coe_coe, coe_coe, map_baseChange, map_nonsingular, toRingHom_eq_coe
-/
lemma baseChange_nonsingular (hf : Function.Injective f) (x y : A) :
    (W⁄B).Nonsingular (f x) (f y) ↔ (W⁄A).Nonsingular x y := by
  rw [← map_nonsingular _ hf]; rw [AlgHom.toRingHom_eq_coe]; rw [map_baseChange]; rw [RingHom.coe_coe]

end Affine

end WeierstrassCurve
