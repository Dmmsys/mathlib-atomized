/-
Copyright (c) 2025 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic

/-!
# Negation and addition formulae for nonsingular points in affine coordinates

Let `W` be a Weierstrass curve over a field `F` with coefficients `aᵢ`. The nonsingular affine
points on `W` can be given negation and addition operations defined by a secant-and-tangent process.
* Given a nonsingular affine point `P`, its *negation* `-P` is defined to be the unique third
  nonsingular point of intersection between `W` and the vertical line through `P`.
  Explicitly, if `P` is `(x, y)`, then `-P` is `(x, -y - a₁x - a₃)`.
* Given two nonsingular affine points `P` and `Q`, their *addition* `P + Q` is defined to be the
  negation of the unique third nonsingular point of intersection between `W` and the line `L`
  through `P` and `Q`. Explicitly, let `P` be `(x₁, y₁)` and let `Q` be `(x₂, y₂)`.
    * If `x₁ = x₂` and `y₁ = -y₂ - a₁x₂ - a₃`, then `L` is vertical.
    * If `x₁ = x₂` and `y₁ ≠ -y₂ - a₁x₂ - a₃`, then `L` is the tangent of `W` at `P = Q`, and has
      slope `ℓ := (3x₁² + 2a₂x₁ + a₄ - a₁y₁) / (2y₁ + a₁x₁ + a₃)`.
    * Otherwise `x₁ ≠ x₂`, then `L` is the secant of `W` through `P` and `Q`, and has slope
      `ℓ := (y₁ - y₂) / (x₁ - x₂)`.

  In the last two cases, the `X`-coordinate of `P + Q` is then the unique third solution of the
  equation obtained by substituting the line `Y = ℓ(X - x₁) + y₁` into the Weierstrass equation,
  and can be written down explicitly as `x := ℓ² + a₁ℓ - a₂ - x₁ - x₂` by inspecting the
  coefficients of `X²`. The `Y`-coordinate of `P + Q`, after applying the final negation that maps
  `Y` to `-Y - a₁X - a₃`, is precisely `y := -(ℓ(x - x₁) + y₁) - a₁x - a₃`.

This file defines polynomials associated to negation and addition of nonsingular affine points,
including slopes of non-vertical lines. The actual group law on nonsingular points in affine
coordinates will be defined in `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean`.

## Main definitions

* `WeierstrassCurve.Affine.negY`: the `Y`-coordinate of `-P`.
* `WeierstrassCurve.Affine.addX`: the `X`-coordinate of `P + Q`.
* `WeierstrassCurve.Affine.negAddY`: the `Y`-coordinate of `-(P + Q)`.
* `WeierstrassCurve.Affine.addY`: the `Y`-coordinate of `P + Q`.

## Main statements

* `WeierstrassCurve.Affine.equation_neg`: negation preserves the Weierstrass equation.
* `WeierstrassCurve.Affine.nonsingular_neg`: negation preserves the nonsingular condition.
* `WeierstrassCurve.Affine.equation_add`: addition preserves the Weierstrass equation.
* `WeierstrassCurve.Affine.nonsingular_add`: addition preserves the nonsingular condition.

## References

[J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, affine, negation, doubling, addition, group law
-/

@[expose] public section

open Polynomial

open scoped Polynomial.Bivariate

local macro "C_simp" : tactic =>
  `(tactic| simp only [map_ofNat, C_0, C_1, C_neg, C_add, C_sub, C_mul, C_pow])

local macro "derivative_simp" : tactic =>
  `(tactic| simp only [derivative_C, derivative_X, derivative_X_pow, derivative_neg, derivative_add,
    derivative_sub, derivative_mul, derivative_sq])

local macro "eval_simp" : tactic =>
  `(tactic| simp only [eval_C, eval_X, eval_neg, eval_add, eval_sub, eval_mul, eval_pow, evalEval])

local macro "map_simp" : tactic =>
  `(tactic| simp only [map_ofNat, map_neg, map_add, map_sub, map_mul, map_pow, map_div₀,
    Polynomial.map_ofNat, map_C, map_X, Polynomial.map_neg, Polynomial.map_add, Polynomial.map_sub,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_div, coe_mapRingHom,
    WeierstrassCurve.map])

universe r s u v w

namespace WeierstrassCurve

variable {R : Type r} {S : Type s} {A F : Type u} {B K : Type v} [CommRing R] [CommRing S]
  [CommRing A] [CommRing B] [Field F] [Field K] {W' : Affine R} {W : Affine F}

namespace Affine

/-! ## Negation formulae in affine coordinates -/

variable (W') in
/--
Definition of `negPolynomial` / `negPolynomial` 的定义

English:
definition negPolynomial
  signature: : R[X][Y]
  body: -(Y : R[X][Y]) - C (C W'.a₁ * X + C W'.a₃)

中文:
定义 negPolynomial
  签名: : R[X][Y]
  定义体: -(Y : R[X][Y]) - C (C W'.a₁ * X + C W'.a₃)

Depends on / 依赖: map_prop
-/
noncomputable def negPolynomial : R[X][Y] :=
  -(Y : R[X][Y]) - C (C W'.a₁ * X + C W'.a₃)

/--
lemma `Y_sub_polynomialY` / 引理 `Y_sub_polynomialY`

English:
lemma Y_sub_polynomialY
  statement: Y - W'.polynomialY = W'.negPolynomial
  proof: by
  rw [polynomialY]; rw [negPolynomial]
  C_simp
  ring1

中文:
引理 Y_sub_polynomialY
  结论: Y - W'.polynomialY = W'.negPolynomial
  证明: by
  rw [polynomialY]; rw [negPolynomial]
  C_simp
  ring1

Depends on / 依赖: C_simp, U.prop, negPolynomial, polynomialY
-/
lemma Y_sub_polynomialY : Y - W'.polynomialY = W'.negPolynomial := by
  rw [polynomialY]; rw [negPolynomial]
  C_simp
  ring1

/--
lemma `Y_sub_negPolynomial` / 引理 `Y_sub_negPolynomial`

English:
lemma Y_sub_negPolynomial
  statement: Y - W'.negPolynomial = W'.polynomialY
  proof: by
  rw [← Y_sub_polynomialY]; rw [sub_sub_cancel]

#adaptation_note

中文:
引理 Y_sub_negPolynomial
  结论: Y - W'.negPolynomial = W'.polynomialY
  证明: by
  rw [← Y_sub_polynomialY]; rw [sub_sub_cancel]

#adaptation_note

Depends on / 依赖: Y_sub_polynomialY, sub_sub_cancel
-/
lemma Y_sub_negPolynomial : Y - W'.negPolynomial = W'.polynomialY := by
  rw [← Y_sub_polynomialY]; rw [sub_sub_cancel]

#adaptation_note
/--
Without this `implicit_reducible` attribute, `simpNF` gives a linter error on `slope_of_Y_eq`
because of a nonconfluence: `negY` can be unfolded on the LHS, which prevents discharging the
side condition of `slope_of_Y_eq` -- except if `negY` is implicit-reducible.
So this attribute improves the confluence of `simp`.
-/
variable (W') in
/-- The `Y`-coordinate of `-(x, y)` for a nonsingular affine point `(x, y)` on a Weierstrass curve
`W`.

This depends on `W`, and has argument order: `x`, `y`. -/
@[simp, implicit_reducible]
/--
Definition of `negY` / `negY` 的定义

English:
definition negY
  signature: (x y : R)
  body: -y - W'.a₁ * x - W'.a₃

中文:
定义 negY
  签名: (x y : R)
  定义体: -y - W'.a₁ * x - W'.a₃
-/
def negY (x y : R) : R :=
  -y - W'.a₁ * x - W'.a₃

/--
lemma `negY_negY` / 引理 `negY_negY`

English:
lemma negY_negY
  given: (x y : R)
  statement: W'.negY x (W'.negY x y) = y
  proof: by
  simp only [negY]
  ring1

中文:
引理 negY_negY
  条件: (x y : R)
  结论: W'.negY x (W'.negY x y) = y
  证明: by
  simp only [negY]
  ring1
-/
lemma negY_negY (x y : R) : W'.negY x (W'.negY x y) = y := by
  simp only [negY]
  ring1

/--
lemma `evalEval_negPolynomial` / 引理 `evalEval_negPolynomial`

English:
lemma evalEval_negPolynomial
  given: (x y : R)
  statement: W'.negPolynomial.evalEval x y = W'.negY x y
  proof: by
  rw [negY]; rw [sub_sub]; rw [negPolynomial]
  eval_simp

中文:
引理 evalEval_negPolynomial
  条件: (x y : R)
  结论: W'.negPolynomial.evalEval x y = W'.negY x y
  证明: by
  rw [negY]; rw [sub_sub]; rw [negPolynomial]
  eval_simp

Depends on / 依赖: eval_simp, negPolynomial, sub_sub
-/
lemma evalEval_negPolynomial (x y : R) : W'.negPolynomial.evalEval x y = W'.negY x y := by
  rw [negY]; rw [sub_sub]; rw [negPolynomial]
  eval_simp

/--
lemma `Y_eq_of_X_eq` / 引理 `Y_eq_of_X_eq`

English:
lemma Y_eq_of_X_eq
  statement: {x₁ x₂ y₁ y₂ : F} (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂)
  proof: by
  rw [equation_iff] at h₁ h₂
  rw [← sub_eq_zero]; rw [← sub_eq_zero (a := y₁)]; rw [← mul_eq_zero]; rw [negY]
  linear_combination (norm := (rw [hx]; ring1)) h₁ - h₂

中文:
引理 Y_eq_of_X_eq
  结论: {x₁ x₂ y₁ y₂ : F} (h₁ : W.方程 x₁ y₁) (h₂ : W.方程 x₂ y₂)
  证明: by
  rw [equation_iff] at h₁ h₂
  rw [← sub_eq_zero]; rw [← sub_eq_zero (a := y₁)]; rw [← mul_eq_zero]; rw [negY]
  linear_combination (norm := (rw [hx]; ring1)) h₁ - h₂

Depends on / 依赖: equation_iff, linear_combination, mul_eq_zero, sub_eq_zero
-/
lemma Y_eq_of_X_eq {x₁ x₂ y₁ y₂ : F} (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂)
    (hx : x₁ = x₂) : y₁ = y₂ ∨ y₁ = W.negY x₂ y₂ := by
  rw [equation_iff] at h₁ h₂
  rw [← sub_eq_zero]; rw [← sub_eq_zero (a := y₁)]; rw [← mul_eq_zero]; rw [negY]
  linear_combination (norm := (rw [hx]; ring1)) h₁ - h₂

/--
lemma `Y_eq_of_Y_ne` / 引理 `Y_eq_of_Y_ne`

English:
lemma Y_eq_of_Y_ne
  statement: {x₁ x₂ y₁ y₂ : F} (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂) (hx : x₁ = x₂)
  proof: (Y_eq_of_X_eq h₁ h₂ hx).resolve_right hy

中文:
引理 Y_eq_of_Y_ne
  结论: {x₁ x₂ y₁ y₂ : F} (h₁ : W.方程 x₁ y₁) (h₂ : W.方程 x₂ y₂) (hx : x₁ = x₂)
  证明: (Y_eq_of_X_eq h₁ h₂ hx).resolve_right hy

Depends on / 依赖: Y_eq_of_X_eq, resolve_right
-/
lemma Y_eq_of_Y_ne {x₁ x₂ y₁ y₂ : F} (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂) (hx : x₁ = x₂)
    (hy : y₁ != W.negY x₂ y₂) : y₁ = y₂ :=
  (Y_eq_of_X_eq h₁ h₂ hx).resolve_right hy

/--
lemma `equation_neg` / 引理 `equation_neg`

English:
lemma equation_neg
  given: (x y : R)
  statement: W'.Equation x (W'.negY x y) ↔ W'.Equation x y
  proof: by
  rw [equation_iff]; rw [equation_iff]; rw [negY]
  congr! 1
  ring1

中文:
引理 equation_neg
  条件: (x y : R)
  结论: W'.方程 x (W'.negY x y) ↔ W'.方程 x y
  证明: by
  rw [equation_iff]; rw [equation_iff]; rw [negY]
  congr! 1
  ring1

Depends on / 依赖: equation_iff
-/
lemma equation_neg (x y : R) : W'.Equation x (W'.negY x y) ↔ W'.Equation x y := by
  rw [equation_iff]; rw [equation_iff]; rw [negY]
  congr! 1
  ring1

/--
lemma `nonsingular_neg` / 引理 `nonsingular_neg`

English:
lemma nonsingular_neg
  given: (x y : R)
  statement: W'.Nonsingular x (W'.negY x y) ↔ W'.Nonsingular x y
  proof: by
  rw [nonsingular_iff]; rw [equation_neg]; rw [← negY]; rw [negY_negY]; rw [← @ne_comm _ y]; rw [nonsingular_iff]
exact and_congr_right' (iff_congr not_and_or.symm not_and_or.symm).mpr
not_congr and_congr_left fun h => by rw [← h]

中文:
引理 nonsingular_neg
  条件: (x y : R)
  结论: W'.非奇异 x (W'.negY x y) ↔ W'.非奇异 x y
  证明: by
  rw [nonsingular_iff]; rw [equation_neg]; rw [← negY]; rw [negY_negY]; rw [← @ne_comm _ y]; rw [nonsingular_iff]
exact and_congr_right' (iff_congr not_and_or.symm not_and_or.symm).mpr
not_congr and_congr_left fun h => by rw [← h]

Depends on / 依赖: and_congr_left, and_congr_right, equation_neg, iff_congr, ne_comm, negY_negY, nonsingular_iff, not_and_or, not_and_or.symm, not_congr
-/
lemma nonsingular_neg (x y : R) : W'.Nonsingular x (W'.negY x y) ↔ W'.Nonsingular x y := by
  rw [nonsingular_iff]; rw [equation_neg]; rw [← negY]; rw [negY_negY]; rw [← @ne_comm _ y]; rw [nonsingular_iff]
exact and_congr_right' (iff_congr not_and_or.symm not_and_or.symm).mpr
not_congr and_congr_left fun h => by rw [← h]

/-! ## Slope formulae in affine coordinates -/

variable (W') in
/--
Definition of `linePolynomial` / `linePolynomial` 的定义

English:
definition linePolynomial
  signature: (x y ℓ : R)
  body: C ℓ * (X - C x) + C y

中文:
定义 linePolynomial
  签名: (x y ℓ : R)
  定义体: C ℓ * (X - C x) + C y
-/
noncomputable def linePolynomial (x y ℓ : R) : R[X] :=
  C ℓ * (X - C x) + C y

section slope

variable [DecidableEq F]

variable (W) in
/--
Definition of `slope` / `slope` 的定义

English:
definition slope
  signature: (x₁ x₂ y₁ y₂ : F)
  body: if x₁ = x₂ then if y₁ = W.negY x₂ y₂ then 0
    else (3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁) / (y₁ - W.negY x₁ y₁)
  else (y₁ - y₂) / (x₁ - x₂)

@[simp]

中文:
定义 slope
  签名: (x₁ x₂ y₁ y₂ : F)
  定义体: if x₁ = x₂ then if y₁ = W.negY x₂ y₂ then 0
    else (3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁) / (y₁ - W.negY x₁ y₁)
  else (y₁ - y₂) / (x₁ - x₂)

@[simp]

Depends on / 依赖: W.negY
-/
def slope (x₁ x₂ y₁ y₂ : F) : F :=
  if x₁ = x₂ then if y₁ = W.negY x₂ y₂ then 0
    else (3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁) / (y₁ - W.negY x₁ y₁)
  else (y₁ - y₂) / (x₁ - x₂)

@[simp]
/--
lemma `slope_of_Y_eq` / 引理 `slope_of_Y_eq`

English:
lemma slope_of_Y_eq
  given: {x₁ x₂ y₁ y₂ : F} (hx : x₁ = x₂) (hy : y₁ = W.negY x₂ y₂)
  proof: by
  rw [slope]; rw [if_pos hx]; rw [if_pos hy]

@[simp]

中文:
引理 slope_of_Y_eq
  条件: {x₁ x₂ y₁ y₂ : F} (hx : x₁ = x₂) (hy : y₁ = W.negY x₂ y₂)
  证明: by
  rw [slope]; rw [if_pos hx]; rw [if_pos hy]

@[simp]

Depends on / 依赖: if_pos
-/
lemma slope_of_Y_eq {x₁ x₂ y₁ y₂ : F} (hx : x₁ = x₂) (hy : y₁ = W.negY x₂ y₂) :
    W.slope x₁ x₂ y₁ y₂ = 0 := by
  rw [slope]; rw [if_pos hx]; rw [if_pos hy]

@[simp]
/--
lemma `slope_of_Y_ne'` / 引理 `slope_of_Y_ne'`

English:
lemma slope_of_Y_ne'
  given: {x₂ y₁ y₂ : F} (hy : ¬y₁ = -y₂ - W.a₁ * x₂ - W.a₃)
  proof: by
  simp [slope, hy]

中文:
引理 slope_of_Y_ne'
  条件: {x₂ y₁ y₂ : F} (hy : ¬y₁ = -y₂ - W.a₁ * x₂ - W.a₃)
  证明: by
  simp [slope, hy]
-/
lemma slope_of_Y_ne' {x₂ y₁ y₂ : F} (hy : ¬y₁ = -y₂ - W.a₁ * x₂ - W.a₃) :
    W.slope x₂ x₂ y₁ y₂ =
      (3 * x₂ ^ 2 + 2 * W.a₂ * x₂ + W.a₄ - W.a₁ * y₁) / (y₁ - (-y₁ - W.a₁ * x₂ - W.a₃)) := by
  simp [slope, hy]

/--
lemma `slope_of_Y_ne` / 引理 `slope_of_Y_ne`

English:
lemma slope_of_Y_ne
  given: {x₁ x₂ y₁ y₂ : F} (hx : x₁ = x₂) (hy : y₁ != W.negY x₂ y₂)
  proof: by
  simp_all

@[simp]

中文:
引理 slope_of_Y_ne
  条件: {x₁ x₂ y₁ y₂ : F} (hx : x₁ = x₂) (hy : y₁ != W.negY x₂ y₂)
  证明: by
  simp_all

@[simp]
-/
lemma slope_of_Y_ne {x₁ x₂ y₁ y₂ : F} (hx : x₁ = x₂) (hy : y₁ != W.negY x₂ y₂) :
    W.slope x₁ x₂ y₁ y₂ =
      (3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁) / (y₁ - W.negY x₁ y₁) := by
  simp_all

@[simp]
/--
lemma `slope_of_X_ne` / 引理 `slope_of_X_ne`

English:
lemma slope_of_X_ne
  given: {x₁ x₂ y₁ y₂ : F} (hx : x₁ != x₂)
  proof: by
  rw [slope]; rw [if_neg hx]

中文:
引理 slope_of_X_ne
  条件: {x₁ x₂ y₁ y₂ : F} (hx : x₁ != x₂)
  证明: by
  rw [slope]; rw [if_neg hx]

Depends on / 依赖: if_neg
-/
lemma slope_of_X_ne {x₁ x₂ y₁ y₂ : F} (hx : x₁ != x₂) :
    W.slope x₁ x₂ y₁ y₂ = (y₁ - y₂) / (x₁ - x₂) := by
  rw [slope]; rw [if_neg hx]

/--
lemma `slope_of_Y_ne_eq_evalEval` / 引理 `slope_of_Y_ne_eq_evalEval`

English:
lemma slope_of_Y_ne_eq_evalEval
  given: {x₁ x₂ y₁ y₂ : F} (hx : x₁ = x₂) (hy : y₁ != W.negY x₂ y₂)
  proof: by
  rw [slope_of_Y_ne hx hy]; rw [evalEval_polynomialX]; rw [neg_sub]
  congr 1
  rw [negY]; rw [evalEval_polynomialY]
  ring1

中文:
引理 slope_of_Y_ne_eq_evalEval
  条件: {x₁ x₂ y₁ y₂ : F} (hx : x₁ = x₂) (hy : y₁ != W.negY x₂ y₂)
  证明: by
  rw [slope_of_Y_ne hx hy]; rw [evalEval_polynomialX]; rw [neg_sub]
  congr 1
  rw [negY]; rw [evalEval_polynomialY]
  ring1

Depends on / 依赖: evalEval_polynomialX, evalEval_polynomialY, neg_sub, slope_of_Y_ne
-/
lemma slope_of_Y_ne_eq_evalEval {x₁ x₂ y₁ y₂ : F} (hx : x₁ = x₂) (hy : y₁ != W.negY x₂ y₂) :
    W.slope x₁ x₂ y₁ y₂ = -W.polynomialX.evalEval x₁ y₁ / W.polynomialY.evalEval x₁ y₁ := by
  rw [slope_of_Y_ne hx hy]; rw [evalEval_polynomialX]; rw [neg_sub]
  congr 1
  rw [negY]; rw [evalEval_polynomialY]
  ring1

end slope

/-! ## Addition formulae in affine coordinates -/

variable (W') in
/--
Definition of `addPolynomial` / `addPolynomial` 的定义

English:
definition addPolynomial
  signature: (x y ℓ : R)
  body: W'.polynomial.eval linePolynomial x y ℓ

中文:
定义 addPolynomial
  签名: (x y ℓ : R)
  定义体: W'.polynomial.eval linePolynomial x y ℓ

Depends on / 依赖: linePolynomial, polynomial, polynomial.eval
-/
noncomputable def addPolynomial (x y ℓ : R) : R[X] :=
W'.polynomial.eval linePolynomial x y ℓ

/--
lemma `C_addPolynomial` / 引理 `C_addPolynomial`

English:
lemma C_addPolynomial
  given: (x y ℓ : R)
  statement: C (W'.addPolynomial x y ℓ) =
  proof: by
  rw [addPolynomial]; rw [linePolynomial]; rw [polynomial]; rw [negPolynomial]
  eval_simp
  C_simp
  ring1

中文:
引理 C_addPolynomial
  条件: (x y ℓ : R)
  结论: C (W'.addPolynomial x y ℓ) =
  证明: by
  rw [addPolynomial]; rw [linePolynomial]; rw [polynomial]; rw [negPolynomial]
  eval_simp
  C_simp
  ring1

Depends on / 依赖: C_simp, addPolynomial, eval_simp, linePolynomial, negPolynomial, polynomial
-/
lemma C_addPolynomial (x y ℓ : R) : C (W'.addPolynomial x y ℓ) =
    (Y - C (linePolynomial x y ℓ)) * (W'.negPolynomial - C (linePolynomial x y ℓ)) +
      W'.polynomial := by
  rw [addPolynomial]; rw [linePolynomial]; rw [polynomial]; rw [negPolynomial]
  eval_simp
  C_simp
  ring1

/--
lemma `addPolynomial_eq` / 引理 `addPolynomial_eq`

English:
lemma addPolynomial_eq
  given: (x y ℓ : R)
  statement: W'.addPolynomial x y ℓ = -Cubic.toPoly
  proof: by
  rw [addPolynomial]; rw [linePolynomial]; rw [polynomial]; rw [Cubic.toPoly]
  eval_simp
  C_simp
  ring1

中文:
引理 addPolynomial_eq
  条件: (x y ℓ : R)
  结论: W'.addPolynomial x y ℓ = -三次.toPoly
  证明: by
  rw [addPolynomial]; rw [linePolynomial]; rw [polynomial]; rw [Cubic.toPoly]
  eval_simp
  C_simp
  ring1

Depends on / 依赖: C_simp, Cubic.toPoly, addPolynomial, eval_simp, linePolynomial, polynomial, toPoly
-/
lemma addPolynomial_eq (x y ℓ : R) : W'.addPolynomial x y ℓ = -Cubic.toPoly
    ⟨1, -ℓ ^ 2 - W'.a₁ * ℓ + W'.a₂,
      2 * x * ℓ ^ 2 + (W'.a₁ * x - 2 * y - W'.a₃) * ℓ + (-W'.a₁ * y + W'.a₄),
      -x ^ 2 * ℓ ^ 2 + (2 * x * y + W'.a₃ * x) * ℓ - (y ^ 2 + W'.a₃ * y - W'.a₆)⟩ := by
  rw [addPolynomial]; rw [linePolynomial]; rw [polynomial]; rw [Cubic.toPoly]
  eval_simp
  C_simp
  ring1

variable (W') in
/-- The `X`-coordinate of `(x₁, y₁) + (x₂, y₂)` for two nonsingular affine points `(x₁, y₁)` and
`(x₂, y₂)` on a Weierstrass curve `W`, where the line through them has a slope of `ℓ`.

This depends on `W`, and has argument order: `x₁`, `x₂`, `ℓ`. -/
@[simp]
/--
Definition of `addX` / `addX` 的定义

English:
definition addX
  signature: (x₁ x₂ ℓ : R)
  body: ℓ ^ 2 + W'.a₁ * ℓ - W'.a₂ - x₁ - x₂

中文:
定义 addX
  签名: (x₁ x₂ ℓ : R)
  定义体: ℓ ^ 2 + W'.a₁ * ℓ - W'.a₂ - x₁ - x₂
-/
def addX (x₁ x₂ ℓ : R) : R :=
  ℓ ^ 2 + W'.a₁ * ℓ - W'.a₂ - x₁ - x₂

variable (W') in
/-- The `Y`-coordinate of `-((x₁, y₁) + (x₂, y₂))` for two nonsingular affine points `(x₁, y₁)` and
`(x₂, y₂)` on a Weierstrass curve `W`, where the line through them has a slope of `ℓ`.

This depends on `W`, and has argument order: `x₁`, `x₂`, `y₁`, `ℓ`. -/
@[simp]
/--
Definition of `negAddY` / `negAddY` 的定义

English:
definition negAddY
  signature: (x₁ x₂ y₁ ℓ : R)
  body: ℓ * (W'.addX x₁ x₂ ℓ - x₁) + y₁

中文:
定义 negAddY
  签名: (x₁ x₂ y₁ ℓ : R)
  定义体: ℓ * (W'.addX x₁ x₂ ℓ - x₁) + y₁
-/
def negAddY (x₁ x₂ y₁ ℓ : R) : R :=
  ℓ * (W'.addX x₁ x₂ ℓ - x₁) + y₁

variable (W') in
/--
Definition of `addY` / `addY` 的定义

English:
definition addY
  signature: (x₁ x₂ y₁ ℓ : R)
  body: W'.negY (W'.addX x₁ x₂ ℓ) (W'.negAddY x₁ x₂ y₁ ℓ)

中文:
定义 addY
  签名: (x₁ x₂ y₁ ℓ : R)
  定义体: W'.negY (W'.addX x₁ x₂ ℓ) (W'.negAddY x₁ x₂ y₁ ℓ)

Depends on / 依赖: negAddY
-/
def addY (x₁ x₂ y₁ ℓ : R) : R :=
  W'.negY (W'.addX x₁ x₂ ℓ) (W'.negAddY x₁ x₂ y₁ ℓ)

section slope

variable [DecidableEq F]

/--
lemma `addPolynomial_slope` / 引理 `addPolynomial_slope`

English:
lemma addPolynomial_slope
  statement: {x₁ x₂ y₁ y₂ : F} (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂)
  proof: by
  rw [addPolynomial_eq]; rw [neg_inj]; rw [Cubic.prod_X_sub_C_eq]; rw [Cubic.toPoly_injective]
  by_cases hx : x₁ = x₂
  · have hy : y₁ != W.negY x₂ y₂ := fun h => hxy ⟨hx, h⟩
    rcases hx, Y_eq_of_Y_ne h₁ h₂ hx hy with ⟨rfl, rfl⟩
    rw [equation_iff] at h₁ h₂
    rw [slope_of_Y_ne rfl hy]
    rw [negY]; rw [← sub_ne_zero] at hy
    replace hy : y₁ - (-y₁ - x₁ * W.a₁ - W.a₃) != 0 := by convert! hy using 1; ring
    ext
    · rfl
    · simp only [addX]
      ring1
    · simp [field]
      ring1
    · linear_combination (norm := (simp [field]; ring1)) -h₁
  · rw [equation_iff] at h₁ h₂
    rw [slope_of_X_ne hx]
    simp only [addX]
    grind

中文:
引理 addPolynomial_slope
  结论: {x₁ x₂ y₁ y₂ : F} (h₁ : W.方程 x₁ y₁) (h₂ : W.方程 x₂ y₂)
  证明: by
  rw [addPolynomial_eq]; rw [neg_inj]; rw [Cubic.prod_X_sub_C_eq]; rw [Cubic.toPoly_injective]
  by_cases hx : x₁ = x₂
  · have hy : y₁ != W.negY x₂ y₂ := fun h => hxy ⟨hx, h⟩
    rcases hx, Y_eq_of_Y_ne h₁ h₂ hx hy with ⟨rfl, rfl⟩
    rw [equation_iff] at h₁ h₂
    rw [slope_of_Y_ne rfl hy]
    rw [negY]; rw [← sub_ne_zero] at hy
    replace hy : y₁ - (-y₁ - x₁ * W.a₁ - W.a₃) != 0 := by convert! hy using 1; ring
    ext
    · rfl
    · simp only [addX]
      ring1
    · simp [field]
      ring1
    · linear_combination (norm := (simp [field]; ring1)) -h₁
  · rw [equation_iff] at h₁ h₂
    rw [slope_of_X_ne hx]
    simp only [addX]
    grind

Depends on / 依赖: Cubic.prod_X_sub_C_eq, Cubic.toPoly_injective, W.negY, Y_eq_of_Y_ne, addPolynomial_eq, convert, equation_iff, linear_combination, neg_inj, prod_X_sub_C_eq, replace, slope_of_Y_ne, sub_ne_zero, toPoly_injective
-/
lemma addPolynomial_slope {x₁ x₂ y₁ y₂ : F} (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) : W.addPolynomial x₁ y₁ (W.slope x₁ x₂ y₁ y₂) =
      -((X - C x₁) * (X - C x₂) * (X - C (W.addX x₁ x₂ <| W.slope x₁ x₂ y₁ y₂))) := by
  rw [addPolynomial_eq]; rw [neg_inj]; rw [Cubic.prod_X_sub_C_eq]; rw [Cubic.toPoly_injective]
  by_cases hx : x₁ = x₂
  · have hy : y₁ != W.negY x₂ y₂ := fun h => hxy ⟨hx, h⟩
    rcases hx, Y_eq_of_Y_ne h₁ h₂ hx hy with ⟨rfl, rfl⟩
    rw [equation_iff] at h₁ h₂
    rw [slope_of_Y_ne rfl hy]
    rw [negY]; rw [← sub_ne_zero] at hy
    replace hy : y₁ - (-y₁ - x₁ * W.a₁ - W.a₃) != 0 := by convert! hy using 1; ring
    ext
    · rfl
    · simp only [addX]
      ring1
    · simp [field]
      ring1
    · linear_combination (norm := (simp [field]; ring1)) -h₁
  · rw [equation_iff] at h₁ h₂
    rw [slope_of_X_ne hx]
    simp only [addX]
    grind

/--
lemma `C_addPolynomial_slope` / 引理 `C_addPolynomial_slope`

English:
lemma C_addPolynomial_slope
  statement: {x₁ x₂ y₁ y₂ : F} (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂)
  proof: by
  rw [addPolynomial_slope h₁ h₂ hxy]
  simp

中文:
引理 C_addPolynomial_slope
  结论: {x₁ x₂ y₁ y₂ : F} (h₁ : W.方程 x₁ y₁) (h₂ : W.方程 x₂ y₂)
  证明: by
  rw [addPolynomial_slope h₁ h₂ hxy]
  simp

Depends on / 依赖: addPolynomial_slope
-/
lemma C_addPolynomial_slope {x₁ x₂ y₁ y₂ : F} (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) : C (W.addPolynomial x₁ y₁ <| W.slope x₁ x₂ y₁ y₂) =
      -(C (X - C x₁) * C (X - C x₂) * C (X - C (W.addX x₁ x₂ <| W.slope x₁ x₂ y₁ y₂))) := by
  rw [addPolynomial_slope h₁ h₂ hxy]
  simp

/--
lemma `derivative_addPolynomial_slope` / 引理 `derivative_addPolynomial_slope`

English:
lemma derivative_addPolynomial_slope
  statement: {x₁ x₂ y₁ y₂ : F} (h₁ : W.Equation x₁ y₁)
  proof: by
  rw [addPolynomial_slope h₁ h₂ hxy]
  derivative_simp
  ring1

中文:
引理 derivative_addPolynomial_slope
  结论: {x₁ x₂ y₁ y₂ : F} (h₁ : W.方程 x₁ y₁)
  证明: by
  rw [addPolynomial_slope h₁ h₂ hxy]
  derivative_simp
  ring1

Depends on / 依赖: addPolynomial_slope, derivative_simp
-/
lemma derivative_addPolynomial_slope {x₁ x₂ y₁ y₂ : F} (h₁ : W.Equation x₁ y₁)
    (h₂ : W.Equation x₂ y₂) (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) :
    derivative (W.addPolynomial x₁ y₁ <| W.slope x₁ x₂ y₁ y₂) =
      -((X - C x₁) * (X - C x₂) + (X - C x₁) * (X - C (W.addX x₁ x₂ <| W.slope x₁ x₂ y₁ y₂)) +
          (X - C x₂) * (X - C (W.addX x₁ x₂ <| W.slope x₁ x₂ y₁ y₂))) := by
  rw [addPolynomial_slope h₁ h₂ hxy]
  derivative_simp
  ring1

/--
lemma `nonsingular_negAdd_of_eval_derivative_ne_zero` / 引理 `nonsingular_negAdd_of_eval_derivative_ne_zero`

English:
lemma nonsingular_negAdd_of_eval_derivative_ne_zero
  statement: {x₁ x₂ y₁ ℓ : R}
  proof: by
  rw [Nonsingular]; rw [and_iff_right hx']; rw [negAddY]; rw [polynomialX]; rw [polynomialY]
  eval_simp
  contrapose! hx
  rw [addPolynomial]; rw [linePolynomial]; rw [polynomial]
  eval_simp
  derivative_simp
  simp only [zero_add, add_zero, sub_zero, zero_mul, mul_one]
  eval_simp
  linear_combination (norm := (norm_num1; ring1)) hx.left + ℓ * hx.right

中文:
引理 nonsingular_negAdd_of_eval_derivative_ne_zero
  结论: {x₁ x₂ y₁ ℓ : R}
  证明: by
  rw [Nonsingular]; rw [and_iff_right hx']; rw [negAddY]; rw [polynomialX]; rw [polynomialY]
  eval_simp
  contrapose! hx
  rw [addPolynomial]; rw [linePolynomial]; rw [polynomial]
  eval_simp
  derivative_simp
  simp only [zero_add, add_zero, sub_zero, zero_mul, mul_one]
  eval_simp
  linear_combination (norm := (norm_num1; ring1)) hx.left + ℓ * hx.right

Depends on / 依赖: Nonsingular, addPolynomial, add_zero, and_iff_right, contrapose, derivative_simp, eval_simp, hx.left, hx.right, linePolynomial, linear_combination, mul_one, negAddY, norm_num1, polynomial, polynomialX, polynomialY, sub_zero, zero_add, zero_mul
-/
lemma nonsingular_negAdd_of_eval_derivative_ne_zero {x₁ x₂ y₁ ℓ : R}
    (hx' : W'.Equation (W'.addX x₁ x₂ ℓ) (W'.negAddY x₁ x₂ y₁ ℓ))
    (hx : (W'.addPolynomial x₁ y₁ ℓ).derivative.eval (W'.addX x₁ x₂ ℓ) != 0) :
    W'.Nonsingular (W'.addX x₁ x₂ ℓ) (W'.negAddY x₁ x₂ y₁ ℓ) := by
  rw [Nonsingular]; rw [and_iff_right hx']; rw [negAddY]; rw [polynomialX]; rw [polynomialY]
  eval_simp
  contrapose! hx
  rw [addPolynomial]; rw [linePolynomial]; rw [polynomial]
  eval_simp
  derivative_simp
  simp only [zero_add, add_zero, sub_zero, zero_mul, mul_one]
  eval_simp
  linear_combination (norm := (norm_num1; ring1)) hx.left + ℓ * hx.right

/--
lemma `equation_add_iff` / 引理 `equation_add_iff`

English:
lemma equation_add_iff
  given: (x₁ x₂ y₁ ℓ : R)
  statement: W'.Equation (W'.addX x₁ x₂ ℓ) (W'.negAddY x₁ x₂ y₁ ℓ) ↔
  proof: by
  rw [Equation]; rw [negAddY]; rw [addPolynomial]; rw [linePolynomial]; rw [polynomial]
  eval_simp

中文:
引理 equation_add_iff
  条件: (x₁ x₂ y₁ ℓ : R)
  结论: W'.方程 (W'.addX x₁ x₂ ℓ) (W'.negAddY x₁ x₂ y₁ ℓ) ↔
  证明: by
  rw [Equation]; rw [negAddY]; rw [addPolynomial]; rw [linePolynomial]; rw [polynomial]
  eval_simp

Depends on / 依赖: Equation, addPolynomial, eval_simp, linePolynomial, negAddY, polynomial
-/
lemma equation_add_iff (x₁ x₂ y₁ ℓ : R) : W'.Equation (W'.addX x₁ x₂ ℓ) (W'.negAddY x₁ x₂ y₁ ℓ) ↔
    (W'.addPolynomial x₁ y₁ ℓ).eval (W'.addX x₁ x₂ ℓ) = 0 := by
  rw [Equation]; rw [negAddY]; rw [addPolynomial]; rw [linePolynomial]; rw [polynomial]
  eval_simp

/--
lemma `equation_negAdd` / 引理 `equation_negAdd`

English:
lemma equation_negAdd
  statement: {x₁ x₂ y₁ y₂ : F} (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂)
  proof: by
  rw [equation_add_iff]; rw [addPolynomial_slope h₁ h₂ hxy]
  eval_simp
  rw [neg_eq_zero]; rw [sub_self]; rw [mul_zero]

中文:
引理 equation_negAdd
  结论: {x₁ x₂ y₁ y₂ : F} (h₁ : W.方程 x₁ y₁) (h₂ : W.方程 x₂ y₂)
  证明: by
  rw [equation_add_iff]; rw [addPolynomial_slope h₁ h₂ hxy]
  eval_simp
  rw [neg_eq_zero]; rw [sub_self]; rw [mul_zero]

Depends on / 依赖: addPolynomial_slope, equation_add_iff, eval_simp, mul_zero, neg_eq_zero, sub_self
-/
lemma equation_negAdd {x₁ x₂ y₁ y₂ : F} (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) : W.Equation
      (W.addX x₁ x₂ <| W.slope x₁ x₂ y₁ y₂) (W.negAddY x₁ x₂ y₁ <| W.slope x₁ x₂ y₁ y₂) := by
  rw [equation_add_iff]; rw [addPolynomial_slope h₁ h₂ hxy]
  eval_simp
  rw [neg_eq_zero]; rw [sub_self]; rw [mul_zero]

/--
lemma `equation_add` / 引理 `equation_add`

English:
lemma equation_add
  statement: {x₁ x₂ y₁ y₂ : F} (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂)
  proof: (equation_neg ..).mpr equation_negAdd h₁ h₂ hxy

中文:
引理 equation_add
  结论: {x₁ x₂ y₁ y₂ : F} (h₁ : W.方程 x₁ y₁) (h₂ : W.方程 x₂ y₂)
  证明: (equation_neg ..).mpr equation_negAdd h₁ h₂ hxy

Depends on / 依赖: equation_neg, equation_negAdd
-/
lemma equation_add {x₁ x₂ y₁ y₂ : F} (h₁ : W.Equation x₁ y₁) (h₂ : W.Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) :
    W.Equation (W.addX x₁ x₂ <| W.slope x₁ x₂ y₁ y₂) (W.addY x₁ x₂ y₁ <| W.slope x₁ x₂ y₁ y₂) :=
(equation_neg ..).mpr equation_negAdd h₁ h₂ hxy

/--
lemma `nonsingular_negAdd` / 引理 `nonsingular_negAdd`

English:
lemma nonsingular_negAdd
  statement: {x₁ x₂ y₁ y₂ : F} (h₁ : W.Nonsingular x₁ y₁) (h₂ : W.Nonsingular x₂ y₂)
  proof: by
  by_cases hx₁ : W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂) = x₁
  · rwa [negAddY, hx₁, sub_self, mul_zero, zero_add]
  · by_cases hx₂ : W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂) = x₂
    · by_cases hx : x₁ = x₂
      · subst hx
        contradiction
      · rwa [negAddY, ← neg_sub, mul_neg, hx₂, slope_of_X_ne hx,
div_mul_cancel₀ _ sub_ne_zero_of_ne hx, neg_sub, sub_add_cancel]
· apply nonsingular_negAdd_of_eval_derivative_ne_zero equation_negAdd h₁.left h₂.left hxy
      rw [derivative_addPolynomial_slope h₁.left h₂.left hxy]
      eval_simp
      simp only [neg_ne_zero, sub_self, mul_zero, add_zero]
      exact mul_ne_zero (sub_ne_zero_of_ne hx₁) (sub_ne_zero_of_ne hx₂)

中文:
引理 nonsingular_negAdd
  结论: {x₁ x₂ y₁ y₂ : F} (h₁ : W.非奇异 x₁ y₁) (h₂ : W.非奇异 x₂ y₂)
  证明: by
  by_cases hx₁ : W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂) = x₁
  · rwa [negAddY, hx₁, sub_self, mul_zero, zero_add]
  · by_cases hx₂ : W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂) = x₂
    · by_cases hx : x₁ = x₂
      · subst hx
        contradiction
      · rwa [negAddY, ← neg_sub, mul_neg, hx₂, slope_of_X_ne hx,
div_mul_cancel₀ _ sub_ne_zero_of_ne hx, neg_sub, sub_add_cancel]
· apply nonsingular_negAdd_of_eval_derivative_ne_zero equation_negAdd h₁.left h₂.left hxy
      rw [derivative_addPolynomial_slope h₁.left h₂.left hxy]
      eval_simp
      simp only [neg_ne_zero, sub_self, mul_zero, add_zero]
      exact mul_ne_zero (sub_ne_zero_of_ne hx₁) (sub_ne_zero_of_ne hx₂)

Depends on / 依赖: W.addX, W.slope, derivative_addPolynomial_slope, equation_negAdd, eval_simp, mul_neg, mul_zero, negAddY, neg_sub, nonsingular_negAdd_of_eval_derivative_ne_zero, slope_of_X_ne, sub_add_cancel, sub_ne_zero_of_ne, sub_self, zero_add
-/
lemma nonsingular_negAdd {x₁ x₂ y₁ y₂ : F} (h₁ : W.Nonsingular x₁ y₁) (h₂ : W.Nonsingular x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) : W.Nonsingular
      (W.addX x₁ x₂ <| W.slope x₁ x₂ y₁ y₂) (W.negAddY x₁ x₂ y₁ <| W.slope x₁ x₂ y₁ y₂) := by
  by_cases hx₁ : W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂) = x₁
  · rwa [negAddY, hx₁, sub_self, mul_zero, zero_add]
  · by_cases hx₂ : W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂) = x₂
    · by_cases hx : x₁ = x₂
      · subst hx
        contradiction
      · rwa [negAddY, ← neg_sub, mul_neg, hx₂, slope_of_X_ne hx,
div_mul_cancel₀ _ sub_ne_zero_of_ne hx, neg_sub, sub_add_cancel]
· apply nonsingular_negAdd_of_eval_derivative_ne_zero equation_negAdd h₁.left h₂.left hxy
      rw [derivative_addPolynomial_slope h₁.left h₂.left hxy]
      eval_simp
      simp only [neg_ne_zero, sub_self, mul_zero, add_zero]
      exact mul_ne_zero (sub_ne_zero_of_ne hx₁) (sub_ne_zero_of_ne hx₂)

/--
lemma `nonsingular_add` / 引理 `nonsingular_add`

English:
lemma nonsingular_add
  statement: {x₁ x₂ y₁ y₂ : F} (h₁ : W.Nonsingular x₁ y₁) (h₂ : W.Nonsingular x₂ y₂)
  proof: (nonsingular_neg ..).mpr nonsingular_negAdd h₁ h₂ hxy

中文:
引理 nonsingular_add
  结论: {x₁ x₂ y₁ y₂ : F} (h₁ : W.非奇异 x₁ y₁) (h₂ : W.非奇异 x₂ y₂)
  证明: (nonsingular_neg ..).mpr nonsingular_negAdd h₁ h₂ hxy

Depends on / 依赖: nonsingular_neg, nonsingular_negAdd
-/
lemma nonsingular_add {x₁ x₂ y₁ y₂ : F} (h₁ : W.Nonsingular x₁ y₁) (h₂ : W.Nonsingular x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)) :
    W.Nonsingular (W.addX x₁ x₂ <| W.slope x₁ x₂ y₁ y₂) (W.addY x₁ x₂ y₁ <| W.slope x₁ x₂ y₁ y₂) :=
(nonsingular_neg ..).mpr nonsingular_negAdd h₁ h₂ hxy

/--
lemma `addX_eq_addX_negY_sub` / 引理 `addX_eq_addX_negY_sub`

English:
lemma addX_eq_addX_negY_sub
  given: {x₁ x₂ : F} (y₁ y₂ : F) (hx : x₁ != x₂)
  proof: by
  simp_rw [slope_of_X_ne hx, addX, negY, ← neg_sub x₁, neg_sq]
  simp [field]
  ring1

中文:
引理 addX_eq_addX_negY_sub
  条件: {x₁ x₂ : F} (y₁ y₂ : F) (hx : x₁ != x₂)
  证明: by
  simp_rw [slope_of_X_ne hx, addX, negY, ← neg_sub x₁, neg_sq]
  simp [field]
  ring1

Depends on / 依赖: neg_sq, neg_sub, simp_rw, slope_of_X_ne
-/
lemma addX_eq_addX_negY_sub {x₁ x₂ : F} (y₁ y₂ : F) (hx : x₁ != x₂) :
    W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂) = W.addX x₁ x₂ (W.slope x₁ x₂ y₁ <| W.negY x₂ y₂) -
      (y₁ - W.negY x₁ y₁) * (y₂ - W.negY x₂ y₂) / (x₂ - x₁) ^ 2 := by
  simp_rw [slope_of_X_ne hx, addX, negY, ← neg_sub x₁, neg_sq]
  simp [field]
  ring1

/--
lemma `cyclic_sum_Y_mul_X_sub_X` / 引理 `cyclic_sum_Y_mul_X_sub_X`

English:
lemma cyclic_sum_Y_mul_X_sub_X
  given: {x₁ x₂ : F} (y₁ y₂ : F) (hx : x₁ != x₂)
  proof: W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂)
    y₁ * (x₂ - x₃) + y₂ * (x₃ - x₁) + W.negAddY x₁ x₂ y₁ (W.slope x₁ x₂ y₁ y₂) * (x₁ - x₂) = 0 := by
  simp_rw [slope_of_X_ne hx, negAddY, addX]
  simp [field]
  ring1

中文:
引理 cyclic_sum_Y_mul_X_sub_X
  条件: {x₁ x₂ : F} (y₁ y₂ : F) (hx : x₁ != x₂)
  证明: W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂)
    y₁ * (x₂ - x₃) + y₂ * (x₃ - x₁) + W.negAddY x₁ x₂ y₁ (W.slope x₁ x₂ y₁ y₂) * (x₁ - x₂) = 0 := by
  simp_rw [slope_of_X_ne hx, negAddY, addX]
  simp [field]
  ring1

Depends on / 依赖: Scheme, Scheme.presieve, W.addX, W.slope
-/
lemma cyclic_sum_Y_mul_X_sub_X {x₁ x₂ : F} (y₁ y₂ : F) (hx : x₁ != x₂) :
    let x₃ := W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂)
    y₁ * (x₂ - x₃) + y₂ * (x₃ - x₁) + W.negAddY x₁ x₂ y₁ (W.slope x₁ x₂ y₁ y₂) * (x₁ - x₂) = 0 := by
  simp_rw [slope_of_X_ne hx, negAddY, addX]
  simp [field]
  ring1

/--
lemma `addY_sub_negY_addY` / 引理 `addY_sub_negY_addY`

English:
lemma addY_sub_negY_addY
  given: {x₁ x₂ : F} (y₁ y₂ : F) (hx : x₁ != x₂)
  proof: W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂)
    let y₃ := W.addY x₁ x₂ y₁ (W.slope x₁ x₂ y₁ y₂)
    y₃ - W.negY x₃ y₃ =
      ((y₂ - W.negY x₂ y₂) * (x₁ - x₃) - (y₁ - W.negY x₁ y₁) * (x₂ - x₃)) / (x₂ - x₁) := by
  simp_rw [addY, negY, eq_div_iff (sub_ne_zero.mpr hx.symm)]
  linear_combination (norm := ring1) 2 * cyclic_sum_Y_mul_X_sub_X y₁ y₂ hx

中文:
引理 addY_sub_negY_addY
  条件: {x₁ x₂ : F} (y₁ y₂ : F) (hx : x₁ != x₂)
  证明: W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂)
    let y₃ := W.addY x₁ x₂ y₁ (W.slope x₁ x₂ y₁ y₂)
    y₃ - W.negY x₃ y₃ =
      ((y₂ - W.negY x₂ y₂) * (x₁ - x₃) - (y₁ - W.negY x₁ y₁) * (x₂ - x₃)) / (x₂ - x₁) := by
  simp_rw [addY, negY, eq_div_iff (sub_ne_zero.mpr hx.symm)]
  linear_combination (norm := ring1) 2 * cyclic_sum_Y_mul_X_sub_X y₁ y₂ hx

Depends on / 依赖: W.addX, W.slope
-/
lemma addY_sub_negY_addY {x₁ x₂ : F} (y₁ y₂ : F) (hx : x₁ != x₂) :
    let x₃ := W.addX x₁ x₂ (W.slope x₁ x₂ y₁ y₂)
    let y₃ := W.addY x₁ x₂ y₁ (W.slope x₁ x₂ y₁ y₂)
    y₃ - W.negY x₃ y₃ =
      ((y₂ - W.negY x₂ y₂) * (x₁ - x₃) - (y₁ - W.negY x₁ y₁) * (x₂ - x₃)) / (x₂ - x₁) := by
  simp_rw [addY, negY, eq_div_iff (sub_ne_zero.mpr hx.symm)]
  linear_combination (norm := ring1) 2 * cyclic_sum_Y_mul_X_sub_X y₁ y₂ hx

end slope

/-! ## Maps and base changes -/

variable (f : R ->+* S) (x y x₁ y₁ x₂ y₂ ℓ : R)

/--
lemma `map_negPolynomial` / 引理 `map_negPolynomial`

English:
lemma map_negPolynomial
  statement: (W'.map f).negPolynomial = W'.negPolynomial.map (mapRingHom f)
  proof: by
  simp only [negPolynomial]
  map_simp

中文:
引理 map_negPolynomial
  结论: (W'.map f).negPolynomial = W'.negPolynomial.map (mapRingHom f)
  证明: by
  simp only [negPolynomial]
  map_simp

Depends on / 依赖: map_simp, negPolynomial
-/
lemma map_negPolynomial : (W'.map f).negPolynomial = W'.negPolynomial.map (mapRingHom f) := by
  simp only [negPolynomial]
  map_simp

/--
lemma `map_negY` / 引理 `map_negY`

English:
lemma map_negY
  statement: (W'.map f).negY (f x) (f y) = f (W'.negY x y)
  proof: by
  simp only [negY]
  map_simp

中文:
引理 map_negY
  结论: (W'.map f).negY (f x) (f y) = f (W'.negY x y)
  证明: by
  simp only [negY]
  map_simp

Depends on / 依赖: infer_instance, map_simp
-/
lemma map_negY : (W'.map f).negY (f x) (f y) = f (W'.negY x y) := by
  simp only [negY]
  map_simp

/--
lemma `map_linePolynomial` / 引理 `map_linePolynomial`

English:
lemma map_linePolynomial
  statement: linePolynomial (f x) (f y) (f ℓ) = (linePolynomial x y ℓ).map f
  proof: by
  simp only [linePolynomial]
  map_simp

中文:
引理 map_linePolynomial
  结论: linePolynomial (f x) (f y) (f ℓ) = (linePolynomial x y ℓ).map f
  证明: by
  simp only [linePolynomial]
  map_simp

Depends on / 依赖: linePolynomial, map_simp
-/
lemma map_linePolynomial : linePolynomial (f x) (f y) (f ℓ) = (linePolynomial x y ℓ).map f := by
  simp only [linePolynomial]
  map_simp

/--
lemma `map_addPolynomial` / 引理 `map_addPolynomial`

English:
lemma map_addPolynomial
  proof: by
  rw [addPolynomial]; rw [map_polynomial]; rw [eval_map]; rw [linePolynomial]; rw [addPolynomial]; rw [← coe_mapRingHom]; rw [← eval₂_hom]; rw [linePolynomial]
  simp

中文:
引理 map_addPolynomial
  证明: by
  rw [addPolynomial]; rw [map_polynomial]; rw [eval_map]; rw [linePolynomial]; rw [addPolynomial]; rw [← coe_mapRingHom]; rw [← eval₂_hom]; rw [linePolynomial]
  simp

Depends on / 依赖: addPolynomial, coe_mapRingHom, eval_map, linePolynomial, map_polynomial
-/
lemma map_addPolynomial :
    (W'.map f).addPolynomial (f x) (f y) (f ℓ) = (W'.addPolynomial x y ℓ).map f := by
  rw [addPolynomial]; rw [map_polynomial]; rw [eval_map]; rw [linePolynomial]; rw [addPolynomial]; rw [← coe_mapRingHom]; rw [← eval₂_hom]; rw [linePolynomial]
  simp

/--
lemma `map_addX` / 引理 `map_addX`

English:
lemma map_addX
  statement: (W'.map f).addX (f x₁) (f x₂) (f ℓ) = f (W'.addX x₁ x₂ ℓ)
  proof: by
  simp only [addX]
  map_simp

中文:
引理 map_addX
  结论: (W'.map f).addX (f x₁) (f x₂) (f ℓ) = f (W'.addX x₁ x₂ ℓ)
  证明: by
  simp only [addX]
  map_simp

Depends on / 依赖: PreZeroHypercover, PreZeroHypercover.sumInr, map_simp, of_hom, sumInr
-/
lemma map_addX : (W'.map f).addX (f x₁) (f x₂) (f ℓ) = f (W'.addX x₁ x₂ ℓ) := by
  simp only [addX]
  map_simp

/--
lemma `map_negAddY` / 引理 `map_negAddY`

English:
lemma map_negAddY
  statement: (W'.map f).negAddY (f x₁) (f x₂) (f y₁) (f ℓ) = f (W'.negAddY x₁ x₂ y₁ ℓ)
  proof: by
  simp only [negAddY, map_addX]
  map_simp

中文:
引理 map_negAddY
  结论: (W'.map f).negAddY (f x₁) (f x₂) (f y₁) (f ℓ) = f (W'.negAddY x₁ x₂ y₁ ℓ)
  证明: by
  simp only [negAddY, map_addX]
  map_simp

Depends on / 依赖: map_addX, map_simp, negAddY
-/
lemma map_negAddY : (W'.map f).negAddY (f x₁) (f x₂) (f y₁) (f ℓ) = f (W'.negAddY x₁ x₂ y₁ ℓ) := by
  simp only [negAddY, map_addX]
  map_simp

/--
lemma `map_addY` / 引理 `map_addY`

English:
lemma map_addY
  statement: (W'.map f).addY (f x₁) (f x₂) (f y₁) (f ℓ) = f (W'.addY x₁ x₂ y₁ ℓ)
  proof: by
  simp only [addY, map_negAddY, map_addX, map_negY]

中文:
引理 map_addY
  结论: (W'.map f).addY (f x₁) (f x₂) (f y₁) (f ℓ) = f (W'.addY x₁ x₂ y₁ ℓ)
  证明: by
  simp only [addY, map_negAddY, map_addX, map_negY]

Depends on / 依赖: map_addX, map_negAddY, map_negY
-/
lemma map_addY : (W'.map f).addY (f x₁) (f x₂) (f y₁) (f ℓ) = f (W'.addY x₁ x₂ y₁ ℓ) := by
  simp only [addY, map_negAddY, map_addX, map_negY]

/--
lemma `map_slope` / 引理 `map_slope`

English:
lemma map_slope
  given: [DecidableEq F] [DecidableEq K] (f : F ->+* K) (x₁ x₂ y₁ y₂ : F)
  proof: by
  by_cases hx : x₁ = x₂
  · by_cases hy : y₁ = W.negY x₂ y₂
    · rw [slope_of_Y_eq (congr_arg f hx) <| by rw [hy, map_negY], slope_of_Y_eq hx hy, map_zero]
    · rw [slope_of_Y_ne (congr_arg f hx) <| map_negY f x₂ y₂ ▸ fun h => hy <| f.injective h,
        map_negY, slope_of_Y_ne hx hy]
      map_simp
  · rw [slope_of_X_ne fun h => hx <| f.injective h, slope_of_X_ne hx]
    map_simp

中文:
引理 map_slope
  条件: [DecidableEq F] [DecidableEq K] (f : F ->+* K) (x₁ x₂ y₁ y₂ : F)
  证明: by
  by_cases hx : x₁ = x₂
  · by_cases hy : y₁ = W.negY x₂ y₂
    · rw [slope_of_Y_eq (congr_arg f hx) <| by rw [hy, map_negY], slope_of_Y_eq hx hy, map_zero]
    · rw [slope_of_Y_ne (congr_arg f hx) <| map_negY f x₂ y₂ ▸ fun h => hy <| f.injective h,
        map_negY, slope_of_Y_ne hx hy]
      map_simp
  · rw [slope_of_X_ne fun h => hx <| f.injective h, slope_of_X_ne hx]
    map_simp

Depends on / 依赖: W.negY, congr_arg, f.injective, injective, map_negY, map_simp, map_zero, slope_of_X_ne, slope_of_Y_eq, slope_of_Y_ne
-/
lemma map_slope [DecidableEq F] [DecidableEq K] (f : F ->+* K) (x₁ x₂ y₁ y₂ : F) :
    (W.map f).slope (f x₁) (f x₂) (f y₁) (f y₂) = f (W.slope x₁ x₂ y₁ y₂) := by
  by_cases hx : x₁ = x₂
  · by_cases hy : y₁ = W.negY x₂ y₂
    · rw [slope_of_Y_eq (congr_arg f hx) <| by rw [hy, map_negY], slope_of_Y_eq hx hy, map_zero]
    · rw [slope_of_Y_ne (congr_arg f hx) <| map_negY f x₂ y₂ ▸ fun h => hy <| f.injective h,
        map_negY, slope_of_Y_ne hx hy]
      map_simp
  · rw [slope_of_X_ne fun h => hx <| f.injective h, slope_of_X_ne hx]
    map_simp

variable [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A] [Algebra R B] [Algebra S B]
  [IsScalarTower R S B] (f : A ->ₐ[S] B) (x y x₁ y₁ x₂ y₂ ℓ : A)

/--
lemma `baseChange_negPolynomial` / 引理 `baseChange_negPolynomial`

English:
lemma baseChange_negPolynomial
  proof: by
  rw [← map_negPolynomial]; rw [map_baseChange]

中文:
引理 baseChange_negPolynomial
  证明: by
  rw [← map_negPolynomial]; rw [map_baseChange]

Depends on / 依赖: map_baseChange, map_negPolynomial
-/
lemma baseChange_negPolynomial :
    (W'⁄B).negPolynomial = (W'⁄A).negPolynomial.map (mapRingHom f) := by
  rw [← map_negPolynomial]; rw [map_baseChange]

/--
lemma `baseChange_negY` / 引理 `baseChange_negY`

English:
lemma baseChange_negY
  statement: (W'⁄B).negY (f x) (f y) = f ((W'⁄A).negY x y)
  proof: by
  rw [← RingHom.coe_coe]; rw [← map_negY]; rw [map_baseChange]

中文:
引理 baseChange_negY
  结论: (W'⁄B).negY (f x) (f y) = f ((W'⁄A).negY x y)
  证明: by
  rw [← RingHom.coe_coe]; rw [← map_negY]; rw [map_baseChange]

Depends on / 依赖: RingHom, RingHom.coe_coe, coe_coe, map_baseChange, map_negY
-/
lemma baseChange_negY : (W'⁄B).negY (f x) (f y) = f ((W'⁄A).negY x y) := by
  rw [← RingHom.coe_coe]; rw [← map_negY]; rw [map_baseChange]

/--
lemma `baseChange_addPolynomial` / 引理 `baseChange_addPolynomial`

English:
lemma baseChange_addPolynomial
  proof: by
  rw [← RingHom.coe_coe]; rw [← map_addPolynomial]; rw [map_baseChange]

中文:
引理 baseChange_addPolynomial
  证明: by
  rw [← RingHom.coe_coe]; rw [← map_addPolynomial]; rw [map_baseChange]

Depends on / 依赖: RingHom, RingHom.coe_coe, coe_coe, map_addPolynomial, map_baseChange
-/
lemma baseChange_addPolynomial :
    (W'⁄B).addPolynomial (f x) (f y) (f ℓ) = ((W'⁄A).addPolynomial x y ℓ).map f := by
  rw [← RingHom.coe_coe]; rw [← map_addPolynomial]; rw [map_baseChange]

/--
lemma `baseChange_addX` / 引理 `baseChange_addX`

English:
lemma baseChange_addX
  statement: (W'⁄B).addX (f x₁) (f x₂) (f ℓ) = f ((W'⁄A).addX x₁ x₂ ℓ)
  proof: by
  rw [← RingHom.coe_coe]; rw [← map_addX]; rw [map_baseChange]

中文:
引理 baseChange_addX
  结论: (W'⁄B).addX (f x₁) (f x₂) (f ℓ) = f ((W'⁄A).addX x₁ x₂ ℓ)
  证明: by
  rw [← RingHom.coe_coe]; rw [← map_addX]; rw [map_baseChange]

Depends on / 依赖: RingHom, RingHom.coe_coe, coe_coe, map_addX, map_baseChange
-/
lemma baseChange_addX : (W'⁄B).addX (f x₁) (f x₂) (f ℓ) = f ((W'⁄A).addX x₁ x₂ ℓ) := by
  rw [← RingHom.coe_coe]; rw [← map_addX]; rw [map_baseChange]

/--
lemma `baseChange_negAddY` / 引理 `baseChange_negAddY`

English:
lemma baseChange_negAddY
  proof: by
  rw [← RingHom.coe_coe]; rw [← map_negAddY]; rw [map_baseChange]

中文:
引理 baseChange_negAddY
  证明: by
  rw [← RingHom.coe_coe]; rw [← map_negAddY]; rw [map_baseChange]

Depends on / 依赖: RingHom, RingHom.coe_coe, coe_coe, map_baseChange, map_negAddY
-/
lemma baseChange_negAddY :
    (W'⁄B).negAddY (f x₁) (f x₂) (f y₁) (f ℓ) = f ((W'⁄A).negAddY x₁ x₂ y₁ ℓ) := by
  rw [← RingHom.coe_coe]; rw [← map_negAddY]; rw [map_baseChange]

/--
lemma `baseChange_addY` / 引理 `baseChange_addY`

English:
lemma baseChange_addY
  statement: (W'⁄B).addY (f x₁) (f x₂) (f y₁) (f ℓ) = f ((W'⁄A).addY x₁ x₂ y₁ ℓ)
  proof: by
  rw [← RingHom.coe_coe]; rw [← map_addY]; rw [map_baseChange]

中文:
引理 baseChange_addY
  结论: (W'⁄B).addY (f x₁) (f x₂) (f y₁) (f ℓ) = f ((W'⁄A).addY x₁ x₂ y₁ ℓ)
  证明: by
  rw [← RingHom.coe_coe]; rw [← map_addY]; rw [map_baseChange]

Depends on / 依赖: RingHom, RingHom.coe_coe, coe_coe, map_addY, map_baseChange
-/
lemma baseChange_addY : (W'⁄B).addY (f x₁) (f x₂) (f y₁) (f ℓ) = f ((W'⁄A).addY x₁ x₂ y₁ ℓ) := by
  rw [← RingHom.coe_coe]; rw [← map_addY]; rw [map_baseChange]

/--
lemma `baseChange_slope` / 引理 `baseChange_slope`

English:
lemma baseChange_slope
  statement: [DecidableEq F] [DecidableEq K] [Algebra R F] [Algebra S F]
  proof: by
  rw [← RingHom.coe_coe]; rw [← map_slope]; rw [map_baseChange]

中文:
引理 baseChange_slope
  结论: [DecidableEq F] [DecidableEq K] [代数 R F] [代数 S F]
  证明: by
  rw [← RingHom.coe_coe]; rw [← map_slope]; rw [map_baseChange]

Depends on / 依赖: RingHom, RingHom.coe_coe, coe_coe, map_baseChange, map_slope
-/
lemma baseChange_slope [DecidableEq F] [DecidableEq K] [Algebra R F] [Algebra S F]
    [IsScalarTower R S F] [Algebra R K] [Algebra S K] [IsScalarTower R S K] (f : F ->ₐ[S] K)
    (x₁ x₂ y₁ y₂ : F) :
    (W'⁄K).slope (f x₁) (f x₂) (f y₁) (f y₂) = f ((W'⁄F).slope x₁ x₂ y₁ y₂) := by
  rw [← RingHom.coe_coe]; rw [← map_slope]; rw [map_baseChange]

end Affine

end WeierstrassCurve
