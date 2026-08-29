/-
Copyright (c) 2025 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic

/-!
# Negation and addition formulae for nonsingular points in projective coordinates

Let `W` be a Weierstrass curve over a field `F`. The nonsingular projective points on `W` can be
given negation and addition operations defined by an analogue of the secant-and-tangent process in
`Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Formula.lean`, but the polynomials involved are
homogeneous, so any instances of division become multiplication in the `Z`-coordinate. Most
computational proofs are immediate from their analogous proofs for affine coordinates.

This file defines polynomials associated to negation, doubling, and addition of projective point
representatives. The group operations and the group law on actual nonsingular projective points will
be defined in `Mathlib/AlgebraicGeometry/EllipticCurve/Projective/Point.lean`.

## Main definitions

* `WeierstrassCurve.Projective.negY`: the `Y`-coordinate of `-P`.
* `WeierstrassCurve.Projective.dblZ`: the `Z`-coordinate of `2 • P`.
* `WeierstrassCurve.Projective.dblX`: the `X`-coordinate of `2 • P`.
* `WeierstrassCurve.Projective.negDblY`: the `Y`-coordinate of `-(2 • P)`.
* `WeierstrassCurve.Projective.dblY`: the `Y`-coordinate of `2 • P`.
* `WeierstrassCurve.Projective.addZ`: the `Z`-coordinate of `P + Q`.
* `WeierstrassCurve.Projective.addX`: the `X`-coordinate of `P + Q`.
* `WeierstrassCurve.Projective.negAddY`: the `Y`-coordinate of `-(P + Q)`.
* `WeierstrassCurve.Projective.addY`: the `Y`-coordinate of `P + Q`.

## Implementation notes

The definitions of `WeierstrassCurve.Projective.dblX`, `WeierstrassCurve.Projective.negDblY`,
`WeierstrassCurve.Projective.addZ`, `WeierstrassCurve.Projective.addX`, and
`WeierstrassCurve.Projective.negAddY` are given explicitly by large polynomials that are homogeneous
of degree `4`. Clearing the denominators of their corresponding affine rational functions in
`Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Formula.lean` would give polynomials that are
homogeneous of degrees `5`, `6`, `6`, `8`, and `8` respectively, so their actual definitions are off
by powers of certain polynomial factors that are homogeneous of degree `1` or `2`. These factors
divide their corresponding affine polynomials only modulo the homogeneous Weierstrass equation, so
their large quotient polynomials are calculated explicitly in a computer algebra system. All of this
is done to ensure that the definitions of both `WeierstrassCurve.Projective.dblXYZ` and
`WeierstrassCurve.Projective.addXYZ` are homogeneous of degree `4`.

Whenever possible, all changes to documentation and naming of definitions and theorems should be
mirrored in `Mathlib/AlgebraicGeometry/EllipticCurve/Jacobian/Formula.lean`.

## References

[J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, projective, negation, doubling, addition, group law
-/

@[expose] public section

local notation3 "x" => (0 : Fin 3)

local notation3 "y" => (1 : Fin 3)

local notation3 "z" => (2 : Fin 3)

open MvPolynomial

local macro "map_simp" : tactic =>
  `(tactic| simp only [map_ofNat, map_C, map_X, map_neg, map_add, map_sub, map_mul, map_pow,
    map_div₀, WeierstrassCurve.map, Function.comp_apply])

universe r s u v

namespace WeierstrassCurve

variable {R : Type r} {S : Type s} {A F : Type u} {B K : Type v} [CommRing R] [CommRing S]
  [CommRing A] [CommRing B] [Field F] [Field K] {W' : Projective R} {W : Projective F}

namespace Projective

/-! ## Negation formulae in projective coordinates -/

variable (W') in
/--
Definition of `negY` / `negY` 的定义

English:
definition negY
  signature: (P : Fin 3 -> R)
  body: -P y - W'.a₁ * P x - W'.a₃ * P z

中文:
定义 negY
  签名: (P : 有限集 3 -> R)
  定义体: -P y - W'.a₁ * P x - W'.a₃ * P z
-/
def negY (P : Fin 3 -> R) : R :=
  -P y - W'.a₁ * P x - W'.a₃ * P z

/--
lemma `negY_eq` / 引理 `negY_eq`

English:
lemma negY_eq
  given: (X Y Z : R)
  statement: W'.negY ![X, Y, Z] = -Y - W'.a₁ * X - W'.a₃ * Z
  proof: rfl

中文:
引理 negY_eq
  条件: (X Y Z : R)
  结论: W'.negY ![X, Y, Z] = -Y - W'.a₁ * X - W'.a₃ * Z
  证明: rfl
-/
lemma negY_eq (X Y Z : R) : W'.negY ![X, Y, Z] = -Y - W'.a₁ * X - W'.a₃ * Z :=
  rfl

/--
lemma `negY_smul` / 引理 `negY_smul`

English:
lemma negY_smul
  given: (P : Fin 3 -> R) (u : R)
  statement: W'.negY (u • P) = u * W'.negY P
  proof: by
  simp only [negY, smul_fin3_ext]
  ring1

中文:
引理 negY_smul
  条件: (P : 有限集 3 -> R) (u : R)
  结论: W'.negY (u • P) = u * W'.negY P
  证明: by
  simp only [negY, smul_fin3_ext]
  ring1

Depends on / 依赖: smul_fin3_ext
-/
lemma negY_smul (P : Fin 3 -> R) (u : R) : W'.negY (u • P) = u * W'.negY P := by
  simp only [negY, smul_fin3_ext]
  ring1

/--
lemma `negY_of_Z_eq_zero` / 引理 `negY_of_Z_eq_zero`

English:
lemma negY_of_Z_eq_zero
  given: [NoZeroDivisors R] {P : Fin 3 -> R} (hP : W'.Equation P) (hPz : P z = 0)
  proof: by
  rw [negY]; rw [hPz]; rw [X_eq_zero_of_Z_eq_zero hP hPz]; rw [mul_zero]; rw [sub_zero]; rw [mul_zero]; rw [sub_zero]

中文:
引理 negY_of_Z_eq_zero
  条件: [无零因子 R] {P : 有限集 3 -> R} (hP : W'.方程 P) (hPz : P z = 0)
  证明: by
  rw [negY]; rw [hPz]; rw [X_eq_zero_of_Z_eq_zero hP hPz]; rw [mul_zero]; rw [sub_zero]; rw [mul_zero]; rw [sub_zero]

Depends on / 依赖: X_eq_zero_of_Z_eq_zero, mul_zero, sub_zero
-/
lemma negY_of_Z_eq_zero [NoZeroDivisors R] {P : Fin 3 -> R} (hP : W'.Equation P) (hPz : P z = 0) :
    W'.negY P = -P y := by
  rw [negY]; rw [hPz]; rw [X_eq_zero_of_Z_eq_zero hP hPz]; rw [mul_zero]; rw [sub_zero]; rw [mul_zero]; rw [sub_zero]

/--
lemma `negY_of_Z_ne_zero` / 引理 `negY_of_Z_ne_zero`

English:
lemma negY_of_Z_ne_zero
  given: {P : Fin 3 -> F} (hPz : P z != 0)
  proof: by
  linear_combination (norm := (rw [negY, Affine.negY]; ring1)) -W.a₃ * div_self hPz

中文:
引理 negY_of_Z_ne_zero
  条件: {P : 有限集 3 -> F} (hPz : P z != 0)
  证明: by
  linear_combination (norm := (rw [negY, Affine.negY]; ring1)) -W.a₃ * div_self hPz

Depends on / 依赖: Affine, Affine.negY, div_self, linear_combination
-/
lemma negY_of_Z_ne_zero {P : Fin 3 -> F} (hPz : P z != 0) :
    W.negY P / P z = W.toAffine.negY (P x / P z) (P y / P z) := by
  linear_combination (norm := (rw [negY, Affine.negY]; ring1)) -W.a₃ * div_self hPz

/--
lemma `Y_sub_Y_mul_Y_sub_negY` / 引理 `Y_sub_Y_mul_Y_sub_negY`

English:
lemma Y_sub_Y_mul_Y_sub_negY
  statement: {P Q : Fin 3 -> R} (hP : W'.Equation P) (hQ : W'.Equation Q)
  proof: by
  linear_combination (norm := (rw [negY]; ring1)) Q z ^ 3 * (equation_iff P).mp hP
    - P z ^ 3 * (equation_iff Q).mp hQ + (P x ^ 2 * Q z ^ 2 + P x * Q x * P z * Q z
      + Q x ^ 2 * P z ^ 2 - W'.a₁ * P y * P z * Q z ^ 2 + W'.a₂ * P x * Q z ^ 2 * P z
      + W'.a₂ * Q x * P z ^ 2 * Q z + W'.a₄ 

中文:
引理 Y_sub_Y_mul_Y_sub_negY
  结论: {P Q : 有限集 3 -> R} (hP : W'.方程 P) (hQ : W'.方程 Q)
  证明: by
  linear_combination (norm := (rw [negY]; ring1)) Q z ^ 3 * (equation_iff P).mp hP
    - P z ^ 3 * (equation_iff Q).mp hQ + (P x ^ 2 * Q z ^ 2 + P x * Q x * P z * Q z
      + Q x ^ 2 * P z ^ 2 - W'.a₁ * P y * P z * Q z ^ 2 + W'.a₂ * P x * Q z ^ 2 * P z
      + W'.a₂ * Q x * P z ^ 2 * Q z + W'.a₄ 

Depends on / 依赖: equation_iff, linear_combination
-/
lemma Y_sub_Y_mul_Y_sub_negY {P Q : Fin 3 -> R} (hP : W'.Equation P) (hQ : W'.Equation Q)
    (hx : P x * Q z = Q x * P z) :
    P z * Q z * (P y * Q z - Q y * P z) * (P y * Q z - W'.negY Q * P z) = 0 := by
  linear_combination (norm := (rw [negY]; ring1)) Q z ^ 3 * (equation_iff P).mp hP
    - P z ^ 3 * (equation_iff Q).mp hQ + (P x ^ 2 * Q z ^ 2 + P x * Q x * P z * Q z
      + Q x ^ 2 * P z ^ 2 - W'.a₁ * P y * P z * Q z ^ 2 + W'.a₂ * P x * Q z ^ 2 * P z
      + W'.a₂ * Q x * P z ^ 2 * Q z + W'.a₄ * P z ^ 2 * Q z ^ 2) * hx

/--
lemma `Y_eq_of_Y_ne` / 引理 `Y_eq_of_Y_ne`

English:
lemma Y_eq_of_Y_ne
  statement: [NoZeroDivisors R] {P Q : Fin 3 -> R} (hP : W'.Equation P) (hQ : W'.Equation Q)
  proof: sub_eq_zero.mp (mul_eq_zero.mp <| Y_sub_Y_mul_Y_sub_negY hP hQ hx).resolve_left
mul_ne_zero (mul_ne_zero hPz hQz) sub_ne_zero.mpr hy

中文:
引理 Y_eq_of_Y_ne
  结论: [无零因子 R] {P Q : 有限集 3 -> R} (hP : W'.方程 P) (hQ : W'.方程 Q)
  证明: sub_eq_zero.mp (mul_eq_zero.mp <| Y_sub_Y_mul_Y_sub_negY hP hQ hx).resolve_left
mul_ne_zero (mul_ne_zero hPz hQz) sub_ne_zero.mpr hy

Depends on / 依赖: Y_sub_Y_mul_Y_sub_negY, mul_eq_zero, mul_eq_zero.mp, mul_ne_zero, resolve_left, sub_eq_zero, sub_eq_zero.mp, sub_ne_zero, sub_ne_zero.mpr
-/
lemma Y_eq_of_Y_ne [NoZeroDivisors R] {P Q : Fin 3 -> R} (hP : W'.Equation P) (hQ : W'.Equation Q)
    (hPz : P z != 0) (hQz : Q z != 0) (hx : P x * Q z = Q x * P z) (hy : P y * Q z != Q y * P z) :
    P y * Q z = W'.negY Q * P z :=
sub_eq_zero.mp (mul_eq_zero.mp <| Y_sub_Y_mul_Y_sub_negY hP hQ hx).resolve_left
mul_ne_zero (mul_ne_zero hPz hQz) sub_ne_zero.mpr hy

/--
lemma `Y_eq_of_Y_ne'` / 引理 `Y_eq_of_Y_ne'`

English:
lemma Y_eq_of_Y_ne'
  statement: [NoZeroDivisors R] {P Q : Fin 3 -> R} (hP : W'.Equation P) (hQ : W'.Equation Q)
  proof: sub_eq_zero.mp (mul_eq_zero.mp <| (mul_eq_zero.mp <| Y_sub_Y_mul_Y_sub_negY hP hQ hx
    ).resolve_right <| sub_ne_zero.mpr hy).resolve_left <| mul_ne_zero hPz hQz

中文:
引理 Y_eq_of_Y_ne'
  结论: [无零因子 R] {P Q : 有限集 3 -> R} (hP : W'.方程 P) (hQ : W'.方程 Q)
  证明: sub_eq_zero.mp (mul_eq_zero.mp <| (mul_eq_zero.mp <| Y_sub_Y_mul_Y_sub_negY hP hQ hx
    ).resolve_right <| sub_ne_zero.mpr hy).resolve_left <| mul_ne_zero hPz hQz

Depends on / 依赖: IsLocalization, Y_sub_Y_mul_Y_sub_negY, functor, mul_eq_zero, mul_eq_zero.mp, mul_ne_zero, resolve_left, resolve_right, sub_eq_zero, sub_eq_zero.mp, sub_ne_zero, sub_ne_zero.mpr, toHoCatLocalizerMorphism
-/
lemma Y_eq_of_Y_ne' [NoZeroDivisors R] {P Q : Fin 3 -> R} (hP : W'.Equation P) (hQ : W'.Equation Q)
    (hPz : P z != 0) (hQz : Q z != 0) (hx : P x * Q z = Q x * P z)
    (hy : P y * Q z != W'.negY Q * P z) : P y * Q z = Q y * P z :=
sub_eq_zero.mp (mul_eq_zero.mp <| (mul_eq_zero.mp <| Y_sub_Y_mul_Y_sub_negY hP hQ hx
    ).resolve_right <| sub_ne_zero.mpr hy).resolve_left <| mul_ne_zero hPz hQz

/--
lemma `Y_eq_iff'` / 引理 `Y_eq_iff'`

English:
lemma Y_eq_iff'
  given: {P Q : Fin 3 -> F} (hPz : P z != 0) (hQz : Q z != 0)
  proof: negY_of_Z_ne_zero hQz ▸ (div_eq_div_iff hPz hQz).symm

中文:
引理 Y_eq_iff'
  条件: {P Q : 有限集 3 -> F} (hPz : P z != 0) (hQz : Q z != 0)
  证明: negY_of_Z_ne_zero hQz ▸ (div_eq_div_iff hPz hQz).symm

Depends on / 依赖: MorphismProperty, MorphismProperty.factorizationData, div_eq_div_iff, factorizationData, fibrations, infer_instance, isFibrant_iff_of_isTerminal, negY_of_Z_ne_zero, terminal, terminal.from, terminalIsTerminal, trivialCofibrations
-/
lemma Y_eq_iff' {P Q : Fin 3 -> F} (hPz : P z != 0) (hQz : Q z != 0) :
    P y * Q z = W.negY Q * P z ↔ P y / P z = W.toAffine.negY (Q x / Q z) (Q y / Q z) :=
  negY_of_Z_ne_zero hQz ▸ (div_eq_div_iff hPz hQz).symm

/--
lemma `Y_sub_Y_add_Y_sub_negY` / 引理 `Y_sub_Y_add_Y_sub_negY`

English:
lemma Y_sub_Y_add_Y_sub_negY
  given: {P Q : Fin 3 -> R} (hx : P x * Q z = Q x * P z)
  proof: by
  linear_combination (norm := (rw [negY, negY]; ring1)) -W'.a₁ * hx

中文:
引理 Y_sub_Y_add_Y_sub_negY
  条件: {P Q : 有限集 3 -> R} (hx : P x * Q z = Q x * P z)
  证明: by
  linear_combination (norm := (rw [negY, negY]; ring1)) -W'.a₁ * hx

Depends on / 依赖: exists_resolution, linear_combination
-/
lemma Y_sub_Y_add_Y_sub_negY {P Q : Fin 3 -> R} (hx : P x * Q z = Q x * P z) :
    (P y * Q z - Q y * P z) + (P y * Q z - W'.negY Q * P z) = (P y - W'.negY P) * Q z := by
  linear_combination (norm := (rw [negY, negY]; ring1)) -W'.a₁ * hx

/--
lemma `Y_ne_negY_of_Y_ne` / 引理 `Y_ne_negY_of_Y_ne`

English:
lemma Y_ne_negY_of_Y_ne
  statement: [NoZeroDivisors R] {P Q : Fin 3 -> R} (hP : W'.Equation P)
  proof: by
have hy' : P y * Q z - W'.negY Q * P z = 0 := sub_eq_zero.mpr Y_eq_of_Y_ne hP hQ hPz hQz hx hy
  contrapose hy
  linear_combination (norm := ring1) Y_sub_Y_add_Y_sub_negY hx + Q z * hy - hy'

中文:
引理 Y_ne_negY_of_Y_ne
  结论: [无零因子 R] {P Q : 有限集 3 -> R} (hP : W'.方程 P)
  证明: by
have hy' : P y * Q z - W'.negY Q * P z = 0 := sub_eq_zero.mpr Y_eq_of_Y_ne hP hQ hPz hQz hx hy
  contrapose hy
  linear_combination (norm := ring1) Y_sub_Y_add_Y_sub_negY hx + Q z * hy - hy'

Depends on / 依赖: HoCat.exists_resolution, Y_eq_of_Y_ne, Y_sub_Y_add_Y_sub_negY, choose_spec, choose_spec.choose, contrapose, exists_resolution, linear_combination, sub_eq_zero, sub_eq_zero.mpr
-/
lemma Y_ne_negY_of_Y_ne [NoZeroDivisors R] {P Q : Fin 3 -> R} (hP : W'.Equation P)
    (hQ : W'.Equation Q) (hPz : P z != 0) (hQz : Q z != 0) (hx : P x * Q z = Q x * P z)
    (hy : P y * Q z != Q y * P z) : P y != W'.negY P := by
have hy' : P y * Q z - W'.negY Q * P z = 0 := sub_eq_zero.mpr Y_eq_of_Y_ne hP hQ hPz hQz hx hy
  contrapose hy
  linear_combination (norm := ring1) Y_sub_Y_add_Y_sub_negY hx + Q z * hy - hy'

/--
lemma `Y_ne_negY_of_Y_ne'` / 引理 `Y_ne_negY_of_Y_ne'`

English:
lemma Y_ne_negY_of_Y_ne'
  statement: [NoZeroDivisors R] {P Q : Fin 3 -> R} (hP : W'.Equation P)
  proof: by
have hy' : P y * Q z - Q y * P z = 0 := sub_eq_zero.mpr Y_eq_of_Y_ne' hP hQ hPz hQz hx hy
  contrapose hy
  linear_combination (norm := ring1) Y_sub_Y_add_Y_sub_negY hx + Q z * hy - hy'

中文:
引理 Y_ne_negY_of_Y_ne'
  结论: [无零因子 R] {P Q : 有限集 3 -> R} (hP : W'.方程 P)
  证明: by
have hy' : P y * Q z - Q y * P z = 0 := sub_eq_zero.mpr Y_eq_of_Y_ne' hP hQ hPz hQz hx hy
  contrapose hy
  linear_combination (norm := ring1) Y_sub_Y_add_Y_sub_negY hx + Q z * hy - hy'

Depends on / 依赖: Y_eq_of_Y_ne, Y_sub_Y_add_Y_sub_negY, contrapose, linear_combination, sub_eq_zero, sub_eq_zero.mpr
-/
lemma Y_ne_negY_of_Y_ne' [NoZeroDivisors R] {P Q : Fin 3 -> R} (hP : W'.Equation P)
    (hQ : W'.Equation Q) (hPz : P z != 0) (hQz : Q z != 0) (hx : P x * Q z = Q x * P z)
    (hy : P y * Q z != W'.negY Q * P z) : P y != W'.negY P := by
have hy' : P y * Q z - Q y * P z = 0 := sub_eq_zero.mpr Y_eq_of_Y_ne' hP hQ hPz hQz hx hy
  contrapose hy
  linear_combination (norm := ring1) Y_sub_Y_add_Y_sub_negY hx + Q z * hy - hy'

/--
lemma `Y_eq_negY_of_Y_eq` / 引理 `Y_eq_negY_of_Y_eq`

English:
lemma Y_eq_negY_of_Y_eq
  statement: [NoZeroDivisors R] {P Q : Fin 3 -> R} (hQz : Q z != 0)
  proof: mul_left_injective₀ hQz by
    linear_combination (norm := ring1) -Y_sub_Y_add_Y_sub_negY hx + hy + hy'

中文:
引理 Y_eq_negY_of_Y_eq
  结论: [无零因子 R] {P Q : 有限集 3 -> R} (hQz : Q z != 0)
  证明: mul_left_injective₀ hQz by
    linear_combination (norm := ring1) -Y_sub_Y_add_Y_sub_negY hx + hy + hy'

Depends on / 依赖: HoCat.exists_resolution, Y_sub_Y_add_Y_sub_negY, choose_spec, choose_spec.choose_spec.choose_spec, exists_resolution, linear_combination
-/
lemma Y_eq_negY_of_Y_eq [NoZeroDivisors R] {P Q : Fin 3 -> R} (hQz : Q z != 0)
    (hx : P x * Q z = Q x * P z) (hy : P y * Q z = Q y * P z) (hy' : P y * Q z = W'.negY Q * P z) :
    P y = W'.negY P :=
mul_left_injective₀ hQz by
    linear_combination (norm := ring1) -Y_sub_Y_add_Y_sub_negY hx + hy + hy'

/--
lemma `nonsingular_iff_of_Y_eq_negY` / 引理 `nonsingular_iff_of_Y_eq_negY`

English:
lemma nonsingular_iff_of_Y_eq_negY
  given: {P : Fin 3 -> F} (hPz : P z != 0) (hy : P y = W.negY P)
  proof: by
  have hy' : eval P W.polynomialY = (P y - W.negY P) * P z := by rw [negY, eval_polynomialY]; ring1
  rw [nonsingular_iff_of_Z_ne_zero hPz]; rw [hy']; rw [hy]; rw [sub_self]; rw [zero_mul]; rw [ne_self_iff_false]; rw [or_false]

中文:
引理 nonsingular_iff_of_Y_eq_negY
  条件: {P : 有限集 3 -> F} (hPz : P z != 0) (hy : P y = W.negY P)
  证明: by
  have hy' : eval P W.polynomialY = (P y - W.negY P) * P z := by rw [negY, eval_polynomialY]; ring1
  rw [nonsingular_iff_of_Z_ne_zero hPz]; rw [hy']; rw [hy]; rw [sub_self]; rw [zero_mul]; rw [ne_self_iff_false]; rw [or_false]

Depends on / 依赖: HoCat.exists_resolution, W.negY, W.polynomialY, choose_spec, choose_spec.choose_spec.choose_spec, eval_polynomialY, exists_resolution, ne_self_iff_false, nonsingular_iff_of_Z_ne_zero, or_false, polynomialY, sub_self, zero_mul
-/
lemma nonsingular_iff_of_Y_eq_negY {P : Fin 3 -> F} (hPz : P z != 0) (hy : P y = W.negY P) :
    W.Nonsingular P ↔ W.Equation P ∧ eval P W.polynomialX != 0 := by
  have hy' : eval P W.polynomialY = (P y - W.negY P) * P z := by rw [negY, eval_polynomialY]; ring1
  rw [nonsingular_iff_of_Z_ne_zero hPz]; rw [hy']; rw [hy]; rw [sub_self]; rw [zero_mul]; rw [ne_self_iff_false]; rw [or_false]

/-! ## Doubling formulae in projective coordinates -/

variable (W) in
/--
Definition of `dblU` / `dblU` 的定义

English:
definition dblU
  signature: (P : Fin 3 -> F)
  body: eval P W.polynomialX ^ 3 / P z ^ 2

中文:
定义 dblU
  签名: (P : 有限集 3 -> F)
  定义体: eval P W.polynomialX ^ 3 / P z ^ 2

Depends on / 依赖: HoCat.iResolutionObj, W.polynomialX, iResolutionObj, isCofibrant_of_cofibration, polynomialX
-/
noncomputable def dblU (P : Fin 3 -> F) : F :=
  eval P W.polynomialX ^ 3 / P z ^ 2

/--
lemma `dblU_eq` / 引理 `dblU_eq`

English:
lemma dblU_eq
  given: (P : Fin 3 -> F)
  statement: W.dblU P =
  proof: by
  rw [dblU]; rw [eval_polynomialX]

中文:
引理 dblU_eq
  条件: (P : 有限集 3 -> F)
  结论: W.dblU P =
  证明: by
  rw [dblU]; rw [eval_polynomialX]

Depends on / 依赖: CommSq, eval_polynomialX, fac_left, iResolutionObj, sq.fac_left, sq.lift, terminal, terminal.from
-/
lemma dblU_eq (P : Fin 3 -> F) : W.dblU P =
    (W.a₁ * P y * P z - (3 * P x ^ 2 + 2 * W.a₂ * P x * P z + W.a₄ * P z ^ 2)) ^ 3 / P z ^ 2 := by
  rw [dblU]; rw [eval_polynomialX]

/--
lemma `dblU_smul` / 引理 `dblU_smul`

English:
lemma dblU_smul
  given: (P : Fin 3 -> F) (u : F)
  proof: by
  simp [field, dblU_eq]

中文:
引理 dblU_smul
  条件: (P : 有限集 3 -> F) (u : F)
  证明: by
  simp [field, dblU_eq]

Depends on / 依赖: dblU_eq, exists_resolution_map
-/
lemma dblU_smul (P : Fin 3 -> F) (u : F) :
    W.dblU (u • P) = u ^ 4 * W.dblU P := by
  simp [field, dblU_eq]

/--
lemma `dblU_of_Z_eq_zero` / 引理 `dblU_of_Z_eq_zero`

English:
lemma dblU_of_Z_eq_zero
  given: {P : Fin 3 -> F} (hPz : P z = 0)
  statement: W.dblU P = 0
  proof: by
  rw [dblU_eq]; rw [hPz]; rw [zero_pow two_ne_zero]; rw [div_zero]

中文:
引理 dblU_of_Z_eq_zero
  条件: {P : 有限集 3 -> F} (hPz : P z = 0)
  结论: W.dblU P = 0
  证明: by
  rw [dblU_eq]; rw [hPz]; rw [zero_pow two_ne_zero]; rw [div_zero]

Depends on / 依赖: choose_spec, dblU_eq, div_zero, exists_resolution_map, two_ne_zero, zero_pow
-/
lemma dblU_of_Z_eq_zero {P : Fin 3 -> F} (hPz : P z = 0) : W.dblU P = 0 := by
  rw [dblU_eq]; rw [hPz]; rw [zero_pow two_ne_zero]; rw [div_zero]

/--
lemma `dblU_ne_zero_of_Y_eq` / 引理 `dblU_ne_zero_of_Y_eq`

English:
lemma dblU_ne_zero_of_Y_eq
  statement: {P Q : Fin 3 -> F} (hP : W.Nonsingular P) (hPz : P z != 0) (hQz : Q z != 0)
  proof: div_ne_zero (pow_ne_zero 3
    ((nonsingular_iff_of_Y_eq_negY hPz <| Y_eq_negY_of_Y_eq hQz hx hy hy').mp hP).right) <|
    pow_ne_zero 2 hPz

中文:
引理 dblU_ne_zero_of_Y_eq
  结论: {P Q : 有限集 3 -> F} (hP : W.非奇异 P) (hPz : P z != 0) (hQz : Q z != 0)
  证明: div_ne_zero (pow_ne_zero 3
    ((nonsingular_iff_of_Y_eq_negY hPz <| Y_eq_negY_of_Y_eq hQz hx hy hy').mp hP).right) <|
    pow_ne_zero 2 hPz

Depends on / 依赖: HoCat.resolutionMap_fac, Y_eq_negY_of_Y_eq, div_ne_zero, iResolutionObj, nonsingular_iff_of_Y_eq_negY, pow_ne_zero, resolutionMap_fac, weakEquivalence_postcomp_iff, weakEquivalence_precomp_iff
-/
lemma dblU_ne_zero_of_Y_eq {P Q : Fin 3 -> F} (hP : W.Nonsingular P) (hPz : P z != 0) (hQz : Q z != 0)
    (hx : P x * Q z = Q x * P z) (hy : P y * Q z = Q y * P z) (hy' : P y * Q z = W.negY Q * P z) :
    W.dblU P != 0 :=
  div_ne_zero (pow_ne_zero 3
    ((nonsingular_iff_of_Y_eq_negY hPz <| Y_eq_negY_of_Y_eq hQz hx hy hy').mp hP).right) <|
    pow_ne_zero 2 hPz

/--
lemma `isUnit_dblU_of_Y_eq` / 引理 `isUnit_dblU_of_Y_eq`

English:
lemma isUnit_dblU_of_Y_eq
  statement: {P Q : Fin 3 -> F} (hP : W.Nonsingular P) (hPz : P z != 0) (hQz : Q z != 0)
  proof: (dblU_ne_zero_of_Y_eq hP hPz hQz hx hy hy').isUnit

中文:
引理 isUnit_dblU_of_Y_eq
  结论: {P Q : 有限集 3 -> F} (hP : W.非奇异 P) (hPz : P z != 0) (hQz : Q z != 0)
  证明: (dblU_ne_zero_of_Y_eq hP hPz hQz hx hy hy').isUnit

Depends on / 依赖: RightHomotopyClass, RightHomotopyClass.mk_eq_mk_iff, RightHomotopyClass.precomp_bijective_of_cofibration_of_weakEquivalence, RightHomotopyRel, RightHomotopyRel.leftHomotopyRel, dblU_ne_zero_of_Y_eq, homRel_iff_leftHomotopyRel, iResolutionObj, isUnit, leftHomotopyRel, mk_eq_mk_iff, precomp_bijective_of_cofibration_of_weakEquivalence, toHoCat_map_eq
-/
lemma isUnit_dblU_of_Y_eq {P Q : Fin 3 -> F} (hP : W.Nonsingular P) (hPz : P z != 0) (hQz : Q z != 0)
    (hx : P x * Q z = Q x * P z) (hy : P y * Q z = Q y * P z) (hy' : P y * Q z = W.negY Q * P z) :
    IsUnit (W.dblU P) :=
  (dblU_ne_zero_of_Y_eq hP hPz hQz hx hy hy').isUnit

variable (W') in
/--
Definition of `dblZ` / `dblZ` 的定义

English:
definition dblZ
  signature: (P : Fin 3 -> R)
  body: P z * (P y - W'.negY P) ^ 3

中文:
定义 dblZ
  签名: (P : 有限集 3 -> R)
  定义体: P z * (P y - W'.negY P) ^ 3

Depends on / 依赖: resolutionObj, toHoCat, toHoCat.obj
-/
def dblZ (P : Fin 3 -> R) : R :=
  P z * (P y - W'.negY P) ^ 3

/--
lemma `dblZ_smul` / 引理 `dblZ_smul`

English:
lemma dblZ_smul
  given: (P : Fin 3 -> R) (u : R)
  statement: W'.dblZ (u • P) = u ^ 4 * W'.dblZ P
  proof: by
  simp only [dblZ, negY_smul, smul_fin3_ext]
  ring1

中文:
引理 dblZ_smul
  条件: (P : 有限集 3 -> R) (u : R)
  结论: W'.dblZ (u • P) = u ^ 4 * W'.dblZ P
  证明: by
  simp only [dblZ, negY_smul, smul_fin3_ext]
  ring1

Depends on / 依赖: HoCat.resolution, negY_smul, resolution, smul_fin3_ext
-/
lemma dblZ_smul (P : Fin 3 -> R) (u : R) : W'.dblZ (u • P) = u ^ 4 * W'.dblZ P := by
  simp only [dblZ, negY_smul, smul_fin3_ext]
  ring1

/--
lemma `dblZ_of_Z_eq_zero` / 引理 `dblZ_of_Z_eq_zero`

English:
lemma dblZ_of_Z_eq_zero
  given: {P : Fin 3 -> R} (hPz : P z = 0)
  statement: W'.dblZ P = 0
  proof: by
  rw [dblZ]; rw [hPz]; rw [zero_mul]

中文:
引理 dblZ_of_Z_eq_zero
  条件: {P : 有限集 3 -> R} (hPz : P z = 0)
  结论: W'.dblZ P = 0
  证明: by
  rw [dblZ]; rw [hPz]; rw [zero_mul]

Depends on / 依赖: zero_mul
-/
lemma dblZ_of_Z_eq_zero {P : Fin 3 -> R} (hPz : P z = 0) : W'.dblZ P = 0 := by
  rw [dblZ]; rw [hPz]; rw [zero_mul]

/--
lemma `dblZ_of_Y_eq` / 引理 `dblZ_of_Y_eq`

English:
lemma dblZ_of_Y_eq
  statement: [NoZeroDivisors R] {P Q : Fin 3 -> R} (hQz : Q z != 0) (hx : P x * Q z = Q x * P z)
  proof: by
  rw [dblZ]; rw [Y_eq_negY_of_Y_eq hQz hx hy hy']; rw [sub_self]; rw [zero_pow three_ne_zero]; rw [mul_zero]

中文:
引理 dblZ_of_Y_eq
  结论: [无零因子 R] {P Q : 有限集 3 -> R} (hQz : Q z != 0) (hx : P x * Q z = Q x * P z)
  证明: by
  rw [dblZ]; rw [Y_eq_negY_of_Y_eq hQz hx hy hy']; rw [sub_self]; rw [zero_pow three_ne_zero]; rw [mul_zero]

Depends on / 依赖: Y_eq_negY_of_Y_eq, infer_instance, mul_zero, sub_self, three_ne_zero, weakEquivalence_iff_of_objectProperty, weakEquivalence_toHoCat_map_iff, zero_pow
-/
lemma dblZ_of_Y_eq [NoZeroDivisors R] {P Q : Fin 3 -> R} (hQz : Q z != 0) (hx : P x * Q z = Q x * P z)
    (hy : P y * Q z = Q y * P z) (hy' : P y * Q z = W'.negY Q * P z) : W'.dblZ P = 0 := by
  rw [dblZ]; rw [Y_eq_negY_of_Y_eq hQz hx hy hy']; rw [sub_self]; rw [zero_pow three_ne_zero]; rw [mul_zero]

/--
lemma `dblZ_ne_zero_of_Y_ne` / 引理 `dblZ_ne_zero_of_Y_ne`

English:
lemma dblZ_ne_zero_of_Y_ne
  statement: [NoZeroDivisors R] {P Q : Fin 3 -> R} (hP : W'.Equation P)
  proof: mul_ne_zero hPz pow_ne_zero 3 sub_ne_zero.mpr Y_ne_negY_of_Y_ne hP hQ hPz hQz hx hy

中文:
引理 dblZ_ne_zero_of_Y_ne
  结论: [无零因子 R] {P Q : 有限集 3 -> R} (hP : W'.方程 P)
  证明: mul_ne_zero hPz pow_ne_zero 3 sub_ne_zero.mpr Y_ne_negY_of_Y_ne hP hQ hPz hQz hx hy

Depends on / 依赖: Localization, Localization.inverts, NatTrans, NatTrans.isIso_iff_isIso_app, Y_ne_negY_of_Y_ne, infer_instance, inverts, isIso_iff_isIso_app, mul_ne_zero, pow_ne_zero, sub_ne_zero, sub_ne_zero.mpr, weakEquivalence_iff, weakEquivalences
-/
lemma dblZ_ne_zero_of_Y_ne [NoZeroDivisors R] {P Q : Fin 3 -> R} (hP : W'.Equation P)
    (hQ : W'.Equation Q) (hPz : P z != 0) (hQz : Q z != 0) (hx : P x * Q z = Q x * P z)
    (hy : P y * Q z != Q y * P z) : W'.dblZ P != 0 :=
mul_ne_zero hPz pow_ne_zero 3 sub_ne_zero.mpr Y_ne_negY_of_Y_ne hP hQ hPz hQz hx hy

/--
lemma `isUnit_dblZ_of_Y_ne` / 引理 `isUnit_dblZ_of_Y_ne`

English:
lemma isUnit_dblZ_of_Y_ne
  statement: {P Q : Fin 3 -> F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z != 0)
  proof: (dblZ_ne_zero_of_Y_ne hP hQ hPz hQz hx hy).isUnit

中文:
引理 isUnit_dblZ_of_Y_ne
  结论: {P Q : 有限集 3 -> F} (hP : W.方程 P) (hQ : W.方程 Q) (hPz : P z != 0)
  证明: (dblZ_ne_zero_of_Y_ne hP hQ hPz hQz hx hy).isUnit

Depends on / 依赖: CategoryTheory, CategoryTheory.Quotient.lift, Localization, Localization.inverts, Quotient, dblZ_ne_zero_of_Y_ne, factorsThroughLocalization, inverts, isUnit, map_eq_of_isInvertedBy, weakEquivalences
-/
lemma isUnit_dblZ_of_Y_ne {P Q : Fin 3 -> F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z != 0)
    (hQz : Q z != 0) (hx : P x * Q z = Q x * P z) (hy : P y * Q z != Q y * P z) : IsUnit (W.dblZ P) :=
  (dblZ_ne_zero_of_Y_ne hP hQ hPz hQz hx hy).isUnit

/--
lemma `dblZ_ne_zero_of_Y_ne'` / 引理 `dblZ_ne_zero_of_Y_ne'`

English:
lemma dblZ_ne_zero_of_Y_ne'
  statement: [NoZeroDivisors R] {P Q : Fin 3 -> R} (hP : W'.Equation P)
  proof: mul_ne_zero hPz pow_ne_zero 3 sub_ne_zero.mpr Y_ne_negY_of_Y_ne' hP hQ hPz hQz hx hy

中文:
引理 dblZ_ne_zero_of_Y_ne'
  结论: [无零因子 R] {P Q : 有限集 3 -> R} (hP : W'.方程 P)
  证明: mul_ne_zero hPz pow_ne_zero 3 sub_ne_zero.mpr Y_ne_negY_of_Y_ne' hP hQ hPz hQz hx hy

Depends on / 依赖: Iso.refl, Y_ne_negY_of_Y_ne, mul_ne_zero, pow_ne_zero, sub_ne_zero, sub_ne_zero.mpr
-/
lemma dblZ_ne_zero_of_Y_ne' [NoZeroDivisors R] {P Q : Fin 3 -> R} (hP : W'.Equation P)
    (hQ : W'.Equation Q) (hPz : P z != 0) (hQz : Q z != 0) (hx : P x * Q z = Q x * P z)
    (hy : P y * Q z != W'.negY Q * P z) : W'.dblZ P != 0 :=
mul_ne_zero hPz pow_ne_zero 3 sub_ne_zero.mpr Y_ne_negY_of_Y_ne' hP hQ hPz hQz hx hy

/--
lemma `isUnit_dblZ_of_Y_ne'` / 引理 `isUnit_dblZ_of_Y_ne'`

English:
lemma isUnit_dblZ_of_Y_ne'
  statement: {P Q : Fin 3 -> F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z != 0)
  proof: (dblZ_ne_zero_of_Y_ne' hP hQ hPz hQz hx hy).isUnit

中文:
引理 isUnit_dblZ_of_Y_ne'
  结论: {P Q : 有限集 3 -> F} (hP : W.方程 P) (hQ : W.方程 Q) (hPz : P z != 0)
  证明: (dblZ_ne_zero_of_Y_ne' hP hQ hPz hQz hx hy).isUnit

Depends on / 依赖: L.map, dblZ_ne_zero_of_Y_ne, iResolutionObj, isUnit
-/
lemma isUnit_dblZ_of_Y_ne' {P Q : Fin 3 -> F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z != 0)
    (hQz : Q z != 0) (hx : P x * Q z = Q x * P z) (hy : P y * Q z != W.negY Q * P z) :
    IsUnit (W.dblZ P) :=
  (dblZ_ne_zero_of_Y_ne' hP hQ hPz hQz hx hy).isUnit

/--
lemma `toAffine_slope_of_eq` / 引理 `toAffine_slope_of_eq`

English:
lemma toAffine_slope_of_eq
  statement: [DecidableEq F] {P Q : Fin 3 -> F}
  proof: by
  simp only [X_eq_iff hPz hQz, ne_eq, Y_eq_iff' hPz hQz] at hx hy
  rw [Affine.slope_of_Y_ne hx <| negY_of_Z_ne_zero hQz ▸ hy]; rw [← negY_of_Z_ne_zero hPz]
  simp [field, eval_polynomialX]

中文:
引理 toAffine_slope_of_eq
  结论: [DecidableEq F] {P Q : 有限集 3 -> F}
  证明: by
  simp only [X_eq_iff hPz hQz, ne_eq, Y_eq_iff' hPz hQz] at hx hy
  rw [Affine.slope_of_Y_ne hx <| negY_of_Z_ne_zero hQz ▸ hy]; rw [← negY_of_Z_ne_zero hPz]
  simp [field, eval_polynomialX]
-/
private lemma toAffine_slope_of_eq [DecidableEq F] {P Q : Fin 3 -> F}
    (hPz : P z != 0) (hQz : Q z != 0) (hx : P x * Q z = Q x * P z) (hy : P y * Q z != W.negY Q * P z) :
    W.toAffine.slope (P x / P z) (Q x / Q z) (P y / P z) (Q y / Q z) =
      -eval P W.polynomialX / P z / (P y - W.negY P) := by
  simp only [X_eq_iff hPz hQz, ne_eq, Y_eq_iff' hPz hQz] at hx hy
  rw [Affine.slope_of_Y_ne hx <| negY_of_Z_ne_zero hQz ▸ hy]; rw [← negY_of_Z_ne_zero hPz]
  simp [field, eval_polynomialX]

variable (W') in
/--
Definition of `dblX` / `dblX` 的定义

English:
definition dblX
  signature: (P : Fin 3 -> R)
  body: 2 * P x * P y ^ 3 + 3 * W'.a₁ * P x ^ 2 * P y ^ 2 + 6 * W'.a₂ * P x ^ 3 * P y
    - 8 * W'.a₂ * P y ^ 3 * P z + 9 * W'.a₃ * P x ^ 4 - 6 * W'.a₃ * P x * P y ^ 2 * P z
    - 6 * W'.a₄ * P x ^ 2 * P y * P z - 18 * W'.a₆ * P x * P y * P z ^ 2
    + 3 * W'.a₁ ^ 2 * P x ^ 3 * P y - 2 * W'.a₁ ^ 2 * P y ^ 3

中文:
定义 dblX
  签名: (P : 有限集 3 -> R)
  定义体: 2 * P x * P y ^ 3 + 3 * W'.a₁ * P x ^ 2 * P y ^ 2 + 6 * W'.a₂ * P x ^ 3 * P y
    - 8 * W'.a₂ * P y ^ 3 * P z + 9 * W'.a₃ * P x ^ 4 - 6 * W'.a₃ * P x * P y ^ 2 * P z
    - 6 * W'.a₄ * P x ^ 2 * P y * P z - 18 * W'.a₆ * P x * P y * P z ^ 2
    + 3 * W'.a₁ ^ 2 * P x ^ 3 * P y - 2 * W'.a₁ ^ 2 * P y ^ 3
-/
noncomputable def dblX (P : Fin 3 -> R) : R :=
  2 * P x * P y ^ 3 + 3 * W'.a₁ * P x ^ 2 * P y ^ 2 + 6 * W'.a₂ * P x ^ 3 * P y
    - 8 * W'.a₂ * P y ^ 3 * P z + 9 * W'.a₃ * P x ^ 4 - 6 * W'.a₃ * P x * P y ^ 2 * P z
    - 6 * W'.a₄ * P x ^ 2 * P y * P z - 18 * W'.a₆ * P x * P y * P z ^ 2
    + 3 * W'.a₁ ^ 2 * P x ^ 3 * P y - 2 * W'.a₁ ^ 2 * P y ^ 3 * P z + 3 * W'.a₁ * W'.a₂ * P x ^ 4
    - 12 * W'.a₁ * W'.a₂ * P x * P y ^ 2 * P z - 9 * W'.a₁ * W'.a₃ * P x ^ 2 * P y * P z
    - 3 * W'.a₁ * W'.a₄ * P x ^ 3 * P z - 9 * W'.a₁ * W'.a₆ * P x ^ 2 * P z ^ 2
    + 8 * W'.a₂ ^ 2 * P x ^ 2 * P y * P z + 12 * W'.a₂ * W'.a₃ * P x ^ 3 * P z
    - 12 * W'.a₂ * W'.a₃ * P y ^ 2 * P z ^ 2 + 8 * W'.a₂ * W'.a₄ * P x * P y * P z ^ 2
    - 12 * W'.a₃ ^ 2 * P x * P y * P z ^ 2 + 6 * W'.a₃ * W'.a₄ * P x ^ 2 * P z ^ 2
    + 2 * W'.a₄ ^ 2 * P y * P z ^ 3 + W'.a₁ ^ 3 * P x ^ 4 - 3 * W'.a₁ ^ 3 * P x * P y ^ 2 * P z
    - 2 * W'.a₁ ^ 2 * W'.a₂ * P x ^ 2 * P y * P z - 3 * W'.a₁ ^ 2 * W'.a₃ * P y ^ 2 * P z ^ 2
    + 2 * W'.a₁ ^ 2 * W'.a₄ * P x * P y * P z ^ 2 + 4 * W'.a₁ * W'.a₂ ^ 2 * P x ^ 3 * P z
    - 8 * W'.a₁ * W'.a₂ * W'.a₃ * P x * P y * P z ^ 2
    + 4 * W'.a₁ * W'.a₂ * W'.a₄ * P x ^ 2 * P z ^ 2 - 3 * W'.a₁ * W'.a₃ ^ 2 * P x ^ 2 * P z ^ 2
    + 2 * W'.a₁ * W'.a₃ * W'.a₄ * P y * P z ^ 3 + W'.a₁ * W'.a₄ ^ 2 * P x * P z ^ 3
    + 4 * W'.a₂ ^ 2 * W'.a₃ * P x ^ 2 * P z ^ 2 - 6 * W'.a₂ * W'.a₃ ^ 2 * P y * P z ^ 3
    + 4 * W'.a₂ * W'.a₃ * W'.a₄ * P x * P z ^ 3 - 2 * W'.a₃ ^ 3 * P x * P z ^ 3
    + W'.a₃ * W'.a₄ ^ 2 * P z ^ 4 - W'.a₁ ^ 4 * P x ^ 2 * P y * P z
    + W'.a₁ ^ 3 * W'.a₂ * P x ^ 3 * P z - 2 * W'.a₁ ^ 3 * W'.a₃ * P x * P y * P z ^ 2
    + W'.a₁ ^ 3 * W'.a₄ * P x ^ 2 * P z ^ 2 + W'.a₁ ^ 2 * W'.a₂ * W'.a₃ * P x ^ 2 * P z ^ 2
    - W'.a₁ ^ 2 * W'.a₃ ^ 2 * P y * P z ^ 3 + 2 * W'.a₁ ^ 2 * W'.a₃ * W'.a₄ * P x * P z ^ 3
    - W'.a₁ * W'.a₂ * W'.a₃ ^ 2 * P x * P z ^ 3 - W'.a₂ * W'.a₃ ^ 3 * P z ^ 4
    + W'.a₁ * W'.a₃ ^ 2 * W'.a₄ * P z ^ 4

/--
lemma `dblX_eq'` / 引理 `dblX_eq'`

English:
lemma dblX_eq'
  given: {P : Fin 3 -> R} (hP : W'.Equation P)
  statement: W'.dblX P * P z =
  proof: by
  linear_combination (norm := (rw [dblX, eval_polynomialX, negY]; ring1))
    9 * (W'.a₁ * P x ^ 2 + 2 * P x * P y) * (equation_iff _).mp hP

中文:
引理 dblX_eq'
  条件: {P : 有限集 3 -> R} (hP : W'.方程 P)
  结论: W'.dblX P * P z =
  证明: by
  linear_combination (norm := (rw [dblX, eval_polynomialX, negY]; ring1))
    9 * (W'.a₁ * P x ^ 2 + 2 * P x * P y) * (equation_iff _).mp hP

Depends on / 依赖: equation_iff, eval_polynomialX, linear_combination
-/
lemma dblX_eq' {P : Fin 3 -> R} (hP : W'.Equation P) : W'.dblX P * P z =
    (eval P W'.polynomialX ^ 2 - W'.a₁ * eval P W'.polynomialX * P z * (P y - W'.negY P)
      - W'.a₂ * P z ^ 2 * (P y - W'.negY P) ^ 2 - 2 * P x * P z * (P y - W'.negY P) ^ 2)
      * (P y - W'.negY P) := by
  linear_combination (norm := (rw [dblX, eval_polynomialX, negY]; ring1))
    9 * (W'.a₁ * P x ^ 2 + 2 * P x * P y) * (equation_iff _).mp hP

/--
lemma `dblX_eq` / 引理 `dblX_eq`

English:
lemma dblX_eq
  given: {P : Fin 3 -> F} (hP : W.Equation P) (hPz : P z != 0)
  statement: W.dblX P =
  proof: by
  rw [← dblX_eq' hP]; rw [mul_div_cancel_right₀ _ hPz]

中文:
引理 dblX_eq
  条件: {P : 有限集 3 -> F} (hP : W.方程 P) (hPz : P z != 0)
  结论: W.dblX P =
  证明: by
  rw [← dblX_eq' hP]; rw [mul_div_cancel_right₀ _ hPz]

Depends on / 依赖: dblX_eq, infer_instance
-/
lemma dblX_eq {P : Fin 3 -> F} (hP : W.Equation P) (hPz : P z != 0) : W.dblX P =
    ((eval P W.polynomialX ^ 2 - W.a₁ * eval P W.polynomialX * P z * (P y - W.negY P)
      - W.a₂ * P z ^ 2 * (P y - W.negY P) ^ 2 - 2 * P x * P z * (P y - W.negY P) ^ 2)
      * (P y - W.negY P)) / P z := by
  rw [← dblX_eq' hP]; rw [mul_div_cancel_right₀ _ hPz]

/--
lemma `dblX_smul` / 引理 `dblX_smul`

English:
lemma dblX_smul
  given: (P : Fin 3 -> R) (u : R)
  statement: W'.dblX (u • P) = u ^ 4 * W'.dblX P
  proof: by
  simp only [dblX, smul_fin3_ext]
  ring1

中文:
引理 dblX_smul
  条件: (P : 有限集 3 -> R) (u : R)
  结论: W'.dblX (u • P) = u ^ 4 * W'.dblX P
  证明: by
  simp only [dblX, smul_fin3_ext]
  ring1

Depends on / 依赖: IsLocalization, functor, localizerMorphism, smul_fin3_ext
-/
lemma dblX_smul (P : Fin 3 -> R) (u : R) : W'.dblX (u • P) = u ^ 4 * W'.dblX P := by
  simp only [dblX, smul_fin3_ext]
  ring1

/--
lemma `dblX_of_Z_eq_zero` / 引理 `dblX_of_Z_eq_zero`

English:
lemma dblX_of_Z_eq_zero
  given: [NoZeroDivisors R] {P : Fin 3 -> R} (hP : W'.Equation P) (hPz : P z = 0)
  proof: by
  rw [dblX]; rw [hPz]; rw [X_eq_zero_of_Z_eq_zero hP hPz]
  ring1

中文:
引理 dblX_of_Z_eq_zero
  条件: [无零因子 R] {P : 有限集 3 -> R} (hP : W'.方程 P) (hPz : P z = 0)
  证明: by
  rw [dblX]; rw [hPz]; rw [X_eq_zero_of_Z_eq_zero hP hPz]
  ring1

Depends on / 依赖: X_eq_zero_of_Z_eq_zero
-/
lemma dblX_of_Z_eq_zero [NoZeroDivisors R] {P : Fin 3 -> R} (hP : W'.Equation P) (hPz : P z = 0) :
    W'.dblX P = 0 := by
  rw [dblX]; rw [hPz]; rw [X_eq_zero_of_Z_eq_zero hP hPz]
  ring1

/--
lemma `dblX_of_Y_eq` / 引理 `dblX_of_Y_eq`

English:
lemma dblX_of_Y_eq
  statement: [NoZeroDivisors R] {P Q : Fin 3 -> R} (hP : W'.Equation P) (hPz : P z != 0)
  proof: by
  apply eq_zero_of_ne_zero_of_mul_right_eq_zero hPz
  rw [dblX_eq' hP]; rw [Y_eq_negY_of_Y_eq hQz hx hy hy']
  ring1

中文:
引理 dblX_of_Y_eq
  结论: [无零因子 R] {P Q : 有限集 3 -> R} (hP : W'.方程 P) (hPz : P z != 0)
  证明: by
  apply eq_zero_of_ne_zero_of_mul_right_eq_zero hPz
  rw [dblX_eq' hP]; rw [Y_eq_negY_of_Y_eq hQz hx hy hy']
  ring1

Depends on / 依赖: Y_eq_negY_of_Y_eq, dblX_eq, eq_zero_of_ne_zero_of_mul_right_eq_zero
-/
lemma dblX_of_Y_eq [NoZeroDivisors R] {P Q : Fin 3 -> R} (hP : W'.Equation P) (hPz : P z != 0)
    (hQz : Q z != 0) (hx : P x * Q z = Q x * P z) (hy : P y * Q z = Q y * P z)
    (hy' : P y * Q z = W'.negY Q * P z) : W'.dblX P = 0 := by
  apply eq_zero_of_ne_zero_of_mul_right_eq_zero hPz
  rw [dblX_eq' hP]; rw [Y_eq_negY_of_Y_eq hQz hx hy hy']
  ring1

/--
lemma `toAffine_addX_of_eq` / 引理 `toAffine_addX_of_eq`

English:
lemma toAffine_addX_of_eq
  given: {P : Fin 3 -> F} (hPz : P z != 0) {n d : F} (hd : d != 0)
  proof: by
  simp [field]
  ring1

中文:
引理 toAffine_addX_of_eq
  条件: {P : 有限集 3 -> F} (hPz : P z != 0) {n d : F} (hd : d != 0)
  证明: by
  simp [field]
  ring1
-/
private lemma toAffine_addX_of_eq {P : Fin 3 -> F} (hPz : P z != 0) {n d : F} (hd : d != 0) :
    W.toAffine.addX (P x / P z) (P x / P z) (-n / P z / d) =
      (n ^ 2 - W.a₁ * n * P z * d - W.a₂ * P z ^ 2 * d ^ 2 - 2 * P x * P z * d ^ 2) * d / P z
        / (P z * d ^ 3) := by
  simp [field]
  ring1

/--
lemma `dblX_of_Z_ne_zero` / 引理 `dblX_of_Z_ne_zero`

English:
lemma dblX_of_Z_ne_zero
  statement: [DecidableEq F] {P Q : Fin 3 -> F} (hP : W.Equation P) (hQ : W.Equation Q)
  proof: by
  rw [dblX_eq hP hPz]; rw [dblZ]; rw [toAffine_slope_of_eq hPz hQz hx hy]; rw [← (X_eq_iff hPz hQz).mp hx]; rw [toAffine_addX_of_eq hPz sub_ne_zero.mpr Y_ne_negY_of_Y_ne' hP hQ hPz hQz hx hy]

中文:
引理 dblX_of_Z_ne_zero
  结论: [DecidableEq F] {P Q : 有限集 3 -> F} (hP : W.方程 P) (hQ : W.方程 Q)
  证明: by
  rw [dblX_eq hP hPz]; rw [dblZ]; rw [toAffine_slope_of_eq hPz hQz hx hy]; rw [← (X_eq_iff hPz hQz).mp hx]; rw [toAffine_addX_of_eq hPz sub_ne_zero.mpr Y_ne_negY_of_Y_ne' hP hQ hPz hQz hx hy]

Depends on / 依赖: X_eq_iff, Y_ne_negY_of_Y_ne, dblX_eq, sub_ne_zero, sub_ne_zero.mpr, toAffine_addX_of_eq, toAffine_slope_of_eq
-/
lemma dblX_of_Z_ne_zero [DecidableEq F] {P Q : Fin 3 -> F} (hP : W.Equation P) (hQ : W.Equation Q)
    (hPz : P z != 0) (hQz : Q z != 0) (hx : P x * Q z = Q x * P z) (hy : P y * Q z != W.negY Q * P z) :
    W.dblX P / W.dblZ P = W.toAffine.addX (P x / P z) (Q x / Q z)
      (W.toAffine.slope (P x / P z) (Q x / Q z) (P y / P z) (Q y / Q z)) := by
  rw [dblX_eq hP hPz]; rw [dblZ]; rw [toAffine_slope_of_eq hPz hQz hx hy]; rw [← (X_eq_iff hPz hQz).mp hx]; rw [toAffine_addX_of_eq hPz sub_ne_zero.mpr Y_ne_negY_of_Y_ne' hP hQ hPz hQz hx hy]

variable (W') in
/--
Definition of `negDblY` / `negDblY` 的定义

English:
definition negDblY
  signature: (P : Fin 3 -> R)
  body: -P y ^ 4 - 3 * W'.a₁ * P x * P y ^ 3 - 9 * W'.a₃ * P x ^ 3 * P y + 3 * W'.a₃ * P y ^ 3 * P z
    - 3 * W'.a₄ * P x * P y ^ 2 * P z - 27 * W'.a₆ * P x ^ 3 * P z + 9 * W'.a₆ * P y ^ 2 * P z ^ 2
    - 3 * W'.a₁ ^ 2 * P x ^ 2 * P y ^ 2 + 4 * W'.a₁ * W'.a₂ * P y ^ 3 * P z
    - 3 * W'.a₁ * W'.a₂ * P x ^ 

中文:
定义 negDblY
  签名: (P : 有限集 3 -> R)
  定义体: -P y ^ 4 - 3 * W'.a₁ * P x * P y ^ 3 - 9 * W'.a₃ * P x ^ 3 * P y + 3 * W'.a₃ * P y ^ 3 * P z
    - 3 * W'.a₄ * P x * P y ^ 2 * P z - 27 * W'.a₆ * P x ^ 3 * P z + 9 * W'.a₆ * P y ^ 2 * P z ^ 2
    - 3 * W'.a₁ ^ 2 * P x ^ 2 * P y ^ 2 + 4 * W'.a₁ * W'.a₂ * P y ^ 3 * P z
    - 3 * W'.a₁ * W'.a₂ * P x ^ 
-/
noncomputable def negDblY (P : Fin 3 -> R) : R :=
  -P y ^ 4 - 3 * W'.a₁ * P x * P y ^ 3 - 9 * W'.a₃ * P x ^ 3 * P y + 3 * W'.a₃ * P y ^ 3 * P z
    - 3 * W'.a₄ * P x * P y ^ 2 * P z - 27 * W'.a₆ * P x ^ 3 * P z + 9 * W'.a₆ * P y ^ 2 * P z ^ 2
    - 3 * W'.a₁ ^ 2 * P x ^ 2 * P y ^ 2 + 4 * W'.a₁ * W'.a₂ * P y ^ 3 * P z
    - 3 * W'.a₁ * W'.a₂ * P x ^ 3 * P y - 9 * W'.a₁ * W'.a₃ * P x ^ 4
    + 6 * W'.a₁ * W'.a₃ * P x * P y ^ 2 * P z + 18 * W'.a₁ * W'.a₆ * P x * P y * P z ^ 2
    + 9 * W'.a₂ ^ 2 * P x ^ 4 - 8 * W'.a₂ ^ 2 * P x * P y ^ 2 * P z
    - 9 * W'.a₂ * W'.a₃ * P x ^ 2 * P y * P z + 9 * W'.a₂ * W'.a₄ * P x ^ 3 * P z
    - 4 * W'.a₂ * W'.a₄ * P y ^ 2 * P z ^ 2 - 27 * W'.a₂ * W'.a₆ * P x ^ 2 * P z ^ 2
    - 9 * W'.a₃ ^ 2 * P x ^ 3 * P z + 6 * W'.a₃ ^ 2 * P y ^ 2 * P z ^ 2
    - 12 * W'.a₃ * W'.a₄ * P x * P y * P z ^ 2 + 9 * W'.a₄ ^ 2 * P x ^ 2 * P z ^ 2
    - 2 * W'.a₁ ^ 3 * P x ^ 3 * P y + W'.a₁ ^ 3 * P y ^ 3 * P z + 3 * W'.a₁ ^ 2 * W'.a₂ * P x ^ 4
    + 2 * W'.a₁ ^ 2 * W'.a₂ * P x * P y ^ 2 * P z + 3 * W'.a₁ ^ 2 * W'.a₃ * P x ^ 2 * P y * P z
    + 3 * W'.a₁ ^ 2 * W'.a₄ * P x ^ 3 * P z - W'.a₁ ^ 2 * W'.a₄ * P y ^ 2 * P z ^ 2
    - 12 * W'.a₁ * W'.a₂ ^ 2 * P x ^ 2 * P y * P z - 6 * W'.a₁ * W'.a₂ * W'.a₃ * P x ^ 3 * P z
    + 4 * W'.a₁ * W'.a₂ * W'.a₃ * P y ^ 2 * P z ^ 2
    - 8 * W'.a₁ * W'.a₂ * W'.a₄ * P x * P y * P z ^ 2 + 6 * W'.a₁ * W'.a₃ ^ 2 * P x * P y * P z ^ 2
    - W'.a₁ * W'.a₄ ^ 2 * P y * P z ^ 3 + 8 * W'.a₂ ^ 3 * P x ^ 3 * P z
    - 8 * W'.a₂ ^ 2 * W'.a₃ * P x * P y * P z ^ 2 + 12 * W'.a₂ ^ 2 * W'.a₄ * P x ^ 2 * P z ^ 2
    - 9 * W'.a₂ * W'.a₃ ^ 2 * P x ^ 2 * P z ^ 2 - 4 * W'.a₂ * W'.a₃ * W'.a₄ * P y * P z ^ 3
    + 6 * W'.a₂ * W'.a₄ ^ 2 * P x * P z ^ 3 + W'.a₃ ^ 3 * P y * P z ^ 3
    - 3 * W'.a₃ ^ 2 * W'.a₄ * P x * P z ^ 3 + W'.a₄ ^ 3 * P z ^ 4 + W'.a₁ ^ 4 * P x * P y ^ 2 * P z
    - 3 * W'.a₁ ^ 3 * W'.a₂ * P x ^ 2 * P y * P z + W'.a₁ ^ 3 * W'.a₃ * P y ^ 2 * P z ^ 2
    - 2 * W'.a₁ ^ 3 * W'.a₄ * P x * P y * P z ^ 2 + 2 * W'.a₁ ^ 2 * W'.a₂ ^ 2 * P x ^ 3 * P z
    - 2 * W'.a₁ ^ 2 * W'.a₂ * W'.a₃ * P x * P y * P z ^ 2
    + 3 * W'.a₁ ^ 2 * W'.a₂ * W'.a₄ * P x ^ 2 * P z ^ 2
    - 2 * W'.a₁ ^ 2 * W'.a₃ * W'.a₄ * P y * P z ^ 3 + W'.a₁ ^ 2 * W'.a₄ ^ 2 * P x * P z ^ 3
    + W'.a₁ * W'.a₂ * W'.a₃ ^ 2 * P y * P z ^ 3 + 2 * W'.a₁ * W'.a₂ * W'.a₃ * W'.a₄ * P x * P z ^ 3
    + W'.a₁ * W'.a₃ * W'.a₄ ^ 2 * P z ^ 4 - 2 * W'.a₂ ^ 2 * W'.a₃ ^ 2 * P x * P z ^ 3
    - W'.a₂ * W'.a₃ ^ 2 * W'.a₄ * P z ^ 4

/--
lemma `negDblY_eq'` / 引理 `negDblY_eq'`

English:
lemma negDblY_eq'
  given: {P : Fin 3 -> R} (hP : W'.Equation P)
  statement: W'.negDblY P * P z ^ 2 =
  proof: by
  linear_combination (norm := (rw [negDblY, eval_polynomialX, negY]; ring1))
    -9 * (P y ^ 2 * P z + 2 * W'.a₁ * P x * P y * P z - 3 * P x ^ 3 - 3 * W'.a₂ * P x ^ 2 * P z)
      * (equation_iff _).mp hP

中文:
引理 negDblY_eq'
  条件: {P : 有限集 3 -> R} (hP : W'.方程 P)
  结论: W'.negDblY P * P z ^ 2 =
  证明: by
  linear_combination (norm := (rw [negDblY, eval_polynomialX, negY]; ring1))
    -9 * (P y ^ 2 * P z + 2 * W'.a₁ * P x * P y * P z - 3 * P x ^ 3 - 3 * W'.a₂ * P x ^ 2 * P z)
      * (equation_iff _).mp hP

Depends on / 依赖: equation_iff, eval_polynomialX, linear_combination, negDblY
-/
lemma negDblY_eq' {P : Fin 3 -> R} (hP : W'.Equation P) : W'.negDblY P * P z ^ 2 =
    -eval P W'.polynomialX * (eval P W'.polynomialX ^ 2
      - W'.a₁ * eval P W'.polynomialX * P z * (P y - W'.negY P)
      - W'.a₂ * P z ^ 2 * (P y - W'.negY P) ^ 2 - 2 * P x * P z * (P y - W'.negY P) ^ 2
      - P x * P z * (P y - W'.negY P) ^ 2) + P y * P z ^ 2 * (P y - W'.negY P) ^ 3 := by
  linear_combination (norm := (rw [negDblY, eval_polynomialX, negY]; ring1))
    -9 * (P y ^ 2 * P z + 2 * W'.a₁ * P x * P y * P z - 3 * P x ^ 3 - 3 * W'.a₂ * P x ^ 2 * P z)
      * (equation_iff _).mp hP

/--
lemma `negDblY_eq` / 引理 `negDblY_eq`

English:
lemma negDblY_eq
  given: {P : Fin 3 -> F} (hP : W.Equation P) (hPz : P z != 0)
  statement: W.negDblY P =
  proof: by
  rw [← negDblY_eq' hP]; rw [mul_div_cancel_right₀ _ <| pow_ne_zero 2 hPz]

中文:
引理 negDblY_eq
  条件: {P : 有限集 3 -> F} (hP : W.方程 P) (hPz : P z != 0)
  结论: W.negDblY P =
  证明: by
  rw [← negDblY_eq' hP]; rw [mul_div_cancel_right₀ _ <| pow_ne_zero 2 hPz]

Depends on / 依赖: negDblY_eq, pow_ne_zero
-/
lemma negDblY_eq {P : Fin 3 -> F} (hP : W.Equation P) (hPz : P z != 0) : W.negDblY P =
    (-eval P W.polynomialX * (eval P W.polynomialX ^ 2
      - W.a₁ * eval P W.polynomialX * P z * (P y - W.negY P)
      - W.a₂ * P z ^ 2 * (P y - W.negY P) ^ 2 - 2 * P x * P z * (P y - W.negY P) ^ 2
      - P x * P z * (P y - W.negY P) ^ 2) + P y * P z ^ 2 * (P y - W.negY P) ^ 3) / P z ^ 2 := by
  rw [← negDblY_eq' hP]; rw [mul_div_cancel_right₀ _ <| pow_ne_zero 2 hPz]

/--
lemma `negDblY_smul` / 引理 `negDblY_smul`

English:
lemma negDblY_smul
  given: (P : Fin 3 -> R) (u : R)
  statement: W'.negDblY (u • P) = u ^ 4 * W'.negDblY P
  proof: by
  simp only [negDblY, smul_fin3_ext]
  ring1

中文:
引理 negDblY_smul
  条件: (P : 有限集 3 -> R) (u : R)
  结论: W'.negDblY (u • P) = u ^ 4 * W'.negDblY P
  证明: by
  simp only [negDblY, smul_fin3_ext]
  ring1

Depends on / 依赖: negDblY, smul_fin3_ext
-/
lemma negDblY_smul (P : Fin 3 -> R) (u : R) : W'.negDblY (u • P) = u ^ 4 * W'.negDblY P := by
  simp only [negDblY, smul_fin3_ext]
  ring1

/--
lemma `negDblY_of_Z_eq_zero` / 引理 `negDblY_of_Z_eq_zero`

English:
lemma negDblY_of_Z_eq_zero
  given: [NoZeroDivisors R] {P : Fin 3 -> R} (hP : W'.Equation P) (hPz : P z = 0)
  proof: by
  rw [negDblY]; rw [hPz]; rw [X_eq_zero_of_Z_eq_zero hP hPz]
  ring1

中文:
引理 negDblY_of_Z_eq_zero
  条件: [无零因子 R] {P : 有限集 3 -> R} (hP : W'.方程 P) (hPz : P z = 0)
  证明: by
  rw [negDblY]; rw [hPz]; rw [X_eq_zero_of_Z_eq_zero hP hPz]
  ring1

Depends on / 依赖: X_eq_zero_of_Z_eq_zero, negDblY
-/
lemma negDblY_of_Z_eq_zero [NoZeroDivisors R] {P : Fin 3 -> R} (hP : W'.Equation P) (hPz : P z = 0) :
    W'.negDblY P = -P y ^ 4 := by
  rw [negDblY]; rw [hPz]; rw [X_eq_zero_of_Z_eq_zero hP hPz]
  ring1

/--
lemma `negDblY_of_Y_eq'` / 引理 `negDblY_of_Y_eq'`

English:
lemma negDblY_of_Y_eq'
  statement: [NoZeroDivisors R] {P Q : Fin 3 -> R} (hP : W'.Equation P) (hQz : Q z != 0)
  proof: by
  rw [negDblY_eq' hP]; rw [Y_eq_negY_of_Y_eq hQz hx hy hy']
  ring1

中文:
引理 negDblY_of_Y_eq'
  结论: [无零因子 R] {P Q : 有限集 3 -> R} (hP : W'.方程 P) (hQz : Q z != 0)
  证明: by
  rw [negDblY_eq' hP]; rw [Y_eq_negY_of_Y_eq hQz hx hy hy']
  ring1

Depends on / 依赖: Y_eq_negY_of_Y_eq, negDblY_eq
-/
lemma negDblY_of_Y_eq' [NoZeroDivisors R] {P Q : Fin 3 -> R} (hP : W'.Equation P) (hQz : Q z != 0)
    (hx : P x * Q z = Q x * P z) (hy : P y * Q z = Q y * P z) (hy' : P y * Q z = W'.negY Q * P z) :
    W'.negDblY P * P z ^ 2 = -eval P W'.polynomialX ^ 3 := by
  rw [negDblY_eq' hP]; rw [Y_eq_negY_of_Y_eq hQz hx hy hy']
  ring1

/--
lemma `negDblY_of_Y_eq` / 引理 `negDblY_of_Y_eq`

English:
lemma negDblY_of_Y_eq
  statement: {P Q : Fin 3 -> F} (hP : W.Equation P) (hPz : P z != 0) (hQz : Q z != 0)
  proof: by
  rw [dblU]; rw [← neg_div]; rw [← negDblY_of_Y_eq' hP hQz hx hy hy']; rw [mul_div_cancel_right₀ _ pow_ne_zero 2 hPz]

中文:
引理 negDblY_of_Y_eq
  结论: {P Q : 有限集 3 -> F} (hP : W.方程 P) (hPz : P z != 0) (hQz : Q z != 0)
  证明: by
  rw [dblU]; rw [← neg_div]; rw [← negDblY_of_Y_eq' hP hQz hx hy hy']; rw [mul_div_cancel_right₀ _ pow_ne_zero 2 hPz]

Depends on / 依赖: negDblY_of_Y_eq, neg_div, pow_ne_zero
-/
lemma negDblY_of_Y_eq {P Q : Fin 3 -> F} (hP : W.Equation P) (hPz : P z != 0) (hQz : Q z != 0)
    (hx : P x * Q z = Q x * P z) (hy : P y * Q z = Q y * P z) (hy' : P y * Q z = W.negY Q * P z) :
    W.negDblY P = -W.dblU P := by
  rw [dblU]; rw [← neg_div]; rw [← negDblY_of_Y_eq' hP hQz hx hy hy']; rw [mul_div_cancel_right₀ _ pow_ne_zero 2 hPz]

/--
lemma `toAffine_negAddY_of_eq` / 引理 `toAffine_negAddY_of_eq`

English:
lemma toAffine_negAddY_of_eq
  given: {P : Fin 3 -> F} (hPz : P z != 0) {n d : F} (hd : d != 0)
  proof: by
  rw [Affine.negAddY]; rw [toAffine_addX_of_eq hPz hd]
  simp [field]

中文:
引理 toAffine_negAddY_of_eq
  条件: {P : 有限集 3 -> F} (hPz : P z != 0) {n d : F} (hd : d != 0)
  证明: by
  rw [Affine.negAddY]; rw [toAffine_addX_of_eq hPz hd]
  simp [field]
-/
private lemma toAffine_negAddY_of_eq {P : Fin 3 -> F} (hPz : P z != 0) {n d : F} (hd : d != 0) :
    W.toAffine.negAddY (P x / P z) (P x / P z) (P y / P z) (-n / P z / d) =
      (-n * (n ^ 2 - W.a₁ * n * P z * d - W.a₂ * P z ^ 2 * d ^ 2 - 2 * P x * P z * d ^ 2
          - P x * P z * d ^ 2) + P y * P z ^ 2 * d ^ 3) / P z ^ 2 / (P z * d ^ 3) := by
  rw [Affine.negAddY]; rw [toAffine_addX_of_eq hPz hd]
  simp [field]

/--
lemma `negDblY_of_Z_ne_zero` / 引理 `negDblY_of_Z_ne_zero`

English:
lemma negDblY_of_Z_ne_zero
  statement: [DecidableEq F] {P Q : Fin 3 -> F} (hP : W.Equation P) (hQ : W.Equation Q)
  proof: by
  rw [negDblY_eq hP hPz]; rw [dblZ]; rw [toAffine_slope_of_eq hPz hQz hx hy]; rw [← (X_eq_iff hPz hQz).mp hx]; rw [toAffine_negAddY_of_eq hPz sub_ne_zero.mpr Y_ne_negY_of_Y_ne' hP hQ hPz hQz hx hy]

中文:
引理 negDblY_of_Z_ne_zero
  结论: [DecidableEq F] {P Q : 有限集 3 -> F} (hP : W.方程 P) (hQ : W.方程 Q)
  证明: by
  rw [negDblY_eq hP hPz]; rw [dblZ]; rw [toAffine_slope_of_eq hPz hQz hx hy]; rw [← (X_eq_iff hPz hQz).mp hx]; rw [toAffine_negAddY_of_eq hPz sub_ne_zero.mpr Y_ne_negY_of_Y_ne' hP hQ hPz hQz hx hy]

Depends on / 依赖: X_eq_iff, Y_ne_negY_of_Y_ne, negDblY_eq, sub_ne_zero, sub_ne_zero.mpr, toAffine_negAddY_of_eq, toAffine_slope_of_eq
-/
lemma negDblY_of_Z_ne_zero [DecidableEq F] {P Q : Fin 3 -> F} (hP : W.Equation P) (hQ : W.Equation Q)
    (hPz : P z != 0) (hQz : Q z != 0) (hx : P x * Q z = Q x * P z) (hy : P y * Q z != W.negY Q * P z) :
    W.negDblY P / W.dblZ P = W.toAffine.negAddY (P x / P z) (Q x / Q z) (P y / P z)
      (W.toAffine.slope (P x / P z) (Q x / Q z) (P y / P z) (Q y / Q z)) := by
  rw [negDblY_eq hP hPz]; rw [dblZ]; rw [toAffine_slope_of_eq hPz hQz hx hy]; rw [← (X_eq_iff hPz hQz).mp hx]; rw [toAffine_negAddY_of_eq hPz sub_ne_zero.mpr Y_ne_negY_of_Y_ne' hP hQ hPz hQz hx hy]

variable (W') in
/--
Definition of `dblY` / `dblY` 的定义

English:
definition dblY
  signature: (P : Fin 3 -> R)
  body: W'.negY ![W'.dblX P, W'.negDblY P, W'.dblZ P]

中文:
定义 dblY
  签名: (P : 有限集 3 -> R)
  定义体: W'.negY ![W'.dblX P, W'.negDblY P, W'.dblZ P]

Depends on / 依赖: negDblY
-/
noncomputable def dblY (P : Fin 3 -> R) : R :=
  W'.negY ![W'.dblX P, W'.negDblY P, W'.dblZ P]

/--
lemma `dblY_smul` / 引理 `dblY_smul`

English:
lemma dblY_smul
  given: (P : Fin 3 -> R) (u : R)
  statement: W'.dblY (u • P) = u ^ 4 * W'.dblY P
  proof: by
  simp only [dblY, negY_eq, negDblY_smul, dblX_smul, dblZ_smul]
  ring1

中文:
引理 dblY_smul
  条件: (P : 有限集 3 -> R) (u : R)
  结论: W'.dblY (u • P) = u ^ 4 * W'.dblY P
  证明: by
  simp only [dblY, negY_eq, negDblY_smul, dblX_smul, dblZ_smul]
  ring1

Depends on / 依赖: dblX_smul, dblZ_smul, negDblY_smul, negY_eq
-/
lemma dblY_smul (P : Fin 3 -> R) (u : R) : W'.dblY (u • P) = u ^ 4 * W'.dblY P := by
  simp only [dblY, negY_eq, negDblY_smul, dblX_smul, dblZ_smul]
  ring1

/--
lemma `dblY_of_Z_eq_zero` / 引理 `dblY_of_Z_eq_zero`

English:
lemma dblY_of_Z_eq_zero
  given: [NoZeroDivisors R] {P : Fin 3 -> R} (hP : W'.Equation P) (hPz : P z = 0)
  proof: by
  rw [dblY]; rw [negY_eq]; rw [negDblY_of_Z_eq_zero hP hPz]; rw [dblX_of_Z_eq_zero hP hPz]; rw [dblZ_of_Z_eq_zero hPz]
  ring1

中文:
引理 dblY_of_Z_eq_zero
  条件: [无零因子 R] {P : 有限集 3 -> R} (hP : W'.方程 P) (hPz : P z = 0)
  证明: by
  rw [dblY]; rw [negY_eq]; rw [negDblY_of_Z_eq_zero hP hPz]; rw [dblX_of_Z_eq_zero hP hPz]; rw [dblZ_of_Z_eq_zero hPz]
  ring1

Depends on / 依赖: dblX_of_Z_eq_zero, dblZ_of_Z_eq_zero, negDblY_of_Z_eq_zero, negY_eq
-/
lemma dblY_of_Z_eq_zero [NoZeroDivisors R] {P : Fin 3 -> R} (hP : W'.Equation P) (hPz : P z = 0) :
    W'.dblY P = P y ^ 4 := by
  rw [dblY]; rw [negY_eq]; rw [negDblY_of_Z_eq_zero hP hPz]; rw [dblX_of_Z_eq_zero hP hPz]; rw [dblZ_of_Z_eq_zero hPz]
  ring1

/--
lemma `dblY_of_Y_eq'` / 引理 `dblY_of_Y_eq'`

English:
lemma dblY_of_Y_eq'
  statement: [NoZeroDivisors R] {P Q : Fin 3 -> R} (hP : W'.Equation P) (hPz : P z != 0)
  proof: by
  linear_combination (norm := (rw [dblY, negY_eq, dblX_of_Y_eq hP hPz hQz hx hy hy',
    dblZ_of_Y_eq hQz hx hy hy']; ring1)) -negDblY_of_Y_eq' hP hQz hx hy hy'

中文:
引理 dblY_of_Y_eq'
  结论: [无零因子 R] {P Q : 有限集 3 -> R} (hP : W'.方程 P) (hPz : P z != 0)
  证明: by
  linear_combination (norm := (rw [dblY, negY_eq, dblX_of_Y_eq hP hPz hQz hx hy hy',
    dblZ_of_Y_eq hQz hx hy hy']; ring1)) -negDblY_of_Y_eq' hP hQz hx hy hy'

Depends on / 依赖: dblX_of_Y_eq, dblZ_of_Y_eq, linear_combination, negDblY_of_Y_eq, negY_eq
-/
lemma dblY_of_Y_eq' [NoZeroDivisors R] {P Q : Fin 3 -> R} (hP : W'.Equation P) (hPz : P z != 0)
    (hQz : Q z != 0) (hx : P x * Q z = Q x * P z) (hy : P y * Q z = Q y * P z)
    (hy' : P y * Q z = W'.negY Q * P z) : W'.dblY P * P z ^ 2 = eval P W'.polynomialX ^ 3 := by
  linear_combination (norm := (rw [dblY, negY_eq, dblX_of_Y_eq hP hPz hQz hx hy hy',
    dblZ_of_Y_eq hQz hx hy hy']; ring1)) -negDblY_of_Y_eq' hP hQz hx hy hy'

/--
lemma `dblY_of_Y_eq` / 引理 `dblY_of_Y_eq`

English:
lemma dblY_of_Y_eq
  statement: {P Q : Fin 3 -> F} (hP : W.Equation P) (hPz : P z != 0) (hQz : Q z != 0)
  proof: by
  rw [dblU]; rw [← dblY_of_Y_eq' hP hPz hQz hx hy hy']; rw [mul_div_cancel_right₀ _ <| pow_ne_zero 2 hPz]

中文:
引理 dblY_of_Y_eq
  结论: {P Q : 有限集 3 -> F} (hP : W.方程 P) (hPz : P z != 0) (hQz : Q z != 0)
  证明: by
  rw [dblU]; rw [← dblY_of_Y_eq' hP hPz hQz hx hy hy']; rw [mul_div_cancel_right₀ _ <| pow_ne_zero 2 hPz]

Depends on / 依赖: dblY_of_Y_eq, pow_ne_zero
-/
lemma dblY_of_Y_eq {P Q : Fin 3 -> F} (hP : W.Equation P) (hPz : P z != 0) (hQz : Q z != 0)
    (hx : P x * Q z = Q x * P z) (hy : P y * Q z = Q y * P z) (hy' : P y * Q z = W.negY Q * P z) :
    W.dblY P = W.dblU P := by
  rw [dblU]; rw [← dblY_of_Y_eq' hP hPz hQz hx hy hy']; rw [mul_div_cancel_right₀ _ <| pow_ne_zero 2 hPz]

/--
lemma `dblY_of_Z_ne_zero` / 引理 `dblY_of_Z_ne_zero`

English:
lemma dblY_of_Z_ne_zero
  statement: [DecidableEq F] {P Q : Fin 3 -> F} (hP : W.Equation P) (hQ : W.Equation Q)
  proof: by
  erw [dblY, negY_of_Z_ne_zero <| dblZ_ne_zero_of_Y_ne' hP hQ hPz hQz hx hy,
    dblX_of_Z_ne_zero hP hQ hPz hQz hx hy, negDblY_of_Z_ne_zero hP hQ hPz hQz hx hy, Affine.addY]

中文:
引理 dblY_of_Z_ne_zero
  结论: [DecidableEq F] {P Q : 有限集 3 -> F} (hP : W.方程 P) (hQ : W.方程 Q)
  证明: by
  erw [dblY, negY_of_Z_ne_zero <| dblZ_ne_zero_of_Y_ne' hP hQ hPz hQz hx hy,
    dblX_of_Z_ne_zero hP hQ hPz hQz hx hy, negDblY_of_Z_ne_zero hP hQ hPz hQz hx hy, Affine.addY]

Depends on / 依赖: Affine, Affine.addY, dblX_of_Z_ne_zero, dblZ_ne_zero_of_Y_ne, negDblY_of_Z_ne_zero, negY_of_Z_ne_zero
-/
lemma dblY_of_Z_ne_zero [DecidableEq F] {P Q : Fin 3 -> F} (hP : W.Equation P) (hQ : W.Equation Q)
    (hPz : P z != 0) (hQz : Q z != 0) (hx : P x * Q z = Q x * P z) (hy : P y * Q z != W.negY Q * P z) :
    W.dblY P / W.dblZ P = W.toAffine.addY (P x / P z) (Q x / Q z) (P y / P z)
      (W.toAffine.slope (P x / P z) (Q x / Q z) (P y / P z) (Q y / Q z)) := by
  erw [dblY, negY_of_Z_ne_zero <| dblZ_ne_zero_of_Y_ne' hP hQ hPz hQz hx hy,
    dblX_of_Z_ne_zero hP hQ hPz hQz hx hy, negDblY_of_Z_ne_zero hP hQ hPz hQz hx hy, Affine.addY]

variable (W') in
/--
Definition of `dblXYZ` / `dblXYZ` 的定义

English:
definition dblXYZ
  signature: (P : Fin 3 -> R)
  body: ![W'.dblX P, W'.dblY P, W'.dblZ P]

中文:
定义 dblXYZ
  签名: (P : 有限集 3 -> R)
  定义体: ![W'.dblX P, W'.dblY P, W'.dblZ P]
-/
noncomputable def dblXYZ (P : Fin 3 -> R) : Fin 3 -> R :=
  ![W'.dblX P, W'.dblY P, W'.dblZ P]

/--
lemma `dblXYZ_X` / 引理 `dblXYZ_X`

English:
lemma dblXYZ_X
  given: (P : Fin 3 -> R)
  statement: W'.dblXYZ P x = W'.dblX P
  proof: rfl

中文:
引理 dblXYZ_X
  条件: (P : 有限集 3 -> R)
  结论: W'.dblXYZ P x = W'.dblX P
  证明: rfl
-/
lemma dblXYZ_X (P : Fin 3 -> R) : W'.dblXYZ P x = W'.dblX P :=
  rfl

/--
lemma `dblXYZ_Y` / 引理 `dblXYZ_Y`

English:
lemma dblXYZ_Y
  given: (P : Fin 3 -> R)
  statement: W'.dblXYZ P y = W'.dblY P
  proof: rfl

中文:
引理 dblXYZ_Y
  条件: (P : 有限集 3 -> R)
  结论: W'.dblXYZ P y = W'.dblY P
  证明: rfl
-/
lemma dblXYZ_Y (P : Fin 3 -> R) : W'.dblXYZ P y = W'.dblY P :=
  rfl

/--
lemma `dblXYZ_Z` / 引理 `dblXYZ_Z`

English:
lemma dblXYZ_Z
  given: (P : Fin 3 -> R)
  statement: W'.dblXYZ P z = W'.dblZ P
  proof: rfl

中文:
引理 dblXYZ_Z
  条件: (P : 有限集 3 -> R)
  结论: W'.dblXYZ P z = W'.dblZ P
  证明: rfl
-/
lemma dblXYZ_Z (P : Fin 3 -> R) : W'.dblXYZ P z = W'.dblZ P :=
  rfl

/--
lemma `dblXYZ_smul` / 引理 `dblXYZ_smul`

English:
lemma dblXYZ_smul
  given: (P : Fin 3 -> R) (u : R)
  statement: W'.dblXYZ (u • P) = u ^ 4 • W'.dblXYZ P
  proof: by
  rw [dblXYZ]; rw [dblX_smul]; rw [dblY_smul]; rw [dblZ_smul]; rw [smul_fin3]; rw [dblXYZ_X]; rw [dblXYZ_Y]; rw [dblXYZ_Z]

中文:
引理 dblXYZ_smul
  条件: (P : 有限集 3 -> R) (u : R)
  结论: W'.dblXYZ (u • P) = u ^ 4 • W'.dblXYZ P
  证明: by
  rw [dblXYZ]; rw [dblX_smul]; rw [dblY_smul]; rw [dblZ_smul]; rw [smul_fin3]; rw [dblXYZ_X]; rw [dblXYZ_Y]; rw [dblXYZ_Z]

Depends on / 依赖: dblXYZ, dblXYZ_X, dblXYZ_Y, dblXYZ_Z, dblX_smul, dblY_smul, dblZ_smul, smul_fin3
-/
lemma dblXYZ_smul (P : Fin 3 -> R) (u : R) : W'.dblXYZ (u • P) = u ^ 4 • W'.dblXYZ P := by
  rw [dblXYZ]; rw [dblX_smul]; rw [dblY_smul]; rw [dblZ_smul]; rw [smul_fin3]; rw [dblXYZ_X]; rw [dblXYZ_Y]; rw [dblXYZ_Z]

/--
lemma `dblXYZ_of_Z_eq_zero` / 引理 `dblXYZ_of_Z_eq_zero`

English:
lemma dblXYZ_of_Z_eq_zero
  given: [NoZeroDivisors R] {P : Fin 3 -> R} (hP : W'.Equation P) (hPz : P z = 0)
  proof: by
  erw [dblXYZ, dblX_of_Z_eq_zero hP hPz, dblY_of_Z_eq_zero hP hPz, dblZ_of_Z_eq_zero hPz, smul_fin3,
    mul_zero, mul_one]

中文:
引理 dblXYZ_of_Z_eq_zero
  条件: [无零因子 R] {P : 有限集 3 -> R} (hP : W'.方程 P) (hPz : P z = 0)
  证明: by
  erw [dblXYZ, dblX_of_Z_eq_zero hP hPz, dblY_of_Z_eq_zero hP hPz, dblZ_of_Z_eq_zero hPz, smul_fin3,
    mul_zero, mul_one]

Depends on / 依赖: dblXYZ, dblX_of_Z_eq_zero, dblY_of_Z_eq_zero, dblZ_of_Z_eq_zero, mul_one, mul_zero, smul_fin3
-/
lemma dblXYZ_of_Z_eq_zero [NoZeroDivisors R] {P : Fin 3 -> R} (hP : W'.Equation P) (hPz : P z = 0) :
    W'.dblXYZ P = P y ^ 4 • ![0, 1, 0] := by
  erw [dblXYZ, dblX_of_Z_eq_zero hP hPz, dblY_of_Z_eq_zero hP hPz, dblZ_of_Z_eq_zero hPz, smul_fin3,
    mul_zero, mul_one]

/--
lemma `dblXYZ_of_Y_eq` / 引理 `dblXYZ_of_Y_eq`

English:
lemma dblXYZ_of_Y_eq
  statement: {P Q : Fin 3 -> F} (hP : W.Equation P) (hPz : P z != 0) (hQz : Q z != 0)
  proof: by
  erw [dblXYZ, dblX_of_Y_eq hP hPz hQz hx hy hy', dblY_of_Y_eq hP hPz hQz hx hy hy',
    dblZ_of_Y_eq hQz hx hy hy', smul_fin3, mul_zero, mul_one]

中文:
引理 dblXYZ_of_Y_eq
  结论: {P Q : 有限集 3 -> F} (hP : W.方程 P) (hPz : P z != 0) (hQz : Q z != 0)
  证明: by
  erw [dblXYZ, dblX_of_Y_eq hP hPz hQz hx hy hy', dblY_of_Y_eq hP hPz hQz hx hy hy',
    dblZ_of_Y_eq hQz hx hy hy', smul_fin3, mul_zero, mul_one]

Depends on / 依赖: dblXYZ, dblX_of_Y_eq, dblY_of_Y_eq, dblZ_of_Y_eq, mul_one, mul_zero, smul_fin3
-/
lemma dblXYZ_of_Y_eq {P Q : Fin 3 -> F} (hP : W.Equation P) (hPz : P z != 0) (hQz : Q z != 0)
    (hx : P x * Q z = Q x * P z) (hy : P y * Q z = Q y * P z) (hy' : P y * Q z = W.negY Q * P z) :
    W.dblXYZ P = W.dblU P • ![0, 1, 0] := by
  erw [dblXYZ, dblX_of_Y_eq hP hPz hQz hx hy hy', dblY_of_Y_eq hP hPz hQz hx hy hy',
    dblZ_of_Y_eq hQz hx hy hy', smul_fin3, mul_zero, mul_one]

/--
lemma `dblXYZ_of_Z_ne_zero` / 引理 `dblXYZ_of_Z_ne_zero`

English:
lemma dblXYZ_of_Z_ne_zero
  statement: [DecidableEq F] {P Q : Fin 3 -> F} (hP : W.Equation P) (hQ : W.Equation Q)
  proof: by
have hZ : IsUnit W.dblZ P := isUnit_dblZ_of_Y_ne' hP hQ hPz hQz hx hy
  erw [dblXYZ, smul_fin3, ← dblX_of_Z_ne_zero hP hQ hPz hQz hx hy, hZ.mul_div_cancel,
    ← dblY_of_Z_ne_zero hP hQ hPz hQz hx hy, hZ.mul_div_cancel, mul_one]

中文:
引理 dblXYZ_of_Z_ne_zero
  结论: [DecidableEq F] {P Q : 有限集 3 -> F} (hP : W.方程 P) (hQ : W.方程 Q)
  证明: by
have hZ : IsUnit W.dblZ P := isUnit_dblZ_of_Y_ne' hP hQ hPz hQz hx hy
  erw [dblXYZ, smul_fin3, ← dblX_of_Z_ne_zero hP hQ hPz hQz hx hy, hZ.mul_div_cancel,
    ← dblY_of_Z_ne_zero hP hQ hPz hQz hx hy, hZ.mul_div_cancel, mul_one]

Depends on / 依赖: IsUnit, W.dblZ, dblXYZ, dblX_of_Z_ne_zero, dblY_of_Z_ne_zero, hZ.mul_div_cancel, isUnit_dblZ_of_Y_ne, mul_div_cancel, mul_one, smul_fin3
-/
lemma dblXYZ_of_Z_ne_zero [DecidableEq F] {P Q : Fin 3 -> F} (hP : W.Equation P) (hQ : W.Equation Q)
    (hPz : P z != 0) (hQz : Q z != 0) (hx : P x * Q z = Q x * P z) (hy : P y * Q z != W.negY Q * P z) :
    W.dblXYZ P = W.dblZ P •
      ![W.toAffine.addX (P x / P z) (Q x / Q z)
          (W.toAffine.slope (P x / P z) (Q x / Q z) (P y / P z) (Q y / Q z)),
        W.toAffine.addY (P x / P z) (Q x / Q z) (P y / P z)
          (W.toAffine.slope (P x / P z) (Q x / Q z) (P y / P z) (Q y / Q z)), 1] := by
have hZ : IsUnit W.dblZ P := isUnit_dblZ_of_Y_ne' hP hQ hPz hQz hx hy
  erw [dblXYZ, smul_fin3, ← dblX_of_Z_ne_zero hP hQ hPz hQz hx hy, hZ.mul_div_cancel,
    ← dblY_of_Z_ne_zero hP hQ hPz hQz hx hy, hZ.mul_div_cancel, mul_one]

/-! ## Addition formulae in projective coordinates -/

/--
Definition of `addU` / `addU` 的定义

English:
definition addU
  signature: (P Q : Fin 3 -> F)
  body: -(P y * Q z - Q y * P z) ^ 3 / (P z * Q z)

中文:
定义 addU
  签名: (P Q : 有限集 3 -> F)
  定义体: -(P y * Q z - Q y * P z) ^ 3 / (P z * Q z)
-/
def addU (P Q : Fin 3 -> F) : F :=
  -(P y * Q z - Q y * P z) ^ 3 / (P z * Q z)

/--
lemma `addU_smul` / 引理 `addU_smul`

English:
lemma addU_smul
  given: (P Q : Fin 3 -> F) (u v : F)
  statement: addU (u • P) (v • Q) = (u * v) ^ 2 * addU P Q
  proof: by
  simp [field, addU]

中文:
引理 addU_smul
  条件: (P Q : 有限集 3 -> F) (u v : F)
  结论: addU (u • P) (v • Q) = (u * v) ^ 2 * addU P Q
  证明: by
  simp [field, addU]
-/
lemma addU_smul (P Q : Fin 3 -> F) (u v : F) : addU (u • P) (v • Q) = (u * v) ^ 2 * addU P Q := by
  simp [field, addU]

/--
lemma `addU_of_Z_eq_zero_left` / 引理 `addU_of_Z_eq_zero_left`

English:
lemma addU_of_Z_eq_zero_left
  given: {P Q : Fin 3 -> F} (hPz : P z = 0)
  statement: addU P Q = 0
  proof: by
  rw [addU]; rw [hPz]; rw [zero_mul]; rw [div_zero]

中文:
引理 addU_of_Z_eq_zero_left
  条件: {P Q : 有限集 3 -> F} (hPz : P z = 0)
  结论: addU P Q = 0
  证明: by
  rw [addU]; rw [hPz]; rw [zero_mul]; rw [div_zero]

Depends on / 依赖: div_zero, zero_mul
-/
lemma addU_of_Z_eq_zero_left {P Q : Fin 3 -> F} (hPz : P z = 0) : addU P Q = 0 := by
  rw [addU]; rw [hPz]; rw [zero_mul]; rw [div_zero]

/--
lemma `addU_of_Z_eq_zero_right` / 引理 `addU_of_Z_eq_zero_right`

English:
lemma addU_of_Z_eq_zero_right
  given: {P Q : Fin 3 -> F} (hQz : Q z = 0)
  statement: addU P Q = 0
  proof: by
  rw [addU]; rw [hQz]; rw [mul_zero <| P z]; rw [div_zero]

中文:
引理 addU_of_Z_eq_zero_right
  条件: {P Q : 有限集 3 -> F} (hQz : Q z = 0)
  结论: addU P Q = 0
  证明: by
  rw [addU]; rw [hQz]; rw [mul_zero <| P z]; rw [div_zero]

Depends on / 依赖: div_zero, mul_zero
-/
lemma addU_of_Z_eq_zero_right {P Q : Fin 3 -> F} (hQz : Q z = 0) : addU P Q = 0 := by
  rw [addU]; rw [hQz]; rw [mul_zero <| P z]; rw [div_zero]

/--
lemma `addU_ne_zero_of_Y_ne` / 引理 `addU_ne_zero_of_Y_ne`

English:
lemma addU_ne_zero_of_Y_ne
  statement: {P Q : Fin 3 -> F} (hPz : P z != 0) (hQz : Q z != 0)
  proof: div_ne_zero (neg_ne_zero.mpr <| pow_ne_zero 3 <| sub_ne_zero.mpr hy) mul_ne_zero hPz hQz

中文:
引理 addU_ne_zero_of_Y_ne
  结论: {P Q : 有限集 3 -> F} (hPz : P z != 0) (hQz : Q z != 0)
  证明: div_ne_zero (neg_ne_zero.mpr <| pow_ne_zero 3 <| sub_ne_zero.mpr hy) mul_ne_zero hPz hQz

Depends on / 依赖: div_ne_zero, mul_ne_zero, neg_ne_zero, neg_ne_zero.mpr, pow_ne_zero, sub_ne_zero, sub_ne_zero.mpr
-/
lemma addU_ne_zero_of_Y_ne {P Q : Fin 3 -> F} (hPz : P z != 0) (hQz : Q z != 0)
    (hy : P y * Q z != Q y * P z) : addU P Q != 0 :=
div_ne_zero (neg_ne_zero.mpr <| pow_ne_zero 3 <| sub_ne_zero.mpr hy) mul_ne_zero hPz hQz

/--
lemma `isUnit_addU_of_Y_ne` / 引理 `isUnit_addU_of_Y_ne`

English:
lemma isUnit_addU_of_Y_ne
  statement: {P Q : Fin 3 -> F} (hPz : P z != 0) (hQz : Q z != 0)
  proof: (addU_ne_zero_of_Y_ne hPz hQz hy).isUnit

中文:
引理 isUnit_addU_of_Y_ne
  结论: {P Q : 有限集 3 -> F} (hPz : P z != 0) (hQz : Q z != 0)
  证明: (addU_ne_zero_of_Y_ne hPz hQz hy).isUnit

Depends on / 依赖: addU_ne_zero_of_Y_ne, isUnit
-/
lemma isUnit_addU_of_Y_ne {P Q : Fin 3 -> F} (hPz : P z != 0) (hQz : Q z != 0)
    (hy : P y * Q z != Q y * P z) : IsUnit (addU P Q) :=
  (addU_ne_zero_of_Y_ne hPz hQz hy).isUnit

variable (W') in
/--
Definition of `addZ` / `addZ` 的定义

English:
definition addZ
  signature: (P Q : Fin 3 -> R)
  body: -3 * P x ^ 2 * Q x * Q z + 3 * P x * Q x ^ 2 * P z + P y ^ 2 * Q z ^ 2 - Q y ^ 2 * P z ^ 2
    + W'.a₁ * P x * P y * Q z ^ 2 - W'.a₁ * Q x * Q y * P z ^ 2 - W'.a₂ * P x ^ 2 * Q z ^ 2
    + W'.a₂ * Q x ^ 2 * P z ^ 2 + W'.a₃ * P y * P z * Q z ^ 2 - W'.a₃ * Q y * P z ^ 2 * Q z
    - W'.a₄ * P x * P z *

中文:
定义 addZ
  签名: (P Q : 有限集 3 -> R)
  定义体: -3 * P x ^ 2 * Q x * Q z + 3 * P x * Q x ^ 2 * P z + P y ^ 2 * Q z ^ 2 - Q y ^ 2 * P z ^ 2
    + W'.a₁ * P x * P y * Q z ^ 2 - W'.a₁ * Q x * Q y * P z ^ 2 - W'.a₂ * P x ^ 2 * Q z ^ 2
    + W'.a₂ * Q x ^ 2 * P z ^ 2 + W'.a₃ * P y * P z * Q z ^ 2 - W'.a₃ * Q y * P z ^ 2 * Q z
    - W'.a₄ * P x * P z *
-/
def addZ (P Q : Fin 3 -> R) : R :=
  -3 * P x ^ 2 * Q x * Q z + 3 * P x * Q x ^ 2 * P z + P y ^ 2 * Q z ^ 2 - Q y ^ 2 * P z ^ 2
    + W'.a₁ * P x * P y * Q z ^ 2 - W'.a₁ * Q x * Q y * P z ^ 2 - W'.a₂ * P x ^ 2 * Q z ^ 2
    + W'.a₂ * Q x ^ 2 * P z ^ 2 + W'.a₃ * P y * P z * Q z ^ 2 - W'.a₃ * Q y * P z ^ 2 * Q z
    - W'.a₄ * P x * P z * Q z ^ 2 + W'.a₄ * Q x * P z ^ 2 * Q z

/--
lemma `addZ_eq'` / 引理 `addZ_eq'`

English:
lemma addZ_eq'
  given: {P Q : Fin 3 -> R} (hP : W'.Equation P) (hQ : W'.Equation Q)
  proof: by
  linear_combination (norm := (rw [addZ]; ring1))
    Q z ^ 3 * (equation_iff _).mp hP - P z ^ 3 * (equation_iff _).mp hQ

中文:
引理 addZ_eq'
  条件: {P Q : 有限集 3 -> R} (hP : W'.方程 P) (hQ : W'.方程 Q)
  证明: by
  linear_combination (norm := (rw [addZ]; ring1))
    Q z ^ 3 * (equation_iff _).mp hP - P z ^ 3 * (equation_iff _).mp hQ

Depends on / 依赖: equation_iff, linear_combination
-/
lemma addZ_eq' {P Q : Fin 3 -> R} (hP : W'.Equation P) (hQ : W'.Equation Q) :
    W'.addZ P Q * (P z * Q z) = (P x * Q z - Q x * P z) ^ 3 := by
  linear_combination (norm := (rw [addZ]; ring1))
    Q z ^ 3 * (equation_iff _).mp hP - P z ^ 3 * (equation_iff _).mp hQ

/--
lemma `addZ_eq` / 引理 `addZ_eq`

English:
lemma addZ_eq
  statement: {P Q : Fin 3 -> F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z != 0)
  proof: by
  rw [← addZ_eq' hP hQ]; rw [mul_div_cancel_right₀ _ <| mul_ne_zero hPz hQz]

中文:
引理 addZ_eq
  结论: {P Q : 有限集 3 -> F} (hP : W.方程 P) (hQ : W.方程 Q) (hPz : P z != 0)
  证明: by
  rw [← addZ_eq' hP hQ]; rw [mul_div_cancel_right₀ _ <| mul_ne_zero hPz hQz]

Depends on / 依赖: addZ_eq, mul_ne_zero
-/
lemma addZ_eq {P Q : Fin 3 -> F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z != 0)
    (hQz : Q z != 0) : W.addZ P Q = (P x * Q z - Q x * P z) ^ 3 / (P z * Q z) := by
  rw [← addZ_eq' hP hQ]; rw [mul_div_cancel_right₀ _ <| mul_ne_zero hPz hQz]

/--
lemma `addZ_smul` / 引理 `addZ_smul`

English:
lemma addZ_smul
  given: (P Q : Fin 3 -> R) (u v : R)
  proof: by
  simp only [addZ, smul_fin3_ext]
  ring1

中文:
引理 addZ_smul
  条件: (P Q : 有限集 3 -> R) (u v : R)
  证明: by
  simp only [addZ, smul_fin3_ext]
  ring1

Depends on / 依赖: smul_fin3_ext
-/
lemma addZ_smul (P Q : Fin 3 -> R) (u v : R) :
    W'.addZ (u • P) (v • Q) = (u * v) ^ 2 * W'.addZ P Q := by
  simp only [addZ, smul_fin3_ext]
  ring1

/--
lemma `addZ_self` / 引理 `addZ_self`

English:
lemma addZ_self
  given: (P : Fin 3 -> R)
  statement: W'.addZ P P = 0
  proof: by
  rw [addZ]
  ring1

中文:
引理 addZ_self
  条件: (P : 有限集 3 -> R)
  结论: W'.addZ P P = 0
  证明: by
  rw [addZ]
  ring1
-/
lemma addZ_self (P : Fin 3 -> R) : W'.addZ P P = 0 := by
  rw [addZ]
  ring1

/--
lemma `addZ_of_Z_eq_zero_left` / 引理 `addZ_of_Z_eq_zero_left`

English:
lemma addZ_of_Z_eq_zero_left
  statement: [NoZeroDivisors R] {P Q : Fin 3 -> R} (hP : W'.Equation P)
  proof: by
  rw [addZ]; rw [hPz]; rw [X_eq_zero_of_Z_eq_zero hP hPz]
  ring1

中文:
引理 addZ_of_Z_eq_zero_left
  结论: [无零因子 R] {P Q : 有限集 3 -> R} (hP : W'.方程 P)
  证明: by
  rw [addZ]; rw [hPz]; rw [X_eq_zero_of_Z_eq_zero hP hPz]
  ring1

Depends on / 依赖: X_eq_zero_of_Z_eq_zero
-/
lemma addZ_of_Z_eq_zero_left [NoZeroDivisors R] {P Q : Fin 3 -> R} (hP : W'.Equation P)
    (hPz : P z = 0) : W'.addZ P Q = P y ^ 2 * Q z * Q z := by
  rw [addZ]; rw [hPz]; rw [X_eq_zero_of_Z_eq_zero hP hPz]
  ring1

/--
lemma `addZ_of_Z_eq_zero_right` / 引理 `addZ_of_Z_eq_zero_right`

English:
lemma addZ_of_Z_eq_zero_right
  statement: [NoZeroDivisors R] {P Q : Fin 3 -> R} (hQ : W'.Equation Q)
  proof: by
  rw [addZ]; rw [hQz]; rw [X_eq_zero_of_Z_eq_zero hQ hQz]
  ring1

中文:
引理 addZ_of_Z_eq_zero_right
  结论: [无零因子 R] {P Q : 有限集 3 -> R} (hQ : W'.方程 Q)
  证明: by
  rw [addZ]; rw [hQz]; rw [X_eq_zero_of_Z_eq_zero hQ hQz]
  ring1

Depends on / 依赖: X_eq_zero_of_Z_eq_zero
-/
lemma addZ_of_Z_eq_zero_right [NoZeroDivisors R] {P Q : Fin 3 -> R} (hQ : W'.Equation Q)
    (hQz : Q z = 0) : W'.addZ P Q = -(Q y ^ 2 * P z) * P z := by
  rw [addZ]; rw [hQz]; rw [X_eq_zero_of_Z_eq_zero hQ hQz]
  ring1

/--
lemma `addZ_of_X_eq` / 引理 `addZ_of_X_eq`

English:
lemma addZ_of_X_eq
  statement: [NoZeroDivisors R] {P Q : Fin 3 -> R} (hP : W'.Equation P) (hQ : W'.Equation Q)
  proof: by
apply eq_zero_of_ne_zero_of_mul_right_eq_zero mul_ne_zero hPz hQz
  rw [addZ_eq' hP hQ]; rw [hx]; rw [sub_self]; rw [zero_pow three_ne_zero]

中文:
引理 addZ_of_X_eq
  结论: [无零因子 R] {P Q : 有限集 3 -> R} (hP : W'.方程 P) (hQ : W'.方程 Q)
  证明: by
apply eq_zero_of_ne_zero_of_mul_right_eq_zero mul_ne_zero hPz hQz
  rw [addZ_eq' hP hQ]; rw [hx]; rw [sub_self]; rw [zero_pow three_ne_zero]

Depends on / 依赖: addZ_eq, eq_zero_of_ne_zero_of_mul_right_eq_zero, mul_ne_zero, sub_self, three_ne_zero, zero_pow
-/
lemma addZ_of_X_eq [NoZeroDivisors R] {P Q : Fin 3 -> R} (hP : W'.Equation P) (hQ : W'.Equation Q)
    (hPz : P z != 0) (hQz : Q z != 0) (hx : P x * Q z = Q x * P z) : W'.addZ P Q = 0 := by
apply eq_zero_of_ne_zero_of_mul_right_eq_zero mul_ne_zero hPz hQz
  rw [addZ_eq' hP hQ]; rw [hx]; rw [sub_self]; rw [zero_pow three_ne_zero]

/--
lemma `addZ_ne_zero_of_X_ne` / 引理 `addZ_ne_zero_of_X_ne`

English:
lemma addZ_ne_zero_of_X_ne
  statement: [NoZeroDivisors R] {P Q : Fin 3 -> R} (hP : W'.Equation P)
  proof: addZ_eq' hP hQ ▸ left_ne_zero_of_mul pow_ne_zero 3 sub_ne_zero.mpr hx

中文:
引理 addZ_ne_zero_of_X_ne
  结论: [无零因子 R] {P Q : 有限集 3 -> R} (hP : W'.方程 P)
  证明: addZ_eq' hP hQ ▸ left_ne_zero_of_mul pow_ne_zero 3 sub_ne_zero.mpr hx

Depends on / 依赖: addZ_eq, left_ne_zero_of_mul, pow_ne_zero, sub_ne_zero, sub_ne_zero.mpr
-/
lemma addZ_ne_zero_of_X_ne [NoZeroDivisors R] {P Q : Fin 3 -> R} (hP : W'.Equation P)
    (hQ : W'.Equation Q) (hx : P x * Q z != Q x * P z) : W'.addZ P Q != 0 :=
addZ_eq' hP hQ ▸ left_ne_zero_of_mul pow_ne_zero 3 sub_ne_zero.mpr hx

/--
lemma `isUnit_addZ_of_X_ne` / 引理 `isUnit_addZ_of_X_ne`

English:
lemma isUnit_addZ_of_X_ne
  statement: {P Q : Fin 3 -> F} (hP : W.Equation P) (hQ : W.Equation Q)
  proof: (addZ_ne_zero_of_X_ne hP hQ hx).isUnit

中文:
引理 isUnit_addZ_of_X_ne
  结论: {P Q : 有限集 3 -> F} (hP : W.方程 P) (hQ : W.方程 Q)
  证明: (addZ_ne_zero_of_X_ne hP hQ hx).isUnit

Depends on / 依赖: addZ_ne_zero_of_X_ne, isUnit
-/
lemma isUnit_addZ_of_X_ne {P Q : Fin 3 -> F} (hP : W.Equation P) (hQ : W.Equation Q)
(hx : P x * Q z != Q x * P z) : IsUnit W.addZ P Q :=
  (addZ_ne_zero_of_X_ne hP hQ hx).isUnit

/--
lemma `toAffine_slope_of_ne` / 引理 `toAffine_slope_of_ne`

English:
lemma toAffine_slope_of_ne
  statement: [DecidableEq F] {P Q : Fin 3 -> F} (hPz : P z != 0) (hQz : Q z != 0)
  proof: by
  simp [field, Affine.slope_of_X_ne <| by rwa [ne_eq, ← X_eq_iff hPz hQz]]

中文:
引理 toAffine_slope_of_ne
  结论: [DecidableEq F] {P Q : 有限集 3 -> F} (hPz : P z != 0) (hQz : Q z != 0)
  证明: by
  simp [field, Affine.slope_of_X_ne <| by rwa [ne_eq, ← X_eq_iff hPz hQz]]
-/
private lemma toAffine_slope_of_ne [DecidableEq F] {P Q : Fin 3 -> F} (hPz : P z != 0) (hQz : Q z != 0)
    (hx : P x * Q z != Q x * P z) :
    W.toAffine.slope (P x / P z) (Q x / Q z) (P y / P z) (Q y / Q z) =
      (P y * Q z - Q y * P z) / (P x * Q z - Q x * P z) := by
  simp [field, Affine.slope_of_X_ne <| by rwa [ne_eq, ← X_eq_iff hPz hQz]]

variable (W') in
/--
Definition of `addX` / `addX` 的定义

English:
definition addX
  signature: (P Q : Fin 3 -> R)
  body: -P x * Q y ^ 2 * P z + Q x * P y ^ 2 * Q z - 2 * P x * P y * Q y * Q z + 2 * Q x * P y * Q y * P z
    - W'.a₁ * P x ^ 2 * Q y * Q z + W'.a₁ * Q x ^ 2 * P y * P z + W'.a₂ * P x ^ 2 * Q x * Q z
    - W'.a₂ * P x * Q x ^ 2 * P z - W'.a₃ * P x * P y * Q z ^ 2 + W'.a₃ * Q x * Q y * P z ^ 2
    - 2 * W'.

中文:
定义 addX
  签名: (P Q : 有限集 3 -> R)
  定义体: -P x * Q y ^ 2 * P z + Q x * P y ^ 2 * Q z - 2 * P x * P y * Q y * Q z + 2 * Q x * P y * Q y * P z
    - W'.a₁ * P x ^ 2 * Q y * Q z + W'.a₁ * Q x ^ 2 * P y * P z + W'.a₂ * P x ^ 2 * Q x * Q z
    - W'.a₂ * P x * Q x ^ 2 * P z - W'.a₃ * P x * P y * Q z ^ 2 + W'.a₃ * Q x * Q y * P z ^ 2
    - 2 * W'.
-/
def addX (P Q : Fin 3 -> R) : R :=
  -P x * Q y ^ 2 * P z + Q x * P y ^ 2 * Q z - 2 * P x * P y * Q y * Q z + 2 * Q x * P y * Q y * P z
    - W'.a₁ * P x ^ 2 * Q y * Q z + W'.a₁ * Q x ^ 2 * P y * P z + W'.a₂ * P x ^ 2 * Q x * Q z
    - W'.a₂ * P x * Q x ^ 2 * P z - W'.a₃ * P x * P y * Q z ^ 2 + W'.a₃ * Q x * Q y * P z ^ 2
    - 2 * W'.a₃ * P x * Q y * P z * Q z + 2 * W'.a₃ * Q x * P y * P z * Q z
    + W'.a₄ * P x ^ 2 * Q z ^ 2 - W'.a₄ * Q x ^ 2 * P z ^ 2 + 3 * W'.a₆ * P x * P z * Q z ^ 2
    - 3 * W'.a₆ * Q x * P z ^ 2 * Q z

/--
lemma `addX_eq'` / 引理 `addX_eq'`

English:
lemma addX_eq'
  given: {P Q : Fin 3 -> R} (hP : W'.Equation P) (hQ : W'.Equation Q)
  proof: by
  linear_combination (norm := (rw [addX]; ring1))
    (2 * Q x * P z * Q z ^ 3 - P x * Q z ^ 4) * (equation_iff _).mp hP
      + (Q x * P z ^ 4 - 2 * P x * P z ^ 3 * Q z) * (equation_iff _).mp hQ

中文:
引理 addX_eq'
  条件: {P Q : 有限集 3 -> R} (hP : W'.方程 P) (hQ : W'.方程 Q)
  证明: by
  linear_combination (norm := (rw [addX]; ring1))
    (2 * Q x * P z * Q z ^ 3 - P x * Q z ^ 4) * (equation_iff _).mp hP
      + (Q x * P z ^ 4 - 2 * P x * P z ^ 3 * Q z) * (equation_iff _).mp hQ

Depends on / 依赖: equation_iff, linear_combination
-/
lemma addX_eq' {P Q : Fin 3 -> R} (hP : W'.Equation P) (hQ : W'.Equation Q) :
    W'.addX P Q * (P z * Q z) ^ 2 =
      ((P y * Q z - Q y * P z) ^ 2 * P z * Q z
        + W'.a₁ * (P y * Q z - Q y * P z) * P z * Q z * (P x * Q z - Q x * P z)
        - W'.a₂ * P z * Q z * (P x * Q z - Q x * P z) ^ 2 - P x * Q z * (P x * Q z - Q x * P z) ^ 2
        - Q x * P z * (P x * Q z - Q x * P z) ^ 2) * (P x * Q z - Q x * P z) := by
  linear_combination (norm := (rw [addX]; ring1))
    (2 * Q x * P z * Q z ^ 3 - P x * Q z ^ 4) * (equation_iff _).mp hP
      + (Q x * P z ^ 4 - 2 * P x * P z ^ 3 * Q z) * (equation_iff _).mp hQ

/--
lemma `addX_eq` / 引理 `addX_eq`

English:
lemma addX_eq
  statement: {P Q : Fin 3 -> F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z != 0)
  proof: by
  rw [← addX_eq' hP hQ]; rw [mul_div_cancel_right₀ _ <| pow_ne_zero 2 <| mul_ne_zero hPz hQz]

中文:
引理 addX_eq
  结论: {P Q : 有限集 3 -> F} (hP : W.方程 P) (hQ : W.方程 Q) (hPz : P z != 0)
  证明: by
  rw [← addX_eq' hP hQ]; rw [mul_div_cancel_right₀ _ <| pow_ne_zero 2 <| mul_ne_zero hPz hQz]

Depends on / 依赖: addX_eq, mul_ne_zero, pow_ne_zero
-/
lemma addX_eq {P Q : Fin 3 -> F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z != 0)
    (hQz : Q z != 0) : W.addX P Q =
      ((P y * Q z - Q y * P z) ^ 2 * P z * Q z
        + W.a₁ * (P y * Q z - Q y * P z) * P z * Q z * (P x * Q z - Q x * P z)
        - W.a₂ * P z * Q z * (P x * Q z - Q x * P z) ^ 2 - P x * Q z * (P x * Q z - Q x * P z) ^ 2
        - Q x * P z * (P x * Q z - Q x * P z) ^ 2) * (P x * Q z - Q x * P z) / (P z * Q z) ^ 2 := by
  rw [← addX_eq' hP hQ]; rw [mul_div_cancel_right₀ _ <| pow_ne_zero 2 <| mul_ne_zero hPz hQz]

/--
lemma `addX_smul` / 引理 `addX_smul`

English:
lemma addX_smul
  given: (P Q : Fin 3 -> R) (u v : R)
  proof: by
  simp only [addX, smul_fin3_ext]
  ring1

中文:
引理 addX_smul
  条件: (P Q : 有限集 3 -> R) (u v : R)
  证明: by
  simp only [addX, smul_fin3_ext]
  ring1

Depends on / 依赖: smul_fin3_ext
-/
lemma addX_smul (P Q : Fin 3 -> R) (u v : R) :
    W'.addX (u • P) (v • Q) = (u * v) ^ 2 * W'.addX P Q := by
  simp only [addX, smul_fin3_ext]
  ring1

/--
lemma `addX_self` / 引理 `addX_self`

English:
lemma addX_self
  given: (P : Fin 3 -> R)
  statement: W'.addX P P = 0
  proof: by
  rw [addX]
  ring1

中文:
引理 addX_self
  条件: (P : 有限集 3 -> R)
  结论: W'.addX P P = 0
  证明: by
  rw [addX]
  ring1
-/
lemma addX_self (P : Fin 3 -> R) : W'.addX P P = 0 := by
  rw [addX]
  ring1

/--
lemma `addX_of_Z_eq_zero_left` / 引理 `addX_of_Z_eq_zero_left`

English:
lemma addX_of_Z_eq_zero_left
  statement: [NoZeroDivisors R] {P Q : Fin 3 -> R} (hP : W'.Equation P)
  proof: by
  rw [addX]; rw [hPz]; rw [X_eq_zero_of_Z_eq_zero hP hPz]
  ring1

中文:
引理 addX_of_Z_eq_zero_left
  结论: [无零因子 R] {P Q : 有限集 3 -> R} (hP : W'.方程 P)
  证明: by
  rw [addX]; rw [hPz]; rw [X_eq_zero_of_Z_eq_zero hP hPz]
  ring1

Depends on / 依赖: X_eq_zero_of_Z_eq_zero
-/
lemma addX_of_Z_eq_zero_left [NoZeroDivisors R] {P Q : Fin 3 -> R} (hP : W'.Equation P)
    (hPz : P z = 0) : W'.addX P Q = P y ^ 2 * Q z * Q x := by
  rw [addX]; rw [hPz]; rw [X_eq_zero_of_Z_eq_zero hP hPz]
  ring1

/--
lemma `addX_of_Z_eq_zero_right` / 引理 `addX_of_Z_eq_zero_right`

English:
lemma addX_of_Z_eq_zero_right
  statement: [NoZeroDivisors R] {P Q : Fin 3 -> R} (hQ : W'.Equation Q)
  proof: by
  rw [addX]; rw [hQz]; rw [X_eq_zero_of_Z_eq_zero hQ hQz]
  ring1

中文:
引理 addX_of_Z_eq_zero_right
  结论: [无零因子 R] {P Q : 有限集 3 -> R} (hQ : W'.方程 Q)
  证明: by
  rw [addX]; rw [hQz]; rw [X_eq_zero_of_Z_eq_zero hQ hQz]
  ring1

Depends on / 依赖: X_eq_zero_of_Z_eq_zero
-/
lemma addX_of_Z_eq_zero_right [NoZeroDivisors R] {P Q : Fin 3 -> R} (hQ : W'.Equation Q)
    (hQz : Q z = 0) : W'.addX P Q = -(Q y ^ 2 * P z) * P x := by
  rw [addX]; rw [hQz]; rw [X_eq_zero_of_Z_eq_zero hQ hQz]
  ring1

/--
lemma `addX_of_X_eq` / 引理 `addX_of_X_eq`

English:
lemma addX_of_X_eq
  statement: [NoZeroDivisors R] {P Q : Fin 3 -> R} (hP : W'.Equation P) (hQ : W'.Equation Q)
  proof: by
apply eq_zero_of_ne_zero_of_mul_right_eq_zero pow_ne_zero 2 mul_ne_zero hPz hQz
  rw [addX_eq' hP hQ]; rw [hx]
  ring1

中文:
引理 addX_of_X_eq
  结论: [无零因子 R] {P Q : 有限集 3 -> R} (hP : W'.方程 P) (hQ : W'.方程 Q)
  证明: by
apply eq_zero_of_ne_zero_of_mul_right_eq_zero pow_ne_zero 2 mul_ne_zero hPz hQz
  rw [addX_eq' hP hQ]; rw [hx]
  ring1

Depends on / 依赖: addX_eq, eq_zero_of_ne_zero_of_mul_right_eq_zero, mul_ne_zero, pow_ne_zero
-/
lemma addX_of_X_eq [NoZeroDivisors R] {P Q : Fin 3 -> R} (hP : W'.Equation P) (hQ : W'.Equation Q)
    (hPz : P z != 0) (hQz : Q z != 0) (hx : P x * Q z = Q x * P z) : W'.addX P Q = 0 := by
apply eq_zero_of_ne_zero_of_mul_right_eq_zero pow_ne_zero 2 mul_ne_zero hPz hQz
  rw [addX_eq' hP hQ]; rw [hx]
  ring1

/--
lemma `toAffine_addX_of_ne` / 引理 `toAffine_addX_of_ne`

English:
lemma toAffine_addX_of_ne
  statement: {P Q : Fin 3 -> F} (hPz : P z != 0) (hQz : Q z != 0) {n d : F}
  proof: by
  simp [field]

中文:
引理 toAffine_addX_of_ne
  结论: {P Q : 有限集 3 -> F} (hPz : P z != 0) (hQz : Q z != 0) {n d : F}
  证明: by
  simp [field]
-/
private lemma toAffine_addX_of_ne {P Q : Fin 3 -> F} (hPz : P z != 0) (hQz : Q z != 0) {n d : F}
    (hd : d != 0) : W.toAffine.addX (P x / P z) (Q x / Q z) (n / d) =
      (n ^ 2 * P z * Q z + W.a₁ * n * P z * Q z * d - W.a₂ * P z * Q z * d ^ 2 - P x * Q z * d ^ 2
        - Q x * P z * d ^ 2) * d / (P z * Q z) ^ 2 / (d ^ 3 / (P z * Q z)) := by
  simp [field]

/--
lemma `addX_of_Z_ne_zero` / 引理 `addX_of_Z_ne_zero`

English:
lemma addX_of_Z_ne_zero
  statement: [DecidableEq F] {P Q : Fin 3 -> F} (hP : W.Equation P) (hQ : W.Equation Q)
  proof: by
  rw [addX_eq hP hQ hPz hQz]; rw [addZ_eq hP hQ hPz hQz]; rw [toAffine_slope_of_ne hPz hQz hx]; rw [toAffine_addX_of_ne hPz hQz sub_ne_zero.mpr hx]

中文:
引理 addX_of_Z_ne_zero
  结论: [DecidableEq F] {P Q : 有限集 3 -> F} (hP : W.方程 P) (hQ : W.方程 Q)
  证明: by
  rw [addX_eq hP hQ hPz hQz]; rw [addZ_eq hP hQ hPz hQz]; rw [toAffine_slope_of_ne hPz hQz hx]; rw [toAffine_addX_of_ne hPz hQz sub_ne_zero.mpr hx]

Depends on / 依赖: addX_eq, addZ_eq, sub_ne_zero, sub_ne_zero.mpr, toAffine_addX_of_ne, toAffine_slope_of_ne
-/
lemma addX_of_Z_ne_zero [DecidableEq F] {P Q : Fin 3 -> F} (hP : W.Equation P) (hQ : W.Equation Q)
    (hPz : P z != 0) (hQz : Q z != 0) (hx : P x * Q z != Q x * P z) : W.addX P Q / W.addZ P Q =
    W.toAffine.addX (P x / P z) (Q x / Q z)
      (W.toAffine.slope (P x / P z) (Q x / Q z) (P y / P z) (Q y / Q z)) := by
  rw [addX_eq hP hQ hPz hQz]; rw [addZ_eq hP hQ hPz hQz]; rw [toAffine_slope_of_ne hPz hQz hx]; rw [toAffine_addX_of_ne hPz hQz sub_ne_zero.mpr hx]

variable (W') in
/--
Definition of `negAddY` / `negAddY` 的定义

English:
definition negAddY
  signature: (P Q : Fin 3 -> R)
  body: -3 * P x ^ 2 * Q x * Q y + 3 * P x * Q x ^ 2 * P y - P y ^ 2 * Q y * Q z + P y * Q y ^ 2 * P z
    + W'.a₁ * P x * Q y ^ 2 * P z - W'.a₁ * Q x * P y ^ 2 * Q z - W'.a₂ * P x ^ 2 * Q y * Q z
    + W'.a₂ * Q x ^ 2 * P y * P z + 2 * W'.a₂ * P x * Q x * P y * Q z
    - 2 * W'.a₂ * P x * Q x * Q y * P z -

中文:
定义 negAddY
  签名: (P Q : 有限集 3 -> R)
  定义体: -3 * P x ^ 2 * Q x * Q y + 3 * P x * Q x ^ 2 * P y - P y ^ 2 * Q y * Q z + P y * Q y ^ 2 * P z
    + W'.a₁ * P x * Q y ^ 2 * P z - W'.a₁ * Q x * P y ^ 2 * Q z - W'.a₂ * P x ^ 2 * Q y * Q z
    + W'.a₂ * Q x ^ 2 * P y * P z + 2 * W'.a₂ * P x * Q x * P y * Q z
    - 2 * W'.a₂ * P x * Q x * Q y * P z -
-/
def negAddY (P Q : Fin 3 -> R) : R :=
  -3 * P x ^ 2 * Q x * Q y + 3 * P x * Q x ^ 2 * P y - P y ^ 2 * Q y * Q z + P y * Q y ^ 2 * P z
    + W'.a₁ * P x * Q y ^ 2 * P z - W'.a₁ * Q x * P y ^ 2 * Q z - W'.a₂ * P x ^ 2 * Q y * Q z
    + W'.a₂ * Q x ^ 2 * P y * P z + 2 * W'.a₂ * P x * Q x * P y * Q z
    - 2 * W'.a₂ * P x * Q x * Q y * P z - W'.a₃ * P y ^ 2 * Q z ^ 2 + W'.a₃ * Q y ^ 2 * P z ^ 2
    + W'.a₄ * P x * P y * Q z ^ 2 - 2 * W'.a₄ * P x * Q y * P z * Q z
    + 2 * W'.a₄ * Q x * P y * P z * Q z - W'.a₄ * Q x * Q y * P z ^ 2
    + 3 * W'.a₆ * P y * P z * Q z ^ 2 - 3 * W'.a₆ * Q y * P z ^ 2 * Q z

/--
lemma `negAddY_eq'` / 引理 `negAddY_eq'`

English:
lemma negAddY_eq'
  given: {P Q : Fin 3 -> R} (hP : W'.Equation P) (hQ : W'.Equation Q)
  proof: by
  linear_combination (norm := (rw [negAddY]; ring1))
    (2 * Q y * P z * Q z ^ 3 - P y * Q z ^ 4) * (equation_iff _).mp hP
      + (Q y * P z ^ 4 - 2 * P y * P z ^ 3 * Q z) * (equation_iff _).mp hQ

中文:
引理 negAddY_eq'
  条件: {P Q : 有限集 3 -> R} (hP : W'.方程 P) (hQ : W'.方程 Q)
  证明: by
  linear_combination (norm := (rw [negAddY]; ring1))
    (2 * Q y * P z * Q z ^ 3 - P y * Q z ^ 4) * (equation_iff _).mp hP
      + (Q y * P z ^ 4 - 2 * P y * P z ^ 3 * Q z) * (equation_iff _).mp hQ

Depends on / 依赖: equation_iff, linear_combination, negAddY
-/
lemma negAddY_eq' {P Q : Fin 3 -> R} (hP : W'.Equation P) (hQ : W'.Equation Q) :
    W'.negAddY P Q * (P z * Q z) ^ 2 =
      (P y * Q z - Q y * P z) * ((P y * Q z - Q y * P z) ^ 2 * P z * Q z
        + W'.a₁ * (P y * Q z - Q y * P z) * P z * Q z * (P x * Q z - Q x * P z)
        - W'.a₂ * P z * Q z * (P x * Q z - Q x * P z) ^ 2 - P x * Q z * (P x * Q z - Q x * P z) ^ 2
        - Q x * P z * (P x * Q z - Q x * P z) ^ 2 - P x * Q z * (P x * Q z - Q x * P z) ^ 2)
        + P y * Q z * (P x * Q z - Q x * P z) ^ 3 := by
  linear_combination (norm := (rw [negAddY]; ring1))
    (2 * Q y * P z * Q z ^ 3 - P y * Q z ^ 4) * (equation_iff _).mp hP
      + (Q y * P z ^ 4 - 2 * P y * P z ^ 3 * Q z) * (equation_iff _).mp hQ

/--
lemma `negAddY_eq` / 引理 `negAddY_eq`

English:
lemma negAddY_eq
  statement: {P Q : Fin 3 -> F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z != 0)
  proof: by
  rw [← negAddY_eq' hP hQ]; rw [mul_div_cancel_right₀ _ <| pow_ne_zero 2 <| mul_ne_zero hPz hQz]

中文:
引理 negAddY_eq
  结论: {P Q : 有限集 3 -> F} (hP : W.方程 P) (hQ : W.方程 Q) (hPz : P z != 0)
  证明: by
  rw [← negAddY_eq' hP hQ]; rw [mul_div_cancel_right₀ _ <| pow_ne_zero 2 <| mul_ne_zero hPz hQz]

Depends on / 依赖: mul_ne_zero, negAddY_eq, pow_ne_zero
-/
lemma negAddY_eq {P Q : Fin 3 -> F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z != 0)
    (hQz : Q z != 0) : W.negAddY P Q =
      ((P y * Q z - Q y * P z) * ((P y * Q z - Q y * P z) ^ 2 * P z * Q z
        + W.a₁ * (P y * Q z - Q y * P z) * P z * Q z * (P x * Q z - Q x * P z)
        - W.a₂ * P z * Q z * (P x * Q z - Q x * P z) ^ 2 - P x * Q z * (P x * Q z - Q x * P z) ^ 2
        - Q x * P z * (P x * Q z - Q x * P z) ^ 2 - P x * Q z * (P x * Q z - Q x * P z) ^ 2)
        + P y * Q z * (P x * Q z - Q x * P z) ^ 3) / (P z * Q z) ^ 2 := by
  rw [← negAddY_eq' hP hQ]; rw [mul_div_cancel_right₀ _ <| pow_ne_zero 2 <| mul_ne_zero hPz hQz]

/--
lemma `negAddY_smul` / 引理 `negAddY_smul`

English:
lemma negAddY_smul
  given: (P Q : Fin 3 -> R) (u v : R)
  proof: by
  simp only [negAddY, smul_fin3_ext]
  ring1

中文:
引理 negAddY_smul
  条件: (P Q : 有限集 3 -> R) (u v : R)
  证明: by
  simp only [negAddY, smul_fin3_ext]
  ring1

Depends on / 依赖: negAddY, smul_fin3_ext
-/
lemma negAddY_smul (P Q : Fin 3 -> R) (u v : R) :
    W'.negAddY (u • P) (v • Q) = (u * v) ^ 2 * W'.negAddY P Q := by
  simp only [negAddY, smul_fin3_ext]
  ring1

/--
lemma `negAddY_self` / 引理 `negAddY_self`

English:
lemma negAddY_self
  given: (P : Fin 3 -> R)
  statement: W'.negAddY P P = 0
  proof: by
  rw [negAddY]
  ring1

中文:
引理 negAddY_self
  条件: (P : 有限集 3 -> R)
  结论: W'.negAddY P P = 0
  证明: by
  rw [negAddY]
  ring1

Depends on / 依赖: negAddY
-/
lemma negAddY_self (P : Fin 3 -> R) : W'.negAddY P P = 0 := by
  rw [negAddY]
  ring1

/--
lemma `negAddY_of_Z_eq_zero_left` / 引理 `negAddY_of_Z_eq_zero_left`

English:
lemma negAddY_of_Z_eq_zero_left
  statement: [NoZeroDivisors R] {P Q : Fin 3 -> R} (hP : W'.Equation P)
  proof: by
  rw [negAddY]; rw [hPz]; rw [X_eq_zero_of_Z_eq_zero hP hPz]; rw [negY]
  ring1

中文:
引理 negAddY_of_Z_eq_zero_left
  结论: [无零因子 R] {P Q : 有限集 3 -> R} (hP : W'.方程 P)
  证明: by
  rw [negAddY]; rw [hPz]; rw [X_eq_zero_of_Z_eq_zero hP hPz]; rw [negY]
  ring1

Depends on / 依赖: X_eq_zero_of_Z_eq_zero, negAddY
-/
lemma negAddY_of_Z_eq_zero_left [NoZeroDivisors R] {P Q : Fin 3 -> R} (hP : W'.Equation P)
    (hPz : P z = 0) : W'.negAddY P Q = P y ^ 2 * Q z * W'.negY Q := by
  rw [negAddY]; rw [hPz]; rw [X_eq_zero_of_Z_eq_zero hP hPz]; rw [negY]
  ring1

/--
lemma `negAddY_of_Z_eq_zero_right` / 引理 `negAddY_of_Z_eq_zero_right`

English:
lemma negAddY_of_Z_eq_zero_right
  statement: [NoZeroDivisors R] {P Q : Fin 3 -> R} (hQ : W'.Equation Q)
  proof: by
  rw [negAddY]; rw [hQz]; rw [X_eq_zero_of_Z_eq_zero hQ hQz]; rw [negY]
  ring1

中文:
引理 negAddY_of_Z_eq_zero_right
  结论: [无零因子 R] {P Q : 有限集 3 -> R} (hQ : W'.方程 Q)
  证明: by
  rw [negAddY]; rw [hQz]; rw [X_eq_zero_of_Z_eq_zero hQ hQz]; rw [negY]
  ring1

Depends on / 依赖: X_eq_zero_of_Z_eq_zero, negAddY
-/
lemma negAddY_of_Z_eq_zero_right [NoZeroDivisors R] {P Q : Fin 3 -> R} (hQ : W'.Equation Q)
    (hQz : Q z = 0) : W'.negAddY P Q = -(Q y ^ 2 * P z) * W'.negY P := by
  rw [negAddY]; rw [hQz]; rw [X_eq_zero_of_Z_eq_zero hQ hQz]; rw [negY]
  ring1

/--
lemma `negAddY_of_X_eq'` / 引理 `negAddY_of_X_eq'`

English:
lemma negAddY_of_X_eq'
  statement: {P Q : Fin 3 -> R} (hP : W'.Equation P) (hQ : W'.Equation Q)
  proof: by
  rw [negAddY_eq' hP hQ]; rw [hx]
  ring1

中文:
引理 negAddY_of_X_eq'
  结论: {P Q : 有限集 3 -> R} (hP : W'.方程 P) (hQ : W'.方程 Q)
  证明: by
  rw [negAddY_eq' hP hQ]; rw [hx]
  ring1

Depends on / 依赖: negAddY_eq
-/
lemma negAddY_of_X_eq' {P Q : Fin 3 -> R} (hP : W'.Equation P) (hQ : W'.Equation Q)
    (hx : P x * Q z = Q x * P z) :
    W'.negAddY P Q * (P z * Q z) ^ 2 = (P y * Q z - Q y * P z) ^ 3 * (P z * Q z) := by
  rw [negAddY_eq' hP hQ]; rw [hx]
  ring1

/--
lemma `negAddY_of_X_eq` / 引理 `negAddY_of_X_eq`

English:
lemma negAddY_of_X_eq
  statement: {P Q : Fin 3 -> F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z != 0)
  proof: by
  rw [addU]; rw [neg_div]; rw [neg_neg]; rw [← mul_div_mul_right _ _ <| mul_ne_zero hPz hQz]; rw [← negAddY_of_X_eq' hP hQ hx]; rw [← sq]; rw [mul_div_cancel_right₀ _ pow_ne_zero 2 mul_ne_zero hPz hQz]

中文:
引理 negAddY_of_X_eq
  结论: {P Q : 有限集 3 -> F} (hP : W.方程 P) (hQ : W.方程 Q) (hPz : P z != 0)
  证明: by
  rw [addU]; rw [neg_div]; rw [neg_neg]; rw [← mul_div_mul_right _ _ <| mul_ne_zero hPz hQz]; rw [← negAddY_of_X_eq' hP hQ hx]; rw [← sq]; rw [mul_div_cancel_right₀ _ pow_ne_zero 2 mul_ne_zero hPz hQz]

Depends on / 依赖: mul_div_mul_right, mul_ne_zero, negAddY_of_X_eq, neg_div, neg_neg, pow_ne_zero
-/
lemma negAddY_of_X_eq {P Q : Fin 3 -> F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z != 0)
    (hQz : Q z != 0) (hx : P x * Q z = Q x * P z) : W.negAddY P Q = -addU P Q := by
  rw [addU]; rw [neg_div]; rw [neg_neg]; rw [← mul_div_mul_right _ _ <| mul_ne_zero hPz hQz]; rw [← negAddY_of_X_eq' hP hQ hx]; rw [← sq]; rw [mul_div_cancel_right₀ _ pow_ne_zero 2 mul_ne_zero hPz hQz]

/--
lemma `toAffine_negAddY_of_ne` / 引理 `toAffine_negAddY_of_ne`

English:
lemma toAffine_negAddY_of_ne
  statement: {P Q : Fin 3 -> F} (hPz : P z != 0) (hQz : Q z != 0) {n d : F}
  proof: by
  rw [Affine.negAddY]; rw [toAffine_addX_of_ne hPz hQz hd]
  simp [field]

中文:
引理 toAffine_negAddY_of_ne
  结论: {P Q : 有限集 3 -> F} (hPz : P z != 0) (hQz : Q z != 0) {n d : F}
  证明: by
  rw [Affine.negAddY]; rw [toAffine_addX_of_ne hPz hQz hd]
  simp [field]
-/
private lemma toAffine_negAddY_of_ne {P Q : Fin 3 -> F} (hPz : P z != 0) (hQz : Q z != 0) {n d : F}
    (hd : d != 0) : W.toAffine.negAddY (P x / P z) (Q x / Q z) (P y / P z) (n / d) =
      (n * (n ^ 2 * P z * Q z + W.a₁ * n * P z * Q z * d - W.a₂ * P z * Q z * d ^ 2
        - P x * Q z * d ^ 2 - Q x * P z * d ^ 2 - P x * Q z * d ^ 2) + P y * Q z * d ^ 3)
        / (P z * Q z) ^ 2 / (d ^ 3 / (P z * Q z)) := by
  rw [Affine.negAddY]; rw [toAffine_addX_of_ne hPz hQz hd]
  simp [field]

/--
lemma `negAddY_of_Z_ne_zero` / 引理 `negAddY_of_Z_ne_zero`

English:
lemma negAddY_of_Z_ne_zero
  statement: [DecidableEq F] {P Q : Fin 3 -> F} (hP : W.Equation P) (hQ : W.Equation Q)
  proof: by
  rw [negAddY_eq hP hQ hPz hQz]; rw [addZ_eq hP hQ hPz hQz]; rw [toAffine_slope_of_ne hPz hQz hx]; rw [toAffine_negAddY_of_ne hPz hQz sub_ne_zero.mpr hx]

中文:
引理 negAddY_of_Z_ne_zero
  结论: [DecidableEq F] {P Q : 有限集 3 -> F} (hP : W.方程 P) (hQ : W.方程 Q)
  证明: by
  rw [negAddY_eq hP hQ hPz hQz]; rw [addZ_eq hP hQ hPz hQz]; rw [toAffine_slope_of_ne hPz hQz hx]; rw [toAffine_negAddY_of_ne hPz hQz sub_ne_zero.mpr hx]

Depends on / 依赖: addZ_eq, negAddY_eq, sub_ne_zero, sub_ne_zero.mpr, toAffine_negAddY_of_ne, toAffine_slope_of_ne
-/
lemma negAddY_of_Z_ne_zero [DecidableEq F] {P Q : Fin 3 -> F} (hP : W.Equation P) (hQ : W.Equation Q)
    (hPz : P z != 0) (hQz : Q z != 0) (hx : P x * Q z != Q x * P z) : W.negAddY P Q / W.addZ P Q =
      W.toAffine.negAddY (P x / P z) (Q x / Q z) (P y / P z)
        (W.toAffine.slope (P x / P z) (Q x / Q z) (P y / P z) (Q y / Q z)) := by
  rw [negAddY_eq hP hQ hPz hQz]; rw [addZ_eq hP hQ hPz hQz]; rw [toAffine_slope_of_ne hPz hQz hx]; rw [toAffine_negAddY_of_ne hPz hQz sub_ne_zero.mpr hx]

variable (W') in
/--
Definition of `addY` / `addY` 的定义

English:
definition addY
  signature: (P Q : Fin 3 -> R)
  body: W'.negY ![W'.addX P Q, W'.negAddY P Q, W'.addZ P Q]

中文:
定义 addY
  签名: (P Q : 有限集 3 -> R)
  定义体: W'.negY ![W'.addX P Q, W'.negAddY P Q, W'.addZ P Q]

Depends on / 依赖: negAddY
-/
def addY (P Q : Fin 3 -> R) : R :=
  W'.negY ![W'.addX P Q, W'.negAddY P Q, W'.addZ P Q]

/--
lemma `addY_smul` / 引理 `addY_smul`

English:
lemma addY_smul
  given: (P Q : Fin 3 -> R) (u v : R)
  proof: by
  simp only [addY, negY_eq, negAddY_smul, addX_smul, addZ_smul]
  ring1

中文:
引理 addY_smul
  条件: (P Q : 有限集 3 -> R) (u v : R)
  证明: by
  simp only [addY, negY_eq, negAddY_smul, addX_smul, addZ_smul]
  ring1

Depends on / 依赖: addX_smul, addZ_smul, negAddY_smul, negY_eq
-/
lemma addY_smul (P Q : Fin 3 -> R) (u v : R) :
    W'.addY (u • P) (v • Q) = (u * v) ^ 2 * W'.addY P Q := by
  simp only [addY, negY_eq, negAddY_smul, addX_smul, addZ_smul]
  ring1

/--
lemma `addY_self` / 引理 `addY_self`

English:
lemma addY_self
  given: (P : Fin 3 -> R)
  statement: W'.addY P P = 0
  proof: by
  simp only [addY, negY_eq, negAddY_self, addX_self, addZ_self, neg_zero, mul_zero, sub_zero]

中文:
引理 addY_self
  条件: (P : 有限集 3 -> R)
  结论: W'.addY P P = 0
  证明: by
  simp only [addY, negY_eq, negAddY_self, addX_self, addZ_self, neg_zero, mul_zero, sub_zero]

Depends on / 依赖: addX_self, addZ_self, mul_zero, negAddY_self, negY_eq, neg_zero, sub_zero
-/
lemma addY_self (P : Fin 3 -> R) : W'.addY P P = 0 := by
  simp only [addY, negY_eq, negAddY_self, addX_self, addZ_self, neg_zero, mul_zero, sub_zero]

/--
lemma `addY_of_Z_eq_zero_left` / 引理 `addY_of_Z_eq_zero_left`

English:
lemma addY_of_Z_eq_zero_left
  statement: [NoZeroDivisors R] {P Q : Fin 3 -> R} (hP : W'.Equation P)
  proof: by
  rw [addY]; rw [negY_eq]; rw [negAddY_of_Z_eq_zero_left hP hPz]; rw [negY]; rw [addX_of_Z_eq_zero_left hP hPz]; rw [addZ_of_Z_eq_zero_left hP hPz]
  ring1

中文:
引理 addY_of_Z_eq_zero_left
  结论: [无零因子 R] {P Q : 有限集 3 -> R} (hP : W'.方程 P)
  证明: by
  rw [addY]; rw [negY_eq]; rw [negAddY_of_Z_eq_zero_left hP hPz]; rw [negY]; rw [addX_of_Z_eq_zero_left hP hPz]; rw [addZ_of_Z_eq_zero_left hP hPz]
  ring1

Depends on / 依赖: addX_of_Z_eq_zero_left, addZ_of_Z_eq_zero_left, negAddY_of_Z_eq_zero_left, negY_eq
-/
lemma addY_of_Z_eq_zero_left [NoZeroDivisors R] {P Q : Fin 3 -> R} (hP : W'.Equation P)
    (hPz : P z = 0) : W'.addY P Q = P y ^ 2 * Q z * Q y := by
  rw [addY]; rw [negY_eq]; rw [negAddY_of_Z_eq_zero_left hP hPz]; rw [negY]; rw [addX_of_Z_eq_zero_left hP hPz]; rw [addZ_of_Z_eq_zero_left hP hPz]
  ring1

/--
lemma `addY_of_Z_eq_zero_right` / 引理 `addY_of_Z_eq_zero_right`

English:
lemma addY_of_Z_eq_zero_right
  statement: [NoZeroDivisors R] {P Q : Fin 3 -> R} (hQ : W'.Equation Q)
  proof: by
  rw [addY]; rw [negY_eq]; rw [negAddY_of_Z_eq_zero_right hQ hQz]; rw [negY]; rw [addX_of_Z_eq_zero_right hQ hQz]; rw [addZ_of_Z_eq_zero_right hQ hQz]
  ring1

中文:
引理 addY_of_Z_eq_zero_right
  结论: [无零因子 R] {P Q : 有限集 3 -> R} (hQ : W'.方程 Q)
  证明: by
  rw [addY]; rw [negY_eq]; rw [negAddY_of_Z_eq_zero_right hQ hQz]; rw [negY]; rw [addX_of_Z_eq_zero_right hQ hQz]; rw [addZ_of_Z_eq_zero_right hQ hQz]
  ring1

Depends on / 依赖: addX_of_Z_eq_zero_right, addZ_of_Z_eq_zero_right, negAddY_of_Z_eq_zero_right, negY_eq
-/
lemma addY_of_Z_eq_zero_right [NoZeroDivisors R] {P Q : Fin 3 -> R} (hQ : W'.Equation Q)
    (hQz : Q z = 0) : W'.addY P Q = -(Q y ^ 2 * P z) * P y := by
  rw [addY]; rw [negY_eq]; rw [negAddY_of_Z_eq_zero_right hQ hQz]; rw [negY]; rw [addX_of_Z_eq_zero_right hQ hQz]; rw [addZ_of_Z_eq_zero_right hQ hQz]
  ring1

/--
lemma `addY_of_X_eq'` / 引理 `addY_of_X_eq'`

English:
lemma addY_of_X_eq'
  statement: [NoZeroDivisors R] {P Q : Fin 3 -> R} (hP : W'.Equation P) (hQ : W'.Equation Q)
  proof: by
  linear_combination (norm := (rw [addY, negY_eq, addX_of_X_eq hP hQ hPz hQz hx,
    addZ_of_X_eq hP hQ hPz hQz hx]; ring1)) -(P z * Q z) * negAddY_of_X_eq' hP hQ hx

中文:
引理 addY_of_X_eq'
  结论: [无零因子 R] {P Q : 有限集 3 -> R} (hP : W'.方程 P) (hQ : W'.方程 Q)
  证明: by
  linear_combination (norm := (rw [addY, negY_eq, addX_of_X_eq hP hQ hPz hQz hx,
    addZ_of_X_eq hP hQ hPz hQz hx]; ring1)) -(P z * Q z) * negAddY_of_X_eq' hP hQ hx

Depends on / 依赖: addX_of_X_eq, addZ_of_X_eq, linear_combination, negAddY_of_X_eq, negY_eq
-/
lemma addY_of_X_eq' [NoZeroDivisors R] {P Q : Fin 3 -> R} (hP : W'.Equation P) (hQ : W'.Equation Q)
    (hPz : P z != 0) (hQz : Q z != 0) (hx : P x * Q z = Q x * P z) :
    W'.addY P Q * (P z * Q z) ^ 3 = -(P y * Q z - Q y * P z) ^ 3 * (P z * Q z) ^ 2 := by
  linear_combination (norm := (rw [addY, negY_eq, addX_of_X_eq hP hQ hPz hQz hx,
    addZ_of_X_eq hP hQ hPz hQz hx]; ring1)) -(P z * Q z) * negAddY_of_X_eq' hP hQ hx

/--
lemma `addY_of_X_eq` / 引理 `addY_of_X_eq`

English:
lemma addY_of_X_eq
  statement: {P Q : Fin 3 -> F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z != 0)
  proof: by
  rw [addU]; rw [← mul_div_mul_right _ _ <| pow_ne_zero 2 <| mul_ne_zero hPz hQz]; rw [← addY_of_X_eq' hP hQ hPz hQz hx]; rw [← pow_succ']; rw [mul_div_cancel_right₀ _ pow_ne_zero 3 mul_ne_zero hPz hQz]

中文:
引理 addY_of_X_eq
  结论: {P Q : 有限集 3 -> F} (hP : W.方程 P) (hQ : W.方程 Q) (hPz : P z != 0)
  证明: by
  rw [addU]; rw [← mul_div_mul_right _ _ <| pow_ne_zero 2 <| mul_ne_zero hPz hQz]; rw [← addY_of_X_eq' hP hQ hPz hQz hx]; rw [← pow_succ']; rw [mul_div_cancel_right₀ _ pow_ne_zero 3 mul_ne_zero hPz hQz]

Depends on / 依赖: addY_of_X_eq, mul_div_mul_right, mul_ne_zero, pow_ne_zero, pow_succ
-/
lemma addY_of_X_eq {P Q : Fin 3 -> F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z != 0)
    (hQz : Q z != 0) (hx : P x * Q z = Q x * P z) : W.addY P Q = addU P Q := by
  rw [addU]; rw [← mul_div_mul_right _ _ <| pow_ne_zero 2 <| mul_ne_zero hPz hQz]; rw [← addY_of_X_eq' hP hQ hPz hQz hx]; rw [← pow_succ']; rw [mul_div_cancel_right₀ _ pow_ne_zero 3 mul_ne_zero hPz hQz]

/--
lemma `addY_of_Z_ne_zero` / 引理 `addY_of_Z_ne_zero`

English:
lemma addY_of_Z_ne_zero
  statement: [DecidableEq F] {P Q : Fin 3 -> F} (hP : W.Equation P) (hQ : W.Equation Q)
  proof: by
  erw [addY, negY_of_Z_ne_zero <| addZ_ne_zero_of_X_ne hP hQ hx, addX_of_Z_ne_zero hP hQ hPz hQz hx,
    negAddY_of_Z_ne_zero hP hQ hPz hQz hx, Affine.addY]

中文:
引理 addY_of_Z_ne_zero
  结论: [DecidableEq F] {P Q : 有限集 3 -> F} (hP : W.方程 P) (hQ : W.方程 Q)
  证明: by
  erw [addY, negY_of_Z_ne_zero <| addZ_ne_zero_of_X_ne hP hQ hx, addX_of_Z_ne_zero hP hQ hPz hQz hx,
    negAddY_of_Z_ne_zero hP hQ hPz hQz hx, Affine.addY]

Depends on / 依赖: Affine, Affine.addY, addX_of_Z_ne_zero, addZ_ne_zero_of_X_ne, negAddY_of_Z_ne_zero, negY_of_Z_ne_zero
-/
lemma addY_of_Z_ne_zero [DecidableEq F] {P Q : Fin 3 -> F} (hP : W.Equation P) (hQ : W.Equation Q)
    (hPz : P z != 0) (hQz : Q z != 0) (hx : P x * Q z != Q x * P z) : W.addY P Q / W.addZ P Q =
      W.toAffine.addY (P x / P z) (Q x / Q z) (P y / P z)
        (W.toAffine.slope (P x / P z) (Q x / Q z) (P y / P z) (Q y / Q z)) := by
  erw [addY, negY_of_Z_ne_zero <| addZ_ne_zero_of_X_ne hP hQ hx, addX_of_Z_ne_zero hP hQ hPz hQz hx,
    negAddY_of_Z_ne_zero hP hQ hPz hQz hx, Affine.addY]

variable (W') in
/--
Definition of `addXYZ` / `addXYZ` 的定义

English:
definition addXYZ
  signature: (P Q : Fin 3 -> R)
  body: ![W'.addX P Q, W'.addY P Q, W'.addZ P Q]

中文:
定义 addXYZ
  签名: (P Q : 有限集 3 -> R)
  定义体: ![W'.addX P Q, W'.addY P Q, W'.addZ P Q]
-/
noncomputable def addXYZ (P Q : Fin 3 -> R) : Fin 3 -> R :=
  ![W'.addX P Q, W'.addY P Q, W'.addZ P Q]

/--
lemma `addXYZ_X` / 引理 `addXYZ_X`

English:
lemma addXYZ_X
  given: (P Q : Fin 3 -> R)
  statement: W'.addXYZ P Q x = W'.addX P Q
  proof: rfl

中文:
引理 addXYZ_X
  条件: (P Q : 有限集 3 -> R)
  结论: W'.addXYZ P Q x = W'.addX P Q
  证明: rfl
-/
lemma addXYZ_X (P Q : Fin 3 -> R) : W'.addXYZ P Q x = W'.addX P Q :=
  rfl

/--
lemma `addXYZ_Y` / 引理 `addXYZ_Y`

English:
lemma addXYZ_Y
  given: (P Q : Fin 3 -> R)
  statement: W'.addXYZ P Q y = W'.addY P Q
  proof: rfl

中文:
引理 addXYZ_Y
  条件: (P Q : 有限集 3 -> R)
  结论: W'.addXYZ P Q y = W'.addY P Q
  证明: rfl
-/
lemma addXYZ_Y (P Q : Fin 3 -> R) : W'.addXYZ P Q y = W'.addY P Q :=
  rfl

/--
lemma `addXYZ_Z` / 引理 `addXYZ_Z`

English:
lemma addXYZ_Z
  given: (P Q : Fin 3 -> R)
  statement: W'.addXYZ P Q z = W'.addZ P Q
  proof: rfl

中文:
引理 addXYZ_Z
  条件: (P Q : 有限集 3 -> R)
  结论: W'.addXYZ P Q z = W'.addZ P Q
  证明: rfl
-/
lemma addXYZ_Z (P Q : Fin 3 -> R) : W'.addXYZ P Q z = W'.addZ P Q :=
  rfl

/--
lemma `addXYZ_smul` / 引理 `addXYZ_smul`

English:
lemma addXYZ_smul
  given: (P Q : Fin 3 -> R) (u v : R)
  proof: by
  rw [addXYZ]; rw [addX_smul]; rw [addY_smul]; rw [addZ_smul]; rw [smul_fin3]; rw [addXYZ_X]; rw [addXYZ_Y]; rw [addXYZ_Z]

中文:
引理 addXYZ_smul
  条件: (P Q : 有限集 3 -> R) (u v : R)
  证明: by
  rw [addXYZ]; rw [addX_smul]; rw [addY_smul]; rw [addZ_smul]; rw [smul_fin3]; rw [addXYZ_X]; rw [addXYZ_Y]; rw [addXYZ_Z]

Depends on / 依赖: addXYZ, addXYZ_X, addXYZ_Y, addXYZ_Z, addX_smul, addY_smul, addZ_smul, smul_fin3
-/
lemma addXYZ_smul (P Q : Fin 3 -> R) (u v : R) :
    W'.addXYZ (u • P) (v • Q) = (u * v) ^ 2 • W'.addXYZ P Q := by
  rw [addXYZ]; rw [addX_smul]; rw [addY_smul]; rw [addZ_smul]; rw [smul_fin3]; rw [addXYZ_X]; rw [addXYZ_Y]; rw [addXYZ_Z]

/--
lemma `addXYZ_self` / 引理 `addXYZ_self`

English:
lemma addXYZ_self
  given: (P : Fin 3 -> R)
  statement: W'.addXYZ P P = ![0, 0, 0]
  proof: by
  rw [addXYZ]; rw [addX_self]; rw [addY_self]; rw [addZ_self]

中文:
引理 addXYZ_self
  条件: (P : 有限集 3 -> R)
  结论: W'.addXYZ P P = ![0, 0, 0]
  证明: by
  rw [addXYZ]; rw [addX_self]; rw [addY_self]; rw [addZ_self]

Depends on / 依赖: addXYZ, addX_self, addY_self, addZ_self
-/
lemma addXYZ_self (P : Fin 3 -> R) : W'.addXYZ P P = ![0, 0, 0] := by
  rw [addXYZ]; rw [addX_self]; rw [addY_self]; rw [addZ_self]

/--
lemma `addXYZ_of_Z_eq_zero_left` / 引理 `addXYZ_of_Z_eq_zero_left`

English:
lemma addXYZ_of_Z_eq_zero_left
  statement: [NoZeroDivisors R] {P Q : Fin 3 -> R} (hP : W'.Equation P)
  proof: by
  rw [addXYZ]; rw [addX_of_Z_eq_zero_left hP hPz]; rw [addY_of_Z_eq_zero_left hP hPz]; rw [addZ_of_Z_eq_zero_left hP hPz]; rw [smul_fin3]

中文:
引理 addXYZ_of_Z_eq_zero_left
  结论: [无零因子 R] {P Q : 有限集 3 -> R} (hP : W'.方程 P)
  证明: by
  rw [addXYZ]; rw [addX_of_Z_eq_zero_left hP hPz]; rw [addY_of_Z_eq_zero_left hP hPz]; rw [addZ_of_Z_eq_zero_left hP hPz]; rw [smul_fin3]

Depends on / 依赖: addXYZ, addX_of_Z_eq_zero_left, addY_of_Z_eq_zero_left, addZ_of_Z_eq_zero_left, smul_fin3
-/
lemma addXYZ_of_Z_eq_zero_left [NoZeroDivisors R] {P Q : Fin 3 -> R} (hP : W'.Equation P)
    (hPz : P z = 0) : W'.addXYZ P Q = (P y ^ 2 * Q z) • Q := by
  rw [addXYZ]; rw [addX_of_Z_eq_zero_left hP hPz]; rw [addY_of_Z_eq_zero_left hP hPz]; rw [addZ_of_Z_eq_zero_left hP hPz]; rw [smul_fin3]

/--
lemma `addXYZ_of_Z_eq_zero_right` / 引理 `addXYZ_of_Z_eq_zero_right`

English:
lemma addXYZ_of_Z_eq_zero_right
  statement: [NoZeroDivisors R] {P Q : Fin 3 -> R} (hQ : W'.Equation Q)
  proof: by
  rw [addXYZ]; rw [addX_of_Z_eq_zero_right hQ hQz]; rw [addY_of_Z_eq_zero_right hQ hQz]; rw [addZ_of_Z_eq_zero_right hQ hQz]; rw [smul_fin3]

中文:
引理 addXYZ_of_Z_eq_zero_right
  结论: [无零因子 R] {P Q : 有限集 3 -> R} (hQ : W'.方程 Q)
  证明: by
  rw [addXYZ]; rw [addX_of_Z_eq_zero_right hQ hQz]; rw [addY_of_Z_eq_zero_right hQ hQz]; rw [addZ_of_Z_eq_zero_right hQ hQz]; rw [smul_fin3]

Depends on / 依赖: addXYZ, addX_of_Z_eq_zero_right, addY_of_Z_eq_zero_right, addZ_of_Z_eq_zero_right, smul_fin3
-/
lemma addXYZ_of_Z_eq_zero_right [NoZeroDivisors R] {P Q : Fin 3 -> R} (hQ : W'.Equation Q)
    (hQz : Q z = 0) : W'.addXYZ P Q = -(Q y ^ 2 * P z) • P := by
  rw [addXYZ]; rw [addX_of_Z_eq_zero_right hQ hQz]; rw [addY_of_Z_eq_zero_right hQ hQz]; rw [addZ_of_Z_eq_zero_right hQ hQz]; rw [smul_fin3]

/--
lemma `addXYZ_of_X_eq` / 引理 `addXYZ_of_X_eq`

English:
lemma addXYZ_of_X_eq
  statement: {P Q : Fin 3 -> F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z != 0)
  proof: by
  erw [addXYZ, addX_of_X_eq hP hQ hPz hQz hx, addY_of_X_eq hP hQ hPz hQz hx,
    addZ_of_X_eq hP hQ hPz hQz hx, smul_fin3, mul_zero, mul_one]

中文:
引理 addXYZ_of_X_eq
  结论: {P Q : 有限集 3 -> F} (hP : W.方程 P) (hQ : W.方程 Q) (hPz : P z != 0)
  证明: by
  erw [addXYZ, addX_of_X_eq hP hQ hPz hQz hx, addY_of_X_eq hP hQ hPz hQz hx,
    addZ_of_X_eq hP hQ hPz hQz hx, smul_fin3, mul_zero, mul_one]

Depends on / 依赖: addXYZ, addX_of_X_eq, addY_of_X_eq, addZ_of_X_eq, mul_one, mul_zero, smul_fin3
-/
lemma addXYZ_of_X_eq {P Q : Fin 3 -> F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z != 0)
    (hQz : Q z != 0) (hx : P x * Q z = Q x * P z) : W.addXYZ P Q = addU P Q • ![0, 1, 0] := by
  erw [addXYZ, addX_of_X_eq hP hQ hPz hQz hx, addY_of_X_eq hP hQ hPz hQz hx,
    addZ_of_X_eq hP hQ hPz hQz hx, smul_fin3, mul_zero, mul_one]

/--
lemma `addXYZ_of_Z_ne_zero` / 引理 `addXYZ_of_Z_ne_zero`

English:
lemma addXYZ_of_Z_ne_zero
  statement: [DecidableEq F] {P Q : Fin 3 -> F} (hP : W.Equation P) (hQ : W.Equation Q)
  proof: by
have hZ : IsUnit W.addZ P Q := isUnit_addZ_of_X_ne hP hQ hx
  erw [addXYZ, smul_fin3, ← addX_of_Z_ne_zero hP hQ hPz hQz hx, hZ.mul_div_cancel,
    ← addY_of_Z_ne_zero hP hQ hPz hQz hx, hZ.mul_div_cancel, mul_one]

中文:
引理 addXYZ_of_Z_ne_zero
  结论: [DecidableEq F] {P Q : 有限集 3 -> F} (hP : W.方程 P) (hQ : W.方程 Q)
  证明: by
have hZ : IsUnit W.addZ P Q := isUnit_addZ_of_X_ne hP hQ hx
  erw [addXYZ, smul_fin3, ← addX_of_Z_ne_zero hP hQ hPz hQz hx, hZ.mul_div_cancel,
    ← addY_of_Z_ne_zero hP hQ hPz hQz hx, hZ.mul_div_cancel, mul_one]

Depends on / 依赖: IsUnit, W.addZ, addXYZ, addX_of_Z_ne_zero, addY_of_Z_ne_zero, hZ.mul_div_cancel, isUnit_addZ_of_X_ne, mul_div_cancel, mul_one, smul_fin3
-/
lemma addXYZ_of_Z_ne_zero [DecidableEq F] {P Q : Fin 3 -> F} (hP : W.Equation P) (hQ : W.Equation Q)
    (hPz : P z != 0) (hQz : Q z != 0) (hx : P x * Q z != Q x * P z) : W.addXYZ P Q = W.addZ P Q •
      ![W.toAffine.addX (P x / P z) (Q x / Q z)
          (W.toAffine.slope (P x / P z) (Q x / Q z) (P y / P z) (Q y / Q z)),
        W.toAffine.addY (P x / P z) (Q x / Q z) (P y / P z)
          (W.toAffine.slope (P x / P z) (Q x / Q z) (P y / P z) (Q y / Q z)), 1] := by
have hZ : IsUnit W.addZ P Q := isUnit_addZ_of_X_ne hP hQ hx
  erw [addXYZ, smul_fin3, ← addX_of_Z_ne_zero hP hQ hPz hQz hx, hZ.mul_div_cancel,
    ← addY_of_Z_ne_zero hP hQ hPz hQz hx, hZ.mul_div_cancel, mul_one]

/-! ## Maps and base changes -/

variable (f : R ->+* S) (P Q : Fin 3 -> R)

@[simp]
/--
lemma `map_negY` / 引理 `map_negY`

English:
lemma map_negY
  statement: (W'.map f).negY (f ∘ P) = f (W'.negY P)
  proof: by
  simp only [negY]
  map_simp

@[simp]

中文:
引理 map_negY
  结论: (W'.map f).negY (f ∘ P) = f (W'.negY P)
  证明: by
  simp only [negY]
  map_simp

@[simp]

Depends on / 依赖: map_simp
-/
lemma map_negY : (W'.map f).negY (f ∘ P) = f (W'.negY P) := by
  simp only [negY]
  map_simp

@[simp]
/--
lemma `map_dblU` / 引理 `map_dblU`

English:
lemma map_dblU
  given: (f : F ->+* K) (P : Fin 3 -> F)
  statement: (W.map f).dblU (f ∘ P) = f (W.dblU P)
  proof: by
  simp only [dblU_eq]
  map_simp

@[simp]

中文:
引理 map_dblU
  条件: (f : F ->+* K) (P : 有限集 3 -> F)
  结论: (W.map f).dblU (f ∘ P) = f (W.dblU P)
  证明: by
  simp only [dblU_eq]
  map_simp

@[simp]

Depends on / 依赖: dblU_eq, map_simp
-/
lemma map_dblU (f : F ->+* K) (P : Fin 3 -> F) : (W.map f).dblU (f ∘ P) = f (W.dblU P) := by
  simp only [dblU_eq]
  map_simp

@[simp]
/--
lemma `map_dblZ` / 引理 `map_dblZ`

English:
lemma map_dblZ
  statement: (W'.map f).dblZ (f ∘ P) = f (W'.dblZ P)
  proof: by
  simp only [dblZ, negY]
  map_simp

@[simp]

中文:
引理 map_dblZ
  结论: (W'.map f).dblZ (f ∘ P) = f (W'.dblZ P)
  证明: by
  simp only [dblZ, negY]
  map_simp

@[simp]

Depends on / 依赖: map_simp
-/
lemma map_dblZ : (W'.map f).dblZ (f ∘ P) = f (W'.dblZ P) := by
  simp only [dblZ, negY]
  map_simp

@[simp]
/--
lemma `map_dblX` / 引理 `map_dblX`

English:
lemma map_dblX
  statement: (W'.map f).dblX (f ∘ P) = f (W'.dblX P)
  proof: by
  simp only [dblX]
  map_simp

@[simp]

中文:
引理 map_dblX
  结论: (W'.map f).dblX (f ∘ P) = f (W'.dblX P)
  证明: by
  simp only [dblX]
  map_simp

@[simp]

Depends on / 依赖: map_simp
-/
lemma map_dblX : (W'.map f).dblX (f ∘ P) = f (W'.dblX P) := by
  simp only [dblX]
  map_simp

@[simp]
/--
lemma `map_negDblY` / 引理 `map_negDblY`

English:
lemma map_negDblY
  statement: (W'.map f).negDblY (f ∘ P) = f (W'.negDblY P)
  proof: by
  simp only [negDblY]
  map_simp

@[simp]

中文:
引理 map_negDblY
  结论: (W'.map f).negDblY (f ∘ P) = f (W'.negDblY P)
  证明: by
  simp only [negDblY]
  map_simp

@[simp]

Depends on / 依赖: map_simp, negDblY
-/
lemma map_negDblY : (W'.map f).negDblY (f ∘ P) = f (W'.negDblY P) := by
  simp only [negDblY]
  map_simp

@[simp]
/--
lemma `map_dblY` / 引理 `map_dblY`

English:
lemma map_dblY
  statement: (W'.map f).dblY (f ∘ P) = f (W'.dblY P)
  proof: by
  simp only [dblY, negY_eq, map_negDblY, map_dblX, map_dblZ]
  map_simp

@[simp]

中文:
引理 map_dblY
  结论: (W'.map f).dblY (f ∘ P) = f (W'.dblY P)
  证明: by
  simp only [dblY, negY_eq, map_negDblY, map_dblX, map_dblZ]
  map_simp

@[simp]

Depends on / 依赖: map_dblX, map_dblZ, map_negDblY, map_simp, negY_eq
-/
lemma map_dblY : (W'.map f).dblY (f ∘ P) = f (W'.dblY P) := by
  simp only [dblY, negY_eq, map_negDblY, map_dblX, map_dblZ]
  map_simp

@[simp]
/--
lemma `map_dblXYZ` / 引理 `map_dblXYZ`

English:
lemma map_dblXYZ
  statement: (W'.map f).dblXYZ (f ∘ P) = f ∘ dblXYZ W' P
  proof: by
  simp only [dblXYZ, map_dblX, map_dblY, map_dblZ, comp_fin3]

@[simp]

中文:
引理 map_dblXYZ
  结论: (W'.map f).dblXYZ (f ∘ P) = f ∘ dblXYZ W' P
  证明: by
  simp only [dblXYZ, map_dblX, map_dblY, map_dblZ, comp_fin3]

@[simp]

Depends on / 依赖: comp_fin3, dblXYZ, map_dblX, map_dblY, map_dblZ
-/
lemma map_dblXYZ : (W'.map f).dblXYZ (f ∘ P) = f ∘ dblXYZ W' P := by
  simp only [dblXYZ, map_dblX, map_dblY, map_dblZ, comp_fin3]

@[simp]
/--
lemma `map_addU` / 引理 `map_addU`

English:
lemma map_addU
  given: (f : F ->+* K) (P Q : Fin 3 -> F)
  statement: addU (f ∘ P) (f ∘ Q) = f (addU P Q)
  proof: by
  simp only [addU]
  map_simp

@[simp]

中文:
引理 map_addU
  条件: (f : F ->+* K) (P Q : 有限集 3 -> F)
  结论: addU (f ∘ P) (f ∘ Q) = f (addU P Q)
  证明: by
  simp only [addU]
  map_simp

@[simp]

Depends on / 依赖: map_simp
-/
lemma map_addU (f : F ->+* K) (P Q : Fin 3 -> F) : addU (f ∘ P) (f ∘ Q) = f (addU P Q) := by
  simp only [addU]
  map_simp

@[simp]
/--
lemma `map_addZ` / 引理 `map_addZ`

English:
lemma map_addZ
  statement: (W'.map f).addZ (f ∘ P) (f ∘ Q) = f (W'.addZ P Q)
  proof: by
  simp only [addZ]
  map_simp

@[simp]

中文:
引理 map_addZ
  结论: (W'.map f).addZ (f ∘ P) (f ∘ Q) = f (W'.addZ P Q)
  证明: by
  simp only [addZ]
  map_simp

@[simp]

Depends on / 依赖: map_simp
-/
lemma map_addZ : (W'.map f).addZ (f ∘ P) (f ∘ Q) = f (W'.addZ P Q) := by
  simp only [addZ]
  map_simp

@[simp]
/--
lemma `map_addX` / 引理 `map_addX`

English:
lemma map_addX
  statement: (W'.map f).addX (f ∘ P) (f ∘ Q) = f (W'.addX P Q)
  proof: by
  simp only [addX]
  map_simp

@[simp]

中文:
引理 map_addX
  结论: (W'.map f).addX (f ∘ P) (f ∘ Q) = f (W'.addX P Q)
  证明: by
  simp only [addX]
  map_simp

@[simp]

Depends on / 依赖: map_simp
-/
lemma map_addX : (W'.map f).addX (f ∘ P) (f ∘ Q) = f (W'.addX P Q) := by
  simp only [addX]
  map_simp

@[simp]
/--
lemma `map_negAddY` / 引理 `map_negAddY`

English:
lemma map_negAddY
  statement: (W'.map f).negAddY (f ∘ P) (f ∘ Q) = f (W'.negAddY P Q)
  proof: by
  simp only [negAddY]
  map_simp

@[simp]

中文:
引理 map_negAddY
  结论: (W'.map f).negAddY (f ∘ P) (f ∘ Q) = f (W'.negAddY P Q)
  证明: by
  simp only [negAddY]
  map_simp

@[simp]

Depends on / 依赖: map_simp, negAddY
-/
lemma map_negAddY : (W'.map f).negAddY (f ∘ P) (f ∘ Q) = f (W'.negAddY P Q) := by
  simp only [negAddY]
  map_simp

@[simp]
/--
lemma `map_addY` / 引理 `map_addY`

English:
lemma map_addY
  statement: (W'.map f).addY (f ∘ P) (f ∘ Q) = f (W'.addY P Q)
  proof: by
  simp only [addY, negY_eq, map_negAddY, map_addX, map_addZ]
  map_simp

@[simp]

中文:
引理 map_addY
  结论: (W'.map f).addY (f ∘ P) (f ∘ Q) = f (W'.addY P Q)
  证明: by
  simp only [addY, negY_eq, map_negAddY, map_addX, map_addZ]
  map_simp

@[simp]

Depends on / 依赖: map_addX, map_addZ, map_negAddY, map_simp, negY_eq
-/
lemma map_addY : (W'.map f).addY (f ∘ P) (f ∘ Q) = f (W'.addY P Q) := by
  simp only [addY, negY_eq, map_negAddY, map_addX, map_addZ]
  map_simp

@[simp]
/--
lemma `map_addXYZ` / 引理 `map_addXYZ`

English:
lemma map_addXYZ
  statement: (W'.map f).addXYZ (f ∘ P) (f ∘ Q) = f ∘ addXYZ W' P Q
  proof: by
  simp only [addXYZ, map_addX, map_addY, map_addZ, comp_fin3]

中文:
引理 map_addXYZ
  结论: (W'.map f).addXYZ (f ∘ P) (f ∘ Q) = f ∘ addXYZ W' P Q
  证明: by
  simp only [addXYZ, map_addX, map_addY, map_addZ, comp_fin3]

Depends on / 依赖: addXYZ, comp_fin3, map_addX, map_addY, map_addZ
-/
lemma map_addXYZ : (W'.map f).addXYZ (f ∘ P) (f ∘ Q) = f ∘ addXYZ W' P Q := by
  simp only [addXYZ, map_addX, map_addY, map_addZ, comp_fin3]

variable [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A] [Algebra R B] [Algebra S B]
  [IsScalarTower R S B] (f : A ->ₐ[S] B) (P Q : Fin 3 -> A)

/--
lemma `baseChange_negY` / 引理 `baseChange_negY`

English:
lemma baseChange_negY
  statement: (W'⁄B).negY (f ∘ P) = f ((W'⁄A).negY P)
  proof: by
  rw [← RingHom.coe_coe]; rw [← map_negY]; rw [map_baseChange]

中文:
引理 baseChange_negY
  结论: (W'⁄B).negY (f ∘ P) = f ((W'⁄A).negY P)
  证明: by
  rw [← RingHom.coe_coe]; rw [← map_negY]; rw [map_baseChange]

Depends on / 依赖: RingHom, RingHom.coe_coe, coe_coe, map_baseChange, map_negY
-/
lemma baseChange_negY : (W'⁄B).negY (f ∘ P) = f ((W'⁄A).negY P) := by
  rw [← RingHom.coe_coe]; rw [← map_negY]; rw [map_baseChange]

/--
lemma `baseChange_dblU` / 引理 `baseChange_dblU`

English:
lemma baseChange_dblU
  statement: [Algebra R F] [Algebra S F] [IsScalarTower R S F] [Algebra R K] [Algebra S K]
  proof: by
  rw [← RingHom.coe_coe]; rw [← map_dblU]; rw [map_baseChange]

中文:
引理 baseChange_dblU
  结论: [代数 R F] [代数 S F] [标量塔 R S F] [代数 R K] [代数 S K]
  证明: by
  rw [← RingHom.coe_coe]; rw [← map_dblU]; rw [map_baseChange]

Depends on / 依赖: RingHom, RingHom.coe_coe, coe_coe, map_baseChange, map_dblU
-/
lemma baseChange_dblU [Algebra R F] [Algebra S F] [IsScalarTower R S F] [Algebra R K] [Algebra S K]
    [IsScalarTower R S K] (f : F ->ₐ[S] K) (P : Fin 3 -> F) :
    (W'⁄K).dblU (f ∘ P) = f ((W'⁄F).dblU P) := by
  rw [← RingHom.coe_coe]; rw [← map_dblU]; rw [map_baseChange]

/--
lemma `baseChange_dblZ` / 引理 `baseChange_dblZ`

English:
lemma baseChange_dblZ
  statement: (W'⁄B).dblZ (f ∘ P) = f ((W'⁄A).dblZ P)
  proof: by
  rw [← RingHom.coe_coe]; rw [← map_dblZ]; rw [map_baseChange]

中文:
引理 baseChange_dblZ
  结论: (W'⁄B).dblZ (f ∘ P) = f ((W'⁄A).dblZ P)
  证明: by
  rw [← RingHom.coe_coe]; rw [← map_dblZ]; rw [map_baseChange]

Depends on / 依赖: RingHom, RingHom.coe_coe, coe_coe, map_baseChange, map_dblZ
-/
lemma baseChange_dblZ : (W'⁄B).dblZ (f ∘ P) = f ((W'⁄A).dblZ P) := by
  rw [← RingHom.coe_coe]; rw [← map_dblZ]; rw [map_baseChange]

/--
lemma `baseChange_dblX` / 引理 `baseChange_dblX`

English:
lemma baseChange_dblX
  statement: (W'⁄B).dblX (f ∘ P) = f ((W'⁄A).dblX P)
  proof: by
  rw [← RingHom.coe_coe]; rw [← map_dblX]; rw [map_baseChange]

中文:
引理 baseChange_dblX
  结论: (W'⁄B).dblX (f ∘ P) = f ((W'⁄A).dblX P)
  证明: by
  rw [← RingHom.coe_coe]; rw [← map_dblX]; rw [map_baseChange]

Depends on / 依赖: RingHom, RingHom.coe_coe, coe_coe, map_baseChange, map_dblX
-/
lemma baseChange_dblX : (W'⁄B).dblX (f ∘ P) = f ((W'⁄A).dblX P) := by
  rw [← RingHom.coe_coe]; rw [← map_dblX]; rw [map_baseChange]

/--
lemma `baseChange_negDblY` / 引理 `baseChange_negDblY`

English:
lemma baseChange_negDblY
  statement: (W'⁄B).negDblY (f ∘ P) = f ((W'⁄A).negDblY P)
  proof: by
  rw [← RingHom.coe_coe]; rw [← map_negDblY]; rw [map_baseChange]

中文:
引理 baseChange_negDblY
  结论: (W'⁄B).negDblY (f ∘ P) = f ((W'⁄A).negDblY P)
  证明: by
  rw [← RingHom.coe_coe]; rw [← map_negDblY]; rw [map_baseChange]

Depends on / 依赖: RingHom, RingHom.coe_coe, coe_coe, map_baseChange, map_negDblY
-/
lemma baseChange_negDblY : (W'⁄B).negDblY (f ∘ P) = f ((W'⁄A).negDblY P) := by
  rw [← RingHom.coe_coe]; rw [← map_negDblY]; rw [map_baseChange]

/--
lemma `baseChange_dblY` / 引理 `baseChange_dblY`

English:
lemma baseChange_dblY
  statement: (W'⁄B).dblY (f ∘ P) = f ((W'⁄A).dblY P)
  proof: by
  rw [← RingHom.coe_coe]; rw [← map_dblY]; rw [map_baseChange]

中文:
引理 baseChange_dblY
  结论: (W'⁄B).dblY (f ∘ P) = f ((W'⁄A).dblY P)
  证明: by
  rw [← RingHom.coe_coe]; rw [← map_dblY]; rw [map_baseChange]

Depends on / 依赖: RingHom, RingHom.coe_coe, coe_coe, map_baseChange, map_dblY
-/
lemma baseChange_dblY : (W'⁄B).dblY (f ∘ P) = f ((W'⁄A).dblY P) := by
  rw [← RingHom.coe_coe]; rw [← map_dblY]; rw [map_baseChange]

/--
lemma `baseChange_dblXYZ` / 引理 `baseChange_dblXYZ`

English:
lemma baseChange_dblXYZ
  statement: (W'⁄B).dblXYZ (f ∘ P) = f ∘ (W'⁄A).dblXYZ P
  proof: by
  rw [← RingHom.coe_coe]; rw [← map_dblXYZ]; rw [map_baseChange]

中文:
引理 baseChange_dblXYZ
  结论: (W'⁄B).dblXYZ (f ∘ P) = f ∘ (W'⁄A).dblXYZ P
  证明: by
  rw [← RingHom.coe_coe]; rw [← map_dblXYZ]; rw [map_baseChange]

Depends on / 依赖: RingHom, RingHom.coe_coe, coe_coe, map_baseChange, map_dblXYZ
-/
lemma baseChange_dblXYZ : (W'⁄B).dblXYZ (f ∘ P) = f ∘ (W'⁄A).dblXYZ P := by
  rw [← RingHom.coe_coe]; rw [← map_dblXYZ]; rw [map_baseChange]

/--
lemma `baseChange_addX` / 引理 `baseChange_addX`

English:
lemma baseChange_addX
  statement: (W'⁄B).addX (f ∘ P) (f ∘ Q) = f ((W'⁄A).addX P Q)
  proof: by
  rw [← RingHom.coe_coe]; rw [← map_addX]; rw [map_baseChange]

中文:
引理 baseChange_addX
  结论: (W'⁄B).addX (f ∘ P) (f ∘ Q) = f ((W'⁄A).addX P Q)
  证明: by
  rw [← RingHom.coe_coe]; rw [← map_addX]; rw [map_baseChange]

Depends on / 依赖: RingHom, RingHom.coe_coe, coe_coe, map_addX, map_baseChange
-/
lemma baseChange_addX : (W'⁄B).addX (f ∘ P) (f ∘ Q) = f ((W'⁄A).addX P Q) := by
  rw [← RingHom.coe_coe]; rw [← map_addX]; rw [map_baseChange]

/--
lemma `baseChange_negAddY` / 引理 `baseChange_negAddY`

English:
lemma baseChange_negAddY
  statement: (W'⁄B).negAddY (f ∘ P) (f ∘ Q) = f ((W'⁄A).negAddY P Q)
  proof: by
  rw [← RingHom.coe_coe]; rw [← map_negAddY]; rw [map_baseChange]

中文:
引理 baseChange_negAddY
  结论: (W'⁄B).negAddY (f ∘ P) (f ∘ Q) = f ((W'⁄A).negAddY P Q)
  证明: by
  rw [← RingHom.coe_coe]; rw [← map_negAddY]; rw [map_baseChange]

Depends on / 依赖: RingHom, RingHom.coe_coe, coe_coe, map_baseChange, map_negAddY
-/
lemma baseChange_negAddY : (W'⁄B).negAddY (f ∘ P) (f ∘ Q) = f ((W'⁄A).negAddY P Q) := by
  rw [← RingHom.coe_coe]; rw [← map_negAddY]; rw [map_baseChange]

/--
lemma `baseChange_addY` / 引理 `baseChange_addY`

English:
lemma baseChange_addY
  statement: (W'⁄B).addY (f ∘ P) (f ∘ Q) = f ((W'⁄A).addY P Q)
  proof: by
  rw [← RingHom.coe_coe]; rw [← map_addY]; rw [map_baseChange]

中文:
引理 baseChange_addY
  结论: (W'⁄B).addY (f ∘ P) (f ∘ Q) = f ((W'⁄A).addY P Q)
  证明: by
  rw [← RingHom.coe_coe]; rw [← map_addY]; rw [map_baseChange]

Depends on / 依赖: RingHom, RingHom.coe_coe, coe_coe, map_addY, map_baseChange
-/
lemma baseChange_addY : (W'⁄B).addY (f ∘ P) (f ∘ Q) = f ((W'⁄A).addY P Q) := by
  rw [← RingHom.coe_coe]; rw [← map_addY]; rw [map_baseChange]

/--
lemma `baseChange_addXYZ` / 引理 `baseChange_addXYZ`

English:
lemma baseChange_addXYZ
  statement: (W'⁄B).addXYZ (f ∘ P) (f ∘ Q) = f ∘ (W'⁄A).addXYZ P Q
  proof: by
  rw [← RingHom.coe_coe]; rw [← map_addXYZ]; rw [map_baseChange]

中文:
引理 baseChange_addXYZ
  结论: (W'⁄B).addXYZ (f ∘ P) (f ∘ Q) = f ∘ (W'⁄A).addXYZ P Q
  证明: by
  rw [← RingHom.coe_coe]; rw [← map_addXYZ]; rw [map_baseChange]

Depends on / 依赖: RingHom, RingHom.coe_coe, coe_coe, map_addXYZ, map_baseChange
-/
lemma baseChange_addXYZ : (W'⁄B).addXYZ (f ∘ P) (f ∘ Q) = f ∘ (W'⁄A).addXYZ P Q := by
  rw [← RingHom.coe_coe]; rw [← map_addXYZ]; rw [map_baseChange]

end Projective

end WeierstrassCurve
