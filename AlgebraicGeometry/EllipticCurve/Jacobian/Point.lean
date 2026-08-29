/-
Copyright (c) 2025 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Formula

/-!
# Nonsingular points and the group law in Jacobian coordinates

Let `W` be a Weierstrass curve over a field `F`. The nonsingular Jacobian points of `W` can be
endowed with a group law, which is uniquely determined by the formulae in
`Mathlib/AlgebraicGeometry/EllipticCurve/Jacobian/Formula.lean` and follows from an equivalence with
the nonsingular points in affine coordinates.

This file defines the group law on nonsingular Jacobian points.

## Main definitions

* `WeierstrassCurve.Jacobian.neg`: the negation of a point representative.
* `WeierstrassCurve.Jacobian.negMap`: the negation of a point class.
* `WeierstrassCurve.Jacobian.add`: the addition of two point representatives.
* `WeierstrassCurve.Jacobian.addMap`: the addition of two point classes.
* `WeierstrassCurve.Jacobian.Point`: a nonsingular Jacobian point.
* `WeierstrassCurve.Jacobian.Point.neg`: the negation of a nonsingular Jacobian point.
* `WeierstrassCurve.Jacobian.Point.add`: the addition of two nonsingular Jacobian points.
* `WeierstrassCurve.Jacobian.Point.toAffineAddEquiv`: the equivalence between the type of
  nonsingular Jacobian points with the type of nonsingular points in affine coordinates.

## Main statements

* `WeierstrassCurve.Jacobian.nonsingular_neg`: negation preserves the nonsingular condition.
* `WeierstrassCurve.Jacobian.nonsingular_add`: addition preserves the nonsingular condition.
* `WeierstrassCurve.Jacobian.Point.instAddCommGroup`: the type of nonsingular Jacobian points forms
  an abelian group under addition.

## Implementation notes

Note that `W(X, Y, Z)` and its partial derivatives are independent of the point representative, and
the nonsingularity condition already implies `(x, y, z) ≠ (0, 0, 0)`, so a nonsingular Jacobian
point on `W` can be given by `[x : y : z]` and the nonsingular condition on any representative.

A nonsingular Jacobian point representative can be converted to a nonsingular point in affine
coordinates using `WeierstrassCurve.Jacobian.Point.toAffine`, which lifts to a map on nonsingular
Jacobian points using `WeierstrassCurve.Jacobian.Point.toAffineLift`. Conversely, a nonsingular
point in affine coordinates can be converted to a nonsingular Jacobian point using
`WeierstrassCurve.Jacobian.Point.fromAffine` or `WeierstrassCurve.Affine.Point.toJacobian`.

Whenever possible, all changes to documentation and naming of definitions and theorems should be
mirrored in `Mathlib/AlgebraicGeometry/EllipticCurve/Projective/Point.lean`.

## References

[J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, Jacobian, point, group law
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
  [CommRing A] [CommRing B] [Field F] [Field K] {W' : Jacobian R} {W : Jacobian F}

namespace Jacobian

/-! ## Negation on Jacobian point representatives -/

variable (W') in
/--
Definition of `neg` / `neg` 的定义

English:
definition neg
  signature: (P : Fin 3 -> R)
  body: ![P x, W'.negY P, P z]

中文:
定义 neg
  签名: (P : 有限集 3 -> R)
  定义体: ![P x, W'.negY P, P z]
-/
def neg (P : Fin 3 -> R) : Fin 3 -> R :=
  ![P x, W'.negY P, P z]

/--
lemma `neg_X` / 引理 `neg_X`

English:
lemma neg_X
  given: (P : Fin 3 -> R)
  statement: W'.neg P x = P x
  proof: rfl

中文:
引理 neg_X
  条件: (P : 有限集 3 -> R)
  结论: W'.neg P x = P x
  证明: rfl
-/
lemma neg_X (P : Fin 3 -> R) : W'.neg P x = P x :=
  rfl

/--
lemma `neg_Y` / 引理 `neg_Y`

English:
lemma neg_Y
  given: (P : Fin 3 -> R)
  statement: W'.neg P y = W'.negY P
  proof: rfl

中文:
引理 neg_Y
  条件: (P : 有限集 3 -> R)
  结论: W'.neg P y = W'.negY P
  证明: rfl
-/
lemma neg_Y (P : Fin 3 -> R) : W'.neg P y = W'.negY P :=
  rfl

/--
lemma `neg_Z` / 引理 `neg_Z`

English:
lemma neg_Z
  given: (P : Fin 3 -> R)
  statement: W'.neg P z = P z
  proof: rfl

中文:
引理 neg_Z
  条件: (P : 有限集 3 -> R)
  结论: W'.neg P z = P z
  证明: rfl
-/
lemma neg_Z (P : Fin 3 -> R) : W'.neg P z = P z :=
  rfl

/--
lemma `neg_smul` / 引理 `neg_smul`

English:
lemma neg_smul
  given: (P : Fin 3 -> R) (u : R)
  statement: W'.neg (u • P) = u • W'.neg P
  proof: by
  rw [neg]; rw [negY_smul]
  rfl

中文:
引理 neg_smul
  条件: (P : 有限集 3 -> R) (u : R)
  结论: W'.neg (u • P) = u • W'.neg P
  证明: by
  rw [neg]; rw [negY_smul]
  rfl
-/
protected lemma neg_smul (P : Fin 3 -> R) (u : R) : W'.neg (u • P) = u • W'.neg P := by
  rw [neg]; rw [negY_smul]
  rfl

/--
lemma `neg_smul_equiv` / 引理 `neg_smul_equiv`

English:
lemma neg_smul_equiv
  given: (P : Fin 3 -> R) {u : R} (hu : IsUnit u)
  statement: W'.neg (u • P) ≈ W'.neg P
  proof: ⟨hu.unit, (W'.neg_smul ..).symm⟩

中文:
引理 neg_smul_equiv
  条件: (P : 有限集 3 -> R) {u : R} (hu : 是单位 u)
  结论: W'.neg (u • P) ≈ W'.neg P
  证明: ⟨hu.unit, (W'.neg_smul ..).symm⟩

Depends on / 依赖: hu.unit, neg_smul
-/
lemma neg_smul_equiv (P : Fin 3 -> R) {u : R} (hu : IsUnit u) : W'.neg (u • P) ≈ W'.neg P :=
  ⟨hu.unit, (W'.neg_smul ..).symm⟩

/--
lemma `neg_equiv` / 引理 `neg_equiv`

English:
lemma neg_equiv
  given: {P Q : Fin 3 -> R} (h : P ≈ Q)
  statement: W'.neg P ≈ W'.neg Q
  proof: by
  rcases h with ⟨u, rfl⟩
  exact neg_smul_equiv Q u.isUnit

中文:
引理 neg_equiv
  条件: {P Q : 有限集 3 -> R} (h : P ≈ Q)
  结论: W'.neg P ≈ W'.neg Q
  证明: by
  rcases h with ⟨u, rfl⟩
  exact neg_smul_equiv Q u.isUnit

Depends on / 依赖: isUnit, neg_smul_equiv, u.isUnit
-/
lemma neg_equiv {P Q : Fin 3 -> R} (h : P ≈ Q) : W'.neg P ≈ W'.neg Q := by
  rcases h with ⟨u, rfl⟩
  exact neg_smul_equiv Q u.isUnit

/--
lemma `neg_of_Z_eq_zero'` / 引理 `neg_of_Z_eq_zero'`

English:
lemma neg_of_Z_eq_zero'
  given: {P : Fin 3 -> R} (hPz : P z = 0)
  statement: W'.neg P = ![P x, -P y, 0]
  proof: by
  rw [neg]; rw [negY_of_Z_eq_zero hPz]; rw [hPz]

中文:
引理 neg_of_Z_eq_zero'
  条件: {P : 有限集 3 -> R} (hPz : P z = 0)
  结论: W'.neg P = ![P x, -P y, 0]
  证明: by
  rw [neg]; rw [negY_of_Z_eq_zero hPz]; rw [hPz]

Depends on / 依赖: negY_of_Z_eq_zero
-/
lemma neg_of_Z_eq_zero' {P : Fin 3 -> R} (hPz : P z = 0) : W'.neg P = ![P x, -P y, 0] := by
  rw [neg]; rw [negY_of_Z_eq_zero hPz]; rw [hPz]

/--
lemma `neg_of_Z_eq_zero` / 引理 `neg_of_Z_eq_zero`

English:
lemma neg_of_Z_eq_zero
  given: {P : Fin 3 -> F} (hP : W.Nonsingular P) (hPz : P z = 0)
  proof: by
have hX {n : Nat} : IsUnit P x ^ n := (isUnit_X_of_Z_eq_zero hP hPz).pow n
  erw [neg_of_Z_eq_zero' hPz, smul_fin3, neg_sq, div_pow, (equation_of_Z_eq_zero hPz).mp hP.left,
pow_succ, hX.mul_div_cancel_left, mul_one, Odd.neg_pow by decide, div_pow, pow_succ,
    (equation_of_Z_eq_zero hPz).mp hP.left, hX.mul_div_cancel_left, mul_one, mul_zero]

中文:
引理 neg_of_Z_eq_zero
  条件: {P : 有限集 3 -> F} (hP : W.非奇异 P) (hPz : P z = 0)
  证明: by
have hX {n : Nat} : IsUnit P x ^ n := (isUnit_X_of_Z_eq_zero hP hPz).pow n
  erw [neg_of_Z_eq_zero' hPz, smul_fin3, neg_sq, div_pow, (equation_of_Z_eq_zero hPz).mp hP.left,
pow_succ, hX.mul_div_cancel_left, mul_one, Odd.neg_pow by decide, div_pow, pow_succ,
    (equation_of_Z_eq_zero hPz).mp hP.left, hX.mul_div_cancel_left, mul_one, mul_zero]

Depends on / 依赖: Homotopic, IsUnit, Odd.neg_pow, PUnit.unit, Path.Homotopic.Quotient, Quotient, Quotient.instSubsingletonQuotient, Subsingleton, convert_to, div_pow, equation_of_Z_eq_zero, hP.left, hX.mul_div_cancel_left, instSubsingletonQuotient, isUnit_X_of_Z_eq_zero, mul_div_cancel_left, mul_one, mul_zero, neg_of_Z_eq_zero, neg_pow
-/
lemma neg_of_Z_eq_zero {P : Fin 3 -> F} (hP : W.Nonsingular P) (hPz : P z = 0) :
    W.neg P = -(P y / P x) • ![1, 1, 0] := by
have hX {n : Nat} : IsUnit P x ^ n := (isUnit_X_of_Z_eq_zero hP hPz).pow n
  erw [neg_of_Z_eq_zero' hPz, smul_fin3, neg_sq, div_pow, (equation_of_Z_eq_zero hPz).mp hP.left,
pow_succ, hX.mul_div_cancel_left, mul_one, Odd.neg_pow by decide, div_pow, pow_succ,
    (equation_of_Z_eq_zero hPz).mp hP.left, hX.mul_div_cancel_left, mul_one, mul_zero]

/--
lemma `neg_of_Z_ne_zero` / 引理 `neg_of_Z_ne_zero`

English:
lemma neg_of_Z_ne_zero
  given: {P : Fin 3 -> F} (hPz : P z != 0)
  proof: by
  rw [neg]; rw [smul_fin3]
  simp only [fin3_def_ext]
  rw [mul_div_cancel₀ _ <| pow_ne_zero 2 hPz]; rw [← negY_of_Z_ne_zero hPz]; rw [mul_div_cancel₀ _ pow_ne_zero 3 hPz]; rw [mul_one]

中文:
引理 neg_of_Z_ne_zero
  条件: {P : 有限集 3 -> F} (hPz : P z != 0)
  证明: by
  rw [neg]; rw [smul_fin3]
  simp only [fin3_def_ext]
  rw [mul_div_cancel₀ _ <| pow_ne_zero 2 hPz]; rw [← negY_of_Z_ne_zero hPz]; rw [mul_div_cancel₀ _ pow_ne_zero 3 hPz]; rw [mul_one]

Depends on / 依赖: fin3_def_ext, mul_one, negY_of_Z_ne_zero, pow_ne_zero, smul_fin3
-/
lemma neg_of_Z_ne_zero {P : Fin 3 -> F} (hPz : P z != 0) :
    W.neg P = P z • ![P x / P z ^ 2, W.toAffine.negY (P x / P z ^ 2) (P y / P z ^ 3), 1] := by
  rw [neg]; rw [smul_fin3]
  simp only [fin3_def_ext]
  rw [mul_div_cancel₀ _ <| pow_ne_zero 2 hPz]; rw [← negY_of_Z_ne_zero hPz]; rw [mul_div_cancel₀ _ pow_ne_zero 3 hPz]; rw [mul_one]

/--
lemma `nonsingular_neg_of_Z_ne_zero` / 引理 `nonsingular_neg_of_Z_ne_zero`

English:
lemma nonsingular_neg_of_Z_ne_zero
  given: {P : Fin 3 -> F} (hP : W.Nonsingular P) (hPz : P z != 0)
  proof: (nonsingular_some ..).mpr (Affine.nonsingular_neg ..).mpr
    (nonsingular_of_Z_ne_zero hPz).mp hP

中文:
引理 nonsingular_neg_of_Z_ne_zero
  条件: {P : 有限集 3 -> F} (hP : W.非奇异 P) (hPz : P z != 0)
  证明: (nonsingular_some ..).mpr (Affine.nonsingular_neg ..).mpr
    (nonsingular_of_Z_ne_zero hPz).mp hP
-/
private lemma nonsingular_neg_of_Z_ne_zero {P : Fin 3 -> F} (hP : W.Nonsingular P) (hPz : P z != 0) :
    W.Nonsingular ![P x / P z ^ 2, W.toAffine.negY (P x / P z ^ 2) (P y / P z ^ 3), 1] :=
(nonsingular_some ..).mpr (Affine.nonsingular_neg ..).mpr
    (nonsingular_of_Z_ne_zero hPz).mp hP

/--
lemma `nonsingular_neg` / 引理 `nonsingular_neg`

English:
lemma nonsingular_neg
  given: {P : Fin 3 -> F} (hP : W.Nonsingular P)
  statement: W.Nonsingular W.neg P
  proof: by
  by_cases hPz : P z = 0
  · simp only [neg_of_Z_eq_zero hP hPz, nonsingular_smul _
        ((isUnit_Y_of_Z_eq_zero hP hPz).div <| isUnit_X_of_Z_eq_zero hP hPz).neg, nonsingular_zero]
  · simp only [neg_of_Z_ne_zero hPz, nonsingular_smul _ <| Ne.isUnit hPz,
      nonsingular_neg_of_Z_ne_zero hP hPz]

中文:
引理 nonsingular_neg
  条件: {P : 有限集 3 -> F} (hP : W.非奇异 P)
  结论: W.非奇异 W.neg P
  证明: by
  by_cases hPz : P z = 0
  · simp only [neg_of_Z_eq_zero hP hPz, nonsingular_smul _
        ((isUnit_Y_of_Z_eq_zero hP hPz).div <| isUnit_X_of_Z_eq_zero hP hPz).neg, nonsingular_zero]
  · simp only [neg_of_Z_ne_zero hPz, nonsingular_smul _ <| Ne.isUnit hPz,
      nonsingular_neg_of_Z_ne_zero hP hPz]

Depends on / 依赖: Ne.isUnit, isUnit, isUnit_X_of_Z_eq_zero, isUnit_Y_of_Z_eq_zero, neg_of_Z_eq_zero, neg_of_Z_ne_zero, nonsingular_neg_of_Z_ne_zero, nonsingular_smul, nonsingular_zero
-/
lemma nonsingular_neg {P : Fin 3 -> F} (hP : W.Nonsingular P) : W.Nonsingular W.neg P := by
  by_cases hPz : P z = 0
  · simp only [neg_of_Z_eq_zero hP hPz, nonsingular_smul _
        ((isUnit_Y_of_Z_eq_zero hP hPz).div <| isUnit_X_of_Z_eq_zero hP hPz).neg, nonsingular_zero]
  · simp only [neg_of_Z_ne_zero hPz, nonsingular_smul _ <| Ne.isUnit hPz,
      nonsingular_neg_of_Z_ne_zero hP hPz]

/--
lemma `addZ_neg` / 引理 `addZ_neg`

English:
lemma addZ_neg
  given: (P : Fin 3 -> R)
  statement: addZ P (W'.neg P) = 0
  proof: addZ_of_X_eq rfl

中文:
引理 addZ_neg
  条件: (P : 有限集 3 -> R)
  结论: addZ P (W'.neg P) = 0
  证明: addZ_of_X_eq rfl

Depends on / 依赖: addZ_of_X_eq
-/
lemma addZ_neg (P : Fin 3 -> R) : addZ P (W'.neg P) = 0 :=
  addZ_of_X_eq rfl

/--
lemma `addX_neg` / 引理 `addX_neg`

English:
lemma addX_neg
  given: {P : Fin 3 -> R} (hP : W'.Equation P)
  statement: W'.addX P (W'.neg P) = W'.dblZ P ^ 2
  proof: by
  linear_combination (norm := (rw [addX, neg_X, neg_Y, neg_Z, dblZ, negY]; ring1))
    -2 * P z ^ 2 * (equation_iff _).mp hP

中文:
引理 addX_neg
  条件: {P : 有限集 3 -> R} (hP : W'.方程 P)
  结论: W'.addX P (W'.neg P) = W'.dblZ P ^ 2
  证明: by
  linear_combination (norm := (rw [addX, neg_X, neg_Y, neg_Z, dblZ, negY]; ring1))
    -2 * P z ^ 2 * (equation_iff _).mp hP

Depends on / 依赖: equation_iff, linear_combination, neg_X, neg_Y, neg_Z
-/
lemma addX_neg {P : Fin 3 -> R} (hP : W'.Equation P) : W'.addX P (W'.neg P) = W'.dblZ P ^ 2 := by
  linear_combination (norm := (rw [addX, neg_X, neg_Y, neg_Z, dblZ, negY]; ring1))
    -2 * P z ^ 2 * (equation_iff _).mp hP

/--
lemma `negAddY_neg` / 引理 `negAddY_neg`

English:
lemma negAddY_neg
  given: {P : Fin 3 -> R} (hP : W'.Equation P)
  proof: by
  linear_combination (norm := (rw [negAddY, neg_X, neg_Y, neg_Z, dblZ, negY]; ring1))
    -2 * P z ^ 3 * (P y - W'.negY P) * (equation_iff _).mp hP

中文:
引理 negAddY_neg
  条件: {P : 有限集 3 -> R} (hP : W'.方程 P)
  证明: by
  linear_combination (norm := (rw [negAddY, neg_X, neg_Y, neg_Z, dblZ, negY]; ring1))
    -2 * P z ^ 3 * (P y - W'.negY P) * (equation_iff _).mp hP

Depends on / 依赖: equation_iff, linear_combination, negAddY, neg_X, neg_Y, neg_Z
-/
lemma negAddY_neg {P : Fin 3 -> R} (hP : W'.Equation P) :
    W'.negAddY P (W'.neg P) = W'.dblZ P ^ 3 := by
  linear_combination (norm := (rw [negAddY, neg_X, neg_Y, neg_Z, dblZ, negY]; ring1))
    -2 * P z ^ 3 * (P y - W'.negY P) * (equation_iff _).mp hP

/--
lemma `addY_neg` / 引理 `addY_neg`

English:
lemma addY_neg
  given: {P : Fin 3 -> R} (hP : W'.Equation P)
  statement: W'.addY P (W'.neg P) = -W'.dblZ P ^ 3
  proof: by
  rw [addY]; rw [addX_neg hP]; rw [negAddY_neg hP]; rw [addZ_neg]; rw [negY_of_Z_eq_zero rfl]
  rfl

中文:
引理 addY_neg
  条件: {P : 有限集 3 -> R} (hP : W'.方程 P)
  结论: W'.addY P (W'.neg P) = -W'.dblZ P ^ 3
  证明: by
  rw [addY]; rw [addX_neg hP]; rw [negAddY_neg hP]; rw [addZ_neg]; rw [negY_of_Z_eq_zero rfl]
  rfl

Depends on / 依赖: addX_neg, addZ_neg, negAddY_neg, negY_of_Z_eq_zero
-/
lemma addY_neg {P : Fin 3 -> R} (hP : W'.Equation P) : W'.addY P (W'.neg P) = -W'.dblZ P ^ 3 := by
  rw [addY]; rw [addX_neg hP]; rw [negAddY_neg hP]; rw [addZ_neg]; rw [negY_of_Z_eq_zero rfl]
  rfl

/--
lemma `addXYZ_neg` / 引理 `addXYZ_neg`

English:
lemma addXYZ_neg
  given: {P : Fin 3 -> R} (hP : W'.Equation P)
  proof: by
  rw [addXYZ]; rw [addX_neg hP]; rw [addY_neg hP]; rw [addZ_neg]; rw [smul_fin3]
  simp +decide [fin3_def_ext, Odd.neg_pow]

中文:
引理 addXYZ_neg
  条件: {P : 有限集 3 -> R} (hP : W'.方程 P)
  证明: by
  rw [addXYZ]; rw [addX_neg hP]; rw [addY_neg hP]; rw [addZ_neg]; rw [smul_fin3]
  simp +decide [fin3_def_ext, Odd.neg_pow]

Depends on / 依赖: Odd.neg_pow, addXYZ, addX_neg, addY_neg, addZ_neg, fin3_def_ext, neg_pow, smul_fin3
-/
lemma addXYZ_neg {P : Fin 3 -> R} (hP : W'.Equation P) :
    W'.addXYZ P (W'.neg P) = -W'.dblZ P • ![1, 1, 0] := by
  rw [addXYZ]; rw [addX_neg hP]; rw [addY_neg hP]; rw [addZ_neg]; rw [smul_fin3]
  simp +decide [fin3_def_ext, Odd.neg_pow]

variable (W') in
/--
Definition of `negMap` / `negMap` 的定义

English:
definition negMap
  signature: (P : PointClass R)
  body: P.map W'.neg fun _ _ => neg_equiv

中文:
定义 negMap
  签名: (P : PointClass R)
  定义体: P.map W'.neg fun _ _ => neg_equiv

Depends on / 依赖: P.map, neg_equiv
-/
def negMap (P : PointClass R) : PointClass R :=
  P.map W'.neg fun _ _ => neg_equiv

/--
lemma `negMap_eq` / 引理 `negMap_eq`

English:
lemma negMap_eq
  given: (P : Fin 3 -> R)
  statement: W'.negMap ⟦P⟧ = ⟦W'.neg P⟧
  proof: rfl

中文:
引理 negMap_eq
  条件: (P : 有限集 3 -> R)
  结论: W'.negMap ⟦P⟧ = ⟦W'.neg P⟧
  证明: rfl
-/
lemma negMap_eq (P : Fin 3 -> R) : W'.negMap ⟦P⟧ = ⟦W'.neg P⟧ :=
  rfl

/--
lemma `negMap_of_Z_eq_zero` / 引理 `negMap_of_Z_eq_zero`

English:
lemma negMap_of_Z_eq_zero
  given: {P : Fin 3 -> F} (hP : W.Nonsingular P) (hPz : P z = 0)
  proof: by
  rw [negMap_eq]; rw [neg_of_Z_eq_zero hP hPz]; rw [smul_eq _ ((isUnit_Y_of_Z_eq_zero hP hPz).div <| isUnit_X_of_Z_eq_zero hP hPz).neg]

中文:
引理 negMap_of_Z_eq_zero
  条件: {P : 有限集 3 -> F} (hP : W.非奇异 P) (hPz : P z = 0)
  证明: by
  rw [negMap_eq]; rw [neg_of_Z_eq_zero hP hPz]; rw [smul_eq _ ((isUnit_Y_of_Z_eq_zero hP hPz).div <| isUnit_X_of_Z_eq_zero hP hPz).neg]

Depends on / 依赖: isUnit_X_of_Z_eq_zero, isUnit_Y_of_Z_eq_zero, negMap_eq, neg_of_Z_eq_zero, smul_eq
-/
lemma negMap_of_Z_eq_zero {P : Fin 3 -> F} (hP : W.Nonsingular P) (hPz : P z = 0) :
    W.negMap ⟦P⟧ = ⟦![1, 1, 0]⟧ := by
  rw [negMap_eq]; rw [neg_of_Z_eq_zero hP hPz]; rw [smul_eq _ ((isUnit_Y_of_Z_eq_zero hP hPz).div <| isUnit_X_of_Z_eq_zero hP hPz).neg]

/--
lemma `negMap_of_Z_ne_zero` / 引理 `negMap_of_Z_ne_zero`

English:
lemma negMap_of_Z_ne_zero
  given: {P : Fin 3 -> F} (hPz : P z != 0)
  proof: by
  rw [negMap_eq]; rw [neg_of_Z_ne_zero hPz]; rw [smul_eq _ <| Ne.isUnit hPz]

中文:
引理 negMap_of_Z_ne_zero
  条件: {P : 有限集 3 -> F} (hPz : P z != 0)
  证明: by
  rw [negMap_eq]; rw [neg_of_Z_ne_zero hPz]; rw [smul_eq _ <| Ne.isUnit hPz]

Depends on / 依赖: Ne.isUnit, isUnit, negMap_eq, neg_of_Z_ne_zero, smul_eq
-/
lemma negMap_of_Z_ne_zero {P : Fin 3 -> F} (hPz : P z != 0) :
    W.negMap ⟦P⟧ = ⟦![P x / P z ^ 2, W.toAffine.negY (P x / P z ^ 2) (P y / P z ^ 3), 1]⟧ := by
  rw [negMap_eq]; rw [neg_of_Z_ne_zero hPz]; rw [smul_eq _ <| Ne.isUnit hPz]

/--
lemma `nonsingularLift_negMap` / 引理 `nonsingularLift_negMap`

English:
lemma nonsingularLift_negMap
  given: {P : PointClass F} (hP : W.NonsingularLift P)
  proof: by
  rcases P with ⟨_⟩
  exact nonsingular_neg hP

中文:
引理 nonsingularLift_negMap
  条件: {P : PointClass F} (hP : W.NonsingularLift P)
  证明: by
  rcases P with ⟨_⟩
  exact nonsingular_neg hP

Depends on / 依赖: nonsingular_neg
-/
lemma nonsingularLift_negMap {P : PointClass F} (hP : W.NonsingularLift P) :
W.NonsingularLift W.negMap P := by
  rcases P with ⟨_⟩
  exact nonsingular_neg hP

/-! ## Addition on Jacobian point representatives -/

open scoped Classical in
variable (W') in
/--
Definition of `add` / `add` 的定义

English:
definition add
  signature: (P Q : Fin 3 -> R)
  body: if P ≈ Q then W'.dblXYZ P else W'.addXYZ P Q

中文:
定义 add
  签名: (P Q : 有限集 3 -> R)
  定义体: if P ≈ Q then W'.dblXYZ P else W'.addXYZ P Q

Depends on / 依赖: addXYZ, dblXYZ
-/
noncomputable def add (P Q : Fin 3 -> R) : Fin 3 -> R :=
  if P ≈ Q then W'.dblXYZ P else W'.addXYZ P Q

/--
lemma `add_of_equiv` / 引理 `add_of_equiv`

English:
lemma add_of_equiv
  given: {P Q : Fin 3 -> R} (h : P ≈ Q)
  statement: W'.add P Q = W'.dblXYZ P
  proof: if_pos h

中文:
引理 add_of_equiv
  条件: {P Q : 有限集 3 -> R} (h : P ≈ Q)
  结论: W'.add P Q = W'.dblXYZ P
  证明: if_pos h

Depends on / 依赖: if_pos
-/
lemma add_of_equiv {P Q : Fin 3 -> R} (h : P ≈ Q) : W'.add P Q = W'.dblXYZ P :=
  if_pos h

/--
lemma `add_smul_of_equiv` / 引理 `add_smul_of_equiv`

English:
lemma add_smul_of_equiv
  given: {P Q : Fin 3 -> R} (h : P ≈ Q) {u v : R} (hu : IsUnit u) (hv : IsUnit v)
  proof: by
  rw [add_of_equiv <| (smul_equiv_smul P Q hu hv).mpr h]; rw [dblXYZ_smul]; rw [add_of_equiv h]

中文:
引理 add_smul_of_equiv
  条件: {P Q : 有限集 3 -> R} (h : P ≈ Q) {u v : R} (hu : 是单位 u) (hv : 是单位 v)
  证明: by
  rw [add_of_equiv <| (smul_equiv_smul P Q hu hv).mpr h]; rw [dblXYZ_smul]; rw [add_of_equiv h]

Depends on / 依赖: add_of_equiv, dblXYZ_smul, smul_equiv_smul
-/
lemma add_smul_of_equiv {P Q : Fin 3 -> R} (h : P ≈ Q) {u v : R} (hu : IsUnit u) (hv : IsUnit v) :
    W'.add (u • P) (v • Q) = u ^ 4 • W'.add P Q := by
  rw [add_of_equiv <| (smul_equiv_smul P Q hu hv).mpr h]; rw [dblXYZ_smul]; rw [add_of_equiv h]

/--
lemma `add_self` / 引理 `add_self`

English:
lemma add_self
  given: (P : Fin 3 -> R)
  statement: W'.add P P = W'.dblXYZ P
  proof: add_of_equiv Setoid.refl _

中文:
引理 add_self
  条件: (P : 有限集 3 -> R)
  结论: W'.add P P = W'.dblXYZ P
  证明: add_of_equiv Setoid.refl _

Depends on / 依赖: Setoid, Setoid.refl, add_of_equiv
-/
lemma add_self (P : Fin 3 -> R) : W'.add P P = W'.dblXYZ P :=
add_of_equiv Setoid.refl _

/--
lemma `add_of_eq` / 引理 `add_of_eq`

English:
lemma add_of_eq
  given: {P Q : Fin 3 -> R} (h : P = Q)
  statement: W'.add P Q = W'.dblXYZ P
  proof: h ▸ add_self P

中文:
引理 add_of_eq
  条件: {P Q : 有限集 3 -> R} (h : P = Q)
  结论: W'.add P Q = W'.dblXYZ P
  证明: h ▸ add_self P

Depends on / 依赖: add_self
-/
lemma add_of_eq {P Q : Fin 3 -> R} (h : P = Q) : W'.add P Q = W'.dblXYZ P :=
  h ▸ add_self P

/--
lemma `add_of_not_equiv` / 引理 `add_of_not_equiv`

English:
lemma add_of_not_equiv
  given: {P Q : Fin 3 -> R} (h : ¬P ≈ Q)
  statement: W'.add P Q = W'.addXYZ P Q
  proof: if_neg h

中文:
引理 add_of_not_equiv
  条件: {P Q : 有限集 3 -> R} (h : ¬P ≈ Q)
  结论: W'.add P Q = W'.addXYZ P Q
  证明: if_neg h

Depends on / 依赖: if_neg
-/
lemma add_of_not_equiv {P Q : Fin 3 -> R} (h : ¬P ≈ Q) : W'.add P Q = W'.addXYZ P Q :=
  if_neg h

/--
lemma `add_smul_of_not_equiv` / 引理 `add_smul_of_not_equiv`

English:
lemma add_smul_of_not_equiv
  statement: {P Q : Fin 3 -> R} (h : ¬P ≈ Q) {u v : R} (hu : IsUnit u)
  proof: by
  rw [add_of_not_equiv <| h.comp (smul_equiv_smul P Q hu hv).mp]; rw [addXYZ_smul]; rw [add_of_not_equiv h]

中文:
引理 add_smul_of_not_equiv
  结论: {P Q : 有限集 3 -> R} (h : ¬P ≈ Q) {u v : R} (hu : 是单位 u)
  证明: by
  rw [add_of_not_equiv <| h.comp (smul_equiv_smul P Q hu hv).mp]; rw [addXYZ_smul]; rw [add_of_not_equiv h]

Depends on / 依赖: addXYZ_smul, add_of_not_equiv, h.comp, smul_equiv_smul
-/
lemma add_smul_of_not_equiv {P Q : Fin 3 -> R} (h : ¬P ≈ Q) {u v : R} (hu : IsUnit u)
    (hv : IsUnit v) : W'.add (u • P) (v • Q) = (u * v) ^ 2 • W'.add P Q := by
  rw [add_of_not_equiv <| h.comp (smul_equiv_smul P Q hu hv).mp]; rw [addXYZ_smul]; rw [add_of_not_equiv h]

/--
lemma `add_smul_equiv` / 引理 `add_smul_equiv`

English:
lemma add_smul_equiv
  given: (P Q : Fin 3 -> R) {u v : R} (hu : IsUnit u) (hv : IsUnit v)
  proof: by
  by_cases h : P ≈ Q
  · exact ⟨hu.unit ^ 4, by convert! (add_smul_of_equiv h hu hv).symm⟩
  · exact ⟨(hu.unit * hv.unit) ^ 2, by convert! (add_smul_of_not_equiv h hu hv).symm⟩

中文:
引理 add_smul_equiv
  条件: (P Q : 有限集 3 -> R) {u v : R} (hu : 是单位 u) (hv : 是单位 v)
  证明: by
  by_cases h : P ≈ Q
  · exact ⟨hu.unit ^ 4, by convert! (add_smul_of_equiv h hu hv).symm⟩
  · exact ⟨(hu.unit * hv.unit) ^ 2, by convert! (add_smul_of_not_equiv h hu hv).symm⟩

Depends on / 依赖: Nonempty, Nonempty.some, Unique, Unique.instSubsingleton, add_smul_of_equiv, add_smul_of_not_equiv, convert, hu.unit, hv.unit, instSubsingleton, simply_connected_iff_unique_homotopic
-/
lemma add_smul_equiv (P Q : Fin 3 -> R) {u v : R} (hu : IsUnit u) (hv : IsUnit v) :
    W'.add (u • P) (v • Q) ≈ W'.add P Q := by
  by_cases h : P ≈ Q
  · exact ⟨hu.unit ^ 4, by convert! (add_smul_of_equiv h hu hv).symm⟩
  · exact ⟨(hu.unit * hv.unit) ^ 2, by convert! (add_smul_of_not_equiv h hu hv).symm⟩

/--
lemma `add_equiv` / 引理 `add_equiv`

English:
lemma add_equiv
  given: {P P' Q Q' : Fin 3 -> R} (hP : P ≈ P') (hQ : Q ≈ Q')
  proof: by
  rcases hP, hQ with ⟨⟨u, rfl⟩, ⟨v, rfl⟩⟩
  exact add_smul_equiv P' Q' u.isUnit v.isUnit

中文:
引理 add_equiv
  条件: {P P' Q Q' : 有限集 3 -> R} (hP : P ≈ P') (hQ : Q ≈ Q')
  证明: by
  rcases hP, hQ with ⟨⟨u, rfl⟩, ⟨v, rfl⟩⟩
  exact add_smul_equiv P' Q' u.isUnit v.isUnit

Depends on / 依赖: Homotopic, Path.Homotopic.Quotient, Quotient, Subsingleton, add_smul_equiv, isUnit, u.isUnit, v.isUnit
-/
lemma add_equiv {P P' Q Q' : Fin 3 -> R} (hP : P ≈ P') (hQ : Q ≈ Q') :
    W'.add P Q ≈ W'.add P' Q' := by
  rcases hP, hQ with ⟨⟨u, rfl⟩, ⟨v, rfl⟩⟩
  exact add_smul_equiv P' Q' u.isUnit v.isUnit

/--
lemma `add_of_Z_eq_zero` / 引理 `add_of_Z_eq_zero`

English:
lemma add_of_Z_eq_zero
  statement: {P Q : Fin 3 -> F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q)
  proof: by
  rw [add_of_equiv <| equiv_of_Z_eq_zero hP hQ hPz hQz]; rw [dblXYZ_of_Z_eq_zero hP.left hPz]

中文:
引理 add_of_Z_eq_zero
  结论: {P Q : 有限集 3 -> F} (hP : W.非奇异 P) (hQ : W.非奇异 Q)
  证明: by
  rw [add_of_equiv <| equiv_of_Z_eq_zero hP hQ hPz hQz]; rw [dblXYZ_of_Z_eq_zero hP.left hPz]

Depends on / 依赖: PathConnectedSpace, add_of_equiv, dblXYZ_of_Z_eq_zero, equiv_of_Z_eq_zero, hP.left
-/
lemma add_of_Z_eq_zero {P Q : Fin 3 -> F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q)
    (hPz : P z = 0) (hQz : Q z = 0) : W.add P Q = P x ^ 2 • ![1, 1, 0] := by
  rw [add_of_equiv <| equiv_of_Z_eq_zero hP hQ hPz hQz]; rw [dblXYZ_of_Z_eq_zero hP.left hPz]

/--
lemma `add_of_Z_eq_zero_left` / 引理 `add_of_Z_eq_zero_left`

English:
lemma add_of_Z_eq_zero_left
  given: {P Q : Fin 3 -> R} (hP : W'.Equation P) (hPz : P z = 0) (hQz : Q z != 0)
  proof: by
  rw [add_of_not_equiv <| not_equiv_of_Z_eq_zero_left hPz hQz]; rw [addXYZ_of_Z_eq_zero_left hP hPz]

中文:
引理 add_of_Z_eq_zero_left
  条件: {P Q : 有限集 3 -> R} (hP : W'.方程 P) (hPz : P z = 0) (hQz : Q z != 0)
  证明: by
  rw [add_of_not_equiv <| not_equiv_of_Z_eq_zero_left hPz hQz]; rw [addXYZ_of_Z_eq_zero_left hP hPz]

Depends on / 依赖: addXYZ_of_Z_eq_zero_left, add_of_not_equiv, not_equiv_of_Z_eq_zero_left
-/
lemma add_of_Z_eq_zero_left {P Q : Fin 3 -> R} (hP : W'.Equation P) (hPz : P z = 0) (hQz : Q z != 0) :
    W'.add P Q = (P x * Q z) • Q := by
  rw [add_of_not_equiv <| not_equiv_of_Z_eq_zero_left hPz hQz]; rw [addXYZ_of_Z_eq_zero_left hP hPz]

/--
lemma `add_of_Z_eq_zero_right` / 引理 `add_of_Z_eq_zero_right`

English:
lemma add_of_Z_eq_zero_right
  statement: {P Q : Fin 3 -> R} (hQ : W'.Equation Q) (hPz : P z != 0)
  proof: by
  rw [add_of_not_equiv <| not_equiv_of_Z_eq_zero_right hPz hQz]; rw [addXYZ_of_Z_eq_zero_right hQ hQz]

中文:
引理 add_of_Z_eq_zero_right
  结论: {P Q : 有限集 3 -> R} (hQ : W'.方程 Q) (hPz : P z != 0)
  证明: by
  rw [add_of_not_equiv <| not_equiv_of_Z_eq_zero_right hPz hQz]; rw [addXYZ_of_Z_eq_zero_right hQ hQz]

Depends on / 依赖: ContractibleSpace, TopologicalSpace, addXYZ_of_Z_eq_zero_right, add_of_not_equiv, not_equiv_of_Z_eq_zero_right, ofContractible
-/
lemma add_of_Z_eq_zero_right {P Q : Fin 3 -> R} (hQ : W'.Equation Q) (hPz : P z != 0)
    (hQz : Q z = 0) : W'.add P Q = -(Q x * P z) • P := by
  rw [add_of_not_equiv <| not_equiv_of_Z_eq_zero_right hPz hQz]; rw [addXYZ_of_Z_eq_zero_right hQ hQz]

/--
lemma `add_of_Y_eq` / 引理 `add_of_Y_eq`

English:
lemma add_of_Y_eq
  statement: {P Q : Fin 3 -> F} (hPz : P z != 0) (hQz : Q z != 0)
  proof: by
  rw [add_of_equiv <| equiv_of_X_eq_of_Y_eq hPz hQz hx hy]; rw [dblXYZ_of_Y_eq hQz hx hy hy']

中文:
引理 add_of_Y_eq
  结论: {P Q : 有限集 3 -> F} (hPz : P z != 0) (hQz : Q z != 0)
  证明: by
  rw [add_of_equiv <| equiv_of_X_eq_of_Y_eq hPz hQz hx hy]; rw [dblXYZ_of_Y_eq hQz hx hy hy']

Depends on / 依赖: add_of_equiv, dblXYZ_of_Y_eq, equiv_of_X_eq_of_Y_eq
-/
lemma add_of_Y_eq {P Q : Fin 3 -> F} (hPz : P z != 0) (hQz : Q z != 0)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y * Q z ^ 3 = Q y * P z ^ 3)
    (hy' : P y * Q z ^ 3 = W.negY Q * P z ^ 3) : W.add P Q = W.dblU P • ![1, 1, 0] := by
  rw [add_of_equiv <| equiv_of_X_eq_of_Y_eq hPz hQz hx hy]; rw [dblXYZ_of_Y_eq hQz hx hy hy']

/--
lemma `add_of_Y_ne` / 引理 `add_of_Y_ne`

English:
lemma add_of_Y_ne
  statement: {P Q : Fin 3 -> F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z != 0)
  proof: by
  rw [add_of_not_equiv <| not_equiv_of_Y_ne hy]; rw [addXYZ_of_X_eq hP hQ hPz hQz hx]

中文:
引理 add_of_Y_ne
  结论: {P Q : 有限集 3 -> F} (hP : W.方程 P) (hQ : W.方程 Q) (hPz : P z != 0)
  证明: by
  rw [add_of_not_equiv <| not_equiv_of_Y_ne hy]; rw [addXYZ_of_X_eq hP hQ hPz hQz hx]

Depends on / 依赖: addXYZ_of_X_eq, add_of_not_equiv, not_equiv_of_Y_ne
-/
lemma add_of_Y_ne {P Q : Fin 3 -> F} (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z != 0)
    (hQz : Q z != 0) (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y * Q z ^ 3 != Q y * P z ^ 3) :
    W.add P Q = addU P Q • ![1, 1, 0] := by
  rw [add_of_not_equiv <| not_equiv_of_Y_ne hy]; rw [addXYZ_of_X_eq hP hQ hPz hQz hx]

/--
lemma `add_of_Y_ne'` / 引理 `add_of_Y_ne'`

English:
lemma add_of_Y_ne'
  statement: [DecidableEq F] {P Q : Fin 3 -> F}
  proof: by
  rw [add_of_equiv <| equiv_of_X_eq_of_Y_eq hPz hQz hx <| Y_eq_of_Y_ne' hP hQ hx hy]; rw [dblXYZ_of_Z_ne_zero hP hQ hPz hQz hx hy]

中文:
引理 add_of_Y_ne'
  结论: [DecidableEq F] {P Q : 有限集 3 -> F}
  证明: by
  rw [add_of_equiv <| equiv_of_X_eq_of_Y_eq hPz hQz hx <| Y_eq_of_Y_ne' hP hQ hx hy]; rw [dblXYZ_of_Z_ne_zero hP hQ hPz hQz hx hy]

Depends on / 依赖: Y_eq_of_Y_ne, add_of_equiv, dblXYZ_of_Z_ne_zero, equiv_of_X_eq_of_Y_eq
-/
lemma add_of_Y_ne' [DecidableEq F] {P Q : Fin 3 -> F}
    (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z != 0) (hQz : Q z != 0)
    (hx : P x * Q z ^ 2 = Q x * P z ^ 2) (hy : P y * Q z ^ 3 != W.negY Q * P z ^ 3) :
    W.add P Q = W.dblZ P •
      ![W.toAffine.addX (P x / P z ^ 2) (Q x / Q z ^ 2)
          (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)),
        W.toAffine.addY (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3)
          (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)),
        1] := by
  rw [add_of_equiv <| equiv_of_X_eq_of_Y_eq hPz hQz hx <| Y_eq_of_Y_ne' hP hQ hx hy]; rw [dblXYZ_of_Z_ne_zero hP hQ hPz hQz hx hy]

/--
lemma `add_of_X_ne` / 引理 `add_of_X_ne`

English:
lemma add_of_X_ne
  statement: [DecidableEq F] {P Q : Fin 3 -> F} (hP : W.Equation P) (hQ : W.Equation Q)
  proof: by
  rw [add_of_not_equiv <| not_equiv_of_X_ne hx]; rw [addXYZ_of_Z_ne_zero hP hQ hPz hQz hx]

中文:
引理 add_of_X_ne
  结论: [DecidableEq F] {P Q : 有限集 3 -> F} (hP : W.方程 P) (hQ : W.方程 Q)
  证明: by
  rw [add_of_not_equiv <| not_equiv_of_X_ne hx]; rw [addXYZ_of_Z_ne_zero hP hQ hPz hQz hx]

Depends on / 依赖: addXYZ_of_Z_ne_zero, add_of_not_equiv, not_equiv_of_X_ne
-/
lemma add_of_X_ne [DecidableEq F] {P Q : Fin 3 -> F} (hP : W.Equation P) (hQ : W.Equation Q)
    (hPz : P z != 0) (hQz : Q z != 0) (hx : P x * Q z ^ 2 != Q x * P z ^ 2) : W.add P Q = addZ P Q •
      ![W.toAffine.addX (P x / P z ^ 2) (Q x / Q z ^ 2)
          (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)),
        W.toAffine.addY (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3)
          (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)),
        1] := by
  rw [add_of_not_equiv <| not_equiv_of_X_ne hx]; rw [addXYZ_of_Z_ne_zero hP hQ hPz hQz hx]

/--
lemma `nonsingular_add_of_Z_ne_zero` / 引理 `nonsingular_add_of_Z_ne_zero`

English:
lemma nonsingular_add_of_Z_ne_zero
  statement: [DecidableEq F] {P Q : Fin 3 -> F} (hP : W.Nonsingular P)
  proof: (nonsingular_some ..).mpr Affine.nonsingular_add ((nonsingular_of_Z_ne_zero hPz).mp hP)
((nonsingular_of_Z_ne_zero hQz).mp hQ) by rwa [← X_eq_iff hPz hQz, ← Y_eq_iff' hPz hQz]

中文:
引理 nonsingular_add_of_Z_ne_zero
  结论: [DecidableEq F] {P Q : 有限集 3 -> F} (hP : W.非奇异 P)
  证明: (nonsingular_some ..).mpr Affine.nonsingular_add ((nonsingular_of_Z_ne_zero hPz).mp hP)
((nonsingular_of_Z_ne_zero hQz).mp hQ) by rwa [← X_eq_iff hPz hQz, ← Y_eq_iff' hPz hQz]
-/
private lemma nonsingular_add_of_Z_ne_zero [DecidableEq F] {P Q : Fin 3 -> F} (hP : W.Nonsingular P)
    (hQ : W.Nonsingular Q) (hPz : P z != 0) (hQz : Q z != 0)
    (hxy : ¬(P x * Q z ^ 2 = Q x * P z ^ 2 ∧ P y * Q z ^ 3 = W.negY Q * P z ^ 3)) : W.Nonsingular
      ![W.toAffine.addX (P x / P z ^ 2) (Q x / Q z ^ 2)
          (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)),
        W.toAffine.addY (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3)
          (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)), 1] :=
(nonsingular_some ..).mpr Affine.nonsingular_add ((nonsingular_of_Z_ne_zero hPz).mp hP)
((nonsingular_of_Z_ne_zero hQz).mp hQ) by rwa [← X_eq_iff hPz hQz, ← Y_eq_iff' hPz hQz]

/--
lemma `nonsingular_add` / 引理 `nonsingular_add`

English:
lemma nonsingular_add
  given: {P Q : Fin 3 -> F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q)
  proof: by
  by_cases hPz : P z = 0
  · by_cases hQz : Q z = 0
    · simp only [add_of_Z_eq_zero hP hQ hPz hQz,
nonsingular_smul _ (isUnit_X_of_Z_eq_zero hP hPz).pow 2, nonsingular_zero]
    · simpa only [add_of_Z_eq_zero_left hP.left hPz hQz,
nonsingular_smul _ (isUnit_X_of_Z_eq_zero hP hPz).mul Ne.isUnit hQz]
  · by_cases hQz : Q z = 0
    · simpa only [add_of_Z_eq_zero_right hQ.left hPz hQz,
        nonsingular_smul _ ((isUnit_X_of_Z_eq_zero hQ hQz).mul <| Ne.isUnit hPz).neg]
    · by_cases hxy : P x * Q z ^ 2 = Q x * P z ^ 2 ∧ P y * Q z ^ 3 = W.negY Q * P z ^ 3
      · by_cases hy : P y * Q z ^ 3 = Q y * P z ^ 3
        · simp only [add_of_Y_eq hPz hQz hxy.left hy hxy.right, nonsingular_smul _ <|
              isUnit_dblU_of_Y_eq hP hPz hQz hxy.left hy hxy.right, nonsingular_zero]
        · simp only [add_of_Y_ne hP.left hQ.left hPz hQz hxy.left hy,
nonsingular_smul _ isUnit_addU_of_Y_ne hPz hQz hy, nonsingular_zero]
      · classical
        have := nonsingular_add_of_Z_ne_zero hP hQ hPz hQz hxy
        by_cases hx : P x * Q z ^ 2 = Q x * P z ^ 2
        · simpa only [add_of_Y_ne' hP.left hQ.left hPz hQz hx <| not_and.mp hxy hx,
nonsingular_smul _ isUnit_dblZ_of_Y_ne' hP.left hQ.left hPz hx not_and.mp hxy hx]
        · simpa only [add_of_X_ne hP.left hQ.left hPz hQz hx,
nonsingular_smul _ isUnit_addZ_of_X_ne hx]

中文:
引理 nonsingular_add
  条件: {P Q : 有限集 3 -> F} (hP : W.非奇异 P) (hQ : W.非奇异 Q)
  证明: by
  by_cases hPz : P z = 0
  · by_cases hQz : Q z = 0
    · simp only [add_of_Z_eq_zero hP hQ hPz hQz,
nonsingular_smul _ (isUnit_X_of_Z_eq_zero hP hPz).pow 2, nonsingular_zero]
    · simpa only [add_of_Z_eq_zero_left hP.left hPz hQz,
nonsingular_smul _ (isUnit_X_of_Z_eq_zero hP hPz).mul Ne.isUnit hQz]
  · by_cases hQz : Q z = 0
    · simpa only [add_of_Z_eq_zero_right hQ.left hPz hQz,
        nonsingular_smul _ ((isUnit_X_of_Z_eq_zero hQ hQz).mul <| Ne.isUnit hPz).neg]
    · by_cases hxy : P x * Q z ^ 2 = Q x * P z ^ 2 ∧ P y * Q z ^ 3 = W.negY Q * P z ^ 3
      · by_cases hy : P y * Q z ^ 3 = Q y * P z ^ 3
        · simp only [add_of_Y_eq hPz hQz hxy.left hy hxy.right, nonsingular_smul _ <|
              isUnit_dblU_of_Y_eq hP hPz hQz hxy.left hy hxy.right, nonsingular_zero]
        · simp only [add_of_Y_ne hP.left hQ.left hPz hQz hxy.left hy,
nonsingular_smul _ isUnit_addU_of_Y_ne hPz hQz hy, nonsingular_zero]
      · classical
        have := nonsingular_add_of_Z_ne_zero hP hQ hPz hQz hxy
        by_cases hx : P x * Q z ^ 2 = Q x * P z ^ 2
        · simpa only [add_of_Y_ne' hP.left hQ.left hPz hQz hx <| not_and.mp hxy hx,
nonsingular_smul _ isUnit_dblZ_of_Y_ne' hP.left hQ.left hPz hx not_and.mp hxy hx]
        · simpa only [add_of_X_ne hP.left hQ.left hPz hQz hx,
nonsingular_smul _ isUnit_addZ_of_X_ne hx]

Depends on / 依赖: Ne.isUnit, add_of_Z_eq_zero, add_of_Z_eq_zero_left, add_of_Z_eq_zero_right, hP.left, hQ.left, isUnit, isUnit_X_of_Z_eq_zero, nonsingular_smul, nonsingular_zero
-/
lemma nonsingular_add {P Q : Fin 3 -> F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q) :
W.Nonsingular W.add P Q := by
  by_cases hPz : P z = 0
  · by_cases hQz : Q z = 0
    · simp only [add_of_Z_eq_zero hP hQ hPz hQz,
nonsingular_smul _ (isUnit_X_of_Z_eq_zero hP hPz).pow 2, nonsingular_zero]
    · simpa only [add_of_Z_eq_zero_left hP.left hPz hQz,
nonsingular_smul _ (isUnit_X_of_Z_eq_zero hP hPz).mul Ne.isUnit hQz]
  · by_cases hQz : Q z = 0
    · simpa only [add_of_Z_eq_zero_right hQ.left hPz hQz,
        nonsingular_smul _ ((isUnit_X_of_Z_eq_zero hQ hQz).mul <| Ne.isUnit hPz).neg]
    · by_cases hxy : P x * Q z ^ 2 = Q x * P z ^ 2 ∧ P y * Q z ^ 3 = W.negY Q * P z ^ 3
      · by_cases hy : P y * Q z ^ 3 = Q y * P z ^ 3
        · simp only [add_of_Y_eq hPz hQz hxy.left hy hxy.right, nonsingular_smul _ <|
              isUnit_dblU_of_Y_eq hP hPz hQz hxy.left hy hxy.right, nonsingular_zero]
        · simp only [add_of_Y_ne hP.left hQ.left hPz hQz hxy.left hy,
nonsingular_smul _ isUnit_addU_of_Y_ne hPz hQz hy, nonsingular_zero]
      · classical
        have := nonsingular_add_of_Z_ne_zero hP hQ hPz hQz hxy
        by_cases hx : P x * Q z ^ 2 = Q x * P z ^ 2
        · simpa only [add_of_Y_ne' hP.left hQ.left hPz hQz hx <| not_and.mp hxy hx,
nonsingular_smul _ isUnit_dblZ_of_Y_ne' hP.left hQ.left hPz hx not_and.mp hxy hx]
        · simpa only [add_of_X_ne hP.left hQ.left hPz hQz hx,
nonsingular_smul _ isUnit_addZ_of_X_ne hx]

variable (W') in
/--
Definition of `addMap` / `addMap` 的定义

English:
definition addMap
  signature: (P Q : PointClass R)
  body: Quotient.map₂ W'.add (fun _ _ hP _ _ hQ => add_equiv hP hQ) P Q

中文:
定义 addMap
  签名: (P Q : PointClass R)
  定义体: Quotient.map₂ W'.add (fun _ _ hP _ _ hQ => add_equiv hP hQ) P Q

Depends on / 依赖: Quotient, Quotient.map, add_equiv
-/
noncomputable def addMap (P Q : PointClass R) : PointClass R :=
  Quotient.map₂ W'.add (fun _ _ hP _ _ hQ => add_equiv hP hQ) P Q

/--
lemma `addMap_eq` / 引理 `addMap_eq`

English:
lemma addMap_eq
  given: (P Q : Fin 3 -> R)
  statement: W'.addMap ⟦P⟧ ⟦Q⟧ = ⟦W'.add P Q⟧
  proof: rfl

中文:
引理 addMap_eq
  条件: (P Q : 有限集 3 -> R)
  结论: W'.addMap ⟦P⟧ ⟦Q⟧ = ⟦W'.add P Q⟧
  证明: rfl
-/
lemma addMap_eq (P Q : Fin 3 -> R) : W'.addMap ⟦P⟧ ⟦Q⟧ = ⟦W'.add P Q⟧ :=
  rfl

/--
lemma `addMap_of_Z_eq_zero_left` / 引理 `addMap_of_Z_eq_zero_left`

English:
lemma addMap_of_Z_eq_zero_left
  statement: {P : Fin 3 -> F} {Q : PointClass F} (hP : W.Nonsingular P)
  proof: by
  revert hQ
  refine Q.inductionOn (motive := fun Q => _ -> W.addMap _ Q = Q) fun Q hQ => ?_
  by_cases hQz : Q z = 0
  · rw [addMap_eq, add_of_Z_eq_zero hP hQ hPz hQz,
smul_eq _ (isUnit_X_of_Z_eq_zero hP hPz).pow 2, Quotient.eq]
exact Setoid.symm equiv_zero_of_Z_eq_zero hQ hQz
  · rw [addMap_eq, add_of_Z_eq_zero_left hP.left hPz hQz,
smul_eq _ (isUnit_X_of_Z_eq_zero hP hPz).mul Ne.isUnit hQz]

中文:
引理 addMap_of_Z_eq_zero_left
  结论: {P : 有限集 3 -> F} {Q : PointClass F} (hP : W.非奇异 P)
  证明: by
  revert hQ
  refine Q.inductionOn (motive := fun Q => _ -> W.addMap _ Q = Q) fun Q hQ => ?_
  by_cases hQz : Q z = 0
  · rw [addMap_eq, add_of_Z_eq_zero hP hQ hPz hQz,
smul_eq _ (isUnit_X_of_Z_eq_zero hP hPz).pow 2, Quotient.eq]
exact Setoid.symm equiv_zero_of_Z_eq_zero hQ hQz
  · rw [addMap_eq, add_of_Z_eq_zero_left hP.left hPz hQz,
smul_eq _ (isUnit_X_of_Z_eq_zero hP hPz).mul Ne.isUnit hQz]

Depends on / 依赖: Ne.isUnit, Q.inductionOn, Quotient, Quotient.eq, Setoid, Setoid.symm, W.addMap, addMap, addMap_eq, add_of_Z_eq_zero, add_of_Z_eq_zero_left, equiv_zero_of_Z_eq_zero, hP.left, inductionOn, isUnit, isUnit_X_of_Z_eq_zero, motive, revert, smul_eq
-/
lemma addMap_of_Z_eq_zero_left {P : Fin 3 -> F} {Q : PointClass F} (hP : W.Nonsingular P)
    (hQ : W.NonsingularLift Q) (hPz : P z = 0) : W.addMap ⟦P⟧ Q = Q := by
  revert hQ
  refine Q.inductionOn (motive := fun Q => _ -> W.addMap _ Q = Q) fun Q hQ => ?_
  by_cases hQz : Q z = 0
  · rw [addMap_eq, add_of_Z_eq_zero hP hQ hPz hQz,
smul_eq _ (isUnit_X_of_Z_eq_zero hP hPz).pow 2, Quotient.eq]
exact Setoid.symm equiv_zero_of_Z_eq_zero hQ hQz
  · rw [addMap_eq, add_of_Z_eq_zero_left hP.left hPz hQz,
smul_eq _ (isUnit_X_of_Z_eq_zero hP hPz).mul Ne.isUnit hQz]

/--
lemma `addMap_of_Z_eq_zero_right` / 引理 `addMap_of_Z_eq_zero_right`

English:
lemma addMap_of_Z_eq_zero_right
  statement: {P : PointClass F} {Q : Fin 3 -> F} (hP : W.NonsingularLift P)
  proof: by
  revert hP
  refine P.inductionOn (motive := fun P => _ -> W.addMap P _ = P) fun P hP => ?_
  by_cases hPz : P z = 0
  · rw [addMap_eq, add_of_Z_eq_zero hP hQ hPz hQz,
smul_eq _ (isUnit_X_of_Z_eq_zero hP hPz).pow 2, Quotient.eq]
exact Setoid.symm equiv_zero_of_Z_eq_zero hP hPz
  · rw [addMap_eq, add_of_Z_eq_zero_right hQ.left hPz hQz,
      smul_eq _ ((isUnit_X_of_Z_eq_zero hQ hQz).mul <| Ne.isUnit hPz).neg]

中文:
引理 addMap_of_Z_eq_zero_right
  结论: {P : PointClass F} {Q : 有限集 3 -> F} (hP : W.NonsingularLift P)
  证明: by
  revert hP
  refine P.inductionOn (motive := fun P => _ -> W.addMap P _ = P) fun P hP => ?_
  by_cases hPz : P z = 0
  · rw [addMap_eq, add_of_Z_eq_zero hP hQ hPz hQz,
smul_eq _ (isUnit_X_of_Z_eq_zero hP hPz).pow 2, Quotient.eq]
exact Setoid.symm equiv_zero_of_Z_eq_zero hP hPz
  · rw [addMap_eq, add_of_Z_eq_zero_right hQ.left hPz hQz,
      smul_eq _ ((isUnit_X_of_Z_eq_zero hQ hQz).mul <| Ne.isUnit hPz).neg]

Depends on / 依赖: Ne.isUnit, P.inductionOn, Quotient, Quotient.eq, Setoid, Setoid.symm, W.addMap, addMap, addMap_eq, add_of_Z_eq_zero, add_of_Z_eq_zero_right, equiv_zero_of_Z_eq_zero, hQ.left, inductionOn, isUnit, isUnit_X_of_Z_eq_zero, motive, revert, smul_eq
-/
lemma addMap_of_Z_eq_zero_right {P : PointClass F} {Q : Fin 3 -> F} (hP : W.NonsingularLift P)
    (hQ : W.Nonsingular Q) (hQz : Q z = 0) : W.addMap P ⟦Q⟧ = P := by
  revert hP
  refine P.inductionOn (motive := fun P => _ -> W.addMap P _ = P) fun P hP => ?_
  by_cases hPz : P z = 0
  · rw [addMap_eq, add_of_Z_eq_zero hP hQ hPz hQz,
smul_eq _ (isUnit_X_of_Z_eq_zero hP hPz).pow 2, Quotient.eq]
exact Setoid.symm equiv_zero_of_Z_eq_zero hP hPz
  · rw [addMap_eq, add_of_Z_eq_zero_right hQ.left hPz hQz,
      smul_eq _ ((isUnit_X_of_Z_eq_zero hQ hQz).mul <| Ne.isUnit hPz).neg]

/--
lemma `addMap_of_Y_eq` / 引理 `addMap_of_Y_eq`

English:
lemma addMap_of_Y_eq
  statement: {P Q : Fin 3 -> F} (hP : W.Nonsingular P) (hQ : W.Equation Q) (hPz : P z != 0)
  proof: by
  by_cases hy : P y * Q z ^ 3 = Q y * P z ^ 3
  · rw [addMap_eq, add_of_Y_eq hPz hQz hx hy hy',
smul_eq _ isUnit_dblU_of_Y_eq hP hPz hQz hx hy hy']
  · rw [addMap_eq, add_of_Y_ne hP.left hQ hPz hQz hx hy,
smul_eq _ isUnit_addU_of_Y_ne hPz hQz hy]

中文:
引理 addMap_of_Y_eq
  结论: {P Q : 有限集 3 -> F} (hP : W.非奇异 P) (hQ : W.方程 Q) (hPz : P z != 0)
  证明: by
  by_cases hy : P y * Q z ^ 3 = Q y * P z ^ 3
  · rw [addMap_eq, add_of_Y_eq hPz hQz hx hy hy',
smul_eq _ isUnit_dblU_of_Y_eq hP hPz hQz hx hy hy']
  · rw [addMap_eq, add_of_Y_ne hP.left hQ hPz hQz hx hy,
smul_eq _ isUnit_addU_of_Y_ne hPz hQz hy]

Depends on / 依赖: addMap_eq, add_of_Y_eq, add_of_Y_ne, hP.left, isUnit_addU_of_Y_ne, isUnit_dblU_of_Y_eq, smul_eq
-/
lemma addMap_of_Y_eq {P Q : Fin 3 -> F} (hP : W.Nonsingular P) (hQ : W.Equation Q) (hPz : P z != 0)
    (hQz : Q z != 0) (hx : P x * Q z ^ 2 = Q x * P z ^ 2)
    (hy' : P y * Q z ^ 3 = W.negY Q * P z ^ 3) : W.addMap ⟦P⟧ ⟦Q⟧ = ⟦![1, 1, 0]⟧ := by
  by_cases hy : P y * Q z ^ 3 = Q y * P z ^ 3
  · rw [addMap_eq, add_of_Y_eq hPz hQz hx hy hy',
smul_eq _ isUnit_dblU_of_Y_eq hP hPz hQz hx hy hy']
  · rw [addMap_eq, add_of_Y_ne hP.left hQ hPz hQz hx hy,
smul_eq _ isUnit_addU_of_Y_ne hPz hQz hy]

/--
lemma `addMap_of_Z_ne_zero` / 引理 `addMap_of_Z_ne_zero`

English:
lemma addMap_of_Z_ne_zero
  statement: [DecidableEq F] {P Q : Fin 3 -> F}
  proof: by
  by_cases hx : P x * Q z ^ 2 = Q x * P z ^ 2
  · rw [addMap_eq, add_of_Y_ne' hP hQ hPz hQz hx <| not_and.mp hxy hx,
smul_eq _ isUnit_dblZ_of_Y_ne' hP hQ hPz hx not_and.mp hxy hx]
  · rw [addMap_eq, add_of_X_ne hP hQ hPz hQz hx, smul_eq _ <| isUnit_addZ_of_X_ne hx]

中文:
引理 addMap_of_Z_ne_zero
  结论: [DecidableEq F] {P Q : 有限集 3 -> F}
  证明: by
  by_cases hx : P x * Q z ^ 2 = Q x * P z ^ 2
  · rw [addMap_eq, add_of_Y_ne' hP hQ hPz hQz hx <| not_and.mp hxy hx,
smul_eq _ isUnit_dblZ_of_Y_ne' hP hQ hPz hx not_and.mp hxy hx]
  · rw [addMap_eq, add_of_X_ne hP hQ hPz hQz hx, smul_eq _ <| isUnit_addZ_of_X_ne hx]

Depends on / 依赖: addMap_eq, add_of_X_ne, add_of_Y_ne, isUnit_addZ_of_X_ne, isUnit_dblZ_of_Y_ne, not_and, not_and.mp, smul_eq
-/
lemma addMap_of_Z_ne_zero [DecidableEq F] {P Q : Fin 3 -> F}
    (hP : W.Equation P) (hQ : W.Equation Q) (hPz : P z != 0) (hQz : Q z != 0)
    (hxy : ¬(P x * Q z ^ 2 = Q x * P z ^ 2 ∧ P y * Q z ^ 3 = W.negY Q * P z ^ 3)) :
    W.addMap ⟦P⟧ ⟦Q⟧ =
      ⟦![W.toAffine.addX (P x / P z ^ 2) (Q x / Q z ^ 2)
          (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)),
        W.toAffine.addY (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3)
          (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)),
        1]⟧ := by
  by_cases hx : P x * Q z ^ 2 = Q x * P z ^ 2
  · rw [addMap_eq, add_of_Y_ne' hP hQ hPz hQz hx <| not_and.mp hxy hx,
smul_eq _ isUnit_dblZ_of_Y_ne' hP hQ hPz hx not_and.mp hxy hx]
  · rw [addMap_eq, add_of_X_ne hP hQ hPz hQz hx, smul_eq _ <| isUnit_addZ_of_X_ne hx]

/--
lemma `nonsingularLift_addMap` / 引理 `nonsingularLift_addMap`

English:
lemma nonsingularLift_addMap
  statement: {P Q : PointClass F} (hP : W.NonsingularLift P)
  proof: by
  rcases P; rcases Q
  exact nonsingular_add hP hQ

中文:
引理 nonsingularLift_addMap
  结论: {P Q : PointClass F} (hP : W.NonsingularLift P)
  证明: by
  rcases P; rcases Q
  exact nonsingular_add hP hQ

Depends on / 依赖: nonsingular_add
-/
lemma nonsingularLift_addMap {P Q : PointClass F} (hP : W.NonsingularLift P)
(hQ : W.NonsingularLift Q) : W.NonsingularLift W.addMap P Q := by
  rcases P; rcases Q
  exact nonsingular_add hP hQ

/-! ## Nonsingular Jacobian points -/

variable (W') in
/-- A nonsingular Jacobian point on a Weierstrass curve `W`. -/
@[ext]
/--
Definition of `Point` / `Point` 的定义

English:
structure Point
  parameters: where
  axioms and operations (2):
    - {point : PointClass R}
    - (nonsingular : W'.NonsingularLift point)

中文:
结构 Point
  参数: where
  公理与运算 (2 个):
    - {point : PointClass R}
    - (nonsingular : W'.NonsingularLift point)
-/
structure Point where
  /-- The Jacobian point class underlying a nonsingular Jacobian point on `W`. -/
  {point : PointClass R}
  /-- The nonsingular condition underlying a nonsingular Jacobian point on `W`. -/
  (nonsingular : W'.NonsingularLift point)

namespace Point

/--
lemma `mk_point` / 引理 `mk_point`

English:
lemma mk_point
  given: {P : PointClass R} (h : W'.NonsingularLift P)
  statement: (mk h).point = P
  proof: rfl

中文:
引理 mk_point
  条件: {P : PointClass R} (h : W'.NonsingularLift P)
  结论: (mk h).point = P
  证明: rfl
-/
lemma mk_point {P : PointClass R} (h : W'.NonsingularLift P) : (mk h).point = P :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nontrivial
  signature: R] : Zero W'.Point
  body: ⟨⟨nonsingularLift_zero⟩⟩

中文:
实例 [非平凡
  签名: R] : 零 W'.Point
  定义体: ⟨⟨nonsingularLift_zero⟩⟩

Depends on / 依赖: nonsingularLift_zero
-/
instance [Nontrivial R] : Zero W'.Point :=
  ⟨⟨nonsingularLift_zero⟩⟩

/--
lemma `zero_def` / 引理 `zero_def`

English:
lemma zero_def
  given: [Nontrivial R]
  statement: (0 : W'.Point) = ⟨nonsingularLift_zero⟩
  proof: rfl

中文:
引理 zero_def
  条件: [非平凡 R]
  结论: (0 : W'.Point) = ⟨nonsingularLift_zero⟩
  证明: rfl
-/
lemma zero_def [Nontrivial R] : (0 : W'.Point) = ⟨nonsingularLift_zero⟩ :=
  rfl

/--
lemma `zero_point` / 引理 `zero_point`

English:
lemma zero_point
  given: [Nontrivial R]
  statement: (0 : W'.Point).point = ⟦![1, 1, 0]⟧
  proof: rfl

中文:
引理 zero_point
  条件: [非平凡 R]
  结论: (0 : W'.Point).point = ⟦![1, 1, 0]⟧
  证明: rfl
-/
lemma zero_point [Nontrivial R] : (0 : W'.Point).point = ⟦![1, 1, 0]⟧ :=
  rfl

/--
lemma `mk_ne_zero` / 引理 `mk_ne_zero`

English:
lemma mk_ne_zero
  given: [Nontrivial R] {X Y : R} (h : W'.NonsingularLift ⟦![X, Y, 1]⟧)
  statement: mk h != 0
  proof: (not_equiv_of_Z_eq_zero_right one_ne_zero rfl).comp Quotient.eq.mp.comp Point.ext_iff.mp

中文:
引理 mk_ne_zero
  条件: [非平凡 R] {X Y : R} (h : W'.NonsingularLift ⟦![X, Y, 1]⟧)
  结论: mk h != 0
  证明: (not_equiv_of_Z_eq_zero_right one_ne_zero rfl).comp Quotient.eq.mp.comp Point.ext_iff.mp

Depends on / 依赖: Point.ext_iff.mp, Quotient, Quotient.eq.mp.comp, ext_iff, not_equiv_of_Z_eq_zero_right, one_ne_zero
-/
lemma mk_ne_zero [Nontrivial R] {X Y : R} (h : W'.NonsingularLift ⟦![X, Y, 1]⟧) : mk h != 0 :=
(not_equiv_of_Z_eq_zero_right one_ne_zero rfl).comp Quotient.eq.mp.comp Point.ext_iff.mp

/--
Definition of `fromAffine` / `fromAffine` 的定义

English:
definition fromAffine
  signature: [Nontrivial R]

中文:
定义 fromAffine
  签名: [非平凡 R]
-/
def fromAffine [Nontrivial R] : W'.toAffine.Point -> W'.Point
  | 0 => 0
  | .some _ _ h => ⟨(nonsingularLift_some ..).mpr h⟩

/--
lemma `fromAffine_zero` / 引理 `fromAffine_zero`

English:
lemma fromAffine_zero
  given: [Nontrivial R]
  statement: fromAffine 0 = (0 : W'.Point)
  proof: rfl

中文:
引理 fromAffine_zero
  条件: [非平凡 R]
  结论: fromAffine 0 = (0 : W'.Point)
  证明: rfl
-/
lemma fromAffine_zero [Nontrivial R] : fromAffine 0 = (0 : W'.Point) :=
  rfl

/--
lemma `fromAffine_some` / 引理 `fromAffine_some`

English:
lemma fromAffine_some
  given: [Nontrivial R] {X Y : R} (h : W'.toAffine.Nonsingular X Y)
  proof: rfl

中文:
引理 fromAffine_some
  条件: [非平凡 R] {X Y : R} (h : W'.toAffine.非奇异 X Y)
  证明: rfl
-/
lemma fromAffine_some [Nontrivial R] {X Y : R} (h : W'.toAffine.Nonsingular X Y) :
    fromAffine (.some _ _ h) = ⟨(nonsingularLift_some ..).mpr h⟩ :=
  rfl

/--
lemma `fromAffine_some_ne_zero` / 引理 `fromAffine_some_ne_zero`

English:
lemma fromAffine_some_ne_zero
  given: [Nontrivial R] {X Y : R} (h : W'.toAffine.Nonsingular X Y)
  proof: mk_ne_zero (nonsingularLift_some ..).mpr h

中文:
引理 fromAffine_some_ne_zero
  条件: [非平凡 R] {X Y : R} (h : W'.toAffine.非奇异 X Y)
  证明: mk_ne_zero (nonsingularLift_some ..).mpr h

Depends on / 依赖: mk_ne_zero, nonsingularLift_some
-/
lemma fromAffine_some_ne_zero [Nontrivial R] {X Y : R} (h : W'.toAffine.Nonsingular X Y) :
    fromAffine (.some _ _ h) != 0 :=
mk_ne_zero (nonsingularLift_some ..).mpr h

/--
Definition of `neg` / `neg` 的定义

English:
definition neg
  signature: (P : W.Point)
  body: ⟨nonsingularLift_negMap P.nonsingular⟩

中文:
定义 neg
  签名: (P : W.Point)
  定义体: ⟨nonsingularLift_negMap P.nonsingular⟩

Depends on / 依赖: P.nonsingular, nonsingular, nonsingularLift_negMap
-/
def neg (P : W.Point) : W.Point :=
  ⟨nonsingularLift_negMap P.nonsingular⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Neg W.Point
  body: ⟨neg⟩

中文:
实例 :
  签名: 取负 W.Point
  定义体: ⟨neg⟩
-/
instance : Neg W.Point :=
  ⟨neg⟩

/--
lemma `neg_def` / 引理 `neg_def`

English:
lemma neg_def
  given: (P : W.Point)
  statement: -P = P.neg
  proof: rfl

中文:
引理 neg_def
  条件: (P : W.Point)
  结论: -P = P.neg
  证明: rfl
-/
lemma neg_def (P : W.Point) : -P = P.neg :=
  rfl

/--
lemma `neg_point` / 引理 `neg_point`

English:
lemma neg_point
  given: (P : W.Point)
  statement: (-P).point = W.negMap P.point
  proof: rfl

中文:
引理 neg_point
  条件: (P : W.Point)
  结论: (-P).point = W.negMap P.point
  证明: rfl
-/
lemma neg_point (P : W.Point) : (-P).point = W.negMap P.point :=
  rfl

/--
Definition of `add` / `add` 的定义

English:
definition add
  signature: (P Q : W.Point)
  body: ⟨nonsingularLift_addMap P.nonsingular Q.nonsingular⟩

中文:
定义 add
  签名: (P Q : W.Point)
  定义体: ⟨nonsingularLift_addMap P.nonsingular Q.nonsingular⟩

Depends on / 依赖: P.nonsingular, Q.nonsingular, nonsingular, nonsingularLift_addMap
-/
noncomputable def add (P Q : W.Point) : W.Point :=
  ⟨nonsingularLift_addMap P.nonsingular Q.nonsingular⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add W.Point
  body: ⟨add⟩

中文:
实例 :
  签名: 加法 W.Point
  定义体: ⟨add⟩
-/
noncomputable instance : Add W.Point :=
  ⟨add⟩

/--
lemma `add_def` / 引理 `add_def`

English:
lemma add_def
  given: (P Q : W.Point)
  statement: P + Q = P.add Q
  proof: rfl

中文:
引理 add_def
  条件: (P Q : W.Point)
  结论: P + Q = P.add Q
  证明: rfl
-/
lemma add_def (P Q : W.Point) : P + Q = P.add Q :=
  rfl

/--
lemma `add_point` / 引理 `add_point`

English:
lemma add_point
  given: (P Q : W.Point)
  statement: (P + Q).point = W.addMap P.point Q.point
  proof: rfl

中文:
引理 add_point
  条件: (P Q : W.Point)
  结论: (P + Q).point = W.addMap P.point Q.point
  证明: rfl
-/
lemma add_point (P Q : W.Point) : (P + Q).point = W.addMap P.point Q.point :=
  rfl

/-! ## Equivalence between Jacobian and affine coordinates -/

open scoped Classical in
variable (W) in
/--
Definition of `toAffine` / `toAffine` 的定义

English:
definition toAffine
  signature: (P : Fin 3 -> F)
  body: if hP : W.Nonsingular P ∧ P z != 0 then .some _ _ (nonsingular_of_Z_ne_zero hP.2).mp hP.1 else 0

中文:
定义 toAffine
  签名: (P : 有限集 3 -> F)
  定义体: if hP : W.Nonsingular P ∧ P z != 0 then .some _ _ (nonsingular_of_Z_ne_zero hP.2).mp hP.1 else 0

Depends on / 依赖: Nonsingular, W.Nonsingular, nonsingular_of_Z_ne_zero
-/
noncomputable def toAffine (P : Fin 3 -> F) : W.toAffine.Point :=
if hP : W.Nonsingular P ∧ P z != 0 then .some _ _ (nonsingular_of_Z_ne_zero hP.2).mp hP.1 else 0

/--
lemma `toAffine_of_singular` / 引理 `toAffine_of_singular`

English:
lemma toAffine_of_singular
  given: {P : Fin 3 -> F} (hP : ¬W.Nonsingular P)
  statement: toAffine W P = 0
  proof: by
  rw [toAffine]; rw [dif_neg <| not_and_of_not_left _ hP]

中文:
引理 toAffine_of_singular
  条件: {P : 有限集 3 -> F} (hP : ¬W.非奇异 P)
  结论: toAffine W P = 0
  证明: by
  rw [toAffine]; rw [dif_neg <| not_and_of_not_left _ hP]

Depends on / 依赖: dif_neg, not_and_of_not_left, toAffine
-/
lemma toAffine_of_singular {P : Fin 3 -> F} (hP : ¬W.Nonsingular P) : toAffine W P = 0 := by
  rw [toAffine]; rw [dif_neg <| not_and_of_not_left _ hP]

/--
lemma `toAffine_of_Z_eq_zero` / 引理 `toAffine_of_Z_eq_zero`

English:
lemma toAffine_of_Z_eq_zero
  given: {P : Fin 3 -> F} (hPz : P z = 0)
  statement: toAffine W P = 0
  proof: by
  rw [toAffine]; rw [dif_neg <| not_and_not_right.mpr fun _ => hPz]

中文:
引理 toAffine_of_Z_eq_zero
  条件: {P : 有限集 3 -> F} (hPz : P z = 0)
  结论: toAffine W P = 0
  证明: by
  rw [toAffine]; rw [dif_neg <| not_and_not_right.mpr fun _ => hPz]

Depends on / 依赖: dif_neg, not_and_not_right, not_and_not_right.mpr, toAffine
-/
lemma toAffine_of_Z_eq_zero {P : Fin 3 -> F} (hPz : P z = 0) : toAffine W P = 0 := by
  rw [toAffine]; rw [dif_neg <| not_and_not_right.mpr fun _ => hPz]

/--
lemma `toAffine_zero` / 引理 `toAffine_zero`

English:
lemma toAffine_zero
  statement: toAffine W ![1, 1, 0] = 0
  proof: toAffine_of_Z_eq_zero rfl

中文:
引理 toAffine_zero
  结论: toAffine W ![1, 1, 0] = 0
  证明: toAffine_of_Z_eq_zero rfl

Depends on / 依赖: toAffine_of_Z_eq_zero
-/
lemma toAffine_zero : toAffine W ![1, 1, 0] = 0 :=
  toAffine_of_Z_eq_zero rfl

/--
lemma `toAffine_of_Z_ne_zero` / 引理 `toAffine_of_Z_ne_zero`

English:
lemma toAffine_of_Z_ne_zero
  given: {P : Fin 3 -> F} (hP : W.Nonsingular P) (hPz : P z != 0)
  proof: by
  rw [toAffine]; rw [dif_pos ⟨hP]; rw [hPz⟩]

中文:
引理 toAffine_of_Z_ne_zero
  条件: {P : 有限集 3 -> F} (hP : W.非奇异 P) (hPz : P z != 0)
  证明: by
  rw [toAffine]; rw [dif_pos ⟨hP]; rw [hPz⟩]

Depends on / 依赖: dif_pos, toAffine
-/
lemma toAffine_of_Z_ne_zero {P : Fin 3 -> F} (hP : W.Nonsingular P) (hPz : P z != 0) :
    toAffine W P = .some _ _ ((nonsingular_of_Z_ne_zero hPz).mp hP) := by
  rw [toAffine]; rw [dif_pos ⟨hP]; rw [hPz⟩]

/--
lemma `toAffine_some` / 引理 `toAffine_some`

English:
lemma toAffine_some
  given: {X Y : F} (h : W.Nonsingular ![X, Y, 1])
  proof: by
  simp only [toAffine_of_Z_ne_zero h one_ne_zero, fin3_def_ext, one_pow, div_one]

中文:
引理 toAffine_some
  条件: {X Y : F} (h : W.非奇异 ![X, Y, 1])
  证明: by
  simp only [toAffine_of_Z_ne_zero h one_ne_zero, fin3_def_ext, one_pow, div_one]

Depends on / 依赖: div_one, fin3_def_ext, one_ne_zero, one_pow, toAffine_of_Z_ne_zero
-/
lemma toAffine_some {X Y : F} (h : W.Nonsingular ![X, Y, 1]) :
    toAffine W ![X, Y, 1] = .some _ _ ((nonsingular_some ..).mp h) := by
  simp only [toAffine_of_Z_ne_zero h one_ne_zero, fin3_def_ext, one_pow, div_one]

/--
lemma `toAffine_smul` / 引理 `toAffine_smul`

English:
lemma toAffine_smul
  given: (P : Fin 3 -> F) {u : F} (hu : IsUnit u)
  proof: by
  by_cases hP : W.Nonsingular P
  · by_cases hPz : P z = 0
    · rw [toAffine_of_Z_eq_zero <| mul_eq_zero_of_right u hPz, toAffine_of_Z_eq_zero hPz]
    · rw [toAffine_of_Z_ne_zero ((nonsingular_smul P hu).mpr hP) <| mul_ne_zero hu.ne_zero hPz,
        toAffine_of_Z_ne_zero hP hPz, Affine.Point.some.injEq]
      simp only [smul_fin3_ext, mul_pow, mul_div_mul_left _ _ (hu.pow _).ne_zero, and_self]
  · rw [toAffine_of_singular <| hP.comp (nonsingular_smul P hu).mp, toAffine_of_singular hP]

中文:
引理 toAffine_smul
  条件: (P : 有限集 3 -> F) {u : F} (hu : 是单位 u)
  证明: by
  by_cases hP : W.Nonsingular P
  · by_cases hPz : P z = 0
    · rw [toAffine_of_Z_eq_zero <| mul_eq_zero_of_right u hPz, toAffine_of_Z_eq_zero hPz]
    · rw [toAffine_of_Z_ne_zero ((nonsingular_smul P hu).mpr hP) <| mul_ne_zero hu.ne_zero hPz,
        toAffine_of_Z_ne_zero hP hPz, Affine.Point.some.injEq]
      simp only [smul_fin3_ext, mul_pow, mul_div_mul_left _ _ (hu.pow _).ne_zero, and_self]
  · rw [toAffine_of_singular <| hP.comp (nonsingular_smul P hu).mp, toAffine_of_singular hP]

Depends on / 依赖: Affine, Affine.Point.some.injEq, Nonsingular, W.Nonsingular, and_self, hP.comp, hu.ne_zero, hu.pow, mul_div_mul_left, mul_eq_zero_of_right, mul_ne_zero, mul_pow, ne_zero, nonsingular_smul, smul_fin3_ext, toAffine_of_Z_eq_zero, toAffine_of_Z_ne_zero, toAffine_of_singular
-/
lemma toAffine_smul (P : Fin 3 -> F) {u : F} (hu : IsUnit u) :
    toAffine W (u • P) = toAffine W P := by
  by_cases hP : W.Nonsingular P
  · by_cases hPz : P z = 0
    · rw [toAffine_of_Z_eq_zero <| mul_eq_zero_of_right u hPz, toAffine_of_Z_eq_zero hPz]
    · rw [toAffine_of_Z_ne_zero ((nonsingular_smul P hu).mpr hP) <| mul_ne_zero hu.ne_zero hPz,
        toAffine_of_Z_ne_zero hP hPz, Affine.Point.some.injEq]
      simp only [smul_fin3_ext, mul_pow, mul_div_mul_left _ _ (hu.pow _).ne_zero, and_self]
  · rw [toAffine_of_singular <| hP.comp (nonsingular_smul P hu).mp, toAffine_of_singular hP]

/--
lemma `toAffine_of_equiv` / 引理 `toAffine_of_equiv`

English:
lemma toAffine_of_equiv
  given: {P Q : Fin 3 -> F} (h : P ≈ Q)
  statement: toAffine W P = toAffine W Q
  proof: by
  rcases h with ⟨u, rfl⟩
  exact toAffine_smul Q u.isUnit

中文:
引理 toAffine_of_equiv
  条件: {P Q : 有限集 3 -> F} (h : P ≈ Q)
  结论: toAffine W P = toAffine W Q
  证明: by
  rcases h with ⟨u, rfl⟩
  exact toAffine_smul Q u.isUnit

Depends on / 依赖: isUnit, toAffine_smul, u.isUnit
-/
lemma toAffine_of_equiv {P Q : Fin 3 -> F} (h : P ≈ Q) : toAffine W P = toAffine W Q := by
  rcases h with ⟨u, rfl⟩
  exact toAffine_smul Q u.isUnit

/--
lemma `toAffine_neg` / 引理 `toAffine_neg`

English:
lemma toAffine_neg
  given: {P : Fin 3 -> F} (hP : W.Nonsingular P)
  proof: by
  by_cases hPz : P z = 0
  · rw [neg_of_Z_eq_zero hP hPz,
      toAffine_smul _ ((isUnit_Y_of_Z_eq_zero hP hPz).div <| isUnit_X_of_Z_eq_zero hP hPz).neg,
      toAffine_zero, toAffine_of_Z_eq_zero hPz, Affine.Point.neg_zero]
  · rw [neg_of_Z_ne_zero hPz, toAffine_smul _ <| Ne.isUnit hPz, toAffine_some <|
(nonsingular_smul _ <| Ne.isUnit hPz).mp neg_of_Z_ne_zero hPz ▸ nonsingular_neg hP,
      toAffine_of_Z_ne_zero hP hPz, Affine.Point.neg_some]

中文:
引理 toAffine_neg
  条件: {P : 有限集 3 -> F} (hP : W.非奇异 P)
  证明: by
  by_cases hPz : P z = 0
  · rw [neg_of_Z_eq_zero hP hPz,
      toAffine_smul _ ((isUnit_Y_of_Z_eq_zero hP hPz).div <| isUnit_X_of_Z_eq_zero hP hPz).neg,
      toAffine_zero, toAffine_of_Z_eq_zero hPz, Affine.Point.neg_zero]
  · rw [neg_of_Z_ne_zero hPz, toAffine_smul _ <| Ne.isUnit hPz, toAffine_some <|
(nonsingular_smul _ <| Ne.isUnit hPz).mp neg_of_Z_ne_zero hPz ▸ nonsingular_neg hP,
      toAffine_of_Z_ne_zero hP hPz, Affine.Point.neg_some]

Depends on / 依赖: Affine, Affine.Point.neg_some, Affine.Point.neg_zero, Ne.isUnit, isUnit, isUnit_X_of_Z_eq_zero, isUnit_Y_of_Z_eq_zero, neg_of_Z_eq_zero, neg_of_Z_ne_zero, neg_some, neg_zero, nonsingular_neg, nonsingular_smul, toAffine_of_Z_eq_zero, toAffine_of_Z_ne_zero, toAffine_smul, toAffine_some, toAffine_zero
-/
lemma toAffine_neg {P : Fin 3 -> F} (hP : W.Nonsingular P) :
    toAffine W (W.neg P) = -toAffine W P := by
  by_cases hPz : P z = 0
  · rw [neg_of_Z_eq_zero hP hPz,
      toAffine_smul _ ((isUnit_Y_of_Z_eq_zero hP hPz).div <| isUnit_X_of_Z_eq_zero hP hPz).neg,
      toAffine_zero, toAffine_of_Z_eq_zero hPz, Affine.Point.neg_zero]
  · rw [neg_of_Z_ne_zero hPz, toAffine_smul _ <| Ne.isUnit hPz, toAffine_some <|
(nonsingular_smul _ <| Ne.isUnit hPz).mp neg_of_Z_ne_zero hPz ▸ nonsingular_neg hP,
      toAffine_of_Z_ne_zero hP hPz, Affine.Point.neg_some]

/--
lemma `toAffine_add_of_Z_ne_zero` / 引理 `toAffine_add_of_Z_ne_zero`

English:
lemma toAffine_add_of_Z_ne_zero
  statement: [DecidableEq F] {P Q : Fin 3 -> F}
  proof: by
  rw [toAffine_some <| nonsingular_add_of_Z_ne_zero hP hQ hPz hQz hxy]; rw [toAffine_of_Z_ne_zero hP hPz]; rw [toAffine_of_Z_ne_zero hQ hQz]; rw [Affine.Point.add_some by rwa [← X_eq_iff hPz hQz]; rw [← Y_eq_iff' hPz hQz]]

中文:
引理 toAffine_add_of_Z_ne_zero
  结论: [DecidableEq F] {P Q : 有限集 3 -> F}
  证明: by
  rw [toAffine_some <| nonsingular_add_of_Z_ne_zero hP hQ hPz hQz hxy]; rw [toAffine_of_Z_ne_zero hP hPz]; rw [toAffine_of_Z_ne_zero hQ hQz]; rw [Affine.Point.add_some by rwa [← X_eq_iff hPz hQz]; rw [← Y_eq_iff' hPz hQz]]
-/
private lemma toAffine_add_of_Z_ne_zero [DecidableEq F] {P Q : Fin 3 -> F}
    (hP : W.Nonsingular P) (hQ : W.Nonsingular Q) (hPz : P z != 0) (hQz : Q z != 0)
    (hxy : ¬(P x * Q z ^ 2 = Q x * P z ^ 2 ∧ P y * Q z ^ 3 = W.negY Q * P z ^ 3)) : toAffine W
      ![W.toAffine.addX (P x / P z ^ 2) (Q x / Q z ^ 2)
          (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)),
        W.toAffine.addY (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3)
          (W.toAffine.slope (P x / P z ^ 2) (Q x / Q z ^ 2) (P y / P z ^ 3) (Q y / Q z ^ 3)),
        1] = toAffine W P + toAffine W Q := by
  rw [toAffine_some <| nonsingular_add_of_Z_ne_zero hP hQ hPz hQz hxy]; rw [toAffine_of_Z_ne_zero hP hPz]; rw [toAffine_of_Z_ne_zero hQ hQz]; rw [Affine.Point.add_some by rwa [← X_eq_iff hPz hQz]; rw [← Y_eq_iff' hPz hQz]]

/--
lemma `toAffine_add` / 引理 `toAffine_add`

English:
lemma toAffine_add
  given: [DecidableEq F] {P Q : Fin 3 -> F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q)
  proof: by
  by_cases hPz : P z = 0
  · rw [toAffine_of_Z_eq_zero hPz, zero_add]
    by_cases hQz : Q z = 0
    · rw [add_of_Z_eq_zero hP hQ hPz hQz, toAffine_smul _ <| (isUnit_X_of_Z_eq_zero hP hPz).pow 2,
        toAffine_zero, toAffine_of_Z_eq_zero hQz]
    · rw [add_of_Z_eq_zero_left hP.left hPz hQz,
toAffine_smul _ (isUnit_X_of_Z_eq_zero hP hPz).mul Ne.isUnit hQz]
  · by_cases hQz : Q z = 0
    · rw [add_of_Z_eq_zero_right hQ.left hPz hQz,
        toAffine_smul _ ((isUnit_X_of_Z_eq_zero hQ hQz).mul <| Ne.isUnit hPz).neg,
        toAffine_of_Z_eq_zero hQz, add_zero]
    · by_cases hxy : P x * Q z ^ 2 = Q x * P z ^ 2 ∧ P y * Q z ^ 3 = W.negY Q * P z ^ 3
      · rw [toAffine_of_Z_ne_zero hP hPz, toAffine_of_Z_ne_zero hQ hQz, Affine.Point.add_of_Y_eq
            ((X_eq_iff hPz hQz).mp hxy.left) ((Y_eq_iff' hPz hQz).mp hxy.right)]
        by_cases hy : P y * Q z ^ 3 = Q y * P z ^ 3
        · rw [add_of_Y_eq hPz hQz hxy.left hy hxy.right,
toAffine_smul _ isUnit_dblU_of_Y_eq hP hPz hQz hxy.left hy hxy.right, toAffine_zero]
        · rw [add_of_Y_ne hP.left hQ.left hPz hQz hxy.left hy,
toAffine_smul _ isUnit_addU_of_Y_ne hPz hQz hy, toAffine_zero]
      · have := toAffine_add_of_Z_ne_zero hP hQ hPz hQz hxy
        by_cases hx : P x * Q z ^ 2 = Q x * P z ^ 2
        · rwa [add_of_Y_ne' hP.left hQ.left hPz hQz hx <| not_and.mp hxy hx,
toAffine_smul _ isUnit_dblZ_of_Y_ne' hP.left hQ.left hPz hx not_and.mp hxy hx]
        · rwa [add_of_X_ne hP.left hQ.left hPz hQz hx, toAffine_smul _ <| isUnit_addZ_of_X_ne hx]

中文:
引理 toAffine_add
  条件: [DecidableEq F] {P Q : 有限集 3 -> F} (hP : W.非奇异 P) (hQ : W.非奇异 Q)
  证明: by
  by_cases hPz : P z = 0
  · rw [toAffine_of_Z_eq_zero hPz, zero_add]
    by_cases hQz : Q z = 0
    · rw [add_of_Z_eq_zero hP hQ hPz hQz, toAffine_smul _ <| (isUnit_X_of_Z_eq_zero hP hPz).pow 2,
        toAffine_zero, toAffine_of_Z_eq_zero hQz]
    · rw [add_of_Z_eq_zero_left hP.left hPz hQz,
toAffine_smul _ (isUnit_X_of_Z_eq_zero hP hPz).mul Ne.isUnit hQz]
  · by_cases hQz : Q z = 0
    · rw [add_of_Z_eq_zero_right hQ.left hPz hQz,
        toAffine_smul _ ((isUnit_X_of_Z_eq_zero hQ hQz).mul <| Ne.isUnit hPz).neg,
        toAffine_of_Z_eq_zero hQz, add_zero]
    · by_cases hxy : P x * Q z ^ 2 = Q x * P z ^ 2 ∧ P y * Q z ^ 3 = W.negY Q * P z ^ 3
      · rw [toAffine_of_Z_ne_zero hP hPz, toAffine_of_Z_ne_zero hQ hQz, Affine.Point.add_of_Y_eq
            ((X_eq_iff hPz hQz).mp hxy.left) ((Y_eq_iff' hPz hQz).mp hxy.right)]
        by_cases hy : P y * Q z ^ 3 = Q y * P z ^ 3
        · rw [add_of_Y_eq hPz hQz hxy.left hy hxy.right,
toAffine_smul _ isUnit_dblU_of_Y_eq hP hPz hQz hxy.left hy hxy.right, toAffine_zero]
        · rw [add_of_Y_ne hP.left hQ.left hPz hQz hxy.left hy,
toAffine_smul _ isUnit_addU_of_Y_ne hPz hQz hy, toAffine_zero]
      · have := toAffine_add_of_Z_ne_zero hP hQ hPz hQz hxy
        by_cases hx : P x * Q z ^ 2 = Q x * P z ^ 2
        · rwa [add_of_Y_ne' hP.left hQ.left hPz hQz hx <| not_and.mp hxy hx,
toAffine_smul _ isUnit_dblZ_of_Y_ne' hP.left hQ.left hPz hx not_and.mp hxy hx]
        · rwa [add_of_X_ne hP.left hQ.left hPz hQz hx, toAffine_smul _ <| isUnit_addZ_of_X_ne hx]

Depends on / 依赖: Ne.isUnit, add_of_Z_eq_zero, add_of_Z_eq_zero_left, add_of_Z_eq_zero_right, hP.left, hQ.left, isUnit, isUnit_X_of_Z_eq_zero, toAffine_of_Z_, toAffine_of_Z_eq_zero, toAffine_smul, toAffine_zero, zero_add
-/
lemma toAffine_add [DecidableEq F] {P Q : Fin 3 -> F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q) :
    toAffine W (W.add P Q) = toAffine W P + toAffine W Q := by
  by_cases hPz : P z = 0
  · rw [toAffine_of_Z_eq_zero hPz, zero_add]
    by_cases hQz : Q z = 0
    · rw [add_of_Z_eq_zero hP hQ hPz hQz, toAffine_smul _ <| (isUnit_X_of_Z_eq_zero hP hPz).pow 2,
        toAffine_zero, toAffine_of_Z_eq_zero hQz]
    · rw [add_of_Z_eq_zero_left hP.left hPz hQz,
toAffine_smul _ (isUnit_X_of_Z_eq_zero hP hPz).mul Ne.isUnit hQz]
  · by_cases hQz : Q z = 0
    · rw [add_of_Z_eq_zero_right hQ.left hPz hQz,
        toAffine_smul _ ((isUnit_X_of_Z_eq_zero hQ hQz).mul <| Ne.isUnit hPz).neg,
        toAffine_of_Z_eq_zero hQz, add_zero]
    · by_cases hxy : P x * Q z ^ 2 = Q x * P z ^ 2 ∧ P y * Q z ^ 3 = W.negY Q * P z ^ 3
      · rw [toAffine_of_Z_ne_zero hP hPz, toAffine_of_Z_ne_zero hQ hQz, Affine.Point.add_of_Y_eq
            ((X_eq_iff hPz hQz).mp hxy.left) ((Y_eq_iff' hPz hQz).mp hxy.right)]
        by_cases hy : P y * Q z ^ 3 = Q y * P z ^ 3
        · rw [add_of_Y_eq hPz hQz hxy.left hy hxy.right,
toAffine_smul _ isUnit_dblU_of_Y_eq hP hPz hQz hxy.left hy hxy.right, toAffine_zero]
        · rw [add_of_Y_ne hP.left hQ.left hPz hQz hxy.left hy,
toAffine_smul _ isUnit_addU_of_Y_ne hPz hQz hy, toAffine_zero]
      · have := toAffine_add_of_Z_ne_zero hP hQ hPz hQz hxy
        by_cases hx : P x * Q z ^ 2 = Q x * P z ^ 2
        · rwa [add_of_Y_ne' hP.left hQ.left hPz hQz hx <| not_and.mp hxy hx,
toAffine_smul _ isUnit_dblZ_of_Y_ne' hP.left hQ.left hPz hx not_and.mp hxy hx]
        · rwa [add_of_X_ne hP.left hQ.left hPz hQz hx, toAffine_smul _ <| isUnit_addZ_of_X_ne hx]

/--
Definition of `toAffineLift` / `toAffineLift` 的定义

English:
definition toAffineLift
  signature: (P : W.Point)
  body: P.point.lift _ fun _ _ => toAffine_of_equiv

中文:
定义 toAffineLift
  签名: (P : W.Point)
  定义体: P.point.lift _ fun _ _ => toAffine_of_equiv

Depends on / 依赖: P.point.lift, toAffine_of_equiv
-/
noncomputable def toAffineLift (P : W.Point) : W.toAffine.Point :=
  P.point.lift _ fun _ _ => toAffine_of_equiv

/--
lemma `toAffineLift_eq` / 引理 `toAffineLift_eq`

English:
lemma toAffineLift_eq
  given: {P : Fin 3 -> F} (hP : W.NonsingularLift ⟦P⟧)
  proof: rfl

中文:
引理 toAffineLift_eq
  条件: {P : 有限集 3 -> F} (hP : W.NonsingularLift ⟦P⟧)
  证明: rfl
-/
lemma toAffineLift_eq {P : Fin 3 -> F} (hP : W.NonsingularLift ⟦P⟧) :
    toAffineLift ⟨hP⟩ = toAffine W P :=
  rfl

/--
lemma `toAffineLift_of_Z_eq_zero` / 引理 `toAffineLift_of_Z_eq_zero`

English:
lemma toAffineLift_of_Z_eq_zero
  given: {P : Fin 3 -> F} (hP : W.NonsingularLift ⟦P⟧) (hPz : P z = 0)
  proof: toAffine_of_Z_eq_zero hPz

中文:
引理 toAffineLift_of_Z_eq_zero
  条件: {P : 有限集 3 -> F} (hP : W.NonsingularLift ⟦P⟧) (hPz : P z = 0)
  证明: toAffine_of_Z_eq_zero hPz

Depends on / 依赖: toAffine_of_Z_eq_zero
-/
lemma toAffineLift_of_Z_eq_zero {P : Fin 3 -> F} (hP : W.NonsingularLift ⟦P⟧) (hPz : P z = 0) :
    toAffineLift ⟨hP⟩ = 0 :=
  toAffine_of_Z_eq_zero hPz

/--
lemma `toAffineLift_zero` / 引理 `toAffineLift_zero`

English:
lemma toAffineLift_zero
  statement: toAffineLift (0 : W.Point) = 0
  proof: toAffine_zero

中文:
引理 toAffineLift_zero
  结论: toAffineLift (0 : W.Point) = 0
  证明: toAffine_zero

Depends on / 依赖: toAffine_zero
-/
lemma toAffineLift_zero : toAffineLift (0 : W.Point) = 0 :=
  toAffine_zero

/--
lemma `toAffineLift_of_Z_ne_zero` / 引理 `toAffineLift_of_Z_ne_zero`

English:
lemma toAffineLift_of_Z_ne_zero
  given: {P : Fin 3 -> F} {hP : W.NonsingularLift ⟦P⟧} (hPz : P z != 0)
  proof: toAffine_of_Z_ne_zero hP hPz

中文:
引理 toAffineLift_of_Z_ne_zero
  条件: {P : 有限集 3 -> F} {hP : W.NonsingularLift ⟦P⟧} (hPz : P z != 0)
  证明: toAffine_of_Z_ne_zero hP hPz

Depends on / 依赖: toAffine_of_Z_ne_zero
-/
lemma toAffineLift_of_Z_ne_zero {P : Fin 3 -> F} {hP : W.NonsingularLift ⟦P⟧} (hPz : P z != 0) :
    toAffineLift ⟨hP⟩ = .some _ _ ((nonsingular_of_Z_ne_zero hPz).mp hP) :=
  toAffine_of_Z_ne_zero hP hPz

/--
lemma `toAffineLift_some` / 引理 `toAffineLift_some`

English:
lemma toAffineLift_some
  given: {X Y : F} (h : W.NonsingularLift ⟦![X, Y, 1]⟧)
  proof: toAffine_some h

中文:
引理 toAffineLift_some
  条件: {X Y : F} (h : W.NonsingularLift ⟦![X, Y, 1]⟧)
  证明: toAffine_some h

Depends on / 依赖: toAffine_some
-/
lemma toAffineLift_some {X Y : F} (h : W.NonsingularLift ⟦![X, Y, 1]⟧) :
    toAffineLift ⟨h⟩ = .some _ _ ((nonsingular_some ..).mp h) :=
  toAffine_some h

/--
lemma `toAffineLift_neg` / 引理 `toAffineLift_neg`

English:
lemma toAffineLift_neg
  given: (P : W.Point)
  statement: (-P).toAffineLift = -P.toAffineLift
  proof: by
  rcases P with @⟨⟨_⟩, hP⟩
  exact toAffine_neg hP

中文:
引理 toAffineLift_neg
  条件: (P : W.Point)
  结论: (-P).toAffineLift = -P.toAffineLift
  证明: by
  rcases P with @⟨⟨_⟩, hP⟩
  exact toAffine_neg hP

Depends on / 依赖: toAffine_neg
-/
lemma toAffineLift_neg (P : W.Point) : (-P).toAffineLift = -P.toAffineLift := by
  rcases P with @⟨⟨_⟩, hP⟩
  exact toAffine_neg hP

/--
lemma `toAffineLift_add` / 引理 `toAffineLift_add`

English:
lemma toAffineLift_add
  given: [DecidableEq F] (P Q : W.Point)
  proof: by
  rcases P, Q with ⟨@⟨⟨_⟩, hP⟩, @⟨⟨_⟩, hQ⟩⟩
  exact toAffine_add hP hQ

中文:
引理 toAffineLift_add
  条件: [DecidableEq F] (P Q : W.Point)
  证明: by
  rcases P, Q with ⟨@⟨⟨_⟩, hP⟩, @⟨⟨_⟩, hQ⟩⟩
  exact toAffine_add hP hQ

Depends on / 依赖: toAffine_add
-/
lemma toAffineLift_add [DecidableEq F] (P Q : W.Point) :
    (P + Q).toAffineLift = P.toAffineLift + Q.toAffineLift := by
  rcases P, Q with ⟨@⟨⟨_⟩, hP⟩, @⟨⟨_⟩, hQ⟩⟩
  exact toAffine_add hP hQ

set_option backward.isDefEq.respectTransparency false in
variable (W) in
/-- The addition-preserving equivalence between the type of nonsingular Jacobian points on a
Weierstrass curve `W` and the type of nonsingular points in affine coordinates. -/
@[simps]
/--
Definition of `toAffineAddEquiv` / `toAffineAddEquiv` 的定义

English:
definition toAffineAddEquiv
  signature: [DecidableEq F]
  body: toAffineLift
  invFun := fromAffine
  left_inv := by
    rintro @⟨⟨P⟩, hP⟩
    by_cases hPz : P z = 0
    · rw [Point.ext_iff, toAffineLift_eq, toAffine_of_Z_eq_zero hPz]
exact Quotient.eq.mpr Setoid.symm equiv_zero_of_Z_eq_zero hP hPz
    · rw [Point.ext_iff, toAffineLift_eq, toAffine_of_Z_ne_zero hP hPz]
exact Quotient.eq.mpr Setoid.symm equiv_some_of_Z_ne_zero hPz
  right_inv := by
    rintro (_ | _)
    · rw [← Affine.Point.zero_def, fromAffine_zero, toAffineLift_zero]
    · rw [fromAffine_some, toAffineLift_some]
  map_add' := toAffineLift_add

中文:
定义 toAffineAddEquiv
  签名: [DecidableEq F]
  定义体: toAffineLift
  invFun := fromAffine
  left_inv := by
    rintro @⟨⟨P⟩, hP⟩
    by_cases hPz : P z = 0
    · rw [Point.ext_iff, toAffineLift_eq, toAffine_of_Z_eq_zero hPz]
exact Quotient.eq.mpr Setoid.symm equiv_zero_of_Z_eq_zero hP hPz
    · rw [Point.ext_iff, toAffineLift_eq, toAffine_of_Z_ne_zero hP hPz]
exact Quotient.eq.mpr Setoid.symm equiv_some_of_Z_ne_zero hPz
  right_inv := by
    rintro (_ | _)
    · rw [← Affine.Point.zero_def, fromAffine_zero, toAffineLift_zero]
    · rw [fromAffine_some, toAffineLift_some]
  map_add' := toAffineLift_add

Depends on / 依赖: toAffineLift
-/
noncomputable def toAffineAddEquiv [DecidableEq F] : W.Point ≃+ W.toAffine.Point where
  toFun := toAffineLift
  invFun := fromAffine
  left_inv := by
    rintro @⟨⟨P⟩, hP⟩
    by_cases hPz : P z = 0
    · rw [Point.ext_iff, toAffineLift_eq, toAffine_of_Z_eq_zero hPz]
exact Quotient.eq.mpr Setoid.symm equiv_zero_of_Z_eq_zero hP hPz
    · rw [Point.ext_iff, toAffineLift_eq, toAffine_of_Z_ne_zero hP hPz]
exact Quotient.eq.mpr Setoid.symm equiv_some_of_Z_ne_zero hPz
  right_inv := by
    rintro (_ | _)
    · rw [← Affine.Point.zero_def, fromAffine_zero, toAffineLift_zero]
    · rw [fromAffine_some, toAffineLift_some]
  map_add' := toAffineLift_add

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommGroup W.Point
  body: nsmulRec
  zsmul := zsmulRec
  zero_add _ := by
    classical
    apply (toAffineAddEquiv W).injective
    simp only [map_add, toAffineAddEquiv_apply, toAffineLift_zero, zero_add]
  add_zero _ := by
    classical
    apply (toAffineAddEquiv W).injective
    simp only [map_add, toAffineAddEquiv_apply, toAffineLift_zero, add_zero]
  neg_add_cancel P := by
    classical
    apply (toAffineAddEquiv W).injective
    simp only [map_add, toAffineAddEquiv_apply, toAffineLift_neg, neg_add_cancel, toAffineLift_zero]
  add_comm _ _ := by
    classical
    apply (toAffineAddEquiv W).injective
    simp only [map_add, add_comm]
  add_assoc _ _ _ := by
    classical
    apply (toAffineAddEquiv W).injective
    simp only [map_add, add_assoc]

中文:
实例 :
  签名: 加法交换群 W.Point
  定义体: nsmulRec
  zsmul := zsmulRec
  zero_add _ := by
    classical
    apply (toAffineAddEquiv W).injective
    simp only [map_add, toAffineAddEquiv_apply, toAffineLift_zero, zero_add]
  add_zero _ := by
    classical
    apply (toAffineAddEquiv W).injective
    simp only [map_add, toAffineAddEquiv_apply, toAffineLift_zero, add_zero]
  neg_add_cancel P := by
    classical
    apply (toAffineAddEquiv W).injective
    simp only [map_add, toAffineAddEquiv_apply, toAffineLift_neg, neg_add_cancel, toAffineLift_zero]
  add_comm _ _ := by
    classical
    apply (toAffineAddEquiv W).injective
    simp only [map_add, add_comm]
  add_assoc _ _ _ := by
    classical
    apply (toAffineAddEquiv W).injective
    simp only [map_add, add_assoc]

Depends on / 依赖: nsmulRec
-/
noncomputable instance : AddCommGroup W.Point where
  nsmul := nsmulRec
  zsmul := zsmulRec
  zero_add _ := by
    classical
    apply (toAffineAddEquiv W).injective
    simp only [map_add, toAffineAddEquiv_apply, toAffineLift_zero, zero_add]
  add_zero _ := by
    classical
    apply (toAffineAddEquiv W).injective
    simp only [map_add, toAffineAddEquiv_apply, toAffineLift_zero, add_zero]
  neg_add_cancel P := by
    classical
    apply (toAffineAddEquiv W).injective
    simp only [map_add, toAffineAddEquiv_apply, toAffineLift_neg, neg_add_cancel, toAffineLift_zero]
  add_comm _ _ := by
    classical
    apply (toAffineAddEquiv W).injective
    simp only [map_add, add_comm]
  add_assoc _ _ _ := by
    classical
    apply (toAffineAddEquiv W).injective
    simp only [map_add, add_assoc]

end Point

/-! ## Maps and base changes -/

@[simp]
/--
lemma `map_neg` / 引理 `map_neg`

English:
lemma map_neg
  given: (f : R ->+* S) (P : Fin 3 -> R)
  statement: (W'.map f).neg (f ∘ P) = f ∘ W'.neg P
  proof: by
  simp only [neg, map_negY, comp_fin3]
  map_simp

@[simp]

中文:
引理 map_neg
  条件: (f : R ->+* S) (P : 有限集 3 -> R)
  结论: (W'.map f).neg (f ∘ P) = f ∘ W'.neg P
  证明: by
  simp only [neg, map_negY, comp_fin3]
  map_simp

@[simp]
-/
protected lemma map_neg (f : R ->+* S) (P : Fin 3 -> R) : (W'.map f).neg (f ∘ P) = f ∘ W'.neg P := by
  simp only [neg, map_negY, comp_fin3]
  map_simp

@[simp]
/--
lemma `map_add` / 引理 `map_add`

English:
lemma map_add
  statement: (f : F ->+* K) {P Q : Fin 3 -> F} (hP : W.Nonsingular P)
  proof: by
  by_cases h : P ≈ Q
  · rw [add_of_equiv <| (comp_equiv_comp f hP hQ).mpr h, add_of_equiv h, map_dblXYZ]
  · rw [add_of_not_equiv <| h.comp (comp_equiv_comp f hP hQ).mp, add_of_not_equiv h, map_addXYZ]

中文:
引理 map_add
  结论: (f : F ->+* K) {P Q : 有限集 3 -> F} (hP : W.非奇异 P)
  证明: by
  by_cases h : P ≈ Q
  · rw [add_of_equiv <| (comp_equiv_comp f hP hQ).mpr h, add_of_equiv h, map_dblXYZ]
  · rw [add_of_not_equiv <| h.comp (comp_equiv_comp f hP hQ).mp, add_of_not_equiv h, map_addXYZ]

Depends on / 依赖: X.property, property
-/
protected lemma map_add (f : F ->+* K) {P Q : Fin 3 -> F} (hP : W.Nonsingular P)
    (hQ : W.Nonsingular Q) : (W.map f).add (f ∘ P) (f ∘ Q) = f ∘ W.add P Q := by
  by_cases h : P ≈ Q
  · rw [add_of_equiv <| (comp_equiv_comp f hP hQ).mpr h, add_of_equiv h, map_dblXYZ]
  · rw [add_of_not_equiv <| h.comp (comp_equiv_comp f hP hQ).mp, add_of_not_equiv h, map_addXYZ]

/--
lemma `baseChange_neg` / 引理 `baseChange_neg`

English:
lemma baseChange_neg
  statement: [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A] [Algebra R B]
  proof: by
  rw [← RingHom.coe_coe]; rw [← WeierstrassCurve.Jacobian.map_neg]; rw [map_baseChange]

中文:
引理 baseChange_neg
  结论: [代数 R S] [代数 R A] [代数 S A] [标量塔 R S A] [代数 R B]
  证明: by
  rw [← RingHom.coe_coe]; rw [← WeierstrassCurve.Jacobian.map_neg]; rw [map_baseChange]

Depends on / 依赖: Jacobian, RingHom, RingHom.coe_coe, WeierstrassCurve, WeierstrassCurve.Jacobian.map_neg, X.property, coe_coe, map_baseChange, map_neg, property
-/
lemma baseChange_neg [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A] [Algebra R B]
    [Algebra S B] [IsScalarTower R S B] (f : A ->ₐ[S] B) (P : Fin 3 -> A) :
    (W'⁄B).neg (f ∘ P) = f ∘ (W'⁄A).neg P := by
  rw [← RingHom.coe_coe]; rw [← WeierstrassCurve.Jacobian.map_neg]; rw [map_baseChange]

/--
lemma `baseChange_add` / 引理 `baseChange_add`

English:
lemma baseChange_add
  statement: [Algebra R S] [Algebra R F] [Algebra S F] [IsScalarTower R S F] [Algebra R K]
  proof: by
  rw [← RingHom.coe_coe]; rw [← WeierstrassCurve.Jacobian.map_add _ hP hQ]; rw [map_baseChange]

中文:
引理 baseChange_add
  结论: [代数 R S] [代数 R F] [代数 S F] [标量塔 R S F] [代数 R K]
  证明: by
  rw [← RingHom.coe_coe]; rw [← WeierstrassCurve.Jacobian.map_add _ hP hQ]; rw [map_baseChange]

Depends on / 依赖: Jacobian, RingHom, RingHom.coe_coe, WeierstrassCurve, WeierstrassCurve.Jacobian.map_add, X.property, coe_coe, map_add, map_baseChange, property
-/
lemma baseChange_add [Algebra R S] [Algebra R F] [Algebra S F] [IsScalarTower R S F] [Algebra R K]
    [Algebra S K] [IsScalarTower R S K] (f : F ->ₐ[S] K) {P Q : Fin 3 -> F}
    (hP : (W'⁄F).Nonsingular P) (hQ : (W'⁄F).Nonsingular Q) :
    (W'⁄K).add (f ∘ P) (f ∘ Q) = f ∘ (W'⁄F).add P Q := by
  rw [← RingHom.coe_coe]; rw [← WeierstrassCurve.Jacobian.map_add _ hP hQ]; rw [map_baseChange]

end Jacobian

/--
Definition of `Affine.Point.toJacobian` / `Affine.Point.toJacobian` 的定义

English:
abbreviation Affine.Point.toJacobian
  signature: [Nontrivial R] {W : Affine R} (P : W.Point)
  body: Jacobian.Point.fromAffine P

中文:
缩写 仿射.Point.toJacobian
  签名: [非平凡 R] {W : 仿射 R} (P : W.Point)
  定义体: Jacobian.Point.fromAffine P

Depends on / 依赖: Jacobian, Jacobian.Point.fromAffine, X.property, fromAffine, property
-/
abbrev Affine.Point.toJacobian [Nontrivial R] {W : Affine R} (P : W.Point) : W.toJacobian.Point :=
  Jacobian.Point.fromAffine P

end WeierstrassCurve
