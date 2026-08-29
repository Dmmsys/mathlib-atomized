/-
Copyright (c) 2025 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
public import Mathlib.Data.Fin.Tuple.Reflection
public import Mathlib.Tactic.Ring.NamePolyVars

/-!
# Weierstrass equations and the nonsingular condition in projective coordinates

A point on the unweighted projective plane over a commutative ring `R` is an equivalence class
`[x : y : z]` of triples `(x, y, z) ≠ (0, 0, 0)` of elements in `R` such that
`(x, y, z) ∼ (x', y', z')` if there is some unit `u` in `Rˣ` with `(x, y, z) = (ux', uy', uz')`.

Let `W` be a Weierstrass curve over a commutative ring `R` with coefficients `aᵢ`. A
*projective point* is a point on the unweighted projective plane over `R` satisfying the
*homogeneous Weierstrass equation* `W(X, Y, Z) = 0` in *projective coordinates*, where
`W(X, Y, Z) := Y²Z + a₁XYZ + a₃YZ² - (X³ + a₂X²Z + a₄XZ² + a₆Z³)`. It is *nonsingular* if its
partial derivatives `W_X(x, y, z)`, `W_Y(x, y, z)`, and `W_Z(x, y, z)` do not vanish simultaneously.

This file gives an explicit implementation of equivalence classes of triples up to scaling by units,
and defines polynomials associated to Weierstrass equations and the nonsingular condition in
projective coordinates. The group law on the actual type of nonsingular projective points will be
defined in `Mathlib/AlgebraicGeometry/EllipticCurve/Projective/Point.lean`, based on the formulae
for group operations in `Mathlib/AlgebraicGeometry/EllipticCurve/Projective/Formula.lean`.

## Main definitions

* `WeierstrassCurve.Projective.PointClass`: the equivalence class of a point representative.
* `WeierstrassCurve.Projective.Nonsingular`: the nonsingular condition on a point representative.
* `WeierstrassCurve.Projective.NonsingularLift`: the nonsingular condition on a point class.

## Main statements

* `WeierstrassCurve.Projective.polynomial_relation`: Euler's homogeneous function theorem.

## Implementation notes

All definitions and lemmas for Weierstrass curves in projective coordinates live in the namespace
`WeierstrassCurve.Projective` to distinguish them from those in other coordinates. This is simply an
abbreviation for `WeierstrassCurve` that can be converted using `WeierstrassCurve.toProjective`.
This can be converted into `WeierstrassCurve.Affine` using `WeierstrassCurve.Projective.toAffine`.

A point representative is implemented as a term `P` of type `Fin 3 → R`, which allows for the vector
notation `![x, y, z]`. However, `P` is not definitionally equivalent to the expanded vector
`![P x, P y, P z]`, so the lemmas `fin3_def` and `fin3_def_ext` can be used to convert between the
two forms. The equivalence of two point representatives `P` and `Q` is implemented as an equivalence
of orbits of the action of `Rˣ`, or equivalently that there is some unit `u` of `R` such that
`P = u • Q`. However, `u • Q` is not definitionally equal to `![u * Q x, u * Q y, u * Q z]`, so the
lemmas `smul_fin3` and `smul_fin3_ext` can be used to convert between the two forms. Files in
`Mathlib/AlgebraicGeometry/EllipticCurve/Projective` make extensive use of `erw` to get around this.
While `erw` is often an indication of a problem, in this case it is self-contained and should not
cause any issues. It would alternatively be possible to add some automation to assist here.

Whenever possible, all changes to documentation and naming of definitions and theorems should be
mirrored in `Mathlib/AlgebraicGeometry/EllipticCurve/Jacobian/Basic.lean`.

## References

[J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, projective, Weierstrass equation, nonsingular
-/

@[expose] public section

local notation3 "x" => (0 : Fin 3)

local notation3 "y" => (1 : Fin 3)

local notation3 "z" => (2 : Fin 3)

open MvPolynomial

local macro "eval_simp" : tactic =>
  `(tactic| simp only [eval_C, eval_X, eval_add, eval_sub, eval_mul, eval_pow])

local macro "map_simp" : tactic =>
  `(tactic| simp only [map_ofNat, map_C, map_X, map_neg, map_add, map_sub, map_mul, map_pow,
    map_div₀, WeierstrassCurve.map, Function.comp_apply])

local macro "matrix_simp" : tactic =>
  `(tactic| simp only [Matrix.head_cons, Matrix.tail_cons, Matrix.smul_empty, Matrix.smul_cons,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two])

local macro "pderiv_simp" : tactic =>
  `(tactic| simp only [map_ofNat, map_neg, map_add, map_sub, map_mul, pderiv_mul, pderiv_pow,
    pderiv_C, pderiv_X_self, pderiv_X_of_ne one_ne_zero, pderiv_X_of_ne one_ne_zero.symm,
    pderiv_X_of_ne (by decide : z != x), pderiv_X_of_ne (by decide : x != z),
    pderiv_X_of_ne (by decide : z != y), pderiv_X_of_ne (by decide : y != z)])

universe r s u v

variable {R : Type r} {F : Type u}

name_poly_vars X, Y, Z over R

namespace WeierstrassCurve

/-! ## Projective coordinates -/

variable (R) in
/--
Definition of `Projective` / `Projective` 的定义

English:
abbreviation Projective
  signature: : Type r
  body: WeierstrassCurve R

中文:
缩写 投射
  签名: : 类型 r
  定义体: WeierstrassCurve R

Depends on / 依赖: WeierstrassCurve
-/
abbrev Projective : Type r :=
  WeierstrassCurve R

/--
Definition of `toProjective` / `toProjective` 的定义

English:
abbreviation toProjective
  signature: (W : WeierstrassCurve R)
  body: W

中文:
缩写 toProjective
  签名: (W : WeierstrassCurve R)
  定义体: W
-/
abbrev toProjective (W : WeierstrassCurve R) : Projective R :=
  W

namespace Projective

/--
Definition of `toAffine` / `toAffine` 的定义

English:
abbreviation toAffine
  signature: (W' : Projective R)
  body: W'

中文:
缩写 toAffine
  签名: (W' : 投射 R)
  定义体: W'
-/
abbrev toAffine (W' : Projective R) : Affine R :=
  W'

/--
lemma `fin3_def` / 引理 `fin3_def`

English:
lemma fin3_def
  given: (P : Fin 3 -> R)
  statement: ![P x, P y, P z] = P
  proof: by
  ext n; fin_cases n <;> rfl

中文:
引理 fin3_def
  条件: (P : 有限集 3 -> R)
  结论: ![P x, P y, P z] = P
  证明: by
  ext n; fin_cases n <;> rfl

Depends on / 依赖: fin_cases
-/
lemma fin3_def (P : Fin 3 -> R) : ![P x, P y, P z] = P := by
  ext n; fin_cases n <;> rfl

/--
lemma `fin3_def_ext` / 引理 `fin3_def_ext`

English:
lemma fin3_def_ext
  given: (a b c : R)
  statement: ![a, b, c] x = a ∧ ![a, b, c] y = b ∧ ![a, b, c] z = c
  proof: ⟨rfl, rfl, rfl⟩

中文:
引理 fin3_def_ext
  条件: (a b c : R)
  结论: ![a, b, c] x = a ∧ ![a, b, c] y = b ∧ ![a, b, c] z = c
  证明: ⟨rfl, rfl, rfl⟩
-/
lemma fin3_def_ext (a b c : R) : ![a, b, c] x = a ∧ ![a, b, c] y = b ∧ ![a, b, c] z = c :=
  ⟨rfl, rfl, rfl⟩

/--
lemma `comp_fin3` / 引理 `comp_fin3`

English:
lemma comp_fin3
  given: {S : Type s} (f : R -> S) (a b c : R)
  statement: f ∘ ![a, b, c] = ![f a, f b, f c]
  proof: (FinVec.map_eq ..).symm

中文:
引理 comp_fin3
  条件: {S : 类型 s} (f : R -> S) (a b c : R)
  结论: f ∘ ![a, b, c] = ![f a, f b, f c]
  证明: (FinVec.map_eq ..).symm

Depends on / 依赖: FinVec, FinVec.map_eq, map_eq
-/
lemma comp_fin3 {S : Type s} (f : R -> S) (a b c : R) : f ∘ ![a, b, c] = ![f a, f b, f c] :=
  (FinVec.map_eq ..).symm

variable [CommRing R] [Field F] {W' : Projective R} {W : Projective F} {S : Type s} [CommRing S]
  {A : Type u} [CommRing A] {B : Type v} [CommRing B] {K : Type v} [Field K]

/--
lemma `smul_fin3` / 引理 `smul_fin3`

English:
lemma smul_fin3
  given: (P : Fin 3 -> R) (u : R)
  statement: u • P = ![u * P x, u * P y, u * P z]
  proof: by
  simp [← List.ofFn_inj, List.ofFn_succ]

中文:
引理 smul_fin3
  条件: (P : 有限集 3 -> R) (u : R)
  结论: u • P = ![u * P x, u * P y, u * P z]
  证明: by
  simp [← List.ofFn_inj, List.ofFn_succ]

Depends on / 依赖: List.ofFn_inj, List.ofFn_succ, ofFn_inj, ofFn_succ
-/
lemma smul_fin3 (P : Fin 3 -> R) (u : R) : u • P = ![u * P x, u * P y, u * P z] := by
  simp [← List.ofFn_inj, List.ofFn_succ]

/--
lemma `smul_fin3_ext` / 引理 `smul_fin3_ext`

English:
lemma smul_fin3_ext
  given: (P : Fin 3 -> R) (u : R)
  proof: ⟨rfl, rfl, rfl⟩

中文:
引理 smul_fin3_ext
  条件: (P : 有限集 3 -> R) (u : R)
  证明: ⟨rfl, rfl, rfl⟩
-/
lemma smul_fin3_ext (P : Fin 3 -> R) (u : R) :
    (u • P) x = u * P x ∧ (u • P) y = u * P y ∧ (u • P) z = u * P z :=
  ⟨rfl, rfl, rfl⟩

/--
lemma `comp_smul` / 引理 `comp_smul`

English:
lemma comp_smul
  given: (f : R ->+* S) (P : Fin 3 -> R) (u : R)
  statement: f ∘ (u • P) = f u • f ∘ P
  proof: by
  ext
  simp

中文:
引理 comp_smul
  条件: (f : R ->+* S) (P : 有限集 3 -> R) (u : R)
  结论: f ∘ (u • P) = f u • f ∘ P
  证明: by
  ext
  simp
-/
lemma comp_smul (f : R ->+* S) (P : Fin 3 -> R) (u : R) : f ∘ (u • P) = f u • f ∘ P := by
  ext
  simp

/-- The equivalence setoid for a projective point representative on a Weierstrass curve. -/
@[reducible]
scoped instance : Setoid Fin 3 -> R :=
MulAction.orbitRel Rˣ Fin 3 -> R

variable (R) in
/--
Definition of `PointClass` / `PointClass` 的定义

English:
abbreviation PointClass
  signature: : Type r
  body: MulAction.orbitRel.Quotient Rˣ Fin 3 -> R

中文:
缩写 PointClass
  签名: : 类型 r
  定义体: MulAction.orbitRel.Quotient Rˣ Fin 3 -> R

Depends on / 依赖: MulAction, MulAction.orbitRel.Quotient, Quotient, orbitRel
-/
abbrev PointClass : Type r :=
MulAction.orbitRel.Quotient Rˣ Fin 3 -> R

/--
lemma `smul_equiv` / 引理 `smul_equiv`

English:
lemma smul_equiv
  given: (P : Fin 3 -> R) {u : R} (hu : IsUnit u)
  statement: u • P ≈ P
  proof: ⟨hu.unit, rfl⟩

@[simp]

中文:
引理 smul_equiv
  条件: (P : 有限集 3 -> R) {u : R} (hu : 是单位 u)
  结论: u • P ≈ P
  证明: ⟨hu.unit, rfl⟩

@[simp]

Depends on / 依赖: hu.unit
-/
lemma smul_equiv (P : Fin 3 -> R) {u : R} (hu : IsUnit u) : u • P ≈ P :=
  ⟨hu.unit, rfl⟩

@[simp]
/--
lemma `smul_eq` / 引理 `smul_eq`

English:
lemma smul_eq
  given: (P : Fin 3 -> R) {u : R} (hu : IsUnit u)
  statement: (⟦u • P⟧ : PointClass R) = ⟦P⟧
  proof: Quotient.eq.mpr smul_equiv P hu

中文:
引理 smul_eq
  条件: (P : 有限集 3 -> R) {u : R} (hu : 是单位 u)
  结论: (⟦u • P⟧ : PointClass R) = ⟦P⟧
  证明: Quotient.eq.mpr smul_equiv P hu

Depends on / 依赖: IsLocalization, Quotient, Quotient.eq.mpr, functor, smul_equiv, toHoCatLocalizerMorphism
-/
lemma smul_eq (P : Fin 3 -> R) {u : R} (hu : IsUnit u) : (⟦u • P⟧ : PointClass R) = ⟦P⟧ :=
Quotient.eq.mpr smul_equiv P hu

/--
lemma `smul_equiv_smul` / 引理 `smul_equiv_smul`

English:
lemma smul_equiv_smul
  given: (P Q : Fin 3 -> R) {u v : R} (hu : IsUnit u) (hv : IsUnit v)
  proof: by
  rw [← Quotient.eq_iff_equiv]; rw [← Quotient.eq_iff_equiv]; rw [smul_eq P hu]; rw [smul_eq Q hv]

中文:
引理 smul_equiv_smul
  条件: (P Q : 有限集 3 -> R) {u v : R} (hu : 是单位 u) (hv : 是单位 v)
  证明: by
  rw [← Quotient.eq_iff_equiv]; rw [← Quotient.eq_iff_equiv]; rw [smul_eq P hu]; rw [smul_eq Q hv]

Depends on / 依赖: Quotient, Quotient.eq_iff_equiv, eq_iff_equiv, smul_eq
-/
lemma smul_equiv_smul (P Q : Fin 3 -> R) {u v : R} (hu : IsUnit u) (hv : IsUnit v) :
    u • P ≈ v • Q ↔ P ≈ Q := by
  rw [← Quotient.eq_iff_equiv]; rw [← Quotient.eq_iff_equiv]; rw [smul_eq P hu]; rw [smul_eq Q hv]

/--
lemma `equiv_iff_eq_of_Z_eq'` / 引理 `equiv_iff_eq_of_Z_eq'`

English:
lemma equiv_iff_eq_of_Z_eq'
  given: {P Q : Fin 3 -> R} (hz : P z = Q z) (hQz : Q z in nonZeroDivisors R)
  proof: by
refine ⟨?_, Quotient.exact.comp congrArg _⟩
  rintro ⟨u, rfl⟩
  simp only [Units.smul_def, (mul_cancel_right_mem_nonZeroDivisors hQz).mp <| one_mul (Q z) ▸ hz]
  rw [one_smul]

中文:
引理 equiv_iff_eq_of_Z_eq'
  条件: {P Q : 有限集 3 -> R} (hz : P z = Q z) (hQz : Q z in nonZeroDivisors R)
  证明: by
refine ⟨?_, Quotient.exact.comp congrArg _⟩
  rintro ⟨u, rfl⟩
  simp only [Units.smul_def, (mul_cancel_right_mem_nonZeroDivisors hQz).mp <| one_mul (Q z) ▸ hz]
  rw [one_smul]

Depends on / 依赖: Quotient, Quotient.exact.comp, Units.smul_def, mul_cancel_right_mem_nonZeroDivisors, one_mul, one_smul, smul_def
-/
lemma equiv_iff_eq_of_Z_eq' {P Q : Fin 3 -> R} (hz : P z = Q z) (hQz : Q z in nonZeroDivisors R) :
    P ≈ Q ↔ P = Q := by
refine ⟨?_, Quotient.exact.comp congrArg _⟩
  rintro ⟨u, rfl⟩
  simp only [Units.smul_def, (mul_cancel_right_mem_nonZeroDivisors hQz).mp <| one_mul (Q z) ▸ hz]
  rw [one_smul]

/--
lemma `equiv_iff_eq_of_Z_eq` / 引理 `equiv_iff_eq_of_Z_eq`

English:
lemma equiv_iff_eq_of_Z_eq
  given: [NoZeroDivisors R] {P Q : Fin 3 -> R} (hz : P z = Q z) (hQz : Q z != 0)
  proof: equiv_iff_eq_of_Z_eq' hz mem_nonZeroDivisors_of_ne_zero hQz

中文:
引理 equiv_iff_eq_of_Z_eq
  条件: [无零因子 R] {P Q : 有限集 3 -> R} (hz : P z = Q z) (hQz : Q z != 0)
  证明: equiv_iff_eq_of_Z_eq' hz mem_nonZeroDivisors_of_ne_zero hQz

Depends on / 依赖: HoCat.exists_resolution, choose_spec, choose_spec.choose, equiv_iff_eq_of_Z_eq, exists_resolution, mem_nonZeroDivisors_of_ne_zero
-/
lemma equiv_iff_eq_of_Z_eq [NoZeroDivisors R] {P Q : Fin 3 -> R} (hz : P z = Q z) (hQz : Q z != 0) :
    P ≈ Q ↔ P = Q :=
equiv_iff_eq_of_Z_eq' hz mem_nonZeroDivisors_of_ne_zero hQz

/--
lemma `Z_eq_zero_of_equiv` / 引理 `Z_eq_zero_of_equiv`

English:
lemma Z_eq_zero_of_equiv
  given: {P Q : Fin 3 -> R} (h : P ≈ Q)
  statement: P z = 0 ↔ Q z = 0
  proof: by
  rcases h with ⟨_, rfl⟩
  simp only [Units.smul_def, smul_fin3_ext, Units.mul_right_eq_zero]

中文:
引理 Z_eq_zero_of_equiv
  条件: {P Q : 有限集 3 -> R} (h : P ≈ Q)
  结论: P z = 0 ↔ Q z = 0
  证明: by
  rcases h with ⟨_, rfl⟩
  simp only [Units.smul_def, smul_fin3_ext, Units.mul_right_eq_zero]

Depends on / 依赖: Units.mul_right_eq_zero, Units.smul_def, mul_right_eq_zero, smul_def, smul_fin3_ext
-/
lemma Z_eq_zero_of_equiv {P Q : Fin 3 -> R} (h : P ≈ Q) : P z = 0 ↔ Q z = 0 := by
  rcases h with ⟨_, rfl⟩
  simp only [Units.smul_def, smul_fin3_ext, Units.mul_right_eq_zero]

/--
lemma `X_eq_of_equiv` / 引理 `X_eq_of_equiv`

English:
lemma X_eq_of_equiv
  given: {P Q : Fin 3 -> R} (h : P ≈ Q)
  statement: P x * Q z = Q x * P z
  proof: by
  rcases h with ⟨u, rfl⟩
  simp only [Units.smul_def, smul_fin3_ext]
  ring1

中文:
引理 X_eq_of_equiv
  条件: {P Q : 有限集 3 -> R} (h : P ≈ Q)
  结论: P x * Q z = Q x * P z
  证明: by
  rcases h with ⟨u, rfl⟩
  simp only [Units.smul_def, smul_fin3_ext]
  ring1

Depends on / 依赖: HoCat.exists_resolution, Units.smul_def, choose_spec, choose_spec.choose_spec.choose_spec, exists_resolution, smul_def, smul_fin3_ext
-/
lemma X_eq_of_equiv {P Q : Fin 3 -> R} (h : P ≈ Q) : P x * Q z = Q x * P z := by
  rcases h with ⟨u, rfl⟩
  simp only [Units.smul_def, smul_fin3_ext]
  ring1

/--
lemma `Y_eq_of_equiv` / 引理 `Y_eq_of_equiv`

English:
lemma Y_eq_of_equiv
  given: {P Q : Fin 3 -> R} (h : P ≈ Q)
  statement: P y * Q z = Q y * P z
  proof: by
  rcases h with ⟨u, rfl⟩
  simp only [Units.smul_def, smul_fin3_ext]
  ring1

中文:
引理 Y_eq_of_equiv
  条件: {P Q : 有限集 3 -> R} (h : P ≈ Q)
  结论: P y * Q z = Q y * P z
  证明: by
  rcases h with ⟨u, rfl⟩
  simp only [Units.smul_def, smul_fin3_ext]
  ring1

Depends on / 依赖: HoCat.exists_resolution, Units.smul_def, choose_spec, choose_spec.choose_spec.choose_spec, exists_resolution, smul_def, smul_fin3_ext
-/
lemma Y_eq_of_equiv {P Q : Fin 3 -> R} (h : P ≈ Q) : P y * Q z = Q y * P z := by
  rcases h with ⟨u, rfl⟩
  simp only [Units.smul_def, smul_fin3_ext]
  ring1

/--
lemma `not_equiv_of_Z_eq_zero_left` / 引理 `not_equiv_of_Z_eq_zero_left`

English:
lemma not_equiv_of_Z_eq_zero_left
  given: {P Q : Fin 3 -> R} (hPz : P z = 0) (hQz : Q z != 0)
  statement: ¬P ≈ Q
  proof: fun h => hQz (Z_eq_zero_of_equiv h).mp hPz

中文:
引理 not_equiv_of_Z_eq_zero_left
  条件: {P Q : 有限集 3 -> R} (hPz : P z = 0) (hQz : Q z != 0)
  结论: ¬P ≈ Q
  证明: fun h => hQz (Z_eq_zero_of_equiv h).mp hPz

Depends on / 依赖: HoCat.pResolutionObj, Z_eq_zero_of_equiv, isFibrant_of_fibration, pResolutionObj
-/
lemma not_equiv_of_Z_eq_zero_left {P Q : Fin 3 -> R} (hPz : P z = 0) (hQz : Q z != 0) : ¬P ≈ Q :=
fun h => hQz (Z_eq_zero_of_equiv h).mp hPz

/--
lemma `not_equiv_of_Z_eq_zero_right` / 引理 `not_equiv_of_Z_eq_zero_right`

English:
lemma not_equiv_of_Z_eq_zero_right
  given: {P Q : Fin 3 -> R} (hPz : P z != 0) (hQz : Q z = 0)
  statement: ¬P ≈ Q
  proof: fun h => hPz (Z_eq_zero_of_equiv h).mpr hQz

中文:
引理 not_equiv_of_Z_eq_zero_right
  条件: {P Q : 有限集 3 -> R} (hPz : P z != 0) (hQz : Q z = 0)
  结论: ¬P ≈ Q
  证明: fun h => hPz (Z_eq_zero_of_equiv h).mpr hQz

Depends on / 依赖: Z_eq_zero_of_equiv
-/
lemma not_equiv_of_Z_eq_zero_right {P Q : Fin 3 -> R} (hPz : P z != 0) (hQz : Q z = 0) : ¬P ≈ Q :=
fun h => hPz (Z_eq_zero_of_equiv h).mpr hQz

/--
lemma `not_equiv_of_X_ne` / 引理 `not_equiv_of_X_ne`

English:
lemma not_equiv_of_X_ne
  given: {P Q : Fin 3 -> R} (hx : P x * Q z != Q x * P z)
  statement: ¬P ≈ Q
  proof: hx.comp X_eq_of_equiv

中文:
引理 not_equiv_of_X_ne
  条件: {P Q : 有限集 3 -> R} (hx : P x * Q z != Q x * P z)
  结论: ¬P ≈ Q
  证明: hx.comp X_eq_of_equiv

Depends on / 依赖: X_eq_of_equiv, hx.comp
-/
lemma not_equiv_of_X_ne {P Q : Fin 3 -> R} (hx : P x * Q z != Q x * P z) : ¬P ≈ Q :=
  hx.comp X_eq_of_equiv

/--
lemma `not_equiv_of_Y_ne` / 引理 `not_equiv_of_Y_ne`

English:
lemma not_equiv_of_Y_ne
  given: {P Q : Fin 3 -> R} (hy : P y * Q z != Q y * P z)
  statement: ¬P ≈ Q
  proof: hy.comp Y_eq_of_equiv

中文:
引理 not_equiv_of_Y_ne
  条件: {P Q : 有限集 3 -> R} (hy : P y * Q z != Q y * P z)
  结论: ¬P ≈ Q
  证明: hy.comp Y_eq_of_equiv

Depends on / 依赖: Y_eq_of_equiv, hy.comp
-/
lemma not_equiv_of_Y_ne {P Q : Fin 3 -> R} (hy : P y * Q z != Q y * P z) : ¬P ≈ Q :=
  hy.comp Y_eq_of_equiv

/--
lemma `equiv_of_X_eq_of_Y_eq` / 引理 `equiv_of_X_eq_of_Y_eq`

English:
lemma equiv_of_X_eq_of_Y_eq
  statement: {P Q : Fin 3 -> F} (hPz : P z != 0) (hQz : Q z != 0)
  proof: by
  use Units.mk0 _ hPz / Units.mk0 _ hQz
  simp only [Units.smul_def, smul_fin3, Units.val_div_eq_div_val, Units.val_mk0, mul_comm, mul_div,
    ← hx, ← hy, mul_div_cancel_right₀ _ hQz, fin3_def]

中文:
引理 equiv_of_X_eq_of_Y_eq
  结论: {P Q : 有限集 3 -> F} (hPz : P z != 0) (hQz : Q z != 0)
  证明: by
  use Units.mk0 _ hPz / Units.mk0 _ hQz
  simp only [Units.smul_def, smul_fin3, Units.val_div_eq_div_val, Units.val_mk0, mul_comm, mul_div,
    ← hx, ← hy, mul_div_cancel_right₀ _ hQz, fin3_def]

Depends on / 依赖: Units.mk0, Units.smul_def, Units.val_div_eq_div_val, Units.val_mk0, fin3_def, mul_comm, mul_div, smul_def, smul_fin3, val_div_eq_div_val, val_mk0
-/
lemma equiv_of_X_eq_of_Y_eq {P Q : Fin 3 -> F} (hPz : P z != 0) (hQz : Q z != 0)
    (hx : P x * Q z = Q x * P z) (hy : P y * Q z = Q y * P z) : P ≈ Q := by
  use Units.mk0 _ hPz / Units.mk0 _ hQz
  simp only [Units.smul_def, smul_fin3, Units.val_div_eq_div_val, Units.val_mk0, mul_comm, mul_div,
    ← hx, ← hy, mul_div_cancel_right₀ _ hQz, fin3_def]

/--
lemma `equiv_some_of_Z_ne_zero` / 引理 `equiv_some_of_Z_ne_zero`

English:
lemma equiv_some_of_Z_ne_zero
  given: {P : Fin 3 -> F} (hPz : P z != 0)
  statement: P ≈ ![P x / P z, P y / P z, 1]
  proof: equiv_of_X_eq_of_Y_eq hPz one_ne_zero
    (by linear_combination (norm := (matrix_simp; ring1)) -P x * div_self hPz)
    (by linear_combination (norm := (matrix_simp; ring1)) -P y * div_self hPz)

中文:
引理 equiv_some_of_Z_ne_zero
  条件: {P : 有限集 3 -> F} (hPz : P z != 0)
  结论: P ≈ ![P x / P z, P y / P z, 1]
  证明: equiv_of_X_eq_of_Y_eq hPz one_ne_zero
    (by linear_combination (norm := (matrix_simp; ring1)) -P x * div_self hPz)
    (by linear_combination (norm := (matrix_simp; ring1)) -P y * div_self hPz)

Depends on / 依赖: div_self, equiv_of_X_eq_of_Y_eq, linear_combination, matrix_simp, one_ne_zero
-/
lemma equiv_some_of_Z_ne_zero {P : Fin 3 -> F} (hPz : P z != 0) : P ≈ ![P x / P z, P y / P z, 1] :=
  equiv_of_X_eq_of_Y_eq hPz one_ne_zero
    (by linear_combination (norm := (matrix_simp; ring1)) -P x * div_self hPz)
    (by linear_combination (norm := (matrix_simp; ring1)) -P y * div_self hPz)

/--
lemma `X_eq_iff` / 引理 `X_eq_iff`

English:
lemma X_eq_iff
  given: {P Q : Fin 3 -> F} (hPz : P z != 0) (hQz : Q z != 0)
  proof: (div_eq_div_iff hPz hQz).symm

中文:
引理 X_eq_iff
  条件: {P Q : 有限集 3 -> F} (hPz : P z != 0) (hQz : Q z != 0)
  证明: (div_eq_div_iff hPz hQz).symm

Depends on / 依赖: div_eq_div_iff
-/
lemma X_eq_iff {P Q : Fin 3 -> F} (hPz : P z != 0) (hQz : Q z != 0) :
    P x * Q z = Q x * P z ↔ P x / P z = Q x / Q z :=
  (div_eq_div_iff hPz hQz).symm

/--
lemma `Y_eq_iff` / 引理 `Y_eq_iff`

English:
lemma Y_eq_iff
  given: {P Q : Fin 3 -> F} (hPz : P z != 0) (hQz : Q z != 0)
  proof: (div_eq_div_iff hPz hQz).symm

中文:
引理 Y_eq_iff
  条件: {P Q : 有限集 3 -> F} (hPz : P z != 0) (hQz : Q z != 0)
  证明: (div_eq_div_iff hPz hQz).symm

Depends on / 依赖: div_eq_div_iff
-/
lemma Y_eq_iff {P Q : Fin 3 -> F} (hPz : P z != 0) (hQz : Q z != 0) :
    P y * Q z = Q y * P z ↔ P y / P z = Q y / Q z :=
  (div_eq_div_iff hPz hQz).symm

/-! ## Weierstrass equations in projective coordinates -/

variable (W') in
/--
Definition of `polynomial` / `polynomial` 的定义

English:
definition polynomial
  signature: : MvPolynomial (Fin 3) R
  body: Y ^ 2 * Z + C W'.a₁ * X * Y * Z + C W'.a₃ * Y * Z ^ 2
    - (X ^ 3 + C W'.a₂ * X ^ 2 * Z + C W'.a₄ * X * Z ^ 2 + C W'.a₆ * Z ^ 3)

中文:
定义 polynomial
  签名: : 多元多项式 (有限集 3) R
  定义体: Y ^ 2 * Z + C W'.a₁ * X * Y * Z + C W'.a₃ * Y * Z ^ 2
    - (X ^ 3 + C W'.a₂ * X ^ 2 * Z + C W'.a₄ * X * Z ^ 2 + C W'.a₆ * Z ^ 3)
-/
noncomputable def polynomial : MvPolynomial (Fin 3) R :=
  Y ^ 2 * Z + C W'.a₁ * X * Y * Z + C W'.a₃ * Y * Z ^ 2
    - (X ^ 3 + C W'.a₂ * X ^ 2 * Z + C W'.a₄ * X * Z ^ 2 + C W'.a₆ * Z ^ 3)

/--
lemma `eval_polynomial` / 引理 `eval_polynomial`

English:
lemma eval_polynomial
  given: (P : Fin 3 -> R)
  statement: eval P W'.polynomial =
  proof: by
  rw [polynomial]
  simp

中文:
引理 eval_polynomial
  条件: (P : 有限集 3 -> R)
  结论: eval P W'.polynomial =
  证明: by
  rw [polynomial]
  simp

Depends on / 依赖: infer_instance, polynomial, weakEquivalence_iff_of_objectProperty, weakEquivalence_toHoCat_map_iff
-/
lemma eval_polynomial (P : Fin 3 -> R) : eval P W'.polynomial =
    P y ^ 2 * P z + W'.a₁ * P x * P y * P z + W'.a₃ * P y * P z ^ 2
      - (P x ^ 3 + W'.a₂ * P x ^ 2 * P z + W'.a₄ * P x * P z ^ 2 + W'.a₆ * P z ^ 3) := by
  rw [polynomial]
  simp

/--
lemma `eval_polynomial_of_Z_ne_zero` / 引理 `eval_polynomial_of_Z_ne_zero`

English:
lemma eval_polynomial_of_Z_ne_zero
  given: {P : Fin 3 -> F} (hPz : P z != 0)
  statement: eval P W.polynomial / P z ^ 3 =
  proof: by
  linear_combination (norm := (rw [eval_polynomial, Affine.evalEval_polynomial]; ring1))
    P y ^ 2 / P z ^ 2 * div_self hPz + W.a₁ * P x * P y / P z ^ 2 * div_self hPz
      + W.a₃ * P y / P z * div_self (pow_ne_zero 2 hPz) - W.a₂ * P x ^ 2 / P z ^ 2 * div_self hPz
      - W.a₄ * P x / P z * div_self (pow_ne_zero 2 hPz) - W.a₆ * div_self (pow_ne_zero 3 hPz)

中文:
引理 eval_polynomial_of_Z_ne_zero
  条件: {P : 有限集 3 -> F} (hPz : P z != 0)
  结论: eval P W.polynomial / P z ^ 3 =
  证明: by
  linear_combination (norm := (rw [eval_polynomial, Affine.evalEval_polynomial]; ring1))
    P y ^ 2 / P z ^ 2 * div_self hPz + W.a₁ * P x * P y / P z ^ 2 * div_self hPz
      + W.a₃ * P y / P z * div_self (pow_ne_zero 2 hPz) - W.a₂ * P x ^ 2 / P z ^ 2 * div_self hPz
      - W.a₄ * P x / P z * div_self (pow_ne_zero 2 hPz) - W.a₆ * div_self (pow_ne_zero 3 hPz)

Depends on / 依赖: Affine, Affine.evalEval_polynomial, Localization, Localization.inverts, NatTrans, NatTrans.isIso_iff_isIso_app, div_self, evalEval_polynomial, eval_polynomial, infer_instance, inverts, isIso_iff_isIso_app, linear_combination, pow_ne_zero, weakEquivalence_iff, weakEquivalences
-/
lemma eval_polynomial_of_Z_ne_zero {P : Fin 3 -> F} (hPz : P z != 0) : eval P W.polynomial / P z ^ 3 =
    W.toAffine.polynomial.evalEval (P x / P z) (P y / P z) := by
  linear_combination (norm := (rw [eval_polynomial, Affine.evalEval_polynomial]; ring1))
    P y ^ 2 / P z ^ 2 * div_self hPz + W.a₁ * P x * P y / P z ^ 2 * div_self hPz
      + W.a₃ * P y / P z * div_self (pow_ne_zero 2 hPz) - W.a₂ * P x ^ 2 / P z ^ 2 * div_self hPz
      - W.a₄ * P x / P z * div_self (pow_ne_zero 2 hPz) - W.a₆ * div_self (pow_ne_zero 3 hPz)

variable (W') in
/--
Definition of `Equation` / `Equation` 的定义

English:
definition Equation
  signature: (P : Fin 3 -> R)
  body: eval P W'.polynomial = 0

中文:
定义 方程
  签名: (P : 有限集 3 -> R)
  定义体: eval P W'.polynomial = 0

Depends on / 依赖: polynomial
-/
def Equation (P : Fin 3 -> R) : Prop :=
  eval P W'.polynomial = 0

/--
lemma `equation_iff` / 引理 `equation_iff`

English:
lemma equation_iff
  given: (P : Fin 3 -> R)
  statement: W'.Equation P ↔
  proof: by
  rw [Equation]; rw [eval_polynomial]; rw [sub_eq_zero]

中文:
引理 equation_iff
  条件: (P : 有限集 3 -> R)
  结论: W'.方程 P ↔
  证明: by
  rw [Equation]; rw [eval_polynomial]; rw [sub_eq_zero]

Depends on / 依赖: Equation, eval_polynomial, sub_eq_zero
-/
lemma equation_iff (P : Fin 3 -> R) : W'.Equation P ↔
    P y ^ 2 * P z + W'.a₁ * P x * P y * P z + W'.a₃ * P y * P z ^ 2
      - (P x ^ 3 + W'.a₂ * P x ^ 2 * P z + W'.a₄ * P x * P z ^ 2 + W'.a₆ * P z ^ 3) = 0 := by
  rw [Equation]; rw [eval_polynomial]; rw [sub_eq_zero]

/--
lemma `equation_smul` / 引理 `equation_smul`

English:
lemma equation_smul
  given: (P : Fin 3 -> R) {u : R} (hu : IsUnit u)
  statement: W'.Equation (u • P) ↔ W'.Equation P
  proof: have hP (u : R) {P : Fin 3 -> R} (hP : W'.Equation P) : W'.Equation u • P := by
    rw [equation_iff] at hP ⊢
    linear_combination (norm := (simp only [smul_fin3_ext]; ring1)) u ^ 3 * hP
  ⟨fun h => by convert! hP (↑hu.unit⁻¹) h; rw [smul_smul, hu.val_inv_mul, one_smul], hP u⟩

中文:
引理 equation_smul
  条件: (P : 有限集 3 -> R) {u : R} (hu : 是单位 u)
  结论: W'.方程 (u • P) ↔ W'.方程 P
  证明: have hP (u : R) {P : Fin 3 -> R} (hP : W'.Equation P) : W'.Equation u • P := by
    rw [equation_iff] at hP ⊢
    linear_combination (norm := (simp only [smul_fin3_ext]; ring1)) u ^ 3 * hP
  ⟨fun h => by convert! hP (↑hu.unit⁻¹) h; rw [smul_smul, hu.val_inv_mul, one_smul], hP u⟩

Depends on / 依赖: Equation, convert, equation_iff, hu.unit, hu.val_inv_mul, linear_combination, one_smul, smul_fin3_ext, smul_smul, val_inv_mul
-/
lemma equation_smul (P : Fin 3 -> R) {u : R} (hu : IsUnit u) : W'.Equation (u • P) ↔ W'.Equation P :=
have hP (u : R) {P : Fin 3 -> R} (hP : W'.Equation P) : W'.Equation u • P := by
    rw [equation_iff] at hP ⊢
    linear_combination (norm := (simp only [smul_fin3_ext]; ring1)) u ^ 3 * hP
  ⟨fun h => by convert! hP (↑hu.unit⁻¹) h; rw [smul_smul, hu.val_inv_mul, one_smul], hP u⟩

/--
lemma `equation_of_equiv` / 引理 `equation_of_equiv`

English:
lemma equation_of_equiv
  given: {P Q : Fin 3 -> R} (h : P ≈ Q)
  statement: W'.Equation P ↔ W'.Equation Q
  proof: by
  rcases h with ⟨u, rfl⟩
  exact equation_smul Q u.isUnit

中文:
引理 equation_of_equiv
  条件: {P Q : 有限集 3 -> R} (h : P ≈ Q)
  结论: W'.方程 P ↔ W'.方程 Q
  证明: by
  rcases h with ⟨u, rfl⟩
  exact equation_smul Q u.isUnit

Depends on / 依赖: equation_smul, isUnit, u.isUnit
-/
lemma equation_of_equiv {P Q : Fin 3 -> R} (h : P ≈ Q) : W'.Equation P ↔ W'.Equation Q := by
  rcases h with ⟨u, rfl⟩
  exact equation_smul Q u.isUnit

/--
lemma `equation_of_Z_eq_zero` / 引理 `equation_of_Z_eq_zero`

English:
lemma equation_of_Z_eq_zero
  given: {P : Fin 3 -> R} (hPz : P z = 0)
  statement: W'.Equation P ↔ P x ^ 3 = 0
  proof: by
  simp only [equation_iff, hPz, add_zero, zero_sub, mul_zero, zero_pow <| OfNat.ofNat_ne_zero _,
    neg_eq_zero]

中文:
引理 equation_of_Z_eq_zero
  条件: {P : 有限集 3 -> R} (hPz : P z = 0)
  结论: W'.方程 P ↔ P x ^ 3 = 0
  证明: by
  simp only [equation_iff, hPz, add_zero, zero_sub, mul_zero, zero_pow <| OfNat.ofNat_ne_zero _,
    neg_eq_zero]

Depends on / 依赖: OfNat.ofNat_ne_zero, add_zero, equation_iff, mul_zero, neg_eq_zero, ofNat_ne_zero, zero_pow, zero_sub
-/
lemma equation_of_Z_eq_zero {P : Fin 3 -> R} (hPz : P z = 0) : W'.Equation P ↔ P x ^ 3 = 0 := by
  simp only [equation_iff, hPz, add_zero, zero_sub, mul_zero, zero_pow <| OfNat.ofNat_ne_zero _,
    neg_eq_zero]

/--
lemma `equation_zero` / 引理 `equation_zero`

English:
lemma equation_zero
  statement: W'.Equation ![0, 1, 0]
  proof: by
  simp only [equation_of_Z_eq_zero, fin3_def_ext, zero_pow three_ne_zero]

中文:
引理 equation_zero
  结论: W'.方程 ![0, 1, 0]
  证明: by
  simp only [equation_of_Z_eq_zero, fin3_def_ext, zero_pow three_ne_zero]

Depends on / 依赖: equation_of_Z_eq_zero, fin3_def_ext, three_ne_zero, zero_pow
-/
lemma equation_zero : W'.Equation ![0, 1, 0] := by
  simp only [equation_of_Z_eq_zero, fin3_def_ext, zero_pow three_ne_zero]

/--
lemma `equation_some` / 引理 `equation_some`

English:
lemma equation_some
  given: (a b : R)
  statement: W'.Equation ![a, b, 1] ↔ W'.toAffine.Equation a b
  proof: by
  simp only [equation_iff, Affine.equation_iff', fin3_def_ext, one_pow, mul_one]

中文:
引理 equation_some
  条件: (a b : R)
  结论: W'.方程 ![a, b, 1] ↔ W'.toAffine.方程 a b
  证明: by
  simp only [equation_iff, Affine.equation_iff', fin3_def_ext, one_pow, mul_one]

Depends on / 依赖: Affine, Affine.equation_iff, equation_iff, fin3_def_ext, infer_instance, mul_one, one_pow
-/
lemma equation_some (a b : R) : W'.Equation ![a, b, 1] ↔ W'.toAffine.Equation a b := by
  simp only [equation_iff, Affine.equation_iff', fin3_def_ext, one_pow, mul_one]

/--
lemma `equation_of_Z_ne_zero` / 引理 `equation_of_Z_ne_zero`

English:
lemma equation_of_Z_ne_zero
  given: {P : Fin 3 -> F} (hPz : P z != 0)
  proof: (equation_of_equiv <| equiv_some_of_Z_ne_zero hPz).trans equation_some ..

中文:
引理 equation_of_Z_ne_zero
  条件: {P : 有限集 3 -> F} (hPz : P z != 0)
  证明: (equation_of_equiv <| equiv_some_of_Z_ne_zero hPz).trans equation_some ..

Depends on / 依赖: IsLocalization, equation_of_equiv, equation_some, equiv_some_of_Z_ne_zero, functor, localizerMorphism
-/
lemma equation_of_Z_ne_zero {P : Fin 3 -> F} (hPz : P z != 0) :
    W.Equation P ↔ W.toAffine.Equation (P x / P z) (P y / P z) :=
(equation_of_equiv <| equiv_some_of_Z_ne_zero hPz).trans equation_some ..

/--
lemma `X_eq_zero_of_Z_eq_zero` / 引理 `X_eq_zero_of_Z_eq_zero`

English:
lemma X_eq_zero_of_Z_eq_zero
  statement: [NoZeroDivisors R] {P : Fin 3 -> R} (hP : W'.Equation P)
  proof: eq_zero_of_pow_eq_zero (equation_of_Z_eq_zero hPz).mp hP

中文:
引理 X_eq_zero_of_Z_eq_zero
  结论: [无零因子 R] {P : 有限集 3 -> R} (hP : W'.方程 P)
  证明: eq_zero_of_pow_eq_zero (equation_of_Z_eq_zero hPz).mp hP

Depends on / 依赖: eq_zero_of_pow_eq_zero, equation_of_Z_eq_zero
-/
lemma X_eq_zero_of_Z_eq_zero [NoZeroDivisors R] {P : Fin 3 -> R} (hP : W'.Equation P)
    (hPz : P z = 0) : P x = 0 :=
eq_zero_of_pow_eq_zero (equation_of_Z_eq_zero hPz).mp hP

/-! ## The nonsingular condition in projective coordinates -/

variable (W') in
/--
Definition of `polynomialX` / `polynomialX` 的定义

English:
definition polynomialX
  signature: : MvPolynomial (Fin 3) R
  body: pderiv x W'.polynomial

中文:
定义 polynomialX
  签名: : 多元多项式 (有限集 3) R
  定义体: pderiv x W'.polynomial

Depends on / 依赖: pderiv, polynomial
-/
noncomputable def polynomialX : MvPolynomial (Fin 3) R :=
  pderiv x W'.polynomial

/--
lemma `polynomialX_eq` / 引理 `polynomialX_eq`

English:
lemma polynomialX_eq
  statement: W'.polynomialX =
  proof: by
  rw [polynomialX]; rw [polynomial]
  pderiv_simp
  ring1

中文:
引理 polynomialX_eq
  结论: W'.polynomialX =
  证明: by
  rw [polynomialX]; rw [polynomial]
  pderiv_simp
  ring1

Depends on / 依赖: pderiv_simp, polynomial, polynomialX
-/
lemma polynomialX_eq : W'.polynomialX =
    C W'.a₁ * Y * Z - (C 3 * X ^ 2 + C (2 * W'.a₂) * X * Z + C W'.a₄ * Z ^ 2) := by
  rw [polynomialX]; rw [polynomial]
  pderiv_simp
  ring1

/--
lemma `eval_polynomialX` / 引理 `eval_polynomialX`

English:
lemma eval_polynomialX
  given: (P : Fin 3 -> R)
  statement: eval P W'.polynomialX =
  proof: by
  rw [polynomialX_eq]
  simp

中文:
引理 eval_polynomialX
  条件: (P : 有限集 3 -> R)
  结论: eval P W'.polynomialX =
  证明: by
  rw [polynomialX_eq]
  simp

Depends on / 依赖: polynomialX_eq
-/
lemma eval_polynomialX (P : Fin 3 -> R) : eval P W'.polynomialX =
    W'.a₁ * P y * P z - (3 * P x ^ 2 + 2 * W'.a₂ * P x * P z + W'.a₄ * P z ^ 2) := by
  rw [polynomialX_eq]
  simp

/--
lemma `eval_polynomialX_of_Z_ne_zero` / 引理 `eval_polynomialX_of_Z_ne_zero`

English:
lemma eval_polynomialX_of_Z_ne_zero
  given: {P : Fin 3 -> F} (hPz : P z != 0)
  proof: by
  linear_combination (norm := (rw [eval_polynomialX, Affine.evalEval_polynomialX]; ring1))
    W.a₁ * P y / P z * div_self hPz - 2 * W.a₂ * P x / P z * div_self hPz
      - W.a₄ * div_self (pow_ne_zero 2 hPz)

中文:
引理 eval_polynomialX_of_Z_ne_zero
  条件: {P : 有限集 3 -> F} (hPz : P z != 0)
  证明: by
  linear_combination (norm := (rw [eval_polynomialX, Affine.evalEval_polynomialX]; ring1))
    W.a₁ * P y / P z * div_self hPz - 2 * W.a₂ * P x / P z * div_self hPz
      - W.a₄ * div_self (pow_ne_zero 2 hPz)

Depends on / 依赖: Affine, Affine.evalEval_polynomialX, div_self, evalEval_polynomialX, eval_polynomialX, linear_combination, pow_ne_zero
-/
lemma eval_polynomialX_of_Z_ne_zero {P : Fin 3 -> F} (hPz : P z != 0) :
    eval P W.polynomialX / P z ^ 2 = W.toAffine.polynomialX.evalEval (P x / P z) (P y / P z) := by
  linear_combination (norm := (rw [eval_polynomialX, Affine.evalEval_polynomialX]; ring1))
    W.a₁ * P y / P z * div_self hPz - 2 * W.a₂ * P x / P z * div_self hPz
      - W.a₄ * div_self (pow_ne_zero 2 hPz)

variable (W') in
/--
Definition of `polynomialY` / `polynomialY` 的定义

English:
definition polynomialY
  signature: : MvPolynomial (Fin 3) R
  body: pderiv y W'.polynomial

中文:
定义 polynomialY
  签名: : 多元多项式 (有限集 3) R
  定义体: pderiv y W'.polynomial

Depends on / 依赖: pderiv, polynomial
-/
noncomputable def polynomialY : MvPolynomial (Fin 3) R :=
  pderiv y W'.polynomial

/--
lemma `polynomialY_eq` / 引理 `polynomialY_eq`

English:
lemma polynomialY_eq
  statement: W'.polynomialY =
  proof: by
  rw [polynomialY]; rw [polynomial]
  pderiv_simp
  ring1

中文:
引理 polynomialY_eq
  结论: W'.polynomialY =
  证明: by
  rw [polynomialY]; rw [polynomial]
  pderiv_simp
  ring1

Depends on / 依赖: pderiv_simp, polynomial, polynomialY
-/
lemma polynomialY_eq : W'.polynomialY =
    C 2 * Y * Z + C W'.a₁ * X * Z + C W'.a₃ * Z ^ 2 := by
  rw [polynomialY]; rw [polynomial]
  pderiv_simp
  ring1

/--
lemma `eval_polynomialY` / 引理 `eval_polynomialY`

English:
lemma eval_polynomialY
  given: (P : Fin 3 -> R)
  proof: by
  rw [polynomialY_eq]
  simp

中文:
引理 eval_polynomialY
  条件: (P : 有限集 3 -> R)
  证明: by
  rw [polynomialY_eq]
  simp

Depends on / 依赖: polynomialY_eq
-/
lemma eval_polynomialY (P : Fin 3 -> R) :
    eval P W'.polynomialY = 2 * P y * P z + W'.a₁ * P x * P z + W'.a₃ * P z ^ 2 := by
  rw [polynomialY_eq]
  simp

/--
lemma `eval_polynomialY_of_Z_ne_zero` / 引理 `eval_polynomialY_of_Z_ne_zero`

English:
lemma eval_polynomialY_of_Z_ne_zero
  given: {P : Fin 3 -> F} (hPz : P z != 0)
  proof: by
  linear_combination (norm := (rw [eval_polynomialY, Affine.evalEval_polynomialY]; ring1))
    2 * P y / P z * div_self hPz + W.a₁ * P x / P z * div_self hPz
      + W.a₃ * div_self (pow_ne_zero 2 hPz)

中文:
引理 eval_polynomialY_of_Z_ne_zero
  条件: {P : 有限集 3 -> F} (hPz : P z != 0)
  证明: by
  linear_combination (norm := (rw [eval_polynomialY, Affine.evalEval_polynomialY]; ring1))
    2 * P y / P z * div_self hPz + W.a₁ * P x / P z * div_self hPz
      + W.a₃ * div_self (pow_ne_zero 2 hPz)

Depends on / 依赖: Affine, Affine.evalEval_polynomialY, div_self, evalEval_polynomialY, eval_polynomialY, linear_combination, pow_ne_zero
-/
lemma eval_polynomialY_of_Z_ne_zero {P : Fin 3 -> F} (hPz : P z != 0) :
    eval P W.polynomialY / P z ^ 2 = W.toAffine.polynomialY.evalEval (P x / P z) (P y / P z) := by
  linear_combination (norm := (rw [eval_polynomialY, Affine.evalEval_polynomialY]; ring1))
    2 * P y / P z * div_self hPz + W.a₁ * P x / P z * div_self hPz
      + W.a₃ * div_self (pow_ne_zero 2 hPz)

variable (W') in
/--
Definition of `polynomialZ` / `polynomialZ` 的定义

English:
definition polynomialZ
  signature: : MvPolynomial (Fin 3) R
  body: pderiv z W'.polynomial

中文:
定义 polynomialZ
  签名: : 多元多项式 (有限集 3) R
  定义体: pderiv z W'.polynomial

Depends on / 依赖: pderiv, polynomial
-/
noncomputable def polynomialZ : MvPolynomial (Fin 3) R :=
  pderiv z W'.polynomial

/--
lemma `polynomialZ_eq` / 引理 `polynomialZ_eq`

English:
lemma polynomialZ_eq
  statement: W'.polynomialZ =
  proof: by
  rw [polynomialZ]; rw [polynomial]
  pderiv_simp
  ring1

中文:
引理 polynomialZ_eq
  结论: W'.polynomialZ =
  证明: by
  rw [polynomialZ]; rw [polynomial]
  pderiv_simp
  ring1

Depends on / 依赖: pderiv_simp, polynomial, polynomialZ
-/
lemma polynomialZ_eq : W'.polynomialZ =
    Y ^ 2 + C W'.a₁ * X * Y + C (2 * W'.a₃) * Y * Z
      - (C W'.a₂ * X ^ 2 + C (2 * W'.a₄) * X * Z + C (3 * W'.a₆) * Z ^ 2) := by
  rw [polynomialZ]; rw [polynomial]
  pderiv_simp
  ring1

/--
lemma `eval_polynomialZ` / 引理 `eval_polynomialZ`

English:
lemma eval_polynomialZ
  given: (P : Fin 3 -> R)
  statement: eval P W'.polynomialZ =
  proof: by
  rw [polynomialZ_eq]
  simp

中文:
引理 eval_polynomialZ
  条件: (P : 有限集 3 -> R)
  结论: eval P W'.polynomialZ =
  证明: by
  rw [polynomialZ_eq]
  simp

Depends on / 依赖: polynomialZ_eq
-/
lemma eval_polynomialZ (P : Fin 3 -> R) : eval P W'.polynomialZ =
    P y ^ 2 + W'.a₁ * P x * P y + 2 * W'.a₃ * P y * P z
      - (W'.a₂ * P x ^ 2 + 2 * W'.a₄ * P x * P z + 3 * W'.a₆ * P z ^ 2) := by
  rw [polynomialZ_eq]
  simp

/--
theorem `polynomial_relation` / 定理 `polynomial_relation`

English:
theorem polynomial_relation
  given: (P : Fin 3 -> R)
  statement: 3 * eval P W'.polynomial =
  proof: by
  rw [eval_polynomial]; rw [eval_polynomialX]; rw [eval_polynomialY]; rw [eval_polynomialZ]
  ring1

中文:
定理 polynomial_relation
  条件: (P : 有限集 3 -> R)
  结论: 3 * eval P W'.polynomial =
  证明: by
  rw [eval_polynomial]; rw [eval_polynomialX]; rw [eval_polynomialY]; rw [eval_polynomialZ]
  ring1

Depends on / 依赖: eval_polynomial, eval_polynomialX, eval_polynomialY, eval_polynomialZ
-/
theorem polynomial_relation (P : Fin 3 -> R) : 3 * eval P W'.polynomial =
    P x * eval P W'.polynomialX + P y * eval P W'.polynomialY + P z * eval P W'.polynomialZ := by
  rw [eval_polynomial]; rw [eval_polynomialX]; rw [eval_polynomialY]; rw [eval_polynomialZ]
  ring1

variable (W') in
-- TODO: generalise this definition to be mathematically accurate for a larger class of rings.
/--
Definition of `Nonsingular` / `Nonsingular` 的定义

English:
definition Nonsingular
  signature: (P : Fin 3 -> R)
  body: W'.Equation P ∧
    (eval P W'.polynomialX != 0 ∨ eval P W'.polynomialY != 0 ∨ eval P W'.polynomialZ != 0)

中文:
定义 非奇异
  签名: (P : 有限集 3 -> R)
  定义体: W'.Equation P ∧
    (eval P W'.polynomialX != 0 ∨ eval P W'.polynomialY != 0 ∨ eval P W'.polynomialZ != 0)

Depends on / 依赖: Equation, polynomialX, polynomialY, polynomialZ
-/
def Nonsingular (P : Fin 3 -> R) : Prop :=
  W'.Equation P ∧
    (eval P W'.polynomialX != 0 ∨ eval P W'.polynomialY != 0 ∨ eval P W'.polynomialZ != 0)

/--
lemma `nonsingular_iff` / 引理 `nonsingular_iff`

English:
lemma nonsingular_iff
  given: (P : Fin 3 -> R)
  statement: W'.Nonsingular P ↔ W'.Equation P ∧
  proof: by
  rw [Nonsingular]; rw [eval_polynomialX]; rw [eval_polynomialY]; rw [eval_polynomialZ]

中文:
引理 nonsingular_iff
  条件: (P : 有限集 3 -> R)
  结论: W'.非奇异 P ↔ W'.方程 P ∧
  证明: by
  rw [Nonsingular]; rw [eval_polynomialX]; rw [eval_polynomialY]; rw [eval_polynomialZ]

Depends on / 依赖: Nonsingular, eval_polynomialX, eval_polynomialY, eval_polynomialZ
-/
lemma nonsingular_iff (P : Fin 3 -> R) : W'.Nonsingular P ↔ W'.Equation P ∧
    (W'.a₁ * P y * P z - (3 * P x ^ 2 + 2 * W'.a₂ * P x * P z + W'.a₄ * P z ^ 2) != 0 ∨
      2 * P y * P z + W'.a₁ * P x * P z + W'.a₃ * P z ^ 2 != 0 ∨
      P y ^ 2 + W'.a₁ * P x * P y + 2 * W'.a₃ * P y * P z
        - (W'.a₂ * P x ^ 2 + 2 * W'.a₄ * P x * P z + 3 * W'.a₆ * P z ^ 2) != 0) := by
  rw [Nonsingular]; rw [eval_polynomialX]; rw [eval_polynomialY]; rw [eval_polynomialZ]

/--
lemma `nonsingular_smul` / 引理 `nonsingular_smul`

English:
lemma nonsingular_smul
  given: (P : Fin 3 -> R) {u : R} (hu : IsUnit u)
  proof: have hP {u : R} (hu : IsUnit u) {P : Fin 3 -> R} (hP : W'.Nonsingular <| u • P) :
      W'.Nonsingular P := by
    rcases (nonsingular_iff _).mp hP with ⟨hP, hP'⟩
    refine (nonsingular_iff P).mpr ⟨(equation_smul P hu).mp hP, ?_⟩
    contrapose! hP'
    simp only [smul_fin3_ext]
    exact ⟨by linear_combination (norm := ring1) u ^ 2 * hP'.left,
      by linear_combination (norm := ring1) u ^ 2 * hP'.right.left,
      by linear_combination (norm := ring1) u ^ 2 * hP'.right.right⟩
⟨hP hu, fun h => hP hu.unit⁻¹.isUnit by rwa [smul_smul, hu.val_inv_mul, one_smul]⟩

中文:
引理 nonsingular_smul
  条件: (P : 有限集 3 -> R) {u : R} (hu : 是单位 u)
  证明: have hP {u : R} (hu : IsUnit u) {P : Fin 3 -> R} (hP : W'.Nonsingular <| u • P) :
      W'.Nonsingular P := by
    rcases (nonsingular_iff _).mp hP with ⟨hP, hP'⟩
    refine (nonsingular_iff P).mpr ⟨(equation_smul P hu).mp hP, ?_⟩
    contrapose! hP'
    simp only [smul_fin3_ext]
    exact ⟨by linear_combination (norm := ring1) u ^ 2 * hP'.left,
      by linear_combination (norm := ring1) u ^ 2 * hP'.right.left,
      by linear_combination (norm := ring1) u ^ 2 * hP'.right.right⟩
⟨hP hu, fun h => hP hu.unit⁻¹.isUnit by rwa [smul_smul, hu.val_inv_mul, one_smul]⟩

Depends on / 依赖: IsUnit, Nonsingular, contrapose, equation_smul, hu.unit, isUnit, linear_combination, nonsingular_iff, right.left, right.right, smul_fin3_ext, smul_smu
-/
lemma nonsingular_smul (P : Fin 3 -> R) {u : R} (hu : IsUnit u) :
    W'.Nonsingular (u • P) ↔ W'.Nonsingular P :=
  have hP {u : R} (hu : IsUnit u) {P : Fin 3 -> R} (hP : W'.Nonsingular <| u • P) :
      W'.Nonsingular P := by
    rcases (nonsingular_iff _).mp hP with ⟨hP, hP'⟩
    refine (nonsingular_iff P).mpr ⟨(equation_smul P hu).mp hP, ?_⟩
    contrapose! hP'
    simp only [smul_fin3_ext]
    exact ⟨by linear_combination (norm := ring1) u ^ 2 * hP'.left,
      by linear_combination (norm := ring1) u ^ 2 * hP'.right.left,
      by linear_combination (norm := ring1) u ^ 2 * hP'.right.right⟩
⟨hP hu, fun h => hP hu.unit⁻¹.isUnit by rwa [smul_smul, hu.val_inv_mul, one_smul]⟩

/--
lemma `nonsingular_of_equiv` / 引理 `nonsingular_of_equiv`

English:
lemma nonsingular_of_equiv
  given: {P Q : Fin 3 -> R} (h : P ≈ Q)
  statement: W'.Nonsingular P ↔ W'.Nonsingular Q
  proof: by
  rcases h with ⟨u, rfl⟩
  exact nonsingular_smul Q u.isUnit

中文:
引理 nonsingular_of_equiv
  条件: {P Q : 有限集 3 -> R} (h : P ≈ Q)
  结论: W'.非奇异 P ↔ W'.非奇异 Q
  证明: by
  rcases h with ⟨u, rfl⟩
  exact nonsingular_smul Q u.isUnit

Depends on / 依赖: isUnit, nonsingular_smul, u.isUnit
-/
lemma nonsingular_of_equiv {P Q : Fin 3 -> R} (h : P ≈ Q) : W'.Nonsingular P ↔ W'.Nonsingular Q := by
  rcases h with ⟨u, rfl⟩
  exact nonsingular_smul Q u.isUnit

/--
lemma `nonsingular_of_Z_eq_zero` / 引理 `nonsingular_of_Z_eq_zero`

English:
lemma nonsingular_of_Z_eq_zero
  given: {P : Fin 3 -> R} (hPz : P z = 0)
  proof: by
  simp only [nonsingular_iff, hPz, add_zero, zero_sub, mul_zero,
zero_pow OfNat.ofNat_ne_zero _, neg_ne_zero, ne_self_iff_false, false_or]

中文:
引理 nonsingular_of_Z_eq_zero
  条件: {P : 有限集 3 -> R} (hPz : P z = 0)
  证明: by
  simp only [nonsingular_iff, hPz, add_zero, zero_sub, mul_zero,
zero_pow OfNat.ofNat_ne_zero _, neg_ne_zero, ne_self_iff_false, false_or]

Depends on / 依赖: OfNat.ofNat_ne_zero, add_zero, false_or, mul_zero, ne_self_iff_false, neg_ne_zero, nonsingular_iff, ofNat_ne_zero, zero_pow, zero_sub
-/
lemma nonsingular_of_Z_eq_zero {P : Fin 3 -> R} (hPz : P z = 0) :
    W'.Nonsingular P ↔
      W'.Equation P ∧ (3 * P x ^ 2 != 0 ∨ P y ^ 2 + W'.a₁ * P x * P y - W'.a₂ * P x ^ 2 != 0) := by
  simp only [nonsingular_iff, hPz, add_zero, zero_sub, mul_zero,
zero_pow OfNat.ofNat_ne_zero _, neg_ne_zero, ne_self_iff_false, false_or]

/--
lemma `nonsingular_zero` / 引理 `nonsingular_zero`

English:
lemma nonsingular_zero
  given: [Nontrivial R]
  statement: W'.Nonsingular ![0, 1, 0]
  proof: by
  simp only [nonsingular_of_Z_eq_zero, equation_zero, true_and, fin3_def_ext, ← not_and_or]
exact fun h => one_ne_zero by linear_combination (norm := ring1) h.right

中文:
引理 nonsingular_zero
  条件: [非平凡 R]
  结论: W'.非奇异 ![0, 1, 0]
  证明: by
  simp only [nonsingular_of_Z_eq_zero, equation_zero, true_and, fin3_def_ext, ← not_and_or]
exact fun h => one_ne_zero by linear_combination (norm := ring1) h.right

Depends on / 依赖: equation_zero, fin3_def_ext, h.right, linear_combination, nonsingular_of_Z_eq_zero, not_and_or, one_ne_zero, true_and
-/
lemma nonsingular_zero [Nontrivial R] : W'.Nonsingular ![0, 1, 0] := by
  simp only [nonsingular_of_Z_eq_zero, equation_zero, true_and, fin3_def_ext, ← not_and_or]
exact fun h => one_ne_zero by linear_combination (norm := ring1) h.right

/--
lemma `nonsingular_some` / 引理 `nonsingular_some`

English:
lemma nonsingular_some
  given: (a b : R)
  statement: W'.Nonsingular ![a, b, 1] ↔ W'.toAffine.Nonsingular a b
  proof: by
  simp_rw [nonsingular_iff, equation_some, fin3_def_ext, Affine.nonsingular_iff',
    Affine.equation_iff', and_congr_right_iff, ← not_and_or, not_iff_not, one_pow, mul_one,
    and_congr_right_iff, Iff.comm, iff_self_and]
  intro h ha hb
  linear_combination (norm := ring1) 3 * h - a * ha - b * hb

中文:
引理 nonsingular_some
  条件: (a b : R)
  结论: W'.非奇异 ![a, b, 1] ↔ W'.toAffine.非奇异 a b
  证明: by
  simp_rw [nonsingular_iff, equation_some, fin3_def_ext, Affine.nonsingular_iff',
    Affine.equation_iff', and_congr_right_iff, ← not_and_or, not_iff_not, one_pow, mul_one,
    and_congr_right_iff, Iff.comm, iff_self_and]
  intro h ha hb
  linear_combination (norm := ring1) 3 * h - a * ha - b * hb

Depends on / 依赖: Affine, Affine.equation_iff, Affine.nonsingular_iff, Iff.comm, and_congr_right_iff, equation_iff, equation_some, fin3_def_ext, iff_self_and, linear_combination, mul_one, nonsingular_iff, not_and_or, not_iff_not, one_pow, simp_rw
-/
lemma nonsingular_some (a b : R) : W'.Nonsingular ![a, b, 1] ↔ W'.toAffine.Nonsingular a b := by
  simp_rw [nonsingular_iff, equation_some, fin3_def_ext, Affine.nonsingular_iff',
    Affine.equation_iff', and_congr_right_iff, ← not_and_or, not_iff_not, one_pow, mul_one,
    and_congr_right_iff, Iff.comm, iff_self_and]
  intro h ha hb
  linear_combination (norm := ring1) 3 * h - a * ha - b * hb

/--
lemma `nonsingular_of_Z_ne_zero` / 引理 `nonsingular_of_Z_ne_zero`

English:
lemma nonsingular_of_Z_ne_zero
  given: {P : Fin 3 -> F} (hPz : P z != 0)
  proof: (nonsingular_of_equiv <| equiv_some_of_Z_ne_zero hPz).trans nonsingular_some ..

中文:
引理 nonsingular_of_Z_ne_zero
  条件: {P : 有限集 3 -> F} (hPz : P z != 0)
  证明: (nonsingular_of_equiv <| equiv_some_of_Z_ne_zero hPz).trans nonsingular_some ..

Depends on / 依赖: equiv_some_of_Z_ne_zero, nonsingular_of_equiv, nonsingular_some
-/
lemma nonsingular_of_Z_ne_zero {P : Fin 3 -> F} (hPz : P z != 0) :
    W.Nonsingular P ↔ W.toAffine.Nonsingular (P x / P z) (P y / P z) :=
(nonsingular_of_equiv <| equiv_some_of_Z_ne_zero hPz).trans nonsingular_some ..

/--
lemma `nonsingular_iff_of_Z_ne_zero` / 引理 `nonsingular_iff_of_Z_ne_zero`

English:
lemma nonsingular_iff_of_Z_ne_zero
  given: {P : Fin 3 -> F} (hPz : P z != 0)
  proof: by
  rw [nonsingular_of_Z_ne_zero hPz]; rw [Affine.Nonsingular]; rw [← equation_of_Z_ne_zero hPz]; rw [← eval_polynomialX_of_Z_ne_zero hPz]; rw [div_ne_zero_iff]; rw [and_iff_left pow_ne_zero 2 hPz]; rw [← eval_polynomialY_of_Z_ne_zero hPz]; rw [div_ne_zero_iff]; rw [and_iff_left pow_ne_zero 2 hPz]

中文:
引理 nonsingular_iff_of_Z_ne_zero
  条件: {P : 有限集 3 -> F} (hPz : P z != 0)
  证明: by
  rw [nonsingular_of_Z_ne_zero hPz]; rw [Affine.Nonsingular]; rw [← equation_of_Z_ne_zero hPz]; rw [← eval_polynomialX_of_Z_ne_zero hPz]; rw [div_ne_zero_iff]; rw [and_iff_left pow_ne_zero 2 hPz]; rw [← eval_polynomialY_of_Z_ne_zero hPz]; rw [div_ne_zero_iff]; rw [and_iff_left pow_ne_zero 2 hPz]

Depends on / 依赖: Affine, Affine.Nonsingular, Nonsingular, and_iff_left, div_ne_zero_iff, equation_of_Z_ne_zero, eval_polynomialX_of_Z_ne_zero, eval_polynomialY_of_Z_ne_zero, nonsingular_of_Z_ne_zero, pow_ne_zero
-/
lemma nonsingular_iff_of_Z_ne_zero {P : Fin 3 -> F} (hPz : P z != 0) :
    W.Nonsingular P ↔ W.Equation P ∧ (eval P W.polynomialX != 0 ∨ eval P W.polynomialY != 0) := by
  rw [nonsingular_of_Z_ne_zero hPz]; rw [Affine.Nonsingular]; rw [← equation_of_Z_ne_zero hPz]; rw [← eval_polynomialX_of_Z_ne_zero hPz]; rw [div_ne_zero_iff]; rw [and_iff_left pow_ne_zero 2 hPz]; rw [← eval_polynomialY_of_Z_ne_zero hPz]; rw [div_ne_zero_iff]; rw [and_iff_left pow_ne_zero 2 hPz]

/--
lemma `Y_ne_zero_of_Z_eq_zero` / 引理 `Y_ne_zero_of_Z_eq_zero`

English:
lemma Y_ne_zero_of_Z_eq_zero
  statement: [NoZeroDivisors R] {P : Fin 3 -> R} (hP : W'.Nonsingular P)
  proof: by
  intro hPy
  simp only [nonsingular_of_Z_eq_zero hPz, X_eq_zero_of_Z_eq_zero hP.left hPz, hPy, add_zero,
    sub_zero, mul_zero, zero_pow two_ne_zero, or_self, ne_self_iff_false, and_false] at hP

中文:
引理 Y_ne_zero_of_Z_eq_zero
  结论: [无零因子 R] {P : 有限集 3 -> R} (hP : W'.非奇异 P)
  证明: by
  intro hPy
  simp only [nonsingular_of_Z_eq_zero hPz, X_eq_zero_of_Z_eq_zero hP.left hPz, hPy, add_zero,
    sub_zero, mul_zero, zero_pow two_ne_zero, or_self, ne_self_iff_false, and_false] at hP

Depends on / 依赖: X_eq_zero_of_Z_eq_zero, add_zero, and_false, hP.left, mul_zero, ne_self_iff_false, nonsingular_of_Z_eq_zero, or_self, sub_zero, two_ne_zero, zero_pow
-/
lemma Y_ne_zero_of_Z_eq_zero [NoZeroDivisors R] {P : Fin 3 -> R} (hP : W'.Nonsingular P)
    (hPz : P z = 0) : P y != 0 := by
  intro hPy
  simp only [nonsingular_of_Z_eq_zero hPz, X_eq_zero_of_Z_eq_zero hP.left hPz, hPy, add_zero,
    sub_zero, mul_zero, zero_pow two_ne_zero, or_self, ne_self_iff_false, and_false] at hP

/--
lemma `isUnit_Y_of_Z_eq_zero` / 引理 `isUnit_Y_of_Z_eq_zero`

English:
lemma isUnit_Y_of_Z_eq_zero
  given: {P : Fin 3 -> F} (hP : W.Nonsingular P) (hPz : P z = 0)
  statement: IsUnit (P y)
  proof: (Y_ne_zero_of_Z_eq_zero hP hPz).isUnit

中文:
引理 isUnit_Y_of_Z_eq_zero
  条件: {P : 有限集 3 -> F} (hP : W.非奇异 P) (hPz : P z = 0)
  结论: 是单位 (P y)
  证明: (Y_ne_zero_of_Z_eq_zero hP hPz).isUnit

Depends on / 依赖: Y_ne_zero_of_Z_eq_zero, isUnit
-/
lemma isUnit_Y_of_Z_eq_zero {P : Fin 3 -> F} (hP : W.Nonsingular P) (hPz : P z = 0) : IsUnit (P y) :=
  (Y_ne_zero_of_Z_eq_zero hP hPz).isUnit

/--
lemma `equiv_of_Z_eq_zero` / 引理 `equiv_of_Z_eq_zero`

English:
lemma equiv_of_Z_eq_zero
  statement: {P Q : Fin 3 -> F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q)
  proof: by
  use (isUnit_Y_of_Z_eq_zero hP hPz).unit / (isUnit_Y_of_Z_eq_zero hQ hQz).unit
  simp only [Units.smul_def, smul_fin3, X_eq_zero_of_Z_eq_zero hQ.left hQz, hQz, mul_zero,
    Units.val_div_eq_div_val, IsUnit.unit_spec, (isUnit_Y_of_Z_eq_zero hQ hQz).div_mul_cancel]
  conv_rhs => rw [← fin3_def P, X_eq_zero_of_Z_eq_zero hP.left hPz, hPz]

中文:
引理 equiv_of_Z_eq_zero
  结论: {P Q : 有限集 3 -> F} (hP : W.非奇异 P) (hQ : W.非奇异 Q)
  证明: by
  use (isUnit_Y_of_Z_eq_zero hP hPz).unit / (isUnit_Y_of_Z_eq_zero hQ hQz).unit
  simp only [Units.smul_def, smul_fin3, X_eq_zero_of_Z_eq_zero hQ.left hQz, hQz, mul_zero,
    Units.val_div_eq_div_val, IsUnit.unit_spec, (isUnit_Y_of_Z_eq_zero hQ hQz).div_mul_cancel]
  conv_rhs => rw [← fin3_def P, X_eq_zero_of_Z_eq_zero hP.left hPz, hPz]

Depends on / 依赖: IsUnit, IsUnit.unit_spec, Units.smul_def, Units.val_div_eq_div_val, X_eq_zero_of_Z_eq_zero, conv_rhs, div_mul_cancel, fin3_def, hP.left, hQ.left, isUnit_Y_of_Z_eq_zero, mul_zero, smul_def, smul_fin3, unit_spec, val_div_eq_div_val
-/
lemma equiv_of_Z_eq_zero {P Q : Fin 3 -> F} (hP : W.Nonsingular P) (hQ : W.Nonsingular Q)
    (hPz : P z = 0) (hQz : Q z = 0) : P ≈ Q := by
  use (isUnit_Y_of_Z_eq_zero hP hPz).unit / (isUnit_Y_of_Z_eq_zero hQ hQz).unit
  simp only [Units.smul_def, smul_fin3, X_eq_zero_of_Z_eq_zero hQ.left hQz, hQz, mul_zero,
    Units.val_div_eq_div_val, IsUnit.unit_spec, (isUnit_Y_of_Z_eq_zero hQ hQz).div_mul_cancel]
  conv_rhs => rw [← fin3_def P, X_eq_zero_of_Z_eq_zero hP.left hPz, hPz]

/--
lemma `equiv_zero_of_Z_eq_zero` / 引理 `equiv_zero_of_Z_eq_zero`

English:
lemma equiv_zero_of_Z_eq_zero
  given: {P : Fin 3 -> F} (hP : W.Nonsingular P) (hPz : P z = 0)
  proof: equiv_of_Z_eq_zero hP nonsingular_zero hPz rfl

中文:
引理 equiv_zero_of_Z_eq_zero
  条件: {P : 有限集 3 -> F} (hP : W.非奇异 P) (hPz : P z = 0)
  证明: equiv_of_Z_eq_zero hP nonsingular_zero hPz rfl

Depends on / 依赖: equiv_of_Z_eq_zero, nonsingular_zero
-/
lemma equiv_zero_of_Z_eq_zero {P : Fin 3 -> F} (hP : W.Nonsingular P) (hPz : P z = 0) :
    P ≈ ![0, 1, 0] :=
  equiv_of_Z_eq_zero hP nonsingular_zero hPz rfl

/--
lemma `comp_equiv_comp` / 引理 `comp_equiv_comp`

English:
lemma comp_equiv_comp
  statement: (f : F ->+* K) {P Q : Fin 3 -> F} (hP : W.Nonsingular P)
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · by_cases hz : f (P z) = 0
· exact equiv_of_Z_eq_zero hP hQ ((map_eq_zero_iff f f.injective).mp hz)
(map_eq_zero_iff f f.injective).mp (Z_eq_zero_of_equiv h).mp hz
    · refine equiv_of_X_eq_of_Y_eq ((map_ne_zero_iff f f.injective).mp hz)
        ((map_ne_zero_iff f f.injective).mp <| hz.comp (Z_eq_zero_of_equiv h).mpr) ?_ ?_
      all_goals apply f.injective; map_simp
      exacts [X_eq_of_equiv h, Y_eq_of_equiv h]
  · rcases h with ⟨u, rfl⟩
    exact ⟨Units.map f u, (comp_smul ..).symm⟩

中文:
引理 comp_equiv_comp
  结论: (f : F ->+* K) {P Q : 有限集 3 -> F} (hP : W.非奇异 P)
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · by_cases hz : f (P z) = 0
· exact equiv_of_Z_eq_zero hP hQ ((map_eq_zero_iff f f.injective).mp hz)
(map_eq_zero_iff f f.injective).mp (Z_eq_zero_of_equiv h).mp hz
    · refine equiv_of_X_eq_of_Y_eq ((map_ne_zero_iff f f.injective).mp hz)
        ((map_ne_zero_iff f f.injective).mp <| hz.comp (Z_eq_zero_of_equiv h).mpr) ?_ ?_
      all_goals apply f.injective; map_simp
      exacts [X_eq_of_equiv h, Y_eq_of_equiv h]
  · rcases h with ⟨u, rfl⟩
    exact ⟨Units.map f u, (comp_smul ..).symm⟩

Depends on / 依赖: Units.map, X_eq_of_equiv, Y_eq_of_equiv, Z_eq_zero_of_equiv, all_goals, comp_smul, equiv_of_X_eq_of_Y_eq, equiv_of_Z_eq_zero, exacts, f.injective, hz.comp, injective, map_eq_zero_iff, map_ne_zero_iff, map_simp
-/
lemma comp_equiv_comp (f : F ->+* K) {P Q : Fin 3 -> F} (hP : W.Nonsingular P)
    (hQ : W.Nonsingular Q) : f ∘ P ≈ f ∘ Q ↔ P ≈ Q := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · by_cases hz : f (P z) = 0
· exact equiv_of_Z_eq_zero hP hQ ((map_eq_zero_iff f f.injective).mp hz)
(map_eq_zero_iff f f.injective).mp (Z_eq_zero_of_equiv h).mp hz
    · refine equiv_of_X_eq_of_Y_eq ((map_ne_zero_iff f f.injective).mp hz)
        ((map_ne_zero_iff f f.injective).mp <| hz.comp (Z_eq_zero_of_equiv h).mpr) ?_ ?_
      all_goals apply f.injective; map_simp
      exacts [X_eq_of_equiv h, Y_eq_of_equiv h]
  · rcases h with ⟨u, rfl⟩
    exact ⟨Units.map f u, (comp_smul ..).symm⟩

variable (W') in
/--
Definition of `NonsingularLift` / `NonsingularLift` 的定义

English:
definition NonsingularLift
  signature: (P : PointClass R)
  body: P.lift W'.Nonsingular fun _ _ => propext ∘ nonsingular_of_equiv

中文:
定义 NonsingularLift
  签名: (P : PointClass R)
  定义体: P.lift W'.Nonsingular fun _ _ => propext ∘ nonsingular_of_equiv

Depends on / 依赖: Nonsingular, P.lift, nonsingular_of_equiv, propext
-/
def NonsingularLift (P : PointClass R) : Prop :=
  P.lift W'.Nonsingular fun _ _ => propext ∘ nonsingular_of_equiv

/--
lemma `nonsingularLift_iff` / 引理 `nonsingularLift_iff`

English:
lemma nonsingularLift_iff
  given: (P : Fin 3 -> R)
  statement: W'.NonsingularLift ⟦P⟧ ↔ W'.Nonsingular P
  proof: Iff.rfl

中文:
引理 nonsingularLift_iff
  条件: (P : 有限集 3 -> R)
  结论: W'.NonsingularLift ⟦P⟧ ↔ W'.非奇异 P
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma nonsingularLift_iff (P : Fin 3 -> R) : W'.NonsingularLift ⟦P⟧ ↔ W'.Nonsingular P :=
  Iff.rfl

/--
lemma `nonsingularLift_zero` / 引理 `nonsingularLift_zero`

English:
lemma nonsingularLift_zero
  given: [Nontrivial R]
  statement: W'.NonsingularLift ⟦![0, 1, 0]⟧
  proof: nonsingular_zero

中文:
引理 nonsingularLift_zero
  条件: [非平凡 R]
  结论: W'.NonsingularLift ⟦![0, 1, 0]⟧
  证明: nonsingular_zero

Depends on / 依赖: nonsingular_zero
-/
lemma nonsingularLift_zero [Nontrivial R] : W'.NonsingularLift ⟦![0, 1, 0]⟧ :=
  nonsingular_zero

/--
lemma `nonsingularLift_some` / 引理 `nonsingularLift_some`

English:
lemma nonsingularLift_some
  given: (a b : R)
  proof: nonsingular_some a b

中文:
引理 nonsingularLift_some
  条件: (a b : R)
  证明: nonsingular_some a b

Depends on / 依赖: R.hw, nonsingular_some, weakEquivalence_iff
-/
lemma nonsingularLift_some (a b : R) :
    W'.NonsingularLift ⟦![a, b, 1]⟧ ↔ W'.toAffine.Nonsingular a b :=
  nonsingular_some a b

/-! ## Maps and base changes -/

variable (W') (f : R ->+* S)

/--
Definition of `map` / `map` 的定义

English:
abbreviation map
  signature: : Projective S
  body: WeierstrassCurve.map W' f

中文:
缩写 map
  签名: : 投射 S
  定义体: WeierstrassCurve.map W' f

Depends on / 依赖: CommSq, HoCat.pResolutionObj, HoCat.resolutionObj, LeftResolution, Nonempty, WeierstrassCurve, WeierstrassCurve.map, Zigzag, Zigzag.of_hom, initial, initial.to, localizerMorphism, mem_weakEquivalences, of_hom, pResolutionObj, resolutionObj, some.symm, some.trans, sq.lift, zigzag_isConnected
-/
abbrev map : Projective S :=
  WeierstrassCurve.map W' f

variable (S) in
/--
Definition of `baseChange` / `baseChange` 的定义

English:
abbreviation baseChange
  signature: [Algebra R S]
  body: WeierstrassCurve.baseChange W' S

中文:
缩写 baseChange
  签名: [代数 R S]
  定义体: WeierstrassCurve.baseChange W' S

Depends on / 依赖: WeierstrassCurve, WeierstrassCurve.baseChange, baseChange
-/
abbrev baseChange [Algebra R S] : Projective S :=
  WeierstrassCurve.baseChange W' S

/-- The notation `\textf` for `WeierstrassCurve.Projective.baseChange W S`. -/
scoped notation:max W:max "⁄" S:max => baseChange W S

@[simp]
/--
lemma `map_polynomial` / 引理 `map_polynomial`

English:
lemma map_polynomial
  statement: (W'.map f).polynomial = .map f W'.polynomial
  proof: by
  simp only [polynomial]
  map_simp

中文:
引理 map_polynomial
  结论: (W'.map f).polynomial = .map f W'.polynomial
  证明: by
  simp only [polynomial]
  map_simp

Depends on / 依赖: map_simp, polynomial
-/
lemma map_polynomial : (W'.map f).polynomial = .map f W'.polynomial := by
  simp only [polynomial]
  map_simp

variable {W'} in
/--
lemma `Equation.map` / 引理 `Equation.map`

English:
lemma Equation.map
  given: {P : Fin 3 -> R} (h : W'.Equation P)
  statement: (W'.map f).Equation (f ∘ P)
  proof: by
  rw [Equation]; rw [map_polynomial]; rw [eval_map]; rw [← eval₂_comp]; rw [h]; rw [map_zero]

中文:
引理 方程.map
  条件: {P : 有限集 3 -> R} (h : W'.方程 P)
  结论: (W'.map f).方程 (f ∘ P)
  证明: by
  rw [Equation]; rw [map_polynomial]; rw [eval_map]; rw [← eval₂_comp]; rw [h]; rw [map_zero]

Depends on / 依赖: R.hw, weakEquivalence_iff
-/
lemma Equation.map {P : Fin 3 -> R} (h : W'.Equation P) : (W'.map f).Equation (f ∘ P) := by
  rw [Equation]; rw [map_polynomial]; rw [eval_map]; rw [← eval₂_comp]; rw [h]; rw [map_zero]

variable {f} in
@[simp]
/--
lemma `map_equation` / 引理 `map_equation`

English:
lemma map_equation
  given: (hf : Function.Injective f) (P : Fin 3 -> R)
  proof: by
  simp only [Equation, map_polynomial, eval_map, ← eval₂_comp, map_eq_zero_iff f hf]

@[simp]

中文:
引理 map_equation
  条件: (hf : 函数.单射 f) (P : 有限集 3 -> R)
  证明: by
  simp only [Equation, map_polynomial, eval_map, ← eval₂_comp, map_eq_zero_iff f hf]

@[simp]

Depends on / 依赖: CommSq, Equation, HoCat.iResolutionObj, HoCat.resolutionObj, Nonempty, RightResolution, Zigzag, Zigzag.of_inv, eval_map, iResolutionObj, localizerMorphism, map_eq_zero_iff, map_polynomial, mem_weakEquivalences, of_inv, resolutionObj, some.symm, some.trans, sq.lift, terminal
-/
lemma map_equation (hf : Function.Injective f) (P : Fin 3 -> R) :
    (W'.map f).Equation (f ∘ P) ↔ W'.Equation P := by
  simp only [Equation, map_polynomial, eval_map, ← eval₂_comp, map_eq_zero_iff f hf]

@[simp]
/--
lemma `map_polynomialX` / 引理 `map_polynomialX`

English:
lemma map_polynomialX
  statement: (W'.map f).polynomialX = .map f W'.polynomialX
  proof: by
  simp only [polynomialX, map_polynomial, pderiv_map]

@[simp]

中文:
引理 map_polynomialX
  结论: (W'.map f).polynomialX = .map f W'.polynomialX
  证明: by
  simp only [polynomialX, map_polynomial, pderiv_map]

@[simp]

Depends on / 依赖: map_polynomial, pderiv_map, polynomialX
-/
lemma map_polynomialX : (W'.map f).polynomialX = .map f W'.polynomialX := by
  simp only [polynomialX, map_polynomial, pderiv_map]

@[simp]
/--
lemma `map_polynomialY` / 引理 `map_polynomialY`

English:
lemma map_polynomialY
  statement: (W'.map f).polynomialY = .map f W'.polynomialY
  proof: by
  simp only [polynomialY, map_polynomial, pderiv_map]

@[simp]

中文:
引理 map_polynomialY
  结论: (W'.map f).polynomialY = .map f W'.polynomialY
  证明: by
  simp only [polynomialY, map_polynomial, pderiv_map]

@[simp]

Depends on / 依赖: map_polynomial, pderiv_map, polynomialY
-/
lemma map_polynomialY : (W'.map f).polynomialY = .map f W'.polynomialY := by
  simp only [polynomialY, map_polynomial, pderiv_map]

@[simp]
/--
lemma `map_polynomialZ` / 引理 `map_polynomialZ`

English:
lemma map_polynomialZ
  statement: (W'.map f).polynomialZ = .map f W'.polynomialZ
  proof: by
  simp only [polynomialZ, map_polynomial, pderiv_map]

中文:
引理 map_polynomialZ
  结论: (W'.map f).polynomialZ = .map f W'.polynomialZ
  证明: by
  simp only [polynomialZ, map_polynomial, pderiv_map]

Depends on / 依赖: map_polynomial, pderiv_map, polynomialZ
-/
lemma map_polynomialZ : (W'.map f).polynomialZ = .map f W'.polynomialZ := by
  simp only [polynomialZ, map_polynomial, pderiv_map]

variable {f} in
@[simp]
/--
lemma `map_nonsingular` / 引理 `map_nonsingular`

English:
lemma map_nonsingular
  given: (hf : Function.Injective f) (P : Fin 3 -> R)
  proof: by
  simp only [Nonsingular, W'.map_equation hf, map_polynomialX, map_polynomialY, map_polynomialZ,
    eval_map, ← eval₂_comp, map_ne_zero_iff f hf]

中文:
引理 map_nonsingular
  条件: (hf : 函数.单射 f) (P : 有限集 3 -> R)
  证明: by
  simp only [Nonsingular, W'.map_equation hf, map_polynomialX, map_polynomialY, map_polynomialZ,
    eval_map, ← eval₂_comp, map_ne_zero_iff f hf]

Depends on / 依赖: Nonsingular, eval_map, map_equation, map_ne_zero_iff, map_polynomialX, map_polynomialY, map_polynomialZ
-/
lemma map_nonsingular (hf : Function.Injective f) (P : Fin 3 -> R) :
    (W'.map f).Nonsingular (f ∘ P) ↔ W'.Nonsingular P := by
  simp only [Nonsingular, W'.map_equation hf, map_polynomialX, map_polynomialY, map_polynomialZ,
    eval_map, ← eval₂_comp, map_ne_zero_iff f hf]

variable [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A] [Algebra R B] [Algebra S B]
  [IsScalarTower R S B] (f : A ->ₐ[S] B)

/--
lemma `map_baseChange` / 引理 `map_baseChange`

English:
lemma map_baseChange
  statement: (W'⁄A).map f = W'⁄B
  proof: WeierstrassCurve.map_baseChange W' f

中文:
引理 map_baseChange
  结论: (W'⁄A).map f = W'⁄B
  证明: WeierstrassCurve.map_baseChange W' f

Depends on / 依赖: WeierstrassCurve, WeierstrassCurve.map_baseChange, map_baseChange
-/
lemma map_baseChange : (W'⁄A).map f = W'⁄B :=
  WeierstrassCurve.map_baseChange W' f

/--
lemma `baseChange_polynomial` / 引理 `baseChange_polynomial`

English:
lemma baseChange_polynomial
  statement: (W'⁄B).polynomial = .map f (W'⁄A).polynomial
  proof: by
  rw [← map_polynomial]; rw [map_baseChange]

中文:
引理 baseChange_polynomial
  结论: (W'⁄B).polynomial = .map f (W'⁄A).polynomial
  证明: by
  rw [← map_polynomial]; rw [map_baseChange]

Depends on / 依赖: map_baseChange, map_polynomial
-/
lemma baseChange_polynomial : (W'⁄B).polynomial = .map f (W'⁄A).polynomial := by
  rw [← map_polynomial]; rw [map_baseChange]

variable {W'} in
/--
lemma `Equation.baseChange` / 引理 `Equation.baseChange`

English:
lemma Equation.baseChange
  given: {P : Fin 3 -> A} (h : (W'⁄A).Equation P)
  statement: (W'⁄B).Equation (f ∘ P)
  proof: by
  convert! Equation.map f.toRingHom h using 1
  rw [AlgHom.toRingHom_eq_coe]; rw [map_baseChange]

中文:
引理 方程.baseChange
  条件: {P : 有限集 3 -> A} (h : (W'⁄A).方程 P)
  结论: (W'⁄B).方程 (f ∘ P)
  证明: by
  convert! Equation.map f.toRingHom h using 1
  rw [AlgHom.toRingHom_eq_coe]; rw [map_baseChange]
-/
lemma Equation.baseChange {P : Fin 3 -> A} (h : (W'⁄A).Equation P) : (W'⁄B).Equation (f ∘ P) := by
  convert! Equation.map f.toRingHom h using 1
  rw [AlgHom.toRingHom_eq_coe]; rw [map_baseChange]

variable {f} in
/--
lemma `baseChange_equation` / 引理 `baseChange_equation`

English:
lemma baseChange_equation
  given: (hf : Function.Injective f) (P : Fin 3 -> A)
  proof: by
  rw [← RingHom.coe_coe]; rw [← map_equation _ hf]; rw [AlgHom.toRingHom_eq_coe]; rw [map_baseChange]

中文:
引理 baseChange_equation
  条件: (hf : 函数.单射 f) (P : 有限集 3 -> A)
  证明: by
  rw [← RingHom.coe_coe]; rw [← map_equation _ hf]; rw [AlgHom.toRingHom_eq_coe]; rw [map_baseChange]

Depends on / 依赖: AlgHom, AlgHom.toRingHom_eq_coe, RingHom, RingHom.coe_coe, coe_coe, map_baseChange, map_equation, toRingHom_eq_coe
-/
lemma baseChange_equation (hf : Function.Injective f) (P : Fin 3 -> A) :
    (W'⁄B).Equation (f ∘ P) ↔ (W'⁄A).Equation P := by
  rw [← RingHom.coe_coe]; rw [← map_equation _ hf]; rw [AlgHom.toRingHom_eq_coe]; rw [map_baseChange]

/--
lemma `baseChange_polynomialX` / 引理 `baseChange_polynomialX`

English:
lemma baseChange_polynomialX
  statement: (W'⁄B).polynomialX = .map f (W'⁄A).polynomialX
  proof: by
  rw [← map_polynomialX]; rw [map_baseChange]

中文:
引理 baseChange_polynomialX
  结论: (W'⁄B).polynomialX = .map f (W'⁄A).polynomialX
  证明: by
  rw [← map_polynomialX]; rw [map_baseChange]

Depends on / 依赖: map_baseChange, map_polynomialX
-/
lemma baseChange_polynomialX : (W'⁄B).polynomialX = .map f (W'⁄A).polynomialX := by
  rw [← map_polynomialX]; rw [map_baseChange]

/--
lemma `baseChange_polynomialY` / 引理 `baseChange_polynomialY`

English:
lemma baseChange_polynomialY
  statement: (W'⁄B).polynomialY = .map f (W'⁄A).polynomialY
  proof: by
  rw [← map_polynomialY]; rw [map_baseChange]

中文:
引理 baseChange_polynomialY
  结论: (W'⁄B).polynomialY = .map f (W'⁄A).polynomialY
  证明: by
  rw [← map_polynomialY]; rw [map_baseChange]

Depends on / 依赖: map_baseChange, map_polynomialY
-/
lemma baseChange_polynomialY : (W'⁄B).polynomialY = .map f (W'⁄A).polynomialY := by
  rw [← map_polynomialY]; rw [map_baseChange]

/--
lemma `baseChange_polynomialZ` / 引理 `baseChange_polynomialZ`

English:
lemma baseChange_polynomialZ
  statement: (W'⁄B).polynomialZ = .map f (W'⁄A).polynomialZ
  proof: by
  rw [← map_polynomialZ]; rw [map_baseChange]

中文:
引理 baseChange_polynomialZ
  结论: (W'⁄B).polynomialZ = .map f (W'⁄A).polynomialZ
  证明: by
  rw [← map_polynomialZ]; rw [map_baseChange]

Depends on / 依赖: map_baseChange, map_polynomialZ
-/
lemma baseChange_polynomialZ : (W'⁄B).polynomialZ = .map f (W'⁄A).polynomialZ := by
  rw [← map_polynomialZ]; rw [map_baseChange]

variable {f} in
/--
lemma `baseChange_nonsingular` / 引理 `baseChange_nonsingular`

English:
lemma baseChange_nonsingular
  given: (hf : Function.Injective f) (P : Fin 3 -> A)
  proof: by
  rw [← RingHom.coe_coe]; rw [← map_nonsingular _ hf]; rw [AlgHom.toRingHom_eq_coe]; rw [map_baseChange]

中文:
引理 baseChange_nonsingular
  条件: (hf : 函数.单射 f) (P : 有限集 3 -> A)
  证明: by
  rw [← RingHom.coe_coe]; rw [← map_nonsingular _ hf]; rw [AlgHom.toRingHom_eq_coe]; rw [map_baseChange]

Depends on / 依赖: AlgHom, AlgHom.toRingHom_eq_coe, RingHom, RingHom.coe_coe, coe_coe, map_baseChange, map_nonsingular, toRingHom_eq_coe
-/
lemma baseChange_nonsingular (hf : Function.Injective f) (P : Fin 3 -> A) :
    (W'⁄B).Nonsingular (f ∘ P) ↔ (W'⁄A).Nonsingular P := by
  rw [← RingHom.coe_coe]; rw [← map_nonsingular _ hf]; rw [AlgHom.toRingHom_eq_coe]; rw [map_baseChange]

end Projective

end WeierstrassCurve
