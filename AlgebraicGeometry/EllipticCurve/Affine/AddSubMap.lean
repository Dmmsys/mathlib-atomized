/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Tactic.Ring.NamePolyVars

/-!
# The addition-and-subtraction map on x-coordinates

We set up the endomorphism of `ℙ²` that on affine points with affine sum is equal to

`(x(P) * x(Q) : x(P) + x(Q) : 1) ↦ (x(P+Q) * x(P-Q) : x(P+Q) + x(P-Q) : 1);`

see `WeierstrassCurve.addSubMap` (this is on coordinate vectors).

TODO: Show that the map really does what it is claimed to do.

This will be used to eventually show the approximate parallelogram law for `K`-points
on an elliptic curve `E`:
`∃ C, ∀ P Q : E(K), |h(P+Q) + h(P-Q) - 2*h(P) - 2*h(Q)| ≤ C`,
where `K` is a field with a height and `h` denotes the (logarithmic) naïve height on `E(K)`.
-/

public section

namespace WeierstrassCurve

/-!
### The addition-and-subtraction map on x-coordinates
-/

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

open MvPolynomial

name_poly_vars s, t, u over R

/--
Definition of `addSubMap` / `addSubMap` 的定义

English:
definition addSubMap
  signature: : Fin 3 -> MvPolynomial (Fin 3) R
  body: ![s ^ 2 - C W.b₄ * s * u - C W.b₆ * t * u - C W.b₈ * u ^ 2,
    C 2 * t * s + C W.b₂ * s * u + C W.b₄ * t * u + C W.b₆ * u ^ 2,
    t ^ 2 - C 4 * s * u]

中文:
定义 addSubMap
  签名: : Fin 3 -> MvPolynomial (Fin 3) R
  定义体: ![s ^ 2 - C W.b₄ * s * u - C W.b₆ * t * u - C W.b₈ * u ^ 2,
    C 2 * t * s + C W.b₂ * s * u + C W.b₄ * t * u + C W.b₆ * u ^ 2,
    t ^ 2 - C 4 * s * u]
-/
@[expose] noncomputable def addSubMap : Fin 3 -> MvPolynomial (Fin 3) R :=
  ![s ^ 2 - C W.b₄ * s * u - C W.b₆ * t * u - C W.b₈ * u ^ 2,
    C 2 * t * s + C W.b₂ * s * u + C W.b₄ * t * u + C W.b₆ * u ^ 2,
    t ^ 2 - C 4 * s * u]

/--
Definition of `addSubMapCoeff` / `addSubMapCoeff` 的定义

English:
definition addSubMapCoeff
  signature: : Fin 3 × Fin 3 -> MvPolynomial (Fin 3) R
  body: ![![C (-W.b₂ ^ 2 * W.b₈ + 9 * W.b₂ * W.b₄ * W.b₆ - 8 * W.b₄ ^ 3 - 27 * W.b₆ ^ 2) * s ^ 2 +
        C (2 * W.b₂ * W.b₄ * W.b₈ - 2 * W.b₄ ^ 2 * W.b₆ - 10 * W.b₆ * W.b₈) * s * t +
        C (-W.b₂ * W.b₆ * W.b₈ + W.b₄ * W.b₆ ^ 2) * s * u +
        C (3 * W.b₄ ^ 2 * W.b₈ - 3 * W.b₄ * W.b₆ ^ 2) * t ^ 2 +

中文:
定义 addSubMapCoeff
  签名: : Fin 3 × Fin 3 -> MvPolynomial (Fin 3) R
  定义体: ![![C (-W.b₂ ^ 2 * W.b₈ + 9 * W.b₂ * W.b₄ * W.b₆ - 8 * W.b₄ ^ 3 - 27 * W.b₆ ^ 2) * s ^ 2 +
        C (2 * W.b₂ * W.b₄ * W.b₈ - 2 * W.b₄ ^ 2 * W.b₆ - 10 * W.b₆ * W.b₈) * s * t +
        C (-W.b₂ * W.b₆ * W.b₈ + W.b₄ * W.b₆ ^ 2) * s * u +
        C (3 * W.b₄ ^ 2 * W.b₈ - 3 * W.b₄ * W.b₆ ^ 2) * t ^ 2 +
-/
noncomputable def addSubMapCoeff : Fin 3 × Fin 3 -> MvPolynomial (Fin 3) R :=
  ![![C (-W.b₂ ^ 2 * W.b₈ + 9 * W.b₂ * W.b₄ * W.b₆ - 8 * W.b₄ ^ 3 - 27 * W.b₆ ^ 2) * s ^ 2 +
        C (2 * W.b₂ * W.b₄ * W.b₈ - 2 * W.b₄ ^ 2 * W.b₆ - 10 * W.b₆ * W.b₈) * s * t +
        C (-W.b₂ * W.b₆ * W.b₈ + W.b₄ * W.b₆ ^ 2) * s * u +
        C (3 * W.b₄ ^ 2 * W.b₈ - 3 * W.b₄ * W.b₆ ^ 2) * t ^ 2 +
        C (3 * W.b₄ * W.b₆ * W.b₈ - 3 * W.b₆ ^ 3) * t * u,
      C (-W.b₂ * W.b₄ * W.b₈ + W.b₄ ^ 2 * W.b₆ + 5 * W.b₆ * W.b₈) * s ^ 2 +
        C (2 * W.b₂ * W.b₆ * W.b₈ - 2 * W.b₄ * W.b₆ ^ 2 - 10 * W.b₈ ^ 2) * s * t +
        C (-W.b₂ * W.b₈ ^ 2 + W.b₄ * W.b₆ * W.b₈) * s * u +
        C (3 * W.b₄ * W.b₆ * W.b₈ - 3 * W.b₆ ^ 3) * t ^ 2 +
        C (3 * W.b₄ * W.b₈ ^ 2 - 3 * W.b₆ ^ 2 * W.b₈) * t * u,
      C (W.b₂ * W.b₆ * W.b₈ - 8 * W.b₄ ^ 2 * W.b₈ + 7 * W.b₄ * W.b₆ ^ 2) * s ^ 2 +
        C (-6 * W.b₄ * W.b₆ * W.b₈ + 6 * W.b₆ ^ 3) * s * t +
        C (-8 * W.b₄ * W.b₈ ^ 2 + 8 * W.b₆ ^ 2 * W.b₈) * s * u],
    ![C (96 * W.b₆) * s * t + C (12 * W.b₂ * W.b₆ - 64 * W.b₈) * t ^ 2 +
        C (16 * W.b₄ * W.b₆) * t * u,
      C (-48 * W.b₆) * s ^ 2 + C (32 * W.b₈) * s * t +
        C (-4 * W.b₂ * W.b₈ + 16 * W.b₄ * W.b₆) * t ^ 2 + C (16 * W.b₄ * W.b₈) * t * u,
      C (-12 * W.b₂ * W.b₆) * s ^ 2 + C (8 * W.b₂ * W.b₈ - 32 * W.b₄ * W.b₆) * s * t +
        C (-12 * W.b₆ ^ 2) * s * u +
        C (-W.b₂ ^ 2 * W.b₈ + 9 * W.b₂ * W.b₄ * W.b₆ - 8 * W.b₄ ^ 3 - 27 * W.b₆ ^ 2) * t ^ 2 +
        C (4 * W.b₂ * W.b₄ * W.b₈ - 4 * W.b₂ * W.b₆ ^ 2) * t * u],
    ![C (-12) * t ^ 2 + C (-4 * W.b₂) * t * u + C (W.b₂ ^ 2 - 32 * W.b₄) * u ^ 2,
      C 6 * s * t + C (-W.b₂) * s * u + C (-5 * W.b₄) * t * u + C (W.b₂ * W.b₄ - 27 * W.b₆) * u ^ 2,
      C (-8 * W.b₄) * s * u + C (-12 * W.b₆) * t * u + C (W.b₄ ^ 2 - 28 * W.b₈) * u ^ 2]].uncurry

/--
lemma `CXX` / 引理 `CXX`

English:
lemma CXX
  given: {i : Fin 3} {a : R}
  statement: (C a * X (R := R) i ^ 2).IsHomogeneous 2
  proof: isHomogeneous_C_mul_X_pow ..

中文:
引理 CXX
  条件: {i : Fin 3} {a : R}
  结论: (C a * X (R := R) i ^ 2).IsHomogeneous 2
  证明: isHomogeneous_C_mul_X_pow ..

Depends on / 依赖: Hom.fiberToSpecResidueField, fiberToSpecResidueField, infer_instance
-/
private lemma CXX {i : Fin 3} {a : R} : (C a * X (R := R) i ^ 2).IsHomogeneous 2 :=
  isHomogeneous_C_mul_X_pow ..

/--
lemma `CXY` / 引理 `CXY`

English:
lemma CXY
  given: {i j : Fin 3} {a : R}
  statement: (C a * X (R := R) i * X j).IsHomogeneous 2
  proof: .mul (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)

中文:
引理 CXY
  条件: {i j : Fin 3} {a : R}
  结论: (C a * X (R := R) i * X j).IsHomogeneous 2
  证明: .mul (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)
-/
private lemma CXY {i j : Fin 3} {a : R} : (C a * X (R := R) i * X j).IsHomogeneous 2 :=
  .mul (isHomogeneous_C_mul_X ..) (isHomogeneous_X ..)

/--
lemma `isHomogeneous_addSubMap` / 引理 `isHomogeneous_addSubMap`

English:
lemma isHomogeneous_addSubMap
  given: (i : Fin 3)
  statement: (addSubMap W i).IsHomogeneous 2
  proof: by
  simp only [addSubMap]
  fin_cases i <;>
    simp only [Fin.isValue, Fin.mk_one, Fin.zero_eta, Fin.reduceFinMk, Matrix.cons_val,
      Matrix.cons_val_one, Matrix.cons_val_zero]
.sub CXX .sub CXY .sub CXY · exact isHomogeneous_X_pow ..
.add CXX .add CXY · exact CXY.add CXY
.sub CXY · exact isHom

中文:
引理 isHomogeneous_addSubMap
  条件: (i : Fin 3)
  结论: (addSubMap W i).IsHomogeneous 2
  证明: by
  simp only [addSubMap]
  fin_cases i <;>
    simp only [Fin.isValue, Fin.mk_one, Fin.zero_eta, Fin.reduceFinMk, Matrix.cons_val,
      Matrix.cons_val_one, Matrix.cons_val_zero]
.sub CXX .sub CXY .sub CXY · exact isHomogeneous_X_pow ..
.add CXX .add CXY · exact CXY.add CXY
.sub CXY · exact isHom

Depends on / 依赖: CXY.add, Fin.isValue, Fin.mk_one, Fin.reduceFinMk, Fin.zero_eta, Matrix, Matrix.cons_val, Matrix.cons_val_one, Matrix.cons_val_zero, addSubMap, cons_val, cons_val_one, cons_val_zero, fin_cases, isHomogeneous_X_pow, isValue, mk_one, reduceFinMk, zero_eta
-/
lemma isHomogeneous_addSubMap (i : Fin 3) : (addSubMap W i).IsHomogeneous 2 := by
  simp only [addSubMap]
  fin_cases i <;>
    simp only [Fin.isValue, Fin.mk_one, Fin.zero_eta, Fin.reduceFinMk, Matrix.cons_val,
      Matrix.cons_val_one, Matrix.cons_val_zero]
.sub CXX .sub CXY .sub CXY · exact isHomogeneous_X_pow ..
.add CXX .add CXY · exact CXY.add CXY
.sub CXY · exact isHomogeneous_X_pow ..

/--
lemma `isHomogeneous_addSubMapCoeff` / 引理 `isHomogeneous_addSubMapCoeff`

English:
lemma isHomogeneous_addSubMapCoeff
  given: (ij : Fin 3 × Fin 3)
  proof: by
  simp only [addSubMapCoeff]
  fin_cases ij <;>
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Function.uncurry_apply_pair,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, neg_mul, Fin.mk_one,
      Matrix.cons_val_one, Fin.reduceFinMk, Matrix.cons_val, Fin

中文:
引理 isHomogeneous_addSubMapCoeff
  条件: (ij : Fin 3 × Fin 3)
  证明: by
  simp only [addSubMapCoeff]
  fin_cases ij <;>
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Function.uncurry_apply_pair,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, neg_mul, Fin.mk_one,
      Matrix.cons_val_one, Fin.reduceFinMk, Matrix.cons_val, Fin

Depends on / 依赖: Fin.isValue, Fin.mk_one, Fin.reduceFinMk, Fin.zero_eta, Function, Function.uncurry_apply_pair, Matrix, Matrix.cons_val, Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.cons_val_zero, Nat.reduceAdd, Nat.succ_eq_add_one, addSubMapCoeff, cons_val, cons_val_fin_one, cons_val_one, cons_val_zero, fin_cases, isValue
-/
lemma isHomogeneous_addSubMapCoeff (ij : Fin 3 × Fin 3) :
    (addSubMapCoeff W ij).IsHomogeneous 2 := by
  simp only [addSubMapCoeff]
  fin_cases ij <;>
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Function.uncurry_apply_pair,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, neg_mul, Fin.mk_one,
      Matrix.cons_val_one, Fin.reduceFinMk, Matrix.cons_val, Fin.zero_eta]
    -- The following works, but is slow (44894 vs. 11717 heartbeats):
    -- <;> repeat first | refine .add ?_ CXY | refine .add ?_ CXX | exact CXX | exact CXY
.add CXY .add CXX .add CXY · exact CXX.add CXY
.add CXY .add CXX .add CXY · exact CXX.add CXY
.add CXY · exact CXX.add CXY
.add CXY · exact CXY.add CXX
.add CXY .add CXX · exact CXX.add CXY
.add CXY .add CXX .add CXY · exact CXX.add CXY
.add CXX · exact CXX.add CXY
.add CXX .add CXY · exact CXY.add CXY
.add CXX · exact CXY.add CXY

variable [W.IsElliptic]

/--
lemma `addSubMapCoeff_condition` / 引理 `addSubMapCoeff_condition`

English:
lemma addSubMapCoeff_condition
  given: (x : Fin 3 -> R) (i : Fin 3)
  proof: by
  simp only [eval_mul, eval_C, mul_assoc]
  rw [← Finset.mul_sum]; rw [Units.inv_mul_eq_iff_eq_mul]; rw [Fin.sum_univ_three]; rw [addSubMap]; rw [addSubMapCoeff]; rw [Function.uncurry_apply_pair]; rw [coe_Δ']; rw [Δ]
  fin_cases i <;> simp <;> grind only [b_relation]

中文:
引理 addSubMapCoeff_condition
  条件: (x : Fin 3 -> R) (i : Fin 3)
  证明: by
  simp only [eval_mul, eval_C, mul_assoc]
  rw [← Finset.mul_sum]; rw [Units.inv_mul_eq_iff_eq_mul]; rw [Fin.sum_univ_three]; rw [addSubMap]; rw [addSubMapCoeff]; rw [Function.uncurry_apply_pair]; rw [coe_Δ']; rw [Δ]
  fin_cases i <;> simp <;> grind only [b_relation]

Depends on / 依赖: Fin.sum_univ_three, Finset, Finset.mul_sum, Function, Function.uncurry_apply_pair, Units.inv_mul_eq_iff_eq_mul, addSubMap, addSubMapCoeff, b_relation, eval_C, eval_mul, fin_cases, inv_mul_eq_iff_eq_mul, mul_assoc, mul_sum, sum_univ_three, uncurry_apply_pair
-/
lemma addSubMapCoeff_condition (x : Fin 3 -> R) (i : Fin 3) :
    ∑ j : Fin 3, (C (↑W.Δ'⁻¹ : R) * addSubMapCoeff W (i, j)).eval x *
      (addSubMap W j).eval x = x i ^ 4 := by
  simp only [eval_mul, eval_C, mul_assoc]
  rw [← Finset.mul_sum]; rw [Units.inv_mul_eq_iff_eq_mul]; rw [Fin.sum_univ_three]; rw [addSubMap]; rw [addSubMapCoeff]; rw [Function.uncurry_apply_pair]; rw [coe_Δ']; rw [Δ]
  fin_cases i <;> simp <;> grind only [b_relation]

/--
lemma `addSubMap_ne_zero` / 引理 `addSubMap_ne_zero`

English:
lemma addSubMap_ne_zero
  given: [IsReduced R] {x : Fin 3 -> R} (hx : x != 0)
  proof: by
  contrapose! hx
  ext i
  simpa [congrFun hx] using (addSubMapCoeff_condition W x i).symm

中文:
引理 addSubMap_ne_zero
  条件: [IsReduced R] {x : Fin 3 -> R} (hx : x != 0)
  证明: by
  contrapose! hx
  ext i
  simpa [congrFun hx] using (addSubMapCoeff_condition W x i).symm

Depends on / 依赖: addSubMapCoeff_condition, contrapose
-/
lemma addSubMap_ne_zero [IsReduced R] {x : Fin 3 -> R} (hx : x != 0) :
    (fun i => (addSubMap W i).eval x) != 0 := by
  contrapose! hx
  ext i
  simpa [congrFun hx] using (addSubMapCoeff_condition W x i).symm

end WeierstrassCurve

/-!
### The symmetric square of the x-coordinate map

We define `Weierstrass.Affine.Point.sym2x`, which sends a pair `P`, `Q` of nonsingular points in
affine coordinates on a Weierstrass curve to a triple projectively equal to
`(x(P)*x(Q), x(P)+x(Q), 1)`, and provide some API.
-/

namespace WeierstrassCurve.Affine.Point

variable {R : Type*} [CommRing R] {W' : Affine R}

/--
Definition of `sym2x` / `sym2x` 的定义

English:
definition sym2x
  signature: (P Q : W'.Point)
  body: letI Px := P.xRep
  letI Qx := Q.xRep
  ![Px 0 * Qx 0, Px 0 * Qx 1 + Px 1 * Qx 0, Px 1 * Qx 1]

@[simp]

中文:
定义 sym2x
  签名: (P Q : W'.Point)
  定义体: letI Px := P.xRep
  letI Qx := Q.xRep
  ![Px 0 * Qx 0, Px 0 * Qx 1 + Px 1 * Qx 0, Px 1 * Qx 1]

@[simp]

Depends on / 依赖: P.xRep, Q.xRep
-/
noncomputable def sym2x (P Q : W'.Point) : Fin 3 -> R :=
  letI Px := P.xRep
  letI Qx := Q.xRep
  ![Px 0 * Qx 0, Px 0 * Qx 1 + Px 1 * Qx 0, Px 1 * Qx 1]

@[simp]
/--
lemma `sym2x_zero_zero` / 引理 `sym2x_zero_zero`

English:
lemma sym2x_zero_zero
  statement: (0 : W'.Point).sym2x 0 = ![1, 0, 0]
  proof: by
  simp [sym2x]

@[simp]

中文:
引理 sym2x_zero_zero
  结论: (0 : W'.Point).sym2x 0 = ![1, 0, 0]
  证明: by
  simp [sym2x]

@[simp]
-/
lemma sym2x_zero_zero : (0 : W'.Point).sym2x 0 = ![1, 0, 0] := by
  simp [sym2x]

@[simp]
/--
lemma `sym2x_zero_some` / 引理 `sym2x_zero_some`

English:
lemma sym2x_zero_some
  given: {x y : R} (h : W'.Nonsingular x y)
  proof: by
  simp [sym2x]

@[simp]

中文:
引理 sym2x_zero_some
  条件: {x y : R} (h : W'.Nonsingular x y)
  证明: by
  simp [sym2x]

@[simp]
-/
lemma sym2x_zero_some {x y : R} (h : W'.Nonsingular x y) :
    (0 : W'.Point).sym2x (some x y h) = ![x, 1, 0] := by
  simp [sym2x]

@[simp]
/--
lemma `sym2x_some_zero` / 引理 `sym2x_some_zero`

English:
lemma sym2x_some_zero
  given: {x y : R} (h : W'.Nonsingular x y)
  proof: by
  simp [sym2x]

@[simp]

中文:
引理 sym2x_some_zero
  条件: {x y : R} (h : W'.Nonsingular x y)
  证明: by
  simp [sym2x]

@[simp]
-/
lemma sym2x_some_zero {x y : R} (h : W'.Nonsingular x y) :
    (some x y h).sym2x 0 = ![x, 1, 0] := by
  simp [sym2x]

@[simp]
/--
lemma `sym2x_some_some` / 引理 `sym2x_some_some`

English:
lemma sym2x_some_some
  given: {x y x' y' : R} (h : W'.Nonsingular x y) (h' : W'.Nonsingular x' y')
  proof: by
  simp [sym2x]

中文:
引理 sym2x_some_some
  条件: {x y x' y' : R} (h : W'.Nonsingular x y) (h' : W'.Nonsingular x' y')
  证明: by
  simp [sym2x]
-/
lemma sym2x_some_some {x y x' y' : R} (h : W'.Nonsingular x y) (h' : W'.Nonsingular x' y') :
    (some x y h).sym2x (some x' y' h') = ![x * x', x + x', 1] := by
  simp [sym2x]

/--
lemma `sym2x_ne_zero` / 引理 `sym2x_ne_zero`

English:
lemma sym2x_ne_zero
  given: [Nontrivial R] (P Q : W'.Point)
  statement: P.sym2x Q != 0
  proof: by
  cases P <;> cases Q <;> simp [sym2x, xRep]

中文:
引理 sym2x_ne_zero
  条件: [Nontrivial R] (P Q : W'.Point)
  结论: P.sym2x Q != 0
  证明: by
  cases P <;> cases Q <;> simp [sym2x, xRep]
-/
lemma sym2x_ne_zero [Nontrivial R] (P Q : W'.Point) : P.sym2x Q != 0 := by
  cases P <;> cases Q <;> simp [sym2x, xRep]

/--
lemma `sym2x_comm` / 引理 `sym2x_comm`

English:
lemma sym2x_comm
  given: (P Q : W'.Point)
  statement: P.sym2x Q = Q.sym2x P
  proof: by
  cases P <;> cases Q <;> simp [← zero_def, mul_comm, add_comm]

中文:
引理 sym2x_comm
  条件: (P Q : W'.Point)
  结论: P.sym2x Q = Q.sym2x P
  证明: by
  cases P <;> cases Q <;> simp [← zero_def, mul_comm, add_comm]

Depends on / 依赖: add_comm, mul_comm, zero_def
-/
lemma sym2x_comm (P Q : W'.Point) : P.sym2x Q = Q.sym2x P := by
  cases P <;> cases Q <;> simp [← zero_def, mul_comm, add_comm]

/--
lemma `sym2x_neg_left` / 引理 `sym2x_neg_left`

English:
lemma sym2x_neg_left
  given: (P Q : W'.Point)
  statement: (-P).sym2x Q = P.sym2x Q
  proof: by
  simp [sym2x]

中文:
引理 sym2x_neg_left
  条件: (P Q : W'.Point)
  结论: (-P).sym2x Q = P.sym2x Q
  证明: by
  simp [sym2x]
-/
lemma sym2x_neg_left (P Q : W'.Point) : (-P).sym2x Q = P.sym2x Q := by
  simp [sym2x]

/--
lemma `sym2x_neg_right` / 引理 `sym2x_neg_right`

English:
lemma sym2x_neg_right
  given: (P Q : W'.Point)
  statement: P.sym2x (-Q) = P.sym2x Q
  proof: by
  simp [sym2x]

中文:
引理 sym2x_neg_right
  条件: (P Q : W'.Point)
  结论: P.sym2x (-Q) = P.sym2x Q
  证明: by
  simp [sym2x]
-/
lemma sym2x_neg_right (P Q : W'.Point) : P.sym2x (-Q) = P.sym2x Q := by
  simp [sym2x]

end WeierstrassCurve.Affine.Point

end
