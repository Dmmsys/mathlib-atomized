/-
Copyright (c) 2022 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
module

public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Tactic.IntervalCases

/-!
# Cubics and discriminants

This file defines cubic polynomials over a semiring and their discriminants over a splitting field.

## Main definitions

* `Cubic`: the structure representing a cubic polynomial.
* `Cubic.discr`: the discriminant of a cubic polynomial.

## Main statements

* `Cubic.discr_ne_zero_iff_roots_nodup`: the cubic discriminant is not equal to zero if and only if
  the cubic has no duplicate roots.

## References

* https://en.wikipedia.org/wiki/Cubic_equation
* https://en.wikipedia.org/wiki/Discriminant

## Tags

cubic, discriminant, polynomial, root
-/

@[expose] public section


noncomputable section

/-- The structure representing a cubic polynomial. -/
@[ext]
/--
Definition of `Cubic` / `Cubic` 的定义

English:
structure Cubic
  parameters: (R : Type*)
  axioms and operations (4):
    - a : R
    - b : R
    - c : R
    - d : R

中文:
结构 Cubic
  参数: (R : 类型)
  公理与运算 (4 个):
    - a : R
    - b : R
    - c : R
    - d : R
-/
structure Cubic (R : Type*) where
  /-- The degree-3 coefficient -/
  a : R
  /-- The degree-2 coefficient -/
  b : R
  /-- The degree-1 coefficient -/
  c : R
  /-- The degree-0 coefficient -/
  d : R

namespace Cubic

open Polynomial

variable {R S F K : Type*}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: R] : Inhabited (Cubic R)
  body: ⟨⟨default, default, default, default⟩⟩

中文:
实例 [Inhabited
  签名: R] : Inhabited (Cubic R)
  定义体: ⟨⟨default, default, default, default⟩⟩
-/
instance [Inhabited R] : Inhabited (Cubic R) :=
  ⟨⟨default, default, default, default⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Zero
  signature: R] : Zero (Cubic R)
  body: ⟨⟨0, 0, 0, 0⟩⟩

中文:
实例 [Zero
  签名: R] : Zero (Cubic R)
  定义体: ⟨⟨0, 0, 0, 0⟩⟩
-/
instance [Zero R] : Zero (Cubic R) :=
  ⟨⟨0, 0, 0, 0⟩⟩

section Basic

variable {P Q : Cubic R} {a b c d a' b' c' d' : R} [Semiring R]

/--
Definition of `toPoly` / `toPoly` 的定义

English:
definition toPoly
  signature: (P : Cubic R)
  body: C P.a * X ^ 3 + C P.b * X ^ 2 + C P.c * X + C P.d

中文:
定义 toPoly
  签名: (P : Cubic R)
  定义体: C P.a * X ^ 3 + C P.b * X ^ 2 + C P.c * X + C P.d
-/
def toPoly (P : Cubic R) : R[X] :=
  C P.a * X ^ 3 + C P.b * X ^ 2 + C P.c * X + C P.d

/--
theorem `C_mul_prod_X_sub_C_eq` / 定理 `C_mul_prod_X_sub_C_eq`

English:
theorem C_mul_prod_X_sub_C_eq
  given: [CommRing S] {w x y z : S}
  proof: by
  simp only [toPoly, C_neg, C_add, C_mul]
  ring1

中文:
定理 C_mul_prod_X_sub_C_eq
  条件: [CommRing S] {w x y z : S}
  证明: by
  simp only [toPoly, C_neg, C_add, C_mul]
  ring1

Depends on / 依赖: C_add, C_mul, C_neg, toPoly
-/
theorem C_mul_prod_X_sub_C_eq [CommRing S] {w x y z : S} :
    C w * (X - C x) * (X - C y) * (X - C z) =
      toPoly ⟨w, w * -(x + y + z), w * (x * y + x * z + y * z), w * -(x * y * z)⟩ := by
  simp only [toPoly, C_neg, C_add, C_mul]
  ring1

/--
theorem `prod_X_sub_C_eq` / 定理 `prod_X_sub_C_eq`

English:
theorem prod_X_sub_C_eq
  given: [CommRing S] {x y z : S}
  proof: by
  rw [← one_mul <| X - C x]; rw [← C_1]; rw [C_mul_prod_X_sub_C_eq]; rw [one_mul]; rw [one_mul]; rw [one_mul]

中文:
定理 prod_X_sub_C_eq
  条件: [CommRing S] {x y z : S}
  证明: by
  rw [← one_mul <| X - C x]; rw [← C_1]; rw [C_mul_prod_X_sub_C_eq]; rw [one_mul]; rw [one_mul]; rw [one_mul]

Depends on / 依赖: C_mul_prod_X_sub_C_eq, one_mul
-/
theorem prod_X_sub_C_eq [CommRing S] {x y z : S} :
    (X - C x) * (X - C y) * (X - C z) =
      toPoly ⟨1, -(x + y + z), x * y + x * z + y * z, -(x * y * z)⟩ := by
  rw [← one_mul <| X - C x]; rw [← C_1]; rw [C_mul_prod_X_sub_C_eq]; rw [one_mul]; rw [one_mul]; rw [one_mul]

/-! ### Coefficients -/


section Coeff

/--
theorem `coeffs` / 定理 `coeffs`

English:
theorem coeffs
  statement: (forall n > 3, P.toPoly.coeff n = 0) ∧ P.toPoly.coeff 3 = P.a ∧
  proof: by
  simp only [Cubic.toPoly, Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul_X,
    Polynomial.coeff_C_mul_X_pow]
  grind [zero_add]

@[simp]

中文:
定理 coeffs
  结论: (对任意 n > 3, P.toPoly.coeff n = 0) ∧ P.toPoly.coeff 3 = P.a ∧
  证明: by
  simp only [Cubic.toPoly, Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul_X,
    Polynomial.coeff_C_mul_X_pow]
  grind [zero_add]

@[simp]
-/
private theorem coeffs : (forall n > 3, P.toPoly.coeff n = 0) ∧ P.toPoly.coeff 3 = P.a ∧
    P.toPoly.coeff 2 = P.b ∧ P.toPoly.coeff 1 = P.c ∧ P.toPoly.coeff 0 = P.d := by
  simp only [Cubic.toPoly, Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul_X,
    Polynomial.coeff_C_mul_X_pow]
  grind [zero_add]

@[simp]
/--
theorem `coeff_eq_zero` / 定理 `coeff_eq_zero`

English:
theorem coeff_eq_zero
  given: {n : Nat} (hn : 3 < n)
  statement: P.toPoly.coeff n = 0
  proof: coeffs.1 n hn

@[simp]

中文:
定理 coeff_eq_zero
  条件: {n : 自然数} (hn : 3 < n)
  结论: P.toPoly.coeff n = 0
  证明: coeffs.1 n hn

@[simp]

Depends on / 依赖: coeffs
-/
theorem coeff_eq_zero {n : Nat} (hn : 3 < n) : P.toPoly.coeff n = 0 :=
  coeffs.1 n hn

@[simp]
/--
theorem `coeff_eq_a` / 定理 `coeff_eq_a`

English:
theorem coeff_eq_a
  statement: P.toPoly.coeff 3 = P.a
  proof: coeffs.2.1

@[simp]

中文:
定理 coeff_eq_a
  结论: P.toPoly.coeff 3 = P.a
  证明: coeffs.2.1

@[simp]

Depends on / 依赖: coeffs
-/
theorem coeff_eq_a : P.toPoly.coeff 3 = P.a :=
  coeffs.2.1

@[simp]
/--
theorem `coeff_eq_b` / 定理 `coeff_eq_b`

English:
theorem coeff_eq_b
  statement: P.toPoly.coeff 2 = P.b
  proof: coeffs.2.2.1

@[simp]

中文:
定理 coeff_eq_b
  结论: P.toPoly.coeff 2 = P.b
  证明: coeffs.2.2.1

@[simp]

Depends on / 依赖: coeffs
-/
theorem coeff_eq_b : P.toPoly.coeff 2 = P.b :=
  coeffs.2.2.1

@[simp]
/--
theorem `coeff_eq_c` / 定理 `coeff_eq_c`

English:
theorem coeff_eq_c
  statement: P.toPoly.coeff 1 = P.c
  proof: coeffs.2.2.2.1

@[simp]

中文:
定理 coeff_eq_c
  结论: P.toPoly.coeff 1 = P.c
  证明: coeffs.2.2.2.1

@[simp]

Depends on / 依赖: coeffs
-/
theorem coeff_eq_c : P.toPoly.coeff 1 = P.c :=
  coeffs.2.2.2.1

@[simp]
/--
theorem `coeff_eq_d` / 定理 `coeff_eq_d`

English:
theorem coeff_eq_d
  statement: P.toPoly.coeff 0 = P.d
  proof: coeffs.2.2.2.2

中文:
定理 coeff_eq_d
  结论: P.toPoly.coeff 0 = P.d
  证明: coeffs.2.2.2.2

Depends on / 依赖: coeffs
-/
theorem coeff_eq_d : P.toPoly.coeff 0 = P.d :=
  coeffs.2.2.2.2

/--
theorem `a_of_eq` / 定理 `a_of_eq`

English:
theorem a_of_eq
  given: (h : P.toPoly = Q.toPoly)
  statement: P.a = Q.a
  proof: by rw [← coeff_eq_a, h, coeff_eq_a]

中文:
定理 a_of_eq
  条件: (h : P.toPoly = Q.toPoly)
  结论: P.a = Q.a
  证明: by rw [← coeff_eq_a, h, coeff_eq_a]

Depends on / 依赖: coeff_eq_a
-/
theorem a_of_eq (h : P.toPoly = Q.toPoly) : P.a = Q.a := by rw [← coeff_eq_a, h, coeff_eq_a]

/--
theorem `b_of_eq` / 定理 `b_of_eq`

English:
theorem b_of_eq
  given: (h : P.toPoly = Q.toPoly)
  statement: P.b = Q.b
  proof: by rw [← coeff_eq_b, h, coeff_eq_b]

中文:
定理 b_of_eq
  条件: (h : P.toPoly = Q.toPoly)
  结论: P.b = Q.b
  证明: by rw [← coeff_eq_b, h, coeff_eq_b]

Depends on / 依赖: coeff_eq_b
-/
theorem b_of_eq (h : P.toPoly = Q.toPoly) : P.b = Q.b := by rw [← coeff_eq_b, h, coeff_eq_b]

/--
theorem `c_of_eq` / 定理 `c_of_eq`

English:
theorem c_of_eq
  given: (h : P.toPoly = Q.toPoly)
  statement: P.c = Q.c
  proof: by rw [← coeff_eq_c, h, coeff_eq_c]

中文:
定理 c_of_eq
  条件: (h : P.toPoly = Q.toPoly)
  结论: P.c = Q.c
  证明: by rw [← coeff_eq_c, h, coeff_eq_c]

Depends on / 依赖: coeff_eq_c
-/
theorem c_of_eq (h : P.toPoly = Q.toPoly) : P.c = Q.c := by rw [← coeff_eq_c, h, coeff_eq_c]

/--
theorem `d_of_eq` / 定理 `d_of_eq`

English:
theorem d_of_eq
  given: (h : P.toPoly = Q.toPoly)
  statement: P.d = Q.d
  proof: by rw [← coeff_eq_d, h, coeff_eq_d]

中文:
定理 d_of_eq
  条件: (h : P.toPoly = Q.toPoly)
  结论: P.d = Q.d
  证明: by rw [← coeff_eq_d, h, coeff_eq_d]

Depends on / 依赖: coeff_eq_d
-/
theorem d_of_eq (h : P.toPoly = Q.toPoly) : P.d = Q.d := by rw [← coeff_eq_d, h, coeff_eq_d]

/--
theorem `toPoly_injective` / 定理 `toPoly_injective`

English:
theorem toPoly_injective
  given: (P Q : Cubic R)
  statement: P.toPoly = Q.toPoly ↔ P = Q
  proof: ⟨fun h => Cubic.ext (a_of_eq h) (b_of_eq h) (c_of_eq h) (d_of_eq h), congr_arg toPoly⟩

中文:
定理 toPoly_injective
  条件: (P Q : Cubic R)
  结论: P.toPoly = Q.toPoly ↔ P = Q
  证明: ⟨fun h => Cubic.ext (a_of_eq h) (b_of_eq h) (c_of_eq h) (d_of_eq h), congr_arg toPoly⟩

Depends on / 依赖: Cubic.ext, a_of_eq, b_of_eq, c_of_eq, congr_arg, d_of_eq, toPoly
-/
theorem toPoly_injective (P Q : Cubic R) : P.toPoly = Q.toPoly ↔ P = Q :=
  ⟨fun h => Cubic.ext (a_of_eq h) (b_of_eq h) (c_of_eq h) (d_of_eq h), congr_arg toPoly⟩

/--
theorem `of_a_eq_zero` / 定理 `of_a_eq_zero`

English:
theorem of_a_eq_zero
  given: (ha : P.a = 0)
  statement: P.toPoly = C P.b * X ^ 2 + C P.c * X + C P.d
  proof: by
  rw [toPoly]; rw [ha]; rw [C_0]; rw [zero_mul]; rw [zero_add]

中文:
定理 of_a_eq_zero
  条件: (ha : P.a = 0)
  结论: P.toPoly = C P.b * X ^ 2 + C P.c * X + C P.d
  证明: by
  rw [toPoly]; rw [ha]; rw [C_0]; rw [zero_mul]; rw [zero_add]

Depends on / 依赖: toPoly, zero_add, zero_mul
-/
theorem of_a_eq_zero (ha : P.a = 0) : P.toPoly = C P.b * X ^ 2 + C P.c * X + C P.d := by
  rw [toPoly]; rw [ha]; rw [C_0]; rw [zero_mul]; rw [zero_add]

/--
theorem `of_a_eq_zero'` / 定理 `of_a_eq_zero'`

English:
theorem of_a_eq_zero'
  statement: toPoly ⟨0, b, c, d⟩ = C b * X ^ 2 + C c * X + C d
  proof: of_a_eq_zero rfl

中文:
定理 of_a_eq_zero'
  结论: toPoly ⟨0, b, c, d⟩ = C b * X ^ 2 + C c * X + C d
  证明: of_a_eq_zero rfl

Depends on / 依赖: of_a_eq_zero
-/
theorem of_a_eq_zero' : toPoly ⟨0, b, c, d⟩ = C b * X ^ 2 + C c * X + C d :=
  of_a_eq_zero rfl

/--
theorem `of_b_eq_zero` / 定理 `of_b_eq_zero`

English:
theorem of_b_eq_zero
  given: (ha : P.a = 0) (hb : P.b = 0)
  statement: P.toPoly = C P.c * X + C P.d
  proof: by
  rw [of_a_eq_zero ha]; rw [hb]; rw [C_0]; rw [zero_mul]; rw [zero_add]

中文:
定理 of_b_eq_zero
  条件: (ha : P.a = 0) (hb : P.b = 0)
  结论: P.toPoly = C P.c * X + C P.d
  证明: by
  rw [of_a_eq_zero ha]; rw [hb]; rw [C_0]; rw [zero_mul]; rw [zero_add]

Depends on / 依赖: CharZero, CharZero.infinite, Infinite, infinite, of_a_eq_zero, zero_add, zero_mul
-/
theorem of_b_eq_zero (ha : P.a = 0) (hb : P.b = 0) : P.toPoly = C P.c * X + C P.d := by
  rw [of_a_eq_zero ha]; rw [hb]; rw [C_0]; rw [zero_mul]; rw [zero_add]

/--
theorem `of_b_eq_zero'` / 定理 `of_b_eq_zero'`

English:
theorem of_b_eq_zero'
  statement: toPoly ⟨0, 0, c, d⟩ = C c * X + C d
  proof: of_b_eq_zero rfl rfl

中文:
定理 of_b_eq_zero'
  结论: toPoly ⟨0, 0, c, d⟩ = C c * X + C d
  证明: of_b_eq_zero rfl rfl

Depends on / 依赖: of_b_eq_zero
-/
theorem of_b_eq_zero' : toPoly ⟨0, 0, c, d⟩ = C c * X + C d :=
  of_b_eq_zero rfl rfl

/--
theorem `of_c_eq_zero` / 定理 `of_c_eq_zero`

English:
theorem of_c_eq_zero
  given: (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0)
  statement: P.toPoly = C P.d
  proof: by
  rw [of_b_eq_zero ha hb]; rw [hc]; rw [C_0]; rw [zero_mul]; rw [zero_add]

中文:
定理 of_c_eq_zero
  条件: (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0)
  结论: P.toPoly = C P.d
  证明: by
  rw [of_b_eq_zero ha hb]; rw [hc]; rw [C_0]; rw [zero_mul]; rw [zero_add]

Depends on / 依赖: of_b_eq_zero, zero_add, zero_mul
-/
theorem of_c_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) : P.toPoly = C P.d := by
  rw [of_b_eq_zero ha hb]; rw [hc]; rw [C_0]; rw [zero_mul]; rw [zero_add]

/--
theorem `of_c_eq_zero'` / 定理 `of_c_eq_zero'`

English:
theorem of_c_eq_zero'
  statement: toPoly ⟨0, 0, 0, d⟩ = C d
  proof: of_c_eq_zero rfl rfl rfl

中文:
定理 of_c_eq_zero'
  结论: toPoly ⟨0, 0, 0, d⟩ = C d
  证明: of_c_eq_zero rfl rfl rfl

Depends on / 依赖: of_c_eq_zero
-/
theorem of_c_eq_zero' : toPoly ⟨0, 0, 0, d⟩ = C d :=
  of_c_eq_zero rfl rfl rfl

/--
theorem `of_d_eq_zero` / 定理 `of_d_eq_zero`

English:
theorem of_d_eq_zero
  given: (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) (hd : P.d = 0)
  proof: by
  rw [of_c_eq_zero ha hb hc]; rw [hd]; rw [C_0]

中文:
定理 of_d_eq_zero
  条件: (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) (hd : P.d = 0)
  证明: by
  rw [of_c_eq_zero ha hb hc]; rw [hd]; rw [C_0]

Depends on / 依赖: of_c_eq_zero
-/
theorem of_d_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) (hd : P.d = 0) :
    P.toPoly = 0 := by
  rw [of_c_eq_zero ha hb hc]; rw [hd]; rw [C_0]

/--
theorem `of_d_eq_zero'` / 定理 `of_d_eq_zero'`

English:
theorem of_d_eq_zero'
  statement: (⟨0, 0, 0, 0⟩ : Cubic R).toPoly = 0
  proof: of_d_eq_zero rfl rfl rfl rfl

中文:
定理 of_d_eq_zero'
  结论: (⟨0, 0, 0, 0⟩ : Cubic R).toPoly = 0
  证明: of_d_eq_zero rfl rfl rfl rfl

Depends on / 依赖: of_d_eq_zero
-/
theorem of_d_eq_zero' : (⟨0, 0, 0, 0⟩ : Cubic R).toPoly = 0 :=
  of_d_eq_zero rfl rfl rfl rfl

/--
theorem `zero` / 定理 `zero`

English:
theorem zero
  statement: (0 : Cubic R).toPoly = 0
  proof: of_d_eq_zero'

中文:
定理 zero
  结论: (0 : Cubic R).toPoly = 0
  证明: of_d_eq_zero'

Depends on / 依赖: of_d_eq_zero
-/
theorem zero : (0 : Cubic R).toPoly = 0 :=
  of_d_eq_zero'

/--
theorem `toPoly_eq_zero_iff` / 定理 `toPoly_eq_zero_iff`

English:
theorem toPoly_eq_zero_iff
  given: (P : Cubic R)
  statement: P.toPoly = 0 ↔ P = 0
  proof: by
  rw [← zero]; rw [toPoly_injective]

中文:
定理 toPoly_eq_zero_iff
  条件: (P : Cubic R)
  结论: P.toPoly = 0 ↔ P = 0
  证明: by
  rw [← zero]; rw [toPoly_injective]

Depends on / 依赖: toPoly_injective
-/
theorem toPoly_eq_zero_iff (P : Cubic R) : P.toPoly = 0 ↔ P = 0 := by
  rw [← zero]; rw [toPoly_injective]

/--
theorem `ne_zero` / 定理 `ne_zero`

English:
theorem ne_zero
  given: (h0 : P.a != 0 ∨ P.b != 0 ∨ P.c != 0 ∨ P.d != 0)
  statement: P.toPoly != 0
  proof: by
  contrapose! h0
  rw [(toPoly_eq_zero_iff P).mp h0]
  exact ⟨rfl, rfl, rfl, rfl⟩

中文:
定理 ne_zero
  条件: (h0 : P.a != 0 ∨ P.b != 0 ∨ P.c != 0 ∨ P.d != 0)
  结论: P.toPoly != 0
  证明: by
  contrapose! h0
  rw [(toPoly_eq_zero_iff P).mp h0]
  exact ⟨rfl, rfl, rfl, rfl⟩
-/
private theorem ne_zero (h0 : P.a != 0 ∨ P.b != 0 ∨ P.c != 0 ∨ P.d != 0) : P.toPoly != 0 := by
  contrapose! h0
  rw [(toPoly_eq_zero_iff P).mp h0]
  exact ⟨rfl, rfl, rfl, rfl⟩

/--
theorem `ne_zero_of_a_ne_zero` / 定理 `ne_zero_of_a_ne_zero`

English:
theorem ne_zero_of_a_ne_zero
  given: (ha : P.a != 0)
  statement: P.toPoly != 0
  proof: (or_imp.mp ne_zero).1 ha

中文:
定理 ne_zero_of_a_ne_zero
  条件: (ha : P.a != 0)
  结论: P.toPoly != 0
  证明: (or_imp.mp ne_zero).1 ha

Depends on / 依赖: ne_zero, or_imp, or_imp.mp
-/
theorem ne_zero_of_a_ne_zero (ha : P.a != 0) : P.toPoly != 0 :=
  (or_imp.mp ne_zero).1 ha

/--
theorem `ne_zero_of_b_ne_zero` / 定理 `ne_zero_of_b_ne_zero`

English:
theorem ne_zero_of_b_ne_zero
  given: (hb : P.b != 0)
  statement: P.toPoly != 0
  proof: (or_imp.mp (or_imp.mp ne_zero).2).1 hb

中文:
定理 ne_zero_of_b_ne_zero
  条件: (hb : P.b != 0)
  结论: P.toPoly != 0
  证明: (or_imp.mp (or_imp.mp ne_zero).2).1 hb

Depends on / 依赖: ne_zero, or_imp, or_imp.mp
-/
theorem ne_zero_of_b_ne_zero (hb : P.b != 0) : P.toPoly != 0 :=
  (or_imp.mp (or_imp.mp ne_zero).2).1 hb

/--
theorem `ne_zero_of_c_ne_zero` / 定理 `ne_zero_of_c_ne_zero`

English:
theorem ne_zero_of_c_ne_zero
  given: (hc : P.c != 0)
  statement: P.toPoly != 0
  proof: (or_imp.mp (or_imp.mp (or_imp.mp ne_zero).2).2).1 hc

中文:
定理 ne_zero_of_c_ne_zero
  条件: (hc : P.c != 0)
  结论: P.toPoly != 0
  证明: (or_imp.mp (or_imp.mp (or_imp.mp ne_zero).2).2).1 hc

Depends on / 依赖: ne_zero, or_imp, or_imp.mp
-/
theorem ne_zero_of_c_ne_zero (hc : P.c != 0) : P.toPoly != 0 :=
  (or_imp.mp (or_imp.mp (or_imp.mp ne_zero).2).2).1 hc

/--
theorem `ne_zero_of_d_ne_zero` / 定理 `ne_zero_of_d_ne_zero`

English:
theorem ne_zero_of_d_ne_zero
  given: (hd : P.d != 0)
  statement: P.toPoly != 0
  proof: (or_imp.mp (or_imp.mp (or_imp.mp ne_zero).2).2).2 hd

@[simp]

中文:
定理 ne_zero_of_d_ne_zero
  条件: (hd : P.d != 0)
  结论: P.toPoly != 0
  证明: (or_imp.mp (or_imp.mp (or_imp.mp ne_zero).2).2).2 hd

@[simp]

Depends on / 依赖: ne_zero, or_imp, or_imp.mp
-/
theorem ne_zero_of_d_ne_zero (hd : P.d != 0) : P.toPoly != 0 :=
  (or_imp.mp (or_imp.mp (or_imp.mp ne_zero).2).2).2 hd

@[simp]
/--
theorem `leadingCoeff_of_a_ne_zero` / 定理 `leadingCoeff_of_a_ne_zero`

English:
theorem leadingCoeff_of_a_ne_zero
  given: (ha : P.a != 0)
  statement: P.toPoly.leadingCoeff = P.a
  proof: leadingCoeff_cubic ha

中文:
定理 leadingCoeff_of_a_ne_zero
  条件: (ha : P.a != 0)
  结论: P.toPoly.leadingCoeff = P.a
  证明: leadingCoeff_cubic ha

Depends on / 依赖: leadingCoeff_cubic
-/
theorem leadingCoeff_of_a_ne_zero (ha : P.a != 0) : P.toPoly.leadingCoeff = P.a :=
  leadingCoeff_cubic ha

/--
theorem `leadingCoeff_of_a_ne_zero'` / 定理 `leadingCoeff_of_a_ne_zero'`

English:
theorem leadingCoeff_of_a_ne_zero'
  given: (ha : a != 0)
  statement: (toPoly ⟨a, b, c, d⟩).leadingCoeff = a
  proof: by
  simp [ha]

@[simp]

中文:
定理 leadingCoeff_of_a_ne_zero'
  条件: (ha : a != 0)
  结论: (toPoly ⟨a, b, c, d⟩).leadingCoeff = a
  证明: by
  simp [ha]

@[simp]
-/
theorem leadingCoeff_of_a_ne_zero' (ha : a != 0) : (toPoly ⟨a, b, c, d⟩).leadingCoeff = a := by
  simp [ha]

@[simp]
/--
theorem `leadingCoeff_of_b_ne_zero` / 定理 `leadingCoeff_of_b_ne_zero`

English:
theorem leadingCoeff_of_b_ne_zero
  given: (ha : P.a = 0) (hb : P.b != 0)
  statement: P.toPoly.leadingCoeff = P.b
  proof: by
  rw [of_a_eq_zero ha]; rw [leadingCoeff_quadratic hb]

中文:
定理 leadingCoeff_of_b_ne_zero
  条件: (ha : P.a = 0) (hb : P.b != 0)
  结论: P.toPoly.leadingCoeff = P.b
  证明: by
  rw [of_a_eq_zero ha]; rw [leadingCoeff_quadratic hb]

Depends on / 依赖: leadingCoeff_quadratic, of_a_eq_zero
-/
theorem leadingCoeff_of_b_ne_zero (ha : P.a = 0) (hb : P.b != 0) : P.toPoly.leadingCoeff = P.b := by
  rw [of_a_eq_zero ha]; rw [leadingCoeff_quadratic hb]

/--
theorem `leadingCoeff_of_b_ne_zero'` / 定理 `leadingCoeff_of_b_ne_zero'`

English:
theorem leadingCoeff_of_b_ne_zero'
  given: (hb : b != 0)
  statement: (toPoly ⟨0, b, c, d⟩).leadingCoeff = b
  proof: by
  simp [hb]

@[simp]

中文:
定理 leadingCoeff_of_b_ne_zero'
  条件: (hb : b != 0)
  结论: (toPoly ⟨0, b, c, d⟩).leadingCoeff = b
  证明: by
  simp [hb]

@[simp]
-/
theorem leadingCoeff_of_b_ne_zero' (hb : b != 0) : (toPoly ⟨0, b, c, d⟩).leadingCoeff = b := by
  simp [hb]

@[simp]
/--
theorem `leadingCoeff_of_c_ne_zero` / 定理 `leadingCoeff_of_c_ne_zero`

English:
theorem leadingCoeff_of_c_ne_zero
  given: (ha : P.a = 0) (hb : P.b = 0) (hc : P.c != 0)
  proof: by
  rw [of_b_eq_zero ha hb]; rw [leadingCoeff_linear hc]

中文:
定理 leadingCoeff_of_c_ne_zero
  条件: (ha : P.a = 0) (hb : P.b = 0) (hc : P.c != 0)
  证明: by
  rw [of_b_eq_zero ha hb]; rw [leadingCoeff_linear hc]

Depends on / 依赖: leadingCoeff_linear, of_b_eq_zero
-/
theorem leadingCoeff_of_c_ne_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c != 0) :
    P.toPoly.leadingCoeff = P.c := by
  rw [of_b_eq_zero ha hb]; rw [leadingCoeff_linear hc]

/--
theorem `leadingCoeff_of_c_ne_zero'` / 定理 `leadingCoeff_of_c_ne_zero'`

English:
theorem leadingCoeff_of_c_ne_zero'
  given: (hc : c != 0)
  statement: (toPoly ⟨0, 0, c, d⟩).leadingCoeff = c
  proof: by
  simp [hc]

@[simp]

中文:
定理 leadingCoeff_of_c_ne_zero'
  条件: (hc : c != 0)
  结论: (toPoly ⟨0, 0, c, d⟩).leadingCoeff = c
  证明: by
  simp [hc]

@[simp]
-/
theorem leadingCoeff_of_c_ne_zero' (hc : c != 0) : (toPoly ⟨0, 0, c, d⟩).leadingCoeff = c := by
  simp [hc]

@[simp]
/--
theorem `leadingCoeff_of_c_eq_zero` / 定理 `leadingCoeff_of_c_eq_zero`

English:
theorem leadingCoeff_of_c_eq_zero
  given: (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0)
  proof: by
  rw [of_c_eq_zero ha hb hc]; rw [leadingCoeff_C]

中文:
定理 leadingCoeff_of_c_eq_zero
  条件: (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0)
  证明: by
  rw [of_c_eq_zero ha hb hc]; rw [leadingCoeff_C]

Depends on / 依赖: leadingCoeff_C, of_c_eq_zero
-/
theorem leadingCoeff_of_c_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) :
    P.toPoly.leadingCoeff = P.d := by
  rw [of_c_eq_zero ha hb hc]; rw [leadingCoeff_C]

/--
theorem `leadingCoeff_of_c_eq_zero'` / 定理 `leadingCoeff_of_c_eq_zero'`

English:
theorem leadingCoeff_of_c_eq_zero'
  statement: (toPoly ⟨0, 0, 0, d⟩).leadingCoeff = d
  proof: leadingCoeff_of_c_eq_zero rfl rfl rfl

中文:
定理 leadingCoeff_of_c_eq_zero'
  结论: (toPoly ⟨0, 0, 0, d⟩).leadingCoeff = d
  证明: leadingCoeff_of_c_eq_zero rfl rfl rfl

Depends on / 依赖: leadingCoeff_of_c_eq_zero
-/
theorem leadingCoeff_of_c_eq_zero' : (toPoly ⟨0, 0, 0, d⟩).leadingCoeff = d :=
  leadingCoeff_of_c_eq_zero rfl rfl rfl

/--
theorem `monic_of_a_eq_one` / 定理 `monic_of_a_eq_one`

English:
theorem monic_of_a_eq_one
  given: (ha : P.a = 1)
  statement: P.toPoly.Monic
  proof: by
  nontriviality R
  rw [Monic]; rw [leadingCoeff_of_a_ne_zero (ha ▸ one_ne_zero)]; rw [ha]

中文:
定理 monic_of_a_eq_one
  条件: (ha : P.a = 1)
  结论: P.toPoly.Monic
  证明: by
  nontriviality R
  rw [Monic]; rw [leadingCoeff_of_a_ne_zero (ha ▸ one_ne_zero)]; rw [ha]

Depends on / 依赖: leadingCoeff_of_a_ne_zero, nontriviality, one_ne_zero
-/
theorem monic_of_a_eq_one (ha : P.a = 1) : P.toPoly.Monic := by
  nontriviality R
  rw [Monic]; rw [leadingCoeff_of_a_ne_zero (ha ▸ one_ne_zero)]; rw [ha]

/--
theorem `monic_of_a_eq_one'` / 定理 `monic_of_a_eq_one'`

English:
theorem monic_of_a_eq_one'
  statement: (toPoly ⟨1, b, c, d⟩).Monic
  proof: monic_of_a_eq_one rfl

中文:
定理 monic_of_a_eq_one'
  结论: (toPoly ⟨1, b, c, d⟩).Monic
  证明: monic_of_a_eq_one rfl

Depends on / 依赖: monic_of_a_eq_one
-/
theorem monic_of_a_eq_one' : (toPoly ⟨1, b, c, d⟩).Monic :=
  monic_of_a_eq_one rfl

/--
theorem `monic_of_b_eq_one` / 定理 `monic_of_b_eq_one`

English:
theorem monic_of_b_eq_one
  given: (ha : P.a = 0) (hb : P.b = 1)
  statement: P.toPoly.Monic
  proof: by
  nontriviality R
  rw [Monic]; rw [leadingCoeff_of_b_ne_zero ha (hb ▸ one_ne_zero)]; rw [hb]

中文:
定理 monic_of_b_eq_one
  条件: (ha : P.a = 0) (hb : P.b = 1)
  结论: P.toPoly.Monic
  证明: by
  nontriviality R
  rw [Monic]; rw [leadingCoeff_of_b_ne_zero ha (hb ▸ one_ne_zero)]; rw [hb]

Depends on / 依赖: leadingCoeff_of_b_ne_zero, nontriviality, one_ne_zero
-/
theorem monic_of_b_eq_one (ha : P.a = 0) (hb : P.b = 1) : P.toPoly.Monic := by
  nontriviality R
  rw [Monic]; rw [leadingCoeff_of_b_ne_zero ha (hb ▸ one_ne_zero)]; rw [hb]

/--
theorem `monic_of_b_eq_one'` / 定理 `monic_of_b_eq_one'`

English:
theorem monic_of_b_eq_one'
  statement: (toPoly ⟨0, 1, c, d⟩).Monic
  proof: monic_of_b_eq_one rfl rfl

中文:
定理 monic_of_b_eq_one'
  结论: (toPoly ⟨0, 1, c, d⟩).Monic
  证明: monic_of_b_eq_one rfl rfl

Depends on / 依赖: monic_of_b_eq_one
-/
theorem monic_of_b_eq_one' : (toPoly ⟨0, 1, c, d⟩).Monic :=
  monic_of_b_eq_one rfl rfl

/--
theorem `monic_of_c_eq_one` / 定理 `monic_of_c_eq_one`

English:
theorem monic_of_c_eq_one
  given: (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 1)
  statement: P.toPoly.Monic
  proof: by
  nontriviality R
  rw [Monic]; rw [leadingCoeff_of_c_ne_zero ha hb (hc ▸ one_ne_zero)]; rw [hc]

中文:
定理 monic_of_c_eq_one
  条件: (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 1)
  结论: P.toPoly.Monic
  证明: by
  nontriviality R
  rw [Monic]; rw [leadingCoeff_of_c_ne_zero ha hb (hc ▸ one_ne_zero)]; rw [hc]

Depends on / 依赖: leadingCoeff_of_c_ne_zero, nontriviality, one_ne_zero
-/
theorem monic_of_c_eq_one (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 1) : P.toPoly.Monic := by
  nontriviality R
  rw [Monic]; rw [leadingCoeff_of_c_ne_zero ha hb (hc ▸ one_ne_zero)]; rw [hc]

/--
theorem `monic_of_c_eq_one'` / 定理 `monic_of_c_eq_one'`

English:
theorem monic_of_c_eq_one'
  statement: (toPoly ⟨0, 0, 1, d⟩).Monic
  proof: monic_of_c_eq_one rfl rfl rfl

中文:
定理 monic_of_c_eq_one'
  结论: (toPoly ⟨0, 0, 1, d⟩).Monic
  证明: monic_of_c_eq_one rfl rfl rfl

Depends on / 依赖: monic_of_c_eq_one
-/
theorem monic_of_c_eq_one' : (toPoly ⟨0, 0, 1, d⟩).Monic :=
  monic_of_c_eq_one rfl rfl rfl

/--
theorem `monic_of_d_eq_one` / 定理 `monic_of_d_eq_one`

English:
theorem monic_of_d_eq_one
  given: (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) (hd : P.d = 1)
  proof: by
  rw [Monic]; rw [leadingCoeff_of_c_eq_zero ha hb hc]; rw [hd]

中文:
定理 monic_of_d_eq_one
  条件: (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) (hd : P.d = 1)
  证明: by
  rw [Monic]; rw [leadingCoeff_of_c_eq_zero ha hb hc]; rw [hd]

Depends on / 依赖: leadingCoeff_of_c_eq_zero
-/
theorem monic_of_d_eq_one (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) (hd : P.d = 1) :
    P.toPoly.Monic := by
  rw [Monic]; rw [leadingCoeff_of_c_eq_zero ha hb hc]; rw [hd]

/--
theorem `monic_of_d_eq_one'` / 定理 `monic_of_d_eq_one'`

English:
theorem monic_of_d_eq_one'
  statement: (toPoly ⟨0, 0, 0, 1⟩).Monic
  proof: monic_of_d_eq_one rfl rfl rfl rfl

中文:
定理 monic_of_d_eq_one'
  结论: (toPoly ⟨0, 0, 0, 1⟩).Monic
  证明: monic_of_d_eq_one rfl rfl rfl rfl

Depends on / 依赖: monic_of_d_eq_one
-/
theorem monic_of_d_eq_one' : (toPoly ⟨0, 0, 0, 1⟩).Monic :=
  monic_of_d_eq_one rfl rfl rfl rfl

end Coeff

/-! ### Degrees -/


section Degree

/-- The equivalence between cubic polynomials and polynomials of degree at most three. -/
@[simps]
/--
Definition of `equiv` / `equiv` 的定义

English:
definition equiv
  signature: : Cubic R ≃ { p : R[X] // p.degree <= 3 } where
  body: ⟨P.toPoly, degree_cubic_le⟩
  invFun f := ⟨coeff f 3, coeff f 2, coeff f 1, coeff f 0⟩
  left_inv P := by ext <;> simp only [coeffs]
  right_inv f := by
    ext n
    obtain hn | hn := le_or_gt n 3
    · interval_cases n <;> simp only <;> ring_nf <;> try simp only [coeffs]
    · rw [coeff_eq_zero hn

中文:
定义 equiv
  签名: : Cubic R ≃ { p : R[X] // p.degree <= 3 } where
  定义体: ⟨P.toPoly, degree_cubic_le⟩
  invFun f := ⟨coeff f 3, coeff f 2, coeff f 1, coeff f 0⟩
  left_inv P := by ext <;> simp only [coeffs]
  right_inv f := by
    ext n
    obtain hn | hn := le_or_gt n 3
    · interval_cases n <;> simp only <;> ring_nf <;> try simp only [coeffs]
    · rw [coeff_eq_zero hn

Depends on / 依赖: P.toPoly, degree_cubic_le, toPoly
-/
def equiv : Cubic R ≃ { p : R[X] // p.degree <= 3 } where
  toFun P := ⟨P.toPoly, degree_cubic_le⟩
  invFun f := ⟨coeff f 3, coeff f 2, coeff f 1, coeff f 0⟩
  left_inv P := by ext <;> simp only [coeffs]
  right_inv f := by
    ext n
    obtain hn | hn := le_or_gt n 3
    · interval_cases n <;> simp only <;> ring_nf <;> try simp only [coeffs]
    · rw [coeff_eq_zero hn, (degree_le_iff_coeff_zero (f : R[X]) 3).mp f.2]
      simpa using hn

@[simp]
/--
theorem `degree_of_a_ne_zero` / 定理 `degree_of_a_ne_zero`

English:
theorem degree_of_a_ne_zero
  given: (ha : P.a != 0)
  statement: P.toPoly.degree = 3
  proof: degree_cubic ha

中文:
定理 degree_of_a_ne_zero
  条件: (ha : P.a != 0)
  结论: P.toPoly.degree = 3
  证明: degree_cubic ha

Depends on / 依赖: degree_cubic
-/
theorem degree_of_a_ne_zero (ha : P.a != 0) : P.toPoly.degree = 3 :=
  degree_cubic ha

/--
theorem `degree_of_a_ne_zero'` / 定理 `degree_of_a_ne_zero'`

English:
theorem degree_of_a_ne_zero'
  given: (ha : a != 0)
  statement: (toPoly ⟨a, b, c, d⟩).degree = 3
  proof: by
  simp [ha]

中文:
定理 degree_of_a_ne_zero'
  条件: (ha : a != 0)
  结论: (toPoly ⟨a, b, c, d⟩).degree = 3
  证明: by
  simp [ha]
-/
theorem degree_of_a_ne_zero' (ha : a != 0) : (toPoly ⟨a, b, c, d⟩).degree = 3 := by
  simp [ha]

/--
theorem `degree_of_a_eq_zero` / 定理 `degree_of_a_eq_zero`

English:
theorem degree_of_a_eq_zero
  given: (ha : P.a = 0)
  statement: P.toPoly.degree <= 2
  proof: by
  simpa only [of_a_eq_zero ha] using degree_quadratic_le

中文:
定理 degree_of_a_eq_zero
  条件: (ha : P.a = 0)
  结论: P.toPoly.degree <= 2
  证明: by
  simpa only [of_a_eq_zero ha] using degree_quadratic_le

Depends on / 依赖: degree_quadratic_le, of_a_eq_zero
-/
theorem degree_of_a_eq_zero (ha : P.a = 0) : P.toPoly.degree <= 2 := by
  simpa only [of_a_eq_zero ha] using degree_quadratic_le

/--
theorem `degree_of_a_eq_zero'` / 定理 `degree_of_a_eq_zero'`

English:
theorem degree_of_a_eq_zero'
  statement: (toPoly ⟨0, b, c, d⟩).degree <= 2
  proof: degree_of_a_eq_zero rfl

@[simp]

中文:
定理 degree_of_a_eq_zero'
  结论: (toPoly ⟨0, b, c, d⟩).degree <= 2
  证明: degree_of_a_eq_zero rfl

@[simp]

Depends on / 依赖: degree_of_a_eq_zero
-/
theorem degree_of_a_eq_zero' : (toPoly ⟨0, b, c, d⟩).degree <= 2 :=
  degree_of_a_eq_zero rfl

@[simp]
/--
theorem `degree_of_b_ne_zero` / 定理 `degree_of_b_ne_zero`

English:
theorem degree_of_b_ne_zero
  given: (ha : P.a = 0) (hb : P.b != 0)
  statement: P.toPoly.degree = 2
  proof: by
  rw [of_a_eq_zero ha]; rw [degree_quadratic hb]

中文:
定理 degree_of_b_ne_zero
  条件: (ha : P.a = 0) (hb : P.b != 0)
  结论: P.toPoly.degree = 2
  证明: by
  rw [of_a_eq_zero ha]; rw [degree_quadratic hb]

Depends on / 依赖: degree_quadratic, of_a_eq_zero
-/
theorem degree_of_b_ne_zero (ha : P.a = 0) (hb : P.b != 0) : P.toPoly.degree = 2 := by
  rw [of_a_eq_zero ha]; rw [degree_quadratic hb]

/--
theorem `degree_of_b_ne_zero'` / 定理 `degree_of_b_ne_zero'`

English:
theorem degree_of_b_ne_zero'
  given: (hb : b != 0)
  statement: (toPoly ⟨0, b, c, d⟩).degree = 2
  proof: by
  simp [hb]

中文:
定理 degree_of_b_ne_zero'
  条件: (hb : b != 0)
  结论: (toPoly ⟨0, b, c, d⟩).degree = 2
  证明: by
  simp [hb]
-/
theorem degree_of_b_ne_zero' (hb : b != 0) : (toPoly ⟨0, b, c, d⟩).degree = 2 := by
  simp [hb]

/--
theorem `degree_of_b_eq_zero` / 定理 `degree_of_b_eq_zero`

English:
theorem degree_of_b_eq_zero
  given: (ha : P.a = 0) (hb : P.b = 0)
  statement: P.toPoly.degree <= 1
  proof: by
  simpa only [of_b_eq_zero ha hb] using degree_linear_le

中文:
定理 degree_of_b_eq_zero
  条件: (ha : P.a = 0) (hb : P.b = 0)
  结论: P.toPoly.degree <= 1
  证明: by
  simpa only [of_b_eq_zero ha hb] using degree_linear_le

Depends on / 依赖: degree_linear_le, of_b_eq_zero
-/
theorem degree_of_b_eq_zero (ha : P.a = 0) (hb : P.b = 0) : P.toPoly.degree <= 1 := by
  simpa only [of_b_eq_zero ha hb] using degree_linear_le

/--
theorem `degree_of_b_eq_zero'` / 定理 `degree_of_b_eq_zero'`

English:
theorem degree_of_b_eq_zero'
  statement: (toPoly ⟨0, 0, c, d⟩).degree <= 1
  proof: degree_of_b_eq_zero rfl rfl

@[simp]

中文:
定理 degree_of_b_eq_zero'
  结论: (toPoly ⟨0, 0, c, d⟩).degree <= 1
  证明: degree_of_b_eq_zero rfl rfl

@[simp]

Depends on / 依赖: degree_of_b_eq_zero
-/
theorem degree_of_b_eq_zero' : (toPoly ⟨0, 0, c, d⟩).degree <= 1 :=
  degree_of_b_eq_zero rfl rfl

@[simp]
/--
theorem `degree_of_c_ne_zero` / 定理 `degree_of_c_ne_zero`

English:
theorem degree_of_c_ne_zero
  given: (ha : P.a = 0) (hb : P.b = 0) (hc : P.c != 0)
  statement: P.toPoly.degree = 1
  proof: by
  rw [of_b_eq_zero ha hb]; rw [degree_linear hc]

中文:
定理 degree_of_c_ne_zero
  条件: (ha : P.a = 0) (hb : P.b = 0) (hc : P.c != 0)
  结论: P.toPoly.degree = 1
  证明: by
  rw [of_b_eq_zero ha hb]; rw [degree_linear hc]

Depends on / 依赖: degree_linear, of_b_eq_zero
-/
theorem degree_of_c_ne_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c != 0) : P.toPoly.degree = 1 := by
  rw [of_b_eq_zero ha hb]; rw [degree_linear hc]

/--
theorem `degree_of_c_ne_zero'` / 定理 `degree_of_c_ne_zero'`

English:
theorem degree_of_c_ne_zero'
  given: (hc : c != 0)
  statement: (toPoly ⟨0, 0, c, d⟩).degree = 1
  proof: by
  simp [hc]

中文:
定理 degree_of_c_ne_zero'
  条件: (hc : c != 0)
  结论: (toPoly ⟨0, 0, c, d⟩).degree = 1
  证明: by
  simp [hc]
-/
theorem degree_of_c_ne_zero' (hc : c != 0) : (toPoly ⟨0, 0, c, d⟩).degree = 1 := by
  simp [hc]

/--
theorem `degree_of_c_eq_zero` / 定理 `degree_of_c_eq_zero`

English:
theorem degree_of_c_eq_zero
  given: (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0)
  statement: P.toPoly.degree <= 0
  proof: by
  simpa only [of_c_eq_zero ha hb hc] using degree_C_le

中文:
定理 degree_of_c_eq_zero
  条件: (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0)
  结论: P.toPoly.degree <= 0
  证明: by
  simpa only [of_c_eq_zero ha hb hc] using degree_C_le

Depends on / 依赖: degree_C_le, of_c_eq_zero
-/
theorem degree_of_c_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) : P.toPoly.degree <= 0 := by
  simpa only [of_c_eq_zero ha hb hc] using degree_C_le

/--
theorem `degree_of_c_eq_zero'` / 定理 `degree_of_c_eq_zero'`

English:
theorem degree_of_c_eq_zero'
  statement: (toPoly ⟨0, 0, 0, d⟩).degree <= 0
  proof: degree_of_c_eq_zero rfl rfl rfl

@[simp]

中文:
定理 degree_of_c_eq_zero'
  结论: (toPoly ⟨0, 0, 0, d⟩).degree <= 0
  证明: degree_of_c_eq_zero rfl rfl rfl

@[simp]

Depends on / 依赖: degree_of_c_eq_zero
-/
theorem degree_of_c_eq_zero' : (toPoly ⟨0, 0, 0, d⟩).degree <= 0 :=
  degree_of_c_eq_zero rfl rfl rfl

@[simp]
/--
theorem `degree_of_d_ne_zero` / 定理 `degree_of_d_ne_zero`

English:
theorem degree_of_d_ne_zero
  given: (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) (hd : P.d != 0)
  proof: by
  rw [of_c_eq_zero ha hb hc]; rw [degree_C hd]

中文:
定理 degree_of_d_ne_zero
  条件: (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) (hd : P.d != 0)
  证明: by
  rw [of_c_eq_zero ha hb hc]; rw [degree_C hd]

Depends on / 依赖: degree_C, of_c_eq_zero
-/
theorem degree_of_d_ne_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) (hd : P.d != 0) :
    P.toPoly.degree = 0 := by
  rw [of_c_eq_zero ha hb hc]; rw [degree_C hd]

/--
theorem `degree_of_d_ne_zero'` / 定理 `degree_of_d_ne_zero'`

English:
theorem degree_of_d_ne_zero'
  given: (hd : d != 0)
  statement: (toPoly ⟨0, 0, 0, d⟩).degree = 0
  proof: by
  simp [hd]

@[simp]

中文:
定理 degree_of_d_ne_zero'
  条件: (hd : d != 0)
  结论: (toPoly ⟨0, 0, 0, d⟩).degree = 0
  证明: by
  simp [hd]

@[simp]
-/
theorem degree_of_d_ne_zero' (hd : d != 0) : (toPoly ⟨0, 0, 0, d⟩).degree = 0 := by
  simp [hd]

@[simp]
/--
theorem `degree_of_d_eq_zero` / 定理 `degree_of_d_eq_zero`

English:
theorem degree_of_d_eq_zero
  given: (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) (hd : P.d = 0)
  proof: by
  rw [of_d_eq_zero ha hb hc hd]; rw [degree_zero]

中文:
定理 degree_of_d_eq_zero
  条件: (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) (hd : P.d = 0)
  证明: by
  rw [of_d_eq_zero ha hb hc hd]; rw [degree_zero]

Depends on / 依赖: degree_zero, of_d_eq_zero
-/
theorem degree_of_d_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) (hd : P.d = 0) :
    P.toPoly.degree = ⊥ := by
  rw [of_d_eq_zero ha hb hc hd]; rw [degree_zero]

/--
theorem `degree_of_d_eq_zero'` / 定理 `degree_of_d_eq_zero'`

English:
theorem degree_of_d_eq_zero'
  statement: (⟨0, 0, 0, 0⟩ : Cubic R).toPoly.degree = ⊥
  proof: degree_of_d_eq_zero rfl rfl rfl rfl

@[simp]

中文:
定理 degree_of_d_eq_zero'
  结论: (⟨0, 0, 0, 0⟩ : Cubic R).toPoly.degree = ⊥
  证明: degree_of_d_eq_zero rfl rfl rfl rfl

@[simp]

Depends on / 依赖: degree_of_d_eq_zero
-/
theorem degree_of_d_eq_zero' : (⟨0, 0, 0, 0⟩ : Cubic R).toPoly.degree = ⊥ :=
  degree_of_d_eq_zero rfl rfl rfl rfl

@[simp]
/--
theorem `degree_of_zero` / 定理 `degree_of_zero`

English:
theorem degree_of_zero
  statement: (0 : Cubic R).toPoly.degree = ⊥
  proof: degree_of_d_eq_zero'

@[simp]

中文:
定理 degree_of_zero
  结论: (0 : Cubic R).toPoly.degree = ⊥
  证明: degree_of_d_eq_zero'

@[simp]

Depends on / 依赖: degree_of_d_eq_zero
-/
theorem degree_of_zero : (0 : Cubic R).toPoly.degree = ⊥ :=
  degree_of_d_eq_zero'

@[simp]
/--
theorem `natDegree_of_a_ne_zero` / 定理 `natDegree_of_a_ne_zero`

English:
theorem natDegree_of_a_ne_zero
  given: (ha : P.a != 0)
  statement: P.toPoly.natDegree = 3
  proof: natDegree_cubic ha

中文:
定理 natDegree_of_a_ne_zero
  条件: (ha : P.a != 0)
  结论: P.toPoly.natDegree = 3
  证明: natDegree_cubic ha

Depends on / 依赖: natDegree_cubic
-/
theorem natDegree_of_a_ne_zero (ha : P.a != 0) : P.toPoly.natDegree = 3 :=
  natDegree_cubic ha

/--
theorem `natDegree_of_a_ne_zero'` / 定理 `natDegree_of_a_ne_zero'`

English:
theorem natDegree_of_a_ne_zero'
  given: (ha : a != 0)
  statement: (toPoly ⟨a, b, c, d⟩).natDegree = 3
  proof: by
  simp [ha]

中文:
定理 natDegree_of_a_ne_zero'
  条件: (ha : a != 0)
  结论: (toPoly ⟨a, b, c, d⟩).natDegree = 3
  证明: by
  simp [ha]
-/
theorem natDegree_of_a_ne_zero' (ha : a != 0) : (toPoly ⟨a, b, c, d⟩).natDegree = 3 := by
  simp [ha]

/--
theorem `natDegree_of_a_eq_zero` / 定理 `natDegree_of_a_eq_zero`

English:
theorem natDegree_of_a_eq_zero
  given: (ha : P.a = 0)
  statement: P.toPoly.natDegree <= 2
  proof: by
  simpa only [of_a_eq_zero ha] using natDegree_quadratic_le

中文:
定理 natDegree_of_a_eq_zero
  条件: (ha : P.a = 0)
  结论: P.toPoly.natDegree <= 2
  证明: by
  simpa only [of_a_eq_zero ha] using natDegree_quadratic_le

Depends on / 依赖: natDegree_quadratic_le, of_a_eq_zero
-/
theorem natDegree_of_a_eq_zero (ha : P.a = 0) : P.toPoly.natDegree <= 2 := by
  simpa only [of_a_eq_zero ha] using natDegree_quadratic_le

/--
theorem `natDegree_of_a_eq_zero'` / 定理 `natDegree_of_a_eq_zero'`

English:
theorem natDegree_of_a_eq_zero'
  statement: (toPoly ⟨0, b, c, d⟩).natDegree <= 2
  proof: natDegree_of_a_eq_zero rfl

@[simp]

中文:
定理 natDegree_of_a_eq_zero'
  结论: (toPoly ⟨0, b, c, d⟩).natDegree <= 2
  证明: natDegree_of_a_eq_zero rfl

@[simp]

Depends on / 依赖: natDegree_of_a_eq_zero
-/
theorem natDegree_of_a_eq_zero' : (toPoly ⟨0, b, c, d⟩).natDegree <= 2 :=
  natDegree_of_a_eq_zero rfl

@[simp]
/--
theorem `natDegree_of_b_ne_zero` / 定理 `natDegree_of_b_ne_zero`

English:
theorem natDegree_of_b_ne_zero
  given: (ha : P.a = 0) (hb : P.b != 0)
  statement: P.toPoly.natDegree = 2
  proof: by
  rw [of_a_eq_zero ha]; rw [natDegree_quadratic hb]

中文:
定理 natDegree_of_b_ne_zero
  条件: (ha : P.a = 0) (hb : P.b != 0)
  结论: P.toPoly.natDegree = 2
  证明: by
  rw [of_a_eq_zero ha]; rw [natDegree_quadratic hb]

Depends on / 依赖: natDegree_quadratic, of_a_eq_zero
-/
theorem natDegree_of_b_ne_zero (ha : P.a = 0) (hb : P.b != 0) : P.toPoly.natDegree = 2 := by
  rw [of_a_eq_zero ha]; rw [natDegree_quadratic hb]

/--
theorem `natDegree_of_b_ne_zero'` / 定理 `natDegree_of_b_ne_zero'`

English:
theorem natDegree_of_b_ne_zero'
  given: (hb : b != 0)
  statement: (toPoly ⟨0, b, c, d⟩).natDegree = 2
  proof: by
  simp [hb]

中文:
定理 natDegree_of_b_ne_zero'
  条件: (hb : b != 0)
  结论: (toPoly ⟨0, b, c, d⟩).natDegree = 2
  证明: by
  simp [hb]
-/
theorem natDegree_of_b_ne_zero' (hb : b != 0) : (toPoly ⟨0, b, c, d⟩).natDegree = 2 := by
  simp [hb]

/--
theorem `natDegree_of_b_eq_zero` / 定理 `natDegree_of_b_eq_zero`

English:
theorem natDegree_of_b_eq_zero
  given: (ha : P.a = 0) (hb : P.b = 0)
  statement: P.toPoly.natDegree <= 1
  proof: by
  simpa only [of_b_eq_zero ha hb] using natDegree_linear_le

中文:
定理 natDegree_of_b_eq_zero
  条件: (ha : P.a = 0) (hb : P.b = 0)
  结论: P.toPoly.natDegree <= 1
  证明: by
  simpa only [of_b_eq_zero ha hb] using natDegree_linear_le

Depends on / 依赖: natDegree_linear_le, of_b_eq_zero
-/
theorem natDegree_of_b_eq_zero (ha : P.a = 0) (hb : P.b = 0) : P.toPoly.natDegree <= 1 := by
  simpa only [of_b_eq_zero ha hb] using natDegree_linear_le

/--
theorem `natDegree_of_b_eq_zero'` / 定理 `natDegree_of_b_eq_zero'`

English:
theorem natDegree_of_b_eq_zero'
  statement: (toPoly ⟨0, 0, c, d⟩).natDegree <= 1
  proof: natDegree_of_b_eq_zero rfl rfl

@[simp]

中文:
定理 natDegree_of_b_eq_zero'
  结论: (toPoly ⟨0, 0, c, d⟩).natDegree <= 1
  证明: natDegree_of_b_eq_zero rfl rfl

@[simp]

Depends on / 依赖: natDegree_of_b_eq_zero
-/
theorem natDegree_of_b_eq_zero' : (toPoly ⟨0, 0, c, d⟩).natDegree <= 1 :=
  natDegree_of_b_eq_zero rfl rfl

@[simp]
/--
theorem `natDegree_of_c_ne_zero` / 定理 `natDegree_of_c_ne_zero`

English:
theorem natDegree_of_c_ne_zero
  given: (ha : P.a = 0) (hb : P.b = 0) (hc : P.c != 0)
  proof: by
  rw [of_b_eq_zero ha hb]; rw [natDegree_linear hc]

中文:
定理 natDegree_of_c_ne_zero
  条件: (ha : P.a = 0) (hb : P.b = 0) (hc : P.c != 0)
  证明: by
  rw [of_b_eq_zero ha hb]; rw [natDegree_linear hc]

Depends on / 依赖: natDegree_linear, of_b_eq_zero
-/
theorem natDegree_of_c_ne_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c != 0) :
    P.toPoly.natDegree = 1 := by
  rw [of_b_eq_zero ha hb]; rw [natDegree_linear hc]

/--
theorem `natDegree_of_c_ne_zero'` / 定理 `natDegree_of_c_ne_zero'`

English:
theorem natDegree_of_c_ne_zero'
  given: (hc : c != 0)
  statement: (toPoly ⟨0, 0, c, d⟩).natDegree = 1
  proof: by
  simp [hc]

@[simp]

中文:
定理 natDegree_of_c_ne_zero'
  条件: (hc : c != 0)
  结论: (toPoly ⟨0, 0, c, d⟩).natDegree = 1
  证明: by
  simp [hc]

@[simp]
-/
theorem natDegree_of_c_ne_zero' (hc : c != 0) : (toPoly ⟨0, 0, c, d⟩).natDegree = 1 := by
  simp [hc]

@[simp]
/--
theorem `natDegree_of_c_eq_zero` / 定理 `natDegree_of_c_eq_zero`

English:
theorem natDegree_of_c_eq_zero
  given: (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0)
  proof: by
  rw [of_c_eq_zero ha hb hc]; rw [natDegree_C]

中文:
定理 natDegree_of_c_eq_zero
  条件: (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0)
  证明: by
  rw [of_c_eq_zero ha hb hc]; rw [natDegree_C]

Depends on / 依赖: natDegree_C, of_c_eq_zero
-/
theorem natDegree_of_c_eq_zero (ha : P.a = 0) (hb : P.b = 0) (hc : P.c = 0) :
    P.toPoly.natDegree = 0 := by
  rw [of_c_eq_zero ha hb hc]; rw [natDegree_C]

/--
theorem `natDegree_of_c_eq_zero'` / 定理 `natDegree_of_c_eq_zero'`

English:
theorem natDegree_of_c_eq_zero'
  statement: (toPoly ⟨0, 0, 0, d⟩).natDegree = 0
  proof: natDegree_of_c_eq_zero rfl rfl rfl

@[simp]

中文:
定理 natDegree_of_c_eq_zero'
  结论: (toPoly ⟨0, 0, 0, d⟩).natDegree = 0
  证明: natDegree_of_c_eq_zero rfl rfl rfl

@[simp]

Depends on / 依赖: natDegree_of_c_eq_zero
-/
theorem natDegree_of_c_eq_zero' : (toPoly ⟨0, 0, 0, d⟩).natDegree = 0 :=
  natDegree_of_c_eq_zero rfl rfl rfl

@[simp]
/--
theorem `natDegree_of_zero` / 定理 `natDegree_of_zero`

English:
theorem natDegree_of_zero
  statement: (0 : Cubic R).toPoly.natDegree = 0
  proof: natDegree_of_c_eq_zero'

中文:
定理 natDegree_of_zero
  结论: (0 : Cubic R).toPoly.natDegree = 0
  证明: natDegree_of_c_eq_zero'

Depends on / 依赖: natDegree_of_c_eq_zero
-/
theorem natDegree_of_zero : (0 : Cubic R).toPoly.natDegree = 0 :=
  natDegree_of_c_eq_zero'

end Degree

/-! ### Map across a homomorphism -/


section Map

variable [Semiring S] {φ : R ->+* S}

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (φ : R ->+* S) (P : Cubic R)
  body: ⟨φ P.a, φ P.b, φ P.c, φ P.d⟩

中文:
定义 map
  签名: (φ : R ->+* S) (P : Cubic R)
  定义体: ⟨φ P.a, φ P.b, φ P.c, φ P.d⟩
-/
def map (φ : R ->+* S) (P : Cubic R) : Cubic S :=
  ⟨φ P.a, φ P.b, φ P.c, φ P.d⟩

/--
theorem `map_toPoly` / 定理 `map_toPoly`

English:
theorem map_toPoly
  statement: (map φ P).toPoly = Polynomial.map φ P.toPoly
  proof: by
  simp only [map, toPoly, map_C, map_X, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow]

中文:
定理 map_toPoly
  结论: (map φ P).toPoly = Polynomial.map φ P.toPoly
  证明: by
  simp only [map, toPoly, map_C, map_X, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow]

Depends on / 依赖: Polynomial, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, map_C, map_X, map_add, map_mul, map_pow, toPoly
-/
theorem map_toPoly : (map φ P).toPoly = Polynomial.map φ P.toPoly := by
  simp only [map, toPoly, map_C, map_X, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow]

end Map

end Basic

section Roots

open Multiset

/-! ### Roots over an extension -/


section Extension

variable {P : Cubic R} [CommRing R] [CommRing S] {φ : R ->+* S}

/--
Definition of `roots` / `roots` 的定义

English:
definition roots
  signature: [IsDomain R] (P : Cubic R)
  body: P.toPoly.roots

中文:
定义 roots
  签名: [IsDomain R] (P : Cubic R)
  定义体: P.toPoly.roots

Depends on / 依赖: P.toPoly.roots, toPoly
-/
def roots [IsDomain R] (P : Cubic R) : Multiset R :=
  P.toPoly.roots

/--
theorem `map_roots` / 定理 `map_roots`

English:
theorem map_roots
  given: [IsDomain S]
  statement: (map φ P).roots = (Polynomial.map φ P.toPoly).roots
  proof: by
  rw [roots]; rw [map_toPoly]

中文:
定理 map_roots
  条件: [IsDomain S]
  结论: (map φ P).roots = (Polynomial.map φ P.toPoly).roots
  证明: by
  rw [roots]; rw [map_toPoly]

Depends on / 依赖: map_toPoly
-/
theorem map_roots [IsDomain S] : (map φ P).roots = (Polynomial.map φ P.toPoly).roots := by
  rw [roots]; rw [map_toPoly]

/--
theorem `mem_roots_iff` / 定理 `mem_roots_iff`

English:
theorem mem_roots_iff
  given: [IsDomain R] (h0 : P.toPoly != 0) (x : R)
  proof: by
  rw [roots]; rw [mem_roots h0]; rw [IsRoot]; rw [toPoly]
  simp only [eval_C, eval_X, eval_add, eval_mul, eval_pow]

中文:
定理 mem_roots_iff
  条件: [IsDomain R] (h0 : P.toPoly != 0) (x : R)
  证明: by
  rw [roots]; rw [mem_roots h0]; rw [IsRoot]; rw [toPoly]
  simp only [eval_C, eval_X, eval_add, eval_mul, eval_pow]

Depends on / 依赖: IsRoot, eval_C, eval_X, eval_add, eval_mul, eval_pow, mem_roots, toPoly
-/
theorem mem_roots_iff [IsDomain R] (h0 : P.toPoly != 0) (x : R) :
    x in P.roots ↔ P.a * x ^ 3 + P.b * x ^ 2 + P.c * x + P.d = 0 := by
  rw [roots]; rw [mem_roots h0]; rw [IsRoot]; rw [toPoly]
  simp only [eval_C, eval_X, eval_add, eval_mul, eval_pow]

/--
theorem `card_roots_le` / 定理 `card_roots_le`

English:
theorem card_roots_le
  given: [IsDomain R] [DecidableEq R]
  statement: P.roots.toFinset.card <= 3
  proof: by
  apply (toFinset_card_le P.toPoly.roots).trans
  by_cases hP : P.toPoly = 0
  · simp [hP]
  · exact WithBot.coe_le_coe.1 ((card_roots hP).trans degree_cubic_le)

中文:
定理 card_roots_le
  条件: [IsDomain R] [DecidableEq R]
  结论: P.roots.toFinset.card <= 3
  证明: by
  apply (toFinset_card_le P.toPoly.roots).trans
  by_cases hP : P.toPoly = 0
  · simp [hP]
  · exact WithBot.coe_le_coe.1 ((card_roots hP).trans degree_cubic_le)

Depends on / 依赖: P.toPoly, P.toPoly.roots, WithBot, WithBot.coe_le_coe, card_roots, coe_le_coe, degree_cubic_le, toFinset_card_le, toPoly
-/
theorem card_roots_le [IsDomain R] [DecidableEq R] : P.roots.toFinset.card <= 3 := by
  apply (toFinset_card_le P.toPoly.roots).trans
  by_cases hP : P.toPoly = 0
  · simp [hP]
  · exact WithBot.coe_le_coe.1 ((card_roots hP).trans degree_cubic_le)

end Extension

variable {P : Cubic F} [Field F] [Field K] {φ : F ->+* K} {x y z : K}

/-! ### Roots over a splitting field -/


section Split

/--
theorem `splits_iff_card_roots` / 定理 `splits_iff_card_roots`

English:
theorem splits_iff_card_roots
  given: (ha : P.a != 0)
  proof: by
  replace ha : (map φ P).a != 0 := (map_ne_zero φ).mpr ha
  rw [roots]; rw [← map_toPoly]; rw [Polynomial.splits_iff_card_roots]; rw [← ((degree_eq_iff_natDegree_eq <| ne_zero_of_a_ne_zero ha).1 <| degree_of_a_ne_zero ha : _ = 3)]

中文:
定理 splits_iff_card_roots
  条件: (ha : P.a != 0)
  证明: by
  replace ha : (map φ P).a != 0 := (map_ne_zero φ).mpr ha
  rw [roots]; rw [← map_toPoly]; rw [Polynomial.splits_iff_card_roots]; rw [← ((degree_eq_iff_natDegree_eq <| ne_zero_of_a_ne_zero ha).1 <| degree_of_a_ne_zero ha : _ = 3)]

Depends on / 依赖: Polynomial, Polynomial.splits_iff_card_roots, degree_eq_iff_natDegree_eq, degree_of_a_ne_zero, map_ne_zero, map_toPoly, ne_zero_of_a_ne_zero, replace, splits_iff_card_roots
-/
theorem splits_iff_card_roots (ha : P.a != 0) :
    Splits (P.toPoly.map φ) ↔ (map φ P).roots.card = 3 := by
  replace ha : (map φ P).a != 0 := (map_ne_zero φ).mpr ha
  rw [roots]; rw [← map_toPoly]; rw [Polynomial.splits_iff_card_roots]; rw [← ((degree_eq_iff_natDegree_eq <| ne_zero_of_a_ne_zero ha).1 <| degree_of_a_ne_zero ha : _ = 3)]

/--
theorem `splits_iff_roots_eq_three` / 定理 `splits_iff_roots_eq_three`

English:
theorem splits_iff_roots_eq_three
  given: (ha : P.a != 0)
  proof: by
  rw [splits_iff_card_roots ha]; rw [card_eq_three]

中文:
定理 splits_iff_roots_eq_three
  条件: (ha : P.a != 0)
  证明: by
  rw [splits_iff_card_roots ha]; rw [card_eq_three]

Depends on / 依赖: card_eq_three, splits_iff_card_roots
-/
theorem splits_iff_roots_eq_three (ha : P.a != 0) :
    Splits (P.toPoly.map φ) ↔ exists x y z : K, (map φ P).roots = {x, y, z} := by
  rw [splits_iff_card_roots ha]; rw [card_eq_three]

/--
theorem `eq_prod_three_roots` / 定理 `eq_prod_three_roots`

English:
theorem eq_prod_three_roots
  given: (ha : P.a != 0) (h3 : (map φ P).roots = {x, y, z})
  proof: by
  rw [map_toPoly]; rw [Splits.eq_prod_roots
(splits_iff_roots_eq_three ha).mpr Exists.intro x Exists.intro y Exists.intro z h3]; rw [leadingCoeff_map]; rw [leadingCoeff_of_a_ne_zero ha]; rw [← map_roots]; rw [h3]
  change C (φ P.a) * ((X - C x) ::ₘ (X - C y) ::ₘ {X - C z}).prod = _
  rw [prod_con

中文:
定理 eq_prod_three_roots
  条件: (ha : P.a != 0) (h3 : (map φ P).roots = {x, y, z})
  证明: by
  rw [map_toPoly]; rw [Splits.eq_prod_roots
(splits_iff_roots_eq_three ha).mpr Exists.intro x Exists.intro y Exists.intro z h3]; rw [leadingCoeff_map]; rw [leadingCoeff_of_a_ne_zero ha]; rw [← map_roots]; rw [h3]
  change C (φ P.a) * ((X - C x) ::ₘ (X - C y) ::ₘ {X - C z}).prod = _
  rw [prod_con

Depends on / 依赖: Exists, Exists.intro, Splits, Splits.eq_prod_roots, eq_prod_roots, leadingCoeff_map, leadingCoeff_of_a_ne_zero, map_roots, map_toPoly, mul_assoc, prod_cons, prod_singleton, splits_iff_roots_eq_three
-/
theorem eq_prod_three_roots (ha : P.a != 0) (h3 : (map φ P).roots = {x, y, z}) :
    (map φ P).toPoly = C (φ P.a) * (X - C x) * (X - C y) * (X - C z) := by
  rw [map_toPoly]; rw [Splits.eq_prod_roots
(splits_iff_roots_eq_three ha).mpr Exists.intro x Exists.intro y Exists.intro z h3]; rw [leadingCoeff_map]; rw [leadingCoeff_of_a_ne_zero ha]; rw [← map_roots]; rw [h3]
  change C (φ P.a) * ((X - C x) ::ₘ (X - C y) ::ₘ {X - C z}).prod = _
  rw [prod_cons]; rw [prod_cons]; rw [prod_singleton]; rw [mul_assoc]; rw [mul_assoc]

/--
theorem `eq_sum_three_roots` / 定理 `eq_sum_three_roots`

English:
theorem eq_sum_three_roots
  given: (ha : P.a != 0) (h3 : (map φ P).roots = {x, y, z})
  proof: by
  apply_fun toPoly
  · rw [eq_prod_three_roots ha h3, C_mul_prod_X_sub_C_eq]
  · exact fun P Q => (toPoly_injective P Q).mp

中文:
定理 eq_sum_three_roots
  条件: (ha : P.a != 0) (h3 : (map φ P).roots = {x, y, z})
  证明: by
  apply_fun toPoly
  · rw [eq_prod_three_roots ha h3, C_mul_prod_X_sub_C_eq]
  · exact fun P Q => (toPoly_injective P Q).mp

Depends on / 依赖: C_mul_prod_X_sub_C_eq, apply_fun, eq_prod_three_roots, toPoly, toPoly_injective
-/
theorem eq_sum_three_roots (ha : P.a != 0) (h3 : (map φ P).roots = {x, y, z}) :
    map φ P =
      ⟨φ P.a, φ P.a * -(x + y + z), φ P.a * (x * y + x * z + y * z), φ P.a * -(x * y * z)⟩ := by
  apply_fun toPoly
  · rw [eq_prod_three_roots ha h3, C_mul_prod_X_sub_C_eq]
  · exact fun P Q => (toPoly_injective P Q).mp

/--
theorem `b_eq_three_roots` / 定理 `b_eq_three_roots`

English:
theorem b_eq_three_roots
  given: (ha : P.a != 0) (h3 : (map φ P).roots = {x, y, z})
  proof: by
  injection eq_sum_three_roots ha h3

中文:
定理 b_eq_three_roots
  条件: (ha : P.a != 0) (h3 : (map φ P).roots = {x, y, z})
  证明: by
  injection eq_sum_three_roots ha h3

Depends on / 依赖: eq_sum_three_roots, injection
-/
theorem b_eq_three_roots (ha : P.a != 0) (h3 : (map φ P).roots = {x, y, z}) :
    φ P.b = φ P.a * -(x + y + z) := by
  injection eq_sum_three_roots ha h3

/--
theorem `c_eq_three_roots` / 定理 `c_eq_three_roots`

English:
theorem c_eq_three_roots
  given: (ha : P.a != 0) (h3 : (map φ P).roots = {x, y, z})
  proof: by
  injection eq_sum_three_roots ha h3

中文:
定理 c_eq_three_roots
  条件: (ha : P.a != 0) (h3 : (map φ P).roots = {x, y, z})
  证明: by
  injection eq_sum_three_roots ha h3

Depends on / 依赖: eq_sum_three_roots, injection
-/
theorem c_eq_three_roots (ha : P.a != 0) (h3 : (map φ P).roots = {x, y, z}) :
    φ P.c = φ P.a * (x * y + x * z + y * z) := by
  injection eq_sum_three_roots ha h3

/--
theorem `d_eq_three_roots` / 定理 `d_eq_three_roots`

English:
theorem d_eq_three_roots
  given: (ha : P.a != 0) (h3 : (map φ P).roots = {x, y, z})
  proof: by
  injection eq_sum_three_roots ha h3

中文:
定理 d_eq_three_roots
  条件: (ha : P.a != 0) (h3 : (map φ P).roots = {x, y, z})
  证明: by
  injection eq_sum_three_roots ha h3

Depends on / 依赖: eq_sum_three_roots, injection
-/
theorem d_eq_three_roots (ha : P.a != 0) (h3 : (map φ P).roots = {x, y, z}) :
    φ P.d = φ P.a * -(x * y * z) := by
  injection eq_sum_three_roots ha h3

end Split

/-! ### Discriminant over a splitting field -/


section Discriminant

/--
Definition of `discr` / `discr` 的定义

English:
definition discr
  signature: {R : Type*} [Ring R] (P : Cubic R)
  body: P.b ^ 2 * P.c ^ 2 - 4 * P.a * P.c ^ 3 - 4 * P.b ^ 3 * P.d - 27 * P.a ^ 2 * P.d ^ 2 +
    18 * P.a * P.b * P.c * P.d

中文:
定义 discr
  签名: {R : 类型} [Ring R] (P : Cubic R)
  定义体: P.b ^ 2 * P.c ^ 2 - 4 * P.a * P.c ^ 3 - 4 * P.b ^ 3 * P.d - 27 * P.a ^ 2 * P.d ^ 2 +
    18 * P.a * P.b * P.c * P.d
-/
def discr {R : Type*} [Ring R] (P : Cubic R) : R :=
  P.b ^ 2 * P.c ^ 2 - 4 * P.a * P.c ^ 3 - 4 * P.b ^ 3 * P.d - 27 * P.a ^ 2 * P.d ^ 2 +
    18 * P.a * P.b * P.c * P.d

/--
theorem `discr_eq_prod_three_roots` / 定理 `discr_eq_prod_three_roots`

English:
theorem discr_eq_prod_three_roots
  given: (ha : P.a != 0) (h3 : (map φ P).roots = {x, y, z})
  proof: by
  simp only [discr, RingHom.map_add, map_sub, map_mul, map_pow, map_ofNat]
  rw [b_eq_three_roots ha h3]; rw [c_eq_three_roots ha h3]; rw [d_eq_three_roots ha h3]
  ring1

中文:
定理 discr_eq_prod_three_roots
  条件: (ha : P.a != 0) (h3 : (map φ P).roots = {x, y, z})
  证明: by
  simp only [discr, RingHom.map_add, map_sub, map_mul, map_pow, map_ofNat]
  rw [b_eq_three_roots ha h3]; rw [c_eq_three_roots ha h3]; rw [d_eq_three_roots ha h3]
  ring1

Depends on / 依赖: RingHom, RingHom.map_add, b_eq_three_roots, c_eq_three_roots, d_eq_three_roots, map_add, map_mul, map_ofNat, map_pow, map_sub
-/
theorem discr_eq_prod_three_roots (ha : P.a != 0) (h3 : (map φ P).roots = {x, y, z}) :
    φ P.discr = (φ P.a * φ P.a * (x - y) * (x - z) * (y - z)) ^ 2 := by
  simp only [discr, RingHom.map_add, map_sub, map_mul, map_pow, map_ofNat]
  rw [b_eq_three_roots ha h3]; rw [c_eq_three_roots ha h3]; rw [d_eq_three_roots ha h3]
  ring1

/--
theorem `discr_ne_zero_iff_roots_ne` / 定理 `discr_ne_zero_iff_roots_ne`

English:
theorem discr_ne_zero_iff_roots_ne
  given: (ha : P.a != 0) (h3 : (map φ P).roots = {x, y, z})
  proof: by
  rw [← map_ne_zero φ]; rw [discr_eq_prod_three_roots ha h3]; rw [pow_two]
  simp_rw [mul_ne_zero_iff, sub_ne_zero, _root_.map_ne_zero, and_self_iff, and_iff_right ha,
    and_assoc]

中文:
定理 discr_ne_zero_iff_roots_ne
  条件: (ha : P.a != 0) (h3 : (map φ P).roots = {x, y, z})
  证明: by
  rw [← map_ne_zero φ]; rw [discr_eq_prod_three_roots ha h3]; rw [pow_two]
  simp_rw [mul_ne_zero_iff, sub_ne_zero, _root_.map_ne_zero, and_self_iff, and_iff_right ha,
    and_assoc]

Depends on / 依赖: _root_, _root_.map_ne_zero, and_assoc, and_iff_right, and_self_iff, discr_eq_prod_three_roots, map_ne_zero, mul_ne_zero_iff, pow_two, simp_rw, sub_ne_zero
-/
theorem discr_ne_zero_iff_roots_ne (ha : P.a != 0) (h3 : (map φ P).roots = {x, y, z}) :
    P.discr != 0 ↔ x != y ∧ x != z ∧ y != z := by
  rw [← map_ne_zero φ]; rw [discr_eq_prod_three_roots ha h3]; rw [pow_two]
  simp_rw [mul_ne_zero_iff, sub_ne_zero, _root_.map_ne_zero, and_self_iff, and_iff_right ha,
    and_assoc]

/--
theorem `discr_ne_zero_iff_roots_nodup` / 定理 `discr_ne_zero_iff_roots_nodup`

English:
theorem discr_ne_zero_iff_roots_nodup
  given: (ha : P.a != 0) (hP : (P.toPoly.map φ).Splits)
  proof: by
  have ⟨x, y, z, h3⟩ := (splits_iff_roots_eq_three ha).mp hP
  rw [discr_ne_zero_iff_roots_ne ha h3]; rw [h3]
  change _ ↔ (x ::ₘ y ::ₘ {z}).Nodup
  rw [nodup_cons]; rw [nodup_cons]; rw [mem_cons]; rw [mem_singleton]; rw [mem_singleton]
  simp only [nodup_singleton]
  tauto

中文:
定理 discr_ne_zero_iff_roots_nodup
  条件: (ha : P.a != 0) (hP : (P.toPoly.map φ).Splits)
  证明: by
  have ⟨x, y, z, h3⟩ := (splits_iff_roots_eq_three ha).mp hP
  rw [discr_ne_zero_iff_roots_ne ha h3]; rw [h3]
  change _ ↔ (x ::ₘ y ::ₘ {z}).Nodup
  rw [nodup_cons]; rw [nodup_cons]; rw [mem_cons]; rw [mem_singleton]; rw [mem_singleton]
  simp only [nodup_singleton]
  tauto

Depends on / 依赖: discr_ne_zero_iff_roots_ne, mem_cons, mem_singleton, nodup_cons, nodup_singleton, splits_iff_roots_eq_three
-/
theorem discr_ne_zero_iff_roots_nodup (ha : P.a != 0) (hP : (P.toPoly.map φ).Splits) :
    P.discr != 0 ↔ (map φ P).roots.Nodup := by
  have ⟨x, y, z, h3⟩ := (splits_iff_roots_eq_three ha).mp hP
  rw [discr_ne_zero_iff_roots_ne ha h3]; rw [h3]
  change _ ↔ (x ::ₘ y ::ₘ {z}).Nodup
  rw [nodup_cons]; rw [nodup_cons]; rw [mem_cons]; rw [mem_singleton]; rw [mem_singleton]
  simp only [nodup_singleton]
  tauto

/--
theorem `card_roots_of_discr_ne_zero` / 定理 `card_roots_of_discr_ne_zero`

English:
theorem card_roots_of_discr_ne_zero
  statement: [DecidableEq K] (ha : P.a != 0) (h3 : (P.toPoly.map φ).Splits)
  proof: by
  rwa [toFinset_card_of_nodup <| (discr_ne_zero_iff_roots_nodup ha h3).mp hd,
    ← splits_iff_card_roots ha]

中文:
定理 card_roots_of_discr_ne_zero
  结论: [DecidableEq K] (ha : P.a != 0) (h3 : (P.toPoly.map φ).Splits)
  证明: by
  rwa [toFinset_card_of_nodup <| (discr_ne_zero_iff_roots_nodup ha h3).mp hd,
    ← splits_iff_card_roots ha]

Depends on / 依赖: discr_ne_zero_iff_roots_nodup, splits_iff_card_roots, toFinset_card_of_nodup
-/
theorem card_roots_of_discr_ne_zero [DecidableEq K] (ha : P.a != 0) (h3 : (P.toPoly.map φ).Splits)
    (hd : P.discr != 0) : (map φ P).roots.toFinset.card = 3 := by
  rwa [toFinset_card_of_nodup <| (discr_ne_zero_iff_roots_nodup ha h3).mp hd,
    ← splits_iff_card_roots ha]

end Discriminant

end Roots

end Cubic
