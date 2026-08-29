/-
Copyright (c) 2024 Jineon Baek and Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jineon Baek, Seewoo Lee
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import Mathlib.RingTheory.Coprime.Basic

/-!
# Wronskian of a pair of polynomial

This file defines Wronskian of a pair of polynomials, which is `W(a, b) = ab' - a'b`.
We also prove basic properties of it.

## Main declarations

- `Polynomial.wronskian_eq_of_sum_zero`: We have `W(a, b) = W(b, c)` when `a + b + c = 0`.
- `Polynomial.degree_wronskian_lt_add`: Degree of Wronskian `W(a, b)` is strictly smaller than
  the sum of degrees of `a` and `b`
- `Polynomial.natDegree_wronskian_lt_add`: `natDegree` version of the above theorem.
  We need to assume that the Wronskian is nonzero. (Otherwise, `a = b = 1` gives a counterexample.)

## TODO

- Define Wronskian for n-tuple of polynomials, not necessarily two.
-/

@[expose] public section

noncomputable section

open scoped Polynomial

namespace Polynomial

variable {R : Type*} [CommRing R]

/--
Definition of `wronskian` / `wronskian` 的定义

English:
definition wronskian
  signature: (a b : R[X])
  body: a * (derivative b) - (derivative a) * b

中文:
定义 wronskian
  签名: (a b : R[X])
  定义体: a * (derivative b) - (derivative a) * b

Depends on / 依赖: derivative
-/
def wronskian (a b : R[X]) : R[X] :=
  a * (derivative b) - (derivative a) * b

variable (R) in
/--
Definition of `wronskianBilin` / `wronskianBilin` 的定义

English:
definition wronskianBilin
  signature: : R[X] ->ₗ[R] R[X] ->ₗ[R] R[X]
  body: (LinearMap.mul R R[X]).compl₂ derivative - (LinearMap.mul R R[X]).comp derivative

@[simp]

中文:
定义 wronskianBilin
  签名: : R[X] ->ₗ[R] R[X] ->ₗ[R] R[X]
  定义体: (LinearMap.mul R R[X]).compl₂ derivative - (LinearMap.mul R R[X]).comp derivative

@[simp]

Depends on / 依赖: LinearMap, LinearMap.mul, derivative
-/
def wronskianBilin : R[X] ->ₗ[R] R[X] ->ₗ[R] R[X] :=
  (LinearMap.mul R R[X]).compl₂ derivative - (LinearMap.mul R R[X]).comp derivative

@[simp]
/--
theorem `wronskianBilin_apply` / 定理 `wronskianBilin_apply`

English:
theorem wronskianBilin_apply
  given: (a b : R[X])
  statement: wronskianBilin R a b = wronskian a b
  proof: rfl

@[simp]

中文:
定理 wronskianBilin_apply
  条件: (a b : R[X])
  结论: wronskianBilin R a b = wronskian a b
  证明: rfl

@[simp]

Depends on / 依赖: CompletableTopField, completable
-/
theorem wronskianBilin_apply (a b : R[X]) : wronskianBilin R a b = wronskian a b := rfl

@[simp]
/--
theorem `wronskian_zero_left` / 定理 `wronskian_zero_left`

English:
theorem wronskian_zero_left
  given: (a : R[X])
  statement: wronskian 0 a = 0
  proof: by
  rw [← wronskianBilin_apply 0 a]; rw [map_zero]; rfl

@[simp]

中文:
定理 wronskian_zero_left
  条件: (a : R[X])
  结论: wronskian 0 a = 0
  证明: by
  rw [← wronskianBilin_apply 0 a]; rw [map_zero]; rfl

@[simp]

Depends on / 依赖: map_zero, wronskianBilin_apply
-/
theorem wronskian_zero_left (a : R[X]) : wronskian 0 a = 0 := by
  rw [← wronskianBilin_apply 0 a]; rw [map_zero]; rfl

@[simp]
/--
theorem `wronskian_zero_right` / 定理 `wronskian_zero_right`

English:
theorem wronskian_zero_right
  given: (a : R[X])
  statement: wronskian a 0 = 0
  proof: (wronskianBilin R a).map_zero

中文:
定理 wronskian_zero_right
  条件: (a : R[X])
  结论: wronskian a 0 = 0
  证明: (wronskianBilin R a).map_zero

Depends on / 依赖: map_zero, wronskianBilin
-/
theorem wronskian_zero_right (a : R[X]) : wronskian a 0 = 0 := (wronskianBilin R a).map_zero

/--
theorem `wronskian_neg_left` / 定理 `wronskian_neg_left`

English:
theorem wronskian_neg_left
  given: (a b : R[X])
  statement: wronskian (-a) b = -wronskian a b
  proof: LinearMap.map_neg₂ (wronskianBilin R) a b

中文:
定理 wronskian_neg_left
  条件: (a b : R[X])
  结论: wronskian (-a) b = -wronskian a b
  证明: LinearMap.map_neg₂ (wronskianBilin R) a b

Depends on / 依赖: LinearMap, LinearMap.map_neg, wronskianBilin
-/
theorem wronskian_neg_left (a b : R[X]) : wronskian (-a) b = -wronskian a b :=
  LinearMap.map_neg₂ (wronskianBilin R) a b

/--
theorem `wronskian_neg_right` / 定理 `wronskian_neg_right`

English:
theorem wronskian_neg_right
  given: (a b : R[X])
  statement: wronskian a (-b) = -wronskian a b
  proof: (wronskianBilin R a).map_neg b

中文:
定理 wronskian_neg_right
  条件: (a b : R[X])
  结论: wronskian a (-b) = -wronskian a b
  证明: (wronskianBilin R a).map_neg b

Depends on / 依赖: map_neg, wronskianBilin
-/
theorem wronskian_neg_right (a b : R[X]) : wronskian a (-b) = -wronskian a b :=
  (wronskianBilin R a).map_neg b

/--
theorem `wronskian_add_right` / 定理 `wronskian_add_right`

English:
theorem wronskian_add_right
  given: (a b c : R[X])
  statement: wronskian a (b + c) = wronskian a b + wronskian a c
  proof: (wronskianBilin R a).map_add b c

中文:
定理 wronskian_add_right
  条件: (a b c : R[X])
  结论: wronskian a (b + c) = wronskian a b + wronskian a c
  证明: (wronskianBilin R a).map_add b c

Depends on / 依赖: map_add, wronskianBilin
-/
theorem wronskian_add_right (a b c : R[X]) : wronskian a (b + c) = wronskian a b + wronskian a c :=
  (wronskianBilin R a).map_add b c

/--
theorem `wronskian_add_left` / 定理 `wronskian_add_left`

English:
theorem wronskian_add_left
  given: (a b c : R[X])
  statement: wronskian (a + b) c = wronskian a c + wronskian b c
  proof: (wronskianBilin R).map_add₂ a b c

中文:
定理 wronskian_add_left
  条件: (a b c : R[X])
  结论: wronskian (a + b) c = wronskian a c + wronskian b c
  证明: (wronskianBilin R).map_add₂ a b c

Depends on / 依赖: wronskianBilin
-/
theorem wronskian_add_left (a b c : R[X]) : wronskian (a + b) c = wronskian a c + wronskian b c :=
  (wronskianBilin R).map_add₂ a b c

/--
theorem `wronskian_self_eq_zero` / 定理 `wronskian_self_eq_zero`

English:
theorem wronskian_self_eq_zero
  given: (a : R[X])
  statement: wronskian a a = 0
  proof: by
  rw [wronskian]; rw [mul_comm]; rw [sub_self]

中文:
定理 wronskian_self_eq_zero
  条件: (a : R[X])
  结论: wronskian a a = 0
  证明: by
  rw [wronskian]; rw [mul_comm]; rw [sub_self]

Depends on / 依赖: mul_comm, sub_self, wronskian
-/
theorem wronskian_self_eq_zero (a : R[X]) : wronskian a a = 0 := by
  rw [wronskian]; rw [mul_comm]; rw [sub_self]

/--
theorem `isAlt_wronskianBilin` / 定理 `isAlt_wronskianBilin`

English:
theorem isAlt_wronskianBilin
  statement: (wronskianBilin R).IsAlt
  proof: wronskian_self_eq_zero

中文:
定理 isAlt_wronskianBilin
  结论: (wronskianBilin R).IsAlt
  证明: wronskian_self_eq_zero

Depends on / 依赖: wronskian_self_eq_zero
-/
theorem isAlt_wronskianBilin : (wronskianBilin R).IsAlt := wronskian_self_eq_zero

/--
theorem `wronskian_neg_eq` / 定理 `wronskian_neg_eq`

English:
theorem wronskian_neg_eq
  given: (a b : R[X])
  statement: -wronskian a b = wronskian b a
  proof: LinearMap.IsAlt.neg isAlt_wronskianBilin a b

中文:
定理 wronskian_neg_eq
  条件: (a b : R[X])
  结论: -wronskian a b = wronskian b a
  证明: LinearMap.IsAlt.neg isAlt_wronskianBilin a b

Depends on / 依赖: LinearMap, LinearMap.IsAlt.neg, isAlt_wronskianBilin
-/
theorem wronskian_neg_eq (a b : R[X]) : -wronskian a b = wronskian b a :=
  LinearMap.IsAlt.neg isAlt_wronskianBilin a b

/--
theorem `wronskian_eq_of_sum_zero` / 定理 `wronskian_eq_of_sum_zero`

English:
theorem wronskian_eq_of_sum_zero
  given: {a b c : R[X]} (hAdd : a + b + c = 0)
  proof: isAlt_wronskianBilin.eq_of_add_add_eq_zero hAdd

中文:
定理 wronskian_eq_of_sum_zero
  条件: {a b c : R[X]} (hAdd : a + b + c = 0)
  证明: isAlt_wronskianBilin.eq_of_add_add_eq_zero hAdd

Depends on / 依赖: eq_of_add_add_eq_zero, isAlt_wronskianBilin, isAlt_wronskianBilin.eq_of_add_add_eq_zero
-/
theorem wronskian_eq_of_sum_zero {a b c : R[X]} (hAdd : a + b + c = 0) :
    wronskian a b = wronskian b c := isAlt_wronskianBilin.eq_of_add_add_eq_zero hAdd

/--
theorem `degree_wronskian_lt_add` / 定理 `degree_wronskian_lt_add`

English:
theorem degree_wronskian_lt_add
  given: {a b : R[X]} (ha : a != 0) (hb : b != 0)
  proof: by
  calc
    (wronskian a b).degree <= max (a * derivative b).degree (derivative a * b).degree :=
      Polynomial.degree_sub_le _ _
    _ < a.degree + b.degree := by
      rw [max_lt_iff]
      constructor
      case left =>
        apply lt_of_le_of_lt
        · exact degree_mul_le a (derivative 

中文:
定理 degree_wronskian_lt_add
  条件: {a b : R[X]} (ha : a != 0) (hb : b != 0)
  证明: by
  calc
    (wronskian a b).degree <= max (a * derivative b).degree (derivative a * b).degree :=
      Polynomial.degree_sub_le _ _
    _ < a.degree + b.degree := by
      rw [max_lt_iff]
      constructor
      case left =>
        apply lt_of_le_of_lt
        · exact degree_mul_le a (derivative 

Depends on / 依赖: Polynomial, Polynomial.degree_derivative_lt, Polynomial.degree_ne_bot, Polynomial.degree_sub_le, WithBot, WithBot.add_, WithBot.add_lt_add_iff_left, a.degree, add_, add_lt_add_iff_left, b.degree, degree, degree_derivative_lt, degree_mul_le, degree_ne_bot, degree_sub_le, derivative, lt_of_le_of_lt, max_lt_iff, wronskian
-/
theorem degree_wronskian_lt_add {a b : R[X]} (ha : a != 0) (hb : b != 0) :
    (wronskian a b).degree < a.degree + b.degree := by
  calc
    (wronskian a b).degree <= max (a * derivative b).degree (derivative a * b).degree :=
      Polynomial.degree_sub_le _ _
    _ < a.degree + b.degree := by
      rw [max_lt_iff]
      constructor
      case left =>
        apply lt_of_le_of_lt
        · exact degree_mul_le a (derivative b)
        · rw [← Polynomial.degree_ne_bot] at ha
          rw [WithBot.add_lt_add_iff_left ha]
          exact Polynomial.degree_derivative_lt hb
      case right =>
        apply lt_of_le_of_lt
        · exact degree_mul_le (derivative a) b
        · rw [← Polynomial.degree_ne_bot] at hb
          rw [WithBot.add_lt_add_iff_right hb]
          exact Polynomial.degree_derivative_lt ha

/--
theorem `natDegree_wronskian_lt_add` / 定理 `natDegree_wronskian_lt_add`

English:
theorem natDegree_wronskian_lt_add
  given: {a b : R[X]} (hw : wronskian a b != 0)
  proof: by
  have ha : a != 0 := by intro h; subst h; rw [wronskian_zero_left] at hw; exact hw rfl
  have hb : b != 0 := by intro h; subst h; rw [wronskian_zero_right] at hw; exact hw rfl
  rw [← WithBot.coe_lt_coe]; rw [WithBot.coe_add]
  convert! ← degree_wronskian_lt_add ha hb
  · exact Polynomial.degree

中文:
定理 natDegree_wronskian_lt_add
  条件: {a b : R[X]} (hw : wronskian a b != 0)
  证明: by
  have ha : a != 0 := by intro h; subst h; rw [wronskian_zero_left] at hw; exact hw rfl
  have hb : b != 0 := by intro h; subst h; rw [wronskian_zero_right] at hw; exact hw rfl
  rw [← WithBot.coe_lt_coe]; rw [WithBot.coe_add]
  convert! ← degree_wronskian_lt_add ha hb
  · exact Polynomial.degree

Depends on / 依赖: Polynomial, Polynomial.degree_eq_natDegree, WithBot, WithBot.coe_add, WithBot.coe_lt_coe, coe_add, coe_lt_coe, convert, degree_eq_natDegree, degree_wronskian_lt_add, wronskian_zero_left, wronskian_zero_right
-/
theorem natDegree_wronskian_lt_add {a b : R[X]} (hw : wronskian a b != 0) :
    (wronskian a b).natDegree < a.natDegree + b.natDegree := by
  have ha : a != 0 := by intro h; subst h; rw [wronskian_zero_left] at hw; exact hw rfl
  have hb : b != 0 := by intro h; subst h; rw [wronskian_zero_right] at hw; exact hw rfl
  rw [← WithBot.coe_lt_coe]; rw [WithBot.coe_add]
  convert! ← degree_wronskian_lt_add ha hb
  · exact Polynomial.degree_eq_natDegree hw
  · exact Polynomial.degree_eq_natDegree ha
  · exact Polynomial.degree_eq_natDegree hb

/--
theorem `_root_.IsCoprime.wronskian_eq_zero_iff` / 定理 `_root_.IsCoprime.wronskian_eq_zero_iff`

English:
theorem _root_.IsCoprime.wronskian_eq_zero_iff
  proof: by
    rw [wronskian]; rw [sub_eq_iff_eq_add]; rw [zero_add] at hw
    constructor
    · rw [← dvd_derivative_iff]
      apply hc.dvd_of_dvd_mul_right
      rw [← hw]; exact dvd_mul_right _ _
    · rw [← dvd_derivative_iff]
      apply hc.symm.dvd_of_dvd_mul_left
      rw [hw]; exact dvd_mul_left _ 

中文:
定理 _root_.IsCoprime.wronskian_eq_zero_iff
  证明: by
    rw [wronskian]; rw [sub_eq_iff_eq_add]; rw [zero_add] at hw
    constructor
    · rw [← dvd_derivative_iff]
      apply hc.dvd_of_dvd_mul_right
      rw [← hw]; exact dvd_mul_right _ _
    · rw [← dvd_derivative_iff]
      apply hc.symm.dvd_of_dvd_mul_left
      rw [hw]; exact dvd_mul_left _ 

Depends on / 依赖: dvd_derivative_iff, dvd_mul_left, dvd_mul_right, dvd_of_dvd_mul_left, dvd_of_dvd_mul_right, hc.dvd_of_dvd_mul_right, hc.symm.dvd_of_dvd_mul_left, mul_zero, sub_eq_iff_eq_add, sub_self, wronskian, zero_add, zero_mul
-/
theorem _root_.IsCoprime.wronskian_eq_zero_iff
    [NoZeroDivisors R] {a b : R[X]} (hc : IsCoprime a b) :
    wronskian a b = 0 ↔ derivative a = 0 ∧ derivative b = 0 where
  mp hw := by
    rw [wronskian]; rw [sub_eq_iff_eq_add]; rw [zero_add] at hw
    constructor
    · rw [← dvd_derivative_iff]
      apply hc.dvd_of_dvd_mul_right
      rw [← hw]; exact dvd_mul_right _ _
    · rw [← dvd_derivative_iff]
      apply hc.symm.dvd_of_dvd_mul_left
      rw [hw]; exact dvd_mul_left _ _
  mpr hdab := by
    obtain ⟨hda, hdb⟩ := hdab
    rw [wronskian]
    rw [hda]; rw [hdb]; simp only [mul_zero, zero_mul, sub_self]

end Polynomial
