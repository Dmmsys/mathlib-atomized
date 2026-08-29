/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Ken Lee, Chris Hughes
-/
module

public import Mathlib.Algebra.Group.Action.Units
public import Mathlib.Algebra.Group.Nat.Units
public import Mathlib.Algebra.GroupWithZero.Associated
public import Mathlib.Algebra.Ring.Divisibility.Basic
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Logic.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Tactic.Ring

/-!
# Coprime elements of a ring or monoid

## Main definition

* `IsCoprime x y`: that `x` and `y` are coprime, defined to be the existence of `a` and `b` such
  that `a * x + b * y = 1`. Note that elements with no common divisors (`IsRelPrime`) are not
  necessarily coprime, e.g., the multivariate polynomials `x₁` and `x₂` are not coprime.
  The two notions are equivalent in Bézout rings, see `isRelPrime_iff_isCoprime`.

This file also contains lemmas about `IsRelPrime` parallel to `IsCoprime`.

See also `RingTheory.Coprime.Lemmas` for further development of coprime elements.
-/

@[expose] public section


universe u v

section CommSemiring

variable {R : Type u} [CommSemiring R] (x y z w : R)

/-- The proposition that `x` and `y` are coprime, defined to be the existence of `a` and `b` such
that `a * x + b * y = 1`. Note that elements with no common divisors are not necessarily coprime,
e.g., the multivariate polynomials `x₁` and `x₂` are not coprime. -/
@[wikidata Q104752]
/--
Definition of `IsCoprime` / `IsCoprime` 的定义

English:
definition IsCoprime
  signature: : Prop
  body: exists a b, a * x + b * y = 1

中文:
定义 IsCoprime
  签名: : 命题
  定义体: exists a b, a * x + b * y = 1
-/
def IsCoprime : Prop :=
  exists a b, a * x + b * y = 1

variable {x y z w}

@[symm]
/--
theorem `IsCoprime.symm` / 定理 `IsCoprime.symm`

English:
theorem IsCoprime.symm
  given: (H : IsCoprime x y)
  statement: IsCoprime y x
  proof: let ⟨a, b, H⟩ := H
  ⟨b, a, by rw [add_comm, H]⟩

中文:
定理 IsCoprime.symm
  条件: (H : IsCoprime x y)
  结论: IsCoprime y x
  证明: let ⟨a, b, H⟩ := H
  ⟨b, a, by rw [add_comm, H]⟩

Depends on / 依赖: add_comm
-/
theorem IsCoprime.symm (H : IsCoprime x y) : IsCoprime y x :=
  let ⟨a, b, H⟩ := H
  ⟨b, a, by rw [add_comm, H]⟩

/--
theorem `isCoprime_comm` / 定理 `isCoprime_comm`

English:
theorem isCoprime_comm
  statement: IsCoprime x y ↔ IsCoprime y x
  proof: ⟨IsCoprime.symm, IsCoprime.symm⟩

中文:
定理 isCoprime_comm
  结论: IsCoprime x y ↔ IsCoprime y x
  证明: ⟨IsCoprime.symm, IsCoprime.symm⟩

Depends on / 依赖: IsCoprime, IsCoprime.symm
-/
theorem isCoprime_comm : IsCoprime x y ↔ IsCoprime y x :=
  ⟨IsCoprime.symm, IsCoprime.symm⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: @Std.Symm R IsCoprime
  body: .symm

中文:
实例 :
  签名: @Std.Symm R IsCoprime
  定义体: .symm
-/
instance : @Std.Symm R IsCoprime where
  symm _ _ := .symm

/--
theorem `isCoprime_self` / 定理 `isCoprime_self`

English:
theorem isCoprime_self
  statement: IsCoprime x x ↔ IsUnit x
  proof: ⟨fun ⟨a, b, h⟩ => .of_mul_eq_one (a + b) by rwa [mul_comm, add_mul], fun h =>
    let ⟨b, hb⟩ := isUnit_iff_exists_inv'.1 h
    ⟨b, 0, by rwa [zero_mul, add_zero]⟩⟩

中文:
定理 isCoprime_self
  结论: IsCoprime x x ↔ 是单位 x
  证明: ⟨fun ⟨a, b, h⟩ => .of_mul_eq_one (a + b) by rwa [mul_comm, add_mul], fun h =>
    let ⟨b, hb⟩ := isUnit_iff_exists_inv'.1 h
    ⟨b, 0, by rwa [zero_mul, add_zero]⟩⟩

Depends on / 依赖: add_mul, add_zero, isUnit_iff_exists_inv, mul_comm, of_mul_eq_one, zero_mul
-/
theorem isCoprime_self : IsCoprime x x ↔ IsUnit x :=
⟨fun ⟨a, b, h⟩ => .of_mul_eq_one (a + b) by rwa [mul_comm, add_mul], fun h =>
    let ⟨b, hb⟩ := isUnit_iff_exists_inv'.1 h
    ⟨b, 0, by rwa [zero_mul, add_zero]⟩⟩

/--
theorem `isCoprime_zero_left` / 定理 `isCoprime_zero_left`

English:
theorem isCoprime_zero_left
  statement: IsCoprime 0 x ↔ IsUnit x
  proof: ⟨fun ⟨a, b, H⟩ => .of_mul_eq_one b by rwa [mul_zero, zero_add, mul_comm] at H, fun H =>
    let ⟨b, hb⟩ := isUnit_iff_exists_inv'.1 H
    ⟨1, b, by rwa [one_mul, zero_add]⟩⟩

中文:
定理 isCoprime_zero_left
  结论: IsCoprime 0 x ↔ 是单位 x
  证明: ⟨fun ⟨a, b, H⟩ => .of_mul_eq_one b by rwa [mul_zero, zero_add, mul_comm] at H, fun H =>
    let ⟨b, hb⟩ := isUnit_iff_exists_inv'.1 H
    ⟨1, b, by rwa [one_mul, zero_add]⟩⟩

Depends on / 依赖: isUnit_iff_exists_inv, mul_comm, mul_zero, of_mul_eq_one, one_mul, zero_add
-/
theorem isCoprime_zero_left : IsCoprime 0 x ↔ IsUnit x :=
⟨fun ⟨a, b, H⟩ => .of_mul_eq_one b by rwa [mul_zero, zero_add, mul_comm] at H, fun H =>
    let ⟨b, hb⟩ := isUnit_iff_exists_inv'.1 H
    ⟨1, b, by rwa [one_mul, zero_add]⟩⟩

/--
theorem `isCoprime_zero_right` / 定理 `isCoprime_zero_right`

English:
theorem isCoprime_zero_right
  statement: IsCoprime x 0 ↔ IsUnit x
  proof: isCoprime_comm.trans isCoprime_zero_left

中文:
定理 isCoprime_zero_right
  结论: IsCoprime x 0 ↔ 是单位 x
  证明: isCoprime_comm.trans isCoprime_zero_left

Depends on / 依赖: isCoprime_comm, isCoprime_comm.trans, isCoprime_zero_left
-/
theorem isCoprime_zero_right : IsCoprime x 0 ↔ IsUnit x :=
  isCoprime_comm.trans isCoprime_zero_left

/--
theorem `not_isCoprime_zero_zero` / 定理 `not_isCoprime_zero_zero`

English:
theorem not_isCoprime_zero_zero
  given: [Nontrivial R]
  statement: ¬IsCoprime (0 : R) 0
  proof: mt isCoprime_zero_right.mp not_isUnit_zero

中文:
定理 not_isCoprime_zero_zero
  条件: [非平凡 R]
  结论: ¬IsCoprime (0 : R) 0
  证明: mt isCoprime_zero_right.mp not_isUnit_zero

Depends on / 依赖: isCoprime_zero_right, isCoprime_zero_right.mp, not_isUnit_zero
-/
theorem not_isCoprime_zero_zero [Nontrivial R] : ¬IsCoprime (0 : R) 0 :=
  mt isCoprime_zero_right.mp not_isUnit_zero

/--
lemma `IsCoprime.intCast` / 引理 `IsCoprime.intCast`

English:
lemma IsCoprime.intCast
  given: {R : Type*} [CommRing R] {a b : Int} (h : IsCoprime a b)
  proof: by
  rcases h with ⟨u, v, H⟩
  use u, v
  rw_mod_cast [H]
  exact Int.cast_one

中文:
引理 IsCoprime.intCast
  条件: {R : 类型} [交换环 R] {a b : 整数} (h : IsCoprime a b)
  证明: by
  rcases h with ⟨u, v, H⟩
  use u, v
  rw_mod_cast [H]
  exact Int.cast_one

Depends on / 依赖: Int.cast_one, cast_one, rw_mod_cast
-/
lemma IsCoprime.intCast {R : Type*} [CommRing R] {a b : Int} (h : IsCoprime a b) :
    IsCoprime (a : R) (b : R) := by
  rcases h with ⟨u, v, H⟩
  use u, v
  rw_mod_cast [H]
  exact Int.cast_one

/--
theorem `IsCoprime.ne_zero` / 定理 `IsCoprime.ne_zero`

English:
theorem IsCoprime.ne_zero
  given: [Nontrivial R] {p : Fin 2 -> R} (h : IsCoprime (p 0) (p 1))
  statement: p != 0
  proof: by
  rintro rfl
  exact not_isCoprime_zero_zero h

中文:
定理 IsCoprime.ne_zero
  条件: [非平凡 R] {p : 有限集 2 -> R} (h : IsCoprime (p 0) (p 1))
  结论: p != 0
  证明: by
  rintro rfl
  exact not_isCoprime_zero_zero h

Depends on / 依赖: not_isCoprime_zero_zero
-/
theorem IsCoprime.ne_zero [Nontrivial R] {p : Fin 2 -> R} (h : IsCoprime (p 0) (p 1)) : p != 0 := by
  rintro rfl
  exact not_isCoprime_zero_zero h

/--
theorem `IsCoprime.ne_zero_or_ne_zero` / 定理 `IsCoprime.ne_zero_or_ne_zero`

English:
theorem IsCoprime.ne_zero_or_ne_zero
  given: [Nontrivial R] (h : IsCoprime x y)
  statement: x != 0 ∨ y != 0
  proof: by
  apply not_or_of_imp
  rintro rfl rfl
  exact not_isCoprime_zero_zero h

中文:
定理 IsCoprime.ne_zero_or_ne_zero
  条件: [非平凡 R] (h : IsCoprime x y)
  结论: x != 0 ∨ y != 0
  证明: by
  apply not_or_of_imp
  rintro rfl rfl
  exact not_isCoprime_zero_zero h

Depends on / 依赖: not_isCoprime_zero_zero, not_or_of_imp
-/
theorem IsCoprime.ne_zero_or_ne_zero [Nontrivial R] (h : IsCoprime x y) : x != 0 ∨ y != 0 := by
  apply not_or_of_imp
  rintro rfl rfl
  exact not_isCoprime_zero_zero h

/--
theorem `isCoprime_one_left` / 定理 `isCoprime_one_left`

English:
theorem isCoprime_one_left
  statement: IsCoprime 1 x
  proof: ⟨1, 0, by rw [one_mul, zero_mul, add_zero]⟩

中文:
定理 isCoprime_one_left
  结论: IsCoprime 1 x
  证明: ⟨1, 0, by rw [one_mul, zero_mul, add_zero]⟩

Depends on / 依赖: add_zero, one_mul, zero_mul
-/
theorem isCoprime_one_left : IsCoprime 1 x :=
  ⟨1, 0, by rw [one_mul, zero_mul, add_zero]⟩

/--
theorem `isCoprime_one_right` / 定理 `isCoprime_one_right`

English:
theorem isCoprime_one_right
  statement: IsCoprime x 1
  proof: ⟨0, 1, by rw [one_mul, zero_mul, zero_add]⟩

中文:
定理 isCoprime_one_right
  结论: IsCoprime x 1
  证明: ⟨0, 1, by rw [one_mul, zero_mul, zero_add]⟩

Depends on / 依赖: one_mul, zero_add, zero_mul
-/
theorem isCoprime_one_right : IsCoprime x 1 :=
  ⟨0, 1, by rw [one_mul, zero_mul, zero_add]⟩

/--
theorem `IsCoprime.dvd_of_dvd_mul_right` / 定理 `IsCoprime.dvd_of_dvd_mul_right`

English:
theorem IsCoprime.dvd_of_dvd_mul_right
  given: (H1 : IsCoprime x z) (H2 : x ∣ y * z)
  statement: x ∣ y
  proof: by
  let ⟨a, b, H⟩ := H1
  rw [← mul_one y]; rw [← H]; rw [mul_add]; rw [← mul_assoc]; rw [mul_left_comm]
  exact dvd_add (dvd_mul_left _ _) (H2.mul_left _)

中文:
定理 IsCoprime.dvd_of_dvd_mul_right
  条件: (H1 : IsCoprime x z) (H2 : x ∣ y * z)
  结论: x ∣ y
  证明: by
  let ⟨a, b, H⟩ := H1
  rw [← mul_one y]; rw [← H]; rw [mul_add]; rw [← mul_assoc]; rw [mul_left_comm]
  exact dvd_add (dvd_mul_left _ _) (H2.mul_left _)

Depends on / 依赖: H2.mul_left, dvd_add, dvd_mul_left, mul_add, mul_assoc, mul_left, mul_left_comm, mul_one
-/
theorem IsCoprime.dvd_of_dvd_mul_right (H1 : IsCoprime x z) (H2 : x ∣ y * z) : x ∣ y := by
  let ⟨a, b, H⟩ := H1
  rw [← mul_one y]; rw [← H]; rw [mul_add]; rw [← mul_assoc]; rw [mul_left_comm]
  exact dvd_add (dvd_mul_left _ _) (H2.mul_left _)

/--
theorem `IsCoprime.dvd_of_dvd_mul_left` / 定理 `IsCoprime.dvd_of_dvd_mul_left`

English:
theorem IsCoprime.dvd_of_dvd_mul_left
  given: (H1 : IsCoprime x y) (H2 : x ∣ y * z)
  statement: x ∣ z
  proof: by
  let ⟨a, b, H⟩ := H1
  rw [← one_mul z]; rw [← H]; rw [add_mul]; rw [mul_right_comm]; rw [mul_assoc b]
  exact dvd_add (dvd_mul_left _ _) (H2.mul_left _)

中文:
定理 IsCoprime.dvd_of_dvd_mul_left
  条件: (H1 : IsCoprime x y) (H2 : x ∣ y * z)
  结论: x ∣ z
  证明: by
  let ⟨a, b, H⟩ := H1
  rw [← one_mul z]; rw [← H]; rw [add_mul]; rw [mul_right_comm]; rw [mul_assoc b]
  exact dvd_add (dvd_mul_left _ _) (H2.mul_left _)

Depends on / 依赖: H2.mul_left, add_mul, dvd_add, dvd_mul_left, mul_assoc, mul_left, mul_right_comm, one_mul
-/
theorem IsCoprime.dvd_of_dvd_mul_left (H1 : IsCoprime x y) (H2 : x ∣ y * z) : x ∣ z := by
  let ⟨a, b, H⟩ := H1
  rw [← one_mul z]; rw [← H]; rw [add_mul]; rw [mul_right_comm]; rw [mul_assoc b]
  exact dvd_add (dvd_mul_left _ _) (H2.mul_left _)

/--
theorem `IsCoprime.mul_left` / 定理 `IsCoprime.mul_left`

English:
theorem IsCoprime.mul_left
  given: (H1 : IsCoprime x z) (H2 : IsCoprime y z)
  statement: IsCoprime (x * y) z
  proof: let ⟨a, b, h1⟩ := H1
  let ⟨c, d, h2⟩ := H2
  ⟨a * c, a * x * d + b * c * y + b * d * z,
    calc a * c * (x * y) + (a * x * d + b * c * y + b * d * z) * z
      _ = (a * x + b * z) * (c * y + d * z) := by ring
      _ = 1 := by rw [h1, h2, mul_one]
      ⟩

中文:
定理 IsCoprime.mul_left
  条件: (H1 : IsCoprime x z) (H2 : IsCoprime y z)
  结论: IsCoprime (x * y) z
  证明: let ⟨a, b, h1⟩ := H1
  let ⟨c, d, h2⟩ := H2
  ⟨a * c, a * x * d + b * c * y + b * d * z,
    calc a * c * (x * y) + (a * x * d + b * c * y + b * d * z) * z
      _ = (a * x + b * z) * (c * y + d * z) := by ring
      _ = 1 := by rw [h1, h2, mul_one]
      ⟩

Depends on / 依赖: mul_one
-/
theorem IsCoprime.mul_left (H1 : IsCoprime x z) (H2 : IsCoprime y z) : IsCoprime (x * y) z :=
  let ⟨a, b, h1⟩ := H1
  let ⟨c, d, h2⟩ := H2
  ⟨a * c, a * x * d + b * c * y + b * d * z,
    calc a * c * (x * y) + (a * x * d + b * c * y + b * d * z) * z
      _ = (a * x + b * z) * (c * y + d * z) := by ring
      _ = 1 := by rw [h1, h2, mul_one]
      ⟩

/--
theorem `IsCoprime.mul_right` / 定理 `IsCoprime.mul_right`

English:
theorem IsCoprime.mul_right
  given: (H1 : IsCoprime x y) (H2 : IsCoprime x z)
  statement: IsCoprime x (y * z)
  proof: by
  rw [isCoprime_comm] at H1 H2 ⊢
  exact H1.mul_left H2

中文:
定理 IsCoprime.mul_right
  条件: (H1 : IsCoprime x y) (H2 : IsCoprime x z)
  结论: IsCoprime x (y * z)
  证明: by
  rw [isCoprime_comm] at H1 H2 ⊢
  exact H1.mul_left H2

Depends on / 依赖: H1.mul_left, isCoprime_comm, mul_left
-/
theorem IsCoprime.mul_right (H1 : IsCoprime x y) (H2 : IsCoprime x z) : IsCoprime x (y * z) := by
  rw [isCoprime_comm] at H1 H2 ⊢
  exact H1.mul_left H2

/--
theorem `IsCoprime.mul_dvd` / 定理 `IsCoprime.mul_dvd`

English:
theorem IsCoprime.mul_dvd
  given: (H : IsCoprime x y) (H1 : x ∣ z) (H2 : y ∣ z)
  statement: x * y ∣ z
  proof: by
  obtain ⟨a, b, h⟩ := H
  rw [← mul_one z]; rw [← h]; rw [mul_add]
  apply dvd_add
  · rw [mul_comm z, mul_assoc]
    exact (mul_dvd_mul_left _ H2).mul_left _
  · rw [mul_comm b, ← mul_assoc]
    exact (mul_dvd_mul_right H1 _).mul_right _

中文:
定理 IsCoprime.mul_dvd
  条件: (H : IsCoprime x y) (H1 : x ∣ z) (H2 : y ∣ z)
  结论: x * y ∣ z
  证明: by
  obtain ⟨a, b, h⟩ := H
  rw [← mul_one z]; rw [← h]; rw [mul_add]
  apply dvd_add
  · rw [mul_comm z, mul_assoc]
    exact (mul_dvd_mul_left _ H2).mul_left _
  · rw [mul_comm b, ← mul_assoc]
    exact (mul_dvd_mul_right H1 _).mul_right _

Depends on / 依赖: dvd_add, mul_add, mul_assoc, mul_comm, mul_dvd_mul_left, mul_dvd_mul_right, mul_left, mul_one, mul_right
-/
theorem IsCoprime.mul_dvd (H : IsCoprime x y) (H1 : x ∣ z) (H2 : y ∣ z) : x * y ∣ z := by
  obtain ⟨a, b, h⟩ := H
  rw [← mul_one z]; rw [← h]; rw [mul_add]
  apply dvd_add
  · rw [mul_comm z, mul_assoc]
    exact (mul_dvd_mul_left _ H2).mul_left _
  · rw [mul_comm b, ← mul_assoc]
    exact (mul_dvd_mul_right H1 _).mul_right _

/--
theorem `IsCoprime.of_mul_left_left` / 定理 `IsCoprime.of_mul_left_left`

English:
theorem IsCoprime.of_mul_left_left
  given: (H : IsCoprime (x * y) z)
  statement: IsCoprime x z
  proof: let ⟨a, b, h⟩ := H
  ⟨a * y, b, by rwa [mul_right_comm, mul_assoc]⟩

中文:
定理 IsCoprime.of_mul_left_left
  条件: (H : IsCoprime (x * y) z)
  结论: IsCoprime x z
  证明: let ⟨a, b, h⟩ := H
  ⟨a * y, b, by rwa [mul_right_comm, mul_assoc]⟩

Depends on / 依赖: mul_assoc, mul_right_comm
-/
theorem IsCoprime.of_mul_left_left (H : IsCoprime (x * y) z) : IsCoprime x z :=
  let ⟨a, b, h⟩ := H
  ⟨a * y, b, by rwa [mul_right_comm, mul_assoc]⟩

/--
theorem `IsCoprime.of_mul_left_right` / 定理 `IsCoprime.of_mul_left_right`

English:
theorem IsCoprime.of_mul_left_right
  given: (H : IsCoprime (x * y) z)
  statement: IsCoprime y z
  proof: by
  rw [mul_comm] at H
  exact H.of_mul_left_left

中文:
定理 IsCoprime.of_mul_left_right
  条件: (H : IsCoprime (x * y) z)
  结论: IsCoprime y z
  证明: by
  rw [mul_comm] at H
  exact H.of_mul_left_left

Depends on / 依赖: H.of_mul_left_left, mul_comm, of_mul_left_left
-/
theorem IsCoprime.of_mul_left_right (H : IsCoprime (x * y) z) : IsCoprime y z := by
  rw [mul_comm] at H
  exact H.of_mul_left_left

/--
theorem `IsCoprime.of_mul_right_left` / 定理 `IsCoprime.of_mul_right_left`

English:
theorem IsCoprime.of_mul_right_left
  given: (H : IsCoprime x (y * z))
  statement: IsCoprime x y
  proof: by
  rw [isCoprime_comm] at H ⊢
  exact H.of_mul_left_left

中文:
定理 IsCoprime.of_mul_right_left
  条件: (H : IsCoprime x (y * z))
  结论: IsCoprime x y
  证明: by
  rw [isCoprime_comm] at H ⊢
  exact H.of_mul_left_left

Depends on / 依赖: H.of_mul_left_left, isCoprime_comm, of_mul_left_left
-/
theorem IsCoprime.of_mul_right_left (H : IsCoprime x (y * z)) : IsCoprime x y := by
  rw [isCoprime_comm] at H ⊢
  exact H.of_mul_left_left

/--
theorem `IsCoprime.of_mul_right_right` / 定理 `IsCoprime.of_mul_right_right`

English:
theorem IsCoprime.of_mul_right_right
  given: (H : IsCoprime x (y * z))
  statement: IsCoprime x z
  proof: by
  rw [mul_comm] at H
  exact H.of_mul_right_left

中文:
定理 IsCoprime.of_mul_right_right
  条件: (H : IsCoprime x (y * z))
  结论: IsCoprime x z
  证明: by
  rw [mul_comm] at H
  exact H.of_mul_right_left

Depends on / 依赖: H.of_mul_right_left, mul_comm, of_mul_right_left
-/
theorem IsCoprime.of_mul_right_right (H : IsCoprime x (y * z)) : IsCoprime x z := by
  rw [mul_comm] at H
  exact H.of_mul_right_left

/--
theorem `IsCoprime.mul_left_iff` / 定理 `IsCoprime.mul_left_iff`

English:
theorem IsCoprime.mul_left_iff
  statement: IsCoprime (x * y) z ↔ IsCoprime x z ∧ IsCoprime y z
  proof: ⟨fun H => ⟨H.of_mul_left_left, H.of_mul_left_right⟩, fun ⟨H1, H2⟩ => H1.mul_left H2⟩

中文:
定理 IsCoprime.mul_left_iff
  结论: IsCoprime (x * y) z ↔ IsCoprime x z ∧ IsCoprime y z
  证明: ⟨fun H => ⟨H.of_mul_left_left, H.of_mul_left_right⟩, fun ⟨H1, H2⟩ => H1.mul_left H2⟩

Depends on / 依赖: H.of_mul_left_left, H.of_mul_left_right, H1.mul_left, mul_left, of_mul_left_left, of_mul_left_right
-/
theorem IsCoprime.mul_left_iff : IsCoprime (x * y) z ↔ IsCoprime x z ∧ IsCoprime y z :=
  ⟨fun H => ⟨H.of_mul_left_left, H.of_mul_left_right⟩, fun ⟨H1, H2⟩ => H1.mul_left H2⟩

/--
theorem `IsCoprime.mul_right_iff` / 定理 `IsCoprime.mul_right_iff`

English:
theorem IsCoprime.mul_right_iff
  statement: IsCoprime x (y * z) ↔ IsCoprime x y ∧ IsCoprime x z
  proof: by
  rw [isCoprime_comm]; rw [IsCoprime.mul_left_iff]; rw [isCoprime_comm]; rw [@isCoprime_comm _ _ z]

中文:
定理 IsCoprime.mul_right_iff
  结论: IsCoprime x (y * z) ↔ IsCoprime x y ∧ IsCoprime x z
  证明: by
  rw [isCoprime_comm]; rw [IsCoprime.mul_left_iff]; rw [isCoprime_comm]; rw [@isCoprime_comm _ _ z]

Depends on / 依赖: IsCoprime, IsCoprime.mul_left_iff, isCoprime_comm, mul_left_iff
-/
theorem IsCoprime.mul_right_iff : IsCoprime x (y * z) ↔ IsCoprime x y ∧ IsCoprime x z := by
  rw [isCoprime_comm]; rw [IsCoprime.mul_left_iff]; rw [isCoprime_comm]; rw [@isCoprime_comm _ _ z]

/--
theorem `IsCoprime.of_isCoprime_of_dvd_left` / 定理 `IsCoprime.of_isCoprime_of_dvd_left`

English:
theorem IsCoprime.of_isCoprime_of_dvd_left
  given: (h : IsCoprime y z) (hdvd : x ∣ y)
  statement: IsCoprime x z
  proof: by
  obtain ⟨d, rfl⟩ := hdvd
  exact IsCoprime.of_mul_left_left h

中文:
定理 IsCoprime.of_isCoprime_of_dvd_left
  条件: (h : IsCoprime y z) (hdvd : x ∣ y)
  结论: IsCoprime x z
  证明: by
  obtain ⟨d, rfl⟩ := hdvd
  exact IsCoprime.of_mul_left_left h

Depends on / 依赖: IsCoprime, IsCoprime.of_mul_left_left, of_mul_left_left
-/
theorem IsCoprime.of_isCoprime_of_dvd_left (h : IsCoprime y z) (hdvd : x ∣ y) : IsCoprime x z := by
  obtain ⟨d, rfl⟩ := hdvd
  exact IsCoprime.of_mul_left_left h

/--
theorem `IsCoprime.of_isCoprime_of_dvd_right` / 定理 `IsCoprime.of_isCoprime_of_dvd_right`

English:
theorem IsCoprime.of_isCoprime_of_dvd_right
  given: (h : IsCoprime z y) (hdvd : x ∣ y)
  statement: IsCoprime z x
  proof: (h.symm.of_isCoprime_of_dvd_left hdvd).symm

@[gcongr]

中文:
定理 IsCoprime.of_isCoprime_of_dvd_right
  条件: (h : IsCoprime z y) (hdvd : x ∣ y)
  结论: IsCoprime z x
  证明: (h.symm.of_isCoprime_of_dvd_left hdvd).symm

@[gcongr]

Depends on / 依赖: h.symm.of_isCoprime_of_dvd_left, of_isCoprime_of_dvd_left
-/
theorem IsCoprime.of_isCoprime_of_dvd_right (h : IsCoprime z y) (hdvd : x ∣ y) : IsCoprime z x :=
  (h.symm.of_isCoprime_of_dvd_left hdvd).symm

@[gcongr]
/--
theorem `IsCoprime.mono` / 定理 `IsCoprime.mono`

English:
theorem IsCoprime.mono
  given: (h₁ : x ∣ y) (h₂ : z ∣ w) (h : IsCoprime y w)
  statement: IsCoprime x z
  proof: .of_isCoprime_of_dvd_right h₂ h.of_isCoprime_of_dvd_left h₁

中文:
定理 IsCoprime.mono
  条件: (h₁ : x ∣ y) (h₂ : z ∣ w) (h : IsCoprime y w)
  结论: IsCoprime x z
  证明: .of_isCoprime_of_dvd_right h₂ h.of_isCoprime_of_dvd_left h₁

Depends on / 依赖: h.of_isCoprime_of_dvd_left, of_isCoprime_of_dvd_left, of_isCoprime_of_dvd_right
-/
theorem IsCoprime.mono (h₁ : x ∣ y) (h₂ : z ∣ w) (h : IsCoprime y w) : IsCoprime x z :=
.of_isCoprime_of_dvd_right h₂ h.of_isCoprime_of_dvd_left h₁

/--
theorem `IsCoprime.isUnit_of_dvd` / 定理 `IsCoprime.isUnit_of_dvd`

English:
theorem IsCoprime.isUnit_of_dvd
  given: (H : IsCoprime x y) (d : x ∣ y)
  statement: IsUnit x
  proof: let ⟨k, hk⟩ := d
isCoprime_self.1 IsCoprime.of_mul_right_left show IsCoprime x (x * k) from hk ▸ H

中文:
定理 IsCoprime.isUnit_of_dvd
  条件: (H : IsCoprime x y) (d : x ∣ y)
  结论: 是单位 x
  证明: let ⟨k, hk⟩ := d
isCoprime_self.1 IsCoprime.of_mul_right_left show IsCoprime x (x * k) from hk ▸ H

Depends on / 依赖: IsCoprime, IsCoprime.of_mul_right_left, isCoprime_self, of_mul_right_left
-/
theorem IsCoprime.isUnit_of_dvd (H : IsCoprime x y) (d : x ∣ y) : IsUnit x :=
  let ⟨k, hk⟩ := d
isCoprime_self.1 IsCoprime.of_mul_right_left show IsCoprime x (x * k) from hk ▸ H

/--
theorem `IsCoprime.isUnit_of_associated` / 定理 `IsCoprime.isUnit_of_associated`

English:
theorem IsCoprime.isUnit_of_associated
  given: {x y : R} (h₁ : IsCoprime x y) (h₂ : Associated x y)
  proof: ⟨h₁.isUnit_of_dvd (h₂.dvd), h₁.symm.isUnit_of_dvd (h₂.dvd')⟩

中文:
定理 IsCoprime.isUnit_of_associated
  条件: {x y : R} (h₁ : IsCoprime x y) (h₂ : Associated x y)
  证明: ⟨h₁.isUnit_of_dvd (h₂.dvd), h₁.symm.isUnit_of_dvd (h₂.dvd')⟩

Depends on / 依赖: isUnit_of_dvd, symm.isUnit_of_dvd
-/
theorem IsCoprime.isUnit_of_associated {x y : R} (h₁ : IsCoprime x y) (h₂ : Associated x y) :
    IsUnit x ∧ IsUnit y :=
  ⟨h₁.isUnit_of_dvd (h₂.dvd), h₁.symm.isUnit_of_dvd (h₂.dvd')⟩

/--
theorem `IsCoprime.isUnit_of_dvd'` / 定理 `IsCoprime.isUnit_of_dvd'`

English:
theorem IsCoprime.isUnit_of_dvd'
  given: {a b x : R} (h : IsCoprime a b) (ha : x ∣ a) (hb : x ∣ b)
  proof: (h.of_isCoprime_of_dvd_left ha).isUnit_of_dvd hb

中文:
定理 IsCoprime.isUnit_of_dvd'
  条件: {a b x : R} (h : IsCoprime a b) (ha : x ∣ a) (hb : x ∣ b)
  证明: (h.of_isCoprime_of_dvd_left ha).isUnit_of_dvd hb

Depends on / 依赖: h.of_isCoprime_of_dvd_left, isUnit_of_dvd, of_isCoprime_of_dvd_left
-/
theorem IsCoprime.isUnit_of_dvd' {a b x : R} (h : IsCoprime a b) (ha : x ∣ a) (hb : x ∣ b) :
    IsUnit x :=
  (h.of_isCoprime_of_dvd_left ha).isUnit_of_dvd hb

/--
theorem `IsCoprime.isRelPrime` / 定理 `IsCoprime.isRelPrime`

English:
theorem IsCoprime.isRelPrime
  given: {a b : R} (h : IsCoprime a b)
  statement: IsRelPrime a b
  proof: fun _ => h.isUnit_of_dvd'

中文:
定理 IsCoprime.isRelPrime
  条件: {a b : R} (h : IsCoprime a b)
  结论: IsRelPrime a b
  证明: fun _ => h.isUnit_of_dvd'

Depends on / 依赖: h.isUnit_of_dvd, isUnit_of_dvd
-/
theorem IsCoprime.isRelPrime {a b : R} (h : IsCoprime a b) : IsRelPrime a b :=
  fun _ => h.isUnit_of_dvd'

/--
theorem `IsCoprime.map` / 定理 `IsCoprime.map`

English:
theorem IsCoprime.map
  given: (H : IsCoprime x y) {S : Type v} [CommSemiring S] (f : R ->+* S)
  proof: let ⟨a, b, h⟩ := H
  ⟨f a, f b, by rw [← f.map_mul, ← f.map_mul, ← f.map_add, h, f.map_one]⟩

中文:
定理 IsCoprime.map
  条件: (H : IsCoprime x y) {S : 类型v} [交换半环 S] (f : R ->+* S)
  证明: let ⟨a, b, h⟩ := H
  ⟨f a, f b, by rw [← f.map_mul, ← f.map_mul, ← f.map_add, h, f.map_one]⟩

Depends on / 依赖: f.map_add, f.map_mul, f.map_one, map_add, map_mul, map_one
-/
theorem IsCoprime.map (H : IsCoprime x y) {S : Type v} [CommSemiring S] (f : R ->+* S) :
    IsCoprime (f x) (f y) :=
  let ⟨a, b, h⟩ := H
  ⟨f a, f b, by rw [← f.map_mul, ← f.map_mul, ← f.map_add, h, f.map_one]⟩

/--
theorem `IsCoprime.of_add_mul_left_left` / 定理 `IsCoprime.of_add_mul_left_left`

English:
theorem IsCoprime.of_add_mul_left_left
  given: (h : IsCoprime (x + y * z) y)
  statement: IsCoprime x y
  proof: let ⟨a, b, H⟩ := h
  ⟨a, a * z + b, by
    simpa only [add_mul, mul_add, add_assoc, add_comm, add_left_comm, mul_assoc, mul_comm,
      mul_left_comm] using H⟩

中文:
定理 IsCoprime.of_add_mul_left_left
  条件: (h : IsCoprime (x + y * z) y)
  结论: IsCoprime x y
  证明: let ⟨a, b, H⟩ := h
  ⟨a, a * z + b, by
    simpa only [add_mul, mul_add, add_assoc, add_comm, add_left_comm, mul_assoc, mul_comm,
      mul_left_comm] using H⟩

Depends on / 依赖: add_assoc, add_comm, add_left_comm, add_mul, mul_add, mul_assoc, mul_comm, mul_left_comm
-/
theorem IsCoprime.of_add_mul_left_left (h : IsCoprime (x + y * z) y) : IsCoprime x y :=
  let ⟨a, b, H⟩ := h
  ⟨a, a * z + b, by
    simpa only [add_mul, mul_add, add_assoc, add_comm, add_left_comm, mul_assoc, mul_comm,
      mul_left_comm] using H⟩

/--
theorem `IsCoprime.of_add_mul_right_left` / 定理 `IsCoprime.of_add_mul_right_left`

English:
theorem IsCoprime.of_add_mul_right_left
  given: (h : IsCoprime (x + z * y) y)
  statement: IsCoprime x y
  proof: by
  rw [mul_comm] at h
  exact h.of_add_mul_left_left

中文:
定理 IsCoprime.of_add_mul_right_left
  条件: (h : IsCoprime (x + z * y) y)
  结论: IsCoprime x y
  证明: by
  rw [mul_comm] at h
  exact h.of_add_mul_left_left

Depends on / 依赖: h.of_add_mul_left_left, mul_comm, of_add_mul_left_left
-/
theorem IsCoprime.of_add_mul_right_left (h : IsCoprime (x + z * y) y) : IsCoprime x y := by
  rw [mul_comm] at h
  exact h.of_add_mul_left_left

/--
theorem `IsCoprime.of_add_mul_left_right` / 定理 `IsCoprime.of_add_mul_left_right`

English:
theorem IsCoprime.of_add_mul_left_right
  given: (h : IsCoprime x (y + x * z))
  statement: IsCoprime x y
  proof: by
  rw [isCoprime_comm] at h ⊢
  exact h.of_add_mul_left_left

中文:
定理 IsCoprime.of_add_mul_left_right
  条件: (h : IsCoprime x (y + x * z))
  结论: IsCoprime x y
  证明: by
  rw [isCoprime_comm] at h ⊢
  exact h.of_add_mul_left_left

Depends on / 依赖: h.of_add_mul_left_left, isCoprime_comm, of_add_mul_left_left
-/
theorem IsCoprime.of_add_mul_left_right (h : IsCoprime x (y + x * z)) : IsCoprime x y := by
  rw [isCoprime_comm] at h ⊢
  exact h.of_add_mul_left_left

/--
theorem `IsCoprime.of_add_mul_right_right` / 定理 `IsCoprime.of_add_mul_right_right`

English:
theorem IsCoprime.of_add_mul_right_right
  given: (h : IsCoprime x (y + z * x))
  statement: IsCoprime x y
  proof: by
  rw [mul_comm] at h
  exact h.of_add_mul_left_right

中文:
定理 IsCoprime.of_add_mul_right_right
  条件: (h : IsCoprime x (y + z * x))
  结论: IsCoprime x y
  证明: by
  rw [mul_comm] at h
  exact h.of_add_mul_left_right

Depends on / 依赖: h.of_add_mul_left_right, mul_comm, of_add_mul_left_right
-/
theorem IsCoprime.of_add_mul_right_right (h : IsCoprime x (y + z * x)) : IsCoprime x y := by
  rw [mul_comm] at h
  exact h.of_add_mul_left_right

/--
theorem `IsCoprime.of_mul_add_left_left` / 定理 `IsCoprime.of_mul_add_left_left`

English:
theorem IsCoprime.of_mul_add_left_left
  given: (h : IsCoprime (y * z + x) y)
  statement: IsCoprime x y
  proof: by
  rw [add_comm] at h
  exact h.of_add_mul_left_left

中文:
定理 IsCoprime.of_mul_add_left_left
  条件: (h : IsCoprime (y * z + x) y)
  结论: IsCoprime x y
  证明: by
  rw [add_comm] at h
  exact h.of_add_mul_left_left

Depends on / 依赖: add_comm, h.of_add_mul_left_left, of_add_mul_left_left
-/
theorem IsCoprime.of_mul_add_left_left (h : IsCoprime (y * z + x) y) : IsCoprime x y := by
  rw [add_comm] at h
  exact h.of_add_mul_left_left

/--
theorem `IsCoprime.of_mul_add_right_left` / 定理 `IsCoprime.of_mul_add_right_left`

English:
theorem IsCoprime.of_mul_add_right_left
  given: (h : IsCoprime (z * y + x) y)
  statement: IsCoprime x y
  proof: by
  rw [add_comm] at h
  exact h.of_add_mul_right_left

中文:
定理 IsCoprime.of_mul_add_right_left
  条件: (h : IsCoprime (z * y + x) y)
  结论: IsCoprime x y
  证明: by
  rw [add_comm] at h
  exact h.of_add_mul_right_left

Depends on / 依赖: add_comm, h.of_add_mul_right_left, of_add_mul_right_left
-/
theorem IsCoprime.of_mul_add_right_left (h : IsCoprime (z * y + x) y) : IsCoprime x y := by
  rw [add_comm] at h
  exact h.of_add_mul_right_left

/--
theorem `IsCoprime.of_mul_add_left_right` / 定理 `IsCoprime.of_mul_add_left_right`

English:
theorem IsCoprime.of_mul_add_left_right
  given: (h : IsCoprime x (x * z + y))
  statement: IsCoprime x y
  proof: by
  rw [add_comm] at h
  exact h.of_add_mul_left_right

中文:
定理 IsCoprime.of_mul_add_left_right
  条件: (h : IsCoprime x (x * z + y))
  结论: IsCoprime x y
  证明: by
  rw [add_comm] at h
  exact h.of_add_mul_left_right

Depends on / 依赖: add_comm, h.of_add_mul_left_right, of_add_mul_left_right
-/
theorem IsCoprime.of_mul_add_left_right (h : IsCoprime x (x * z + y)) : IsCoprime x y := by
  rw [add_comm] at h
  exact h.of_add_mul_left_right

/--
theorem `IsCoprime.of_mul_add_right_right` / 定理 `IsCoprime.of_mul_add_right_right`

English:
theorem IsCoprime.of_mul_add_right_right
  given: (h : IsCoprime x (z * x + y))
  statement: IsCoprime x y
  proof: by
  rw [add_comm] at h
  exact h.of_add_mul_right_right

中文:
定理 IsCoprime.of_mul_add_right_right
  条件: (h : IsCoprime x (z * x + y))
  结论: IsCoprime x y
  证明: by
  rw [add_comm] at h
  exact h.of_add_mul_right_right

Depends on / 依赖: add_comm, h.of_add_mul_right_right, of_add_mul_right_right
-/
theorem IsCoprime.of_mul_add_right_right (h : IsCoprime x (z * x + y)) : IsCoprime x y := by
  rw [add_comm] at h
  exact h.of_add_mul_right_right

/--
theorem `IsRelPrime.of_add_mul_left_left` / 定理 `IsRelPrime.of_add_mul_left_left`

English:
theorem IsRelPrime.of_add_mul_left_left
  given: (h : IsRelPrime (x + y * z) y)
  statement: IsRelPrime x y
  proof: fun _ hx hy => h (dvd_add hx <| dvd_mul_of_dvd_left hy z) hy

中文:
定理 IsRelPrime.of_add_mul_left_left
  条件: (h : IsRelPrime (x + y * z) y)
  结论: IsRelPrime x y
  证明: fun _ hx hy => h (dvd_add hx <| dvd_mul_of_dvd_left hy z) hy

Depends on / 依赖: dvd_add, dvd_mul_of_dvd_left
-/
theorem IsRelPrime.of_add_mul_left_left (h : IsRelPrime (x + y * z) y) : IsRelPrime x y :=
  fun _ hx hy => h (dvd_add hx <| dvd_mul_of_dvd_left hy z) hy

/--
theorem `IsRelPrime.of_add_mul_right_left` / 定理 `IsRelPrime.of_add_mul_right_left`

English:
theorem IsRelPrime.of_add_mul_right_left
  given: (h : IsRelPrime (x + z * y) y)
  statement: IsRelPrime x y
  proof: (mul_comm z y ▸ h).of_add_mul_left_left

中文:
定理 IsRelPrime.of_add_mul_right_left
  条件: (h : IsRelPrime (x + z * y) y)
  结论: IsRelPrime x y
  证明: (mul_comm z y ▸ h).of_add_mul_left_left

Depends on / 依赖: mul_comm, of_add_mul_left_left
-/
theorem IsRelPrime.of_add_mul_right_left (h : IsRelPrime (x + z * y) y) : IsRelPrime x y :=
  (mul_comm z y ▸ h).of_add_mul_left_left

/--
theorem `IsRelPrime.of_add_mul_left_right` / 定理 `IsRelPrime.of_add_mul_left_right`

English:
theorem IsRelPrime.of_add_mul_left_right
  given: (h : IsRelPrime x (y + x * z))
  statement: IsRelPrime x y
  proof: by
  rw [isRelPrime_comm] at h ⊢
  exact h.of_add_mul_left_left

中文:
定理 IsRelPrime.of_add_mul_left_right
  条件: (h : IsRelPrime x (y + x * z))
  结论: IsRelPrime x y
  证明: by
  rw [isRelPrime_comm] at h ⊢
  exact h.of_add_mul_left_left

Depends on / 依赖: h.of_add_mul_left_left, isRelPrime_comm, of_add_mul_left_left
-/
theorem IsRelPrime.of_add_mul_left_right (h : IsRelPrime x (y + x * z)) : IsRelPrime x y := by
  rw [isRelPrime_comm] at h ⊢
  exact h.of_add_mul_left_left

/--
theorem `IsRelPrime.of_add_mul_right_right` / 定理 `IsRelPrime.of_add_mul_right_right`

English:
theorem IsRelPrime.of_add_mul_right_right
  given: (h : IsRelPrime x (y + z * x))
  statement: IsRelPrime x y
  proof: (mul_comm z x ▸ h).of_add_mul_left_right

中文:
定理 IsRelPrime.of_add_mul_right_right
  条件: (h : IsRelPrime x (y + z * x))
  结论: IsRelPrime x y
  证明: (mul_comm z x ▸ h).of_add_mul_left_right

Depends on / 依赖: mul_comm, of_add_mul_left_right
-/
theorem IsRelPrime.of_add_mul_right_right (h : IsRelPrime x (y + z * x)) : IsRelPrime x y :=
  (mul_comm z x ▸ h).of_add_mul_left_right

/--
theorem `IsRelPrime.of_mul_add_left_left` / 定理 `IsRelPrime.of_mul_add_left_left`

English:
theorem IsRelPrime.of_mul_add_left_left
  given: (h : IsRelPrime (y * z + x) y)
  statement: IsRelPrime x y
  proof: (add_comm _ x ▸ h).of_add_mul_left_left

中文:
定理 IsRelPrime.of_mul_add_left_left
  条件: (h : IsRelPrime (y * z + x) y)
  结论: IsRelPrime x y
  证明: (add_comm _ x ▸ h).of_add_mul_left_left

Depends on / 依赖: add_comm, of_add_mul_left_left
-/
theorem IsRelPrime.of_mul_add_left_left (h : IsRelPrime (y * z + x) y) : IsRelPrime x y :=
  (add_comm _ x ▸ h).of_add_mul_left_left

/--
theorem `IsRelPrime.of_mul_add_right_left` / 定理 `IsRelPrime.of_mul_add_right_left`

English:
theorem IsRelPrime.of_mul_add_right_left
  given: (h : IsRelPrime (z * y + x) y)
  statement: IsRelPrime x y
  proof: (add_comm _ x ▸ h).of_add_mul_right_left

中文:
定理 IsRelPrime.of_mul_add_right_left
  条件: (h : IsRelPrime (z * y + x) y)
  结论: IsRelPrime x y
  证明: (add_comm _ x ▸ h).of_add_mul_right_left

Depends on / 依赖: add_comm, of_add_mul_right_left
-/
theorem IsRelPrime.of_mul_add_right_left (h : IsRelPrime (z * y + x) y) : IsRelPrime x y :=
  (add_comm _ x ▸ h).of_add_mul_right_left

/--
theorem `IsRelPrime.of_mul_add_left_right` / 定理 `IsRelPrime.of_mul_add_left_right`

English:
theorem IsRelPrime.of_mul_add_left_right
  given: (h : IsRelPrime x (x * z + y))
  statement: IsRelPrime x y
  proof: (add_comm _ y ▸ h).of_add_mul_left_right

中文:
定理 IsRelPrime.of_mul_add_left_right
  条件: (h : IsRelPrime x (x * z + y))
  结论: IsRelPrime x y
  证明: (add_comm _ y ▸ h).of_add_mul_left_right

Depends on / 依赖: add_comm, of_add_mul_left_right
-/
theorem IsRelPrime.of_mul_add_left_right (h : IsRelPrime x (x * z + y)) : IsRelPrime x y :=
  (add_comm _ y ▸ h).of_add_mul_left_right

/--
theorem `IsRelPrime.of_mul_add_right_right` / 定理 `IsRelPrime.of_mul_add_right_right`

English:
theorem IsRelPrime.of_mul_add_right_right
  given: (h : IsRelPrime x (z * x + y))
  statement: IsRelPrime x y
  proof: (add_comm _ y ▸ h).of_add_mul_right_right

中文:
定理 IsRelPrime.of_mul_add_right_right
  条件: (h : IsRelPrime x (z * x + y))
  结论: IsRelPrime x y
  证明: (add_comm _ y ▸ h).of_add_mul_right_right

Depends on / 依赖: add_comm, of_add_mul_right_right
-/
theorem IsRelPrime.of_mul_add_right_right (h : IsRelPrime x (z * x + y)) : IsRelPrime x y :=
  (add_comm _ y ▸ h).of_add_mul_right_right

end CommSemiring

section ScalarTower

variable {R G : Type*} [CommSemiring R] [Group G] [MulAction G R] [SMulCommClass G R R]
  [IsScalarTower G R R] (x : G) (y z : R)

/--
theorem `isCoprime_group_smul_left` / 定理 `isCoprime_group_smul_left`

English:
theorem isCoprime_group_smul_left
  statement: IsCoprime (x • y) z ↔ IsCoprime y z
  proof: ⟨fun ⟨a, b, h⟩ => ⟨x • a, b, by rwa [smul_mul_assoc, ← mul_smul_comm]⟩, fun ⟨a, b, h⟩ =>
    ⟨x⁻¹ • a, b, by rwa [smul_mul_smul_comm, inv_mul_cancel, one_smul]⟩⟩

中文:
定理 isCoprime_group_smul_left
  结论: IsCoprime (x • y) z ↔ IsCoprime y z
  证明: ⟨fun ⟨a, b, h⟩ => ⟨x • a, b, by rwa [smul_mul_assoc, ← mul_smul_comm]⟩, fun ⟨a, b, h⟩ =>
    ⟨x⁻¹ • a, b, by rwa [smul_mul_smul_comm, inv_mul_cancel, one_smul]⟩⟩

Depends on / 依赖: inv_mul_cancel, mul_smul_comm, one_smul, smul_mul_assoc, smul_mul_smul_comm
-/
theorem isCoprime_group_smul_left : IsCoprime (x • y) z ↔ IsCoprime y z :=
  ⟨fun ⟨a, b, h⟩ => ⟨x • a, b, by rwa [smul_mul_assoc, ← mul_smul_comm]⟩, fun ⟨a, b, h⟩ =>
    ⟨x⁻¹ • a, b, by rwa [smul_mul_smul_comm, inv_mul_cancel, one_smul]⟩⟩

/--
theorem `isCoprime_group_smul_right` / 定理 `isCoprime_group_smul_right`

English:
theorem isCoprime_group_smul_right
  statement: IsCoprime y (x • z) ↔ IsCoprime y z
  proof: isCoprime_comm.trans (isCoprime_group_smul_left x z y).trans isCoprime_comm

中文:
定理 isCoprime_group_smul_right
  结论: IsCoprime y (x • z) ↔ IsCoprime y z
  证明: isCoprime_comm.trans (isCoprime_group_smul_left x z y).trans isCoprime_comm

Depends on / 依赖: isCoprime_comm, isCoprime_comm.trans, isCoprime_group_smul_left
-/
theorem isCoprime_group_smul_right : IsCoprime y (x • z) ↔ IsCoprime y z :=
isCoprime_comm.trans (isCoprime_group_smul_left x z y).trans isCoprime_comm

/--
theorem `isCoprime_group_smul` / 定理 `isCoprime_group_smul`

English:
theorem isCoprime_group_smul
  statement: IsCoprime (x • y) (x • z) ↔ IsCoprime y z
  proof: (isCoprime_group_smul_left x y (x • z)).trans (isCoprime_group_smul_right x y z)

中文:
定理 isCoprime_group_smul
  结论: IsCoprime (x • y) (x • z) ↔ IsCoprime y z
  证明: (isCoprime_group_smul_left x y (x • z)).trans (isCoprime_group_smul_right x y z)

Depends on / 依赖: isCoprime_group_smul_left, isCoprime_group_smul_right
-/
theorem isCoprime_group_smul : IsCoprime (x • y) (x • z) ↔ IsCoprime y z :=
  (isCoprime_group_smul_left x y (x • z)).trans (isCoprime_group_smul_right x y z)

end ScalarTower

section CommSemiringUnit

variable {R : Type*} [CommSemiring R] {x u v : R}

/--
theorem `isCoprime_mul_unit_left_left` / 定理 `isCoprime_mul_unit_left_left`

English:
theorem isCoprime_mul_unit_left_left
  given: (hu : IsUnit x) (y z : R)
  proof: let ⟨u, hu⟩ := hu
  hu ▸ isCoprime_group_smul_left u y z

中文:
定理 isCoprime_mul_unit_left_left
  条件: (hu : 是单位 x) (y z : R)
  证明: let ⟨u, hu⟩ := hu
  hu ▸ isCoprime_group_smul_left u y z

Depends on / 依赖: isCoprime_group_smul_left
-/
theorem isCoprime_mul_unit_left_left (hu : IsUnit x) (y z : R) :
    IsCoprime (x * y) z ↔ IsCoprime y z :=
  let ⟨u, hu⟩ := hu
  hu ▸ isCoprime_group_smul_left u y z

/--
theorem `isCoprime_mul_unit_left_right` / 定理 `isCoprime_mul_unit_left_right`

English:
theorem isCoprime_mul_unit_left_right
  given: (hu : IsUnit x) (y z : R)
  proof: let ⟨u, hu⟩ := hu
  hu ▸ isCoprime_group_smul_right u y z

中文:
定理 isCoprime_mul_unit_left_right
  条件: (hu : 是单位 x) (y z : R)
  证明: let ⟨u, hu⟩ := hu
  hu ▸ isCoprime_group_smul_right u y z

Depends on / 依赖: isCoprime_group_smul_right
-/
theorem isCoprime_mul_unit_left_right (hu : IsUnit x) (y z : R) :
    IsCoprime y (x * z) ↔ IsCoprime y z :=
  let ⟨u, hu⟩ := hu
  hu ▸ isCoprime_group_smul_right u y z

/--
theorem `isCoprime_mul_unit_right_left` / 定理 `isCoprime_mul_unit_right_left`

English:
theorem isCoprime_mul_unit_right_left
  given: (hu : IsUnit x) (y z : R)
  proof: mul_comm x y ▸ isCoprime_mul_unit_left_left hu y z

中文:
定理 isCoprime_mul_unit_right_left
  条件: (hu : 是单位 x) (y z : R)
  证明: mul_comm x y ▸ isCoprime_mul_unit_left_left hu y z

Depends on / 依赖: isCoprime_mul_unit_left_left, mul_comm
-/
theorem isCoprime_mul_unit_right_left (hu : IsUnit x) (y z : R) :
    IsCoprime (y * x) z ↔ IsCoprime y z :=
  mul_comm x y ▸ isCoprime_mul_unit_left_left hu y z

/--
theorem `isCoprime_mul_unit_right_right` / 定理 `isCoprime_mul_unit_right_right`

English:
theorem isCoprime_mul_unit_right_right
  given: (hu : IsUnit x) (y z : R)
  proof: mul_comm x z ▸ isCoprime_mul_unit_left_right hu y z

中文:
定理 isCoprime_mul_unit_right_right
  条件: (hu : 是单位 x) (y z : R)
  证明: mul_comm x z ▸ isCoprime_mul_unit_left_right hu y z

Depends on / 依赖: isCoprime_mul_unit_left_right, mul_comm
-/
theorem isCoprime_mul_unit_right_right (hu : IsUnit x) (y z : R) :
    IsCoprime y (z * x) ↔ IsCoprime y z :=
  mul_comm x z ▸ isCoprime_mul_unit_left_right hu y z

/--
theorem `isCoprime_mul_units_left` / 定理 `isCoprime_mul_units_left`

English:
theorem isCoprime_mul_units_left
  given: (hu : IsUnit u) (hv : IsUnit v) (y z : R)
  proof: Iff.trans
    (isCoprime_mul_unit_left_left hu _ _)
    (isCoprime_mul_unit_left_right hv _ _)

中文:
定理 isCoprime_mul_units_left
  条件: (hu : 是单位 u) (hv : 是单位 v) (y z : R)
  证明: Iff.trans
    (isCoprime_mul_unit_left_left hu _ _)
    (isCoprime_mul_unit_left_right hv _ _)

Depends on / 依赖: Iff.trans, isCoprime_mul_unit_left_left, isCoprime_mul_unit_left_right
-/
theorem isCoprime_mul_units_left (hu : IsUnit u) (hv : IsUnit v) (y z : R) :
    IsCoprime (u * y) (v * z) ↔ IsCoprime y z :=
  Iff.trans
    (isCoprime_mul_unit_left_left hu _ _)
    (isCoprime_mul_unit_left_right hv _ _)

/--
theorem `isCoprime_mul_units_right` / 定理 `isCoprime_mul_units_right`

English:
theorem isCoprime_mul_units_right
  given: (hu : IsUnit u) (hv : IsUnit v) (y z : R)
  proof: Iff.trans
    (isCoprime_mul_unit_right_left hu _ _)
    (isCoprime_mul_unit_right_right hv _ _)

中文:
定理 isCoprime_mul_units_right
  条件: (hu : 是单位 u) (hv : 是单位 v) (y z : R)
  证明: Iff.trans
    (isCoprime_mul_unit_right_left hu _ _)
    (isCoprime_mul_unit_right_right hv _ _)

Depends on / 依赖: Iff.trans, isCoprime_mul_unit_right_left, isCoprime_mul_unit_right_right
-/
theorem isCoprime_mul_units_right (hu : IsUnit u) (hv : IsUnit v) (y z : R) :
    IsCoprime (y * u) (z * v) ↔ IsCoprime y z :=
  Iff.trans
    (isCoprime_mul_unit_right_left hu _ _)
    (isCoprime_mul_unit_right_right hv _ _)

/--
theorem `isCoprime_mul_unit_left` / 定理 `isCoprime_mul_unit_left`

English:
theorem isCoprime_mul_unit_left
  given: (hu : IsUnit x) (y z : R)
  proof: isCoprime_mul_units_left hu hu _ _

中文:
定理 isCoprime_mul_unit_left
  条件: (hu : 是单位 x) (y z : R)
  证明: isCoprime_mul_units_left hu hu _ _

Depends on / 依赖: isCoprime_mul_units_left
-/
theorem isCoprime_mul_unit_left (hu : IsUnit x) (y z : R) :
    IsCoprime (x * y) (x * z) ↔ IsCoprime y z :=
  isCoprime_mul_units_left hu hu _ _

/--
theorem `isCoprime_mul_unit_right` / 定理 `isCoprime_mul_unit_right`

English:
theorem isCoprime_mul_unit_right
  given: (hu : IsUnit x) (y z : R)
  proof: isCoprime_mul_units_right hu hu _ _

中文:
定理 isCoprime_mul_unit_right
  条件: (hu : 是单位 x) (y z : R)
  证明: isCoprime_mul_units_right hu hu _ _

Depends on / 依赖: isCoprime_mul_units_right
-/
theorem isCoprime_mul_unit_right (hu : IsUnit x) (y z : R) :
    IsCoprime (y * x) (z * x) ↔ IsCoprime y z :=
  isCoprime_mul_units_right hu hu _ _

end CommSemiringUnit

namespace IsCoprime

section CommRing

variable {R : Type u} [CommRing R]

/--
theorem `add_mul_left_left` / 定理 `add_mul_left_left`

English:
theorem add_mul_left_left
  given: {x y : R} (h : IsCoprime x y) (z : R)
  statement: IsCoprime (x + y * z) y
  proof: @of_add_mul_left_left R _ _ _ (-z) by simpa only [mul_neg, add_neg_cancel_right] using h

中文:
定理 add_mul_left_left
  条件: {x y : R} (h : IsCoprime x y) (z : R)
  结论: IsCoprime (x + y * z) y
  证明: @of_add_mul_left_left R _ _ _ (-z) by simpa only [mul_neg, add_neg_cancel_right] using h

Depends on / 依赖: add_neg_cancel_right, mul_neg, of_add_mul_left_left
-/
theorem add_mul_left_left {x y : R} (h : IsCoprime x y) (z : R) : IsCoprime (x + y * z) y :=
@of_add_mul_left_left R _ _ _ (-z) by simpa only [mul_neg, add_neg_cancel_right] using h

/--
theorem `add_mul_right_left` / 定理 `add_mul_right_left`

English:
theorem add_mul_right_left
  given: {x y : R} (h : IsCoprime x y) (z : R)
  statement: IsCoprime (x + z * y) y
  proof: by
  rw [mul_comm]
  exact h.add_mul_left_left z

中文:
定理 add_mul_right_left
  条件: {x y : R} (h : IsCoprime x y) (z : R)
  结论: IsCoprime (x + z * y) y
  证明: by
  rw [mul_comm]
  exact h.add_mul_left_left z

Depends on / 依赖: add_mul_left_left, h.add_mul_left_left, mul_comm
-/
theorem add_mul_right_left {x y : R} (h : IsCoprime x y) (z : R) : IsCoprime (x + z * y) y := by
  rw [mul_comm]
  exact h.add_mul_left_left z

/--
theorem `add_mul_left_right` / 定理 `add_mul_left_right`

English:
theorem add_mul_left_right
  given: {x y : R} (h : IsCoprime x y) (z : R)
  statement: IsCoprime x (y + x * z)
  proof: by
  rw [isCoprime_comm]
  exact h.symm.add_mul_left_left z

中文:
定理 add_mul_left_right
  条件: {x y : R} (h : IsCoprime x y) (z : R)
  结论: IsCoprime x (y + x * z)
  证明: by
  rw [isCoprime_comm]
  exact h.symm.add_mul_left_left z

Depends on / 依赖: add_mul_left_left, h.symm.add_mul_left_left, isCoprime_comm
-/
theorem add_mul_left_right {x y : R} (h : IsCoprime x y) (z : R) : IsCoprime x (y + x * z) := by
  rw [isCoprime_comm]
  exact h.symm.add_mul_left_left z

/--
theorem `add_mul_right_right` / 定理 `add_mul_right_right`

English:
theorem add_mul_right_right
  given: {x y : R} (h : IsCoprime x y) (z : R)
  statement: IsCoprime x (y + z * x)
  proof: by
  rw [isCoprime_comm]
  exact h.symm.add_mul_right_left z

中文:
定理 add_mul_right_right
  条件: {x y : R} (h : IsCoprime x y) (z : R)
  结论: IsCoprime x (y + z * x)
  证明: by
  rw [isCoprime_comm]
  exact h.symm.add_mul_right_left z

Depends on / 依赖: add_mul_right_left, h.symm.add_mul_right_left, isCoprime_comm
-/
theorem add_mul_right_right {x y : R} (h : IsCoprime x y) (z : R) : IsCoprime x (y + z * x) := by
  rw [isCoprime_comm]
  exact h.symm.add_mul_right_left z

/--
theorem `mul_add_left_left` / 定理 `mul_add_left_left`

English:
theorem mul_add_left_left
  given: {x y : R} (h : IsCoprime x y) (z : R)
  statement: IsCoprime (y * z + x) y
  proof: by
  rw [add_comm]
  exact h.add_mul_left_left z

中文:
定理 mul_add_left_left
  条件: {x y : R} (h : IsCoprime x y) (z : R)
  结论: IsCoprime (y * z + x) y
  证明: by
  rw [add_comm]
  exact h.add_mul_left_left z

Depends on / 依赖: add_comm, add_mul_left_left, h.add_mul_left_left
-/
theorem mul_add_left_left {x y : R} (h : IsCoprime x y) (z : R) : IsCoprime (y * z + x) y := by
  rw [add_comm]
  exact h.add_mul_left_left z

/--
theorem `mul_add_right_left` / 定理 `mul_add_right_left`

English:
theorem mul_add_right_left
  given: {x y : R} (h : IsCoprime x y) (z : R)
  statement: IsCoprime (z * y + x) y
  proof: by
  rw [add_comm]
  exact h.add_mul_right_left z

中文:
定理 mul_add_right_left
  条件: {x y : R} (h : IsCoprime x y) (z : R)
  结论: IsCoprime (z * y + x) y
  证明: by
  rw [add_comm]
  exact h.add_mul_right_left z

Depends on / 依赖: add_comm, add_mul_right_left, h.add_mul_right_left
-/
theorem mul_add_right_left {x y : R} (h : IsCoprime x y) (z : R) : IsCoprime (z * y + x) y := by
  rw [add_comm]
  exact h.add_mul_right_left z

/--
theorem `mul_add_left_right` / 定理 `mul_add_left_right`

English:
theorem mul_add_left_right
  given: {x y : R} (h : IsCoprime x y) (z : R)
  statement: IsCoprime x (x * z + y)
  proof: by
  rw [add_comm]
  exact h.add_mul_left_right z

中文:
定理 mul_add_left_right
  条件: {x y : R} (h : IsCoprime x y) (z : R)
  结论: IsCoprime x (x * z + y)
  证明: by
  rw [add_comm]
  exact h.add_mul_left_right z

Depends on / 依赖: add_comm, add_mul_left_right, h.add_mul_left_right
-/
theorem mul_add_left_right {x y : R} (h : IsCoprime x y) (z : R) : IsCoprime x (x * z + y) := by
  rw [add_comm]
  exact h.add_mul_left_right z

/--
theorem `mul_add_right_right` / 定理 `mul_add_right_right`

English:
theorem mul_add_right_right
  given: {x y : R} (h : IsCoprime x y) (z : R)
  statement: IsCoprime x (z * x + y)
  proof: by
  rw [add_comm]
  exact h.add_mul_right_right z

中文:
定理 mul_add_right_right
  条件: {x y : R} (h : IsCoprime x y) (z : R)
  结论: IsCoprime x (z * x + y)
  证明: by
  rw [add_comm]
  exact h.add_mul_right_right z

Depends on / 依赖: add_comm, add_mul_right_right, h.add_mul_right_right
-/
theorem mul_add_right_right {x y : R} (h : IsCoprime x y) (z : R) : IsCoprime x (z * x + y) := by
  rw [add_comm]
  exact h.add_mul_right_right z

/--
theorem `add_mul_left_left_iff` / 定理 `add_mul_left_left_iff`

English:
theorem add_mul_left_left_iff
  given: {x y z : R}
  statement: IsCoprime (x + y * z) y ↔ IsCoprime x y
  proof: ⟨of_add_mul_left_left, fun h => h.add_mul_left_left z⟩

中文:
定理 add_mul_left_left_iff
  条件: {x y z : R}
  结论: IsCoprime (x + y * z) y ↔ IsCoprime x y
  证明: ⟨of_add_mul_left_left, fun h => h.add_mul_left_left z⟩
-/
@[simp] theorem add_mul_left_left_iff {x y z : R} : IsCoprime (x + y * z) y ↔ IsCoprime x y :=
  ⟨of_add_mul_left_left, fun h => h.add_mul_left_left z⟩

/--
theorem `add_mul_right_left_iff` / 定理 `add_mul_right_left_iff`

English:
theorem add_mul_right_left_iff
  given: {x y z : R}
  statement: IsCoprime (x + z * y) y ↔ IsCoprime x y
  proof: ⟨of_add_mul_right_left, fun h => h.add_mul_right_left z⟩

中文:
定理 add_mul_right_left_iff
  条件: {x y z : R}
  结论: IsCoprime (x + z * y) y ↔ IsCoprime x y
  证明: ⟨of_add_mul_right_left, fun h => h.add_mul_right_left z⟩
-/
@[simp] theorem add_mul_right_left_iff {x y z : R} : IsCoprime (x + z * y) y ↔ IsCoprime x y :=
  ⟨of_add_mul_right_left, fun h => h.add_mul_right_left z⟩

/--
theorem `add_mul_left_right_iff` / 定理 `add_mul_left_right_iff`

English:
theorem add_mul_left_right_iff
  given: {x y z : R}
  statement: IsCoprime x (y + x * z) ↔ IsCoprime x y
  proof: ⟨of_add_mul_left_right, fun h => h.add_mul_left_right z⟩

中文:
定理 add_mul_left_right_iff
  条件: {x y z : R}
  结论: IsCoprime x (y + x * z) ↔ IsCoprime x y
  证明: ⟨of_add_mul_left_right, fun h => h.add_mul_left_right z⟩
-/
@[simp] theorem add_mul_left_right_iff {x y z : R} : IsCoprime x (y + x * z) ↔ IsCoprime x y :=
  ⟨of_add_mul_left_right, fun h => h.add_mul_left_right z⟩

/--
theorem `add_mul_right_right_iff` / 定理 `add_mul_right_right_iff`

English:
theorem add_mul_right_right_iff
  given: {x y z : R}
  statement: IsCoprime x (y + z * x) ↔ IsCoprime x y
  proof: ⟨of_add_mul_right_right, fun h => h.add_mul_right_right z⟩

中文:
定理 add_mul_right_right_iff
  条件: {x y z : R}
  结论: IsCoprime x (y + z * x) ↔ IsCoprime x y
  证明: ⟨of_add_mul_right_right, fun h => h.add_mul_right_right z⟩
-/
@[simp] theorem add_mul_right_right_iff {x y z : R} : IsCoprime x (y + z * x) ↔ IsCoprime x y :=
  ⟨of_add_mul_right_right, fun h => h.add_mul_right_right z⟩

/--
theorem `mul_add_left_left_iff` / 定理 `mul_add_left_left_iff`

English:
theorem mul_add_left_left_iff
  given: {x y z : R}
  statement: IsCoprime (y * z + x) y ↔ IsCoprime x y
  proof: ⟨of_mul_add_left_left, fun h => h.mul_add_left_left z⟩

中文:
定理 mul_add_left_left_iff
  条件: {x y z : R}
  结论: IsCoprime (y * z + x) y ↔ IsCoprime x y
  证明: ⟨of_mul_add_left_left, fun h => h.mul_add_left_left z⟩
-/
@[simp] theorem mul_add_left_left_iff {x y z : R} : IsCoprime (y * z + x) y ↔ IsCoprime x y :=
  ⟨of_mul_add_left_left, fun h => h.mul_add_left_left z⟩

/--
theorem `mul_add_right_left_iff` / 定理 `mul_add_right_left_iff`

English:
theorem mul_add_right_left_iff
  given: {x y z : R}
  statement: IsCoprime (z * y + x) y ↔ IsCoprime x y
  proof: ⟨of_mul_add_right_left, fun h => h.mul_add_right_left z⟩

中文:
定理 mul_add_right_left_iff
  条件: {x y z : R}
  结论: IsCoprime (z * y + x) y ↔ IsCoprime x y
  证明: ⟨of_mul_add_right_left, fun h => h.mul_add_right_left z⟩
-/
@[simp] theorem mul_add_right_left_iff {x y z : R} : IsCoprime (z * y + x) y ↔ IsCoprime x y :=
  ⟨of_mul_add_right_left, fun h => h.mul_add_right_left z⟩

/--
theorem `mul_add_left_right_iff` / 定理 `mul_add_left_right_iff`

English:
theorem mul_add_left_right_iff
  given: {x y z : R}
  statement: IsCoprime x (x * z + y) ↔ IsCoprime x y
  proof: ⟨of_mul_add_left_right, fun h => h.mul_add_left_right z⟩

中文:
定理 mul_add_left_right_iff
  条件: {x y z : R}
  结论: IsCoprime x (x * z + y) ↔ IsCoprime x y
  证明: ⟨of_mul_add_left_right, fun h => h.mul_add_left_right z⟩
-/
@[simp] theorem mul_add_left_right_iff {x y z : R} : IsCoprime x (x * z + y) ↔ IsCoprime x y :=
  ⟨of_mul_add_left_right, fun h => h.mul_add_left_right z⟩

/--
theorem `mul_add_right_right_iff` / 定理 `mul_add_right_right_iff`

English:
theorem mul_add_right_right_iff
  given: {x y z : R}
  statement: IsCoprime x (z * x + y) ↔ IsCoprime x y
  proof: ⟨of_mul_add_right_right, fun h => h.mul_add_right_right z⟩

中文:
定理 mul_add_right_right_iff
  条件: {x y z : R}
  结论: IsCoprime x (z * x + y) ↔ IsCoprime x y
  证明: ⟨of_mul_add_right_right, fun h => h.mul_add_right_right z⟩
-/
@[simp] theorem mul_add_right_right_iff {x y z : R} : IsCoprime x (z * x + y) ↔ IsCoprime x y :=
  ⟨of_mul_add_right_right, fun h => h.mul_add_right_right z⟩

/--
theorem `neg_left` / 定理 `neg_left`

English:
theorem neg_left
  given: {x y : R} (h : IsCoprime x y)
  statement: IsCoprime (-x) y
  proof: by
  obtain ⟨a, b, h⟩ := h
  use -a, b
  rwa [neg_mul_neg]

中文:
定理 neg_left
  条件: {x y : R} (h : IsCoprime x y)
  结论: IsCoprime (-x) y
  证明: by
  obtain ⟨a, b, h⟩ := h
  use -a, b
  rwa [neg_mul_neg]

Depends on / 依赖: neg_mul_neg
-/
theorem neg_left {x y : R} (h : IsCoprime x y) : IsCoprime (-x) y := by
  obtain ⟨a, b, h⟩ := h
  use -a, b
  rwa [neg_mul_neg]

/--
theorem `neg_left_iff` / 定理 `neg_left_iff`

English:
theorem neg_left_iff
  given: (x y : R)
  statement: IsCoprime (-x) y ↔ IsCoprime x y
  proof: ⟨fun h => neg_neg x ▸ h.neg_left, neg_left⟩

中文:
定理 neg_left_iff
  条件: (x y : R)
  结论: IsCoprime (-x) y ↔ IsCoprime x y
  证明: ⟨fun h => neg_neg x ▸ h.neg_left, neg_left⟩

Depends on / 依赖: h.neg_left, neg_left, neg_neg
-/
theorem neg_left_iff (x y : R) : IsCoprime (-x) y ↔ IsCoprime x y :=
  ⟨fun h => neg_neg x ▸ h.neg_left, neg_left⟩

/--
theorem `neg_right` / 定理 `neg_right`

English:
theorem neg_right
  given: {x y : R} (h : IsCoprime x y)
  statement: IsCoprime x (-y)
  proof: h.symm.neg_left.symm

中文:
定理 neg_right
  条件: {x y : R} (h : IsCoprime x y)
  结论: IsCoprime x (-y)
  证明: h.symm.neg_left.symm

Depends on / 依赖: h.symm.neg_left.symm, neg_left
-/
theorem neg_right {x y : R} (h : IsCoprime x y) : IsCoprime x (-y) :=
  h.symm.neg_left.symm

/--
theorem `neg_right_iff` / 定理 `neg_right_iff`

English:
theorem neg_right_iff
  given: (x y : R)
  statement: IsCoprime x (-y) ↔ IsCoprime x y
  proof: ⟨fun h => neg_neg y ▸ h.neg_right, neg_right⟩

中文:
定理 neg_right_iff
  条件: (x y : R)
  结论: IsCoprime x (-y) ↔ IsCoprime x y
  证明: ⟨fun h => neg_neg y ▸ h.neg_right, neg_right⟩

Depends on / 依赖: h.neg_right, neg_neg, neg_right
-/
theorem neg_right_iff (x y : R) : IsCoprime x (-y) ↔ IsCoprime x y :=
  ⟨fun h => neg_neg y ▸ h.neg_right, neg_right⟩

/--
theorem `neg_neg` / 定理 `neg_neg`

English:
theorem neg_neg
  given: {x y : R} (h : IsCoprime x y)
  statement: IsCoprime (-x) (-y)
  proof: h.neg_left.neg_right

中文:
定理 neg_neg
  条件: {x y : R} (h : IsCoprime x y)
  结论: IsCoprime (-x) (-y)
  证明: h.neg_left.neg_right

Depends on / 依赖: h.neg_left.neg_right, neg_left, neg_right
-/
theorem neg_neg {x y : R} (h : IsCoprime x y) : IsCoprime (-x) (-y) :=
  h.neg_left.neg_right

/--
theorem `neg_neg_iff` / 定理 `neg_neg_iff`

English:
theorem neg_neg_iff
  given: (x y : R)
  statement: IsCoprime (-x) (-y) ↔ IsCoprime x y
  proof: (neg_left_iff _ _).trans (neg_right_iff _ _)

中文:
定理 neg_neg_iff
  条件: (x y : R)
  结论: IsCoprime (-x) (-y) ↔ IsCoprime x y
  证明: (neg_left_iff _ _).trans (neg_right_iff _ _)

Depends on / 依赖: neg_left_iff, neg_right_iff
-/
theorem neg_neg_iff (x y : R) : IsCoprime (-x) (-y) ↔ IsCoprime x y :=
  (neg_left_iff _ _).trans (neg_right_iff _ _)

/--
theorem `sub_mul_left_left_iff` / 定理 `sub_mul_left_left_iff`

English:
theorem sub_mul_left_left_iff
  given: {x y z : R}
  statement: IsCoprime (x - y * z) y ↔ IsCoprime x y
  proof: by
  rw [sub_eq_add_neg]; rw [← mul_neg]; rw [add_mul_left_left_iff]

中文:
定理 sub_mul_left_left_iff
  条件: {x y z : R}
  结论: IsCoprime (x - y * z) y ↔ IsCoprime x y
  证明: by
  rw [sub_eq_add_neg]; rw [← mul_neg]; rw [add_mul_left_left_iff]
-/
@[simp] theorem sub_mul_left_left_iff {x y z : R} : IsCoprime (x - y * z) y ↔ IsCoprime x y := by
  rw [sub_eq_add_neg]; rw [← mul_neg]; rw [add_mul_left_left_iff]

/--
theorem `sub_mul_right_left_iff` / 定理 `sub_mul_right_left_iff`

English:
theorem sub_mul_right_left_iff
  given: {x y z : R}
  statement: IsCoprime (x - z * y) y ↔ IsCoprime x y
  proof: by
  rw [sub_eq_add_neg]; rw [← neg_mul]; rw [add_mul_right_left_iff]

中文:
定理 sub_mul_right_left_iff
  条件: {x y z : R}
  结论: IsCoprime (x - z * y) y ↔ IsCoprime x y
  证明: by
  rw [sub_eq_add_neg]; rw [← neg_mul]; rw [add_mul_right_left_iff]
-/
@[simp] theorem sub_mul_right_left_iff {x y z : R} : IsCoprime (x - z * y) y ↔ IsCoprime x y := by
  rw [sub_eq_add_neg]; rw [← neg_mul]; rw [add_mul_right_left_iff]

/--
theorem `sub_mul_left_right_iff` / 定理 `sub_mul_left_right_iff`

English:
theorem sub_mul_left_right_iff
  given: {x y z : R}
  statement: IsCoprime x (y - x * z) ↔ IsCoprime x y
  proof: by
  rw [sub_eq_add_neg]; rw [← mul_neg]; rw [add_mul_left_right_iff]

中文:
定理 sub_mul_left_right_iff
  条件: {x y z : R}
  结论: IsCoprime x (y - x * z) ↔ IsCoprime x y
  证明: by
  rw [sub_eq_add_neg]; rw [← mul_neg]; rw [add_mul_left_right_iff]
-/
@[simp] theorem sub_mul_left_right_iff {x y z : R} : IsCoprime x (y - x * z) ↔ IsCoprime x y := by
  rw [sub_eq_add_neg]; rw [← mul_neg]; rw [add_mul_left_right_iff]

/--
theorem `sub_mul_right_right_iff` / 定理 `sub_mul_right_right_iff`

English:
theorem sub_mul_right_right_iff
  given: {x y z : R}
  statement: IsCoprime x (y - z * x) ↔ IsCoprime x y
  proof: by
  rw [sub_eq_add_neg]; rw [← neg_mul]; rw [add_mul_right_right_iff]

中文:
定理 sub_mul_right_right_iff
  条件: {x y z : R}
  结论: IsCoprime x (y - z * x) ↔ IsCoprime x y
  证明: by
  rw [sub_eq_add_neg]; rw [← neg_mul]; rw [add_mul_right_right_iff]
-/
@[simp] theorem sub_mul_right_right_iff {x y z : R} : IsCoprime x (y - z * x) ↔ IsCoprime x y := by
  rw [sub_eq_add_neg]; rw [← neg_mul]; rw [add_mul_right_right_iff]

/--
theorem `mul_sub_left_left_iff` / 定理 `mul_sub_left_left_iff`

English:
theorem mul_sub_left_left_iff
  given: {x y z : R}
  statement: IsCoprime (y * z - x) y ↔ IsCoprime x y
  proof: by
  rw [sub_eq_neg_add]; rw [add_mul_left_left_iff]; rw [neg_left_iff]

中文:
定理 mul_sub_left_left_iff
  条件: {x y z : R}
  结论: IsCoprime (y * z - x) y ↔ IsCoprime x y
  证明: by
  rw [sub_eq_neg_add]; rw [add_mul_left_left_iff]; rw [neg_left_iff]
-/
@[simp] theorem mul_sub_left_left_iff {x y z : R} : IsCoprime (y * z - x) y ↔ IsCoprime x y := by
  rw [sub_eq_neg_add]; rw [add_mul_left_left_iff]; rw [neg_left_iff]

/--
theorem `mul_sub_right_left_iff` / 定理 `mul_sub_right_left_iff`

English:
theorem mul_sub_right_left_iff
  given: {x y z : R}
  statement: IsCoprime (z * y - x) y ↔ IsCoprime x y
  proof: by
  rw [sub_eq_neg_add]; rw [add_mul_right_left_iff]; rw [neg_left_iff]

中文:
定理 mul_sub_right_left_iff
  条件: {x y z : R}
  结论: IsCoprime (z * y - x) y ↔ IsCoprime x y
  证明: by
  rw [sub_eq_neg_add]; rw [add_mul_right_left_iff]; rw [neg_left_iff]
-/
@[simp] theorem mul_sub_right_left_iff {x y z : R} : IsCoprime (z * y - x) y ↔ IsCoprime x y := by
  rw [sub_eq_neg_add]; rw [add_mul_right_left_iff]; rw [neg_left_iff]

/--
theorem `mul_sub_left_right_iff` / 定理 `mul_sub_left_right_iff`

English:
theorem mul_sub_left_right_iff
  given: {x y z : R}
  statement: IsCoprime x (x * z - y) ↔ IsCoprime x y
  proof: by
  rw [sub_eq_add_neg]; rw [mul_add_left_right_iff]; rw [neg_right_iff]

中文:
定理 mul_sub_left_right_iff
  条件: {x y z : R}
  结论: IsCoprime x (x * z - y) ↔ IsCoprime x y
  证明: by
  rw [sub_eq_add_neg]; rw [mul_add_left_right_iff]; rw [neg_right_iff]
-/
@[simp] theorem mul_sub_left_right_iff {x y z : R} : IsCoprime x (x * z - y) ↔ IsCoprime x y := by
  rw [sub_eq_add_neg]; rw [mul_add_left_right_iff]; rw [neg_right_iff]

/--
theorem `mul_sub_right_right_iff` / 定理 `mul_sub_right_right_iff`

English:
theorem mul_sub_right_right_iff
  given: {x y z : R}
  statement: IsCoprime x (z * x - y) ↔ IsCoprime x y
  proof: by
  rw [sub_eq_add_neg]; rw [mul_add_right_right_iff]; rw [neg_right_iff]

中文:
定理 mul_sub_right_right_iff
  条件: {x y z : R}
  结论: IsCoprime x (z * x - y) ↔ IsCoprime x y
  证明: by
  rw [sub_eq_add_neg]; rw [mul_add_right_right_iff]; rw [neg_right_iff]
-/
@[simp] theorem mul_sub_right_right_iff {x y z : R} : IsCoprime x (z * x - y) ↔ IsCoprime x y := by
  rw [sub_eq_add_neg]; rw [mul_add_right_right_iff]; rw [neg_right_iff]

/--
lemma `add_one_left_of_dvd` / 引理 `add_one_left_of_dvd`

English:
lemma add_one_left_of_dvd
  given: {x y : R} (h : y ∣ x)
  statement: IsCoprime (x + 1) y
  proof: by
  obtain ⟨z, rfl⟩ := h
  rw [mul_add_left_left_iff]
  exact isCoprime_one_left

中文:
引理 add_one_left_of_dvd
  条件: {x y : R} (h : y ∣ x)
  结论: IsCoprime (x + 1) y
  证明: by
  obtain ⟨z, rfl⟩ := h
  rw [mul_add_left_left_iff]
  exact isCoprime_one_left

Depends on / 依赖: isCoprime_one_left, mul_add_left_left_iff
-/
lemma add_one_left_of_dvd {x y : R} (h : y ∣ x) : IsCoprime (x + 1) y := by
  obtain ⟨z, rfl⟩ := h
  rw [mul_add_left_left_iff]
  exact isCoprime_one_left

/--
lemma `add_one_right_of_dvd` / 引理 `add_one_right_of_dvd`

English:
lemma add_one_right_of_dvd
  given: {x y : R} (h : x ∣ y)
  statement: IsCoprime x (y + 1)
  proof: isCoprime_comm.mp (add_one_left_of_dvd h)

中文:
引理 add_one_right_of_dvd
  条件: {x y : R} (h : x ∣ y)
  结论: IsCoprime x (y + 1)
  证明: isCoprime_comm.mp (add_one_left_of_dvd h)

Depends on / 依赖: add_one_left_of_dvd, isCoprime_comm, isCoprime_comm.mp
-/
lemma add_one_right_of_dvd {x y : R} (h : x ∣ y) : IsCoprime x (y + 1) :=
  isCoprime_comm.mp (add_one_left_of_dvd h)

/--
lemma `sub_one_left_of_dvd` / 引理 `sub_one_left_of_dvd`

English:
lemma sub_one_left_of_dvd
  given: {x y : R} (h : y ∣ x)
  statement: IsCoprime (x - 1) y
  proof: by
  rw [← neg_sub]; rw [neg_left_iff]; rw [sub_eq_neg_add]
  exact add_one_left_of_dvd h.neg_right

中文:
引理 sub_one_left_of_dvd
  条件: {x y : R} (h : y ∣ x)
  结论: IsCoprime (x - 1) y
  证明: by
  rw [← neg_sub]; rw [neg_left_iff]; rw [sub_eq_neg_add]
  exact add_one_left_of_dvd h.neg_right

Depends on / 依赖: add_one_left_of_dvd, h.neg_right, neg_left_iff, neg_right, neg_sub, sub_eq_neg_add
-/
lemma sub_one_left_of_dvd {x y : R} (h : y ∣ x) : IsCoprime (x - 1) y := by
  rw [← neg_sub]; rw [neg_left_iff]; rw [sub_eq_neg_add]
  exact add_one_left_of_dvd h.neg_right

/--
lemma `sub_one_right_of_dvd` / 引理 `sub_one_right_of_dvd`

English:
lemma sub_one_right_of_dvd
  given: {x y : R} (h : x ∣ y)
  statement: IsCoprime x (y - 1)
  proof: isCoprime_comm.mp (sub_one_left_of_dvd h)

中文:
引理 sub_one_right_of_dvd
  条件: {x y : R} (h : x ∣ y)
  结论: IsCoprime x (y - 1)
  证明: isCoprime_comm.mp (sub_one_left_of_dvd h)

Depends on / 依赖: isCoprime_comm, isCoprime_comm.mp, sub_one_left_of_dvd
-/
lemma sub_one_right_of_dvd {x y : R} (h : x ∣ y) : IsCoprime x (y - 1) :=
  isCoprime_comm.mp (sub_one_left_of_dvd h)

/--
lemma `add_one_sub_one_of_two_dvd` / 引理 `add_one_sub_one_of_two_dvd`

English:
lemma add_one_sub_one_of_two_dvd
  given: {x : R} (h : 2 ∣ x)
  statement: IsCoprime (x + 1) (x - 1)
  proof: by
  simpa [show 2 + (x - 1) = x + 1 by ring] using add_mul_left_left (sub_one_right_of_dvd h) 1

中文:
引理 add_one_sub_one_of_two_dvd
  条件: {x : R} (h : 2 ∣ x)
  结论: IsCoprime (x + 1) (x - 1)
  证明: by
  simpa [show 2 + (x - 1) = x + 1 by ring] using add_mul_left_left (sub_one_right_of_dvd h) 1

Depends on / 依赖: add_mul_left_left, sub_one_right_of_dvd
-/
lemma add_one_sub_one_of_two_dvd {x : R} (h : 2 ∣ x) : IsCoprime (x + 1) (x - 1) := by
  simpa [show 2 + (x - 1) = x + 1 by ring] using add_mul_left_left (sub_one_right_of_dvd h) 1

section abs

variable [LinearOrder R] [AddLeftMono R]

/--
lemma `abs_left_iff` / 引理 `abs_left_iff`

English:
lemma abs_left_iff
  given: (x y : R)
  statement: IsCoprime |x| y ↔ IsCoprime x y
  proof: by
  cases le_or_gt 0 x with
  | inl h => rw [abs_of_nonneg h]
  | inr h => rw [abs_of_neg h, IsCoprime.neg_left_iff]

.2 h lemma abs_left {x y : R} (h : IsCoprime x y) : IsCoprime |x| y := abs_left_iff _ _

中文:
引理 abs_left_iff
  条件: (x y : R)
  结论: IsCoprime |x| y ↔ IsCoprime x y
  证明: by
  cases le_or_gt 0 x with
  | inl h => rw [abs_of_nonneg h]
  | inr h => rw [abs_of_neg h, IsCoprime.neg_left_iff]

.2 h lemma abs_left {x y : R} (h : IsCoprime x y) : IsCoprime |x| y := abs_left_iff _ _

Depends on / 依赖: IsCoprime, IsCoprime.neg_left_iff, abs_of_neg, abs_of_nonneg, le_or_gt, neg_left_iff
-/
lemma abs_left_iff (x y : R) : IsCoprime |x| y ↔ IsCoprime x y := by
  cases le_or_gt 0 x with
  | inl h => rw [abs_of_nonneg h]
  | inr h => rw [abs_of_neg h, IsCoprime.neg_left_iff]

.2 h lemma abs_left {x y : R} (h : IsCoprime x y) : IsCoprime |x| y := abs_left_iff _ _

/--
lemma `abs_right_iff` / 引理 `abs_right_iff`

English:
lemma abs_right_iff
  given: (x y : R)
  statement: IsCoprime x |y| ↔ IsCoprime x y
  proof: by
  rw [isCoprime_comm]; rw [IsCoprime.abs_left_iff]; rw [isCoprime_comm]

.2 h lemma abs_right {x y : R} (h : IsCoprime x y) : IsCoprime x |y| := abs_right_iff _ _

中文:
引理 abs_right_iff
  条件: (x y : R)
  结论: IsCoprime x |y| ↔ IsCoprime x y
  证明: by
  rw [isCoprime_comm]; rw [IsCoprime.abs_left_iff]; rw [isCoprime_comm]

.2 h lemma abs_right {x y : R} (h : IsCoprime x y) : IsCoprime x |y| := abs_right_iff _ _

Depends on / 依赖: IsCoprime, IsCoprime.abs_left_iff, abs_left_iff, isCoprime_comm
-/
lemma abs_right_iff (x y : R) : IsCoprime x |y| ↔ IsCoprime x y := by
  rw [isCoprime_comm]; rw [IsCoprime.abs_left_iff]; rw [isCoprime_comm]

.2 h lemma abs_right {x y : R} (h : IsCoprime x y) : IsCoprime x |y| := abs_right_iff _ _

/--
theorem `abs_abs_iff` / 定理 `abs_abs_iff`

English:
theorem abs_abs_iff
  given: (x y : R)
  statement: IsCoprime |x| |y| ↔ IsCoprime x y
  proof: (abs_left_iff _ _).trans (abs_right_iff _ _)

中文:
定理 abs_abs_iff
  条件: (x y : R)
  结论: IsCoprime |x| |y| ↔ IsCoprime x y
  证明: (abs_left_iff _ _).trans (abs_right_iff _ _)

Depends on / 依赖: abs_left_iff, abs_right_iff
-/
theorem abs_abs_iff (x y : R) : IsCoprime |x| |y| ↔ IsCoprime x y :=
  (abs_left_iff _ _).trans (abs_right_iff _ _)

/--
theorem `abs_abs` / 定理 `abs_abs`

English:
theorem abs_abs
  given: {x y : R} (h : IsCoprime x y)
  statement: IsCoprime |x| |y|
  proof: h.abs_left.abs_right

中文:
定理 abs_abs
  条件: {x y : R} (h : IsCoprime x y)
  结论: IsCoprime |x| |y|
  证明: h.abs_left.abs_right

Depends on / 依赖: abs_left, abs_right, h.abs_left.abs_right
-/
theorem abs_abs {x y : R} (h : IsCoprime x y) : IsCoprime |x| |y| := h.abs_left.abs_right

end abs

end CommRing

/--
theorem `sq_add_sq_ne_zero` / 定理 `sq_add_sq_ne_zero`

English:
theorem sq_add_sq_ne_zero
  statement: {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
  proof: by
  intro h'
  obtain ⟨ha, hb⟩ := (add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _)).mp h'
  obtain rfl := eq_zero_of_pow_eq_zero ha
  obtain rfl := eq_zero_of_pow_eq_zero hb
  exact not_isCoprime_zero_zero h

中文:
定理 sq_add_sq_ne_zero
  结论: {R : 类型} [交换环 R] [线性序 R] [是StrictOrdered环 R]
  证明: by
  intro h'
  obtain ⟨ha, hb⟩ := (add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _)).mp h'
  obtain rfl := eq_zero_of_pow_eq_zero ha
  obtain rfl := eq_zero_of_pow_eq_zero hb
  exact not_isCoprime_zero_zero h

Depends on / 依赖: add_eq_zero_iff_of_nonneg, eq_zero_of_pow_eq_zero, not_isCoprime_zero_zero, sq_nonneg
-/
theorem sq_add_sq_ne_zero {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    {a b : R} (h : IsCoprime a b) :
    a ^ 2 + b ^ 2 != 0 := by
  intro h'
  obtain ⟨ha, hb⟩ := (add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _)).mp h'
  obtain rfl := eq_zero_of_pow_eq_zero ha
  obtain rfl := eq_zero_of_pow_eq_zero hb
  exact not_isCoprime_zero_zero h

end IsCoprime

/-- `IsCoprime` is not a useful definition for `Nat`; consider using `Nat.Coprime` instead. -/
@[simp]
/--
lemma `Nat.isCoprime_iff` / 引理 `Nat.isCoprime_iff`

English:
lemma Nat.isCoprime_iff
  given: {m n : Nat}
  statement: IsCoprime m n ↔ m = 1 ∨ n = 1
  proof: by
  refine ⟨fun ⟨a, b, H⟩ => ?_, fun h => ?_⟩
  · simp_rw [Nat.add_eq_one_iff, mul_eq_one, mul_eq_zero] at H
    exact H.symm.imp (·.1.2) (·.2.2)
  · obtain rfl | rfl := h
    · exact isCoprime_one_left
    · exact isCoprime_one_right

中文:
引理 自然数.isCoprime_iff
  条件: {m n : 自然数}
  结论: IsCoprime m n ↔ m = 1 ∨ n = 1
  证明: by
  refine ⟨fun ⟨a, b, H⟩ => ?_, fun h => ?_⟩
  · simp_rw [Nat.add_eq_one_iff, mul_eq_one, mul_eq_zero] at H
    exact H.symm.imp (·.1.2) (·.2.2)
  · obtain rfl | rfl := h
    · exact isCoprime_one_left
    · exact isCoprime_one_right

Depends on / 依赖: H.symm.imp, Nat.add_eq_one_iff, add_eq_one_iff, isCoprime_one_left, isCoprime_one_right, mul_eq_one, mul_eq_zero, simp_rw
-/
lemma Nat.isCoprime_iff {m n : Nat} : IsCoprime m n ↔ m = 1 ∨ n = 1 := by
  refine ⟨fun ⟨a, b, H⟩ => ?_, fun h => ?_⟩
  · simp_rw [Nat.add_eq_one_iff, mul_eq_one, mul_eq_zero] at H
    exact H.symm.imp (·.1.2) (·.2.2)
  · obtain rfl | rfl := h
    · exact isCoprime_one_left
    · exact isCoprime_one_right

/--
lemma `PNat.isCoprime_iff` / 引理 `PNat.isCoprime_iff`

English:
lemma PNat.isCoprime_iff
  given: {m n : Nat+}
  statement: IsCoprime (m : Nat) n ↔ m = 1 ∨ n = 1
  proof: by simp

中文:
引理 正自然数.isCoprime_iff
  条件: {m n : 自然数+}
  结论: IsCoprime (m : 自然数) n ↔ m = 1 ∨ n = 1
  证明: by simp
-/
lemma PNat.isCoprime_iff {m n : Nat+} : IsCoprime (m : Nat) n ↔ m = 1 ∨ n = 1 := by simp

/-- `IsCoprime` is not a useful definition if an inverse is available. -/
@[simp]
/--
lemma `Semifield.isCoprime_iff` / 引理 `Semifield.isCoprime_iff`

English:
lemma Semifield.isCoprime_iff
  given: {R : Type*} [Semifield R] {m n : R}
  proof: by
  obtain rfl | hn := eq_or_ne n 0
  · simp [isCoprime_zero_right]
  suffices IsCoprime m n by simpa [hn]
  refine ⟨0, n⁻¹, ?_⟩
  simp [inv_mul_cancel₀ hn]

中文:
引理 半域.isCoprime_iff
  条件: {R : 类型} [半域 R] {m n : R}
  证明: by
  obtain rfl | hn := eq_or_ne n 0
  · simp [isCoprime_zero_right]
  suffices IsCoprime m n by simpa [hn]
  refine ⟨0, n⁻¹, ?_⟩
  simp [inv_mul_cancel₀ hn]

Depends on / 依赖: IsCoprime, eq_or_ne, isCoprime_zero_right
-/
lemma Semifield.isCoprime_iff {R : Type*} [Semifield R] {m n : R} :
    IsCoprime m n ↔ m != 0 ∨ n != 0 := by
  obtain rfl | hn := eq_or_ne n 0
  · simp [isCoprime_zero_right]
  suffices IsCoprime m n by simpa [hn]
  refine ⟨0, n⁻¹, ?_⟩
  simp [inv_mul_cancel₀ hn]

namespace IsRelPrime

variable {R} [CommRing R] {x y : R}

/--
theorem `add_mul_left_left` / 定理 `add_mul_left_left`

English:
theorem add_mul_left_left
  given: (h : IsRelPrime x y) (z : R)
  statement: IsRelPrime (x + y * z) y
  proof: @of_add_mul_left_left R _ _ _ (-z) by simpa only [mul_neg, add_neg_cancel_right] using h

中文:
定理 add_mul_left_left
  条件: (h : IsRelPrime x y) (z : R)
  结论: IsRelPrime (x + y * z) y
  证明: @of_add_mul_left_left R _ _ _ (-z) by simpa only [mul_neg, add_neg_cancel_right] using h

Depends on / 依赖: add_neg_cancel_right, mul_neg, of_add_mul_left_left
-/
theorem add_mul_left_left (h : IsRelPrime x y) (z : R) : IsRelPrime (x + y * z) y :=
@of_add_mul_left_left R _ _ _ (-z) by simpa only [mul_neg, add_neg_cancel_right] using h

/--
theorem `add_mul_right_left` / 定理 `add_mul_right_left`

English:
theorem add_mul_right_left
  given: (h : IsRelPrime x y) (z : R)
  statement: IsRelPrime (x + z * y) y
  proof: mul_comm z y ▸ h.add_mul_left_left z

中文:
定理 add_mul_right_left
  条件: (h : IsRelPrime x y) (z : R)
  结论: IsRelPrime (x + z * y) y
  证明: mul_comm z y ▸ h.add_mul_left_left z

Depends on / 依赖: add_mul_left_left, h.add_mul_left_left, mul_comm
-/
theorem add_mul_right_left (h : IsRelPrime x y) (z : R) : IsRelPrime (x + z * y) y :=
  mul_comm z y ▸ h.add_mul_left_left z

/--
theorem `add_mul_left_right` / 定理 `add_mul_left_right`

English:
theorem add_mul_left_right
  given: (h : IsRelPrime x y) (z : R)
  statement: IsRelPrime x (y + x * z)
  proof: (h.symm.add_mul_left_left z).symm

中文:
定理 add_mul_left_right
  条件: (h : IsRelPrime x y) (z : R)
  结论: IsRelPrime x (y + x * z)
  证明: (h.symm.add_mul_left_left z).symm

Depends on / 依赖: add_mul_left_left, h.symm.add_mul_left_left
-/
theorem add_mul_left_right (h : IsRelPrime x y) (z : R) : IsRelPrime x (y + x * z) :=
  (h.symm.add_mul_left_left z).symm

/--
theorem `add_mul_right_right` / 定理 `add_mul_right_right`

English:
theorem add_mul_right_right
  given: (h : IsRelPrime x y) (z : R)
  statement: IsRelPrime x (y + z * x)
  proof: (h.symm.add_mul_right_left z).symm

中文:
定理 add_mul_right_right
  条件: (h : IsRelPrime x y) (z : R)
  结论: IsRelPrime x (y + z * x)
  证明: (h.symm.add_mul_right_left z).symm

Depends on / 依赖: add_mul_right_left, h.symm.add_mul_right_left
-/
theorem add_mul_right_right (h : IsRelPrime x y) (z : R) : IsRelPrime x (y + z * x) :=
  (h.symm.add_mul_right_left z).symm

/--
theorem `mul_add_left_left` / 定理 `mul_add_left_left`

English:
theorem mul_add_left_left
  given: (h : IsRelPrime x y) (z : R)
  statement: IsRelPrime (y * z + x) y
  proof: add_comm x _ ▸ h.add_mul_left_left z

中文:
定理 mul_add_left_left
  条件: (h : IsRelPrime x y) (z : R)
  结论: IsRelPrime (y * z + x) y
  证明: add_comm x _ ▸ h.add_mul_left_left z

Depends on / 依赖: add_comm, add_mul_left_left, h.add_mul_left_left
-/
theorem mul_add_left_left (h : IsRelPrime x y) (z : R) : IsRelPrime (y * z + x) y :=
  add_comm x _ ▸ h.add_mul_left_left z

/--
theorem `mul_add_right_left` / 定理 `mul_add_right_left`

English:
theorem mul_add_right_left
  given: (h : IsRelPrime x y) (z : R)
  statement: IsRelPrime (z * y + x) y
  proof: add_comm x _ ▸ h.add_mul_right_left z

中文:
定理 mul_add_right_left
  条件: (h : IsRelPrime x y) (z : R)
  结论: IsRelPrime (z * y + x) y
  证明: add_comm x _ ▸ h.add_mul_right_left z

Depends on / 依赖: add_comm, add_mul_right_left, h.add_mul_right_left
-/
theorem mul_add_right_left (h : IsRelPrime x y) (z : R) : IsRelPrime (z * y + x) y :=
  add_comm x _ ▸ h.add_mul_right_left z

/--
theorem `mul_add_left_right` / 定理 `mul_add_left_right`

English:
theorem mul_add_left_right
  given: (h : IsRelPrime x y) (z : R)
  statement: IsRelPrime x (x * z + y)
  proof: add_comm y _ ▸ h.add_mul_left_right z

中文:
定理 mul_add_left_right
  条件: (h : IsRelPrime x y) (z : R)
  结论: IsRelPrime x (x * z + y)
  证明: add_comm y _ ▸ h.add_mul_left_right z

Depends on / 依赖: add_comm, add_mul_left_right, h.add_mul_left_right
-/
theorem mul_add_left_right (h : IsRelPrime x y) (z : R) : IsRelPrime x (x * z + y) :=
  add_comm y _ ▸ h.add_mul_left_right z

/--
theorem `mul_add_right_right` / 定理 `mul_add_right_right`

English:
theorem mul_add_right_right
  given: (h : IsRelPrime x y) (z : R)
  statement: IsRelPrime x (z * x + y)
  proof: add_comm y _ ▸ h.add_mul_right_right z

中文:
定理 mul_add_right_right
  条件: (h : IsRelPrime x y) (z : R)
  结论: IsRelPrime x (z * x + y)
  证明: add_comm y _ ▸ h.add_mul_right_right z

Depends on / 依赖: add_comm, add_mul_right_right, h.add_mul_right_right
-/
theorem mul_add_right_right (h : IsRelPrime x y) (z : R) : IsRelPrime x (z * x + y) :=
  add_comm y _ ▸ h.add_mul_right_right z

variable {z}

/--
theorem `add_mul_left_left_iff` / 定理 `add_mul_left_left_iff`

English:
theorem add_mul_left_left_iff
  statement: IsRelPrime (x + y * z) y ↔ IsRelPrime x y
  proof: ⟨of_add_mul_left_left, fun h => h.add_mul_left_left z⟩

中文:
定理 add_mul_left_left_iff
  结论: IsRelPrime (x + y * z) y ↔ IsRelPrime x y
  证明: ⟨of_add_mul_left_left, fun h => h.add_mul_left_left z⟩
-/
@[simp] theorem add_mul_left_left_iff : IsRelPrime (x + y * z) y ↔ IsRelPrime x y :=
  ⟨of_add_mul_left_left, fun h => h.add_mul_left_left z⟩

/--
theorem `add_mul_right_left_iff` / 定理 `add_mul_right_left_iff`

English:
theorem add_mul_right_left_iff
  statement: IsRelPrime (x + z * y) y ↔ IsRelPrime x y
  proof: ⟨of_add_mul_right_left, fun h => h.add_mul_right_left z⟩

中文:
定理 add_mul_right_left_iff
  结论: IsRelPrime (x + z * y) y ↔ IsRelPrime x y
  证明: ⟨of_add_mul_right_left, fun h => h.add_mul_right_left z⟩
-/
@[simp] theorem add_mul_right_left_iff : IsRelPrime (x + z * y) y ↔ IsRelPrime x y :=
  ⟨of_add_mul_right_left, fun h => h.add_mul_right_left z⟩

/--
theorem `add_mul_left_right_iff` / 定理 `add_mul_left_right_iff`

English:
theorem add_mul_left_right_iff
  statement: IsRelPrime x (y + x * z) ↔ IsRelPrime x y
  proof: ⟨of_add_mul_left_right, fun h => h.add_mul_left_right z⟩

中文:
定理 add_mul_left_right_iff
  结论: IsRelPrime x (y + x * z) ↔ IsRelPrime x y
  证明: ⟨of_add_mul_left_right, fun h => h.add_mul_left_right z⟩
-/
@[simp] theorem add_mul_left_right_iff : IsRelPrime x (y + x * z) ↔ IsRelPrime x y :=
  ⟨of_add_mul_left_right, fun h => h.add_mul_left_right z⟩

/--
theorem `add_mul_right_right_iff` / 定理 `add_mul_right_right_iff`

English:
theorem add_mul_right_right_iff
  statement: IsRelPrime x (y + z * x) ↔ IsRelPrime x y
  proof: ⟨of_add_mul_right_right, fun h => h.add_mul_right_right z⟩

中文:
定理 add_mul_right_right_iff
  结论: IsRelPrime x (y + z * x) ↔ IsRelPrime x y
  证明: ⟨of_add_mul_right_right, fun h => h.add_mul_right_right z⟩
-/
@[simp] theorem add_mul_right_right_iff : IsRelPrime x (y + z * x) ↔ IsRelPrime x y :=
  ⟨of_add_mul_right_right, fun h => h.add_mul_right_right z⟩

/--
theorem `mul_add_left_left_iff` / 定理 `mul_add_left_left_iff`

English:
theorem mul_add_left_left_iff
  statement: IsRelPrime (y * z + x) y ↔ IsRelPrime x y
  proof: ⟨of_mul_add_left_left, fun h => h.mul_add_left_left z⟩

中文:
定理 mul_add_left_left_iff
  结论: IsRelPrime (y * z + x) y ↔ IsRelPrime x y
  证明: ⟨of_mul_add_left_left, fun h => h.mul_add_left_left z⟩
-/
@[simp] theorem mul_add_left_left_iff : IsRelPrime (y * z + x) y ↔ IsRelPrime x y :=
  ⟨of_mul_add_left_left, fun h => h.mul_add_left_left z⟩

/--
theorem `mul_add_right_left_iff` / 定理 `mul_add_right_left_iff`

English:
theorem mul_add_right_left_iff
  statement: IsRelPrime (z * y + x) y ↔ IsRelPrime x y
  proof: ⟨of_mul_add_right_left, fun h => h.mul_add_right_left z⟩

中文:
定理 mul_add_right_left_iff
  结论: IsRelPrime (z * y + x) y ↔ IsRelPrime x y
  证明: ⟨of_mul_add_right_left, fun h => h.mul_add_right_left z⟩
-/
@[simp] theorem mul_add_right_left_iff : IsRelPrime (z * y + x) y ↔ IsRelPrime x y :=
  ⟨of_mul_add_right_left, fun h => h.mul_add_right_left z⟩

/--
theorem `mul_add_left_right_iff` / 定理 `mul_add_left_right_iff`

English:
theorem mul_add_left_right_iff
  statement: IsRelPrime x (x * z + y) ↔ IsRelPrime x y
  proof: ⟨of_mul_add_left_right, fun h => h.mul_add_left_right z⟩

中文:
定理 mul_add_left_right_iff
  结论: IsRelPrime x (x * z + y) ↔ IsRelPrime x y
  证明: ⟨of_mul_add_left_right, fun h => h.mul_add_left_right z⟩
-/
@[simp] theorem mul_add_left_right_iff : IsRelPrime x (x * z + y) ↔ IsRelPrime x y :=
  ⟨of_mul_add_left_right, fun h => h.mul_add_left_right z⟩

/--
theorem `mul_add_right_right_iff` / 定理 `mul_add_right_right_iff`

English:
theorem mul_add_right_right_iff
  statement: IsRelPrime x (z * x + y) ↔ IsRelPrime x y
  proof: ⟨of_mul_add_right_right, fun h => h.mul_add_right_right z⟩

中文:
定理 mul_add_right_right_iff
  结论: IsRelPrime x (z * x + y) ↔ IsRelPrime x y
  证明: ⟨of_mul_add_right_right, fun h => h.mul_add_right_right z⟩
-/
@[simp] theorem mul_add_right_right_iff : IsRelPrime x (z * x + y) ↔ IsRelPrime x y :=
  ⟨of_mul_add_right_right, fun h => h.mul_add_right_right z⟩

/--
theorem `neg_left` / 定理 `neg_left`

English:
theorem neg_left
  given: (h : IsRelPrime x y)
  statement: IsRelPrime (-x) y
  proof: fun _ => (h <| dvd_neg.mp ·)

中文:
定理 neg_left
  条件: (h : IsRelPrime x y)
  结论: IsRelPrime (-x) y
  证明: fun _ => (h <| dvd_neg.mp ·)

Depends on / 依赖: dvd_neg, dvd_neg.mp
-/
theorem neg_left (h : IsRelPrime x y) : IsRelPrime (-x) y := fun _ => (h <| dvd_neg.mp ·)
/--
theorem `neg_right` / 定理 `neg_right`

English:
theorem neg_right
  given: (h : IsRelPrime x y)
  statement: IsRelPrime x (-y)
  proof: h.symm.neg_left.symm

中文:
定理 neg_right
  条件: (h : IsRelPrime x y)
  结论: IsRelPrime x (-y)
  证明: h.symm.neg_left.symm

Depends on / 依赖: h.symm.neg_left.symm, neg_left
-/
theorem neg_right (h : IsRelPrime x y) : IsRelPrime x (-y) := h.symm.neg_left.symm
/--
theorem `neg_neg` / 定理 `neg_neg`

English:
theorem neg_neg
  given: (h : IsRelPrime x y)
  statement: IsRelPrime (-x) (-y)
  proof: h.neg_left.neg_right

中文:
定理 neg_neg
  条件: (h : IsRelPrime x y)
  结论: IsRelPrime (-x) (-y)
  证明: h.neg_left.neg_right
-/
protected theorem neg_neg (h : IsRelPrime x y) : IsRelPrime (-x) (-y) := h.neg_left.neg_right

/--
theorem `neg_left_iff` / 定理 `neg_left_iff`

English:
theorem neg_left_iff
  given: (x y : R)
  statement: IsRelPrime (-x) y ↔ IsRelPrime x y
  proof: ⟨fun h => neg_neg x ▸ h.neg_left, neg_left⟩

中文:
定理 neg_left_iff
  条件: (x y : R)
  结论: IsRelPrime (-x) y ↔ IsRelPrime x y
  证明: ⟨fun h => neg_neg x ▸ h.neg_left, neg_left⟩

Depends on / 依赖: h.neg_left, neg_left, neg_neg
-/
theorem neg_left_iff (x y : R) : IsRelPrime (-x) y ↔ IsRelPrime x y :=
  ⟨fun h => neg_neg x ▸ h.neg_left, neg_left⟩

/--
theorem `neg_right_iff` / 定理 `neg_right_iff`

English:
theorem neg_right_iff
  given: (x y : R)
  statement: IsRelPrime x (-y) ↔ IsRelPrime x y
  proof: ⟨fun h => neg_neg y ▸ h.neg_right, neg_right⟩

中文:
定理 neg_right_iff
  条件: (x y : R)
  结论: IsRelPrime x (-y) ↔ IsRelPrime x y
  证明: ⟨fun h => neg_neg y ▸ h.neg_right, neg_right⟩

Depends on / 依赖: h.neg_right, neg_neg, neg_right
-/
theorem neg_right_iff (x y : R) : IsRelPrime x (-y) ↔ IsRelPrime x y :=
  ⟨fun h => neg_neg y ▸ h.neg_right, neg_right⟩

/--
theorem `neg_neg_iff` / 定理 `neg_neg_iff`

English:
theorem neg_neg_iff
  given: (x y : R)
  statement: IsRelPrime (-x) (-y) ↔ IsRelPrime x y
  proof: (neg_left_iff _ _).trans (neg_right_iff _ _)

中文:
定理 neg_neg_iff
  条件: (x y : R)
  结论: IsRelPrime (-x) (-y) ↔ IsRelPrime x y
  证明: (neg_left_iff _ _).trans (neg_right_iff _ _)

Depends on / 依赖: neg_left_iff, neg_right_iff
-/
theorem neg_neg_iff (x y : R) : IsRelPrime (-x) (-y) ↔ IsRelPrime x y :=
  (neg_left_iff _ _).trans (neg_right_iff _ _)

/--
theorem `sub_mul_left_left_iff` / 定理 `sub_mul_left_left_iff`

English:
theorem sub_mul_left_left_iff
  statement: IsRelPrime (x - y * z) y ↔ IsRelPrime x y
  proof: by
  rw [sub_eq_add_neg]; rw [← mul_neg]; rw [add_mul_left_left_iff]

中文:
定理 sub_mul_left_left_iff
  结论: IsRelPrime (x - y * z) y ↔ IsRelPrime x y
  证明: by
  rw [sub_eq_add_neg]; rw [← mul_neg]; rw [add_mul_left_left_iff]
-/
@[simp] theorem sub_mul_left_left_iff : IsRelPrime (x - y * z) y ↔ IsRelPrime x y := by
  rw [sub_eq_add_neg]; rw [← mul_neg]; rw [add_mul_left_left_iff]

/--
theorem `sub_mul_right_left_iff` / 定理 `sub_mul_right_left_iff`

English:
theorem sub_mul_right_left_iff
  statement: IsRelPrime (x - z * y) y ↔ IsRelPrime x y
  proof: by
  rw [sub_eq_add_neg]; rw [← neg_mul]; rw [add_mul_right_left_iff]

中文:
定理 sub_mul_right_left_iff
  结论: IsRelPrime (x - z * y) y ↔ IsRelPrime x y
  证明: by
  rw [sub_eq_add_neg]; rw [← neg_mul]; rw [add_mul_right_left_iff]
-/
@[simp] theorem sub_mul_right_left_iff : IsRelPrime (x - z * y) y ↔ IsRelPrime x y := by
  rw [sub_eq_add_neg]; rw [← neg_mul]; rw [add_mul_right_left_iff]

/--
theorem `sub_mul_left_right_iff` / 定理 `sub_mul_left_right_iff`

English:
theorem sub_mul_left_right_iff
  statement: IsRelPrime x (y - x * z) ↔ IsRelPrime x y
  proof: by
  rw [sub_eq_add_neg]; rw [← mul_neg]; rw [add_mul_left_right_iff]

中文:
定理 sub_mul_left_right_iff
  结论: IsRelPrime x (y - x * z) ↔ IsRelPrime x y
  证明: by
  rw [sub_eq_add_neg]; rw [← mul_neg]; rw [add_mul_left_right_iff]
-/
@[simp] theorem sub_mul_left_right_iff : IsRelPrime x (y - x * z) ↔ IsRelPrime x y := by
  rw [sub_eq_add_neg]; rw [← mul_neg]; rw [add_mul_left_right_iff]

/--
theorem `sub_mul_right_right_iff` / 定理 `sub_mul_right_right_iff`

English:
theorem sub_mul_right_right_iff
  statement: IsRelPrime x (y - z * x) ↔ IsRelPrime x y
  proof: by
  rw [sub_eq_add_neg]; rw [← neg_mul]; rw [add_mul_right_right_iff]

中文:
定理 sub_mul_right_right_iff
  结论: IsRelPrime x (y - z * x) ↔ IsRelPrime x y
  证明: by
  rw [sub_eq_add_neg]; rw [← neg_mul]; rw [add_mul_right_right_iff]
-/
@[simp] theorem sub_mul_right_right_iff : IsRelPrime x (y - z * x) ↔ IsRelPrime x y := by
  rw [sub_eq_add_neg]; rw [← neg_mul]; rw [add_mul_right_right_iff]

/--
theorem `mul_sub_left_left_iff` / 定理 `mul_sub_left_left_iff`

English:
theorem mul_sub_left_left_iff
  statement: IsRelPrime (y * z - x) y ↔ IsRelPrime x y
  proof: by
  rw [sub_eq_neg_add]; rw [add_mul_left_left_iff]; rw [neg_left_iff]

中文:
定理 mul_sub_left_left_iff
  结论: IsRelPrime (y * z - x) y ↔ IsRelPrime x y
  证明: by
  rw [sub_eq_neg_add]; rw [add_mul_left_left_iff]; rw [neg_left_iff]
-/
@[simp] theorem mul_sub_left_left_iff : IsRelPrime (y * z - x) y ↔ IsRelPrime x y := by
  rw [sub_eq_neg_add]; rw [add_mul_left_left_iff]; rw [neg_left_iff]

/--
theorem `mul_sub_right_left_iff` / 定理 `mul_sub_right_left_iff`

English:
theorem mul_sub_right_left_iff
  statement: IsRelPrime (z * y - x) y ↔ IsRelPrime x y
  proof: by
  rw [sub_eq_neg_add]; rw [add_mul_right_left_iff]; rw [neg_left_iff]

中文:
定理 mul_sub_right_left_iff
  结论: IsRelPrime (z * y - x) y ↔ IsRelPrime x y
  证明: by
  rw [sub_eq_neg_add]; rw [add_mul_right_left_iff]; rw [neg_left_iff]
-/
@[simp] theorem mul_sub_right_left_iff : IsRelPrime (z * y - x) y ↔ IsRelPrime x y := by
  rw [sub_eq_neg_add]; rw [add_mul_right_left_iff]; rw [neg_left_iff]

/--
theorem `mul_sub_left_right_iff` / 定理 `mul_sub_left_right_iff`

English:
theorem mul_sub_left_right_iff
  statement: IsRelPrime x (x * z - y) ↔ IsRelPrime x y
  proof: by
  rw [sub_eq_add_neg]; rw [mul_add_left_right_iff]; rw [neg_right_iff]

中文:
定理 mul_sub_left_right_iff
  结论: IsRelPrime x (x * z - y) ↔ IsRelPrime x y
  证明: by
  rw [sub_eq_add_neg]; rw [mul_add_left_right_iff]; rw [neg_right_iff]
-/
@[simp] theorem mul_sub_left_right_iff : IsRelPrime x (x * z - y) ↔ IsRelPrime x y := by
  rw [sub_eq_add_neg]; rw [mul_add_left_right_iff]; rw [neg_right_iff]

/--
theorem `mul_sub_right_right_iff` / 定理 `mul_sub_right_right_iff`

English:
theorem mul_sub_right_right_iff
  statement: IsRelPrime x (z * x - y) ↔ IsRelPrime x y
  proof: by
  rw [sub_eq_add_neg]; rw [mul_add_right_right_iff]; rw [neg_right_iff]

中文:
定理 mul_sub_right_right_iff
  结论: IsRelPrime x (z * x - y) ↔ IsRelPrime x y
  证明: by
  rw [sub_eq_add_neg]; rw [mul_add_right_right_iff]; rw [neg_right_iff]
-/
@[simp] theorem mul_sub_right_right_iff : IsRelPrime x (z * x - y) ↔ IsRelPrime x y := by
  rw [sub_eq_add_neg]; rw [mul_add_right_right_iff]; rw [neg_right_iff]

/--
lemma `add_one_left_of_dvd` / 引理 `add_one_left_of_dvd`

English:
lemma add_one_left_of_dvd
  given: (h : y ∣ x)
  statement: IsRelPrime (x + 1) y
  proof: by
  obtain ⟨z, rfl⟩ := h
  rw [mul_add_left_left_iff]
  exact isRelPrime_one_left

中文:
引理 add_one_left_of_dvd
  条件: (h : y ∣ x)
  结论: IsRelPrime (x + 1) y
  证明: by
  obtain ⟨z, rfl⟩ := h
  rw [mul_add_left_left_iff]
  exact isRelPrime_one_left

Depends on / 依赖: isRelPrime_one_left, mul_add_left_left_iff
-/
lemma add_one_left_of_dvd (h : y ∣ x) : IsRelPrime (x + 1) y := by
  obtain ⟨z, rfl⟩ := h
  rw [mul_add_left_left_iff]
  exact isRelPrime_one_left

/--
lemma `add_one_right_of_dvd` / 引理 `add_one_right_of_dvd`

English:
lemma add_one_right_of_dvd
  given: (h : x ∣ y)
  statement: IsRelPrime x (y + 1)
  proof: isRelPrime_comm.mp (add_one_left_of_dvd h)

中文:
引理 add_one_right_of_dvd
  条件: (h : x ∣ y)
  结论: IsRelPrime x (y + 1)
  证明: isRelPrime_comm.mp (add_one_left_of_dvd h)

Depends on / 依赖: add_one_left_of_dvd, isRelPrime_comm, isRelPrime_comm.mp
-/
lemma add_one_right_of_dvd (h : x ∣ y) : IsRelPrime x (y + 1) :=
  isRelPrime_comm.mp (add_one_left_of_dvd h)

/--
lemma `sub_one_left_of_dvd` / 引理 `sub_one_left_of_dvd`

English:
lemma sub_one_left_of_dvd
  given: (h : y ∣ x)
  statement: IsRelPrime (x - 1) y
  proof: by
  rw [← neg_sub]; rw [neg_left_iff]; rw [sub_eq_neg_add]
  exact add_one_left_of_dvd h.neg_right

中文:
引理 sub_one_left_of_dvd
  条件: (h : y ∣ x)
  结论: IsRelPrime (x - 1) y
  证明: by
  rw [← neg_sub]; rw [neg_left_iff]; rw [sub_eq_neg_add]
  exact add_one_left_of_dvd h.neg_right

Depends on / 依赖: add_one_left_of_dvd, h.neg_right, neg_left_iff, neg_right, neg_sub, sub_eq_neg_add
-/
lemma sub_one_left_of_dvd (h : y ∣ x) : IsRelPrime (x - 1) y := by
  rw [← neg_sub]; rw [neg_left_iff]; rw [sub_eq_neg_add]
  exact add_one_left_of_dvd h.neg_right

/--
lemma `sub_one_right_of_dvd` / 引理 `sub_one_right_of_dvd`

English:
lemma sub_one_right_of_dvd
  given: (h : x ∣ y)
  statement: IsRelPrime x (y - 1)
  proof: isRelPrime_comm.mp (sub_one_left_of_dvd h)

中文:
引理 sub_one_right_of_dvd
  条件: (h : x ∣ y)
  结论: IsRelPrime x (y - 1)
  证明: isRelPrime_comm.mp (sub_one_left_of_dvd h)

Depends on / 依赖: isRelPrime_comm, isRelPrime_comm.mp, sub_one_left_of_dvd
-/
lemma sub_one_right_of_dvd (h : x ∣ y) : IsRelPrime x (y - 1) :=
  isRelPrime_comm.mp (sub_one_left_of_dvd h)

/--
lemma `add_one_sub_one_of_two_dvd` / 引理 `add_one_sub_one_of_two_dvd`

English:
lemma add_one_sub_one_of_two_dvd
  given: (h : 2 ∣ x)
  statement: IsRelPrime (x + 1) (x - 1)
  proof: by
  simpa [show 2 + (x - 1) = x + 1 by ring] using add_mul_left_left (sub_one_right_of_dvd h) 1

中文:
引理 add_one_sub_one_of_two_dvd
  条件: (h : 2 ∣ x)
  结论: IsRelPrime (x + 1) (x - 1)
  证明: by
  simpa [show 2 + (x - 1) = x + 1 by ring] using add_mul_left_left (sub_one_right_of_dvd h) 1

Depends on / 依赖: add_mul_left_left, sub_one_right_of_dvd
-/
lemma add_one_sub_one_of_two_dvd (h : 2 ∣ x) : IsRelPrime (x + 1) (x - 1) := by
  simpa [show 2 + (x - 1) = x + 1 by ring] using add_mul_left_left (sub_one_right_of_dvd h) 1

end IsRelPrime
