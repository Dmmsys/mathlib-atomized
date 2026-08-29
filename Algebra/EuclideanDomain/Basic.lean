/-
Copyright (c) 2018 Louis Carlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Louis Carlin, Mario Carneiro
-/
module

public import Mathlib.Algebra.EuclideanDomain.Defs
public import Mathlib.Algebra.Ring.Divisibility.Basic
public import Mathlib.Algebra.GroupWithZero.Divisibility
public import Mathlib.Algebra.Ring.Equiv

/-!
# Lemmas about Euclidean domains

## Main statements

* `gcd_eq_gcd_ab`: states Bézout's lemma for Euclidean domains.

-/

@[expose] public section


universe u

namespace EuclideanDomain

variable {R : Type u}
variable [EuclideanDomain R]

/-- The well-founded relation in a Euclidean Domain satisfying `a % b ≺ b` for `b ≠ 0` -/
local infixl:50 " ≺ " => EuclideanDomain.r

-- See note [lower instance priority]
instance (priority := 100) toMulDivCancelClass : MulDivCancelClass R where
  mul_div_cancel a b hb := by
    refine (eq_of_sub_eq_zero ?_).symm
    by_contra h
    have := mul_right_not_lt b h
    rw [sub_mul]; rw [mul_comm (_ / _)]; rw [sub_eq_iff_eq_add'.2 (div_add_mod (a * b) b).symm] at this
    exact this (mod_lt _ hb)

/--
theorem `mod_eq_sub_mul_div` / 定理 `mod_eq_sub_mul_div`

English:
theorem mod_eq_sub_mul_div
  given: {R : Type*} [EuclideanDomain R] (a b : R)
  statement: a % b = a - b * (a / b)
  proof: calc
    a % b = b * (a / b) + a % b - b * (a / b) := (add_sub_cancel_left _ _).symm
    _ = a - b * (a / b) := by rw [div_add_mod]

中文:
定理 mod_eq_sub_mul_div
  条件: {R : 类型} [欧几里得整环 R] (a b : R)
  结论: a % b = a - b * (a / b)
  证明: calc
    a % b = b * (a / b) + a % b - b * (a / b) := (add_sub_cancel_left _ _).symm
    _ = a - b * (a / b) := by rw [div_add_mod]

Depends on / 依赖: add_sub_cancel_left, div_add_mod
-/
theorem mod_eq_sub_mul_div {R : Type*} [EuclideanDomain R] (a b : R) : a % b = a - b * (a / b) :=
  calc
    a % b = b * (a / b) + a % b - b * (a / b) := (add_sub_cancel_left _ _).symm
    _ = a - b * (a / b) := by rw [div_add_mod]

/--
theorem `val_dvd_le` / 定理 `val_dvd_le`

English:
theorem val_dvd_le
  statement: forall a b : R, b ∣ a -> a != 0 -> ¬a ≺ b

中文:
定理 val_dvd_le
  结论: 对任意 a b : R, b ∣ a -> a != 0 -> ¬a ≺ b
-/
theorem val_dvd_le : forall a b : R, b ∣ a -> a != 0 -> ¬a ≺ b
  | _, b, ⟨d, rfl⟩, ha => mul_left_not_lt b (mt (by rintro rfl; exact mul_zero _) ha)

@[simp]
/--
theorem `mod_eq_zero` / 定理 `mod_eq_zero`

English:
theorem mod_eq_zero
  given: {a b : R}
  statement: a % b = 0 ↔ b ∣ a
  proof: ⟨fun h => by
    rw [← div_add_mod a b]; rw [h]; rw [add_zero]
    exact dvd_mul_right _ _, fun ⟨c, e⟩ => by
    rw [e]; rw [← add_left_cancel_iff]; rw [div_add_mod]; rw [add_zero]
    have := Classical.dec
    by_cases b0 : b = 0
    · simp only [b0, zero_mul]
    · rw [mul_div_cancel_left₀ _ b0]⟩

@[simp]

中文:
定理 mod_eq_zero
  条件: {a b : R}
  结论: a % b = 0 ↔ b ∣ a
  证明: ⟨fun h => by
    rw [← div_add_mod a b]; rw [h]; rw [add_zero]
    exact dvd_mul_right _ _, fun ⟨c, e⟩ => by
    rw [e]; rw [← add_left_cancel_iff]; rw [div_add_mod]; rw [add_zero]
    have := Classical.dec
    by_cases b0 : b = 0
    · simp only [b0, zero_mul]
    · rw [mul_div_cancel_left₀ _ b0]⟩

@[simp]

Depends on / 依赖: Classical, Classical.dec, add_left_cancel_iff, add_zero, div_add_mod, dvd_mul_right, zero_mul
-/
theorem mod_eq_zero {a b : R} : a % b = 0 ↔ b ∣ a :=
  ⟨fun h => by
    rw [← div_add_mod a b]; rw [h]; rw [add_zero]
    exact dvd_mul_right _ _, fun ⟨c, e⟩ => by
    rw [e]; rw [← add_left_cancel_iff]; rw [div_add_mod]; rw [add_zero]
    have := Classical.dec
    by_cases b0 : b = 0
    · simp only [b0, zero_mul]
    · rw [mul_div_cancel_left₀ _ b0]⟩

@[simp]
/--
theorem `mod_self` / 定理 `mod_self`

English:
theorem mod_self
  given: (a : R)
  statement: a % a = 0
  proof: mod_eq_zero.2 dvd_rfl

中文:
定理 mod_self
  条件: (a : R)
  结论: a % a = 0
  证明: mod_eq_zero.2 dvd_rfl

Depends on / 依赖: dvd_rfl, mod_eq_zero
-/
theorem mod_self (a : R) : a % a = 0 :=
  mod_eq_zero.2 dvd_rfl

/--
theorem `dvd_mod_iff` / 定理 `dvd_mod_iff`

English:
theorem dvd_mod_iff
  given: {a b c : R} (h : c ∣ b)
  statement: c ∣ a % b ↔ c ∣ a
  proof: by
  rw [← dvd_add_right (h.mul_right _)]; rw [div_add_mod]

@[simp]

中文:
定理 dvd_mod_iff
  条件: {a b c : R} (h : c ∣ b)
  结论: c ∣ a % b ↔ c ∣ a
  证明: by
  rw [← dvd_add_right (h.mul_right _)]; rw [div_add_mod]

@[simp]

Depends on / 依赖: div_add_mod, dvd_add_right, h.mul_right, mul_right
-/
theorem dvd_mod_iff {a b c : R} (h : c ∣ b) : c ∣ a % b ↔ c ∣ a := by
  rw [← dvd_add_right (h.mul_right _)]; rw [div_add_mod]

@[simp]
/--
theorem `mod_one` / 定理 `mod_one`

English:
theorem mod_one
  given: (a : R)
  statement: a % 1 = 0
  proof: mod_eq_zero.2 (one_dvd _)

@[simp]

中文:
定理 mod_one
  条件: (a : R)
  结论: a % 1 = 0
  证明: mod_eq_zero.2 (one_dvd _)

@[simp]

Depends on / 依赖: mod_eq_zero, one_dvd
-/
theorem mod_one (a : R) : a % 1 = 0 :=
  mod_eq_zero.2 (one_dvd _)

@[simp]
/--
theorem `zero_mod` / 定理 `zero_mod`

English:
theorem zero_mod
  given: (b : R)
  statement: 0 % b = 0
  proof: mod_eq_zero.2 (dvd_zero _)

@[simp]

中文:
定理 zero_mod
  条件: (b : R)
  结论: 0 % b = 0
  证明: mod_eq_zero.2 (dvd_zero _)

@[simp]

Depends on / 依赖: dvd_zero, mod_eq_zero
-/
theorem zero_mod (b : R) : 0 % b = 0 :=
  mod_eq_zero.2 (dvd_zero _)

@[simp]
/--
theorem `zero_div` / 定理 `zero_div`

English:
theorem zero_div
  given: {a : R}
  statement: 0 / a = 0
  proof: by_cases (fun a0 : a = 0 => a0.symm ▸ div_zero 0) fun a0 => by
    simpa only [zero_mul] using mul_div_cancel_right₀ 0 a0

@[simp]

中文:
定理 zero_div
  条件: {a : R}
  结论: 0 / a = 0
  证明: by_cases (fun a0 : a = 0 => a0.symm ▸ div_zero 0) fun a0 => by
    simpa only [zero_mul] using mul_div_cancel_right₀ 0 a0

@[simp]

Depends on / 依赖: a0.symm, div_zero, zero_mul
-/
theorem zero_div {a : R} : 0 / a = 0 :=
  by_cases (fun a0 : a = 0 => a0.symm ▸ div_zero 0) fun a0 => by
    simpa only [zero_mul] using mul_div_cancel_right₀ 0 a0

@[simp]
/--
theorem `div_self` / 定理 `div_self`

English:
theorem div_self
  given: {a : R} (a0 : a != 0)
  statement: a / a = 1
  proof: by
  simpa only [one_mul] using mul_div_cancel_right₀ 1 a0

中文:
定理 div_self
  条件: {a : R} (a0 : a != 0)
  结论: a / a = 1
  证明: by
  simpa only [one_mul] using mul_div_cancel_right₀ 1 a0

Depends on / 依赖: one_mul
-/
theorem div_self {a : R} (a0 : a != 0) : a / a = 1 := by
  simpa only [one_mul] using mul_div_cancel_right₀ 1 a0

/--
theorem `eq_div_of_mul_eq_left` / 定理 `eq_div_of_mul_eq_left`

English:
theorem eq_div_of_mul_eq_left
  given: {a b c : R} (hb : b != 0) (h : a * b = c)
  statement: a = c / b
  proof: by
  rw [← h]; rw [mul_div_cancel_right₀ _ hb]

中文:
定理 eq_div_of_mul_eq_left
  条件: {a b c : R} (hb : b != 0) (h : a * b = c)
  结论: a = c / b
  证明: by
  rw [← h]; rw [mul_div_cancel_right₀ _ hb]
-/
theorem eq_div_of_mul_eq_left {a b c : R} (hb : b != 0) (h : a * b = c) : a = c / b := by
  rw [← h]; rw [mul_div_cancel_right₀ _ hb]

/--
theorem `eq_div_of_mul_eq_right` / 定理 `eq_div_of_mul_eq_right`

English:
theorem eq_div_of_mul_eq_right
  given: {a b c : R} (ha : a != 0) (h : a * b = c)
  statement: b = c / a
  proof: by
  rw [← h]; rw [mul_div_cancel_left₀ _ ha]

中文:
定理 eq_div_of_mul_eq_right
  条件: {a b c : R} (ha : a != 0) (h : a * b = c)
  结论: b = c / a
  证明: by
  rw [← h]; rw [mul_div_cancel_left₀ _ ha]
-/
theorem eq_div_of_mul_eq_right {a b c : R} (ha : a != 0) (h : a * b = c) : b = c / a := by
  rw [← h]; rw [mul_div_cancel_left₀ _ ha]

/--
theorem `mul_div_assoc` / 定理 `mul_div_assoc`

English:
theorem mul_div_assoc
  given: (x : R) {y z : R} (h : z ∣ y)
  statement: x * y / z = x * (y / z)
  proof: by
  by_cases hz : z = 0
  · subst hz
    rw [div_zero]; rw [div_zero]; rw [mul_zero]
  rcases h with ⟨p, rfl⟩
  rw [mul_div_cancel_left₀ _ hz]; rw [mul_left_comm]; rw [mul_div_cancel_left₀ _ hz]

中文:
定理 mul_div_assoc
  条件: (x : R) {y z : R} (h : z ∣ y)
  结论: x * y / z = x * (y / z)
  证明: by
  by_cases hz : z = 0
  · subst hz
    rw [div_zero]; rw [div_zero]; rw [mul_zero]
  rcases h with ⟨p, rfl⟩
  rw [mul_div_cancel_left₀ _ hz]; rw [mul_left_comm]; rw [mul_div_cancel_left₀ _ hz]

Depends on / 依赖: div_zero, mul_left_comm, mul_zero
-/
theorem mul_div_assoc (x : R) {y z : R} (h : z ∣ y) : x * y / z = x * (y / z) := by
  by_cases hz : z = 0
  · subst hz
    rw [div_zero]; rw [div_zero]; rw [mul_zero]
  rcases h with ⟨p, rfl⟩
  rw [mul_div_cancel_left₀ _ hz]; rw [mul_left_comm]; rw [mul_div_cancel_left₀ _ hz]

/--
theorem `mul_div_cancel'` / 定理 `mul_div_cancel'`

English:
theorem mul_div_cancel'
  given: {a b : R} (hb : b != 0) (hab : b ∣ a)
  statement: b * (a / b) = a
  proof: by
  rw [← mul_div_assoc _ hab]; rw [mul_div_cancel_left₀ _ hb]

中文:
定理 mul_div_cancel'
  条件: {a b : R} (hb : b != 0) (hab : b ∣ a)
  结论: b * (a / b) = a
  证明: by
  rw [← mul_div_assoc _ hab]; rw [mul_div_cancel_left₀ _ hb]
-/
protected theorem mul_div_cancel' {a b : R} (hb : b != 0) (hab : b ∣ a) : b * (a / b) = a := by
  rw [← mul_div_assoc _ hab]; rw [mul_div_cancel_left₀ _ hb]

-- This generalizes `Int.div_one`, see note [simp-normal form]
@[simp]
/--
theorem `div_one` / 定理 `div_one`

English:
theorem div_one
  given: (p : R)
  statement: p / 1 = p
  proof: (EuclideanDomain.eq_div_of_mul_eq_left (one_ne_zero' R) (mul_one p)).symm

中文:
定理 div_one
  条件: (p : R)
  结论: p / 1 = p
  证明: (EuclideanDomain.eq_div_of_mul_eq_left (one_ne_zero' R) (mul_one p)).symm

Depends on / 依赖: EuclideanDomain, EuclideanDomain.eq_div_of_mul_eq_left, eq_div_of_mul_eq_left, mul_one, one_ne_zero
-/
theorem div_one (p : R) : p / 1 = p :=
  (EuclideanDomain.eq_div_of_mul_eq_left (one_ne_zero' R) (mul_one p)).symm

/--
theorem `div_dvd_of_dvd` / 定理 `div_dvd_of_dvd`

English:
theorem div_dvd_of_dvd
  given: {p q : R} (hpq : q ∣ p)
  statement: p / q ∣ p
  proof: by
  by_cases hq : q = 0
  · rw [hq, zero_dvd_iff] at hpq
    rw [hpq]
    exact dvd_zero _
  use q
  rw [mul_comm]; rw [← EuclideanDomain.mul_div_assoc _ hpq]; rw [mul_comm]; rw [mul_div_cancel_right₀ _ hq]

中文:
定理 div_dvd_of_dvd
  条件: {p q : R} (hpq : q ∣ p)
  结论: p / q ∣ p
  证明: by
  by_cases hq : q = 0
  · rw [hq, zero_dvd_iff] at hpq
    rw [hpq]
    exact dvd_zero _
  use q
  rw [mul_comm]; rw [← EuclideanDomain.mul_div_assoc _ hpq]; rw [mul_comm]; rw [mul_div_cancel_right₀ _ hq]

Depends on / 依赖: EuclideanDomain, EuclideanDomain.mul_div_assoc, dvd_zero, mul_comm, mul_div_assoc, zero_dvd_iff
-/
theorem div_dvd_of_dvd {p q : R} (hpq : q ∣ p) : p / q ∣ p := by
  by_cases hq : q = 0
  · rw [hq, zero_dvd_iff] at hpq
    rw [hpq]
    exact dvd_zero _
  use q
  rw [mul_comm]; rw [← EuclideanDomain.mul_div_assoc _ hpq]; rw [mul_comm]; rw [mul_div_cancel_right₀ _ hq]

/--
theorem `dvd_div_of_mul_dvd` / 定理 `dvd_div_of_mul_dvd`

English:
theorem dvd_div_of_mul_dvd
  given: {a b c : R} (h : a * b ∣ c)
  statement: b ∣ c / a
  proof: by
  rcases eq_or_ne a 0 with (rfl | ha)
  · simp only [div_zero, dvd_zero]
  rcases h with ⟨d, rfl⟩
  refine ⟨d, ?_⟩
  rw [mul_assoc]; rw [mul_div_cancel_left₀ _ ha]

中文:
定理 dvd_div_of_mul_dvd
  条件: {a b c : R} (h : a * b ∣ c)
  结论: b ∣ c / a
  证明: by
  rcases eq_or_ne a 0 with (rfl | ha)
  · simp only [div_zero, dvd_zero]
  rcases h with ⟨d, rfl⟩
  refine ⟨d, ?_⟩
  rw [mul_assoc]; rw [mul_div_cancel_left₀ _ ha]

Depends on / 依赖: div_zero, dvd_zero, eq_or_ne, mul_assoc
-/
theorem dvd_div_of_mul_dvd {a b c : R} (h : a * b ∣ c) : b ∣ c / a := by
  rcases eq_or_ne a 0 with (rfl | ha)
  · simp only [div_zero, dvd_zero]
  rcases h with ⟨d, rfl⟩
  refine ⟨d, ?_⟩
  rw [mul_assoc]; rw [mul_div_cancel_left₀ _ ha]

section GCD

variable [DecidableEq R]

@[simp]
/--
theorem `gcd_zero_right` / 定理 `gcd_zero_right`

English:
theorem gcd_zero_right
  given: (a : R)
  statement: gcd a 0 = a
  proof: by
  rw [gcd]
  split_ifs with h <;> simp only [h, zero_mod, gcd_zero_left]

中文:
定理 gcd_zero_right
  条件: (a : R)
  结论: 最大公约数 a 0 = a
  证明: by
  rw [gcd]
  split_ifs with h <;> simp only [h, zero_mod, gcd_zero_left]

Depends on / 依赖: gcd_zero_left, split_ifs, zero_mod
-/
theorem gcd_zero_right (a : R) : gcd a 0 = a := by
  rw [gcd]
  split_ifs with h <;> simp only [h, zero_mod, gcd_zero_left]

/--
theorem `gcd_val` / 定理 `gcd_val`

English:
theorem gcd_val
  given: (a b : R)
  statement: gcd a b = gcd (b % a) a
  proof: by
  rw [gcd]
  split_ifs with h <;> [simp only [h, mod_zero, gcd_zero_right]; rfl]

中文:
定理 gcd_val
  条件: (a b : R)
  结论: 最大公约数 a b = 最大公约数 (b % a) a
  证明: by
  rw [gcd]
  split_ifs with h <;> [simp only [h, mod_zero, gcd_zero_right]; rfl]

Depends on / 依赖: gcd_zero_right, mod_zero, split_ifs
-/
theorem gcd_val (a b : R) : gcd a b = gcd (b % a) a := by
  rw [gcd]
  split_ifs with h <;> [simp only [h, mod_zero, gcd_zero_right]; rfl]

/--
theorem `gcd_dvd` / 定理 `gcd_dvd`

English:
theorem gcd_dvd
  given: (a b : R)
  statement: gcd a b ∣ a ∧ gcd a b ∣ b
  proof: GCD.induction a b
    (fun b => by
      rw [gcd_zero_left]
      exact ⟨dvd_zero _, dvd_rfl⟩)
    fun a b _ ⟨IH₁, IH₂⟩ => by
    rw [gcd_val]
    exact ⟨IH₂, (dvd_mod_iff IH₂).1 IH₁⟩

中文:
定理 gcd_dvd
  条件: (a b : R)
  结论: 最大公约数 a b ∣ a ∧ 最大公约数 a b ∣ b
  证明: GCD.induction a b
    (fun b => by
      rw [gcd_zero_left]
      exact ⟨dvd_zero _, dvd_rfl⟩)
    fun a b _ ⟨IH₁, IH₂⟩ => by
    rw [gcd_val]
    exact ⟨IH₂, (dvd_mod_iff IH₂).1 IH₁⟩

Depends on / 依赖: GCD.induction, dvd_mod_iff, dvd_rfl, dvd_zero, gcd_val, gcd_zero_left
-/
theorem gcd_dvd (a b : R) : gcd a b ∣ a ∧ gcd a b ∣ b :=
  GCD.induction a b
    (fun b => by
      rw [gcd_zero_left]
      exact ⟨dvd_zero _, dvd_rfl⟩)
    fun a b _ ⟨IH₁, IH₂⟩ => by
    rw [gcd_val]
    exact ⟨IH₂, (dvd_mod_iff IH₂).1 IH₁⟩

/--
theorem `gcd_dvd_left` / 定理 `gcd_dvd_left`

English:
theorem gcd_dvd_left
  given: (a b : R)
  statement: gcd a b ∣ a
  proof: (gcd_dvd a b).left

中文:
定理 gcd_dvd_left
  条件: (a b : R)
  结论: 最大公约数 a b ∣ a
  证明: (gcd_dvd a b).left

Depends on / 依赖: gcd_dvd
-/
theorem gcd_dvd_left (a b : R) : gcd a b ∣ a :=
  (gcd_dvd a b).left

/--
theorem `gcd_dvd_right` / 定理 `gcd_dvd_right`

English:
theorem gcd_dvd_right
  given: (a b : R)
  statement: gcd a b ∣ b
  proof: (gcd_dvd a b).right

中文:
定理 gcd_dvd_right
  条件: (a b : R)
  结论: 最大公约数 a b ∣ b
  证明: (gcd_dvd a b).right

Depends on / 依赖: gcd_dvd
-/
theorem gcd_dvd_right (a b : R) : gcd a b ∣ b :=
  (gcd_dvd a b).right

/--
theorem `gcd_eq_zero_iff` / 定理 `gcd_eq_zero_iff`

English:
theorem gcd_eq_zero_iff
  given: {a b : R}
  statement: gcd a b = 0 ↔ a = 0 ∧ b = 0
  proof: ⟨fun h => by simpa [h] using gcd_dvd a b, by
    rintro ⟨rfl, rfl⟩
    exact gcd_zero_right _⟩

中文:
定理 gcd_eq_zero_iff
  条件: {a b : R}
  结论: 最大公约数 a b = 0 ↔ a = 0 ∧ b = 0
  证明: ⟨fun h => by simpa [h] using gcd_dvd a b, by
    rintro ⟨rfl, rfl⟩
    exact gcd_zero_right _⟩
-/
protected theorem gcd_eq_zero_iff {a b : R} : gcd a b = 0 ↔ a = 0 ∧ b = 0 :=
  ⟨fun h => by simpa [h] using gcd_dvd a b, by
    rintro ⟨rfl, rfl⟩
    exact gcd_zero_right _⟩

/--
theorem `dvd_gcd` / 定理 `dvd_gcd`

English:
theorem dvd_gcd
  given: {a b c : R}
  statement: c ∣ a -> c ∣ b -> c ∣ gcd a b
  proof: GCD.induction a b (fun _ _ H => by simpa only [gcd_zero_left] using H) fun a b _ IH ca cb => by
    rw [gcd_val]
    exact IH ((dvd_mod_iff ca).2 cb) ca

中文:
定理 dvd_gcd
  条件: {a b c : R}
  结论: c ∣ a -> c ∣ b -> c ∣ 最大公约数 a b
  证明: GCD.induction a b (fun _ _ H => by simpa only [gcd_zero_left] using H) fun a b _ IH ca cb => by
    rw [gcd_val]
    exact IH ((dvd_mod_iff ca).2 cb) ca

Depends on / 依赖: GCD.induction, dvd_mod_iff, gcd_val, gcd_zero_left
-/
theorem dvd_gcd {a b c : R} : c ∣ a -> c ∣ b -> c ∣ gcd a b :=
  GCD.induction a b (fun _ _ H => by simpa only [gcd_zero_left] using H) fun a b _ IH ca cb => by
    rw [gcd_val]
    exact IH ((dvd_mod_iff ca).2 cb) ca

/--
theorem `gcd_eq_left` / 定理 `gcd_eq_left`

English:
theorem gcd_eq_left
  given: {a b : R}
  statement: gcd a b = a ↔ a ∣ b
  proof: ⟨fun h => by
    rw [← h]
    apply gcd_dvd_right, fun h => by rw [gcd_val, mod_eq_zero.2 h, gcd_zero_left]⟩

@[simp]

中文:
定理 gcd_eq_left
  条件: {a b : R}
  结论: 最大公约数 a b = a ↔ a ∣ b
  证明: ⟨fun h => by
    rw [← h]
    apply gcd_dvd_right, fun h => by rw [gcd_val, mod_eq_zero.2 h, gcd_zero_left]⟩

@[simp]

Depends on / 依赖: gcd_dvd_right, gcd_val, gcd_zero_left, mod_eq_zero
-/
theorem gcd_eq_left {a b : R} : gcd a b = a ↔ a ∣ b :=
  ⟨fun h => by
    rw [← h]
    apply gcd_dvd_right, fun h => by rw [gcd_val, mod_eq_zero.2 h, gcd_zero_left]⟩

@[simp]
/--
theorem `gcd_one_left` / 定理 `gcd_one_left`

English:
theorem gcd_one_left
  given: (a : R)
  statement: gcd 1 a = 1
  proof: gcd_eq_left.2 (one_dvd _)

@[simp]

中文:
定理 gcd_one_left
  条件: (a : R)
  结论: 最大公约数 1 a = 1
  证明: gcd_eq_left.2 (one_dvd _)

@[simp]

Depends on / 依赖: gcd_eq_left, one_dvd
-/
theorem gcd_one_left (a : R) : gcd 1 a = 1 :=
  gcd_eq_left.2 (one_dvd _)

@[simp]
/--
theorem `gcd_self` / 定理 `gcd_self`

English:
theorem gcd_self
  given: (a : R)
  statement: gcd a a = a
  proof: gcd_eq_left.2 dvd_rfl

@[simp]

中文:
定理 gcd_self
  条件: (a : R)
  结论: 最大公约数 a a = a
  证明: gcd_eq_left.2 dvd_rfl

@[simp]

Depends on / 依赖: dvd_rfl, gcd_eq_left
-/
theorem gcd_self (a : R) : gcd a a = a :=
  gcd_eq_left.2 dvd_rfl

@[simp]
/--
theorem `xgcdAux_fst` / 定理 `xgcdAux_fst`

English:
theorem xgcdAux_fst
  given: (x y : R)
  statement: forall s t s' t', (xgcdAux x s t y s' t').1 = gcd x y
  proof: GCD.induction x y
    (by
      intros
      rw [xgcd_zero_left]; rw [gcd_zero_left])
    fun x y h IH s t s' t' => by
    simp only [xgcdAux_rec h, IH]
    rw [← gcd_val]

中文:
定理 xgcdAux_fst
  条件: (x y : R)
  结论: 对任意 s t s' t', (xgcdAux x s t y s' t').1 = 最大公约数 x y
  证明: GCD.induction x y
    (by
      intros
      rw [xgcd_zero_left]; rw [gcd_zero_left])
    fun x y h IH s t s' t' => by
    simp only [xgcdAux_rec h, IH]
    rw [← gcd_val]

Depends on / 依赖: GCD.induction, gcd_val, gcd_zero_left, intros, xgcdAux_rec, xgcd_zero_left
-/
theorem xgcdAux_fst (x y : R) : forall s t s' t', (xgcdAux x s t y s' t').1 = gcd x y :=
  GCD.induction x y
    (by
      intros
      rw [xgcd_zero_left]; rw [gcd_zero_left])
    fun x y h IH s t s' t' => by
    simp only [xgcdAux_rec h, IH]
    rw [← gcd_val]

/--
theorem `xgcdAux_val` / 定理 `xgcdAux_val`

English:
theorem xgcdAux_val
  given: (x y : R)
  statement: xgcdAux x 1 0 y 0 1 = (gcd x y, xgcd x y)
  proof: by
  rw [xgcd]; rw [← xgcdAux_fst x y 1 0 0 1]

中文:
定理 xgcdAux_val
  条件: (x y : R)
  结论: xgcdAux x 1 0 y 0 1 = (最大公约数 x y, xgcd x y)
  证明: by
  rw [xgcd]; rw [← xgcdAux_fst x y 1 0 0 1]

Depends on / 依赖: xgcdAux_fst
-/
theorem xgcdAux_val (x y : R) : xgcdAux x 1 0 y 0 1 = (gcd x y, xgcd x y) := by
  rw [xgcd]; rw [← xgcdAux_fst x y 1 0 0 1]

set_option backward.privateInPublic true in
/--
Definition of `P` / `P` 的定义

English:
definition P
  signature: (a b : R)

中文:
定义 P
  签名: (a b : R)
-/
private def P (a b : R) : R × R × R -> Prop
  | (r, s, t) => (r : R) = a * s + b * t

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
theorem `xgcdAux_P` / 定理 `xgcdAux_P`

English:
theorem xgcdAux_P
  statement: (a b : R) {r r' : R} {s t s' t'} (p : P a b (r, s, t))
  proof: by
  induction r, r' using GCD.induction generalizing s t s' t' with
  | H0 n => simpa only [xgcd_zero_left]
  | H1 _ _ h IH =>
    rw [xgcdAux_rec h]
    refine IH ?_ p
    unfold P at p p' ⊢
    dsimp
    rw [mul_sub]; rw [mul_sub]; rw [add_sub]; rw [sub_add_eq_add_sub]; rw [← p']; rw [sub_sub]; rw [mul_comm _ s]; rw [← mul_assoc]; rw [mul_comm _ t]; rw [← mul_assoc]; rw [← add_mul]; rw [← p]; rw [mod_eq_sub_mul_div]

中文:
定理 xgcdAux_P
  结论: (a b : R) {r r' : R} {s t s' t'} (p : P a b (r, s, t))
  证明: by
  induction r, r' using GCD.induction generalizing s t s' t' with
  | H0 n => simpa only [xgcd_zero_left]
  | H1 _ _ h IH =>
    rw [xgcdAux_rec h]
    refine IH ?_ p
    unfold P at p p' ⊢
    dsimp
    rw [mul_sub]; rw [mul_sub]; rw [add_sub]; rw [sub_add_eq_add_sub]; rw [← p']; rw [sub_sub]; rw [mul_comm _ s]; rw [← mul_assoc]; rw [mul_comm _ t]; rw [← mul_assoc]; rw [← add_mul]; rw [← p]; rw [mod_eq_sub_mul_div]

Depends on / 依赖: GCD.induction, add_mul, add_sub, generalizing, mod_eq_sub_mul_div, mul_assoc, mul_comm, mul_sub, sub_add_eq_add_sub, sub_sub, xgcdAux_rec, xgcd_zero_left
-/
theorem xgcdAux_P (a b : R) {r r' : R} {s t s' t'} (p : P a b (r, s, t))
    (p' : P a b (r', s', t')) : P a b (xgcdAux r s t r' s' t') := by
  induction r, r' using GCD.induction generalizing s t s' t' with
  | H0 n => simpa only [xgcd_zero_left]
  | H1 _ _ h IH =>
    rw [xgcdAux_rec h]
    refine IH ?_ p
    unfold P at p p' ⊢
    dsimp
    rw [mul_sub]; rw [mul_sub]; rw [add_sub]; rw [sub_add_eq_add_sub]; rw [← p']; rw [sub_sub]; rw [mul_comm _ s]; rw [← mul_assoc]; rw [mul_comm _ t]; rw [← mul_assoc]; rw [← add_mul]; rw [← p]; rw [mod_eq_sub_mul_div]

/--
theorem `gcd_eq_gcd_ab` / 定理 `gcd_eq_gcd_ab`

English:
theorem gcd_eq_gcd_ab
  given: (a b : R)
  statement: (gcd a b : R) = a * gcdA a b + b * gcdB a b
  proof: by
  have :=
    @xgcdAux_P _ _ _ a b a b 1 0 0 1 (by dsimp [P]; rw [mul_one, mul_zero, add_zero])
      (by dsimp [P]; rw [mul_one, mul_zero, zero_add])
  rwa [xgcdAux_val, xgcd_val] at this

中文:
定理 gcd_eq_gcd_ab
  条件: (a b : R)
  结论: (最大公约数 a b : R) = a * gcdA a b + b * gcdB a b
  证明: by
  have :=
    @xgcdAux_P _ _ _ a b a b 1 0 0 1 (by dsimp [P]; rw [mul_one, mul_zero, add_zero])
      (by dsimp [P]; rw [mul_one, mul_zero, zero_add])
  rwa [xgcdAux_val, xgcd_val] at this

Depends on / 依赖: add_zero, mul_one, mul_zero, xgcdAux_P, xgcdAux_val, xgcd_val, zero_add
-/
theorem gcd_eq_gcd_ab (a b : R) : (gcd a b : R) = a * gcdA a b + b * gcdB a b := by
  have :=
    @xgcdAux_P _ _ _ a b a b 1 0 0 1 (by dsimp [P]; rw [mul_one, mul_zero, add_zero])
      (by dsimp [P]; rw [mul_one, mul_zero, zero_add])
  rwa [xgcdAux_val, xgcd_val] at this

-- see Note [lower instance priority]
instance (priority := 70) (R : Type*) [e : EuclideanDomain R] : IsDomain R :=
  haveI := Classical.decEq R
  have : NoZeroDivisors R :=
  { eq_zero_or_eq_zero_of_mul_eq_zero {a b} h :=
or_iff_not_and_not.2 fun h0 => h0.1 by rw [← mul_div_cancel_right₀ a h0.2, h, zero_div] }
  { e, NoZeroDivisors.to_isDomain R with }

/--
theorem `div_pow` / 定理 `div_pow`

English:
theorem div_pow
  given: {R : Type*} [EuclideanDomain R] {a b : R} {n : Nat} (hab : b ∣ a)
  proof: by
  obtain ⟨c, rfl⟩ := hab
  obtain rfl | hb := eq_or_ne b 0
  · obtain rfl | hn := eq_or_ne n 0 <;> simp [*]
  · simp [hb, mul_pow]

中文:
定理 div_pow
  条件: {R : 类型} [欧几里得整环 R] {a b : R} {n : 自然数} (hab : b ∣ a)
  证明: by
  obtain ⟨c, rfl⟩ := hab
  obtain rfl | hb := eq_or_ne b 0
  · obtain rfl | hn := eq_or_ne n 0 <;> simp [*]
  · simp [hb, mul_pow]

Depends on / 依赖: eq_or_ne, mul_pow
-/
theorem div_pow {R : Type*} [EuclideanDomain R] {a b : R} {n : Nat} (hab : b ∣ a) :
    (a / b) ^ n = a ^ n / b ^ n := by
  obtain ⟨c, rfl⟩ := hab
  obtain rfl | hb := eq_or_ne b 0
  · obtain rfl | hn := eq_or_ne n 0 <;> simp [*]
  · simp [hb, mul_pow]

end GCD

section LCM

variable [DecidableEq R]

/--
theorem `dvd_lcm_left` / 定理 `dvd_lcm_left`

English:
theorem dvd_lcm_left
  given: (x y : R)
  statement: x ∣ lcm x y
  proof: by_cases
    (fun hxy : gcd x y = 0 => by
      rw [lcm]; rw [hxy]; rw [div_zero]
      exact dvd_zero _)
    fun hxy =>
    let ⟨z, hz⟩ := (gcd_dvd x y).2
⟨z, Eq.symm eq_div_of_mul_eq_left hxy by rw [mul_right_comm, mul_assoc, ← hz]⟩

中文:
定理 dvd_lcm_left
  条件: (x y : R)
  结论: x ∣ 最小公倍数 x y
  证明: by_cases
    (fun hxy : gcd x y = 0 => by
      rw [lcm]; rw [hxy]; rw [div_zero]
      exact dvd_zero _)
    fun hxy =>
    let ⟨z, hz⟩ := (gcd_dvd x y).2
⟨z, Eq.symm eq_div_of_mul_eq_left hxy by rw [mul_right_comm, mul_assoc, ← hz]⟩

Depends on / 依赖: Eq.symm, div_zero, dvd_zero, eq_div_of_mul_eq_left, gcd_dvd, mul_assoc, mul_right_comm
-/
theorem dvd_lcm_left (x y : R) : x ∣ lcm x y :=
  by_cases
    (fun hxy : gcd x y = 0 => by
      rw [lcm]; rw [hxy]; rw [div_zero]
      exact dvd_zero _)
    fun hxy =>
    let ⟨z, hz⟩ := (gcd_dvd x y).2
⟨z, Eq.symm eq_div_of_mul_eq_left hxy by rw [mul_right_comm, mul_assoc, ← hz]⟩

/--
theorem `dvd_lcm_right` / 定理 `dvd_lcm_right`

English:
theorem dvd_lcm_right
  given: (x y : R)
  statement: y ∣ lcm x y
  proof: by_cases
    (fun hxy : gcd x y = 0 => by
      rw [lcm]; rw [hxy]; rw [div_zero]
      exact dvd_zero _)
    fun hxy =>
    let ⟨z, hz⟩ := (gcd_dvd x y).1
⟨z, Eq.symm eq_div_of_mul_eq_right hxy by rw [← mul_assoc, mul_right_comm, ← hz]⟩

中文:
定理 dvd_lcm_right
  条件: (x y : R)
  结论: y ∣ 最小公倍数 x y
  证明: by_cases
    (fun hxy : gcd x y = 0 => by
      rw [lcm]; rw [hxy]; rw [div_zero]
      exact dvd_zero _)
    fun hxy =>
    let ⟨z, hz⟩ := (gcd_dvd x y).1
⟨z, Eq.symm eq_div_of_mul_eq_right hxy by rw [← mul_assoc, mul_right_comm, ← hz]⟩

Depends on / 依赖: Eq.symm, div_zero, dvd_zero, eq_div_of_mul_eq_right, gcd_dvd, mul_assoc, mul_right_comm
-/
theorem dvd_lcm_right (x y : R) : y ∣ lcm x y :=
  by_cases
    (fun hxy : gcd x y = 0 => by
      rw [lcm]; rw [hxy]; rw [div_zero]
      exact dvd_zero _)
    fun hxy =>
    let ⟨z, hz⟩ := (gcd_dvd x y).1
⟨z, Eq.symm eq_div_of_mul_eq_right hxy by rw [← mul_assoc, mul_right_comm, ← hz]⟩

/--
theorem `lcm_dvd` / 定理 `lcm_dvd`

English:
theorem lcm_dvd
  given: {x y z : R} (hxz : x ∣ z) (hyz : y ∣ z)
  statement: lcm x y ∣ z
  proof: by
  rw [lcm]
  by_cases hxy : gcd x y = 0
  · rw [hxy, div_zero]
    rw [EuclideanDomain.gcd_eq_zero_iff] at hxy
    rwa [hxy.1] at hxz
  rcases gcd_dvd x y with ⟨⟨r, hr⟩, ⟨s, hs⟩⟩
  suffices x * y ∣ z * gcd x y by
    obtain ⟨p, hp⟩ := this
    use p
    generalize gcd x y = g at hxy hs hp ⊢
    subst hs
    rw [mul_left_comm]; rw [mul_div_cancel_left₀ _ hxy]; rw [← mul_left_inj' hxy]; rw [hp]
    rw [← mul_assoc]
    simp only [mul_right_comm]
  rw [gcd_eq_gcd_ab]; rw [mul_add]
  apply dvd_add
  · rw [mul_left_comm]
    gcongr
    apply hyz.mul_right
  · rw [mul_left_comm, mul_comm]
    gcongr
    apply hxz.mul_right

@[simp]

中文:
定理 lcm_dvd
  条件: {x y z : R} (hxz : x ∣ z) (hyz : y ∣ z)
  结论: 最小公倍数 x y ∣ z
  证明: by
  rw [lcm]
  by_cases hxy : gcd x y = 0
  · rw [hxy, div_zero]
    rw [EuclideanDomain.gcd_eq_zero_iff] at hxy
    rwa [hxy.1] at hxz
  rcases gcd_dvd x y with ⟨⟨r, hr⟩, ⟨s, hs⟩⟩
  suffices x * y ∣ z * gcd x y by
    obtain ⟨p, hp⟩ := this
    use p
    generalize gcd x y = g at hxy hs hp ⊢
    subst hs
    rw [mul_left_comm]; rw [mul_div_cancel_left₀ _ hxy]; rw [← mul_left_inj' hxy]; rw [hp]
    rw [← mul_assoc]
    simp only [mul_right_comm]
  rw [gcd_eq_gcd_ab]; rw [mul_add]
  apply dvd_add
  · rw [mul_left_comm]
    gcongr
    apply hyz.mul_right
  · rw [mul_left_comm, mul_comm]
    gcongr
    apply hxz.mul_right

@[simp]

Depends on / 依赖: EuclideanDomain, EuclideanDomain.gcd_eq_zero_iff, div_zero, dvd_add, gcd_dvd, gcd_eq_gcd_ab, gcd_eq_zero_iff, generalize, hyz.mul_right, mul_add, mul_assoc, mul_left_comm, mul_left_inj, mul_right, mul_right_comm
-/
theorem lcm_dvd {x y z : R} (hxz : x ∣ z) (hyz : y ∣ z) : lcm x y ∣ z := by
  rw [lcm]
  by_cases hxy : gcd x y = 0
  · rw [hxy, div_zero]
    rw [EuclideanDomain.gcd_eq_zero_iff] at hxy
    rwa [hxy.1] at hxz
  rcases gcd_dvd x y with ⟨⟨r, hr⟩, ⟨s, hs⟩⟩
  suffices x * y ∣ z * gcd x y by
    obtain ⟨p, hp⟩ := this
    use p
    generalize gcd x y = g at hxy hs hp ⊢
    subst hs
    rw [mul_left_comm]; rw [mul_div_cancel_left₀ _ hxy]; rw [← mul_left_inj' hxy]; rw [hp]
    rw [← mul_assoc]
    simp only [mul_right_comm]
  rw [gcd_eq_gcd_ab]; rw [mul_add]
  apply dvd_add
  · rw [mul_left_comm]
    gcongr
    apply hyz.mul_right
  · rw [mul_left_comm, mul_comm]
    gcongr
    apply hxz.mul_right

@[simp]
/--
theorem `lcm_dvd_iff` / 定理 `lcm_dvd_iff`

English:
theorem lcm_dvd_iff
  given: {x y z : R}
  statement: lcm x y ∣ z ↔ x ∣ z ∧ y ∣ z
  proof: ⟨fun hz => ⟨(dvd_lcm_left _ _).trans hz, (dvd_lcm_right _ _).trans hz⟩, fun ⟨hxz, hyz⟩ =>
    lcm_dvd hxz hyz⟩

@[simp]

中文:
定理 lcm_dvd_iff
  条件: {x y z : R}
  结论: 最小公倍数 x y ∣ z ↔ x ∣ z ∧ y ∣ z
  证明: ⟨fun hz => ⟨(dvd_lcm_left _ _).trans hz, (dvd_lcm_right _ _).trans hz⟩, fun ⟨hxz, hyz⟩ =>
    lcm_dvd hxz hyz⟩

@[simp]

Depends on / 依赖: dvd_lcm_left, dvd_lcm_right, lcm_dvd
-/
theorem lcm_dvd_iff {x y z : R} : lcm x y ∣ z ↔ x ∣ z ∧ y ∣ z :=
  ⟨fun hz => ⟨(dvd_lcm_left _ _).trans hz, (dvd_lcm_right _ _).trans hz⟩, fun ⟨hxz, hyz⟩ =>
    lcm_dvd hxz hyz⟩

@[simp]
/--
theorem `lcm_zero_left` / 定理 `lcm_zero_left`

English:
theorem lcm_zero_left
  given: (x : R)
  statement: lcm 0 x = 0
  proof: by rw [lcm, zero_mul, zero_div]

@[simp]

中文:
定理 lcm_zero_left
  条件: (x : R)
  结论: 最小公倍数 0 x = 0
  证明: by rw [lcm, zero_mul, zero_div]

@[simp]

Depends on / 依赖: zero_div, zero_mul
-/
theorem lcm_zero_left (x : R) : lcm 0 x = 0 := by rw [lcm, zero_mul, zero_div]

@[simp]
/--
theorem `lcm_zero_right` / 定理 `lcm_zero_right`

English:
theorem lcm_zero_right
  given: (x : R)
  statement: lcm x 0 = 0
  proof: by rw [lcm, mul_zero, zero_div]

@[simp]

中文:
定理 lcm_zero_right
  条件: (x : R)
  结论: 最小公倍数 x 0 = 0
  证明: by rw [lcm, mul_zero, zero_div]

@[simp]

Depends on / 依赖: mul_zero, zero_div
-/
theorem lcm_zero_right (x : R) : lcm x 0 = 0 := by rw [lcm, mul_zero, zero_div]

@[simp]
/--
theorem `lcm_eq_zero_iff` / 定理 `lcm_eq_zero_iff`

English:
theorem lcm_eq_zero_iff
  given: {x y : R}
  statement: lcm x y = 0 ↔ x = 0 ∨ y = 0
  proof: by
  constructor
  · intro hxy
    rw [lcm]; rw [mul_div_assoc _ (gcd_dvd_right _ _)]; rw [mul_eq_zero] at hxy
    apply Or.imp_right _ hxy
    intro hy
    by_cases hgxy : gcd x y = 0
    · rw [EuclideanDomain.gcd_eq_zero_iff] at hgxy
      exact hgxy.2
    · rcases gcd_dvd x y with ⟨⟨r, hr⟩, ⟨s, hs⟩⟩
      generalize gcd x y = g at hr hs hy hgxy ⊢
      subst hs
      rw [mul_div_cancel_left₀ _ hgxy] at hy
      rw [hy]; rw [mul_zero]
  rintro (hx | hy)
  · rw [hx, lcm_zero_left]
  · rw [hy, lcm_zero_right]

@[simp]

中文:
定理 lcm_eq_zero_iff
  条件: {x y : R}
  结论: 最小公倍数 x y = 0 ↔ x = 0 ∨ y = 0
  证明: by
  constructor
  · intro hxy
    rw [lcm]; rw [mul_div_assoc _ (gcd_dvd_right _ _)]; rw [mul_eq_zero] at hxy
    apply Or.imp_right _ hxy
    intro hy
    by_cases hgxy : gcd x y = 0
    · rw [EuclideanDomain.gcd_eq_zero_iff] at hgxy
      exact hgxy.2
    · rcases gcd_dvd x y with ⟨⟨r, hr⟩, ⟨s, hs⟩⟩
      generalize gcd x y = g at hr hs hy hgxy ⊢
      subst hs
      rw [mul_div_cancel_left₀ _ hgxy] at hy
      rw [hy]; rw [mul_zero]
  rintro (hx | hy)
  · rw [hx, lcm_zero_left]
  · rw [hy, lcm_zero_right]

@[simp]

Depends on / 依赖: EuclideanDomain, EuclideanDomain.gcd_eq_zero_iff, Or.imp_right, gcd_dvd, gcd_dvd_right, gcd_eq_zero_iff, generalize, imp_right, lcm_zero_left, lcm_zero_right, mul_div_assoc, mul_eq_zero, mul_zero
-/
theorem lcm_eq_zero_iff {x y : R} : lcm x y = 0 ↔ x = 0 ∨ y = 0 := by
  constructor
  · intro hxy
    rw [lcm]; rw [mul_div_assoc _ (gcd_dvd_right _ _)]; rw [mul_eq_zero] at hxy
    apply Or.imp_right _ hxy
    intro hy
    by_cases hgxy : gcd x y = 0
    · rw [EuclideanDomain.gcd_eq_zero_iff] at hgxy
      exact hgxy.2
    · rcases gcd_dvd x y with ⟨⟨r, hr⟩, ⟨s, hs⟩⟩
      generalize gcd x y = g at hr hs hy hgxy ⊢
      subst hs
      rw [mul_div_cancel_left₀ _ hgxy] at hy
      rw [hy]; rw [mul_zero]
  rintro (hx | hy)
  · rw [hx, lcm_zero_left]
  · rw [hy, lcm_zero_right]

@[simp]
/--
theorem `gcd_mul_lcm` / 定理 `gcd_mul_lcm`

English:
theorem gcd_mul_lcm
  given: (x y : R)
  statement: gcd x y * lcm x y = x * y
  proof: by
  rw [lcm]; by_cases h : gcd x y = 0
  · rw [h, zero_mul]
    rw [EuclideanDomain.gcd_eq_zero_iff] at h
    rw [h.1]; rw [zero_mul]
  rcases gcd_dvd x y with ⟨⟨r, hr⟩, ⟨s, hs⟩⟩
  generalize gcd x y = g at h hr ⊢; subst hr
  rw [mul_assoc]; rw [mul_div_cancel_left₀ _ h]

中文:
定理 gcd_mul_lcm
  条件: (x y : R)
  结论: 最大公约数 x y * 最小公倍数 x y = x * y
  证明: by
  rw [lcm]; by_cases h : gcd x y = 0
  · rw [h, zero_mul]
    rw [EuclideanDomain.gcd_eq_zero_iff] at h
    rw [h.1]; rw [zero_mul]
  rcases gcd_dvd x y with ⟨⟨r, hr⟩, ⟨s, hs⟩⟩
  generalize gcd x y = g at h hr ⊢; subst hr
  rw [mul_assoc]; rw [mul_div_cancel_left₀ _ h]

Depends on / 依赖: EuclideanDomain, EuclideanDomain.gcd_eq_zero_iff, gcd_dvd, gcd_eq_zero_iff, generalize, mul_assoc, zero_mul
-/
theorem gcd_mul_lcm (x y : R) : gcd x y * lcm x y = x * y := by
  rw [lcm]; by_cases h : gcd x y = 0
  · rw [h, zero_mul]
    rw [EuclideanDomain.gcd_eq_zero_iff] at h
    rw [h.1]; rw [zero_mul]
  rcases gcd_dvd x y with ⟨⟨r, hr⟩, ⟨s, hs⟩⟩
  generalize gcd x y = g at h hr ⊢; subst hr
  rw [mul_assoc]; rw [mul_div_cancel_left₀ _ h]

end LCM

section Div

/--
theorem `mul_div_mul_cancel` / 定理 `mul_div_mul_cancel`

English:
theorem mul_div_mul_cancel
  given: {a b c : R} (ha : a != 0) (hcb : c ∣ b)
  statement: a * b / (a * c) = b / c
  proof: by
  by_cases hc : c = 0; · simp [hc]
  refine eq_div_of_mul_eq_right hc (mul_left_cancel₀ ha ?_)
  rw [← mul_assoc]; rw [← mul_div_assoc _ (by gcongr)]; rw [mul_div_cancel_left₀ _ (mul_ne_zero ha hc)]

中文:
定理 mul_div_mul_cancel
  条件: {a b c : R} (ha : a != 0) (hcb : c ∣ b)
  结论: a * b / (a * c) = b / c
  证明: by
  by_cases hc : c = 0; · simp [hc]
  refine eq_div_of_mul_eq_right hc (mul_left_cancel₀ ha ?_)
  rw [← mul_assoc]; rw [← mul_div_assoc _ (by gcongr)]; rw [mul_div_cancel_left₀ _ (mul_ne_zero ha hc)]

Depends on / 依赖: eq_div_of_mul_eq_right, mul_assoc, mul_div_assoc, mul_ne_zero
-/
theorem mul_div_mul_cancel {a b c : R} (ha : a != 0) (hcb : c ∣ b) : a * b / (a * c) = b / c := by
  by_cases hc : c = 0; · simp [hc]
  refine eq_div_of_mul_eq_right hc (mul_left_cancel₀ ha ?_)
  rw [← mul_assoc]; rw [← mul_div_assoc _ (by gcongr)]; rw [mul_div_cancel_left₀ _ (mul_ne_zero ha hc)]

/--
theorem `mul_div_mul_comm_of_dvd_dvd` / 定理 `mul_div_mul_comm_of_dvd_dvd`

English:
theorem mul_div_mul_comm_of_dvd_dvd
  given: {a b c d : R} (hac : c ∣ a) (hbd : d ∣ b)
  proof: by
  rcases eq_or_ne c 0 with (rfl | hc0); · simp
  rcases eq_or_ne d 0 with (rfl | hd0); · simp
  obtain ⟨k1, rfl⟩ := hac
  obtain ⟨k2, rfl⟩ := hbd
  rw [mul_div_cancel_left₀ _ hc0]; rw [mul_div_cancel_left₀ _ hd0]; rw [mul_mul_mul_comm]; rw [mul_div_cancel_left₀ _ (mul_ne_zero hc0 hd0)]

中文:
定理 mul_div_mul_comm_of_dvd_dvd
  条件: {a b c d : R} (hac : c ∣ a) (hbd : d ∣ b)
  证明: by
  rcases eq_or_ne c 0 with (rfl | hc0); · simp
  rcases eq_or_ne d 0 with (rfl | hd0); · simp
  obtain ⟨k1, rfl⟩ := hac
  obtain ⟨k2, rfl⟩ := hbd
  rw [mul_div_cancel_left₀ _ hc0]; rw [mul_div_cancel_left₀ _ hd0]; rw [mul_mul_mul_comm]; rw [mul_div_cancel_left₀ _ (mul_ne_zero hc0 hd0)]

Depends on / 依赖: eq_or_ne, mul_mul_mul_comm, mul_ne_zero
-/
theorem mul_div_mul_comm_of_dvd_dvd {a b c d : R} (hac : c ∣ a) (hbd : d ∣ b) :
    a * b / (c * d) = a / c * (b / d) := by
  rcases eq_or_ne c 0 with (rfl | hc0); · simp
  rcases eq_or_ne d 0 with (rfl | hd0); · simp
  obtain ⟨k1, rfl⟩ := hac
  obtain ⟨k2, rfl⟩ := hbd
  rw [mul_div_cancel_left₀ _ hc0]; rw [mul_div_cancel_left₀ _ hd0]; rw [mul_mul_mul_comm]; rw [mul_div_cancel_left₀ _ (mul_ne_zero hc0 hd0)]

/--
theorem `add_mul_div_left` / 定理 `add_mul_div_left`

English:
theorem add_mul_div_left
  given: (x y z : R) (h1 : y != 0) (h2 : y ∣ x)
  statement: (x + y * z) / y = x / y + z
  proof: by
  rw [eq_comm]
  apply eq_div_of_mul_eq_right h1
  rw [mul_add]; rw [EuclideanDomain.mul_div_cancel' h1 h2]

中文:
定理 add_mul_div_left
  条件: (x y z : R) (h1 : y != 0) (h2 : y ∣ x)
  结论: (x + y * z) / y = x / y + z
  证明: by
  rw [eq_comm]
  apply eq_div_of_mul_eq_right h1
  rw [mul_add]; rw [EuclideanDomain.mul_div_cancel' h1 h2]

Depends on / 依赖: EuclideanDomain, EuclideanDomain.mul_div_cancel, eq_comm, eq_div_of_mul_eq_right, mul_add, mul_div_cancel
-/
theorem add_mul_div_left (x y z : R) (h1 : y != 0) (h2 : y ∣ x) : (x + y * z) / y = x / y + z := by
  rw [eq_comm]
  apply eq_div_of_mul_eq_right h1
  rw [mul_add]; rw [EuclideanDomain.mul_div_cancel' h1 h2]

/--
theorem `add_mul_div_right` / 定理 `add_mul_div_right`

English:
theorem add_mul_div_right
  given: (x y z : R) (h1 : y != 0) (h2 : y ∣ x)
  statement: (x + z * y) / y = x / y + z
  proof: by
  rw [mul_comm z y]
  exact add_mul_div_left _ _ _ h1 h2

中文:
定理 add_mul_div_right
  条件: (x y z : R) (h1 : y != 0) (h2 : y ∣ x)
  结论: (x + z * y) / y = x / y + z
  证明: by
  rw [mul_comm z y]
  exact add_mul_div_left _ _ _ h1 h2

Depends on / 依赖: add_mul_div_left, mul_comm
-/
theorem add_mul_div_right (x y z : R) (h1 : y != 0) (h2 : y ∣ x) : (x + z * y) / y = x / y + z := by
  rw [mul_comm z y]
  exact add_mul_div_left _ _ _ h1 h2

/--
theorem `sub_mul_div_left` / 定理 `sub_mul_div_left`

English:
theorem sub_mul_div_left
  given: (x y z : R) (h1 : y != 0) (h2 : y ∣ x)
  statement: (x - y * z) / y = x / y - z
  proof: by
  rw [eq_comm]
  apply eq_div_of_mul_eq_right h1
  rw [mul_sub]; rw [EuclideanDomain.mul_div_cancel' h1 h2]

中文:
定理 sub_mul_div_left
  条件: (x y z : R) (h1 : y != 0) (h2 : y ∣ x)
  结论: (x - y * z) / y = x / y - z
  证明: by
  rw [eq_comm]
  apply eq_div_of_mul_eq_right h1
  rw [mul_sub]; rw [EuclideanDomain.mul_div_cancel' h1 h2]

Depends on / 依赖: EuclideanDomain, EuclideanDomain.mul_div_cancel, eq_comm, eq_div_of_mul_eq_right, mul_div_cancel, mul_sub
-/
theorem sub_mul_div_left (x y z : R) (h1 : y != 0) (h2 : y ∣ x) : (x - y * z) / y = x / y - z := by
  rw [eq_comm]
  apply eq_div_of_mul_eq_right h1
  rw [mul_sub]; rw [EuclideanDomain.mul_div_cancel' h1 h2]

/--
theorem `sub_mul_div_right` / 定理 `sub_mul_div_right`

English:
theorem sub_mul_div_right
  given: (x y z : R) (h1 : y != 0) (h2 : y ∣ x)
  statement: (x - z * y) / y = x / y - z
  proof: by
  rw [mul_comm z y]
  exact sub_mul_div_left _ _ _ h1 h2

中文:
定理 sub_mul_div_right
  条件: (x y z : R) (h1 : y != 0) (h2 : y ∣ x)
  结论: (x - z * y) / y = x / y - z
  证明: by
  rw [mul_comm z y]
  exact sub_mul_div_left _ _ _ h1 h2

Depends on / 依赖: mul_comm, sub_mul_div_left
-/
theorem sub_mul_div_right (x y z : R) (h1 : y != 0) (h2 : y ∣ x) : (x - z * y) / y = x / y - z := by
  rw [mul_comm z y]
  exact sub_mul_div_left _ _ _ h1 h2

/--
theorem `mul_add_div_left` / 定理 `mul_add_div_left`

English:
theorem mul_add_div_left
  given: (x y z : R) (h1 : z != 0) (h2 : z ∣ y)
  statement: (z * x + y) / z = x + y / z
  proof: by
  rw [eq_comm]
  apply eq_div_of_mul_eq_right h1
  rw [mul_add]; rw [EuclideanDomain.mul_div_cancel' h1 h2]

中文:
定理 mul_add_div_left
  条件: (x y z : R) (h1 : z != 0) (h2 : z ∣ y)
  结论: (z * x + y) / z = x + y / z
  证明: by
  rw [eq_comm]
  apply eq_div_of_mul_eq_right h1
  rw [mul_add]; rw [EuclideanDomain.mul_div_cancel' h1 h2]

Depends on / 依赖: EuclideanDomain, EuclideanDomain.mul_div_cancel, eq_comm, eq_div_of_mul_eq_right, mul_add, mul_div_cancel
-/
theorem mul_add_div_left (x y z : R) (h1 : z != 0) (h2 : z ∣ y) : (z * x + y) / z = x + y / z := by
  rw [eq_comm]
  apply eq_div_of_mul_eq_right h1
  rw [mul_add]; rw [EuclideanDomain.mul_div_cancel' h1 h2]

/--
theorem `mul_add_div_right` / 定理 `mul_add_div_right`

English:
theorem mul_add_div_right
  given: (x y z : R) (h1 : z != 0) (h2 : z ∣ y)
  statement: (x * z + y) / z = x + y / z
  proof: by
  rw [mul_comm x z]
  exact mul_add_div_left _ _ _ h1 h2

中文:
定理 mul_add_div_right
  条件: (x y z : R) (h1 : z != 0) (h2 : z ∣ y)
  结论: (x * z + y) / z = x + y / z
  证明: by
  rw [mul_comm x z]
  exact mul_add_div_left _ _ _ h1 h2

Depends on / 依赖: mul_add_div_left, mul_comm
-/
theorem mul_add_div_right (x y z : R) (h1 : z != 0) (h2 : z ∣ y) : (x * z + y) / z = x + y / z := by
  rw [mul_comm x z]
  exact mul_add_div_left _ _ _ h1 h2

/--
theorem `mul_sub_div_left` / 定理 `mul_sub_div_left`

English:
theorem mul_sub_div_left
  given: (x y z : R) (h1 : z != 0) (h2 : z ∣ y)
  statement: (z * x - y) / z = x - y / z
  proof: by
  rw [eq_comm]
  apply eq_div_of_mul_eq_right h1
  rw [mul_sub]; rw [EuclideanDomain.mul_div_cancel' h1 h2]

中文:
定理 mul_sub_div_left
  条件: (x y z : R) (h1 : z != 0) (h2 : z ∣ y)
  结论: (z * x - y) / z = x - y / z
  证明: by
  rw [eq_comm]
  apply eq_div_of_mul_eq_right h1
  rw [mul_sub]; rw [EuclideanDomain.mul_div_cancel' h1 h2]

Depends on / 依赖: EuclideanDomain, EuclideanDomain.mul_div_cancel, eq_comm, eq_div_of_mul_eq_right, mul_div_cancel, mul_sub
-/
theorem mul_sub_div_left (x y z : R) (h1 : z != 0) (h2 : z ∣ y) : (z * x - y) / z = x - y / z := by
  rw [eq_comm]
  apply eq_div_of_mul_eq_right h1
  rw [mul_sub]; rw [EuclideanDomain.mul_div_cancel' h1 h2]

/--
theorem `mul_sub_div_right` / 定理 `mul_sub_div_right`

English:
theorem mul_sub_div_right
  given: (x y z : R) (h1 : z != 0) (h2 : z ∣ y)
  statement: (x * z - y) / z = x - y / z
  proof: by
  rw [mul_comm x z]
  exact mul_sub_div_left _ _ _ h1 h2

中文:
定理 mul_sub_div_right
  条件: (x y z : R) (h1 : z != 0) (h2 : z ∣ y)
  结论: (x * z - y) / z = x - y / z
  证明: by
  rw [mul_comm x z]
  exact mul_sub_div_left _ _ _ h1 h2

Depends on / 依赖: mul_comm, mul_sub_div_left
-/
theorem mul_sub_div_right (x y z : R) (h1 : z != 0) (h2 : z ∣ y) : (x * z - y) / z = x - y / z := by
  rw [mul_comm x z]
  exact mul_sub_div_left _ _ _ h1 h2

/--
theorem `div_mul` / 定理 `div_mul`

English:
theorem div_mul
  given: {x y z : R} (h1 : y ∣ x) (h2 : y * z ∣ x)
  proof: by
  rcases eq_or_ne z 0 with rfl | hz
  · simp only [mul_zero, div_zero]
  apply eq_div_of_mul_eq_right hz
  rw [← EuclideanDomain.mul_div_assoc z h2]; rw [mul_comm y z]; rw [mul_div_mul_cancel hz h1]

中文:
定理 div_mul
  条件: {x y z : R} (h1 : y ∣ x) (h2 : y * z ∣ x)
  证明: by
  rcases eq_or_ne z 0 with rfl | hz
  · simp only [mul_zero, div_zero]
  apply eq_div_of_mul_eq_right hz
  rw [← EuclideanDomain.mul_div_assoc z h2]; rw [mul_comm y z]; rw [mul_div_mul_cancel hz h1]

Depends on / 依赖: EuclideanDomain, EuclideanDomain.mul_div_assoc, div_zero, eq_div_of_mul_eq_right, eq_or_ne, mul_comm, mul_div_assoc, mul_div_mul_cancel, mul_zero
-/
theorem div_mul {x y z : R} (h1 : y ∣ x) (h2 : y * z ∣ x) :
    x / (y * z) = x / y / z := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp only [mul_zero, div_zero]
  apply eq_div_of_mul_eq_right hz
  rw [← EuclideanDomain.mul_div_assoc z h2]; rw [mul_comm y z]; rw [mul_div_mul_cancel hz h1]

/--
theorem `div_div` / 定理 `div_div`

English:
theorem div_div
  given: {x y z : R} (h1 : y ∣ x) (h2 : z ∣ (x / y))
  proof: by
  rcases eq_or_ne y 0 with rfl | hy
  · simp only [div_zero, zero_div, zero_mul]
  rw [← mul_dvd_mul_iff_left hy]; rw [EuclideanDomain.mul_div_cancel' hy h1] at h2
  exact (div_mul h1 h2).symm

中文:
定理 div_div
  条件: {x y z : R} (h1 : y ∣ x) (h2 : z ∣ (x / y))
  证明: by
  rcases eq_or_ne y 0 with rfl | hy
  · simp only [div_zero, zero_div, zero_mul]
  rw [← mul_dvd_mul_iff_left hy]; rw [EuclideanDomain.mul_div_cancel' hy h1] at h2
  exact (div_mul h1 h2).symm

Depends on / 依赖: EuclideanDomain, EuclideanDomain.mul_div_cancel, div_mul, div_zero, eq_or_ne, mul_div_cancel, mul_dvd_mul_iff_left, zero_div, zero_mul
-/
theorem div_div {x y z : R} (h1 : y ∣ x) (h2 : z ∣ (x / y)) :
    x / y / z = x / (y * z) := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp only [div_zero, zero_div, zero_mul]
  rw [← mul_dvd_mul_iff_left hy]; rw [EuclideanDomain.mul_div_cancel' hy h1] at h2
  exact (div_mul h1 h2).symm

/--
theorem `div_add_div_of_dvd` / 定理 `div_add_div_of_dvd`

English:
theorem div_add_div_of_dvd
  given: {x y z t : R} (h1 : y != 0) (h2 : t != 0) (h3 : y ∣ x) (h4 : t ∣ z)
  proof: by
  apply eq_div_of_mul_eq_right (mul_ne_zero h2 h1)
  rw [mul_add]; rw [mul_assoc]; rw [EuclideanDomain.mul_div_cancel' h1 h3]; rw [mul_comm t y]; rw [mul_assoc]; rw [EuclideanDomain.mul_div_cancel' h2 h4]

中文:
定理 div_add_div_of_dvd
  条件: {x y z t : R} (h1 : y != 0) (h2 : t != 0) (h3 : y ∣ x) (h4 : t ∣ z)
  证明: by
  apply eq_div_of_mul_eq_right (mul_ne_zero h2 h1)
  rw [mul_add]; rw [mul_assoc]; rw [EuclideanDomain.mul_div_cancel' h1 h3]; rw [mul_comm t y]; rw [mul_assoc]; rw [EuclideanDomain.mul_div_cancel' h2 h4]

Depends on / 依赖: EuclideanDomain, EuclideanDomain.mul_div_cancel, eq_div_of_mul_eq_right, mul_add, mul_assoc, mul_comm, mul_div_cancel, mul_ne_zero
-/
theorem div_add_div_of_dvd {x y z t : R} (h1 : y != 0) (h2 : t != 0) (h3 : y ∣ x) (h4 : t ∣ z) :
    x / y + z / t = (t * x + y * z) / (t * y) := by
  apply eq_div_of_mul_eq_right (mul_ne_zero h2 h1)
  rw [mul_add]; rw [mul_assoc]; rw [EuclideanDomain.mul_div_cancel' h1 h3]; rw [mul_comm t y]; rw [mul_assoc]; rw [EuclideanDomain.mul_div_cancel' h2 h4]

/--
theorem `div_sub_div_of_dvd` / 定理 `div_sub_div_of_dvd`

English:
theorem div_sub_div_of_dvd
  given: {x y z t : R} (h1 : y != 0) (h2 : t != 0) (h3 : y ∣ x) (h4 : t ∣ z)
  proof: by
  apply eq_div_of_mul_eq_right (mul_ne_zero h2 h1)
  rw [mul_sub]; rw [mul_assoc]; rw [EuclideanDomain.mul_div_cancel' h1 h3]; rw [mul_comm t y]; rw [mul_assoc]; rw [EuclideanDomain.mul_div_cancel' h2 h4]

中文:
定理 div_sub_div_of_dvd
  条件: {x y z t : R} (h1 : y != 0) (h2 : t != 0) (h3 : y ∣ x) (h4 : t ∣ z)
  证明: by
  apply eq_div_of_mul_eq_right (mul_ne_zero h2 h1)
  rw [mul_sub]; rw [mul_assoc]; rw [EuclideanDomain.mul_div_cancel' h1 h3]; rw [mul_comm t y]; rw [mul_assoc]; rw [EuclideanDomain.mul_div_cancel' h2 h4]

Depends on / 依赖: EuclideanDomain, EuclideanDomain.mul_div_cancel, eq_div_of_mul_eq_right, mul_assoc, mul_comm, mul_div_cancel, mul_ne_zero, mul_sub
-/
theorem div_sub_div_of_dvd {x y z t : R} (h1 : y != 0) (h2 : t != 0) (h3 : y ∣ x) (h4 : t ∣ z) :
    x / y - z / t = (t * x - y * z) / (t * y) := by
  apply eq_div_of_mul_eq_right (mul_ne_zero h2 h1)
  rw [mul_sub]; rw [mul_assoc]; rw [EuclideanDomain.mul_div_cancel' h1 h3]; rw [mul_comm t y]; rw [mul_assoc]; rw [EuclideanDomain.mul_div_cancel' h2 h4]

/--
theorem `div_eq_iff_eq_mul_of_dvd` / 定理 `div_eq_iff_eq_mul_of_dvd`

English:
theorem div_eq_iff_eq_mul_of_dvd
  given: (x y z : R) (h1 : y != 0) (h2 : y ∣ x)
  proof: by
  obtain ⟨a, ha⟩ := h2
  rw [ha]; rw [mul_div_cancel_left₀ _ h1]
  simp only [mul_eq_mul_left_iff, h1, or_false]

中文:
定理 div_eq_iff_eq_mul_of_dvd
  条件: (x y z : R) (h1 : y != 0) (h2 : y ∣ x)
  证明: by
  obtain ⟨a, ha⟩ := h2
  rw [ha]; rw [mul_div_cancel_left₀ _ h1]
  simp only [mul_eq_mul_left_iff, h1, or_false]

Depends on / 依赖: mul_eq_mul_left_iff, or_false
-/
theorem div_eq_iff_eq_mul_of_dvd (x y z : R) (h1 : y != 0) (h2 : y ∣ x) :
    x / y = z ↔ x = y * z := by
  obtain ⟨a, ha⟩ := h2
  rw [ha]; rw [mul_div_cancel_left₀ _ h1]
  simp only [mul_eq_mul_left_iff, h1, or_false]

/--
theorem `eq_div_iff_mul_eq_of_dvd` / 定理 `eq_div_iff_mul_eq_of_dvd`

English:
theorem eq_div_iff_mul_eq_of_dvd
  given: (x y z : R) (h1 : z != 0) (h2 : z ∣ y)
  proof: by
  rw [eq_comm]; rw [div_eq_iff_eq_mul_of_dvd _ _ _ h1 h2]; rw [eq_comm]

中文:
定理 eq_div_iff_mul_eq_of_dvd
  条件: (x y z : R) (h1 : z != 0) (h2 : z ∣ y)
  证明: by
  rw [eq_comm]; rw [div_eq_iff_eq_mul_of_dvd _ _ _ h1 h2]; rw [eq_comm]

Depends on / 依赖: div_eq_iff_eq_mul_of_dvd, eq_comm
-/
theorem eq_div_iff_mul_eq_of_dvd (x y z : R) (h1 : z != 0) (h2 : z ∣ y) :
    x = y / z ↔ z * x = y := by
  rw [eq_comm]; rw [div_eq_iff_eq_mul_of_dvd _ _ _ h1 h2]; rw [eq_comm]

/--
theorem `div_eq_div_iff_mul_eq_mul_of_dvd` / 定理 `div_eq_div_iff_mul_eq_mul_of_dvd`

English:
theorem div_eq_div_iff_mul_eq_mul_of_dvd
  statement: {x y z t : R} (h1 : y != 0) (h2 : t != 0)
  proof: by
  rw [div_eq_iff_eq_mul_of_dvd _ _ _ h1 h3]; rw [← mul_div_assoc _ h4]; rw [eq_div_iff_mul_eq_of_dvd _ _ _ h2]
  obtain ⟨a, ha⟩ := h4
  use y * a
  rw [ha]; rw [mul_comm]; rw [mul_assoc]; rw [mul_comm y a]

中文:
定理 div_eq_div_iff_mul_eq_mul_of_dvd
  结论: {x y z t : R} (h1 : y != 0) (h2 : t != 0)
  证明: by
  rw [div_eq_iff_eq_mul_of_dvd _ _ _ h1 h3]; rw [← mul_div_assoc _ h4]; rw [eq_div_iff_mul_eq_of_dvd _ _ _ h2]
  obtain ⟨a, ha⟩ := h4
  use y * a
  rw [ha]; rw [mul_comm]; rw [mul_assoc]; rw [mul_comm y a]

Depends on / 依赖: div_eq_iff_eq_mul_of_dvd, eq_div_iff_mul_eq_of_dvd, mul_assoc, mul_comm, mul_div_assoc
-/
theorem div_eq_div_iff_mul_eq_mul_of_dvd {x y z t : R} (h1 : y != 0) (h2 : t != 0)
    (h3 : y ∣ x) (h4 : t ∣ z) : x / y = z / t ↔ t * x = y * z := by
  rw [div_eq_iff_eq_mul_of_dvd _ _ _ h1 h3]; rw [← mul_div_assoc _ h4]; rw [eq_div_iff_mul_eq_of_dvd _ _ _ h2]
  obtain ⟨a, ha⟩ := h4
  use y * a
  rw [ha]; rw [mul_comm]; rw [mul_assoc]; rw [mul_comm y a]

end Div

end EuclideanDomain

section RingEquiv

variable {R S : Type*} [EuclideanDomain R] [CommRing S]

/--
Definition of `RingEquiv.euclideanDomain` / `RingEquiv.euclideanDomain` 的定义

English:
abbreviation RingEquiv.euclideanDomain
  signature: (e : S ≃+* R)
  body: e.nontrivial
  quotient a b := e.symm (e a / e b)
  remainder a b := e.symm (e a % e b)
  r a b := EuclideanDomain.r (e a) (e b)
  r_wellFounded := InvImage.wf e EuclideanDomain.r_wellFounded
  quotient_zero a := by simp
  quotient_mul_add_remainder_eq a b := by
    apply e.injective
    simpa using! EuclideanDomain.quotient_mul_add_remainder_eq (e a) (e b)
  remainder_lt a b hb := by
    have hb' : e b != 0 := by simpa using hb
    simpa using! EuclideanDomain.remainder_lt (e a) hb'
  mul_left_not_lt a b hb := by
    have hb' : e b != 0 := by simpa using hb
    simpa using! EuclideanDomain.mul_left_not_lt (e a) hb'

中文:
缩写 环等价.euclideanDomain
  签名: (e : S ≃+* R)
  定义体: e.nontrivial
  quotient a b := e.symm (e a / e b)
  remainder a b := e.symm (e a % e b)
  r a b := EuclideanDomain.r (e a) (e b)
  r_wellFounded := InvImage.wf e EuclideanDomain.r_wellFounded
  quotient_zero a := by simp
  quotient_mul_add_remainder_eq a b := by
    apply e.injective
    simpa using! EuclideanDomain.quotient_mul_add_remainder_eq (e a) (e b)
  remainder_lt a b hb := by
    have hb' : e b != 0 := by simpa using hb
    simpa using! EuclideanDomain.remainder_lt (e a) hb'
  mul_left_not_lt a b hb := by
    have hb' : e b != 0 := by simpa using hb
    simpa using! EuclideanDomain.mul_left_not_lt (e a) hb'
-/
protected abbrev RingEquiv.euclideanDomain (e : S ≃+* R) : EuclideanDomain S where
  toNontrivial := e.nontrivial
  quotient a b := e.symm (e a / e b)
  remainder a b := e.symm (e a % e b)
  r a b := EuclideanDomain.r (e a) (e b)
  r_wellFounded := InvImage.wf e EuclideanDomain.r_wellFounded
  quotient_zero a := by simp
  quotient_mul_add_remainder_eq a b := by
    apply e.injective
    simpa using! EuclideanDomain.quotient_mul_add_remainder_eq (e a) (e b)
  remainder_lt a b hb := by
    have hb' : e b != 0 := by simpa using hb
    simpa using! EuclideanDomain.remainder_lt (e a) hb'
  mul_left_not_lt a b hb := by
    have hb' : e b != 0 := by simpa using hb
    simpa using! EuclideanDomain.mul_left_not_lt (e a) hb'

end RingEquiv
