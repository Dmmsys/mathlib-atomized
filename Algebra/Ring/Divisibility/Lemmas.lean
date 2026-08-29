/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.GroupWithZero.Divisibility
public import Mathlib.Algebra.Ring.Divisibility.Basic
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.Algebra.GCDMonoid.Basic

/-!
# Lemmas about divisibility in rings

## Main results:
* `dvd_smul_of_dvd`: stating that `x ∣ y → x ∣ m • y` for any scalar `m`.
* `Commute.pow_dvd_add_pow_of_pow_eq_zero_right`: stating that if `y` is nilpotent then
  `x ^ m ∣ (x + y) ^ p` for sufficiently large `p` (together with many variations for convenience).
-/

public section

variable {R : Type*}

/--
lemma `dvd_smul_of_dvd` / 引理 `dvd_smul_of_dvd`

English:
lemma dvd_smul_of_dvd
  statement: {M : Type*} [SMul M R] [Semigroup R] [SMulCommClass M R R] {x y : R}
  proof: let ⟨k, hk⟩ := h; ⟨m • k, by rw [mul_smul_comm, ← hk]⟩

中文:
引理 dvd_smul_of_dvd
  结论: {M : 类型} [标量乘法 M R] [半群 R] [标量交换类 M R R] {x y : R}
  证明: let ⟨k, hk⟩ := h; ⟨m • k, by rw [mul_smul_comm, ← hk]⟩

Depends on / 依赖: mul_smul_comm
-/
lemma dvd_smul_of_dvd {M : Type*} [SMul M R] [Semigroup R] [SMulCommClass M R R] {x y : R}
    (m : M) (h : x ∣ y) : x ∣ m • y :=
  let ⟨k, hk⟩ := h; ⟨m • k, by rw [mul_smul_comm, ← hk]⟩

/--
lemma `dvd_nsmul_of_dvd` / 引理 `dvd_nsmul_of_dvd`

English:
lemma dvd_nsmul_of_dvd
  given: [NonUnitalSemiring R] {x y : R} (n : Nat) (h : x ∣ y)
  statement: x ∣ n • y
  proof: dvd_smul_of_dvd n h

中文:
引理 dvd_nsmul_of_dvd
  条件: [非幺半环 R] {x y : R} (n : 自然数) (h : x ∣ y)
  结论: x ∣ n • y
  证明: dvd_smul_of_dvd n h

Depends on / 依赖: dvd_smul_of_dvd
-/
lemma dvd_nsmul_of_dvd [NonUnitalSemiring R] {x y : R} (n : Nat) (h : x ∣ y) : x ∣ n • y :=
  dvd_smul_of_dvd n h

/--
lemma `dvd_zsmul_of_dvd` / 引理 `dvd_zsmul_of_dvd`

English:
lemma dvd_zsmul_of_dvd
  given: [NonUnitalRing R] {x y : R} (z : Int) (h : x ∣ y)
  statement: x ∣ z • y
  proof: dvd_smul_of_dvd z h

中文:
引理 dvd_zsmul_of_dvd
  条件: [非幺环 R] {x y : R} (z : 整数) (h : x ∣ y)
  结论: x ∣ z • y
  证明: dvd_smul_of_dvd z h

Depends on / 依赖: dvd_smul_of_dvd
-/
lemma dvd_zsmul_of_dvd [NonUnitalRing R] {x y : R} (z : Int) (h : x ∣ y) : x ∣ z • y :=
  dvd_smul_of_dvd z h

namespace Commute

variable {x y : R} {n m p : Nat}

section Semiring

variable [Semiring R]

/--
lemma `pow_dvd_add_pow_of_pow_eq_zero_right` / 引理 `pow_dvd_add_pow_of_pow_eq_zero_right`

English:
lemma pow_dvd_add_pow_of_pow_eq_zero_right
  statement: (hp : n + m <= p + 1) (h_comm : Commute x y)
  proof: by
  rw [h_comm.add_pow']
  refine Finset.dvd_sum fun ⟨i, j⟩ hij => ?_
  replace hij : i + j = p := by simpa using hij
  apply dvd_nsmul_of_dvd
  rcases le_or_gt m i with (hi : m <= i) | (hi : i + 1 <= m)
  · exact dvd_mul_of_dvd_left (pow_dvd_pow x hi) _
  · simp [pow_eq_zero_of_le (by lia : n <= j) hy]

中文:
引理 pow_dvd_add_pow_of_pow_eq_zero_right
  结论: (hp : n + m <= p + 1) (h_comm : Commute x y)
  证明: by
  rw [h_comm.add_pow']
  refine Finset.dvd_sum fun ⟨i, j⟩ hij => ?_
  replace hij : i + j = p := by simpa using hij
  apply dvd_nsmul_of_dvd
  rcases le_or_gt m i with (hi : m <= i) | (hi : i + 1 <= m)
  · exact dvd_mul_of_dvd_left (pow_dvd_pow x hi) _
  · simp [pow_eq_zero_of_le (by lia : n <= j) hy]

Depends on / 依赖: Finset, Finset.dvd_sum, add_pow, dvd_mul_of_dvd_left, dvd_nsmul_of_dvd, dvd_sum, h_comm, h_comm.add_pow, le_or_gt, pow_dvd_pow, pow_eq_zero_of_le, replace
-/
lemma pow_dvd_add_pow_of_pow_eq_zero_right (hp : n + m <= p + 1) (h_comm : Commute x y)
    (hy : y ^ n = 0) : x ^ m ∣ (x + y) ^ p := by
  rw [h_comm.add_pow']
  refine Finset.dvd_sum fun ⟨i, j⟩ hij => ?_
  replace hij : i + j = p := by simpa using hij
  apply dvd_nsmul_of_dvd
  rcases le_or_gt m i with (hi : m <= i) | (hi : i + 1 <= m)
  · exact dvd_mul_of_dvd_left (pow_dvd_pow x hi) _
  · simp [pow_eq_zero_of_le (by lia : n <= j) hy]

/--
lemma `pow_dvd_add_pow_of_pow_eq_zero_left` / 引理 `pow_dvd_add_pow_of_pow_eq_zero_left`

English:
lemma pow_dvd_add_pow_of_pow_eq_zero_left
  statement: (hp : n + m <= p + 1) (h_comm : Commute x y)
  proof: add_comm x y ▸ h_comm.symm.pow_dvd_add_pow_of_pow_eq_zero_right hp hx

中文:
引理 pow_dvd_add_pow_of_pow_eq_zero_left
  结论: (hp : n + m <= p + 1) (h_comm : Commute x y)
  证明: add_comm x y ▸ h_comm.symm.pow_dvd_add_pow_of_pow_eq_zero_right hp hx

Depends on / 依赖: add_comm, h_comm, h_comm.symm.pow_dvd_add_pow_of_pow_eq_zero_right, pow_dvd_add_pow_of_pow_eq_zero_right
-/
lemma pow_dvd_add_pow_of_pow_eq_zero_left (hp : n + m <= p + 1) (h_comm : Commute x y)
    (hx : x ^ n = 0) : y ^ m ∣ (x + y) ^ p :=
  add_comm x y ▸ h_comm.symm.pow_dvd_add_pow_of_pow_eq_zero_right hp hx

end Semiring

section Ring

variable [Ring R]

/--
lemma `pow_dvd_pow_of_sub_pow_eq_zero` / 引理 `pow_dvd_pow_of_sub_pow_eq_zero`

English:
lemma pow_dvd_pow_of_sub_pow_eq_zero
  statement: (hp : n + m <= p + 1) (h_comm : Commute x y)
  proof: by
  rw [← sub_add_cancel y x]
  apply (h_comm.symm.sub_left rfl).pow_dvd_add_pow_of_pow_eq_zero_left hp _
  rw [← neg_sub x y]; rw [neg_pow]; rw [h]; rw [mul_zero]

中文:
引理 pow_dvd_pow_of_sub_pow_eq_zero
  结论: (hp : n + m <= p + 1) (h_comm : Commute x y)
  证明: by
  rw [← sub_add_cancel y x]
  apply (h_comm.symm.sub_left rfl).pow_dvd_add_pow_of_pow_eq_zero_left hp _
  rw [← neg_sub x y]; rw [neg_pow]; rw [h]; rw [mul_zero]

Depends on / 依赖: h_comm, h_comm.symm.sub_left, mul_zero, neg_pow, neg_sub, pow_dvd_add_pow_of_pow_eq_zero_left, sub_add_cancel, sub_left
-/
lemma pow_dvd_pow_of_sub_pow_eq_zero (hp : n + m <= p + 1) (h_comm : Commute x y)
    (h : (x - y) ^ n = 0) : x ^ m ∣ y ^ p := by
  rw [← sub_add_cancel y x]
  apply (h_comm.symm.sub_left rfl).pow_dvd_add_pow_of_pow_eq_zero_left hp _
  rw [← neg_sub x y]; rw [neg_pow]; rw [h]; rw [mul_zero]

/--
lemma `pow_dvd_pow_of_add_pow_eq_zero` / 引理 `pow_dvd_pow_of_add_pow_eq_zero`

English:
lemma pow_dvd_pow_of_add_pow_eq_zero
  statement: (hp : n + m <= p + 1) (h_comm : Commute x y)
  proof: by
  rw [← neg_neg y]; rw [neg_pow']
  apply dvd_mul_of_dvd_left
  apply h_comm.neg_right.pow_dvd_pow_of_sub_pow_eq_zero hp
  simpa

中文:
引理 pow_dvd_pow_of_add_pow_eq_zero
  结论: (hp : n + m <= p + 1) (h_comm : Commute x y)
  证明: by
  rw [← neg_neg y]; rw [neg_pow']
  apply dvd_mul_of_dvd_left
  apply h_comm.neg_right.pow_dvd_pow_of_sub_pow_eq_zero hp
  simpa

Depends on / 依赖: dvd_mul_of_dvd_left, h_comm, h_comm.neg_right.pow_dvd_pow_of_sub_pow_eq_zero, neg_neg, neg_pow, neg_right, pow_dvd_pow_of_sub_pow_eq_zero
-/
lemma pow_dvd_pow_of_add_pow_eq_zero (hp : n + m <= p + 1) (h_comm : Commute x y)
    (h : (x + y) ^ n = 0) : x ^ m ∣ y ^ p := by
  rw [← neg_neg y]; rw [neg_pow']
  apply dvd_mul_of_dvd_left
  apply h_comm.neg_right.pow_dvd_pow_of_sub_pow_eq_zero hp
  simpa

/--
lemma `pow_dvd_sub_pow_of_pow_eq_zero_right` / 引理 `pow_dvd_sub_pow_of_pow_eq_zero_right`

English:
lemma pow_dvd_sub_pow_of_pow_eq_zero_right
  statement: (hp : n + m <= p + 1) (h_comm : Commute x y)
  proof: (sub_right rfl h_comm).pow_dvd_pow_of_sub_pow_eq_zero hp (by simpa)

中文:
引理 pow_dvd_sub_pow_of_pow_eq_zero_right
  结论: (hp : n + m <= p + 1) (h_comm : Commute x y)
  证明: (sub_right rfl h_comm).pow_dvd_pow_of_sub_pow_eq_zero hp (by simpa)

Depends on / 依赖: h_comm, pow_dvd_pow_of_sub_pow_eq_zero, sub_right
-/
lemma pow_dvd_sub_pow_of_pow_eq_zero_right (hp : n + m <= p + 1) (h_comm : Commute x y)
    (hy : y ^ n = 0) : x ^ m ∣ (x - y) ^ p :=
  (sub_right rfl h_comm).pow_dvd_pow_of_sub_pow_eq_zero hp (by simpa)

/--
lemma `pow_dvd_sub_pow_of_pow_eq_zero_left` / 引理 `pow_dvd_sub_pow_of_pow_eq_zero_left`

English:
lemma pow_dvd_sub_pow_of_pow_eq_zero_left
  statement: (hp : n + m <= p + 1) (h_comm : Commute x y)
  proof: by
  rw [← neg_sub y x]; rw [neg_pow']
  apply dvd_mul_of_dvd_left
  exact h_comm.symm.pow_dvd_sub_pow_of_pow_eq_zero_right hp hx

中文:
引理 pow_dvd_sub_pow_of_pow_eq_zero_left
  结论: (hp : n + m <= p + 1) (h_comm : Commute x y)
  证明: by
  rw [← neg_sub y x]; rw [neg_pow']
  apply dvd_mul_of_dvd_left
  exact h_comm.symm.pow_dvd_sub_pow_of_pow_eq_zero_right hp hx

Depends on / 依赖: dvd_mul_of_dvd_left, h_comm, h_comm.symm.pow_dvd_sub_pow_of_pow_eq_zero_right, neg_pow, neg_sub, pow_dvd_sub_pow_of_pow_eq_zero_right
-/
lemma pow_dvd_sub_pow_of_pow_eq_zero_left (hp : n + m <= p + 1) (h_comm : Commute x y)
    (hx : x ^ n = 0) : y ^ m ∣ (x - y) ^ p := by
  rw [← neg_sub y x]; rw [neg_pow']
  apply dvd_mul_of_dvd_left
  exact h_comm.symm.pow_dvd_sub_pow_of_pow_eq_zero_right hp hx

/--
lemma `add_pow_dvd_pow_of_pow_eq_zero_right` / 引理 `add_pow_dvd_pow_of_pow_eq_zero_right`

English:
lemma add_pow_dvd_pow_of_pow_eq_zero_right
  statement: (hp : n + m <= p + 1) (h_comm : Commute x y)
  proof: (h_comm.add_left rfl).pow_dvd_pow_of_sub_pow_eq_zero hp (by simpa)

中文:
引理 add_pow_dvd_pow_of_pow_eq_zero_right
  结论: (hp : n + m <= p + 1) (h_comm : Commute x y)
  证明: (h_comm.add_left rfl).pow_dvd_pow_of_sub_pow_eq_zero hp (by simpa)

Depends on / 依赖: add_left, h_comm, h_comm.add_left, pow_dvd_pow_of_sub_pow_eq_zero
-/
lemma add_pow_dvd_pow_of_pow_eq_zero_right (hp : n + m <= p + 1) (h_comm : Commute x y)
    (hx : x ^ n = 0) : (x + y) ^ m ∣ y ^ p :=
  (h_comm.add_left rfl).pow_dvd_pow_of_sub_pow_eq_zero hp (by simpa)

/--
lemma `add_pow_dvd_pow_of_pow_eq_zero_left` / 引理 `add_pow_dvd_pow_of_pow_eq_zero_left`

English:
lemma add_pow_dvd_pow_of_pow_eq_zero_left
  statement: (hp : n + m <= p + 1) (h_comm : Commute x y)
  proof: add_comm x y ▸ h_comm.symm.add_pow_dvd_pow_of_pow_eq_zero_right hp hy

中文:
引理 add_pow_dvd_pow_of_pow_eq_zero_left
  结论: (hp : n + m <= p + 1) (h_comm : Commute x y)
  证明: add_comm x y ▸ h_comm.symm.add_pow_dvd_pow_of_pow_eq_zero_right hp hy

Depends on / 依赖: add_comm, add_pow_dvd_pow_of_pow_eq_zero_right, h_comm, h_comm.symm.add_pow_dvd_pow_of_pow_eq_zero_right
-/
lemma add_pow_dvd_pow_of_pow_eq_zero_left (hp : n + m <= p + 1) (h_comm : Commute x y)
    (hy : y ^ n = 0) : (x + y) ^ m ∣ x ^ p :=
  add_comm x y ▸ h_comm.symm.add_pow_dvd_pow_of_pow_eq_zero_right hp hy

end Ring

end Commute
section CommRing

variable [CommRing R]

/--
lemma `dvd_mul_sub_mul_mul_left_of_dvd` / 引理 `dvd_mul_sub_mul_mul_left_of_dvd`

English:
lemma dvd_mul_sub_mul_mul_left_of_dvd
  statement: {p a b c d x y : R}
  proof: by
  obtain ⟨k1, hk1⟩ := h1
  obtain ⟨k2, hk2⟩ := h2
  refine ⟨d * k1 - b * k2, ?_⟩
  grind

中文:
引理 dvd_mul_sub_mul_mul_left_of_dvd
  结论: {p a b c d x y : R}
  证明: by
  obtain ⟨k1, hk1⟩ := h1
  obtain ⟨k2, hk2⟩ := h2
  refine ⟨d * k1 - b * k2, ?_⟩
  grind
-/
lemma dvd_mul_sub_mul_mul_left_of_dvd {p a b c d x y : R}
    (h1 : p ∣ a * x + b * y) (h2 : p ∣ c * x + d * y) : p ∣ (a * d - b * c) * x := by
  obtain ⟨k1, hk1⟩ := h1
  obtain ⟨k2, hk2⟩ := h2
  refine ⟨d * k1 - b * k2, ?_⟩
  grind

/--
lemma `dvd_mul_sub_mul_mul_right_of_dvd` / 引理 `dvd_mul_sub_mul_mul_right_of_dvd`

English:
lemma dvd_mul_sub_mul_mul_right_of_dvd
  statement: {p a b c d x y : R}
  proof: (mul_comm a _ ▸ mul_comm c _ ▸ dvd_mul_sub_mul_mul_left_of_dvd
    (add_comm (c * x) _ ▸ h2) (add_comm (a * x) _ ▸ h1))

中文:
引理 dvd_mul_sub_mul_mul_right_of_dvd
  结论: {p a b c d x y : R}
  证明: (mul_comm a _ ▸ mul_comm c _ ▸ dvd_mul_sub_mul_mul_left_of_dvd
    (add_comm (c * x) _ ▸ h2) (add_comm (a * x) _ ▸ h1))

Depends on / 依赖: add_comm, dvd_mul_sub_mul_mul_left_of_dvd, mul_comm
-/
lemma dvd_mul_sub_mul_mul_right_of_dvd {p a b c d x y : R}
    (h1 : p ∣ a * x + b * y) (h2 : p ∣ c * x + d * y) : p ∣ (a * d - b * c) * y :=
  (mul_comm a _ ▸ mul_comm c _ ▸ dvd_mul_sub_mul_mul_left_of_dvd
    (add_comm (c * x) _ ▸ h2) (add_comm (a * x) _ ▸ h1))

/--
lemma `dvd_mul_sub_mul_mul_gcd_of_dvd` / 引理 `dvd_mul_sub_mul_mul_gcd_of_dvd`

English:
lemma dvd_mul_sub_mul_mul_gcd_of_dvd
  statement: {p a b c d x y : R} [GCDMonoid R]
  proof: by
  rw [← (gcd_mul_left' (a * d - b * c) x y).dvd_iff_dvd_right]
  exact (dvd_gcd_iff _ _ _).2 ⟨dvd_mul_sub_mul_mul_left_of_dvd h1 h2,
    dvd_mul_sub_mul_mul_right_of_dvd h1 h2⟩

中文:
引理 dvd_mul_sub_mul_mul_gcd_of_dvd
  结论: {p a b c d x y : R} [最大公约数幺半群 R]
  证明: by
  rw [← (gcd_mul_left' (a * d - b * c) x y).dvd_iff_dvd_right]
  exact (dvd_gcd_iff _ _ _).2 ⟨dvd_mul_sub_mul_mul_left_of_dvd h1 h2,
    dvd_mul_sub_mul_mul_right_of_dvd h1 h2⟩

Depends on / 依赖: dvd_gcd_iff, dvd_iff_dvd_right, dvd_mul_sub_mul_mul_left_of_dvd, dvd_mul_sub_mul_mul_right_of_dvd, gcd_mul_left
-/
lemma dvd_mul_sub_mul_mul_gcd_of_dvd {p a b c d x y : R} [GCDMonoid R]
    (h1 : p ∣ a * x + b * y) (h2 : p ∣ c * x + d * y) : p ∣ (a * d - b * c) * gcd x y := by
  rw [← (gcd_mul_left' (a * d - b * c) x y).dvd_iff_dvd_right]
  exact (dvd_gcd_iff _ _ _).2 ⟨dvd_mul_sub_mul_mul_left_of_dvd h1 h2,
    dvd_mul_sub_mul_mul_right_of_dvd h1 h2⟩

end CommRing

section misc

variable [Ring R] [LinearOrder R] {x y : R}

@[simp]
/--
theorem `associated_abs_left_iff` / 定理 `associated_abs_left_iff`

English:
theorem associated_abs_left_iff
  proof: by
  obtain h | h := abs_choice x <;>
  simp [h]

@[simp]

中文:
定理 associated_abs_left_iff
  证明: by
  obtain h | h := abs_choice x <;>
  simp [h]

@[simp]

Depends on / 依赖: abs_choice
-/
theorem associated_abs_left_iff :
    Associated |x| y ↔ Associated x y := by
  obtain h | h := abs_choice x <;>
  simp [h]

@[simp]
/--
theorem `associated_abs_right_iff` / 定理 `associated_abs_right_iff`

English:
theorem associated_abs_right_iff
  proof: by
  rw [Associated.comm]; rw [associated_abs_left_iff]; rw [Associated.comm]

alias ⟨_, Associated.abs_left⟩ := associated_abs_left_iff

alias ⟨_, Associated.abs_right⟩ := associated_abs_right_iff

中文:
定理 associated_abs_right_iff
  证明: by
  rw [Associated.comm]; rw [associated_abs_left_iff]; rw [Associated.comm]

alias ⟨_, Associated.abs_left⟩ := associated_abs_left_iff

alias ⟨_, Associated.abs_right⟩ := associated_abs_right_iff

Depends on / 依赖: Associated, Associated.comm, associated_abs_left_iff
-/
theorem associated_abs_right_iff :
    Associated x |y| ↔ Associated x y := by
  rw [Associated.comm]; rw [associated_abs_left_iff]; rw [Associated.comm]

alias ⟨_, Associated.abs_left⟩ := associated_abs_left_iff

alias ⟨_, Associated.abs_right⟩ := associated_abs_right_iff

end misc
