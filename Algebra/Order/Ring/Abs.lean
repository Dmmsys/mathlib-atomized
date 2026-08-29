/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro
-/
module

public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Order.Ring.Basic
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.Ring.Divisibility.Basic
public import Mathlib.Algebra.Ring.Int.Units
public import Mathlib.Data.Nat.Cast.Order.Ring

/-!
# Absolute values in linear ordered rings.
-/

@[expose] public section


variable {α : Type*}

section LinearOrderedAddCommGroup
variable [CommGroup α] [LinearOrder α] [IsOrderedMonoid α]

/--
lemma `mabs_zpow` / 引理 `mabs_zpow`

English:
lemma mabs_zpow
  given: (n : Int) (a : α)
  statement: |a ^ n|ₘ = |a|ₘ ^ |n|
  proof: by
  obtain n0 | n0 := le_total 0 n
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le n0
    simp only [mabs_pow, zpow_natCast, Nat.abs_cast]
  · obtain ⟨m, h⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.2 n0)
    rw [← mabs_inv]; rw [← zpow_neg]; rw [← abs_neg]; rw [h]; rw [zpow_natCast]; rw [Nat.abs_cast]

中文:
引理 mabs_zpow
  条件: (n : 整数) (a : α)
  结论: |a ^ n|ₘ = |a|ₘ ^ |n|
  证明: by
  obtain n0 | n0 := le_total 0 n
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le n0
    simp only [mabs_pow, zpow_natCast, Nat.abs_cast]
  · obtain ⟨m, h⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.2 n0)
    rw [← mabs_inv]; rw [← zpow_neg]; rw [← abs_neg]; rw [h]; rw [zpow_natCast]; rw [Nat.abs_cast]
-/
@[to_additive] lemma mabs_zpow (n : Int) (a : α) : |a ^ n|ₘ = |a|ₘ ^ |n| := by
  obtain n0 | n0 := le_total 0 n
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le n0
    simp only [mabs_pow, zpow_natCast, Nat.abs_cast]
  · obtain ⟨m, h⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.2 n0)
    rw [← mabs_inv]; rw [← zpow_neg]; rw [← abs_neg]; rw [h]; rw [zpow_natCast]; rw [Nat.abs_cast]; rw [zpow_natCast]
    exact mabs_pow m _

end LinearOrderedAddCommGroup

/--
lemma `odd_abs` / 引理 `odd_abs`

English:
lemma odd_abs
  given: [LinearOrder α] [Ring α] {a : α}
  statement: Odd (abs a) ↔ Odd a
  proof: by
  rcases abs_choice a with h | h <;> simp only [h, odd_neg]

中文:
引理 odd_abs
  条件: [线性序 α] [环 α] {a : α}
  结论: Odd (abs a) ↔ Odd a
  证明: by
  rcases abs_choice a with h | h <;> simp only [h, odd_neg]

Depends on / 依赖: abs_choice, odd_neg
-/
lemma odd_abs [LinearOrder α] [Ring α] {a : α} : Odd (abs a) ↔ Odd a := by
  rcases abs_choice a with h | h <;> simp only [h, odd_neg]

section LinearOrderedRing

variable [Ring α] [LinearOrder α] [IsOrderedRing α] {n : Nat} {a b : α}

/--
lemma `abs_one` / 引理 `abs_one`

English:
lemma abs_one
  statement: |(1 : α)| = 1
  proof: abs_of_nonneg zero_le_one

中文:
引理 abs_one
  结论: |(1 : α)| = 1
  证明: abs_of_nonneg zero_le_one
-/
@[simp] lemma abs_one : |(1 : α)| = 1 := abs_of_nonneg zero_le_one

/--
lemma `abs_two` / 引理 `abs_two`

English:
lemma abs_two
  statement: |(2 : α)| = 2
  proof: abs_of_nonneg zero_le_two

@[simp, grind =]

中文:
引理 abs_two
  结论: |(2 : α)| = 2
  证明: abs_of_nonneg zero_le_two

@[simp, grind =]

Depends on / 依赖: abs_of_nonneg, zero_le_two
-/
lemma abs_two : |(2 : α)| = 2 := abs_of_nonneg zero_le_two

@[simp, grind =]
/--
lemma `abs_mul` / 引理 `abs_mul`

English:
lemma abs_mul
  given: (a b : α)
  statement: |a * b| = |a| * |b|
  proof: by
  rw [abs_eq (mul_nonneg (abs_nonneg a) (abs_nonneg b))]
  rcases le_total a 0 with ha | ha <;> rcases le_total b 0 with hb | hb <;>
    simp only [abs_of_nonpos, abs_of_nonneg, true_or, or_true, neg_mul, mul_neg, neg_neg, *]

中文:
引理 abs_mul
  条件: (a b : α)
  结论: |a * b| = |a| * |b|
  证明: by
  rw [abs_eq (mul_nonneg (abs_nonneg a) (abs_nonneg b))]
  rcases le_total a 0 with ha | ha <;> rcases le_total b 0 with hb | hb <;>
    simp only [abs_of_nonpos, abs_of_nonneg, true_or, or_true, neg_mul, mul_neg, neg_neg, *]

Depends on / 依赖: abs_eq, abs_nonneg, abs_of_nonneg, abs_of_nonpos, le_total, mul_neg, mul_nonneg, neg_mul, neg_neg, or_true, true_or
-/
lemma abs_mul (a b : α) : |a * b| = |a| * |b| := by
  rw [abs_eq (mul_nonneg (abs_nonneg a) (abs_nonneg b))]
  rcases le_total a 0 with ha | ha <;> rcases le_total b 0 with hb | hb <;>
    simp only [abs_of_nonpos, abs_of_nonneg, true_or, or_true, neg_mul, mul_neg, neg_neg, *]

/--
Definition of `absHom` / `absHom` 的定义

English:
definition absHom
  signature: : α ->*₀ α where
  body: abs
  map_zero' := abs_zero
  map_one' := abs_one
  map_mul' := abs_mul

@[simp, grind =]

中文:
定义 absHom
  签名: : α ->*₀ α where
  定义体: abs
  map_zero' := abs_zero
  map_one' := abs_one
  map_mul' := abs_mul

@[simp, grind =]
-/
def absHom : α ->*₀ α where
  toFun := abs
  map_zero' := abs_zero
  map_one' := abs_one
  map_mul' := abs_mul

@[simp, grind =]
/--
lemma `abs_pow` / 引理 `abs_pow`

English:
lemma abs_pow
  given: (a : α) (n : Nat)
  statement: |a ^ n| = |a| ^ n
  proof: (absHom.toMonoidHom : α ->* α).map_pow _ _

中文:
引理 abs_pow
  条件: (a : α) (n : 自然数)
  结论: |a ^ n| = |a| ^ n
  证明: (absHom.toMonoidHom : α ->* α).map_pow _ _

Depends on / 依赖: absHom, absHom.toMonoidHom, map_pow, toMonoidHom
-/
lemma abs_pow (a : α) (n : Nat) : |a ^ n| = |a| ^ n := (absHom.toMonoidHom : α ->* α).map_pow _ _

/--
lemma `pow_abs` / 引理 `pow_abs`

English:
lemma pow_abs
  given: (a : α) (n : Nat)
  statement: |a| ^ n = |a ^ n|
  proof: (abs_pow a n).symm

中文:
引理 pow_abs
  条件: (a : α) (n : 自然数)
  结论: |a| ^ n = |a ^ n|
  证明: (abs_pow a n).symm

Depends on / 依赖: abs_pow
-/
lemma pow_abs (a : α) (n : Nat) : |a| ^ n = |a ^ n| := (abs_pow a n).symm

/--
lemma `Even.pow_abs` / 引理 `Even.pow_abs`

English:
lemma Even.pow_abs
  given: (hn : Even n) (a : α)
  statement: |a| ^ n = a ^ n
  proof: by
  rw [← abs_pow]; rw [abs_eq_self]; exact hn.pow_nonneg _

中文:
引理 Even.pow_abs
  条件: (hn : Even n) (a : α)
  结论: |a| ^ n = a ^ n
  证明: by
  rw [← abs_pow]; rw [abs_eq_self]; exact hn.pow_nonneg _

Depends on / 依赖: abs_eq_self, abs_pow, hn.pow_nonneg, pow_nonneg
-/
lemma Even.pow_abs (hn : Even n) (a : α) : |a| ^ n = a ^ n := by
  rw [← abs_pow]; rw [abs_eq_self]; exact hn.pow_nonneg _

/--
lemma `pow_abs_two_mul` / 引理 `pow_abs_two_mul`

English:
lemma pow_abs_two_mul
  given: (a : α)
  statement: |a| ^ (2 * n) = a ^ (2 * n)
  proof: Even.pow_abs ⟨n, two_mul n⟩ a

中文:
引理 pow_abs_two_mul
  条件: (a : α)
  结论: |a| ^ (2 * n) = a ^ (2 * n)
  证明: Even.pow_abs ⟨n, two_mul n⟩ a

Depends on / 依赖: Even.pow_abs, pow_abs, two_mul
-/
lemma pow_abs_two_mul (a : α) : |a| ^ (2 * n) = a ^ (2 * n) :=
  Even.pow_abs ⟨n, two_mul n⟩ a

/--
lemma `abs_neg_one_pow` / 引理 `abs_neg_one_pow`

English:
lemma abs_neg_one_pow
  given: (n : Nat)
  statement: |(-1 : α) ^ n| = 1
  proof: by rw [← pow_abs, abs_neg, abs_one, one_pow]

omit [IsOrderedRing α] in

中文:
引理 abs_neg_one_pow
  条件: (n : 自然数)
  结论: |(-1 : α) ^ n| = 1
  证明: by rw [← pow_abs, abs_neg, abs_one, one_pow]

omit [IsOrderedRing α] in

Depends on / 依赖: abs_neg, abs_one, one_pow, pow_abs
-/
lemma abs_neg_one_pow (n : Nat) : |(-1 : α) ^ n| = 1 := by rw [← pow_abs, abs_neg, abs_one, one_pow]

omit [IsOrderedRing α] in
/--
lemma `abs_mul_abs_self` / 引理 `abs_mul_abs_self`

English:
lemma abs_mul_abs_self
  given: (a : α)
  statement: |a| * |a| = a * a
  proof: abs_by_cases (fun x => x * x = a * a) rfl (neg_mul_neg a a)

中文:
引理 abs_mul_abs_self
  条件: (a : α)
  结论: |a| * |a| = a * a
  证明: abs_by_cases (fun x => x * x = a * a) rfl (neg_mul_neg a a)
-/
@[simp] lemma abs_mul_abs_self (a : α) : |a| * |a| = a * a :=
  abs_by_cases (fun x => x * x = a * a) rfl (neg_mul_neg a a)

/--
lemma `abs_mul_self` / 引理 `abs_mul_self`

English:
lemma abs_mul_self
  given: (a : α)
  statement: |a * a| = a * a
  proof: by simp

omit [IsOrderedRing α] in

中文:
引理 abs_mul_self
  条件: (a : α)
  结论: |a * a| = a * a
  证明: by simp

omit [IsOrderedRing α] in
-/
lemma abs_mul_self (a : α) : |a * a| = a * a := by simp

omit [IsOrderedRing α] in
/--
lemma `sq_abs` / 引理 `sq_abs`

English:
lemma sq_abs
  given: (a : α)
  statement: |a| ^ 2 = a ^ 2
  proof: by simpa only [sq] using abs_mul_abs_self a

中文:
引理 sq_abs
  条件: (a : α)
  结论: |a| ^ 2 = a ^ 2
  证明: by simpa only [sq] using abs_mul_abs_self a
-/
@[simp] lemma sq_abs (a : α) : |a| ^ 2 = a ^ 2 := by simpa only [sq] using abs_mul_abs_self a

/--
lemma `abs_sq` / 引理 `abs_sq`

English:
lemma abs_sq
  given: (x : α)
  statement: |x ^ 2| = x ^ 2
  proof: by simpa only [sq] using abs_mul_self x

中文:
引理 abs_sq
  条件: (x : α)
  结论: |x ^ 2| = x ^ 2
  证明: by simpa only [sq] using abs_mul_self x

Depends on / 依赖: abs_mul_self
-/
lemma abs_sq (x : α) : |x ^ 2| = x ^ 2 := by simpa only [sq] using abs_mul_self x

/--
lemma `exists_abs_lt` / 引理 `exists_abs_lt`

English:
lemma exists_abs_lt
  given: [Nontrivial α] (a : α)
  statement: exists b > 0, |a| < b
  proof: ⟨|a| + 1, lt_of_lt_of_le zero_lt_one by simp, lt_add_one |a|⟩

中文:
引理 存在_abs_lt
  条件: [非平凡 α] (a : α)
  结论: 存在 b > 0, |a| < b
  证明: ⟨|a| + 1, lt_of_lt_of_le zero_lt_one by simp, lt_add_one |a|⟩

Depends on / 依赖: lt_add_one, lt_of_lt_of_le, zero_lt_one
-/
lemma exists_abs_lt [Nontrivial α] (a : α) : exists b > 0, |a| < b :=
⟨|a| + 1, lt_of_lt_of_le zero_lt_one by simp, lt_add_one |a|⟩

end LinearOrderedRing

section LinearStrictOrderedRing

variable [Ring α] [LinearOrder α] [IsStrictOrderedRing α] {n : Nat} {a b : α}

/--
lemma `abs_pow_eq_one` / 引理 `abs_pow_eq_one`

English:
lemma abs_pow_eq_one
  given: (a : α) (h : n != 0)
  statement: |a ^ n| = 1 ↔ |a| = 1
  proof: by
  convert! pow_left_inj₀ (abs_nonneg a) zero_le_one h
  exacts [(pow_abs _ _).symm, (one_pow _).symm]

中文:
引理 abs_pow_eq_one
  条件: (a : α) (h : n != 0)
  结论: |a ^ n| = 1 ↔ |a| = 1
  证明: by
  convert! pow_left_inj₀ (abs_nonneg a) zero_le_one h
  exacts [(pow_abs _ _).symm, (one_pow _).symm]

Depends on / 依赖: abs_nonneg, convert, exacts, one_pow, pow_abs, zero_le_one
-/
lemma abs_pow_eq_one (a : α) (h : n != 0) : |a ^ n| = 1 ↔ |a| = 1 := by
  convert! pow_left_inj₀ (abs_nonneg a) zero_le_one h
  exacts [(pow_abs _ _).symm, (one_pow _).symm]

/--
lemma `abs_eq_iff_mul_self_eq` / 引理 `abs_eq_iff_mul_self_eq`

English:
lemma abs_eq_iff_mul_self_eq
  statement: |a| = |b| ↔ a * a = b * b
  proof: by
  rw [← abs_mul_abs_self]; rw [← abs_mul_abs_self b]
  exact (mul_self_inj (abs_nonneg a) (abs_nonneg b)).symm

中文:
引理 abs_eq_iff_mul_self_eq
  结论: |a| = |b| ↔ a * a = b * b
  证明: by
  rw [← abs_mul_abs_self]; rw [← abs_mul_abs_self b]
  exact (mul_self_inj (abs_nonneg a) (abs_nonneg b)).symm

Depends on / 依赖: abs_mul_abs_self, abs_nonneg, mul_self_inj
-/
lemma abs_eq_iff_mul_self_eq : |a| = |b| ↔ a * a = b * b := by
  rw [← abs_mul_abs_self]; rw [← abs_mul_abs_self b]
  exact (mul_self_inj (abs_nonneg a) (abs_nonneg b)).symm

/--
lemma `abs_lt_iff_mul_self_lt` / 引理 `abs_lt_iff_mul_self_lt`

English:
lemma abs_lt_iff_mul_self_lt
  statement: |a| < |b| ↔ a * a < b * b
  proof: by
  rw [← abs_mul_abs_self]; rw [← abs_mul_abs_self b]
  exact mul_self_lt_mul_self_iff (abs_nonneg a) (abs_nonneg b)

中文:
引理 abs_lt_iff_mul_self_lt
  结论: |a| < |b| ↔ a * a < b * b
  证明: by
  rw [← abs_mul_abs_self]; rw [← abs_mul_abs_self b]
  exact mul_self_lt_mul_self_iff (abs_nonneg a) (abs_nonneg b)

Depends on / 依赖: abs_mul_abs_self, abs_nonneg, mul_self_lt_mul_self_iff
-/
lemma abs_lt_iff_mul_self_lt : |a| < |b| ↔ a * a < b * b := by
  rw [← abs_mul_abs_self]; rw [← abs_mul_abs_self b]
  exact mul_self_lt_mul_self_iff (abs_nonneg a) (abs_nonneg b)

/--
lemma `abs_le_iff_mul_self_le` / 引理 `abs_le_iff_mul_self_le`

English:
lemma abs_le_iff_mul_self_le
  statement: |a| <= |b| ↔ a * a <= b * b
  proof: by
  rw [← abs_mul_abs_self]; rw [← abs_mul_abs_self b]
  exact mul_self_le_mul_self_iff (abs_nonneg a) (abs_nonneg b)

中文:
引理 abs_le_iff_mul_self_le
  结论: |a| <= |b| ↔ a * a <= b * b
  证明: by
  rw [← abs_mul_abs_self]; rw [← abs_mul_abs_self b]
  exact mul_self_le_mul_self_iff (abs_nonneg a) (abs_nonneg b)

Depends on / 依赖: abs_mul_abs_self, abs_nonneg, mul_self_le_mul_self_iff
-/
lemma abs_le_iff_mul_self_le : |a| <= |b| ↔ a * a <= b * b := by
  rw [← abs_mul_abs_self]; rw [← abs_mul_abs_self b]
  exact mul_self_le_mul_self_iff (abs_nonneg a) (abs_nonneg b)

/--
lemma `abs_le_one_iff_mul_self_le_one` / 引理 `abs_le_one_iff_mul_self_le_one`

English:
lemma abs_le_one_iff_mul_self_le_one
  statement: |a| <= 1 ↔ a * a <= 1
  proof: by
  simpa only [abs_one, one_mul] using abs_le_iff_mul_self_le (a := a) (b := 1)

中文:
引理 abs_le_one_iff_mul_self_le_one
  结论: |a| <= 1 ↔ a * a <= 1
  证明: by
  simpa only [abs_one, one_mul] using abs_le_iff_mul_self_le (a := a) (b := 1)

Depends on / 依赖: abs_le_iff_mul_self_le, abs_one, one_mul
-/
lemma abs_le_one_iff_mul_self_le_one : |a| <= 1 ↔ a * a <= 1 := by
  simpa only [abs_one, one_mul] using abs_le_iff_mul_self_le (a := a) (b := 1)

/--
lemma `sq_lt_sq` / 引理 `sq_lt_sq`

English:
lemma sq_lt_sq
  statement: a ^ 2 < b ^ 2 ↔ |a| < |b|
  proof: by
  simpa only [sq_abs] using sq_lt_sq₀ (abs_nonneg a) (abs_nonneg b)

中文:
引理 sq_lt_sq
  结论: a ^ 2 < b ^ 2 ↔ |a| < |b|
  证明: by
  simpa only [sq_abs] using sq_lt_sq₀ (abs_nonneg a) (abs_nonneg b)

Depends on / 依赖: abs_nonneg, sq_abs
-/
lemma sq_lt_sq : a ^ 2 < b ^ 2 ↔ |a| < |b| := by
  simpa only [sq_abs] using sq_lt_sq₀ (abs_nonneg a) (abs_nonneg b)

/--
lemma `sq_lt_sq'` / 引理 `sq_lt_sq'`

English:
lemma sq_lt_sq'
  given: (h1 : -b < a) (h2 : a < b)
  statement: a ^ 2 < b ^ 2
  proof: sq_lt_sq.2 (lt_of_lt_of_le (abs_lt.2 ⟨h1, h2⟩) (le_abs_self _))

中文:
引理 sq_lt_sq'
  条件: (h1 : -b < a) (h2 : a < b)
  结论: a ^ 2 < b ^ 2
  证明: sq_lt_sq.2 (lt_of_lt_of_le (abs_lt.2 ⟨h1, h2⟩) (le_abs_self _))

Depends on / 依赖: abs_lt, le_abs_self, lt_of_lt_of_le, sq_lt_sq
-/
lemma sq_lt_sq' (h1 : -b < a) (h2 : a < b) : a ^ 2 < b ^ 2 :=
  sq_lt_sq.2 (lt_of_lt_of_le (abs_lt.2 ⟨h1, h2⟩) (le_abs_self _))

/--
lemma `sq_le_sq` / 引理 `sq_le_sq`

English:
lemma sq_le_sq
  statement: a ^ 2 <= b ^ 2 ↔ |a| <= |b|
  proof: by
  simpa only [sq_abs] using sq_le_sq₀ (abs_nonneg a) (abs_nonneg b)

中文:
引理 sq_le_sq
  结论: a ^ 2 <= b ^ 2 ↔ |a| <= |b|
  证明: by
  simpa only [sq_abs] using sq_le_sq₀ (abs_nonneg a) (abs_nonneg b)

Depends on / 依赖: abs_nonneg, sq_abs
-/
lemma sq_le_sq : a ^ 2 <= b ^ 2 ↔ |a| <= |b| := by
  simpa only [sq_abs] using sq_le_sq₀ (abs_nonneg a) (abs_nonneg b)

/--
lemma `sq_le_sq'` / 引理 `sq_le_sq'`

English:
lemma sq_le_sq'
  given: (h1 : -b <= a) (h2 : a <= b)
  statement: a ^ 2 <= b ^ 2
  proof: sq_le_sq.2 (le_trans (abs_le.mpr ⟨h1, h2⟩) (le_abs_self _))

中文:
引理 sq_le_sq'
  条件: (h1 : -b <= a) (h2 : a <= b)
  结论: a ^ 2 <= b ^ 2
  证明: sq_le_sq.2 (le_trans (abs_le.mpr ⟨h1, h2⟩) (le_abs_self _))

Depends on / 依赖: abs_le, abs_le.mpr, le_abs_self, le_trans, sq_le_sq
-/
lemma sq_le_sq' (h1 : -b <= a) (h2 : a <= b) : a ^ 2 <= b ^ 2 :=
  sq_le_sq.2 (le_trans (abs_le.mpr ⟨h1, h2⟩) (le_abs_self _))

/--
lemma `abs_lt_of_sq_lt_sq` / 引理 `abs_lt_of_sq_lt_sq`

English:
lemma abs_lt_of_sq_lt_sq
  given: (h : a ^ 2 < b ^ 2) (hb : 0 <= b)
  statement: |a| < b
  proof: by
  rwa [← abs_of_nonneg hb, ← sq_lt_sq]

中文:
引理 abs_lt_of_sq_lt_sq
  条件: (h : a ^ 2 < b ^ 2) (hb : 0 <= b)
  结论: |a| < b
  证明: by
  rwa [← abs_of_nonneg hb, ← sq_lt_sq]

Depends on / 依赖: abs_of_nonneg, sq_lt_sq
-/
lemma abs_lt_of_sq_lt_sq (h : a ^ 2 < b ^ 2) (hb : 0 <= b) : |a| < b := by
  rwa [← abs_of_nonneg hb, ← sq_lt_sq]

/--
lemma `abs_lt_of_sq_lt_sq'` / 引理 `abs_lt_of_sq_lt_sq'`

English:
lemma abs_lt_of_sq_lt_sq'
  given: (h : a ^ 2 < b ^ 2) (hb : 0 <= b)
  statement: -b < a ∧ a < b
  proof: abs_lt.1 abs_lt_of_sq_lt_sq h hb

中文:
引理 abs_lt_of_sq_lt_sq'
  条件: (h : a ^ 2 < b ^ 2) (hb : 0 <= b)
  结论: -b < a ∧ a < b
  证明: abs_lt.1 abs_lt_of_sq_lt_sq h hb

Depends on / 依赖: abs_lt, abs_lt_of_sq_lt_sq
-/
lemma abs_lt_of_sq_lt_sq' (h : a ^ 2 < b ^ 2) (hb : 0 <= b) : -b < a ∧ a < b :=
abs_lt.1 abs_lt_of_sq_lt_sq h hb

/--
lemma `abs_le_of_sq_le_sq` / 引理 `abs_le_of_sq_le_sq`

English:
lemma abs_le_of_sq_le_sq
  given: (h : a ^ 2 <= b ^ 2) (hb : 0 <= b)
  statement: |a| <= b
  proof: by
  rwa [← abs_of_nonneg hb, ← sq_le_sq]

中文:
引理 abs_le_of_sq_le_sq
  条件: (h : a ^ 2 <= b ^ 2) (hb : 0 <= b)
  结论: |a| <= b
  证明: by
  rwa [← abs_of_nonneg hb, ← sq_le_sq]

Depends on / 依赖: abs_of_nonneg, sq_le_sq
-/
lemma abs_le_of_sq_le_sq (h : a ^ 2 <= b ^ 2) (hb : 0 <= b) : |a| <= b := by
  rwa [← abs_of_nonneg hb, ← sq_le_sq]

/--
theorem `le_of_sq_le_sq` / 定理 `le_of_sq_le_sq`

English:
theorem le_of_sq_le_sq
  given: (h : a ^ 2 <= b ^ 2) (hb : 0 <= b)
  statement: a <= b
  proof: .trans abs_le_of_sq_le_sq h hb le_abs_self a

中文:
定理 le_of_sq_le_sq
  条件: (h : a ^ 2 <= b ^ 2) (hb : 0 <= b)
  结论: a <= b
  证明: .trans abs_le_of_sq_le_sq h hb le_abs_self a

Depends on / 依赖: abs_le_of_sq_le_sq, le_abs_self
-/
theorem le_of_sq_le_sq (h : a ^ 2 <= b ^ 2) (hb : 0 <= b) : a <= b :=
.trans abs_le_of_sq_le_sq h hb le_abs_self a

/--
lemma `abs_le_of_sq_le_sq'` / 引理 `abs_le_of_sq_le_sq'`

English:
lemma abs_le_of_sq_le_sq'
  given: (h : a ^ 2 <= b ^ 2) (hb : 0 <= b)
  statement: -b <= a ∧ a <= b
  proof: abs_le.1 abs_le_of_sq_le_sq h hb

中文:
引理 abs_le_of_sq_le_sq'
  条件: (h : a ^ 2 <= b ^ 2) (hb : 0 <= b)
  结论: -b <= a ∧ a <= b
  证明: abs_le.1 abs_le_of_sq_le_sq h hb

Depends on / 依赖: abs_le, abs_le_of_sq_le_sq
-/
lemma abs_le_of_sq_le_sq' (h : a ^ 2 <= b ^ 2) (hb : 0 <= b) : -b <= a ∧ a <= b :=
abs_le.1 abs_le_of_sq_le_sq h hb

/--
lemma `sq_eq_sq_iff_abs_eq_abs` / 引理 `sq_eq_sq_iff_abs_eq_abs`

English:
lemma sq_eq_sq_iff_abs_eq_abs
  given: (a b : α)
  statement: a ^ 2 = b ^ 2 ↔ |a| = |b|
  proof: by
  simp only [le_antisymm_iff, sq_le_sq]

中文:
引理 sq_eq_sq_iff_abs_eq_abs
  条件: (a b : α)
  结论: a ^ 2 = b ^ 2 ↔ |a| = |b|
  证明: by
  simp only [le_antisymm_iff, sq_le_sq]

Depends on / 依赖: le_antisymm_iff, sq_le_sq
-/
lemma sq_eq_sq_iff_abs_eq_abs (a b : α) : a ^ 2 = b ^ 2 ↔ |a| = |b| := by
  simp only [le_antisymm_iff, sq_le_sq]

/--
lemma `sq_le_one_iff_abs_le_one` / 引理 `sq_le_one_iff_abs_le_one`

English:
lemma sq_le_one_iff_abs_le_one
  given: (a : α)
  statement: a ^ 2 <= 1 ↔ |a| <= 1
  proof: by
  simpa only [one_pow, abs_one] using sq_le_sq (a := a) (b := 1)

中文:
引理 sq_le_one_iff_abs_le_one
  条件: (a : α)
  结论: a ^ 2 <= 1 ↔ |a| <= 1
  证明: by
  simpa only [one_pow, abs_one] using sq_le_sq (a := a) (b := 1)
-/
@[simp] lemma sq_le_one_iff_abs_le_one (a : α) : a ^ 2 <= 1 ↔ |a| <= 1 := by
  simpa only [one_pow, abs_one] using sq_le_sq (a := a) (b := 1)

/--
lemma `sq_lt_one_iff_abs_lt_one` / 引理 `sq_lt_one_iff_abs_lt_one`

English:
lemma sq_lt_one_iff_abs_lt_one
  given: (a : α)
  statement: a ^ 2 < 1 ↔ |a| < 1
  proof: by
  simpa only [one_pow, abs_one] using sq_lt_sq (a := a) (b := 1)

中文:
引理 sq_lt_one_iff_abs_lt_one
  条件: (a : α)
  结论: a ^ 2 < 1 ↔ |a| < 1
  证明: by
  simpa only [one_pow, abs_one] using sq_lt_sq (a := a) (b := 1)
-/
@[simp] lemma sq_lt_one_iff_abs_lt_one (a : α) : a ^ 2 < 1 ↔ |a| < 1 := by
  simpa only [one_pow, abs_one] using sq_lt_sq (a := a) (b := 1)

/--
lemma `one_le_sq_iff_one_le_abs` / 引理 `one_le_sq_iff_one_le_abs`

English:
lemma one_le_sq_iff_one_le_abs
  given: (a : α)
  statement: 1 <= a ^ 2 ↔ 1 <= |a|
  proof: by
  simpa only [one_pow, abs_one] using sq_le_sq (a := 1) (b := a)

中文:
引理 one_le_sq_iff_one_le_abs
  条件: (a : α)
  结论: 1 <= a ^ 2 ↔ 1 <= |a|
  证明: by
  simpa only [one_pow, abs_one] using sq_le_sq (a := 1) (b := a)
-/
@[simp] lemma one_le_sq_iff_one_le_abs (a : α) : 1 <= a ^ 2 ↔ 1 <= |a| := by
  simpa only [one_pow, abs_one] using sq_le_sq (a := 1) (b := a)

/--
lemma `one_lt_sq_iff_one_lt_abs` / 引理 `one_lt_sq_iff_one_lt_abs`

English:
lemma one_lt_sq_iff_one_lt_abs
  given: (a : α)
  statement: 1 < a ^ 2 ↔ 1 < |a|
  proof: by
  simpa only [one_pow, abs_one] using sq_lt_sq (a := 1) (b := a)

中文:
引理 one_lt_sq_iff_one_lt_abs
  条件: (a : α)
  结论: 1 < a ^ 2 ↔ 1 < |a|
  证明: by
  simpa only [one_pow, abs_one] using sq_lt_sq (a := 1) (b := a)
-/
@[simp] lemma one_lt_sq_iff_one_lt_abs (a : α) : 1 < a ^ 2 ↔ 1 < |a| := by
  simpa only [one_pow, abs_one] using sq_lt_sq (a := 1) (b := a)

end LinearStrictOrderedRing

section LinearOrderedCommRing

variable [CommRing α] [LinearOrder α] (a b : α) (n : Nat)

/--
theorem `abs_sub_sq` / 定理 `abs_sub_sq`

English:
theorem abs_sub_sq
  given: (a b : α)
  statement: |a - b| * |a - b| = a * a + b * b - (1 + 1) * a * b
  proof: by
  rw [abs_mul_abs_self]
  simp only [mul_add, add_comm, add_left_comm, mul_comm, sub_eq_add_neg, mul_one, mul_neg,
    neg_add_rev, neg_neg, add_assoc]

中文:
定理 abs_sub_sq
  条件: (a b : α)
  结论: |a - b| * |a - b| = a * a + b * b - (1 + 1) * a * b
  证明: by
  rw [abs_mul_abs_self]
  simp only [mul_add, add_comm, add_left_comm, mul_comm, sub_eq_add_neg, mul_one, mul_neg,
    neg_add_rev, neg_neg, add_assoc]

Depends on / 依赖: abs_mul_abs_self, add_assoc, add_comm, add_left_comm, mul_add, mul_comm, mul_neg, mul_one, neg_add_rev, neg_neg, sub_eq_add_neg
-/
theorem abs_sub_sq (a b : α) : |a - b| * |a - b| = a * a + b * b - (1 + 1) * a * b := by
  rw [abs_mul_abs_self]
  simp only [mul_add, add_comm, add_left_comm, mul_comm, sub_eq_add_neg, mul_one, mul_neg,
    neg_add_rev, neg_neg, add_assoc]

/--
lemma `abs_unit_intCast` / 引理 `abs_unit_intCast`

English:
lemma abs_unit_intCast
  given: [IsOrderedRing α] (a : Intˣ)
  statement: |((a : Int) : α)| = 1
  proof: by
  cases Int.units_eq_one_or a <;> simp_all

中文:
引理 abs_unit_intCast
  条件: [是Ordered环 α] (a : 整数ˣ)
  结论: |((a : 整数) : α)| = 1
  证明: by
  cases Int.units_eq_one_or a <;> simp_all

Depends on / 依赖: Int.units_eq_one_or, units_eq_one_or
-/
lemma abs_unit_intCast [IsOrderedRing α] (a : Intˣ) : |((a : Int) : α)| = 1 := by
  cases Int.units_eq_one_or a <;> simp_all

/--
Definition of `geomSum` / `geomSum` 的定义

English:
definition geomSum
  signature: : Nat -> α

中文:
定义 geomSum
  签名: : 自然数 -> α
-/
private def geomSum : Nat -> α
  | 0 => 1
  | n + 1 => a * geomSum n + b ^ (n + 1)

/--
theorem `abs_geomSum_le` / 定理 `abs_geomSum_le`

English:
theorem abs_geomSum_le
  given: [IsOrderedRing α]
  statement: |geomSum a b n| <= (n + 1) * max |a| |b| ^ n
  proof: by
  induction n with | zero => simp [geomSum] | succ n ih => ?_
  refine (abs_add_le ..).trans ?_
  rw [abs_mul]; rw [abs_pow]; rw [Nat.cast_succ]; rw [add_one_mul]
  refine add_le_add ?_ (pow_le_pow_left₀ (abs_nonneg _) le_sup_right _)
  rw [pow_succ]; rw [← mul_assoc]; rw [mul_comm |a|]
  gcongr


中文:
定理 abs_geomSum_le
  条件: [是Ordered环 α]
  结论: |geomSum a b n| <= (n + 1) * 最大值 |a| |b| ^ n
  证明: by
  induction n with | zero => simp [geomSum] | succ n ih => ?_
  refine (abs_add_le ..).trans ?_
  rw [abs_mul]; rw [abs_pow]; rw [Nat.cast_succ]; rw [add_one_mul]
  refine add_le_add ?_ (pow_le_pow_left₀ (abs_nonneg _) le_sup_right _)
  rw [pow_succ]; rw [← mul_assoc]; rw [mul_comm |a|]
  gcongr

-/
private theorem abs_geomSum_le [IsOrderedRing α] : |geomSum a b n| <= (n + 1) * max |a| |b| ^ n := by
  induction n with | zero => simp [geomSum] | succ n ih => ?_
  refine (abs_add_le ..).trans ?_
  rw [abs_mul]; rw [abs_pow]; rw [Nat.cast_succ]; rw [add_one_mul]
  refine add_le_add ?_ (pow_le_pow_left₀ (abs_nonneg _) le_sup_right _)
  rw [pow_succ]; rw [← mul_assoc]; rw [mul_comm |a|]
  gcongr
  exacts [abs_nonneg _, (abs_nonneg _).trans ih, le_sup_left]

omit [LinearOrder α] in
/--
theorem `pow_sub_pow_eq_sub_mul_geomSum` / 定理 `pow_sub_pow_eq_sub_mul_geomSum`

English:
theorem pow_sub_pow_eq_sub_mul_geomSum
  proof: by
  induction n with | zero => simp [geomSum] | succ n ih => ?_
  rw [geomSum]; rw [mul_add]; rw [mul_comm a]; rw [← mul_assoc]; rw [← ih]; rw [sub_mul]; rw [sub_mul]; rw [← pow_succ]; rw [← pow_succ']; rw [mul_comm]; rw [sub_add_sub_cancel]

中文:
定理 pow_sub_pow_eq_sub_mul_geomSum
  证明: by
  induction n with | zero => simp [geomSum] | succ n ih => ?_
  rw [geomSum]; rw [mul_add]; rw [mul_comm a]; rw [← mul_assoc]; rw [← ih]; rw [sub_mul]; rw [sub_mul]; rw [← pow_succ]; rw [← pow_succ']; rw [mul_comm]; rw [sub_add_sub_cancel]
-/
private theorem pow_sub_pow_eq_sub_mul_geomSum :
    a ^ (n + 1) - b ^ (n + 1) = (a - b) * geomSum a b n := by
  induction n with | zero => simp [geomSum] | succ n ih => ?_
  rw [geomSum]; rw [mul_add]; rw [mul_comm a]; rw [← mul_assoc]; rw [← ih]; rw [sub_mul]; rw [sub_mul]; rw [← pow_succ]; rw [← pow_succ']; rw [mul_comm]; rw [sub_add_sub_cancel]

/--
theorem `abs_pow_sub_pow_le` / 定理 `abs_pow_sub_pow_le`

English:
theorem abs_pow_sub_pow_le
  given: [IsOrderedRing α]
  proof: by
  obtain _ | n := n; · simp
  rw [Nat.add_sub_cancel]; rw [pow_sub_pow_eq_sub_mul_geomSum]; rw [abs_mul]; rw [mul_assoc]; rw [Nat.cast_succ]
  gcongr
  · exact abs_nonneg _
  · exact abs_geomSum_le ..

中文:
定理 abs_pow_sub_pow_le
  条件: [是Ordered环 α]
  证明: by
  obtain _ | n := n; · simp
  rw [Nat.add_sub_cancel]; rw [pow_sub_pow_eq_sub_mul_geomSum]; rw [abs_mul]; rw [mul_assoc]; rw [Nat.cast_succ]
  gcongr
  · exact abs_nonneg _
  · exact abs_geomSum_le ..

Depends on / 依赖: Nat.add_sub_cancel, Nat.cast_succ, abs_geomSum_le, abs_mul, abs_nonneg, add_sub_cancel, cast_succ, mul_assoc, pow_sub_pow_eq_sub_mul_geomSum
-/
theorem abs_pow_sub_pow_le [IsOrderedRing α] :
    |a ^ n - b ^ n| <= |a - b| * n * max |a| |b| ^ (n - 1) := by
  obtain _ | n := n; · simp
  rw [Nat.add_sub_cancel]; rw [pow_sub_pow_eq_sub_mul_geomSum]; rw [abs_mul]; rw [mul_assoc]; rw [Nat.cast_succ]
  gcongr
  · exact abs_nonneg _
  · exact abs_geomSum_le ..

end LinearOrderedCommRing

section

variable [Ring α] [LinearOrder α]

@[simp]
/--
theorem `abs_dvd` / 定理 `abs_dvd`

English:
theorem abs_dvd
  given: (a b : α)
  statement: |a| ∣ b ↔ a ∣ b
  proof: by
  rcases abs_choice a with h | h <;> simp only [h, neg_dvd]

中文:
定理 abs_dvd
  条件: (a b : α)
  结论: |a| ∣ b ↔ a ∣ b
  证明: by
  rcases abs_choice a with h | h <;> simp only [h, neg_dvd]

Depends on / 依赖: abs_choice, neg_dvd
-/
theorem abs_dvd (a b : α) : |a| ∣ b ↔ a ∣ b := by
  rcases abs_choice a with h | h <;> simp only [h, neg_dvd]

/--
theorem `abs_dvd_self` / 定理 `abs_dvd_self`

English:
theorem abs_dvd_self
  given: (a : α)
  statement: |a| ∣ a
  proof: (abs_dvd a a).mpr (dvd_refl a)

@[simp]

中文:
定理 abs_dvd_self
  条件: (a : α)
  结论: |a| ∣ a
  证明: (abs_dvd a a).mpr (dvd_refl a)

@[simp]

Depends on / 依赖: abs_dvd, dvd_refl
-/
theorem abs_dvd_self (a : α) : |a| ∣ a :=
  (abs_dvd a a).mpr (dvd_refl a)

@[simp]
/--
theorem `dvd_abs` / 定理 `dvd_abs`

English:
theorem dvd_abs
  given: (a b : α)
  statement: a ∣ |b| ↔ a ∣ b
  proof: by
  rcases abs_choice b with h | h <;> simp only [h, dvd_neg]

中文:
定理 dvd_abs
  条件: (a b : α)
  结论: a ∣ |b| ↔ a ∣ b
  证明: by
  rcases abs_choice b with h | h <;> simp only [h, dvd_neg]

Depends on / 依赖: abs_choice, dvd_neg
-/
theorem dvd_abs (a b : α) : a ∣ |b| ↔ a ∣ b := by
  rcases abs_choice b with h | h <;> simp only [h, dvd_neg]

/--
theorem `self_dvd_abs` / 定理 `self_dvd_abs`

English:
theorem self_dvd_abs
  given: (a : α)
  statement: a ∣ |a|
  proof: (dvd_abs a a).mpr (dvd_refl a)

中文:
定理 self_dvd_abs
  条件: (a : α)
  结论: a ∣ |a|
  证明: (dvd_abs a a).mpr (dvd_refl a)

Depends on / 依赖: dvd_abs, dvd_refl
-/
theorem self_dvd_abs (a : α) : a ∣ |a| :=
  (dvd_abs a a).mpr (dvd_refl a)

/--
theorem `abs_dvd_abs` / 定理 `abs_dvd_abs`

English:
theorem abs_dvd_abs
  given: (a b : α)
  statement: |a| ∣ |b| ↔ a ∣ b
  proof: (abs_dvd _ _).trans (dvd_abs _ _)

中文:
定理 abs_dvd_abs
  条件: (a b : α)
  结论: |a| ∣ |b| ↔ a ∣ b
  证明: (abs_dvd _ _).trans (dvd_abs _ _)

Depends on / 依赖: abs_dvd, dvd_abs
-/
theorem abs_dvd_abs (a b : α) : |a| ∣ |b| ↔ a ∣ b :=
  (abs_dvd _ _).trans (dvd_abs _ _)

end

open Nat

section LinearOrderedRing
variable {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] {a b : R} {n : Nat}

/--
lemma `pow_eq_pow_iff_of_ne_zero` / 引理 `pow_eq_pow_iff_of_ne_zero`

English:
lemma pow_eq_pow_iff_of_ne_zero
  given: (hn : n != 0)
  statement: a ^ n = b ^ n ↔ a = b ∨ a = -b ∧ Even n
  proof: match n.even_xor_odd with
  | .inl hne => by simp only [*, and_true, ← abs_eq_abs,
    ← pow_left_inj₀ (abs_nonneg a) (abs_nonneg b) hn, hne.1.pow_abs]
  | .inr hn => by simp [hn, (hn.1.strictMono_pow (R := R)).injective.eq_iff]

中文:
引理 pow_eq_pow_iff_of_ne_zero
  条件: (hn : n != 0)
  结论: a ^ n = b ^ n ↔ a = b ∨ a = -b ∧ Even n
  证明: match n.even_xor_odd with
  | .inl hne => by simp only [*, and_true, ← abs_eq_abs,
    ← pow_left_inj₀ (abs_nonneg a) (abs_nonneg b) hn, hne.1.pow_abs]
  | .inr hn => by simp [hn, (hn.1.strictMono_pow (R := R)).injective.eq_iff]

Depends on / 依赖: abs_eq_abs, abs_nonneg, and_true, eq_iff, even_xor_odd, injective, injective.eq_iff, n.even_xor_odd, pow_abs, strictMono_pow
-/
lemma pow_eq_pow_iff_of_ne_zero (hn : n != 0) : a ^ n = b ^ n ↔ a = b ∨ a = -b ∧ Even n :=
  match n.even_xor_odd with
  | .inl hne => by simp only [*, and_true, ← abs_eq_abs,
    ← pow_left_inj₀ (abs_nonneg a) (abs_nonneg b) hn, hne.1.pow_abs]
  | .inr hn => by simp [hn, (hn.1.strictMono_pow (R := R)).injective.eq_iff]

/--
lemma `pow_eq_pow_iff_cases` / 引理 `pow_eq_pow_iff_cases`

English:
lemma pow_eq_pow_iff_cases
  statement: a ^ n = b ^ n ↔ n = 0 ∨ a = b ∨ a = -b ∧ Even n
  proof: by
  rcases eq_or_ne n 0 with rfl | hn <;> simp [pow_eq_pow_iff_of_ne_zero, *]

中文:
引理 pow_eq_pow_iff_cases
  结论: a ^ n = b ^ n ↔ n = 0 ∨ a = b ∨ a = -b ∧ Even n
  证明: by
  rcases eq_or_ne n 0 with rfl | hn <;> simp [pow_eq_pow_iff_of_ne_zero, *]

Depends on / 依赖: eq_or_ne, pow_eq_pow_iff_of_ne_zero
-/
lemma pow_eq_pow_iff_cases : a ^ n = b ^ n ↔ n = 0 ∨ a = b ∨ a = -b ∧ Even n := by
  rcases eq_or_ne n 0 with rfl | hn <;> simp [pow_eq_pow_iff_of_ne_zero, *]

/--
lemma `pow_eq_one_iff_of_ne_zero` / 引理 `pow_eq_one_iff_of_ne_zero`

English:
lemma pow_eq_one_iff_of_ne_zero
  given: (hn : n != 0)
  statement: a ^ n = 1 ↔ a = 1 ∨ a = -1 ∧ Even n
  proof: by
  simp [← pow_eq_pow_iff_of_ne_zero hn]

中文:
引理 pow_eq_one_iff_of_ne_zero
  条件: (hn : n != 0)
  结论: a ^ n = 1 ↔ a = 1 ∨ a = -1 ∧ Even n
  证明: by
  simp [← pow_eq_pow_iff_of_ne_zero hn]

Depends on / 依赖: pow_eq_pow_iff_of_ne_zero
-/
lemma pow_eq_one_iff_of_ne_zero (hn : n != 0) : a ^ n = 1 ↔ a = 1 ∨ a = -1 ∧ Even n := by
  simp [← pow_eq_pow_iff_of_ne_zero hn]

/--
lemma `pow_eq_one_iff_cases` / 引理 `pow_eq_one_iff_cases`

English:
lemma pow_eq_one_iff_cases
  statement: a ^ n = 1 ↔ n = 0 ∨ a = 1 ∨ a = -1 ∧ Even n
  proof: by
  simp [← pow_eq_pow_iff_cases]

中文:
引理 pow_eq_one_iff_cases
  结论: a ^ n = 1 ↔ n = 0 ∨ a = 1 ∨ a = -1 ∧ Even n
  证明: by
  simp [← pow_eq_pow_iff_cases]

Depends on / 依赖: pow_eq_pow_iff_cases
-/
lemma pow_eq_one_iff_cases : a ^ n = 1 ↔ n = 0 ∨ a = 1 ∨ a = -1 ∧ Even n := by
  simp [← pow_eq_pow_iff_cases]

/--
lemma `pow_eq_neg_pow_iff` / 引理 `pow_eq_neg_pow_iff`

English:
lemma pow_eq_neg_pow_iff
  given: (hb : b != 0)
  statement: a ^ n = -b ^ n ↔ a = -b ∧ Odd n
  proof: match n.even_or_odd with
  | .inl he =>
    suffices a ^ n > -b ^ n by simpa [he, not_odd_iff_even.2 he] using this.ne'
    lt_of_lt_of_le (by simp [he.pow_pos hb]) (he.pow_nonneg _)
  | .inr ho => by
    simp only [ho, and_true, ← ho.neg_pow, (ho.strictMono_pow (R := R)).injective.eq_iff]

中文:
引理 pow_eq_neg_pow_iff
  条件: (hb : b != 0)
  结论: a ^ n = -b ^ n ↔ a = -b ∧ Odd n
  证明: match n.even_or_odd with
  | .inl he =>
    suffices a ^ n > -b ^ n by simpa [he, not_odd_iff_even.2 he] using this.ne'
    lt_of_lt_of_le (by simp [he.pow_pos hb]) (he.pow_nonneg _)
  | .inr ho => by
    simp only [ho, and_true, ← ho.neg_pow, (ho.strictMono_pow (R := R)).injective.eq_iff]

Depends on / 依赖: and_true, eq_iff, even_or_odd, he.pow_nonneg, he.pow_pos, ho.neg_pow, ho.strictMono_pow, injective, injective.eq_iff, lt_of_lt_of_le, n.even_or_odd, neg_pow, not_odd_iff_even, pow_nonneg, pow_pos, strictMono_pow, this.ne
-/
lemma pow_eq_neg_pow_iff (hb : b != 0) : a ^ n = -b ^ n ↔ a = -b ∧ Odd n :=
  match n.even_or_odd with
  | .inl he =>
    suffices a ^ n > -b ^ n by simpa [he, not_odd_iff_even.2 he] using this.ne'
    lt_of_lt_of_le (by simp [he.pow_pos hb]) (he.pow_nonneg _)
  | .inr ho => by
    simp only [ho, and_true, ← ho.neg_pow, (ho.strictMono_pow (R := R)).injective.eq_iff]

/--
lemma `pow_eq_neg_one_iff` / 引理 `pow_eq_neg_one_iff`

English:
lemma pow_eq_neg_one_iff
  statement: a ^ n = -1 ↔ a = -1 ∧ Odd n
  proof: by
  simpa using pow_eq_neg_pow_iff (R := R) one_ne_zero

中文:
引理 pow_eq_neg_one_iff
  结论: a ^ n = -1 ↔ a = -1 ∧ Odd n
  证明: by
  simpa using pow_eq_neg_pow_iff (R := R) one_ne_zero

Depends on / 依赖: one_ne_zero, pow_eq_neg_pow_iff
-/
lemma pow_eq_neg_one_iff : a ^ n = -1 ↔ a = -1 ∧ Odd n := by
  simpa using pow_eq_neg_pow_iff (R := R) one_ne_zero

end LinearOrderedRing

variable {m n a : Nat}

/--
lemma `Odd.mod_even_iff` / 引理 `Odd.mod_even_iff`

English:
lemma Odd.mod_even_iff
  given: (ha : Even a)
  statement: Odd (n % a) ↔ Odd n
  proof: ((even_sub' <| mod_le n a).mp <|
even_iff_two_dvd.mpr (even_iff_two_dvd.mp ha).trans dvd_sub_mod n).symm

中文:
引理 Odd.mod_even_iff
  条件: (ha : Even a)
  结论: Odd (n % a) ↔ Odd n
  证明: ((even_sub' <| mod_le n a).mp <|
even_iff_two_dvd.mpr (even_iff_two_dvd.mp ha).trans dvd_sub_mod n).symm

Depends on / 依赖: dvd_sub_mod, even_iff_two_dvd, even_iff_two_dvd.mp, even_iff_two_dvd.mpr, even_sub, mod_le
-/
lemma Odd.mod_even_iff (ha : Even a) : Odd (n % a) ↔ Odd n :=
  ((even_sub' <| mod_le n a).mp <|
even_iff_two_dvd.mpr (even_iff_two_dvd.mp ha).trans dvd_sub_mod n).symm

/--
lemma `Even.mod_even_iff` / 引理 `Even.mod_even_iff`

English:
lemma Even.mod_even_iff
  given: (ha : Even a)
  statement: Even (n % a) ↔ Even n
  proof: ((even_sub <| mod_le n a).mp <|
even_iff_two_dvd.mpr (even_iff_two_dvd.mp ha).trans dvd_sub_mod n).symm

中文:
引理 Even.mod_even_iff
  条件: (ha : Even a)
  结论: Even (n % a) ↔ Even n
  证明: ((even_sub <| mod_le n a).mp <|
even_iff_two_dvd.mpr (even_iff_two_dvd.mp ha).trans dvd_sub_mod n).symm

Depends on / 依赖: dvd_sub_mod, even_iff_two_dvd, even_iff_two_dvd.mp, even_iff_two_dvd.mpr, even_sub, mod_le
-/
lemma Even.mod_even_iff (ha : Even a) : Even (n % a) ↔ Even n :=
  ((even_sub <| mod_le n a).mp <|
even_iff_two_dvd.mpr (even_iff_two_dvd.mp ha).trans dvd_sub_mod n).symm

/--
lemma `Odd.mod_even` / 引理 `Odd.mod_even`

English:
lemma Odd.mod_even
  given: (hn : Odd n) (ha : Even a)
  statement: Odd (n % a)
  proof: (Odd.mod_even_iff ha).mpr hn

中文:
引理 Odd.mod_even
  条件: (hn : Odd n) (ha : Even a)
  结论: Odd (n % a)
  证明: (Odd.mod_even_iff ha).mpr hn

Depends on / 依赖: Odd.mod_even_iff, mod_even_iff
-/
lemma Odd.mod_even (hn : Odd n) (ha : Even a) : Odd (n % a) := (Odd.mod_even_iff ha).mpr hn

/--
lemma `Even.mod_even` / 引理 `Even.mod_even`

English:
lemma Even.mod_even
  given: (hn : Even n) (ha : Even a)
  statement: Even (n % a)
  proof: (Even.mod_even_iff ha).mpr hn

中文:
引理 Even.mod_even
  条件: (hn : Even n) (ha : Even a)
  结论: Even (n % a)
  证明: (Even.mod_even_iff ha).mpr hn

Depends on / 依赖: Even.mod_even_iff, mod_even_iff
-/
lemma Even.mod_even (hn : Even n) (ha : Even a) : Even (n % a) :=
  (Even.mod_even_iff ha).mpr hn

/--
lemma `Odd.of_dvd_nat` / 引理 `Odd.of_dvd_nat`

English:
lemma Odd.of_dvd_nat
  given: (hn : Odd n) (hm : m ∣ n)
  statement: Odd m
  proof: not_even_iff_odd.1 mt hm.even (not_even_iff_odd.2 hn)

中文:
引理 Odd.of_dvd_nat
  条件: (hn : Odd n) (hm : m ∣ n)
  结论: Odd m
  证明: not_even_iff_odd.1 mt hm.even (not_even_iff_odd.2 hn)

Depends on / 依赖: hm.even, not_even_iff_odd
-/
lemma Odd.of_dvd_nat (hn : Odd n) (hm : m ∣ n) : Odd m :=
not_even_iff_odd.1 mt hm.even (not_even_iff_odd.2 hn)

/--
lemma `Odd.ne_two_of_dvd_nat` / 引理 `Odd.ne_two_of_dvd_nat`

English:
lemma Odd.ne_two_of_dvd_nat
  given: {m n : Nat} (hn : Odd n) (hm : m ∣ n)
  statement: m != 2
  proof: by
  rintro rfl
  exact absurd (hn.of_dvd_nat hm) (by decide)

中文:
引理 Odd.ne_two_of_dvd_nat
  条件: {m n : 自然数} (hn : Odd n) (hm : m ∣ n)
  结论: m != 2
  证明: by
  rintro rfl
  exact absurd (hn.of_dvd_nat hm) (by decide)

Depends on / 依赖: absurd, hn.of_dvd_nat, of_dvd_nat
-/
lemma Odd.ne_two_of_dvd_nat {m n : Nat} (hn : Odd n) (hm : m ∣ n) : m != 2 := by
  rintro rfl
  exact absurd (hn.of_dvd_nat hm) (by decide)

/--
lemma `Int.le_abs_of_dvd` / 引理 `Int.le_abs_of_dvd`

English:
lemma Int.le_abs_of_dvd
  given: {a b : Int} (h₁ : b != 0) (h₂ : a ∣ b)
  statement: a <= |b|
  proof: le_of_dvd (by simpa) (by simpa)

中文:
引理 整数.le_abs_of_dvd
  条件: {a b : 整数} (h₁ : b != 0) (h₂ : a ∣ b)
  结论: a <= |b|
  证明: le_of_dvd (by simpa) (by simpa)

Depends on / 依赖: le_of_dvd
-/
lemma Int.le_abs_of_dvd {a b : Int} (h₁ : b != 0) (h₂ : a ∣ b) : a <= |b| :=
  le_of_dvd (by simpa) (by simpa)
