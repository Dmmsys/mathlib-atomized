/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Johan Commelin
-/
module

public import Mathlib.Algebra.Ring.Int.Parity
public import Mathlib.Algebra.Ring.Int.Units
public import Mathlib.Data.ZMod.IntUnitsPower

/-!
# Integer powers of (-1)

This file defines the map `negOnePow : ℤ → ℤˣ` which sends `n` to `(-1 : ℤˣ) ^ n`.

The definition of `negOnePow` and some lemmas first appeared in contributions by
Johan Commelin to the Liquid Tensor Experiment.

-/

@[expose] public section

assert_not_exists Field
assert_not_exists TwoSidedIdeal

namespace Int

/--
Definition of `negOnePow` / `negOnePow` 的定义

English:
definition negOnePow
  signature: (n : Int)
  body: (-1 : Intˣ) ^ n

中文:
定义 negOnePow
  签名: (n : 整数)
  定义体: (-1 : Intˣ) ^ n
-/
def negOnePow (n : Int) : Intˣ := (-1 : Intˣ) ^ n

/--
lemma `negOnePow_def` / 引理 `negOnePow_def`

English:
lemma negOnePow_def
  given: (n : Int)
  statement: n.negOnePow = (-1 : Intˣ) ^ n
  proof: rfl

中文:
引理 negOnePow_def
  条件: (n : 整数)
  结论: n.negOnePow = (-1 : 整数ˣ) ^ n
  证明: rfl
-/
lemma negOnePow_def (n : Int) : n.negOnePow = (-1 : Intˣ) ^ n := rfl

/--
lemma `negOnePow_add` / 引理 `negOnePow_add`

English:
lemma negOnePow_add
  given: (n₁ n₂ : Int)
  proof: zpow_add _ _ _

@[simp]

中文:
引理 negOnePow_add
  条件: (n₁ n₂ : 整数)
  证明: zpow_add _ _ _

@[simp]

Depends on / 依赖: zpow_add
-/
lemma negOnePow_add (n₁ n₂ : Int) :
    (n₁ + n₂).negOnePow = n₁.negOnePow * n₂.negOnePow :=
  zpow_add _ _ _

@[simp]
/--
lemma `negOnePow_zero` / 引理 `negOnePow_zero`

English:
lemma negOnePow_zero
  statement: negOnePow 0 = 1
  proof: rfl

@[simp]

中文:
引理 negOnePow_zero
  结论: negOnePow 0 = 1
  证明: rfl

@[simp]

Depends on / 依赖: infer_instance, opensFunctor
-/
lemma negOnePow_zero : negOnePow 0 = 1 := rfl

@[simp]
/--
lemma `negOnePow_one` / 引理 `negOnePow_one`

English:
lemma negOnePow_one
  statement: negOnePow 1 = -1
  proof: rfl

中文:
引理 negOnePow_one
  结论: negOnePow 1 = -1
  证明: rfl
-/
lemma negOnePow_one : negOnePow 1 = -1 := rfl

/--
lemma `negOnePow_succ` / 引理 `negOnePow_succ`

English:
lemma negOnePow_succ
  given: (n : Int)
  statement: (n + 1).negOnePow = -n.negOnePow
  proof: by
  rw [negOnePow_add]; rw [negOnePow_one]; rw [mul_neg]; rw [mul_one]

中文:
引理 negOnePow_succ
  条件: (n : 整数)
  结论: (n + 1).negOnePow = -n.negOnePow
  证明: by
  rw [negOnePow_add]; rw [negOnePow_one]; rw [mul_neg]; rw [mul_one]

Depends on / 依赖: mul_neg, mul_one, negOnePow_add, negOnePow_one
-/
lemma negOnePow_succ (n : Int) : (n + 1).negOnePow = -n.negOnePow := by
  rw [negOnePow_add]; rw [negOnePow_one]; rw [mul_neg]; rw [mul_one]

/--
lemma `negOnePow_even` / 引理 `negOnePow_even`

English:
lemma negOnePow_even
  given: (n : Int) (hn : Even n)
  statement: n.negOnePow = 1
  proof: by
  obtain ⟨k, rfl⟩ := hn
  rw [negOnePow_add]; rw [units_mul_self]

@[simp]

中文:
引理 negOnePow_even
  条件: (n : 整数) (hn : Even n)
  结论: n.negOnePow = 1
  证明: by
  obtain ⟨k, rfl⟩ := hn
  rw [negOnePow_add]; rw [units_mul_self]

@[simp]

Depends on / 依赖: negOnePow_add, units_mul_self
-/
lemma negOnePow_even (n : Int) (hn : Even n) : n.negOnePow = 1 := by
  obtain ⟨k, rfl⟩ := hn
  rw [negOnePow_add]; rw [units_mul_self]

@[simp]
/--
lemma `negOnePow_two_mul` / 引理 `negOnePow_two_mul`

English:
lemma negOnePow_two_mul
  given: (n : Int)
  statement: (2 * n).negOnePow = 1
  proof: negOnePow_even _ ⟨n, two_mul n⟩

中文:
引理 negOnePow_two_mul
  条件: (n : 整数)
  结论: (2 * n).negOnePow = 1
  证明: negOnePow_even _ ⟨n, two_mul n⟩

Depends on / 依赖: negOnePow_even, two_mul
-/
lemma negOnePow_two_mul (n : Int) : (2 * n).negOnePow = 1 :=
  negOnePow_even _ ⟨n, two_mul n⟩

/--
lemma `negOnePow_odd` / 引理 `negOnePow_odd`

English:
lemma negOnePow_odd
  given: (n : Int) (hn : Odd n)
  statement: n.negOnePow = -1
  proof: by
  obtain ⟨k, rfl⟩ := hn
  simp only [negOnePow_add, negOnePow_two_mul, negOnePow_one, mul_neg, mul_one]

@[simp]

中文:
引理 negOnePow_odd
  条件: (n : 整数) (hn : Odd n)
  结论: n.negOnePow = -1
  证明: by
  obtain ⟨k, rfl⟩ := hn
  simp only [negOnePow_add, negOnePow_two_mul, negOnePow_one, mul_neg, mul_one]

@[simp]

Depends on / 依赖: mul_neg, mul_one, negOnePow_add, negOnePow_one, negOnePow_two_mul
-/
lemma negOnePow_odd (n : Int) (hn : Odd n) : n.negOnePow = -1 := by
  obtain ⟨k, rfl⟩ := hn
  simp only [negOnePow_add, negOnePow_two_mul, negOnePow_one, mul_neg, mul_one]

@[simp]
/--
lemma `negOnePow_two_mul_add_one` / 引理 `negOnePow_two_mul_add_one`

English:
lemma negOnePow_two_mul_add_one
  given: (n : Int)
  statement: (2 * n + 1).negOnePow = -1
  proof: negOnePow_odd _ ⟨n, rfl⟩

中文:
引理 negOnePow_two_mul_add_one
  条件: (n : 整数)
  结论: (2 * n + 1).negOnePow = -1
  证明: negOnePow_odd _ ⟨n, rfl⟩

Depends on / 依赖: negOnePow_odd
-/
lemma negOnePow_two_mul_add_one (n : Int) : (2 * n + 1).negOnePow = -1 :=
  negOnePow_odd _ ⟨n, rfl⟩

/--
lemma `negOnePow_eq_one_iff` / 引理 `negOnePow_eq_one_iff`

English:
lemma negOnePow_eq_one_iff
  given: (n : Int)
  statement: n.negOnePow = 1 ↔ Even n
  proof: by
  constructor
  · intro h
    rw [← Int.not_odd_iff_even]
    intro h'
    simp only [negOnePow_odd _ h'] at h
    contradiction
  · exact negOnePow_even n

中文:
引理 negOnePow_eq_one_iff
  条件: (n : 整数)
  结论: n.negOnePow = 1 ↔ Even n
  证明: by
  constructor
  · intro h
    rw [← Int.not_odd_iff_even]
    intro h'
    simp only [negOnePow_odd _ h'] at h
    contradiction
  · exact negOnePow_even n

Depends on / 依赖: Int.not_odd_iff_even, negOnePow_even, negOnePow_odd, not_odd_iff_even
-/
lemma negOnePow_eq_one_iff (n : Int) : n.negOnePow = 1 ↔ Even n := by
  constructor
  · intro h
    rw [← Int.not_odd_iff_even]
    intro h'
    simp only [negOnePow_odd _ h'] at h
    contradiction
  · exact negOnePow_even n

/--
lemma `negOnePow_eq_neg_one_iff` / 引理 `negOnePow_eq_neg_one_iff`

English:
lemma negOnePow_eq_neg_one_iff
  given: (n : Int)
  statement: n.negOnePow = -1 ↔ Odd n
  proof: by
  constructor
  · intro h
    rw [← Int.not_even_iff_odd]
    intro h'
    rw [negOnePow_even _ h'] at h
    contradiction
  · exact negOnePow_odd n

中文:
引理 negOnePow_eq_neg_one_iff
  条件: (n : 整数)
  结论: n.negOnePow = -1 ↔ Odd n
  证明: by
  constructor
  · intro h
    rw [← Int.not_even_iff_odd]
    intro h'
    rw [negOnePow_even _ h'] at h
    contradiction
  · exact negOnePow_odd n

Depends on / 依赖: Int.not_even_iff_odd, negOnePow_even, negOnePow_odd, not_even_iff_odd
-/
lemma negOnePow_eq_neg_one_iff (n : Int) : n.negOnePow = -1 ↔ Odd n := by
  constructor
  · intro h
    rw [← Int.not_even_iff_odd]
    intro h'
    rw [negOnePow_even _ h'] at h
    contradiction
  · exact negOnePow_odd n

/--
theorem `abs_negOnePow` / 定理 `abs_negOnePow`

English:
theorem abs_negOnePow
  given: (n : Int)
  statement: |(n.negOnePow : Int)| = 1
  proof: by
  rw [abs_eq_natAbs]; rw [Int.units_natAbs]; rw [Nat.cast_one]

中文:
定理 abs_negOnePow
  条件: (n : 整数)
  结论: |(n.negOnePow : 整数)| = 1
  证明: by
  rw [abs_eq_natAbs]; rw [Int.units_natAbs]; rw [Nat.cast_one]

Depends on / 依赖: Int.units_natAbs, Nat.cast_one, abs_eq_natAbs, cast_one, units_natAbs
-/
theorem abs_negOnePow (n : Int) : |(n.negOnePow : Int)| = 1 := by
  rw [abs_eq_natAbs]; rw [Int.units_natAbs]; rw [Nat.cast_one]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `negOnePow_neg` / 引理 `negOnePow_neg`

English:
lemma negOnePow_neg
  given: (n : Int)
  statement: (-n).negOnePow = n.negOnePow
  proof: by
  dsimp [negOnePow]
  simp only [zpow_neg, ← inv_zpow, inv_neg, inv_one]

@[simp]

中文:
引理 negOnePow_neg
  条件: (n : 整数)
  结论: (-n).negOnePow = n.negOnePow
  证明: by
  dsimp [negOnePow]
  simp only [zpow_neg, ← inv_zpow, inv_neg, inv_one]

@[simp]

Depends on / 依赖: inv_neg, inv_one, inv_zpow, negOnePow, zpow_neg
-/
lemma negOnePow_neg (n : Int) : (-n).negOnePow = n.negOnePow := by
  dsimp [negOnePow]
  simp only [zpow_neg, ← inv_zpow, inv_neg, inv_one]

@[simp]
/--
lemma `negOnePow_abs` / 引理 `negOnePow_abs`

English:
lemma negOnePow_abs
  given: (n : Int)
  statement: |n|.negOnePow = n.negOnePow
  proof: by
  obtain h | h := abs_choice n <;> simp only [h, negOnePow_neg]

中文:
引理 negOnePow_abs
  条件: (n : 整数)
  结论: |n|.negOnePow = n.negOnePow
  证明: by
  obtain h | h := abs_choice n <;> simp only [h, negOnePow_neg]

Depends on / 依赖: abs_choice, negOnePow_neg
-/
lemma negOnePow_abs (n : Int) : |n|.negOnePow = n.negOnePow := by
  obtain h | h := abs_choice n <;> simp only [h, negOnePow_neg]

/--
lemma `negOnePow_sub` / 引理 `negOnePow_sub`

English:
lemma negOnePow_sub
  given: (n₁ n₂ : Int)
  proof: by
  simp only [sub_eq_add_neg, negOnePow_add, negOnePow_neg]

中文:
引理 negOnePow_sub
  条件: (n₁ n₂ : 整数)
  证明: by
  simp only [sub_eq_add_neg, negOnePow_add, negOnePow_neg]

Depends on / 依赖: negOnePow_add, negOnePow_neg, sub_eq_add_neg
-/
lemma negOnePow_sub (n₁ n₂ : Int) :
    (n₁ - n₂).negOnePow = n₁.negOnePow * n₂.negOnePow := by
  simp only [sub_eq_add_neg, negOnePow_add, negOnePow_neg]

/--
lemma `negOnePow_eq_iff` / 引理 `negOnePow_eq_iff`

English:
lemma negOnePow_eq_iff
  given: (n₁ n₂ : Int)
  proof: by
  by_cases h₂ : Even n₂
  · rw [negOnePow_even _ h₂, Int.even_sub, negOnePow_eq_one_iff]
    tauto
  · rw [Int.not_even_iff_odd] at h₂
    rw [negOnePow_odd _ h₂]; rw [Int.even_sub]; rw [negOnePow_eq_neg_one_iff]; rw [← Int.not_odd_iff_even]; rw [← Int.not_odd_iff_even]
    tauto

@[simp]

中文:
引理 negOnePow_eq_iff
  条件: (n₁ n₂ : 整数)
  证明: by
  by_cases h₂ : Even n₂
  · rw [negOnePow_even _ h₂, Int.even_sub, negOnePow_eq_one_iff]
    tauto
  · rw [Int.not_even_iff_odd] at h₂
    rw [negOnePow_odd _ h₂]; rw [Int.even_sub]; rw [negOnePow_eq_neg_one_iff]; rw [← Int.not_odd_iff_even]; rw [← Int.not_odd_iff_even]
    tauto

@[simp]

Depends on / 依赖: Int.even_sub, Int.not_even_iff_odd, Int.not_odd_iff_even, even_sub, negOnePow_eq_neg_one_iff, negOnePow_eq_one_iff, negOnePow_even, negOnePow_odd, not_even_iff_odd, not_odd_iff_even
-/
lemma negOnePow_eq_iff (n₁ n₂ : Int) :
    n₁.negOnePow = n₂.negOnePow ↔ Even (n₁ - n₂) := by
  by_cases h₂ : Even n₂
  · rw [negOnePow_even _ h₂, Int.even_sub, negOnePow_eq_one_iff]
    tauto
  · rw [Int.not_even_iff_odd] at h₂
    rw [negOnePow_odd _ h₂]; rw [Int.even_sub]; rw [negOnePow_eq_neg_one_iff]; rw [← Int.not_odd_iff_even]; rw [← Int.not_odd_iff_even]
    tauto

@[simp]
/--
lemma `negOnePow_mul_self` / 引理 `negOnePow_mul_self`

English:
lemma negOnePow_mul_self
  given: (n : Int)
  statement: (n * n).negOnePow = n.negOnePow
  proof: by
  simpa [mul_sub, negOnePow_eq_iff] using n.even_mul_pred_self

中文:
引理 negOnePow_mul_self
  条件: (n : 整数)
  结论: (n * n).negOnePow = n.negOnePow
  证明: by
  simpa [mul_sub, negOnePow_eq_iff] using n.even_mul_pred_self

Depends on / 依赖: even_mul_pred_self, mul_sub, n.even_mul_pred_self, negOnePow_eq_iff
-/
lemma negOnePow_mul_self (n : Int) : (n * n).negOnePow = n.negOnePow := by
  simpa [mul_sub, negOnePow_eq_iff] using n.even_mul_pred_self

/--
lemma `cast_negOnePow_natCast` / 引理 `cast_negOnePow_natCast`

English:
lemma cast_negOnePow_natCast
  given: (R : Type*) [Ring R] (n : Nat)
  statement: negOnePow n = (-1 : R) ^ n
  proof: by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n <;> simp [pow_succ, pow_mul]

中文:
引理 cast_negOnePow_natCast
  条件: (R : 类型) [Ring R] (n : 自然数)
  结论: negOnePow n = (-1 : R) ^ n
  证明: by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n <;> simp [pow_succ, pow_mul]

Depends on / 依赖: Nat.even_or_odd, even_or_odd, pow_mul, pow_succ
-/
lemma cast_negOnePow_natCast (R : Type*) [Ring R] (n : Nat) : negOnePow n = (-1 : R) ^ n := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n <;> simp [pow_succ, pow_mul]

/--
lemma `coe_negOnePow_natCast` / 引理 `coe_negOnePow_natCast`

English:
lemma coe_negOnePow_natCast
  given: (n : Nat)
  statement: negOnePow n = (-1 : Int) ^ n
  proof: cast_negOnePow_natCast ..

中文:
引理 coe_negOnePow_natCast
  条件: (n : 自然数)
  结论: negOnePow n = (-1 : 整数) ^ n
  证明: cast_negOnePow_natCast ..

Depends on / 依赖: cast_negOnePow_natCast
-/
lemma coe_negOnePow_natCast (n : Nat) : negOnePow n = (-1 : Int) ^ n := cast_negOnePow_natCast ..

set_option backward.isDefEq.respectTransparency false in
/-- The cast of `negOnePow n` to a ring equals `(-1) ^ n.natAbs`. -/
@[simp]
/--
lemma `coe_negOnePow` / 引理 `coe_negOnePow`

English:
lemma coe_negOnePow
  given: (R : Type*) [Ring R] (n : Int)
  proof: by
  cases n with
  | ofNat n => exact cast_negOnePow_natCast R n
  | negSucc n => simp [negOnePow_def, Units.val_pow_eq_pow_val]

中文:
引理 coe_negOnePow
  条件: (R : 类型) [Ring R] (n : 整数)
  证明: by
  cases n with
  | ofNat n => exact cast_negOnePow_natCast R n
  | negSucc n => simp [negOnePow_def, Units.val_pow_eq_pow_val]

Depends on / 依赖: Units.val_pow_eq_pow_val, cast_negOnePow_natCast, isOpenImmersion_SpecMap_localizationAway, negOnePow_def, negSucc, val_pow_eq_pow_val
-/
lemma coe_negOnePow (R : Type*) [Ring R] (n : Int) :
    (n.negOnePow : R) = (-1 : R) ^ n.natAbs := by
  cases n with
  | ofNat n => exact cast_negOnePow_natCast R n
  | negSucc n => simp [negOnePow_def, Units.val_pow_eq_pow_val]

end Int
