/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
module

public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Data.Int.Sqrt

/-!
# Parity of integers
-/

public section

open Nat

namespace Int

/-! #### Parity -/

variable {m n : Int}

/--
lemma `emod_two_ne_one` / 引理 `emod_two_ne_one`

English:
lemma emod_two_ne_one
  statement: ¬n % 2 = 1 ↔ n % 2 = 0
  proof: by grind

中文:
引理 emod_two_ne_one
  结论: ¬n % 2 = 1 ↔ n % 2 = 0
  证明: by grind
-/
@[simp] lemma emod_two_ne_one : ¬n % 2 = 1 ↔ n % 2 = 0 := by grind

/--
lemma `one_emod_two` / 引理 `one_emod_two`

English:
lemma one_emod_two
  statement: (1 : Int) % 2 = 1
  proof: rfl

中文:
引理 one_emod_two
  结论: (1 : 整数) % 2 = 1
  证明: rfl
-/
@[simp] lemma one_emod_two : (1 : Int) % 2 = 1 := rfl

-- `EuclideanDomain.mod_eq_zero` uses (2 ∣ n) as normal form
/--
lemma `emod_two_ne_zero` / 引理 `emod_two_ne_zero`

English:
lemma emod_two_ne_zero
  statement: ¬n % 2 = 0 ↔ n % 2 = 1
  proof: by grind

@[grind =]

中文:
引理 emod_two_ne_zero
  结论: ¬n % 2 = 0 ↔ n % 2 = 1
  证明: by grind

@[grind =]
-/
@[local simp] lemma emod_two_ne_zero : ¬n % 2 = 0 ↔ n % 2 = 1 := by grind

@[grind =]
/--
lemma `even_iff` / 引理 `even_iff`

English:
lemma even_iff
  statement: Even n ↔ n % 2 = 0 where
  proof: fun ⟨m, hm⟩ => by simp [← Int.two_mul, hm]
  mpr h := ⟨n / 2, by grind⟩

中文:
引理 even_iff
  结论: Even n ↔ n % 2 = 0 where
  证明: fun ⟨m, hm⟩ => by simp [← Int.two_mul, hm]
  mpr h := ⟨n / 2, by grind⟩

Depends on / 依赖: Int.two_mul, two_mul
-/
lemma even_iff : Even n ↔ n % 2 = 0 where
  mp := fun ⟨m, hm⟩ => by simp [← Int.two_mul, hm]
  mpr h := ⟨n / 2, by grind⟩

/--
lemma `not_even_iff` / 引理 `not_even_iff`

English:
lemma not_even_iff
  statement: ¬Even n ↔ n % 2 = 1
  proof: by grind

中文:
引理 not_even_iff
  结论: ¬Even n ↔ n % 2 = 1
  证明: by grind
-/
lemma not_even_iff : ¬Even n ↔ n % 2 = 1 := by grind

/--
lemma `two_dvd_ne_zero` / 引理 `two_dvd_ne_zero`

English:
lemma two_dvd_ne_zero
  statement: ¬2 ∣ n ↔ n % 2 = 1
  proof: by grind

中文:
引理 two_dvd_ne_zero
  结论: ¬2 ∣ n ↔ n % 2 = 1
  证明: by grind
-/
@[simp] lemma two_dvd_ne_zero : ¬2 ∣ n ↔ n % 2 = 1 := by grind

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DecidablePred (Even : Int -> Prop)
  body: fun _ => decidable_of_iff _ even_iff.symm

中文:
实例 :
  签名: DecidablePred (Even : 整数 -> 命题)
  定义体: fun _ => decidable_of_iff _ even_iff.symm

Depends on / 依赖: decidable_of_iff, even_iff, even_iff.symm
-/
instance : DecidablePred (Even : Int -> Prop) := fun _ => decidable_of_iff _ even_iff.symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DecidablePred (IsSquare : Int -> Prop)
  body: fun m => decidable_of_iff' (sqrt m * sqrt m = m) by
    simp_rw [← exists_mul_self m, IsSquare, eq_comm]

中文:
实例 :
  签名: DecidablePred (IsSquare : 整数 -> 命题)
  定义体: fun m => decidable_of_iff' (sqrt m * sqrt m = m) by
    simp_rw [← exists_mul_self m, IsSquare, eq_comm]

Depends on / 依赖: IsSquare, decidable_of_iff, eq_comm, exists_mul_self, simp_rw
-/
instance : DecidablePred (IsSquare : Int -> Prop) :=
fun m => decidable_of_iff' (sqrt m * sqrt m = m) by
    simp_rw [← exists_mul_self m, IsSquare, eq_comm]

/--
lemma `not_even_one` / 引理 `not_even_one`

English:
lemma not_even_one
  statement: ¬Even (1 : Int)
  proof: by simp [even_iff]

中文:
引理 not_even_one
  结论: ¬Even (1 : 整数)
  证明: by simp [even_iff]
-/
@[simp] lemma not_even_one : ¬Even (1 : Int) := by simp [even_iff]

/--
lemma `even_add` / 引理 `even_add`

English:
lemma even_add
  statement: Even (m + n) ↔ (Even m ↔ Even n)
  proof: by grind

中文:
引理 even_add
  结论: Even (m + n) ↔ (Even m ↔ Even n)
  证明: by grind
-/
@[parity_simps] lemma even_add : Even (m + n) ↔ (Even m ↔ Even n) := by grind

/--
lemma `two_not_dvd_two_mul_add_one` / 引理 `two_not_dvd_two_mul_add_one`

English:
lemma two_not_dvd_two_mul_add_one
  given: (n : Int)
  statement: ¬2 ∣ 2 * n + 1
  proof: by grind

@[parity_simps]

中文:
引理 two_not_dvd_two_mul_add_one
  条件: (n : 整数)
  结论: ¬2 ∣ 2 * n + 1
  证明: by grind

@[parity_simps]
-/
lemma two_not_dvd_two_mul_add_one (n : Int) : ¬2 ∣ 2 * n + 1 := by grind

@[parity_simps]
/--
lemma `even_sub` / 引理 `even_sub`

English:
lemma even_sub
  statement: Even (m - n) ↔ (Even m ↔ Even n)
  proof: by grind

中文:
引理 even_sub
  结论: Even (m - n) ↔ (Even m ↔ Even n)
  证明: by grind
-/
lemma even_sub : Even (m - n) ↔ (Even m ↔ Even n) := by grind

/--
lemma `even_add_one` / 引理 `even_add_one`

English:
lemma even_add_one
  statement: Even (n + 1) ↔ ¬Even n
  proof: by grind

中文:
引理 even_add_one
  结论: Even (n + 1) ↔ ¬Even n
  证明: by grind
-/
@[parity_simps] lemma even_add_one : Even (n + 1) ↔ ¬Even n := by grind

/--
lemma `even_sub_one` / 引理 `even_sub_one`

English:
lemma even_sub_one
  statement: Even (n - 1) ↔ ¬Even n
  proof: by grind

中文:
引理 even_sub_one
  结论: Even (n - 1) ↔ ¬Even n
  证明: by grind
-/
@[parity_simps] lemma even_sub_one : Even (n - 1) ↔ ¬Even n := by grind

/--
lemma `even_mul` / 引理 `even_mul`

English:
lemma even_mul
  statement: Even (m * n) ↔ Even m ∨ Even n
  proof: by
  rcases emod_two_eq_zero_or_one m with h₁ | h₁ <;>
  rcases emod_two_eq_zero_or_one n with h₂ | h₂ <;>
  simp [even_iff, h₁, h₂, Int.mul_emod]

中文:
引理 even_mul
  结论: Even (m * n) ↔ Even m ∨ Even n
  证明: by
  rcases emod_two_eq_zero_or_one m with h₁ | h₁ <;>
  rcases emod_two_eq_zero_or_one n with h₂ | h₂ <;>
  simp [even_iff, h₁, h₂, Int.mul_emod]
-/
@[parity_simps, grind =] lemma even_mul : Even (m * n) ↔ Even m ∨ Even n := by
  rcases emod_two_eq_zero_or_one m with h₁ | h₁ <;>
  rcases emod_two_eq_zero_or_one n with h₂ | h₂ <;>
  simp [even_iff, h₁, h₂, Int.mul_emod]

/--
lemma `even_pow` / 引理 `even_pow`

English:
lemma even_pow
  given: {n : Nat}
  statement: Even (m ^ n) ↔ Even m ∧ n != 0
  proof: by
  induction n with grind

中文:
引理 even_pow
  条件: {n : 自然数}
  结论: Even (m ^ n) ↔ Even m ∧ n != 0
  证明: by
  induction n with grind
-/
@[parity_simps, grind =] lemma even_pow {n : Nat} : Even (m ^ n) ↔ Even m ∧ n != 0 := by
  induction n with grind

/--
lemma `even_pow'` / 引理 `even_pow'`

English:
lemma even_pow'
  given: {n : Nat} (h : n != 0)
  statement: Even (m ^ n) ↔ Even m
  proof: by grind

@[simp, norm_cast, grind =]

中文:
引理 even_pow'
  条件: {n : 自然数} (h : n != 0)
  结论: Even (m ^ n) ↔ Even m
  证明: by grind

@[simp, norm_cast, grind =]
-/
lemma even_pow' {n : Nat} (h : n != 0) : Even (m ^ n) ↔ Even m := by grind

@[simp, norm_cast, grind =]
/--
lemma `even_coe_nat` / 引理 `even_coe_nat`

English:
lemma even_coe_nat
  given: (n : Nat)
  statement: Even (n : Int) ↔ Even n
  proof: by
  rw_mod_cast [even_iff, Nat.even_iff]

中文:
引理 even_coe_nat
  条件: (n : 自然数)
  结论: Even (n : 整数) ↔ Even n
  证明: by
  rw_mod_cast [even_iff, Nat.even_iff]

Depends on / 依赖: Nat.even_iff, even_iff, rw_mod_cast
-/
lemma even_coe_nat (n : Nat) : Even (n : Int) ↔ Even n := by
  rw_mod_cast [even_iff, Nat.even_iff]

/--
lemma `two_mul_ediv_two_of_even` / 引理 `two_mul_ediv_two_of_even`

English:
lemma two_mul_ediv_two_of_even
  statement: Even n -> 2 * (n / 2) = n
  proof: by grind

中文:
引理 two_mul_ediv_two_of_even
  结论: Even n -> 2 * (n / 2) = n
  证明: by grind
-/
lemma two_mul_ediv_two_of_even : Even n -> 2 * (n / 2) = n := by grind

/--
lemma `ediv_two_mul_two_of_even` / 引理 `ediv_two_mul_two_of_even`

English:
lemma ediv_two_mul_two_of_even
  statement: Even n -> n / 2 * 2 = n
  proof: by grind

中文:
引理 ediv_two_mul_two_of_even
  结论: Even n -> n / 2 * 2 = n
  证明: by grind
-/
lemma ediv_two_mul_two_of_even : Even n -> n / 2 * 2 = n := by grind

-- Here are examples of how `parity_simps` can be used with `Int`.
example (m n : Int) (h : Even m) : ¬Even (n + 3) ↔ Even (m ^ 2 + m + n) := by
  simp +decide [*, parity_simps]

example : ¬Even (25394535 : Int) := by decide

@[simp]
/--
theorem `isSquare_sign_iff` / 定理 `isSquare_sign_iff`

English:
theorem isSquare_sign_iff
  given: {z : Int}
  statement: IsSquare z.sign ↔ 0 <= z
  proof: by
  induction z using Int.induction_on with
  | zero => simpa using ⟨0, by simp⟩
  | succ => norm_cast; simp
  | pred =>
    rw [sign_eq_neg_one_of_neg (by lia)]; rw [← neg_add']; rw [Int.neg_nonneg]
    norm_cast
    simp only [reduceNeg, le_zero_eq, Nat.add_eq_zero_iff, succ_ne_self, and_false, iff_false]
    rintro ⟨a | a, ⟨⟩⟩

中文:
定理 isSquare_sign_iff
  条件: {z : 整数}
  结论: IsSquare z.sign ↔ 0 <= z
  证明: by
  induction z using Int.induction_on with
  | zero => simpa using ⟨0, by simp⟩
  | succ => norm_cast; simp
  | pred =>
    rw [sign_eq_neg_one_of_neg (by lia)]; rw [← neg_add']; rw [Int.neg_nonneg]
    norm_cast
    simp only [reduceNeg, le_zero_eq, Nat.add_eq_zero_iff, succ_ne_self, and_false, iff_false]
    rintro ⟨a | a, ⟨⟩⟩

Depends on / 依赖: Int.induction_on, Int.neg_nonneg, Nat.add_eq_zero_iff, add_eq_zero_iff, and_false, iff_false, induction_on, le_zero_eq, neg_add, neg_nonneg, reduceNeg, sign_eq_neg_one_of_neg, succ_ne_self
-/
theorem isSquare_sign_iff {z : Int} : IsSquare z.sign ↔ 0 <= z := by
  induction z using Int.induction_on with
  | zero => simpa using ⟨0, by simp⟩
  | succ => norm_cast; simp
  | pred =>
    rw [sign_eq_neg_one_of_neg (by lia)]; rw [← neg_add']; rw [Int.neg_nonneg]
    norm_cast
    simp only [reduceNeg, le_zero_eq, Nat.add_eq_zero_iff, succ_ne_self, and_false, iff_false]
    rintro ⟨a | a, ⟨⟩⟩

end Int
