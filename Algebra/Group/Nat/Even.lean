/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module

public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Tactic.Attr.Register

/-!
# `IsSquare` and `Even` for natural numbers
-/

public section

assert_not_exists MonoidWithZero DenselyOrdered

namespace Nat

/-! #### Parity -/

variable {m n : Nat}

@[grind =]
/--
lemma `even_iff` / 引理 `even_iff`

English:
lemma even_iff
  statement: Even n ↔ n % 2 = 0 where
  proof: fun ⟨m, hm⟩ => by simp [← Nat.two_mul, hm]
  mpr h := ⟨n / 2, by grind⟩

中文:
引理 even_iff
  结论: Even n ↔ n % 2 = 0 where
  证明: fun ⟨m, hm⟩ => by simp [← Nat.two_mul, hm]
  mpr h := ⟨n / 2, by grind⟩

Depends on / 依赖: Nat.two_mul, two_mul
-/
lemma even_iff : Even n ↔ n % 2 = 0 where
  mp := fun ⟨m, hm⟩ => by simp [← Nat.two_mul, hm]
  mpr h := ⟨n / 2, by grind⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DecidablePred (Even : Nat -> Prop)
  body: fun _ => decidable_of_iff _ even_iff.symm

中文:
实例 :
  签名: DecidablePred (Even : 自然数 -> 命题)
  定义体: fun _ => decidable_of_iff _ even_iff.symm

Depends on / 依赖: decidable_of_iff, even_iff, even_iff.symm
-/
instance : DecidablePred (Even : Nat -> Prop) := fun _ => decidable_of_iff _ even_iff.symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DecidablePred (IsSquare : Nat -> Prop)
  body: fun m => decidable_of_iff' (Nat.sqrt m * Nat.sqrt m = m) by
    simp_rw [← Nat.exists_mul_self m, IsSquare, eq_comm]

中文:
实例 :
  签名: DecidablePred (IsSquare : 自然数 -> 命题)
  定义体: fun m => decidable_of_iff' (Nat.sqrt m * Nat.sqrt m = m) by
    simp_rw [← Nat.exists_mul_self m, IsSquare, eq_comm]

Depends on / 依赖: IsSquare, Nat.exists_mul_self, Nat.sqrt, decidable_of_iff, eq_comm, exists_mul_self, simp_rw
-/
instance : DecidablePred (IsSquare : Nat -> Prop) :=
fun m => decidable_of_iff' (Nat.sqrt m * Nat.sqrt m = m) by
    simp_rw [← Nat.exists_mul_self m, IsSquare, eq_comm]

/--
lemma `not_even_iff` / 引理 `not_even_iff`

English:
lemma not_even_iff
  statement: ¬ Even n ↔ n % 2 = 1
  proof: by grind

中文:
引理 not_even_iff
  结论: ¬ Even n ↔ n % 2 = 1
  证明: by grind
-/
lemma not_even_iff : ¬ Even n ↔ n % 2 = 1 := by grind

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
lemma `not_even_one` / 引理 `not_even_one`

English:
lemma not_even_one
  statement: ¬Even 1
  proof: by grind

中文:
引理 not_even_one
  结论: ¬Even 1
  证明: by grind
-/
@[simp] lemma not_even_one : ¬Even 1 := by grind

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
@[parity_simps, grind =] lemma even_add : Even (m + n) ↔ (Even m ↔ Even n) := by grind

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
lemma `succ_mod_two_eq_zero_iff` / 引理 `succ_mod_two_eq_zero_iff`

English:
lemma succ_mod_two_eq_zero_iff
  statement: (m + 1) % 2 = 0 ↔ m % 2 = 1
  proof: by lia

中文:
引理 succ_mod_two_eq_zero_iff
  结论: (m + 1) % 2 = 0 ↔ m % 2 = 1
  证明: by lia
-/
lemma succ_mod_two_eq_zero_iff : (m + 1) % 2 = 0 ↔ m % 2 = 1 := by lia

/--
lemma `succ_mod_two_eq_one_iff` / 引理 `succ_mod_two_eq_one_iff`

English:
lemma succ_mod_two_eq_one_iff
  statement: (m + 1) % 2 = 1 ↔ m % 2 = 0
  proof: by lia

中文:
引理 succ_mod_two_eq_one_iff
  结论: (m + 1) % 2 = 1 ↔ m % 2 = 0
  证明: by lia
-/
lemma succ_mod_two_eq_one_iff : (m + 1) % 2 = 1 ↔ m % 2 = 0 := by lia

/--
lemma `two_not_dvd_two_mul_add_one` / 引理 `two_not_dvd_two_mul_add_one`

English:
lemma two_not_dvd_two_mul_add_one
  given: (n : Nat)
  statement: ¬2 ∣ 2 * n + 1
  proof: by lia

中文:
引理 two_not_dvd_two_mul_add_one
  条件: (n : 自然数)
  结论: ¬2 ∣ 2 * n + 1
  证明: by lia
-/
lemma two_not_dvd_two_mul_add_one (n : Nat) : ¬2 ∣ 2 * n + 1 := by lia

/--
lemma `two_not_dvd_two_mul_sub_one` / 引理 `two_not_dvd_two_mul_sub_one`

English:
lemma two_not_dvd_two_mul_sub_one
  given: {n}
  statement: 0 < n -> ¬2 ∣ 2 * n - 1
  proof: by lia

中文:
引理 two_not_dvd_two_mul_sub_one
  条件: {n}
  结论: 0 < n -> ¬2 ∣ 2 * n - 1
  证明: by lia
-/
lemma two_not_dvd_two_mul_sub_one {n} : 0 < n -> ¬2 ∣ 2 * n - 1 := by lia

/--
lemma `even_sub` / 引理 `even_sub`

English:
lemma even_sub
  given: (h : n <= m)
  statement: Even (m - n) ↔ (Even m ↔ Even n)
  proof: by grind

中文:
引理 even_sub
  条件: (h : n <= m)
  结论: Even (m - n) ↔ (Even m ↔ Even n)
  证明: by grind
-/
@[parity_simps] lemma even_sub (h : n <= m) : Even (m - n) ↔ (Even m ↔ Even n) := by grind

/--
lemma `even_mul` / 引理 `even_mul`

English:
lemma even_mul
  statement: Even (m * n) ↔ Even m ∨ Even n
  proof: by
  rcases mod_two_eq_zero_or_one m with h₁ | h₁ <;> rcases mod_two_eq_zero_or_one n with h₂ | h₂ <;>
    simp [even_iff, h₁, h₂, Nat.mul_mod]

中文:
引理 even_mul
  结论: Even (m * n) ↔ Even m ∨ Even n
  证明: by
  rcases mod_two_eq_zero_or_one m with h₁ | h₁ <;> rcases mod_two_eq_zero_or_one n with h₂ | h₂ <;>
    simp [even_iff, h₁, h₂, Nat.mul_mod]
-/
@[parity_simps, grind =] lemma even_mul : Even (m * n) ↔ Even m ∨ Even n := by
  rcases mod_two_eq_zero_or_one m with h₁ | h₁ <;> rcases mod_two_eq_zero_or_one n with h₂ | h₂ <;>
    simp [even_iff, h₁, h₂, Nat.mul_mod]

/--
lemma `even_pow` / 引理 `even_pow`

English:
lemma even_pow
  statement: Even (m ^ n) ↔ Even m ∧ n != 0
  proof: by
  induction n with grind

中文:
引理 even_pow
  结论: Even (m ^ n) ↔ Even m ∧ n != 0
  证明: by
  induction n with grind
-/
@[parity_simps, grind =] lemma even_pow : Even (m ^ n) ↔ Even m ∧ n != 0 := by
  induction n with grind

/--
lemma `even_pow'` / 引理 `even_pow'`

English:
lemma even_pow'
  given: (h : n != 0)
  statement: Even (m ^ n) ↔ Even m
  proof: by grind

中文:
引理 even_pow'
  条件: (h : n != 0)
  结论: Even (m ^ n) ↔ Even m
  证明: by grind
-/
lemma even_pow' (h : n != 0) : Even (m ^ n) ↔ Even m := by grind

/--
lemma `even_mul_succ_self` / 引理 `even_mul_succ_self`

English:
lemma even_mul_succ_self
  given: (n : Nat)
  statement: Even (n * (n + 1))
  proof: by grind

中文:
引理 even_mul_succ_self
  条件: (n : 自然数)
  结论: Even (n * (n + 1))
  证明: by grind
-/
lemma even_mul_succ_self (n : Nat) : Even (n * (n + 1)) := by grind

/--
lemma `even_mul_pred_self` / 引理 `even_mul_pred_self`

English:
lemma even_mul_pred_self
  given: (n : Nat)
  statement: Even (n * (n - 1))
  proof: by grind

中文:
引理 even_mul_pred_self
  条件: (n : 自然数)
  结论: Even (n * (n - 1))
  证明: by grind
-/
lemma even_mul_pred_self (n : Nat) : Even (n * (n - 1)) := by grind

/--
lemma `two_mul_div_two_of_even` / 引理 `two_mul_div_two_of_even`

English:
lemma two_mul_div_two_of_even
  statement: Even n -> 2 * (n / 2) = n
  proof: fun h =>
  Nat.mul_div_cancel_left' ((even_iff_exists_two_nsmul _).1 h)

中文:
引理 two_mul_div_two_of_even
  结论: Even n -> 2 * (n / 2) = n
  证明: fun h =>
  Nat.mul_div_cancel_left' ((even_iff_exists_two_nsmul _).1 h)
-/
lemma two_mul_div_two_of_even : Even n -> 2 * (n / 2) = n := fun h =>
  Nat.mul_div_cancel_left' ((even_iff_exists_two_nsmul _).1 h)

/--
lemma `div_two_mul_two_of_even` / 引理 `div_two_mul_two_of_even`

English:
lemma div_two_mul_two_of_even
  statement: Even n -> n / 2 * 2 = n
  proof: fun h => Nat.div_mul_cancel ((even_iff_exists_two_nsmul _).1 h)

中文:
引理 div_two_mul_two_of_even
  结论: Even n -> n / 2 * 2 = n
  证明: fun h => Nat.div_mul_cancel ((even_iff_exists_two_nsmul _).1 h)

Depends on / 依赖: Nat.div_mul_cancel, div_mul_cancel, even_iff_exists_two_nsmul
-/
lemma div_two_mul_two_of_even : Even n -> n / 2 * 2 = n :=
  fun h => Nat.div_mul_cancel ((even_iff_exists_two_nsmul _).1 h)

/--
theorem `one_lt_of_ne_zero_of_even` / 定理 `one_lt_of_ne_zero_of_even`

English:
theorem one_lt_of_ne_zero_of_even
  given: (h0 : n != 0) (hn : Even n)
  statement: 1 < n
  proof: by grind

中文:
定理 one_lt_of_ne_zero_of_even
  条件: (h0 : n != 0) (hn : Even n)
  结论: 1 < n
  证明: by grind
-/
theorem one_lt_of_ne_zero_of_even (h0 : n != 0) (hn : Even n) : 1 < n := by grind

/--
theorem `add_one_lt_of_even` / 定理 `add_one_lt_of_even`

English:
theorem add_one_lt_of_even
  given: (hn : Even n) (hm : Even m) (hnm : n < m)
  proof: by grind

中文:
定理 add_one_lt_of_even
  条件: (hn : Even n) (hm : Even m) (hnm : n < m)
  证明: by grind
-/
theorem add_one_lt_of_even (hn : Even n) (hm : Even m) (hnm : n < m) :
    n + 1 < m := by grind

-- Here are examples of how `parity_simps` can be used with `Nat`.
example (m n : Nat) (h : Even m) : ¬Even (n + 3) ↔ Even (m ^ 2 + m + n) := by simp [*, parity_simps]

example : ¬Even 25394535 := by decide

end Nat
