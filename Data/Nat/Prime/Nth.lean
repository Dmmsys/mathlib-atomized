/-
Copyright (c) 2024 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Nat.Nth

/-!
# The Nth primes
-/

public section

namespace Nat

@[simp]
/--
theorem `nth_prime_zero_eq_two` / 定理 `nth_prime_zero_eq_two`

English:
theorem nth_prime_zero_eq_two
  statement: nth Prime 0 = 2
  proof: nth_count prime_two

@[simp]

中文:
定理 nth_prime_zero_eq_two
  结论: nth Prime 0 = 2
  证明: nth_count prime_two

@[simp]

Depends on / 依赖: nth_count, prime_two
-/
theorem nth_prime_zero_eq_two : nth Prime 0 = 2 := nth_count prime_two

@[simp]
/--
theorem `nth_prime_one_eq_three` / 定理 `nth_prime_one_eq_three`

English:
theorem nth_prime_one_eq_three
  statement: nth Nat.Prime 1 = 3
  proof: nth_count prime_three

@[simp]

中文:
定理 nth_prime_one_eq_three
  结论: nth 自然数.Prime 1 = 3
  证明: nth_count prime_three

@[simp]

Depends on / 依赖: nth_count, prime_three
-/
theorem nth_prime_one_eq_three : nth Nat.Prime 1 = 3 := nth_count prime_three

@[simp]
/--
theorem `nth_prime_two_eq_five` / 定理 `nth_prime_two_eq_five`

English:
theorem nth_prime_two_eq_five
  statement: nth Nat.Prime 2 = 5
  proof: nth_count prime_five

@[simp]

中文:
定理 nth_prime_two_eq_five
  结论: nth 自然数.Prime 2 = 5
  证明: nth_count prime_five

@[simp]

Depends on / 依赖: nth_count, prime_five
-/
theorem nth_prime_two_eq_five : nth Nat.Prime 2 = 5 := nth_count prime_five

@[simp]
/--
theorem `nth_prime_three_eq_seven` / 定理 `nth_prime_three_eq_seven`

English:
theorem nth_prime_three_eq_seven
  statement: nth Nat.Prime 3 = 7
  proof: nth_count prime_seven

@[simp]

中文:
定理 nth_prime_three_eq_seven
  结论: nth 自然数.Prime 3 = 7
  证明: nth_count prime_seven

@[simp]

Depends on / 依赖: nth_count, prime_seven
-/
theorem nth_prime_three_eq_seven : nth Nat.Prime 3 = 7 := nth_count prime_seven

@[simp]
/--
theorem `nth_prime_four_eq_eleven` / 定理 `nth_prime_four_eq_eleven`

English:
theorem nth_prime_four_eq_eleven
  statement: nth Nat.Prime 4 = 11
  proof: nth_count prime_eleven

中文:
定理 nth_prime_four_eq_eleven
  结论: nth 自然数.Prime 4 = 11
  证明: nth_count prime_eleven

Depends on / 依赖: nth_count, prime_eleven
-/
theorem nth_prime_four_eq_eleven : nth Nat.Prime 4 = 11 := nth_count prime_eleven

end Nat
