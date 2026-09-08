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
/-
**Nat.nth_prime_zero_eq_two** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：nth_prime_zero_eq_two : nth Prime 0 = 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.nth_count`：nth_count {n : Nat} (hpn : p n) : nth p (count p n) = n
· 使用定理 `Nat.prime_two`：prime_two : Prime 2
-/
theorem nth_prime_zero_eq_two : nth Prime 0 = 2 := nth_count prime_two

@[simp]
/-
**Nat.nth_prime_one_eq_three** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：nth_prime_one_eq_three : nth Nat.Prime 1 = 3
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.nth_count`：nth_count {n : Nat} (hpn : p n) : nth p (count p n) = n
· 使用定理 `Nat.prime_three`：prime_three : Prime 3
-/
theorem nth_prime_one_eq_three : nth Nat.Prime 1 = 3 := nth_count prime_three

@[simp]
/-
**Nat.nth_prime_two_eq_five** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：nth_prime_two_eq_five : nth Nat.Prime 2 = 5
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.nth_count`：nth_count {n : Nat} (hpn : p n) : nth p (count p n) = n
· 使用定理 `Nat.prime_five`：prime_five : Prime 5
-/
theorem nth_prime_two_eq_five : nth Nat.Prime 2 = 5 := nth_count prime_five

@[simp]
/-
**Nat.nth_prime_three_eq_seven** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：nth_prime_three_eq_seven : nth Nat.Prime 3 = 7
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.nth_count`：nth_count {n : Nat} (hpn : p n) : nth p (count p n) = n
· 使用定理 `Nat.prime_seven`：prime_seven : Prime 7
-/
theorem nth_prime_three_eq_seven : nth Nat.Prime 3 = 7 := nth_count prime_seven

@[simp]
/-
**Nat.nth_prime_four_eq_eleven** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：nth_prime_four_eq_eleven : nth Nat.Prime 4 = 11
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.nth_count`：nth_count {n : Nat} (hpn : p n) : nth p (count p n) = n
· 使用定理 `Nat.prime_eleven`：prime_eleven : Prime 11
-/
theorem nth_prime_four_eq_eleven : nth Nat.Prime 4 = 11 := nth_count prime_eleven

end Nat

