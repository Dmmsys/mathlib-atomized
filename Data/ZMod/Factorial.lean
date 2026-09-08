/-
Copyright (c) 2023 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/
module

public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Data.ZMod.Basic

/-!
# Facts about factorials in ZMod

We collect facts about factorials in context of modular arithmetic.

## Main statements

* `ZMod.cast_descFactorial`: For natural numbers `n` and `p`, where `n` is less than or equal to `p`
  the descending factorial of `(p - 1)` taken `n` times modulo `p` equals `(-1) ^ n * n!`.

## See also

For the prime case and involving `factorial` rather than `descFactorial`, see Wilson's theorem:
* `Nat.prime_iff_fac_equiv_neg_one`

-/

public section

assert_not_exists TwoSidedIdeal

open Finset Nat

namespace ZMod

/-
**ZMod.cast_descFactorial** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：cast_descFactorial {n p : Nat} (h : n <= p) : (descFactorial (p - 1) n : Z
Mod p) = (-1) ^ n * n !
参数：h : n <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.descFactorial_eq_prod_range`：∀ (n k : ℕ), n.descFactorial k = ∏ i ∈ 
Finset.range k, (n - i)
· 使用定理 `Nat.factorial_eq_prod_range_add_one`：∀ (n : ℕ), n.factorial = ∏ i ∈ Fins
et.range n, (i + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Nat.cast_prod`：cast_prod [CommSemiring R] (f : ι -> Nat) (s : Finset ι) 
: (↑(∏ i in s, f i) : R) = ∏ i in s, (f i : R)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
· 使用定理 `Finset.pow_card_mul_prod`：pow_card_mul_prod {b : M} : b ^ #s * ∏ a in s,
 f a = ∏ a in s, b * f a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `tsub_add_eq_tsub_tsub_swap`：tsub_add_eq_tsub_tsub_swap (a b c : α) : a -
 (b + c) = a - c - b
· 使用定理 `Nat.cast_sub`：cast_sub {m n} (h : m <= n) : ((n - m : Nat) : R) = n - m
· 使用定理 `Nat.le_trans`：∀ {n m k : ℕ}, n ≤ m → m ≤ k → n ≤ k
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.add_one_le_iff`：∀ {n m : ℕ}, n + 1 ≤ m ↔ n < m
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.mem_range`：∀ {m n : ℕ}, m ∈ List.range n ↔ m < n
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `Nat.cast_succ`：cast_succ (n : Nat) : ((succ n : Nat) : R) = n + 1
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem cast_descFactorial {n p : ℕ} (h : n ≤ p) :
    (descFactorial (p - 1) n : ZMod p) = (-1) ^ n * n ! := by
  rw [descFactorial_eq_prod_range, factorial_eq_prod_range_add_one]
  simp only [cast_prod]
  nth_rw 2 [← card_range n]
  rw [pow_card_mul_prod]
  refine prod_congr rfl ?_
  intro x hx
  rw [← tsub_add_eq_tsub_tsub_swap,
    Nat.cast_sub <| Nat.le_trans (Nat.add_one_le_iff.mpr (List.mem_range.mp hx)) h,
    CharP.cast_eq_zero, zero_sub, cast_succ, neg_add_rev, mul_add, neg_mul, one_mul,
    mul_one, add_comm]

end ZMod

