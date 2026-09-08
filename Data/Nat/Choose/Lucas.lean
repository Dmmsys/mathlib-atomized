/-
Copyright (c) 2023 Gareth Ma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gareth Ma
-/
module

public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Polynomial.Basic
meta import Mathlib.Tactic.GRewrite

/-!
# Lucas's theorem

This file contains a proof of [Lucas's theorem](https://en.wikipedia.org/wiki/Lucas's_theorem) about
binomial coefficients, which says that for primes `p`, `n` choose `k` is congruent to product of
`n_i` choose `k_i` modulo `p`, where `n_i` and `k_i` are the base-`p` digits of `n` and `k`,
respectively.

## Main statements

* `lucas_theorem`: the binomial coefficient `n choose k` is congruent to the product of `n_i choose
  k_i` modulo `p`, where `n_i` and `k_i` are the base-`p` digits of `n` and `k`, respectively.
-/

public section

open Finset hiding choose

open Nat Polynomial

namespace Choose

variable {n k a b p : ℕ} [Fact p.Prime]

/-- For primes `p`, `choose n k` is congruent to `choose (n % p) (k % p) * choose (n / p) (k / p)`
modulo `p`. Also see `choose_modEq_choose_mod_mul_choose_div_nat` for the version with `MOD`. -/
/-
**Choose.choose_modEq_choose_mod_mul_choose_div** 是 Mathlib 中的一个定理，位于命名空间 `Choos
e`。
形式化陈述：choose_modEq_choose_mod_mul_choose_div : choose n k ≡ choose (n % p) (k % 
p) * choose (n / p) (k / p) [ZMOD p]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用引理 `add_pow_eq_mul_pow_add_pow_div_char`：add_pow_eq_mul_pow_add_pow_div_char
 : (x + y) ^ n = (x + y) ^ (n % p) * (x ^ p + y ^ p) ^ (n / p)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.coeff_X_add_one_pow`：coeff_X_add_one_pow (R : Type*) [Semirin
g R] (n k : Nat) : ((X + 1) ^ n).coeff k = (n.choose k : R)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用定理 `Polynomial.map_pow`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p :
 Polynomial R} [inst_1 : Semiring S] (f : R →+* S) (n : ℕ),   Polynomial.map f (
p ^ n) =…
· 使用定理 `Polynomial.map_add`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p + q)
 = Polyn…
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `Polynomial.map_one`：∀ {R : Type u} {S : Type v} [inst : Semiring R] [ins
t_1 : Semiring S] (f : R →+* S), Polynomial.map f 1 = 1
· 使用定理 `add_pow`：add_pow [CommSemiring R] (x y : R) (n : Nat) : (x + y) ^ n = ∑ 
m in range (n + 1), x ^ m * y ^ (n - m) * n.choose m
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `Finset.sum_mul_sum`：sum_mul_sum (s : Finset ι) (t : Finset κ) (f : ι -> 
R) (g : κ -> R) : (∑ i in s, f i) * ∑ j in t, g j = ∑ i in s, ∑ j in t, f i * g 
j
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_right_comm`：mul_right_comm (a b c : G) : a * b * c = a * c * b
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `Fin.pos'`：∀ {n : ℕ} [Nonempty (Fin n)], 0 < n
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
（共 71 条，此处仅展示前 30 条）

--- 原说明 ---
For primes `p`, `choose n k` is congruent to `choose (n % p) (k % p) * choose (n
 / p) (k / p)`
modulo `p`. Also see `choose_modEq_choose_mod_mul_choose_div_nat` for the versio
n with `MOD`.
-/
theorem choose_modEq_choose_mod_mul_choose_div :
    choose n k ≡ choose (n % p) (k % p) * choose (n / p) (k / p) [ZMOD p] := by
  have decompose : ((X : (ZMod p)[X]) + 1) ^ n = (X + 1) ^ (n % p) * (X ^ p + 1) ^ (n / p) := by
    simpa using add_pow_eq_mul_pow_add_pow_div_char (X : (ZMod p)[X]) 1 p _
  simp only [← ZMod.intCast_eq_intCast_iff,
    ← coeff_X_add_one_pow _ n k, ← eq_intCast (Int.castRingHom (ZMod p)), ← coeff_map,
    Polynomial.map_pow, Polynomial.map_add, Polynomial.map_one, map_X, decompose]
  simp only [add_pow, one_pow, mul_one, ← pow_mul, sum_mul_sum]
  conv_lhs =>
    enter [1, 2, k, 2, k']
    rw [← mul_assoc, mul_right_comm _ _ (X ^ (p * k')), ← pow_add, mul_assoc, ← cast_mul]
  have h_iff : ∀ x ∈ range (n % p + 1) ×ˢ range (n / p + 1),
      k = x.1 + p * x.2 ↔ (k % p, k / p) = x := by
    intro ⟨x₁, x₂⟩ hx
    rw [Prod.mk.injEq]
    constructor <;> intro h
    · simp only [mem_product, mem_range] at hx
      have h' : x₁ < p := lt_of_lt_of_le hx.left <| mod_lt _ Fin.pos'
      rw [h, add_mul_mod_self_left, add_mul_div_left _ _ Fin.pos', eq_comm (b := x₂)]
      exact ⟨mod_eq_of_lt h', right_eq_add.mpr (div_eq_of_lt h')⟩
    · rw [← h.left, ← h.right, mod_add_div]
  simp only [finsetSum_coeff, coeff_mul_natCast, coeff_X_pow, ite_mul, zero_mul, ← cast_mul]
  rw [← sum_product', sum_congr rfl (fun a ha ↦ if_congr (h_iff a ha) rfl rfl), sum_ite_eq]
  split_ifs with h
  · simp
  · rw [mem_product, mem_range, mem_range, not_and_or, Nat.lt_succ_iff, not_le, not_lt] at h
    cases h <;> simp [choose_eq_zero_of_lt (by tauto)]

/-- For primes `p`, `choose n k` is congruent to `choose (n % p) (k % p) * choose (n / p) (k / p)`
modulo `p`. Also see `choose_modEq_choose_mod_mul_choose_div` for the version with `ZMOD`. -/
/-
**Choose.choose_modEq_choose_mod_mul_choose_div_nat** 是 Mathlib 中的一个定理，位于命名空间 `C
hoose`。
形式化陈述：choose_modEq_choose_mod_mul_choose_div_nat : choose n k ≡ choose (n % p) (
k % p) * choose (n / p) (k / p) [MOD p]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.natCast_modEq_iff`：natCast_modEq_iff {a b n : Nat} : a ≡ b [ZMOD n] 
↔ a ≡ b [MOD n]
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Choose.choose_modEq_choose_mod_mul_choose_div`：choose_modEq_choose_mod_m
ul_choose_div : choose n k ≡ choose (n % p) (k % p) * choose (n / p) (k / p) [ZM
OD p]

--- 原说明 ---
For primes `p`, `choose n k` is congruent to `choose (n % p) (k % p) * choose (n
 / p) (k / p)`
modulo `p`. Also see `choose_modEq_choose_mod_mul_choose_div` for the version wi
th `ZMOD`.
-/
theorem choose_modEq_choose_mod_mul_choose_div_nat :
    choose n k ≡ choose (n % p) (k % p) * choose (n / p) (k / p) [MOD p] := by
  rw [← Int.natCast_modEq_iff]
  exact_mod_cast choose_modEq_choose_mod_mul_choose_div

/-- For primes `p`, `choose n k` is congruent to the product of `choose (⌊n / p ^ i⌋ % p)
(⌊k / p ^ i⌋ % p)` over i < a, multiplied by `choose (⌊n / p ^ a⌋) (⌊k / p ^ a⌋)`, modulo `p`. -/
/-
**Choose.choose_modEq_choose_mul_prod_range_choose** 是 Mathlib 中的一个定理，位于命名空间 `Ch
oose`。
形式化陈述：choose_modEq_choose_mul_prod_range_choose (a : Nat) : choose n k ≡ choose 
(n / p ^ a) (k / p ^ a) * ∏ i in range a, choose (n / p ^ i % p) (k / p ^ i % p)
 [ZMOD p]
参数：a : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For primes `p`, `choose n k` is congruent to the product of `choose (⌊n / p ^ i⌋
 % p)
(⌊k / p ^ i⌋ % p)` over i < a, multiplied by `choose (⌊n / p ^ a⌋) (⌊k / p ^ a⌋)
`, modulo `p`.
-/
theorem choose_modEq_choose_mul_prod_range_choose (a : ℕ) :
    choose n k ≡ choose (n / p ^ a) (k / p ^ a) *
      ∏ i ∈ range a, choose (n / p ^ i % p) (k / p ^ i % p) [ZMOD p] :=
  match a with
  | Nat.zero => by simp
  | Nat.succ a => (choose_modEq_choose_mul_prod_range_choose a).trans <| by
    rw [prod_range_succ, cast_mul, ← mul_assoc, mul_right_comm]
    gcongr
    apply choose_modEq_choose_mod_mul_choose_div.trans
    simp_rw [pow_succ, Nat.div_div_eq_div_mul, mul_comm, Int.ModEq.refl]

/-- **Lucas's Theorem**: For primes `p`, `choose n k` is congruent to the product of
`choose (⌊n / p ^ i⌋ % p) (⌊k / p ^ i⌋ % p)` over `i` modulo `p`. -/
/-
**Choose.choose_modEq_prod_range_choose** 是 Mathlib 中的一个定理，位于命名空间 `Choose`。
形式化陈述：choose_modEq_prod_range_choose {a : Nat} (ha₁ : n < p ^ a) (ha₂ : k < p ^ 
a) : choose n k ≡ ∏ i in range a, choose (n / p ^ i % p) (k / p ^ i % p) [ZMOD p
]
参数：ha₁ : n < p ^ a；ha₂ : k < p ^ a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.ModEq.trans`：∀ {n a b c : ℤ}, a ≡ b [ZMOD n] → b ≡ c [ZMOD n] → a ≡ 
c [ZMOD n]
· 使用定理 `Choose.choose_modEq_choose_mul_prod_range_choose`：choose_modEq_choose_mu
l_prod_range_choose (a : Nat) : choose n k ≡ choose (n / p ^ a) (k / p ^ a) * ∏ 
i in range a, choose (n / p ^ i % p) (…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.div_eq_of_lt`：∀ {a b : ℕ}, a < b → a / b = 0
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `Nat.cast_prod`：cast_prod [CommSemiring R] (f : ι -> Nat) (s : Finset ι) 
: (↑(∏ i in s, f i) : R) = ∏ i in s, (f i : R)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p

--- 原说明 ---
**Lucas's Theorem**: For primes `p`, `choose n k` is congruent to the product of
`choose (⌊n / p ^ i⌋ % p) (⌊k / p ^ i⌋ % p)` over `i` modulo `p`.
-/
theorem choose_modEq_prod_range_choose {a : ℕ} (ha₁ : n < p ^ a) (ha₂ : k < p ^ a) :
    choose n k ≡ ∏ i ∈ range a, choose (n / p ^ i % p) (k / p ^ i % p) [ZMOD p] := by
  apply (choose_modEq_choose_mul_prod_range_choose a).trans
  simp_rw [Nat.div_eq_of_lt ha₁, Nat.div_eq_of_lt ha₂, choose, cast_one, one_mul, cast_prod,
    Int.ModEq.refl]

/-- **Lucas's Theorem**: For primes `p`, `choose n k` is congruent to the product of
`choose (⌊n / p ^ i⌋ % p) (⌊k / p ^ i⌋ % p)` over `i` modulo `p`. -/
/-
**Choose.choose_modEq_prod_range_choose_nat** 是 Mathlib 中的一个定理，位于命名空间 `Choose`。
形式化陈述：choose_modEq_prod_range_choose_nat {a : Nat} (ha₁ : n < p ^ a) (ha₂ : k < 
p ^ a) : choose n k ≡ ∏ i in range a, choose (n / p ^ i % p) (k / p ^ i % p) [MO
D p]
参数：ha₁ : n < p ^ a；ha₂ : k < p ^ a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.natCast_modEq_iff`：natCast_modEq_iff {a b n : Nat} : a ≡ b [ZMOD n] 
↔ a ≡ b [MOD n]
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Choose.choose_modEq_prod_range_choose`：choose_modEq_prod_range_choose {a
 : Nat} (ha₁ : n < p ^ a) (ha₂ : k < p ^ a) : choose n k ≡ ∏ i in range a, choos
e (n / p ^ i % p) (k / p ^ …

--- 原说明 ---
**Lucas's Theorem**: For primes `p`, `choose n k` is congruent to the product of
`choose (⌊n / p ^ i⌋ % p) (⌊k / p ^ i⌋ % p)` over `i` modulo `p`.
-/
theorem choose_modEq_prod_range_choose_nat {a : ℕ} (ha₁ : n < p ^ a) (ha₂ : k < p ^ a) :
    choose n k ≡ ∏ i ∈ range a, choose (n / p ^ i % p) (k / p ^ i % p) [MOD p] := by
  rw [← Int.natCast_modEq_iff]
  exact_mod_cast choose_modEq_prod_range_choose ha₁ ha₂

alias lucas_theorem := choose_modEq_prod_range_choose
alias lucas_theorem_nat := choose_modEq_prod_range_choose_nat

/-- For primes `p`, `choose (p * a) (p * b)` is congruent to `choose a b` modulo `p`.
Also see `choose_mul_mul_modEq_choose_nat` for the version with `MOD`. -/
/-
**Choose.choose_mul_mul_modEq_choose** 是 Mathlib 中的一个定理，位于命名空间 `Choose`。
形式化陈述：choose_mul_mul_modEq_choose : choose (p * a) (p * b) ≡ choose a b [ZMOD p]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.GCongr.rel_imp_rel`：rel_imp_rel (h₁ : r c a) (h₂ : r b d)
 : r a b -> r c d
· 使用定理 `Int.ModEq.instIsTrans`：∀ {n : ℤ}, IsTrans ℤ n.ModEq
· 使用定理 `Choose.choose_modEq_choose_mod_mul_choose_div`：choose_modEq_choose_mod_m
ul_choose_div : choose n k ≡ choose (n % p) (k % p) * choose (n / p) (k / p) [ZM
OD p]
· 使用定理 `Int.ModEq.refl`：∀ {n : ℤ} (a : ℤ), a ≡ a [ZMOD n]
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.mul_mod_right`：∀ (m n : ℕ), m * n % m = 0
· 使用定理 `Nat.choose_self`：choose_self (n : Nat) : choose n n = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.mul_div_right`：∀ (n : ℕ) {m : ℕ}, 0 < m → m * n / m = n
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a

--- 原说明 ---
For primes `p`, `choose (p * a) (p * b)` is congruent to `choose a b` modulo `p`
.
Also see `choose_mul_mul_modEq_choose_nat` for the version with `MOD`.
-/
theorem choose_mul_mul_modEq_choose :
    choose (p * a) (p * b) ≡ choose a b [ZMOD p] := by
  grw [choose_modEq_choose_mod_mul_choose_div]
  simp [NeZero.pos, Int.ModEq.refl]

/-- For primes `p`, `choose (p * a) (p * b)` is congruent to `choose a b` modulo `p`.
Also see `choose_mul_mul_modEq_choose` for the version with `ZMOD`. -/
/-
**Choose.choose_mul_mul_modEq_choose_nat** 是 Mathlib 中的一个定理，位于命名空间 `Choose`。
形式化陈述：choose_mul_mul_modEq_choose_nat : choose (p * a) (p * b) ≡ choose a b [MOD
 p]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.natCast_modEq_iff`：natCast_modEq_iff {a b n : Nat} : a ≡ b [ZMOD n] 
↔ a ≡ b [MOD n]
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Choose.choose_mul_mul_modEq_choose`：choose_mul_mul_modEq_choose : choose
 (p * a) (p * b) ≡ choose a b [ZMOD p]

--- 原说明 ---
For primes `p`, `choose (p * a) (p * b)` is congruent to `choose a b` modulo `p`
.
Also see `choose_mul_mul_modEq_choose` for the version with `ZMOD`.
-/
theorem choose_mul_mul_modEq_choose_nat :
    choose (p * a) (p * b) ≡ choose a b [MOD p] := by
  rw [← Int.natCast_modEq_iff]
  exact_mod_cast choose_mul_mul_modEq_choose

/-- For primes `p`, `choose (p ^ k * a) (p ^ k * b)` is congruent to `choose a b` modulo `p`.
Also see `choose_pow_mul_pow_mul_modEq_choose_nat` for the version with `MOD`. -/
/-
**Choose.choose_pow_mul_pow_mul_modEq_choose** 是 Mathlib 中的一个定理，位于命名空间 `Choose`。
形式化陈述：choose_pow_mul_pow_mul_modEq_choose : choose (p ^ k * a) (p ^ k * b) ≡ cho
ose a b [ZMOD p]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Nat.pow_succ'`：∀ {m n : ℕ}, m ^ n.succ = m * m ^ n
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `Mathlib.Tactic.GCongr.rel_imp_rel`：rel_imp_rel (h₁ : r c a) (h₂ : r b d)
 : r a b -> r c d
· 使用定理 `Int.ModEq.instIsTrans`：∀ {n : ℤ}, IsTrans ℤ n.ModEq
· 使用定理 `Choose.choose_mul_mul_modEq_choose`：choose_mul_mul_modEq_choose : choose
 (p * a) (p * b) ≡ choose a b [ZMOD p]
· 使用定理 `Int.ModEq.refl`：∀ {n : ℤ} (a : ℤ), a ≡ a [ZMOD n]

--- 原说明 ---
For primes `p`, `choose (p ^ k * a) (p ^ k * b)` is congruent to `choose a b` mo
dulo `p`.
Also see `choose_pow_mul_pow_mul_modEq_choose_nat` for the version with `MOD`.
-/
theorem choose_pow_mul_pow_mul_modEq_choose :
    choose (p ^ k * a) (p ^ k * b) ≡ choose a b [ZMOD p] := by
  induction k with
  | zero => simp [Int.ModEq.refl]
  | succ k ih =>
    grw [Nat.pow_succ', mul_assoc, mul_assoc, choose_mul_mul_modEq_choose, ih]

/-- For primes `p`, `choose (p ^ k * a) (p ^ k * b)` is congruent to `choose a b` modulo `p`.
Also see `choose_pow_mul_pow_mul_modEq_choose` for the version with `ZMOD`. -/
/-
**Choose.choose_pow_mul_pow_mul_modEq_choose_nat** 是 Mathlib 中的一个定理，位于命名空间 `Choo
se`。
形式化陈述：choose_pow_mul_pow_mul_modEq_choose_nat : choose (p ^ k * a) (p ^ k * b) ≡
 choose a b [MOD p]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.natCast_modEq_iff`：natCast_modEq_iff {a b n : Nat} : a ≡ b [ZMOD n] 
↔ a ≡ b [MOD n]
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Choose.choose_pow_mul_pow_mul_modEq_choose`：choose_pow_mul_pow_mul_modEq
_choose : choose (p ^ k * a) (p ^ k * b) ≡ choose a b [ZMOD p]

--- 原说明 ---
For primes `p`, `choose (p ^ k * a) (p ^ k * b)` is congruent to `choose a b` mo
dulo `p`.
Also see `choose_pow_mul_pow_mul_modEq_choose` for the version with `ZMOD`.
-/
theorem choose_pow_mul_pow_mul_modEq_choose_nat :
    choose (p ^ k * a) (p ^ k * b) ≡ choose a b [MOD p] := by
  rw [← Int.natCast_modEq_iff]
  exact_mod_cast choose_pow_mul_pow_mul_modEq_choose

/-- For primes `p` and positive integer `n`, assume that for all `i ∈ Icc 1 (n - 1)`,
`choose n i` congruent to `0` module `p`, then `n = p ^ multiplicity p n`.
Also see `eq_pow_multiplicity_of_choose_modEq_zero_nat` for the version with `MOD`. -/
/-
**Choose.eq_pow_multiplicity_of_choose_modEq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cho
ose`。
形式化陈述：eq_pow_multiplicity_of_choose_modEq_zero (hn : 0 < n) (h : forall i in Icc
 1 (n - 1), n.choose i ≡ 0 [ZMOD p]) : n = p ^ multiplicity p n
参数：hn : 0 < n；h : forall i in Icc 1 (n - 1), n.choose i ≡ 0 [ZMOD p]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `pow_multiplicity_dvd`：pow_multiplicity_dvd (a b : α) : a ^ (multiplicity
 a b) ∣ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FiniteMultiplicity.pow_dvd_iff_le_multiplicity`：FiniteMultiplicity.pow_d
vd_iff_le_multiplicity (hf : FiniteMultiplicity a b) {k : Nat} : a ^ k ∣ b ↔ k <
= multiplicity a b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.finiteMultiplicity_iff`：Nat.finiteMultiplicity_iff {a b : Nat} : Fin
iteMultiplicity a b ↔ a != 1 ∧ 0 < b
· 使用定理 `Nat.Prime.ne_one`：∀ {p : ℕ}, Nat.Prime p → p ≠ 1
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Nat.mul_dvd_mul_left`：∀ {b c : ℕ} (a : ℕ), b ∣ c → a * b ∣ a * c
· 使用定理 `Nat.dvd_iff_mod_eq_zero`：∀ {m n : ℕ}, m ∣ n ↔ n % m = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用引理 `Nat.choose_one_right`：choose_one_right (n : Nat) : choose n 1 = n
· 使用引理 `Mathlib.Tactic.GCongr.rel_imp_rel`：rel_imp_rel (h₁ : r c a) (h₂ : r b d)
 : r a b -> r c d
· 使用定理 `Int.ModEq.instIsTrans`：∀ {n : ℤ}, IsTrans ℤ n.ModEq
· 使用定理 `Int.ModEq.symm`：∀ {n a b : ℤ}, a ≡ b [ZMOD n] → b ≡ a [ZMOD n]
· 使用定理 `Choose.choose_pow_mul_pow_mul_modEq_choose`：choose_pow_mul_pow_mul_modEq
_choose : choose (p ^ k * a) (p ^ k * b) ≡ choose a b [ZMOD p]
· 使用定理 `Int.ModEq.refl`：∀ {n : ℤ} (a : ℤ), a ≡ a [ZMOD n]
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a

--- 原说明 ---
For primes `p` and positive integer `n`, assume that for all `i ∈ Icc 1 (n - 1)`
,
`choose n i` congruent to `0` module `p`, then `n = p ^ multiplicity p n`.
Also see `eq_pow_multiplicity_of_choose_modEq_zero_nat` for the version with `MO
D`.
-/
theorem eq_pow_multiplicity_of_choose_modEq_zero (hn : 0 < n)
    (h : ∀ i ∈ Icc 1 (n - 1), n.choose i ≡ 0 [ZMOD p]) : n = p ^ multiplicity p n := by
  rename_i hp
  by_contra! hn₀
  obtain ⟨m, hm⟩ := pow_multiplicity_dvd p n
  specialize h (p ^ multiplicity p n) (by grind [le_of_dvd hn (pow_multiplicity_dvd p n)])
  nth_grw 1 [← mul_one (p ^ _), hm, choose_pow_mul_pow_mul_modEq_choose, choose_one_right] at h
  suffices multiplicity p n + 1 ≤ multiplicity p n by lia
  rw [← FiniteMultiplicity.pow_dvd_iff_le_multiplicity]
  · nth_rw 2 [hm]
    simpa [pow_add] using Nat.mul_dvd_mul_left _ (dvd_iff_mod_eq_zero.mpr (by exact_mod_cast h))
  · exact finiteMultiplicity_iff.mpr ⟨hp.out.ne_one, hn⟩

/-- For primes `p` and positive integer `n`, assume that for all `i ∈ Icc 1 (n - 1)`,
`choose n i` congruent to `0` module `p`, then `n = p ^ multiplicity p n`.
Also see `eq_pow_multiplicity_of_choose_modEq_zero` for the version with `ZMOD`. -/
/-
**Choose.eq_pow_multiplicity_of_choose_modEq_zero_nat** 是 Mathlib 中的一个定理，位于命名空间 
`Choose`。
形式化陈述：eq_pow_multiplicity_of_choose_modEq_zero_nat (hn : 0 < n) (h : forall i in
 Icc 1 (n - 1), n.choose i ≡ 0 [MOD p]) : n = p ^ multiplicity p n
参数：hn : 0 < n；h : forall i in Icc 1 (n - 1), n.choose i ≡ 0 [MOD p]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Choose.eq_pow_multiplicity_of_choose_modEq_zero`：eq_pow_multiplicity_of_
choose_modEq_zero (hn : 0 < n) (h : forall i in Icc 1 (n - 1), n.choose i ≡ 0 [Z
MOD p]) : n = p ^ multiplicity p n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0

--- 原说明 ---
For primes `p` and positive integer `n`, assume that for all `i ∈ Icc 1 (n - 1)`
,
`choose n i` congruent to `0` module `p`, then `n = p ^ multiplicity p n`.
Also see `eq_pow_multiplicity_of_choose_modEq_zero` for the version with `ZMOD`.
-/
theorem eq_pow_multiplicity_of_choose_modEq_zero_nat (hn : 0 < n)
    (h : ∀ i ∈ Icc 1 (n - 1), n.choose i ≡ 0 [MOD p]) : n = p ^ multiplicity p n :=
  eq_pow_multiplicity_of_choose_modEq_zero hn (by exact_mod_cast h)

/-- For a prime power `n`, the minimal prime factor divides the greatest common divisor of
`choose n 1, ⋯, choose n (n - 1)`. -/
/-
**Choose.minFac_dvd_gcd_choose_of_isPrimePow** 是 Mathlib 中的一个定理，位于命名空间 `Choose`。
形式化陈述：minFac_dvd_gcd_choose_of_isPrimePow (h : IsPrimePow n) : n.minFac ∣ (Icc 1
 (n - 1)).gcd n.choose
参数：h : IsPrimePow n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isPrimePow_nat_iff_bounded_log_minFac`：isPrimePow_nat_iff_bounded_log_mi
nFac (n : Nat) : IsPrimePow n ↔ exists k : Nat, k <= Nat.log 2 n ∧ 0 < k ∧ n = n
.minFac ^ k
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.dvd_gcd_iff`：dvd_gcd_iff {a : α} : a ∣ s.gcd f ↔ forall b in s, a
 ∣ f b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.Prime.dvd_choose_pow`：dvd_choose_pow (hp : Prime p) (hk : k != 0) (h
kp : k != p ^ n) : p ∣ (p ^ n).choose k
· 使用定理 `Nat.minFac_prime_iff`：minFac_prime_iff {n : Nat} : Prime (minFac n) ↔ n 
!= 1
· 使用定理 `IsPrimePow.ne_one`：IsPrimePow.ne_one {n : R} (h : IsPrimePow n) : n != 1

--- 原说明 ---
For a prime power `n`, the minimal prime factor divides the greatest common divi
sor of
`choose n 1, ⋯, choose n (n - 1)`.
-/
theorem minFac_dvd_gcd_choose_of_isPrimePow (h : IsPrimePow n) :
    n.minFac ∣ (Icc 1 (n - 1)).gcd n.choose := by
  obtain ⟨k, _, _, hn₁⟩ := (isPrimePow_nat_iff_bounded_log_minFac _).mp h
  exact dvd_gcd_iff.mpr fun i hi => by
    nth_rw 2 [hn₁]
    exact Prime.dvd_choose_pow (minFac_prime_iff.mpr h.ne_one) (by grind) (by grind)
/-
**Choose.minFac_sq_ndvd_gcd_choose_of_isPrimePow** 是 Mathlib 中的一个引理，位于命名空间 `Choo
se`。
形式化陈述：minFac_sq_ndvd_gcd_choose_of_isPrimePow (h : IsPrimePow n) : ¬ n.minFac ^ 
2 ∣ (Icc 1 (n - 1)).gcd n.choose
参数：h : IsPrimePow n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isPrimePow_nat_iff_bounded_log_minFac`：isPrimePow_nat_iff_bounded_log_mi
nFac (n : Nat) : IsPrimePow n ↔ exists k : Nat, k <= Nat.log 2 n ∧ 0 < k ∧ n = n
.minFac ^ k
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.minFac_prime_iff`：minFac_prime_iff {n : Nat} : Prime (minFac n) ↔ n 
!= 1
· 使用定理 `IsPrimePow.ne_one`：IsPrimePow.ne_one {n : R} (h : IsPrimePow n) : n != 1
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Finset.dvd_gcd_iff`：dvd_gcd_iff {a : α} : a ∣ s.gcd f ↔ forall b in s, a
 ∣ f b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.pow_le_pow_right`：∀ {n : ℕ}, n > 0 → ∀ {i j : ℕ}, i ≤ j → n ^ i ≤ n 
^ j
· 使用定理 `Nat.minFac_pos`：minFac_pos (n : Nat) : 0 < minFac n
· 使用定理 `Nat.sub_le`：∀ (n m : ℕ), n - m ≤ n
· 使用定理 `Nat.one_le_pow`：∀ (n m : ℕ), 0 < m → 1 ≤ m ^ n
· 使用定理 `Nat.le_sub_one_of_lt`：∀ {a b : ℕ}, a < b → a ≤ b - 1
· 使用定理 `Nat.pow_lt_pow_of_lt`：∀ {a n m : ℕ}, 1 < a → n < m → a ^ n < a ^ m
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `Nat.sub_one_lt_of_lt`：∀ {n m : ℕ}, m < n → n - 1 < n
· 使用定理 `emultiplicity_lt_iff_not_dvd`：emultiplicity_lt_iff_not_dvd {k : Nat} : e
multiplicity a b < k ↔ ¬a ^ k ∣ b
· 使用定理 `Nat.Prime.emultiplicity_choose_prime_pow`：emultiplicity_choose_prime_pow
 {p n k : Nat} (hp : p.Prime) (hkn : k <= p ^ n) (hk0 : k != 0) : emultiplicity 
p (choose (p ^ n) k) = ↑(n - m…
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用定理 `multiplicity_pow_self_of_prime`：multiplicity_pow_self_of_prime {p : α} (
hp : Prime p) (n : Nat) : multiplicity p (p ^ n) = n
· 使用定理 `Nat.prime_iff`：prime_iff {p : Nat} : p.Prime ↔ _root_.Prime p
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
（共 33 条，此处仅展示前 30 条）
-/
lemma minFac_sq_ndvd_gcd_choose_of_isPrimePow (h : IsPrimePow n) :
    ¬ n.minFac ^ 2 ∣ (Icc 1 (n - 1)).gcd n.choose := by
  obtain ⟨k, _, k_pos, hn₁⟩ := (isPrimePow_nat_iff_bounded_log_minFac _).mp h
  have isPrime := minFac_prime_iff.mpr (IsPrimePow.ne_one h)
  refine mt Finset.dvd_gcd_iff.mp ?_
  simp only [mem_Icc, not_forall]
  have : n.minFac ^ (k - 1) ≤ n.minFac ^ k := Nat.pow_le_pow_right (minFac_pos n) (sub_le k 1)
  refine ⟨n.minFac ^ (k - 1), ⟨one_le_pow _ _ (minFac_pos n), ?_⟩, ?_⟩
  · refine le_sub_one_of_lt ?_
    nth_rw 2 [hn₁]
    exact Nat.pow_lt_pow_of_lt (Prime.one_lt isPrime) (sub_one_lt_of_lt k_pos)
  · refine emultiplicity_lt_iff_not_dvd.mp ?_
    nth_rw 2 [hn₁]
    rw [Nat.Prime.emultiplicity_choose_prime_pow isPrime this (pow_ne_zero _
      (Nat.Prime.ne_zero isPrime)), multiplicity_pow_self_of_prime (prime_iff.mp isPrime)]
    norm_cast
    grind
/-
**Choose.primeFactors_gcd_choose_of_isPrimePow** 是 Mathlib 中的一个引理，位于命名空间 `Choose
`。
形式化陈述：primeFactors_gcd_choose_of_isPrimePow (h : IsPrimePow n) : ((Icc 1 (n - 1)
).gcd n.choose).primeFactors = {n.minFac}
参数：h : IsPrimePow n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.gcd_ne_zero_iff`：gcd_ne_zero_iff : s.gcd f != 0 ↔ exists x in s, 
f x != 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用引理 `Nat.choose_one_right`：choose_one_right (n : Nat) : choose n 1 = n
· 使用定理 `Nat.minFac_prime_iff`：minFac_prime_iff {n : Nat} : Prime (minFac n) ↔ n 
!= 1
· 使用定理 `IsPrimePow.ne_one`：IsPrimePow.ne_one {n : R} (h : IsPrimePow n) : n != 1
· 使用定理 `Finset.eq_singleton_iff_unique_mem`：eq_singleton_iff_unique_mem {s : Fin
set α} {a : α} : s = {a} ↔ a in s ∧ forall x in s, x = a
· 使用定理 `Nat.Prime.mem_primeFactors`：∀ {n p : ℕ}, Nat.Prime p → p ∣ n → n ≠ 0 → p
 ∈ n.primeFactors
· 使用定理 `Choose.minFac_dvd_gcd_choose_of_isPrimePow`：minFac_dvd_gcd_choose_of_isP
rimePow (h : IsPrimePow n) : n.minFac ∣ (Icc 1 (n - 1)).gcd n.choose
· 使用定理 `Choose.eq_pow_multiplicity_of_choose_modEq_zero_nat`：eq_pow_multiplicity
_of_choose_modEq_zero_nat (hn : 0 < n) (h : forall i in Icc 1 (n - 1), n.choose 
i ≡ 0 [MOD p]) : n = p ^ multiplicity p n
· 使用定理 `IsPrimePow.pos`：IsPrimePow.pos {n : Nat} (hn : IsPrimePow n) : 0 < n
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Nat.minFac_dvd`：minFac_dvd (n : Nat) : minFac n ∣ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.prime_dvd_prime_iff_eq`：prime_dvd_prime_iff_eq {p q : Nat} (pp : p.P
rime) (qp : q.Prime) : p ∣ q ↔ p = q
· 使用定理 `Nat.Prime.dvd_of_dvd_pow`：∀ {p m n : ℕ}, Nat.Prime p → p ∣ m ^ n → p ∣ m
-/
lemma primeFactors_gcd_choose_of_isPrimePow (h : IsPrimePow n) :
    ((Icc 1 (n - 1)).gcd n.choose).primeFactors = {n.minFac} := by
  have ne_zero : (Icc 1 (n - 1)).gcd n.choose ≠ 0 :=
    gcd_ne_zero_iff.mpr ⟨1, by simp; grind [IsPrimePow.two_le h]⟩
  have isPrime := minFac_prime_iff.mpr (IsPrimePow.ne_one h)
  refine eq_singleton_iff_unique_mem.mpr ⟨isPrime.mem_primeFactors
    (minFac_dvd_gcd_choose_of_isPrimePow h) ne_zero, ?_⟩
  intro p hp
  simp only [mem_primeFactors, ne_eq] at hp
  obtain ⟨hp₁, hp₂, hp₃⟩ := hp
  have : Fact (Nat.Prime p) := ⟨hp₁⟩
  simp_rw [Finset.dvd_gcd_iff, ← modEq_zero_iff_dvd] at hp₂
  have := eq_pow_multiplicity_of_choose_modEq_zero_nat h.pos hp₂
  have dvd_pow : n.minFac ∣  p ^ multiplicity p n := this ▸ minFac_dvd _
  exact (Nat.prime_dvd_prime_iff_eq isPrime hp₁).mp (isPrime.dvd_of_dvd_pow dvd_pow)|>.symm

/-- For a prime power `n`, the greatest common divisor of `choose n 1, ⋯, choose n (n - 1)`
is actually the minimal prime factor of `n`. -/
/-
**Choose.gcd_choose_eq_minFac_of_isPrimePow** 是 Mathlib 中的一个定理，位于命名空间 `Choose`。
形式化陈述：gcd_choose_eq_minFac_of_isPrimePow (h : IsPrimePow n) : (Icc 1 (n - 1)).gc
d n.choose = n.minFac
参数：h : IsPrimePow n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.gcd_ne_zero_iff`：gcd_ne_zero_iff : s.gcd f != 0 ↔ exists x in s, 
f x != 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用引理 `Nat.choose_one_right`：choose_one_right (n : Nat) : choose n 1 = n
· 使用定理 `Nat.minFac_prime_iff`：minFac_prime_iff {n : Nat} : Prime (minFac n) ↔ n 
!= 1
· 使用定理 `IsPrimePow.ne_one`：IsPrimePow.ne_one {n : R} (h : IsPrimePow n) : n != 1
· 使用定理 `multiplicity_eq_of_dvd_of_not_dvd`：multiplicity_eq_of_dvd_of_not_dvd {k 
: Nat} (hk : a ^ k ∣ b) (hsucc : ¬a ^ (k + 1) ∣ b) : multiplicity a b = k
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Choose.minFac_dvd_gcd_choose_of_isPrimePow`：minFac_dvd_gcd_choose_of_isP
rimePow (h : IsPrimePow n) : n.minFac ∣ (Icc 1 (n - 1)).gcd n.choose
· 使用引理 `Choose.minFac_sq_ndvd_gcd_choose_of_isPrimePow`：minFac_sq_ndvd_gcd_choos
e_of_isPrimePow (h : IsPrimePow n) : ¬ n.minFac ^ 2 ∣ (Icc 1 (n - 1)).gcd n.choo
se
· 使用引理 `Nat.prod_primeFactors_coe_pow_factorization`：prod_primeFactors_coe_pow_f
actorization (hn : n != 0) : n = ∏ (p : n.primeFactors), (p : Nat) ^ (n.factoriz
ation p)
· 使用引理 `Choose.primeFactors_gcd_choose_of_isPrimePow`：primeFactors_gcd_choose_of
_isPrimePow (h : IsPrimePow n) : ((Icc 1 (n - 1)).gcd n.choose).primeFactors = {
n.minFac}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `Finset.prod_singleton`：prod_singleton (f : ι -> M) (a : ι) : ∏ x in sing
leton a, f x = f a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.multiplicity_eq_factorization`：multiplicity_eq_factorization {n p : 
Nat} (pp : p.Prime) (hn : n != 0) : multiplicity p n = n.factorization p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
For a prime power `n`, the greatest common divisor of `choose n 1, ⋯, choose n (
n - 1)`
is actually the minimal prime factor of `n`.
-/
theorem gcd_choose_eq_minFac_of_isPrimePow (h : IsPrimePow n) :
    (Icc 1 (n - 1)).gcd n.choose = n.minFac := by
  have ne_zero : (Icc 1 (n - 1)).gcd n.choose ≠ 0 :=
    gcd_ne_zero_iff.mpr ⟨1, by simp; grind [IsPrimePow.two_le h]⟩
  have isPrime := minFac_prime_iff.mpr (IsPrimePow.ne_one h)
  have : multiplicity n.minFac ((Icc 1 (n - 1)).gcd n.choose) = 1 := by
    refine multiplicity_eq_of_dvd_of_not_dvd ?_ (minFac_sq_ndvd_gcd_choose_of_isPrimePow h)
    simpa using minFac_dvd_gcd_choose_of_isPrimePow h
  rw [Nat.prod_primeFactors_coe_pow_factorization ne_zero, primeFactors_gcd_choose_of_isPrimePow h]
  simp [← Nat.multiplicity_eq_factorization isPrime ne_zero, this]

/-- For a natural number `n` greater than `1`, assume that `n` is not a prime power, then
the greatest common divisor of  `choose n 1, ⋯, choose n (n - 1)` is `1`. -/
/-
**Choose.gcd_choose_eq_one_of_not_isPrimePow** 是 Mathlib 中的一个定理，位于命名空间 `Choose`。
形式化陈述：gcd_choose_eq_one_of_not_isPrimePow (hn : 1 < n) (hpn : ¬ IsPrimePow n) : 
(Icc 1 (n - 1)).gcd n.choose = 1
参数：hn : 1 < n；hpn : ¬ IsPrimePow n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `Nat.exists_prime_and_dvd`：exists_prime_and_dvd {n : Nat} (hn : n != 1) :
 exists p, Prime p ∧ p ∣ n
· 使用定理 `Choose.eq_pow_multiplicity_of_choose_modEq_zero_nat`：eq_pow_multiplicity
_of_choose_modEq_zero_nat (hn : 0 < n) (h : forall i in Icc 1 (n - 1), n.choose 
i ≡ 0 [MOD p]) : n = p ^ multiplicity p n
· 使用定理 `Nat.zero_lt_of_lt`：∀ {a b : ℕ}, a < b → 0 < b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isPrimePow_nat_iff`：isPrimePow_nat_iff (n : Nat) : IsPrimePow n ↔ exists
 p k : Nat, Nat.Prime p ∧ 0 < k ∧ p ^ k = n
· 使用定理 `Dvd.multiplicity_pos`：∀ {α : Type u_1} [inst : Monoid α] {a b : α}, a ∣ 
b → 0 < multiplicity a b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.modEq_zero_iff_dvd`：modEq_zero_iff_dvd : a ≡ 0 [MOD n] ↔ n ∣ a
· 使用引理 `Nat.choose_one_right`：choose_one_right (n : Nat) : choose n 1 = n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
For a natural number `n` greater than `1`, assume that `n` is not a prime power,
 then
the greatest common divisor of  `choose n 1, ⋯, choose n (n - 1)` is `1`.
-/
theorem gcd_choose_eq_one_of_not_isPrimePow (hn : 1 < n) (hpn : ¬ IsPrimePow n) :
    (Icc 1 (n - 1)).gcd n.choose = 1 := by
  contrapose! hpn
  obtain ⟨q, hq, h⟩ := Nat.exists_prime_and_dvd hpn
  simp_rw [Finset.dvd_gcd_iff, ← modEq_zero_iff_dvd] at h
  have : Fact (Nat.Prime q) := ⟨hq⟩
  have := eq_pow_multiplicity_of_choose_modEq_zero_nat (zero_lt_of_lt hn) h
  refine (isPrimePow_nat_iff n).mpr ⟨q, _, hq, Dvd.multiplicity_pos ?_, this.symm⟩
  specialize h 1 (by grind)
  rw [choose_one_right, modEq_zero_iff_dvd] at h
  exact h

end Choose

