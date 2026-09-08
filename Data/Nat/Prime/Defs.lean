/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module

public import Mathlib.Algebra.Group.Nat.Units
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.Prime.Defs
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Order.Basic

/-!
# Prime numbers

This file deals with prime numbers: natural numbers `p ≥ 2` whose only divisors are `p` and `1`.

## Important declarations

- `Nat.Prime`: the predicate that expresses that a natural number `p` is prime
- `Nat.Primes`: the subtype of natural numbers that are prime
- `Nat.minFac n`: the minimal prime factor of a natural number `n ≠ 1`
- `Nat.prime_iff`: `Nat.Prime` coincides with the general definition of `Prime`
- `Nat.irreducible_iff_nat_prime`: a non-unit natural number is
                                  only divisible by `1` iff it is prime

-/

@[expose] public section

assert_not_exists Ring

namespace Nat

variable {n : ℕ}

/-- `Nat.Prime p` means that `p` is a prime number, that is, a natural number
  at least 2 whose only divisors are `p` and `1`.
  The theorem `Nat.prime_def` witnesses this description of a prime number. -/
@[pp_nodot, wikidata Q49008]
/-
**Nat.Prime** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：Prime (p : Nat)
参数：p : Nat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Nat.Prime p` means that `p` is a prime number, that is, a natural number
  at least 2 whose only divisors are `p` and `1`.
  The theorem `Nat.prime_def` witnesses this description of a prime number.
-/
def Prime (p : ℕ) :=
  Irreducible p
/-
**Nat.irreducible_iff_nat_prime** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：irreducible_iff_nat_prime (a : Nat) : Irreducible a ↔ Nat.Prime a
参数：a : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem irreducible_iff_nat_prime (a : ℕ) : Irreducible a ↔ Nat.Prime a :=
  Iff.rfl
/-
**Nat.not_prime_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：¬Nat.Prime 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irreducible.ne_zero`：∀ {M : Type u_1} [inst : MonoidWithZero M] {p : M},
 Irreducible p → p ≠ 0
-/
theorem not_prime_zero : ¬ Prime 0
  | h => h.ne_zero rfl

/-- A copy of `not_prime_zero` stated in a way that works for `aesop`.

See https://github.com/leanprover-community/aesop/issues/197 for an explanation. -/
/-
**Nat.prime_zero_false** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：Nat.Prime 0 → False
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.not_prime_zero`：¬Nat.Prime 0

--- 原说明 ---
A copy of `not_prime_zero` stated in a way that works for `aesop`.

See https://github.com/leanprover-community/aesop/issues/197 for an explanation.
-/
@[aesop safe destruct] theorem prime_zero_false : Prime 0 → False :=
  not_prime_zero
/-
**Nat.not_prime_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：¬Nat.Prime 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Irreducible.ne_one`：Irreducible.ne_one (hp : Irreducible p) : p != 1
-/
theorem not_prime_one : ¬ Prime 1
  | h => h.ne_one rfl

/-- A copy of `not_prime_one` stated in a way that works for `aesop`.

See https://github.com/leanprover-community/aesop/issues/197 for an explanation. -/
/-
**Nat.prime_one_false** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：Nat.Prime 1 → False
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.not_prime_one`：¬Nat.Prime 1

--- 原说明 ---
A copy of `not_prime_one` stated in a way that works for `aesop`.

See https://github.com/leanprover-community/aesop/issues/197 for an explanation.
-/
@[aesop safe destruct] theorem prime_one_false : Prime 1 → False :=
  not_prime_one
/-
**Nat.Prime.ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irreducible.ne_zero`：∀ {M : Type u_1} [inst : MonoidWithZero M] {p : M},
 Irreducible p → p ≠ 0
-/
theorem Prime.ne_zero {n : ℕ} (h : Prime n) : n ≠ 0 :=
  Irreducible.ne_zero h
/-
**Nat.Prime.pos** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：∀ {p : ℕ}, Nat.Prime p → 0 < p
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
-/
theorem Prime.pos {p : ℕ} (pp : Prime p) : 0 < p :=
  Nat.pos_of_ne_zero pp.ne_zero
/-
**Nat.Prime.two_le** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：∀ {p : ℕ}, Nat.Prime p → 2 ≤ p
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.not_prime_zero`：¬Nat.Prime 0
· 使用定理 `Nat.not_prime_one`：¬Nat.Prime 1
· 使用定理 `Nat.le_add_left`：∀ (n m : ℕ), n ≤ m + n
-/
theorem Prime.two_le : ∀ {p : ℕ}, Prime p → 2 ≤ p
  | 0, h => (not_prime_zero h).elim
  | 1, h => (not_prime_one h).elim
  | _ + 2, _ => le_add_left 2 _
/-
**Nat.Prime.one_lt** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：∀ {p : ℕ}, Nat.Prime p → 1 < p
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Prime.two_le`：∀ {p : ℕ}, Nat.Prime p → 2 ≤ p
-/
theorem Prime.one_lt {p : ℕ} : Prime p → 1 < p :=
  Prime.two_le
/-
**Nat.Prime.one_le** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：∀ {p : ℕ}, Nat.Prime p → 1 ≤ p
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
-/
lemma Prime.one_le {p : ℕ} (hp : p.Prime) : 1 ≤ p := hp.one_lt.le
/-
**Nat.Prime.one_lt'** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
参数：p : ℕ；Nat.Prime p；1 < p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
-/
instance Prime.one_lt' (p : ℕ) [hp : Fact p.Prime] : Fact (1 < p) :=
  ⟨hp.1.one_lt⟩
/-
**Nat.Prime.ne_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：∀ {p : ℕ}, Nat.Prime p → p ≠ 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
-/
theorem Prime.ne_one {p : ℕ} (hp : p.Prime) : p ≠ 1 :=
  hp.one_lt.ne'
/-
**Nat.Prime.eq_one_or_self_of_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：∀ {p : ℕ}, Nat.Prime p → ∀ (m : ℕ), m ∣ p → m = 1 ∨ m = p
参数：m : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irreducible.isUnit_or_isUnit`：∀ {M : Type u_1} [inst : Monoid M] {p : M}
, Irreducible p → ∀ ⦃a b : M⦄, p = a * b → IsUnit a ∨ IsUnit b
· 使用定理 `Or.imp_right`：∀ {b c a : Prop}, (b → c) → a ∨ b → a ∨ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.isUnit_iff`：∀ {n : ℕ}, IsUnit n ↔ n = 1
-/
theorem Prime.eq_one_or_self_of_dvd {p : ℕ} (pp : p.Prime) (m : ℕ) (hm : m ∣ p) :
    m = 1 ∨ m = p := by
  obtain ⟨n, hn⟩ := hm
  have := pp.isUnit_or_isUnit hn
  rw [Nat.isUnit_iff, Nat.isUnit_iff] at this
  apply Or.imp_right _ this
  rintro rfl
  rw [hn, mul_one]

@[inherit_doc Nat.Prime]
/-
**Nat.prime_def** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：prime_def {p : Nat} : Prime p ↔ 2 <= p ∧ forall m, m ∣ p -> m = 1 ∨ m = p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Prime.two_le`：∀ {p : ℕ}, Nat.Prime p → 2 ≤ p
· 使用定理 `Nat.Prime.eq_one_or_self_of_dvd`：∀ {p : ℕ}, Nat.Prime p → ∀ (m : ℕ), m ∣
 p → m = 1 ∨ m = p
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Nat.one_lt_two`：1 < 2
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.isUnit_iff`：∀ {n : ℕ}, IsUnit n ↔ n = 1
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Or.imp_right`：∀ {b c a : Prop}, (b → c) → a ∨ b → a ∨ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `mul_right_inj'`：mul_right_inj' (ha : a != 0) : a * b = a * c ↔ b = c
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `Nat.ne_zero_of_lt`：∀ {b a : ℕ}, b < a → a ≠ 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `dvd_mul_right`：dvd_mul_right (a b : α) : a ∣ a * b
-/
theorem prime_def {p : ℕ} : Prime p ↔ 2 ≤ p ∧ ∀ m, m ∣ p → m = 1 ∨ m = p := by
  refine ⟨fun h => ⟨h.two_le, h.eq_one_or_self_of_dvd⟩, fun h => ?_⟩
  have h1 := Nat.one_lt_two.trans_le h.1
  refine ⟨mt Nat.isUnit_iff.mp h1.ne', ?_⟩
  rintro a b rfl
  simp only [Nat.isUnit_iff]
  refine (h.2 a <| dvd_mul_right ..).imp_right fun hab ↦ ?_
  rw [← mul_right_inj' (Nat.ne_zero_of_lt h1), ← hab, ← hab, mul_one]
/-
**Nat.prime_def_lt** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：prime_def_lt {p : Nat} : Prime p ↔ 2 <= p ∧ forall m < p, m ∣ p -> m = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Nat.prime_def`：prime_def {p : Nat} : Prime p ↔ 2 <= p ∧ forall m, m ∣ p 
-> m = 1 ∨ m = p
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `Nat.ne_of_lt`：∀ {a b : ℕ}, a < b → a ≠ b
· 使用定理 `Or.imp_left`：∀ {a b c : Prop}, (a → b) → a ∨ c → b ∨ c
· 使用定理 `LE.le.lt_or_eq_dec`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α} [
DecidableLE α], a ≤ b → a < b ∨ a = b
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
· 使用定理 `Nat.le_of_succ_le`：∀ {n m : ℕ}, n.succ ≤ m → n ≤ m
-/
theorem prime_def_lt {p : ℕ} : Prime p ↔ 2 ≤ p ∧ ∀ m < p, m ∣ p → m = 1 :=
  prime_def.trans <|
    and_congr_right fun p2 =>
      forall_congr' fun _ =>
        ⟨fun h l d => (h d).resolve_right (ne_of_lt l), fun h d =>
          (le_of_dvd (le_of_succ_le p2) d).lt_or_eq_dec.imp_left fun l => h l d⟩
/-
**Nat.prime_def_lt'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：prime_def_lt' {p : Nat} : Prime p ↔ 2 <= p ∧ forall m, 2 <= m -> m < p -> 
¬m ∣ p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Nat.prime_def_lt`：prime_def_lt {p : Nat} : Prime p ↔ 2 <= p ∧ forall m <
 p, m ∣ p -> m = 1
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `not_lt_of_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Nat.le_add_left`：∀ (n m : ℕ), n ≤ m + n
-/
theorem prime_def_lt' {p : ℕ} : Prime p ↔ 2 ≤ p ∧ ∀ m, 2 ≤ m → m < p → ¬m ∣ p :=
  prime_def_lt.trans <|
    and_congr_right fun p2 =>
      forall_congr' fun m =>
        ⟨fun h m2 l d => not_lt_of_ge m2 ((h l d).symm ▸ by decide), fun h l d => by
          rcases m with (_ | _ | m)
          · omega
          · rfl
          · exact (h (le_add_left 2 m) l).elim d⟩
/-
**Nat.prime_def_le_sqrt** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：prime_def_le_sqrt {p : Nat} : Prime p ↔ 2 <= p ∧ forall m, 2 <= m -> m <= 
sqrt p -> ¬m ∣ p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Nat.prime_def_lt'`：prime_def_lt' {p : Nat} : Prime p ↔ 2 <= p ∧ forall m
, 2 <= m -> m < p -> ¬m ∣ p
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用引理 `Nat.sqrt_lt_self`：sqrt_lt_self (h : 1 < n) : sqrt n < n
· 使用引理 `Nat.le_sqrt_of_eq_mul`：le_sqrt_of_eq_mul {a b c : Nat} (h : a = b * c) :
 b <= a.sqrt ∨ c <= a.sqrt
· 使用定理 `Nat.lt_of_mul_lt_mul_right`：∀ {a b c : ℕ}, b * a < c * a → b < c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem prime_def_le_sqrt {p : ℕ} : Prime p ↔ 2 ≤ p ∧ ∀ m, 2 ≤ m → m ≤ sqrt p → ¬m ∣ p :=
  prime_def_lt'.trans <|
    and_congr_right fun p2 =>
      ⟨fun a m m2 l => a m m2 <| lt_of_le_of_lt l <| sqrt_lt_self p2, fun a m m2 l mdvd@⟨k, e⟩ => by
        rcases le_sqrt_of_eq_mul e with hm | hk
        · exact a m m2 hm mdvd
        · rw [mul_comm] at e
          exact a k (Nat.lt_of_mul_lt_mul_right (a := m) (by rwa [one_mul, ← e])) hk ⟨m, e⟩⟩
/-
**Nat.prime_iff_not_exists_mul_eq** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：prime_iff_not_exists_mul_eq {p : Nat} : p.Prime ↔ 2 <= p ∧ ¬ exists m n, m
 < p ∧ n < p ∧ m * n = p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Std.instReflLeOfIsPreorder`：∀ {α : Type u} [inst : LE α] [Std.IsPreorder
 α], Std.Refl fun x1 x2 => x1 ≤ x2
· 使用定理 `Lean.Grind.instIsPreorderNat`：Std.IsPreorder ℕ
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_ne_zero_iff`：mul_ne_zero_iff : a * b != 0 ↔ a != 0 ∧ b != 0
· 使用定理 `IsRightCancelMulZero.to_noZeroDivisors`：∀ (M₀ : Type u_1) [inst : MulZer
oClass M₀] [IsRightCancelMulZero M₀], NoZeroDivisors M₀
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `Nat.mul_eq_right`：∀ {b a : ℕ}, b ≠ 0 → (a * b = b ↔ a = 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Nat.le_mul_of_pos_left`：∀ {n : ℕ} (m : ℕ), 0 < n → m ≤ n * m
-/
theorem prime_iff_not_exists_mul_eq {p : ℕ} :
    p.Prime ↔ 2 ≤ p ∧ ¬ ∃ m n, m < p ∧ n < p ∧ m * n = p := by
  push Not
  simp_rw [prime_def_lt, dvd_def, exists_imp]
  refine and_congr_right fun hp ↦ forall_congr' fun m ↦ (forall_congr' fun h ↦ ?_).trans forall_comm
  simp_rw [Ne, forall_comm (β := _ = _), eq_comm, imp_false, not_lt]
  refine forall₂_congr fun n hp ↦ ⟨by simp_all, fun hpn ↦ ?_⟩
  have := mul_ne_zero_iff.mp (hp ▸ show p ≠ 0 by lia)
  exact (Nat.mul_eq_right (by lia)).mp
    (hp.symm.trans (hpn.antisymm (hp ▸ Nat.le_mul_of_pos_left _ (by lia))))
/-
**Nat.prime_of_coprime** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：prime_of_coprime (n : Nat) (h1 : 1 < n) (h : forall m < n, m != 0 -> n.Cop
rime m) : Prime n
参数：n : Nat；h1 : 1 < n；h : forall m < n, m != 0 -> n.Coprime m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.prime_def_lt`：prime_def_lt {p : Nat} : Prime p ↔ 2 <= p ∧ forall m <
 p, m ∣ p -> m = 1
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_dvd_iff`：zero_dvd_iff : 0 ∣ a ↔ a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.Coprime.eq_one_of_dvd`：∀ {k m : ℕ}, k.Coprime m → k ∣ m → k = 1
· 使用定理 `Nat.Coprime.symm`：∀ {n m : ℕ}, n.Coprime m → m.Coprime n
-/
theorem prime_of_coprime (n : ℕ) (h1 : 1 < n) (h : ∀ m < n, m ≠ 0 → n.Coprime m) : Prime n := by
  refine prime_def_lt.mpr ⟨h1, fun m mlt mdvd => ?_⟩
  have hm : m ≠ 0 := by
    rintro rfl
    rw [zero_dvd_iff] at mdvd
    exact mlt.ne' mdvd
  exact (h m mlt hm).symm.eq_one_of_dvd mdvd

/--
This instance is set up to work in the kernel (`by decide`) for small values.

Below (`decidablePrime'`) we will define a faster variant to be used by the compiler
(e.g. in `#eval` or `by native_decide`).

If you need to prove that a particular number is prime, in any case
you should not use `by decide`, but rather `by norm_num`, which is
much faster.
-/
/-
**Nat.decidablePrime** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
形式化陈述：decidablePrime (p : Nat) : Decidable (Prime p)
参数：p : Nat。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.prime_def_lt'`：prime_def_lt' {p : Nat} : Prime p ↔ 2 <= p ∧ forall m
, 2 <= m -> m < p -> ¬m ∣ p

--- 原说明 ---
This instance is set up to work in the kernel (`by decide`) for small values.

Below (`decidablePrime'`) we will define a faster variant to be used by the comp
iler
(e.g. in `#eval` or `by native_decide`).

If you need to prove that a particular number is prime, in any case
you should not use `by decide`, but rather `by norm_num`, which is
much faster.
-/
instance decidablePrime (p : ℕ) : Decidable (Prime p) :=
  decidable_of_iff' _ prime_def_lt'

/-!
### Specific small primes

It is recommended not to add further lemmas to this list; instead, import
`Mathlib.Tactic.NormNum.Prime` in downstream files and use `norm_num` for primality proofs.
-/
/-
**Nat.prime_two** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：prime_two : Prime 2
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p

--- 原说明 ---
### Specific small primes

It is recommended not to add further lemmas to this list; instead, import
`Mathlib.Tactic.NormNum.Prime` in downstream files and use `norm_num` for primal
ity proofs.
-/
theorem prime_two : Prime 2 := by decide
/-
**Nat.prime_three** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：prime_three : Prime 3
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem prime_three : Prime 3 := by decide
/-
**Nat.prime_five** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：prime_five : Prime 5
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem prime_five : Prime 5 := by decide
/-
**Nat.prime_seven** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：prime_seven : Prime 7
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem prime_seven : Prime 7 := by decide
/-
**Nat.prime_eleven** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：prime_eleven : Prime 11
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem prime_eleven : Prime 11 := by decide
/-
**Nat.dvd_prime** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：dvd_prime {p m : Nat} (pp : Prime p) : m ∣ p ↔ m = 1 ∨ m = p
参数：pp : Prime p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Prime.eq_one_or_self_of_dvd`：∀ {p : ℕ}, Nat.Prime p → ∀ (m : ℕ), m ∣
 p → m = 1 ∨ m = p
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `one_dvd`：one_dvd (a : α) : 1 ∣ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dvd_rfl`：dvd_rfl : forall {a : α}, a ∣ a
-/
theorem dvd_prime {p m : ℕ} (pp : Prime p) : m ∣ p ↔ m = 1 ∨ m = p :=
  ⟨fun d => pp.eq_one_or_self_of_dvd m d, fun h =>
    h.elim (fun e => e.symm ▸ one_dvd _) fun e => e.symm ▸ dvd_rfl⟩
/-
**Nat.dvd_prime_two_le** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：dvd_prime_two_le {p m : Nat} (pp : Prime p) (H : 2 <= m) : m ∣ p ↔ m = p
参数：pp : Prime p；H : 2 <= m。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Nat.dvd_prime`：dvd_prime {p m : Nat} (pp : Prime p) : m ∣ p ↔ m = 1 ∨ m 
= p
· 使用定理 `or_iff_right_of_imp`：∀ {a b : Prop}, (a → b) → (a ∨ b ↔ b)
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
theorem dvd_prime_two_le {p m : ℕ} (pp : Prime p) (H : 2 ≤ m) : m ∣ p ↔ m = p :=
  (dvd_prime pp).trans <| or_iff_right_of_imp <| Not.elim <| ne_of_gt H
/-
**Nat.prime_dvd_prime_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：prime_dvd_prime_iff_eq {p q : Nat} (pp : p.Prime) (qp : q.Prime) : p ∣ q ↔
 p = q
参数：pp : p.Prime；qp : q.Prime。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.dvd_prime_two_le`：dvd_prime_two_le {p m : Nat} (pp : Prime p) (H : 2
 <= m) : m ∣ p ↔ m = p
· 使用定理 `Nat.Prime.two_le`：∀ {p : ℕ}, Nat.Prime p → 2 ≤ p
-/
theorem prime_dvd_prime_iff_eq {p q : ℕ} (pp : p.Prime) (qp : q.Prime) : p ∣ q ↔ p = q :=
  dvd_prime_two_le qp (Prime.two_le pp)
/-
**Nat.Prime.not_dvd_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：∀ {p : ℕ}, Nat.Prime p → ¬p ∣ 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irreducible.not_dvd_one`：Irreducible.not_dvd_one [CommMonoid M] {p : M} 
(hp : Irreducible p) : ¬p ∣ 1
-/
theorem Prime.not_dvd_one {p : ℕ} (pp : Prime p) : ¬p ∣ 1 :=
  Irreducible.not_dvd_one pp

section MinFac

/-
**Nat.minFac_lemma** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：minFac_lemma (n k : Nat) (h : ¬n < k * k) : sqrt n - k < sqrt n + 2 - k
参数：n k : Nat；h : ¬n < k * k。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.sub_lt_sub_right`：∀ {a b c : ℕ}, c ≤ a → a < b → a - c < b - c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Nat.le_sqrt`：le_sqrt : m <= sqrt n ↔ m * m <= n
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Nat.lt_add_of_pos_right`：∀ {k n : ℕ}, 0 < k → n < n + k
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem minFac_lemma (n k : ℕ) (h : ¬n < k * k) : sqrt n - k < sqrt n + 2 - k :=
  (Nat.sub_lt_sub_right <| le_sqrt.2 <| le_of_not_gt h) <| Nat.lt_add_of_pos_right (by decide)

/--
If `n < k * k`, then `minFacAux n k = n`, if `k | n`, then `minFacAux n k = k`.
Otherwise, `minFacAux n k = minFacAux n (k+2)` using well-founded recursion.
If `n` is odd and `1 < n`, then `minFacAux n 3` is the smallest prime factor of `n`.

This definition is by well-founded recursion, so `rfl` or `decide` cannot be used.
One can use `norm_num` to prove `Nat.prime n` for small `n`.
-/
/-
**Nat.minFacAux** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：ℕ → ℕ → ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `n < k * k`, then `minFacAux n k = n`, if `k | n`, then `minFacAux n k = k`.
Otherwise, `minFacAux n k = minFacAux n (k+2)` using well-founded recursion.
If `n` is odd and `1 < n`, then `minFacAux n 3` is the smallest prime factor of 
`n`.

This definition is by well-founded recursion, so `rfl` or `decide` cannot be use
d.
One can use `norm_num` to prove `Nat.prime n` for small `n`.
-/
def minFacAux (n : ℕ) : ℕ → ℕ
  | k =>
    if n < k * k then n
    else
      if k ∣ n then k
      else
        minFacAux n (k + 2)
termination_by k => sqrt n + 2 - k
decreasing_by simp_wf; apply minFac_lemma n k; assumption

/-- Returns the smallest prime factor of `n ≠ 1`. -/
/-
**Nat.minFac** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：minFac (n : Nat) : Nat
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Returns the smallest prime factor of `n ≠ 1`.
-/
def minFac (n : ℕ) : ℕ :=
  if 2 ∣ n then 2 else minFacAux n 3

@[simp]
/-
**Nat.minFac_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：minFac_zero : minFac 0 = 2
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem minFac_zero : minFac 0 = 2 :=
  rfl

@[simp]
/-
**Nat.minFac_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：minFac_one : minFac 1 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Nat.minFacAux.eq_1`：∀ (n x : ℕ), n.minFacAux x = if n < x * x then n els
e if x ∣ n then x else n.minFacAux (x + 2)
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true_of_decide`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem minFac_one : minFac 1 = 1 := by
  simp [minFac, minFacAux]

@[simp]
/-
**Nat.minFac_two** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：minFac_two : minFac 2 = 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem minFac_two : minFac 2 = 2 := by
  simp [minFac]
/-
**Nat.minFac_eq** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：minFac_eq (n : Nat) : minFac n = if 2 ∣ n then 2 else minFacAux n 3
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem minFac_eq (n : ℕ) : minFac n = if 2 ∣ n then 2 else minFacAux n 3 := rfl

set_option backward.privateInPublic true in
/-
**Nat.minFacProp** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def minFacProp (n k : ℕ) :=
  2 ≤ k ∧ k ∣ n ∧ ∀ m, 2 ≤ m → m ∣ n → k ≤ m

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**Nat.minFacAux_has_prop** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：minFacAux_has_prop {n : Nat} (n2 : 2 <= n) : forall k i, k = 2 * i + 3 -> 
(forall m, 2 <= m -> m ∣ n -> k <= m) -> minFacProp n (minFacAux n k) | k => fun
 i e a => by rw [minFacAux] by_cases h : n < k * k · have pp : Prime n
参数：n2 : 2 <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.minFacAux.eq_1`：∀ (n x : ℕ), n.minFacAux x = if n < x * x then n els
e if x ∣ n then x else n.minFacAux (x + 2)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.prime_def_le_sqrt`：prime_def_le_sqrt {p : Nat} : Prime p ↔ 2 <= p ∧ 
forall m, 2 <= m -> m <= sqrt p -> ¬m ∣ p
· 使用定理 `not_lt_of_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用引理 `Nat.sqrt_lt`：sqrt_lt : sqrt m < n ↔ m < n * n
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `dvd_rfl`：dvd_rfl : forall {a : α}, a ∣ a
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.dvd_prime_two_le`：dvd_prime_two_le {p m : Nat} (pp : Prime p) (H : 2
 <= m) : m ∣ p ↔ m = p
· 使用定理 `Nat.le_add_left`：∀ (n m : ℕ), n ≤ m + n
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `Nat.minFac_lemma`：minFac_lemma (n k : Nat) (h : ¬n < k * k) : sqrt n - k
 < sqrt n + 2 - k
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.Simproc.add_sub_add_le`：∀ (a c : ℕ) {b d : ℕ}, b ≤ d → a + b - (c + 
d) = a - (c + (d - b))
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_right_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G)
, a + b + c = a + c + b
· 使用定理 `Nat.left_distrib`：∀ (n m k : ℕ), n * (m + k) = n * m + n * k
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.eq_or_lt_of_le`：∀ {n m : ℕ}, n ≤ m → n = m ∨ n < m
（共 34 条，此处仅展示前 30 条）
-/
theorem minFacAux_has_prop {n : ℕ} (n2 : 2 ≤ n) :
    ∀ k i, k = 2 * i + 3 → (∀ m, 2 ≤ m → m ∣ n → k ≤ m) → minFacProp n (minFacAux n k)
  | k => fun i e a => by
    rw [minFacAux]
    by_cases h : n < k * k
    · have pp : Prime n :=
        prime_def_le_sqrt.2
          ⟨n2, fun m m2 l d => not_lt_of_ge l <| lt_of_lt_of_le (sqrt_lt.2 h) (a m m2 d)⟩
      simpa only [k, h] using
        ⟨n2, dvd_rfl, fun m m2 d => le_of_eq ((dvd_prime_two_le pp m2).1 d).symm⟩
    have k2 : 2 ≤ k := by
      subst e
      apply Nat.le_add_left
    simp only [k, h, ↓reduceIte]
    by_cases dk : k ∣ n <;> simp only [k, dk, ↓reduceIte]
    · exact ⟨k2, dk, a⟩
    · refine
        have := minFac_lemma n k h
        minFacAux_has_prop n2 (k + 2) (i + 1) (by simp [k, e, Nat.left_distrib, add_right_comm])
          fun m m2 d => ?_
      rcases Nat.eq_or_lt_of_le (a m m2 d) with rfl | ml
      · contradiction
      apply (Nat.eq_or_lt_of_le ml).resolve_left
      intro me
      rw [← me, e] at d
      have d' : 2 * (i + 2) ∣ n := d
      have := a _ le_rfl (dvd_of_mul_right_dvd d')
      rw [e] at this
      exact absurd this (by contradiction)
  termination_by k => sqrt n + 2 - k

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**Nat.minFac_has_prop** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：minFac_has_prop {n : Nat} (n1 : n != 1) : minFacProp n (minFac n)
参数：n1 : n != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Std.instReflLeOfIsPreorder`：∀ {α : Type u} [inst : LE α] [Std.IsPreorder
 α], Std.Refl fun x1 x2 => x1 ≤ x2
· 使用定理 `Lean.Grind.instIsPreorderNat`：Std.IsPreorder ℕ
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Nat.le_zero_eq`：∀ (a : ℕ), (a ≤ 0) = (a = 0)
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_false_of_decide`：∀ {p : Prop} {x : Decidable p}, decide p = false → p
 = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Nat.minFacAux_has_prop`：minFacAux_has_prop {n : Nat} (n2 : 2 <= n) : for
all k i, k = 2 * i + 3 -> (forall m, 2 <= m -> m ∣ n -> k <= m) -> minFacProp n 
(minFacAux n…
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Nat.eq_or_lt_of_le`：∀ {n m : ℕ}, n ≤ m → n = m ∨ n < m
（共 32 条，此处仅展示前 30 条）
-/
theorem minFac_has_prop {n : ℕ} (n1 : n ≠ 1) : minFacProp n (minFac n) := by
  by_cases n0 : n = 0
  · simp [n0, minFacProp]
  have n2 : 2 ≤ n := by
    revert n0 n1
    rcases n with (_ | _ | _) <;> simp [succ_le_succ]
  simp only [minFac_eq]
  by_cases d2 : 2 ∣ n <;> simp only [d2, ↓reduceIte]
  · exact ⟨le_rfl, d2, fun k k2 _ => k2⟩
  · refine
      minFacAux_has_prop n2 3 0 rfl fun m m2 d => (Nat.eq_or_lt_of_le m2).resolve_left (mt ?_ d2)
    exact fun e => e.symm ▸ d
/-
**Nat.minFac_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：minFac_dvd (n : Nat) : minFac n ∣ n
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.minFac_one`：minFac_one : minFac 1 = 1
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Nat.minFac_has_prop`：minFac_has_prop {n : Nat} (n1 : n != 1) : minFacPro
p n (minFac n)
-/
theorem minFac_dvd (n : ℕ) : minFac n ∣ n :=
  if n1 : n = 1 then by simp [n1] else (minFac_has_prop n1).2.1
/-
**Nat.minFac_prime** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：minFac_prime {n : Nat} (n1 : n != 1) : Prime (minFac n)
参数：n1 : n != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.minFac_has_prop`：minFac_has_prop {n : Nat} (n1 : n != 1) : minFacPro
p n (minFac n)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.prime_def_lt'`：prime_def_lt' {p : Nat} : Prime p ↔ 2 <= p ∧ forall m
, 2 <= m -> m < p -> ¬m ∣ p
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
-/
theorem minFac_prime {n : ℕ} (n1 : n ≠ 1) : Prime (minFac n) :=
  let ⟨f2, fd, a⟩ := minFac_has_prop n1
  prime_def_lt'.2 ⟨f2, fun m m2 l d => not_le_of_gt l (a m m2 (d.trans fd))⟩

@[simp]
/-
**Nat.minFac_prime_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：minFac_prime_iff {n : Nat} : Prime (minFac n) ↔ n != 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.minFac_one`：minFac_one : minFac 1 = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.minFac_prime`：minFac_prime {n : Nat} (n1 : n != 1) : Prime (minFac n
)
-/
theorem minFac_prime_iff {n : ℕ} : Prime (minFac n) ↔ n ≠ 1 := by
  refine ⟨?_, minFac_prime⟩
  rintro h rfl
  simp only [minFac_one, not_prime_one] at h
/-
**Nat.minFac_le_of_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：minFac_le_of_dvd {n : Nat} : forall {m : Nat}, 2 <= m -> m ∣ n -> minFac n
 <= m
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.minFac_one`：minFac_one : minFac 1 = 1
· 使用定理 `eq_true_of_decide`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Nat.minFac_has_prop`：minFac_has_prop {n : Nat} (n1 : n != 1) : minFacPro
p n (minFac n)
-/
theorem minFac_le_of_dvd {n : ℕ} : ∀ {m : ℕ}, 2 ≤ m → m ∣ n → minFac n ≤ m := by
  by_cases n1 : n = 1
  · exact fun m2 _ => n1.symm ▸ le_trans (by simp) m2
  · apply (minFac_has_prop n1).2.2
/-
**Nat.minFac_pos** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：minFac_pos (n : Nat) : 0 < minFac n
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.minFac_one`：minFac_one : minFac 1 = 1
· 使用定理 `Nat.Prime.pos`：∀ {p : ℕ}, Nat.Prime p → 0 < p
· 使用定理 `Nat.minFac_prime`：minFac_prime {n : Nat} (n1 : n != 1) : Prime (minFac n
)
-/
theorem minFac_pos (n : ℕ) : 0 < minFac n := by
  by_cases n1 : n = 1
  · simp [n1]
  · exact (minFac_prime n1).pos
/-
**Nat.minFac_le** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：minFac_le {n : Nat} (H : 0 < n) : minFac n <= n
参数：H : 0 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
· 使用定理 `Nat.minFac_dvd`：minFac_dvd (n : Nat) : minFac n ∣ n
-/
theorem minFac_le {n : ℕ} (H : 0 < n) : minFac n ≤ n :=
  le_of_dvd H (minFac_dvd n)
/-
**Nat.le_minFac** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：le_minFac {m n : Nat} : n = 1 ∨ m <= minFac n ↔ forall p, Prime p -> p ∣ n
 -> m <= p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Nat.Prime.not_dvd_one`：∀ {p : ℕ}, Nat.Prime p → ¬p ∣ 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Nat.minFac_le_of_dvd`：minFac_le_of_dvd {n : Nat} : forall {m : Nat}, 2 <
= m -> m ∣ n -> minFac n <= m
· 使用定理 `Nat.Prime.two_le`：∀ {p : ℕ}, Nat.Prime p → 2 ≤ p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Nat.minFac_prime`：minFac_prime {n : Nat} (n1 : n != 1) : Prime (minFac n
)
· 使用定理 `Nat.minFac_dvd`：minFac_dvd (n : Nat) : minFac n ∣ n
-/
theorem le_minFac {m n : ℕ} : n = 1 ∨ m ≤ minFac n ↔ ∀ p, Prime p → p ∣ n → m ≤ p :=
  ⟨fun h p pp d =>
    h.elim (by rintro rfl; cases pp.not_dvd_one d) fun h =>
      le_trans h <| minFac_le_of_dvd pp.two_le d,
    fun H => or_iff_not_imp_left.2 fun n1 => H _ (minFac_prime n1) (minFac_dvd _)⟩
/-
**Nat.le_minFac'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：le_minFac' {m n : Nat} : n = 1 ∨ m <= minFac n ↔ forall p, 2 <= p -> p ∣ n
 -> m <= p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Nat.minFac_le_of_dvd`：minFac_le_of_dvd {n : Nat} : forall {m : Nat}, 2 <
= m -> m ∣ n -> minFac n <= m
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.le_minFac`：le_minFac {m n : Nat} : n = 1 ∨ m <= minFac n ↔ forall p,
 Prime p -> p ∣ n -> m <= p
· 使用定理 `Nat.Prime.two_le`：∀ {p : ℕ}, Nat.Prime p → 2 ≤ p
-/
theorem le_minFac' {m n : ℕ} : n = 1 ∨ m ≤ minFac n ↔ ∀ p, 2 ≤ p → p ∣ n → m ≤ p :=
  ⟨fun h p (pp : 1 < p) d =>
    h.elim (by rintro rfl; cases not_le_of_gt pp (le_of_dvd (by decide) d)) fun h =>
      le_trans h <| minFac_le_of_dvd pp d,
    fun H => le_minFac.2 fun p pp d => H p pp.two_le d⟩
/-
**Nat.prime_def_minFac** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：prime_def_minFac {p : Nat} : Prime p ↔ 2 <= p ∧ minFac p = p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Prime.two_le`：∀ {p : ℕ}, Nat.Prime p → 2 ≤ p
· 使用定理 `Nat.minFac_has_prop`：minFac_has_prop {n : Nat} (n1 : n != 1) : minFacPro
p n (minFac n)
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.dvd_prime`：dvd_prime {p m : Nat} (pp : Prime p) : m ∣ p ↔ m = 1 ∨ m 
= p
· 使用定理 `Nat.minFac_prime`：minFac_prime {n : Nat} (n1 : n != 1) : Prime (minFac n
)
-/
theorem prime_def_minFac {p : ℕ} : Prime p ↔ 2 ≤ p ∧ minFac p = p :=
  ⟨fun pp =>
    ⟨pp.two_le,
      let ⟨f2, fd, _⟩ := minFac_has_prop <| ne_of_gt pp.one_lt
      ((dvd_prime pp).1 fd).resolve_left (ne_of_gt f2)⟩,
    fun ⟨p2, e⟩ => e ▸ minFac_prime (ne_of_gt p2)⟩

@[simp]
/-
**Nat.Prime.minFac_eq** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：∀ {p : ℕ}, Nat.Prime p → p.minFac = p
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.prime_def_minFac`：prime_def_minFac {p : Nat} : Prime p ↔ 2 <= p ∧ mi
nFac p = p
-/
theorem Prime.minFac_eq {p : ℕ} (hp : Prime p) : minFac p = p :=
  (prime_def_minFac.1 hp).2

/--
This definition is faster in the virtual machine than `decidablePrime`,
but slower in the kernel.
-/
/-
**Nat.decidablePrime'** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：decidablePrime' (p : Nat) : Decidable (Prime p)
参数：p : Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.prime_def_minFac`：prime_def_minFac {p : Nat} : Prime p ↔ 2 <= p ∧ mi
nFac p = p

--- 原说明 ---
This definition is faster in the virtual machine than `decidablePrime`,
but slower in the kernel.
-/
def decidablePrime' (p : ℕ) : Decidable (Prime p) :=
  decidable_of_iff' _ prime_def_minFac
/-
**Nat.decidablePrime_csimp** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：Nat.decidablePrime = Nat.decidablePrime'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
-/
@[csimp] theorem decidablePrime_csimp :
    @decidablePrime = @decidablePrime' := by
  subsingleton
/-
**Nat.not_prime_iff_minFac_lt** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：not_prime_iff_minFac_lt {n : Nat} (n2 : 2 <= n) : ¬Prime n ↔ minFac n < n
参数：n2 : 2 <= n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Nat.prime_def_minFac`：prime_def_minFac {p : Nat} : Prime p ↔ 2 <= p ∧ mi
nFac p = p
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `lt_iff_le_and_ne`：lt_iff_le_and_ne : a < b ↔ a <= b ∧ a != b
· 使用定理 `Nat.minFac_le`：minFac_le {n : Nat} (H : 0 < n) : minFac n <= n
· 使用定理 `Nat.le_of_succ_le`：∀ {n m : ℕ}, n.succ ≤ m → n ≤ m
-/
theorem not_prime_iff_minFac_lt {n : ℕ} (n2 : 2 ≤ n) : ¬Prime n ↔ minFac n < n :=
  (not_congr <| prime_def_minFac.trans <| and_iff_right n2).trans <|
    (lt_iff_le_and_ne.trans <| and_iff_right <| minFac_le <| le_of_succ_le n2).symm
/-
**Nat.minFac_le_div** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：minFac_le_div {n : Nat} (pos : 0 < n) (np : ¬Prime n) : minFac n <= n / mi
nFac n
参数：pos : 0 < n；np : ¬Prime n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.minFac_dvd`：minFac_dvd (n : Nat) : minFac n ∣ n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Nat.le_of_lt_succ`：∀ {m n : ℕ}, m < n.succ → m ≤ n
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `not_true`：¬True ↔ False
· 使用定理 `eq_self_iff_true`：∀ {α : Sort u_1} (a : α), a = a ↔ True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `not_and_or`：not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b
· 使用定理 `Nat.prime_def_minFac`：prime_def_minFac {p : Nat} : Prime p ↔ 2 <= p ∧ mi
nFac p = p
· 使用定理 `Nat.succ_le_of_lt`：∀ {n m : ℕ}, n < m → n.succ ≤ m
· 使用定理 `Nat.minFac_one`：minFac_one : minFac 1 = 1
· 使用定理 `Nat.div_one`：∀ (n : ℕ), n / 1 = n
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.mul_div_cancel_left`：∀ (m : ℕ) {n : ℕ}, 0 < n → n * m / n = m
· 使用定理 `Nat.minFac_pos`：minFac_pos (n : Nat) : 0 < minFac n
· 使用定理 `Nat.minFac_le_of_dvd`：minFac_le_of_dvd {n : Nat} : forall {m : Nat}, 2 <
= m -> m ∣ n -> minFac n <= m
· 使用定理 `Nat.le_add_left`：∀ (n m : ℕ), n ≤ m + n
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem minFac_le_div {n : ℕ} (pos : 0 < n) (np : ¬Prime n) : minFac n ≤ n / minFac n :=
  match minFac_dvd n with
  | ⟨0, h0⟩ => absurd pos <| by rw [h0, mul_zero]; decide
  | ⟨1, h1⟩ => by
    rw [mul_one] at h1
    rw [prime_def_minFac, not_and_or, ← h1, eq_self_iff_true, _root_.not_true, _root_.or_false,
      not_le] at np
    rw [le_antisymm (le_of_lt_succ np) (succ_le_of_lt pos), minFac_one, Nat.div_one]
  | ⟨x + 2, hx⟩ => by
    conv_rhs =>
      congr
      rw [hx]
    rw [Nat.mul_div_cancel_left _ (minFac_pos _)]
    exact minFac_le_of_dvd (le_add_left 2 x) ⟨minFac n, by rwa [mul_comm]⟩

/-- The square of the smallest prime factor of a composite number `n` is at most `n`.
-/
/-
**Nat.minFac_sq_le_self** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：minFac_sq_le_self {n : Nat} (w : 0 < n) (h : ¬Prime n) : minFac n ^ 2 <= n
参数：w : 0 < n；h : ¬Prime n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.minFac_le_div`：minFac_le_div {n : Nat} (pos : 0 < n) (np : ¬Prime n)
 : minFac n <= n / minFac n
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Nat.mul_le_mul_right`：∀ {n m : ℕ} (k : ℕ), n ≤ m → n * k ≤ m * k
· 使用定理 `Nat.div_mul_le_self`：∀ (m n : ℕ), m / n * n ≤ m

--- 原说明 ---
The square of the smallest prime factor of a composite number `n` is at most `n`
.
-/
theorem minFac_sq_le_self {n : ℕ} (w : 0 < n) (h : ¬Prime n) : minFac n ^ 2 ≤ n :=
  have t : minFac n ≤ n / minFac n := minFac_le_div w h
  calc
    minFac n ^ 2 = minFac n * minFac n := sq (minFac n)
    _ ≤ n / minFac n * minFac n := Nat.mul_le_mul_right (minFac n) t
    _ ≤ n := div_mul_le_self n (minFac n)

@[simp]
/-
**Nat.minFac_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：minFac_eq_one_iff {n : Nat} : minFac n = 1 ↔ n = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Nat.minFac_prime`：minFac_prime {n : Nat} (n1 : n != 1) : Prime (minFac n
)
· 使用定理 `Nat.not_prime_one`：¬Nat.Prime 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Nat.minFacAux.eq_1`：∀ (n x : ℕ), n.minFacAux x = if n < x * x then n els
e if x ∣ n then x else n.minFacAux (x + 2)
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true_of_decide`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem minFac_eq_one_iff {n : ℕ} : minFac n = 1 ↔ n = 1 := by
  constructor
  · intro h
    by_contra hn
    have := minFac_prime hn
    rw [h] at this
    exact not_prime_one this
  · rintro rfl
    simp [minFac, minFacAux]

@[simp]
/-
**Nat.minFac_eq_two_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：minFac_eq_two_iff (n : Nat) : minFac n = 2 ↔ 2 ∣ n
参数：n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.minFac_dvd`：minFac_dvd (n : Nat) : minFac n ∣ n
· 使用定理 `Nat.minFac_le_of_dvd`：minFac_le_of_dvd {n : Nat} : forall {m : Nat}, 2 <
= m -> m ∣ n -> minFac n <= m
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Nat.minFac_pos`：minFac_pos (n : Nat) : 0 < minFac n
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Nat.succ_le_of_lt`：∀ {n m : ℕ}, n < m → n.succ ≤ m
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.lt_succ_iff`：∀ {m n : ℕ}, m < n.succ ↔ m ≤ n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem minFac_eq_two_iff (n : ℕ) : minFac n = 2 ↔ 2 ∣ n := by
  constructor
  · intro h
    rw [← h]
    exact minFac_dvd n
  · intro h
    have ub := minFac_le_of_dvd (le_refl 2) h
    have lb := minFac_pos n
    refine ub.eq_or_lt.resolve_right fun h' => ?_
    suffices n.minFac = 1 by simp_all
    exact (le_antisymm (Nat.succ_le_of_lt lb) (Nat.lt_succ_iff.mp h')).symm
/-
**Nat.factors_lemma** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：factors_lemma {k} : (k + 2) / minFac (k + 2) < k + 2
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.div_lt_self`：∀ {n k : ℕ}, 0 < n → 1 < k → n / k < n
· 使用定理 `Nat.zero_lt_succ`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `Nat.minFac_prime`：minFac_prime {n : Nat} (n1 : n != 1) : Prime (minFac n
)
· 使用定理 `Nat.ne_of_gt`：∀ {a b : ℕ}, b < a → a ≠ b
· 使用定理 `Nat.succ_lt_succ`：∀ {n m : ℕ}, n < m → n.succ < m.succ
-/
theorem factors_lemma {k} : (k + 2) / minFac (k + 2) < k + 2 :=
  div_lt_self (Nat.zero_lt_succ _) (minFac_prime (by
      apply Nat.ne_of_gt
      apply Nat.succ_lt_succ
      apply Nat.zero_lt_succ)).one_lt

end MinFac

/-
**Nat.exists_prime_and_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：exists_prime_and_dvd {n : Nat} (hn : n != 1) : exists p, Prime p ∧ p ∣ n
参数：hn : n != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.minFac_prime`：minFac_prime {n : Nat} (n1 : n != 1) : Prime (minFac n
)
· 使用定理 `Nat.minFac_dvd`：minFac_dvd (n : Nat) : minFac n ∣ n
-/
theorem exists_prime_and_dvd {n : ℕ} (hn : n ≠ 1) : ∃ p, Prime p ∧ p ∣ n :=
  ⟨minFac n, minFac_prime hn, minFac_dvd _⟩
/-
**Nat.coprime_of_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：coprime_of_dvd {m n : Nat} (H : forall k, Prime k -> k ∣ m -> ¬k ∣ n) : Co
prime m n
参数：H : forall k, Prime k -> k ∣ m -> ¬k ∣ n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.coprime_iff_gcd_eq_one`：∀ {m n : ℕ}, m.Coprime n ↔ m.gcd n = 1
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Nat.exists_prime_and_dvd`：exists_prime_and_dvd {n : Nat} (hn : n != 1) :
 exists p, Prime p ∧ p ∣ n
· 使用定理 `dvd_trans`：dvd_trans : a ∣ b -> b ∣ c -> a ∣ c | ⟨d, h₁⟩, ⟨e, h₂⟩ => ⟨d 
* e, h₁ ▸ h₂.trans mul_assoc a d e⟩  alias Dvd.dvd.trans
· 使用定理 `Nat.gcd_dvd_left`：∀ (m n : ℕ), m.gcd n ∣ m
· 使用定理 `Nat.gcd_dvd_right`：∀ (m n : ℕ), m.gcd n ∣ n
-/
theorem coprime_of_dvd {m n : ℕ} (H : ∀ k, Prime k → k ∣ m → ¬k ∣ n) : Coprime m n := by
  rw [coprime_iff_gcd_eq_one]
  by_contra g2
  obtain ⟨p, hp, hpdvd⟩ := exists_prime_and_dvd g2
  apply H p hp <;> apply dvd_trans hpdvd
  · exact gcd_dvd_left _ _
  · exact gcd_dvd_right _ _
/-
**Nat.Prime.coprime_iff_not_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：∀ {p n : ℕ}, Nat.Prime p → (p.Coprime n ↔ ¬p ∣ n)
参数：p.Coprime n ↔ ¬p ∣ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Prime.not_dvd_one`：∀ {p : ℕ}, Nat.Prime p → ¬p ∣ 1
· 使用定理 `Nat.Coprime.dvd_of_dvd_mul_left`：∀ {k m n : ℕ}, k.Coprime m → k ∣ m * n 
→ k ∣ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Nat.coprime_of_dvd`：coprime_of_dvd {m n : Nat} (H : forall k, Prime k ->
 k ∣ m -> ¬k ∣ n) : Coprime m n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.prime_dvd_prime_iff_eq`：prime_dvd_prime_iff_eq {p q : Nat} (pp : p.P
rime) (qp : q.Prime) : p ∣ q ↔ p = q
-/
theorem Prime.coprime_iff_not_dvd {p n : ℕ} (pp : Prime p) : Coprime p n ↔ ¬p ∣ n :=
  ⟨fun co d => pp.not_dvd_one <| co.dvd_of_dvd_mul_left (by simp [d]), fun nd =>
    coprime_of_dvd fun _ m2 mp => ((prime_dvd_prime_iff_eq m2 pp).1 mp).symm ▸ nd⟩
/-
**Nat.Prime.dvd_mul** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：∀ {p m n : ℕ}, Nat.Prime p → (p ∣ m * n ↔ p ∣ m ∨ p ∣ n)
参数：p ∣ m * n ↔ p ∣ m ∨ p ∣ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Nat.Coprime.dvd_of_dvd_mul_left`：∀ {k m n : ℕ}, k.Coprime m → k ∣ m * n 
→ k ∣ n
· 使用定理 `Nat.Prime.coprime_iff_not_dvd`：∀ {p n : ℕ}, Nat.Prime p → (p.Coprime n ↔
 ¬p ∣ n)
· 使用定理 `Dvd.dvd.mul_right`：∀ {α : Type u_1} [inst : Semigroup α] {a b : α}, a ∣ 
b → ∀ (c : α), a ∣ b * c
· 使用定理 `Dvd.dvd.mul_left`：∀ {α : Type u_1} [inst : CommSemigroup α] {a b : α}, a
 ∣ b → ∀ (c : α), a ∣ c * b
-/
theorem Prime.dvd_mul {p m n : ℕ} (pp : Prime p) : p ∣ m * n ↔ p ∣ m ∨ p ∣ n :=
  ⟨fun H => or_iff_not_imp_left.2 fun h => (pp.coprime_iff_not_dvd.2 h).dvd_of_dvd_mul_left H,
    Or.rec (fun h : p ∣ m => h.mul_right _) fun h : p ∣ n => h.mul_left _⟩

alias ⟨Prime.dvd_or_dvd, _⟩ := Prime.dvd_mul
/-
**Nat.prime_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：prime_iff {p : Nat} : p.Prime ↔ _root_.Prime p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用定理 `Irreducible.not_isUnit`：∀ {M : Type u_1} [inst : Monoid M] {p : M}, Irre
ducible p → ¬IsUnit p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.Prime.dvd_mul`：∀ {p m n : ℕ}, Nat.Prime p → (p ∣ m * n ↔ p ∣ m ∨ p ∣
 n)
· 使用定理 `Prime.irreducible`：∀ {M : Type u_1} [inst : CommMonoidWithZero M] [IsCan
celMulZero M] {p : M}, Prime p → Irreducible p
-/
theorem prime_iff {p : ℕ} : p.Prime ↔ _root_.Prime p :=
  ⟨fun h => ⟨h.ne_zero, h.not_isUnit, fun _ _ => h.dvd_mul.mp⟩, Prime.irreducible⟩

alias ⟨Prime.prime, _root_.Prime.nat_prime⟩ := prime_iff
/-
**Nat.instDecidablePredPrime** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
形式化陈述：instDecidablePredPrime : DecidablePred (_root_.Prime : Nat -> Prop)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.prime_iff`：prime_iff {p : Nat} : p.Prime ↔ _root_.Prime p
-/
instance instDecidablePredPrime : DecidablePred (_root_.Prime : ℕ → Prop) := fun n ↦
  decidable_of_iff (Nat.Prime n) Nat.prime_iff
/-
**Nat.irreducible_iff_prime** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：irreducible_iff_prime {p : Nat} : Irreducible p ↔ _root_.Prime p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.prime_iff`：prime_iff {p : Nat} : p.Prime ↔ _root_.Prime p
-/
theorem irreducible_iff_prime {p : ℕ} : Irreducible p ↔ _root_.Prime p :=
  prime_iff
/-
**Nat.instDecidablePredIrreducible** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
形式化陈述：instDecidablePredIrreducible : DecidablePred (Irreducible : Nat -> Prop)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDecidablePredIrreducible : DecidablePred (Irreducible : ℕ → Prop) :=
  decidablePrime

/-- The type of prime numbers -/
/-
**Nat.Primes** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：Primes
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of prime numbers
-/
def Primes :=
  { p : ℕ // p.Prime }
  deriving DecidableEq

namespace Primes

/-
**Nat.Primes.** 是 Mathlib 中的一个实例，位于命名空间 `Nat.Primes`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Repr Nat.Primes :=
  ⟨fun p _ => repr p.val⟩
/-
**Nat.Primes.inhabitedPrimes** 是 Mathlib 中的一个实例，位于命名空间 `Nat.Primes`。
形式化陈述：inhabitedPrimes : Inhabited Primes
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.prime_two`：prime_two : Prime 2
-/
instance inhabitedPrimes : Inhabited Primes :=
  ⟨⟨2, prime_two⟩⟩
/-
**Nat.Primes.coeNat** 是 Mathlib 中的一个实例，位于命名空间 `Nat.Primes`。
形式化陈述：coeNat : Coe Nat.Primes Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance coeNat : Coe Nat.Primes ℕ :=
  ⟨Subtype.val⟩
/-
**Nat.Primes.coe_nat_injective** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Primes`。
形式化陈述：coe_nat_injective : Function.Injective ((↑) : Nat.Primes -> Nat)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
theorem coe_nat_injective : Function.Injective ((↑) : Nat.Primes → ℕ) :=
  Subtype.coe_injective
/-
**Nat.Primes.coe_nat_inj** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Primes`。
形式化陈述：coe_nat_inj (p q : Nat.Primes) : (p : Nat) = (q : Nat) ↔ p = q
参数：p q : Nat.Primes。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
-/
theorem coe_nat_inj (p q : Nat.Primes) : (p : ℕ) = (q : ℕ) ↔ p = q :=
  Subtype.ext_iff.symm

end Primes

/-
**Nat.monoid.primePow** 是 Mathlib 中的一个定义，位于命名空间 `Nat.monoid`。
形式化陈述：{α : Type u_1} → [Monoid α] → Pow α Nat.Primes
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance monoid.primePow {α : Type*} [Monoid α] : Pow α Primes :=
  ⟨fun x p => x ^ (p : ℕ)⟩
/-
**Nat.fact_prime_two** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
形式化陈述：fact_prime_two : Fact (Prime 2)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.prime_two`：prime_two : Prime 2
-/
instance fact_prime_two : Fact (Prime 2) :=
  ⟨prime_two⟩
/-
**Nat.fact_prime_three** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
形式化陈述：fact_prime_three : Fact (Prime 3)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.prime_three`：prime_three : Prime 3
-/
instance fact_prime_three : Fact (Prime 3) :=
  ⟨prime_three⟩

end Nat

