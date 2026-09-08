/-
Copyright (c) 2022 Pim Otte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Pim Otte
-/
module

public import Mathlib.Algebra.Order.Antidiag.Pi
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.List.ToFinsupp
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
/-!
# Multinomial

This file defines the multinomial coefficients and several small lemmas for manipulating them.

- `Nat.multinomial`: the multinomial coefficient,
  Given a function `f : α → ℕ` and `s : Finset α`, this is the number of strings
  consisting of symbols from `s`, where `c ∈ s` appears with multiplicity `f c`.

  It is defined as `(∑ i ∈ s, f i)! / ∏ i ∈ s, (f i)!`.

- `Multiset.countPerms`: multinomial coefficient associated with the `Multiset.count` function
  of a multiset. This is the number of lists that induce the given multiset.

- `Finset.sum_pow`: The expansion of `(s.sum x) ^ n` using multinomial coefficients

- `Multiset.multinomial`.
  Given a multiset `m` of natural numbers, `m.multinomial` is the
  multinomial coefficient defined by `(m.sum) ! / ∏ i ∈ m, m i !`.

This should not be confused with `m.countPerms` which
is defined as `m.toFinsupp.multinomial`.

As an example, one has `Multiset.multinomial {1, 2, 2} = 30`,
while `Multiset.countPerms {1, 2, 2} = 3`.

- `Multiset.multinomial_cons` proves that
  `(x ::ₘ m).multinomial = Nat.choose (x + m.sum) x * m.multinomial`
- `Multiset.multinomial_add` proves that
  `(m + m').multinomial = Nat.choose (m + m').sum m.sum * m.multinomial * m'.multinomial`

## Implementation note for `Multiset.multinomial`.

To avoid the definition of `Multiset.multinomial` as a quotient given above,
we define it in terms of `Finsupp.multinomial`, via lists:
If `m : Multiset ℕ` is the multiset associated with a list `l : List ℕ`,
then `m.multinomial = l.toFinsupp.multinomial`.
Then we prove its invariance under permutation.

-/

@[expose] public section

open Finset
open scoped Nat

namespace Nat

variable {α : Type*} (s : Finset α) (f : α → ℕ) {a b : α} (n : ℕ)

/-- The multinomial coefficient. Gives the number of strings consisting of symbols
from `s`, where `c ∈ s` appears with multiplicity `f c`.

Defined as `(∑ i ∈ s, f i)! / ∏ i ∈ s, (f i)!`.
-/
/-
**Nat.multinomial** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：multinomial : Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multinomial coefficient. Gives the number of strings consisting of symbols
from `s`, where `c ∈ s` appears with multiplicity `f c`.

Defined as `(∑ i ∈ s, f i)! / ∏ i ∈ s, (f i)!`.
-/
def multinomial : ℕ :=
  (∑ i ∈ s, f i)! / ∏ i ∈ s, (f i)!
/-
**Nat.multinomial_pos** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：multinomial_pos : 0 < multinomial s f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.div_pos`：∀ {b a : ℕ}, b ≤ a → 0 < b → 0 < a / b
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
· 使用定理 `Nat.factorial_pos`：∀ (n : ℕ), 0 < n.factorial
· 使用定理 `Nat.prod_factorial_dvd_factorial_sum`：prod_factorial_dvd_factorial_sum :
 (∏ i in s, (f i)!) ∣ (∑ i in s, f i)!
· 使用定理 `Nat.prod_factorial_pos`：prod_factorial_pos : 0 < ∏ i in s, (f i)!
-/
theorem multinomial_pos : 0 < multinomial s f :=
  Nat.div_pos (le_of_dvd (factorial_pos _) (prod_factorial_dvd_factorial_sum s f))
    (prod_factorial_pos s f)
/-
**Nat.multinomial_spec** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：multinomial_spec : (∏ i in s, (f i)!) * multinomial s f = (∑ i in s, f i)!
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.mul_div_cancel'`：∀ {n m : ℕ}, n ∣ m → n * (m / n) = m
· 使用定理 `Nat.prod_factorial_dvd_factorial_sum`：prod_factorial_dvd_factorial_sum :
 (∏ i in s, (f i)!) ∣ (∑ i in s, f i)!
-/
theorem multinomial_spec : (∏ i ∈ s, (f i)!) * multinomial s f = (∑ i ∈ s, f i)! :=
  Nat.mul_div_cancel' (prod_factorial_dvd_factorial_sum s f)
/-
**Nat.multinomial_empty** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {α : Type u_1} (f : α → ℕ), Nat.multinomial ∅ f = 1
参数：f : α → ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.div_self`：∀ {n : ℕ}, 0 < n → n / n = 1
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma multinomial_empty : multinomial ∅ f = 1 := by simp [multinomial]

variable {s f}
/-
**Nat.multinomial_cons** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：multinomial_cons (ha : a ∉ s) (f : α -> Nat) : multinomial (s.cons a ha) f
 = (f a + ∑ i in s, f i).choose (f a) * multinomial s f
参数：ha : a ∉ s；f : α -> Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.multinomial.eq_1`：∀ {α : Type u_1} (s : Finset α) (f : α → ℕ), Nat.m
ultinomial s f = (∑ i ∈ s, f i).factorial / ∏ i ∈ s, (f i).factorial
· 使用定理 `Nat.div_eq_iff_eq_mul_left`：∀ {a b c : ℕ}, 0 < b → b ∣ a → (a / b = c ↔ 
a = c * b)
· 使用引理 `Finset.prod_pos`：prod_pos (h0 : forall i in s, 0 < f i) : 0 < ∏ i in s, 
f i
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `Nat.factorial_pos`：∀ (n : ℕ), 0 < n.factorial
· 使用定理 `Nat.prod_factorial_dvd_factorial_sum`：prod_factorial_dvd_factorial_sum :
 (∏ i in s, (f i)!) ∣ (∑ i in s, f i)!
· 使用定理 `Finset.prod_cons`：prod_cons (h : a ∉ s) : ∏ x in cons a s h, f x = f a *
 ∏ x in s, f x
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `Nat.div_mul_cancel`：∀ {n m : ℕ}, n ∣ m → m / n * n = m
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.choose_symm_add`：choose_symm_add {a b : Nat} : choose (a + b) a = ch
oose (a + b) b
· 使用定理 `Nat.add_choose_mul_factorial_mul_factorial`：add_choose_mul_factorial_mul
_factorial (i j : Nat) : (i + j).choose j * i ! * j ! = (i + j)!
· 使用定理 `Finset.sum_cons`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι} 
[inst : AddCommMonoid M] {f : ι → M} (h : a ∉ s),   ∑ x ∈ Finset.cons a s h, f x
 = f …
-/
lemma multinomial_cons (ha : a ∉ s) (f : α → ℕ) :
    multinomial (s.cons a ha) f = (f a + ∑ i ∈ s, f i).choose (f a) * multinomial s f := by
  rw [multinomial, Nat.div_eq_iff_eq_mul_left _ (prod_factorial_dvd_factorial_sum _ _), prod_cons,
    multinomial, mul_assoc, mul_left_comm _ (f a)!,
    Nat.div_mul_cancel (prod_factorial_dvd_factorial_sum _ _), ← mul_assoc, Nat.choose_symm_add,
    Nat.add_choose_mul_factorial_mul_factorial, Finset.sum_cons]
  positivity
/-
**Nat.multinomial_insert** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：multinomial_insert [DecidableEq α] (ha : a ∉ s) (f : α -> Nat) : multinomi
al (insert a s) f = (f a + ∑ i in s, f i).choose (f a) * multinomial s f
参数：ha : a ∉ s；f : α -> Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.cons_eq_insert`：cons_eq_insert (a s h) : @cons α a s h = insert a
 s
· 使用引理 `Nat.multinomial_cons`：multinomial_cons (ha : a ∉ s) (f : α -> Nat) : mul
tinomial (s.cons a ha) f = (f a + ∑ i in s, f i).choose (f a) * multinomial s f
-/
lemma multinomial_insert [DecidableEq α] (ha : a ∉ s) (f : α → ℕ) :
    multinomial (insert a s) f = (f a + ∑ i ∈ s, f i).choose (f a) * multinomial s f := by
  rw [← cons_eq_insert _ _ ha, multinomial_cons]
/-
**Nat.multinomial_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {α : Type u_1} (a : α) (f : α → ℕ), Nat.multinomial {a} f = 1
参数：a : α；f : α → ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.notMem_empty`：notMem_empty (a : α) : a ∉ (∅ : Finset α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.cons_empty`：cons_empty (a : α) : cons a ∅ (notMem_empty _) = {a}
· 使用引理 `Nat.multinomial_cons`：multinomial_cons (ha : a ∉ s) (f : α -> Nat) : mul
tinomial (s.cons a ha) f = (f a + ∑ i in s, f i).choose (f a) * multinomial s f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Nat.choose_self`：choose_self (n : Nat) : choose n n = 1
· 使用定理 `Nat.multinomial_empty`：∀ {α : Type u_1} (f : α → ℕ), Nat.multinomial ∅ f
 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma multinomial_singleton (a : α) (f : α → ℕ) : multinomial {a} f = 1 := by
  rw [← cons_empty, multinomial_cons]; simp

@[simp]
/-
**Nat.multinomial_insert_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：multinomial_insert_one [DecidableEq α] (h : a ∉ s) (h₁ : f a = 1) : multin
omial (insert a s) f = (s.sum f).succ * multinomial s f
参数：h : a ∉ s；h₁ : f a = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.succ_eq_add_one`：∀ (n : ℕ), n.succ = n + 1
· 使用定理 `Nat.factorial_succ`：factorial_succ (n : Nat) : (n + 1)! = (n + 1) * n !
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Nat.mul_div_assoc`：∀ {k n : ℕ} (m : ℕ), k ∣ n → m * n / k = m * (n / k)
· 使用定理 `Nat.prod_factorial_dvd_factorial_sum`：prod_factorial_dvd_factorial_sum :
 (∏ i in s, (f i)!) ∣ (∑ i in s, f i)!
-/
theorem multinomial_insert_one [DecidableEq α] (h : a ∉ s) (h₁ : f a = 1) :
    multinomial (insert a s) f = (s.sum f).succ * multinomial s f := by
  simp only [multinomial]
  rw [Finset.sum_insert h, Finset.prod_insert h, h₁, add_comm, ← succ_eq_add_one, factorial_succ]
  simp only [factorial, succ_eq_add_one, zero_add, mul_one, one_mul]
  rw [Nat.mul_div_assoc _ (prod_factorial_dvd_factorial_sum _ _)]
/-
**Nat.multinomial_congr** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：multinomial_congr {f g : α -> Nat} (h : forall a in s, f a = g a) : multin
omial s f = multinomial s g
参数：h : forall a in s, f a = g a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
-/
theorem multinomial_congr {f g : α → ℕ} (h : ∀ a ∈ s, f a = g a) :
    multinomial s f = multinomial s g := by
  simp only [multinomial]; congr 1
  · rw [Finset.sum_congr rfl h]
  · exact Finset.prod_congr rfl fun a ha => by rw [h a ha]
/-
**Nat.multinomial_congr_of_eq_on_inter** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：multinomial_congr_of_eq_on_inter [DecidableEq α] {f g : α -> Nat} {s t : F
inset α} (hf : forall a in s \ t, f a = 0) (hg : forall a in t \ s, g a = 0) (hf
g : forall a in s inter t, f a = g a) : multinomial s f = multinomial t g
参数：hf : forall a in s \ t, f a = 0；hg : forall a in t \ s, g a = 0；hfg : forall 
a in s inter t, f a = g a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.mul_right_inj`：∀ {a b c : ℕ}, a ≠ 0 → (a * b = a * c ↔ b = c)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Finset.prod_ne_zero_iff`：prod_ne_zero_iff : ∏ x in s, f x != 0 ↔ forall 
a in s, f a != 0
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `Nat.factorial_ne_zero`：factorial_ne_zero (n : Nat) : n ! != 0
· 使用定理 `Nat.multinomial_spec`：multinomial_spec : (∏ i in s, (f i)!) * multinomia
l s f = (∑ i in s, f i)!
· 使用引理 `Finset.prod_congr_of_eq_on_inter`：prod_congr_of_eq_on_inter {ι M : Type*
} {s₁ s₂ : Finset ι} {f g : ι -> M} [CommMonoid M] (h₁ : forall a in s₁, a ∉ s₂ 
-> f a = 1) (h₂ : fora…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_congr_of_eq_on_inter`：∀ {ι : Type u_5} {M : Type u_6} {s₁ s₂ 
: Finset ι} {f g : ι → M} [inst : AddCommMonoid M],   (∀ a ∈ s₁, a ∉ s₂ → f a = 
0) →     (∀ a ∈ s₂, a…
-/
theorem multinomial_congr_of_eq_on_inter [DecidableEq α] {f g : α → ℕ} {s t : Finset α}
    (hf : ∀ a ∈ s \ t, f a = 0) (hg : ∀ a ∈ t \ s, g a = 0) (hfg : ∀ a ∈ s ∩ t, f a = g a) :
    multinomial s f = multinomial t g := by
  rw [← Nat.mul_right_inj (prod_ne_zero_iff.mpr (fun x _ ↦ factorial_ne_zero (g x))),
    multinomial_spec, prod_congr_of_eq_on_inter (g := fun a ↦ (f a)!) (s₂ := s) (by aesop)
    (by aesop) (by aesop), multinomial_spec s f]
  congr 1
  exact sum_congr_of_eq_on_inter (by grind) (by grind) (by grind)
/-
**Nat.multinomial_congr_of_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：multinomial_congr_of_sdiff [DecidableEq α] {f g : α -> Nat} {s t : Finset 
α} (hst : s subseteq t) (hg : forall a in t \ s, g a = 0) (hfg : forall a in s, 
f a = g a) : multinomial s f = multinomial t g
参数：hst : s subseteq t；hg : forall a in t \ s, g a = 0；hfg : forall a in s, f a =
 g a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.multinomial_congr_of_eq_on_inter`：multinomial_congr_of_eq_on_inter [
DecidableEq α] {f g : α -> Nat} {s t : Finset α} (hf : forall a in s \ t, f a = 
0) (hg : forall a in t \ s…
-/
theorem multinomial_congr_of_sdiff [DecidableEq α] {f g : α → ℕ} {s t : Finset α}
    (hst : s ⊆ t) (hg : ∀ a ∈ t \ s, g a = 0) (hfg : ∀ a ∈ s, f a = g a) :
    multinomial s f = multinomial t g :=
  multinomial_congr_of_eq_on_inter (by grind) hg (by grind)

variable (s a) in
/-
**Nat.multinomial_single** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：multinomial_single [DecidableEq α] : multinomial s (Pi.single a n) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.mul_right_inj`：∀ {a b c : ℕ}, a ≠ 0 → (a * b = a * c ↔ b = c)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Finset.prod_ne_zero_iff`：prod_ne_zero_iff : ∏ x in s, f x != 0 ↔ forall 
a in s, f a != 0
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `Nat.factorial_ne_zero`：factorial_ne_zero (n : Nat) : n ! != 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Nat.multinomial_spec`：multinomial_spec : (∏ i in s, (f i)!) * multinomia
l s f = (∑ i in s, f i)!
· 使用定理 `Finset.sum_pi_single'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMo
noid M] [inst_1 : DecidableEq ι] (a : ι) (x : M) (s : Finset ι),   ∑ a' ∈ s, Pi.
single a x …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Finset.prod_eq_single`：prod_eq_single {s : Finset ι} {f : ι -> M} (a : ι
) (h₀ : forall b in s, b != a -> f b = 1) (h₁ : a ∉ s -> f a = 1) : ∏ x in s, f 
x = f a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Nat.factorial_zero`：Nat.factorial 0 = 1
（共 33 条，此处仅展示前 30 条）
-/
theorem multinomial_single [DecidableEq α] :
    multinomial s (Pi.single a n) = 1 := by
  rw [← Nat.mul_right_inj (prod_ne_zero_iff.mpr (fun _ _ ↦ factorial_ne_zero _)), mul_one,
    multinomial_spec, sum_pi_single']
  split_ifs with ha
  · rw [Finset.prod_eq_single a (by simp_all) (by simp_all), Pi.single_eq_same]
  · rw [eq_comm, factorial_zero]
    apply Finset.prod_eq_one
    intro _ hb
    rw [Pi.single_apply, if_neg (ne_of_mem_of_not_mem hb ha), factorial_zero]

/-! ### Connection to binomial coefficients

When `Nat.multinomial` is applied to a `Finset` of two elements `{a, b}`, the
result a binomial coefficient. We use `binomial` in the names of lemmas that
involves `Nat.multinomial {a, b}`.
-/

/-
**Nat.binomial_eq** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：binomial_eq [DecidableEq α] (h : a != b) : multinomial {a, b} f = (f a + f
 b)! / ((f a)! * (f b)!)
参数：h : a != b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_pair`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid M
] {f : ι → M} [inst_1 : DecidableEq ι] {a b : ι},   a ≠ b → ∑ x ∈ {a, b}, f x = 
f a +…
· 使用定理 `Finset.prod_pair`：prod_pair [DecidableEq ι] {a b : ι} (h : a != b) : (∏ 
x in ({a, b} : Finset ι), f x) = f a * f b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
### Connection to binomial coefficients

When `Nat.multinomial` is applied to a `Finset` of two elements `{a, b}`, the
result a binomial coefficient. We use `binomial` in the names of lemmas that
involves `Nat.multinomial {a, b}`.
-/
theorem binomial_eq [DecidableEq α] (h : a ≠ b) :
    multinomial {a, b} f = (f a + f b)! / ((f a)! * (f b)!) := by
  simp [multinomial, Finset.sum_pair h, Finset.prod_pair h]
/-
**Nat.binomial_eq_choose** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：binomial_eq_choose [DecidableEq α] (h : a != b) : multinomial {a, b} f = (
f a + f b).choose (f a)
参数：h : a != b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.binomial_eq`：binomial_eq [DecidableEq α] (h : a != b) : multinomial 
{a, b} f = (f a + f b)! / ((f a)! * (f b)!)
· 使用定理 `Nat.choose_eq_factorial_div_factorial`：choose_eq_factorial_div_factorial
 {n k : Nat} (hk : k <= n) : choose n k = n ! / (k ! * (n - k)!)
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
· 使用定理 `add_tsub_cancel_left`：add_tsub_cancel_left (a b : α) : a + b - a = b
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem binomial_eq_choose [DecidableEq α] (h : a ≠ b) :
    multinomial {a, b} f = (f a + f b).choose (f a) := by
  simp [binomial_eq h, choose_eq_factorial_div_factorial (Nat.le_add_right _ _)]
/-
**Nat.binomial_spec** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：binomial_spec [DecidableEq α] (hab : a != b) : (f a)! * (f b)! * multinomi
al {a, b} f = (f a + f b)!
参数：hab : a != b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.prod_pair`：prod_pair [DecidableEq ι] {a b : ι} (h : a != b) : (∏ 
x in ({a, b} : Finset ι), f x) = f a * f b
· 使用定理 `Finset.sum_pair`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid M
] {f : ι → M} [inst_1 : DecidableEq ι] {a b : ι},   a ≠ b → ∑ x ∈ {a, b}, f x = 
f a +…
· 使用定理 `Nat.multinomial_spec`：multinomial_spec : (∏ i in s, (f i)!) * multinomia
l s f = (∑ i in s, f i)!
-/
theorem binomial_spec [DecidableEq α] (hab : a ≠ b) :
    (f a)! * (f b)! * multinomial {a, b} f = (f a + f b)! := by
  simpa [Finset.sum_pair hab, Finset.prod_pair hab] using multinomial_spec {a, b} f
/-
**Nat.binomial_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：binomial_one [DecidableEq α] (h : a != b) (h₁ : f a = 1) : multinomial {a,
 b} f = (f b).succ
参数：h : a != b；h₁ : f a = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.multinomial_insert_one`：multinomial_insert_one [DecidableEq α] (h : 
a ∉ s) (h₁ : f a = 1) : multinomial (insert a s) f = (s.sum f).succ * multinomia
l s f
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `Nat.multinomial_singleton`：∀ {α : Type u_1} (a : α) (f : α → ℕ), Nat.mul
tinomial {a} f = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem binomial_one [DecidableEq α] (h : a ≠ b) (h₁ : f a = 1) :
    multinomial {a, b} f = (f b).succ := by
  simp [h, h₁]
/-
**Nat.binomial_succ_succ** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：binomial_succ_succ [DecidableEq α] (h : a != b) : multinomial {a, b} (Func
tion.update (Function.update f a (f a).succ) b (f b).succ) = multinomial {a, b} 
(Function.update f a (f a).succ) + multinomial {a, b} (Function.update f b (f b)
.succ)
参数：h : a != b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.binomial_eq_choose`：binomial_eq_choose [DecidableEq α] (h : a != b) 
: multinomial {a, b} f = (f a + f b).choose (f a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Function.update_apply`：update_apply {β : Sort*} (f : α -> β) (a' : α) (b
 : β) (a : α) : update f a' b a = if a = a' then b else f a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Nat.add_succ`：∀ (n m : ℕ), n + m.succ = (n + m).succ
· 使用定理 `Nat.choose_succ_succ`：choose_succ_succ (n k : Nat) : choose (succ n) (su
cc k) = choose n k + choose n (succ k)
· 使用定理 `Nat.succ_add_eq_add_succ`：∀ (a b : ℕ), a.succ + b = a + b.succ
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
-/
theorem binomial_succ_succ [DecidableEq α] (h : a ≠ b) :
    multinomial {a, b} (Function.update (Function.update f a (f a).succ) b (f b).succ) =
      multinomial {a, b} (Function.update f a (f a).succ) +
      multinomial {a, b} (Function.update f b (f b).succ) := by
  simp only [binomial_eq_choose, Function.update_apply,
    h, Ne, ite_true, ite_false, not_false_eq_true]
  rw [if_neg h.symm]
  rw [add_succ, choose_succ_succ, succ_add_eq_add_succ]
  ring
/-
**Nat.succ_mul_binomial** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：succ_mul_binomial [DecidableEq α] (h : a != b) : (f a + f b).succ * multin
omial {a, b} f = (f a).succ * multinomial {a, b} (Function.update f a (f a).succ
)
参数：h : a != b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.binomial_eq_choose`：binomial_eq_choose [DecidableEq α] (h : a != b) 
: multinomial {a, b} f = (f a + f b).choose (f a)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Nat.succ_eq_add_one`：∀ (n : ℕ), n.succ = n + 1
· 使用定理 `Nat.add_one_mul_choose_eq`：∀ (n k : ℕ), (n + 1) * n.choose k = (n + 1).c
hoose (k + 1) * (k + 1)
· 使用定理 `Nat.succ_add`：∀ (n m : ℕ), n.succ + m = (n + m).succ
-/
theorem succ_mul_binomial [DecidableEq α] (h : a ≠ b) :
    (f a + f b).succ * multinomial {a, b} f =
      (f a).succ * multinomial {a, b} (Function.update f a (f a).succ) := by
  rw [binomial_eq_choose h, binomial_eq_choose h, mul_comm (f a).succ, Function.update_self,
    Function.update_of_ne h.symm]
  rw [succ_eq_add_one, add_one_mul_choose_eq (f a + f b) (f a), succ_add (f a) (f b)]

/-! ### Simple cases -/


/-
**Nat.multinomial_univ_two** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：multinomial_univ_two (a b : Nat) : multinomial Finset.univ ![a, b] = (a + 
b)! / (a ! * b !)
参数：a b : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.multinomial.eq_1`：∀ {α : Type u_1} (s : Finset α) (f : α → ℕ), Nat.m
ultinomial s f = (∑ i ∈ s, f i).factorial / ∏ i ∈ s, (f i).factorial
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fin.sum_univ_two`：∀ {M : Type u_2} [inst : AddCommMonoid M] (f : Fin 2 →
 M), ∑ i, f i = f 0 + f 1
· 使用定理 `Fin.prod_univ_two`：prod_univ_two (f : Fin 2 -> M) : ∏ i, f i = f 0 * f 1

--- 原说明 ---
### Simple cases
-/
theorem multinomial_univ_two (a b : ℕ) :
    multinomial Finset.univ ![a, b] = (a + b)! / (a ! * b !) := by
  rw [multinomial, Fin.sum_univ_two, Fin.prod_univ_two]
  dsimp only [Matrix.cons_val]
/-
**Nat.multinomial_univ_three** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：multinomial_univ_three (a b c : Nat) : multinomial Finset.univ ![a, b, c] 
= (a + b + c)! / (a ! * b ! * c !)
参数：a b c : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.multinomial.eq_1`：∀ {α : Type u_1} (s : Finset α) (f : α → ℕ), Nat.m
ultinomial s f = (∑ i ∈ s, f i).factorial / ∏ i ∈ s, (f i).factorial
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fin.sum_univ_three`：∀ {M : Type u_2} [inst : AddCommMonoid M] (f : Fin 3
 → M), ∑ i, f i = f 0 + f 1 + f 2
· 使用定理 `Fin.prod_univ_three`：prod_univ_three (f : Fin 3 -> M) : ∏ i, f i = f 0 *
 f 1 * f 2
-/
theorem multinomial_univ_three (a b c : ℕ) :
    multinomial Finset.univ ![a, b, c] = (a + b + c)! / (a ! * b ! * c !) := by
  rw [multinomial, Fin.sum_univ_three, Fin.prod_univ_three]
  rfl

end Nat

/-! ### Alternative definitions -/

namespace Finsupp

variable {α : Type*}

/-- Alternative multinomial definition based on a finsupp, using the support
  for the big operations
-/
/-
**Finsupp.multinomial** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：multinomial (f : α ->₀ Nat) : Nat
参数：f : α ->₀ Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Alternative multinomial definition based on a finsupp, using the support
  for the big operations
-/
def multinomial (f : α →₀ ℕ) : ℕ :=
  (f.sum fun _ => id)! / f.prod fun _ n => n !
/-
**Finsupp.multinomial_eq** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：multinomial_eq (f : α ->₀ Nat) : f.multinomial = Nat.multinomial f.support
 f
参数：f : α ->₀ Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem multinomial_eq (f : α →₀ ℕ) : f.multinomial = Nat.multinomial f.support f :=
  rfl
/-
**Finsupp.multinomial_eq_of_support_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：multinomial_eq_of_support_subset {f : α ->₀ Nat} {s : Finset α} (h : f.sup
port subseteq s) : f.multinomial = Nat.multinomial s f
参数：h : f.support subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_subset`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [i
nst : AddCommMonoid M] {f : ι → M},   s₁ ⊆ s₂ → (∀ x ∈ s₂, x ∉ s₁ → f x = 0) → ∑
 x ∈ s₁…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.prod_subset`：prod_subset (h : s₁ subseteq s₂) (hf : forall x in s
₂, x ∉ s₁ -> f x = 1) : ∏ x in s₁, f x = ∏ x in s₂, f x
-/
theorem multinomial_eq_of_support_subset {f : α →₀ ℕ} {s : Finset α} (h : f.support ⊆ s) :
    f.multinomial = Nat.multinomial s f := by
  simp only [Finsupp.multinomial_eq, Nat.multinomial]
  congr 1
  · simp [Finset.sum_subset h]
  · rw [Finset.prod_subset h]
    grind [Nat.factorial_eq_one]
/-
**Finsupp.multinomial_update** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：multinomial_update (a : α) (f : α ->₀ Nat) : f.multinomial = (f.sum fun _ 
=> id).choose (f a) * (f.update a 0).multinomial
参数：a : α；f : α ->₀ Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.insert_erase`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Finset
 α} {a : α}, a ∈ s → insert a (s.erase a) = s
· 使用引理 `Nat.multinomial_insert`：multinomial_insert [DecidableEq α] (ha : a ∉ s) 
(f : α -> Nat) : multinomial (insert a s) f = (f a + ∑ i in s, f i).choose (f a)
 * multinomi…
· 使用定理 `Finset.notMem_erase`：notMem_erase (a : α) (s : Finset α) : a ∉ erase s a
· 使用定理 `Finset.add_sum_erase`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] [inst_1 : DecidableEq ι] (s : Finset ι) (f : ι → M) {a : ι},   a ∈ s → f 
a + ∑ x ∈ …
· 使用定理 `Finsupp.support_update_zero`：support_update_zero [DecidableEq α] : suppo
rt (f.update a 0) = f.support.erase a
· 使用定理 `Nat.multinomial_congr`：multinomial_congr {f g : α -> Nat} (h : forall a 
in s, f a = g a) : multinomial s f = multinomial s g
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_erase`：mem_erase {a b : α} {s : Finset α} : a in erase s b ↔ 
a != b ∧ a in s
· 使用定理 `Finsupp.notMem_support_iff`：notMem_support_iff {f : α ->₀ M} {a} : a ∉ f
.support ↔ f a = 0
· 使用定理 `Nat.choose_zero_right`：choose_zero_right (n : Nat) : choose n 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Finsupp.update_self`：update_self : f.update a (f a) = f
-/
theorem multinomial_update (a : α) (f : α →₀ ℕ) :
    f.multinomial = (f.sum fun _ => id).choose (f a) * (f.update a 0).multinomial := by
  simp only [multinomial_eq]
  classical
    by_cases h : a ∈ f.support
    · rw [← Finset.insert_erase h, Nat.multinomial_insert (Finset.notMem_erase a _),
        Finset.add_sum_erase _ f h, support_update_zero]
      congr 1
      exact Nat.multinomial_congr fun _ h ↦ (Function.update_of_ne (mem_erase.1 h).1 0 f).symm
    rw [notMem_support_iff] at h
    rw [h, Nat.choose_zero_right, one_mul, ← h, update_self]

end Finsupp

namespace Multiset

variable {α : Type*}

/-- The number of permutations of a given multiset. -/
/-
**Multiset.countPerms** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：countPerms [DecidableEq α] (m : Multiset α) : Nat
参数：m : Multiset α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The number of permutations of a given multiset.
-/
noncomputable def countPerms [DecidableEq α] (m : Multiset α) : ℕ :=
  m.toFinsupp.multinomial
/-
**Multiset.countPerms_filter_ne** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：countPerms_filter_ne [DecidableEq α] (a : α) (m : Multiset α) : m.countPer
ms = m.card.choose (m.count a) * (m.filter (a != ·)).countPerms
参数：a : α；m : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.card_toMultiset`：card_toMultiset (f : α ->₀ Nat) : Multiset.card
 (toMultiset f) = f.sum fun _ => id
· 使用定理 `Multiset.toFinsupp_toMultiset`：toFinsupp_toMultiset (s : Multiset α) : F
insupp.toMultiset (toFinsupp s) = s
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `Multiset.toFinsupp_apply`：toFinsupp_apply (s : Multiset α) (a : α) : toF
insupp s a = s.count a
· 使用定理 `Multiset.count_filter`：count_filter {p} [DecidablePred p] {a} {s : Multi
set α} : count a (filter p s) = if p a then count a s else 0
· 使用定理 `Finsupp.coe_update`：coe_update [DecidableEq α] : (f.update a b : α -> M)
 = Function.update f a b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_ne_iff`：not_ne_iff {α : Sort*} {a b : α} : ¬a != b ↔ a = b
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `Finsupp.multinomial_update`：multinomial_update (a : α) (f : α ->₀ Nat) :
 f.multinomial = (f.sum fun _ => id).choose (f a) * (f.update a 0).multinomial
-/
theorem countPerms_filter_ne [DecidableEq α] (a : α) (m : Multiset α) :
    m.countPerms = m.card.choose (m.count a) * (m.filter (a ≠ ·)).countPerms := by
  dsimp only [countPerms]
  convert! Finsupp.multinomial_update a _
  · rw [← Finsupp.card_toMultiset, m.toFinsupp_toMultiset]
  · ext1 a
    rw [toFinsupp_apply, count_filter, Finsupp.coe_update]
    split_ifs with h
    · rw [Function.update_of_ne h.symm, toFinsupp_apply]
    · rw [not_ne_iff.1 h, Function.update_self]

@[simp]
/-
**Multiset.countPerms_zero** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：countPerms_zero [DecidableEq α] : countPerms (0 : Multiset α) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
· 使用定理 `Nat.div_self`：∀ {n : ℕ}, 0 < n → n / n = 1
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem countPerms_zero [DecidableEq α] : countPerms (0 : Multiset α) = 1 := by
  simp [countPerms, Finsupp.multinomial]

end Multiset

namespace Finset
open _root_.Nat

/-! ### Multinomial theorem -/

variable {α R : Type*} [DecidableEq α]

section Semiring
variable [Semiring R]

open scoped Function -- required for scoped `on` notation

set_option backward.isDefEq.respectTransparency false in
-- TODO: Can we prove one of the following two from the other one?
/-- The **multinomial theorem**. -/
/-
**Finset.sum_pow_eq_sum_piAntidiag_of_commute** 是 Mathlib 中的一个引理，位于命名空间 `Finset`
。
形式化陈述：sum_pow_eq_sum_piAntidiag_of_commute (s : Finset α) (f : α -> R) (hc : (s 
: Set α).Pairwise (Commute on f)) (n : Nat) : (∑ i in s, f i) ^ n = ∑ k in piAnt
idiag s n, multinomial s k * s.noncommProd (fun i => f i ^ k i) (hc.mono' fun _ 
_ h => h.pow_pow ..)
参数：s : Finset α；f : α -> R；hc : (s : Set α).Pairwise (Commute on f)；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction`：∀ {α : Type u_3} {motive : Finset α → Prop},   mo
tive ∅ → (∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a
 s h)) → ∀ …
· 使用定理 `Set.Pairwise.mono'`：∀ {α : Type u_1} {r p : α → α → Prop} {s : Set α}, r
 ≤ p → s.Pairwise r → s.Pairwise p
· 使用定理 `Commute.pow_pow`：pow_pow (h : Commute a b) (m n : Nat) : Commute (a ^ m)
 (b ^ n)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.piAntidiag_zero`：∀ {ι : Type u_1} {μ : Type u_2} [inst : Decidabl
eEq ι] [inst_1 : AddCommMonoid μ] [inst_2 : PartialOrder μ]   [CanonicallyOrdere
dAdd μ] [ins…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.multinomial_empty`：∀ {α : Type u_1} (f : α → ℕ), Nat.multinomial ∅ f
 = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.piAntidiag_empty_of_ne_zero`：∀ {ι : Type u_1} {μ : Type u_2} [ins
t : DecidableEq ι] [inst_1 : AddCommMonoid μ] [inst_2 : Finset.HasAntidiagonal μ
]   [inst_3 : DecidableE…
· 使用定理 `zero_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 0 • a = 0
· 使用定理 `Finset.sum_cons`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι} 
[inst : AddCommMonoid M] {f : ι → M} (h : a ∉ s),   ∑ x ∈ Finset.cons a s h, f x
 = f …
· 使用定理 `Pi.instIsRightCancelAdd`：∀ {I : Type u} {f : I → Type v₁} [inst : (i : I
) → Add (f i)] [∀ (i : I), IsRightCancelAdd (f i)],   IsRightCancelAdd ((i : I) 
→ f i)
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `Finset.pairwiseDisjoint_piAntidiag_map_addRightEmbedding`：pairwiseDisjoi
nt_piAntidiag_map_addRightEmbedding (hi : i ∉ s) (n : μ) : (antidiagonal n : Set
 (μ × μ)).PairwiseDisjoint fun p => map (addRi…
· 使用引理 `Finset.piAntidiag_cons`：piAntidiag_cons (hi : i ∉ s) (n : μ) : piAntidia
g (cons i s hi) n = (antidiagonal n).disjiUnion (fun p : μ × μ => (piAntidiag s 
p.snd).map (…
（共 73 条，此处仅展示前 30 条）

--- 原说明 ---
The **multinomial theorem**.
-/
lemma sum_pow_eq_sum_piAntidiag_of_commute (s : Finset α) (f : α → R)
    (hc : (s : Set α).Pairwise (Commute on f)) (n : ℕ) :
    (∑ i ∈ s, f i) ^ n = ∑ k ∈ piAntidiag s n, multinomial s k *
      s.noncommProd (fun i ↦ f i ^ k i) (hc.mono' fun _ _ h ↦ h.pow_pow ..) := by
  induction s using Finset.cons_induction generalizing n with
  | empty => cases n <;> simp
  | cons a s has ih => ?_
  rw [Finset.sum_cons, piAntidiag_cons, sum_disjiUnion]
  simp only [sum_map, Pi.add_apply, multinomial_cons,
    Pi.add_apply, if_true, Nat.cast_mul, noncommProd_cons,
    if_true, sum_add_distrib, sum_ite_eq', has, if_false, add_zero,
    addRightEmbedding_apply]
  suffices ∀ p : ℕ × ℕ, p ∈ antidiagonal n →
    ∑ g ∈ piAntidiag s p.2, ((g a + p.1 + s.sum g).choose (g a + p.1) : R) *
      multinomial s (g + fun i ↦ ite (i = a) p.1 0) *
        (f a ^ (g a + p.1) * s.noncommProd (fun i ↦ f i ^ (g i + ite (i = a) p.1 0))
          ((hc.mono (by simp)).mono' fun i j h ↦ h.pow_pow ..)) =
      ∑ g ∈ piAntidiag s p.2, n.choose p.1 * multinomial s g * (f a ^ p.1 *
        s.noncommProd (fun i ↦ f i ^ g i) ((hc.mono (by simp)).mono' fun i j h ↦ h.pow_pow ..)) by
    rw [sum_congr rfl this]
    simp only [Nat.antidiagonal_eq_map, sum_map, Function.Embedding.coeFn_mk]
    rw [(Commute.sum_right _ _ _ fun i hi ↦ hc (by simp) (by simp [hi])
      (by simpa [eq_comm] using ne_of_mem_of_not_mem hi has)).add_pow]
    simp only [ih (hc.mono (by simp)), sum_mul, mul_sum]
    refine sum_congr rfl fun i _ ↦ sum_congr rfl fun g _ ↦ ?_
    rw [← Nat.cast_comm, (Nat.commute_cast (f a ^ i) _).left_comm, mul_assoc]
  refine fun p hp ↦ sum_congr rfl fun f hf ↦ ?_
  rw [mem_piAntidiag] at hf
  rw [not_imp_comm.1 (hf.2 _) has, zero_add, hf.1]
  congr 2
  · rw [mem_antidiagonal.1 hp]
  · rw [multinomial_congr]
    intro t ht
    rw [Pi.add_apply, if_neg, add_zero]
    exact ne_of_mem_of_not_mem ht has
  refine noncommProd_congr rfl (fun t ht ↦ ?_) _
  rw [if_neg, add_zero]
  exact ne_of_mem_of_not_mem ht has

/-- The **multinomial theorem**. -/
/-
**Finset.sum_pow_of_commute** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sum_pow_of_commute (x : α -> R) (s : Finset α) (hc : (s : Set α).Pairwise 
(Commute on x)) : forall n, s.sum x ^ n = ∑ k : s.sym n, k.1.1.countPerms * (k.1
.1.map <| x).noncommProd (Multiset.map_set_pairwise <| hc.mono <| mem_sym_iff.1 
k.2)
参数：x : α -> R；s : Finset α；hc : (s : Set α).Pairwise (Commute on x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `Multiset.map_set_pairwise`：map_set_pairwise {f : α -> β} {r : β -> β -> 
Prop} {m : Multiset α} (h : { a | a in m }.Pairwise fun a₁ a₂ => r (f a₁) (f a₂)
) : { b | b in …
· 使用定理 `Set.Pairwise.mono`：∀ {α : Type u_1} {r : α → α → Prop} {s t : Set α}, t 
⊆ s → s.Pairwise r → t.Pairwise r
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_sym_iff`：mem_sym_iff {m : Sym α n} : m in s.sym n ↔ forall a 
in m, a in s
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_empty`：∀ {ι : Type u_1} {M : Type u_3} {f : ι → M} [inst : Ad
dCommMonoid M], ∑ x ∈ ∅, f x = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Fintype.sum_subsingleton`：∀ {M : Type u_4} {ι : Type u_7} [inst : Fintyp
e ι] [inst_1 : AddCommMonoid M] [Subsingleton ι] (f : ι → M) (a : ι),   ∑ x, f x
 = f a
· 使用定理 `instSubsingletonSubtype_mathlib`：∀ {α : Sort u_1} [Subsingleton α] (p : 
α → Prop), Subsingleton (Subtype p)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.countPerms_zero`：countPerms_zero [DecidableEq α] : countPerms (
0 : Multiset α) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Fintype.sum_empty`：∀ {ι : Type u_1} {M : Type u_3} [inst : Fintype ι] [i
nst_1 : AddCommMonoid M] [IsEmpty ι] (f : ι → M), ∑ x, f x = 0
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `Commute.add_pow`：add_pow (h : Commute x y) (n : Nat) : (x + y) ^ n = ∑ m
 in range (n + 1), x ^ m * y ^ (n - m) * n.choose m
· 使用定理 `Commute.sum_right`：∀ {ι : Type u_1} {R : Type u_4} [inst : NonUnitalNonA
ssocSemiring R] (s : Finset ι) (f : ι → R) (b : R),   (∀ i ∈ s, Commute b (f i))
 → Comm…
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
（共 56 条，此处仅展示前 30 条）

--- 原说明 ---
The **multinomial theorem**.
-/
theorem sum_pow_of_commute (x : α → R) (s : Finset α)
    (hc : (s : Set α).Pairwise (Commute on x)) :
    ∀ n,
      s.sum x ^ n =
        ∑ k : s.sym n,
          k.1.1.countPerms *
            (k.1.1.map <| x).noncommProd
              (Multiset.map_set_pairwise <| hc.mono <| mem_sym_iff.1 k.2) := by
  induction s using Finset.induction with
  | empty =>
    rw [sum_empty]
    rintro (_ | n)
    · rw [_root_.pow_zero, Fintype.sum_subsingleton]
      swap
      · exact ⟨0, by simp [eq_iff_true_of_subsingleton]⟩
      convert! (@one_mul R _ _).symm
      convert! @Nat.cast_one R _
      simp
    · rw [_root_.pow_succ, mul_zero]
      have : IsEmpty (Finset.sym (∅ : Finset α) n.succ) := Finset.instIsEmpty
      apply (Fintype.sum_empty _).symm
  | insert a s ha ih => ?_
  intro n; specialize ih (hc.mono <| s.subset_insert a)
  rw [sum_insert ha, (Commute.sum_right s _ _ _).add_pow, sum_range]; swap
  · exact fun _ hb => hc (mem_insert_self a s) (mem_insert_of_mem hb)
      (ne_of_mem_of_not_mem hb ha).symm
  · simp_rw [ih, mul_sum, sum_mul, sum_sigma', univ_sigma_univ]
    refine (Fintype.sum_equiv (symInsertEquiv ha) _ _ fun m => ?_).symm
    rw [m.1.1.countPerms_filter_ne a]
    conv in m.1.1.map _ => rw [← m.1.1.filter_add_not (a = ·), Multiset.map_add]
    simp_rw [Multiset.noncommProd_add, m.1.1.filter_eq, Multiset.map_replicate, m.1.2]
    rw [Multiset.noncommProd_eq_pow_card _ _ _ fun _ => Multiset.eq_of_mem_replicate]
    rw [Multiset.card_replicate, Nat.cast_mul, mul_assoc, Nat.cast_comm]
    congr 1; simp_rw [← mul_assoc, Nat.cast_comm]; rfl

end Semiring

section CommSemiring
variable [CommSemiring R] {f : α → R} {s : Finset α}

/-
**Finset.sum_pow_eq_sum_piAntidiag** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：sum_pow_eq_sum_piAntidiag (s : Finset α) (f : α -> R) (n : Nat) : (∑ i in 
s, f i) ^ n = ∑ k in piAntidiag s n, multinomial s k * ∏ i in s, f i ^ k i
参数：s : Finset α；f : α -> R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Set.Pairwise.mono'`：∀ {α : Type u_1} {r p : α → α → Prop} {s : Set α}, r
 ≤ p → s.Pairwise r → s.Pairwise p
· 使用定理 `Commute.pow_pow`：pow_pow (h : Commute a b) (m n : Nat) : Commute (a ^ m)
 (b ^ n)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.sum_pow_eq_sum_piAntidiag_of_commute`：sum_pow_eq_sum_piAntidiag_o
f_commute (s : Finset α) (f : α -> R) (hc : (s : Set α).Pairwise (Commute on f))
 (n : Nat) : (∑ i in s, f i) ^ n …
-/
lemma sum_pow_eq_sum_piAntidiag (s : Finset α) (f : α → R) (n : ℕ) :
    (∑ i ∈ s, f i) ^ n = ∑ k ∈ piAntidiag s n, multinomial s k * ∏ i ∈ s, f i ^ k i := by
  simp_rw [← noncommProd_eq_prod]
  rw [← sum_pow_eq_sum_piAntidiag_of_commute _ _ fun _ _ _ _ _ ↦ Commute.all ..]
/-
**Finset.sum_pow** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sum_pow (x : α -> R) (n : Nat) : s.sum x ^ n = ∑ k in s.sym n, k.val.count
Perms * (k.val.map x).prod
参数：x : α -> R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_coe_sort`：∀ {ι : Type u_1} {M : Type u_4} (s : Finset ι) [ins
t : AddCommMonoid M] (f : ι → M), ∑ i, f ↑i = ∑ i ∈ s, f i
· 使用定理 `Multiset.map_set_pairwise`：map_set_pairwise {f : α -> β} {r : β -> β -> 
Prop} {m : Multiset α} (h : { a | a in m }.Pairwise fun a₁ a₂ => r (f a₁) (f a₂)
) : { b | b in …
· 使用定理 `Set.Pairwise.mono`：∀ {α : Type u_1} {r : α → α → Prop} {s t : Set α}, t 
⊆ s → s.Pairwise r → t.Pairwise r
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_sym_iff`：mem_sym_iff {m : Sym α n} : m in s.sym n ↔ forall a 
in m, a in s
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Multiset.noncommProd_eq_prod`：noncommProd_eq_prod {α : Type*} [CommMonoi
d α] (s : Multiset α) : (noncommProd s fun _ _ _ _ _ => Commute.all _ _) = prod 
s
· 使用定理 `Finset.sum_pow_of_commute`：sum_pow_of_commute (x : α -> R) (s : Finset α
) (hc : (s : Set α).Pairwise (Commute on x)) : forall n, s.sum x ^ n = ∑ k : s.s
ym n, k.1.1.cou…
-/
theorem sum_pow (x : α → R) (n : ℕ) :
    s.sum x ^ n = ∑ k ∈ s.sym n, k.val.countPerms * (k.val.map x).prod := by
  conv_rhs => rw [← sum_coe_sort]
  convert! sum_pow_of_commute x s (fun _ _ _ _ _ ↦ Commute.all ..) n
  rw [Multiset.noncommProd_eq_prod]

end CommSemiring
end Finset

namespace Nat
variable {ι : Type*} {s : Finset ι} {f : ι → ℕ}

/-
**Nat.multinomial_two_mul_le_mul_multinomial** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：multinomial_two_mul_le_mul_multinomial : multinomial s (fun i => 2 * f i) 
<= ((∑ i in s, f i) ^ ∑ i in s, f i) * multinomial s f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.multinomial.eq_1`：∀ {α : Type u_1} (s : Finset α) (f : α → ℕ), Nat.m
ultinomial s f = (∑ i ∈ s, f i).factorial / ∏ i ∈ s, (f i).factorial
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `Nat.mul_div_assoc`：∀ {k n : ℕ} (m : ℕ), k ∣ n → m * n / k = m * (n / k)
· 使用定理 `Nat.prod_factorial_dvd_factorial_sum`：prod_factorial_dvd_factorial_sum :
 (∏ i in s, (f i)!) ∣ (∑ i in s, f i)!
· 使用定理 `Nat.div_le_div_of_mul_le_mul`：∀ {d c a b : ℕ}, d ≠ 0 → d ∣ c → a * d ≤ c
 * b → a / b ≤ c / d
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `Finset.prod_pos`：prod_pos (h0 : forall i in s, 0 < f i) : 0 < ∏ i in s, 
f i
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `Nat.factorial_pos`：∀ (n : ℕ), 0 < n.factorial
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `Nat.dvd_mul_left`：∀ (a b : ℕ), a ∣ b * a
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用引理 `Nat.factorial_two_mul_le`：factorial_two_mul_le (n : Nat) : (2 * n)! <= (
2 * n) ^ n * n !
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用引理 `Finset.prod_pow_eq_pow_sum`：prod_pow_eq_pow_sum (s : Finset ι) (f : ι ->
 Nat) (a : M) : ∏ i in s, a ^ f i = a ^ ∑ i in s, f i
· 使用定理 `Finset.prod_mul_distrib`：prod_mul_distrib : ∏ x in s, f x * g x = (∏ x i
n s, f x) * ∏ x in s, g x
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.single_pow`：∀ {R : Type u_1} [inst : CommSemi
ring R] {a c : R} {b : ℕ}, a ^ b = c → (a + 0) ^ b = c + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pow_mul`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₂ c₂ : R} {ea₁ b c₁ : ℕ} {xa₁ c₃ d : R},   ea₁ * b = c₁ → a₂ ^ b = c₂
 → xa₁ ^ c₁ * Nat.rawCast 1 …
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
（共 50 条，此处仅展示前 30 条）
-/
lemma multinomial_two_mul_le_mul_multinomial :
    multinomial s (fun i ↦ 2 * f i) ≤ ((∑ i ∈ s, f i) ^ ∑ i ∈ s, f i) * multinomial s f := by
  rw [multinomial, multinomial, ← mul_sum,
    ← Nat.mul_div_assoc _ (prod_factorial_dvd_factorial_sum ..)]
  refine Nat.div_le_div_of_mul_le_mul (by positivity)
    ((prod_factorial_dvd_factorial_sum ..).trans (Nat.dvd_mul_left ..)) ?_
  calc
    (2 * ∑ i ∈ s, f i)! * ∏ i ∈ s, (f i)!
      ≤ ((2 * ∑ i ∈ s, f i) ^ (∑ i ∈ s, f i) * (∑ i ∈ s, f i)!) * ∏ i ∈ s, (f i)! := by
      gcongr; exact Nat.factorial_two_mul_le _
    _ = ((∑ i ∈ s, f i) ^ ∑ i ∈ s, f i) * (∑ i ∈ s, f i)! * ∏ i ∈ s, 2 ^ f i * (f i)! := by
      rw [mul_pow, ← prod_pow_eq_pow_sum, prod_mul_distrib]; ring
    _ ≤ ((∑ i ∈ s, f i) ^ ∑ i ∈ s, f i) * (∑ i ∈ s, f i)! * ∏ i ∈ s, (2 * f i)! := by
      gcongr
      rw [← doubleFactorial_two_mul]
      exact doubleFactorial_le_factorial _

end Nat

namespace Sym

variable {n : ℕ} {α : Type*} [DecidableEq α]

/-
**Sym.countPerms_coe_fill_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Sym`。
形式化陈述：countPerms_coe_fill_of_notMem {m : Fin (n + 1)} {s : Sym α (n - m)} {x : α
} (hx : x ∉ s) : (fill x m s : Multiset α).countPerms = n.choose m * (s : Multis
et α).countPerms
参数：n + 1；n - m；hx : x ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.countPerms_filter_ne`：countPerms_filter_ne [DecidableEq α] (a :
 α) (m : Multiset α) : m.countPerms = m.card.choose (m.count a) * (m.filter (a !
= ·)).countPerms
· 使用定理 `congrArg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → γ
) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Sym.card_coe`：card_coe : Multiset.card (s : Multiset α) = n
· 使用定理 `Sym.count_coe_fill_self_of_notMem`：count_coe_fill_self_of_notMem [Decida
bleEq α] {a : α} {i : Fin (n + 1)} {s : Sym α (n - i)} (hx : a ∉ s) : count a (f
ill a i s : Multiset α)…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Sym.mem_coe`：mem_coe : a in (s : Multiset α) ↔ a in s
· 使用定理 `Sym.coe_fill`：coe_fill {a : α} {i : Fin (n + 1)} {m : Sym α (n - i)} : (
fill a i m : Multiset α) = m + replicate i a
· 使用定理 `Sym.coe_replicate`：coe_replicate : (replicate n a : Multiset α) = Multis
et.replicate n a
· 使用定理 `Multiset.filter_add`：filter_add (s t : Multiset α) : filter p (s + t) = 
filter p s + filter p t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.filter_eq_self`：filter_eq_self {s} : filter p s = s ↔ forall a 
in s, p a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_eq_left`：∀ {M : Type u_4} [inst : AddMonoid M] [IsLeftCancelAdd M] {
a b : M}, a + b = a ↔ b = 0
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `Multiset.filter_eq_nil`：filter_eq_nil {s} : filter p s = 0 ↔ forall a in
 s, ¬p a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_replicate`：mem_replicate {a b : α} {n : Nat} : b in replica
te n a ↔ n != 0 ∧ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem countPerms_coe_fill_of_notMem {m : Fin (n + 1)} {s : Sym α (n - m)} {x : α} (hx : x ∉ s) :
    (fill x m s : Multiset α).countPerms = n.choose m * (s : Multiset α).countPerms := by
  rw [Multiset.countPerms_filter_ne x]
  rw [← mem_coe] at hx
  refine congrArg₂ _ ?_ ?_
  · rw [card_coe, count_coe_fill_self_of_notMem hx]
  · refine congrArg _ ?_
    rw [coe_fill, coe_replicate, Multiset.filter_add]
    rw [Multiset.filter_eq_self.mpr]
    · rw [add_eq_left]
      rw [Multiset.filter_eq_nil]
      exact fun j hj ↦ by simp [Multiset.mem_replicate.mp hj]
    · exact fun j hj h ↦ hx <| by simpa [h] using hj

end Sym

/-
**Finsupp.multinomial_of_support_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finsupp.multinomial_of_support_subset {σ : Type*} {d : σ ->₀ Nat} {s : Fin
set σ} (h : d.support subseteq s) : Nat.multinomial s d = d.multinomial
参数：h : d.support subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.multinomial.eq_1`：∀ {α : Type u_1} (s : Finset α) (f : α → ℕ), Nat.m
ultinomial s f = (∑ i ∈ s, f i).factorial / ∏ i ∈ s, (f i).factorial
· 使用定理 `Finsupp.multinomial.eq_1`：∀ {α : Type u_1} (f : α →₀ ℕ), f.multinomial =
 (f.sum fun x => id).factorial / f.prod fun x n => n.factorial
· 使用定理 `Finsupp.sum_of_support_subset`：∀ {α : Type u_1} {M : Type u_8} {N : Type
 u_10} [inst : Zero M] [inst_1 : AddCommMonoid N] (f : α →₀ M) {s : Finset α},  
 f.support ⊆ s → ∀ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finsupp.prod_of_support_subset`：prod_of_support_subset (f : α ->₀ M) {s 
: Finset α} (hs : f.support subseteq s) (g : α -> M -> N) (h : forall i in s, g 
i 0 = 1) : f.prod g …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
-/
theorem Finsupp.multinomial_of_support_subset {σ : Type*} {d : σ →₀ ℕ} {s : Finset σ}
    (h : d.support ⊆ s) : Nat.multinomial s d = d.multinomial := by
  rw [Nat.multinomial, Finsupp.multinomial,
    sum_of_support_subset _ h _ (by simp), prod_of_support_subset _ h _ (by simp)]
  simp

namespace List


/-
**List.toFinsupp_sum** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：toFinsupp_sum {α : Type*} [AddCommMonoid α] [DecidableEq α] (l : List α) :
 l.toFinsupp.sum (fun _ a => a) = l.sum
参数：l : List α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toFinsupp_sum {α : Type*} [AddCommMonoid α] [DecidableEq α] (l : List α) :
    l.toFinsupp.sum (fun _ a ↦ a) = l.sum := by
  match l with
  | nil => simp
  | x :: l =>
    simp only [toFinsupp_cons_eq_single_add_embDomain, sum_cons]
    rw [Finsupp.sum_add_index (by simp) (by simp)]
    simp [Finsupp.sum_embDomain, l.toFinsupp_sum]

/-- The multinomial coefficients given by a list of natural numbers.

See also `Multiset.multinomial` -/
/-
**List.multinomial** 是 Mathlib 中的一个缩写定义，位于命名空间 `List`。
形式化陈述：multinomial (l : List Nat) : Nat
参数：l : List Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multinomial coefficients given by a list of natural numbers.

See also `Multiset.multinomial`
-/
abbrev multinomial (l : List ℕ) : ℕ := l.toFinsupp.multinomial
/-
**List.multinomial_cons** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：multinomial_cons (x : Nat) (l : List Nat) : (x :: l).multinomial = Nat.cho
ose (x + l.sum) x * l.multinomial
参数：x : Nat；l : List Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.multinomial_update`：multinomial_update (a : α) (f : α ->₀ Nat) :
 f.multinomial = (f.sum fun _ => id).choose (f a) * (f.update a 0).multinomial
· 使用引理 `List.toFinsupp_sum`：toFinsupp_sum {α : Type*} [AddCommMonoid α] [Decidab
leEq α] (l : List α) : l.toFinsupp.sum (fun _ a => a) = l.sum
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Finsupp.coe_update`：coe_update [DecidableEq α] : (f.update a b : α -> M)
 = Function.update f a b
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finsupp.update_apply`：update_apply [DecidableEq α] : (f.update a b) i = 
if i = a then b else f i
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.single_eq_of_ne`：single_eq_of_ne (h : a' != a) : (single a b : α
 ->₀ M) a' = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Finsupp.embDomain_apply`：embDomain_apply (f : α ↪ β) (v : α ->₀ M) (b : 
β) : embDomain f v b = if h : exists a, f a = b then v h.choose else 0
· 使用定理 `addRightEmbedding_apply`：∀ {G : Type u_1} [inst : Add G] [inst_1 : IsRig
htCancelAdd G] (g h : G), (addRightEmbedding g) h = h + g
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Exists.choose.congr_simp`：∀ {α : Sort u_1} {p p_1 : α → Prop} (e_p : p =
 p_1) (P : ∃ a, p a), P.choose = ⋯.choose
· 使用定理 `Classical.choose_eq`：∀ {α : Sort u_1} (a : α), ⋯.choose = a
· 使用定理 `List.getD_eq_getElem?_getD`：∀ {α : Type u_1} {l : List α} {i : ℕ} {a : α
}, l.getD i a = l[i]?.getD a
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
（共 43 条，此处仅展示前 30 条）
-/
theorem multinomial_cons (x : ℕ) (l : List ℕ) :
    (x :: l).multinomial = Nat.choose (x + l.sum) x * l.multinomial := by
  simp only [multinomial]
  rw [Finsupp.multinomial_update 0 (x :: l).toFinsupp]
  congr 1
  · congr
    exact List.toFinsupp_sum (x :: l)
  let succEmb : ℕ ↪ ℕ := addRightEmbedding 1
  have : (Finsupp.single 0 x + l.toFinsupp.embDomain succEmb).update 0 0 =
    (l.toFinsupp.embDomain succEmb).update 0 0 := by
    ext i
    by_cases hi : i = 0
    · simp [hi]
    · simp [Finsupp.update_apply, if_neg hi, Finsupp.single_eq_of_ne hi]
  have h (x) : (l.toFinsupp.embDomain succEmb) (x + 1) = l[x]?.getD 0 := by
    rw [Finsupp.embDomain_apply, dif_pos ⟨x, by simp [succEmb]⟩]
    simp [succEmb]
  simp [toFinsupp_cons_eq_single_add_embDomain, Finsupp.multinomial_eq,
    succEmb, this, Nat.multinomial, h]

end List

namespace Multiset

/-- The `multinomial` coefficients on `Multiset ℕ`. -/
/-
**Multiset.multinomial** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：multinomial (m : Multiset Nat) : Nat
参数：m : Multiset Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `multinomial` coefficients on `Multiset ℕ`.
-/
def multinomial (m : Multiset ℕ) : ℕ := Quot.liftOn m List.multinomial <| fun l l' h ↦ by
  induction h with
  | nil => simp
  | @cons x l l' hl hl' => simp [List.multinomial_cons, hl', hl.sum_nat]
  | @swap x y l =>
    simp only [List.multinomial_cons, ← mul_assoc, List.sum_cons]
    rw [← Nat.choose_symm (Nat.le_add_right y _), add_tsub_cancel_left]
    rw [add_left_comm, Nat.choose_mul (Nat.le_add_right _ _), add_tsub_cancel_left]
    simp [← Nat.choose_symm (Nat.le_add_right _ _), add_tsub_cancel_left]
  | @trans l l' l'' h h' ih ih' => rw [ih, ih']
/-
**Multiset.multinomial_cons** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：multinomial_cons (x : Nat) (m : Multiset Nat) : (x ::ₘ m).multinomial = Na
t.choose (x + m.sum) x * m.multinomial
参数：x : Nat；m : Multiset Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.exists_rep`：∀ {α : Sort u} {s : Setoid α} (q : Quotient s), ∃ a
, ⟦a⟧ = q
· 使用定理 `List.multinomial_cons`：multinomial_cons (x : Nat) (l : List Nat) : (x ::
 l).multinomial = Nat.choose (x + l.sum) x * l.multinomial
-/
theorem multinomial_cons (x : ℕ) (m : Multiset ℕ) :
    (x ::ₘ m).multinomial = Nat.choose (x + m.sum) x * m.multinomial := by
  obtain ⟨l, rfl⟩ := Quotient.exists_rep m
  exact List.multinomial_cons x l

@[simp]
/-
**Multiset.multinomial_zero** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：multinomial_zero : Multiset.multinomial 0 = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem multinomial_zero : Multiset.multinomial 0 = 1 := rfl

@[simp]
/-
**Multiset.multinomial_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：multinomial_singleton (n : Nat) : Multiset.multinomial {n} = 1
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.multinomial_cons`：multinomial_cons (x : Nat) (m : Multiset Nat)
 : (x ::ₘ m).multinomial = Nat.choose (x + m.sum) x * m.multinomial
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Nat.choose_self`：choose_self (n : Nat) : choose n n = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem multinomial_singleton (n : ℕ) :
    Multiset.multinomial {n} = 1 := by
  simp [← cons_zero, multinomial_cons]
/-
**Multiset.multinomial_add** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：multinomial_add (m m' : Multiset Nat) : (m + m').multinomial = Nat.choose 
(m + m').sum m.sum * m.multinomial * m'.multinomial
参数：m m' : Multiset Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.zero_add`：∀ {α : Type u_1} (s : Multiset α), 0 + s = s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.choose_zero_right`：choose_zero_right (n : Nat) : choose n 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Multiset.cons_add`：cons_add (a : α) (s t : Multiset α) : a ::ₘ s + t = a
 ::ₘ (s + t)
· 使用定理 `Multiset.multinomial_cons`：multinomial_cons (x : Nat) (m : Multiset Nat)
 : (x ::ₘ m).multinomial = Nat.choose (x + m.sum) x * m.multinomial
· 使用定理 `Multiset.sum_add`：∀ {M : Type u_5} [inst : AddCommMonoid M] (s t : Multi
set M), (s + t).sum = s.sum + t.sum
· 使用定理 `Multiset.sum_cons`：∀ {M : Type u_3} [inst : AddCommMonoid M] (a : M) (s 
: Multiset M), (a ::ₘ s).sum = a + s.sum
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.choose_symm`：choose_symm {n k : Nat} (hk : k <= n) : choose n (n - k
) = choose n k
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
· 使用定理 `add_tsub_cancel_left`：add_tsub_cancel_left (a b : α) : a + b - a = b
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Nat.choose_mul`：choose_mul {n k s : Nat} (hsk : s <= k) : n.choose k * k
.choose s = n.choose s * (n - s).choose (k - s)
-/
theorem multinomial_add (m m' : Multiset ℕ) :
    (m + m').multinomial = Nat.choose (m + m').sum m.sum * m.multinomial * m'.multinomial := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons x m hind =>
    simp only [cons_add, sum_cons, sum_add, multinomial_cons, hind, ← mul_assoc]
    congr 2
    rw [← Nat.choose_symm (Nat.le_add_right _ _), add_tsub_cancel_left, eq_comm,
      Nat.choose_mul (Nat.le_add_right _ _), ← Nat.choose_symm (Nat.le_add_right x _)]
    simp [add_tsub_cancel_left]
/-
**Multiset.multinomial_nsmul** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：multinomial_nsmul (k : Nat) (m : Multiset Nat) : (k • m).multinomial = Nat
.multinomial (Finset.range k) (fun _ => m.sum) * m.multinomial ^ k
参数：k : Nat；m : Multiset Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 0 • a = 0
· 使用定理 `Nat.multinomial_empty`：∀ {α : Type u_1} (f : α → ℕ), Nat.multinomial ∅ f
 = 1
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `succ_nsmul'`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M) (n : ℕ), (n +
 1) • a = a + n • a
· 使用定理 `Multiset.multinomial_add`：multinomial_add (m m' : Multiset Nat) : (m + m
').multinomial = Nat.choose (m + m').sum m.sum * m.multinomial * m'.multinomial
· 使用定理 `Finset.range_add_one`：range_add_one : range (n + 1) = insert n (range n)
· 使用引理 `Nat.multinomial_insert`：multinomial_insert [DecidableEq α] (ha : a ∉ s) 
(f : α -> Nat) : multinomial (insert a s) f = (f a + ∑ i in s, f i).choose (f a)
 * multinomi…
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Multiset.sum_add`：∀ {M : Type u_5} [inst : AddCommMonoid M] (s t : Multi
set M), (s + t).sum = s.sum + t.sum
· 使用定理 `Multiset.sum_nsmul`：∀ {M : Type u_5} [inst : AddCommMonoid M] (m : Multi
set M) (n : ℕ), (n • m).sum = n • m.sum
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
（共 40 条，此处仅展示前 30 条）
-/
theorem multinomial_nsmul (k : ℕ) (m : Multiset ℕ) :
    (k • m).multinomial = Nat.multinomial (Finset.range k) (fun _ ↦ m.sum) * m.multinomial ^ k := by
  induction k with
  | zero => simp
  | succ k hk =>
    rw [succ_nsmul', multinomial_add, hk, Finset.range_add_one,
      Nat.multinomial_insert (by simp), sum_add, sum_nsmul, pow_succ']
    simp [smul_eq_mul, Finset.sum_const, Finset.card_range]
    ring
/-
**Multiset.multinomial_nsmul_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：multinomial_nsmul_singleton (k n : Nat) : (k • {n} : Multiset Nat).multino
mial = Nat.multinomial (Finset.range k) (fun _ => n)
参数：k n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.multinomial_nsmul`：multinomial_nsmul (k : Nat) (m : Multiset Na
t) : (k • m).multinomial = Nat.multinomial (Finset.range k) (fun _ => m.sum) * m
.multinomial ^ k
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Multiset.sum_singleton`：∀ {M : Type u_3} [inst : AddCommMonoid M] (a : M
), {a}.sum = a
· 使用定理 `Multiset.multinomial_singleton`：multinomial_singleton (n : Nat) : Multis
et.multinomial {n} = 1
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem multinomial_nsmul_singleton (k n : ℕ) :
    (k • {n} : Multiset ℕ).multinomial = Nat.multinomial (Finset.range k) (fun _ ↦ n) := by
  simp [multinomial_nsmul]
/-
**Multiset.multinomial_pos** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：multinomial_pos (m : Multiset Nat) : 0 < m.multinomial
参数：m : Multiset Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.multinomial_cons`：multinomial_cons (x : Nat) (m : Multiset Nat)
 : (x ::ₘ m).multinomial = Nat.choose (x + m.sum) x * m.multinomial
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `Nat.choose_pos`：∀ {n k : ℕ}, k ≤ n → 0 < n.choose k
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
-/
theorem multinomial_pos (m : Multiset ℕ) : 0 < m.multinomial := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons x m h =>
    simp only [multinomial_cons, h, mul_pos_iff_of_pos_right]
    exact Nat.choose_pos (Nat.le_add_right x m.sum)

section PositivityExtension

open Mathlib.Meta.Positivity Qq in
/--
Positivity extension for `Multiset.multinomial`.
-/
@[positivity multinomial (_ : Multiset ℕ)]
meta def evalMultinomial : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => throwError "not PartialOrder ℕ" | some _ => do
  match u, α, e with
  | 0, ~q(ℕ), ~q(multinomial $a) =>
    assertInstancesCommute
    return .positive q(multinomial_pos $a)
  | _, _, _ => throwError "not multinomial"

end PositivityExtension

end Multiset

