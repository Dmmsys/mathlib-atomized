/-
Copyright (c) 2023 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Group.Torsion
public import Mathlib.Algebra.Module.Rat
public import Mathlib.Algebra.Order.Ring.NNRat
public import Mathlib.Algebra.Polynomial.Smeval
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Tactic.Field
public import Mathlib.Tactic.Module

/-!
# Binomial rings

In this file we introduce the binomial property as a mixin, and define the `multichoose`
and `choose` functions generalizing binomial coefficients.

According to our main reference [elliott2006binomial] (which lists many equivalent conditions), a
binomial ring is a torsion-free commutative ring `R` such that for any `x ∈ R` and any `k ∈ ℕ`, the
product `x(x-1)⋯(x-k+1)` is divisible by `k!`. The torsion-free condition lets us divide by `k!`
unambiguously, so we get uniquely defined binomial coefficients.

The defining condition doesn't require commutativity or associativity, and we get a theory with
essentially the same power by replacing subtraction with addition. Thus, we consider any additive
commutative monoid with a notion of natural number exponents in which multiplication by positive
integers is injective, and demand that the evaluation of the ascending Pochhammer polynomial
`X(X+1)⋯(X+(k-1))` at any element is divisible by `k!`. The quotient is called `multichoose r k`,
because for `r` a natural number, it is the number of multisets of cardinality `k` taken from a type
of cardinality `n`.

## Definitions

* `BinomialRing`: a mixin class specifying a suitable `multichoose` function.
* `Ring.multichoose`: the quotient of an ascending Pochhammer evaluation by a factorial.
* `Ring.choose`: the quotient of a descending Pochhammer evaluation by a factorial.

## Results

* Basic results with choose and multichoose, e.g., `choose_zero_right`
* Relations between choose and multichoose, negated input.
* Fundamental recursion: `choose_succ_succ`
* Chu-Vandermonde identity: `add_choose_eq`
* Pochhammer API

## References

* [J. Elliott, *Binomial rings, integer-valued polynomials, and λ-rings*][elliott2006binomial]

## TODO

Further results in Elliot's paper:
* A CommRing is binomial if and only if it admits a λ-ring structure with trivial Adams operations.
* The free commutative binomial ring on a set `X` is the ring of integer-valued polynomials in the
  variables `X`.  (also, noncommutative version?)
* Given a commutative binomial ring `A` and an `A`-algebra `B` that is complete with respect to an
  ideal `I`, formal exponentiation induces an `A`-module structure on the multiplicative subgroup
  `1 + I`.

-/

@[expose] public section

open Function Polynomial

/-- A binomial ring is a ring for which ascending Pochhammer evaluations are uniquely divisible by
suitable factorials. We define this notion as a mixin for additive commutative monoids with natural
number powers, but retain the ring name. We introduce `Ring.multichoose` as the uniquely defined
quotient. -/
/-
**BinomialRing** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) → [AddCommMonoid R] → [Pow R ℕ] → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A binomial ring is a ring for which ascending Pochhammer evaluations are uniquel
y divisible by
suitable factorials. We define this notion as a mixin for additive commutative m
onoids with natural
number powers, but retain the ring name. We introduce `Ring.multichoose` as the 
uniquely defined
quotient.
-/
class BinomialRing (R : Type*) [AddCommMonoid R] [Pow R ℕ] where
  -- This base class has been demoted to a field, to avoid creating
  -- an expensive global instance.
  [toIsAddTorsionFree : IsAddTorsionFree R]
  /-- A multichoose function, giving the quotient of Pochhammer evaluations by factorials. -/
  multichoose : R → ℕ → R
  /-- The `n`th ascending Pochhammer polynomial evaluated at any element is divisible by `n!` -/
  factorial_nsmul_multichoose (r : R) (n : ℕ) :
    n.factorial • multichoose r n = (ascPochhammer ℕ n).smeval r

-- This is only a local instance as it otherwise causes significant slow downs
-- to every call to `grind` involving a ring. Please do not make it a global instance.
-- (~1500 heartbeats measured on `nightly-testing-2025-09-09`.)
attribute [local instance] BinomialRing.toIsAddTorsionFree

section Multichoose

namespace Ring

variable {R : Type*} [AddCommMonoid R] [Pow R ℕ] [BinomialRing R]

/-- The multichoose function is the quotient of ascending Pochhammer evaluation by the corresponding
factorial. When applied to natural numbers, `multichoose k n` describes choosing a multiset of `n`
items from a type of size `k`, i.e., choosing with replacement. -/
/-
**Ring.multichoose** 是 Mathlib 中的一个定义，位于命名空间 `Ring`。
形式化陈述：multichoose (r : R) (n : Nat) : R
参数：r : R；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multichoose function is the quotient of ascending Pochhammer evaluation by t
he corresponding
factorial. When applied to natural numbers, `multichoose k n` describes choosing
 a multiset of `n`
items from a type of size `k`, i.e., choosing with replacement.
-/
def multichoose (r : R) (n : ℕ) : R := BinomialRing.multichoose r n

@[simp]
/-
**Ring.multichoose_eq_multichoose** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：multichoose_eq_multichoose (r : R) (n : Nat) : BinomialRing.multichoose r 
n = multichoose r n
参数：r : R；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem multichoose_eq_multichoose (r : R) (n : ℕ) :
    BinomialRing.multichoose r n = multichoose r n := rfl
/-
**Ring.factorial_nsmul_multichoose_eq_ascPochhammer** 是 Mathlib 中的一个定理，位于命名空间 `R
ing`。
形式化陈述：factorial_nsmul_multichoose_eq_ascPochhammer (r : R) (n : Nat) : n.factori
al • multichoose r n = (ascPochhammer Nat n).smeval r
参数：r : R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BinomialRing.factorial_nsmul_multichoose`：∀ {R : Type u_1} {inst : AddCo
mmMonoid R} {inst_1 : Pow R ℕ} [self : BinomialRing R] (r : R) (n : ℕ),   n.fact
orial • BinomialRing.multichoo…
-/
theorem factorial_nsmul_multichoose_eq_ascPochhammer (r : R) (n : ℕ) :
    n.factorial • multichoose r n = (ascPochhammer ℕ n).smeval r :=
  BinomialRing.factorial_nsmul_multichoose r n

@[simp]
/-
**Ring.multichoose_zero_right'** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：multichoose_zero_right' (r : R) : multichoose r 0 = r ^ 0
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nsmul_right_inj`：∀ {M : Type u_1} [inst : AddMonoid M] [IsAddTorsionFree
 M] {n : ℕ} {a b : M}, n ≠ 0 → (n • a = n • b ↔ a = b)
· 使用定理 `BinomialRing.toIsAddTorsionFree`：∀ {R : Type u_1} {inst : AddCommMonoid 
R} {inst_1 : Pow R ℕ} [self : BinomialRing R], IsAddTorsionFree R
· 使用定理 `Nat.factorial_ne_zero`：factorial_ne_zero (n : Nat) : n ! != 0
· 使用定理 `Ring.factorial_nsmul_multichoose_eq_ascPochhammer`：factorial_nsmul_multi
choose_eq_ascPochhammer (r : R) (n : Nat) : n.factorial • multichoose r n = (asc
Pochhammer Nat n).smeval r
· 使用定理 `ascPochhammer_zero`：ascPochhammer_zero : ascPochhammer S 0 = 1
· 使用定理 `Polynomial.smeval_one`：smeval_one : (1 : R[X]).smeval x = 1 • x ^ 0
· 使用定理 `Nat.factorial.eq_1`：Nat.factorial 0 = 1
-/
theorem multichoose_zero_right' (r : R) : multichoose r 0 = r ^ 0 := by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero 0),
    factorial_nsmul_multichoose_eq_ascPochhammer, ascPochhammer_zero, smeval_one, Nat.factorial]
/-
**Ring.multichoose_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：multichoose_zero_right [MulOneClass R] [NatPowAssoc R] (r : R) : multichoo
se r 0 = 1
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ring.multichoose_zero_right'`：multichoose_zero_right' (r : R) : multicho
ose r 0 = r ^ 0
· 使用定理 `npow_zero`：npow_zero (x : M) : x ^ 0 = 1
-/
theorem multichoose_zero_right [MulOneClass R] [NatPowAssoc R]
    (r : R) : multichoose r 0 = 1 := by
  rw [multichoose_zero_right', npow_zero]

@[simp]
/-
**Ring.multichoose_one_right'** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：multichoose_one_right' (r : R) : multichoose r 1 = r ^ 1
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nsmul_right_inj`：∀ {M : Type u_1} [inst : AddMonoid M] [IsAddTorsionFree
 M] {n : ℕ} {a b : M}, n ≠ 0 → (n • a = n • b ↔ a = b)
· 使用定理 `BinomialRing.toIsAddTorsionFree`：∀ {R : Type u_1} {inst : AddCommMonoid 
R} {inst_1 : Pow R ℕ} [self : BinomialRing R], IsAddTorsionFree R
· 使用定理 `Nat.factorial_ne_zero`：factorial_ne_zero (n : Nat) : n ! != 0
· 使用定理 `Ring.factorial_nsmul_multichoose_eq_ascPochhammer`：factorial_nsmul_multi
choose_eq_ascPochhammer (r : R) (n : Nat) : n.factorial • multichoose r n = (asc
Pochhammer Nat n).smeval r
· 使用定理 `ascPochhammer_one`：ascPochhammer_one : ascPochhammer S 1 = X
· 使用定理 `Polynomial.smeval_X`：smeval_X : (X : R[X]).smeval x = x ^ 1
· 使用定理 `Nat.factorial_one`：Nat.factorial 1 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem multichoose_one_right' (r : R) : multichoose r 1 = r ^ 1 := by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero 1),
    factorial_nsmul_multichoose_eq_ascPochhammer, ascPochhammer_one, smeval_X, Nat.factorial_one,
    one_smul]
/-
**Ring.multichoose_one_right** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：multichoose_one_right [MulOneClass R] [NatPowAssoc R] (r : R) : multichoos
e r 1 = r
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ring.multichoose_one_right'`：multichoose_one_right' (r : R) : multichoos
e r 1 = r ^ 1
· 使用定理 `npow_one`：npow_one (x : M) : x ^ 1 = x
-/
theorem multichoose_one_right [MulOneClass R] [NatPowAssoc R] (r : R) : multichoose r 1 = r := by
  rw [multichoose_one_right', npow_one]

variable {R : Type*} [NonAssocSemiring R] [Pow R ℕ] [NatPowAssoc R] [BinomialRing R]

@[simp]
/-
**Ring.multichoose_zero_succ** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：multichoose_zero_succ (k : Nat) : multichoose (0 : R) (k + 1) = 0
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nsmul_right_inj`：∀ {M : Type u_1} [inst : AddMonoid M] [IsAddTorsionFree
 M] {n : ℕ} {a b : M}, n ≠ 0 → (n • a = n • b ↔ a = b)
· 使用定理 `BinomialRing.toIsAddTorsionFree`：∀ {R : Type u_1} {inst : AddCommMonoid 
R} {inst_1 : Pow R ℕ} [self : BinomialRing R], IsAddTorsionFree R
· 使用定理 `Nat.factorial_ne_zero`：factorial_ne_zero (n : Nat) : n ! != 0
· 使用定理 `Ring.factorial_nsmul_multichoose_eq_ascPochhammer`：factorial_nsmul_multi
choose_eq_ascPochhammer (r : R) (n : Nat) : n.factorial • multichoose r n = (asc
Pochhammer Nat n).smeval r
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `ascPochhammer_succ_left`：ascPochhammer_succ_left (n : Nat) : ascPochhamm
er S (n + 1) = X * (ascPochhammer S n).comp (X + 1)
· 使用定理 `Polynomial.smeval_X_mul`：smeval_X_mul : (X * p).smeval x = x * p.smeval 
x
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
theorem multichoose_zero_succ (k : ℕ) : multichoose (0 : R) (k + 1) = 0 := by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero (k + 1)),
    factorial_nsmul_multichoose_eq_ascPochhammer, smul_zero, ascPochhammer_succ_left,
    smeval_X_mul, zero_mul]
/-
**Ring.ascPochhammer_succ_succ** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：ascPochhammer_succ_succ (r : R) (k : Nat) : smeval (ascPochhammer Nat (k +
 1)) (r + 1) = Nat.factorial (k + 1) • multichoose (r + 1) k + smeval (ascPochha
mmer Nat (k + 1)) r
参数：r : R；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ascPochhammer_succ_right`：ascPochhammer_succ_right (n : Nat) : ascPochha
mmer S (n + 1) = ascPochhammer S n * (X + (n : S[X]))
· 使用定理 `ascPochhammer_succ_left`：ascPochhammer_succ_left (n : Nat) : ascPochhamm
er S (n + 1) = X * (ascPochhammer S n).comp (X + 1)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.smeval_mul`：smeval_mul : (p * q).smeval x = p.smeval x * q.sm
eval x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.smeval_add`：smeval_add : (p + q).smeval x = p.smeval x + q.sm
eval x
· 使用定理 `Polynomial.smeval_X`：smeval_X : (X : R[X]).smeval x = x ^ 1
· 使用定理 `Polynomial.smeval_comp`：smeval_comp : (p.comp q).smeval x = p.smeval (q.
smeval x)
· 使用定理 `Nat.factorial.eq_2`：∀ (n : ℕ), n.succ.factorial = n.succ * n.factorial
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `Ring.factorial_nsmul_multichoose_eq_ascPochhammer`：factorial_nsmul_multi
choose_eq_ascPochhammer (r : R) (n : Nat) : n.factorial • multichoose r n = (asc
Pochhammer Nat n).smeval r
· 使用定理 `npow_one`：npow_one (x : M) : x ^ 1 = x
· 使用定理 `Polynomial.smeval_one`：smeval_one : (1 : R[X]).smeval x = 1 • x ^ 0
· 使用定理 `npow_zero`：npow_zero (x : M) : x ^ 0 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.C_eq_natCast`：C_eq_natCast (n : Nat) : C (n : R) = (n : R[X])
· 使用定理 `Polynomial.smeval_C`：smeval_C : (C r).smeval x = r • x ^ 0
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `nsmul_one`：∀ {A : Type u_2} [inst : AddMonoidWithOne A] (n : ℕ), n • 1 =
 ↑n
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `add_rotate'`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G), a
 + (b + c) = b + (c + a)
· 使用定理 `succ_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M) (n : ℕ), (n + 
1) • a = n • a + a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
（共 32 条，此处仅展示前 30 条）
-/
theorem ascPochhammer_succ_succ (r : R) (k : ℕ) :
    smeval (ascPochhammer ℕ (k + 1)) (r + 1) = Nat.factorial (k + 1) • multichoose (r + 1) k +
    smeval (ascPochhammer ℕ (k + 1)) r := by
  nth_rw 1 [ascPochhammer_succ_right, ascPochhammer_succ_left, mul_comm (ascPochhammer ℕ k)]
  simp only [smeval_mul, smeval_comp, smeval_add, smeval_X]
  rw [Nat.factorial, mul_smul, factorial_nsmul_multichoose_eq_ascPochhammer]
  simp only [smeval_one, npow_one, npow_zero, one_smul]
  rw [← C_eq_natCast, smeval_C, npow_zero, add_assoc, add_mul, add_comm 1, @nsmul_one, add_mul]
  rw [← @nsmul_eq_mul, @add_rotate', @succ_nsmul, add_assoc]
  simp_all only [Nat.cast_id, nsmul_eq_mul, one_mul]
/-
**Ring.multichoose_succ_succ** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：multichoose_succ_succ (r : R) (k : Nat) : multichoose (r + 1) (k + 1) = mu
ltichoose r (k + 1) + multichoose (r + 1) k
参数：r : R；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nsmul_right_inj`：∀ {M : Type u_1} [inst : AddMonoid M] [IsAddTorsionFree
 M] {n : ℕ} {a b : M}, n ≠ 0 → (n • a = n • b ↔ a = b)
· 使用定理 `BinomialRing.toIsAddTorsionFree`：∀ {R : Type u_1} {inst : AddCommMonoid 
R} {inst_1 : Pow R ℕ} [self : BinomialRing R], IsAddTorsionFree R
· 使用定理 `Nat.factorial_ne_zero`：factorial_ne_zero (n : Nat) : n ! != 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Ring.factorial_nsmul_multichoose_eq_ascPochhammer`：factorial_nsmul_multi
choose_eq_ascPochhammer (r : R) (n : Nat) : n.factorial • multichoose r n = (asc
Pochhammer Nat n).smeval r
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Ring.ascPochhammer_succ_succ`：ascPochhammer_succ_succ (r : R) (k : Nat) 
: smeval (ascPochhammer Nat (k + 1)) (r + 1) = Nat.factorial (k + 1) • multichoo
se (r + 1) k + sme…
-/
theorem multichoose_succ_succ (r : R) (k : ℕ) :
    multichoose (r + 1) (k + 1) = multichoose r (k + 1) + multichoose (r + 1) k := by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero (k + 1))]
  simp only [factorial_nsmul_multichoose_eq_ascPochhammer, smul_add]
  rw [add_comm (smeval (ascPochhammer ℕ (k + 1)) r), ascPochhammer_succ_succ r k]

@[simp]
/-
**Ring.multichoose_one** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：multichoose_one (k : Nat) : multichoose (1 : R) k = 1
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ring.multichoose_zero_right`：multichoose_zero_right [MulOneClass R] [Nat
PowAssoc R] (r : R) : multichoose r 0 = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Ring.multichoose_succ_succ`：multichoose_succ_succ (r : R) (k : Nat) : mu
ltichoose (r + 1) (k + 1) = multichoose r (k + 1) + multichoose (r + 1) k
· 使用定理 `Ring.multichoose_zero_succ`：multichoose_zero_succ (k : Nat) : multichoos
e (0 : R) (k + 1) = 0
-/
theorem multichoose_one (k : ℕ) : multichoose (1 : R) k = 1 := by
  induction k with
  | zero => exact multichoose_zero_right 1
  | succ n ih =>
    rw [show (1 : R) = 0 + 1 by exact (@zero_add R _ 1).symm, multichoose_succ_succ,
      multichoose_zero_succ, zero_add, zero_add, ih]
/-
**Ring.multichoose_two** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：multichoose_two (k : Nat) : multichoose (2 : R) k = k + 1
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ring.multichoose_zero_right`：multichoose_zero_right [MulOneClass R] [Nat
PowAssoc R] (r : R) : multichoose r 0 = 1
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_add_one_eq_two`：one_add_one_eq_two [AddMonoidWithOne R] : 1 + 1 = (2
 : R)
· 使用定理 `Ring.multichoose_succ_succ`：multichoose_succ_succ (r : R) (k : Nat) : mu
ltichoose (r + 1) (k + 1) = multichoose r (k + 1) + multichoose (r + 1) k
· 使用定理 `Ring.multichoose_one`：multichoose_one (k : Nat) : multichoose (1 : R) k 
= 1
· 使用定理 `Nat.cast_succ`：cast_succ (n : Nat) : ((succ n : Nat) : R) = n + 1
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem multichoose_two (k : ℕ) : multichoose (2 : R) k = k + 1 := by
  induction k with
  | zero =>
    rw [multichoose_zero_right, Nat.cast_zero, zero_add]
  | succ n ih =>
    rw [one_add_one_eq_two.symm, multichoose_succ_succ, multichoose_one, one_add_one_eq_two, ih,
      Nat.cast_succ, add_comm]

attribute [local instance] BinomialRing.toIsAddTorsionFree in
/-
**Ring.map_multichoose** 是 Mathlib 中的一个引理，位于命名空间 `Ring`。
形式化陈述：map_multichoose {R S F : Type*} [Ring R] [Ring S] [BinomialRing R] [Binomi
alRing S] [FunLike F R S] [RingHomClass F R S] (f : F) (a : R) (n : Nat) : f (Ri
ng.multichoose a n) = Ring.multichoose (f a) n
参数：f : F；a : R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nsmul_right_injective`：∀ {M : Type u_1} [inst : AddMonoid M] [IsAddTorsi
onFree M] {n : ℕ}, n ≠ 0 → Function.Injective fun a => n • a
· 使用定理 `BinomialRing.toIsAddTorsionFree`：∀ {R : Type u_1} {inst : AddCommMonoid 
R} {inst_1 : Pow R ℕ} [self : BinomialRing R], IsAddTorsionFree R
· 使用定理 `Nat.factorial_ne_zero`：factorial_ne_zero (n : Nat) : n ! != 0
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Ring.factorial_nsmul_multichoose_eq_ascPochhammer`：factorial_nsmul_multi
choose_eq_ascPochhammer (r : R) (n : Nat) : n.factorial • multichoose r n = (asc
Pochhammer Nat n).smeval r
· 使用定理 `Polynomial.hom_eval₂`：hom_eval₂ (x : S) : g (p.eval₂ f x) = p.eval₂ (g.c
omp f) (g x)
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
lemma map_multichoose {R S F : Type*} [Ring R] [Ring S] [BinomialRing R] [BinomialRing S]
    [FunLike F R S] [RingHomClass F R S] (f : F) (a : R) (n : ℕ) :
    f (Ring.multichoose a n) = Ring.multichoose (f a) n := by
  apply nsmul_right_injective n.factorial_ne_zero
  simp only [← map_nsmul, Ring.factorial_nsmul_multichoose_eq_ascPochhammer,
    ← Polynomial.eval₂_smulOneHom_eq_smeval, Polynomial.hom_eval₂, ← RingHom.coe_coe f]
  congr
  exact Subsingleton.elim _ _

end Ring

end Multichoose

section Pochhammer

namespace Polynomial

@[simp]
/-
**Polynomial.ascPochhammer_smeval_cast** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：ascPochhammer_smeval_cast (R : Type*) [Semiring R] {S : Type*} [NonAssocSe
miring S] [Pow S Nat] [Module R S] [IsScalarTower R S S] [NatPowAssoc S] (x : S)
 (n : Nat) : (ascPochhammer R n).smeval x = (ascPochhammer Nat n).smeval x
参数：R : Type*；x : S；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.smeval_one`：smeval_one : (1 : R[X]).smeval x = 1 • x ^ 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ascPochhammer_succ_right`：ascPochhammer_succ_right (n : Nat) : ascPochha
mmer S (n + 1) = ascPochhammer S n * (X + (n : S[X]))
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `Polynomial.smeval_add`：smeval_add : (p + q).smeval x = p.smeval x + q.sm
eval x
· 使用定理 `Polynomial.smeval_mul_X`：smeval_mul_X : (p * X).smeval x = p.smeval x * 
x
· 使用定理 `Polynomial.smeval_C_mul`：smeval_C_mul : (C r * p).smeval x = r • p.smeva
l x
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
-/
theorem ascPochhammer_smeval_cast (R : Type*) [Semiring R] {S : Type*} [NonAssocSemiring S]
    [Pow S ℕ] [Module R S] [IsScalarTower R S S] [NatPowAssoc S]
    (x : S) (n : ℕ) : (ascPochhammer R n).smeval x = (ascPochhammer ℕ n).smeval x := by
  induction n with
  | zero => simp only [ascPochhammer_zero, smeval_one]
  | succ n hn =>
    simp only [ascPochhammer_succ_right, mul_add, smeval_add, smeval_mul_X, ← Nat.cast_comm]
    simp only [← C_eq_natCast, smeval_C_mul, hn, Nat.cast_smul_eq_nsmul R n]
    simp only [nsmul_eq_mul, Nat.cast_id]

variable {R : Type*}
/-
**Polynomial.ascPochhammer_smeval_eq_eval** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`
。
形式化陈述：ascPochhammer_smeval_eq_eval [Semiring R] (r : R) (n : Nat) : (ascPochhamm
er Nat n).smeval r = (ascPochhammer R n).eval r
参数：r : R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval_eq_smeval`：eval_eq_smeval : p.eval r = p.smeval r
· 使用定理 `Polynomial.ascPochhammer_smeval_cast`：ascPochhammer_smeval_cast (R : Typ
e*) [Semiring R] {S : Type*} [NonAssocSemiring S] [Pow S Nat] [Module R S] [IsSc
alarTower R S S] [NatPowAs…
-/
theorem ascPochhammer_smeval_eq_eval [Semiring R] (r : R) (n : ℕ) :
    (ascPochhammer ℕ n).smeval r = (ascPochhammer R n).eval r := by
  rw [eval_eq_smeval, ascPochhammer_smeval_cast R]

variable [NonAssocRing R] [Pow R ℕ] [NatPowAssoc R]
/-
**Polynomial.descPochhammer_smeval_eq_ascPochhammer** 是 Mathlib 中的一个定理，位于命名空间 `P
olynomial`。
形式化陈述：descPochhammer_smeval_eq_ascPochhammer (r : R) (n : Nat) : (descPochhammer
 Int n).smeval r = (ascPochhammer Nat n).smeval (r - n + 1)
参数：r : R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.smeval_one`：smeval_one : (1 : R[X]).smeval x = 1 • x ^ 0
· 使用定理 `npow_zero`：npow_zero (x : M) : x ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.cast_succ`：cast_succ (n : Nat) : ((succ n : Nat) : R) = n + 1
· 使用定理 `sub_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b + c = a - (b - c)
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `descPochhammer_succ_right`：descPochhammer_succ_right (n : Nat) : descPoc
hhammer R (n + 1) = descPochhammer R n * (X - (n : R[X]))
· 使用定理 `Polynomial.smeval_mul`：smeval_mul : (p * q).smeval x = p.smeval x * q.sm
eval x
· 使用定理 `ascPochhammer_succ_left`：ascPochhammer_succ_left (n : Nat) : ascPochhamm
er S (n + 1) = X * (ascPochhammer S n).comp (X + 1)
· 使用定理 `Polynomial.X_mul`：X_mul : X * p = p * X
· 使用定理 `Polynomial.smeval_mul_X`：smeval_mul_X : (p * X).smeval x = p.smeval x * 
x
· 使用定理 `Polynomial.smeval_comp`：smeval_comp : (p.comp q).smeval x = p.smeval (q.
smeval x)
· 使用定理 `Polynomial.smeval_sub`：smeval_sub : (p - q).smeval x = p.smeval x - q.sm
eval x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.C_eq_natCast`：C_eq_natCast (n : Nat) : C (n : R) = (n : R[X])
· 使用定理 `Polynomial.smeval_add`：smeval_add : (p + q).smeval x = p.smeval x + q.sm
eval x
· 使用定理 `Polynomial.smeval_C`：smeval_C : (C r).smeval x = r • x ^ 0
· 使用定理 `Polynomial.smeval_X`：smeval_X : (X : R[X]).smeval x = x ^ 1
· 使用定理 `npow_one`：npow_one (x : M) : x ^ 1 = x
· 使用定理 `zsmul_one`：∀ {R : Type u_1} [inst : AddGroupWithOne R] (n : ℤ), n • 1 = 
↑n
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem descPochhammer_smeval_eq_ascPochhammer (r : R) (n : ℕ) :
    (descPochhammer ℤ n).smeval r = (ascPochhammer ℕ n).smeval (r - n + 1) := by
  induction n with
  | zero => simp only [descPochhammer_zero, ascPochhammer_zero, smeval_one, npow_zero]
  | succ n ih =>
    rw [Nat.cast_succ, sub_add, add_sub_cancel_right, descPochhammer_succ_right, smeval_mul, ih,
      ascPochhammer_succ_left, X_mul, smeval_mul_X, smeval_comp, smeval_sub, ← C_eq_natCast,
      smeval_add, smeval_one, smeval_C]
    simp only [smeval_X, npow_one, npow_zero, zsmul_one, Int.cast_natCast, one_smul]
/-
**Polynomial.descPochhammer_smeval_eq_descFactorial** 是 Mathlib 中的一个定理，位于命名空间 `P
olynomial`。
形式化陈述：descPochhammer_smeval_eq_descFactorial (n k : Nat) : (descPochhammer Int k
).smeval (n : R) = n.descFactorial k
参数：n k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `descPochhammer_zero`：descPochhammer_zero : descPochhammer R 0 = 1
· 使用定理 `Nat.descFactorial_zero`：descFactorial_zero (n : Nat) : n.descFactorial 0
 = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Polynomial.smeval_one`：smeval_one : (1 : R[X]).smeval x = 1 • x ^ 0
· 使用定理 `npow_zero`：npow_zero (x : M) : x ^ 0 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `descPochhammer_succ_right`：descPochhammer_succ_right (n : Nat) : descPoc
hhammer R (n + 1) = descPochhammer R n * (X - (n : R[X]))
· 使用定理 `Nat.descFactorial_succ`：descFactorial_succ (n k : Nat) : n.descFactorial
 (k + 1) = (n - k) * n.descFactorial k
· 使用定理 `Polynomial.smeval_mul`：smeval_mul : (p * q).smeval x = p.smeval x * q.sm
eval x
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Polynomial.smeval_sub`：smeval_sub : (p - q).smeval x = p.smeval x - q.sm
eval x
· 使用定理 `Polynomial.smeval_X`：smeval_X : (X : R[X]).smeval x = x ^ 1
· 使用定理 `Polynomial.smeval_natCast`：smeval_natCast (n : Nat) : (n : R[X]).smeval 
x = n • x ^ 0
· 使用定理 `npow_one`：npow_one (x : M) : x ^ 1 = x
· 使用定理 `nsmul_one`：∀ {A : Type u_2} [inst : AddMonoidWithOne A] (n : ℕ), n • 1 =
 ↑n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.descFactorial_eq_zero_iff_lt`：∀ {n k : ℕ}, n.descFactorial k = 0 ↔ n
 < k
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.cast_sub`：cast_sub {m n} (h : m <= n) : ((n - m : Nat) : R) = n - m
-/
theorem descPochhammer_smeval_eq_descFactorial (n k : ℕ) :
    (descPochhammer ℤ k).smeval (n : R) = n.descFactorial k := by
  induction k with
  | zero =>
    rw [descPochhammer_zero, Nat.descFactorial_zero, Nat.cast_one, smeval_one, npow_zero, one_smul]
  | succ k ih =>
    rw [descPochhammer_succ_right, Nat.descFactorial_succ, smeval_mul, ih, mul_comm, Nat.cast_mul,
      smeval_sub, smeval_X, smeval_natCast, npow_one, npow_zero, nsmul_one]
    by_cases! h : n < k
    · simp only [Nat.descFactorial_eq_zero_iff_lt.mpr h, Nat.cast_zero, zero_mul]
    · rw [Nat.cast_sub h]
/-
**Polynomial.ascPochhammer_smeval_neg_eq_descPochhammer** 是 Mathlib 中的一个定理，位于命名空
间 `Polynomial`。
形式化陈述：ascPochhammer_smeval_neg_eq_descPochhammer (r : R) (k : Nat) : (ascPochham
mer Nat k).smeval (-r) = Int.negOnePow k • (descPochhammer Int k).smeval r
参数：r : R；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.smeval_one`：smeval_one : (1 : R[X]).smeval x = 1 • x ^ 0
· 使用定理 `npow_zero`：npow_zero (x : M) : x ^ 0 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ascPochhammer_succ_right`：ascPochhammer_succ_right (n : Nat) : ascPochha
mmer S (n + 1) = ascPochhammer S n * (X + (n : S[X]))
· 使用定理 `Polynomial.smeval_mul`：smeval_mul : (p * q).smeval x = p.smeval x * q.sm
eval x
· 使用定理 `descPochhammer_succ_right`：descPochhammer_succ_right (n : Nat) : descPoc
hhammer R (n + 1) = descPochhammer R n * (X - (n : R[X]))
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Polynomial.smeval_add`：smeval_add : (p + q).smeval x = p.smeval x + q.sm
eval x
· 使用定理 `Polynomial.smeval_natCast`：smeval_natCast (n : Nat) : (n : R[X]).smeval 
x = n • x ^ 0
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Polynomial.smeval_X`：smeval_X : (X : R[X]).smeval x = x ^ 1
· 使用定理 `npow_one`：npow_one (x : M) : x ^ 1 = x
· 使用定理 `Polynomial.smeval_neg`：smeval_neg : (-p).smeval x = -p.smeval x
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_mul_comm`：neg_mul_comm (a b : α) : -a * b = a * -b
· 使用定理 `Int.natCast_add`：∀ (n m : ℕ), ↑(n + m) = ↑n + ↑m
· 使用定理 `Int.natCast_one`：↑1 = 1
· 使用引理 `Int.negOnePow_succ`：negOnePow_succ (n : Int) : (n + 1).negOnePow = -n.ne
gOnePow
（共 34 条，此处仅展示前 30 条）
-/
theorem ascPochhammer_smeval_neg_eq_descPochhammer (r : R) (k : ℕ) :
    (ascPochhammer ℕ k).smeval (-r) = Int.negOnePow k • (descPochhammer ℤ k).smeval r := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [ascPochhammer_succ_right, smeval_mul, ih, descPochhammer_succ_right, sub_eq_add_neg]
    have h : (X + (k : ℕ[X])).smeval (-r) = -(X + (-k : ℤ[X])).smeval r := by
      simp [smeval_natCast, add_comm]
    rw [h, ← neg_mul_comm, Int.natCast_add, Int.natCast_one, Int.negOnePow_succ, Units.neg_smul,
      Units.smul_def, Units.smul_def, ← smul_mul_assoc, neg_mul]

end Polynomial

end Pochhammer

section Basic_Instances

open Polynomial

/-
**Nat.instBinomialRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Nat.instBinomialRing : BinomialRing Nat where multichoose
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Nat.instBinomialRing : BinomialRing ℕ where
  multichoose := Nat.multichoose
  factorial_nsmul_multichoose r n := by
    rw [smul_eq_mul, Nat.multichoose_eq r n, ← Nat.descFactorial_eq_factorial_mul_choose,
      ← eval_eq_smeval r (ascPochhammer ℕ n), ascPochhammer_nat_eq_descFactorial]

/-- The multichoose function for integers. -/
/-
**Int.multichoose** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Int.multichoose (n : Int) (k : Nat) : Int
参数：n : Int；k : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multichoose function for integers.
-/
def Int.multichoose (n : ℤ) (k : ℕ) : ℤ :=
  match n with
  | ofNat n => (Nat.choose (n + k - 1) k : ℤ)
  | negSucc n => Int.negOnePow k * Nat.choose (n + 1) k
/-
**Int.instBinomialRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Int.instBinomialRing : BinomialRing Int where multichoose
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Int.instBinomialRing : BinomialRing ℤ where
  multichoose := Int.multichoose
  factorial_nsmul_multichoose r k := by
    rw [Int.multichoose.eq_def, nsmul_eq_mul]
    cases r with
    | ofNat n =>
      simp only [Int.ofNat_eq_natCast, Int.ofNat_mul_ofNat]
      rw [← Nat.descFactorial_eq_factorial_mul_choose, smeval_at_natCast, ← eval_eq_smeval n,
        ascPochhammer_nat_eq_descFactorial]
    | negSucc n =>
      simp only
      rw [mul_comm, mul_assoc, ← Nat.cast_mul, mul_comm _ (k.factorial),
        ← Nat.descFactorial_eq_factorial_mul_choose, ← descPochhammer_smeval_eq_descFactorial,
        ← Int.neg_ofNat_succ, ascPochhammer_smeval_neg_eq_descPochhammer]
      norm_cast

attribute [local instance] IsAddTorsionFree.of_module_nnrat
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance {R : Type*} [AddCommMonoid R] [Module ℚ≥0 R] [Pow R ℕ] : BinomialRing R where
  multichoose r n := (n.factorial : ℚ≥0)⁻¹ • Polynomial.smeval (ascPochhammer ℕ n) r
  factorial_nsmul_multichoose r n := by
    match_scalars
    field

end Basic_Instances

section Neg

namespace Ring

open Polynomial

variable {R : Type*} [NonAssocRing R] [Pow R ℕ] [BinomialRing R]

@[simp]
/-
**Ring.smeval_ascPochhammer_self_neg** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：∀ (n : ℕ), (ascPochhammer ℕ n).smeval (-↑n) = (-1) ^ n * ↑n.factorial
参数：n : ℕ；ascPochhammer ℕ n；-↑n；-1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smeval_ascPochhammer_self_neg : ∀ n : ℕ,
    smeval (ascPochhammer ℕ n) (-n : ℤ) = (-1) ^ n * n.factorial
  | 0 => by
    rw [Nat.cast_zero, neg_zero, ascPochhammer_zero, Nat.factorial_zero, smeval_one, pow_zero,
      one_smul, pow_zero, Nat.cast_one, one_mul]
  | n + 1 => by
    rw [ascPochhammer_succ_left, smeval_X_mul, smeval_comp, smeval_add, smeval_X, smeval_one,
      pow_zero, pow_one, one_smul, Nat.cast_add, Nat.cast_one, neg_add_rev, neg_add_cancel_comm,
      smeval_ascPochhammer_self_neg n, ← mul_assoc, mul_comm _ ((-1) ^ n),
      show (-1 + -↑n = (-1 : ℤ) * (n + 1)) by lia, ← mul_assoc, pow_add, pow_one,
      Nat.factorial, Nat.cast_mul, ← mul_assoc, Nat.cast_succ]

@[simp]
/-
**Ring.smeval_ascPochhammer_succ_neg** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：smeval_ascPochhammer_succ_neg (n : Nat) : smeval (ascPochhammer Nat (n + 1
)) (-n : Int) = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ascPochhammer_succ_right`：ascPochhammer_succ_right (n : Nat) : ascPochha
mmer S (n + 1) = ascPochhammer S n * (X + (n : S[X]))
· 使用定理 `Polynomial.smeval_mul`：smeval_mul : (p * q).smeval x = p.smeval x * q.sm
eval x
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Polynomial.smeval_add`：smeval_add : (p + q).smeval x = p.smeval x + q.sm
eval x
· 使用定理 `Polynomial.smeval_X`：smeval_X : (X : R[X]).smeval x = x ^ 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.C_eq_natCast`：C_eq_natCast (n : Nat) : C (n : R) = (n : R[X])
· 使用定理 `Polynomial.smeval_C`：smeval_C : (C r).smeval x = r • x ^ 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Nat.cast_id`：Nat.cast_id (n : Nat) : n.cast = n
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem smeval_ascPochhammer_succ_neg (n : ℕ) :
    smeval (ascPochhammer ℕ (n + 1)) (-n : ℤ) = 0 := by
  rw [ascPochhammer_succ_right, smeval_mul, smeval_add, smeval_X, ← C_eq_natCast, smeval_C,
    pow_zero, pow_one, Nat.cast_id, nsmul_eq_mul, mul_one, neg_add_cancel, mul_zero]
/-
**Ring.smeval_ascPochhammer_neg_add** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：∀ (n k : ℕ), (ascPochhammer ℕ (n + k + 1)).smeval (-↑n) = 0
参数：n k : ℕ；ascPochhammer ℕ (n + k + 1)；-↑n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smeval_ascPochhammer_neg_add (n : ℕ) : ∀ k : ℕ,
    smeval (ascPochhammer ℕ (n + k + 1)) (-n : ℤ) = 0
  | 0 => by
    rw [add_zero, smeval_ascPochhammer_succ_neg]
  | k + 1 => by
    rw [ascPochhammer_succ_right, smeval_mul, ← add_assoc, smeval_ascPochhammer_neg_add n k,
      zero_mul]

@[simp]
/-
**Ring.smeval_ascPochhammer_neg_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：smeval_ascPochhammer_neg_of_lt {n k : Nat} (h : n < k) : smeval (ascPochha
mmer Nat k) (-n : Int) = 0
参数：h : n < k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ring.smeval_ascPochhammer_neg_add`：∀ (n k : ℕ), (ascPochhammer ℕ (n + k 
+ 1)).smeval (-↑n) = 0
-/
theorem smeval_ascPochhammer_neg_of_lt {n k : ℕ} (h : n < k) :
    smeval (ascPochhammer ℕ k) (-n : ℤ) = 0 := by
  rw [show k = n + (k - n - 1) + 1 by lia, smeval_ascPochhammer_neg_add]
/-
**Ring.smeval_ascPochhammer_nat_cast** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：smeval_ascPochhammer_nat_cast {R} [NonAssocSemiring R] [Pow R Nat] [NatPow
Assoc R] (n k : Nat) : smeval (ascPochhammer Nat k) (n : R) = smeval (ascPochham
mer Nat k) n
参数：n k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.smeval_at_natCast`：smeval_at_natCast (q : Nat[X]) : forall (n
 : Nat), q.smeval (n : S) = q.smeval n
-/
theorem smeval_ascPochhammer_nat_cast {R} [NonAssocSemiring R] [Pow R ℕ] [NatPowAssoc R] (n k : ℕ) :
    smeval (ascPochhammer ℕ k) (n : R) = smeval (ascPochhammer ℕ k) n := by
  rw [smeval_at_natCast (ascPochhammer ℕ k) n]
/-
**Ring.multichoose_neg_self** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：multichoose_neg_self (n : Nat) : multichoose (-n : Int) n = (-1) ^ n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nsmul_right_inj`：∀ {M : Type u_1} [inst : AddMonoid M] [IsAddTorsionFree
 M] {n : ℕ} {a b : M}, n ≠ 0 → (n • a = n • b ↔ a = b)
· 使用定理 `Nat.factorial_ne_zero`：factorial_ne_zero (n : Nat) : n ! != 0
· 使用定理 `Ring.factorial_nsmul_multichoose_eq_ascPochhammer`：factorial_nsmul_multi
choose_eq_ascPochhammer (r : R) (n : Nat) : n.factorial • multichoose r n = (asc
Pochhammer Nat n).smeval r
· 使用定理 `Ring.smeval_ascPochhammer_self_neg`：∀ (n : ℕ), (ascPochhammer ℕ n).smeva
l (-↑n) = (-1) ^ n * ↑n.factorial
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `Nat.cast_comm`：cast_comm (n : Nat) (x : α) : (n : α) * x = x * n
-/
theorem multichoose_neg_self (n : ℕ) : multichoose (-n : ℤ) n = (-1) ^ n := by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero _),
    factorial_nsmul_multichoose_eq_ascPochhammer, smeval_ascPochhammer_self_neg, nsmul_eq_mul,
    Nat.cast_comm]

@[simp]
/-
**Ring.multichoose_neg_succ** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：multichoose_neg_succ (n : Nat) : multichoose (-n : Int) (n + 1) = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nsmul_right_inj`：∀ {M : Type u_1} [inst : AddMonoid M] [IsAddTorsionFree
 M] {n : ℕ} {a b : M}, n ≠ 0 → (n • a = n • b ↔ a = b)
· 使用定理 `Nat.factorial_ne_zero`：factorial_ne_zero (n : Nat) : n ! != 0
· 使用定理 `Ring.factorial_nsmul_multichoose_eq_ascPochhammer`：factorial_nsmul_multi
choose_eq_ascPochhammer (r : R) (n : Nat) : n.factorial • multichoose r n = (asc
Pochhammer Nat n).smeval r
· 使用定理 `Ring.smeval_ascPochhammer_succ_neg`：smeval_ascPochhammer_succ_neg (n : N
at) : smeval (ascPochhammer Nat (n + 1)) (-n : Int) = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
theorem multichoose_neg_succ (n : ℕ) : multichoose (-n : ℤ) (n + 1) = 0 := by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero _),
    factorial_nsmul_multichoose_eq_ascPochhammer, smeval_ascPochhammer_succ_neg, smul_zero]
/-
**Ring.multichoose_neg_add** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：multichoose_neg_add (n k : Nat) : multichoose (-n : Int) (n + k + 1) = 0
参数：n k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nsmul_right_inj`：∀ {M : Type u_1} [inst : AddMonoid M] [IsAddTorsionFree
 M] {n : ℕ} {a b : M}, n ≠ 0 → (n • a = n • b ↔ a = b)
· 使用定理 `Nat.factorial_ne_zero`：factorial_ne_zero (n : Nat) : n ! != 0
· 使用定理 `Ring.factorial_nsmul_multichoose_eq_ascPochhammer`：factorial_nsmul_multi
choose_eq_ascPochhammer (r : R) (n : Nat) : n.factorial • multichoose r n = (asc
Pochhammer Nat n).smeval r
· 使用定理 `Ring.smeval_ascPochhammer_neg_add`：∀ (n k : ℕ), (ascPochhammer ℕ (n + k 
+ 1)).smeval (-↑n) = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
theorem multichoose_neg_add (n k : ℕ) : multichoose (-n : ℤ) (n + k + 1) = 0 := by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero (n + k + 1)),
    factorial_nsmul_multichoose_eq_ascPochhammer, smeval_ascPochhammer_neg_add, smul_zero]

@[simp]
/-
**Ring.multichoose_neg_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：multichoose_neg_of_lt (n k : Nat) (h : n < k) : multichoose (-n : Int) k =
 0
参数：n k : Nat；h : n < k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nsmul_right_inj`：∀ {M : Type u_1} [inst : AddMonoid M] [IsAddTorsionFree
 M] {n : ℕ} {a b : M}, n ≠ 0 → (n • a = n • b ↔ a = b)
· 使用定理 `Nat.factorial_ne_zero`：factorial_ne_zero (n : Nat) : n ! != 0
· 使用定理 `Ring.factorial_nsmul_multichoose_eq_ascPochhammer`：factorial_nsmul_multi
choose_eq_ascPochhammer (r : R) (n : Nat) : n.factorial • multichoose r n = (asc
Pochhammer Nat n).smeval r
· 使用定理 `Ring.smeval_ascPochhammer_neg_of_lt`：smeval_ascPochhammer_neg_of_lt {n k
 : Nat} (h : n < k) : smeval (ascPochhammer Nat k) (-n : Int) = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
theorem multichoose_neg_of_lt (n k : ℕ) (h : n < k) : multichoose (-n : ℤ) k = 0 := by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero k),
    factorial_nsmul_multichoose_eq_ascPochhammer, smeval_ascPochhammer_neg_of_lt h, smul_zero]
/-
**Ring.multichoose_succ_neg_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：multichoose_succ_neg_natCast [NatPowAssoc R] (n : Nat) : multichoose (-n :
 R) (n + 1) = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nsmul_right_inj`：∀ {M : Type u_1} [inst : AddMonoid M] [IsAddTorsionFree
 M] {n : ℕ} {a b : M}, n ≠ 0 → (n • a = n • b ↔ a = b)
· 使用定理 `BinomialRing.toIsAddTorsionFree`：∀ {R : Type u_1} {inst : AddCommMonoid 
R} {inst_1 : Pow R ℕ} [self : BinomialRing R], IsAddTorsionFree R
· 使用定理 `Nat.factorial_ne_zero`：factorial_ne_zero (n : Nat) : n ! != 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Ring.factorial_nsmul_multichoose_eq_ascPochhammer`：factorial_nsmul_multi
choose_eq_ascPochhammer (r : R) (n : Nat) : n.factorial • multichoose r n = (asc
Pochhammer Nat n).smeval r
· 使用定理 `Polynomial.smeval_neg_nat`：smeval_neg_nat (S : Type*) [NonAssocRing S] [
Pow S Nat] [NatPowAssoc S] (q : Nat[X]) (n : Nat) : q.smeval (-(n : S)) = q.smev
al (-n : Int)
· 使用定理 `Ring.smeval_ascPochhammer_succ_neg`：smeval_ascPochhammer_succ_neg (n : N
at) : smeval (ascPochhammer Nat (n + 1)) (-n : Int) = 0
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
-/
theorem multichoose_succ_neg_natCast [NatPowAssoc R] (n : ℕ) :
    multichoose (-n : R) (n + 1) = 0 := by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero (n + 1)), smul_zero,
    factorial_nsmul_multichoose_eq_ascPochhammer, smeval_neg_nat,
    smeval_ascPochhammer_succ_neg n, Int.cast_zero]
/-
**Ring.smeval_ascPochhammer_int_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：∀ {R : Type u_2} [inst : NonAssocRing R] [inst_1 : Pow R ℕ] [NatPowAssoc R
] (r : R) (n : ℕ),   (ascPochhammer ℤ n).smeval r = (ascPochhammer ℕ n).smeval r
参数：r : R；n : ℕ；ascPochhammer ℤ n；ascPochhammer ℕ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smeval_ascPochhammer_int_ofNat {R} [NonAssocRing R] [Pow R ℕ] [NatPowAssoc R] (r : R) :
    ∀ n : ℕ, smeval (ascPochhammer ℤ n) r = smeval (ascPochhammer ℕ n) r
  | 0 => by
    simp only [ascPochhammer_zero, smeval_one]
  | n + 1 => by
    simp only [ascPochhammer_succ_right, smeval_mul]
    rw [smeval_ascPochhammer_int_ofNat r n]
    simp only [smeval_add, smeval_X, ← C_eq_natCast, smeval_C, natCast_zsmul, nsmul_eq_mul,
      Nat.cast_id]

end Ring

end Neg

section Choose

namespace Ring

open Polynomial

variable {R : Type*}

section

/-- The binomial coefficient `choose r n` generalizes the natural number `Nat.choose` function,
  interpreted in terms of choosing without replacement. -/
/-
**Ring.choose** 是 Mathlib 中的一个定义，位于命名空间 `Ring`。
形式化陈述：choose [AddCommGroupWithOne R] [Pow R Nat] [BinomialRing R] (r : R) (n : N
at) : R
参数：r : R；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The binomial coefficient `choose r n` generalizes the natural number `Nat.choose
` function,
  interpreted in terms of choosing without replacement.
-/
def choose [AddCommGroupWithOne R] [Pow R ℕ] [BinomialRing R] (r : R) (n : ℕ) : R :=
  multichoose (r - n + 1) n

variable [NonAssocRing R] [Pow R ℕ] [BinomialRing R]
/-
**Ring.multichoose_eq** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：multichoose_eq (r : R) (n : Nat) : multichoose r n = choose (r + n - 1) n
参数：r : R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ring.choose.eq_1`：∀ {R : Type u_1} [inst : AddCommGroupWithOne R] [inst_
1 : Pow R ℕ] [inst_2 : BinomialRing R] (r : R) (n : ℕ),   Ring.choose r n = Ring
.multi…
· 使用定理 `_private.Mathlib.RingTheory.Binomial.0.Ring.multichoose_eq._abel_1_2`：∀ 
{R : Type u_1} [inst : NonAssocRing R] (r : R) (n : ℕ), r = r + ↑n - 1 - ↑n + 1
-/
theorem multichoose_eq (r : R) (n : ℕ) : multichoose r n = choose (r + n - 1) n := by
  rw [choose]
  congr
  abel
/-
**Ring.descPochhammer_eq_factorial_smul_choose** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：descPochhammer_eq_factorial_smul_choose [NatPowAssoc R] (r : R) (n : Nat) 
: (descPochhammer Int n).smeval r = n.factorial • choose r n
参数：r : R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ring.choose.eq_1`：∀ {R : Type u_1} [inst : AddCommGroupWithOne R] [inst_
1 : Pow R ℕ] [inst_2 : BinomialRing R] (r : R) (n : ℕ),   Ring.choose r n = Ring
.multi…
· 使用定理 `Ring.factorial_nsmul_multichoose_eq_ascPochhammer`：factorial_nsmul_multi
choose_eq_ascPochhammer (r : R) (n : Nat) : n.factorial • multichoose r n = (asc
Pochhammer Nat n).smeval r
· 使用定理 `descPochhammer_eq_ascPochhammer`：descPochhammer_eq_ascPochhammer (n : Na
t) : descPochhammer Int n = (ascPochhammer Int n).comp ((X : Int[X]) - n + 1)
· 使用定理 `Polynomial.smeval_comp`：smeval_comp : (p.comp q).smeval x = p.smeval (q.
smeval x)
· 使用定理 `add_comm_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c :
 α), a - b + c = a + (c - b)
· 使用定理 `Polynomial.smeval_add`：smeval_add : (p + q).smeval x = p.smeval x + q.sm
eval x
· 使用定理 `Polynomial.smeval_X`：smeval_X : (X : R[X]).smeval x = x ^ 1
· 使用定理 `npow_one`：npow_one (x : M) : x ^ 1 = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.C_eq_natCast`：C_eq_natCast (n : Nat) : C (n : R) = (n : R[X])
· 使用定理 `Polynomial.C_1`：C_1 : C (1 : R) = 1
· 使用定理 `Polynomial.C_sub`：C_sub : C (a - b) = C a - C b
· 使用定理 `Polynomial.smeval_C`：smeval_C : (C r).smeval x = r • x ^ 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `npow_zero`：npow_zero (x : M) : x ^ 0 = 1
· 使用定理 `zsmul_one`：∀ {R : Type u_1} [inst : AddGroupWithOne R] (n : ℤ), n • 1 = 
↑n
· 使用定理 `Int.cast_sub`：cast_sub (m n) : ((m - n : Int) : R) = m - n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.ascPochhammer_smeval_cast`：ascPochhammer_smeval_cast (R : Typ
e*) [Semiring R] {S : Type*} [NonAssocSemiring S] [Pow S Nat] [Module R S] [IsSc
alarTower R S S] [NatPowAs…
-/
theorem descPochhammer_eq_factorial_smul_choose [NatPowAssoc R] (r : R) (n : ℕ) :
    (descPochhammer ℤ n).smeval r = n.factorial • choose r n := by
  rw [choose, factorial_nsmul_multichoose_eq_ascPochhammer, descPochhammer_eq_ascPochhammer,
    smeval_comp, add_comm_sub, smeval_add, smeval_X, npow_one]
  have h : smeval (1 - n : Polynomial ℤ) r = 1 - n := by
    rw [← C_eq_natCast, ← C_1, ← C_sub, smeval_C]
    simp only [npow_zero, zsmul_one, Int.cast_sub, Int.cast_one, Int.cast_natCast]
  rw [h, ascPochhammer_smeval_cast, add_comm_sub]
/-
**Ring.choose_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：choose_natCast [NatPowAssoc R] (n k : Nat) : choose (n : R) k = Nat.choose
 n k
参数：n k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nsmul_right_inj`：∀ {M : Type u_1} [inst : AddMonoid M] [IsAddTorsionFree
 M] {n : ℕ} {a b : M}, n ≠ 0 → (n • a = n • b ↔ a = b)
· 使用定理 `BinomialRing.toIsAddTorsionFree`：∀ {R : Type u_1} {inst : AddCommMonoid 
R} {inst_1 : Pow R ℕ} [self : BinomialRing R], IsAddTorsionFree R
· 使用定理 `Nat.factorial_ne_zero`：factorial_ne_zero (n : Nat) : n ! != 0
· 使用定理 `Ring.descPochhammer_eq_factorial_smul_choose`：descPochhammer_eq_factoria
l_smul_choose [NatPowAssoc R] (r : R) (n : Nat) : (descPochhammer Int n).smeval 
r = n.factorial • choose r n
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Nat.descFactorial_eq_factorial_mul_choose`：descFactorial_eq_factorial_mu
l_choose (n k : Nat) : n.descFactorial k = k ! * n.choose k
· 使用定理 `Polynomial.descPochhammer_smeval_eq_descFactorial`：descPochhammer_smeval
_eq_descFactorial (n k : Nat) : (descPochhammer Int k).smeval (n : R) = n.descFa
ctorial k
-/
theorem choose_natCast [NatPowAssoc R] (n k : ℕ) : choose (n : R) k = Nat.choose n k := by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero k),
    ← descPochhammer_eq_factorial_smul_choose, nsmul_eq_mul, ← Nat.cast_mul,
    ← Nat.descFactorial_eq_factorial_mul_choose, ← descPochhammer_smeval_eq_descFactorial]

@[simp]
/-
**Ring.choose_zero_right'** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：choose_zero_right' (r : R) : choose r 0 = (r + 1) ^ 0
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nsmul_right_inj`：∀ {M : Type u_1} [inst : AddMonoid M] [IsAddTorsionFree
 M] {n : ℕ} {a b : M}, n ≠ 0 → (n • a = n • b ↔ a = b)
· 使用定理 `BinomialRing.toIsAddTorsionFree`：∀ {R : Type u_1} {inst : AddCommMonoid 
R} {inst_1 : Pow R ℕ} [self : BinomialRing R], IsAddTorsionFree R
· 使用定理 `Nat.factorial_ne_zero`：factorial_ne_zero (n : Nat) : n ! != 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Ring.multichoose_zero_right'`：multichoose_zero_right' (r : R) : multicho
ose r 0 = r ^ 0
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem choose_zero_right' (r : R) : choose r 0 = (r + 1) ^ 0 := by
  dsimp only [choose]
  rw [← nsmul_right_inj (Nat.factorial_ne_zero 0)]
  simp
/-
**Ring.choose_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：choose_zero_right [NatPowAssoc R] (r : R) : choose r 0 = 1
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ring.choose_zero_right'`：choose_zero_right' (r : R) : choose r 0 = (r + 
1) ^ 0
· 使用定理 `npow_zero`：npow_zero (x : M) : x ^ 0 = 1
-/
theorem choose_zero_right [NatPowAssoc R] (r : R) : choose r 0 = 1 := by
  rw [choose_zero_right', npow_zero]

@[simp]
/-
**Ring.choose_zero_succ** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：choose_zero_succ (R) [NonAssocRing R] [Pow R Nat] [NatPowAssoc R] [Binomia
lRing R] (n : Nat) : choose (0 : R) (n + 1) = 0
参数：R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ring.choose.eq_1`：∀ {R : Type u_1} [inst : AddCommGroupWithOne R] [inst_
1 : Pow R ℕ] [inst_2 : BinomialRing R] (r : R) (n : ℕ),   Ring.choose r n = Ring
.multi…
· 使用定理 `Nat.cast_succ`：cast_succ (n : Nat) : ((succ n : Nat) : R) = n + 1
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `neg_add`：neg_add {R} [CommRing R] {a₁ a₂ b₁ b₂ : R} (_ : -a₁ = b₁) (_ : 
-a₂ = b₂) : -(a₁ + a₂) = b₁ + b₂
· 使用定理 `neg_add_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ -b + b = a
· 使用定理 `Ring.multichoose_succ_neg_natCast`：multichoose_succ_neg_natCast [NatPowA
ssoc R] (n : Nat) : multichoose (-n : R) (n + 1) = 0
-/
theorem choose_zero_succ (R) [NonAssocRing R] [Pow R ℕ] [NatPowAssoc R] [BinomialRing R]
    (n : ℕ) : choose (0 : R) (n + 1) = 0 := by
  rw [choose, Nat.cast_succ, zero_sub, neg_add, neg_add_cancel_right, multichoose_succ_neg_natCast]
/-
**Ring.choose_zero_pos** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：choose_zero_pos (R) [NonAssocRing R] [Pow R Nat] [NatPowAssoc R] [Binomial
Ring R] {k : Nat} (h_pos : 0 < k) : choose (0 : R) k = 0
参数：R；h_pos : 0 < k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.succ_pred_eq_of_pos`：∀ {n : ℕ}, 0 < n → n.pred.succ = n
· 使用定理 `Ring.choose_zero_succ`：choose_zero_succ (R) [NonAssocRing R] [Pow R Nat]
 [NatPowAssoc R] [BinomialRing R] (n : Nat) : choose (0 : R) (n + 1) = 0
-/
theorem choose_zero_pos (R) [NonAssocRing R] [Pow R ℕ] [NatPowAssoc R] [BinomialRing R]
    {k : ℕ} (h_pos : 0 < k) : choose (0 : R) k = 0 := by
  rw [← Nat.succ_pred_eq_of_pos h_pos, choose_zero_succ]
/-
**Ring.choose_zero_ite** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：choose_zero_ite (R) [NonAssocRing R] [Pow R Nat] [NatPowAssoc R] [Binomial
Ring R] (k : Nat) : choose (0 : R) k = if k = 0 then 1 else 0
参数：R；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Ring.choose_zero_right`：choose_zero_right [NatPowAssoc R] (r : R) : choo
se r 0 = 1
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Ring.choose_zero_pos`：choose_zero_pos (R) [NonAssocRing R] [Pow R Nat] [
NatPowAssoc R] [BinomialRing R] {k : Nat} (h_pos : 0 < k) : choose (0 : R) k = 0
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
-/
theorem choose_zero_ite (R) [NonAssocRing R] [Pow R ℕ] [NatPowAssoc R] [BinomialRing R]
    (k : ℕ) : choose (0 : R) k = if k = 0 then 1 else 0 := by
  split_ifs with hk
  · rw [hk, choose_zero_right]
  · rw [choose_zero_pos R <| Nat.pos_of_ne_zero hk]

@[simp]
/-
**Ring.choose_one_right'** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：choose_one_right' (r : R) : choose r 1 = r ^ 1
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ring.choose.eq_1`：∀ {R : Type u_1} [inst : AddCommGroupWithOne R] [inst_
1 : Pow R ℕ] [inst_2 : BinomialRing R] (r : R) (n : ℕ),   Ring.choose r n = Ring
.multi…
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `Ring.multichoose_one_right'`：multichoose_one_right' (r : R) : multichoos
e r 1 = r ^ 1
-/
theorem choose_one_right' (r : R) : choose r 1 = r ^ 1 := by
  rw [choose, Nat.cast_one, sub_add_cancel, multichoose_one_right']
/-
**Ring.choose_one_right** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：choose_one_right [NatPowAssoc R] (r : R) : choose r 1 = r
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ring.choose_one_right'`：choose_one_right' (r : R) : choose r 1 = r ^ 1
· 使用定理 `npow_one`：npow_one (x : M) : x ^ 1 = x
-/
theorem choose_one_right [NatPowAssoc R] (r : R) : choose r 1 = r := by
  rw [choose_one_right', npow_one]
/-
**Ring.choose_neg** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：choose_neg [NatPowAssoc R] (r : R) (n : Nat) : choose (-r) n = Int.negOneP
ow n • choose (r + n - 1) n
参数：r : R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `nsmul_right_inj`：∀ {M : Type u_1} [inst : AddMonoid M] [IsAddTorsionFree
 M] {n : ℕ} {a b : M}, n ≠ 0 → (n • a = n • b ↔ a = b)
· 使用定理 `BinomialRing.toIsAddTorsionFree`：∀ {R : Type u_1} {inst : AddCommMonoid 
R} {inst_1 : Pow R ℕ} [self : BinomialRing R], IsAddTorsionFree R
· 使用定理 `Nat.factorial_ne_zero`：factorial_ne_zero (n : Nat) : n ! != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ring.descPochhammer_eq_factorial_smul_choose`：descPochhammer_eq_factoria
l_smul_choose [NatPowAssoc R] (r : R) (n : Nat) : (descPochhammer Int n).smeval 
r = n.factorial • choose r n
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `Polynomial.descPochhammer_smeval_eq_ascPochhammer`：descPochhammer_smeval
_eq_ascPochhammer (r : R) (n : Nat) : (descPochhammer Int n).smeval r = (ascPoch
hammer Nat n).smeval (r - n + 1)
· 使用定理 `_private.Mathlib.RingTheory.Binomial.0.Ring.choose_neg._abel_1_1`：∀ {R :
 Type u_1} [inst : NonAssocRing R] (r : R) (n : ℕ), -r - ↑n + 1 = -(r + ↑n - 1)
· 使用定理 `Polynomial.ascPochhammer_smeval_neg_eq_descPochhammer`：ascPochhammer_sme
val_neg_eq_descPochhammer (r : R) (k : Nat) : (ascPochhammer Nat k).smeval (-r) 
= Int.negOnePow k • (descPochhammer Int k).…
-/
theorem choose_neg [NatPowAssoc R] (r : R) (n : ℕ) :
    choose (-r) n = Int.negOnePow n • choose (r + n - 1) n := by
  apply (nsmul_right_inj (Nat.factorial_ne_zero n)).mp
  rw [← descPochhammer_eq_factorial_smul_choose, smul_comm,
    ← descPochhammer_eq_factorial_smul_choose, descPochhammer_smeval_eq_ascPochhammer,
    show (-r - n + 1) = -(r + n - 1) by abel, ascPochhammer_smeval_neg_eq_descPochhammer]
/-
**Ring.choose_neg'** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：choose_neg' [NatPowAssoc R] (r : R) (n : Nat) : choose (-r) n = Int.negOne
Pow n • multichoose r n
参数：r : R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ring.choose_neg`：choose_neg [NatPowAssoc R] (r : R) (n : Nat) : choose (
-r) n = Int.negOnePow n • choose (r + n - 1) n
· 使用定理 `Ring.multichoose_eq`：multichoose_eq (r : R) (n : Nat) : multichoose r n 
= choose (r + n - 1) n
-/
theorem choose_neg' [NatPowAssoc R] (r : R) (n : ℕ) :
    choose (-r) n = Int.negOnePow n • multichoose r n := by
  rw [choose_neg, multichoose_eq]
/-
**Ring.descPochhammer_succ_succ_smeval** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：descPochhammer_succ_succ_smeval {R} [NonAssocRing R] [Pow R Nat] [NatPowAs
soc R] (r : R) (k : Nat) : smeval (descPochhammer Int (k + 1)) (r + 1) = (k + 1)
 • smeval (descPochhammer Int k) r + smeval (descPochhammer Int (k + 1)) r
参数：r : R；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `descPochhammer_succ_left`：descPochhammer_succ_left (n : Nat) : descPochh
ammer R (n + 1) = X * (descPochhammer R n).comp (X - 1)
· 使用定理 `descPochhammer_succ_right`：descPochhammer_succ_right (n : Nat) : descPoc
hhammer R (n + 1) = descPochhammer R n * (X - (n : R[X]))
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.smeval_mul`：smeval_mul : (p * q).smeval x = p.smeval x * q.sm
eval x
· 使用定理 `Polynomial.smeval_X`：smeval_X : (X : R[X]).smeval x = x ^ 1
· 使用定理 `npow_one`：npow_one (x : M) : x ^ 1 = x
· 使用定理 `Polynomial.smeval_comp`：smeval_comp : (p.comp q).smeval x = p.smeval (q.
smeval x)
· 使用定理 `Polynomial.smeval_sub`：smeval_sub : (p - q).smeval x = p.smeval x - q.sm
eval x
· 使用定理 `Polynomial.smeval_one`：smeval_one : (1 : R[X]).smeval x = 1 • x ^ 0
· 使用定理 `npow_zero`：npow_zero (x : M) : x ^ 0 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.C_eq_natCast`：C_eq_natCast (n : Nat) : C (n : R) = (n : R[X])
· 使用定理 `Polynomial.smeval_C`：smeval_C : (C r).smeval x = r • x ^ 0
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_sub_assoc`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b c : G), a +
 b - c = a + (b - c)
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `zsmul_one`：∀ {R : Type u_1} [inst : AddGroupWithOne R] (n : ℤ), n • 1 = 
↑n
（共 32 条，此处仅展示前 30 条）
-/
theorem descPochhammer_succ_succ_smeval {R} [NonAssocRing R] [Pow R ℕ] [NatPowAssoc R]
    (r : R) (k : ℕ) : smeval (descPochhammer ℤ (k + 1)) (r + 1) =
    (k + 1) • smeval (descPochhammer ℤ k) r + smeval (descPochhammer ℤ (k + 1)) r := by
  nth_rw 1 [descPochhammer_succ_left]
  rw [descPochhammer_succ_right, mul_comm (descPochhammer ℤ k)]
  simp only [smeval_comp, smeval_sub, smeval_mul, smeval_X, smeval_one, npow_one,
    npow_zero, one_smul, add_sub_cancel_right, sub_mul, add_mul, add_smul, one_mul]
  rw [← C_eq_natCast, smeval_C, npow_zero, add_comm (k • smeval (descPochhammer ℤ k) r) _,
    add_assoc, add_comm (k • smeval (descPochhammer ℤ k) r) _, ← add_assoc, ← add_sub_assoc,
    nsmul_eq_mul, zsmul_one, Int.cast_natCast, sub_add_cancel, add_comm]
/-
**Ring.choose_succ_succ** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：choose_succ_succ [NatPowAssoc R] (r : R) (k : Nat) : choose (r + 1) (k + 1
) = choose r k + choose r (k + 1)
参数：r : R；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nsmul_right_inj`：∀ {M : Type u_1} [inst : AddMonoid M] [IsAddTorsionFree
 M] {n : ℕ} {a b : M}, n ≠ 0 → (n • a = n • b ↔ a = b)
· 使用定理 `BinomialRing.toIsAddTorsionFree`：∀ {R : Type u_1} {inst : AddCommMonoid 
R} {inst_1 : Pow R ℕ} [self : BinomialRing R], IsAddTorsionFree R
· 使用定理 `Nat.factorial_ne_zero`：factorial_ne_zero (n : Nat) : n ! != 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `Nat.factorial_succ`：factorial_succ (n : Nat) : (n + 1)! = (n + 1) * n !
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `Ring.descPochhammer_eq_factorial_smul_choose`：descPochhammer_eq_factoria
l_smul_choose [NatPowAssoc R] (r : R) (n : Nat) : (descPochhammer Int n).smeval 
r = n.factorial • choose r n
· 使用定理 `Ring.descPochhammer_succ_succ_smeval`：descPochhammer_succ_succ_smeval {R
} [NonAssocRing R] [Pow R Nat] [NatPowAssoc R] (r : R) (k : Nat) : smeval (descP
ochhammer Int (k + 1)) (r …
-/
theorem choose_succ_succ [NatPowAssoc R] (r : R) (k : ℕ) :
    choose (r + 1) (k + 1) = choose r k + choose r (k + 1) := by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero (k + 1))]
  simp only [smul_add, ← descPochhammer_eq_factorial_smul_choose]
  rw [Nat.factorial_succ, mul_smul,
    ← descPochhammer_eq_factorial_smul_choose r, descPochhammer_succ_succ_smeval r k]
/-
**Ring.choose_smul_choose** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：choose_smul_choose [NatPowAssoc R] (r : R) {n k : Nat} (hkn : k <= n) : (N
at.choose n k) • choose r n = choose r k * choose (r - k) (n - k)
参数：r : R；hkn : k <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nsmul_right_inj`：∀ {M : Type u_1} [inst : AddMonoid M] [IsAddTorsionFree
 M] {n : ℕ} {a b : M}, n ≠ 0 → (n • a = n • b ↔ a = b)
· 使用定理 `BinomialRing.toIsAddTorsionFree`：∀ {R : Type u_1} {inst : AddCommMonoid 
R} {inst_1 : Pow R ℕ} [self : BinomialRing R], IsAddTorsionFree R
· 使用定理 `Nat.factorial_ne_zero`：factorial_ne_zero (n : Nat) : n ! != 0
· 使用定理 `nsmul_left_comm`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M) (m n : ℕ)
, n • m • a = m • n • a
· 使用定理 `Ring.descPochhammer_eq_factorial_smul_choose`：descPochhammer_eq_factoria
l_smul_choose [NatPowAssoc R] (r : R) (n : Nat) : (descPochhammer Int n).smeval 
r = n.factorial • choose r n
· 使用定理 `Nat.choose_mul_factorial_mul_factorial`：choose_mul_factorial_mul_factori
al : forall {n k}, k <= n -> choose n k * k ! * (n - k)! = n ! | 0, _, hk => by 
simp [Nat.eq_zero_of_le_zero…
· 使用引理 `smul_mul_smul_comm`：smul_mul_smul_comm [Mul α] [Mul β] [SMul α β] [IsSca
larTower α β β] [IsScalarTower α α β] [SMulCommClass α β β] (a : α) (b : β) (c :
 α) (d :…
· 使用定理 `mul_nsmul'`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M) (m n : ℕ), (m 
* n) • a = m • n • a
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `descPochhammer_mul`：descPochhammer_mul (n m : Nat) : descPochhammer R n 
* (descPochhammer R m).comp (X - (n : R[X])) = descPochhammer R (n + m)
· 使用定理 `Polynomial.smeval_mul`：smeval_mul : (p * q).smeval x = p.smeval x * q.sm
eval x
· 使用定理 `Polynomial.smeval_comp`：smeval_comp : (p.comp q).smeval x = p.smeval (q.
smeval x)
· 使用定理 `Polynomial.smeval_sub`：smeval_sub : (p - q).smeval x = p.smeval x - q.sm
eval x
· 使用定理 `Polynomial.smeval_X`：smeval_X : (X : R[X]).smeval x = x ^ 1
· 使用定理 `Polynomial.C_eq_natCast`：C_eq_natCast (n : Nat) : C (n : R) = (n : R[X])
· 使用定理 `Polynomial.smeval_C`：smeval_C : (C r).smeval x = r • x ^ 0
· 使用定理 `npow_one`：npow_one (x : M) : x ^ 1 = x
· 使用定理 `npow_zero`：npow_zero (x : M) : x ^ 0 = 1
· 使用定理 `zsmul_one`：∀ {R : Type u_1} [inst : AddGroupWithOne R] (n : ℤ), n • 1 = 
↑n
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
-/
theorem choose_smul_choose [NatPowAssoc R] (r : R) {n k : ℕ} (hkn : k ≤ n) :
    (Nat.choose n k) • choose r n = choose r k * choose (r - k) (n - k) := by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero n),
    nsmul_left_comm, ← descPochhammer_eq_factorial_smul_choose,
    ← Nat.choose_mul_factorial_mul_factorial hkn, ← smul_mul_smul_comm,
    ← descPochhammer_eq_factorial_smul_choose, mul_nsmul',
    ← descPochhammer_eq_factorial_smul_choose, smul_mul_assoc]
  nth_rw 2 [← Nat.sub_add_cancel hkn]
  rw [add_comm, ← descPochhammer_mul, smeval_mul, smeval_comp, smeval_sub, smeval_X,
    ← C_eq_natCast, smeval_C, npow_one, npow_zero, zsmul_one, Int.cast_natCast, nsmul_eq_mul]
/-
**Ring.choose_add_smul_choose** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：choose_add_smul_choose [NatPowAssoc R] (r : R) (n k : Nat) : (Nat.choose (
n + k) k) • choose (r + k) (n + k) = choose (r + k) k * choose r n
参数：r : R；n k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ring.choose_smul_choose`：choose_smul_choose [NatPowAssoc R] (r : R) {n k
 : Nat} (hkn : k <= n) : (Nat.choose n k) • choose r n = choose r k * choose (r 
- k) (n - k)
· 使用定理 `Nat.le_add_left`：∀ (n m : ℕ), n ≤ m + n
· 使用定理 `Nat.add_sub_cancel`：∀ (n m : ℕ), n + m - m = n
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
-/
theorem choose_add_smul_choose [NatPowAssoc R] (r : R) (n k : ℕ) :
    (Nat.choose (n + k) k) • choose (r + k) (n + k) = choose (r + k) k * choose r n := by
  rw [choose_smul_choose (r + k) (Nat.le_add_left k n), Nat.add_sub_cancel,
    add_sub_cancel_right]

end

/-
**Ring.choose_eq_smul** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：choose_eq_smul [Field R] [CharZero R] {a : R} {n : Nat} : Ring.choose a n 
= (n.factorial : R)⁻¹ • (descPochhammer Int n).smeval a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ring.descPochhammer_eq_factorial_smul_choose`：descPochhammer_eq_factoria
l_smul_choose [NatPowAssoc R] (r : R) (n : Nat) : (descPochhammer Int n).smeval 
r = n.factorial • choose r n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `inv_smul_smul₀`：∀ {α : Type u_4} {β : Type u_5} [inst : GroupWithZero α]
 [inst_1 : MulAction α β] {a : α},   a ≠ 0 → ∀ (x : β), a⁻¹ • a • x = x
· 使用定理 `Nat.factorial_ne_zero`：factorial_ne_zero (n : Nat) : n ! != 0
-/
theorem choose_eq_smul [Field R] [CharZero R] {a : R} {n : ℕ} :
    Ring.choose a n = (n.factorial : R)⁻¹ • (descPochhammer ℤ n).smeval a := by
  rw [Ring.descPochhammer_eq_factorial_smul_choose, ← Nat.cast_smul_eq_nsmul R, inv_smul_smul₀]
  simpa using Nat.factorial_ne_zero n

open Finset

/-- Pochhammer version of Chu-Vandermonde identity -/
/-
**Ring.descPochhammer_smeval_add** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：descPochhammer_smeval_add [Ring R] {r s : R} (k : Nat) (h : Commute r s) :
 (descPochhammer Int k).smeval (r + s) = ∑ ij in antidiagonal k, Nat.choose k ij
.1 * ((descPochhammer Int ij.1).smeval r * (descPochhammer Int ij.2).smeval s)
参数：k : Nat；h : Commute r s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.smeval_one`：smeval_one : (1 : R[X]).smeval x = 1 • x ^ 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.HasAntidiagonal.antidiagonal_zero`：∀ {A : Type u_1} [inst : AddCo
mmMonoid A] [inst_1 : PartialOrder A] [CanonicallyOrderedAdd A]   [inst_3 : Fins
et.HasAntidiagonal A], Finset.…
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `Nat.choose_self`：choose_self (n : Nat) : choose n n = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `descPochhammer_succ_right`：descPochhammer_succ_right (n : Nat) : descPoc
hhammer R (n + 1) = descPochhammer R n * (X - (n : R[X]))
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Polynomial.smeval_mul`：smeval_mul : (p * q).smeval x = p.smeval x * q.sm
eval x
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Finset.sum_antidiagonal_choose_succ_mul`：sum_antidiagonal_choose_succ_mu
l (f : Nat -> Nat -> R) (n : Nat) : (∑ ij in antidiagonal (n + 1), ((n + 1).choo
se ij.1 : R) * f ij.1 ij.2) =…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `Polynomial.smeval_sub`：smeval_sub : (p - q).smeval x = p.smeval x - q.sm
eval x
· 使用定理 `Polynomial.smeval_X`：smeval_X : (X : R[X]).smeval x = x ^ 1
· 使用定理 `Polynomial.smeval_natCast`：smeval_natCast (n : Nat) : (n : R[X]).smeval 
x = n • x ^ 0
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `commute_iff_eq`：commute_iff_eq [Mul S] (a b : S) : Commute a b ↔ a * b =
 b * a
· 使用定理 `Polynomial.smeval_commute`：smeval_commute (hc : Commute x y) : Commute (
p.smeval x) (q.smeval y)
（共 52 条，此处仅展示前 30 条）

--- 原说明 ---
Pochhammer version of Chu-Vandermonde identity
-/
theorem descPochhammer_smeval_add [Ring R] {r s : R} (k : ℕ) (h : Commute r s) :
    (descPochhammer ℤ k).smeval (r + s) = ∑ ij ∈ antidiagonal k,
    Nat.choose k ij.1 * ((descPochhammer ℤ ij.1).smeval r * (descPochhammer ℤ ij.2).smeval s) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [descPochhammer_succ_right, mul_comm, smeval_mul, sum_antidiagonal_choose_succ_mul
      fun i j => ((descPochhammer ℤ i).smeval r * (descPochhammer ℤ j).smeval s),
      ← sum_add_distrib, smeval_sub, smeval_X, smeval_natCast, pow_zero, pow_one, ih, mul_sum]
    refine sum_congr rfl ?_
    intro ij hij -- try to move `descPochhammer`s to right, gather multipliers.
    have hdx : (descPochhammer ℤ ij.1).smeval r * (X - (ij.2 : ℤ[X])).smeval s =
        (X - (ij.2 : ℤ[X])).smeval s * (descPochhammer ℤ ij.1).smeval r := by
      refine (commute_iff_eq ((descPochhammer ℤ ij.1).smeval r)
        ((X - (ij.2 : ℤ[X])).smeval s)).mp ?_
      exact smeval_commute ℤ (descPochhammer ℤ ij.1) (X - (ij.2 : ℤ[X])) h
    rw [descPochhammer_succ_right, mul_comm, smeval_mul, descPochhammer_succ_right, mul_comm,
      smeval_mul, ← mul_assoc ((descPochhammer ℤ ij.1).smeval r), hdx]
    simp only [mul_assoc _ ((descPochhammer ℤ ij.1).smeval r) _,
      ← mul_assoc _ _ (((descPochhammer ℤ ij.1).smeval r) * _)]
    have hl : (r + s - k • 1) * (k.choose ij.1) = (k.choose ij.1) * (X - (ij.2 : ℤ[X])).smeval s +
        ↑(k.choose ij.2) * (X - (ij.1 : ℤ[X])).smeval r := by
      simp only [smeval_sub, smeval_X, pow_one, smeval_natCast, pow_zero]
      rw [← Nat.choose_symm_of_eq_add (List.Nat.mem_antidiagonal.mp hij).symm,
        (List.Nat.mem_antidiagonal.mp hij).symm, ← mul_add, Nat.cast_comm, add_smul]
      abel_nf
    rw [hl, ← add_mul]

/-- The Chu-Vandermonde identity for binomial rings -/
/-
**Ring.add_choose_eq** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：add_choose_eq [Ring R] [BinomialRing R] {r s : R} (k : Nat) (h : Commute r
 s) : choose (r + s) k = ∑ ij in antidiagonal k, choose r ij.1 * choose s ij.2
参数：k : Nat；h : Commute r s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nsmul_right_inj`：∀ {M : Type u_1} [inst : AddMonoid M] [IsAddTorsionFree
 M] {n : ℕ} {a b : M}, n ≠ 0 → (n • a = n • b ↔ a = b)
· 使用定理 `BinomialRing.toIsAddTorsionFree`：∀ {R : Type u_1} {inst : AddCommMonoid 
R} {inst_1 : Pow R ℕ} [self : BinomialRing R], IsAddTorsionFree R
· 使用定理 `Nat.factorial_ne_zero`：factorial_ne_zero (n : Nat) : n ! != 0
· 使用定理 `Ring.descPochhammer_eq_factorial_smul_choose`：descPochhammer_eq_factoria
l_smul_choose [NatPowAssoc R] (r : R) (n : Nat) : (descPochhammer Int n).smeval 
r = n.factorial • choose r n
· 使用定理 `Finset.smul_sum`：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x 
in s, f x) = ∑ x in s, r • f x
· 使用定理 `Ring.descPochhammer_smeval_add`：descPochhammer_smeval_add [Ring R] {r s 
: R} (k : Nat) (h : Commute r s) : (descPochhammer Int k).smeval (r + s) = ∑ ij 
in antidiagonal k, N…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Nat.choose_mul_factorial_mul_factorial`：choose_mul_factorial_mul_factori
al : forall {n k}, k <= n -> choose n k * k ! * (n - k)! = n ! | 0, _, hk => by 
simp [Nat.eq_zero_of_le_zero…
· 使用定理 `Finset.HasAntidiagonal.antidiagonal.fst_le`：∀ {A : Type u_1} [inst : Add
CommMonoid A] [inst_1 : PartialOrder A] [CanonicallyOrderedAdd A]   [inst_3 : Fi
nset.HasAntidiagonal A] {n : A} …
· 使用定理 `tsub_eq_of_eq_add_rev`：tsub_eq_of_eq_add_rev (h : a = b + c) : a - b = c
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.Nat.mem_antidiagonal`：mem_antidiagonal {n : Nat} {x : Nat × Nat} : 
x in antidiagonal n ↔ x.1 + x.2 = n
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Nat.cast_commute`：cast_commute (n : Nat) (x : α) : Commute (n : α) x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The Chu-Vandermonde identity for binomial rings
-/
theorem add_choose_eq [Ring R] [BinomialRing R] {r s : R} (k : ℕ) (h : Commute r s) :
    choose (r + s) k =
      ∑ ij ∈ antidiagonal k, choose r ij.1 * choose s ij.2 := by
  rw [← nsmul_right_inj (Nat.factorial_ne_zero k),
    ← descPochhammer_eq_factorial_smul_choose, smul_sum, descPochhammer_smeval_add _ h]
  refine sum_congr rfl ?_
  intro x hx
  rw [← Nat.choose_mul_factorial_mul_factorial (HasAntidiagonal.antidiagonal.fst_le hx),
    tsub_eq_of_eq_add_rev (List.Nat.mem_antidiagonal.mp hx).symm, mul_assoc, nsmul_eq_mul,
    Nat.cast_mul, Nat.cast_mul, ← mul_assoc _ (x.1.factorial : R), mul_assoc _ (x.2.factorial : R),
    ← mul_assoc (x.2.factorial : R), Nat.cast_commute x.2.factorial,
    mul_assoc _ (x.2.factorial : R), ← nsmul_eq_mul x.2.factorial]
  simp [mul_assoc, descPochhammer_eq_factorial_smul_choose]
/-
**Ring.map_choose** 是 Mathlib 中的一个引理，位于命名空间 `Ring`。
形式化陈述：map_choose {R S F : Type*} [Ring R] [Ring S] [BinomialRing R] [BinomialRin
g S] [FunLike F R S] [RingHomClass F R S] (f : F) (a : R) (n : Nat) : f (Ring.ch
oose a n) = Ring.choose (f a) n
参数：f : F；a : R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `Ring.map_multichoose`：map_multichoose {R S F : Type*} [Ring R] [Ring S] 
[BinomialRing R] [BinomialRing S] [FunLike F R S] [RingHomClass F R S] (f : F) (
a : R) (n …
-/
lemma map_choose {R S F : Type*} [Ring R] [Ring S] [BinomialRing R] [BinomialRing S]
    [FunLike F R S] [RingHomClass F R S] (f : F) (a : R) (n : ℕ) :
    f (Ring.choose a n) = Ring.choose (f a) n := by
  simpa using! Ring.map_multichoose f (a - n + 1) n

end Ring

end Choose

