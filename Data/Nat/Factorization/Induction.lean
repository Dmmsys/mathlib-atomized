/-
Copyright (c) 2021 Stuart Presnell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stuart Presnell
-/
module

public import Mathlib.Data.Nat.Factorization.Defs

/-!
# Induction principles involving factorizations
-/

@[expose] public section

open Nat Finset List Finsupp

namespace Nat
variable {a b m n p : ℕ}

/-! ## Definitions -/


/-- Given `P 0, P 1` and a way to extend `P a` to `P (p ^ n * a)` for prime `p` not dividing `a`,
we can define `P` for all natural numbers. -/
@[elab_as_elim]
/-
**Nat.recOnPrimePow** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：recOnPrimePow {motive : Nat -> Sort*} (zero : motive 0) (one : motive 1) (
prime_pow_mul : forall a p n : Nat, p.Prime -> ¬p ∣ a -> 0 < n -> motive a -> mo
tive (p ^ n * a)) : forall a, motive a
参数：zero : motive 0；one : motive 1；prime_pow_mul : forall a p n : Nat, p.Prime ->
 ¬p ∣ a -> 0 < n -> motive a -> motive (p ^ n * a)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `P 0, P 1` and a way to extend `P a` to `P (p ^ n * a)` for prime `p` not 
dividing `a`,
we can define `P` for all natural numbers.
-/
def recOnPrimePow {motive : ℕ → Sort*} (zero : motive 0) (one : motive 1)
    (prime_pow_mul : ∀ a p n : ℕ, p.Prime → ¬p ∣ a → 0 < n → motive a → motive (p ^ n * a)) :
    ∀ a, motive a :=
  Nat.strongRec fun n ↦
    match n with
    | 0 => fun _ => zero
    | 1 => fun _ => one
    | k + 2 => fun hk => by
      letI p := (k + 2).minFac
      haveI hp : Prime p := minFac_prime (succ_succ_ne_one k)
      letI t := (k + 2).factorization p
      haveI hpt : p ^ t ∣ k + 2 := ordProj_dvd _ _
      haveI htp : 0 < t := hp.factorization_pos_of_dvd (k + 1).succ_ne_zero (k + 2).minFac_dvd
      convert! prime_pow_mul ((k + 2) / p ^ t) p t hp _ htp (hk _ (Nat.div_lt_of_lt_mul _)) using 1
      · rw [Nat.mul_div_cancel' hpt]
      · rw [Nat.dvd_div_iff_mul_dvd hpt, ← Nat.pow_succ]
        exact pow_succ_factorization_not_dvd (k + 1).succ_ne_zero hp
      · simp [htp.ne', hp.one_lt]

/-- Given `P 0`, `P 1`, and `P (p ^ n)` for positive prime powers, and a way to extend `P a` and
`P b` to `P (a * b)` when `a, b` are positive coprime, we can define `P` for all natural numbers. -/
@[elab_as_elim]
/-
**Nat.recOnPosPrimePosCoprime** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：recOnPosPrimePosCoprime {motive : Nat -> Sort*} (prime_pow : forall p n : 
Nat, Prime p -> 0 < n -> motive (p ^ n)) (zero : motive 0) (one : motive 1) (cop
rime : forall a b, 1 < a -> 1 < b -> Coprime a b -> motive a -> motive b -> moti
ve (a * b)) : forall a, motive a
参数：prime_pow : forall p n : Nat, Prime p -> 0 < n -> motive (p ^ n)；zero : motiv
e 0；one : motive 1；coprime : forall a b, 1 < a -> 1 < b -> Coprime a b -> motive
 a -> motive b -> motive (a * b)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `P 0`, `P 1`, and `P (p ^ n)` for positive prime powers, and a way to exte
nd `P a` and
`P b` to `P (a * b)` when `a, b` are positive coprime, we can define `P` for all
 natural numbers.
-/
def recOnPosPrimePosCoprime {motive : ℕ → Sort*}
    (prime_pow : ∀ p n : ℕ, Prime p → 0 < n → motive (p ^ n))
    (zero : motive 0) (one : motive 1)
    (coprime : ∀ a b, 1 < a → 1 < b → Coprime a b → motive a → motive b → motive (a * b)) :
    ∀ a, motive a :=
  recOnPrimePow zero one <| by
    intro a p n hp' hpa hn hPa
    by_cases ha1 : a = 1
    · rw [ha1, mul_one]
      exact prime_pow p n hp' hn
    refine coprime (p ^ n) a (hp'.one_lt.trans_le (le_self_pow hn.ne' _)) ?_ ?_
      (prime_pow _ _ hp' hn) hPa
    · contrapose! hpa
      simp [lt_one_iff.1 (lt_of_le_of_ne hpa ha1)]
    · simpa [hn, Prime.coprime_iff_not_dvd hp']

/-- Given `P 0`, `P (p ^ n)` for all prime powers, and a way to extend `P a` and `P b` to
`P (a * b)` when `a, b` are positive coprime, we can define `P` for all natural numbers. -/
@[elab_as_elim]
/-
**Nat.recOnPrimeCoprime** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：recOnPrimeCoprime {motive : Nat -> Sort*} (zero : motive 0) (prime_pow : f
orall p n : Nat, Prime p -> motive (p ^ n)) (coprime : forall a b, 1 < a -> 1 < 
b -> Coprime a b -> motive a -> motive b -> motive (a * b)) : forall a, motive a
参数：zero : motive 0；prime_pow : forall p n : Nat, Prime p -> motive (p ^ n)；copri
me : forall a b, 1 < a -> 1 < b -> Coprime a b -> motive a -> motive b -> motive
 (a * b)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.prime_two`：prime_two : Prime 2

--- 原说明 ---
Given `P 0`, `P (p ^ n)` for all prime powers, and a way to extend `P a` and `P 
b` to
`P (a * b)` when `a, b` are positive coprime, we can define `P` for all natural 
numbers.
-/
def recOnPrimeCoprime {motive : ℕ → Sort*} (zero : motive 0)
    (prime_pow : ∀ p n : ℕ, Prime p → motive (p ^ n))
    (coprime : ∀ a b, 1 < a → 1 < b → Coprime a b → motive a → motive b → motive (a * b)) :
    ∀ a, motive a :=
  recOnPosPrimePosCoprime (fun p n h _ => prime_pow p n h) zero (prime_pow 2 0 prime_two) coprime

/-- Given `P 0`, `P 1`, `P p` for all primes, and a way to extend `P a` and `P b` to
`P (a * b)`, we can define `P` for all natural numbers. -/
@[elab_as_elim]
/-
**Nat.recOnMul** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：recOnMul {motive : Nat -> Sort*} (zero : motive 0) (one : motive 1) (prime
 : forall p, Prime p -> motive p) (mul : forall a b, motive a -> motive b -> mot
ive (a * b)) : forall a, motive a
参数：zero : motive 0；one : motive 1；prime : forall p, Prime p -> motive p；mul : fo
rall a b, motive a -> motive b -> motive (a * b)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `P 0`, `P 1`, `P p` for all primes, and a way to extend `P a` and `P b` to
`P (a * b)`, we can define `P` for all natural numbers.
-/
def recOnMul {motive : ℕ → Sort*} (zero : motive 0) (one : motive 1)
    (prime : ∀ p, Prime p → motive p)
    (mul : ∀ a b, motive a → motive b → motive (a * b)) : ∀ a, motive a :=
  recOnPrimeCoprime zero
    (fun p n hp' => Nat.rec one (fun _ ih => mul _ _ ih (prime p hp')) n)
    (fun a b _ _ _ => mul a b)
/-
**Nat._root_.induction_on_primes** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.induction_on_primes {motive : ℕ → Prop} (zero : motive 0) (one : motive 1)
    (prime_mul : ∀ p a : ℕ, p.Prime → motive a → motive (p * a)) : ∀ n, motive n := by
  refine recOnPrimePow zero one ?_
  rintro a p n hp - - ha
  induction n with
  | zero => simpa using ha
  | succ n ih =>
    rw [pow_succ', mul_assoc]
    exact prime_mul _ _ hp ih
/-
**Nat.prime_composite_induction** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：prime_composite_induction {motive : Nat -> Prop} (zero : motive 0) (one : 
motive 1) (prime : forall p : Nat, p.Prime -> motive p) (composite : forall a, 2
 <= a -> motive a -> forall b, 2 <= b -> motive b -> motive (a * b)) (n : Nat) :
 motive n
参数：zero : motive 0；one : motive 1；prime : forall p : Nat, p.Prime -> motive p；co
mposite : forall a, 2 <= a -> motive a -> forall b, 2 <= b -> motive b -> motive
 (a * b)；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `induction_on_primes`：∀ {motive : ℕ → Prop},   motive 0 → motive 1 → (∀ (
p a : ℕ), Nat.Prime p → motive a → motive (p * a)) → ∀ (n : ℕ), motive n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Nat.Prime.two_le`：∀ {p : ℕ}, Nat.Prime p → 2 ≤ p
· 使用定理 `Nat.one_lt_succ_succ`：∀ (n : ℕ), 1 < n.succ.succ
-/
lemma prime_composite_induction {motive : ℕ → Prop} (zero : motive 0) (one : motive 1)
    (prime : ∀ p : ℕ, p.Prime → motive p)
    (composite : ∀ a, 2 ≤ a → motive a → ∀ b, 2 ≤ b → motive b → motive (a * b))
    (n : ℕ) : motive n := by
  refine induction_on_primes zero one ?_ _
  rintro p (_ | _ | a) hp ha
  · simpa
  · simpa using prime _ hp
  · exact composite _ hp.two_le (prime _ hp) _ a.one_lt_succ_succ ha

/-! ## Lemmas on multiplicative functions -/

/-- For any multiplicative function `f` with `f 1 = 1` and any `n ≠ 0`,
we can evaluate `f n` by evaluating `f` at `p ^ k` over the factorization of `n` -/
/-
**Nat.multiplicative_factorization** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：multiplicative_factorization {β : Type*} [CommMonoid β] (f : Nat -> β) (h_
mult : forall x y : Nat, Coprime x y -> f (x * y) = f x * f y) (hf : f 1 = 1) : 
forall {n : Nat}, n != 0 -> f n = n.factorization.prod fun p k => f (p ^ k)
参数：f : Nat -> β；h_mult : forall x y : Nat, Coprime x y -> f (x * y) = f x * f y；
hf : f 1 = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.Prime.factorization_pow`：∀ {p k : ℕ}, Nat.Prime p → (p ^ k).factoriz
ation = fun₀ | p => k
· 使用定理 `Finsupp.prod_single_index`：prod_single_index {a : α} {b : M} {h : α -> M
 -> N} (h_zero : h a 0 = 1) : (single a b).prod h = h a b
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Nat.factorization_zero`：factorization_zero : factorization 0 = 0
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `Nat.factorization_one`：factorization_one : factorization 1 = 0
· 使用定理 `left_ne_zero_of_mul`：left_ne_zero_of_mul : a * b != 0 -> a != 0
· 使用定理 `right_ne_zero_of_mul`：right_ne_zero_of_mul : a * b != 0 -> b != 0
· 使用定理 `Nat.factorization_mul_of_coprime`：factorization_mul_of_coprime {a b : Na
t} (hab : Coprime a b) : (a * b).factorization = a.factorization + b.factorizati
on
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.prod_add_index_of_disjoint`：prod_add_index_of_disjoint [AddCommM
onoid M] {f1 f2 : α ->₀ M} (hd : Disjoint f1.support f2.support) {β : Type*} [Co
mmMonoid β] (g : α -> M …
· 使用定理 `Nat.Coprime.disjoint_primeFactors`：∀ {a b : ℕ}, a.Coprime b → Disjoint a
.primeFactors b.primeFactors

--- 原说明 ---
For any multiplicative function `f` with `f 1 = 1` and any `n ≠ 0`,
we can evaluate `f n` by evaluating `f` at `p ^ k` over the factorization of `n`
-/
theorem multiplicative_factorization {β : Type*} [CommMonoid β] (f : ℕ → β)
    (h_mult : ∀ x y : ℕ, Coprime x y → f (x * y) = f x * f y) (hf : f 1 = 1) :
    ∀ {n : ℕ}, n ≠ 0 → f n = n.factorization.prod fun p k => f (p ^ k) := by
  apply Nat.recOnPosPrimePosCoprime
  · rintro p k hp - -
    simp [Prime.factorization_pow hp, Finsupp.prod_single_index _, hf]
  · simp
  · rintro -
    rw [factorization_one, hf]
    simp
  · intro a b _ _ hab ha hb hab_pos
    rw [h_mult a b hab, ha (left_ne_zero_of_mul hab_pos), hb (right_ne_zero_of_mul hab_pos),
      factorization_mul_of_coprime hab, ← prod_add_index_of_disjoint]
    exact hab.disjoint_primeFactors

/-- For any multiplicative function `f` with `f 1 = 1` and `f 0 = 1`,
we can evaluate `f n` by evaluating `f` at `p ^ k` over the factorization of `n` -/
/-
**Nat.multiplicative_factorization'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：multiplicative_factorization' {β : Type*} [CommMonoid β] (f : Nat -> β) (h
_mult : forall x y : Nat, Coprime x y -> f (x * y) = f x * f y) (hf0 : f 0 = 1) 
(hf1 : f 1 = 1) : f n = n.factorization.prod fun p k => f (p ^ k)
参数：f : Nat -> β；h_mult : forall x y : Nat, Coprime x y -> f (x * y) = f x * f y；
hf0 : f 0 = 1；hf1 : f 1 = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.factorization_zero`：factorization_zero : factorization 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.multiplicative_factorization`：multiplicative_factorization {β : Type
*} [CommMonoid β] (f : Nat -> β) (h_mult : forall x y : Nat, Coprime x y -> f (x
 * y) = f x * f y) (hf…

--- 原说明 ---
For any multiplicative function `f` with `f 1 = 1` and `f 0 = 1`,
we can evaluate `f n` by evaluating `f` at `p ^ k` over the factorization of `n`
-/
theorem multiplicative_factorization' {β : Type*} [CommMonoid β] (f : ℕ → β)
    (h_mult : ∀ x y : ℕ, Coprime x y → f (x * y) = f x * f y) (hf0 : f 0 = 1) (hf1 : f 1 = 1) :
    f n = n.factorization.prod fun p k => f (p ^ k) := by
  obtain rfl | hn := eq_or_ne n 0
  · simpa
  · exact multiplicative_factorization _ h_mult hf1 hn

end Nat

