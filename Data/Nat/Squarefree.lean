/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.NumberTheory.Divisors
public import Mathlib.RingTheory.UniqueFactorizationDomain.Nat

/-!
# Lemmas about squarefreeness of natural numbers

A number is squarefree when it is not divisible by any squares except the squares of units.

## Main Results
- `Nat.squarefree_iff_nodup_primeFactorsList`: A positive natural number `x` is squarefree iff
  the list `factors x` has no duplicate factors.

## Tags
squarefree, multiplicity

-/

@[expose] public section

open Finset

namespace Nat

/-
**Nat.squarefree_iff_nodup_primeFactorsList** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：squarefree_iff_nodup_primeFactorsList {n : Nat} (h0 : n != 0) : Squarefree
 n ↔ n.primeFactorsList.Nodup
参数：h0 : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors`：square
free_iff_nodup_normalizedFactors [NormalizationMonoid R] {x : R} (x0 : x != 0) :
 Squarefree x ↔ Multiset.Nodup (normalizedFactors x)
· 使用定理 `Nat.factors_eq`：∀ (n : ℕ), UniqueFactorizationMonoid.normalizedFactors n
 = ↑n.primeFactorsList
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem squarefree_iff_nodup_primeFactorsList {n : ℕ} (h0 : n ≠ 0) :
    Squarefree n ↔ n.primeFactorsList.Nodup := by
  rw [UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors h0, Nat.factors_eq]
  simp

end Nat

/-
**Squarefree.nodup_primeFactorsList** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Squarefree.nodup_primeFactorsList {n : Nat} (hn : Squarefree n) : n.primeF
actorsList.Nodup
参数：hn : Squarefree n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.squarefree_iff_nodup_primeFactorsList`：squarefree_iff_nodup_primeFac
torsList {n : Nat} (h0 : n != 0) : Squarefree n ↔ n.primeFactorsList.Nodup
· 使用定理 `Squarefree.ne_zero`：Squarefree.ne_zero [MonoidWithZero R] [Nontrivial R]
 {m : R} (hm : Squarefree (m : R)) : m != 0
-/
theorem Squarefree.nodup_primeFactorsList {n : ℕ} (hn : Squarefree n) : n.primeFactorsList.Nodup :=
  (Nat.squarefree_iff_nodup_primeFactorsList hn.ne_zero).mp hn

namespace Nat
variable {s : Finset ℕ} {m n p : ℕ}

/-
**Nat.squarefree_iff_prime_squarefree** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：squarefree_iff_prime_squarefree {n : Nat} : Squarefree n ↔ forall x, Prime
 x -> ¬x * x ∣ n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `squarefree_iff_irreducible_sq_not_dvd_of_exists_irreducible`：squarefree_
iff_irreducible_sq_not_dvd_of_exists_irreducible {r : R} (hr : exists x : R, Irr
educible x) : Squarefree r ↔ forall x : R, Irredu…
· 使用定理 `Nat.prime_two`：prime_two : Prime 2
-/
theorem squarefree_iff_prime_squarefree {n : ℕ} : Squarefree n ↔ ∀ x, Prime x → ¬x * x ∣ n :=
  squarefree_iff_irreducible_sq_not_dvd_of_exists_irreducible ⟨_, prime_two⟩
/-
**Nat._root_.Squarefree.natFactorization_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Squarefree.natFactorization_le_one {n : ℕ} (p : ℕ) (hn : Squarefree n) :
    n.factorization p ≤ 1 := by
  rcases eq_or_ne n 0 with (rfl | hn')
  · simp
  rw [squarefree_iff_emultiplicity_le_one] at hn
  by_cases hp : p.Prime
  · have := hn p
    rw [← multiplicity_eq_factorization hp hn']
    simp only [Nat.isUnit_iff, hp.ne_one, or_false] at this
    exact multiplicity_le_of_emultiplicity_le this
  · rw [factorization_eq_zero_of_not_prime _ hp]
    exact zero_le_one
/-
**Nat.factorization_eq_one_of_squarefree** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：factorization_eq_one_of_squarefree (hn : Squarefree n) (hp : p.Prime) (hpn
 : p ∣ n) : factorization n p = 1
参数：hn : Squarefree n；hp : p.Prime；hpn : p ∣ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Squarefree.natFactorization_le_one`：∀ {n : ℕ} (p : ℕ), Squarefree n → n.
factorization p ≤ 1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.Prime.dvd_iff_one_le_factorization`：∀ {p n : ℕ}, Nat.Prime p → n ≠ 0
 → (p ∣ n ↔ 1 ≤ n.factorization p)
· 使用定理 `Squarefree.ne_zero`：Squarefree.ne_zero [MonoidWithZero R] [Nontrivial R]
 {m : R} (hm : Squarefree (m : R)) : m != 0
-/
lemma factorization_eq_one_of_squarefree (hn : Squarefree n) (hp : p.Prime) (hpn : p ∣ n) :
    factorization n p = 1 :=
  (hn.natFactorization_le_one _).antisymm <| (hp.dvd_iff_one_le_factorization hn.ne_zero).1 hpn
/-
**Nat.squarefree_of_factorization_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：squarefree_of_factorization_le_one {n : Nat} (hn : n != 0) (hn' : forall p
, n.factorization p <= 1) : Squarefree n
参数：hn : n != 0；hn' : forall p, n.factorization p <= 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.squarefree_iff_nodup_primeFactorsList`：squarefree_iff_nodup_primeFac
torsList {n : Nat} (h0 : n != 0) : Squarefree n ↔ n.primeFactorsList.Nodup
· 使用定理 `List.nodup_iff_count_le_one`：nodup_iff_count_le_one [BEq α] [LawfulBEq α
] {l : List α} : Nodup l ↔ forall a, count a l <= 1
· 使用定理 `Nat.instLawfulBEq`：LawfulBEq ℕ
· 使用定理 `Nat.primeFactorsList_count_eq`：primeFactorsList_count_eq {n p : Nat} : n
.primeFactorsList.count p = n.factorization p
-/
theorem squarefree_of_factorization_le_one {n : ℕ} (hn : n ≠ 0) (hn' : ∀ p, n.factorization p ≤ 1) :
    Squarefree n := by
  rw [squarefree_iff_nodup_primeFactorsList hn, List.nodup_iff_count_le_one]
  intro a
  rw [primeFactorsList_count_eq]
  apply hn'
/-
**Nat.squarefree_iff_factorization_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：squarefree_iff_factorization_le_one {n : Nat} (hn : n != 0) : Squarefree n
 ↔ forall p, n.factorization p <= 1
参数：hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Squarefree.natFactorization_le_one`：∀ {n : ℕ} (p : ℕ), Squarefree n → n.
factorization p ≤ 1
· 使用定理 `Nat.squarefree_of_factorization_le_one`：squarefree_of_factorization_le_o
ne {n : Nat} (hn : n != 0) (hn' : forall p, n.factorization p <= 1) : Squarefree
 n
-/
theorem squarefree_iff_factorization_le_one {n : ℕ} (hn : n ≠ 0) :
    Squarefree n ↔ ∀ p, n.factorization p ≤ 1 :=
  ⟨fun hn => hn.natFactorization_le_one, squarefree_of_factorization_le_one hn⟩
/-
**Nat.Squarefree.ext_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Squarefree`。
形式化陈述：∀ {n m : ℕ}, Squarefree n → Squarefree m → (n = m ↔ ∀ (p : ℕ), Nat.Prime p
 → (p ∣ n ↔ p ∣ m))
参数：n = m ↔ ∀ (p : ℕ), Nat.Prime p → (p ∣ n ↔ p ∣ m)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Nat.eq_of_factorization_eq`：eq_of_factorization_eq {a b : Nat} (ha : a !
= 0) (hb : b != 0) (h : forall p : Nat, a.factorization p = b.factorization p) :
 a = b
· 使用定理 `Squarefree.ne_zero`：Squarefree.ne_zero [MonoidWithZero R] [Nontrivial R]
 {m : R} (hm : Squarefree (m : R)) : m != 0
· 使用定理 `Squarefree.natFactorization_le_one`：∀ {n : ℕ} (p : ℕ), Squarefree n → n.
factorization p ≤ 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.lt_one_iff`：∀ {n : ℕ}, n < 1 ↔ n = 0
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Nat.Prime.dvd_iff_one_le_factorization`：∀ {p n : ℕ}, Nat.Prime p → n ≠ 0
 → (p ∣ n ↔ 1 ≤ n.factorization p)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `Nat.factorization_eq_zero_of_not_prime`：factorization_eq_zero_of_not_pri
me (n : Nat) {p : Nat} (hp : ¬p.Prime) : n.factorization p = 0
-/
theorem Squarefree.ext_iff {n m : ℕ} (hn : Squarefree n) (hm : Squarefree m) :
    n = m ↔ ∀ p, Prime p → (p ∣ n ↔ p ∣ m) := by
  refine ⟨by rintro rfl; simp, fun h => eq_of_factorization_eq hn.ne_zero hm.ne_zero fun p => ?_⟩
  by_cases hp : p.Prime
  · have h₁ := h _ hp
    rw [← not_iff_not, hp.dvd_iff_one_le_factorization hn.ne_zero, not_le, lt_one_iff,
      hp.dvd_iff_one_le_factorization hm.ne_zero, not_le, lt_one_iff] at h₁
    have h₂ := hn.natFactorization_le_one p
    have h₃ := hm.natFactorization_le_one p
    lia
  rw [factorization_eq_zero_of_not_prime _ hp, factorization_eq_zero_of_not_prime _ hp]
/-
**Nat.squarefree_pow_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：squarefree_pow_iff {n k : Nat} (hn : n != 1) (hk : k != 0) : Squarefree (n
 ^ k) ↔ Squarefree n ∧ k = 1
参数：hn : n != 1；hk : k != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Squarefree.squarefree_of_dvd`：Squarefree.squarefree_of_dvd [Monoid R] {x
 y : R} (hdvd : x ∣ y) (hsq : Squarefree y) : Squarefree x
· 使用引理 `dvd_pow_self`：dvd_pow_self (a : α) {n : Nat} (hn : n != 0) : a ∣ a ^ n
· 使用定理 `by_contradiction`：by_contradiction {p : Prop} : (¬p -> False) -> p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.two_le_iff`：∀ (n : ℕ), 2 ≤ n ↔ n ≠ 0 ∧ n ≠ 1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.isUnit_iff`：∀ {n : ℕ}, IsUnit n ↔ n = 1
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用引理 `pow_dvd_pow`：pow_dvd_pow (a : α) (h : m <= n) : a ^ m ∣ a ^ n
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
-/
theorem squarefree_pow_iff {n k : ℕ} (hn : n ≠ 1) (hk : k ≠ 0) :
    Squarefree (n ^ k) ↔ Squarefree n ∧ k = 1 := by
  refine ⟨fun h => ?_, by rintro ⟨hn, rfl⟩; simpa⟩
  rcases eq_or_ne n 0 with (rfl | -)
  · simp [zero_pow hk] at h
  refine ⟨h.squarefree_of_dvd (dvd_pow_self _ hk), by_contradiction fun h₁ => ?_⟩
  have : 2 ≤ k := k.two_le_iff.mpr ⟨hk, h₁⟩
  apply hn (Nat.isUnit_iff.1 (h _ _))
  rw [← sq]
  exact pow_dvd_pow _ this
/-
**Nat.squarefree_and_prime_pow_iff_prime** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：squarefree_and_prime_pow_iff_prime {n : Nat} : Squarefree n ∧ IsPrimePow n
 ↔ Prime n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isPrimePow_nat_iff`：isPrimePow_nat_iff (n : Nat) : IsPrimePow n ↔ exists
 p k : Nat, Nat.Prime p ∧ 0 < k ∧ p ^ k = n
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Nat.squarefree_pow_iff`：squarefree_pow_iff {n k : Nat} (hn : n != 1) (hk
 : k != 0) : Squarefree (n ^ k) ↔ Squarefree n ∧ k = 1
· 使用定理 `Nat.Prime.ne_one`：∀ {p : ℕ}, Nat.Prime p → p ≠ 1
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Irreducible.squarefree`：Irreducible.squarefree [CommMonoid R] {x : R} (h
 : Irreducible x) : Squarefree x
· 使用定理 `Nat.Prime.isPrimePow`：Nat.Prime.isPrimePow {p : Nat} (hp : p.Prime) : Is
PrimePow p
-/
theorem squarefree_and_prime_pow_iff_prime {n : ℕ} : Squarefree n ∧ IsPrimePow n ↔ Prime n := by
  refine ⟨?_, fun hn => ⟨hn.squarefree, hn.isPrimePow⟩⟩
  rw [isPrimePow_nat_iff]
  rintro ⟨h, p, k, hp, hk, rfl⟩
  rw [squarefree_pow_iff hp.ne_one hk.ne'] at h
  rwa [h.2, pow_one]

/-- Assuming that `n` has no factors less than `k`, returns the smallest prime `p` such that
  `p^2 ∣ n`. -/
/-
**Nat.minSqFacAux** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：minSqFacAux : Nat -> Nat -> Option Nat | n, k => if h : n < k * k then non
e else have : Nat.sqrt n - k < Nat.sqrt n + 2 - k
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Assuming that `n` has no factors less than `k`, returns the smallest prime `p` s
uch that
  `p^2 ∣ n`.
-/
def minSqFacAux : ℕ → ℕ → Option ℕ
  | n, k =>
    if h : n < k * k then none
    else
      have : Nat.sqrt n - k < Nat.sqrt n + 2 - k := by
        exact Nat.minFac_lemma n k h
      if k ∣ n then
        let n' := n / k
        have : Nat.sqrt n' - k < Nat.sqrt n + 2 - k :=
        lt_of_le_of_lt (by gcongr; apply div_le_self) this
        if k ∣ n' then some k else minSqFacAux n' (k + 2)
      else minSqFacAux n (k + 2)
termination_by n k => sqrt n + 2 - k

/-- Returns the smallest prime factor `p` of `n` such that `p^2 ∣ n`, or `none` if there is no
  such `p` (that is, `n` is squarefree). See also `Nat.squarefree_iff_minSqFac`. -/
/-
**Nat.minSqFac** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：minSqFac (n : Nat) : Option Nat
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Returns the smallest prime factor `p` of `n` such that `p^2 ∣ n`, or `none` if t
here is no
  such `p` (that is, `n` is squarefree). See also `Nat.squarefree_iff_minSqFac`.
-/
def minSqFac (n : ℕ) : Option ℕ :=
  if 2 ∣ n then
    let n' := n / 2
    if 2 ∣ n' then some 2 else minSqFacAux n' 3
  else minSqFacAux n 3

/-- The correctness property of the return value of `minSqFac`.
  * If `none`, then `n` is squarefree;
  * If `some d`, then `d` is a minimal square factor of `n` -/
/-
**Nat.MinSqFacProp** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：ℕ → Option ℕ → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The correctness property of the return value of `minSqFac`.
  * If `none`, then `n` is squarefree;
  * If `some d`, then `d` is a minimal square factor of `n`
-/
def MinSqFacProp (n : ℕ) : Option ℕ → Prop
  | none => Squarefree n
  | some d => Prime d ∧ d * d ∣ n ∧ ∀ p, Prime p → p * p ∣ n → d ≤ p
/-
**Nat.minSqFacProp_div** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：minSqFacProp_div (n) {k} (pk : Prime k) (dk : k ∣ n) (dkk : ¬k * k ∣ n) {o
} (H : MinSqFacProp (n / k) o) : MinSqFacProp n o
参数：n；pk : Prime k；dk : k ∣ n；dkk : ¬k * k ∣ n；H : MinSqFacProp (n / k) o。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.coprime_primes`：coprime_primes {p q : Nat} (pp : Prime p) (pq : Prim
e q) : Coprime p q ↔ p != q
· 使用定理 `Nat.Coprime.mul_dvd_of_dvd_of_dvd`：∀ {m n a : ℕ}, m.Coprime n → m ∣ a → 
n ∣ a → m * n ∣ a
· 使用定理 `Nat.coprime_mul_iff_right`：∀ {k m n : ℕ}, k.Coprime (m * n) ↔ k.Coprime 
m ∧ k.Coprime n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.MinSqFacProp.eq_1`：∀ (n : ℕ), n.MinSqFacProp none = Squarefree n
· 使用定理 `Nat.squarefree_iff_prime_squarefree`：squarefree_iff_prime_squarefree {n 
: Nat} : Squarefree n ↔ forall x, Prime x -> ¬x * x ∣ n
· 使用定理 `Nat.dvd_div_iff_mul_dvd`：∀ {a b c : ℕ}, c ∣ b → (a ∣ b / c ↔ c * a ∣ b)
· 使用定理 `dvd_trans`：dvd_trans : a ∣ b -> b ∣ c -> a ∣ c | ⟨d, h₁⟩, ⟨e, h₂⟩ => ⟨d 
* e, h₁ ▸ h₂.trans mul_assoc a d e⟩  alias Dvd.dvd.trans
· 使用定理 `dvd_mul_left`：dvd_mul_left (a b : α) : a ∣ b * a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem minSqFacProp_div (n) {k} (pk : Prime k) (dk : k ∣ n) (dkk : ¬k * k ∣ n) {o}
    (H : MinSqFacProp (n / k) o) : MinSqFacProp n o := by
  have : ∀ p, Prime p → p * p ∣ n → k * (p * p) ∣ n := fun p pp dp =>
    have :=
      (coprime_primes pk pp).2 fun e => by
        subst e
        contradiction
    (coprime_mul_iff_right.2 ⟨this, this⟩).mul_dvd_of_dvd_of_dvd dk dp
  rcases o with - | d
  · rw [MinSqFacProp, squarefree_iff_prime_squarefree] at H ⊢
    exact fun p pp dp => H p pp ((dvd_div_iff_mul_dvd dk).2 (this _ pp dp))
  · obtain ⟨H1, H2, H3⟩ := H
    simp only [dvd_div_iff_mul_dvd dk] at H2 H3
    exact ⟨H1, dvd_trans (dvd_mul_left _ _) H2, fun p pp dp => H3 _ pp (this _ pp dp)⟩
/-
**Nat.minSqFacAux_has_prop** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：minSqFacAux_has_prop {n : Nat} (k) (n0 : 0 < n) (i) (e : k = 2 * i + 3) (i
h : forall m, Prime m -> m ∣ n -> k <= m) : MinSqFacProp n (minSqFacAux n k)
参数：k；n0 : 0 < n；i；e : k = 2 * i + 3；ih : forall m, Prime m -> m ∣ n -> k <= m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.minSqFacAux_has_prop._unary`：∀ (_x : (n : ℕ) ×' (k : ℕ) ×' (_ : 0 < 
n) ×' (i : ℕ) ×' (_ : k = 2 * i + 3) ×' ∀ (m : ℕ), Nat.Prime m → m ∣ n → k ≤ m),
   _x.1.MinSqFacProp …
-/
theorem minSqFacAux_has_prop {n : ℕ} (k) (n0 : 0 < n) (i) (e : k = 2 * i + 3)
    (ih : ∀ m, Prime m → m ∣ n → k ≤ m) : MinSqFacProp n (minSqFacAux n k) := by
  rw [minSqFacAux]
  by_cases h : n < k * k <;> simp only [h, ↓reduceDIte]
  · refine squarefree_iff_prime_squarefree.2 fun p pp d => ?_
    have := ih p pp (dvd_trans ⟨_, rfl⟩ d)
    have := Nat.mul_le_mul this this
    exact not_le_of_gt h (le_trans this (le_of_dvd n0 d))
  have k2 : 2 ≤ k := by lia
  have k0 : 0 < k := lt_of_lt_of_le (by decide) k2
  have IH : ∀ n', n' ∣ n → ¬k ∣ n' → MinSqFacProp n' (n'.minSqFacAux (k + 2)) := by
    intro n' nd' nk
    have hn' := le_of_dvd n0 nd'
    refine
      have : Nat.sqrt n' - k < Nat.sqrt n + 2 - k :=
        lt_of_le_of_lt (by gcongr) (Nat.minFac_lemma n k h)
      @minSqFacAux_has_prop n' (k + 2) (pos_of_dvd_of_pos nd' n0) (i + 1)
        (by simp [e, left_distrib]) fun m m2 d => ?_
    rcases Nat.eq_or_lt_of_le (ih m m2 (dvd_trans d nd')) with rfl | ml
    · contradiction
    apply (Nat.eq_or_lt_of_le ml).resolve_left
    intro me
    rw [← me, e] at d
    change 2 * (i + 2) ∣ n' at d
    have := ih _ prime_two (dvd_trans (dvd_of_mul_right_dvd d) nd')
    rw [e] at this
    exact absurd this (by lia)
  have pk : k ∣ n → Prime k := by
    refine fun dk => prime_def_minFac.2 ⟨k2, le_antisymm (minFac_le k0) ?_⟩
    exact ih _ (minFac_prime (ne_of_gt k2)) (dvd_trans (minFac_dvd _) dk)
  split_ifs with dk dkk
  · exact ⟨pk dk, (Nat.dvd_div_iff_mul_dvd dk).1 dkk, fun p pp d => ih p pp (dvd_trans ⟨_, rfl⟩ d)⟩
  · specialize IH (n / k) (div_dvd_of_dvd dk) dkk
    exact minSqFacProp_div _ (pk dk) dk (mt (Nat.dvd_div_iff_mul_dvd dk).2 dkk) IH
  · exact IH n (dvd_refl _) dk
termination_by n.sqrt + 2 - k
/-
**Nat.minSqFac_has_prop** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：minSqFac_has_prop (n : Nat) : MinSqFacProp n (minSqFac n)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Nat.prime_two`：prime_two : Prime 2
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.dvd_div_iff_mul_dvd`：∀ {a b c : ℕ}, c ∣ b → (a ∣ b / c ↔ c * a ∣ b)
· 使用定理 `Nat.Prime.two_le`：∀ {p : ℕ}, Nat.Prime p → 2 ≤ p
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.minSqFacProp_div`：minSqFacProp_div (n) {k} (pk : Prime k) (dk : k ∣ 
n) (dkk : ¬k * k ∣ n) {o} (H : MinSqFacProp (n / k) o) : MinSqFacProp n o
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.minSqFacAux_has_prop`：minSqFacAux_has_prop {n : Nat} (k) (n0 : 0 < n
) (i) (e : k = 2 * i + 3) (ih : forall m, Prime m -> m ∣ n -> k <= m) : MinSqFac
Prop n (minSqF…
· 使用定理 `Nat.div_pos`：∀ {b a : ℕ}, b ≤ a → 0 < b → 0 < a / b
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
· 使用定理 `Nat.succ_le_of_lt`：∀ {n m : ℕ}, n < m → n.succ ≤ m
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
-/
theorem minSqFac_has_prop (n : ℕ) : MinSqFacProp n (minSqFac n) := by
  dsimp only [minSqFac]; split_ifs with d2 d4
  · exact ⟨prime_two, (dvd_div_iff_mul_dvd d2).1 d4, fun p pp _ => pp.two_le⟩
  · rcases Nat.eq_zero_or_pos n with rfl | n0
    · cases d4 (by decide)
    refine minSqFacProp_div _ prime_two d2 (mt (dvd_div_iff_mul_dvd d2).2 d4) ?_
    refine minSqFacAux_has_prop 3 (Nat.div_pos (le_of_dvd n0 d2) (by decide)) 0 rfl ?_
    refine fun p pp dp => succ_le_of_lt (lt_of_le_of_ne pp.two_le ?_)
    rintro rfl
    contradiction
  · rcases Nat.eq_zero_or_pos n with rfl | n0
    · cases d2 (by decide)
    refine minSqFacAux_has_prop _ n0 0 rfl ?_
    refine fun p pp dp => succ_le_of_lt (lt_of_le_of_ne pp.two_le ?_)
    rintro rfl
    contradiction
/-
**Nat.minSqFac_prime** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：minSqFac_prime {n d : Nat} (h : n.minSqFac = some d) : Prime d
参数：h : n.minSqFac = some d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.minSqFac_has_prop`：minSqFac_has_prop (n : Nat) : MinSqFacProp n (min
SqFac n)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem minSqFac_prime {n d : ℕ} (h : n.minSqFac = some d) : Prime d := by
  have := minSqFac_has_prop n
  rw [h] at this
  exact this.1
/-
**Nat.minSqFac_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：minSqFac_dvd {n d : Nat} (h : n.minSqFac = some d) : d * d ∣ n
参数：h : n.minSqFac = some d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.minSqFac_has_prop`：minSqFac_has_prop (n : Nat) : MinSqFacProp n (min
SqFac n)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem minSqFac_dvd {n d : ℕ} (h : n.minSqFac = some d) : d * d ∣ n := by
  have := minSqFac_has_prop n
  rw [h] at this
  exact this.2.1
/-
**Nat.minSqFac_le_of_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：minSqFac_le_of_dvd {n d : Nat} (h : n.minSqFac = some d) {m} (m2 : 2 <= m)
 (md : m * m ∣ n) : d <= m
参数：h : n.minSqFac = some d；m2 : 2 <= m；md : m * m ∣ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.minSqFac_has_prop`：minSqFac_has_prop (n : Nat) : MinSqFacProp n (min
SqFac n)
· 使用定理 `Nat.minFac_dvd`：minFac_dvd (n : Nat) : minFac n ∣ n
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.minFac_prime`：minFac_prime {n : Nat} (n1 : n != 1) : Prime (minFac n
)
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `dvd_trans`：dvd_trans : a ∣ b -> b ∣ c -> a ∣ c | ⟨d, h₁⟩, ⟨e, h₂⟩ => ⟨d 
* e, h₁ ▸ h₂.trans mul_assoc a d e⟩  alias Dvd.dvd.trans
· 使用定理 `mul_dvd_mul`：∀ {α : Type u_1} [inst : CommSemigroup α] {a b c d : α}, a 
∣ b → c ∣ d → a * c ∣ b * d
· 使用定理 `Nat.minFac_le`：minFac_le {n : Nat} (H : 0 < n) : minFac n <= n
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem minSqFac_le_of_dvd {n d : ℕ} (h : n.minSqFac = some d) {m} (m2 : 2 ≤ m) (md : m * m ∣ n) :
    d ≤ m := by
  have := minSqFac_has_prop n; rw [h] at this
  have fd := minFac_dvd m
  exact
    le_trans (this.2.2 _ (minFac_prime <| ne_of_gt m2) (dvd_trans (mul_dvd_mul fd fd) md))
      (minFac_le <| lt_of_lt_of_le (by decide) m2)
/-
**Nat.squarefree_iff_minSqFac** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：squarefree_iff_minSqFac {n : Nat} : Squarefree n ↔ n.minSqFac = none
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.minSqFac_has_prop`：minSqFac_has_prop (n : Nat) : MinSqFacProp n (min
SqFac n)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.squarefree_iff_prime_squarefree`：squarefree_iff_prime_squarefree {n 
: Nat} : Squarefree n ↔ forall x, Prime x -> ¬x * x ∣ n
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem squarefree_iff_minSqFac {n : ℕ} : Squarefree n ↔ n.minSqFac = none := by
  have := minSqFac_has_prop n
  constructor <;> intro H
  · rcases e : n.minSqFac with - | d
    · rfl
    rw [e] at this
    cases squarefree_iff_prime_squarefree.1 H _ this.1 this.2.1
  · rwa [H] at this
/-
**Nat.** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DecidablePred (Squarefree : ℕ → Prop) := fun _ =>
  decidable_of_iff' _ squarefree_iff_minSqFac
/-
**Nat.squarefree_two** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：squarefree_two : Squarefree 2
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.squarefree_iff_nodup_primeFactorsList`：squarefree_iff_nodup_primeFac
torsList {n : Nat} (h0 : n != 0) : Squarefree n ↔ n.primeFactorsList.Nodup
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Nat.primeFactorsList_two`：primeFactorsList_two : primeFactorsList 2 = [2
]
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem squarefree_two : Squarefree 2 := by
  rw [squarefree_iff_nodup_primeFactorsList] <;> simp
/-
**Nat.divisors_filter_squarefree_of_squarefree** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：divisors_filter_squarefree_of_squarefree {n : Nat} (hn : Squarefree n) : {
d in n.divisors | Squarefree d} = n.divisors
参数：hn : Squarefree n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Finset.filter_subset`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidableP
red p] (s : Finset α), Finset.filter p s ⊆ s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `Squarefree.squarefree_of_dvd`：Squarefree.squarefree_of_dvd [Monoid R] {x
 y : R} (hdvd : x ∣ y) (hsq : Squarefree y) : Squarefree x
· 使用定理 `Nat.dvd_of_mem_divisors`：dvd_of_mem_divisors {m : Nat} (h : n in divisor
s m) : n ∣ m
-/
theorem divisors_filter_squarefree_of_squarefree {n : ℕ} (hn : Squarefree n) :
    {d ∈ n.divisors | Squarefree d} = n.divisors :=
  Finset.ext fun d => ⟨@Finset.filter_subset _ _ _ _ d, fun hd =>
    Finset.mem_filter.mpr ⟨hd, hn.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd) ⟩⟩

open UniqueFactorizationMonoid
/-
**Nat.divisors_filter_squarefree** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：divisors_filter_squarefree {n : Nat} (h0 : n != 0) : {d in n.divisors | Sq
uarefree d}.val = (UniqueFactorizationMonoid.normalizedFactors n).toFinset.power
set.val.map fun x => x.val.prod
参数：h0 : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.Nodup.ext`：∀ {α : Type u_1} {s t : Multiset α}, s.Nodup → t.Nod
up → (s = t ↔ ∀ (a : α), a ∈ s ↔ a ∈ t)
· 使用定理 `Finset.nodup`：∀ {α : Type u_4} (self : Finset α), self.val.Nodup
· 使用定理 `Multiset.Nodup.map_on`：∀ {α : Type u_1} {β : Type v} {s : Multiset α} {f
 : α → β},   (∀ x ∈ s, ∀ y ∈ s, f x = f y → x = y) → s.Nodup → (Multiset.map f s
).Nodup
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.val_inj`：val_inj {s t : Finset α} : s.1 = t.1 ↔ s = t
· 使用定理 `Multiset.rel_eq`：rel_eq {s t : Multiset α} : Rel (· = ·) s t ↔ s = t
· 使用定理 `associated_eq_eq`：associated_eq_eq : (Associated : M -> M -> Prop) = Eq
· 使用定理 `UniqueFactorizationMonoid.factors_unique`：factors_unique {f g : Multiset
 α} (hf : forall x in f, Irreducible x) (hg : forall x in g, Irreducible x) (h :
 f.prod ~ᵤ g.prod) : Multiset.…
· 使用定理 `UniqueFactorizationMonoid.irreducible_of_normalized_factor`：irreducible_
of_normalized_factor {a : α} : forall x : α, x in normalizedFactors a -> Irreduc
ible x
· 使用定理 `Multiset.mem_toFinset`：mem_toFinset {a : α} {s : Multiset α} : a in s.to
Finset ↔ a in s
· 使用定理 `Finset.mem_powerset`：mem_powerset {s t : Finset α} : s in powerset t ↔ s
 subseteq t
· 使用定理 `Finset.mem_def`：mem_def {a : α} {s : Finset α} : a in s ↔ a in s.1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `associated_iff_eq`：associated_iff_eq {x y : M} : x ~ᵤ y ↔ x = y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Multiset.toFinset_subset`：toFinset_subset : s.toFinset subseteq t.toFins
et ↔ s subseteq t
· 使用定理 `Multiset.toFinset_val`：toFinset_val (s : Multiset α) : s.toFinset.1 = s.
dedup
· 使用定理 `Multiset.Nodup.dedup`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Multi
set α}, s.Nodup → s.dedup = s
· 使用定理 `UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors`：square
free_iff_nodup_normalizedFactors [NormalizationMonoid R] {x : R} (x0 : x != 0) :
 Squarefree x ↔ Multiset.Nodup (normalizedFactors x)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `mul_ne_zero_iff`：mul_ne_zero_iff : a * b != 0 ↔ a != 0 ∧ b != 0
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `UniqueFactorizationMonoid.normalizedFactors_mul`：normalizedFactors_mul {
x y : α} (hx : x != 0) (hy : y != 0) : normalizedFactors (x * y) = normalizedFac
tors x + normalizedFactors y
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
（共 45 条，此处仅展示前 30 条）
-/
theorem divisors_filter_squarefree {n : ℕ} (h0 : n ≠ 0) :
    {d ∈ n.divisors | Squarefree d}.val =
      (UniqueFactorizationMonoid.normalizedFactors n).toFinset.powerset.val.map fun x =>
        x.val.prod := by
  rw [(Finset.nodup _).ext ((Finset.nodup _).map_on _)]
  · intro a
    simp only [Multiset.mem_filter, Multiset.mem_map, Finset.filter_val, ← Finset.mem_def,
      mem_divisors]
    constructor
    · rintro ⟨⟨an, h0⟩, hsq⟩
      use (UniqueFactorizationMonoid.normalizedFactors a).toFinset
      simp only [Finset.mem_powerset]
      rcases an with ⟨b, rfl⟩
      rw [mul_ne_zero_iff] at h0
      rw [UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors h0.1] at hsq
      rw [Multiset.toFinset_subset, Multiset.toFinset_val, hsq.dedup, ← associated_iff_eq,
        normalizedFactors_mul h0.1 h0.2]
      exact ⟨Multiset.subset_of_le (Multiset.le_add_right _ _), prod_normalizedFactors h0.1⟩
    · rintro ⟨s, hs, rfl⟩
      rw [Finset.mem_powerset, ← Finset.val_le_iff, Multiset.toFinset_val] at hs
      have hs0 : s.val.prod ≠ 0 := by
        rw [Ne, Multiset.prod_eq_zero_iff]
        intro con
        apply
          not_irreducible_zero
            (irreducible_of_normalized_factor 0 (Multiset.mem_dedup.1 (Multiset.mem_of_le hs con)))
      rw [(prod_normalizedFactors h0).symm.dvd_iff_dvd_right]
      refine ⟨⟨Multiset.prod_dvd_prod_of_le (le_trans hs (Multiset.dedup_le _)), h0⟩, ?_⟩
      have h :=
        UniqueFactorizationMonoid.factors_unique irreducible_of_normalized_factor
          (fun x hx =>
            irreducible_of_normalized_factor x
              (Multiset.mem_of_le (le_trans hs (Multiset.dedup_le _)) hx))
          (prod_normalizedFactors hs0)
      rw [associated_eq_eq, Multiset.rel_eq] at h
      rw [UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hs0, h]
      apply s.nodup
  · intro x hx y hy h
    rw [← Finset.val_inj, ← Multiset.rel_eq, ← associated_eq_eq]
    rw [← Finset.mem_def, Finset.mem_powerset] at hx hy
    apply UniqueFactorizationMonoid.factors_unique _ _ (associated_iff_eq.2 h)
    · intro z hz
      apply irreducible_of_normalized_factor z
      · rw [← Multiset.mem_toFinset]
        apply hx hz
    · intro z hz
      apply irreducible_of_normalized_factor z
      · rw [← Multiset.mem_toFinset]
        apply hy hz
/-
**Nat.sum_divisors_filter_squarefree** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：sum_divisors_filter_squarefree {n : Nat} (h0 : n != 0) {α : Type*} [AddCom
mMonoid α] {f : Nat -> α} : ∑ d in n.divisors with Squarefree d, f d = ∑ i in (U
niqueFactorizationMonoid.normalizedFactors n).toFinset.powerset, f i.val.prod
参数：h0 : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_eq_multiset_sum`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddC
ommMonoid M] (s : Finset ι) (f : ι → M),   ∑ x ∈ s, f x = (Multiset.map f s.val)
.sum
· 使用定理 `Nat.divisors_filter_squarefree`：divisors_filter_squarefree {n : Nat} (h0
 : n != 0) : {d in n.divisors | Squarefree d}.val = (UniqueFactorizationMonoid.n
ormalizedFactors n).…
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
-/
theorem sum_divisors_filter_squarefree {n : ℕ} (h0 : n ≠ 0) {α : Type*} [AddCommMonoid α]
    {f : ℕ → α} :
    ∑ d ∈ n.divisors with Squarefree d, f d =
      ∑ i ∈ (UniqueFactorizationMonoid.normalizedFactors n).toFinset.powerset, f i.val.prod := by
  rw [Finset.sum_eq_multiset_sum, divisors_filter_squarefree h0, Multiset.map_map,
    Finset.sum_eq_multiset_sum]
  rfl
/-
**Nat.sq_mul_squarefree_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：sq_mul_squarefree_of_pos {n : Nat} (hn : 0 < n) : exists a b : Nat, 0 < a 
∧ 0 < b ∧ b ^ 2 * a = n ∧ Squarefree a
参数：hn : 0 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
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
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
· 使用定理 `Finset.max'_mem`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) 
(H : s.Nonempty), s.max' H ∈ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CanonicallyOrderedAdd.mul_pos`：∀ {R : Type u} [inst : CommSemiring R] [i
nst_1 : PartialOrder R] [CanonicallyOrderedAdd R] [NoZeroDivisors R] {a b : R}, 
  0 < a * b ↔ 0 < a…
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用引理 `pow_pos_iff`：pow_pos_iff (hn : n != 0) : 0 < a ^ n ↔ 0 < a
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.isUnit_iff`：∀ {n : ℕ}, IsUnit n ↔ n = 1
（共 70 条，此处仅展示前 30 条）
-/
theorem sq_mul_squarefree_of_pos {n : ℕ} (hn : 0 < n) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ b ^ 2 * a = n ∧ Squarefree a := by
  classical
  set S := {s ∈ range (n + 1) | s ∣ n ∧ ∃ x, s = x ^ 2}
  have hSne : S.Nonempty := by
    use 1
    have h1 : 0 < n ∧ ∃ x : ℕ, 1 = x ^ 2 := ⟨hn, ⟨1, (one_pow 2).symm⟩⟩
    simp [S, h1]
  let s := Finset.max' S hSne
  have hs : s ∈ S := Finset.max'_mem S hSne
  simp only [S, Finset.mem_filter, Finset.mem_range] at hs
  obtain ⟨-, ⟨a, hsa⟩, ⟨b, hsb⟩⟩ := hs
  rw [hsa] at hn
  obtain ⟨hlts, hlta⟩ := CanonicallyOrderedAdd.mul_pos.mp hn
  rw [hsb] at hsa hn hlts
  refine ⟨a, b, hlta, (pow_pos_iff two_ne_zero).mp hlts, hsa.symm, ?_⟩
  rintro x ⟨y, hy⟩
  rw [Nat.isUnit_iff]
  by_contra hx
  refine Nat.lt_le_asymm ?_ (Finset.le_max' S ((b * x) ^ 2) ?_)
  · convert!
      lt_mul_of_one_lt_right hlts
        (one_lt_pow two_ne_zero (one_lt_iff_ne_zero_and_ne_one.mpr ⟨fun h => by simp_all, hx⟩))
    using 1
    rw [mul_pow]
  · simp_rw [S, hsa, Finset.mem_filter, Finset.mem_range]
    refine ⟨Nat.lt_succ_iff.mpr (le_of_dvd hn ?_), ?_, ⟨b * x, rfl⟩⟩ <;> use y <;> rw [hy] <;> ring
/-
**Nat.sq_mul_squarefree_of_pos'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：sq_mul_squarefree_of_pos' {n : Nat} (h : 0 < n) : exists a b : Nat, (b + 1
) ^ 2 * (a + 1) = n ∧ Squarefree (a + 1)
参数：h : 0 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.sq_mul_squarefree_of_pos`：sq_mul_squarefree_of_pos {n : Nat} (hn : 0
 < n) : exists a b : Nat, 0 < a ∧ 0 < b ∧ b ^ 2 * a = n ∧ Squarefree a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.succ_pred_eq_of_pos`：∀ {n : ℕ}, 0 < n → n.pred.succ = n
-/
theorem sq_mul_squarefree_of_pos' {n : ℕ} (h : 0 < n) :
    ∃ a b : ℕ, (b + 1) ^ 2 * (a + 1) = n ∧ Squarefree (a + 1) := by
  obtain ⟨a₁, b₁, ha₁, hb₁, hab₁, hab₂⟩ := sq_mul_squarefree_of_pos h
  refine ⟨a₁.pred, b₁.pred, ?_, ?_⟩ <;> simpa only [add_one, succ_pred_eq_of_pos, ha₁, hb₁]
/-
**Nat.sq_mul_squarefree** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：sq_mul_squarefree (n : Nat) : exists a b : Nat, b ^ 2 * a = n ∧ Squarefree
 a
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `squarefree_one`：squarefree_one [CommMonoid R] : Squarefree (1 : R)
· 使用定理 `Nat.sq_mul_squarefree_of_pos`：sq_mul_squarefree_of_pos {n : Nat} (hn : 0
 < n) : exists a b : Nat, 0 < a ∧ 0 < b ∧ b ^ 2 * a = n ∧ Squarefree a
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
-/
theorem sq_mul_squarefree (n : ℕ) : ∃ a b : ℕ, b ^ 2 * a = n ∧ Squarefree a := by
  rcases n with - | n
  · exact ⟨1, 0, by simp, squarefree_one⟩
  · obtain ⟨a, b, -, -, h₁, h₂⟩ := sq_mul_squarefree_of_pos (succ_pos n)
    exact ⟨a, b, h₁, h₂⟩

/-- `Squarefree` is multiplicative. Note that the → direction does not require `hmn`
and generalizes to arbitrary commutative monoids. See `Squarefree.of_mul_left` and
`Squarefree.of_mul_right` above for auxiliary lemmas. -/
/-
**Nat.squarefree_mul** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：squarefree_mul {m n : Nat} (hmn : m.Coprime n) : Squarefree (m * n) ↔ Squa
refree m ∧ Squarefree n
参数：hmn : m.Coprime n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instDecompositionMonoidOfIsGCDMonoid`：∀ {α : Type u_1} [inst : CommMonoi
dWithZero α] [h : IsGCDMonoid α], DecompositionMonoid α
· 使用定理 `instIsGCDMonoidOfUniqueFactorizationMonoid`：∀ (α : Type u_2) [inst : Com
mMonoidWithZero α] [UniqueFactorizationMonoid α], IsGCDMonoid α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.coprime_iff_isRelPrime`：coprime_iff_isRelPrime {m n : Nat} : m.Copri
me n ↔ IsRelPrime m n
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
`Squarefree` is multiplicative. Note that the → direction does not require `hmn`
and generalizes to arbitrary commutative monoids. See `Squarefree.of_mul_left` a
nd
`Squarefree.of_mul_right` above for auxiliary lemmas.
-/
theorem squarefree_mul {m n : ℕ} (hmn : m.Coprime n) :
    Squarefree (m * n) ↔ Squarefree m ∧ Squarefree n := by
  simp [squarefree_mul_iff, Nat.coprime_iff_isRelPrime.mp hmn]
/-
**Nat.coprime_of_squarefree_mul** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：coprime_of_squarefree_mul {m n : Nat} (h : Squarefree (m * n)) : m.Coprime
 n
参数：h : Squarefree (m * n)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.coprime_of_dvd`：coprime_of_dvd {m n : Nat} (H : forall k, Prime k ->
 k ∣ m -> ¬k ∣ n) : Coprime m n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.squarefree_iff_prime_squarefree`：squarefree_iff_prime_squarefree {n 
: Nat} : Squarefree n ↔ forall x, Prime x -> ¬x * x ∣ n
· 使用定理 `mul_dvd_mul`：∀ {α : Type u_1} [inst : CommSemigroup α] {a b c d : α}, a 
∣ b → c ∣ d → a * c ∣ b * d
-/
theorem coprime_of_squarefree_mul {m n : ℕ} (h : Squarefree (m * n)) : m.Coprime n :=
  coprime_of_dvd fun p hp hm hn => squarefree_iff_prime_squarefree.mp h p hp (mul_dvd_mul hm hn)
/-
**Nat.squarefree_mul_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：squarefree_mul_iff {m n : Nat} : Squarefree (m * n) ↔ m.Coprime n ∧ Square
free m ∧ Squarefree n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `squarefree_mul_iff`：squarefree_mul_iff : Squarefree (x * y) ↔ IsRelPrime
 x y ∧ Squarefree x ∧ Squarefree y
· 使用定理 `instDecompositionMonoidOfIsGCDMonoid`：∀ {α : Type u_1} [inst : CommMonoi
dWithZero α] [h : IsGCDMonoid α], DecompositionMonoid α
· 使用定理 `instIsGCDMonoidOfUniqueFactorizationMonoid`：∀ (α : Type u_2) [inst : Com
mMonoidWithZero α] [UniqueFactorizationMonoid α], IsGCDMonoid α
· 使用定理 `Nat.coprime_iff_isRelPrime`：coprime_iff_isRelPrime {m n : Nat} : m.Copri
me n ↔ IsRelPrime m n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem squarefree_mul_iff {m n : ℕ} :
    Squarefree (m * n) ↔ m.Coprime n ∧ Squarefree m ∧ Squarefree n := by
  rw [_root_.squarefree_mul_iff, Nat.coprime_iff_isRelPrime]
/-
**Nat.coprime_div_gcd_of_squarefree** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：coprime_div_gcd_of_squarefree (hm : Squarefree m) (hn : n != 0) : Coprime 
(m / gcd m n) n
参数：hm : Squarefree m；hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.coprime_of_squarefree_mul`：coprime_of_squarefree_mul {m n : Nat} (h 
: Squarefree (m * n)) : m.Coprime n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.div_mul_cancel`：∀ {n m : ℕ}, n ∣ m → m / n * n = m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.Coprime.mul_right`：∀ {k m n : ℕ}, k.Coprime m → k.Coprime n → k.Copr
ime (m * n)
· 使用定理 `Nat.coprime_div_gcd_div_gcd`：∀ {m n : ℕ}, 0 < m.gcd n → (m / m.gcd n).Co
prime (n / m.gcd n)
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
· 使用定理 `Nat.gcd_ne_zero_right`：∀ {n m : ℕ}, n ≠ 0 → m.gcd n ≠ 0
-/
lemma coprime_div_gcd_of_squarefree (hm : Squarefree m) (hn : n ≠ 0) : Coprime (m / gcd m n) n := by
  have : Coprime (m / gcd m n) (gcd m n) :=
    coprime_of_squarefree_mul <| by simpa [Nat.div_mul_cancel, gcd_dvd_left]
  simpa [Nat.div_mul_cancel, gcd_dvd_right] using
    (coprime_div_gcd_div_gcd (m := m) (gcd_ne_zero_right hn).bot_lt).mul_right this
/-
**Nat.prod_primeFactors_of_squarefree** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：prod_primeFactors_of_squarefree (hn : Squarefree n) : ∏ p in n.primeFactor
s, p = n
参数：hn : Squarefree n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.toFinset_factors`：∀ (n : ℕ), n.primeFactorsList.toFinset = n.primeFa
ctors
· 使用定理 `List.prod_toFinset`：prod_toFinset {M : Type*} [DecidableEq ι] [CommMonoi
d M] (f : ι -> M) : forall {l : List ι} (_hl : l.Nodup), l.toFinset.prod f = (l.
map f).p…
· 使用定理 `Squarefree.nodup_primeFactorsList`：Squarefree.nodup_primeFactorsList {n 
: Nat} (hn : Squarefree n) : n.primeFactorsList.Nodup
· 使用定理 `List.map_id'`：∀ {α : Type u_1} (l : List α), List.map (fun a => a) l = l
· 使用定理 `Nat.prod_primeFactorsList`：prod_primeFactorsList : forall {n}, n != 0 ->
 List.prod (primeFactorsList n) = n | 0 => by simp | 1 => by simp | k + 2 => fun
 _ => let m
· 使用定理 `Squarefree.ne_zero`：Squarefree.ne_zero [MonoidWithZero R] [Nontrivial R]
 {m : R} (hm : Squarefree (m : R)) : m != 0
-/
lemma prod_primeFactors_of_squarefree (hn : Squarefree n) : ∏ p ∈ n.primeFactors, p = n := by
  rw [← toFinset_factors, List.prod_toFinset _ hn.nodup_primeFactorsList,
    List.map_id', Nat.prod_primeFactorsList hn.ne_zero]
/-
**Nat.primeFactors_prod** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：primeFactors_prod (hs : forall p in s, p.Prime) : primeFactors (∏ p in s, 
p) = s
参数：hs : forall p in s, p.Prime。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Finset.prod_ne_zero_iff`：prod_ne_zero_iff : ∏ x in s, f x != 0 ↔ forall 
a in s, f a != 0
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.mem_primeFactors_of_ne_zero`：mem_primeFactors_of_ne_zero (hn : n != 
0) : p in n.primeFactors ↔ p.Prime ∧ p ∣ n
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用定理 `Prime.dvd_finsetProd_iff`：Prime.dvd_finsetProd_iff {S : Finset M₀} {p : 
M} (pp : Prime p) (g : M₀ -> M) : p ∣ S.prod g ↔ exists a in S, p ∣ g a
· 使用定理 `Nat.Prime.prime`：∀ {p : ℕ}, Nat.Prime p → Prime p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.Prime.dvd_iff_eq`：∀ {p a : ℕ}, Nat.Prime p → a ≠ 1 → (a ∣ p ↔ p = a)
· 使用定理 `Nat.Prime.ne_one`：∀ {p : ℕ}, Nat.Prime p → p ≠ 1
· 使用定理 `dvd_rfl`：dvd_rfl : forall {a : α}, a ∣ a
-/
lemma primeFactors_prod (hs : ∀ p ∈ s, p.Prime) : primeFactors (∏ p ∈ s, p) = s := by
  have hn : ∏ p ∈ s, p ≠ 0 := prod_ne_zero_iff.2 fun p hp ↦ (hs _ hp).ne_zero
  ext p
  rw [mem_primeFactors_of_ne_zero hn, and_congr_right (fun hp ↦ hp.prime.dvd_finsetProd_iff _)]
  refine ⟨?_, fun hp ↦ ⟨hs _ hp, _, hp, dvd_rfl⟩⟩
  rintro ⟨hp, q, hq, hpq⟩
  rwa [← ((hs _ hq).dvd_iff_eq hp.ne_one).1 hpq]
/-
**Nat.primeFactors_prod_primeFactors** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：primeFactors_prod_primeFactors (n : Nat) : (∏ p in n.primeFactors, p).prim
eFactors = n.primeFactors
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.primeFactors_prod`：primeFactors_prod (hs : forall p in s, p.Prime) :
 primeFactors (∏ p in s, p) = s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.mem_primeFactors`：∀ {n p : ℕ}, p ∈ n.primeFactors ↔ Nat.Prime p ∧ p 
∣ n ∧ n ≠ 0
-/
theorem primeFactors_prod_primeFactors (n : ℕ) :
    (∏ p ∈ n.primeFactors, p).primeFactors = n.primeFactors :=
  primeFactors_prod fun _ hp ↦ n.mem_primeFactors.mp hp |>.left
/-
**Nat.prod_primeFactors_dvd_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：prod_primeFactors_dvd_iff {n k : Nat} (hk : k != 0) : (∏ p in n.primeFacto
rs, p) ∣ k ↔ n.primeFactors subseteq k.primeFactors
参数：hk : k != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `Nat.primeFactors_mono`：primeFactors_mono (hmn : m ∣ n) (hn : n != 0) : p
rimeFactors m subseteq primeFactors n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.primeFactors_prod_primeFactors`：primeFactors_prod_primeFactors (n : 
Nat) : (∏ p in n.primeFactors, p).primeFactors = n.primeFactors
· 使用引理 `Mathlib.Tactic.GCongr.rel_imp_rel`：rel_imp_rel (h₁ : r c a) (h₂ : r b d)
 : r a b -> r c d
· 使用定理 `instIsTransDvd`：∀ {α : Type u_1} [inst : Semigroup α], IsTrans α Dvd.dvd
· 使用定理 `dvd_refl`：dvd_refl (a : α) : a ∣ a
· 使用定理 `Nat.prod_primeFactors_dvd`：prod_primeFactors_dvd (n : Nat) : ∏ p in n.pr
imeFactors, p ∣ n
· 使用定理 `Finset.prod_dvd_prod_of_subset`：prod_dvd_prod_of_subset {ι M : Type*} [C
ommMonoid M] (s t : Finset ι) (f : ι -> M) (h : s subseteq t) : (∏ i in s, f i) 
∣ ∏ i in t, f i
-/
theorem prod_primeFactors_dvd_iff {n k : ℕ} (hk : k ≠ 0) :
    (∏ p ∈ n.primeFactors, p) ∣ k ↔ n.primeFactors ⊆ k.primeFactors := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · grw [← Nat.primeFactors_mono h hk, primeFactors_prod_primeFactors]
  · grw [← k.prod_primeFactors_dvd, Finset.prod_dvd_prod_of_subset _ _ _ h]
/-
**Nat.primeFactors_div_gcd** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：primeFactors_div_gcd (hm : Squarefree m) (hn : n != 0) : primeFactors (m /
 m.gcd n) = primeFactors m \ primeFactors n
参数：hm : Squarefree m；hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Nat.gcd_ne_zero_right`：∀ {n m : ℕ}, n ≠ 0 → m.gcd n ≠ 0
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Nat.gcd_le_left`：∀ {m : ℕ} (n : ℕ), 0 < m → m.gcd n ≤ m
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
· 使用定理 `Squarefree.ne_zero`：Squarefree.ne_zero [MonoidWithZero R] [Nontrivial R]
 {m : R} (hm : Squarefree (m : R)) : m != 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.dvd_div_iff_mul_dvd`：∀ {a b c : ℕ}, c ∣ b → (a ∣ b / c ↔ c * a ∣ b)
· 使用定理 `Nat.gcd_dvd_left`：∀ (m n : ℕ), m.gcd n ∣ m
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `dvd_of_mul_left_dvd`：dvd_of_mul_left_dvd (h : a * b ∣ c) : b ∣ c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Irreducible.not_isUnit`：∀ {M : Type u_1} [inst : Monoid M] {p : M}, Irre
ducible p → ¬IsUnit p
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `mul_dvd_mul_right`：mul_dvd_mul_right (h : a ∣ b) (c : α) : a * c ∣ b * c
· 使用定理 `Nat.dvd_gcd`：∀ {k m n : ℕ}, k ∣ m → k ∣ n → k ∣ m.gcd n
· 使用定理 `Nat.Coprime.mul_dvd_of_dvd_of_dvd`：∀ {m n a : ℕ}, m.Coprime n → m ∣ a → 
n ∣ a → m * n ∣ a
· 使用定理 `Nat.coprime_comm`：∀ {n m : ℕ}, n.Coprime m ↔ m.Coprime n
· 使用定理 `Nat.Prime.coprime_iff_not_dvd`：∀ {p n : ℕ}, Nat.Prime p → (p.Coprime n ↔
 ¬p ∣ n)
· 使用定理 `Nat.gcd_dvd_right`：∀ (m n : ℕ), m.gcd n ∣ n
-/
lemma primeFactors_div_gcd (hm : Squarefree m) (hn : n ≠ 0) :
    primeFactors (m / m.gcd n) = primeFactors m \ primeFactors n := by
  ext p
  have : m / m.gcd n ≠ 0 := by simp [gcd_ne_zero_right hn, gcd_le_left _ hm.ne_zero.bot_lt]
  simp only [mem_primeFactors, ne_eq, this, not_false_eq_true, and_true, not_and, mem_sdiff,
    hm.ne_zero, hn, dvd_div_iff_mul_dvd (gcd_dvd_left _ _)]
  refine ⟨fun hp ↦ ⟨⟨hp.1, dvd_of_mul_left_dvd hp.2⟩, fun _ hpn ↦ hp.1.not_isUnit <| hm _ <|
    (mul_dvd_mul_right (dvd_gcd (dvd_of_mul_left_dvd hp.2) hpn) _).trans hp.2⟩, fun hp ↦
      ⟨hp.1.1, Coprime.mul_dvd_of_dvd_of_dvd ?_ (gcd_dvd_left _ _) hp.1.2⟩⟩
  rw [coprime_comm, hp.1.1.coprime_iff_not_dvd]
  exact fun hpn ↦ hp.2 hp.1.1 <| hpn.trans <| gcd_dvd_right _ _
/-
**Nat.prod_primeFactors_invOn_squarefree** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：prod_primeFactors_invOn_squarefree : Set.InvOn (fun n : Nat => (factorizat
ion n).support) (fun s => ∏ p in s, p) {s | forall p in s, p.Prime} {n | Squaref
ree n}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.primeFactors_prod`：primeFactors_prod (hs : forall p in s, p.Prime) :
 primeFactors (∏ p in s, p) = s
· 使用引理 `Nat.prod_primeFactors_of_squarefree`：prod_primeFactors_of_squarefree (hn
 : Squarefree n) : ∏ p in n.primeFactors, p = n
-/
lemma prod_primeFactors_invOn_squarefree :
    Set.InvOn (fun n : ℕ ↦ (factorization n).support) (fun s ↦ ∏ p ∈ s, p)
      {s | ∀ p ∈ s, p.Prime} {n | Squarefree n} :=
  ⟨fun _s ↦ primeFactors_prod, fun _n ↦ prod_primeFactors_of_squarefree⟩
/-
**Nat.prod_primeFactors_sdiff_of_squarefree** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：prod_primeFactors_sdiff_of_squarefree {n : Nat} (hn : Squarefree n) {t : F
inset Nat} (ht : t subseteq n.primeFactors) : ∏ a in (n.primeFactors \ t), a = n
 / ∏ a in t, a
参数：hn : Squarefree n；ht : t subseteq n.primeFactors。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `symm`：symm [Std.Symm r] : a ≺ b -> b ≺ a
· 使用定理 `IsEquiv.toSymm`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEquiv α r]
, Std.Symm r
· 使用定理 `Nat.div_eq_of_eq_mul_left`：∀ {n m k : ℕ}, 0 < n → m = k * n → m / n = k
· 使用引理 `Finset.prod_pos`：prod_pos (h0 : forall i in s, 0 < f i) : 0 < ∏ i in s, 
f i
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `Nat.Prime.pos`：∀ {p : ℕ}, Nat.Prime p → 0 < p
· 使用定理 `Nat.prime_of_mem_primeFactorsList`：prime_of_mem_primeFactorsList {n : Na
t} : forall {p : Nat}, p in primeFactorsList n -> Prime p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.mem_toFinset`：mem_toFinset : a in l.toFinset ↔ a in l
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_sdiff`：prod_sdiff [DecidableEq ι] (h : s₁ subseteq s₂) : (∏ 
x in s₂ \ s₁, f x) * ∏ x in s₁, f x = ∏ x in s₂, f x
· 使用引理 `Nat.prod_primeFactors_of_squarefree`：prod_primeFactors_of_squarefree (hn
 : Squarefree n) : ∏ p in n.primeFactors, p = n
-/
theorem prod_primeFactors_sdiff_of_squarefree {n : ℕ} (hn : Squarefree n) {t : Finset ℕ}
    (ht : t ⊆ n.primeFactors) :
    ∏ a ∈ (n.primeFactors \ t), a = n / ∏ a ∈ t, a := by
  refine symm <| Nat.div_eq_of_eq_mul_left (Finset.prod_pos
    fun p hp => (prime_of_mem_primeFactorsList (List.mem_toFinset.mp (ht hp))).pos) ?_
  rw [Finset.prod_sdiff ht, prod_primeFactors_of_squarefree hn]

end Nat

-- Porting note: comment out NormNum tactic, to be moved to another file.
/-

/-! ### Square-free prover -/


open NormNum

namespace Tactic

namespace NormNum

/-- A predicate representing partial progress in a proof of `Squarefree`. -/
def SquarefreeHelper (n k : ℕ) : Prop :=
  0 < k → (∀ m, Nat.Prime m → m ∣ bit1 n → bit1 k ≤ m) → Squarefree (bit1 n)

theorem squarefree_bit10 (n : ℕ) (h : SquarefreeHelper n 1) : Squarefree (bit0 (bit1 n)) := by
  refine' @Nat.minSqFacProp_div _ _ Nat.prime_two two_dvd_bit0 _ none _
  · rw [bit0_eq_two_mul (bit1 n), mul_dvd_mul_iff_left (two_ne_zero' ℕ)]
    exact Nat.not_two_dvd_bit1 _
  · rw [bit0_eq_two_mul, Nat.mul_div_right _ (by decide : 0 < 2)]
    refine' h (by decide) fun p pp dp => Nat.succ_le_of_lt (lt_of_le_of_ne pp.two_le _)
    rintro rfl
    exact Nat.not_two_dvd_bit1 _ dp

theorem squarefree_bit1 (n : ℕ) (h : SquarefreeHelper n 1) : Squarefree (bit1 n) := by
  refine' h (by decide) fun p pp dp => Nat.succ_le_of_lt (lt_of_le_of_ne pp.two_le _)
  rintro rfl; exact Nat.not_two_dvd_bit1 _ dp

theorem squarefree_helper_0 {k} (k0 : 0 < k) {p : ℕ} (pp : Nat.Prime p) (h : bit1 k ≤ p) :
    bit1 (k + 1) ≤ p ∨ bit1 k = p := by
  rcases lt_or_eq_of_le h with ((hp : _ + 1 ≤ _) | hp)
  · rw [bit1, bit0_eq_two_mul] at hp
    change 2 * (_ + 1) ≤ _ at hp
    rw [bit1, bit0_eq_two_mul]
    refine' Or.inl (lt_of_le_of_ne hp _)
    rintro rfl
    exact Nat.not_prime_mul (by decide) (lt_add_of_pos_left _ k0) pp
  · exact Or.inr hp

theorem squarefreeHelper_1 (n k k' : ℕ) (e : k + 1 = k')
    (hk : Nat.Prime (bit1 k) → ¬bit1 k ∣ bit1 n) (H : SquarefreeHelper n k') :
    SquarefreeHelper n k := fun k0 ih => by
  subst e
  refine' H (Nat.succ_pos _) fun p pp dp => _
  refine' (squarefree_helper_0 k0 pp (ih p pp dp)).resolve_right fun hp => _
  subst hp; cases hk pp dp

theorem squarefreeHelper_2 (n k k' c : ℕ) (e : k + 1 = k') (hc : bit1 n % bit1 k = c) (c0 : 0 < c)
    (h : SquarefreeHelper n k') : SquarefreeHelper n k := by
  refine' squarefree_helper_1 _ _ _ e (fun _ => _) h
  refine' mt _ (ne_of_gt c0); intro e₁
  rwa [← hc, ← Nat.dvd_iff_mod_eq_zero]

theorem squarefreeHelper_3 (n n' k k' c : ℕ) (e : k + 1 = k') (hn' : bit1 n' * bit1 k = bit1 n)
    (hc : bit1 n' % bit1 k = c) (c0 : 0 < c) (H : SquarefreeHelper n' k') : SquarefreeHelper n k :=
  fun k0 ih => by
  subst e
  have k0' : 0 < bit1 k := bit1_pos (Nat.zero_le _)
  have dn' : bit1 n' ∣ bit1 n := ⟨_, hn'.symm⟩
  have dk : bit1 k ∣ bit1 n := ⟨_, ((mul_comm _ _).trans hn').symm⟩
  have : bit1 n / bit1 k = bit1 n' := by rw [← hn', Nat.mul_div_cancel _ k0']
  have k2 : 2 ≤ bit1 k := Nat.succ_le_succ (bit0_pos k0)
  have pk : (bit1 k).Prime := by
    refine' Nat.prime_def_minFac.2 ⟨k2, le_antisymm (Nat.minFac_le k0') _⟩
    exact ih _ (Nat.minFac_prime (ne_of_gt k2)) (dvd_trans (Nat.minFac_dvd _) dk)
  have dkk' : ¬bit1 k ∣ bit1 n' := by
    rw [Nat.dvd_iff_mod_eq_zero, hc]
    exact ne_of_gt c0
  have dkk : ¬bit1 k * bit1 k ∣ bit1 n := by rwa [← Nat.dvd_div_iff_mul_dvd dk, this]
  refine' @Nat.minSqFacProp_div _ _ pk dk dkk none _
  rw [this]
  refine' H (Nat.succ_pos _) fun p pp dp => _
  refine' (squarefree_helper_0 k0 pp (ih p pp <| dvd_trans dp dn')).resolve_right fun e => _
  subst e
  contradiction

theorem squarefreeHelper_4 (n k k' : ℕ) (e : bit1 k * bit1 k = k') (hd : bit1 n < k') :
    SquarefreeHelper n k := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst n
    exact fun _ _ => squarefree_one
  subst e
  refine' fun k0 ih => Irreducible.squarefree (Nat.prime_def_le_sqrt.2 ⟨bit1_lt_bit1.2 h, _⟩)
  intro m m2 hm md
  obtain ⟨p, pp, hp⟩ := Nat.exists_prime_and_dvd (ne_of_gt m2)
  have :=
    (ih p pp (dvd_trans hp md)).trans
      (le_trans (Nat.le_of_dvd (lt_of_lt_of_le (by decide) m2) hp) hm)
  rw [Nat.le_sqrt] at this
  exact not_le_of_gt hd this

theorem not_squarefree_mul (a aa b n : ℕ) (ha : a * a = aa) (hb : aa * b = n) (h₁ : 1 < a) :
    ¬Squarefree n := by
  rw [← hb, ← ha]
  exact fun H => ne_of_gt h₁ (Nat.isUnit_iff.1 <| H _ ⟨_, rfl⟩)

/-- Given `e` a natural numeral and `a : ℕ` with `a^2 ∣ n`, return `⊢ ¬ Squarefree e`. -/
unsafe def prove_non_squarefree (e : expr) (n a : ℕ) : tactic expr := do
  let ea := reflect a
  let eaa := reflect (a * a)
  let c ← mk_instance_cache q(Nat)
  let (c, p₁) ← prove_lt_nat c q(1) ea
  let b := n / (a * a)
  let eb := reflect b
  let (c, eaa, pa) ← prove_mul_nat c ea ea
  let (c, e', pb) ← prove_mul_nat c eaa eb
  guard (e' == e)
  return <| q(@not_squarefree_mul).mk_app [ea, eaa, eb, e, pa, pb, p₁]

/-- Given `en`,`en1 := bit1 en`, `n1` the value of `en1`, `ek`,
  returns `⊢ squarefree_helper en ek`. -/
unsafe def prove_squarefree_aux :
    ∀ (ic : instance_cache) (en en1 : expr) (n1 : ℕ) (ek : expr) (k : ℕ), tactic expr
  | ic, en, en1, n1, ek, k => do
    let k1 := bit1 k
    let ek1 := q((bit1 : ℕ → ℕ)).mk_app [ek]
    if n1 < k1 * k1 then do
        let (ic, ek', p₁) ← prove_mul_nat ic ek1 ek1
        let (ic, p₂) ← prove_lt_nat ic en1 ek'
        pure <| q(squarefreeHelper_4).mk_app [en, ek, ek', p₁, p₂]
      else do
        let c := n1 % k1
        let k' := k + 1
        let ek' := reflect k'
        let (ic, p₁) ← prove_succ ic ek ek'
        if c = 0 then do
            let n1' := n1 / k1
            let n' := n1' / 2
            let en' := reflect n'
            let en1' := q((bit1 : ℕ → ℕ)).mk_app [en']
            let (ic, _, pn') ← prove_mul_nat ic en1' ek1
            let c := n1' % k1
            guard (c ≠ 0)
            let (ic, ec, pc) ← prove_div_mod ic en1' ek1 tt
            let (ic, p₀) ← prove_pos ic ec
            let p₂ ← prove_squarefree_aux ic en' en1' n1' ek' k'
            pure <| q(squarefreeHelper_3).mk_app [en, en', ek, ek', ec, p₁, pn', pc, p₀, p₂]
          else do
            let (ic, ec, pc) ← prove_div_mod ic en1 ek1 tt
            let (ic, p₀) ← prove_pos ic ec
            let p₂ ← prove_squarefree_aux ic en en1 n1 ek' k'
            pure <| q(squarefreeHelper_2).mk_app [en, ek, ek', ec, p₁, pc, p₀, p₂]

/-- Given `n > 0` a squarefree natural numeral, returns `⊢ Squarefree n`. -/
unsafe def prove_squarefree (en : expr) (n : ℕ) : tactic expr :=
  match match_numeral en with
  | match_numeral_result.one => pure q(@squarefree_one ℕ _)
  | match_numeral_result.bit0 en1 =>
    match match_numeral en1 with
    | match_numeral_result.one => pure q(Nat.squarefree_two)
    | match_numeral_result.bit1 en => do
      let ic ← mk_instance_cache q(ℕ)
      let p ← prove_squarefree_aux ic en en1 (n / 2) q((1 : ℕ)) 1
      pure <| q(squarefree_bit10).mk_app [en, p]
    | _ => failed
  | match_numeral_result.bit1 en' => do
    let ic ← mk_instance_cache q(ℕ)
    let p ← prove_squarefree_aux ic en' en n q((1 : ℕ)) 1
    pure <| q(squarefree_bit1).mk_app [en', p]
  | _ => failed

/-- Evaluates the `Squarefree` predicate on naturals. -/
@[norm_num]
unsafe def eval_squarefree : expr → tactic (expr × expr)
  | q(@Squarefree ℕ $(inst) $(e)) => do
    is_def_eq inst q(Nat.monoid)
    let n ← e.toNat
    match n with
      | 0 => false_intro q(@not_squarefree_zero ℕ _ _)
      | 1 => true_intro q(@squarefree_one ℕ _)
      | _ =>
        match n with
        | some d => prove_non_squarefree e n d >>= false_intro
        | none => prove_squarefree e n >>= true_intro
  | _ => failed

end NormNum

end Tactic

-/

