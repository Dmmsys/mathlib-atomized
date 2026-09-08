/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module

public import Mathlib.Algebra.BigOperators.Ring.List
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.List.Prime
public import Mathlib.Data.List.Sort
public import Mathlib.Data.List.Perm.Subperm

/-!
# Prime numbers

This file deals with the factors of natural numbers.

## Important declarations

- `Nat.primeFactorsList n`: the prime factorization of `n`
- `Nat.primeFactorsList_unique`: uniqueness of the prime factorisation

-/

@[expose] public section

assert_not_exists Multiset

open Bool Subtype

open Nat

namespace Nat

/-- `primeFactorsList n` is the prime factorization of `n`, listed in increasing order. -/
/-
**Nat.primeFactorsList** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：primeFactorsList : Nat -> List Nat | 0 => [] | 1 => [] | k + 2 => let m
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`primeFactorsList n` is the prime factorization of `n`, listed in increasing ord
er.
-/
def primeFactorsList : ℕ → List ℕ
  | 0 => []
  | 1 => []
  | k + 2 =>
    let m := minFac (k + 2)
    m :: primeFactorsList ((k + 2) / m)
decreasing_by exact factors_lemma

@[simp]
/-
**Nat.primeFactorsList_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：primeFactorsList_zero : primeFactorsList 0 = []
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.primeFactorsList.eq_1`：Nat.primeFactorsList 0 = []
-/
theorem primeFactorsList_zero : primeFactorsList 0 = [] := by rw [primeFactorsList]

@[simp]
/-
**Nat.primeFactorsList_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：primeFactorsList_one : primeFactorsList 1 = []
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.primeFactorsList.eq_2`：Nat.primeFactorsList 1 = []
-/
theorem primeFactorsList_one : primeFactorsList 1 = [] := by rw [primeFactorsList]

@[simp]
/-
**Nat.primeFactorsList_two** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：primeFactorsList_two : primeFactorsList 2 = [2]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.primeFactorsList.eq_3`：∀ (k : ℕ), k.succ.succ.primeFactorsList = (k 
+ 2).minFac :: ((k + 2) / (k + 2).minFac).primeFactorsList
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.minFac_two`：minFac_two : minFac 2 = 2
· 使用定理 `Nat.div_self`：∀ {n : ℕ}, 0 < n → n / n = 1
· 使用定理 `Nat.primeFactorsList_one`：primeFactorsList_one : primeFactorsList 1 = []
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem primeFactorsList_two : primeFactorsList 2 = [2] := by simp [primeFactorsList]
/-
**Nat.prime_of_mem_primeFactorsList** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：prime_of_mem_primeFactorsList {n : Nat} : forall {p : Nat}, p in primeFact
orsList n -> Prime p
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.primeFactorsList_zero`：primeFactorsList_zero : primeFactorsList 0 = 
[]
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Nat.primeFactorsList_one`：primeFactorsList_one : primeFactorsList 1 = []
· 使用定理 `Nat.factors_lemma`：factors_lemma {k} : (k + 2) / minFac (k + 2) < k + 2
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.mem_cons`：∀ {α : Type u_1} {b : α} {l : List α} {a : α}, a ∈ b :: l
 ↔ a = b ∨ a ∈ l
· 使用定理 `Nat.primeFactorsList.eq_3`：∀ (k : ℕ), k.succ.succ.primeFactorsList = (k 
+ 2).minFac :: ((k + 2) / (k + 2).minFac).primeFactorsList
· 使用定理 `Nat.minFac_prime`：minFac_prime {n : Nat} (n1 : n != 1) : Prime (minFac n
)
· 使用定理 `Nat.Simproc.add_eq_gt`：∀ (a : ℕ) {b c : ℕ}, b > c → (a + b = c) = False
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem prime_of_mem_primeFactorsList {n : ℕ} : ∀ {p : ℕ}, p ∈ primeFactorsList n → Prime p := by
  match n with
  | 0 => simp
  | 1 => simp
  | k + 2 =>
      intro p h
      let m := minFac (k + 2)
      have : (k + 2) / m < (k + 2) := factors_lemma
      have h₁ : p = m ∨ p ∈ primeFactorsList ((k + 2) / m) :=
        List.mem_cons.1 (by rwa [primeFactorsList] at h)
      exact Or.casesOn h₁ (fun h₂ => h₂.symm ▸ minFac_prime (by simp)) prime_of_mem_primeFactorsList
/-
**Nat.pos_of_mem_primeFactorsList** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：pos_of_mem_primeFactorsList {n p : Nat} (h : p in primeFactorsList n) : 0 
< p
参数：h : p in primeFactorsList n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Prime.pos`：∀ {p : ℕ}, Nat.Prime p → 0 < p
· 使用定理 `Nat.prime_of_mem_primeFactorsList`：prime_of_mem_primeFactorsList {n : Na
t} : forall {p : Nat}, p in primeFactorsList n -> Prime p
-/
theorem pos_of_mem_primeFactorsList {n p : ℕ} (h : p ∈ primeFactorsList n) : 0 < p :=
  Prime.pos (prime_of_mem_primeFactorsList h)
/-
**Nat.prod_primeFactorsList** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：prod_primeFactorsList : forall {n}, n != 0 -> List.prod (primeFactorsList 
n) = n | 0 => by simp | 1 => by simp | k + 2 => fun _ => let m
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.primeFactorsList_zero`：primeFactorsList_zero : primeFactorsList 0 = 
[]
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Nat.primeFactorsList_one`：primeFactorsList_one : primeFactorsList 1 = []
· 使用定理 `Nat.factors_lemma`：factors_lemma {k} : (k + 2) / minFac (k + 2) < k + 2
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.div_eq_iff_eq_mul_left`：∀ {a b c : ℕ}, 0 < b → b ∣ a → (a / b = c ↔ 
a = c * b)
· 使用定理 `Nat.minFac_pos`：minFac_pos (n : Nat) : 0 < minFac n
· 使用定理 `Nat.minFac_dvd`：minFac_dvd (n : Nat) : minFac n ∣ n
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Nat.primeFactorsList.eq_3`：∀ (k : ℕ), k.succ.succ.primeFactorsList = (k 
+ 2).minFac :: ((k + 2) / (k + 2).minFac).primeFactorsList
· 使用定理 `List.prod_cons`：∀ {α : Type u} [inst : Mul α] [inst_1 : One α] {a : α} {
l : List α}, (a :: l).prod = a * l.prod
· 使用定理 `Nat.mul_div_cancel'`：∀ {n m : ℕ}, n ∣ m → n * (m / n) = m
-/
theorem prod_primeFactorsList : ∀ {n}, n ≠ 0 → List.prod (primeFactorsList n) = n
  | 0 => by simp
  | 1 => by simp
  | k + 2 => fun _ =>
    let m := minFac (k + 2)
    have : (k + 2) / m < (k + 2) := factors_lemma
    show (primeFactorsList (k + 2)).prod = (k + 2) by
      have h₁ : (k + 2) / m ≠ 0 := fun h => by
        have : (k + 2) = 0 * m := (Nat.div_eq_iff_eq_mul_left (minFac_pos _) (minFac_dvd _)).1 h
        rw [zero_mul] at this; exact (show k + 2 ≠ 0 by simp) this
      rw [primeFactorsList, List.prod_cons, prod_primeFactorsList h₁,
        Nat.mul_div_cancel' (minFac_dvd _)]
/-
**Nat.primeFactorsList_prime** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：primeFactorsList_prime {p : Nat} (hp : Nat.Prime p) : p.primeFactorsList =
 [p]
参数：hp : Nat.Prime p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_add_of_sub_eq`：∀ {a b c : ℕ}, b ≤ a → a - b = c → a = c + b
· 使用定理 `Nat.Prime.two_le`：∀ {p : ℕ}, Nat.Prime p → 2 ≤ p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.primeFactorsList.eq_3`：∀ (k : ℕ), k.succ.succ.primeFactorsList = (k 
+ 2).minFac :: ((k + 2) / (k + 2).minFac).primeFactorsList
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.prime_def_minFac`：prime_def_minFac {p : Nat} : Prime p ↔ 2 <= p ∧ mi
nFac p = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.div_self`：∀ {n : ℕ}, 0 < n → n / n = 1
· 使用定理 `Nat.Prime.pos`：∀ {p : ℕ}, Nat.Prime p → 0 < p
· 使用定理 `Nat.primeFactorsList.eq_2`：Nat.primeFactorsList 1 = []
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem primeFactorsList_prime {p : ℕ} (hp : Nat.Prime p) : p.primeFactorsList = [p] := by
  have : p = p - 2 + 2 := Nat.eq_add_of_sub_eq hp.two_le rfl
  rw [this, primeFactorsList]
  simp only [Eq.symm this]
  have : Nat.minFac p = p := (Nat.prime_def_minFac.mp hp).2
  simp only [this, primeFactorsList, Nat.div_self (Nat.Prime.pos hp)]
/-
**Nat.isChain_cons_primeFactorsList** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：isChain_cons_primeFactorsList {n : Nat} : forall {a}, (forall p, Prime p -
> p ∣ n -> a <= p) -> List.IsChain (· <= ·) (a :: primeFactorsList n)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.primeFactorsList_zero`：primeFactorsList_zero : primeFactorsList 0 = 
[]
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Nat.primeFactorsList_one`：primeFactorsList_one : primeFactorsList 1 = []
· 使用定理 `Nat.factors_lemma`：factors_lemma {k} : (k + 2) / minFac (k + 2) < k + 2
· 使用定理 `Nat.primeFactorsList.eq_3`：∀ (k : ℕ), k.succ.succ.primeFactorsList = (k 
+ 2).minFac :: ((k + 2) / (k + 2).minFac).primeFactorsList
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.le_minFac`：le_minFac {m n : Nat} : n = 1 ∨ m <= minFac n ↔ forall p,
 Prime p -> p ∣ n -> m <= p
· 使用定理 `Nat.Simproc.add_eq_gt`：∀ (a : ℕ) {b c : ℕ}, b > c → (a + b = c) = False
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Nat.minFac_le_of_dvd`：minFac_le_of_dvd {n : Nat} : forall {m : Nat}, 2 <
= m -> m ∣ n -> minFac n <= m
· 使用定理 `Nat.Prime.two_le`：∀ {p : ℕ}, Nat.Prime p → 2 ≤ p
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `Nat.div_dvd_of_dvd`：∀ {n m : ℕ}, n ∣ m → m / n ∣ m
· 使用定理 `Nat.minFac_dvd`：minFac_dvd (n : Nat) : minFac n ∣ n
-/
theorem isChain_cons_primeFactorsList {n : ℕ} :
    ∀ {a}, (∀ p, Prime p → p ∣ n → a ≤ p) → List.IsChain (· ≤ ·) (a :: primeFactorsList n) := by
  match n with
  | 0 => simp
  | 1 => simp
  | k + 2 =>
      intro a h
      let m := minFac (k + 2)
      have : (k + 2) / m < (k + 2) := factors_lemma
      rw [primeFactorsList]
      refine List.IsChain.cons_cons
        ((le_minFac.2 h).resolve_left (by simp)) (isChain_cons_primeFactorsList ?_)
      exact fun p pp d => minFac_le_of_dvd pp.two_le (d.trans <| div_dvd_of_dvd <| minFac_dvd _)
/-
**Nat.isChain_two_cons_primeFactorsList** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：isChain_two_cons_primeFactorsList (n) : List.IsChain (· <= ·) (2 :: primeF
actorsList n)
参数：n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.isChain_cons_primeFactorsList`：isChain_cons_primeFactorsList {n : Na
t} : forall {a}, (forall p, Prime p -> p ∣ n -> a <= p) -> List.IsChain (· <= ·)
 (a :: primeFactorsList…
· 使用定理 `Nat.Prime.two_le`：∀ {p : ℕ}, Nat.Prime p → 2 ≤ p
-/
theorem isChain_two_cons_primeFactorsList (n) : List.IsChain (· ≤ ·) (2 :: primeFactorsList n) :=
  isChain_cons_primeFactorsList fun _ pp _ => pp.two_le
/-
**Nat.isChain_primeFactorsList** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：isChain_primeFactorsList (n) : List.IsChain (· <= ·) (primeFactorsList n)
参数：n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.IsChain.tail`：∀ {α : Type u_1} {R : α → α → Prop} {l : List α}, Lis
t.IsChain R l → List.IsChain R l.tail
· 使用定理 `Nat.isChain_two_cons_primeFactorsList`：isChain_two_cons_primeFactorsList
 (n) : List.IsChain (· <= ·) (2 :: primeFactorsList n)
-/
theorem isChain_primeFactorsList (n) : List.IsChain (· ≤ ·) (primeFactorsList n) :=
  (isChain_two_cons_primeFactorsList _).tail
/-
**Nat.primeFactorsList_sorted** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：primeFactorsList_sorted (n : Nat) : List.SortedLE (primeFactorsList n)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.IsChain.sortedLE`：∀ {α : Type u_1} {l : List α} [inst : Preorder α]
, List.IsChain (fun x1 x2 => x1 ≤ x2) l → l.SortedLE
· 使用定理 `Nat.isChain_primeFactorsList`：isChain_primeFactorsList (n) : List.IsChai
n (· <= ·) (primeFactorsList n)
-/
theorem primeFactorsList_sorted (n : ℕ) : List.SortedLE (primeFactorsList n) :=
  (isChain_primeFactorsList _).sortedLE

/-- `primeFactorsList` can be constructed inductively by extracting `minFac`, for sufficiently
large `n`. -/
/-
**Nat.primeFactorsList_add_two** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：primeFactorsList_add_two (n : Nat) : primeFactorsList (n + 2) = minFac (n 
+ 2) :: primeFactorsList ((n + 2) / minFac (n + 2))
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.primeFactorsList.eq_3`：∀ (k : ℕ), k.succ.succ.primeFactorsList = (k 
+ 2).minFac :: ((k + 2) / (k + 2).minFac).primeFactorsList

--- 原说明 ---
`primeFactorsList` can be constructed inductively by extracting `minFac`, for su
fficiently
large `n`.
-/
theorem primeFactorsList_add_two (n : ℕ) :
    primeFactorsList (n + 2) = minFac (n + 2) :: primeFactorsList ((n + 2) / minFac (n + 2)) := by
  rw [primeFactorsList]

@[simp]
/-
**Nat.primeFactorsList_eq_nil** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：primeFactorsList_eq_nil (n : Nat) : n.primeFactorsList = [] ↔ n = 0 ∨ n = 
1
参数：n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.primeFactorsList.eq_3`：∀ (k : ℕ), k.succ.succ.primeFactorsList = (k 
+ 2).minFac :: ((k + 2) / (k + 2).minFac).primeFactorsList
· 使用定理 `Nat.primeFactorsList_zero`：primeFactorsList_zero : primeFactorsList 0 = 
[]
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.primeFactorsList_one`：primeFactorsList_one : primeFactorsList 1 = []
-/
theorem primeFactorsList_eq_nil (n : ℕ) : n.primeFactorsList = [] ↔ n = 0 ∨ n = 1 := by
  constructor <;> intro h
  · rcases n with (_ | _ | n)
    · exact Or.inl rfl
    · exact Or.inr rfl
    · rw [primeFactorsList] at h
      injection h
  · rcases h with (rfl | rfl)
    · exact primeFactorsList_zero
    · exact primeFactorsList_one
/-
**Nat.primeFactorsList_ne_nil** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：primeFactorsList_ne_nil (n : Nat) : n.primeFactorsList != [] ↔ 1 < n
参数：n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.primeFactorsList_eq_nil`：primeFactorsList_eq_nil (n : Nat) : n.prime
FactorsList = [] ↔ n = 0 ∨ n = 1
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem primeFactorsList_ne_nil (n : ℕ) : n.primeFactorsList ≠ [] ↔ 1 < n := by
  simp [primeFactorsList_eq_nil n, one_lt_iff_ne_zero_and_ne_one]

open scoped List in
/-
**Nat.eq_of_perm_primeFactorsList** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：eq_of_perm_primeFactorsList {a b : Nat} (ha : a != 0) (hb : b != 0) (h : a
.primeFactorsList ~ b.primeFactorsList) : a = b
参数：ha : a != 0；hb : b != 0；h : a.primeFactorsList ~ b.primeFactorsList。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.prod_primeFactorsList`：prod_primeFactorsList : forall {n}, n != 0 ->
 List.prod (primeFactorsList n) = n | 0 => by simp | 1 => by simp | k + 2 => fun
 _ => let m
· 使用定理 `List.Perm.prod_eq`：∀ {M : Type u_4} [inst : CommMonoid M] {l₁ l₂ : List 
M}, l₁.Perm l₂ → l₁.prod = l₂.prod
-/
theorem eq_of_perm_primeFactorsList {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : a.primeFactorsList ~ b.primeFactorsList) : a = b := by
  simpa [prod_primeFactorsList ha, prod_primeFactorsList hb] using List.Perm.prod_eq h

section

open List

/-
**Nat.mem_primeFactorsList_iff_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：mem_primeFactorsList_iff_dvd {n p : Nat} (hn : n != 0) (hp : Prime p) : p 
in primeFactorsList n ↔ p ∣ n where mp h
参数：hn : n != 0；hp : Prime p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.dvd_prod`：dvd_prod [CommMonoid M] {a} {l : List M} (ha : a in l) : 
a ∣ l.prod
· 使用定理 `Nat.prod_primeFactorsList`：prod_primeFactorsList : forall {n}, n != 0 ->
 List.prod (primeFactorsList n) = n | 0 => by simp | 1 => by simp | k + 2 => fun
 _ => let m
· 使用定理 `mem_list_primes_of_dvd_prod`：mem_list_primes_of_dvd_prod {p : M} (hp : P
rime p) {L : List M} (hL : forall q in L, Prime q) (hpL : p ∣ L.prod) : p in L
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.prime_iff`：prime_iff {p : Nat} : p.Prime ↔ _root_.Prime p
· 使用定理 `Nat.prime_of_mem_primeFactorsList`：prime_of_mem_primeFactorsList {n : Na
t} : forall {p : Nat}, p in primeFactorsList n -> Prime p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem mem_primeFactorsList_iff_dvd {n p : ℕ} (hn : n ≠ 0) (hp : Prime p) :
    p ∈ primeFactorsList n ↔ p ∣ n where
  mp h := prod_primeFactorsList hn ▸ List.dvd_prod h
  mpr h := mem_list_primes_of_dvd_prod (prime_iff.mp hp)
    (fun _ h ↦ prime_iff.mp (prime_of_mem_primeFactorsList h)) ((prod_primeFactorsList hn).symm ▸ h)
/-
**Nat.dvd_of_mem_primeFactorsList** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：dvd_of_mem_primeFactorsList {n p : Nat} (h : p in n.primeFactorsList) : p 
∣ n
参数：h : p in n.primeFactorsList。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `dvd_zero`：dvd_zero (a : α) : a ∣ 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.mem_primeFactorsList_iff_dvd`：mem_primeFactorsList_iff_dvd {n p : Na
t} (hn : n != 0) (hp : Prime p) : p in primeFactorsList n ↔ p ∣ n where mp h
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.prime_of_mem_primeFactorsList`：prime_of_mem_primeFactorsList {n : Na
t} : forall {p : Nat}, p in primeFactorsList n -> Prime p
-/
theorem dvd_of_mem_primeFactorsList {n p : ℕ} (h : p ∈ n.primeFactorsList) : p ∣ n := by
  rcases n.eq_zero_or_pos with (rfl | hn)
  · exact dvd_zero p
  · rwa [← mem_primeFactorsList_iff_dvd hn.ne' (prime_of_mem_primeFactorsList h)]
/-
**Nat.mem_primeFactorsList** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：mem_primeFactorsList {n p} (hn : n != 0) : p in primeFactorsList n ↔ Prime
 p ∧ p ∣ n
参数：hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.prime_of_mem_primeFactorsList`：prime_of_mem_primeFactorsList {n : Na
t} : forall {p : Nat}, p in primeFactorsList n -> Prime p
· 使用定理 `Nat.dvd_of_mem_primeFactorsList`：dvd_of_mem_primeFactorsList {n p : Nat}
 (h : p in n.primeFactorsList) : p ∣ n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.mem_primeFactorsList_iff_dvd`：mem_primeFactorsList_iff_dvd {n p : Na
t} (hn : n != 0) (hp : Prime p) : p in primeFactorsList n ↔ p ∣ n where mp h
-/
theorem mem_primeFactorsList {n p} (hn : n ≠ 0) : p ∈ primeFactorsList n ↔ Prime p ∧ p ∣ n :=
  ⟨fun h => ⟨prime_of_mem_primeFactorsList h, dvd_of_mem_primeFactorsList h⟩, fun ⟨hprime, hdvd⟩ =>
    (mem_primeFactorsList_iff_dvd hn hprime).mpr hdvd⟩
/-
**Nat.mem_primeFactorsList'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {n p : ℕ}, p ∈ n.primeFactorsList ↔ Nat.Prime p ∧ p ∣ n ∧ n ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.primeFactorsList_zero`：primeFactorsList_zero : primeFactorsList 0 = 
[]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
@[simp] lemma mem_primeFactorsList' {n p} : p ∈ n.primeFactorsList ↔ p.Prime ∧ p ∣ n ∧ n ≠ 0 := by
  cases n <;> simp [mem_primeFactorsList, *]
/-
**Nat.le_of_mem_primeFactorsList** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：le_of_mem_primeFactorsList {n p : Nat} (h : p in n.primeFactorsList) : p <
= n
参数：h : p in n.primeFactorsList。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.primeFactorsList_zero`：primeFactorsList_zero : primeFactorsList 0 = 
[]
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
· 使用定理 `Nat.dvd_of_mem_primeFactorsList`：dvd_of_mem_primeFactorsList {n p : Nat}
 (h : p in n.primeFactorsList) : p ∣ n
-/
theorem le_of_mem_primeFactorsList {n p : ℕ} (h : p ∈ n.primeFactorsList) : p ≤ n := by
  rcases n.eq_zero_or_pos with (rfl | hn)
  · rw [primeFactorsList_zero] at h
    cases h
  · exact le_of_dvd hn (dvd_of_mem_primeFactorsList h)

/-- **Fundamental theorem of arithmetic** -/
/-
**Nat.primeFactorsList_unique** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：primeFactorsList_unique {n : Nat} {l : List Nat} (h₁ : prod l = n) (h₂ : f
orall p in l, Prime p) : l ~ primeFactorsList n
参数：h₁ : prod l = n；h₂ : forall p in l, Prime p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `perm_of_prod_eq_prod`：perm_of_prod_eq_prod : forall {l₁ l₂ : List M}, l₁
.prod = l₂.prod -> (forall p in l₁, Prime p) -> (forall p in l₂, Prime p) -> Per
m l₁ l₂ | …
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.prod_primeFactorsList`：prod_primeFactorsList : forall {n}, n != 0 ->
 List.prod (primeFactorsList n) = n | 0 => by simp | 1 => by simp | k + 2 => fun
 _ => let m
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用定理 `List.prod_eq_zero_iff`：∀ {M₀ : Type u_4} [inst : MonoidWithZero M₀] [Non
trivial M₀] [NoZeroDivisors M₀] {l : List M₀}, l.prod = 0 ↔ 0 ∈ l
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Nat.instIsDomain`：IsDomain ℕ
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Nat.prime_of_mem_primeFactorsList`：prime_of_mem_primeFactorsList {n : Na
t} : forall {p : Nat}, p in primeFactorsList n -> Prime p

--- 原说明 ---
**Fundamental theorem of arithmetic**
-/
theorem primeFactorsList_unique {n : ℕ} {l : List ℕ} (h₁ : prod l = n) (h₂ : ∀ p ∈ l, Prime p) :
    l ~ primeFactorsList n := by
  refine perm_of_prod_eq_prod ?_ ?_ ?_
  · rw [h₁]
    refine (prod_primeFactorsList ?_).symm
    rintro rfl
    rw [prod_eq_zero_iff] at h₁
    exact Prime.ne_zero (h₂ 0 h₁) rfl
  · simp_rw [← prime_iff]
    exact h₂
  · simp_rw [← prime_iff]
    exact fun p => prime_of_mem_primeFactorsList
/-
**Nat.Prime.primeFactorsList_pow** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：∀ {p : ℕ}, Nat.Prime p → ∀ (n : ℕ), (p ^ n).primeFactorsList = List.replic
ate n p
参数：n : ℕ；p ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.replicate_perm`：∀ {α : Type u_1} {n : ℕ} {a : α} {l : List α}, (Lis
t.replicate n a).Perm l ↔ List.replicate n a = l
· 使用定理 `Nat.primeFactorsList_unique`：primeFactorsList_unique {n : Nat} {l : List
 Nat} (h₁ : prod l = n) (h₂ : forall p in l, Prime p) : l ~ primeFactorsList n
· 使用定理 `List.prod_replicate`：prod_replicate (n : Nat) (a : M) : (replicate n a).
prod = a ^ n
· 使用定理 `List.eq_of_mem_replicate`：∀ {α : Type u_1} {a b : α} {n : ℕ}, b ∈ List.r
eplicate n a → b = a
-/
theorem Prime.primeFactorsList_pow {p : ℕ} (hp : p.Prime) (n : ℕ) :
    (p ^ n).primeFactorsList = List.replicate n p := by
  symm
  rw [← List.replicate_perm]
  apply Nat.primeFactorsList_unique (List.prod_replicate n p)
  intro q hq
  rwa [eq_of_mem_replicate hq]
/-
**Nat.eq_prime_pow_of_unique_prime_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：eq_prime_pow_of_unique_prime_dvd {n p : Nat} (hpos : n != 0) (h : forall {
d}, Nat.Prime d -> d ∣ n -> d = p) : n = p ^ n.primeFactorsList.length
参数：hpos : n != 0；h : forall {d}, Nat.Prime d -> d ∣ n -> d = p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.prod_primeFactorsList`：prod_primeFactorsList : forall {n}, n != 0 ->
 List.prod (primeFactorsList n) = n | 0 => by simp | 1 => by simp | k + 2 => fun
 _ => let m
· 使用定理 `List.prod_replicate`：prod_replicate (n : Nat) (a : M) : (replicate n a).
prod = a ^ n
· 使用定理 `List.eq_replicate_of_mem`：∀ {α : Type u_1} {a : α} {l : List α}, (∀ b ∈ 
l, b = a) → l = List.replicate l.length a
· 使用定理 `Nat.prime_of_mem_primeFactorsList`：prime_of_mem_primeFactorsList {n : Na
t} : forall {p : Nat}, p in primeFactorsList n -> Prime p
· 使用定理 `Nat.dvd_of_mem_primeFactorsList`：dvd_of_mem_primeFactorsList {n p : Nat}
 (h : p in n.primeFactorsList) : p ∣ n
-/
theorem eq_prime_pow_of_unique_prime_dvd {n p : ℕ} (hpos : n ≠ 0)
    (h : ∀ {d}, Nat.Prime d → d ∣ n → d = p) : n = p ^ n.primeFactorsList.length := by
  set k := n.primeFactorsList.length
  rw [← prod_primeFactorsList hpos, ← prod_replicate k p, eq_replicate_of_mem fun d hd =>
    h (prime_of_mem_primeFactorsList hd) (dvd_of_mem_primeFactorsList hd)]

/-- For positive `a` and `b`, the prime factors of `a * b` are the union of those of `a` and `b` -/
/-
**Nat.perm_primeFactorsList_mul** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：perm_primeFactorsList_mul {a b : Nat} (ha : a != 0) (hb : b != 0) : (a * b
).primeFactorsList ~ a.primeFactorsList ++ b.primeFactorsList
参数：ha : a != 0；hb : b != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Perm.symm`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → l₂.Perm 
l₁
· 使用定理 `Nat.primeFactorsList_unique`：primeFactorsList_unique {n : Nat} {l : List
 Nat} (h₁ : prod l = n) (h₂ : forall p in l, Prime p) : l ~ primeFactorsList n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.prod_append`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : One α] [Std.
LawfulLeftIdentity (fun x1 x2 => x1 * x2) 1]   [Std.Associative fun x1 x2 => x1 
* x2] …
· 使用定理 `Std.LawfulIdentity.toLawfulLeftIdentity`：∀ {α : Sort u} {op : α → α → α}
 {o : outParam α} [self : Std.LawfulIdentity op o], Std.LawfulLeftIdentity op o
· 使用定理 `Nat.instLawfulIdentityHMulOfNat`：Std.LawfulIdentity (fun x1 x2 => x1 * x
2) 1
· 使用定理 `Nat.instAssociativeHMul`：Std.Associative fun x1 x2 => x1 * x2
· 使用定理 `Nat.prod_primeFactorsList`：prod_primeFactorsList : forall {n}, n != 0 ->
 List.prod (primeFactorsList n) = n | 0 => by simp | 1 => by simp | k + 2 => fun
 _ => let m
· 使用定理 `List.mem_append`：∀ {α : Type u_1} {a : α} {s t : List α}, a ∈ s ++ t ↔ a
 ∈ s ∨ a ∈ t
· 使用定理 `Nat.prime_of_mem_primeFactorsList`：prime_of_mem_primeFactorsList {n : Na
t} : forall {p : Nat}, p in primeFactorsList n -> Prime p

--- 原说明 ---
For positive `a` and `b`, the prime factors of `a * b` are the union of those of
 `a` and `b`
-/
theorem perm_primeFactorsList_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (a * b).primeFactorsList ~ a.primeFactorsList ++ b.primeFactorsList := by
  refine (primeFactorsList_unique ?_ ?_).symm
  · rw [List.prod_append, prod_primeFactorsList ha, prod_primeFactorsList hb]
  · intro p hp
    rw [List.mem_append] at hp
    rcases hp with hp' | hp' <;> exact prime_of_mem_primeFactorsList hp'

/-- For coprime `a` and `b`, the prime factors of `a * b` are the union of those of `a` and `b` -/
/-
**Nat.perm_primeFactorsList_mul_of_coprime** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：perm_primeFactorsList_mul_of_coprime {a b : Nat} (hab : Coprime a b) : (a 
* b).primeFactorsList ~ a.primeFactorsList ++ b.primeFactorsList
参数：hab : Coprime a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.coprime_zero_left`：∀ (n : ℕ), Nat.Coprime 0 n ↔ n = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Nat.primeFactorsList_zero`：primeFactorsList_zero : primeFactorsList 0 = 
[]
· 使用定理 `Nat.primeFactorsList_one`：primeFactorsList_one : primeFactorsList 1 = []
· 使用定理 `List.append_nil`：∀ {α : Type u} (as : List α), as ++ [] = as
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.coprime_zero_right`：∀ (n : ℕ), n.Coprime 0 ↔ n = 1
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Nat.perm_primeFactorsList_mul`：perm_primeFactorsList_mul {a b : Nat} (ha
 : a != 0) (hb : b != 0) : (a * b).primeFactorsList ~ a.primeFactorsList ++ b.pr
imeFactorsList
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b

--- 原说明 ---
For coprime `a` and `b`, the prime factors of `a * b` are the union of those of 
`a` and `b`
-/
theorem perm_primeFactorsList_mul_of_coprime {a b : ℕ} (hab : Coprime a b) :
    (a * b).primeFactorsList ~ a.primeFactorsList ++ b.primeFactorsList := by
  rcases a.eq_zero_or_pos with (rfl | ha)
  · simp [(coprime_zero_left _).mp hab]
  rcases b.eq_zero_or_pos with (rfl | hb)
  · simp [(coprime_zero_right _).mp hab]
  exact perm_primeFactorsList_mul ha.ne' hb.ne'
/-
**Nat.primeFactorsList_sublist_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：primeFactorsList_sublist_right {n k : Nat} (h : k != 0) : n.primeFactorsLi
st <+ (n * k).primeFactorsList
参数：h : k != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.primeFactorsList_zero`：primeFactorsList_zero : primeFactorsList 0 = 
[]
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `List.sublist_of_subperm_of_pairwise`：sublist_of_subperm_of_pairwise {l₁ 
l₂ : List α} (hp : l₁ <+~ l₂) (hs₁ : l₁.Pairwise r) (hs₂ : l₂.Pairwise r) : l₁ <
+ l₂
· 使用定理 `Nat.instAntisymmLe`：Std.Antisymm fun x1 x2 => x1 ≤ x2
· 使用定理 `List.Perm.subperm_left`：∀ {α : Type u_1} {l l₁ l₂ : List α}, l₁.Perm l₂ 
→ (l.Subperm l₁ ↔ l.Subperm l₂)
· 使用定理 `Nat.perm_primeFactorsList_mul`：perm_primeFactorsList_mul {a b : Nat} (ha
 : a != 0) (hb : b != 0) : (a * b).primeFactorsList ~ a.primeFactorsList ++ b.pr
imeFactorsList
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
· 使用定理 `List.Sublist.subperm`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂ →
 l₁.Subperm l₂
· 使用定理 `List.sublist_append_left`：∀ {α : Type u_1} (l₁ l₂ : List α), l₁.Sublist 
(l₁ ++ l₂)
· 使用定理 `List.SortedLE.pairwise`：∀ {α : Type u_1} {l : List α} [inst : Preorder α
], l.SortedLE → List.Pairwise (fun x1 x2 => x1 ≤ x2) l
· 使用定理 `Nat.primeFactorsList_sorted`：primeFactorsList_sorted (n : Nat) : List.So
rtedLE (primeFactorsList n)
-/
theorem primeFactorsList_sublist_right {n k : ℕ} (h : k ≠ 0) :
    n.primeFactorsList <+ (n * k).primeFactorsList := by
  rcases n with - | hn
  · simp [zero_mul]
  apply sublist_of_subperm_of_pairwise _
    (primeFactorsList_sorted _).pairwise (primeFactorsList_sorted _).pairwise
  simp only [(perm_primeFactorsList_mul (Nat.succ_ne_zero _) h).subperm_left]
  exact (sublist_append_left _ _).subperm
/-
**Nat.primeFactorsList_sublist_of_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：primeFactorsList_sublist_of_dvd {n k : Nat} (h : n ∣ k) (h' : k != 0) : n.
primeFactorsList <+ k.primeFactorsList
参数：h : n ∣ k；h' : k != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.primeFactorsList_sublist_right`：primeFactorsList_sublist_right {n k 
: Nat} (h : k != 0) : n.primeFactorsList <+ (n * k).primeFactorsList
· 使用定理 `right_ne_zero_of_mul`：right_ne_zero_of_mul : a * b != 0 -> b != 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem primeFactorsList_sublist_of_dvd {n k : ℕ} (h : n ∣ k) (h' : k ≠ 0) :
    n.primeFactorsList <+ k.primeFactorsList := by
  obtain ⟨a, rfl⟩ := h
  exact primeFactorsList_sublist_right (right_ne_zero_of_mul h')
/-
**Nat.primeFactorsList_subset_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：primeFactorsList_subset_right {n k : Nat} (h : k != 0) : n.primeFactorsLis
t subseteq (n * k).primeFactorsList
参数：h : k != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Sublist.subset`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂ → 
l₁ ⊆ l₂
· 使用定理 `Nat.primeFactorsList_sublist_right`：primeFactorsList_sublist_right {n k 
: Nat} (h : k != 0) : n.primeFactorsList <+ (n * k).primeFactorsList
-/
theorem primeFactorsList_subset_right {n k : ℕ} (h : k ≠ 0) :
    n.primeFactorsList ⊆ (n * k).primeFactorsList :=
  (primeFactorsList_sublist_right h).subset
/-
**Nat.primeFactorsList_subset_of_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：primeFactorsList_subset_of_dvd {n k : Nat} (h : n ∣ k) (h' : k != 0) : n.p
rimeFactorsList subseteq k.primeFactorsList
参数：h : n ∣ k；h' : k != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Sublist.subset`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂ → 
l₁ ⊆ l₂
· 使用定理 `Nat.primeFactorsList_sublist_of_dvd`：primeFactorsList_sublist_of_dvd {n 
k : Nat} (h : n ∣ k) (h' : k != 0) : n.primeFactorsList <+ k.primeFactorsList
-/
theorem primeFactorsList_subset_of_dvd {n k : ℕ} (h : n ∣ k) (h' : k ≠ 0) :
    n.primeFactorsList ⊆ k.primeFactorsList :=
  (primeFactorsList_sublist_of_dvd h h').subset
/-
**Nat.dvd_of_primeFactorsList_subperm** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：dvd_of_primeFactorsList_subperm {a b : Nat} (ha : a != 0) (h : a.primeFact
orsList <+~ b.primeFactorsList) : a ∣ b
参数：ha : a != 0；h : a.primeFactorsList <+~ b.primeFactorsList。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `dvd_zero`：dvd_zero (a : α) : a ∣ 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_dvd`：one_dvd (a : α) : 1 ∣ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.prod_primeFactorsList`：prod_primeFactorsList : forall {n}, n != 0 ->
 List.prod (primeFactorsList n) = n | 0 => by simp | 1 => by simp | k + 2 => fun
 _ => let m
· 使用定理 `List.prod_append`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : One α] [Std.
LawfulLeftIdentity (fun x1 x2 => x1 * x2) 1]   [Std.Associative fun x1 x2 => x1 
* x2] …
· 使用定理 `Std.LawfulIdentity.toLawfulLeftIdentity`：∀ {α : Sort u} {op : α → α → α}
 {o : outParam α} [self : Std.LawfulIdentity op o], Std.LawfulLeftIdentity op o
· 使用定理 `Nat.instLawfulIdentityHMulOfNat`：Std.LawfulIdentity (fun x1 x2 => x1 * x
2) 1
· 使用定理 `Nat.instAssociativeHMul`：Std.Associative fun x1 x2 => x1 * x2
· 使用定理 `List.Perm.prod_eq`：∀ {M : Type u_4} [inst : CommMonoid M] {l₁ l₂ : List 
M}, l₁.Perm l₂ → l₁.prod = l₂.prod
· 使用定理 `List.subperm_append_diff_self_of_count_le`：∀ {α : Type u_1} [inst : BEq 
α] [LawfulBEq α] {l₁ l₂ : List α},   (∀ x ∈ l₁, List.count x l₁ ≤ List.count x l
₂) → (l₁ ++ l₂.diff l₁).Perm l₂
· 使用定理 `Nat.instLawfulBEq`：LawfulBEq ℕ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.subperm_ext_iff`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {l₁ 
l₂ : List α},   l₁.Subperm l₂ ↔ ∀ x ∈ l₁, List.count x l₁ ≤ List.count x l₂
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
theorem dvd_of_primeFactorsList_subperm {a b : ℕ} (ha : a ≠ 0)
    (h : a.primeFactorsList <+~ b.primeFactorsList) : a ∣ b := by
  rcases b.eq_zero_or_pos with (rfl | hb)
  · exact dvd_zero _
  rcases a with (_ | _ | a)
  · exact (ha rfl).elim
  · exact one_dvd _
  use (b.primeFactorsList.diff a.succ.succ.primeFactorsList).prod
  nth_rw 1 [← Nat.prod_primeFactorsList ha]
  rw [← List.prod_append,
    List.Perm.prod_eq <| List.subperm_append_diff_self_of_count_le <| List.subperm_ext_iff.mp h,
    Nat.prod_primeFactorsList hb.ne']
/-
**Nat.replicate_subperm_primeFactorsList_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：replicate_subperm_primeFactorsList_iff {a b n : Nat} (ha : Prime a) (hb : 
b != 0) : replicate n a <+~ primeFactorsList b ↔ a ^ n ∣ b
参数：ha : Prime a；hb : b != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用引理 `List.subperm_iff`：subperm_iff : l₁ <+~ l₂ ↔ exists l, l ~ l₂ ∧ l₁ <+ l
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.prod_primeFactorsList`：prod_primeFactorsList : forall {n}, n != 0 ->
 List.prod (primeFactorsList n) = n | 0 => by simp | 1 => by simp | k + 2 => fun
 _ => let m
· 使用定理 `List.Perm.prod_eq`：∀ {M : Type u_4} [inst : CommMonoid M] {l₁ l₂ : List 
M}, l₁.Perm l₂ → l₁.prod = l₂.prod
· 使用定理 `List.prod_replicate`：prod_replicate (n : Nat) (a : M) : (replicate n a).
prod = a ^ n
· 使用定理 `List.Sublist.prod_dvd_prod`：∀ {M : Type u_4} [inst : CommMonoid M] {l₁ l
₂ : List M}, l₁.Sublist l₂ → l₁.prod ∣ l₂.prod
· 使用定理 `Nat.pow_succ'`：∀ {m n : ℕ}, m ^ n.succ = m * m ^ n
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `List.replicate_succ`：∀ {α : Type u} {a : α} {n : ℕ}, List.replicate (n +
 1) a = a :: List.replicate n a
· 使用定理 `List.Perm.subperm_left`：∀ {α : Type u_1} {l l₁ l₂ : List α}, l₁.Perm l₂ 
→ (l.Subperm l₁ ↔ l.Subperm l₂)
· 使用定理 `Nat.perm_primeFactorsList_mul`：perm_primeFactorsList_mul {a b : Nat} (ha
 : a != 0) (hb : b != 0) : (a * b).primeFactorsList ~ a.primeFactorsList ++ b.pr
imeFactorsList
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `not_or`：∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q
· 使用定理 `Nat.mul_eq_zero`：∀ {m n : ℕ}, n * m = 0 ↔ n = 0 ∨ m = 0
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Nat.primeFactorsList_prime`：primeFactorsList_prime {p : Nat} (hp : Nat.P
rime p) : p.primeFactorsList = [p]
· 使用定理 `List.singleton_append`：∀ {α : Type u_1} {x : α} {l : List α}, [x] ++ l =
 x :: l
· 使用定理 `List.subperm_cons`：∀ {α : Type u_1} (a : α) {l₁ l₂ : List α}, (a :: l₁).
Subperm (a :: l₂) ↔ l₁.Subperm l₂
· 使用定理 `dvd_mul_right`：dvd_mul_right (a b : α) : a ∣ a * b
-/
theorem replicate_subperm_primeFactorsList_iff {a b n : ℕ} (ha : Prime a) (hb : b ≠ 0) :
    replicate n a <+~ primeFactorsList b ↔ a ^ n ∣ b := by
  induction n generalizing b with
  | zero => simp
  | succ n ih =>
    constructor
    · rw [List.subperm_iff]
      rintro ⟨u, hu1, hu2⟩
      rw [← Nat.prod_primeFactorsList hb, ← hu1.prod_eq, ← prod_replicate]
      exact hu2.prod_dvd_prod
    · rintro ⟨c, rfl⟩
      rw [Ne, pow_succ', mul_assoc, mul_eq_zero, _root_.not_or] at hb
      rw [pow_succ', mul_assoc, replicate_succ,
        (Nat.perm_primeFactorsList_mul hb.1 hb.2).subperm_left, primeFactorsList_prime ha,
        singleton_append, subperm_cons, ih hb.2]
      exact dvd_mul_right _ _

end

/-
**Nat.mem_primeFactorsList_mul** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：mem_primeFactorsList_mul {a b : Nat} (ha : a != 0) (hb : b != 0) {p : Nat}
 : p in (a * b).primeFactorsList ↔ p in a.primeFactorsList ∨ p in b.primeFactors
List
参数：ha : a != 0；hb : b != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.mem_primeFactorsList`：mem_primeFactorsList {n p} (hn : n != 0) : p i
n primeFactorsList n ↔ Prime p ∧ p ∣ n
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Nat.instIsDomain`：IsDomain ℕ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `and_or_left`：∀ {a b c : Prop}, a ∧ (b ∨ c) ↔ a ∧ b ∨ a ∧ c
· 使用定理 `Nat.Prime.dvd_mul`：∀ {p m n : ℕ}, Nat.Prime p → (p ∣ m * n ↔ p ∣ m ∨ p ∣
 n)
-/
theorem mem_primeFactorsList_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) {p : ℕ} :
    p ∈ (a * b).primeFactorsList ↔ p ∈ a.primeFactorsList ∨ p ∈ b.primeFactorsList := by
  rw [mem_primeFactorsList (mul_ne_zero ha hb), mem_primeFactorsList ha, mem_primeFactorsList hb,
    ← and_or_left]
  simpa only [and_congr_right_iff] using Prime.dvd_mul

/-- The sets of factors of coprime `a` and `b` are disjoint -/
/-
**Nat.coprime_primeFactorsList_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：coprime_primeFactorsList_disjoint {a b : Nat} (hab : a.Coprime b) : List.D
isjoint a.primeFactorsList b.primeFactorsList
参数：hab : a.Coprime b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.not_prime_one`：¬Nat.Prime 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.eq_one_of_dvd_coprimes`：eq_one_of_dvd_coprimes {a b k : Nat} (h_ab_c
oprime : Coprime a b) (hka : k ∣ a) (hkb : k ∣ b) : k = 1
· 使用定理 `Nat.dvd_of_mem_primeFactorsList`：dvd_of_mem_primeFactorsList {n p : Nat}
 (h : p in n.primeFactorsList) : p ∣ n
· 使用定理 `Nat.prime_of_mem_primeFactorsList`：prime_of_mem_primeFactorsList {n : Na
t} : forall {p : Nat}, p in primeFactorsList n -> Prime p

--- 原说明 ---
The sets of factors of coprime `a` and `b` are disjoint
-/
theorem coprime_primeFactorsList_disjoint {a b : ℕ} (hab : a.Coprime b) :
    List.Disjoint a.primeFactorsList b.primeFactorsList := by
  intro q hqa hqb
  apply not_prime_one
  rw [← eq_one_of_dvd_coprimes hab (dvd_of_mem_primeFactorsList hqa)
    (dvd_of_mem_primeFactorsList hqb)]
  exact prime_of_mem_primeFactorsList hqa
/-
**Nat.mem_primeFactorsList_mul_of_coprime** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：mem_primeFactorsList_mul_of_coprime {a b : Nat} (hab : Coprime a b) (p : N
at) : p in (a * b).primeFactorsList ↔ p in a.primeFactorsList union b.primeFacto
rsList
参数：hab : Coprime a b；p : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.coprime_zero_left`：∀ (n : ℕ), Nat.Coprime 0 n ↔ n = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Nat.primeFactorsList_zero`：primeFactorsList_zero : primeFactorsList 0 = 
[]
· 使用定理 `Nat.primeFactorsList_one`：primeFactorsList_one : primeFactorsList 1 = []
· 使用定理 `List.nil_union`：∀ {α : Type u_1} [inst : BEq α] (l : List α), [] ∪ l = l
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.coprime_zero_right`：∀ (n : ℕ), n.Coprime 0 ↔ n = 1
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Nat.mem_primeFactorsList_mul`：mem_primeFactorsList_mul {a b : Nat} (ha :
 a != 0) (hb : b != 0) {p : Nat} : p in (a * b).primeFactorsList ↔ p in a.primeF
actorsList ∨ p in …
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `List.mem_union_iff`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {x : α
} {l₁ l₂ : List α}, x ∈ l₁ ∪ l₂ ↔ x ∈ l₁ ∨ x ∈ l₂
· 使用定理 `Nat.instLawfulBEq`：LawfulBEq ℕ
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_primeFactorsList_mul_of_coprime {a b : ℕ} (hab : Coprime a b) (p : ℕ) :
    p ∈ (a * b).primeFactorsList ↔ p ∈ a.primeFactorsList ∪ b.primeFactorsList := by
  rcases a.eq_zero_or_pos with (rfl | ha)
  · simp [(coprime_zero_left _).mp hab]
  rcases b.eq_zero_or_pos with (rfl | hb)
  · simp [(coprime_zero_right _).mp hab]
  rw [mem_primeFactorsList_mul ha.ne' hb.ne', List.mem_union_iff]

open List

/-- If `p` is a prime factor of `a` then `p` is also a prime factor of `a * b` for any `b > 0` -/
/-
**Nat.mem_primeFactorsList_mul_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：mem_primeFactorsList_mul_left {p a b : Nat} (hpa : p in a.primeFactorsList
) (hb : b != 0) : p in (a * b).primeFactorsList
参数：hpa : p in a.primeFactorsList；hb : b != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.primeFactorsList_zero`：primeFactorsList_zero : primeFactorsList 0 = 
[]
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.mem_primeFactorsList_mul`：mem_primeFactorsList_mul {a b : Nat} (ha :
 a != 0) (hb : b != 0) {p : Nat} : p in (a * b).primeFactorsList ↔ p in a.primeF
actorsList ∨ p in …

--- 原说明 ---
If `p` is a prime factor of `a` then `p` is also a prime factor of `a * b` for a
ny `b > 0`
-/
theorem mem_primeFactorsList_mul_left {p a b : ℕ} (hpa : p ∈ a.primeFactorsList) (hb : b ≠ 0) :
    p ∈ (a * b).primeFactorsList := by
  rcases eq_or_ne a 0 with (rfl | ha)
  · simp at hpa
  apply (mem_primeFactorsList_mul ha hb).2 (Or.inl hpa)

/-- If `p` is a prime factor of `b` then `p` is also a prime factor of `a * b` for any `a > 0` -/
/-
**Nat.mem_primeFactorsList_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：mem_primeFactorsList_mul_right {p a b : Nat} (hpb : p in b.primeFactorsLis
t) (ha : a != 0) : p in (a * b).primeFactorsList
参数：hpb : p in b.primeFactorsList；ha : a != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Nat.mem_primeFactorsList_mul_left`：mem_primeFactorsList_mul_left {p a b 
: Nat} (hpa : p in a.primeFactorsList) (hb : b != 0) : p in (a * b).primeFactors
List

--- 原说明 ---
If `p` is a prime factor of `b` then `p` is also a prime factor of `a * b` for a
ny `a > 0`
-/
theorem mem_primeFactorsList_mul_right {p a b : ℕ} (hpb : p ∈ b.primeFactorsList) (ha : a ≠ 0) :
    p ∈ (a * b).primeFactorsList := by
  rw [mul_comm]
  exact mem_primeFactorsList_mul_left hpb ha
/-
**Nat.eq_two_pow_or_exists_odd_prime_and_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：eq_two_pow_or_exists_odd_prime_and_dvd (n : Nat) : (exists k : Nat, n = 2 
^ k) ∨ exists p, Nat.Prime p ∧ p ∣ n ∧ Odd p
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Nat.prime_three`：prime_three : Prime 3
· 使用定理 `dvd_zero`：dvd_zero (a : α) : a ∣ 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_right`：∀ {a b : Prop}, a ∨ b ↔ ¬b → a
· 使用定理 `Nat.eq_prime_pow_of_unique_prime_dvd`：eq_prime_pow_of_unique_prime_dvd {
n p : Nat} (hpos : n != 0) (h : forall {d}, Nat.Prime d -> d ∣ n -> d = p) : n =
 p ^ n.primeFactorsList.le…
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `Nat.Prime.eq_two_or_odd'`：∀ {p : ℕ}, Nat.Prime p → p = 2 ∨ Odd p
-/
theorem eq_two_pow_or_exists_odd_prime_and_dvd (n : ℕ) :
    (∃ k : ℕ, n = 2 ^ k) ∨ ∃ p, Nat.Prime p ∧ p ∣ n ∧ Odd p :=
  (eq_or_ne n 0).elim (fun hn => Or.inr ⟨3, prime_three, hn.symm ▸ dvd_zero 3, ⟨1, rfl⟩⟩) fun hn =>
    or_iff_not_imp_right.mpr fun H =>
      ⟨n.primeFactorsList.length,
        eq_prime_pow_of_unique_prime_dvd hn fun {_} hprime hdvd =>
          hprime.eq_two_or_odd'.resolve_right fun hodd => H ⟨_, hprime, hdvd, hodd⟩⟩
/-
**Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt** 是 Mathlib 中的一个定理，位于命名空间 `
Nat`。
形式化陈述：four_dvd_or_exists_odd_prime_and_dvd_of_two_lt {n : Nat} (n2 : 2 < n) : 4 
∣ n ∨ exists p, Prime p ∧ p ∣ n ∧ Odd p
参数：n2 : 2 < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_two_pow_or_exists_odd_prime_and_dvd`：eq_two_pow_or_exists_odd_pri
me_and_dvd (n : Nat) : (exists k : Nat, n = 2 ^ k) ∨ exists p, Nat.Prime p ∧ p ∣
 n ∧ Odd p
· 使用定理 `of_decide_eq_false`：∀ {p : Prop} [inst : Decidable p], decide p = false 
→ ¬p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
theorem four_dvd_or_exists_odd_prime_and_dvd_of_two_lt {n : ℕ} (n2 : 2 < n) :
    4 ∣ n ∨ ∃ p, Prime p ∧ p ∣ n ∧ Odd p := by
  obtain ⟨_ | _ | k, rfl⟩ | ⟨p, hp, hdvd, hodd⟩ := n.eq_two_pow_or_exists_odd_prime_and_dvd
  · contradiction
  · contradiction
  · simp [Nat.pow_succ, mul_assoc]
  · exact Or.inr ⟨p, hp, hdvd, hodd⟩

end Nat

