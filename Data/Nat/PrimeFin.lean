/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module

public import Mathlib.Data.Countable.Defs
public import Mathlib.Data.Nat.Factors
public import Mathlib.Data.Nat.Prime.Infinite
public import Mathlib.Data.Set.Finite.Lattice

/-!
# Prime numbers

This file contains some results about prime numbers which depend on finiteness of sets.
-/

@[expose] public section

open Finset

namespace Nat
variable {a b k m n p : ℕ}

/-- A version of `Nat.exists_infinite_primes` using the `Set.Infinite` predicate. -/
/-
**Nat.infinite_setOfPred_prime** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：infinite_setOfPred_prime : { p | Prime p }.Infinite
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.infinite_of_not_bddAbove`：infinite_of_not_bddAbove : ¬BddAbove s -> 
s.Infinite
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Nat.not_bddAbove_setOfPred_prime`：not_bddAbove_setOfPred_prime : ¬BddAbo
ve { p | Prime p }

--- 原说明 ---
A version of `Nat.exists_infinite_primes` using the `Set.Infinite` predicate.
-/
theorem infinite_setOfPred_prime : { p | Prime p }.Infinite :=
  Set.infinite_of_not_bddAbove not_bddAbove_setOfPred_prime

@[deprecated (since := "2026-07-09")] alias infinite_setOf_prime := infinite_setOfPred_prime
/-
**Nat.Primes.infinite** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Primes`。
形式化陈述：Infinite Nat.Primes
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Infinite.to_subtype`：∀ {α : Type u} {s : Set α}, s.Infinite → Infini
te ↑s
· 使用定理 `Nat.infinite_setOfPred_prime`：infinite_setOfPred_prime : { p | Prime p }
.Infinite
-/
instance Primes.infinite : Infinite Primes := infinite_setOfPred_prime.to_subtype
/-
**Nat.Primes.countable** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Primes`。
形式化陈述：Countable Nat.Primes
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Primes.coe_nat_injective`：coe_nat_injective : Function.Injective ((↑
) : Nat.Primes -> Nat)
-/
instance Primes.countable : Countable Primes := ⟨⟨coeNat.coe, coe_nat_injective⟩⟩

/-- The prime factors of a natural number as a finset. -/
/-
**Nat.primeFactors** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：primeFactors (n : Nat) : Finset Nat
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The prime factors of a natural number as a finset.
-/
def primeFactors (n : ℕ) : Finset ℕ := n.primeFactorsList.toFinset
/-
**Nat.toFinset_factors** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (n : ℕ), n.primeFactorsList.toFinset = n.primeFactors
参数：n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toFinset_factors (n : ℕ) : n.primeFactorsList.toFinset = n.primeFactors := rfl
/-
**Nat.mem_primeFactors** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {n p : ℕ}, p ∈ n.primeFactors ↔ Nat.Prime p ∧ p ∣ n ∧ n ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp, grind =] lemma mem_primeFactors : p ∈ n.primeFactors ↔ p.Prime ∧ p ∣ n ∧ n ≠ 0 := by
  simp_rw [← toFinset_factors, List.mem_toFinset, mem_primeFactorsList']
/-
**Nat.mem_primeFactors_of_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：mem_primeFactors_of_ne_zero (hn : n != 0) : p in n.primeFactors ↔ p.Prime 
∧ p ∣ n
参数：hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_primeFactors_of_ne_zero (hn : n ≠ 0) : p ∈ n.primeFactors ↔ p.Prime ∧ p ∣ n := by
  simp [hn]
/-
**Nat.Prime.mem_primeFactors** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：∀ {n p : ℕ}, Nat.Prime p → p ∣ n → n ≠ 0 → p ∈ n.primeFactors
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.mem_primeFactors`：∀ {n p : ℕ}, p ∈ n.primeFactors ↔ Nat.Prime p ∧ p 
∣ n ∧ n ≠ 0
-/
lemma Prime.mem_primeFactors (hp : p.Prime) (hdvd : p ∣ n) (hn : n ≠ 0) : p ∈ n.primeFactors :=
  Nat.mem_primeFactors.mpr ⟨hp, hdvd, hn⟩

/-- A version of `Nat.Prime.mem_primeFactors` using `[NeZero n]` instead of an explicit argument. -/
/-
**Nat.Prime.mem_primeFactors'** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：∀ {n p : ℕ}, Nat.Prime p → p ∣ n → ∀ [NeZero n], p ∈ n.primeFactors
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Prime.mem_primeFactors`：∀ {n p : ℕ}, Nat.Prime p → p ∣ n → n ≠ 0 → p
 ∈ n.primeFactors
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0

--- 原说明 ---
A version of `Nat.Prime.mem_primeFactors` using `[NeZero n]` instead of an expli
cit argument.
-/
lemma Prime.mem_primeFactors' (hp : p.Prime) (hdvd : p ∣ n) [NeZero n] : p ∈ n.primeFactors :=
  hp.mem_primeFactors hdvd (NeZero.ne n)
/-
**Nat.Prime.mem_primeFactors_self** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：∀ {p : ℕ}, Nat.Prime p → p ∈ p.primeFactors
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Prime.mem_primeFactors`：∀ {n p : ℕ}, Nat.Prime p → p ∣ n → n ≠ 0 → p
 ∈ n.primeFactors
· 使用定理 `Nat.dvd_refl`：∀ (a : ℕ), a ∣ a
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
-/
lemma Prime.mem_primeFactors_self (hp : p.Prime) : p ∈ p.primeFactors :=
  hp.mem_primeFactors p.dvd_refl hp.ne_zero
/-
**Nat.primeFactors_mono** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：primeFactors_mono (hmn : m ∣ n) (hn : n != 0) : primeFactors m subseteq pr
imeFactors n
参数：hmn : m ∣ n；hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
-/
lemma primeFactors_mono (hmn : m ∣ n) (hn : n ≠ 0) : primeFactors m ⊆ primeFactors n := by
  simp only [subset_iff, mem_primeFactors, and_imp]
  exact fun p hp hpm _ ↦ ⟨hp, hpm.trans hmn, hn⟩
/-
**Nat.mem_primeFactors_iff_mem_primeFactorsList** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：mem_primeFactors_iff_mem_primeFactorsList : p in n.primeFactors ↔ p in n.p
rimeFactorsList
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_primeFactors_iff_mem_primeFactorsList : p ∈ n.primeFactors ↔ p ∈ n.primeFactorsList := by
  simp only [primeFactors, List.mem_toFinset]
/-
**Nat.prime_of_mem_primeFactors** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：prime_of_mem_primeFactors (hp : p in n.primeFactors) : p.Prime
参数：hp : p in n.primeFactors。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.mem_primeFactors`：∀ {n p : ℕ}, p ∈ n.primeFactors ↔ Nat.Prime p ∧ p 
∣ n ∧ n ≠ 0
-/
lemma prime_of_mem_primeFactors (hp : p ∈ n.primeFactors) : p.Prime := (mem_primeFactors.1 hp).1
/-
**Nat.dvd_of_mem_primeFactors** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：dvd_of_mem_primeFactors (hp : p in n.primeFactors) : p ∣ n
参数：hp : p in n.primeFactors。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.mem_primeFactors`：∀ {n p : ℕ}, p ∈ n.primeFactors ↔ Nat.Prime p ∧ p 
∣ n ∧ n ≠ 0
-/
lemma dvd_of_mem_primeFactors (hp : p ∈ n.primeFactors) : p ∣ n := (mem_primeFactors.1 hp).2.1
/-
**Nat.pos_of_mem_primeFactors** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：pos_of_mem_primeFactors (hp : p in n.primeFactors) : 0 < p
参数：hp : p in n.primeFactors。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Prime.pos`：∀ {p : ℕ}, Nat.Prime p → 0 < p
· 使用引理 `Nat.prime_of_mem_primeFactors`：prime_of_mem_primeFactors (hp : p in n.pr
imeFactors) : p.Prime
-/
lemma pos_of_mem_primeFactors (hp : p ∈ n.primeFactors) : 0 < p :=
  (prime_of_mem_primeFactors hp).pos
/-
**Nat.le_of_mem_primeFactors** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：le_of_mem_primeFactors (h : p in n.primeFactors) : p <= n
参数：h : p in n.primeFactors。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.mem_primeFactors`：∀ {n p : ℕ}, p ∈ n.primeFactors ↔ Nat.Prime p ∧ p 
∣ n ∧ n ≠ 0
· 使用引理 `Nat.dvd_of_mem_primeFactors`：dvd_of_mem_primeFactors (hp : p in n.primeF
actors) : p ∣ n
-/
lemma le_of_mem_primeFactors (h : p ∈ n.primeFactors) : p ≤ n :=
  le_of_dvd (mem_primeFactors.1 h).2.2.bot_lt <| dvd_of_mem_primeFactors h
/-
**Nat.primeFactors_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：Nat.primeFactors 0 = ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma primeFactors_zero : primeFactors 0 = ∅ := by
  ext
  simp
/-
**Nat.primeFactors_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：Nat.primeFactors 1 = ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `Nat.Prime.ne_one`：∀ {p : ℕ}, Nat.Prime p → p ≠ 1
-/
@[simp] lemma primeFactors_one : primeFactors 1 = ∅ := by
  ext
  simpa using Prime.ne_one
/-
**Nat.primeFactors_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {n : ℕ}, n.primeFactors = ∅ ↔ n = 0 ∨ n = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Nat.exists_prime_and_dvd`：exists_prime_and_dvd {n : Nat} (hn : n != 1) :
 exists p, Prime p ∧ p ∣ n
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.mem_primeFactors`：∀ {n p : ℕ}, p ∈ n.primeFactors ↔ Nat.Prime p ∧ p 
∣ n ∧ n ≠ 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.primeFactors_zero`：Nat.primeFactors 0 = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.primeFactors_one`：Nat.primeFactors 1 = ∅
-/
@[simp] lemma primeFactors_eq_empty : n.primeFactors = ∅ ↔ n = 0 ∨ n = 1 := by
  constructor
  · contrapose!
    rintro hn
    obtain ⟨p, hp, hpn⟩ := exists_prime_and_dvd hn.2
    exact ⟨_, mem_primeFactors.2 ⟨hp, hpn, hn.1⟩⟩
  · rintro (rfl | rfl) <;> simp

@[simp]
/-
**Nat.nonempty_primeFactors** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：nonempty_primeFactors {n : Nat} : n.primeFactors.Nonempty ↔ 1 < n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₁`：contrapose_iff₁ {p q : Prop} 
: (¬ p ↔ ¬ q) -> (p ↔ q)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.primeFactors_eq_empty`：∀ {n : ℕ}, n.primeFactors = ∅ ↔ n = 0 ∨ n = 1
· 使用定理 `Nat.le_one_iff_eq_zero_or_eq_one`：∀ {n : ℕ}, n ≤ 1 ↔ n = 0 ∨ n = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma nonempty_primeFactors {n : ℕ} : n.primeFactors.Nonempty ↔ 1 < n := by
  contrapose!
  rw [primeFactors_eq_empty, Nat.le_one_iff_eq_zero_or_eq_one]
/-
**Nat.Prime.primeFactors** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：∀ {p : ℕ}, Nat.Prime p → p.primeFactors = {p}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.primeFactorsList_prime`：primeFactorsList_prime {p : Nat} (hp : Nat.P
rime p) : p.primeFactorsList = [p]
· 使用定理 `List.toFinset_cons`：toFinset_cons : toFinset (a :: l) = insert a (toFins
et l)
· 使用定理 `LawfulSingleton.insert_empty_eq`：∀ {α : Type u} {β : Type v} {inst : Emp
tyCollection β} {inst_1 : Insert α β} {inst_2 : Singleton α β}   [self : LawfulS
ingleton α β] (x : α)…
· 使用定理 `Finset.instLawfulSingleton`：∀ {α : Type u_1} [inst : DecidableEq α], Law
fulSingleton α (Finset α)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] protected lemma Prime.primeFactors (hp : p.Prime) : p.primeFactors = {p} := by
  simp [Nat.primeFactors, primeFactorsList_prime hp]
/-
**Nat.primeFactors_mul** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：primeFactors_mul (ha : a != 0) (hb : b != 0) : (a * b).primeFactors = a.pr
imeFactors union b.primeFactors
参数：ha : a != 0；hb : b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.mem_primeFactorsList_mul`：mem_primeFactorsList_mul {a b : Nat} (ha :
 a != 0) (hb : b != 0) {p : Nat} : p in (a * b).primeFactorsList ↔ p in a.primeF
actorsList ∨ p in …
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma primeFactors_mul (ha : a ≠ 0) (hb : b ≠ 0) :
    (a * b).primeFactors = a.primeFactors ∪ b.primeFactors := by
  ext; simp only [Finset.mem_union, mem_primeFactors_iff_mem_primeFactorsList,
    mem_primeFactorsList_mul ha hb]
/-
**Nat.Coprime.primeFactors_mul** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Coprime`。
形式化陈述：∀ {a b : ℕ}, a.Coprime b → (a * b).primeFactors = a.primeFactors ∪ b.prime
Factors
参数：a * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.toFinset.ext`：∀ {α : Type u_1} [inst : DecidableEq α] {l l' : List 
α}, (∀ (x : α), x ∈ l ↔ x ∈ l') → l.toFinset = l'.toFinset
· 使用定理 `Nat.mem_primeFactorsList_mul_of_coprime`：mem_primeFactorsList_mul_of_cop
rime {a b : Nat} (hab : Coprime a b) (p : Nat) : p in (a * b).primeFactorsList ↔
 p in a.primeFactorsList unio…
· 使用定理 `List.toFinset_union`：toFinset_union (l l' : List α) : (l union l').toFin
set = l.toFinset union l'.toFinset
-/
lemma Coprime.primeFactors_mul {a b : ℕ} (hab : Coprime a b) :
    (a * b).primeFactors = a.primeFactors ∪ b.primeFactors :=
  (List.toFinset.ext <| mem_primeFactorsList_mul_of_coprime hab).trans <| List.toFinset_union _ _
/-
**Nat.primeFactors_gcd** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：primeFactors_gcd (ha : a != 0) (hb : b != 0) : (a.gcd b).primeFactors = a.
primeFactors inter b.primeFactors
参数：ha : a != 0；hb : b != 0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma primeFactors_gcd (ha : a ≠ 0) (hb : b ≠ 0) :
    (a.gcd b).primeFactors = a.primeFactors ∩ b.primeFactors := by
  grind [dvd_gcd_iff]
/-
**Nat.disjoint_primeFactors** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {a b : ℕ}, a ≠ 0 → b ≠ 0 → (Disjoint a.primeFactors b.primeFactors ↔ a.C
oprime b)
参数：Disjoint a.primeFactors b.primeFactors ↔ a.Coprime b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma disjoint_primeFactors (ha : a ≠ 0) (hb : b ≠ 0) :
    Disjoint a.primeFactors b.primeFactors ↔ Coprime a b := by
  simp [disjoint_iff_inter_eq_empty, coprime_iff_gcd_eq_one, ← primeFactors_gcd,
    ha, hb]
/-
**Nat.Coprime.disjoint_primeFactors** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Coprime`。
形式化陈述：∀ {a b : ℕ}, a.Coprime b → Disjoint a.primeFactors b.primeFactors
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.disjoint_toFinset_iff_disjoint`：disjoint_toFinset_iff_disjoint : _r
oot_.Disjoint l.toFinset l'.toFinset ↔ l.Disjoint l'
· 使用定理 `Nat.coprime_primeFactorsList_disjoint`：coprime_primeFactorsList_disjoint
 {a b : Nat} (hab : a.Coprime b) : List.Disjoint a.primeFactorsList b.primeFacto
rsList
-/
protected lemma Coprime.disjoint_primeFactors (hab : Coprime a b) :
    Disjoint a.primeFactors b.primeFactors :=
  List.disjoint_toFinset_iff_disjoint.2 <| coprime_primeFactorsList_disjoint hab
/-
**Nat.primeFactors_pow_succ** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：primeFactors_pow_succ (n k : Nat) : (n ^ (k + 1)).primeFactors = n.primeFa
ctors
参数：n k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Nat.primeFactors_zero`：Nat.primeFactors 0 = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Nat.pow_succ'`：∀ {m n : ℕ}, m ^ n.succ = m * m ^ n
· 使用引理 `Nat.primeFactors_mul`：primeFactors_mul (ha : a != 0) (hb : b != 0) : (a 
* b).primeFactors = a.primeFactors union b.primeFactors
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Nat.instIsDomain`：IsDomain ℕ
· 使用定理 `Finset.union_idempotent`：union_idempotent (s : Finset α) : s union s = s
-/
lemma primeFactors_pow_succ (n k : ℕ) : (n ^ (k + 1)).primeFactors = n.primeFactors := by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', primeFactors_mul hn (pow_ne_zero _ hn), ih, Finset.union_idempotent]
/-
**Nat.primeFactors_pow** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：primeFactors_pow (n : Nat) (hk : k != 0) : (n ^ k).primeFactors = n.primeF
actors
参数：n : Nat；hk : k != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nat.primeFactors_pow_succ`：primeFactors_pow_succ (n k : Nat) : (n ^ (k +
 1)).primeFactors = n.primeFactors
-/
lemma primeFactors_pow (n : ℕ) (hk : k ≠ 0) : (n ^ k).primeFactors = n.primeFactors := by
  cases k
  · simp at hk
  rw [primeFactors_pow_succ]

/-- The only prime divisor of positive prime power `p^k` is `p` itself -/
/-
**Nat.primeFactors_prime_pow** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：primeFactors_prime_pow (hk : k != 0) (hp : Prime p) : (p ^ k).primeFactors
 = {p}
参数：hk : k != 0；hp : Prime p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.primeFactors_pow`：primeFactors_pow (n : Nat) (hk : k != 0) : (n ^ k)
.primeFactors = n.primeFactors
· 使用定理 `Nat.Prime.primeFactors`：∀ {p : ℕ}, Nat.Prime p → p.primeFactors = {p}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The only prime divisor of positive prime power `p^k` is `p` itself
-/
lemma primeFactors_prime_pow (hk : k ≠ 0) (hp : Prime p) :
    (p ^ k).primeFactors = {p} := by simp [primeFactors_pow p hk, hp]

end Nat

