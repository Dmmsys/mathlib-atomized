/-
Copyright (c) 2021 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Ralf Stephan
-/
module

public import Mathlib.Data.Nat.Prime.Nth
public import Mathlib.Data.Nat.Totient
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# The Prime Counting Function

In this file we define the prime counting function: the function on natural numbers that returns
the number of primes less than or equal to its input.

## Main Results

The main definitions for this file are

- `Nat.primeCounting`: The prime counting function π
- `Nat.primeCounting'`: π(n - 1)
- `Nat.primesBelow`: The finset of primes less than n
  (this was previously in `Mathlib.NumberTheory.SmoothNumbers`)
- `Nat.primesLE`: The finset of primes less than or equal to n

We then prove that these are monotone in `Nat.monotone_primeCounting` and
`Nat.monotone_primeCounting'`. The last main theorem `Nat.primeCounting'_add_le` is an upper
bound on `π'` which arises by observing that all numbers greater than `k` and not coprime to `k`
are not prime, and so only at most `φ(k)/k` fraction of the numbers from `k` to `n` are prime.

## Notation

With `open scoped Nat.Prime`, we use the standard notation `π` to represent the prime counting
function (and `π'` to represent the reindexed version).

-/

@[expose] public section


namespace Nat

open Finset

/-- A variant of the traditional prime counting function which gives the number of primes
*strictly* less than the input. More convenient for avoiding off-by-one errors.

With `open scoped Nat.Prime`, this has notation `π'`. -/
/-
**Nat.primeCounting'** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：primeCounting' : Nat -> Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A variant of the traditional prime counting function which gives the number of p
rimes
*strictly* less than the input. More convenient for avoiding off-by-one errors.

With `open scoped Nat.Prime`, this has notation `π'`.
-/
def primeCounting' : ℕ → ℕ :=
  Nat.count Prime

/-- The prime counting function: Returns the number of primes less than or equal to the input.

With `open scoped Nat.Prime`, this has notation `π`. -/
/-
**Nat.primeCounting** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：primeCounting (n : Nat) : Nat
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The prime counting function: Returns the number of primes less than or equal to 
the input.

With `open scoped Nat.Prime`, this has notation `π`.
-/
def primeCounting (n : ℕ) : ℕ :=
  primeCounting' (n + 1)

@[inherit_doc] scoped[Nat.Prime] notation "π" => Nat.primeCounting

@[inherit_doc] scoped[Nat.Prime] notation "π'" => Nat.primeCounting'

open scoped Nat.Prime
/-
**Nat.primeCounting_eq_primeCounting'_succ** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (n : ℕ), n.primeCounting = (n + 1).primeCounting'
参数：n : ℕ；n + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem primeCounting_eq_primeCounting'_succ (n : ℕ) : π n = π' (n + 1) := rfl

@[simp]
/-
**Nat.primeCounting_sub_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：primeCounting_sub_one (n : Nat) : π (n - 1) = π' n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem primeCounting_sub_one (n : ℕ) : π (n - 1) = π' n := by
  cases n <;> rfl
/-
**Nat.monotone_primeCounting'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：monotone_primeCounting' : Monotone primeCounting'
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.count_monotone`：count_monotone : Monotone (count p)
-/
theorem monotone_primeCounting' : Monotone primeCounting' :=
  count_monotone Prime
/-
**Nat.monotone_primeCounting** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：monotone_primeCounting : Monotone primeCounting
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preorder
 α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Monot
one…
· 使用定理 `Nat.monotone_primeCounting'`：monotone_primeCounting' : Monotone primeCou
nting'
· 使用定理 `Monotone.add_const`：∀ {α : Type u_1} {β : Type u_2} [inst : Add α] [inst
_1 : Preorder α] [inst_2 : Preorder β] {f : β → α} [AddRightMono α],   Monotone 
f → ∀ (a…
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `monotone_id`：monotone_id [Preorder α] : Monotone (id : α -> α)
-/
theorem monotone_primeCounting : Monotone primeCounting :=
  monotone_primeCounting'.comp (monotone_id.add_const _)

@[simp]
/-
**Nat.primeCounting'_nth_eq** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ (n : ℕ), (Nat.nth Nat.Prime n).primeCounting' = n
参数：n : ℕ；Nat.nth Nat.Prime n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.count_nth_of_infinite`：count_nth_of_infinite (hp : (Set.ofPred p).In
finite) (n : Nat) : count p (nth p n) = n
· 使用定理 `Nat.infinite_setOfPred_prime`：infinite_setOfPred_prime : { p | Prime p }
.Infinite
-/
theorem primeCounting'_nth_eq (n : ℕ) : π' (nth Prime n) = n :=
  count_nth_of_infinite infinite_setOfPred_prime _

/-- The `n`th prime is greater or equal to `n + 2`. -/
/-
**Nat.add_two_le_nth_prime** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：add_two_le_nth_prime (n : Nat) : n + 2 <= nth Prime n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StrictMono.add_le_nat`：StrictMono.add_le_nat {f : Nat -> Nat} (hf : Stri
ctMono f) (m n : Nat) : m + f n <= f (m + n)
· 使用定理 `Nat.nth_strictMono`：nth_strictMono (hf : (Set.ofPred p).Infinite) : Stri
ctMono (nth p)
· 使用定理 `Nat.infinite_setOfPred_prime`：infinite_setOfPred_prime : { p | Prime p }
.Infinite
· 使用定理 `Nat.nth_prime_zero_eq_two`：nth_prime_zero_eq_two : nth Prime 0 = 2

--- 原说明 ---
The `n`th prime is greater or equal to `n + 2`.
-/
theorem add_two_le_nth_prime (n : ℕ) : n + 2 ≤ nth Prime n :=
  nth_prime_zero_eq_two ▸ (nth_strictMono infinite_setOfPred_prime).add_le_nat n 0
/-
**Nat.surjective_primeCounting'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：surjective_primeCounting' : Function.Surjective π'
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.surjective_count_of_infinite_setOfPred`：surjective_count_of_infinite
_setOfPred (h : {n | p n}.Infinite) : Function.Surjective (Nat.count p)
· 使用定理 `Nat.infinite_setOfPred_prime`：infinite_setOfPred_prime : { p | Prime p }
.Infinite
-/
theorem surjective_primeCounting' : Function.Surjective π' :=
  Nat.surjective_count_of_infinite_setOfPred infinite_setOfPred_prime
/-
**Nat.surjective_primeCounting** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：surjective_primeCounting : Function.Surjective π
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.primeCounting_sub_one`：primeCounting_sub_one (n : Nat) : π (n - 1) =
 π' n
· 使用定理 `Nat.surjective_primeCounting'`：surjective_primeCounting' : Function.Surj
ective π'
· 使用定理 `Function.Surjective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u
_3} {f : α → β} {g : γ → α},   Function.Surjective (f ∘ g) → Function.Surjective
 f
-/
theorem surjective_primeCounting : Function.Surjective π := by
  suffices Function.Surjective (π ∘ fun n => n - 1) from this.of_comp
  convert! surjective_primeCounting'
  ext
  exact primeCounting_sub_one _

open Filter
/-
**Nat.tendsto_primeCounting'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：tendsto_primeCounting' : Tendsto π' atTop atTop
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendsto_atTop_atTop_of_monotone'`：tendsto_atTop_atTop_of_monotone
' [Preorder ι] [LinearOrder α] {u : ι -> α} (h : Monotone u) (H : ¬BddAbove (ran
ge u)) : Tendsto u atTop atTo…
· 使用定理 `Nat.monotone_primeCounting'`：monotone_primeCounting' : Monotone primeCou
nting'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.range_eq_univ`：range_eq_univ : range f = univ ↔ Surjective f
· 使用定理 `Nat.surjective_primeCounting'`：surjective_primeCounting' : Function.Surj
ective π'
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem tendsto_primeCounting' : Tendsto π' atTop atTop := by
  apply tendsto_atTop_atTop_of_monotone' monotone_primeCounting'
  simp [Set.range_eq_univ.mpr surjective_primeCounting']
/-
**Nat.tendsto_primeCounting** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：tendsto_primeCounting : Tendsto π atTop atTop
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_add_atTop_iff_nat`：tendsto_add_atTop_iff_nat {f : Nat -> 
α} {l : Filter α} (k : Nat) : Tendsto (fun n => f (n + k)) atTop l ↔ Tendsto f a
tTop l
· 使用定理 `Nat.tendsto_primeCounting'`：tendsto_primeCounting' : Tendsto π' atTop at
Top
-/
theorem tendsto_primeCounting : Tendsto π atTop atTop :=
  (tendsto_add_atTop_iff_nat 1).mpr tendsto_primeCounting'

@[simp]
/-
**Nat.prime_nth_prime** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：prime_nth_prime (n : Nat) : Prime (nth Prime n)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.nth_mem_of_infinite`：nth_mem_of_infinite (hf : (Set.ofPred p).Infini
te) (n : Nat) : p (nth p n)
· 使用定理 `Nat.infinite_setOfPred_prime`：infinite_setOfPred_prime : { p | Prime p }
.Infinite
-/
theorem prime_nth_prime (n : ℕ) : Prime (nth Prime n) :=
  nth_mem_of_infinite infinite_setOfPred_prime _

@[simp]
/-
**Nat.primeCounting'_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {n : ℕ}, n.primeCounting' = 0 ↔ n ≤ 2
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.primeCounting'.eq_1`：Nat.primeCounting' = Nat.count Nat.Prime
· 使用定理 `Nat.count_eq_zero`：∀ {p : ℕ → Prop} [inst : DecidablePred p], (∃ n, p n)
 → ∀ {n : ℕ}, Nat.count p n = 0 ↔ n ≤ Nat.nth p 0
· 使用定理 `Nat.prime_two`：prime_two : Prime 2
· 使用定理 `Nat.nth_prime_zero_eq_two`：nth_prime_zero_eq_two : nth Prime 0 = 2
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma primeCounting'_eq_zero_iff {n : ℕ} : n.primeCounting' = 0 ↔ n ≤ 2 := by
  rw [primeCounting', Nat.count_eq_zero ⟨_, Nat.prime_two⟩, Nat.nth_prime_zero_eq_two]

@[simp]
/-
**Nat.primeCounting_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：primeCounting_eq_zero_iff {n : Nat} : n.primeCounting = 0 ↔ n <= 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.Simproc.add_le_le`：∀ (a : ℕ) {b c : ℕ}, b ≤ c → (a + b ≤ c) = (a ≤ c
 - b)
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma primeCounting_eq_zero_iff {n : ℕ} : n.primeCounting = 0 ↔ n ≤ 1 := by
  simp [primeCounting, -Order.add_one_le_iff]

@[simp]
/-
**Nat.primeCounting_zero** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：primeCounting_zero : primeCounting 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Nat.primeCounting_eq_zero_iff`：primeCounting_eq_zero_iff {n : Nat} : n.p
rimeCounting = 0 ↔ n <= 1
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
-/
lemma primeCounting_zero : primeCounting 0 = 0 :=
  primeCounting_eq_zero_iff.mpr zero_le_one

@[simp]
/-
**Nat.primeCounting_one** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：primeCounting_one : primeCounting 1 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Nat.primeCounting_eq_zero_iff`：primeCounting_eq_zero_iff {n : Nat} : n.p
rimeCounting = 0 ↔ n <= 1
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma primeCounting_one : primeCounting 1 = 0 :=
  primeCounting_eq_zero_iff.mpr le_rfl

section PrimeSets

variable {p k n : ℕ}

/-- `primesBelow n` is the set of primes less than `n` as a `Finset`. -/
/-
**Nat.primesBelow** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：primesBelow (n : Nat) : Finset Nat
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`primesBelow n` is the set of primes less than `n` as a `Finset`.
-/
def primesBelow (n : ℕ) : Finset ℕ := {p ∈ Finset.range n | p.Prime}

/-- `primesLE n` is the set of primes less than or equal to `n` as a `Finset`. -/
/-
**Nat.primesLE** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：primesLE (n : Nat) : Finset Nat
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`primesLE n` is the set of primes less than or equal to `n` as a `Finset`.
-/
def primesLE (n : ℕ) : Finset ℕ := primesBelow (n + 1)
/-
**Nat.primesBelow_eq_filter_range** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：primesBelow_eq_filter_range (n : Nat) : primesBelow n = filter Nat.Prime (
range n)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma primesBelow_eq_filter_range (n : ℕ) : primesBelow n = filter Nat.Prime (range n) := rfl
/-
**Nat.primesLE_eq_filter_range** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：primesLE_eq_filter_range (n : Nat) : primesLE n = filter Nat.Prime (range 
(n + 1))
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma primesLE_eq_filter_range (n : ℕ) : primesLE n = filter Nat.Prime (range (n + 1)) := rfl

@[simp]
/-
**Nat.primesBelow_zero** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：primesBelow_zero : primesBelow 0 = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
lemma primesBelow_zero : primesBelow 0 = ∅ := by
  decide

@[simp]
/-
**Nat.primesBelow_one** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：primesBelow_one : primesBelow 1 = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
lemma primesBelow_one : primesBelow 1 = ∅ := by
  decide

@[simp]
/-
**Nat.primesBelow_two** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：primesBelow_two : primesBelow 2 = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
lemma primesBelow_two : primesBelow 2 = ∅ := by
  decide

@[simp]
/-
**Nat.primesLE_zero** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：primesLE_zero : primesLE 0 = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.primesBelow_one`：primesBelow_one : primesBelow 1 = ∅
-/
lemma primesLE_zero : primesLE 0 = ∅ := primesBelow_one

@[simp]
/-
**Nat.primesLE_one** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：primesLE_one : primesLE 1 = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.primesBelow_two`：primesBelow_two : primesBelow 2 = ∅
-/
lemma primesLE_one : primesLE 1 = ∅ := primesBelow_two
/-
**Nat.primesBelow_eq_primesLE_sub_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：primesBelow_eq_primesLE_sub_one (n : Nat) : primesBelow n = primesLE (n - 
1)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.primesBelow_zero`：primesBelow_zero : primesBelow 0 = ∅
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `Nat.primesBelow_one`：primesBelow_one : primesBelow 1 = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem primesBelow_eq_primesLE_sub_one (n : ℕ) : primesBelow n = primesLE (n - 1) := by
  cases n <;> simp [primesLE]
/-
**Nat.mem_primesBelow** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：mem_primesBelow : n in primesBelow k ↔ n < k ∧ n.Prime
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
lemma mem_primesBelow :
    n ∈ primesBelow k ↔ n < k ∧ n.Prime := by simp [primesBelow]
/-
**Nat.mem_primesLE** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：mem_primesLE : p in primesLE n ↔ p <= n ∧ p.Prime
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
lemma mem_primesLE : p ∈ primesLE n ↔ p ≤ n ∧ p.Prime := by
  simp [primesLE, mem_primesBelow]
/-
**Nat.prime_of_mem_primesBelow** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：prime_of_mem_primesBelow (h : p in n.primesBelow) : p.Prime
参数：h : p in n.primesBelow。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
-/
lemma prime_of_mem_primesBelow (h : p ∈ n.primesBelow) : p.Prime :=
  (Finset.mem_filter.mp h).2
/-
**Nat.prime_of_mem_primesLE** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：prime_of_mem_primesLE (hp : p in primesLE n) : p.Prime
参数：hp : p in primesLE n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.prime_of_mem_primesBelow`：prime_of_mem_primesBelow (h : p in n.prime
sBelow) : p.Prime
-/
lemma prime_of_mem_primesLE (hp : p ∈ primesLE n) : p.Prime :=
  prime_of_mem_primesBelow hp
/-
**Nat.lt_of_mem_primesBelow** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：lt_of_mem_primesBelow (h : p in n.primesBelow) : p < n
参数：h : p in n.primesBelow。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n
· 使用定理 `Finset.mem_of_mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : Decida
blePred p] {s : Finset α}, ∀ x ∈ Finset.filter p s, x ∈ s
-/
lemma lt_of_mem_primesBelow (h : p ∈ n.primesBelow) : p < n :=
  Finset.mem_range.mp <| Finset.mem_of_mem_filter p h
/-
**Nat.le_of_mem_primesLE** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：le_of_mem_primesLE (hp : p in primesLE n) : p <= n
参数：hp : p in primesLE n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Nat.mem_primesLE`：mem_primesLE : p in primesLE n ↔ p <= n ∧ p.Prime
-/
lemma le_of_mem_primesLE (hp : p ∈ primesLE n) : p ≤ n := (mem_primesLE.mp hp).1
/-
**Nat.one_lt_of_mem_primesBelow** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：one_lt_of_mem_primesBelow (hp : p in primesBelow n) : 1 < p
参数：hp : p in primesBelow n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用引理 `Nat.prime_of_mem_primesBelow`：prime_of_mem_primesBelow (h : p in n.prime
sBelow) : p.Prime
-/
lemma one_lt_of_mem_primesBelow (hp : p ∈ primesBelow n) : 1 < p :=
  (prime_of_mem_primesBelow hp).one_lt
/-
**Nat.one_lt_of_mem_primesLE** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：one_lt_of_mem_primesLE (hp : p in primesLE n) : 1 < p
参数：hp : p in primesLE n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.one_lt_of_mem_primesBelow`：one_lt_of_mem_primesBelow (hp : p in prim
esBelow n) : 1 < p
-/
lemma one_lt_of_mem_primesLE (hp : p ∈ primesLE n) : 1 < p :=
  one_lt_of_mem_primesBelow hp
/-
**Nat.two_le_of_mem_primesBelow** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：two_le_of_mem_primesBelow (hp : p in primesBelow n) : 2 <= p
参数：hp : p in primesBelow n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Prime.two_le`：∀ {p : ℕ}, Nat.Prime p → 2 ≤ p
· 使用引理 `Nat.prime_of_mem_primesBelow`：prime_of_mem_primesBelow (h : p in n.prime
sBelow) : p.Prime
-/
lemma two_le_of_mem_primesBelow (hp : p ∈ primesBelow n) : 2 ≤ p :=
  (prime_of_mem_primesBelow hp).two_le
/-
**Nat.two_le_of_mem_primesLE** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：two_le_of_mem_primesLE (hp : p in primesLE n) : 2 <= p
参数：hp : p in primesLE n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.two_le_of_mem_primesBelow`：two_le_of_mem_primesBelow (hp : p in prim
esBelow n) : 2 <= p
-/
lemma two_le_of_mem_primesLE (hp : p ∈ primesLE n) : 2 ≤ p :=
  two_le_of_mem_primesBelow hp
/-
**Nat.primesBelow_eq_filter_Ico_zero** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：primesBelow_eq_filter_Ico_zero (n : Nat) : primesBelow n = filter Nat.Prim
e (Ico 0 n)
参数：n : Nat。
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.filter.congr_simp`：∀ {α : Type u_1} (p p_1 : α → Prop),   p = p_1
 →     ∀ {inst : DecidablePred p} [inst_1 : DecidablePred p_1] (s s_1 : Finset α
),       s = s…
· 使用定理 `Nat.Ico_zero_eq_range`：Ico_zero_eq_range : Ico 0 a = range a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma primesBelow_eq_filter_Ico_zero (n : ℕ) : primesBelow n = filter Nat.Prime (Ico 0 n) := by
  ext p
  simp [primesBelow_eq_filter_range]
/-
**Nat.primesLE_eq_filter_Icc_zero** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：primesLE_eq_filter_Icc_zero (n : Nat) : primesLE n = filter Nat.Prime (Icc
 0 n)
参数：n : Nat。
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma primesLE_eq_filter_Icc_zero (n : ℕ) : primesLE n = filter Nat.Prime (Icc 0 n) := by
  ext p
  simp [primesLE_eq_filter_range]
/-
**Nat.primesBelow_eq_filter_Ioo_zero** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：primesBelow_eq_filter_Ioo_zero (n : Nat) : primesBelow n = filter Nat.Prim
e (Ioo 0 n)
参数：n : Nat。
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma primesBelow_eq_filter_Ioo_zero (n : ℕ) : primesBelow n = filter Nat.Prime (Ioo 0 n) := by
  ext p
  simp +contextual [primesBelow_eq_filter_range, Nat.Prime.pos]
/-
**Nat.primesLE_eq_filter_Ioc_zero** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：primesLE_eq_filter_Ioc_zero (n : Nat) : primesLE n = filter Nat.Prime (Ioc
 0 n)
参数：n : Nat。
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma primesLE_eq_filter_Ioc_zero (n : ℕ) : primesLE n = filter Nat.Prime (Ioc 0 n) := by
  ext p
  simp +contextual [primesLE_eq_filter_range, Nat.Prime.pos]
/-
**Nat.primesBelow_eq_filter_Ico_one** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：primesBelow_eq_filter_Ico_one (n : Nat) : primesBelow n = filter Nat.Prime
 (Ico 1 n)
参数：n : Nat。
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma primesBelow_eq_filter_Ico_one (n : ℕ) : primesBelow n = filter Nat.Prime (Ico 1 n) := by
  ext p
  simp +contextual [primesBelow_eq_filter_range, Nat.Prime.one_le]
/-
**Nat.primesLE_eq_filter_Icc_one** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：primesLE_eq_filter_Icc_one (n : Nat) : primesLE n = filter Nat.Prime (Icc 
1 n)
参数：n : Nat。
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma primesLE_eq_filter_Icc_one (n : ℕ) : primesLE n = filter Nat.Prime (Icc 1 n) := by
  ext p
  simp +contextual [primesLE_eq_filter_range, Nat.Prime.one_le]
/-
**Nat.primesBelow_eq_filter_Ioo_one** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：primesBelow_eq_filter_Ioo_one (n : Nat) : primesBelow n = filter Nat.Prime
 (Ioo 1 n)
参数：n : Nat。
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma primesBelow_eq_filter_Ioo_one (n : ℕ) : primesBelow n = filter Nat.Prime (Ioo 1 n) := by
  ext p
  simp +contextual [primesBelow_eq_filter_range, Nat.Prime.one_lt]
/-
**Nat.primesLE_eq_filter_Ioc_one** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：primesLE_eq_filter_Ioc_one (n : Nat) : primesLE n = filter Nat.Prime (Ioc 
1 n)
参数：n : Nat。
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma primesLE_eq_filter_Ioc_one (n : ℕ) : primesLE n = filter Nat.Prime (Ioc 1 n) := by
  ext p
  simp +contextual [primesLE_eq_filter_range, Nat.Prime.one_lt]
/-
**Nat.primesBelow_eq_filter_Ico_two** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：primesBelow_eq_filter_Ico_two (n : Nat) : primesBelow n = filter Nat.Prime
 (Ico 2 n)
参数：n : Nat。
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma primesBelow_eq_filter_Ico_two (n : ℕ) : primesBelow n = filter Nat.Prime (Ico 2 n) := by
  ext p
  simp +contextual [primesBelow_eq_filter_range, Nat.Prime.two_le]
/-
**Nat.primesLE_eq_filter_Icc_two** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：primesLE_eq_filter_Icc_two (n : Nat) : primesLE n = filter Nat.Prime (Icc 
2 n)
参数：n : Nat。
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma primesLE_eq_filter_Icc_two (n : ℕ) : primesLE n = filter Nat.Prime (Icc 2 n) := by
  ext p
  simp +contextual [primesLE_eq_filter_range, Nat.Prime.two_le]
/-
**Nat.primesBelow_mono** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：primesBelow_mono : Monotone primesBelow
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
lemma primesBelow_mono : Monotone primesBelow := by
  intros n m _ p
  simp [mem_primesBelow]; grind
/-
**Nat.primesLE_mono** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：primesLE_mono : Monotone primesLE
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
lemma primesLE_mono : Monotone primesLE := by
  intros n m _ p
  simp [mem_primesLE]; grind
/-
**Nat.primesBelow_succ** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：primesBelow_succ (n : Nat) : primesBelow (n + 1) = if n.Prime then insert 
n (primesBelow n) else primesBelow n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.primesBelow.eq_1`：∀ (n : ℕ), n.primesBelow = {p ∈ Finset.range n | N
at.Prime p}
· 使用定理 `Finset.range_add_one`：range_add_one : range (n + 1) = insert n (range n)
· 使用定理 `Finset.filter_insert`：filter_insert (a : α) (s : Finset α) : (insert a s
).filter p = if p a then insert a (s.filter p) else s.filter p
-/
lemma primesBelow_succ (n : ℕ) :
    primesBelow (n + 1) = if n.Prime then insert n (primesBelow n) else primesBelow n := by
  rw [primesBelow, primesBelow, Finset.range_add_one, Finset.filter_insert]
/-
**Nat.primesLE_succ** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：primesLE_succ (n : Nat) : primesLE (n + 1) = if (n + 1).Prime then insert 
(n + 1) (primesLE n) else primesLE n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.primesBelow_succ`：primesBelow_succ (n : Nat) : primesBelow (n + 1) =
 if n.Prime then insert n (primesBelow n) else primesBelow n
-/
lemma primesLE_succ (n : ℕ) :
    primesLE (n + 1) = if (n + 1).Prime then insert (n + 1) (primesLE n) else primesLE n :=
  primesBelow_succ (n + 1)
/-
**Nat.notMem_primesBelow** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：notMem_primesBelow (n : Nat) : n ∉ primesBelow n
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.false`：∀ {α : Type u_2} [inst : Preorder α] {a : α}, a < a → False
· 使用引理 `Nat.lt_of_mem_primesBelow`：lt_of_mem_primesBelow (h : p in n.primesBelow
) : p < n
-/
lemma notMem_primesBelow (n : ℕ) : n ∉ primesBelow n :=
  fun hn ↦ (lt_of_mem_primesBelow hn).false
/-
**Nat.notMem_primesLE** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：notMem_primesLE (n : Nat) : n + 1 ∉ primesLE n
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.notMem_primesBelow`：notMem_primesBelow (n : Nat) : n ∉ primesBelow n
-/
lemma notMem_primesLE (n : ℕ) : n + 1 ∉ primesLE n :=
  notMem_primesBelow (n + 1)

end PrimeSets

/-- The cardinality of the finset `primesBelow n` equals the counting function
`primeCounting'` at `n`. -/
/-
**Nat.primesBelow_card_eq_primeCounting'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：primesBelow_card_eq_primeCounting' (n : Nat) : #n.primesBelow = π' n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.count_eq_card_filter_range`：count_eq_card_filter_range (n : Nat) : c
ount p n = #{x in range n | p x}

--- 原说明 ---
The cardinality of the finset `primesBelow n` equals the counting function
`primeCounting'` at `n`.
-/
theorem primesBelow_card_eq_primeCounting' (n : ℕ) : #n.primesBelow = π' n := by
  simp only [primesBelow, primeCounting']
  exact (count_eq_card_filter_range Prime n).symm

/-- The cardinality of the finset `primesLE n` equals the counting function
`primeCounting` at `n`. -/
@[simp]
/-
**Nat.primesLE_card_eq_primeCounting** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：primesLE_card_eq_primeCounting (n : Nat) : #(primesLE n) = π n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.primesBelow_card_eq_primeCounting'`：primesBelow_card_eq_primeCountin
g' (n : Nat) : #n.primesBelow = π' n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The cardinality of the finset `primesLE n` equals the counting function
`primeCounting` at `n`.
-/
theorem primesLE_card_eq_primeCounting (n : ℕ) : #(primesLE n) = π n := by
  simp only [primesLE, primeCounting, primesBelow_card_eq_primeCounting']

/-- A linear upper bound on the size of the `primeCounting'` function -/
/-
**Nat.primeCounting'_add_le** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {a k : ℕ}, a ≠ 0 → a < k → ∀ (n : ℕ), (k + n).primeCounting' ≤ k.primeCo
unting' + a.totient * (n / a + 1)
参数：n : ℕ；k + n；n / a + 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.primeCounting'.eq_1`：Nat.primeCounting' = Nat.count Nat.Prime
· 使用定理 `Nat.count_eq_card_filter_range`：count_eq_card_filter_range (n : Nat) : c
ount p n = #{x in range n | p x}
· 使用定理 `Finset.range_eq_Ico`：∀ (a : ℕ), Finset.range a = Finset.Ico 0 a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.Ico_union_Ico_eq_Ico`：Ico_union_Ico_eq_Ico {a b c : α} (hab : a <
= b) (hbc : b <= c) : Ico a b union Ico b c = Ico a c
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `le_self_add`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ a + b
· 使用定理 `Finset.filter_union`：filter_union (s₁ s₂ : Finset α) : (s₁ union s₂).fil
ter p = s₁.filter p union s₂.filter p
· 使用定理 `Finset.card_union_le`：card_union_le (s t : Finset α) : #(s union t) <= #
s + #t
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用定理 `Finset.monotone_filter_right`：∀ {α : Type u_1} (s : Finset α) ⦃p q : α →
 Prop⦄ [inst : DecidablePred p] [inst_1 : DecidablePred q],   (∀ a ∈ s, p a → q 
a) → Finset.filter…
· 使用定理 `Nat.coprime_comm`：∀ {n m : ℕ}, n.Coprime m ↔ m.Coprime n
· 使用定理 `Nat.coprime_of_lt_prime`：coprime_of_lt_prime {n p} (ne_zero : n != 0) (h
lt : n < p) (pp : Prime p) : Coprime p n
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_Ico`：mem_Ico : x in Ico a b ↔ a <= x ∧ x < b
· 使用定理 `add_le_add_iff_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [Ad
dLeftMono α] [AddLeftReflectLE α] (a : α) {b c : α},   a + b ≤ a + c ↔ b ≤ c
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `Nat.Ico_filter_coprime_le`：Ico_filter_coprime_le {a : Nat} (k n : Nat) (
a_ne_zero : a != 0) : #{x in Ico k (k + n) | a.Coprime x} <= totient a * (n / a 
+ 1)

--- 原说明 ---
A linear upper bound on the size of the `primeCounting'` function
-/
theorem primeCounting'_add_le {a k : ℕ} (h0 : a ≠ 0) (h1 : a < k) (n : ℕ) :
    π' (k + n) ≤ π' k + Nat.totient a * (n / a + 1) :=
  calc
    π' (k + n) ≤ #{p ∈ range k | p.Prime} + #{p ∈ Ico k (k + n) | p.Prime} := by
      rw [primeCounting', count_eq_card_filter_range, range_eq_Ico, range_eq_Ico, ←
        Ico_union_Ico_eq_Ico (zero_le k) le_self_add, filter_union]
      apply card_union_le
    _ ≤ π' k + #{p ∈ Ico k (k + n) | p.Prime} := by
      rw [primeCounting', count_eq_card_filter_range]
    _ ≤ π' k + #{b ∈ Ico k (k + n) | a.Coprime b} := by
      gcongr with p hp
      rw [coprime_comm]
      exact coprime_of_lt_prime h0 <| h1.trans_le (mem_Ico.1 hp).1
    _ ≤ π' k + totient a * (n / a + 1) := by
      rw [add_le_add_iff_left]
      exact Ico_filter_coprime_le k n h0
/-
**Nat.primeCounting_add_le** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：primeCounting_add_le {a k : Nat} (h0 : a != 0) (h1 : a <= k) (n : Nat) : π
 (k + n) <= π k + totient a * (n / a + 1)
参数：h0 : a != 0；h1 : a <= k；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.primeCounting_eq_primeCounting'_succ`：∀ (n : ℕ), n.primeCounting = (
n + 1).primeCounting'
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Nat.primeCounting'_add_le`：∀ {a k : ℕ}, a ≠ 0 → a < k → ∀ (n : ℕ), (k + 
n).primeCounting' ≤ k.primeCounting' + a.totient * (n / a + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Order.lt_add_one_iff`：lt_add_one_iff [NoMaxOrder α] : x < y + 1 ↔ x <= y
-/
theorem primeCounting_add_le {a k : ℕ} (h0 : a ≠ 0) (h1 : a ≤ k) (n : ℕ) :
    π (k + n) ≤ π k + totient a * (n / a + 1) := by
  rw [primeCounting_eq_primeCounting'_succ]
  convert! primeCounting'_add_le h0 (Order.lt_add_one_iff.mpr h1) n using 2
  omega

end Nat

