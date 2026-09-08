/-
Copyright (c) 2023 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll, Ralf Stephan
-/
module

public import Mathlib.Data.Nat.Factorization.Defs
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.NumberTheory.PrimeCounting

/-!
# Smooth numbers

For `s : Finset ℕ` we define the set `Nat.factoredNumbers s` of "`s`-factored numbers"
consisting of the positive natural numbers all of whose prime factors are in `s`, and
we provide some API for this.

We then define the set `Nat.smoothNumbers n` consisting of the positive natural numbers all of
whose prime factors are strictly less than `n`. This is the special case `s = Finset.range n`
of the set of `s`-factored numbers.

The main definition `Nat.equivProdNatSmoothNumbers` establishes the bijection between
`ℕ × (smoothNumbers p)` and `smoothNumbers (p+1)` given by sending `(e, n)` to `p^e * n`.
Here `p` is a prime number. It is obtained from the more general bijection between
`ℕ × (factoredNumbers s)` and `factoredNumbers (s ∪ {p})`; see `Nat.equivProdNatFactoredNumbers`.

Additionally, we define `Nat.smoothNumbersUpTo N n` as the `Finset` of `n`-smooth numbers
up to and including `N`, and similarly `Nat.roughNumbersUpTo` for its complement in `{1, ..., N}`,
and we provide some API, in particular bounds for their cardinalities; see
`Nat.smoothNumbersUpTo_card_le` and `Nat.roughNumbersUpTo_card_le`.
-/

@[expose] public section

open scoped Finset
namespace Nat

/-!
### `s`-factored numbers
-/

/-- `factoredNumbers s`, for a finite set `s` of natural numbers, is the set of positive natural
numbers all of whose prime factors are in `s`. -/
/-
**Nat.factoredNumbers** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：factoredNumbers (s : Finset Nat) : Set Nat
参数：s : Finset Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`factoredNumbers s`, for a finite set `s` of natural numbers, is the set of posi
tive natural
numbers all of whose prime factors are in `s`.
-/
def factoredNumbers (s : Finset ℕ) : Set ℕ := {m | m ≠ 0 ∧ ∀ p ∈ primeFactorsList m, p ∈ s}
/-
**Nat.mem_factoredNumbers** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：mem_factoredNumbers {s : Finset Nat} {m : Nat} : m in factoredNumbers s ↔ 
m != 0 ∧ forall p in primeFactorsList m, p in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_factoredNumbers {s : Finset ℕ} {m : ℕ} :
    m ∈ factoredNumbers s ↔ m ≠ 0 ∧ ∀ p ∈ primeFactorsList m, p ∈ s :=
  Iff.rfl

/-- Membership in `Nat.factoredNumbers n` is decidable. -/
/-
**Nat.** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Membership in `Nat.factoredNumbers n` is decidable.
-/
instance (s : Finset ℕ) : DecidablePred (· ∈ factoredNumbers s) :=
  inferInstanceAs <| DecidablePred fun x ↦ x ∈ {m | m ≠ 0 ∧ ∀ p ∈ primeFactorsList m, p ∈ s}

/-- A number that divides an `s`-factored number is itself `s`-factored. -/
/-
**Nat.mem_factoredNumbers_of_dvd** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：mem_factoredNumbers_of_dvd {s : Finset Nat} {m k : Nat} (h : m in factored
Numbers s) (h' : k ∣ m) : k in factoredNumbers s
参数：h : m in factoredNumbers s；h' : k ∣ m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_zero_of_dvd_ne_zero`：ne_zero_of_dvd_ne_zero {p q : α} (h₁ : q != 0) (
h₂ : p ∣ q) : p != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.mem_primeFactorsList`：mem_primeFactorsList {n p} (hn : n != 0) : p i
n primeFactorsList n ↔ Prime p ∧ p ∣ n
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
A number that divides an `s`-factored number is itself `s`-factored.
-/
lemma mem_factoredNumbers_of_dvd {s : Finset ℕ} {m k : ℕ} (h : m ∈ factoredNumbers s)
    (h' : k ∣ m) :
    k ∈ factoredNumbers s := by
  obtain ⟨h₁, h₂⟩ := h
  have hk := ne_zero_of_dvd_ne_zero h₁ h'
  refine ⟨hk, fun p hp ↦ h₂ p ?_⟩
  rw [mem_primeFactorsList <| by assumption] at hp ⊢
  exact ⟨hp.1, hp.2.trans h'⟩

/-- `m` is `s`-factored if and only if `m` is nonzero and all prime divisors `≤ m` of `m`
are in `s`. -/
/-
**Nat.mem_factoredNumbers_iff_forall_le** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：mem_factoredNumbers_iff_forall_le {s : Finset Nat} {m : Nat} : m in factor
edNumbers s ↔ m != 0 ∧ forall p <= m, p.Prime -> p ∣ m -> p in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n

--- 原说明 ---
`m` is `s`-factored if and only if `m` is nonzero and all prime divisors `≤ m` o
f `m`
are in `s`.
-/
lemma mem_factoredNumbers_iff_forall_le {s : Finset ℕ} {m : ℕ} :
    m ∈ factoredNumbers s ↔ m ≠ 0 ∧ ∀ p ≤ m, p.Prime → p ∣ m → p ∈ s := by
  simp_rw [mem_factoredNumbers, mem_primeFactorsList']
  exact ⟨fun ⟨H₀, H₁⟩ ↦ ⟨H₀, fun p _ hp₂ hp₃ ↦ H₁ p ⟨hp₂, hp₃, H₀⟩⟩,
    fun ⟨H₀, H₁⟩ ↦
      ⟨H₀, fun p ⟨hp₁, hp₂, hp₃⟩ ↦ H₁ p (le_of_dvd (Nat.pos_of_ne_zero hp₃) hp₂) hp₁ hp₂⟩⟩

/-- `m` is `s`-factored if and only if all prime divisors of `m` are in `s`. -/
/-
**Nat.mem_factoredNumbers'** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：mem_factoredNumbers' {s : Finset Nat} {m : Nat} : m in factoredNumbers s ↔
 forall p, p.Prime -> p ∣ m -> p in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.exists_infinite_primes`：exists_infinite_primes (n : Nat) : exists p,
 n <= p ∧ Prime p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.mem_factoredNumbers_iff_forall_le`：mem_factoredNumbers_iff_forall_le
 {s : Finset Nat} {m : Nat} : m in factoredNumbers s ↔ m != 0 ∧ forall p <= m, p
.Prime -> p ∣ m -> p in s
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
· 使用定理 `dvd_zero`：dvd_zero (a : α) : a ∣ 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `lt_one_add`：lt_one_add [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddRightStrictMono α] (a : α) : a < 1 + a
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
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

--- 原说明 ---
`m` is `s`-factored if and only if all prime divisors of `m` are in `s`.
-/
lemma mem_factoredNumbers' {s : Finset ℕ} {m : ℕ} :
    m ∈ factoredNumbers s ↔ ∀ p, p.Prime → p ∣ m → p ∈ s := by
  obtain ⟨p, hp₁, hp₂⟩ := exists_infinite_primes (1 + Finset.sup s id)
  rw [mem_factoredNumbers_iff_forall_le]
  refine ⟨fun ⟨H₀, H₁⟩ ↦ fun p hp₁ hp₂ ↦ H₁ p (le_of_dvd (Nat.pos_of_ne_zero H₀) hp₂) hp₁ hp₂,
         fun H ↦ ⟨fun h ↦ lt_irrefl p ?_, fun p _ ↦ H p⟩⟩
  calc
    p ≤ s.sup id := Finset.le_sup (f := @id ℕ) <| H p hp₂ <| h.symm ▸ dvd_zero p
    _ < 1 + s.sup id := lt_one_add _
    _ ≤ p := hp₁
/-
**Nat.ne_zero_of_mem_factoredNumbers** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：ne_zero_of_mem_factoredNumbers {s : Finset Nat} {m : Nat} (h : m in factor
edNumbers s) : m != 0
参数：h : m in factoredNumbers s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma ne_zero_of_mem_factoredNumbers {s : Finset ℕ} {m : ℕ} (h : m ∈ factoredNumbers s) : m ≠ 0 :=
  h.1

/-- The `Finset` of prime factors of an `s`-factored number is contained in `s`. -/
/-
**Nat.primeFactors_subset_of_mem_factoredNumbers** 是 Mathlib 中的一个引理，位于命名空间 `Nat`
。
形式化陈述：primeFactors_subset_of_mem_factoredNumbers {s : Finset Nat} {m : Nat} (hm 
: m in factoredNumbers s) : m.primeFactors subseteq s
参数：hm : m in factoredNumbers s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.mem_factoredNumbers`：mem_factoredNumbers {s : Finset Nat} {m : Nat} 
: m in factoredNumbers s ↔ m != 0 ∧ forall p in primeFactorsList m, p in s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Nat.mem_primeFactors_iff_mem_primeFactorsList`：mem_primeFactors_iff_mem_
primeFactorsList : p in n.primeFactors ↔ p in n.primeFactorsList

--- 原说明 ---
The `Finset` of prime factors of an `s`-factored number is contained in `s`.
-/
lemma primeFactors_subset_of_mem_factoredNumbers {s : Finset ℕ} {m : ℕ}
    (hm : m ∈ factoredNumbers s) :
    m.primeFactors ⊆ s := by
  rw [mem_factoredNumbers] at hm
  exact fun n hn ↦ hm.2 n (mem_primeFactors_iff_mem_primeFactorsList.mp hn)

/-- If `m ≠ 0` and the `Finset` of prime factors of `m` is contained in `s`, then `m`
is `s`-factored. -/
/-
**Nat.mem_factoredNumbers_of_primeFactors_subset** 是 Mathlib 中的一个引理，位于命名空间 `Nat`
。
形式化陈述：mem_factoredNumbers_of_primeFactors_subset {s : Finset Nat} {m : Nat} (hm 
: m != 0) (hp : m.primeFactors subseteq s) : m in factoredNumbers s
参数：hm : m != 0；hp : m.primeFactors subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.mem_factoredNumbers`：mem_factoredNumbers {s : Finset Nat} {m : Nat} 
: m in factoredNumbers s ↔ m != 0 ∧ forall p in primeFactorsList m, p in s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Nat.mem_primeFactors_iff_mem_primeFactorsList`：mem_primeFactors_iff_mem_
primeFactorsList : p in n.primeFactors ↔ p in n.primeFactorsList

--- 原说明 ---
If `m ≠ 0` and the `Finset` of prime factors of `m` is contained in `s`, then `m
`
is `s`-factored.
-/
lemma mem_factoredNumbers_of_primeFactors_subset {s : Finset ℕ} {m : ℕ} (hm : m ≠ 0)
    (hp : m.primeFactors ⊆ s) :
    m ∈ factoredNumbers s := by
  rw [mem_factoredNumbers]
  exact ⟨hm, fun p hp' ↦ hp <| mem_primeFactors_iff_mem_primeFactorsList.mpr hp'⟩

/-- `m` is `s`-factored if and only if `m ≠ 0` and its `Finset` of prime factors
is contained in `s`. -/
/-
**Nat.mem_factoredNumbers_iff_primeFactors_subset** 是 Mathlib 中的一个引理，位于命名空间 `Nat
`。
形式化陈述：mem_factoredNumbers_iff_primeFactors_subset {s : Finset Nat} {m : Nat} : m
 in factoredNumbers s ↔ m != 0 ∧ m.primeFactors subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.ne_zero_of_mem_factoredNumbers`：ne_zero_of_mem_factoredNumbers {s : 
Finset Nat} {m : Nat} (h : m in factoredNumbers s) : m != 0
· 使用引理 `Nat.primeFactors_subset_of_mem_factoredNumbers`：primeFactors_subset_of_m
em_factoredNumbers {s : Finset Nat} {m : Nat} (hm : m in factoredNumbers s) : m.
primeFactors subseteq s
· 使用引理 `Nat.mem_factoredNumbers_of_primeFactors_subset`：mem_factoredNumbers_of_p
rimeFactors_subset {s : Finset Nat} {m : Nat} (hm : m != 0) (hp : m.primeFactors
 subseteq s) : m in factoredNumbers …

--- 原说明 ---
`m` is `s`-factored if and only if `m ≠ 0` and its `Finset` of prime factors
is contained in `s`.
-/
lemma mem_factoredNumbers_iff_primeFactors_subset {s : Finset ℕ} {m : ℕ} :
    m ∈ factoredNumbers s ↔ m ≠ 0 ∧ m.primeFactors ⊆ s :=
  ⟨fun h ↦ ⟨ne_zero_of_mem_factoredNumbers h, primeFactors_subset_of_mem_factoredNumbers h⟩,
   fun ⟨h₁, h₂⟩ ↦ mem_factoredNumbers_of_primeFactors_subset h₁ h₂⟩

@[simp]
/-
**Nat.factoredNumbers_empty** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：factoredNumbers_empty : factoredNumbers ∅ = {1}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `ne_and_eq_iff_right`：ne_and_eq_iff_right {a b c : α} (h : b != c) : a !=
 b ∧ a = c ↔ a = c
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma factoredNumbers_empty : factoredNumbers ∅ = {1} := by
  ext m
  simp only [mem_factoredNumbers, Finset.notMem_empty, ← List.eq_nil_iff_forall_not_mem,
    primeFactorsList_eq_nil, and_or_left, not_and_self_iff, ne_and_eq_iff_right zero_ne_one,
    false_or, Set.mem_singleton_iff]

/-- The product of two `s`-factored numbers is again `s`-factored. -/
/-
**Nat.mul_mem_factoredNumbers** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：mul_mem_factoredNumbers {s : Finset Nat} {m n : Nat} (hm : m in factoredNu
mbers s) (hn : n in factoredNumbers s) : m * n in factoredNumbers s
参数：hm : m in factoredNumbers s；hn : n in factoredNumbers s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.primeFactors_subset_of_mem_factoredNumbers`：primeFactors_subset_of_m
em_factoredNumbers {s : Finset Nat} {m : Nat} (hm : m in factoredNumbers s) : m.
primeFactors subseteq s
· 使用引理 `Nat.mem_factoredNumbers_of_primeFactors_subset`：mem_factoredNumbers_of_p
rimeFactors_subset {s : Finset Nat} {m : Nat} (hm : m != 0) (hp : m.primeFactors
 subseteq s) : m in factoredNumbers …
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.union_subset`：union_subset (hs : s subseteq u) : t subseteq u -> 
s union t subseteq u
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nat.primeFactors_mul`：primeFactors_mul (ha : a != 0) (hb : b != 0) : (a 
* b).primeFactors = a.primeFactors union b.primeFactors

--- 原说明 ---
The product of two `s`-factored numbers is again `s`-factored.
-/
lemma mul_mem_factoredNumbers {s : Finset ℕ} {m n : ℕ} (hm : m ∈ factoredNumbers s)
    (hn : n ∈ factoredNumbers s) :
    m * n ∈ factoredNumbers s := by
  have hm' := primeFactors_subset_of_mem_factoredNumbers hm
  have hn' := primeFactors_subset_of_mem_factoredNumbers hn
  exact mem_factoredNumbers_of_primeFactors_subset (mul_ne_zero hm.1 hn.1)
    <| primeFactors_mul hm.1 hn.1 ▸ Finset.union_subset hm' hn'

/-- The product of the prime factors of `n` that are in `s` is an `s`-factored number. -/
/-
**Nat.prod_mem_factoredNumbers** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：prod_mem_factoredNumbers (s : Finset Nat) (n : Nat) : (n.primeFactorsList.
filter (· in s)).prod in factoredNumbers s
参数：s : Finset Nat；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `List.prod_ne_zero`：prod_ne_zero (hL : (0 : M₀) ∉ l) : l.prod != 0
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `LT.lt.false`：∀ {α : Type u_2} [inst : Preorder α] {a : α}, a < a → False
· 使用定理 `Nat.pos_of_mem_primeFactorsList`：pos_of_mem_primeFactorsList {n p : Nat}
 (h : p in primeFactorsList n) : 0 < p
· 使用定理 `List.mem_of_mem_filter`：mem_of_mem_filter {a : α} {l} (h : a in filter p
 l) : a in l
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.mem_primeFactorsList`：mem_primeFactorsList {n p} (hn : n != 0) : p i
n primeFactorsList n ↔ Prime p ∧ p ∣ n
· 使用定理 `decide_eq_true_eq`：∀ {p : Prop} [inst : Decidable p], (decide p = true) 
= p
· 使用定理 `List.of_mem_filter`：of_mem_filter {a : α} {l} (h : a in filter p l) : p 
a
· 使用定理 `mem_list_primes_of_dvd_prod`：mem_list_primes_of_dvd_prod {p : M} (hp : P
rime p) {L : List M} (hL : forall q in L, Prime q) (hpL : p ∣ L.prod) : p in L
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Nat.Prime.prime`：∀ {p : ℕ}, Nat.Prime p → Prime p
· 使用定理 `Nat.prime_of_mem_primeFactorsList`：prime_of_mem_primeFactorsList {n : Na
t} : forall {p : Nat}, p in primeFactorsList n -> Prime p

--- 原说明 ---
The product of the prime factors of `n` that are in `s` is an `s`-factored numbe
r.
-/
lemma prod_mem_factoredNumbers (s : Finset ℕ) (n : ℕ) :
    (n.primeFactorsList.filter (· ∈ s)).prod ∈ factoredNumbers s := by
  have h₀ : (n.primeFactorsList.filter (· ∈ s)).prod ≠ 0 :=
    List.prod_ne_zero fun h ↦ (pos_of_mem_primeFactorsList (List.mem_of_mem_filter h)).false
  refine ⟨h₀, fun p hp ↦ ?_⟩
  obtain ⟨H₁, H₂⟩ := (mem_primeFactorsList h₀).mp hp
  simpa only [decide_eq_true_eq] using List.of_mem_filter <| mem_list_primes_of_dvd_prod H₁.prime
    (fun _ hq ↦ (prime_of_mem_primeFactorsList (List.mem_of_mem_filter hq)).prime) H₂

/-- The sets of `s`-factored and of `s ∪ {N}`-factored numbers are the same when `N` is not prime.
See `Nat.equivProdNatFactoredNumbers` for when `N` is prime. -/
/-
**Nat.factoredNumbers_insert** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：factoredNumbers_insert (s : Finset Nat) {N : Nat} (hN : ¬ N.Prime) : facto
redNumbers (insert N s) = factoredNumbers s
参数：s : Finset Nat；hN : ¬ N.Prime。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.mem_of_mem_insert_of_ne`：mem_of_mem_insert_of_ne (h : b in insert
 a s) : b != a -> b in s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Nat.prime_of_mem_primeFactorsList`：prime_of_mem_primeFactorsList {n : Na
t} : forall {p : Nat}, p in primeFactorsList n -> Prime p
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s

--- 原说明 ---
The sets of `s`-factored and of `s ∪ {N}`-factored numbers are the same when `N`
 is not prime.
See `Nat.equivProdNatFactoredNumbers` for when `N` is prime.
-/
lemma factoredNumbers_insert (s : Finset ℕ) {N : ℕ} (hN : ¬ N.Prime) :
    factoredNumbers (insert N s) = factoredNumbers s := by
  ext m
  refine ⟨fun hm ↦ ⟨hm.1, fun p hp ↦ ?_⟩,
          fun hm ↦ ⟨hm.1, fun p hp ↦ Finset.mem_insert_of_mem <| hm.2 p hp⟩⟩
  exact Finset.mem_of_mem_insert_of_ne (hm.2 p hp)
    fun h ↦ hN <| h ▸ prime_of_mem_primeFactorsList hp
/-
**Nat.factoredNumbers_mono** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {s t : Finset ℕ}, s ⊆ t → Nat.factoredNumbers s ⊆ Nat.factoredNumbers t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
@[gcongr] lemma factoredNumbers_mono {s t : Finset ℕ} (hst : s ≤ t) :
    factoredNumbers s ⊆ factoredNumbers t :=
  fun _ hx ↦ ⟨hx.1, fun p hp ↦ hst <| hx.2 p hp⟩

/-- The non-zero non-`s`-factored numbers are `≥ N` when `s` contains all primes less than `N`. -/
/-
**Nat.factoredNumbers_compl** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：factoredNumbers_compl {N : Nat} {s : Finset Nat} (h : primesBelow N <= s) 
: (factoredNumbers s)ᶜ \ {0} subseteq {n | N <= n}
参数：h : primesBelow N <= s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Nat.mem_primesBelow`：mem_primesBelow : n in primesBelow k ↔ n < k ∧ n.Pr
ime
· 使用定理 `Nat.prime_of_mem_primeFactorsList`：prime_of_mem_primeFactorsList {n : Na
t} : forall {p : Nat}, p in primeFactorsList n -> Prime p
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Nat.le_of_mem_primeFactorsList`：le_of_mem_primeFactorsList {n p : Nat} (
h : p in n.primeFactorsList) : p <= n

--- 原说明 ---
The non-zero non-`s`-factored numbers are `≥ N` when `s` contains all primes les
s than `N`.
-/
lemma factoredNumbers_compl {N : ℕ} {s : Finset ℕ} (h : primesBelow N ≤ s) :
    (factoredNumbers s)ᶜ \ {0} ⊆ {n | N ≤ n} := by
  intro n hn
  simp only [Set.mem_compl_iff, mem_factoredNumbers, Set.mem_sdiff, ne_eq, not_and, not_forall,
    exists_prop, Set.mem_singleton_iff] at hn
  simp only [Set.mem_ofPred_eq]
  obtain ⟨p, hp₁, hp₂⟩ := hn.1 hn.2
  have : N ≤ p := by
    contrapose! hp₂
    exact h <| mem_primesBelow.mpr ⟨hp₂, prime_of_mem_primeFactorsList hp₁⟩
  exact this.trans <| le_of_mem_primeFactorsList hp₁

/-- If `p` is a prime and `n` is `s`-factored, then every product `p^e * n`
is `s ∪ {p}`-factored. -/
/-
**Nat.pow_mul_mem_factoredNumbers** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：pow_mul_mem_factoredNumbers {s : Finset Nat} {p n : Nat} (hp : p.Prime) (e
 : Nat) (hn : n in factoredNumbers s) : p ^ e * n in factoredNumbers (insert p s
)
参数：hp : p.Prime；e : Nat；hn : n in factoredNumbers s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.mem_primeFactorsList_mul`：mem_primeFactorsList_mul {a b : Nat} (ha :
 a != 0) (hb : b != 0) {p : Nat} : p in (a * b).primeFactorsList ↔ p in a.primeF
actorsList ∨ p in …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.prime_dvd_prime_iff_eq`：prime_dvd_prime_iff_eq {p q : Nat} (pp : p.P
rime) (qp : q.Prime) : p ∣ q ↔ p = q
· 使用定理 `Nat.mem_primeFactorsList`：mem_primeFactorsList {n p} (hn : n != 0) : p i
n primeFactorsList n ↔ Prime p ∧ p ∣ n
· 使用定理 `Nat.Prime.dvd_of_dvd_pow`：∀ {p m n : ℕ}, Nat.Prime p → p ∣ m ^ n → p ∣ m
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s

--- 原说明 ---
If `p` is a prime and `n` is `s`-factored, then every product `p^e * n`
is `s ∪ {p}`-factored.
-/
lemma pow_mul_mem_factoredNumbers {s : Finset ℕ} {p n : ℕ} (hp : p.Prime) (e : ℕ)
    (hn : n ∈ factoredNumbers s) :
    p ^ e * n ∈ factoredNumbers (insert p s) := by
  have hp' := pow_ne_zero e hp.ne_zero
  refine ⟨mul_ne_zero hp' hn.1, fun q hq ↦ ?_⟩
  rcases (mem_primeFactorsList_mul hp' hn.1).mp hq with H | H
  · rw [mem_primeFactorsList hp'] at H
    rw [(prime_dvd_prime_iff_eq H.1 hp).mp <| H.1.dvd_of_dvd_pow H.2]
    exact Finset.mem_insert_self p s
  · exact Finset.mem_insert_of_mem <| hn.2 _ H

/-- If `p ∉ s` is a prime and `n` is `s`-factored, then `p` and `n` are coprime. -/
/-
**Nat.Prime.factoredNumbers_coprime** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：∀ {s : Finset ℕ} {p n : ℕ}, Nat.Prime p → p ∉ s → n ∈ Nat.factoredNumbers 
s → p.Coprime n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.Prime.coprime_iff_not_dvd`：∀ {p n : ℕ}, Nat.Prime p → (p.Coprime n ↔
 ¬p ∣ n)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.mem_primeFactorsList_iff_dvd`：mem_primeFactorsList_iff_dvd {n p : Na
t} (hn : n != 0) (hp : Prime p) : p in primeFactorsList n ↔ p ∣ n where mp h
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
If `p ∉ s` is a prime and `n` is `s`-factored, then `p` and `n` are coprime.
-/
lemma Prime.factoredNumbers_coprime {s : Finset ℕ} {p n : ℕ} (hp : p.Prime) (hs : p ∉ s)
    (hn : n ∈ factoredNumbers s) :
    Nat.Coprime p n := by
  rw [hp.coprime_iff_not_dvd, ← mem_primeFactorsList_iff_dvd hn.1 hp]
  exact fun H ↦ hs <| hn.2 p H

/-- If `f : ℕ → F` is multiplicative on coprime arguments, `p ∉ s` is a prime and `m`
is `s`-factored, then `f (p^e * m) = f (p^e) * f m`. -/
/-
**Nat.factoredNumbers.map_prime_pow_mul** 是 Mathlib 中的一个定理，位于命名空间 `Nat.factoredN
umbers`。
形式化陈述：∀ {F : Type u_1} [inst : Mul F] {f : ℕ → F},   (∀ {m n : ℕ}, m.Coprime n →
 f (m * n) = f m * f n) →     ∀ {s : Finset ℕ} {p : ℕ},       Nat.Prime p → p ∉ 
s → ∀ (e : ℕ) {m : ↑(Nat.factoredNumbers s)}, f (p ^ e * ↑m) = f (p ^ e) * f ↑m
参数：∀ {m n : ℕ}, m.Coprime n → f (m * n) = f m * f n；e : ℕ；Nat.factoredNumbers s；
p ^ e * ↑m；p ^ e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Coprime.pow_left`：∀ {m k : ℕ} (n : ℕ), m.Coprime k → (m ^ n).Coprime
 k
· 使用定理 `Nat.Prime.factoredNumbers_coprime`：∀ {s : Finset ℕ} {p n : ℕ}, Nat.Prime
 p → p ∉ s → n ∈ Nat.factoredNumbers s → p.Coprime n
· 使用定理 `Subtype.mem`：Subtype.mem {α : Type*} {s : Set α} (p : s) : (p : α) in s

--- 原说明 ---
If `f : ℕ → F` is multiplicative on coprime arguments, `p ∉ s` is a prime and `m
`
is `s`-factored, then `f (p^e * m) = f (p^e) * f m`.
-/
lemma factoredNumbers.map_prime_pow_mul {F : Type*} [Mul F] {f : ℕ → F}
    (hmul : ∀ {m n}, Coprime m n → f (m * n) = f m * f n) {s : Finset ℕ} {p : ℕ}
    (hp : p.Prime) (hs : p ∉ s) (e : ℕ) {m : factoredNumbers s} :
    f (p ^ e * m) = f (p ^ e) * f m :=
  hmul <| Coprime.pow_left _ <| hp.factoredNumbers_coprime hs <| Subtype.mem m

set_option backward.isDefEq.respectTransparency false in
open List Perm in
/-- We establish the bijection from `ℕ × factoredNumbers s` to `factoredNumbers (s ∪ {p})`
given by `(e, n) ↦ p^e * n` when `p ∉ s` is a prime. See `Nat.factoredNumbers_insert` for
when `p` is not prime. -/
/-
**Nat.equivProdNatFactoredNumbers** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：equivProdNatFactoredNumbers {s : Finset Nat} {p : Nat} (hp : p.Prime) (hs 
: p ∉ s) : Nat × factoredNumbers s ≃ factoredNumbers (insert p s) where toFun
参数：hp : p.Prime；hs : p ∉ s。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.prod_mem_factoredNumbers`：prod_mem_factoredNumbers (s : Finset Nat) 
(n : Nat) : (n.primeFactorsList.filter (· in s)).prod in factoredNumbers s

--- 原说明 ---
We establish the bijection from `ℕ × factoredNumbers s` to `factoredNumbers (s ∪
 {p})`
given by `(e, n) ↦ p^e * n` when `p ∉ s` is a prime. See `Nat.factoredNumbers_in
sert` for
when `p` is not prime.
-/
def equivProdNatFactoredNumbers {s : Finset ℕ} {p : ℕ} (hp : p.Prime) (hs : p ∉ s) :
    ℕ × factoredNumbers s ≃ factoredNumbers (insert p s) where
  toFun := fun ⟨e, n⟩ ↦ ⟨p ^ e * n, pow_mul_mem_factoredNumbers hp e n.2⟩
  invFun := fun ⟨m, _⟩  ↦ (m.factorization p,
                            ⟨(m.primeFactorsList.filter (· ∈ s)).prod, prod_mem_factoredNumbers ..⟩)
  left_inv := by
    rintro ⟨e, m, hm₀, hm⟩
    have hpm : ¬ p ∣ m := by grind [mem_primeFactorsList]
    simp only [Prod.mk.injEq, Subtype.mk.injEq]
    constructor
    · rw [factorization_mul (pow_ne_zero e hp.ne_zero) hm₀, Finsupp.add_apply,
        factorization_pow_self hp, factorization_eq_zero_of_not_dvd hpm, add_zero]
    · conv_rhs => rw [← prod_primeFactorsList hm₀]
      refine prod_eq <|
        (filter _ <| perm_primeFactorsList_mul (pow_ne_zero e hp.ne_zero) hm₀).trans ?_
      rw [filter_append, hp.primeFactorsList_pow, filter_eq_nil_iff.mpr <| by grind, nil_append,
        filter_eq_self.mpr <| by grind]
  right_inv := by
    rintro ⟨m, hm₀, hm⟩
    rw [Subtype.mk.injEq, ← primeFactorsList_count_eq, ← prod_replicate, ← prod_append]
    conv_rhs => rw [← prod_primeFactorsList hm₀]
    have : m.primeFactorsList.filter (· = p) = m.primeFactorsList.filter (· ∉ s) :=
      filter_congr <| by grind
    refine prod_eq <| (filter_eq p).symm ▸ this ▸ perm_append_comm.trans ?_
    simp only [decide_not]
    exact filter_append_perm (· ∈ s) (primeFactorsList m)

@[simp]
/-
**Nat.equivProdNatFactoredNumbers_apply** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：equivProdNatFactoredNumbers_apply {s : Finset Nat} {p e m : Nat} (hp : p.P
rime) (hs : p ∉ s) (hm : m in factoredNumbers s) : equivProdNatFactoredNumbers h
p hs (e, ⟨m, hm⟩) = p ^ e * m
参数：hp : p.Prime；hs : p ∉ s；hm : m in factoredNumbers s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma equivProdNatFactoredNumbers_apply {s : Finset ℕ} {p e m : ℕ} (hp : p.Prime) (hs : p ∉ s)
    (hm : m ∈ factoredNumbers s) :
    equivProdNatFactoredNumbers hp hs (e, ⟨m, hm⟩) = p ^ e * m := rfl

@[simp]
/-
**Nat.equivProdNatFactoredNumbers_apply'** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：equivProdNatFactoredNumbers_apply' {s : Finset Nat} {p : Nat} (hp : p.Prim
e) (hs : p ∉ s) (x : Nat × factoredNumbers s) : equivProdNatFactoredNumbers hp h
s x = p ^ x.1 * x.2
参数：hp : p.Prime；hs : p ∉ s；x : Nat × factoredNumbers s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma equivProdNatFactoredNumbers_apply' {s : Finset ℕ} {p : ℕ} (hp : p.Prime) (hs : p ∉ s)
    (x : ℕ × factoredNumbers s) :
    equivProdNatFactoredNumbers hp hs x = p ^ x.1 * x.2 := rfl


/-!
### `n`-smooth numbers
-/

/-- `smoothNumbers n` is the set of *`n`-smooth positive natural numbers*, i.e., the
positive natural numbers all of whose prime factors are less than `n`. -/
/-
**Nat.smoothNumbers** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：smoothNumbers (n : Nat) : Set Nat
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`smoothNumbers n` is the set of *`n`-smooth positive natural numbers*, i.e., the
positive natural numbers all of whose prime factors are less than `n`.
-/
def smoothNumbers (n : ℕ) : Set ℕ := {m | m ≠ 0 ∧ ∀ p ∈ primeFactorsList m, p < n}
/-
**Nat.mem_smoothNumbers** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：mem_smoothNumbers {n m : Nat} : m in smoothNumbers n ↔ m != 0 ∧ forall p i
n primeFactorsList m, p < n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_smoothNumbers {n m : ℕ} : m ∈ smoothNumbers n ↔ m ≠ 0 ∧ ∀ p ∈ primeFactorsList m, p < n :=
  Iff.rfl

/-- The `n`-smooth numbers agree with the `Finset.range n`-factored numbers. -/
/-
**Nat.smoothNumbers_eq_factoredNumbers** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：smoothNumbers_eq_factoredNumbers (n : Nat) : smoothNumbers n = factoredNum
bers (Finset.range n)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The `n`-smooth numbers agree with the `Finset.range n`-factored numbers.
-/
lemma smoothNumbers_eq_factoredNumbers (n : ℕ) :
    smoothNumbers n = factoredNumbers (Finset.range n) := by
  simp only [smoothNumbers, ne_eq, mem_primeFactorsList', and_imp, factoredNumbers,
    Finset.mem_range]

/-- The `n`-smooth numbers agree with the `primesBelow n`-factored numbers. -/
/-
**Nat.smoothNumbers_eq_factoredNumbers_primesBelow** 是 Mathlib 中的一个引理，位于命名空间 `Na
t`。
形式化陈述：smoothNumbers_eq_factoredNumbers_primesBelow (n : Nat) : smoothNumbers n =
 factoredNumbers n.primesBelow
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.smoothNumbers_eq_factoredNumbers`：smoothNumbers_eq_factoredNumbers (
n : Nat) : smoothNumbers n = factoredNumbers (Finset.range n)
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Nat.mem_primesBelow`：mem_primesBelow : n in primesBelow k ↔ n < k ∧ n.Pr
ime
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n
· 使用定理 `Nat.factoredNumbers_mono`：∀ {s t : Finset ℕ}, s ⊆ t → Nat.factoredNumber
s s ⊆ Nat.factoredNumbers t
· 使用定理 `Finset.mem_of_mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : Decida
blePred p] {s : Finset α}, ∀ x ∈ Finset.filter p s, x ∈ s

--- 原说明 ---
The `n`-smooth numbers agree with the `primesBelow n`-factored numbers.
-/
lemma smoothNumbers_eq_factoredNumbers_primesBelow (n : ℕ) :
    smoothNumbers n = factoredNumbers n.primesBelow := by
  rw [smoothNumbers_eq_factoredNumbers]
  refine Set.Subset.antisymm (fun m hm ↦ ?_) <| factoredNumbers_mono Finset.mem_of_mem_filter
  simp_rw [mem_factoredNumbers'] at hm ⊢
  exact fun p hp hp' ↦ mem_primesBelow.mpr ⟨Finset.mem_range.mp <| hm p hp hp', hp⟩

/-- Membership in `Nat.smoothNumbers n` is decidable. -/
/-
**Nat.** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Membership in `Nat.smoothNumbers n` is decidable.
-/
instance (n : ℕ) : DecidablePred (· ∈ smoothNumbers n) :=
  inferInstanceAs <| DecidablePred fun x ↦ x ∈ {m | m ≠ 0 ∧ ∀ p ∈ primeFactorsList m, p < n}

/-- A number that divides an `n`-smooth number is itself `n`-smooth. -/
/-
**Nat.mem_smoothNumbers_of_dvd** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：mem_smoothNumbers_of_dvd {n m k : Nat} (h : m in smoothNumbers n) (h' : k 
∣ m) : k in smoothNumbers n
参数：h : m in smoothNumbers n；h' : k ∣ m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.smoothNumbers_eq_factoredNumbers`：smoothNumbers_eq_factoredNumbers (
n : Nat) : smoothNumbers n = factoredNumbers (Finset.range n)
· 使用引理 `Nat.mem_factoredNumbers_of_dvd`：mem_factoredNumbers_of_dvd {s : Finset N
at} {m k : Nat} (h : m in factoredNumbers s) (h' : k ∣ m) : k in factoredNumbers
 s

--- 原说明 ---
A number that divides an `n`-smooth number is itself `n`-smooth.
-/
lemma mem_smoothNumbers_of_dvd {n m k : ℕ} (h : m ∈ smoothNumbers n) (h' : k ∣ m) :
    k ∈ smoothNumbers n := by
  simp only [smoothNumbers_eq_factoredNumbers] at h ⊢
  exact mem_factoredNumbers_of_dvd h h'

/-- `m` is `n`-smooth if and only if `m` is nonzero and all prime divisors `≤ m` of `m`
are less than `n`. -/
/-
**Nat.mem_smoothNumbers_iff_forall_le** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：mem_smoothNumbers_iff_forall_le {n m : Nat} : m in smoothNumbers n ↔ m != 
0 ∧ forall p <= m, p.Prime -> p ∣ m -> p < n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.smoothNumbers_eq_factoredNumbers`：smoothNumbers_eq_factoredNumbers (
n : Nat) : smoothNumbers n = factoredNumbers (Finset.range n)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
`m` is `n`-smooth if and only if `m` is nonzero and all prime divisors `≤ m` of 
`m`
are less than `n`.
-/
lemma mem_smoothNumbers_iff_forall_le {n m : ℕ} :
    m ∈ smoothNumbers n ↔ m ≠ 0 ∧ ∀ p ≤ m, p.Prime → p ∣ m → p < n := by
  simp only [smoothNumbers_eq_factoredNumbers, mem_factoredNumbers_iff_forall_le, Finset.mem_range]

/-- `m` is `n`-smooth if and only if all prime divisors of `m` are less than `n`. -/
/-
**Nat.mem_smoothNumbers'** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：mem_smoothNumbers' {n m : Nat} : m in smoothNumbers n ↔ forall p, p.Prime 
-> p ∣ m -> p < n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.smoothNumbers_eq_factoredNumbers`：smoothNumbers_eq_factoredNumbers (
n : Nat) : smoothNumbers n = factoredNumbers (Finset.range n)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
`m` is `n`-smooth if and only if all prime divisors of `m` are less than `n`.
-/
lemma mem_smoothNumbers' {n m : ℕ} : m ∈ smoothNumbers n ↔ ∀ p, p.Prime → p ∣ m → p < n := by
  simp only [smoothNumbers_eq_factoredNumbers, mem_factoredNumbers', Finset.mem_range]

/-- The `Finset` of prime factors of an `n`-smooth number is contained in the `Finset`
of primes below `n`. -/
/-
**Nat.primeFactors_subset_of_mem_smoothNumbers** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：primeFactors_subset_of_mem_smoothNumbers {m n : Nat} (hms : m in n.smoothN
umbers) : m.primeFactors subseteq n.primesBelow
参数：hms : m in n.smoothNumbers。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.primeFactors_subset_of_mem_factoredNumbers`：primeFactors_subset_of_m
em_factoredNumbers {s : Finset Nat} {m : Nat} (hm : m in factoredNumbers s) : m.
primeFactors subseteq s
· 使用引理 `Nat.smoothNumbers_eq_factoredNumbers_primesBelow`：smoothNumbers_eq_facto
redNumbers_primesBelow (n : Nat) : smoothNumbers n = factoredNumbers n.primesBel
ow

--- 原说明 ---
The `Finset` of prime factors of an `n`-smooth number is contained in the `Finse
t`
of primes below `n`.
-/
lemma primeFactors_subset_of_mem_smoothNumbers {m n : ℕ} (hms : m ∈ n.smoothNumbers) :
    m.primeFactors ⊆ n.primesBelow :=
  primeFactors_subset_of_mem_factoredNumbers <|
    smoothNumbers_eq_factoredNumbers_primesBelow n ▸ hms

/-- `m` is an `n`-smooth number if the `Finset` of its prime factors consists of numbers `< n`. -/
/-
**Nat.mem_smoothNumbers_of_primeFactors_subset** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：mem_smoothNumbers_of_primeFactors_subset {m n : Nat} (hm : m != 0) (hp : m
.primeFactors subseteq Finset.range n) : m in n.smoothNumbers
参数：hm : m != 0；hp : m.primeFactors subseteq Finset.range n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.mem_factoredNumbers_of_primeFactors_subset`：mem_factoredNumbers_of_p
rimeFactors_subset {s : Finset Nat} {m : Nat} (hm : m != 0) (hp : m.primeFactors
 subseteq s) : m in factoredNumbers …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nat.smoothNumbers_eq_factoredNumbers`：smoothNumbers_eq_factoredNumbers (
n : Nat) : smoothNumbers n = factoredNumbers (Finset.range n)

--- 原说明 ---
`m` is an `n`-smooth number if the `Finset` of its prime factors consists of num
bers `< n`.
-/
lemma mem_smoothNumbers_of_primeFactors_subset {m n : ℕ} (hm : m ≠ 0)
    (hp : m.primeFactors ⊆ Finset.range n) : m ∈ n.smoothNumbers :=
  smoothNumbers_eq_factoredNumbers n ▸ mem_factoredNumbers_of_primeFactors_subset hm hp

/-- `m` is an `n`-smooth number if and only if `m ≠ 0` and the `Finset` of its prime factors
is contained in the `Finset` of primes below `n` -/
/-
**Nat.mem_smoothNumbers_iff_primeFactors_subset** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：mem_smoothNumbers_iff_primeFactors_subset {m n : Nat} : m in n.smoothNumbe
rs ↔ m != 0 ∧ m.primeFactors subseteq n.primesBelow
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `Nat.primeFactors_subset_of_mem_smoothNumbers`：primeFactors_subset_of_mem
_smoothNumbers {m n : Nat} (hms : m in n.smoothNumbers) : m.primeFactors subsete
q n.primesBelow
· 使用引理 `Nat.mem_smoothNumbers_of_primeFactors_subset`：mem_smoothNumbers_of_prime
Factors_subset {m n : Nat} (hm : m != 0) (hp : m.primeFactors subseteq Finset.ra
nge n) : m in n.smoothNumbers
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finset.filter_subset`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidableP
red p] (s : Finset α), Finset.filter p s ⊆ s

--- 原说明 ---
`m` is an `n`-smooth number if and only if `m ≠ 0` and the `Finset` of its prime
 factors
is contained in the `Finset` of primes below `n`
-/
lemma mem_smoothNumbers_iff_primeFactors_subset {m n : ℕ} :
    m ∈ n.smoothNumbers ↔ m ≠ 0 ∧ m.primeFactors ⊆ n.primesBelow :=
  ⟨fun h ↦ ⟨h.1, primeFactors_subset_of_mem_smoothNumbers h⟩,
   fun h ↦ mem_smoothNumbers_of_primeFactors_subset h.1 <| h.2.trans <| Finset.filter_subset ..⟩

/-- Zero is never a smooth number -/
/-
**Nat.ne_zero_of_mem_smoothNumbers** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：ne_zero_of_mem_smoothNumbers {n m : Nat} (h : m in smoothNumbers n) : m !=
 0
参数：h : m in smoothNumbers n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
Zero is never a smooth number
-/
lemma ne_zero_of_mem_smoothNumbers {n m : ℕ} (h : m ∈ smoothNumbers n) : m ≠ 0 := h.1

@[simp]
/-
**Nat.smoothNumbers_zero** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：smoothNumbers_zero : smoothNumbers 0 = {1}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.smoothNumbers_eq_factoredNumbers`：smoothNumbers_eq_factoredNumbers (
n : Nat) : smoothNumbers n = factoredNumbers (Finset.range n)
· 使用引理 `Nat.factoredNumbers_empty`：factoredNumbers_empty : factoredNumbers ∅ = {
1}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma smoothNumbers_zero : smoothNumbers 0 = {1} := by
  simp only [smoothNumbers_eq_factoredNumbers, Finset.range_zero, factoredNumbers_empty]

/-- The product of two `n`-smooth numbers is an `n`-smooth number. -/
/-
**Nat.mul_mem_smoothNumbers** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：mul_mem_smoothNumbers {m₁ m₂ n : Nat} (hm1 : m₁ in n.smoothNumbers) (hm2 :
 m₂ in n.smoothNumbers) : m₁ * m₂ in n.smoothNumbers
参数：hm1 : m₁ in n.smoothNumbers；hm2 : m₂ in n.smoothNumbers。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.smoothNumbers_eq_factoredNumbers`：smoothNumbers_eq_factoredNumbers (
n : Nat) : smoothNumbers n = factoredNumbers (Finset.range n)
· 使用引理 `Nat.mul_mem_factoredNumbers`：mul_mem_factoredNumbers {s : Finset Nat} {m
 n : Nat} (hm : m in factoredNumbers s) (hn : n in factoredNumbers s) : m * n in
 factoredNumbers …

--- 原说明 ---
The product of two `n`-smooth numbers is an `n`-smooth number.
-/
theorem mul_mem_smoothNumbers {m₁ m₂ n : ℕ}
    (hm1 : m₁ ∈ n.smoothNumbers) (hm2 : m₂ ∈ n.smoothNumbers) : m₁ * m₂ ∈ n.smoothNumbers := by
  rw [smoothNumbers_eq_factoredNumbers] at hm1 hm2 ⊢
  exact mul_mem_factoredNumbers hm1 hm2

/-- The product of the prime factors of `n` that are less than `N` is an `N`-smooth number. -/
/-
**Nat.prod_mem_smoothNumbers** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：prod_mem_smoothNumbers (n N : Nat) : (n.primeFactorsList.filter (· < N)).p
rod in smoothNumbers N
参数：n N : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.smoothNumbers_eq_factoredNumbers`：smoothNumbers_eq_factoredNumbers (
n : Nat) : smoothNumbers n = factoredNumbers (Finset.range n)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Decidable.decide.congr_simp`：∀ (p p_1 : Prop), p = p_1 → ∀ {h : Decidabl
e p} [h_1 : Decidable p_1], decide p = decide p_1

--- 原说明 ---
The product of the prime factors of `n` that are less than `N` is an `N`-smooth 
number.
-/
lemma prod_mem_smoothNumbers (n N : ℕ) :
    (n.primeFactorsList.filter (· < N)).prod ∈ smoothNumbers N := by
  simp only [smoothNumbers_eq_factoredNumbers, ← Finset.mem_range, prod_mem_factoredNumbers]

/-- The sets of `N`-smooth and of `(N+1)`-smooth numbers are the same when `N` is not prime.
See `Nat.equivProdNatSmoothNumbers` for when `N` is prime. -/
/-
**Nat.smoothNumbers_succ** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：smoothNumbers_succ {N : Nat} (hN : ¬ N.Prime) : (N + 1).smoothNumbers = N.
smoothNumbers
参数：hN : ¬ N.Prime。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.smoothNumbers_eq_factoredNumbers`：smoothNumbers_eq_factoredNumbers (
n : Nat) : smoothNumbers n = factoredNumbers (Finset.range n)
· 使用定理 `Finset.range_add_one`：range_add_one : range (n + 1) = insert n (range n)
· 使用引理 `Nat.factoredNumbers_insert`：factoredNumbers_insert (s : Finset Nat) {N :
 Nat} (hN : ¬ N.Prime) : factoredNumbers (insert N s) = factoredNumbers s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The sets of `N`-smooth and of `(N+1)`-smooth numbers are the same when `N` is no
t prime.
See `Nat.equivProdNatSmoothNumbers` for when `N` is prime.
-/
lemma smoothNumbers_succ {N : ℕ} (hN : ¬ N.Prime) : (N + 1).smoothNumbers = N.smoothNumbers := by
  simp only [smoothNumbers_eq_factoredNumbers, Finset.range_add_one, factoredNumbers_insert _ hN]
/-
**Nat.smoothNumbers_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：Nat.smoothNumbers 1 = {1}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.smoothNumbers_succ`：smoothNumbers_succ {N : Nat} (hN : ¬ N.Prime) : 
(N + 1).smoothNumbers = N.smoothNumbers
· 使用定理 `eq_false_of_decide`：∀ {p : Prop} {x : Decidable p}, decide p = false → p
 = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `Nat.smoothNumbers_zero`：smoothNumbers_zero : smoothNumbers 0 = {1}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma smoothNumbers_one : smoothNumbers 1 = {1} := by
  simp +decide only [not_false_eq_true, smoothNumbers_succ, smoothNumbers_zero]
/-
**Nat.smoothNumbers_mono** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {N M : ℕ}, N ≤ M → N.smoothNumbers ⊆ M.smoothNumbers
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
@[gcongr] lemma smoothNumbers_mono {N M : ℕ} (hNM : N ≤ M) : N.smoothNumbers ⊆ M.smoothNumbers :=
  fun _ hx ↦ ⟨hx.1, fun p hp => (hx.2 p hp).trans_le hNM⟩

/-- All `m`, `0 < m < n` are `n`-smooth numbers -/
/-
**Nat.mem_smoothNumbers_of_lt** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：mem_smoothNumbers_of_lt {m n : Nat} (hm : 0 < m) (hmn : m < n) : m in n.sm
oothNumbers
参数：hm : 0 < m；hmn : m < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_zero_of_lt`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : 
Zero α] [IsBotZeroClass α], a < b → b ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Nat.le_of_mem_primeFactorsList`：le_of_mem_primeFactorsList {n p : Nat} (
h : p in n.primeFactorsList) : p <= n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nat.smoothNumbers_eq_factoredNumbers`：smoothNumbers_eq_factoredNumbers (
n : Nat) : smoothNumbers n = factoredNumbers (Finset.range n)

--- 原说明 ---
All `m`, `0 < m < n` are `n`-smooth numbers
-/
lemma mem_smoothNumbers_of_lt {m n : ℕ} (hm : 0 < m) (hmn : m < n) : m ∈ n.smoothNumbers :=
  smoothNumbers_eq_factoredNumbers _ ▸ ⟨ne_zero_of_lt hm,
  fun _ h => Finset.mem_range.mpr <| lt_of_le_of_lt (le_of_mem_primeFactorsList h) hmn⟩

/-- The non-zero non-`N`-smooth numbers are `≥ N`. -/
/-
**Nat.smoothNumbers_compl** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：smoothNumbers_compl (N : Nat) : (N.smoothNumbers)ᶜ \ {0} subseteq {n | N <
= n}
参数：N : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.smoothNumbers_eq_factoredNumbers`：smoothNumbers_eq_factoredNumbers (
n : Nat) : smoothNumbers n = factoredNumbers (Finset.range n)
· 使用引理 `Nat.factoredNumbers_compl`：factoredNumbers_compl {N : Nat} {s : Finset N
at} (h : primesBelow N <= s) : (factoredNumbers s)ᶜ \ {0} subseteq {n | N <= n}
· 使用定理 `Finset.filter_subset`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidableP
red p] (s : Finset α), Finset.filter p s ⊆ s

--- 原说明 ---
The non-zero non-`N`-smooth numbers are `≥ N`.
-/
lemma smoothNumbers_compl (N : ℕ) : (N.smoothNumbers)ᶜ \ {0} ⊆ {n | N ≤ n} := by
  simpa only [smoothNumbers_eq_factoredNumbers]
    using factoredNumbers_compl <| Finset.filter_subset _ (Finset.range N)

/-- If `p` is positive and `n` is `p`-smooth, then every product `p^e * n` is `(p+1)`-smooth. -/
/-
**Nat.pow_mul_mem_smoothNumbers** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：pow_mul_mem_smoothNumbers {p n : Nat} (hp : p != 0) (e : Nat) (hn : n in s
moothNumbers p) : p ^ e * n in smoothNumbers (succ p)
参数：hp : p != 0；e : Nat；hn : n in smoothNumbers p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.mem_primeFactorsList_mul`：mem_primeFactorsList_mul {a b : Nat} (ha :
 a != 0) (hb : b != 0) {p : Nat} : p in (a * b).primeFactorsList ↔ p in a.primeF
actorsList ∨ p in …
· 使用定理 `Nat.lt_succ_of_le`：∀ {n m : ℕ}, n ≤ m → n < m.succ
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
· 使用定理 `Nat.Prime.dvd_of_dvd_pow`：∀ {p m n : ℕ}, Nat.Prime p → p ∣ m ^ n → p ∣ m
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.mem_primeFactorsList`：mem_primeFactorsList {n p} (hn : n != 0) : p i
n primeFactorsList n ↔ Prime p ∧ p ∣ n
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ

--- 原说明 ---
If `p` is positive and `n` is `p`-smooth, then every product `p^e * n` is `(p+1)
`-smooth.
-/
lemma pow_mul_mem_smoothNumbers {p n : ℕ} (hp : p ≠ 0) (e : ℕ) (hn : n ∈ smoothNumbers p) :
    p ^ e * n ∈ smoothNumbers (succ p) := by
  -- This cannot be easily reduced to `pow_mul_mem_factoredNumbers`, as there `p.Prime` is needed.
  have : NoZeroDivisors ℕ := inferInstance -- this is needed twice --> speed-up
  have hp' := pow_ne_zero e hp
  refine ⟨mul_ne_zero hp' hn.1, fun q hq ↦ ?_⟩
  rcases (mem_primeFactorsList_mul hp' hn.1).mp hq with H | H
  · rw [mem_primeFactorsList hp'] at H
    exact Nat.lt_succ_of_le <| le_of_dvd hp.bot_lt <| H.1.dvd_of_dvd_pow H.2
  · exact (hn.2 q H).trans <| lt_succ_self p

/-- If `p` is a prime and `n` is `p`-smooth, then `p` and `n` are coprime. -/
/-
**Nat.Prime.smoothNumbers_coprime** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：∀ {p n : ℕ}, Nat.Prime p → n ∈ p.smoothNumbers → p.Coprime n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Prime.factoredNumbers_coprime`：∀ {s : Finset ℕ} {p n : ℕ}, Nat.Prime
 p → p ∉ s → n ∈ Nat.factoredNumbers s → p.Coprime n
· 使用定理 `Finset.notMem_range_self`：notMem_range_self : n ∉ range n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.smoothNumbers_eq_factoredNumbers`：smoothNumbers_eq_factoredNumbers (
n : Nat) : smoothNumbers n = factoredNumbers (Finset.range n)

--- 原说明 ---
If `p` is a prime and `n` is `p`-smooth, then `p` and `n` are coprime.
-/
lemma Prime.smoothNumbers_coprime {p n : ℕ} (hp : p.Prime) (hn : n ∈ smoothNumbers p) :
    Nat.Coprime p n := by
  simp only [smoothNumbers_eq_factoredNumbers] at hn
  exact hp.factoredNumbers_coprime Finset.notMem_range_self hn

/-- If `f : ℕ → F` is multiplicative on coprime arguments, `p` is a prime and `m` is `p`-smooth,
then `f (p^e * m) = f (p^e) * f m`. -/
/-
**Nat.map_prime_pow_mul** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：map_prime_pow_mul {F : Type*} [Mul F] {f : Nat -> F} (hmul : forall {m n},
 Nat.Coprime m n -> f (m * n) = f m * f n) {p : Nat} (hp : p.Prime) (e : Nat) {m
 : p.smoothNumbers} : f (p ^ e * m) = f (p ^ e) * f m
参数：hmul : forall {m n}, Nat.Coprime m n -> f (m * n) = f m * f n；hp : p.Prime；e 
: Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Coprime.pow_left`：∀ {m k : ℕ} (n : ℕ), m.Coprime k → (m ^ n).Coprime
 k
· 使用定理 `Nat.Prime.smoothNumbers_coprime`：∀ {p n : ℕ}, Nat.Prime p → n ∈ p.smooth
Numbers → p.Coprime n
· 使用定理 `Subtype.mem`：Subtype.mem {α : Type*} {s : Set α} (p : s) : (p : α) in s

--- 原说明 ---
If `f : ℕ → F` is multiplicative on coprime arguments, `p` is a prime and `m` is
 `p`-smooth,
then `f (p^e * m) = f (p^e) * f m`.
-/
lemma map_prime_pow_mul {F : Type*} [Mul F] {f : ℕ → F}
    (hmul : ∀ {m n}, Nat.Coprime m n → f (m * n) = f m * f n) {p : ℕ} (hp : p.Prime) (e : ℕ)
    {m : p.smoothNumbers} :
    f (p ^ e * m) = f (p ^ e) * f m :=
  hmul <| Coprime.pow_left _ <| hp.smoothNumbers_coprime <| Subtype.mem m

open List Perm Equiv in
/-- We establish the bijection from `ℕ × smoothNumbers p` to `smoothNumbers (p+1)`
given by `(e, n) ↦ p^e * n` when `p` is a prime. See `Nat.smoothNumbers_succ` for
when `p` is not prime. -/
/-
**Nat.equivProdNatSmoothNumbers** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：equivProdNatSmoothNumbers {p : Nat} (hp : p.Prime) : Nat × smoothNumbers p
 ≃ smoothNumbers (p + 1)
参数：hp : p.Prime。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用引理 `Nat.smoothNumbers_eq_factoredNumbers`：smoothNumbers_eq_factoredNumbers (
n : Nat) : smoothNumbers n = factoredNumbers (Finset.range n)
· 使用定理 `Finset.notMem_range_self`：notMem_range_self : n ∉ range n

--- 原说明 ---
We establish the bijection from `ℕ × smoothNumbers p` to `smoothNumbers (p+1)`
given by `(e, n) ↦ p^e * n` when `p` is a prime. See `Nat.smoothNumbers_succ` fo
r
when `p` is not prime.
-/
def equivProdNatSmoothNumbers {p : ℕ} (hp : p.Prime) :
    ℕ × smoothNumbers p ≃ smoothNumbers (p + 1) :=
  ((prodCongrRight fun _ ↦ setCongr <| smoothNumbers_eq_factoredNumbers p).trans <|
    equivProdNatFactoredNumbers hp Finset.notMem_range_self).trans <|
    setCongr <| (smoothNumbers_eq_factoredNumbers (p + 1)) ▸ Finset.range_add_one ▸ rfl

@[simp]
/-
**Nat.equivProdNatSmoothNumbers_apply** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：equivProdNatSmoothNumbers_apply {p e m : Nat} (hp : p.Prime) (hm : m in p.
smoothNumbers) : equivProdNatSmoothNumbers hp (e, ⟨m, hm⟩) = p ^ e * m
参数：hp : p.Prime；hm : m in p.smoothNumbers。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma equivProdNatSmoothNumbers_apply {p e m : ℕ} (hp : p.Prime) (hm : m ∈ p.smoothNumbers) :
    equivProdNatSmoothNumbers hp (e, ⟨m, hm⟩) = p ^ e * m := rfl

@[simp]
/-
**Nat.equivProdNatSmoothNumbers_apply'** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：equivProdNatSmoothNumbers_apply' {p : Nat} (hp : p.Prime) (x : Nat × p.smo
othNumbers) : equivProdNatSmoothNumbers hp x = p ^ x.1 * x.2
参数：hp : p.Prime；x : Nat × p.smoothNumbers。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma equivProdNatSmoothNumbers_apply' {p : ℕ} (hp : p.Prime) (x : ℕ × p.smoothNumbers) :
    equivProdNatSmoothNumbers hp x = p ^ x.1 * x.2 := rfl


/-!
### Smooth and rough numbers up to a bound

We consider the sets of smooth and non-smooth ("rough") positive natural numbers `≤ N`
and prove bounds for their sizes.
-/

/-- The `k`-smooth numbers up to and including `N` as a `Finset` -/
/-
**Nat.smoothNumbersUpTo** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：smoothNumbersUpTo (N k : Nat) : Finset Nat
参数：N k : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `k`-smooth numbers up to and including `N` as a `Finset`
-/
def smoothNumbersUpTo (N k : ℕ) : Finset ℕ :=
  {n ∈ Finset.range (N + 1) | n ∈ smoothNumbers k}
/-
**Nat.mem_smoothNumbersUpTo** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：mem_smoothNumbersUpTo {N k n : Nat} : n in smoothNumbersUpTo N k ↔ n <= N 
∧ n in smoothNumbers k
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
lemma mem_smoothNumbersUpTo {N k n : ℕ} :
    n ∈ smoothNumbersUpTo N k ↔ n ≤ N ∧ n ∈ smoothNumbers k := by
  simp [smoothNumbersUpTo]

/-- The positive non-`k`-smooth (so "`k`-rough") numbers up to and including `N` as a `Finset` -/
/-
**Nat.roughNumbersUpTo** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：roughNumbersUpTo (N k : Nat) : Finset Nat
参数：N k : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The positive non-`k`-smooth (so "`k`-rough") numbers up to and including `N` as 
a `Finset`
-/
def roughNumbersUpTo (N k : ℕ) : Finset ℕ :=
  {n ∈ Finset.range (N + 1) | n ≠ 0 ∧ n ∉ smoothNumbers k}
/-
**Nat.smoothNumbersUpTo_card_add_roughNumbersUpTo_card** 是 Mathlib 中的一个引理，位于命名空间
 `Nat`。
形式化陈述：smoothNumbersUpTo_card_add_roughNumbersUpTo_card (N k : Nat) : #(smoothNum
bersUpTo N k) + #(roughNumbersUpTo N k) = N
参数：N k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.smoothNumbersUpTo.eq_1`：∀ (N k : ℕ), N.smoothNumbersUpTo k = {n ∈ Fi
nset.range (N + 1) | n ∈ k.smoothNumbers}
· 使用定理 `Nat.roughNumbersUpTo.eq_1`：∀ (N k : ℕ), N.roughNumbersUpTo k = {n ∈ Fins
et.range (N + 1) | n ≠ 0 ∧ n ∉ k.smoothNumbers}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_union_of_disjoint`：∀ {α : Type u_1} {s t : Finset α} [inst :
 DecidableEq α], Disjoint s t → (s ∪ t).card = s.card + t.card
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.disjoint_filter`：disjoint_filter {s : Finset α} {p q : α -> Prop}
 [DecidablePred p] [DecidablePred q] : Disjoint (s.filter p) (s.filter q) ↔ fora
ll x in s, p…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finset.filter_union_right`：filter_union_right (s : Finset α) : s.filter 
p union s.filter q = s.filter fun x => p x ∨ q x
· 使用定理 `Finset.filter_ne'`：filter_ne' [DecidableEq β] (s : Finset β) (b : β) : (
s.filter fun a => a != b) = s.erase b
· 使用定理 `Finset.card_erase_of_mem`：card_erase_of_mem : a in s -> #(s.erase a) = #
s - 1
· 使用定理 `Finset.mem_range_succ_iff`：mem_range_succ_iff {a b : Nat} : a in range b
.succ ↔ a <= b
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
· 使用定理 `Nat.succ_sub_succ_eq_sub`：∀ (n m : ℕ), n.succ - m.succ = n - m
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Nat.ne_zero_of_mem_smoothNumbers`：ne_zero_of_mem_smoothNumbers {n m : Na
t} (h : m in smoothNumbers n) : m != 0
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
-/
lemma smoothNumbersUpTo_card_add_roughNumbersUpTo_card (N k : ℕ) :
    #(smoothNumbersUpTo N k) + #(roughNumbersUpTo N k) = N := by
  rw [smoothNumbersUpTo, roughNumbersUpTo,
    ← Finset.card_union_of_disjoint <| Finset.disjoint_filter.mpr fun n _ hn₂ h ↦ h.2 hn₂,
    Finset.filter_union_right]
  suffices #{x ∈ Finset.range (N + 1) | x ≠ 0} = N by
    have hn' (n) : n ∈ smoothNumbers k ∨ n ≠ 0 ∧ n ∉ smoothNumbers k ↔ n ≠ 0 := by
      have : n ∈ smoothNumbers k → n ≠ 0 := ne_zero_of_mem_smoothNumbers
      refine ⟨fun H ↦ Or.elim H this fun H ↦ H.1, fun H ↦ ?_⟩
      simp only [ne_eq, H, not_false_eq_true, true_and, or_not]
    rwa [Finset.filter_congr (s := Finset.range (succ N)) fun n _ ↦ hn' n]
  rw [Finset.filter_ne', Finset.card_erase_of_mem <| Finset.mem_range_succ_iff.mpr <| zero_le N]
  simp only [Finset.card_range, succ_sub_succ_eq_sub, Nat.sub_zero]

/-- A `k`-smooth number can be written as a square times a product of distinct primes `< k`. -/
/-
**Nat.eq_prod_primes_mul_sq_of_mem_smoothNumbers** 是 Mathlib 中的一个引理，位于命名空间 `Nat`
。
形式化陈述：eq_prod_primes_mul_sq_of_mem_smoothNumbers {n k : Nat} (h : n in smoothNum
bers k) : exists s in k.primesBelow.powerset, exists m, n = m ^ 2 * (s.prod id)
参数：h : n in smoothNumbers k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.sq_mul_squarefree`：sq_mul_squarefree (n : Nat) : exists a b : Nat, b
 ^ 2 * a = n ∧ Squarefree a
· 使用引理 `Nat.mem_smoothNumbers_of_dvd`：mem_smoothNumbers_of_dvd {n m k : Nat} (h 
: m in smoothNumbers n) (h' : k ∣ m) : k in smoothNumbers n
· 使用定理 `Dvd.intro_left`：Dvd.intro_left (c : α) (h : c * a = b) : a ∣ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Nat.mem_primesBelow`：mem_primesBelow : n in primesBelow k ↔ n < k ∧ n.Pr
ime
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Nat.mem_smoothNumbers'`：mem_smoothNumbers' {n m : Nat} : m in smoothNumb
ers n ↔ forall p, p.Prime -> p ∣ m -> p < n
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.mem_primeFactors`：∀ {n p : ℕ}, p ∈ n.primeFactors ↔ Nat.Prime p ∧ p 
∣ n ∧ n ≠ 0
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nat.prod_primeFactors_of_squarefree`：prod_primeFactors_of_squarefree (hn
 : Squarefree n) : ∏ p in n.primeFactors, p = n

--- 原说明 ---
A `k`-smooth number can be written as a square times a product of distinct prime
s `< k`.
-/
lemma eq_prod_primes_mul_sq_of_mem_smoothNumbers {n k : ℕ} (h : n ∈ smoothNumbers k) :
    ∃ s ∈ k.primesBelow.powerset, ∃ m, n = m ^ 2 * (s.prod id) := by
  obtain ⟨l, m, H₁, H₂⟩ := sq_mul_squarefree n
  have hl : l ∈ smoothNumbers k := mem_smoothNumbers_of_dvd h (Dvd.intro_left (m ^ 2) H₁)
  refine ⟨l.primeFactorsList.toFinset, ?_, m, ?_⟩
  · simp only [toFinset_factors, Finset.mem_powerset]
    refine fun p hp ↦ mem_primesBelow.mpr ⟨?_, (mem_primeFactors.mp hp).1⟩
    rw [mem_primeFactors] at hp
    exact mem_smoothNumbers'.mp hl p hp.1 hp.2.1
  rw [← H₁]
  congr
  simp only [toFinset_factors]
  exact (prod_primeFactors_of_squarefree H₂).symm

/-- The set of `k`-smooth numbers `≤ N` is contained in the set of numbers of the form `m^2 * P`,
where `m ≤ √N` and `P` is a product of distinct primes `< k`. -/
/-
**Nat.smoothNumbersUpTo_subset_image** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：smoothNumbersUpTo_subset_image (N k : Nat) : smoothNumbersUpTo N k subsete
q Finset.image (fun (s, m) => m ^ 2 * (s.prod id)) (k.primesBelow.powerset ×ˢ (F
inset.range (N.sqrt + 1)).erase 0)
参数：N k : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Nat.mem_smoothNumbersUpTo`：mem_smoothNumbersUpTo {N k n : Nat} : n in sm
oothNumbersUpTo N k ↔ n <= N ∧ n in smoothNumbers k
· 使用引理 `Nat.eq_prod_primes_mul_sq_of_mem_smoothNumbers`：eq_prod_primes_mul_sq_of
_mem_smoothNumbers {n k : Nat} (h : n in smoothNumbers k) : exists s in k.primes
Below.powerset, exists m, n = m ^ 2 …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.mem_powerset`：mem_powerset {s t : Finset α} : s in powerset t ↔ s
 subseteq t
· 使用引理 `Nat.ne_zero_of_mem_smoothNumbers`：ne_zero_of_mem_smoothNumbers {n m : Na
t} (h : m in smoothNumbers n) : m != 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `Nat.lt_succ_iff`：∀ {m n : ℕ}, m < n.succ ↔ m ≤ n
· 使用引理 `Nat.le_sqrt'`：le_sqrt' : m <= sqrt n ↔ m ^ 2 <= n
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Finset.one_le_prod'`：one_le_prod' [MulLeftMono N] (h : forall i in s, 1 
<= f i) : 1 <= ∏ i in s, f i
· 使用定理 `Nat.Prime.one_le`：∀ {p : ℕ}, Nat.Prime p → 1 ≤ p
· 使用引理 `Nat.prime_of_mem_primesBelow`：prime_of_mem_primesBelow (h : p in n.prime
sBelow) : p.Prime

--- 原说明 ---
The set of `k`-smooth numbers `≤ N` is contained in the set of numbers of the fo
rm `m^2 * P`,
where `m ≤ √N` and `P` is a product of distinct primes `< k`.
-/
lemma smoothNumbersUpTo_subset_image (N k : ℕ) :
    smoothNumbersUpTo N k ⊆ Finset.image (fun (s, m) ↦ m ^ 2 * (s.prod id))
      (k.primesBelow.powerset ×ˢ (Finset.range (N.sqrt + 1)).erase 0) := by
  intro n hn
  obtain ⟨hn₁, hn₂⟩ := mem_smoothNumbersUpTo.mp hn
  obtain ⟨s, hs, m, hm⟩ := eq_prod_primes_mul_sq_of_mem_smoothNumbers hn₂
  simp only [id_eq, Finset.mem_range, Finset.mem_image,
    Finset.mem_product, Finset.mem_powerset, Finset.mem_erase, Prod.exists]
  refine ⟨s, m, ⟨Finset.mem_powerset.mp hs, ?_, ?_⟩, hm.symm⟩
  · have := hm ▸ ne_zero_of_mem_smoothNumbers hn₂
    simp only [ne_eq, _root_.mul_eq_zero, sq_eq_zero_iff, not_or] at this
    exact this.1
  · rw [Nat.lt_succ_iff, le_sqrt']
    refine LE.le.trans ?_ (hm ▸ hn₁)
    nth_rw 1 [← mul_one (m ^ 2)]
    gcongr
    exact Finset.one_le_prod' fun p hp ↦
      (prime_of_mem_primesBelow <| Finset.mem_powerset.mp hs hp).one_le

/-- The cardinality of the set of `k`-smooth numbers `≤ N` is bounded by `2^π(k-1) * √N`. -/
/-
**Nat.smoothNumbersUpTo_card_le** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：smoothNumbersUpTo_card_le (N k : Nat) : #(smoothNumbersUpTo N k) <= 2 ^ #k
.primesBelow * N.sqrt
参数：N k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_product`：card_product (s : Finset α) (t : Finset β) : card (
s ×ˢ t) = card s * card t
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.card_powerset`：card_powerset (s : Finset α) : card (powerset s) =
 2 ^ card s
· 使用定理 `Finset.card_erase_of_mem`：card_erase_of_mem : a in s -> #(s.erase a) = #
s - 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
· 使用定理 `Nat.succ_sub_succ_eq_sub`：∀ (n m : ℕ), n.succ - m.succ = n - m
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用引理 `Nat.smoothNumbersUpTo_subset_image`：smoothNumbersUpTo_subset_image (N k 
: Nat) : smoothNumbersUpTo N k subseteq Finset.image (fun (s, m) => m ^ 2 * (s.p
rod id)) (k.primesBelow.…
· 使用定理 `Finset.card_image_le`：card_image_le [DecidableEq β] : #(s.image f) <= #s

--- 原说明 ---
The cardinality of the set of `k`-smooth numbers `≤ N` is bounded by `2^π(k-1) *
 √N`.
-/
lemma smoothNumbersUpTo_card_le (N k : ℕ) :
    #(smoothNumbersUpTo N k) ≤ 2 ^ #k.primesBelow * N.sqrt := by
  convert! (Finset.card_le_card <| smoothNumbersUpTo_subset_image N k).trans <| Finset.card_image_le
  simp only [Finset.card_product, Finset.card_powerset, Finset.mem_range, zero_lt_succ,
    Finset.card_erase_of_mem, Finset.card_range, succ_sub_succ_eq_sub, Nat.sub_zero]

/-- The set of `k`-rough numbers `≤ N` can be written as the union of the sets of multiples `≤ N`
of primes `k ≤ p ≤ N`. -/
/-
**Nat.roughNumbersUpTo_eq_biUnion** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：roughNumbersUpTo_eq_biUnion (N k) : roughNumbersUpTo N k = ((N + 1).primes
Below \ k.primesBelow).biUnion fun p => {m in Finset.range (N + 1) | m != 0 ∧ p 
∣ m}
参数：N k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Decidable.not_or_of_imp`：∀ {a b : Prop} [Decidable a], (a → b) → ¬a ∨ b
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n

--- 原说明 ---
The set of `k`-rough numbers `≤ N` can be written as the union of the sets of mu
ltiples `≤ N`
of primes `k ≤ p ≤ N`.
-/
lemma roughNumbersUpTo_eq_biUnion (N k) :
    roughNumbersUpTo N k =
      ((N + 1).primesBelow \ k.primesBelow).biUnion
        fun p ↦ {m ∈ Finset.range (N + 1) | m ≠ 0 ∧ p ∣ m} := by
  ext m
  simp only [roughNumbersUpTo, mem_smoothNumbers_iff_forall_le, not_and, not_forall,
    not_lt, exists_prop, Finset.mem_range, Finset.mem_filter,
    Finset.mem_biUnion, Finset.mem_sdiff, mem_primesBelow,
    show ∀ P Q : Prop, P ∧ (P → Q) ↔ P ∧ Q by tauto]
  simp_rw [← exists_and_left, ← not_lt]
  refine exists_congr fun p ↦ ?_
  have H : m ≠ 0 → p ∣ m → ¬ m < p :=
    fun h₁ h₂ ↦ not_lt.mpr <| le_of_dvd (Nat.pos_of_ne_zero h₁) h₂
  grind

/-- The cardinality of the set of `k`-rough numbers `≤ N` is bounded by the sum of `⌊N/p⌋`
over the primes `k ≤ p ≤ N`. -/
/-
**Nat.roughNumbersUpTo_card_le** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：roughNumbersUpTo_card_le (N k : Nat) : #(roughNumbersUpTo N k) <= ((N + 1)
.primesBelow \ k.primesBelow).sum (fun p => N / p)
参数：N k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.roughNumbersUpTo_eq_biUnion`：roughNumbersUpTo_eq_biUnion (N k) : rou
ghNumbersUpTo N k = ((N + 1).primesBelow \ k.primesBelow).biUnion fun p => {m in
 Finset.range (N + 1)…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finset.card_biUnion_le`：card_biUnion_le [DecidableEq M] {s : Finset ι} {
t : ι -> Finset M} : #(s.biUnion t) <= ∑ a in s, #(t a)
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用引理 `Nat.card_multiples'`：card_multiples' (N n : Nat) : #{k in range N.succ |
 k != 0 ∧ n ∣ k} = N / n

--- 原说明 ---
The cardinality of the set of `k`-rough numbers `≤ N` is bounded by the sum of `
⌊N/p⌋`
over the primes `k ≤ p ≤ N`.
-/
lemma roughNumbersUpTo_card_le (N k : ℕ) :
    #(roughNumbersUpTo N k) ≤ ((N + 1).primesBelow \ k.primesBelow).sum (fun p ↦ N / p) := by
  rw [roughNumbersUpTo_eq_biUnion]
  exact Finset.card_biUnion_le.trans <| Finset.sum_le_sum fun p _ ↦ (card_multiples' N p).le

end Nat

