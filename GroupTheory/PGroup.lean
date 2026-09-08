/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Thomas Browning, Snir Broshi
-/
module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# p-groups

This file contains a proof that if `G` is a `p`-group acting on a finite set `α`,
then the number of fixed points of the action is congruent mod `p` to the cardinality of `α`.
It also contains proofs of some corollaries of this lemma about existence of fixed points.
-/

@[expose] public section

open Fintype MulAction

variable (p : ℕ) (G : Type*) [Group G]

/-- A p-group is a group in which the order of every element is a power of `p`. -/
/-
**IsPGroup** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsPGroup : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A p-group is a group in which the order of every element is a power of `p`.
-/
def IsPGroup : Prop :=
  ∀ g : G, ∃ k : ℕ, g ^ p ^ k = 1

variable {p} {G}

namespace IsPGroup

/-
**IsPGroup._root_.isPGroup_iff_pow_pow_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `IsPGrou
p`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.isPGroup_iff_pow_pow_eq_one : IsPGroup p G ↔ ∀ g : G, ∃ k, g ^ p ^ k = 1 :=
  .rfl

alias ⟨exists_pow_pow_eq_one, _⟩ := isPGroup_iff_pow_pow_eq_one
/-
**IsPGroup._root_.isPGroup_iff_orderOf_dvd_pow** 是 Mathlib 中的一个定理，位于命名空间 `IsPGro
up`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.isPGroup_iff_orderOf_dvd_pow : IsPGroup p G ↔ ∀ g : G, ∃ k, orderOf g ∣ p ^ k := by
  simp_rw [isPGroup_iff_pow_pow_eq_one, orderOf_dvd_iff_pow_eq_one]

alias ⟨exists_orderOf_dvd_pow, _⟩ := isPGroup_iff_orderOf_dvd_pow
/-
**IsPGroup.iff_orderOf** 是 Mathlib 中的一个定理，位于命名空间 `IsPGroup`。
形式化陈述：iff_orderOf [Fact p.Prime] : IsPGroup p G ↔ forall g : G, exists k, orderO
f g = p ^ k
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.dvd_prime_pow`：dvd_prime_pow {p : Nat} (pp : Prime p) {m i : Nat} : 
i ∣ p ^ m ↔ exists k <= m, i = p ^ k
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
-/
theorem iff_orderOf [Fact p.Prime] : IsPGroup p G ↔ ∀ g : G, ∃ k, orderOf g = p ^ k := by
  simp_rw [isPGroup_iff_orderOf_dvd_pow, Nat.dvd_prime_pow Fact.out]
  exact forall_congr' fun g ↦ ⟨by grind, .imp <| by grind⟩

alias ⟨exists_orderOf_eq_pow, _⟩ := iff_orderOf
/-
**IsPGroup.of_card_dvd_pow** 是 Mathlib 中的一个定理，位于命名空间 `IsPGroup`。
形式化陈述：of_card_dvd_pow {n : Nat} (hG : Nat.card G ∣ p ^ n) : IsPGroup p G
参数：hG : Nat.card G ∣ p ^ n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `orderOf_dvd_iff_pow_eq_one`：orderOf_dvd_iff_pow_eq_one {n : Nat} : order
Of x ∣ n ↔ x ^ n = 1
· 使用引理 `Mathlib.Tactic.GCongr.rel_imp_rel`：rel_imp_rel (h₁ : r c a) (h₂ : r b d)
 : r a b -> r c d
· 使用定理 `instIsTransDvd`：∀ {α : Type u_1} [inst : Semigroup α], IsTrans α Dvd.dvd
· 使用定理 `dvd_refl`：dvd_refl (a : α) : a ∣ a
· 使用定理 `orderOf_dvd_natCard`：orderOf_dvd_natCard {G : Type*} [Group G] (x : G) :
 orderOf x ∣ Nat.card G
-/
theorem of_card_dvd_pow {n : ℕ} (hG : Nat.card G ∣ p ^ n) : IsPGroup p G := by
  refine fun g ↦ ⟨n, ?_⟩
  grw [← orderOf_dvd_iff_pow_eq_one, ← hG, orderOf_dvd_natCard]
/-
**IsPGroup._root_.isPGroup_iff_card_dvd_pow** 是 Mathlib 中的一个定理，位于命名空间 `IsPGroup`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.isPGroup_iff_card_dvd_pow [Finite G] : IsPGroup p G ↔ ∃ n, Nat.card G ∣ p ^ n := by
  refine ⟨fun h ↦ ?_, fun ⟨n, hn⟩ ↦ of_card_dvd_pow hn⟩
  rcases eq_or_ne p 0 with rfl | hp
  · exact ⟨1, by simp⟩
  refine ⟨Nat.card G, Nat.dvd_pow_self_iff NeZero.out hp |>.mpr fun q hq ↦ ?_⟩
  have ⟨hqp, hqdvd, _⟩ := Nat.mem_primeFactors.mp hq
  have ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' q (hp := ⟨hqp⟩) hqdvd
  have ⟨k, hk⟩ := h.exists_orderOf_dvd_pow g
  exact Nat.mem_primeFactors.mpr ⟨hqp, hqp.dvd_of_dvd_pow <| hg ▸ hk, hp⟩

alias ⟨exists_card_dvd_pow, _⟩ := isPGroup_iff_card_dvd_pow
/-
**IsPGroup.dvd_orderOf** 是 Mathlib 中的一个定理，位于命名空间 `IsPGroup`。
形式化陈述：dvd_orderOf [Fact p.Prime] (hG : IsPGroup p G) {g : G} (hg : g != 1) : p ∣
 orderOf g
参数：hG : IsPGroup p G；hg : g != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPGroup.exists_orderOf_eq_pow`：∀ {p : ℕ} {G : Type u_1} [inst : Group G
] [Fact (Nat.Prime p)], IsPGroup p G → ∀ (g : G), ∃ k, orderOf g = p ^ k
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `dvd_pow_self`：dvd_pow_self (a : α) {n : Nat} (hn : n != 0) : a ∣ a ^ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `orderOf_eq_one_iff`：orderOf_eq_one_iff : orderOf x = 1 ↔ x = 1
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
-/
theorem dvd_orderOf [Fact p.Prime] (hG : IsPGroup p G) {g : G} (hg : g ≠ 1) : p ∣ orderOf g := by
  have ⟨k, hk⟩ := hG.exists_orderOf_eq_pow g
  rw [hk]
  refine dvd_pow_self _ fun hk0 ↦ hg ?_
  rw [← orderOf_eq_one_iff, hk, hk0, pow_zero]
/-
**IsPGroup.of_card** 是 Mathlib 中的一个定理，位于命名空间 `IsPGroup`。
形式化陈述：of_card {n : Nat} (hG : Nat.card G = p ^ n) : IsPGroup p G
参数：hG : Nat.card G = p ^ n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPGroup.of_card_dvd_pow`：of_card_dvd_pow {n : Nat} (hG : Nat.card G ∣ p
 ^ n) : IsPGroup p G
· 使用定理 `Eq.dvd`：∀ {α : Type u_1} [inst : Monoid α] {a b : α}, a = b → a ∣ b
-/
theorem of_card {n : ℕ} (hG : Nat.card G = p ^ n) : IsPGroup p G :=
  of_card_dvd_pow hG.dvd

variable (p G) in
/-
**IsPGroup.of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `IsPGroup`。
形式化陈述：of_subsingleton [Subsingleton G] : IsPGroup p G
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPGroup.of_card`：of_card {n : Nat} (hG : Nat.card G = p ^ n) : IsPGroup
 p G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_unique`：card_unique [Nonempty α] [Subsingleton α] : Nat.card α 
= 1
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem of_subsingleton [Subsingleton G] : IsPGroup p G :=
  of_card (n := 0) (by simp)
/-
**IsPGroup.of_bot** 是 Mathlib 中的一个定理，位于命名空间 `IsPGroup`。
形式化陈述：of_bot : IsPGroup p (⊥ : Subgroup G)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPGroup.of_subsingleton`：of_subsingleton [Subsingleton G] : IsPGroup p 
G
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem of_bot : IsPGroup p (⊥ : Subgroup G) :=
  .of_subsingleton p _

variable (G) in
@[simp]
/-
**IsPGroup.zero** 是 Mathlib 中的一个定理，位于命名空间 `IsPGroup`。
形式化陈述：∀ (G : Type u_1) [inst : Group G], IsPGroup 0 G
参数：G : Type u_1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem zero : IsPGroup 0 G :=
  fun g ↦ ⟨1, by simp⟩

@[simp]
/-
**IsPGroup._root_.isPGroup_one_iff_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `IsPGr
oup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.isPGroup_one_iff_subsingleton : IsPGroup 1 G ↔ Subsingleton G := by
  refine ⟨?_, fun h ↦ .of_subsingleton 1 G⟩
  simpa [isPGroup_iff_pow_pow_eq_one] using subsingleton_of_forall_eq 1
/-
**IsPGroup.card** 是 Mathlib 中的一个定理，位于命名空间 `IsPGroup`。
形式化陈述：∀ {G : Type u_1} [inst : Group G], IsPGroup (Nat.card G) G
参数：Nat.card G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `pow_card_eq_one'`：pow_card_eq_one' {G : Type*} [Group G] {x : G} : x ^ N
at.card G = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem card : IsPGroup (Nat.card G) G :=
  fun g ↦ ⟨1, by simp⟩

@[gcongr]
/-
**IsPGroup.mono** 是 Mathlib 中的一个定理，位于命名空间 `IsPGroup`。
形式化陈述：∀ {p : ℕ} {G : Type u_1} [inst : Group G] {q : ℕ}, p ∣ q → IsPGroup p G → 
IsPGroup q G
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isPGroup_iff_orderOf_dvd_pow`：∀ {p : ℕ} {G : Type u_1} [inst : Group G],
 IsPGroup p G ↔ ∀ (g : G), ∃ k, orderOf g ∣ p ^ k
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `pow_dvd_pow_of_dvd`：pow_dvd_pow_of_dvd (h : a ∣ b) (n : Nat) : a ^ n ∣ b
 ^ n
-/
protected theorem mono {q : ℕ} (hpq : p ∣ q) (hp : IsPGroup p G) : IsPGroup q G := by
  rw [isPGroup_iff_orderOf_dvd_pow] at hp ⊢
  exact fun g ↦ (hp g).imp fun k hk ↦ hk.trans <| pow_dvd_pow_of_dvd hpq k
/-
**IsPGroup.of_pow** 是 Mathlib 中的一个定理，位于命名空间 `IsPGroup`。
形式化陈述：of_pow {n : Nat} (h : IsPGroup (p ^ n) G) : IsPGroup p G
参数：h : IsPGroup (p ^ n) G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp'`：∀ {α : Sort u_2} {p : α → Prop} {β : Sort u_1} {q : β → Pro
p} (f : α → β),   (∀ (a : α), p a → q (f a)) → (∃ a, p a) → ∃ b, q b
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
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem of_pow {n : ℕ} (h : IsPGroup (p ^ n) G) : IsPGroup p G :=
  fun g ↦ (h g).imp' (n * ·) <| by simp [pow_mul]
/-
**IsPGroup.iff_card** 是 Mathlib 中的一个定理，位于命名空间 `IsPGroup`。
形式化陈述：iff_card [Fact p.Prime] [Finite G] : IsPGroup p G ↔ exists n : Nat, Nat.ca
rd G = p ^ n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.dvd_prime_pow`：dvd_prime_pow {p : Nat} (pp : Prime p) {m i : Nat} : 
i ∣ p ^ m ↔ exists k <= m, i = p ^ k
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem iff_card [Fact p.Prime] [Finite G] : IsPGroup p G ↔ ∃ n : ℕ, Nat.card G = p ^ n := by
  simp_rw [isPGroup_iff_card_dvd_pow, Nat.dvd_prime_pow Fact.out]
  exact ⟨fun ⟨n, k, _, hk⟩ ↦ ⟨k, hk⟩, fun ⟨n, hn⟩ ↦ ⟨n, n, le_rfl, hn⟩⟩

alias ⟨exists_card_eq, _⟩ := iff_card
/-
**IsPGroup._root_.isPGroup_iff_exists_orderOf_dvd_pow** 是 Mathlib 中的一个定理，位于命名空间 
`IsPGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.isPGroup_iff_exists_orderOf_dvd_pow [Finite G] :
    IsPGroup p G ↔ ∃ k, ∀ g : G, orderOf g ∣ p ^ k := by
  refine isPGroup_iff_orderOf_dvd_pow.trans ⟨fun h ↦ ?_, fun ⟨k, hk⟩ ↦ fun g ↦ ⟨k, hk g⟩⟩
  choose k hk using h
  have := Fintype.ofFinite G
  have ⟨g, _, hg⟩ := Finset.exists_max_image .univ k Finset.univ_nonempty
  refine ⟨k g, fun g' ↦ ?_⟩
  grw [← Nat.pow_dvd_pow p <| hg g' <| Finset.mem_univ g']
  exact hk g'
/-
**IsPGroup._root_.isPGroup_iff_exists_pow_pow_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `
IsPGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.isPGroup_iff_exists_pow_pow_eq_one [Finite G] :
    IsPGroup p G ↔ ∃ k, ∀ g : G, g ^ p ^ k = 1 := by
  simp_rw [isPGroup_iff_exists_orderOf_dvd_pow, orderOf_dvd_iff_pow_eq_one]
/-
**IsPGroup.of_exponent_dvd_pow** 是 Mathlib 中的一个定理，位于命名空间 `IsPGroup`。
形式化陈述：of_exponent_dvd_pow {n : Nat} (h : Monoid.exponent G ∣ p ^ n) : IsPGroup p
 G
参数：h : Monoid.exponent G ∣ p ^ n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Monoid.exponent_dvd_iff_forall_pow_eq_one`：exponent_dvd_iff_forall_pow_e
q_one {n : Nat} : exponent G ∣ n ↔ forall g : G, g ^ n = 1
-/
theorem of_exponent_dvd_pow {n : ℕ} (h : Monoid.exponent G ∣ p ^ n) : IsPGroup p G :=
  fun g ↦ ⟨n, Monoid.exponent_dvd_iff_forall_pow_eq_one.mp h g⟩
/-
**IsPGroup._root_.isPGroup_iff_exponent_dvd_pow** 是 Mathlib 中的一个定理，位于命名空间 `IsPGr
oup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.isPGroup_iff_exponent_dvd_pow [Finite G] :
    IsPGroup p G ↔ ∃ n, Monoid.exponent G ∣ p ^ n := by
  simp_rw [isPGroup_iff_exists_orderOf_dvd_pow, Monoid.exponent_dvd]

alias ⟨exists_exponent_dvd_pow, _⟩ := isPGroup_iff_exponent_dvd_pow
/-
**IsPGroup._root_.isPGroup_iff_exponent_eq_pow** 是 Mathlib 中的一个定理，位于命名空间 `IsPGro
up`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.isPGroup_iff_exponent_eq_pow [Finite G] [Fact p.Prime] :
    IsPGroup p G ↔ ∃ n, Monoid.exponent G = p ^ n := by
  simp_rw [isPGroup_iff_exponent_dvd_pow, Nat.dvd_prime_pow Fact.out]
  exact ⟨fun ⟨n, k, _, hk⟩ ↦ ⟨k, hk⟩, fun ⟨n, hn⟩ ↦ ⟨n, n, le_rfl, hn⟩⟩

alias ⟨exists_exponent_eq_pow, _⟩ := isPGroup_iff_exponent_eq_pow
/-
**IsPGroup._root_.isPGroup_iff_isPGroup_prod_primeFactors** 是 Mathlib 中的一个定理，位于命
名空间 `IsPGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.isPGroup_iff_isPGroup_prod_primeFactors (h : p ≠ 0) :
    IsPGroup p G ↔ IsPGroup (p.primeFactors.prod id) G :=
  ⟨(.of_pow <| ·.mono <| p.dvd_prod_primeFactors_pow_self h), .mono p.prod_primeFactors_dvd⟩
/-
**IsPGroup._root_.isPGroup_iff_primeFactors_card_subset** 是 Mathlib 中的一个定理，位于命名空
间 `IsPGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.isPGroup_iff_primeFactors_card_subset [Finite G] (h : p ≠ 0) :
    IsPGroup p G ↔ (Nat.card G).primeFactors ⊆ p.primeFactors := by
  refine isPGroup_iff_card_dvd_pow.trans ⟨fun ⟨n, hn⟩ ↦ ?_, fun hG ↦ ?_⟩
  · rcases eq_or_ne n 0 with (rfl | hn0)
    · simp_all
    grw [← Nat.primeFactors_pow p hn0, Nat.primeFactors_mono hn <| pow_ne_zero n h]
  · refine ⟨Nat.card G, Nat.dvd_prod_primeFactors_pow_self NeZero.out |>.trans ?_⟩
    grw [Finset.prod_dvd_prod_of_subset _ _ (·) hG, p.prod_primeFactors_dvd]

section GIsPGroup

variable (hG : IsPGroup p G)
include hG

/-
**IsPGroup.of_injective** 是 Mathlib 中的一个定理，位于命名空间 `IsPGroup`。
形式化陈述：of_injective {H : Type*} [Group H] (ϕ : H ->* G) (hϕ : Function.Injective 
ϕ) : IsPGroup p H
参数：ϕ : H ->* G；hϕ : Function.Injective ϕ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MonoidHom.map_pow`：∀ {M : Type u_4} {N : Type u_5} [inst : Monoid M] [in
st_1 : Monoid N] (f : M →* N) (a : M) (n : ℕ), f (a ^ n) = f a ^ n
· 使用定理 `MonoidHom.map_one`：∀ {M : Type u_4} {N : Type u_5} [inst : MulOne M] [in
st_1 : MulOne N] (f : M →* N), f 1 = 1
-/
theorem of_injective {H : Type*} [Group H] (ϕ : H →* G) (hϕ : Function.Injective ϕ) :
    IsPGroup p H := by
  simp_rw [IsPGroup, ← hϕ.eq_iff, ϕ.map_pow, ϕ.map_one]
  exact fun h => hG (ϕ h)
/-
**IsPGroup.to_subgroup** 是 Mathlib 中的一个定理，位于命名空间 `IsPGroup`。
形式化陈述：to_subgroup (H : Subgroup G) : IsPGroup p H
参数：H : Subgroup G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPGroup.of_injective`：of_injective {H : Type*} [Group H] (ϕ : H ->* G) 
(hϕ : Function.Injective ϕ) : IsPGroup p H
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
theorem to_subgroup (H : Subgroup G) : IsPGroup p H :=
  hG.of_injective H.subtype Subtype.coe_injective
/-
**IsPGroup.of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `IsPGroup`。
形式化陈述：of_surjective {H : Type*} [Group H] (ϕ : G ->* H) (hϕ : Function.Surjectiv
e ϕ) : IsPGroup p H
参数：ϕ : G ->* H；hϕ : Function.Surjective ϕ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidHom.map_pow`：∀ {M : Type u_4} {N : Type u_5} [inst : Monoid M] [in
st_1 : Monoid N] (f : M →* N) (a : M) (n : ℕ), f (a ^ n) = f a ^ n
· 使用定理 `MonoidHom.map_one`：∀ {M : Type u_4} {N : Type u_5} [inst : MulOne M] [in
st_1 : MulOne N] (f : M →* N), f 1 = 1
-/
theorem of_surjective {H : Type*} [Group H] (ϕ : G →* H) (hϕ : Function.Surjective ϕ) :
    IsPGroup p H := by
  refine fun h => Exists.elim (hϕ h) fun g hg => Exists.imp (fun k hk => ?_) (hG g)
  rw [← hg, ← ϕ.map_pow, hk, ϕ.map_one]
/-
**IsPGroup.to_quotient** 是 Mathlib 中的一个定理，位于命名空间 `IsPGroup`。
形式化陈述：to_quotient (H : Subgroup G) [H.Normal] : IsPGroup p (G ⧸ H)
参数：H : Subgroup G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPGroup.of_surjective`：of_surjective {H : Type*} [Group H] (ϕ : G ->* H
) (hϕ : Function.Surjective ϕ) : IsPGroup p H
· 使用定理 `Quotient.mk''_surjective`：∀ {α : Sort u_1} {s₁ : Setoid α}, Function.Sur
jective Quotient.mk''
-/
theorem to_quotient (H : Subgroup G) [H.Normal] : IsPGroup p (G ⧸ H) :=
  hG.of_surjective (QuotientGroup.mk' H) Quotient.mk''_surjective
/-
**IsPGroup.of_equiv** 是 Mathlib 中的一个定理，位于命名空间 `IsPGroup`。
形式化陈述：of_equiv {H : Type*} [Group H] (ϕ : G ≃* H) : IsPGroup p H
参数：ϕ : G ≃* H。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPGroup.of_surjective`：of_surjective {H : Type*} [Group H] (ϕ : G ->* H
) (hϕ : Function.Surjective ϕ) : IsPGroup p H
· 使用定理 `MulEquiv.surjective`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [ins
t_1 : Mul N] (e : M ≃* N), Function.Surjective ⇑e
-/
theorem of_equiv {H : Type*} [Group H] (ϕ : G ≃* H) : IsPGroup p H :=
  hG.of_surjective ϕ.toMonoidHom ϕ.surjective
/-
**IsPGroup.isOfFinOrder** 是 Mathlib 中的一个定理，位于命名空间 `IsPGroup`。
形式化陈述：isOfFinOrder (hp : p != 0) (g : G) : IsOfFinOrder g
参数：hp : p != 0；g : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isOfFinOrder_iff_pow_eq_one`：isOfFinOrder_iff_pow_eq_one : IsOfFinOrder 
x ↔ exists n, 0 < n ∧ x ^ n = 1
· 使用定理 `Ne.pos`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_1 : Zero 
α] [IsBotZeroClass α], a ≠ 0 → 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
-/
theorem isOfFinOrder (hp : p ≠ 0) (g : G) : IsOfFinOrder g :=
  hG g |>.elim (isOfFinOrder_iff_pow_eq_one.mpr ⟨_, pow_ne_zero · hp |>.pos, ·⟩)
/-
**IsPGroup.orderOf_coprime** 是 Mathlib 中的一个定理，位于命名空间 `IsPGroup`。
形式化陈述：orderOf_coprime {n : Nat} (hn : p.Coprime n) (g : G) : (orderOf g).Coprime
 n
参数：hn : p.Coprime n；g : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Coprime.coprime_dvd_left`：∀ {m k n : ℕ}, m ∣ k → k.Coprime n → m.Cop
rime n
· 使用定理 `orderOf_dvd_of_pow_eq_one`：orderOf_dvd_of_pow_eq_one (h : x ^ n = 1) : o
rderOf x ∣ n
· 使用定理 `Nat.Coprime.pow_left`：∀ {m k : ℕ} (n : ℕ), m.Coprime k → (m ^ n).Coprime
 k
-/
theorem orderOf_coprime {n : ℕ} (hn : p.Coprime n) (g : G) : (orderOf g).Coprime n :=
  let ⟨k, hk⟩ := hG g
  (hn.pow_left k).coprime_dvd_left (orderOf_dvd_of_pow_eq_one hk)

/-- If `gcd(p,n) = 1`, then the `n`th power map is a bijection. -/
/-
**IsPGroup.powEquiv** 是 Mathlib 中的一个定义，位于命名空间 `IsPGroup`。
形式化陈述：powEquiv {n : Nat} (hn : p.Coprime n) : G ≃ G
参数：hn : p.Coprime n。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Subgroup.mem_zpowers`：mem_zpowers (g : G) : g in zpowers g

--- 原说明 ---
If `gcd(p,n) = 1`, then the `n`th power map is a bijection.
-/
noncomputable def powEquiv {n : ℕ} (hn : p.Coprime n) : G ≃ G :=
  let h : ∀ g : G, (Nat.card (Subgroup.zpowers g)).Coprime n := fun g =>
    (Nat.card_zpowers g).symm ▸ hG.orderOf_coprime hn g
  { toFun := (· ^ n)
    invFun := fun g => (powCoprime (h g)).symm ⟨g, Subgroup.mem_zpowers g⟩
    left_inv := fun g =>
      Subtype.ext_iff.1 <|
        (powCoprime (h (g ^ n))).left_inv
          ⟨g, _, Subtype.ext_iff.1 <| (powCoprime (h g)).left_inv ⟨g, Subgroup.mem_zpowers g⟩⟩
    right_inv := fun g =>
      Subtype.ext_iff.1 <| (powCoprime (h g)).right_inv ⟨g, Subgroup.mem_zpowers g⟩ }

@[simp]
/-
**IsPGroup.powEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `IsPGroup`。
形式化陈述：powEquiv_apply {n : Nat} (hn : p.Coprime n) (g : G) : hG.powEquiv hn g = g
 ^ n
参数：hn : p.Coprime n；g : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem powEquiv_apply {n : ℕ} (hn : p.Coprime n) (g : G) : hG.powEquiv hn g = g ^ n :=
  rfl

@[simp]
/-
**IsPGroup.powEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `IsPGroup`。
形式化陈述：powEquiv_symm_apply {n : Nat} (hn : p.Coprime n) (g : G) : (hG.powEquiv hn
).symm g = g ^ (orderOf g).gcdB n
参数：hn : p.Coprime n；g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.card_zpowers`：Nat.card_zpowers : Nat.card (zpowers a) = orderOf a
-/
theorem powEquiv_symm_apply {n : ℕ} (hn : p.Coprime n) (g : G) :
    (hG.powEquiv hn).symm g = g ^ (orderOf g).gcdB n := by rw [← Nat.card_zpowers]; rfl

variable [hp : Fact p.Prime]

/-- If `p ∤ n`, then the `n`th power map is a bijection. -/
/-
**IsPGroup.powEquiv'** 是 Mathlib 中的一个缩写定义，位于命名空间 `IsPGroup`。
形式化陈述：powEquiv' {n : Nat} (hn : ¬p ∣ n) : G ≃ G
参数：hn : ¬p ∣ n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `p ∤ n`, then the `n`th power map is a bijection.
-/
noncomputable abbrev powEquiv' {n : ℕ} (hn : ¬p ∣ n) : G ≃ G :=
  powEquiv hG (hp.out.coprime_iff_not_dvd.mpr hn)
/-
**IsPGroup.index** 是 Mathlib 中的一个定理，位于命名空间 `IsPGroup`。
形式化陈述：index (H : Subgroup G) [H.FiniteIndex] : exists n : Nat, H.index = p ^ n
参数：H : Subgroup G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsPGroup.iff_card`：iff_card [Fact p.Prime] [Finite G] : IsPGroup p G ↔ e
xists n : Nat, Nat.card G = p ^ n
· 使用定理 `IsPGroup.to_quotient`：to_quotient (H : Subgroup G) [H.Normal] : IsPGroup
 p (G ⧸ H)
· 使用定理 `Nat.dvd_prime_pow`：dvd_prime_pow {p : Nat} (pp : Prime p) {m i : Nat} : 
i ∣ p ^ m ↔ exists k <= m, i = p ^ k
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subgroup.index_eq_card`：index_eq_card : H.index = Nat.card (G ⧸ H)
· 使用定理 `Subgroup.index_dvd_of_le`：index_dvd_of_le (h : H <= K) : K.index ∣ H.ind
ex
· 使用定理 `Subgroup.normalCore_le`：normalCore_le (H : Subgroup G) : H.normalCore <=
 H
-/
theorem index (H : Subgroup G) [H.FiniteIndex] : ∃ n : ℕ, H.index = p ^ n := by
  obtain ⟨n, hn⟩ := iff_card.mp (hG.to_quotient H.normalCore)
  obtain ⟨k, _, hk2⟩ :=
    (Nat.dvd_prime_pow hp.out).mp
      ((congr_arg _ (H.normalCore.index_eq_card.trans hn)).mp
        (Subgroup.index_dvd_of_le H.normalCore_le))
  exact ⟨k, hk2⟩
/-
**IsPGroup.card_eq_or_dvd** 是 Mathlib 中的一个定理，位于命名空间 `IsPGroup`。
形式化陈述：card_eq_or_dvd : Nat.card G = 1 ∨ p ∣ Nat.card G
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finite_or_infinite`：finite_or_infinite (α : Sort*) : Finite α ∨ Infinite
 α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsPGroup.iff_card`：iff_card [Fact p.Prime] [Finite G] : IsPGroup p G ↔ e
xists n : Nat, Nat.card G = p ^ n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `Nat.card_eq_zero_of_infinite`：∀ {α : Type u_1} [Infinite α], Nat.card α 
= 0
-/
theorem card_eq_or_dvd : Nat.card G = 1 ∨ p ∣ Nat.card G := by
  cases finite_or_infinite G
  · obtain ⟨n, hn⟩ := iff_card.mp hG
    rw [hn]
    rcases n with - | n
    · exact Or.inl rfl
    · exact Or.inr ⟨p ^ n, by rw [pow_succ']⟩
  · rw [Nat.card_eq_zero_of_infinite]
    exact Or.inr ⟨0, rfl⟩
/-
**IsPGroup.nontrivial_iff_card** 是 Mathlib 中的一个定理，位于命名空间 `IsPGroup`。
形式化陈述：nontrivial_iff_card [Finite G] : Nontrivial G ↔ exists n > 0, Nat.card G =
 p ^ n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsPGroup.iff_card`：iff_card [Fact p.Prime] [Finite G] : IsPGroup p G ↔ e
xists n : Nat, Nat.card G = p ^ n
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Finite.one_lt_card`：one_lt_card [Finite α] [h : Nontrivial α] : 1 < Nat.
card α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Finite.one_lt_card_iff_nontrivial`：one_lt_card_iff_nontrivial [Finite α]
 : 1 < Nat.card α ↔ Nontrivial α
· 使用定理 `one_lt_pow₀`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preo
rder M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   1 < a → ∀ {n : ℕ}, n ≠ 
0…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem nontrivial_iff_card [Finite G] : Nontrivial G ↔ ∃ n > 0, Nat.card G = p ^ n :=
  ⟨fun hGnt =>
    let ⟨k, hk⟩ := iff_card.1 hG
    ⟨k,
      Nat.pos_of_ne_zero fun hk0 => by
        rw [hk0, pow_zero] at hk; exact Finite.one_lt_card.ne' hk,
      hk⟩,
    fun ⟨_, hk0, hk⟩ =>
    Finite.one_lt_card_iff_nontrivial.1 <|
      hk.symm ▸ one_lt_pow₀ (Fact.out (p := p.Prime)).one_lt (ne_of_gt hk0)⟩

variable {α : Type*} [MulAction G α]
/-
**IsPGroup.card_orbit** 是 Mathlib 中的一个定理，位于命名空间 `IsPGroup`。
形式化陈述：card_orbit (a : α) [Finite (orbit G a)] : exists n : Nat, Nat.card (orbit 
G a) = p ^ n
参数：a : α；orbit G a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_equiv`：Finite.of_equiv (α : Sort*) [h : Finite α] (f : α ≃ β) 
: Finite β
· 使用定理 `Subgroup.finiteIndex_of_finite_quotient`：finiteIndex_of_finite_quotient 
[Finite (G ⧸ H)] : FiniteIndex H
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
· 使用定理 `IsPGroup.index`：index (H : Subgroup G) [H.FiniteIndex] : exists n : Nat,
 H.index = p ^ n
-/
theorem card_orbit (a : α) [Finite (orbit G a)] : ∃ n : ℕ, Nat.card (orbit G a) = p ^ n := by
  let ϕ := orbitEquivQuotientStabilizer G a
  have := Finite.of_equiv (orbit G a) ϕ
  have := (stabilizer G a).finiteIndex_of_finite_quotient
  rw [Nat.card_congr ϕ]
  exact hG.index (stabilizer G a)

variable (α) [Finite α]

/-- If `G` is a `p`-group acting on a finite set `α`, then the number of fixed points
  of the action is congruent mod `p` to the cardinality of `α` -/
/-
**IsPGroup.card_modEq_card_fixedPoints** 是 Mathlib 中的一个定理，位于命名空间 `IsPGroup`。
形式化陈述：card_modEq_card_fixedPoints : Nat.card α ≡ Nat.card (fixedPoints G α) [MOD
 p]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `Fintype.card_congr`：card_congr {α β} [Fintype α] [Fintype β] (f : α ≃ β)
 : card α = card β
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Fintype.card_sigma`：∀ {ι : Type u_8} {α : ι → Type u_7} [inst : Fintype 
ι] [inst_1 : (i : ι) → Fintype (α i)],   Fintype.card (Sigma α) = ∑ i, Fintype.c
ard (α i…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZMod.natCast_eq_natCast_iff`：natCast_eq_natCast_iff (a b c : Nat) : (a :
 ZMod c) = (b : ZMod c) ↔ a ≡ b [MOD c]
· 使用引理 `Nat.cast_sum`：cast_sum [AddCommMonoidWithOne R] (s : Finset ι) (f : ι ->
 Nat) : ↑(∑ x in s, f x : Nat) = ∑ x in s, (f x : R)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fintype.card_congr'`：card_congr' {α β} [Fintype α] [Fintype β] (h : α = 
β) : card α = card β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_bij_ne_zero`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_4} [
inst : AddCommMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M}   {g : κ → M} 
(i : (a : ι)…
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MulAction.mem_fixedPoints'`：mem_fixedPoints' {a : α} : a in fixedPoints 
M α ↔ forall a', a' in orbit M a -> a' = a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Quotient.exact'`：exact' {a b : α} : (Quotient.mk'' a : Quotient s₁) = Qu
otient.mk'' b -> s₁ a b
· 使用定理 `Quotient.inductionOn'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁
 → Prop} (q : Quotient s₁), (∀ (a : α), p (Quotient.mk'' a)) → p q
· 使用定理 `IsPGroup.card_orbit`：card_orbit (a : α) [Finite (orbit G a)] : exists n 
: Nat, Nat.card (orbit G a) = p ^ n
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
（共 41 条，此处仅展示前 30 条）

--- 原说明 ---
If `G` is a `p`-group acting on a finite set `α`, then the number of fixed point
s
  of the action is congruent mod `p` to the cardinality of `α`
-/
theorem card_modEq_card_fixedPoints : Nat.card α ≡ Nat.card (fixedPoints G α) [MOD p] := by
  have := Fintype.ofFinite α
  have := Fintype.ofFinite (fixedPoints G α)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  classical
    calc
      card α = card (Σ y : Quotient (orbitRel G α), { x // Quotient.mk'' x = y }) :=
        card_congr (Equiv.sigmaFiberEquiv (@Quotient.mk'' _ (orbitRel G α))).symm
      _ = ∑ a : Quotient (orbitRel G α), card { x // Quotient.mk'' x = a } := card_sigma
      _ ≡ ∑ _a : fixedPoints G α, 1 [MOD p] := ?_
      _ = _ := by simp
    rw [← ZMod.natCast_eq_natCast_iff _ _ p, Nat.cast_sum, Nat.cast_sum]
    have key :
      ∀ x,
        card { y // (Quotient.mk'' y : Quotient (orbitRel G α)) = Quotient.mk'' x } =
          card (orbit G x) :=
      fun x => by simp only [Quotient.eq'']; congr
    refine
      Eq.symm
        (Finset.sum_bij_ne_zero (fun a _ _ => Quotient.mk'' a.1) (fun _ _ _ => Finset.mem_univ _)
          (fun a₁ _ _ a₂ _ _ h =>
            Subtype.ext (mem_fixedPoints'.mp a₂.2 a₁.1 (Quotient.exact' h)))
          (fun b => Quotient.inductionOn' b fun b _ hb => ?_) fun a ha _ => by
          rw [key, mem_fixedPoints_iff_card_orbit_eq_one.mp a.2])
    obtain ⟨k, hk⟩ := hG.card_orbit b
    rw [Nat.card_eq_fintype_card] at hk
    have : k = 0 := by
      contrapose! hb
      simp [key, hk, hb]
    exact
      ⟨⟨b, mem_fixedPoints_iff_card_orbit_eq_one.2 <| by rw [hk, this, pow_zero]⟩,
        Finset.mem_univ _, ne_of_eq_of_ne Nat.cast_one one_ne_zero, rfl⟩

/-- If a p-group acts on `α` and the cardinality of `α` is not a multiple
  of `p` then the action has a fixed point. -/
/-
**IsPGroup.nonempty_fixed_point_of_prime_not_dvd_card** 是 Mathlib 中的一个定理，位于命名空间 
`IsPGroup`。
形式化陈述：nonempty_fixed_point_of_prime_not_dvd_card (α) [MulAction G α] (hpα : ¬p ∣
 Nat.card α) : (fixedPoints G α).Nonempty
参数：α；hpα : ¬p ∣ Nat.card α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.finite_of_card_ne_zero`：finite_of_card_ne_zero (h : Nat.card α != 0)
 : Finite α
· 使用定理 `dvd_zero`：dvd_zero (a : α) : a ∣ 0
· 使用定理 `Set.Nonempty.of_subtype`：∀ {α : Type u} {s : Set α} [Nonempty ↑s], s.Non
empty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finite.card_pos_iff`：Finite.card_pos_iff [Finite α] : 0 < Nat.card α ↔ N
onempty α
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `Nat.modEq_zero_iff_dvd`：modEq_zero_iff_dvd : a ≡ 0 [MOD n] ↔ n ∣ a
· 使用定理 `IsPGroup.card_modEq_card_fixedPoints`：card_modEq_card_fixedPoints : Nat.
card α ≡ Nat.card (fixedPoints G α) [MOD p]

--- 原说明 ---
If a p-group acts on `α` and the cardinality of `α` is not a multiple
  of `p` then the action has a fixed point.
-/
theorem nonempty_fixed_point_of_prime_not_dvd_card (α) [MulAction G α] (hpα : ¬p ∣ Nat.card α) :
    (fixedPoints G α).Nonempty :=
  have : Finite α := Nat.finite_of_card_ne_zero (fun h ↦ (h ▸ hpα) (dvd_zero p))
  @Set.Nonempty.of_subtype _ _
    (by
      rw [← Finite.card_pos_iff, pos_iff_ne_zero]
      contrapose hpα
      rw [← Nat.modEq_zero_iff_dvd, ← hpα]
      exact hG.card_modEq_card_fixedPoints α)

/-- If a p-group acts on `α` and the cardinality of `α` is a multiple
  of `p`, and the action has one fixed point, then it has another fixed point. -/
/-
**IsPGroup.exists_fixed_point_of_prime_dvd_card_of_fixed_point** 是 Mathlib 中的一个定
理，位于命名空间 `IsPGroup`。
形式化陈述：exists_fixed_point_of_prime_dvd_card_of_fixed_point (hpα : p ∣ Nat.card α)
 {a : α} (ha : a in fixedPoints G α) : exists b, b in fixedPoints G α ∧ a != b
参数：hpα : p ∣ Nat.card α；ha : a in fixedPoints G α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.modEq_zero_iff_dvd`：modEq_zero_iff_dvd : a ≡ 0 [MOD n] ↔ n ∣ a
· 使用定理 `Nat.ModEq.trans`：∀ {n a b c : ℕ}, a ≡ b [MOD n] → b ≡ c [MOD n] → a ≡ c 
[MOD n]
· 使用定理 `Nat.ModEq.symm`：∀ {n a b : ℕ}, a ≡ b [MOD n] → b ≡ a [MOD n]
· 使用定理 `IsPGroup.card_modEq_card_fixedPoints`：card_modEq_card_fixedPoints : Nat.
card α ≡ Nat.card (fixedPoints G α) [MOD p]
· 使用定理 `Dvd.dvd.modEq_zero_nat`：∀ {n a : ℕ}, n ∣ a → a ≡ 0 [MOD n]
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finite.card_pos_iff`：Finite.card_pos_iff [Finite α] : 0 < Nat.card α ↔ N
onempty α
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finite.one_lt_card_iff_nontrivial`：one_lt_card_iff_nontrivial [Finite α]
 : 1 < Nat.card α ↔ Nontrivial α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If a p-group acts on `α` and the cardinality of `α` is a multiple
  of `p`, and the action has one fixed point, then it has another fixed point.
-/
theorem exists_fixed_point_of_prime_dvd_card_of_fixed_point (hpα : p ∣ Nat.card α) {a : α}
    (ha : a ∈ fixedPoints G α) : ∃ b, b ∈ fixedPoints G α ∧ a ≠ b := by
  have hpf : p ∣ Nat.card (fixedPoints G α) :=
    Nat.modEq_zero_iff_dvd.mp ((hG.card_modEq_card_fixedPoints α).symm.trans hpα.modEq_zero_nat)
  have hα : 1 < Nat.card (fixedPoints G α) :=
    (Fact.out (p := p.Prime)).one_lt.trans_le (Nat.le_of_dvd (Finite.card_pos_iff.2 ⟨⟨a, ha⟩⟩) hpf)
  rw [Finite.one_lt_card_iff_nontrivial] at hα
  exact
    let ⟨⟨b, hb⟩, hba⟩ := exists_ne (⟨a, ha⟩ : fixedPoints G α)
    ⟨b, hb, fun hab => hba (by simp_rw [hab])⟩
/-
**IsPGroup.center_nontrivial** 是 Mathlib 中的一个定理，位于命名空间 `IsPGroup`。
形式化陈述：center_nontrivial [Nontrivial G] [Finite G] : Nontrivial (Subgroup.center 
G)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPGroup.exists_fixed_point_of_prime_dvd_card_of_fixed_point`：exists_fix
ed_point_of_prime_dvd_card_of_fixed_point (hpα : p ∣ Nat.card α) {a : α} (ha : a
 in fixedPoints G α) : exists b, b in fixedPoints …
· 使用定理 `IsPGroup.of_equiv`：of_equiv {H : Type*} [Group H] (ϕ : G ≃* H) : IsPGrou
p p H
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsPGroup.nontrivial_iff_card`：nontrivial_iff_card [Finite G] : Nontrivia
l G ↔ exists n > 0, Nat.card G = p ^ n
· 使用引理 `dvd_pow_self`：dvd_pow_self (a : α) {n : Nat} (hn : n != 0) : a ∣ a ^ n
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ConjAct.fixedPoints_eq_center`：fixedPoints_eq_center : fixedPoints (Conj
Act G) G = center G
· 使用定理 `Subgroup.one_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G), 1 
∈ H
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem center_nontrivial [Nontrivial G] [Finite G] : Nontrivial (Subgroup.center G) := by
  have := (hG.of_equiv ConjAct.toConjAct).exists_fixed_point_of_prime_dvd_card_of_fixed_point G
  rw [ConjAct.fixedPoints_eq_center] at this
  have dvd : p ∣ Nat.card G := by
    obtain ⟨n, hn0, hn⟩ := hG.nontrivial_iff_card.mp inferInstance
    exact hn.symm ▸ dvd_pow_self _ (ne_of_gt hn0)
  obtain ⟨g, hg⟩ := this dvd (Subgroup.center G).one_mem
  exact ⟨⟨1, ⟨g, hg.1⟩, mt Subtype.ext_iff.mp hg.2⟩⟩
/-
**IsPGroup.bot_lt_center** 是 Mathlib 中的一个定理，位于命名空间 `IsPGroup`。
形式化陈述：bot_lt_center [Nontrivial G] [Finite G] : ⊥ < Subgroup.center G
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPGroup.center_nontrivial`：center_nontrivial [Nontrivial G] [Finite G] 
: Nontrivial (Subgroup.center G)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `bot_lt_iff_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Orde
rBot α] {a : α}, ⊥ < a ↔ a ≠ ⊥
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.one_lt_card_iff_ne_bot`：one_lt_card_iff_ne_bot [Finite H] : 1 <
 Nat.card H ↔ H != ⊥
· 使用定理 `Subgroup.instFiniteSubtypeMem`：∀ {G : Type u_1} [inst : Group G] (K : Su
bgroup G) [Finite G], Finite ↥K
· 使用定理 `Finite.one_lt_card`：one_lt_card [Finite α] [h : Nontrivial α] : 1 < Nat.
card α
-/
theorem bot_lt_center [Nontrivial G] [Finite G] : ⊥ < Subgroup.center G := by
  have := center_nontrivial hG
  exact
      bot_lt_iff_ne_bot.mpr ((Subgroup.center G).one_lt_card_iff_ne_bot.mp Finite.one_lt_card)

end GIsPGroup

/-
**IsPGroup.to_le** 是 Mathlib 中的一个定理，位于命名空间 `IsPGroup`。
形式化陈述：to_le {H K : Subgroup G} (hK : IsPGroup p K) (hHK : H <= K) : IsPGroup p H
参数：hK : IsPGroup p K；hHK : H <= K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPGroup.of_injective`：of_injective {H : Type*} [Group H] (ϕ : H ->* G) 
(hϕ : Function.Injective ϕ) : IsPGroup p H
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
-/
theorem to_le {H K : Subgroup G} (hK : IsPGroup p K) (hHK : H ≤ K) : IsPGroup p H :=
  hK.of_injective (Subgroup.inclusion hHK) fun a b h =>
    Subtype.ext (by
      change ((Subgroup.inclusion hHK) a : G) = (Subgroup.inclusion hHK) b
      apply Subtype.ext_iff.mp h)
/-
**IsPGroup.to_inf_left** 是 Mathlib 中的一个定理，位于命名空间 `IsPGroup`。
形式化陈述：to_inf_left {H K : Subgroup G} (hH : IsPGroup p H) : IsPGroup p (H ⊓ K : S
ubgroup G)
参数：hH : IsPGroup p H。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPGroup.to_le`：to_le {H K : Subgroup G} (hK : IsPGroup p K) (hHK : H <=
 K) : IsPGroup p H
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
theorem to_inf_left {H K : Subgroup G} (hH : IsPGroup p H) : IsPGroup p (H ⊓ K : Subgroup G) :=
  hH.to_le inf_le_left
/-
**IsPGroup.to_inf_right** 是 Mathlib 中的一个定理，位于命名空间 `IsPGroup`。
形式化陈述：to_inf_right {H K : Subgroup G} (hK : IsPGroup p K) : IsPGroup p (H ⊓ K : 
Subgroup G)
参数：hK : IsPGroup p K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPGroup.to_le`：to_le {H K : Subgroup G} (hK : IsPGroup p K) (hHK : H <=
 K) : IsPGroup p H
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
theorem to_inf_right {H K : Subgroup G} (hK : IsPGroup p K) : IsPGroup p (H ⊓ K : Subgroup G) :=
  hK.to_le inf_le_right
/-
**IsPGroup.map** 是 Mathlib 中的一个定理，位于命名空间 `IsPGroup`。
形式化陈述：map {H : Subgroup G} (hH : IsPGroup p H) {K : Type*} [Group K] (ϕ : G ->* 
K) : IsPGroup p (H.map ϕ)
参数：hH : IsPGroup p H；ϕ : G ->* K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.range_subtype`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup 
G), H.subtype.range = H
· 使用定理 `MonoidHom.map_range`：map_range (g : N ->* P) (f : G ->* N) : f.range.map
 g = (g.comp f).range
· 使用定理 `IsPGroup.of_surjective`：of_surjective {H : Type*} [Group H] (ϕ : G ->* H
) (hϕ : Function.Surjective ϕ) : IsPGroup p H
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `MonoidHom.rangeRestrict_surjective`：rangeRestrict_surjective (f : G ->* 
N) : Function.Surjective f.rangeRestrict
-/
theorem map {H : Subgroup G} (hH : IsPGroup p H) {K : Type*} [Group K] (ϕ : G →* K) :
    IsPGroup p (H.map ϕ) := by
  rw [← H.range_subtype, MonoidHom.map_range]
  exact hH.of_surjective (ϕ.domRestrict H).rangeRestrict (ϕ.domRestrict H).rangeRestrict_surjective

set_option backward.isDefEq.respectTransparency false in
/-
**IsPGroup.comap_of_ker_isPGroup** 是 Mathlib 中的一个定理，位于命名空间 `IsPGroup`。
形式化陈述：comap_of_ker_isPGroup {H : Subgroup G} (hH : IsPGroup p H) {K : Type*} [Gr
oup K] (ϕ : K ->* G) (hϕ : IsPGroup p ϕ.ker) : IsPGroup p (H.comap ϕ)
参数：hH : IsPGroup p H；ϕ : K ->* G；hϕ : IsPGroup p ϕ.ker。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidHom.map_pow`：∀ {M : Type u_4} {N : Type u_5} [inst : Monoid M] [in
st_1 : Monoid N] (f : M →* N) (a : M) (n : ℕ), f (a ^ n) = f a ^ n
· 使用定理 `Subtype.coe_mk`：coe_mk (a h) : (@mk α p a h : α) = a
· 使用定理 `Subgroup.coe_pow`：coe_pow (x : H) (n : Nat) : ((x ^ n : H) : G) = (x : G
) ^ n
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
-/
theorem comap_of_ker_isPGroup {H : Subgroup G} (hH : IsPGroup p H) {K : Type*} [Group K]
    (ϕ : K →* G) (hϕ : IsPGroup p ϕ.ker) : IsPGroup p (H.comap ϕ) := by
  intro g
  obtain ⟨j, hj⟩ := hH ⟨ϕ g.1, g.2⟩
  rw [Subtype.ext_iff, H.coe_pow, Subtype.coe_mk, ← ϕ.map_pow] at hj
  obtain ⟨k, hk⟩ := hϕ ⟨g.1 ^ p ^ j, hj⟩
  rw [Subtype.ext_iff, ϕ.ker.coe_pow, Subtype.coe_mk, ← pow_mul, ← pow_add] at hk
  exact ⟨j + k, by rwa [Subtype.ext_iff, (H.comap ϕ).coe_pow]⟩
/-
**IsPGroup.ker_isPGroup_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `IsPGroup`。
形式化陈述：ker_isPGroup_of_injective {K : Type*} [Group K] {ϕ : K ->* G} (hϕ : Functi
on.Injective ϕ) : IsPGroup p ϕ.ker
参数：hϕ : Function.Injective ϕ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `MonoidHom.ker_eq_bot`：ker_eq_bot (f : G ->* M) (hf : Function.Injective 
f) : f.ker = ⊥
· 使用定理 `IsPGroup.of_bot`：of_bot : IsPGroup p (⊥ : Subgroup G)
-/
theorem ker_isPGroup_of_injective {K : Type*} [Group K] {ϕ : K →* G} (hϕ : Function.Injective ϕ) :
    IsPGroup p ϕ.ker :=
  (congr_arg (fun Q : Subgroup K => IsPGroup p Q) (ϕ.ker_eq_bot hϕ)).mpr IsPGroup.of_bot
/-
**IsPGroup.comap_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `IsPGroup`。
形式化陈述：comap_of_injective {H : Subgroup G} (hH : IsPGroup p H) {K : Type*} [Group
 K] (ϕ : K ->* G) (hϕ : Function.Injective ϕ) : IsPGroup p (H.comap ϕ)
参数：hH : IsPGroup p H；ϕ : K ->* G；hϕ : Function.Injective ϕ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPGroup.comap_of_ker_isPGroup`：comap_of_ker_isPGroup {H : Subgroup G} (
hH : IsPGroup p H) {K : Type*} [Group K] (ϕ : K ->* G) (hϕ : IsPGroup p ϕ.ker) :
 IsPGroup p (H.comap…
· 使用定理 `IsPGroup.ker_isPGroup_of_injective`：ker_isPGroup_of_injective {K : Type*
} [Group K] {ϕ : K ->* G} (hϕ : Function.Injective ϕ) : IsPGroup p ϕ.ker
-/
theorem comap_of_injective {H : Subgroup G} (hH : IsPGroup p H) {K : Type*} [Group K] (ϕ : K →* G)
    (hϕ : Function.Injective ϕ) : IsPGroup p (H.comap ϕ) :=
  hH.comap_of_ker_isPGroup ϕ (ker_isPGroup_of_injective hϕ)
/-
**IsPGroup.comap_subtype** 是 Mathlib 中的一个定理，位于命名空间 `IsPGroup`。
形式化陈述：comap_subtype {H : Subgroup G} (hH : IsPGroup p H) {K : Subgroup G} : IsPG
roup p (H.comap K.subtype)
参数：hH : IsPGroup p H。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPGroup.comap_of_injective`：comap_of_injective {H : Subgroup G} (hH : I
sPGroup p H) {K : Type*} [Group K] (ϕ : K ->* G) (hϕ : Function.Injective ϕ) : I
sPGroup p (H.coma…
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
theorem comap_subtype {H : Subgroup G} (hH : IsPGroup p H) {K : Subgroup G} :
    IsPGroup p (H.comap K.subtype) :=
  hH.comap_of_injective K.subtype Subtype.coe_injective
/-
**IsPGroup.to_sup_of_normal_right** 是 Mathlib 中的一个定理，位于命名空间 `IsPGroup`。
形式化陈述：to_sup_of_normal_right {H K : Subgroup G} (hH : IsPGroup p H) (hK : IsPGro
up p K) [K.Normal] : IsPGroup p (H ⊔ K : Subgroup G)
参数：hH : IsPGroup p H；hK : IsPGroup p K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QuotientGroup.ker_mk'`：ker_mk' : MonoidHom.ker (QuotientGroup.mk' N : G 
->* G ⧸ N) = N
· 使用定理 `Subgroup.comap_map_eq`：comap_map_eq (H : Subgroup G) : comap f (map f H)
 = H ⊔ f.ker
· 使用定理 `IsPGroup.comap_of_ker_isPGroup`：comap_of_ker_isPGroup {H : Subgroup G} (
hH : IsPGroup p H) {K : Type*} [Group K] (ϕ : K ->* G) (hϕ : IsPGroup p ϕ.ker) :
 IsPGroup p (H.comap…
· 使用定理 `IsPGroup.map`：map {H : Subgroup G} (hH : IsPGroup p H) {K : Type*} [Grou
p K] (ϕ : G ->* K) : IsPGroup p (H.map ϕ)
-/
theorem to_sup_of_normal_right {H K : Subgroup G} (hH : IsPGroup p H) (hK : IsPGroup p K)
    [K.Normal] : IsPGroup p (H ⊔ K : Subgroup G) := by
  rw [← QuotientGroup.ker_mk' K, ← Subgroup.comap_map_eq]
  apply (hH.map (QuotientGroup.mk' K)).comap_of_ker_isPGroup
  rwa [QuotientGroup.ker_mk']
/-
**IsPGroup.to_sup_of_normal_left** 是 Mathlib 中的一个定理，位于命名空间 `IsPGroup`。
形式化陈述：to_sup_of_normal_left {H K : Subgroup G} (hH : IsPGroup p H) (hK : IsPGrou
p p K) [H.Normal] : IsPGroup p (H ⊔ K : Subgroup G)
参数：hH : IsPGroup p H；hK : IsPGroup p K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPGroup.to_sup_of_normal_right`：to_sup_of_normal_right {H K : Subgroup 
G} (hH : IsPGroup p H) (hK : IsPGroup p K) [K.Normal] : IsPGroup p (H ⊔ K : Subg
roup G)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
-/
theorem to_sup_of_normal_left {H K : Subgroup G} (hH : IsPGroup p H) (hK : IsPGroup p K)
    [H.Normal] : IsPGroup p (H ⊔ K : Subgroup G) := sup_comm H K ▸ to_sup_of_normal_right hK hH
/-
**IsPGroup.to_sup_of_normal_right'** 是 Mathlib 中的一个定理，位于命名空间 `IsPGroup`。
形式化陈述：to_sup_of_normal_right' {H K : Subgroup G} (hH : IsPGroup p H) (hK : IsPGr
oup p K) (hHK : H <= Subgroup.normalizer K) : IsPGroup p (H ⊔ K : Subgroup G)
参数：hH : IsPGroup p H；hK : IsPGroup p K；hHK : H <= Subgroup.normalizer K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPGroup.to_sup_of_normal_right`：to_sup_of_normal_right {H K : Subgroup 
G} (hH : IsPGroup p H) (hK : IsPGroup p K) [K.Normal] : IsPGroup p (H ⊔ K : Subg
roup G)
· 使用定理 `IsPGroup.of_equiv`：of_equiv {H : Type*} [Group H] (ϕ : G ≃* H) : IsPGrou
p p H
· 使用定理 `Subgroup.le_normalizer`：le_normalizer : H <= normalizer H
· 使用定理 `Subgroup.normal_in_normalizer`：∀ {G : Type u_1} [inst : Group G] {H : Su
bgroup G}, (H.subgroupOf (Subgroup.normalizer ↑H)).Normal
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.subgroupOf_sup`：subgroupOf_sup {A A' B : Subgroup G} (hA : A <=
 B) (hA' : A' <= B) : (A ⊔ A').subgroupOf B = A.subgroupOf B ⊔ A'.subgroupOf B
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
-/
theorem to_sup_of_normal_right' {H K : Subgroup G} (hH : IsPGroup p H) (hK : IsPGroup p K)
    (hHK : H ≤ Subgroup.normalizer K) : IsPGroup p (H ⊔ K : Subgroup G) :=
  let hHK' :=
    to_sup_of_normal_right (hH.of_equiv (Subgroup.subgroupOfEquivOfLe hHK).symm)
      (hK.of_equiv (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).symm)
  ((congr_arg (fun H : Subgroup (Subgroup.normalizer K) => IsPGroup p H)
            ((Subgroup.subgroupOf_sup hHK Subgroup.le_normalizer).symm)).mp
        hHK').of_equiv
    (Subgroup.subgroupOfEquivOfLe (sup_le hHK Subgroup.le_normalizer))
/-
**IsPGroup.to_sup_of_normal_left'** 是 Mathlib 中的一个定理，位于命名空间 `IsPGroup`。
形式化陈述：to_sup_of_normal_left' {H K : Subgroup G} (hH : IsPGroup p H) (hK : IsPGro
up p K) (hHK : K <= Subgroup.normalizer H) : IsPGroup p (H ⊔ K : Subgroup G)
参数：hH : IsPGroup p H；hK : IsPGroup p K；hHK : K <= Subgroup.normalizer H。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPGroup.to_sup_of_normal_right'`：to_sup_of_normal_right' {H K : Subgrou
p G} (hH : IsPGroup p H) (hK : IsPGroup p K) (hHK : H <= Subgroup.normalizer K) 
: IsPGroup p (H ⊔ K : …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
-/
theorem to_sup_of_normal_left' {H K : Subgroup G} (hH : IsPGroup p H) (hK : IsPGroup p K)
    (hHK : K ≤ Subgroup.normalizer H) : IsPGroup p (H ⊔ K : Subgroup G) :=
  sup_comm H K ▸ to_sup_of_normal_right' hK hH hHK

/-- finite p-groups with different p have coprime orders -/
/-
**IsPGroup.coprime_card_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `IsPGroup`。
形式化陈述：coprime_card_of_ne {G₂ : Type*} [Group G₂] (p₁ p₂ : Nat) [hp₁ : Fact p₁.Pr
ime] [hp₂ : Fact p₂.Prime] (hne : p₁ != p₂) (H₁ : Subgroup G) (H₂ : Subgroup G₂)
 [Finite H₁] [Finite H₂] (hH₁ : IsPGroup p₁ H₁) (hH₂ : IsPGroup p₂ H₂) : Nat.Cop
rime (Nat.card H₁) (Nat.card H₂)
参数：p₁ p₂ : Nat；hne : p₁ != p₂；H₁ : Subgroup G；H₂ : Subgroup G₂；hH₁ : IsPGroup p₁
 H₁；hH₂ : IsPGroup p₂ H₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsPGroup.iff_card`：iff_card [Fact p.Prime] [Finite G] : IsPGroup p G ↔ e
xists n : Nat, Nat.card G = p ^ n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.coprime_pow_primes`：coprime_pow_primes {p q : Nat} (n m : Nat) (pp :
 Prime p) (pq : Prime q) (h : p != q) : Coprime (p ^ n) (q ^ m)
· 使用定理 `Fact.elim`：Fact.elim {p : Prop} (h : Fact p) : p

--- 原说明 ---
finite p-groups with different p have coprime orders
-/
theorem coprime_card_of_ne {G₂ : Type*} [Group G₂] (p₁ p₂ : ℕ) [hp₁ : Fact p₁.Prime]
    [hp₂ : Fact p₂.Prime] (hne : p₁ ≠ p₂) (H₁ : Subgroup G) (H₂ : Subgroup G₂) [Finite H₁]
    [Finite H₂] (hH₁ : IsPGroup p₁ H₁) (hH₂ : IsPGroup p₂ H₂) :
    Nat.Coprime (Nat.card H₁) (Nat.card H₂) := by
  obtain ⟨n₁, heq₁⟩ := iff_card.mp hH₁; rw [heq₁]; clear heq₁
  obtain ⟨n₂, heq₂⟩ := iff_card.mp hH₂; rw [heq₂]; clear heq₂
  exact Nat.coprime_pow_primes _ _ hp₁.elim hp₂.elim hne
/-
**IsPGroup.disjoint_of_coprime** 是 Mathlib 中的一个定理，位于命名空间 `IsPGroup`。
形式化陈述：disjoint_of_coprime {p₁ p₂ : Nat} {H₁ H₂ : Subgroup G} (hH₁ : IsPGroup p₁ 
H₁) (hH₂ : IsPGroup p₂ H₂) (h : p₁.Coprime p₂) : Disjoint H₁ H₂
参数：hH₁ : IsPGroup p₁ H₁；hH₂ : IsPGroup p₂ H₂；h : p₁.Coprime p₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subgroup.disjoint_def`：disjoint_def {H₁ H₂ : Subgroup G} : Disjoint H₁ H
₂ ↔ forall {x : G}, x in H₁ -> x in H₂ -> x = 1
· 使用定理 `orderOf_dvd_of_pow_eq_one`：orderOf_dvd_of_pow_eq_one (h : x ^ n = 1) : o
rderOf x ∣ n
· 使用引理 `Subgroup.orderOf_mk`：orderOf_mk (a : G) (ha) : orderOf (⟨a, ha⟩ : H) = o
rderOf a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `orderOf_eq_one_iff`：orderOf_eq_one_iff : orderOf x = 1 ↔ x = 1
· 使用定理 `Nat.eq_one_of_dvd_coprimes`：eq_one_of_dvd_coprimes {a b k : Nat} (h_ab_c
oprime : Coprime a b) (hka : k ∣ a) (hkb : k ∣ b) : k = 1
· 使用定理 `Nat.Coprime.pow`：∀ {k l : ℕ} (m n : ℕ), k.Coprime l → (k ^ m).Coprime (l
 ^ n)
-/
theorem disjoint_of_coprime {p₁ p₂ : ℕ} {H₁ H₂ : Subgroup G} (hH₁ : IsPGroup p₁ H₁)
    (hH₂ : IsPGroup p₂ H₂) (h : p₁.Coprime p₂) : Disjoint H₁ H₂ := by
  refine Subgroup.disjoint_def.mpr fun {g} hg₁ hg₂ ↦ ?_
  have ⟨k₁, hk₁⟩ := hH₁ ⟨g, hg₁⟩
  have hg₁ := Subgroup.orderOf_mk g _ ▸ orderOf_dvd_of_pow_eq_one hk₁
  have ⟨k₂, hk₂⟩ := hH₂ ⟨g, hg₂⟩
  have hg₂ := Subgroup.orderOf_mk g _ ▸ orderOf_dvd_of_pow_eq_one hk₂
  exact orderOf_eq_one_iff.mp <| Nat.eq_one_of_dvd_coprimes (h.pow k₁ k₂) hg₁ hg₂

/-- p-groups with different p are disjoint -/
/-
**IsPGroup.disjoint_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `IsPGroup`。
形式化陈述：disjoint_of_ne (p₁ p₂ : Nat) [hp₁ : Fact p₁.Prime] [hp₂ : Fact p₂.Prime] (
hne : p₁ != p₂) (H₁ H₂ : Subgroup G) (hH₁ : IsPGroup p₁ H₁) (hH₂ : IsPGroup p₂ H
₂) : Disjoint H₁ H₂
参数：p₁ p₂ : Nat；hne : p₁ != p₂；H₁ H₂ : Subgroup G；hH₁ : IsPGroup p₁ H₁；hH₂ : IsPG
roup p₂ H₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPGroup.disjoint_of_coprime`：disjoint_of_coprime {p₁ p₂ : Nat} {H₁ H₂ :
 Subgroup G} (hH₁ : IsPGroup p₁ H₁) (hH₂ : IsPGroup p₂ H₂) (h : p₁.Coprime p₂) :
 Disjoint H₁ H₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.coprime_primes`：coprime_primes {p q : Nat} (pp : Prime p) (pq : Prim
e q) : Coprime p q ↔ p != q
· 使用定理 `Fact.elim`：Fact.elim {p : Prop} (h : Fact p) : p

--- 原说明 ---
p-groups with different p are disjoint
-/
theorem disjoint_of_ne (p₁ p₂ : ℕ) [hp₁ : Fact p₁.Prime] [hp₂ : Fact p₂.Prime] (hne : p₁ ≠ p₂)
    (H₁ H₂ : Subgroup G) (hH₁ : IsPGroup p₁ H₁) (hH₂ : IsPGroup p₂ H₂) : Disjoint H₁ H₂ :=
  disjoint_of_coprime hH₁ hH₂ <| Nat.coprime_primes hp₁.elim hp₂.elim |>.mpr hne
/-
**IsPGroup.le_or_disjoint_of_coprime** 是 Mathlib 中的一个定理，位于命名空间 `IsPGroup`。
形式化陈述：le_or_disjoint_of_coprime [hp : Fact p.Prime] {P : Subgroup G} (hP : IsPGr
oup p P) {H : Subgroup G} [H.Normal] (h_cop : (Nat.card H).Coprime H.index) : P 
<= H ∨ Disjoint H P
参数：hP : IsPGroup p P；h_cop : (Nat.card H).Coprime H.index。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.index_eq_one`：index_eq_one : H.index = 1 ↔ H = ⊤
· 使用定理 `Nat.coprime_zero_left`：∀ (n : ℕ), Nat.Coprime 0 n ↔ n = 1
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Subgroup.card_eq_one`：card_eq_one : Nat.card H = 1 ↔ H = ⊥
· 使用定理 `Nat.coprime_zero_right`：∀ (n : ℕ), n.Coprime 0 ↔ n = 1
· 使用定理 `disjoint_bot_left`：disjoint_bot_left : Disjoint ⊥ a
· 使用定理 `Nat.finite_of_card_ne_zero`：finite_of_card_ne_zero (h : Nat.card α != 0)
 : Finite α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.card_mul_index`：card_mul_index : Nat.card H * H.index = Nat.car
d G
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsPGroup.exists_card_eq`：∀ {p : ℕ} {G : Type u_1} [inst : Group G] [Fact
 (Nat.Prime p)] [Finite G], IsPGroup p G → ∃ n, Nat.card G = p ^ n
· 使用定理 `Subgroup.instFiniteSubtypeMem`：∀ {G : Type u_1} [inst : Group G] (K : Su
bgroup G) [Finite G], Finite ↥K
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `Nat.Prime.coprime_pow_of_not_dvd`：∀ {p m a : ℕ}, Nat.Prime p → ¬p ∣ a → 
a.Coprime (p ^ m)
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.Prime.not_coprime_iff_dvd`：∀ {m n : ℕ}, ¬m.Coprime n ↔ ∃ p, Nat.Prim
e p ∧ p ∣ m ∧ p ∣ n
· 使用定理 `Subgroup.relIndex_eq_one`：relIndex_eq_one : H.relIndex K = 1 ↔ K <= H
· 使用定理 `Nat.eq_one_of_dvd_coprimes`：eq_one_of_dvd_coprimes {a b k : Nat} (h_ab_c
oprime : Coprime a b) (hka : k ∣ a) (hkb : k ∣ b) : k = 1
· 使用定理 `Subgroup.relIndex_dvd_index_of_normal`：relIndex_dvd_index_of_normal [H.N
ormal] : H.relIndex K ∣ H.index
· 使用定理 `Subgroup.relIndex_dvd_card`：relIndex_dvd_card : H.relIndex K ∣ Nat.card 
K
· 使用引理 `Subgroup.disjoint_of_coprime_natCard`：disjoint_of_coprime_natCard (h : N
at.card H |>.Coprime <| Nat.card K) : Disjoint H K
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
-/
theorem le_or_disjoint_of_coprime [hp : Fact p.Prime] {P : Subgroup G} (hP : IsPGroup p P)
    {H : Subgroup G} [H.Normal] (h_cop : (Nat.card H).Coprime H.index) :
    P ≤ H ∨ Disjoint H P := by
  by_cases h1 : Nat.card H = 0
  · rw [h1, Nat.coprime_zero_left, Subgroup.index_eq_one] at h_cop
    rw [h_cop]
    exact Or.inl le_top
  by_cases h2 : H.index = 0
  · rw [h2, Nat.coprime_zero_right, Subgroup.card_eq_one] at h_cop
    rw [h_cop]
    exact Or.inr disjoint_bot_left
  have : Finite G := by
    apply Nat.finite_of_card_ne_zero
    rw [← H.card_mul_index]
    exact mul_ne_zero h1 h2
  have h3 : (Nat.card H).Coprime (Nat.card P) ∨ H.index.Coprime (Nat.card P) := by
    obtain ⟨k, hk⟩ := hP.exists_card_eq
    refine hk ▸ Or.imp hp.out.coprime_pow_of_not_dvd hp.out.coprime_pow_of_not_dvd ?_
    contrapose! h_cop
    exact Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp.out, h_cop⟩
  refine h3.symm.imp (fun h4 ↦ ?_) (fun h4 ↦ ?_)
  · rw [← Subgroup.relIndex_eq_one]
    exact Nat.eq_one_of_dvd_coprimes h4 (H.relIndex_dvd_index_of_normal P)
      (Subgroup.relIndex_dvd_card H P)
  · exact Subgroup.disjoint_of_coprime_natCard h4

section P2comm

variable [Fact p.Prime] {n : ℕ}

open Subgroup

/-- The cardinality of the `center` of a `p`-group is `p ^ k` where `k` is positive. -/
/-
**IsPGroup.card_center_eq_prime_pow** 是 Mathlib 中的一个定理，位于命名空间 `IsPGroup`。
形式化陈述：card_center_eq_prime_pow (hGpn : Nat.card G = p ^ n) (hn : 0 < n) : exists
 k > 0, Nat.card (center G) = p ^ k
参数：hGpn : Nat.card G = p ^ n；hn : 0 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.finite_of_card_ne_zero`：finite_of_card_ne_zero (h : Nat.card α != 0)
 : Finite α
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsPGroup.to_subgroup`：to_subgroup (H : Subgroup G) : IsPGroup p H
· 使用定理 `IsPGroup.of_card`：of_card {n : Nat} (hG : Nat.card G = p ^ n) : IsPGroup
 p G
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsPGroup.nontrivial_iff_card`：nontrivial_iff_card [Finite G] : Nontrivia
l G ↔ exists n > 0, Nat.card G = p ^ n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.instFiniteSubtypeMem`：∀ {G : Type u_1} [inst : Group G] (K : Su
bgroup G) [Finite G], Finite ↥K
· 使用定理 `IsPGroup.center_nontrivial`：center_nontrivial [Nontrivial G] [Finite G] 
: Nontrivial (Subgroup.center G)

--- 原说明 ---
The cardinality of the `center` of a `p`-group is `p ^ k` where `k` is positive.
-/
theorem card_center_eq_prime_pow (hGpn : Nat.card G = p ^ n) (hn : 0 < n) :
    ∃ k > 0, Nat.card (center G) = p ^ k := by
  have : Finite G := Nat.finite_of_card_ne_zero (hGpn ▸ pow_ne_zero n (NeZero.ne p))
  have hcG := to_subgroup (of_card hGpn) (center G)
  rcases iff_card.1 hcG with _
  have : Nontrivial G := (nontrivial_iff_card <| of_card hGpn).2 ⟨n, hn, hGpn⟩
  exact (nontrivial_iff_card hcG).mp (center_nontrivial (of_card hGpn))

/-- The quotient by the center of a group of cardinality `p ^ 2` is cyclic. -/
/-
**IsPGroup.cyclic_center_quotient_of_card_eq_prime_sq** 是 Mathlib 中的一个定理，位于命名空间 
`IsPGroup`。
形式化陈述：cyclic_center_quotient_of_card_eq_prime_sq (hG : Nat.card G = p ^ 2) : IsC
yclic (G ⧸ center G)
参数：hG : Nat.card G = p ^ 2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isCyclic_of_card_dvd_prime`：isCyclic_of_card_dvd_prime {p : Nat} [hp : F
act p.Prime] (h : Nat.card α ∣ p) : IsCyclic α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_dvd_mul_iff_left`：mul_dvd_mul_iff_left [MonoidWithZero α] [IsLeftCan
celMulZero α] {a b c : α} (ha : a != 0) : a * b ∣ a * c ↔ b ∣ c
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Subgroup.card_mul_index`：card_mul_index : Nat.card H * H.index = Nat.car
d G
· 使用定理 `mul_dvd_mul_right`：mul_dvd_mul_right (h : a ∣ b) (c : α) : a * c ∣ b * c
· 使用定理 `IsPGroup.card_center_eq_prime_pow`：card_center_eq_prime_pow (hGpn : Nat.
card G = p ^ n) (hn : 0 < n) : exists k > 0, Nat.card (center G) = p ^ k
· 使用定理 `zero_lt_two`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Part
ialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `dvd_pow_self`：dvd_pow_self (a : α) {n : Nat} (hn : n != 0) : a ∣ a ^ n
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b

--- 原说明 ---
The quotient by the center of a group of cardinality `p ^ 2` is cyclic.
-/
theorem cyclic_center_quotient_of_card_eq_prime_sq (hG : Nat.card G = p ^ 2) :
    IsCyclic (G ⧸ center G) := by
  apply isCyclic_of_card_dvd_prime (p := p)
  rw [← mul_dvd_mul_iff_left (NeZero.ne p), ← sq, ← hG, ← (center G).card_mul_index]
  apply mul_dvd_mul_right
  rcases card_center_eq_prime_pow hG zero_lt_two with ⟨k, hk0, hk⟩
  rw [hk]
  exact dvd_pow_self p hk0.ne'

/-- A group of order `p ^ 2` is commutative. See also `IsPGroup.commGroupOfCardEqPrimeSq`
for the `CommGroup` instance. -/
/-
**IsPGroup.isMulCommutative_of_card_eq_prime_sq** 是 Mathlib 中的一个定理，位于命名空间 `IsPGr
oup`。
形式化陈述：isMulCommutative_of_card_eq_prime_sq (hG : Nat.card G = p ^ 2) : IsMulComm
utative G
参数：hG : Nat.card G = p ^ 2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPGroup.cyclic_center_quotient_of_card_eq_prime_sq`：cyclic_center_quoti
ent_of_card_eq_prime_sq (hG : Nat.card G = p ^ 2) : IsCyclic (G ⧸ center G)
· 使用定理 `isMulCommutative_of_isCyclic_quotient_center_self`：isMulCommutative_of_i
sCyclic_quotient_center_self [IsCyclic (G ⧸ Subgroup.center G)] : IsMulCommutati
ve G

--- 原说明 ---
A group of order `p ^ 2` is commutative. See also `IsPGroup.commGroupOfCardEqPri
meSq`
for the `CommGroup` instance.
-/
theorem isMulCommutative_of_card_eq_prime_sq (hG : Nat.card G = p ^ 2) : IsMulCommutative G :=
  let := cyclic_center_quotient_of_card_eq_prime_sq hG
  isMulCommutative_of_isCyclic_quotient_center_self G

/-- A group of order `p ^ 2` is commutative. See also `IsPGroup.commutative_of_card_eq_prime_sq`
for just the proof that `∀ a b, a * b = b * a` -/
@[instance_reducible]
/-
**IsPGroup.commGroupOfCardEqPrimeSq** 是 Mathlib 中的一个定义，位于命名空间 `IsPGroup`。
形式化陈述：commGroupOfCardEqPrimeSq (hG : Nat.card G = p ^ 2) : CommGroup G
参数：hG : Nat.card G = p ^ 2。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsPGroup.cyclic_center_quotient_of_card_eq_prime_sq`：cyclic_center_quoti
ent_of_card_eq_prime_sq (hG : Nat.card G = p ^ 2) : IsCyclic (G ⧸ center G)

--- 原说明 ---
A group of order `p ^ 2` is commutative. See also `IsPGroup.commutative_of_card_
eq_prime_sq`
for just the proof that `∀ a b, a * b = b * a`
-/
def commGroupOfCardEqPrimeSq (hG : Nat.card G = p ^ 2) : CommGroup G :=
  let := cyclic_center_quotient_of_card_eq_prime_sq hG
  commGroupOfCyclicCenterQuotient _ (QuotientGroup.ker_mk' <| center G).le

@[deprecated isMulCommutative_of_card_eq_prime_sq (since := "2026-05-26")]
/-
**IsPGroup.commutative_of_card_eq_prime_sq** 是 Mathlib 中的一个定理，位于命名空间 `IsPGroup`。
形式化陈述：commutative_of_card_eq_prime_sq (hG : Nat.card G = p ^ 2) : forall a b : G
, a * b = b * a
参数：hG : Nat.card G = p ^ 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Std.Commutative.comm`：∀ {α : Sort u} {op : α → α → α} [self : Std.Commut
ative op] (a b : α), op a b = op b a
· 使用定理 `IsMulCommutative.is_comm`：∀ {M : Type u_2} {inst : Mul M} [self : IsMulC
ommutative M], Std.Commutative fun x1 x2 => x1 * x2
· 使用定理 `IsPGroup.isMulCommutative_of_card_eq_prime_sq`：isMulCommutative_of_card_
eq_prime_sq (hG : Nat.card G = p ^ 2) : IsMulCommutative G
-/
theorem commutative_of_card_eq_prime_sq (hG : Nat.card G = p ^ 2) : ∀ a b : G, a * b = b * a :=
  isMulCommutative_of_card_eq_prime_sq hG |>.is_comm.comm

end P2comm

end IsPGroup

namespace ZModModule
variable {n : ℕ} {G : Type*} [AddCommGroup G] [Module (ZMod n) G]

/-
**ZModModule.isPGroup_multiplicative** 是 Mathlib 中的一个引理，位于命名空间 `ZModModule`。
形式化陈述：isPGroup_multiplicative : IsPGroup n (Multiplicative G)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用引理 `ZModModule.char_nsmul_eq_zero`：ZModModule.char_nsmul_eq_zero (x : G) : n
 • x = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isPGroup_multiplicative : IsPGroup n (Multiplicative G) := by
  simpa [IsPGroup, Multiplicative.forall] using
    fun _ ↦ ⟨1, by simp [← ofAdd_nsmul, ZModModule.char_nsmul_eq_zero]⟩

end ZModModule

