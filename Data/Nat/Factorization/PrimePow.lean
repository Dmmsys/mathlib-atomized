/-
Copyright (c) 2022 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.Algebra.IsPrimePow
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.Prime.Pow
public import Mathlib.NumberTheory.Divisors

/-!
# Prime powers and factorizations

This file deals with factorizations of prime powers.
-/

@[expose] public section


/-
**IsPrimePow.minFac_pow_factorization_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPrimePow.minFac_pow_factorization_eq {n : Nat} (hn : IsPrimePow n) : n.m
inFac ^ n.factorization n.minFac = n
参数：hn : IsPrimePow n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.Prime.pow_minFac`：∀ {p k : ℕ}, Nat.Prime p → k ≠ 0 → (p ^ k).minFac 
= p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.prime_iff`：prime_iff {p : Nat} : p.Prime ↔ _root_.Prime p
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.Prime.factorization_pow`：∀ {p k : ℕ}, Nat.Prime p → (p ^ k).factoriz
ation = fun₀ | p => k
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b

--- 原说明 ---
# Prime powers and factorizations

This file deals with factorizations of prime powers.
-/
theorem IsPrimePow.minFac_pow_factorization_eq {n : ℕ} (hn : IsPrimePow n) :
    n.minFac ^ n.factorization n.minFac = n := by
  obtain ⟨p, k, hp, hk, rfl⟩ := hn
  rw [← Nat.prime_iff] at hp
  rw [hp.pow_minFac hk.ne', hp.factorization_pow, Finsupp.single_eq_same]
/-
**isPrimePow_of_minFac_pow_factorization_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isPrimePow_of_minFac_pow_factorization_eq {n : Nat} (h : n.minFac ^ n.fact
orization n.minFac = n) (hn : n != 1) : IsPrimePow n
参数：h : n.minFac ^ n.factorization n.minFac = n；hn : n != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.factorization_zero`：factorization_zero : factorization 0 = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.Prime.prime`：∀ {p : ℕ}, Nat.Prime p → Prime p
· 使用定理 `Nat.minFac_prime`：minFac_prime {n : Nat} (n1 : n != 1) : Prime (minFac n
)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem isPrimePow_of_minFac_pow_factorization_eq {n : ℕ}
    (h : n.minFac ^ n.factorization n.minFac = n) (hn : n ≠ 1) : IsPrimePow n := by
  rcases eq_or_ne n 0 with (rfl | hn')
  · simp_all
  refine ⟨_, _, (Nat.minFac_prime hn).prime, ?_, h⟩
  simp [pos_iff_ne_zero, ← Finsupp.mem_support_iff, Nat.support_factorization, hn',
    Nat.minFac_prime hn, Nat.minFac_dvd]
/-
**isPrimePow_iff_minFac_pow_factorization_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isPrimePow_iff_minFac_pow_factorization_eq {n : Nat} (hn : n != 1) : IsPri
mePow n ↔ n.minFac ^ n.factorization n.minFac = n
参数：hn : n != 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPrimePow.minFac_pow_factorization_eq`：IsPrimePow.minFac_pow_factorizat
ion_eq {n : Nat} (hn : IsPrimePow n) : n.minFac ^ n.factorization n.minFac = n
· 使用定理 `isPrimePow_of_minFac_pow_factorization_eq`：isPrimePow_of_minFac_pow_fact
orization_eq {n : Nat} (h : n.minFac ^ n.factorization n.minFac = n) (hn : n != 
1) : IsPrimePow n
-/
theorem isPrimePow_iff_minFac_pow_factorization_eq {n : ℕ} (hn : n ≠ 1) :
    IsPrimePow n ↔ n.minFac ^ n.factorization n.minFac = n :=
  ⟨fun h => h.minFac_pow_factorization_eq, fun h => isPrimePow_of_minFac_pow_factorization_eq h hn⟩
/-
**isPrimePow_iff_factorization_eq_single** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isPrimePow_iff_factorization_eq_single {n : Nat} : IsPrimePow n ↔ exists p
 k : Nat, 0 < k ∧ n.factorization = Finsupp.single p k
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isPrimePow_nat_iff`：isPrimePow_nat_iff (n : Nat) : IsPrimePow n ↔ exists
 p k : Nat, Nat.Prime p ∧ 0 < k ∧ p ^ k = n
· 使用定理 `exists₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∃ a b, p a b) ↔ ∃ a b, q a b
)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.Prime.factorization_pow`：∀ {p k : ℕ}, Nat.Prime p → (p ^ k).factoriz
ation = fun₀ | p => k
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.factorization_zero`：factorization_zero : factorization 0 = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.eq_pow_of_factorization_eq_single`：eq_pow_of_factorization_eq_single
 {n p k : Nat} (hn : n != 0) (h : n.factorization = Finsupp.single p k) : n = p 
^ k
· 使用引理 `Nat.prime_of_mem_primeFactors`：prime_of_mem_primeFactors (hp : p in n.pr
imeFactors) : p.Prime
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finsupp.mem_support_iff`：mem_support_iff {f : α ->₀ M} : forall {a : α},
 a in f.support ↔ f a != 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem isPrimePow_iff_factorization_eq_single {n : ℕ} :
    IsPrimePow n ↔ ∃ p k : ℕ, 0 < k ∧ n.factorization = Finsupp.single p k := by
  rw [isPrimePow_nat_iff]
  refine exists₂_congr fun p k => ?_
  constructor
  · rintro ⟨hp, hk, hn⟩
    exact ⟨hk, by rw [← hn, Nat.Prime.factorization_pow hp]⟩
  · rintro ⟨hk, hn⟩
    have hn0 : n ≠ 0 := by
      rintro rfl
      simp_all only [Finsupp.single_eq_zero, eq_comm, Nat.factorization_zero, hk.ne']
    rw [Nat.eq_pow_of_factorization_eq_single hn0 hn]
    exact ⟨Nat.prime_of_mem_primeFactors <|
      Finsupp.mem_support_iff.2 (by simp [hn, hk.ne'] : n.factorization p ≠ 0), hk, rfl⟩
/-
**isPrimePow_iff_card_primeFactors_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isPrimePow_iff_card_primeFactors_eq_one {n : Nat} : IsPrimePow n ↔ n.prime
Factors.card = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isPrimePow_iff_card_primeFactors_eq_one {n : ℕ} :
    IsPrimePow n ↔ n.primeFactors.card = 1 := by
  simp_rw [isPrimePow_iff_factorization_eq_single, ← Nat.support_factorization,
    Finsupp.card_support_eq_one', pos_iff_ne_zero]
/-
**Nat.not_isPrimePow_iff_nontrivial_of_two_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.not_isPrimePow_iff_nontrivial_of_two_le {n : Nat} (hn : 2 <= n) : ¬ Is
PrimePow n ↔ n.primeFactors.Nontrivial
参数：hn : 2 <= n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isPrimePow_iff_card_primeFactors_eq_one`：isPrimePow_iff_card_primeFactor
s_eq_one {n : Nat} : IsPrimePow n ↔ n.primeFactors.card = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.one_lt_card_iff_nontrivial`：one_lt_card_iff_nontrivial : 1 < #s ↔
 s.Nontrivial
-/
theorem Nat.not_isPrimePow_iff_nontrivial_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    ¬ IsPrimePow n ↔ n.primeFactors.Nontrivial := by
  rw [isPrimePow_iff_card_primeFactors_eq_one, ← Finset.one_lt_card_iff_nontrivial]
  grind [primeFactors_eq_empty]
/-
**IsPrimePow.exists_ordCompl_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPrimePow.exists_ordCompl_eq_one {n : Nat} (h : IsPrimePow n) : exists p 
: Nat, p.Prime ∧ ordCompl[p] n = 1
参数：h : IsPrimePow n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `not_isPrimePow_zero`：not_isPrimePow_zero [IsReduced R] : ¬IsPrimePow (0 
: R)
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Nat.instIsDomain`：IsDomain ℕ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isPrimePow_iff_factorization_eq_single`：isPrimePow_iff_factorization_eq_
single {n : Nat} : IsPrimePow n ↔ exists p k : Nat, 0 < k ∧ n.factorization = Fi
nsupp.single p k
· 使用定理 `em'`：em' (p : Prop) : ¬p ∨ p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.factorization_eq_zero_of_not_prime`：factorization_eq_zero_of_not_pri
me (n : Nat) {p : Nat} (hp : ¬p.Prime) : n.factorization p = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.eq_of_factorization_eq`：eq_of_factorization_eq {a b : Nat} (ha : a !
= 0) (hb : b != 0) (h : forall p : Nat, a.factorization p = b.factorization p) :
 a = b
· 使用定理 `Nat.ordCompl_pos`：ordCompl_pos {n : Nat} (p : Nat) (hn : n != 0) : 0 < o
rdCompl[p] n
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Nat.factorization_ordCompl`：factorization_ordCompl (n p : Nat) : (ordCom
pl[p] n).factorization = n.factorization.erase p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finsupp.erase_single`：erase_single {a : α} {b : M} : erase a (single a b
) = 0
· 使用定理 `Nat.factorization_one`：factorization_one : factorization 1 = 0
-/
theorem IsPrimePow.exists_ordCompl_eq_one {n : ℕ} (h : IsPrimePow n) :
    ∃ p : ℕ, p.Prime ∧ ordCompl[p] n = 1 := by
  rcases eq_or_ne n 0 with (rfl | hn0); · cases not_isPrimePow_zero h
  rcases isPrimePow_iff_factorization_eq_single.mp h with ⟨p, k, hk0, h1⟩
  rcases em' p.Prime with (pp | pp)
  · refine absurd ?_ hk0.ne'
    simp [← Nat.factorization_eq_zero_of_not_prime n pp, h1]
  refine ⟨p, pp, ?_⟩
  refine Nat.eq_of_factorization_eq (Nat.ordCompl_pos p hn0).ne' (by simp) fun q => ?_
  rw [Nat.factorization_ordCompl n p, h1]
  simp
/-
**exists_ordCompl_eq_one_iff_isPrimePow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_ordCompl_eq_one_iff_isPrimePow {n : Nat} (hn : n != 1) : IsPrimePow
 n ↔ exists p : Nat, p.Prime ∧ ordCompl[p] n = 1
参数：hn : n != 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPrimePow.exists_ordCompl_eq_one`：IsPrimePow.exists_ordCompl_eq_one {n 
: Nat} (h : IsPrimePow n) : exists p : Nat, p.Prime ∧ ordCompl[p] n = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isPrimePow_nat_iff`：isPrimePow_nat_iff (n : Nat) : IsPrimePow n ↔ exists
 p k : Nat, Nat.Prime p ∧ 0 < k ∧ p ^ k = n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.eq_of_dvd_of_div_eq_one`：∀ {a b : ℕ}, a ∣ b → b / a = 1 → a = b
· 使用定理 `Nat.ordProj_dvd`：ordProj_dvd (n p : Nat) : ordProj[p] n ∣ n
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.le_zero`：∀ {i : ℕ}, i ≤ 0 ↔ i = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem exists_ordCompl_eq_one_iff_isPrimePow {n : ℕ} (hn : n ≠ 1) :
    IsPrimePow n ↔ ∃ p : ℕ, p.Prime ∧ ordCompl[p] n = 1 := by
  refine ⟨fun h => IsPrimePow.exists_ordCompl_eq_one h, fun h => ?_⟩
  rcases h with ⟨p, pp, h⟩
  rw [isPrimePow_nat_iff]
  rw [← Nat.eq_of_dvd_of_div_eq_one (Nat.ordProj_dvd n p) h] at hn ⊢
  refine ⟨p, n.factorization p, pp, ?_, by simp⟩
  contrapose! hn
  simp [Nat.le_zero.1 hn]

/-- An equivalent definition for prime powers: `n` is a prime power iff there is a unique prime
dividing it. -/
/-
**isPrimePow_iff_unique_prime_dvd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isPrimePow_iff_unique_prime_dvd {n : Nat} : IsPrimePow n ↔ exists! p : Nat
, p.Prime ∧ p ∣ n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isPrimePow_nat_iff`：isPrimePow_nat_iff (n : Nat) : IsPrimePow n ↔ exists
 p k : Nat, Nat.Prime p ∧ 0 < k ∧ p ^ k = n
· 使用引理 `dvd_pow_self`：dvd_pow_self (a : α) {n : Nat} (hn : n != 0) : a ∣ a ^ n
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.prime_dvd_prime_iff_eq`：prime_dvd_prime_iff_eq {p q : Nat} (pp : p.P
rime) (qp : q.Prime) : p ∣ q ↔ p = q
· 使用定理 `Nat.Prime.dvd_of_dvd_pow`：∀ {p m n : ℕ}, Nat.Prime p → p ∣ m ^ n → p ∣ m
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.prime_two`：prime_two : Prime 2
· 使用定理 `dvd_zero`：dvd_zero (a : α) : a ∣ 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.prime_three`：prime_three : Prime 3
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Nat.Prime.factorization_pos_of_dvd`：∀ {n p : ℕ}, Nat.Prime p → n ≠ 0 → p
 ∣ n → 0 < n.factorization p
· 使用定理 `Nat.dvd_antisymm`：∀ {m n : ℕ}, m ∣ n → n ∣ m → m = n
· 使用定理 `Nat.ordProj_dvd`：ordProj_dvd (n p : Nat) : ordProj[p] n ∣ n
· 使用定理 `Nat.dvd_of_primeFactorsList_subperm`：dvd_of_primeFactorsList_subperm {a 
b : Nat} (ha : a != 0) (h : a.primeFactorsList <+~ b.primeFactorsList) : a ∣ b
· 使用定理 `Nat.Prime.primeFactorsList_pow`：∀ {p : ℕ}, Nat.Prime p → ∀ (n : ℕ), (p ^
 n).primeFactorsList = List.replicate n p
· 使用定理 `List.subperm_ext_iff`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {l₁ 
l₂ : List α},   l₁.Subperm l₂ ↔ ∀ x ∈ l₁, List.count x l₁ ≤ List.count x l₂
· 使用定理 `Nat.instLawfulBEq`：LawfulBEq ℕ
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Nat.mem_primeFactorsList`：mem_primeFactorsList {n p} (hn : n != 0) : p i
n primeFactorsList n ↔ Prime p ∧ p ∣ n
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.primeFactorsList_count_eq`：primeFactorsList_count_eq {n p : Nat} : n
.primeFactorsList.count p = n.factorization p
· 使用定理 `List.count_replicate_self`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α]
 {a : α} {n : ℕ}, List.count a (List.replicate n a) = n

--- 原说明 ---
An equivalent definition for prime powers: `n` is a prime power iff there is a u
nique prime
dividing it.
-/
theorem isPrimePow_iff_unique_prime_dvd {n : ℕ} : IsPrimePow n ↔ ∃! p : ℕ, p.Prime ∧ p ∣ n := by
  rw [isPrimePow_nat_iff]
  constructor
  · rintro ⟨p, k, hp, hk, rfl⟩
    refine ⟨p, ⟨hp, dvd_pow_self _ hk.ne'⟩, ?_⟩
    rintro q ⟨hq, hq'⟩
    exact (Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow hq')
  rintro ⟨p, ⟨hp, hn⟩, hq⟩
  rcases eq_or_ne n 0 with (rfl | hn₀)
  · cases (hq 2 ⟨Nat.prime_two, dvd_zero 2⟩).trans (hq 3 ⟨Nat.prime_three, dvd_zero 3⟩).symm
  refine ⟨p, n.factorization p, hp, hp.factorization_pos_of_dvd hn₀ hn, ?_⟩
  simp only [and_imp] at hq
  apply Nat.dvd_antisymm (Nat.ordProj_dvd _ _)
  -- We need to show n ∣ p ^ n.factorization p
  apply Nat.dvd_of_primeFactorsList_subperm hn₀
  rw [hp.primeFactorsList_pow, List.subperm_ext_iff]
  intro q hq'
  rw [Nat.mem_primeFactorsList hn₀] at hq'
  cases hq _ hq'.1 hq'.2
  simp
/-
**isPrimePow_pow_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isPrimePow_pow_iff {n k : Nat} (hk : k != 0) : IsPrimePow (n ^ k) ↔ IsPrim
ePow n
参数：hk : k != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `existsUnique_congr`：existsUnique_congr {p q : α -> Prop} (h : forall a, 
p a ↔ q a) : (exists! a, p a) ↔ exists! a, q a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem isPrimePow_pow_iff {n k : ℕ} (hk : k ≠ 0) : IsPrimePow (n ^ k) ↔ IsPrimePow n := by
  simp only [isPrimePow_iff_unique_prime_dvd]
  apply existsUnique_congr
  simp +contextual [Nat.prime_iff, Prime.dvd_pow_iff_dvd, hk]
/-
**Nat.Coprime.isPrimePow_dvd_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.Coprime.isPrimePow_dvd_mul {n a b : Nat} (hab : Nat.Coprime a b) (hn :
 IsPrimePow n) : n ∣ a * b ↔ n ∣ a ∨ n ∣ b
参数：hab : Nat.Coprime a b；hn : IsPrimePow n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isPrimePow_nat_iff`：isPrimePow_nat_iff (n : Nat) : IsPrimePow n ↔ exists
 p k : Nat, Nat.Prime p ∧ 0 < k ∧ p ^ k = n
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Nat.Prime.pow_dvd_iff_le_factorization`：∀ {p k n : ℕ}, Nat.Prime p → n ≠
 0 → (p ^ k ∣ n ↔ k ≤ n.factorization p)
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Nat.instIsDomain`：IsDomain ℕ
· 使用定理 `Nat.factorization_mul`：factorization_mul {a b : Nat} (ha : a != 0) (hb :
 b != 0) : (a * b).factorization = a.factorization + b.factorization
· 使用定理 `Finsupp.notMem_support_iff`：notMem_support_iff {f : α ->₀ M} {a} : a ∉ f
.support ↔ f a = 0
· 使用定理 `not_and_or`：not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b
· 使用定理 `Finset.mem_inter`：mem_inter {a : α} {s₁ s₂ : Finset α} : a in s₁ inter s
₂ ↔ a in s₁ ∧ a in s₂
· 使用定理 `Disjoint.le_bot`：Disjoint.le_bot : Disjoint a b -> a ⊓ b <= ⊥
· 使用定理 `Nat.Coprime.disjoint_primeFactors`：∀ {a b : ℕ}, a.Coprime b → Disjoint a
.primeFactors b.primeFactors
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
（共 35 条，此处仅展示前 30 条）
-/
theorem Nat.Coprime.isPrimePow_dvd_mul {n a b : ℕ} (hab : Nat.Coprime a b) (hn : IsPrimePow n) :
    n ∣ a * b ↔ n ∣ a ∨ n ∣ b := by
  rcases eq_or_ne a 0 with (rfl | ha)
  · simp
  rcases eq_or_ne b 0 with (rfl | hb)
  · simp
  refine
    ⟨?_, fun h =>
      Or.elim h (fun i => i.trans ((@dvd_mul_right a b a hab).mpr (dvd_refl a)))
          fun i => i.trans ((@dvd_mul_left a b b hab.symm).mpr (dvd_refl b))⟩
  obtain ⟨p, k, hp, _, rfl⟩ := (isPrimePow_nat_iff _).1 hn
  simp only [hp.pow_dvd_iff_le_factorization (mul_ne_zero ha hb), Nat.factorization_mul ha hb,
    hp.pow_dvd_iff_le_factorization ha, hp.pow_dvd_iff_le_factorization hb, Pi.add_apply,
    Finsupp.coe_add]
  have : a.factorization p = 0 ∨ b.factorization p = 0 := by
    rw [← Finsupp.notMem_support_iff, ← Finsupp.notMem_support_iff, ← not_and_or, ←
      Finset.mem_inter]
    intro t
    simpa using hab.disjoint_primeFactors.le_bot t
  rcases this with h | h <;> simp [h, imp_or]
/-
**Nat.mul_divisors_filter_prime_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.mul_divisors_filter_prime_pow {a b : Nat} (hab : a.Coprime b) : {d in 
(a * b).divisors | IsPrimePow d} = {d in a.divisors union b.divisors | IsPrimePo
w d}
参数：hab : a.Coprime b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.filter.congr_simp`：∀ {α : Type u_1} (p p_1 : α → Prop),   p = p_1
 →     ∀ {inst : DecidablePred p} [inst_1 : DecidablePred p_1] (s s_1 : Finset α
),       s = s…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Nat.divisors_zero`：divisors_zero : divisors 0 = ∅
· 使用定理 `Finset.filter_empty`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePr
ed p], Finset.filter p ∅ = ∅
· 使用定理 `Nat.divisors_one`：divisors_one : divisors 1 = {1}
· 使用定理 `Finset.empty_union`：empty_union (s : Finset α) : ∅ union s = s
· 使用定理 `Finset.filter_singleton`：filter_singleton (a : α) : filter p {a} = if p 
a then {a} else ∅
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Finset.union_empty`：union_empty (s : Finset α) : s union ∅ = s
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Nat.Coprime.isPrimePow_dvd_mul`：Nat.Coprime.isPrimePow_dvd_mul {n a b : 
Nat} (hab : Nat.Coprime a b) (hn : IsPrimePow n) : n ∣ a * b ↔ n ∣ a ∨ n ∣ b
-/
theorem Nat.mul_divisors_filter_prime_pow {a b : ℕ} (hab : a.Coprime b) :
    {d ∈ (a * b).divisors | IsPrimePow d} = {d ∈ a.divisors ∪ b.divisors | IsPrimePow d} := by
  rcases eq_or_ne a 0 with (rfl | ha)
  · simp only [Nat.coprime_zero_left] at hab
    simp [hab, Finset.filter_singleton, not_isPrimePow_one]
  rcases eq_or_ne b 0 with (rfl | hb)
  · simp only [Nat.coprime_zero_right] at hab
    simp [hab, Finset.filter_singleton, not_isPrimePow_one]
  ext n
  simp only [ha, hb, Finset.mem_union, Finset.mem_filter, Nat.mul_eq_zero, and_true, Ne,
    and_congr_left_iff, not_false_iff, Nat.mem_divisors, or_self_iff]
  apply hab.isPrimePow_dvd_mul

set_option backward.isDefEq.respectTransparency false in
/-- The canonical equivalence between pairs `(p, k)` with `p` a prime and `k : ℕ`
and the set of prime powers given by `(p, k) ↦ p^(k+1)`. -/
/-
**Nat.Primes.prodNatEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Nat.Primes.prodNatEquiv : Nat.Primes × Nat ≃ {n : Nat // IsPrimePow n} whe
re toFun pk
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical equivalence between pairs `(p, k)` with `p` a prime and `k : ℕ`
and the set of prime powers given by `(p, k) ↦ p^(k+1)`.
-/
def Nat.Primes.prodNatEquiv : Nat.Primes × ℕ ≃ {n : ℕ // IsPrimePow n} where
  toFun pk :=
    ⟨pk.1 ^ (pk.2 + 1), ⟨pk.1, pk.2 + 1, prime_iff.mp pk.1.prop, pk.2.add_one_pos, rfl⟩⟩
  invFun n :=
    (⟨n.val.minFac, minFac_prime n.prop.ne_one⟩, n.val.factorization n.val.minFac - 1)
  left_inv := fun (p, k) ↦ by
    simp only [p.prop.pow_minFac k.add_one_ne_zero, Subtype.coe_eta, factorization_pow, p.prop,
      Prime.factorization, Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.single_add,
      Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same, add_tsub_cancel_right]
  right_inv n := by
    ext1
    dsimp only
    rw [sub_one_add_one (Nat.factorization_minFac_ne_zero n.prop.one_lt),
      n.prop.minFac_pow_factorization_eq]

@[simp]
/-
**Nat.Primes.prodNatEquiv_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Nat.Primes.prodNatEquiv_apply (p : Nat.Primes) (k : Nat) : prodNatEquiv (p
, k) = ⟨p ^ (k + 1), p, k + 1, prime_iff.mp p.prop, k.add_one_pos, rfl⟩
参数：p : Nat.Primes；k : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Nat.Primes.prodNatEquiv_apply (p : Nat.Primes) (k : ℕ) :
    prodNatEquiv (p, k) = ⟨p ^ (k + 1), p, k + 1, prime_iff.mp p.prop, k.add_one_pos, rfl⟩ := by
  rfl

@[simp]
/-
**Nat.Primes.coe_prodNatEquiv_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Nat.Primes.coe_prodNatEquiv_apply (p : Nat.Primes) (k : Nat) : (prodNatEqu
iv (p, k) : Nat) = p ^ (k + 1)
参数：p : Nat.Primes；k : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Nat.Primes.coe_prodNatEquiv_apply (p : Nat.Primes) (k : ℕ) :
    (prodNatEquiv (p, k) : ℕ) = p ^ (k + 1) :=
  rfl

@[simp]
/-
**Nat.Primes.prodNatEquiv_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Nat.Primes.prodNatEquiv_symm_apply {n : Nat} (hn : IsPrimePow n) : prodNat
Equiv.symm ⟨n, hn⟩ = (⟨n.minFac, minFac_prime hn.ne_one⟩, n.factorization n.minF
ac - 1)
参数：hn : IsPrimePow n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma Nat.Primes.prodNatEquiv_symm_apply {n : ℕ} (hn : IsPrimePow n) :
    prodNatEquiv.symm ⟨n, hn⟩ =
      (⟨n.minFac, minFac_prime hn.ne_one⟩, n.factorization n.minFac - 1) :=
  rfl

namespace Nat

section PrimePowEqPow
variable {p a m n : ℕ} (hp : p.Prime) (hn : n ≠ 0) (h : p ^ m = a ^ n)
include hp h

/-
**Nat.exponent_eq_exponent_mul_factorization_of_prime_pow_eq_base_pow** 是 Mathli
b 中的一个定理，位于命名空间 `Nat`。
形式化陈述：exponent_eq_exponent_mul_factorization_of_prime_pow_eq_base_pow : m = n * 
a.factorization p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `Nat.factorization_pow`：factorization_pow (n k : Nat) : factorization (n 
^ k) = k • n.factorization
· 使用定理 `Nat.Prime.factorization_pow`：∀ {p k : ℕ}, Nat.Prime p → (p ^ k).factoriz
ation = fun₀ | p => k
-/
theorem exponent_eq_exponent_mul_factorization_of_prime_pow_eq_base_pow :
    m = n * a.factorization p := by
  have := congrArg Nat.factorization h
  rw [Nat.Prime.factorization_pow hp, Nat.factorization_pow] at this
  simpa using congr($this p)
/-
**Nat.exponent_dvd_of_prime_pow_eq_pow** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：exponent_dvd_of_prime_pow_eq_pow : n ∣ m
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dvd.intro`：Dvd.intro (c : α) (h : a * c = b) : a ∣ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.exponent_eq_exponent_mul_factorization_of_prime_pow_eq_base_pow`：exp
onent_eq_exponent_mul_factorization_of_prime_pow_eq_base_pow : m = n * a.factori
zation p
-/
theorem exponent_dvd_of_prime_pow_eq_pow : n ∣ m :=
  Dvd.intro (a.factorization p)
    (exponent_eq_exponent_mul_factorization_of_prime_pow_eq_base_pow hp h).symm

include hn
/-
**Nat.exists_base_eq_prime_pow_of_prime_pow_eq_base_pow** 是 Mathlib 中的一个定理，位于命名空
间 `Nat`。
形式化陈述：exists_base_eq_prime_pow_of_prime_pow_eq_base_pow : exists k, a = p ^ k
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.exponent_dvd_of_prime_pow_eq_pow`：exponent_dvd_of_prime_pow_eq_pow :
 n ∣ m
· 使用引理 `Nat.pow_left_injective`：pow_left_injective (hn : n != 0) : Injective (fu
n a : Nat => a ^ n)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_mul'`：pow_mul' (a : M) (m n : Nat) : a ^ (m * n) = (a ^ n) ^ m
-/
theorem exists_base_eq_prime_pow_of_prime_pow_eq_base_pow : ∃ k, a = p ^ k := by
  rcases exponent_dvd_of_prime_pow_eq_pow hp h with ⟨k, m_eq⟩
  rw [m_eq, pow_mul'] at h
  use k
  exact Nat.pow_left_injective hn h.symm

end PrimePowEqPow

end Nat

