/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module

public import Mathlib.Algebra.GroupWithZero.Associated
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Nat.Prime.Defs

/-!
# Prime numbers

This file develops the theory of prime numbers: natural numbers `p ≥ 2` whose only divisors are
`p` and `1`.

-/

public section

namespace Nat
variable {n : ℕ}

/-
**Nat.prime_mul_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：prime_mul_iff {a b : Nat} : Nat.Prime (a * b) ↔ a.Prime ∧ b = 1 ∨ b.Prime 
∧ a = 1
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem prime_mul_iff {a b : ℕ} : Nat.Prime (a * b) ↔ a.Prime ∧ b = 1 ∨ b.Prime ∧ a = 1 := by
  simp only [irreducible_mul_iff, ← irreducible_iff_nat_prime, Nat.isUnit_iff]
/-
**Nat.not_prime_mul** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：not_prime_mul {a b : Nat} (a1 : a != 1) (b1 : b != 1) : ¬Prime (a * b)
参数：a1 : a != 1；b1 : b != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem not_prime_mul {a b : ℕ} (a1 : a ≠ 1) (b1 : b ≠ 1) : ¬Prime (a * b) := by
  simp [prime_mul_iff, *]
/-
**Nat.not_prime_of_mul_eq** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：not_prime_of_mul_eq {a b n : Nat} (h : a * b = n) (h₁ : a != 1) (h₂ : b !=
 1) : ¬Prime n
参数：h : a * b = n；h₁ : a != 1；h₂ : b != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.not_prime_mul`：not_prime_mul {a b : Nat} (a1 : a != 1) (b1 : b != 1)
 : ¬Prime (a * b)
-/
theorem not_prime_of_mul_eq {a b n : ℕ} (h : a * b = n) (h₁ : a ≠ 1) (h₂ : b ≠ 1) : ¬Prime n :=
  h ▸ not_prime_mul h₁ h₂
/-
**Nat.Prime.dvd_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：∀ {p a : ℕ}, Nat.Prime p → a ≠ 1 → (a ∣ p ↔ p = a)
参数：a ∣ p ↔ p = a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.prime_mul_iff`：prime_mul_iff {a b : Nat} : Nat.Prime (a * b) ↔ a.Pri
me ∧ b = 1 ∨ b.Prime ∧ a = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dvd_refl`：dvd_refl (a : α) : a ∣ a
-/
theorem Prime.dvd_iff_eq {p a : ℕ} (hp : p.Prime) (a1 : a ≠ 1) : a ∣ p ↔ p = a := by
  refine ⟨?_, by rintro rfl; rfl⟩
  rintro ⟨j, rfl⟩
  rcases prime_mul_iff.mp hp with (⟨_, rfl⟩ | ⟨_, rfl⟩)
  · exact mul_one _
  · exact (a1 rfl).elim
/-
**Nat.Prime.eq_two_or_odd** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：∀ {p : ℕ}, Nat.Prime p → p = 2 ∨ p % 2 = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp_left`：∀ {a b c : Prop}, (a → b) → a ∨ c → b ∨ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Nat.Prime.eq_one_or_self_of_dvd`：∀ {p : ℕ}, Nat.Prime p → ∀ (m : ℕ), m ∣
 p → m = 1 ∨ m = p
· 使用定理 `Nat.dvd_of_mod_eq_zero`：∀ {m n : ℕ}, n % m = 0 → m ∣ n
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Nat.mod_two_eq_zero_or_one`：∀ (n : ℕ), n % 2 = 0 ∨ n % 2 = 1
-/
theorem Prime.eq_two_or_odd {p : ℕ} (hp : Prime p) : p = 2 ∨ p % 2 = 1 :=
  p.mod_two_eq_zero_or_one.imp_left fun h =>
    ((hp.eq_one_or_self_of_dvd 2 (dvd_of_mod_eq_zero h)).resolve_left (by decide)).symm
/-
**Nat.Prime.eq_two_or_odd'** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：∀ {p : ℕ}, Nat.Prime p → p = 2 ∨ Odd p
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp_right`：∀ {b c a : Prop}, (b → c) → a ∨ b → a ∨ c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.div_add_mod`：∀ (m n : ℕ), n * (m / n) + m % n = m
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Nat.Prime.eq_two_or_odd`：∀ {p : ℕ}, Nat.Prime p → p = 2 ∨ p % 2 = 1
-/
theorem Prime.eq_two_or_odd' {p : ℕ} (hp : Prime p) : p = 2 ∨ Odd p :=
  Or.imp_right (fun h => ⟨p / 2, (div_add_mod p 2).symm.trans (congr_arg _ h)⟩) hp.eq_two_or_odd

section

/-
**Nat.Prime.five_le_of_ne_two_of_ne_three** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：∀ {p : ℕ}, Nat.Prime p → p ≠ 2 → p ≠ 3 → 5 ≤ p
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem Prime.five_le_of_ne_two_of_ne_three {p : ℕ} (hp : p.Prime) (h_two : p ≠ 2)
    (h_three : p ≠ 3) : 5 ≤ p := by
  by_contra! h
  revert h_two h_three hp
  decide +revert

end

/-
**Nat.Prime.pred_pos** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：∀ {p : ℕ}, Nat.Prime p → 0 < p.pred
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.lt_pred_iff`：∀ {n : ℕ} {m : ℕ}, n < m.pred ↔ n.succ < m
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
-/
theorem Prime.pred_pos {p : ℕ} (pp : Prime p) : 0 < pred p :=
  lt_pred_iff.2 pp.one_lt
/-
**Nat.succ_pred_prime** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：succ_pred_prime {p : Nat} (pp : Prime p) : succ (pred p) = p
参数：pp : Prime p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.succ_pred_eq_of_pos`：∀ {n : ℕ}, 0 < n → n.pred.succ = n
· 使用定理 `Nat.Prime.pos`：∀ {p : ℕ}, Nat.Prime p → 0 < p
-/
theorem succ_pred_prime {p : ℕ} (pp : Prime p) : succ (pred p) = p :=
  succ_pred_eq_of_pos pp.pos
/-
**Nat.exists_dvd_of_not_prime** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：exists_dvd_of_not_prime {n : Nat} (n2 : 2 <= n) (np : ¬Prime n) : exists m
, m ∣ n ∧ m != 1 ∧ m != n
参数：n2 : 2 <= n；np : ¬Prime n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.minFac_dvd`：minFac_dvd (n : Nat) : minFac n ∣ n
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `Nat.minFac_prime`：minFac_prime {n : Nat} (n1 : n != 1) : Prime (minFac n
)
· 使用定理 `Nat.ne_of_lt`：∀ {a b : ℕ}, a < b → a ≠ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.not_prime_iff_minFac_lt`：not_prime_iff_minFac_lt {n : Nat} (n2 : 2 <
= n) : ¬Prime n ↔ minFac n < n
-/
theorem exists_dvd_of_not_prime {n : ℕ} (n2 : 2 ≤ n) (np : ¬Prime n) : ∃ m, m ∣ n ∧ m ≠ 1 ∧ m ≠ n :=
  ⟨minFac n, minFac_dvd _, ne_of_gt (minFac_prime (ne_of_gt n2)).one_lt,
    ne_of_lt <| (not_prime_iff_minFac_lt n2).1 np⟩
/-
**Nat.exists_dvd_of_not_prime2** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：exists_dvd_of_not_prime2 {n : Nat} (n2 : 2 <= n) (np : ¬Prime n) : exists 
m, m ∣ n ∧ 2 <= m ∧ m < n
参数：n2 : 2 <= n；np : ¬Prime n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.minFac_dvd`：minFac_dvd (n : Nat) : minFac n ∣ n
· 使用定理 `Nat.Prime.two_le`：∀ {p : ℕ}, Nat.Prime p → 2 ≤ p
· 使用定理 `Nat.minFac_prime`：minFac_prime {n : Nat} (n1 : n != 1) : Prime (minFac n
)
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.not_prime_iff_minFac_lt`：not_prime_iff_minFac_lt {n : Nat} (n2 : 2 <
= n) : ¬Prime n ↔ minFac n < n
-/
theorem exists_dvd_of_not_prime2 {n : ℕ} (n2 : 2 ≤ n) (np : ¬Prime n) :
    ∃ m, m ∣ n ∧ 2 ≤ m ∧ m < n :=
  ⟨minFac n, minFac_dvd _, (minFac_prime (ne_of_gt n2)).two_le,
    (not_prime_iff_minFac_lt n2).1 np⟩
/-
**Nat.not_prime_of_dvd_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：not_prime_of_dvd_of_ne {m n : Nat} (h1 : m ∣ n) (h2 : m != 1) (h3 : m != n
) : ¬Prime n
参数：h1 : m ∣ n；h2 : m != 1；h3 : m != n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Nat.Prime.eq_one_or_self_of_dvd`：∀ {p : ℕ}, Nat.Prime p → ∀ (m : ℕ), m ∣
 p → m = 1 ∨ m = p
-/
theorem not_prime_of_dvd_of_ne {m n : ℕ} (h1 : m ∣ n) (h2 : m ≠ 1) (h3 : m ≠ n) : ¬Prime n :=
  fun h => Or.elim (h.eq_one_or_self_of_dvd m h1) h2 h3
/-
**Nat.not_prime_of_dvd_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：not_prime_of_dvd_of_lt {m n : Nat} (h1 : m ∣ n) (h2 : 2 <= m) (h3 : m < n)
 : ¬Prime n
参数：h1 : m ∣ n；h2 : 2 <= m；h3 : m < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.not_prime_of_dvd_of_ne`：not_prime_of_dvd_of_ne {m n : Nat} (h1 : m ∣
 n) (h2 : m != 1) (h3 : m != n) : ¬Prime n
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.ne_of_lt`：∀ {a b : ℕ}, a < b → a ≠ b
-/
theorem not_prime_of_dvd_of_lt {m n : ℕ} (h1 : m ∣ n) (h2 : 2 ≤ m) (h3 : m < n) : ¬Prime n :=
  not_prime_of_dvd_of_ne h1 (ne_of_gt h2) (ne_of_lt h3)
/-
**Nat.not_prime_iff_exists_dvd_ne** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：not_prime_iff_exists_dvd_ne {n : Nat} (h : 2 <= n) : (¬Prime n) ↔ exists m
, m ∣ n ∧ m != 1 ∧ m != n
参数：h : 2 <= n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.exists_dvd_of_not_prime`：exists_dvd_of_not_prime {n : Nat} (n2 : 2 <
= n) (np : ¬Prime n) : exists m, m ∣ n ∧ m != 1 ∧ m != n
· 使用定理 `Nat.not_prime_of_dvd_of_ne`：not_prime_of_dvd_of_ne {m n : Nat} (h1 : m ∣
 n) (h2 : m != 1) (h3 : m != n) : ¬Prime n
-/
theorem not_prime_iff_exists_dvd_ne {n : ℕ} (h : 2 ≤ n) : (¬Prime n) ↔ ∃ m, m ∣ n ∧ m ≠ 1 ∧ m ≠ n :=
  ⟨exists_dvd_of_not_prime h, fun ⟨_, h1, h2, h3⟩ => not_prime_of_dvd_of_ne h1 h2 h3⟩
/-
**Nat.not_prime_iff_exists_dvd_lt** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：not_prime_iff_exists_dvd_lt {n : Nat} (h : 2 <= n) : (¬Prime n) ↔ exists m
, m ∣ n ∧ 2 <= m ∧ m < n
参数：h : 2 <= n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.exists_dvd_of_not_prime2`：exists_dvd_of_not_prime2 {n : Nat} (n2 : 2
 <= n) (np : ¬Prime n) : exists m, m ∣ n ∧ 2 <= m ∧ m < n
· 使用定理 `Nat.not_prime_of_dvd_of_lt`：not_prime_of_dvd_of_lt {m n : Nat} (h1 : m ∣
 n) (h2 : 2 <= m) (h3 : m < n) : ¬Prime n
-/
theorem not_prime_iff_exists_dvd_lt {n : ℕ} (h : 2 ≤ n) : (¬Prime n) ↔ ∃ m, m ∣ n ∧ 2 ≤ m ∧ m < n :=
  ⟨exists_dvd_of_not_prime2 h, fun ⟨_, h1, h2, h3⟩ => not_prime_of_dvd_of_lt h1 h2 h3⟩
/-
**Nat.not_prime_iff_exists_mul_eq** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：not_prime_iff_exists_mul_eq {n : Nat} (h : 2 <= n) : (¬Prime n) ↔ exists a
 b, a < n ∧ b < n ∧ a * b = n
参数：h : 2 <= n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.prime_iff_not_exists_mul_eq`：prime_iff_not_exists_mul_eq {p : Nat} :
 p.Prime ↔ 2 <= p ∧ ¬ exists m n, m < p ∧ n < p ∧ m * n = p
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem not_prime_iff_exists_mul_eq {n : ℕ} (h : 2 ≤ n) :
    (¬Prime n) ↔ ∃ a b, a < n ∧ b < n ∧ a * b = n := by
  rw [prime_iff_not_exists_mul_eq, and_iff_right h, Classical.not_not]
/-
**Nat.dvd_of_forall_prime_mul_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：dvd_of_forall_prime_mul_dvd {a b : Nat} (hdvd : forall p : Nat, p.Prime ->
 p ∣ a -> p * a ∣ b) : a ∣ b
参数：hdvd : forall p : Nat, p.Prime -> p ∣ a -> p * a ∣ b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `one_dvd`：one_dvd (a : α) : 1 ∣ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.exists_prime_and_dvd`：exists_prime_and_dvd {n : Nat} (hn : n != 1) :
 exists p, Prime p ∧ p ∣ n
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `instIsTransDvd`：∀ {α : Type u_1} [inst : Semigroup α], IsTrans α Dvd.dvd
· 使用定理 `dvd_mul_left`：dvd_mul_left (a b : α) : a ∣ b * a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem dvd_of_forall_prime_mul_dvd {a b : ℕ}
    (hdvd : ∀ p : ℕ, p.Prime → p ∣ a → p * a ∣ b) : a ∣ b := by
  obtain rfl | ha := eq_or_ne a 1
  · apply one_dvd
  obtain ⟨p, hp⟩ := exists_prime_and_dvd ha
  exact _root_.trans (dvd_mul_left a p) (hdvd p hp.1 hp.2)
/-
**Nat.Prime.even_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：∀ {p : ℕ}, Nat.Prime p → (Even p ↔ p = 2)
参数：Even p ↔ p = 2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `even_iff_two_dvd`：even_iff_two_dvd : Even a ↔ 2 ∣ a
· 使用定理 `Nat.prime_dvd_prime_iff_eq`：prime_dvd_prime_iff_eq {p q : Nat} (pp : p.P
rime) (qp : q.Prime) : p ∣ q ↔ p = q
· 使用定理 `Nat.prime_two`：prime_two : Prime 2
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Prime.even_iff {p : ℕ} (hp : Prime p) : Even p ↔ p = 2 := by
  rw [even_iff_two_dvd, prime_dvd_prime_iff_eq prime_two hp, eq_comm]
/-
**Nat.Prime.odd_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：∀ {p : ℕ}, Nat.Prime p → (Odd p ↔ 3 ≤ p)
参数：Odd p ↔ 3 ≤ p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `Nat.not_odd_iff_even`：∀ {n : ℕ}, ¬Odd n ↔ Even n
· 使用定理 `Nat.Prime.even_iff`：∀ {p : ℕ}, Nat.Prime p → (Even p ↔ p = 2)
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
-/
theorem Prime.odd_iff {p : ℕ} (hp : Prime p) : Odd p ↔ 3 ≤ p := by
  rw [← not_iff_not, not_odd_iff_even, hp.even_iff, not_le]
  grind [hp.two_le]
/-
**Nat.Prime.odd_of_ne_two** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：∀ {p : ℕ}, Nat.Prime p → p ≠ 2 → Odd p
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Nat.Prime.eq_two_or_odd'`：∀ {p : ℕ}, Nat.Prime p → p = 2 ∨ Odd p
-/
theorem Prime.odd_of_ne_two {p : ℕ} (hp : p.Prime) (h_two : p ≠ 2) : Odd p :=
  hp.eq_two_or_odd'.resolve_left h_two
/-
**Nat.Prime.even_sub_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：∀ {p : ℕ}, Nat.Prime p → p ≠ 2 → Even (p - 1)
参数：p - 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Prime.odd_of_ne_two`：∀ {p : ℕ}, Nat.Prime p → p ≠ 2 → Odd p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.add_sub_cancel`：∀ (n m : ℕ), n + m - m = n
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
-/
theorem Prime.even_sub_one {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) : Even (p - 1) :=
  let ⟨n, hn⟩ := hp.odd_of_ne_two h2; ⟨n, by rw [hn, Nat.add_sub_cancel, two_mul]⟩

/-- A prime `p` satisfies `p % 2 = 1` if and only if `p ≠ 2`. -/
/-
**Nat.Prime.mod_two_eq_one_iff_ne_two** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：∀ {p : ℕ}, Nat.Prime p → (p % 2 = 1 ↔ p ≠ 2)
参数：p % 2 = 1 ↔ p ≠ 2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.mod_self`：∀ (n : ℕ), n % n = 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Nat.Prime.eq_two_or_odd`：∀ {p : ℕ}, Nat.Prime p → p = 2 ∨ p % 2 = 1

--- 原说明 ---
A prime `p` satisfies `p % 2 = 1` if and only if `p ≠ 2`.
-/
theorem Prime.mod_two_eq_one_iff_ne_two {p : ℕ} (hp : p.Prime) : p % 2 = 1 ↔ p ≠ 2 := by
  refine ⟨fun h hf => ?_, hp.eq_two_or_odd.resolve_left⟩
  rw [hf] at h
  simp at h
/-
**Nat.coprime_of_dvd'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：coprime_of_dvd' {m n : Nat} (H : forall k, Prime k -> k ∣ m -> k ∣ n -> k 
∣ 1) : Coprime m n
参数：H : forall k, Prime k -> k ∣ m -> k ∣ n -> k ∣ 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.coprime_of_dvd`：coprime_of_dvd {m n : Nat} (H : forall k, Prime k ->
 k ∣ m -> ¬k ∣ n) : Coprime m n
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
-/
theorem coprime_of_dvd' {m n : ℕ} (H : ∀ k, Prime k → k ∣ m → k ∣ n → k ∣ 1) : Coprime m n :=
  coprime_of_dvd fun k kp km kn => not_le_of_gt kp.one_lt <| le_of_dvd Nat.one_pos <| H k kp km kn
/-
**Nat.Prime.dvd_iff_not_coprime** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：∀ {p n : ℕ}, Nat.Prime p → (p ∣ n ↔ ¬p.Coprime n)
参数：p ∣ n ↔ ¬p.Coprime n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `iff_not_comm`：iff_not_comm : (a ↔ ¬b) ↔ (b ↔ ¬a)
· 使用定理 `Nat.Prime.coprime_iff_not_dvd`：∀ {p n : ℕ}, Nat.Prime p → (p.Coprime n ↔
 ¬p ∣ n)
-/
theorem Prime.dvd_iff_not_coprime {p n : ℕ} (pp : Prime p) : p ∣ n ↔ ¬Coprime p n :=
  iff_not_comm.2 pp.coprime_iff_not_dvd
/-
**Nat.Prime.not_coprime_iff_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：∀ {m n : ℕ}, ¬m.Coprime n ↔ ∃ p, Nat.Prime p ∧ p ∣ m ∧ p ∣ n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.minFac_prime`：minFac_prime {n : Nat} (n1 : n != 1) : Prime (minFac n
)
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `Nat.minFac_dvd`：minFac_dvd (n : Nat) : minFac n ∣ n
· 使用定理 `Nat.gcd_dvd_left`：∀ (m n : ℕ), m.gcd n ∣ m
· 使用定理 `Nat.gcd_dvd_right`：∀ (m n : ℕ), m.gcd n ∣ n
· 使用定理 `Nat.not_coprime_of_dvd_of_dvd`：∀ {d m n : ℕ}, 1 < d → d ∣ m → d ∣ n → ¬m
.Coprime n
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Prime.not_coprime_iff_dvd {m n : ℕ} : ¬Coprime m n ↔ ∃ p, Prime p ∧ p ∣ m ∧ p ∣ n := by
  apply Iff.intro
  · intro h
    exact
      ⟨minFac (gcd m n), minFac_prime h, (minFac_dvd (gcd m n)).trans (gcd_dvd_left m n),
        (minFac_dvd (gcd m n)).trans (gcd_dvd_right m n)⟩
  · intro h
    obtain ⟨p, hp⟩ := h
    apply Nat.not_coprime_of_dvd_of_dvd (Prime.one_lt hp.1) hp.2.1 hp.2.2

/-- If `0 < m < minFac n`, then `n` and `m` are coprime. -/
/-
**Nat.coprime_of_lt_minFac** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：coprime_of_lt_minFac {n m : Nat} (h₀ : m != 0) (h : m < minFac n) : Coprim
e n m
参数：h₀ : m != 0；h : m < minFac n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Nat.Prime.not_coprime_iff_dvd`：∀ {m n : ℕ}, ¬m.Coprime n ↔ ∃ p, Nat.Prim
e p ∧ p ∣ m ∧ p ∣ n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `LT.lt.false`：∀ {α : Type u_2} [inst : Preorder α] {a : α}, a < a → False
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Nat.minFac_le_of_dvd`：minFac_le_of_dvd {n : Nat} : forall {m : Nat}, 2 <
= m -> m ∣ n -> minFac n <= m
· 使用定理 `Nat.Prime.two_le`：∀ {p : ℕ}, Nat.Prime p → 2 ≤ p

--- 原说明 ---
If `0 < m < minFac n`, then `n` and `m` are coprime.
-/
lemma coprime_of_lt_minFac {n m : ℕ} (h₀ : m ≠ 0) (h : m < minFac n) : Coprime n m := by
  rw [← not_not (a := n.Coprime m), Prime.not_coprime_iff_dvd]
  push Not
  exact fun p hp hn hm ↦
    ((le_of_dvd (by lia) hm).trans_lt <| h.trans_le <| minFac_le_of_dvd hp.two_le hn).false

/-- If `0 < m < minFac n`, then `n` and `m` have gcd equal to `1`. -/
/-
**Nat.gcd_eq_one_of_lt_minFac** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：gcd_eq_one_of_lt_minFac {n m : Nat} (h₀ : m != 0) (h : m < minFac n) : n.g
cd m = 1
参数：h₀ : m != 0；h : m < minFac n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.coprime_iff_gcd_eq_one`：∀ {m n : ℕ}, m.Coprime n ↔ m.gcd n = 1
· 使用引理 `Nat.coprime_of_lt_minFac`：coprime_of_lt_minFac {n m : Nat} (h₀ : m != 0)
 (h : m < minFac n) : Coprime n m

--- 原说明 ---
If `0 < m < minFac n`, then `n` and `m` have gcd equal to `1`.
-/
lemma gcd_eq_one_of_lt_minFac {n m : ℕ} (h₀ : m ≠ 0) (h : m < minFac n) : n.gcd m = 1 :=
  coprime_iff_gcd_eq_one.mp <| coprime_of_lt_minFac h₀ h
/-
**Nat.Prime.not_dvd_mul** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：∀ {p m n : ℕ}, Nat.Prime p → ¬p ∣ m → ¬p ∣ n → ¬p ∣ m * n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.Prime.dvd_mul`：∀ {p m n : ℕ}, Nat.Prime p → (p ∣ m * n ↔ p ∣ m ∨ p ∣
 n)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem Prime.not_dvd_mul {p m n : ℕ} (pp : Prime p) (Hm : ¬p ∣ m) (Hn : ¬p ∣ n) : ¬p ∣ m * n :=
  mt pp.dvd_mul.1 <| by simp [Hm, Hn]
/-
**Nat.coprime_two_left** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {n : ℕ}, Nat.Coprime 2 n ↔ Odd n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.Prime.coprime_iff_not_dvd`：∀ {p n : ℕ}, Nat.Prime p → (p.Coprime n ↔
 ¬p ∣ n)
· 使用定理 `Nat.prime_two`：prime_two : Prime 2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.not_even_iff_odd`：∀ {n : ℕ}, ¬Even n ↔ Odd n
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `even_iff_two_dvd`：even_iff_two_dvd : Even a ↔ 2 ∣ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma coprime_two_left : Coprime 2 n ↔ Odd n := by
  rw [prime_two.coprime_iff_not_dvd, ← not_even_iff_odd, even_iff_two_dvd]
/-
**Nat.coprime_two_right** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {n : ℕ}, n.Coprime 2 ↔ Odd n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Nat.coprime_comm`：∀ {n m : ℕ}, n.Coprime m ↔ m.Coprime n
· 使用定理 `Nat.coprime_two_left`：∀ {n : ℕ}, Nat.Coprime 2 n ↔ Odd n
-/
@[simp] lemma coprime_two_right : n.Coprime 2 ↔ Odd n := coprime_comm.trans coprime_two_left

protected alias ⟨Coprime.odd_of_left, _root_.Odd.coprime_two_left⟩ := coprime_two_left
protected alias ⟨Coprime.odd_of_right, _root_.Odd.coprime_two_right⟩ := coprime_two_right
/-
**Nat.Prime.dvd_of_dvd_pow** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：∀ {p m n : ℕ}, Nat.Prime p → p ∣ m ^ n → p ∣ m
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prime.dvd_of_dvd_pow`：dvd_of_dvd_pow {a : M} {n : Nat} (h : p ∣ a ^ n) :
 p ∣ a
· 使用定理 `Nat.Prime.prime`：∀ {p : ℕ}, Nat.Prime p → Prime p
-/
theorem Prime.dvd_of_dvd_pow {p m n : ℕ} (pp : Prime p) (h : p ∣ m ^ n) : p ∣ m :=
  pp.prime.dvd_of_dvd_pow h
/-
**Nat.Prime.not_prime_pow'** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：∀ {x n : ℕ}, n ≠ 1 → ¬Nat.Prime (x ^ n)
参数：x ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `not_irreducible_pow`：not_irreducible_pow : forall {n : Nat}, n != 1 -> ¬
 Irreducible (x ^ n) | 0, _ => by simp | n + 2, _ => by intro ⟨h₁, h₂⟩ have
-/
theorem Prime.not_prime_pow' {x n : ℕ} (hn : n ≠ 1) : ¬(x ^ n).Prime :=
  not_irreducible_pow hn
/-
**Nat.Prime.not_prime_pow** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：∀ {x n : ℕ}, 2 ≤ n → ¬Nat.Prime (x ^ n)
参数：x ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Prime.not_prime_pow'`：∀ {x n : ℕ}, n ≠ 1 → ¬Nat.Prime (x ^ n)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.two_le_iff`：∀ (n : ℕ), 2 ≤ n ↔ n ≠ 0 ∧ n ≠ 1
-/
theorem Prime.not_prime_pow {x n : ℕ} (hn : 2 ≤ n) : ¬(x ^ n).Prime :=
  not_prime_pow' ((two_le_iff _).mp hn).2
/-
**Nat.Prime.eq_one_of_pow** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：∀ {x n : ℕ}, Nat.Prime (x ^ n) → n = 1
参数：x ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_imp_not`：not_imp_not : ¬a -> ¬b ↔ b -> a
· 使用定理 `Nat.Prime.not_prime_pow'`：∀ {x n : ℕ}, n ≠ 1 → ¬Nat.Prime (x ^ n)
-/
theorem Prime.eq_one_of_pow {x n : ℕ} (h : (x ^ n).Prime) : n = 1 :=
  not_imp_not.mp Prime.not_prime_pow' h
/-
**Nat.Prime.pow_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：∀ {p a k : ℕ}, Nat.Prime p → (a ^ k = p ↔ a = p ∧ k = 1)
参数：a ^ k = p ↔ a = p ∧ k = 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.Prime.eq_one_of_pow`：∀ {x n : ℕ}, Nat.Prime (x ^ n) → n = 1
· 使用定理 `eq_self_iff_true`：∀ {α : Sort u_1} (a : α), a = a ↔ True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Prime.pow_eq_iff {p a k : ℕ} (hp : p.Prime) : a ^ k = p ↔ a = p ∧ k = 1 := by
  refine ⟨fun h => ?_, fun h => by rw [h.1, h.2, pow_one]⟩
  rw [← h] at hp
  rw [← h, hp.eq_one_of_pow, eq_self_iff_true, _root_.and_true, pow_one]
/-
**Nat.Prime.mul_eq_prime_sq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：∀ {x y p : ℕ}, Nat.Prime p → x ≠ 1 → y ≠ 1 → (x * y = p ^ 2 ↔ x = p ∧ y = 
p)
参数：x * y = p ^ 2 ↔ x = p ∧ y = p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用引理 `mul_right_inj'`：mul_right_inj' (ha : a != 0) : a * b = a * c ↔ b = c
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.dvd_prime`：dvd_prime {p m : Nat} (pp : Prime p) : m ∣ p ↔ m = 1 ∨ m 
= p
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.mul_eq_left`：∀ {a b : ℕ}, a ≠ 0 → (a * b = a ↔ b = 1)
· 使用定理 `Nat.mul_ne_zero`：∀ {n m : ℕ}, n ≠ 0 → m ≠ 0 → n * m ≠ 0
· 使用定理 `Nat.Prime.dvd_mul`：∀ {p m n : ℕ}, Nat.Prime p → (p ∣ m * n ↔ p ∣ m ∨ p ∣
 n)
· 使用定理 `And.comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem Prime.mul_eq_prime_sq_iff {x y p : ℕ} (hp : p.Prime) (hx : x ≠ 1) (hy : y ≠ 1) :
    x * y = p ^ 2 ↔ x = p ∧ y = p := by
  refine ⟨fun h => ?_, fun ⟨h₁, h₂⟩ => h₁.symm ▸ h₂.symm ▸ (sq _).symm⟩
  have pdvdxy : p ∣ x * y := by rw [h]; simp [sq]
  -- Could be `wlog := hp.dvd_mul.1 pdvdxy using x y`, but that imports more than we want.
  suffices ∀ x' y' : ℕ, x' ≠ 1 → y' ≠ 1 → x' * y' = p ^ 2 → p ∣ x' → x' = p ∧ y' = p by
    obtain hx | hy := hp.dvd_mul.1 pdvdxy <;>
      [skip; rw [And.comm]] <;>
      [skip; rw [mul_comm] at h pdvdxy] <;>
      apply this <;>
      assumption
  rintro x y hx hy h ⟨a, ha⟩
  have : a ∣ p := ⟨y, by rwa [ha, sq, mul_assoc, mul_right_inj' hp.ne_zero, eq_comm] at h⟩
  obtain rfl | hap := (Nat.dvd_prime hp).mp ‹a ∣ p›
  · rw [mul_one] at ha
    subst ha
    simp only [sq, mul_right_inj' hp.ne_zero] at h
    subst h
    exact ⟨rfl, rfl⟩
  · refine (hy ?_).elim
    subst hap
    subst ha
    rw [sq, Nat.mul_eq_left (Nat.mul_ne_zero hp.ne_zero hp.ne_zero)] at h
    exact h
/-
**Nat.Prime.coprime_pow_of_not_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：∀ {p m a : ℕ}, Nat.Prime p → ¬p ∣ a → a.Coprime (p ^ m)
参数：p ^ m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Coprime.pow_right`：∀ {k m : ℕ} (n : ℕ), k.Coprime m → k.Coprime (m ^
 n)
· 使用定理 `Nat.Coprime.symm`：∀ {n m : ℕ}, n.Coprime m → m.Coprime n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.Prime.coprime_iff_not_dvd`：∀ {p n : ℕ}, Nat.Prime p → (p.Coprime n ↔
 ¬p ∣ n)
-/
theorem Prime.coprime_pow_of_not_dvd {p m a : ℕ} (pp : Prime p) (h : ¬p ∣ a) : Coprime a (p ^ m) :=
  (pp.coprime_iff_not_dvd.2 h).symm.pow_right _
/-
**Nat.coprime_primes** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：coprime_primes {p q : Nat} (pp : Prime p) (pq : Prime q) : Coprime p q ↔ p
 != q
参数：pp : Prime p；pq : Prime q。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Nat.Prime.coprime_iff_not_dvd`：∀ {p n : ℕ}, Nat.Prime p → (p.Coprime n ↔
 ¬p ∣ n)
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Nat.dvd_prime_two_le`：dvd_prime_two_le {p m : Nat} (pp : Prime p) (H : 2
 <= m) : m ∣ p ↔ m = p
· 使用定理 `Nat.Prime.two_le`：∀ {p : ℕ}, Nat.Prime p → 2 ≤ p
-/
theorem coprime_primes {p q : ℕ} (pp : Prime p) (pq : Prime q) : Coprime p q ↔ p ≠ q :=
  pp.coprime_iff_not_dvd.trans <| not_congr <| dvd_prime_two_le pq pp.two_le
/-
**Nat.coprime_pow_primes** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：coprime_pow_primes {p q : Nat} (n m : Nat) (pp : Prime p) (pq : Prime q) (
h : p != q) : Coprime (p ^ n) (q ^ m)
参数：n m : Nat；pp : Prime p；pq : Prime q；h : p != q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Coprime.pow`：∀ {k l : ℕ} (m n : ℕ), k.Coprime l → (k ^ m).Coprime (l
 ^ n)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.coprime_primes`：coprime_primes {p q : Nat} (pp : Prime p) (pq : Prim
e q) : Coprime p q ↔ p != q
-/
theorem coprime_pow_primes {p q : ℕ} (n m : ℕ) (pp : Prime p) (pq : Prime q) (h : p ≠ q) :
    Coprime (p ^ n) (q ^ m) :=
  ((coprime_primes pp pq).2 h).pow _ _
/-
**Nat.coprime_or_dvd_of_prime** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：coprime_or_dvd_of_prime {p} (pp : Prime p) (i : Nat) : Coprime p i ∨ p ∣ i
参数：pp : Prime p；i : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.Prime.dvd_iff_not_coprime`：∀ {p n : ℕ}, Nat.Prime p → (p ∣ n ↔ ¬p.Co
prime n)
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
-/
theorem coprime_or_dvd_of_prime {p} (pp : Prime p) (i : ℕ) : Coprime p i ∨ p ∣ i := by
  rw [pp.dvd_iff_not_coprime]; apply em
/-
**Nat.coprime_of_lt_prime** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：coprime_of_lt_prime {n p} (ne_zero : n != 0) (hlt : n < p) (pp : Prime p) 
: Coprime p n
参数：ne_zero : n != 0；hlt : n < p；pp : Prime p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `Nat.coprime_or_dvd_of_prime`：coprime_or_dvd_of_prime {p} (pp : Prime p) 
(i : Nat) : Coprime p i ∨ p ∣ i
· 使用定理 `Nat.lt_le_asymm`：∀ {a b : ℕ}, a < b → ¬b ≤ a
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
-/
theorem coprime_of_lt_prime {n p} (ne_zero : n ≠ 0) (hlt : n < p) (pp : Prime p) : Coprime p n :=
  (coprime_or_dvd_of_prime pp n).resolve_right fun h => Nat.lt_le_asymm hlt
    (le_of_dvd (Nat.pos_of_ne_zero ne_zero) h)
/-
**Nat.eq_or_coprime_of_le_prime** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：eq_or_coprime_of_le_prime {n p} (ne_zero : n != 0) (hle : n <= p) (pp : Pr
ime p) : p = n ∨ Coprime p n
参数：ne_zero : n != 0；hle : n <= p；pp : Prime p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.coprime_of_lt_prime`：coprime_of_lt_prime {n p} (ne_zero : n != 0) (h
lt : n < p) (pp : Prime p) : Coprime p n
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
-/
theorem eq_or_coprime_of_le_prime {n p} (ne_zero : n ≠ 0) (hle : n ≤ p) (pp : Prime p) :
    p = n ∨ Coprime p n :=
  hle.eq_or_lt.imp Eq.symm fun h => coprime_of_lt_prime ne_zero h pp
/-
**Nat.prime_eq_prime_of_dvd_pow** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：prime_eq_prime_of_dvd_pow {m p q} (pp : Prime p) (pq : Prime q) (h : p ∣ q
 ^ m) : p = q
参数：pp : Prime p；pq : Prime q；h : p ∣ q ^ m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.prime_dvd_prime_iff_eq`：prime_dvd_prime_iff_eq {p q : Nat} (pp : p.P
rime) (qp : q.Prime) : p ∣ q ↔ p = q
· 使用定理 `Nat.Prime.dvd_of_dvd_pow`：∀ {p m n : ℕ}, Nat.Prime p → p ∣ m ^ n → p ∣ m
-/
theorem prime_eq_prime_of_dvd_pow {m p q} (pp : Prime p) (pq : Prime q) (h : p ∣ q ^ m) : p = q :=
  (prime_dvd_prime_iff_eq pp pq).mp (pp.dvd_of_dvd_pow h)
/-
**Nat.dvd_prime_pow** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：dvd_prime_pow {p : Nat} (pp : Prime p) {m i : Nat} : i ∣ p ^ m ↔ exists k 
<= m, i = p ^ k
参数：pp : Prime p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dvd_prime_pow`：dvd_prime_pow [CommMonoidWithZero M] [IsCancelMulZero M] 
{p q : M} (hp : Prime p) (n : Nat) : q ∣ p ^ n ↔ exists i <= n, Associated q (p 
^ i…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.prime_iff`：prime_iff {p : Nat} : p.Prime ↔ _root_.Prime p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `associated_eq_eq`：associated_eq_eq : (Associated : M -> M -> Prop) = Eq
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem dvd_prime_pow {p : ℕ} (pp : Prime p) {m i : ℕ} : i ∣ p ^ m ↔ ∃ k ≤ m, i = p ^ k := by
  simp_rw [_root_.dvd_prime_pow (prime_iff.mp pp) m, associated_eq_eq]
/-
**Nat.Prime.dvd_mul_of_dvd_ne** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：∀ {p1 p2 n : ℕ}, p1 ≠ p2 → Nat.Prime p1 → Nat.Prime p2 → p1 ∣ n → p2 ∣ n →
 p1 * p2 ∣ n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Coprime.mul_dvd_of_dvd_of_dvd`：∀ {m n a : ℕ}, m.Coprime n → m ∣ a → 
n ∣ a → m * n ∣ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.coprime_primes`：coprime_primes {p q : Nat} (pp : Prime p) (pq : Prim
e q) : Coprime p q ↔ p != q
-/
theorem Prime.dvd_mul_of_dvd_ne {p1 p2 n : ℕ} (h_ne : p1 ≠ p2) (pp1 : Prime p1) (pp2 : Prime p2)
    (h1 : p1 ∣ n) (h2 : p2 ∣ n) : p1 * p2 ∣ n :=
  Coprime.mul_dvd_of_dvd_of_dvd ((coprime_primes pp1 pp2).mpr h_ne) h1 h2

/-- If `p` is prime,
and `a` doesn't divide `p^k`, but `a` does divide `p^(k+1)`
then `a = p^(k+1)`.
-/
/-
**Nat.eq_prime_pow_of_dvd_least_prime_pow** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：eq_prime_pow_of_dvd_least_prime_pow {a p k : Nat} (pp : Prime p) (h₁ : ¬a 
∣ p ^ k) (h₂ : a ∣ p ^ (k + 1)) : a = p ^ (k + 1)
参数：pp : Prime p；h₁ : ¬a ∣ p ^ k；h₂ : a ∣ p ^ (k + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.dvd_prime_pow`：dvd_prime_pow {p : Nat} (pp : Prime p) {m i : Nat} : 
i ∣ p ^ m ↔ exists k <= m, i = p ^ k
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Nat.pow_dvd_pow_iff_le_right`：∀ {x k l : ℕ}, 1 < x → (x ^ k ∣ x ^ l ↔ k 
≤ l)
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If `p` is prime,
and `a` doesn't divide `p^k`, but `a` does divide `p^(k+1)`
then `a = p^(k+1)`.
-/
theorem eq_prime_pow_of_dvd_least_prime_pow {a p k : ℕ} (pp : Prime p) (h₁ : ¬a ∣ p ^ k)
    (h₂ : a ∣ p ^ (k + 1)) : a = p ^ (k + 1) := by
  obtain ⟨l, ⟨h, rfl⟩⟩ := (dvd_prime_pow pp).1 h₂
  congr
  exact le_antisymm h (not_le.1 ((not_congr (pow_dvd_pow_iff_le_right (Prime.one_lt pp))).1 h₁))
/-
**Nat.ne_one_iff_exists_prime_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ne_one_iff_exists_prime_dvd : forall {n}, n != 1 ↔ exists p : Nat, p.Prime
 ∧ p ∣ n | 0 => by simpa using Exists.intro 2 Nat.prime_two | 1 => by simp [Nat.
not_prime_one] | n + 2 => by let a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
· 使用定理 `Nat.prime_two`：prime_two : Prime 2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Nat.succ_succ_ne_one`：∀ (a : ℕ), a.succ.succ ≠ 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Nat.minFac_prime`：minFac_prime {n : Nat} (n1 : n != 1) : Prime (minFac n
)
· 使用定理 `Nat.minFac_dvd`：minFac_dvd (n : Nat) : minFac n ∣ n
-/
theorem ne_one_iff_exists_prime_dvd : ∀ {n}, n ≠ 1 ↔ ∃ p : ℕ, p.Prime ∧ p ∣ n
  | 0 => by simpa using Exists.intro 2 Nat.prime_two
  | 1 => by simp [Nat.not_prime_one]
  | n + 2 => by
    let a := n + 2
    have ha : a ≠ 1 := Nat.succ_succ_ne_one n
    simp only [a, true_iff, Ne, not_false_iff, ha]
    exact ⟨a.minFac, Nat.minFac_prime ha, a.minFac_dvd⟩
/-
**Nat.eq_one_iff_not_exists_prime_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：eq_one_iff_not_exists_prime_dvd {n : Nat} : n = 1 ↔ forall p : Nat, p.Prim
e -> ¬p ∣ n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `Nat.ne_one_iff_exists_prime_dvd`：ne_one_iff_exists_prime_dvd : forall {n
}, n != 1 ↔ exists p : Nat, p.Prime ∧ p ∣ n | 0 => by simpa using Exists.intro 2
 Nat.prime_two | 1 =>…
-/
theorem eq_one_iff_not_exists_prime_dvd {n : ℕ} : n = 1 ↔ ∀ p : ℕ, p.Prime → ¬p ∣ n := by
  simpa using not_iff_not.mpr ne_one_iff_exists_prime_dvd
/-
**Nat.succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul {p : Nat} (p_prime : Prime p) {m 
n k l : Nat} (hpm : p ^ k ∣ m) (hpn : p ^ l ∣ n) (hpmn : p ^ (k + l + 1) ∣ m * n
) : p ^ (k + 1) ∣ m ∨ p ^ (l + 1) ∣ n
参数：p_prime : Prime p；hpm : p ^ k ∣ m；hpn : p ^ l ∣ n；hpmn : p ^ (k + l + 1) ∣ m 
* n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.dvd_div_of_mul_dvd`：∀ {a b c : ℕ}, a * b ∣ c → b ∣ c / a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `Nat.div_mul_div_comm`：∀ {a b c d : ℕ}, b ∣ a → d ∣ c → a / b * (c / d) =
 a * c / (b * d)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.Prime.dvd_mul`：∀ {p m n : ℕ}, Nat.Prime p → (p ∣ m * n ↔ p ∣ m ∨ p ∣
 n)
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Nat.mul_dvd_of_dvd_div`：∀ {a b c : ℕ}, c ∣ b → a ∣ b / c → c * a ∣ b
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
-/
theorem succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul {p : ℕ} (p_prime : Prime p) {m n k l : ℕ}
    (hpm : p ^ k ∣ m) (hpn : p ^ l ∣ n) (hpmn : p ^ (k + l + 1) ∣ m * n) :
    p ^ (k + 1) ∣ m ∨ p ^ (l + 1) ∣ n := by
  have hpd : p ^ (k + l) * p ∣ m * n := by
      let hpmn' : p ^ (succ (k + l)) ∣ m * n := hpmn
      rwa [pow_succ'] at hpmn'
  have hpd2 : p ∣ m * n / p ^ (k + l) := dvd_div_of_mul_dvd hpd
  have hpd3 : p ∣ m * n / (p ^ k * p ^ l) := by simpa [pow_add] using hpd2
  have hpd4 : p ∣ m / p ^ k * (n / p ^ l) := by simpa [Nat.div_mul_div_comm hpm hpn] using hpd3
  have hpd5 : p ∣ m / p ^ k ∨ p ∣ n / p ^ l :=
    (Prime.dvd_mul p_prime).1 hpd4
  suffices p ^ k * p ∣ m ∨ p ^ l * p ∣ n by rwa [_root_.pow_succ, _root_.pow_succ]
  exact hpd5.elim (fun h : p ∣ m / p ^ k => Or.inl <| mul_dvd_of_dvd_div hpm h)
    fun h : p ∣ n / p ^ l => Or.inr <| mul_dvd_of_dvd_div hpn h

end Nat

