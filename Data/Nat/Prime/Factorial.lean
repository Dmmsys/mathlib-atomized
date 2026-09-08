/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module

public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Prime.Basic
/-!
# Prime natural numbers and the factorial operator

-/

public section

open Bool Subtype

open Nat

namespace Nat

/-
**Nat.Prime.dvd_factorial** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：∀ {n p : ℕ}, Nat.Prime p → (p ∣ n.factorial ↔ p ≤ n)
参数：p ∣ n.factorial ↔ p ≤ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Prime.dvd_factorial : ∀ {n p : ℕ} (_ : Prime p), p ∣ n ! ↔ p ≤ n
  | 0, _, hp => iff_of_false hp.not_dvd_one (not_le_of_gt hp.pos)
  | n + 1, p, hp => by
    rw [factorial_succ, hp.dvd_mul, Prime.dvd_factorial hp]
    exact
      ⟨fun h => h.elim (le_of_dvd (succ_pos _)) le_succ_of_le, fun h =>
        (_root_.lt_or_eq_of_le h).elim (Or.inr ∘ le_of_lt_succ) fun h => Or.inl <| by rw [h]⟩
/-
**Nat.coprime_factorial_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：coprime_factorial_iff {m n : Nat} (hm : m != 1) : m.Coprime n ! ↔ n < m.mi
nFac
参数：hm : m != 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `iff_not_comm`：iff_not_comm : (a ↔ ¬b) ↔ (b ↔ ¬a)
· 使用定理 `Nat.Prime.not_coprime_iff_dvd`：∀ {m n : ℕ}, ¬m.Coprime n ↔ ∃ p, Nat.Prim
e p ∧ p ∣ m ∧ p ∣ n
· 使用定理 `Nat.minFac_prime`：minFac_prime {n : Nat} (n1 : n != 1) : Prime (minFac n
)
· 使用定理 `Nat.minFac_dvd`：minFac_dvd (n : Nat) : minFac n ∣ n
· 使用定理 `Nat.dvd_factorial`：∀ {m n : ℕ}, 0 < m → m ≤ n → m ∣ n.factorial
· 使用定理 `Nat.minFac_pos`：minFac_pos (n : Nat) : 0 < minFac n
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Nat.minFac_le_of_dvd`：minFac_le_of_dvd {n : Nat} : forall {m : Nat}, 2 <
= m -> m ∣ n -> minFac n <= m
· 使用定理 `Nat.Prime.two_le`：∀ {p : ℕ}, Nat.Prime p → 2 ≤ p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.Prime.dvd_factorial`：∀ {n p : ℕ}, Nat.Prime p → (p ∣ n.factorial ↔ p
 ≤ n)
-/
theorem coprime_factorial_iff {m n : ℕ} (hm : m ≠ 1) :
    m.Coprime n ! ↔ n < m.minFac := by
  rw [← not_le, iff_not_comm, Nat.Prime.not_coprime_iff_dvd]
  constructor
  · intro h
    exact ⟨m.minFac, minFac_prime hm, minFac_dvd m, Nat.dvd_factorial (minFac_pos m) h⟩
  · rintro ⟨p, hp, hdvd, hdvd'⟩
    exact le_trans (minFac_le_of_dvd hp.two_le hdvd) (hp.dvd_factorial.mp hdvd')
/-
**Nat.Prime.coprime_factorial_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：∀ {p n : ℕ}, Nat.Prime p → n < p → p.Coprime n.factorial
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.Prime.coprime_iff_not_dvd`：∀ {p n : ℕ}, Nat.Prime p → (p.Coprime n ↔
 ¬p ∣ n)
· 使用定理 `Nat.Prime.dvd_factorial`：∀ {n p : ℕ}, Nat.Prime p → (p ∣ n.factorial ↔ p
 ≤ n)
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
-/
lemma Prime.coprime_factorial_of_lt {p n : ℕ} (hp : p.Prime) (hn : n < p) :
    p.Coprime n.factorial := by
  rwa [hp.coprime_iff_not_dvd, hp.dvd_factorial, not_le]
/-
**Nat.Prime.coprime_descFactorial_of_lt_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Pri
me`。
形式化陈述：∀ {p n k : ℕ}, Nat.Prime p → n < p → k ≤ n → p.Coprime (n.descFactorial k)
参数：n.descFactorial k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.descFactorial_eq_div`：descFactorial_eq_div {n k : Nat} (h : k <= n) 
: n.descFactorial k = n ! / (n - k)!
· 使用定理 `Nat.Coprime.coprime_div_right`：∀ {m n a : ℕ}, m.Coprime n → a ∣ n → m.Co
prime (n / a)
· 使用定理 `Nat.Prime.coprime_factorial_of_lt`：∀ {p n : ℕ}, Nat.Prime p → n < p → p.
Coprime n.factorial
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma Prime.coprime_descFactorial_of_lt_of_le {p n k : ℕ} (hp : p.Prime) (hn : n < p) (hk : k ≤ n) :
    p.Coprime (n.descFactorial k) := by
  rw [Nat.descFactorial_eq_div hk]
  refine (hp.coprime_factorial_of_lt hn).coprime_div_right ?_
  simp [Nat.factorial_dvd_factorial]

end Nat

