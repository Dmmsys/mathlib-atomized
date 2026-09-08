/-
Copyright (c) 2025 Yongshun Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongshun Ye
-/
module

public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Data.Nat.Prime.Defs

/-!
# Lemmas related to `Nat.Prime` and `lcm`

This file contains lemmas related to `Nat.Prime`.
These lemmas are kept separate from `Mathlib/Data/Nat/GCD/Basic.lean` in order to minimize imports.

## Main results

- `Nat.Prime.dvd_or_dvd_of_dvd_lcm`: If `p ∣ lcm a b`, then `p ∣ a ∨ p ∣ b`.
- `Nat.Prime.dvd_lcm`: `p ∣ lcm a b ↔ p ∣ a ∨ p ∣ b`.
- `Nat.Prime.not_dvd_lcm`: If `p ∤ a` and `p ∤ b`, then `p ∤ lcm a b`.

-/

public section

namespace Nat

namespace Prime
variable {p a b : ℕ} (hp : Prime p)

include hp

/-
**Nat.Prime.dvd_or_dvd_of_dvd_lcm** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：dvd_or_dvd_of_dvd_lcm (h : p ∣ lcm a b) : p ∣ a ∨ p ∣ b
参数：h : p ∣ lcm a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Prime.dvd_or_dvd`：∀ {p m n : ℕ}, Nat.Prime p → p ∣ m * n → p ∣ m ∨ p
 ∣ n
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `Nat.lcm_dvd_mul`：∀ (m n : ℕ), m.lcm n ∣ m * n
-/
theorem dvd_or_dvd_of_dvd_lcm (h : p ∣ lcm a b) : p ∣ a ∨ p ∣ b :=
  dvd_or_dvd hp (h.trans (lcm_dvd_mul a b))
/-
**Nat.Prime.dvd_lcm** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：dvd_lcm : p ∣ lcm a b ↔ p ∣ a ∨ p ∣ b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Prime.dvd_or_dvd_of_dvd_lcm`：dvd_or_dvd_of_dvd_lcm (h : p ∣ lcm a b)
 : p ∣ a ∨ p ∣ b
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Nat.dvd_lcm_of_dvd_left`：dvd_lcm_of_dvd_left (h : a ∣ b) (c : Nat) : a ∣
 lcm b c
· 使用定理 `Nat.dvd_lcm_of_dvd_right`：dvd_lcm_of_dvd_right {a b : Nat} (h : a ∣ b) (
c : Nat) : a ∣ lcm c b
-/
theorem dvd_lcm : p ∣ lcm a b ↔ p ∣ a ∨ p ∣ b :=
  ⟨hp.dvd_or_dvd_of_dvd_lcm, (Or.elim · (dvd_lcm_of_dvd_left · _) (dvd_lcm_of_dvd_right · _))⟩
/-
**Nat.Prime.not_dvd_lcm** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Prime`。
形式化陈述：not_dvd_lcm (ha : ¬ p ∣ a) (hb : ¬ p ∣ b) : ¬ p ∣ lcm a b
参数：ha : ¬ p ∣ a；hb : ¬ p ∣ b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Nat.Prime.dvd_lcm`：dvd_lcm : p ∣ lcm a b ↔ p ∣ a ∨ p ∣ b
· 使用定理 `not_or`：∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q
-/
theorem not_dvd_lcm (ha : ¬ p ∣ a) (hb : ¬ p ∣ b) : ¬ p ∣ lcm a b :=
  hp.dvd_lcm.not.mpr <| not_or.mpr ⟨ha, hb⟩

end Prime

end Nat

