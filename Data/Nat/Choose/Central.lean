/-
Copyright (c) 2021 Patrick Stevens. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Stevens, Thomas Browning
-/
module

public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-!
# Central binomial coefficients

This file proves properties of the central binomial coefficients (that is, `Nat.choose (2 * n) n`).

## Main definition and results

* `Nat.centralBinom`: the central binomial coefficient, `(2 * n).choose n`.
* `Nat.succ_mul_centralBinom_succ`: the inductive relationship between successive central binomial
  coefficients.
* `Nat.four_pow_lt_mul_centralBinom`: an exponential lower bound on the central binomial
  coefficient.
* `succ_dvd_centralBinom`: The result that `n+1 ∣ n.centralBinom`, ensuring that the explicit
  definition of the Catalan numbers is integer-valued.
-/

@[expose] public section


namespace Nat

/-- The central binomial coefficient, `Nat.choose (2 * n) n`.
-/
/-
**Nat.centralBinom** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：centralBinom (n : Nat)
参数：n : Nat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The central binomial coefficient, `Nat.choose (2 * n) n`.
-/
def centralBinom (n : ℕ) :=
  (2 * n).choose n
/-
**Nat.centralBinom_eq_two_mul_choose** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：centralBinom_eq_two_mul_choose (n : Nat) : centralBinom n = (2 * n).choose
 n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem centralBinom_eq_two_mul_choose (n : ℕ) : centralBinom n = (2 * n).choose n :=
  rfl
/-
**Nat.centralBinom_pos** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：centralBinom_pos (n : Nat) : 0 < centralBinom n
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.choose_pos`：∀ {n k : ℕ}, k ≤ n → 0 < n.choose k
· 使用定理 `Nat.le_mul_of_pos_left`：∀ {n : ℕ} (m : ℕ), 0 < n → m ≤ n * m
· 使用定理 `zero_lt_two`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Part
ialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem centralBinom_pos (n : ℕ) : 0 < centralBinom n :=
  choose_pos (Nat.le_mul_of_pos_left _ zero_lt_two)
/-
**Nat.centralBinom_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：centralBinom_ne_zero (n : Nat) : centralBinom n != 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.centralBinom_pos`：centralBinom_pos (n : Nat) : 0 < centralBinom n
-/
theorem centralBinom_ne_zero (n : ℕ) : centralBinom n ≠ 0 :=
  (centralBinom_pos n).ne'

@[simp]
/-
**Nat.centralBinom_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：centralBinom_zero : centralBinom 0 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.choose_zero_right`：choose_zero_right (n : Nat) : choose n 0 = 1
-/
theorem centralBinom_zero : centralBinom 0 = 1 :=
  choose_zero_right _

/-- The central binomial coefficient is the largest binomial coefficient.
-/
/-
**Nat.choose_le_centralBinom** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：choose_le_centralBinom (r n : Nat) : choose (2 * n) r <= centralBinom n
参数：r n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.choose_le_middle`：choose_le_middle (r n : Nat) : choose n r <= choos
e n (n / 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.mul_div_cancel_left`：∀ (m : ℕ) {n : ℕ}, 0 < n → n * m / n = m
· 使用定理 `zero_lt_two`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Part
ialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α

--- 原说明 ---
The central binomial coefficient is the largest binomial coefficient.
-/
theorem choose_le_centralBinom (r n : ℕ) : choose (2 * n) r ≤ centralBinom n :=
  calc
    (2 * n).choose r ≤ (2 * n).choose (2 * n / 2) := choose_le_middle r (2 * n)
    _ = (2 * n).choose n := by rw [Nat.mul_div_cancel_left n zero_lt_two]
/-
**Nat.centralBinom_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：centralBinom_strictMono : StrictMono centralBinom
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `strictMono_nat_of_lt_succ`：strictMono_nat_of_lt_succ {f : Nat -> α} (hf 
: forall n, f n < f (n + 1)) : StrictMono f
-/
theorem centralBinom_strictMono : StrictMono centralBinom :=
  strictMono_nat_of_lt_succ (by grind [Nat.choose_pos, centralBinom])
/-
**Nat.two_le_centralBinom** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：two_le_centralBinom (n : Nat) (n_pos : 0 < n) : 2 <= centralBinom n
参数：n : Nat；n_pos : 0 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_mul_of_pos_right`：∀ {m : ℕ} (n : ℕ), 0 < m → n ≤ n * m
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nat.choose_one_right`：choose_one_right (n : Nat) : choose n 1 = n
· 使用定理 `Nat.choose_le_centralBinom`：choose_le_centralBinom (r n : Nat) : choose 
(2 * n) r <= centralBinom n
-/
theorem two_le_centralBinom (n : ℕ) (n_pos : 0 < n) : 2 ≤ centralBinom n :=
  calc
    2 ≤ 2 * n := Nat.le_mul_of_pos_right _ n_pos
    _ = (2 * n).choose 1 := (choose_one_right (2 * n)).symm
    _ ≤ centralBinom n := choose_le_centralBinom 1 n
/-
**Nat.centralBinom_le_four_pow** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：centralBinom_le_four_pow (n : Nat) : centralBinom n <= 4 ^ n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `Nat.centralBinom_eq_two_mul_choose`：centralBinom_eq_two_mul_choose (n : 
Nat) : centralBinom n = (2 * n).choose n
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `Nat.choose_le_two_pow`：choose_le_two_pow (n k : Nat) : n.choose k <= 2 ^
 n
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem centralBinom_le_four_pow (n : ℕ) : centralBinom n ≤ 4 ^ n := by
  grw [show 4 = 2 ^ 2 by rfl, ← pow_mul, centralBinom_eq_two_mul_choose, choose_le_two_pow]
/-
**Nat.centralBinom_lt_four_pow** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：centralBinom_lt_four_pow {n : Nat} (h : n != 0) : centralBinom n < 4 ^ n
参数：h : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `Nat.choose_lt_two_pow`：choose_lt_two_pow (n k : Nat) (p : 0 < n) : n.cho
ose k < 2 ^ n
-/
theorem centralBinom_lt_four_pow {n : ℕ} (h : n ≠ 0) : centralBinom n < 4 ^ n := by
  rw [show 4 = 2 ^ 2 by rfl, ← pow_mul]
  apply choose_lt_two_pow
  lia

/-- An inductive property of the central binomial coefficient.
-/
/-
**Nat.succ_mul_centralBinom_succ** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：succ_mul_centralBinom_succ (n : Nat) : (n + 1) * centralBinom (n + 1) = 2 
* (2 * n + 1) * centralBinom n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.choose_succ_right_eq`：choose_succ_right_eq (n k : Nat) : choose n (k
 + 1) * (k + 1) = choose n k * (n - k)
· 使用定理 `Nat.choose_mul_succ_eq`：choose_mul_succ_eq (n k : Nat) : n.choose k * (n
 + 1) = (n + 1).choose k * (n + 1 - k)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Nat.add_sub_cancel_left`：∀ (n m : ℕ), n + m - n = m
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)

--- 原说明 ---
An inductive property of the central binomial coefficient.
-/
theorem succ_mul_centralBinom_succ (n : ℕ) :
    (n + 1) * centralBinom (n + 1) = 2 * (2 * n + 1) * centralBinom n :=
  calc
    (n + 1) * (2 * (n + 1)).choose (n + 1) = (2 * n + 2).choose (n + 1) * (n + 1) := mul_comm _ _
    _ = (2 * n + 1).choose n * (2 * n + 2) := by rw [choose_succ_right_eq, choose_mul_succ_eq]
    _ = 2 * ((2 * n + 1).choose n * (n + 1)) := by ring
    _ = 2 * ((2 * n + 1).choose n * (2 * n + 1 - n)) := by rw [two_mul n, add_assoc,
                                                               Nat.add_sub_cancel_left]
    _ = 2 * ((2 * n).choose n * (2 * n + 1)) := by rw [choose_mul_succ_eq]
    _ = 2 * (2 * n + 1) * (2 * n).choose n := by rw [mul_assoc, mul_comm (2 * n + 1)]

/-- An exponential lower bound on the central binomial coefficient.
This bound is of interest because it appears in
[Tochiori's refinement of Erdős's proof of Bertrand's postulate](tochiori_bertrand).
-/
/-
**Nat.four_pow_lt_mul_centralBinom** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：four_pow_lt_mul_centralBinom (n : Nat) (n_big : 4 <= n) : 4 ^ n < n * cent
ralBinom n
参数：n : Nat；n_big : 4 <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.strong_induction_on`：∀ {p : ℕ → Prop} (n : ℕ), (∀ (n : ℕ), (∀ m < n,
 p m) → p n) → p n
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_eq`：∀ {α : Type u} [inst : AddMonoidWithOn
e α] {n : ℕ} {a a' : α}, Mathlib.Meta.NormNum.IsNat a n → ↑n = a' → a = a'
· 使用定理 `Mathlib.Meta.NormNum.isNat_pow`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → ℕ → α} {a : α} {b a' b' c : ℕ},   f = HPow.hPow →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.IsNatPowT.run`：∀ {a b c : ℕ}, Mathlib.Meta.NormNum.
IsNatPowT (a.pow 1 = a) a b c → a.pow b = c
· 使用定理 `Mathlib.Meta.NormNum.IsNatPowT.trans`：∀ {a b c : ℕ} {p : Prop} {b' c' : 
ℕ},   Mathlib.Meta.NormNum.IsNatPowT p a b c →     Mathlib.Meta.NormNum.IsNatPow
T (a.pow b = c) a b' c' → …
· 使用定理 `Mathlib.Meta.NormNum.IsNatPowT.bit0`：∀ {a b c : ℕ}, Mathlib.Meta.NormNum
.IsNatPowT (a.pow b = c) a (2 * b) (c.mul c)
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Mathlib.Meta.NormNum.isNat_lt_true`：∀ {α : Type u_1} [inst : Semiring α]
 [inst_1 : PartialOrder α] [IsOrderedRing α] [CharZero α] {a b : α} {a' b' : ℕ},
   Mathlib.Meta.NormNum.…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.exists_eq_succ_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → ∃ k, n = k.succ
· 使用定理 `Nat.ne_zero_of_lt`：∀ {b a : ℕ}, b < a → a ≠ 0
· 使用定理 `Nat.pow_succ'`：∀ {m n : ℕ}, m ^ n.succ = m * m ^ n
· 使用定理 `mul_lt_mul_of_pos_left`：mul_lt_mul_of_pos_left [PosMulStrictMono α] (hbc
 : b < c) (ha : 0 < a) : a * b < a * c
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `Nat.le_of_lt_succ`：∀ {m n : ℕ}, m < n.succ → m ≤ n
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
（共 80 条，此处仅展示前 30 条）

--- 原说明 ---
An exponential lower bound on the central binomial coefficient.
This bound is of interest because it appears in
[Tochiori's refinement of Erdős's proof of Bertrand's postulate](tochiori_bertra
nd).
-/
theorem four_pow_lt_mul_centralBinom (n : ℕ) (n_big : 4 ≤ n) : 4 ^ n < n * centralBinom n := by
  induction n using Nat.strong_induction_on with | _ n IH
  rcases lt_trichotomy n 4 with (hn | rfl | hn)
  · clear IH; exact False.elim ((not_lt.2 n_big) hn)
  · norm_num [centralBinom, choose]
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hn)
  calc
    4 ^ (n + 1)
    _ = 4 * 4 ^ n := by rw [pow_succ']
    _ < 4 * (n * centralBinom n) := by gcongr; exact IH n n.lt_succ_self (Nat.le_of_lt_succ hn)
    _ ≤ 2 * (2 * n + 1) * centralBinom n := by rw [← mul_assoc]; linarith
    _ = (n + 1) * centralBinom (n + 1) := (succ_mul_centralBinom_succ n).symm

/-- An exponential lower bound on the central binomial coefficient.
This bound is weaker than `Nat.four_pow_lt_mul_centralBinom`, but it is of historical interest
because it appears in Erdős's proof of Bertrand's postulate.
-/
/-
**Nat.four_pow_le_two_mul_self_mul_centralBinom** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：four_pow_le_two_mul_self_mul_centralBinom : forall (n : Nat) (_ : 0 < n), 
4 ^ n <= 2 * n * centralBinom n | 0, pr => (Nat.not_lt_zero _ pr).elim | 1, _ =>
 by simp [centralBinom, choose] | 2, _ => by simp [centralBinom, choose] | 3, _ 
=> by simp [centralBinom, choose] | n + 4, _ => calc 4 ^ (n + 4) <= (n + 4) * ce
ntralBinom (n + 4)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.not_lt_zero`：∀ (n : ℕ), ¬n < 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_true_of_decide`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p = True
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.four_pow_lt_mul_centralBinom`：four_pow_lt_mul_centralBinom (n : Nat)
 (n_big : 4 <= n) : 4 ^ n < n * centralBinom n
· 使用定理 `le_add_self`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ b + a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Nat.le_mul_of_pos_left`：∀ {n : ℕ} (m : ℕ), 0 < n → m ≤ n * m
· 使用定理 `zero_lt_two`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Part
ialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α

--- 原说明 ---
An exponential lower bound on the central binomial coefficient.
This bound is weaker than `Nat.four_pow_lt_mul_centralBinom`, but it is of histo
rical interest
because it appears in Erdős's proof of Bertrand's postulate.
-/
theorem four_pow_le_two_mul_self_mul_centralBinom :
    ∀ (n : ℕ) (_ : 0 < n), 4 ^ n ≤ 2 * n * centralBinom n
  | 0, pr => (Nat.not_lt_zero _ pr).elim
  | 1, _ => by simp [centralBinom, choose]
  | 2, _ => by simp [centralBinom, choose]
  | 3, _ => by simp [centralBinom, choose]
  | n + 4, _ =>
    calc
      4 ^ (n + 4) ≤ (n + 4) * centralBinom (n + 4) :=
        (four_pow_lt_mul_centralBinom _ le_add_self).le
      _ ≤ 2 * (n + 4) * centralBinom (n + 4) := by
        rw [mul_assoc]; refine Nat.le_mul_of_pos_left _ zero_lt_two
/-
**Nat.two_dvd_centralBinom_succ** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：two_dvd_centralBinom_succ (n : Nat) : 2 ∣ centralBinom (n + 1)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.centralBinom_eq_two_mul_choose`：centralBinom_eq_two_mul_choose (n : 
Nat) : centralBinom n = (2 * n).choose n
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Nat.choose_succ_succ'`：choose_succ_succ' (n k : Nat) : choose (n + 1) (k
 + 1) = choose n k + choose n (k + 1)
· 使用定理 `Nat.choose_symm_add`：choose_symm_add {a b : Nat} : choose (a + b) a = ch
oose (a + b) b
-/
theorem two_dvd_centralBinom_succ (n : ℕ) : 2 ∣ centralBinom (n + 1) := by
  use (n + 1 + n).choose n
  rw [centralBinom_eq_two_mul_choose, two_mul, ← add_assoc,
      choose_succ_succ' (n + 1 + n) n, choose_symm_add, ← two_mul]
/-
**Nat.two_dvd_centralBinom_of_one_le** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：two_dvd_centralBinom_of_one_le {n : Nat} (h : 0 < n) : 2 ∣ centralBinom n
参数：h : 0 < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.succ_pred_eq_of_pos`：∀ {n : ℕ}, 0 < n → n.pred.succ = n
· 使用定理 `Nat.two_dvd_centralBinom_succ`：two_dvd_centralBinom_succ (n : Nat) : 2 ∣
 centralBinom (n + 1)
-/
theorem two_dvd_centralBinom_of_one_le {n : ℕ} (h : 0 < n) : 2 ∣ centralBinom n := by
  rw [← Nat.succ_pred_eq_of_pos h]
  exact two_dvd_centralBinom_succ n.pred

/-- A crucial lemma to ensure that Catalan numbers can be defined via their explicit formula
  `catalan n = n.centralBinom / (n + 1)`. -/
/-
**Nat.succ_dvd_centralBinom** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：succ_dvd_centralBinom (n : Nat) : n + 1 ∣ n.centralBinom
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Nat.coprime_add_self_right`：coprime_add_self_right {m n : Nat} : Coprime
 m (n + m) ↔ Coprime m n
· 使用定理 `Nat.coprime_self_add_left`：coprime_self_add_left {m n : Nat} : Coprime (
m + n) m ↔ Coprime n m
· 使用定理 `Nat.coprime_one_left`：∀ (n : ℕ), Nat.Coprime 1 n
· 使用定理 `Nat.Coprime.dvd_of_dvd_mul_left`：∀ {k m n : ℕ}, k.Coprime m → k ∣ m * n 
→ k ∣ n
· 使用定理 `Nat.dvd_of_mul_dvd_mul_left`：∀ {k m n : ℕ}, 0 < k → k * m ∣ k * n → m ∣ 
n
· 使用定理 `zero_lt_two`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Part
ialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Nat.succ_mul_centralBinom_succ`：succ_mul_centralBinom_succ (n : Nat) : (
n + 1) * centralBinom (n + 1) = 2 * (2 * n + 1) * centralBinom n
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_dvd_mul_left`：mul_dvd_mul_left (a : α) (h : b ∣ c) : a * b ∣ a * c
· 使用定理 `Nat.two_dvd_centralBinom_succ`：two_dvd_centralBinom_succ (n : Nat) : 2 ∣
 centralBinom (n + 1)

--- 原说明 ---
A crucial lemma to ensure that Catalan numbers can be defined via their explicit
 formula
  `catalan n = n.centralBinom / (n + 1)`.
-/
theorem succ_dvd_centralBinom (n : ℕ) : n + 1 ∣ n.centralBinom := by
  have h_s : (n + 1).Coprime (2 * n + 1) := by
    rw [two_mul, add_assoc, coprime_add_self_right, coprime_self_add_left]
    exact coprime_one_left n
  apply h_s.dvd_of_dvd_mul_left
  apply Nat.dvd_of_mul_dvd_mul_left zero_lt_two
  rw [← mul_assoc, ← succ_mul_centralBinom_succ, mul_comm]
  exact mul_dvd_mul_left _ (two_dvd_centralBinom_succ n)

end Nat

