/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module

public import Mathlib.Data.Nat.Prime.Basic
public meta import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Tactic.NormNum.Basic
public meta import Mathlib.Tactic.NormNum.Result

/-!
# `norm_num` extensions on natural numbers

This file provides a `norm_num` extension to prove that natural numbers are prime and compute
its minimal factor. Todo: compute the list of all factors.


## Implementation Notes

For numbers larger than 25 bits, the primality proof produced by `norm_num` is an expression
that is thousands of levels deep, and the Lean kernel seems to raise a stack overflow when
type-checking that proof. If we want an implementation that works for larger primes, we should
generate a proof that has a smaller depth.

Note: `evalMinFac.aux` does not raise a stack overflow, which can be checked by replacing the
`prf'` in the recursive call by something like `(.sort .zero)`
-/

public meta section

open Nat Qq Lean Meta

namespace Mathlib.Meta.NormNum

/-
**Mathlib.Meta.NormNum.not_prime_mul_of_ble** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.M
eta.NormNum`。
形式化陈述：not_prime_mul_of_ble (a b n : Nat) (h : a * b = n) (h₁ : a.ble 1 = false) 
(h₂ : b.ble 1 = false) : ¬ n.Prime
参数：a b n : Nat；h : a * b = n；h₁ : a.ble 1 = false；h₂ : b.ble 1 = false。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.not_prime_of_mul_eq`：not_prime_of_mul_eq {a b n : Nat} (h : a * b = 
n) (h₁ : a != 1) (h₂ : b != 1) : ¬Prime n
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Mathlib.Meta.NormNum.ble_eq_false`：ble_eq_false {x y : Nat} : x.ble y = 
false ↔ y < x
-/
theorem not_prime_mul_of_ble (a b n : ℕ) (h : a * b = n) (h₁ : a.ble 1 = false)
    (h₂ : b.ble 1 = false) : ¬ n.Prime :=
  not_prime_of_mul_eq h (ble_eq_false.mp h₁).ne' (ble_eq_false.mp h₂).ne'

/-- Produce a proof that `n` is not prime from a factor `1 < d < n`. `en` should be the expression
  that is the natural number literal `n`. -/
/-
**Mathlib.Meta.NormNum.deriveNotPrime** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.No
rmNum`。
形式化陈述：deriveNotPrime (n d : Nat) (en : Q(Nat)) : Q(¬ Nat.Prime $en)
参数：n d : Nat；en : Q(Nat)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Produce a proof that `n` is not prime from a factor `1 < d < n`. `en` should be 
the expression
  that is the natural number literal `n`.
-/
def deriveNotPrime (n d : ℕ) (en : Q(ℕ)) : Q(¬ Nat.Prime $en) := Id.run do
  let d' : ℕ := n / d
  let prf : Q($d * $d' = $en) := (q(Eq.refl $en) : Expr)
  let r : Q(Nat.ble $d 1 = false) := (q(Eq.refl false) : Expr)
  let r' : Q(Nat.ble $d' 1 = false) := (q(Eq.refl false) : Expr)
  return q(not_prime_mul_of_ble _ _ _ $prf $r $r')

/-- A predicate representing partial progress in a proof of `minFac`. -/
/-
**Mathlib.Meta.NormNum.MinFacHelper** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.Norm
Num`。
形式化陈述：MinFacHelper (n k : Nat) : Prop
参数：n k : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A predicate representing partial progress in a proof of `minFac`.
-/
def MinFacHelper (n k : ℕ) : Prop :=
  2 < k ∧ k % 2 = 1 ∧ k ≤ minFac n
/-
**Mathlib.Meta.NormNum.MinFacHelper.one_lt** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Me
ta.NormNum.MinFacHelper`。
形式化陈述：∀ {n k : ℕ}, Mathlib.Meta.NormNum.MinFacHelper n k → 1 < n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `of_decide_eq_false`：∀ {p : Prop} [inst : Decidable p], decide p = false 
→ ¬p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `Nat.succ_le_of_lt`：∀ {n m : ℕ}, n < m → n.succ ≤ m
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.minFac_one`：minFac_one : minFac 1 = 1
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem MinFacHelper.one_lt {n k : ℕ} (h : MinFacHelper n k) : 1 < n := by
  have : 2 < minFac n := h.1.trans_le h.2.2
  obtain rfl | h := n.eq_zero_or_pos
  · contradiction
  rcases (succ_le_of_lt h).eq_or_lt with rfl | h
  · simp_all
  exact h
/-
**Mathlib.Meta.NormNum.minFacHelper_0** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.No
rmNum`。
形式化陈述：minFacHelper_0 (n : Nat) (h1 : Nat.ble (nat_lit 2) n = true) (h2 : nat_lit
 1 = n % (nat_lit 2)) : MinFacHelper n (nat_lit 3)
参数：n : Nat；h1 : Nat.ble (nat_lit 2) n = true；h2 : nat_lit 1 = n % (nat_lit 2)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.le_minFac'`：le_minFac' {m n : Nat} : n = 1 ∨ m <= minFac n ↔ forall 
p, 2 <= p -> p ∣ n -> m <= p
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.dvd_iff_mod_eq_zero`：∀ {m n : ℕ}, m ∣ n ↔ n % m = 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.ne_of_gt`：∀ {a b : ℕ}, b < a → a ≠ b
· 使用定理 `Nat.le_of_ble_eq_true`：∀ {n m : ℕ}, n.ble m = true → n ≤ m
-/
theorem minFacHelper_0 (n : ℕ)
    (h1 : Nat.ble (nat_lit 2) n = true) (h2 : nat_lit 1 = n % (nat_lit 2)) :
    MinFacHelper n (nat_lit 3) := by
  refine ⟨by simp, by simp, ?_⟩
  refine (le_minFac'.mpr fun p hp hpn ↦ ?_).resolve_left (Nat.ne_of_gt (Nat.le_of_ble_eq_true h1))
  rcases hp.eq_or_lt with rfl | h
  · simp [(Nat.dvd_iff_mod_eq_zero ..).1 hpn] at h2
  · exact h
/-
**Mathlib.Meta.NormNum.minFacHelper_1** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.No
rmNum`。
形式化陈述：minFacHelper_1 {n k k' : Nat} (e : k + 2 = k') (h : MinFacHelper n k) (np 
: minFac n != k) : MinFacHelper n k'
参数：e : k + 2 = k'；h : MinFacHelper n k；np : minFac n != k。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.lt_add_right`：∀ {a b : ℕ} (c : ℕ), a < b → a < b + c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Nat.add_mod`：∀ (a b n : ℕ), (a + b) % n = (a % n + b % n) % n
· 使用定理 `Nat.mod_self`：∀ (n : ℕ), n % n = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Nat.mod_mod`：∀ (a n : ℕ), a % n % n = a % n
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `Nat.succ_le_of_lt`：∀ {n m : ℕ}, n < m → n.succ ≤ m
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Nat.dvd_iff_mod_eq_zero`：∀ {m n : ℕ}, m ∣ n ↔ n % m = 0
· 使用定理 `Nat.succ_eq_add_one`：∀ (n : ℕ), n.succ = n + 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.dvd_prime`：dvd_prime {p m : Nat} (pp : Prime p) : m ∣ p ↔ m = 1 ∨ m 
= p
· 使用定理 `Nat.minFac_prime`：minFac_prime {n : Nat} (n1 : n != 1) : Prime (minFac n
)
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Mathlib.Meta.NormNum.MinFacHelper.one_lt`：∀ {n k : ℕ}, Mathlib.Meta.Norm
Num.MinFacHelper n k → 1 < n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
-/
theorem minFacHelper_1 {n k k' : ℕ} (e : k + 2 = k') (h : MinFacHelper n k)
    (np : minFac n ≠ k) : MinFacHelper n k' := by
  rw [← e]
  refine ⟨Nat.lt_add_right _ h.1, ?_, ?_⟩
  · rw [add_mod, mod_self, add_zero, mod_mod]
    exact h.2.1
  rcases h.2.2.eq_or_lt with rfl | h2
  · exact (np rfl).elim
  rcases (succ_le_of_lt h2).eq_or_lt with h2|h2
  · refine ((h.1.trans_le h.2.2).ne ?_).elim
    have h3 : 2 ∣ minFac n := by
      rw [Nat.dvd_iff_mod_eq_zero, ← h2, succ_eq_add_one, add_mod, h.2.1]
    simpa [dvd_prime <| minFac_prime h.one_lt.ne'] using h3
  exact h2
/-
**Mathlib.Meta.NormNum.minFacHelper_2** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.No
rmNum`。
形式化陈述：minFacHelper_2 {n k k' : Nat} (e : k + 2 = k') (nk : ¬ Nat.Prime k) (h : M
inFacHelper n k) : MinFacHelper n k'
参数：e : k + 2 = k'；nk : ¬ Nat.Prime k；h : MinFacHelper n k。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Meta.NormNum.minFacHelper_1`：minFacHelper_1 {n k k' : Nat} (e : 
k + 2 = k') (h : MinFacHelper n k) (np : minFac n != k) : MinFacHelper n k'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.minFac_prime`：minFac_prime {n : Nat} (n1 : n != 1) : Prime (minFac n
)
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Mathlib.Meta.NormNum.MinFacHelper.one_lt`：∀ {n k : ℕ}, Mathlib.Meta.Norm
Num.MinFacHelper n k → 1 < n
-/
theorem minFacHelper_2 {n k k' : ℕ} (e : k + 2 = k') (nk : ¬ Nat.Prime k)
    (h : MinFacHelper n k) : MinFacHelper n k' := by
  refine minFacHelper_1 e h fun h2 ↦ ?_
  rw [← h2] at nk
  exact nk <| minFac_prime h.one_lt.ne'
/-
**Mathlib.Meta.NormNum.minFacHelper_3** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.No
rmNum`。
形式化陈述：minFacHelper_3 {n k k' : Nat} (e : k + 2 = k') (nk : (n % k).beq 0 = false
) (h : MinFacHelper n k) : MinFacHelper n k'
参数：e : k + 2 = k'；nk : (n % k).beq 0 = false；h : MinFacHelper n k。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Meta.NormNum.minFacHelper_1`：minFacHelper_1 {n k k' : Nat} (e : 
k + 2 = k') (h : MinFacHelper n k) (np : minFac n != k) : MinFacHelper n k'
· 使用定理 `Nat.ne_of_beq_eq_false`：∀ {n m : ℕ}, n.beq m = false → ¬n = m
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.dvd_iff_mod_eq_zero`：∀ {m n : ℕ}, m ∣ n ↔ n % m = 0
· 使用定理 `Nat.minFac_dvd`：minFac_dvd (n : Nat) : minFac n ∣ n
-/
theorem minFacHelper_3 {n k k' : ℕ} (e : k + 2 = k') (nk : (n % k).beq 0 = false)
    (h : MinFacHelper n k) : MinFacHelper n k' := by
  refine minFacHelper_1 e h fun h2 ↦ ?_
  have nk := Nat.ne_of_beq_eq_false nk
  rw [← Nat.dvd_iff_mod_eq_zero, ← h2] at nk
  exact nk <| minFac_dvd n
/-
**Mathlib.Meta.NormNum.isNat_minFac_1** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.No
rmNum`。
形式化陈述：∀ {a : ℕ}, Mathlib.Meta.NormNum.IsNat a 1 → Mathlib.Meta.NormNum.IsNat a.m
inFac 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.minFac_one`：minFac_one : minFac 1 = 1
-/
theorem isNat_minFac_1 : {a : ℕ} → IsNat a (nat_lit 1) → IsNat a.minFac 1
  | _, ⟨rfl⟩ => ⟨minFac_one⟩
/-
**Mathlib.Meta.NormNum.isNat_minFac_2** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.No
rmNum`。
形式化陈述：∀ {a a' : ℕ}, Mathlib.Meta.NormNum.IsNat a a' → a' % 2 = 0 → Mathlib.Meta.
NormNum.IsNat a.minFac 2
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_ofNat`：∀ {R : Type u_1} {n : ℕ} [inst : NatCast R] [inst_1 : n.
AtLeastTwo], ↑(OfNat.ofNat n) = OfNat.ofNat n
· 使用定理 `Nat.minFac_eq_two_iff`：minFac_eq_two_iff (n : Nat) : minFac n = 2 ↔ 2 ∣ 
n
· 使用定理 `Nat.dvd_iff_mod_eq_zero`：∀ {m n : ℕ}, m ∣ n ↔ n % m = 0
-/
theorem isNat_minFac_2 : {a a' : ℕ} → IsNat a a' → a' % 2 = 0 → IsNat a.minFac 2
  | a, _, ⟨rfl⟩, h => ⟨by rw [cast_ofNat, minFac_eq_two_iff, Nat.dvd_iff_mod_eq_zero, h]⟩
/-
**Mathlib.Meta.NormNum.isNat_minFac_3** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.No
rmNum`。
形式化陈述：∀ {n n' : ℕ} (k : ℕ),   Mathlib.Meta.NormNum.IsNat n n' →     Mathlib.Meta
.NormNum.MinFacHelper n' k → 0 = n' % k → Mathlib.Meta.NormNum.IsNat n.minFac k
参数：k : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Nat.minFac_le_of_dvd`：minFac_le_of_dvd {n : Nat} : forall {m : Nat}, 2 <
= m -> m ∣ n -> minFac n <= m
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.dvd_iff_mod_eq_zero`：∀ {m n : ℕ}, m ∣ n ↔ n % m = 0
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem isNat_minFac_3 : {n n' : ℕ} → (k : ℕ) →
    IsNat n n' → MinFacHelper n' k → nat_lit 0 = n' % k → IsNat (minFac n) k
  | n, _, k, ⟨rfl⟩, h1, h2 => by
    rw [eq_comm, ← Nat.dvd_iff_mod_eq_zero] at h2
    exact ⟨le_antisymm (minFac_le_of_dvd h1.1.le h2) h1.2.2⟩
/-
**Mathlib.Meta.NormNum.isNat_minFac_4** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.No
rmNum`。
形式化陈述：isNat_minFac_4 : {n n' k : Nat} -> IsNat n n' -> MinFacHelper n' k -> (k *
 k).ble n' = false -> IsNat (minFac n) n' | n, _, k, ⟨rfl⟩, h1, h2 => by refine 
⟨(Nat.prime_def_minFac.mp ?_).2⟩ rw [Nat.prime_def_le_sqrt] refine ⟨h1.one_lt, f
un m hm hmn h2mn => ?_⟩ exact lt_irrefl m calc m <= sqrt n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.prime_def_minFac`：prime_def_minFac {p : Nat} : Prime p ↔ 2 <= p ∧ mi
nFac p = p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.prime_def_le_sqrt`：prime_def_le_sqrt {p : Nat} : Prime p ↔ 2 <= p ∧ 
forall m, 2 <= m -> m <= sqrt p -> ¬m ∣ p
· 使用定理 `Mathlib.Meta.NormNum.MinFacHelper.one_lt`：∀ {n k : ℕ}, Mathlib.Meta.Norm
Num.MinFacHelper n k → 1 < n
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Nat.sqrt_lt`：sqrt_lt : sqrt m < n ↔ m < n * n
· 使用定理 `Mathlib.Meta.NormNum.ble_eq_false`：ble_eq_false {x y : Nat} : x.ble y = 
false ↔ y < x
· 使用定理 `Nat.minFac_le_of_dvd`：minFac_le_of_dvd {n : Nat} : forall {m : Nat}, 2 <
= m -> m ∣ n -> minFac n <= m
-/
theorem isNat_minFac_4 : {n n' k : ℕ} →
    IsNat n n' → MinFacHelper n' k → (k * k).ble n' = false → IsNat (minFac n) n'
  | n, _, k, ⟨rfl⟩, h1, h2 => by
    refine ⟨(Nat.prime_def_minFac.mp ?_).2⟩
    rw [Nat.prime_def_le_sqrt]
    refine ⟨h1.one_lt, fun m hm hmn h2mn ↦ ?_⟩
    exact lt_irrefl m <| calc
      m ≤ sqrt n   := hmn
      _ < k        := sqrt_lt.mpr (ble_eq_false.mp h2)
      _ ≤ n.minFac := h1.2.2
      _ ≤ m        := Nat.minFac_le_of_dvd hm h2mn

/-- The `norm_num` extension which identifies expressions of the form `minFac n`. -/
/-
**Mathlib.Meta.NormNum.evalMinFac** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.NormNu
m`。
形式化陈述：Mathlib.Meta.NormNum.NormNumExt
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `norm_num` extension which identifies expressions of the form `minFac n`.
-/
@[norm_num Nat.minFac _] partial def evalMinFac : NormNumExt where eval {_ _} e := do
  let .app (.const ``Nat.minFac _) (n : Q(ℕ)) ← whnfR e | failure
  let sℕ : Q(AddMonoidWithOne ℕ) := q(Nat.instAddMonoidWithOne)
  let ⟨nn, pn⟩ ← deriveNat n sℕ
  let n' := nn.natLit!
  let rec aux (ek : Q(ℕ)) (prf : Q(MinFacHelper $nn $ek)) :
      (c : Q(ℕ)) × Q(IsNat (Nat.minFac $n) $c) :=
    let k := ek.natLit!
    -- remark: `deriveBool q($nn < $ek * $ek)` is 2x slower than the following test.
    if n' < k * k then
      let r : Q(Nat.ble ($ek * $ek) $nn = false) := (q(Eq.refl false) : Expr)
      ⟨nn, q(isNat_minFac_4 $pn $prf $r)⟩
    else
      let d : ℕ := k.minFac
      -- the following branch is not necessary for the correctness,
      -- but makes the algorithm 2x faster
      if d < k then
        have ek' : Q(ℕ) := mkRawNatLit <| k + 2
        let pk' : Q($ek + 2 = $ek') := (q(Eq.refl $ek') : Expr)
        let pd := deriveNotPrime k d ek
        aux ek' q(minFacHelper_2 $pk' $pd $prf)
      -- remark: `deriveBool q($nn % $ek = 0)` is 5x slower than the following test
      else if n' % k = 0 then
        let r : Q(nat_lit 0 = $nn % $ek) := (q(Eq.refl 0) : Expr)
        let r' : Q(IsNat (minFac $n) $ek) := q(isNat_minFac_3 _ $pn $prf $r)
        ⟨ek, r'⟩
      else
        let r : Q(Nat.beq ($nn % $ek) 0 = false) := (q(Eq.refl false) : Expr)
        have ek' : Q(ℕ) := mkRawNatLit <| k + 2
        let pk' : Q($ek + 2 = $ek') := (q(Eq.refl $ek') : Expr)
        aux ek' q(minFacHelper_3 $pk' $r $prf)
  let rec core : MetaM <| Result q(Nat.minFac $n) := do
    if n' = 1 then
      let pn : Q(IsNat $n (nat_lit 1)) := pn
      return .isNat sℕ q(nat_lit 1) q(isNat_minFac_1 $pn)
    if n' % 2 = 0 then
      let pq : Q($nn % 2 = 0) := (q(Eq.refl 0) : Expr)
      return .isNat sℕ q(nat_lit 2) q(isNat_minFac_2 $pn $pq)
    let pp : Q(Nat.ble 2 $nn = true) := (q(Eq.refl true) : Expr)
    let pq : Q(1 = $nn % 2) := (q(Eq.refl (nat_lit 1)) : Expr)
    let ⟨c, pc⟩ := aux q(nat_lit 3) q(minFacHelper_0 $nn $pp $pq)
    return .isNat sℕ c pc
  core
/-
**Mathlib.Meta.NormNum.isNat_prime_0** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.Nor
mNum`。
形式化陈述：∀ {n : ℕ}, Mathlib.Meta.NormNum.IsNat n 0 → ¬Nat.Prime n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.not_prime_zero`：¬Nat.Prime 0
-/
theorem isNat_prime_0 : {n : ℕ} → IsNat n (nat_lit 0) → ¬ n.Prime
  | _, ⟨rfl⟩ => not_prime_zero
/-
**Mathlib.Meta.NormNum.isNat_prime_1** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.Nor
mNum`。
形式化陈述：∀ {n : ℕ}, Mathlib.Meta.NormNum.IsNat n 1 → ¬Nat.Prime n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.not_prime_one`：¬Nat.Prime 1
-/
theorem isNat_prime_1 : {n : ℕ} → IsNat n (nat_lit 1) → ¬ n.Prime
  | _, ⟨rfl⟩ => not_prime_one
/-
**Mathlib.Meta.NormNum.isNat_prime_2** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.Nor
mNum`。
形式化陈述：∀ {n n' : ℕ},   Mathlib.Meta.NormNum.IsNat n n' → Nat.ble 2 n' = true → Ma
thlib.Meta.NormNum.IsNat n'.minFac n' → Nat.Prime n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.prime_def_minFac`：prime_def_minFac {p : Nat} : Prime p ↔ 2 <= p ∧ mi
nFac p = p
· 使用定理 `Nat.ble_eq`：∀ {x y : ℕ}, (x.ble y = true) = (x ≤ y)
-/
theorem isNat_prime_2 : {n n' : ℕ} →
    IsNat n n' → Nat.ble 2 n' = true → IsNat (minFac n') n' → n.Prime
  | _, _, ⟨rfl⟩, h1, ⟨h2⟩ => prime_def_minFac.mpr ⟨ble_eq.mp h1, h2⟩
/-
**Mathlib.Meta.NormNum.isNat_not_prime** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.N
ormNum`。
形式化陈述：isNat_not_prime {n n' : Nat} (h : IsNat n n') : ¬n'.Prime -> ¬n.Prime
参数：h : IsNat n n'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Meta.NormNum.isNat.natElim`：∀ {p : ℕ → Prop} {n n' : ℕ}, Mathlib
.Meta.NormNum.IsNat n n' → p n' → p n
-/
theorem isNat_not_prime {n n' : ℕ} (h : IsNat n n') : ¬n'.Prime → ¬n.Prime := isNat.natElim h

/-- The `norm_num` extension which identifies expressions of the form `Nat.Prime n`. -/
/-
**Mathlib.Meta.NormNum.evalNatPrime** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.Norm
Num`。
形式化陈述：Mathlib.Meta.NormNum.NormNumExt
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `norm_num` extension which identifies expressions of the form `Nat.Prime n`.
-/
@[norm_num Nat.Prime _] def evalNatPrime : NormNumExt where eval {_ _} e := do
  let .app (.const `Nat.Prime _) (n : Q(ℕ)) ← whnfR e | failure
  let ⟨nn, pn⟩ ← deriveNat n _
  let n' := nn.natLit!
  -- note: if `n` is not prime, we don't have to verify the calculation of `n.minFac`, we just have
  -- to compute it, which is a lot quicker
  let rec core : MetaM (Result q(Nat.Prime $n)) := do
    match n' with
    | 0 => haveI' : $nn =Q 0 := ⟨⟩; return .isFalse q(isNat_prime_0 $pn)
    | 1 => haveI' : $nn =Q 1 := ⟨⟩; return .isFalse q(isNat_prime_1 $pn)
    | _ =>
      let d := n'.minFac
      if d < n' then
        let prf : Q(¬ Nat.Prime $nn) := deriveNotPrime n' d nn
        return .isFalse q(isNat_not_prime $pn $prf)
      let r : Q(Nat.ble 2 $nn = true) := (q(Eq.refl true) : Expr)
      let .isNat _ _lit (p2n : Q(IsNat (minFac $nn) $nn)) ←
        evalMinFac.core nn _ nn q(.raw_refl _) nn.natLit! | failure
      return .isTrue q(isNat_prime_2 $pn $r $p2n)
  core


end NormNum

end Meta

end Mathlib

