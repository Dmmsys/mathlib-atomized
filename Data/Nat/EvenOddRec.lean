/-
Copyright (c) 2022 Stuart Presnell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stuart Presnell
-/
module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Nat.BinaryRec

/-! # A recursion principle based on even and odd numbers. -/

@[expose] public section

namespace Nat

/-- Recursion principle on even and odd numbers: if we have `P 0`, and for all `i : ℕ` we can
extend from `P i` to both `P (2 * i)` and `P (2 * i + 1)`, then we have `P n` for all `n : ℕ`.
This is nothing more than a wrapper around `Nat.binaryRec`, to avoid having to switch to
dealing with `bit0` and `bit1`. -/
@[elab_as_elim]
/-
**Nat.evenOddRec** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：evenOddRec {P : Nat -> Sort*} (h0 : P 0) (h_even : forall n, P n -> P (2 *
 n)) (h_odd : forall n, P n -> P (2 * n + 1)) (n : Nat) : P n
参数：h0 : P 0；h_even : forall n, P n -> P (2 * n)；h_odd : forall n, P n -> P (2 * 
n + 1)；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Recursion principle on even and odd numbers: if we have `P 0`, and for all `i : 
ℕ` we can
extend from `P i` to both `P (2 * i)` and `P (2 * i + 1)`, then we have `P n` fo
r all `n : ℕ`.
This is nothing more than a wrapper around `Nat.binaryRec`, to avoid having to s
witch to
dealing with `bit0` and `bit1`.
-/
def evenOddRec {P : ℕ → Sort*} (h0 : P 0) (h_even : ∀ n, P n → P (2 * n))
    (h_odd : ∀ n, P n → P (2 * n + 1)) (n : ℕ) : P n :=
  binaryRec h0 (fun
    | false, i, hi => (h_even i hi : P (2 * i))
    | true, i, hi => (h_odd i hi : P (2 * i + 1))) n

@[simp]
/-
**Nat.evenOddRec_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：evenOddRec_zero {P : Nat -> Sort*} (h0 : P 0) (h_even : forall i, P i -> P
 (2 * i)) (h_odd : forall i, P i -> P (2 * i + 1)) : evenOddRec h0 h_even h_odd 
0 = h0
参数：h0 : P 0；h_even : forall i, P i -> P (2 * i)；h_odd : forall i, P i -> P (2 * 
i + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.binaryRec_zero`：binaryRec_zero (zero : motive 0) (bit : forall b n, 
motive n -> motive (bit b n)) : binaryRec zero bit 0 = zero
-/
theorem evenOddRec_zero {P : ℕ → Sort*} (h0 : P 0) (h_even : ∀ i, P i → P (2 * i))
    (h_odd : ∀ i, P i → P (2 * i + 1)) : evenOddRec h0 h_even h_odd 0 = h0 :=
  binaryRec_zero _ _

@[simp]
/-
**Nat.evenOddRec_even** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：evenOddRec_even {P : Nat -> Sort*} (h0 : P 0) (h_even : forall i, P i -> P
 (2 * i)) (h_odd : forall i, P i -> P (2 * i + 1)) (H : h_even 0 h0 = h0) (n : N
at) : (2 * n).evenOddRec h0 h_even h_odd = h_even n (evenOddRec h0 h_even h_odd 
n)
参数：h0 : P 0；h_even : forall i, P i -> P (2 * i)；h_odd : forall i, P i -> P (2 * 
i + 1)；H : h_even 0 h0 = h0；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.binaryRec_eq`：binaryRec_eq {zero : motive 0} {bit : forall b n, moti
ve n -> motive (bit b n)} (b n) (h : bit false 0 zero = zero ∨ (n = 0 -> b = tru
e)) : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Bool.false_eq_true`：(false = true) = False
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
theorem evenOddRec_even {P : ℕ → Sort*} (h0 : P 0) (h_even : ∀ i, P i → P (2 * i))
    (h_odd : ∀ i, P i → P (2 * i + 1)) (H : h_even 0 h0 = h0) (n : ℕ) :
    (2 * n).evenOddRec h0 h_even h_odd = h_even n (evenOddRec h0 h_even h_odd n) := by
  apply binaryRec_eq false n
  simp [H]

@[simp]
/-
**Nat.evenOddRec_odd** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：evenOddRec_odd {P : Nat -> Sort*} (h0 : P 0) (h_even : forall i, P i -> P 
(2 * i)) (h_odd : forall i, P i -> P (2 * i + 1)) (H : h_even 0 h0 = h0) (n : Na
t) : (2 * n + 1).evenOddRec h0 h_even h_odd = h_odd n (evenOddRec h0 h_even h_od
d n)
参数：h0 : P 0；h_even : forall i, P i -> P (2 * i)；h_odd : forall i, P i -> P (2 * 
i + 1)；H : h_even 0 h0 = h0；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.binaryRec_eq`：binaryRec_eq {zero : motive 0} {bit : forall b n, moti
ve n -> motive (bit b n)} (b n) (h : bit false 0 zero = zero ∨ (n = 0 -> b = tru
e)) : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
-/
theorem evenOddRec_odd {P : ℕ → Sort*} (h0 : P 0) (h_even : ∀ i, P i → P (2 * i))
    (h_odd : ∀ i, P i → P (2 * i + 1)) (H : h_even 0 h0 = h0) (n : ℕ) :
    (2 * n + 1).evenOddRec h0 h_even h_odd = h_odd n (evenOddRec h0 h_even h_odd n) := by
  apply binaryRec_eq true n
  simp [H]

/-- Strong recursion principle on even and odd numbers: if for all `i : ℕ` we can prove `P (2 * i)`
from `P j` for all `j < 2 * i` and we can prove `P (2 * i + 1)` from `P j` for all `j < 2 * i + 1`,
then we have `P n` for all `n : ℕ`. -/
@[elab_as_elim]
/-
**Nat.evenOddStrongRec** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：evenOddStrongRec {P : Nat -> Sort*} (h_even : forall n : Nat, (forall k < 
2 * n, P k) -> P (2 * n)) (h_odd : forall n : Nat, (forall k < 2 * n + 1, P k) -
> P (2 * n + 1)) (n : Nat) : P n
参数：h_even : forall n : Nat, (forall k < 2 * n, P k) -> P (2 * n)；h_odd : forall 
n : Nat, (forall k < 2 * n + 1, P k) -> P (2 * n + 1)；n : Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.even_or_odd'`：even_or_odd' (n : Nat) : exists k, n = 2 * k ∨ n = 2 *
 k + 1

--- 原说明 ---
Strong recursion principle on even and odd numbers: if for all `i : ℕ` we can pr
ove `P (2 * i)`
from `P j` for all `j < 2 * i` and we can prove `P (2 * i + 1)` from `P j` for a
ll `j < 2 * i + 1`,
then we have `P n` for all `n : ℕ`.
-/
noncomputable def evenOddStrongRec {P : ℕ → Sort*}
    (h_even : ∀ n : ℕ, (∀ k < 2 * n, P k) → P (2 * n))
    (h_odd : ∀ n : ℕ, (∀ k < 2 * n + 1, P k) → P (2 * n + 1)) (n : ℕ) : P n :=
  n.strongRecOn fun m ih => m.even_or_odd'.choose_spec.by_cases
    (fun h => h.symm ▸ h_even m.even_or_odd'.choose <| h ▸ ih)
    (fun h => h.symm ▸ h_odd m.even_or_odd'.choose <| h ▸ ih)

end Nat

