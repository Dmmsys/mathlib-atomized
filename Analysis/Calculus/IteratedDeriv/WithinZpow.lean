/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.Deriv.ZPow

/-!
# Derivatives of `x ^ m`, `m : ℤ` within an open set

In this file we prove theorems about iterated derivatives of `x ^ m`, `m : ℤ` within an open set.

## Keywords

iterated, derivative, power, open set
-/

public section

open scoped Nat

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {s : Set 𝕜}

/-
**iteratedDerivWithin_zpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDerivWithin_zpow (m : Int) (k : Nat) (hs : IsOpen s) : s.EqOn (ite
ratedDerivWithin k (fun y => y ^ m) s) (fun y => (∏ i in Finset.range k, ((m : 𝕜
) - i)) * y ^ (m - k))
参数：m : Int；k : Nat；hs : IsOpen s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.EqOn.trans`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ f₃ : 
α → β}, Set.EqOn f₁ f₂ s → Set.EqOn f₂ f₃ s → Set.EqOn f₁ f₃ s
· 使用定理 `iteratedDerivWithin_of_isOpen_eq_iterate`：iteratedDerivWithin_of_isOpen_
eq_iterate (hs : IsOpen s) : EqOn (iteratedDerivWithin n f s) (deriv^[n] f) s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iter_deriv_zpow'`：iter_deriv_zpow' (m : Int) (k : Nat) : (deriv^[k] fun 
x : 𝕜 => x ^ m) = fun x => (∏ i in Finset.range k, ((m : 𝕜) - i)) * x ^ (m - k)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iteratedDerivWithin_zpow (m : ℤ) (k : ℕ) (hs : IsOpen s) :
    s.EqOn (iteratedDerivWithin k (fun y ↦ y ^ m) s)
    (fun y ↦ (∏ i ∈ Finset.range k, ((m : 𝕜) - i)) * y ^ (m - k)) := by
  apply Set.EqOn.trans (iteratedDerivWithin_of_isOpen_eq_iterate hs)
  intro t ht
  simp
/-
**iteratedDerivWithin_one_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDerivWithin_one_div (k : Nat) (hs : IsOpen s) : s.EqOn (iteratedDe
rivWithin k (fun y => 1 / y) s) (fun y => (-1) ^ k * (k !) * (y ^ (-1 - k : Int)
))
参数：k : Nat；hs : IsOpen s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.EqOn.trans`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ f₃ : 
α → β}, Set.EqOn f₁ f₂ s → Set.EqOn f₂ f₃ s → Set.EqOn f₁ f₃ s
· 使用定理 `iteratedDerivWithin_of_isOpen_eq_iterate`：iteratedDerivWithin_of_isOpen_
eq_iterate (hs : IsOpen s) : EqOn (iteratedDerivWithin n f s) (deriv^[n] f) s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iter_deriv_inv'`：iter_deriv_inv' (k : Nat) : deriv^[k] Inv.inv = fun x :
 𝕜 => (-1) ^ k * k ! * x ^ (-1 - k : Int)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iteratedDerivWithin_one_div (k : ℕ) (hs : IsOpen s) :
    s.EqOn (iteratedDerivWithin k (fun y ↦ 1 / y) s)
    (fun y ↦ (-1) ^ k * (k !) * (y ^ (-1 - k : ℤ))) := by
  apply Set.EqOn.trans (iteratedDerivWithin_of_isOpen_eq_iterate hs)
  intro t ht
  simp
