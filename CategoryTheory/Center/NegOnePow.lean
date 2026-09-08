/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Center.Preadditive
public import Mathlib.Algebra.Ring.NegOnePow

/-!
# Powers of `-1` in the center of a preadditive category

-/

public section

universe v u

namespace CategoryTheory.CatCenter

variable {C : Type u} [Category.{v} C] [Preadditive C]

open scoped IsMulCommutative in
@[simp]
/-
**CategoryTheory.CatCenter.app_neg_one_zpow** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.CatCenter`。
形式化陈述：app_neg_one_zpow (n : Int) (X : C) : ((-1) ^ n : (CatCenter C)ˣ).val.app X
 = n.negOnePow • 𝟙 X
参数：n : Int；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CatCenter.instIsMulCommutative`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C], IsMulCommutative (CategoryTheory.CatCenter C)
· 使用引理 `Int.even_or_odd`：even_or_odd (n : Int) : Even n ∨ Odd n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `zpow_add`：zpow_add (a : G) (m n : Int) : a ^ (m + n) = a ^ m * a ^ n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `one_zpow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (n : ℤ), 1 ^ n = 1
· 使用引理 `Int.negOnePow_even`：negOnePow_even (n : Int) (hn : Even n) : n.negOnePow
 = 1
· 使用定理 `Even.add_self`：∀ {α : Type u_2} [inst : Add α] (r : α), Even (r + r)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Int.negOnePow_odd`：negOnePow_odd (n : Int) (hn : Odd n) : n.negOnePow = 
-1
· 使用引理 `odd_two_mul_add_one`：odd_two_mul_add_one (a : α) : Odd (2 * a + 1)
· 使用定理 `Int.two_mul`：∀ (n : ℤ), 2 * n = n + n
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
-/
lemma app_neg_one_zpow (n : ℤ) (X : C) :
    ((-1) ^ n : (CatCenter C)ˣ).val.app X = n.negOnePow • 𝟙 X := by
  obtain ⟨n, rfl⟩ | ⟨n, rfl⟩ := Int.even_or_odd n
  · simp [zpow_add, ← mul_zpow, Int.negOnePow_even _ (Even.add_self n)]
  · rw [Int.negOnePow_odd _ (by exact odd_two_mul_add_one n)]
    simp [Units.smul_def, zpow_add, Int.two_mul, ← mul_zpow]

end CategoryTheory.CatCenter

