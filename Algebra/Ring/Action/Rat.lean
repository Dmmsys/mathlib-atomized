/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs

/-!
# Actions by nonnegative rational numbers
-/

public section

assert_not_exists IsOrderedMonoid

variable {R : Type*}

/-! ### Scalar multiplication -/

namespace NNRat
variable [DivisionSemiring R]

/-
**NNRat.** 是 Mathlib 中的一个实例，位于命名空间 `NNRat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) instDistribSMul : DistribSMul ℚ≥0 R where
  smul_zero a := by rw [smul_def, mul_zero]
  smul_add a x y := by rw [smul_def, smul_def, smul_def, mul_add]
/-
**NNRat.instIsScalarTowerRight** 是 Mathlib 中的一个实例，位于命名空间 `NNRat`。
形式化陈述：instIsScalarTowerRight : IsScalarTower Rat>=0 R R where smul_assoc a x y
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `NNRat.smul_def`：smul_def (q : Rat>=0) (a : K) : q • a = q * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance instIsScalarTowerRight : IsScalarTower ℚ≥0 R R where
  smul_assoc a x y := by simp only [smul_def, smul_eq_mul, mul_assoc]

end NNRat

namespace Rat
variable [DivisionRing R]

/-
**Rat.** 是 Mathlib 中的一个实例，位于命名空间 `Rat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) instDistribSMul : DistribSMul ℚ R where
  smul_zero a := by rw [smul_def, mul_zero]
  smul_add a x y := by rw [smul_def, smul_def, smul_def, mul_add]
/-
**Rat.instIsScalarTowerRight** 是 Mathlib 中的一个实例，位于命名空间 `Rat`。
形式化陈述：instIsScalarTowerRight : IsScalarTower Rat R R where smul_assoc a x y
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Rat.smul_def`：smul_def (a : Rat) (x : K) : a • x = ↑a * x
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance instIsScalarTowerRight : IsScalarTower ℚ R R where
  smul_assoc a x y := by simp only [smul_def, smul_eq_mul, mul_assoc]

end Rat

