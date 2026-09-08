/-
Copyright (c) 2020 Mario Carneiro, Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johan Commelin
-/
module

public import Mathlib.Algebra.GroupWithZero.WithZero
public import Mathlib.Algebra.Ring.Defs

/-!
# Adjoining a zero to a semiring
-/

public section

namespace WithZero
variable {α : Type*}

/-
**WithZero.instLeftDistribClass** 是 Mathlib 中的一个实例，位于命名空间 `WithZero`。
形式化陈述：instLeftDistribClass [Mul α] [Add α] [LeftDistribClass α] : LeftDistribCla
ss (WithZero α) where left_distrib a b c
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `left_distrib`：left_distrib [Mul R] [Add R] [LeftDistribClass R] (a b c :
 R) : a * (b + c) = a * b + a * c
-/
instance instLeftDistribClass [Mul α] [Add α] [LeftDistribClass α] :
    LeftDistribClass (WithZero α) where
  left_distrib a b c := by
    cases a; · rfl
    cases b <;> cases c <;> try rfl
    exact congr_arg some (left_distrib _ _ _)
/-
**WithZero.instRightDistribClass** 是 Mathlib 中的一个实例，位于命名空间 `WithZero`。
形式化陈述：instRightDistribClass [Mul α] [Add α] [RightDistribClass α] : RightDistrib
Class (WithZero α) where right_distrib a b c
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `right_distrib`：right_distrib [Mul R] [Add R] [RightDistribClass R] (a b 
c : R) : (a + b) * c = a * c + b * c
-/
instance instRightDistribClass [Mul α] [Add α] [RightDistribClass α] :
    RightDistribClass (WithZero α) where
  right_distrib a b c := by
    cases c; · simp
    cases a <;> cases b <;> try rfl
    exact congr_arg some (right_distrib _ _ _)
/-
**WithZero.instDistrib** 是 Mathlib 中的一个实例，位于命名空间 `WithZero`。
形式化陈述：instDistrib [Distrib α] : Distrib (WithZero α) where left_distrib
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDistrib [Distrib α] : Distrib (WithZero α) where
  left_distrib := left_distrib
  right_distrib := right_distrib
/-
**WithZero.instSemiring** 是 Mathlib 中的一个定义，位于命名空间 `WithZero`。
形式化陈述：{α : Type u_1} → [Semiring α] → Semiring (WithZero α)
参数：WithZero α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSemiring [Semiring α] : Semiring (WithZero α) where

end WithZero

