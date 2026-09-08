/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.Monoid.Defs

/-!
# Topological (sub)algebras over `Rat`

## Results

This is just a minimal stub for now!

-/

public section

section DivisionRing

/-- The action induced by `DivisionRing.toRatAlgebra` is continuous. -/
/-
**DivisionRing.continuousConstSMul_rat** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：DivisionRing.continuousConstSMul_rat {A} [DivisionRing A] [TopologicalSpac
e A] [SeparatelyContinuousMul A] [CharZero A] : ContinuousConstSMul Rat A
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `Continuous.const_mul`：Continuous.const_mul (hf : Continuous f) (b : M) :
 Continuous (b * f ·)
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)

--- 原说明 ---
The action induced by `DivisionRing.toRatAlgebra` is continuous.
-/
instance DivisionRing.continuousConstSMul_rat {A} [DivisionRing A] [TopologicalSpace A]
    [SeparatelyContinuousMul A] [CharZero A] : ContinuousConstSMul ℚ A :=
  ⟨fun r => by simpa only [Algebra.smul_def] using! continuous_id.const_mul _⟩

end DivisionRing

