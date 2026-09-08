/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.Algebra.Order.Group.Synonym
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs

/-! # Unbundled ordered monoid structures on the order dual. -/

public section

universe u

variable {α : Type u}

open Function

namespace OrderDual

@[to_additive]
/-
**OrderDual.mulLeftReflectLE** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
形式化陈述：mulLeftReflectLE [LE α] [Mul α] [MulLeftReflectLE α] : MulLeftReflectLE αᵒ
ᵈ where le_of_mul_le_mul_left'
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Contravariant.flip`：Contravariant.flip (h : Contravariant M N μ r) : Con
travariant M N μ (flip r)
· 使用定理 `MulLeftReflectLE.le_of_mul_le_mul_left'`：∀ {M : Type u_1} {inst : Mul M}
 {inst_1 : LE M} [self : MulLeftReflectLE M] {a b₁ b₂ : M}, a * b₁ ≤ a * b₂ → b₁
 ≤ b₂
-/
instance mulLeftReflectLE [LE α] [Mul α] [MulLeftReflectLE α] : MulLeftReflectLE αᵒᵈ where
  le_of_mul_le_mul_left' :=
    Contravariant.flip (μ := (· * ·)) (fun _ ↦ ‹MulLeftReflectLE α›.le_of_mul_le_mul_left') _

@[to_additive]
/-
**OrderDual.mulLeftMono** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
形式化陈述：mulLeftMono [LE α] [Mul α] [c : MulLeftMono α] : MulLeftMono αᵒᵈ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Covariant.flip`：Covariant.flip (h : Covariant M N μ r) : Covariant M N μ
 (flip r)
· 使用定理 `CovariantClass.elim`：∀ {M : Type u_1} {N : Type u_2} {μ : M → N → N} {r 
: N → N → Prop} [self : CovariantClass M N μ r], Covariant M N μ r
-/
instance mulLeftMono [LE α] [Mul α] [c : MulLeftMono α] : MulLeftMono αᵒᵈ :=
  ⟨c.1.flip⟩

@[to_additive]
/-
**OrderDual.mulRightReflectLE** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
形式化陈述：mulRightReflectLE [LE α] [Mul α] [MulRightReflectLE α] : MulRightReflectLE
 αᵒᵈ where le_of_mul_le_mul_right'
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Contravariant.flip`：Contravariant.flip (h : Contravariant M N μ r) : Con
travariant M N μ (flip r)
· 使用定理 `MulRightReflectLE.le_of_mul_le_mul_right'`：∀ {M : Type u_1} {inst : Mul 
M} {inst_1 : LE M} [self : MulRightReflectLE M] {b a₁ a₂ : M}, a₁ * b ≤ a₂ * b →
 a₁ ≤ a₂
-/
instance mulRightReflectLE [LE α] [Mul α] [MulRightReflectLE α] : MulRightReflectLE αᵒᵈ where
  le_of_mul_le_mul_right' :=
    Contravariant.flip (μ := swap (· * ·)) (fun _ ↦ ‹MulRightReflectLE α›.le_of_mul_le_mul_right') _

@[to_additive]
/-
**OrderDual.mulRightMono** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
形式化陈述：mulRightMono [LE α] [Mul α] [c : MulRightMono α] : MulRightMono αᵒᵈ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Covariant.flip`：Covariant.flip (h : Covariant M N μ r) : Covariant M N μ
 (flip r)
· 使用定理 `CovariantClass.elim`：∀ {M : Type u_1} {N : Type u_2} {μ : M → N → N} {r 
: N → N → Prop} [self : CovariantClass M N μ r], Covariant M N μ r
-/
instance mulRightMono [LE α] [Mul α] [c : MulRightMono α] : MulRightMono αᵒᵈ :=
  ⟨c.1.flip⟩

@[to_additive]
/-
**OrderDual.mulLeftReflectLT** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
形式化陈述：mulLeftReflectLT [LT α] [Mul α] [c : MulLeftReflectLT α] : MulLeftReflectL
T αᵒᵈ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Contravariant.flip`：Contravariant.flip (h : Contravariant M N μ r) : Con
travariant M N μ (flip r)
· 使用定理 `ContravariantClass.elim`：∀ {M : Type u_1} {N : Type u_2} {μ : M → N → N}
 {r : N → N → Prop} [self : ContravariantClass M N μ r],   Contravariant M N μ r
-/
instance mulLeftReflectLT [LT α] [Mul α] [c : MulLeftReflectLT α] : MulLeftReflectLT αᵒᵈ :=
  ⟨c.1.flip⟩

@[to_additive]
/-
**OrderDual.mulLeftStrictMono** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
形式化陈述：mulLeftStrictMono [LT α] [Mul α] [c : MulLeftStrictMono α] : MulLeftStrict
Mono αᵒᵈ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Covariant.flip`：Covariant.flip (h : Covariant M N μ r) : Covariant M N μ
 (flip r)
· 使用定理 `CovariantClass.elim`：∀ {M : Type u_1} {N : Type u_2} {μ : M → N → N} {r 
: N → N → Prop} [self : CovariantClass M N μ r], Covariant M N μ r
-/
instance mulLeftStrictMono [LT α] [Mul α] [c : MulLeftStrictMono α] : MulLeftStrictMono αᵒᵈ :=
  ⟨c.1.flip⟩

@[to_additive]
/-
**OrderDual.mulRightReflectLT** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
形式化陈述：mulRightReflectLT [LT α] [Mul α] [c : MulRightReflectLT α] : MulRightRefle
ctLT αᵒᵈ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Contravariant.flip`：Contravariant.flip (h : Contravariant M N μ r) : Con
travariant M N μ (flip r)
· 使用定理 `ContravariantClass.elim`：∀ {M : Type u_1} {N : Type u_2} {μ : M → N → N}
 {r : N → N → Prop} [self : ContravariantClass M N μ r],   Contravariant M N μ r
-/
instance mulRightReflectLT [LT α] [Mul α] [c : MulRightReflectLT α] : MulRightReflectLT αᵒᵈ :=
  ⟨c.1.flip⟩

@[to_additive]
/-
**OrderDual.mulRightStrictMono** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
形式化陈述：mulRightStrictMono [LT α] [Mul α] [c : MulRightStrictMono α] : MulRightStr
ictMono αᵒᵈ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Covariant.flip`：Covariant.flip (h : Covariant M N μ r) : Covariant M N μ
 (flip r)
· 使用定理 `CovariantClass.elim`：∀ {M : Type u_1} {N : Type u_2} {μ : M → N → N} {r 
: N → N → Prop} [self : CovariantClass M N μ r], Covariant M N μ r
-/
instance mulRightStrictMono [LT α] [Mul α] [c : MulRightStrictMono α] : MulRightStrictMono αᵒᵈ :=
  ⟨c.1.flip⟩

end OrderDual

