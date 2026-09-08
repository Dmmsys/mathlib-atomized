/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.CommSq
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Square

/-!
# Relation between pullback/pushout squares and kernel/cokernel sequences

This file is the bundled counterpart of `Mathlib/Algebra/Homology/CommSq.lean`.
The same results are obtained here for squares `sq : Square C` where
`C` is an additive category.

-/

@[expose] public section
namespace CategoryTheory

open Category Limits

namespace Square

variable {C : Type*} [Category* C] [Preadditive C]
  (sq : Square C) [HasBinaryBiproduct sq.X₂ sq.X₃]

/-- The cokernel cofork attached to a commutative square in a preadditive category. -/
/-
**CategoryTheory.Square.cokernelCofork** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheo
ry.Square`。
形式化陈述：cokernelCofork : CokernelCofork (biprod.lift sq.f₁₂ (-sq.f₁₃))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cokernel cofork attached to a commutative square in a preadditive category.
-/
noncomputable abbrev cokernelCofork :
    CokernelCofork (biprod.lift sq.f₁₂ (-sq.f₁₃)) :=
  CokernelCofork.ofπ (biprod.desc sq.f₂₄ sq.f₃₄) (by simp [sq.fac])

/-- A commutative square in a preadditive category is a pushout square iff
the corresponding diagram `X₁ ⟶ X₂ ⊞ X₃ ⟶ X₄ ⟶ 0` makes `X₄` a cokernel. -/
/-
**CategoryTheory.Square.isPushoutEquivIsColimitCokernelCofork** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.Square`。
形式化陈述：isPushoutEquivIsColimitCokernelCofork : sq.IsPushout ≃ IsColimit sq.cokern
elCofork
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `CategoryTheory.Square.IsPushout.mk`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] (sq : CategoryTheory.Square C)   (h : CategoryTheory.Limits
.IsColimit sq.pushoutCoc…
· 使用引理 `CategoryTheory.Square.commSq`：commSq (sq : Square C) : CommSq sq.f₁₂ sq.
f₁₃ sq.f₂₄ sq.f₃₄ where w

--- 原说明 ---
A commutative square in a preadditive category is a pushout square iff
the corresponding diagram `X₁ ⟶ X₂ ⊞ X₃ ⟶ X₄ ⟶ 0` makes `X₄` a cokernel.
-/
noncomputable def isPushoutEquivIsColimitCokernelCofork :
    sq.IsPushout ≃ IsColimit sq.cokernelCofork :=
  Equiv.trans
    { toFun := fun h ↦ h.isColimit
      invFun := fun h ↦ IsPushout.mk _ h
      right_inv := fun _ ↦ Subsingleton.elim _ _ }
    sq.commSq.isColimitEquivIsColimitCokernelCofork

variable {sq} in
/-- The colimit cokernel cofork attached to a pushout square. -/
/-
**CategoryTheory.Square.IsPushout.isColimitCokernelCofork** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Square.IsPushout`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.Preadditive C] →       {sq : CategoryTheory.Square C} →   
      [inst_2 : CategoryTheory.Limits.HasBinaryBiproduct sq.X₂ sq.X₃] →         
  sq.IsPushout → CategoryTheory.Limits.IsColimit sq.cokernelCofork
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The colimit cokernel cofork attached to a pushout square.
-/
noncomputable def IsPushout.isColimitCokernelCofork (h : sq.IsPushout) :
    IsColimit sq.cokernelCofork :=
  h.isColimitEquivIsColimitCokernelCofork h.isColimit

/-- The kernel fork attached to a commutative square in a preadditive category. -/
/-
**CategoryTheory.Square.kernelFork** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.S
quare`。
形式化陈述：kernelFork : KernelFork (biprod.desc sq.f₂₄ (-sq.f₃₄))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The kernel fork attached to a commutative square in a preadditive category.
-/
noncomputable abbrev kernelFork :
    KernelFork (biprod.desc sq.f₂₄ (-sq.f₃₄)) :=
  KernelFork.ofι (biprod.lift sq.f₁₂ sq.f₁₃) (by simp [sq.fac])

/-- A commutative square in a preadditive category is a pullback square iff
the corresponding diagram `0 ⟶ X₁ ⟶ X₂ ⊞ X₃ ⟶ X₄ ⟶ 0` makes `X₁` a kernel. -/
/-
**CategoryTheory.Square.isPullbackEquivIsLimitKernelFork** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.Square`。
形式化陈述：isPullbackEquivIsLimitKernelFork : sq.IsPullback ≃ IsLimit sq.kernelFork
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `CategoryTheory.Square.IsPullback.mk`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] (sq : CategoryTheory.Square C)   (h : CategoryTheory.Limit
s.IsLimit sq.pullbackCone…
· 使用引理 `CategoryTheory.Square.commSq`：commSq (sq : Square C) : CommSq sq.f₁₂ sq.
f₁₃ sq.f₂₄ sq.f₃₄ where w

--- 原说明 ---
A commutative square in a preadditive category is a pullback square iff
the corresponding diagram `0 ⟶ X₁ ⟶ X₂ ⊞ X₃ ⟶ X₄ ⟶ 0` makes `X₁` a kernel.
-/
noncomputable def isPullbackEquivIsLimitKernelFork :
    sq.IsPullback ≃ IsLimit sq.kernelFork :=
  Equiv.trans
    { toFun := fun h ↦ h.isLimit
      invFun := fun h ↦ IsPullback.mk _ h
      right_inv := fun _ ↦ Subsingleton.elim _ _ }
    sq.commSq.isLimitEquivIsLimitKernelFork

variable {sq} in
/-- The limit kernel fork attached to a pullback square. -/
/-
**CategoryTheory.Square.IsPullback.isLimitKernelFork** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Square.IsPullback`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.Preadditive C] →       {sq : CategoryTheory.Square C} →   
      [inst_2 : CategoryTheory.Limits.HasBinaryBiproduct sq.X₂ sq.X₃] →         
  sq.IsPullback → CategoryTheory.Limits.IsLimit sq.kernelFork
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The limit kernel fork attached to a pullback square.
-/
noncomputable def IsPullback.isLimitKernelFork (h : sq.IsPullback) :
    IsLimit sq.kernelFork :=
  h.isLimitEquivIsLimitKernelFork h.isLimit

end Square

end CategoryTheory

