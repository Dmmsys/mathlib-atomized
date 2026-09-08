/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Initial and terminal objects in the category of functors

We show that if a functor `F : C ⥤ D` is such that `F.obj X`
is terminal for all `X`, then `F` is a terminal object.

-/

@[expose] public section

namespace CategoryTheory.Functor

open Limits

variable {C D : Type*} [Category* C] [Category* D]

/-- If `F : C ⥤ D` is such that `F.obj X` is terminal for any `X : C`,
then `F` is a terminal object. -/
/-
**CategoryTheory.Functor.isTerminal** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Fu
nctor`。
形式化陈述：isTerminal {F : C ⥤ D} (hF : forall (X : C), IsTerminal (F.obj X)) : IsTer
minal F
参数：hF : forall (X : C), IsTerminal (F.obj X)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : C ⥤ D` is such that `F.obj X` is terminal for any `X : C`,
then `F` is a terminal object.
-/
def isTerminal {F : C ⥤ D} (hF : ∀ (X : C), IsTerminal (F.obj X)) :
    IsTerminal F := by
  refine evaluationJointlyReflectsLimits _
    fun X ↦ IsLimit.equivOfNatIsoOfIso (Functor.emptyExt _ _) _ _ ?_ (hF X)
  exact Cone.ext (Iso.refl _)

/-- If `F : C ⥤ D` is such that `F.obj X` is initial for any `X : C`,
then `F` is an initial object. -/
/-
**CategoryTheory.Functor.isInitial** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Fun
ctor`。
形式化陈述：isInitial {F : C ⥤ D} (hF : forall (X : C), IsInitial (F.obj X)) : IsIniti
al F
参数：hF : forall (X : C), IsInitial (F.obj X)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : C ⥤ D` is such that `F.obj X` is initial for any `X : C`,
then `F` is an initial object.
-/
def isInitial {F : C ⥤ D} (hF : ∀ (X : C), IsInitial (F.obj X)) :
    IsInitial F := by
  refine evaluationJointlyReflectsColimits _
    fun X ↦ IsColimit.equivOfNatIsoOfIso (Functor.emptyExt _ _) _ _ ?_ (hF X)
  exact Cocone.ext (Iso.refl _)

end CategoryTheory.Functor

