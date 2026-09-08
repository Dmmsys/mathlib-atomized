/-
Copyright (c) 2024 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.CategoryTheory.Functor.FunctorHom
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# Functors to Type are closed.

Show that `C ⥤ Type max w v u` is monoidal closed for `C` a category in `Type u` with morphisms in
`Type v`, and `w` an arbitrary universe.

## TODO
It should be shown that `C ⥤ Type max w v u` is Cartesian closed.

-/

@[expose] public section


universe w v' v u u'

open CategoryTheory Functor MonoidalCategory

namespace CategoryTheory.FunctorToTypes

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

variable (F : C ⥤ Type (max w v u))

/-- When `F G H : C ⥤ Type max w v u`, we have `(G ⟶ F.functorHom H) ≃ (F ⊗ G ⟶ H)`. -/
@[simps! apply_app symm_apply_app]
/-
**CategoryTheory.FunctorToTypes.functorHomEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.FunctorToTypes`。
形式化陈述：functorHomEquiv (G H : C ⥤ Type (max w v u)) : (G ⟶ F.functorHom H) ≃ (F o
times G ⟶ H)
参数：G H : C ⥤ Type (max w v u)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
When `F G H : C ⥤ Type max w v u`, we have `(G ⟶ F.functorHom H) ≃ (F ⊗ G ⟶ H)`.
-/
def functorHomEquiv (G H : C ⥤ Type (max w v u)) : (G ⟶ F.functorHom H) ≃ (F ⊗ G ⟶ H) :=
  (Functor.functorHomEquiv F H G).trans (homObjEquiv F H G)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A right adjoint of `tensorLeft F`. -/
@[simps! obj_obj obj_map map_app]
/-
**CategoryTheory.FunctorToTypes.rightAdj** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.FunctorToTypes`。
形式化陈述：rightAdj : (C ⥤ Type (max w v u)) ⥤ C ⥤ Type (max w v u) where obj G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A right adjoint of `tensorLeft F`.
-/
def rightAdj : (C ⥤ Type (max w v u)) ⥤ C ⥤ Type (max w v u) where
  obj G := F.functorHom G
  map f := { app X := ↾fun a ↦ {
    app d b := a.app d b ≫ f.app d
    naturality g h := by
      have := a.naturality g h
      change (F.map g ≫ a.app _ (h ≫ g)) ≫ _ = _
      aesop  }}

@[deprecated "Use `(rightAdj F).map instead" (since := "2026-04-08")] alias rightAdj_map := rightAdj

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
attribute [local simp] types_tensorObj_def in
/-- The adjunction `tensorLeft F ⊣ rightAdj F`. -/
/-
**CategoryTheory.FunctorToTypes.adj** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Fu
nctorToTypes`。
形式化陈述：adj : tensorLeft F ⊣ rightAdj F where unit
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The adjunction `tensorLeft F ⊣ rightAdj F`.
-/
def adj : tensorLeft F ⊣ rightAdj F where
  unit := {
    app := fun G ↦ (functorHomEquiv F G _).2 (𝟙 _)
    naturality := fun G H f ↦ by
      ext
      dsimp
      ext
      apply Prod.ext
      · rfl
      · simp }
  counit := { app := fun G ↦ functorHomEquiv F _ G (𝟙 _) }
/-
**CategoryTheory.FunctorToTypes.closed** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.FunctorToTypes`。
形式化陈述：closed : Closed F where rightAdj
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance closed : Closed F where
  rightAdj := rightAdj F
  adj := adj F
/-
**CategoryTheory.FunctorToTypes.monoidalClosed** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.FunctorToTypes`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     CategoryT
heory.MonoidalClosed (CategoryTheory.Functor C (Type (max w v u)))
参数：CategoryTheory.Functor C (Type (max w v u))。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance monoidalClosed : MonoidalClosed (C ⥤ Type (max w v u)) where

end CategoryTheory.FunctorToTypes

