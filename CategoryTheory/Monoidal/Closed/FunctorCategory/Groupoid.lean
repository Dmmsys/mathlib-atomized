/-
Copyright (c) 2022 Antoine Labelle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory

/-!
# Functors from a groupoid into a monoidal closed category form a monoidal closed category.

(Using the pointwise monoidal structure on the functor category.)
-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

universe v u

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed

namespace CategoryTheory.Functor

variable {D : Type u} {C : Type*} [Groupoid.{v} D] [Category* C]
  [MonoidalCategory C] [MonoidalClosed C]

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- Auxiliary definition for `CategoryTheory.Functor.closed`.
The internal hom functor `F ⟶[C] -` -/
@[simps!]
/-
**CategoryTheory.Functor.closedIhom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Fu
nctor`。
形式化陈述：closedIhom (F : D ⥤ C) : (D ⥤ C) ⥤ D ⥤ C
参数：F : D ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `CategoryTheory.Functor.closed`.
The internal hom functor `F ⟶[C] -`
-/
def closedIhom (F : D ⥤ C) : (D ⥤ C) ⥤ D ⥤ C :=
  ((whiskeringRight₂ D Cᵒᵖ C C).obj internalHom).obj
    ((Groupoid.invEquivalence D).functor ⋙ F.op)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `CategoryTheory.Functor.closed`.
The unit for the adjunction `(tensorLeft F) ⊣ (ihom F)`. -/
@[simps]
/-
**CategoryTheory.Functor.closedUnit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Fu
nctor`。
形式化陈述：closedUnit (F : D ⥤ C) : 𝟭 (D ⥤ C) ⟶ tensorLeft F ⋙ closedIhom F where app
 G
参数：F : D ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `CategoryTheory.Functor.closed`.
The unit for the adjunction `(tensorLeft F) ⊣ (ihom F)`.
-/
def closedUnit (F : D ⥤ C) : 𝟭 (D ⥤ C) ⟶ tensorLeft F ⋙ closedIhom F where
  app G :=
  { app := fun X => (ihom.coev (F.obj X)).app (G.obj X)
    naturality := by
      intro X Y f
      dsimp
      simp only [ihom.coev_naturality, closedIhom_obj_map, Monoidal.tensorObj_map]
      dsimp
      rw [coev_app_comp_pre_app_assoc, ← Functor.map_comp, tensorHom_def]
      simp }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Auxiliary definition for `CategoryTheory.Functor.closed`.
The counit for the adjunction `(tensorLeft F) ⊣ (ihom F)`. -/
@[simps]
/-
**CategoryTheory.Functor.closedCounit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Functor`。
形式化陈述：closedCounit (F : D ⥤ C) : closedIhom F ⋙ tensorLeft F ⟶ 𝟭 (D ⥤ C) where a
pp G
参数：F : D ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `CategoryTheory.Functor.closed`.
The counit for the adjunction `(tensorLeft F) ⊣ (ihom F)`.
-/
def closedCounit (F : D ⥤ C) : closedIhom F ⋙ tensorLeft F ⟶ 𝟭 (D ⥤ C) where
  app G :=
  { app := fun X => (ihom.ev (F.obj X)).app (G.obj X)
    naturality := by
      intro X Y f
      dsimp
      simp only [closedIhom_obj_map, pre_comm_ihom_map]
      rw [tensorHom_def]
      simp }

set_option backward.isDefEq.respectTransparency false in
/-- If `C` is a monoidal closed category and `D` is a groupoid, then every functor `F : D ⥤ C` is
closed in the functor category `F : D ⥤ C` with the pointwise monoidal structure. -/
/-
**CategoryTheory.Functor.closed** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functo
r`。
形式化陈述：closed (F : D ⥤ C) : Closed F where rightAdj
参数：F : D ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `C` is a monoidal closed category and `D` is a groupoid, then every functor `
F : D ⥤ C` is
closed in the functor category `F : D ⥤ C` with the pointwise monoidal structure
.
-/
instance closed (F : D ⥤ C) : Closed F where
  rightAdj := closedIhom F
  adj :=
    { unit := closedUnit F
      counit := closedCounit F }

/-- If `C` is a monoidal closed category and `D` is a groupoid, then the functor category `D ⥤ C`,
with the pointwise monoidal structure, is monoidal closed. -/
@[simps! closed_adj]
/-
**CategoryTheory.Functor.monoidalClosed** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Functor`。
形式化陈述：{D : Type u} →   {C : Type u_1} →     [inst : CategoryTheory.Groupoid D] →
       [inst_1 : CategoryTheory.Category.{v_1, u_1} C] →         [inst_2 : Categ
oryTheory.MonoidalCategory C] →           [CategoryTheory.MonoidalClosed C] → Ca
tegoryTheory.MonoidalClosed (CategoryTheory.Functor D C)
参数：CategoryTheory.Functor D C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `C` is a monoidal closed category and `D` is a groupoid, then the functor cat
egory `D ⥤ C`,
with the pointwise monoidal structure, is monoidal closed.
-/
instance monoidalClosed : MonoidalClosed (D ⥤ C) where
/-
**CategoryTheory.Functor.ihom_map** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Func
tor`。
形式化陈述：ihom_map (F : D ⥤ C) {G H : D ⥤ C} (f : G ⟶ H) : (ihom F).map f = (closedI
hom F).map f
参数：F : D ⥤ C；f : G ⟶ H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ihom_map (F : D ⥤ C) {G H : D ⥤ C} (f : G ⟶ H) : (ihom F).map f = (closedIhom F).map f :=
  rfl
/-
**CategoryTheory.Functor.ihom_ev_app** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.F
unctor`。
形式化陈述：ihom_ev_app (F G : D ⥤ C) : (ihom.ev F).app G = (closedCounit F).app G
参数：F G : D ⥤ C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ihom_ev_app (F G : D ⥤ C) : (ihom.ev F).app G = (closedCounit F).app G :=
  rfl
/-
**CategoryTheory.Functor.ihom_coev_app** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Functor`。
形式化陈述：ihom_coev_app (F G : D ⥤ C) : (ihom.coev F).app G = (closedUnit F).app G
参数：F G : D ⥤ C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ihom_coev_app (F G : D ⥤ C) : (ihom.coev F).app G = (closedUnit F).app G :=
  rfl

end CategoryTheory.Functor

