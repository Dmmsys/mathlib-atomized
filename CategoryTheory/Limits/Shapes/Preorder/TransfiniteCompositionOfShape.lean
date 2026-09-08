/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ComposableArrows.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Preorder.WellOrderContinuous
public import Mathlib.CategoryTheory.Limits.Shapes.Preorder.Fin
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Preorder
public import Mathlib.Data.Fin.SuccPredOrder
public import Mathlib.Order.LatticeIntervals
public import Mathlib.Order.Interval.Set.Final

/-!
# A structure to describe transfinite compositions

Given a well-ordered type `J` and a morphism `f : X ⟶ Y` in a category,
we introduce a structure `TransfiniteCompositionOfShape J f` expressing
that `f` is a transfinite composition of shape `J`.
This allows to extend this structure in order to require
more properties or data for the morphisms `F.obj j ⟶ F.obj (Order.succ j)`
which appear in the transfinite composition.
See `MorphismProperty.TransfiniteCompositionOfShape` in the
file `MorphismProperty.TransfiniteComposition`.

-/

@[expose] public section

universe w w' v v' u u'

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (J : Type w) [LinearOrder J] [OrderBot J]
  {X Y : C} (f : X ⟶ Y)

/-- Given a well-ordered type `J`, a morphism `f : X ⟶ Y` in a category `C`
is a transfinite composition of shape `J` if we have a well order continuous
functor `F : J ⥤ C`, an isomorphism `F.obj ⊥ ≅ X`, a colimit cocone for `F`
whose point is `Y`, such that the composition `X ⟶ F.obj ⊥ ⟶ Y` is `f`. -/
/-
**CategoryTheory.TransfiniteCompositionOfShape** 是 Mathlib 中的一个结构，位于命名空间 `Catego
ryTheory`。
形式化陈述：TransfiniteCompositionOfShape [SuccOrder J] [WellFoundedLT J] where /-- a 
well order continuous functor `F : J ⥤ C` -/ F : J ⥤ C /-- the isomorphism `F.ob
j ⊥ ≅ X` -/ isoBot : F.obj ⊥ ≅ X isWellOrderContinuous : F.IsWellOrderContinuous
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a well-ordered type `J`, a morphism `f : X ⟶ Y` in a category `C`
is a transfinite composition of shape `J` if we have a well order continuous
functor `F : J ⥤ C`, an isomorphism `F.obj ⊥ ≅ X`, a colimit cocone for `F`
whose point is `Y`, such that the composition `X ⟶ F.obj ⊥ ⟶ Y` is `f`.
-/
structure TransfiniteCompositionOfShape [SuccOrder J] [WellFoundedLT J] where
  /-- a well order continuous functor `F : J ⥤ C` -/
  F : J ⥤ C
  /-- the isomorphism `F.obj ⊥ ≅ X` -/
  isoBot : F.obj ⊥ ≅ X
  isWellOrderContinuous : F.IsWellOrderContinuous := by infer_instance
  /-- the natural morphism `F.obj j ⟶ Y` -/
  incl : F ⟶ (Functor.const _).obj Y
  /-- the colimit of `F` identifies to `Y` -/
  isColimit : IsColimit (Cocone.mk Y incl)
  fac : isoBot.inv ≫ incl.app ⊥ = f := by cat_disch


initialize_simps_projections TransfiniteCompositionOfShape (-isColimit)

namespace TransfiniteCompositionOfShape

attribute [reassoc (attr := simp)] fac
attribute [instance] isWellOrderContinuous

variable {J f} [SuccOrder J] [WellFoundedLT J] (c : TransfiniteCompositionOfShape J f)

set_option backward.isDefEq.respectTransparency false in
/-- If `f` and `f'` are two isomorphic morphisms, and `f` is a transfinite composition
of shape `J`, then `f'` also is. -/
@[simps]
/-
**CategoryTheory.TransfiniteCompositionOfShape.ofArrowIso** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.TransfiniteCompositionOfShape`。
形式化陈述：ofArrowIso {X' Y' : C} {f' : X' ⟶ Y'} (e : Arrow.mk f ≅ Arrow.mk f') : Tra
nsfiniteCompositionOfShape J f' where F
参数：e : Arrow.mk f ≅ Arrow.mk f'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` and `f'` are two isomorphic morphisms, and `f` is a transfinite compositi
on
of shape `J`, then `f'` also is.
-/
def ofArrowIso {X' Y' : C} {f' : X' ⟶ Y'} (e : Arrow.mk f ≅ Arrow.mk f') :
    TransfiniteCompositionOfShape J f' where
  F := c.F
  isoBot := c.isoBot ≪≫ Arrow.leftFunc.mapIso e
  incl := c.incl ≫ (Functor.const J).map e.hom.right
  isColimit := IsColimit.ofIsoColimit c.isColimit
    (Cocone.ext (Arrow.rightFunc.mapIso e))

/-- If `G : ComposableArrows C n`, then `G.hom : G.left ⟶ G.right` is a
transfinite composition of shape `Fin (n + 1)`. -/
@[simps]
/-
**CategoryTheory.TransfiniteCompositionOfShape.ofComposableArrows** 是 Mathlib 中的
一个定义，位于命名空间 `CategoryTheory.TransfiniteCompositionOfShape`。
形式化陈述：ofComposableArrows {n : Nat} (G : ComposableArrows C n) : TransfiniteCompo
sitionOfShape (Fin (n + 1)) G.hom where F
参数：G : ComposableArrows C n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `G : ComposableArrows C n`, then `G.hom : G.left ⟶ G.right` is a
transfinite composition of shape `Fin (n + 1)`.
-/
def ofComposableArrows {n : ℕ} (G : ComposableArrows C n) :
    TransfiniteCompositionOfShape (Fin (n + 1)) G.hom where
  F := G
  isoBot := Iso.refl _
  incl := _
  isColimit := colimitOfDiagramTerminal (Fin.isTerminalLast n) G
  fac := Category.id_comp _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `f` is a transfinite composition of shape `J`, then it is
also a transfinite composition of shape `J'` if `J' ≃o J`. -/
@[simps]
/-
**CategoryTheory.TransfiniteCompositionOfShape.ofOrderIso** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.TransfiniteCompositionOfShape`。
形式化陈述：ofOrderIso {J' : Type w'} [LinearOrder J'] [OrderBot J'] [SuccOrder J'] [W
ellFoundedLT J'] (e : J' ≃o J) : TransfiniteCompositionOfShape J' f where F
参数：e : J' ≃o J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` is a transfinite composition of shape `J`, then it is
also a transfinite composition of shape `J'` if `J' ≃o J`.
-/
def ofOrderIso {J' : Type w'} [LinearOrder J'] [OrderBot J']
    [SuccOrder J'] [WellFoundedLT J'] (e : J' ≃o J) :
    TransfiniteCompositionOfShape J' f where
  F := e.equivalence.functor ⋙ c.F
  isoBot := c.F.mapIso (eqToIso e.map_bot) ≪≫ c.isoBot
  incl := Functor.whiskerLeft e.equivalence.functor c.incl
  isColimit := IsColimit.whiskerEquivalence (c.isColimit) e.equivalence

set_option backward.isDefEq.respectTransparency false in
/-- If `f` is a transfinite composition of shape `J`, then `F.map f` also is
provided `F` preserves suitable colimits. -/
@[simps]
/-
**CategoryTheory.TransfiniteCompositionOfShape.map** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.TransfiniteCompositionOfShape`。
形式化陈述：map (F : C ⥤ D) [PreservesWellOrderContinuousOfShape J F] [PreservesColimi
tsOfShape J F] : TransfiniteCompositionOfShape J (F.map f) where F
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` is a transfinite composition of shape `J`, then `F.map f` also is
provided `F` preserves suitable colimits.
-/
noncomputable def map (F : C ⥤ D) [PreservesWellOrderContinuousOfShape J F]
    [PreservesColimitsOfShape J F] :
    TransfiniteCompositionOfShape J (F.map f) where
  F := c.F ⋙ F
  isoBot := F.mapIso c.isoBot
  incl := Functor.whiskerRight c.incl F ≫ (Functor.constComp _ _ _).hom
  isColimit :=
    IsColimit.ofIsoColimit (isColimitOfPreserves F c.isColimit)
      (Cocone.ext (Iso.refl _))
  fac := by simp [← Functor.map_comp]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A transfinite composition of shape `J` induces a transfinite composition
of shape `Set.Iic j` for any `j : J`. -/
@[simps]
/-
**CategoryTheory.TransfiniteCompositionOfShape.iic** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.TransfiniteCompositionOfShape`。
形式化陈述：iic (j : J) : TransfiniteCompositionOfShape (Set.Iic j) (c.F.map (homOfLE 
bot_le : ⊥ ⟶ j)) where F
参数：j : J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A transfinite composition of shape `J` induces a transfinite composition
of shape `Set.Iic j` for any `j : J`.
-/
noncomputable def iic (j : J) :
    TransfiniteCompositionOfShape (Set.Iic j) (c.F.map (homOfLE bot_le : ⊥ ⟶ j)) where
  F := (Set.initialSegIic j).monotone.functor ⋙ c.F
  isoBot := Iso.refl _
  incl :=
    { app i := c.F.map (homOfLE i.2)
      naturality i i' φ := by
        dsimp
        rw [← Functor.map_comp, Category.comp_id]
        rfl }
  isColimit := colimitOfDiagramTerminal isTerminalTop _

set_option backward.defeqAttrib.useBackward true in
/-- A transfinite composition of shape `J` induces a transfinite composition
of shape `Set.Ici j` for any `j : J`. -/
@[simps]
/-
**CategoryTheory.TransfiniteCompositionOfShape.ici** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.TransfiniteCompositionOfShape`。
形式化陈述：ici (j : J) : TransfiniteCompositionOfShape (Set.Ici j) (c.incl.app j) whe
re F
参数：j : J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A transfinite composition of shape `J` induces a transfinite composition
of shape `Set.Ici j` for any `j : J`.
-/
noncomputable def ici (j : J) :
    TransfiniteCompositionOfShape (Set.Ici j) (c.incl.app j) where
  F := (Subtype.mono_coe (· ∈ Set.Ici j)).functor ⋙ c.F
  isWellOrderContinuous := Functor.IsWellOrderContinuous.restriction_setIci _
  isoBot := Iso.refl _
  incl := Functor.whiskerLeft _ c.incl
  isColimit := (Functor.Final.isColimitWhiskerEquiv
    (Subtype.mono_coe (· ∈ Set.Ici j)).functor _).2 c.isColimit

end TransfiniteCompositionOfShape

end CategoryTheory

