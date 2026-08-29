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

/--
Definition of `TransfiniteCompositionOfShape` / `TransfiniteCompositionOfShape` 的定义

English:
structure TransfiniteCompositionOfShape
  parameters: [SuccOrder J] [WellFoundedLT J]
  axioms and operations (6):
    - F : J ⥤ C
    - isoBot : F.obj ⊥ ≅ X
    - isWellOrderContinuous : F.IsWellOrderContinuous  [default: by infer_instance]
    - incl : F ⟶ (Functor.const _).obj Y
    - isColimit : IsColimit (Cocone.mk Y incl)
    - fac : isoBot.inv ≫ incl.app ⊥ = f  [default: by cat_disch]

中文:
结构 TransfiniteCompositionOfShape
  参数: [SuccOrder J] [WellFoundedLT J]
  公理与运算 (6 个):
    - F : J ⥤ C
    - isoBot : F.obj ⊥ ≅ X
    - isWellOrderContinuous : F.IsWellOrderContinuous  [默认: by infer_instance]
    - incl : F ⟶ (Functor.const _).obj Y
    - isColimit : IsColimit (Cocone.mk Y incl)
    - fac : isoBot.inv ≫ incl.app ⊥ = f  [默认: by cat_disch]

Depends on / 依赖: infer_instance
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
/--
Definition of `ofArrowIso` / `ofArrowIso` 的定义

English:
definition ofArrowIso
  signature: {X' Y' : C} {f' : X' ⟶ Y'} (e : Arrow.mk f ≅ Arrow.mk f')
  body: c.F
  isoBot := c.isoBot ≪≫ Arrow.leftFunc.mapIso e
  incl := c.incl ≫ (Functor.const J).map e.hom.right
  isColimit := IsColimit.ofIsoColimit c.isColimit
    (Cocone.ext (Arrow.rightFunc.mapIso e))

中文:
定义 ofArrowIso
  签名: {X' Y' : C} {f' : X' ⟶ Y'} (e : Arrow.mk f ≅ Arrow.mk f')
  定义体: c.F
  isoBot := c.isoBot ≪≫ Arrow.leftFunc.mapIso e
  incl := c.incl ≫ (Functor.const J).map e.hom.right
  isColimit := IsColimit.ofIsoColimit c.isColimit
    (Cocone.ext (Arrow.rightFunc.mapIso e))
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
/--
Definition of `ofComposableArrows` / `ofComposableArrows` 的定义

English:
definition ofComposableArrows
  signature: {n : Nat} (G : ComposableArrows C n)
  body: G
  isoBot := Iso.refl _
  incl := _
  isColimit := colimitOfDiagramTerminal (Fin.isTerminalLast n) G
  fac := Category.id_comp _

中文:
定义 ofComposableArrows
  签名: {n : 自然数} (G : ComposableArrows C n)
  定义体: G
  isoBot := Iso.refl _
  incl := _
  isColimit := colimitOfDiagramTerminal (Fin.isTerminalLast n) G
  fac := Category.id_comp _
-/
def ofComposableArrows {n : Nat} (G : ComposableArrows C n) :
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
/--
Definition of `ofOrderIso` / `ofOrderIso` 的定义

English:
definition ofOrderIso
  signature: {J' : Type w'} [LinearOrder J'] [OrderBot J']
  body: e.equivalence.functor ⋙ c.F
  isoBot := c.F.mapIso (eqToIso e.map_bot) ≪≫ c.isoBot
  incl := Functor.whiskerLeft e.equivalence.functor c.incl
  isColimit := IsColimit.whiskerEquivalence (c.isColimit) e.equivalence

中文:
定义 ofOrderIso
  签名: {J' : Type w'} [LinearOrder J'] [OrderBot J']
  定义体: e.equivalence.functor ⋙ c.F
  isoBot := c.F.mapIso (eqToIso e.map_bot) ≪≫ c.isoBot
  incl := Functor.whiskerLeft e.equivalence.functor c.incl
  isColimit := IsColimit.whiskerEquivalence (c.isColimit) e.equivalence

Depends on / 依赖: e.equivalence.functor, equivalence, functor
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
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (F : C ⥤ D) [PreservesWellOrderContinuousOfShape J F]
  body: c.F ⋙ F
  isoBot := F.mapIso c.isoBot
  incl := Functor.whiskerRight c.incl F ≫ (Functor.constComp _ _ _).hom
  isColimit :=
    IsColimit.ofIsoColimit (isColimitOfPreserves F c.isColimit)
      (Cocone.ext (Iso.refl _))
  fac := by simp [← Functor.map_comp]

中文:
定义 map
  签名: (F : C ⥤ D) [PreservesWellOrderContinuousOfShape J F]
  定义体: c.F ⋙ F
  isoBot := F.mapIso c.isoBot
  incl := Functor.whiskerRight c.incl F ≫ (Functor.constComp _ _ _).hom
  isColimit :=
    IsColimit.ofIsoColimit (isColimitOfPreserves F c.isColimit)
      (Cocone.ext (Iso.refl _))
  fac := by simp [← Functor.map_comp]
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
/--
Definition of `iic` / `iic` 的定义

English:
definition iic
  signature: (j : J)
  body: (Set.initialSegIic j).monotone.functor ⋙ c.F
  isoBot := Iso.refl _
  incl :=
    { app i := c.F.map (homOfLE i.2)
      naturality i i' φ := by
        dsimp
        rw [← Functor.map_comp]; rw [Category.comp_id]
        rfl }
  isColimit := colimitOfDiagramTerminal isTerminalTop _

中文:
定义 iic
  签名: (j : J)
  定义体: (Set.initialSegIic j).monotone.functor ⋙ c.F
  isoBot := Iso.refl _
  incl :=
    { app i := c.F.map (homOfLE i.2)
      naturality i i' φ := by
        dsimp
        rw [← Functor.map_comp]; rw [Category.comp_id]
        rfl }
  isColimit := colimitOfDiagramTerminal isTerminalTop _

Depends on / 依赖: Set.initialSegIic, functor, initialSegIic, monotone, monotone.functor
-/
noncomputable def iic (j : J) :
    TransfiniteCompositionOfShape (Set.Iic j) (c.F.map (homOfLE bot_le : ⊥ ⟶ j)) where
  F := (Set.initialSegIic j).monotone.functor ⋙ c.F
  isoBot := Iso.refl _
  incl :=
    { app i := c.F.map (homOfLE i.2)
      naturality i i' φ := by
        dsimp
        rw [← Functor.map_comp]; rw [Category.comp_id]
        rfl }
  isColimit := colimitOfDiagramTerminal isTerminalTop _

set_option backward.defeqAttrib.useBackward true in
/-- A transfinite composition of shape `J` induces a transfinite composition
of shape `Set.Ici j` for any `j : J`. -/
@[simps]
/--
Definition of `ici` / `ici` 的定义

English:
definition ici
  signature: (j : J)
  body: (Subtype.mono_coe (· in Set.Ici j)).functor ⋙ c.F
  isWellOrderContinuous := Functor.IsWellOrderContinuous.restriction_setIci _
  isoBot := Iso.refl _
  incl := Functor.whiskerLeft _ c.incl
  isColimit := (Functor.Final.isColimitWhiskerEquiv
    (Subtype.mono_coe (· in Set.Ici j)).functor _).2 c.isC

中文:
定义 ici
  签名: (j : J)
  定义体: (Subtype.mono_coe (· in Set.Ici j)).functor ⋙ c.F
  isWellOrderContinuous := Functor.IsWellOrderContinuous.restriction_setIci _
  isoBot := Iso.refl _
  incl := Functor.whiskerLeft _ c.incl
  isColimit := (Functor.Final.isColimitWhiskerEquiv
    (Subtype.mono_coe (· in Set.Ici j)).functor _).2 c.isC

Depends on / 依赖: Set.Ici, Subtype, Subtype.mono_coe, functor, mono_coe
-/
noncomputable def ici (j : J) :
    TransfiniteCompositionOfShape (Set.Ici j) (c.incl.app j) where
  F := (Subtype.mono_coe (· in Set.Ici j)).functor ⋙ c.F
  isWellOrderContinuous := Functor.IsWellOrderContinuous.restriction_setIci _
  isoBot := Iso.refl _
  incl := Functor.whiskerLeft _ c.incl
  isColimit := (Functor.Final.isColimitWhiskerEquiv
    (Subtype.mono_coe (· in Set.Ici j)).functor _).2 c.isColimit

end TransfiniteCompositionOfShape

end CategoryTheory
