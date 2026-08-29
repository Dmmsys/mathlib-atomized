/-
Copyright (c) 2021 Luke Kershaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Kershaw
-/
module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Triangulated.Basic

/-!
# Rotate

This file adds the ability to rotate triangles and triangle morphisms.
It also shows that rotation gives an equivalence on the category of triangles.

-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section


noncomputable section

open CategoryTheory

open CategoryTheory.Preadditive

open CategoryTheory.Limits

universe v v₀ v₁ v₂ u u₀ u₁ u₂

namespace CategoryTheory.Pretriangulated

open CategoryTheory.Category

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [HasShift C Int]
variable (X : C)

/-- If you rotate a triangle, you get another triangle.
Given a triangle of the form:
```
      f g h
  X ───> Y ───> Z ───> X⟦1⟧
```
applying `rotate` gives a triangle of the form:
```
      g h -f⟦1⟧'
  Y ───> Z ───> X⟦1⟧ ───> Y⟦1⟧
```
-/
@[simps!]
/--
Definition of `Triangle.rotate` / `Triangle.rotate` 的定义

English:
definition Triangle.rotate
  signature: (T : Triangle C)
  body: Triangle.mk T.mor₂ T.mor₃ (-T.mor₁⟦1⟧')

中文:
定义 Triangle.rotate
  签名: (T : Triangle C)
  定义体: Triangle.mk T.mor₂ T.mor₃ (-T.mor₁⟦1⟧')

Depends on / 依赖: T.mor, Triangle, Triangle.mk
-/
def Triangle.rotate (T : Triangle C) : Triangle C :=
  Triangle.mk T.mor₂ T.mor₃ (-T.mor₁⟦1⟧')

section

/-- Given a triangle of the form:
```
      f g h
  X ───> Y ───> Z ───> X⟦1⟧
```
applying `invRotate` gives a triangle that can be thought of as:
```
        -h⟦-1⟧' f g
  Z⟦-1⟧ ───> X ───> Y ───> Z
```
(note that this diagram doesn't technically fit the definition of triangle, as `Z⟦-1⟧⟦1⟧` is
not necessarily equal to `Z`, but it is isomorphic, by the `counitIso` of `shiftEquiv C 1`)
-/
@[simps!]
/--
Definition of `Triangle.invRotate` / `Triangle.invRotate` 的定义

English:
definition Triangle.invRotate
  signature: (T : Triangle C)
  body: Triangle.mk (-T.mor₃⟦(-1 : Int)⟧' ≫ (shiftEquiv C (1 : Int)).unitIso.inv.app _) (T.mor₁)
    (T.mor₂ ≫ (shiftEquiv C (1 : Int)).counitIso.inv.app _)

中文:
定义 Triangle.invRotate
  签名: (T : Triangle C)
  定义体: Triangle.mk (-T.mor₃⟦(-1 : Int)⟧' ≫ (shiftEquiv C (1 : Int)).unitIso.inv.app _) (T.mor₁)
    (T.mor₂ ≫ (shiftEquiv C (1 : Int)).counitIso.inv.app _)

Depends on / 依赖: T.mor, Triangle, Triangle.mk, counitIso, counitIso.inv.app, shiftEquiv, unitIso, unitIso.inv.app
-/
def Triangle.invRotate (T : Triangle C) : Triangle C :=
  Triangle.mk (-T.mor₃⟦(-1 : Int)⟧' ≫ (shiftEquiv C (1 : Int)).unitIso.inv.app _) (T.mor₁)
    (T.mor₂ ≫ (shiftEquiv C (1 : Int)).counitIso.inv.app _)

end

attribute [local simp] shift_shift_neg' shift_neg_shift'
  shift_shiftFunctorCompIsoId_add_neg_cancel_inv_app
  shift_shiftFunctorCompIsoId_add_neg_cancel_hom_app

variable (C)

set_option backward.defeqAttrib.useBackward true in
/-- Rotating triangles gives an endofunctor on the category of triangles in `C`.
-/
@[simps]
/--
Definition of `rotate` / `rotate` 的定义

English:
definition rotate
  signature: : Triangle C ⥤ Triangle C where
  body: Triangle.rotate
  map f :=
  { hom₁ := f.hom₂
    hom₂ := f.hom₃
    hom₃ := f.hom₁⟦1⟧'
    comm₃ := by
      dsimp
      simp only [comp_neg, neg_comp, ← Functor.map_comp, f.comm₁] }

中文:
定义 rotate
  签名: : Triangle C ⥤ Triangle C where
  定义体: Triangle.rotate
  map f :=
  { hom₁ := f.hom₂
    hom₂ := f.hom₃
    hom₃ := f.hom₁⟦1⟧'
    comm₃ := by
      dsimp
      simp only [comp_neg, neg_comp, ← Functor.map_comp, f.comm₁] }

Depends on / 依赖: Triangle, Triangle.rotate, rotate
-/
def rotate : Triangle C ⥤ Triangle C where
  obj := Triangle.rotate
  map f :=
  { hom₁ := f.hom₂
    hom₂ := f.hom₃
    hom₃ := f.hom₁⟦1⟧'
    comm₃ := by
      dsimp
      simp only [comp_neg, neg_comp, ← Functor.map_comp, f.comm₁] }

set_option backward.isDefEq.respectTransparency false in
/-- The inverse rotation of triangles gives an endofunctor on the category of triangles in `C`.
-/
@[simps]
/--
Definition of `invRotate` / `invRotate` 的定义

English:
definition invRotate
  signature: : Triangle C ⥤ Triangle C where
  body: Triangle.invRotate
  map f :=
  { hom₁ := f.hom₃⟦-1⟧'
    hom₂ := f.hom₁
    hom₃ := f.hom₂
    comm₁ := by
      dsimp
      simp only [comp_neg, ← Functor.map_comp_assoc, ← f.comm₃]
      rw [Functor.map_comp]
      simp }

中文:
定义 invRotate
  签名: : Triangle C ⥤ Triangle C where
  定义体: Triangle.invRotate
  map f :=
  { hom₁ := f.hom₃⟦-1⟧'
    hom₂ := f.hom₁
    hom₃ := f.hom₂
    comm₁ := by
      dsimp
      simp only [comp_neg, ← Functor.map_comp_assoc, ← f.comm₃]
      rw [Functor.map_comp]
      simp }

Depends on / 依赖: Triangle, Triangle.invRotate, invRotate
-/
def invRotate : Triangle C ⥤ Triangle C where
  obj := Triangle.invRotate
  map f :=
  { hom₁ := f.hom₃⟦-1⟧'
    hom₂ := f.hom₁
    hom₃ := f.hom₂
    comm₁ := by
      dsimp
      simp only [comp_neg, ← Functor.map_comp_assoc, ← f.comm₃]
      rw [Functor.map_comp]
      simp }

variable {C}
variable [forall n : Int, Functor.Additive (shiftFunctor C n)]

set_option backward.isDefEq.respectTransparency false in
/-- The unit isomorphism of the auto-equivalence of categories `triangleRotation C` of
`Triangle C` given by the rotation of triangles. -/
@[simps!]
/--
Definition of `rotCompInvRot` / `rotCompInvRot` 的定义

English:
definition rotCompInvRot
  signature: : 𝟭 (Triangle C) ≅ rotate C ⋙ invRotate C
  body: NatIso.ofComponents fun T => Triangle.isoMk _ _
    ((shiftEquiv C (1 : Int)).unitIso.app T.obj₁) (Iso.refl _) (Iso.refl _)

中文:
定义 rotCompInvRot
  签名: : 𝟭 (Triangle C) ≅ rotate C ⋙ invRotate C
  定义体: NatIso.ofComponents fun T => Triangle.isoMk _ _
    ((shiftEquiv C (1 : Int)).unitIso.app T.obj₁) (Iso.refl _) (Iso.refl _)

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, T.obj, Triangle, Triangle.isoMk, ofComponents, shiftEquiv, unitIso, unitIso.app
-/
def rotCompInvRot : 𝟭 (Triangle C) ≅ rotate C ⋙ invRotate C :=
  NatIso.ofComponents fun T => Triangle.isoMk _ _
    ((shiftEquiv C (1 : Int)).unitIso.app T.obj₁) (Iso.refl _) (Iso.refl _)

set_option backward.isDefEq.respectTransparency false in
/-- The counit isomorphism of the auto-equivalence of categories `triangleRotation C` of
`Triangle C` given by the rotation of triangles. -/
@[simps!]
/--
Definition of `invRotCompRot` / `invRotCompRot` 的定义

English:
definition invRotCompRot
  signature: : invRotate C ⋙ rotate C ≅ 𝟭 (Triangle C)
  body: NatIso.ofComponents fun T => Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    ((shiftEquiv C (1 : Int)).counitIso.app T.obj₃)

中文:
定义 invRotCompRot
  签名: : invRotate C ⋙ rotate C ≅ 𝟭 (Triangle C)
  定义体: NatIso.ofComponents fun T => Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    ((shiftEquiv C (1 : Int)).counitIso.app T.obj₃)

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, T.obj, Triangle, Triangle.isoMk, counitIso, counitIso.app, ofComponents, shiftEquiv
-/
def invRotCompRot : invRotate C ⋙ rotate C ≅ 𝟭 (Triangle C) :=
  NatIso.ofComponents fun T => Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    ((shiftEquiv C (1 : Int)).counitIso.app T.obj₃)

set_option backward.isDefEq.respectTransparency false in
variable (C) in
/-- Rotating triangles gives an auto-equivalence on the category of triangles in `C`.
-/
@[simps]
/--
Definition of `triangleRotation` / `triangleRotation` 的定义

English:
definition triangleRotation
  signature: : Equivalence (Triangle C) (Triangle C) where
  body: rotate C
  inverse := invRotate C
  unitIso := rotCompInvRot
  counitIso := invRotCompRot

中文:
定义 triangleRotation
  签名: : Equivalence (Triangle C) (Triangle C) where
  定义体: rotate C
  inverse := invRotate C
  unitIso := rotCompInvRot
  counitIso := invRotCompRot

Depends on / 依赖: rotate
-/
def triangleRotation : Equivalence (Triangle C) (Triangle C) where
  functor := rotate C
  inverse := invRotate C
  unitIso := rotCompInvRot
  counitIso := invRotCompRot

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (rotate C).IsEquivalence
  body: by
  change (triangleRotation C).functor.IsEquivalence
  infer_instance

中文:
实例 :
  签名: (rotate C).IsEquivalence
  定义体: by
  change (triangleRotation C).functor.IsEquivalence
  infer_instance

Depends on / 依赖: IsEquivalence, functor, functor.IsEquivalence, infer_instance, triangleRotation
-/
instance : (rotate C).IsEquivalence := by
  change (triangleRotation C).functor.IsEquivalence
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (invRotate C).IsEquivalence
  body: by
  change (triangleRotation C).inverse.IsEquivalence
  infer_instance

中文:
实例 :
  签名: (invRotate C).IsEquivalence
  定义体: by
  change (triangleRotation C).inverse.IsEquivalence
  infer_instance

Depends on / 依赖: IsEquivalence, infer_instance, inverse, inverse.IsEquivalence, triangleRotation
-/
instance : (invRotate C).IsEquivalence := by
  change (triangleRotation C).inverse.IsEquivalence
  infer_instance

end CategoryTheory.Pretriangulated
