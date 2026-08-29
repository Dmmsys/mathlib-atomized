/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Triangulated.Basic
public import Mathlib.CategoryTheory.Triangulated.Opposite.Basic

/-!
# Triangles in the opposite category of a (pre)triangulated category

Let `C` be a (pre)triangulated category.
In `CategoryTheory.Triangulated.Opposite.Basic`, we have constructed
a shift on `Cᵒᵖ` that will be part of a structure of (pre)triangulated
category. In this file, we construct an equivalence of categories
between `(Triangle C)ᵒᵖ` and `Triangle Cᵒᵖ`, called
`CategoryTheory.Pretriangulated.triangleOpEquivalence`. It sends a triangle
`X ⟶ Y ⟶ Z ⟶ X⟦1⟧` in `C` to the triangle `op Z ⟶ op Y ⟶ op X ⟶ (op Z)⟦1⟧` in `Cᵒᵖ`
(without introducing signs).

## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*][verdier1996]

-/

@[expose] public section

namespace CategoryTheory.Pretriangulated

open Category Limits Preadditive ZeroObject Pretriangulated.Opposite

variable (C : Type*) [Category* C] [HasShift C Int]

namespace TriangleOpEquivalence

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The functor which sends a triangle `X ⟶ Y ⟶ Z ⟶ X⟦1⟧` in `C` to the triangle
`op Z ⟶ op Y ⟶ op X ⟶ (op Z)⟦1⟧` in `Cᵒᵖ` (without introducing signs). -/
@[simps]
/--
Definition of `functor` / `functor` 的定义

English:
definition functor
  signature: : (Triangle C)ᵒᵖ ⥤ Triangle Cᵒᵖ where
  body: Triangle.mk T.unop.mor₂.op T.unop.mor₁.op
      ((opShiftFunctorEquivalence C 1).counitIso.inv.app (Opposite.op T.unop.obj₁) ≫
        T.unop.mor₃.op⟦(1 : Int)⟧')
  map {T₁ T₂} φ :=
    { hom₁ := φ.unop.hom₃.op
      hom₂ := φ.unop.hom₂.op
      hom₃ := φ.unop.hom₁.op
      comm₁ := Quiver.Hom.unop_

中文:
定义 functor
  签名: : (Triangle C)ᵒᵖ ⥤ Triangle Cᵒᵖ where
  定义体: Triangle.mk T.unop.mor₂.op T.unop.mor₁.op
      ((opShiftFunctorEquivalence C 1).counitIso.inv.app (Opposite.op T.unop.obj₁) ≫
        T.unop.mor₃.op⟦(1 : Int)⟧')
  map {T₁ T₂} φ :=
    { hom₁ := φ.unop.hom₃.op
      hom₂ := φ.unop.hom₂.op
      hom₃ := φ.unop.hom₁.op
      comm₁ := Quiver.Hom.unop_

Depends on / 依赖: T.unop.mor, Triangle, Triangle.mk
-/
noncomputable def functor : (Triangle C)ᵒᵖ ⥤ Triangle Cᵒᵖ where
  obj T := Triangle.mk T.unop.mor₂.op T.unop.mor₁.op
      ((opShiftFunctorEquivalence C 1).counitIso.inv.app (Opposite.op T.unop.obj₁) ≫
        T.unop.mor₃.op⟦(1 : Int)⟧')
  map {T₁ T₂} φ :=
    { hom₁ := φ.unop.hom₃.op
      hom₂ := φ.unop.hom₂.op
      hom₃ := φ.unop.hom₁.op
      comm₁ := Quiver.Hom.unop_inj φ.unop.comm₂.symm
      comm₂ := Quiver.Hom.unop_inj φ.unop.comm₁.symm
      comm₃ := by
        dsimp
        rw [assoc]; rw [← Functor.map_comp]; rw [← op_comp]; rw [← φ.unop.comm₃]; rw [op_comp]; rw [Functor.map_comp]; rw [opShiftFunctorEquivalence_counitIso_inv_naturality_assoc]
        rfl }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The functor which sends a triangle `X ⟶ Y ⟶ Z ⟶ X⟦1⟧` in `Cᵒᵖ` to the triangle
`Z.unop ⟶ Y.unop ⟶ X.unop ⟶ Z.unop⟦1⟧` in `C` (without introducing signs). -/
@[simps]
/--
Definition of `inverse` / `inverse` 的定义

English:
definition inverse
  signature: : Triangle Cᵒᵖ ⥤ (Triangle C)ᵒᵖ where
  body: Opposite.op (Triangle.mk T.mor₂.unop T.mor₁.unop
      (((opShiftFunctorEquivalence C 1).unitIso.inv.app T.obj₁).unop ≫ T.mor₃.unop⟦(1 : Int)⟧'))
  map {T₁ T₂} φ := Quiver.Hom.op
    { hom₁ := φ.hom₃.unop
      hom₂ := φ.hom₂.unop
      hom₃ := φ.hom₁.unop
      comm₁ := Quiver.Hom.op_inj φ.comm₂.sy

中文:
定义 inverse
  签名: : Triangle Cᵒᵖ ⥤ (Triangle C)ᵒᵖ where
  定义体: Opposite.op (Triangle.mk T.mor₂.unop T.mor₁.unop
      (((opShiftFunctorEquivalence C 1).unitIso.inv.app T.obj₁).unop ≫ T.mor₃.unop⟦(1 : Int)⟧'))
  map {T₁ T₂} φ := Quiver.Hom.op
    { hom₁ := φ.hom₃.unop
      hom₂ := φ.hom₂.unop
      hom₃ := φ.hom₁.unop
      comm₁ := Quiver.Hom.op_inj φ.comm₂.sy

Depends on / 依赖: Opposite, Opposite.op, T.mor, Triangle, Triangle.mk
-/
noncomputable def inverse : Triangle Cᵒᵖ ⥤ (Triangle C)ᵒᵖ where
  obj T := Opposite.op (Triangle.mk T.mor₂.unop T.mor₁.unop
      (((opShiftFunctorEquivalence C 1).unitIso.inv.app T.obj₁).unop ≫ T.mor₃.unop⟦(1 : Int)⟧'))
  map {T₁ T₂} φ := Quiver.Hom.op
    { hom₁ := φ.hom₃.unop
      hom₂ := φ.hom₂.unop
      hom₃ := φ.hom₁.unop
      comm₁ := Quiver.Hom.op_inj φ.comm₂.symm
      comm₂ := Quiver.Hom.op_inj φ.comm₁.symm
      comm₃ := Quiver.Hom.op_inj (by
        dsimp
        rw [assoc]; rw [← opShiftFunctorEquivalence_unitIso_inv_naturality]; rw [← op_comp_assoc]; rw [← Functor.map_comp]; rw [← unop_comp]; rw [← φ.comm₃]; rw [unop_comp]; rw [Functor.map_comp]; rw [op_comp]; rw [assoc]) }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The unit isomorphism of the
equivalence `triangleOpEquivalence C : (Triangle C)ᵒᵖ ≌ Triangle Cᵒᵖ` . -/
@[simps!]
/--
Definition of `unitIso` / `unitIso` 的定义

English:
definition unitIso
  signature: : 𝟭 _ ≅ functor C ⋙ inverse C
  body: NatIso.ofComponents (fun T => Iso.op
    (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp)
      (Quiver.Hom.op_inj
        (by simp [shift_unop_opShiftFunctorEquivalence_counitIso_inv_app]))))
    (fun {T₁ T₂} f => Quiver.Hom.unop_inj (by cat_disch))

中文:
定义 unitIso
  签名: : 𝟭 _ ≅ functor C ⋙ inverse C
  定义体: NatIso.ofComponents (fun T => Iso.op
    (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp)
      (Quiver.Hom.op_inj
        (by simp [shift_unop_opShiftFunctorEquivalence_counitIso_inv_app]))))
    (fun {T₁ T₂} f => Quiver.Hom.unop_inj (by cat_disch))

Depends on / 依赖: Iso.op, Iso.refl, NatIso, NatIso.ofComponents, Quiver, Quiver.Hom.op_inj, Quiver.Hom.unop_inj, Triangle, Triangle.isoMk, cat_disch, ofComponents, op_inj, shift_unop_opShiftFunctorEquivalence_counitIso_inv_app, unop_inj
-/
noncomputable def unitIso : 𝟭 _ ≅ functor C ⋙ inverse C :=
  NatIso.ofComponents (fun T => Iso.op
    (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp)
      (Quiver.Hom.op_inj
        (by simp [shift_unop_opShiftFunctorEquivalence_counitIso_inv_app]))))
    (fun {T₁ T₂} f => Quiver.Hom.unop_inj (by cat_disch))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The counit isomorphism of the
equivalence `triangleOpEquivalence C : (Triangle C)ᵒᵖ ≌ Triangle Cᵒᵖ` . -/
@[simps!]
/--
Definition of `counitIso` / `counitIso` 的定义

English:
definition counitIso
  signature: : inverse C ⋙ functor C ≅ 𝟭 _
  body: NatIso.ofComponents (fun T => by
    refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
    · simp
    · simp
    · dsimp
      rw [Functor.map_id]; rw [comp_id]; rw [id_comp]; rw [Functor.map_comp]; rw [← opShiftFunctorEquivalence_counitIso_inv_naturality_assoc]; rw [opShiftF

中文:
定义 counitIso
  签名: : inverse C ⋙ functor C ≅ 𝟭 _
  定义体: NatIso.ofComponents (fun T => by
    refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
    · simp
    · simp
    · dsimp
      rw [Functor.map_id]; rw [comp_id]; rw [id_comp]; rw [Functor.map_comp]; rw [← opShiftFunctorEquivalence_counitIso_inv_naturality_assoc]; rw [opShiftF

Depends on / 依赖: Functor, Functor.id_obj, Functor.map_comp, Functor.map_id, Iso.hom_inv_id_app, Iso.refl, NatIso, NatIso.ofComponents, Triangle, Triangle.isoMk, cat_disch, comp_id, hom_inv_id_app, id_comp, id_obj, map_comp, map_id, ofComponents, opShiftFunctorEquivalence_counitIso_inv_app_shift, opShiftFunctorEquivalence_counitIso_inv_naturality_assoc
-/
noncomputable def counitIso : inverse C ⋙ functor C ≅ 𝟭 _ :=
  NatIso.ofComponents (fun T => by
    refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
    · simp
    · simp
    · dsimp
      rw [Functor.map_id]; rw [comp_id]; rw [id_comp]; rw [Functor.map_comp]; rw [← opShiftFunctorEquivalence_counitIso_inv_naturality_assoc]; rw [opShiftFunctorEquivalence_counitIso_inv_app_shift]; rw [← Functor.map_comp]; rw [Iso.hom_inv_id_app]; rw [Functor.map_id]
      simp only [Functor.id_obj, comp_id])
    (by cat_disch)

end TriangleOpEquivalence

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- An anti-equivalence between the categories of triangles in `C` and in `Cᵒᵖ`.
A triangle in `Cᵒᵖ` shall be distinguished iff it corresponds to a distinguished
triangle in `C` via this equivalence. -/
@[simps]
/--
Definition of `triangleOpEquivalence` / `triangleOpEquivalence` 的定义

English:
definition triangleOpEquivalence
  signature: :
  body: TriangleOpEquivalence.functor C
  inverse := TriangleOpEquivalence.inverse C
  unitIso := TriangleOpEquivalence.unitIso C
  counitIso := TriangleOpEquivalence.counitIso C

中文:
定义 triangleOpEquivalence
  签名: :
  定义体: TriangleOpEquivalence.functor C
  inverse := TriangleOpEquivalence.inverse C
  unitIso := TriangleOpEquivalence.unitIso C
  counitIso := TriangleOpEquivalence.counitIso C

Depends on / 依赖: TriangleOpEquivalence, TriangleOpEquivalence.functor, functor
-/
noncomputable def triangleOpEquivalence :
    (Triangle C)ᵒᵖ ≌ Triangle Cᵒᵖ where
  functor := TriangleOpEquivalence.functor C
  inverse := TriangleOpEquivalence.inverse C
  unitIso := TriangleOpEquivalence.unitIso C
  counitIso := TriangleOpEquivalence.counitIso C

end CategoryTheory.Pretriangulated
