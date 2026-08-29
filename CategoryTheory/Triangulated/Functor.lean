/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import Mathlib.CategoryTheory.ComposableArrows.Basic
public import Mathlib.CategoryTheory.Shift.CommShift

/-!
# Triangulated functors

In this file, when `C` and `D` are categories equipped with a shift by `ℤ` and
`F : C ⥤ D` is a functor which commutes with the shift, we define the induced
functor `F.mapTriangle : Triangle C ⥤ Triangle D` on the categories of
triangles. When `C` and `D` are pretriangulated, a triangulated functor
is such a functor `F` which also sends distinguished triangles to
distinguished triangles: this defines the typeclass `Functor.IsTriangulated`.

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

namespace CategoryTheory

open Category Limits Pretriangulated Preadditive

namespace Functor

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [HasShift C Int] [HasShift D Int] [HasShift E Int]
  (F : C ⥤ D) [F.CommShift Int] (G : D ⥤ E) [G.CommShift Int]

set_option backward.defeqAttrib.useBackward true in
/-- The functor `Triangle C ⥤ Triangle D` that is induced by a functor `F : C ⥤ D`
which commutes with shift by `ℤ`. -/
@[simps]
/--
Definition of `mapTriangle` / `mapTriangle` 的定义

English:
definition mapTriangle
  signature: : Triangle C ⥤ Triangle D where
  body: Triangle.mk (F.map T.mor₁) (F.map T.mor₂)
    (F.map T.mor₃ ≫ (F.commShiftIso (1 : Int)).hom.app T.obj₁)
  map f :=
    { hom₁ := F.map f.hom₁
      hom₂ := F.map f.hom₂
      hom₃ := F.map f.hom₃
      comm₁ := by dsimp; simp only [← F.map_comp, f.comm₁]
      comm₂ := by dsimp; simp only [← F.map_

中文:
定义 mapTriangle
  签名: : Triangle C ⥤ Triangle D where
  定义体: Triangle.mk (F.map T.mor₁) (F.map T.mor₂)
    (F.map T.mor₃ ≫ (F.commShiftIso (1 : Int)).hom.app T.obj₁)
  map f :=
    { hom₁ := F.map f.hom₁
      hom₂ := F.map f.hom₂
      hom₃ := F.map f.hom₃
      comm₁ := by dsimp; simp only [← F.map_comp, f.comm₁]
      comm₂ := by dsimp; simp only [← F.map_

Depends on / 依赖: F.map, T.mor, Triangle, Triangle.mk
-/
def mapTriangle : Triangle C ⥤ Triangle D where
  obj T := Triangle.mk (F.map T.mor₁) (F.map T.mor₂)
    (F.map T.mor₃ ≫ (F.commShiftIso (1 : Int)).hom.app T.obj₁)
  map f :=
    { hom₁ := F.map f.hom₁
      hom₂ := F.map f.hom₂
      hom₃ := F.map f.hom₃
      comm₁ := by dsimp; simp only [← F.map_comp, f.comm₁]
      comm₂ := by dsimp; simp only [← F.map_comp, f.comm₂]
      comm₃ := by
        dsimp [Functor.comp]
        simp only [Category.assoc, ← NatTrans.naturality,
          ← F.map_comp_assoc, f.comm₃] }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Faithful
  signature: F] : Faithful F.mapTriangle where
  body: by
    ext <;> apply F.map_injective
    · exact congr_arg TriangleMorphism.hom₁ h
    · exact congr_arg TriangleMorphism.hom₂ h
    · exact congr_arg TriangleMorphism.hom₃ h

中文:
实例 [忠实
  签名: F] : 忠实 F.mapTriangle where
  定义体: by
    ext <;> apply F.map_injective
    · exact congr_arg TriangleMorphism.hom₁ h
    · exact congr_arg TriangleMorphism.hom₂ h
    · exact congr_arg TriangleMorphism.hom₃ h

Depends on / 依赖: F.map_injective, TriangleMorphism, TriangleMorphism.hom, congr_arg, map_injective
-/
instance [Faithful F] : Faithful F.mapTriangle where
  map_injective {X Y} f g h := by
    ext <;> apply F.map_injective
    · exact congr_arg TriangleMorphism.hom₁ h
    · exact congr_arg TriangleMorphism.hom₂ h
    · exact congr_arg TriangleMorphism.hom₃ h

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Full
  signature: F] [Faithful F] : Full F.mapTriangle where
  body: ⟨{hom₁ := F.preimage f.hom₁
      hom₂ := F.preimage f.hom₂
      hom₃ := F.preimage f.hom₃
      comm₁ := F.map_injective
        (by simpa only [mapTriangle_obj, map_comp, map_preimage] using! f.comm₁)
      comm₂ := F.map_injective
        (by simpa only [mapTriangle_obj, map_comp, map_preimage] 

中文:
实例 [满
  签名: F] [忠实 F] : 满 F.mapTriangle where
  定义体: ⟨{hom₁ := F.preimage f.hom₁
      hom₂ := F.preimage f.hom₂
      hom₃ := F.preimage f.hom₃
      comm₁ := F.map_injective
        (by simpa only [mapTriangle_obj, map_comp, map_preimage] using! f.comm₁)
      comm₂ := F.map_injective
        (by simpa only [mapTriangle_obj, map_comp, map_preimage] 

Depends on / 依赖: F.commShiftIso, F.map_injective, F.preimage, Triangle, Triangle.mk_mor, Y.obj, cancel_mono, commShiftIso, commShiftIso_hom_naturality, f.comm, f.hom, hom.app, mapTriangle_obj, map_comp, map_injective, map_preimage, preimage
-/
instance [Full F] [Faithful F] : Full F.mapTriangle where
  map_surjective {X Y} f :=
    ⟨{hom₁ := F.preimage f.hom₁
      hom₂ := F.preimage f.hom₂
      hom₃ := F.preimage f.hom₃
      comm₁ := F.map_injective
        (by simpa only [mapTriangle_obj, map_comp, map_preimage] using! f.comm₁)
      comm₂ := F.map_injective
        (by simpa only [mapTriangle_obj, map_comp, map_preimage] using! f.comm₂)
      comm₃ := F.map_injective (by
        rw [← cancel_mono ((F.commShiftIso (1 : Int)).hom.app Y.obj₁)]
        simpa only [mapTriangle_obj, map_comp, assoc, commShiftIso_hom_naturality,
          map_preimage, Triangle.mk_mor₃] using! f.comm₃) }, by cat_disch⟩

section Additive

variable [Preadditive C] [Preadditive D] [F.Additive]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `mapTriangleCommShiftIso` / `mapTriangleCommShiftIso` 的定义

English:
definition mapTriangleCommShiftIso
  signature: (n : Int)
  body: NatIso.ofComponents (fun T => Triangle.isoMk _ _
    ((F.commShiftIso n).app _) ((F.commShiftIso n).app _) ((F.commShiftIso n).app _)
    (by simp) (by simp) (by
      dsimp
      simp only [map_units_smul, map_comp, Linear.units_smul_comp, assoc,
        Linear.comp_units_smul, ← F.commShiftIso_hom

中文:
定义 mapTriangleCommShiftIso
  签名: (n : 整数)
  定义体: NatIso.ofComponents (fun T => Triangle.isoMk _ _
    ((F.commShiftIso n).app _) ((F.commShiftIso n).app _) ((F.commShiftIso n).app _)
    (by simp) (by simp) (by
      dsimp
      simp only [map_units_smul, map_comp, Linear.units_smul_comp, assoc,
        Linear.comp_units_smul, ← F.commShiftIso_hom

Depends on / 依赖: F.commShiftIso, F.commShiftIso_hom_naturality_assoc, F.map_shiftFunctorComm_hom_app, Functor, Functor.map_comp, Iso.inv_hom_id_app, Iso.inv_hom_id_app_assoc, Linear, Linear.comp_units_smul, Linear.units_smul_comp, NatIso, NatIso.ofComponents, T.obj, Triangle, Triangle.isoMk, cat_disch, commShiftIso, commShiftIso_hom_naturality_assoc, comp_id, comp_obj
-/
noncomputable def mapTriangleCommShiftIso (n : Int) :
    Triangle.shiftFunctor C n ⋙ F.mapTriangle ≅ F.mapTriangle ⋙ Triangle.shiftFunctor D n :=
  NatIso.ofComponents (fun T => Triangle.isoMk _ _
    ((F.commShiftIso n).app _) ((F.commShiftIso n).app _) ((F.commShiftIso n).app _)
    (by simp) (by simp) (by
      dsimp
      simp only [map_units_smul, map_comp, Linear.units_smul_comp, assoc,
        Linear.comp_units_smul, ← F.commShiftIso_hom_naturality_assoc]
      rw [F.map_shiftFunctorComm_hom_app T.obj₁ 1 n]
      simp only [comp_obj, assoc, Iso.inv_hom_id_app_assoc,
        ← Functor.map_comp, Iso.inv_hom_id_app, map_id, comp_id])) (by cat_disch)

attribute [simps!] mapTriangleCommShiftIso

attribute [local simp] map_zsmul comp_zsmul zsmul_comp
  commShiftIso_zero commShiftIso_add commShiftIso_comp_hom_app
  shiftFunctorAdd'_eq_shiftFunctorAdd

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
-- Split out from the following instance for faster elaboration.
set_option backward.privateInPublic true in
/--
theorem `mapTriangleCommShiftIso_add` / 定理 `mapTriangleCommShiftIso_add`

English:
theorem mapTriangleCommShiftIso_add
  proof: by
  ext <;> simp

中文:
定理 mapTriangleCommShiftIso_add
  证明: by
  ext <;> simp
-/
private theorem mapTriangleCommShiftIso_add
    [forall (n : Int), (shiftFunctor C n).Additive]
    [forall (n : Int), (shiftFunctor D n).Additive] (n m : Int) :
    F.mapTriangleCommShiftIso (n + m) =
      CommShift.isoAdd (a := n) (b := m)
        (F.mapTriangleCommShiftIso n) (F.mapTriangleCommShiftIso m) := by
  ext <;> simp

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: (n : Int), (shiftFunctor C n).Additive]
  body: F.mapTriangleCommShiftIso
  commShiftIso_add _ _ := mapTriangleCommShiftIso_add ..

中文:
实例 [对任意
  签名: (n : 整数), (shiftFunctor C n).加性]
  定义体: F.mapTriangleCommShiftIso
  commShiftIso_add _ _ := mapTriangleCommShiftIso_add ..

Depends on / 依赖: F.mapTriangleCommShiftIso, mapTriangleCommShiftIso
-/
noncomputable instance [forall (n : Int), (shiftFunctor C n).Additive]
    [forall (n : Int), (shiftFunctor D n).Additive] : (F.mapTriangle).CommShift Int where
  commShiftIso := F.mapTriangleCommShiftIso
  commShiftIso_add _ _ := mapTriangleCommShiftIso_add ..

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `F.mapTriangle` commutes with the rotation of triangles. -/
@[simps!]
/--
Definition of `mapTriangleRotateIso` / `mapTriangleRotateIso` 的定义

English:
definition mapTriangleRotateIso
  signature: :
  body: NatIso.ofComponents
    (fun T => Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
      ((F.commShiftIso (1 : Int)).symm.app _)
      (by simp) (by simp) (by simp)) (by cat_disch)

中文:
定义 mapTriangleRotateIso
  签名: :
  定义体: NatIso.ofComponents
    (fun T => Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
      ((F.commShiftIso (1 : Int)).symm.app _)
      (by simp) (by simp) (by simp)) (by cat_disch)

Depends on / 依赖: F.commShiftIso, Iso.refl, NatIso, NatIso.ofComponents, Triangle, Triangle.isoMk, cat_disch, commShiftIso, ofComponents, symm.app
-/
def mapTriangleRotateIso :
    F.mapTriangle ⋙ Pretriangulated.rotate D ≅
      Pretriangulated.rotate C ⋙ F.mapTriangle :=
  NatIso.ofComponents
    (fun T => Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
      ((F.commShiftIso (1 : Int)).symm.app _)
      (by simp) (by simp) (by simp)) (by cat_disch)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `F.mapTriangle` commutes with the inverse of the rotation of triangles. -/
@[simps!]
/--
Definition of `mapTriangleInvRotateIso` / `mapTriangleInvRotateIso` 的定义

English:
definition mapTriangleInvRotateIso
  signature: :
  body: NatIso.ofComponents
    (fun T => Triangle.isoMk _ _ ((F.commShiftIso (-1 : Int)).symm.app _) (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simp)) (by cat_disch)

中文:
定义 mapTriangleInvRotateIso
  签名: :
  定义体: NatIso.ofComponents
    (fun T => Triangle.isoMk _ _ ((F.commShiftIso (-1 : Int)).symm.app _) (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simp)) (by cat_disch)

Depends on / 依赖: F.commShiftIso, Iso.refl, NatIso, NatIso.ofComponents, Triangle, Triangle.isoMk, cat_disch, commShiftIso, ofComponents, symm.app
-/
noncomputable def mapTriangleInvRotateIso :
    F.mapTriangle ⋙ Pretriangulated.invRotate D ≅
      Pretriangulated.invRotate C ⋙ F.mapTriangle :=
  NatIso.ofComponents
    (fun T => Triangle.isoMk _ _ ((F.commShiftIso (-1 : Int)).symm.app _) (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simp)) (by cat_disch)


set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
variable (C) in
/-- The canonical isomorphism `(𝟭 C).mapTriangle ≅ 𝟭 (Triangle C)`. -/
@[simps!]
/--
Definition of `mapTriangleIdIso` / `mapTriangleIdIso` 的定义

English:
definition mapTriangleIdIso
  signature: : (𝟭 C).mapTriangle ≅ 𝟭 _
  body: NatIso.ofComponents (fun T => Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _))

中文:
定义 mapTriangleIdIso
  签名: : (𝟭 C).mapTriangle ≅ 𝟭 _
  定义体: NatIso.ofComponents (fun T => Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _))

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, Triangle, Triangle.isoMk, ofComponents
-/
def mapTriangleIdIso : (𝟭 C).mapTriangle ≅ 𝟭 _ :=
  NatIso.ofComponents (fun T => Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The canonical isomorphism `(F ⋙ G).mapTriangle ≅ F.mapTriangle ⋙ G.mapTriangle`. -/
@[simps!]
/--
Definition of `mapTriangleCompIso` / `mapTriangleCompIso` 的定义

English:
definition mapTriangleCompIso
  signature: : (F ⋙ G).mapTriangle ≅ F.mapTriangle ⋙ G.mapTriangle
  body: NatIso.ofComponents (fun T => Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _))

中文:
定义 mapTriangleCompIso
  签名: : (F ⋙ G).mapTriangle ≅ F.mapTriangle ⋙ G.mapTriangle
  定义体: NatIso.ofComponents (fun T => Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _))

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, Triangle, Triangle.isoMk, ofComponents
-/
def mapTriangleCompIso : (F ⋙ G).mapTriangle ≅ F.mapTriangle ⋙ G.mapTriangle :=
  NatIso.ofComponents (fun T => Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Two isomorphic functors `F₁` and `F₂` induce isomorphic functors
`F₁.mapTriangle` and `F₂.mapTriangle` if the isomorphism `F₁ ≅ F₂` is compatible
with the shifts. -/
@[simps!]
/--
Definition of `mapTriangleIso` / `mapTriangleIso` 的定义

English:
definition mapTriangleIso
  signature: {F₁ F₂ : C ⥤ D} (e : F₁ ≅ F₂) [F₁.CommShift Int] [F₂.CommShift Int]
  body: NatIso.ofComponents (fun T =>
    Triangle.isoMk _ _ (e.app _) (e.app _) (e.app _) (by simp) (by simp) (by
      dsimp
      simp only [assoc, NatTrans.shift_app_comm e.hom (1 : Int) T.obj₁,
        NatTrans.naturality_assoc])) (by cat_disch)

中文:
定义 mapTriangleIso
  签名: {F₁ F₂ : C ⥤ D} (e : F₁ ≅ F₂) [F₁.交换Shift 整数] [F₂.交换Shift 整数]
  定义体: NatIso.ofComponents (fun T =>
    Triangle.isoMk _ _ (e.app _) (e.app _) (e.app _) (by simp) (by simp) (by
      dsimp
      simp only [assoc, NatTrans.shift_app_comm e.hom (1 : Int) T.obj₁,
        NatTrans.naturality_assoc])) (by cat_disch)

Depends on / 依赖: NatIso, NatIso.ofComponents, NatTrans, NatTrans.naturality_assoc, NatTrans.shift_app_comm, T.obj, Triangle, Triangle.isoMk, cat_disch, e.app, e.hom, naturality_assoc, ofComponents, shift_app_comm
-/
def mapTriangleIso {F₁ F₂ : C ⥤ D} (e : F₁ ≅ F₂) [F₁.CommShift Int] [F₂.CommShift Int]
    [NatTrans.CommShift e.hom Int] : F₁.mapTriangle ≅ F₂.mapTriangle :=
  NatIso.ofComponents (fun T =>
    Triangle.isoMk _ _ (e.app _) (e.app _) (e.app _) (by simp) (by simp) (by
      dsimp
      simp only [assoc, NatTrans.shift_app_comm e.hom (1 : Int) T.obj₁,
        NatTrans.naturality_assoc])) (by cat_disch)

end Additive

variable [HasZeroObject C] [HasZeroObject D] [HasZeroObject E]
  [Preadditive C] [Preadditive D] [Preadditive E]
  [forall (n : Int), (shiftFunctor C n).Additive] [forall (n : Int), (shiftFunctor D n).Additive]
  [forall (n : Int), (shiftFunctor E n).Additive]
  [Pretriangulated C] [Pretriangulated D] [Pretriangulated E]

/--
Definition of `IsTriangulated` / `IsTriangulated` 的定义

English:
class IsTriangulated
  parameters: : Prop where
  axioms and operations (1):
    - map_distinguished((T : Triangle C)) : (T in distTriang C) -> F.mapTriangle.obj T in distTriang D

中文:
类 是三角
  参数: : 命题 where
  公理与运算 (1 个):
    - map_distinguished((T : Triangle C)) : (T in distTriang C) -> F.mapTriangle.obj T in distTriang D
-/
class IsTriangulated : Prop where
  map_distinguished (T : Triangle C) : (T in distTriang C) -> F.mapTriangle.obj T in distTriang D

/--
lemma `map_distinguished` / 引理 `map_distinguished`

English:
lemma map_distinguished
  given: [F.IsTriangulated] (T : Triangle C) (hT : T in distTriang C)
  proof: IsTriangulated.map_distinguished _ hT

中文:
引理 map_distinguished
  条件: [F.是三角] (T : Triangle C) (hT : T in distTriang C)
  证明: IsTriangulated.map_distinguished _ hT

Depends on / 依赖: IsTriangulated, IsTriangulated.map_distinguished, map_distinguished
-/
lemma map_distinguished [F.IsTriangulated] (T : Triangle C) (hT : T in distTriang C) :
    F.mapTriangle.obj T in distTriang D :=
  IsTriangulated.map_distinguished _ hT

namespace IsTriangulated

open ZeroObject

set_option backward.defeqAttrib.useBackward true in
instance (priority := 100) [F.IsTriangulated] : PreservesZeroMorphisms F where
  map_zero X Y := by
    have h₁ : (0 : X ⟶ Y) = 0 ≫ 𝟙 0 ≫ 0 := by simp
    have h₂ : 𝟙 (F.obj 0) = 0 := by
      rw [← IsZero.iff_id_eq_zero]
      apply Triangle.isZero₃_of_isIso₁ _
        (F.map_distinguished _ (contractible_distinguished (0 : C)))
      dsimp
      infer_instance
    rw [h₁]; rw [F.map_comp]; rw [F.map_comp]; rw [F.map_id]; rw [h₂]; rw [zero_comp]; rw [comp_zero]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [F.IsTriangulated]
  signature: :
  body: by
  suffices forall (X₁ X₃ : C), IsIso (prodComparison F X₁ X₃) by
    have := fun (X₁ X₃ : C) => PreservesLimitPair.of_iso_prod_comparison F X₁ X₃
    exact ⟨fun {K} => preservesLimit_of_iso_diagram F (diagramIsoPair K).symm⟩
  intro X₁ X₃
  let φ : F.mapTriangle.obj (binaryProductTriangle X₁ X₃) 

中文:
实例 [F.是三角]
  签名: :
  定义体: by
  suffices forall (X₁ X₃ : C), IsIso (prodComparison F X₁ X₃) by
    have := fun (X₁ X₃ : C) => PreservesLimitPair.of_iso_prod_comparison F X₁ X₃
    exact ⟨fun {K} => preservesLimit_of_iso_diagram F (diagramIsoPair K).symm⟩
  intro X₁ X₃
  let φ : F.mapTriangle.obj (binaryProductTriangle X₁ X₃) 

Depends on / 依赖: F.mapTriangle.obj, F.obj, PreservesLimitPair, PreservesLimitPair.of_iso_prod_comparison, binaryProductTriangle, comp_id, comp_lift, comp_zero, diagramIsoPair, limit.lift, mapTriangle, of_iso_prod_comparison, preservesLimit_of_iso_diagram, prod.comp_lift, prodComparison, prodComparison_fst
-/
noncomputable instance [F.IsTriangulated] :
    PreservesLimitsOfShape (Discrete WalkingPair) F := by
  suffices forall (X₁ X₃ : C), IsIso (prodComparison F X₁ X₃) by
    have := fun (X₁ X₃ : C) => PreservesLimitPair.of_iso_prod_comparison F X₁ X₃
    exact ⟨fun {K} => preservesLimit_of_iso_diagram F (diagramIsoPair K).symm⟩
  intro X₁ X₃
  let φ : F.mapTriangle.obj (binaryProductTriangle X₁ X₃) ⟶
      binaryProductTriangle (F.obj X₁) (F.obj X₃) :=
    { hom₁ := 𝟙 _
      hom₂ := prodComparison F X₁ X₃
      hom₃ := 𝟙 _
      comm₁ := by
        dsimp
        ext
        · simp only [assoc, prodComparison_fst, prod.comp_lift, comp_id, comp_zero,
            limit.lift_π, BinaryFan.mk_pt, BinaryFan.π_app_left, BinaryFan.mk_fst,
            ← F.map_comp, F.map_id]
        · simp only [assoc, prodComparison_snd, prod.comp_lift, comp_id, comp_zero,
            limit.lift_π, BinaryFan.mk_pt, BinaryFan.π_app_right, BinaryFan.mk_snd,
            ← F.map_comp, F.map_zero]
      comm₂ := by simp
      comm₃ := by simp }
  exact isIso₂_of_isIso₁₃ φ (F.map_distinguished _ (binaryProductTriangle_distinguished X₁ X₃))
    (binaryProductTriangle_distinguished _ _)
    (by dsimp [φ]; infer_instance) (by dsimp [φ]; infer_instance)

instance (priority := 100) [F.IsTriangulated] : F.Additive :=
  F.additive_of_preserves_binary_products

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (𝟭 C).IsTriangulated
  body: isomorphic_distinguished _ hT _ ((mapTriangleIdIso C).app T)

中文:
实例 :
  签名: (𝟭 C).是三角
  定义体: isomorphic_distinguished _ hT _ ((mapTriangleIdIso C).app T)

Depends on / 依赖: isomorphic_distinguished, mapTriangleIdIso
-/
instance : (𝟭 C).IsTriangulated where
  map_distinguished T hT :=
    isomorphic_distinguished _ hT _ ((mapTriangleIdIso C).app T)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [F.IsTriangulated]
  signature: [G.IsTriangulated]
  body: isomorphic_distinguished _ (G.map_distinguished _ (F.map_distinguished T hT)) _
      ((mapTriangleCompIso F G).app T)

中文:
实例 [F.是三角]
  签名: [G.是三角]
  定义体: isomorphic_distinguished _ (G.map_distinguished _ (F.map_distinguished T hT)) _
      ((mapTriangleCompIso F G).app T)

Depends on / 依赖: F.map_distinguished, G.map_distinguished, isomorphic_distinguished, mapTriangleCompIso, map_distinguished
-/
instance [F.IsTriangulated] [G.IsTriangulated] : (F ⋙ G).IsTriangulated where
  map_distinguished T hT :=
    isomorphic_distinguished _ (G.map_distinguished _ (F.map_distinguished T hT)) _
      ((mapTriangleCompIso F G).app T)

end IsTriangulated

set_option backward.defeqAttrib.useBackward true in
/--
lemma `map_distinguished_iff` / 引理 `map_distinguished_iff`

English:
lemma map_distinguished_iff
  given: [F.IsTriangulated] [Full F] [Faithful F] (T : Triangle C)
  proof: by
  refine ⟨fun hT => ?_, F.map_distinguished T⟩
  obtain ⟨Z, g, h, mem⟩ := distinguished_cocone_triangle T.mor₁
  refine isomorphic_distinguished _ mem _ (F.mapTriangle.preimageIso ?_)
  exact isoTriangleOfIso₁₂ _ _ hT (F.map_distinguished _ mem)
    (Iso.refl _) (Iso.refl _) (by simp)

中文:
引理 map_distinguished_iff
  条件: [F.是三角] [满 F] [忠实 F] (T : Triangle C)
  证明: by
  refine ⟨fun hT => ?_, F.map_distinguished T⟩
  obtain ⟨Z, g, h, mem⟩ := distinguished_cocone_triangle T.mor₁
  refine isomorphic_distinguished _ mem _ (F.mapTriangle.preimageIso ?_)
  exact isoTriangleOfIso₁₂ _ _ hT (F.map_distinguished _ mem)
    (Iso.refl _) (Iso.refl _) (by simp)

Depends on / 依赖: F.mapTriangle.preimageIso, F.map_distinguished, Iso.refl, T.mor, distinguished_cocone_triangle, isomorphic_distinguished, mapTriangle, map_distinguished, preimageIso
-/
lemma map_distinguished_iff [F.IsTriangulated] [Full F] [Faithful F] (T : Triangle C) :
    (F.mapTriangle.obj T in distTriang D) ↔ T in distTriang C := by
  refine ⟨fun hT => ?_, F.map_distinguished T⟩
  obtain ⟨Z, g, h, mem⟩ := distinguished_cocone_triangle T.mor₁
  refine isomorphic_distinguished _ mem _ (F.mapTriangle.preimageIso ?_)
  exact isoTriangleOfIso₁₂ _ _ hT (F.map_distinguished _ mem)
    (Iso.refl _) (Iso.refl _) (by simp)

/--
lemma `isTriangulated_of_iso` / 引理 `isTriangulated_of_iso`

English:
lemma isTriangulated_of_iso
  statement: {F₁ F₂ : C ⥤ D} (e : F₁ ≅ F₂) [F₁.CommShift Int] [F₂.CommShift Int]
  proof: isomorphic_distinguished _ (F₁.map_distinguished T hT) _ ((mapTriangleIso e).app T).symm

中文:
引理 isTriangulated_of_iso
  结论: {F₁ F₂ : C ⥤ D} (e : F₁ ≅ F₂) [F₁.交换Shift 整数] [F₂.交换Shift 整数]
  证明: isomorphic_distinguished _ (F₁.map_distinguished T hT) _ ((mapTriangleIso e).app T).symm

Depends on / 依赖: isomorphic_distinguished, mapTriangleIso, map_distinguished
-/
lemma isTriangulated_of_iso {F₁ F₂ : C ⥤ D} (e : F₁ ≅ F₂) [F₁.CommShift Int] [F₂.CommShift Int]
    [NatTrans.CommShift e.hom Int] [F₁.IsTriangulated] : F₂.IsTriangulated where
  map_distinguished T hT :=
    isomorphic_distinguished _ (F₁.map_distinguished T hT) _ ((mapTriangleIso e).app T).symm

/--
lemma `isTriangulated_iff_of_iso` / 引理 `isTriangulated_iff_of_iso`

English:
lemma isTriangulated_iff_of_iso
  statement: {F₁ F₂ : C ⥤ D} (e : F₁ ≅ F₂) [F₁.CommShift Int] [F₂.CommShift Int]
  proof: by
  constructor
  · intro
    exact isTriangulated_of_iso e
  · intro
    have : NatTrans.CommShift e.symm.hom Int := inferInstanceAs (NatTrans.CommShift e.inv Int)
    exact isTriangulated_of_iso e.symm

中文:
引理 isTriangulated_iff_of_iso
  结论: {F₁ F₂ : C ⥤ D} (e : F₁ ≅ F₂) [F₁.交换Shift 整数] [F₂.交换Shift 整数]
  证明: by
  constructor
  · intro
    exact isTriangulated_of_iso e
  · intro
    have : NatTrans.CommShift e.symm.hom Int := inferInstanceAs (NatTrans.CommShift e.inv Int)
    exact isTriangulated_of_iso e.symm

Depends on / 依赖: CommShift, NatTrans, NatTrans.CommShift, e.inv, e.symm, e.symm.hom, isTriangulated_of_iso
-/
lemma isTriangulated_iff_of_iso {F₁ F₂ : C ⥤ D} (e : F₁ ≅ F₂) [F₁.CommShift Int] [F₂.CommShift Int]
    [NatTrans.CommShift e.hom Int] : F₁.IsTriangulated ↔ F₂.IsTriangulated := by
  constructor
  · intro
    exact isTriangulated_of_iso e
  · intro
    have : NatTrans.CommShift e.symm.hom Int := inferInstanceAs (NatTrans.CommShift e.inv Int)
    exact isTriangulated_of_iso e.symm

/--
lemma `isTriangulated_iff_comp_right` / 引理 `isTriangulated_iff_comp_right`

English:
lemma isTriangulated_iff_comp_right
  statement: {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E} (e : F ⋙ G ≅ H)
  proof: by
  rw [← isTriangulated_iff_of_iso e]
  refine ⟨fun _ => inferInstance, fun _ => ⟨fun T hT => ?_⟩⟩
  rw [← G.map_distinguished_iff]
  exact isomorphic_distinguished _ ((F ⋙ G).map_distinguished T hT) _
    ((mapTriangleCompIso F G).symm.app T)

中文:
引理 isTriangulated_iff_comp_right
  结论: {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E} (e : F ⋙ G ≅ H)
  证明: by
  rw [← isTriangulated_iff_of_iso e]
  refine ⟨fun _ => inferInstance, fun _ => ⟨fun T hT => ?_⟩⟩
  rw [← G.map_distinguished_iff]
  exact isomorphic_distinguished _ ((F ⋙ G).map_distinguished T hT) _
    ((mapTriangleCompIso F G).symm.app T)

Depends on / 依赖: G.map_distinguished_iff, isTriangulated_iff_of_iso, isomorphic_distinguished, mapTriangleCompIso, map_distinguished, map_distinguished_iff, symm.app
-/
lemma isTriangulated_iff_comp_right {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E} (e : F ⋙ G ≅ H)
    [F.CommShift Int] [G.CommShift Int] [H.CommShift Int] [NatTrans.CommShift e.hom Int]
    [G.IsTriangulated] [G.Full] [G.Faithful] :
    F.IsTriangulated ↔ H.IsTriangulated := by
  rw [← isTriangulated_iff_of_iso e]
  refine ⟨fun _ => inferInstance, fun _ => ⟨fun T hT => ?_⟩⟩
  rw [← G.map_distinguished_iff]
  exact isomorphic_distinguished _ ((F ⋙ G).map_distinguished T hT) _
    ((mapTriangleCompIso F G).symm.app T)

/--
lemma `mem_mapTriangle_essImage_of_distinguished` / 引理 `mem_mapTriangle_essImage_of_distinguished`

English:
lemma mem_mapTriangle_essImage_of_distinguished
  proof: by
  obtain ⟨X, Y, f, e₁, e₂, w⟩ : exists (X Y : C) (f : X ⟶ Y) (e₁ : F.obj X ≅ T.obj₁)
    (e₂ : F.obj Y ≅ T.obj₂), F.map f ≫ e₂.hom = e₁.hom ≫ T.mor₁ := by
      let e := F.mapArrow.objObjPreimageIso (Arrow.mk T.mor₁)
      exact ⟨_, _, _, Arrow.leftFunc.mapIso e, Arrow.rightFunc.mapIso e, e.hom.w

中文:
引理 mem_mapTriangle_essImage_of_distinguished
  证明: by
  obtain ⟨X, Y, f, e₁, e₂, w⟩ : exists (X Y : C) (f : X ⟶ Y) (e₁ : F.obj X ≅ T.obj₁)
    (e₂ : F.obj Y ≅ T.obj₂), F.map f ≫ e₂.hom = e₁.hom ≫ T.mor₁ := by
      let e := F.mapArrow.objObjPreimageIso (Arrow.mk T.mor₁)
      exact ⟨_, _, _, Arrow.leftFunc.mapIso e, Arrow.rightFunc.mapIso e, e.hom.w

Depends on / 依赖: Arrow.leftFunc.mapIso, Arrow.mk, Arrow.rightFunc.mapIso, F.map, F.mapArrow.objObjPreimageIso, F.map_distinguished, F.obj, T.mor, T.obj, distinguished_cocone_triangle, e.hom.w.symm, leftFunc, mapArrow, mapIso, map_distinguished, objObjPreimageIso, rightFunc
-/
lemma mem_mapTriangle_essImage_of_distinguished
    [F.IsTriangulated] [F.mapArrow.EssSurj] (T : Triangle D) (hT : T in distTriang D) :
    exists (T' : Triangle C) (_ : T' in distTriang C), Nonempty (F.mapTriangle.obj T' ≅ T) := by
  obtain ⟨X, Y, f, e₁, e₂, w⟩ : exists (X Y : C) (f : X ⟶ Y) (e₁ : F.obj X ≅ T.obj₁)
    (e₂ : F.obj Y ≅ T.obj₂), F.map f ≫ e₂.hom = e₁.hom ≫ T.mor₁ := by
      let e := F.mapArrow.objObjPreimageIso (Arrow.mk T.mor₁)
      exact ⟨_, _, _, Arrow.leftFunc.mapIso e, Arrow.rightFunc.mapIso e, e.hom.w.symm⟩
  obtain ⟨W, g, h, H⟩ := distinguished_cocone_triangle f
  exact ⟨_, H, ⟨isoTriangleOfIso₁₂ _ _ (F.map_distinguished _ H) hT e₁ e₂ w⟩⟩

/--
lemma `isTriangulated_of_precomp` / 引理 `isTriangulated_of_precomp`

English:
lemma isTriangulated_of_precomp
  proof: by
    obtain ⟨T', hT', ⟨e⟩⟩ := F.mem_mapTriangle_essImage_of_distinguished T hT
    exact isomorphic_distinguished _ ((F ⋙ G).map_distinguished T' hT') _
      (G.mapTriangle.mapIso e.symm ≪≫ (mapTriangleCompIso F G).symm.app _)

中文:
引理 isTriangulated_of_precomp
  证明: by
    obtain ⟨T', hT', ⟨e⟩⟩ := F.mem_mapTriangle_essImage_of_distinguished T hT
    exact isomorphic_distinguished _ ((F ⋙ G).map_distinguished T' hT') _
      (G.mapTriangle.mapIso e.symm ≪≫ (mapTriangleCompIso F G).symm.app _)

Depends on / 依赖: F.mem_mapTriangle_essImage_of_distinguished, G.mapTriangle.mapIso, e.symm, isomorphic_distinguished, mapIso, mapTriangle, mapTriangleCompIso, map_distinguished, mem_mapTriangle_essImage_of_distinguished, symm.app
-/
lemma isTriangulated_of_precomp
    [(F ⋙ G).IsTriangulated] [F.IsTriangulated] [F.mapArrow.EssSurj] :
    G.IsTriangulated where
  map_distinguished T hT := by
    obtain ⟨T', hT', ⟨e⟩⟩ := F.mem_mapTriangle_essImage_of_distinguished T hT
    exact isomorphic_distinguished _ ((F ⋙ G).map_distinguished T' hT') _
      (G.mapTriangle.mapIso e.symm ≪≫ (mapTriangleCompIso F G).symm.app _)

variable {F G} in
/--
lemma `isTriangulated_of_precomp_iso` / 引理 `isTriangulated_of_precomp_iso`

English:
lemma isTriangulated_of_precomp_iso
  statement: {H : C ⥤ E} (e : F ⋙ G ≅ H) [H.CommShift Int]
  proof: by
  have := (isTriangulated_iff_of_iso e).2 inferInstance
  exact isTriangulated_of_precomp F G

中文:
引理 isTriangulated_of_precomp_iso
  结论: {H : C ⥤ E} (e : F ⋙ G ≅ H) [H.交换Shift 整数]
  证明: by
  have := (isTriangulated_iff_of_iso e).2 inferInstance
  exact isTriangulated_of_precomp F G

Depends on / 依赖: isTriangulated_iff_of_iso, isTriangulated_of_precomp
-/
lemma isTriangulated_of_precomp_iso {H : C ⥤ E} (e : F ⋙ G ≅ H) [H.CommShift Int]
    [H.IsTriangulated] [F.IsTriangulated] [F.mapArrow.EssSurj] [NatTrans.CommShift e.hom Int] :
    G.IsTriangulated := by
  have := (isTriangulated_iff_of_iso e).2 inferInstance
  exact isTriangulated_of_precomp F G

end Functor

variable {C D : Type*} [Category* C] [Category* D] [HasShift C Int] [HasShift D Int]
  [HasZeroObject C] [HasZeroObject D] [Preadditive C] [Preadditive D]
  [forall (n : Int), (shiftFunctor C n).Additive] [forall (n : Int), (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]

namespace Triangulated

namespace Octahedron

variable {X₁ X₂ X₃ Z₁₂ Z₂₃ Z₁₃ : C}
  {u₁₂ : X₁ ⟶ X₂} {u₂₃ : X₂ ⟶ X₃} {u₁₃ : X₁ ⟶ X₃} {comm : u₁₂ ≫ u₂₃ = u₁₃}
  {v₁₂ : X₂ ⟶ Z₁₂} {w₁₂ : Z₁₂ ⟶ X₁⟦(1 : Int)⟧} {h₁₂ : Triangle.mk u₁₂ v₁₂ w₁₂ in distTriang C}
  {v₂₃ : X₃ ⟶ Z₂₃} {w₂₃ : Z₂₃ ⟶ X₂⟦(1 : Int)⟧} {h₂₃ : Triangle.mk u₂₃ v₂₃ w₂₃ in distTriang C}
  {v₁₃ : X₃ ⟶ Z₁₃} {w₁₃ : Z₁₃ ⟶ X₁⟦(1 : Int)⟧} {h₁₃ : Triangle.mk u₁₃ v₁₃ w₁₃ in distTriang C}
  (h : Octahedron comm h₁₂ h₂₃ h₁₃)
  (F : C ⥤ D) [F.CommShift Int] [F.IsTriangulated]

set_option backward.defeqAttrib.useBackward true in
/-- The image of an octahedron by a triangulated functor. -/
@[simps]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: : Octahedron (by dsimp; rw [← F.map_comp, comm])
  body: F.map h.m₁
  m₃ := F.map h.m₃
  comm₁ := by simpa using F.congr_map h.comm₁
  comm₂ := by simpa using F.congr_map h.comm₂ =≫ (F.commShiftIso 1).hom.app X₁
  comm₃ := by simpa using F.congr_map h.comm₃
  comm₄ := by simpa using F.congr_map h.comm₄ =≫ (F.commShiftIso 1).hom.app X₂
  mem := isomorphic_

中文:
定义 map
  签名: : 八面体 (by dsimp; rw [← F.map_comp, comm])
  定义体: F.map h.m₁
  m₃ := F.map h.m₃
  comm₁ := by simpa using F.congr_map h.comm₁
  comm₂ := by simpa using F.congr_map h.comm₂ =≫ (F.commShiftIso 1).hom.app X₁
  comm₃ := by simpa using F.congr_map h.comm₃
  comm₄ := by simpa using F.congr_map h.comm₄ =≫ (F.commShiftIso 1).hom.app X₂
  mem := isomorphic_

Depends on / 依赖: F.map
-/
def map : Octahedron (by dsimp; rw [← F.map_comp, comm])
    (F.map_distinguished _ h₁₂) (F.map_distinguished _ h₂₃) (F.map_distinguished _ h₁₃) where
  m₁ := F.map h.m₁
  m₃ := F.map h.m₃
  comm₁ := by simpa using F.congr_map h.comm₁
  comm₂ := by simpa using F.congr_map h.comm₂ =≫ (F.commShiftIso 1).hom.app X₁
  comm₃ := by simpa using F.congr_map h.comm₃
  comm₄ := by simpa using F.congr_map h.comm₄ =≫ (F.commShiftIso 1).hom.app X₂
  mem := isomorphic_distinguished _ (F.map_distinguished _ h.mem) _
    (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _))

end Octahedron

end Triangulated

open Triangulated

/--
lemma `isTriangulated_of_essSurj_mapComposableArrows_two` / 引理 `isTriangulated_of_essSurj_mapComposableArrows_two`

English:
lemma isTriangulated_of_essSurj_mapComposableArrows_two
  proof: by
  apply IsTriangulated.mk
  intro Y₁ Y₂ Y₃ Z₁₂ Z₂₃ Z₁₃ u₁₂ u₂₃ u₁₃ comm v₁₂ w₁₂ h₁₂ v₂₃ w₂₃ h₂₃ v₁₃ w₁₃ h₁₃
  obtain ⟨α, ⟨e⟩⟩ : exists (α : ComposableArrows C 2),
      Nonempty ((F.mapComposableArrows 2).obj α ≅ ComposableArrows.mk₂ u₁₂ u₂₃) :=
    ⟨_, ⟨Functor.objObjPreimageIso _ _⟩⟩
  obtain ⟨

中文:
引理 isTriangulated_of_essSurj_mapComposableArrows_two
  证明: by
  apply IsTriangulated.mk
  intro Y₁ Y₂ Y₃ Z₁₂ Z₂₃ Z₁₃ u₁₂ u₂₃ u₁₃ comm v₁₂ w₁₂ h₁₂ v₂₃ w₂₃ h₂₃ v₁₃ w₁₃ h₁₃
  obtain ⟨α, ⟨e⟩⟩ : exists (α : ComposableArrows C 2),
      Nonempty ((F.mapComposableArrows 2).obj α ≅ ComposableArrows.mk₂ u₁₂ u₂₃) :=
    ⟨_, ⟨Functor.objObjPreimageIso _ _⟩⟩
  obtain ⟨

Depends on / 依赖: ComposableArrows, ComposableArrows.mk, F.mapComposableArrows, Functor, Functor.objObjPreimageIso, IsTriangulated, IsTriangulated.mk, Nonempty, distinguished_co, distinguished_cocone_triangle, mapComposableArrows, objObjPreimageIso
-/
lemma isTriangulated_of_essSurj_mapComposableArrows_two
    (F : C ⥤ D) [F.CommShift Int] [F.IsTriangulated]
    [(F.mapComposableArrows 2).EssSurj] [IsTriangulated C] :
    IsTriangulated D := by
  apply IsTriangulated.mk
  intro Y₁ Y₂ Y₃ Z₁₂ Z₂₃ Z₁₃ u₁₂ u₂₃ u₁₃ comm v₁₂ w₁₂ h₁₂ v₂₃ w₂₃ h₂₃ v₁₃ w₁₃ h₁₃
  obtain ⟨α, ⟨e⟩⟩ : exists (α : ComposableArrows C 2),
      Nonempty ((F.mapComposableArrows 2).obj α ≅ ComposableArrows.mk₂ u₁₂ u₂₃) :=
    ⟨_, ⟨Functor.objObjPreimageIso _ _⟩⟩
  obtain ⟨X₁, X₂, X₃, f, g, rfl⟩ := ComposableArrows.mk₂_surjective α
  obtain ⟨_, _, _, h₁₂'⟩ := distinguished_cocone_triangle f
  obtain ⟨_, _, _, h₂₃'⟩ := distinguished_cocone_triangle g
  obtain ⟨_, _, _, h₁₃'⟩ := distinguished_cocone_triangle (f ≫ g)
  exact ⟨Octahedron.ofIso (e₁ := (e.app 0).symm) (e₂ := (e.app 1).symm) (e₃ := (e.app 2).symm)
    (comm₁₂ := ComposableArrows.naturality' e.inv 0 1)
    (comm₂₃ := ComposableArrows.naturality' e.inv 1 2)
    (H := (someOctahedron rfl h₁₂' h₂₃' h₁₃').map F) ..⟩

set_option backward.defeqAttrib.useBackward true in
/--
lemma `IsTriangulated.of_fully_faithful_triangulated_functor` / 引理 `IsTriangulated.of_fully_faithful_triangulated_functor`

English:
lemma IsTriangulated.of_fully_faithful_triangulated_functor
  proof: by
    have comm' : F.map u₁₂ ≫ F.map u₂₃ = F.map u₁₃ := by rw [← comm, F.map_comp]
    let H := Triangulated.someOctahedron comm' (F.map_distinguished _ h₁₂)
      (F.map_distinguished _ h₂₃) (F.map_distinguished _ h₁₃)
    exact
      ⟨{m₁ := F.preimage H.m₁
        m₃ := F.preimage H.m₃
        c

中文:
引理 是三角.of_fully_faithful_triangulated_functor
  证明: by
    have comm' : F.map u₁₂ ≫ F.map u₂₃ = F.map u₁₃ := by rw [← comm, F.map_comp]
    let H := Triangulated.someOctahedron comm' (F.map_distinguished _ h₁₂)
      (F.map_distinguished _ h₂₃) (F.map_distinguished _ h₁₃)
    exact
      ⟨{m₁ := F.preimage H.m₁
        m₃ := F.preimage H.m₃
        c

Depends on / 依赖: F.commShiftIso, F.map, F.map_comp, F.map_distinguished, F.map_injective, F.preimage, H.comm, Triangulated, Triangulated.someOctahedron, cancel_mono, commShiftIso, hom.app, map_comp, map_distinguished, map_injective, preimage, someOctahedron
-/
lemma IsTriangulated.of_fully_faithful_triangulated_functor
    (F : C ⥤ D) [F.CommShift Int]
    [F.IsTriangulated] [F.Full] [F.Faithful] [IsTriangulated D] :
    IsTriangulated C where
  octahedron_axiom {X₁ X₂ X₃ Z₁₂ Z₂₃ Z₁₃ u₁₂ u₂₃ u₁₃} comm
    {v₁₂ w₁₂} h₁₂ {v₂₃ w₂₃} h₂₃ {v₁₃ w₁₃} h₁₃ := by
    have comm' : F.map u₁₂ ≫ F.map u₂₃ = F.map u₁₃ := by rw [← comm, F.map_comp]
    let H := Triangulated.someOctahedron comm' (F.map_distinguished _ h₁₂)
      (F.map_distinguished _ h₂₃) (F.map_distinguished _ h₁₃)
    exact
      ⟨{m₁ := F.preimage H.m₁
        m₃ := F.preimage H.m₃
        comm₁ := F.map_injective (by simpa using H.comm₁)
        comm₂ := F.map_injective (by
          simpa [← cancel_mono ((F.commShiftIso (1 : Int)).hom.app X₁)] using H.comm₂)
        comm₃ := F.map_injective (by simpa using H.comm₃)
        comm₄ := F.map_injective (by
          simpa [← cancel_mono ((F.commShiftIso (1 : Int)).hom.app X₂)] using H.comm₄)
        mem := by simpa [← F.map_distinguished_iff] using H.mem }⟩

end CategoryTheory
