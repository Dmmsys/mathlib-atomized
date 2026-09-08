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
  [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ]
  (F : C ⥤ D) [F.CommShift ℤ] (G : D ⥤ E) [G.CommShift ℤ]

set_option backward.defeqAttrib.useBackward true in
/-- The functor `Triangle C ⥤ Triangle D` that is induced by a functor `F : C ⥤ D`
which commutes with shift by `ℤ`. -/
@[simps]
/-
**CategoryTheory.Functor.mapTriangle** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.F
unctor`。
形式化陈述：mapTriangle : Triangle C ⥤ Triangle D where obj T
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `Triangle C ⥤ Triangle D` that is induced by a functor `F : C ⥤ D`
which commutes with shift by `ℤ`.
-/
def mapTriangle : Triangle C ⥤ Triangle D where
  obj T := Triangle.mk (F.map T.mor₁) (F.map T.mor₂)
    (F.map T.mor₃ ≫ (F.commShiftIso (1 : ℤ)).hom.app T.obj₁)
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
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Faithful F] : Faithful F.mapTriangle where
  map_injective {X Y} f g h := by
    ext <;> apply F.map_injective
    · exact congr_arg TriangleMorphism.hom₁ h
    · exact congr_arg TriangleMorphism.hom₂ h
    · exact congr_arg TriangleMorphism.hom₃ h

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
        rw [← cancel_mono ((F.commShiftIso (1 : ℤ)).hom.app Y.obj₁)]
        simpa only [mapTriangle_obj, map_comp, assoc, commShiftIso_hom_naturality,
          map_preimage, Triangle.mk_mor₃] using! f.comm₃) }, by cat_disch⟩

section Additive

variable [Preadditive C] [Preadditive D] [F.Additive]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The functor `F.mapTriangle` commutes with the shift. -/
/-
**CategoryTheory.Functor.mapTriangleCommShiftIso** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Functor`。
形式化陈述：mapTriangleCommShiftIso (n : Int) : Triangle.shiftFunctor C n ⋙ F.mapTrian
gle ≅ F.mapTriangle ⋙ Triangle.shiftFunctor D n
参数：n : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `F.mapTriangle` commutes with the shift.
-/
noncomputable def mapTriangleCommShiftIso (n : ℤ) :
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
/-
**CategoryTheory.Functor.mapTriangleCommShiftIso_add** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem mapTriangleCommShiftIso_add
    [∀ (n : ℤ), (shiftFunctor C n).Additive]
    [∀ (n : ℤ), (shiftFunctor D n).Additive] (n m : ℤ) :
    F.mapTriangleCommShiftIso (n + m) =
      CommShift.isoAdd (a := n) (b := m)
        (F.mapTriangleCommShiftIso n) (F.mapTriangleCommShiftIso m) := by
  ext <;> simp

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [∀ (n : ℤ), (shiftFunctor C n).Additive]
    [∀ (n : ℤ), (shiftFunctor D n).Additive] : (F.mapTriangle).CommShift ℤ where
  commShiftIso := F.mapTriangleCommShiftIso
  commShiftIso_add _ _ := mapTriangleCommShiftIso_add ..

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `F.mapTriangle` commutes with the rotation of triangles. -/
@[simps!]
/-
**CategoryTheory.Functor.mapTriangleRotateIso** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Functor`。
形式化陈述：mapTriangleRotateIso : F.mapTriangle ⋙ Pretriangulated.rotate D ≅ Pretrian
gulated.rotate C ⋙ F.mapTriangle
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`F.mapTriangle` commutes with the rotation of triangles.
-/
def mapTriangleRotateIso :
    F.mapTriangle ⋙ Pretriangulated.rotate D ≅
      Pretriangulated.rotate C ⋙ F.mapTriangle :=
  NatIso.ofComponents
    (fun T => Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
      ((F.commShiftIso (1 : ℤ)).symm.app _)
      (by simp) (by simp) (by simp)) (by cat_disch)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `F.mapTriangle` commutes with the inverse of the rotation of triangles. -/
@[simps!]
/-
**CategoryTheory.Functor.mapTriangleInvRotateIso** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Functor`。
形式化陈述：mapTriangleInvRotateIso : F.mapTriangle ⋙ Pretriangulated.invRotate D ≅ Pr
etriangulated.invRotate C ⋙ F.mapTriangle
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`F.mapTriangle` commutes with the inverse of the rotation of triangles.
-/
noncomputable def mapTriangleInvRotateIso :
    F.mapTriangle ⋙ Pretriangulated.invRotate D ≅
      Pretriangulated.invRotate C ⋙ F.mapTriangle :=
  NatIso.ofComponents
    (fun T => Triangle.isoMk _ _ ((F.commShiftIso (-1 : ℤ)).symm.app _) (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simp)) (by cat_disch)


set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
variable (C) in
/-- The canonical isomorphism `(𝟭 C).mapTriangle ≅ 𝟭 (Triangle C)`. -/
@[simps!]
/-
**CategoryTheory.Functor.mapTriangleIdIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Functor`。
形式化陈述：mapTriangleIdIso : (𝟭 C).mapTriangle ≅ 𝟭 _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism `(𝟭 C).mapTriangle ≅ 𝟭 (Triangle C)`.
-/
def mapTriangleIdIso : (𝟭 C).mapTriangle ≅ 𝟭 _ :=
  NatIso.ofComponents (fun T ↦ Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The canonical isomorphism `(F ⋙ G).mapTriangle ≅ F.mapTriangle ⋙ G.mapTriangle`. -/
@[simps!]
/-
**CategoryTheory.Functor.mapTriangleCompIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Functor`。
形式化陈述：mapTriangleCompIso : (F ⋙ G).mapTriangle ≅ F.mapTriangle ⋙ G.mapTriangle
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism `(F ⋙ G).mapTriangle ≅ F.mapTriangle ⋙ G.mapTriangle`.
-/
def mapTriangleCompIso : (F ⋙ G).mapTriangle ≅ F.mapTriangle ⋙ G.mapTriangle :=
  NatIso.ofComponents (fun T => Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Two isomorphic functors `F₁` and `F₂` induce isomorphic functors
`F₁.mapTriangle` and `F₂.mapTriangle` if the isomorphism `F₁ ≅ F₂` is compatible
with the shifts. -/
@[simps!]
/-
**CategoryTheory.Functor.mapTriangleIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Functor`。
形式化陈述：mapTriangleIso {F₁ F₂ : C ⥤ D} (e : F₁ ≅ F₂) [F₁.CommShift Int] [F₂.CommSh
ift Int] [NatTrans.CommShift e.hom Int] : F₁.mapTriangle ≅ F₂.mapTriangle
参数：e : F₁ ≅ F₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two isomorphic functors `F₁` and `F₂` induce isomorphic functors
`F₁.mapTriangle` and `F₂.mapTriangle` if the isomorphism `F₁ ≅ F₂` is compatible
with the shifts.
-/
def mapTriangleIso {F₁ F₂ : C ⥤ D} (e : F₁ ≅ F₂) [F₁.CommShift ℤ] [F₂.CommShift ℤ]
    [NatTrans.CommShift e.hom ℤ] : F₁.mapTriangle ≅ F₂.mapTriangle :=
  NatIso.ofComponents (fun T =>
    Triangle.isoMk _ _ (e.app _) (e.app _) (e.app _) (by simp) (by simp) (by
      dsimp
      simp only [assoc, NatTrans.shift_app_comm e.hom (1 : ℤ) T.obj₁,
        NatTrans.naturality_assoc])) (by cat_disch)

end Additive

variable [HasZeroObject C] [HasZeroObject D] [HasZeroObject E]
  [Preadditive C] [Preadditive D] [Preadditive E]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [∀ (n : ℤ), (shiftFunctor E n).Additive]
  [Pretriangulated C] [Pretriangulated D] [Pretriangulated E]

/-- A functor which commutes with the shift by `ℤ` is triangulated if
it sends distinguished triangles to distinguished triangles. -/
/-
**CategoryTheory.Functor.IsTriangulated** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryThe
ory.Functor`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         [i
nst_2 : CategoryTheory.HasShift C ℤ] →           [inst_3 : CategoryTheory.HasShi
ft D ℤ] →             (F : CategoryTheory.Functor C D) →               [F.CommSh
ift ℤ] →                 [inst_5 : CategoryTheory.Limits.HasZeroObject C] →     
              [inst_6 : CategoryTheory.Limits.HasZeroObject D] →                
     [inst_7 : CategoryTheory.Preadditive C] →                       [inst_8 : C
ategoryTheory.Preadditive D] →                         [inst_9 : ∀ (n : ℤ), (Cat
egoryTheory.shiftFunctor C n).Additive] →                           [inst_10 : ∀
 (n : ℤ), (CategoryTheory.shiftFunctor D n).Additive] →                         
    [CategoryTheory.Pretriangulated C] → [CategoryTheory.Pretriangulated D] → Pr
op
参数：F : CategoryTheory.Functor C D；n : ℤ；CategoryTheory.shiftFunctor C n；n : ℤ；Ca
tegoryTheory.shiftFunctor D n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor which commutes with the shift by `ℤ` is triangulated if
it sends distinguished triangles to distinguished triangles.
-/
class IsTriangulated : Prop where
  map_distinguished (T : Triangle C) : (T ∈ distTriang C) → F.mapTriangle.obj T ∈ distTriang D
/-
**CategoryTheory.Functor.map_distinguished** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.Functor`。
形式化陈述：map_distinguished [F.IsTriangulated] (T : Triangle C) (hT : T in distTrian
g C) : F.mapTriangle.obj T in distTriang D
参数：T : Triangle C；hT : T in distTriang C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsTriangulated.map_distinguished`：∀ {C : Type u_1
} {D : Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {inst_1 : Categ
oryTheory.Category.{v_2, u_2} D} {inst_2 : Ca…
-/
lemma map_distinguished [F.IsTriangulated] (T : Triangle C) (hT : T ∈ distTriang C) :
    F.mapTriangle.obj T ∈ distTriang D :=
  IsTriangulated.map_distinguished _ hT

namespace IsTriangulated

open ZeroObject

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Functor.IsTriangulated.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Functor.IsTriangulated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) [F.IsTriangulated] : PreservesZeroMorphisms F where
  map_zero X Y := by
    have h₁ : (0 : X ⟶ Y) = 0 ≫ 𝟙 0 ≫ 0 := by simp
    have h₂ : 𝟙 (F.obj 0) = 0 := by
      rw [← IsZero.iff_id_eq_zero]
      apply Triangle.isZero₃_of_isIso₁ _
        (F.map_distinguished _ (contractible_distinguished (0 : C)))
      dsimp
      infer_instance
    rw [h₁, F.map_comp, F.map_comp, F.map_id, h₂, zero_comp, comp_zero]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Functor.IsTriangulated.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Functor.IsTriangulated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [F.IsTriangulated] :
    PreservesLimitsOfShape (Discrete WalkingPair) F := by
  suffices ∀ (X₁ X₃ : C), IsIso (prodComparison F X₁ X₃) by
    have := fun (X₁ X₃ : C) ↦ PreservesLimitPair.of_iso_prod_comparison F X₁ X₃
    exact ⟨fun {K} ↦ preservesLimit_of_iso_diagram F (diagramIsoPair K).symm⟩
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
/-
**CategoryTheory.Functor.IsTriangulated.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Functor.IsTriangulated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) [F.IsTriangulated] : F.Additive :=
  F.additive_of_preserves_binary_products
/-
**CategoryTheory.Functor.IsTriangulated.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Functor.IsTriangulated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (𝟭 C).IsTriangulated where
  map_distinguished T hT :=
    isomorphic_distinguished _ hT _ ((mapTriangleIdIso C).app T)
/-
**CategoryTheory.Functor.IsTriangulated.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Functor.IsTriangulated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [F.IsTriangulated] [G.IsTriangulated] : (F ⋙ G).IsTriangulated where
  map_distinguished T hT :=
    isomorphic_distinguished _ (G.map_distinguished _ (F.map_distinguished T hT)) _
      ((mapTriangleCompIso F G).app T)

end IsTriangulated

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Functor.map_distinguished_iff** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Functor`。
形式化陈述：map_distinguished_iff [F.IsTriangulated] [Full F] [Faithful F] (T : Triang
le C) : (F.mapTriangle.obj T in distTriang D) ↔ T in distTriang C
参数：T : Triangle C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Pretriangulated.distinguished_cocone_triangle`：∀ {C : Typ
e u} {inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.H
asZeroObject C}   {inst_2 : CategoryTheory.HasShif…
· 使用定理 `CategoryTheory.Pretriangulated.isomorphic_distinguished`：∀ {C : Type u} 
{inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZer
oObject C}   {inst_2 : CategoryTheory.HasShif…
· 使用定理 `CategoryTheory.Functor.instFullTriangleMapTriangleOfFaithful`：∀ {C : Typ
e u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : 
CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Functor.instFaithfulTriangleMapTriangle`：∀ {C : Type u_1}
 {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Catego
ryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用引理 `CategoryTheory.Functor.map_distinguished`：map_distinguished [F.IsTriangu
lated] (T : Triangle C) (hT : T in distTriang C) : F.mapTriangle.obj T in distTr
iang D
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_distinguished_iff [F.IsTriangulated] [Full F] [Faithful F] (T : Triangle C) :
    (F.mapTriangle.obj T ∈ distTriang D) ↔ T ∈ distTriang C := by
  refine ⟨fun hT ↦ ?_, F.map_distinguished T⟩
  obtain ⟨Z, g, h, mem⟩ := distinguished_cocone_triangle T.mor₁
  refine isomorphic_distinguished _ mem _ (F.mapTriangle.preimageIso ?_)
  exact isoTriangleOfIso₁₂ _ _ hT (F.map_distinguished _ mem)
    (Iso.refl _) (Iso.refl _) (by simp)
/-
**CategoryTheory.Functor.isTriangulated_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.Functor`。
形式化陈述：isTriangulated_of_iso {F₁ F₂ : C ⥤ D} (e : F₁ ≅ F₂) [F₁.CommShift Int] [F₂
.CommShift Int] [NatTrans.CommShift e.hom Int] [F₁.IsTriangulated] : F₂.IsTriang
ulated where map_distinguished T hT
参数：e : F₁ ≅ F₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Pretriangulated.isomorphic_distinguished`：∀ {C : Type u} 
{inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZer
oObject C}   {inst_2 : CategoryTheory.HasShif…
· 使用引理 `CategoryTheory.Functor.map_distinguished`：map_distinguished [F.IsTriangu
lated] (T : Triangle C) (hT : T in distTriang C) : F.mapTriangle.obj T in distTr
iang D
-/
lemma isTriangulated_of_iso {F₁ F₂ : C ⥤ D} (e : F₁ ≅ F₂) [F₁.CommShift ℤ] [F₂.CommShift ℤ]
    [NatTrans.CommShift e.hom ℤ] [F₁.IsTriangulated] : F₂.IsTriangulated where
  map_distinguished T hT :=
    isomorphic_distinguished _ (F₁.map_distinguished T hT) _ ((mapTriangleIso e).app T).symm
/-
**CategoryTheory.Functor.isTriangulated_iff_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Functor`。
形式化陈述：isTriangulated_iff_of_iso {F₁ F₂ : C ⥤ D} (e : F₁ ≅ F₂) [F₁.CommShift Int]
 [F₂.CommShift Int] [NatTrans.CommShift e.hom Int] : F₁.IsTriangulated ↔ F₂.IsTr
iangulated
参数：e : F₁ ≅ F₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.isTriangulated_of_iso`：isTriangulated_of_iso {F₁ 
F₂ : C ⥤ D} (e : F₁ ≅ F₂) [F₁.CommShift Int] [F₂.CommShift Int] [NatTrans.CommSh
ift e.hom Int] [F₁.IsTriangulated]…
-/
lemma isTriangulated_iff_of_iso {F₁ F₂ : C ⥤ D} (e : F₁ ≅ F₂) [F₁.CommShift ℤ] [F₂.CommShift ℤ]
    [NatTrans.CommShift e.hom ℤ] : F₁.IsTriangulated ↔ F₂.IsTriangulated := by
  constructor
  · intro
    exact isTriangulated_of_iso e
  · intro
    have : NatTrans.CommShift e.symm.hom ℤ := inferInstanceAs (NatTrans.CommShift e.inv ℤ)
    exact isTriangulated_of_iso e.symm
/-
**CategoryTheory.Functor.isTriangulated_iff_comp_right** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Functor`。
形式化陈述：isTriangulated_iff_comp_right {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E} (e : F ⋙
 G ≅ H) [F.CommShift Int] [G.CommShift Int] [H.CommShift Int] [NatTrans.CommShif
t e.hom Int] [G.IsTriangulated] [G.Full] [G.Faithful] : F.IsTriangulated ↔ H.IsT
riangulated
参数：e : F ⋙ G ≅ H。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Functor.isTriangulated_iff_of_iso`：isTriangulated_iff_of_
iso {F₁ F₂ : C ⥤ D} (e : F₁ ≅ F₂) [F₁.CommShift Int] [F₂.CommShift Int] [NatTran
s.CommShift e.hom Int] : F₁.IsTriangul…
· 使用定理 `CategoryTheory.Functor.IsTriangulated.instComp`：∀ {C : Type u_1} {D : Ty
pe u_2} {E : Type u_3} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 :
 CategoryTheory.Category.{v_2, u_2} …
· 使用引理 `CategoryTheory.Functor.map_distinguished_iff`：map_distinguished_iff [F.I
sTriangulated] [Full F] [Faithful F] (T : Triangle C) : (F.mapTriangle.obj T in 
distTriang D) ↔ T in distTriang C
· 使用定理 `CategoryTheory.Pretriangulated.isomorphic_distinguished`：∀ {C : Type u} 
{inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZer
oObject C}   {inst_2 : CategoryTheory.HasShif…
· 使用引理 `CategoryTheory.Functor.map_distinguished`：map_distinguished [F.IsTriangu
lated] (T : Triangle C) (hT : T in distTriang C) : F.mapTriangle.obj T in distTr
iang D
-/
lemma isTriangulated_iff_comp_right {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E} (e : F ⋙ G ≅ H)
    [F.CommShift ℤ] [G.CommShift ℤ] [H.CommShift ℤ] [NatTrans.CommShift e.hom ℤ]
    [G.IsTriangulated] [G.Full] [G.Faithful] :
    F.IsTriangulated ↔ H.IsTriangulated := by
  rw [← isTriangulated_iff_of_iso e]
  refine ⟨fun _ ↦ inferInstance, fun _ ↦ ⟨fun T hT ↦ ?_⟩⟩
  rw [← G.map_distinguished_iff]
  exact isomorphic_distinguished _ ((F ⋙ G).map_distinguished T hT) _
    ((mapTriangleCompIso F G).symm.app T)
/-
**CategoryTheory.Functor.mem_mapTriangle_essImage_of_distinguished** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：mem_mapTriangle_essImage_of_distinguished [F.IsTriangulated] [F.mapArrow.E
ssSurj] (T : Triangle D) (hT : T in distTriang D) : exists (T' : Triangle C) (_ 
: T' in distTriang C), Nonempty (F.mapTriangle.obj T' ≅ T)
参数：T : Triangle D；hT : T in distTriang D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Arrow.Hom.w`：∀ {T : Type u} [inst : CategoryTheory.Catego
ry.{v, u} T] {f g : CategoryTheory.Arrow T} (sq : f ⟶ g),   CategoryTheory.Categ
oryStruct.comp (…
· 使用定理 `CategoryTheory.Pretriangulated.distinguished_cocone_triangle`：∀ {C : Typ
e u} {inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.H
asZeroObject C}   {inst_2 : CategoryTheory.HasShif…
· 使用引理 `CategoryTheory.Functor.map_distinguished`：map_distinguished [F.IsTriangu
lated] (T : Triangle C) (hT : T in distTriang C) : F.mapTriangle.obj T in distTr
iang D
-/
lemma mem_mapTriangle_essImage_of_distinguished
    [F.IsTriangulated] [F.mapArrow.EssSurj] (T : Triangle D) (hT : T ∈ distTriang D) :
    ∃ (T' : Triangle C) (_ : T' ∈ distTriang C), Nonempty (F.mapTriangle.obj T' ≅ T) := by
  obtain ⟨X, Y, f, e₁, e₂, w⟩ : ∃ (X Y : C) (f : X ⟶ Y) (e₁ : F.obj X ≅ T.obj₁)
    (e₂ : F.obj Y ≅ T.obj₂), F.map f ≫ e₂.hom = e₁.hom ≫ T.mor₁ := by
      let e := F.mapArrow.objObjPreimageIso (Arrow.mk T.mor₁)
      exact ⟨_, _, _, Arrow.leftFunc.mapIso e, Arrow.rightFunc.mapIso e, e.hom.w.symm⟩
  obtain ⟨W, g, h, H⟩ := distinguished_cocone_triangle f
  exact ⟨_, H, ⟨isoTriangleOfIso₁₂ _ _ (F.map_distinguished _ H) hT e₁ e₂ w⟩⟩
/-
**CategoryTheory.Functor.isTriangulated_of_precomp** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Functor`。
形式化陈述：isTriangulated_of_precomp [(F ⋙ G).IsTriangulated] [F.IsTriangulated] [F.m
apArrow.EssSurj] : G.IsTriangulated where map_distinguished T hT
参数：F ⋙ G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.mem_mapTriangle_essImage_of_distinguished`：mem_ma
pTriangle_essImage_of_distinguished [F.IsTriangulated] [F.mapArrow.EssSurj] (T :
 Triangle D) (hT : T in distTriang D) : exists (T' : T…
· 使用定理 `CategoryTheory.Pretriangulated.isomorphic_distinguished`：∀ {C : Type u} 
{inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZer
oObject C}   {inst_2 : CategoryTheory.HasShif…
· 使用引理 `CategoryTheory.Functor.map_distinguished`：map_distinguished [F.IsTriangu
lated] (T : Triangle C) (hT : T in distTriang C) : F.mapTriangle.obj T in distTr
iang D
-/
lemma isTriangulated_of_precomp
    [(F ⋙ G).IsTriangulated] [F.IsTriangulated] [F.mapArrow.EssSurj] :
    G.IsTriangulated where
  map_distinguished T hT := by
    obtain ⟨T', hT', ⟨e⟩⟩ := F.mem_mapTriangle_essImage_of_distinguished T hT
    exact isomorphic_distinguished _ ((F ⋙ G).map_distinguished T' hT') _
      (G.mapTriangle.mapIso e.symm ≪≫ (mapTriangleCompIso F G).symm.app _)

variable {F G} in
/-
**CategoryTheory.Functor.isTriangulated_of_precomp_iso** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Functor`。
形式化陈述：isTriangulated_of_precomp_iso {H : C ⥤ E} (e : F ⋙ G ≅ H) [H.CommShift Int
] [H.IsTriangulated] [F.IsTriangulated] [F.mapArrow.EssSurj] [NatTrans.CommShift
 e.hom Int] : G.IsTriangulated
参数：e : F ⋙ G ≅ H。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `CategoryTheory.Functor.isTriangulated_iff_of_iso`：isTriangulated_iff_of_
iso {F₁ F₂ : C ⥤ D} (e : F₁ ≅ F₂) [F₁.CommShift Int] [F₂.CommShift Int] [NatTran
s.CommShift e.hom Int] : F₁.IsTriangul…
· 使用引理 `CategoryTheory.Functor.isTriangulated_of_precomp`：isTriangulated_of_prec
omp [(F ⋙ G).IsTriangulated] [F.IsTriangulated] [F.mapArrow.EssSurj] : G.IsTrian
gulated where map_distinguished T hT
-/
lemma isTriangulated_of_precomp_iso {H : C ⥤ E} (e : F ⋙ G ≅ H) [H.CommShift ℤ]
    [H.IsTriangulated] [F.IsTriangulated] [F.mapArrow.EssSurj] [NatTrans.CommShift e.hom ℤ] :
    G.IsTriangulated := by
  have := (isTriangulated_iff_of_iso e).2 inferInstance
  exact isTriangulated_of_precomp F G

end Functor

variable {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ] [HasShift D ℤ]
  [HasZeroObject C] [HasZeroObject D] [Preadditive C] [Preadditive D]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D]

namespace Triangulated

namespace Octahedron

variable {X₁ X₂ X₃ Z₁₂ Z₂₃ Z₁₃ : C}
  {u₁₂ : X₁ ⟶ X₂} {u₂₃ : X₂ ⟶ X₃} {u₁₃ : X₁ ⟶ X₃} {comm : u₁₂ ≫ u₂₃ = u₁₃}
  {v₁₂ : X₂ ⟶ Z₁₂} {w₁₂ : Z₁₂ ⟶ X₁⟦(1 : ℤ)⟧} {h₁₂ : Triangle.mk u₁₂ v₁₂ w₁₂ ∈ distTriang C}
  {v₂₃ : X₃ ⟶ Z₂₃} {w₂₃ : Z₂₃ ⟶ X₂⟦(1 : ℤ)⟧} {h₂₃ : Triangle.mk u₂₃ v₂₃ w₂₃ ∈ distTriang C}
  {v₁₃ : X₃ ⟶ Z₁₃} {w₁₃ : Z₁₃ ⟶ X₁⟦(1 : ℤ)⟧} {h₁₃ : Triangle.mk u₁₃ v₁₃ w₁₃ ∈ distTriang C}
  (h : Octahedron comm h₁₂ h₂₃ h₁₃)
  (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]

set_option backward.defeqAttrib.useBackward true in
/-- The image of an octahedron by a triangulated functor. -/
@[simps]
/-
**CategoryTheory.Triangulated.Octahedron.map** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Triangulated.Octahedron`。
形式化陈述：map : Octahedron (by dsimp; rw [← F.map_comp, comm]) (F.map_distinguished 
_ h₁₂) (F.map_distinguished _ h₂₃) (F.map_distinguished _ h₁₃) where m₁
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of an octahedron by a triangulated functor.
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

/-- If `F : C ⥤ D` is a triangulated functor from a triangulated category, then `D`
is also triangulated if tuples of composable arrows in `D` can be lifted to `C`. -/
/-
**CategoryTheory.isTriangulated_of_essSurj_mapComposableArrows_two** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：isTriangulated_of_essSurj_mapComposableArrows_two (F : C ⥤ D) [F.CommShift
 Int] [F.IsTriangulated] [(F.mapComposableArrows 2).EssSurj] [IsTriangulated C] 
: IsTriangulated D
参数：F : C ⥤ D；F.mapComposableArrows 2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ComposableArrows.mk₂_surjective`：mk₂_surjective (X : Comp
osableArrows C 2) : exists (X₀ X₁ X₂ : C) (f₀ : X₀ ⟶ X₁) (f₁ : X₁ ⟶ X₂), X = mk₂
 f₀ f₁
· 使用定理 `CategoryTheory.Pretriangulated.distinguished_cocone_triangle`：∀ {C : Typ
e u} {inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.H
asZeroObject C}   {inst_2 : CategoryTheory.HasShif…
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `CategoryTheory.ComposableArrows.naturality'`：naturality' (φ : F ⟶ G) (i 
j : Nat) (hij : i <= j
· 使用引理 `CategoryTheory.Functor.map_distinguished`：map_distinguished [F.IsTriangu
lated] (T : Triangle C) (hT : T in distTriang C) : F.mapTriangle.obj T in distTr
iang D
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If `F : C ⥤ D` is a triangulated functor from a triangulated category, then `D`
is also triangulated if tuples of composable arrows in `D` can be lifted to `C`.
-/
lemma isTriangulated_of_essSurj_mapComposableArrows_two
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated]
    [(F.mapComposableArrows 2).EssSurj] [IsTriangulated C] :
    IsTriangulated D := by
  apply IsTriangulated.mk
  intro Y₁ Y₂ Y₃ Z₁₂ Z₂₃ Z₁₃ u₁₂ u₂₃ u₁₃ comm v₁₂ w₁₂ h₁₂ v₂₃ w₂₃ h₂₃ v₁₃ w₁₃ h₁₃
  obtain ⟨α, ⟨e⟩⟩ : ∃ (α : ComposableArrows C 2),
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
/-
**CategoryTheory.IsTriangulated.of_fully_faithful_triangulated_functor** 是 Mathl
ib 中的一个定理，位于命名空间 `CategoryTheory.IsTriangulated`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : CategoryTheory.H
asShift C ℤ]   [inst_3 : CategoryTheory.HasShift D ℤ] [inst_4 : CategoryTheory.L
imits.HasZeroObject C]   [inst_5 : CategoryTheory.Limits.HasZeroObject D] [inst_
6 : CategoryTheory.Preadditive C]   [inst_7 : CategoryTheory.Preadditive D] [ins
t_8 : ∀ (n : ℤ), (CategoryTheory.shiftFunctor C n).Additive]   [inst_9 : ∀ (n : 
ℤ), (CategoryTheory.shiftFunctor D n).Additive] [inst_10 : CategoryTheory.Pretri
angulated C]   [inst_11 : CategoryTheory.Pretriangulated D] (F : CategoryTheory.
Functor C D) [inst_12 : F.CommShift ℤ]   [F.IsTriangulated] [F.Full] [F.Faithful
] [CategoryTheory.IsTriangulated D], CategoryTheory.IsTriangulated C
参数：n : ℤ；CategoryTheory.shiftFunctor C n；n : ℤ；CategoryTheory.shiftFunctor D n；F
 : CategoryTheory.Functor C D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用引理 `CategoryTheory.Functor.map_distinguished`：map_distinguished [F.IsTriangu
lated] (T : Triangle C) (hT : T in distTriang C) : F.mapTriangle.obj T in distTr
iang D
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Functor.map_preimage`：map_preimage (F : C ⥤ D) [Full F] {
X Y : C} (f : F.obj X ⟶ F.obj Y) : F.map (preimage F f) = f
· 使用定理 `CategoryTheory.Triangulated.Octahedron.comm₁`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   [
inst_2 : CategoryTheory.Limits.Has…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.strongMono_of_isIso`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {P Q : C} (f : Q ⟶ P) [CategoryTheory.IsIso f],   CategoryT
heory.StrongMono f
· 使用定理 `CategoryTheory.NatIso.hom_app_isIso`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Triangulated.Octahedron.comm₂`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   [
inst_2 : CategoryTheory.Limits.Has…
· 使用定理 `CategoryTheory.Triangulated.Octahedron.comm₃`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   [
inst_2 : CategoryTheory.Limits.Has…
· 使用引理 `CategoryTheory.Functor.commShiftIso_hom_naturality`：commShiftIso_hom_nat
urality {X Y : C} (f : X ⟶ Y) (a : A) : dsimp% F.map (f⟦a⟧') ≫ (F.commShiftIso a
).hom.app Y = (F.commShiftIso a).hom.app…
· 使用定理 `CategoryTheory.Triangulated.Octahedron.comm₄`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   [
inst_2 : CategoryTheory.Limits.Has…
· 使用引理 `CategoryTheory.Functor.map_distinguished_iff`：map_distinguished_iff [F.I
sTriangulated] [Full F] [Faithful F] (T : Triangle C) : (F.mapTriangle.obj T in 
distTriang D) ↔ T in distTriang C
· 使用定理 `CategoryTheory.Triangulated.Octahedron.mem`：∀ {C : Type u_1} [inst : Cat
egoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   [in
st_2 : CategoryTheory.Limits.Has…
-/
lemma IsTriangulated.of_fully_faithful_triangulated_functor
    (F : C ⥤ D) [F.CommShift ℤ]
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
          simpa [← cancel_mono ((F.commShiftIso (1 : ℤ)).hom.app X₁)] using H.comm₂)
        comm₃ := F.map_injective (by simpa using H.comm₃)
        comm₄ := F.map_injective (by
          simpa [← cancel_mono ((F.commShiftIso (1 : ℤ)).hom.app X₂)] using H.comm₄)
        mem := by simpa [← F.map_distinguished_iff] using H.mem }⟩

end CategoryTheory

