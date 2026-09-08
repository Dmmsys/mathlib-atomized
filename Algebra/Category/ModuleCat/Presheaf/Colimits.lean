/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import Mathlib.Algebra.Category.ModuleCat.Colimits

/-! # Colimits in categories of presheaves of modules

In this file, it is shown that under suitable assumptions,
colimits exist in the category `PresheafOfModules R`.

-/

@[expose] public section

universe v v₁ v₂ u₁ u₂ u u'

open CategoryTheory Category Limits

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
  {J : Type u₂} [Category.{v₂} J]
  (F : J ⥤ PresheafOfModules.{v} R)

section Colimits

variable [∀ {X Y : Cᵒᵖ} (f : X ⟶ Y), PreservesColimit (F ⋙ evaluation R Y)
  (ModuleCat.restrictScalars (R.map f).hom)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A cocone in the category `PresheafOfModules R` is colimit if it is so after the application
of the functors `evaluation R X` for all `X`. -/
/-
**PresheafOfModules.evaluationJointlyReflectsColimits** 是 Mathlib 中的一个定义，位于命名空间 
`PresheafOfModules`。
形式化陈述：evaluationJointlyReflectsColimits (c : Cocone F) (hc : forall (X : Cᵒᵖ), I
sColimit ((evaluation R X).mapCocone c)) : IsColimit c where desc s
参数：c : Cocone F；hc : forall (X : Cᵒᵖ), IsColimit ((evaluation R X).mapCocone c)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A cocone in the category `PresheafOfModules R` is colimit if it is so after the 
application
of the functors `evaluation R X` for all `X`.
-/
def evaluationJointlyReflectsColimits (c : Cocone F)
    (hc : ∀ (X : Cᵒᵖ), IsColimit ((evaluation R X).mapCocone c)) : IsColimit c where
  desc s :=
    { app := fun X => (hc X).desc ((evaluation R X).mapCocone s)
      naturality := fun {X Y} f ↦ (hc X).hom_ext (fun j ↦ by
        rw [(hc X).fac_assoc ((evaluation R X).mapCocone s) j]
        have h₁ := (c.ι.app j).naturality f
        have h₂ := (hc Y).fac ((evaluation R Y).mapCocone s)
        dsimp at h₁ h₂ ⊢
        simp only [← reassoc_of% h₁, ← Functor.map_comp, h₂, Hom.naturality]) }
  fac s j := by
    ext1 X
    exact (hc X).fac ((evaluation R X).mapCocone s) j
  uniq s m hm := by
    ext1 X
    apply (hc X).uniq ((evaluation R X).mapCocone s)
    intro j
    dsimp
    rw [← hm]
    rfl

variable [∀ X, HasColimit (F ⋙ evaluation R X)]
/-
**PresheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `PresheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    HasColimit (F ⋙ evaluation R Y ⋙ (ModuleCat.restrictScalars (R.map f).hom)) :=
  ⟨_, isColimitOfPreserves (ModuleCat.restrictScalars (R.map f).hom)
    (colimit.isColimit (F ⋙ evaluation R Y))⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given `F : J ⥤ PresheafOfModules.{v} R`, this is the presheaf of modules obtained by
taking a colimit in the category of modules over `R.obj X` for all `X`. -/
@[simps]
/-
**PresheafOfModules.colimitPresheafOfModules** 是 Mathlib 中的一个定义，位于命名空间 `Presheaf
OfModules`。
形式化陈述：colimitPresheafOfModules : PresheafOfModules R where obj X
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PresheafOfModules.instHasColimitModuleCatCarrierObjOppositeRingCatCompEv
aluationRestrictScalarsHomMap`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{
v₁, u₁} C] {R : CategoryTheory.Functor Cᵒᵖ RingCat} {J : Type u₂}   [inst_1 : Ca
tegoryTheor…

--- 原说明 ---
Given `F : J ⥤ PresheafOfModules.{v} R`, this is the presheaf of modules obtaine
d by
taking a colimit in the category of modules over `R.obj X` for all `X`.
-/
noncomputable def colimitPresheafOfModules : PresheafOfModules R where
  obj X := colimit (F ⋙ evaluation R X)
  map {_ Y} f := colimMap (Functor.whiskerLeft F (restriction R f)) ≫
    (preservesColimitIso (ModuleCat.restrictScalars (R.map f).hom) (F ⋙ evaluation R Y)).inv
  map_id X := colimit.hom_ext (fun j => by
    dsimp
    rw [ι_colimMap_assoc, Functor.whiskerLeft_app, restriction_app]
    -- Here we should rewrite using `Functor.assoc` but that gives a "motive is type-incorrect"
    erw [ι_preservesColimitIso_inv (G := ModuleCat.restrictScalars (R.map (𝟙 X)).hom)]
    rw [ModuleCat.restrictScalarsId'App_inv_naturality, map_id]
    dsimp)
  map_comp {X Y Z} f g := colimit.hom_ext (fun j => by
    dsimp
    rw [ι_colimMap_assoc, Functor.whiskerLeft_app, restriction_app, assoc, ι_colimMap_assoc]
    -- Here we should rewrite using `Functor.assoc` but that gives a "motive is type-incorrect"
    erw [ι_preservesColimitIso_inv (G := ModuleCat.restrictScalars (R.map (f ≫ g)).hom),
      ι_preservesColimitIso_inv_assoc (G := ModuleCat.restrictScalars (R.map f).hom)]
    rw [← Functor.map_comp_assoc, ι_colimMap_assoc]
    erw [ι_preservesColimitIso_inv (G := ModuleCat.restrictScalars (R.map g).hom)]
    rw [map_comp, ModuleCat.restrictScalarsComp'_inv_app, assoc, assoc,
      Functor.whiskerLeft_app, Functor.whiskerLeft_app, restriction_app, restriction_app]
    simp only [Functor.map_comp, assoc]
    rfl)

set_option backward.defeqAttrib.useBackward true in
/-- The (colimit) cocone for `F : J ⥤ PresheafOfModules.{v} R` that is constructed from
the colimit of `F ⋙ evaluation R X` for all `X`. -/
@[simps]
/-
**PresheafOfModules.colimitCocone** 是 Mathlib 中的一个定义，位于命名空间 `PresheafOfModules`。
形式化陈述：colimitCocone : Cocone F where pt
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (colimit) cocone for `F : J ⥤ PresheafOfModules.{v} R` that is constructed f
rom
the colimit of `F ⋙ evaluation R X` for all `X`.
-/
noncomputable def colimitCocone : Cocone F where
  pt := colimitPresheafOfModules F
  ι :=
    { app := fun j ↦
        { app := fun X ↦ colimit.ι (F ⋙ evaluation R X) j
          naturality := fun {X Y} f ↦ by
            dsimp
            erw [colimit.ι_desc_assoc, assoc, ← ι_preservesColimitIso_inv]
            rfl }
      naturality := fun {X Y} f ↦ by
        ext1 X
        simpa using colimit.w (F ⋙ evaluation R X) f }

/-- The cocone `colimitCocone F` is colimit for any `F : J ⥤ PresheafOfModules.{v} R`. -/
/-
**PresheafOfModules.isColimitColimitCocone** 是 Mathlib 中的一个定义，位于命名空间 `PresheafOf
Modules`。
形式化陈述：isColimitColimitCocone : IsColimit (colimitCocone F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cocone `colimitCocone F` is colimit for any `F : J ⥤ PresheafOfModules.{v} R
`.
-/
noncomputable def isColimitColimitCocone : IsColimit (colimitCocone F) :=
  evaluationJointlyReflectsColimits _ _ (fun _ => colimit.isColimit _)
/-
**PresheafOfModules.hasColimit** 是 Mathlib 中的一个实例，位于命名空间 `PresheafOfModules`。
形式化陈述：hasColimit : HasColimit F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasColimit : HasColimit F := ⟨_, isColimitColimitCocone F⟩
/-
**PresheafOfModules.evaluation_preservesColimit** 是 Mathlib 中的一个实例，位于命名空间 `Presh
eafOfModules`。
形式化陈述：evaluation_preservesColimit (X : Cᵒᵖ) : PreservesColimit F (evaluation R X
)
参数：X : Cᵒᵖ。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimit_of_preserves_colimit_cocone`：pres
ervesColimit_of_preserves_colimit_cocone {F : C ⥤ D} {t : Cocone K} (h : IsColim
it t) (hF : IsColimit (F.mapCocone t)) : PreservesColimi…
-/
instance evaluation_preservesColimit (X : Cᵒᵖ) :
    PreservesColimit F (evaluation R X) :=
  preservesColimit_of_preserves_colimit_cocone (isColimitColimitCocone F) (colimit.isColimit _)

variable [∀ X, PreservesColimit F
  (evaluation R X ⋙ forget₂ (ModuleCat (R.obj X)) AddCommGrpCat)]
/-
**PresheafOfModules.toPresheaf_preservesColimit** 是 Mathlib 中的一个实例，位于命名空间 `Presh
eafOfModules`。
形式化陈述：toPresheaf_preservesColimit : PreservesColimit F (toPresheaf R)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimit_of_preserves_colimit_cocone`：pres
ervesColimit_of_preserves_colimit_cocone {F : C ⥤ D} {t : Cocone K} (h : IsColim
it t) (hF : IsColimit (F.mapCocone t)) : PreservesColimi…
-/
instance toPresheaf_preservesColimit :
    PreservesColimit F (toPresheaf R) :=
  preservesColimit_of_preserves_colimit_cocone (isColimitColimitCocone F)
    (Limits.evaluationJointlyReflectsColimits _
      (fun X => isColimitOfPreserves (evaluation R X ⋙ forget₂ _ AddCommGrpCat)
        (isColimitColimitCocone F)))

end Colimits

variable (R J)

section HasColimitsOfShape

variable [HasColimitsOfShape J AddCommGrpCat.{v}]

/-
**PresheafOfModules.hasColimitsOfShape** 是 Mathlib 中的一个定理，位于命名空间 `PresheafOfModu
les`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] (R : CategoryT
heory.Functor Cᵒᵖ RingCat) (J : Type u₂)   [inst_1 : CategoryTheory.Category.{v₂
, u₂} J] [CategoryTheory.Limits.HasColimitsOfShape J AddCommGrpCat],   CategoryT
heory.Limits.HasColimitsOfShape J (PresheafOfModules R)
参数：R : CategoryTheory.Functor Cᵒᵖ RingCat；J : Type u₂；PresheafOfModules R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitCompOfPreservesColimit`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Category
Theory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `ModuleCat.hasColimitsOfShape`：∀ (R : Type w) [inst : Ring R] (J : Type u
) [inst_1 : CategoryTheory.Category.{v, u} J]   [CategoryTheory.Limits.HasColimi
tsOfShape J AddCom…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `ModuleCat.forget₂PreservesColimitsOfShape`：∀ (R : Type w) [inst : Ring R
] (J : Type u) [inst_1 : CategoryTheory.Category.{v, u} J]   [CategoryTheory.Lim
its.HasColimitsOfShape J AddCom…
-/
instance hasColimitsOfShape : HasColimitsOfShape J (PresheafOfModules.{v} R) where
/-
**PresheafOfModules.evaluation_preservesColimitsOfShape** 是 Mathlib 中的一个定理，位于命名空
间 `PresheafOfModules`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] (R : CategoryT
heory.Functor Cᵒᵖ RingCat) (J : Type u₂)   [inst_1 : CategoryTheory.Category.{v₂
, u₂} J] [CategoryTheory.Limits.HasColimitsOfShape J AddCommGrpCat] (X : Cᵒᵖ),  
 CategoryTheory.Limits.PreservesColimitsOfShape J (PresheafOfModules.evaluation 
R X)
参数：R : CategoryTheory.Functor Cᵒᵖ RingCat；J : Type u₂；X : Cᵒᵖ；PresheafOfModules.
evaluation R X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitCompOfPreservesColimit`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Category
Theory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `ModuleCat.hasColimitsOfShape`：∀ (R : Type w) [inst : Ring R] (J : Type u
) [inst_1 : CategoryTheory.Category.{v, u} J]   [CategoryTheory.Limits.HasColimi
tsOfShape J AddCom…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `ModuleCat.forget₂PreservesColimitsOfShape`：∀ (R : Type w) [inst : Ring R
] (J : Type u) [inst_1 : CategoryTheory.Category.{v, u} J]   [CategoryTheory.Lim
its.HasColimitsOfShape J AddCom…
-/
noncomputable instance evaluation_preservesColimitsOfShape (X : Cᵒᵖ) :
    PreservesColimitsOfShape J (evaluation R X : PresheafOfModules.{v} R ⥤ _) where
/-
**PresheafOfModules.toPresheaf_preservesColimitsOfShape** 是 Mathlib 中的一个定理，位于命名空
间 `PresheafOfModules`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] (R : CategoryT
heory.Functor Cᵒᵖ RingCat) (J : Type u₂)   [inst_1 : CategoryTheory.Category.{v₂
, u₂} J] [CategoryTheory.Limits.HasColimitsOfShape J AddCommGrpCat],   CategoryT
heory.Limits.PreservesColimitsOfShape J (PresheafOfModules.toPresheaf R)
参数：R : CategoryTheory.Functor Cᵒᵖ RingCat；J : Type u₂；PresheafOfModules.toPreshe
af R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitCompOfPreservesColimit`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Category
Theory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `PresheafOfModules.hasColimitsOfShape`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] (R : CategoryTheory.Functor Cᵒᵖ RingCat) (J : Type u₂)
   [inst_1 : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `PresheafOfModules.evaluation_preservesColimitsOfShape`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] (R : CategoryTheory.Functor Cᵒᵖ RingC
at) (J : Type u₂)   [inst_1 : CategoryTheor…
· 使用定理 `ModuleCat.forget₂PreservesColimitsOfShape`：∀ (R : Type w) [inst : Ring R
] (J : Type u) [inst_1 : CategoryTheory.Category.{v, u} J]   [CategoryTheory.Lim
its.HasColimitsOfShape J AddCom…
-/
noncomputable instance toPresheaf_preservesColimitsOfShape :
    PreservesColimitsOfShape J (toPresheaf.{v} R) where

end HasColimitsOfShape

namespace Finite

/-
**PresheafOfModules.Finite.hasFiniteColimits** 是 Mathlib 中的一个实例，位于命名空间 `Presheaf
OfModules.Finite`。
形式化陈述：hasFiniteColimits : HasFiniteColimits (PresheafOfModules.{v} R)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `PresheafOfModules.hasColimitsOfShape`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] (R : CategoryTheory.Functor Cᵒᵖ RingCat) (J : Type u₂)
   [inst_1 : CategoryTheor…
· 使用定理 `AddCommGrpCat.hasColimitsOfShape`：∀ {J : Type u} [inst : CategoryTheory.
Category.{v, u} J] [Small.{w, u} J],   CategoryTheory.Limits.HasColimitsOfShape 
J AddCommGrpCat
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
instance hasFiniteColimits : HasFiniteColimits (PresheafOfModules.{v} R) :=
  ⟨fun _ => inferInstance⟩
/-
**PresheafOfModules.Finite.evaluation_preservesFiniteColimits** 是 Mathlib 中的一个定理
，位于命名空间 `PresheafOfModules.Finite`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] (R : CategoryT
heory.Functor Cᵒᵖ RingCat) (X : Cᵒᵖ),   CategoryTheory.Limits.PreservesFiniteCol
imits (PresheafOfModules.evaluation R X)
参数：R : CategoryTheory.Functor Cᵒᵖ RingCat；X : Cᵒᵖ；PresheafOfModules.evaluation R
 X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PresheafOfModules.evaluation_preservesColimitsOfShape`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] (R : CategoryTheory.Functor Cᵒᵖ RingC
at) (J : Type u₂)   [inst_1 : CategoryTheor…
· 使用定理 `AddCommGrpCat.hasColimitsOfShape`：∀ {J : Type u} [inst : CategoryTheory.
Category.{v, u} J] [Small.{w, u} J],   CategoryTheory.Limits.HasColimitsOfShape 
J AddCommGrpCat
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
noncomputable instance evaluation_preservesFiniteColimits (X : Cᵒᵖ) :
    PreservesFiniteColimits (evaluation.{v} R X) where
/-
**PresheafOfModules.Finite.toPresheaf_preservesFiniteColimits** 是 Mathlib 中的一个定理
，位于命名空间 `PresheafOfModules.Finite`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] (R : CategoryT
heory.Functor Cᵒᵖ RingCat),   CategoryTheory.Limits.PreservesFiniteColimits (Pre
sheafOfModules.toPresheaf R)
参数：R : CategoryTheory.Functor Cᵒᵖ RingCat；PresheafOfModules.toPresheaf R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PresheafOfModules.toPresheaf_preservesColimitsOfShape`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] (R : CategoryTheory.Functor Cᵒᵖ RingC
at) (J : Type u₂)   [inst_1 : CategoryTheor…
· 使用定理 `AddCommGrpCat.hasColimitsOfShape`：∀ {J : Type u} [inst : CategoryTheory.
Category.{v, u} J] [Small.{w, u} J],   CategoryTheory.Limits.HasColimitsOfShape 
J AddCommGrpCat
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
noncomputable instance toPresheaf_preservesFiniteColimits :
    PreservesFiniteColimits (toPresheaf R) where

end Finite

section HasColimitsOfSize

variable [HasColimitsOfSize.{v₂, u₂} AddCommGrpCat.{v}]

/-
**PresheafOfModules.hasColimitsOfSize** 是 Mathlib 中的一个定理，位于命名空间 `PresheafOfModul
es`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] (R : CategoryT
heory.Functor Cᵒᵖ RingCat)   [CategoryTheory.Limits.HasColimitsOfSize.{v₂, u₂, v
, v + 1} AddCommGrpCat],   CategoryTheory.Limits.HasColimitsOfSize.{v₂, u₂, max 
u₁ v, max (max (max (v + 1) u) u₁) v₁} (PresheafOfModules R)
参数：R : CategoryTheory.Functor Cᵒᵖ RingCat；max (max (v + 1) u) u₁；PresheafOfModul
es R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PresheafOfModules.hasColimitsOfShape`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] (R : CategoryTheory.Functor Cᵒᵖ RingCat) (J : Type u₂)
   [inst_1 : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.instHasColimitsOfShapeOfHasColimitsOfSize`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : Catego
ryTheory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
instance hasColimitsOfSize : HasColimitsOfSize.{v₂, u₂} (PresheafOfModules.{v} R) where
/-
**PresheafOfModules.evaluation_preservesColimitsOfSize** 是 Mathlib 中的一个定理，位于命名空间
 `PresheafOfModules`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] (R : CategoryT
heory.Functor Cᵒᵖ RingCat)   [CategoryTheory.Limits.HasColimitsOfSize.{v₂, u₂, v
, v + 1} AddCommGrpCat] (X : Cᵒᵖ),   CategoryTheory.Limits.PreservesColimitsOfSi
ze.{v₂, u₂, max u₁ v, v, max (max (max u u₁) (v + 1)) v₁, max u (v + 1)}     (Pr
esheafOfModules.evaluation R X)
参数：R : CategoryTheory.Functor Cᵒᵖ RingCat；X : Cᵒᵖ；max (max u u₁) (v + 1)；v + 1；P
resheafOfModules.evaluation R X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PresheafOfModules.evaluation_preservesColimitsOfShape`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] (R : CategoryTheory.Functor Cᵒᵖ RingC
at) (J : Type u₂)   [inst_1 : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.instHasColimitsOfShapeOfHasColimitsOfSize`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : Catego
ryTheory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
noncomputable instance evaluation_preservesColimitsOfSize (X : Cᵒᵖ) :
    PreservesColimitsOfSize.{v₂, u₂} (evaluation R X : PresheafOfModules.{v} R ⥤ _) where
/-
**PresheafOfModules.toPresheaf_preservesColimitsOfSize** 是 Mathlib 中的一个定理，位于命名空间
 `PresheafOfModules`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] (R : CategoryT
heory.Functor Cᵒᵖ RingCat)   [CategoryTheory.Limits.HasColimitsOfSize.{v₂, u₂, v
, v + 1} AddCommGrpCat],   CategoryTheory.Limits.PreservesColimitsOfSize.{v₂, u₂
, max u₁ v, max u₁ v, max (max (max u u₁) (v + 1)) v₁,       max (max u₁ (v + 1)
) v₁}     (PresheafOfModules.toPresheaf R)
参数：R : CategoryTheory.Functor Cᵒᵖ RingCat；max (max u u₁) (v + 1)；max u₁ (v + 1)；
PresheafOfModules.toPresheaf R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PresheafOfModules.toPresheaf_preservesColimitsOfShape`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] (R : CategoryTheory.Functor Cᵒᵖ RingC
at) (J : Type u₂)   [inst_1 : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.instHasColimitsOfShapeOfHasColimitsOfSize`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : Catego
ryTheory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
noncomputable instance toPresheaf_preservesColimitsOfSize :
    PreservesColimitsOfSize.{v₂, u₂} (toPresheaf.{v} R) where

end HasColimitsOfSize

end PresheafOfModules

