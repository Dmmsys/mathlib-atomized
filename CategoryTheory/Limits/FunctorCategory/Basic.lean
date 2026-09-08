/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Limits.Preserves.Limits

/-!
# (Co)limits in functor categories.

We show that if `D` has limits, then the functor category `C ⥤ D` also has limits
(`CategoryTheory.Limits.functorCategoryHasLimits`),
and the evaluation functors preserve limits
(`CategoryTheory.Limits.evaluation_preservesLimits`)
(and similarly for colimits).

We also show that `F : D ⥤ K ⥤ C` preserves (co)limits if it does so for each `k : K`
(`CategoryTheory.Limits.preservesLimits_of_evaluation` and
`CategoryTheory.Limits.preservesColimits_of_evaluation`).
-/

@[expose] public section


open CategoryTheory CategoryTheory.Category CategoryTheory.Functor

-- morphism levels before object levels. See note [category theory universes].
universe w' w v₁ v₂ u₁ u₂ v v' u u'

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
variable {J : Type u₁} [Category.{v₁} J] {K : Type u₂} [Category.{v₂} K]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.limit.lift_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Li
mits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem limit.lift_π_app (H : J ⥤ K ⥤ C) [HasLimit H] (c : Cone H) (j : J) (k : K) :
    (limit.lift H c).app k ≫ (limit.π H j).app k = (c.π.app j).app k :=
  congr_app (limit.lift_π c j) k

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.colimit.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limit
s`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem colimit.ι_desc_app (H : J ⥤ K ⥤ C) [HasColimit H] (c : Cocone H) (j : J) (k : K) :
    (colimit.ι H j).app k ≫ (colimit.desc H c).app k = (c.ι.app j).app k :=
  congr_app (colimit.ι_desc c j) k

set_option backward.isDefEq.respectTransparency false in
/-- The evaluation functors jointly reflect limits: that is, to show a cone is a limit of `F`
it suffices to show that each evaluation cone is a limit. In other words, to prove a cone is
limiting you can show it's pointwise limiting.
-/
/-
**CategoryTheory.Limits.evaluationJointlyReflectsLimits** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.Limits`。
形式化陈述：evaluationJointlyReflectsLimits {F : J ⥤ K ⥤ C} (c : Cone F) (t : forall k
 : K, IsLimit (((evaluation K C).obj k).mapCone c)) : IsLimit c where lift s
参数：c : Cone F；t : forall k : K, IsLimit (((evaluation K C).obj k).mapCone c)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The evaluation functors jointly reflect limits: that is, to show a cone is a lim
it of `F`
it suffices to show that each evaluation cone is a limit. In other words, to pro
ve a cone is
limiting you can show it's pointwise limiting.
-/
def evaluationJointlyReflectsLimits {F : J ⥤ K ⥤ C} (c : Cone F)
    (t : ∀ k : K, IsLimit (((evaluation K C).obj k).mapCone c)) : IsLimit c where
  lift s :=
    { app := fun k => (t k).lift ⟨s.pt.obj k, whiskerRight s.π ((evaluation K C).obj k)⟩
      naturality := fun X Y f =>
        (t Y).hom_ext fun j => by
          rw [assoc, (t Y).fac _ j]
          simpa using
            ((t X).fac_assoc ⟨s.pt.obj X, whiskerRight s.π ((evaluation K C).obj X)⟩ j _).symm }
  fac s j := by ext k; exact (t k).fac _ j
  uniq s m w := by
    ext x
    exact (t x).hom_ext fun j =>
      (congr_app (w j) x).trans
        ((t x).fac ⟨s.pt.obj _, whiskerRight s.π ((evaluation K C).obj _)⟩ j).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given a functor `F` and a collection of limit cones for each diagram `X ↦ F X k`, we can stitch
them together to give a cone for the diagram `F`.
`combinedIsLimit` shows that the new cone is limiting, and `evalCombined` shows it is
(essentially) made up of the original cones.
-/
@[simps]
/-
**CategoryTheory.Limits.combineCones** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.L
imits`。
形式化陈述：combineCones (F : J ⥤ K ⥤ C) (c : forall k : K, LimitCone (F.flip.obj k)) 
: Cone F where pt
参数：F : J ⥤ K ⥤ C；c : forall k : K, LimitCone (F.flip.obj k)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a functor `F` and a collection of limit cones for each diagram `X ↦ F X k`
, we can stitch
them together to give a cone for the diagram `F`.
`combinedIsLimit` shows that the new cone is limiting, and `evalCombined` shows 
it is
(essentially) made up of the original cones.
-/
def combineCones (F : J ⥤ K ⥤ C) (c : ∀ k : K, LimitCone (F.flip.obj k)) : Cone F where
  pt :=
    { obj := fun k => (c k).cone.pt
      map := fun {k₁} {k₂} f => (c k₂).isLimit.lift ⟨_, (c k₁).cone.π ≫ F.flip.map f⟩
      map_id := fun k =>
        (c k).isLimit.hom_ext fun j => by simp
      map_comp := fun {k₁} {k₂} {k₃} f₁ f₂ => (c k₃).isLimit.hom_ext fun j => by simp }
  π :=
    { app := fun j => { app := fun k => (c k).cone.π.app j }
      naturality := fun j₁ j₂ g => by ext k; exact (c k).cone.π.naturality g }

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The stitched together cones each project down to the original given cones (up to iso). -/
/-
**CategoryTheory.Limits.evaluateCombinedCones** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：evaluateCombinedCones (F : J ⥤ K ⥤ C) (c : forall k : K, LimitCone (F.flip
.obj k)) (k : K) : ((evaluation K C).obj k).mapCone (combineCones F c) ≅ (c k).c
one
参数：F : J ⥤ K ⥤ C；c : forall k : K, LimitCone (F.flip.obj k)；k : K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The stitched together cones each project down to the original given cones (up to
 iso).
-/
def evaluateCombinedCones (F : J ⥤ K ⥤ C) (c : ∀ k : K, LimitCone (F.flip.obj k)) (k : K) :
    ((evaluation K C).obj k).mapCone (combineCones F c) ≅ (c k).cone :=
  Cone.ext (Iso.refl _)

set_option backward.isDefEq.respectTransparency false in
/-- Stitching together limiting cones gives a limiting cone. -/
/-
**CategoryTheory.Limits.combinedIsLimit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Limits`。
形式化陈述：combinedIsLimit (F : J ⥤ K ⥤ C) (c : forall k : K, LimitCone (F.flip.obj k
)) : IsLimit (combineCones F c)
参数：F : J ⥤ K ⥤ C；c : forall k : K, LimitCone (F.flip.obj k)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Stitching together limiting cones gives a limiting cone.
-/
def combinedIsLimit (F : J ⥤ K ⥤ C) (c : ∀ k : K, LimitCone (F.flip.obj k)) :
    IsLimit (combineCones F c) :=
  evaluationJointlyReflectsLimits _ fun k =>
    (c k).isLimit.ofIsoLimit (evaluateCombinedCones F c k).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The evaluation functors jointly reflect colimits: that is, to show a cocone is a colimit of `F`
it suffices to show that each evaluation cocone is a colimit. In other words, to prove a cocone is
colimiting you can show it's pointwise colimiting.
-/
/-
**CategoryTheory.Limits.evaluationJointlyReflectsColimits** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Limits`。
形式化陈述：evaluationJointlyReflectsColimits {F : J ⥤ K ⥤ C} (c : Cocone F) (t : fora
ll k : K, IsColimit (((evaluation K C).obj k).mapCocone c)) : IsColimit c where 
desc s
参数：c : Cocone F；t : forall k : K, IsColimit (((evaluation K C).obj k).mapCocone 
c)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The evaluation functors jointly reflect colimits: that is, to show a cocone is a
 colimit of `F`
it suffices to show that each evaluation cocone is a colimit. In other words, to
 prove a cocone is
colimiting you can show it's pointwise colimiting.
-/
def evaluationJointlyReflectsColimits {F : J ⥤ K ⥤ C} (c : Cocone F)
    (t : ∀ k : K, IsColimit (((evaluation K C).obj k).mapCocone c)) : IsColimit c where
  desc s :=
    { app := fun k => (t k).desc ⟨s.pt.obj k, whiskerRight s.ι ((evaluation K C).obj k)⟩
      naturality := fun X Y f =>
        (t X).hom_ext fun j => by
          rw [(t X).fac_assoc _ j]
          erw [← (c.ι.app j).naturality_assoc f]
          erw [(t Y).fac ⟨s.pt.obj _, whiskerRight s.ι _⟩ j]
          simp }
  fac s j := by ext k; exact (t k).fac _ j
  uniq s m w := by
    ext x
    exact (t x).hom_ext fun j =>
      (congr_app (w j) x).trans
        ((t x).fac ⟨s.pt.obj _, whiskerRight s.ι ((evaluation K C).obj _)⟩ j).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Given a functor `F` and a collection of colimit cocones for each diagram `X ↦ F X k`, we can stitch
them together to give a cocone for the diagram `F`.
`combinedIsColimit` shows that the new cocone is colimiting, and `evalCombined` shows it is
(essentially) made up of the original cocones.
-/
@[simps]
/-
**CategoryTheory.Limits.combineCocones** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Limits`。
形式化陈述：combineCocones (F : J ⥤ K ⥤ C) (c : forall k : K, ColimitCocone (F.flip.ob
j k)) : Cocone F where pt
参数：F : J ⥤ K ⥤ C；c : forall k : K, ColimitCocone (F.flip.obj k)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a functor `F` and a collection of colimit cocones for each diagram `X ↦ F 
X k`, we can stitch
them together to give a cocone for the diagram `F`.
`combinedIsColimit` shows that the new cocone is colimiting, and `evalCombined` 
shows it is
(essentially) made up of the original cocones.
-/
def combineCocones (F : J ⥤ K ⥤ C) (c : ∀ k : K, ColimitCocone (F.flip.obj k)) : Cocone F where
  pt :=
    { obj := fun k => (c k).cocone.pt
      map := fun {k₁} {k₂} f => (c k₁).isColimit.desc ⟨_, F.flip.map f ≫ (c k₂).cocone.ι⟩
      map_id := fun k =>
        (c k).isColimit.hom_ext fun j => by simp
      map_comp := fun {k₁} {k₂} {k₃} f₁ f₂ => (c k₁).isColimit.hom_ext fun j => by simp }
  ι :=
    { app := fun j => { app := fun k => (c k).cocone.ι.app j }
      naturality := fun j₁ j₂ g => by ext k; exact (c k).cocone.ι.naturality g }

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The stitched together cocones each project down to the original given cocones (up to iso). -/
/-
**CategoryTheory.Limits.evaluateCombinedCocones** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：evaluateCombinedCocones (F : J ⥤ K ⥤ C) (c : forall k : K, ColimitCocone (
F.flip.obj k)) (k : K) : ((evaluation K C).obj k).mapCocone (combineCocones F c)
 ≅ (c k).cocone
参数：F : J ⥤ K ⥤ C；c : forall k : K, ColimitCocone (F.flip.obj k)；k : K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The stitched together cocones each project down to the original given cocones (u
p to iso).
-/
def evaluateCombinedCocones (F : J ⥤ K ⥤ C) (c : ∀ k : K, ColimitCocone (F.flip.obj k)) (k : K) :
    ((evaluation K C).obj k).mapCocone (combineCocones F c) ≅ (c k).cocone :=
  Cocone.ext (Iso.refl _)

set_option backward.isDefEq.respectTransparency false in
/-- Stitching together colimiting cocones gives a colimiting cocone. -/
/-
**CategoryTheory.Limits.combinedIsColimit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Limits`。
形式化陈述：combinedIsColimit (F : J ⥤ K ⥤ C) (c : forall k : K, ColimitCocone (F.flip
.obj k)) : IsColimit (combineCocones F c)
参数：F : J ⥤ K ⥤ C；c : forall k : K, ColimitCocone (F.flip.obj k)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Stitching together colimiting cocones gives a colimiting cocone.
-/
def combinedIsColimit (F : J ⥤ K ⥤ C) (c : ∀ k : K, ColimitCocone (F.flip.obj k)) :
    IsColimit (combineCocones F c) :=
  evaluationJointlyReflectsColimits _ fun k =>
    (c k).isColimit.ofIsoColimit (evaluateCombinedCocones F c k).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
An alternative colimit cocone in the functor category `K ⥤ C` in the case where `C` has
`J`-shaped colimits, with cocone point `F.flip ⋙ colim`.
-/
@[simps]
/-
**CategoryTheory.Limits.pointwiseCocone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Limits`。
形式化陈述：pointwiseCocone [HasColimitsOfShape J C] (F : J ⥤ K ⥤ C) : Cocone F where 
pt
参数：F : J ⥤ K ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An alternative colimit cocone in the functor category `K ⥤ C` in the case where 
`C` has
`J`-shaped colimits, with cocone point `F.flip ⋙ colim`.
-/
noncomputable def pointwiseCocone [HasColimitsOfShape J C] (F : J ⥤ K ⥤ C) : Cocone F where
  pt := F.flip ⋙ colim
  ι := {
    app X := { app Y := (colimit.ι _ X : (F.flip.obj Y).obj X ⟶ _) }
    naturality X Y f := by
      ext x
      simp only [Functor.const_obj_obj, Functor.comp_obj, colim_obj, NatTrans.comp_app,
        Functor.const_obj_map, Category.comp_id]
      change (F.flip.obj x).map f ≫ _ = _
      rw [colimit.w] }

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- `pointwiseCocone` is indeed a colimit cocone. -/
/-
**CategoryTheory.Limits.pointwiseIsColimit** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：pointwiseIsColimit [HasColimitsOfShape J C] (F : J ⥤ K ⥤ C) : IsColimit (p
ointwiseCocone F)
参数：F : J ⥤ K ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`pointwiseCocone` is indeed a colimit cocone.
-/
noncomputable def pointwiseIsColimit [HasColimitsOfShape J C] (F : J ⥤ K ⥤ C) :
    IsColimit (pointwiseCocone F) := by
  apply IsColimit.ofIsoColimit (combinedIsColimit _
    (fun k ↦ ⟨colimit.cocone _, colimit.isColimit _⟩))
  exact Cocone.ext (Iso.refl _)

noncomputable section
/-
**CategoryTheory.Limits.functorCategoryHasLimit** 是 Mathlib 中的一个实例，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：functorCategoryHasLimit (F : J ⥤ K ⥤ C) [forall k, HasLimit (F.flip.obj k)
] : HasLimit F
参数：F : J ⥤ K ⥤ C；F.flip.obj k。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasLimit.mk`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C] 
  {F : CategoryTheory.F…
-/
instance functorCategoryHasLimit (F : J ⥤ K ⥤ C) [∀ k, HasLimit (F.flip.obj k)] : HasLimit F :=
  HasLimit.mk
    { cone := combineCones F fun _ => getLimitCone _
      isLimit := combinedIsLimit _ _ }
/-
**CategoryTheory.Limits.functorCategoryHasLimitsOfShape** 是 Mathlib 中的一个实例，位于命名空
间 `CategoryTheory.Limits`。
形式化陈述：functorCategoryHasLimitsOfShape [HasLimitsOfShape J C] : HasLimitsOfShape 
J (K ⥤ C) where has_limit _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
instance functorCategoryHasLimitsOfShape [HasLimitsOfShape J C] : HasLimitsOfShape J (K ⥤ C) where
  has_limit _ := inferInstance
/-
**CategoryTheory.Limits.functorCategoryHasColimit** 是 Mathlib 中的一个实例，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：functorCategoryHasColimit (F : J ⥤ K ⥤ C) [forall k, HasColimit (F.flip.ob
j k)] : HasColimit F
参数：F : J ⥤ K ⥤ C；F.flip.obj k。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasColimit.mk`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…
-/
instance functorCategoryHasColimit (F : J ⥤ K ⥤ C) [∀ k, HasColimit (F.flip.obj k)] :
    HasColimit F :=
  HasColimit.mk
    { cocone := combineCocones F fun _ => getColimitCocone _
      isColimit := combinedIsColimit _ _ }
/-
**CategoryTheory.Limits.functorCategoryHasColimitsOfShape** 是 Mathlib 中的一个实例，位于命
名空间 `CategoryTheory.Limits`。
形式化陈述：functorCategoryHasColimitsOfShape [HasColimitsOfShape J C] : HasColimitsOf
Shape J (K ⥤ C) where has_colimit _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
instance functorCategoryHasColimitsOfShape [HasColimitsOfShape J C] :
    HasColimitsOfShape J (K ⥤ C) where
  has_colimit _ := inferInstance
/-
**CategoryTheory.Limits.functorCategoryHasLimitsOfSize** 是 Mathlib 中的一个实例，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：functorCategoryHasLimitsOfSize [HasLimitsOfSize.{v₁, u₁} C] : HasLimitsOfS
ize.{v₁, u₁} (K ⥤ C) where has_limits_of_shape
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitsOfShapeOfHasLimitsOfSize`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTh
eory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
instance functorCategoryHasLimitsOfSize [HasLimitsOfSize.{v₁, u₁} C] :
    HasLimitsOfSize.{v₁, u₁} (K ⥤ C) where
  has_limits_of_shape := inferInstance
/-
**CategoryTheory.Limits.functorCategoryHasColimitsOfSize** 是 Mathlib 中的一个实例，位于命名
空间 `CategoryTheory.Limits`。
形式化陈述：functorCategoryHasColimitsOfSize [HasColimitsOfSize.{v₁, u₁} C] : HasColim
itsOfSize.{v₁, u₁} (K ⥤ C) where has_colimits_of_shape
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitsOfShapeOfHasColimitsOfSize`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : Catego
ryTheory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
instance functorCategoryHasColimitsOfSize [HasColimitsOfSize.{v₁, u₁} C] :
    HasColimitsOfSize.{v₁, u₁} (K ⥤ C) where
  has_colimits_of_shape := inferInstance
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) hasLimitCompEvaluation (F : J ⥤ K ⥤ C) (k : K)
    [HasLimit (F.flip.obj k)] : HasLimit (F ⋙ (evaluation _ _).obj k) :=
  hasLimit_of_iso (F := F.flip.obj k) (Iso.refl _)
/-
**CategoryTheory.Limits.evaluation_preservesLimit** 是 Mathlib 中的一个实例，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：evaluation_preservesLimit (F : J ⥤ K ⥤ C) [forall k, HasLimit (F.flip.obj 
k)] (k : K) : PreservesLimit F ((evaluation K C).obj k)
参数：F : J ⥤ K ⥤ C；F.flip.obj k；k : K。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_preserves_limit_cone`：preservesL
imit_of_preserves_limit_cone {F : C ⥤ D} {t : Cone K} (h : IsLimit t) (hF : IsLi
mit (F.mapCone t)) : PreservesLimit K F where pres…
· 使用定理 `CategoryTheory.Limits.hasLimitCompEvaluation`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Category.{
v₁, u₁} J]   {K : Type u₂} [inst_2…
-/
instance evaluation_preservesLimit (F : J ⥤ K ⥤ C) [∀ k, HasLimit (F.flip.obj k)] (k : K) :
    PreservesLimit F ((evaluation K C).obj k) :=
  -- Porting note: added a let because X was not inferred
  let X : (k : K) → LimitCone (F.flip.obj k) := fun k => getLimitCone (F.flip.obj k)
  preservesLimit_of_preserves_limit_cone (combinedIsLimit _ X) <|
    IsLimit.ofIsoLimit (limit.isLimit _) (evaluateCombinedCones F X k).symm
/-
**CategoryTheory.Limits.evaluation_preservesLimitsOfShape** 是 Mathlib 中的一个实例，位于命
名空间 `CategoryTheory.Limits`。
形式化陈述：evaluation_preservesLimitsOfShape [HasLimitsOfShape J C] (k : K) : Preserv
esLimitsOfShape J ((evaluation K C).obj k) where preservesLimit
参数：k : K。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
instance evaluation_preservesLimitsOfShape [HasLimitsOfShape J C] (k : K) :
    PreservesLimitsOfShape J ((evaluation K C).obj k) where
  preservesLimit := inferInstance

/-- If `F : J ⥤ K ⥤ C` is a functor into a functor category which has a limit,
then the evaluation of that limit at `k` is the limit of the evaluations of `F.obj j` at `k`.
-/
/-
**CategoryTheory.Limits.limitObjIsoLimitCompEvaluation** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：limitObjIsoLimitCompEvaluation [HasLimitsOfShape J C] (F : J ⥤ K ⥤ C) (k :
 K) : (limit F).obj k ≅ limit (F ⋙ (evaluation K C).obj k)
参数：F : J ⥤ K ⥤ C；k : K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : J ⥤ K ⥤ C` is a functor into a functor category which has a limit,
then the evaluation of that limit at `k` is the limit of the evaluations of `F.o
bj j` at `k`.
-/
def limitObjIsoLimitCompEvaluation [HasLimitsOfShape J C] (F : J ⥤ K ⥤ C) (k : K) :
    (limit F).obj k ≅ limit (F ⋙ (evaluation K C).obj k) :=
  preservesLimitIso ((evaluation K C).obj k) F

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.limitObjIsoLimitCompEvaluation_hom_** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem limitObjIsoLimitCompEvaluation_hom_π [HasLimitsOfShape J C] (F : J ⥤ K ⥤ C) (j : J)
    (k : K) :
    (limitObjIsoLimitCompEvaluation F k).hom ≫ limit.π (F ⋙ (evaluation K C).obj k) j =
      (limit.π F j).app k := by
  dsimp [limitObjIsoLimitCompEvaluation]
  simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.limitObjIsoLimitCompEvaluation_inv_** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem limitObjIsoLimitCompEvaluation_inv_π_app [HasLimitsOfShape J C] (F : J ⥤ K ⥤ C) (j : J)
    (k : K) :
    (limitObjIsoLimitCompEvaluation F k).inv ≫ (limit.π F j).app k =
      limit.π (F ⋙ (evaluation K C).obj k) j := by
  dsimp [limitObjIsoLimitCompEvaluation]
  rw [Iso.inv_comp_eq]
  simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.limit_map_limitObjIsoLimitCompEvaluation_hom** 是 Mathlib
 中的一个定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：limit_map_limitObjIsoLimitCompEvaluation_hom [HasLimitsOfShape J C] {i j :
 K} (F : J ⥤ K ⥤ C) (f : i ⟶ j) : (limit F).map f ≫ (limitObjIsoLimitCompEvaluat
ion _ _).hom = (limitObjIsoLimitCompEvaluation _ _).hom ≫ limMap (whiskerLeft _ 
((evaluation _ _).map f))
参数：F : J ⥤ K ⥤ C；f : i ⟶ j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.limit.hom_ext`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.instHasLimitCompOfPreservesLimit`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.limitObjIsoLimitCompEvaluation_hom_π`：limitObjIsoL
imitCompEvaluation_hom_π [HasLimitsOfShape J C] (F : J ⥤ K ⥤ C) (j : J) (k : K) 
: (limitObjIsoLimitCompEvaluation F k).hom ≫ lim…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Limits.limMap_π`：limMap_π {F G : J ⥤ C} [HasLimit F] [Has
Limit G] (α : F ⟶ G) (j : J) : limMap α ≫ limit.π G j = limit.π F j ≫ α.app j
· 使用定理 `CategoryTheory.Limits.limitObjIsoLimitCompEvaluation_hom_π_assoc`：∀ {C :
 Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : Categ
oryTheory.Category.{v₁, u₁} J]   {K : Type u₂} [inst_2…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem limit_map_limitObjIsoLimitCompEvaluation_hom [HasLimitsOfShape J C] {i j : K}
    (F : J ⥤ K ⥤ C) (f : i ⟶ j) : (limit F).map f ≫ (limitObjIsoLimitCompEvaluation _ _).hom =
    (limitObjIsoLimitCompEvaluation _ _).hom ≫ limMap (whiskerLeft _ ((evaluation _ _).map f)) := by
  ext
  simp

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.limitObjIsoLimitCompEvaluation_inv_limit_map** 是 Mathlib
 中的一个定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：limitObjIsoLimitCompEvaluation_inv_limit_map [HasLimitsOfShape J C] {i j :
 K} (F : J ⥤ K ⥤ C) (f : i ⟶ j) : (limitObjIsoLimitCompEvaluation _ _).inv ≫ (li
mit F).map f = limMap (whiskerLeft _ ((evaluation _ _).map f)) ≫ (limitObjIsoLim
itCompEvaluation _ _).inv
参数：F : J ⥤ K ⥤ C；f : i ⟶ j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitCompOfPreservesLimit`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.inv_comp_eq`：inv_comp_eq (α : X ≅ Y) {f : X ⟶ Z} {g :
 Y ⟶ Z} : α.inv ≫ f = g ↔ f = α.hom ≫ g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.eq_comp_inv`：eq_comp_inv (α : X ≅ Y) {f : Z ⟶ Y} {g :
 Z ⟶ X} : g = f ≫ α.inv ↔ g ≫ α.hom = f
· 使用定理 `CategoryTheory.Limits.limit_map_limitObjIsoLimitCompEvaluation_hom`：limi
t_map_limitObjIsoLimitCompEvaluation_hom [HasLimitsOfShape J C] {i j : K} (F : J
 ⥤ K ⥤ C) (f : i ⟶ j) : (limit F).map f ≫ (limitObjIsoLi…
-/
theorem limitObjIsoLimitCompEvaluation_inv_limit_map [HasLimitsOfShape J C] {i j : K}
    (F : J ⥤ K ⥤ C) (f : i ⟶ j) : (limitObjIsoLimitCompEvaluation _ _).inv ≫ (limit F).map f =
    limMap (whiskerLeft _ ((evaluation _ _).map f)) ≫ (limitObjIsoLimitCompEvaluation _ _).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv,
    limit_map_limitObjIsoLimitCompEvaluation_hom]

set_option backward.isDefEq.respectTransparency false in
@[ext]
/-
**CategoryTheory.Limits.limit_obj_ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Limits`。
形式化陈述：limit_obj_ext {H : J ⥤ K ⥤ C} [HasLimitsOfShape J C] {k : K} {W : C} {f g 
: W ⟶ (limit H).obj k} (w : forall j, f ≫ (Limits.limit.π H j).app k = g ≫ (Limi
ts.limit.π H j).app k) : f = g
参数：limit H；w : forall j, f ≫ (Limits.limit.π H j).app k = g ≫ (Limits.limit.π H 
j).app k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Limits.instHasLimitCompOfPreservesLimit`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.strongMono_of_isIso`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {P Q : C} (f : Q ⟶ P) [CategoryTheory.IsIso f],   CategoryT
heory.StrongMono f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Limits.limit.hom_ext`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.limitObjIsoLimitCompEvaluation_hom_π`：limitObjIsoL
imitCompEvaluation_hom_π [HasLimitsOfShape J C] (F : J ⥤ K ⥤ C) (j : J) (k : K) 
: (limitObjIsoLimitCompEvaluation F k).hom ≫ lim…
-/
theorem limit_obj_ext {H : J ⥤ K ⥤ C} [HasLimitsOfShape J C] {k : K} {W : C}
    {f g : W ⟶ (limit H).obj k}
    (w : ∀ j, f ≫ (Limits.limit.π H j).app k = g ≫ (Limits.limit.π H j).app k) : f = g := by
  apply (cancel_mono (limitObjIsoLimitCompEvaluation H k).hom).1
  ext j
  simpa using w j

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Taking a limit after whiskering by `G` is the same as using `G` and then taking a limit. -/
/-
**CategoryTheory.Limits.limitCompWhiskeringLeftIsoCompLimit** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.Limits`。
形式化陈述：limitCompWhiskeringLeftIsoCompLimit (F : J ⥤ K ⥤ C) (G : D ⥤ K) [HasLimits
OfShape J C] : limit (F ⋙ (whiskeringLeft _ _ _).obj G) ≅ G ⋙ limit F
参数：F : J ⥤ K ⥤ C；G : D ⥤ K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Taking a limit after whiskering by `G` is the same as using `G` and then taking 
a limit.
-/
def limitCompWhiskeringLeftIsoCompLimit (F : J ⥤ K ⥤ C) (G : D ⥤ K) [HasLimitsOfShape J C] :
    limit (F ⋙ (whiskeringLeft _ _ _).obj G) ≅ G ⋙ limit F :=
  NatIso.ofComponents (fun j =>
    limitObjIsoLimitCompEvaluation (F ⋙ (whiskeringLeft _ _ _).obj G) j ≪≫
      HasLimit.isoOfNatIso (isoWhiskerLeft F (whiskeringLeftCompEvaluation G j)) ≪≫
      (limitObjIsoLimitCompEvaluation F (G.obj j)).symm)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.limitCompWhiskeringLeftIsoCompLimit_hom_whiskerLeft_** 是
 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem limitCompWhiskeringLeftIsoCompLimit_hom_whiskerLeft_π (F : J ⥤ K ⥤ C) (G : D ⥤ K)
    [HasLimitsOfShape J C] (j : J) :
    (limitCompWhiskeringLeftIsoCompLimit F G).hom ≫ whiskerLeft G (limit.π F j) =
      limit.π (F ⋙ (whiskeringLeft _ _ _).obj G) j := by
  ext d
  simp [limitCompWhiskeringLeftIsoCompLimit]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.limitCompWhiskeringLeftIsoCompLimit_inv_** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem limitCompWhiskeringLeftIsoCompLimit_inv_π (F : J ⥤ K ⥤ C) (G : D ⥤ K)
    [HasLimitsOfShape J C] (j : J) :
    (limitCompWhiskeringLeftIsoCompLimit F G).inv ≫ limit.π (F ⋙ (whiskeringLeft _ _ _).obj G) j =
      whiskerLeft G (limit.π F j) := by
  simp [Iso.inv_comp_eq]
/-
**CategoryTheory.Limits.hasColimitCompEvaluation** 是 Mathlib 中的一个实例，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：hasColimitCompEvaluation (F : J ⥤ K ⥤ C) (k : K) [HasColimit (F.flip.obj k
)] : HasColimit (F ⋙ (evaluation _ _).obj k)
参数：F : J ⥤ K ⥤ C；k : K；F.flip.obj k。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasColimit_of_iso`：hasColimit_of_iso {F G : J ⥤ C}
 [HasColimit F] (α : G ≅ F) : HasColimit G
-/
instance hasColimitCompEvaluation (F : J ⥤ K ⥤ C) (k : K) [HasColimit (F.flip.obj k)] :
    HasColimit (F ⋙ (evaluation _ _).obj k) :=
  hasColimit_of_iso (F := F.flip.obj k) (Iso.refl _)
/-
**CategoryTheory.Limits.evaluation_preservesColimit** 是 Mathlib 中的一个实例，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：evaluation_preservesColimit (F : J ⥤ K ⥤ C) [forall k, HasColimit (F.flip.
obj k)] (k : K) : PreservesColimit F ((evaluation K C).obj k)
参数：F : J ⥤ K ⥤ C；F.flip.obj k；k : K。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimit_of_preserves_colimit_cocone`：pres
ervesColimit_of_preserves_colimit_cocone {F : C ⥤ D} {t : Cocone K} (h : IsColim
it t) (hF : IsColimit (F.mapCocone t)) : PreservesColimi…
-/
instance evaluation_preservesColimit (F : J ⥤ K ⥤ C) [∀ k, HasColimit (F.flip.obj k)] (k : K) :
    PreservesColimit F ((evaluation K C).obj k) :=
  -- Porting note: added a let because X was not inferred
  let X : (k : K) → ColimitCocone (F.flip.obj k) := fun k => getColimitCocone (F.flip.obj k)
  preservesColimit_of_preserves_colimit_cocone (combinedIsColimit _ X) <|
    IsColimit.ofIsoColimit (colimit.isColimit _) (evaluateCombinedCocones F X k).symm
/-
**CategoryTheory.Limits.evaluation_preservesColimitsOfShape** 是 Mathlib 中的一个实例，位
于命名空间 `CategoryTheory.Limits`。
形式化陈述：evaluation_preservesColimitsOfShape [HasColimitsOfShape J C] (k : K) : Pre
servesColimitsOfShape J ((evaluation K C).obj k) where preservesColimit
参数：k : K。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
instance evaluation_preservesColimitsOfShape [HasColimitsOfShape J C] (k : K) :
    PreservesColimitsOfShape J ((evaluation K C).obj k) where
  preservesColimit := inferInstance

/-- If `F : J ⥤ K ⥤ C` is a functor into a functor category which has a colimit,
then the evaluation of that colimit at `k` is the colimit of the evaluations of `F.obj j` at `k`.
-/
/-
**CategoryTheory.Limits.colimitObjIsoColimitCompEvaluation** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.Limits`。
形式化陈述：colimitObjIsoColimitCompEvaluation [HasColimitsOfShape J C] (F : J ⥤ K ⥤ C
) (k : K) : (colimit F).obj k ≅ colimit (F ⋙ (evaluation K C).obj k)
参数：F : J ⥤ K ⥤ C；k : K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F : J ⥤ K ⥤ C` is a functor into a functor category which has a colimit,
then the evaluation of that colimit at `k` is the colimit of the evaluations of 
`F.obj j` at `k`.
-/
def colimitObjIsoColimitCompEvaluation [HasColimitsOfShape J C] (F : J ⥤ K ⥤ C) (k : K) :
    (colimit F).obj k ≅ colimit (F ⋙ (evaluation K C).obj k) :=
  preservesColimitIso ((evaluation K C).obj k) F

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.colimitObjIsoColimitCompEvaluation_** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem colimitObjIsoColimitCompEvaluation_ι_inv [HasColimitsOfShape J C] (F : J ⥤ K ⥤ C) (j : J)
    (k : K) :
    colimit.ι (F ⋙ (evaluation K C).obj k) j ≫ (colimitObjIsoColimitCompEvaluation F k).inv =
      (colimit.ι F j).app k := by
  dsimp [colimitObjIsoColimitCompEvaluation]
  simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.colimitObjIsoColimitCompEvaluation_** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem colimitObjIsoColimitCompEvaluation_ι_app_hom [HasColimitsOfShape J C] (F : J ⥤ K ⥤ C)
    (j : J) (k : K) :
    (colimit.ι F j).app k ≫ (colimitObjIsoColimitCompEvaluation F k).hom =
      colimit.ι (F ⋙ (evaluation K C).obj k) j := by
  dsimp [colimitObjIsoColimitCompEvaluation]
  rw [← Iso.eq_comp_inv]
  simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.colimitObjIsoColimitCompEvaluation_inv_colimit_map** 是 M
athlib 中的一个定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：colimitObjIsoColimitCompEvaluation_inv_colimit_map [HasColimitsOfShape J C
] (F : J ⥤ K ⥤ C) {i j : K} (f : i ⟶ j) : (colimitObjIsoColimitCompEvaluation _ 
_).inv ≫ (colimit F).map f = colimMap (whiskerLeft _ ((evaluation _ _).map f)) ≫
 (colimitObjIsoColimitCompEvaluation _ _).inv
参数：F : J ⥤ K ⥤ C；f : i ⟶ j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.colimit.hom_ext`：∀ {J : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u}
 C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.colimitObjIsoColimitCompEvaluation_ι_inv_assoc`：∀ 
{C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : C
ategoryTheory.Category.{v₁, u₁} J]   {K : Type u₂} [inst_2…
· 使用定理 `CategoryTheory.Limits.ι_colimMap_assoc`：∀ {J : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u
} C]   {F G : CategoryTheory…
· 使用定理 `CategoryTheory.Limits.colimitObjIsoColimitCompEvaluation_ι_inv`：colimitO
bjIsoColimitCompEvaluation_ι_inv [HasColimitsOfShape J C] (F : J ⥤ K ⥤ C) (j : J
) (k : K) : colimit.ι (F ⋙ (evaluation K C).obj k) j…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem colimitObjIsoColimitCompEvaluation_inv_colimit_map [HasColimitsOfShape J C] (F : J ⥤ K ⥤ C)
    {i j : K} (f : i ⟶ j) :
    (colimitObjIsoColimitCompEvaluation _ _).inv ≫ (colimit F).map f =
      colimMap (whiskerLeft _ ((evaluation _ _).map f)) ≫
        (colimitObjIsoColimitCompEvaluation _ _).inv := by
  ext
  simp

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.colimit_map_colimitObjIsoColimitCompEvaluation_hom** 是 M
athlib 中的一个定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：colimit_map_colimitObjIsoColimitCompEvaluation_hom [HasColimitsOfShape J C
] (F : J ⥤ K ⥤ C) {i j : K} (f : i ⟶ j) : (colimit F).map f ≫ (colimitObjIsoColi
mitCompEvaluation _ _).hom = (colimitObjIsoColimitCompEvaluation _ _).hom ≫ coli
mMap (whiskerLeft _ ((evaluation _ _).map f))
参数：F : J ⥤ K ⥤ C；f : i ⟶ j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Iso.inv_comp_eq`：inv_comp_eq (α : X ≅ Y) {f : X ⟶ Z} {g :
 Y ⟶ Z} : α.inv ≫ f = g ↔ f = α.hom ≫ g
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.eq_comp_inv`：eq_comp_inv (α : X ≅ Y) {f : Z ⟶ Y} {g :
 Z ⟶ X} : g = f ≫ α.inv ↔ g ≫ α.hom = f
· 使用定理 `CategoryTheory.Limits.colimitObjIsoColimitCompEvaluation_inv_colimit_map
`：colimitObjIsoColimitCompEvaluation_inv_colimit_map [HasColimitsOfShape J C] (F
 : J ⥤ K ⥤ C) {i j : K} (f : i ⟶ j) : (colimitObjIsoColimitCom…
-/
theorem colimit_map_colimitObjIsoColimitCompEvaluation_hom [HasColimitsOfShape J C] (F : J ⥤ K ⥤ C)
    {i j : K} (f : i ⟶ j) :
    (colimit F).map f ≫ (colimitObjIsoColimitCompEvaluation _ _).hom =
      (colimitObjIsoColimitCompEvaluation _ _).hom ≫
        colimMap (whiskerLeft _ ((evaluation _ _).map f)) := by
  rw [← Iso.inv_comp_eq, ← Category.assoc, ← Iso.eq_comp_inv,
    colimitObjIsoColimitCompEvaluation_inv_colimit_map]

set_option backward.isDefEq.respectTransparency false in
@[ext]
/-
**CategoryTheory.Limits.colimit_obj_ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits`。
形式化陈述：colimit_obj_ext {H : J ⥤ K ⥤ C} [HasColimitsOfShape J C] {k : K} {W : C} {
f g : (colimit H).obj k ⟶ W} (w : forall j, (colimit.ι H j).app k ≫ f = (colimit
.ι H j).app k ≫ g) : f = g
参数：colimit H；w : forall j, (colimit.ι H j).app k ≫ f = (colimit.ι H j).app k ≫ g
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.Limits.colimit.hom_ext`：∀ {J : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u}
 C]   {F : CategoryTheory.F…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.colimitObjIsoColimitCompEvaluation_ι_inv_assoc`：∀ 
{C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : C
ategoryTheory.Category.{v₁, u₁} J]   {K : Type u₂} [inst_2…
-/
theorem colimit_obj_ext {H : J ⥤ K ⥤ C} [HasColimitsOfShape J C] {k : K} {W : C}
    {f g : (colimit H).obj k ⟶ W} (w : ∀ j, (colimit.ι H j).app k ≫ f = (colimit.ι H j).app k ≫ g) :
    f = g := by
  apply (cancel_epi (colimitObjIsoColimitCompEvaluation H k).inv).1
  ext j
  simpa using w j

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Taking a colimit after whiskering by `G` is the same as using `G` and then taking a colimit. -/
/-
**CategoryTheory.Limits.colimitCompWhiskeringLeftIsoCompColimit** 是 Mathlib 中的一个
定义，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：colimitCompWhiskeringLeftIsoCompColimit (F : J ⥤ K ⥤ C) (G : D ⥤ K) [HasCo
limitsOfShape J C] : colimit (F ⋙ (whiskeringLeft _ _ _).obj G) ≅ G ⋙ colimit F
参数：F : J ⥤ K ⥤ C；G : D ⥤ K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Taking a colimit after whiskering by `G` is the same as using `G` and then takin
g a colimit.
-/
def colimitCompWhiskeringLeftIsoCompColimit (F : J ⥤ K ⥤ C) (G : D ⥤ K) [HasColimitsOfShape J C] :
    colimit (F ⋙ (whiskeringLeft _ _ _).obj G) ≅ G ⋙ colimit F :=
  NatIso.ofComponents (fun j =>
    colimitObjIsoColimitCompEvaluation (F ⋙ (whiskeringLeft _ _ _).obj G) j ≪≫
      HasColimit.isoOfNatIso (isoWhiskerLeft F (whiskeringLeftCompEvaluation G j)) ≪≫
      (colimitObjIsoColimitCompEvaluation F (G.obj j)).symm)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_colimitCompWhiskeringLeftIsoCompColimit_hom (F : J ⥤ K ⥤ C) (G : D ⥤ K)
    [HasColimitsOfShape J C] (j : J) :
    colimit.ι (F ⋙ (whiskeringLeft _ _ _).obj G) j ≫
      (colimitCompWhiskeringLeftIsoCompColimit F G).hom = whiskerLeft G (colimit.ι F j) := by
  ext d
  simp [colimitCompWhiskeringLeftIsoCompColimit]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.whiskerLeft_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.L
imits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem whiskerLeft_ι_colimitCompWhiskeringLeftIsoCompColimit_inv (F : J ⥤ K ⥤ C) (G : D ⥤ K)
    [HasColimitsOfShape J C] (j : J) :
    whiskerLeft G (colimit.ι F j) ≫ (colimitCompWhiskeringLeftIsoCompColimit F G).inv =
      colimit.ι (F ⋙ (whiskeringLeft _ _ _).obj G) j := by
  simp [Iso.comp_inv_eq]
/-
**CategoryTheory.Limits.evaluationPreservesLimits** 是 Mathlib 中的一个实例，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：evaluationPreservesLimits [HasLimits C] (k : K) : PreservesLimits ((evalua
tion K C).obj k) where preservesLimitsOfShape {_} _𝒥
参数：k : K。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitsOfShapeOfHasLimitsOfSize`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTh
eory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
instance evaluationPreservesLimits [HasLimits C] (k : K) :
    PreservesLimits ((evaluation K C).obj k) where
  preservesLimitsOfShape {_} _𝒥 := inferInstance

/-- `F : D ⥤ K ⥤ C` preserves the limit of some `G : J ⥤ D` if it does for each `k : K`. -/
/-
**CategoryTheory.Limits.preservesLimit_of_evaluation** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：preservesLimit_of_evaluation (F : D ⥤ K ⥤ C) (G : J ⥤ D) (H : forall k : K
, PreservesLimit G (F ⋙ (evaluation K C).obj k : D ⥤ C)) : PreservesLimit G F
参数：F : D ⥤ K ⥤ C；G : J ⥤ D；H : forall k : K, PreservesLimit G (F ⋙ (evaluation K
 C).obj k : D ⥤ C)。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`F : D ⥤ K ⥤ C` preserves the limit of some `G : J ⥤ D` if it does for each `k :
 K`.
-/
lemma preservesLimit_of_evaluation (F : D ⥤ K ⥤ C) (G : J ⥤ D)
    (H : ∀ k : K, PreservesLimit G (F ⋙ (evaluation K C).obj k : D ⥤ C)) : PreservesLimit G F :=
  ⟨fun {c} hc => ⟨by
    apply evaluationJointlyReflectsLimits
    intro X
    haveI := H X
    change IsLimit ((F ⋙ (evaluation K C).obj X).mapCone c)
    exact isLimitOfPreserves _ hc⟩⟩

/-- `F : D ⥤ K ⥤ C` preserves limits of shape `J` if it does for each `k : K`. -/
/-
**CategoryTheory.Limits.preservesLimitsOfShape_of_evaluation** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesLimitsOfShape_of_evaluation (F : D ⥤ K ⥤ C) (J : Type*) [Category
* J] (_ : forall k : K, PreservesLimitsOfShape J (F ⋙ (evaluation K C).obj k)) :
 PreservesLimitsOfShape J F
参数：F : D ⥤ K ⥤ C；J : Type*；_ : forall k : K, PreservesLimitsOfShape J (F ⋙ (eval
uation K C).obj k)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_evaluation`：preservesLimit_of_ev
aluation (F : D ⥤ K ⥤ C) (G : J ⥤ D) (H : forall k : K, PreservesLimit G (F ⋙ (e
valuation K C).obj k : D ⥤ C)) : Preserv…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…

--- 原说明 ---
`F : D ⥤ K ⥤ C` preserves limits of shape `J` if it does for each `k : K`.
-/
lemma preservesLimitsOfShape_of_evaluation (F : D ⥤ K ⥤ C) (J : Type*) [Category* J]
    (_ : ∀ k : K, PreservesLimitsOfShape J (F ⋙ (evaluation K C).obj k)) :
    PreservesLimitsOfShape J F :=
  ⟨fun {G} => preservesLimit_of_evaluation F G fun _ => PreservesLimitsOfShape.preservesLimit⟩

/-- `F : D ⥤ K ⥤ C` preserves all limits if it does for each `k : K`. -/
/-
**CategoryTheory.Limits.preservesLimits_of_evaluation** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：preservesLimits_of_evaluation (F : D ⥤ K ⥤ C) (_ : forall k : K, Preserves
LimitsOfSize.{w', w} (F ⋙ (evaluation K C).obj k)) : PreservesLimitsOfSize.{w', 
w} F
参数：F : D ⥤ K ⥤ C；_ : forall k : K, PreservesLimitsOfSize.{w', w} (F ⋙ (evaluatio
n K C).obj k)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimitsOfShape_of_evaluation`：preservesLim
itsOfShape_of_evaluation (F : D ⥤ K ⥤ C) (J : Type*) [Category* J] (_ : forall k
 : K, PreservesLimitsOfShape J (F ⋙ (evaluation …
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfSize.preservesLimitsOfShape`：∀ {C
 : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : 
CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
`F : D ⥤ K ⥤ C` preserves all limits if it does for each `k : K`.
-/
lemma preservesLimits_of_evaluation (F : D ⥤ K ⥤ C)
    (_ : ∀ k : K, PreservesLimitsOfSize.{w', w} (F ⋙ (evaluation K C).obj k)) :
    PreservesLimitsOfSize.{w', w} F :=
  ⟨fun {L} _ =>
    preservesLimitsOfShape_of_evaluation F L fun _ => PreservesLimitsOfSize.preservesLimitsOfShape⟩

/-- The constant functor `C ⥤ (D ⥤ C)` preserves limits. -/
/-
**CategoryTheory.Limits.preservesLimits_const** 是 Mathlib 中的一个实例，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：preservesLimits_const : PreservesLimitsOfSize.{w', w} (const D : C ⥤ _)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimits_of_evaluation`：preservesLimits_of_
evaluation (F : D ⥤ K ⥤ C) (_ : forall k : K, PreservesLimitsOfSize.{w', w} (F ⋙
 (evaluation K C).obj k)) : PreservesLimi…
· 使用引理 `CategoryTheory.Limits.preservesLimits_of_natIso`：preservesLimits_of_natI
so {F G : C ⥤ D} (h : F ≅ G) [PreservesLimitsOfSize.{w, w'} F] : PreservesLimits
OfSize.{w, w'} G where preservesLimit…

--- 原说明 ---
The constant functor `C ⥤ (D ⥤ C)` preserves limits.
-/
instance preservesLimits_const : PreservesLimitsOfSize.{w', w} (const D : C ⥤ _) :=
  preservesLimits_of_evaluation _ fun _ =>
    preservesLimits_of_natIso <| Iso.symm <| constCompEvaluationObj _ _
/-
**CategoryTheory.Limits.evaluation_preservesColimits** 是 Mathlib 中的一个实例，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：evaluation_preservesColimits [HasColimits C] (k : K) : PreservesColimits (
(evaluation K C).obj k) where preservesColimitsOfShape
参数：k : K。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitsOfShapeOfHasColimitsOfSize`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : Catego
ryTheory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
instance evaluation_preservesColimits [HasColimits C] (k : K) :
    PreservesColimits ((evaluation K C).obj k) where
  preservesColimitsOfShape := inferInstance

/-- `F : D ⥤ K ⥤ C` preserves the colimit of some `G : J ⥤ D` if it does for each `k : K`. -/
/-
**CategoryTheory.Limits.preservesColimit_of_evaluation** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：preservesColimit_of_evaluation (F : D ⥤ K ⥤ C) (G : J ⥤ D) (H : forall k, 
PreservesColimit G (F ⋙ (evaluation K C).obj k)) : PreservesColimit G F
参数：F : D ⥤ K ⥤ C；G : J ⥤ D；H : forall k, PreservesColimit G (F ⋙ (evaluation K C
).obj k)。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`F : D ⥤ K ⥤ C` preserves the colimit of some `G : J ⥤ D` if it does for each `k
 : K`.
-/
lemma preservesColimit_of_evaluation (F : D ⥤ K ⥤ C) (G : J ⥤ D)
    (H : ∀ k, PreservesColimit G (F ⋙ (evaluation K C).obj k)) : PreservesColimit G F :=
  ⟨fun {c} hc => ⟨by
    apply evaluationJointlyReflectsColimits
    intro X
    haveI := H X
    change IsColimit ((F ⋙ (evaluation K C).obj X).mapCocone c)
    exact isColimitOfPreserves _ hc⟩⟩

/-- `F : D ⥤ K ⥤ C` preserves all colimits of shape `J` if it does for each `k : K`. -/
/-
**CategoryTheory.Limits.preservesColimitsOfShape_of_evaluation** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesColimitsOfShape_of_evaluation (F : D ⥤ K ⥤ C) (J : Type*) [Catego
ry* J] (_ : forall k : K, PreservesColimitsOfShape J (F ⋙ (evaluation K C).obj k
)) : PreservesColimitsOfShape J F
参数：F : D ⥤ K ⥤ C；J : Type*；_ : forall k : K, PreservesColimitsOfShape J (F ⋙ (ev
aluation K C).obj k)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimit_of_evaluation`：preservesColimit_o
f_evaluation (F : D ⥤ K ⥤ C) (G : J ⥤ D) (H : forall k, PreservesColimit G (F ⋙ 
(evaluation K C).obj k)) : PreservesColimi…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…

--- 原说明 ---
`F : D ⥤ K ⥤ C` preserves all colimits of shape `J` if it does for each `k : K`.
-/
lemma preservesColimitsOfShape_of_evaluation (F : D ⥤ K ⥤ C) (J : Type*) [Category* J]
    (_ : ∀ k : K, PreservesColimitsOfShape J (F ⋙ (evaluation K C).obj k)) :
    PreservesColimitsOfShape J F :=
  ⟨fun {G} => preservesColimit_of_evaluation F G fun _ => PreservesColimitsOfShape.preservesColimit⟩

/-- `F : D ⥤ K ⥤ C` preserves all colimits if it does for each `k : K`. -/
/-
**CategoryTheory.Limits.preservesColimits_of_evaluation** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Limits`。
形式化陈述：preservesColimits_of_evaluation (F : D ⥤ K ⥤ C) (_ : forall k : K, Preserv
esColimitsOfSize.{w', w} (F ⋙ (evaluation K C).obj k)) : PreservesColimitsOfSize
.{w', w} F
参数：F : D ⥤ K ⥤ C；_ : forall k : K, PreservesColimitsOfSize.{w', w} (F ⋙ (evaluat
ion K C).obj k)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimitsOfShape_of_evaluation`：preservesC
olimitsOfShape_of_evaluation (F : D ⥤ K ⥤ C) (J : Type*) [Category* J] (_ : fora
ll k : K, PreservesColimitsOfShape J (F ⋙ (evaluat…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfSize.preservesColimitsOfShape`：
∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_
1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
`F : D ⥤ K ⥤ C` preserves all colimits if it does for each `k : K`.
-/
lemma preservesColimits_of_evaluation (F : D ⥤ K ⥤ C)
    (_ : ∀ k : K, PreservesColimitsOfSize.{w', w} (F ⋙ (evaluation K C).obj k)) :
    PreservesColimitsOfSize.{w', w} F :=
  ⟨fun {L} _ =>
    preservesColimitsOfShape_of_evaluation F L fun _ =>
      PreservesColimitsOfSize.preservesColimitsOfShape⟩

/-- The constant functor `C ⥤ (D ⥤ C)` preserves colimits. -/
/-
**CategoryTheory.Limits.preservesColimits_const** 是 Mathlib 中的一个实例，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：preservesColimits_const : PreservesColimitsOfSize.{w', w} (const D : C ⥤ _
)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimits_of_evaluation`：preservesColimits
_of_evaluation (F : D ⥤ K ⥤ C) (_ : forall k : K, PreservesColimitsOfSize.{w', w
} (F ⋙ (evaluation K C).obj k)) : Preserves…
· 使用引理 `CategoryTheory.Limits.preservesColimits_of_natIso`：preservesColimits_of_
natIso {F G : C ⥤ D} (h : F ≅ G) [PreservesColimitsOfSize.{w, w'} F] : Preserves
ColimitsOfSize.{w, w'} G where preserve…

--- 原说明 ---
The constant functor `C ⥤ (D ⥤ C)` preserves colimits.
-/
instance preservesColimits_const : PreservesColimitsOfSize.{w', w} (const D : C ⥤ _) :=
  preservesColimits_of_evaluation _ fun _ =>
    preservesColimits_of_natIso <| Iso.symm <| constCompEvaluationObj _ _

open CategoryTheory.prod

set_option backward.isDefEq.respectTransparency false in
/-- The limit of a diagram `F : J ⥤ K ⥤ C` is isomorphic to the functor given by
the individual limits on objects. -/
@[simps!]
/-
**CategoryTheory.Limits.limitIsoFlipCompLim** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：limitIsoFlipCompLim [HasLimitsOfShape J C] (F : J ⥤ K ⥤ C) : limit F ≅ F.f
lip ⋙ lim
参数：F : J ⥤ K ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The limit of a diagram `F : J ⥤ K ⥤ C` is isomorphic to the functor given by
the individual limits on objects.
-/
def limitIsoFlipCompLim [HasLimitsOfShape J C] (F : J ⥤ K ⥤ C) : limit F ≅ F.flip ⋙ lim :=
  NatIso.ofComponents (limitObjIsoLimitCompEvaluation F)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `limitIsoFlipCompLim` is natural with respect to diagrams. -/
@[simps!]
/-
**CategoryTheory.Limits.limIsoFlipCompWhiskerLim** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：limIsoFlipCompWhiskerLim [HasLimitsOfShape J C] : lim ≅ flipFunctor J K C 
⋙ (whiskeringRight _ _ _).obj lim
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`limitIsoFlipCompLim` is natural with respect to diagrams.
-/
def limIsoFlipCompWhiskerLim [HasLimitsOfShape J C] :
    lim ≅ flipFunctor J K C ⋙ (whiskeringRight _ _ _).obj lim :=
  (NatIso.ofComponents (limitIsoFlipCompLim · |>.symm) fun {F G} η ↦ by
    ext k
    apply limit_obj_ext
    intro j
    simp [comp_evaluation, ← NatTrans.comp_app (limMap η)]).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A variant of `limitIsoFlipCompLim` where the arguments of `F` are flipped. -/
@[simps!]
/-
**CategoryTheory.Limits.limitFlipIsoCompLim** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：limitFlipIsoCompLim [HasLimitsOfShape J C] (F : K ⥤ J ⥤ C) : limit F.flip 
≅ F ⋙ lim
参数：F : K ⥤ J ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A variant of `limitIsoFlipCompLim` where the arguments of `F` are flipped.
-/
def limitFlipIsoCompLim [HasLimitsOfShape J C] (F : K ⥤ J ⥤ C) : limit F.flip ≅ F ⋙ lim :=
  let f := fun k =>
    limitObjIsoLimitCompEvaluation F.flip k ≪≫ HasLimit.isoOfNatIso (flipCompEvaluation _ _)
  NatIso.ofComponents f

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `limitFlipIsoCompLim` is natural with respect to diagrams. -/
@[simps!]
/-
**CategoryTheory.Limits.limCompFlipIsoWhiskerLim** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：limCompFlipIsoWhiskerLim [HasLimitsOfShape J C] : flipFunctor K J C ⋙ lim 
≅ (whiskeringRight _ _ _).obj lim
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`limitFlipIsoCompLim` is natural with respect to diagrams.
-/
def limCompFlipIsoWhiskerLim [HasLimitsOfShape J C] :
    flipFunctor K J C ⋙ lim ≅ (whiskeringRight _ _ _).obj lim :=
  (NatIso.ofComponents (limitFlipIsoCompLim · |>.symm) fun {F G} η ↦ by
    ext k
    apply limit_obj_ext
    intro j
    simp [comp_evaluation, ← NatTrans.comp_app (limMap _)]).symm

/-- For a functor `G : J ⥤ K ⥤ C`, its limit `K ⥤ C` is given by `(G' : K ⥤ J ⥤ C) ⋙ lim`.
Note that this does not require `K` to be small.
-/
@[simps!]
/-
**CategoryTheory.Limits.limitIsoSwapCompLim** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：limitIsoSwapCompLim [HasLimitsOfShape J C] (G : J ⥤ K ⥤ C) : limit G ≅ cur
ry.obj (Prod.swap K J ⋙ uncurry.obj G) ⋙ lim
参数：G : J ⥤ K ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a functor `G : J ⥤ K ⥤ C`, its limit `K ⥤ C` is given by `(G' : K ⥤ J ⥤ C) ⋙
 lim`.
Note that this does not require `K` to be small.
-/
def limitIsoSwapCompLim [HasLimitsOfShape J C] (G : J ⥤ K ⥤ C) :
    limit G ≅ curry.obj (Prod.swap K J ⋙ uncurry.obj G) ⋙ lim :=
  limitIsoFlipCompLim G ≪≫ isoWhiskerRight (flipIsoCurrySwapUncurry _) _

set_option backward.isDefEq.respectTransparency false in
/-- The colimit of a diagram `F : J ⥤ K ⥤ C` is isomorphic to the functor given by
the individual colimits on objects. -/
@[simps!]
/-
**CategoryTheory.Limits.colimitIsoFlipCompColim** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：colimitIsoFlipCompColim [HasColimitsOfShape J C] (F : J ⥤ K ⥤ C) : colimit
 F ≅ F.flip ⋙ colim
参数：F : J ⥤ K ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The colimit of a diagram `F : J ⥤ K ⥤ C` is isomorphic to the functor given by
the individual colimits on objects.
-/
def colimitIsoFlipCompColim [HasColimitsOfShape J C] (F : J ⥤ K ⥤ C) : colimit F ≅ F.flip ⋙ colim :=
  NatIso.ofComponents (colimitObjIsoColimitCompEvaluation F)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `colimitIsoFlipCompColim` is natural with respect to diagrams. -/
@[simps!]
/-
**CategoryTheory.Limits.colimIsoFlipCompWhiskerColim** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：colimIsoFlipCompWhiskerColim [HasColimitsOfShape J C] : colim ≅ flipFuncto
r J K C ⋙ (whiskeringRight _ _ _).obj colim
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`colimitIsoFlipCompColim` is natural with respect to diagrams.
-/
def colimIsoFlipCompWhiskerColim [HasColimitsOfShape J C] :
    colim ≅ flipFunctor J K C ⋙ (whiskeringRight _ _ _).obj colim :=
  NatIso.ofComponents colimitIsoFlipCompColim fun {F G} η ↦ by
    ext k
    apply colimit_obj_ext
    intro j
    simp [comp_evaluation, ← NatTrans.comp_app_assoc _ (colimMap η)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A variant of `colimitIsoFlipCompColim` where the arguments of `F` are flipped. -/
@[simps!]
/-
**CategoryTheory.Limits.colimitFlipIsoCompColim** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：colimitFlipIsoCompColim [HasColimitsOfShape J C] (F : K ⥤ J ⥤ C) : colimit
 F.flip ≅ F ⋙ colim
参数：F : K ⥤ J ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A variant of `colimitIsoFlipCompColim` where the arguments of `F` are flipped.
-/
def colimitFlipIsoCompColim [HasColimitsOfShape J C] (F : K ⥤ J ⥤ C) : colimit F.flip ≅ F ⋙ colim :=
  let f := fun _ =>
      colimitObjIsoColimitCompEvaluation _ _ ≪≫ HasColimit.isoOfNatIso (flipCompEvaluation _ _)
  NatIso.ofComponents f

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `colimitFlipIsoCompColim` is natural with respect to diagrams. -/
@[simps!]
/-
**CategoryTheory.Limits.colimCompFlipIsoWhiskerColim** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：colimCompFlipIsoWhiskerColim [HasColimitsOfShape J C] : flipFunctor K J C 
⋙ colim ≅ (whiskeringRight _ _ _).obj colim
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`colimitFlipIsoCompColim` is natural with respect to diagrams.
-/
def colimCompFlipIsoWhiskerColim [HasColimitsOfShape J C] :
    flipFunctor K J C ⋙ colim ≅ (whiskeringRight _ _ _).obj colim :=
  NatIso.ofComponents colimitFlipIsoCompColim fun {F G} η ↦ by
    ext k
    apply colimit_obj_ext
    intro j
    simp [comp_evaluation, ← NatTrans.comp_app_assoc _ (colimMap _)]

/-- For a functor `G : J ⥤ K ⥤ C`, its colimit `K ⥤ C` is given by `(G' : K ⥤ J ⥤ C) ⋙ colim`.
Note that this does not require `K` to be small.
-/
@[simps!]
/-
**CategoryTheory.Limits.colimitIsoSwapCompColim** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：colimitIsoSwapCompColim [HasColimitsOfShape J C] (G : J ⥤ K ⥤ C) : colimit
 G ≅ curry.obj (Prod.swap K J ⋙ uncurry.obj G) ⋙ colim
参数：G : J ⥤ K ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a functor `G : J ⥤ K ⥤ C`, its colimit `K ⥤ C` is given by `(G' : K ⥤ J ⥤ C)
 ⋙ colim`.
Note that this does not require `K` to be small.
-/
def colimitIsoSwapCompColim [HasColimitsOfShape J C] (G : J ⥤ K ⥤ C) :
    colimit G ≅ curry.obj (Prod.swap K J ⋙ uncurry.obj G) ⋙ colim :=
  colimitIsoFlipCompColim G ≪≫ isoWhiskerRight (flipIsoCurrySwapUncurry _) _

end

end Limits

end CategoryTheory

