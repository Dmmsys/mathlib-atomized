/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Reid Barton, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Creates.Opposites
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.IsConnected
public import Mathlib.CategoryTheory.Filtered.Final

/-!
# Connected limits in the over category

We show that the projection `CostructuredArrow K B ⥤ C` creates and preserves
connected limits, without assuming that `C` has any limits.
In particular, `CostructuredArrow K B` has any connected limit which `C` has.

From this we deduce the corresponding results for the over category.
-/

@[expose] public section

universe v' u' v u

-- morphism levels before object levels. See note [category theory universes].
noncomputable section

open CategoryTheory CategoryTheory.Limits

variable {J : Type u'} [Category.{v'} J]
variable {C : Type u} [Category.{v} C] {D : Type*} [Category* D] {K : C ⥤ D}
variable {X : C}

namespace CategoryTheory.CostructuredArrow

namespace CreatesConnected

set_option backward.defeqAttrib.useBackward true in
/-- (Implementation) Given a diagram in `CostructuredArrow K B`, produce a natural transformation
from the diagram legs to the specific object.
-/
@[simps]
/--
Definition of `natTransInCostructuredArrow` / `natTransInCostructuredArrow` 的定义

English:
definition natTransInCostructuredArrow
  signature: {B : D} (F : J ⥤ CostructuredArrow K B)
  body: (F.obj j).hom

中文:
定义 natTransInCostructuredArrow
  签名: {B : D} (F : J ⥤ CostructuredArrow K B)
  定义体: (F.obj j).hom

Depends on / 依赖: F.obj
-/
def natTransInCostructuredArrow {B : D} (F : J ⥤ CostructuredArrow K B) :
    F ⋙ CostructuredArrow.proj K B ⋙ K ⟶ (CategoryTheory.Functor.const J).obj B where
  app j := (F.obj j).hom

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- (Implementation) Given a cone in the base category, raise it to a cone in
`CostructuredArrow K B`. Note this is where the connected assumption is used.
-/
@[simps]
/--
Definition of `raiseCone` / `raiseCone` 的定义

English:
definition raiseCone
  signature: [IsConnected J] {B : D} {F : J ⥤ CostructuredArrow K B}
  body: CostructuredArrow.mk
    (K.map (c.π.app (Classical.arbitrary J)) ≫ (F.obj (Classical.arbitrary J)).hom)
π.app j := CostructuredArrow.homMk (c.π.app j) by
    let z : (Functor.const J).obj (K.obj c.pt) ⟶ _ :=
      (CategoryTheory.Functor.constComp J c.pt K).inv ≫ Functor.whiskerRight c.π K ≫
        natTransInCostructuredArrow F
    convert! (nat_trans_from_is_connected z j (Classical.arbitrary J)) <;> simp [z]
  π.naturality X Y f := by
    apply CommaMorphism.ext
    · simpa using (c.w f).symm
    · simp

中文:
定义 raiseCone
  签名: [是连通 J] {B : D} {F : J ⥤ CostructuredArrow K B}
  定义体: CostructuredArrow.mk
    (K.map (c.π.app (Classical.arbitrary J)) ≫ (F.obj (Classical.arbitrary J)).hom)
π.app j := CostructuredArrow.homMk (c.π.app j) by
    let z : (Functor.const J).obj (K.obj c.pt) ⟶ _ :=
      (CategoryTheory.Functor.constComp J c.pt K).inv ≫ Functor.whiskerRight c.π K ≫
        natTransInCostructuredArrow F
    convert! (nat_trans_from_is_connected z j (Classical.arbitrary J)) <;> simp [z]
  π.naturality X Y f := by
    apply CommaMorphism.ext
    · simpa using (c.w f).symm
    · simp

Depends on / 依赖: CostructuredArrow, CostructuredArrow.mk
-/
def raiseCone [IsConnected J] {B : D} {F : J ⥤ CostructuredArrow K B}
    (c : Cone (F ⋙ CostructuredArrow.proj K B)) :
    Cone F where
  pt := CostructuredArrow.mk
    (K.map (c.π.app (Classical.arbitrary J)) ≫ (F.obj (Classical.arbitrary J)).hom)
π.app j := CostructuredArrow.homMk (c.π.app j) by
    let z : (Functor.const J).obj (K.obj c.pt) ⟶ _ :=
      (CategoryTheory.Functor.constComp J c.pt K).inv ≫ Functor.whiskerRight c.π K ≫
        natTransInCostructuredArrow F
    convert! (nat_trans_from_is_connected z j (Classical.arbitrary J)) <;> simp [z]
  π.naturality X Y f := by
    apply CommaMorphism.ext
    · simpa using (c.w f).symm
    · simp

/--
theorem `mapCone_raiseCone` / 定理 `mapCone_raiseCone`

English:
theorem mapCone_raiseCone
  statement: [IsConnected J] {B : D} {F : J ⥤ CostructuredArrow K B}
  proof: by cat_disch

中文:
定理 mapCone_raiseCone
  结论: [是连通 J] {B : D} {F : J ⥤ CostructuredArrow K B}
  证明: by cat_disch

Depends on / 依赖: cat_disch
-/
theorem mapCone_raiseCone [IsConnected J] {B : D} {F : J ⥤ CostructuredArrow K B}
    (c : Cone (F ⋙ CostructuredArrow.proj K B)) :
    (CostructuredArrow.proj K B).mapCone (raiseCone c) = c := by cat_disch

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isLimitRaiseCone` / `isLimitRaiseCone` 的定义

English:
definition isLimitRaiseCone
  signature: [IsConnected J] {B : D} {F : J ⥤ CostructuredArrow K B}
  body: CostructuredArrow.homMk (t.lift ((CostructuredArrow.proj K B).mapCone s)) by
      simp [← Functor.map_comp_assoc]
  uniq s m K := by
    ext1
    apply t.hom_ext
    intro j
    simp [← K j]

中文:
定义 isLimitRaiseCone
  签名: [是连通 J] {B : D} {F : J ⥤ CostructuredArrow K B}
  定义体: CostructuredArrow.homMk (t.lift ((CostructuredArrow.proj K B).mapCone s)) by
      simp [← Functor.map_comp_assoc]
  uniq s m K := by
    ext1
    apply t.hom_ext
    intro j
    simp [← K j]

Depends on / 依赖: CostructuredArrow, CostructuredArrow.homMk, CostructuredArrow.proj, Functor, Functor.map_comp_assoc, hom_ext, mapCone, map_comp_assoc, t.hom_ext, t.lift
-/
def isLimitRaiseCone [IsConnected J] {B : D} {F : J ⥤ CostructuredArrow K B}
    {c : Cone (F ⋙ CostructuredArrow.proj K B)}
    (t : IsLimit c) : IsLimit (raiseCone c) where
  lift s :=
CostructuredArrow.homMk (t.lift ((CostructuredArrow.proj K B).mapCone s)) by
      simp [← Functor.map_comp_assoc]
  uniq s m K := by
    ext1
    apply t.hom_ext
    intro j
    simp [← K j]

end CreatesConnected

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsConnected
  signature: J] {B
  body: createsLimitOfReflectsIso fun c t =>
      { liftedCone := CreatesConnected.raiseCone c
        validLift := eqToIso (CreatesConnected.mapCone_raiseCone c)
        makesLimit := CreatesConnected.isLimitRaiseCone t }

中文:
实例 [是连通
  签名: J] {B
  定义体: createsLimitOfReflectsIso fun c t =>
      { liftedCone := CreatesConnected.raiseCone c
        validLift := eqToIso (CreatesConnected.mapCone_raiseCone c)
        makesLimit := CreatesConnected.isLimitRaiseCone t }

Depends on / 依赖: CreatesConnected, CreatesConnected.isLimitRaiseCone, CreatesConnected.mapCone_raiseCone, CreatesConnected.raiseCone, createsLimitOfReflectsIso, eqToIso, isLimitRaiseCone, liftedCone, makesLimit, mapCone_raiseCone, raiseCone, validLift
-/
instance [IsConnected J] {B : D} : CreatesLimitsOfShape J (CostructuredArrow.proj K B) where
  CreatesLimit :=
    createsLimitOfReflectsIso fun c t =>
      { liftedCone := CreatesConnected.raiseCone c
        validLift := eqToIso (CreatesConnected.mapCone_raiseCone c)
        makesLimit := CreatesConnected.isLimitRaiseCone t }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsConnected
  signature: J] {B
  body: ⟨{
    lift s := (CostructuredArrow.proj K B).map (hc.lift (CreatesConnected.raiseCone s))
    fac _ _ := by
      rw [Functor.mapCone_π_app]; rw [← Functor.map_comp]; rw [hc.fac]; rw [CreatesConnected.raiseCone_π_app]; rw [CostructuredArrow.proj_map]; rw [CostructuredArrow.homMk_left _ _]
    uniq s m fac :=
      congrArg (CostructuredArrow.proj K B).map (hc.uniq (CreatesConnected.raiseCone s)
        (CostructuredArrow.homMk m (by simp [← fac])) fun j =>
          (CostructuredArrow.proj K B).map_injective (fac j))
  }⟩

中文:
实例 [是连通
  签名: J] {B
  定义体: ⟨{
    lift s := (CostructuredArrow.proj K B).map (hc.lift (CreatesConnected.raiseCone s))
    fac _ _ := by
      rw [Functor.mapCone_π_app]; rw [← Functor.map_comp]; rw [hc.fac]; rw [CreatesConnected.raiseCone_π_app]; rw [CostructuredArrow.proj_map]; rw [CostructuredArrow.homMk_left _ _]
    uniq s m fac :=
      congrArg (CostructuredArrow.proj K B).map (hc.uniq (CreatesConnected.raiseCone s)
        (CostructuredArrow.homMk m (by simp [← fac])) fun j =>
          (CostructuredArrow.proj K B).map_injective (fac j))
  }⟩
-/
instance [IsConnected J] {B : D} : PreservesLimitsOfShape J (CostructuredArrow.proj K B) where
  preservesLimit.preserves hc := ⟨{
    lift s := (CostructuredArrow.proj K B).map (hc.lift (CreatesConnected.raiseCone s))
    fac _ _ := by
      rw [Functor.mapCone_π_app]; rw [← Functor.map_comp]; rw [hc.fac]; rw [CreatesConnected.raiseCone_π_app]; rw [CostructuredArrow.proj_map]; rw [CostructuredArrow.homMk_left _ _]
    uniq s m fac :=
      congrArg (CostructuredArrow.proj K B).map (hc.uniq (CreatesConnected.raiseCone s)
        (CostructuredArrow.homMk m (by simp [← fac])) fun j =>
          (CostructuredArrow.proj K B).map_injective (fac j))
  }⟩

/--
Instance `hasLimitsOfShape_of_isConnected` / 实例 `hasLimitsOfShape_of_isConnected`

English:
instance hasLimitsOfShape_of_isConnected
  signature: {B : D} [IsConnected J] [HasLimitsOfShape J C]
  body: hasLimit_of_created F (CostructuredArrow.proj K B)

中文:
实例 hasLimitsOfShape_of_isConnected
  签名: {B : D} [是连通 J] [有形状极限 J C]
  定义体: hasLimit_of_created F (CostructuredArrow.proj K B)

Depends on / 依赖: CostructuredArrow, CostructuredArrow.proj, hasLimit_of_created
-/
instance hasLimitsOfShape_of_isConnected {B : D} [IsConnected J] [HasLimitsOfShape J C] :
    HasLimitsOfShape J (CostructuredArrow K B) where
  has_limit F := hasLimit_of_created F (CostructuredArrow.proj K B)

end CostructuredArrow

namespace StructuredArrow

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsConnected
  signature: J] {B
  body: letI : CreatesLimitsOfShape Jᵒᵖ (proj B K).op :=
inferInstanceAs CreatesLimitsOfShape Jᵒᵖ
      (structuredArrowOpEquivalence K B).functor ⋙ CostructuredArrow.proj K.op (.op B)
  createsColimitsOfShapeOfOp _ _

中文:
实例 [是连通
  签名: J] {B
  定义体: letI : CreatesLimitsOfShape Jᵒᵖ (proj B K).op :=
inferInstanceAs CreatesLimitsOfShape Jᵒᵖ
      (structuredArrowOpEquivalence K B).functor ⋙ CostructuredArrow.proj K.op (.op B)
  createsColimitsOfShapeOfOp _ _

Depends on / 依赖: CostructuredArrow, CostructuredArrow.proj, CreatesLimitsOfShape, K.op, createsColimitsOfShapeOfOp, functor, structuredArrowOpEquivalence
-/
instance [IsConnected J] {B : D} : CreatesColimitsOfShape J (StructuredArrow.proj B K) :=
  letI : CreatesLimitsOfShape Jᵒᵖ (proj B K).op :=
inferInstanceAs CreatesLimitsOfShape Jᵒᵖ
      (structuredArrowOpEquivalence K B).functor ⋙ CostructuredArrow.proj K.op (.op B)
  createsColimitsOfShapeOfOp _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsConnected
  signature: J] {B
  body: by
  have : PreservesLimitsOfShape Jᵒᵖ (proj B K).op :=
inferInstanceAs PreservesLimitsOfShape Jᵒᵖ
      (structuredArrowOpEquivalence K B).functor ⋙ CostructuredArrow.proj K.op (.op B)
  apply preservesColimitsOfShape_of_op

中文:
实例 [是连通
  签名: J] {B
  定义体: by
  have : PreservesLimitsOfShape Jᵒᵖ (proj B K).op :=
inferInstanceAs PreservesLimitsOfShape Jᵒᵖ
      (structuredArrowOpEquivalence K B).functor ⋙ CostructuredArrow.proj K.op (.op B)
  apply preservesColimitsOfShape_of_op

Depends on / 依赖: CostructuredArrow, CostructuredArrow.proj, K.op, PreservesLimitsOfShape, functor, preservesColimitsOfShape_of_op, structuredArrowOpEquivalence
-/
instance [IsConnected J] {B : D} : PreservesColimitsOfShape J (StructuredArrow.proj B K) := by
  have : PreservesLimitsOfShape Jᵒᵖ (proj B K).op :=
inferInstanceAs PreservesLimitsOfShape Jᵒᵖ
      (structuredArrowOpEquivalence K B).functor ⋙ CostructuredArrow.proj K.op (.op B)
  apply preservesColimitsOfShape_of_op

instance {B : D} [IsConnected J] [HasColimitsOfShape J C] :
    HasColimitsOfShape J (StructuredArrow B K) where
  has_colimit F := hasColimit_of_created F (StructuredArrow.proj B K)

end StructuredArrow

namespace Over

/--
Instance `createsLimitsOfShapeForgetOfIsConnected` / 实例 `createsLimitsOfShapeForgetOfIsConnected`

English:
instance createsLimitsOfShapeForgetOfIsConnected
  signature: [IsConnected J] {B : C}
  body: inferInstanceAs CreatesLimitsOfShape J (CostructuredArrow.proj _ _)

中文:
实例 createsLimitsOfShapeForgetOfIsConnected
  签名: [是连通 J] {B : C}
  定义体: inferInstanceAs CreatesLimitsOfShape J (CostructuredArrow.proj _ _)

Depends on / 依赖: CostructuredArrow, CostructuredArrow.proj, CreatesLimitsOfShape
-/
instance createsLimitsOfShapeForgetOfIsConnected [IsConnected J] {B : C} :
    CreatesLimitsOfShape J (forget B) :=
inferInstanceAs CreatesLimitsOfShape J (CostructuredArrow.proj _ _)

/--
Instance `preservesLimitsOfShape_forget_of_isConnected` / 实例 `preservesLimitsOfShape_forget_of_isConnected`

English:
instance preservesLimitsOfShape_forget_of_isConnected
  signature: [IsConnected J] {B : C}
  body: inferInstanceAs PreservesLimitsOfShape J (CostructuredArrow.proj _ _)

中文:
实例 preservesLimitsOfShape_forget_of_isConnected
  签名: [是连通 J] {B : C}
  定义体: inferInstanceAs PreservesLimitsOfShape J (CostructuredArrow.proj _ _)

Depends on / 依赖: CostructuredArrow, CostructuredArrow.proj, PreservesLimitsOfShape
-/
instance preservesLimitsOfShape_forget_of_isConnected [IsConnected J] {B : C} :
    PreservesLimitsOfShape J (forget B) :=
inferInstanceAs PreservesLimitsOfShape J (CostructuredArrow.proj _ _)

/--
Instance `hasLimitsOfShape_of_isConnected` / 实例 `hasLimitsOfShape_of_isConnected`

English:
instance hasLimitsOfShape_of_isConnected
  signature: {B : C} [IsConnected J] [HasLimitsOfShape J C]
  body: hasLimit_of_created F (forget B)

中文:
实例 hasLimitsOfShape_of_isConnected
  签名: {B : C} [是连通 J] [有形状极限 J C]
  定义体: hasLimit_of_created F (forget B)

Depends on / 依赖: forget, hasLimit_of_created
-/
instance hasLimitsOfShape_of_isConnected {B : C} [IsConnected J] [HasLimitsOfShape J C] :
    HasLimitsOfShape J (Over B) where
  has_limit F := hasLimit_of_created F (forget B)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The functor taking a cone over `F` to a cone over `Over.post F : Over i ⥤ Over (F.obj i)`.
This takes limit cones to limit cones when `J` is cofiltered. See `isLimitConePost` -/
@[simps]
/--
Definition of `conePost` / `conePost` 的定义

English:
definition conePost
  signature: (F : J ⥤ C) (i : J)
  body: { pt := Over.mk (c.π.app i), π := { app X := Over.homMk (c.π.app X.left) } }
  map f := { hom := Over.homMk f.hom }

中文:
定义 conePost
  签名: (F : J ⥤ C) (i : J)
  定义体: { pt := Over.mk (c.π.app i), π := { app X := Over.homMk (c.π.app X.left) } }
  map f := { hom := Over.homMk f.hom }
-/
def conePost (F : J ⥤ C) (i : J) : Cone F ⥤ Cone (Over.post (X := i) F) where
  obj c := { pt := Over.mk (c.π.app i), π := { app X := Over.homMk (c.π.app X.left) } }
  map f := { hom := Over.homMk f.hom }

set_option backward.isDefEq.respectTransparency.types false in
/-- `conePost` is compatible with the forgetful functors on over categories. -/
@[simps!]
/--
Definition of `conePostIso` / `conePostIso` 的定义

English:
definition conePostIso
  signature: (F : J ⥤ C) (i : J)
  body: .refl _

中文:
定义 conePostIso
  签名: (F : J ⥤ C) (i : J)
  定义体: .refl _
-/
def conePostIso (F : J ⥤ C) (i : J) :
    conePost F i ⋙ Cone.functoriality _ (Over.forget (F.obj i)) ≅
      Cone.whiskering (Over.forget _) := .refl _

set_option backward.isDefEq.respectTransparency.types false in
attribute [local instance] IsCofiltered.isConnected in
/-- The functor taking a cone over `F` to a cone over `Over.post F : Over i ⥤ Over (F.obj i)`
preserves limit cones -/
noncomputable
/--
Definition of `isLimitConePost` / `isLimitConePost` 的定义

English:
definition isLimitConePost
  signature: [IsCofilteredOrEmpty J] {F : J ⥤ C} {c : Cone F} (i : J) (hc : IsLimit c)
  body: isLimitOfReflects (Over.forget _)
    ((Functor.Initial.isLimitWhiskerEquiv (Over.forget i) c).symm hc)

中文:
定义 isLimitConePost
  签名: [是余filteredOrEmpty J] {F : J ⥤ C} {c : 锥 F} (i : J) (hc : 是极限 c)
  定义体: isLimitOfReflects (Over.forget _)
    ((Functor.Initial.isLimitWhiskerEquiv (Over.forget i) c).symm hc)

Depends on / 依赖: Functor, Functor.Initial.isLimitWhiskerEquiv, Initial, Over.forget, forget, isLimitOfReflects, isLimitWhiskerEquiv
-/
def isLimitConePost [IsCofilteredOrEmpty J] {F : J ⥤ C} {c : Cone F} (i : J) (hc : IsLimit c) :
    IsLimit ((conePost F i).obj c) :=
  isLimitOfReflects (Over.forget _)
    ((Functor.Initial.isLimitWhiskerEquiv (Over.forget i) c).symm hc)

end Over

instance {B : D} [IsConnected J] [HasLimitsOfShape J C] [PreservesLimitsOfShape J K] :
    PreservesLimitsOfShape J (CostructuredArrow.toOver K B) where
  preservesLimit {D} := by
    have : PreservesLimit D (CostructuredArrow.toOver K B ⋙ Over.forget B) :=
inferInstanceAs PreservesLimit D (CostructuredArrow.proj K B ⋙ K)
    exact Limits.preservesLimit_of_reflects_of_preserves _ (Over.forget B)

namespace Under

/--
Instance `createsColimitsOfShapeForgetOfIsConnected` / 实例 `createsColimitsOfShapeForgetOfIsConnected`

English:
instance createsColimitsOfShapeForgetOfIsConnected
  signature: [IsConnected J] {B : C}
  body: inferInstanceAs CreatesColimitsOfShape J (StructuredArrow.proj _ _)

中文:
实例 createsColimitsOfShapeForgetOfIsConnected
  签名: [是连通 J] {B : C}
  定义体: inferInstanceAs CreatesColimitsOfShape J (StructuredArrow.proj _ _)

Depends on / 依赖: CreatesColimitsOfShape, StructuredArrow, StructuredArrow.proj
-/
instance createsColimitsOfShapeForgetOfIsConnected [IsConnected J] {B : C} :
    CreatesColimitsOfShape J (forget B) :=
inferInstanceAs CreatesColimitsOfShape J (StructuredArrow.proj _ _)

/--
Instance `preservesColimitsOfShape_forget_of_isConnected` / 实例 `preservesColimitsOfShape_forget_of_isConnected`

English:
instance preservesColimitsOfShape_forget_of_isConnected
  signature: [IsConnected J] {B : C}
  body: inferInstanceAs PreservesColimitsOfShape J (StructuredArrow.proj _ _)

中文:
实例 preservesColimitsOfShape_forget_of_isConnected
  签名: [是连通 J] {B : C}
  定义体: inferInstanceAs PreservesColimitsOfShape J (StructuredArrow.proj _ _)

Depends on / 依赖: PreservesColimitsOfShape, StructuredArrow, StructuredArrow.proj
-/
instance preservesColimitsOfShape_forget_of_isConnected [IsConnected J] {B : C} :
    PreservesColimitsOfShape J (forget B) :=
inferInstanceAs PreservesColimitsOfShape J (StructuredArrow.proj _ _)

/--
Instance `hasColimitsOfShape_of_isConnected` / 实例 `hasColimitsOfShape_of_isConnected`

English:
instance hasColimitsOfShape_of_isConnected
  signature: {B : C} [IsConnected J] [HasColimitsOfShape J C]
  body: hasColimit_of_created F (forget B)

中文:
实例 hasColimitsOfShape_of_isConnected
  签名: {B : C} [是连通 J] [有形状余极限 J C]
  定义体: hasColimit_of_created F (forget B)

Depends on / 依赖: forget, hasColimit_of_created
-/
instance hasColimitsOfShape_of_isConnected {B : C} [IsConnected J] [HasColimitsOfShape J C] :
    HasColimitsOfShape J (Under B) where
  has_colimit F := hasColimit_of_created F (forget B)

end Under

instance {B : D} [IsConnected J] [HasColimitsOfShape J C] [PreservesColimitsOfShape J K] :
    PreservesColimitsOfShape J (StructuredArrow.toUnder B K) where
  preservesColimit {D} := by
    have : PreservesColimit D (StructuredArrow.toUnder B K ⋙ Under.forget B) :=
inferInstanceAs PreservesColimit D (StructuredArrow.proj B K ⋙ K)
    exact Limits.preservesColimit_of_reflects_of_preserves _ (Under.forget B)

end CategoryTheory
