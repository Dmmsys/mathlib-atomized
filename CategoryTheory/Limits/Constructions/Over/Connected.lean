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
/-
**CategoryTheory.CostructuredArrow.CreatesConnected.natTransInCostructuredArrow*
* 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.CostructuredArrow.CreatesConnected`。
形式化陈述：natTransInCostructuredArrow {B : D} (F : J ⥤ CostructuredArrow K B) : F ⋙ 
CostructuredArrow.proj K B ⋙ K ⟶ (CategoryTheory.Functor.const J).obj B where ap
p j
参数：F : J ⥤ CostructuredArrow K B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Implementation) Given a diagram in `CostructuredArrow K B`, produce a natural t
ransformation
from the diagram legs to the specific object.
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
/-
**CategoryTheory.CostructuredArrow.CreatesConnected.raiseCone** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.CostructuredArrow.CreatesConnected`。
形式化陈述：raiseCone [IsConnected J] {B : D} {F : J ⥤ CostructuredArrow K B} (c : Con
e (F ⋙ CostructuredArrow.proj K B)) : Cone F where pt
参数：c : Cone (F ⋙ CostructuredArrow.proj K B)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsConnected.is_nonempty`：∀ {J : Type u₁} {inst : Category
Theory.Category.{v₁, u₁} J} [self : CategoryTheory.IsConnected J], Nonempty J

--- 原说明 ---
(Implementation) Given a cone in the base category, raise it to a cone in
`CostructuredArrow K B`. Note this is where the connected assumption is used.
-/
def raiseCone [IsConnected J] {B : D} {F : J ⥤ CostructuredArrow K B}
    (c : Cone (F ⋙ CostructuredArrow.proj K B)) :
    Cone F where
  pt := CostructuredArrow.mk
    (K.map (c.π.app (Classical.arbitrary J)) ≫ (F.obj (Classical.arbitrary J)).hom)
  π.app j := CostructuredArrow.homMk (c.π.app j) <| by
    let z : (Functor.const J).obj (K.obj c.pt) ⟶ _ :=
      (CategoryTheory.Functor.constComp J c.pt K).inv ≫ Functor.whiskerRight c.π K ≫
        natTransInCostructuredArrow F
    convert! (nat_trans_from_is_connected z j (Classical.arbitrary J)) <;> simp [z]
  π.naturality X Y f := by
    apply CommaMorphism.ext
    · simpa using (c.w f).symm
    · simp
/-
**CategoryTheory.CostructuredArrow.CreatesConnected.mapCone_raiseCone** 是 Mathli
b 中的一个定理，位于命名空间 `CategoryTheory.CostructuredArrow.CreatesConnected`。
形式化陈述：mapCone_raiseCone [IsConnected J] {B : D} {F : J ⥤ CostructuredArrow K B} 
(c : Cone (F ⋙ CostructuredArrow.proj K B)) : (CostructuredArrow.proj K B).mapCo
ne (raiseCone c) = c
参数：c : Cone (F ⋙ CostructuredArrow.proj K B)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapCone_raiseCone [IsConnected J] {B : D} {F : J ⥤ CostructuredArrow K B}
    (c : Cone (F ⋙ CostructuredArrow.proj K B)) :
    (CostructuredArrow.proj K B).mapCone (raiseCone c) = c := by cat_disch

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- (Implementation) Show that the raised cone is a limit. -/
/-
**CategoryTheory.CostructuredArrow.CreatesConnected.isLimitRaiseCone** 是 Mathlib
 中的一个定义，位于命名空间 `CategoryTheory.CostructuredArrow.CreatesConnected`。
形式化陈述：isLimitRaiseCone [IsConnected J] {B : D} {F : J ⥤ CostructuredArrow K B} {
c : Cone (F ⋙ CostructuredArrow.proj K B)} (t : IsLimit c) : IsLimit (raiseCone 
c) where lift s
参数：F ⋙ CostructuredArrow.proj K B；t : IsLimit c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Implementation) Show that the raised cone is a limit.
-/
def isLimitRaiseCone [IsConnected J] {B : D} {F : J ⥤ CostructuredArrow K B}
    {c : Cone (F ⋙ CostructuredArrow.proj K B)}
    (t : IsLimit c) : IsLimit (raiseCone c) where
  lift s :=
    CostructuredArrow.homMk (t.lift ((CostructuredArrow.proj K B).mapCone s)) <| by
      simp [← Functor.map_comp_assoc]
  uniq s m K := by
    ext1
    apply t.hom_ext
    intro j
    simp [← K j]

end CreatesConnected

/-- The projection from `CostructuredArrow K B` to `C` creates any connected limit. -/
/-
**CategoryTheory.CostructuredArrow.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Co
structuredArrow`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projection from `CostructuredArrow K B` to `C` creates any connected limit.
-/
instance [IsConnected J] {B : D} : CreatesLimitsOfShape J (CostructuredArrow.proj K B) where
  CreatesLimit :=
    createsLimitOfReflectsIso fun c t =>
      { liftedCone := CreatesConnected.raiseCone c
        validLift := eqToIso (CreatesConnected.mapCone_raiseCone c)
        makesLimit := CreatesConnected.isLimitRaiseCone t }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The forgetful functor from `CostructuredArrow K B` preserves any connected limit. -/
/-
**CategoryTheory.CostructuredArrow.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Co
structuredArrow`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from `CostructuredArrow K B` preserves any connected limit
.
-/
instance [IsConnected J] {B : D} : PreservesLimitsOfShape J (CostructuredArrow.proj K B) where
  preservesLimit.preserves hc := ⟨{
    lift s := (CostructuredArrow.proj K B).map (hc.lift (CreatesConnected.raiseCone s))
    fac _ _ := by
      rw [Functor.mapCone_π_app, ← Functor.map_comp, hc.fac,
        CreatesConnected.raiseCone_π_app, CostructuredArrow.proj_map,
        CostructuredArrow.homMk_left _ _]
    uniq s m fac :=
      congrArg (CostructuredArrow.proj K B).map (hc.uniq (CreatesConnected.raiseCone s)
        (CostructuredArrow.homMk m (by simp [← fac])) fun j =>
          (CostructuredArrow.proj K B).map_injective (fac j))
  }⟩

/-- The over category has any connected limit which the original category has. -/
/-
**CategoryTheory.CostructuredArrow.hasLimitsOfShape_of_isConnected** 是 Mathlib 中
的一个实例，位于命名空间 `CategoryTheory.CostructuredArrow`。
形式化陈述：hasLimitsOfShape_of_isConnected {B : D} [IsConnected J] [HasLimitsOfShape 
J C] : HasLimitsOfShape J (CostructuredArrow K B) where has_limit F
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.hasLimit_of_created`：hasLimit_of_created (K : J ⥤ C) (F :
 C ⥤ D) [HasLimit (K ⋙ F)] [CreatesLimit K F] : HasLimit K
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…

--- 原说明 ---
The over category has any connected limit which the original category has.
-/
instance hasLimitsOfShape_of_isConnected {B : D} [IsConnected J] [HasLimitsOfShape J C] :
    HasLimitsOfShape J (CostructuredArrow K B) where
  has_limit F := hasLimit_of_created F (CostructuredArrow.proj K B)

end CostructuredArrow

namespace StructuredArrow

/-- The projection from `StructuredArrow K B` to `C` creates any connected colimit. -/
/-
**CategoryTheory.StructuredArrow.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Stru
cturedArrow`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projection from `StructuredArrow K B` to `C` creates any connected colimit.
-/
instance [IsConnected J] {B : D} : CreatesColimitsOfShape J (StructuredArrow.proj B K) :=
  letI : CreatesLimitsOfShape Jᵒᵖ (proj B K).op :=
    inferInstanceAs <| CreatesLimitsOfShape Jᵒᵖ <|
      (structuredArrowOpEquivalence K B).functor ⋙ CostructuredArrow.proj K.op (.op B)
  createsColimitsOfShapeOfOp _ _

/-- The forgetful functor from `StructuredArrow K B` preserves any connected colimit. -/
/-
**CategoryTheory.StructuredArrow.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Stru
cturedArrow`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from `StructuredArrow K B` preserves any connected colimit
.
-/
instance [IsConnected J] {B : D} : PreservesColimitsOfShape J (StructuredArrow.proj B K) := by
  have : PreservesLimitsOfShape Jᵒᵖ (proj B K).op :=
    inferInstanceAs <| PreservesLimitsOfShape Jᵒᵖ <|
      (structuredArrowOpEquivalence K B).functor ⋙ CostructuredArrow.proj K.op (.op B)
  apply preservesColimitsOfShape_of_op
/-
**CategoryTheory.StructuredArrow.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Stru
cturedArrow`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {B : D} [IsConnected J] [HasColimitsOfShape J C] :
    HasColimitsOfShape J (StructuredArrow B K) where
  has_colimit F := hasColimit_of_created F (StructuredArrow.proj B K)

end StructuredArrow

namespace Over

/-- The forgetful functor from the over category creates any connected limit. -/
/-
**CategoryTheory.Over.createsLimitsOfShapeForgetOfIsConnected** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.Over`。
形式化陈述：{J : Type u'} →   [inst : CategoryTheory.Category.{v', u'} J] →     {C : T
ype u} →       [inst_1 : CategoryTheory.Category.{v, u} C] →         [CategoryTh
eory.IsConnected J] → {B : C} → CategoryTheory.CreatesLimitsOfShape J (CategoryT
heory.Over.forget B)
参数：CategoryTheory.Over.forget B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from the over category creates any connected limit.
-/
instance createsLimitsOfShapeForgetOfIsConnected [IsConnected J] {B : C} :
    CreatesLimitsOfShape J (forget B) :=
  inferInstanceAs <| CreatesLimitsOfShape J (CostructuredArrow.proj _ _)

/-- The forgetful functor from the over category preserves any connected limit. -/
/-
**CategoryTheory.Over.preservesLimitsOfShape_forget_of_isConnected** 是 Mathlib 中
的一个定理，位于命名空间 `CategoryTheory.Over`。
形式化陈述：∀ {J : Type u'} [inst : CategoryTheory.Category.{v', u'} J] {C : Type u} [
inst_1 : CategoryTheory.Category.{v, u} C]   [CategoryTheory.IsConnected J] {B :
 C}, CategoryTheory.Limits.PreservesLimitsOfShape J (CategoryTheory.Over.forget 
B)
参数：CategoryTheory.Over.forget B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from the over category preserves any connected limit.
-/
instance preservesLimitsOfShape_forget_of_isConnected [IsConnected J] {B : C} :
    PreservesLimitsOfShape J (forget B) :=
  inferInstanceAs <| PreservesLimitsOfShape J (CostructuredArrow.proj _ _)

/-- The over category has any connected limit which the original category has. -/
/-
**CategoryTheory.Over.hasLimitsOfShape_of_isConnected** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Over`。
形式化陈述：∀ {J : Type u'} [inst : CategoryTheory.Category.{v', u'} J] {C : Type u} [
inst_1 : CategoryTheory.Category.{v, u} C]   {B : C} [CategoryTheory.IsConnected
 J] [CategoryTheory.Limits.HasLimitsOfShape J C],   CategoryTheory.Limits.HasLim
itsOfShape J (CategoryTheory.Over B)
参数：CategoryTheory.Over B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.hasLimit_of_created`：hasLimit_of_created (K : J ⥤ C) (F :
 C ⥤ D) [HasLimit (K ⋙ F)] [CreatesLimit K F] : HasLimit K
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…

--- 原说明 ---
The over category has any connected limit which the original category has.
-/
instance hasLimitsOfShape_of_isConnected {B : C} [IsConnected J] [HasLimitsOfShape J C] :
    HasLimitsOfShape J (Over B) where
  has_limit F := hasLimit_of_created F (forget B)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The functor taking a cone over `F` to a cone over `Over.post F : Over i ⥤ Over (F.obj i)`.
This takes limit cones to limit cones when `J` is cofiltered. See `isLimitConePost` -/
@[simps]
/-
**CategoryTheory.Over.conePost** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Over`。
形式化陈述：{J : Type u'} →   [inst : CategoryTheory.Category.{v', u'} J] →     {C : T
ype u} →       [inst_1 : CategoryTheory.Category.{v, u} C] →         (F : Catego
ryTheory.Functor J C) →           (i : J) →             CategoryTheory.Functor (
CategoryTheory.Limits.Cone F)               (CategoryTheory.Limits.Cone (Categor
yTheory.Over.post F))
参数：F : CategoryTheory.Functor J C；i : J；CategoryTheory.Limits.Cone F；CategoryThe
ory.Limits.Cone (CategoryTheory.Over.post F)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor taking a cone over `F` to a cone over `Over.post F : Over i ⥤ Over (
F.obj i)`.
This takes limit cones to limit cones when `J` is cofiltered. See `isLimitConePo
st`
-/
def conePost (F : J ⥤ C) (i : J) : Cone F ⥤ Cone (Over.post (X := i) F) where
  obj c := { pt := Over.mk (c.π.app i), π := { app X := Over.homMk (c.π.app X.left) } }
  map f := { hom := Over.homMk f.hom }

set_option backward.isDefEq.respectTransparency.types false in
/-- `conePost` is compatible with the forgetful functors on over categories. -/
@[simps!]
/-
**CategoryTheory.Over.conePostIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Over
`。
形式化陈述：{J : Type u'} →   [inst : CategoryTheory.Category.{v', u'} J] →     {C : T
ype u} →       [inst_1 : CategoryTheory.Category.{v, u} C] →         (F : Catego
ryTheory.Functor J C) →           (i : J) →             (CategoryTheory.Over.con
ePost F i).comp                 (CategoryTheory.Limits.Cone.functoriality (Categ
oryTheory.Over.post F)                   (CategoryTheory.Over.forget (F.obj i)))
 ≅               CategoryTheory.Limits.Cone.whiskering (CategoryTheory.Over.forg
et i)
参数：F : CategoryTheory.Functor J C；i : J；CategoryTheory.Over.conePost F i；Categor
yTheory.Limits.Cone.functoriality (CategoryTheory.Over.post F)                  
 (CategoryTheory.Over.forget (F.obj i))；CategoryTheory.Over.forget i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`conePost` is compatible with the forgetful functors on over categories.
-/
def conePostIso (F : J ⥤ C) (i : J) :
    conePost F i ⋙ Cone.functoriality _ (Over.forget (F.obj i)) ≅
      Cone.whiskering (Over.forget _) := .refl _

set_option backward.isDefEq.respectTransparency.types false in
attribute [local instance] IsCofiltered.isConnected in
/-- The functor taking a cone over `F` to a cone over `Over.post F : Over i ⥤ Over (F.obj i)`
preserves limit cones -/
noncomputable
/-
**CategoryTheory.Over.isLimitConePost** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Over`。
形式化陈述：{J : Type u'} →   [inst : CategoryTheory.Category.{v', u'} J] →     {C : T
ype u} →       [inst_1 : CategoryTheory.Category.{v, u} C] →         [CategoryTh
eory.IsCofilteredOrEmpty J] →           {F : CategoryTheory.Functor J C} →      
       {c : CategoryTheory.Limits.Cone F} →               (i : J) →             
    CategoryTheory.Limits.IsLimit c →                   CategoryTheory.Limits.Is
Limit ((CategoryTheory.Over.conePost F i).obj c)
参数：i : J；(CategoryTheory.Over.conePost F i).obj c。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.Over.initial_forget`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] [CategoryTheory.IsCofilteredOrEmpty C] (c : C),   (Categ
oryTheory.Over.forget c)…
-/
def isLimitConePost [IsCofilteredOrEmpty J] {F : J ⥤ C} {c : Cone F} (i : J) (hc : IsLimit c) :
    IsLimit ((conePost F i).obj c) :=
  isLimitOfReflects (Over.forget _)
    ((Functor.Initial.isLimitWhiskerEquiv (Over.forget i) c).symm hc)

end Over

/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {B : D} [IsConnected J] [HasLimitsOfShape J C] [PreservesLimitsOfShape J K] :
    PreservesLimitsOfShape J (CostructuredArrow.toOver K B) where
  preservesLimit {D} := by
    have : PreservesLimit D (CostructuredArrow.toOver K B ⋙ Over.forget B) :=
      inferInstanceAs <| PreservesLimit D (CostructuredArrow.proj K B ⋙ K)
    exact Limits.preservesLimit_of_reflects_of_preserves _ (Over.forget B)

namespace Under

/-- The forgetful functor from the under category creates any connected limit. -/
/-
**CategoryTheory.Under.createsColimitsOfShapeForgetOfIsConnected** 是 Mathlib 中的一
个定义，位于命名空间 `CategoryTheory.Under`。
形式化陈述：{J : Type u'} →   [inst : CategoryTheory.Category.{v', u'} J] →     {C : T
ype u} →       [inst_1 : CategoryTheory.Category.{v, u} C] →         [CategoryTh
eory.IsConnected J] →           {B : C} → CategoryTheory.CreatesColimitsOfShape 
J (CategoryTheory.Under.forget B)
参数：CategoryTheory.Under.forget B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from the under category creates any connected limit.
-/
instance createsColimitsOfShapeForgetOfIsConnected [IsConnected J] {B : C} :
    CreatesColimitsOfShape J (forget B) :=
  inferInstanceAs <| CreatesColimitsOfShape J (StructuredArrow.proj _ _)

/-- The forgetful functor from the under category preserves any connected limit. -/
/-
**CategoryTheory.Under.preservesColimitsOfShape_forget_of_isConnected** 是 Mathli
b 中的一个定理，位于命名空间 `CategoryTheory.Under`。
形式化陈述：∀ {J : Type u'} [inst : CategoryTheory.Category.{v', u'} J] {C : Type u} [
inst_1 : CategoryTheory.Category.{v, u} C]   [CategoryTheory.IsConnected J] {B :
 C},   CategoryTheory.Limits.PreservesColimitsOfShape J (CategoryTheory.Under.fo
rget B)
参数：CategoryTheory.Under.forget B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from the under category preserves any connected limit.
-/
instance preservesColimitsOfShape_forget_of_isConnected [IsConnected J] {B : C} :
    PreservesColimitsOfShape J (forget B) :=
  inferInstanceAs <| PreservesColimitsOfShape J (StructuredArrow.proj _ _)

/-- The under category has any connected limit which the original category has. -/
/-
**CategoryTheory.Under.hasColimitsOfShape_of_isConnected** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Under`。
形式化陈述：∀ {J : Type u'} [inst : CategoryTheory.Category.{v', u'} J] {C : Type u} [
inst_1 : CategoryTheory.Category.{v, u} C]   {B : C} [CategoryTheory.IsConnected
 J] [CategoryTheory.Limits.HasColimitsOfShape J C],   CategoryTheory.Limits.HasC
olimitsOfShape J (CategoryTheory.Under B)
参数：CategoryTheory.Under B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.hasColimit_of_created`：hasColimit_of_created (K : J ⥤ C) 
(F : C ⥤ D) [HasColimit (K ⋙ F)] [CreatesColimit K F] : HasColimit K
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…

--- 原说明 ---
The under category has any connected limit which the original category has.
-/
instance hasColimitsOfShape_of_isConnected {B : C} [IsConnected J] [HasColimitsOfShape J C] :
    HasColimitsOfShape J (Under B) where
  has_colimit F := hasColimit_of_created F (forget B)

end Under

/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {B : D} [IsConnected J] [HasColimitsOfShape J C] [PreservesColimitsOfShape J K] :
    PreservesColimitsOfShape J (StructuredArrow.toUnder B K) where
  preservesColimit {D} := by
    have : PreservesColimit D (StructuredArrow.toUnder B K ⋙ Under.forget B) :=
      inferInstanceAs <| PreservesColimit D (StructuredArrow.proj B K ⋙ K)
    exact Limits.preservesColimit_of_reflects_of_preserves _ (Under.forget B)

end CategoryTheory

