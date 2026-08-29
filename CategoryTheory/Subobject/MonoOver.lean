/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Adjunction.Reflective
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Limits.Shapes.Images
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic
public import Mathlib.CategoryTheory.WithTerminal.Cone
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# Monomorphisms over a fixed object

As preparation for defining `Subobject X`, we set up the theory for
`MonoOver X := { f : Over X // Mono f.hom}`.

Here `MonoOver X` is a thin category (a pair of objects has at most one morphism between them),
so we can think of it as a preorder. However as it is not skeletal, it is not yet a partial order.

`Subobject X` will be defined as the skeletalization of `MonoOver X`.

We provide
* `def pullback [HasPullbacks C] (f : X ⟶ Y) : MonoOver Y ⥤ MonoOver X`
* `def map (f : X ⟶ Y) [Mono f] : MonoOver X ⥤ MonoOver Y`
* `def «exists» [HasImages C] (f : X ⟶ Y) : MonoOver X ⥤ MonoOver Y`

and prove their basic properties and relationships.

## Notes

This development originally appeared in Bhavik Mehta's "Topos theory for Lean" repository,
and was ported to mathlib by Kim Morrison.

-/

@[expose] public section


universe w' w v₁ v₂ v₃ u₁ u₂ u₃

noncomputable section

namespace CategoryTheory

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] {X Y Z : C}
variable {D : Type u₂} [Category.{v₂} D]

/--
Definition of `Over.isMono` / `Over.isMono` 的定义

English:
abbreviation Over.isMono
  signature: (X : C)
  body: fun f : Over X => Mono f.hom

中文:
缩写 Over.isMono
  签名: (X : C)
  定义体: fun f : Over X => Mono f.hom

Depends on / 依赖: f.hom
-/
abbrev Over.isMono (X : C) : ObjectProperty (Over X) :=
  fun f : Over X => Mono f.hom

/--
Definition of `MonoOver` / `MonoOver` 的定义

English:
abbreviation MonoOver
  signature: (X : C)
  body: (Over.isMono X).FullSubcategory

中文:
缩写 MonoOver
  签名: (X : C)
  定义体: (Over.isMono X).FullSubcategory

Depends on / 依赖: FullSubcategory, Over.isMono, isMono
-/
abbrev MonoOver (X : C) := (Over.isMono X).FullSubcategory

namespace MonoOver

/--
Instance `mono_obj_hom` / 实例 `mono_obj_hom`

English:
instance mono_obj_hom
  signature: (S : MonoOver X)
  body: S.2

中文:
实例 mono_obj_hom
  签名: (S : MonoOver X)
  定义体: S.2
-/
instance mono_obj_hom (S : MonoOver X) : Mono S.obj.hom := S.2

/-- Construct a `MonoOver X`. -/
@[simps]
/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: {X A : C} (f : A ⟶ X) [hf : Mono f]
  body: Over.mk f
  property := hf

中文:
定义 mk
  签名: {X A : C} (f : A ⟶ X) [hf : 单态射 f]
  定义体: Over.mk f
  property := hf

Depends on / 依赖: Over.mk
-/
def mk {X A : C} (f : A ⟶ X) [hf : Mono f] : MonoOver X where
  obj := Over.mk f
  property := hf

/--
Definition of `forget` / `forget` 的定义

English:
abbreviation forget
  signature: (X : C)
  body: ObjectProperty.ι _

中文:
缩写 forget
  签名: (X : C)
  定义体: ObjectProperty.ι _

Depends on / 依赖: ObjectProperty
-/
abbrev forget (X : C) : MonoOver X ⥤ Over X :=
  ObjectProperty.ι _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeOut (MonoOver X) C
  body: Y.obj.left

@[simp]

中文:
实例 :
  签名: CoeOut (MonoOver X) C
  定义体: Y.obj.left

@[simp]

Depends on / 依赖: Y.obj.left
-/
instance : CoeOut (MonoOver X) C where coe Y := Y.obj.left

@[simp]
/--
theorem `forget_obj_left` / 定理 `forget_obj_left`

English:
theorem forget_obj_left
  given: {f}
  statement: ((forget X).obj f).left = (f : C)
  proof: rfl

@[simp]

中文:
定理 forget_obj_left
  条件: {f}
  结论: ((forget X).obj f).left = (f : C)
  证明: rfl

@[simp]
-/
theorem forget_obj_left {f} : ((forget X).obj f).left = (f : C) :=
  rfl

@[simp]
/--
theorem `mk_coe` / 定理 `mk_coe`

English:
theorem mk_coe
  given: {X A : C} (f : A ⟶ X) [Mono f]
  statement: (mk f : C) = A
  proof: rfl

中文:
定理 mk_coe
  条件: {X A : C} (f : A ⟶ X) [单态射 f]
  结论: (mk f : C) = A
  证明: rfl
-/
theorem mk_coe {X A : C} (f : A ⟶ X) [Mono f] : (mk f : C) = A :=
  rfl

/--
Definition of `arrow` / `arrow` 的定义

English:
abbreviation arrow
  signature: (f : MonoOver X)
  body: f.obj.hom

@[simp]

中文:
缩写 arrow
  签名: (f : MonoOver X)
  定义体: f.obj.hom

@[simp]

Depends on / 依赖: f.obj.hom
-/
abbrev arrow (f : MonoOver X) : (f : C) ⟶ X := f.obj.hom

@[simp]
/--
theorem `mk_arrow` / 定理 `mk_arrow`

English:
theorem mk_arrow
  given: {X A : C} (f : A ⟶ X) [Mono f]
  statement: (mk f).arrow = f
  proof: rfl

中文:
定理 mk_arrow
  条件: {X A : C} (f : A ⟶ X) [单态射 f]
  结论: (mk f).arrow = f
  证明: rfl
-/
theorem mk_arrow {X A : C} (f : A ⟶ X) [Mono f] : (mk f).arrow = f :=
  rfl

/--
theorem `forget_obj_hom` / 定理 `forget_obj_hom`

English:
theorem forget_obj_hom
  given: {f}
  statement: ((forget X).obj f).hom = f.arrow
  proof: rfl

中文:
定理 forget_obj_hom
  条件: {f}
  结论: ((forget X).obj f).hom = f.arrow
  证明: rfl
-/
theorem forget_obj_hom {f} : ((forget X).obj f).hom = f.arrow := rfl

/--
Definition of `fullyFaithfulForget` / `fullyFaithfulForget` 的定义

English:
definition fullyFaithfulForget
  signature: (X : C)
  body: ObjectProperty.fullyFaithfulι _

中文:
定义 fullyFaithfulForget
  签名: (X : C)
  定义体: ObjectProperty.fullyFaithfulι _

Depends on / 依赖: ObjectProperty, ObjectProperty.fullyFaithful
-/
def fullyFaithfulForget (X : C) : (forget X).FullyFaithful :=
  ObjectProperty.fullyFaithfulι _

/--
Instance `mono` / 实例 `mono`

English:
instance mono
  signature: (f : MonoOver X)
  body: f.property

中文:
实例 mono
  签名: (f : MonoOver X)
  定义体: f.property

Depends on / 依赖: f.property, property
-/
instance mono (f : MonoOver X) : Mono f.arrow :=
  f.property

instance {X : C} {f : MonoOver X} : Mono ((MonoOver.forget X).obj f).hom := f.mono

/--
Instance `isThin` / 实例 `isThin`

English:
instance isThin
  signature: {X : C}
  body: fun f g =>
  ⟨by
    intro h₁ h₂
    apply InducedCategory.hom_ext
    apply Over.OverMorphism.ext
    rw [← cancel_mono g.arrow]; rw [Over.w h₁.hom]; rw [Over.w h₂.hom]⟩

@[reassoc]

中文:
实例 isThin
  签名: {X : C}
  定义体: fun f g =>
  ⟨by
    intro h₁ h₂
    apply InducedCategory.hom_ext
    apply Over.OverMorphism.ext
    rw [← cancel_mono g.arrow]; rw [Over.w h₁.hom]; rw [Over.w h₂.hom]⟩

@[reassoc]
-/
instance isThin {X : C} : Quiver.IsThin (MonoOver X) := fun f g =>
  ⟨by
    intro h₁ h₂
    apply InducedCategory.hom_ext
    apply Over.OverMorphism.ext
    rw [← cancel_mono g.arrow]; rw [Over.w h₁.hom]; rw [Over.w h₂.hom]⟩

@[reassoc]
/--
theorem `w` / 定理 `w`

English:
theorem w
  given: {f g : MonoOver X} (k : f ⟶ g)
  statement: k.hom.left ≫ g.arrow = f.arrow
  proof: Over.w _

中文:
定理 w
  条件: {f g : MonoOver X} (k : f ⟶ g)
  结论: k.hom.left ≫ g.arrow = f.arrow
  证明: Over.w _

Depends on / 依赖: Over.w
-/
theorem w {f g : MonoOver X} (k : f ⟶ g) : k.hom.left ≫ g.arrow = f.arrow :=
  Over.w _

/--
Definition of `homMk` / `homMk` 的定义

English:
abbreviation homMk
  signature: {f g : MonoOver X} (h : f.obj.left ⟶ g.obj.left)
  body: InducedCategory.homMk (Over.homMk h w)

中文:
缩写 homMk
  签名: {f g : MonoOver X} (h : f.obj.left ⟶ g.obj.left)
  定义体: InducedCategory.homMk (Over.homMk h w)

Depends on / 依赖: InducedCategory, InducedCategory.homMk, Over.homMk, aesop_cat
-/
abbrev homMk {f g : MonoOver X} (h : f.obj.left ⟶ g.obj.left)
    (w : h ≫ g.arrow = f.arrow := by aesop_cat) : f ⟶ g :=
  InducedCategory.homMk (Over.homMk h w)

/-- Convenience constructor for an isomorphism in monomorphisms over `X`. -/
@[simps]
/--
Definition of `isoMk` / `isoMk` 的定义

English:
definition isoMk
  signature: {f g : MonoOver X} (h : f.obj.left ≅ g.obj.left)
  body: homMk h.hom w
  inv := homMk h.inv (by rw [h.inv_comp_eq, w])

中文:
定义 isoMk
  签名: {f g : MonoOver X} (h : f.obj.left ≅ g.obj.left)
  定义体: homMk h.hom w
  inv := homMk h.inv (by rw [h.inv_comp_eq, w])

Depends on / 依赖: cat_disch, h.hom, h.inv, h.inv_comp_eq, inv_comp_eq
-/
def isoMk {f g : MonoOver X} (h : f.obj.left ≅ g.obj.left)
    (w : h.hom ≫ g.arrow = f.arrow := by cat_disch) : f ≅ g where
  hom := homMk h.hom w
  inv := homMk h.inv (by rw [h.inv_comp_eq, w])

/-- If `f : MonoOver X`, then `mk' f.arrow` is of course just `f`, but not definitionally, so we
package it as an isomorphism. -/
@[simps!]
/--
Definition of `mkArrowIso` / `mkArrowIso` 的定义

English:
definition mkArrowIso
  signature: {X : C} (f : MonoOver X)
  body: isoMk (Iso.refl _)

中文:
定义 mkArrowIso
  签名: {X : C} (f : MonoOver X)
  定义体: isoMk (Iso.refl _)

Depends on / 依赖: Iso.refl
-/
def mkArrowIso {X : C} (f : MonoOver X) : mk f.arrow ≅ f :=
  isoMk (Iso.refl _)

instance {A B : MonoOver X} (f : A ⟶ B) [IsIso f] : IsIso f.hom.left :=
  inferInstanceAs (IsIso ((MonoOver.forget _ ⋙ Over.forget _).map f))

/--
lemma `isIso_iff_isIso_hom_left` / 引理 `isIso_iff_isIso_hom_left`

English:
lemma isIso_iff_isIso_hom_left
  given: {A B : MonoOver X} (f : A ⟶ B)
  proof: (isIso_iff_of_reflects_iso _ (MonoOver.forget X ⋙ Over.forget _)).symm

中文:
引理 isIso_iff_isIso_hom_left
  条件: {A B : MonoOver X} (f : A ⟶ B)
  证明: (isIso_iff_of_reflects_iso _ (MonoOver.forget X ⋙ Over.forget _)).symm

Depends on / 依赖: MonoOver, MonoOver.forget, Over.forget, forget, isIso_iff_of_reflects_iso
-/
lemma isIso_iff_isIso_hom_left {A B : MonoOver X} (f : A ⟶ B) :
    IsIso f ↔ IsIso f.hom.left :=
  (isIso_iff_of_reflects_iso _ (MonoOver.forget X ⋙ Over.forget _)).symm

/-- Lift a functor between over categories to a functor between `MonoOver` categories,
given suitable evidence that morphisms are taken to monomorphisms.
-/
@[simps!]
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: {Y : D} (F : Over Y ⥤ Over X)
  body: ObjectProperty.lift _ (forget _ ⋙ F) h

中文:
定义 lift
  签名: {Y : D} (F : Over Y ⥤ Over X)
  定义体: ObjectProperty.lift _ (forget _ ⋙ F) h

Depends on / 依赖: ObjectProperty, ObjectProperty.lift, forget
-/
def lift {Y : D} (F : Over Y ⥤ Over X)
    (h : forall f : MonoOver Y, Mono (F.obj ((MonoOver.forget Y).obj f)).hom) :
    MonoOver Y ⥤ MonoOver X :=
  ObjectProperty.lift _ (forget _ ⋙ F) h

/--
Definition of `liftIso` / `liftIso` 的定义

English:
definition liftIso
  signature: {Y : D} {F₁ F₂ : Over Y ⥤ Over X} (h₁ h₂) (i : F₁ ≅ F₂)
  body: Functor.fullyFaithfulCancelRight (MonoOver.forget X) (isoWhiskerLeft (MonoOver.forget Y) i)

中文:
定义 liftIso
  签名: {Y : D} {F₁ F₂ : Over Y ⥤ Over X} (h₁ h₂) (i : F₁ ≅ F₂)
  定义体: Functor.fullyFaithfulCancelRight (MonoOver.forget X) (isoWhiskerLeft (MonoOver.forget Y) i)

Depends on / 依赖: Functor, Functor.fullyFaithfulCancelRight, MonoOver, MonoOver.forget, forget, fullyFaithfulCancelRight, isoWhiskerLeft
-/
def liftIso {Y : D} {F₁ F₂ : Over Y ⥤ Over X} (h₁ h₂) (i : F₁ ≅ F₂) : lift F₁ h₁ ≅ lift F₂ h₂ :=
  Functor.fullyFaithfulCancelRight (MonoOver.forget X) (isoWhiskerLeft (MonoOver.forget Y) i)

/--
Definition of `liftComp` / `liftComp` 的定义

English:
definition liftComp
  signature: {X Z : C} {Y : D} (F : Over X ⥤ Over Y) (G : Over Y ⥤ Over Z) (h₁ h₂)
  body: Functor.fullyFaithfulCancelRight (MonoOver.forget _) (Iso.refl _)

中文:
定义 liftComp
  签名: {X Z : C} {Y : D} (F : Over X ⥤ Over Y) (G : Over Y ⥤ Over Z) (h₁ h₂)
  定义体: Functor.fullyFaithfulCancelRight (MonoOver.forget _) (Iso.refl _)

Depends on / 依赖: Functor, Functor.fullyFaithfulCancelRight, Iso.refl, MonoOver, MonoOver.forget, forget, fullyFaithfulCancelRight
-/
def liftComp {X Z : C} {Y : D} (F : Over X ⥤ Over Y) (G : Over Y ⥤ Over Z) (h₁ h₂) :
    lift F h₁ ⋙ lift G h₂ ≅ lift (F ⋙ G) fun f => h₂ ⟨_, h₁ f⟩ :=
  Functor.fullyFaithfulCancelRight (MonoOver.forget _) (Iso.refl _)

/--
Definition of `liftId` / `liftId` 的定义

English:
definition liftId
  signature: : (lift (𝟭 (Over X)) fun f => f.2) ≅ 𝟭 _
  body: Functor.fullyFaithfulCancelRight (MonoOver.forget _) (Iso.refl _)

@[simp]

中文:
定义 liftId
  签名: : (lift (𝟭 (Over X)) fun f => f.2) ≅ 𝟭 _
  定义体: Functor.fullyFaithfulCancelRight (MonoOver.forget _) (Iso.refl _)

@[simp]

Depends on / 依赖: Functor, Functor.fullyFaithfulCancelRight, Iso.refl, MonoOver, MonoOver.forget, forget, fullyFaithfulCancelRight
-/
def liftId : (lift (𝟭 (Over X)) fun f => f.2) ≅ 𝟭 _ :=
  Functor.fullyFaithfulCancelRight (MonoOver.forget _) (Iso.refl _)

@[simp]
/--
theorem `lift_comm` / 定理 `lift_comm`

English:
theorem lift_comm
  statement: (F : Over Y ⥤ Over X)
  proof: rfl

@[simp]

中文:
定理 lift_comm
  结论: (F : Over Y ⥤ Over X)
  证明: rfl

@[simp]
-/
theorem lift_comm (F : Over Y ⥤ Over X)
    (h : forall f : MonoOver Y, Mono (F.obj ((MonoOver.forget Y).obj f)).hom) :
    lift F h ⋙ MonoOver.forget X = MonoOver.forget Y ⋙ F :=
  rfl

@[simp]
/--
theorem `lift_obj_arrow` / 定理 `lift_obj_arrow`

English:
theorem lift_obj_arrow
  statement: {Y : D} (F : Over Y ⥤ Over X)
  proof: rfl

中文:
定理 lift_obj_arrow
  结论: {Y : D} (F : Over Y ⥤ Over X)
  证明: rfl
-/
theorem lift_obj_arrow {Y : D} (F : Over Y ⥤ Over X)
    (h : forall f : MonoOver Y, Mono (F.obj ((MonoOver.forget Y).obj f)).hom) (f : MonoOver Y) :
    ((lift F h).obj f).arrow = (F.obj ((forget Y).obj f)).hom :=
  rfl

/--
Definition of `slice` / `slice` 的定义

English:
definition slice
  signature: {A : C} {f : Over A}
  body: MonoOver.lift f.iteratedSliceEquiv.functor h₁
  inverse := MonoOver.lift f.iteratedSliceEquiv.inverse h₂
  unitIso :=
    MonoOver.liftId.symm ≪≫
      MonoOver.liftIso _ _ f.iteratedSliceEquiv.unitIso ≪≫ (MonoOver.liftComp _ _ _ _).symm
  counitIso :=
    MonoOver.liftComp _ _ _ _ ≪≫
      MonoOver.liftIso _ _ f.iteratedSliceEquiv.counitIso ≪≫ MonoOver.liftId

中文:
定义 slice
  签名: {A : C} {f : Over A}
  定义体: MonoOver.lift f.iteratedSliceEquiv.functor h₁
  inverse := MonoOver.lift f.iteratedSliceEquiv.inverse h₂
  unitIso :=
    MonoOver.liftId.symm ≪≫
      MonoOver.liftIso _ _ f.iteratedSliceEquiv.unitIso ≪≫ (MonoOver.liftComp _ _ _ _).symm
  counitIso :=
    MonoOver.liftComp _ _ _ _ ≪≫
      MonoOver.liftIso _ _ f.iteratedSliceEquiv.counitIso ≪≫ MonoOver.liftId

Depends on / 依赖: MonoOver, MonoOver.lift, f.iteratedSliceEquiv.functor, functor, iteratedSliceEquiv
-/
def slice {A : C} {f : Over A}
    (h₁ : forall (g : MonoOver f),
      Mono ((Over.iteratedSliceEquiv f).functor.obj ((forget f).obj g)).hom)
    (h₂ : forall (g : MonoOver f.left),
      Mono ((Over.iteratedSliceEquiv f).inverse.obj ((forget f.left).obj g)).hom) :
    MonoOver f ≌ MonoOver f.left where
  functor := MonoOver.lift f.iteratedSliceEquiv.functor h₁
  inverse := MonoOver.lift f.iteratedSliceEquiv.inverse h₂
  unitIso :=
    MonoOver.liftId.symm ≪≫
      MonoOver.liftIso _ _ f.iteratedSliceEquiv.unitIso ≪≫ (MonoOver.liftComp _ _ _ _).symm
  counitIso :=
    MonoOver.liftComp _ _ _ _ ≪≫
      MonoOver.liftIso _ _ f.iteratedSliceEquiv.counitIso ≪≫ MonoOver.liftId

section Limits

variable {J : Type u₃} [Category.{v₃} J] (X : C)

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (Over.isMono X).IsClosedUnderLimitsOfShape J
  body: fun F ⟨p, hp⟩ => ⟨fun g h e => by
    refine (WithTerminal.isLimitEquiv.invFun p.isLimit).hom_ext (fun j => ?_)
    cases j with
    | of j => have := hp j; rw [← cancel_mono ((p.diag.obj j).hom)]; simpa
    | star => exact e⟩

中文:
实例 :
  签名: (Over.isMono X).是ClosedUnderLimitsOfShape J
  定义体: fun F ⟨p, hp⟩ => ⟨fun g h e => by
    refine (WithTerminal.isLimitEquiv.invFun p.isLimit).hom_ext (fun j => ?_)
    cases j with
    | of j => have := hp j; rw [← cancel_mono ((p.diag.obj j).hom)]; simpa
    | star => exact e⟩

Depends on / 依赖: WithTerminal, WithTerminal.isLimitEquiv.invFun, cancel_mono, hom_ext, invFun, isLimit, isLimitEquiv, p.diag.obj, p.isLimit
-/
instance : (Over.isMono X).IsClosedUnderLimitsOfShape J where
  limitsOfShape_le := fun F ⟨p, hp⟩ => ⟨fun g h e => by
    refine (WithTerminal.isLimitEquiv.invFun p.isLimit).hom_ext (fun j => ?_)
    cases j with
    | of j => have := hp j; rw [← cancel_mono ((p.diag.obj j).hom)]; simpa
    | star => exact e⟩

/--
Instance `hasLimit` / 实例 `hasLimit`

English:
instance hasLimit
  signature: (F : J ⥤ MonoOver X) [HasLimit (F ⋙ (Over.isMono X).ι)]
  body: hasLimit_of_closedUnderLimits _ _ _

中文:
实例 hasLimit
  签名: (F : J ⥤ MonoOver X) [有极限 (F ⋙ (Over.isMono X).ι)]
  定义体: hasLimit_of_closedUnderLimits _ _ _

Depends on / 依赖: hasLimit_of_closedUnderLimits
-/
instance hasLimit (F : J ⥤ MonoOver X) [HasLimit (F ⋙ (Over.isMono X).ι)] :
    HasLimit F :=
  hasLimit_of_closedUnderLimits _ _ _

/--
Instance `hasLimitsOfShape` / 实例 `hasLimitsOfShape`

English:
instance hasLimitsOfShape
  signature: [HasLimitsOfShape J (Over X)]

中文:
实例 hasLimitsOfShape
  签名: [有形状极限 J (Over X)]
-/
instance hasLimitsOfShape [HasLimitsOfShape J (Over X)] :
    HasLimitsOfShape J (MonoOver X) where

/--
Instance `hasFiniteLimits` / 实例 `hasFiniteLimits`

English:
instance hasFiniteLimits
  signature: [HasFiniteLimits (Over X)]
  body: inferInstance

中文:
实例 hasFiniteLimits
  签名: [有有限极限 (Over X)]
  定义体: inferInstance
-/
instance hasFiniteLimits [HasFiniteLimits (Over X)] : HasFiniteLimits (MonoOver X) where
  out _ _ _ := inferInstance

/--
Instance `hasLimitsOfSize` / 实例 `hasLimitsOfSize`

English:
instance hasLimitsOfSize
  signature: [HasLimitsOfSize.{w, w'} (Over X)]

中文:
实例 hasLimitsOfSize
  签名: [有LimitsOfSize.{w, w'} (Over X)]
-/
instance hasLimitsOfSize [HasLimitsOfSize.{w, w'} (Over X)] :
    HasLimitsOfSize.{w, w'} (MonoOver X) where

end Limits

section Colimits

variable [HasCoproducts C] [HasStrongEpiMonoFactorisations C] {J : Type u₂} [Category.{v₂} J]

/--
Definition of `strongEpiMonoFactorisationSigmaDesc` / `strongEpiMonoFactorisationSigmaDesc` 的定义

English:
definition strongEpiMonoFactorisationSigmaDesc
  signature: (F : J ⥤ MonoOver Y)
  body: Classical.choice HasStrongEpiMonoFactorisations.has_fac (Sigma.desc fun i => (F.obj i).arrow)

中文:
定义 strongEpiMonoFactorisationSigmaDesc
  签名: (F : J ⥤ MonoOver Y)
  定义体: Classical.choice HasStrongEpiMonoFactorisations.has_fac (Sigma.desc fun i => (F.obj i).arrow)

Depends on / 依赖: Classical, Classical.choice, F.obj, HasStrongEpiMonoFactorisations, HasStrongEpiMonoFactorisations.has_fac, Sigma.desc, choice, has_fac
-/
def strongEpiMonoFactorisationSigmaDesc (F : J ⥤ MonoOver Y) :
    StrongEpiMonoFactorisation (Sigma.desc fun i => (F.obj i).arrow) :=
Classical.choice HasStrongEpiMonoFactorisations.has_fac (Sigma.desc fun i => (F.obj i).arrow)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `coconeOfHasStrongEpiMonoFactorisation` / `coconeOfHasStrongEpiMonoFactorisation` 的定义

English:
definition coconeOfHasStrongEpiMonoFactorisation
  signature: (F : J ⥤ MonoOver Y)
  body: MonoOver.mk ((strongEpiMonoFactorisationSigmaDesc F).m)
  ι.app j := homMk (Sigma.ι (fun i => (F.obj i : C)) j ≫
    (strongEpiMonoFactorisationSigmaDesc F).e)

中文:
定义 coconeOfHasStrongEpiMonoFactorisation
  签名: (F : J ⥤ MonoOver Y)
  定义体: MonoOver.mk ((strongEpiMonoFactorisationSigmaDesc F).m)
  ι.app j := homMk (Sigma.ι (fun i => (F.obj i : C)) j ≫
    (strongEpiMonoFactorisationSigmaDesc F).e)

Depends on / 依赖: MonoOver, MonoOver.mk, strongEpiMonoFactorisationSigmaDesc
-/
def coconeOfHasStrongEpiMonoFactorisation (F : J ⥤ MonoOver Y) :
    Cocone F where
  pt := MonoOver.mk ((strongEpiMonoFactorisationSigmaDesc F).m)
  ι.app j := homMk (Sigma.ι (fun i => (F.obj i : C)) j ≫
    (strongEpiMonoFactorisationSigmaDesc F).e)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `commSqOfHasStrongEpiMonoFactorisation` / 引理 `commSqOfHasStrongEpiMonoFactorisation`

English:
lemma commSqOfHasStrongEpiMonoFactorisation
  given: (F : J ⥤ MonoOver Y) (c : Cocone F)

中文:
引理 commSqOfHasStrongEpiMonoFactorisation
  条件: (F : J ⥤ MonoOver Y) (c : 余锥 F)
-/
lemma commSqOfHasStrongEpiMonoFactorisation (F : J ⥤ MonoOver Y) (c : Cocone F) :
    CommSq (Sigma.desc fun i => (c.ι.app i).hom.left) (strongEpiMonoFactorisationSigmaDesc F).e
      c.pt.arrow (strongEpiMonoFactorisationSigmaDesc F).m where

/--
Definition of `liftStructOfHasStrongEpiMonoFactorisation` / `liftStructOfHasStrongEpiMonoFactorisation` 的定义

English:
definition liftStructOfHasStrongEpiMonoFactorisation
  signature: (F : J ⥤ MonoOver Y) (c : Cocone F)
  body: Classical.choice
    (((strongEpiMonoFactorisationSigmaDesc F).e_strong_epi.llp _).sq_hasLift
      (commSqOfHasStrongEpiMonoFactorisation F c)).exists_lift

中文:
定义 liftStructOfHasStrongEpiMonoFactorisation
  签名: (F : J ⥤ MonoOver Y) (c : 余锥 F)
  定义体: Classical.choice
    (((strongEpiMonoFactorisationSigmaDesc F).e_strong_epi.llp _).sq_hasLift
      (commSqOfHasStrongEpiMonoFactorisation F c)).exists_lift

Depends on / 依赖: Classical, Classical.choice, choice, commSqOfHasStrongEpiMonoFactorisation, e_strong_epi, e_strong_epi.llp, exists_lift, sq_hasLift, strongEpiMonoFactorisationSigmaDesc
-/
def liftStructOfHasStrongEpiMonoFactorisation (F : J ⥤ MonoOver Y) (c : Cocone F) :
    (commSqOfHasStrongEpiMonoFactorisation F c).LiftStruct :=
  Classical.choice
    (((strongEpiMonoFactorisationSigmaDesc F).e_strong_epi.llp _).sq_hasLift
      (commSqOfHasStrongEpiMonoFactorisation F c)).exists_lift

/--
Definition of `isColimitCoconeOfHasStrongEpiMonoFactorisation` / `isColimitCoconeOfHasStrongEpiMonoFactorisation` 的定义

English:
definition isColimitCoconeOfHasStrongEpiMonoFactorisation
  signature: (F : J ⥤ MonoOver Y)
  body: homMk (liftStructOfHasStrongEpiMonoFactorisation F c).l
    (liftStructOfHasStrongEpiMonoFactorisation F c).fac_right

中文:
定义 isColimitCoconeOfHasStrongEpiMonoFactorisation
  签名: (F : J ⥤ MonoOver Y)
  定义体: homMk (liftStructOfHasStrongEpiMonoFactorisation F c).l
    (liftStructOfHasStrongEpiMonoFactorisation F c).fac_right

Depends on / 依赖: liftStructOfHasStrongEpiMonoFactorisation
-/
def isColimitCoconeOfHasStrongEpiMonoFactorisation (F : J ⥤ MonoOver Y) :
    IsColimit (coconeOfHasStrongEpiMonoFactorisation F) where
  desc c := homMk (liftStructOfHasStrongEpiMonoFactorisation F c).l
    (liftStructOfHasStrongEpiMonoFactorisation F c).fac_right

/--
Instance `hasColimitsOfSize_of_hasStrongEpiMonoFactorisations` / 实例 `hasColimitsOfSize_of_hasStrongEpiMonoFactorisations`

English:
instance hasColimitsOfSize_of_hasStrongEpiMonoFactorisations
  signature: :
  body: ⟨fun F =>
      ⟨coconeOfHasStrongEpiMonoFactorisation F, isColimitCoconeOfHasStrongEpiMonoFactorisation F⟩⟩

中文:
实例 hasColimitsOfSize_of_hasStrongEpiMonoFactorisations
  签名: :
  定义体: ⟨fun F =>
      ⟨coconeOfHasStrongEpiMonoFactorisation F, isColimitCoconeOfHasStrongEpiMonoFactorisation F⟩⟩

Depends on / 依赖: coconeOfHasStrongEpiMonoFactorisation, isColimitCoconeOfHasStrongEpiMonoFactorisation
-/
instance hasColimitsOfSize_of_hasStrongEpiMonoFactorisations :
    HasColimitsOfSize.{w, w'} (MonoOver Y) where
  has_colimits_of_shape _ _ :=
    ⟨fun F =>
      ⟨coconeOfHasStrongEpiMonoFactorisation F, isColimitCoconeOfHasStrongEpiMonoFactorisation F⟩⟩

end Colimits

section Pullback

variable [HasPullbacks C]

/--
Definition of `pullback` / `pullback` 的定义

English:
definition pullback
  signature: (f : X ⟶ Y)
  body: MonoOver.lift (Over.pullback f) (fun g => by
    have : Mono ((forget Y).obj g).hom := (inferInstance : Mono g.arrow)
    apply pullback.snd_of_mono)

中文:
定义 pullback
  签名: (f : X ⟶ Y)
  定义体: MonoOver.lift (Over.pullback f) (fun g => by
    have : Mono ((forget Y).obj g).hom := (inferInstance : Mono g.arrow)
    apply pullback.snd_of_mono)

Depends on / 依赖: MonoOver, MonoOver.lift, Over.pullback, forget, g.arrow, pullback, pullback.snd_of_mono, snd_of_mono
-/
def pullback (f : X ⟶ Y) : MonoOver Y ⥤ MonoOver X :=
  MonoOver.lift (Over.pullback f) (fun g => by
    have : Mono ((forget Y).obj g).hom := (inferInstance : Mono g.arrow)
    apply pullback.snd_of_mono)

/--
Definition of `pullbackComp` / `pullbackComp` 的定义

English:
definition pullbackComp
  signature: (f : X ⟶ Y) (g : Y ⟶ Z)
  body: liftIso _ _ (Over.pullbackComp _ _) ≪≫ (liftComp _ _ _ _).symm

中文:
定义 pullbackComp
  签名: (f : X ⟶ Y) (g : Y ⟶ Z)
  定义体: liftIso _ _ (Over.pullbackComp _ _) ≪≫ (liftComp _ _ _ _).symm

Depends on / 依赖: Over.pullbackComp, liftComp, liftIso, pullbackComp
-/
def pullbackComp (f : X ⟶ Y) (g : Y ⟶ Z) : pullback (f ≫ g) ≅ pullback g ⋙ pullback f :=
  liftIso _ _ (Over.pullbackComp _ _) ≪≫ (liftComp _ _ _ _).symm

/--
Definition of `pullbackId` / `pullbackId` 的定义

English:
definition pullbackId
  signature: : pullback (𝟙 X) ≅ 𝟭 _
  body: liftIso _ _ Over.pullbackId ≪≫ liftId

@[simp]

中文:
定义 pullbackId
  签名: : pullback (𝟙 X) ≅ 𝟭 _
  定义体: liftIso _ _ Over.pullbackId ≪≫ liftId

@[simp]

Depends on / 依赖: Over.pullbackId, liftId, liftIso, pullbackId
-/
def pullbackId : pullback (𝟙 X) ≅ 𝟭 _ :=
  liftIso _ _ Over.pullbackId ≪≫ liftId

@[simp]
/--
theorem `pullback_obj_left` / 定理 `pullback_obj_left`

English:
theorem pullback_obj_left
  given: (f : X ⟶ Y) (g : MonoOver Y)
  proof: rfl

@[simp]

中文:
定理 pullback_obj_left
  条件: (f : X ⟶ Y) (g : MonoOver Y)
  证明: rfl

@[simp]
-/
theorem pullback_obj_left (f : X ⟶ Y) (g : MonoOver Y) :
    ((pullback f).obj g : C) = Limits.pullback g.arrow f :=
  rfl

@[simp]
/--
theorem `pullback_obj_arrow` / 定理 `pullback_obj_arrow`

English:
theorem pullback_obj_arrow
  given: (f : X ⟶ Y) (g : MonoOver Y)
  proof: rfl

中文:
定理 pullback_obj_arrow
  条件: (f : X ⟶ Y) (g : MonoOver Y)
  证明: rfl
-/
theorem pullback_obj_arrow (f : X ⟶ Y) (g : MonoOver Y) :
    ((pullback f).obj g).arrow = pullback.snd _ _ :=
  rfl

end Pullback

section IsPullback

/--
Definition of `pullbackObjIsoOfIsPullback` / `pullbackObjIsoOfIsPullback` 的定义

English:
definition pullbackObjIsoOfIsPullback
  signature: [HasPullbacks C] {X Y : C} (f : Y ⟶ X) (S : MonoOver X)
  body: isoMk ((IsPullback.isoPullback h).symm)

中文:
定义 pullbackObjIsoOfIsPullback
  签名: [有Pullbacks C] {X Y : C} (f : Y ⟶ X) (S : MonoOver X)
  定义体: isoMk ((IsPullback.isoPullback h).symm)

Depends on / 依赖: IsPullback, IsPullback.isoPullback, isoPullback
-/
def pullbackObjIsoOfIsPullback [HasPullbacks C] {X Y : C} (f : Y ⟶ X) (S : MonoOver X)
    (T : MonoOver Y) (f' : (T : C) ⟶ (S : C))
    (h : IsPullback f' T.arrow S.arrow f) :
    (pullback f).obj S ≅ T :=
  isoMk ((IsPullback.isoPullback h).symm)

end IsPullback

section Map

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : X ⟶ Y) [Mono f]
  body: lift (Over.map f) fun g => mono_comp g.arrow f

中文:
定义 map
  签名: (f : X ⟶ Y) [单态射 f]
  定义体: lift (Over.map f) fun g => mono_comp g.arrow f

Depends on / 依赖: Over.map, g.arrow, mono_comp
-/
def map (f : X ⟶ Y) [Mono f] : MonoOver X ⥤ MonoOver Y :=
  lift (Over.map f) fun g => mono_comp g.arrow f

/--
Definition of `mapComp` / `mapComp` 的定义

English:
definition mapComp
  signature: (f : X ⟶ Y) (g : Y ⟶ Z) [Mono f] [Mono g]
  body: liftIso _ _ (Over.mapComp _ _) ≪≫ (liftComp _ _ _ _).symm

中文:
定义 mapComp
  签名: (f : X ⟶ Y) (g : Y ⟶ Z) [单态射 f] [单态射 g]
  定义体: liftIso _ _ (Over.mapComp _ _) ≪≫ (liftComp _ _ _ _).symm

Depends on / 依赖: Over.mapComp, liftComp, liftIso, mapComp
-/
def mapComp (f : X ⟶ Y) (g : Y ⟶ Z) [Mono f] [Mono g] : map (f ≫ g) ≅ map f ⋙ map g :=
  liftIso _ _ (Over.mapComp _ _) ≪≫ (liftComp _ _ _ _).symm

variable (X) in
/--
Definition of `mapId` / `mapId` 的定义

English:
definition mapId
  signature: : map (𝟙 X) ≅ 𝟭 _
  body: liftIso _ _ (Over.mapId X) ≪≫ liftId

@[simp]

中文:
定义 mapId
  签名: : map (𝟙 X) ≅ 𝟭 _
  定义体: liftIso _ _ (Over.mapId X) ≪≫ liftId

@[simp]

Depends on / 依赖: Over.mapId, liftId, liftIso
-/
def mapId : map (𝟙 X) ≅ 𝟭 _ :=
  liftIso _ _ (Over.mapId X) ≪≫ liftId

@[simp]
/--
theorem `map_obj_left` / 定理 `map_obj_left`

English:
theorem map_obj_left
  given: (f : X ⟶ Y) [Mono f] (g : MonoOver X)
  statement: ((map f).obj g : C) = g.obj.left
  proof: rfl

@[simp]

中文:
定理 map_obj_left
  条件: (f : X ⟶ Y) [单态射 f] (g : MonoOver X)
  结论: ((map f).obj g : C) = g.obj.left
  证明: rfl

@[simp]
-/
theorem map_obj_left (f : X ⟶ Y) [Mono f] (g : MonoOver X) : ((map f).obj g : C) = g.obj.left :=
  rfl

@[simp]
/--
theorem `map_obj_arrow` / 定理 `map_obj_arrow`

English:
theorem map_obj_arrow
  given: (f : X ⟶ Y) [Mono f] (g : MonoOver X)
  statement: ((map f).obj g).arrow = g.arrow ≫ f
  proof: rfl

中文:
定理 map_obj_arrow
  条件: (f : X ⟶ Y) [单态射 f] (g : MonoOver X)
  结论: ((map f).obj g).arrow = g.arrow ≫ f
  证明: rfl
-/
theorem map_obj_arrow (f : X ⟶ Y) [Mono f] (g : MonoOver X) : ((map f).obj g).arrow = g.arrow ≫ f :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `full_map` / 实例 `full_map`

English:
instance full_map
  signature: (f : X ⟶ Y) [Mono f]
  body: by
    refine ⟨homMk e.hom.left ?_, rfl⟩
    · rw [← cancel_mono f, assoc]
      apply w e

中文:
实例 full_map
  签名: (f : X ⟶ Y) [单态射 f]
  定义体: by
    refine ⟨homMk e.hom.left ?_, rfl⟩
    · rw [← cancel_mono f, assoc]
      apply w e

Depends on / 依赖: cancel_mono, e.hom.left
-/
instance full_map (f : X ⟶ Y) [Mono f] : Functor.Full (map f) where
  map_surjective {g h} e := by
    refine ⟨homMk e.hom.left ?_, rfl⟩
    · rw [← cancel_mono f, assoc]
      apply w e

/--
Instance `faithful_map` / 实例 `faithful_map`

English:
instance faithful_map
  signature: (f : X ⟶ Y) [Mono f]

中文:
实例 faithful_map
  签名: (f : X ⟶ Y) [单态射 f]
-/
instance faithful_map (f : X ⟶ Y) [Mono f] : Functor.Faithful (map f) where

/-- Isomorphic objects have equivalent `MonoOver` categories.
-/
@[simps]
/--
Definition of `mapIso` / `mapIso` 的定义

English:
definition mapIso
  signature: {A B : C} (e : A ≅ B)
  body: map e.hom
  inverse := map e.inv
  unitIso := ((mapComp _ _).symm ≪≫ eqToIso (by simp) ≪≫ (mapId _)).symm
  counitIso := (mapComp _ _).symm ≪≫ eqToIso (by simp) ≪≫ (mapId _)

中文:
定义 mapIso
  签名: {A B : C} (e : A ≅ B)
  定义体: map e.hom
  inverse := map e.inv
  unitIso := ((mapComp _ _).symm ≪≫ eqToIso (by simp) ≪≫ (mapId _)).symm
  counitIso := (mapComp _ _).symm ≪≫ eqToIso (by simp) ≪≫ (mapId _)

Depends on / 依赖: e.hom
-/
def mapIso {A B : C} (e : A ≅ B) : MonoOver A ≌ MonoOver B where
  functor := map e.hom
  inverse := map e.inv
  unitIso := ((mapComp _ _).symm ≪≫ eqToIso (by simp) ≪≫ (mapId _)).symm
  counitIso := (mapComp _ _).symm ≪≫ eqToIso (by simp) ≪≫ (mapId _)

section

variable (X)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- An equivalence of categories `e` between `C` and `D` induces an equivalence between
`MonoOver X` and `MonoOver (e.functor.obj X)` whenever `X` is an object of `C`. -/
@[simps]
/--
Definition of `congr` / `congr` 的定义

English:
definition congr
  signature: (e : C ≌ D)
  body: lift (Over.post e.functor) fun f => by
      dsimp
      infer_instance
  inverse :=
    (lift (Over.post e.inverse) fun f => by
        dsimp
        infer_instance) ⋙
      (mapIso (e.unitIso.symm.app X)).functor
  unitIso := NatIso.ofComponents fun Y => isoMk (e.unitIso.app Y)
  counitIso := NatIso.ofComponents fun Y => isoMk (e.counitIso.app Y)

中文:
定义 congr
  签名: (e : C ≌ D)
  定义体: lift (Over.post e.functor) fun f => by
      dsimp
      infer_instance
  inverse :=
    (lift (Over.post e.inverse) fun f => by
        dsimp
        infer_instance) ⋙
      (mapIso (e.unitIso.symm.app X)).functor
  unitIso := NatIso.ofComponents fun Y => isoMk (e.unitIso.app Y)
  counitIso := NatIso.ofComponents fun Y => isoMk (e.counitIso.app Y)

Depends on / 依赖: NatIso, NatIso.ofComponents, Over.post, counitIso, e.counitIso.app, e.functor, e.inverse, e.unitIso.app, e.unitIso.symm.app, functor, infer_instance, inverse, mapIso, ofComponents, unitIso
-/
def congr (e : C ≌ D) : MonoOver X ≌ MonoOver (e.functor.obj X) where
  functor :=
    lift (Over.post e.functor) fun f => by
      dsimp
      infer_instance
  inverse :=
    (lift (Over.post e.inverse) fun f => by
        dsimp
        infer_instance) ⋙
      (mapIso (e.unitIso.symm.app X)).functor
  unitIso := NatIso.ofComponents fun Y => isoMk (e.unitIso.app Y)
  counitIso := NatIso.ofComponents fun Y => isoMk (e.counitIso.app Y)

end

section

variable [HasPullbacks C]

/--
Definition of `mapPullbackAdj` / `mapPullbackAdj` 的定义

English:
definition mapPullbackAdj
  signature: (f : X ⟶ Y) [Mono f]
  body: (Over.mapPullbackAdj f).restrictFullyFaithful (fullyFaithfulForget X) (fullyFaithfulForget Y)
    (Iso.refl _) (Iso.refl _)

中文:
定义 mapPullbackAdj
  签名: (f : X ⟶ Y) [单态射 f]
  定义体: (Over.mapPullbackAdj f).restrictFullyFaithful (fullyFaithfulForget X) (fullyFaithfulForget Y)
    (Iso.refl _) (Iso.refl _)

Depends on / 依赖: Iso.refl, Over.mapPullbackAdj, fullyFaithfulForget, mapPullbackAdj, restrictFullyFaithful
-/
def mapPullbackAdj (f : X ⟶ Y) [Mono f] : map f ⊣ pullback f :=
  (Over.mapPullbackAdj f).restrictFullyFaithful (fullyFaithfulForget X) (fullyFaithfulForget Y)
    (Iso.refl _) (Iso.refl _)

/--
Definition of `pullbackMapSelf` / `pullbackMapSelf` 的定义

English:
definition pullbackMapSelf
  signature: (f : X ⟶ Y) [Mono f]
  body: (asIso (MonoOver.mapPullbackAdj f).unit).symm

中文:
定义 pullbackMapSelf
  签名: (f : X ⟶ Y) [单态射 f]
  定义体: (asIso (MonoOver.mapPullbackAdj f).unit).symm

Depends on / 依赖: MonoOver, MonoOver.mapPullbackAdj, mapPullbackAdj
-/
def pullbackMapSelf (f : X ⟶ Y) [Mono f] : map f ⋙ pullback f ≅ 𝟭 _ :=
  (asIso (MonoOver.mapPullbackAdj f).unit).symm

end

end Map

section Image

variable (f : X ⟶ Y) [HasImage f]

/--
Definition of `imageMonoOver` / `imageMonoOver` 的定义

English:
definition imageMonoOver
  signature: (f : X ⟶ Y) [HasImage f]
  body: MonoOver.mk (image.ι f)

@[simp]

中文:
定义 imageMonoOver
  签名: (f : X ⟶ Y) [有像 f]
  定义体: MonoOver.mk (image.ι f)

@[simp]

Depends on / 依赖: MonoOver, MonoOver.mk
-/
def imageMonoOver (f : X ⟶ Y) [HasImage f] : MonoOver Y :=
  MonoOver.mk (image.ι f)

@[simp]
/--
theorem `imageMonoOver_arrow` / 定理 `imageMonoOver_arrow`

English:
theorem imageMonoOver_arrow
  given: (f : X ⟶ Y) [HasImage f]
  statement: (imageMonoOver f).arrow = image.ι f
  proof: rfl

中文:
定理 imageMonoOver_arrow
  条件: (f : X ⟶ Y) [有像 f]
  结论: (imageMonoOver f).arrow = 像.ι f
  证明: rfl
-/
theorem imageMonoOver_arrow (f : X ⟶ Y) [HasImage f] : (imageMonoOver f).arrow = image.ι f :=
  rfl

end Image

section Image

variable [HasImages C]

/-- Taking the image of a morphism gives a functor `Over X ⥤ MonoOver X`.
-/
@[simps]
/--
Definition of `image` / `image` 的定义

English:
definition image
  signature: : Over X ⥤ MonoOver X where
  body: imageMonoOver f.hom
  map {f g} k := by
    apply (forget X).preimage _
    apply Over.homMk _ _
    · exact
        image.lift
          { I := Limits.image _
            m := image.ι g.hom
            e := k.left ≫ factorThruImage g.hom }
    · apply image.lift_fac

中文:
定义 像
  签名: : Over X ⥤ MonoOver X where
  定义体: imageMonoOver f.hom
  map {f g} k := by
    apply (forget X).preimage _
    apply Over.homMk _ _
    · exact
        image.lift
          { I := Limits.image _
            m := image.ι g.hom
            e := k.left ≫ factorThruImage g.hom }
    · apply image.lift_fac

Depends on / 依赖: f.hom, imageMonoOver
-/
def image : Over X ⥤ MonoOver X where
  obj f := imageMonoOver f.hom
  map {f g} k := by
    apply (forget X).preimage _
    apply Over.homMk _ _
    · exact
        image.lift
          { I := Limits.image _
            m := image.ι g.hom
            e := k.left ≫ factorThruImage g.hom }
    · apply image.lift_fac

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `imageForgetAdj` / `imageForgetAdj` 的定义

English:
definition imageForgetAdj
  signature: : image ⊣ forget X
  body: Adjunction.mkOfHomEquiv
    { homEquiv := fun f g =>
        { toFun := fun k => by
            apply Over.homMk (factorThruImage f.hom ≫ k.hom.left) _
            rw [assoc]; rw [Over.w k.hom]
            apply image.fac
          invFun k :=
            homMk
              (image.lift
                { I := g.obj.left
                  m := g.arrow
                  e := k.left
                  fac := Over.w k }) (image.lift_fac _)
          left_inv _ := Subsingleton.elim _ _
          right_inv k := by ext; simp } }

中文:
定义 imageForgetAdj
  签名: : 像 ⊣ forget X
  定义体: Adjunction.mkOfHomEquiv
    { homEquiv := fun f g =>
        { toFun := fun k => by
            apply Over.homMk (factorThruImage f.hom ≫ k.hom.left) _
            rw [assoc]; rw [Over.w k.hom]
            apply image.fac
          invFun k :=
            homMk
              (image.lift
                { I := g.obj.left
                  m := g.arrow
                  e := k.left
                  fac := Over.w k }) (image.lift_fac _)
          left_inv _ := Subsingleton.elim _ _
          right_inv k := by ext; simp } }

Depends on / 依赖: Adjunction, Adjunction.mkOfHomEquiv, Over.homMk, Over.w, Subsingleton, Subsingleton.elim, f.hom, factorThruImage, g.arrow, g.obj.left, homEquiv, image.fac, image.lift, image.lift_fac, invFun, k.hom, k.hom.left, k.left, left_inv, lift_fac
-/
def imageForgetAdj : image ⊣ forget X :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun f g =>
        { toFun := fun k => by
            apply Over.homMk (factorThruImage f.hom ≫ k.hom.left) _
            rw [assoc]; rw [Over.w k.hom]
            apply image.fac
          invFun k :=
            homMk
              (image.lift
                { I := g.obj.left
                  m := g.arrow
                  e := k.left
                  fac := Over.w k }) (image.lift_fac _)
          left_inv _ := Subsingleton.elim _ _
          right_inv k := by ext; simp } }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget X).IsRightAdjoint
  body: ⟨_, ⟨imageForgetAdj⟩⟩

中文:
实例 :
  签名: (forget X).是右伴随
  定义体: ⟨_, ⟨imageForgetAdj⟩⟩

Depends on / 依赖: imageForgetAdj
-/
instance : (forget X).IsRightAdjoint :=
  ⟨_, ⟨imageForgetAdj⟩⟩

/--
Instance `reflective` / 实例 `reflective`

English:
instance reflective
  signature: : Reflective (forget X) where
  body: image
  adj := imageForgetAdj

中文:
实例 reflective
  签名: : 反射 (forget X) where
  定义体: image
  adj := imageForgetAdj
-/
instance reflective : Reflective (forget X) where
  L := image
  adj := imageForgetAdj

/--
Definition of `forgetImage` / `forgetImage` 的定义

English:
definition forgetImage
  signature: : forget X ⋙ image ≅ 𝟭 (MonoOver X)
  body: asIso (Adjunction.counit imageForgetAdj)

中文:
定义 forgetImage
  签名: : forget X ⋙ 像 ≅ 𝟭 (MonoOver X)
  定义体: asIso (Adjunction.counit imageForgetAdj)

Depends on / 依赖: Adjunction, Adjunction.counit, counit, imageForgetAdj
-/
def forgetImage : forget X ⋙ image ≅ 𝟭 (MonoOver X) :=
  asIso (Adjunction.counit imageForgetAdj)

end Image

section Exists

variable [HasImages C]

/--
Definition of `«exists»` / `«exists»` 的定义

English:
definition «exists»
  signature: (f : X ⟶ Y)
  body: forget _ ⋙ Over.map f ⋙ image

中文:
定义 «存在»
  签名: (f : X ⟶ Y)
  定义体: forget _ ⋙ Over.map f ⋙ image
-/
def «exists» (f : X ⟶ Y) : MonoOver X ⥤ MonoOver Y :=
  forget _ ⋙ Over.map f ⋙ image

/--
Instance `faithful_exists` / 实例 `faithful_exists`

English:
instance faithful_exists
  signature: (f : X ⟶ Y)

中文:
实例 faithful_存在
  签名: (f : X ⟶ Y)
-/
instance faithful_exists (f : X ⟶ Y) : Functor.Faithful («exists» f) where

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `existsIsoMap` / `existsIsoMap` 的定义

English:
definition existsIsoMap
  signature: (f : X ⟶ Y) [Mono f]
  body: NatIso.ofComponents (by
    intro Z
    suffices (forget _).obj ((«exists» f).obj Z) ≅ (forget _).obj ((map f).obj Z) by
      apply (forget _).preimageIso this
    apply Over.isoMk _ _
    · apply imageMonoIsoSource (Z.arrow ≫ f)
    · apply imageMonoIsoSource_hom_self)

中文:
定义 存在IsoMap
  签名: (f : X ⟶ Y) [单态射 f]
  定义体: NatIso.ofComponents (by
    intro Z
    suffices (forget _).obj ((«exists» f).obj Z) ≅ (forget _).obj ((map f).obj Z) by
      apply (forget _).preimageIso this
    apply Over.isoMk _ _
    · apply imageMonoIsoSource (Z.arrow ≫ f)
    · apply imageMonoIsoSource_hom_self)

Depends on / 依赖: NatIso, NatIso.ofComponents, Over.isoMk, Z.arrow, forget, imageMonoIsoSource, imageMonoIsoSource_hom_self, ofComponents, preimageIso
-/
def existsIsoMap (f : X ⟶ Y) [Mono f] : «exists» f ≅ map f :=
  NatIso.ofComponents (by
    intro Z
    suffices (forget _).obj ((«exists» f).obj Z) ≅ (forget _).obj ((map f).obj Z) by
      apply (forget _).preimageIso this
    apply Over.isoMk _ _
    · apply imageMonoIsoSource (Z.arrow ≫ f)
    · apply imageMonoIsoSource_hom_self)

/--
Definition of `existsPullbackAdj` / `existsPullbackAdj` 的定义

English:
definition existsPullbackAdj
  signature: (f : X ⟶ Y) [HasPullbacks C]
  body: ((Over.mapPullbackAdj f).comp imageForgetAdj).restrictFullyFaithful
    (fullyFaithfulForget X) (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _)

中文:
定义 存在PullbackAdj
  签名: (f : X ⟶ Y) [有Pullbacks C]
  定义体: ((Over.mapPullbackAdj f).comp imageForgetAdj).restrictFullyFaithful
    (fullyFaithfulForget X) (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _)

Depends on / 依赖: FullyFaithful, Functor, Functor.FullyFaithful.id, Iso.refl, Over.mapPullbackAdj, fullyFaithfulForget, imageForgetAdj, mapPullbackAdj, restrictFullyFaithful
-/
def existsPullbackAdj (f : X ⟶ Y) [HasPullbacks C] : «exists» f ⊣ pullback f :=
  ((Over.mapPullbackAdj f).comp imageForgetAdj).restrictFullyFaithful
    (fullyFaithfulForget X) (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _)

end Exists

end MonoOver

end CategoryTheory
