/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Emily Riehl
-/
module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Limits.Creates
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Limits in the category of elements

We show that if `C` has limits of shape `I` and `A : C ⥤ Type w` preserves limits of shape `I`, then
the category of elements of `A` has limits of shape `I` and the forgetful functor
`π : A.Elements ⥤ C` creates them.

## Further results

- If `A` is (co)representable, then `A.Elements` has an initial object.

-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

universe w v₁ v u₁ u

namespace CategoryTheory

open Limits Opposite ConcreteCategory

variable {C : Type u} [Category.{v} C]

namespace CategoryOfElements

variable {A : C ⥤ Type w} {I : Type u₁} [Category.{v₁} I] [Small.{w} I]

namespace CreatesLimitsAux

variable (F : I ⥤ A.Elements)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `liftedConeElement'` / `liftedConeElement'` 的定义

English:
definition liftedConeElement'
  signature: : limit ((F ⋙ π A) ⋙ A)
  body: Types.Limit.mk _ (fun i => (F.obj i).2) (by simp)

@[simp]

中文:
定义 liftedConeElement'
  签名: : limit ((F ⋙ π A) ⋙ A)
  定义体: Types.Limit.mk _ (fun i => (F.obj i).2) (by simp)

@[simp]

Depends on / 依赖: F.obj, Types.Limit.mk
-/
noncomputable def liftedConeElement' : limit ((F ⋙ π A) ⋙ A) :=
  Types.Limit.mk _ (fun i => (F.obj i).2) (by simp)

@[simp]
/--
lemma `π_liftedConeElement'` / 引理 `π_liftedConeElement'`

English:
lemma π_liftedConeElement'
  given: (i : I)
  proof: Types.Limit.π_mk _ _ _ _

中文:
引理 π_liftedConeElement'
  条件: (i : I)
  证明: Types.Limit.π_mk _ _ _ _

Depends on / 依赖: Types.Limit
-/
lemma π_liftedConeElement' (i : I) :
    dsimp% limit.π ((F ⋙ π A) ⋙ A) i (liftedConeElement' F) = (F.obj i).2 :=
  Types.Limit.π_mk _ _ _ _

variable [HasLimitsOfShape I C] [PreservesLimitsOfShape I A]

/--
Definition of `liftedConeElement` / `liftedConeElement` 的定义

English:
definition liftedConeElement
  signature: : A.obj (limit (F ⋙ π A))
  body: (preservesLimitIso A (F ⋙ π A)).inv (liftedConeElement' F)

中文:
定义 liftedConeElement
  签名: : A.obj (limit (F ⋙ π A))
  定义体: (preservesLimitIso A (F ⋙ π A)).inv (liftedConeElement' F)

Depends on / 依赖: liftedConeElement, preservesLimitIso
-/
noncomputable def liftedConeElement : A.obj (limit (F ⋙ π A)) :=
  (preservesLimitIso A (F ⋙ π A)).inv (liftedConeElement' F)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `map_lift_mapCone` / 引理 `map_lift_mapCone`

English:
lemma map_lift_mapCone
  given: (c : Cone F)
  proof: by
  apply (preservesLimitIso A (F ⋙ π A)).toEquiv.injective
  ext i
  have h₁ := congr_hom (preservesLimitIso_hom_π A (F ⋙ π A) i)
    (A.map (limit.lift (F ⋙ π A) ((π A).mapCone c)) c.pt.snd)
  have h₂ := (c.π.app i).property
  simpa [-Functor.comp_obj, ← comp_apply, ← Functor.map_comp, liftedCone

中文:
引理 map_lift_mapCone
  条件: (c : Cone F)
  证明: by
  apply (preservesLimitIso A (F ⋙ π A)).toEquiv.injective
  ext i
  have h₁ := congr_hom (preservesLimitIso_hom_π A (F ⋙ π A) i)
    (A.map (limit.lift (F ⋙ π A) ((π A).mapCone c)) c.pt.snd)
  have h₂ := (c.π.app i).property
  simpa [-Functor.comp_obj, ← comp_apply, ← Functor.map_comp, liftedCone

Depends on / 依赖: A.map, Functor, Functor.comp_obj, Functor.map_comp, c.pt.snd, comp_apply, comp_obj, congr_hom, injective, liftedConeElement, limit.lift, mapCone, map_comp, preservesLimitIso, property, toEquiv, toEquiv.injective
-/
lemma map_lift_mapCone (c : Cone F) :
    dsimp% A.map (limit.lift (F ⋙ π A) ((π A).mapCone c)) c.pt.snd = liftedConeElement F := by
  apply (preservesLimitIso A (F ⋙ π A)).toEquiv.injective
  ext i
  have h₁ := congr_hom (preservesLimitIso_hom_π A (F ⋙ π A) i)
    (A.map (limit.lift (F ⋙ π A) ((π A).mapCone c)) c.pt.snd)
  have h₂ := (c.π.app i).property
  simpa [-Functor.comp_obj, ← comp_apply, ← Functor.map_comp, liftedConeElement, liftedConeElement']

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `map_π_liftedConeElement` / 引理 `map_π_liftedConeElement`

English:
lemma map_π_liftedConeElement
  given: (i : I)
  proof: by
  have := congr_hom
    (preservesLimitIso_inv_π A (F ⋙ π A) i) (liftedConeElement' F)
  simp [liftedConeElement, ← comp_apply]

中文:
引理 map_π_liftedConeElement
  条件: (i : I)
  证明: by
  have := congr_hom
    (preservesLimitIso_inv_π A (F ⋙ π A) i) (liftedConeElement' F)
  simp [liftedConeElement, ← comp_apply]

Depends on / 依赖: comp_apply, congr_hom, liftedConeElement
-/
lemma map_π_liftedConeElement (i : I) :
    dsimp% A.map (limit.π (F ⋙ π A) i) (liftedConeElement F) = (F.obj i).snd := by
  have := congr_hom
    (preservesLimitIso_inv_π A (F ⋙ π A) i) (liftedConeElement' F)
  simp [liftedConeElement, ← comp_apply]

set_option backward.isDefEq.respectTransparency.types false in
/-- (implementation) The constructed limit cone. -/
@[simps]
/--
Definition of `liftedCone` / `liftedCone` 的定义

English:
definition liftedCone
  signature: : Cone F where
  body: ⟨_, liftedConeElement F⟩
  π :=
    { app := fun i => ⟨limit.π (F ⋙ π A) i, by simpa using! map_π_liftedConeElement _ _⟩
      naturality := fun i i' f => by ext; simpa using! (limit.w _ _).symm }

中文:
定义 liftedCone
  签名: : Cone F where
  定义体: ⟨_, liftedConeElement F⟩
  π :=
    { app := fun i => ⟨limit.π (F ⋙ π A) i, by simpa using! map_π_liftedConeElement _ _⟩
      naturality := fun i i' f => by ext; simpa using! (limit.w _ _).symm }

Depends on / 依赖: liftedConeElement
-/
noncomputable def liftedCone : Cone F where
  pt := ⟨_, liftedConeElement F⟩
  π :=
    { app := fun i => ⟨limit.π (F ⋙ π A) i, by simpa using! map_π_liftedConeElement _ _⟩
      naturality := fun i i' f => by ext; simpa using! (limit.w _ _).symm }

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `isValidLift` / `isValidLift` 的定义

English:
definition isValidLift
  signature: : (π A).mapCone (liftedCone F) ≅ limit.cone (F ⋙ π A)
  body: Iso.refl _

中文:
定义 isValidLift
  签名: : (π A).mapCone (liftedCone F) ≅ limit.cone (F ⋙ π A)
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl, UnivLE, hasLimitsOfSize
-/
noncomputable def isValidLift : (π A).mapCone (liftedCone F) ≅ limit.cone (F ⋙ π A) :=
  Iso.refl _

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isLimit` / `isLimit` 的定义

English:
definition isLimit
  signature: : IsLimit (liftedCone F) where
  body: ⟨limit.lift (F ⋙ π A) ((π A).mapCone s), by simp⟩
uniq s m h := ext _ _ _ limit.hom_ext
    fun i => by simpa using congrArg Subtype.val (h i)

中文:
定义 isLimit
  签名: : IsLimit (liftedCone F) where
  定义体: ⟨limit.lift (F ⋙ π A) ((π A).mapCone s), by simp⟩
uniq s m h := ext _ _ _ limit.hom_ext
    fun i => by simpa using congrArg Subtype.val (h i)

Depends on / 依赖: limit.lift, mapCone
-/
noncomputable def isLimit : IsLimit (liftedCone F) where
  lift s := ⟨limit.lift (F ⋙ π A) ((π A).mapCone s), by simp⟩
uniq s m h := ext _ _ _ limit.hom_ext
    fun i => by simpa using congrArg Subtype.val (h i)

end CreatesLimitsAux

variable [HasLimitsOfShape I C] [PreservesLimitsOfShape I A]

section

open CreatesLimitsAux

noncomputable instance (F : I ⥤ A.Elements) : CreatesLimit F (π A) :=
  createsLimitOfReflectsIso' (limit.isLimit _) ⟨⟨liftedCone F, isValidLift F⟩, isLimit F⟩

end

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CreatesLimitsOfShape I (π A)

中文:
实例 :
  签名: CreatesLimitsOfShape I (π A)
-/
noncomputable instance : CreatesLimitsOfShape I (π A) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasLimitsOfShape I A.Elements
  body: hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (π A)

中文:
实例 :
  签名: HasLimitsOfShape I A.Elements
  定义体: hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (π A)

Depends on / 依赖: hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape
-/
instance : HasLimitsOfShape I A.Elements :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (π A)

section Initial

instance {F : Cᵒᵖ ⥤ Type*} [F.IsRepresentable] : HasInitial F.Elements :=
  (Functor.Elements.isInitialOfRepresentableBy F.representableBy).hasInitial

instance {F : C ⥤ Type*} [F.IsCorepresentable] : HasInitial F.Elements :=
  (Functor.Elements.isInitialOfCorepresentableBy F.corepresentableBy).hasInitial

end Initial

end CategoryOfElements

namespace Functor.Elements

/--
Definition of `corepresentableByOfIsInitial` / `corepresentableByOfIsInitial` 的定义

English:
definition corepresentableByOfIsInitial
  signature: {F : C ⥤ Type w} {E : Elements F} (he : IsInitial E)
  body: { toFun f := F.map f E.snd
      invFun y := (he.to ⟨_, y⟩).val
      left_inv f := Subtype.ext_iff.mp (he.hom_ext (he.to ⟨_, F.map f E.snd⟩) ⟨f, rfl⟩)
      right_inv y := (he.to ⟨_, y⟩).prop }

中文:
定义 corepresentableByOfIsInitial
  签名: {F : C ⥤ Type w} {E : Elements F} (he : IsInitial E)
  定义体: { toFun f := F.map f E.snd
      invFun y := (he.to ⟨_, y⟩).val
      left_inv f := Subtype.ext_iff.mp (he.hom_ext (he.to ⟨_, F.map f E.snd⟩) ⟨f, rfl⟩)
      right_inv y := (he.to ⟨_, y⟩).prop }

Depends on / 依赖: E.snd, F.map, Subtype, Subtype.ext_iff.mp, ext_iff, he.hom_ext, he.to, hom_ext, invFun, left_inv, right_inv
-/
def corepresentableByOfIsInitial {F : C ⥤ Type w} {E : Elements F} (he : IsInitial E) :
    CorepresentableBy F E.fst where
  homEquiv :=
    { toFun f := F.map f E.snd
      invFun y := (he.to ⟨_, y⟩).val
      left_inv f := Subtype.ext_iff.mp (he.hom_ext (he.to ⟨_, F.map f E.snd⟩) ⟨f, rfl⟩)
      right_inv y := (he.to ⟨_, y⟩).prop }

/--
lemma `isCorepresentable_of_hasInitial` / 引理 `isCorepresentable_of_hasInitial`

English:
lemma isCorepresentable_of_hasInitial
  given: (F : C ⥤ Type w) [HasInitial (Elements F)]
  proof: ⟨(⊥_ F.Elements).fst,
      (Nonempty.intro (corepresentableByOfIsInitial initialIsInitial))⟩

中文:
引理 isCorepresentable_of_hasInitial
  条件: (F : C ⥤ Type w) [HasInitial (Elements F)]
  证明: ⟨(⊥_ F.Elements).fst,
      (Nonempty.intro (corepresentableByOfIsInitial initialIsInitial))⟩

Depends on / 依赖: Elements, F.Elements, Nonempty, Nonempty.intro, corepresentableByOfIsInitial, initialIsInitial
-/
lemma isCorepresentable_of_hasInitial (F : C ⥤ Type w) [HasInitial (Elements F)] :
    IsCorepresentable F where
  has_corepresentation :=
    ⟨(⊥_ F.Elements).fst,
      (Nonempty.intro (corepresentableByOfIsInitial initialIsInitial))⟩

/--
theorem `hasInitial_iff_isCorepresentable` / 定理 `hasInitial_iff_isCorepresentable`

English:
theorem hasInitial_iff_isCorepresentable
  given: (F : C ⥤ Type w)
  proof: isCorepresentable_of_hasInitial F
  mpr _ := inferInstance

中文:
定理 hasInitial_iff_isCorepresentable
  条件: (F : C ⥤ Type w)
  证明: isCorepresentable_of_hasInitial F
  mpr _ := inferInstance

Depends on / 依赖: isCorepresentable_of_hasInitial
-/
theorem hasInitial_iff_isCorepresentable (F : C ⥤ Type w) :
    HasInitial (Elements F) ↔ IsCorepresentable F where
  mp _ := isCorepresentable_of_hasInitial F
  mpr _ := inferInstance

/--
Definition of `representableByOfIsInitial` / `representableByOfIsInitial` 的定义

English:
definition representableByOfIsInitial
  signature: {F : Cᵒᵖ ⥤ Type w} {E : Elements F} (he : IsInitial E)
  body: { toFun f := F.map f.op E.snd
      invFun y := (he.to ⟨_, y⟩).val.unop
      left_inv f := by
        have :=
          Subtype.ext_iff.mp (he.hom_ext (he.to ⟨_, F.map f.op E.snd⟩) ⟨f.op, rfl⟩)
        simp only [this, Quiver.Hom.unop_op]
      right_inv y := (he.to ⟨_, y⟩).prop }

中文:
定义 representableByOfIsInitial
  签名: {F : Cᵒᵖ ⥤ Type w} {E : Elements F} (he : IsInitial E)
  定义体: { toFun f := F.map f.op E.snd
      invFun y := (he.to ⟨_, y⟩).val.unop
      left_inv f := by
        have :=
          Subtype.ext_iff.mp (he.hom_ext (he.to ⟨_, F.map f.op E.snd⟩) ⟨f.op, rfl⟩)
        simp only [this, Quiver.Hom.unop_op]
      right_inv y := (he.to ⟨_, y⟩).prop }

Depends on / 依赖: E.snd, F.map, Quiver, Quiver.Hom.unop_op, Subtype, Subtype.ext_iff.mp, ext_iff, f.op, he.hom_ext, he.to, hom_ext, invFun, left_inv, right_inv, unop_op, val.unop
-/
def representableByOfIsInitial {F : Cᵒᵖ ⥤ Type w} {E : Elements F} (he : IsInitial E) :
    RepresentableBy F (E.fst.unop) where
  homEquiv :=
    { toFun f := F.map f.op E.snd
      invFun y := (he.to ⟨_, y⟩).val.unop
      left_inv f := by
        have :=
          Subtype.ext_iff.mp (he.hom_ext (he.to ⟨_, F.map f.op E.snd⟩) ⟨f.op, rfl⟩)
        simp only [this, Quiver.Hom.unop_op]
      right_inv y := (he.to ⟨_, y⟩).prop }

/--
lemma `isRepresentable_of_hasInitial` / 引理 `isRepresentable_of_hasInitial`

English:
lemma isRepresentable_of_hasInitial
  given: (F : Cᵒᵖ ⥤ Type w) [HasInitial (Elements F)]
  proof: ⟨(⊥_ F.Elements).fst.unop,
      (Nonempty.intro (representableByOfIsInitial initialIsInitial))⟩

中文:
引理 isRepresentable_of_hasInitial
  条件: (F : Cᵒᵖ ⥤ Type w) [HasInitial (Elements F)]
  证明: ⟨(⊥_ F.Elements).fst.unop,
      (Nonempty.intro (representableByOfIsInitial initialIsInitial))⟩

Depends on / 依赖: Elements, F.Elements, Nonempty, Nonempty.intro, fst.unop, initialIsInitial, representableByOfIsInitial
-/
lemma isRepresentable_of_hasInitial (F : Cᵒᵖ ⥤ Type w) [HasInitial (Elements F)] :
    IsRepresentable F where
  has_representation :=
    ⟨(⊥_ F.Elements).fst.unop,
      (Nonempty.intro (representableByOfIsInitial initialIsInitial))⟩

/--
theorem `hasInitial_iff_isRepresentable` / 定理 `hasInitial_iff_isRepresentable`

English:
theorem hasInitial_iff_isRepresentable
  given: (F : Cᵒᵖ ⥤ Type w)
  proof: isRepresentable_of_hasInitial F
  mpr _ := inferInstance

中文:
定理 hasInitial_iff_isRepresentable
  条件: (F : Cᵒᵖ ⥤ Type w)
  证明: isRepresentable_of_hasInitial F
  mpr _ := inferInstance

Depends on / 依赖: isRepresentable_of_hasInitial
-/
theorem hasInitial_iff_isRepresentable (F : Cᵒᵖ ⥤ Type w) :
    HasInitial (Elements F) ↔ IsRepresentable F where
  mp _ := isRepresentable_of_hasInitial F
  mpr _ := inferInstance

end Functor.Elements

end CategoryTheory
