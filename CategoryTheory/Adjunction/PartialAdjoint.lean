/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Yoneda

/-!
# Domain of definition of the partial left adjoint

Given a functor `F : D ⥤ C`, we define a functor
`F.partialLeftAdjoint : F.PartialLeftAdjointSource ⥤ D` which is
defined on the full subcategory of `C` consisting of those objects `X : C`
such that `F ⋙ coyoneda.obj (op X) : D ⥤ Type _` is corepresentable.
For `X : F.PartialLeftAdjointSource` and `Y : D`, we have a natural bijection
`(F.partialLeftAdjoint.obj X ⟶ Y) ≃ (X.obj ⟶ F.obj Y)`
that is similar to what we would expect for the image of the object `X`
by the left adjoint of `F`, if such an adjoint existed.

Indeed, if the predicate `F.leftAdjointObjIsDefined` which defines
the `F.PartialLeftAdjointSource` holds for all
objects `X : C`, then `F` has a left adjoint.

When colimits indexed by a category `J` exist in `D`, we show that
the predicate `F.leftAdjointObjIsDefined` is stable under colimits indexed by `J`.

## TODO
* consider dualizing the results to right adjoints

-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Functor

open Category Opposite Limits

section partialLeftAdjoint

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : D ⥤ C)

/--
Definition of `leftAdjointObjIsDefined` / `leftAdjointObjIsDefined` 的定义

English:
definition leftAdjointObjIsDefined
  signature: : ObjectProperty C
  body: fun X => IsCorepresentable (F ⋙ coyoneda.obj (op X))

中文:
定义 leftAdjointObjIsDefined
  签名: : ObjectProperty C
  定义体: fun X => IsCorepresentable (F ⋙ coyoneda.obj (op X))

Depends on / 依赖: IsCorepresentable, coyoneda, coyoneda.obj
-/
def leftAdjointObjIsDefined : ObjectProperty C :=
  fun X => IsCorepresentable (F ⋙ coyoneda.obj (op X))

/--
lemma `leftAdjointObjIsDefined_iff` / 引理 `leftAdjointObjIsDefined_iff`

English:
lemma leftAdjointObjIsDefined_iff
  given: (X : C)
  proof: by rfl

中文:
引理 leftAdjointObjIsDefined_iff
  条件: (X : C)
  证明: by rfl
-/
lemma leftAdjointObjIsDefined_iff (X : C) :
    F.leftAdjointObjIsDefined X ↔ IsCorepresentable (F ⋙ coyoneda.obj (op X)) := by rfl

variable {F} in
/--
lemma `leftAdjointObjIsDefined_of_adjunction` / 引理 `leftAdjointObjIsDefined_of_adjunction`

English:
lemma leftAdjointObjIsDefined_of_adjunction
  given: {G : C ⥤ D} (adj : G ⊣ F) (X : C)
  proof: (adj.corepresentableBy X).isCorepresentable

中文:
引理 leftAdjointObjIsDefined_of_adjunction
  条件: {G : C ⥤ D} (adj : G ⊣ F) (X : C)
  证明: (adj.corepresentableBy X).isCorepresentable

Depends on / 依赖: adj.corepresentableBy, corepresentableBy, isCorepresentable
-/
lemma leftAdjointObjIsDefined_of_adjunction {G : C ⥤ D} (adj : G ⊣ F) (X : C) :
    F.leftAdjointObjIsDefined X :=
  (adj.corepresentableBy X).isCorepresentable

/--
Definition of `PartialLeftAdjointSource` / `PartialLeftAdjointSource` 的定义

English:
abbreviation PartialLeftAdjointSource
  body: F.leftAdjointObjIsDefined.FullSubcategory

中文:
缩写 PartialLeftAdjointSource
  定义体: F.leftAdjointObjIsDefined.FullSubcategory

Depends on / 依赖: F.leftAdjointObjIsDefined.FullSubcategory, FullSubcategory, leftAdjointObjIsDefined
-/
abbrev PartialLeftAdjointSource := F.leftAdjointObjIsDefined.FullSubcategory

instance (X : F.PartialLeftAdjointSource) :
    IsCorepresentable (F ⋙ coyoneda.obj (op X.obj)) := X.property

/--
Definition of `partialLeftAdjointObj` / `partialLeftAdjointObj` 的定义

English:
definition partialLeftAdjointObj
  signature: (X : F.PartialLeftAdjointSource)
  body: (F ⋙ coyoneda.obj (op X.obj)).coreprX

中文:
定义 partialLeftAdjointObj
  签名: (X : F.PartialLeftAdjointSource)
  定义体: (F ⋙ coyoneda.obj (op X.obj)).coreprX

Depends on / 依赖: X.obj, coreprX, coyoneda, coyoneda.obj
-/
noncomputable def partialLeftAdjointObj (X : F.PartialLeftAdjointSource) : D :=
  (F ⋙ coyoneda.obj (op X.obj)).coreprX

/--
Definition of `partialLeftAdjointHomEquiv` / `partialLeftAdjointHomEquiv` 的定义

English:
definition partialLeftAdjointHomEquiv
  signature: {X : F.PartialLeftAdjointSource} {Y : D}
  body: (F ⋙ coyoneda.obj (op X.obj)).corepresentableBy.homEquiv

中文:
定义 partialLeftAdjointHomEquiv
  签名: {X : F.PartialLeftAdjointSource} {Y : D}
  定义体: (F ⋙ coyoneda.obj (op X.obj)).corepresentableBy.homEquiv

Depends on / 依赖: X.obj, corepresentableBy, corepresentableBy.homEquiv, coyoneda, coyoneda.obj, homEquiv
-/
noncomputable def partialLeftAdjointHomEquiv {X : F.PartialLeftAdjointSource} {Y : D} :
    (F.partialLeftAdjointObj X ⟶ Y) ≃ (X.obj ⟶ F.obj Y) :=
  (F ⋙ coyoneda.obj (op X.obj)).corepresentableBy.homEquiv

/--
lemma `partialLeftAdjointHomEquiv_comp` / 引理 `partialLeftAdjointHomEquiv_comp`

English:
lemma partialLeftAdjointHomEquiv_comp
  statement: {X : F.PartialLeftAdjointSource} {Y Y' : D}
  proof: by
  apply CorepresentableBy.homEquiv_comp

中文:
引理 partialLeftAdjointHomEquiv_comp
  结论: {X : F.PartialLeftAdjointSource} {Y Y' : D}
  证明: by
  apply CorepresentableBy.homEquiv_comp

Depends on / 依赖: CorepresentableBy, CorepresentableBy.homEquiv_comp, homEquiv_comp
-/
lemma partialLeftAdjointHomEquiv_comp {X : F.PartialLeftAdjointSource} {Y Y' : D}
    (f : F.partialLeftAdjointObj X ⟶ Y) (g : Y ⟶ Y') :
    F.partialLeftAdjointHomEquiv (f ≫ g) =
      F.partialLeftAdjointHomEquiv f ≫ F.map g := by
  apply CorepresentableBy.homEquiv_comp

/--
Definition of `partialLeftAdjointMap` / `partialLeftAdjointMap` 的定义

English:
definition partialLeftAdjointMap
  signature: {X Y : F.PartialLeftAdjointSource}
  body: F.partialLeftAdjointHomEquiv.symm (f.hom ≫ F.partialLeftAdjointHomEquiv (𝟙 _))

@[simp]

中文:
定义 partialLeftAdjointMap
  签名: {X Y : F.PartialLeftAdjointSource}
  定义体: F.partialLeftAdjointHomEquiv.symm (f.hom ≫ F.partialLeftAdjointHomEquiv (𝟙 _))

@[simp]

Depends on / 依赖: F.partialLeftAdjointHomEquiv, F.partialLeftAdjointHomEquiv.symm, f.hom, partialLeftAdjointHomEquiv
-/
noncomputable def partialLeftAdjointMap {X Y : F.PartialLeftAdjointSource}
    (f : X ⟶ Y) : F.partialLeftAdjointObj X ⟶ F.partialLeftAdjointObj Y :=
    F.partialLeftAdjointHomEquiv.symm (f.hom ≫ F.partialLeftAdjointHomEquiv (𝟙 _))

@[simp]
/--
lemma `partialLeftAdjointHomEquiv_map` / 引理 `partialLeftAdjointHomEquiv_map`

English:
lemma partialLeftAdjointHomEquiv_map
  statement: {X Y : F.PartialLeftAdjointSource}
  proof: by
  simp [partialLeftAdjointMap]

中文:
引理 partialLeftAdjointHomEquiv_map
  结论: {X Y : F.PartialLeftAdjointSource}
  证明: by
  simp [partialLeftAdjointMap]

Depends on / 依赖: partialLeftAdjointMap
-/
lemma partialLeftAdjointHomEquiv_map {X Y : F.PartialLeftAdjointSource}
    (f : X ⟶ Y) :
    F.partialLeftAdjointHomEquiv (F.partialLeftAdjointMap f) =
      f.hom ≫ F.partialLeftAdjointHomEquiv (𝟙 _) := by
  simp [partialLeftAdjointMap]

/--
lemma `partialLeftAdjointHomEquiv_map_comp` / 引理 `partialLeftAdjointHomEquiv_map_comp`

English:
lemma partialLeftAdjointHomEquiv_map_comp
  statement: {X X' : F.PartialLeftAdjointSource} {Y : D}
  proof: by
  rw [partialLeftAdjointHomEquiv_comp]; rw [partialLeftAdjointHomEquiv_map]; rw [assoc]; rw [← partialLeftAdjointHomEquiv_comp]; rw [id_comp]

@[reassoc]

中文:
引理 partialLeftAdjointHomEquiv_map_comp
  结论: {X X' : F.PartialLeftAdjointSource} {Y : D}
  证明: by
  rw [partialLeftAdjointHomEquiv_comp]; rw [partialLeftAdjointHomEquiv_map]; rw [assoc]; rw [← partialLeftAdjointHomEquiv_comp]; rw [id_comp]

@[reassoc]

Depends on / 依赖: id_comp, partialLeftAdjointHomEquiv_comp, partialLeftAdjointHomEquiv_map
-/
lemma partialLeftAdjointHomEquiv_map_comp {X X' : F.PartialLeftAdjointSource} {Y : D}
    (f : X ⟶ X') (g : F.partialLeftAdjointObj X' ⟶ Y) :
    F.partialLeftAdjointHomEquiv (F.partialLeftAdjointMap f ≫ g) =
      f.hom ≫ F.partialLeftAdjointHomEquiv g := by
  rw [partialLeftAdjointHomEquiv_comp]; rw [partialLeftAdjointHomEquiv_map]; rw [assoc]; rw [← partialLeftAdjointHomEquiv_comp]; rw [id_comp]

@[reassoc]
/--
lemma `partialLeftAdjointHomEquiv_symm_comp` / 引理 `partialLeftAdjointHomEquiv_symm_comp`

English:
lemma partialLeftAdjointHomEquiv_symm_comp
  statement: {X : F.PartialLeftAdjointSource} {Y Y' : D}
  proof: CorepresentableBy.homEquiv_symm_comp ..

@[reassoc]

中文:
引理 partialLeftAdjointHomEquiv_symm_comp
  结论: {X : F.PartialLeftAdjointSource} {Y Y' : D}
  证明: CorepresentableBy.homEquiv_symm_comp ..

@[reassoc]

Depends on / 依赖: CorepresentableBy, CorepresentableBy.homEquiv_symm_comp, homEquiv_symm_comp
-/
lemma partialLeftAdjointHomEquiv_symm_comp {X : F.PartialLeftAdjointSource} {Y Y' : D}
    (f : X.obj ⟶ F.obj Y) (g : Y ⟶ Y') :
    F.partialLeftAdjointHomEquiv.symm f ≫ g = F.partialLeftAdjointHomEquiv.symm (f ≫ F.map g) :=
  CorepresentableBy.homEquiv_symm_comp ..

@[reassoc]
/--
lemma `partialLeftAdjointHomEquiv_comp_symm` / 引理 `partialLeftAdjointHomEquiv_comp_symm`

English:
lemma partialLeftAdjointHomEquiv_comp_symm
  statement: {X X' : F.PartialLeftAdjointSource} {Y : D}
  proof: by
  rw [Equiv.eq_symm_apply]; rw [partialLeftAdjointHomEquiv_comp]; rw [partialLeftAdjointHomEquiv_map]; rw [assoc]; rw [← partialLeftAdjointHomEquiv_comp]; rw [id_comp]; rw [Equiv.apply_symm_apply]

中文:
引理 partialLeftAdjointHomEquiv_comp_symm
  结论: {X X' : F.PartialLeftAdjointSource} {Y : D}
  证明: by
  rw [Equiv.eq_symm_apply]; rw [partialLeftAdjointHomEquiv_comp]; rw [partialLeftAdjointHomEquiv_map]; rw [assoc]; rw [← partialLeftAdjointHomEquiv_comp]; rw [id_comp]; rw [Equiv.apply_symm_apply]

Depends on / 依赖: Equiv.apply_symm_apply, Equiv.eq_symm_apply, apply_symm_apply, eq_symm_apply, id_comp, partialLeftAdjointHomEquiv_comp, partialLeftAdjointHomEquiv_map
-/
lemma partialLeftAdjointHomEquiv_comp_symm {X X' : F.PartialLeftAdjointSource} {Y : D}
    (f : X'.obj ⟶ F.obj Y) (g : X ⟶ X') :
    F.partialLeftAdjointMap g ≫ F.partialLeftAdjointHomEquiv.symm f =
    F.partialLeftAdjointHomEquiv.symm (g.hom ≫ f) := by
  rw [Equiv.eq_symm_apply]; rw [partialLeftAdjointHomEquiv_comp]; rw [partialLeftAdjointHomEquiv_map]; rw [assoc]; rw [← partialLeftAdjointHomEquiv_comp]; rw [id_comp]; rw [Equiv.apply_symm_apply]

/-- Given `F : D ⥤ C`, this is the partial adjoint functor `F.PartialLeftAdjointSource ⥤ D`. -/
@[simps]
/--
Definition of `partialLeftAdjoint` / `partialLeftAdjoint` 的定义

English:
definition partialLeftAdjoint
  signature: : F.PartialLeftAdjointSource ⥤ D where
  body: F.partialLeftAdjointObj
  map := F.partialLeftAdjointMap
  map_id X := by
    apply F.partialLeftAdjointHomEquiv.injective
    simp [partialLeftAdjointHomEquiv_map]
  map_comp {X Y Z} f g := by
    apply F.partialLeftAdjointHomEquiv.injective
    simp [partialLeftAdjointHomEquiv_comp, ← F.partialLef

中文:
定义 partialLeftAdjoint
  签名: : F.PartialLeftAdjointSource ⥤ D where
  定义体: F.partialLeftAdjointObj
  map := F.partialLeftAdjointMap
  map_id X := by
    apply F.partialLeftAdjointHomEquiv.injective
    simp [partialLeftAdjointHomEquiv_map]
  map_comp {X Y Z} f g := by
    apply F.partialLeftAdjointHomEquiv.injective
    simp [partialLeftAdjointHomEquiv_comp, ← F.partialLef

Depends on / 依赖: F.partialLeftAdjointObj, partialLeftAdjointObj
-/
noncomputable def partialLeftAdjoint : F.PartialLeftAdjointSource ⥤ D where
  obj := F.partialLeftAdjointObj
  map := F.partialLeftAdjointMap
  map_id X := by
    apply F.partialLeftAdjointHomEquiv.injective
    simp [partialLeftAdjointHomEquiv_map]
  map_comp {X Y Z} f g := by
    apply F.partialLeftAdjointHomEquiv.injective
    simp [partialLeftAdjointHomEquiv_comp, ← F.partialLeftAdjointHomEquiv_comp]

variable {F}

/--
lemma `isRightAdjoint_of_leftAdjointObjIsDefined_eq_top` / 引理 `isRightAdjoint_of_leftAdjointObjIsDefined_eq_top`

English:
lemma isRightAdjoint_of_leftAdjointObjIsDefined_eq_top
  proof: by
  replace h : forall X, IsCorepresentable (F ⋙ coyoneda.obj (op X)) := fun X => by
    simp only [← leftAdjointObjIsDefined_iff, h, Pi.top_apply, Prop.top_eq_true]
  exact (Adjunction.adjunctionOfEquivLeft
    (fun X Y => (F ⋙ coyoneda.obj (op X)).corepresentableBy.homEquiv)
    (fun X Y Y' g f =

中文:
引理 isRightAdjoint_of_leftAdjointObjIsDefined_eq_top
  证明: by
  replace h : forall X, IsCorepresentable (F ⋙ coyoneda.obj (op X)) := fun X => by
    simp only [← leftAdjointObjIsDefined_iff, h, Pi.top_apply, Prop.top_eq_true]
  exact (Adjunction.adjunctionOfEquivLeft
    (fun X Y => (F ⋙ coyoneda.obj (op X)).corepresentableBy.homEquiv)
    (fun X Y Y' g f =

Depends on / 依赖: Adjunction, Adjunction.adjunctionOfEquivLeft, CorepresentableBy, CorepresentableBy.homEquiv_comp, IsCorepresentable, Pi.top_apply, Prop.top_eq_true, adjunctionOfEquivLeft, corepresentableBy, corepresentableBy.homEquiv, coyoneda, coyoneda.obj, homEquiv, homEquiv_comp, isRightAdjoint, leftAdjointObjIsDefined_iff, replace, top_apply, top_eq_true
-/
lemma isRightAdjoint_of_leftAdjointObjIsDefined_eq_top
    (h : F.leftAdjointObjIsDefined = ⊤) : F.IsRightAdjoint := by
  replace h : forall X, IsCorepresentable (F ⋙ coyoneda.obj (op X)) := fun X => by
    simp only [← leftAdjointObjIsDefined_iff, h, Pi.top_apply, Prop.top_eq_true]
  exact (Adjunction.adjunctionOfEquivLeft
    (fun X Y => (F ⋙ coyoneda.obj (op X)).corepresentableBy.homEquiv)
    (fun X Y Y' g f => by apply CorepresentableBy.homEquiv_comp)).isRightAdjoint

variable (F) in
/--
lemma `isRightAdjoint_iff_leftAdjointObjIsDefined_eq_top` / 引理 `isRightAdjoint_iff_leftAdjointObjIsDefined_eq_top`

English:
lemma isRightAdjoint_iff_leftAdjointObjIsDefined_eq_top
  proof: by
  refine ⟨fun h => ?_, isRightAdjoint_of_leftAdjointObjIsDefined_eq_top⟩
  ext X
  simpa only [Pi.top_apply, Prop.top_eq_true, iff_true]
    using leftAdjointObjIsDefined_of_adjunction (Adjunction.ofIsRightAdjoint F) X

中文:
引理 isRightAdjoint_iff_leftAdjointObjIsDefined_eq_top
  证明: by
  refine ⟨fun h => ?_, isRightAdjoint_of_leftAdjointObjIsDefined_eq_top⟩
  ext X
  simpa only [Pi.top_apply, Prop.top_eq_true, iff_true]
    using leftAdjointObjIsDefined_of_adjunction (Adjunction.ofIsRightAdjoint F) X

Depends on / 依赖: Adjunction, Adjunction.ofIsRightAdjoint, Pi.top_apply, Prop.top_eq_true, iff_true, isRightAdjoint_of_leftAdjointObjIsDefined_eq_top, leftAdjointObjIsDefined_of_adjunction, ofIsRightAdjoint, top_apply, top_eq_true
-/
lemma isRightAdjoint_iff_leftAdjointObjIsDefined_eq_top :
    F.IsRightAdjoint ↔ F.leftAdjointObjIsDefined = ⊤ := by
  refine ⟨fun h => ?_, isRightAdjoint_of_leftAdjointObjIsDefined_eq_top⟩
  ext X
  simpa only [Pi.top_apply, Prop.top_eq_true, iff_true]
    using leftAdjointObjIsDefined_of_adjunction (Adjunction.ofIsRightAdjoint F) X

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `corepresentableByCompCoyonedaObjOfIsColimit` / `corepresentableByCompCoyonedaObjOfIsColimit` 的定义

English:
definition corepresentableByCompCoyonedaObjOfIsColimit
  signature: {J : Type*} [Category* J]
  body: { toFun := fun f => hc.desc (Cocone.mk _
        { app := fun j => F.partialLeftAdjointHomEquiv (c'.ι.app j ≫ f)
          naturality := fun j j' φ => by
            dsimp
            rw [comp_id]; rw [← c'.w φ]; rw [← partialLeftAdjointHomEquiv_map_comp]; rw [assoc]
            dsimp })
      invFu

中文:
定义 corepresentableByCompCoyonedaObjOfIsColimit
  签名: {J : 类型} [范畴* J]
  定义体: { toFun := fun f => hc.desc (Cocone.mk _
        { app := fun j => F.partialLeftAdjointHomEquiv (c'.ι.app j ≫ f)
          naturality := fun j j' φ => by
            dsimp
            rw [comp_id]; rw [← c'.w φ]; rw [← partialLeftAdjointHomEquiv_map_comp]; rw [assoc]
            dsimp })
      invFu

Depends on / 依赖: Cocone, Cocone.mk, Equiv.apply_symm_apply, F.partialLeftAdjointHomEquiv, F.partialLeftAdjointHomEquiv.injective, F.partialLeftAdjointHomEquiv.symm, apply_symm_apply, comp_id, hc.desc, injective, invFun, naturality, partialLeftAdjointHomEquiv, partialLeftAdjointHomEquiv_map_comp
-/
noncomputable def corepresentableByCompCoyonedaObjOfIsColimit {J : Type*} [Category* J]
    {R : J ⥤ F.PartialLeftAdjointSource}
    {c : Cocone (R ⋙ ObjectProperty.ι _)} (hc : IsColimit c)
    {c' : Cocone (R ⋙ F.partialLeftAdjoint)} (hc' : IsColimit c') :
    (F ⋙ coyoneda.obj (op c.pt)).CorepresentableBy c'.pt where
  homEquiv {Y} :=
    { toFun := fun f => hc.desc (Cocone.mk _
        { app := fun j => F.partialLeftAdjointHomEquiv (c'.ι.app j ≫ f)
          naturality := fun j j' φ => by
            dsimp
            rw [comp_id]; rw [← c'.w φ]; rw [← partialLeftAdjointHomEquiv_map_comp]; rw [assoc]
            dsimp })
      invFun := fun g => hc'.desc (Cocone.mk _
        { app := fun j => F.partialLeftAdjointHomEquiv.symm (c.ι.app j ≫ g)
          naturality := fun j j' φ => by
            apply F.partialLeftAdjointHomEquiv.injective
            have := c.w φ
            dsimp at this ⊢
            rw [comp_id]; rw [Equiv.apply_symm_apply]; rw [partialLeftAdjointHomEquiv_map_comp]; rw [Equiv.apply_symm_apply]; rw [reassoc_of% this] })
      left_inv := fun f => hc'.hom_ext (fun j => by simp)
      right_inv := fun g => hc.hom_ext (fun j => by simp) }
  homEquiv_comp {Y Y'} g f := hc.hom_ext (fun j => by
    dsimp
    simp only [IsColimit.fac, IsColimit.fac_assoc, partialLeftAdjointHomEquiv_comp,
      F.map_comp, assoc])

/--
lemma `leftAdjointObjIsDefined_of_isColimit` / 引理 `leftAdjointObjIsDefined_of_isColimit`

English:
lemma leftAdjointObjIsDefined_of_isColimit
  statement: {J : Type*} [Category* J] {R : J ⥤ C} {c : Cocone R}
  proof: (corepresentableByCompCoyonedaObjOfIsColimit
    (R := ObjectProperty.lift _ R h) hc (colimit.isColimit _)).isCorepresentable

中文:
引理 leftAdjointObjIsDefined_of_isColimit
  结论: {J : 类型} [范畴* J] {R : J ⥤ C} {c : 余锥 R}
  证明: (corepresentableByCompCoyonedaObjOfIsColimit
    (R := ObjectProperty.lift _ R h) hc (colimit.isColimit _)).isCorepresentable

Depends on / 依赖: ObjectProperty, ObjectProperty.lift, colimit, colimit.isColimit, corepresentableByCompCoyonedaObjOfIsColimit, isColimit, isCorepresentable
-/
lemma leftAdjointObjIsDefined_of_isColimit {J : Type*} [Category* J] {R : J ⥤ C} {c : Cocone R}
    (hc : IsColimit c) [HasColimitsOfShape J D]
    (h : forall (j : J), F.leftAdjointObjIsDefined (R.obj j)) :
    F.leftAdjointObjIsDefined c.pt :=
  (corepresentableByCompCoyonedaObjOfIsColimit
    (R := ObjectProperty.lift _ R h) hc (colimit.isColimit _)).isCorepresentable

/--
lemma `leftAdjointObjIsDefined_colimit` / 引理 `leftAdjointObjIsDefined_colimit`

English:
lemma leftAdjointObjIsDefined_colimit
  statement: {J : Type*} [Category* J] (R : J ⥤ C)
  proof: leftAdjointObjIsDefined_of_isColimit (colimit.isColimit R) h

中文:
引理 leftAdjointObjIsDefined_colimit
  结论: {J : 类型} [范畴* J] (R : J ⥤ C)
  证明: leftAdjointObjIsDefined_of_isColimit (colimit.isColimit R) h

Depends on / 依赖: colimit, colimit.isColimit, isColimit, leftAdjointObjIsDefined_of_isColimit
-/
lemma leftAdjointObjIsDefined_colimit {J : Type*} [Category* J] (R : J ⥤ C)
    [HasColimit R] [HasColimitsOfShape J D]
    (h : forall (j : J), F.leftAdjointObjIsDefined (R.obj j)) :
    F.leftAdjointObjIsDefined (colimit R) :=
  leftAdjointObjIsDefined_of_isColimit (colimit.isColimit R) h

end partialLeftAdjoint

section partialRightAdjoint

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)

/--
Definition of `rightAdjointObjIsDefined` / `rightAdjointObjIsDefined` 的定义

English:
definition rightAdjointObjIsDefined
  signature: : ObjectProperty D
  body: fun Y => IsRepresentable (F.op ⋙ yoneda.obj Y)

中文:
定义 rightAdjointObjIsDefined
  签名: : ObjectProperty D
  定义体: fun Y => IsRepresentable (F.op ⋙ yoneda.obj Y)

Depends on / 依赖: F.op, IsRepresentable, yoneda, yoneda.obj
-/
def rightAdjointObjIsDefined : ObjectProperty D :=
  fun Y => IsRepresentable (F.op ⋙ yoneda.obj Y)

/--
lemma `rightAdjointObjIsDefined_iff` / 引理 `rightAdjointObjIsDefined_iff`

English:
lemma rightAdjointObjIsDefined_iff
  given: (Y : D)
  proof: by rfl

中文:
引理 rightAdjointObjIsDefined_iff
  条件: (Y : D)
  证明: by rfl
-/
lemma rightAdjointObjIsDefined_iff (Y : D) :
    F.rightAdjointObjIsDefined Y ↔ IsRepresentable (F.op ⋙ yoneda.obj Y) := by rfl

variable {F} in
/--
lemma `rightAdjointObjIsDefined_of_adjunction` / 引理 `rightAdjointObjIsDefined_of_adjunction`

English:
lemma rightAdjointObjIsDefined_of_adjunction
  given: {G : D ⥤ C} (adj : F ⊣ G) (Y : D)
  proof: (adj.representableBy Y).isRepresentable

中文:
引理 rightAdjointObjIsDefined_of_adjunction
  条件: {G : D ⥤ C} (adj : F ⊣ G) (Y : D)
  证明: (adj.representableBy Y).isRepresentable

Depends on / 依赖: adj.representableBy, isRepresentable, representableBy
-/
lemma rightAdjointObjIsDefined_of_adjunction {G : D ⥤ C} (adj : F ⊣ G) (Y : D) :
    F.rightAdjointObjIsDefined Y :=
  (adj.representableBy Y).isRepresentable

/--
Definition of `PartialRightAdjointSource` / `PartialRightAdjointSource` 的定义

English:
abbreviation PartialRightAdjointSource
  body: F.rightAdjointObjIsDefined.FullSubcategory

中文:
缩写 PartialRightAdjointSource
  定义体: F.rightAdjointObjIsDefined.FullSubcategory

Depends on / 依赖: F.rightAdjointObjIsDefined.FullSubcategory, FullSubcategory, rightAdjointObjIsDefined
-/
abbrev PartialRightAdjointSource := F.rightAdjointObjIsDefined.FullSubcategory

instance (Y : F.PartialRightAdjointSource) :
    IsRepresentable (F.op ⋙ yoneda.obj Y.obj) := Y.property

/--
Definition of `partialRightAdjointObj` / `partialRightAdjointObj` 的定义

English:
definition partialRightAdjointObj
  signature: (Y : F.PartialRightAdjointSource)
  body: (F.op ⋙ yoneda.obj Y.obj).reprX

中文:
定义 partialRightAdjointObj
  签名: (Y : F.PartialRightAdjointSource)
  定义体: (F.op ⋙ yoneda.obj Y.obj).reprX

Depends on / 依赖: F.op, Y.obj, yoneda, yoneda.obj
-/
noncomputable def partialRightAdjointObj (Y : F.PartialRightAdjointSource) : C :=
  (F.op ⋙ yoneda.obj Y.obj).reprX

/--
Definition of `partialRightAdjointHomEquiv` / `partialRightAdjointHomEquiv` 的定义

English:
definition partialRightAdjointHomEquiv
  signature: {X : C} {Y : F.PartialRightAdjointSource}
  body: (F.op ⋙ yoneda.obj Y.obj).representableBy.homEquiv

中文:
定义 partialRightAdjointHomEquiv
  签名: {X : C} {Y : F.PartialRightAdjointSource}
  定义体: (F.op ⋙ yoneda.obj Y.obj).representableBy.homEquiv

Depends on / 依赖: F.op, Y.obj, homEquiv, representableBy, representableBy.homEquiv, yoneda, yoneda.obj
-/
noncomputable def partialRightAdjointHomEquiv {X : C} {Y : F.PartialRightAdjointSource} :
    (X ⟶ F.partialRightAdjointObj Y) ≃ (F.obj X ⟶ Y.obj) :=
  (F.op ⋙ yoneda.obj Y.obj).representableBy.homEquiv

/--
lemma `partialRightAdjointHomEquiv_comp` / 引理 `partialRightAdjointHomEquiv_comp`

English:
lemma partialRightAdjointHomEquiv_comp
  statement: {X X' : C} {Y : F.PartialRightAdjointSource}
  proof: RepresentableBy.homEquiv_comp ..

中文:
引理 partialRightAdjointHomEquiv_comp
  结论: {X X' : C} {Y : F.PartialRightAdjointSource}
  证明: RepresentableBy.homEquiv_comp ..

Depends on / 依赖: RepresentableBy, RepresentableBy.homEquiv_comp, homEquiv_comp
-/
lemma partialRightAdjointHomEquiv_comp {X X' : C} {Y : F.PartialRightAdjointSource}
    (f : X' ⟶ F.partialRightAdjointObj Y) (g : X ⟶ X') :
    F.partialRightAdjointHomEquiv (g ≫ f) =
      F.map g ≫ F.partialRightAdjointHomEquiv f :=
  RepresentableBy.homEquiv_comp ..

/--
Definition of `partialRightAdjointMap` / `partialRightAdjointMap` 的定义

English:
definition partialRightAdjointMap
  signature: {X Y : F.PartialRightAdjointSource}
  body: F.partialRightAdjointHomEquiv.symm (F.partialRightAdjointHomEquiv (𝟙 _) ≫ f.hom)

@[simp]

中文:
定义 partialRightAdjointMap
  签名: {X Y : F.PartialRightAdjointSource}
  定义体: F.partialRightAdjointHomEquiv.symm (F.partialRightAdjointHomEquiv (𝟙 _) ≫ f.hom)

@[simp]

Depends on / 依赖: F.partialRightAdjointHomEquiv, F.partialRightAdjointHomEquiv.symm, f.hom, partialRightAdjointHomEquiv
-/
noncomputable def partialRightAdjointMap {X Y : F.PartialRightAdjointSource}
    (f : X ⟶ Y) : F.partialRightAdjointObj X ⟶ F.partialRightAdjointObj Y :=
    F.partialRightAdjointHomEquiv.symm (F.partialRightAdjointHomEquiv (𝟙 _) ≫ f.hom)

@[simp]
/--
lemma `partialRightAdjointHomEquiv_map` / 引理 `partialRightAdjointHomEquiv_map`

English:
lemma partialRightAdjointHomEquiv_map
  statement: {X Y : F.PartialRightAdjointSource}
  proof: by
  simp [partialRightAdjointMap]

中文:
引理 partialRightAdjointHomEquiv_map
  结论: {X Y : F.PartialRightAdjointSource}
  证明: by
  simp [partialRightAdjointMap]

Depends on / 依赖: partialRightAdjointMap
-/
lemma partialRightAdjointHomEquiv_map {X Y : F.PartialRightAdjointSource}
    (f : X ⟶ Y) :
    F.partialRightAdjointHomEquiv (F.partialRightAdjointMap f) =
      F.partialRightAdjointHomEquiv (𝟙 _) ≫ f.hom := by
  simp [partialRightAdjointMap]

/--
lemma `partialRightAdjointHomEquiv_map_comp` / 引理 `partialRightAdjointHomEquiv_map_comp`

English:
lemma partialRightAdjointHomEquiv_map_comp
  statement: {X : C} {Y Y' : F.PartialRightAdjointSource}
  proof: by
  rw [partialRightAdjointHomEquiv_comp]; rw [partialRightAdjointHomEquiv_map]; rw [← assoc]; rw [← partialRightAdjointHomEquiv_comp]; rw [comp_id]

@[reassoc]

中文:
引理 partialRightAdjointHomEquiv_map_comp
  结论: {X : C} {Y Y' : F.PartialRightAdjointSource}
  证明: by
  rw [partialRightAdjointHomEquiv_comp]; rw [partialRightAdjointHomEquiv_map]; rw [← assoc]; rw [← partialRightAdjointHomEquiv_comp]; rw [comp_id]

@[reassoc]

Depends on / 依赖: comp_id, partialRightAdjointHomEquiv_comp, partialRightAdjointHomEquiv_map
-/
lemma partialRightAdjointHomEquiv_map_comp {X : C} {Y Y' : F.PartialRightAdjointSource}
    (f : X ⟶ F.partialRightAdjointObj Y) (g : Y ⟶ Y') :
    F.partialRightAdjointHomEquiv (f ≫ F.partialRightAdjointMap g) =
      F.partialRightAdjointHomEquiv f ≫ g.hom := by
  rw [partialRightAdjointHomEquiv_comp]; rw [partialRightAdjointHomEquiv_map]; rw [← assoc]; rw [← partialRightAdjointHomEquiv_comp]; rw [comp_id]

@[reassoc]
/--
lemma `partialRightAdjointHomEquiv_comp_symm` / 引理 `partialRightAdjointHomEquiv_comp_symm`

English:
lemma partialRightAdjointHomEquiv_comp_symm
  statement: {X X' : C} {Y : F.PartialRightAdjointSource}
  proof: RepresentableBy.comp_homEquiv_symm ..

@[reassoc]

中文:
引理 partialRightAdjointHomEquiv_comp_symm
  结论: {X X' : C} {Y : F.PartialRightAdjointSource}
  证明: RepresentableBy.comp_homEquiv_symm ..

@[reassoc]

Depends on / 依赖: RepresentableBy, RepresentableBy.comp_homEquiv_symm, comp_homEquiv_symm
-/
lemma partialRightAdjointHomEquiv_comp_symm {X X' : C} {Y : F.PartialRightAdjointSource}
    (f : F.obj X' ⟶ Y.obj) (g : X ⟶ X') :
    g ≫ F.partialRightAdjointHomEquiv.symm f =
      F.partialRightAdjointHomEquiv.symm (F.map g ≫ f) :=
  RepresentableBy.comp_homEquiv_symm ..

@[reassoc]
/--
lemma `partialRightAdjointHomEquiv_symm_comp` / 引理 `partialRightAdjointHomEquiv_symm_comp`

English:
lemma partialRightAdjointHomEquiv_symm_comp
  statement: {X : C} {Y Y' : F.PartialRightAdjointSource}
  proof: by
  simp [Equiv.eq_symm_apply, partialRightAdjointHomEquiv_map_comp]

中文:
引理 partialRightAdjointHomEquiv_symm_comp
  结论: {X : C} {Y Y' : F.PartialRightAdjointSource}
  证明: by
  simp [Equiv.eq_symm_apply, partialRightAdjointHomEquiv_map_comp]

Depends on / 依赖: Equiv.eq_symm_apply, eq_symm_apply, partialRightAdjointHomEquiv_map_comp
-/
lemma partialRightAdjointHomEquiv_symm_comp {X : C} {Y Y' : F.PartialRightAdjointSource}
    (f : F.obj X ⟶ Y.obj) (g : Y ⟶ Y') :
    F.partialRightAdjointHomEquiv.symm f ≫ F.partialRightAdjointMap g =
      F.partialRightAdjointHomEquiv.symm (f ≫ g.hom) := by
  simp [Equiv.eq_symm_apply, partialRightAdjointHomEquiv_map_comp]

/-- Given `F : C ⥤ D`, this is the partial adjoint functor `F.PartialRightAdjointSource ⥤ C`. -/
@[simps]
/--
Definition of `partialRightAdjoint` / `partialRightAdjoint` 的定义

English:
definition partialRightAdjoint
  signature: : F.PartialRightAdjointSource ⥤ C where
  body: F.partialRightAdjointObj
  map := F.partialRightAdjointMap
  map_id X := by
    apply F.partialRightAdjointHomEquiv.injective
    simp [partialRightAdjointHomEquiv_map]
  map_comp {X Y Z} f g := by
    apply F.partialRightAdjointHomEquiv.injective
    simp [partialRightAdjointHomEquiv_comp, ← assoc,

中文:
定义 partialRightAdjoint
  签名: : F.PartialRightAdjointSource ⥤ C where
  定义体: F.partialRightAdjointObj
  map := F.partialRightAdjointMap
  map_id X := by
    apply F.partialRightAdjointHomEquiv.injective
    simp [partialRightAdjointHomEquiv_map]
  map_comp {X Y Z} f g := by
    apply F.partialRightAdjointHomEquiv.injective
    simp [partialRightAdjointHomEquiv_comp, ← assoc,

Depends on / 依赖: F.partialRightAdjointObj, partialRightAdjointObj
-/
noncomputable def partialRightAdjoint : F.PartialRightAdjointSource ⥤ C where
  obj := F.partialRightAdjointObj
  map := F.partialRightAdjointMap
  map_id X := by
    apply F.partialRightAdjointHomEquiv.injective
    simp [partialRightAdjointHomEquiv_map]
  map_comp {X Y Z} f g := by
    apply F.partialRightAdjointHomEquiv.injective
    simp [partialRightAdjointHomEquiv_comp, ← assoc, ← F.partialRightAdjointHomEquiv_comp]

variable {F}

/--
lemma `isLeftAdjoint_of_rightAdjointObjIsDefined_eq_top` / 引理 `isLeftAdjoint_of_rightAdjointObjIsDefined_eq_top`

English:
lemma isLeftAdjoint_of_rightAdjointObjIsDefined_eq_top
  proof: by
  replace h : forall X, IsRepresentable (F.op ⋙ yoneda.obj X) := fun X => by
    simp only [← rightAdjointObjIsDefined_iff, h, Pi.top_apply, Prop.top_eq_true]
  exact (Adjunction.adjunctionOfEquivRight
    (fun X Y => (F.op ⋙ yoneda.obj Y).representableBy.homEquiv.symm)
    (fun X Y Y' g f => (Re

中文:
引理 isLeftAdjoint_of_rightAdjointObjIsDefined_eq_top
  证明: by
  replace h : forall X, IsRepresentable (F.op ⋙ yoneda.obj X) := fun X => by
    simp only [← rightAdjointObjIsDefined_iff, h, Pi.top_apply, Prop.top_eq_true]
  exact (Adjunction.adjunctionOfEquivRight
    (fun X Y => (F.op ⋙ yoneda.obj Y).representableBy.homEquiv.symm)
    (fun X Y Y' g f => (Re

Depends on / 依赖: Adjunction, Adjunction.adjunctionOfEquivRight, F.op, IsRepresentable, Pi.top_apply, Prop.top_eq_true, RepresentableBy, RepresentableBy.comp_homEquiv_symm, adjunctionOfEquivRight, comp_homEquiv_symm, homEquiv, isLeftAdjoint, replace, representableBy, representableBy.homEquiv.symm, rightAdjointObjIsDefined_iff, top_apply, top_eq_true, yoneda, yoneda.obj
-/
lemma isLeftAdjoint_of_rightAdjointObjIsDefined_eq_top
    (h : F.rightAdjointObjIsDefined = ⊤) : F.IsLeftAdjoint := by
  replace h : forall X, IsRepresentable (F.op ⋙ yoneda.obj X) := fun X => by
    simp only [← rightAdjointObjIsDefined_iff, h, Pi.top_apply, Prop.top_eq_true]
  exact (Adjunction.adjunctionOfEquivRight
    (fun X Y => (F.op ⋙ yoneda.obj Y).representableBy.homEquiv.symm)
    (fun X Y Y' g f => (RepresentableBy.comp_homEquiv_symm ..).symm)).isLeftAdjoint

variable (F) in
/--
lemma `isLeftAdjoint_iff_rightAdjointObjIsDefined_eq_top` / 引理 `isLeftAdjoint_iff_rightAdjointObjIsDefined_eq_top`

English:
lemma isLeftAdjoint_iff_rightAdjointObjIsDefined_eq_top
  proof: by
  refine ⟨fun h => ?_, isLeftAdjoint_of_rightAdjointObjIsDefined_eq_top⟩
  ext X
  simpa only [Pi.top_apply, Prop.top_eq_true, iff_true]
    using rightAdjointObjIsDefined_of_adjunction (Adjunction.ofIsLeftAdjoint F) X

中文:
引理 isLeftAdjoint_iff_rightAdjointObjIsDefined_eq_top
  证明: by
  refine ⟨fun h => ?_, isLeftAdjoint_of_rightAdjointObjIsDefined_eq_top⟩
  ext X
  simpa only [Pi.top_apply, Prop.top_eq_true, iff_true]
    using rightAdjointObjIsDefined_of_adjunction (Adjunction.ofIsLeftAdjoint F) X

Depends on / 依赖: Adjunction, Adjunction.ofIsLeftAdjoint, Pi.top_apply, Prop.top_eq_true, iff_true, isLeftAdjoint_of_rightAdjointObjIsDefined_eq_top, ofIsLeftAdjoint, rightAdjointObjIsDefined_of_adjunction, top_apply, top_eq_true
-/
lemma isLeftAdjoint_iff_rightAdjointObjIsDefined_eq_top :
    F.IsLeftAdjoint ↔ F.rightAdjointObjIsDefined = ⊤ := by
  refine ⟨fun h => ?_, isLeftAdjoint_of_rightAdjointObjIsDefined_eq_top⟩
  ext X
  simpa only [Pi.top_apply, Prop.top_eq_true, iff_true]
    using rightAdjointObjIsDefined_of_adjunction (Adjunction.ofIsLeftAdjoint F) X

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `representableByCompYonedaObjOfIsLimit` / `representableByCompYonedaObjOfIsLimit` 的定义

English:
definition representableByCompYonedaObjOfIsLimit
  signature: {J : Type*} [Category* J]
  body: { toFun := fun f => hc.lift (Cone.mk _
        { app := fun j => F.partialRightAdjointHomEquiv (f ≫ c'.π.app j)
          naturality := fun j j' φ => by
            dsimp
            rw [id_comp]; rw [← c'.w φ]; rw [← partialRightAdjointHomEquiv_map_comp]; rw [← assoc]
            dsimp })
      inv

中文:
定义 representableByCompYonedaObjOfIsLimit
  签名: {J : 类型} [范畴* J]
  定义体: { toFun := fun f => hc.lift (Cone.mk _
        { app := fun j => F.partialRightAdjointHomEquiv (f ≫ c'.π.app j)
          naturality := fun j j' φ => by
            dsimp
            rw [id_comp]; rw [← c'.w φ]; rw [← partialRightAdjointHomEquiv_map_comp]; rw [← assoc]
            dsimp })
      inv

Depends on / 依赖: Cone.mk, Equiv.apply_symm_apply, F.partialRightAdjointHomEquiv, F.partialRightAdjointHomEquiv.injective, F.partialRightAdjointHomEquiv.symm, apply_symm_apply, hc.lift, id_comp, injective, invFun, naturality, partialRightAdjointHomEquiv, partialRightAdjointHomEquiv_map_comp
-/
noncomputable def representableByCompYonedaObjOfIsLimit {J : Type*} [Category* J]
    {R : J ⥤ F.PartialRightAdjointSource}
    {c : Cone (R ⋙ ObjectProperty.ι _)} (hc : IsLimit c)
    {c' : Cone (R ⋙ F.partialRightAdjoint)} (hc' : IsLimit c') :
    (F.op ⋙ yoneda.obj c.pt).RepresentableBy c'.pt where
  homEquiv {Y} :=
    { toFun := fun f => hc.lift (Cone.mk _
        { app := fun j => F.partialRightAdjointHomEquiv (f ≫ c'.π.app j)
          naturality := fun j j' φ => by
            dsimp
            rw [id_comp]; rw [← c'.w φ]; rw [← partialRightAdjointHomEquiv_map_comp]; rw [← assoc]
            dsimp })
      invFun := fun g => hc'.lift (Cone.mk _
        { app := fun j => F.partialRightAdjointHomEquiv.symm (g ≫ c.π.app j)
          naturality := fun j j' φ => by
            apply F.partialRightAdjointHomEquiv.injective
            have := c.w φ
            dsimp at this ⊢
            rw [id_comp]; rw [Equiv.apply_symm_apply]; rw [partialRightAdjointHomEquiv_map_comp]; rw [Equiv.apply_symm_apply]; rw [assoc]; rw [this] })
      left_inv := fun f => hc'.hom_ext (fun j => by simp)
      right_inv := fun g => hc.hom_ext (fun j => by simp) }
  homEquiv_comp {Y Y'} g f := hc.hom_ext (fun j => by
    dsimp
    simp only [IsLimit.fac, partialRightAdjointHomEquiv_comp, assoc])

/--
lemma `rightAdjointObjIsDefined_of_isLimit` / 引理 `rightAdjointObjIsDefined_of_isLimit`

English:
lemma rightAdjointObjIsDefined_of_isLimit
  statement: {J : Type*} [Category* J] {R : J ⥤ D} {c : Cone R}
  proof: (representableByCompYonedaObjOfIsLimit
    (R := ObjectProperty.lift _ R h) hc (limit.isLimit _)).isRepresentable

中文:
引理 rightAdjointObjIsDefined_of_isLimit
  结论: {J : 类型} [范畴* J] {R : J ⥤ D} {c : 锥 R}
  证明: (representableByCompYonedaObjOfIsLimit
    (R := ObjectProperty.lift _ R h) hc (limit.isLimit _)).isRepresentable

Depends on / 依赖: ObjectProperty, ObjectProperty.lift, isLimit, isRepresentable, limit.isLimit, representableByCompYonedaObjOfIsLimit
-/
lemma rightAdjointObjIsDefined_of_isLimit {J : Type*} [Category* J] {R : J ⥤ D} {c : Cone R}
    (hc : IsLimit c) [HasLimitsOfShape J C]
    (h : forall (j : J), F.rightAdjointObjIsDefined (R.obj j)) :
    F.rightAdjointObjIsDefined c.pt :=
  (representableByCompYonedaObjOfIsLimit
    (R := ObjectProperty.lift _ R h) hc (limit.isLimit _)).isRepresentable

/--
lemma `rightAdjointObjIsDefined_limit` / 引理 `rightAdjointObjIsDefined_limit`

English:
lemma rightAdjointObjIsDefined_limit
  statement: {J : Type*} [Category* J] (R : J ⥤ D)
  proof: rightAdjointObjIsDefined_of_isLimit (limit.isLimit R) h

中文:
引理 rightAdjointObjIsDefined_limit
  结论: {J : 类型} [范畴* J] (R : J ⥤ D)
  证明: rightAdjointObjIsDefined_of_isLimit (limit.isLimit R) h

Depends on / 依赖: isLimit, limit.isLimit, rightAdjointObjIsDefined_of_isLimit
-/
lemma rightAdjointObjIsDefined_limit {J : Type*} [Category* J] (R : J ⥤ D)
    [HasLimit R] [HasLimitsOfShape J C]
    (h : forall (j : J), F.rightAdjointObjIsDefined (R.obj j)) :
    F.rightAdjointObjIsDefined (limit R) :=
  rightAdjointObjIsDefined_of_isLimit (limit.isLimit R) h

end partialRightAdjoint

end Functor

end CategoryTheory
