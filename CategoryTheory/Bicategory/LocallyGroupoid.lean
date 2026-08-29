/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Core
public import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo

/-!
# (2,1)-categories

A bicategory `B` is said to be locally groupoidal (or a (2,1)-category) if for every pair
of objects `x, y`, the Hom-category `x ⟶ y` is a groupoid (which is expressed using the
`CategoryTheory.IsGroupoid` typeclass).

Given a bicategory `B`, we construct a bicategory `Pith B` which is obtained from `B`
by discarding non-invertible 2-morphisms. This is realized in practice by applying
`Core` to each hom-category of `C`. By construction, `Pith B` is a (2,1)-category,
and for every (2,1)-category B', every pseudofunctor `B' ⥤ B` factors (essentially) uniquely
through the inclusion from `Pith B` to `B` (see
`CategoryTheory.Bicategory.Pith.pseudofunctorToPith`).

## References
- [Kerodon, section 1.2.2](https://kerodon.net/tag/02GD).

-/

@[expose] public section

namespace CategoryTheory.Bicategory

open Bicategory

universe w₁ w₂ v₁ v₂ u₁ u₂

/-- A bicategory is locally groupoidal if the categories of 1-morphisms are groupoids. -/
@[kerodon 009Q]
/--
Definition of `IsLocallyGroupoid` / `IsLocallyGroupoid` 的定义

English:
abbreviation IsLocallyGroupoid
  signature: (B : Type u₁) [Bicategory.{w₁, v₁} B]
  body: forall (b c : B), IsGroupoid (b ⟶ c)

中文:
缩写 IsLocallyGroupoid
  签名: (B : 类型u₁) [双范畴.{w₁, v₁} B]
  定义体: forall (b c : B), IsGroupoid (b ⟶ c)

Depends on / 依赖: IsGroupoid
-/
abbrev IsLocallyGroupoid (B : Type u₁) [Bicategory.{w₁, v₁} B] := forall (b c : B), IsGroupoid (b ⟶ c)

/-- Given a bicategory `B`, `Pith B` is the bicategory obtained by discarding the non-invertible
2-cells from `B`. We implement this as a wrapper type for `B`, and use `CategoryTheory.Core`
to discard the non-invertible morphisms. -/
@[kerodon 00AL]
/--
Definition of `Pith` / `Pith` 的定义

English:
structure Pith
  parameters: (B : Type u₁)
  axioms and operations (1):
    - as : B

中文:
结构 Pith
  参数: (B : 类型u₁)
  公理与运算 (1 个):
    - as : B
-/
structure Pith (B : Type u₁) where
  /-- The underlying object of the bicategory. -/
  as : B

namespace Pith

variable (B : Type u₁)

/--
theorem `mk_as` / 定理 `mk_as`

English:
theorem mk_as
  given: (b : Pith B)
  statement: mk b.as = b
  proof: rfl

中文:
定理 mk_as
  条件: (b : Pith B)
  结论: mk b.as = b
  证明: rfl

Depends on / 依赖: F.property, property
-/
theorem mk_as (b : Pith B) : mk b.as = b := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: B] : Inhabited (Pith B)
  body: ⟨⟨default⟩⟩

中文:
实例 [可居
  签名: B] : 可居 (Pith B)
  定义体: ⟨⟨default⟩⟩

Depends on / 依赖: F.property, property
-/
instance [Inhabited B] : Inhabited (Pith B) := ⟨⟨default⟩⟩

/--
Instance `categoryStruct` / 实例 `categoryStruct`

English:
instance categoryStruct
  signature: [Bicategory.{w₁, v₁} B]
  body: Core (a.as ⟶ b.as)
  id a := ⟨𝟙 a.as⟩
  comp f g := ⟨f.of ≫ g.of⟩

中文:
实例 categoryStruct
  签名: [双范畴.{w₁, v₁} B]
  定义体: Core (a.as ⟶ b.as)
  id a := ⟨𝟙 a.as⟩
  comp f g := ⟨f.of ≫ g.of⟩

Depends on / 依赖: F.property, a.as, b.as, property
-/
instance categoryStruct [Bicategory.{w₁, v₁} B] : CategoryStruct (Pith B) where
  Hom a b := Core (a.as ⟶ b.as)
  id a := ⟨𝟙 a.as⟩
  comp f g := ⟨f.of ≫ g.of⟩

variable [Bicategory.{w₁, v₁} B]

-- @[simps!] in categoryStruct puts `Core (a.as ⟶ b.as)` in the hyps for the next two
-- lemmas, so we record them manually instead.
@[simp]
/--
lemma `id_of` / 引理 `id_of`

English:
lemma id_of
  given: (a : Pith B)
  statement: (𝟙 a : a ⟶ a).of = 𝟙 a.as
  proof: rfl

@[simp]

中文:
引理 id_of
  条件: (a : Pith B)
  结论: (𝟙 a : a ⟶ a).of = 𝟙 a.as
  证明: rfl

@[simp]

Depends on / 依赖: F.property, property
-/
lemma id_of (a : Pith B) : (𝟙 a : a ⟶ a).of = 𝟙 a.as := rfl

@[simp]
/--
lemma `comp_of` / 引理 `comp_of`

English:
lemma comp_of
  given: {a b c : Pith B} (f : a ⟶ b) (g : b ⟶ c)
  statement: (f ≫ g).of = f.of ≫ g.of
  proof: rfl

中文:
引理 comp_of
  条件: {a b c : Pith B} (f : a ⟶ b) (g : b ⟶ c)
  结论: (f ≫ g).of = f.of ≫ g.of
  证明: rfl
-/
lemma comp_of {a b c : Pith B} (f : a ⟶ b) (g : b ⟶ c) : (f ≫ g).of = f.of ≫ g.of := rfl

/--
Instance `homGroupoid` / 实例 `homGroupoid`

English:
instance homGroupoid
  signature: (a b : Pith B)
  body: inferInstanceAs Groupoid Core _

@[ext]

中文:
实例 homGroupoid
  签名: (a b : Pith B)
  定义体: inferInstanceAs Groupoid Core _

@[ext]

Depends on / 依赖: Groupoid
-/
instance homGroupoid (a b : Pith B) :
Groupoid.{w₁} (a ⟶ b) := inferInstanceAs Groupoid Core _

@[ext]
/--
lemma `hom₂_ext` / 引理 `hom₂_ext`

English:
lemma hom₂_ext
  given: {a b : Pith B} {x y : a ⟶ b} {f g : x ⟶ y} (h : f.iso.hom = g.iso.hom)
  proof: CoreHom.ext Iso.ext h

@[simp, reassoc]

中文:
引理 hom₂_ext
  条件: {a b : Pith B} {x y : a ⟶ b} {f g : x ⟶ y} (h : f.iso.hom = g.iso.hom)
  证明: CoreHom.ext Iso.ext h

@[simp, reassoc]

Depends on / 依赖: CoreHom, CoreHom.ext, Iso.ext
-/
lemma hom₂_ext {a b : Pith B} {x y : a ⟶ b} {f g : x ⟶ y} (h : f.iso.hom = g.iso.hom) :
f = g := CoreHom.ext Iso.ext h

@[simp, reassoc]
/--
lemma `comp₂_iso_hom` / 引理 `comp₂_iso_hom`

English:
lemma comp₂_iso_hom
  given: {a b : Pith B} {x y z : a ⟶ b} {f : x ⟶ y} {g : y ⟶ z}
  proof: rfl

@[simp, reassoc]

中文:
引理 comp₂_iso_hom
  条件: {a b : Pith B} {x y z : a ⟶ b} {f : x ⟶ y} {g : y ⟶ z}
  证明: rfl

@[simp, reassoc]
-/
lemma comp₂_iso_hom {a b : Pith B} {x y z : a ⟶ b} {f : x ⟶ y} {g : y ⟶ z} :
    (f ≫ g).iso.hom = f.iso.hom ≫ g.iso.hom := rfl

@[simp, reassoc]
/--
lemma `comp₂_iso_inv` / 引理 `comp₂_iso_inv`

English:
lemma comp₂_iso_inv
  given: {a b : Pith B} {x y z : a ⟶ b} {f : x ⟶ y} {g : y ⟶ z}
  proof: rfl

@[simp]

中文:
引理 comp₂_iso_inv
  条件: {a b : Pith B} {x y z : a ⟶ b} {f : x ⟶ y} {g : y ⟶ z}
  证明: rfl

@[simp]
-/
lemma comp₂_iso_inv {a b : Pith B} {x y z : a ⟶ b} {f : x ⟶ y} {g : y ⟶ z} :
    (f ≫ g).iso.inv = g.iso.inv ≫ f.iso.inv := rfl

@[simp]
/--
lemma `id₂_iso_hom` / 引理 `id₂_iso_hom`

English:
lemma id₂_iso_hom
  given: {a b : Pith B} {x : a ⟶ b}
  statement: (𝟙 x : x ⟶ x).iso.hom = 𝟙 _
  proof: rfl

@[simp]

中文:
引理 id₂_iso_hom
  条件: {a b : Pith B} {x : a ⟶ b}
  结论: (𝟙 x : x ⟶ x).iso.hom = 𝟙 _
  证明: rfl

@[simp]
-/
lemma id₂_iso_hom {a b : Pith B} {x : a ⟶ b} : (𝟙 x : x ⟶ x).iso.hom = 𝟙 _ := rfl

@[simp]
/--
lemma `id₂_iso_inv` / 引理 `id₂_iso_inv`

English:
lemma id₂_iso_inv
  given: {a b : Pith B} {x : a ⟶ b}
  statement: (𝟙 x : x ⟶ x).iso.inv = 𝟙 _
  proof: rfl

@[simps! whiskerLeft_iso_hom whiskerLeft_iso_inv whiskerRight_iso_hom whiskerRight_iso_inv
associator_hom_iso associator_inv_iso_hom associator_inv_iso_inv leftUnitor_hom_iso
leftUnitor_inv_iso_hom rightUnitor_hom_iso rightUnitor_inv_iso_hom rightUnitor_inv_iso_inv]

中文:
引理 id₂_iso_inv
  条件: {a b : Pith B} {x : a ⟶ b}
  结论: (𝟙 x : x ⟶ x).iso.inv = 𝟙 _
  证明: rfl

@[simps! whiskerLeft_iso_hom whiskerLeft_iso_inv whiskerRight_iso_hom whiskerRight_iso_inv
associator_hom_iso associator_inv_iso_hom associator_inv_iso_inv leftUnitor_hom_iso
leftUnitor_inv_iso_hom rightUnitor_hom_iso rightUnitor_inv_iso_hom rightUnitor_inv_iso_inv]
-/
lemma id₂_iso_inv {a b : Pith B} {x : a ⟶ b} : (𝟙 x : x ⟶ x).iso.inv = 𝟙 _ := rfl

@[simps! whiskerLeft_iso_hom whiskerLeft_iso_inv whiskerRight_iso_hom whiskerRight_iso_inv
associator_hom_iso associator_inv_iso_hom associator_inv_iso_inv leftUnitor_hom_iso
leftUnitor_inv_iso_hom rightUnitor_hom_iso rightUnitor_inv_iso_hom rightUnitor_inv_iso_inv]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Bicategory.{w₁, v₁} (Pith B)
  body: CoreHom.mk whiskerLeftIso x.of (CoreHom.iso f)
whiskerRight f y := CoreHom.mk whiskerRightIso (CoreHom.iso f) y.of
leftUnitor x := Core.isoMk leftUnitor x.of
rightUnitor x := Core.isoMk rightUnitor x.of
associator x y z := Core.isoMk associator x.of y.of z.of
  whisker_exchange η θ := by
    ext
   

中文:
实例 :
  签名: 双范畴.{w₁, v₁} (Pith B)
  定义体: CoreHom.mk whiskerLeftIso x.of (CoreHom.iso f)
whiskerRight f y := CoreHom.mk whiskerRightIso (CoreHom.iso f) y.of
leftUnitor x := Core.isoMk leftUnitor x.of
rightUnitor x := Core.isoMk rightUnitor x.of
associator x y z := Core.isoMk associator x.of y.of z.of
  whisker_exchange η θ := by
    ext
   

Depends on / 依赖: CoreHom, CoreHom.iso, CoreHom.mk, whiskerLeftIso, x.of
-/
instance : Bicategory.{w₁, v₁} (Pith B) where
whiskerLeft x _ _ f := CoreHom.mk whiskerLeftIso x.of (CoreHom.iso f)
whiskerRight f y := CoreHom.mk whiskerRightIso (CoreHom.iso f) y.of
leftUnitor x := Core.isoMk leftUnitor x.of
rightUnitor x := Core.isoMk rightUnitor x.of
associator x y z := Core.isoMk associator x.of y.of z.of
  whisker_exchange η θ := by
    ext
    simp [whisker_exchange]

/-- The pith is a (2,1)-category. -/
example : IsLocallyGroupoid (Pith B) := by infer_instance

/-- The canonical inclusion from the pith of `B` to `B`, as a Pseudofunctor. -/
@[simps]
/--
Definition of `inclusion` / `inclusion` 的定义

English:
definition inclusion
  signature: : Pseudofunctor (Pith B) B where
  body: x.as
  map f := f.of
  map₂ η := η.iso.hom
  mapId _ := .refl _
  mapComp _ _ := .refl _

中文:
定义 inclusion
  签名: : Pseudofunctor (Pith B) B where
  定义体: x.as
  map f := f.of
  map₂ η := η.iso.hom
  mapId _ := .refl _
  mapComp _ _ := .refl _

Depends on / 依赖: x.as
-/
def inclusion : Pseudofunctor (Pith B) B where
  obj x := x.as
  map f := f.of
  map₂ η := η.iso.hom
  mapId _ := .refl _
  mapComp _ _ := .refl _

variable {B} in
/-- Any pseudofunctor from a (2,1)-category to a bicategory factors through
the pith of the target bicategory. -/
@[simps!]
/--
Definition of `pseudofunctorToPith` / `pseudofunctorToPith` 的定义

English:
definition pseudofunctorToPith
  signature: {B' : Type u₂} [Bicategory.{w₂, v₂} B']
  body: .mk F.obj x
map f := .mk F.map f
map₂ f := .mk asIso F.map₂ f
mapId x := Core.isoMk F.mapId x
mapComp f g := Core.isoMk F.mapComp f g

中文:
定义 pseudofunctorToPith
  签名: {B' : 类型u₂} [双范畴.{w₂, v₂} B']
  定义体: .mk F.obj x
map f := .mk F.map f
map₂ f := .mk asIso F.map₂ f
mapId x := Core.isoMk F.mapId x
mapComp f g := Core.isoMk F.mapComp f g

Depends on / 依赖: F.obj
-/
noncomputable def pseudofunctorToPith {B' : Type u₂} [Bicategory.{w₂, v₂} B']
    [IsLocallyGroupoid B'] (F : Pseudofunctor B' B) :
    Pseudofunctor B' (Pith B) where
obj x := .mk F.obj x
map f := .mk F.map f
map₂ f := .mk asIso F.map₂ f
mapId x := Core.isoMk F.mapId x
mapComp f g := Core.isoMk F.mapComp f g

section

variable {B} {B' : Type u₂} [Bicategory.{w₂, v₂} B'] [IsLocallyGroupoid B'] (F : Pseudofunctor B' B)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `pseudofunctorToPithCompInclusionStrongIsoHom` / `pseudofunctorToPithCompInclusionStrongIsoHom` 的定义

English:
definition pseudofunctorToPithCompInclusionStrongIsoHom
  signature: :
  body: 𝟙 _
  naturality f := (ρ_ _) ≪≫ (fun_ _).symm

中文:
定义 pseudofunctorToPithCompInclusionStrongIsoHom
  签名: :
  定义体: 𝟙 _
  naturality f := (ρ_ _) ≪≫ (fun_ _).symm

Depends on / 依赖: hasFilteredColimitsOfSize_of_hasColimitsOfSize
-/
noncomputable def pseudofunctorToPithCompInclusionStrongIsoHom :
    ((pseudofunctorToPith F).comp (inclusion B)).StrongTrans F where
  app b' := 𝟙 _
  naturality f := (ρ_ _) ≪≫ (fun_ _).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `pseudofunctorToPithCompInclusionStrongIsoInv` / `pseudofunctorToPithCompInclusionStrongIsoInv` 的定义

English:
definition pseudofunctorToPithCompInclusionStrongIsoInv
  signature: :
  body: 𝟙 _
  naturality f := (ρ_ _) ≪≫ (fun_ _).symm

中文:
定义 pseudofunctorToPithCompInclusionStrongIsoInv
  签名: :
  定义体: 𝟙 _
  naturality f := (ρ_ _) ≪≫ (fun_ _).symm

Depends on / 依赖: hasCofilteredLimitsOfSize_of_hasLimitsOfSize
-/
noncomputable def pseudofunctorToPithCompInclusionStrongIsoInv :
    F.StrongTrans ((pseudofunctorToPith F).comp (inclusion B)) where
  app b' := 𝟙 _
  naturality f := (ρ_ _) ≪≫ (fun_ _).symm

end

end Pith

variable {B : Type u₁} [Bicategory.{w₁, v₁} B]

/-- If `B` is a (2,1)-category, then every lax functor `F` from a bicategory to `B` defines a
`CategoryTheory.LaxFunctor.PseudoCore` structure on `F` that can be used to promote `F` to a
pseudofunctor using `CategoryTheory.Pseudofunctor.mkOfLax`. -/
@[simps! mapIdIso_hom mapCompIso_hom]
/--
Definition of `Pseudofunctor.ofLaxFunctorToLocallyGroupoid` / `Pseudofunctor.ofLaxFunctorToLocallyGroupoid` 的定义

English:
definition Pseudofunctor.ofLaxFunctorToLocallyGroupoid
  body: (asIso (F.mapId x)).symm
  mapCompIso f g := (asIso <| F.mapComp f g).symm

中文:
定义 Pseudofunctor.ofLaxFunctorToLocallyGroupoid
  定义体: (asIso (F.mapId x)).symm
  mapCompIso f g := (asIso <| F.mapComp f g).symm

Depends on / 依赖: F.mapId, hasLimitsOfShape_of_has_cofiltered_limits
-/
noncomputable def Pseudofunctor.ofLaxFunctorToLocallyGroupoid
    {B' : Type u₂} [Bicategory.{w₂, v₂} B'] [IsLocallyGroupoid B] (F : LaxFunctor B' B) :
    F.PseudoCore where
  mapIdIso x := (asIso (F.mapId x)).symm
  mapCompIso f g := (asIso <| F.mapComp f g).symm

/-- If `B` is a (2,1)-category, then every oplax functor `F` from a bicategory to `B` defines
a `CategoryTheory.OplaxFunctor.PseudoCore` structure on `F` that can be used to promote `F`
to a pseudofunctor using `CategoryTheory.Pseudofunctor.mkOfOplax`. -/
@[simps! mapIdIso_inv mapCompIso_inv]
/--
Definition of `Pseudofunctor.ofOplaxFunctorToLocallyGroupoid` / `Pseudofunctor.ofOplaxFunctorToLocallyGroupoid` 的定义

English:
definition Pseudofunctor.ofOplaxFunctorToLocallyGroupoid
  body: asIso (F.mapId x)
  mapCompIso f g := asIso (F.mapComp f g)

中文:
定义 Pseudofunctor.ofOplaxFunctorToLocallyGroupoid
  定义体: asIso (F.mapId x)
  mapCompIso f g := asIso (F.mapComp f g)

Depends on / 依赖: F.mapId, hasColimitsOfShape_of_has_filtered_colimits
-/
noncomputable def Pseudofunctor.ofOplaxFunctorToLocallyGroupoid
    {B' : Type u₂} [Bicategory.{w₂, v₂} B'] [IsLocallyGroupoid B] (F : OplaxFunctor B' B) :
    F.PseudoCore where
  mapIdIso x := asIso (F.mapId x)
  mapCompIso f g := asIso (F.mapComp f g)

end CategoryTheory.Bicategory
