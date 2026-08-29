/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne, Joseph Hua
-/
module

public import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete
public import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo

/-!
# The Grothendieck and CoGrothendieck constructions

## The Grothendieck construction

Given a category `𝒮` and any pseudofunctor `F` from `𝒮` to `Cat`, we associate to it a category
`∫ F`, defined as follows:
* Objects: pairs `(S, a)` where `S` is an object of the base category and `a` is an object of the
  category `F(S)`.
* Morphisms: morphisms `(R, b) ⟶ (S, a)` are defined as pairs `(f, h)` where `f : R ⟶ S` is a
  morphism in `𝒮` and `h : F(f)(a) ⟶ b`

The category `∫ F` is equipped with a projection functor `∫ F ⥤ 𝒮`,
given by projecting to the first factors, i.e.
* On objects, it sends `(S, a)` to `S`
* On morphisms, it sends `(f, h)` to `f`

## The CoGrothendieck construction

Given a category `𝒮` and any pseudofunctor `F` from `𝒮ᵒᵖ` to `Cat`,
we associate to it a category `∫ᶜ F`, defined as follows:
* Objects: pairs `(S, a)` where `S` is an object of the base category and `a` is an object of the
  category `F(S)`.
* Morphisms: morphisms `(R, b) ⟶ (S, a)` are defined as pairs `(f, h)` where `f : R ⟶ S` is a
  morphism in `𝒮` and `h : b ⟶ F(f)(a)`

The category `∫ᶜ F` is equipped with a functor `∫ᶜ F ⥤ 𝒮`,
given by projecting to the first factors, i.e.
* On objects, it sends `(S, a)` to `S`
* On morphisms, it sends `(f, h)` to `f`

## Naming conventions

The name `Grothendieck` is reserved for the construction on covariant pseudofunctors from `𝒮` to
`Cat`, whereas the word `CoGrothendieck` is used for the contravariant construction.
This is consistent with the convention for the Grothendieck construction on 1-functors
`CategoryTheory.Grothendieck`.

## Future work / TODO

1. Once the bicategory of pseudofunctors has been defined, show that this construction forms a
   pseudofunctor from `LocallyDiscrete 𝒮 ⥤ᵖ Catᵒᵖ` to `Cat`.
2. Deduce the results in `CategoryTheory.Grothendieck` as a specialization of
   `Pseudofunctor.Grothendieck`.

## References
[Vistoli2008] "Notes on Grothendieck Topologies, Fibered Categories and Descent Theory" by
Angelo Vistoli

-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

namespace CategoryTheory.Pseudofunctor

universe w v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory.Functor Category Opposite Discrete Bicategory StrongTrans

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮]

/-- The type of objects in the fibered category associated to a pseudofunctor from a
1-category to Cat. -/
@[ext]
/--
Definition of `Grothendieck` / `Grothendieck` 的定义

English:
structure Grothendieck
  parameters: (F : LocallyDiscrete 𝒮 ⥤ᵖ Cat.{v₂, u₂})
  axioms and operations (2):
    - base : 𝒮
    - fiber : F.obj ⟨base⟩

中文:
结构 Grothendieck
  参数: (F : LocallyDiscrete 𝒮 ⥤ᵖ Cat.{v₂, u₂})
  公理与运算 (2 个):
    - base : 𝒮
    - fiber : F.obj ⟨base⟩
-/
structure Grothendieck (F : LocallyDiscrete 𝒮 ⥤ᵖ Cat.{v₂, u₂}) where
  /-- The underlying object in the base category. -/
  base : 𝒮
  /-- The object in the fiber of the base object. -/
  fiber : F.obj ⟨base⟩

namespace Grothendieck

variable {F : LocallyDiscrete 𝒮 ⥤ᵖ Cat.{v₂, u₂}}

/-- Notation for the Grothendieck category associated to a pseudofunctor `F`. -/
scoped prefix:75 "∫ " => Grothendieck

/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (X Y : ∫ F)
  axioms and operations (2):
    - base : X.base ⟶ Y.base
    - fiber : (F.map base.toLoc).toFunctor.obj X.fiber ⟶ Y.fiber

中文:
结构 Hom
  参数: (X Y : ∫ F)
  公理与运算 (2 个):
    - base : X.base ⟶ Y.base
    - fiber : (F.map base.toLoc).toFunctor.obj X.fiber ⟶ Y.fiber
-/
structure Hom (X Y : ∫ F) where
  /-- The morphism between base objects. -/
  base : X.base ⟶ Y.base
  /-- The morphism in the fiber over the domain. -/
  fiber : (F.map base.toLoc).toFunctor.obj X.fiber ⟶ Y.fiber

@[simps! id_base id_fiber comp_base comp_fiber]
/--
Instance `categoryStruct` / 实例 `categoryStruct`

English:
instance categoryStruct
  signature: : CategoryStruct (∫ F) where
  body: Hom X Y
  id X := {
    base := 𝟙 X.base
    fiber := (F.mapId ⟨X.base⟩).hom.toNatTrans.app X.fiber }
  comp {X _ _} f g := {
    base := f.base ≫ g.base
    fiber := (F.mapComp f.base.toLoc g.base.toLoc).hom.toNatTrans.app X.fiber ≫
      (F.map g.base.toLoc).toFunctor.map f.fiber ≫ g.fiber }

中文:
实例 categoryStruct
  签名: : CategoryStruct (∫ F) where
  定义体: Hom X Y
  id X := {
    base := 𝟙 X.base
    fiber := (F.mapId ⟨X.base⟩).hom.toNatTrans.app X.fiber }
  comp {X _ _} f g := {
    base := f.base ≫ g.base
    fiber := (F.mapComp f.base.toLoc g.base.toLoc).hom.toNatTrans.app X.fiber ≫
      (F.map g.base.toLoc).toFunctor.map f.fiber ≫ g.fiber }
-/
instance categoryStruct : CategoryStruct (∫ F) where
  Hom X Y := Hom X Y
  id X := {
    base := 𝟙 X.base
    fiber := (F.mapId ⟨X.base⟩).hom.toNatTrans.app X.fiber }
  comp {X _ _} f g := {
    base := f.base ≫ g.base
    fiber := (F.mapComp f.base.toLoc g.base.toLoc).hom.toNatTrans.app X.fiber ≫
      (F.map g.base.toLoc).toFunctor.map f.fiber ≫ g.fiber }

instance (X : ∫ F) : Inhabited (Hom X X) :=
  ⟨𝟙 X⟩

section

variable {a b : ∫ F}

@[ext (iff := false)]
/--
lemma `Hom.ext` / 引理 `Hom.ext`

English:
lemma Hom.ext
  statement: (f g : a ⟶ b) (hfg₁ : f.base = g.base)
  proof: by
  cases f; cases g
  dsimp at hfg₁ hfg₂
  cat_disch

中文:
引理 Hom.ext
  结论: (f g : a ⟶ b) (hfg₁ : f.base = g.base)
  证明: by
  cases f; cases g
  dsimp at hfg₁ hfg₂
  cat_disch
-/
lemma Hom.ext (f g : a ⟶ b) (hfg₁ : f.base = g.base)
    (hfg₂ : eqToHom (hfg₁ ▸ rfl) ≫ f.fiber = g.fiber) : f = g := by
  cases f; cases g
  dsimp at hfg₁ hfg₂
  cat_disch

/--
lemma `Hom.ext_iff` / 引理 `Hom.ext_iff`

English:
lemma Hom.ext_iff
  given: (f g : a ⟶ b)
  proof: by subst hfg; simp
  mpr := fun ⟨hfg₁, hfg₂⟩ => Hom.ext f g hfg₁ hfg₂

中文:
引理 Hom.ext_iff
  条件: (f g : a ⟶ b)
  证明: by subst hfg; simp
  mpr := fun ⟨hfg₁, hfg₂⟩ => Hom.ext f g hfg₁ hfg₂

Depends on / 依赖: Hom.ext
-/
lemma Hom.ext_iff (f g : a ⟶ b) :
    f = g ↔ exists (hfg : f.base = g.base), eqToHom (hfg ▸ rfl) ≫ f.fiber = g.fiber where
  mp hfg := by subst hfg; simp
  mpr := fun ⟨hfg₁, hfg₂⟩ => Hom.ext f g hfg₁ hfg₂

/--
lemma `Hom.congr` / 引理 `Hom.congr`

English:
lemma Hom.congr
  given: {a b : ∫ F} {f g : a ⟶ b} (h : f = g)
  proof: by
  subst h
  simp

中文:
引理 Hom.congr
  条件: {a b : ∫ F} {f g : a ⟶ b} (h : f = g)
  证明: by
  subst h
  simp
-/
lemma Hom.congr {a b : ∫ F} {f g : a ⟶ b} (h : f = g) :
    f.fiber = eqToHom (h ▸ rfl) ≫ g.fiber := by
  subst h
  simp

end

set_option backward.isDefEq.respectTransparency false in
attribute [local simp] PrelaxFunctor.map₂_eqToHom in
/--
Instance `category` / 实例 `category`

English:
instance category
  signature: : Category (∫ F) where
  body: Pseudofunctor.Grothendieck.categoryStruct
  id_comp {a b} f := by
    ext
    · simp
    · simp [F.mapComp_id_left_hom_app, Strict.leftUnitor_eqToIso, ← Functor.map_comp_assoc,
        ← Cat.Hom₂.comp_app]
  comp_id {a b} f := by
    ext
    · simp
    · simp [F.mapComp_id_right_hom_app, Strict.righ

中文:
实例 category
  签名: : Category (∫ F) where
  定义体: Pseudofunctor.Grothendieck.categoryStruct
  id_comp {a b} f := by
    ext
    · simp
    · simp [F.mapComp_id_left_hom_app, Strict.leftUnitor_eqToIso, ← Functor.map_comp_assoc,
        ← Cat.Hom₂.comp_app]
  comp_id {a b} f := by
    ext
    · simp
    · simp [F.mapComp_id_right_hom_app, Strict.righ

Depends on / 依赖: Grothendieck, Pseudofunctor, Pseudofunctor.Grothendieck.categoryStruct, categoryStruct
-/
instance category : Category (∫ F) where
  toCategoryStruct := Pseudofunctor.Grothendieck.categoryStruct
  id_comp {a b} f := by
    ext
    · simp
    · simp [F.mapComp_id_left_hom_app, Strict.leftUnitor_eqToIso, ← Functor.map_comp_assoc,
        ← Cat.Hom₂.comp_app]
  comp_id {a b} f := by
    ext
    · simp
    · simp [F.mapComp_id_right_hom_app, Strict.rightUnitor_eqToIso, ← reassoc_of% Cat.Hom₂.comp_app]
  assoc f g h := by
    ext
    · simp
    · simp [mapComp_assoc_right_hom_app_assoc, Strict.associator_eqToIso]

variable (F)

/-- The projection `∫ F ⥤ 𝒮` given by projecting both objects and homs to the first factor. -/
@[simps]
/--
Definition of `forget` / `forget` 的定义

English:
definition forget
  signature: (F : Pseudofunctor (LocallyDiscrete 𝒮) Cat.{v₂, u₂})
  body: X.base
  map f := f.base

中文:
定义 forget
  签名: (F : Pseudofunctor (LocallyDiscrete 𝒮) Cat.{v₂, u₂})
  定义体: X.base
  map f := f.base

Depends on / 依赖: X.base
-/
def forget (F : Pseudofunctor (LocallyDiscrete 𝒮) Cat.{v₂, u₂}) : ∫ F ⥤ 𝒮 where
  obj X := X.base
  map f := f.base

section

attribute [local simp]
  Strict.leftUnitor_eqToIso Strict.rightUnitor_eqToIso Strict.associator_eqToIso

variable {F} {G : Pseudofunctor (LocallyDiscrete 𝒮) Cat.{v₂, u₂}}
  {H : Pseudofunctor (LocallyDiscrete 𝒮) Cat.{v₂, u₂}}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The Grothendieck construction is functorial: a strong natural transformation `α : F ⟶ G`
induces a functor `Grothendieck.map : ∫ F ⥤ ∫ G`. -/
@[simps!]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (α : F ⟶ G)
  body: {
    base := a.base
    fiber := (α.app ⟨a.base⟩).toFunctor.obj a.fiber }
  map {a b} f := {
    base := f.1
    fiber := (α.naturality f.1.toLoc).inv.toNatTrans.app a.fiber ≫
      (α.app ⟨b.base⟩).toFunctor.map f.2 }
  map_id a := by
    ext
    · dsimp
    · simp [StrongTrans.naturality_id_inv_a

中文:
定义 map
  签名: (α : F ⟶ G)
  定义体: {
    base := a.base
    fiber := (α.app ⟨a.base⟩).toFunctor.obj a.fiber }
  map {a b} f := {
    base := f.1
    fiber := (α.naturality f.1.toLoc).inv.toNatTrans.app a.fiber ≫
      (α.app ⟨b.base⟩).toFunctor.map f.2 }
  map_id a := by
    ext
    · dsimp
    · simp [StrongTrans.naturality_id_inv_a
-/
def map (α : F ⟶ G) : ∫ F ⥤ ∫ G where
  obj a := {
    base := a.base
    fiber := (α.app ⟨a.base⟩).toFunctor.obj a.fiber }
  map {a b} f := {
    base := f.1
    fiber := (α.naturality f.1.toLoc).inv.toNatTrans.app a.fiber ≫
      (α.app ⟨b.base⟩).toFunctor.map f.2 }
  map_id a := by
    ext
    · dsimp
    · simp [StrongTrans.naturality_id_inv_app, ← map_comp, ← Cat.Hom₂.comp_app]
  map_comp {a b c} f g := by
    ext
    · dsimp
    · simp only [Cat.Hom.comp_toFunctor, comp_obj, categoryStruct_comp_base, Quiver.Hom.comp_toLoc,
        categoryStruct_comp_fiber, eqToHom_refl, map_comp, ← Cat.Hom.comp_map, assoc,
        NatTrans.naturality_assoc]
      simp [naturality_comp_inv_app, ← Functor.map_comp, ← reassoc_of% Cat.Hom₂.comp_app]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `map_id_map` / 引理 `map_id_map`

English:
lemma map_id_map
  given: {x y : ∫ F} (f : x ⟶ y)
  statement: (map (𝟙 F)).map f = f
  proof: by
  ext <;> simp

@[simp]

中文:
引理 map_id_map
  条件: {x y : ∫ F} (f : x ⟶ y)
  结论: (map (𝟙 F)).map f = f
  证明: by
  ext <;> simp

@[simp]
-/
lemma map_id_map {x y : ∫ F} (f : x ⟶ y) : (map (𝟙 F)).map f = f := by
  ext <;> simp

@[simp]
/--
theorem `map_comp_forget` / 定理 `map_comp_forget`

English:
theorem map_comp_forget
  given: (α : F ⟶ G)
  statement: map α ⋙ forget G = forget F
  proof: rfl

中文:
定理 map_comp_forget
  条件: (α : F ⟶ G)
  结论: map α ⋙ forget G = forget F
  证明: rfl
-/
theorem map_comp_forget (α : F ⟶ G) : map α ⋙ forget G = forget F := rfl

section

variable (F)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `mapIdIso` / `mapIdIso` 的定义

English:
definition mapIdIso
  signature: : map (𝟙 F) ≅ 𝟭 (∫ F)
  body: NatIso.ofComponents (fun _ => eqToIso (by cat_disch))

中文:
定义 mapIdIso
  签名: : map (𝟙 F) ≅ 𝟭 (∫ F)
  定义体: NatIso.ofComponents (fun _ => eqToIso (by cat_disch))

Depends on / 依赖: NatIso, NatIso.ofComponents, cat_disch, eqToIso, ofComponents
-/
def mapIdIso : map (𝟙 F) ≅ 𝟭 (∫ F) :=
  NatIso.ofComponents (fun _ => eqToIso (by cat_disch))

/--
lemma `map_id_eq` / 引理 `map_id_eq`

English:
lemma map_id_eq
  statement: map (𝟙 F) = 𝟭 (∫ F)
  proof: Functor.ext_of_iso (mapIdIso F) (fun x => by simp [map]) (fun x => by simp [mapIdIso])

中文:
引理 map_id_eq
  结论: map (𝟙 F) = 𝟭 (∫ F)
  证明: Functor.ext_of_iso (mapIdIso F) (fun x => by simp [map]) (fun x => by simp [mapIdIso])

Depends on / 依赖: Functor, Functor.ext_of_iso, ext_of_iso, mapIdIso
-/
lemma map_id_eq : map (𝟙 F) = 𝟭 (∫ F) :=
  Functor.ext_of_iso (mapIdIso F) (fun x => by simp [map]) (fun x => by simp [mapIdIso])

end

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `mapCompIso` / `mapCompIso` 的定义

English:
definition mapCompIso
  signature: (α : F ⟶ G) (β : G ⟶ H)
  body: NatIso.ofComponents (fun _ => eqToIso (by cat_disch)) (fun f => by
    dsimp
    simp only [comp_id, id_comp]
    ext <;> simp)

中文:
定义 mapCompIso
  签名: (α : F ⟶ G) (β : G ⟶ H)
  定义体: NatIso.ofComponents (fun _ => eqToIso (by cat_disch)) (fun f => by
    dsimp
    simp only [comp_id, id_comp]
    ext <;> simp)

Depends on / 依赖: NatIso, NatIso.ofComponents, cat_disch, comp_id, eqToIso, id_comp, ofComponents
-/
def mapCompIso (α : F ⟶ G) (β : G ⟶ H) : map (α ≫ β) ≅ map α ⋙ map β :=
  NatIso.ofComponents (fun _ => eqToIso (by cat_disch)) (fun f => by
    dsimp
    simp only [comp_id, id_comp]
    ext <;> simp)

/--
lemma `map_comp_eq` / 引理 `map_comp_eq`

English:
lemma map_comp_eq
  given: (α : F ⟶ G) (β : G ⟶ H)
  statement: map (α ≫ β) = map α ⋙ map β
  proof: Functor.ext_of_iso (mapCompIso α β) (fun _ => by simp [map]) (fun _ => by simp [mapCompIso])

中文:
引理 map_comp_eq
  条件: (α : F ⟶ G) (β : G ⟶ H)
  结论: map (α ≫ β) = map α ⋙ map β
  证明: Functor.ext_of_iso (mapCompIso α β) (fun _ => by simp [map]) (fun _ => by simp [mapCompIso])

Depends on / 依赖: Functor, Functor.ext_of_iso, ext_of_iso, mapCompIso
-/
lemma map_comp_eq (α : F ⟶ G) (β : G ⟶ H) : map (α ≫ β) = map α ⋙ map β :=
  Functor.ext_of_iso (mapCompIso α β) (fun _ => by simp [map]) (fun _ => by simp [mapCompIso])

end

end Grothendieck

/-- The type of objects in the fibered category associated to a contravariant
pseudofunctor from a 1-category to Cat. -/
@[ext]
/--
Definition of `CoGrothendieck` / `CoGrothendieck` 的定义

English:
structure CoGrothendieck
  parameters: (F : LocallyDiscrete 𝒮ᵒᵖ ⥤ᵖ Cat.{v₂, u₂})
  axioms and operations (2):
    - base : 𝒮
    - fiber : F.obj ⟨op base⟩

中文:
结构 CoGrothendieck
  参数: (F : LocallyDiscrete 𝒮ᵒᵖ ⥤ᵖ Cat.{v₂, u₂})
  公理与运算 (2 个):
    - base : 𝒮
    - fiber : F.obj ⟨op base⟩
-/
structure CoGrothendieck (F : LocallyDiscrete 𝒮ᵒᵖ ⥤ᵖ Cat.{v₂, u₂}) where
  /-- The underlying object in the base category. -/
  base : 𝒮
  /-- The object in the fiber of the base object. -/
  fiber : F.obj ⟨op base⟩

namespace CoGrothendieck

variable {F : LocallyDiscrete 𝒮ᵒᵖ ⥤ᵖ Cat.{v₂, u₂}}

/-- Notation for the CoGrothendieck category associated to a pseudofunctor `F`. -/
scoped prefix:75 "∫ᶜ " => CoGrothendieck

/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (X Y : ∫ᶜ F)
  axioms and operations (2):
    - base : X.base ⟶ Y.base
    - fiber : X.fiber ⟶ (F.map base.op.toLoc).toFunctor.obj Y.fiber

中文:
结构 Hom
  参数: (X Y : ∫ᶜ F)
  公理与运算 (2 个):
    - base : X.base ⟶ Y.base
    - fiber : X.fiber ⟶ (F.map base.op.toLoc).toFunctor.obj Y.fiber
-/
structure Hom (X Y : ∫ᶜ F) where
  /-- The morphism between base objects. -/
  base : X.base ⟶ Y.base
  /-- The morphism in the fiber over the domain. -/
  fiber : X.fiber ⟶ (F.map base.op.toLoc).toFunctor.obj Y.fiber

@[simps! id_base id_fiber comp_base comp_fiber]
/--
Instance `categoryStruct` / 实例 `categoryStruct`

English:
instance categoryStruct
  signature: : CategoryStruct (∫ᶜ F) where
  body: Hom X Y
  id X := {
    base := 𝟙 X.base
    fiber := (F.mapId ⟨op X.base⟩).inv.toNatTrans.app X.fiber }
  comp {_ _ Z} f g := {
    base := f.base ≫ g.base
    fiber := f.fiber ≫ (F.map f.base.op.toLoc).toFunctor.map g.fiber ≫
      (F.mapComp g.base.op.toLoc f.base.op.toLoc).inv.toNatTrans.app Z.f

中文:
实例 categoryStruct
  签名: : CategoryStruct (∫ᶜ F) where
  定义体: Hom X Y
  id X := {
    base := 𝟙 X.base
    fiber := (F.mapId ⟨op X.base⟩).inv.toNatTrans.app X.fiber }
  comp {_ _ Z} f g := {
    base := f.base ≫ g.base
    fiber := f.fiber ≫ (F.map f.base.op.toLoc).toFunctor.map g.fiber ≫
      (F.mapComp g.base.op.toLoc f.base.op.toLoc).inv.toNatTrans.app Z.f
-/
instance categoryStruct : CategoryStruct (∫ᶜ F) where
  Hom X Y := Hom X Y
  id X := {
    base := 𝟙 X.base
    fiber := (F.mapId ⟨op X.base⟩).inv.toNatTrans.app X.fiber }
  comp {_ _ Z} f g := {
    base := f.base ≫ g.base
    fiber := f.fiber ≫ (F.map f.base.op.toLoc).toFunctor.map g.fiber ≫
      (F.mapComp g.base.op.toLoc f.base.op.toLoc).inv.toNatTrans.app Z.fiber }

instance (X : ∫ᶜ F) : Inhabited (Hom X X) :=
  ⟨𝟙 X⟩

section

variable {a b : ∫ᶜ F}

@[ext (iff := false)]
/--
lemma `Hom.ext` / 引理 `Hom.ext`

English:
lemma Hom.ext
  statement: (f g : a ⟶ b) (hfg₁ : f.base = g.base)
  proof: by
  cases f; cases g
  dsimp at hfg₁
  cat_disch

中文:
引理 Hom.ext
  结论: (f g : a ⟶ b) (hfg₁ : f.base = g.base)
  证明: by
  cases f; cases g
  dsimp at hfg₁
  cat_disch
-/
lemma Hom.ext (f g : a ⟶ b) (hfg₁ : f.base = g.base)
    (hfg₂ : f.fiber = g.fiber ≫ eqToHom (hfg₁ ▸ rfl)) : f = g := by
  cases f; cases g
  dsimp at hfg₁
  cat_disch

/--
lemma `Hom.ext_iff` / 引理 `Hom.ext_iff`

English:
lemma Hom.ext_iff
  given: (f g : a ⟶ b)
  proof: ⟨by rw [hfg], by simp [hfg]⟩
  mpr := fun ⟨hfg₁, hfg₂⟩ => Hom.ext f g hfg₁ hfg₂

中文:
引理 Hom.ext_iff
  条件: (f g : a ⟶ b)
  证明: ⟨by rw [hfg], by simp [hfg]⟩
  mpr := fun ⟨hfg₁, hfg₂⟩ => Hom.ext f g hfg₁ hfg₂
-/
lemma Hom.ext_iff (f g : a ⟶ b) :
    f = g ↔ exists (hfg : f.base = g.base), f.fiber = g.fiber ≫ eqToHom (hfg ▸ rfl) where
  mp hfg := ⟨by rw [hfg], by simp [hfg]⟩
  mpr := fun ⟨hfg₁, hfg₂⟩ => Hom.ext f g hfg₁ hfg₂

/--
lemma `Hom.congr` / 引理 `Hom.congr`

English:
lemma Hom.congr
  given: {a b : ∫ᶜ F} {f g : a ⟶ b} (h : f = g)
  proof: by
  simp [h]

中文:
引理 Hom.congr
  条件: {a b : ∫ᶜ F} {f g : a ⟶ b} (h : f = g)
  证明: by
  simp [h]
-/
lemma Hom.congr {a b : ∫ᶜ F} {f g : a ⟶ b} (h : f = g) :
    f.fiber = g.fiber ≫ eqToHom (h ▸ rfl) := by
  simp [h]

end

set_option backward.isDefEq.respectTransparency false in
attribute [local simp] PrelaxFunctor.map₂_eqToHom in
/--
Instance `category` / 实例 `category`

English:
instance category
  signature: : Category (∫ᶜ F) where
  body: Pseudofunctor.CoGrothendieck.categoryStruct
  id_comp {a b} f := by
    ext
    · simp
    · simp [F.mapComp_id_right_inv_app, Strict.rightUnitor_eqToIso, ← NatTrans.naturality_assoc,
        ← Cat.Hom₂.comp_app]
  comp_id {a b} f := by
    ext
    · simp
    · simp [F.mapComp_id_left_inv_app, Stric

中文:
实例 category
  签名: : Category (∫ᶜ F) where
  定义体: Pseudofunctor.CoGrothendieck.categoryStruct
  id_comp {a b} f := by
    ext
    · simp
    · simp [F.mapComp_id_right_inv_app, Strict.rightUnitor_eqToIso, ← NatTrans.naturality_assoc,
        ← Cat.Hom₂.comp_app]
  comp_id {a b} f := by
    ext
    · simp
    · simp [F.mapComp_id_left_inv_app, Stric

Depends on / 依赖: CoGrothendieck, Pseudofunctor, Pseudofunctor.CoGrothendieck.categoryStruct, categoryStruct
-/
instance category : Category (∫ᶜ F) where
  toCategoryStruct := Pseudofunctor.CoGrothendieck.categoryStruct
  id_comp {a b} f := by
    ext
    · simp
    · simp [F.mapComp_id_right_inv_app, Strict.rightUnitor_eqToIso, ← NatTrans.naturality_assoc,
        ← Cat.Hom₂.comp_app]
  comp_id {a b} f := by
    ext
    · simp
    · simp [F.mapComp_id_left_inv_app, Strict.leftUnitor_eqToIso, ← Functor.map_comp_assoc,
        ← Cat.Hom₂.comp_app]
  assoc f g h := by
    ext
    · simp
    · simp [← NatTrans.naturality_assoc, F.mapComp_assoc_right_inv_app, Strict.associator_eqToIso]

variable (F)

/-- The projection `∫ᶜ F ⥤ 𝒮` given by projecting both objects and homs to the first factor. -/
@[simps]
/--
Definition of `forget` / `forget` 的定义

English:
definition forget
  signature: (F : LocallyDiscrete 𝒮ᵒᵖ ⥤ᵖ Cat.{v₂, u₂})
  body: X.base
  map f := f.base

中文:
定义 forget
  签名: (F : LocallyDiscrete 𝒮ᵒᵖ ⥤ᵖ Cat.{v₂, u₂})
  定义体: X.base
  map f := f.base

Depends on / 依赖: X.base
-/
def forget (F : LocallyDiscrete 𝒮ᵒᵖ ⥤ᵖ Cat.{v₂, u₂}) : ∫ᶜ F ⥤ 𝒮 where
  obj X := X.base
  map f := f.base

section

attribute [local simp]
  Strict.leftUnitor_eqToIso Strict.rightUnitor_eqToIso Strict.associator_eqToIso

variable {F} {G : LocallyDiscrete 𝒮ᵒᵖ ⥤ᵖ Cat.{v₂, u₂}}
  {H : LocallyDiscrete 𝒮ᵒᵖ ⥤ᵖ Cat.{v₂, u₂}}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The CoGrothendieck construction is functorial: a strong natural transformation `α : F ⟶ G`
induces a functor `CoGrothendieck.map : ∫ᶜ F ⥤ ∫ᶜ G`. -/
@[simps!]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (α : F ⟶ G)
  body: {
    base := a.base
    fiber := (α.app ⟨op a.base⟩).toFunctor.obj a.fiber }
  map {a b} f := {
    base := f.1
    fiber := (α.app ⟨op a.base⟩).toFunctor.map f.2 ≫
      (α.naturality f.1.op.toLoc).hom.toNatTrans.app b.fiber }
  map_id a := by
    ext1
    · dsimp
    · simp [Cat.Hom.comp_toFuncto

中文:
定义 map
  签名: (α : F ⟶ G)
  定义体: {
    base := a.base
    fiber := (α.app ⟨op a.base⟩).toFunctor.obj a.fiber }
  map {a b} f := {
    base := f.1
    fiber := (α.app ⟨op a.base⟩).toFunctor.map f.2 ≫
      (α.naturality f.1.op.toLoc).hom.toNatTrans.app b.fiber }
  map_id a := by
    ext1
    · dsimp
    · simp [Cat.Hom.comp_toFuncto
-/
def map (α : F ⟶ G) : ∫ᶜ F ⥤ ∫ᶜ G where
  obj a := {
    base := a.base
    fiber := (α.app ⟨op a.base⟩).toFunctor.obj a.fiber }
  map {a b} f := {
    base := f.1
    fiber := (α.app ⟨op a.base⟩).toFunctor.map f.2 ≫
      (α.naturality f.1.op.toLoc).hom.toNatTrans.app b.fiber }
  map_id a := by
    ext1
    · dsimp
    · simp [Cat.Hom.comp_toFunctor, naturality_id_hom_app, Cat.Hom.id_toFunctor, ← Category.assoc,
        ← Functor.map_comp, ← Cat.Hom₂.comp_app]
  map_comp {a b c} f g := by
    ext
    · dsimp
    · simp only [categoryStruct_comp_base, op_comp, Quiver.Hom.comp_toLoc,
        categoryStruct_comp_fiber, Cat.Hom.comp_toFunctor, map_comp, naturality_comp_hom_app, assoc,
        eqToHom_refl, comp_id]
      slice_lhs 2 4 => simp [← Cat.Hom.toNatIso_inv, Cat.Hom.comp_toFunctor,
        ← Cat.Hom.toNatIso_hom, ← map_comp, Iso.inv_hom_id_app, comp_obj, map_id, comp_id]
      simp only [assoc, ← reassoc_of% Cat.Hom.comp_map,
        Cat.Hom.comp_toFunctor, Functor.comp_obj, NatTrans.naturality_assoc]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `map_id_map` / 引理 `map_id_map`

English:
lemma map_id_map
  given: {x y : ∫ᶜ F} (f : x ⟶ y)
  statement: (map (𝟙 F)).map f = f
  proof: by
  ext <;> simp

@[simp]

中文:
引理 map_id_map
  条件: {x y : ∫ᶜ F} (f : x ⟶ y)
  结论: (map (𝟙 F)).map f = f
  证明: by
  ext <;> simp

@[simp]
-/
lemma map_id_map {x y : ∫ᶜ F} (f : x ⟶ y) : (map (𝟙 F)).map f = f := by
  ext <;> simp

@[simp]
/--
theorem `map_comp_forget` / 定理 `map_comp_forget`

English:
theorem map_comp_forget
  given: (α : F ⟶ G)
  statement: map α ⋙ forget G = forget F
  proof: rfl

中文:
定理 map_comp_forget
  条件: (α : F ⟶ G)
  结论: map α ⋙ forget G = forget F
  证明: rfl
-/
theorem map_comp_forget (α : F ⟶ G) : map α ⋙ forget G = forget F := rfl

section

variable (F)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `mapIdIso` / `mapIdIso` 的定义

English:
definition mapIdIso
  signature: : map (𝟙 F) ≅ 𝟭 (∫ᶜ F)
  body: NatIso.ofComponents (fun _ => eqToIso (by cat_disch))

中文:
定义 mapIdIso
  签名: : map (𝟙 F) ≅ 𝟭 (∫ᶜ F)
  定义体: NatIso.ofComponents (fun _ => eqToIso (by cat_disch))

Depends on / 依赖: NatIso, NatIso.ofComponents, cat_disch, eqToIso, ofComponents
-/
def mapIdIso : map (𝟙 F) ≅ 𝟭 (∫ᶜ F) :=
  NatIso.ofComponents (fun _ => eqToIso (by cat_disch))

/--
lemma `map_id_eq` / 引理 `map_id_eq`

English:
lemma map_id_eq
  statement: map (𝟙 F) = 𝟭 (∫ᶜ F)
  proof: Functor.ext_of_iso (mapIdIso F) (fun x => by simp [map]) (fun x => by simp [mapIdIso])

中文:
引理 map_id_eq
  结论: map (𝟙 F) = 𝟭 (∫ᶜ F)
  证明: Functor.ext_of_iso (mapIdIso F) (fun x => by simp [map]) (fun x => by simp [mapIdIso])

Depends on / 依赖: Functor, Functor.ext_of_iso, ext_of_iso, mapIdIso
-/
lemma map_id_eq : map (𝟙 F) = 𝟭 (∫ᶜ F) :=
  Functor.ext_of_iso (mapIdIso F) (fun x => by simp [map]) (fun x => by simp [mapIdIso])

end

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `mapCompIso` / `mapCompIso` 的定义

English:
definition mapCompIso
  signature: (α : F ⟶ G) (β : G ⟶ H)
  body: NatIso.ofComponents (fun _ => eqToIso (by cat_disch)) (fun f => by
    dsimp
    simp only [comp_id, id_comp]
    ext <;> simp)

中文:
定义 mapCompIso
  签名: (α : F ⟶ G) (β : G ⟶ H)
  定义体: NatIso.ofComponents (fun _ => eqToIso (by cat_disch)) (fun f => by
    dsimp
    simp only [comp_id, id_comp]
    ext <;> simp)

Depends on / 依赖: NatIso, NatIso.ofComponents, cat_disch, comp_id, eqToIso, id_comp, ofComponents
-/
def mapCompIso (α : F ⟶ G) (β : G ⟶ H) : map (α ≫ β) ≅ map α ⋙ map β :=
  NatIso.ofComponents (fun _ => eqToIso (by cat_disch)) (fun f => by
    dsimp
    simp only [comp_id, id_comp]
    ext <;> simp)

/--
lemma `map_comp_eq` / 引理 `map_comp_eq`

English:
lemma map_comp_eq
  given: (α : F ⟶ G) (β : G ⟶ H)
  statement: map (α ≫ β) = map α ⋙ map β
  proof: Functor.ext_of_iso (mapCompIso α β) (fun _ => by simp [map]) (fun _ => by simp [mapCompIso])

中文:
引理 map_comp_eq
  条件: (α : F ⟶ G) (β : G ⟶ H)
  结论: map (α ≫ β) = map α ⋙ map β
  证明: Functor.ext_of_iso (mapCompIso α β) (fun _ => by simp [map]) (fun _ => by simp [mapCompIso])

Depends on / 依赖: Functor, Functor.ext_of_iso, ext_of_iso, mapCompIso
-/
lemma map_comp_eq (α : F ⟶ G) (β : G ⟶ H) : map (α ≫ β) = map α ⋙ map β :=
  Functor.ext_of_iso (mapCompIso α β) (fun _ => by simp [map]) (fun _ => by simp [mapCompIso])

end

end Pseudofunctor.CoGrothendieck

end CategoryTheory
