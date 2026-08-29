/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.Order.BooleanAlgebra.Defs

/-!
# Essential image of a functor

The essential image `essImage` of a functor consists of the objects in the target category which
are isomorphic to an object in the image of the object function.
This, for instance, allows us to talk about objects belonging to a subcategory expressed as a
functor rather than a subtype, preserving the principle of equivalence. For example this lets us
define exponential ideals.

The essential image can also be seen as a subcategory of the target category, and witnesses that
a functor decomposes into an essentially surjective functor and a fully faithful functor.
(TODO: show that this decomposition forms an orthogonal factorisation system).
-/

@[expose] public section


universe v₁ v₂ v₃ u₁ u₂ u₃

noncomputable section

namespace CategoryTheory

variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] {F : C ⥤ D} {G : D ⥤ E}

namespace Functor

/--
Definition of `essImage` / `essImage` 的定义

English:
definition essImage
  signature: (F : C ⥤ D)
  body: fun Y => exists X : C, Nonempty (F.obj X ≅ Y)

中文:
定义 essImage
  签名: (F : C ⥤ D)
  定义体: fun Y => exists X : C, Nonempty (F.obj X ≅ Y)

Depends on / 依赖: F.obj, Nonempty
-/
def essImage (F : C ⥤ D) : ObjectProperty D := fun Y => exists X : C, Nonempty (F.obj X ≅ Y)

/--
Definition of `essImage.witness` / `essImage.witness` 的定义

English:
definition essImage.witness
  signature: {Y : D} (h : F.essImage Y)
  body: h.choose

中文:
定义 essImage.witness
  签名: {Y : D} (h : F.essImage Y)
  定义体: h.choose

Depends on / 依赖: h.choose
-/
def essImage.witness {Y : D} (h : F.essImage Y) : C :=
  h.choose

/--
lemma `isoClosure_eq_essImage` / 引理 `isoClosure_eq_essImage`

English:
lemma isoClosure_eq_essImage
  statement: ObjectProperty.isoClosure (· in Set.range F.obj) = F.essImage
  proof: by
  ext
  exact ⟨fun ⟨_, ⟨Z, rfl⟩, ⟨e⟩⟩ => ⟨Z, ⟨e.symm⟩⟩, fun ⟨Z, ⟨e⟩⟩ => ⟨F.obj Z, ⟨Z, rfl⟩, ⟨e.symm⟩⟩⟩

中文:
引理 isoClosure_eq_essImage
  结论: Object命题erty.isoClosure (· in Set.range F.obj) = F.essImage
  证明: by
  ext
  exact ⟨fun ⟨_, ⟨Z, rfl⟩, ⟨e⟩⟩ => ⟨Z, ⟨e.symm⟩⟩, fun ⟨Z, ⟨e⟩⟩ => ⟨F.obj Z, ⟨Z, rfl⟩, ⟨e.symm⟩⟩⟩

Depends on / 依赖: F.obj, e.symm
-/
lemma isoClosure_eq_essImage : ObjectProperty.isoClosure (· in Set.range F.obj) = F.essImage := by
  ext
  exact ⟨fun ⟨_, ⟨Z, rfl⟩, ⟨e⟩⟩ => ⟨Z, ⟨e.symm⟩⟩, fun ⟨Z, ⟨e⟩⟩ => ⟨F.obj Z, ⟨Z, rfl⟩, ⟨e.symm⟩⟩⟩

/--
Definition of `essImage.getIso` / `essImage.getIso` 的定义

English:
definition essImage.getIso
  signature: {Y : D} (h : F.essImage Y)
  body: Classical.choice h.choose_spec

中文:
定义 essImage.getIso
  签名: {Y : D} (h : F.essImage Y)
  定义体: Classical.choice h.choose_spec

Depends on / 依赖: Classical, Classical.choice, choice, choose_spec, h.choose_spec
-/
def essImage.getIso {Y : D} (h : F.essImage Y) : F.obj h.witness ≅ Y :=
  Classical.choice h.choose_spec

/--
theorem `essImage.ofIso` / 定理 `essImage.ofIso`

English:
theorem essImage.ofIso
  given: {Y Y' : D} (h : Y ≅ Y') (hY : essImage F Y)
  statement: essImage F Y'
  proof: hY.imp fun _ => Nonempty.map (· ≪≫ h)

中文:
定理 essImage.ofIso
  条件: {Y Y' : D} (h : Y ≅ Y') (hY : essImage F Y)
  结论: essImage F Y'
  证明: hY.imp fun _ => Nonempty.map (· ≪≫ h)

Depends on / 依赖: Nonempty, Nonempty.map, hY.imp
-/
theorem essImage.ofIso {Y Y' : D} (h : Y ≅ Y') (hY : essImage F Y) : essImage F Y' :=
  hY.imp fun _ => Nonempty.map (· ≪≫ h)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: F.essImage.IsClosedUnderIsomorphisms
  body: essImage.ofIso e h

中文:
实例 :
  签名: F.essImage.IsClosedUnderIsomorphisms
  定义体: essImage.ofIso e h

Depends on / 依赖: essImage, essImage.ofIso
-/
instance : F.essImage.IsClosedUnderIsomorphisms where
  of_iso e h := essImage.ofIso e h

/--
theorem `essImage.ofNatIso` / 定理 `essImage.ofNatIso`

English:
theorem essImage.ofNatIso
  given: {F' : C ⥤ D} (h : F ≅ F') {Y : D} (hY : essImage F Y)
  proof: hY.imp fun X => Nonempty.map fun t => h.symm.app X ≪≫ t

中文:
定理 essImage.ofNatIso
  条件: {F' : C ⥤ D} (h : F ≅ F') {Y : D} (hY : essImage F Y)
  证明: hY.imp fun X => Nonempty.map fun t => h.symm.app X ≪≫ t

Depends on / 依赖: Nonempty, Nonempty.map, h.symm.app, hY.imp
-/
theorem essImage.ofNatIso {F' : C ⥤ D} (h : F ≅ F') {Y : D} (hY : essImage F Y) :
    essImage F' Y :=
  hY.imp fun X => Nonempty.map fun t => h.symm.app X ≪≫ t

/--
theorem `essImage_eq_of_natIso` / 定理 `essImage_eq_of_natIso`

English:
theorem essImage_eq_of_natIso
  given: {F' : C ⥤ D} (h : F ≅ F')
  statement: essImage F = essImage F'
  proof: funext fun _ => propext ⟨essImage.ofNatIso h, essImage.ofNatIso h.symm⟩

中文:
定理 essImage_eq_of_natIso
  条件: {F' : C ⥤ D} (h : F ≅ F')
  结论: essImage F = essImage F'
  证明: funext fun _ => propext ⟨essImage.ofNatIso h, essImage.ofNatIso h.symm⟩

Depends on / 依赖: essImage, essImage.ofNatIso, h.symm, ofNatIso, propext
-/
theorem essImage_eq_of_natIso {F' : C ⥤ D} (h : F ≅ F') : essImage F = essImage F' :=
  funext fun _ => propext ⟨essImage.ofNatIso h, essImage.ofNatIso h.symm⟩

/--
theorem `obj_mem_essImage` / 定理 `obj_mem_essImage`

English:
theorem obj_mem_essImage
  given: (F : D ⥤ C) (Y : D)
  statement: essImage F (F.obj Y)
  proof: ⟨Y, ⟨Iso.refl _⟩⟩

中文:
定理 obj_mem_essImage
  条件: (F : D ⥤ C) (Y : D)
  结论: essImage F (F.obj Y)
  证明: ⟨Y, ⟨Iso.refl _⟩⟩

Depends on / 依赖: Iso.refl
-/
theorem obj_mem_essImage (F : D ⥤ C) (Y : D) : essImage F (F.obj Y) :=
  ⟨Y, ⟨Iso.refl _⟩⟩

/--
Definition of `EssImageSubcategory` / `EssImageSubcategory` 的定义

English:
abbreviation EssImageSubcategory
  signature: (F : C ⥤ D)
  body: F.essImage.FullSubcategory

中文:
缩写 EssImageSubcategory
  签名: (F : C ⥤ D)
  定义体: F.essImage.FullSubcategory

Depends on / 依赖: F.essImage.FullSubcategory, FullSubcategory, essImage
-/
abbrev EssImageSubcategory (F : C ⥤ D) := F.essImage.FullSubcategory

/--
lemma `essImage_ext` / 引理 `essImage_ext`

English:
lemma essImage_ext
  statement: (F : C ⥤ D) {X Y : F.EssImageSubcategory} (f g : X ⟶ Y)
  proof: F.essImage.ι.map_injective h

中文:
引理 essImage_ext
  结论: (F : C ⥤ D) {X Y : F.EssImageSubcategory} (f g : X ⟶ Y)
  证明: F.essImage.ι.map_injective h

Depends on / 依赖: F.essImage, essImage, map_injective
-/
lemma essImage_ext (F : C ⥤ D) {X Y : F.EssImageSubcategory} (f g : X ⟶ Y)
    (h : F.essImage.ι.map f = F.essImage.ι.map g) : f = g :=
  F.essImage.ι.map_injective h

/--
Given a functor `F : C ⥤ D`, we have an (essentially surjective) functor from `C` to the essential
image of `F`.
-/
@[implicit_reducible, simps!]
/--
Definition of `toEssImage` / `toEssImage` 的定义

English:
definition toEssImage
  signature: (F : C ⥤ D)
  body: F.essImage.lift F (obj_mem_essImage _)

中文:
定义 toEssImage
  签名: (F : C ⥤ D)
  定义体: F.essImage.lift F (obj_mem_essImage _)

Depends on / 依赖: F.essImage.lift, essImage, obj_mem_essImage
-/
def toEssImage (F : C ⥤ D) : C ⥤ F.EssImageSubcategory :=
  F.essImage.lift F (obj_mem_essImage _)

/-- The functor `F` factorises through its essential image, where the first functor is essentially
surjective and the second is fully faithful.
-/
@[simps!]
/--
Definition of `toEssImageCompι` / `toEssImageCompι` 的定义

English:
definition toEssImageCompι
  signature: (F : C ⥤ D)
  body: ObjectProperty.liftCompιIso _ _ _

中文:
定义 toEssImageCompι
  签名: (F : C ⥤ D)
  定义体: ObjectProperty.liftCompιIso _ _ _

Depends on / 依赖: ObjectProperty, ObjectProperty.liftComp
-/
def toEssImageCompι (F : C ⥤ D) : F.toEssImage ⋙ F.essImage.ι ≅ F :=
  ObjectProperty.liftCompιIso _ _ _

/-- A functor `F : C ⥤ D` is essentially surjective if every object of `D` is in the essential
image of `F`. In other words, for every `Y : D`, there is some `X : C` with `F.obj X ≅ Y`. -/
@[stacks 001C]
/--
Definition of `EssSurj` / `EssSurj` 的定义

English:
class EssSurj
  parameters: (F : C ⥤ D)
  axioms and operations (1):
    - mem_essImage((F) (Y : D)) : F.essImage Y

中文:
类 EssSurj
  参数: (F : C ⥤ D)
  公理与运算 (1 个):
    - mem_essImage((F) (Y : D)) : F.essImage Y
-/
class EssSurj (F : C ⥤ D) : Prop where
  /-- All the objects of the target category are in the essential image. -/
  mem_essImage (F) (Y : D) : F.essImage Y

/--
Instance `EssSurj.toEssImage` / 实例 `EssSurj.toEssImage`

English:
instance EssSurj.toEssImage
  signature: : EssSurj F.toEssImage where
  body: fun ⟨_, hY⟩ => ⟨hY.witness, ⟨F.essImage.isoMk hY.getIso⟩⟩

中文:
实例 EssSurj.toEssImage
  签名: : EssSurj F.toEssImage where
  定义体: fun ⟨_, hY⟩ => ⟨hY.witness, ⟨F.essImage.isoMk hY.getIso⟩⟩

Depends on / 依赖: F.essImage.isoMk, essImage, getIso, hY.getIso, hY.witness, witness
-/
instance EssSurj.toEssImage : EssSurj F.toEssImage where
  mem_essImage := fun ⟨_, hY⟩ => ⟨hY.witness, ⟨F.essImage.isoMk hY.getIso⟩⟩

/--
theorem `essSurj_of_surj` / 定理 `essSurj_of_surj`

English:
theorem essSurj_of_surj
  given: (h : Function.Surjective F.obj)
  statement: EssSurj F where
  proof: by
    obtain ⟨X, rfl⟩ := h Y
    apply obj_mem_essImage

中文:
定理 essSurj_of_surj
  条件: (h : Function.Surjective F.obj)
  结论: EssSurj F where
  证明: by
    obtain ⟨X, rfl⟩ := h Y
    apply obj_mem_essImage

Depends on / 依赖: obj_mem_essImage
-/
theorem essSurj_of_surj (h : Function.Surjective F.obj) : EssSurj F where
  mem_essImage Y := by
    obtain ⟨X, rfl⟩ := h Y
    apply obj_mem_essImage

section EssSurj
variable (F)
variable [F.EssSurj]

/--
Definition of `objPreimage` / `objPreimage` 的定义

English:
definition objPreimage
  signature: (Y : D)
  body: essImage.witness (EssSurj.mem_essImage F Y)

中文:
定义 objPreimage
  签名: (Y : D)
  定义体: essImage.witness (EssSurj.mem_essImage F Y)

Depends on / 依赖: EssSurj, EssSurj.mem_essImage, essImage, essImage.witness, mem_essImage, witness
-/
def objPreimage (Y : D) : C :=
  essImage.witness (EssSurj.mem_essImage F Y)

/--
Definition of `objObjPreimageIso` / `objObjPreimageIso` 的定义

English:
definition objObjPreimageIso
  signature: (Y : D)
  body: Functor.essImage.getIso _

中文:
定义 objObjPreimageIso
  签名: (Y : D)
  定义体: Functor.essImage.getIso _

Depends on / 依赖: Functor, Functor.essImage.getIso, essImage, getIso
-/
def objObjPreimageIso (Y : D) : F.obj (F.objPreimage Y) ≅ Y :=
  Functor.essImage.getIso _

/--
Instance `Faithful.toEssImage` / 实例 `Faithful.toEssImage`

English:
instance Faithful.toEssImage
  signature: (F : C ⥤ D) [Faithful F]
  body: by
  dsimp only [Functor.toEssImage]
  infer_instance

中文:
实例 Faithful.toEssImage
  签名: (F : C ⥤ D) [Faithful F]
  定义体: by
  dsimp only [Functor.toEssImage]
  infer_instance

Depends on / 依赖: Functor, Functor.toEssImage, infer_instance, toEssImage
-/
instance Faithful.toEssImage (F : C ⥤ D) [Faithful F] : Faithful F.toEssImage := by
  dsimp only [Functor.toEssImage]
  infer_instance

/--
Instance `Full.toEssImage` / 实例 `Full.toEssImage`

English:
instance Full.toEssImage
  signature: (F : C ⥤ D) [Full F]
  body: by
  dsimp only [Functor.toEssImage]
  infer_instance

中文:
实例 Full.toEssImage
  签名: (F : C ⥤ D) [Full F]
  定义体: by
  dsimp only [Functor.toEssImage]
  infer_instance

Depends on / 依赖: Functor, Functor.toEssImage, infer_instance, toEssImage
-/
instance Full.toEssImage (F : C ⥤ D) [Full F] : Full F.toEssImage := by
  dsimp only [Functor.toEssImage]
  infer_instance

/--
Instance `instEssSurjId` / 实例 `instEssSurjId`

English:
instance instEssSurjId
  signature: : EssSurj (𝟭 C) where
  body: ⟨Y, ⟨Iso.refl _⟩⟩

中文:
实例 instEssSurjId
  签名: : EssSurj (𝟭 C) where
  定义体: ⟨Y, ⟨Iso.refl _⟩⟩

Depends on / 依赖: Iso.refl
-/
instance instEssSurjId : EssSurj (𝟭 C) where
  mem_essImage Y := ⟨Y, ⟨Iso.refl _⟩⟩

/--
lemma `essSurj_of_iso` / 引理 `essSurj_of_iso`

English:
lemma essSurj_of_iso
  given: {F G : C ⥤ D} [EssSurj F] (α : F ≅ G)
  statement: EssSurj G where
  proof: Functor.essImage.ofNatIso α (EssSurj.mem_essImage F Y)

中文:
引理 essSurj_of_iso
  条件: {F G : C ⥤ D} [EssSurj F] (α : F ≅ G)
  结论: EssSurj G where
  证明: Functor.essImage.ofNatIso α (EssSurj.mem_essImage F Y)

Depends on / 依赖: EssSurj, EssSurj.mem_essImage, Functor, Functor.essImage.ofNatIso, essImage, mem_essImage, ofNatIso
-/
lemma essSurj_of_iso {F G : C ⥤ D} [EssSurj F] (α : F ≅ G) : EssSurj G where
  mem_essImage Y := Functor.essImage.ofNatIso α (EssSurj.mem_essImage F Y)

/--
Instance `essSurj_comp` / 实例 `essSurj_comp`

English:
instance essSurj_comp
  signature: (F : C ⥤ D) (G : D ⥤ E) [F.EssSurj] [G.EssSurj]
  body: ⟨_, ⟨G.mapIso (F.objObjPreimageIso _) ≪≫ G.objObjPreimageIso Z⟩⟩

中文:
实例 essSurj_comp
  签名: (F : C ⥤ D) (G : D ⥤ E) [F.EssSurj] [G.EssSurj]
  定义体: ⟨_, ⟨G.mapIso (F.objObjPreimageIso _) ≪≫ G.objObjPreimageIso Z⟩⟩

Depends on / 依赖: F.objObjPreimageIso, G.mapIso, G.objObjPreimageIso, mapIso, objObjPreimageIso
-/
instance essSurj_comp (F : C ⥤ D) (G : D ⥤ E) [F.EssSurj] [G.EssSurj] :
    (F ⋙ G).EssSurj where
  mem_essImage Z := ⟨_, ⟨G.mapIso (F.objObjPreimageIso _) ≪≫ G.objObjPreimageIso Z⟩⟩

/--
lemma `essSurj_of_comp_fully_faithful` / 引理 `essSurj_of_comp_fully_faithful`

English:
lemma essSurj_of_comp_fully_faithful
  statement: (F : C ⥤ D) (G : D ⥤ E) [(F ⋙ G).EssSurj]
  proof: ⟨_, ⟨G.preimageIso ((F ⋙ G).objObjPreimageIso (G.obj X))⟩⟩

中文:
引理 essSurj_of_comp_fully_faithful
  结论: (F : C ⥤ D) (G : D ⥤ E) [(F ⋙ G).EssSurj]
  证明: ⟨_, ⟨G.preimageIso ((F ⋙ G).objObjPreimageIso (G.obj X))⟩⟩

Depends on / 依赖: G.obj, G.preimageIso, objObjPreimageIso, preimageIso
-/
lemma essSurj_of_comp_fully_faithful (F : C ⥤ D) (G : D ⥤ E) [(F ⋙ G).EssSurj]
    [G.Faithful] [G.Full] : F.EssSurj where
  mem_essImage X := ⟨_, ⟨G.preimageIso ((F ⋙ G).objObjPreimageIso (G.obj X))⟩⟩

variable {F} {X : E}

/--
lemma `essImage_comp_apply_of_essSurj` / 引理 `essImage_comp_apply_of_essSurj`

English:
lemma essImage_comp_apply_of_essSurj
  statement: (F ⋙ G).essImage X ↔ G.essImage X where
  proof: fun ⟨Y, ⟨e⟩⟩ => ⟨F.obj Y, ⟨e⟩⟩
  mpr := fun ⟨Y, ⟨e⟩⟩ =>
    let ⟨Z, ⟨e'⟩⟩ := Functor.EssSurj.mem_essImage F Y; ⟨Z, ⟨(G.mapIso e').trans e⟩⟩

中文:
引理 essImage_comp_apply_of_essSurj
  结论: (F ⋙ G).essImage X ↔ G.essImage X where
  证明: fun ⟨Y, ⟨e⟩⟩ => ⟨F.obj Y, ⟨e⟩⟩
  mpr := fun ⟨Y, ⟨e⟩⟩ =>
    let ⟨Z, ⟨e'⟩⟩ := Functor.EssSurj.mem_essImage F Y; ⟨Z, ⟨(G.mapIso e').trans e⟩⟩

Depends on / 依赖: F.obj
-/
lemma essImage_comp_apply_of_essSurj : (F ⋙ G).essImage X ↔ G.essImage X where
  mp := fun ⟨Y, ⟨e⟩⟩ => ⟨F.obj Y, ⟨e⟩⟩
  mpr := fun ⟨Y, ⟨e⟩⟩ =>
    let ⟨Z, ⟨e'⟩⟩ := Functor.EssSurj.mem_essImage F Y; ⟨Z, ⟨(G.mapIso e').trans e⟩⟩

/--
lemma `essImage_comp_of_essSurj` / 引理 `essImage_comp_of_essSurj`

English:
lemma essImage_comp_of_essSurj
  statement: (F ⋙ G).essImage = G.essImage
  proof: funext fun _X => propext essImage_comp_apply_of_essSurj

中文:
引理 essImage_comp_of_essSurj
  结论: (F ⋙ G).essImage = G.essImage
  证明: funext fun _X => propext essImage_comp_apply_of_essSurj
-/
@[simp] lemma essImage_comp_of_essSurj : (F ⋙ G).essImage = G.essImage :=
  funext fun _X => propext essImage_comp_apply_of_essSurj

end EssSurj

section

variable {J C D : Type*} [Category* J] [Category* C] [Category* D]
  (G : J ⥤ D) (F : C ⥤ D) [F.Full] [F.Faithful] (hG : forall j, F.essImage (G.obj j))

/-- Lift a functor `G : J ⥤ D` to the essential image of a fully faithful functor `F : C ⥤ D` to a
functor `G' : J ⥤ C` such that `G' ⋙ F ≅ G`. See `essImage.liftFunctorCompIso`. -/
@[implicit_reducible, simps]
/--
Definition of `essImage.liftFunctor` / `essImage.liftFunctor` 的定义

English:
definition essImage.liftFunctor
  signature: : J ⥤ C where
  body: F.toEssImage.objPreimage ⟨G.obj j, hG j⟩
  map {i j} f :=
F.preimage
    (F.toEssImage.objObjPreimageIso ⟨G.obj i, hG i⟩).hom.hom ≫ G.map f ≫
      (F.toEssImage.objObjPreimageIso ⟨G.obj j, hG j⟩).inv.hom
  map_id _ := F.map_injective (by simp)
  map_comp _ _ := F.map_injective (by simp)

中文:
定义 essImage.liftFunctor
  签名: : J ⥤ C where
  定义体: F.toEssImage.objPreimage ⟨G.obj j, hG j⟩
  map {i j} f :=
F.preimage
    (F.toEssImage.objObjPreimageIso ⟨G.obj i, hG i⟩).hom.hom ≫ G.map f ≫
      (F.toEssImage.objObjPreimageIso ⟨G.obj j, hG j⟩).inv.hom
  map_id _ := F.map_injective (by simp)
  map_comp _ _ := F.map_injective (by simp)

Depends on / 依赖: F.toEssImage.objPreimage, G.obj, objPreimage, toEssImage
-/
def essImage.liftFunctor : J ⥤ C where
  obj j := F.toEssImage.objPreimage ⟨G.obj j, hG j⟩
  map {i j} f :=
F.preimage
    (F.toEssImage.objObjPreimageIso ⟨G.obj i, hG i⟩).hom.hom ≫ G.map f ≫
      (F.toEssImage.objObjPreimageIso ⟨G.obj j, hG j⟩).inv.hom
  map_id _ := F.map_injective (by simp)
  map_comp _ _ := F.map_injective (by simp)

/--
Definition of `essImage.liftFunctorCompIso` / `essImage.liftFunctorCompIso` 的定义

English:
definition essImage.liftFunctorCompIso
  signature: : essImage.liftFunctor G F hG ⋙ F ≅ G
  body: NatIso.ofComponents
    (fun i => F.essImage.ι.mapIso (F.toEssImage.objObjPreimageIso ⟨G.obj i, hG _⟩))

中文:
定义 essImage.liftFunctorCompIso
  签名: : essImage.liftFunctor G F hG ⋙ F ≅ G
  定义体: NatIso.ofComponents
    (fun i => F.essImage.ι.mapIso (F.toEssImage.objObjPreimageIso ⟨G.obj i, hG _⟩))
-/
@[simps!] def essImage.liftFunctorCompIso : essImage.liftFunctor G F hG ⋙ F ≅ G :=
  NatIso.ofComponents
    (fun i => F.essImage.ι.mapIso (F.toEssImage.objObjPreimageIso ⟨G.obj i, hG _⟩))

end

/--
lemma `essImage_ι_comp` / 引理 `essImage_ι_comp`

English:
lemma essImage_ι_comp
  given: (F : C ⥤ D) (P : ObjectProperty C)
  proof: by
  ext Y
  constructor
  · rintro ⟨X, ⟨e⟩⟩
    exact ⟨X.1, X.2, ⟨e⟩⟩
  · rintro ⟨X, hX, ⟨e⟩⟩
    exact ⟨⟨X, hX⟩, ⟨e⟩⟩

中文:
引理 essImage_ι_comp
  条件: (F : C ⥤ D) (P : Object命题erty C)
  证明: by
  ext Y
  constructor
  · rintro ⟨X, ⟨e⟩⟩
    exact ⟨X.1, X.2, ⟨e⟩⟩
  · rintro ⟨X, hX, ⟨e⟩⟩
    exact ⟨⟨X, hX⟩, ⟨e⟩⟩
-/
lemma essImage_ι_comp (F : C ⥤ D) (P : ObjectProperty C) :
    (P.ι ⋙ F).essImage = P.map F := by
  ext Y
  constructor
  · rintro ⟨X, ⟨e⟩⟩
    exact ⟨X.1, X.2, ⟨e⟩⟩
  · rintro ⟨X, hX, ⟨e⟩⟩
    exact ⟨⟨X, hX⟩, ⟨e⟩⟩

/--
lemma `full_of_comp_essSurj` / 引理 `full_of_comp_essSurj`

English:
lemma full_of_comp_essSurj
  statement: (F : D ⥤ E) (L : C ⥤ D) [EssSurj L]
  proof: ⟨by
  intro X₁ X₂ ψ
  obtain ⟨f, hf⟩ := h (F.map (L.objObjPreimageIso X₁).hom ≫ ψ ≫
    F.map (L.objObjPreimageIso X₂).inv)
  exact ⟨(L.objObjPreimageIso X₁).inv ≫ f ≫ (L.objObjPreimageIso X₂).hom, by simp [hf]⟩⟩

中文:
引理 full_of_comp_essSurj
  结论: (F : D ⥤ E) (L : C ⥤ D) [EssSurj L]
  证明: ⟨by
  intro X₁ X₂ ψ
  obtain ⟨f, hf⟩ := h (F.map (L.objObjPreimageIso X₁).hom ≫ ψ ≫
    F.map (L.objObjPreimageIso X₂).inv)
  exact ⟨(L.objObjPreimageIso X₁).inv ≫ f ≫ (L.objObjPreimageIso X₂).hom, by simp [hf]⟩⟩

Depends on / 依赖: F.map, L.objObjPreimageIso, objObjPreimageIso
-/
lemma full_of_comp_essSurj (F : D ⥤ E) (L : C ⥤ D) [EssSurj L]
    (h : forall ⦃X₁ X₂ : C⦄ (φ : F.obj (L.obj X₁) ⟶ F.obj (L.obj X₂)),
      exists (f : L.obj X₁ ⟶ L.obj X₂), F.map f = φ) :
    F.Full := ⟨by
  intro X₁ X₂ ψ
  obtain ⟨f, hf⟩ := h (F.map (L.objObjPreimageIso X₁).hom ≫ ψ ≫
    F.map (L.objObjPreimageIso X₂).inv)
  exact ⟨(L.objObjPreimageIso X₁).inv ≫ f ≫ (L.objObjPreimageIso X₂).hom, by simp [hf]⟩⟩

/--
lemma `faithful_of_comp_essSurj` / 引理 `faithful_of_comp_essSurj`

English:
lemma faithful_of_comp_essSurj
  statement: (F : D ⥤ E) (L : C ⥤ D) [EssSurj L]
  proof: by
    rw [← cancel_mono (L.objObjPreimageIso _).inv]; rw [← cancel_epi (L.objObjPreimageIso _).hom]
    exact h _ _ (by simp [hfg])

中文:
引理 faithful_of_comp_essSurj
  结论: (F : D ⥤ E) (L : C ⥤ D) [EssSurj L]
  证明: by
    rw [← cancel_mono (L.objObjPreimageIso _).inv]; rw [← cancel_epi (L.objObjPreimageIso _).hom]
    exact h _ _ (by simp [hfg])

Depends on / 依赖: L.objObjPreimageIso, cancel_epi, cancel_mono, objObjPreimageIso
-/
lemma faithful_of_comp_essSurj (F : D ⥤ E) (L : C ⥤ D) [EssSurj L]
    (h : forall ⦃X₁ X₂ : C⦄ (f g : L.obj X₁ ⟶ L.obj X₂), F.map f = F.map g -> f = g) :
    F.Faithful where
  map_injective hfg := by
    rw [← cancel_mono (L.objObjPreimageIso _).inv]; rw [← cancel_epi (L.objObjPreimageIso _).hom]
    exact h _ _ (by simp [hfg])

end Functor

/--
lemma `ObjectProperty.map_top` / 引理 `ObjectProperty.map_top`

English:
lemma ObjectProperty.map_top
  given: (F : C ⥤ D)
  proof: by
  ext Y
  refine ⟨?_, ?_⟩
  · rintro ⟨X, _, ⟨e⟩⟩
    exact ⟨X, ⟨e⟩⟩
  · rintro ⟨X, ⟨e⟩⟩
    exact ⟨X, by simp, ⟨e⟩⟩

中文:
引理 ObjectProperty.map_top
  条件: (F : C ⥤ D)
  证明: by
  ext Y
  refine ⟨?_, ?_⟩
  · rintro ⟨X, _, ⟨e⟩⟩
    exact ⟨X, ⟨e⟩⟩
  · rintro ⟨X, ⟨e⟩⟩
    exact ⟨X, by simp, ⟨e⟩⟩
-/
lemma ObjectProperty.map_top (F : C ⥤ D) :
    (⊤ : ObjectProperty C).map F = F.essImage := by
  ext Y
  refine ⟨?_, ?_⟩
  · rintro ⟨X, _, ⟨e⟩⟩
    exact ⟨X, ⟨e⟩⟩
  · rintro ⟨X, ⟨e⟩⟩
    exact ⟨X, by simp, ⟨e⟩⟩

end CategoryTheory
