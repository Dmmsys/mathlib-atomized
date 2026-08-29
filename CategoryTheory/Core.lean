/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Groupoid
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Control.EquivFunctor

/-!
# The core of a category

The core of a category `C` is the (non-full) subcategory of `C` consisting of all objects,
and all isomorphisms. We construct it as a `CategoryTheory.Groupoid`.

`CategoryTheory.Core.inclusion : Core C ⥤ C` gives the faithful inclusion into the original
category.

Any functor `F` from a groupoid `G` into `C` factors through `CategoryTheory.Core C`,
but this is not functorial with respect to `F`.
-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

namespace CategoryTheory

open CategoryTheory.Functor

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

-- morphism levels before object levels. See note [category theory universes].
/--
Definition of `Core` / `Core` 的定义

English:
structure Core
  parameters: (C : Type u₁)
  axioms and operations (1):
    - of : C

中文:
结构 核
  参数: (C : 类型u₁)
  公理与运算 (1 个):
    - of : C
-/
structure Core (C : Type u₁) where
  /-- The object of the base category underlying an object in `Core C`. -/
  of : C

variable {C : Type u₁} [Category.{v₁} C]

/-- The hom-type between two objects of `Core C`.
It is defined as a one-field structure to prevent defeq abuses. -/
@[ext]
/--
Definition of `CoreHom` / `CoreHom` 的定义

English:
structure CoreHom
  parameters: (X Y : Core C)
  axioms and operations (1):
    - iso : X.of ≅ Y.of

中文:
结构 核态射
  参数: (X Y : 核 C)
  公理与运算 (1 个):
    - iso : X.of ≅ Y.of
-/
structure CoreHom (X Y : Core C) where
  /-- The isomorphism of objects of `C` underlying a morphism in `Core C`. -/
  iso : X.of ≅ Y.of

@[simps! id_iso inv_iso]
/--
Instance `coreCategory` / 实例 `coreCategory`

English:
instance coreCategory
  signature: : Groupoid.{v₁} (Core C) where
  body: CoreHom X Y
id (X : Core C) := .mk Iso.refl X.of
comp f g := .mk Iso.trans f.iso g.iso
inv {_ _} f := .mk Iso.symm f.iso

@[simp]

中文:
实例 coreCategory
  签名: : 群胚.{v₁} (核 C) where
  定义体: CoreHom X Y
id (X : Core C) := .mk Iso.refl X.of
comp f g := .mk Iso.trans f.iso g.iso
inv {_ _} f := .mk Iso.symm f.iso

@[simp]

Depends on / 依赖: CoreHom
-/
instance coreCategory : Groupoid.{v₁} (Core C) where
  Hom (X Y : Core C) := CoreHom X Y
id (X : Core C) := .mk Iso.refl X.of
comp f g := .mk Iso.trans f.iso g.iso
inv {_ _} f := .mk Iso.symm f.iso

@[simp]
/--
lemma `coreCategory_comp_iso` / 引理 `coreCategory_comp_iso`

English:
lemma coreCategory_comp_iso
  given: {x y z : Core C} (f : x ⟶ y) (g : y ⟶ z)
  proof: rfl

中文:
引理 coreCategory_comp_iso
  条件: {x y z : 核 C} (f : x ⟶ y) (g : y ⟶ z)
  证明: rfl
-/
lemma coreCategory_comp_iso {x y z : Core C} (f : x ⟶ y) (g : y ⟶ z) :
    (f ≫ g).iso = f.iso ≪≫ g.iso := rfl

namespace Core

variable (C) in
/-- The core of a category is naturally included in the category. -/
@[simps!]
/--
Definition of `inclusion` / `inclusion` 的定义

English:
definition inclusion
  signature: : Core C ⥤ C where
  body: of
  map f := f.iso.hom

@[ext]

中文:
定义 inclusion
  签名: : 核 C ⥤ C where
  定义体: of
  map f := f.iso.hom

@[ext]
-/
def inclusion : Core C ⥤ C where
  obj := of
  map f := f.iso.hom

@[ext]
/--
theorem `hom_ext` / 定理 `hom_ext`

English:
theorem hom_ext
  given: {X Y : Core C} {f g : X ⟶ Y} (h : f.iso.hom = g.iso.hom)
  proof: by
  apply CoreHom.ext
  exact Iso.ext h

中文:
定理 hom_ext
  条件: {X Y : 核 C} {f g : X ⟶ Y} (h : f.iso.hom = g.iso.hom)
  证明: by
  apply CoreHom.ext
  exact Iso.ext h

Depends on / 依赖: CoreHom, CoreHom.ext, Iso.ext
-/
theorem hom_ext {X Y : Core C} {f g : X ⟶ Y} (h : f.iso.hom = g.iso.hom) :
    f = g := by
  apply CoreHom.ext
  exact Iso.ext h

/-- Construct an isomorphism in `Core C` from an isomorphism in `C`. -/
@[simps! hom_iso inv_iso]
/--
Definition of `isoMk` / `isoMk` 的定义

English:
definition isoMk
  signature: {x y : Core C} (e : x.of ≅ y.of)
  body: .symm (.mk e) Groupoid.isoEquivHom _ _

中文:
定义 isoMk
  签名: {x y : 核 C} (e : x.of ≅ y.of)
  定义体: .symm (.mk e) Groupoid.isoEquivHom _ _

Depends on / 依赖: Groupoid, Groupoid.isoEquivHom, isoEquivHom
-/
def isoMk {x y : Core C} (e : x.of ≅ y.of) : x ≅ y :=
.symm (.mk e) Groupoid.isoEquivHom _ _

variable (C)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (inclusion C).Faithful

中文:
实例 :
  签名: (inclusion C).忠实
-/
instance : (inclusion C).Faithful where

variable {C} {G : Type u₂} [Groupoid.{v₂} G]

-- Note that this function is not functorial
-- (consider the two functors from [0] to [1], and the natural transformation between them).
/-- A functor from a groupoid to a category C factors through the core of C. -/
@[simps!]
/--
Definition of `functorToCore` / `functorToCore` 的定义

English:
definition functorToCore
  signature: (F : G ⥤ C)
  body: .mk F.obj X
map f := .mk { hom := F.map f, inv := F.map (Groupoid.inv f) }

中文:
定义 functorToCore
  签名: (F : G ⥤ C)
  定义体: .mk F.obj X
map f := .mk { hom := F.map f, inv := F.map (Groupoid.inv f) }

Depends on / 依赖: F.obj
-/
def functorToCore (F : G ⥤ C) : G ⥤ Core C where
obj X := .mk F.obj X
map f := .mk { hom := F.map f, inv := F.map (Groupoid.inv f) }

/-- We can functorially associate to any functor from a groupoid to the core of a category `C`,
a functor from the groupoid to `C`, simply by composing with the embedding `Core C ⥤ C`.
-/
@[simps!]
/--
Definition of `forgetFunctorToCore` / `forgetFunctorToCore` 的定义

English:
definition forgetFunctorToCore
  signature: : (G ⥤ Core C) ⥤ G ⥤ C
  body: (whiskeringRight _ _ _).obj (inclusion C)

中文:
定义 forgetFunctorToCore
  签名: : (G ⥤ 核 C) ⥤ G ⥤ C
  定义体: (whiskeringRight _ _ _).obj (inclusion C)

Depends on / 依赖: inclusion, whiskeringRight
-/
def forgetFunctorToCore : (G ⥤ Core C) ⥤ G ⥤ C :=
  (whiskeringRight _ _ _).obj (inclusion C)

end Core

section

namespace Functor

variable {D : Type u₂} [Category.{v₂} D]

/-- A functor `C ⥤ D` induces a functor `Core C ⥤ Core D`. -/
@[simps!]
/--
Definition of `core` / `core` 的定义

English:
definition core
  signature: (F : C ⥤ D)
  body: Core.functorToCore (Core.inclusion _ ⋙ F)

中文:
定义 core
  签名: (F : C ⥤ D)
  定义体: Core.functorToCore (Core.inclusion _ ⋙ F)

Depends on / 依赖: Core.functorToCore, Core.inclusion, functorToCore, inclusion
-/
def core (F : C ⥤ D) : Core C ⥤ Core D := Core.functorToCore (Core.inclusion _ ⋙ F)

variable (C) in
/-- The core of the identity functor is the identity functor on the cores. -/
@[simps!]
/--
Definition of `coreId` / `coreId` 的定义

English:
definition coreId
  signature: : (𝟭 C).core ≅ 𝟭 (Core C)
  body: Iso.refl _

中文:
定义 coreId
  签名: : (𝟭 C).core ≅ 𝟭 (核 C)
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def coreId : (𝟭 C).core ≅ 𝟭 (Core C) := Iso.refl _

/-- The core of the composition of F and G is the composition of the cores. -/
@[simps!]
/--
Definition of `coreComp` / `coreComp` 的定义

English:
definition coreComp
  signature: {E : Type u₃} [Category.{v₃} E] (F : C ⥤ D) (G : D ⥤ E)
  body: Iso.refl _

中文:
定义 coreComp
  签名: {E : 类型u₃} [范畴.{v₃} E] (F : C ⥤ D) (G : D ⥤ E)
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def coreComp {E : Type u₃} [Category.{v₃} E] (F : C ⥤ D) (G : D ⥤ E) :
    (F ⋙ G).core ≅ F.core ⋙ G.core := Iso.refl _

/-- The natural isomorphism
```
                  F.core
            Core C ⥤ Core D
 inclusion C ‖ ‖ inclusion D
              V V
              C ⥤ D
                    F
```
thought of as pseudonaturality of `inclusion`,
when viewing `Core` as a pseudofunctor.
-/
@[simps!]
/--
Definition of `coreCompInclusionIso` / `coreCompInclusionIso` 的定义

English:
definition coreCompInclusionIso
  signature: (F : C ⥤ D)
  body: Iso.refl _

中文:
定义 coreCompInclusionIso
  签名: (F : C ⥤ D)
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def coreCompInclusionIso (F : C ⥤ D) :
    F.core ⋙ Core.inclusion D ≅ Core.inclusion C ⋙ F :=
  Iso.refl _

/--
lemma `core_comp_inclusion` / 引理 `core_comp_inclusion`

English:
lemma core_comp_inclusion
  given: (F : C ⥤ D)
  proof: Functor.ext_of_iso (coreCompInclusionIso F) (by cat_disch)

中文:
引理 core_comp_inclusion
  条件: (F : C ⥤ D)
  证明: Functor.ext_of_iso (coreCompInclusionIso F) (by cat_disch)

Depends on / 依赖: Functor, Functor.ext_of_iso, cat_disch, coreCompInclusionIso, ext_of_iso
-/
lemma core_comp_inclusion (F : C ⥤ D) :
    F.core ⋙ Core.inclusion D = Core.inclusion C ⋙ F :=
  Functor.ext_of_iso (coreCompInclusionIso F) (by cat_disch)

end Functor

namespace Iso

variable {D : Type u₂} [Category.{v₂} D]

set_option backward.isDefEq.respectTransparency.types false in
/-- A natural isomorphism of functors induces a natural isomorphism between their cores. -/
@[simps!]
/--
Definition of `core` / `core` 的定义

English:
definition core
  signature: {F G : C ⥤ D} (α : F ≅ G)
  body: NatIso.ofComponents
    (fun x => Groupoid.isoEquivHom _ _ |>.symm <| .mk <| α.app x.of)

中文:
定义 core
  签名: {F G : C ⥤ D} (α : F ≅ G)
  定义体: NatIso.ofComponents
    (fun x => Groupoid.isoEquivHom _ _ |>.symm <| .mk <| α.app x.of)

Depends on / 依赖: Groupoid, Groupoid.isoEquivHom, NatIso, NatIso.ofComponents, isoEquivHom, ofComponents, x.of
-/
def core {F G : C ⥤ D} (α : F ≅ G) : F.core ≅ G.core :=
  NatIso.ofComponents
    (fun x => Groupoid.isoEquivHom _ _ |>.symm <| .mk <| α.app x.of)

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `coreComp` / 引理 `coreComp`

English:
lemma coreComp
  given: {F G H : C ⥤ D} (α : F ≅ G) (β : G ≅ H)
  statement: (α ≪≫ β).core = α.core ≪≫ β.core
  proof: rfl

中文:
引理 coreComp
  条件: {F G H : C ⥤ D} (α : F ≅ G) (β : G ≅ H)
  结论: (α ≪≫ β).core = α.core ≪≫ β.core
  证明: rfl
-/
lemma coreComp {F G H : C ⥤ D} (α : F ≅ G) (β : G ≅ H) : (α ≪≫ β).core = α.core ≪≫ β.core := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `coreId` / 引理 `coreId`

English:
lemma coreId
  given: {F : C ⥤ D}
  statement: (Iso.refl F).core = Iso.refl F.core
  proof: rfl

中文:
引理 coreId
  条件: {F : C ⥤ D}
  结论: (同构.refl F).core = 同构.refl F.core
  证明: rfl
-/
lemma coreId {F : C ⥤ D} : (Iso.refl F).core = Iso.refl F.core := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `coreWhiskerLeft` / 引理 `coreWhiskerLeft`

English:
lemma coreWhiskerLeft
  given: {E : Type u₃} [Category.{v₃} E] (F : C ⥤ D) {G H : D ⥤ E} (η : G ≅ H)
  proof: by
  cat_disch

中文:
引理 coreWhiskerLeft
  条件: {E : 类型u₃} [范畴.{v₃} E] (F : C ⥤ D) {G H : D ⥤ E} (η : G ≅ H)
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma coreWhiskerLeft {E : Type u₃} [Category.{v₃} E] (F : C ⥤ D) {G H : D ⥤ E} (η : G ≅ H) :
    (isoWhiskerLeft F η).core =
    F.coreComp G ≪≫ isoWhiskerLeft F.core η.core ≪≫ (F.coreComp H).symm := by
  cat_disch

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `coreWhiskerRight` / 引理 `coreWhiskerRight`

English:
lemma coreWhiskerRight
  given: {E : Type u₃} [Category.{v₃} E] {F G : C ⥤ D} (η : F ≅ G) (H : D ⥤ E)
  proof: by
  cat_disch

中文:
引理 coreWhiskerRight
  条件: {E : 类型u₃} [范畴.{v₃} E] {F G : C ⥤ D} (η : F ≅ G) (H : D ⥤ E)
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma coreWhiskerRight {E : Type u₃} [Category.{v₃} E] {F G : C ⥤ D} (η : F ≅ G) (H : D ⥤ E) :
    (isoWhiskerRight η H).core =
    F.coreComp H ≪≫ isoWhiskerRight η.core H.core ≪≫ (G.coreComp H).symm := by
  cat_disch

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `coreLeftUnitor` / 引理 `coreLeftUnitor`

English:
lemma coreLeftUnitor
  given: {F : C ⥤ D}
  proof: by
  cat_disch

中文:
引理 coreLeftUnitor
  条件: {F : C ⥤ D}
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma coreLeftUnitor {F : C ⥤ D} :
    F.leftUnitor.core =
    (𝟭 C).coreComp F ≪≫ isoWhiskerRight (Functor.coreId C) _ ≪≫ F.core.leftUnitor := by
  cat_disch

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `coreRightUnitor` / 引理 `coreRightUnitor`

English:
lemma coreRightUnitor
  given: {F : C ⥤ D}
  proof: by
  cat_disch

中文:
引理 coreRightUnitor
  条件: {F : C ⥤ D}
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma coreRightUnitor {F : C ⥤ D} :
    F.rightUnitor.core =
    (F).coreComp (𝟭 D) ≪≫ isoWhiskerLeft _ (Functor.coreId D) ≪≫ F.core.rightUnitor := by
  cat_disch

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `coreAssociator` / 引理 `coreAssociator`

English:
lemma coreAssociator
  statement: {E : Type u₃} [Category.{v₃} E] {E' : Type u₄} [Category.{v₄} E']
  proof: by
  cat_disch

中文:
引理 coreAssociator
  结论: {E : 类型u₃} [范畴.{v₃} E] {E' : 类型u₄} [范畴.{v₄} E']
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma coreAssociator {E : Type u₃} [Category.{v₃} E] {E' : Type u₄} [Category.{v₄} E']
    (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ E') :
    (Functor.associator F G H).core =
    (F ⋙ G).coreComp H ≪≫ isoWhiskerRight (F.coreComp G) H.core ≪≫
      Functor.associator F.core G.core H.core ≪≫ (isoWhiskerLeft F.core (G.coreComp H)).symm ≪≫
      (F.coreComp (G ⋙ H)).symm := by
  cat_disch

end Iso

namespace Core

variable {G : Type u₂} [Groupoid.{v₂} G]

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `functorToCoreCompLeftIso` / `functorToCoreCompLeftIso` 的定义

English:
definition functorToCoreCompLeftIso
  signature: {G' : Type u₃} [Groupoid.{v₃} G'] (H : G ⥤ C) (F : G' ⥤ G)
  body: NatIso.ofComponents (fun _ => Iso.refl _)

中文:
定义 functorToCoreCompLeftIso
  签名: {G' : 类型u₃} [群胚.{v₃} G'] (H : G ⥤ C) (F : G' ⥤ G)
  定义体: NatIso.ofComponents (fun _ => Iso.refl _)

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def functorToCoreCompLeftIso {G' : Type u₃} [Groupoid.{v₃} G'] (H : G ⥤ C) (F : G' ⥤ G) :
    functorToCore (F ⋙ H) ≅ F ⋙ functorToCore H :=
  NatIso.ofComponents (fun _ => Iso.refl _)

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `functorToCore_comp_left` / 引理 `functorToCore_comp_left`

English:
lemma functorToCore_comp_left
  given: {G' : Type u₃} [Groupoid.{v₃} G'] (H : G ⥤ C) (F : G' ⥤ G)
  proof: Functor.ext_of_iso (functorToCoreCompLeftIso H F) (by cat_disch)

中文:
引理 functorToCore_comp_left
  条件: {G' : 类型u₃} [群胚.{v₃} G'] (H : G ⥤ C) (F : G' ⥤ G)
  证明: Functor.ext_of_iso (functorToCoreCompLeftIso H F) (by cat_disch)

Depends on / 依赖: Functor, Functor.ext_of_iso, cat_disch, ext_of_iso, functorToCoreCompLeftIso
-/
lemma functorToCore_comp_left {G' : Type u₃} [Groupoid.{v₃} G'] (H : G ⥤ C) (F : G' ⥤ G) :
    functorToCore (F ⋙ H) = F ⋙ functorToCore H :=
  Functor.ext_of_iso (functorToCoreCompLeftIso H F) (by cat_disch)

/--
Definition of `functorToCoreCompRightIso` / `functorToCoreCompRightIso` 的定义

English:
definition functorToCoreCompRightIso
  signature: {C' : Type u₄} [Category.{v₄} C'] (H : G ⥤ C) (F : C ⥤ C')
  body: Iso.refl _

中文:
定义 functorToCoreCompRightIso
  签名: {C' : 类型u₄} [范畴.{v₄} C'] (H : G ⥤ C) (F : C ⥤ C')
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def functorToCoreCompRightIso {C' : Type u₄} [Category.{v₄} C'] (H : G ⥤ C) (F : C ⥤ C') :
    functorToCore (H ⋙ F) ≅ functorToCore H ⋙ F.core :=
  Iso.refl _

/--
lemma `functorToCore_comp_right` / 引理 `functorToCore_comp_right`

English:
lemma functorToCore_comp_right
  given: {C' : Type u₄} [Category.{v₄} C'] (H : G ⥤ C) (F : C ⥤ C')
  proof: Functor.ext_of_iso (functorToCoreCompRightIso H F) (by cat_disch)

中文:
引理 functorToCore_comp_right
  条件: {C' : 类型u₄} [范畴.{v₄} C'] (H : G ⥤ C) (F : C ⥤ C')
  证明: Functor.ext_of_iso (functorToCoreCompRightIso H F) (by cat_disch)

Depends on / 依赖: Functor, Functor.ext_of_iso, cat_disch, ext_of_iso, functorToCoreCompRightIso
-/
lemma functorToCore_comp_right {C' : Type u₄} [Category.{v₄} C'] (H : G ⥤ C) (F : C ⥤ C') :
    functorToCore (H ⋙ F) = functorToCore H ⋙ F.core :=
  Functor.ext_of_iso (functorToCoreCompRightIso H F) (by cat_disch)

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `inclusionCompFunctorToCoreIso` / `inclusionCompFunctorToCoreIso` 的定义

English:
definition inclusionCompFunctorToCoreIso
  signature: : inclusion G ⋙ functorToCore (𝟭 G) ≅ 𝟭 (Core G)
  body: NatIso.ofComponents (fun _ => Iso.refl _)

中文:
定义 inclusionCompFunctorToCoreIso
  签名: : inclusion G ⋙ functorToCore (𝟭 G) ≅ 𝟭 (核 G)
  定义体: NatIso.ofComponents (fun _ => Iso.refl _)

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def inclusionCompFunctorToCoreIso : inclusion G ⋙ functorToCore (𝟭 G) ≅ 𝟭 (Core G) :=
  NatIso.ofComponents (fun _ => Iso.refl _)

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `inclusion_comp_functorToCore` / 定理 `inclusion_comp_functorToCore`

English:
theorem inclusion_comp_functorToCore
  statement: inclusion G ⋙ functorToCore (𝟭 G) = 𝟭 (Core G)
  proof: Functor.ext_of_iso inclusionCompFunctorToCoreIso (by cat_disch)

中文:
定理 inclusion_comp_functorToCore
  结论: inclusion G ⋙ functorToCore (𝟭 G) = 𝟭 (核 G)
  证明: Functor.ext_of_iso inclusionCompFunctorToCoreIso (by cat_disch)

Depends on / 依赖: Functor, Functor.ext_of_iso, cat_disch, ext_of_iso, inclusionCompFunctorToCoreIso
-/
theorem inclusion_comp_functorToCore : inclusion G ⋙ functorToCore (𝟭 G) = 𝟭 (Core G) :=
  Functor.ext_of_iso inclusionCompFunctorToCoreIso (by cat_disch)

/--
Definition of `functorToCoreInclusionIso` / `functorToCoreInclusionIso` 的定义

English:
definition functorToCoreInclusionIso
  signature: : functorToCore (inclusion C) ≅ 𝟭 (Core C)
  body: Iso.refl _

中文:
定义 functorToCoreInclusionIso
  签名: : functorToCore (inclusion C) ≅ 𝟭 (核 C)
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def functorToCoreInclusionIso : functorToCore (inclusion C) ≅ 𝟭 (Core C) :=
  Iso.refl _

/--
theorem `functorToCore_inclusion` / 定理 `functorToCore_inclusion`

English:
theorem functorToCore_inclusion
  statement: functorToCore (inclusion C) = 𝟭 (Core C)
  proof: Functor.ext_of_iso functorToCoreInclusionIso (by cat_disch)

中文:
定理 functorToCore_inclusion
  结论: functorToCore (inclusion C) = 𝟭 (核 C)
  证明: Functor.ext_of_iso functorToCoreInclusionIso (by cat_disch)

Depends on / 依赖: Functor, Functor.ext_of_iso, cat_disch, ext_of_iso, functorToCoreInclusionIso
-/
theorem functorToCore_inclusion : functorToCore (inclusion C) = 𝟭 (Core C) :=
  Functor.ext_of_iso functorToCoreInclusionIso (by cat_disch)

end Core

variable (D : Type u₂) [Category.{v₂} D]

namespace Equivalence

set_option backward.isDefEq.respectTransparency.types false in
variable {D} in
/-- Equivalent categories have equivalent cores. -/
@[simps!]
/--
Definition of `core` / `core` 的定义

English:
definition core
  signature: (E : C ≌ D)
  body: E.functor.core
  inverse := E.inverse.core
  unitIso := E.unitIso.core
  counitIso := E.counitIso.core

中文:
定义 core
  签名: (E : C ≌ D)
  定义体: E.functor.core
  inverse := E.inverse.core
  unitIso := E.unitIso.core
  counitIso := E.counitIso.core

Depends on / 依赖: E.functor.core, functor
-/
def core (E : C ≌ D) : Core C ≌ Core D where
  functor := E.functor.core
  inverse := E.inverse.core
  unitIso := E.unitIso.core
  counitIso := E.counitIso.core

end Equivalence

set_option backward.isDefEq.respectTransparency.types false in
variable (C) in
/-- Taking the core of a functor is functorial if we discard non-invertible natural
transformations. -/
@[simps!]
/--
Definition of `coreFunctor` / `coreFunctor` 的定义

English:
definition coreFunctor
  signature: : Core (C ⥤ D) ⥤ Core C ⥤ Core D where
  body: F.of.core
  map η := η.iso.core.hom

中文:
定义 coreFunctor
  签名: : 核 (C ⥤ D) ⥤ 核 C ⥤ 核 D where
  定义体: F.of.core
  map η := η.iso.core.hom

Depends on / 依赖: F.of.core
-/
def coreFunctor : Core (C ⥤ D) ⥤ Core C ⥤ Core D where
  obj F := F.of.core
  map η := η.iso.core.hom

end

/--
Definition of `ofEquivFunctor` / `ofEquivFunctor` 的定义

English:
definition ofEquivFunctor
  signature: (m : Type u₁ -> Type u₂) [EquivFunctor m]
  body: .mk m x.of
map f := .mk (EquivFunctor.mapEquiv m f.iso.toEquiv).toIso
  map_id α := by ext x; exact congr_fun (EquivFunctor.map_refl' _) x
  map_comp f g := by
    ext
    simp [Equiv.toIso, EquivFunctor.map_trans']

中文:
定义 ofEquivFunctor
  签名: (m : 类型u₁ -> 类型u₂) [等价函子 m]
  定义体: .mk m x.of
map f := .mk (EquivFunctor.mapEquiv m f.iso.toEquiv).toIso
  map_id α := by ext x; exact congr_fun (EquivFunctor.map_refl' _) x
  map_comp f g := by
    ext
    simp [Equiv.toIso, EquivFunctor.map_trans']

Depends on / 依赖: x.of
-/
def ofEquivFunctor (m : Type u₁ -> Type u₂) [EquivFunctor m] :
    Core (Type u₁) ⥤ Core (Type u₂) where
obj x := .mk m x.of
map f := .mk (EquivFunctor.mapEquiv m f.iso.toEquiv).toIso
  map_id α := by ext x; exact congr_fun (EquivFunctor.map_refl' _) x
  map_comp f g := by
    ext
    simp [Equiv.toIso, EquivFunctor.map_trans']

end CategoryTheory
