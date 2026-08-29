/-
Copyright (c) 2022 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno, Calle Sönne
-/
module

public import Mathlib.CategoryTheory.Bicategory.Functor.Oplax
public import Mathlib.CategoryTheory.Bicategory.Functor.Lax
public import Mathlib.Tactic.CategoryTheory.ToApp

/-!
# Pseudofunctors

A pseudofunctor is an oplax (or lax) functor whose `mapId` and `mapComp` are isomorphisms.
We provide several constructors for pseudofunctors:
* `Pseudofunctor.mk` : the default constructor, which requires `map₂_whiskerLeft` and
  `map₂_whiskerRight` instead of naturality of `mapComp`.

* `Pseudofunctor.mkOfOplax` : construct a pseudofunctor from an oplax functor whose
  `mapId` and `mapComp` are isomorphisms. This constructor uses `Iso` to describe isomorphisms.
* `Pseudofunctor.mkOfOplax'` : similar to `mkOfOplax`, but uses `IsIso` to describe isomorphisms.

* `Pseudofunctor.mkOfLax` : construct a pseudofunctor from a lax functor whose
  `mapId` and `mapComp` are isomorphisms. This constructor uses `Iso` to describe isomorphisms.
* `Pseudofunctor.mkOfLax'` : similar to `mkOfLax`, but uses `IsIso` to describe isomorphisms.

## Main definitions

* `CategoryTheory.Pseudofunctor B C` : a pseudofunctor between bicategories `B` and `C`, which we
  denote by `B ⥤ᵖ C`.
* `CategoryTheory.Pseudofunctor.comp F G` : the composition of pseudofunctors

-/

@[expose] public section

namespace CategoryTheory

open Category Bicategory

universe w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]
variable {D : Type u₃} [Bicategory.{w₃, v₃} D]

/--
Definition of `Pseudofunctor` / `Pseudofunctor` 的定义

English:
structure Pseudofunctor
  parameters: (B : Type u₁) [Bicategory.{w₁, v₁} B] (C : Type u₂)
  extends: PrelaxFunctor B C
  axioms and operations (7):
    - mapId((a : B)) : map (𝟙 a) ≅ 𝟙 (obj a)
    - mapComp({a b c : B} (f : a ⟶ b) (g : b ⟶ c)) : map (f ≫ g) ≅ map f ≫ map g
    - map₂_whisker_left : forall {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h), map₂ (f ◁ η) = (mapComp f g).hom ≫ map f ◁ map₂ η ≫ (mapComp f h).inv  [default: by cat_disch]
    - map₂_whisker_right : forall {a b c : B} {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c), map₂ (η ▷ h) = (mapComp f h).hom ≫ map₂ η ▷ map h ≫ (mapComp g h).inv  [default: by cat_disch]
    - map₂_associator : forall {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d), map₂ (α_ f g h).hom = (mapComp (f ≫ g) h).hom ≫ (mapComp f g).hom ▷ map h ≫ (α_ (map f) (map g) (map h)).hom ≫ map f ◁ (mapComp g h).inv ≫ (mapComp f (g ≫ h)).inv  [default: by cat_disch]
    - map₂_left_unitor : forall {a b : B} (f : a ⟶ b), map₂ (fun_ f).hom = (mapComp (𝟙 a) f).hom ≫ (mapId a).hom ▷ map f ≫ (fun_ (map f)).hom  [default: by cat_disch]
    - map₂_right_unitor : forall {a b : B} (f : a ⟶ b), map₂ (ρ_ f).hom = (mapComp f (𝟙 b)).hom ≫ map f ◁ (mapId b).hom ≫ (ρ_ (map f)).hom  [default: by cat_disch]

中文:
结构 Pseudofunctor
  参数: (B : 类型u₁) [双范畴.{w₁, v₁} B] (C : 类型u₂)
  继承: 预松弛函子 B C
  公理与运算 (7 个):
    - mapId((a : B)) : map (𝟙 a) ≅ 𝟙 (obj a)
    - mapComp({a b c : B} (f : a ⟶ b) (g : b ⟶ c)) : map (f ≫ g) ≅ map f ≫ map g
    - map₂_whisker_left : 对任意 {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h), map₂ (f ◁ η) = (mapComp f g).hom ≫ map f ◁ map₂ η ≫ (mapComp f h).inv  [默认: by cat_disch]
    - map₂_whisker_right : 对任意 {a b c : B} {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c), map₂ (η ▷ h) = (mapComp f h).hom ≫ map₂ η ▷ map h ≫ (mapComp g h).inv  [默认: by cat_disch]
    - map₂_associator : 对任意 {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d), map₂ (α_ f g h).hom = (mapComp (f ≫ g) h).hom ≫ (mapComp f g).hom ▷ map h ≫ (α_ (map f) (map g) (map h)).hom ≫ map f ◁ (mapComp g h).inv ≫ (mapComp f (g ≫ h)).inv  [默认: by cat_disch]
    - map₂_left_unitor : 对任意 {a b : B} (f : a ⟶ b), map₂ (fun_ f).hom = (mapComp (𝟙 a) f).hom ≫ (mapId a).hom ▷ map f ≫ (fun_ (map f)).hom  [默认: by cat_disch]
    - map₂_right_unitor : 对任意 {a b : B} (f : a ⟶ b), map₂ (ρ_ f).hom = (mapComp f (𝟙 b)).hom ≫ map f ◁ (mapId b).hom ≫ (ρ_ (map f)).hom  [默认: by cat_disch]

Depends on / 依赖: cat_disch, fun_, mapComp
-/
structure Pseudofunctor (B : Type u₁) [Bicategory.{w₁, v₁} B] (C : Type u₂)
    [Bicategory.{w₂, v₂} C] extends PrelaxFunctor B C where
  mapId (a : B) : map (𝟙 a) ≅ 𝟙 (obj a)
  mapComp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) : map (f ≫ g) ≅ map f ≫ map g
  map₂_whisker_left :
    forall {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h),
      map₂ (f ◁ η) = (mapComp f g).hom ≫ map f ◁ map₂ η ≫ (mapComp f h).inv := by
    cat_disch
  map₂_whisker_right :
    forall {a b c : B} {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c),
      map₂ (η ▷ h) = (mapComp f h).hom ≫ map₂ η ▷ map h ≫ (mapComp g h).inv := by
    cat_disch
  map₂_associator :
    forall {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d),
      map₂ (α_ f g h).hom = (mapComp (f ≫ g) h).hom ≫ (mapComp f g).hom ▷ map h ≫
      (α_ (map f) (map g) (map h)).hom ≫ map f ◁ (mapComp g h).inv ≫
      (mapComp f (g ≫ h)).inv := by
    cat_disch
  map₂_left_unitor :
    forall {a b : B} (f : a ⟶ b),
      map₂ (fun_ f).hom = (mapComp (𝟙 a) f).hom ≫ (mapId a).hom ▷ map f ≫ (fun_ (map f)).hom := by
    cat_disch
  map₂_right_unitor :
    forall {a b : B} (f : a ⟶ b),
      map₂ (ρ_ f).hom = (mapComp f (𝟙 b)).hom ≫ map f ◁ (mapId b).hom ≫ (ρ_ (map f)).hom := by
    cat_disch

/-- Notation for a pseudofunctor between bicategories. -/
-- Given similar precedence as ⥤ (26).
scoped[CategoryTheory.Bicategory] infixr:26 " ⥤ᵖ " => Pseudofunctor -- type as \func\^p

initialize_simps_projections Pseudofunctor (+toPrelaxFunctor, -obj, -map, -map₂)

namespace Pseudofunctor

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
attribute [simp, to_app (attr := reassoc)]
  map₂_whisker_left map₂_whisker_right map₂_associator map₂_left_unitor map₂_right_unitor

section

open Iso

/-- The underlying prelax functor. -/
add_decl_doc Pseudofunctor.toPrelaxFunctor


attribute [nolint docBlame] CategoryTheory.Pseudofunctor.mapId
  CategoryTheory.Pseudofunctor.mapComp
  CategoryTheory.Pseudofunctor.map₂_whisker_left
  CategoryTheory.Pseudofunctor.map₂_whisker_right
  CategoryTheory.Pseudofunctor.map₂_associator
  CategoryTheory.Pseudofunctor.map₂_left_unitor
  CategoryTheory.Pseudofunctor.map₂_right_unitor

variable (F : B ⥤ᵖ C)

/-- The oplax functor associated with a pseudofunctor. -/
@[simps]
/--
Definition of `toOplax` / `toOplax` 的定义

English:
definition toOplax
  signature: : B ⥤ᵒᵖᴸ C where
  body: F.toPrelaxFunctor
  mapId := fun a => (F.mapId a).hom
  mapComp := fun f g => (F.mapComp f g).hom

中文:
定义 toOplax
  签名: : B ⥤ᵒᵖᴸ C where
  定义体: F.toPrelaxFunctor
  mapId := fun a => (F.mapId a).hom
  mapComp := fun f g => (F.mapComp f g).hom

Depends on / 依赖: F.toPrelaxFunctor, toPrelaxFunctor
-/
def toOplax : B ⥤ᵒᵖᴸ C where
  toPrelaxFunctor := F.toPrelaxFunctor
  mapId := fun a => (F.mapId a).hom
  mapComp := fun f g => (F.mapComp f g).hom

/--
Instance `hasCoeToOplax` / 实例 `hasCoeToOplax`

English:
instance hasCoeToOplax
  signature: : Coe (B ⥤ᵖ C) (B ⥤ᵒᵖᴸ C)
  body: ⟨toOplax⟩

中文:
实例 hasCoeToOplax
  签名: : Coe (B ⥤ᵖ C) (B ⥤ᵒᵖᴸ C)
  定义体: ⟨toOplax⟩

Depends on / 依赖: toOplax
-/
instance hasCoeToOplax : Coe (B ⥤ᵖ C) (B ⥤ᵒᵖᴸ C) :=
  ⟨toOplax⟩

/-- The lax functor associated with a pseudofunctor. -/
@[simps]
/--
Definition of `toLax` / `toLax` 的定义

English:
definition toLax
  signature: : B ⥤ᴸ C where
  body: F.toPrelaxFunctor
  mapId := fun a => (F.mapId a).inv
  mapComp := fun f g => (F.mapComp f g).inv
  map₂_leftUnitor f := by
    rw [← F.map₂Iso_inv]; rw [eq_inv_comp]; rw [comp_inv_eq]
    simp
  map₂_rightUnitor f := by
    rw [← F.map₂Iso_inv]; rw [eq_inv_comp]; rw [comp_inv_eq]
    simp

中文:
定义 toLax
  签名: : B ⥤ᴸ C where
  定义体: F.toPrelaxFunctor
  mapId := fun a => (F.mapId a).inv
  mapComp := fun f g => (F.mapComp f g).inv
  map₂_leftUnitor f := by
    rw [← F.map₂Iso_inv]; rw [eq_inv_comp]; rw [comp_inv_eq]
    simp
  map₂_rightUnitor f := by
    rw [← F.map₂Iso_inv]; rw [eq_inv_comp]; rw [comp_inv_eq]
    simp

Depends on / 依赖: F.toPrelaxFunctor, toPrelaxFunctor
-/
def toLax : B ⥤ᴸ C where
  toPrelaxFunctor := F.toPrelaxFunctor
  mapId := fun a => (F.mapId a).inv
  mapComp := fun f g => (F.mapComp f g).inv
  map₂_leftUnitor f := by
    rw [← F.map₂Iso_inv]; rw [eq_inv_comp]; rw [comp_inv_eq]
    simp
  map₂_rightUnitor f := by
    rw [← F.map₂Iso_inv]; rw [eq_inv_comp]; rw [comp_inv_eq]
    simp

/--
Instance `hasCoeToLax` / 实例 `hasCoeToLax`

English:
instance hasCoeToLax
  signature: : Coe (B ⥤ᵖ C) (B ⥤ᴸ C)
  body: ⟨toLax⟩

中文:
实例 hasCoeToLax
  签名: : Coe (B ⥤ᵖ C) (B ⥤ᴸ C)
  定义体: ⟨toLax⟩
-/
instance hasCoeToLax : Coe (B ⥤ᵖ C) (B ⥤ᴸ C) :=
  ⟨toLax⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The identity pseudofunctor. -/
@[simps]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: (B : Type u₁) [Bicategory.{w₁, v₁} B]
  body: PrelaxFunctor.id B
  mapId := fun a => Iso.refl (𝟙 a)
  mapComp := fun f g => Iso.refl (f ≫ g)

中文:
定义 id
  签名: (B : 类型u₁) [双范畴.{w₁, v₁} B]
  定义体: PrelaxFunctor.id B
  mapId := fun a => Iso.refl (𝟙 a)
  mapComp := fun f g => Iso.refl (f ≫ g)

Depends on / 依赖: PrelaxFunctor, PrelaxFunctor.id
-/
def id (B : Type u₁) [Bicategory.{w₁, v₁} B] : B ⥤ᵖ B where
  toPrelaxFunctor := PrelaxFunctor.id B
  mapId := fun a => Iso.refl (𝟙 a)
  mapComp := fun f g => Iso.refl (f ≫ g)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (B ⥤ᵖ B)
  body: ⟨id B⟩

中文:
实例 :
  签名: 可居 (B ⥤ᵖ B)
  定义体: ⟨id B⟩
-/
instance : Inhabited (B ⥤ᵖ B) :=
  ⟨id B⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Composition of pseudofunctors. -/
@[simps]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (F : B ⥤ᵖ C) (G : C ⥤ᵖ D)
  body: F.toPrelaxFunctor.comp G.toPrelaxFunctor
  mapId := fun a => G.map₂Iso (F.mapId a) ≪≫ G.mapId (F.obj a)
  mapComp := fun f g => (G.map₂Iso (F.mapComp f g)) ≪≫ G.mapComp (F.map f) (F.map g)

中文:
定义 comp
  签名: (F : B ⥤ᵖ C) (G : C ⥤ᵖ D)
  定义体: F.toPrelaxFunctor.comp G.toPrelaxFunctor
  mapId := fun a => G.map₂Iso (F.mapId a) ≪≫ G.mapId (F.obj a)
  mapComp := fun f g => (G.map₂Iso (F.mapComp f g)) ≪≫ G.mapComp (F.map f) (F.map g)

Depends on / 依赖: F.toPrelaxFunctor.comp, G.toPrelaxFunctor, toPrelaxFunctor
-/
def comp (F : B ⥤ᵖ C) (G : C ⥤ᵖ D) : B ⥤ᵖ D where
  toPrelaxFunctor := F.toPrelaxFunctor.comp G.toPrelaxFunctor
  mapId := fun a => G.map₂Iso (F.mapId a) ≪≫ G.mapId (F.obj a)
  mapComp := fun f g => (G.map₂Iso (F.mapComp f g)) ≪≫ G.mapComp (F.map f) (F.map g)

section

variable (F : B ⥤ᵖ C) {a b : B}

@[to_app (attr := reassoc)]
/--
lemma `mapComp_assoc_right_hom` / 引理 `mapComp_assoc_right_hom`

English:
lemma mapComp_assoc_right_hom
  given: {c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d)
  proof: F.toOplax.mapComp_assoc_right _ _ _

@[to_app (attr := reassoc)]

中文:
引理 mapComp_assoc_right_hom
  条件: {c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d)
  证明: F.toOplax.mapComp_assoc_right _ _ _

@[to_app (attr := reassoc)]

Depends on / 依赖: F.toOplax.mapComp_assoc_right, mapComp_assoc_right, toOplax
-/
lemma mapComp_assoc_right_hom {c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (F.mapComp f (g ≫ h)).hom ≫ F.map f ◁ (F.mapComp g h).hom = F.map₂ (α_ f g h).inv ≫
    (F.mapComp (f ≫ g) h).hom ≫ (F.mapComp f g).hom ▷ F.map h ≫
    (α_ (F.map f) (F.map g) (F.map h)).hom :=
  F.toOplax.mapComp_assoc_right _ _ _

@[to_app (attr := reassoc)]
/--
lemma `mapComp_assoc_left_hom` / 引理 `mapComp_assoc_left_hom`

English:
lemma mapComp_assoc_left_hom
  given: {c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d)
  proof: F.toOplax.mapComp_assoc_left _ _ _

@[to_app (attr := reassoc)]

中文:
引理 mapComp_assoc_left_hom
  条件: {c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d)
  证明: F.toOplax.mapComp_assoc_left _ _ _

@[to_app (attr := reassoc)]

Depends on / 依赖: F.toOplax.mapComp_assoc_left, mapComp_assoc_left, toOplax
-/
lemma mapComp_assoc_left_hom {c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (F.mapComp (f ≫ g) h).hom ≫ (F.mapComp f g).hom ▷ F.map h =
    F.map₂ (α_ f g h).hom ≫ (F.mapComp f (g ≫ h)).hom ≫ F.map f ◁ (F.mapComp g h).hom
    ≫ (α_ (F.map f) (F.map g) (F.map h)).inv :=
  F.toOplax.mapComp_assoc_left _ _ _

@[to_app (attr := reassoc)]
/--
lemma `mapComp_assoc_right_inv` / 引理 `mapComp_assoc_right_inv`

English:
lemma mapComp_assoc_right_inv
  given: {c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d)
  proof: F.toLax.mapComp_assoc_right _ _ _

@[to_app (attr := reassoc)]

中文:
引理 mapComp_assoc_right_inv
  条件: {c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d)
  证明: F.toLax.mapComp_assoc_right _ _ _

@[to_app (attr := reassoc)]

Depends on / 依赖: F.toLax.mapComp_assoc_right, mapComp_assoc_right
-/
lemma mapComp_assoc_right_inv {c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    F.map f ◁ (F.mapComp g h).inv ≫ (F.mapComp f (g ≫ h)).inv =
    (α_ (F.map f) (F.map g) (F.map h)).inv ≫ (F.mapComp f g).inv ▷ F.map h ≫
    (F.mapComp (f ≫ g) h).inv ≫ F.map₂ (α_ f g h).hom :=
  F.toLax.mapComp_assoc_right _ _ _

@[to_app (attr := reassoc)]
/--
lemma `mapComp_assoc_left_inv` / 引理 `mapComp_assoc_left_inv`

English:
lemma mapComp_assoc_left_inv
  given: {c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d)
  proof: F.toLax.mapComp_assoc_left _ _ _

#adaptation_note

中文:
引理 mapComp_assoc_left_inv
  条件: {c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d)
  证明: F.toLax.mapComp_assoc_left _ _ _

#adaptation_note

Depends on / 依赖: F.toLax.mapComp_assoc_left, mapComp_assoc_left
-/
lemma mapComp_assoc_left_inv {c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (F.mapComp f g).inv ▷ F.map h ≫ (F.mapComp (f ≫ g) h).inv =
    (α_ (F.map f) (F.map g) (F.map h)).hom ≫ F.map f ◁ (F.mapComp g h).inv ≫
    (F.mapComp f (g ≫ h)).inv ≫ F.map₂ (α_ f g h).inv :=
  F.toLax.mapComp_assoc_left _ _ _

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[to_app (attr := reassoc)]
/--
lemma `mapComp_id_left_hom` / 引理 `mapComp_id_left_hom`

English:
lemma mapComp_id_left_hom
  given: (f : a ⟶ b)
  statement: (F.mapComp (𝟙 a) f).hom =
  proof: by
  simp

中文:
引理 mapComp_id_left_hom
  条件: (f : a ⟶ b)
  结论: (F.mapComp (𝟙 a) f).hom =
  证明: by
  simp
-/
lemma mapComp_id_left_hom (f : a ⟶ b) : (F.mapComp (𝟙 a) f).hom =
    F.map₂ (fun_ f).hom ≫ (fun_ (F.map f)).inv ≫ (F.mapId a).inv ▷ F.map f := by
  simp

/--
lemma `mapComp_id_left` / 引理 `mapComp_id_left`

English:
lemma mapComp_id_left
  given: (f : a ⟶ b)
  statement: (F.mapComp (𝟙 a) f) = F.map₂Iso (fun_ f) ≪≫
  proof: Iso.ext F.mapComp_id_left_hom f

#adaptation_note

中文:
引理 mapComp_id_left
  条件: (f : a ⟶ b)
  结论: (F.mapComp (𝟙 a) f) = F.map₂Iso (fun_ f) ≪≫
  证明: Iso.ext F.mapComp_id_left_hom f

#adaptation_note

Depends on / 依赖: F.mapComp_id_left_hom, Iso.ext, mapComp_id_left_hom
-/
lemma mapComp_id_left (f : a ⟶ b) : (F.mapComp (𝟙 a) f) = F.map₂Iso (fun_ f) ≪≫
    (fun_ (F.map f)).symm ≪≫ (whiskerRightIso (F.mapId a) (F.map f)).symm :=
Iso.ext F.mapComp_id_left_hom f

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[to_app (attr := reassoc)]
/--
lemma `mapComp_id_left_inv` / 引理 `mapComp_id_left_inv`

English:
lemma mapComp_id_left_inv
  given: (f : a ⟶ b)
  statement: (F.mapComp (𝟙 a) f).inv =
  proof: by
  simp [mapComp_id_left]

中文:
引理 mapComp_id_left_inv
  条件: (f : a ⟶ b)
  结论: (F.mapComp (𝟙 a) f).inv =
  证明: by
  simp [mapComp_id_left]

Depends on / 依赖: mapComp_id_left
-/
lemma mapComp_id_left_inv (f : a ⟶ b) : (F.mapComp (𝟙 a) f).inv =
    (F.mapId a).hom ▷ F.map f ≫ (fun_ (F.map f)).hom ≫ F.map₂ (fun_ f).inv := by
  simp [mapComp_id_left]

/--
lemma `whiskerRightIso_mapId` / 引理 `whiskerRightIso_mapId`

English:
lemma whiskerRightIso_mapId
  given: (f : a ⟶ b)
  statement: whiskerRightIso (F.mapId a) (F.map f) =
  proof: by
  simp [mapComp_id_left]

#adaptation_note

中文:
引理 whiskerRightIso_mapId
  条件: (f : a ⟶ b)
  结论: whiskerRightIso (F.mapId a) (F.map f) =
  证明: by
  simp [mapComp_id_left]

#adaptation_note

Depends on / 依赖: mapComp_id_left
-/
lemma whiskerRightIso_mapId (f : a ⟶ b) : whiskerRightIso (F.mapId a) (F.map f) =
    (F.mapComp (𝟙 a) f).symm ≪≫ F.map₂Iso (fun_ f) ≪≫ (fun_ (F.map f)).symm := by
  simp [mapComp_id_left]

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[to_app (attr := reassoc)]
/--
lemma `whiskerRight_mapId_hom` / 引理 `whiskerRight_mapId_hom`

English:
lemma whiskerRight_mapId_hom
  given: (f : a ⟶ b)
  statement: (F.mapId a).hom ▷ F.map f =
  proof: by
  simp

#adaptation_note

中文:
引理 whiskerRight_mapId_hom
  条件: (f : a ⟶ b)
  结论: (F.mapId a).hom ▷ F.map f =
  证明: by
  simp

#adaptation_note
-/
lemma whiskerRight_mapId_hom (f : a ⟶ b) : (F.mapId a).hom ▷ F.map f =
    (F.mapComp (𝟙 a) f).inv ≫ F.map₂ (fun_ f).hom ≫ (fun_ (F.map f)).inv := by
  simp

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[to_app (attr := reassoc)]
/--
lemma `whiskerRight_mapId_inv` / 引理 `whiskerRight_mapId_inv`

English:
lemma whiskerRight_mapId_inv
  given: (f : a ⟶ b)
  statement: (F.mapId a).inv ▷ F.map f =
  proof: by
  simpa using congrArg (·.inv) (F.whiskerRightIso_mapId f)

#adaptation_note

中文:
引理 whiskerRight_mapId_inv
  条件: (f : a ⟶ b)
  结论: (F.mapId a).inv ▷ F.map f =
  证明: by
  simpa using congrArg (·.inv) (F.whiskerRightIso_mapId f)

#adaptation_note

Depends on / 依赖: F.whiskerRightIso_mapId, whiskerRightIso_mapId
-/
lemma whiskerRight_mapId_inv (f : a ⟶ b) : (F.mapId a).inv ▷ F.map f =
    (fun_ (F.map f)).hom ≫ F.map₂ (fun_ f).inv ≫ (F.mapComp (𝟙 a) f).hom := by
  simpa using congrArg (·.inv) (F.whiskerRightIso_mapId f)

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[to_app (attr := reassoc)]
/--
lemma `mapComp_id_right_hom` / 引理 `mapComp_id_right_hom`

English:
lemma mapComp_id_right_hom
  given: (f : a ⟶ b)
  statement: (F.mapComp f (𝟙 b)).hom =
  proof: by
  simp

中文:
引理 mapComp_id_right_hom
  条件: (f : a ⟶ b)
  结论: (F.mapComp f (𝟙 b)).hom =
  证明: by
  simp
-/
lemma mapComp_id_right_hom (f : a ⟶ b) : (F.mapComp f (𝟙 b)).hom =
    F.map₂ (ρ_ f).hom ≫ (ρ_ (F.map f)).inv ≫ F.map f ◁ (F.mapId b).inv := by
  simp

/--
lemma `mapComp_id_right` / 引理 `mapComp_id_right`

English:
lemma mapComp_id_right
  given: (f : a ⟶ b)
  statement: (F.mapComp f (𝟙 b)) = F.map₂Iso (ρ_ f) ≪≫
  proof: Iso.ext F.mapComp_id_right_hom f

#adaptation_note

中文:
引理 mapComp_id_right
  条件: (f : a ⟶ b)
  结论: (F.mapComp f (𝟙 b)) = F.map₂Iso (ρ_ f) ≪≫
  证明: Iso.ext F.mapComp_id_right_hom f

#adaptation_note

Depends on / 依赖: F.mapComp_id_right_hom, Iso.ext, mapComp_id_right_hom
-/
lemma mapComp_id_right (f : a ⟶ b) : (F.mapComp f (𝟙 b)) = F.map₂Iso (ρ_ f) ≪≫
    (ρ_ (F.map f)).symm ≪≫ (whiskerLeftIso (F.map f) (F.mapId b)).symm :=
Iso.ext F.mapComp_id_right_hom f

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[to_app (attr := reassoc)]
/--
lemma `mapComp_id_right_inv` / 引理 `mapComp_id_right_inv`

English:
lemma mapComp_id_right_inv
  given: (f : a ⟶ b)
  statement: (F.mapComp f (𝟙 b)).inv =
  proof: by
  simp [mapComp_id_right]

中文:
引理 mapComp_id_right_inv
  条件: (f : a ⟶ b)
  结论: (F.mapComp f (𝟙 b)).inv =
  证明: by
  simp [mapComp_id_right]

Depends on / 依赖: mapComp_id_right
-/
lemma mapComp_id_right_inv (f : a ⟶ b) : (F.mapComp f (𝟙 b)).inv =
    F.map f ◁ (F.mapId b).hom ≫ (ρ_ (F.map f)).hom ≫ F.map₂ (ρ_ f).inv := by
  simp [mapComp_id_right]

/--
lemma `whiskerLeftIso_mapId` / 引理 `whiskerLeftIso_mapId`

English:
lemma whiskerLeftIso_mapId
  given: (f : a ⟶ b)
  statement: whiskerLeftIso (F.map f) (F.mapId b) =
  proof: by
  simp [mapComp_id_right]

#adaptation_note

中文:
引理 whiskerLeftIso_mapId
  条件: (f : a ⟶ b)
  结论: whiskerLeftIso (F.map f) (F.mapId b) =
  证明: by
  simp [mapComp_id_right]

#adaptation_note

Depends on / 依赖: mapComp_id_right
-/
lemma whiskerLeftIso_mapId (f : a ⟶ b) : whiskerLeftIso (F.map f) (F.mapId b) =
    (F.mapComp f (𝟙 b)).symm ≪≫ F.map₂Iso (ρ_ f) ≪≫ (ρ_ (F.map f)).symm := by
  simp [mapComp_id_right]

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[to_app (attr := reassoc)]
/--
lemma `whiskerLeft_mapId_hom` / 引理 `whiskerLeft_mapId_hom`

English:
lemma whiskerLeft_mapId_hom
  given: (f : a ⟶ b)
  statement: F.map f ◁ (F.mapId b).hom =
  proof: by
  simp

#adaptation_note

中文:
引理 whiskerLeft_mapId_hom
  条件: (f : a ⟶ b)
  结论: F.map f ◁ (F.mapId b).hom =
  证明: by
  simp

#adaptation_note
-/
lemma whiskerLeft_mapId_hom (f : a ⟶ b) : F.map f ◁ (F.mapId b).hom =
    (F.mapComp f (𝟙 b)).inv ≫ F.map₂ (ρ_ f).hom ≫ (ρ_ (F.map f)).inv := by
  simp

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[to_app (attr := reassoc)]
/--
lemma `whiskerLeft_mapId_inv` / 引理 `whiskerLeft_mapId_inv`

English:
lemma whiskerLeft_mapId_inv
  given: (f : a ⟶ b)
  statement: F.map f ◁ (F.mapId b).inv =
  proof: by
  simpa using congrArg (·.inv) (F.whiskerLeftIso_mapId f)

中文:
引理 whiskerLeft_mapId_inv
  条件: (f : a ⟶ b)
  结论: F.map f ◁ (F.mapId b).inv =
  证明: by
  simpa using congrArg (·.inv) (F.whiskerLeftIso_mapId f)

Depends on / 依赖: F.whiskerLeftIso_mapId, whiskerLeftIso_mapId
-/
lemma whiskerLeft_mapId_inv (f : a ⟶ b) : F.map f ◁ (F.mapId b).inv =
    (ρ_ (F.map f)).hom ≫ F.map₂ (ρ_ f).inv ≫ (F.mapComp f (𝟙 b)).hom := by
  simpa using congrArg (·.inv) (F.whiskerLeftIso_mapId f)

/--
Definition of `mapId'` / `mapId'` 的定义

English:
definition mapId'
  signature: {b : B} (f : b ⟶ b) (hf : f = 𝟙 b := by cat_disch)
  body: F.map₂Iso (eqToIso (by rw [hf])) ≪≫ F.mapId _

中文:
定义 mapId'
  签名: {b : B} (f : b ⟶ b) (hf : f = 𝟙 b := by cat_disch)
  定义体: F.map₂Iso (eqToIso (by rw [hf])) ≪≫ F.mapId _
-/
def mapId' {b : B} (f : b ⟶ b) (hf : f = 𝟙 b := by cat_disch) :
    F.map f ≅ 𝟙 (F.obj b) :=
  F.map₂Iso (eqToIso (by rw [hf])) ≪≫ F.mapId _

set_option backward.defeqAttrib.useBackward true in
/--
lemma `mapId'_eq_mapId` / 引理 `mapId'_eq_mapId`

English:
lemma mapId'_eq_mapId
  given: (b : B)
  proof: by
  simp [mapId']

@[simp]

中文:
引理 mapId'_eq_mapId
  条件: (b : B)
  证明: by
  simp [mapId']

@[simp]
-/
lemma mapId'_eq_mapId (b : B) :
    F.mapId' (𝟙 b) rfl = F.mapId b := by
  simp [mapId']

@[simp]
/--
lemma `toLax_mapId'` / 引理 `toLax_mapId'`

English:
lemma toLax_mapId'
  given: {b : B} (f : b ⟶ b) (hf : f = 𝟙 b := by cat_disch)
  proof: rfl

@[simp]

中文:
引理 toLax_mapId'
  条件: {b : B} (f : b ⟶ b) (hf : f = 𝟙 b := by cat_disch)
  证明: rfl

@[simp]

Depends on / 依赖: F.mapId, F.toLax.mapId, cat_disch
-/
lemma toLax_mapId' {b : B} (f : b ⟶ b) (hf : f = 𝟙 b := by cat_disch) :
    F.toLax.mapId' f hf = (F.mapId' f hf).inv :=
  rfl

@[simp]
/--
lemma `toOplax_mapId'` / 引理 `toOplax_mapId'`

English:
lemma toOplax_mapId'
  given: {b : B} (f : b ⟶ b) (hf : f = 𝟙 b := by cat_disch)
  proof: rfl

中文:
引理 toOplax_mapId'
  条件: {b : B} (f : b ⟶ b) (hf : f = 𝟙 b := by cat_disch)
  证明: rfl

Depends on / 依赖: F.mapId, F.toOplax.mapId, cat_disch, toOplax
-/
lemma toOplax_mapId' {b : B} (f : b ⟶ b) (hf : f = 𝟙 b := by cat_disch) :
    F.toOplax.mapId' f hf = (F.mapId' f hf).hom :=
  rfl

/--
Definition of `mapComp'` / `mapComp'` 的定义

English:
definition mapComp'
  signature: {b₀ b₁ b₂ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (fg : b₀ ⟶ b₂)
  body: F.map₂Iso (eqToIso (by rw [h])) ≪≫ F.mapComp f g

中文:
定义 mapComp'
  签名: {b₀ b₁ b₂ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (fg : b₀ ⟶ b₂)
  定义体: F.map₂Iso (eqToIso (by rw [h])) ≪≫ F.mapComp f g
-/
def mapComp' {b₀ b₁ b₂ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (fg : b₀ ⟶ b₂)
    (h : f ≫ g = fg := by cat_disch) :
    F.map fg ≅ F.map f ≫ F.map g :=
  F.map₂Iso (eqToIso (by rw [h])) ≪≫ F.mapComp f g

set_option backward.defeqAttrib.useBackward true in
/--
lemma `mapComp'_eq_mapComp` / 引理 `mapComp'_eq_mapComp`

English:
lemma mapComp'_eq_mapComp
  given: {b₀ b₁ b₂ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂)
  proof: by
  simp [mapComp']

@[simp]

中文:
引理 mapComp'_eq_mapComp
  条件: {b₀ b₁ b₂ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂)
  证明: by
  simp [mapComp']

@[simp]
-/
lemma mapComp'_eq_mapComp {b₀ b₁ b₂ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) :
    F.mapComp' f g _ rfl = F.mapComp f g := by
  simp [mapComp']

@[simp]
/--
lemma `toLax_mapComp'` / 引理 `toLax_mapComp'`

English:
lemma toLax_mapComp'
  statement: {b₀ b₁ b₂ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (fg : b₀ ⟶ b₂)
  proof: rfl

@[simp]

中文:
引理 toLax_mapComp'
  结论: {b₀ b₁ b₂ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (fg : b₀ ⟶ b₂)
  证明: rfl

@[simp]

Depends on / 依赖: F.mapComp, F.toLax.mapComp, cat_disch, mapComp
-/
lemma toLax_mapComp' {b₀ b₁ b₂ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (fg : b₀ ⟶ b₂)
    (h : f ≫ g = fg := by cat_disch) :
    F.toLax.mapComp' f g fg h = (F.mapComp' f g fg h).inv :=
  rfl

@[simp]
/--
lemma `toOplax_mapComp'` / 引理 `toOplax_mapComp'`

English:
lemma toOplax_mapComp'
  statement: {b₀ b₁ b₂ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (fg : b₀ ⟶ b₂)
  proof: rfl

中文:
引理 toOplax_mapComp'
  结论: {b₀ b₁ b₂ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (fg : b₀ ⟶ b₂)
  证明: rfl

Depends on / 依赖: F.mapComp, F.toOplax.mapComp, cat_disch, mapComp, toOplax
-/
lemma toOplax_mapComp' {b₀ b₁ b₂ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (fg : b₀ ⟶ b₂)
    (h : f ≫ g = fg := by cat_disch) :
    F.toOplax.mapComp' f g fg h = (F.mapComp' f g fg h).hom :=
  rfl

end

/-- Construct a pseudofunctor from an oplax functor whose `mapId` and `mapComp` are isomorphisms. -/
@[simps]
/--
Definition of `mkOfOplax` / `mkOfOplax` 的定义

English:
definition mkOfOplax
  signature: (F : B ⥤ᵒᵖᴸ C) (F' : F.PseudoCore)
  body: F.toPrelaxFunctor
  mapId := F'.mapIdIso
  mapComp := F'.mapCompIso
  map₂_whisker_left := fun f g h η => by
    rw [F'.mapCompIso_hom f g]; rw [← F.mapComp_naturality_right_assoc]; rw [← F'.mapCompIso_hom f h]; rw [hom_inv_id]; rw [comp_id]
  map₂_whisker_right := fun η h => by
    rw [F'.mapCompIso_hom _ h]; rw [← F.mapComp_naturality_left_assoc]; rw [← F'.mapCompIso_hom _ h]; rw [hom_inv_id]; rw [comp_id]
  map₂_associator := fun f g h => by
    rw [F'.mapCompIso_hom (f ≫ g) h]; rw [F'.mapCompIso_hom f g]; rw [← F.map₂_associator_assoc]; rw [←
      F'.mapCompIso_hom f (g ≫ h)]; rw [← F'.mapCompIso_hom g h]; rw [whiskerLeft_hom_inv_assoc]; rw [hom_inv_id]; rw [comp_id]

中文:
定义 mkOfOplax
  签名: (F : B ⥤ᵒᵖᴸ C) (F' : F.PseudoCore)
  定义体: F.toPrelaxFunctor
  mapId := F'.mapIdIso
  mapComp := F'.mapCompIso
  map₂_whisker_left := fun f g h η => by
    rw [F'.mapCompIso_hom f g]; rw [← F.mapComp_naturality_right_assoc]; rw [← F'.mapCompIso_hom f h]; rw [hom_inv_id]; rw [comp_id]
  map₂_whisker_right := fun η h => by
    rw [F'.mapCompIso_hom _ h]; rw [← F.mapComp_naturality_left_assoc]; rw [← F'.mapCompIso_hom _ h]; rw [hom_inv_id]; rw [comp_id]
  map₂_associator := fun f g h => by
    rw [F'.mapCompIso_hom (f ≫ g) h]; rw [F'.mapCompIso_hom f g]; rw [← F.map₂_associator_assoc]; rw [←
      F'.mapCompIso_hom f (g ≫ h)]; rw [← F'.mapCompIso_hom g h]; rw [whiskerLeft_hom_inv_assoc]; rw [hom_inv_id]; rw [comp_id]

Depends on / 依赖: F.toPrelaxFunctor, toPrelaxFunctor
-/
def mkOfOplax (F : B ⥤ᵒᵖᴸ C) (F' : F.PseudoCore) : B ⥤ᵖ C where
  toPrelaxFunctor := F.toPrelaxFunctor
  mapId := F'.mapIdIso
  mapComp := F'.mapCompIso
  map₂_whisker_left := fun f g h η => by
    rw [F'.mapCompIso_hom f g]; rw [← F.mapComp_naturality_right_assoc]; rw [← F'.mapCompIso_hom f h]; rw [hom_inv_id]; rw [comp_id]
  map₂_whisker_right := fun η h => by
    rw [F'.mapCompIso_hom _ h]; rw [← F.mapComp_naturality_left_assoc]; rw [← F'.mapCompIso_hom _ h]; rw [hom_inv_id]; rw [comp_id]
  map₂_associator := fun f g h => by
    rw [F'.mapCompIso_hom (f ≫ g) h]; rw [F'.mapCompIso_hom f g]; rw [← F.map₂_associator_assoc]; rw [←
      F'.mapCompIso_hom f (g ≫ h)]; rw [← F'.mapCompIso_hom g h]; rw [whiskerLeft_hom_inv_assoc]; rw [hom_inv_id]; rw [comp_id]

/-- Construct a pseudofunctor from an oplax functor whose `mapId` and `mapComp` are isomorphisms. -/
@[simps!]
/--
Definition of `mkOfOplax'` / `mkOfOplax'` 的定义

English:
definition mkOfOplax'
  signature: (F : B ⥤ᵒᵖᴸ C) [forall a, IsIso (F.mapId a)]
  body: F.toPrelaxFunctor
  mapId := fun a => asIso (F.mapId a)
  mapComp := fun f g => asIso (F.mapComp f g)
  map₂_whisker_left := fun f g h η => by
    dsimp
    rw [← assoc]; rw [IsIso.eq_comp_inv]; rw [F.mapComp_naturality_right]
  map₂_whisker_right := fun η h => by
    dsimp
    rw [← assoc]; rw [IsIso.eq_comp_inv]; rw [F.mapComp_naturality_left]
  map₂_associator := fun f g h => by
    dsimp
    simp only [← assoc]
    rw [IsIso.eq_comp_inv]; rw [← Bicategory.inv_whiskerLeft]; rw [IsIso.eq_comp_inv]
    simp only [assoc, F.map₂_associator]

中文:
定义 mkOfOplax'
  签名: (F : B ⥤ᵒᵖᴸ C) [对任意 a, 是同构 (F.mapId a)]
  定义体: F.toPrelaxFunctor
  mapId := fun a => asIso (F.mapId a)
  mapComp := fun f g => asIso (F.mapComp f g)
  map₂_whisker_left := fun f g h η => by
    dsimp
    rw [← assoc]; rw [IsIso.eq_comp_inv]; rw [F.mapComp_naturality_right]
  map₂_whisker_right := fun η h => by
    dsimp
    rw [← assoc]; rw [IsIso.eq_comp_inv]; rw [F.mapComp_naturality_left]
  map₂_associator := fun f g h => by
    dsimp
    simp only [← assoc]
    rw [IsIso.eq_comp_inv]; rw [← Bicategory.inv_whiskerLeft]; rw [IsIso.eq_comp_inv]
    simp only [assoc, F.map₂_associator]

Depends on / 依赖: F.toPrelaxFunctor, toPrelaxFunctor
-/
noncomputable def mkOfOplax' (F : B ⥤ᵒᵖᴸ C) [forall a, IsIso (F.mapId a)]
    [forall {a b c} (f : a ⟶ b) (g : b ⟶ c), IsIso (F.mapComp f g)] : B ⥤ᵖ C where
  toPrelaxFunctor := F.toPrelaxFunctor
  mapId := fun a => asIso (F.mapId a)
  mapComp := fun f g => asIso (F.mapComp f g)
  map₂_whisker_left := fun f g h η => by
    dsimp
    rw [← assoc]; rw [IsIso.eq_comp_inv]; rw [F.mapComp_naturality_right]
  map₂_whisker_right := fun η h => by
    dsimp
    rw [← assoc]; rw [IsIso.eq_comp_inv]; rw [F.mapComp_naturality_left]
  map₂_associator := fun f g h => by
    dsimp
    simp only [← assoc]
    rw [IsIso.eq_comp_inv]; rw [← Bicategory.inv_whiskerLeft]; rw [IsIso.eq_comp_inv]
    simp only [assoc, F.map₂_associator]

/-- Construct a pseudofunctor from a lax functor whose `mapId` and `mapComp` are isomorphisms. -/
@[simps]
/--
Definition of `mkOfLax` / `mkOfLax` 的定义

English:
definition mkOfLax
  signature: (F : B ⥤ᴸ C) (F' : F.PseudoCore)
  body: F.toPrelaxFunctor
  mapId := F'.mapIdIso
  mapComp := F'.mapCompIso
  map₂_whisker_left f g h η := by
    rw [F'.mapCompIso_inv]; rw [← LaxFunctor.mapComp_naturality_right]; rw [← F'.mapCompIso_inv]; rw [hom_inv_id_assoc]
  map₂_whisker_right η h := by
    rw [F'.mapCompIso_inv]; rw [← LaxFunctor.mapComp_naturality_left]; rw [← F'.mapCompIso_inv]; rw [hom_inv_id_assoc]
  map₂_associator {a b c d} f g h := by
    rw [F'.mapCompIso_inv]; rw [F'.mapCompIso_inv]; rw [← inv_comp_eq]; rw [← IsIso.inv_comp_eq]
    simp
  map₂_left_unitor {a b} f := by rw [← IsIso.inv_eq_inv, ← F.map₂_inv]; simp
  map₂_right_unitor {a b} f := by rw [← IsIso.inv_eq_inv, ← F.map₂_inv]; simp

中文:
定义 mkOfLax
  签名: (F : B ⥤ᴸ C) (F' : F.PseudoCore)
  定义体: F.toPrelaxFunctor
  mapId := F'.mapIdIso
  mapComp := F'.mapCompIso
  map₂_whisker_left f g h η := by
    rw [F'.mapCompIso_inv]; rw [← LaxFunctor.mapComp_naturality_right]; rw [← F'.mapCompIso_inv]; rw [hom_inv_id_assoc]
  map₂_whisker_right η h := by
    rw [F'.mapCompIso_inv]; rw [← LaxFunctor.mapComp_naturality_left]; rw [← F'.mapCompIso_inv]; rw [hom_inv_id_assoc]
  map₂_associator {a b c d} f g h := by
    rw [F'.mapCompIso_inv]; rw [F'.mapCompIso_inv]; rw [← inv_comp_eq]; rw [← IsIso.inv_comp_eq]
    simp
  map₂_left_unitor {a b} f := by rw [← IsIso.inv_eq_inv, ← F.map₂_inv]; simp
  map₂_right_unitor {a b} f := by rw [← IsIso.inv_eq_inv, ← F.map₂_inv]; simp

Depends on / 依赖: F.toPrelaxFunctor, toPrelaxFunctor
-/
def mkOfLax (F : B ⥤ᴸ C) (F' : F.PseudoCore) : B ⥤ᵖ C where
  toPrelaxFunctor := F.toPrelaxFunctor
  mapId := F'.mapIdIso
  mapComp := F'.mapCompIso
  map₂_whisker_left f g h η := by
    rw [F'.mapCompIso_inv]; rw [← LaxFunctor.mapComp_naturality_right]; rw [← F'.mapCompIso_inv]; rw [hom_inv_id_assoc]
  map₂_whisker_right η h := by
    rw [F'.mapCompIso_inv]; rw [← LaxFunctor.mapComp_naturality_left]; rw [← F'.mapCompIso_inv]; rw [hom_inv_id_assoc]
  map₂_associator {a b c d} f g h := by
    rw [F'.mapCompIso_inv]; rw [F'.mapCompIso_inv]; rw [← inv_comp_eq]; rw [← IsIso.inv_comp_eq]
    simp
  map₂_left_unitor {a b} f := by rw [← IsIso.inv_eq_inv, ← F.map₂_inv]; simp
  map₂_right_unitor {a b} f := by rw [← IsIso.inv_eq_inv, ← F.map₂_inv]; simp

/-- Construct a pseudofunctor from a lax functor whose `mapId` and `mapComp` are isomorphisms. -/
@[simps!]
/--
Definition of `mkOfLax'` / `mkOfLax'` 的定义

English:
definition mkOfLax'
  signature: (F : B ⥤ᴸ C) [forall a, IsIso (F.mapId a)]
  body: mkOfLax F
  { mapIdIso := fun a => (asIso (F.mapId a)).symm
    mapCompIso := fun f g => (asIso (F.mapComp f g)).symm }

中文:
定义 mkOfLax'
  签名: (F : B ⥤ᴸ C) [对任意 a, 是同构 (F.mapId a)]
  定义体: mkOfLax F
  { mapIdIso := fun a => (asIso (F.mapId a)).symm
    mapCompIso := fun f g => (asIso (F.mapComp f g)).symm }

Depends on / 依赖: F.mapComp, F.mapId, mapComp, mapCompIso, mapIdIso, mkOfLax
-/
noncomputable def mkOfLax' (F : B ⥤ᴸ C) [forall a, IsIso (F.mapId a)]
    [forall {a b c} (f : a ⟶ b) (g : b ⟶ c), IsIso (F.mapComp f g)] : B ⥤ᵖ C :=
  mkOfLax F
  { mapIdIso := fun a => (asIso (F.mapId a)).symm
    mapCompIso := fun f g => (asIso (F.mapComp f g)).symm }

end

end Pseudofunctor

end CategoryTheory
