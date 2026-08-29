/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/
module

public import Mathlib.CategoryTheory.Bicategory.Functor.Prelax
public import Mathlib.Tactic.CategoryTheory.Slice
public import Mathlib.Tactic.CategoryTheory.ToApp

/-!
# Lax functors

A lax functor `F` between bicategories `B` and `C` consists of
* a function between objects `F.obj : B → C`,
* a family of functions between 1-morphisms `F.map : (a ⟶ b) → (F.obj a ⟶ F.obj b)`,
* a family of functions between 2-morphisms `F.map₂ : (f ⟶ g) → (F.map f ⟶ F.map g)`,
* a family of 2-morphisms `F.mapId a : 𝟙 (F.obj a) ⟶ F.map (𝟙 a)`,
* a family of 2-morphisms `F.mapComp f g : F.map f ≫ F.map g ⟶ F.map (f ≫ g)`, and
* certain consistency conditions on them.

## Main definitions

* `CategoryTheory.LaxFunctor B C` : a lax functor between bicategories `B` and `C`, which we
  denote by `B ⥤ᴸ C`.
* `CategoryTheory.LaxFunctor.comp F G` : the composition of lax functors
* `CategoryTheory.LaxFunctor.PseudoCore` : a structure on a lax functor that promotes a
  lax functor to a pseudofunctor

## Future work

Some constructions in the bicategory library have only been done in terms of oplax functors,
since lax functors had not yet been added (e.g `FunctorBicategory.lean`). A possible project would
be to mirror these constructions for lax functors.

-/

@[expose] public section

namespace CategoryTheory

open Category Bicategory

open Bicategory

universe w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃

/--
Definition of `LaxFunctor` / `LaxFunctor` 的定义

English:
structure LaxFunctor
  parameters: (B : Type u₁) [Bicategory.{w₁, v₁} B] (C : Type u₂) [Bicategory.{w₂, v₂} C]
  extends: PrelaxFunctor B C
  axioms and operations (7):
    - mapId((a : B)) : 𝟙 (obj a) ⟶ map (𝟙 a)
    - mapComp({a b c : B} (f : a ⟶ b) (g : b ⟶ c)) : map f ≫ map g ⟶ map (f ≫ g)
    - mapComp_naturality_left : forall {a b c : B} {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c), mapComp f g ≫ map₂ (η ▷ g) = map₂ η ▷ map g ≫ mapComp f' g  [default: by cat_disch]
    - mapComp_naturality_right : forall {a b c : B} (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g'), mapComp f g ≫ map₂ (f ◁ η) = map f ◁ map₂ η ≫ mapComp f g'  [default: by cat_disch]
    - map₂_associator : forall {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d), mapComp f g ▷ map h ≫ mapComp (f ≫ g) h ≫ map₂ (α_ f g h).hom = (α_ (map f) (map g) (map h)).hom ≫ map f ◁ mapComp g h ≫ mapComp f (g ≫ h)  [default: by cat_disch]
    - map₂_leftUnitor : forall {a b : B} (f : a ⟶ b), map₂ (fun_ f).inv = (fun_ (map f)).inv ≫ mapId a ▷ map f ≫ mapComp (𝟙 a) f  [default: by cat_disch]
    - map₂_rightUnitor : forall {a b : B} (f : a ⟶ b), map₂ (ρ_ f).inv = (ρ_ (map f)).inv ≫ map f ◁ mapId b ≫ mapComp f (𝟙 b)  [default: by cat_disch]

中文:
结构 松弛函子
  参数: (B : 类型u₁) [双范畴.{w₁, v₁} B] (C : 类型u₂) [双范畴.{w₂, v₂} C]
  继承: 预松弛函子 B C
  公理与运算 (7 个):
    - mapId((a : B)) : 𝟙 (obj a) ⟶ map (𝟙 a)
    - mapComp({a b c : B} (f : a ⟶ b) (g : b ⟶ c)) : map f ≫ map g ⟶ map (f ≫ g)
    - mapComp_naturality_left : 对任意 {a b c : B} {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c), mapComp f g ≫ map₂ (η ▷ g) = map₂ η ▷ map g ≫ mapComp f' g  [默认: by cat_disch]
    - mapComp_naturality_right : 对任意 {a b c : B} (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g'), mapComp f g ≫ map₂ (f ◁ η) = map f ◁ map₂ η ≫ mapComp f g'  [默认: by cat_disch]
    - map₂_associator : 对任意 {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d), mapComp f g ▷ map h ≫ mapComp (f ≫ g) h ≫ map₂ (α_ f g h).hom = (α_ (map f) (map g) (map h)).hom ≫ map f ◁ mapComp g h ≫ mapComp f (g ≫ h)  [默认: by cat_disch]
    - map₂_leftUnitor : 对任意 {a b : B} (f : a ⟶ b), map₂ (fun_ f).inv = (fun_ (map f)).inv ≫ mapId a ▷ map f ≫ mapComp (𝟙 a) f  [默认: by cat_disch]
    - map₂_rightUnitor : 对任意 {a b : B} (f : a ⟶ b), map₂ (ρ_ f).inv = (ρ_ (map f)).inv ≫ map f ◁ mapId b ≫ mapComp f (𝟙 b)  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure LaxFunctor (B : Type u₁) [Bicategory.{w₁, v₁} B] (C : Type u₂) [Bicategory.{w₂, v₂} C]
    extends PrelaxFunctor B C where
  /-- The 2-morphism underlying the lax unity constraint. -/
  mapId (a : B) : 𝟙 (obj a) ⟶ map (𝟙 a)
  /-- The 2-morphism underlying the lax functoriality constraint. -/
  mapComp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) : map f ≫ map g ⟶ map (f ≫ g)
  /-- Naturality of the lax functoriality constraint, on the left. -/
  mapComp_naturality_left :
    forall {a b c : B} {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c),
      mapComp f g ≫ map₂ (η ▷ g) = map₂ η ▷ map g ≫ mapComp f' g := by cat_disch
  /-- Naturality of the lax functoriality constraint, on the right. -/
  mapComp_naturality_right :
    forall {a b c : B} (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g'),
     mapComp f g ≫ map₂ (f ◁ η) = map f ◁ map₂ η ≫ mapComp f g' := by cat_disch
  /-- Lax associativity. -/
  map₂_associator :
    forall {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d),
      mapComp f g ▷ map h ≫ mapComp (f ≫ g) h ≫ map₂ (α_ f g h).hom =
      (α_ (map f) (map g) (map h)).hom ≫ map f ◁ mapComp g h ≫ mapComp f (g ≫ h) := by cat_disch
  /-- Lax left unity. -/
  map₂_leftUnitor :
    forall {a b : B} (f : a ⟶ b),
      map₂ (fun_ f).inv = (fun_ (map f)).inv ≫ mapId a ▷ map f ≫ mapComp (𝟙 a) f := by cat_disch
  /-- Lax right unity. -/
  map₂_rightUnitor :
    forall {a b : B} (f : a ⟶ b),
      map₂ (ρ_ f).inv = (ρ_ (map f)).inv ≫ map f ◁ mapId b ≫ mapComp f (𝟙 b) := by cat_disch

/-- Notation for a lax functor between bicategories. -/
-- Given similar precedence as ⥤ (26).
scoped[CategoryTheory.Bicategory] infixr:26 " ⥤ᴸ " => LaxFunctor -- type as \func\^L

initialize_simps_projections LaxFunctor (+toPrelaxFunctor, -obj, -map, -map₂)

namespace LaxFunctor

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]

attribute [to_app (attr := reassoc (attr := simp))]
  mapComp_naturality_left mapComp_naturality_right map₂_associator
#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
attribute [simp, to_app (attr := reassoc)] map₂_leftUnitor map₂_rightUnitor

/-- The underlying prelax functor. -/
add_decl_doc LaxFunctor.toPrelaxFunctor

variable (F : B ⥤ᴸ C)

@[to_app (attr := reassoc)]
/--
lemma `mapComp_assoc_left` / 引理 `mapComp_assoc_left`

English:
lemma mapComp_assoc_left
  given: {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d)
  proof: by
  rw [← F.map₂_associator_assoc]; rw [← F.map₂_comp]
  simp only [Iso.hom_inv_id, PrelaxFunctor.map₂_id, comp_id]

@[to_app (attr := reassoc)]

中文:
引理 mapComp_assoc_left
  条件: {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d)
  证明: by
  rw [← F.map₂_associator_assoc]; rw [← F.map₂_comp]
  simp only [Iso.hom_inv_id, PrelaxFunctor.map₂_id, comp_id]

@[to_app (attr := reassoc)]

Depends on / 依赖: F.map, Iso.hom_inv_id, PrelaxFunctor, PrelaxFunctor.map, comp_id, hom_inv_id
-/
lemma mapComp_assoc_left {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    F.mapComp f g ▷ F.map h ≫ F.mapComp (f ≫ g) h = (α_ (F.map f) (F.map g) (F.map h)).hom ≫
      F.map f ◁ F.mapComp g h ≫ F.mapComp f (g ≫ h) ≫ F.map₂ (α_ f g h).inv := by
  rw [← F.map₂_associator_assoc]; rw [← F.map₂_comp]
  simp only [Iso.hom_inv_id, PrelaxFunctor.map₂_id, comp_id]

@[to_app (attr := reassoc)]
/--
lemma `mapComp_assoc_right` / 引理 `mapComp_assoc_right`

English:
lemma mapComp_assoc_right
  given: {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d)
  proof: by
  simp only [map₂_associator, Iso.inv_hom_id_assoc]

#adaptation_note

中文:
引理 mapComp_assoc_right
  条件: {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d)
  证明: by
  simp only [map₂_associator, Iso.inv_hom_id_assoc]

#adaptation_note

Depends on / 依赖: Iso.inv_hom_id_assoc, inv_hom_id_assoc
-/
lemma mapComp_assoc_right {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    F.map f ◁ F.mapComp g h ≫ F.mapComp f (g ≫ h) =
      (α_ (F.map f) (F.map g) (F.map h)).inv ≫ F.mapComp f g ▷ F.map h ≫
        F.mapComp (f ≫ g) h ≫ F.map₂ (α_ f g h).hom := by
  simp only [map₂_associator, Iso.inv_hom_id_assoc]

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[to_app (attr := reassoc)]
/--
lemma `map₂_leftUnitor_hom` / 引理 `map₂_leftUnitor_hom`

English:
lemma map₂_leftUnitor_hom
  given: {a b : B} (f : a ⟶ b)
  proof: by
  rw [← PrelaxFunctor.map₂Iso_hom]; rw [← assoc]; rw [← Iso.comp_inv_eq]; rw [← Iso.eq_inv_comp]
  simp only [Functor.mapIso_inv, PrelaxFunctor.mapFunctor_map, map₂_leftUnitor]

#adaptation_note

中文:
引理 map₂_leftUnitor_hom
  条件: {a b : B} (f : a ⟶ b)
  证明: by
  rw [← PrelaxFunctor.map₂Iso_hom]; rw [← assoc]; rw [← Iso.comp_inv_eq]; rw [← Iso.eq_inv_comp]
  simp only [Functor.mapIso_inv, PrelaxFunctor.mapFunctor_map, map₂_leftUnitor]

#adaptation_note

Depends on / 依赖: Functor, Functor.mapIso_inv, Iso.comp_inv_eq, Iso.eq_inv_comp, PrelaxFunctor, PrelaxFunctor.map, PrelaxFunctor.mapFunctor_map, comp_inv_eq, eq_inv_comp, mapFunctor_map, mapIso_inv
-/
lemma map₂_leftUnitor_hom {a b : B} (f : a ⟶ b) :
    (fun_ (F.map f)).hom = F.mapId a ▷ F.map f ≫ F.mapComp (𝟙 a) f ≫ F.map₂ (fun_ f).hom := by
  rw [← PrelaxFunctor.map₂Iso_hom]; rw [← assoc]; rw [← Iso.comp_inv_eq]; rw [← Iso.eq_inv_comp]
  simp only [Functor.mapIso_inv, PrelaxFunctor.mapFunctor_map, map₂_leftUnitor]

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[to_app (attr := reassoc)]
/--
lemma `map₂_rightUnitor_hom` / 引理 `map₂_rightUnitor_hom`

English:
lemma map₂_rightUnitor_hom
  given: {a b : B} (f : a ⟶ b)
  proof: by
  rw [← PrelaxFunctor.map₂Iso_hom]; rw [← assoc]; rw [← Iso.comp_inv_eq]; rw [← Iso.eq_inv_comp]
  simp only [Functor.mapIso_inv, PrelaxFunctor.mapFunctor_map, map₂_rightUnitor]

中文:
引理 map₂_rightUnitor_hom
  条件: {a b : B} (f : a ⟶ b)
  证明: by
  rw [← PrelaxFunctor.map₂Iso_hom]; rw [← assoc]; rw [← Iso.comp_inv_eq]; rw [← Iso.eq_inv_comp]
  simp only [Functor.mapIso_inv, PrelaxFunctor.mapFunctor_map, map₂_rightUnitor]

Depends on / 依赖: Functor, Functor.mapIso_inv, Iso.comp_inv_eq, Iso.eq_inv_comp, PrelaxFunctor, PrelaxFunctor.map, PrelaxFunctor.mapFunctor_map, comp_inv_eq, eq_inv_comp, mapFunctor_map, mapIso_inv
-/
lemma map₂_rightUnitor_hom {a b : B} (f : a ⟶ b) :
    (ρ_ (F.map f)).hom = F.map f ◁ F.mapId b ≫ F.mapComp f (𝟙 b) ≫ F.map₂ (ρ_ f).hom := by
  rw [← PrelaxFunctor.map₂Iso_hom]; rw [← assoc]; rw [← Iso.comp_inv_eq]; rw [← Iso.eq_inv_comp]
  simp only [Functor.mapIso_inv, PrelaxFunctor.mapFunctor_map, map₂_rightUnitor]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The identity lax functor. -/
@[simps]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: (B : Type u₁) [Bicategory.{w₁, v₁} B]
  body: PrelaxFunctor.id B
  mapId := fun a => 𝟙 (𝟙 a)
  mapComp := fun f g => 𝟙 (f ≫ g)

中文:
定义 id
  签名: (B : 类型u₁) [双范畴.{w₁, v₁} B]
  定义体: PrelaxFunctor.id B
  mapId := fun a => 𝟙 (𝟙 a)
  mapComp := fun f g => 𝟙 (f ≫ g)

Depends on / 依赖: PrelaxFunctor, PrelaxFunctor.id
-/
def id (B : Type u₁) [Bicategory.{w₁, v₁} B] : B ⥤ᴸ B where
  toPrelaxFunctor := PrelaxFunctor.id B
  mapId := fun a => 𝟙 (𝟙 a)
  mapComp := fun f g => 𝟙 (f ≫ g)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (B ⥤ᴸ B)
  body: ⟨id B⟩

中文:
实例 :
  签名: 可居 (B ⥤ᴸ B)
  定义体: ⟨id B⟩
-/
instance : Inhabited (B ⥤ᴸ B) :=
  ⟨id B⟩

/--
Definition of `mapId'` / `mapId'` 的定义

English:
definition mapId'
  signature: {b : B} (f : b ⟶ b) (hf : f = 𝟙 b := by cat_disch)
  body: F.mapId _ ≫ F.map₂ (eqToHom (by rw [hf]))

中文:
定义 mapId'
  签名: {b : B} (f : b ⟶ b) (hf : f = 𝟙 b := by cat_disch)
  定义体: F.mapId _ ≫ F.map₂ (eqToHom (by rw [hf]))

Depends on / 依赖: F.map, F.mapId, F.obj, cat_disch, eqToHom
-/
def mapId' {b : B} (f : b ⟶ b) (hf : f = 𝟙 b := by cat_disch) :
    𝟙 (F.obj b) ⟶ F.map f :=
  F.mapId _ ≫ F.map₂ (eqToHom (by rw [hf]))

/--
lemma `mapId'_eq_mapId` / 引理 `mapId'_eq_mapId`

English:
lemma mapId'_eq_mapId
  given: (b : B)
  proof: by
  simp [mapId']

中文:
引理 mapId'_eq_mapId
  条件: (b : B)
  证明: by
  simp [mapId']
-/
lemma mapId'_eq_mapId (b : B) :
    F.mapId' (𝟙 b) rfl = F.mapId b := by
  simp [mapId']

/--
Definition of `mapComp'` / `mapComp'` 的定义

English:
definition mapComp'
  signature: {b₀ b₁ b₂ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (fg : b₀ ⟶ b₂)
  body: F.mapComp f g ≫ F.map₂ (eqToHom (by rw [h]))

中文:
定义 mapComp'
  签名: {b₀ b₁ b₂ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (fg : b₀ ⟶ b₂)
  定义体: F.mapComp f g ≫ F.map₂ (eqToHom (by rw [h]))

Depends on / 依赖: F.map, F.mapComp, cat_disch, eqToHom, mapComp
-/
def mapComp' {b₀ b₁ b₂ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (fg : b₀ ⟶ b₂)
    (h : f ≫ g = fg := by cat_disch) :
    F.map f ≫ F.map g ⟶ F.map fg :=
  F.mapComp f g ≫ F.map₂ (eqToHom (by rw [h]))

/--
lemma `mapComp'_eq_mapComp` / 引理 `mapComp'_eq_mapComp`

English:
lemma mapComp'_eq_mapComp
  given: {b₀ b₁ b₂ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂)
  proof: by
  simp [mapComp']

中文:
引理 mapComp'_eq_mapComp
  条件: {b₀ b₁ b₂ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂)
  证明: by
  simp [mapComp']
-/
lemma mapComp'_eq_mapComp {b₀ b₁ b₂ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) :
    F.mapComp' f g _ rfl = F.mapComp f g := by
  simp [mapComp']

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Composition of lax functors. -/
@[simps]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: {D : Type u₃} [Bicategory.{w₃, v₃} D] (F : B ⥤ᴸ C) (G : C ⥤ᴸ D)
  body: PrelaxFunctor.comp F.toPrelaxFunctor G.toPrelaxFunctor
  mapId := fun a => G.mapId (F.obj a) ≫ G.map₂ (F.mapId a)
  mapComp := fun f g => G.mapComp (F.map f) (F.map g) ≫ G.map₂ (F.mapComp f g)
  mapComp_naturality_left := fun η g => by
    dsimp
    rw [assoc]; rw [← G.map₂_comp]; rw [mapComp_natura

中文:
定义 comp
  签名: {D : 类型u₃} [双范畴.{w₃, v₃} D] (F : B ⥤ᴸ C) (G : C ⥤ᴸ D)
  定义体: PrelaxFunctor.comp F.toPrelaxFunctor G.toPrelaxFunctor
  mapId := fun a => G.mapId (F.obj a) ≫ G.map₂ (F.mapId a)
  mapComp := fun f g => G.mapComp (F.map f) (F.map g) ≫ G.map₂ (F.mapComp f g)
  mapComp_naturality_left := fun η g => by
    dsimp
    rw [assoc]; rw [← G.map₂_comp]; rw [mapComp_natura

Depends on / 依赖: F.toPrelaxFunctor, G.toPrelaxFunctor, PrelaxFunctor, PrelaxFunctor.comp, toPrelaxFunctor
-/
def comp {D : Type u₃} [Bicategory.{w₃, v₃} D] (F : B ⥤ᴸ C) (G : C ⥤ᴸ D) :
    B ⥤ᴸ D where
  toPrelaxFunctor := PrelaxFunctor.comp F.toPrelaxFunctor G.toPrelaxFunctor
  mapId := fun a => G.mapId (F.obj a) ≫ G.map₂ (F.mapId a)
  mapComp := fun f g => G.mapComp (F.map f) (F.map g) ≫ G.map₂ (F.mapComp f g)
  mapComp_naturality_left := fun η g => by
    dsimp
    rw [assoc]; rw [← G.map₂_comp]; rw [mapComp_naturality_left]; rw [G.map₂_comp]; rw [mapComp_naturality_left_assoc]
  mapComp_naturality_right := fun f _ _ η => by
    dsimp
    rw [assoc]; rw [← G.map₂_comp]; rw [mapComp_naturality_right]; rw [G.map₂_comp]; rw [mapComp_naturality_right_assoc]
  map₂_associator := fun f g h => by
    dsimp
    slice_rhs 1 3 =>
      rw [Bicategory.whiskerLeft_comp]; rw [assoc]; rw [← mapComp_naturality_right]; rw [← map₂_associator_assoc]
    slice_rhs 3 5 =>
      rw [← G.map₂_comp]; rw [← G.map₂_comp]; rw [← F.map₂_associator]; rw [G.map₂_comp]; rw [G.map₂_comp]
    slice_lhs 1 3 =>
      rw [comp_whiskerRight]; rw [assoc]; rw [← G.mapComp_naturality_left_assoc]
    simp only [assoc]
  map₂_leftUnitor := fun f => by
    dsimp
    simp only [map₂_leftUnitor, PrelaxFunctor.map₂_comp, assoc, mapComp_naturality_left_assoc,
      comp_whiskerRight]
  map₂_rightUnitor := fun f => by
    dsimp
    simp only [map₂_rightUnitor, PrelaxFunctor.map₂_comp, assoc, mapComp_naturality_right_assoc,
      Bicategory.whiskerLeft_comp]

/--
Definition of `PseudoCore` / `PseudoCore` 的定义

English:
structure PseudoCore
  parameters: (F : B ⥤ᴸ C)
  axioms and operations (4):
    - mapIdIso((a : B)) : F.map (𝟙 a) ≅ 𝟙 (F.obj a)
    - mapCompIso({a b c : B} (f : a ⟶ b) (g : b ⟶ c)) : F.map (f ≫ g) ≅ F.map f ≫ F.map g
    - mapIdIso_inv({a : B}) : (mapIdIso a).inv = F.mapId a  [default: by cat_disch]
    - mapCompIso_inv({a b c : B} (f : a ⟶ b) (g : b ⟶ c)) : (mapCompIso f g).inv = F.mapComp f g  [default: by cat_disch]

中文:
结构 PseudoCore
  参数: (F : B ⥤ᴸ C)
  公理与运算 (4 个):
    - mapIdIso((a : B)) : F.map (𝟙 a) ≅ 𝟙 (F.obj a)
    - mapCompIso({a b c : B} (f : a ⟶ b) (g : b ⟶ c)) : F.map (f ≫ g) ≅ F.map f ≫ F.map g
    - mapIdIso_inv({a : B}) : (mapIdIso a).inv = F.mapId a  [默认: by cat_disch]
    - mapCompIso_inv({a b c : B} (f : a ⟶ b) (g : b ⟶ c)) : (mapCompIso f g).inv = F.mapComp f g  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure PseudoCore (F : B ⥤ᴸ C) where
  /-- The isomorphism giving rise to the lax unity constraint -/
  mapIdIso (a : B) : F.map (𝟙 a) ≅ 𝟙 (F.obj a)
  /-- The isomorphism giving rise to the lax functoriality constraint -/
  mapCompIso {a b c : B} (f : a ⟶ b) (g : b ⟶ c) : F.map (f ≫ g) ≅ F.map f ≫ F.map g
  /-- `mapIdIso` gives rise to the lax unity constraint -/
  mapIdIso_inv {a : B} : (mapIdIso a).inv = F.mapId a := by cat_disch
  /-- `mapCompIso` gives rise to the lax functoriality constraint -/
  mapCompIso_inv {a b c : B} (f : a ⟶ b) (g : b ⟶ c) : (mapCompIso f g).inv = F.mapComp f g := by
    cat_disch

attribute [simp] PseudoCore.mapIdIso_inv PseudoCore.mapCompIso_inv

end LaxFunctor

end CategoryTheory
