/-
Copyright (c) 2022 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module

public import Mathlib.CategoryTheory.Bicategory.Functor.Prelax
public import Mathlib.Tactic.CategoryTheory.ToApp

/-!
# Oplax functors

An oplax functor `F` between bicategories `B` and `C` consists of
* a function between objects `F.obj : B → C`,
* a family of functions between 1-morphisms `F.map : (a ⟶ b) → (F.obj a ⟶ F.obj b)`,
* a family of functions between 2-morphisms `F.map₂ : (f ⟶ g) → (F.map f ⟶ F.map g)`,
* a family of 2-morphisms `F.mapId a : F.map (𝟙 a) ⟶ 𝟙 (F.obj a)`,
* a family of 2-morphisms `F.mapComp f g : F.map (f ≫ g) ⟶ F.map f ≫ F.map g`, and
* certain consistency conditions on them.

## Main definitions

* `CategoryTheory.OplaxFunctor B C` : an oplax functor between bicategories `B` and `C`, which we
  denote by `B ⥤ᵒᵖᴸ C`.
* `CategoryTheory.OplaxFunctor.comp F G` : the composition of oplax functors

-/

@[expose] public section

namespace CategoryTheory

open Category Bicategory

open Bicategory

universe w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃

section

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]
variable {D : Type u₃} [Bicategory.{w₃, v₃} D]

/--
Definition of `OplaxFunctor` / `OplaxFunctor` 的定义

English:
structure OplaxFunctor
  parameters: (B : Type u₁) [Bicategory.{w₁, v₁} B] (C : Type u₂)
  extends: PrelaxFunctor B C
  axioms and operations (7):
    - mapId((a : B)) : map (𝟙 a) ⟶ 𝟙 (obj a)
    - mapComp({a b c : B} (f : a ⟶ b) (g : b ⟶ c)) : map (f ≫ g) ⟶ map f ≫ map g
    - mapComp_naturality_left : forall {a b c : B} {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c), map₂ (η ▷ g) ≫ mapComp f' g = mapComp f g ≫ map₂ η ▷ map g  [default: by cat_disch]
    - mapComp_naturality_right : forall {a b c : B} (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g'), map₂ (f ◁ η) ≫ mapComp f g' = mapComp f g ≫ map f ◁ map₂ η  [default: by cat_disch]
    - map₂_associator : forall {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d), map₂ (α_ f g h).hom ≫ mapComp f (g ≫ h) ≫ map f ◁ mapComp g h = mapComp (f ≫ g) h ≫ mapComp f g ▷ map h ≫ (α_ (map f) (map g) (map h)).hom  [default: by cat_disch]
    - map₂_leftUnitor : forall {a b : B} (f : a ⟶ b), map₂ (fun_ f).hom = mapComp (𝟙 a) f ≫ mapId a ▷ map f ≫ (fun_ (map f)).hom  [default: by cat_disch]
    - map₂_rightUnitor : forall {a b : B} (f : a ⟶ b), map₂ (ρ_ f).hom = mapComp f (𝟙 b) ≫ map f ◁ mapId b ≫ (ρ_ (map f)).hom  [default: by cat_disch]

中文:
结构 Oplax函子
  参数: (B : 类型u₁) [双范畴.{w₁, v₁} B] (C : 类型u₂)
  继承: 预松弛函子 B C
  公理与运算 (7 个):
    - mapId((a : B)) : map (𝟙 a) ⟶ 𝟙 (obj a)
    - mapComp({a b c : B} (f : a ⟶ b) (g : b ⟶ c)) : map (f ≫ g) ⟶ map f ≫ map g
    - mapComp_naturality_left : 对任意 {a b c : B} {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c), map₂ (η ▷ g) ≫ mapComp f' g = mapComp f g ≫ map₂ η ▷ map g  [默认: by cat_disch]
    - mapComp_naturality_right : 对任意 {a b c : B} (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g'), map₂ (f ◁ η) ≫ mapComp f g' = mapComp f g ≫ map f ◁ map₂ η  [默认: by cat_disch]
    - map₂_associator : 对任意 {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d), map₂ (α_ f g h).hom ≫ mapComp f (g ≫ h) ≫ map f ◁ mapComp g h = mapComp (f ≫ g) h ≫ mapComp f g ▷ map h ≫ (α_ (map f) (map g) (map h)).hom  [默认: by cat_disch]
    - map₂_leftUnitor : 对任意 {a b : B} (f : a ⟶ b), map₂ (fun_ f).hom = mapComp (𝟙 a) f ≫ mapId a ▷ map f ≫ (fun_ (map f)).hom  [默认: by cat_disch]
    - map₂_rightUnitor : 对任意 {a b : B} (f : a ⟶ b), map₂ (ρ_ f).hom = mapComp f (𝟙 b) ≫ map f ◁ mapId b ≫ (ρ_ (map f)).hom  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure OplaxFunctor (B : Type u₁) [Bicategory.{w₁, v₁} B] (C : Type u₂)
  [Bicategory.{w₂, v₂} C] extends PrelaxFunctor B C where
  /-- The 2-morphism underlying the oplax unity constraint. -/
  mapId (a : B) : map (𝟙 a) ⟶ 𝟙 (obj a)
  /-- The 2-morphism underlying the oplax functoriality constraint. -/
  mapComp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) : map (f ≫ g) ⟶ map f ≫ map g
  /-- Naturality of the oplax functoriality constraint, on the left. -/
  mapComp_naturality_left :
    forall {a b c : B} {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c),
      map₂ (η ▷ g) ≫ mapComp f' g = mapComp f g ≫ map₂ η ▷ map g := by
    cat_disch
  /-- Naturality of the oplax functoriality constraint, on the right. -/
  mapComp_naturality_right :
    forall {a b c : B} (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g'),
      map₂ (f ◁ η) ≫ mapComp f g' = mapComp f g ≫ map f ◁ map₂ η := by
    cat_disch
  /-- Oplax associativity. -/
  map₂_associator :
    forall {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d),
      map₂ (α_ f g h).hom ≫ mapComp f (g ≫ h) ≫ map f ◁ mapComp g h =
      mapComp (f ≫ g) h ≫ mapComp f g ▷ map h ≫ (α_ (map f) (map g) (map h)).hom := by
    cat_disch
  /-- Oplax left unity. -/
  map₂_leftUnitor :
    forall {a b : B} (f : a ⟶ b),
      map₂ (fun_ f).hom = mapComp (𝟙 a) f ≫ mapId a ▷ map f ≫ (fun_ (map f)).hom := by
    cat_disch
  /-- Oplax right unity. -/
  map₂_rightUnitor :
    forall {a b : B} (f : a ⟶ b),
      map₂ (ρ_ f).hom = mapComp f (𝟙 b) ≫ map f ◁ mapId b ≫ (ρ_ (map f)).hom := by
    cat_disch

/-- Notation for an oplax functor between bicategories. -/
-- Given similar precedence as ⥤ (26).
scoped[CategoryTheory.Bicategory] infixr:26 " ⥤ᵒᵖᴸ " => OplaxFunctor -- type as \func\op\^L

initialize_simps_projections OplaxFunctor (+toPrelaxFunctor, -obj, -map, -map₂)

namespace OplaxFunctor

attribute [to_app (attr := reassoc (attr := simp))]
  mapComp_naturality_left mapComp_naturality_right map₂_associator
#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
attribute [simp, to_app (attr := reassoc)] map₂_leftUnitor map₂_rightUnitor

section

/-- The underlying prelax functor. -/
add_decl_doc OplaxFunctor.toPrelaxFunctor

variable (F : B ⥤ᵒᵖᴸ C)

@[to_app (attr := reassoc)]
/--
lemma `mapComp_assoc_right` / 引理 `mapComp_assoc_right`

English:
lemma mapComp_assoc_right
  given: {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d)
  proof: by
  rw [← F.map₂_associator]; rw [← F.map₂_comp_assoc]
  simp

@[to_app (attr := reassoc)]

中文:
引理 mapComp_assoc_right
  条件: {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d)
  证明: by
  rw [← F.map₂_associator]; rw [← F.map₂_comp_assoc]
  simp

@[to_app (attr := reassoc)]

Depends on / 依赖: F.map
-/
lemma mapComp_assoc_right {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    F.mapComp f (g ≫ h) ≫ F.map f ◁ F.mapComp g h = F.map₂ (α_ f g h).inv ≫
    F.mapComp (f ≫ g) h ≫ F.mapComp f g ▷ F.map h ≫
    (α_ (F.map f) (F.map g) (F.map h)).hom := by
  rw [← F.map₂_associator]; rw [← F.map₂_comp_assoc]
  simp

@[to_app (attr := reassoc)]
/--
lemma `mapComp_assoc_left` / 引理 `mapComp_assoc_left`

English:
lemma mapComp_assoc_left
  given: {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d)
  proof: by
  simp

@[reassoc]

中文:
引理 mapComp_assoc_left
  条件: {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d)
  证明: by
  simp

@[reassoc]
-/
lemma mapComp_assoc_left {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    F.mapComp (f ≫ g) h ≫ F.mapComp f g ▷ F.map h =
    F.map₂ (α_ f g h).hom ≫ F.mapComp f (g ≫ h) ≫ F.map f ◁ F.mapComp g h
    ≫ (α_ (F.map f) (F.map g) (F.map h)).inv := by
  simp

@[reassoc]
/--
theorem `mapComp_id_left` / 定理 `mapComp_id_left`

English:
theorem mapComp_id_left
  given: {a b : B} (f : a ⟶ b)
  proof: by
  rw [Iso.eq_comp_inv]
  simp only [Category.assoc]
  rw [← F.map₂_leftUnitor]

@[reassoc]

中文:
定理 mapComp_id_left
  条件: {a b : B} (f : a ⟶ b)
  证明: by
  rw [Iso.eq_comp_inv]
  simp only [Category.assoc]
  rw [← F.map₂_leftUnitor]

@[reassoc]

Depends on / 依赖: Category, Category.assoc, F.map, Iso.eq_comp_inv, eq_comp_inv
-/
theorem mapComp_id_left {a b : B} (f : a ⟶ b) :
    F.mapComp (𝟙 a) f ≫ F.mapId a ▷ F.map f = F.map₂ (fun_ f).hom ≫ (fun_ (F.map f)).inv := by
  rw [Iso.eq_comp_inv]
  simp only [Category.assoc]
  rw [← F.map₂_leftUnitor]

@[reassoc]
/--
theorem `mapComp_id_right` / 定理 `mapComp_id_right`

English:
theorem mapComp_id_right
  given: {a b : B} (f : a ⟶ b)
  proof: by
  rw [Iso.eq_comp_inv]
  simp only [Category.assoc]
  rw [← F.map₂_rightUnitor]

中文:
定理 mapComp_id_right
  条件: {a b : B} (f : a ⟶ b)
  证明: by
  rw [Iso.eq_comp_inv]
  simp only [Category.assoc]
  rw [← F.map₂_rightUnitor]

Depends on / 依赖: Category, Category.assoc, F.map, Iso.eq_comp_inv, eq_comp_inv
-/
theorem mapComp_id_right {a b : B} (f : a ⟶ b) :
    F.mapComp f (𝟙 b) ≫ F.map f ◁ F.mapId b = F.map₂ (ρ_ f).hom ≫ (ρ_ (F.map f)).inv := by
  rw [Iso.eq_comp_inv]
  simp only [Category.assoc]
  rw [← F.map₂_rightUnitor]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The identity oplax functor. -/
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
def id (B : Type u₁) [Bicategory.{w₁, v₁} B] : B ⥤ᵒᵖᴸ B where
  toPrelaxFunctor := PrelaxFunctor.id B
  mapId := fun a => 𝟙 (𝟙 a)
  mapComp := fun f g => 𝟙 (f ≫ g)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (B ⥤ᵒᵖᴸ B)
  body: ⟨id B⟩

中文:
实例 :
  签名: 可居 (B ⥤ᵒᵖᴸ B)
  定义体: ⟨id B⟩
-/
instance : Inhabited (B ⥤ᵒᵖᴸ B) :=
  ⟨id B⟩

/--
Definition of `mapId'` / `mapId'` 的定义

English:
definition mapId'
  signature: {b : B} (f : b ⟶ b) (hf : f = 𝟙 b := by cat_disch)
  body: F.map₂ (eqToHom (by rw [hf])) ≫ F.mapId _

中文:
定义 mapId'
  签名: {b : B} (f : b ⟶ b) (hf : f = 𝟙 b := by cat_disch)
  定义体: F.map₂ (eqToHom (by rw [hf])) ≫ F.mapId _

Depends on / 依赖: F.map, F.mapId, F.obj, cat_disch, eqToHom
-/
def mapId' {b : B} (f : b ⟶ b) (hf : f = 𝟙 b := by cat_disch) :
    F.map f ⟶ 𝟙 (F.obj b) :=
  F.map₂ (eqToHom (by rw [hf])) ≫ F.mapId _

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
  body: F.map₂ (eqToHom (by rw [h])) ≫ F.mapComp f g

中文:
定义 mapComp'
  签名: {b₀ b₁ b₂ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (fg : b₀ ⟶ b₂)
  定义体: F.map₂ (eqToHom (by rw [h])) ≫ F.mapComp f g

Depends on / 依赖: F.map, F.mapComp, cat_disch, eqToHom, mapComp
-/
def mapComp' {b₀ b₁ b₂ : B} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (fg : b₀ ⟶ b₂)
    (h : f ≫ g = fg := by cat_disch) :
    F.map fg ⟶ F.map f ≫ F.map g :=
  F.map₂ (eqToHom (by rw [h])) ≫ F.mapComp f g

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
--@[simps]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (F : B ⥤ᵒᵖᴸ C) (G : C ⥤ᵒᵖᴸ D)
  body: F.toPrelaxFunctor.comp G.toPrelaxFunctor
  mapId := fun a => (G.mapFunctor _ _).map (F.mapId a) ≫ G.mapId (F.obj a)
  mapComp := fun f g => (G.mapFunctor _ _).map (F.mapComp f g) ≫ G.mapComp (F.map f) (F.map g)
  mapComp_naturality_left := fun η g => by
    dsimp
    rw [← G.map₂_comp_assoc]; rw [ma

中文:
定义 comp
  签名: (F : B ⥤ᵒᵖᴸ C) (G : C ⥤ᵒᵖᴸ D)
  定义体: F.toPrelaxFunctor.comp G.toPrelaxFunctor
  mapId := fun a => (G.mapFunctor _ _).map (F.mapId a) ≫ G.mapId (F.obj a)
  mapComp := fun f g => (G.mapFunctor _ _).map (F.mapComp f g) ≫ G.mapComp (F.map f) (F.map g)
  mapComp_naturality_left := fun η g => by
    dsimp
    rw [← G.map₂_comp_assoc]; rw [ma

Depends on / 依赖: F.toPrelaxFunctor.comp, G.toPrelaxFunctor, toPrelaxFunctor
-/
def comp (F : B ⥤ᵒᵖᴸ C) (G : C ⥤ᵒᵖᴸ D) : B ⥤ᵒᵖᴸ D where
  toPrelaxFunctor := F.toPrelaxFunctor.comp G.toPrelaxFunctor
  mapId := fun a => (G.mapFunctor _ _).map (F.mapId a) ≫ G.mapId (F.obj a)
  mapComp := fun f g => (G.mapFunctor _ _).map (F.mapComp f g) ≫ G.mapComp (F.map f) (F.map g)
  mapComp_naturality_left := fun η g => by
    dsimp
    rw [← G.map₂_comp_assoc]; rw [mapComp_naturality_left]; rw [G.map₂_comp_assoc]; rw [mapComp_naturality_left]; rw [assoc]
  mapComp_naturality_right := fun η => by
    dsimp
    intros
    rw [← G.map₂_comp_assoc]; rw [mapComp_naturality_right]; rw [G.map₂_comp_assoc]; rw [mapComp_naturality_right]; rw [assoc]
  map₂_associator := fun f g h => by
    dsimp
    simp only [map₂_associator, ← PrelaxFunctor.map₂_comp_assoc, ← mapComp_naturality_right_assoc,
      whiskerLeft_comp, assoc]
    simp only [map₂_associator, PrelaxFunctor.map₂_comp, mapComp_naturality_left_assoc,
      comp_whiskerRight, assoc]
  map₂_leftUnitor := fun f => by
    dsimp
    simp only [map₂_leftUnitor, PrelaxFunctor.map₂_comp, mapComp_naturality_left_assoc,
      comp_whiskerRight, assoc]
  map₂_rightUnitor := fun f => by
    dsimp
    simp only [map₂_rightUnitor, PrelaxFunctor.map₂_comp, mapComp_naturality_right_assoc,
      whiskerLeft_comp, assoc]

/--
Definition of `PseudoCore` / `PseudoCore` 的定义

English:
structure PseudoCore
  parameters: (F : B ⥤ᵒᵖᴸ C)
  axioms and operations (4):
    - mapIdIso((a : B)) : F.map (𝟙 a) ≅ 𝟙 (F.obj a)
    - mapCompIso({a b c : B} (f : a ⟶ b) (g : b ⟶ c)) : F.map (f ≫ g) ≅ F.map f ≫ F.map g
    - mapIdIso_hom : forall {a : B}, (mapIdIso a).hom = F.mapId a  [default: by cat_disch]
    - mapCompIso_hom : forall {a b c : B} (f : a ⟶ b) (g : b ⟶ c), (mapCompIso f g).hom = F.mapComp f g  [default: by cat_disch]

中文:
结构 PseudoCore
  参数: (F : B ⥤ᵒᵖᴸ C)
  公理与运算 (4 个):
    - mapIdIso((a : B)) : F.map (𝟙 a) ≅ 𝟙 (F.obj a)
    - mapCompIso({a b c : B} (f : a ⟶ b) (g : b ⟶ c)) : F.map (f ≫ g) ≅ F.map f ≫ F.map g
    - mapIdIso_hom : 对任意 {a : B}, (mapIdIso a).hom = F.mapId a  [默认: by cat_disch]
    - mapCompIso_hom : 对任意 {a b c : B} (f : a ⟶ b) (g : b ⟶ c), (mapCompIso f g).hom = F.mapComp f g  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure PseudoCore (F : B ⥤ᵒᵖᴸ C) where
  /-- The isomorphism giving rise to the oplax unity constraint -/
  mapIdIso (a : B) : F.map (𝟙 a) ≅ 𝟙 (F.obj a)
  /-- The isomorphism giving rise to the oplax functoriality constraint -/
  mapCompIso {a b c : B} (f : a ⟶ b) (g : b ⟶ c) : F.map (f ≫ g) ≅ F.map f ≫ F.map g
  /-- `mapIdIso` gives rise to the oplax unity constraint -/
  mapIdIso_hom : forall {a : B}, (mapIdIso a).hom = F.mapId a := by cat_disch
  /-- `mapCompIso` gives rise to the oplax functoriality constraint -/
  mapCompIso_hom :
    forall {a b c : B} (f : a ⟶ b) (g : b ⟶ c), (mapCompIso f g).hom = F.mapComp f g := by cat_disch

attribute [simp] PseudoCore.mapIdIso_hom PseudoCore.mapCompIso_hom

end

end OplaxFunctor

end

end CategoryTheory
