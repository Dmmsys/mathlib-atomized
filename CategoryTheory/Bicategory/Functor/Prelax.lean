/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno, Calle Sönne
-/
module

public import Mathlib.CategoryTheory.Bicategory.Basic
public import Mathlib.CategoryTheory.EqToHom

/-!

# Prelax functors

This file defines lax prefunctors and prelax functors between bicategories. The point of these
definitions is to provide some common API that will be helpful in the development of both lax and
oplax functors.

## Main definitions

`PrelaxFunctorStruct B C`:

A PrelaxFunctorStruct `F` between quivers `B` and `C`, such that both have been equipped with quiver
structures on the hom-types, consists of
* a function between objects `F.obj : B → C`,
* a family of functions between 1-morphisms `F.map : (a ⟶ b) → (F.obj a ⟶ F.obj b)`,
* a family of functions between 2-morphisms `F.map₂ : (f ⟶ g) → (F.map f ⟶ F.map g)`,

`PrelaxFunctor B C`:

A prelax functor `F` between bicategories `B` and `C` is a `PrelaxFunctorStruct` such that the
associated prefunctors between the hom types are all functors. In other words, it is a
`PrelaxFunctorStruct` that satisfies
* `F.map₂ (𝟙 f) = 𝟙 (F.map f)`,
* `F.map₂ (η ≫ θ) = F.map₂ η ≫ F.map₂ θ`.

`mkOfHomFunctor`: constructs a `PrelaxFunctor` from a map on objects and functors between the
corresponding hom types.

-/

@[expose] public section

namespace CategoryTheory

open Category Bicategory

universe w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃

section

variable (B : Type u₁) [Quiver.{v₁} B] [forall a b : B, Quiver.{w₁} (a ⟶ b)]
variable (C : Type u₂) [Quiver.{v₂} C] [forall a b : C, Quiver.{w₂} (a ⟶ b)]
variable {D : Type u₃} [Quiver.{v₃} D] [forall a b : D, Quiver.{w₃} (a ⟶ b)]

/--
Definition of `PrelaxFunctorStruct` / `PrelaxFunctorStruct` 的定义

English:
structure PrelaxFunctorStruct
  parameters: extends Prefunctor B C
  extends: Prefunctor B C
  axioms and operations (1):
    - map₂({a b : B} {f g : a ⟶ b}) : (f ⟶ g) -> (map f ⟶ map g)

中文:
结构 PrelaxFunctorStruct
  参数: extends Prefunctor B C
  继承: Prefunctor B C
  公理与运算 (1 个):
    - map₂({a b : B} {f g : a ⟶ b}) : (f ⟶ g) -> (map f ⟶ map g)
-/
structure PrelaxFunctorStruct extends Prefunctor B C where
  /-- The action of a lax prefunctor on 2-morphisms. -/
  map₂ {a b : B} {f g : a ⟶ b} : (f ⟶ g) -> (map f ⟶ map g)

initialize_simps_projections PrelaxFunctorStruct (+toPrefunctor, -obj, -map)

/-- The prefunctor between the underlying quivers. -/
add_decl_doc PrelaxFunctorStruct.toPrefunctor

variable {B} {C}

namespace PrelaxFunctorStruct

/-- Construct a lax prefunctor from a map on objects, and prefunctors between the corresponding
hom types. -/
@[simps]
/--
Definition of `mkOfHomPrefunctors` / `mkOfHomPrefunctors` 的定义

English:
definition mkOfHomPrefunctors
  signature: (F : B -> C) (F' : (a : B) -> (b : B) -> Prefunctor (a ⟶ b) (F a ⟶ F b))
  body: F
  map {a b} := (F' a b).obj
  map₂ {a b} := (F' a b).map

中文:
定义 mkOfHomPrefunctors
  签名: (F : B -> C) (F' : (a : B) -> (b : B) -> Prefunctor (a ⟶ b) (F a ⟶ F b))
  定义体: F
  map {a b} := (F' a b).obj
  map₂ {a b} := (F' a b).map
-/
def mkOfHomPrefunctors (F : B -> C) (F' : (a : B) -> (b : B) -> Prefunctor (a ⟶ b) (F a ⟶ F b)) :
    PrelaxFunctorStruct B C where
  obj := F
  map {a b} := (F' a b).obj
  map₂ {a b} := (F' a b).map

/-- The identity lax prefunctor. -/
@[simps]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: (B : Type u₁) [Quiver.{v₁} B] [forall a b : B, Quiver.{w₁} (a ⟶ b)]
  body: { Prefunctor.id B with map₂ := fun η => η }

中文:
定义 id
  签名: (B : 类型u₁) [Quiver.{v₁} B] [对任意 a b : B, Quiver.{w₁} (a ⟶ b)]
  定义体: { Prefunctor.id B with map₂ := fun η => η }

Depends on / 依赖: Prefunctor, Prefunctor.id
-/
def id (B : Type u₁) [Quiver.{v₁} B] [forall a b : B, Quiver.{w₁} (a ⟶ b)] :
    PrelaxFunctorStruct B B :=
  { Prefunctor.id B with map₂ := fun η => η }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (PrelaxFunctorStruct B B)
  body: ⟨PrelaxFunctorStruct.id B⟩

中文:
实例 :
  签名: Inhabited (PrelaxFunctorStruct B B)
  定义体: ⟨PrelaxFunctorStruct.id B⟩

Depends on / 依赖: CostructuredArrow, CostructuredArrow.hasTerminal, PrelaxFunctorStruct, PrelaxFunctorStruct.id, hasTerminal
-/
instance : Inhabited (PrelaxFunctorStruct B B) :=
  ⟨PrelaxFunctorStruct.id B⟩

/-- Composition of lax prefunctors. -/
@[simps]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (F : PrelaxFunctorStruct B C) (G : PrelaxFunctorStruct C D)
  body: F.toPrefunctor.comp G.toPrefunctor
  map₂ := fun η => G.map₂ (F.map₂ η)

中文:
定义 comp
  签名: (F : PrelaxFunctorStruct B C) (G : PrelaxFunctorStruct C D)
  定义体: F.toPrefunctor.comp G.toPrefunctor
  map₂ := fun η => G.map₂ (F.map₂ η)

Depends on / 依赖: F.toPrefunctor.comp, G.toPrefunctor, Under.mkIdInitial.hasInitial, hasInitial, mkIdInitial, toPrefunctor
-/
def comp (F : PrelaxFunctorStruct B C) (G : PrelaxFunctorStruct C D) : PrelaxFunctorStruct B D where
  toPrefunctor := F.toPrefunctor.comp G.toPrefunctor
  map₂ := fun η => G.map₂ (F.map₂ η)

end PrelaxFunctorStruct

end

/--
Definition of `PrelaxFunctor` / `PrelaxFunctor` 的定义

English:
structure PrelaxFunctor
  parameters: (B : Type u₁) [Bicategory.{w₁, v₁} B] (C : Type u₂) [Bicategory.{w₂, v₂} C]
  extends: PrelaxFunctorStruct B C
  axioms and operations (2):
    - map₂_id : forall {a b : B} (f : a ⟶ b), map₂ (𝟙 f) = 𝟙 (map f)  [default: by aesop -- TODO: why not cat_disch?]
    - map₂_comp : forall {a b : B} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h), map₂ (η ≫ θ) = map₂ η ≫ map₂ θ  [default: by cat_disch]

中文:
结构 PrelaxFunctor
  参数: (B : 类型u₁) [Bicategory.{w₁, v₁} B] (C : 类型u₂) [Bicategory.{w₂, v₂} C]
  继承: PrelaxFunctorStruct B C
  公理与运算 (2 个):
    - map₂_id : 对任意 {a b : B} (f : a ⟶ b), map₂ (𝟙 f) = 𝟙 (map f)  [默认: by aesop -- TODO: why not cat_disch?]
    - map₂_comp : 对任意 {a b : B} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h), map₂ (η ≫ θ) = map₂ η ≫ map₂ θ  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure PrelaxFunctor (B : Type u₁) [Bicategory.{w₁, v₁} B] (C : Type u₂) [Bicategory.{w₂, v₂} C]
    extends PrelaxFunctorStruct B C where
  /-- Prelax functors preserve identity 2-morphisms. -/
  map₂_id : forall {a b : B} (f : a ⟶ b), map₂ (𝟙 f) = 𝟙 (map f) := by aesop -- TODO: why not cat_disch?
  /-- Prelax functors preserve compositions of 2-morphisms. -/
  map₂_comp : forall {a b : B} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h),
      map₂ (η ≫ θ) = map₂ η ≫ map₂ θ := by cat_disch

namespace PrelaxFunctor

initialize_simps_projections PrelaxFunctor (+toPrelaxFunctorStruct, -obj, -map, -map₂)

attribute [simp] map₂_id
attribute [reassoc] map₂_comp
attribute [simp] map₂_comp

/-- The underlying lax prefunctor. -/
add_decl_doc PrelaxFunctor.toPrelaxFunctorStruct

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C]
variable {D : Type u₃} [Bicategory.{w₃, v₃} D]

/-- Construct a prelax functor from a map on objects, and functors between the corresponding
hom types. -/
@[simps]
/--
Definition of `mkOfHomFunctors` / `mkOfHomFunctors` 的定义

English:
definition mkOfHomFunctors
  signature: (F : B -> C) (F' : (a : B) -> (b : B) -> (a ⟶ b) ⥤ (F a ⟶ F b))
  body: PrelaxFunctorStruct.mkOfHomPrefunctors F fun a b => (F' a b).toPrefunctor
  map₂_id {a b} := (F' a b).map_id
  map₂_comp {a b} := (F' a b).map_comp

中文:
定义 mkOfHomFunctors
  签名: (F : B -> C) (F' : (a : B) -> (b : B) -> (a ⟶ b) ⥤ (F a ⟶ F b))
  定义体: PrelaxFunctorStruct.mkOfHomPrefunctors F fun a b => (F' a b).toPrefunctor
  map₂_id {a b} := (F' a b).map_id
  map₂_comp {a b} := (F' a b).map_comp

Depends on / 依赖: PrelaxFunctorStruct, PrelaxFunctorStruct.mkOfHomPrefunctors, mkOfHomPrefunctors, toPrefunctor
-/
def mkOfHomFunctors (F : B -> C) (F' : (a : B) -> (b : B) -> (a ⟶ b) ⥤ (F a ⟶ F b)) :
    PrelaxFunctor B C where
  toPrelaxFunctorStruct := PrelaxFunctorStruct.mkOfHomPrefunctors F fun a b => (F' a b).toPrefunctor
  map₂_id {a b} := (F' a b).map_id
  map₂_comp {a b} := (F' a b).map_comp

/-- The identity prelax functor. -/
@[simps]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: (B : Type u₁) [Bicategory.{w₁, v₁} B]
  body: PrelaxFunctorStruct.id B

中文:
定义 id
  签名: (B : 类型u₁) [Bicategory.{w₁, v₁} B]
  定义体: PrelaxFunctorStruct.id B

Depends on / 依赖: PrelaxFunctorStruct, PrelaxFunctorStruct.id
-/
def id (B : Type u₁) [Bicategory.{w₁, v₁} B] : PrelaxFunctor B B where
  toPrelaxFunctorStruct := PrelaxFunctorStruct.id B

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (PrelaxFunctor B B)
  body: ⟨PrelaxFunctor.id B⟩

中文:
实例 :
  签名: Inhabited (PrelaxFunctor B B)
  定义体: ⟨PrelaxFunctor.id B⟩

Depends on / 依赖: PrelaxFunctor, PrelaxFunctor.id
-/
instance : Inhabited (PrelaxFunctor B B) :=
  ⟨PrelaxFunctor.id B⟩

variable (F : PrelaxFunctor B C)

/-- Composition of prelax functors. -/
@[simps]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (G : PrelaxFunctor C D)
  body: PrelaxFunctorStruct.comp F.toPrelaxFunctorStruct G.toPrelaxFunctorStruct

中文:
定义 comp
  签名: (G : PrelaxFunctor C D)
  定义体: PrelaxFunctorStruct.comp F.toPrelaxFunctorStruct G.toPrelaxFunctorStruct

Depends on / 依赖: F.toPrelaxFunctorStruct, G.toPrelaxFunctorStruct, PrelaxFunctorStruct, PrelaxFunctorStruct.comp, toPrelaxFunctorStruct
-/
def comp (G : PrelaxFunctor C D) : PrelaxFunctor B D where
  toPrelaxFunctorStruct := PrelaxFunctorStruct.comp F.toPrelaxFunctorStruct G.toPrelaxFunctorStruct

/-- Function between 1-morphisms as a functor. -/
@[simps]
/--
Definition of `mapFunctor` / `mapFunctor` 的定义

English:
definition mapFunctor
  signature: (a b : B)
  body: F.map f
  map η := F.map₂ η

@[simp]

中文:
定义 mapFunctor
  签名: (a b : B)
  定义体: F.map f
  map η := F.map₂ η

@[simp]

Depends on / 依赖: F.map
-/
def mapFunctor (a b : B) : (a ⟶ b) ⥤ (F.obj a ⟶ F.obj b) where
  obj f := F.map f
  map η := F.map₂ η

@[simp]
/--
lemma `mkOfHomFunctors_mapFunctor` / 引理 `mkOfHomFunctors_mapFunctor`

English:
lemma mkOfHomFunctors_mapFunctor
  statement: (F : B -> C) (F' : (a : B) -> (b : B) -> (a ⟶ b) ⥤ (F a ⟶ F b))
  proof: rfl

中文:
引理 mkOfHomFunctors_mapFunctor
  结论: (F : B -> C) (F' : (a : B) -> (b : B) -> (a ⟶ b) ⥤ (F a ⟶ F b))
  证明: rfl
-/
lemma mkOfHomFunctors_mapFunctor (F : B -> C) (F' : (a : B) -> (b : B) -> (a ⟶ b) ⥤ (F a ⟶ F b))
    (a b : B) : (mkOfHomFunctors F F').mapFunctor a b = F' a b :=
  rfl

section

variable {a b : B}

/-- A prelax functor `F` sends 2-isomorphisms `η : f ≅ g` to 2-isomorphisms
`F.map f ≅ F.map g`. -/
@[simps! -isSimp]
/--
Definition of `map₂Iso` / `map₂Iso` 的定义

English:
abbreviation map₂Iso
  signature: {f g : a ⟶ b} (η : f ≅ g)
  body: (F.mapFunctor a b).mapIso η

中文:
缩写 map₂Iso
  签名: {f g : a ⟶ b} (η : f ≅ g)
  定义体: (F.mapFunctor a b).mapIso η

Depends on / 依赖: F.mapFunctor, mapFunctor, mapIso
-/
abbrev map₂Iso {f g : a ⟶ b} (η : f ≅ g) : F.map f ≅ F.map g :=
  (F.mapFunctor a b).mapIso η

/--
Instance `map₂_isIso` / 实例 `map₂_isIso`

English:
instance map₂_isIso
  signature: {f g : a ⟶ b} (η : f ⟶ g) [IsIso η]
  body: (F.map₂Iso (asIso η)).isIso_hom

@[simp]

中文:
实例 map₂_isIso
  签名: {f g : a ⟶ b} (η : f ⟶ g) [IsIso η]
  定义体: (F.map₂Iso (asIso η)).isIso_hom

@[simp]

Depends on / 依赖: F.map, isIso_hom
-/
instance map₂_isIso {f g : a ⟶ b} (η : f ⟶ g) [IsIso η] : IsIso (F.map₂ η) :=
  (F.map₂Iso (asIso η)).isIso_hom

@[simp]
/--
lemma `map₂_inv` / 引理 `map₂_inv`

English:
lemma map₂_inv
  given: {f g : a ⟶ b} (η : f ⟶ g) [IsIso η]
  statement: F.map₂ (inv η) = inv (F.map₂ η)
  proof: by
  apply IsIso.eq_inv_of_hom_inv_id
  simp [← F.map₂_comp η (inv η)]

中文:
引理 map₂_inv
  条件: {f g : a ⟶ b} (η : f ⟶ g) [IsIso η]
  结论: F.map₂ (inv η) = inv (F.map₂ η)
  证明: by
  apply IsIso.eq_inv_of_hom_inv_id
  simp [← F.map₂_comp η (inv η)]

Depends on / 依赖: F.map, IsIso.eq_inv_of_hom_inv_id, eq_inv_of_hom_inv_id
-/
lemma map₂_inv {f g : a ⟶ b} (η : f ⟶ g) [IsIso η] : F.map₂ (inv η) = inv (F.map₂ η) := by
  apply IsIso.eq_inv_of_hom_inv_id
  simp [← F.map₂_comp η (inv η)]

/--
lemma `map₂_iso_inv` / 引理 `map₂_iso_inv`

English:
lemma map₂_iso_inv
  given: {f g : a ⟶ b} (η : f ≅ g)
  proof: by
  rw [← F.map₂_inv]; rw [IsIso.Iso.inv_hom]

@[reassoc, simp]

中文:
引理 map₂_iso_inv
  条件: {f g : a ⟶ b} (η : f ≅ g)
  证明: by
  rw [← F.map₂_inv]; rw [IsIso.Iso.inv_hom]

@[reassoc, simp]

Depends on / 依赖: F.map, IsIso.Iso.inv_hom, inv_hom
-/
lemma map₂_iso_inv {f g : a ⟶ b} (η : f ≅ g) :
    F.map₂ η.inv = inv (F.map₂ η.hom) := by
  rw [← F.map₂_inv]; rw [IsIso.Iso.inv_hom]

@[reassoc, simp]
/--
lemma `map₂_hom_inv` / 引理 `map₂_hom_inv`

English:
lemma map₂_hom_inv
  given: {f g : a ⟶ b} (η : f ≅ g)
  proof: by
  rw [← F.map₂_comp]; rw [Iso.hom_inv_id]; rw [F.map₂_id]

@[reassoc]

中文:
引理 map₂_hom_inv
  条件: {f g : a ⟶ b} (η : f ≅ g)
  证明: by
  rw [← F.map₂_comp]; rw [Iso.hom_inv_id]; rw [F.map₂_id]

@[reassoc]

Depends on / 依赖: F.map, Iso.hom_inv_id, hom_inv_id
-/
lemma map₂_hom_inv {f g : a ⟶ b} (η : f ≅ g) :
    F.map₂ η.hom ≫ F.map₂ η.inv = 𝟙 (F.map f) := by
  rw [← F.map₂_comp]; rw [Iso.hom_inv_id]; rw [F.map₂_id]

@[reassoc]
/--
lemma `map₂_hom_inv_isIso` / 引理 `map₂_hom_inv_isIso`

English:
lemma map₂_hom_inv_isIso
  given: {f g : a ⟶ b} (η : f ⟶ g) [IsIso η]
  proof: by
  simp

@[reassoc, simp]

中文:
引理 map₂_hom_inv_isIso
  条件: {f g : a ⟶ b} (η : f ⟶ g) [IsIso η]
  证明: by
  simp

@[reassoc, simp]
-/
lemma map₂_hom_inv_isIso {f g : a ⟶ b} (η : f ⟶ g) [IsIso η] :
    F.map₂ η ≫ F.map₂ (inv η) = 𝟙 (F.map f) := by
  simp

@[reassoc, simp]
/--
lemma `map₂_inv_hom` / 引理 `map₂_inv_hom`

English:
lemma map₂_inv_hom
  given: {f g : a ⟶ b} (η : f ≅ g)
  proof: by
  rw [← F.map₂_comp]; rw [Iso.inv_hom_id]; rw [F.map₂_id]

@[reassoc]

中文:
引理 map₂_inv_hom
  条件: {f g : a ⟶ b} (η : f ≅ g)
  证明: by
  rw [← F.map₂_comp]; rw [Iso.inv_hom_id]; rw [F.map₂_id]

@[reassoc]

Depends on / 依赖: F.map, Iso.inv_hom_id, inv_hom_id
-/
lemma map₂_inv_hom {f g : a ⟶ b} (η : f ≅ g) :
    F.map₂ η.inv ≫ F.map₂ η.hom = 𝟙 (F.map g) := by
  rw [← F.map₂_comp]; rw [Iso.inv_hom_id]; rw [F.map₂_id]

@[reassoc]
/--
lemma `map₂_inv_hom_isIso` / 引理 `map₂_inv_hom_isIso`

English:
lemma map₂_inv_hom_isIso
  given: {f g : a ⟶ b} (η : f ⟶ g) [IsIso η]
  proof: by
  simp

中文:
引理 map₂_inv_hom_isIso
  条件: {f g : a ⟶ b} (η : f ⟶ g) [IsIso η]
  证明: by
  simp
-/
lemma map₂_inv_hom_isIso {f g : a ⟶ b} (η : f ⟶ g) [IsIso η] :
    F.map₂ (inv η) ≫ F.map₂ η = 𝟙 (F.map g) := by
  simp

end

/--
lemma `map₂_eqToHom` / 引理 `map₂_eqToHom`

English:
lemma map₂_eqToHom
  given: {x y : B} (f g : x ⟶ y) (hfg : f = g)
  proof: by
  subst hfg
  simp

中文:
引理 map₂_eqToHom
  条件: {x y : B} (f g : x ⟶ y) (hfg : f = g)
  证明: by
  subst hfg
  simp
-/
lemma map₂_eqToHom {x y : B} (f g : x ⟶ y) (hfg : f = g) :
    F.map₂ (eqToHom hfg) = eqToHom (by rw [← hfg]) := by
  subst hfg
  simp

set_option backward.defeqAttrib.useBackward true in
/--
lemma `map₂Iso_eqToIso` / 引理 `map₂Iso_eqToIso`

English:
lemma map₂Iso_eqToIso
  given: {x y : B} (f g : x ⟶ y) (hfg : f = g)
  proof: by
  subst hfg
  simp

中文:
引理 map₂Iso_eqToIso
  条件: {x y : B} (f g : x ⟶ y) (hfg : f = g)
  证明: by
  subst hfg
  simp
-/
lemma map₂Iso_eqToIso {x y : B} (f g : x ⟶ y) (hfg : f = g) :
    F.map₂Iso (eqToIso hfg) = eqToIso (by rw [← hfg]) := by
  subst hfg
  simp

end PrelaxFunctor

end CategoryTheory
