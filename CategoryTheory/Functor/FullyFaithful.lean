/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.NatIso
public import Mathlib.Logic.Equiv.Defs

/-!
# Full and faithful functors

We define typeclasses `Full` and `Faithful`, decorating functors. These typeclasses
carry no data. However, we also introduce a structure `Functor.FullyFaithful` which
contains the data of the inverse map `(F.obj X ⟶ F.obj Y) ⟶ (X ⟶ Y)` of the
map induced on morphisms by a functor `F`.

## Main definitions and results
* Use `F.map_injective` to retrieve the fact that `F.map` is injective when `[Faithful F]`.
* Similarly, `F.map_surjective` states that `F.map` is surjective when `[Full F]`.
* Use `F.preimage` to obtain preimages of morphisms when `[Full F]`.
* We prove some basic "cancellation" lemmas for full and/or faithful functors, as well as a
  construction for "dividing" a functor by a faithful functor, see `Faithful.div`.

See `CategoryTheory.Equivalence.of_fullyFaithful_ess_surj` for the fact that a functor is an
equivalence if and only if it is fully faithful and essentially surjective.

-/

@[expose] public section


-- declare the `v`'s first; see `CategoryTheory.Category` for an explanation
universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {E : Type*} [Category* E]

namespace Functor

/-- A functor `F : C ⥤ D` is full if for each `X Y : C`, `F.map` is surjective. -/
@[stacks 001C]
/--
Definition of `Full` / `Full` 的定义

English:
class Full
  parameters: (F : C ⥤ D)
  axioms and operations (1):
    - map_surjective({X Y : C}) : Function.Surjective (F.map (X := X) (Y := Y))

中文:
类 满
  参数: (F : C ⥤ D)
  公理与运算 (1 个):
    - map_surjective({X Y : C}) : 函数.满射 (F.map (X := X) (Y := Y))
-/
class Full (F : C ⥤ D) : Prop where
  map_surjective {X Y : C} : Function.Surjective (F.map (X := X) (Y := Y))

attribute [to_dual self] Full.map_surjective Full.mk

/-- A functor `F : C ⥤ D` is faithful if for each `X Y : C`, `F.map` is injective. -/
@[stacks 001C]
/--
Definition of `Faithful` / `Faithful` 的定义

English:
class Faithful
  parameters: (F : C ⥤ D)
  axioms and operations (1):
    - map_injective : forall {X Y : C}, Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))  [default: by cat_disch]

中文:
类 忠实
  参数: (F : C ⥤ D)
  公理与运算 (1 个):
    - map_injective : 对任意 {X Y : C}, 函数.单射 (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))  [默认: by cat_disch]

Depends on / 依赖: HasImage, cat_disch, mono_hasImage
-/
class Faithful (F : C ⥤ D) : Prop where
  /-- `F.map` is injective for each `X Y : C`. -/
  map_injective : forall {X Y : C}, Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y)) := by
    cat_disch

attribute [to_dual self] Faithful.map_injective Faithful.mk

variable {X Y : C}

@[grind inj, to_dual self]
/--
theorem `map_injective` / 定理 `map_injective`

English:
theorem map_injective
  given: (F : C ⥤ D) [Faithful F]
  proof: Faithful.map_injective

中文:
定理 map_injective
  条件: (F : C ⥤ D) [忠实 F]
  证明: Faithful.map_injective

Depends on / 依赖: Faithful, Faithful.map_injective, map_injective
-/
theorem map_injective (F : C ⥤ D) [Faithful F] :
Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y)) :=
  Faithful.map_injective

/--
lemma `map_injective_iff` / 引理 `map_injective_iff`

English:
lemma map_injective_iff
  given: (F : C ⥤ D) [Faithful F] {X Y : C} (f g : X ⟶ Y)
  proof: ⟨fun h => F.map_injective h, fun h => by rw [h]⟩

中文:
引理 map_injective_iff
  条件: (F : C ⥤ D) [忠实 F] {X Y : C} (f g : X ⟶ Y)
  证明: ⟨fun h => F.map_injective h, fun h => by rw [h]⟩

Depends on / 依赖: F.map_injective, map_injective
-/
lemma map_injective_iff (F : C ⥤ D) [Faithful F] {X Y : C} (f g : X ⟶ Y) :
    F.map f = F.map g ↔ f = g :=
  ⟨fun h => F.map_injective h, fun h => by rw [h]⟩

/--
theorem `mapIso_injective` / 定理 `mapIso_injective`

English:
theorem mapIso_injective
  given: (F : C ⥤ D) [Faithful F]
  proof: fun _ _ h =>
  Iso.ext (map_injective F (congr_arg Iso.hom h :))

中文:
定理 mapIso_injective
  条件: (F : C ⥤ D) [忠实 F]
  证明: fun _ _ h =>
  Iso.ext (map_injective F (congr_arg Iso.hom h :))
-/
theorem mapIso_injective (F : C ⥤ D) [Faithful F] :
Function.Injective (F.mapIso : (X ≅ Y) -> (F.obj X ≅ F.obj Y)) := fun _ _ h =>
  Iso.ext (map_injective F (congr_arg Iso.hom h :))

/--
theorem `map_surjective` / 定理 `map_surjective`

English:
theorem map_surjective
  given: (F : C ⥤ D) [Full F]
  proof: Full.map_surjective

中文:
定理 map_surjective
  条件: (F : C ⥤ D) [满 F]
  证明: Full.map_surjective

Depends on / 依赖: Full.map_surjective, map_surjective
-/
theorem map_surjective (F : C ⥤ D) [Full F] :
    Function.Surjective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y)) :=
  Full.map_surjective

/-- The choice of a preimage of a morphism under a full functor. -/
@[to_dual self]
/--
Definition of `preimage` / `preimage` 的定义

English:
definition preimage
  signature: (F : C ⥤ D) [Full F] (f : F.obj X ⟶ F.obj Y)
  body: (F.map_surjective f).choose

中文:
定义 原像
  签名: (F : C ⥤ D) [满 F] (f : F.obj X ⟶ F.obj Y)
  定义体: (F.map_surjective f).choose

Depends on / 依赖: F.map_surjective, Image.monoFactorisation, map_surjective, monoFactorisation
-/
noncomputable def preimage (F : C ⥤ D) [Full F] (f : F.obj X ⟶ F.obj Y) : X ⟶ Y :=
  (F.map_surjective f).choose

-- TODO: `to_dual` should deal with this automatically:
attribute [to_dual self] preimage.congr_simp

@[simp, to_dual self]
/--
theorem `map_preimage` / 定理 `map_preimage`

English:
theorem map_preimage
  given: (F : C ⥤ D) [Full F] {X Y : C} (f : F.obj X ⟶ F.obj Y)
  proof: (F.map_surjective f).choose_spec

中文:
定理 map_preimage
  条件: (F : C ⥤ D) [满 F] {X Y : C} (f : F.obj X ⟶ F.obj Y)
  证明: (F.map_surjective f).choose_spec

Depends on / 依赖: F.map_surjective, choose_spec, map_surjective
-/
theorem map_preimage (F : C ⥤ D) [Full F] {X Y : C} (f : F.obj X ⟶ F.obj Y) :
    F.map (preimage F f) = f :=
  (F.map_surjective f).choose_spec

variable {F : C ⥤ D} {X Y Z : C}

section
variable [Full F] [F.Faithful]

@[simp]
/--
theorem `preimage_id` / 定理 `preimage_id`

English:
theorem preimage_id
  statement: F.preimage (𝟙 (F.obj X)) = 𝟙 X
  proof: F.map_injective (by simp)

@[simp, to_dual self]

中文:
定理 preimage_id
  结论: F.原像 (𝟙 (F.obj X)) = 𝟙 X
  证明: F.map_injective (by simp)

@[simp, to_dual self]

Depends on / 依赖: F.map_injective, map_injective
-/
theorem preimage_id : F.preimage (𝟙 (F.obj X)) = 𝟙 X :=
  F.map_injective (by simp)

@[simp, to_dual self]
/--
theorem `preimage_comp` / 定理 `preimage_comp`

English:
theorem preimage_comp
  given: (f : F.obj X ⟶ F.obj Y) (g : F.obj Y ⟶ F.obj Z)
  proof: F.map_injective (by simp)

@[simp, to_dual self]

中文:
定理 preimage_comp
  条件: (f : F.obj X ⟶ F.obj Y) (g : F.obj Y ⟶ F.obj Z)
  证明: F.map_injective (by simp)

@[simp, to_dual self]

Depends on / 依赖: F.map_injective, map_injective
-/
theorem preimage_comp (f : F.obj X ⟶ F.obj Y) (g : F.obj Y ⟶ F.obj Z) :
    F.preimage (f ≫ g) = F.preimage f ≫ F.preimage g :=
  F.map_injective (by simp)

@[simp, to_dual self]
/--
theorem `preimage_map` / 定理 `preimage_map`

English:
theorem preimage_map
  given: (f : X ⟶ Y)
  statement: F.preimage (F.map f) = f
  proof: F.map_injective (by simp)

中文:
定理 preimage_map
  条件: (f : X ⟶ Y)
  结论: F.原像 (F.map f) = f
  证明: F.map_injective (by simp)

Depends on / 依赖: F.map_injective, map_injective
-/
theorem preimage_map (f : X ⟶ Y) : F.preimage (F.map f) = f :=
  F.map_injective (by simp)

variable (F)

/-- If `F : C ⥤ D` is fully faithful, every isomorphism `F.obj X ≅ F.obj Y` has a preimage. -/
@[simps]
/--
Definition of `preimageIso` / `preimageIso` 的定义

English:
definition preimageIso
  signature: (f : F.obj X ≅ F.obj Y)
  body: F.preimage f.hom
  inv := F.preimage f.inv
  hom_inv_id := F.map_injective (by simp)
  inv_hom_id := F.map_injective (by simp)

@[simp]

中文:
定义 preimageIso
  签名: (f : F.obj X ≅ F.obj Y)
  定义体: F.preimage f.hom
  inv := F.preimage f.inv
  hom_inv_id := F.map_injective (by simp)
  inv_hom_id := F.map_injective (by simp)

@[simp]

Depends on / 依赖: F.preimage, Image.monoFactorisation, f.hom, monoFactorisation, preimage
-/
noncomputable def preimageIso (f : F.obj X ≅ F.obj Y) :
    X ≅ Y where
  hom := F.preimage f.hom
  inv := F.preimage f.inv
  hom_inv_id := F.map_injective (by simp)
  inv_hom_id := F.map_injective (by simp)

@[simp]
/--
theorem `preimageIso_mapIso` / 定理 `preimageIso_mapIso`

English:
theorem preimageIso_mapIso
  given: (f : X ≅ Y)
  statement: F.preimageIso (F.mapIso f) = f
  proof: by
  ext
  simp

中文:
定理 preimageIso_mapIso
  条件: (f : X ≅ Y)
  结论: F.preimageIso (F.mapIso f) = f
  证明: by
  ext
  simp

Depends on / 依赖: Image.isImage, isImage
-/
theorem preimageIso_mapIso (f : X ≅ Y) : F.preimageIso (F.mapIso f) = f := by
  ext
  simp

end

variable (F) in
/--
Definition of `FullyFaithful` / `FullyFaithful` 的定义

English:
structure FullyFaithful
  parameters: where
  axioms and operations (3):
    - preimage({X Y : C} (f : F.obj X ⟶ F.obj Y)) : X ⟶ Y
    - map_preimage({X Y : C} (f : F.obj X ⟶ F.obj Y)) : F.map (preimage f) = f  [default: by cat_disch]
    - preimage_map({X Y : C} (f : X ⟶ Y)) : preimage (F.map f) = f  [default: by cat_disch]

中文:
结构 满忠实
  参数: where
  公理与运算 (3 个):
    - preimage({X Y : C} (f : F.obj X ⟶ F.obj Y)) : X ⟶ Y
    - map_preimage({X Y : C} (f : F.obj X ⟶ F.obj Y)) : F.map (原像 f) = f  [默认: by cat_disch]
    - preimage_map({X Y : C} (f : X ⟶ Y)) : 原像 (F.map f) = f  [默认: by cat_disch]

Depends on / 依赖: F.map, Image.isImage, cat_disch, isImage, lift_fac, preimage, preimage_map
-/
structure FullyFaithful where
  /-- The inverse map `(F.obj X ⟶ F.obj Y) ⟶ (X ⟶ Y)` of `F.map`. -/
  preimage {X Y : C} (f : F.obj X ⟶ F.obj Y) : X ⟶ Y
  map_preimage {X Y : C} (f : F.obj X ⟶ F.obj Y) : F.map (preimage f) = f := by cat_disch
  preimage_map {X Y : C} (f : X ⟶ Y) : preimage (F.map f) = f := by cat_disch

namespace FullyFaithful

attribute [simp] map_preimage preimage_map

variable (F) in
/--
Definition of `ofFullyFaithful` / `ofFullyFaithful` 的定义

English:
definition ofFullyFaithful
  signature: [F.Full] [F.Faithful]
  body: F.preimage

中文:
定义 ofFullyFaithful
  签名: [F.满] [F.忠实]
  定义体: F.preimage

Depends on / 依赖: F.preimage, preimage
-/
noncomputable def ofFullyFaithful [F.Full] [F.Faithful] :
    F.FullyFaithful where
  preimage := F.preimage

variable (C) in
/-- The identity functor is fully faithful. -/
@[simps]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : (𝟭 C).FullyFaithful where
  body: f

中文:
定义 id
  签名: : (𝟭 C).满忠实 where
  定义体: f
-/
def id : (𝟭 C).FullyFaithful where
  preimage f := f

section
variable (hF : F.FullyFaithful)

include hF

/-- The equivalence `(X ⟶ Y) ≃ (F.obj X ⟶ F.obj Y)` given by `h : F.FullyFaithful`. -/
@[simps]
/--
Definition of `homEquiv` / `homEquiv` 的定义

English:
definition homEquiv
  signature: {X Y : C}
  body: F.map
  invFun := hF.preimage
  left_inv _ := by simp
  right_inv _ := by simp

中文:
定义 homEquiv
  签名: {X Y : C}
  定义体: F.map
  invFun := hF.preimage
  left_inv _ := by simp
  right_inv _ := by simp

Depends on / 依赖: F.map
-/
def homEquiv {X Y : C} : (X ⟶ Y) ≃ (F.obj X ⟶ F.obj Y) where
  toFun := F.map
  invFun := hF.preimage
  left_inv _ := by simp
  right_inv _ := by simp

/--
lemma `map_injective` / 引理 `map_injective`

English:
lemma map_injective
  given: {X Y : C} {f g : X ⟶ Y} (h : F.map f = F.map g)
  statement: f = g
  proof: hF.homEquiv.injective h

中文:
引理 map_injective
  条件: {X Y : C} {f g : X ⟶ Y} (h : F.map f = F.map g)
  结论: f = g
  证明: hF.homEquiv.injective h

Depends on / 依赖: hF.homEquiv.injective, homEquiv, injective
-/
lemma map_injective {X Y : C} {f g : X ⟶ Y} (h : F.map f = F.map g) : f = g :=
  hF.homEquiv.injective h

/--
lemma `map_surjective` / 引理 `map_surjective`

English:
lemma map_surjective
  given: {X Y : C}
  proof: hF.homEquiv.surjective

中文:
引理 map_surjective
  条件: {X Y : C}
  证明: hF.homEquiv.surjective

Depends on / 依赖: hF.homEquiv.surjective, homEquiv, surjective
-/
lemma map_surjective {X Y : C} :
    Function.Surjective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y)) :=
  hF.homEquiv.surjective

/--
lemma `map_bijective` / 引理 `map_bijective`

English:
lemma map_bijective
  given: (X Y : C)
  proof: hF.homEquiv.bijective

@[simp]

中文:
引理 map_bijective
  条件: (X Y : C)
  证明: hF.homEquiv.bijective

@[simp]

Depends on / 依赖: bijective, hF.homEquiv.bijective, homEquiv
-/
lemma map_bijective (X Y : C) :
    Function.Bijective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y)) :=
  hF.homEquiv.bijective

@[simp]
/--
lemma `preimage_id` / 引理 `preimage_id`

English:
lemma preimage_id
  given: {X : C}
  proof: hF.map_injective (by simp)

@[simp, reassoc]

中文:
引理 preimage_id
  条件: {X : C}
  证明: hF.map_injective (by simp)

@[simp, reassoc]

Depends on / 依赖: hF.map_injective, map_injective
-/
lemma preimage_id {X : C} :
    hF.preimage (𝟙 (F.obj X)) = 𝟙 X :=
  hF.map_injective (by simp)

@[simp, reassoc]
/--
lemma `preimage_comp` / 引理 `preimage_comp`

English:
lemma preimage_comp
  given: {X Y Z : C} (f : F.obj X ⟶ F.obj Y) (g : F.obj Y ⟶ F.obj Z)
  proof: hF.map_injective (by simp)

中文:
引理 preimage_comp
  条件: {X Y Z : C} (f : F.obj X ⟶ F.obj Y) (g : F.obj Y ⟶ F.obj Z)
  证明: hF.map_injective (by simp)

Depends on / 依赖: factorThruImage, hF.map_injective, image.lift, isImage, map_injective
-/
lemma preimage_comp {X Y Z : C} (f : F.obj X ⟶ F.obj Y) (g : F.obj Y ⟶ F.obj Z) :
    hF.preimage (f ≫ g) = hF.preimage f ≫ hF.preimage g :=
  hF.map_injective (by simp)

/--
lemma `full` / 引理 `full`

English:
lemma full
  statement: F.Full where
  proof: hF.map_surjective

中文:
引理 full
  结论: F.满 where
  证明: hF.map_surjective

Depends on / 依赖: hF.map_surjective, map_surjective
-/
lemma full : F.Full where
  map_surjective := hF.map_surjective

/--
lemma `faithful` / 引理 `faithful`

English:
lemma faithful
  statement: F.Faithful where
  proof: hF.map_injective

中文:
引理 faithful
  结论: F.忠实 where
  证明: hF.map_injective

Depends on / 依赖: hF.map_injective, map_injective
-/
lemma faithful : F.Faithful where
  map_injective := hF.map_injective

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Subsingleton F.FullyFaithful
  body: by
    have := h₁.faithful
    cases h₁ with | mk f₁ hf₁ _ => cases h₂ with | mk f₂ hf₂ _ =>
    simp only [Functor.FullyFaithful.mk.injEq]
    ext
    apply F.map_injective
    rw [hf₁]; rw [hf₂]

中文:
实例 :
  签名: 子单例 F.满忠实
  定义体: by
    have := h₁.faithful
    cases h₁ with | mk f₁ hf₁ _ => cases h₂ with | mk f₂ hf₂ _ =>
    simp only [Functor.FullyFaithful.mk.injEq]
    ext
    apply F.map_injective
    rw [hf₁]; rw [hf₂]

Depends on / 依赖: F.map_injective, FullyFaithful, Functor, Functor.FullyFaithful.mk.injEq, faithful, map_injective
-/
instance : Subsingleton F.FullyFaithful where
  allEq h₁ h₂ := by
    have := h₁.faithful
    cases h₁ with | mk f₁ hf₁ _ => cases h₂ with | mk f₂ hf₂ _ =>
    simp only [Functor.FullyFaithful.mk.injEq]
    ext
    apply F.map_injective
    rw [hf₁]; rw [hf₂]

/-- The unique isomorphism `X ≅ Y` which induces an isomorphism `F.obj X ≅ F.obj Y`
when `hF : F.FullyFaithful`. -/
@[simps]
/--
Definition of `preimageIso` / `preimageIso` 的定义

English:
definition preimageIso
  signature: {X Y : C} (e : F.obj X ≅ F.obj Y)
  body: hF.preimage e.hom
  inv := hF.preimage e.inv
  hom_inv_id := hF.map_injective (by simp)
  inv_hom_id := hF.map_injective (by simp)

中文:
定义 preimageIso
  签名: {X Y : C} (e : F.obj X ≅ F.obj Y)
  定义体: hF.preimage e.hom
  inv := hF.preimage e.inv
  hom_inv_id := hF.map_injective (by simp)
  inv_hom_id := hF.map_injective (by simp)

Depends on / 依赖: e.hom, hF.preimage, preimage
-/
def preimageIso {X Y : C} (e : F.obj X ≅ F.obj Y) : X ≅ Y where
  hom := hF.preimage e.hom
  inv := hF.preimage e.inv
  hom_inv_id := hF.map_injective (by simp)
  inv_hom_id := hF.map_injective (by simp)

/--
lemma `isIso_of_isIso_map` / 引理 `isIso_of_isIso_map`

English:
lemma isIso_of_isIso_map
  given: {X Y : C} (f : X ⟶ Y) [IsIso (F.map f)]
  proof: by
  simpa using (hF.preimageIso (asIso (F.map f))).isIso_hom

中文:
引理 isIso_of_isIso_map
  条件: {X Y : C} (f : X ⟶ Y) [是同构 (F.map f)]
  证明: by
  simpa using (hF.preimageIso (asIso (F.map f))).isIso_hom

Depends on / 依赖: F.map, hF.preimageIso, isIso_hom, preimageIso
-/
lemma isIso_of_isIso_map {X Y : C} (f : X ⟶ Y) [IsIso (F.map f)] :
    IsIso f := by
  simpa using (hF.preimageIso (asIso (F.map f))).isIso_hom

/-- The equivalence `(X ≅ Y) ≃ (F.obj X ≅ F.obj Y)` given by `h : F.FullyFaithful`. -/
@[simps]
/--
Definition of `isoEquiv` / `isoEquiv` 的定义

English:
definition isoEquiv
  signature: {X Y : C}
  body: F.mapIso
  invFun := hF.preimageIso
  left_inv := by cat_disch
  right_inv := by cat_disch

中文:
定义 isoEquiv
  签名: {X Y : C}
  定义体: F.mapIso
  invFun := hF.preimageIso
  left_inv := by cat_disch
  right_inv := by cat_disch

Depends on / 依赖: F.mapIso, mapIso
-/
def isoEquiv {X Y : C} : (X ≅ Y) ≃ (F.obj X ≅ F.obj Y) where
  toFun := F.mapIso
  invFun := hF.preimageIso
  left_inv := by cat_disch
  right_inv := by cat_disch

/-- Fully faithful functors are stable by composition. -/
@[simps]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: {G : D ⥤ E} (hG : G.FullyFaithful)
  body: hF.preimage (hG.preimage f)

中文:
定义 comp
  签名: {G : D ⥤ E} (hG : G.满忠实)
  定义体: hF.preimage (hG.preimage f)

Depends on / 依赖: hF.preimage, hG.preimage, preimage
-/
def comp {G : D ⥤ E} (hG : G.FullyFaithful) : (F ⋙ G).FullyFaithful where
  preimage f := hF.preimage (hG.preimage f)

/--
Definition of `ofIso` / `ofIso` 的定义

English:
definition ofIso
  signature: {G : C ⥤ D} (e : F ≅ G)
  body: hF.preimage (e.hom.app _ ≫ f ≫ e.inv.app _)
  map_preimage f := by simp [← NatIso.naturality_1 e]

中文:
定义 ofIso
  签名: {G : C ⥤ D} (e : F ≅ G)
  定义体: hF.preimage (e.hom.app _ ≫ f ≫ e.inv.app _)
  map_preimage f := by simp [← NatIso.naturality_1 e]

Depends on / 依赖: e.hom.app, e.inv.app, hF.preimage, preimage
-/
def ofIso {G : C ⥤ D} (e : F ≅ G) : G.FullyFaithful where
  preimage f := hF.preimage (e.hom.app _ ≫ f ≫ e.inv.app _)
  map_preimage f := by simp [← NatIso.naturality_1 e]

end

variable (F) in
/--
lemma `nonempty_iff_map_bijective` / 引理 `nonempty_iff_map_bijective`

English:
lemma nonempty_iff_map_bijective
  proof: ⟨fun ⟨hF⟩ => hF.map_bijective, fun hF => by
    have : F.Faithful := ⟨fun h => (hF _ _).injective h⟩
    have : F.Full := ⟨(hF _ _).surjective⟩
    exact ⟨.ofFullyFaithful _⟩⟩

中文:
引理 nonempty_iff_map_bijective
  证明: ⟨fun ⟨hF⟩ => hF.map_bijective, fun hF => by
    have : F.Faithful := ⟨fun h => (hF _ _).injective h⟩
    have : F.Full := ⟨(hF _ _).surjective⟩
    exact ⟨.ofFullyFaithful _⟩⟩

Depends on / 依赖: Category, Category.assoc, Category.id_comp, F.Faithful, F.Full, Faithful, cancel_mono, eqToHom, h.symm, hF.map_bijective, id_comp, image.eqToHom, injective, map_bijective, ofFullyFaithful, surjective
-/
lemma nonempty_iff_map_bijective :
    Nonempty F.FullyFaithful ↔ forall (X Y : C), Function.Bijective (F.map : (X ⟶ Y) -> _) :=
  ⟨fun ⟨hF⟩ => hF.map_bijective, fun hF => by
    have : F.Faithful := ⟨fun h => (hF _ _).injective h⟩
    have : F.Full := ⟨(hF _ _).surjective⟩
    exact ⟨.ofFullyFaithful _⟩⟩

/--
Definition of `ofCompFaithful` / `ofCompFaithful` 的定义

English:
definition ofCompFaithful
  signature: {G : D ⥤ E} [G.Faithful] (hFG : (F ⋙ G).FullyFaithful)
  body: hFG.preimage (G.map f)
  map_preimage f := G.map_injective (hFG.map_preimage (G.map f))
  preimage_map f := hFG.preimage_map f

中文:
定义 ofCompFaithful
  签名: {G : D ⥤ E} [G.忠实] (hFG : (F ⋙ G).满忠实)
  定义体: hFG.preimage (G.map f)
  map_preimage f := G.map_injective (hFG.map_preimage (G.map f))
  preimage_map f := hFG.preimage_map f

Depends on / 依赖: G.map, hFG.preimage, preimage
-/
def ofCompFaithful {G : D ⥤ E} [G.Faithful] (hFG : (F ⋙ G).FullyFaithful) :
    F.FullyFaithful where
  preimage f := hFG.preimage (G.map f)
  map_preimage f := G.map_injective (hFG.map_preimage (G.map f))
  preimage_map f := hFG.preimage_map f

end FullyFaithful

end Functor


section

variable (F : C ⥤ D) [F.Full] [F.Faithful] {X Y : C}

/--
theorem `isIso_of_fully_faithful` / 定理 `isIso_of_fully_faithful`

English:
theorem isIso_of_fully_faithful
  given: (f : X ⟶ Y) [IsIso (F.map f)]
  statement: IsIso f
  proof: ⟨⟨F.preimage (inv (F.map f)), ⟨F.map_injective (by simp), F.map_injective (by simp)⟩⟩⟩

中文:
定理 isIso_of_fully_faithful
  条件: (f : X ⟶ Y) [是同构 (F.map f)]
  结论: 是同构 f
  证明: ⟨⟨F.preimage (inv (F.map f)), ⟨F.map_injective (by simp), F.map_injective (by simp)⟩⟩⟩

Depends on / 依赖: F.map, F.map_injective, F.preimage, map_injective, preimage
-/
theorem isIso_of_fully_faithful (f : X ⟶ Y) [IsIso (F.map f)] : IsIso f :=
  ⟨⟨F.preimage (inv (F.map f)), ⟨F.map_injective (by simp), F.map_injective (by simp)⟩⟩⟩


end

end CategoryTheory

namespace CategoryTheory

namespace Functor

variable {C : Type u₁} [Category.{v₁} C]

/--
Instance `Full.id` / 实例 `Full.id`

English:
instance Full.id
  signature: : Full (𝟭 C) where map_surjective
  body: Function.surjective_id

中文:
实例 满.id
  签名: : 满 (𝟭 C) where map_surjective
  定义体: Function.surjective_id

Depends on / 依赖: Function, Function.surjective_id, surjective_id
-/
instance Full.id : Full (𝟭 C) where map_surjective := Function.surjective_id

/--
Instance `Faithful.id` / 实例 `Faithful.id`

English:
instance Faithful.id
  signature: : Functor.Faithful (𝟭 C)
  body: { }

中文:
实例 忠实.id
  签名: : 函子.忠实 (𝟭 C)
  定义体: { }
-/
instance Faithful.id : Functor.Faithful (𝟭 C) := { }

variable {D : Type u₂} [Category.{v₂} D] {E : Type u₃} [Category.{v₃} E]
variable (F F' : C ⥤ D) (G : D ⥤ E)

/--
Instance `Faithful.comp` / 实例 `Faithful.comp`

English:
instance Faithful.comp
  signature: [F.Faithful] [G.Faithful]
  body: F.map_injective (G.map_injective p)

中文:
实例 忠实.comp
  签名: [F.忠实] [G.忠实]
  定义体: F.map_injective (G.map_injective p)

Depends on / 依赖: F.map_injective, G.map_injective, map_injective
-/
instance Faithful.comp [F.Faithful] [G.Faithful] : (F ⋙ G).Faithful where
  map_injective p := F.map_injective (G.map_injective p)

/--
theorem `Faithful.of_comp` / 定理 `Faithful.of_comp`

English:
theorem Faithful.of_comp
  given: [(F ⋙ G).Faithful]
  statement: F.Faithful
  proof: -- Porting note: (F ⋙ G).map_injective.of_comp has the incorrect type
  { map_injective := fun {_ _} => Function.Injective.of_comp (F ⋙ G).map_injective }

中文:
定理 忠实.of_comp
  条件: [(F ⋙ G).忠实]
  结论: F.忠实
  证明: -- Porting note: (F ⋙ G).map_injective.of_comp has the incorrect type
  { map_injective := fun {_ _} => Function.Injective.of_comp (F ⋙ G).map_injective }
-/
theorem Faithful.of_comp [(F ⋙ G).Faithful] : F.Faithful :=
  -- Porting note: (F ⋙ G).map_injective.of_comp has the incorrect type
  { map_injective := fun {_ _} => Function.Injective.of_comp (F ⋙ G).map_injective }

instance (priority := 100) [Quiver.IsThin C] : F.Faithful where

section

variable {F F'}

/--
lemma `Full.of_iso` / 引理 `Full.of_iso`

English:
lemma Full.of_iso
  given: [Full F] (α : F ≅ F')
  statement: Full F' where
  proof: ⟨F.preimage ((α.app X).hom ≫ f ≫ (α.app Y).inv), by simp [← NatIso.naturality_1 α]⟩

中文:
引理 满.of_iso
  条件: [满 F] (α : F ≅ F')
  结论: 满 F' where
  证明: ⟨F.preimage ((α.app X).hom ≫ f ≫ (α.app Y).inv), by simp [← NatIso.naturality_1 α]⟩

Depends on / 依赖: F.preimage, NatIso, NatIso.naturality_1, naturality_1, preimage
-/
lemma Full.of_iso [Full F] (α : F ≅ F') : Full F' where
  map_surjective {X Y} f :=
    ⟨F.preimage ((α.app X).hom ≫ f ≫ (α.app Y).inv), by simp [← NatIso.naturality_1 α]⟩

/--
theorem `Faithful.of_iso` / 定理 `Faithful.of_iso`

English:
theorem Faithful.of_iso
  given: [F.Faithful] (α : F ≅ F')
  statement: F'.Faithful
  proof: { map_injective := fun h =>
      F.map_injective (by rw [← NatIso.naturality_1 α.symm, h, NatIso.naturality_1 α.symm]) }

中文:
定理 忠实.of_iso
  条件: [F.忠实] (α : F ≅ F')
  结论: F'.忠实
  证明: { map_injective := fun h =>
      F.map_injective (by rw [← NatIso.naturality_1 α.symm, h, NatIso.naturality_1 α.symm]) }

Depends on / 依赖: F.map_injective, NatIso, NatIso.naturality_1, map_injective, naturality_1
-/
theorem Faithful.of_iso [F.Faithful] (α : F ≅ F') : F'.Faithful :=
  { map_injective := fun h =>
      F.map_injective (by rw [← NatIso.naturality_1 α.symm, h, NatIso.naturality_1 α.symm]) }

end

variable {F G}

/--
theorem `Faithful.of_comp_iso` / 定理 `Faithful.of_comp_iso`

English:
theorem Faithful.of_comp_iso
  given: {H : C ⥤ E} [H.Faithful] (h : F ⋙ G ≅ H)
  statement: F.Faithful
  proof: @Faithful.of_comp _ _ _ _ _ _ F G (Faithful.of_iso h.symm)

alias _root_.CategoryTheory.Iso.faithful_of_comp := Faithful.of_comp_iso

中文:
定理 忠实.of_comp_iso
  条件: {H : C ⥤ E} [H.忠实] (h : F ⋙ G ≅ H)
  结论: F.忠实
  证明: @Faithful.of_comp _ _ _ _ _ _ F G (Faithful.of_iso h.symm)

alias _root_.CategoryTheory.Iso.faithful_of_comp := Faithful.of_comp_iso

Depends on / 依赖: Faithful, Faithful.of_comp, Faithful.of_iso, h.symm, of_comp, of_iso
-/
theorem Faithful.of_comp_iso {H : C ⥤ E} [H.Faithful] (h : F ⋙ G ≅ H) : F.Faithful :=
  @Faithful.of_comp _ _ _ _ _ _ F G (Faithful.of_iso h.symm)

alias _root_.CategoryTheory.Iso.faithful_of_comp := Faithful.of_comp_iso

-- We could prove this from `Faithful.of_comp_iso` using `eq_to_iso`,
-- but that would introduce a cyclic import.
/--
theorem `Faithful.of_comp_eq` / 定理 `Faithful.of_comp_eq`

English:
theorem Faithful.of_comp_eq
  given: {H : C ⥤ E} [ℋ : H.Faithful] (h : F ⋙ G = H)
  statement: F.Faithful
  proof: @Faithful.of_comp _ _ _ _ _ _ F G (h.symm ▸ ℋ)

alias _root_.Eq.faithful_of_comp := Faithful.of_comp_eq

中文:
定理 忠实.of_comp_eq
  条件: {H : C ⥤ E} [ℋ : H.忠实] (h : F ⋙ G = H)
  结论: F.忠实
  证明: @Faithful.of_comp _ _ _ _ _ _ F G (h.symm ▸ ℋ)

alias _root_.Eq.faithful_of_comp := Faithful.of_comp_eq

Depends on / 依赖: Faithful, Faithful.of_comp, h.symm, of_comp
-/
theorem Faithful.of_comp_eq {H : C ⥤ E} [ℋ : H.Faithful] (h : F ⋙ G = H) : F.Faithful :=
  @Faithful.of_comp _ _ _ _ _ _ F G (h.symm ▸ ℋ)

alias _root_.Eq.faithful_of_comp := Faithful.of_comp_eq

variable (F G)
/--
Definition of `Faithful.div` / `Faithful.div` 的定义

English:
definition Faithful.div
  signature: (F : C ⥤ E) (G : D ⥤ E) [G.Faithful] (obj : C -> D)
  body: { obj, map := @map,
    map_id := by
      intro X
      apply G.map_injective
      grind
    map_comp := by grind }

中文:
定义 忠实.div
  签名: (F : C ⥤ E) (G : D ⥤ E) [G.忠实] (obj : C -> D)
  定义体: { obj, map := @map,
    map_id := by
      intro X
      apply G.map_injective
      grind
    map_comp := by grind }
-/
protected def Faithful.div (F : C ⥤ E) (G : D ⥤ E) [G.Faithful] (obj : C -> D)
    (h_obj : forall X, G.obj (obj X) = F.obj X) (map : forall {X Y}, (X ⟶ Y) -> (obj X ⟶ obj Y))
    (h_map : forall {X Y} {f : X ⟶ Y}, G.map (map f) ≍ F.map f) : C ⥤ D :=
  { obj, map := @map,
    map_id := by
      intro X
      apply G.map_injective
      grind
    map_comp := by grind }

-- This follows immediately from `Functor.hext` (`Functor.hext h_obj @h_map`),
-- but importing `CategoryTheory.EqToHom` causes an import loop:
-- CategoryTheory.EqToHom → CategoryTheory.Opposites →
-- CategoryTheory.Equivalence → CategoryTheory.FullyFaithful
/--
theorem `Faithful.div_comp` / 定理 `Faithful.div_comp`

English:
theorem Faithful.div_comp
  statement: (F : C ⥤ E) [F.Faithful] (G : D ⥤ E) [G.Faithful] (obj : C -> D)
  proof: by
  obtain ⟨F_obj, _, _, _⟩ := F; obtain ⟨G_obj, _, _, _⟩ := G
  unfold Faithful.div Functor.comp
  have : F_obj = G_obj ∘ obj := (funext h_obj).symm
  subst this
  congr
  simp only [Function.comp_apply, heq_eq_eq] at h_map
  ext
  exact h_map

中文:
定理 忠实.div_comp
  结论: (F : C ⥤ E) [F.忠实] (G : D ⥤ E) [G.忠实] (obj : C -> D)
  证明: by
  obtain ⟨F_obj, _, _, _⟩ := F; obtain ⟨G_obj, _, _, _⟩ := G
  unfold Faithful.div Functor.comp
  have : F_obj = G_obj ∘ obj := (funext h_obj).symm
  subst this
  congr
  simp only [Function.comp_apply, heq_eq_eq] at h_map
  ext
  exact h_map

Depends on / 依赖: F_obj, Faithful, Faithful.div, Function, Function.comp_apply, Functor, Functor.comp, G_obj, comp_apply, h_map, h_obj, heq_eq_eq
-/
theorem Faithful.div_comp (F : C ⥤ E) [F.Faithful] (G : D ⥤ E) [G.Faithful] (obj : C -> D)
    (h_obj : forall X, G.obj (obj X) = F.obj X) (map : forall {X Y}, (X ⟶ Y) -> (obj X ⟶ obj Y))
    (h_map : forall {X Y} {f : X ⟶ Y}, G.map (map f) ≍ F.map f) :
    Faithful.div F G obj @h_obj @map @h_map ⋙ G = F := by
  obtain ⟨F_obj, _, _, _⟩ := F; obtain ⟨G_obj, _, _, _⟩ := G
  unfold Faithful.div Functor.comp
  have : F_obj = G_obj ∘ obj := (funext h_obj).symm
  subst this
  congr
  simp only [Function.comp_apply, heq_eq_eq] at h_map
  ext
  exact h_map

/--
theorem `Faithful.div_faithful` / 定理 `Faithful.div_faithful`

English:
theorem Faithful.div_faithful
  statement: (F : C ⥤ E) [F.Faithful] (G : D ⥤ E) [G.Faithful] (obj : C -> D)
  proof: (Faithful.div_comp F G _ h_obj _ @h_map).faithful_of_comp

中文:
定理 忠实.div_faithful
  结论: (F : C ⥤ E) [F.忠实] (G : D ⥤ E) [G.忠实] (obj : C -> D)
  证明: (Faithful.div_comp F G _ h_obj _ @h_map).faithful_of_comp

Depends on / 依赖: Faithful, Faithful.div_comp, div_comp, faithful_of_comp, h_map, h_obj
-/
theorem Faithful.div_faithful (F : C ⥤ E) [F.Faithful] (G : D ⥤ E) [G.Faithful] (obj : C -> D)
    (h_obj : forall X, G.obj (obj X) = F.obj X) (map : forall {X Y}, (X ⟶ Y) -> (obj X ⟶ obj Y))
    (h_map : forall {X Y} {f : X ⟶ Y}, G.map (map f) ≍ F.map f) :
    Functor.Faithful (Faithful.div F G obj @h_obj @map @h_map) :=
  (Faithful.div_comp F G _ h_obj _ @h_map).faithful_of_comp

/--
Instance `Full.comp` / 实例 `Full.comp`

English:
instance Full.comp
  signature: [Full F] [Full G]
  body: ⟨F.preimage (G.preimage f), by simp⟩

中文:
实例 满.comp
  签名: [满 F] [满 G]
  定义体: ⟨F.preimage (G.preimage f), by simp⟩

Depends on / 依赖: F.preimage, G.preimage, preimage
-/
instance Full.comp [Full F] [Full G] : Full (F ⋙ G) where
  map_surjective f := ⟨F.preimage (G.preimage f), by simp⟩

/--
lemma `Full.of_comp_faithful` / 引理 `Full.of_comp_faithful`

English:
lemma Full.of_comp_faithful
  given: [Full <| F ⋙ G] [G.Faithful]
  statement: Full F where
  proof: ⟨(F ⋙ G).preimage (G.map f), G.map_injective ((F ⋙ G).map_preimage _)⟩

中文:
引理 满.of_comp_faithful
  条件: [满 <| F ⋙ G] [G.忠实]
  结论: 满 F where
  证明: ⟨(F ⋙ G).preimage (G.map f), G.map_injective ((F ⋙ G).map_preimage _)⟩

Depends on / 依赖: G.map, G.map_injective, HasImage, map_injective, map_preimage, preimage
-/
lemma Full.of_comp_faithful [Full <| F ⋙ G] [G.Faithful] : Full F where
  map_surjective f := ⟨(F ⋙ G).preimage (G.map f), G.map_injective ((F ⋙ G).map_preimage _)⟩

/--
lemma `Full.of_comp_faithful_iso` / 引理 `Full.of_comp_faithful_iso`

English:
lemma Full.of_comp_faithful_iso
  statement: {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E} [Full H] [G.Faithful]
  proof: by
  have := Full.of_iso h.symm
  exact Full.of_comp_faithful F G

中文:
引理 满.of_comp_faithful_iso
  结论: {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E} [满 H] [G.忠实]
  证明: by
  have := Full.of_iso h.symm
  exact Full.of_comp_faithful F G

Depends on / 依赖: Full.of_comp_faithful, Full.of_iso, h.symm, of_comp_faithful, of_iso
-/
lemma Full.of_comp_faithful_iso {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E} [Full H] [G.Faithful]
    (h : F ⋙ G ≅ H) : Full F := by
  have := Full.of_iso h.symm
  exact Full.of_comp_faithful F G

/--
Definition of `fullyFaithfulCancelRight` / `fullyFaithfulCancelRight` 的定义

English:
definition fullyFaithfulCancelRight
  signature: {F G : C ⥤ D} (H : D ⥤ E) [Full H] [H.Faithful]
  body: NatIso.ofComponents (fun X => H.preimageIso (comp_iso.app X)) fun f =>
    H.map_injective (by simpa using! comp_iso.hom.naturality f)

@[simp]

中文:
定义 fullyFaithfulCancelRight
  签名: {F G : C ⥤ D} (H : D ⥤ E) [满 H] [H.忠实]
  定义体: NatIso.ofComponents (fun X => H.preimageIso (comp_iso.app X)) fun f =>
    H.map_injective (by simpa using! comp_iso.hom.naturality f)

@[simp]

Depends on / 依赖: H.map_injective, H.preimageIso, NatIso, NatIso.ofComponents, comp_iso, comp_iso.app, comp_iso.hom.naturality, map_injective, naturality, ofComponents, preimageIso
-/
noncomputable def fullyFaithfulCancelRight {F G : C ⥤ D} (H : D ⥤ E) [Full H] [H.Faithful]
    (comp_iso : F ⋙ H ≅ G ⋙ H) : F ≅ G :=
  NatIso.ofComponents (fun X => H.preimageIso (comp_iso.app X)) fun f =>
    H.map_injective (by simpa using! comp_iso.hom.naturality f)

@[simp]
/--
theorem `fullyFaithfulCancelRight_hom_app` / 定理 `fullyFaithfulCancelRight_hom_app`

English:
theorem fullyFaithfulCancelRight_hom_app
  statement: {F G : C ⥤ D} {H : D ⥤ E} [Full H] [H.Faithful]
  proof: rfl

@[simp]

中文:
定理 fullyFaithfulCancelRight_hom_app
  结论: {F G : C ⥤ D} {H : D ⥤ E} [满 H] [H.忠实]
  证明: rfl

@[simp]
-/
theorem fullyFaithfulCancelRight_hom_app {F G : C ⥤ D} {H : D ⥤ E} [Full H] [H.Faithful]
    (comp_iso : F ⋙ H ≅ G ⋙ H) (X : C) :
    (fullyFaithfulCancelRight H comp_iso).hom.app X = H.preimage (comp_iso.hom.app X) :=
  rfl

@[simp]
/--
theorem `fullyFaithfulCancelRight_inv_app` / 定理 `fullyFaithfulCancelRight_inv_app`

English:
theorem fullyFaithfulCancelRight_inv_app
  statement: {F G : C ⥤ D} {H : D ⥤ E} [Full H] [H.Faithful]
  proof: rfl

中文:
定理 fullyFaithfulCancelRight_inv_app
  结论: {F G : C ⥤ D} {H : D ⥤ E} [满 H] [H.忠实]
  证明: rfl
-/
theorem fullyFaithfulCancelRight_inv_app {F G : C ⥤ D} {H : D ⥤ E} [Full H] [H.Faithful]
    (comp_iso : F ⋙ H ≅ G ⋙ H) (X : C) :
    (fullyFaithfulCancelRight H comp_iso).inv.app X = H.preimage (comp_iso.inv.app X) :=
  rfl

end Functor
end CategoryTheory
