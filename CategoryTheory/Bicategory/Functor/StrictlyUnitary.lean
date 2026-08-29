/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor

/-!
# Strictly unitary lax functors and pseudofunctors

In this file, we define strictly unitary lax functors and
strictly unitary pseudofunctors between bicategories.

A lax functor `F` is said to be *strictly unitary* (sometimes, it is also
called *normal*) if there is an equality `F.map (𝟙 X) = 𝟙 (F.obj X)` and the
unit 2-morphism `𝟙 (F.obj X) ⟶ F.map (𝟙 X)` is the identity 2-morphism induced
by this equality.

A pseudofunctor is called *strictly unitary* (or a *normal homomorphism*) if it
satisfies the same condition (i.e. its "underlying" lax functor is strictly
unitary).

## References
- [Kerodon, section 2.2.2.4](https://kerodon.net/tag/008G)

## TODOs
* Define lax-composable (resp. pseudo-composable) arrows as strictly unitary
  lax (resp. pseudo-) functors out of `LocallyDiscrete Fin n`.
* Define identity-component oplax natural transformations ("icons") between
  strictly unitary pseudofunctors and construct a bicategory structure on
  bicategories, strictly unitary pseudofunctors and icons.
* Construct the Duskin nerve of a bicategory using lax-composable arrows
* Construct the 2-nerve of a bicategory using pseudo-composable arrows

-/

@[expose] public section

namespace CategoryTheory

open Category Bicategory

open Bicategory

universe w₁ w₂ w₃ w₄ v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {B : Type u₁} [Bicategory.{w₁, v₁} B]
  {C : Type u₂} [Bicategory.{w₂, v₂} C]
  {D : Type u₃} [Bicategory.{w₃, v₃} D]

variable (B C)

/-- A strictly unitary lax functor `F` between bicategories `B` and `C` is a
lax functor `F` from `B` to `C` such that the structure 2-morphism
`𝟙 (obj X) ⟶ map (𝟙 X)` is in fact an identity 2-morphism for every `X : B`. -/
@[kerodon 008R]
/--
Definition of `StrictlyUnitaryLaxFunctor` / `StrictlyUnitaryLaxFunctor` 的定义

English:
structure StrictlyUnitaryLaxFunctor
  parameters: extends B ⥤ᴸ C
  extends: B ⥤ᴸ C
  axioms and operations (2):
    - map_id((X : B)) : map (𝟙 X) = 𝟙 (obj X)  [default: by rfl_cat]
    - mapId_eq_eqToHom((X : B)) : (mapId X) = eqToHom (map_id X).symm  [default: by cat_disch]

中文:
结构 StrictlyUnitaryLaxFunctor
  参数: extends B ⥤ᴸ C
  继承: B ⥤ᴸ C
  公理与运算 (2 个):
    - map_id((X : B)) : map (𝟙 X) = 𝟙 (obj X)  [默认: by rfl_cat]
    - mapId_eq_eqToHom((X : B)) : (mapId X) = eqToHom (map_id X).symm  [默认: by cat_disch]

Depends on / 依赖: cat_disch, eqToHom, mapId_eq_eqToHom, map_id, rfl_cat
-/
structure StrictlyUnitaryLaxFunctor extends B ⥤ᴸ C where
  map_id (X : B) : map (𝟙 X) = 𝟙 (obj X) := by rfl_cat
  mapId_eq_eqToHom (X : B) : (mapId X) = eqToHom (map_id X).symm := by cat_disch


/--
Definition of `StrictlyUnitaryLaxFunctorCore` / `StrictlyUnitaryLaxFunctorCore` 的定义

English:
structure StrictlyUnitaryLaxFunctorCore
  parameters: where
  axioms and operations (12):
    - obj : B -> C
    - map : forall {X Y : B}, (X ⟶ Y) -> (obj X ⟶ obj Y)
    - map_id : forall (X : B), map (𝟙 X) = 𝟙 (obj X)  [default: by cat_disch]
    - map₂ : forall {a b : B} {f g : a ⟶ b}, (f ⟶ g) -> (map f ⟶ map g)
    - map₂_id : forall {a b : B} (f : a ⟶ b), map₂ (𝟙 f) = 𝟙 (map f)  [default: by cat_disch]
    - map₂_comp : forall {a b : B} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h), map₂ (η ≫ θ) = map₂ η ≫ map₂ θ  [default: by cat_disch]
    - mapComp : forall {a b c : B} (f : a ⟶ b) (g : b ⟶ c), map f ≫ map g ⟶ map (f ≫ g)
    - mapComp_naturality_left : forall {a b c : B} {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c), mapComp f g ≫ map₂ (η ▷ g) = map₂ η ▷ map g ≫ mapComp f' g  [default: by cat_disch]
    - mapComp_naturality_right : forall {a b c : B} (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g'), mapComp f g ≫ map₂ (f ◁ η) = map f ◁ map₂ η ≫ mapComp f g'  [default: by cat_disch]
    - map₂_leftUnitor : forall {a b : B} (f : a ⟶ b), map₂ (fun_ f).inv = (fun_ (map f)).inv ≫ eqToHom (by rw [map_id a]) ≫ mapComp (𝟙 a) f  [default: by cat_disch]
    - map₂_rightUnitor : forall {a b : B} (f : a ⟶ b), map₂ (ρ_ f).inv = (ρ_ (map f)).inv ≫ eqToHom (by rw [map_id b]) ≫ mapComp f (𝟙 b)  [default: by cat_disch]
    - map₂_associator : forall {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d), mapComp f g ▷ map h ≫ mapComp (f ≫ g) h ≫ map₂ (α_ f g h).hom = (α_ (map f) (map g) (map h)).hom ≫ map f ◁ mapComp g h ≫ mapComp f (g ≫ h)  [default: by cat_disch]

中文:
结构 StrictlyUnitaryLaxFunctorCore
  参数: where
  公理与运算 (12 个):
    - obj : B -> C
    - map : 对任意 {X Y : B}, (X ⟶ Y) -> (obj X ⟶ obj Y)
    - map_id : 对任意 (X : B), map (𝟙 X) = 𝟙 (obj X)  [默认: by cat_disch]
    - map₂ : 对任意 {a b : B} {f g : a ⟶ b}, (f ⟶ g) -> (map f ⟶ map g)
    - map₂_id : 对任意 {a b : B} (f : a ⟶ b), map₂ (𝟙 f) = 𝟙 (map f)  [默认: by cat_disch]
    - map₂_comp : 对任意 {a b : B} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h), map₂ (η ≫ θ) = map₂ η ≫ map₂ θ  [默认: by cat_disch]
    - mapComp : 对任意 {a b c : B} (f : a ⟶ b) (g : b ⟶ c), map f ≫ map g ⟶ map (f ≫ g)
    - mapComp_naturality_left : 对任意 {a b c : B} {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c), mapComp f g ≫ map₂ (η ▷ g) = map₂ η ▷ map g ≫ mapComp f' g  [默认: by cat_disch]
    - mapComp_naturality_right : 对任意 {a b c : B} (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g'), mapComp f g ≫ map₂ (f ◁ η) = map f ◁ map₂ η ≫ mapComp f g'  [默认: by cat_disch]
    - map₂_leftUnitor : 对任意 {a b : B} (f : a ⟶ b), map₂ (fun_ f).inv = (fun_ (map f)).inv ≫ eqToHom (by rw [map_id a]) ≫ mapComp (𝟙 a) f  [默认: by cat_disch]
    - map₂_rightUnitor : 对任意 {a b : B} (f : a ⟶ b), map₂ (ρ_ f).inv = (ρ_ (map f)).inv ≫ eqToHom (by rw [map_id b]) ≫ mapComp f (𝟙 b)  [默认: by cat_disch]
    - map₂_associator : 对任意 {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d), mapComp f g ▷ map h ≫ mapComp (f ≫ g) h ≫ map₂ (α_ f g h).hom = (α_ (map f) (map g) (map h)).hom ≫ map f ◁ mapComp g h ≫ mapComp f (g ≫ h)  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure StrictlyUnitaryLaxFunctorCore where
  /-- action on objects -/
  obj : B -> C
  /-- action on 1-morphisms -/
  map : forall {X Y : B}, (X ⟶ Y) -> (obj X ⟶ obj Y)
  map_id : forall (X : B), map (𝟙 X) = 𝟙 (obj X) := by cat_disch
  /-- action on 2-morphisms -/
  map₂ : forall {a b : B} {f g : a ⟶ b}, (f ⟶ g) -> (map f ⟶ map g)
  map₂_id : forall {a b : B} (f : a ⟶ b), map₂ (𝟙 f) = 𝟙 (map f) := by cat_disch
  map₂_comp :
      forall {a b : B} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h),
        map₂ (η ≫ θ) = map₂ η ≫ map₂ θ := by
    cat_disch
  /-- structure 2-morphism for composition of 1-morphism -/
  mapComp : forall {a b c : B} (f : a ⟶ b) (g : b ⟶ c),
    map f ≫ map g ⟶ map (f ≫ g)
  mapComp_naturality_left :
      forall {a b c : B} {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c),
        mapComp f g ≫ map₂ (η ▷ g) = map₂ η ▷ map g ≫ mapComp f' g := by
    cat_disch
  mapComp_naturality_right :
      forall {a b c : B} (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g'),
        mapComp f g ≫ map₂ (f ◁ η) = map f ◁ map₂ η ≫ mapComp f g' := by
    cat_disch
  map₂_leftUnitor :
      forall {a b : B} (f : a ⟶ b),
        map₂ (fun_ f).inv =
        (fun_ (map f)).inv ≫ eqToHom (by rw [map_id a]) ≫ mapComp (𝟙 a) f := by
    cat_disch
  map₂_rightUnitor :
      forall {a b : B} (f : a ⟶ b),
        map₂ (ρ_ f).inv =
        (ρ_ (map f)).inv ≫ eqToHom (by rw [map_id b]) ≫ mapComp f (𝟙 b) := by
    cat_disch
  map₂_associator :
      forall {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d),
        mapComp f g ▷ map h ≫ mapComp (f ≫ g) h ≫ map₂ (α_ f g h).hom =
        (α_ (map f) (map g) (map h)).hom ≫ map f ◁ mapComp g h ≫
          mapComp f (g ≫ h) := by
    cat_disch

namespace StrictlyUnitaryLaxFunctor

variable {B C}

/-- An alternate constructor for strictly unitary lax functors that does not
require the `mapId` fields, and that adapts the `map₂_leftUnitor` and
`map₂_rightUnitor` to the fact that the functor is strictly unitary. -/
@[simps]
/--
Definition of `mk'` / `mk'` 的定义

English:
definition mk'
  signature: (S : StrictlyUnitaryLaxFunctorCore B C)
  body: S.obj
  map := S.map
  map_id := S.map_id
  mapId x := eqToHom (S.map_id x).symm
  mapId_eq_eqToHom x := rfl
  map₂ := S.map₂
  map₂_id := S.map₂_id
  map₂_comp := S.map₂_comp
  mapComp := S.mapComp
  mapComp_naturality_left := S.mapComp_naturality_left
  mapComp_naturality_right := S.mapComp_natura

中文:
定义 mk'
  签名: (S : StrictlyUnitaryLaxFunctorCore B C)
  定义体: S.obj
  map := S.map
  map_id := S.map_id
  mapId x := eqToHom (S.map_id x).symm
  mapId_eq_eqToHom x := rfl
  map₂ := S.map₂
  map₂_id := S.map₂_id
  map₂_comp := S.map₂_comp
  mapComp := S.mapComp
  mapComp_naturality_left := S.mapComp_naturality_left
  mapComp_naturality_right := S.mapComp_natura

Depends on / 依赖: S.obj
-/
def mk' (S : StrictlyUnitaryLaxFunctorCore B C) :
    StrictlyUnitaryLaxFunctor B C where
  obj := S.obj
  map := S.map
  map_id := S.map_id
  mapId x := eqToHom (S.map_id x).symm
  mapId_eq_eqToHom x := rfl
  map₂ := S.map₂
  map₂_id := S.map₂_id
  map₂_comp := S.map₂_comp
  mapComp := S.mapComp
  mapComp_naturality_left := S.mapComp_naturality_left
  mapComp_naturality_right := S.mapComp_naturality_right
  map₂_leftUnitor f := by
    simpa using S.map₂_leftUnitor f
  map₂_rightUnitor f := by
    simpa using S.map₂_rightUnitor f
  map₂_associator f g h := by
    simpa using S.map₂_associator f g h

/--
Instance `mapId_isIso` / 实例 `mapId_isIso`

English:
instance mapId_isIso
  signature: (F : StrictlyUnitaryLaxFunctor B C) (x : B)
  body: by
  rw [mapId_eq_eqToHom]
  infer_instance

中文:
实例 mapId_isIso
  签名: (F : StrictlyUnitaryLaxFunctor B C) (x : B)
  定义体: by
  rw [mapId_eq_eqToHom]
  infer_instance

Depends on / 依赖: infer_instance, mapId_eq_eqToHom
-/
instance mapId_isIso (F : StrictlyUnitaryLaxFunctor B C) (x : B) :
    IsIso (F.mapId x) := by
  rw [mapId_eq_eqToHom]
  infer_instance

/-- Promote the morphism `F.mapId x : 𝟙 (F.obj x) ⟶ F.map (𝟙 x)`
to an isomorphism when `F` is strictly unitary. -/
@[simps]
/--
Definition of `mapIdIso` / `mapIdIso` 的定义

English:
definition mapIdIso
  signature: (F : StrictlyUnitaryLaxFunctor B C) (x : B)
  body: F.mapId x
  inv := eqToHom (F.map_id x)
  hom_inv_id := by simp [F.mapId_eq_eqToHom]
  inv_hom_id := by simp [F.mapId_eq_eqToHom]

中文:
定义 mapIdIso
  签名: (F : StrictlyUnitaryLaxFunctor B C) (x : B)
  定义体: F.mapId x
  inv := eqToHom (F.map_id x)
  hom_inv_id := by simp [F.mapId_eq_eqToHom]
  inv_hom_id := by simp [F.mapId_eq_eqToHom]

Depends on / 依赖: F.mapId
-/
def mapIdIso (F : StrictlyUnitaryLaxFunctor B C) (x : B) :
    𝟙 (F.obj x) ≅ F.map (𝟙 x) where
  hom := F.mapId x
  inv := eqToHom (F.map_id x)
  hom_inv_id := by simp [F.mapId_eq_eqToHom]
  inv_hom_id := by simp [F.mapId_eq_eqToHom]

variable (B) in
/-- The identity `StrictlyUnitaryLaxFunctor`. -/
@[simps!]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : StrictlyUnitaryLaxFunctor B B where
  body: LaxFunctor.id B
  map_id _ := rfl
  mapId_eq_eqToHom _ := rfl

中文:
定义 id
  签名: : StrictlyUnitaryLaxFunctor B B where
  定义体: LaxFunctor.id B
  map_id _ := rfl
  mapId_eq_eqToHom _ := rfl

Depends on / 依赖: LaxFunctor, LaxFunctor.id
-/
def id : StrictlyUnitaryLaxFunctor B B where
  __ := LaxFunctor.id B
  map_id _ := rfl
  mapId_eq_eqToHom _ := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Composition of `StrictlyUnitaryLaxFunctor`. -/
@[simps!]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (F : StrictlyUnitaryLaxFunctor B C)
  body: LaxFunctor.comp F.toLaxFunctor G.toLaxFunctor
  map_id _ := by simp [StrictlyUnitaryLaxFunctor.map_id]
  mapId_eq_eqToHom _ := by
    simp [StrictlyUnitaryLaxFunctor.mapId_eq_eqToHom,
      PrelaxFunctor.map₂_eqToHom]

中文:
定义 comp
  签名: (F : StrictlyUnitaryLaxFunctor B C)
  定义体: LaxFunctor.comp F.toLaxFunctor G.toLaxFunctor
  map_id _ := by simp [StrictlyUnitaryLaxFunctor.map_id]
  mapId_eq_eqToHom _ := by
    simp [StrictlyUnitaryLaxFunctor.mapId_eq_eqToHom,
      PrelaxFunctor.map₂_eqToHom]

Depends on / 依赖: F.toLaxFunctor, G.toLaxFunctor, LaxFunctor, LaxFunctor.comp, toLaxFunctor
-/
def comp (F : StrictlyUnitaryLaxFunctor B C)
    (G : StrictlyUnitaryLaxFunctor C D) :
    StrictlyUnitaryLaxFunctor B D where
  __ := LaxFunctor.comp F.toLaxFunctor G.toLaxFunctor
  map_id _ := by simp [StrictlyUnitaryLaxFunctor.map_id]
  mapId_eq_eqToHom _ := by
    simp [StrictlyUnitaryLaxFunctor.mapId_eq_eqToHom,
      PrelaxFunctor.map₂_eqToHom]

section
attribute [local ext] StrictlyUnitaryLaxFunctor

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `comp_id` / 引理 `comp_id`

English:
lemma comp_id
  given: (F : StrictlyUnitaryLaxFunctor B C)
  proof: by
  ext
  · simp
  all_goals
  · rw [heq_iff_eq]
    ext
    simp

中文:
引理 comp_id
  条件: (F : StrictlyUnitaryLaxFunctor B C)
  证明: by
  ext
  · simp
  all_goals
  · rw [heq_iff_eq]
    ext
    simp

Depends on / 依赖: all_goals, heq_iff_eq
-/
lemma comp_id (F : StrictlyUnitaryLaxFunctor B C) :
    F.comp (.id C) = F := by
  ext
  · simp
  all_goals
  · rw [heq_iff_eq]
    ext
    simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `id_comp` / 引理 `id_comp`

English:
lemma id_comp
  given: (F : StrictlyUnitaryLaxFunctor B C)
  proof: by
  ext
  · simp
  all_goals
  · rw [heq_iff_eq]
    ext
    simp

中文:
引理 id_comp
  条件: (F : StrictlyUnitaryLaxFunctor B C)
  证明: by
  ext
  · simp
  all_goals
  · rw [heq_iff_eq]
    ext
    simp

Depends on / 依赖: all_goals, heq_iff_eq
-/
lemma id_comp (F : StrictlyUnitaryLaxFunctor B C) :
    (StrictlyUnitaryLaxFunctor.id B).comp F = F := by
  ext
  · simp
  all_goals
  · rw [heq_iff_eq]
    ext
    simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `comp_assoc` / 引理 `comp_assoc`

English:
lemma comp_assoc
  statement: {E : Type u₄} [Bicategory.{w₄, v₄} E]
  proof: by
  ext
  · simp
  all_goals
  · rw [heq_iff_eq]
    ext
    simp

中文:
引理 comp_assoc
  结论: {E : 类型u₄} [Bicategory.{w₄, v₄} E]
  证明: by
  ext
  · simp
  all_goals
  · rw [heq_iff_eq]
    ext
    simp

Depends on / 依赖: all_goals, heq_iff_eq
-/
lemma comp_assoc {E : Type u₄} [Bicategory.{w₄, v₄} E]
    (F : StrictlyUnitaryLaxFunctor B C) (G : StrictlyUnitaryLaxFunctor C D)
    (H : StrictlyUnitaryLaxFunctor D E) :
    (F.comp G).comp H = F.comp (G.comp H) := by
  ext
  · simp
  all_goals
  · rw [heq_iff_eq]
    ext
    simp

end

end StrictlyUnitaryLaxFunctor

/-- A strictly unitary pseudofunctor (sometimes called a "normal homomorphism")
`F` between bicategories `B` and `C` is a pseudofunctor `F` from `B` to `C`
such that the structure isomorphism `map (𝟙 X) ≅ 𝟙 (F.obj X)` is in fact an
identity 2-isomorphism for every `X : B` (in particular, there is an equality
`F.map (𝟙 X) = 𝟙 (F.obj X)`). -/
@[kerodon 008R]
/--
Definition of `StrictlyUnitaryPseudofunctor` / `StrictlyUnitaryPseudofunctor` 的定义

English:
structure StrictlyUnitaryPseudofunctor
  parameters: extends Pseudofunctor B C
  extends: Pseudofunctor B C
  axioms and operations (2):
    - map_id((X : B)) : map (𝟙 X) = 𝟙 (obj X)  [default: by rfl_cat]
    - mapId_eq_eqToIso((X : B)) : (mapId X) = eqToIso (map_id X)  [default: by cat_disch]

中文:
结构 StrictlyUnitaryPseudofunctor
  参数: extends Pseudofunctor B C
  继承: Pseudofunctor B C
  公理与运算 (2 个):
    - map_id((X : B)) : map (𝟙 X) = 𝟙 (obj X)  [默认: by rfl_cat]
    - mapId_eq_eqToIso((X : B)) : (mapId X) = eqToIso (map_id X)  [默认: by cat_disch]

Depends on / 依赖: cat_disch, eqToIso, mapId_eq_eqToIso, map_id, rfl_cat
-/
structure StrictlyUnitaryPseudofunctor extends Pseudofunctor B C where
  map_id (X : B) : map (𝟙 X) = 𝟙 (obj X) := by rfl_cat
  mapId_eq_eqToIso (X : B) : (mapId X) = eqToIso (map_id X) := by cat_disch

/--
Definition of `StrictlyUnitaryPseudofunctorCore` / `StrictlyUnitaryPseudofunctorCore` 的定义

English:
structure StrictlyUnitaryPseudofunctorCore
  parameters: where
  axioms and operations (12):
    - obj : B -> C
    - map : forall {X Y : B}, (X ⟶ Y) -> (obj X ⟶ obj Y)
    - map_id : forall (X : B), map (𝟙 X) = 𝟙 (obj X)  [default: by rfl_cat]
    - map₂ : forall {a b : B} {f g : a ⟶ b}, (f ⟶ g) -> (map f ⟶ map g)
    - map₂_id : forall {a b : B} (f : a ⟶ b), map₂ (𝟙 f) = 𝟙 (map f)  [default: by cat_disch]
    - map₂_comp : forall {a b : B} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h), map₂ (η ≫ θ) = map₂ η ≫ map₂ θ  [default: by cat_disch]
    - mapComp : forall {a b c : B} (f : a ⟶ b) (g : b ⟶ c), map (f ≫ g) ≅ map f ≫ map g
    - map₂_whisker_left : forall {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h), map₂ (f ◁ η) = (mapComp f g).hom ≫ map f ◁ map₂ η ≫ (mapComp f h).inv  [default: by cat_disch]
    - map₂_whisker_right : forall {a b c : B} {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c), map₂ (η ▷ h) = (mapComp f h).hom ≫ map₂ η ▷ map h ≫ (mapComp g h).inv  [default: by cat_disch]
    - map₂_left_unitor : forall {a b : B} (f : a ⟶ b), map₂ (fun_ f).hom = (mapComp (𝟙 a) f).hom ≫ eqToHom (by rw [map_id a]) ≫ (fun_ (map f)).hom  [default: by cat_disch]
    - map₂_right_unitor : forall {a b : B} (f : a ⟶ b), map₂ (ρ_ f).hom = (mapComp f (𝟙 b)).hom ≫ eqToHom (by rw [map_id b]) ≫ (ρ_ (map f)).hom  [default: by cat_disch]
    - map₂_associator : forall {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d), map₂ (α_ f g h).hom = (mapComp (f ≫ g) h).hom ≫ (mapComp f g).hom ▷ map h ≫ (α_ (map f) (map g) (map h)).hom ≫ map f ◁ (mapComp g h).inv ≫ (mapComp f (g ≫ h)).inv  [default: by cat_disch]

中文:
结构 StrictlyUnitaryPseudofunctorCore
  参数: where
  公理与运算 (12 个):
    - obj : B -> C
    - map : 对任意 {X Y : B}, (X ⟶ Y) -> (obj X ⟶ obj Y)
    - map_id : 对任意 (X : B), map (𝟙 X) = 𝟙 (obj X)  [默认: by rfl_cat]
    - map₂ : 对任意 {a b : B} {f g : a ⟶ b}, (f ⟶ g) -> (map f ⟶ map g)
    - map₂_id : 对任意 {a b : B} (f : a ⟶ b), map₂ (𝟙 f) = 𝟙 (map f)  [默认: by cat_disch]
    - map₂_comp : 对任意 {a b : B} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h), map₂ (η ≫ θ) = map₂ η ≫ map₂ θ  [默认: by cat_disch]
    - mapComp : 对任意 {a b c : B} (f : a ⟶ b) (g : b ⟶ c), map (f ≫ g) ≅ map f ≫ map g
    - map₂_whisker_left : 对任意 {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h), map₂ (f ◁ η) = (mapComp f g).hom ≫ map f ◁ map₂ η ≫ (mapComp f h).inv  [默认: by cat_disch]
    - map₂_whisker_right : 对任意 {a b c : B} {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c), map₂ (η ▷ h) = (mapComp f h).hom ≫ map₂ η ▷ map h ≫ (mapComp g h).inv  [默认: by cat_disch]
    - map₂_left_unitor : 对任意 {a b : B} (f : a ⟶ b), map₂ (fun_ f).hom = (mapComp (𝟙 a) f).hom ≫ eqToHom (by rw [map_id a]) ≫ (fun_ (map f)).hom  [默认: by cat_disch]
    - map₂_right_unitor : 对任意 {a b : B} (f : a ⟶ b), map₂ (ρ_ f).hom = (mapComp f (𝟙 b)).hom ≫ eqToHom (by rw [map_id b]) ≫ (ρ_ (map f)).hom  [默认: by cat_disch]
    - map₂_associator : 对任意 {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d), map₂ (α_ f g h).hom = (mapComp (f ≫ g) h).hom ≫ (mapComp f g).hom ▷ map h ≫ (α_ (map f) (map g) (map h)).hom ≫ map f ◁ (mapComp g h).inv ≫ (mapComp f (g ≫ h)).inv  [默认: by cat_disch]

Depends on / 依赖: rfl_cat
-/
structure StrictlyUnitaryPseudofunctorCore where
  /-- action on objects -/
  obj : B -> C
  /-- action on 1-morphisms -/
  map : forall {X Y : B}, (X ⟶ Y) -> (obj X ⟶ obj Y)
  map_id : forall (X : B), map (𝟙 X) = 𝟙 (obj X) := by rfl_cat
  /-- action on 2-morphisms -/
  map₂ : forall {a b : B} {f g : a ⟶ b}, (f ⟶ g) -> (map f ⟶ map g)
  map₂_id : forall {a b : B} (f : a ⟶ b), map₂ (𝟙 f) = 𝟙 (map f) := by cat_disch
  map₂_comp :
      forall {a b : B} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h),
        map₂ (η ≫ θ) = map₂ η ≫ map₂ θ := by
    cat_disch
  /-- structure 2-isomorphism for composition of 1-morphisms -/
  mapComp : forall {a b c : B} (f : a ⟶ b) (g : b ⟶ c),
    map (f ≫ g) ≅ map f ≫ map g
  map₂_whisker_left :
      forall {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h),
        map₂ (f ◁ η) =
        (mapComp f g).hom ≫ map f ◁ map₂ η ≫ (mapComp f h).inv := by
    cat_disch
  map₂_whisker_right :
      forall {a b c : B} {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c),
        map₂ (η ▷ h) =
        (mapComp f h).hom ≫ map₂ η ▷ map h ≫ (mapComp g h).inv := by
    cat_disch
  map₂_left_unitor :
      forall {a b : B} (f : a ⟶ b),
        map₂ (fun_ f).hom =
        (mapComp (𝟙 a) f).hom ≫ eqToHom (by rw [map_id a]) ≫
          (fun_ (map f)).hom := by
    cat_disch
  map₂_right_unitor :
      forall {a b : B} (f : a ⟶ b),
        map₂ (ρ_ f).hom =
        (mapComp f (𝟙 b)).hom ≫ eqToHom (by rw [map_id b]) ≫
          (ρ_ (map f)).hom := by
    cat_disch
  map₂_associator :
      forall {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d),
        map₂ (α_ f g h).hom =
          (mapComp (f ≫ g) h).hom ≫ (mapComp f g).hom ▷ map h ≫
          (α_ (map f) (map g) (map h)).hom ≫ map f ◁ (mapComp g h).inv ≫
          (mapComp f (g ≫ h)).inv := by
    cat_disch

namespace StrictlyUnitaryPseudofunctor

variable {B C}

/-- An alternate constructor for strictly unitary pseudofunctors that does not
require the `mapId` fields, and that adapts the `map₂_leftUnitor` and
`map₂_rightUnitor` to the fact that the functor is strictly unitary. -/
@[simps]
/--
Definition of `mk'` / `mk'` 的定义

English:
definition mk'
  signature: (S : StrictlyUnitaryPseudofunctorCore B C)
  body: S.obj
  map := S.map
  map_id := S.map_id
  mapId x := eqToIso (S.map_id x)
  mapId_eq_eqToIso x := rfl
  map₂ := S.map₂
  map₂_id := S.map₂_id
  map₂_comp := S.map₂_comp
  mapComp := S.mapComp
  map₂_left_unitor f := by
    simpa using S.map₂_left_unitor f
  map₂_right_unitor f := by
    simpa usin

中文:
定义 mk'
  签名: (S : StrictlyUnitaryPseudofunctorCore B C)
  定义体: S.obj
  map := S.map
  map_id := S.map_id
  mapId x := eqToIso (S.map_id x)
  mapId_eq_eqToIso x := rfl
  map₂ := S.map₂
  map₂_id := S.map₂_id
  map₂_comp := S.map₂_comp
  mapComp := S.mapComp
  map₂_left_unitor f := by
    simpa using S.map₂_left_unitor f
  map₂_right_unitor f := by
    simpa usin

Depends on / 依赖: S.obj
-/
def mk' (S : StrictlyUnitaryPseudofunctorCore B C) :
    StrictlyUnitaryPseudofunctor B C where
  obj := S.obj
  map := S.map
  map_id := S.map_id
  mapId x := eqToIso (S.map_id x)
  mapId_eq_eqToIso x := rfl
  map₂ := S.map₂
  map₂_id := S.map₂_id
  map₂_comp := S.map₂_comp
  mapComp := S.mapComp
  map₂_left_unitor f := by
    simpa using S.map₂_left_unitor f
  map₂_right_unitor f := by
    simpa using S.map₂_right_unitor f
  map₂_associator f g h := by
    simpa using S.map₂_associator f g h
  map₂_whisker_left f _ _ η := by
    simpa using S.map₂_whisker_left f η
  map₂_whisker_right η f := by
    simpa using S.map₂_whisker_right η f

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `toStrictlyUnitaryLaxFunctor` / `toStrictlyUnitaryLaxFunctor` 的定义

English:
definition toStrictlyUnitaryLaxFunctor
  signature: (F : StrictlyUnitaryPseudofunctor B C)
  body: F.toPseudofunctor.toLax
  map_id x := by simp [F.map_id]
  mapId_eq_eqToHom x := by simp [F.mapId_eq_eqToIso]

中文:
定义 toStrictlyUnitaryLaxFunctor
  签名: (F : StrictlyUnitaryPseudofunctor B C)
  定义体: F.toPseudofunctor.toLax
  map_id x := by simp [F.map_id]
  mapId_eq_eqToHom x := by simp [F.mapId_eq_eqToIso]

Depends on / 依赖: F.toPseudofunctor.toLax, f.inv.hom, toPseudofunctor
-/
def toStrictlyUnitaryLaxFunctor (F : StrictlyUnitaryPseudofunctor B C) :
    StrictlyUnitaryLaxFunctor B C where
  __ := F.toPseudofunctor.toLax
  map_id x := by simp [F.map_id]
  mapId_eq_eqToHom x := by simp [F.mapId_eq_eqToIso]

section

variable (F : StrictlyUnitaryPseudofunctor B C)

@[simp]
/--
lemma `toStrictlyUnitaryLaxFunctor_obj` / 引理 `toStrictlyUnitaryLaxFunctor_obj`

English:
lemma toStrictlyUnitaryLaxFunctor_obj
  given: (x : B)
  proof: rfl

@[simp]

中文:
引理 toStrictlyUnitaryLaxFunctor_obj
  条件: (x : B)
  证明: rfl

@[simp]

Depends on / 依赖: f.hom.hom
-/
lemma toStrictlyUnitaryLaxFunctor_obj (x : B) :
    F.toStrictlyUnitaryLaxFunctor.obj x = F.obj x :=
  rfl

@[simp]
/--
lemma `toStrictlyUnitaryLaxFunctor_map` / 引理 `toStrictlyUnitaryLaxFunctor_map`

English:
lemma toStrictlyUnitaryLaxFunctor_map
  given: {x y : B} (f : x ⟶ y)
  proof: rfl

@[simp]

中文:
引理 toStrictlyUnitaryLaxFunctor_map
  条件: {x y : B} (f : x ⟶ y)
  证明: rfl

@[simp]
-/
lemma toStrictlyUnitaryLaxFunctor_map {x y : B} (f : x ⟶ y) :
    F.toStrictlyUnitaryLaxFunctor.map f = F.map f :=
  rfl

@[simp]
/--
lemma `toStrictlyUnitaryLaxFunctor_map₂` / 引理 `toStrictlyUnitaryLaxFunctor_map₂`

English:
lemma toStrictlyUnitaryLaxFunctor_map₂
  given: {x y : B} {f g : x ⟶ y} (η : f ⟶ g)
  proof: rfl

@[simp]

中文:
引理 toStrictlyUnitaryLaxFunctor_map₂
  条件: {x y : B} {f g : x ⟶ y} (η : f ⟶ g)
  证明: rfl

@[simp]
-/
lemma toStrictlyUnitaryLaxFunctor_map₂ {x y : B} {f g : x ⟶ y} (η : f ⟶ g) :
    F.toStrictlyUnitaryLaxFunctor.map₂ η = F.map₂ η :=
  rfl

@[simp]
/--
lemma `toStrictlyUnitaryLaxFunctor_mapComp` / 引理 `toStrictlyUnitaryLaxFunctor_mapComp`

English:
lemma toStrictlyUnitaryLaxFunctor_mapComp
  given: {x y z : B} (f : x ⟶ y) (g : y ⟶ z)
  proof: rfl

@[simp]

中文:
引理 toStrictlyUnitaryLaxFunctor_mapComp
  条件: {x y z : B} (f : x ⟶ y) (g : y ⟶ z)
  证明: rfl

@[simp]
-/
lemma toStrictlyUnitaryLaxFunctor_mapComp {x y z : B} (f : x ⟶ y) (g : y ⟶ z) :
    F.toStrictlyUnitaryLaxFunctor.mapComp f g = (F.mapComp f g).inv :=
  rfl

@[simp]
/--
lemma `toStrictlyUnitaryLaxFunctor_mapId` / 引理 `toStrictlyUnitaryLaxFunctor_mapId`

English:
lemma toStrictlyUnitaryLaxFunctor_mapId
  given: {x : B}
  proof: rfl

中文:
引理 toStrictlyUnitaryLaxFunctor_mapId
  条件: {x : B}
  证明: rfl
-/
lemma toStrictlyUnitaryLaxFunctor_mapId {x : B} :
    F.toStrictlyUnitaryLaxFunctor.mapId x = (F.mapId x).inv :=
  rfl

variable (B) in
/-- The identity `StrictlyUnitaryPseudofunctor`. -/
@[simps!]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : StrictlyUnitaryPseudofunctor B B where
  body: Pseudofunctor.id B
  map_id _ := rfl
  mapId_eq_eqToIso _ := rfl

中文:
定义 id
  签名: : StrictlyUnitaryPseudofunctor B B where
  定义体: Pseudofunctor.id B
  map_id _ := rfl
  mapId_eq_eqToIso _ := rfl

Depends on / 依赖: Pseudofunctor, Pseudofunctor.id
-/
def id : StrictlyUnitaryPseudofunctor B B where
  __ := Pseudofunctor.id B
  map_id _ := rfl
  mapId_eq_eqToIso _ := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Composition of `StrictlyUnitaryPseudofunctor`. -/
@[simps!]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (F : StrictlyUnitaryPseudofunctor B C)
  body: Pseudofunctor.comp F.toPseudofunctor G.toPseudofunctor
  map_id _ := by simp [StrictlyUnitaryPseudofunctor.map_id]
  mapId_eq_eqToIso _ := by
    ext
    simp [StrictlyUnitaryPseudofunctor.mapId_eq_eqToIso,
      PrelaxFunctor.map₂_eqToHom]

中文:
定义 comp
  签名: (F : StrictlyUnitaryPseudofunctor B C)
  定义体: Pseudofunctor.comp F.toPseudofunctor G.toPseudofunctor
  map_id _ := by simp [StrictlyUnitaryPseudofunctor.map_id]
  mapId_eq_eqToIso _ := by
    ext
    simp [StrictlyUnitaryPseudofunctor.mapId_eq_eqToIso,
      PrelaxFunctor.map₂_eqToHom]

Depends on / 依赖: F.toPseudofunctor, G.toPseudofunctor, Pseudofunctor, Pseudofunctor.comp, toPseudofunctor
-/
def comp (F : StrictlyUnitaryPseudofunctor B C)
    (G : StrictlyUnitaryPseudofunctor C D) :
    StrictlyUnitaryPseudofunctor B D where
  __ := Pseudofunctor.comp F.toPseudofunctor G.toPseudofunctor
  map_id _ := by simp [StrictlyUnitaryPseudofunctor.map_id]
  mapId_eq_eqToIso _ := by
    ext
    simp [StrictlyUnitaryPseudofunctor.mapId_eq_eqToIso,
      PrelaxFunctor.map₂_eqToHom]

end

end StrictlyUnitaryPseudofunctor

end CategoryTheory
