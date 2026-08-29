/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Functor.Basic

/-!
# Unbundled functors, as a typeclass decorating the object-level function.
-/

@[expose] public section


namespace CategoryTheory

-- declare the `v`'s first; see `CategoryTheory.Category` for an explanation
universe v v₁ v₂ v₃ u u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

-- Perhaps in the future we could redefine `Functor` in terms of this, but that isn't the
-- immediate plan.
/--
Definition of `Functorial` / `Functorial` 的定义

English:
class Functorial
  parameters: (F : C -> D)
  axioms and operations (3):
    - map((F)) : forall {X Y : C}, (X ⟶ Y) -> (F X ⟶ F Y)
    - map_id : forall {X : C}, map (𝟙 X) = 𝟙 (F X)  [default: by cat_disch]
    - map_comp : forall {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}, map (f ≫ g) = map f ≫ map g  [default: by cat_disch]

中文:
类 函子性
  参数: (F : C -> D)
  公理与运算 (3 个):
    - map((F)) : 对任意 {X Y : C}, (X ⟶ Y) -> (F X ⟶ F Y)
    - map_id : 对任意 {X : C}, map (𝟙 X) = 𝟙 (F X)  [默认: by cat_disch]
    - map_comp : 对任意 {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}, map (f ≫ g) = map f ≫ map g  [默认: by cat_disch]

Depends on / 依赖: cat_disch, hasImages_of_hasStrongEpiMonoFactorisations
-/
class Functorial (F : C -> D) : Type max v₁ v₂ u₁ u₂ where
  /-- If `F : C → D` (just a function) has `[Functorial F]`,
  we can write `map F f : F X ⟶ F Y` for the action of `F` on a morphism `f : X ⟶ Y`. -/
  map (F) : forall {X Y : C}, (X ⟶ Y) -> (F X ⟶ F Y)
  /-- A functorial map preserves identities. -/
  map_id : forall {X : C}, map (𝟙 X) = 𝟙 (F X) := by cat_disch
  /-- A functorial map preserves composition of morphisms. -/
  map_comp : forall {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}, map (f ≫ g) = map f ≫ map g := by
    cat_disch

attribute [simp, grind =] Functorial.map_id Functorial.map_comp
export Functorial (map)

namespace Functor

/--
Definition of `of` / `of` 的定义

English:
definition of
  signature: (F : C -> D) [I : Functorial.{v₁, v₂} F]
  body: { I with obj := F
           map := Functorial.map F }

中文:
定义 of
  签名: (F : C -> D) [I : 函子性.{v₁, v₂} F]
  定义体: { I with obj := F
           map := Functorial.map F }

Depends on / 依赖: Functorial, Functorial.map
-/
def of (F : C -> D) [I : Functorial.{v₁, v₂} F] : C ⥤ D :=
  { I with obj := F
           map := Functorial.map F }

end Functor

instance (F : C ⥤ D) : Functorial.{v₁, v₂} F.obj :=
  { F with map := F.map }

@[simp, grind =]
/--
theorem `map_functorial_obj` / 定理 `map_functorial_obj`

English:
theorem map_functorial_obj
  given: (F : C ⥤ D) {X Y : C} (f : X ⟶ Y)
  statement: map F.obj f = F.map f
  proof: rfl

中文:
定理 map_functorial_obj
  条件: (F : C ⥤ D) {X Y : C} (f : X ⟶ Y)
  结论: map F.obj f = F.map f
  证明: rfl
-/
theorem map_functorial_obj (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) : map F.obj f = F.map f :=
  rfl

/--
Instance `functorial_id` / 实例 `functorial_id`

English:
instance functorial_id
  signature: : Functorial.{v₁, v₁} (id : C -> C) where map f
  body: f

中文:
实例 functorial_id
  签名: : 函子性.{v₁, v₁} (id : C -> C) where map f
  定义体: f

Depends on / 依赖: hasStrongEpiImages_of_hasStrongEpiMonoFactorisations
-/
instance functorial_id : Functorial.{v₁, v₁} (id : C -> C) where map f := f

section

variable {E : Type u₃} [Category.{v₃} E]

-- This is no longer viable as an instance in Lean 3.7,
-- #lint reports an instance loop
-- Will this be a problem?
/-- `G ∘ F` is a functorial if both `F` and `G` are.
-/
@[instance_reducible]
/--
Definition of `functorial_comp` / `functorial_comp` 的定义

English:
definition functorial_comp
  signature: (F : C -> D) [Functorial.{v₁, v₂} F] (G : D -> E) [Functorial.{v₂, v₃} G]
  body: { Functor.of F ⋙ Functor.of G with map := fun f => map G (map F f) }

中文:
定义 functorial_comp
  签名: (F : C -> D) [函子性.{v₁, v₂} F] (G : D -> E) [函子性.{v₂, v₃} G]
  定义体: { Functor.of F ⋙ Functor.of G with map := fun f => map G (map F f) }

Depends on / 依赖: Functor, Functor.of, HasStrongEpiImages, hasImageMapsOfHasStrongEpiImages
-/
def functorial_comp (F : C -> D) [Functorial.{v₁, v₂} F] (G : D -> E) [Functorial.{v₂, v₃} G] :
    Functorial.{v₁, v₃} (G ∘ F) :=
  { Functor.of F ⋙ Functor.of G with map := fun f => map G (map F f) }

end

end CategoryTheory
