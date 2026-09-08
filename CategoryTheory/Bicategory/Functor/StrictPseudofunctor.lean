/-
Copyright (c) 2025 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/
module

public import Mathlib.CategoryTheory.Bicategory.Functor.StrictlyUnitary

/-!
# Strict pseudofunctors

In this file we introduce the notion of strict pseudofunctors, which are pseudofunctors such
that `mapId` and `mapComp` are given by `eqToIso _`.

To a strict pseudofunctor between strict bicategories we can associate a functor between the
underlying categories, see `StrictPseudofunctor.toFunctor`.

## TODO

Once the deprecated `Mathlib/CategoryTheory/Bicategory/Functor/Strict.lean` is removed we should
rename this file to `Mathlib/CategoryTheory/Bicategory/Functor/Strict.lean`.

-/

@[expose] public section

namespace CategoryTheory

open Bicategory

universe w₁ w₂ w₃ w₄ v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {B : Type u₁} [Bicategory.{w₁, v₁} B]
  {C : Type u₂} [Bicategory.{w₂, v₂} C]
  {D : Type u₃} [Bicategory.{w₃, v₃} D]

variable (B C)

/-- A strict pseudofunctor `F` between bicategories `B` and `C` is a
pseudofunctor `F` from `B` to `C` such that `mapId` and `mapComp` are given by `eqToIso _`. -/
@[kerodon 008H]
/-
**CategoryTheory.StrictPseudofunctor** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory`。
形式化陈述：StrictPseudofunctor extends StrictlyUnitaryPseudofunctor B C where map_com
p : forall {a b c : B} (f : a ⟶ b) (g : b ⟶ c), map (f ≫ g) = map f ≫ map g
继承自：StrictlyUnitaryPseudofunctor B C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A strict pseudofunctor `F` between bicategories `B` and `C` is a
pseudofunctor `F` from `B` to `C` such that `mapId` and `mapComp` are given by `
eqToIso _`.
-/
structure StrictPseudofunctor extends StrictlyUnitaryPseudofunctor B C where
  map_comp : ∀ {a b c : B} (f : a ⟶ b) (g : b ⟶ c), map (f ≫ g) = map f ≫ map g := by
    rfl_cat
  mapComp_eq_eqToIso : ∀ {a b c : B} (f : a ⟶ b) (g : b ⟶ c),
    mapComp f g = eqToIso (map_comp f g) := by cat_disch

/-- A helper structure that bundles the necessary data to
construct a `StrictPseudofunctor`.

`StrictPseudofunctorPreCore` does not construct a Pseudofunctor in general,
since it does not include the compatibility conditions on the associator
and unitors. However, when the underlying bicategories are strict, a
`StrictPseudofunctorPreCore` does induce a `StrictPseudofunctor`. -/
/-
**CategoryTheory.StrictPseudofunctorPreCore** 是 Mathlib 中的一个结构，位于命名空间 `CategoryT
heory`。
形式化陈述：StrictPseudofunctorPreCore extends PrelaxFunctor B C where map_id (X : B) 
: map (𝟙 X) = 𝟙 (obj X)
参数：X : B。
继承自：PrelaxFunctor B C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A helper structure that bundles the necessary data to
construct a `StrictPseudofunctor`.

`StrictPseudofunctorPreCore` does not construct a Pseudofunctor in general,
since it does not include the compatibility conditions on the associator
and unitors. However, when the underlying bicategories are strict, a
`StrictPseudofunctorPreCore` does induce a `StrictPseudofunctor`.
-/
structure StrictPseudofunctorPreCore extends PrelaxFunctor B C where
  map_id (X : B) : map (𝟙 X) = 𝟙 (obj X) := by rfl_cat
  map_comp : ∀ {a b c : B} (f : a ⟶ b) (g : b ⟶ c), map (f ≫ g) = map f ≫ map g := by
    rfl_cat
  map₂_whisker_left :
    ∀ {a b c : B} (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g'),
      map₂ (f ◁ η) = eqToHom (map_comp f g) ≫
        map f ◁ map₂ η ≫ eqToHom (map_comp f g').symm := by cat_disch
  map₂_whisker_right :
      ∀ {a b c : B} {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c),
        map₂ (η ▷ g) = eqToHom (map_comp f g) ≫
          map₂ η ▷ map g ≫ eqToHom (map_comp f' g).symm := by cat_disch

/-- A helper structure that bundles the necessary data to
construct a `StrictPseudofunctor` without specifying the redundant
fields `mapId` and `mapComp`. -/
/-
**CategoryTheory.StrictPseudofunctorCore** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheo
ry`。
形式化陈述：StrictPseudofunctorCore extends StrictPseudofunctorPreCore B C where map₂_
left_unitor : forall {a b : B} (f : a ⟶ b), map₂ (fun_ f).hom = eqToHom (by rw [
map_comp (𝟙 a) f, map_id a]) ≫ (fun_ (map f)).hom
继承自：StrictPseudofunctorPreCore B C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A helper structure that bundles the necessary data to
construct a `StrictPseudofunctor` without specifying the redundant
fields `mapId` and `mapComp`.
-/
structure StrictPseudofunctorCore extends StrictPseudofunctorPreCore B C where
  map₂_left_unitor :
      ∀ {a b : B} (f : a ⟶ b),
        map₂ (λ_ f).hom =
        eqToHom (by rw [map_comp (𝟙 a) f, map_id a]) ≫
          (λ_ (map f)).hom := by
    cat_disch
  map₂_right_unitor :
      ∀ {a b : B} (f : a ⟶ b),
        map₂ (ρ_ f).hom =
         eqToHom (by rw [map_comp f (𝟙 b), map_id b]) ≫
          (ρ_ (map f)).hom := by
    cat_disch
  map₂_associator :
      ∀ {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d),
        map₂ (α_ f g h).hom = eqToHom (by simp only [map_comp]) ≫
          (α_ (map f) (map g) (map h)).hom ≫ eqToHom (by simp only [map_comp]) := by
    cat_disch

namespace StrictPseudofunctor

variable {B C}

/-- An alternate constructor for strict pseudofunctors that does not
require the `mapId` or `mapComp` fields, and that adapts the compatibility conditions
to the fact that the pseudofunctor is strict -/
@[simps]
/-
**CategoryTheory.StrictPseudofunctor.mk'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.StrictPseudofunctor`。
形式化陈述：mk' (S : StrictPseudofunctorCore B C) : StrictPseudofunctor B C where obj
参数：S : StrictPseudofunctorCore B C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An alternate constructor for strict pseudofunctors that does not
require the `mapId` or `mapComp` fields, and that adapts the compatibility condi
tions
to the fact that the pseudofunctor is strict
-/
def mk' (S : StrictPseudofunctorCore B C) : StrictPseudofunctor B C where
  obj := S.obj
  map := S.map
  map_id := S.map_id
  mapId x := eqToIso (S.map_id x)
  mapId_eq_eqToIso x := rfl
  map₂ := S.map₂
  map₂_id := S.map₂_id
  map₂_comp := S.map₂_comp
  map_comp := S.map_comp
  mapComp f g := eqToIso <| S.map_comp f g
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

section

variable (F : StrictPseudofunctor B C)

variable (B) in
/-- The identity `StrictPseudofunctor`. -/
@[simps!]
/-
**CategoryTheory.StrictPseudofunctor.id** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.StrictPseudofunctor`。
形式化陈述：id : StrictPseudofunctor B B where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity `StrictPseudofunctor`.
-/
def id : StrictPseudofunctor B B where
  __ := StrictlyUnitaryPseudofunctor.id B

set_option backward.isDefEq.respectTransparency false in
/-- Composition of `StrictPseudofunctor`. -/
@[simps!]
/-
**CategoryTheory.StrictPseudofunctor.comp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.StrictPseudofunctor`。
形式化陈述：comp (F : StrictPseudofunctor B C) (G : StrictPseudofunctor C D) : StrictP
seudofunctor B D where __
参数：F : StrictPseudofunctor B C；G : StrictPseudofunctor C D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of `StrictPseudofunctor`.
-/
def comp (F : StrictPseudofunctor B C)
    (G : StrictPseudofunctor C D) :
    StrictPseudofunctor B D where
  __ := StrictlyUnitaryPseudofunctor.comp
    F.toStrictlyUnitaryPseudofunctor G.toStrictlyUnitaryPseudofunctor
  map_comp _ := by simp [StrictPseudofunctor.map_comp]
  mapComp_eq_eqToIso _ _ := by
    ext
    simp [StrictPseudofunctor.mapComp_eq_eqToIso,
      PrelaxFunctor.map₂_eqToHom]

end

section

variable [Strict B] [Strict C]

attribute [local simp] Strict.leftUnitor_eqToIso Strict.rightUnitor_eqToIso
  Strict.associator_eqToIso PrelaxFunctor.map₂_eqToHom in
/-- An alternate constructor for strict pseudofunctors between strict bicategories, that
only requires the data bundled in `StrictPseudofunctorPreCore`. -/
@[simps]
/-
**CategoryTheory.StrictPseudofunctor.mk''** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.StrictPseudofunctor`。
形式化陈述：mk'' (S : StrictPseudofunctorPreCore B C) : StrictPseudofunctor B C where 
obj
参数：S : StrictPseudofunctorPreCore B C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.StrictPseudofunctorPreCore.map_id`：∀ {B : Type u₁} [inst 
: CategoryTheory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicategory
 C]   (self : CategoryTheory.StrictPse…
· 使用定理 `CategoryTheory.StrictPseudofunctorPreCore.map_comp`：∀ {B : Type u₁} [ins
t : CategoryTheory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicatego
ry C]   (self : CategoryTheory.StrictPse…

--- 原说明 ---
An alternate constructor for strict pseudofunctors between strict bicategories, 
that
only requires the data bundled in `StrictPseudofunctorPreCore`.
-/
def mk'' (S : StrictPseudofunctorPreCore B C) : StrictPseudofunctor B C where
  obj := S.obj
  map := S.map
  map_id := S.map_id
  mapId x := eqToIso (S.map_id x)
  mapId_eq_eqToIso x := rfl
  map₂ := S.map₂
  map₂_id := S.map₂_id
  map₂_comp := S.map₂_comp
  map_comp := S.map_comp
  mapComp f g := eqToIso <| S.map_comp f g
  map₂_whisker_left f _ _ η := by
    simpa using S.map₂_whisker_left f η
  map₂_whisker_right η f := by
    simpa using S.map₂_whisker_right η f

/-- A strict pseudofunctor between strict bicategories induces a functor on the underlying
categories. -/
@[simps]
/-
**CategoryTheory.StrictPseudofunctor.toFunctor** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.StrictPseudofunctor`。
形式化陈述：toFunctor (F : StrictPseudofunctor B C) : Functor B C where obj
参数：F : StrictPseudofunctor B C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.StrictPseudofunctor.map_comp`：∀ {B : Type u₁} [inst : Cat
egoryTheory.Bicategory B] {C : Type u₂} [inst_1 : CategoryTheory.Bicategory C]  
 (self : CategoryTheory.StrictPse…

--- 原说明 ---
A strict pseudofunctor between strict bicategories induces a functor on the unde
rlying
categories.
-/
def toFunctor (F : StrictPseudofunctor B C) : Functor B C where
  obj := F.obj
  map := F.map
  map_id := F.map_id
  map_comp := F.map_comp

end

end StrictPseudofunctor

end CategoryTheory

