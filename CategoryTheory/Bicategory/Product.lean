/-
Copyright (c) 2025 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/
module

public import Mathlib.CategoryTheory.Bicategory.Functor.StrictPseudofunctor

/-!
# Cartesian products of bicategories

We define the bicategory instance on `B × C` when `B` and `C` are bicategories.

We define:
* `sectL B c` : the strictly unitary pseudofunctor `B ⥤ B × C` given by `X ↦ ⟨X, c⟩`
* `sectR b C` : the strictly unitary pseudofunctor `C ⥤ B × C` given by `Y ↦ ⟨b, Y⟩`
* `fst` : the strict pseudofunctor `⟨X, Y⟩ ↦ X`
* `snd` : the strict pseudofunctor `⟨X, Y⟩ ↦ Y`
* `swap` : the strict pseudofunctor `B × C ⥤ C × B` given by `⟨X, Y⟩ ↦ ⟨Y, X⟩`

-/

@[expose] public section

namespace CategoryTheory.Bicategory

open CategoryTheory.Prod

universe w₁ w₂ v₁ v₂ u₁ u₂

variable (B : Type u₁) [Bicategory.{w₁, v₁} B] (C : Type u₂) [Bicategory.{w₂, v₂} C]

/-- The cartesian product of two bicategories. -/
@[simps! (notRecursive := [])] -- notRecursive to generate simp lemmas like _fst and _snd
/--
Instance `prod` / 实例 `prod`

English:
instance prod
  signature: : Bicategory (B × C) where
  body: CategoryTheory.prod' (X.1 ⟶ Y.1) (X.2 ⟶ Y.2)
  whiskerLeft f g h θ := f.1 ◁ θ.1 ×ₘ f.2 ◁ θ.2
  whiskerRight θ g := θ.1 ▷ g.1 ×ₘ θ.2 ▷ g.2
  associator f g h := Iso.prod (α_ f.1 g.1 h.1) (α_ f.2 g.2 h.2)
  leftUnitor f := Iso.prod (fun_ f.1) (fun_ f.2)
  rightUnitor f := Iso.prod (ρ_ f.1) (ρ_ f.2)
  

中文:
实例 prod
  签名: : Bicategory (B × C) where
  定义体: CategoryTheory.prod' (X.1 ⟶ Y.1) (X.2 ⟶ Y.2)
  whiskerLeft f g h θ := f.1 ◁ θ.1 ×ₘ f.2 ◁ θ.2
  whiskerRight θ g := θ.1 ▷ g.1 ×ₘ θ.2 ▷ g.2
  associator f g h := Iso.prod (α_ f.1 g.1 h.1) (α_ f.2 g.2 h.2)
  leftUnitor f := Iso.prod (fun_ f.1) (fun_ f.2)
  rightUnitor f := Iso.prod (ρ_ f.1) (ρ_ f.2)
  

Depends on / 依赖: CategoryTheory, CategoryTheory.prod
-/
instance prod : Bicategory (B × C) where
  homCategory X Y := CategoryTheory.prod' (X.1 ⟶ Y.1) (X.2 ⟶ Y.2)
  whiskerLeft f g h θ := f.1 ◁ θ.1 ×ₘ f.2 ◁ θ.2
  whiskerRight θ g := θ.1 ▷ g.1 ×ₘ θ.2 ▷ g.2
  associator f g h := Iso.prod (α_ f.1 g.1 h.1) (α_ f.2 g.2 h.2)
  leftUnitor f := Iso.prod (fun_ f.1) (fun_ f.2)
  rightUnitor f := Iso.prod (ρ_ f.1) (ρ_ f.2)
  whisker_exchange η θ := Prod.ext (whisker_exchange η.1 θ.1) (whisker_exchange η.2 θ.2)

open Strict in
attribute [local simp] leftUnitor_eqToIso rightUnitor_eqToIso associator_eqToIso in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Strict
  signature: B] [Strict C] : Strict (B × C) where

中文:
实例 [Strict
  签名: B] [Strict C] : Strict (B × C) where
-/
instance [Strict B] [Strict C] : Strict (B × C) where

namespace Prod

/-- `sectL B c` is the strictly unitary pseudofunctor `B ⥤ B × C` given by `X ↦ (X, c)`. -/
@[simps!]
/--
Definition of `sectL` / `sectL` 的定义

English:
definition sectL
  signature: (B : Type u₁) [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C] (c : C)
  body: .mk'
  { obj X := (X, c)
    map f := f ×ₘ 𝟙 c
    map₂ η := η ×ₘ 𝟙 _
    mapComp f g := Iso.prod (Iso.refl _) (fun_ (g, 𝟙 c).2).symm }

中文:
定义 sectL
  签名: (B : 类型u₁) [Bicategory.{w₁, v₁} B] {C : 类型u₂} [Bicategory.{w₂, v₂} C] (c : C)
  定义体: .mk'
  { obj X := (X, c)
    map f := f ×ₘ 𝟙 c
    map₂ η := η ×ₘ 𝟙 _
    mapComp f g := Iso.prod (Iso.refl _) (fun_ (g, 𝟙 c).2).symm }
-/
def sectL (B : Type u₁) [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C] (c : C) :
    StrictlyUnitaryPseudofunctor B (B × C) := .mk'
  { obj X := (X, c)
    map f := f ×ₘ 𝟙 c
    map₂ η := η ×ₘ 𝟙 _
    mapComp f g := Iso.prod (Iso.refl _) (fun_ (g, 𝟙 c).2).symm }

/-- `sectR b C` is the strictly unitary pseudofunctor `C ⥤ B × C` given by `Y ↦ (b, Y)`. -/
@[simps!]
/--
Definition of `sectR` / `sectR` 的定义

English:
definition sectR
  signature: {B : Type u₁} [Bicategory.{w₁, v₁} B] (b : B) (C : Type u₂) [Bicategory.{w₂, v₂} C]
  body: .mk'
  { obj Y := (b, Y)
    map f := 𝟙 b ×ₘ f
    map₂ η := 𝟙 _ ×ₘ η
    mapComp f g := Iso.prod (ρ_ (𝟙 b)).symm (Iso.refl _) }

中文:
定义 sectR
  签名: {B : 类型u₁} [Bicategory.{w₁, v₁} B] (b : B) (C : 类型u₂) [Bicategory.{w₂, v₂} C]
  定义体: .mk'
  { obj Y := (b, Y)
    map f := 𝟙 b ×ₘ f
    map₂ η := 𝟙 _ ×ₘ η
    mapComp f g := Iso.prod (ρ_ (𝟙 b)).symm (Iso.refl _) }
-/
def sectR {B : Type u₁} [Bicategory.{w₁, v₁} B] (b : B) (C : Type u₂) [Bicategory.{w₂, v₂} C] :
    StrictlyUnitaryPseudofunctor C (B × C) := .mk'
  { obj Y := (b, Y)
    map f := 𝟙 b ×ₘ f
    map₂ η := 𝟙 _ ×ₘ η
    mapComp f g := Iso.prod (ρ_ (𝟙 b)).symm (Iso.refl _) }

variable (B : Type u₁) [Bicategory.{w₁, v₁} B] (C : Type u₂) [Bicategory.{w₂, v₂} C]

/-- `fst` is the strict pseudofunctor given by projection to the first factor. -/
@[simps!]
/--
Definition of `fst` / `fst` 的定义

English:
definition fst
  signature: : StrictPseudofunctor (B × C) B
  body: .mk'
  { obj X := X.1
    map f := f.1
    map₂ η := η.1 }

中文:
定义 fst
  签名: : StrictPseudofunctor (B × C) B
  定义体: .mk'
  { obj X := X.1
    map f := f.1
    map₂ η := η.1 }

Depends on / 依赖: FintypeCat, FintypeCat.inclusionCreatesFiniteColimits, inclusionCreatesFiniteColimits
-/
def fst : StrictPseudofunctor (B × C) B := .mk'
  { obj X := X.1
    map f := f.1
    map₂ η := η.1 }

/-- `snd` is the strict pseudofunctor given by projection to the second factor. -/
@[simps!]
/--
Definition of `snd` / `snd` 的定义

English:
definition snd
  signature: : StrictPseudofunctor (B × C) C
  body: .mk'
  { obj X := X.2
    map f := f.2
    map₂ η := η.2 }

中文:
定义 snd
  签名: : StrictPseudofunctor (B × C) C
  定义体: .mk'
  { obj X := X.2
    map f := f.2
    map₂ η := η.2 }

Depends on / 依赖: FintypeCat, FintypeCat.incl, hasColimit_of_created
-/
def snd : StrictPseudofunctor (B × C) C := .mk'
  { obj X := X.2
    map f := f.2
    map₂ η := η.2 }

/-- The pseudofunctor swapping the factors of a cartesian product of bicategories,
`B × C ⥤ C × B`. -/
@[simps!]
/--
Definition of `swap` / `swap` 的定义

English:
definition swap
  signature: : StrictPseudofunctor (B × C) (C × B)
  body: .mk'
  { obj X := (X.2, X.1)
    map f := f.2 ×ₘ f.1
    map₂ η := η.2 ×ₘ η.1 }

中文:
定义 swap
  签名: : StrictPseudofunctor (B × C) (C × B)
  定义体: .mk'
  { obj X := (X.2, X.1)
    map f := f.2 ×ₘ f.1
    map₂ η := η.2 ×ₘ η.1 }
-/
def swap : StrictPseudofunctor (B × C) (C × B) := .mk'
  { obj X := (X.2, X.1)
    map f := f.2 ×ₘ f.1
    map₂ η := η.2 ×ₘ η.1 }

end Prod

section

variable (B : Type u₁) [Bicategory.{w₁, v₁} B] (C : Type u₁) [Bicategory.{w₁, v₁} C]

/--
Instance `uniformProd` / 实例 `uniformProd`

English:
instance uniformProd
  signature: : Bicategory (B × C)
  body: Bicategory.prod B C

中文:
实例 uniformProd
  签名: : Bicategory (B × C)
  定义体: Bicategory.prod B C

Depends on / 依赖: Bicategory, Bicategory.prod
-/
instance uniformProd : Bicategory (B × C) :=
  Bicategory.prod B C

end

end CategoryTheory.Bicategory
