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
* `fst`       : the strict pseudofunctor `⟨X, Y⟩ ↦ X`
* `snd`       : the strict pseudofunctor `⟨X, Y⟩ ↦ Y`
* `swap`      : the strict pseudofunctor `B × C ⥤ C × B` given by `⟨X, Y⟩ ↦ ⟨Y, X⟩`

-/

@[expose] public section

namespace CategoryTheory.Bicategory

open CategoryTheory.Prod

universe w₁ w₂ v₁ v₂ u₁ u₂

variable (B : Type u₁) [Bicategory.{w₁, v₁} B] (C : Type u₂) [Bicategory.{w₂, v₂} C]

/-- The cartesian product of two bicategories. -/
@[simps! (notRecursive := [])] -- notRecursive to generate simp lemmas like _fst and _snd
/-
**CategoryTheory.Bicategory.prod** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Bicat
egory`。
形式化陈述：prod : Bicategory (B × C) where homCategory X Y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cartesian product of two bicategories.
-/
instance prod : Bicategory (B × C) where
  homCategory X Y := CategoryTheory.prod' (X.1 ⟶ Y.1) (X.2 ⟶ Y.2)
  whiskerLeft f g h θ := f.1 ◁ θ.1 ×ₘ f.2 ◁ θ.2
  whiskerRight θ g := θ.1 ▷ g.1 ×ₘ θ.2 ▷ g.2
  associator f g h := Iso.prod (α_ f.1 g.1 h.1) (α_ f.2 g.2 h.2)
  leftUnitor f := Iso.prod (λ_ f.1) (λ_ f.2)
  rightUnitor f := Iso.prod (ρ_ f.1) (ρ_ f.2)
  whisker_exchange η θ := Prod.ext (whisker_exchange η.1 θ.1) (whisker_exchange η.2 θ.2)

open Strict in
attribute [local simp] leftUnitor_eqToIso rightUnitor_eqToIso associator_eqToIso in
/-- The cartesian product of two strict bicategories is strict. -/
/-
**CategoryTheory.Bicategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Bicategor
y`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cartesian product of two strict bicategories is strict.
-/
instance [Strict B] [Strict C] : Strict (B × C) where

namespace Prod

/-- `sectL B c` is the strictly unitary pseudofunctor `B ⥤ B × C` given by `X ↦ (X, c)`. -/
@[simps!]
/-
**CategoryTheory.Bicategory.Prod.sectL** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Bicategory.Prod`。
形式化陈述：sectL (B : Type u₁) [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂,
 v₂} C] (c : C) : StrictlyUnitaryPseudofunctor B (B × C)
参数：B : Type u₁；c : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`sectL B c` is the strictly unitary pseudofunctor `B ⥤ B × C` given by `X ↦ (X, 
c)`.
-/
def sectL (B : Type u₁) [Bicategory.{w₁, v₁} B] {C : Type u₂} [Bicategory.{w₂, v₂} C] (c : C) :
    StrictlyUnitaryPseudofunctor B (B × C) := .mk'
  { obj X := (X, c)
    map f := f ×ₘ 𝟙 c
    map₂ η := η ×ₘ 𝟙 _
    mapComp f g := Iso.prod (Iso.refl _) (λ_ (g, 𝟙 c).2).symm }

/-- `sectR b C` is the strictly unitary pseudofunctor `C ⥤ B × C` given by `Y ↦ (b, Y)`. -/
@[simps!]
/-
**CategoryTheory.Bicategory.Prod.sectR** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Bicategory.Prod`。
形式化陈述：sectR {B : Type u₁} [Bicategory.{w₁, v₁} B] (b : B) (C : Type u₂) [Bicateg
ory.{w₂, v₂} C] : StrictlyUnitaryPseudofunctor C (B × C)
参数：b : B；C : Type u₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`sectR b C` is the strictly unitary pseudofunctor `C ⥤ B × C` given by `Y ↦ (b, 
Y)`.
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
/-
**CategoryTheory.Bicategory.Prod.fst** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.B
icategory.Prod`。
形式化陈述：fst : StrictPseudofunctor (B × C) B
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`fst` is the strict pseudofunctor given by projection to the first factor.
-/
def fst : StrictPseudofunctor (B × C) B := .mk'
  { obj X := X.1
    map f := f.1
    map₂ η := η.1 }

/-- `snd` is the strict pseudofunctor given by projection to the second factor. -/
@[simps!]
/-
**CategoryTheory.Bicategory.Prod.snd** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.B
icategory.Prod`。
形式化陈述：snd : StrictPseudofunctor (B × C) C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`snd` is the strict pseudofunctor given by projection to the second factor.
-/
def snd : StrictPseudofunctor (B × C) C := .mk'
  { obj X := X.2
    map f := f.2
    map₂ η := η.2 }

/-- The pseudofunctor swapping the factors of a cartesian product of bicategories,
`B × C ⥤ C × B`. -/
@[simps!]
/-
**CategoryTheory.Bicategory.Prod.swap** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Bicategory.Prod`。
形式化陈述：swap : StrictPseudofunctor (B × C) (C × B)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pseudofunctor swapping the factors of a cartesian product of bicategories,
`B × C ⥤ C × B`.
-/
def swap : StrictPseudofunctor (B × C) (C × B) := .mk'
  { obj X := (X.2, X.1)
    map f := f.2 ×ₘ f.1
    map₂ η := η.2 ×ₘ η.1 }

end Prod

section

variable (B : Type u₁) [Bicategory.{w₁, v₁} B] (C : Type u₁) [Bicategory.{w₁, v₁} C]

/-- `Bicategory.uniformProd B C` is an additional instance specialised so both factors have the same
universe levels. This helps typeclass resolution.
-/
/-
**CategoryTheory.Bicategory.uniformProd** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.Bicategory`。
形式化陈述：uniformProd : Bicategory (B × C)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Bicategory.uniformProd B C` is an additional instance specialised so both facto
rs have the same
universe levels. This helps typeclass resolution.
-/
instance uniformProd : Bicategory (B × C) :=
  Bicategory.prod B C

end

end CategoryTheory.Bicategory

