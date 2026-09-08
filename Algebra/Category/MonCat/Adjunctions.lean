/-
Copyright (c) 2021 Julian Kuelshammer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Kuelshammer
-/
module

public import Mathlib.Algebra.Category.MonCat.Basic
public import Mathlib.Algebra.Category.Semigrp.Basic
public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Algebra.Group.WithOne.Basic
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finsupp.SMulWithZero
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Adjunctions regarding the category of monoids

This file proves the adjunction between adjoining a unit to a semigroup and the forgetful functor
from monoids to semigroups.

## TODO

* free-forgetful adjunction for monoids
* adjunctions related to commutative monoids
-/

@[expose] public section


universe u

open CategoryTheory

namespace MonCat

/-- The functor of adjoining a neutral element `one` to a semigroup. -/
@[to_additive (attr := simps)
/-- The functor of adjoining a neutral element `zero` to a semigroup -/]
/-
**MonCat.adjoinOne** 是 Mathlib 中的一个定义，位于命名空间 `MonCat`。
形式化陈述：adjoinOne : Semigrp.{u} ⥤ MonCat.{u} where obj S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def adjoinOne : Semigrp.{u} ⥤ MonCat.{u} where
  obj S := MonCat.of (WithOne S)
  map f := ofHom (WithOne.mapMulHom f.hom)
  map_id _ := MonCat.hom_ext WithOne.mapMulHom_id
  map_comp _ _ := MonCat.hom_ext (WithOne.mapMulHom_comp _ _)

@[to_additive]
/-
**MonCat.hasForgetToSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `MonCat`。
形式化陈述：hasForgetToSemigroup : HasForget₂ MonCat Semigrp where forget₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasForgetToSemigroup : HasForget₂ MonCat Semigrp where
  forget₂ :=
    { obj := fun M => Semigrp.of M
      map f := Semigrp.ofHom f.hom.toMulHom }

/-- The `adjoinOne`-forgetful adjunction from `Semigrp` to `MonCat`. -/
@[to_additive /-- The `adjoinZero`-forgetful adjunction from `AddSemigrp` to `AddMonCat` -/]
/-
**MonCat.adjoinOneAdj** 是 Mathlib 中的一个定义，位于命名空间 `MonCat`。
形式化陈述：adjoinOneAdj : adjoinOne ⊣ forget₂ MonCat.{u} Semigrp.{u}
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The `adjoinOne`-forgetful adjunction from `Semigrp` to `MonCat`.
-/
def adjoinOneAdj : adjoinOne ⊣ forget₂ MonCat.{u} Semigrp.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv X Y :=
        ConcreteCategory.homEquiv.trans (WithOne.lift.symm.trans
          (ConcreteCategory.homEquiv (X := X) (Y := (forget₂ _ _).obj Y)).symm)
      homEquiv_naturality_left_symm := by
        intros
        ext ⟨_ | _⟩ <;> simp <;> rfl }

/-- The free functor `Type u ⥤ MonCat` sending a type `X` to the free monoid on `X`. -/
@[to_additive
/-- The free functor `Type u ⥤ AddMonCat` sending a type `X` to the free additive monoid on `X`. -/]
/-
**MonCat.free** 是 Mathlib 中的一个定义，位于命名空间 `MonCat`。
形式化陈述：free : Type u ⥤ MonCat.{u} where obj α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def free : Type u ⥤ MonCat.{u} where
  obj α := MonCat.of (FreeMonoid α)
  map f := ofHom (FreeMonoid.map f)
  map_id _ := MonCat.hom_ext (FreeMonoid.hom_eq fun _ => rfl)
  map_comp _ _ := MonCat.hom_ext (FreeMonoid.hom_eq fun _ => rfl)

/-- The free-forgetful adjunction for monoids. -/
@[to_additive /-- The free-forgetful adjunction for additive monoids. -/]
/-
**MonCat.adj** 是 Mathlib 中的一个定义，位于命名空间 `MonCat`。
形式化陈述：adj : free ⊣ forget MonCat.{u}
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The free-forgetful adjunction for monoids.
-/
def adj : free ⊣ forget MonCat.{u} :=
  Adjunction.mkOfHomEquiv
    -- The hint `(C := MonCat)` below speeds up the declaration by 10 times.
    { homEquiv X Y := (ConcreteCategory.homEquiv (C := MonCat)).trans (FreeMonoid.lift.symm.trans
        TypeCat.homEquiv.symm)
      homEquiv_naturality_left_symm _ _ := ConcreteCategory.ext (FreeMonoid.hom_eq fun _ ↦ by rfl) }
/-
**MonCat.** 是 Mathlib 中的一个实例，位于命名空间 `MonCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (forget MonCat.{u}).IsRightAdjoint :=
  ⟨_, ⟨adj⟩⟩

end MonCat

namespace AddCommMonCat

/-- The free functor `Type u ⥤ AddCommMonCat`
sending a type `X` to the free commutative monoid on `X`. -/
@[simps]
noncomputable
/-
**AddCommMonCat.free** 是 Mathlib 中的一个定义，位于命名空间 `AddCommMonCat`。
形式化陈述：free : Type u ⥤ AddCommMonCat.{u} where obj α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def free : Type u ⥤ AddCommMonCat.{u} where
  obj α := .of (α →₀ ℕ)
  map f := ofHom (Finsupp.mapDomain.addMonoidHom f)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The free-forgetful adjunction for commutative monoids. -/
noncomputable
/-
**AddCommMonCat.adj** 是 Mathlib 中的一个定义，位于命名空间 `AddCommMonCat`。
形式化陈述：adj : free ⊣ forget AddCommMonCat.{u} where unit
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def adj : free ⊣ forget AddCommMonCat.{u} where
  unit := { app X := ↾fun i ↦ Finsupp.single i 1 }
  counit :=
  { app M := ofHom (Finsupp.liftAddHom (multiplesHom M))
    naturality {M N} f := by ext1; apply Finsupp.liftAddHom.symm.injective; cat_disch }
/-
**AddCommMonCat.** 是 Mathlib 中的一个实例，位于命名空间 `AddCommMonCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : free.IsLeftAdjoint := ⟨_, ⟨adj⟩⟩
/-
**AddCommMonCat.** 是 Mathlib 中的一个实例，位于命名空间 `AddCommMonCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (forget AddCommMonCat.{u}).IsRightAdjoint := ⟨_, ⟨adj⟩⟩

end AddCommMonCat

namespace CommMonCat

/-
**CommMonCat.** 是 Mathlib 中的一个实例，位于命名空间 `CommMonCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (forget CommMonCat.{u}).IsRightAdjoint :=
  ⟨_, ⟨AddCommMonCat.adj.comp AddCommMonCat.equivalence.toAdjunction⟩⟩

end CommMonCat

