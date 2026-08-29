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
/--
Definition of `adjoinOne` / `adjoinOne` 的定义

English:
definition adjoinOne
  signature: : Semigrp.{u} ⥤ MonCat.{u} where
  body: MonCat.of (WithOne S)
  map f := ofHom (WithOne.mapMulHom f.hom)
  map_id _ := MonCat.hom_ext WithOne.mapMulHom_id
  map_comp _ _ := MonCat.hom_ext (WithOne.mapMulHom_comp _ _)

@[to_additive]

中文:
定义 adjoinOne
  签名: : 半群.{u} ⥤ 幺半群范畴.{u} where
  定义体: MonCat.of (WithOne S)
  map f := ofHom (WithOne.mapMulHom f.hom)
  map_id _ := MonCat.hom_ext WithOne.mapMulHom_id
  map_comp _ _ := MonCat.hom_ext (WithOne.mapMulHom_comp _ _)

@[to_additive]

Depends on / 依赖: MonCat, MonCat.of, WithOne
-/
def adjoinOne : Semigrp.{u} ⥤ MonCat.{u} where
  obj S := MonCat.of (WithOne S)
  map f := ofHom (WithOne.mapMulHom f.hom)
  map_id _ := MonCat.hom_ext WithOne.mapMulHom_id
  map_comp _ _ := MonCat.hom_ext (WithOne.mapMulHom_comp _ _)

@[to_additive]
/--
Instance `hasForgetToSemigroup` / 实例 `hasForgetToSemigroup`

English:
instance hasForgetToSemigroup
  signature: : HasForget₂ MonCat Semigrp where
  body: { obj := fun M => Semigrp.of M
      map f := Semigrp.ofHom f.hom.toMulHom }

中文:
实例 hasForgetToSemigroup
  签名: : 有Forget₂ 幺半群范畴 半群 where
  定义体: { obj := fun M => Semigrp.of M
      map f := Semigrp.ofHom f.hom.toMulHom }

Depends on / 依赖: Semigrp, Semigrp.of, Semigrp.ofHom, f.hom.toMulHom, toMulHom
-/
instance hasForgetToSemigroup : HasForget₂ MonCat Semigrp where
  forget₂ :=
    { obj := fun M => Semigrp.of M
      map f := Semigrp.ofHom f.hom.toMulHom }

/-- The `adjoinOne`-forgetful adjunction from `Semigrp` to `MonCat`. -/
@[to_additive /-- The `adjoinZero`-forgetful adjunction from `AddSemigrp` to `AddMonCat` -/]
/--
Definition of `adjoinOneAdj` / `adjoinOneAdj` 的定义

English:
definition adjoinOneAdj
  signature: : adjoinOne ⊣ forget₂ MonCat.{u} Semigrp.{u}
  body: Adjunction.mkOfHomEquiv
    { homEquiv X Y :=
        ConcreteCategory.homEquiv.trans (WithOne.lift.symm.trans
          (ConcreteCategory.homEquiv (X := X) (Y := (forget₂ _ _).obj Y)).symm)
      homEquiv_naturality_left_symm := by
        intros
        ext ⟨_ | _⟩ <;> simp <;> rfl }

中文:
定义 adjoinOneAdj
  签名: : adjoinOne ⊣ forget₂ 幺半群范畴.{u} 半群.{u}
  定义体: Adjunction.mkOfHomEquiv
    { homEquiv X Y :=
        ConcreteCategory.homEquiv.trans (WithOne.lift.symm.trans
          (ConcreteCategory.homEquiv (X := X) (Y := (forget₂ _ _).obj Y)).symm)
      homEquiv_naturality_left_symm := by
        intros
        ext ⟨_ | _⟩ <;> simp <;> rfl }

Depends on / 依赖: Adjunction, Adjunction.mkOfHomEquiv, ConcreteCategory, ConcreteCategory.homEquiv, ConcreteCategory.homEquiv.trans, WithOne, WithOne.lift.symm.trans, homEquiv, homEquiv_naturality_left_symm, intros, mkOfHomEquiv
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
/--
Definition of `free` / `free` 的定义

English:
definition free
  signature: : Type u ⥤ MonCat.{u} where
  body: MonCat.of (FreeMonoid α)
  map f := ofHom (FreeMonoid.map f)
  map_id _ := MonCat.hom_ext (FreeMonoid.hom_eq fun _ => rfl)
  map_comp _ _ := MonCat.hom_ext (FreeMonoid.hom_eq fun _ => rfl)

中文:
定义 free
  签名: : 类型u ⥤ 幺半群范畴.{u} where
  定义体: MonCat.of (FreeMonoid α)
  map f := ofHom (FreeMonoid.map f)
  map_id _ := MonCat.hom_ext (FreeMonoid.hom_eq fun _ => rfl)
  map_comp _ _ := MonCat.hom_ext (FreeMonoid.hom_eq fun _ => rfl)

Depends on / 依赖: FreeMonoid, MonCat, MonCat.of
-/
def free : Type u ⥤ MonCat.{u} where
  obj α := MonCat.of (FreeMonoid α)
  map f := ofHom (FreeMonoid.map f)
  map_id _ := MonCat.hom_ext (FreeMonoid.hom_eq fun _ => rfl)
  map_comp _ _ := MonCat.hom_ext (FreeMonoid.hom_eq fun _ => rfl)

/-- The free-forgetful adjunction for monoids. -/
@[to_additive /-- The free-forgetful adjunction for additive monoids. -/]
/--
Definition of `adj` / `adj` 的定义

English:
definition adj
  signature: : free ⊣ forget MonCat.{u}
  body: Adjunction.mkOfHomEquiv
    -- The hint `(C := MonCat)` below speeds up the declaration by 10 times.
    { homEquiv X Y := (ConcreteCategory.homEquiv (C := MonCat)).trans (FreeMonoid.lift.symm.trans
        TypeCat.homEquiv.symm)
      homEquiv_naturality_left_symm _ _ := ConcreteCategory.ext (FreeM

中文:
定义 adj
  签名: : free ⊣ forget 幺半群范畴.{u}
  定义体: Adjunction.mkOfHomEquiv
    -- The hint `(C := MonCat)` below speeds up the declaration by 10 times.
    { homEquiv X Y := (ConcreteCategory.homEquiv (C := MonCat)).trans (FreeMonoid.lift.symm.trans
        TypeCat.homEquiv.symm)
      homEquiv_naturality_left_symm _ _ := ConcreteCategory.ext (FreeM

Depends on / 依赖: Adjunction, Adjunction.mkOfHomEquiv, mkOfHomEquiv
-/
def adj : free ⊣ forget MonCat.{u} :=
  Adjunction.mkOfHomEquiv
    -- The hint `(C := MonCat)` below speeds up the declaration by 10 times.
    { homEquiv X Y := (ConcreteCategory.homEquiv (C := MonCat)).trans (FreeMonoid.lift.symm.trans
        TypeCat.homEquiv.symm)
      homEquiv_naturality_left_symm _ _ := ConcreteCategory.ext (FreeMonoid.hom_eq fun _ => by rfl) }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget MonCat.{u}).IsRightAdjoint
  body: ⟨_, ⟨adj⟩⟩

中文:
实例 :
  签名: (forget 幺半群范畴.{u}).是右伴随
  定义体: ⟨_, ⟨adj⟩⟩
-/
instance : (forget MonCat.{u}).IsRightAdjoint :=
  ⟨_, ⟨adj⟩⟩

end MonCat

namespace AddCommMonCat

/-- The free functor `Type u ⥤ AddCommMonCat`
sending a type `X` to the free commutative monoid on `X`. -/
@[simps]
noncomputable
/--
Definition of `free` / `free` 的定义

English:
definition free
  signature: : Type u ⥤ AddCommMonCat.{u} where
  body: .of (α ->₀ Nat)
  map f := ofHom (Finsupp.mapDomain.addMonoidHom f)

中文:
定义 free
  签名: : 类型u ⥤ 加法交换幺半群范畴.{u} where
  定义体: .of (α ->₀ Nat)
  map f := ofHom (Finsupp.mapDomain.addMonoidHom f)
-/
def free : Type u ⥤ AddCommMonCat.{u} where
  obj α := .of (α ->₀ Nat)
  map f := ofHom (Finsupp.mapDomain.addMonoidHom f)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The free-forgetful adjunction for commutative monoids. -/
noncomputable
/--
Definition of `adj` / `adj` 的定义

English:
definition adj
  signature: : free ⊣ forget AddCommMonCat.{u} where
  body: { app X := ↾fun i => Finsupp.single i 1 }
  counit :=
  { app M := ofHom (Finsupp.liftAddHom (multiplesHom M))
    naturality {M N} f := by ext1; apply Finsupp.liftAddHom.symm.injective; cat_disch }

中文:
定义 adj
  签名: : free ⊣ forget 加法交换幺半群范畴.{u} where
  定义体: { app X := ↾fun i => Finsupp.single i 1 }
  counit :=
  { app M := ofHom (Finsupp.liftAddHom (multiplesHom M))
    naturality {M N} f := by ext1; apply Finsupp.liftAddHom.symm.injective; cat_disch }

Depends on / 依赖: Finsupp, Finsupp.single, single
-/
def adj : free ⊣ forget AddCommMonCat.{u} where
  unit := { app X := ↾fun i => Finsupp.single i 1 }
  counit :=
  { app M := ofHom (Finsupp.liftAddHom (multiplesHom M))
    naturality {M N} f := by ext1; apply Finsupp.liftAddHom.symm.injective; cat_disch }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: free.IsLeftAdjoint
  body: ⟨_, ⟨adj⟩⟩

中文:
实例 :
  签名: free.是左伴随
  定义体: ⟨_, ⟨adj⟩⟩
-/
instance : free.IsLeftAdjoint := ⟨_, ⟨adj⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget AddCommMonCat.{u}).IsRightAdjoint
  body: ⟨_, ⟨adj⟩⟩

中文:
实例 :
  签名: (forget 加法交换幺半群范畴.{u}).是右伴随
  定义体: ⟨_, ⟨adj⟩⟩
-/
instance : (forget AddCommMonCat.{u}).IsRightAdjoint := ⟨_, ⟨adj⟩⟩

end AddCommMonCat

namespace CommMonCat

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget CommMonCat.{u}).IsRightAdjoint
  body: ⟨_, ⟨AddCommMonCat.adj.comp AddCommMonCat.equivalence.toAdjunction⟩⟩

中文:
实例 :
  签名: (forget 交换幺半群范畴.{u}).是右伴随
  定义体: ⟨_, ⟨AddCommMonCat.adj.comp AddCommMonCat.equivalence.toAdjunction⟩⟩

Depends on / 依赖: AddCommMonCat, AddCommMonCat.adj.comp, AddCommMonCat.equivalence.toAdjunction, equivalence, toAdjunction
-/
instance : (forget CommMonCat.{u}).IsRightAdjoint :=
  ⟨_, ⟨AddCommMonCat.adj.comp AddCommMonCat.equivalence.toAdjunction⟩⟩

end CommMonCat
