/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Condensed.Basic
/-!

# Condensed `R`-modules

This file defines condensed modules over a ring `R`.

## Main results

* Condensed `R`-modules form an abelian category.

* The forgetful functor from condensed `R`-modules to condensed sets has a left adjoint, sending a
  condensed set to the corresponding *free* condensed `R`-module.
-/

@[expose] public section

universe u

open CategoryTheory

variable (R : Type (u + 1)) [Ring R]

/--
Definition of `CondensedMod` / `CondensedMod` 的定义

English:
abbreviation CondensedMod
  body: Condensed.{u} (ModuleCat.{u + 1} R)

中文:
缩写 CondensedMod
  定义体: Condensed.{u} (ModuleCat.{u + 1} R)

Depends on / 依赖: Condensed, ModuleCat
-/
abbrev CondensedMod := Condensed.{u} (ModuleCat.{u + 1} R)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Abelian (CondensedMod.{u} R)
  body: sheafIsAbelian

中文:
实例 :
  签名: 交换 (CondensedMod.{u} R)
  定义体: sheafIsAbelian

Depends on / 依赖: sheafIsAbelian
-/
noncomputable instance : Abelian (CondensedMod.{u} R) := sheafIsAbelian

/--
Definition of `Condensed.forget` / `Condensed.forget` 的定义

English:
definition Condensed.forget
  signature: : CondensedMod R ⥤ CondensedSet
  body: sheafCompose _ (CategoryTheory.forget _)

中文:
定义 Condensed.forget
  签名: : CondensedMod R ⥤ CondensedSet
  定义体: sheafCompose _ (CategoryTheory.forget _)

Depends on / 依赖: CategoryTheory, CategoryTheory.forget, forget, sheafCompose
-/
def Condensed.forget : CondensedMod R ⥤ CondensedSet := sheafCompose _ (CategoryTheory.forget _)

/--
The left adjoint to the forgetful functor. The *free condensed `R`-module* on a condensed set.
-/
noncomputable
/--
Definition of `Condensed.free` / `Condensed.free` 的定义

English:
definition Condensed.free
  signature: : CondensedSet ⥤ CondensedMod R
  body: Sheaf.composeAndSheafify _ (ModuleCat.free R)

中文:
定义 Condensed.free
  签名: : CondensedSet ⥤ CondensedMod R
  定义体: Sheaf.composeAndSheafify _ (ModuleCat.free R)

Depends on / 依赖: ModuleCat, ModuleCat.free, Sheaf.composeAndSheafify, composeAndSheafify
-/
def Condensed.free : CondensedSet ⥤ CondensedMod R :=
  Sheaf.composeAndSheafify _ (ModuleCat.free R)

/-- The condensed version of the free-forgetful adjunction. -/
noncomputable
/--
Definition of `Condensed.freeForgetAdjunction` / `Condensed.freeForgetAdjunction` 的定义

English:
definition Condensed.freeForgetAdjunction
  signature: : free R ⊣ forget R
  body: Sheaf.adjunction _ (ModuleCat.adj R)

中文:
定义 Condensed.freeForgetAdjunction
  签名: : free R ⊣ forget R
  定义体: Sheaf.adjunction _ (ModuleCat.adj R)

Depends on / 依赖: ModuleCat, ModuleCat.adj, Sheaf.adjunction, adjunction
-/
def Condensed.freeForgetAdjunction : free R ⊣ forget R := Sheaf.adjunction _ (ModuleCat.adj R)

/--
Definition of `CondensedAb` / `CondensedAb` 的定义

English:
abbreviation CondensedAb
  body: CondensedMod.{u} (ULift Int)

noncomputable example : Abelian CondensedAb.{u} := inferInstance

中文:
缩写 CondensedAb
  定义体: CondensedMod.{u} (ULift Int)

noncomputable example : Abelian CondensedAb.{u} := inferInstance

Depends on / 依赖: CondensedMod
-/
abbrev CondensedAb := CondensedMod.{u} (ULift Int)

noncomputable example : Abelian CondensedAb.{u} := inferInstance

/--
Definition of `Condensed.abForget` / `Condensed.abForget` 的定义

English:
abbreviation Condensed.abForget
  signature: : CondensedAb ⥤ CondensedSet
  body: forget _

中文:
缩写 Condensed.abForget
  签名: : CondensedAb ⥤ CondensedSet
  定义体: forget _

Depends on / 依赖: forget
-/
abbrev Condensed.abForget : CondensedAb ⥤ CondensedSet := forget _

/--
Definition of `Condensed.freeAb` / `Condensed.freeAb` 的定义

English:
abbreviation Condensed.freeAb
  signature: : CondensedSet ⥤ CondensedAb
  body: free _

中文:
缩写 Condensed.freeAb
  签名: : CondensedSet ⥤ CondensedAb
  定义体: free _
-/
noncomputable abbrev Condensed.freeAb : CondensedSet ⥤ CondensedAb := free _

/--
Definition of `Condensed.setAbAdjunction` / `Condensed.setAbAdjunction` 的定义

English:
abbreviation Condensed.setAbAdjunction
  signature: : freeAb ⊣ abForget
  body: freeForgetAdjunction _

中文:
缩写 Condensed.setAbAdjunction
  签名: : freeAb ⊣ abForget
  定义体: freeForgetAdjunction _

Depends on / 依赖: freeForgetAdjunction
-/
noncomputable abbrev Condensed.setAbAdjunction : freeAb ⊣ abForget := freeForgetAdjunction _

namespace CondensedMod

/--
lemma `hom_naturality_apply` / 引理 `hom_naturality_apply`

English:
lemma hom_naturality_apply
  statement: {X Y : CondensedMod.{u} R} (f : X ⟶ Y) {S T : CompHausᵒᵖ} (g : S ⟶ T)
  proof: NatTrans.naturality_apply f.hom g x

中文:
引理 hom_naturality_apply
  结论: {X Y : CondensedMod.{u} R} (f : X ⟶ Y) {S T : CompHausᵒᵖ} (g : S ⟶ T)
  证明: NatTrans.naturality_apply f.hom g x

Depends on / 依赖: NatTrans, NatTrans.naturality_apply, f.hom, naturality_apply
-/
lemma hom_naturality_apply {X Y : CondensedMod.{u} R} (f : X ⟶ Y) {S T : CompHausᵒᵖ} (g : S ⟶ T)
    (x : X.obj.obj S) : f.hom.app T (X.obj.map g x) = Y.obj.map g (f.hom.app S x) :=
  NatTrans.naturality_apply f.hom g x

end CondensedMod
