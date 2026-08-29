/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Condensed.Light.Basic
public import Mathlib.Condensed.Light.Instances
/-!

# Light condensed `R`-modules

This file defines light condensed modules over a ring `R`.

## Main results

* Light condensed `R`-modules form an abelian category.

* The forgetful functor from light condensed `R`-modules to light condensed sets has a left
  adjoint, sending a light condensed set to the corresponding *free* light condensed `R`-module.
-/

@[expose] public section


universe u

open CategoryTheory

variable (R : Type u) [Ring R]

/--
Definition of `LightCondMod` / `LightCondMod` 的定义

English:
abbreviation LightCondMod
  body: LightCondensed.{u} (ModuleCat.{u} R)

中文:
缩写 LightCondMod
  定义体: LightCondensed.{u} (ModuleCat.{u} R)

Depends on / 依赖: LightCondensed, ModuleCat
-/
abbrev LightCondMod := LightCondensed.{u} (ModuleCat.{u} R)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Abelian (LightCondMod.{u} R)
  body: sheafIsAbelian

中文:
实例 :
  签名: 交换 (LightCondMod.{u} R)
  定义体: sheafIsAbelian

Depends on / 依赖: sheafIsAbelian
-/
noncomputable instance : Abelian (LightCondMod.{u} R) := sheafIsAbelian

/--
Definition of `LightCondensed.forget` / `LightCondensed.forget` 的定义

English:
definition LightCondensed.forget
  signature: : LightCondMod R ⥤ LightCondSet
  body: sheafCompose _ (CategoryTheory.forget _)

@[simp]

中文:
定义 LightCondensed.forget
  签名: : LightCondMod R ⥤ LightCondSet
  定义体: sheafCompose _ (CategoryTheory.forget _)

@[simp]

Depends on / 依赖: CategoryTheory, CategoryTheory.forget, forget, sheafCompose
-/
def LightCondensed.forget : LightCondMod R ⥤ LightCondSet :=
  sheafCompose _ (CategoryTheory.forget _)

@[simp]
/--
lemma `LightCondensed.forget_obj_obj_map_hom_apply` / 引理 `LightCondensed.forget_obj_obj_map_hom_apply`

English:
lemma LightCondensed.forget_obj_obj_map_hom_apply
  statement: (X : LightCondMod R)
  proof: rfl

@[simp]

中文:
引理 LightCondensed.forget_obj_obj_map_hom_apply
  结论: (X : LightCondMod R)
  证明: rfl

@[simp]
-/
lemma LightCondensed.forget_obj_obj_map_hom_apply (X : LightCondMod R)
    {S T : LightProfiniteᵒᵖ} (f : S ⟶ T) (a : ((sheafToPresheaf _ _).obj X).obj S) :
    ((forget R).obj X).obj.map f a = X.obj.map f a :=
  rfl

@[simp]
/--
lemma `LightCondensed.forget_map_hom_app_hom_apply` / 引理 `LightCondensed.forget_map_hom_app_hom_apply`

English:
lemma LightCondensed.forget_map_hom_app_hom_apply
  proof: rfl

中文:
引理 LightCondensed.forget_map_hom_app_hom_apply
  证明: rfl
-/
lemma LightCondensed.forget_map_hom_app_hom_apply
    {X Y : LightCondMod R} (f : X ⟶ Y) (S : LightProfiniteᵒᵖ)
    (a : ((sheafToPresheaf _ _).obj X).obj S) :
    ((forget R).map f).hom.app S a = f.hom.app S a :=
  rfl

/--
The left adjoint to the forgetful functor. The *free light condensed `R`-module* on a light
condensed set.
-/
noncomputable
/--
Definition of `LightCondensed.free` / `LightCondensed.free` 的定义

English:
definition LightCondensed.free
  signature: : LightCondSet ⥤ LightCondMod R
  body: Sheaf.composeAndSheafify _ (ModuleCat.free R)

中文:
定义 LightCondensed.free
  签名: : LightCondSet ⥤ LightCondMod R
  定义体: Sheaf.composeAndSheafify _ (ModuleCat.free R)

Depends on / 依赖: ModuleCat, ModuleCat.free, Sheaf.composeAndSheafify, composeAndSheafify
-/
def LightCondensed.free : LightCondSet ⥤ LightCondMod R :=
  Sheaf.composeAndSheafify _ (ModuleCat.free R)

/-- The condensed version of the free-forgetful adjunction. -/
noncomputable
/--
Definition of `LightCondensed.freeForgetAdjunction` / `LightCondensed.freeForgetAdjunction` 的定义

English:
definition LightCondensed.freeForgetAdjunction
  signature: : free R ⊣ forget R
  body: Sheaf.adjunction _ (ModuleCat.adj R)

中文:
定义 LightCondensed.freeForgetAdjunction
  签名: : free R ⊣ forget R
  定义体: Sheaf.adjunction _ (ModuleCat.adj R)

Depends on / 依赖: ModuleCat, ModuleCat.adj, Sheaf.adjunction, adjunction
-/
def LightCondensed.freeForgetAdjunction : free R ⊣ forget R := Sheaf.adjunction _ (ModuleCat.adj R)

open LightCondensed

.isLeftAdjoint instance : (LightCondensed.free R).IsLeftAdjoint := freeForgetAdjunction R

.isRightAdjoint instance : (LightCondensed.forget R).IsRightAdjoint := freeForgetAdjunction R

/--
Definition of `LightCondAb` / `LightCondAb` 的定义

English:
abbreviation LightCondAb
  body: LightCondMod Int

noncomputable example : Abelian LightCondAb := inferInstance

中文:
缩写 LightCondAb
  定义体: LightCondMod Int

noncomputable example : Abelian LightCondAb := inferInstance

Depends on / 依赖: LightCondMod
-/
abbrev LightCondAb := LightCondMod Int

noncomputable example : Abelian LightCondAb := inferInstance

namespace LightCondMod

/--
lemma `hom_naturality_apply` / 引理 `hom_naturality_apply`

English:
lemma hom_naturality_apply
  statement: {X Y : LightCondMod.{u} R} (f : X ⟶ Y) {S T : LightProfiniteᵒᵖ}
  proof: NatTrans.naturality_apply f.hom g x

中文:
引理 hom_naturality_apply
  结论: {X Y : LightCondMod.{u} R} (f : X ⟶ Y) {S T : LightProfiniteᵒᵖ}
  证明: NatTrans.naturality_apply f.hom g x

Depends on / 依赖: NatTrans, NatTrans.naturality_apply, f.hom, naturality_apply
-/
lemma hom_naturality_apply {X Y : LightCondMod.{u} R} (f : X ⟶ Y) {S T : LightProfiniteᵒᵖ}
    (g : S ⟶ T) (x : X.obj.obj S) : f.hom.app T (X.obj.map g x) = Y.obj.map g (f.hom.app S x) :=
  NatTrans.naturality_apply f.hom g x

end LightCondMod
