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
The category of light condensed `R`-modules, defined as sheaves of `R`-modules over
`LightProfinite.{u}` with respect to the coherent Grothendieck topology.
-/
/-
**LightCondMod** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：LightCondMod
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of light condensed `R`-modules, defined as sheaves of `R`-modules o
ver
`LightProfinite.{u}` with respect to the coherent Grothendieck topology.
-/
abbrev LightCondMod := LightCondensed.{u} (ModuleCat.{u} R)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Abelian (LightCondMod.{u} R) := sheafIsAbelian

/-- The forgetful functor from light condensed `R`-modules to light condensed sets. -/
/-
**LightCondensed.forget** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LightCondensed.forget : LightCondMod R ⥤ LightCondSet
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from light condensed `R`-modules to light condensed sets.
-/
def LightCondensed.forget : LightCondMod R ⥤ LightCondSet :=
  sheafCompose _ (CategoryTheory.forget _)

@[simp]
/-
**LightCondensed.forget_obj_obj_map_hom_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LightCondensed.forget_obj_obj_map_hom_apply (X : LightCondMod R) {S T : Li
ghtProfiniteᵒᵖ} (f : S ⟶ T) (a : ((sheafToPresheaf _ _).obj X).obj S) : ((forget
 R).obj X).obj.map f a = X.obj.map f a
参数：X : LightCondMod R；f : S ⟶ T；a : ((sheafToPresheaf _ _).obj X).obj S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma LightCondensed.forget_obj_obj_map_hom_apply (X : LightCondMod R)
    {S T : LightProfiniteᵒᵖ} (f : S ⟶ T) (a : ((sheafToPresheaf _ _).obj X).obj S) :
    ((forget R).obj X).obj.map f a = X.obj.map f a :=
  rfl

@[simp]
/-
**LightCondensed.forget_map_hom_app_hom_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LightCondensed.forget_map_hom_app_hom_apply {X Y : LightCondMod R} (f : X 
⟶ Y) (S : LightProfiniteᵒᵖ) (a : ((sheafToPresheaf _ _).obj X).obj S) : ((forget
 R).map f).hom.app S a = f.hom.app S a
参数：f : X ⟶ Y；S : LightProfiniteᵒᵖ；a : ((sheafToPresheaf _ _).obj X).obj S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**LightCondensed.free** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LightCondensed.free : LightCondSet ⥤ LightCondMod R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def LightCondensed.free : LightCondSet ⥤ LightCondMod R :=
  Sheaf.composeAndSheafify _ (ModuleCat.free R)

/-- The condensed version of the free-forgetful adjunction. -/
noncomputable
/-
**LightCondensed.freeForgetAdjunction** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LightCondensed.freeForgetAdjunction : free R ⊣ forget R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def LightCondensed.freeForgetAdjunction : free R ⊣ forget R := Sheaf.adjunction _ (ModuleCat.adj R)

open LightCondensed
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (LightCondensed.free R).IsLeftAdjoint := freeForgetAdjunction R |>.isLeftAdjoint
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (LightCondensed.forget R).IsRightAdjoint := freeForgetAdjunction R |>.isRightAdjoint

/--
The category of light condensed abelian groups, defined as sheaves of `ℤ`-modules over
`LightProfinite.{0}` with respect to the coherent Grothendieck topology.
-/
/-
**LightCondAb** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：LightCondAb
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of light condensed abelian groups, defined as sheaves of `ℤ`-module
s over
`LightProfinite.{0}` with respect to the coherent Grothendieck topology.
-/
abbrev LightCondAb := LightCondMod ℤ
/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable example : Abelian LightCondAb := inferInstance

namespace LightCondMod

/-
**LightCondMod.hom_naturality_apply** 是 Mathlib 中的一个引理，位于命名空间 `LightCondMod`。
形式化陈述：hom_naturality_apply {X Y : LightCondMod.{u} R} (f : X ⟶ Y) {S T : LightPr
ofiniteᵒᵖ} (g : S ⟶ T) (x : X.obj.obj S) : f.hom.app T (X.obj.map g x) = Y.obj.m
ap g (f.hom.app S x)
参数：f : X ⟶ Y；g : S ⟶ T；x : X.obj.obj S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.naturality_apply`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {D : Type u_1} [inst_1 : CategoryTheory.Category.{v_1
, u_1} D]   {FD : outParam (D …
-/
lemma hom_naturality_apply {X Y : LightCondMod.{u} R} (f : X ⟶ Y) {S T : LightProfiniteᵒᵖ}
    (g : S ⟶ T) (x : X.obj.obj S) : f.hom.app T (X.obj.map g x) = Y.obj.map g (f.hom.app S x) :=
  NatTrans.naturality_apply f.hom g x

end LightCondMod

