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
The category of condensed `R`-modules, defined as sheaves of `R`-modules over
`CompHaus` with respect to the coherent Grothendieck topology.
-/
/-
**CondensedMod** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：CondensedMod
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of condensed `R`-modules, defined as sheaves of `R`-modules over
`CompHaus` with respect to the coherent Grothendieck topology.
-/
abbrev CondensedMod := Condensed.{u} (ModuleCat.{u + 1} R)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Abelian (CondensedMod.{u} R) := sheafIsAbelian

/-- The forgetful functor from condensed `R`-modules to condensed sets. -/
/-
**Condensed.forget** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Condensed.forget : CondensedMod R ⥤ CondensedSet
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from condensed `R`-modules to condensed sets.
-/
def Condensed.forget : CondensedMod R ⥤ CondensedSet := sheafCompose _ (CategoryTheory.forget _)

/--
The left adjoint to the forgetful functor. The *free condensed `R`-module* on a condensed set.
-/
noncomputable
/-
**Condensed.free** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Condensed.free : CondensedSet ⥤ CondensedMod R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Condensed.free : CondensedSet ⥤ CondensedMod R :=
  Sheaf.composeAndSheafify _ (ModuleCat.free R)

/-- The condensed version of the free-forgetful adjunction. -/
noncomputable
/-
**Condensed.freeForgetAdjunction** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Condensed.freeForgetAdjunction : free R ⊣ forget R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Condensed.freeForgetAdjunction : free R ⊣ forget R := Sheaf.adjunction _ (ModuleCat.adj R)

/--
The category of condensed abelian groups is defined as condensed `ℤ`-modules.
-/
/-
**CondensedAb** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：CondensedAb
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of condensed abelian groups is defined as condensed `ℤ`-modules.
-/
abbrev CondensedAb := CondensedMod.{u} (ULift ℤ)
/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable example : Abelian CondensedAb.{u} := inferInstance

/-- The forgetful functor from condensed abelian groups to condensed sets. -/
/-
**Condensed.abForget** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Condensed.abForget : CondensedAb ⥤ CondensedSet
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from condensed abelian groups to condensed sets.
-/
abbrev Condensed.abForget : CondensedAb ⥤ CondensedSet := forget _

/-- The free condensed abelian group on a condensed set. -/
/-
**Condensed.freeAb** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Condensed.freeAb : CondensedSet ⥤ CondensedAb
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The free condensed abelian group on a condensed set.
-/
noncomputable abbrev Condensed.freeAb : CondensedSet ⥤ CondensedAb := free _

/-- The free-forgetful adjunction for condensed abelian groups. -/
/-
**Condensed.setAbAdjunction** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Condensed.setAbAdjunction : freeAb ⊣ abForget
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The free-forgetful adjunction for condensed abelian groups.
-/
noncomputable abbrev Condensed.setAbAdjunction : freeAb ⊣ abForget := freeForgetAdjunction _

namespace CondensedMod

/-
**CondensedMod.hom_naturality_apply** 是 Mathlib 中的一个引理，位于命名空间 `CondensedMod`。
形式化陈述：hom_naturality_apply {X Y : CondensedMod.{u} R} (f : X ⟶ Y) {S T : CompHau
sᵒᵖ} (g : S ⟶ T) (x : X.obj.obj S) : f.hom.app T (X.obj.map g x) = Y.obj.map g (
f.hom.app S x)
参数：f : X ⟶ Y；g : S ⟶ T；x : X.obj.obj S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.naturality_apply`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {D : Type u_1} [inst_1 : CategoryTheory.Category.{v_1
, u_1} D]   {FD : outParam (D …
-/
lemma hom_naturality_apply {X Y : CondensedMod.{u} R} (f : X ⟶ Y) {S T : CompHausᵒᵖ} (g : S ⟶ T)
    (x : X.obj.obj S) : f.hom.app T (X.obj.map g x) = Y.obj.map g (f.hom.app S x) :=
  NatTrans.naturality_apply f.hom g x

end CondensedMod

