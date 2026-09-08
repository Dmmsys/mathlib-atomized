/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Nailin Guan, Yuyang Zhao
-/
module

public import Mathlib.Data.Finite.Defs
public import Mathlib.Algebra.Category.Grp.Basic

/-!

## Main definitions and results

* `FiniteGrp` is the category of finite groups.

-/

@[expose] public section

universe u v

open CategoryTheory

/-- The category of finite groups. -/
@[pp_with_univ]
/-
**FiniteGrp** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type (u + 1)
参数：u + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of finite groups.
-/
structure FiniteGrp where
  /-- A group that is finite -/
  toGrp : GrpCat.{u}
  [isFinite : Finite toGrp]

/-- The category of finite additive groups. -/
@[pp_with_univ]
/-
**FiniteAddGrp** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type (u + 1)
参数：u + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of finite additive groups.
-/
structure FiniteAddGrp where
  /-- An additive group that is finite -/
  toAddGrp : AddGrpCat.{u}
  [isFinite : Finite toAddGrp]

attribute [to_additive] FiniteGrp

namespace FiniteGrp

@[to_additive]
/-
**FiniteGrp.** 是 Mathlib 中的一个实例，位于命名空间 `FiniteGrp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort FiniteGrp.{u} (Type u) where
  coe G := G.toGrp

@[to_additive]
/-
**FiniteGrp.** 是 Mathlib 中的一个实例，位于命名空间 `FiniteGrp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category FiniteGrp :=
  inferInstanceAs <| Category (InducedCategory _ FiniteGrp.toGrp)

@[to_additive]
/-
**FiniteGrp.** 是 Mathlib 中的一个实例，位于命名空间 `FiniteGrp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ConcreteCategory FiniteGrp (· →* ·) :=
  inferInstanceAs <| ConcreteCategory (InducedCategory _ toGrp) _

@[to_additive]
/-
**FiniteGrp.** 是 Mathlib 中的一个实例，位于命名空间 `FiniteGrp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (G : FiniteGrp) : Group G := inferInstanceAs <| Group G.toGrp

@[to_additive]
/-
**FiniteGrp.** 是 Mathlib 中的一个实例，位于命名空间 `FiniteGrp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (G : FiniteGrp) : Finite G := G.isFinite

/-- Construct a term of `FiniteGrp` from a type endowed with the structure of a finite group. -/
@[to_additive /-- Construct a term of `FiniteAddGrp` from a type endowed with the structure of a
finite additive group. -/]
/-
**FiniteGrp.of** 是 Mathlib 中的一个定义，位于命名空间 `FiniteGrp`。
形式化陈述：of (G : Type u) [Group G] [Finite G] : FiniteGrp where toGrp
参数：G : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def of (G : Type u) [Group G] [Finite G] : FiniteGrp where
  toGrp := GrpCat.of G
  isFinite := ‹_›

/-- The morphism in `FiniteGrp`, induced from a morphism of the category `GrpCat`. -/
@[to_additive
/-- The morphism in `FiniteAddGrp`, induced from a morphism of the category `AddGrpCat` -/]
/-
**FiniteGrp.ofHom** 是 Mathlib 中的一个定义，位于命名空间 `FiniteGrp`。
形式化陈述：ofHom {X Y : Type u} [Group X] [Finite X] [Group Y] [Finite Y] (f : X ->* 
Y) : of X ⟶ of Y
参数：f : X ->* Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def ofHom {X Y : Type u} [Group X] [Finite X] [Group Y] [Finite Y] (f : X →* Y) : of X ⟶ of Y :=
  InducedCategory.homMk (GrpCat.ofHom f)

@[to_additive]
/-
**FiniteGrp.ofHom_apply** 是 Mathlib 中的一个引理，位于命名空间 `FiniteGrp`。
形式化陈述：ofHom_apply {X Y : Type u} [Group X] [Finite X] [Group Y] [Finite Y] (f : 
X ->* Y) (x : X) : ofHom f x = f x
参数：f : X ->* Y；x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofHom_apply {X Y : Type u} [Group X] [Finite X] [Group Y] [Finite Y] (f : X →* Y) (x : X) :
    ofHom f x = f x :=
  rfl

end FiniteGrp

