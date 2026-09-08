/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Condensed.Basic
public import Mathlib.Condensed.Light.Basic
public import Mathlib.Condensed.Light.Instances
/-!

# Discrete-underlying adjunction

Given a category `C` with sheafification with respect to the coherent topology on compact Hausdorff
spaces, we define a functor `C ⥤ Condensed C` which associates to an object of `C` the
corresponding "discrete" condensed object (see `Condensed.discrete`).

In `Condensed.discreteUnderlyingAdj` we prove that this functor is left adjoint to the forgetful
functor from `Condensed C` to `C`.

We also give the variant `LightCondensed.discreteUnderlyingAdj` for light condensed objects.

The file `Mathlib/Condensed/Discrete/Characterization.lean` defines a predicate `IsDiscrete` on
condensed and light condensed objects, and provides several conditions on a (light) condensed
set or module that characterize it as discrete.
-/

@[expose] public section

universe u v w

open CategoryTheory Limits Opposite GrothendieckTopology

namespace Condensed

variable (C : Type w) [Category.{u + 1} C] [HasWeakSheafify (coherentTopology CompHaus.{u}) C]

/--
The discrete condensed object associated to an object of `C` is the constant sheaf at that object.
-/
@[simps!]
/-
**Condensed.discrete** 是 Mathlib 中的一个定义，位于命名空间 `Condensed`。
形式化陈述：discrete : C ⥤ Condensed.{u} C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The discrete condensed object associated to an object of `C` is the constant she
af at that object.
-/
noncomputable def discrete : C ⥤ Condensed.{u} C := constantSheaf _ C

/--
The underlying object of a condensed object in `C` is the condensed object evaluated at a point.
This can be viewed as a sort of forgetful functor from `Condensed C` to `C`
-/
@[simps!]
/-
**Condensed.underlying** 是 Mathlib 中的一个定义，位于命名空间 `Condensed`。
形式化陈述：underlying : Condensed.{u} C ⥤ C
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instCompactSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Indiscrete
Topology X], CompactSpace X
· 使用定理 `instIndiscreteTopologyPUnit`：IndiscreteTopology PUnit.{u_1 + 1}

--- 原说明 ---
The underlying object of a condensed object in `C` is the condensed object evalu
ated at a point.
This can be viewed as a sort of forgetful functor from `Condensed C` to `C`
-/
noncomputable def underlying : Condensed.{u} C ⥤ C :=
  (sheafSections _ _).obj ⟨CompHaus.of PUnit.{u + 1}⟩

/--
Discreteness is left adjoint to the forgetful functor. When `C` is `Type*`, this is analogous to
`TopCat.adj₁ : TopCat.discrete ⊣ forget TopCat`.
-/
/-
**Condensed.discreteUnderlyingAdj** 是 Mathlib 中的一个定义，位于命名空间 `Condensed`。
形式化陈述：discreteUnderlyingAdj : discrete C ⊣ underlying C
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instCompactSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Indiscrete
Topology X], CompactSpace X
· 使用定理 `instIndiscreteTopologyPUnit`：IndiscreteTopology PUnit.{u_1 + 1}

--- 原说明 ---
Discreteness is left adjoint to the forgetful functor. When `C` is `Type*`, this
 is analogous to
`TopCat.adj₁ : TopCat.discrete ⊣ forget TopCat`.
-/
noncomputable def discreteUnderlyingAdj : discrete C ⊣ underlying C :=
  constantSheafAdj _ _ CompHaus.isTerminalPUnit

end Condensed

namespace LightCondensed

variable (C : Type w) [Category.{u} C] [HasSheafify (coherentTopology LightProfinite.{u}) C]

/--
The discrete light condensed object associated to an object of `C` is the constant sheaf at that
object.
-/
@[simps!]
/-
**LightCondensed.discrete** 是 Mathlib 中的一个定义，位于命名空间 `LightCondensed`。
形式化陈述：discrete : C ⥤ LightCondensed.{u} C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The discrete light condensed object associated to an object of `C` is the consta
nt sheaf at that
object.
-/
noncomputable def discrete : C ⥤ LightCondensed.{u} C := constantSheaf _ C

/--
The underlying object of a condensed object in `C` is the light condensed object evaluated at a
point. This can be viewed as a sort of forgetful functor from `LightCondensed C` to `C`
-/
@[simps!]
/-
**LightCondensed.underlying** 是 Mathlib 中的一个定义，位于命名空间 `LightCondensed`。
形式化陈述：underlying : LightCondensed.{u} C ⥤ C
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instCompactSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Indiscrete
Topology X], CompactSpace X
· 使用定理 `instIndiscreteTopologyPUnit`：IndiscreteTopology PUnit.{u_1 + 1}

--- 原说明 ---
The underlying object of a condensed object in `C` is the light condensed object
 evaluated at a
point. This can be viewed as a sort of forgetful functor from `LightCondensed C`
 to `C`
-/
noncomputable def underlying : LightCondensed.{u} C ⥤ C :=
  (sheafSections _ _).obj (op (LightProfinite.of PUnit))

/--
Discreteness is left adjoint to the forgetful functor. When `C` is `Type*`, this is analogous to
`TopCat.adj₁ : TopCat.discrete ⊣ forget TopCat`.
-/
/-
**LightCondensed.discreteUnderlyingAdj** 是 Mathlib 中的一个定义，位于命名空间 `LightCondensed
`。
形式化陈述：discreteUnderlyingAdj : discrete C ⊣ underlying C
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instCompactSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Indiscrete
Topology X], CompactSpace X
· 使用定理 `instIndiscreteTopologyPUnit`：IndiscreteTopology PUnit.{u_1 + 1}
· 使用定理 `LightProfinite.instHasPropAndTotallyDisconnectedSpaceCarrierSecondCounta
bleTopology`：∀ (X : Type u_1) [inst : TopologicalSpace X] [TotallyDisconnectedSp
ace X] [SecondCountableTopology X],   CompHausLike.HasProp (fun Y => Tota…

--- 原说明 ---
Discreteness is left adjoint to the forgetful functor. When `C` is `Type*`, this
 is analogous to
`TopCat.adj₁ : TopCat.discrete ⊣ forget TopCat`.
-/
noncomputable def discreteUnderlyingAdj : discrete C ⊣ underlying C :=
  constantSheafAdj _ _ CompHausLike.isTerminalPUnit

end LightCondensed

/-- A version of `LightCondensed.discrete` in the `LightCondSet` namespace -/
/-
**LightCondSet.discrete** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：LightCondSet.discrete
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `LightCondensed.discrete` in the `LightCondSet` namespace
-/
noncomputable abbrev LightCondSet.discrete := LightCondensed.discrete <| Type u

/-- A version of `LightCondensed.underlying` in the `LightCondSet` namespace -/
/-
**LightCondSet.underlying** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：LightCondSet.underlying
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `LightCondensed.underlying` in the `LightCondSet` namespace
-/
noncomputable abbrev LightCondSet.underlying := LightCondensed.underlying <| Type u

/-- A version of `LightCondensed.discrete_underlying_adj` in the `LightCondSet` namespace -/
/-
**LightCondSet.discreteUnderlyingAdj** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：LightCondSet.discreteUnderlyingAdj : discrete ⊣ underlying
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `LightCondensed.discrete_underlying_adj` in the `LightCondSet` name
space
-/
noncomputable abbrev LightCondSet.discreteUnderlyingAdj : discrete ⊣ underlying :=
  LightCondensed.discreteUnderlyingAdj _
