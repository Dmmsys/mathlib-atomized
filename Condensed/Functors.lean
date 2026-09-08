/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Sites.PreservesLimits
public import Mathlib.Condensed.Explicit

/-!
# Functors from categories of topological spaces to condensed sets

This file defines the embedding of the test objects (compact Hausdorff spaces) into condensed
sets.

## Main definitions

* `compHausToCondensed : CompHaus.{u} ⥤ CondensedSet.{u}` is essentially the yoneda presheaf
  functor. We also define `profiniteToCondensed` and `stoneanToCondensed`.

-/

@[expose] public section

universe u v

open CategoryTheory Limits

section Universes

/-- Increase the size of the target category of condensed sets. -/
/-
**Condensed.ulift** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Condensed.ulift : Condensed.{u} (Type u) ⥤ CondensedSet.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Increase the size of the target category of condensed sets.
-/
def Condensed.ulift : Condensed.{u} (Type u) ⥤ CondensedSet.{u} :=
  sheafCompose (coherentTopology CompHaus) uliftFunctor.{u + 1, u}
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Condensed.ulift.Full := show (sheafCompose _ _).Full from inferInstance
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Condensed.ulift.Faithful := show (sheafCompose _ _).Faithful from inferInstance

end Universes

section Topology

/-- The functor from `CompHaus` to `Condensed.{u} (Type u)` given by the Yoneda sheaf. -/
/-
**compHausToCondensed'** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：compHausToCondensed' : CompHaus.{u} ⥤ Condensed.{u} (Type u)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor from `CompHaus` to `Condensed.{u} (Type u)` given by the Yoneda shea
f.
-/
def compHausToCondensed' : CompHaus.{u} ⥤ Condensed.{u} (Type u) :=
  (coherentTopology CompHaus).yoneda

/-- The yoneda presheaf as an actual condensed set. -/
/-
**compHausToCondensed** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：compHausToCondensed : CompHaus.{u} ⥤ CondensedSet.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The yoneda presheaf as an actual condensed set.
-/
def compHausToCondensed : CompHaus.{u} ⥤ CondensedSet.{u} :=
  compHausToCondensed' ⋙ Condensed.ulift

/-- Dot notation for the value of `compHausToCondensed`. -/
/-
**CompHaus.toCondensed** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：CompHaus.toCondensed (S : CompHaus.{u}) : CondensedSet.{u}
参数：S : CompHaus.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Dot notation for the value of `compHausToCondensed`.
-/
abbrev CompHaus.toCondensed (S : CompHaus.{u}) : CondensedSet.{u} := compHausToCondensed.obj S

/-- The yoneda presheaf as a condensed set, restricted to profinite spaces. -/
/-
**profiniteToCondensed** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：profiniteToCondensed : Profinite.{u} ⥤ CondensedSet.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The yoneda presheaf as a condensed set, restricted to profinite spaces.
-/
def profiniteToCondensed : Profinite.{u} ⥤ CondensedSet.{u} :=
  profiniteToCompHaus ⋙ compHausToCondensed

/-- Dot notation for the value of `profiniteToCondensed`. -/
/-
**Profinite.toCondensed** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Profinite.toCondensed (S : Profinite.{u}) : CondensedSet.{u}
参数：S : Profinite.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Dot notation for the value of `profiniteToCondensed`.
-/
abbrev Profinite.toCondensed (S : Profinite.{u}) : CondensedSet.{u} := profiniteToCondensed.obj S

/-- The yoneda presheaf as a condensed set, restricted to Stonean spaces. -/
/-
**stoneanToCondensed** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：stoneanToCondensed : Stonean.{u} ⥤ CondensedSet.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The yoneda presheaf as a condensed set, restricted to Stonean spaces.
-/
def stoneanToCondensed : Stonean.{u} ⥤ CondensedSet.{u} :=
  Stonean.toCompHaus ⋙ compHausToCondensed

/-- Dot notation for the value of `stoneanToCondensed`. -/
/-
**Stonean.toCondensed** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Stonean.toCondensed (S : Stonean.{u}) : CondensedSet.{u}
参数：S : Stonean.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Dot notation for the value of `stoneanToCondensed`.
-/
abbrev Stonean.toCondensed (S : Stonean.{u}) : CondensedSet.{u} := stoneanToCondensed.obj S
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : compHausToCondensed'.Full :=
  inferInstanceAs ((coherentTopology CompHaus).yoneda).Full
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : compHausToCondensed'.Faithful :=
  inferInstanceAs ((coherentTopology CompHaus).yoneda).Faithful
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : compHausToCondensed.Full := inferInstanceAs (_ ⋙ _).Full
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : compHausToCondensed.Faithful := inferInstanceAs (_ ⋙ _).Faithful
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PreservesFiniteCoproducts compHausToCondensed.{u} :=
  inferInstanceAs <| PreservesFiniteCoproducts (coherentTopology _).uliftYoneda

end Topology

