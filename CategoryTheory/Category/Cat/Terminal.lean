/-
Copyright (c) 2025 Emily Riehl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier, Emily Riehl
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Terminal categories

We prove that a category is terminal if its underlying type has a `Unique` structure and the
category has an `IsDiscrete` instance.

We then use this to provide various examples of terminal categories.

TODO: Show the converse: that terminal categories have a unique object and are discrete.

TODO: Provide an analogous characterization of terminal categories as codiscrete categories
with a unique object.

-/

@[expose] public section

universe v u v' u'

open CategoryTheory Limits Functor

namespace CategoryTheory.Cat

set_option backward.isDefEq.respectTransparency false in
/-- A discrete category with a unique object is terminal. -/
/-
**CategoryTheory.Cat.isTerminalOfUniqueOfIsDiscrete** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Cat`。
形式化陈述：isTerminalOfUniqueOfIsDiscrete {T : Type u} [Category.{v} T] [Unique T] [I
sDiscrete T] : IsTerminal (Cat.of T)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A discrete category with a unique object is terminal.
-/
def isTerminalOfUniqueOfIsDiscrete {T : Type u} [Category.{v} T] [Unique T] [IsDiscrete T] :
    IsTerminal (Cat.of T) :=
  IsTerminal.ofUniqueHom (fun X ↦ ((const X).obj (default : T)).toCatHom)
    (fun _ _ ↦ Cat.Hom.ext <| Functor.ext (by simp [eq_iff_true_of_subsingleton]))
/-
**CategoryTheory.Cat.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Cat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasTerminal Cat.{v, u} := by
  have : IsDiscrete (ShrinkHoms.{u} PUnit.{u + 1}) := {
    subsingleton _ _ := { allEq _ _ := eq_of_comp_right_eq (congrFun rfl) }
    eq_of_hom _ := rfl
  }
  exact IsTerminal.hasTerminal (X := Cat.of (ShrinkHoms PUnit)) isTerminalOfUniqueOfIsDiscrete

/-- Any `T : Cat.{u, u}` with a unique object and discrete homs is isomorphic to `⊤_ Cat.{u, u}.` -/
/-
**CategoryTheory.Cat.terminalIsoOfUniqueOfIsDiscrete** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Cat`。
形式化陈述：terminalIsoOfUniqueOfIsDiscrete {T : Type u} [Category.{v} T] [Unique T] [
IsDiscrete T] : ⊤_ Cat.{v, u} ≅ Cat.of T
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Cat.instHasTerminal`：CategoryTheory.Limits.HasTerminal Ca
tegoryTheory.Cat

--- 原说明 ---
Any `T : Cat.{u, u}` with a unique object and discrete homs is isomorphic to `⊤_
 Cat.{u, u}.`
-/
noncomputable def terminalIsoOfUniqueOfIsDiscrete
    {T : Type u} [Category.{v} T] [Unique T] [IsDiscrete T] : ⊤_ Cat.{v, u} ≅ Cat.of T :=
  terminalIsoIsTerminal isTerminalOfUniqueOfIsDiscrete

/-- The discrete category on `PUnit` is terminal. -/
/-
**CategoryTheory.Cat.isTerminalDiscretePUnit** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Cat`。
形式化陈述：isTerminalDiscretePUnit : IsTerminal (Cat.of (Discrete PUnit))
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Discrete.isDiscrete`：∀ (C : Type u_1), CategoryTheory.IsD
iscrete (CategoryTheory.Discrete C)

--- 原说明 ---
The discrete category on `PUnit` is terminal.
-/
def isTerminalDiscretePUnit : IsTerminal (Cat.of (Discrete PUnit)) :=
  isTerminalOfUniqueOfIsDiscrete

/-- Any terminal object `T : Cat.{u, u}` is isomorphic to `Cat.of (Discrete PUnit)`. -/
/-
**CategoryTheory.Cat.isoDiscretePUnitOfIsTerminal** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Cat`。
形式化陈述：isoDiscretePUnitOfIsTerminal {T : Type u} [Category.{u} T] (hT : IsTermina
l (Cat.of T)) : Cat.of T ≅ Cat.of (Discrete PUnit)
参数：hT : IsTerminal (Cat.of T)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any terminal object `T : Cat.{u, u}` is isomorphic to `Cat.of (Discrete PUnit)`.
-/
def isoDiscretePUnitOfIsTerminal {T : Type u} [Category.{u} T] (hT : IsTerminal (Cat.of T)) :
    Cat.of T ≅ Cat.of (Discrete PUnit) :=
  IsTerminal.uniqueUpToIso hT isTerminalDiscretePUnit

end CategoryTheory.Cat

