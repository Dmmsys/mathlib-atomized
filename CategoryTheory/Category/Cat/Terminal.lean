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
/--
Definition of `isTerminalOfUniqueOfIsDiscrete` / `isTerminalOfUniqueOfIsDiscrete` 的定义

English:
definition isTerminalOfUniqueOfIsDiscrete
  signature: {T : Type u} [Category.{v} T] [Unique T] [IsDiscrete T]
  body: IsTerminal.ofUniqueHom (fun X => ((const X).obj (default : T)).toCatHom)
    (fun _ _ => Cat.Hom.ext <| Functor.ext (by simp [eq_iff_true_of_subsingleton]))

中文:
定义 isTerminalOfUniqueOfIsDiscrete
  签名: {T : 类型u} [范畴.{v} T] [唯一 T] [是离散 T]
  定义体: IsTerminal.ofUniqueHom (fun X => ((const X).obj (default : T)).toCatHom)
    (fun _ _ => Cat.Hom.ext <| Functor.ext (by simp [eq_iff_true_of_subsingleton]))

Depends on / 依赖: Cat.Hom.ext, Functor, Functor.ext, IsTerminal, IsTerminal.ofUniqueHom, eq_iff_true_of_subsingleton, ofUniqueHom, toCatHom
-/
def isTerminalOfUniqueOfIsDiscrete {T : Type u} [Category.{v} T] [Unique T] [IsDiscrete T] :
    IsTerminal (Cat.of T) :=
  IsTerminal.ofUniqueHom (fun X => ((const X).obj (default : T)).toCatHom)
    (fun _ _ => Cat.Hom.ext <| Functor.ext (by simp [eq_iff_true_of_subsingleton]))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasTerminal Cat.{v, u}
  body: by
  have : IsDiscrete (ShrinkHoms.{u} PUnit.{u + 1}) := {
    subsingleton _ _ := { allEq _ _ := eq_of_comp_right_eq (congrFun rfl) }
    eq_of_hom _ := rfl
  }
  exact IsTerminal.hasTerminal (X := Cat.of (ShrinkHoms PUnit)) isTerminalOfUniqueOfIsDiscrete

中文:
实例 :
  签名: 有终止 Cat.{v, u}
  定义体: by
  have : IsDiscrete (ShrinkHoms.{u} PUnit.{u + 1}) := {
    subsingleton _ _ := { allEq _ _ := eq_of_comp_right_eq (congrFun rfl) }
    eq_of_hom _ := rfl
  }
  exact IsTerminal.hasTerminal (X := Cat.of (ShrinkHoms PUnit)) isTerminalOfUniqueOfIsDiscrete

Depends on / 依赖: Cat.of, IsDiscrete, IsTerminal, IsTerminal.hasTerminal, ShrinkHoms, eq_of_comp_right_eq, eq_of_hom, hasTerminal, isTerminalOfUniqueOfIsDiscrete, subsingleton
-/
instance : HasTerminal Cat.{v, u} := by
  have : IsDiscrete (ShrinkHoms.{u} PUnit.{u + 1}) := {
    subsingleton _ _ := { allEq _ _ := eq_of_comp_right_eq (congrFun rfl) }
    eq_of_hom _ := rfl
  }
  exact IsTerminal.hasTerminal (X := Cat.of (ShrinkHoms PUnit)) isTerminalOfUniqueOfIsDiscrete

/--
Definition of `terminalIsoOfUniqueOfIsDiscrete` / `terminalIsoOfUniqueOfIsDiscrete` 的定义

English:
definition terminalIsoOfUniqueOfIsDiscrete
  body: terminalIsoIsTerminal isTerminalOfUniqueOfIsDiscrete

中文:
定义 terminalIsoOfUniqueOfIsDiscrete
  定义体: terminalIsoIsTerminal isTerminalOfUniqueOfIsDiscrete

Depends on / 依赖: isTerminalOfUniqueOfIsDiscrete, terminalIsoIsTerminal
-/
noncomputable def terminalIsoOfUniqueOfIsDiscrete
    {T : Type u} [Category.{v} T] [Unique T] [IsDiscrete T] : ⊤_ Cat.{v, u} ≅ Cat.of T :=
  terminalIsoIsTerminal isTerminalOfUniqueOfIsDiscrete

/--
Definition of `isTerminalDiscretePUnit` / `isTerminalDiscretePUnit` 的定义

English:
definition isTerminalDiscretePUnit
  signature: : IsTerminal (Cat.of (Discrete PUnit))
  body: isTerminalOfUniqueOfIsDiscrete

中文:
定义 isTerminalDiscretePUnit
  签名: : 是终止 (Cat.of (离散 命题单元))
  定义体: isTerminalOfUniqueOfIsDiscrete

Depends on / 依赖: isTerminalOfUniqueOfIsDiscrete
-/
def isTerminalDiscretePUnit : IsTerminal (Cat.of (Discrete PUnit)) :=
  isTerminalOfUniqueOfIsDiscrete

/--
Definition of `isoDiscretePUnitOfIsTerminal` / `isoDiscretePUnitOfIsTerminal` 的定义

English:
definition isoDiscretePUnitOfIsTerminal
  signature: {T : Type u} [Category.{u} T] (hT : IsTerminal (Cat.of T))
  body: IsTerminal.uniqueUpToIso hT isTerminalDiscretePUnit

中文:
定义 isoDiscretePUnitOfIsTerminal
  签名: {T : 类型u} [范畴.{u} T] (hT : 是终止 (Cat.of T))
  定义体: IsTerminal.uniqueUpToIso hT isTerminalDiscretePUnit

Depends on / 依赖: IsTerminal, IsTerminal.uniqueUpToIso, isTerminalDiscretePUnit, uniqueUpToIso
-/
def isoDiscretePUnitOfIsTerminal {T : Type u} [Category.{u} T] (hT : IsTerminal (Cat.of T)) :
    Cat.of T ≅ Cat.of (Discrete PUnit) :=
  IsTerminal.uniqueUpToIso hT isTerminalDiscretePUnit

end CategoryTheory.Cat
