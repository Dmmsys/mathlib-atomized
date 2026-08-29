/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.ConcreteCategory.Forget
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic

/-!
A `forget₂ C D` forgetful functor between concrete categories `C` and `D`
whose forgetful functors both reflect isomorphisms, itself reflects isomorphisms.
-/

public section


universe t₁ t₂ w

namespace CategoryTheory

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget Type*).ReflectsIsomorphisms
  body: i

中文:
实例 :
  签名: (forget 类型).反映同构
  定义体: i
-/
instance : (forget Type*).ReflectsIsomorphisms where reflects _ _ _ {i} := i

variable (C : Type*) [Category* C]
    {FC : outParam <| C -> C -> Type t₁} {CC : outParam <| C -> Type w}
    [outParam <| forall X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{w} C FC]
variable (D : Type*) [Category* D]
    {FD : outParam <| D -> D -> Type t₂} {CD : outParam <| D -> Type w}
    [outParam <| forall X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory.{w} D FD]

/--
Instance `reflectsIsomorphisms_forget₂` / 实例 `reflectsIsomorphisms_forget₂`

English:
instance reflectsIsomorphisms_forget₂
  signature: [HasForget₂ C D] [(forget C).ReflectsIsomorphisms]
  body: { reflects := fun X Y f {i} => by
      have i' : IsIso ((forget D).map ((forget₂ C D).map f)) := Functor.map_isIso (forget D) _
      have : IsIso ((forget C).map f) := by
        rwa [← @HasForget₂.forget_comp (C := C) (D := D)]
      apply isIso_of_reflects_iso f (forget C) }

中文:
实例 reflectsIsomorphisms_forget₂
  签名: [有Forget₂ C D] [(forget C).反映同构]
  定义体: { reflects := fun X Y f {i} => by
      have i' : IsIso ((forget D).map ((forget₂ C D).map f)) := Functor.map_isIso (forget D) _
      have : IsIso ((forget C).map f) := by
        rwa [← @HasForget₂.forget_comp (C := C) (D := D)]
      apply isIso_of_reflects_iso f (forget C) }

Depends on / 依赖: Functor, Functor.map_isIso, forget, forget_comp, isIso_of_reflects_iso, map_isIso, reflects
-/
instance reflectsIsomorphisms_forget₂ [HasForget₂ C D] [(forget C).ReflectsIsomorphisms] :
    (forget₂ C D).ReflectsIsomorphisms :=
  { reflects := fun X Y f {i} => by
      have i' : IsIso ((forget D).map ((forget₂ C D).map f)) := Functor.map_isIso (forget D) _
      have : IsIso ((forget C).map f) := by
        rwa [← @HasForget₂.forget_comp (C := C) (D := D)]
      apply isIso_of_reflects_iso f (forget C) }

end CategoryTheory
