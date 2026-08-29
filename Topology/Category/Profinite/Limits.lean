/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Dagur Asgeirsson
-/
module

public import Mathlib.Topology.Category.Profinite.Basic
public import Mathlib.Topology.Category.CompHausLike.Limits
/-!

# Explicit limits and colimits

This file applies the general API for explicit limits and colimits in `CompHausLike P` (see
the file `Mathlib/Topology/Category/CompHausLike/Limits.lean`) to the special case of `Profinite`.
-/

public section

namespace Profinite

universe u w

open CategoryTheory Limits CompHausLike

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasExplicitPullbacks (fun Y => TotallyDisconnectedSpace Y)
  body: { hasProp :=
    show TotallyDisconnectedSpace {_xy : _ | _} from inferInstance }

中文:
实例 :
  签名: HasExplicitPullbacks (fun Y => TotallyDisconnectedSpace Y)
  定义体: { hasProp :=
    show TotallyDisconnectedSpace {_xy : _ | _} from inferInstance }

Depends on / 依赖: hasProp
-/
instance : HasExplicitPullbacks (fun Y => TotallyDisconnectedSpace Y) where
  hasProp _ _ := { hasProp :=
    show TotallyDisconnectedSpace {_xy : _ | _} from inferInstance }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasExplicitFiniteCoproducts.{w, u} (fun Y => TotallyDisconnectedSpace Y)
  body: { hasProp :=
    show TotallyDisconnectedSpace (Σ (_a : _), _) from inferInstance }

中文:
实例 :
  签名: HasExplicitFiniteCoproducts.{w, u} (fun Y => TotallyDisconnectedSpace Y)
  定义体: { hasProp :=
    show TotallyDisconnectedSpace (Σ (_a : _), _) from inferInstance }

Depends on / 依赖: hasProp
-/
instance : HasExplicitFiniteCoproducts.{w, u} (fun Y => TotallyDisconnectedSpace Y) where
  hasProp _ := { hasProp :=
    show TotallyDisconnectedSpace (Σ (_a : _), _) from inferInstance }

/--
Definition of `isTerminalPUnit` / `isTerminalPUnit` 的定义

English:
abbreviation isTerminalPUnit
  signature: : IsTerminal (Profinite.of PUnit.{u + 1})
  body: CompHausLike.isTerminalPUnit

example : FinitaryExtensive Profinite.{u} := inferInstance

noncomputable example : PreservesFiniteCoproducts profiniteToCompHaus := inferInstance

中文:
缩写 isTerminalPUnit
  签名: : IsTerminal (Profinite.of PUnit.{u + 1})
  定义体: CompHausLike.isTerminalPUnit

example : FinitaryExtensive Profinite.{u} := inferInstance

noncomputable example : PreservesFiniteCoproducts profiniteToCompHaus := inferInstance

Depends on / 依赖: CompHausLike, CompHausLike.isTerminalPUnit, isTerminalPUnit
-/
abbrev isTerminalPUnit : IsTerminal (Profinite.of PUnit.{u + 1}) := CompHausLike.isTerminalPUnit

example : FinitaryExtensive Profinite.{u} := inferInstance

noncomputable example : PreservesFiniteCoproducts profiniteToCompHaus := inferInstance

end Profinite
