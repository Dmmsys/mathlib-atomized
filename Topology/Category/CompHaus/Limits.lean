/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Dagur Asgeirsson
-/
module

public import Mathlib.Topology.Category.CompHaus.Basic
public import Mathlib.Topology.Category.CompHausLike.Limits
/-!

# Explicit limits and colimits

This file applies the general API for explicit limits and colimits in `CompHausLike P` (see
the file `Mathlib/Topology/Category/CompHausLike/Limits.lean`) to the special case of `CompHaus`.
-/

@[expose] public section

namespace CompHaus

universe u w

open CategoryTheory Limits CompHausLike

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasExplicitPullbacks (fun _ => True)
  body: inferInstance

中文:
实例 :
  签名: HasExplicitPullbacks (fun _ => True)
  定义体: inferInstance
-/
instance : HasExplicitPullbacks (fun _ => True) where
  hasProp _ _ := inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasExplicitFiniteCoproducts.{w, u} (fun _ => True)
  body: inferInstance

example : FinitaryExtensive CompHaus.{u} := inferInstance

中文:
实例 :
  签名: HasExplicitFiniteCoproducts.{w, u} (fun _ => True)
  定义体: inferInstance

example : FinitaryExtensive CompHaus.{u} := inferInstance
-/
instance : HasExplicitFiniteCoproducts.{w, u} (fun _ => True) where
  hasProp _ := inferInstance

example : FinitaryExtensive CompHaus.{u} := inferInstance

/--
Definition of `isTerminalPUnit` / `isTerminalPUnit` 的定义

English:
abbreviation isTerminalPUnit
  signature: : IsTerminal (CompHaus.of PUnit.{u + 1})
  body: CompHausLike.isTerminalPUnit

中文:
缩写 isTerminalPUnit
  签名: : IsTerminal (CompHaus.of PUnit.{u + 1})
  定义体: CompHausLike.isTerminalPUnit

Depends on / 依赖: CompHausLike, CompHausLike.isTerminalPUnit, isTerminalPUnit
-/
abbrev isTerminalPUnit : IsTerminal (CompHaus.of PUnit.{u + 1}) := CompHausLike.isTerminalPUnit

/--
Definition of `terminalIsoPUnit` / `terminalIsoPUnit` 的定义

English:
definition terminalIsoPUnit
  signature: : ⊤_ CompHaus.{u} ≅ CompHaus.of PUnit
  body: terminalIsTerminal.uniqueUpToIso CompHaus.isTerminalPUnit

noncomputable example : PreservesFiniteCoproducts compHausToTop := inferInstance

中文:
定义 terminalIsoPUnit
  签名: : ⊤_ CompHaus.{u} ≅ CompHaus.of PUnit
  定义体: terminalIsTerminal.uniqueUpToIso CompHaus.isTerminalPUnit

noncomputable example : PreservesFiniteCoproducts compHausToTop := inferInstance

Depends on / 依赖: CompHaus, CompHaus.isTerminalPUnit, isTerminalPUnit, terminalIsTerminal, terminalIsTerminal.uniqueUpToIso, uniqueUpToIso
-/
noncomputable def terminalIsoPUnit : ⊤_ CompHaus.{u} ≅ CompHaus.of PUnit :=
  terminalIsTerminal.uniqueUpToIso CompHaus.isTerminalPUnit

noncomputable example : PreservesFiniteCoproducts compHausToTop := inferInstance

end CompHaus
