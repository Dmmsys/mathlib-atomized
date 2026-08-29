/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.Order.Fin.Basic

/-!
# Limits and colimits indexed by `Fin`

In this file, we show that `0 : Fin (n + 1)` is an initial object
and `Fin.last n` is a terminal object. This allows to compute
limits and colimits indexed by `Fin (n + 1)`, see
`limitOfDiagramInitial` and `colimitOfDiagramTerminal`
in the file `Limits.Shapes.IsTerminal`.

-/

@[expose] public section

universe v v' u u' w

open CategoryTheory Limits

namespace Fin

variable (n : Nat)

/--
Definition of `isInitialZero` / `isInitialZero` 的定义

English:
definition isInitialZero
  signature: [NeZero n]
  body: isInitialBot

中文:
定义 isInitialZero
  签名: [NeZero n]
  定义体: isInitialBot

Depends on / 依赖: isInitialBot
-/
def isInitialZero [NeZero n] : IsInitial (0 : Fin n) := isInitialBot

/--
Definition of `isTerminalLast` / `isTerminalLast` 的定义

English:
definition isTerminalLast
  signature: : IsTerminal (Fin.last n)
  body: isTerminalTop

中文:
定义 isTerminalLast
  签名: : IsTerminal (Fin.last n)
  定义体: isTerminalTop

Depends on / 依赖: isTerminalTop
-/
def isTerminalLast : IsTerminal (Fin.last n) := isTerminalTop

end Fin
