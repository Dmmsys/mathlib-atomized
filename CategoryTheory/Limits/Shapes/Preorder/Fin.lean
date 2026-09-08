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

variable (n : ℕ)

/-- `0` is an initial object in `Fin n` when `n ≠ 0`. -/
/-
**Fin.isInitialZero** 是 Mathlib 中的一个定义，位于命名空间 `Fin`。
形式化陈述：isInitialZero [NeZero n] : IsInitial (0 : Fin n)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`0` is an initial object in `Fin n` when `n ≠ 0`.
-/
def isInitialZero [NeZero n] : IsInitial (0 : Fin n) := isInitialBot

/-- `Fin.last n` is a terminal object in `Fin (n + 1)`. -/
/-
**Fin.isTerminalLast** 是 Mathlib 中的一个定义，位于命名空间 `Fin`。
形式化陈述：isTerminalLast : IsTerminal (Fin.last n)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Fin.last n` is a terminal object in `Fin (n + 1)`.
-/
def isTerminalLast : IsTerminal (Fin.last n) := isTerminalTop

end Fin

