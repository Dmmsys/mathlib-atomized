/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Basic  -- shake: keep (tactic dependency)

/-!
The command `name_power_vars` names variables in
`MvPowerSeries (Fin n) R` for the appropriate value of `n`.
The notation introduced by this command is local.

Usage:

```lean
variable (R : Type) [CommRing R]

name_power_vars X, Y, Z over R

#check Y -- Y : MvPowerSeries (Fin 3) R
```
-/

public meta section

open Lean Elab Command

namespace Mathlib.Tactic

/--
The command `name_power_vars` names variables in
`MvPowerSeries (Fin n) R` for the appropriate value of `n`.
The notation introduced by this command is local.

Usage:

```lean
variable (R : Type) [CommRing R]

name_power_vars X, Y, Z over R

#check Y -- Y : MvPowerSeries (Fin 3) R
```
-/
syntax (name := namePowerVarsOver) "name_power_vars" (ppSpace ident),+ " over " term : command

@[command_elab namePowerVarsOver, inherit_doc namePowerVarsOver]
/-
**Mathlib.Tactic.elabNamePowerSeriesVariablesOver** 是 Mathlib 中的一个定义，位于命名空间 `Mat
hlib.Tactic`。
形式化陈述：elabNamePowerSeriesVariablesOver : CommandElab | `(command|name_power_vars
 $vars:ident,* over $R:term) => do let vars
该定义给出了一等式。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.zero_lt_one`：0 < 1
-/
def elabNamePowerSeriesVariablesOver : CommandElab
| `(command|name_power_vars $vars:ident,* over $R:term) => do
  let vars := vars.getElems
  let size := vars.size
  let sizeStx : TSyntax `term := quote size
  for h : idx in [:size] do
    let var := vars[idx]
    let var := quote s!"{var.getId}"
    let idx : TSyntax `term ← `(($(quote idx) : Fin $sizeStx))
    let cmd ← `(command|local notation3 $var:str =>
      MvPowerSeries.X (R := $R) (σ := Fin $sizeStx) $idx)
    elabCommand cmd
| _ => throwUnsupportedSyntax

end Mathlib.Tactic

