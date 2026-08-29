/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Init
public meta import Lean.Util.Heartbeats
public meta import Lean.Meta.Tactic.TryThis

/-!
Defines a command wrapper that prints the number of heartbeats used in the enclosed command.

For example
```
#count_heartbeats in
theorem foo : 42 = 6 * 7 := rfl
```
will produce an info message containing a number around 51.
If this number is above the current `maxHeartbeats`, we also print a `Try this:` suggestion.
-/

public meta section


open Lean Elab Command Meta Linter

namespace Mathlib.CountHeartbeats

-- This file mentions bare `set_option maxHeartbeats` by design: do not warn about this.
set_option linter.style.setOption false

open Tactic

/--
Definition of `runTacForHeartbeats` / `runTacForHeartbeats` 的定义

English:
definition runTacForHeartbeats
  signature: (tac : TSyntax `Lean.Parser.Tactic.tacticSeq) (revert : Bool := true)
  body: do
  let start ← IO.getNumHeartbeats
  let s ← saveState
  withOptions (fun opts => opts.set ``Elab.async false) do
    evalTactic tac
  if revert then restoreState s
  return (← IO.getNumHeartbeats) - start

中文:
定义 runTacForHeartbeats
  签名: (tac : TSyntax `Lean.Parser.Tactic.tacticSeq) (revert : 布尔值 := true)
  定义体: do
  let start ← IO.getNumHeartbeats
  let s ← saveState
  withOptions (fun opts => opts.set ``Elab.async false) do
    evalTactic tac
  if revert then restoreState s
  return (← IO.getNumHeartbeats) - start
-/
def runTacForHeartbeats (tac : TSyntax `Lean.Parser.Tactic.tacticSeq) (revert : Bool := true) :
    TacticM Nat := do
  let start ← IO.getNumHeartbeats
  let s ← saveState
  withOptions (fun opts => opts.set ``Elab.async false) do
    evalTactic tac
  if revert then restoreState s
  return (← IO.getNumHeartbeats) - start

/--
Definition of `variation` / `variation` 的定义

English:
definition variation
  signature: (counts : List Nat)
  body: let min := counts.min?.getD 0
  let max := counts.max?.getD 0
  let toFloat (n : Nat) := n.toUInt64.toFloat
  let toNat (f : Float) := f.toUInt64.toNat
  let counts' := counts.map toFloat
  let μ : Float := counts'.foldl (· + ·) 0 / toFloat counts.length
let stddev : Float := Float.sqrt
    ((counts

中文:
定义 variation
  签名: (counts : 列表 自然数)
  定义体: let min := counts.min?.getD 0
  let max := counts.max?.getD 0
  let toFloat (n : Nat) := n.toUInt64.toFloat
  let toNat (f : Float) := f.toUInt64.toNat
  let counts' := counts.map toFloat
  let μ : Float := counts'.foldl (· + ·) 0 / toFloat counts.length
let stddev : Float := Float.sqrt
    ((counts

Depends on / 依赖: Float.sqrt, counts, counts.length, counts.map, counts.max, counts.min, f.toUInt64.toNat, length, n.toUInt64.toFloat, stddev, toFloat, toUInt64
-/
def variation (counts : List Nat) : List Nat :=
  let min := counts.min?.getD 0
  let max := counts.max?.getD 0
  let toFloat (n : Nat) := n.toUInt64.toFloat
  let toNat (f : Float) := f.toUInt64.toNat
  let counts' := counts.map toFloat
  let μ : Float := counts'.foldl (· + ·) 0 / toFloat counts.length
let stddev : Float := Float.sqrt
    ((counts'.map fun i => (i - μ)^2).foldl (· + ·) 0) / toFloat counts.length
  [min, max, toNat stddev]

/--
Definition of `logVariation` / `logVariation` 的定义

English:
definition logVariation
  signature: {m} [Monad m] [MonadLog m] [AddMessageContext m] [MonadOptions m]
  body: do
  if let [min, max, stddev] := variation counts then
  -- convert `[min, max, stddev]` to user-facing heartbeats
  logInfo s!"Min: {min / 1000} Max: {max / 1000} StdDev: {stddev / 10}%"

中文:
定义 logVariation
  签名: {m} [单子 m] [MonadLog m] [AddMessageContext m] [MonadOptions m]
  定义体: do
  if let [min, max, stddev] := variation counts then
  -- convert `[min, max, stddev]` to user-facing heartbeats
  logInfo s!"Min: {min / 1000} Max: {max / 1000} StdDev: {stddev / 10}%"
-/
def logVariation {m} [Monad m] [MonadLog m] [AddMessageContext m] [MonadOptions m]
    (counts : List Nat) : m Unit := do
  if let [min, max, stddev] := variation counts then
  -- convert `[min, max, stddev]` to user-facing heartbeats
  logInfo s!"Min: {min / 1000} Max: {max / 1000} StdDev: {stddev / 10}%"

/-- `#count_heartbeats tac` counts the heartbeats used by the tactic sequence `tac`
and prints an info line with the number of heartbeats.

* `#count_heartbeats! n in tac`, where `n` is an optional natural number literal, runs `tac`
  `n` times on the same goal while counting the heartbeats, and prints an info line with range and
  standard deviation. `n` can be left out, and defaults to 10.

Example:

```
example : 1 + 1 = 2 := by
  -- The next line will print an info message of this format; the exact number may vary.
  -- info: 4646
  #count_heartbeats simp

example : 1 + 1 = 2 := by
  -- The next line will print an info message of this format; the exact numbers may vary.
  -- info: Min: 4 Max: 4 StdDev: 2%
  #count_heartbeats! 37 in simp
```
-/
elab "#count_heartbeats " tac:tacticSeq : tactic => do
  logInfo s!"{← runTacForHeartbeats tac (revert := false)}"

@[tactic_alt «tactic#count_heartbeats_»]
elab "#count_heartbeats! " n:(num)? "in" ppLine tac:tacticSeq : tactic => do
  let n := match n with
           | some j => j.getNat
           | none => 10
  -- First run the tactic `n-1` times, reverting the state.
  let counts ← (List.range (n - 1)).mapM fun _ => runTacForHeartbeats tac
  -- Then run once more, keeping the state.
  let counts := (← runTacForHeartbeats tac (revert := false)) :: counts
  logVariation counts

/--
Definition of `roundDownIf` / `roundDownIf` 的定义

English:
definition roundDownIf
  signature: (n : Nat) (approx : Bool)
  body: if approx then s!"approximately {(n / 1000) * 1000}" else s!"{n}"

中文:
定义 roundDownIf
  签名: (n : 自然数) (approx : 布尔值)
  定义体: if approx then s!"approximately {(n / 1000) * 1000}" else s!"{n}"

Depends on / 依赖: approx, approximately
-/
def roundDownIf (n : Nat) (approx : Bool) : String :=
  if approx then s!"approximately {(n / 1000) * 1000}" else s!"{n}"

set_option linter.style.maxHeartbeats false in
/--
`#count_heartbeats in cmd` counts the heartbeats used in the enclosed command `cmd`.
Use `#count_heartbeats` to count the heartbeats in *all* the following declarations.

This is most useful for setting sufficient but reasonable limits via `set_option maxHeartbeats`
for long-running declarations.

If you do so, please resist the temptation to set the limit as low as possible.
As the `simp` set and other features of the library evolve,
other contributors will find that their (likely unrelated) changes
have pushed the declaration over the limit.
`count_heartbeats in` will automatically suggest a `set_option maxHeartbeats` via "Try this:"
using the least number of the form `2^k * 200000` that suffices.

Note that the internal heartbeat counter accessible via `IO.getNumHeartbeats`
has granularity 1000 times finer than the limits set by `set_option maxHeartbeats`.
As this is intended as a user command, we divide by 1000.

The optional `approximately` keyword rounds down the heartbeats to the nearest thousand.
This helps make the tests more stable to small changes in heartbeats.
To use this functionality, use `#count_heartbeats approximately in cmd`.
-/
elab "#count_heartbeats " approx:(&"approximately ")? "in" ppLine cmd:command : command => do
  let start ← IO.getNumHeartbeats
  try
    elabCommand (← `(command| set_option maxHeartbeats 0 in $cmd))
  finally
    let finish ← IO.getNumHeartbeats
    let elapsed := (finish - start) / 1000
    let roundElapsed := roundDownIf elapsed approx.isSome
    let max := (← Command.liftCoreM getMaxHeartbeats) / 1000
    if elapsed < max then
      logInfo
        m!"Used {roundElapsed} heartbeats, which is less than the current maximum of {max}."
    else
      let mut max' := max
      while max' < elapsed do
        max' := 2 * max'
      logInfo
        m!"Used {roundElapsed} heartbeats, which is greater than the current maximum of {max}."
      let m : TSyntax `num := quote max'
Command.liftCoreM MetaM.run' do
        Lean.Meta.Tactic.TryThis.addSuggestion (← getRef)
          (← (set_option hygiene false in `(command| set_option maxHeartbeats $m in $cmd)))

set_option linter.style.maxHeartbeats false in
/--
Guard the minimal number of heartbeats used in the enclosed command.

This is most useful in the context of debugging and minimizing an example of a slow declaration.
By guarding the number of heartbeats used in the slow declaration,
an error message will be generated if a minimization step makes the slow behaviour go away.

The default number of minimal heartbeats is the value of `maxHeartbeats` (typically 200000).
Alternatively, you can specify a number of heartbeats to guard against,
using the syntax `guard_min_heartbeats n in cmd`.

The optional `approximately` keyword rounds down the heartbeats to the nearest thousand.
This helps make the tests more stable to small changes in heartbeats.
To use this functionality, use `guard_min_heartbeats approximately (n)? in cmd`.
-/
elab "guard_min_heartbeats " approx:(&"approximately ")? n:(num)? "in" ppLine cmd:command :
    command => do
  let max := (← Command.liftCoreM getMaxHeartbeats) / 1000
  let n := match n with
           | some j => j.getNat
           | none => max
  let start ← IO.getNumHeartbeats
  try
    elabCommand (← `(command| set_option Elab.async false in set_option maxHeartbeats 0 in $cmd))
  finally
    let finish ← IO.getNumHeartbeats
    let elapsed := (finish - start) / 1000
    if elapsed < n then
      logInfo m!"Used {roundDownIf elapsed approx.isSome} heartbeats, \
                which is less than the minimum of {n}."

set_option linter.style.maxHeartbeats false in
/--
Definition of `elabForHeartbeats` / `elabForHeartbeats` 的定义

English:
definition elabForHeartbeats
  signature: (cmd : TSyntax `command) (revert : Bool := true)
  body: do
  let start ← IO.getNumHeartbeats
  let s ← get
  elabCommand (← `(command| set_option maxHeartbeats 0 in $cmd))
  if revert then set s
  return (← IO.getNumHeartbeats) - start

中文:
定义 elabForHeartbeats
  签名: (cmd : TSyntax `command) (revert : 布尔值 := true)
  定义体: do
  let start ← IO.getNumHeartbeats
  let s ← get
  elabCommand (← `(command| set_option maxHeartbeats 0 in $cmd))
  if revert then set s
  return (← IO.getNumHeartbeats) - start

Depends on / 依赖: CommandElabM
-/
def elabForHeartbeats (cmd : TSyntax `command) (revert : Bool := true) : CommandElabM Nat := do
  let start ← IO.getNumHeartbeats
  let s ← get
  elabCommand (← `(command| set_option maxHeartbeats 0 in $cmd))
  if revert then set s
  return (← IO.getNumHeartbeats) - start

/--
`#count_heartbeats! in cmd` runs a command `10` times, reporting the range in heartbeats, and the
standard deviation. The command `#count_heartbeats! n in cmd` runs it `n` times instead.

Example usage:
```
#count_heartbeats! in
def f := 37
```
displays the info message `Min: 7 Max: 8 StdDev: 14%`.
-/
elab "#count_heartbeats! " n:(num)? "in" ppLine cmd:command : command => do
  let n := match n with
           | some j => j.getNat
           | none => 10
  -- First run the command `n-1` times, reverting the state.
  let counts ← (List.range (n - 1)).mapM fun _ => elabForHeartbeats cmd
  -- Then run once more, keeping the state.
  let counts := (← elabForHeartbeats cmd (revert := false)) :: counts
  logVariation counts

end CountHeartbeats

end Mathlib

/-!
# The "countHeartbeats" linter

The "countHeartbeats" linter counts the heartbeats of every declaration.
-/

namespace Mathlib.Linter

/--
The "countHeartbeats" linter counts the heartbeats of every declaration.

The effect of the linter is similar to `#count_heartbeats in xxx`, except that it applies
to all declarations.

Note that the linter only counts heartbeats in "top-level" declarations:
it looks inside `set_option ... in`, but not, for instance, inside `mutual` blocks.

There is a convenience notation `#count_heartbeats` that simply sets the linter option to true.
-/
@[deprecated "use `#count_heartbeats in` or `set_option trace.profiler true` with \
  `set_option trace.profiler.useHeartbeats true`" (since := "2026-07-30")]
register_option linter.countHeartbeats : Bool := {
  defValue := false
  descr := "enable the countHeartbeats linter"
}

/--
An option used by the `countHeartbeats` linter: if set to `true`, then the countHeartbeats linter
rounds down to the nearest 1000 the heartbeat count.
-/
@[deprecated "use `#count_heartbeats in` or `set_option trace.profiler true` with \
  `set_option trace.profiler.useHeartbeats true`" (since := "2026-07-30")]
register_option linter.countHeartbeatsApprox : Bool := {
  defValue := false
  descr := "if set to `true`, then the countHeartbeats linter rounds down \
            to the nearest 1000 the heartbeat count"
}

namespace CountHeartbeats

@[inherit_doc Mathlib.Linter.linter.countHeartbeats,
deprecated "use `#count_heartbeats in` or `set_option trace.profiler true` with \
  `set_option trace.profiler.useHeartbeats true`" (since := "2026-07-30")]
/--
Definition of `countHeartbeatsLinter` / `countHeartbeatsLinter` 的定义

English:
definition countHeartbeatsLinter
  signature: : Linter where run
  body: withSetOptionIn fun stx => do
  unless getLinterValue linter.countHeartbeats (← getLinterOptions) do
    return
  if (← get).messages.hasErrors then
    return
  let mut msgs := #[]
  if [``Lean.Parser.Command.declaration, `lemma].contains stx.getKind then
    let s ← get
    if getLinterValue linte

中文:
定义 countHeartbeatsLinter
  签名: : Linter where run
  定义体: withSetOptionIn fun stx => do
  unless getLinterValue linter.countHeartbeats (← getLinterOptions) do
    return
  if (← get).messages.hasErrors then
    return
  let mut msgs := #[]
  if [``Lean.Parser.Command.declaration, `lemma].contains stx.getKind then
    let s ← get
    if getLinterValue linte

Depends on / 依赖: withSetOptionIn
-/
def countHeartbeatsLinter : Linter where run := withSetOptionIn fun stx => do
  unless getLinterValue linter.countHeartbeats (← getLinterOptions) do
    return
  if (← get).messages.hasErrors then
    return
  let mut msgs := #[]
  if [``Lean.Parser.Command.declaration, `lemma].contains stx.getKind then
    let s ← get
    if getLinterValue linter.countHeartbeatsApprox (← getLinterOptions) then
      elabCommand (← `(command| #count_heartbeats approximately in $(⟨stx⟩)))
    else
      elabCommand (← `(command| #count_heartbeats in $(⟨stx⟩)))
    msgs := (← get).messages.unreported.toArray.filter (·.severity != .error)
    set s
  match stx.find? (·.isOfKind ``Parser.Command.declId) with
    | some decl =>
      for msg in msgs do logInfoAt decl m!"'{decl[0].getId}' {(← msg.toString).decapitalize}"
    | none =>
      for msg in msgs do logInfoAt stx m!"{← msg.toString}"

set_option linter.deprecated false in
initialize addLinter countHeartbeatsLinter

@[inherit_doc Mathlib.Linter.linter.countHeartbeats]
macro (name := countHeartbeats) "#count_heartbeats" approx:(&" approximately")? : command => do
  let approx ←
    if approx.isSome then
      `(set_option linter.countHeartbeatsApprox true) else
      `(set_option linter.countHeartbeatsApprox false)
  return ⟨mkNullNode
    #[← `(command| set_option linter.countHeartbeats true),
      approx]⟩

deprecated_syntax countHeartbeats "use `#count_heartbeats in` or \
  `set_option trace.profiler true` with `set_option trace.profiler.useHeartbeats true`"
  (since := "2026-07-30")

end CountHeartbeats

end Mathlib.Linter
