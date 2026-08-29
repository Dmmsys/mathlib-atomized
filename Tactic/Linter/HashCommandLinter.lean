/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public meta import Lean.Elab.Command
-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
public meta import Mathlib.Tactic.Linter.Header -- shake: keep
public import Lean.Parser.Command

/-!
# `#`-command linter

The `#`-command linter produces a warning when a command starting with `#` is used *and*
* either the command emits no message;
* or `warningAsError` is set to `true`.

The rationale behind this is that `#`-commands are intended to be transient:
they provide useful information in development, but are not intended to be present in final code.
Most of them are noisy and get picked up anyway by CI, but even the quiet ones are not expected to
outlive their in-development status.
-/

meta section

namespace Mathlib.Linter

/--
The linter emits a warning on any command beginning with `#` that itself emits no message.
For example, `#guard true` and `#check_tactic True ~> True by skip` trigger a message.
There is a list of silent `#`-command that are allowed.
-/
public register_option linter.hashCommand : Bool := {
  defValue := false
  descr := "enable the `#`-command linter"
}

namespace HashCommandLinter

open Lean Elab Linter

open Command in
/--
Definition of `withSetOptionIn'` / `withSetOptionIn'` 的定义

English:
definition withSetOptionIn'
  signature: (cmd : CommandElab)
  body: fun stx => do
  if stx.getKind == ``Lean.Parser.Command.in then
    if stx[0].getKind == ``Lean.Parser.Command.set_option then
      let (opts, _) ← Elab.elabSetOption stx[0][1] stx[0][3]
      withScope (fun scope => { scope with opts }) do
        withSetOptionIn' cmd stx[2]
    else
      withSet

中文:
定义 withSetOptionIn'
  签名: (cmd : CommandElab)
  定义体: fun stx => do
  if stx.getKind == ``Lean.Parser.Command.in then
    if stx[0].getKind == ``Lean.Parser.Command.set_option then
      let (opts, _) ← Elab.elabSetOption stx[0][1] stx[0][3]
      withScope (fun scope => { scope with opts }) do
        withSetOptionIn' cmd stx[2]
    else
      withSet
-/
partial def withSetOptionIn' (cmd : CommandElab) : CommandElab := fun stx => do
  if stx.getKind == ``Lean.Parser.Command.in then
    if stx[0].getKind == ``Lean.Parser.Command.set_option then
      let (opts, _) ← Elab.elabSetOption stx[0][1] stx[0][3]
      withScope (fun scope => { scope with opts }) do
        withSetOptionIn' cmd stx[2]
    else
      withSetOptionIn' cmd stx[2]
  else
    cmd stx

/--
Definition of `allowed_commands` / `allowed_commands` 的定义

English:
abbreviation allowed_commands
  signature: : Std.HashSet String
  body: { "#adaptation_note" }

中文:
缩写 allowed_commands
  签名: : Std.HashSet String
  定义体: { "#adaptation_note" }

Depends on / 依赖: adaptation_note
-/
abbrev allowed_commands : Std.HashSet String := { "#adaptation_note" }

/--
Definition of `hashCommandLinter` / `hashCommandLinter` 的定义

English:
definition hashCommandLinter
  signature: : Linter where run
  body: withSetOptionIn' fun stx => do
  if getLinterValue linter.hashCommand (← getLinterOptions) &&
    ((← get).messages.reportedPlusUnreported.isEmpty || warningAsError.get (← getOptions))
  then
    if let some sa := stx.getHead? then
      let a := sa.getAtomVal
      if (a.front == '#' && ! allowed_c

中文:
定义 hashCommandLinter
  签名: : Linter where run
  定义体: withSetOptionIn' fun stx => do
  if getLinterValue linter.hashCommand (← getLinterOptions) &&
    ((← get).messages.reportedPlusUnreported.isEmpty || warningAsError.get (← getOptions))
  then
    if let some sa := stx.getHead? then
      let a := sa.getAtomVal
      if (a.front == '#' && ! allowed_c

Depends on / 依赖: withSetOptionIn
-/
def hashCommandLinter : Linter where run := withSetOptionIn' fun stx => do
  if getLinterValue linter.hashCommand (← getLinterOptions) &&
    ((← get).messages.reportedPlusUnreported.isEmpty || warningAsError.get (← getOptions))
  then
    if let some sa := stx.getHead? then
      let a := sa.getAtomVal
      if (a.front == '#' && ! allowed_commands.contains a) then
        let msg := m!"`#`-commands, such as '{a}', are not allowed in 'Mathlib'"
        if warningAsError.get (← getOptions) then
          logInfoAt sa (msg ++ " [linter.hashCommand]")
        else Linter.logLint linter.hashCommand sa msg

initialize addLinter hashCommandLinter

end HashCommandLinter
