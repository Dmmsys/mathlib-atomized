/-
Copyright (c) 2025 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

public meta import Lean.Elab.Command
public meta import Lean.Linter.Basic
-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
import Mathlib.Tactic.Linter.Header -- shake: keep

/-!
# Additional utilities and boilerplate for the `Linter` API
-/

public meta section

open Lean Elab Command Linter

namespace Lean.Linter

variable {m : Type -> Type} [Monad m] [MonadOptions m] [MonadEnv m]

/--
Runs a `CommandElabM` action when the provided linter option is `true`.

This function assumes you have already called `withSetOptionIn`; use `whenLinterActivated`
to do so automatically. At the start of linter code, `whenLinterActivated` should be preferred when
possible.

Note: this definition is marked as `@[macro_inline]`, so it is okay to supply it with a linter
option which has been registered in the same module.
-/
@[expose, macro_inline]
/--
Definition of `whenLinterOption` / `whenLinterOption` 的定义

English:
definition whenLinterOption
  signature: (opt : Lean.Option Bool) (x : m Unit)
  body: do
  if getLinterValue opt (← getLinterOptions) then x

中文:
定义 whenLinterOption
  签名: (opt : Lean.选项类型 布尔值) (x : m 单元)
  定义体: do
  if getLinterValue opt (← getLinterOptions) then x
-/
def whenLinterOption (opt : Lean.Option Bool) (x : m Unit) : m Unit := do
  if getLinterValue opt (← getLinterOptions) then x

/--
Runs a `CommandElabM` action when the provided linter option is `false`.

Note: this definition is marked as `@[macro_inline]`, so it is okay to supply it with a linter
option which has been registered in the same module.
-/
@[expose, macro_inline]
/--
Definition of `whenNotLinterOption` / `whenNotLinterOption` 的定义

English:
definition whenNotLinterOption
  signature: (opt : Lean.Option Bool) (x : m Unit)
  body: do
  unless getLinterValue opt (← getLinterOptions) do x

中文:
定义 whenNotLinterOption
  签名: (opt : Lean.选项类型 布尔值) (x : m 单元)
  定义体: do
  unless getLinterValue opt (← getLinterOptions) do x
-/
def whenNotLinterOption (opt : Lean.Option Bool) (x : m Unit) : m Unit := do
  unless getLinterValue opt (← getLinterOptions) do x

/--
Processes `set_option ... in`s that wrap the input `stx`, then acts on the inner syntax with
`x` after checking that the provided linter option is `true`.

If `breakOnError` is `true` (the default), avoids running the linter when errors are present.

This is typically used to start off linter code:
```
def myLinter : Linter where
  run := whenLinterActivated linter.myLinter fun stx ↦ do
    ...
```

Note: this definition is marked as `@[macro_inline]`, so it is okay to supply it with a linter
option which has been registered in the same module.
-/
@[expose, macro_inline]
/--
Definition of `whenLinterActivated` / `whenLinterActivated` 的定义

English:
definition whenLinterActivated
  signature: (opt : Lean.Option Bool) (x : CommandElab) (breakOnError := true)
  body: withSetOptionIn fun stx => whenLinterOption opt do
    unless ← pure breakOnError <&&> MonadLog.hasErrors do
      x stx

中文:
定义 whenLinterActivated
  签名: (opt : Lean.选项类型 布尔值) (x : CommandElab) (breakOnError := true)
  定义体: withSetOptionIn fun stx => whenLinterOption opt do
    unless ← pure breakOnError <&&> MonadLog.hasErrors do
      x stx
-/
def whenLinterActivated (opt : Lean.Option Bool) (x : CommandElab) (breakOnError := true) :
    CommandElab :=
  withSetOptionIn fun stx => whenLinterOption opt do
    unless ← pure breakOnError <&&> MonadLog.hasErrors do
      x stx

end Lean.Linter
