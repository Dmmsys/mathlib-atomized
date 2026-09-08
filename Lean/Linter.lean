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
import Mathlib.Tactic.Linter.Header  -- shake: keep

/-!
# Additional utilities and boilerplate for the `Linter` API
-/

public meta section

open Lean Elab Command Linter

namespace Lean.Linter

variable {m : Type → Type} [Monad m] [MonadOptions m] [MonadEnv m]

/--
Runs a `CommandElabM` action when the provided linter option is `true`.

This function assumes you have already called `withSetOptionIn`; use `whenLinterActivated`
to do so automatically. At the start of linter code, `whenLinterActivated` should be preferred when
possible.

Note: this definition is marked as `@[macro_inline]`, so it is okay to supply it with a linter
option which has been registered in the same module.
-/
@[expose, macro_inline]
/-
**Lean.Linter.whenLinterOption** 是 Mathlib 中的一个定义，位于命名空间 `Lean.Linter`。
形式化陈述：whenLinterOption (opt : Lean.Option Bool) (x : m Unit) : m Unit
参数：opt : Lean.Option Bool；x : m Unit。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Runs a `CommandElabM` action when the provided linter option is `true`.

This function assumes you have already called `withSetOptionIn`; use `whenLinter
Activated`
to do so automatically. At the start of linter code, `whenLinterActivated` shoul
d be preferred when
possible.

Note: this definition is marked as `@[macro_inline]`, so it is okay to supply it
 with a linter
option which has been registered in the same module.
-/
def whenLinterOption (opt : Lean.Option Bool) (x : m Unit) : m Unit := do
  if getLinterValue opt (← getLinterOptions) then x

/--
Runs a `CommandElabM` action when the provided linter option is `false`.

Note: this definition is marked as `@[macro_inline]`, so it is okay to supply it with a linter
option which has been registered in the same module.
-/
@[expose, macro_inline]
/-
**Lean.Linter.whenNotLinterOption** 是 Mathlib 中的一个定义，位于命名空间 `Lean.Linter`。
形式化陈述：whenNotLinterOption (opt : Lean.Option Bool) (x : m Unit) : m Unit
参数：opt : Lean.Option Bool；x : m Unit。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Runs a `CommandElabM` action when the provided linter option is `false`.

Note: this definition is marked as `@[macro_inline]`, so it is okay to supply it
 with a linter
option which has been registered in the same module.
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
/-
**Lean.Linter.whenLinterActivated** 是 Mathlib 中的一个定义，位于命名空间 `Lean.Linter`。
形式化陈述：whenLinterActivated (opt : Lean.Option Bool) (x : CommandElab) (breakOnErr
or
参数：opt : Lean.Option Bool；x : CommandElab。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Processes `set_option ... in`s that wrap the input `stx`, then acts on the inner
 syntax with
`x` after checking that the provided linter option is `true`.

If `breakOnError` is `true` (the default), avoids running the linter when errors
 are present.

This is typically used to start off linter code:
```
def myLinter : Linter where
  run := whenLinterActivated linter.myLinter fun stx ↦ do
    ...
```

Note: this definition is marked as `@[macro_inline]`, so it is okay to supply it
 with a linter
option which has been registered in the same module.
-/
def whenLinterActivated (opt : Lean.Option Bool) (x : CommandElab) (breakOnError := true) :
    CommandElab :=
  withSetOptionIn fun stx => whenLinterOption opt do
    unless ← pure breakOnError <&&> MonadLog.hasErrors do
      x stx

end Lean.Linter

