/-
Copyright (c) 2024 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, Moritz Firsching
-/
module

public meta import Lean.DeclarationRange
public meta import Lean.ResolveName
-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
public meta import Mathlib.Tactic.Linter.Header  -- shake: keep
public import Lean.Message

/-!
This file contains functions that are used by multiple linters.
-/

public meta section

open Lean Parser Elab Command Meta
namespace Mathlib.Linter

/--
If `pos` is a `String.Pos`, then `getNamesFrom pos` returns the array of identifiers
for the names of the declarations whose syntax begins in position at least `pos`.
-/
/-
**Mathlib.Linter.getNamesFrom** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Linter`。
形式化陈述：getNamesFrom {m} [Monad m] [MonadEnv m] [MonadFileMap m] (pos : String.Pos
.Raw) : m (Array Syntax)
参数：pos : String.Pos.Raw。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `pos` is a `String.Pos`, then `getNamesFrom pos` returns the array of identif
iers
for the names of the declarations whose syntax begins in position at least `pos`
.
-/
def getNamesFrom {m} [Monad m] [MonadEnv m] [MonadFileMap m] (pos : String.Pos.Raw) :
    m (Array Syntax) := do
  -- declarations from parallelism branches should not be interesting here, so use `local`
  let drs := declRangeExt.toPersistentEnvExtension.getState (asyncMode := .local) (← getEnv)
  let fm ← getFileMap
  let mut nms := #[]
  for (nm, rgs) in drs do
    if pos ≤ fm.ofPosition rgs.range.pos then
      let ofPos1 := fm.ofPosition rgs.selectionRange.pos
      let ofPos2 := fm.ofPosition rgs.selectionRange.endPos
      nms := nms.push (mkIdentFrom (.ofRange ⟨ofPos1, ofPos2⟩) nm)
  return nms

/--
If `stx` is a syntax node for an `export` statement, then `getAliasSyntax stx` returns the array of
identifiers with the "exported" names.
-/
/-
**Mathlib.Linter.getAliasSyntax** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Linter`。
形式化陈述：getAliasSyntax {m} [Monad m] [MonadResolveName m] (stx : Syntax) : m (Arra
y Syntax)
参数：stx : Syntax。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `stx` is a syntax node for an `export` statement, then `getAliasSyntax stx` r
eturns the array of
identifiers with the "exported" names.
-/
def getAliasSyntax {m} [Monad m] [MonadResolveName m] (stx : Syntax) : m (Array Syntax) := do
  let mut aliases := #[]
  if let `(export $_ ($ids*)) := stx then
    let currNamespace ← getCurrNamespace
    for idStx in ids do
      let id := idStx.getId
      aliases := aliases.push
        (mkIdentFrom (.ofRange (idStx.raw.getRange?.getD default)) (currNamespace ++ id))
  return aliases

/-- Used for linters which use `0` instead of `false` for disabling. -/
/-
**Mathlib.Linter.logLint0Disable** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Linter`。
形式化陈述：logLint0Disable {m} [Monad m] [MonadLog m] [AddMessageContext m] [MonadOpt
ions m] (linterOption : Lean.Option Nat) (stx : Syntax) (msg : MessageData) : m 
Unit
参数：linterOption : Lean.Option Nat；stx : Syntax；msg : MessageData。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Used for linters which use `0` instead of `false` for disabling.
-/
def logLint0Disable {m} [Monad m] [MonadLog m] [AddMessageContext m] [MonadOptions m]
    (linterOption : Lean.Option Nat) (stx : Syntax) (msg : MessageData) : m Unit :=
  let disable := .note m!"This linter can be disabled with `set_option {linterOption.name} 0`"
  logWarningAt stx (.tagged linterOption.name m!"{msg}{disable}")
