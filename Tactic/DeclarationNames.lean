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
public meta import Mathlib.Tactic.Linter.Header -- shake: keep
public import Lean.Message

/-!
This file contains functions that are used by multiple linters.
-/

public meta section

open Lean Parser Elab Command Meta
namespace Mathlib.Linter

/--
Definition of `getNamesFrom` / `getNamesFrom` 的定义

English:
definition getNamesFrom
  signature: {m} [Monad m] [MonadEnv m] [MonadFileMap m] (pos : String.Pos.Raw)
  body: do
  -- declarations from parallelism branches should not be interesting here, so use `local`
  let drs := declRangeExt.toPersistentEnvExtension.getState (asyncMode := .local) (← getEnv)
  let fm ← getFileMap
  let mut nms := #[]
  for (nm, rgs) in drs do
    if pos <= fm.ofPosition rgs.range.pos th

中文:
定义 getNamesFrom
  签名: {m} [单子 m] [MonadEnv m] [MonadFileMap m] (pos : String.Pos.Raw)
  定义体: do
  -- declarations from parallelism branches should not be interesting here, so use `local`
  let drs := declRangeExt.toPersistentEnvExtension.getState (asyncMode := .local) (← getEnv)
  let fm ← getFileMap
  let mut nms := #[]
  for (nm, rgs) in drs do
    if pos <= fm.ofPosition rgs.range.pos th
-/
def getNamesFrom {m} [Monad m] [MonadEnv m] [MonadFileMap m] (pos : String.Pos.Raw) :
    m (Array Syntax) := do
  -- declarations from parallelism branches should not be interesting here, so use `local`
  let drs := declRangeExt.toPersistentEnvExtension.getState (asyncMode := .local) (← getEnv)
  let fm ← getFileMap
  let mut nms := #[]
  for (nm, rgs) in drs do
    if pos <= fm.ofPosition rgs.range.pos then
      let ofPos1 := fm.ofPosition rgs.selectionRange.pos
      let ofPos2 := fm.ofPosition rgs.selectionRange.endPos
      nms := nms.push (mkIdentFrom (.ofRange ⟨ofPos1, ofPos2⟩) nm)
  return nms

/--
Definition of `getAliasSyntax` / `getAliasSyntax` 的定义

English:
definition getAliasSyntax
  signature: {m} [Monad m] [MonadResolveName m] (stx : Syntax)
  body: do
  let mut aliases := #[]
  if let `(export $_ ($ids*)) := stx then
    let currNamespace ← getCurrNamespace
    for idStx in ids do
      let id := idStx.getId
      aliases := aliases.push
        (mkIdentFrom (.ofRange (idStx.raw.getRange?.getD default)) (currNamespace ++ id))
  return aliases

中文:
定义 getAliasSyntax
  签名: {m} [单子 m] [MonadResolveName m] (stx : Syntax)
  定义体: do
  let mut aliases := #[]
  if let `(export $_ ($ids*)) := stx then
    let currNamespace ← getCurrNamespace
    for idStx in ids do
      let id := idStx.getId
      aliases := aliases.push
        (mkIdentFrom (.ofRange (idStx.raw.getRange?.getD default)) (currNamespace ++ id))
  return aliases
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

/--
Definition of `logLint0Disable` / `logLint0Disable` 的定义

English:
definition logLint0Disable
  signature: {m} [Monad m] [MonadLog m] [AddMessageContext m] [MonadOptions m]
  body: let disable := .note m!"This linter can be disabled with `set_option {linterOption.name} 0`"
  logWarningAt stx (.tagged linterOption.name m!"{msg}{disable}")

中文:
定义 logLint0Disable
  签名: {m} [单子 m] [MonadLog m] [AddMessageContext m] [MonadOptions m]
  定义体: let disable := .note m!"This linter can be disabled with `set_option {linterOption.name} 0`"
  logWarningAt stx (.tagged linterOption.name m!"{msg}{disable}")

Depends on / 依赖: disable, disabled, linter, linterOption, linterOption.name, logWarningAt, set_option, tagged
-/
def logLint0Disable {m} [Monad m] [MonadLog m] [AddMessageContext m] [MonadOptions m]
    (linterOption : Lean.Option Nat) (stx : Syntax) (msg : MessageData) : m Unit :=
  let disable := .note m!"This linter can be disabled with `set_option {linterOption.name} 0`"
  logWarningAt stx (.tagged linterOption.name m!"{msg}{disable}")
