/-
Copyright (c) 2023 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
module

public import Mathlib.Init
public meta import Lean.Elab.Tactic.Basic

/-!
# Defines `sleep_heartbeats` tactic.

This is useful for testing / debugging long running commands or elaboration in a somewhat precise
manner.
-/

public meta section
open Lean Elab

/--
Definition of `sleepAtLeastHeartbeats` / `sleepAtLeastHeartbeats` 的定义

English:
definition sleepAtLeastHeartbeats
  signature: (n : Nat)
  body: do
  -- TODO: adjust docstring
  IO.addHeartbeats n

中文:
定义 sleepAtLeastHeartbeats
  签名: (n : 自然数)
  定义体: do
  -- TODO: adjust docstring
  IO.addHeartbeats n
-/
def sleepAtLeastHeartbeats (n : Nat) : IO Unit := do
  -- TODO: adjust docstring
  IO.addHeartbeats n

/-- do nothing for at least n heartbeats -/
elab "sleep_heartbeats " n:num : tactic => do
  match Syntax.isNatLit? n with
  | none => throwIllFormedSyntax
  /-
  We multiply by `1000` to convert the user-facing heartbeat count to the
  internal heartbeat counter used by `IO.getNumHeartbeats`.
  -/
  | some m => sleepAtLeastHeartbeats (m * 1000)

example : 1 = 1 := by
  sleep_heartbeats 1000
  rfl
