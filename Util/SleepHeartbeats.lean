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

/-- A low level command to sleep for at least a given number of heartbeats by running in a loop
until the desired number of heartbeats is hit.
Warning: this function relies on interpreter / compiler
behaviour that is not guaranteed to function in the way that is relied upon here.
As such this function is not to be considered reliable, especially after future updates to Lean.
This should be used with caution and basically only for demo / testing purposes
and not in compiled code without further testing. -/
/-
**sleepAtLeastHeartbeats** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：sleepAtLeastHeartbeats (n : Nat) : IO Unit
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A low level command to sleep for at least a given number of heartbeats by runnin
g in a loop
until the desired number of heartbeats is hit.
Warning: this function relies on interpreter / compiler
behaviour that is not guaranteed to function in the way that is relied upon here
.
As such this function is not to be considered reliable, especially after future 
updates to Lean.
This should be used with caution and basically only for demo / testing purposes
and not in compiled code without further testing.
-/
def sleepAtLeastHeartbeats (n : Nat) : IO Unit := do
  -- TODO: adjust docstring
  IO.addHeartbeats n

/-- do nothing for at least n heartbeats -/
elab "sleep_heartbeats " n:num : tactic => do
  match Syntax.isNatLit? n with
  | none    => throwIllFormedSyntax
  /-
  We multiply by `1000` to convert the user-facing heartbeat count to the
  internal heartbeat counter used by `IO.getNumHeartbeats`.
  -/
  | some m => sleepAtLeastHeartbeats (m * 1000)

/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : 1 = 1 := by
  sleep_heartbeats 1000
  rfl
