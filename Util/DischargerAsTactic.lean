/-
Copyright (c) 2023 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
module

public import Mathlib.Init
public import Batteries.Tactic.Exact
public import Lean.Meta.Tactic.Simp

/-!
## Dischargers for `simp` to tactics

This file defines a wrapper for `Simp.Discharger`s as regular tactics, that allows them to be
used via the tactic frontend of `simp` via `simp (discharger := wrapSimpDischarger my_discharger)`.
-/

public meta section

open Lean Meta Elab Tactic

/--
Definition of `wrapSimpDischarger` / `wrapSimpDischarger` 的定义

English:
definition wrapSimpDischarger
  signature: (dis : Simp.Discharge)
  body: do
  let eS : Lean.Meta.Simp.State := {}
  let eC : Lean.Meta.Simp.Context ← Simp.mkContext {}
  let eM : Lean.Meta.Simp.Methods := {}
let (some a, _) ← liftM StateRefT'.run (ReaderT.run (ReaderT.run (dis <| ← getMainTarget)
    eM.toMethodsRef) eC) eS | failure
  (← getMainGoal).assignIfDefEq a

中文:
定义 wrapSimpDischarger
  签名: (dis : Simp.Discharge)
  定义体: do
  let eS : Lean.Meta.Simp.State := {}
  let eC : Lean.Meta.Simp.Context ← Simp.mkContext {}
  let eM : Lean.Meta.Simp.Methods := {}
let (some a, _) ← liftM StateRefT'.run (ReaderT.run (ReaderT.run (dis <| ← getMainTarget)
    eM.toMethodsRef) eC) eS | failure
  (← getMainGoal).assignIfDefEq a
-/
def wrapSimpDischarger (dis : Simp.Discharge) : TacticM Unit := do
  let eS : Lean.Meta.Simp.State := {}
  let eC : Lean.Meta.Simp.Context ← Simp.mkContext {}
  let eM : Lean.Meta.Simp.Methods := {}
let (some a, _) ← liftM StateRefT'.run (ReaderT.run (ReaderT.run (dis <| ← getMainTarget)
    eM.toMethodsRef) eC) eS | failure
  (← getMainGoal).assignIfDefEq a
