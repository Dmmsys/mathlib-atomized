/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public meta import Mathlib.Lean.Name
public meta import Mathlib.Lean.Expr.Basic
public meta import Lean.Elab.Command
public import Mathlib.Init

/-!
# Commands `#long_names` and `#long_instances`

For finding declarations with excessively long names.
-/

public meta section

open Lean Meta Elab

/--
Definition of `printNameHashMap` / `printNameHashMap` 的定义

English:
definition printNameHashMap
  signature: (h : Std.HashMap Name (Array Name))
  body: for (m, names) in h.toList do
    IO.println "----"
IO.println m.toString ++ ":"
    for n in names do
      IO.println n

中文:
定义 printNameHashMap
  签名: (h : Std.HashMap Name (数组 Name))
  定义体: for (m, names) in h.toList do
    IO.println "----"
IO.println m.toString ++ ":"
    for n in names do
      IO.println n

Depends on / 依赖: IO.println, h.toList, m.toString, println, toList, toString
-/
def printNameHashMap (h : Std.HashMap Name (Array Name)) : IO Unit :=
  for (m, names) in h.toList do
    IO.println "----"
IO.println m.toString ++ ":"
    for n in names do
      IO.println n

/--
Lists all declarations with a long name, gathered according to the module they are defined in.
Use as `#long_names` or `#long_names 100` to specify the length.
-/
elab "#long_names " N:(num)? : command =>
  Command.runTermElabM fun _ => do
.getD 50 let N := N.map TSyntax.getNat
    let namesByModule ← allNamesByModule (fun n => n.toString.length > N)
    let namesByModule := namesByModule.filter fun m _ => m.getRoot.toString = "Mathlib"
    printNameHashMap namesByModule

/--
Lists all instances with a long name beginning with `inst`,
gathered according to the module they are defined in.
This is useful for finding automatically named instances with absurd names.

Use as `#long_names` or `#long_names 100` to specify the length.
-/
elab "#long_instances " N:(num)?: command =>
  Command.runTermElabM fun _ => do
.getD 50 let N := N.map TSyntax.getNat
    let namesByModule ← allNamesByModule
      (fun n => n.lastComponentAsString.startsWith "inst" && n.lastComponentAsString.length > N)
    let namesByModule := namesByModule.filter fun m _ => m.getRoot.toString = "Mathlib"
    printNameHashMap namesByModule
