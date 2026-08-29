/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Init

/-!
# Additional functions using `CoreM` state.
-/

@[expose] public section

open Lean Core

/--
Definition of `CoreM.withImportModules` / `CoreM.withImportModules` 的定义

English:
definition CoreM.withImportModules
  signature: {α : Type} (modules : Array Name) (run : CoreM α)
  body: unsafe do
  if let some sp := searchPath then searchPathRef.set sp
  Lean.withImportModules (modules.map ({ module := · })) options (trustLevel := trustLevel)
    fun env =>
      let ctx := {fileName, options, fileMap := default}
      let state := {env}
Prod.fst < > (CoreM.toIO · ctx state) do
        run

中文:
定义 CoreM.withImportModules
  签名: {α : 类型} (modules : 数组 Name) (run : CoreM α)
  定义体: unsafe do
  if let some sp := searchPath then searchPathRef.set sp
  Lean.withImportModules (modules.map ({ module := · })) options (trustLevel := trustLevel)
    fun env =>
      let ctx := {fileName, options, fileMap := default}
      let state := {env}
Prod.fst < > (CoreM.toIO · ctx state) do
        run

Depends on / 依赖: Options, options
-/
def CoreM.withImportModules {α : Type} (modules : Array Name) (run : CoreM α)
    (searchPath : Option SearchPath := none) (options : Options := {})
    (trustLevel : UInt32 := 0) (fileName := "") :
    IO α := unsafe do
  if let some sp := searchPath then searchPathRef.set sp
  Lean.withImportModules (modules.map ({ module := · })) options (trustLevel := trustLevel)
    fun env =>
      let ctx := {fileName, options, fileMap := default}
      let state := {env}
Prod.fst < > (CoreM.toIO · ctx state) do
        run
