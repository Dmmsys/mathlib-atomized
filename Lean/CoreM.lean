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
Run a `CoreM α` in a fresh `Environment` with specified `modules : List Name` imported.
-/
/-
**CoreM.withImportModules** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：CoreM.withImportModules {α : Type} (modules : Array Name) (run : CoreM α) 
(searchPath : Option SearchPath
参数：modules : Array Name；run : CoreM α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Run a `CoreM α` in a fresh `Environment` with specified `modules : List Name` im
ported.
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
      Prod.fst <$> (CoreM.toIO · ctx state) do
        run
