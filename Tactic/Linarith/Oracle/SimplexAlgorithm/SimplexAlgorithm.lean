/-
Copyright (c) 2024 Vasily Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Nesterov
-/
module

public meta import Mathlib.Tactic.Linarith.Oracle.SimplexAlgorithm.Datatypes
public import Mathlib.Tactic.Linarith.Oracle.SimplexAlgorithm.Datatypes

/-!
# Simplex Algorithm

To obtain required vector in `Linarith.SimplexAlgorithm.findPositiveVector` we run the Simplex
Algorithm. We use Bland's rule for pivoting, which guarantees that the algorithm terminates.
-/

public meta section

namespace Mathlib.Tactic.Linarith.SimplexAlgorithm

/--
Inductive type `SimplexAlgorithmException` / 归纳类型 `SimplexAlgorithmException`

English:
inductive SimplexAlgorithmException
  constructors (1):
    - infeasible: SimplexAlgorithmException

中文:
归纳类型 SimplexAlgorithmException
  构造子 (1 个):
    - infeasible: SimplexAlgorithmException
-/
inductive SimplexAlgorithmException
  /-- The solution is infeasible. -/
| infeasible : SimplexAlgorithmException

/--
Definition of `SimplexAlgorithmM` / `SimplexAlgorithmM` 的定义

English:
abbreviation SimplexAlgorithmM
  signature: (matType : Nat -> Nat -> Type) [UsableInSimplexAlgorithm matType]
  body: ExceptT SimplexAlgorithmException StateT (Tableau matType) Lean.CoreM

中文:
缩写 SimplexAlgorithmM
  签名: (matType : 自然数 -> 自然数 -> 类型) [UsableInSimplexAlgorithm matType]
  定义体: ExceptT SimplexAlgorithmException StateT (Tableau matType) Lean.CoreM

Depends on / 依赖: ExceptT, Lean.CoreM, SimplexAlgorithmException, StateT, Tableau, matType
-/
abbrev SimplexAlgorithmM (matType : Nat -> Nat -> Type) [UsableInSimplexAlgorithm matType] :=
ExceptT SimplexAlgorithmException StateT (Tableau matType) Lean.CoreM

variable {matType : Nat -> Nat -> Type} [UsableInSimplexAlgorithm matType]

/--
Definition of `doPivotOperation` / `doPivotOperation` 的定义

English:
definition doPivotOperation
  signature: (exitIdx enterIdx : Nat)
  body: modify fun s : Tableau matType => Id.run do
    let mut mat := s.mat
    let intersectCoef := mat[(exitIdx, enterIdx)]!

    for i in [:s.basic.size] do
      if i == exitIdx then
        continue
      let coef := mat[(i, enterIdx)]! / intersectCoef
      if coef != 0 then
        mat := subtractRow mat exitIdx i coef
      mat := setElem mat i enterIdx coef
    mat := setElem mat exitIdx enterIdx (-1)
    mat := divideRow mat exitIdx (-intersectCoef)

    let newBasic := s.basic.set! exitIdx s.free[enterIdx]!
    let newFree := s.free.set! enterIdx s.basic[exitIdx]!

    have hb : newBasic.size = s.basic.size := by apply Array.size_setIfInBounds
    have hf : newFree.size = s.free.size := by apply Array.size_setIfInBounds

    return (⟨newBasic, newFree, hb ▸ hf ▸ mat⟩ : Tableau matType)

中文:
定义 doPivotOperation
  签名: (exitIdx enterIdx : 自然数)
  定义体: modify fun s : Tableau matType => Id.run do
    let mut mat := s.mat
    let intersectCoef := mat[(exitIdx, enterIdx)]!

    for i in [:s.basic.size] do
      if i == exitIdx then
        continue
      let coef := mat[(i, enterIdx)]! / intersectCoef
      if coef != 0 then
        mat := subtractRow mat exitIdx i coef
      mat := setElem mat i enterIdx coef
    mat := setElem mat exitIdx enterIdx (-1)
    mat := divideRow mat exitIdx (-intersectCoef)

    let newBasic := s.basic.set! exitIdx s.free[enterIdx]!
    let newFree := s.free.set! enterIdx s.basic[exitIdx]!

    have hb : newBasic.size = s.basic.size := by apply Array.size_setIfInBounds
    have hf : newFree.size = s.free.size := by apply Array.size_setIfInBounds

    return (⟨newBasic, newFree, hb ▸ hf ▸ mat⟩ : Tableau matType)

Depends on / 依赖: Id.run, Tableau, enterIdx, exitIdx, intersectCoef, matType, modify, s.mat
-/
def doPivotOperation (exitIdx enterIdx : Nat) : SimplexAlgorithmM matType Unit :=
  modify fun s : Tableau matType => Id.run do
    let mut mat := s.mat
    let intersectCoef := mat[(exitIdx, enterIdx)]!

    for i in [:s.basic.size] do
      if i == exitIdx then
        continue
      let coef := mat[(i, enterIdx)]! / intersectCoef
      if coef != 0 then
        mat := subtractRow mat exitIdx i coef
      mat := setElem mat i enterIdx coef
    mat := setElem mat exitIdx enterIdx (-1)
    mat := divideRow mat exitIdx (-intersectCoef)

    let newBasic := s.basic.set! exitIdx s.free[enterIdx]!
    let newFree := s.free.set! enterIdx s.basic[exitIdx]!

    have hb : newBasic.size = s.basic.size := by apply Array.size_setIfInBounds
    have hf : newFree.size = s.free.size := by apply Array.size_setIfInBounds

    return (⟨newBasic, newFree, hb ▸ hf ▸ mat⟩ : Tableau matType)

/--
Definition of `checkSuccess` / `checkSuccess` 的定义

English:
definition checkSuccess
  signature: : SimplexAlgorithmM matType Bool
  body: do
  let lastIdx := (← get).free.size - 1
  return (← get).mat[(0, lastIdx)]! > 0 &&
    (← (← get).basic.size.allM (fun i _ => do return (← get).mat[(i, lastIdx)]! >= 0))

中文:
定义 checkSuccess
  签名: : SimplexAlgorithmM matType 布尔值
  定义体: do
  let lastIdx := (← get).free.size - 1
  return (← get).mat[(0, lastIdx)]! > 0 &&
    (← (← get).basic.size.allM (fun i _ => do return (← get).mat[(i, lastIdx)]! >= 0))
-/
def checkSuccess : SimplexAlgorithmM matType Bool := do
  let lastIdx := (← get).free.size - 1
  return (← get).mat[(0, lastIdx)]! > 0 &&
    (← (← get).basic.size.allM (fun i _ => do return (← get).mat[(i, lastIdx)]! >= 0))

/--
Definition of `chooseEnteringVar` / `chooseEnteringVar` 的定义

English:
definition chooseEnteringVar
  signature: : SimplexAlgorithmM matType Nat
  body: do
  let mut enterIdxOpt : Option Nat := none -- index of entering variable in the `free` array
  let mut minIdx := 0
  for i in [:(← get).free.size - 1] do
    if (← get).mat[(0, i)]! > 0 &&
        (enterIdxOpt.isNone || (← get).free[i]! < minIdx) then
      enterIdxOpt := i
      minIdx := (← get).free[i]!

  /- If there is no such variable the solution does not exist for sure. -/
  match enterIdxOpt with
  | none => throwThe SimplexAlgorithmException SimplexAlgorithmException.infeasible
  | some enterIdx => return enterIdx

中文:
定义 chooseEnteringVar
  签名: : SimplexAlgorithmM matType 自然数
  定义体: do
  let mut enterIdxOpt : Option Nat := none -- index of entering variable in the `free` array
  let mut minIdx := 0
  for i in [:(← get).free.size - 1] do
    if (← get).mat[(0, i)]! > 0 &&
        (enterIdxOpt.isNone || (← get).free[i]! < minIdx) then
      enterIdxOpt := i
      minIdx := (← get).free[i]!

  /- If there is no such variable the solution does not exist for sure. -/
  match enterIdxOpt with
  | none => throwThe SimplexAlgorithmException SimplexAlgorithmException.infeasible
  | some enterIdx => return enterIdx
-/
def chooseEnteringVar : SimplexAlgorithmM matType Nat := do
  let mut enterIdxOpt : Option Nat := none -- index of entering variable in the `free` array
  let mut minIdx := 0
  for i in [:(← get).free.size - 1] do
    if (← get).mat[(0, i)]! > 0 &&
        (enterIdxOpt.isNone || (← get).free[i]! < minIdx) then
      enterIdxOpt := i
      minIdx := (← get).free[i]!

  /- If there is no such variable the solution does not exist for sure. -/
  match enterIdxOpt with
  | none => throwThe SimplexAlgorithmException SimplexAlgorithmException.infeasible
  | some enterIdx => return enterIdx

/--
Definition of `chooseExitingVar` / `chooseExitingVar` 的定义

English:
definition chooseExitingVar
  signature: (enterIdx : Nat)
  body: do
  let mut exitIdxOpt : Option Nat := none -- index of entering variable in the `basic` array
  let mut minCoef := 0
  let mut minIdx := 0
  for i in [1:(← get).basic.size] do
    if (← get).mat[(i, enterIdx)]! >= 0 then
      continue
    let lastIdx := (← get).free.size - 1
    let coef := -(← get).mat[(i, lastIdx)]! / (← get).mat[(i, enterIdx)]!
    if exitIdxOpt.isNone || coef < minCoef ||
        (coef == minCoef && (← get).basic[i]! < minIdx) then
      exitIdxOpt := i
      minCoef := coef
      minIdx := (← get).basic[i]!
  return exitIdxOpt.get! -- such variable always exists because our problem is bounded

中文:
定义 chooseExitingVar
  签名: (enterIdx : 自然数)
  定义体: do
  let mut exitIdxOpt : Option Nat := none -- index of entering variable in the `basic` array
  let mut minCoef := 0
  let mut minIdx := 0
  for i in [1:(← get).basic.size] do
    if (← get).mat[(i, enterIdx)]! >= 0 then
      continue
    let lastIdx := (← get).free.size - 1
    let coef := -(← get).mat[(i, lastIdx)]! / (← get).mat[(i, enterIdx)]!
    if exitIdxOpt.isNone || coef < minCoef ||
        (coef == minCoef && (← get).basic[i]! < minIdx) then
      exitIdxOpt := i
      minCoef := coef
      minIdx := (← get).basic[i]!
  return exitIdxOpt.get! -- such variable always exists because our problem is bounded
-/
def chooseExitingVar (enterIdx : Nat) : SimplexAlgorithmM matType Nat := do
  let mut exitIdxOpt : Option Nat := none -- index of entering variable in the `basic` array
  let mut minCoef := 0
  let mut minIdx := 0
  for i in [1:(← get).basic.size] do
    if (← get).mat[(i, enterIdx)]! >= 0 then
      continue
    let lastIdx := (← get).free.size - 1
    let coef := -(← get).mat[(i, lastIdx)]! / (← get).mat[(i, enterIdx)]!
    if exitIdxOpt.isNone || coef < minCoef ||
        (coef == minCoef && (← get).basic[i]! < minIdx) then
      exitIdxOpt := i
      minCoef := coef
      minIdx := (← get).basic[i]!
  return exitIdxOpt.get! -- such variable always exists because our problem is bounded

/--
Definition of `choosePivots` / `choosePivots` 的定义

English:
definition choosePivots
  signature: : SimplexAlgorithmM matType (Nat × Nat)
  body: do
  let enterIdx ← chooseEnteringVar
  let exitIdx ← chooseExitingVar enterIdx
  return ⟨exitIdx, enterIdx⟩

中文:
定义 choosePivots
  签名: : SimplexAlgorithmM matType (自然数 × 自然数)
  定义体: do
  let enterIdx ← chooseEnteringVar
  let exitIdx ← chooseExitingVar enterIdx
  return ⟨exitIdx, enterIdx⟩
-/
def choosePivots : SimplexAlgorithmM matType (Nat × Nat) := do
  let enterIdx ← chooseEnteringVar
  let exitIdx ← chooseExitingVar enterIdx
  return ⟨exitIdx, enterIdx⟩

/--
Definition of `runSimplexAlgorithm` / `runSimplexAlgorithm` 的定义

English:
definition runSimplexAlgorithm
  signature: : SimplexAlgorithmM matType Unit
  body: do
  while !(← checkSuccess) do
    Lean.Core.checkSystem decl_name%.toString
    let ⟨exitIdx, enterIdx⟩ ← choosePivots
    doPivotOperation exitIdx enterIdx

中文:
定义 runSimplexAlgorithm
  签名: : SimplexAlgorithmM matType 单元
  定义体: do
  while !(← checkSuccess) do
    Lean.Core.checkSystem decl_name%.toString
    let ⟨exitIdx, enterIdx⟩ ← choosePivots
    doPivotOperation exitIdx enterIdx
-/
def runSimplexAlgorithm : SimplexAlgorithmM matType Unit := do
  while !(← checkSuccess) do
    Lean.Core.checkSystem decl_name%.toString
    let ⟨exitIdx, enterIdx⟩ ← choosePivots
    doPivotOperation exitIdx enterIdx

end Mathlib.Tactic.Linarith.SimplexAlgorithm
