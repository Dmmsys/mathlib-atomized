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

/-- An exception in the `SimplexAlgorithmM` monad. -/
/-
**Mathlib.Tactic.Linarith.SimplexAlgorithm.SimplexAlgorithmException** 是 Mathlib
 中的一个归纳类型，位于命名空间 `Mathlib.Tactic.Linarith.SimplexAlgorithm`。
形式化陈述：Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An exception in the `SimplexAlgorithmM` monad.
-/
inductive SimplexAlgorithmException
  /-- The solution is infeasible. -/
| infeasible : SimplexAlgorithmException

/-- The monad for the Simplex Algorithm. -/
/-
**Mathlib.Tactic.Linarith.SimplexAlgorithm.SimplexAlgorithmM** 是 Mathlib 中的一个缩写定
义，位于命名空间 `Mathlib.Tactic.Linarith.SimplexAlgorithm`。
形式化陈述：SimplexAlgorithmM (matType : Nat -> Nat -> Type) [UsableInSimplexAlgorithm
 matType]
参数：matType : Nat -> Nat -> Type。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The monad for the Simplex Algorithm.
-/
abbrev SimplexAlgorithmM (matType : Nat → Nat → Type) [UsableInSimplexAlgorithm matType] :=
  ExceptT SimplexAlgorithmException <| StateT (Tableau matType) Lean.CoreM

variable {matType : Nat → Nat → Type} [UsableInSimplexAlgorithm matType]

/--
Given indexes `exitIdx` and `enterIdx` of exiting and entering variables in the `basic` and `free`
arrays, performs pivot operation, i.e. expresses one through the other and makes the free one basic
and vice versa.
-/
/-
**Mathlib.Tactic.Linarith.SimplexAlgorithm.doPivotOperation** 是 Mathlib 中的一个定义，位
于命名空间 `Mathlib.Tactic.Linarith.SimplexAlgorithm`。
形式化陈述：doPivotOperation (exitIdx enterIdx : Nat) : SimplexAlgorithmM matType Unit
参数：exitIdx enterIdx : Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.zero_lt_one`：0 < 1

--- 原说明 ---
Given indexes `exitIdx` and `enterIdx` of exiting and entering variables in the 
`basic` and `free`
arrays, performs pivot operation, i.e. expresses one through the other and makes
 the free one basic
and vice versa.
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
Check if the solution is found: the objective function is positive and all basic variables are
nonnegative.
-/
/-
**Mathlib.Tactic.Linarith.SimplexAlgorithm.checkSuccess** 是 Mathlib 中的一个定义，位于命名空
间 `Mathlib.Tactic.Linarith.SimplexAlgorithm`。
形式化陈述：checkSuccess : SimplexAlgorithmM matType Bool
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Check if the solution is found: the objective function is positive and all basic
 variables are
nonnegative.
-/
def checkSuccess : SimplexAlgorithmM matType Bool := do
  let lastIdx := (← get).free.size - 1
  return (← get).mat[(0, lastIdx)]! > 0 &&
    (← (← get).basic.size.allM (fun i _ => do return (← get).mat[(i, lastIdx)]! ≥ 0))

/--
Chooses an entering variable: among the variables with a positive coefficient in the objective
function, the one with the smallest index (in the initial indexing).
-/
/-
**Mathlib.Tactic.Linarith.SimplexAlgorithm.chooseEnteringVar** 是 Mathlib 中的一个定义，
位于命名空间 `Mathlib.Tactic.Linarith.SimplexAlgorithm`。
形式化陈述：chooseEnteringVar : SimplexAlgorithmM matType Nat
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.zero_lt_one`：0 < 1

--- 原说明 ---
Chooses an entering variable: among the variables with a positive coefficient in
 the objective
function, the one with the smallest index (in the initial indexing).
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
Chooses an exiting variable: the variable imposing the strictest limit on the increase of the
entering variable, breaking ties by choosing the variable with smallest index.
-/
/-
**Mathlib.Tactic.Linarith.SimplexAlgorithm.chooseExitingVar** 是 Mathlib 中的一个定义，位
于命名空间 `Mathlib.Tactic.Linarith.SimplexAlgorithm`。
形式化陈述：chooseExitingVar (enterIdx : Nat) : SimplexAlgorithmM matType Nat
参数：enterIdx : Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.zero_lt_one`：0 < 1

--- 原说明 ---
Chooses an exiting variable: the variable imposing the strictest limit on the in
crease of the
entering variable, breaking ties by choosing the variable with smallest index.
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
Chooses entering and exiting variables using
[Bland's rule](https://en.wikipedia.org/wiki/Bland%27s_rule) that guarantees that the Simplex
Algorithm terminates.
-/
/-
**Mathlib.Tactic.Linarith.SimplexAlgorithm.choosePivots** 是 Mathlib 中的一个定义，位于命名空
间 `Mathlib.Tactic.Linarith.SimplexAlgorithm`。
形式化陈述：choosePivots : SimplexAlgorithmM matType (Nat × Nat)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Chooses entering and exiting variables using
[Bland's rule](https://en.wikipedia.org/wiki/Bland%27s_rule) that guarantees tha
t the Simplex
Algorithm terminates.
-/
def choosePivots : SimplexAlgorithmM matType (Nat × Nat) := do
  let enterIdx ← chooseEnteringVar
  let exitIdx ← chooseExitingVar enterIdx
  return ⟨exitIdx, enterIdx⟩

/--
Runs the Simplex Algorithm inside the `SimplexAlgorithmM`. It always terminates, finding solution if
such exists.
-/
/-
**Mathlib.Tactic.Linarith.SimplexAlgorithm.runSimplexAlgorithm** 是 Mathlib 中的一个定
义，位于命名空间 `Mathlib.Tactic.Linarith.SimplexAlgorithm`。
形式化陈述：runSimplexAlgorithm : SimplexAlgorithmM matType Unit
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Runs the Simplex Algorithm inside the `SimplexAlgorithmM`. It always terminates,
 finding solution if
such exists.
-/
def runSimplexAlgorithm : SimplexAlgorithmM matType Unit := do
  while !(← checkSuccess) do
    Lean.Core.checkSystem decl_name%.toString
    let ⟨exitIdx, enterIdx⟩ ← choosePivots
    doPivotOperation exitIdx enterIdx

end Mathlib.Tactic.Linarith.SimplexAlgorithm

