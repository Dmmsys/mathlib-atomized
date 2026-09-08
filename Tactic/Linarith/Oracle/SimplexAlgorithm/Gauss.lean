/-
Copyright (c) 2024 Vasily Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Nesterov
-/
module

public meta import Mathlib.Tactic.Linarith.Oracle.SimplexAlgorithm.Datatypes
public import Mathlib.Tactic.Linarith.Oracle.SimplexAlgorithm.Datatypes

/-!
# Gaussian Elimination algorithm

The first step of `Linarith.SimplexAlgorithm.findPositiveVector` is finding initial feasible
solution which is done by standard Gaussian Elimination algorithm implemented in this file.
-/

public meta section

namespace Mathlib.Tactic.Linarith.SimplexAlgorithm.Gauss

/-- The monad for the Gaussian Elimination algorithm. -/
/-
**Mathlib.Tactic.Linarith.SimplexAlgorithm.Gauss.GaussM** 是 Mathlib 中的一个缩写定义，位于命
名空间 `Mathlib.Tactic.Linarith.SimplexAlgorithm.Gauss`。
形式化陈述：GaussM (n m : Nat) (matType : Nat -> Nat -> Type)
参数：n m : Nat；matType : Nat -> Nat -> Type。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The monad for the Gaussian Elimination algorithm.
-/
abbrev GaussM (n m : Nat) (matType : Nat → Nat → Type) := StateT (matType n m) Lean.CoreM

variable {n m : Nat} {matType : Nat → Nat → Type} [UsableInSimplexAlgorithm matType]

/-- Finds the first row starting from the `rowStart` with nonzero element in the column `col`. -/
/-
**Mathlib.Tactic.Linarith.SimplexAlgorithm.Gauss.findNonzeroRow** 是 Mathlib 中的一个
定义，位于命名空间 `Mathlib.Tactic.Linarith.SimplexAlgorithm.Gauss`。
形式化陈述：findNonzeroRow (rowStart col : Nat) : GaussM n m matType Option Nat
参数：rowStart col : Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.zero_lt_one`：0 < 1

--- 原说明 ---
Finds the first row starting from the `rowStart` with nonzero element in the col
umn `col`.
-/
def findNonzeroRow (rowStart col : Nat) : GaussM n m matType <| Option Nat := do
  for i in [rowStart:n] do
    if (← get)[(i, col)]! != 0 then
      return i
  return none

/-- Implementation of `getTableau` in `GaussM` monad. -/
/-
**Mathlib.Tactic.Linarith.SimplexAlgorithm.Gauss.getTableauImp** 是 Mathlib 中的一个定
义，位于命名空间 `Mathlib.Tactic.Linarith.SimplexAlgorithm.Gauss`。
形式化陈述：getTableauImp : GaussM n m matType Tableau matType
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.zero_lt_one`：0 < 1

--- 原说明 ---
Implementation of `getTableau` in `GaussM` monad.
-/
def getTableauImp : GaussM n m matType <| Tableau matType := do
  let mut free : Array Nat := #[]
  let mut basic : Array Nat := #[]

  let mut row : Nat := 0
  let mut col : Nat := 0

  while row < n && col < m do
    Lean.Core.checkSystem decl_name%.toString
    match ← findNonzeroRow row col with
    | none =>
      free := free.push col
      col := col + 1
      continue
    | some rowToSwap =>
      modify fun mat => swapRows mat row rowToSwap

    modify fun mat => divideRow mat row mat[(row, col)]!

    for i in [:n] do
      if i == row then
        continue
      let coef := (← get)[(i, col)]!
      if coef != 0 then
        modify fun mat => subtractRow mat row i coef

    basic := basic.push col
    row := row + 1
    col := col + 1

  for i in [col:m] do
    free := free.push i

  let ansMatrix : matType basic.size free.size ← do
    let vals := getValues (← get) |>.filterMap fun (i, j, v) =>
      if j == basic[i]! then
        none
      else
        some (i, free.findIdx? (· == j) |>.get!, -v)
    pure <| ofValues vals

  return ⟨basic, free, ansMatrix⟩

/--
Given matrix `A`, solves the linear equation `A x = 0` and returns the solution as a tableau where
some variables are free and others (basic) variable are expressed as linear combinations of the free
ones.
-/
/-
**Mathlib.Tactic.Linarith.SimplexAlgorithm.Gauss.getTableau** 是 Mathlib 中的一个定义，位
于命名空间 `Mathlib.Tactic.Linarith.SimplexAlgorithm.Gauss`。
形式化陈述：getTableau (A : matType n m) : Lean.CoreM (Tableau matType)
参数：A : matType n m。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given matrix `A`, solves the linear equation `A x = 0` and returns the solution 
as a tableau where
some variables are free and others (basic) variable are expressed as linear comb
inations of the free
ones.
-/
def getTableau (A : matType n m) : Lean.CoreM (Tableau matType) := do
  return (← getTableauImp.run A).fst

end Mathlib.Tactic.Linarith.SimplexAlgorithm.Gauss

