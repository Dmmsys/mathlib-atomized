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

/--
Definition of `GaussM` / `GaussM` 的定义

English:
abbreviation GaussM
  signature: (n m : Nat) (matType : Nat -> Nat -> Type)
  body: StateT (matType n m) Lean.CoreM

中文:
缩写 GaussM
  签名: (n m : 自然数) (matType : 自然数 -> 自然数 -> Type)
  定义体: StateT (matType n m) Lean.CoreM

Depends on / 依赖: Lean.CoreM, StateT, matType
-/
abbrev GaussM (n m : Nat) (matType : Nat -> Nat -> Type) := StateT (matType n m) Lean.CoreM

variable {n m : Nat} {matType : Nat -> Nat -> Type} [UsableInSimplexAlgorithm matType]

/--
Definition of `findNonzeroRow` / `findNonzeroRow` 的定义

English:
definition findNonzeroRow
  signature: (rowStart col : Nat)
  body: do
  for i in [rowStart:n] do
    if (← get)[(i, col)]! != 0 then
      return i
  return none

中文:
定义 findNonzeroRow
  签名: (rowStart col : 自然数)
  定义体: do
  for i in [rowStart:n] do
    if (← get)[(i, col)]! != 0 then
      return i
  return none
-/
def findNonzeroRow (rowStart col : Nat) : GaussM n m matType Option Nat := do
  for i in [rowStart:n] do
    if (← get)[(i, col)]! != 0 then
      return i
  return none

/--
Definition of `getTableauImp` / `getTableauImp` 的定义

English:
definition getTableauImp
  signature: : GaussM n m matType Tableau matType
  body: do
  let mut free : Array Nat := #[]
  let mut basic : Array Nat := #[]

  let mut row : Nat := 0
  let mut col : Nat := 0

  while row < n && col < m do
    Lean.Core.checkSystem decl_name%.toString
    match ← findNonzeroRow row col with
    | none =>
      free := free.push col
      col := col +

中文:
定义 getTableauImp
  签名: : GaussM n m matType Tableau matType
  定义体: do
  let mut free : Array Nat := #[]
  let mut basic : Array Nat := #[]

  let mut row : Nat := 0
  let mut col : Nat := 0

  while row < n && col < m do
    Lean.Core.checkSystem decl_name%.toString
    match ← findNonzeroRow row col with
    | none =>
      free := free.push col
      col := col +
-/
def getTableauImp : GaussM n m matType Tableau matType := do
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
.filterMap fun (i, j, v) => let vals := getValues (← get)
      if j == basic[i]! then
        none
      else
        some (i, free.findIdx? (· == j) |>.get!, -v)
pure ofValues vals

  return ⟨basic, free, ansMatrix⟩

/--
Definition of `getTableau` / `getTableau` 的定义

English:
definition getTableau
  signature: (A : matType n m)
  body: do
  return (← getTableauImp.run A).fst

中文:
定义 getTableau
  签名: (A : matType n m)
  定义体: do
  return (← getTableauImp.run A).fst
-/
def getTableau (A : matType n m) : Lean.CoreM (Tableau matType) := do
  return (← getTableauImp.run A).fst

end Mathlib.Tactic.Linarith.SimplexAlgorithm.Gauss
