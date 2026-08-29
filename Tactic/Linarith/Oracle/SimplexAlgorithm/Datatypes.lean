/-
Copyright (c) 2024 Vasily Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Nesterov
-/
module

public import Mathlib.Init

/-!
# Datatypes for the Simplex Algorithm implementation
-/

public meta section

namespace Mathlib.Tactic.Linarith.SimplexAlgorithm

/--
Definition of `UsableInSimplexAlgorithm` / `UsableInSimplexAlgorithm` 的定义

English:
class UsableInSimplexAlgorithm
  parameters: (α : Nat -> Nat -> Type)
  axioms and operations (7):
    - getElem({n m : Nat} (mat : α n m) (i j : Nat)) : Rat
    - setElem({n m : Nat} (mat : α n m) (i j : Nat) (v : Rat)) : α n m
    - getValues({n m : Nat} (mat : α n m)) : List (Nat × Nat × Rat)
    - ofValues({n m : Nat} (values : List (Nat × Nat × Rat))) : α n m
    - swapRows({n m : Nat} (mat : α n m) (i j : Nat)) : α n m
    - subtractRow({n m : Nat} (mat : α n m) (i j : Nat) (coef : Rat)) : α n m
    - divideRow({n m : Nat} (mat : α n m) (i : Nat) (coef : Rat)) : α n m

中文:
类 UsableInSimplexAlgorithm
  参数: (α : 自然数 -> 自然数 -> 类型)
  公理与运算 (7 个):
    - getElem({n m : 自然数} (mat : α n m) (i j : 自然数)) : 有理数
    - setElem({n m : 自然数} (mat : α n m) (i j : 自然数) (v : 有理数)) : α n m
    - getValues({n m : 自然数} (mat : α n m)) : 列表 (自然数 × 自然数 × 有理数)
    - ofValues({n m : 自然数} (values : 列表 (自然数 × 自然数 × 有理数))) : α n m
    - swapRows({n m : 自然数} (mat : α n m) (i j : 自然数)) : α n m
    - subtractRow({n m : 自然数} (mat : α n m) (i j : 自然数) (coef : 有理数)) : α n m
    - divideRow({n m : 自然数} (mat : α n m) (i : 自然数) (coef : 有理数)) : α n m
-/
class UsableInSimplexAlgorithm (α : Nat -> Nat -> Type) where
  /-- Returns `mat[i, j]`. -/
  getElem {n m : Nat} (mat : α n m) (i j : Nat) : Rat
  /-- Sets `mat[i, j]`. -/
  setElem {n m : Nat} (mat : α n m) (i j : Nat) (v : Rat) : α n m
  /-- Returns the list of elements of `mat` in the form `(i, j, mat[i, j])`. -/
  getValues {n m : Nat} (mat : α n m) : List (Nat × Nat × Rat)
  /-- Creates a matrix from a list of elements in the form `(i, j, mat[i, j])`. -/
  ofValues {n m : Nat} (values : List (Nat × Nat × Rat)) : α n m
  /-- Swaps two rows. -/
  swapRows {n m : Nat} (mat : α n m) (i j : Nat) : α n m
  /-- Subtracts `i`-th row multiplied by `coef` from `j`-th row. -/
  subtractRow {n m : Nat} (mat : α n m) (i j : Nat) (coef : Rat) : α n m
  /-- Divides the `i`-th row by `coef`. -/
  divideRow {n m : Nat} (mat : α n m) (i : Nat) (coef : Rat) : α n m

export UsableInSimplexAlgorithm (setElem getValues ofValues swapRows subtractRow divideRow)

instance (n m : Nat) (matType : Nat -> Nat -> Type) [UsableInSimplexAlgorithm matType] :
    GetElem (matType n m) (Nat × Nat) Rat fun _ p => p.1 < n ∧ p.2 < m where
  getElem mat p _ := UsableInSimplexAlgorithm.getElem mat p.1 p.2

/--
Definition of `DenseMatrix` / `DenseMatrix` 的定义

English:
structure DenseMatrix
  parameters: (n m : Nat)
  axioms and operations (1):
    - data : Array (Array Rat)

中文:
结构 DenseMatrix
  参数: (n m : 自然数)
  公理与运算 (1 个):
    - data : 数组 (数组 有理数)
-/
structure DenseMatrix (n m : Nat) where
  /-- The content of the matrix. -/
  data : Array (Array Rat)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: UsableInSimplexAlgorithm DenseMatrix
  body: mat.data[i]![j]!
  setElem mat i j v := ⟨mat.data.modify i fun row => row.set! j v⟩
  getValues mat :=
    mat.data.zipIdx.foldl (init := []) fun acc (row, i) =>
let rowVals := Array.toList row.zipIdx.filterMap fun (v, j) =>
        if v != 0 then
          some (i, j, v)
        else
          none
      rowVals ++ acc
  ofValues {n m : Nat} vals : DenseMatrix _ _ := Id.run do
let mut data : Array (Array Rat) := Array.replicate n Array.replicate m 0
    for ⟨i, j, v⟩ in vals do
      data := data.modify i fun row => row.set! j v
    return ⟨data⟩
  swapRows mat i j := ⟨mat.data.swapIfInBounds i j⟩
  subtractRow mat i j coef :=
    let newData : Array (Array Rat) := mat.data.modify j fun row =>
      Array.zipWith (fun x y => x - coef * y) row mat.data[i]!
    ⟨newData⟩
  divideRow mat i coef := ⟨mat.data.modify i (·.map (· / coef))⟩

中文:
实例 :
  签名: UsableInSimplexAlgorithm DenseMatrix
  定义体: mat.data[i]![j]!
  setElem mat i j v := ⟨mat.data.modify i fun row => row.set! j v⟩
  getValues mat :=
    mat.data.zipIdx.foldl (init := []) fun acc (row, i) =>
let rowVals := Array.toList row.zipIdx.filterMap fun (v, j) =>
        if v != 0 then
          some (i, j, v)
        else
          none
      rowVals ++ acc
  ofValues {n m : Nat} vals : DenseMatrix _ _ := Id.run do
let mut data : Array (Array Rat) := Array.replicate n Array.replicate m 0
    for ⟨i, j, v⟩ in vals do
      data := data.modify i fun row => row.set! j v
    return ⟨data⟩
  swapRows mat i j := ⟨mat.data.swapIfInBounds i j⟩
  subtractRow mat i j coef :=
    let newData : Array (Array Rat) := mat.data.modify j fun row =>
      Array.zipWith (fun x y => x - coef * y) row mat.data[i]!
    ⟨newData⟩
  divideRow mat i coef := ⟨mat.data.modify i (·.map (· / coef))⟩

Depends on / 依赖: mat.data
-/
instance : UsableInSimplexAlgorithm DenseMatrix where
  getElem mat i j := mat.data[i]![j]!
  setElem mat i j v := ⟨mat.data.modify i fun row => row.set! j v⟩
  getValues mat :=
    mat.data.zipIdx.foldl (init := []) fun acc (row, i) =>
let rowVals := Array.toList row.zipIdx.filterMap fun (v, j) =>
        if v != 0 then
          some (i, j, v)
        else
          none
      rowVals ++ acc
  ofValues {n m : Nat} vals : DenseMatrix _ _ := Id.run do
let mut data : Array (Array Rat) := Array.replicate n Array.replicate m 0
    for ⟨i, j, v⟩ in vals do
      data := data.modify i fun row => row.set! j v
    return ⟨data⟩
  swapRows mat i j := ⟨mat.data.swapIfInBounds i j⟩
  subtractRow mat i j coef :=
    let newData : Array (Array Rat) := mat.data.modify j fun row =>
      Array.zipWith (fun x y => x - coef * y) row mat.data[i]!
    ⟨newData⟩
  divideRow mat i coef := ⟨mat.data.modify i (·.map (· / coef))⟩

/--
Definition of `SparseMatrix` / `SparseMatrix` 的定义

English:
structure SparseMatrix
  parameters: (n m : Nat)
  axioms and operations (1):
    - data : Array Std.HashMap Nat Rat

中文:
结构 SparseMatrix
  参数: (n m : 自然数)
  公理与运算 (1 个):
    - data : 数组 Std.HashMap 自然数 有理数
-/
structure SparseMatrix (n m : Nat) where
  /-- The content of the matrix. -/
data : Array Std.HashMap Nat Rat

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: UsableInSimplexAlgorithm SparseMatrix
  body: mat.data[i]!.getD j 0
  setElem mat i j v :=
    if v == 0 then
      ⟨mat.data.modify i fun row => row.erase j⟩
    else
      ⟨mat.data.modify i fun row => row.insert j v⟩
  getValues mat :=
    mat.data.zipIdx.foldl (init := []) fun acc (row, i) =>
      let rowVals := row.toList.map fun (j, v) => (i, j, v)
      rowVals ++ acc
  ofValues {n _ : Nat} vals := Id.run do
    let mut data : Array (Std.HashMap Nat Rat) := Array.replicate n ∅
    for ⟨i, j, v⟩ in vals do
      if v != 0 then
        data := data.modify i fun row => row.insert j v
    return ⟨data⟩
  swapRows mat i j := ⟨mat.data.swapIfInBounds i j⟩
  subtractRow mat i j coef :=
    let newData := mat.data.modify j fun row =>
      mat.data[i]!.fold (fun cur k val =>
        let newVal := (cur.getD k 0) - coef * val
        if newVal != 0 then cur.insert k newVal else cur.erase k
      ) row
    ⟨newData⟩
  divideRow mat i coef :=
    let newData : Array (Std.HashMap Nat Rat) := mat.data.modify i fun row =>
      row.fold (fun cur k v => cur.insert k (v / coef)) row
    ⟨newData⟩

中文:
实例 :
  签名: UsableInSimplexAlgorithm SparseMatrix
  定义体: mat.data[i]!.getD j 0
  setElem mat i j v :=
    if v == 0 then
      ⟨mat.data.modify i fun row => row.erase j⟩
    else
      ⟨mat.data.modify i fun row => row.insert j v⟩
  getValues mat :=
    mat.data.zipIdx.foldl (init := []) fun acc (row, i) =>
      let rowVals := row.toList.map fun (j, v) => (i, j, v)
      rowVals ++ acc
  ofValues {n _ : Nat} vals := Id.run do
    let mut data : Array (Std.HashMap Nat Rat) := Array.replicate n ∅
    for ⟨i, j, v⟩ in vals do
      if v != 0 then
        data := data.modify i fun row => row.insert j v
    return ⟨data⟩
  swapRows mat i j := ⟨mat.data.swapIfInBounds i j⟩
  subtractRow mat i j coef :=
    let newData := mat.data.modify j fun row =>
      mat.data[i]!.fold (fun cur k val =>
        let newVal := (cur.getD k 0) - coef * val
        if newVal != 0 then cur.insert k newVal else cur.erase k
      ) row
    ⟨newData⟩
  divideRow mat i coef :=
    let newData : Array (Std.HashMap Nat Rat) := mat.data.modify i fun row =>
      row.fold (fun cur k v => cur.insert k (v / coef)) row
    ⟨newData⟩

Depends on / 依赖: mat.data
-/
instance : UsableInSimplexAlgorithm SparseMatrix where
  getElem mat i j := mat.data[i]!.getD j 0
  setElem mat i j v :=
    if v == 0 then
      ⟨mat.data.modify i fun row => row.erase j⟩
    else
      ⟨mat.data.modify i fun row => row.insert j v⟩
  getValues mat :=
    mat.data.zipIdx.foldl (init := []) fun acc (row, i) =>
      let rowVals := row.toList.map fun (j, v) => (i, j, v)
      rowVals ++ acc
  ofValues {n _ : Nat} vals := Id.run do
    let mut data : Array (Std.HashMap Nat Rat) := Array.replicate n ∅
    for ⟨i, j, v⟩ in vals do
      if v != 0 then
        data := data.modify i fun row => row.insert j v
    return ⟨data⟩
  swapRows mat i j := ⟨mat.data.swapIfInBounds i j⟩
  subtractRow mat i j coef :=
    let newData := mat.data.modify j fun row =>
      mat.data[i]!.fold (fun cur k val =>
        let newVal := (cur.getD k 0) - coef * val
        if newVal != 0 then cur.insert k newVal else cur.erase k
      ) row
    ⟨newData⟩
  divideRow mat i coef :=
    let newData : Array (Std.HashMap Nat Rat) := mat.data.modify i fun row =>
      row.fold (fun cur k v => cur.insert k (v / coef)) row
    ⟨newData⟩

/--
Definition of `Tableau` / `Tableau` 的定义

English:
structure Tableau
  parameters: (matType : Nat -> Nat -> Type) [UsableInSimplexAlgorithm matType]
  axioms and operations (3):
    - basic : Array Nat
    - free : Array Nat
    - mat : matType basic.size free.size

中文:
结构 Tableau
  参数: (matType : 自然数 -> 自然数 -> 类型) [UsableInSimplexAlgorithm matType]
  公理与运算 (3 个):
    - basic : 数组 自然数
    - free : 数组 自然数
    - mat : matType basic.size free.size
-/
structure Tableau (matType : Nat -> Nat -> Type) [UsableInSimplexAlgorithm matType] where
  /-- Array containing the basic variables' indexes -/
  basic : Array Nat
  /-- Array containing the free variables' indexes -/
  free : Array Nat
  /-- Matrix of coefficients the basic variables expressed through the free ones. -/
  mat : matType basic.size free.size

end Mathlib.Tactic.Linarith.SimplexAlgorithm
