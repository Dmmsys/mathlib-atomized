/-
Copyright (c) 2024 Vasily Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Nesterov
-/
module

public meta import Mathlib.Tactic.Linarith.Datatypes
public import Mathlib.Tactic.Linarith.Datatypes
public import Mathlib.Tactic.Linarith.Oracle.SimplexAlgorithm.PositiveVector

/-!
# The oracle based on Simplex Algorithm

This file contains hooks to enable the use of the Simplex Algorithm in `linarith`.
The algorithm's entry point is the function `Linarith.SimplexAlgorithm.findPositiveVector`.
See the file `PositiveVector.lean` for details of how the procedure works.
-/

public meta section

namespace Mathlib.Tactic.Linarith.SimplexAlgorithm

/--
Definition of `preprocess` / `preprocess` 的定义

English:
definition preprocess
  signature: (matType : Nat -> Nat -> Type) [UsableInSimplexAlgorithm matType] (hyps : List Comp)
  body: let values : List (Nat × Nat × Rat) := hyps.foldlIdx (init := []) fun idx cur comp =>
    cur ++ comp.coeffs.map fun (var, c) => (var, idx, c)

  let strictIndexes := hyps.findIdxs (·.str == Ineq.lt)
  (ofValues values, strictIndexes)

中文:
定义 preprocess
  签名: (matType : 自然数 -> 自然数 -> 类型) [UsableInSimplexAlgorithm matType] (hyps : 列表 复合)
  定义体: let values : List (Nat × Nat × Rat) := hyps.foldlIdx (init := []) fun idx cur comp =>
    cur ++ comp.coeffs.map fun (var, c) => (var, idx, c)

  let strictIndexes := hyps.findIdxs (·.str == Ineq.lt)
  (ofValues values, strictIndexes)

Depends on / 依赖: coeffs, comp.coeffs.map, foldlIdx, hyps.foldlIdx, values
-/
def preprocess (matType : Nat -> Nat -> Type) [UsableInSimplexAlgorithm matType] (hyps : List Comp)
    (maxVar : Nat) : matType (maxVar + 1) (hyps.length) × List Nat :=
  let values : List (Nat × Nat × Rat) := hyps.foldlIdx (init := []) fun idx cur comp =>
    cur ++ comp.coeffs.map fun (var, c) => (var, idx, c)

  let strictIndexes := hyps.findIdxs (·.str == Ineq.lt)
  (ofValues values, strictIndexes)

/--
Definition of `postprocess` / `postprocess` 的定义

English:
definition postprocess
  signature: (vec : Array Rat)
  body: let common_den : Nat := vec.foldl (fun acc item => acc.lcm item.den) 1
  let vecNat : Array Nat := vec.map (fun x : Rat => (x * common_den).floor.toNat)
(∅ : Std.HashMap Nat Nat).insertMany vecNat.zipIdx.filterMap
    fun ⟨item, idx⟩ => if item != 0 then some (idx, item) else none

中文:
定义 postprocess
  签名: (vec : 数组 有理数)
  定义体: let common_den : Nat := vec.foldl (fun acc item => acc.lcm item.den) 1
  let vecNat : Array Nat := vec.map (fun x : Rat => (x * common_den).floor.toNat)
(∅ : Std.HashMap Nat Nat).insertMany vecNat.zipIdx.filterMap
    fun ⟨item, idx⟩ => if item != 0 then some (idx, item) else none

Depends on / 依赖: HashMap, Std.HashMap, acc.lcm, common_den, filterMap, floor.toNat, insertMany, item.den, vec.foldl, vec.map, vecNat, vecNat.zipIdx.filterMap, zipIdx
-/
def postprocess (vec : Array Rat) : Std.HashMap Nat Nat :=
  let common_den : Nat := vec.foldl (fun acc item => acc.lcm item.den) 1
  let vecNat : Array Nat := vec.map (fun x : Rat => (x * common_den).floor.toNat)
(∅ : Std.HashMap Nat Nat).insertMany vecNat.zipIdx.filterMap
    fun ⟨item, idx⟩ => if item != 0 then some (idx, item) else none

end SimplexAlgorithm

open SimplexAlgorithm

/--
Definition of `CertificateOracle.simplexAlgorithmSparse` / `CertificateOracle.simplexAlgorithmSparse` 的定义

English:
definition CertificateOracle.simplexAlgorithmSparse
  signature: : CertificateOracle where
  body: do
    let (A, strictIndexes) := preprocess SparseMatrix hyps maxVar
    let vec ← findPositiveVector A strictIndexes
    return postprocess vec

中文:
定义 CertificateOracle.simplexAlgorithmSparse
  签名: : CertificateOracle where
  定义体: do
    let (A, strictIndexes) := preprocess SparseMatrix hyps maxVar
    let vec ← findPositiveVector A strictIndexes
    return postprocess vec
-/
def CertificateOracle.simplexAlgorithmSparse : CertificateOracle where
  produceCertificate hyps maxVar := do
    let (A, strictIndexes) := preprocess SparseMatrix hyps maxVar
    let vec ← findPositiveVector A strictIndexes
    return postprocess vec

/--
Definition of `CertificateOracle.simplexAlgorithmDense` / `CertificateOracle.simplexAlgorithmDense` 的定义

English:
definition CertificateOracle.simplexAlgorithmDense
  signature: : CertificateOracle where
  body: do
    let (A, strictIndexes) := preprocess DenseMatrix hyps maxVar
    let vec ← findPositiveVector A strictIndexes
    return postprocess vec

中文:
定义 CertificateOracle.simplexAlgorithmDense
  签名: : CertificateOracle where
  定义体: do
    let (A, strictIndexes) := preprocess DenseMatrix hyps maxVar
    let vec ← findPositiveVector A strictIndexes
    return postprocess vec
-/
def CertificateOracle.simplexAlgorithmDense : CertificateOracle where
  produceCertificate hyps maxVar := do
    let (A, strictIndexes) := preprocess DenseMatrix hyps maxVar
    let vec ← findPositiveVector A strictIndexes
    return postprocess vec

end Mathlib.Tactic.Linarith
