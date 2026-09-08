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

/-- Preprocess the goal to pass it to `Linarith.SimplexAlgorithm.findPositiveVector`. -/
/-
**Mathlib.Tactic.Linarith.SimplexAlgorithm.preprocess** 是 Mathlib 中的一个定义，位于命名空间 
`Mathlib.Tactic.Linarith.SimplexAlgorithm`。
形式化陈述：preprocess (matType : Nat -> Nat -> Type) [UsableInSimplexAlgorithm matTyp
e] (hyps : List Comp) (maxVar : Nat) : matType (maxVar + 1) (hyps.length) × List
 Nat
参数：matType : Nat -> Nat -> Type；hyps : List Comp；maxVar : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Preprocess the goal to pass it to `Linarith.SimplexAlgorithm.findPositiveVector`
.
-/
def preprocess (matType : ℕ → ℕ → Type) [UsableInSimplexAlgorithm matType] (hyps : List Comp)
    (maxVar : ℕ) : matType (maxVar + 1) (hyps.length) × List Nat :=
  let values : List (ℕ × ℕ × ℚ) := hyps.foldlIdx (init := []) fun idx cur comp =>
    cur ++ comp.coeffs.map fun (var, c) => (var, idx, c)

  let strictIndexes := hyps.findIdxs (·.str == Ineq.lt)
  (ofValues values, strictIndexes)

/--
Extract the certificate from the `vec` found by `Linarith.SimplexAlgorithm.findPositiveVector`.
-/
/-
**Mathlib.Tactic.Linarith.SimplexAlgorithm.postprocess** 是 Mathlib 中的一个定义，位于命名空间
 `Mathlib.Tactic.Linarith.SimplexAlgorithm`。
形式化陈述：postprocess (vec : Array Rat) : Std.HashMap Nat Nat
参数：vec : Array Rat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extract the certificate from the `vec` found by `Linarith.SimplexAlgorithm.findP
ositiveVector`.
-/
def postprocess (vec : Array ℚ) : Std.HashMap ℕ ℕ :=
  let common_den : ℕ := vec.foldl (fun acc item => acc.lcm item.den) 1
  let vecNat : Array ℕ := vec.map (fun x : ℚ => (x * common_den).floor.toNat)
  (∅ : Std.HashMap Nat Nat).insertMany <| vecNat.zipIdx.filterMap
    fun ⟨item, idx⟩ => if item != 0 then some (idx, item) else none

end SimplexAlgorithm

open SimplexAlgorithm

/-- An oracle that uses the Simplex Algorithm. -/
/-
**Mathlib.Tactic.Linarith.CertificateOracle.simplexAlgorithmSparse** 是 Mathlib 中
的一个定义，位于命名空间 `Mathlib.Tactic.Linarith.CertificateOracle`。
形式化陈述：Mathlib.Tactic.Linarith.CertificateOracle
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An oracle that uses the Simplex Algorithm.
-/
def CertificateOracle.simplexAlgorithmSparse : CertificateOracle where
  produceCertificate hyps maxVar := do
    let (A, strictIndexes) := preprocess SparseMatrix hyps maxVar
    let vec ← findPositiveVector A strictIndexes
    return postprocess vec

/--
The same oracle as `CertificateOracle.simplexAlgorithmSparse`, but uses dense matrices. Works faster
on dense states.
-/
/-
**Mathlib.Tactic.Linarith.CertificateOracle.simplexAlgorithmDense** 是 Mathlib 中的
一个定义，位于命名空间 `Mathlib.Tactic.Linarith.CertificateOracle`。
形式化陈述：Mathlib.Tactic.Linarith.CertificateOracle
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The same oracle as `CertificateOracle.simplexAlgorithmSparse`, but uses dense ma
trices. Works faster
on dense states.
-/
def CertificateOracle.simplexAlgorithmDense : CertificateOracle where
  produceCertificate hyps maxVar := do
    let (A, strictIndexes) := preprocess DenseMatrix hyps maxVar
    let vec ← findPositiveVector A strictIndexes
    return postprocess vec

end Mathlib.Tactic.Linarith

