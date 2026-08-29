/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark, Kyle Miller, Lu-Ming Zhang
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.Hadamard

import Mathlib.Algebra.GroupWithZero.Idempotent
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Adjacency Matrices

This module defines the adjacency matrix of a graph, and provides theorems connecting graph
properties to computational properties of the matrix.

## Main definitions

* `Matrix.IsAdjMatrix`: `A : Matrix V V α` is qualified as an "adjacency matrix" if
  (1) every entry of `A` is `0` or `1`,
  (2) `A` is symmetric,
  (3) every diagonal entry of `A` is `0`.

* `Matrix.IsAdjMatrix.toGraph`: for `A : Matrix V V α` and `h : A.IsAdjMatrix`,
  `h.toGraph` is the simple graph induced by `A`.

* `Matrix.compl`: for `A : Matrix V V α`, `A.compl` is supposed to be
  the adjacency matrix of the complement graph of the graph induced by `A`.

* `SimpleGraph.adjMatrix`: the adjacency matrix of a `SimpleGraph`.

* `SimpleGraph.adjMatrix_pow_apply_eq_card_walk`: each entry of the `n`th power of
  a graph's adjacency matrix counts the number of length-`n` walks between the corresponding
  pair of vertices.

-/

@[expose] public section


open Matrix

open Finset SimpleGraph

variable {α V W : Type*}

namespace Matrix

/--
Definition of `IsAdjMatrix` / `IsAdjMatrix` 的定义

English:
structure IsAdjMatrix
  parameters: [Zero α] [One α] (A : Matrix V V α)
  axioms and operations (3):
    - zero_or_one : forall i j, A i j = 0 ∨ A i j = 1  [default: by aesop]
    - symm : A.IsSymm  [default: by aesop]
    - apply_diag : forall i, A i i = 0  [default: by aesop]

中文:
结构 IsAdjMatrix
  参数: [Zero α] [One α] (A : Matrix V V α)
  公理与运算 (3 个):
    - zero_or_one : 对任意 i j, A i j = 0 ∨ A i j = 1  [默认: by aesop]
    - symm : A.IsSymm  [默认: by aesop]
    - apply_diag : 对任意 i, A i i = 0  [默认: by aesop]

Depends on / 依赖: A.IsSymm, IsSymm, apply_diag
-/
structure IsAdjMatrix [Zero α] [One α] (A : Matrix V V α) : Prop where
  zero_or_one : forall i j, A i j = 0 ∨ A i j = 1 := by aesop
  symm : A.IsSymm := by aesop
  apply_diag : forall i, A i i = 0 := by aesop

namespace IsAdjMatrix

variable {A : Matrix V V α}

/--
theorem `zero` / 定理 `zero`

English:
theorem zero
  given: [Zero α] [One α]
  statement: (0 : Matrix V V α).IsAdjMatrix where

中文:
定理 zero
  条件: [Zero α] [One α]
  结论: (0 : Matrix V V α).IsAdjMatrix where
-/
@[simp] protected theorem zero [Zero α] [One α] : (0 : Matrix V V α).IsAdjMatrix where

@[simp]
/--
theorem `apply_diag_ne` / 定理 `apply_diag_ne`

English:
theorem apply_diag_ne
  given: [MulZeroOneClass α] [Nontrivial α] (h : IsAdjMatrix A) (i : V)
  proof: by simp [h.apply_diag i]

@[simp]

中文:
定理 apply_diag_ne
  条件: [MulZeroOneClass α] [Nontrivial α] (h : IsAdjMatrix A) (i : V)
  证明: by simp [h.apply_diag i]

@[simp]

Depends on / 依赖: apply_diag, h.apply_diag
-/
theorem apply_diag_ne [MulZeroOneClass α] [Nontrivial α] (h : IsAdjMatrix A) (i : V) :
    ¬A i i = 1 := by simp [h.apply_diag i]

@[simp]
/--
theorem `apply_ne_one_iff` / 定理 `apply_ne_one_iff`

English:
theorem apply_ne_one_iff
  given: [MulZeroOneClass α] [Nontrivial α] (h : IsAdjMatrix A) (i j : V)
  proof: by obtain h | h := h.zero_or_one i j <;> simp [h]

@[simp]

中文:
定理 apply_ne_one_iff
  条件: [MulZeroOneClass α] [Nontrivial α] (h : IsAdjMatrix A) (i j : V)
  证明: by obtain h | h := h.zero_or_one i j <;> simp [h]

@[simp]

Depends on / 依赖: h.zero_or_one, zero_or_one
-/
theorem apply_ne_one_iff [MulZeroOneClass α] [Nontrivial α] (h : IsAdjMatrix A) (i j : V) :
    ¬A i j = 1 ↔ A i j = 0 := by obtain h | h := h.zero_or_one i j <;> simp [h]

@[simp]
/--
theorem `apply_ne_zero_iff` / 定理 `apply_ne_zero_iff`

English:
theorem apply_ne_zero_iff
  given: [MulZeroOneClass α] [Nontrivial α] (h : IsAdjMatrix A) (i j : V)
  proof: by rw [← apply_ne_one_iff h, Classical.not_not]

@[simp]

中文:
定理 apply_ne_zero_iff
  条件: [MulZeroOneClass α] [Nontrivial α] (h : IsAdjMatrix A) (i j : V)
  证明: by rw [← apply_ne_one_iff h, Classical.not_not]

@[simp]

Depends on / 依赖: Classical, Classical.not_not, apply_ne_one_iff, not_not
-/
theorem apply_ne_zero_iff [MulZeroOneClass α] [Nontrivial α] (h : IsAdjMatrix A) (i j : V) :
    ¬A i j = 0 ↔ A i j = 1 := by rw [← apply_ne_one_iff h, Classical.not_not]

@[simp]
/--
theorem `diag_eq_zero` / 定理 `diag_eq_zero`

English:
theorem diag_eq_zero
  given: [Zero α] [One α] (h : IsAdjMatrix A)
  statement: A.diag = 0
  proof: by
  ext
  simp [h.apply_diag]

中文:
定理 diag_eq_zero
  条件: [Zero α] [One α] (h : IsAdjMatrix A)
  结论: A.diag = 0
  证明: by
  ext
  simp [h.apply_diag]

Depends on / 依赖: apply_diag, h.apply_diag
-/
theorem diag_eq_zero [Zero α] [One α] (h : IsAdjMatrix A) : A.diag = 0 := by
  ext
  simp [h.apply_diag]

/--
theorem `submatrix` / 定理 `submatrix`

English:
theorem submatrix
  given: [Zero α] [One α] (h : IsAdjMatrix A) (f : W -> V)
  proof: by simp [h.zero_or_one]
  symm := h.symm.submatrix f
  apply_diag i := by simp [h.apply_diag]

中文:
定理 submatrix
  条件: [Zero α] [One α] (h : IsAdjMatrix A) (f : W -> V)
  证明: by simp [h.zero_or_one]
  symm := h.symm.submatrix f
  apply_diag i := by simp [h.apply_diag]
-/
protected theorem submatrix [Zero α] [One α] (h : IsAdjMatrix A) (f : W -> V) :
.IsAdjMatrix where A.submatrix f f
  zero_or_one i j := by simp [h.zero_or_one]
  symm := h.symm.submatrix f
  apply_diag i := by simp [h.apply_diag]

/--
theorem `_root_.Matrix.isAdjMatrix_submatrix_iff` / 定理 `_root_.Matrix.isAdjMatrix_submatrix_iff`

English:
theorem _root_.Matrix.isAdjMatrix_submatrix_iff
  given: [Zero α] [One α] {f : W -> V} (hf : f.Surjective)
  proof: by
  refine ⟨fun h => ?_, (·.submatrix f)⟩
  rw [← A.submatrix_id_id]; rw [← f.comp_surjInv hf]
  apply h.submatrix

.IsAdjMatrix := theorem reindex [Zero α] [One α] (h : IsAdjMatrix A) (f : V ≃ W) : A.reindex f f
  h.submatrix f.symm

中文:
定理 _root_.Matrix.isAdjMatrix_submatrix_iff
  条件: [Zero α] [One α] {f : W -> V} (hf : f.Surjective)
  证明: by
  refine ⟨fun h => ?_, (·.submatrix f)⟩
  rw [← A.submatrix_id_id]; rw [← f.comp_surjInv hf]
  apply h.submatrix

.IsAdjMatrix := theorem reindex [Zero α] [One α] (h : IsAdjMatrix A) (f : V ≃ W) : A.reindex f f
  h.submatrix f.symm

Depends on / 依赖: A.submatrix_id_id, comp_surjInv, f.comp_surjInv, h.submatrix, submatrix, submatrix_id_id
-/
theorem _root_.Matrix.isAdjMatrix_submatrix_iff [Zero α] [One α] {f : W -> V} (hf : f.Surjective) :
    (A.submatrix f f).IsAdjMatrix ↔ A.IsAdjMatrix := by
  refine ⟨fun h => ?_, (·.submatrix f)⟩
  rw [← A.submatrix_id_id]; rw [← f.comp_surjInv hf]
  apply h.submatrix

.IsAdjMatrix := theorem reindex [Zero α] [One α] (h : IsAdjMatrix A) (f : V ≃ W) : A.reindex f f
  h.submatrix f.symm

/--
theorem `_root_.Matrix.isAdjMatrix_reindex_iff` / 定理 `_root_.Matrix.isAdjMatrix_reindex_iff`

English:
theorem _root_.Matrix.isAdjMatrix_reindex_iff
  given: [Zero α] [One α] {f : V ≃ W}
  proof: isAdjMatrix_submatrix_iff f.symm.surjective

中文:
定理 _root_.Matrix.isAdjMatrix_reindex_iff
  条件: [Zero α] [One α] {f : V ≃ W}
  证明: isAdjMatrix_submatrix_iff f.symm.surjective

Depends on / 依赖: f.symm.surjective, isAdjMatrix_submatrix_iff, surjective
-/
theorem _root_.Matrix.isAdjMatrix_reindex_iff [Zero α] [One α] {f : V ≃ W} :
    (A.reindex f f).IsAdjMatrix ↔ A.IsAdjMatrix :=
  isAdjMatrix_submatrix_iff f.symm.surjective

/-- For `A : Matrix V V α` and `h : IsAdjMatrix A`,
`h.toGraph` is the simple graph whose adjacency matrix is `A`. -/
@[simps]
/--
Definition of `toGraph` / `toGraph` 的定义

English:
definition toGraph
  signature: [MulZeroOneClass α] [Nontrivial α] (h : IsAdjMatrix A)
  body: A i j = 1
  symm.symm i j hij := by rwa [h.symm.apply i j]

中文:
定义 toGraph
  签名: [MulZeroOneClass α] [Nontrivial α] (h : IsAdjMatrix A)
  定义体: A i j = 1
  symm.symm i j hij := by rwa [h.symm.apply i j]
-/
def toGraph [MulZeroOneClass α] [Nontrivial α] (h : IsAdjMatrix A) : SimpleGraph V where
  Adj i j := A i j = 1
  symm.symm i j hij := by rwa [h.symm.apply i j]

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MulZeroOneClass
  signature: α] [Nontrivial α] [DecidableEq α] (h
  body: by
  simp only [toGraph]
  infer_instance

中文:
实例 [MulZeroOneClass
  签名: α] [Nontrivial α] [DecidableEq α] (h
  定义体: by
  simp only [toGraph]
  infer_instance

Depends on / 依赖: infer_instance, toGraph
-/
instance [MulZeroOneClass α] [Nontrivial α] [DecidableEq α] (h : IsAdjMatrix A) :
    DecidableRel h.toGraph.Adj := by
  simp only [toGraph]
  infer_instance

variable (A) in
/-- A homomorphism of the graph of a submatrix of an adjacency matrix to the graph of the
adjacency matrix itself -/
@[simps]
/--
Definition of `toGraphSubmatrixHom` / `toGraphSubmatrixHom` 的定义

English:
definition toGraphSubmatrixHom
  signature: [MulZeroOneClass α] [Nontrivial α] (h : IsAdjMatrix A) (f : W -> V)
  body: f
  map_rel' := by simp

中文:
定义 toGraphSubmatrixHom
  签名: [MulZeroOneClass α] [Nontrivial α] (h : IsAdjMatrix A) (f : W -> V)
  定义体: f
  map_rel' := by simp
-/
def toGraphSubmatrixHom [MulZeroOneClass α] [Nontrivial α] (h : IsAdjMatrix A) (f : W -> V) :
    (h.submatrix f).toGraph ->g h.toGraph where
  toFun := f
  map_rel' := by simp

variable (A) in
/--
Definition of `toGraphSubmatrixEmbedding` / `toGraphSubmatrixEmbedding` 的定义

English:
definition toGraphSubmatrixEmbedding
  signature: [MulZeroOneClass α] [Nontrivial α] (h : IsAdjMatrix A) (f : W ↪ V)
  body: f
  map_rel_iff' := by simp

中文:
定义 toGraphSubmatrixEmbedding
  签名: [MulZeroOneClass α] [Nontrivial α] (h : IsAdjMatrix A) (f : W ↪ V)
  定义体: f
  map_rel_iff' := by simp
-/
def toGraphSubmatrixEmbedding [MulZeroOneClass α] [Nontrivial α] (h : IsAdjMatrix A) (f : W ↪ V) :
    (h.submatrix f).toGraph ↪g h.toGraph where
  __ := f
  map_rel_iff' := by simp

variable (A) in
@[simp]
/--
theorem `toGraphSubmatrixEmbedding_apply` / 定理 `toGraphSubmatrixEmbedding_apply`

English:
theorem toGraphSubmatrixEmbedding_apply
  statement: [MulZeroOneClass α] [Nontrivial α] (h : A.IsAdjMatrix)
  proof: rfl

中文:
定理 toGraphSubmatrixEmbedding_apply
  结论: [MulZeroOneClass α] [Nontrivial α] (h : A.IsAdjMatrix)
  证明: rfl
-/
theorem toGraphSubmatrixEmbedding_apply [MulZeroOneClass α] [Nontrivial α] (h : A.IsAdjMatrix)
    (f : W -> V) (v : W) : (toGraphSubmatrixHom A h f) v = f v :=
  rfl

variable (A) in
/-- An isomorphism of the graph of a reindexing of an adjacency matrix to the graph of the
adjacency matrix itself -/
@[simps!]
/--
Definition of `toGraphReindexIso` / `toGraphReindexIso` 的定义

English:
definition toGraphReindexIso
  signature: [MulZeroOneClass α] [Nontrivial α] (h : IsAdjMatrix A) (f : V ≃ W)
  body: f.symm
  map_rel_iff' := by simp

中文:
定义 toGraphReindexIso
  签名: [MulZeroOneClass α] [Nontrivial α] (h : IsAdjMatrix A) (f : V ≃ W)
  定义体: f.symm
  map_rel_iff' := by simp

Depends on / 依赖: f.symm
-/
def toGraphReindexIso [MulZeroOneClass α] [Nontrivial α] (h : IsAdjMatrix A) (f : V ≃ W) :
    (h.reindex f).toGraph ≃g h.toGraph where
  __ := f.symm
  map_rel_iff' := by simp

/--
theorem `hadamard_self` / 定理 `hadamard_self`

English:
theorem hadamard_self
  given: [MulZeroOneClass α] {A : Matrix V V α} (hA : A.IsAdjMatrix)
  proof: by ext i j; have := hA.zero_or_one i j; aesop

中文:
定理 hadamard_self
  条件: [MulZeroOneClass α] {A : Matrix V V α} (hA : A.IsAdjMatrix)
  证明: by ext i j; have := hA.zero_or_one i j; aesop
-/
@[simp] theorem hadamard_self [MulZeroOneClass α] {A : Matrix V V α} (hA : A.IsAdjMatrix) :
    A ⊙ A = A := by ext i j; have := hA.zero_or_one i j; aesop

end IsAdjMatrix

/--
theorem `isAdjMatrix_iff_hadamard` / 定理 `isAdjMatrix_iff_hadamard`

English:
theorem isAdjMatrix_iff_hadamard
  statement: [DecidableEq V] [MonoidWithZero α]
  proof: by
  simp only [hadamard_self_eq_self_iff, IsIdempotentElem.iff_eq_zero_or_one,
    one_hadamard_eq_zero_iff, funext_iff, diag, Pi.zero_apply]
  grind [IsAdjMatrix]

中文:
定理 isAdjMatrix_iff_hadamard
  结论: [DecidableEq V] [MonoidWithZero α]
  证明: by
  simp only [hadamard_self_eq_self_iff, IsIdempotentElem.iff_eq_zero_or_one,
    one_hadamard_eq_zero_iff, funext_iff, diag, Pi.zero_apply]
  grind [IsAdjMatrix]

Depends on / 依赖: IsAdjMatrix, IsIdempotentElem, IsIdempotentElem.iff_eq_zero_or_one, Pi.zero_apply, funext_iff, hadamard_self_eq_self_iff, iff_eq_zero_or_one, one_hadamard_eq_zero_iff, zero_apply
-/
theorem isAdjMatrix_iff_hadamard [DecidableEq V] [MonoidWithZero α]
    [IsLeftCancelMulZero α] {A : Matrix V V α} :
    A.IsAdjMatrix ↔ (A ⊙ A = A ∧ A.IsSymm ∧ 1 ⊙ A = 0) := by
  simp only [hadamard_self_eq_self_iff, IsIdempotentElem.iff_eq_zero_or_one,
    one_hadamard_eq_zero_iff, funext_iff, diag, Pi.zero_apply]
  grind [IsAdjMatrix]

/--
Definition of `compl` / `compl` 的定义

English:
definition compl
  signature: [Zero α] [One α] [DecidableEq α] [DecidableEq V] (A : Matrix V V α)
  body: of fun i j => if i = j then 0 else if A i j = 0 then 1 else 0

中文:
定义 compl
  签名: [Zero α] [One α] [DecidableEq α] [DecidableEq V] (A : Matrix V V α)
  定义体: of fun i j => if i = j then 0 else if A i j = 0 then 1 else 0
-/
def compl [Zero α] [One α] [DecidableEq α] [DecidableEq V] (A : Matrix V V α) : Matrix V V α :=
  of fun i j => if i = j then 0 else if A i j = 0 then 1 else 0

section Compl

variable [DecidableEq α] [DecidableEq V] (A : Matrix V V α)

@[simp]
/--
theorem `compl_apply_diag` / 定理 `compl_apply_diag`

English:
theorem compl_apply_diag
  given: [Zero α] [One α] (i : V)
  statement: A.compl i i = 0
  proof: by simp [compl]

@[simp]

中文:
定理 compl_apply_diag
  条件: [Zero α] [One α] (i : V)
  结论: A.compl i i = 0
  证明: by simp [compl]

@[simp]
-/
theorem compl_apply_diag [Zero α] [One α] (i : V) : A.compl i i = 0 := by simp [compl]

@[simp]
/--
theorem `compl_apply` / 定理 `compl_apply`

English:
theorem compl_apply
  given: [Zero α] [One α] (i j : V)
  statement: A.compl i j = 0 ∨ A.compl i j = 1
  proof: by
  #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
  (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal
  without the `simp`. This is probably a problem at Mathlib's end rather than `grind`'s,
  as we are relying on seeing through

中文:
定理 compl_apply
  条件: [Zero α] [One α] (i j : V)
  结论: A.compl i j = 0 ∨ A.compl i j = 1
  证明: by
  #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
  (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal
  without the `simp`. This is probably a problem at Mathlib's end rather than `grind`'s,
  as we are relying on seeing through

Depends on / 依赖: Before, Mathlib, Matrix, adaptation_note, canonicalizer, closed, definition, directed, github, github.com, leanprover, normalizer, probably, problem, rather, relying, replacing, seeing, through, without
-/
theorem compl_apply [Zero α] [One α] (i j : V) : A.compl i j = 0 ∨ A.compl i j = 1 := by
  #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
  (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal
  without the `simp`. This is probably a problem at Mathlib's end rather than `grind`'s,
  as we are relying on seeing through the definition of `Matrix`, and `of`. -/
  simp [compl]
  grind

@[simp]
/--
theorem `isSymm_compl` / 定理 `isSymm_compl`

English:
theorem isSymm_compl
  given: [Zero α] [One α] (h : A.IsSymm)
  statement: A.compl.IsSymm
  proof: by
  ext
  simp [compl, h.apply, eq_comm]

@[simp]

中文:
定理 isSymm_compl
  条件: [Zero α] [One α] (h : A.IsSymm)
  结论: A.compl.IsSymm
  证明: by
  ext
  simp [compl, h.apply, eq_comm]

@[simp]

Depends on / 依赖: eq_comm, h.apply
-/
theorem isSymm_compl [Zero α] [One α] (h : A.IsSymm) : A.compl.IsSymm := by
  ext
  simp [compl, h.apply, eq_comm]

@[simp]
/--
theorem `isAdjMatrix_compl` / 定理 `isAdjMatrix_compl`

English:
theorem isAdjMatrix_compl
  given: [Zero α] [One α] (h : A.IsSymm)
  statement: IsAdjMatrix A.compl
  proof: { symm := by simp [h] }

中文:
定理 isAdjMatrix_compl
  条件: [Zero α] [One α] (h : A.IsSymm)
  结论: IsAdjMatrix A.compl
  证明: { symm := by simp [h] }
-/
theorem isAdjMatrix_compl [Zero α] [One α] (h : A.IsSymm) : IsAdjMatrix A.compl :=
  { symm := by simp [h] }

/--
theorem `IsAdjMatrix.compl_inj` / 定理 `IsAdjMatrix.compl_inj`

English:
theorem IsAdjMatrix.compl_inj
  statement: [Zero α] [One α] {A B : Matrix V V α}
  proof: ⟨fun h => ext fun i j => by
    #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
    (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal
    without the `simp`. This is probably a problem at Mathlib's end rather than `grind`'s,
    as

中文:
定理 IsAdjMatrix.compl_inj
  结论: [Zero α] [One α] {A B : Matrix V V α}
  证明: ⟨fun h => ext fun i j => by
    #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
    (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal
    without the `simp`. This is probably a problem at Mathlib's end rather than `grind`'s,
    as

Depends on / 依赖: Before, IsAdjMatrix, Mathlib, Matrix, adaptation_note, canonicalizer, closed, definition, directed, github, github.com, leanprover, normalizer, original, probably, problem, rather, relying, replacing, seeing
-/
theorem IsAdjMatrix.compl_inj [Zero α] [One α] {A B : Matrix V V α}
    (hA : A.IsAdjMatrix) (hB : B.IsAdjMatrix) : A.compl = B.compl ↔ A = B :=
  ⟨fun h => ext fun i j => by
    #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
    (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal
    without the `simp`. This is probably a problem at Mathlib's end rather than `grind`'s,
    as we are relying on seeing through the definition of `Matrix`, and `of`.
    The original proof was: `grind [of, congr($h i j), compl, IsAdjMatrix]` -/
    simp [compl] at h; grind [congr($h i j), IsAdjMatrix], fun h => h ▸ rfl⟩

/--
theorem `IsAdjMatrix.compl_compl` / 定理 `IsAdjMatrix.compl_compl`

English:
theorem IsAdjMatrix.compl_compl
  given: [Zero α] [One α] {A : Matrix V V α} (hA : A.IsAdjMatrix)
  proof: by
  ext
  #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
  (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal
  without the `simp`. This is probably a problem at Mathlib's end rather than `grind`'s,
  as we are relying on seeing t

中文:
定理 IsAdjMatrix.compl_compl
  条件: [Zero α] [One α] {A : Matrix V V α} (hA : A.IsAdjMatrix)
  证明: by
  ext
  #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
  (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal
  without the `simp`. This is probably a problem at Mathlib's end rather than `grind`'s,
  as we are relying on seeing t
-/
@[simp] theorem IsAdjMatrix.compl_compl [Zero α] [One α] {A : Matrix V V α} (hA : A.IsAdjMatrix) :
    A.compl.compl = A := by
  ext
  #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
  (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal
  without the `simp`. This is probably a problem at Mathlib's end rather than `grind`'s,
  as we are relying on seeing through the definition of `Matrix`, and `of`. The original proof was:
  `grind [of, compl, IsAdjMatrix]` -/
  simp [compl]; grind [compl, IsAdjMatrix]

namespace IsAdjMatrix

variable {A}

@[simp]
/--
theorem `compl` / 定理 `compl`

English:
theorem compl
  given: [Zero α] [One α] (h : IsAdjMatrix A)
  statement: IsAdjMatrix A.compl
  proof: isAdjMatrix_compl A h.symm

中文:
定理 compl
  条件: [Zero α] [One α] (h : IsAdjMatrix A)
  结论: IsAdjMatrix A.compl
  证明: isAdjMatrix_compl A h.symm

Depends on / 依赖: h.symm, isAdjMatrix_compl
-/
theorem compl [Zero α] [One α] (h : IsAdjMatrix A) : IsAdjMatrix A.compl :=
  isAdjMatrix_compl A h.symm

/--
theorem `toGraph_compl_eq` / 定理 `toGraph_compl_eq`

English:
theorem toGraph_compl_eq
  given: [MulZeroOneClass α] [Nontrivial α] (h : IsAdjMatrix A)
  proof: by
  ext v w
  rcases h.zero_or_one v w with h | h <;> by_cases hvw : v = w <;> simp [Matrix.compl, h, hvw]

中文:
定理 toGraph_compl_eq
  条件: [MulZeroOneClass α] [Nontrivial α] (h : IsAdjMatrix A)
  证明: by
  ext v w
  rcases h.zero_or_one v w with h | h <;> by_cases hvw : v = w <;> simp [Matrix.compl, h, hvw]

Depends on / 依赖: Matrix, Matrix.compl, h.zero_or_one, zero_or_one
-/
theorem toGraph_compl_eq [MulZeroOneClass α] [Nontrivial α] (h : IsAdjMatrix A) :
    h.compl.toGraph = h.toGraphᶜ := by
  ext v w
  rcases h.zero_or_one v w with h | h <;> by_cases hvw : v = w <;> simp [Matrix.compl, h, hvw]

end IsAdjMatrix

end Compl

end Matrix

namespace SimpleGraph

variable (G : SimpleGraph V) [DecidableRel G.Adj]

variable (α) in
/--
Definition of `adjMatrix` / `adjMatrix` 的定义

English:
definition adjMatrix
  signature: [Zero α] [One α]
  body: of fun i j => if G.Adj i j then (1 : α) else 0

中文:
定义 adjMatrix
  签名: [Zero α] [One α]
  定义体: of fun i j => if G.Adj i j then (1 : α) else 0

Depends on / 依赖: G.Adj
-/
def adjMatrix [Zero α] [One α] : Matrix V V α :=
  of fun i j => if G.Adj i j then (1 : α) else 0

-- TODO: set as an equation lemma for `adjMatrix`, see https://github.com/leanprover-community/mathlib4/pull/3024
@[simp]
/--
theorem `adjMatrix_apply` / 定理 `adjMatrix_apply`

English:
theorem adjMatrix_apply
  given: (v w : V) [Zero α] [One α]
  proof: rfl

@[simp]

中文:
定理 adjMatrix_apply
  条件: (v w : V) [Zero α] [One α]
  证明: rfl

@[simp]
-/
theorem adjMatrix_apply (v w : V) [Zero α] [One α] :
    G.adjMatrix α v w = if G.Adj v w then 1 else 0 :=
  rfl

@[simp]
/--
theorem `adjMatrix_bot` / 定理 `adjMatrix_bot`

English:
theorem adjMatrix_bot
  given: [Zero α] [One α]
  proof: by
  ext; simp

@[simp]

中文:
定理 adjMatrix_bot
  条件: [Zero α] [One α]
  证明: by
  ext; simp

@[simp]
-/
theorem adjMatrix_bot [Zero α] [One α] :
    (⊥ : SimpleGraph V).adjMatrix α = 0 := by
  ext; simp

@[simp]
/--
theorem `adjMatrix_top` / 定理 `adjMatrix_top`

English:
theorem adjMatrix_top
  given: [DecidableEq V] [Ring α]
  proof: by
  ext i j
  cases eq_or_ne i j <;> simp [‹_›]

@[simp]

中文:
定理 adjMatrix_top
  条件: [DecidableEq V] [Ring α]
  证明: by
  ext i j
  cases eq_or_ne i j <;> simp [‹_›]

@[simp]

Depends on / 依赖: eq_or_ne
-/
theorem adjMatrix_top [DecidableEq V] [Ring α] :
    (⊤ : SimpleGraph V).adjMatrix α = .of (fun i j => if i = j then 0 else 1) := by
  ext i j
  cases eq_or_ne i j <;> simp [‹_›]

@[simp]
/--
theorem `transpose_adjMatrix` / 定理 `transpose_adjMatrix`

English:
theorem transpose_adjMatrix
  given: [Zero α] [One α]
  statement: (G.adjMatrix α)ᵀ = G.adjMatrix α
  proof: by
  ext
  simp [adj_comm]

@[simp]

中文:
定理 transpose_adjMatrix
  条件: [Zero α] [One α]
  结论: (G.adjMatrix α)ᵀ = G.adjMatrix α
  证明: by
  ext
  simp [adj_comm]

@[simp]

Depends on / 依赖: adj_comm
-/
theorem transpose_adjMatrix [Zero α] [One α] : (G.adjMatrix α)ᵀ = G.adjMatrix α := by
  ext
  simp [adj_comm]

@[simp]
/--
theorem `isSymm_adjMatrix` / 定理 `isSymm_adjMatrix`

English:
theorem isSymm_adjMatrix
  given: [Zero α] [One α]
  statement: (G.adjMatrix α).IsSymm
  proof: transpose_adjMatrix G

中文:
定理 isSymm_adjMatrix
  条件: [Zero α] [One α]
  结论: (G.adjMatrix α).IsSymm
  证明: transpose_adjMatrix G

Depends on / 依赖: transpose_adjMatrix
-/
theorem isSymm_adjMatrix [Zero α] [One α] : (G.adjMatrix α).IsSymm :=
  transpose_adjMatrix G

variable (α)

/-- The adjacency matrix of `G` is an adjacency matrix. -/
@[simp]
/--
theorem `isAdjMatrix_adjMatrix` / 定理 `isAdjMatrix_adjMatrix`

English:
theorem isAdjMatrix_adjMatrix
  given: [Zero α] [One α]
  statement: (G.adjMatrix α).IsAdjMatrix where
  proof: by grind [adjMatrix_apply]

中文:
定理 isAdjMatrix_adjMatrix
  条件: [Zero α] [One α]
  结论: (G.adjMatrix α).IsAdjMatrix where
  证明: by grind [adjMatrix_apply]

Depends on / 依赖: adjMatrix_apply
-/
theorem isAdjMatrix_adjMatrix [Zero α] [One α] : (G.adjMatrix α).IsAdjMatrix where
  zero_or_one := by grind [adjMatrix_apply]

/--
theorem `diag_adjMatrix` / 定理 `diag_adjMatrix`

English:
theorem diag_adjMatrix
  given: [Zero α] [One α]
  statement: (G.adjMatrix α).diag = 0
  proof: by
  simp

中文:
定理 diag_adjMatrix
  条件: [Zero α] [One α]
  结论: (G.adjMatrix α).diag = 0
  证明: by
  simp
-/
theorem diag_adjMatrix [Zero α] [One α] : (G.adjMatrix α).diag = 0 := by
  simp

/-- The graph induced by the adjacency matrix of `G` is `G` itself. -/
@[simp]
/--
theorem `toGraph_adjMatrix_eq` / 定理 `toGraph_adjMatrix_eq`

English:
theorem toGraph_adjMatrix_eq
  given: [MulZeroOneClass α] [Nontrivial α]
  proof: by
  ext
  simp only [IsAdjMatrix.toGraph_adj, adjMatrix_apply, ite_eq_left_iff, zero_ne_one]
  apply Classical.not_not

中文:
定理 toGraph_adjMatrix_eq
  条件: [MulZeroOneClass α] [Nontrivial α]
  证明: by
  ext
  simp only [IsAdjMatrix.toGraph_adj, adjMatrix_apply, ite_eq_left_iff, zero_ne_one]
  apply Classical.not_not

Depends on / 依赖: Classical, Classical.not_not, IsAdjMatrix, IsAdjMatrix.toGraph_adj, adjMatrix_apply, ite_eq_left_iff, not_not, toGraph_adj, zero_ne_one
-/
theorem toGraph_adjMatrix_eq [MulZeroOneClass α] [Nontrivial α] :
    (G.isAdjMatrix_adjMatrix α).toGraph = G := by
  ext
  simp only [IsAdjMatrix.toGraph_adj, adjMatrix_apply, ite_eq_left_iff, zero_ne_one]
  apply Classical.not_not

/--
theorem `compl_adjMatrix_eq_adjMatrix_compl` / 定理 `compl_adjMatrix_eq_adjMatrix_compl`

English:
theorem compl_adjMatrix_eq_adjMatrix_compl
  given: [DecidableEq V] [DecidableEq α] [Zero α] [One α]
  proof: by aesop (add simp [Matrix.compl])

中文:
定理 compl_adjMatrix_eq_adjMatrix_compl
  条件: [DecidableEq V] [DecidableEq α] [Zero α] [One α]
  证明: by aesop (add simp [Matrix.compl])

Depends on / 依赖: Matrix, Matrix.compl
-/
theorem compl_adjMatrix_eq_adjMatrix_compl [DecidableEq V] [DecidableEq α] [Zero α] [One α] :
    (G.adjMatrix α).compl = Gᶜ.adjMatrix α := by aesop (add simp [Matrix.compl])

variable {G} in
@[simp]
/--
theorem `Embedding.submatrix_adjMatrix` / 定理 `Embedding.submatrix_adjMatrix`

English:
theorem Embedding.submatrix_adjMatrix
  statement: [Zero α] [One α] {H : SimpleGraph W} [DecidableRel H.Adj]
  proof: by
  ext
  simp

中文:
定理 Embedding.submatrix_adjMatrix
  结论: [Zero α] [One α] {H : SimpleGraph W} [DecidableRel H.Adj]
  证明: by
  ext
  simp
-/
theorem Embedding.submatrix_adjMatrix [Zero α] [One α] {H : SimpleGraph W} [DecidableRel H.Adj]
    (f : G ↪g H) : (H.adjMatrix α).submatrix f f = G.adjMatrix α := by
  ext
  simp

variable {G} in
/--
theorem `Iso.reindex_adjMatrix` / 定理 `Iso.reindex_adjMatrix`

English:
theorem Iso.reindex_adjMatrix
  statement: [Zero α] [One α] {H : SimpleGraph W} [DecidableRel H.Adj]
  proof: f.symm.toEmbedding.submatrix_adjMatrix α

中文:
定理 Iso.reindex_adjMatrix
  结论: [Zero α] [One α] {H : SimpleGraph W} [DecidableRel H.Adj]
  证明: f.symm.toEmbedding.submatrix_adjMatrix α

Depends on / 依赖: f.symm.toEmbedding.submatrix_adjMatrix, submatrix_adjMatrix, toEmbedding
-/
theorem Iso.reindex_adjMatrix [Zero α] [One α] {H : SimpleGraph W} [DecidableRel H.Adj]
    (f : G ≃g H) : (G.adjMatrix α).reindex f f = H.adjMatrix α :=
  f.symm.toEmbedding.submatrix_adjMatrix α

variable {G} in
/--
theorem `IsCompl.adjMatrix_add_adjMatrix_eq_adjMatrix_completeGraph` / 定理 `IsCompl.adjMatrix_add_adjMatrix_eq_adjMatrix_completeGraph`

English:
theorem IsCompl.adjMatrix_add_adjMatrix_eq_adjMatrix_completeGraph
  statement: [DecidableEq V] [AddZeroClass α]
  proof: calc
  _ = G.adjMatrix α + Gᶜ.adjMatrix α := by have := h.compl_eq; subst this; congr
  _ = _ := by aesop (add simp Matrix.compl)

中文:
定理 IsCompl.adjMatrix_add_adjMatrix_eq_adjMatrix_completeGraph
  结论: [DecidableEq V] [AddZeroClass α]
  证明: calc
  _ = G.adjMatrix α + Gᶜ.adjMatrix α := by have := h.compl_eq; subst this; congr
  _ = _ := by aesop (add simp Matrix.compl)
-/
theorem IsCompl.adjMatrix_add_adjMatrix_eq_adjMatrix_completeGraph [DecidableEq V] [AddZeroClass α]
    [One α] {H : SimpleGraph V} [DecidableRel H.Adj] (h : IsCompl G H) :
    G.adjMatrix α + H.adjMatrix α = (completeGraph V).adjMatrix α := calc
  _ = G.adjMatrix α + Gᶜ.adjMatrix α := by have := h.compl_eq; subst this; congr
  _ = _ := by aesop (add simp Matrix.compl)

/--
theorem `adjMatrix_add_compl_adjMatrix_eq_adjMatrix_completeGraph` / 定理 `adjMatrix_add_compl_adjMatrix_eq_adjMatrix_completeGraph`

English:
theorem adjMatrix_add_compl_adjMatrix_eq_adjMatrix_completeGraph
  statement: [DecidableEq V]
  proof: G.compl_adjMatrix_eq_adjMatrix_compl α ▸
    isCompl_compl.adjMatrix_add_adjMatrix_eq_adjMatrix_completeGraph α

中文:
定理 adjMatrix_add_compl_adjMatrix_eq_adjMatrix_completeGraph
  结论: [DecidableEq V]
  证明: G.compl_adjMatrix_eq_adjMatrix_compl α ▸
    isCompl_compl.adjMatrix_add_adjMatrix_eq_adjMatrix_completeGraph α
-/
@[simp] theorem adjMatrix_add_compl_adjMatrix_eq_adjMatrix_completeGraph [DecidableEq V]
    [DecidableEq α] [AddZeroClass α] [One α] :
    G.adjMatrix α + (G.adjMatrix α).compl = (completeGraph V).adjMatrix α :=
  G.compl_adjMatrix_eq_adjMatrix_compl α ▸
    isCompl_compl.adjMatrix_add_adjMatrix_eq_adjMatrix_completeGraph α

/--
theorem `one_add_adjMatrix_add_compl_adjMatrix_eq_of_one` / 定理 `one_add_adjMatrix_add_compl_adjMatrix_eq_of_one`

English:
theorem one_add_adjMatrix_add_compl_adjMatrix_eq_of_one
  statement: [DecidableEq V] [DecidableEq α]
  proof: by
  aesop (add simp [add_assoc])

@[deprecated (since := "2026-01-30")] alias one_add_adjMatrix_add_compl_adjMatrix_eq_allOnes :=
  one_add_adjMatrix_add_compl_adjMatrix_eq_of_one

中文:
定理 one_add_adjMatrix_add_compl_adjMatrix_eq_of_one
  结论: [DecidableEq V] [DecidableEq α]
  证明: by
  aesop (add simp [add_assoc])

@[deprecated (since := "2026-01-30")] alias one_add_adjMatrix_add_compl_adjMatrix_eq_allOnes :=
  one_add_adjMatrix_add_compl_adjMatrix_eq_of_one

Depends on / 依赖: add_assoc
-/
theorem one_add_adjMatrix_add_compl_adjMatrix_eq_of_one [DecidableEq V] [DecidableEq α]
    [AddMonoid α] [One α] : 1 + G.adjMatrix α + (G.adjMatrix α).compl = of 1 := by
  aesop (add simp [add_assoc])

@[deprecated (since := "2026-01-30")] alias one_add_adjMatrix_add_compl_adjMatrix_eq_allOnes :=
  one_add_adjMatrix_add_compl_adjMatrix_eq_of_one

variable (V)

/--
theorem `compl_adjMatrix_completeGraph` / 定理 `compl_adjMatrix_completeGraph`

English:
theorem compl_adjMatrix_completeGraph
  given: [Zero α] [One α] [DecidableEq α] [DecidableEq V]
  proof: by aesop (add simp Matrix.compl)

中文:
定理 compl_adjMatrix_completeGraph
  条件: [Zero α] [One α] [DecidableEq α] [DecidableEq V]
  证明: by aesop (add simp Matrix.compl)
-/
@[simp] theorem compl_adjMatrix_completeGraph [Zero α] [One α] [DecidableEq α] [DecidableEq V] :
    ((completeGraph V).adjMatrix α).compl = 0 := by aesop (add simp Matrix.compl)

/--
theorem `_root_.Matrix.compl_zero` / 定理 `_root_.Matrix.compl_zero`

English:
theorem _root_.Matrix.compl_zero
  given: [Zero α] [One α] [DecidableEq α] [DecidableEq V]
  proof: by simp [← IsAdjMatrix.compl_inj]

中文:
定理 _root_.Matrix.compl_zero
  条件: [Zero α] [One α] [DecidableEq α] [DecidableEq V]
  证明: by simp [← IsAdjMatrix.compl_inj]
-/
@[simp] theorem _root_.Matrix.compl_zero [Zero α] [One α] [DecidableEq α] [DecidableEq V] :
    (0 : Matrix V V α).compl = (completeGraph V).adjMatrix α := by simp [← IsAdjMatrix.compl_inj]

/--
theorem `adjMatrix_completeGraph_eq_of_one_sub_one` / 定理 `adjMatrix_completeGraph_eq_of_one_sub_one`

English:
theorem adjMatrix_completeGraph_eq_of_one_sub_one
  given: [AddGroup α] [One α] [DecidableEq V]
  proof: by ext; simp [one_apply, sub_ite]

中文:
定理 adjMatrix_completeGraph_eq_of_one_sub_one
  条件: [AddGroup α] [One α] [DecidableEq V]
  证明: by ext; simp [one_apply, sub_ite]

Depends on / 依赖: one_apply, sub_ite
-/
theorem adjMatrix_completeGraph_eq_of_one_sub_one [AddGroup α] [One α] [DecidableEq V] :
    (completeGraph V).adjMatrix α = of 1 - 1 := by ext; simp [one_apply, sub_ite]

/--
theorem `_root_.Matrix.compl_zero_eq_of_one_sub_one` / 定理 `_root_.Matrix.compl_zero_eq_of_one_sub_one`

English:
theorem _root_.Matrix.compl_zero_eq_of_one_sub_one
  statement: [AddGroup α] [One α] [DecidableEq V]
  proof: by
  simp [adjMatrix_completeGraph_eq_of_one_sub_one]

中文:
定理 _root_.Matrix.compl_zero_eq_of_one_sub_one
  结论: [AddGroup α] [One α] [DecidableEq V]
  证明: by
  simp [adjMatrix_completeGraph_eq_of_one_sub_one]

Depends on / 依赖: adjMatrix_completeGraph_eq_of_one_sub_one
-/
theorem _root_.Matrix.compl_zero_eq_of_one_sub_one [AddGroup α] [One α] [DecidableEq V]
    [DecidableEq α] : (0 : Matrix V V α).compl = of 1 - 1 := by
  simp [adjMatrix_completeGraph_eq_of_one_sub_one]

/--
theorem `_root_.Matrix.compl_of_one_sub_one` / 定理 `_root_.Matrix.compl_of_one_sub_one`

English:
theorem _root_.Matrix.compl_of_one_sub_one
  statement: [AddGroup α] [One α] [DecidableEq V]
  proof: by
  simp [← adjMatrix_completeGraph_eq_of_one_sub_one]

中文:
定理 _root_.Matrix.compl_of_one_sub_one
  结论: [AddGroup α] [One α] [DecidableEq V]
  证明: by
  simp [← adjMatrix_completeGraph_eq_of_one_sub_one]
-/
@[simp] theorem _root_.Matrix.compl_of_one_sub_one [AddGroup α] [One α] [DecidableEq V]
    [DecidableEq α] : (of 1 - 1 : Matrix V V α).compl = 0 := by
  simp [← adjMatrix_completeGraph_eq_of_one_sub_one]

variable {V}

/--
theorem `adjMatrix_hadamard_self` / 定理 `adjMatrix_hadamard_self`

English:
theorem adjMatrix_hadamard_self
  given: [MulZeroOneClass α]
  proof: by simp

中文:
定理 adjMatrix_hadamard_self
  条件: [MulZeroOneClass α]
  证明: by simp
-/
theorem adjMatrix_hadamard_self [MulZeroOneClass α] :
    G.adjMatrix α ⊙ G.adjMatrix α = G.adjMatrix α := by simp

variable {α}

section fintype
variable [Fintype V]

@[simp]
/--
theorem `adjMatrix_dotProduct` / 定理 `adjMatrix_dotProduct`

English:
theorem adjMatrix_dotProduct
  given: [NonAssocSemiring α] (v : V) (vec : V -> α)
  proof: by
  simp [neighborFinset_eq_filter, dotProduct, sum_filter]

@[simp]

中文:
定理 adjMatrix_dotProduct
  条件: [NonAssocSemiring α] (v : V) (vec : V -> α)
  证明: by
  simp [neighborFinset_eq_filter, dotProduct, sum_filter]

@[simp]

Depends on / 依赖: dotProduct, neighborFinset_eq_filter, sum_filter
-/
theorem adjMatrix_dotProduct [NonAssocSemiring α] (v : V) (vec : V -> α) :
    G.adjMatrix α v ⬝ᵥ vec = ∑ u in G.neighborFinset v, vec u := by
  simp [neighborFinset_eq_filter, dotProduct, sum_filter]

@[simp]
/--
theorem `dotProduct_adjMatrix` / 定理 `dotProduct_adjMatrix`

English:
theorem dotProduct_adjMatrix
  given: [NonAssocSemiring α] (v : V) (vec : V -> α)
  proof: by
  simp [neighborFinset_eq_filter, dotProduct, sum_filter]

@[simp]

中文:
定理 dotProduct_adjMatrix
  条件: [NonAssocSemiring α] (v : V) (vec : V -> α)
  证明: by
  simp [neighborFinset_eq_filter, dotProduct, sum_filter]

@[simp]

Depends on / 依赖: dotProduct, neighborFinset_eq_filter, sum_filter
-/
theorem dotProduct_adjMatrix [NonAssocSemiring α] (v : V) (vec : V -> α) :
    vec ⬝ᵥ G.adjMatrix α v = ∑ u in G.neighborFinset v, vec u := by
  simp [neighborFinset_eq_filter, dotProduct, sum_filter]

@[simp]
/--
theorem `adjMatrix_mulVec_apply` / 定理 `adjMatrix_mulVec_apply`

English:
theorem adjMatrix_mulVec_apply
  given: [NonAssocSemiring α] (v : V) (vec : V -> α)
  proof: by
  rw [mulVec]; rw [adjMatrix_dotProduct]

@[simp]

中文:
定理 adjMatrix_mulVec_apply
  条件: [NonAssocSemiring α] (v : V) (vec : V -> α)
  证明: by
  rw [mulVec]; rw [adjMatrix_dotProduct]

@[simp]

Depends on / 依赖: adjMatrix_dotProduct, mulVec
-/
theorem adjMatrix_mulVec_apply [NonAssocSemiring α] (v : V) (vec : V -> α) :
    (G.adjMatrix α *ᵥ vec) v = ∑ u in G.neighborFinset v, vec u := by
  rw [mulVec]; rw [adjMatrix_dotProduct]

@[simp]
/--
theorem `adjMatrix_vecMul_apply` / 定理 `adjMatrix_vecMul_apply`

English:
theorem adjMatrix_vecMul_apply
  given: [NonAssocSemiring α] (v : V) (vec : V -> α)
  proof: by
  simp only [← dotProduct_adjMatrix, vecMul]
  refine congr rfl ?_; ext x
  rw [← transpose_apply (adjMatrix α G) x v]; rw [transpose_adjMatrix]

@[simp]

中文:
定理 adjMatrix_vecMul_apply
  条件: [NonAssocSemiring α] (v : V) (vec : V -> α)
  证明: by
  simp only [← dotProduct_adjMatrix, vecMul]
  refine congr rfl ?_; ext x
  rw [← transpose_apply (adjMatrix α G) x v]; rw [transpose_adjMatrix]

@[simp]

Depends on / 依赖: adjMatrix, dotProduct_adjMatrix, transpose_adjMatrix, transpose_apply, vecMul
-/
theorem adjMatrix_vecMul_apply [NonAssocSemiring α] (v : V) (vec : V -> α) :
    (vec ᵥ* G.adjMatrix α) v = ∑ u in G.neighborFinset v, vec u := by
  simp only [← dotProduct_adjMatrix, vecMul]
  refine congr rfl ?_; ext x
  rw [← transpose_apply (adjMatrix α G) x v]; rw [transpose_adjMatrix]

@[simp]
/--
theorem `adjMatrix_mul_apply` / 定理 `adjMatrix_mul_apply`

English:
theorem adjMatrix_mul_apply
  given: [NonAssocSemiring α] (M : Matrix V V α) (v w : V)
  proof: by
  simp [mul_apply, neighborFinset_eq_filter, sum_filter]

@[simp]

中文:
定理 adjMatrix_mul_apply
  条件: [NonAssocSemiring α] (M : Matrix V V α) (v w : V)
  证明: by
  simp [mul_apply, neighborFinset_eq_filter, sum_filter]

@[simp]

Depends on / 依赖: mul_apply, neighborFinset_eq_filter, sum_filter
-/
theorem adjMatrix_mul_apply [NonAssocSemiring α] (M : Matrix V V α) (v w : V) :
    (G.adjMatrix α * M) v w = ∑ u in G.neighborFinset v, M u w := by
  simp [mul_apply, neighborFinset_eq_filter, sum_filter]

@[simp]
/--
theorem `mul_adjMatrix_apply` / 定理 `mul_adjMatrix_apply`

English:
theorem mul_adjMatrix_apply
  given: [NonAssocSemiring α] (M : Matrix V V α) (v w : V)
  proof: by
  simp [mul_apply, neighborFinset_eq_filter, sum_filter, adj_comm]

中文:
定理 mul_adjMatrix_apply
  条件: [NonAssocSemiring α] (M : Matrix V V α) (v w : V)
  证明: by
  simp [mul_apply, neighborFinset_eq_filter, sum_filter, adj_comm]

Depends on / 依赖: adj_comm, mul_apply, neighborFinset_eq_filter, sum_filter
-/
theorem mul_adjMatrix_apply [NonAssocSemiring α] (M : Matrix V V α) (v w : V) :
    (M * G.adjMatrix α) v w = ∑ u in G.neighborFinset w, M v u := by
  simp [mul_apply, neighborFinset_eq_filter, sum_filter, adj_comm]

variable (α) in
@[simp]
/--
theorem `trace_adjMatrix` / 定理 `trace_adjMatrix`

English:
theorem trace_adjMatrix
  given: [AddCommMonoid α] [One α]
  statement: Matrix.trace (G.adjMatrix α) = 0
  proof: by
  simp [Matrix.trace]

中文:
定理 trace_adjMatrix
  条件: [AddCommMonoid α] [One α]
  结论: Matrix.trace (G.adjMatrix α) = 0
  证明: by
  simp [Matrix.trace]

Depends on / 依赖: Matrix, Matrix.trace
-/
theorem trace_adjMatrix [AddCommMonoid α] [One α] : Matrix.trace (G.adjMatrix α) = 0 := by
  simp [Matrix.trace]

/--
theorem `adjMatrix_mul_self_apply_self` / 定理 `adjMatrix_mul_self_apply_self`

English:
theorem adjMatrix_mul_self_apply_self
  given: [NonAssocSemiring α] (i : V)
  proof: by simp [filter_true_of_mem]

中文:
定理 adjMatrix_mul_self_apply_self
  条件: [NonAssocSemiring α] (i : V)
  证明: by simp [filter_true_of_mem]

Depends on / 依赖: filter_true_of_mem
-/
theorem adjMatrix_mul_self_apply_self [NonAssocSemiring α] (i : V) :
    (G.adjMatrix α * G.adjMatrix α) i i = degree G i := by simp [filter_true_of_mem]

variable (R) in
/--
theorem `natCast_card_dart_eq_dotProduct` / 定理 `natCast_card_dart_eq_dotProduct`

English:
theorem natCast_card_dart_eq_dotProduct
  given: [NonAssocSemiring α]
  proof: by
  simp [G.dart_card_eq_sum_degrees, dotProduct_one]

中文:
定理 natCast_card_dart_eq_dotProduct
  条件: [NonAssocSemiring α]
  证明: by
  simp [G.dart_card_eq_sum_degrees, dotProduct_one]

Depends on / 依赖: G.dart_card_eq_sum_degrees, dart_card_eq_sum_degrees, dotProduct_one
-/
theorem natCast_card_dart_eq_dotProduct [NonAssocSemiring α] :
    (Fintype.card G.Dart : α) = adjMatrix α G *ᵥ 1 ⬝ᵥ 1 := by
  simp [G.dart_card_eq_sum_degrees, dotProduct_one]

variable {G}

/--
theorem `adjMatrix_mulVec_const_apply` / 定理 `adjMatrix_mulVec_const_apply`

English:
theorem adjMatrix_mulVec_const_apply
  given: [NonAssocSemiring α] {a : α} {v : V}
  proof: by simp

中文:
定理 adjMatrix_mulVec_const_apply
  条件: [NonAssocSemiring α] {a : α} {v : V}
  证明: by simp
-/
theorem adjMatrix_mulVec_const_apply [NonAssocSemiring α] {a : α} {v : V} :
    (G.adjMatrix α *ᵥ Function.const _ a) v = G.degree v * a := by simp

/--
theorem `adjMatrix_mulVec_const_apply_of_regular` / 定理 `adjMatrix_mulVec_const_apply_of_regular`

English:
theorem adjMatrix_mulVec_const_apply_of_regular
  statement: [NonAssocSemiring α] {d : Nat} {a : α}
  proof: by
  simp [hd v]

中文:
定理 adjMatrix_mulVec_const_apply_of_regular
  结论: [NonAssocSemiring α] {d : 自然数} {a : α}
  证明: by
  simp [hd v]
-/
theorem adjMatrix_mulVec_const_apply_of_regular [NonAssocSemiring α] {d : Nat} {a : α}
    (hd : G.IsRegularOfDegree d) {v : V} : (G.adjMatrix α *ᵥ Function.const _ a) v = d * a := by
  simp [hd v]

/--
theorem `adjMatrix_pow_apply_eq_card_walk` / 定理 `adjMatrix_pow_apply_eq_card_walk`

English:
theorem adjMatrix_pow_apply_eq_card_walk
  given: [DecidableEq V] [Semiring α] (n : Nat) (u v : V)
  proof: by
  rw [card_set_walk_length_eq]
  induction n generalizing u v with
  | zero => obtain rfl | h := eq_or_ne u v <;> simp [finsetWalkLength, *]
  | succ n ih =>
    simp only [pow_succ', finsetWalkLength, ih, adjMatrix_mul_apply]
    rw [Finset.card_biUnion]
    · norm_cast
      simp only [Nat.cast

中文:
定理 adjMatrix_pow_apply_eq_card_walk
  条件: [DecidableEq V] [Semiring α] (n : 自然数) (u v : V)
  证明: by
  rw [card_set_walk_length_eq]
  induction n generalizing u v with
  | zero => obtain rfl | h := eq_or_ne u v <;> simp [finsetWalkLength, *]
  | succ n ih =>
    simp only [pow_succ', finsetWalkLength, ih, adjMatrix_mul_apply]
    rw [Finset.card_biUnion]
    · norm_cast
      simp only [Nat.cast

Depends on / 依赖: Finset, Finset.card_biUnion, Finset.sum_toFinset_eq_subtype, Nat.cast_sum, adjMatrix_mul_apply, card_biUnion, card_map, card_set_walk_length_eq, cast_sum, eq_or_ne, finsetWalkLength, generalizing, neighborFinset_def, pow_succ, sum_toFinset_eq_subtype
-/
theorem adjMatrix_pow_apply_eq_card_walk [DecidableEq V] [Semiring α] (n : Nat) (u v : V) :
    (G.adjMatrix α ^ n) u v = Fintype.card { p : G.Walk u v | p.length = n } := by
  rw [card_set_walk_length_eq]
  induction n generalizing u v with
  | zero => obtain rfl | h := eq_or_ne u v <;> simp [finsetWalkLength, *]
  | succ n ih =>
    simp only [pow_succ', finsetWalkLength, ih, adjMatrix_mul_apply]
    rw [Finset.card_biUnion]
    · norm_cast
      simp only [Nat.cast_sum, card_map, neighborFinset_def]
      apply Finset.sum_toFinset_eq_subtype
    -- Disjointness for card_bUnion
    · rintro ⟨x, hx⟩ - ⟨y, hy⟩ - hxy
      rw [Function.onFun]; rw [disjoint_iff_inf_le]
      intro p hp
      simp only [inf_eq_inter, mem_inter, mem_map] at hp
      obtain ⟨⟨px, _, rfl⟩, ⟨py, hpy, hp⟩⟩ := hp
      cases hp
      simp at hxy

/--
theorem `dotProduct_mulVec_adjMatrix` / 定理 `dotProduct_mulVec_adjMatrix`

English:
theorem dotProduct_mulVec_adjMatrix
  given: [NonAssocSemiring α] (x y : V -> α)
  proof: by
  simp [dotProduct, mulVec, mul_sum]

中文:
定理 dotProduct_mulVec_adjMatrix
  条件: [NonAssocSemiring α] (x y : V -> α)
  证明: by
  simp [dotProduct, mulVec, mul_sum]

Depends on / 依赖: dotProduct, mulVec, mul_sum
-/
theorem dotProduct_mulVec_adjMatrix [NonAssocSemiring α] (x y : V -> α) :
    x ⬝ᵥ G.adjMatrix α *ᵥ y = ∑ i : V, ∑ j : V, if G.Adj i j then x i * y j else 0 := by
  simp [dotProduct, mulVec, mul_sum]

end fintype

section hadamard
variable (α) [DecidableEq V] [MulZeroOneClass α]

open Matrix

/--
theorem `adjMatrix_hadamard_diagonal` / 定理 `adjMatrix_hadamard_diagonal`

English:
theorem adjMatrix_hadamard_diagonal
  given: (d : V -> α)
  proof: by simp [hadamard_diagonal]

中文:
定理 adjMatrix_hadamard_diagonal
  条件: (d : V -> α)
  证明: by simp [hadamard_diagonal]
-/
@[simp] theorem adjMatrix_hadamard_diagonal (d : V -> α) :
    G.adjMatrix α ⊙ diagonal d = 0 := by simp [hadamard_diagonal]

/--
theorem `diagonal_hadamard_adjMatrix` / 定理 `diagonal_hadamard_adjMatrix`

English:
theorem diagonal_hadamard_adjMatrix
  given: (d : V -> α)
  proof: by simp [diagonal_hadamard]

中文:
定理 diagonal_hadamard_adjMatrix
  条件: (d : V -> α)
  证明: by simp [diagonal_hadamard]
-/
@[simp] theorem diagonal_hadamard_adjMatrix (d : V -> α) :
    diagonal d ⊙ G.adjMatrix α = 0 := by simp [diagonal_hadamard]

/--
theorem `adjMatrix_hadamard_natCast` / 定理 `adjMatrix_hadamard_natCast`

English:
theorem adjMatrix_hadamard_natCast
  given: [NatCast α] (a : Nat)
  proof: adjMatrix_hadamard_diagonal _ _ _

中文:
定理 adjMatrix_hadamard_natCast
  条件: [自然数Cast α] (a : 自然数)
  证明: adjMatrix_hadamard_diagonal _ _ _
-/
@[simp] theorem adjMatrix_hadamard_natCast [NatCast α] (a : Nat) :
    G.adjMatrix α ⊙ a.cast = 0 := adjMatrix_hadamard_diagonal _ _ _

/--
theorem `natCast_hadamard_adjMatrix` / 定理 `natCast_hadamard_adjMatrix`

English:
theorem natCast_hadamard_adjMatrix
  given: [NatCast α] (a : Nat)
  proof: diagonal_hadamard_adjMatrix _ _ _

中文:
定理 natCast_hadamard_adjMatrix
  条件: [自然数Cast α] (a : 自然数)
  证明: diagonal_hadamard_adjMatrix _ _ _
-/
@[simp] theorem natCast_hadamard_adjMatrix [NatCast α] (a : Nat) :
    a.cast ⊙ G.adjMatrix α = 0 := diagonal_hadamard_adjMatrix _ _ _

/--
theorem `adjMatrix_hadamard_ofNat` / 定理 `adjMatrix_hadamard_ofNat`

English:
theorem adjMatrix_hadamard_ofNat
  given: [NatCast α] (a : Nat) [a.AtLeastTwo]
  proof: adjMatrix_hadamard_diagonal _ _ _

中文:
定理 adjMatrix_hadamard_ofNat
  条件: [自然数Cast α] (a : 自然数) [a.AtLeastTwo]
  证明: adjMatrix_hadamard_diagonal _ _ _
-/
@[simp] theorem adjMatrix_hadamard_ofNat [NatCast α] (a : Nat) [a.AtLeastTwo] :
    G.adjMatrix α ⊙ ofNat(a) = 0 := adjMatrix_hadamard_diagonal _ _ _

/--
theorem `ofNat_hadamard_adjMatrix` / 定理 `ofNat_hadamard_adjMatrix`

English:
theorem ofNat_hadamard_adjMatrix
  given: [NatCast α] (a : Nat) [a.AtLeastTwo]
  proof: diagonal_hadamard_adjMatrix _ _ _

中文:
定理 ofNat_hadamard_adjMatrix
  条件: [自然数Cast α] (a : 自然数) [a.AtLeastTwo]
  证明: diagonal_hadamard_adjMatrix _ _ _
-/
@[simp] theorem ofNat_hadamard_adjMatrix [NatCast α] (a : Nat) [a.AtLeastTwo] :
    ofNat(a) ⊙ G.adjMatrix α = 0 := diagonal_hadamard_adjMatrix _ _ _

/--
theorem `adjMatrix_hadamard_intCast` / 定理 `adjMatrix_hadamard_intCast`

English:
theorem adjMatrix_hadamard_intCast
  given: [IntCast α] (a : Int)
  proof: adjMatrix_hadamard_diagonal _ _ _

中文:
定理 adjMatrix_hadamard_intCast
  条件: [整数Cast α] (a : 整数)
  证明: adjMatrix_hadamard_diagonal _ _ _
-/
@[simp] theorem adjMatrix_hadamard_intCast [IntCast α] (a : Int) :
    G.adjMatrix α ⊙ a.cast = 0 := adjMatrix_hadamard_diagonal _ _ _

/--
theorem `intCast_hadamard_adjMatrix` / 定理 `intCast_hadamard_adjMatrix`

English:
theorem intCast_hadamard_adjMatrix
  given: [IntCast α] (a : Int)
  proof: diagonal_hadamard_adjMatrix _ _ _

中文:
定理 intCast_hadamard_adjMatrix
  条件: [整数Cast α] (a : 整数)
  证明: diagonal_hadamard_adjMatrix _ _ _
-/
@[simp] theorem intCast_hadamard_adjMatrix [IntCast α] (a : Int) :
    a.cast ⊙ G.adjMatrix α = 0 := diagonal_hadamard_adjMatrix _ _ _

/--
theorem `adjMatrix_hadamard_one` / 定理 `adjMatrix_hadamard_one`

English:
theorem adjMatrix_hadamard_one
  proof: adjMatrix_hadamard_diagonal _ _ _

中文:
定理 adjMatrix_hadamard_one
  证明: adjMatrix_hadamard_diagonal _ _ _
-/
@[simp] theorem adjMatrix_hadamard_one :
    G.adjMatrix α ⊙ 1 = 0 := adjMatrix_hadamard_diagonal _ _ _

/--
theorem `one_hadamard_adjMatrix` / 定理 `one_hadamard_adjMatrix`

English:
theorem one_hadamard_adjMatrix
  proof: diagonal_hadamard_adjMatrix _ _ _

中文:
定理 one_hadamard_adjMatrix
  证明: diagonal_hadamard_adjMatrix _ _ _
-/
@[simp] theorem one_hadamard_adjMatrix :
    1 ⊙ G.adjMatrix α = 0 := diagonal_hadamard_adjMatrix _ _ _

end hadamard

end SimpleGraph

namespace Matrix.IsAdjMatrix

variable [MulZeroOneClass α] [Nontrivial α]
variable {A : Matrix V V α} (h : IsAdjMatrix A)

/--
theorem `adjMatrix_toGraph_eq` / 定理 `adjMatrix_toGraph_eq`

English:
theorem adjMatrix_toGraph_eq
  given: [DecidableEq α]
  statement: h.toGraph.adjMatrix α = A
  proof: by
  ext i j
  obtain h' | h' := h.zero_or_one i j <;> simp [h']

中文:
定理 adjMatrix_toGraph_eq
  条件: [DecidableEq α]
  结论: h.toGraph.adjMatrix α = A
  证明: by
  ext i j
  obtain h' | h' := h.zero_or_one i j <;> simp [h']

Depends on / 依赖: h.zero_or_one, zero_or_one
-/
theorem adjMatrix_toGraph_eq [DecidableEq α] : h.toGraph.adjMatrix α = A := by
  ext i j
  obtain h' | h' := h.zero_or_one i j <;> simp [h']

end Matrix.IsAdjMatrix
