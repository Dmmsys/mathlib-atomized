/-
Copyright (c) 2021 Gabriel Moise. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Moise, Yaël Dillies, Kyle Miller
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Finset.Sym
public import Mathlib.Data.Matrix.Mul

/-!
# Incidence matrix of a simple graph

This file defines the unoriented incidence matrix of a simple graph.

## Main definitions

* `SimpleGraph.incMatrix`: `G.incMatrix R` is the incidence matrix of `G` over the ring `R`.

## Main results

* `SimpleGraph.incMatrix_mul_transpose_diag`: The diagonal entries of the product of
  `G.incMatrix R` and its transpose are the degrees of the vertices.
* `SimpleGraph.incMatrix_mul_transpose`: Gives a complete description of the product of
  `G.incMatrix R` and its transpose; the diagonal is the degrees of each vertex, and the
  off-diagonals are 1 or 0 depending on whether or not the vertices are adjacent.
* `SimpleGraph.incMatrix_transpose_mul_diag`: The diagonal entries of the product of the
  transpose of `G.incMatrix R` and `G.inc_matrix R` are `2` or `0` depending on whether or
  not the unordered pair is an edge of `G`.

## Implementation notes

The usual definition of an incidence matrix has one row per vertex and one column per edge.
However, this definition has columns indexed by all of `Sym2 α`, where `α` is the vertex type.
This appears not to change the theory, and for simple graphs it has the nice effect that every
incidence matrix for each `SimpleGraph α` has the same type.

## TODO

* Define the oriented incidence matrices for oriented graphs.
* Define the graph Laplacian of a simple graph using the oriented incidence matrix from an
  arbitrary orientation of a simple graph.
-/

@[expose] public section

assert_not_exists Field

open Finset Matrix SimpleGraph Sym2

namespace SimpleGraph

variable (R : Type*) {α : Type*} (G : SimpleGraph α)

/--
Definition of `incMatrix` / `incMatrix` 的定义

English:
definition incMatrix
  signature: [Zero R] [One R] [DecidableEq α] [DecidableRel G.Adj]
  body: .of fun a e =>
    if e in G.incidenceSet a then 1 else 0

中文:
定义 incMatrix
  签名: [零 R] [幺 R] [DecidableEq α] [DecidableRel G.伴随]
  定义体: .of fun a e =>
    if e in G.incidenceSet a then 1 else 0

Depends on / 依赖: G.incidenceSet, incidenceSet
-/
def incMatrix [Zero R] [One R] [DecidableEq α] [DecidableRel G.Adj] : Matrix α (Sym2 α) R :=
  .of fun a e =>
    if e in G.incidenceSet a then 1 else 0

variable {R}

/--
theorem `incMatrix_apply` / 定理 `incMatrix_apply`

English:
theorem incMatrix_apply
  given: [Zero R] [One R] [DecidableEq α] [DecidableRel G.Adj] {a : α} {e : Sym2 α}
  proof: by
  simp [incMatrix, Set.indicator]

中文:
定理 incMatrix_apply
  条件: [零 R] [幺 R] [DecidableEq α] [DecidableRel G.伴随] {a : α} {e : Sym2 α}
  证明: by
  simp [incMatrix, Set.indicator]

Depends on / 依赖: Set.indicator, incMatrix, indicator
-/
theorem incMatrix_apply [Zero R] [One R] [DecidableEq α] [DecidableRel G.Adj] {a : α} {e : Sym2 α} :
    G.incMatrix R a e = (G.incidenceSet a).indicator 1 e := by
  simp [incMatrix, Set.indicator]

/--
theorem `incMatrix_apply'` / 定理 `incMatrix_apply'`

English:
theorem incMatrix_apply'
  statement: [Zero R] [One R] [DecidableEq α] [DecidableRel G.Adj] {a : α}
  proof: rfl

中文:
定理 incMatrix_apply'
  结论: [零 R] [幺 R] [DecidableEq α] [DecidableRel G.伴随] {a : α}
  证明: rfl
-/
theorem incMatrix_apply' [Zero R] [One R] [DecidableEq α] [DecidableRel G.Adj] {a : α}
    {e : Sym2 α} : G.incMatrix R a e = if e in G.incidenceSet a then 1 else 0 := rfl

section MulZeroOneClass

variable [MulZeroOneClass R] [DecidableEq α] [DecidableRel G.Adj] {a b : α} {e : Sym2 α}

/--
theorem `incMatrix_apply_mul_incMatrix_apply` / 定理 `incMatrix_apply_mul_incMatrix_apply`

English:
theorem incMatrix_apply_mul_incMatrix_apply
  statement: G.incMatrix R a e * G.incMatrix R b e =
  proof: by
  simp [incMatrix_apply', Set.indicator_apply, ← ite_and, and_comm]

中文:
定理 incMatrix_apply_mul_incMatrix_apply
  结论: G.incMatrix R a e * G.incMatrix R b e =
  证明: by
  simp [incMatrix_apply', Set.indicator_apply, ← ite_and, and_comm]

Depends on / 依赖: Set.indicator_apply, and_comm, incMatrix_apply, indicator_apply, ite_and
-/
theorem incMatrix_apply_mul_incMatrix_apply : G.incMatrix R a e * G.incMatrix R b e =
    (G.incidenceSet a inter G.incidenceSet b).indicator 1 e := by
  simp [incMatrix_apply', Set.indicator_apply, ← ite_and, and_comm]

/--
theorem `incMatrix_apply_mul_incMatrix_apply_of_not_adj` / 定理 `incMatrix_apply_mul_incMatrix_apply_of_not_adj`

English:
theorem incMatrix_apply_mul_incMatrix_apply_of_not_adj
  given: (hab : a != b) (h : ¬G.Adj a b)
  proof: by
  rw [incMatrix_apply_mul_incMatrix_apply]; rw [Set.indicator_of_notMem]
  rw [G.incidenceSet_inter_incidenceSet_of_not_adj h hab]
  exact Set.notMem_empty e

中文:
定理 incMatrix_apply_mul_incMatrix_apply_of_not_adj
  条件: (hab : a != b) (h : ¬G.伴随 a b)
  证明: by
  rw [incMatrix_apply_mul_incMatrix_apply]; rw [Set.indicator_of_notMem]
  rw [G.incidenceSet_inter_incidenceSet_of_not_adj h hab]
  exact Set.notMem_empty e

Depends on / 依赖: G.incidenceSet_inter_incidenceSet_of_not_adj, Set.indicator_of_notMem, Set.notMem_empty, incMatrix_apply_mul_incMatrix_apply, incidenceSet_inter_incidenceSet_of_not_adj, indicator_of_notMem, notMem_empty
-/
theorem incMatrix_apply_mul_incMatrix_apply_of_not_adj (hab : a != b) (h : ¬G.Adj a b) :
    G.incMatrix R a e * G.incMatrix R b e = 0 := by
  rw [incMatrix_apply_mul_incMatrix_apply]; rw [Set.indicator_of_notMem]
  rw [G.incidenceSet_inter_incidenceSet_of_not_adj h hab]
  exact Set.notMem_empty e

/--
theorem `incMatrix_of_notMem_incidenceSet` / 定理 `incMatrix_of_notMem_incidenceSet`

English:
theorem incMatrix_of_notMem_incidenceSet
  given: (h : e ∉ G.incidenceSet a)
  statement: G.incMatrix R a e = 0
  proof: by
  rw [incMatrix_apply]; rw [Set.indicator_of_notMem h]

中文:
定理 incMatrix_of_notMem_incidenceSet
  条件: (h : e ∉ G.incidenceSet a)
  结论: G.incMatrix R a e = 0
  证明: by
  rw [incMatrix_apply]; rw [Set.indicator_of_notMem h]

Depends on / 依赖: Set.indicator_of_notMem, incMatrix_apply, indicator_of_notMem
-/
theorem incMatrix_of_notMem_incidenceSet (h : e ∉ G.incidenceSet a) : G.incMatrix R a e = 0 := by
  rw [incMatrix_apply]; rw [Set.indicator_of_notMem h]

/--
theorem `incMatrix_of_mem_incidenceSet` / 定理 `incMatrix_of_mem_incidenceSet`

English:
theorem incMatrix_of_mem_incidenceSet
  given: (h : e in G.incidenceSet a)
  statement: G.incMatrix R a e = 1
  proof: by
  rw [incMatrix_apply]; rw [Set.indicator_of_mem h]; rw [Pi.one_apply]

中文:
定理 incMatrix_of_mem_incidenceSet
  条件: (h : e in G.incidenceSet a)
  结论: G.incMatrix R a e = 1
  证明: by
  rw [incMatrix_apply]; rw [Set.indicator_of_mem h]; rw [Pi.one_apply]

Depends on / 依赖: Pi.one_apply, Set.indicator_of_mem, incMatrix_apply, indicator_of_mem, one_apply
-/
theorem incMatrix_of_mem_incidenceSet (h : e in G.incidenceSet a) : G.incMatrix R a e = 1 := by
  rw [incMatrix_apply]; rw [Set.indicator_of_mem h]; rw [Pi.one_apply]

variable [Nontrivial R]

/--
theorem `incMatrix_apply_eq_zero_iff` / 定理 `incMatrix_apply_eq_zero_iff`

English:
theorem incMatrix_apply_eq_zero_iff
  statement: G.incMatrix R a e = 0 ↔ e ∉ G.incidenceSet a
  proof: by
  simp only [incMatrix_apply, Set.indicator_apply_eq_zero, Pi.one_apply, one_ne_zero]

中文:
定理 incMatrix_apply_eq_zero_iff
  结论: G.incMatrix R a e = 0 ↔ e ∉ G.incidenceSet a
  证明: by
  simp only [incMatrix_apply, Set.indicator_apply_eq_zero, Pi.one_apply, one_ne_zero]

Depends on / 依赖: Pi.one_apply, Set.indicator_apply_eq_zero, incMatrix_apply, indicator_apply_eq_zero, one_apply, one_ne_zero
-/
theorem incMatrix_apply_eq_zero_iff : G.incMatrix R a e = 0 ↔ e ∉ G.incidenceSet a := by
  simp only [incMatrix_apply, Set.indicator_apply_eq_zero, Pi.one_apply, one_ne_zero]

/--
theorem `incMatrix_apply_eq_one_iff` / 定理 `incMatrix_apply_eq_one_iff`

English:
theorem incMatrix_apply_eq_one_iff
  statement: G.incMatrix R a e = 1 ↔ e in G.incidenceSet a
  proof: by
  convert! one_ne_zero.ite_eq_left_iff
  infer_instance

中文:
定理 incMatrix_apply_eq_one_iff
  结论: G.incMatrix R a e = 1 ↔ e in G.incidenceSet a
  证明: by
  convert! one_ne_zero.ite_eq_left_iff
  infer_instance

Depends on / 依赖: convert, infer_instance, ite_eq_left_iff, one_ne_zero, one_ne_zero.ite_eq_left_iff
-/
theorem incMatrix_apply_eq_one_iff : G.incMatrix R a e = 1 ↔ e in G.incidenceSet a := by
  convert! one_ne_zero.ite_eq_left_iff
  infer_instance

end MulZeroOneClass

section NonAssocSemiring

variable [NonAssocSemiring R] [DecidableEq α] [DecidableRel G.Adj] {a : α} {e : Sym2 α}

/--
theorem `sum_incMatrix_apply` / 定理 `sum_incMatrix_apply`

English:
theorem sum_incMatrix_apply
  given: [Fintype (Sym2 α)] [Fintype (neighborSet G a)]
  proof: by
  simp [incMatrix_apply', sum_boole, Set.filter_mem_univ_eq_toFinset, card_incidenceSet_eq_degree]

中文:
定理 sum_incMatrix_apply
  条件: [有限类型 (Sym2 α)] [有限类型 (neighborSet G a)]
  证明: by
  simp [incMatrix_apply', sum_boole, Set.filter_mem_univ_eq_toFinset, card_incidenceSet_eq_degree]

Depends on / 依赖: Set.filter_mem_univ_eq_toFinset, card_incidenceSet_eq_degree, filter_mem_univ_eq_toFinset, incMatrix_apply, sum_boole
-/
theorem sum_incMatrix_apply [Fintype (Sym2 α)] [Fintype (neighborSet G a)] :
    ∑ e, G.incMatrix R a e = G.degree a := by
  simp [incMatrix_apply', sum_boole, Set.filter_mem_univ_eq_toFinset, card_incidenceSet_eq_degree]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `incMatrix_mul_transpose_diag` / 定理 `incMatrix_mul_transpose_diag`

English:
theorem incMatrix_mul_transpose_diag
  given: [Fintype (Sym2 α)] [Fintype (neighborSet G a)]
  proof: by
  rw [← sum_incMatrix_apply]
  simp only [mul_apply, incMatrix_apply', transpose_apply, mul_ite, mul_one, mul_zero]
  simp_all only [ite_true, sum_boole]

中文:
定理 incMatrix_mul_transpose_diag
  条件: [有限类型 (Sym2 α)] [有限类型 (neighborSet G a)]
  证明: by
  rw [← sum_incMatrix_apply]
  simp only [mul_apply, incMatrix_apply', transpose_apply, mul_ite, mul_one, mul_zero]
  simp_all only [ite_true, sum_boole]

Depends on / 依赖: incMatrix_apply, ite_true, mul_apply, mul_ite, mul_one, mul_zero, sum_boole, sum_incMatrix_apply, transpose_apply
-/
theorem incMatrix_mul_transpose_diag [Fintype (Sym2 α)] [Fintype (neighborSet G a)] :
    (G.incMatrix R * (G.incMatrix R)ᵀ) a a = G.degree a := by
  rw [← sum_incMatrix_apply]
  simp only [mul_apply, incMatrix_apply', transpose_apply, mul_ite, mul_one, mul_zero]
  simp_all only [ite_true, sum_boole]

/--
theorem `sum_incMatrix_apply_of_mem_edgeSet` / 定理 `sum_incMatrix_apply_of_mem_edgeSet`

English:
theorem sum_incMatrix_apply_of_mem_edgeSet
  given: [Fintype α]
  proof: by
  refine e.ind ?_
  intro a b h
  rw [mem_edgeSet] at h
  rw [← Nat.cast_two]; rw [← card_pair h.ne]
  simp only [incMatrix_apply', sum_boole, mk'_mem_incidenceSet_iff, h]
  congr 2
  ext e
  simp

中文:
定理 sum_incMatrix_apply_of_mem_edgeSet
  条件: [有限类型 α]
  证明: by
  refine e.ind ?_
  intro a b h
  rw [mem_edgeSet] at h
  rw [← Nat.cast_two]; rw [← card_pair h.ne]
  simp only [incMatrix_apply', sum_boole, mk'_mem_incidenceSet_iff, h]
  congr 2
  ext e
  simp

Depends on / 依赖: Nat.cast_two, _mem_incidenceSet_iff, card_pair, cast_two, e.ind, h.ne, incMatrix_apply, mem_edgeSet, sum_boole
-/
theorem sum_incMatrix_apply_of_mem_edgeSet [Fintype α] :
    e in G.edgeSet -> ∑ a, G.incMatrix R a e = 2 := by
  refine e.ind ?_
  intro a b h
  rw [mem_edgeSet] at h
  rw [← Nat.cast_two]; rw [← card_pair h.ne]
  simp only [incMatrix_apply', sum_boole, mk'_mem_incidenceSet_iff, h]
  congr 2
  ext e
  simp

/--
theorem `sum_incMatrix_apply_of_notMem_edgeSet` / 定理 `sum_incMatrix_apply_of_notMem_edgeSet`

English:
theorem sum_incMatrix_apply_of_notMem_edgeSet
  given: [Fintype α] (h : e ∉ G.edgeSet)
  proof: sum_eq_zero fun _ _ => G.incMatrix_of_notMem_incidenceSet fun he => h he.1

中文:
定理 sum_incMatrix_apply_of_notMem_edgeSet
  条件: [有限类型 α] (h : e ∉ G.edgeSet)
  证明: sum_eq_zero fun _ _ => G.incMatrix_of_notMem_incidenceSet fun he => h he.1

Depends on / 依赖: G.incMatrix_of_notMem_incidenceSet, incMatrix_of_notMem_incidenceSet, sum_eq_zero
-/
theorem sum_incMatrix_apply_of_notMem_edgeSet [Fintype α] (h : e ∉ G.edgeSet) :
    ∑ a, G.incMatrix R a e = 0 :=
  sum_eq_zero fun _ _ => G.incMatrix_of_notMem_incidenceSet fun he => h he.1

/--
theorem `incMatrix_transpose_mul_diag` / 定理 `incMatrix_transpose_mul_diag`

English:
theorem incMatrix_transpose_mul_diag
  given: [Fintype α] [Decidable (e in G.edgeSet)]
  proof: by
  simp only [Matrix.mul_apply, incMatrix_apply', transpose_apply, ite_zero_mul_ite_zero, one_mul,
    sum_boole, and_self_iff]
  split_ifs with h
  · revert h
    refine e.ind ?_
    intro v w h
    rw [← Nat.cast_two]; rw [← card_pair (G.ne_of_adj h)]
    simp only [mk'_mem_incidenceSet_iff, G.m

中文:
定理 incMatrix_transpose_mul_diag
  条件: [有限类型 α] [可判定 (e in G.edgeSet)]
  证明: by
  simp only [Matrix.mul_apply, incMatrix_apply', transpose_apply, ite_zero_mul_ite_zero, one_mul,
    sum_boole, and_self_iff]
  split_ifs with h
  · revert h
    refine e.ind ?_
    intro v w h
    rw [← Nat.cast_two]; rw [← card_pair (G.ne_of_adj h)]
    simp only [mk'_mem_incidenceSet_iff, G.m

Depends on / 依赖: G.mem_edgeSet.mp, G.mem_edgeSet.not.mp, G.ne_of_adj, Matrix, Matrix.mul_apply, Nat.cast_two, _mem_incidenceSet_iff, and_self_iff, card_pair, cast_two, e.ind, incMatrix_apply, ite_zero_mul_ite_zero, mem_edgeSet, mul_apply, ne_of_adj, one_mul, revert, split_ifs, sum_boole
-/
theorem incMatrix_transpose_mul_diag [Fintype α] [Decidable (e in G.edgeSet)] :
    ((G.incMatrix R)ᵀ * G.incMatrix R) e e = if e in G.edgeSet then 2 else 0 := by
  simp only [Matrix.mul_apply, incMatrix_apply', transpose_apply, ite_zero_mul_ite_zero, one_mul,
    sum_boole, and_self_iff]
  split_ifs with h
  · revert h
    refine e.ind ?_
    intro v w h
    rw [← Nat.cast_two]; rw [← card_pair (G.ne_of_adj h)]
    simp only [mk'_mem_incidenceSet_iff, G.mem_edgeSet.mp h, true_and]
    congr 2
    ext u
    simp
  · revert h
    refine e.ind ?_
    intro v w h
    simp [mk'_mem_incidenceSet_iff, G.mem_edgeSet.not.mp h]

end NonAssocSemiring

section Semiring

variable [Fintype (Sym2 α)] [DecidableEq α] [DecidableRel G.Adj] [Semiring R] {a b : α}

/--
theorem `incMatrix_mul_transpose_apply_of_adj` / 定理 `incMatrix_mul_transpose_apply_of_adj`

English:
theorem incMatrix_mul_transpose_apply_of_adj
  given: (h : G.Adj a b)
  proof: by
  simp_rw [Matrix.mul_apply, Matrix.transpose_apply, incMatrix_apply_mul_incMatrix_apply,
    Set.indicator_apply, Pi.one_apply, sum_boole]
  convert! @Nat.cast_one R _
  convert! card_singleton s(a, b)
  rw [← coe_eq_singleton]; rw [coe_filter_univ]
  exact G.incidenceSet_inter_incidenceSet_of_a

中文:
定理 incMatrix_mul_transpose_apply_of_adj
  条件: (h : G.伴随 a b)
  证明: by
  simp_rw [Matrix.mul_apply, Matrix.transpose_apply, incMatrix_apply_mul_incMatrix_apply,
    Set.indicator_apply, Pi.one_apply, sum_boole]
  convert! @Nat.cast_one R _
  convert! card_singleton s(a, b)
  rw [← coe_eq_singleton]; rw [coe_filter_univ]
  exact G.incidenceSet_inter_incidenceSet_of_a

Depends on / 依赖: G.incidenceSet_inter_incidenceSet_of_adj, Matrix, Matrix.mul_apply, Matrix.transpose_apply, Nat.cast_one, Pi.one_apply, Set.indicator_apply, card_singleton, cast_one, coe_eq_singleton, coe_filter_univ, convert, incMatrix_apply_mul_incMatrix_apply, incidenceSet_inter_incidenceSet_of_adj, indicator_apply, mul_apply, one_apply, simp_rw, sum_boole, transpose_apply
-/
theorem incMatrix_mul_transpose_apply_of_adj (h : G.Adj a b) :
    (G.incMatrix R * (G.incMatrix R)ᵀ) a b = (1 : R) := by
  simp_rw [Matrix.mul_apply, Matrix.transpose_apply, incMatrix_apply_mul_incMatrix_apply,
    Set.indicator_apply, Pi.one_apply, sum_boole]
  convert! @Nat.cast_one R _
  convert! card_singleton s(a, b)
  rw [← coe_eq_singleton]; rw [coe_filter_univ]
  exact G.incidenceSet_inter_incidenceSet_of_adj h

/--
theorem `incMatrix_mul_transpose` / 定理 `incMatrix_mul_transpose`

English:
theorem incMatrix_mul_transpose
  given: [G.LocallyFinite]
  proof: by
  ext a b
  dsimp
  split_ifs with h h'
  · subst b
    exact incMatrix_mul_transpose_diag (R := R) G
  · exact G.incMatrix_mul_transpose_apply_of_adj h'
  · simp only [Matrix.mul_apply, Matrix.transpose_apply,
      G.incMatrix_apply_mul_incMatrix_apply_of_not_adj h h', sum_const_zero]

中文:
定理 incMatrix_mul_transpose
  条件: [G.局部有限]
  证明: by
  ext a b
  dsimp
  split_ifs with h h'
  · subst b
    exact incMatrix_mul_transpose_diag (R := R) G
  · exact G.incMatrix_mul_transpose_apply_of_adj h'
  · simp only [Matrix.mul_apply, Matrix.transpose_apply,
      G.incMatrix_apply_mul_incMatrix_apply_of_not_adj h h', sum_const_zero]

Depends on / 依赖: G.incMatrix_apply_mul_incMatrix_apply_of_not_adj, G.incMatrix_mul_transpose_apply_of_adj, Matrix, Matrix.mul_apply, Matrix.transpose_apply, incMatrix_apply_mul_incMatrix_apply_of_not_adj, incMatrix_mul_transpose_apply_of_adj, incMatrix_mul_transpose_diag, mul_apply, split_ifs, sum_const_zero, transpose_apply
-/
theorem incMatrix_mul_transpose [G.LocallyFinite] :
    G.incMatrix R * (G.incMatrix R)ᵀ =
      of fun a b => if a = b then (G.degree a : R) else if G.Adj a b then 1 else 0 := by
  ext a b
  dsimp
  split_ifs with h h'
  · subst b
    exact incMatrix_mul_transpose_diag (R := R) G
  · exact G.incMatrix_mul_transpose_apply_of_adj h'
  · simp only [Matrix.mul_apply, Matrix.transpose_apply,
      G.incMatrix_apply_mul_incMatrix_apply_of_not_adj h h', sum_const_zero]

end Semiring

end SimpleGraph
