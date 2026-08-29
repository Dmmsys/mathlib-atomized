/-
Copyright (c) 2023 Adrian Wüthrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrian Wüthrich
-/
module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# Laplacian Matrix

This module defines the Laplacian matrix of a graph, and proves some of its elementary properties.

## Main definitions & Results

* `SimpleGraph.degMatrix`: The degree matrix of a simple graph
* `SimpleGraph.lapMatrix`: The Laplacian matrix of a simple graph, defined as the difference
  between the degree matrix and the adjacency matrix.
* `posSemidef_lapMatrix`: The Laplacian matrix is positive semidefinite.
* `card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix`:
  The number of connected components in a graph
  is the dimension of the nullspace of its Laplacian matrix.

-/

@[expose] public section

open Finset Matrix Module

namespace Matrix.IsAdjMatrix

variable {α V : Type*} [NonAssocSemiring α] [StarRing α] {A : Matrix V V α} (h : A.IsAdjMatrix)
include h

@[simp]
/--
theorem `isHermitian` / 定理 `isHermitian`

English:
theorem isHermitian
  statement: A.IsHermitian
  proof: by
  ext i j
  rcases h.zero_or_one i j with heq | heq
    <;> simp [heq, h.symm.apply]

中文:
定理 isHermitian
  结论: A.IsHermitian
  证明: by
  ext i j
  rcases h.zero_or_one i j with heq | heq
    <;> simp [heq, h.symm.apply]
-/
protected theorem isHermitian : A.IsHermitian := by
  ext i j
  rcases h.zero_or_one i j with heq | heq
    <;> simp [heq, h.symm.apply]

end Matrix.IsAdjMatrix

namespace SimpleGraph

variable {V : Type*} (R : Type*)
variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] in
/--
theorem `isHermitian_adjMatrix` / 定理 `isHermitian_adjMatrix`

English:
theorem isHermitian_adjMatrix
  given: [NonAssocSemiring R] [StarRing R]
  statement: (G.adjMatrix R).IsHermitian
  proof: .isHermitian G.isAdjMatrix_adjMatrix R

中文:
定理 isHermitian_adjMatrix
  条件: [NonAssocSemiring R] [StarRing R]
  结论: (G.adjMatrix R).IsHermitian
  证明: .isHermitian G.isAdjMatrix_adjMatrix R

Depends on / 依赖: G.isAdjMatrix_adjMatrix, isAdjMatrix_adjMatrix, isHermitian
-/
theorem isHermitian_adjMatrix [NonAssocSemiring R] [StarRing R] : (G.adjMatrix R).IsHermitian :=
.isHermitian G.isAdjMatrix_adjMatrix R

/--
theorem `degree_eq_sum_if_adj` / 定理 `degree_eq_sum_if_adj`

English:
theorem degree_eq_sum_if_adj
  given: {R : Type*} [AddCommMonoidWithOne R] (i : V)
  proof: by
  unfold degree neighborFinset neighborSet
  rw [sum_boole]; rw [Set.toFinset_ofPred]

中文:
定理 degree_eq_sum_if_adj
  条件: {R : 类型} [AddCommMonoidWithOne R] (i : V)
  证明: by
  unfold degree neighborFinset neighborSet
  rw [sum_boole]; rw [Set.toFinset_ofPred]

Depends on / 依赖: Set.toFinset_ofPred, degree, neighborFinset, neighborSet, sum_boole, toFinset_ofPred
-/
theorem degree_eq_sum_if_adj {R : Type*} [AddCommMonoidWithOne R] (i : V) :
    (G.degree i : R) = ∑ j : V, if G.Adj i j then 1 else 0 := by
  unfold degree neighborFinset neighborSet
  rw [sum_boole]; rw [Set.toFinset_ofPred]

variable [DecidableEq V]

/--
Definition of `degMatrix` / `degMatrix` 的定义

English:
definition degMatrix
  signature: [AddMonoidWithOne R]
  body: Matrix.diagonal (G.degree ·)

中文:
定义 degMatrix
  签名: [AddMonoidWithOne R]
  定义体: Matrix.diagonal (G.degree ·)

Depends on / 依赖: G.degree, Matrix, Matrix.diagonal, degree, diagonal
-/
def degMatrix [AddMonoidWithOne R] : Matrix V V R := Matrix.diagonal (G.degree ·)

/--
Definition of `lapMatrix` / `lapMatrix` 的定义

English:
definition lapMatrix
  signature: [AddGroupWithOne R]
  body: G.degMatrix R - G.adjMatrix R

中文:
定义 lapMatrix
  签名: [AddGroupWithOne R]
  定义体: G.degMatrix R - G.adjMatrix R

Depends on / 依赖: G.adjMatrix, G.degMatrix, adjMatrix, degMatrix
-/
def lapMatrix [AddGroupWithOne R] : Matrix V V R := G.degMatrix R - G.adjMatrix R

/--
theorem `isSymm_degMatrix` / 定理 `isSymm_degMatrix`

English:
theorem isSymm_degMatrix
  given: [AddMonoidWithOne R]
  statement: (G.degMatrix R).IsSymm
  proof: isSymm_diagonal _

中文:
定理 isSymm_degMatrix
  条件: [AddMonoidWithOne R]
  结论: (G.degMatrix R).IsSymm
  证明: isSymm_diagonal _

Depends on / 依赖: isSymm_diagonal
-/
theorem isSymm_degMatrix [AddMonoidWithOne R] : (G.degMatrix R).IsSymm :=
  isSymm_diagonal _

/--
theorem `isHermitian_degMatrix` / 定理 `isHermitian_degMatrix`

English:
theorem isHermitian_degMatrix
  given: [NonAssocSemiring R] [StarRing R]
  statement: (G.degMatrix R).IsHermitian
  proof: Matrix.isHermitian_diagonal_iff.mpr by simp

中文:
定理 isHermitian_degMatrix
  条件: [NonAssocSemiring R] [StarRing R]
  结论: (G.degMatrix R).IsHermitian
  证明: Matrix.isHermitian_diagonal_iff.mpr by simp

Depends on / 依赖: Matrix, Matrix.isHermitian_diagonal_iff.mpr, isHermitian_diagonal_iff
-/
theorem isHermitian_degMatrix [NonAssocSemiring R] [StarRing R] : (G.degMatrix R).IsHermitian :=
Matrix.isHermitian_diagonal_iff.mpr by simp

/--
theorem `isSymm_lapMatrix` / 定理 `isSymm_lapMatrix`

English:
theorem isSymm_lapMatrix
  given: [AddGroupWithOne R]
  statement: (G.lapMatrix R).IsSymm
  proof: .sub G.isSymm_adjMatrix G.isSymm_degMatrix R

中文:
定理 isSymm_lapMatrix
  条件: [AddGroupWithOne R]
  结论: (G.lapMatrix R).IsSymm
  证明: .sub G.isSymm_adjMatrix G.isSymm_degMatrix R

Depends on / 依赖: G.isSymm_adjMatrix, G.isSymm_degMatrix, isSymm_adjMatrix, isSymm_degMatrix
-/
theorem isSymm_lapMatrix [AddGroupWithOne R] : (G.lapMatrix R).IsSymm :=
.sub G.isSymm_adjMatrix G.isSymm_degMatrix R

/--
theorem `isHermitian_lapMatrix` / 定理 `isHermitian_lapMatrix`

English:
theorem isHermitian_lapMatrix
  given: [NonAssocRing R] [StarRing R]
  statement: (G.lapMatrix R).IsHermitian
  proof: .sub G.isHermitian_adjMatrix R G.isHermitian_degMatrix R

中文:
定理 isHermitian_lapMatrix
  条件: [NonAssocRing R] [StarRing R]
  结论: (G.lapMatrix R).IsHermitian
  证明: .sub G.isHermitian_adjMatrix R G.isHermitian_degMatrix R

Depends on / 依赖: G.isHermitian_adjMatrix, G.isHermitian_degMatrix, isHermitian_adjMatrix, isHermitian_degMatrix
-/
theorem isHermitian_lapMatrix [NonAssocRing R] [StarRing R] : (G.lapMatrix R).IsHermitian :=
.sub G.isHermitian_adjMatrix R G.isHermitian_degMatrix R

variable {R}

/--
theorem `degMatrix_mulVec_apply` / 定理 `degMatrix_mulVec_apply`

English:
theorem degMatrix_mulVec_apply
  given: [NonAssocSemiring R] (v : V) (vec : V -> R)
  proof: by
  rw [degMatrix]; rw [mulVec_diagonal]

中文:
定理 degMatrix_mulVec_apply
  条件: [NonAssocSemiring R] (v : V) (vec : V -> R)
  证明: by
  rw [degMatrix]; rw [mulVec_diagonal]

Depends on / 依赖: degMatrix, mulVec_diagonal
-/
theorem degMatrix_mulVec_apply [NonAssocSemiring R] (v : V) (vec : V -> R) :
    (G.degMatrix R *ᵥ vec) v = G.degree v * vec v := by
  rw [degMatrix]; rw [mulVec_diagonal]

/--
theorem `lapMatrix_mulVec_apply` / 定理 `lapMatrix_mulVec_apply`

English:
theorem lapMatrix_mulVec_apply
  given: [NonAssocRing R] (v : V) (vec : V -> R)
  proof: by
  simp_rw [lapMatrix, sub_mulVec, Pi.sub_apply, degMatrix_mulVec_apply, adjMatrix_mulVec_apply]

中文:
定理 lapMatrix_mulVec_apply
  条件: [NonAssocRing R] (v : V) (vec : V -> R)
  证明: by
  simp_rw [lapMatrix, sub_mulVec, Pi.sub_apply, degMatrix_mulVec_apply, adjMatrix_mulVec_apply]

Depends on / 依赖: Pi.sub_apply, adjMatrix_mulVec_apply, degMatrix_mulVec_apply, lapMatrix, simp_rw, sub_apply, sub_mulVec
-/
theorem lapMatrix_mulVec_apply [NonAssocRing R] (v : V) (vec : V -> R) :
    (G.lapMatrix R *ᵥ vec) v = G.degree v * vec v - ∑ u in G.neighborFinset v, vec u := by
  simp_rw [lapMatrix, sub_mulVec, Pi.sub_apply, degMatrix_mulVec_apply, adjMatrix_mulVec_apply]

/--
theorem `lapMatrix_mulVec_const_eq_zero` / 定理 `lapMatrix_mulVec_const_eq_zero`

English:
theorem lapMatrix_mulVec_const_eq_zero
  given: [NonAssocRing R]
  proof: by
  ext1 i
  rw [lapMatrix_mulVec_apply]
  simp

中文:
定理 lapMatrix_mulVec_const_eq_zero
  条件: [NonAssocRing R]
  证明: by
  ext1 i
  rw [lapMatrix_mulVec_apply]
  simp

Depends on / 依赖: lapMatrix_mulVec_apply
-/
theorem lapMatrix_mulVec_const_eq_zero [NonAssocRing R] :
    mulVec (G.lapMatrix R) (fun _ => 1) = 0 := by
  ext1 i
  rw [lapMatrix_mulVec_apply]
  simp

/--
theorem `dotProduct_mulVec_degMatrix` / 定理 `dotProduct_mulVec_degMatrix`

English:
theorem dotProduct_mulVec_degMatrix
  given: [CommSemiring R] (x : V -> R)
  proof: by
  simp only [dotProduct, degMatrix, mulVec_diagonal, ← mul_assoc, mul_comm]

中文:
定理 dotProduct_mulVec_degMatrix
  条件: [CommSemiring R] (x : V -> R)
  证明: by
  simp only [dotProduct, degMatrix, mulVec_diagonal, ← mul_assoc, mul_comm]

Depends on / 依赖: degMatrix, dotProduct, mulVec_diagonal, mul_assoc, mul_comm
-/
theorem dotProduct_mulVec_degMatrix [CommSemiring R] (x : V -> R) :
    x ⬝ᵥ (G.degMatrix R *ᵥ x) = ∑ i : V, G.degree i * x i * x i := by
  simp only [dotProduct, degMatrix, mulVec_diagonal, ← mul_assoc, mul_comm]

variable (R)

/--
theorem `lapMatrix_toLinearMap₂'` / 定理 `lapMatrix_toLinearMap₂'`

English:
theorem lapMatrix_toLinearMap₂'
  given: [Field R] [CharZero R] (x : V -> R)
  proof: by
  simp_rw [toLinearMap₂'_apply', lapMatrix, sub_mulVec, dotProduct_sub, dotProduct_mulVec_degMatrix,
    dotProduct_mulVec_adjMatrix, ← sum_sub_distrib, degree_eq_sum_if_adj, sum_mul, ite_mul, one_mul,
    zero_mul, ← sum_sub_distrib, ite_sub_ite, sub_zero]
  rw [← add_self_div_two (∑ x_1 : V]; r

中文:
定理 lapMatrix_toLinearMap₂'
  条件: [Field R] [CharZero R] (x : V -> R)
  证明: by
  simp_rw [toLinearMap₂'_apply', lapMatrix, sub_mulVec, dotProduct_sub, dotProduct_mulVec_degMatrix,
    dotProduct_mulVec_adjMatrix, ← sum_sub_distrib, degree_eq_sum_if_adj, sum_mul, ite_mul, one_mul,
    zero_mul, ← sum_sub_distrib, ite_sub_ite, sub_zero]
  rw [← add_self_div_two (∑ x_1 : V]; r

Depends on / 依赖: Finset, Finset.sum_comm, _apply, add_self_div_two, adj_comm, conv_lhs, degree_eq_sum_if_adj, dotProduct_mulVec_adjMatrix, dotProduct_mulVec_degMatrix, dotProduct_sub, if_congr, ite_add_ite, ite_mul, ite_sub_ite, lapMatrix, one_mul, simp_rw, sub_mulVec, sub_zero, sum_add_distrib
-/
theorem lapMatrix_toLinearMap₂' [Field R] [CharZero R] (x : V -> R) :
    toLinearMap₂' R (G.lapMatrix R) x x =
    (∑ i : V, ∑ j : V, if G.Adj i j then (x i - x j) ^ 2 else 0) / 2 := by
  simp_rw [toLinearMap₂'_apply', lapMatrix, sub_mulVec, dotProduct_sub, dotProduct_mulVec_degMatrix,
    dotProduct_mulVec_adjMatrix, ← sum_sub_distrib, degree_eq_sum_if_adj, sum_mul, ite_mul, one_mul,
    zero_mul, ← sum_sub_distrib, ite_sub_ite, sub_zero]
  rw [← add_self_div_two (∑ x_1 : V]; rw [∑ x_2 : V]; rw [_)]
  conv_lhs => enter [1, 2, 2, i, 2, j]; rw [if_congr (adj_comm G i j) rfl rfl]
  conv_lhs => enter [1, 2]; rw [Finset.sum_comm]
  simp_rw [← sum_add_distrib, ite_add_ite]
  congr 2 with i
  congr 2 with j
  ring_nf

/--
theorem `posSemidef_lapMatrix` / 定理 `posSemidef_lapMatrix`

English:
theorem posSemidef_lapMatrix
  statement: [Field R] [LinearOrder R] [IsStrictOrderedRing R] [StarRing R]
  proof: by
  refine .of_dotProduct_mulVec_nonneg ?_ (fun x => ?_)
  · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, isSymm_lapMatrix]
  · rw [star_trivial, ← toLinearMap₂'_apply', lapMatrix_toLinearMap₂']
    positivity

中文:
定理 posSemidef_lapMatrix
  结论: [Field R] [LinearOrder R] [IsStrictOrderedRing R] [StarRing R]
  证明: by
  refine .of_dotProduct_mulVec_nonneg ?_ (fun x => ?_)
  · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, isSymm_lapMatrix]
  · rw [star_trivial, ← toLinearMap₂'_apply', lapMatrix_toLinearMap₂']
    positivity

Depends on / 依赖: IsHermitian, _apply, conjTranspose_eq_transpose_of_trivial, isSymm_lapMatrix, of_dotProduct_mulVec_nonneg, star_trivial
-/
theorem posSemidef_lapMatrix [Field R] [LinearOrder R] [IsStrictOrderedRing R] [StarRing R]
    [TrivialStar R] : PosSemidef (G.lapMatrix R) := by
  refine .of_dotProduct_mulVec_nonneg ?_ (fun x => ?_)
  · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, isSymm_lapMatrix]
  · rw [star_trivial, ← toLinearMap₂'_apply', lapMatrix_toLinearMap₂']
    positivity

/--
theorem `lapMatrix_toLinearMap₂'_apply'_eq_zero_iff_forall_adj` / 定理 `lapMatrix_toLinearMap₂'_apply'_eq_zero_iff_forall_adj`

English:
theorem lapMatrix_toLinearMap₂'_apply'_eq_zero_iff_forall_adj
  proof: by
  simp (disch := intros; positivity)
    [lapMatrix_toLinearMap₂', sum_eq_zero_iff_of_nonneg, sub_eq_zero]

中文:
定理 lapMatrix_toLinearMap₂'_apply'_eq_zero_iff_forall_adj
  证明: by
  simp (disch := intros; positivity)
    [lapMatrix_toLinearMap₂', sum_eq_zero_iff_of_nonneg, sub_eq_zero]
-/
theorem lapMatrix_toLinearMap₂'_apply'_eq_zero_iff_forall_adj
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] (x : V -> R) :
    Matrix.toLinearMap₂' R (G.lapMatrix R) x x = 0 ↔ forall i j : V, G.Adj i j -> x i = x j := by
  simp (disch := intros; positivity)
    [lapMatrix_toLinearMap₂', sum_eq_zero_iff_of_nonneg, sub_eq_zero]

/--
theorem `lapMatrix_mulVec_eq_zero_iff_forall_adj` / 定理 `lapMatrix_mulVec_eq_zero_iff_forall_adj`

English:
theorem lapMatrix_mulVec_eq_zero_iff_forall_adj
  given: {x : V -> Real}
  proof: by
  rw [← (posSemidef_lapMatrix Real G).toLinearMap₂'_zero_iff]; rw [star_trivial]; rw [lapMatrix_toLinearMap₂'_apply'_eq_zero_iff_forall_adj]

中文:
定理 lapMatrix_mulVec_eq_zero_iff_forall_adj
  条件: {x : V -> 实数}
  证明: by
  rw [← (posSemidef_lapMatrix Real G).toLinearMap₂'_zero_iff]; rw [star_trivial]; rw [lapMatrix_toLinearMap₂'_apply'_eq_zero_iff_forall_adj]

Depends on / 依赖: _apply, _eq_zero_iff_forall_adj, _zero_iff, posSemidef_lapMatrix, star_trivial
-/
theorem lapMatrix_mulVec_eq_zero_iff_forall_adj {x : V -> Real} :
    G.lapMatrix Real *ᵥ x = 0 ↔ forall i j : V, G.Adj i j -> x i = x j := by
  rw [← (posSemidef_lapMatrix Real G).toLinearMap₂'_zero_iff]; rw [star_trivial]; rw [lapMatrix_toLinearMap₂'_apply'_eq_zero_iff_forall_adj]

/--
theorem `lapMatrix_toLinearMap₂'_apply'_eq_zero_iff_forall_reachable` / 定理 `lapMatrix_toLinearMap₂'_apply'_eq_zero_iff_forall_reachable`

English:
theorem lapMatrix_toLinearMap₂'_apply'_eq_zero_iff_forall_reachable
  given: (x : V -> Real)
  proof: by
  rw [lapMatrix_toLinearMap₂'_apply'_eq_zero_iff_forall_adj]
  refine ⟨?_, fun h i j hA => h i j hA.reachable⟩
  intro h i j ⟨w⟩
  induction w with
  | nil => rfl
  | cons hA _ h' => exact (h _ _ hA).trans h'

中文:
定理 lapMatrix_toLinearMap₂'_apply'_eq_zero_iff_forall_reachable
  条件: (x : V -> 实数)
  证明: by
  rw [lapMatrix_toLinearMap₂'_apply'_eq_zero_iff_forall_adj]
  refine ⟨?_, fun h i j hA => h i j hA.reachable⟩
  intro h i j ⟨w⟩
  induction w with
  | nil => rfl
  | cons hA _ h' => exact (h _ _ hA).trans h'
-/
theorem lapMatrix_toLinearMap₂'_apply'_eq_zero_iff_forall_reachable (x : V -> Real) :
    Matrix.toLinearMap₂' Real (G.lapMatrix Real) x x = 0 ↔
      forall i j : V, G.Reachable i j -> x i = x j := by
  rw [lapMatrix_toLinearMap₂'_apply'_eq_zero_iff_forall_adj]
  refine ⟨?_, fun h i j hA => h i j hA.reachable⟩
  intro h i j ⟨w⟩
  induction w with
  | nil => rfl
  | cons hA _ h' => exact (h _ _ hA).trans h'

/--
theorem `lapMatrix_mulVec_eq_zero_iff_forall_reachable` / 定理 `lapMatrix_mulVec_eq_zero_iff_forall_reachable`

English:
theorem lapMatrix_mulVec_eq_zero_iff_forall_reachable
  given: {x : V -> Real}
  proof: by
  rw [← (posSemidef_lapMatrix Real G).toLinearMap₂'_zero_iff]; rw [star_trivial]; rw [lapMatrix_toLinearMap₂'_apply'_eq_zero_iff_forall_reachable]

@[simp]

中文:
定理 lapMatrix_mulVec_eq_zero_iff_forall_reachable
  条件: {x : V -> 实数}
  证明: by
  rw [← (posSemidef_lapMatrix Real G).toLinearMap₂'_zero_iff]; rw [star_trivial]; rw [lapMatrix_toLinearMap₂'_apply'_eq_zero_iff_forall_reachable]

@[simp]

Depends on / 依赖: _apply, _eq_zero_iff_forall_reachable, _zero_iff, posSemidef_lapMatrix, star_trivial
-/
theorem lapMatrix_mulVec_eq_zero_iff_forall_reachable {x : V -> Real} :
    G.lapMatrix Real *ᵥ x = 0 ↔ forall i j : V, G.Reachable i j -> x i = x j := by
  rw [← (posSemidef_lapMatrix Real G).toLinearMap₂'_zero_iff]; rw [star_trivial]; rw [lapMatrix_toLinearMap₂'_apply'_eq_zero_iff_forall_reachable]

@[simp]
/--
theorem `det_lapMatrix_eq_zero` / 定理 `det_lapMatrix_eq_zero`

English:
theorem det_lapMatrix_eq_zero
  given: [h : Nonempty V]
  statement: (G.lapMatrix Real).det = 0
  proof: by
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  use fun _ => 1
  refine ⟨?_, (lapMatrix_mulVec_eq_zero_iff_forall_adj G).mpr fun _ _ _ => rfl⟩
  rw [← Function.support_nonempty_iff]
  use Classical.choice h
  simp

中文:
定理 det_lapMatrix_eq_zero
  条件: [h : Nonempty V]
  结论: (G.lapMatrix 实数).det = 0
  证明: by
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  use fun _ => 1
  refine ⟨?_, (lapMatrix_mulVec_eq_zero_iff_forall_adj G).mpr fun _ _ _ => rfl⟩
  rw [← Function.support_nonempty_iff]
  use Classical.choice h
  simp

Depends on / 依赖: Classical, Classical.choice, Function, Function.support_nonempty_iff, Matrix, Matrix.exists_mulVec_eq_zero_iff, choice, exists_mulVec_eq_zero_iff, lapMatrix_mulVec_eq_zero_iff_forall_adj, support_nonempty_iff
-/
theorem det_lapMatrix_eq_zero [h : Nonempty V] : (G.lapMatrix Real).det = 0 := by
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  use fun _ => 1
  refine ⟨?_, (lapMatrix_mulVec_eq_zero_iff_forall_adj G).mpr fun _ _ _ => rfl⟩
  rw [← Function.support_nonempty_iff]
  use Classical.choice h
  simp

section

variable [DecidableEq G.ConnectedComponent]

/--
lemma `mem_ker_toLin'_lapMatrix_of_connectedComponent` / 引理 `mem_ker_toLin'_lapMatrix_of_connectedComponent`

English:
lemma mem_ker_toLin'_lapMatrix_of_connectedComponent
  statement: {G : SimpleGraph V} [DecidableRel G.Adj]
  proof: by
  rw [LinearMap.mem_ker]; rw [toLin'_apply]; rw [lapMatrix_mulVec_eq_zero_iff_forall_reachable]
  grind [ConnectedComponent.eq]

中文:
引理 mem_ker_toLin'_lapMatrix_of_connectedComponent
  结论: {G : SimpleGraph V} [DecidableRel G.Adj]
  证明: by
  rw [LinearMap.mem_ker]; rw [toLin'_apply]; rw [lapMatrix_mulVec_eq_zero_iff_forall_reachable]
  grind [ConnectedComponent.eq]

Depends on / 依赖: ConnectedComponent, ConnectedComponent.eq, LinearMap, LinearMap.mem_ker, _apply, lapMatrix_mulVec_eq_zero_iff_forall_reachable, mem_ker
-/
lemma mem_ker_toLin'_lapMatrix_of_connectedComponent {G : SimpleGraph V} [DecidableRel G.Adj]
    [DecidableEq G.ConnectedComponent] (c : G.ConnectedComponent) :
    (fun i => if connectedComponentMk G i = c then 1 else 0) in
      LinearMap.ker (toLin' (lapMatrix Real G)) := by
  rw [LinearMap.mem_ker]; rw [toLin'_apply]; rw [lapMatrix_mulVec_eq_zero_iff_forall_reachable]
  grind [ConnectedComponent.eq]

/--
Definition of `lapMatrix_ker_basis_aux` / `lapMatrix_ker_basis_aux` 的定义

English:
definition lapMatrix_ker_basis_aux
  signature: (c : G.ConnectedComponent)
  body: ⟨fun i => if G.connectedComponentMk i = c then (1 : Real) else 0,
    mem_ker_toLin'_lapMatrix_of_connectedComponent c⟩

中文:
定义 lapMatrix_ker_basis_aux
  签名: (c : G.ConnectedComponent)
  定义体: ⟨fun i => if G.connectedComponentMk i = c then (1 : Real) else 0,
    mem_ker_toLin'_lapMatrix_of_connectedComponent c⟩

Depends on / 依赖: G.connectedComponentMk, _lapMatrix_of_connectedComponent, connectedComponentMk, mem_ker_toLin
-/
def lapMatrix_ker_basis_aux (c : G.ConnectedComponent) :
    LinearMap.ker (Matrix.toLin' (G.lapMatrix Real)) :=
  ⟨fun i => if G.connectedComponentMk i = c then (1 : Real) else 0,
    mem_ker_toLin'_lapMatrix_of_connectedComponent c⟩

/--
lemma `linearIndependent_lapMatrix_ker_basis_aux` / 引理 `linearIndependent_lapMatrix_ker_basis_aux`

English:
lemma linearIndependent_lapMatrix_ker_basis_aux
  proof: by
  rw [Fintype.linearIndependent_iff]
  intro g h0
  rw [Subtype.ext_iff] at h0
  have h : ∑ c, g c • lapMatrix_ker_basis_aux G c = fun i => g (connectedComponentMk G i) := by
    simp only [lapMatrix_ker_basis_aux, SetLike.mk_smul_mk]
    repeat rw [AddSubmonoid.coe_finsetSum]
    ext i
    simp 

中文:
引理 linearIndependent_lapMatrix_ker_basis_aux
  证明: by
  rw [Fintype.linearIndependent_iff]
  intro g h0
  rw [Subtype.ext_iff] at h0
  have h : ∑ c, g c • lapMatrix_ker_basis_aux G c = fun i => g (connectedComponentMk G i) := by
    simp only [lapMatrix_ker_basis_aux, SetLike.mk_smul_mk]
    repeat rw [AddSubmonoid.coe_finsetSum]
    ext i
    simp 

Depends on / 依赖: AddSubmonoid, AddSubmonoid.coe_finsetSum, Finset, Finset.sum_apply, Fintype, Fintype.linearIndependent_iff, G.connectedComponentMk, Pi.smul_apply, Quot.exists_rep, SetLike, SetLike.mk_smul_mk, Subtype, Subtype.ext_iff, coe_finsetSum, connectedComponentMk, exists_rep, ext_iff, lapMatrix_ker_basis_aux, linearIndependent_iff, mem_univ
-/
lemma linearIndependent_lapMatrix_ker_basis_aux :
    LinearIndependent Real (lapMatrix_ker_basis_aux G) := by
  rw [Fintype.linearIndependent_iff]
  intro g h0
  rw [Subtype.ext_iff] at h0
  have h : ∑ c, g c • lapMatrix_ker_basis_aux G c = fun i => g (connectedComponentMk G i) := by
    simp only [lapMatrix_ker_basis_aux, SetLike.mk_smul_mk]
    repeat rw [AddSubmonoid.coe_finsetSum]
    ext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, sum_ite_eq,
      mem_univ, ↓reduceIte]
  rw [h] at h0
  intro c
  obtain ⟨i, h'⟩ : exists i : V, G.connectedComponentMk i = c := Quot.exists_rep c
  exact h' ▸ congrFun h0 i

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `top_le_span_range_lapMatrix_ker_basis_aux` / 引理 `top_le_span_range_lapMatrix_ker_basis_aux`

English:
lemma top_le_span_range_lapMatrix_ker_basis_aux
  proof: by
  intro x _
  rw [Submodule.mem_span_range_iff_exists_fun]
  use Quot.lift x.val (by rw [← lapMatrix_mulVec_eq_zero_iff_forall_reachable,
    ← toLin'_apply, LinearMap.map_coe_ker])
  ext j
  simp only [lapMatrix_ker_basis_aux]
  rw [AddSubmonoid.coe_finsetSum]
  simp only [SetLike.mk_smul_mk, Fi

中文:
引理 top_le_span_range_lapMatrix_ker_basis_aux
  证明: by
  intro x _
  rw [Submodule.mem_span_range_iff_exists_fun]
  use Quot.lift x.val (by rw [← lapMatrix_mulVec_eq_zero_iff_forall_reachable,
    ← toLin'_apply, LinearMap.map_coe_ker])
  ext j
  simp only [lapMatrix_ker_basis_aux]
  rw [AddSubmonoid.coe_finsetSum]
  simp only [SetLike.mk_smul_mk, Fi

Depends on / 依赖: AddSubmonoid, AddSubmonoid.coe_finsetSum, Finset, Finset.sum_apply, LinearMap, LinearMap.map_coe_ker, Pi.smul_apply, Quot.lift, SetLike, SetLike.mk_smul_mk, Submodule, Submodule.mem_span_range_iff_exists_fun, _apply, coe_finsetSum, lapMatrix_ker_basis_aux, lapMatrix_mulVec_eq_zero_iff_forall_reachable, map_coe_ker, mem_span_range_iff_exists_fun, mem_univ, mk_smul_mk
-/
lemma top_le_span_range_lapMatrix_ker_basis_aux :
    ⊤ <= Submodule.span Real (Set.range (lapMatrix_ker_basis_aux G)) := by
  intro x _
  rw [Submodule.mem_span_range_iff_exists_fun]
  use Quot.lift x.val (by rw [← lapMatrix_mulVec_eq_zero_iff_forall_reachable,
    ← toLin'_apply, LinearMap.map_coe_ker])
  ext j
  simp only [lapMatrix_ker_basis_aux]
  rw [AddSubmonoid.coe_finsetSum]
  simp only [SetLike.mk_smul_mk, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero, sum_ite_eq, mem_univ, ↓reduceIte]
  rfl

/--
Definition of `lapMatrix_ker_basis` / `lapMatrix_ker_basis` 的定义

English:
definition lapMatrix_ker_basis
  body: Basis.mk G.linearIndependent_lapMatrix_ker_basis_aux G.top_le_span_range_lapMatrix_ker_basis_aux

中文:
定义 lapMatrix_ker_basis
  定义体: Basis.mk G.linearIndependent_lapMatrix_ker_basis_aux G.top_le_span_range_lapMatrix_ker_basis_aux

Depends on / 依赖: Basis.mk, G.linearIndependent_lapMatrix_ker_basis_aux, G.top_le_span_range_lapMatrix_ker_basis_aux, linearIndependent_lapMatrix_ker_basis_aux, top_le_span_range_lapMatrix_ker_basis_aux
-/
noncomputable def lapMatrix_ker_basis :=
  Basis.mk G.linearIndependent_lapMatrix_ker_basis_aux G.top_le_span_range_lapMatrix_ker_basis_aux

end

/--
theorem `card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix` / 定理 `card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix`

English:
theorem card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix
  proof: by
  classical
  rw [Module.finrank_eq_card_basis G.lapMatrix_ker_basis]

中文:
定理 card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix
  证明: by
  classical
  rw [Module.finrank_eq_card_basis G.lapMatrix_ker_basis]

Depends on / 依赖: G.lapMatrix_ker_basis, Module, Module.finrank_eq_card_basis, classical, finrank_eq_card_basis, lapMatrix_ker_basis
-/
theorem card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix :
    Fintype.card G.ConnectedComponent = Module.finrank Real (G.lapMatrix Real).toLin'.ker := by
  classical
  rw [Module.finrank_eq_card_basis G.lapMatrix_ker_basis]

end SimpleGraph
