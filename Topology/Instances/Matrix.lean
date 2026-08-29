/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Star

/-!
# Topological properties of matrices

This file is a place to collect topological results about matrices.

## Main definitions:

* `Matrix.topologicalRing`: square matrices form a topological ring

## Main results

* Sets of matrices:
  * `IsOpen.matrix`: the set of finite matrices with entries in an open set
    is itself an open set.
  * `IsCompact.matrix`: the set of matrices with entries in a compact set
    is itself a compact set.
* Continuity:
  * `Continuous.matrix_det`: the determinant is continuous over a topological ring.
  * `Continuous.matrix_adjugate`: the adjugate is continuous over a topological ring.
* Infinite sums
  * `Matrix.transpose_tsum`: transpose commutes with infinite sums
  * `Matrix.diagonal_tsum`: diagonal commutes with infinite sums
  * `Matrix.blockDiagonal_tsum`: block diagonal commutes with infinite sums
  * `Matrix.blockDiagonal'_tsum`: non-uniform block diagonal commutes with infinite sums
-/

public section

assert_not_exists Matrix.GeneralLinearGroup Matrix.SpecialLinearGroup -- guard against import creep

open Matrix

variable {X α l m n p S R : Type*} {m' n' : l -> Type*}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [TopologicalSpace
  signature: R] : TopologicalSpace (Matrix m n R)
  body: inferInstanceAs TopologicalSpace (m -> n -> R)

中文:
实例 [TopologicalSpace
  签名: R] : TopologicalSpace (Matrix m n R)
  定义体: inferInstanceAs TopologicalSpace (m -> n -> R)

Depends on / 依赖: TopologicalSpace
-/
instance [TopologicalSpace R] : TopologicalSpace (Matrix m n R) :=
inferInstanceAs TopologicalSpace (m -> n -> R)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [TopologicalSpace
  signature: R] [T2Space R] : T2Space (Matrix m n R)
  body: inferInstanceAs T2Space (m -> n -> R)

中文:
实例 [TopologicalSpace
  签名: R] [T2Space R] : T2Space (Matrix m n R)
  定义体: inferInstanceAs T2Space (m -> n -> R)

Depends on / 依赖: T2Space
-/
instance [TopologicalSpace R] [T2Space R] : T2Space (Matrix m n R) :=
inferInstanceAs T2Space (m -> n -> R)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [TopologicalSpace
  signature: R] [Finite m] [Finite n] [DiscreteTopology R] :
  body: inferInstanceAs DiscreteTopology (m -> n -> R)

中文:
实例 [TopologicalSpace
  签名: R] [Finite m] [Finite n] [DiscreteTopology R] :
  定义体: inferInstanceAs DiscreteTopology (m -> n -> R)

Depends on / 依赖: DiscreteTopology
-/
instance [TopologicalSpace R] [Finite m] [Finite n] [DiscreteTopology R] :
    DiscreteTopology (Matrix m n R) :=
inferInstanceAs DiscreteTopology (m -> n -> R)

section Set

/--
theorem `IsOpen.matrix` / 定理 `IsOpen.matrix`

English:
theorem IsOpen.matrix
  statement: [Finite m] [Finite n]
  proof: Set.matrix_eq_pi ▸
    (isOpen_set_pi Set.finite_univ fun _ _ =>
    isOpen_set_pi Set.finite_univ fun _ _ => hS).preimage continuous_id

中文:
定理 IsOpen.matrix
  结论: [Finite m] [Finite n]
  证明: Set.matrix_eq_pi ▸
    (isOpen_set_pi Set.finite_univ fun _ _ =>
    isOpen_set_pi Set.finite_univ fun _ _ => hS).preimage continuous_id

Depends on / 依赖: Set.finite_univ, Set.matrix_eq_pi, continuous_id, finite_univ, isOpen_set_pi, matrix_eq_pi, preimage
-/
theorem IsOpen.matrix [Finite m] [Finite n]
    [TopologicalSpace R] {S : Set R} (hS : IsOpen S) :
    IsOpen (S.matrix : Set (Matrix m n R)) :=
  Set.matrix_eq_pi ▸
    (isOpen_set_pi Set.finite_univ fun _ _ =>
    isOpen_set_pi Set.finite_univ fun _ _ => hS).preimage continuous_id

/--
theorem `IsCompact.matrix` / 定理 `IsCompact.matrix`

English:
theorem IsCompact.matrix
  given: [TopologicalSpace R] {S : Set R} (hS : IsCompact S)
  proof: isCompact_pi_infinite fun _ => isCompact_pi_infinite fun _ => hS

中文:
定理 IsCompact.matrix
  条件: [TopologicalSpace R] {S : Set R} (hS : IsCompact S)
  证明: isCompact_pi_infinite fun _ => isCompact_pi_infinite fun _ => hS

Depends on / 依赖: isCompact_pi_infinite
-/
theorem IsCompact.matrix [TopologicalSpace R] {S : Set R} (hS : IsCompact S) :
    IsCompact (S.matrix : Set (Matrix m n R)) :=
  isCompact_pi_infinite fun _ => isCompact_pi_infinite fun _ => hS

end Set

/-! ### Lemmas about continuity of operations -/

section Continuity

variable [TopologicalSpace X] [TopologicalSpace R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: α R] [ContinuousConstSMul α R] : ContinuousConstSMul α (Matrix m n R)
  body: inferInstanceAs (ContinuousConstSMul α (m -> n -> R))

中文:
实例 [SMul
  签名: α R] [ContinuousConstSMul α R] : ContinuousConstSMul α (Matrix m n R)
  定义体: inferInstanceAs (ContinuousConstSMul α (m -> n -> R))

Depends on / 依赖: ContinuousConstSMul
-/
instance [SMul α R] [ContinuousConstSMul α R] : ContinuousConstSMul α (Matrix m n R) :=
  inferInstanceAs (ContinuousConstSMul α (m -> n -> R))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [TopologicalSpace
  signature: α] [SMul α R] [ContinuousSMul α R] : ContinuousSMul α (Matrix m n R)
  body: inferInstanceAs (ContinuousSMul α (m -> n -> R))

中文:
实例 [TopologicalSpace
  签名: α] [SMul α R] [ContinuousSMul α R] : ContinuousSMul α (Matrix m n R)
  定义体: inferInstanceAs (ContinuousSMul α (m -> n -> R))

Depends on / 依赖: ContinuousSMul
-/
instance [TopologicalSpace α] [SMul α R] [ContinuousSMul α R] : ContinuousSMul α (Matrix m n R) :=
  inferInstanceAs (ContinuousSMul α (m -> n -> R))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Add
  signature: R] [ContinuousAdd R] : ContinuousAdd (Matrix m n R)
  body: Pi.continuousAdd

中文:
实例 [Add
  签名: R] [ContinuousAdd R] : ContinuousAdd (Matrix m n R)
  定义体: Pi.continuousAdd

Depends on / 依赖: Pi.continuousAdd, continuousAdd
-/
instance [Add R] [ContinuousAdd R] : ContinuousAdd (Matrix m n R) :=
  Pi.continuousAdd

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Neg
  signature: R] [ContinuousNeg R] : ContinuousNeg (Matrix m n R)
  body: Pi.continuousNeg

中文:
实例 [Neg
  签名: R] [ContinuousNeg R] : ContinuousNeg (Matrix m n R)
  定义体: Pi.continuousNeg

Depends on / 依赖: Pi.continuousNeg, continuousNeg
-/
instance [Neg R] [ContinuousNeg R] : ContinuousNeg (Matrix m n R) :=
  Pi.continuousNeg

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddGroup
  signature: R] [IsTopologicalAddGroup R] : IsTopologicalAddGroup (Matrix m n R)
  body: Pi.topologicalAddGroup

中文:
实例 [AddGroup
  签名: R] [IsTopologicalAddGroup R] : IsTopologicalAddGroup (Matrix m n R)
  定义体: Pi.topologicalAddGroup

Depends on / 依赖: Pi.topologicalAddGroup, topologicalAddGroup
-/
instance [AddGroup R] [IsTopologicalAddGroup R] : IsTopologicalAddGroup (Matrix m n R) :=
  Pi.topologicalAddGroup

/-- To show a function into matrices is continuous it suffices to show the coefficients of the
resulting matrix are continuous -/
@[continuity]
/--
theorem `continuous_matrix` / 定理 `continuous_matrix`

English:
theorem continuous_matrix
  statement: [TopologicalSpace α] {f : α -> Matrix m n R}
  proof: continuous_pi fun _ => continuous_pi fun _ => h _ _

中文:
定理 continuous_matrix
  结论: [TopologicalSpace α] {f : α -> Matrix m n R}
  证明: continuous_pi fun _ => continuous_pi fun _ => h _ _

Depends on / 依赖: continuous_pi
-/
theorem continuous_matrix [TopologicalSpace α] {f : α -> Matrix m n R}
    (h : forall i j, Continuous fun a => f a i j) : Continuous f :=
  continuous_pi fun _ => continuous_pi fun _ => h _ _

/--
theorem `Continuous.matrix_elem` / 定理 `Continuous.matrix_elem`

English:
theorem Continuous.matrix_elem
  given: {A : X -> Matrix m n R} (hA : Continuous A) (i : m) (j : n)
  proof: (continuous_apply_apply i j).comp hA

中文:
定理 Continuous.matrix_elem
  条件: {A : X -> Matrix m n R} (hA : Continuous A) (i : m) (j : n)
  证明: (continuous_apply_apply i j).comp hA

Depends on / 依赖: continuous_apply_apply
-/
theorem Continuous.matrix_elem {A : X -> Matrix m n R} (hA : Continuous A) (i : m) (j : n) :
    Continuous fun x => A x i j :=
  (continuous_apply_apply i j).comp hA

/--
lemma `continuous_matrixOf` / 引理 `continuous_matrixOf`

English:
lemma continuous_matrixOf
  given: [TopologicalSpace α] {f : α -> m -> n -> R}
  proof: by
  rfl

@[fun_prop]
alias ⟨_, Continuous.matrixOf⟩ := continuous_matrixOf

@[continuity, fun_prop]

中文:
引理 continuous_matrixOf
  条件: [TopologicalSpace α] {f : α -> m -> n -> R}
  证明: by
  rfl

@[fun_prop]
alias ⟨_, Continuous.matrixOf⟩ := continuous_matrixOf

@[continuity, fun_prop]
-/
lemma continuous_matrixOf [TopologicalSpace α] {f : α -> m -> n -> R} :
    Continuous (fun x => Matrix.of (f x)) ↔ Continuous f := by
  rfl

@[fun_prop]
alias ⟨_, Continuous.matrixOf⟩ := continuous_matrixOf

@[continuity, fun_prop]
/--
theorem `Continuous.matrix_map` / 定理 `Continuous.matrix_map`

English:
theorem Continuous.matrix_map
  statement: [TopologicalSpace S] {A : X -> Matrix m n S} {f : S -> R}
  proof: continuous_matrix fun _ _ => hf.comp hA.matrix_elem _ _

@[continuity, fun_prop]

中文:
定理 Continuous.matrix_map
  结论: [TopologicalSpace S] {A : X -> Matrix m n S} {f : S -> R}
  证明: continuous_matrix fun _ _ => hf.comp hA.matrix_elem _ _

@[continuity, fun_prop]

Depends on / 依赖: continuous_matrix, hA.matrix_elem, hf.comp, matrix_elem
-/
theorem Continuous.matrix_map [TopologicalSpace S] {A : X -> Matrix m n S} {f : S -> R}
    (hA : Continuous A) (hf : Continuous f) : Continuous fun x => (A x).map f :=
continuous_matrix fun _ _ => hf.comp hA.matrix_elem _ _

@[continuity, fun_prop]
/--
theorem `Continuous.matrix_transpose` / 定理 `Continuous.matrix_transpose`

English:
theorem Continuous.matrix_transpose
  given: {A : X -> Matrix m n R} (hA : Continuous A)
  proof: continuous_matrix fun i j => hA.matrix_elem j i

@[continuity, fun_prop]

中文:
定理 Continuous.matrix_transpose
  条件: {A : X -> Matrix m n R} (hA : Continuous A)
  证明: continuous_matrix fun i j => hA.matrix_elem j i

@[continuity, fun_prop]

Depends on / 依赖: continuous_matrix, hA.matrix_elem, matrix_elem
-/
theorem Continuous.matrix_transpose {A : X -> Matrix m n R} (hA : Continuous A) :
    Continuous fun x => (A x)ᵀ :=
  continuous_matrix fun i j => hA.matrix_elem j i

@[continuity, fun_prop]
/--
theorem `Continuous.matrix_conjTranspose` / 定理 `Continuous.matrix_conjTranspose`

English:
theorem Continuous.matrix_conjTranspose
  statement: [Star R] [ContinuousStar R] {A : X -> Matrix m n R}
  proof: hA.matrix_transpose.matrix_map continuous_star

中文:
定理 Continuous.matrix_conjTranspose
  结论: [Star R] [ContinuousStar R] {A : X -> Matrix m n R}
  证明: hA.matrix_transpose.matrix_map continuous_star

Depends on / 依赖: continuous_star, hA.matrix_transpose.matrix_map, matrix_map, matrix_transpose
-/
theorem Continuous.matrix_conjTranspose [Star R] [ContinuousStar R] {A : X -> Matrix m n R}
    (hA : Continuous A) : Continuous fun x => (A x)ᴴ :=
  hA.matrix_transpose.matrix_map continuous_star

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Star
  signature: R] [ContinuousStar R] : ContinuousStar (Matrix m m R)
  body: ⟨continuous_id.matrix_conjTranspose⟩

@[continuity, fun_prop]

中文:
实例 [Star
  签名: R] [ContinuousStar R] : ContinuousStar (Matrix m m R)
  定义体: ⟨continuous_id.matrix_conjTranspose⟩

@[continuity, fun_prop]

Depends on / 依赖: continuous_id, continuous_id.matrix_conjTranspose, matrix_conjTranspose
-/
instance [Star R] [ContinuousStar R] : ContinuousStar (Matrix m m R) :=
  ⟨continuous_id.matrix_conjTranspose⟩

@[continuity, fun_prop]
/--
theorem `Continuous.matrix_replicateCol` / 定理 `Continuous.matrix_replicateCol`

English:
theorem Continuous.matrix_replicateCol
  given: {ι : Type*} {A : X -> n -> R} (hA : Continuous A)
  proof: continuous_matrix fun i _ => (continuous_apply i).comp hA

@[continuity, fun_prop]

中文:
定理 Continuous.matrix_replicateCol
  条件: {ι : 类型} {A : X -> n -> R} (hA : Continuous A)
  证明: continuous_matrix fun i _ => (continuous_apply i).comp hA

@[continuity, fun_prop]

Depends on / 依赖: continuous_apply, continuous_matrix
-/
theorem Continuous.matrix_replicateCol {ι : Type*} {A : X -> n -> R} (hA : Continuous A) :
    Continuous fun x => replicateCol ι (A x) :=
  continuous_matrix fun i _ => (continuous_apply i).comp hA

@[continuity, fun_prop]
/--
theorem `Continuous.matrix_replicateRow` / 定理 `Continuous.matrix_replicateRow`

English:
theorem Continuous.matrix_replicateRow
  given: {ι : Type*} {A : X -> n -> R} (hA : Continuous A)
  proof: continuous_matrix fun _ _ => (continuous_apply _).comp hA

@[continuity, fun_prop]

中文:
定理 Continuous.matrix_replicateRow
  条件: {ι : 类型} {A : X -> n -> R} (hA : Continuous A)
  证明: continuous_matrix fun _ _ => (continuous_apply _).comp hA

@[continuity, fun_prop]

Depends on / 依赖: continuous_apply, continuous_matrix
-/
theorem Continuous.matrix_replicateRow {ι : Type*} {A : X -> n -> R} (hA : Continuous A) :
    Continuous fun x => replicateRow ι (A x) :=
  continuous_matrix fun _ _ => (continuous_apply _).comp hA

@[continuity, fun_prop]
/--
theorem `Continuous.matrix_diagonal` / 定理 `Continuous.matrix_diagonal`

English:
theorem Continuous.matrix_diagonal
  given: [Zero R] [DecidableEq n] {A : X -> n -> R} (hA : Continuous A)
  proof: continuous_matrix fun i _ => ((continuous_apply i).comp hA).if_const _ continuous_zero

@[continuity, fun_prop]

中文:
定理 Continuous.matrix_diagonal
  条件: [Zero R] [DecidableEq n] {A : X -> n -> R} (hA : Continuous A)
  证明: continuous_matrix fun i _ => ((continuous_apply i).comp hA).if_const _ continuous_zero

@[continuity, fun_prop]

Depends on / 依赖: continuous_apply, continuous_matrix, continuous_zero, if_const
-/
theorem Continuous.matrix_diagonal [Zero R] [DecidableEq n] {A : X -> n -> R} (hA : Continuous A) :
    Continuous fun x => diagonal (A x) :=
  continuous_matrix fun i _ => ((continuous_apply i).comp hA).if_const _ continuous_zero

@[continuity, fun_prop]
/--
theorem `Continuous.dotProduct` / 定理 `Continuous.dotProduct`

English:
theorem Continuous.dotProduct
  statement: [Fintype n] [Mul R] [AddCommMonoid R] [ContinuousAdd R]
  proof: by
  dsimp only [dotProduct]
  fun_prop

中文:
定理 Continuous.dotProduct
  结论: [Fintype n] [Mul R] [AddCommMonoid R] [ContinuousAdd R]
  证明: by
  dsimp only [dotProduct]
  fun_prop
-/
protected theorem Continuous.dotProduct [Fintype n] [Mul R] [AddCommMonoid R] [ContinuousAdd R]
    [ContinuousMul R] {A : X -> n -> R} {B : X -> n -> R} (hA : Continuous A) (hB : Continuous B) :
    Continuous fun x => A x ⬝ᵥ B x := by
  dsimp only [dotProduct]
  fun_prop

/-- For square matrices the usual `continuous_mul` can be used. -/
@[continuity, fun_prop]
/--
theorem `Continuous.matrix_mul` / 定理 `Continuous.matrix_mul`

English:
theorem Continuous.matrix_mul
  statement: [Fintype n] [Mul R] [AddCommMonoid R] [ContinuousAdd R]
  proof: continuous_matrix fun _ _ =>
    continuous_finsetSum _ fun _ _ => (hA.matrix_elem _ _).mul (hB.matrix_elem _ _)

中文:
定理 Continuous.matrix_mul
  结论: [Fintype n] [Mul R] [AddCommMonoid R] [ContinuousAdd R]
  证明: continuous_matrix fun _ _ =>
    continuous_finsetSum _ fun _ _ => (hA.matrix_elem _ _).mul (hB.matrix_elem _ _)

Depends on / 依赖: continuous_finsetSum, continuous_matrix, hA.matrix_elem, hB.matrix_elem, matrix_elem
-/
theorem Continuous.matrix_mul [Fintype n] [Mul R] [AddCommMonoid R] [ContinuousAdd R]
    [ContinuousMul R] {A : X -> Matrix m n R} {B : X -> Matrix n p R} (hA : Continuous A)
    (hB : Continuous B) : Continuous fun x => A x * B x :=
  continuous_matrix fun _ _ =>
    continuous_finsetSum _ fun _ _ => (hA.matrix_elem _ _).mul (hB.matrix_elem _ _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Fintype
  signature: n] [Mul R] [AddCommMonoid R] [ContinuousAdd R] [ContinuousMul R] :
  body: ⟨continuous_fst.matrix_mul continuous_snd⟩

中文:
实例 [Fintype
  签名: n] [Mul R] [AddCommMonoid R] [ContinuousAdd R] [ContinuousMul R] :
  定义体: ⟨continuous_fst.matrix_mul continuous_snd⟩

Depends on / 依赖: continuous_fst, continuous_fst.matrix_mul, continuous_snd, matrix_mul
-/
instance [Fintype n] [Mul R] [AddCommMonoid R] [ContinuousAdd R] [ContinuousMul R] :
    ContinuousMul (Matrix n n R) :=
  ⟨continuous_fst.matrix_mul continuous_snd⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Fintype
  signature: n] [NonUnitalNonAssocSemiring R] [IsTopologicalSemiring R] :

中文:
实例 [Fintype
  签名: n] [NonUnitalNonAssocSemiring R] [IsTopologicalSemiring R] :
-/
instance [Fintype n] [NonUnitalNonAssocSemiring R] [IsTopologicalSemiring R] :
    IsTopologicalSemiring (Matrix n n R) where

/--
Instance `Matrix.topologicalRing` / 实例 `Matrix.topologicalRing`

English:
instance Matrix.topologicalRing
  signature: [Fintype n] [NonUnitalNonAssocRing R] [IsTopologicalRing R]

中文:
实例 Matrix.topologicalRing
  签名: [Fintype n] [NonUnitalNonAssocRing R] [IsTopologicalRing R]
-/
instance Matrix.topologicalRing [Fintype n] [NonUnitalNonAssocRing R] [IsTopologicalRing R] :
    IsTopologicalRing (Matrix n n R) where

@[continuity, fun_prop]
/--
theorem `Continuous.matrix_vecMulVec` / 定理 `Continuous.matrix_vecMulVec`

English:
theorem Continuous.matrix_vecMulVec
  statement: [Mul R] [ContinuousMul R] {A : X -> m -> R} {B : X -> n -> R}
  proof: continuous_matrix fun _ _ => ((continuous_apply _).comp hA).mul ((continuous_apply _).comp hB)

@[continuity, fun_prop]

中文:
定理 Continuous.matrix_vecMulVec
  结论: [Mul R] [ContinuousMul R] {A : X -> m -> R} {B : X -> n -> R}
  证明: continuous_matrix fun _ _ => ((continuous_apply _).comp hA).mul ((continuous_apply _).comp hB)

@[continuity, fun_prop]

Depends on / 依赖: continuous_apply, continuous_matrix
-/
theorem Continuous.matrix_vecMulVec [Mul R] [ContinuousMul R] {A : X -> m -> R} {B : X -> n -> R}
    (hA : Continuous A) (hB : Continuous B) : Continuous fun x => vecMulVec (A x) (B x) :=
  continuous_matrix fun _ _ => ((continuous_apply _).comp hA).mul ((continuous_apply _).comp hB)

@[continuity, fun_prop]
/--
theorem `Continuous.matrix_mulVec` / 定理 `Continuous.matrix_mulVec`

English:
theorem Continuous.matrix_mulVec
  statement: [NonUnitalNonAssocSemiring R] [ContinuousAdd R] [ContinuousMul R]
  proof: continuous_pi fun i => ((continuous_apply i).comp hA).dotProduct hB

@[continuity, fun_prop]

中文:
定理 Continuous.matrix_mulVec
  结论: [NonUnitalNonAssocSemiring R] [ContinuousAdd R] [ContinuousMul R]
  证明: continuous_pi fun i => ((continuous_apply i).comp hA).dotProduct hB

@[continuity, fun_prop]

Depends on / 依赖: continuous_apply, continuous_pi, dotProduct
-/
theorem Continuous.matrix_mulVec [NonUnitalNonAssocSemiring R] [ContinuousAdd R] [ContinuousMul R]
    [Fintype n] {A : X -> Matrix m n R} {B : X -> n -> R} (hA : Continuous A) (hB : Continuous B) :
    Continuous fun x => A x *ᵥ B x :=
  continuous_pi fun i => ((continuous_apply i).comp hA).dotProduct hB

@[continuity, fun_prop]
/--
theorem `Continuous.matrix_vecMul` / 定理 `Continuous.matrix_vecMul`

English:
theorem Continuous.matrix_vecMul
  statement: [NonUnitalNonAssocSemiring R] [ContinuousAdd R] [ContinuousMul R]
  proof: continuous_pi fun _i => hA.dotProduct continuous_pi fun _j => hB.matrix_elem _ _

@[continuity, fun_prop]

中文:
定理 Continuous.matrix_vecMul
  结论: [NonUnitalNonAssocSemiring R] [ContinuousAdd R] [ContinuousMul R]
  证明: continuous_pi fun _i => hA.dotProduct continuous_pi fun _j => hB.matrix_elem _ _

@[continuity, fun_prop]

Depends on / 依赖: continuous_pi, dotProduct, hA.dotProduct, hB.matrix_elem, matrix_elem
-/
theorem Continuous.matrix_vecMul [NonUnitalNonAssocSemiring R] [ContinuousAdd R] [ContinuousMul R]
    [Fintype m] {A : X -> m -> R} {B : X -> Matrix m n R} (hA : Continuous A) (hB : Continuous B) :
    Continuous fun x => A x ᵥ* B x :=
continuous_pi fun _i => hA.dotProduct continuous_pi fun _j => hB.matrix_elem _ _

@[continuity, fun_prop]
/--
theorem `Continuous.matrix_submatrix` / 定理 `Continuous.matrix_submatrix`

English:
theorem Continuous.matrix_submatrix
  statement: {A : X -> Matrix l n R} (hA : Continuous A) (e₁ : m -> l)
  proof: continuous_matrix fun _i _j => hA.matrix_elem _ _

@[continuity, fun_prop]

中文:
定理 Continuous.matrix_submatrix
  结论: {A : X -> Matrix l n R} (hA : Continuous A) (e₁ : m -> l)
  证明: continuous_matrix fun _i _j => hA.matrix_elem _ _

@[continuity, fun_prop]

Depends on / 依赖: continuous_matrix, hA.matrix_elem, matrix_elem
-/
theorem Continuous.matrix_submatrix {A : X -> Matrix l n R} (hA : Continuous A) (e₁ : m -> l)
    (e₂ : p -> n) : Continuous fun x => (A x).submatrix e₁ e₂ :=
  continuous_matrix fun _i _j => hA.matrix_elem _ _

@[continuity, fun_prop]
/--
theorem `Continuous.matrix_reindex` / 定理 `Continuous.matrix_reindex`

English:
theorem Continuous.matrix_reindex
  statement: {A : X -> Matrix l n R} (hA : Continuous A) (e₁ : l ≃ m)
  proof: hA.matrix_submatrix _ _

@[continuity, fun_prop]

中文:
定理 Continuous.matrix_reindex
  结论: {A : X -> Matrix l n R} (hA : Continuous A) (e₁ : l ≃ m)
  证明: hA.matrix_submatrix _ _

@[continuity, fun_prop]

Depends on / 依赖: hA.matrix_submatrix, matrix_submatrix
-/
theorem Continuous.matrix_reindex {A : X -> Matrix l n R} (hA : Continuous A) (e₁ : l ≃ m)
    (e₂ : n ≃ p) : Continuous fun x => reindex e₁ e₂ (A x) :=
  hA.matrix_submatrix _ _

@[continuity, fun_prop]
/--
theorem `Continuous.matrix_diag` / 定理 `Continuous.matrix_diag`

English:
theorem Continuous.matrix_diag
  given: {A : X -> Matrix n n R} (hA : Continuous A)
  proof: continuous_pi fun _ => hA.matrix_elem _ _

中文:
定理 Continuous.matrix_diag
  条件: {A : X -> Matrix n n R} (hA : Continuous A)
  证明: continuous_pi fun _ => hA.matrix_elem _ _

Depends on / 依赖: continuous_pi, hA.matrix_elem, matrix_elem
-/
theorem Continuous.matrix_diag {A : X -> Matrix n n R} (hA : Continuous A) :
    Continuous fun x => Matrix.diag (A x) :=
  continuous_pi fun _ => hA.matrix_elem _ _

-- note this doesn't elaborate well from the above
/--
theorem `continuous_matrix_diag` / 定理 `continuous_matrix_diag`

English:
theorem continuous_matrix_diag
  statement: Continuous (Matrix.diag : Matrix n n R -> n -> R)
  proof: show Continuous fun x : Matrix n n R => Matrix.diag x from continuous_id.matrix_diag

@[continuity, fun_prop]

中文:
定理 continuous_matrix_diag
  结论: Continuous (Matrix.diag : Matrix n n R -> n -> R)
  证明: show Continuous fun x : Matrix n n R => Matrix.diag x from continuous_id.matrix_diag

@[continuity, fun_prop]

Depends on / 依赖: Continuous, Matrix, Matrix.diag, continuous_id, continuous_id.matrix_diag, matrix_diag
-/
theorem continuous_matrix_diag : Continuous (Matrix.diag : Matrix n n R -> n -> R) :=
  show Continuous fun x : Matrix n n R => Matrix.diag x from continuous_id.matrix_diag

@[continuity, fun_prop]
/--
theorem `Continuous.matrix_trace` / 定理 `Continuous.matrix_trace`

English:
theorem Continuous.matrix_trace
  statement: [Fintype n] [AddCommMonoid R] [ContinuousAdd R]
  proof: continuous_finsetSum _ fun _ _ => hA.matrix_elem _ _

@[continuity, fun_prop]

中文:
定理 Continuous.matrix_trace
  结论: [Fintype n] [AddCommMonoid R] [ContinuousAdd R]
  证明: continuous_finsetSum _ fun _ _ => hA.matrix_elem _ _

@[continuity, fun_prop]

Depends on / 依赖: continuous_finsetSum, hA.matrix_elem, matrix_elem
-/
theorem Continuous.matrix_trace [Fintype n] [AddCommMonoid R] [ContinuousAdd R]
    {A : X -> Matrix n n R} (hA : Continuous A) : Continuous fun x => trace (A x) :=
  continuous_finsetSum _ fun _ _ => hA.matrix_elem _ _

@[continuity, fun_prop]
/--
theorem `Continuous.matrix_det` / 定理 `Continuous.matrix_det`

English:
theorem Continuous.matrix_det
  statement: [Fintype n] [DecidableEq n] [CommRing R] [IsTopologicalRing R]
  proof: by
  simp_rw [Matrix.det_apply]
  refine continuous_finsetSum _ fun l _ => Continuous.const_smul ?_ _
  exact continuous_finsetProd _ fun l _ => hA.matrix_elem _ _

@[continuity, fun_prop]

中文:
定理 Continuous.matrix_det
  结论: [Fintype n] [DecidableEq n] [CommRing R] [IsTopologicalRing R]
  证明: by
  simp_rw [Matrix.det_apply]
  refine continuous_finsetSum _ fun l _ => Continuous.const_smul ?_ _
  exact continuous_finsetProd _ fun l _ => hA.matrix_elem _ _

@[continuity, fun_prop]

Depends on / 依赖: Continuous, Continuous.const_smul, Matrix, Matrix.det_apply, const_smul, continuous_finsetProd, continuous_finsetSum, det_apply, hA.matrix_elem, matrix_elem, simp_rw
-/
theorem Continuous.matrix_det [Fintype n] [DecidableEq n] [CommRing R] [IsTopologicalRing R]
    {A : X -> Matrix n n R} (hA : Continuous A) : Continuous fun x => (A x).det := by
  simp_rw [Matrix.det_apply]
  refine continuous_finsetSum _ fun l _ => Continuous.const_smul ?_ _
  exact continuous_finsetProd _ fun l _ => hA.matrix_elem _ _

@[continuity, fun_prop]
/--
theorem `Continuous.matrix_updateCol` / 定理 `Continuous.matrix_updateCol`

English:
theorem Continuous.matrix_updateCol
  statement: [DecidableEq n] (i : n) {A : X -> Matrix m n R}
  proof: continuous_matrix fun _j k =>
(continuous_apply k).comp
      ((continuous_apply _).comp hA).update i ((continuous_apply _).comp hB)

@[continuity, fun_prop]

中文:
定理 Continuous.matrix_updateCol
  结论: [DecidableEq n] (i : n) {A : X -> Matrix m n R}
  证明: continuous_matrix fun _j k =>
(continuous_apply k).comp
      ((continuous_apply _).comp hA).update i ((continuous_apply _).comp hB)

@[continuity, fun_prop]

Depends on / 依赖: continuous_apply, continuous_matrix, update
-/
theorem Continuous.matrix_updateCol [DecidableEq n] (i : n) {A : X -> Matrix m n R}
    {B : X -> m -> R} (hA : Continuous A) (hB : Continuous B) :
    Continuous fun x => (A x).updateCol i (B x) :=
  continuous_matrix fun _j k =>
(continuous_apply k).comp
      ((continuous_apply _).comp hA).update i ((continuous_apply _).comp hB)

@[continuity, fun_prop]
/--
theorem `Continuous.matrix_updateRow` / 定理 `Continuous.matrix_updateRow`

English:
theorem Continuous.matrix_updateRow
  statement: [DecidableEq m] (i : m) {A : X -> Matrix m n R} {B : X -> n -> R}
  proof: hA.update i hB

@[continuity, fun_prop]

中文:
定理 Continuous.matrix_updateRow
  结论: [DecidableEq m] (i : m) {A : X -> Matrix m n R} {B : X -> n -> R}
  证明: hA.update i hB

@[continuity, fun_prop]

Depends on / 依赖: hA.update, update
-/
theorem Continuous.matrix_updateRow [DecidableEq m] (i : m) {A : X -> Matrix m n R} {B : X -> n -> R}
    (hA : Continuous A) (hB : Continuous B) : Continuous fun x => (A x).updateRow i (B x) :=
  hA.update i hB

@[continuity, fun_prop]
/--
theorem `Continuous.matrix_cramer` / 定理 `Continuous.matrix_cramer`

English:
theorem Continuous.matrix_cramer
  statement: [Fintype n] [DecidableEq n] [CommRing R] [IsTopologicalRing R]
  proof: continuous_pi fun _ => (hA.matrix_updateCol _ hB).matrix_det

@[continuity, fun_prop]

中文:
定理 Continuous.matrix_cramer
  结论: [Fintype n] [DecidableEq n] [CommRing R] [IsTopologicalRing R]
  证明: continuous_pi fun _ => (hA.matrix_updateCol _ hB).matrix_det

@[continuity, fun_prop]

Depends on / 依赖: continuous_pi, hA.matrix_updateCol, matrix_det, matrix_updateCol
-/
theorem Continuous.matrix_cramer [Fintype n] [DecidableEq n] [CommRing R] [IsTopologicalRing R]
    {A : X -> Matrix n n R} {B : X -> n -> R} (hA : Continuous A) (hB : Continuous B) :
    Continuous fun x => cramer (A x) (B x) :=
  continuous_pi fun _ => (hA.matrix_updateCol _ hB).matrix_det

@[continuity, fun_prop]
/--
theorem `Continuous.matrix_adjugate` / 定理 `Continuous.matrix_adjugate`

English:
theorem Continuous.matrix_adjugate
  statement: [Fintype n] [DecidableEq n] [CommRing R] [IsTopologicalRing R]
  proof: continuous_matrix fun _j k =>
    (hA.matrix_transpose.matrix_updateCol k continuous_const).matrix_det

中文:
定理 Continuous.matrix_adjugate
  结论: [Fintype n] [DecidableEq n] [CommRing R] [IsTopologicalRing R]
  证明: continuous_matrix fun _j k =>
    (hA.matrix_transpose.matrix_updateCol k continuous_const).matrix_det

Depends on / 依赖: continuous_const, continuous_matrix, hA.matrix_transpose.matrix_updateCol, matrix_det, matrix_transpose, matrix_updateCol
-/
theorem Continuous.matrix_adjugate [Fintype n] [DecidableEq n] [CommRing R] [IsTopologicalRing R]
    {A : X -> Matrix n n R} (hA : Continuous A) : Continuous fun x => (A x).adjugate :=
  continuous_matrix fun _j k =>
    (hA.matrix_transpose.matrix_updateCol k continuous_const).matrix_det

/--
theorem `continuousAt_matrix_inv` / 定理 `continuousAt_matrix_inv`

English:
theorem continuousAt_matrix_inv
  statement: [Fintype n] [DecidableEq n] [CommRing R] [IsTopologicalRing R]
  proof: (h.comp continuous_id.matrix_det.continuousAt).smul continuous_id.matrix_adjugate.continuousAt

中文:
定理 continuousAt_matrix_inv
  结论: [Fintype n] [DecidableEq n] [CommRing R] [IsTopologicalRing R]
  证明: (h.comp continuous_id.matrix_det.continuousAt).smul continuous_id.matrix_adjugate.continuousAt

Depends on / 依赖: continuousAt, continuous_id, continuous_id.matrix_adjugate.continuousAt, continuous_id.matrix_det.continuousAt, h.comp, matrix_adjugate, matrix_det
-/
theorem continuousAt_matrix_inv [Fintype n] [DecidableEq n] [CommRing R] [IsTopologicalRing R]
    (A : Matrix n n R) (h : ContinuousAt Ring.inverse A.det) : ContinuousAt Inv.inv A :=
  (h.comp continuous_id.matrix_det.continuousAt).smul continuous_id.matrix_adjugate.continuousAt

namespace Topology

variable {m n R S : Type*} [TopologicalSpace R] [TopologicalSpace S] {f : R -> S}

/--
lemma `IsInducing.matrix_map` / 引理 `IsInducing.matrix_map`

English:
lemma IsInducing.matrix_map
  given: (hf : IsInducing f)
  proof: IsInducing.piMap fun _ : m => (IsInducing.piMap fun _ : n => hf)

中文:
引理 IsInducing.matrix_map
  条件: (hf : IsInducing f)
  证明: IsInducing.piMap fun _ : m => (IsInducing.piMap fun _ : n => hf)

Depends on / 依赖: IsInducing, IsInducing.piMap
-/
lemma IsInducing.matrix_map (hf : IsInducing f) :
    IsInducing (map · f : Matrix m n R -> Matrix m n S) :=
  IsInducing.piMap fun _ : m => (IsInducing.piMap fun _ : n => hf)

/--
lemma `IsEmbedding.matrix_map` / 引理 `IsEmbedding.matrix_map`

English:
lemma IsEmbedding.matrix_map
  given: (hf : IsEmbedding f)
  proof: IsEmbedding.piMap fun _ : m => (IsEmbedding.piMap fun _ : n => hf)

中文:
引理 IsEmbedding.matrix_map
  条件: (hf : IsEmbedding f)
  证明: IsEmbedding.piMap fun _ : m => (IsEmbedding.piMap fun _ : n => hf)

Depends on / 依赖: IsEmbedding, IsEmbedding.piMap
-/
lemma IsEmbedding.matrix_map (hf : IsEmbedding f) :
    IsEmbedding (map · f : Matrix m n R -> Matrix m n S) :=
  IsEmbedding.piMap fun _ : m => (IsEmbedding.piMap fun _ : n => hf)

/--
lemma `IsClosedEmbedding.matrix_map` / 引理 `IsClosedEmbedding.matrix_map`

English:
lemma IsClosedEmbedding.matrix_map
  given: (hf : IsClosedEmbedding f)
  proof: IsClosedEmbedding.piMap fun _ : m => (IsClosedEmbedding.piMap fun _ : n => hf)

中文:
引理 IsClosedEmbedding.matrix_map
  条件: (hf : IsClosedEmbedding f)
  证明: IsClosedEmbedding.piMap fun _ : m => (IsClosedEmbedding.piMap fun _ : n => hf)

Depends on / 依赖: IsClosedEmbedding, IsClosedEmbedding.piMap
-/
lemma IsClosedEmbedding.matrix_map (hf : IsClosedEmbedding f) :
    IsClosedEmbedding (map · f : Matrix m n R -> Matrix m n S) :=
  IsClosedEmbedding.piMap fun _ : m => (IsClosedEmbedding.piMap fun _ : n => hf)

/--
lemma `IsOpenEmbedding.matrix_map` / 引理 `IsOpenEmbedding.matrix_map`

English:
lemma IsOpenEmbedding.matrix_map
  given: [Finite m] [Finite n] (hf : IsOpenEmbedding f)
  proof: IsOpenEmbedding.piMap fun _ : m => (IsOpenEmbedding.piMap fun _ : n => hf)

中文:
引理 IsOpenEmbedding.matrix_map
  条件: [Finite m] [Finite n] (hf : IsOpenEmbedding f)
  证明: IsOpenEmbedding.piMap fun _ : m => (IsOpenEmbedding.piMap fun _ : n => hf)

Depends on / 依赖: IsOpenEmbedding, IsOpenEmbedding.piMap
-/
lemma IsOpenEmbedding.matrix_map [Finite m] [Finite n] (hf : IsOpenEmbedding f) :
    IsOpenEmbedding (map · f : Matrix m n R -> Matrix m n S) :=
  IsOpenEmbedding.piMap fun _ : m => (IsOpenEmbedding.piMap fun _ : n => hf)

end Topology

-- lemmas about functions in `Mathlib/Data/Matrix/Block.lean`
section BlockMatrices

@[continuity, fun_prop]
/--
theorem `Continuous.matrix_fromBlocks` / 定理 `Continuous.matrix_fromBlocks`

English:
theorem Continuous.matrix_fromBlocks
  statement: {A : X -> Matrix n l R} {B : X -> Matrix n m R}
  proof: continuous_matrix by
    rintro (i | i) (j | j) <;> refine Continuous.matrix_elem ?_ i j <;> assumption

@[continuity, fun_prop]

中文:
定理 Continuous.matrix_fromBlocks
  结论: {A : X -> Matrix n l R} {B : X -> Matrix n m R}
  证明: continuous_matrix by
    rintro (i | i) (j | j) <;> refine Continuous.matrix_elem ?_ i j <;> assumption

@[continuity, fun_prop]

Depends on / 依赖: Continuous, Continuous.matrix_elem, continuous_matrix, matrix_elem
-/
theorem Continuous.matrix_fromBlocks {A : X -> Matrix n l R} {B : X -> Matrix n m R}
    {C : X -> Matrix p l R} {D : X -> Matrix p m R} (hA : Continuous A) (hB : Continuous B)
    (hC : Continuous C) (hD : Continuous D) :
    Continuous fun x => Matrix.fromBlocks (A x) (B x) (C x) (D x) :=
continuous_matrix by
    rintro (i | i) (j | j) <;> refine Continuous.matrix_elem ?_ i j <;> assumption

@[continuity, fun_prop]
/--
theorem `Continuous.matrix_blockDiagonal` / 定理 `Continuous.matrix_blockDiagonal`

English:
theorem Continuous.matrix_blockDiagonal
  statement: [Zero R] [DecidableEq p] {A : X -> p -> Matrix m n R}
  proof: continuous_matrix fun ⟨i₁, i₂⟩ ⟨j₁, _j₂⟩ =>
    (((continuous_apply i₂).comp hA).matrix_elem i₁ j₁).if_const _ continuous_zero

@[continuity, fun_prop]

中文:
定理 Continuous.matrix_blockDiagonal
  结论: [Zero R] [DecidableEq p] {A : X -> p -> Matrix m n R}
  证明: continuous_matrix fun ⟨i₁, i₂⟩ ⟨j₁, _j₂⟩ =>
    (((continuous_apply i₂).comp hA).matrix_elem i₁ j₁).if_const _ continuous_zero

@[continuity, fun_prop]

Depends on / 依赖: continuous_apply, continuous_matrix, continuous_zero, if_const, matrix_elem
-/
theorem Continuous.matrix_blockDiagonal [Zero R] [DecidableEq p] {A : X -> p -> Matrix m n R}
    (hA : Continuous A) : Continuous fun x => blockDiagonal (A x) :=
  continuous_matrix fun ⟨i₁, i₂⟩ ⟨j₁, _j₂⟩ =>
    (((continuous_apply i₂).comp hA).matrix_elem i₁ j₁).if_const _ continuous_zero

@[continuity, fun_prop]
/--
theorem `Continuous.matrix_blockDiag` / 定理 `Continuous.matrix_blockDiag`

English:
theorem Continuous.matrix_blockDiag
  given: {A : X -> Matrix (m × p) (n × p) R} (hA : Continuous A)
  proof: continuous_pi fun _i => continuous_matrix fun _j _k => hA.matrix_elem _ _

@[continuity, fun_prop]

中文:
定理 Continuous.matrix_blockDiag
  条件: {A : X -> Matrix (m × p) (n × p) R} (hA : Continuous A)
  证明: continuous_pi fun _i => continuous_matrix fun _j _k => hA.matrix_elem _ _

@[continuity, fun_prop]

Depends on / 依赖: continuous_matrix, continuous_pi, hA.matrix_elem, matrix_elem
-/
theorem Continuous.matrix_blockDiag {A : X -> Matrix (m × p) (n × p) R} (hA : Continuous A) :
    Continuous fun x => blockDiag (A x) :=
  continuous_pi fun _i => continuous_matrix fun _j _k => hA.matrix_elem _ _

@[continuity, fun_prop]
/--
theorem `Continuous.matrix_blockDiagonal'` / 定理 `Continuous.matrix_blockDiagonal'`

English:
theorem Continuous.matrix_blockDiagonal'
  statement: [Zero R] [DecidableEq l]
  proof: continuous_matrix fun ⟨i₁, i₂⟩ ⟨j₁, j₂⟩ => by
    dsimp only [blockDiagonal'_apply']
    split_ifs with h
    · subst h
      exact ((continuous_apply i₁).comp hA).matrix_elem i₂ j₂
    · exact continuous_const

@[continuity, fun_prop]

中文:
定理 Continuous.matrix_blockDiagonal'
  结论: [Zero R] [DecidableEq l]
  证明: continuous_matrix fun ⟨i₁, i₂⟩ ⟨j₁, j₂⟩ => by
    dsimp only [blockDiagonal'_apply']
    split_ifs with h
    · subst h
      exact ((continuous_apply i₁).comp hA).matrix_elem i₂ j₂
    · exact continuous_const

@[continuity, fun_prop]

Depends on / 依赖: _apply, blockDiagonal, continuous_apply, continuous_const, continuous_matrix, matrix_elem, split_ifs
-/
theorem Continuous.matrix_blockDiagonal' [Zero R] [DecidableEq l]
    {A : X -> forall i, Matrix (m' i) (n' i) R} (hA : Continuous A) :
    Continuous fun x => blockDiagonal' (A x) :=
  continuous_matrix fun ⟨i₁, i₂⟩ ⟨j₁, j₂⟩ => by
    dsimp only [blockDiagonal'_apply']
    split_ifs with h
    · subst h
      exact ((continuous_apply i₁).comp hA).matrix_elem i₂ j₂
    · exact continuous_const

@[continuity, fun_prop]
/--
theorem `Continuous.matrix_blockDiag'` / 定理 `Continuous.matrix_blockDiag'`

English:
theorem Continuous.matrix_blockDiag'
  proof: continuous_pi fun _i => continuous_matrix fun _j _k => hA.matrix_elem _ _

中文:
定理 Continuous.matrix_blockDiag'
  证明: continuous_pi fun _i => continuous_matrix fun _j _k => hA.matrix_elem _ _

Depends on / 依赖: continuous_matrix, continuous_pi, hA.matrix_elem, matrix_elem
-/
theorem Continuous.matrix_blockDiag'
    {A : X -> Matrix (Σ i, m' i) (Σ i, n' i) R} (hA : Continuous A) :
    Continuous fun x => blockDiag' (A x) :=
  continuous_pi fun _i => continuous_matrix fun _j _k => hA.matrix_elem _ _

/--
theorem `isClosed_setOfPred_blockTriangular` / 定理 `isClosed_setOfPred_blockTriangular`

English:
theorem isClosed_setOfPred_blockTriangular
  statement: {α : Type*} {b : m -> α} [LinearOrder α] [Zero R]
  proof: by
  simp only [BlockTriangular, Set.ofPred_forall]
  refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => ?_
  exact isClosed_eq (continuous_id.matrix_elem i j) continuous_const

@[deprecated (since := "2026-07-09")]
alias isClosed_setOf_blockTriangular := isClosed_setO

中文:
定理 isClosed_setOfPred_blockTriangular
  结论: {α : 类型} {b : m -> α} [LinearOrder α] [Zero R]
  证明: by
  simp only [BlockTriangular, Set.ofPred_forall]
  refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => ?_
  exact isClosed_eq (continuous_id.matrix_elem i j) continuous_const

@[deprecated (since := "2026-07-09")]
alias isClosed_setOf_blockTriangular := isClosed_setO

Depends on / 依赖: BlockTriangular, Set.ofPred_forall, continuous_const, continuous_id, continuous_id.matrix_elem, isClosed_eq, isClosed_iInter, matrix_elem, ofPred_forall
-/
theorem isClosed_setOfPred_blockTriangular {α : Type*} {b : m -> α} [LinearOrder α] [Zero R]
    [T2Space R] : IsClosed {M : Matrix m m R | M.BlockTriangular b} := by
  simp only [BlockTriangular, Set.ofPred_forall]
  refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => ?_
  exact isClosed_eq (continuous_id.matrix_elem i j) continuous_const

@[deprecated (since := "2026-07-09")]
alias isClosed_setOf_blockTriangular := isClosed_setOfPred_blockTriangular

end BlockMatrices

end Continuity

/-! ### Lemmas about infinite sums -/


section tsum

variable [AddCommMonoid R] [TopologicalSpace R] {L : SummationFilter X}

/--
theorem `HasSum.matrix_transpose` / 定理 `HasSum.matrix_transpose`

English:
theorem HasSum.matrix_transpose
  given: {f : X -> Matrix m n R} {a : Matrix m n R} (hf : HasSum f a L)
  proof: (hf.map (Matrix.transposeAddEquiv m n R) continuous_id.matrix_transpose :)

中文:
定理 HasSum.matrix_transpose
  条件: {f : X -> Matrix m n R} {a : Matrix m n R} (hf : HasSum f a L)
  证明: (hf.map (Matrix.transposeAddEquiv m n R) continuous_id.matrix_transpose :)

Depends on / 依赖: Matrix, Matrix.transposeAddEquiv, continuous_id, continuous_id.matrix_transpose, hf.map, matrix_transpose, transposeAddEquiv
-/
theorem HasSum.matrix_transpose {f : X -> Matrix m n R} {a : Matrix m n R} (hf : HasSum f a L) :
    HasSum (fun x => (f x)ᵀ) aᵀ L :=
  (hf.map (Matrix.transposeAddEquiv m n R) continuous_id.matrix_transpose :)

/--
theorem `Summable.matrix_transpose` / 定理 `Summable.matrix_transpose`

English:
theorem Summable.matrix_transpose
  given: {f : X -> Matrix m n R} (hf : Summable f L)
  proof: hf.hasSum.matrix_transpose.summable

@[simp]

中文:
定理 Summable.matrix_transpose
  条件: {f : X -> Matrix m n R} (hf : Summable f L)
  证明: hf.hasSum.matrix_transpose.summable

@[simp]

Depends on / 依赖: hasSum, hf.hasSum.matrix_transpose.summable, matrix_transpose, summable
-/
theorem Summable.matrix_transpose {f : X -> Matrix m n R} (hf : Summable f L) :
    Summable (fun x => (f x)ᵀ) L :=
  hf.hasSum.matrix_transpose.summable

@[simp]
/--
theorem `summable_matrix_transpose` / 定理 `summable_matrix_transpose`

English:
theorem summable_matrix_transpose
  given: {f : X -> Matrix m n R}
  proof: Summable.map_iff_of_equiv (Matrix.transposeAddEquiv m n R)
    continuous_id.matrix_transpose continuous_id.matrix_transpose

中文:
定理 summable_matrix_transpose
  条件: {f : X -> Matrix m n R}
  证明: Summable.map_iff_of_equiv (Matrix.transposeAddEquiv m n R)
    continuous_id.matrix_transpose continuous_id.matrix_transpose

Depends on / 依赖: Matrix, Matrix.transposeAddEquiv, Summable, Summable.map_iff_of_equiv, continuous_id, continuous_id.matrix_transpose, map_iff_of_equiv, matrix_transpose, transposeAddEquiv
-/
theorem summable_matrix_transpose {f : X -> Matrix m n R} :
    (Summable (fun x => (f x)ᵀ) L) ↔ Summable f L :=
  Summable.map_iff_of_equiv (Matrix.transposeAddEquiv m n R)
    continuous_id.matrix_transpose continuous_id.matrix_transpose

/--
theorem `Matrix.transpose_tsum` / 定理 `Matrix.transpose_tsum`

English:
theorem Matrix.transpose_tsum
  given: [T2Space R] {f : X -> Matrix m n R}
  proof: Function.LeftInverse.map_tsum f (g := transposeAddEquiv m n R) continuous_id.matrix_transpose
    continuous_id.matrix_transpose transpose_transpose

中文:
定理 Matrix.transpose_tsum
  条件: [T2Space R] {f : X -> Matrix m n R}
  证明: Function.LeftInverse.map_tsum f (g := transposeAddEquiv m n R) continuous_id.matrix_transpose
    continuous_id.matrix_transpose transpose_transpose

Depends on / 依赖: Function, Function.LeftInverse.map_tsum, LeftInverse, continuous_id, continuous_id.matrix_transpose, map_tsum, matrix_transpose, transposeAddEquiv, transpose_transpose
-/
theorem Matrix.transpose_tsum [T2Space R] {f : X -> Matrix m n R} :
    (∑'[L] x, f x)ᵀ = ∑'[L] x, (f x)ᵀ :=
  Function.LeftInverse.map_tsum f (g := transposeAddEquiv m n R) continuous_id.matrix_transpose
    continuous_id.matrix_transpose transpose_transpose

/--
theorem `HasSum.matrix_conjTranspose` / 定理 `HasSum.matrix_conjTranspose`

English:
theorem HasSum.matrix_conjTranspose
  statement: [StarAddMonoid R] [ContinuousStar R] {f : X -> Matrix m n R}
  proof: (hf.map (Matrix.conjTransposeAddEquiv m n R) continuous_id.matrix_conjTranspose :)

中文:
定理 HasSum.matrix_conjTranspose
  结论: [StarAddMonoid R] [ContinuousStar R] {f : X -> Matrix m n R}
  证明: (hf.map (Matrix.conjTransposeAddEquiv m n R) continuous_id.matrix_conjTranspose :)

Depends on / 依赖: Matrix, Matrix.conjTransposeAddEquiv, conjTransposeAddEquiv, continuous_id, continuous_id.matrix_conjTranspose, hf.map, matrix_conjTranspose
-/
theorem HasSum.matrix_conjTranspose [StarAddMonoid R] [ContinuousStar R] {f : X -> Matrix m n R}
    {a : Matrix m n R} (hf : HasSum f a L) : HasSum (fun x => (f x)ᴴ) aᴴ L :=
  (hf.map (Matrix.conjTransposeAddEquiv m n R) continuous_id.matrix_conjTranspose :)

/--
theorem `Summable.matrix_conjTranspose` / 定理 `Summable.matrix_conjTranspose`

English:
theorem Summable.matrix_conjTranspose
  statement: [StarAddMonoid R] [ContinuousStar R] {f : X -> Matrix m n R}
  proof: hf.hasSum.matrix_conjTranspose.summable

@[simp]

中文:
定理 Summable.matrix_conjTranspose
  结论: [StarAddMonoid R] [ContinuousStar R] {f : X -> Matrix m n R}
  证明: hf.hasSum.matrix_conjTranspose.summable

@[simp]

Depends on / 依赖: hasSum, hf.hasSum.matrix_conjTranspose.summable, matrix_conjTranspose, summable
-/
theorem Summable.matrix_conjTranspose [StarAddMonoid R] [ContinuousStar R] {f : X -> Matrix m n R}
    (hf : Summable f L) : Summable (fun x => (f x)ᴴ) L :=
  hf.hasSum.matrix_conjTranspose.summable

@[simp]
/--
theorem `summable_matrix_conjTranspose` / 定理 `summable_matrix_conjTranspose`

English:
theorem summable_matrix_conjTranspose
  given: [StarAddMonoid R] [ContinuousStar R] {f : X -> Matrix m n R}
  proof: Summable.map_iff_of_equiv (Matrix.conjTransposeAddEquiv m n R)
    continuous_id.matrix_conjTranspose continuous_id.matrix_conjTranspose

中文:
定理 summable_matrix_conjTranspose
  条件: [StarAddMonoid R] [ContinuousStar R] {f : X -> Matrix m n R}
  证明: Summable.map_iff_of_equiv (Matrix.conjTransposeAddEquiv m n R)
    continuous_id.matrix_conjTranspose continuous_id.matrix_conjTranspose

Depends on / 依赖: Matrix, Matrix.conjTransposeAddEquiv, Summable, Summable.map_iff_of_equiv, conjTransposeAddEquiv, continuous_id, continuous_id.matrix_conjTranspose, map_iff_of_equiv, matrix_conjTranspose
-/
theorem summable_matrix_conjTranspose [StarAddMonoid R] [ContinuousStar R] {f : X -> Matrix m n R} :
    (Summable (fun x => (f x)ᴴ) L) ↔ Summable f L :=
  Summable.map_iff_of_equiv (Matrix.conjTransposeAddEquiv m n R)
    continuous_id.matrix_conjTranspose continuous_id.matrix_conjTranspose

/--
theorem `Matrix.conjTranspose_tsum` / 定理 `Matrix.conjTranspose_tsum`

English:
theorem Matrix.conjTranspose_tsum
  statement: [StarAddMonoid R] [ContinuousStar R] [T2Space R]
  proof: Function.LeftInverse.map_tsum f (g := conjTransposeAddEquiv m n R)
    continuous_id.matrix_conjTranspose continuous_id.matrix_conjTranspose
    conjTranspose_conjTranspose

中文:
定理 Matrix.conjTranspose_tsum
  结论: [StarAddMonoid R] [ContinuousStar R] [T2Space R]
  证明: Function.LeftInverse.map_tsum f (g := conjTransposeAddEquiv m n R)
    continuous_id.matrix_conjTranspose continuous_id.matrix_conjTranspose
    conjTranspose_conjTranspose

Depends on / 依赖: Function, Function.LeftInverse.map_tsum, LeftInverse, conjTransposeAddEquiv, conjTranspose_conjTranspose, continuous_id, continuous_id.matrix_conjTranspose, map_tsum, matrix_conjTranspose
-/
theorem Matrix.conjTranspose_tsum [StarAddMonoid R] [ContinuousStar R] [T2Space R]
    {f : X -> Matrix m n R} : (∑'[L] x, f x)ᴴ = ∑'[L] x, (f x)ᴴ :=
  Function.LeftInverse.map_tsum f (g := conjTransposeAddEquiv m n R)
    continuous_id.matrix_conjTranspose continuous_id.matrix_conjTranspose
    conjTranspose_conjTranspose

/--
theorem `HasSum.matrix_diagonal` / 定理 `HasSum.matrix_diagonal`

English:
theorem HasSum.matrix_diagonal
  given: [DecidableEq n] {f : X -> n -> R} {a : n -> R} (hf : HasSum f a L)
  proof: hf.map (diagonalAddMonoidHom n R) continuous_id.matrix_diagonal

中文:
定理 HasSum.matrix_diagonal
  条件: [DecidableEq n] {f : X -> n -> R} {a : n -> R} (hf : HasSum f a L)
  证明: hf.map (diagonalAddMonoidHom n R) continuous_id.matrix_diagonal

Depends on / 依赖: continuous_id, continuous_id.matrix_diagonal, diagonalAddMonoidHom, hf.map, matrix_diagonal
-/
theorem HasSum.matrix_diagonal [DecidableEq n] {f : X -> n -> R} {a : n -> R} (hf : HasSum f a L) :
    HasSum (fun x => diagonal (f x)) (diagonal a) L :=
  hf.map (diagonalAddMonoidHom n R) continuous_id.matrix_diagonal

/--
theorem `Summable.matrix_diagonal` / 定理 `Summable.matrix_diagonal`

English:
theorem Summable.matrix_diagonal
  given: [DecidableEq n] {f : X -> n -> R} (hf : Summable f L)
  proof: hf.hasSum.matrix_diagonal.summable

@[simp]

中文:
定理 Summable.matrix_diagonal
  条件: [DecidableEq n] {f : X -> n -> R} (hf : Summable f L)
  证明: hf.hasSum.matrix_diagonal.summable

@[simp]

Depends on / 依赖: hasSum, hf.hasSum.matrix_diagonal.summable, matrix_diagonal, summable
-/
theorem Summable.matrix_diagonal [DecidableEq n] {f : X -> n -> R} (hf : Summable f L) :
    Summable (fun x => diagonal (f x)) L :=
  hf.hasSum.matrix_diagonal.summable

@[simp]
/--
theorem `summable_matrix_diagonal` / 定理 `summable_matrix_diagonal`

English:
theorem summable_matrix_diagonal
  given: [DecidableEq n] {f : X -> n -> R}
  proof: Summable.map_iff_of_leftInverse (Matrix.diagonalAddMonoidHom n R) (Matrix.diagAddMonoidHom n R)
    continuous_id.matrix_diagonal continuous_matrix_diag fun A => diag_diagonal A

中文:
定理 summable_matrix_diagonal
  条件: [DecidableEq n] {f : X -> n -> R}
  证明: Summable.map_iff_of_leftInverse (Matrix.diagonalAddMonoidHom n R) (Matrix.diagAddMonoidHom n R)
    continuous_id.matrix_diagonal continuous_matrix_diag fun A => diag_diagonal A

Depends on / 依赖: Matrix, Matrix.diagAddMonoidHom, Matrix.diagonalAddMonoidHom, Summable, Summable.map_iff_of_leftInverse, continuous_id, continuous_id.matrix_diagonal, continuous_matrix_diag, diagAddMonoidHom, diag_diagonal, diagonalAddMonoidHom, map_iff_of_leftInverse, matrix_diagonal
-/
theorem summable_matrix_diagonal [DecidableEq n] {f : X -> n -> R} :
    (Summable (fun x => diagonal (f x)) L) ↔ Summable f L :=
  Summable.map_iff_of_leftInverse (Matrix.diagonalAddMonoidHom n R) (Matrix.diagAddMonoidHom n R)
    continuous_id.matrix_diagonal continuous_matrix_diag fun A => diag_diagonal A

/--
theorem `Matrix.diagonal_tsum` / 定理 `Matrix.diagonal_tsum`

English:
theorem Matrix.diagonal_tsum
  given: [DecidableEq n] [T2Space R] {f : X -> n -> R}
  proof: Function.LeftInverse.map_tsum f (g := diagonalAddMonoidHom n R)
    continuous_id.matrix_diagonal continuous_matrix_diag diag_diagonal

中文:
定理 Matrix.diagonal_tsum
  条件: [DecidableEq n] [T2Space R] {f : X -> n -> R}
  证明: Function.LeftInverse.map_tsum f (g := diagonalAddMonoidHom n R)
    continuous_id.matrix_diagonal continuous_matrix_diag diag_diagonal

Depends on / 依赖: Function, Function.LeftInverse.map_tsum, LeftInverse, continuous_id, continuous_id.matrix_diagonal, continuous_matrix_diag, diag_diagonal, diagonalAddMonoidHom, map_tsum, matrix_diagonal
-/
theorem Matrix.diagonal_tsum [DecidableEq n] [T2Space R] {f : X -> n -> R} :
    diagonal (∑'[L] x, f x) = ∑'[L] x, diagonal (f x) :=
  Function.LeftInverse.map_tsum f (g := diagonalAddMonoidHom n R)
    continuous_id.matrix_diagonal continuous_matrix_diag diag_diagonal

/--
theorem `HasSum.matrix_diag` / 定理 `HasSum.matrix_diag`

English:
theorem HasSum.matrix_diag
  given: {f : X -> Matrix n n R} {a : Matrix n n R} (hf : HasSum f a L)
  proof: hf.map (diagAddMonoidHom n R) continuous_matrix_diag

中文:
定理 HasSum.matrix_diag
  条件: {f : X -> Matrix n n R} {a : Matrix n n R} (hf : HasSum f a L)
  证明: hf.map (diagAddMonoidHom n R) continuous_matrix_diag

Depends on / 依赖: continuous_matrix_diag, diagAddMonoidHom, hf.map
-/
theorem HasSum.matrix_diag {f : X -> Matrix n n R} {a : Matrix n n R} (hf : HasSum f a L) :
    HasSum (fun x => diag (f x)) (diag a) L :=
  hf.map (diagAddMonoidHom n R) continuous_matrix_diag

/--
theorem `Summable.matrix_diag` / 定理 `Summable.matrix_diag`

English:
theorem Summable.matrix_diag
  given: {f : X -> Matrix n n R} (hf : Summable f L)
  proof: hf.hasSum.matrix_diag.summable

中文:
定理 Summable.matrix_diag
  条件: {f : X -> Matrix n n R} (hf : Summable f L)
  证明: hf.hasSum.matrix_diag.summable

Depends on / 依赖: hasSum, hf.hasSum.matrix_diag.summable, matrix_diag, summable
-/
theorem Summable.matrix_diag {f : X -> Matrix n n R} (hf : Summable f L) :
    Summable (fun x => diag (f x)) L :=
  hf.hasSum.matrix_diag.summable

section BlockMatrices

/--
theorem `HasSum.matrix_blockDiagonal` / 定理 `HasSum.matrix_blockDiagonal`

English:
theorem HasSum.matrix_blockDiagonal
  statement: [DecidableEq p] {f : X -> p -> Matrix m n R}
  proof: hf.map (blockDiagonalAddMonoidHom m n p R) continuous_id.matrix_blockDiagonal

中文:
定理 HasSum.matrix_blockDiagonal
  结论: [DecidableEq p] {f : X -> p -> Matrix m n R}
  证明: hf.map (blockDiagonalAddMonoidHom m n p R) continuous_id.matrix_blockDiagonal

Depends on / 依赖: blockDiagonalAddMonoidHom, continuous_id, continuous_id.matrix_blockDiagonal, hf.map, matrix_blockDiagonal
-/
theorem HasSum.matrix_blockDiagonal [DecidableEq p] {f : X -> p -> Matrix m n R}
    {a : p -> Matrix m n R} (hf : HasSum f a L) :
    HasSum (fun x => blockDiagonal (f x)) (blockDiagonal a) L :=
  hf.map (blockDiagonalAddMonoidHom m n p R) continuous_id.matrix_blockDiagonal

/--
theorem `Summable.matrix_blockDiagonal` / 定理 `Summable.matrix_blockDiagonal`

English:
theorem Summable.matrix_blockDiagonal
  statement: [DecidableEq p] {f : X -> p -> Matrix m n R}
  proof: hf.hasSum.matrix_blockDiagonal.summable

中文:
定理 Summable.matrix_blockDiagonal
  结论: [DecidableEq p] {f : X -> p -> Matrix m n R}
  证明: hf.hasSum.matrix_blockDiagonal.summable

Depends on / 依赖: hasSum, hf.hasSum.matrix_blockDiagonal.summable, matrix_blockDiagonal, summable
-/
theorem Summable.matrix_blockDiagonal [DecidableEq p] {f : X -> p -> Matrix m n R}
    (hf : Summable f L) : Summable (fun x => blockDiagonal (f x)) L :=
  hf.hasSum.matrix_blockDiagonal.summable

/--
theorem `summable_matrix_blockDiagonal` / 定理 `summable_matrix_blockDiagonal`

English:
theorem summable_matrix_blockDiagonal
  given: [DecidableEq p] {f : X -> p -> Matrix m n R}
  proof: Summable.map_iff_of_leftInverse (blockDiagonalAddMonoidHom m n p R)
    (blockDiagAddMonoidHom m n p R) continuous_id.matrix_blockDiagonal
    continuous_id.matrix_blockDiag fun A => blockDiag_blockDiagonal A

中文:
定理 summable_matrix_blockDiagonal
  条件: [DecidableEq p] {f : X -> p -> Matrix m n R}
  证明: Summable.map_iff_of_leftInverse (blockDiagonalAddMonoidHom m n p R)
    (blockDiagAddMonoidHom m n p R) continuous_id.matrix_blockDiagonal
    continuous_id.matrix_blockDiag fun A => blockDiag_blockDiagonal A

Depends on / 依赖: Summable, Summable.map_iff_of_leftInverse, blockDiagAddMonoidHom, blockDiag_blockDiagonal, blockDiagonalAddMonoidHom, continuous_id, continuous_id.matrix_blockDiag, continuous_id.matrix_blockDiagonal, map_iff_of_leftInverse, matrix_blockDiag, matrix_blockDiagonal
-/
theorem summable_matrix_blockDiagonal [DecidableEq p] {f : X -> p -> Matrix m n R} :
    (Summable (fun x => blockDiagonal (f x)) L) ↔ Summable f L :=
  Summable.map_iff_of_leftInverse (blockDiagonalAddMonoidHom m n p R)
    (blockDiagAddMonoidHom m n p R) continuous_id.matrix_blockDiagonal
    continuous_id.matrix_blockDiag fun A => blockDiag_blockDiagonal A

/--
theorem `Matrix.blockDiagonal_tsum` / 定理 `Matrix.blockDiagonal_tsum`

English:
theorem Matrix.blockDiagonal_tsum
  given: [DecidableEq p] [T2Space R] {f : X -> p -> Matrix m n R}
  proof: Function.LeftInverse.map_tsum (g := blockDiagonalAddMonoidHom m n p R) f
    continuous_id.matrix_blockDiagonal continuous_id.matrix_blockDiag blockDiag_blockDiagonal

中文:
定理 Matrix.blockDiagonal_tsum
  条件: [DecidableEq p] [T2Space R] {f : X -> p -> Matrix m n R}
  证明: Function.LeftInverse.map_tsum (g := blockDiagonalAddMonoidHom m n p R) f
    continuous_id.matrix_blockDiagonal continuous_id.matrix_blockDiag blockDiag_blockDiagonal

Depends on / 依赖: Function, Function.LeftInverse.map_tsum, LeftInverse, blockDiag_blockDiagonal, blockDiagonalAddMonoidHom, continuous_id, continuous_id.matrix_blockDiag, continuous_id.matrix_blockDiagonal, map_tsum, matrix_blockDiag, matrix_blockDiagonal
-/
theorem Matrix.blockDiagonal_tsum [DecidableEq p] [T2Space R] {f : X -> p -> Matrix m n R} :
    blockDiagonal (∑'[L] x, f x) = ∑'[L] x, blockDiagonal (f x) :=
  Function.LeftInverse.map_tsum (g := blockDiagonalAddMonoidHom m n p R) f
    continuous_id.matrix_blockDiagonal continuous_id.matrix_blockDiag blockDiag_blockDiagonal

/--
theorem `HasSum.matrix_blockDiag` / 定理 `HasSum.matrix_blockDiag`

English:
theorem HasSum.matrix_blockDiag
  statement: {f : X -> Matrix (m × p) (n × p) R} {a : Matrix (m × p) (n × p) R}
  proof: (hf.map (blockDiagAddMonoidHom m n p R) <| Continuous.matrix_blockDiag continuous_id :)

中文:
定理 HasSum.matrix_blockDiag
  结论: {f : X -> Matrix (m × p) (n × p) R} {a : Matrix (m × p) (n × p) R}
  证明: (hf.map (blockDiagAddMonoidHom m n p R) <| Continuous.matrix_blockDiag continuous_id :)

Depends on / 依赖: Continuous, Continuous.matrix_blockDiag, blockDiagAddMonoidHom, continuous_id, hf.map, matrix_blockDiag
-/
theorem HasSum.matrix_blockDiag {f : X -> Matrix (m × p) (n × p) R} {a : Matrix (m × p) (n × p) R}
    (hf : HasSum f a L) : HasSum (fun x => blockDiag (f x)) (blockDiag a) L :=
  (hf.map (blockDiagAddMonoidHom m n p R) <| Continuous.matrix_blockDiag continuous_id :)

/--
theorem `Summable.matrix_blockDiag` / 定理 `Summable.matrix_blockDiag`

English:
theorem Summable.matrix_blockDiag
  given: {f : X -> Matrix (m × p) (n × p) R} (hf : Summable f L)
  proof: hf.hasSum.matrix_blockDiag.summable

中文:
定理 Summable.matrix_blockDiag
  条件: {f : X -> Matrix (m × p) (n × p) R} (hf : Summable f L)
  证明: hf.hasSum.matrix_blockDiag.summable

Depends on / 依赖: hasSum, hf.hasSum.matrix_blockDiag.summable, matrix_blockDiag, summable
-/
theorem Summable.matrix_blockDiag {f : X -> Matrix (m × p) (n × p) R} (hf : Summable f L) :
    Summable (fun x => blockDiag (f x)) L :=
  hf.hasSum.matrix_blockDiag.summable

/--
theorem `HasSum.matrix_blockDiagonal'` / 定理 `HasSum.matrix_blockDiagonal'`

English:
theorem HasSum.matrix_blockDiagonal'
  statement: [DecidableEq l] {f : X -> forall i, Matrix (m' i) (n' i) R}
  proof: hf.map (blockDiagonal'AddMonoidHom m' n' R) continuous_id.matrix_blockDiagonal'

中文:
定理 HasSum.matrix_blockDiagonal'
  结论: [DecidableEq l] {f : X -> 对任意 i, Matrix (m' i) (n' i) R}
  证明: hf.map (blockDiagonal'AddMonoidHom m' n' R) continuous_id.matrix_blockDiagonal'

Depends on / 依赖: AddMonoidHom, blockDiagonal, continuous_id, continuous_id.matrix_blockDiagonal, hf.map, matrix_blockDiagonal
-/
theorem HasSum.matrix_blockDiagonal' [DecidableEq l] {f : X -> forall i, Matrix (m' i) (n' i) R}
    {a : forall i, Matrix (m' i) (n' i) R} (hf : HasSum f a L) :
    HasSum (fun x => blockDiagonal' (f x)) (blockDiagonal' a) L :=
  hf.map (blockDiagonal'AddMonoidHom m' n' R) continuous_id.matrix_blockDiagonal'

/--
theorem `Summable.matrix_blockDiagonal'` / 定理 `Summable.matrix_blockDiagonal'`

English:
theorem Summable.matrix_blockDiagonal'
  statement: [DecidableEq l] {f : X -> forall i, Matrix (m' i) (n' i) R}
  proof: hf.hasSum.matrix_blockDiagonal'.summable

中文:
定理 Summable.matrix_blockDiagonal'
  结论: [DecidableEq l] {f : X -> 对任意 i, Matrix (m' i) (n' i) R}
  证明: hf.hasSum.matrix_blockDiagonal'.summable

Depends on / 依赖: hasSum, hf.hasSum.matrix_blockDiagonal, matrix_blockDiagonal, summable
-/
theorem Summable.matrix_blockDiagonal' [DecidableEq l] {f : X -> forall i, Matrix (m' i) (n' i) R}
    (hf : Summable f L) : Summable (fun x => blockDiagonal' (f x)) L :=
  hf.hasSum.matrix_blockDiagonal'.summable

/--
theorem `summable_matrix_blockDiagonal'` / 定理 `summable_matrix_blockDiagonal'`

English:
theorem summable_matrix_blockDiagonal'
  given: [DecidableEq l] {f : X -> forall i, Matrix (m' i) (n' i) R}
  proof: Summable.map_iff_of_leftInverse (blockDiagonal'AddMonoidHom m' n' R)
    (blockDiag'AddMonoidHom m' n' R) continuous_id.matrix_blockDiagonal'
    continuous_id.matrix_blockDiag' fun A => blockDiag'_blockDiagonal' A

中文:
定理 summable_matrix_blockDiagonal'
  条件: [DecidableEq l] {f : X -> 对任意 i, Matrix (m' i) (n' i) R}
  证明: Summable.map_iff_of_leftInverse (blockDiagonal'AddMonoidHom m' n' R)
    (blockDiag'AddMonoidHom m' n' R) continuous_id.matrix_blockDiagonal'
    continuous_id.matrix_blockDiag' fun A => blockDiag'_blockDiagonal' A

Depends on / 依赖: AddMonoidHom, Summable, Summable.map_iff_of_leftInverse, _blockDiagonal, blockDiag, blockDiagonal, continuous_id, continuous_id.matrix_blockDiag, continuous_id.matrix_blockDiagonal, map_iff_of_leftInverse, matrix_blockDiag, matrix_blockDiagonal
-/
theorem summable_matrix_blockDiagonal' [DecidableEq l] {f : X -> forall i, Matrix (m' i) (n' i) R} :
    (Summable (fun x => blockDiagonal' (f x)) L) ↔ Summable f L :=
  Summable.map_iff_of_leftInverse (blockDiagonal'AddMonoidHom m' n' R)
    (blockDiag'AddMonoidHom m' n' R) continuous_id.matrix_blockDiagonal'
    continuous_id.matrix_blockDiag' fun A => blockDiag'_blockDiagonal' A

/--
theorem `Matrix.blockDiagonal'_tsum` / 定理 `Matrix.blockDiagonal'_tsum`

English:
theorem Matrix.blockDiagonal'_tsum
  statement: [DecidableEq l] [T2Space R]
  proof: Function.LeftInverse.map_tsum (g := blockDiagonal'AddMonoidHom m' n' R) f
    continuous_id.matrix_blockDiagonal' continuous_id.matrix_blockDiag' blockDiag'_blockDiagonal'

中文:
定理 Matrix.blockDiagonal'_tsum
  结论: [DecidableEq l] [T2Space R]
  证明: Function.LeftInverse.map_tsum (g := blockDiagonal'AddMonoidHom m' n' R) f
    continuous_id.matrix_blockDiagonal' continuous_id.matrix_blockDiag' blockDiag'_blockDiagonal'
-/
theorem Matrix.blockDiagonal'_tsum [DecidableEq l] [T2Space R]
    {f : X -> forall i, Matrix (m' i) (n' i) R} :
    blockDiagonal' (∑'[L] x, f x) = ∑'[L] x, blockDiagonal' (f x) :=
  Function.LeftInverse.map_tsum (g := blockDiagonal'AddMonoidHom m' n' R) f
    continuous_id.matrix_blockDiagonal' continuous_id.matrix_blockDiag' blockDiag'_blockDiagonal'

/--
theorem `HasSum.matrix_blockDiag'` / 定理 `HasSum.matrix_blockDiag'`

English:
theorem HasSum.matrix_blockDiag'
  statement: {f : X -> Matrix (Σ i, m' i) (Σ i, n' i) R}
  proof: hf.map (blockDiag'AddMonoidHom m' n' R) continuous_id.matrix_blockDiag'

中文:
定理 HasSum.matrix_blockDiag'
  结论: {f : X -> Matrix (Σ i, m' i) (Σ i, n' i) R}
  证明: hf.map (blockDiag'AddMonoidHom m' n' R) continuous_id.matrix_blockDiag'

Depends on / 依赖: AddMonoidHom, blockDiag, continuous_id, continuous_id.matrix_blockDiag, hf.map, matrix_blockDiag
-/
theorem HasSum.matrix_blockDiag' {f : X -> Matrix (Σ i, m' i) (Σ i, n' i) R}
    {a : Matrix (Σ i, m' i) (Σ i, n' i) R} (hf : HasSum f a L) :
    HasSum (fun x => blockDiag' (f x)) (blockDiag' a) L :=
  hf.map (blockDiag'AddMonoidHom m' n' R) continuous_id.matrix_blockDiag'

/--
theorem `Summable.matrix_blockDiag'` / 定理 `Summable.matrix_blockDiag'`

English:
theorem Summable.matrix_blockDiag'
  given: {f : X -> Matrix (Σ i, m' i) (Σ i, n' i) R} (hf : Summable f L)
  proof: hf.hasSum.matrix_blockDiag'.summable

中文:
定理 Summable.matrix_blockDiag'
  条件: {f : X -> Matrix (Σ i, m' i) (Σ i, n' i) R} (hf : Summable f L)
  证明: hf.hasSum.matrix_blockDiag'.summable

Depends on / 依赖: hasSum, hf.hasSum.matrix_blockDiag, matrix_blockDiag, summable
-/
theorem Summable.matrix_blockDiag' {f : X -> Matrix (Σ i, m' i) (Σ i, n' i) R} (hf : Summable f L) :
    Summable (fun x => blockDiag' (f x)) L :=
  hf.hasSum.matrix_blockDiag'.summable

end BlockMatrices

end tsum
