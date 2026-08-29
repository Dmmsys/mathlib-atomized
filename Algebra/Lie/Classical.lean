/-
Copyright (c) 2020 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Data.Matrix.Basis
public import Mathlib.Algebra.Lie.Abelian
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Algebra.Lie.SkewAdjoint
public import Mathlib.LinearAlgebra.SymplecticGroup

/-!
# Classical Lie algebras

This file is the place to find definitions and basic properties of the classical Lie algebras:
  * Aₗ = sl(l+1)
  * Bₗ ≃ so(l+1, l) ≃ so(2l+1)
  * Cₗ = sp(l)
  * Dₗ ≃ so(l, l) ≃ so(2l)

## Main definitions

  * `LieAlgebra.SpecialLinear.sl`
  * `LieAlgebra.Symplectic.sp`
  * `LieAlgebra.Orthogonal.so`
  * `LieAlgebra.Orthogonal.so'`
  * `LieAlgebra.Orthogonal.soIndefiniteEquiv`
  * `LieAlgebra.Orthogonal.typeD`
  * `LieAlgebra.Orthogonal.typeB`
  * `LieAlgebra.Orthogonal.typeDEquivSo'`
  * `LieAlgebra.Orthogonal.typeBEquivSo'`

## Implementation notes

### Matrices or endomorphisms

Given a finite type and a commutative ring, the corresponding square matrices are equivalent to the
endomorphisms of the corresponding finite-rank free module as Lie algebras, see `lieEquivMatrix'`.
We can thus define the classical Lie algebras as Lie subalgebras either of matrices or of
endomorphisms. We have opted for the former. At the time of writing (August 2020) it is unclear
which approach should be preferred so the choice should be assumed to be somewhat arbitrary.

### Diagonal quadratic form or diagonal Cartan subalgebra

For the algebras of type `B` and `D`, there are two natural definitions. For example since the
`2l × 2l` matrix:
$$
  J = \left[\begin{array}{cc}
              0_l & 1_l\\
              1_l & 0_l
            \end{array}\right]
$$
defines a symmetric bilinear form equivalent to that defined by the identity matrix `I`, we can
define the algebras of type `D` to be the Lie subalgebra of skew-adjoint matrices either for `J` or
for `I`. Both definitions have their advantages (in particular the `J`-skew-adjoint matrices define
a Lie algebra for which the diagonal matrices form a Cartan subalgebra) and so we provide both.
We thus also provide equivalences `typeDEquivSo'`, `soIndefiniteEquiv` which show the two
definitions are equivalent. Similarly for the algebras of type `B`.

## Tags

classical lie algebra, special linear, symplectic, orthogonal
-/

@[expose] public section


universe u₁ u₂

namespace LieAlgebra

open Matrix

variable (n p q l : Type*) (R : Type u₂)
variable [DecidableEq p] [DecidableEq q] [DecidableEq l]
variable [CommRing R]

@[simp]
/--
theorem `matrix_trace_commutator_zero` / 定理 `matrix_trace_commutator_zero`

English:
theorem matrix_trace_commutator_zero
  given: [Fintype n] (X Y : Matrix n n R)
  statement: Matrix.trace ⁅X, Y⁆ = 0
  proof: calc
    _ = Matrix.trace (X * Y) - Matrix.trace (Y * X) := trace_sub _ _
    _ = Matrix.trace (X * Y) - Matrix.trace (X * Y) :=
      (congr_arg (fun x => _ - x) (Matrix.trace_mul_comm Y X))
    _ = 0 := sub_self _

中文:
定理 matrix_trace_commutator_zero
  条件: [有限类型 n] (X Y : 矩阵 n n R)
  结论: 矩阵.trace ⁅X, Y⁆ = 0
  证明: calc
    _ = Matrix.trace (X * Y) - Matrix.trace (Y * X) := trace_sub _ _
    _ = Matrix.trace (X * Y) - Matrix.trace (X * Y) :=
      (congr_arg (fun x => _ - x) (Matrix.trace_mul_comm Y X))
    _ = 0 := sub_self _

Depends on / 依赖: Matrix, Matrix.trace, Matrix.trace_mul_comm, congr_arg, sub_self, trace_mul_comm, trace_sub
-/
theorem matrix_trace_commutator_zero [Fintype n] (X Y : Matrix n n R) : Matrix.trace ⁅X, Y⁆ = 0 :=
  calc
    _ = Matrix.trace (X * Y) - Matrix.trace (Y * X) := trace_sub _ _
    _ = Matrix.trace (X * Y) - Matrix.trace (X * Y) :=
      (congr_arg (fun x => _ - x) (Matrix.trace_mul_comm Y X))
    _ = 0 := sub_self _

variable [DecidableEq n]
attribute [local instance 100] LieRing.ofAssociativeRing

namespace SpecialLinear

/--
Definition of `sl` / `sl` 的定义

English:
definition sl
  signature: [Fintype n]
  body: { LinearMap.ker (Matrix.traceLinearMap n R R) with
lie_mem' := fun _ _ => LinearMap.mem_ker.2 matrix_trace_commutator_zero _ _ _ _ }

中文:
定义 sl
  签名: [有限类型 n]
  定义体: { LinearMap.ker (Matrix.traceLinearMap n R R) with
lie_mem' := fun _ _ => LinearMap.mem_ker.2 matrix_trace_commutator_zero _ _ _ _ }

Depends on / 依赖: LinearMap, LinearMap.ker, LinearMap.mem_ker, Matrix, Matrix.traceLinearMap, lie_mem, matrix_trace_commutator_zero, mem_ker, traceLinearMap
-/
def sl [Fintype n] : LieSubalgebra R (Matrix n n R) :=
  { LinearMap.ker (Matrix.traceLinearMap n R R) with
lie_mem' := fun _ _ => LinearMap.mem_ker.2 matrix_trace_commutator_zero _ _ _ _ }

/--
theorem `sl_bracket` / 定理 `sl_bracket`

English:
theorem sl_bracket
  given: [Fintype n] (A B : sl n R)
  statement: ⁅A, B⁆.val = A.val * B.val - B.val * A.val
  proof: rfl

中文:
定理 sl_bracket
  条件: [有限类型 n] (A B : sl n R)
  结论: ⁅A, B⁆.val = A.val * B.val - B.val * A.val
  证明: rfl
-/
theorem sl_bracket [Fintype n] (A B : sl n R) : ⁅A, B⁆.val = A.val * B.val - B.val * A.val :=
  rfl

section ElementaryBasis

variable {n R} [Fintype n] (i j k : n)

/--
Definition of `single` / `single` 的定义

English:
definition single
  signature: (h : i != j)
  body: .codRestrict _ fun r => Matrix.trace_single_eq_of_ne i j r h Matrix.singleLinearMap R i j

@[simp]

中文:
定义 single
  签名: (h : i != j)
  定义体: .codRestrict _ fun r => Matrix.trace_single_eq_of_ne i j r h Matrix.singleLinearMap R i j

@[simp]

Depends on / 依赖: Matrix, Matrix.singleLinearMap, Matrix.trace_single_eq_of_ne, codRestrict, singleLinearMap, trace_single_eq_of_ne
-/
def single (h : i != j) : R ->ₗ[R] sl n R :=
.codRestrict _ fun r => Matrix.trace_single_eq_of_ne i j r h Matrix.singleLinearMap R i j

@[simp]
/--
theorem `val_single` / 定理 `val_single`

English:
theorem val_single
  given: (h : i != j) (r : R)
  statement: (single i j h r).val = Matrix.single i j r
  proof: rfl

中文:
定理 val_single
  条件: (h : i != j) (r : R)
  结论: (single i j h r).val = 矩阵.single i j r
  证明: rfl
-/
theorem val_single (h : i != j) (r : R) : (single i j h r).val = Matrix.single i j r :=
  rfl

/--
Definition of `singleSubSingle` / `singleSubSingle` 的定义

English:
definition singleSubSingle
  signature: : R ->ₗ[R] sl n R
  body: LinearMap.codRestrict _ (Matrix.singleLinearMap R i i - Matrix.singleLinearMap R j j) fun r =>
LinearMap.sub_mem_ker_iff.mpr by simp

@[simp]

中文:
定义 singleSubSingle
  签名: : R ->ₗ[R] sl n R
  定义体: LinearMap.codRestrict _ (Matrix.singleLinearMap R i i - Matrix.singleLinearMap R j j) fun r =>
LinearMap.sub_mem_ker_iff.mpr by simp

@[simp]

Depends on / 依赖: LinearMap, LinearMap.codRestrict, LinearMap.sub_mem_ker_iff.mpr, Matrix, Matrix.singleLinearMap, codRestrict, singleLinearMap, sub_mem_ker_iff
-/
def singleSubSingle : R ->ₗ[R] sl n R :=
  LinearMap.codRestrict _ (Matrix.singleLinearMap R i i - Matrix.singleLinearMap R j j) fun r =>
LinearMap.sub_mem_ker_iff.mpr by simp

@[simp]
/--
theorem `val_singleSubSingle` / 定理 `val_singleSubSingle`

English:
theorem val_singleSubSingle
  given: (r : R)
  proof: rfl

@[simp]

中文:
定理 val_singleSubSingle
  条件: (r : R)
  证明: rfl

@[simp]
-/
theorem val_singleSubSingle (r : R) :
    (singleSubSingle i j r).val = Matrix.single i i r - Matrix.single j j r :=
  rfl

@[simp]
/--
theorem `singleSubSingle_add_singleSubSingle` / 定理 `singleSubSingle_add_singleSubSingle`

English:
theorem singleSubSingle_add_singleSubSingle
  given: (r : R)
  proof: by
  ext : 1; simp

@[simp]

中文:
定理 singleSubSingle_add_singleSubSingle
  条件: (r : R)
  证明: by
  ext : 1; simp

@[simp]
-/
theorem singleSubSingle_add_singleSubSingle (r : R) :
    singleSubSingle i j r + singleSubSingle j k r = singleSubSingle i k r := by
  ext : 1; simp

@[simp]
/--
theorem `singleSubSingle_sub_singleSubSingle` / 定理 `singleSubSingle_sub_singleSubSingle`

English:
theorem singleSubSingle_sub_singleSubSingle
  given: (r : R)
  proof: by
  ext : 1; simp

@[simp]

中文:
定理 singleSubSingle_sub_singleSubSingle
  条件: (r : R)
  证明: by
  ext : 1; simp

@[simp]
-/
theorem singleSubSingle_sub_singleSubSingle (r : R) :
    singleSubSingle i k r - singleSubSingle i j r = singleSubSingle j k r := by
  ext : 1; simp

@[simp]
/--
theorem `singleSubSingle_sub_singleSubSingle'` / 定理 `singleSubSingle_sub_singleSubSingle'`

English:
theorem singleSubSingle_sub_singleSubSingle'
  given: (r : R)
  proof: by
  ext : 1; simp

中文:
定理 singleSubSingle_sub_singleSubSingle'
  条件: (r : R)
  证明: by
  ext : 1; simp
-/
theorem singleSubSingle_sub_singleSubSingle' (r : R) :
    singleSubSingle i k r - singleSubSingle j k r = singleSubSingle i j r := by
  ext : 1; simp

end ElementaryBasis

/--
theorem `sl_non_abelian` / 定理 `sl_non_abelian`

English:
theorem sl_non_abelian
  given: [Fintype n] [Nontrivial R] (h : 1 < Fintype.card n)
  proof: by
  rcases Fintype.exists_pair_of_one_lt_card h with ⟨i, j, hij⟩
  let A := single i j hij (1 : R)
  let B := single j i hij.symm (1 : R)
  intro c
  have c' : A.val * B.val = B.val * A.val := by
    rw [← sub_eq_zero]; rw [← sl_bracket]; rw [c.trivial]; rw [ZeroMemClass.coe_zero]
  simpa [A, B, Ma

中文:
定理 sl_non_abelian
  条件: [有限类型 n] [非平凡 R] (h : 1 < 有限类型.card n)
  证明: by
  rcases Fintype.exists_pair_of_one_lt_card h with ⟨i, j, hij⟩
  let A := single i j hij (1 : R)
  let B := single j i hij.symm (1 : R)
  intro c
  have c' : A.val * B.val = B.val * A.val := by
    rw [← sub_eq_zero]; rw [← sl_bracket]; rw [c.trivial]; rw [ZeroMemClass.coe_zero]
  simpa [A, B, Ma

Depends on / 依赖: A.val, B.val, Fintype, Fintype.exists_pair_of_one_lt_card, Matrix, Matrix.mul_apply, Matrix.single, ZeroMemClass, ZeroMemClass.coe_zero, c.trivial, coe_zero, congr_fun, exists_pair_of_one_lt_card, hij.symm, mul_apply, single, sl_bracket, sub_eq_zero
-/
theorem sl_non_abelian [Fintype n] [Nontrivial R] (h : 1 < Fintype.card n) :
    ¬IsLieAbelian (sl n R) := by
  rcases Fintype.exists_pair_of_one_lt_card h with ⟨i, j, hij⟩
  let A := single i j hij (1 : R)
  let B := single j i hij.symm (1 : R)
  intro c
  have c' : A.val * B.val = B.val * A.val := by
    rw [← sub_eq_zero]; rw [← sl_bracket]; rw [c.trivial]; rw [ZeroMemClass.coe_zero]
  simpa [A, B, Matrix.single, Matrix.mul_apply, hij.symm] using congr_fun (congr_fun c' i) i

end SpecialLinear

namespace Symplectic

/--
Definition of `sp` / `sp` 的定义

English:
definition sp
  signature: [Fintype l]
  body: skewAdjointMatricesLieSubalgebra (Matrix.J l R)

中文:
定义 sp
  签名: [有限类型 l]
  定义体: skewAdjointMatricesLieSubalgebra (Matrix.J l R)

Depends on / 依赖: Matrix, Matrix.J, skewAdjointMatricesLieSubalgebra
-/
def sp [Fintype l] : LieSubalgebra R (Matrix (l oplus l) (l oplus l) R) :=
  skewAdjointMatricesLieSubalgebra (Matrix.J l R)

end Symplectic

namespace Orthogonal

/--
Definition of `so` / `so` 的定义

English:
definition so
  signature: [Fintype n]
  body: skewAdjointMatricesLieSubalgebra (1 : Matrix n n R)

@[simp]

中文:
定义 so
  签名: [有限类型 n]
  定义体: skewAdjointMatricesLieSubalgebra (1 : Matrix n n R)

@[simp]

Depends on / 依赖: Matrix, skewAdjointMatricesLieSubalgebra
-/
def so [Fintype n] : LieSubalgebra R (Matrix n n R) :=
  skewAdjointMatricesLieSubalgebra (1 : Matrix n n R)

@[simp]
/--
theorem `mem_so` / 定理 `mem_so`

English:
theorem mem_so
  given: [Fintype n] (A : Matrix n n R)
  statement: A in so n R ↔ Aᵀ = -A
  proof: by
  rw [so]; rw [mem_skewAdjointMatricesLieSubalgebra]; rw [mem_skewAdjointMatricesSubmodule]
  simp only [Matrix.IsSkewAdjoint, Matrix.IsAdjointPair, Matrix.mul_one, Matrix.one_mul]

中文:
定理 mem_so
  条件: [有限类型 n] (A : 矩阵 n n R)
  结论: A in so n R ↔ Aᵀ = -A
  证明: by
  rw [so]; rw [mem_skewAdjointMatricesLieSubalgebra]; rw [mem_skewAdjointMatricesSubmodule]
  simp only [Matrix.IsSkewAdjoint, Matrix.IsAdjointPair, Matrix.mul_one, Matrix.one_mul]

Depends on / 依赖: IsAdjointPair, IsSkewAdjoint, Matrix, Matrix.IsAdjointPair, Matrix.IsSkewAdjoint, Matrix.mul_one, Matrix.one_mul, mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule, mul_one, one_mul
-/
theorem mem_so [Fintype n] (A : Matrix n n R) : A in so n R ↔ Aᵀ = -A := by
  rw [so]; rw [mem_skewAdjointMatricesLieSubalgebra]; rw [mem_skewAdjointMatricesSubmodule]
  simp only [Matrix.IsSkewAdjoint, Matrix.IsAdjointPair, Matrix.mul_one, Matrix.one_mul]

/--
Definition of `indefiniteDiagonal` / `indefiniteDiagonal` 的定义

English:
definition indefiniteDiagonal
  signature: : Matrix (p oplus q) (p oplus q) R
  body: Matrix.diagonal Sum.elim (fun _ => 1) fun _ => -1

中文:
定义 indefiniteDiagonal
  签名: : 矩阵 (p oplus q) (p oplus q) R
  定义体: Matrix.diagonal Sum.elim (fun _ => 1) fun _ => -1

Depends on / 依赖: Matrix, Matrix.diagonal, Sum.elim, diagonal
-/
def indefiniteDiagonal : Matrix (p oplus q) (p oplus q) R :=
Matrix.diagonal Sum.elim (fun _ => 1) fun _ => -1

/--
Definition of `so'` / `so'` 的定义

English:
definition so'
  signature: [Fintype p] [Fintype q]
  body: skewAdjointMatricesLieSubalgebra indefiniteDiagonal p q R

中文:
定义 so'
  签名: [有限类型 p] [有限类型 q]
  定义体: skewAdjointMatricesLieSubalgebra indefiniteDiagonal p q R

Depends on / 依赖: indefiniteDiagonal, skewAdjointMatricesLieSubalgebra
-/
def so' [Fintype p] [Fintype q] : LieSubalgebra R (Matrix (p oplus q) (p oplus q) R) :=
skewAdjointMatricesLieSubalgebra indefiniteDiagonal p q R

/--
Definition of `Pso` / `Pso` 的定义

English:
definition Pso
  signature: (i : R)
  body: Matrix.diagonal Sum.elim (fun _ => 1) fun _ => i

中文:
定义 Pso
  签名: (i : R)
  定义体: Matrix.diagonal Sum.elim (fun _ => 1) fun _ => i

Depends on / 依赖: Matrix, Matrix.diagonal, Sum.elim, diagonal
-/
def Pso (i : R) : Matrix (p oplus q) (p oplus q) R :=
Matrix.diagonal Sum.elim (fun _ => 1) fun _ => i

variable [Fintype p] [Fintype q]

/--
theorem `pso_inv` / 定理 `pso_inv`

English:
theorem pso_inv
  given: {i : R} (hi : i * i = -1)
  statement: Pso p q R i * Pso p q R (-i) = 1
  proof: by
  ext (x y); rcases x with ⟨x⟩ | ⟨x⟩ <;> rcases y with ⟨y⟩ | ⟨y⟩
  · -- x y : p
    by_cases h : x = y <;>
    simp [Pso, h, one_apply]
  · -- x : p, y : q
    simp [Pso]
  · -- x : q, y : p
    simp [Pso]
  · -- x y : q
    by_cases h : x = y <;>
    simp [Pso, h, hi, one_apply]

中文:
定理 pso_inv
  条件: {i : R} (hi : i * i = -1)
  结论: Pso p q R i * Pso p q R (-i) = 1
  证明: by
  ext (x y); rcases x with ⟨x⟩ | ⟨x⟩ <;> rcases y with ⟨y⟩ | ⟨y⟩
  · -- x y : p
    by_cases h : x = y <;>
    simp [Pso, h, one_apply]
  · -- x : p, y : q
    simp [Pso]
  · -- x : q, y : p
    simp [Pso]
  · -- x y : q
    by_cases h : x = y <;>
    simp [Pso, h, hi, one_apply]

Depends on / 依赖: one_apply
-/
theorem pso_inv {i : R} (hi : i * i = -1) : Pso p q R i * Pso p q R (-i) = 1 := by
  ext (x y); rcases x with ⟨x⟩ | ⟨x⟩ <;> rcases y with ⟨y⟩ | ⟨y⟩
  · -- x y : p
    by_cases h : x = y <;>
    simp [Pso, h, one_apply]
  · -- x : p, y : q
    simp [Pso]
  · -- x : q, y : p
    simp [Pso]
  · -- x y : q
    by_cases h : x = y <;>
    simp [Pso, h, hi, one_apply]

/-- There is a constructive inverse of `Pso p q R i`. -/
@[instance_reducible]
/--
Definition of `invertiblePso` / `invertiblePso` 的定义

English:
definition invertiblePso
  signature: {i : R} (hi : i * i = -1)
  body: invertibleOfRightInverse _ _ (pso_inv p q R hi)

中文:
定义 invertiblePso
  签名: {i : R} (hi : i * i = -1)
  定义体: invertibleOfRightInverse _ _ (pso_inv p q R hi)

Depends on / 依赖: invertibleOfRightInverse, pso_inv
-/
def invertiblePso {i : R} (hi : i * i = -1) : Invertible (Pso p q R i) :=
  invertibleOfRightInverse _ _ (pso_inv p q R hi)

/--
theorem `indefiniteDiagonal_transform` / 定理 `indefiniteDiagonal_transform`

English:
theorem indefiniteDiagonal_transform
  given: {i : R} (hi : i * i = -1)
  proof: by
  ext (x y); rcases x with ⟨x⟩ | ⟨x⟩ <;> rcases y with ⟨y⟩ | ⟨y⟩
  · -- x y : p
    by_cases h : x = y <;>
    simp [Pso, indefiniteDiagonal, h, one_apply]
  · -- x : p, y : q
    simp [Pso, indefiniteDiagonal]
  · -- x : q, y : p
    simp [Pso, indefiniteDiagonal]
  · -- x y : q
    by_cases h :

中文:
定理 indefiniteDiagonal_transform
  条件: {i : R} (hi : i * i = -1)
  证明: by
  ext (x y); rcases x with ⟨x⟩ | ⟨x⟩ <;> rcases y with ⟨y⟩ | ⟨y⟩
  · -- x y : p
    by_cases h : x = y <;>
    simp [Pso, indefiniteDiagonal, h, one_apply]
  · -- x : p, y : q
    simp [Pso, indefiniteDiagonal]
  · -- x : q, y : p
    simp [Pso, indefiniteDiagonal]
  · -- x y : q
    by_cases h :

Depends on / 依赖: indefiniteDiagonal, one_apply
-/
theorem indefiniteDiagonal_transform {i : R} (hi : i * i = -1) :
    (Pso p q R i)ᵀ * indefiniteDiagonal p q R * Pso p q R i = 1 := by
  ext (x y); rcases x with ⟨x⟩ | ⟨x⟩ <;> rcases y with ⟨y⟩ | ⟨y⟩
  · -- x y : p
    by_cases h : x = y <;>
    simp [Pso, indefiniteDiagonal, h, one_apply]
  · -- x : p, y : q
    simp [Pso, indefiniteDiagonal]
  · -- x : q, y : p
    simp [Pso, indefiniteDiagonal]
  · -- x y : q
    by_cases h : x = y <;>
    simp [Pso, indefiniteDiagonal, h, hi, one_apply]

/--
Definition of `soIndefiniteEquiv` / `soIndefiniteEquiv` 的定义

English:
definition soIndefiniteEquiv
  signature: {i : R} (hi : i * i = -1)
  body: by
  apply
    (skewAdjointMatricesLieSubalgebraEquiv (indefiniteDiagonal p q R) (Pso p q R i)
        (invertiblePso p q R hi)).trans
  apply LieEquiv.ofEq
  ext A; rw [indefiniteDiagonal_transform p q R hi]; rfl

中文:
定义 soIndefiniteEquiv
  签名: {i : R} (hi : i * i = -1)
  定义体: by
  apply
    (skewAdjointMatricesLieSubalgebraEquiv (indefiniteDiagonal p q R) (Pso p q R i)
        (invertiblePso p q R hi)).trans
  apply LieEquiv.ofEq
  ext A; rw [indefiniteDiagonal_transform p q R hi]; rfl

Depends on / 依赖: LieEquiv, LieEquiv.ofEq, indefiniteDiagonal, indefiniteDiagonal_transform, invertiblePso, skewAdjointMatricesLieSubalgebraEquiv
-/
noncomputable def soIndefiniteEquiv {i : R} (hi : i * i = -1) : so' p q R ≃ₗ⁅R⁆ so (p oplus q) R := by
  apply
    (skewAdjointMatricesLieSubalgebraEquiv (indefiniteDiagonal p q R) (Pso p q R i)
        (invertiblePso p q R hi)).trans
  apply LieEquiv.ofEq
  ext A; rw [indefiniteDiagonal_transform p q R hi]; rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `soIndefiniteEquiv_apply` / 定理 `soIndefiniteEquiv_apply`

English:
theorem soIndefiniteEquiv_apply
  given: {i : R} (hi : i * i = -1) (A : so' p q R)
  proof: by
  rw [soIndefiniteEquiv]; rw [LieEquiv.trans_apply]; rw [LieEquiv.ofEq_apply]
  simp only [so', skewAdjointMatricesLieSubalgebraEquiv_apply]

中文:
定理 soIndefiniteEquiv_apply
  条件: {i : R} (hi : i * i = -1) (A : so' p q R)
  证明: by
  rw [soIndefiniteEquiv]; rw [LieEquiv.trans_apply]; rw [LieEquiv.ofEq_apply]
  simp only [so', skewAdjointMatricesLieSubalgebraEquiv_apply]

Depends on / 依赖: LieEquiv, LieEquiv.ofEq_apply, LieEquiv.trans_apply, ofEq_apply, skewAdjointMatricesLieSubalgebraEquiv_apply, soIndefiniteEquiv, trans_apply
-/
theorem soIndefiniteEquiv_apply {i : R} (hi : i * i = -1) (A : so' p q R) :
    (soIndefiniteEquiv p q R hi A : Matrix (p oplus q) (p oplus q) R) =
      (Pso p q R i)⁻¹ * (A : Matrix (p oplus q) (p oplus q) R) * Pso p q R i := by
  rw [soIndefiniteEquiv]; rw [LieEquiv.trans_apply]; rw [LieEquiv.ofEq_apply]
  simp only [so', skewAdjointMatricesLieSubalgebraEquiv_apply]

/--
Definition of `JD` / `JD` 的定义

English:
definition JD
  signature: : Matrix (l oplus l) (l oplus l) R
  body: Matrix.fromBlocks 0 1 1 0

中文:
定义 JD
  签名: : 矩阵 (l oplus l) (l oplus l) R
  定义体: Matrix.fromBlocks 0 1 1 0

Depends on / 依赖: Matrix, Matrix.fromBlocks, fromBlocks
-/
def JD : Matrix (l oplus l) (l oplus l) R :=
  Matrix.fromBlocks 0 1 1 0

/--
Definition of `typeD` / `typeD` 的定义

English:
definition typeD
  signature: [Fintype l]
  body: skewAdjointMatricesLieSubalgebra (JD l R)

中文:
定义 typeD
  签名: [有限类型 l]
  定义体: skewAdjointMatricesLieSubalgebra (JD l R)

Depends on / 依赖: skewAdjointMatricesLieSubalgebra
-/
def typeD [Fintype l] :=
  skewAdjointMatricesLieSubalgebra (JD l R)

/--
Definition of `PD` / `PD` 的定义

English:
definition PD
  signature: : Matrix (l oplus l) (l oplus l) R
  body: Matrix.fromBlocks 1 (-1) 1 1

中文:
定义 PD
  签名: : 矩阵 (l oplus l) (l oplus l) R
  定义体: Matrix.fromBlocks 1 (-1) 1 1

Depends on / 依赖: Matrix, Matrix.fromBlocks, fromBlocks
-/
def PD : Matrix (l oplus l) (l oplus l) R :=
  Matrix.fromBlocks 1 (-1) 1 1

/--
Definition of `S` / `S` 的定义

English:
definition S
  body: indefiniteDiagonal l l R

中文:
定义 S
  定义体: indefiniteDiagonal l l R

Depends on / 依赖: indefiniteDiagonal
-/
def S :=
  indefiniteDiagonal l l R

/--
theorem `s_as_blocks` / 定理 `s_as_blocks`

English:
theorem s_as_blocks
  statement: S l R = Matrix.fromBlocks 1 0 0 (-1)
  proof: by
  rw [← Matrix.diagonal_one]; rw [Matrix.diagonal_neg]; rw [Matrix.fromBlocks_diagonal]
  rfl

中文:
定理 s_as_blocks
  结论: S l R = 矩阵.fromBlocks 1 0 0 (-1)
  证明: by
  rw [← Matrix.diagonal_one]; rw [Matrix.diagonal_neg]; rw [Matrix.fromBlocks_diagonal]
  rfl

Depends on / 依赖: Matrix, Matrix.diagonal_neg, Matrix.diagonal_one, Matrix.fromBlocks_diagonal, diagonal_neg, diagonal_one, fromBlocks_diagonal
-/
theorem s_as_blocks : S l R = Matrix.fromBlocks 1 0 0 (-1) := by
  rw [← Matrix.diagonal_one]; rw [Matrix.diagonal_neg]; rw [Matrix.fromBlocks_diagonal]
  rfl

/--
theorem `jd_transform` / 定理 `jd_transform`

English:
theorem jd_transform
  given: [Fintype l]
  statement: (PD l R)ᵀ * JD l R * PD l R = (2 : R) • S l R
  proof: by
  have h : (PD l R)ᵀ * JD l R = Matrix.fromBlocks 1 1 1 (-1) := by
    simp [PD, JD, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
  rw [h]; rw [PD]; rw [s_as_blocks]; rw [Matrix.fromBlocks_multiply]; rw [Matrix.fromBlocks_smul]
  simp [two_smul]

中文:
定理 jd_transform
  条件: [有限类型 l]
  结论: (PD l R)ᵀ * JD l R * PD l R = (2 : R) • S l R
  证明: by
  have h : (PD l R)ᵀ * JD l R = Matrix.fromBlocks 1 1 1 (-1) := by
    simp [PD, JD, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
  rw [h]; rw [PD]; rw [s_as_blocks]; rw [Matrix.fromBlocks_multiply]; rw [Matrix.fromBlocks_smul]
  simp [two_smul]

Depends on / 依赖: Matrix, Matrix.fromBlocks, Matrix.fromBlocks_multiply, Matrix.fromBlocks_smul, Matrix.fromBlocks_transpose, fromBlocks, fromBlocks_multiply, fromBlocks_smul, fromBlocks_transpose, s_as_blocks, two_smul
-/
theorem jd_transform [Fintype l] : (PD l R)ᵀ * JD l R * PD l R = (2 : R) • S l R := by
  have h : (PD l R)ᵀ * JD l R = Matrix.fromBlocks 1 1 1 (-1) := by
    simp [PD, JD, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
  rw [h]; rw [PD]; rw [s_as_blocks]; rw [Matrix.fromBlocks_multiply]; rw [Matrix.fromBlocks_smul]
  simp [two_smul]

/--
theorem `pd_inv` / 定理 `pd_inv`

English:
theorem pd_inv
  given: [Fintype l] [Invertible (2 : R)]
  statement: PD l R * ⅟(2 : R) • (PD l R)ᵀ = 1
  proof: by
  rw [PD]; rw [Matrix.fromBlocks_transpose]; rw [Matrix.fromBlocks_smul]; rw [Matrix.fromBlocks_multiply]
  simp

中文:
定理 pd_inv
  条件: [有限类型 l] [可逆 (2 : R)]
  结论: PD l R * ⅟(2 : R) • (PD l R)ᵀ = 1
  证明: by
  rw [PD]; rw [Matrix.fromBlocks_transpose]; rw [Matrix.fromBlocks_smul]; rw [Matrix.fromBlocks_multiply]
  simp

Depends on / 依赖: Matrix, Matrix.fromBlocks_multiply, Matrix.fromBlocks_smul, Matrix.fromBlocks_transpose, fromBlocks_multiply, fromBlocks_smul, fromBlocks_transpose
-/
theorem pd_inv [Fintype l] [Invertible (2 : R)] : PD l R * ⅟(2 : R) • (PD l R)ᵀ = 1 := by
  rw [PD]; rw [Matrix.fromBlocks_transpose]; rw [Matrix.fromBlocks_smul]; rw [Matrix.fromBlocks_multiply]
  simp

/--
Instance `invertiblePD` / 实例 `invertiblePD`

English:
instance invertiblePD
  signature: [Fintype l] [Invertible (2 : R)]
  body: invertibleOfRightInverse _ _ (pd_inv l R)

中文:
实例 invertiblePD
  签名: [有限类型 l] [可逆 (2 : R)]
  定义体: invertibleOfRightInverse _ _ (pd_inv l R)

Depends on / 依赖: invertibleOfRightInverse, pd_inv
-/
instance invertiblePD [Fintype l] [Invertible (2 : R)] : Invertible (PD l R) :=
  invertibleOfRightInverse _ _ (pd_inv l R)

/--
Definition of `typeDEquivSo'` / `typeDEquivSo'` 的定义

English:
definition typeDEquivSo'
  signature: [Fintype l] [Invertible (2 : R)]
  body: by
  apply (skewAdjointMatricesLieSubalgebraEquiv (JD l R) (PD l R) (by infer_instance)).trans
  apply LieEquiv.ofEq
  ext A
  rw [jd_transform]; rw [← val_unitOfInvertible (2 : R)]; rw [← Units.smul_def]; rw [LieSubalgebra.mem_coe]; rw [mem_skewAdjointMatricesLieSubalgebra_unit_smul]
  rfl

中文:
定义 typeDEquivSo'
  签名: [有限类型 l] [可逆 (2 : R)]
  定义体: by
  apply (skewAdjointMatricesLieSubalgebraEquiv (JD l R) (PD l R) (by infer_instance)).trans
  apply LieEquiv.ofEq
  ext A
  rw [jd_transform]; rw [← val_unitOfInvertible (2 : R)]; rw [← Units.smul_def]; rw [LieSubalgebra.mem_coe]; rw [mem_skewAdjointMatricesLieSubalgebra_unit_smul]
  rfl

Depends on / 依赖: LieEquiv, LieEquiv.ofEq, LieSubalgebra, LieSubalgebra.mem_coe, Units.smul_def, infer_instance, jd_transform, mem_coe, mem_skewAdjointMatricesLieSubalgebra_unit_smul, skewAdjointMatricesLieSubalgebraEquiv, smul_def, val_unitOfInvertible
-/
noncomputable def typeDEquivSo' [Fintype l] [Invertible (2 : R)] : typeD l R ≃ₗ⁅R⁆ so' l l R := by
  apply (skewAdjointMatricesLieSubalgebraEquiv (JD l R) (PD l R) (by infer_instance)).trans
  apply LieEquiv.ofEq
  ext A
  rw [jd_transform]; rw [← val_unitOfInvertible (2 : R)]; rw [← Units.smul_def]; rw [LieSubalgebra.mem_coe]; rw [mem_skewAdjointMatricesLieSubalgebra_unit_smul]
  rfl

/--
Definition of `JB` / `JB` 的定义

English:
definition JB
  body: Matrix.fromBlocks ((2 : R) • (1 : Matrix Unit Unit R)) 0 0 (JD l R)

中文:
定义 JB
  定义体: Matrix.fromBlocks ((2 : R) • (1 : Matrix Unit Unit R)) 0 0 (JD l R)

Depends on / 依赖: Matrix, Matrix.fromBlocks, fromBlocks
-/
def JB :=
  Matrix.fromBlocks ((2 : R) • (1 : Matrix Unit Unit R)) 0 0 (JD l R)

/--
Definition of `typeB` / `typeB` 的定义

English:
definition typeB
  signature: [Fintype l]
  body: skewAdjointMatricesLieSubalgebra (JB l R)

中文:
定义 typeB
  签名: [有限类型 l]
  定义体: skewAdjointMatricesLieSubalgebra (JB l R)

Depends on / 依赖: skewAdjointMatricesLieSubalgebra
-/
def typeB [Fintype l] :=
  skewAdjointMatricesLieSubalgebra (JB l R)

/--
Definition of `PB` / `PB` 的定义

English:
definition PB
  body: Matrix.fromBlocks (1 : Matrix Unit Unit R) 0 0 (PD l R)

中文:
定义 PB
  定义体: Matrix.fromBlocks (1 : Matrix Unit Unit R) 0 0 (PD l R)

Depends on / 依赖: Matrix, Matrix.fromBlocks, fromBlocks
-/
def PB :=
  Matrix.fromBlocks (1 : Matrix Unit Unit R) 0 0 (PD l R)

variable [Fintype l]

/--
theorem `pb_inv` / 定理 `pb_inv`

English:
theorem pb_inv
  given: [Invertible (2 : R)]
  statement: PB l R * Matrix.fromBlocks 1 0 0 (⅟(PD l R)) = 1
  proof: by
  rw [PB]; rw [Matrix.fromBlocks_multiply]; rw [mul_invOf_self]
  simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.zero_mul, zero_add, add_zero,
    Matrix.fromBlocks_one]

中文:
定理 pb_inv
  条件: [可逆 (2 : R)]
  结论: PB l R * 矩阵.fromBlocks 1 0 0 (⅟(PD l R)) = 1
  证明: by
  rw [PB]; rw [Matrix.fromBlocks_multiply]; rw [mul_invOf_self]
  simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.zero_mul, zero_add, add_zero,
    Matrix.fromBlocks_one]

Depends on / 依赖: Matrix, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, fromBlocks_multiply, fromBlocks_one, mul_invOf_self, mul_one, mul_zero, zero_add, zero_mul
-/
theorem pb_inv [Invertible (2 : R)] : PB l R * Matrix.fromBlocks 1 0 0 (⅟(PD l R)) = 1 := by
  rw [PB]; rw [Matrix.fromBlocks_multiply]; rw [mul_invOf_self]
  simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.zero_mul, zero_add, add_zero,
    Matrix.fromBlocks_one]

/--
Instance `invertiblePB` / 实例 `invertiblePB`

English:
instance invertiblePB
  signature: [Invertible (2 : R)]
  body: invertibleOfRightInverse _ _ (pb_inv l R)

中文:
实例 invertiblePB
  签名: [可逆 (2 : R)]
  定义体: invertibleOfRightInverse _ _ (pb_inv l R)

Depends on / 依赖: invertibleOfRightInverse, pb_inv
-/
instance invertiblePB [Invertible (2 : R)] : Invertible (PB l R) :=
  invertibleOfRightInverse _ _ (pb_inv l R)

/--
theorem `jb_transform` / 定理 `jb_transform`

English:
theorem jb_transform
  statement: (PB l R)ᵀ * JB l R * PB l R = (2 : R) • Matrix.fromBlocks 1 0 0 (S l R)
  proof: by
  simp [PB, JB, jd_transform, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_smul]

中文:
定理 jb_transform
  结论: (PB l R)ᵀ * JB l R * PB l R = (2 : R) • 矩阵.fromBlocks 1 0 0 (S l R)
  证明: by
  simp [PB, JB, jd_transform, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_smul]

Depends on / 依赖: Matrix, Matrix.fromBlocks_multiply, Matrix.fromBlocks_smul, Matrix.fromBlocks_transpose, fromBlocks_multiply, fromBlocks_smul, fromBlocks_transpose, jd_transform
-/
theorem jb_transform : (PB l R)ᵀ * JB l R * PB l R = (2 : R) • Matrix.fromBlocks 1 0 0 (S l R) := by
  simp [PB, JB, jd_transform, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_smul]

/--
theorem `indefiniteDiagonal_assoc` / 定理 `indefiniteDiagonal_assoc`

English:
theorem indefiniteDiagonal_assoc
  proof: by
  ext ⟨⟨i₁ | i₂⟩ | i₃⟩ ⟨⟨j₁ | j₂⟩ | j₃⟩ <;>
    simp only [indefiniteDiagonal, Matrix.diagonal_apply, Equiv.sumAssoc_apply_inl_inl,
      Matrix.reindexLieEquiv_apply, Matrix.submatrix_apply, Equiv.symm_symm, Matrix.reindex_apply,
      Sum.elim_inl, if_true, Matrix.one_apply_eq, Matrix.fromBlock

中文:
定理 indefiniteDiagonal_assoc
  证明: by
  ext ⟨⟨i₁ | i₂⟩ | i₃⟩ ⟨⟨j₁ | j₂⟩ | j₃⟩ <;>
    simp only [indefiniteDiagonal, Matrix.diagonal_apply, Equiv.sumAssoc_apply_inl_inl,
      Matrix.reindexLieEquiv_apply, Matrix.submatrix_apply, Equiv.symm_symm, Matrix.reindex_apply,
      Sum.elim_inl, if_true, Matrix.one_apply_eq, Matrix.fromBlock

Depends on / 依赖: Equiv.sumAssoc_apply_inl_inl, Equiv.sumAssoc_apply_inl_inr, Equiv.sumAssoc_apply_inr, Equiv.symm_symm, Matrix, Matrix.diagonal_apply, Matrix.fromBlocks_apply, Matrix.one_apply_eq, Matrix.reindexLieEquiv_apply, Matrix.reindex_apply, Matrix.submatrix_apply, Sum.elim_inl, Sum.elim_inr, Sum.inl_injective.eq_iff, Sum.inr_injective.eq, diagonal_apply, elim_inl, elim_inr, eq_iff, if_false
-/
theorem indefiniteDiagonal_assoc :
    indefiniteDiagonal (Unit oplus l) l R =
      Matrix.reindexLieEquiv (Equiv.sumAssoc Unit l l).symm
        (Matrix.fromBlocks 1 0 0 (indefiniteDiagonal l l R)) := by
  ext ⟨⟨i₁ | i₂⟩ | i₃⟩ ⟨⟨j₁ | j₂⟩ | j₃⟩ <;>
    simp only [indefiniteDiagonal, Matrix.diagonal_apply, Equiv.sumAssoc_apply_inl_inl,
      Matrix.reindexLieEquiv_apply, Matrix.submatrix_apply, Equiv.symm_symm, Matrix.reindex_apply,
      Sum.elim_inl, if_true, Matrix.one_apply_eq, Matrix.fromBlocks_apply₁₁,
      Equiv.sumAssoc_apply_inl_inr, if_false, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Equiv.sumAssoc_apply_inr, Sum.elim_inr, Sum.inl_injective.eq_iff,
      Sum.inr_injective.eq_iff, reduceCtorEq] <;>
    congr 1

/--
Definition of `typeBEquivSo'` / `typeBEquivSo'` 的定义

English:
definition typeBEquivSo'
  signature: [Invertible (2 : R)]
  body: by
  apply (skewAdjointMatricesLieSubalgebraEquiv (JB l R) (PB l R) (by infer_instance)).trans
  symm
  apply
    (skewAdjointMatricesLieSubalgebraEquivTranspose (indefiniteDiagonal (Sum Unit l) l R)
        (Matrix.reindexAlgEquiv _ _ (Equiv.sumAssoc PUnit l l))
        (Matrix.transpose_reindex _ 

中文:
定义 typeBEquivSo'
  签名: [可逆 (2 : R)]
  定义体: by
  apply (skewAdjointMatricesLieSubalgebraEquiv (JB l R) (PB l R) (by infer_instance)).trans
  symm
  apply
    (skewAdjointMatricesLieSubalgebraEquivTranspose (indefiniteDiagonal (Sum Unit l) l R)
        (Matrix.reindexAlgEquiv _ _ (Equiv.sumAssoc PUnit l l))
        (Matrix.transpose_reindex _ 

Depends on / 依赖: Equiv.sumAssoc, LieEquiv, LieEquiv.ofEq, LieSubalgebra, LieSubalgebra.mem_coe, Matrix, Matrix.reindexAlgEquiv, Matrix.transpose_reindex, Units.smul_def, indefiniteDiagonal, infer_instance, jb_transform, mem_coe, mem_skewAdjointMatricesLieSubalgebra_unit_smul, reindexAlgEquiv, skewAdjointMatricesLieSubalgebraEquiv, skewAdjointMatricesLieSubalgebraEquivTranspose, smul_def, sumAssoc, transpose_reindex
-/
noncomputable def typeBEquivSo' [Invertible (2 : R)] : typeB l R ≃ₗ⁅R⁆ so' (Unit oplus l) l R := by
  apply (skewAdjointMatricesLieSubalgebraEquiv (JB l R) (PB l R) (by infer_instance)).trans
  symm
  apply
    (skewAdjointMatricesLieSubalgebraEquivTranspose (indefiniteDiagonal (Sum Unit l) l R)
        (Matrix.reindexAlgEquiv _ _ (Equiv.sumAssoc PUnit l l))
        (Matrix.transpose_reindex _ _)).trans
  apply LieEquiv.ofEq
  ext A
  rw [jb_transform]; rw [← val_unitOfInvertible (2 : R)]; rw [← Units.smul_def]; rw [LieSubalgebra.mem_coe]; rw [LieSubalgebra.mem_coe]; rw [mem_skewAdjointMatricesLieSubalgebra_unit_smul]
  simp [indefiniteDiagonal_assoc, S]

end Orthogonal

end LieAlgebra
