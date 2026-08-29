/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Mohanad Ahmed
-/
module

public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Real.Star
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.Vec
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-! # Positive Definite Matrices

This file defines positive (semi)definite matrices and connects the notion to positive definiteness
of quadratic forms.
In `Mathlib/Analysis/Matrix/Order.lean`, positive semi-definiteness is used to define the partial
order on matrices on `ℝ` or `ℂ`.

## Main definitions

* `Matrix.PosSemidef` : a matrix `M : Matrix n n R` is positive semidefinite if it is Hermitian
  and `xᴴMx` is nonnegative for all `x`.
* `Matrix.PosDef` : a matrix `M : Matrix n n R` is positive definite if it is Hermitian and `xᴴMx`
  is greater than zero for all nonzero `x`.

## Main results

* `Matrix.PosSemidef.fromBlocks₁₁` and `Matrix.PosSemidef.fromBlocks₂₂`: If a matrix `A` is
  positive definite, then `[A B; Bᴴ D]` is positive semidefinite if and only if `D - Bᴴ A⁻¹ B` is
  positive semidefinite.
* `Matrix.PosDef.isUnit`: A positive definite matrix in a field is invertible.
-/

@[expose] public section

-- TODO:
-- assert_not_exists MonoidAlgebra
assert_not_exists NormedGroup

open Matrix

namespace Matrix

variable {m n R R' : Type*}
variable [Ring R] [PartialOrder R] [StarRing R]
variable [CommRing R'] [PartialOrder R'] [StarRing R']

/-!
## Positive semidefinite matrices
-/

/--
Definition of `PosSemidef` / `PosSemidef` 的定义

English:
definition PosSemidef
  signature: (M : Matrix n n R)
  body: M.IsHermitian ∧ forall x : n ->₀ R, 0 <= x.sum fun i xi => x.sum fun j xj => star xi * M i j * xj

中文:
定义 PosSemidef
  签名: (M : 矩阵 n n R)
  定义体: M.IsHermitian ∧ forall x : n ->₀ R, 0 <= x.sum fun i xi => x.sum fun j xj => star xi * M i j * xj

Depends on / 依赖: IsHermitian, M.IsHermitian, x.sum
-/
def PosSemidef (M : Matrix n n R) : Prop :=
  M.IsHermitian ∧ forall x : n ->₀ R, 0 <= x.sum fun i xi => x.sum fun j xj => star xi * M i j * xj

/--
theorem `PosSemidef.diagonal` / 定理 `PosSemidef.diagonal`

English:
theorem PosSemidef.diagonal
  given: [StarOrderedRing R] [DecidableEq n] {d : n -> R} (h : 0 <= d)
  proof: isHermitian_diagonal_of_self_adjoint _ funext fun i => IsSelfAdjoint.of_nonneg (h i)
  right x := by
    -- TODO: positivity
    refine Finsupp.sum_nonneg fun i _ => Finsupp.sum_nonneg fun j _ => ?_
    simp +contextual [diagonal, apply_ite, star_left_conjugate_nonneg (h _)]

中文:
定理 PosSemidef.diagonal
  条件: [StarOrdered环 R] [DecidableEq n] {d : n -> R} (h : 0 <= d)
  证明: isHermitian_diagonal_of_self_adjoint _ funext fun i => IsSelfAdjoint.of_nonneg (h i)
  right x := by
    -- TODO: positivity
    refine Finsupp.sum_nonneg fun i _ => Finsupp.sum_nonneg fun j _ => ?_
    simp +contextual [diagonal, apply_ite, star_left_conjugate_nonneg (h _)]
-/
protected theorem PosSemidef.diagonal [StarOrderedRing R] [DecidableEq n] {d : n -> R} (h : 0 <= d) :
    PosSemidef (diagonal d) where
left := isHermitian_diagonal_of_self_adjoint _ funext fun i => IsSelfAdjoint.of_nonneg (h i)
  right x := by
    -- TODO: positivity
    refine Finsupp.sum_nonneg fun i _ => Finsupp.sum_nonneg fun j _ => ?_
    simp +contextual [diagonal, apply_ite, star_left_conjugate_nonneg (h _)]

/--
lemma `posSemidef_diagonal_iff` / 引理 `posSemidef_diagonal_iff`

English:
lemma posSemidef_diagonal_iff
  given: [StarOrderedRing R] [DecidableEq n] {d : n -> R}
  proof: ⟨fun ⟨_, hP⟩ i => by simpa using hP (.single i 1), .diagonal⟩

中文:
引理 posSemidef_diagonal_iff
  条件: [StarOrdered环 R] [DecidableEq n] {d : n -> R}
  证明: ⟨fun ⟨_, hP⟩ i => by simpa using hP (.single i 1), .diagonal⟩
-/
@[simp] lemma posSemidef_diagonal_iff [StarOrderedRing R] [DecidableEq n] {d : n -> R} :
    PosSemidef (diagonal d) ↔ forall i, 0 <= d i :=
  ⟨fun ⟨_, hP⟩ i => by simpa using hP (.single i 1), .diagonal⟩

namespace PosSemidef

/--
theorem `isHermitian` / 定理 `isHermitian`

English:
theorem isHermitian
  given: {M : Matrix n n R} (hM : M.PosSemidef)
  statement: M.IsHermitian
  proof: hM.1

中文:
定理 isHermitian
  条件: {M : 矩阵 n n R} (hM : M.PosSemidef)
  结论: M.IsHermitian
  证明: hM.1
-/
theorem isHermitian {M : Matrix n n R} (hM : M.PosSemidef) : M.IsHermitian :=
  hM.1

/--
theorem `submatrix` / 定理 `submatrix`

English:
theorem submatrix
  given: {M : Matrix n n R} (hM : M.PosSemidef) (e : m -> n)
  proof: by
  refine ⟨hM.1.submatrix _, fun x => ?_⟩
simpa [Finsupp.sum_mapDomain_index, add_mul, mul_add] using hM.2 x.mapDomain e

中文:
定理 submatrix
  条件: {M : 矩阵 n n R} (hM : M.PosSemidef) (e : m -> n)
  证明: by
  refine ⟨hM.1.submatrix _, fun x => ?_⟩
simpa [Finsupp.sum_mapDomain_index, add_mul, mul_add] using hM.2 x.mapDomain e

Depends on / 依赖: Finsupp, Finsupp.sum_mapDomain_index, add_mul, mapDomain, mul_add, submatrix, sum_mapDomain_index, x.mapDomain
-/
theorem submatrix {M : Matrix n n R} (hM : M.PosSemidef) (e : m -> n) :
    (M.submatrix e e).PosSemidef := by
  refine ⟨hM.1.submatrix _, fun x => ?_⟩
simpa [Finsupp.sum_mapDomain_index, add_mul, mul_add] using hM.2 x.mapDomain e

/--
theorem `transpose` / 定理 `transpose`

English:
theorem transpose
  given: {M : Matrix n n R'} (hM : M.PosSemidef)
  statement: Mᵀ.PosSemidef
  proof: by
  have (a b c : R') : a * b * c = c * b * a := by ring
  refine ⟨hM.1.transpose, fun x => ?_⟩
  rw [Finsupp.sum_comm]
  simpa [Finsupp.sum_mapRange_index, this] using hM.2 (Finsupp.mapRange star (star_zero R') x)

@[simp]

中文:
定理 transpose
  条件: {M : 矩阵 n n R'} (hM : M.PosSemidef)
  结论: Mᵀ.PosSemidef
  证明: by
  have (a b c : R') : a * b * c = c * b * a := by ring
  refine ⟨hM.1.transpose, fun x => ?_⟩
  rw [Finsupp.sum_comm]
  simpa [Finsupp.sum_mapRange_index, this] using hM.2 (Finsupp.mapRange star (star_zero R') x)

@[simp]

Depends on / 依赖: Finsupp, Finsupp.mapRange, Finsupp.sum_comm, Finsupp.sum_mapRange_index, mapRange, star_zero, sum_comm, sum_mapRange_index, transpose
-/
theorem transpose {M : Matrix n n R'} (hM : M.PosSemidef) : Mᵀ.PosSemidef := by
  have (a b c : R') : a * b * c = c * b * a := by ring
  refine ⟨hM.1.transpose, fun x => ?_⟩
  rw [Finsupp.sum_comm]
  simpa [Finsupp.sum_mapRange_index, this] using hM.2 (Finsupp.mapRange star (star_zero R') x)

@[simp]
/--
theorem `_root_.Matrix.posSemidef_transpose_iff` / 定理 `_root_.Matrix.posSemidef_transpose_iff`

English:
theorem _root_.Matrix.posSemidef_transpose_iff
  given: {M : Matrix n n R'}
  statement: Mᵀ.PosSemidef ↔ M.PosSemidef
  proof: ⟨.transpose, .transpose⟩

中文:
定理 _root_.矩阵.posSemidef_transpose_iff
  条件: {M : 矩阵 n n R'}
  结论: Mᵀ.PosSemidef ↔ M.PosSemidef
  证明: ⟨.transpose, .transpose⟩

Depends on / 依赖: transpose
-/
theorem _root_.Matrix.posSemidef_transpose_iff {M : Matrix n n R'} : Mᵀ.PosSemidef ↔ M.PosSemidef :=
  ⟨.transpose, .transpose⟩

/--
theorem `conjTranspose` / 定理 `conjTranspose`

English:
theorem conjTranspose
  given: {M : Matrix n n R} (hM : M.PosSemidef)
  statement: Mᴴ.PosSemidef
  proof: hM.1.symm ▸ hM

@[simp]

中文:
定理 conjTranspose
  条件: {M : 矩阵 n n R} (hM : M.PosSemidef)
  结论: Mᴴ.PosSemidef
  证明: hM.1.symm ▸ hM

@[simp]
-/
theorem conjTranspose {M : Matrix n n R} (hM : M.PosSemidef) : Mᴴ.PosSemidef := hM.1.symm ▸ hM

@[simp]
/--
theorem `_root_.Matrix.posSemidef_conjTranspose_iff` / 定理 `_root_.Matrix.posSemidef_conjTranspose_iff`

English:
theorem _root_.Matrix.posSemidef_conjTranspose_iff
  given: {M : Matrix n n R}
  proof: ⟨(by simpa using ·.conjTranspose), .conjTranspose⟩

中文:
定理 _root_.矩阵.posSemidef_conjTranspose_iff
  条件: {M : 矩阵 n n R}
  证明: ⟨(by simpa using ·.conjTranspose), .conjTranspose⟩

Depends on / 依赖: conjTranspose
-/
theorem _root_.Matrix.posSemidef_conjTranspose_iff {M : Matrix n n R} :
    Mᴴ.PosSemidef ↔ M.PosSemidef :=
  ⟨(by simpa using ·.conjTranspose), .conjTranspose⟩

/--
lemma `add` / 引理 `add`

English:
lemma add
  statement: [AddLeftMono R] {A : Matrix m m R} {B : Matrix m m R}
  proof: ⟨hA.isHermitian.add hB.isHermitian, fun x => by
    simpa [mul_add, add_mul] using add_nonneg (hA.2 x) (hB.2 x)⟩

中文:
引理 add
  结论: [AddLeftMono R] {A : 矩阵 m m R} {B : 矩阵 m m R}
  证明: ⟨hA.isHermitian.add hB.isHermitian, fun x => by
    simpa [mul_add, add_mul] using add_nonneg (hA.2 x) (hB.2 x)⟩
-/
protected lemma add [AddLeftMono R] {A : Matrix m m R} {B : Matrix m m R}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : (A + B).PosSemidef :=
  ⟨hA.isHermitian.add hB.isHermitian, fun x => by
    simpa [mul_add, add_mul] using add_nonneg (hA.2 x) (hB.2 x)⟩

/--
theorem `smul` / 定理 `smul`

English:
theorem smul
  statement: {α : Type*} [CommSemiring α] [PartialOrder α] [StarRing α]
  proof: by
  refine ⟨IsSelfAdjoint.smul (.of_nonneg ha) hx.1, fun y => ?_⟩
  simpa [mul_smul_comm, smul_mul_assoc, ← Finsupp.smul_sum] using smul_nonneg ha (hx.2 _)

中文:
定理 smul
  结论: {α : 类型} [交换半环 α] [偏序 α] [对合环 α]
  证明: by
  refine ⟨IsSelfAdjoint.smul (.of_nonneg ha) hx.1, fun y => ?_⟩
  simpa [mul_smul_comm, smul_mul_assoc, ← Finsupp.smul_sum] using smul_nonneg ha (hx.2 _)
-/
protected theorem smul {α : Type*} [CommSemiring α] [PartialOrder α] [StarRing α]
    [StarOrderedRing α] [Algebra α R] [StarModule α R] [PosSMulMono α R] {x : Matrix n n R}
    (hx : x.PosSemidef) {a : α} (ha : 0 <= a) : (a • x).PosSemidef := by
  refine ⟨IsSelfAdjoint.smul (.of_nonneg ha) hx.1, fun y => ?_⟩
  simpa [mul_smul_comm, smul_mul_assoc, ← Finsupp.smul_sum] using smul_nonneg ha (hx.2 _)

/--
lemma `zero` / 引理 `zero`

English:
lemma zero
  statement: PosSemidef (0 : Matrix n n R)
  proof: ⟨isHermitian_zero, by simp⟩

中文:
引理 zero
  结论: PosSemidef (0 : 矩阵 n n R)
  证明: ⟨isHermitian_zero, by simp⟩
-/
protected lemma zero : PosSemidef (0 : Matrix n n R) := ⟨isHermitian_zero, by simp⟩

/--
lemma `one` / 引理 `one`

English:
lemma one
  given: [StarOrderedRing R] [DecidableEq n]
  statement: PosSemidef (1 : Matrix n n R)
  proof: ⟨isHermitian_one, fun x => Finsupp.sum_nonneg fun i _ => Finsupp.sum_nonneg fun j _ => by
    obtain rfl | hij := eq_or_ne i j <;> simp [*]⟩

中文:
引理 one
  条件: [StarOrdered环 R] [DecidableEq n]
  结论: PosSemidef (1 : 矩阵 n n R)
  证明: ⟨isHermitian_one, fun x => Finsupp.sum_nonneg fun i _ => Finsupp.sum_nonneg fun j _ => by
    obtain rfl | hij := eq_or_ne i j <;> simp [*]⟩
-/
protected lemma one [StarOrderedRing R] [DecidableEq n] : PosSemidef (1 : Matrix n n R) :=
  ⟨isHermitian_one, fun x => Finsupp.sum_nonneg fun i _ => Finsupp.sum_nonneg fun j _ => by
    obtain rfl | hij := eq_or_ne i j <;> simp [*]⟩

/--
theorem `natCast` / 定理 `natCast`

English:
theorem natCast
  given: [StarOrderedRing R] [DecidableEq n] (d : Nat)
  proof: ⟨isHermitian_natCast _, fun x => Finsupp.sum_nonneg fun i _ => Finsupp.sum_nonneg fun j _ => by
    obtain rfl | hij := eq_or_ne i j <;> simp [← diagonal_natCast', star_left_conjugate_nonneg, *]⟩

中文:
定理 natCast
  条件: [StarOrdered环 R] [DecidableEq n] (d : 自然数)
  证明: ⟨isHermitian_natCast _, fun x => Finsupp.sum_nonneg fun i _ => Finsupp.sum_nonneg fun j _ => by
    obtain rfl | hij := eq_or_ne i j <;> simp [← diagonal_natCast', star_left_conjugate_nonneg, *]⟩
-/
protected theorem natCast [StarOrderedRing R] [DecidableEq n] (d : Nat) :
    PosSemidef (d : Matrix n n R) :=
  ⟨isHermitian_natCast _, fun x => Finsupp.sum_nonneg fun i _ => Finsupp.sum_nonneg fun j _ => by
    obtain rfl | hij := eq_or_ne i j <;> simp [← diagonal_natCast', star_left_conjugate_nonneg, *]⟩

/--
theorem `ofNat` / 定理 `ofNat`

English:
theorem ofNat
  given: [StarOrderedRing R] [DecidableEq n] (d : Nat) [d.AtLeastTwo]
  proof: .natCast d

中文:
定理 of自然数
  条件: [StarOrdered环 R] [DecidableEq n] (d : 自然数) [d.AtLeastTwo]
  证明: .natCast d
-/
protected theorem ofNat [StarOrderedRing R] [DecidableEq n] (d : Nat) [d.AtLeastTwo] :
    PosSemidef (ofNat(d) : Matrix n n R) :=
  .natCast d

/--
theorem `intCast` / 定理 `intCast`

English:
theorem intCast
  given: [StarOrderedRing R] [DecidableEq n] (d : Int) (hd : 0 <= d)
  proof: ⟨isHermitian_intCast _, fun x => Finsupp.sum_nonneg fun i _ => Finsupp.sum_nonneg fun j _ => by
    obtain rfl | hij := eq_or_ne i j <;> simp [← diagonal_intCast', star_left_conjugate_nonneg, *]⟩

@[simp]

中文:
定理 intCast
  条件: [StarOrdered环 R] [DecidableEq n] (d : 整数) (hd : 0 <= d)
  证明: ⟨isHermitian_intCast _, fun x => Finsupp.sum_nonneg fun i _ => Finsupp.sum_nonneg fun j _ => by
    obtain rfl | hij := eq_or_ne i j <;> simp [← diagonal_intCast', star_left_conjugate_nonneg, *]⟩

@[simp]
-/
protected theorem intCast [StarOrderedRing R] [DecidableEq n] (d : Int) (hd : 0 <= d) :
    PosSemidef (d : Matrix n n R) :=
  ⟨isHermitian_intCast _, fun x => Finsupp.sum_nonneg fun i _ => Finsupp.sum_nonneg fun j _ => by
    obtain rfl | hij := eq_or_ne i j <;> simp [← diagonal_intCast', star_left_conjugate_nonneg, *]⟩

@[simp]
/--
theorem `_root_.Matrix.posSemidef_intCast_iff` / 定理 `_root_.Matrix.posSemidef_intCast_iff`

English:
theorem _root_.Matrix.posSemidef_intCast_iff
  proof: by simp [← diagonal_intCast']

中文:
定理 _root_.矩阵.posSemidef_intCast_iff
  证明: by simp [← diagonal_intCast']
-/
protected theorem _root_.Matrix.posSemidef_intCast_iff
    [StarOrderedRing R] [DecidableEq n] [Nonempty n] [Nontrivial R] (d : Int) :
    PosSemidef (d : Matrix n n R) ↔ 0 <= d := by simp [← diagonal_intCast']

/--
lemma `diag_nonneg` / 引理 `diag_nonneg`

English:
lemma diag_nonneg
  given: {A : Matrix n n R} (hA : A.PosSemidef) {i : n}
  statement: 0 <= A i i
  proof: by
simpa using hA.2 .single i 1

中文:
引理 diag_nonneg
  条件: {A : 矩阵 n n R} (hA : A.PosSemidef) {i : n}
  结论: 0 <= A i i
  证明: by
simpa using hA.2 .single i 1

Depends on / 依赖: single
-/
lemma diag_nonneg {A : Matrix n n R} (hA : A.PosSemidef) {i : n} : 0 <= A i i := by
simpa using hA.2 .single i 1

end PosSemidef

@[simp]
/--
theorem `posSemidef_submatrix_equiv` / 定理 `posSemidef_submatrix_equiv`

English:
theorem posSemidef_submatrix_equiv
  given: {M : Matrix n n R} (e : m ≃ n)
  proof: ⟨fun h => by simpa using h.submatrix e.symm, fun h => h.submatrix _⟩

中文:
定理 posSemidef_submatrix_equiv
  条件: {M : 矩阵 n n R} (e : m ≃ n)
  证明: ⟨fun h => by simpa using h.submatrix e.symm, fun h => h.submatrix _⟩

Depends on / 依赖: e.symm, h.submatrix, submatrix
-/
theorem posSemidef_submatrix_equiv {M : Matrix n n R} (e : m ≃ n) :
    (M.submatrix e e).PosSemidef ↔ M.PosSemidef :=
  ⟨fun h => by simpa using h.submatrix e.symm, fun h => h.submatrix _⟩

/--
theorem `posSemidef_sum` / 定理 `posSemidef_sum`

English:
theorem posSemidef_sum
  statement: {ι : Type*} [AddLeftMono R]
  proof: by
.1, fun y => ?_⟩ refine ⟨isSelfAdjoint_sum s fun _ hi => h _ hi
  simp [sum_apply, Finset.mul_sum, Finset.sum_mul, Finsupp.sum_finsetSum_comm,
    Finset.sum_nonneg fun _ hi => (h _ hi).2 _]

中文:
定理 posSemidef_sum
  结论: {ι : 类型} [AddLeftMono R]
  证明: by
.1, fun y => ?_⟩ refine ⟨isSelfAdjoint_sum s fun _ hi => h _ hi
  simp [sum_apply, Finset.mul_sum, Finset.sum_mul, Finsupp.sum_finsetSum_comm,
    Finset.sum_nonneg fun _ hi => (h _ hi).2 _]

Depends on / 依赖: Finset, Finset.mul_sum, Finset.sum_mul, Finset.sum_nonneg, Finsupp, Finsupp.sum_finsetSum_comm, isSelfAdjoint_sum, mul_sum, sum_apply, sum_finsetSum_comm, sum_mul, sum_nonneg
-/
theorem posSemidef_sum {ι : Type*} [AddLeftMono R]
    {x : ι -> Matrix n n R} (s : Finset ι) (h : forall i in s, PosSemidef (x i)) :
    PosSemidef (∑ i in s, x i) := by
.1, fun y => ?_⟩ refine ⟨isSelfAdjoint_sum s fun _ hi => h _ hi
  simp [sum_apply, Finset.mul_sum, Finset.sum_mul, Finsupp.sum_finsetSum_comm,
    Finset.sum_nonneg fun _ hi => (h _ hi).2 _]

/-!
## Positive definite matrices
-/

/--
Definition of `PosDef` / `PosDef` 的定义

English:
definition PosDef
  signature: (M : Matrix n n R)
  body: M.IsHermitian ∧ forall ⦃x : n ->₀ R⦄, x != 0 -> 0 < x.sum fun i xi => x.sum fun j xj => star xi * M i j * xj

中文:
定义 PosDef
  签名: (M : 矩阵 n n R)
  定义体: M.IsHermitian ∧ forall ⦃x : n ->₀ R⦄, x != 0 -> 0 < x.sum fun i xi => x.sum fun j xj => star xi * M i j * xj

Depends on / 依赖: IsHermitian, M.IsHermitian, x.sum
-/
def PosDef (M : Matrix n n R) :=
  M.IsHermitian ∧ forall ⦃x : n ->₀ R⦄, x != 0 -> 0 < x.sum fun i xi => x.sum fun j xj => star xi * M i j * xj

namespace PosDef

/--
theorem `isHermitian` / 定理 `isHermitian`

English:
theorem isHermitian
  given: {M : Matrix n n R} (hM : M.PosDef)
  statement: M.IsHermitian
  proof: hM.1

中文:
定理 isHermitian
  条件: {M : 矩阵 n n R} (hM : M.PosDef)
  结论: M.IsHermitian
  证明: hM.1
-/
theorem isHermitian {M : Matrix n n R} (hM : M.PosDef) : M.IsHermitian :=
  hM.1

/--
theorem `posSemidef` / 定理 `posSemidef`

English:
theorem posSemidef
  given: {M : Matrix n n R} (hM : M.PosDef)
  statement: M.PosSemidef
  proof: ⟨hM.1, fun x => by obtain rfl | hx := eq_or_ne x 0 <;> simp [le_of_lt, hM.2, *]⟩

中文:
定理 posSemidef
  条件: {M : 矩阵 n n R} (hM : M.PosDef)
  结论: M.PosSemidef
  证明: ⟨hM.1, fun x => by obtain rfl | hx := eq_or_ne x 0 <;> simp [le_of_lt, hM.2, *]⟩

Depends on / 依赖: eq_or_ne, le_of_lt
-/
theorem posSemidef {M : Matrix n n R} (hM : M.PosDef) : M.PosSemidef :=
  ⟨hM.1, fun x => by obtain rfl | hx := eq_or_ne x 0 <;> simp [le_of_lt, hM.2, *]⟩

/--
theorem `submatrix` / 定理 `submatrix`

English:
theorem submatrix
  statement: {M : Matrix n n R} (hM : M.PosDef) {e : m -> n}
  proof: by
  refine ⟨hM.1.submatrix _, fun x hx => ?_⟩
  simpa [Finsupp.sum_mapDomain_index, add_mul, mul_add] using
hM.2 .2 hx .ne_iff' Finsupp.mapDomain_zero Finsupp.mapDomain_injective he

中文:
定理 submatrix
  结论: {M : 矩阵 n n R} (hM : M.PosDef) {e : m -> n}
  证明: by
  refine ⟨hM.1.submatrix _, fun x hx => ?_⟩
  simpa [Finsupp.sum_mapDomain_index, add_mul, mul_add] using
hM.2 .2 hx .ne_iff' Finsupp.mapDomain_zero Finsupp.mapDomain_injective he

Depends on / 依赖: Finsupp, Finsupp.mapDomain_injective, Finsupp.mapDomain_zero, Finsupp.sum_mapDomain_index, add_mul, mapDomain_injective, mapDomain_zero, mul_add, ne_iff, submatrix, sum_mapDomain_index
-/
theorem submatrix {M : Matrix n n R} (hM : M.PosDef) {e : m -> n}
    (he : Function.Injective e) : (M.submatrix e e).PosDef := by
  refine ⟨hM.1.submatrix _, fun x hx => ?_⟩
  simpa [Finsupp.sum_mapDomain_index, add_mul, mul_add] using
hM.2 .2 hx .ne_iff' Finsupp.mapDomain_zero Finsupp.mapDomain_injective he

/--
theorem `transpose` / 定理 `transpose`

English:
theorem transpose
  given: {M : Matrix n n R'} (hM : M.PosDef)
  statement: Mᵀ.PosDef
  proof: by
  have (a b c : R') : a * b * c = c * b * a := by ring
  refine ⟨hM.1.transpose, fun x => ?_⟩
  rw [Finsupp.sum_comm]
  simpa [star_injective, Finsupp.sum_mapRange_index, this] using
      hM.2 (x := x.mapRange star (star_zero R'))

@[simp]

中文:
定理 transpose
  条件: {M : 矩阵 n n R'} (hM : M.PosDef)
  结论: Mᵀ.PosDef
  证明: by
  have (a b c : R') : a * b * c = c * b * a := by ring
  refine ⟨hM.1.transpose, fun x => ?_⟩
  rw [Finsupp.sum_comm]
  simpa [star_injective, Finsupp.sum_mapRange_index, this] using
      hM.2 (x := x.mapRange star (star_zero R'))

@[simp]

Depends on / 依赖: Finsupp, Finsupp.sum_comm, Finsupp.sum_mapRange_index, mapRange, star_injective, star_zero, sum_comm, sum_mapRange_index, transpose, x.mapRange
-/
theorem transpose {M : Matrix n n R'} (hM : M.PosDef) : Mᵀ.PosDef := by
  have (a b c : R') : a * b * c = c * b * a := by ring
  refine ⟨hM.1.transpose, fun x => ?_⟩
  rw [Finsupp.sum_comm]
  simpa [star_injective, Finsupp.sum_mapRange_index, this] using
      hM.2 (x := x.mapRange star (star_zero R'))

@[simp]
/--
theorem `transpose_iff` / 定理 `transpose_iff`

English:
theorem transpose_iff
  given: {M : Matrix n n R'}
  statement: Mᵀ.PosDef ↔ M.PosDef
  proof: ⟨(by simpa using ·.transpose), .transpose⟩

中文:
定理 transpose_iff
  条件: {M : 矩阵 n n R'}
  结论: Mᵀ.PosDef ↔ M.PosDef
  证明: ⟨(by simpa using ·.transpose), .transpose⟩

Depends on / 依赖: transpose
-/
theorem transpose_iff {M : Matrix n n R'} : Mᵀ.PosDef ↔ M.PosDef :=
  ⟨(by simpa using ·.transpose), .transpose⟩

/--
theorem `diagonal` / 定理 `diagonal`

English:
theorem diagonal
  statement: [StarOrderedRing R] [DecidableEq n] [NoZeroDivisors R]
  proof: isHermitian_diagonal_of_self_adjoint _ funext fun i => IsSelfAdjoint.of_nonneg (h i).le
  right x hx := by
    refine Finsupp.sum_pos' (fun _ _ => Finsupp.sum_nonneg ?_) ?_
    · simp +contextual [diagonal, apply_ite, star_left_conjugate_nonneg (h _).le]
    obtain ⟨i, hxi⟩ := by simpa [Finsupp.ext_iff] using hx
    refine ⟨i, ?_, Finsupp.sum_pos' ?_ ⟨i, ?_, ?_⟩⟩ <;> simp +contextual [diagonal,
      apply_ite, star_left_conjugate_nonneg (h _).le,
      star_left_conjugate_pos (h i), IsRegular.of_ne_zero hxi, Finsupp.mem_support_iff.mpr hxi]

@[simp]

中文:
定理 diagonal
  结论: [StarOrdered环 R] [DecidableEq n] [无零因子 R]
  证明: isHermitian_diagonal_of_self_adjoint _ funext fun i => IsSelfAdjoint.of_nonneg (h i).le
  right x hx := by
    refine Finsupp.sum_pos' (fun _ _ => Finsupp.sum_nonneg ?_) ?_
    · simp +contextual [diagonal, apply_ite, star_left_conjugate_nonneg (h _).le]
    obtain ⟨i, hxi⟩ := by simpa [Finsupp.ext_iff] using hx
    refine ⟨i, ?_, Finsupp.sum_pos' ?_ ⟨i, ?_, ?_⟩⟩ <;> simp +contextual [diagonal,
      apply_ite, star_left_conjugate_nonneg (h _).le,
      star_left_conjugate_pos (h i), IsRegular.of_ne_zero hxi, Finsupp.mem_support_iff.mpr hxi]

@[simp]
-/
protected theorem diagonal [StarOrderedRing R] [DecidableEq n] [NoZeroDivisors R]
    {d : n -> R} (h : forall i, 0 < d i) :
    PosDef (diagonal d) where
left := isHermitian_diagonal_of_self_adjoint _ funext fun i => IsSelfAdjoint.of_nonneg (h i).le
  right x hx := by
    refine Finsupp.sum_pos' (fun _ _ => Finsupp.sum_nonneg ?_) ?_
    · simp +contextual [diagonal, apply_ite, star_left_conjugate_nonneg (h _).le]
    obtain ⟨i, hxi⟩ := by simpa [Finsupp.ext_iff] using hx
    refine ⟨i, ?_, Finsupp.sum_pos' ?_ ⟨i, ?_, ?_⟩⟩ <;> simp +contextual [diagonal,
      apply_ite, star_left_conjugate_nonneg (h _).le,
      star_left_conjugate_pos (h i), IsRegular.of_ne_zero hxi, Finsupp.mem_support_iff.mpr hxi]

@[simp]
/--
theorem `_root_.Matrix.posDef_diagonal_iff` / 定理 `_root_.Matrix.posDef_diagonal_iff`

English:
theorem _root_.Matrix.posDef_diagonal_iff
  proof: ⟨fun h i => by simpa using h.2 (x := .single i 1), .diagonal⟩

@[simp, nontriviality]

中文:
定理 _root_.矩阵.posDef_diagonal_iff
  证明: ⟨fun h i => by simpa using h.2 (x := .single i 1), .diagonal⟩

@[simp, nontriviality]

Depends on / 依赖: diagonal, single
-/
theorem _root_.Matrix.posDef_diagonal_iff
    [StarOrderedRing R] [DecidableEq n] [NoZeroDivisors R] [Nontrivial R] {d : n -> R} :
    PosDef (diagonal d) ↔ forall i, 0 < d i :=
  ⟨fun h i => by simpa using h.2 (x := .single i 1), .diagonal⟩

@[simp, nontriviality]
/--
theorem `of_subsingleton` / 定理 `of_subsingleton`

English:
theorem of_subsingleton
  given: (h : Subsingleton R) (M : Matrix n n R)
  statement: M.PosDef
  proof: ⟨.of_subsingleton, fun _ hx => (hx <| Subsingleton.elim ..).elim⟩

中文:
定理 of_subsingleton
  条件: (h : 子单例 R) (M : 矩阵 n n R)
  结论: M.PosDef
  证明: ⟨.of_subsingleton, fun _ hx => (hx <| Subsingleton.elim ..).elim⟩

Depends on / 依赖: Subsingleton, Subsingleton.elim, of_subsingleton
-/
theorem of_subsingleton (h : Subsingleton R) (M : Matrix n n R) : M.PosDef :=
  ⟨.of_subsingleton, fun _ hx => (hx <| Subsingleton.elim ..).elim⟩

/--
theorem `one` / 定理 `one`

English:
theorem one
  given: [StarOrderedRing R] [DecidableEq n] [NoZeroDivisors R]
  proof: by
  nontriviality R
  exact .diagonal fun i => zero_lt_one' R

中文:
定理 one
  条件: [StarOrdered环 R] [DecidableEq n] [无零因子 R]
  证明: by
  nontriviality R
  exact .diagonal fun i => zero_lt_one' R
-/
protected theorem one [StarOrderedRing R] [DecidableEq n] [NoZeroDivisors R] :
    PosDef (1 : Matrix n n R) := by
  nontriviality R
  exact .diagonal fun i => zero_lt_one' R

/--
theorem `natCast` / 定理 `natCast`

English:
theorem natCast
  statement: [StarOrderedRing R] [DecidableEq n] [NoZeroDivisors R]
  proof: by
  nontriviality R
  exact .diagonal fun _ => by simpa [pos_iff_ne_zero]

@[simp]

中文:
定理 natCast
  结论: [StarOrdered环 R] [DecidableEq n] [无零因子 R]
  证明: by
  nontriviality R
  exact .diagonal fun _ => by simpa [pos_iff_ne_zero]

@[simp]
-/
protected theorem natCast [StarOrderedRing R] [DecidableEq n] [NoZeroDivisors R]
    (d : Nat) (hd : d != 0) :
    PosDef (d : Matrix n n R) := by
  nontriviality R
  exact .diagonal fun _ => by simpa [pos_iff_ne_zero]

@[simp]
/--
theorem `_root_.Matrix.posDef_natCast_iff` / 定理 `_root_.Matrix.posDef_natCast_iff`

English:
theorem _root_.Matrix.posDef_natCast_iff
  statement: [StarOrderedRing R] [DecidableEq n] [NoZeroDivisors R]
  proof: posDef_diagonal_iff.trans by simp

中文:
定理 _root_.矩阵.posDef_natCast_iff
  结论: [StarOrdered环 R] [DecidableEq n] [无零因子 R]
  证明: posDef_diagonal_iff.trans by simp

Depends on / 依赖: posDef_diagonal_iff, posDef_diagonal_iff.trans
-/
theorem _root_.Matrix.posDef_natCast_iff [StarOrderedRing R] [DecidableEq n] [NoZeroDivisors R]
    [Nonempty n] [Nontrivial R] {d : Nat} :
    PosDef (d : Matrix n n R) ↔ 0 < d :=
posDef_diagonal_iff.trans by simp

/--
theorem `ofNat` / 定理 `ofNat`

English:
theorem ofNat
  statement: [StarOrderedRing R] [DecidableEq n] [NoZeroDivisors R]
  proof: .natCast d (NeZero.ne _)

中文:
定理 of自然数
  结论: [StarOrdered环 R] [DecidableEq n] [无零因子 R]
  证明: .natCast d (NeZero.ne _)
-/
protected theorem ofNat [StarOrderedRing R] [DecidableEq n] [NoZeroDivisors R]
    (d : Nat) [d.AtLeastTwo] :
    PosDef (ofNat(d) : Matrix n n R) :=
  .natCast d (NeZero.ne _)

/--
theorem `intCast` / 定理 `intCast`

English:
theorem intCast
  statement: [StarOrderedRing R] [DecidableEq n] [NoZeroDivisors R]
  proof: by
  nontriviality R
  exact .diagonal fun _ => by simpa [pos_iff_ne_zero]

@[simp]

中文:
定理 intCast
  结论: [StarOrdered环 R] [DecidableEq n] [无零因子 R]
  证明: by
  nontriviality R
  exact .diagonal fun _ => by simpa [pos_iff_ne_zero]

@[simp]
-/
protected theorem intCast [StarOrderedRing R] [DecidableEq n] [NoZeroDivisors R]
    (d : Int) (hd : 0 < d) :
    PosDef (d : Matrix n n R) := by
  nontriviality R
  exact .diagonal fun _ => by simpa [pos_iff_ne_zero]

@[simp]
/--
theorem `_root_.Matrix.posDef_intCast_iff` / 定理 `_root_.Matrix.posDef_intCast_iff`

English:
theorem _root_.Matrix.posDef_intCast_iff
  statement: [StarOrderedRing R] [DecidableEq n] [NoZeroDivisors R]
  proof: posDef_diagonal_iff.trans by simp

中文:
定理 _root_.矩阵.posDef_intCast_iff
  结论: [StarOrdered环 R] [DecidableEq n] [无零因子 R]
  证明: posDef_diagonal_iff.trans by simp

Depends on / 依赖: posDef_diagonal_iff, posDef_diagonal_iff.trans
-/
theorem _root_.Matrix.posDef_intCast_iff [StarOrderedRing R] [DecidableEq n] [NoZeroDivisors R]
    [Nonempty n] [Nontrivial R] {d : Int} :
    PosDef (d : Matrix n n R) ↔ 0 < d :=
posDef_diagonal_iff.trans by simp

/--
lemma `add_posSemidef` / 引理 `add_posSemidef`

English:
lemma add_posSemidef
  statement: [AddLeftMono R]
  proof: ⟨hA.isHermitian.add hB.isHermitian, fun x hx => by
    simpa [mul_add,add_mul] using add_pos_of_pos_of_nonneg (hA.2 (x := x) hx) (hB.2 x)⟩

中文:
引理 add_posSemidef
  结论: [AddLeftMono R]
  证明: ⟨hA.isHermitian.add hB.isHermitian, fun x hx => by
    simpa [mul_add,add_mul] using add_pos_of_pos_of_nonneg (hA.2 (x := x) hx) (hB.2 x)⟩
-/
protected lemma add_posSemidef [AddLeftMono R]
    {A : Matrix m m R} {B : Matrix m m R}
    (hA : A.PosDef) (hB : B.PosSemidef) : (A + B).PosDef :=
  ⟨hA.isHermitian.add hB.isHermitian, fun x hx => by
    simpa [mul_add,add_mul] using add_pos_of_pos_of_nonneg (hA.2 (x := x) hx) (hB.2 x)⟩

/--
lemma `posSemidef_add` / 引理 `posSemidef_add`

English:
lemma posSemidef_add
  statement: [AddLeftMono R]
  proof: add_comm A B ▸ hB.add_posSemidef hA

中文:
引理 posSemidef_add
  结论: [AddLeftMono R]
  证明: add_comm A B ▸ hB.add_posSemidef hA
-/
protected lemma posSemidef_add [AddLeftMono R]
    {A : Matrix m m R} {B : Matrix m m R}
    (hA : A.PosSemidef) (hB : B.PosDef) : (A + B).PosDef :=
  add_comm A B ▸ hB.add_posSemidef hA

/--
lemma `add` / 引理 `add`

English:
lemma add
  statement: [AddLeftMono R] {A : Matrix m m R} {B : Matrix m m R}
  proof: hA.add_posSemidef hB.posSemidef

中文:
引理 add
  结论: [AddLeftMono R] {A : 矩阵 m m R} {B : 矩阵 m m R}
  证明: hA.add_posSemidef hB.posSemidef
-/
protected lemma add [AddLeftMono R] {A : Matrix m m R} {B : Matrix m m R}
    (hA : A.PosDef) (hB : B.PosDef) : (A + B).PosDef :=
  hA.add_posSemidef hB.posSemidef

/--
theorem `_root_.Matrix.posDef_sum` / 定理 `_root_.Matrix.posDef_sum`

English:
theorem _root_.Matrix.posDef_sum
  statement: {ι : Type*} [AddLeftMono R] {A : ι -> Matrix m m R}
  proof: by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hs
  | insert i hi hins H =>
      rw [Finset.sum_insert hins]
      by_cases h : ¬ hi.Nonempty
      · simp_all
· exact PosDef.add (hA _ <| Finset.mem_insert_self i hi)
          H (not_not.mp h) fun _ _hi => hA _ (Finset.mem_insert_of_mem _hi)

中文:
定理 _root_.矩阵.posDef_sum
  结论: {ι : 类型} [AddLeftMono R] {A : ι -> 矩阵 m m R}
  证明: by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hs
  | insert i hi hins H =>
      rw [Finset.sum_insert hins]
      by_cases h : ¬ hi.Nonempty
      · simp_all
· exact PosDef.add (hA _ <| Finset.mem_insert_self i hi)
          H (not_not.mp h) fun _ _hi => hA _ (Finset.mem_insert_of_mem _hi)

Depends on / 依赖: Finset, Finset.induction_on, Finset.mem_insert_of_mem, Finset.mem_insert_self, Finset.sum_insert, Nonempty, PosDef, PosDef.add, classical, hi.Nonempty, induction_on, insert, mem_insert_of_mem, mem_insert_self, not_not, not_not.mp, sum_insert
-/
theorem _root_.Matrix.posDef_sum {ι : Type*} [AddLeftMono R] {A : ι -> Matrix m m R}
    {s : Finset ι} (hs : s.Nonempty) (hA : forall i in s, (A i).PosDef) : (∑ i in s, A i).PosDef := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hs
  | insert i hi hins H =>
      rw [Finset.sum_insert hins]
      by_cases h : ¬ hi.Nonempty
      · simp_all
· exact PosDef.add (hA _ <| Finset.mem_insert_self i hi)
          H (not_not.mp h) fun _ _hi => hA _ (Finset.mem_insert_of_mem _hi)

/--
theorem `smul` / 定理 `smul`

English:
theorem smul
  statement: {α : Type*} [CommSemiring α] [PartialOrder α] [StarRing α]
  proof: by
  refine ⟨IsSelfAdjoint.smul (IsSelfAdjoint.of_nonneg ha.le) hx.1, fun y hy => ?_⟩
  simpa [← Finsupp.smul_sum] using smul_pos ha (hx.2 hy)

中文:
定理 smul
  结论: {α : 类型} [交换半环 α] [偏序 α] [对合环 α]
  证明: by
  refine ⟨IsSelfAdjoint.smul (IsSelfAdjoint.of_nonneg ha.le) hx.1, fun y hy => ?_⟩
  simpa [← Finsupp.smul_sum] using smul_pos ha (hx.2 hy)
-/
protected theorem smul {α : Type*} [CommSemiring α] [PartialOrder α] [StarRing α]
    [StarOrderedRing α] [Algebra α R] [StarModule α R] [PosSMulStrictMono α R]
    {x : Matrix n n R} (hx : x.PosDef) {a : α} (ha : 0 < a) : (a • x).PosDef := by
  refine ⟨IsSelfAdjoint.smul (IsSelfAdjoint.of_nonneg ha.le) hx.1, fun y hy => ?_⟩
  simpa [← Finsupp.smul_sum] using smul_pos ha (hx.2 hy)

/--
theorem `conjTranspose` / 定理 `conjTranspose`

English:
theorem conjTranspose
  given: {M : Matrix n n R} (hM : M.PosDef)
  statement: Mᴴ.PosDef
  proof: hM.1.symm ▸ hM

@[simp]

中文:
定理 conjTranspose
  条件: {M : 矩阵 n n R} (hM : M.PosDef)
  结论: Mᴴ.PosDef
  证明: hM.1.symm ▸ hM

@[simp]
-/
theorem conjTranspose {M : Matrix n n R} (hM : M.PosDef) : Mᴴ.PosDef := hM.1.symm ▸ hM

@[simp]
/--
theorem `_root_.Matrix.posDef_conjTranspose_iff` / 定理 `_root_.Matrix.posDef_conjTranspose_iff`

English:
theorem _root_.Matrix.posDef_conjTranspose_iff
  given: {M : Matrix n n R}
  statement: Mᴴ.PosDef ↔ M.PosDef
  proof: ⟨(by simpa using ·.conjTranspose), .conjTranspose⟩

中文:
定理 _root_.矩阵.posDef_conjTranspose_iff
  条件: {M : 矩阵 n n R}
  结论: Mᴴ.PosDef ↔ M.PosDef
  证明: ⟨(by simpa using ·.conjTranspose), .conjTranspose⟩

Depends on / 依赖: conjTranspose
-/
theorem _root_.Matrix.posDef_conjTranspose_iff {M : Matrix n n R} : Mᴴ.PosDef ↔ M.PosDef :=
  ⟨(by simpa using ·.conjTranspose), .conjTranspose⟩

/--
lemma `diag_pos` / 引理 `diag_pos`

English:
lemma diag_pos
  given: [Nontrivial R] {A : Matrix n n R} (hA : A.PosDef) {i : n}
  statement: 0 < A i i
  proof: by
  simpa [trace] using hA.2 (x := Finsupp.single i 1)

中文:
引理 diag_pos
  条件: [非平凡 R] {A : 矩阵 n n R} (hA : A.PosDef) {i : n}
  结论: 0 < A i i
  证明: by
  simpa [trace] using hA.2 (x := Finsupp.single i 1)

Depends on / 依赖: Finsupp, Finsupp.single, single
-/
lemma diag_pos [Nontrivial R] {A : Matrix n n R} (hA : A.PosDef) {i : n} : 0 < A i i := by
  simpa [trace] using hA.2 (x := Finsupp.single i 1)

end PosDef

/-!
## Finite positive semidefinite matrices
-/

variable [Fintype n] [Fintype m]

/--
theorem `posSemidef_iff_dotProduct_mulVec` / 定理 `posSemidef_iff_dotProduct_mulVec`

English:
theorem posSemidef_iff_dotProduct_mulVec
  given: {M : Matrix n n R}
  proof: by
  simp [PosSemidef, ← Finsupp.equivFunOnFinite.forall_congr_right, dotProduct, mulVec,
    Finsupp.sum_fintype, Finset.mul_sum, mul_assoc]

中文:
定理 posSemidef_iff_dotProduct_mulVec
  条件: {M : 矩阵 n n R}
  证明: by
  simp [PosSemidef, ← Finsupp.equivFunOnFinite.forall_congr_right, dotProduct, mulVec,
    Finsupp.sum_fintype, Finset.mul_sum, mul_assoc]

Depends on / 依赖: Finset, Finset.mul_sum, Finsupp, Finsupp.equivFunOnFinite.forall_congr_right, Finsupp.sum_fintype, PosSemidef, dotProduct, equivFunOnFinite, forall_congr_right, mulVec, mul_assoc, mul_sum, sum_fintype
-/
theorem posSemidef_iff_dotProduct_mulVec {M : Matrix n n R} :
    M.PosSemidef ↔ M.IsHermitian ∧ forall x, 0 <= star x ⬝ᵥ (M *ᵥ x) := by
  simp [PosSemidef, ← Finsupp.equivFunOnFinite.forall_congr_right, dotProduct, mulVec,
    Finsupp.sum_fintype, Finset.mul_sum, mul_assoc]

namespace PosSemidef

@[simp]
/--
theorem `dotProduct_mulVec_nonneg` / 定理 `dotProduct_mulVec_nonneg`

English:
theorem dotProduct_mulVec_nonneg
  given: {M : Matrix n n R} (hM : M.PosSemidef)
  proof: (posSemidef_iff_dotProduct_mulVec.mp hM).2

中文:
定理 dotProduct_mulVec_nonneg
  条件: {M : 矩阵 n n R} (hM : M.PosSemidef)
  证明: (posSemidef_iff_dotProduct_mulVec.mp hM).2

Depends on / 依赖: posSemidef_iff_dotProduct_mulVec, posSemidef_iff_dotProduct_mulVec.mp
-/
theorem dotProduct_mulVec_nonneg {M : Matrix n n R} (hM : M.PosSemidef) :
    forall x : n -> R, 0 <= star x ⬝ᵥ (M *ᵥ x) := (posSemidef_iff_dotProduct_mulVec.mp hM).2

/--
lemma `of_dotProduct_mulVec_nonneg` / 引理 `of_dotProduct_mulVec_nonneg`

English:
lemma of_dotProduct_mulVec_nonneg
  statement: {M : Matrix n n R} (hM1 : M.IsHermitian)
  proof: posSemidef_iff_dotProduct_mulVec.mpr ⟨hM1, hM2⟩

omit [Fintype m] in variable [Finite m] in

中文:
引理 of_dotProduct_mulVec_nonneg
  结论: {M : 矩阵 n n R} (hM1 : M.IsHermitian)
  证明: posSemidef_iff_dotProduct_mulVec.mpr ⟨hM1, hM2⟩

omit [Fintype m] in variable [Finite m] in

Depends on / 依赖: posSemidef_iff_dotProduct_mulVec, posSemidef_iff_dotProduct_mulVec.mpr
-/
lemma of_dotProduct_mulVec_nonneg {M : Matrix n n R} (hM1 : M.IsHermitian)
    (hM2 : forall x, 0 <= star x ⬝ᵥ (M *ᵥ x)) : M.PosSemidef :=
  posSemidef_iff_dotProduct_mulVec.mpr ⟨hM1, hM2⟩

omit [Fintype m] in variable [Finite m] in
/--
lemma `conjTranspose_mul_mul_same` / 引理 `conjTranspose_mul_mul_same`

English:
lemma conjTranspose_mul_mul_same
  given: {A : Matrix n n R} (hA : PosSemidef A) (B : Matrix n m R)
  proof: by
  have := Fintype.ofFinite m
  refine of_dotProduct_mulVec_nonneg (isHermitian_conjTranspose_mul_mul B hA.1) fun x => ?_
  simpa only [star_mulVec, dotProduct_mulVec, vecMul_vecMul] using
      hA.dotProduct_mulVec_nonneg (B *ᵥ x)

omit [Fintype m] in variable [Finite m] in

中文:
引理 conjTranspose_mul_mul_same
  条件: {A : 矩阵 n n R} (hA : PosSemidef A) (B : 矩阵 n m R)
  证明: by
  have := Fintype.ofFinite m
  refine of_dotProduct_mulVec_nonneg (isHermitian_conjTranspose_mul_mul B hA.1) fun x => ?_
  simpa only [star_mulVec, dotProduct_mulVec, vecMul_vecMul] using
      hA.dotProduct_mulVec_nonneg (B *ᵥ x)

omit [Fintype m] in variable [Finite m] in

Depends on / 依赖: Fintype, Fintype.ofFinite, dotProduct_mulVec, dotProduct_mulVec_nonneg, hA.dotProduct_mulVec_nonneg, isHermitian_conjTranspose_mul_mul, ofFinite, of_dotProduct_mulVec_nonneg, star_mulVec, vecMul_vecMul
-/
lemma conjTranspose_mul_mul_same {A : Matrix n n R} (hA : PosSemidef A) (B : Matrix n m R) :
    PosSemidef (Bᴴ * A * B) := by
  have := Fintype.ofFinite m
  refine of_dotProduct_mulVec_nonneg (isHermitian_conjTranspose_mul_mul B hA.1) fun x => ?_
  simpa only [star_mulVec, dotProduct_mulVec, vecMul_vecMul] using
      hA.dotProduct_mulVec_nonneg (B *ᵥ x)

omit [Fintype m] in variable [Finite m] in
/--
lemma `mul_mul_conjTranspose_same` / 引理 `mul_mul_conjTranspose_same`

English:
lemma mul_mul_conjTranspose_same
  given: {A : Matrix n n R} (hA : PosSemidef A) (B : Matrix m n R)
  proof: by
  simpa only [conjTranspose_conjTranspose] using hA.conjTranspose_mul_mul_same Bᴴ

中文:
引理 mul_mul_conjTranspose_same
  条件: {A : 矩阵 n n R} (hA : PosSemidef A) (B : 矩阵 m n R)
  证明: by
  simpa only [conjTranspose_conjTranspose] using hA.conjTranspose_mul_mul_same Bᴴ

Depends on / 依赖: conjTranspose_conjTranspose, conjTranspose_mul_mul_same, hA.conjTranspose_mul_mul_same
-/
lemma mul_mul_conjTranspose_same {A : Matrix n n R} (hA : PosSemidef A) (B : Matrix m n R) :
    PosSemidef (B * A * Bᴴ) := by
  simpa only [conjTranspose_conjTranspose] using hA.conjTranspose_mul_mul_same Bᴴ

/--
lemma `pow` / 引理 `pow`

English:
lemma pow
  statement: [StarOrderedRing R] [DecidableEq n]
  proof: match k with
  | 0 => .one
  | 1 => by simpa using hM
  | (k + 2) => by
    rw [pow_succ]; rw [pow_succ']
    simpa only [hM.isHermitian.eq] using (hM.pow k).mul_mul_conjTranspose_same M

中文:
引理 pow
  结论: [StarOrdered环 R] [DecidableEq n]
  证明: match k with
  | 0 => .one
  | 1 => by simpa using hM
  | (k + 2) => by
    rw [pow_succ]; rw [pow_succ']
    simpa only [hM.isHermitian.eq] using (hM.pow k).mul_mul_conjTranspose_same M
-/
protected lemma pow [StarOrderedRing R] [DecidableEq n]
    {M : Matrix n n R} (hM : M.PosSemidef) (k : Nat) :
    PosSemidef (M ^ k) :=
  match k with
  | 0 => .one
  | 1 => by simpa using hM
  | (k + 2) => by
    rw [pow_succ]; rw [pow_succ']
    simpa only [hM.isHermitian.eq] using (hM.pow k).mul_mul_conjTranspose_same M

/--
lemma `inv` / 引理 `inv`

English:
lemma inv
  given: [DecidableEq n] {M : Matrix n n R'} (hM : M.PosSemidef)
  statement: M⁻¹.PosSemidef
  proof: by
  by_cases h : IsUnit M.det
  · have := (conjTranspose_mul_mul_same hM M⁻¹).conjTranspose
    rwa [mul_nonsing_inv_cancel_right _ _ h, conjTranspose_conjTranspose] at this
  · rw [nonsing_inv_apply_not_isUnit _ h]
    exact .zero

中文:
引理 inv
  条件: [DecidableEq n] {M : 矩阵 n n R'} (hM : M.PosSemidef)
  结论: M⁻¹.PosSemidef
  证明: by
  by_cases h : IsUnit M.det
  · have := (conjTranspose_mul_mul_same hM M⁻¹).conjTranspose
    rwa [mul_nonsing_inv_cancel_right _ _ h, conjTranspose_conjTranspose] at this
  · rw [nonsing_inv_apply_not_isUnit _ h]
    exact .zero
-/
protected lemma inv [DecidableEq n] {M : Matrix n n R'} (hM : M.PosSemidef) : M⁻¹.PosSemidef := by
  by_cases h : IsUnit M.det
  · have := (conjTranspose_mul_mul_same hM M⁻¹).conjTranspose
    rwa [mul_nonsing_inv_cancel_right _ _ h, conjTranspose_conjTranspose] at this
  · rw [nonsing_inv_apply_not_isUnit _ h]
    exact .zero

/--
lemma `zpow` / 引理 `zpow`

English:
lemma zpow
  statement: [StarOrderedRing R'] [DecidableEq n]
  proof: by
  obtain ⟨n, rfl | rfl⟩ := z.eq_nat_or_neg
  · simpa using hM.pow n
  · simpa using (hM.pow n).inv

中文:
引理 zpow
  结论: [StarOrdered环 R'] [DecidableEq n]
  证明: by
  obtain ⟨n, rfl | rfl⟩ := z.eq_nat_or_neg
  · simpa using hM.pow n
  · simpa using (hM.pow n).inv
-/
protected lemma zpow [StarOrderedRing R'] [DecidableEq n]
    {M : Matrix n n R'} (hM : M.PosSemidef) (z : Int) :
    (M ^ z).PosSemidef := by
  obtain ⟨n, rfl | rfl⟩ := z.eq_nat_or_neg
  · simpa using hM.pow n
  · simpa using (hM.pow n).inv

/--
lemma `trace_nonneg` / 引理 `trace_nonneg`

English:
lemma trace_nonneg
  given: [AddLeftMono R] {A : Matrix n n R} (hA : A.PosSemidef)
  statement: 0 <= A.trace
  proof: Fintype.sum_nonneg fun _ => hA.diag_nonneg

中文:
引理 trace_nonneg
  条件: [AddLeftMono R] {A : 矩阵 n n R} (hA : A.PosSemidef)
  结论: 0 <= A.trace
  证明: Fintype.sum_nonneg fun _ => hA.diag_nonneg

Depends on / 依赖: Fintype, Fintype.sum_nonneg, diag_nonneg, hA.diag_nonneg, sum_nonneg
-/
lemma trace_nonneg [AddLeftMono R] {A : Matrix n n R} (hA : A.PosSemidef) : 0 <= A.trace :=
  Fintype.sum_nonneg fun _ => hA.diag_nonneg

end PosSemidef

omit [Fintype n] in variable [Finite n] in
/--
theorem `posSemidef_conjTranspose_mul_self` / 定理 `posSemidef_conjTranspose_mul_self`

English:
theorem posSemidef_conjTranspose_mul_self
  given: [StarOrderedRing R] (A : Matrix m n R)
  proof: by
  have := Fintype.ofFinite n
  refine .of_dotProduct_mulVec_nonneg (isHermitian_conjTranspose_mul_self _) fun x => ?_
  rw [← mulVec_mulVec]; rw [dotProduct_mulVec]; rw [vecMul_conjTranspose]; rw [star_star]
  exact Finset.sum_nonneg fun i _ => star_mul_self_nonneg _

omit [Fintype m] in variable [Finite m] in

中文:
定理 posSemidef_conjTranspose_mul_self
  条件: [StarOrdered环 R] (A : 矩阵 m n R)
  证明: by
  have := Fintype.ofFinite n
  refine .of_dotProduct_mulVec_nonneg (isHermitian_conjTranspose_mul_self _) fun x => ?_
  rw [← mulVec_mulVec]; rw [dotProduct_mulVec]; rw [vecMul_conjTranspose]; rw [star_star]
  exact Finset.sum_nonneg fun i _ => star_mul_self_nonneg _

omit [Fintype m] in variable [Finite m] in

Depends on / 依赖: Finset, Finset.sum_nonneg, Fintype, Fintype.ofFinite, dotProduct_mulVec, isHermitian_conjTranspose_mul_self, mulVec_mulVec, ofFinite, of_dotProduct_mulVec_nonneg, star_mul_self_nonneg, star_star, sum_nonneg, vecMul_conjTranspose
-/
theorem posSemidef_conjTranspose_mul_self [StarOrderedRing R] (A : Matrix m n R) :
    PosSemidef (Aᴴ * A) := by
  have := Fintype.ofFinite n
  refine .of_dotProduct_mulVec_nonneg (isHermitian_conjTranspose_mul_self _) fun x => ?_
  rw [← mulVec_mulVec]; rw [dotProduct_mulVec]; rw [vecMul_conjTranspose]; rw [star_star]
  exact Finset.sum_nonneg fun i _ => star_mul_self_nonneg _

omit [Fintype m] in variable [Finite m] in
/--
theorem `posSemidef_self_mul_conjTranspose` / 定理 `posSemidef_self_mul_conjTranspose`

English:
theorem posSemidef_self_mul_conjTranspose
  given: [StarOrderedRing R] (A : Matrix m n R)
  proof: by
  simpa only [conjTranspose_conjTranspose] using posSemidef_conjTranspose_mul_self Aᴴ

中文:
定理 posSemidef_self_mul_conjTranspose
  条件: [StarOrdered环 R] (A : 矩阵 m n R)
  证明: by
  simpa only [conjTranspose_conjTranspose] using posSemidef_conjTranspose_mul_self Aᴴ

Depends on / 依赖: conjTranspose_conjTranspose, posSemidef_conjTranspose_mul_self
-/
theorem posSemidef_self_mul_conjTranspose [StarOrderedRing R] (A : Matrix m n R) :
    PosSemidef (A * Aᴴ) := by
  simpa only [conjTranspose_conjTranspose] using posSemidef_conjTranspose_mul_self Aᴴ

section trace
-- TODO: move these results to an earlier file

variable {R : Type*} [PartialOrder R] [NonUnitalRing R]
  [StarRing R] [StarOrderedRing R] [NoZeroDivisors R]

/--
theorem `trace_conjTranspose_mul_self_eq_zero_iff` / 定理 `trace_conjTranspose_mul_self_eq_zero_iff`

English:
theorem trace_conjTranspose_mul_self_eq_zero_iff
  given: {A : Matrix m n R}
  proof: by
  rw [← star_vec_dotProduct_vec]; rw [dotProduct_star_self_eq_zero]; rw [vec_eq_zero_iff]

中文:
定理 trace_conjTranspose_mul_self_eq_zero_iff
  条件: {A : 矩阵 m n R}
  证明: by
  rw [← star_vec_dotProduct_vec]; rw [dotProduct_star_self_eq_zero]; rw [vec_eq_zero_iff]

Depends on / 依赖: dotProduct_star_self_eq_zero, star_vec_dotProduct_vec, vec_eq_zero_iff
-/
theorem trace_conjTranspose_mul_self_eq_zero_iff {A : Matrix m n R} :
    (Aᴴ * A).trace = 0 ↔ A = 0 := by
  rw [← star_vec_dotProduct_vec]; rw [dotProduct_star_self_eq_zero]; rw [vec_eq_zero_iff]

/--
theorem `trace_mul_conjTranspose_self_eq_zero_iff` / 定理 `trace_mul_conjTranspose_self_eq_zero_iff`

English:
theorem trace_mul_conjTranspose_self_eq_zero_iff
  given: {A : Matrix m n R}
  proof: by
  simpa using trace_conjTranspose_mul_self_eq_zero_iff (A := Aᴴ)

中文:
定理 trace_mul_conjTranspose_self_eq_zero_iff
  条件: {A : 矩阵 m n R}
  证明: by
  simpa using trace_conjTranspose_mul_self_eq_zero_iff (A := Aᴴ)

Depends on / 依赖: trace_conjTranspose_mul_self_eq_zero_iff
-/
theorem trace_mul_conjTranspose_self_eq_zero_iff {A : Matrix m n R} :
    (A * Aᴴ).trace = 0 ↔ A = 0 := by
  simpa using trace_conjTranspose_mul_self_eq_zero_iff (A := Aᴴ)

end trace

section conjugate
variable [DecidableEq n] {U x : Matrix n n R}

/--
theorem `IsUnit.posSemidef_star_left_conjugate_iff` / 定理 `IsUnit.posSemidef_star_left_conjugate_iff`

English:
theorem IsUnit.posSemidef_star_left_conjugate_iff
  given: (hU : IsUnit U)
  proof: by
  refine ⟨fun h => ?_, fun h => h.conjTranspose_mul_mul_same _⟩
  lift U to (Matrix n n R)ˣ using hU
  have := h.conjTranspose_mul_mul_same ((U⁻¹ : (Matrix n n R)ˣ) : Matrix n n R)
  rwa [← star_eq_conjTranspose, ← mul_assoc, ← mul_assoc, ← star_mul, mul_assoc,
    Units.mul_inv, mul_one, star_one, one_mul] at this

中文:
定理 是单位.posSemidef_star_left_conjugate_iff
  条件: (hU : 是单位 U)
  证明: by
  refine ⟨fun h => ?_, fun h => h.conjTranspose_mul_mul_same _⟩
  lift U to (Matrix n n R)ˣ using hU
  have := h.conjTranspose_mul_mul_same ((U⁻¹ : (Matrix n n R)ˣ) : Matrix n n R)
  rwa [← star_eq_conjTranspose, ← mul_assoc, ← mul_assoc, ← star_mul, mul_assoc,
    Units.mul_inv, mul_one, star_one, one_mul] at this

Depends on / 依赖: Matrix, Units.mul_inv, conjTranspose_mul_mul_same, h.conjTranspose_mul_mul_same, mul_assoc, mul_inv, mul_one, one_mul, star_eq_conjTranspose, star_mul, star_one
-/
theorem IsUnit.posSemidef_star_left_conjugate_iff (hU : IsUnit U) :
    PosSemidef (star U * x * U) ↔ x.PosSemidef := by
  refine ⟨fun h => ?_, fun h => h.conjTranspose_mul_mul_same _⟩
  lift U to (Matrix n n R)ˣ using hU
  have := h.conjTranspose_mul_mul_same ((U⁻¹ : (Matrix n n R)ˣ) : Matrix n n R)
  rwa [← star_eq_conjTranspose, ← mul_assoc, ← mul_assoc, ← star_mul, mul_assoc,
    Units.mul_inv, mul_one, star_one, one_mul] at this

/--
theorem `IsUnit.posSemidef_star_right_conjugate_iff` / 定理 `IsUnit.posSemidef_star_right_conjugate_iff`

English:
theorem IsUnit.posSemidef_star_right_conjugate_iff
  given: (hU : IsUnit U)
  proof: by
  simpa using hU.star.posSemidef_star_left_conjugate_iff

中文:
定理 是单位.posSemidef_star_right_conjugate_iff
  条件: (hU : 是单位 U)
  证明: by
  simpa using hU.star.posSemidef_star_left_conjugate_iff

Depends on / 依赖: hU.star.posSemidef_star_left_conjugate_iff, posSemidef_star_left_conjugate_iff
-/
theorem IsUnit.posSemidef_star_right_conjugate_iff (hU : IsUnit U) :
    PosSemidef (U * x * star U) ↔ x.PosSemidef := by
  simpa using hU.star.posSemidef_star_left_conjugate_iff

end conjugate

omit [Fintype n] [Fintype m] in variable [Finite n] [Finite m] in
/--
theorem `posSemidef_vecMulVec_self_star` / 定理 `posSemidef_vecMulVec_self_star`

English:
theorem posSemidef_vecMulVec_self_star
  given: [StarOrderedRing R] (a : n -> R)
  proof: by
  simp [vecMulVec_eq Unit, ← conjTranspose_replicateCol, posSemidef_self_mul_conjTranspose]

omit [Fintype n] in variable [Finite n] in

中文:
定理 posSemidef_vecMulVec_self_star
  条件: [StarOrdered环 R] (a : n -> R)
  证明: by
  simp [vecMulVec_eq Unit, ← conjTranspose_replicateCol, posSemidef_self_mul_conjTranspose]

omit [Fintype n] in variable [Finite n] in

Depends on / 依赖: conjTranspose_replicateCol, posSemidef_self_mul_conjTranspose, vecMulVec_eq
-/
theorem posSemidef_vecMulVec_self_star [StarOrderedRing R] (a : n -> R) :
    (vecMulVec a (star a)).PosSemidef := by
  simp [vecMulVec_eq Unit, ← conjTranspose_replicateCol, posSemidef_self_mul_conjTranspose]

omit [Fintype n] in variable [Finite n] in
/--
theorem `posSemidef_vecMulVec_star_self` / 定理 `posSemidef_vecMulVec_star_self`

English:
theorem posSemidef_vecMulVec_star_self
  given: [StarOrderedRing R] (a : n -> R)
  proof: by
  simp [vecMulVec_eq Unit, ← conjTranspose_replicateRow, posSemidef_conjTranspose_mul_self]

中文:
定理 posSemidef_vecMulVec_star_self
  条件: [StarOrdered环 R] (a : n -> R)
  证明: by
  simp [vecMulVec_eq Unit, ← conjTranspose_replicateRow, posSemidef_conjTranspose_mul_self]

Depends on / 依赖: conjTranspose_replicateRow, posSemidef_conjTranspose_mul_self, vecMulVec_eq
-/
theorem posSemidef_vecMulVec_star_self [StarOrderedRing R] (a : n -> R) :
    (vecMulVec (star a) a).PosSemidef := by
  simp [vecMulVec_eq Unit, ← conjTranspose_replicateRow, posSemidef_conjTranspose_mul_self]


/--
theorem `posDef_iff_dotProduct_mulVec` / 定理 `posDef_iff_dotProduct_mulVec`

English:
theorem posDef_iff_dotProduct_mulVec
  given: {M : Matrix n n R}
  proof: by
  have (x : n ->₀ R) : x = 0 ↔ Finsupp.equivFunOnFinite x = 0 :=
    ⟨fun h1 => Finsupp.coe_eq_zero.mpr h1,fun h2 => Finsupp.coe_eq_zero.mp h2⟩
  simp [PosDef, ← Finsupp.equivFunOnFinite.forall_congr_right, dotProduct, mulVec,
    Finsupp.sum_fintype, Finset.mul_sum, mul_assoc, this]

中文:
定理 posDef_iff_dotProduct_mulVec
  条件: {M : 矩阵 n n R}
  证明: by
  have (x : n ->₀ R) : x = 0 ↔ Finsupp.equivFunOnFinite x = 0 :=
    ⟨fun h1 => Finsupp.coe_eq_zero.mpr h1,fun h2 => Finsupp.coe_eq_zero.mp h2⟩
  simp [PosDef, ← Finsupp.equivFunOnFinite.forall_congr_right, dotProduct, mulVec,
    Finsupp.sum_fintype, Finset.mul_sum, mul_assoc, this]

Depends on / 依赖: Finset, Finset.mul_sum, Finsupp, Finsupp.coe_eq_zero.mp, Finsupp.coe_eq_zero.mpr, Finsupp.equivFunOnFinite, Finsupp.equivFunOnFinite.forall_congr_right, Finsupp.sum_fintype, PosDef, coe_eq_zero, dotProduct, equivFunOnFinite, forall_congr_right, mulVec, mul_assoc, mul_sum, sum_fintype
-/
theorem posDef_iff_dotProduct_mulVec {M : Matrix n n R} :
    M.PosDef ↔ M.IsHermitian ∧ forall ⦃x⦄, x != 0 -> 0 < star x ⬝ᵥ (M *ᵥ x) := by
  have (x : n ->₀ R) : x = 0 ↔ Finsupp.equivFunOnFinite x = 0 :=
    ⟨fun h1 => Finsupp.coe_eq_zero.mpr h1,fun h2 => Finsupp.coe_eq_zero.mp h2⟩
  simp [PosDef, ← Finsupp.equivFunOnFinite.forall_congr_right, dotProduct, mulVec,
    Finsupp.sum_fintype, Finset.mul_sum, mul_assoc, this]

namespace PosDef

/-- A matrix `M : Matrix n n R` is positive definite if it is Hermitian
and `xᴴMx` is greater than zero for all nonzero `x`. -/
@[simp]
/--
lemma `dotProduct_mulVec_pos` / 引理 `dotProduct_mulVec_pos`

English:
lemma dotProduct_mulVec_pos
  given: {M : Matrix n n R} (hM : M.PosDef) {x} (hx : x != 0)
  proof: (posDef_iff_dotProduct_mulVec.mp hM).2 hx

中文:
引理 dotProduct_mulVec_pos
  条件: {M : 矩阵 n n R} (hM : M.PosDef) {x} (hx : x != 0)
  证明: (posDef_iff_dotProduct_mulVec.mp hM).2 hx

Depends on / 依赖: posDef_iff_dotProduct_mulVec, posDef_iff_dotProduct_mulVec.mp
-/
lemma dotProduct_mulVec_pos {M : Matrix n n R} (hM : M.PosDef) {x} (hx : x != 0) :
    0 < star x ⬝ᵥ (M *ᵥ x) := (posDef_iff_dotProduct_mulVec.mp hM).2 hx

/--
lemma `of_dotProduct_mulVec_pos` / 引理 `of_dotProduct_mulVec_pos`

English:
lemma of_dotProduct_mulVec_pos
  statement: {M : Matrix n n R} (hM1 : M.IsHermitian)
  proof: posDef_iff_dotProduct_mulVec.mpr ⟨hM1, hM2⟩

中文:
引理 of_dotProduct_mulVec_pos
  结论: {M : 矩阵 n n R} (hM1 : M.IsHermitian)
  证明: posDef_iff_dotProduct_mulVec.mpr ⟨hM1, hM2⟩

Depends on / 依赖: posDef_iff_dotProduct_mulVec, posDef_iff_dotProduct_mulVec.mpr
-/
lemma of_dotProduct_mulVec_pos {M : Matrix n n R} (hM1 : M.IsHermitian)
    (hM2 : forall ⦃x⦄, x != 0 -> 0 < star x ⬝ᵥ (M *ᵥ x)) : M.PosDef :=
  posDef_iff_dotProduct_mulVec.mpr ⟨hM1, hM2⟩

/--
lemma `conjTranspose_mul_mul_same` / 引理 `conjTranspose_mul_mul_same`

English:
lemma conjTranspose_mul_mul_same
  statement: {A : Matrix n n R} {B : Matrix n m R} (hA : A.PosDef)
  proof: by
  refine of_dotProduct_mulVec_pos (isHermitian_conjTranspose_mul_mul _ hA.1) fun x hx => ?_
have : B *ᵥ x != 0 := fun h => hx .1 h hB.eq_iff' (mulVec_zero _)
  simpa only [star_mulVec, dotProduct_mulVec, vecMul_vecMul] using hA.dotProduct_mulVec_pos this

中文:
引理 conjTranspose_mul_mul_same
  结论: {A : 矩阵 n n R} {B : 矩阵 n m R} (hA : A.PosDef)
  证明: by
  refine of_dotProduct_mulVec_pos (isHermitian_conjTranspose_mul_mul _ hA.1) fun x hx => ?_
have : B *ᵥ x != 0 := fun h => hx .1 h hB.eq_iff' (mulVec_zero _)
  simpa only [star_mulVec, dotProduct_mulVec, vecMul_vecMul] using hA.dotProduct_mulVec_pos this

Depends on / 依赖: dotProduct_mulVec, dotProduct_mulVec_pos, eq_iff, hA.dotProduct_mulVec_pos, hB.eq_iff, isHermitian_conjTranspose_mul_mul, mulVec_zero, of_dotProduct_mulVec_pos, star_mulVec, vecMul_vecMul
-/
lemma conjTranspose_mul_mul_same {A : Matrix n n R} {B : Matrix n m R} (hA : A.PosDef)
    (hB : Function.Injective B.mulVec) :
    (Bᴴ * A * B).PosDef := by
  refine of_dotProduct_mulVec_pos (isHermitian_conjTranspose_mul_mul _ hA.1) fun x hx => ?_
have : B *ᵥ x != 0 := fun h => hx .1 h hB.eq_iff' (mulVec_zero _)
  simpa only [star_mulVec, dotProduct_mulVec, vecMul_vecMul] using hA.dotProduct_mulVec_pos this

/--
lemma `mul_mul_conjTranspose_same` / 引理 `mul_mul_conjTranspose_same`

English:
lemma mul_mul_conjTranspose_same
  statement: {A : Matrix n n R} {B : Matrix m n R} (hA : A.PosDef)
  proof: by
replace hB := star_injective.comp hB.comp star_injective
  simp_rw [Function.comp_def, star_vecMul, star_star] at hB
  simpa using hA.conjTranspose_mul_mul_same (B := Bᴴ) hB

中文:
引理 mul_mul_conjTranspose_same
  结论: {A : 矩阵 n n R} {B : 矩阵 m n R} (hA : A.PosDef)
  证明: by
replace hB := star_injective.comp hB.comp star_injective
  simp_rw [Function.comp_def, star_vecMul, star_star] at hB
  simpa using hA.conjTranspose_mul_mul_same (B := Bᴴ) hB

Depends on / 依赖: Function, Function.comp_def, comp_def, conjTranspose_mul_mul_same, hA.conjTranspose_mul_mul_same, hB.comp, replace, simp_rw, star_injective, star_injective.comp, star_star, star_vecMul
-/
lemma mul_mul_conjTranspose_same {A : Matrix n n R} {B : Matrix m n R} (hA : A.PosDef)
    (hB : Function.Injective B.vecMul) :
    (B * A * Bᴴ).PosDef := by
replace hB := star_injective.comp hB.comp star_injective
  simp_rw [Function.comp_def, star_vecMul, star_star] at hB
  simpa using hA.conjTranspose_mul_mul_same (B := Bᴴ) hB

/--
theorem `conjTranspose_mul_self` / 定理 `conjTranspose_mul_self`

English:
theorem conjTranspose_mul_self
  statement: [StarOrderedRing R] [NoZeroDivisors R] (A : Matrix m n R)
  proof: by
  classical
  simpa using conjTranspose_mul_mul_same .one hA

中文:
定理 conjTranspose_mul_self
  结论: [StarOrdered环 R] [无零因子 R] (A : 矩阵 m n R)
  证明: by
  classical
  simpa using conjTranspose_mul_mul_same .one hA

Depends on / 依赖: classical, conjTranspose_mul_mul_same
-/
theorem conjTranspose_mul_self [StarOrderedRing R] [NoZeroDivisors R] (A : Matrix m n R)
    (hA : Function.Injective A.mulVec) :
    PosDef (Aᴴ * A) := by
  classical
  simpa using conjTranspose_mul_mul_same .one hA

/--
theorem `mul_conjTranspose_self` / 定理 `mul_conjTranspose_self`

English:
theorem mul_conjTranspose_self
  statement: [StarOrderedRing R] [NoZeroDivisors R] (A : Matrix m n R)
  proof: by
  classical
  simpa using mul_mul_conjTranspose_same .one hA

中文:
定理 mul_conjTranspose_self
  结论: [StarOrdered环 R] [无零因子 R] (A : 矩阵 m n R)
  证明: by
  classical
  simpa using mul_mul_conjTranspose_same .one hA

Depends on / 依赖: classical, mul_mul_conjTranspose_same
-/
theorem mul_conjTranspose_self [StarOrderedRing R] [NoZeroDivisors R] (A : Matrix m n R)
    (hA : Function.Injective A.vecMul) :
    PosDef (A * Aᴴ) := by
  classical
  simpa using mul_mul_conjTranspose_same .one hA

/--
theorem `of_toQuadraticForm'` / 定理 `of_toQuadraticForm'`

English:
theorem of_toQuadraticForm'
  statement: {R : Type*} [CommRing R] [PartialOrder R] [StarRing R] [TrivialStar R]
  proof: by
  refine of_dotProduct_mulVec_pos (by simpa) fun x hx => ?_
  simpa [toQuadraticForm', toLinearMap₂'_apply'] using hMq x hx

中文:
定理 of_toQuadraticForm'
  结论: {R : 类型} [交换环 R] [偏序 R] [对合环 R] [TrivialStar R]
  证明: by
  refine of_dotProduct_mulVec_pos (by simpa) fun x hx => ?_
  simpa [toQuadraticForm', toLinearMap₂'_apply'] using hMq x hx

Depends on / 依赖: _apply, of_dotProduct_mulVec_pos, toQuadraticForm
-/
theorem of_toQuadraticForm' {R : Type*} [CommRing R] [PartialOrder R] [StarRing R] [TrivialStar R]
    [DecidableEq n] {M : Matrix n n R} (hM : M.IsSymm)
    (hMq : M.toQuadraticForm'.PosDef) : M.PosDef := by
  refine of_dotProduct_mulVec_pos (by simpa) fun x hx => ?_
  simpa [toQuadraticForm', toLinearMap₂'_apply'] using hMq x hx

/--
theorem `toQuadraticForm'` / 定理 `toQuadraticForm'`

English:
theorem toQuadraticForm'
  statement: {R : Type*} [CommRing R] [PartialOrder R] [StarRing R] [TrivialStar R]
  proof: by
  intro x hx
  simpa [Matrix.toQuadraticForm', toLinearMap₂'_apply'] using hM.dotProduct_mulVec_pos hx

中文:
定理 toQuadraticForm'
  结论: {R : 类型} [交换环 R] [偏序 R] [对合环 R] [TrivialStar R]
  证明: by
  intro x hx
  simpa [Matrix.toQuadraticForm', toLinearMap₂'_apply'] using hM.dotProduct_mulVec_pos hx

Depends on / 依赖: Matrix, Matrix.toQuadraticForm, _apply, dotProduct_mulVec_pos, hM.dotProduct_mulVec_pos, toQuadraticForm
-/
theorem toQuadraticForm' {R : Type*} [CommRing R] [PartialOrder R] [StarRing R] [TrivialStar R]
    [DecidableEq n] {M : Matrix n n R} (hM : M.PosDef) :
    M.toQuadraticForm'.PosDef := by
  intro x hx
  simpa [Matrix.toQuadraticForm', toLinearMap₂'_apply'] using hM.dotProduct_mulVec_pos hx

/--
theorem `_root_.LinearMap.BilinForm.posDef_toQuadraticMap_iff_matrix` / 定理 `_root_.LinearMap.BilinForm.posDef_toQuadraticMap_iff_matrix`

English:
theorem _root_.LinearMap.BilinForm.posDef_toQuadraticMap_iff_matrix
  proof: by
  have aux (i j : n) (s t : R) : t * B (b i) (b j) * s = t * (s * B (b j) (b i)) := by
    grind [hB_symm.eq (b i) (b j)]
  refine ⟨fun h => ⟨?_, fun v hv => ?_⟩, fun h v hv => ?_⟩
  · simp [isHermitian_iff_isSymm, IsSymm.ext_iff, hB_symm.eq (b _) (b _)]
  · simpa [Finsupp.linearCombination_apply, map_finsuppSum, Finsupp.mul_sum, ← aux] using
      h _ (b.repr.symm.map_ne_zero_iff.mpr hv)
  · rw [B.toQuadraticMap_apply, ← b.linearCombination_repr (x := v)]
    simpa [Finsupp.linearCombination_apply, map_finsuppSum, Finsupp.mul_sum, aux]
      using h.2 (b.repr.map_ne_zero_iff.mpr hv)

中文:
定理 _root_.线性映射.BilinForm.posDef_toQuadraticMap_iff_matrix
  证明: by
  have aux (i j : n) (s t : R) : t * B (b i) (b j) * s = t * (s * B (b j) (b i)) := by
    grind [hB_symm.eq (b i) (b j)]
  refine ⟨fun h => ⟨?_, fun v hv => ?_⟩, fun h v hv => ?_⟩
  · simp [isHermitian_iff_isSymm, IsSymm.ext_iff, hB_symm.eq (b _) (b _)]
  · simpa [Finsupp.linearCombination_apply, map_finsuppSum, Finsupp.mul_sum, ← aux] using
      h _ (b.repr.symm.map_ne_zero_iff.mpr hv)
  · rw [B.toQuadraticMap_apply, ← b.linearCombination_repr (x := v)]
    simpa [Finsupp.linearCombination_apply, map_finsuppSum, Finsupp.mul_sum, aux]
      using h.2 (b.repr.map_ne_zero_iff.mpr hv)

Depends on / 依赖: B.toQuadraticMap_apply, Finsupp, Finsupp.linearCombination_apply, Finsupp.mul_sum, IsSymm, IsSymm.ext_iff, b.linearCombination_repr, b.repr.symm.map_ne_zero_iff.mpr, ext_iff, hB_symm, hB_symm.eq, isHermitian_iff_isSymm, linearCombination_apply, linearCombination_repr, map_finsuppSum, map_ne_zero_iff, mul_sum, toQuadraticMap_apply
-/
theorem _root_.LinearMap.BilinForm.posDef_toQuadraticMap_iff_matrix
    {R M : Type*} [CommRing R] [PartialOrder R] [StarRing R] [TrivialStar R]
    [AddCommGroup M] [Module R M] [DecidableEq n]
    (b : Module.Basis n R M) (B : LinearMap.BilinForm R M) (hB_symm : B.IsSymm) :
    B.toQuadraticMap.PosDef ↔ (B.toMatrix b).PosDef := by
  have aux (i j : n) (s t : R) : t * B (b i) (b j) * s = t * (s * B (b j) (b i)) := by
    grind [hB_symm.eq (b i) (b j)]
  refine ⟨fun h => ⟨?_, fun v hv => ?_⟩, fun h v hv => ?_⟩
  · simp [isHermitian_iff_isSymm, IsSymm.ext_iff, hB_symm.eq (b _) (b _)]
  · simpa [Finsupp.linearCombination_apply, map_finsuppSum, Finsupp.mul_sum, ← aux] using
      h _ (b.repr.symm.map_ne_zero_iff.mpr hv)
  · rw [B.toQuadraticMap_apply, ← b.linearCombination_repr (x := v)]
    simpa [Finsupp.linearCombination_apply, map_finsuppSum, Finsupp.mul_sum, aux]
      using h.2 (b.repr.map_ne_zero_iff.mpr hv)


/--
lemma `trace_pos` / 引理 `trace_pos`

English:
lemma trace_pos
  statement: [Nontrivial R] [IsOrderedCancelAddMonoid R] [Nonempty n] {A : Matrix n n R}
  proof: Finset.sum_pos (fun _ _ => hA.diag_pos) Finset.univ_nonempty

中文:
引理 trace_pos
  结论: [非平凡 R] [是OrderedCancelAdd幺半群 R] [非空 n] {A : 矩阵 n n R}
  证明: Finset.sum_pos (fun _ _ => hA.diag_pos) Finset.univ_nonempty

Depends on / 依赖: Finset, Finset.sum_pos, Finset.univ_nonempty, diag_pos, hA.diag_pos, sum_pos, univ_nonempty
-/
lemma trace_pos [Nontrivial R] [IsOrderedCancelAddMonoid R] [Nonempty n] {A : Matrix n n R}
    (hA : A.PosDef) : 0 < A.trace :=
  Finset.sum_pos (fun _ _ => hA.diag_pos) Finset.univ_nonempty

section Field
variable {K : Type*} [Field K] [PartialOrder K] [StarRing K]

/--
theorem `isUnit` / 定理 `isUnit`

English:
theorem isUnit
  given: [DecidableEq n] {M : Matrix n n K} (hM : M.PosDef)
  statement: IsUnit M
  proof: by
  by_contra h
  obtain ⟨a, ha, ha2⟩ : exists a != 0, M *ᵥ a = 0 := by
obtain ⟨a, b, ha⟩ := Function.not_injective_iff.mp mulVec_injective_iff_isUnit.not.mpr h
    exact ⟨a - b, by simp [sub_eq_zero, ha, mulVec_sub]⟩
  simpa [ha2] using hM.dotProduct_mulVec_pos ha

中文:
定理 isUnit
  条件: [DecidableEq n] {M : 矩阵 n n K} (hM : M.PosDef)
  结论: 是单位 M
  证明: by
  by_contra h
  obtain ⟨a, ha, ha2⟩ : exists a != 0, M *ᵥ a = 0 := by
obtain ⟨a, b, ha⟩ := Function.not_injective_iff.mp mulVec_injective_iff_isUnit.not.mpr h
    exact ⟨a - b, by simp [sub_eq_zero, ha, mulVec_sub]⟩
  simpa [ha2] using hM.dotProduct_mulVec_pos ha

Depends on / 依赖: Function, Function.not_injective_iff.mp, dotProduct_mulVec_pos, hM.dotProduct_mulVec_pos, mulVec_injective_iff_isUnit, mulVec_injective_iff_isUnit.not.mpr, mulVec_sub, not_injective_iff, sub_eq_zero
-/
theorem isUnit [DecidableEq n] {M : Matrix n n K} (hM : M.PosDef) : IsUnit M := by
  by_contra h
  obtain ⟨a, ha, ha2⟩ : exists a != 0, M *ᵥ a = 0 := by
obtain ⟨a, b, ha⟩ := Function.not_injective_iff.mp mulVec_injective_iff_isUnit.not.mpr h
    exact ⟨a - b, by simp [sub_eq_zero, ha, mulVec_sub]⟩
  simpa [ha2] using hM.dotProduct_mulVec_pos ha

/--
theorem `inv` / 定理 `inv`

English:
theorem inv
  given: [DecidableEq n] {M : Matrix n n K} (hM : M.PosDef)
  statement: M⁻¹.PosDef
  proof: by
  have := hM.mul_mul_conjTranspose_same (B := M⁻¹) ?_
  · let _ := hM.isUnit.invertible
    simpa using this.conjTranspose
  · simp only [Matrix.vecMul_injective_iff_isUnit, isUnit_nonsing_inv_iff, hM.isUnit]

@[simp]

中文:
定理 inv
  条件: [DecidableEq n] {M : 矩阵 n n K} (hM : M.PosDef)
  结论: M⁻¹.PosDef
  证明: by
  have := hM.mul_mul_conjTranspose_same (B := M⁻¹) ?_
  · let _ := hM.isUnit.invertible
    simpa using this.conjTranspose
  · simp only [Matrix.vecMul_injective_iff_isUnit, isUnit_nonsing_inv_iff, hM.isUnit]

@[simp]
-/
protected theorem inv [DecidableEq n] {M : Matrix n n K} (hM : M.PosDef) : M⁻¹.PosDef := by
  have := hM.mul_mul_conjTranspose_same (B := M⁻¹) ?_
  · let _ := hM.isUnit.invertible
    simpa using this.conjTranspose
  · simp only [Matrix.vecMul_injective_iff_isUnit, isUnit_nonsing_inv_iff, hM.isUnit]

@[simp]
/--
theorem `_root_.Matrix.posDef_inv_iff` / 定理 `_root_.Matrix.posDef_inv_iff`

English:
theorem _root_.Matrix.posDef_inv_iff
  given: [DecidableEq n] {M : Matrix n n K}
  proof: ⟨fun h =>
    letI := (Matrix.isUnit_nonsing_inv_iff.1 <| h.isUnit).invertible
    Matrix.inv_inv_of_invertible M ▸ h.inv, (·.inv)⟩

中文:
定理 _root_.矩阵.posDef_inv_iff
  条件: [DecidableEq n] {M : 矩阵 n n K}
  证明: ⟨fun h =>
    letI := (Matrix.isUnit_nonsing_inv_iff.1 <| h.isUnit).invertible
    Matrix.inv_inv_of_invertible M ▸ h.inv, (·.inv)⟩

Depends on / 依赖: Matrix, Matrix.inv_inv_of_invertible, Matrix.isUnit_nonsing_inv_iff, h.inv, h.isUnit, inv_inv_of_invertible, invertible, isUnit, isUnit_nonsing_inv_iff
-/
theorem _root_.Matrix.posDef_inv_iff [DecidableEq n] {M : Matrix n n K} :
    M⁻¹.PosDef ↔ M.PosDef :=
  ⟨fun h =>
    letI := (Matrix.isUnit_nonsing_inv_iff.1 <| h.isUnit).invertible
    Matrix.inv_inv_of_invertible M ▸ h.inv, (·.inv)⟩

end Field

section conjugate
variable [DecidableEq n] {x U : Matrix n n R}

/--
theorem `_root_.Matrix.IsUnit.posDef_star_left_conjugate_iff` / 定理 `_root_.Matrix.IsUnit.posDef_star_left_conjugate_iff`

English:
theorem _root_.Matrix.IsUnit.posDef_star_left_conjugate_iff
  given: (hU : IsUnit U)
  proof: by
refine ⟨fun h => ?_, fun h => h.conjTranspose_mul_mul_same mulVec_injective_of_isUnit hU⟩
  lift U to (Matrix n n R)ˣ using hU
  have := h.conjTranspose_mul_mul_same (mulVec_injective_of_isUnit (Units.isUnit U⁻¹))
  rwa [← star_eq_conjTranspose, ← mul_assoc, ← mul_assoc, ← star_mul, mul_assoc,
    Units.mul_inv, mul_one, star_one, one_mul] at this

中文:
定理 _root_.矩阵.是单位.posDef_star_left_conjugate_iff
  条件: (hU : 是单位 U)
  证明: by
refine ⟨fun h => ?_, fun h => h.conjTranspose_mul_mul_same mulVec_injective_of_isUnit hU⟩
  lift U to (Matrix n n R)ˣ using hU
  have := h.conjTranspose_mul_mul_same (mulVec_injective_of_isUnit (Units.isUnit U⁻¹))
  rwa [← star_eq_conjTranspose, ← mul_assoc, ← mul_assoc, ← star_mul, mul_assoc,
    Units.mul_inv, mul_one, star_one, one_mul] at this

Depends on / 依赖: Matrix, Units.isUnit, Units.mul_inv, conjTranspose_mul_mul_same, h.conjTranspose_mul_mul_same, isUnit, mulVec_injective_of_isUnit, mul_assoc, mul_inv, mul_one, one_mul, star_eq_conjTranspose, star_mul, star_one
-/
theorem _root_.Matrix.IsUnit.posDef_star_left_conjugate_iff (hU : IsUnit U) :
    PosDef (star U * x * U) ↔ x.PosDef := by
refine ⟨fun h => ?_, fun h => h.conjTranspose_mul_mul_same mulVec_injective_of_isUnit hU⟩
  lift U to (Matrix n n R)ˣ using hU
  have := h.conjTranspose_mul_mul_same (mulVec_injective_of_isUnit (Units.isUnit U⁻¹))
  rwa [← star_eq_conjTranspose, ← mul_assoc, ← mul_assoc, ← star_mul, mul_assoc,
    Units.mul_inv, mul_one, star_one, one_mul] at this

/--
theorem `_root_.Matrix.IsUnit.posDef_star_right_conjugate_iff` / 定理 `_root_.Matrix.IsUnit.posDef_star_right_conjugate_iff`

English:
theorem _root_.Matrix.IsUnit.posDef_star_right_conjugate_iff
  given: (hU : IsUnit U)
  proof: by
  simpa using hU.star.posDef_star_left_conjugate_iff

中文:
定理 _root_.矩阵.是单位.posDef_star_right_conjugate_iff
  条件: (hU : 是单位 U)
  证明: by
  simpa using hU.star.posDef_star_left_conjugate_iff

Depends on / 依赖: hU.star.posDef_star_left_conjugate_iff, posDef_star_left_conjugate_iff
-/
theorem _root_.Matrix.IsUnit.posDef_star_right_conjugate_iff (hU : IsUnit U) :
    PosDef (U * x * star U) ↔ x.PosDef := by
  simpa using hU.star.posDef_star_left_conjugate_iff

end conjugate

section SchurComplement

variable [StarOrderedRing R']

omit [Fintype n] in variable [Finite n] in
/--
theorem `fromBlocks₁₁` / 定理 `fromBlocks₁₁`

English:
theorem fromBlocks₁₁
  statement: [DecidableEq m] {A : Matrix m m R'}
  proof: by
  have := Fintype.ofFinite n
  rw [posSemidef_iff_dotProduct_mulVec]; rw [IsHermitian.fromBlocks₁₁ _ _ hA.1]
  constructor
  · refine fun h => .of_dotProduct_mulVec_nonneg h.1 fun x => ?_
    have := h.2 (-((A⁻¹ * B) *ᵥ x) oplusᵥ x)
    rwa [dotProduct_mulVec, schur_complement_eq₁₁ B D _ _ hA.1, neg_add_cancel, dotProduct_zero,
      zero_add, ← dotProduct_mulVec] at this
  · refine fun h => ⟨h.1, fun x => ?_⟩
    rw [dotProduct_mulVec]; rw [← Sum.elim_comp_inl_inr x]; rw [schur_complement_eq₁₁ B D _ _ hA.1]
    apply le_add_of_nonneg_of_le
    · rw [← dotProduct_mulVec]
      apply (posSemidef_iff_dotProduct_mulVec.mp hA.posSemidef).2
    · rw [← dotProduct_mulVec (star (x ∘ Sum.inr))]
      apply (posSemidef_iff_dotProduct_mulVec.mp h).2

omit [Fintype m] in variable [Finite m] in

中文:
定理 fromBlocks₁₁
  结论: [DecidableEq m] {A : 矩阵 m m R'}
  证明: by
  have := Fintype.ofFinite n
  rw [posSemidef_iff_dotProduct_mulVec]; rw [IsHermitian.fromBlocks₁₁ _ _ hA.1]
  constructor
  · refine fun h => .of_dotProduct_mulVec_nonneg h.1 fun x => ?_
    have := h.2 (-((A⁻¹ * B) *ᵥ x) oplusᵥ x)
    rwa [dotProduct_mulVec, schur_complement_eq₁₁ B D _ _ hA.1, neg_add_cancel, dotProduct_zero,
      zero_add, ← dotProduct_mulVec] at this
  · refine fun h => ⟨h.1, fun x => ?_⟩
    rw [dotProduct_mulVec]; rw [← Sum.elim_comp_inl_inr x]; rw [schur_complement_eq₁₁ B D _ _ hA.1]
    apply le_add_of_nonneg_of_le
    · rw [← dotProduct_mulVec]
      apply (posSemidef_iff_dotProduct_mulVec.mp hA.posSemidef).2
    · rw [← dotProduct_mulVec (star (x ∘ Sum.inr))]
      apply (posSemidef_iff_dotProduct_mulVec.mp h).2

omit [Fintype m] in variable [Finite m] in

Depends on / 依赖: Fintype, Fintype.ofFinite, IsHermitian, IsHermitian.fromBlocks, Sum.elim_comp_inl_inr, dotProduct_mulVec, dotProduct_zero, elim_comp_inl_inr, le_ad, neg_add_cancel, ofFinite, of_dotProduct_mulVec_nonneg, posSemidef_iff_dotProduct_mulVec, zero_add
-/
theorem fromBlocks₁₁ [DecidableEq m] {A : Matrix m m R'}
    (B : Matrix m n R') (D : Matrix n n R') (hA : A.PosDef) [Invertible A] :
    (fromBlocks A B Bᴴ D).PosSemidef ↔ (D - Bᴴ * A⁻¹ * B).PosSemidef := by
  have := Fintype.ofFinite n
  rw [posSemidef_iff_dotProduct_mulVec]; rw [IsHermitian.fromBlocks₁₁ _ _ hA.1]
  constructor
  · refine fun h => .of_dotProduct_mulVec_nonneg h.1 fun x => ?_
    have := h.2 (-((A⁻¹ * B) *ᵥ x) oplusᵥ x)
    rwa [dotProduct_mulVec, schur_complement_eq₁₁ B D _ _ hA.1, neg_add_cancel, dotProduct_zero,
      zero_add, ← dotProduct_mulVec] at this
  · refine fun h => ⟨h.1, fun x => ?_⟩
    rw [dotProduct_mulVec]; rw [← Sum.elim_comp_inl_inr x]; rw [schur_complement_eq₁₁ B D _ _ hA.1]
    apply le_add_of_nonneg_of_le
    · rw [← dotProduct_mulVec]
      apply (posSemidef_iff_dotProduct_mulVec.mp hA.posSemidef).2
    · rw [← dotProduct_mulVec (star (x ∘ Sum.inr))]
      apply (posSemidef_iff_dotProduct_mulVec.mp h).2

omit [Fintype m] in variable [Finite m] in
/--
theorem `fromBlocks₂₂` / 定理 `fromBlocks₂₂`

English:
theorem fromBlocks₂₂
  statement: [DecidableEq n] (A : Matrix m m R')
  proof: by
  rw [← posSemidef_submatrix_equiv (Equiv.sumComm n m)]; rw [Equiv.sumComm_apply]; rw [fromBlocks_submatrix_sum_swap_sum_swap]
  convert! fromBlocks₁₁ Bᴴ A hD <;> simp

中文:
定理 fromBlocks₂₂
  结论: [DecidableEq n] (A : 矩阵 m m R')
  证明: by
  rw [← posSemidef_submatrix_equiv (Equiv.sumComm n m)]; rw [Equiv.sumComm_apply]; rw [fromBlocks_submatrix_sum_swap_sum_swap]
  convert! fromBlocks₁₁ Bᴴ A hD <;> simp

Depends on / 依赖: Equiv.sumComm, Equiv.sumComm_apply, convert, fromBlocks_submatrix_sum_swap_sum_swap, posSemidef_submatrix_equiv, sumComm, sumComm_apply
-/
theorem fromBlocks₂₂ [DecidableEq n] (A : Matrix m m R')
    (B : Matrix m n R') {D : Matrix n n R'} (hD : D.PosDef) [Invertible D] :
    (fromBlocks A B Bᴴ D).PosSemidef ↔ (A - B * D⁻¹ * Bᴴ).PosSemidef := by
  rw [← posSemidef_submatrix_equiv (Equiv.sumComm n m)]; rw [Equiv.sumComm_apply]; rw [fromBlocks_submatrix_sum_swap_sum_swap]
  convert! fromBlocks₁₁ Bᴴ A hD <;> simp

end SchurComplement

end PosDef

end Matrix

namespace QuadraticForm


variable {n : Type*} [Fintype n]

/--
theorem `posDef_of_toMatrix'` / 定理 `posDef_of_toMatrix'`

English:
theorem posDef_of_toMatrix'
  statement: [DecidableEq n] {Q : QuadraticForm Real (n -> Real)}
  proof: by
  rw [← Q.toQuadraticMap_associated Real]; rw [← (LinearMap.toMatrix₂' Real).left_inv (Q.associatedHom Real)]
  exact hQ.toQuadraticForm'

中文:
定理 posDef_of_toMatrix'
  结论: [DecidableEq n] {Q : QuadraticForm 实数 (n -> 实数)}
  证明: by
  rw [← Q.toQuadraticMap_associated Real]; rw [← (LinearMap.toMatrix₂' Real).left_inv (Q.associatedHom Real)]
  exact hQ.toQuadraticForm'

Depends on / 依赖: LinearMap, LinearMap.toMatrix, Q.associatedHom, Q.toQuadraticMap_associated, associatedHom, hQ.toQuadraticForm, left_inv, toQuadraticForm, toQuadraticMap_associated
-/
theorem posDef_of_toMatrix' [DecidableEq n] {Q : QuadraticForm Real (n -> Real)}
    (hQ : Q.toMatrix'.PosDef) : Q.PosDef := by
  rw [← Q.toQuadraticMap_associated Real]; rw [← (LinearMap.toMatrix₂' Real).left_inv (Q.associatedHom Real)]
  exact hQ.toQuadraticForm'

/--
theorem `posDef_toMatrix'` / 定理 `posDef_toMatrix'`

English:
theorem posDef_toMatrix'
  given: [DecidableEq n] {Q : QuadraticForm Real (n -> Real)} (hQ : Q.PosDef)
  proof: by
  rw [← Q.toQuadraticMap_associated Real]; rw [← (LinearMap.toMatrix₂' Real).left_inv (Q.associatedHom Real)] at hQ
  exact .of_toQuadraticForm' (isSymm_toMatrix' Q) hQ

中文:
定理 posDef_toMatrix'
  条件: [DecidableEq n] {Q : QuadraticForm 实数 (n -> 实数)} (hQ : Q.PosDef)
  证明: by
  rw [← Q.toQuadraticMap_associated Real]; rw [← (LinearMap.toMatrix₂' Real).left_inv (Q.associatedHom Real)] at hQ
  exact .of_toQuadraticForm' (isSymm_toMatrix' Q) hQ

Depends on / 依赖: LinearMap, LinearMap.toMatrix, Q.associatedHom, Q.toQuadraticMap_associated, associatedHom, isSymm_toMatrix, left_inv, of_toQuadraticForm, toQuadraticMap_associated
-/
theorem posDef_toMatrix' [DecidableEq n] {Q : QuadraticForm Real (n -> Real)} (hQ : Q.PosDef) :
    Q.toMatrix'.PosDef := by
  rw [← Q.toQuadraticMap_associated Real]; rw [← (LinearMap.toMatrix₂' Real).left_inv (Q.associatedHom Real)] at hQ
  exact .of_toQuadraticForm' (isSymm_toMatrix' Q) hQ

end QuadraticForm
