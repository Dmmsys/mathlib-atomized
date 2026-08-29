/-
Copyright (c) 2021 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam
-/
module

public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Data.Matrix.Reflection
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The Unitary Group

This file defines elements of the unitary group `Matrix.unitaryGroup n α`, where `α` is a
`StarRing`. This consists of all `n` by `n` matrices with entries in `α` such that the
star-transpose is its inverse. In addition, we define the group structure on
`Matrix.unitaryGroup n α`, and the embedding into the general linear group
`LinearMap.GeneralLinearGroup α (n → α)`.

We also define the orthogonal group `Matrix.orthogonalGroup n R`, where `R` is a `CommRing`.

## Main Definitions

* `Matrix.unitaryGroup` is the submonoid of matrices where the star-transpose is the inverse; the
  group structure (under multiplication) is inherited from a more general `unitary` construction.
* `Matrix.UnitaryGroup.embeddingGL` is the embedding `Matrix.unitaryGroup n α → GLₙ(α)`, where
  `GLₙ(α)` is `LinearMap.GeneralLinearGroup α (n → α)`.
* `Matrix.orthogonalGroup` is the submonoid of matrices where the transpose is the inverse.

## References

* https://en.wikipedia.org/wiki/Unitary_group

## Tags

matrix group, group, unitary group, orthogonal group

-/

@[expose] public section


universe u v

namespace Matrix

open LinearMap Matrix

section

variable (n : Type u) [DecidableEq n] [Fintype n]
variable (α : Type v) [CommRing α] [StarRing α]

/--
Definition of `unitaryGroup` / `unitaryGroup` 的定义

English:
abbreviation unitaryGroup
  signature: : Submonoid (Matrix n n α)
  body: unitary (Matrix n n α)

中文:
缩写 unitaryGroup
  签名: : Submonoid (Matrix n n α)
  定义体: unitary (Matrix n n α)

Depends on / 依赖: Matrix, unitary
-/
abbrev unitaryGroup : Submonoid (Matrix n n α) :=
  unitary (Matrix n n α)

-- the group and star structure is already defined in another file
example : Group (unitaryGroup n α) := inferInstance
example : StarMul (unitaryGroup n α) := inferInstance

end

variable {n : Type u} [DecidableEq n] [Fintype n]
variable {α : Type v} [CommRing α] [StarRing α] {A : Matrix n n α}

/--
theorem `mem_unitaryGroup_iff` / 定理 `mem_unitaryGroup_iff`

English:
theorem mem_unitaryGroup_iff
  statement: A in Matrix.unitaryGroup n α ↔ A * star A = 1
  proof: by
  refine ⟨And.right, fun hA => ⟨?_, hA⟩⟩
  simpa only [mul_eq_one_comm] using hA

中文:
定理 mem_unitaryGroup_iff
  结论: A in Matrix.unitaryGroup n α ↔ A * star A = 1
  证明: by
  refine ⟨And.right, fun hA => ⟨?_, hA⟩⟩
  simpa only [mul_eq_one_comm] using hA

Depends on / 依赖: And.right, mul_eq_one_comm
-/
theorem mem_unitaryGroup_iff : A in Matrix.unitaryGroup n α ↔ A * star A = 1 := by
  refine ⟨And.right, fun hA => ⟨?_, hA⟩⟩
  simpa only [mul_eq_one_comm] using hA

/--
theorem `mem_unitaryGroup_iff'` / 定理 `mem_unitaryGroup_iff'`

English:
theorem mem_unitaryGroup_iff'
  statement: A in Matrix.unitaryGroup n α ↔ star A * A = 1
  proof: by
  refine ⟨And.left, fun hA => ⟨hA, ?_⟩⟩
  rwa [mul_eq_one_comm] at hA

中文:
定理 mem_unitaryGroup_iff'
  结论: A in Matrix.unitaryGroup n α ↔ star A * A = 1
  证明: by
  refine ⟨And.left, fun hA => ⟨hA, ?_⟩⟩
  rwa [mul_eq_one_comm] at hA

Depends on / 依赖: And.left, mul_eq_one_comm
-/
theorem mem_unitaryGroup_iff' : A in Matrix.unitaryGroup n α ↔ star A * A = 1 := by
  refine ⟨And.left, fun hA => ⟨hA, ?_⟩⟩
  rwa [mul_eq_one_comm] at hA

/--
theorem `det_of_mem_unitary` / 定理 `det_of_mem_unitary`

English:
theorem det_of_mem_unitary
  given: {A : Matrix n n α} (hA : A in Matrix.unitaryGroup n α)
  proof: by
  constructor
  · simpa [star, det_transpose] using congr_arg det hA.1
  · simpa [star, det_transpose] using congr_arg det hA.2

中文:
定理 det_of_mem_unitary
  条件: {A : Matrix n n α} (hA : A in Matrix.unitaryGroup n α)
  证明: by
  constructor
  · simpa [star, det_transpose] using congr_arg det hA.1
  · simpa [star, det_transpose] using congr_arg det hA.2

Depends on / 依赖: congr_arg, det_transpose
-/
theorem det_of_mem_unitary {A : Matrix n n α} (hA : A in Matrix.unitaryGroup n α) :
    A.det in unitary α := by
  constructor
  · simpa [star, det_transpose] using congr_arg det hA.1
  · simpa [star, det_transpose] using congr_arg det hA.2

open scoped Kronecker in
/--
theorem `kronecker_mem_unitary` / 定理 `kronecker_mem_unitary`

English:
theorem kronecker_mem_unitary
  statement: {R m : Type*} [Semiring R] [StarRing R] [Fintype m]
  proof: by
  simp_rw [Unitary.mem_iff, star_eq_conjTranspose, conjTranspose_kronecker']
  constructor <;> ext <;> simp only [mul_apply, submatrix_apply, kroneckerMap_apply, Prod.fst_swap,
    conjTranspose_apply, ← star_apply, Prod.snd_swap, ← mul_assoc]
  · simp_rw [mul_assoc _ (star U₁ _ _), ← Finset.univ

中文:
定理 kronecker_mem_unitary
  结论: {R m : 类型} [Semiring R] [StarRing R] [Fintype m]
  证明: by
  simp_rw [Unitary.mem_iff, star_eq_conjTranspose, conjTranspose_kronecker']
  constructor <;> ext <;> simp only [mul_apply, submatrix_apply, kroneckerMap_apply, Prod.fst_swap,
    conjTranspose_apply, ← star_apply, Prod.snd_swap, ← mul_assoc]
  · simp_rw [mul_assoc _ (star U₁ _ _), ← Finset.univ

Depends on / 依赖: Finset, Finset.mul_sum, Finset.sum_comm, Finset.sum_ite_irrel, Finset.sum_mul, Finset.sum_product, Finset.univ_product_univ, Matrix, Matrix.mul, Matrix.mul_apply, Matrix.one_apply, Prod.fst_swap, Prod.snd_swap, Unitary, Unitary.mem_iff, conjTranspose_apply, conjTranspose_kronecker, fst_swap, ite_mul, kroneckerMap_apply
-/
theorem kronecker_mem_unitary {R m : Type*} [Semiring R] [StarRing R] [Fintype m]
    [DecidableEq m] {U₁ : Matrix n n R} {U₂ : Matrix m m R}
    (hU₁ : U₁ in unitary (Matrix n n R)) (hU₂ : U₂ in unitary (Matrix m m R)) :
    U₁ otimesₖ U₂ in unitary (Matrix (n × m) (n × m) R) := by
  simp_rw [Unitary.mem_iff, star_eq_conjTranspose, conjTranspose_kronecker']
  constructor <;> ext <;> simp only [mul_apply, submatrix_apply, kroneckerMap_apply, Prod.fst_swap,
    conjTranspose_apply, ← star_apply, Prod.snd_swap, ← mul_assoc]
  · simp_rw [mul_assoc _ (star U₁ _ _), ← Finset.univ_product_univ, Finset.sum_product]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, ← Finset.mul_sum, ← Matrix.mul_apply, hU₁.1, Matrix.one_apply,
      mul_boole, ite_mul, zero_mul, Finset.sum_ite_irrel, ← Matrix.mul_apply, hU₂.1,
      Matrix.one_apply, Finset.sum_const_zero, ← ite_and, Prod.eq_iff_fst_eq_snd_eq]
  · simp_rw [mul_assoc _ _ (star U₂ _ _), ← Finset.univ_product_univ, Finset.sum_product,
      ← Finset.sum_mul, ← Finset.mul_sum, ← Matrix.mul_apply, hU₂.2, Matrix.one_apply, mul_boole,
      ite_mul, zero_mul, Finset.sum_ite_irrel, ← Matrix.mul_apply, hU₁.2, Matrix.one_apply,
      Finset.sum_const_zero, ← ite_and, and_comm, Prod.eq_iff_fst_eq_snd_eq]

section TensorProduct
variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
  [StarRing A] [StarRing B] [StarRing R] [StarModule R A] [StarModule R B]

open scoped TensorProduct Kronecker

/--
theorem `_root_.Unitary.tmul_mem` / 定理 `_root_.Unitary.tmul_mem`

English:
theorem _root_.Unitary.tmul_mem
  given: {U : A} {V : B} (hU : U in unitary A) (hV : V in unitary B)
  proof: by
  simp [Unitary.mem_iff, hU, hV, Algebra.TensorProduct.one_def]

中文:
定理 _root_.Unitary.tmul_mem
  条件: {U : A} {V : B} (hU : U in unitary A) (hV : V in unitary B)
  证明: by
  simp [Unitary.mem_iff, hU, hV, Algebra.TensorProduct.one_def]

Depends on / 依赖: Algebra, Algebra.TensorProduct.one_def, TensorProduct, Unitary, Unitary.mem_iff, mem_iff, one_def
-/
theorem _root_.Unitary.tmul_mem {U : A} {V : B} (hU : U in unitary A) (hV : V in unitary B) :
    U otimesₜ[R] V in unitary (A otimes[R] B) := by
  simp [Unitary.mem_iff, hU, hV, Algebra.TensorProduct.one_def]

/--
theorem `kroneckerTMul_mem_unitary` / 定理 `kroneckerTMul_mem_unitary`

English:
theorem kroneckerTMul_mem_unitary
  statement: {m : Type*} [Fintype m] [DecidableEq m] {U : Matrix m m A}
  proof: by
  simp_rw [Unitary.mem_iff, star_eq_conjTranspose] at hU hV ⊢
  simp [conjTranspose_kroneckerTMul, ← mul_kroneckerTMul_mul, hU, hV]

中文:
定理 kroneckerTMul_mem_unitary
  结论: {m : 类型} [Fintype m] [DecidableEq m] {U : Matrix m m A}
  证明: by
  simp_rw [Unitary.mem_iff, star_eq_conjTranspose] at hU hV ⊢
  simp [conjTranspose_kroneckerTMul, ← mul_kroneckerTMul_mul, hU, hV]

Depends on / 依赖: Unitary, Unitary.mem_iff, conjTranspose_kroneckerTMul, mem_iff, mul_kroneckerTMul_mul, simp_rw, star_eq_conjTranspose
-/
theorem kroneckerTMul_mem_unitary {m : Type*} [Fintype m] [DecidableEq m] {U : Matrix m m A}
    {V : Matrix n n B} (hU : U in unitary (Matrix m m A)) (hV : V in unitary (Matrix n n B)) :
    U otimesₖₜ[R] V in unitary (Matrix (m × n) (m × n) (A otimes[R] B)) := by
  simp_rw [Unitary.mem_iff, star_eq_conjTranspose] at hU hV ⊢
  simp [conjTranspose_kroneckerTMul, ← mul_kroneckerTMul_mul, hU, hV]

end TensorProduct

namespace UnitaryGroup

/--
Instance `coeMatrix` / 实例 `coeMatrix`

English:
instance coeMatrix
  signature: : Coe (unitaryGroup n α) (Matrix n n α)
  body: ⟨Subtype.val⟩

中文:
实例 coeMatrix
  签名: : Coe (unitaryGroup n α) (Matrix n n α)
  定义体: ⟨Subtype.val⟩

Depends on / 依赖: Subtype, Subtype.val
-/
instance coeMatrix : Coe (unitaryGroup n α) (Matrix n n α) :=
  ⟨Subtype.val⟩

/--
Instance `coeFun` / 实例 `coeFun`

English:
instance coeFun
  signature: : CoeFun (unitaryGroup n α) fun _ => n -> n -> α where coe A
  body: A.val

中文:
实例 coeFun
  签名: : CoeFun (unitaryGroup n α) fun _ => n -> n -> α where coe A
  定义体: A.val

Depends on / 依赖: A.val
-/
instance coeFun : CoeFun (unitaryGroup n α) fun _ => n -> n -> α where coe A := A.val

/--
Definition of `toLin'` / `toLin'` 的定义

English:
definition toLin'
  signature: (A : unitaryGroup n α)
  body: Matrix.toLin' A.1

中文:
定义 toLin'
  签名: (A : unitaryGroup n α)
  定义体: Matrix.toLin' A.1

Depends on / 依赖: Matrix, Matrix.toLin
-/
def toLin' (A : unitaryGroup n α) :=
  Matrix.toLin' A.1

/--
theorem `ext_iff` / 定理 `ext_iff`

English:
theorem ext_iff
  given: (A B : unitaryGroup n α)
  statement: A = B ↔ forall i j, A i j = B i j
  proof: Subtype.ext_iff.trans ⟨fun h i j => congr_fun (congr_fun h i) j, Matrix.ext⟩

@[ext]

中文:
定理 ext_iff
  条件: (A B : unitaryGroup n α)
  结论: A = B ↔ 对任意 i j, A i j = B i j
  证明: Subtype.ext_iff.trans ⟨fun h i j => congr_fun (congr_fun h i) j, Matrix.ext⟩

@[ext]

Depends on / 依赖: Matrix, Matrix.ext, Subtype, Subtype.ext_iff.trans, congr_fun, ext_iff
-/
theorem ext_iff (A B : unitaryGroup n α) : A = B ↔ forall i j, A i j = B i j :=
  Subtype.ext_iff.trans ⟨fun h i j => congr_fun (congr_fun h i) j, Matrix.ext⟩

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: (A B : unitaryGroup n α)
  statement: (forall i j, A i j = B i j) -> A = B
  proof: (UnitaryGroup.ext_iff A B).mpr

中文:
定理 ext
  条件: (A B : unitaryGroup n α)
  结论: (对任意 i j, A i j = B i j) -> A = B
  证明: (UnitaryGroup.ext_iff A B).mpr

Depends on / 依赖: UnitaryGroup, UnitaryGroup.ext_iff, ext_iff
-/
theorem ext (A B : unitaryGroup n α) : (forall i j, A i j = B i j) -> A = B :=
  (UnitaryGroup.ext_iff A B).mpr

/--
theorem `star_mul_self` / 定理 `star_mul_self`

English:
theorem star_mul_self
  given: (A : unitaryGroup n α)
  statement: star A.1 * A.1 = 1
  proof: A.2.1

@[simp]

中文:
定理 star_mul_self
  条件: (A : unitaryGroup n α)
  结论: star A.1 * A.1 = 1
  证明: A.2.1

@[simp]
-/
theorem star_mul_self (A : unitaryGroup n α) : star A.1 * A.1 = 1 :=
  A.2.1

@[simp]
/--
theorem `det_isUnit` / 定理 `det_isUnit`

English:
theorem det_isUnit
  given: (A : unitaryGroup n α)
  statement: IsUnit (A : Matrix n n α).det
  proof: .mp (Unitary.toUnits A).isUnit isUnit_iff_isUnit_det _

中文:
定理 det_isUnit
  条件: (A : unitaryGroup n α)
  结论: IsUnit (A : Matrix n n α).det
  证明: .mp (Unitary.toUnits A).isUnit isUnit_iff_isUnit_det _

Depends on / 依赖: Unitary, Unitary.toUnits, isUnit, isUnit_iff_isUnit_det, toUnits
-/
theorem det_isUnit (A : unitaryGroup n α) : IsUnit (A : Matrix n n α).det :=
.mp (Unitary.toUnits A).isUnit isUnit_iff_isUnit_det _

section CoeLemmas

variable (A B : unitaryGroup n α)

/--
theorem `inv_val` / 定理 `inv_val`

English:
theorem inv_val
  statement: ↑A⁻¹ = (star A : Matrix n n α)
  proof: rfl

中文:
定理 inv_val
  结论: ↑A⁻¹ = (star A : Matrix n n α)
  证明: rfl
-/
@[simp] theorem inv_val : ↑A⁻¹ = (star A : Matrix n n α) := rfl

/--
theorem `inv_apply` / 定理 `inv_apply`

English:
theorem inv_apply
  statement: ⇑A⁻¹ = (star A : Matrix n n α)
  proof: rfl

中文:
定理 inv_apply
  结论: ⇑A⁻¹ = (star A : Matrix n n α)
  证明: rfl
-/
@[simp] theorem inv_apply : ⇑A⁻¹ = (star A : Matrix n n α) := rfl

/--
theorem `mul_val` / 定理 `mul_val`

English:
theorem mul_val
  statement: ↑(A * B) = A.1 * B.1
  proof: rfl

中文:
定理 mul_val
  结论: ↑(A * B) = A.1 * B.1
  证明: rfl
-/
@[simp] theorem mul_val : ↑(A * B) = A.1 * B.1 := rfl

/--
theorem `mul_apply` / 定理 `mul_apply`

English:
theorem mul_apply
  statement: ⇑(A * B) = A.1 * B.1
  proof: rfl

中文:
定理 mul_apply
  结论: ⇑(A * B) = A.1 * B.1
  证明: rfl
-/
@[simp] theorem mul_apply : ⇑(A * B) = A.1 * B.1 := rfl

/--
theorem `one_val` / 定理 `one_val`

English:
theorem one_val
  statement: ↑(1 : unitaryGroup n α) = (1 : Matrix n n α)
  proof: rfl

中文:
定理 one_val
  结论: ↑(1 : unitaryGroup n α) = (1 : Matrix n n α)
  证明: rfl
-/
@[simp] theorem one_val : ↑(1 : unitaryGroup n α) = (1 : Matrix n n α) := rfl

/--
theorem `one_apply` / 定理 `one_apply`

English:
theorem one_apply
  statement: ⇑(1 : unitaryGroup n α) = (1 : Matrix n n α)
  proof: rfl

@[simp]

中文:
定理 one_apply
  结论: ⇑(1 : unitaryGroup n α) = (1 : Matrix n n α)
  证明: rfl

@[simp]
-/
@[simp] theorem one_apply : ⇑(1 : unitaryGroup n α) = (1 : Matrix n n α) := rfl

@[simp]
/--
theorem `toLin'_mul` / 定理 `toLin'_mul`

English:
theorem toLin'_mul
  statement: toLin' (A * B) = (toLin' A).comp (toLin' B)
  proof: Matrix.toLin'_mul A.1 B.1

@[simp]

中文:
定理 toLin'_mul
  结论: toLin' (A * B) = (toLin' A).comp (toLin' B)
  证明: Matrix.toLin'_mul A.1 B.1

@[simp]
-/
theorem toLin'_mul : toLin' (A * B) = (toLin' A).comp (toLin' B) :=
  Matrix.toLin'_mul A.1 B.1

@[simp]
/--
theorem `toLin'_one` / 定理 `toLin'_one`

English:
theorem toLin'_one
  statement: toLin' (1 : unitaryGroup n α) = LinearMap.id
  proof: Matrix.toLin'_one

中文:
定理 toLin'_one
  结论: toLin' (1 : unitaryGroup n α) = LinearMap.id
  证明: Matrix.toLin'_one
-/
theorem toLin'_one : toLin' (1 : unitaryGroup n α) = LinearMap.id :=
  Matrix.toLin'_one

end CoeLemmas

-- TODO: redefine `toGL`/`embeddingGL` as in the following example,
-- so that we can get `toLinearEquiv` from `GeneralLinearGroup.toLinearEquiv`
example : unitaryGroup n α ->* GeneralLinearGroup α (n -> α) :=
  .toHomUnits ⟨⟨toLin', toLin'_one⟩, toLin'_mul⟩

/--
Definition of `toLinearEquiv` / `toLinearEquiv` 的定义

English:
definition toLinearEquiv
  signature: (A : unitaryGroup n α)
  body: { Matrix.toLin' A.1 with
    invFun := toLin' A⁻¹
    left_inv := fun x =>
      calc
        (toLin' A⁻¹).comp (toLin' A) x = (toLin' (A⁻¹ * A)) x := by rw [← toLin'_mul]
        _ = x := by rw [inv_mul_cancel, toLin'_one, id_apply]
    right_inv := fun x =>
      calc
        (toLin' A).comp (toLi

中文:
定义 toLinearEquiv
  签名: (A : unitaryGroup n α)
  定义体: { Matrix.toLin' A.1 with
    invFun := toLin' A⁻¹
    left_inv := fun x =>
      calc
        (toLin' A⁻¹).comp (toLin' A) x = (toLin' (A⁻¹ * A)) x := by rw [← toLin'_mul]
        _ = x := by rw [inv_mul_cancel, toLin'_one, id_apply]
    right_inv := fun x =>
      calc
        (toLin' A).comp (toLi

Depends on / 依赖: Matrix, Matrix.toLin, _mul, _one, id_apply, invFun, inv_mul_cancel, left_inv, mul_inv_cancel, right_inv
-/
def toLinearEquiv (A : unitaryGroup n α) : (n -> α) ≃ₗ[α] n -> α :=
  { Matrix.toLin' A.1 with
    invFun := toLin' A⁻¹
    left_inv := fun x =>
      calc
        (toLin' A⁻¹).comp (toLin' A) x = (toLin' (A⁻¹ * A)) x := by rw [← toLin'_mul]
        _ = x := by rw [inv_mul_cancel, toLin'_one, id_apply]
    right_inv := fun x =>
      calc
        (toLin' A).comp (toLin' A⁻¹) x = toLin' (A * A⁻¹) x := by rw [← toLin'_mul]
        _ = x := by rw [mul_inv_cancel, toLin'_one, id_apply] }

/--
Definition of `toGL` / `toGL` 的定义

English:
definition toGL
  signature: (A : unitaryGroup n α)
  body: GeneralLinearGroup.ofLinearEquiv (toLinearEquiv A)

中文:
定义 toGL
  签名: (A : unitaryGroup n α)
  定义体: GeneralLinearGroup.ofLinearEquiv (toLinearEquiv A)

Depends on / 依赖: GeneralLinearGroup, GeneralLinearGroup.ofLinearEquiv, ofLinearEquiv, toLinearEquiv
-/
def toGL (A : unitaryGroup n α) : GeneralLinearGroup α (n -> α) :=
  GeneralLinearGroup.ofLinearEquiv (toLinearEquiv A)

/--
theorem `coe_toGL` / 定理 `coe_toGL`

English:
theorem coe_toGL
  given: (A : unitaryGroup n α)
  statement: (toGL A).1 = toLin' A
  proof: rfl

@[simp]

中文:
定理 coe_toGL
  条件: (A : unitaryGroup n α)
  结论: (toGL A).1 = toLin' A
  证明: rfl

@[simp]
-/
theorem coe_toGL (A : unitaryGroup n α) : (toGL A).1 = toLin' A := rfl

@[simp]
/--
theorem `toGL_one` / 定理 `toGL_one`

English:
theorem toGL_one
  statement: toGL (1 : unitaryGroup n α) = 1
  proof: Units.ext by
  simp only [coe_toGL, toLin'_one]
  rfl

@[simp]

中文:
定理 toGL_one
  结论: toGL (1 : unitaryGroup n α) = 1
  证明: Units.ext by
  simp only [coe_toGL, toLin'_one]
  rfl

@[simp]

Depends on / 依赖: Units.ext, _one, coe_toGL
-/
theorem toGL_one : toGL (1 : unitaryGroup n α) = 1 := Units.ext by
  simp only [coe_toGL, toLin'_one]
  rfl

@[simp]
/--
theorem `toGL_mul` / 定理 `toGL_mul`

English:
theorem toGL_mul
  given: (A B : unitaryGroup n α)
  statement: toGL (A * B) = toGL A * toGL B
  proof: Units.ext by
  simp only [coe_toGL, toLin'_mul]
  rfl

中文:
定理 toGL_mul
  条件: (A B : unitaryGroup n α)
  结论: toGL (A * B) = toGL A * toGL B
  证明: Units.ext by
  simp only [coe_toGL, toLin'_mul]
  rfl

Depends on / 依赖: Units.ext, _mul, coe_toGL
-/
theorem toGL_mul (A B : unitaryGroup n α) : toGL (A * B) = toGL A * toGL B := Units.ext by
  simp only [coe_toGL, toLin'_mul]
  rfl

/--
Definition of `embeddingGL` / `embeddingGL` 的定义

English:
definition embeddingGL
  signature: : unitaryGroup n α ->* GeneralLinearGroup α (n -> α)
  body: ⟨⟨fun A => toGL A, toGL_one⟩, toGL_mul⟩

中文:
定义 embeddingGL
  签名: : unitaryGroup n α ->* GeneralLinearGroup α (n -> α)
  定义体: ⟨⟨fun A => toGL A, toGL_one⟩, toGL_mul⟩

Depends on / 依赖: toGL_mul, toGL_one
-/
def embeddingGL : unitaryGroup n α ->* GeneralLinearGroup α (n -> α) :=
  ⟨⟨fun A => toGL A, toGL_one⟩, toGL_mul⟩

/--
theorem `_root_.Matrix.transpose_mem_unitaryGroup_iff` / 定理 `_root_.Matrix.transpose_mem_unitaryGroup_iff`

English:
theorem _root_.Matrix.transpose_mem_unitaryGroup_iff
  given: {U : Matrix n n α}
  proof: by
  conv_rhs => rw [mem_unitaryGroup_iff']
  rw [mem_unitaryGroup_iff]; rw [show star Uᵀ = (star U)ᵀ by rfl]; rw [← transpose_mul]; rw [← transpose_inj]
  simp

中文:
定理 _root_.Matrix.transpose_mem_unitaryGroup_iff
  条件: {U : Matrix n n α}
  证明: by
  conv_rhs => rw [mem_unitaryGroup_iff']
  rw [mem_unitaryGroup_iff]; rw [show star Uᵀ = (star U)ᵀ by rfl]; rw [← transpose_mul]; rw [← transpose_inj]
  simp

Depends on / 依赖: conv_rhs, mem_unitaryGroup_iff, transpose_inj, transpose_mul
-/
theorem _root_.Matrix.transpose_mem_unitaryGroup_iff {U : Matrix n n α} :
    Uᵀ in unitaryGroup n α ↔ U in unitaryGroup n α := by
  conv_rhs => rw [mem_unitaryGroup_iff']
  rw [mem_unitaryGroup_iff]; rw [show star Uᵀ = (star U)ᵀ by rfl]; rw [← transpose_mul]; rw [← transpose_inj]
  simp

/--
theorem `_root_.Matrix.map_star_mem_unitaryGroup_iff` / 定理 `_root_.Matrix.map_star_mem_unitaryGroup_iff`

English:
theorem _root_.Matrix.map_star_mem_unitaryGroup_iff
  given: {U : Matrix n n α}
  proof: by
  simp [← conjTranspose_transpose, transpose_mem_unitaryGroup_iff, ← star_eq_conjTranspose]

中文:
定理 _root_.Matrix.map_star_mem_unitaryGroup_iff
  条件: {U : Matrix n n α}
  证明: by
  simp [← conjTranspose_transpose, transpose_mem_unitaryGroup_iff, ← star_eq_conjTranspose]

Depends on / 依赖: conjTranspose_transpose, star_eq_conjTranspose, transpose_mem_unitaryGroup_iff
-/
theorem _root_.Matrix.map_star_mem_unitaryGroup_iff {U : Matrix n n α} :
    U.map star in unitaryGroup n α ↔ U in unitaryGroup n α := by
  simp [← conjTranspose_transpose, transpose_mem_unitaryGroup_iff, ← star_eq_conjTranspose]

/--
Definition of `transpose` / `transpose` 的定义

English:
definition transpose
  signature: (U : unitaryGroup n α)
  body: ⟨Uᵀ, transpose_mem_unitaryGroup_iff.mpr (SetLike.coe_mem _)⟩

中文:
定义 transpose
  签名: (U : unitaryGroup n α)
  定义体: ⟨Uᵀ, transpose_mem_unitaryGroup_iff.mpr (SetLike.coe_mem _)⟩
-/
@[simps] def transpose (U : unitaryGroup n α) : unitaryGroup n α :=
  ⟨Uᵀ, transpose_mem_unitaryGroup_iff.mpr (SetLike.coe_mem _)⟩

/--
Definition of `map_star` / `map_star` 的定义

English:
definition map_star
  signature: (U : unitaryGroup n α)
  body: ⟨(U : Matrix n n α).map star, map_star_mem_unitaryGroup_iff.mpr (SetLike.coe_mem _)⟩

中文:
定义 map_star
  签名: (U : unitaryGroup n α)
  定义体: ⟨(U : Matrix n n α).map star, map_star_mem_unitaryGroup_iff.mpr (SetLike.coe_mem _)⟩
-/
@[simps] def map_star (U : unitaryGroup n α) : unitaryGroup n α :=
  ⟨(U : Matrix n n α).map star, map_star_mem_unitaryGroup_iff.mpr (SetLike.coe_mem _)⟩

/--
theorem `map_star_inv_eq_transpose` / 定理 `map_star_inv_eq_transpose`

English:
theorem map_star_inv_eq_transpose
  given: (U : unitaryGroup n α)
  proof: by ext; simp

中文:
定理 map_star_inv_eq_transpose
  条件: (U : unitaryGroup n α)
  证明: by ext; simp
-/
theorem map_star_inv_eq_transpose (U : unitaryGroup n α) :
    (map_star U)⁻¹ = UnitaryGroup.transpose U := by ext; simp

/--
theorem `transpose_inv_eq_map_star` / 定理 `transpose_inv_eq_map_star`

English:
theorem transpose_inv_eq_map_star
  given: (U : unitaryGroup n α)
  proof: by
  simp [← map_star_inv_eq_transpose]

中文:
定理 transpose_inv_eq_map_star
  条件: (U : unitaryGroup n α)
  证明: by
  simp [← map_star_inv_eq_transpose]

Depends on / 依赖: map_star_inv_eq_transpose
-/
theorem transpose_inv_eq_map_star (U : unitaryGroup n α) :
    (UnitaryGroup.transpose U)⁻¹ = map_star U := by
  simp [← map_star_inv_eq_transpose]

end UnitaryGroup

section specialUnitaryGroup

variable (n) (α)

/--
Definition of `specialUnitaryGroup` / `specialUnitaryGroup` 的定义

English:
definition specialUnitaryGroup
  signature: : Submonoid (Matrix n n α)
  body: unitaryGroup n α ⊓ MonoidHom.mker detMonoidHom

中文:
定义 specialUnitaryGroup
  签名: : Submonoid (Matrix n n α)
  定义体: unitaryGroup n α ⊓ MonoidHom.mker detMonoidHom

Depends on / 依赖: MonoidHom, MonoidHom.mker, detMonoidHom, unitaryGroup
-/
def specialUnitaryGroup : Submonoid (Matrix n n α) := unitaryGroup n α ⊓ MonoidHom.mker detMonoidHom

variable {n} {α}

/--
theorem `specialUnitaryGroup_le_unitaryGroup` / 定理 `specialUnitaryGroup_le_unitaryGroup`

English:
theorem specialUnitaryGroup_le_unitaryGroup
  statement: specialUnitaryGroup n α <= unitaryGroup n α
  proof: inf_le_left

中文:
定理 specialUnitaryGroup_le_unitaryGroup
  结论: specialUnitaryGroup n α <= unitaryGroup n α
  证明: inf_le_left

Depends on / 依赖: inf_le_left
-/
theorem specialUnitaryGroup_le_unitaryGroup : specialUnitaryGroup n α <= unitaryGroup n α :=
  inf_le_left

/--
theorem `mem_specialUnitaryGroup_iff` / 定理 `mem_specialUnitaryGroup_iff`

English:
theorem mem_specialUnitaryGroup_iff
  proof: Iff.rfl

中文:
定理 mem_specialUnitaryGroup_iff
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_specialUnitaryGroup_iff :
    A in specialUnitaryGroup n α ↔ A in unitaryGroup n α ∧ A.det = 1 :=
  Iff.rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: StarMul (specialUnitaryGroup n α)
  body: ⟨star A, by simpa using A.prop.1, by have := A.prop.2; simp_all [star_eq_conjTranspose]⟩
star_mul A B := Subtype.ext star_mul A.1 B.1
star_involutive A := Subtype.ext star_involutive A.1

@[simp, norm_cast]

中文:
实例 :
  签名: StarMul (specialUnitaryGroup n α)
  定义体: ⟨star A, by simpa using A.prop.1, by have := A.prop.2; simp_all [star_eq_conjTranspose]⟩
star_mul A B := Subtype.ext star_mul A.1 B.1
star_involutive A := Subtype.ext star_involutive A.1

@[simp, norm_cast]

Depends on / 依赖: A.prop, star_eq_conjTranspose
-/
instance : StarMul (specialUnitaryGroup n α) where
  star A := ⟨star A, by simpa using A.prop.1, by have := A.prop.2; simp_all [star_eq_conjTranspose]⟩
star_mul A B := Subtype.ext star_mul A.1 B.1
star_involutive A := Subtype.ext star_involutive A.1

@[simp, norm_cast]
/--
theorem `specialUnitaryGroup.coe_star` / 定理 `specialUnitaryGroup.coe_star`

English:
theorem specialUnitaryGroup.coe_star
  given: (A : specialUnitaryGroup n α)
  statement: (star A).1 = star A.1
  proof: rfl

中文:
定理 specialUnitaryGroup.coe_star
  条件: (A : specialUnitaryGroup n α)
  结论: (star A).1 = star A.1
  证明: rfl
-/
theorem specialUnitaryGroup.coe_star (A : specialUnitaryGroup n α) : (star A).1 = star A.1 := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inv (specialUnitaryGroup n α)
  body: star

中文:
实例 :
  签名: Inv (specialUnitaryGroup n α)
  定义体: star
-/
instance : Inv (specialUnitaryGroup n α) where inv := star

/--
theorem `star_eq_inv` / 定理 `star_eq_inv`

English:
theorem star_eq_inv
  given: (A : specialUnitaryGroup n α)
  statement: star A = A⁻¹
  proof: rfl

中文:
定理 star_eq_inv
  条件: (A : specialUnitaryGroup n α)
  结论: star A = A⁻¹
  证明: rfl
-/
theorem star_eq_inv (A : specialUnitaryGroup n α) : star A = A⁻¹ :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Group (specialUnitaryGroup n α)
  body: Subtype.ext A.prop.1.1

中文:
实例 :
  签名: Group (specialUnitaryGroup n α)
  定义体: Subtype.ext A.prop.1.1

Depends on / 依赖: A.prop, Subtype, Subtype.ext
-/
instance : Group (specialUnitaryGroup n α) where
  inv_mul_cancel A := Subtype.ext A.prop.1.1

end specialUnitaryGroup

section OrthogonalGroup

variable (n) (R : Type v) [CommRing R]

-- TODO: will lemmas about `Matrix.orthogonalGroup` work without making
-- `starRingOfComm` a local instance? E.g., can we talk about unitary group and orthogonal group
-- at the same time?
attribute [local instance] starRingOfComm

/--
Definition of `orthogonalGroup` / `orthogonalGroup` 的定义

English:
abbreviation orthogonalGroup
  body: unitaryGroup n R

中文:
缩写 orthogonalGroup
  定义体: unitaryGroup n R

Depends on / 依赖: unitaryGroup
-/
abbrev orthogonalGroup := unitaryGroup n R

/--
theorem `mem_orthogonalGroup_iff` / 定理 `mem_orthogonalGroup_iff`

English:
theorem mem_orthogonalGroup_iff
  given: {A : Matrix n n R}
  proof: mem_unitaryGroup_iff

中文:
定理 mem_orthogonalGroup_iff
  条件: {A : Matrix n n R}
  证明: mem_unitaryGroup_iff

Depends on / 依赖: mem_unitaryGroup_iff
-/
theorem mem_orthogonalGroup_iff {A : Matrix n n R} :
    A in Matrix.orthogonalGroup n R ↔ A * Aᵀ = 1 :=
  mem_unitaryGroup_iff

/--
theorem `mem_orthogonalGroup_iff'` / 定理 `mem_orthogonalGroup_iff'`

English:
theorem mem_orthogonalGroup_iff'
  given: {A : Matrix n n R}
  proof: mem_unitaryGroup_iff'

中文:
定理 mem_orthogonalGroup_iff'
  条件: {A : Matrix n n R}
  证明: mem_unitaryGroup_iff'

Depends on / 依赖: mem_unitaryGroup_iff
-/
theorem mem_orthogonalGroup_iff' {A : Matrix n n R} :
    A in Matrix.orthogonalGroup n R ↔ Aᵀ * A = 1 :=
  mem_unitaryGroup_iff'

end OrthogonalGroup

section specialOrthogonalGroup

variable (n) (R : Type v) [CommRing R]

attribute [local instance] starRingOfComm

/--
Definition of `specialOrthogonalGroup` / `specialOrthogonalGroup` 的定义

English:
abbreviation specialOrthogonalGroup
  signature: : Submonoid (Matrix n n R)
  body: specialUnitaryGroup n R

中文:
缩写 specialOrthogonalGroup
  签名: : Submonoid (Matrix n n R)
  定义体: specialUnitaryGroup n R

Depends on / 依赖: specialUnitaryGroup
-/
abbrev specialOrthogonalGroup : Submonoid (Matrix n n R) := specialUnitaryGroup n R

variable {n} {R} {A : Matrix n n R}

-- the group and star structure is automatic from `specialUnitaryGroup`
example : Group (specialOrthogonalGroup n R) := inferInstance
example : StarMul (specialOrthogonalGroup n R) := inferInstance

/--
theorem `mem_specialOrthogonalGroup_iff` / 定理 `mem_specialOrthogonalGroup_iff`

English:
theorem mem_specialOrthogonalGroup_iff
  proof: Iff.rfl

中文:
定理 mem_specialOrthogonalGroup_iff
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_specialOrthogonalGroup_iff :
    A in specialOrthogonalGroup n R ↔ A in orthogonalGroup n R ∧ A.det = 1 :=
  Iff.rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `of_mem_specialOrthogonalGroup_fin_two_iff` / 引理 `of_mem_specialOrthogonalGroup_fin_two_iff`

English:
lemma of_mem_specialOrthogonalGroup_fin_two_iff
  given: {a b c d : R}
  proof: by
  trans ((a * a + b * b = 1 ∧ a * c + b * d = 0) ∧
    c * a + d * b = 0 ∧ c * c + d * d = 1) ∧ a * d - b * c = 1
  · simp [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff,
      ← Matrix.ext_iff, Fin.forall_fin_succ, Matrix.vecHead, Matrix.vecTail]
  grind

中文:
引理 of_mem_specialOrthogonalGroup_fin_two_iff
  条件: {a b c d : R}
  证明: by
  trans ((a * a + b * b = 1 ∧ a * c + b * d = 0) ∧
    c * a + d * b = 0 ∧ c * c + d * d = 1) ∧ a * d - b * c = 1
  · simp [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff,
      ← Matrix.ext_iff, Fin.forall_fin_succ, Matrix.vecHead, Matrix.vecTail]
  grind

Depends on / 依赖: Fin.forall_fin_succ, Matrix, Matrix.ext_iff, Matrix.mem_orthogonalGroup_iff, Matrix.mem_specialOrthogonalGroup_iff, Matrix.vecHead, Matrix.vecTail, ext_iff, forall_fin_succ, mem_orthogonalGroup_iff, mem_specialOrthogonalGroup_iff, vecHead, vecTail
-/
lemma of_mem_specialOrthogonalGroup_fin_two_iff {a b c d : R} :
    !![a, b; c, d] in Matrix.specialOrthogonalGroup (Fin 2) R ↔
      a = d ∧ b = -c ∧ a ^ 2 + b ^ 2 = 1 := by
  trans ((a * a + b * b = 1 ∧ a * c + b * d = 0) ∧
    c * a + d * b = 0 ∧ c * c + d * d = 1) ∧ a * d - b * c = 1
  · simp [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff,
      ← Matrix.ext_iff, Fin.forall_fin_succ, Matrix.vecHead, Matrix.vecTail]
  grind

/--
lemma `mem_specialOrthogonalGroup_fin_two_iff` / 引理 `mem_specialOrthogonalGroup_fin_two_iff`

English:
lemma mem_specialOrthogonalGroup_fin_two_iff
  given: {M : Matrix (Fin 2) (Fin 2) R}
  proof: by
  rw [← M.etaExpand_eq]
  exact of_mem_specialOrthogonalGroup_fin_two_iff

中文:
引理 mem_specialOrthogonalGroup_fin_two_iff
  条件: {M : Matrix (Fin 2) (Fin 2) R}
  证明: by
  rw [← M.etaExpand_eq]
  exact of_mem_specialOrthogonalGroup_fin_two_iff

Depends on / 依赖: M.etaExpand_eq, etaExpand_eq, of_mem_specialOrthogonalGroup_fin_two_iff
-/
lemma mem_specialOrthogonalGroup_fin_two_iff {M : Matrix (Fin 2) (Fin 2) R} :
    M in Matrix.specialOrthogonalGroup (Fin 2) R ↔
      M 0 0 = M 1 1 ∧ M 0 1 = - M 1 0 ∧ M 0 0 ^ 2 + M 0 1 ^ 2 = 1 := by
  rw [← M.etaExpand_eq]
  exact of_mem_specialOrthogonalGroup_fin_two_iff

end specialOrthogonalGroup

end Matrix
