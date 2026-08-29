/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.LinearAlgebra.Determinant

/-!
# Norm for (finite) ring extensions

Suppose we have an `R`-algebra `S` with a finite basis. For each `s : S`,
the determinant of the linear map given by multiplying by `s` gives information
about the roots of the minimal polynomial of `s` over `R`.

## Implementation notes

Typically, the norm is defined specifically for finite field extensions.
The current definition is as general as possible and the assumption that we have
fields or that the extension is finite is added to the lemmas as needed.

We only define the norm for left multiplication (`Algebra.leftMulMatrix`,
i.e. `LinearMap.mulLeft`).
For now, the definitions assume `S` is commutative, so the choice doesn't
matter anyway.

See also `Algebra.trace`, which is defined similarly as the trace of
`Algebra.leftMulMatrix`.

## References

* https://en.wikipedia.org/wiki/Field_norm

-/

@[expose] public section


universe u v w

variable {R S : Type*} [CommRing R] [Ring S]
variable [Algebra R S]
variable {K : Type*} [Field K]
variable {ι : Type w}

open Module

open LinearMap

open Matrix Polynomial

open scoped Matrix

namespace Algebra

variable (R)

/-- The norm of an element `s` of an `R`-algebra is the determinant of `(*) s`. -/
@[stacks 0BIF "Norm"]
/--
Definition of `norm` / `norm` 的定义

English:
definition norm
  signature: : S ->* R
  body: LinearMap.det.comp (lmul R S).toRingHom.toMonoidHom

中文:
定义 norm
  签名: : S ->* R
  定义体: LinearMap.det.comp (lmul R S).toRingHom.toMonoidHom

Depends on / 依赖: LinearMap, LinearMap.det.comp, toMonoidHom, toRingHom, toRingHom.toMonoidHom
-/
noncomputable def norm : S ->* R :=
  LinearMap.det.comp (lmul R S).toRingHom.toMonoidHom

/--
theorem `norm_apply` / 定理 `norm_apply`

English:
theorem norm_apply
  given: (x : S)
  statement: norm R x = LinearMap.det (lmul R S x)
  proof: rfl

@[simp]

中文:
定理 norm_apply
  条件: (x : S)
  结论: norm R x = 线性映射.det (lmul R S x)
  证明: rfl

@[simp]
-/
theorem norm_apply (x : S) : norm R x = LinearMap.det (lmul R S x) := rfl

@[simp]
/--
theorem `norm_self` / 定理 `norm_self`

English:
theorem norm_self
  statement: Algebra.norm R = MonoidHom.id R
  proof: by
  ext
  simp [norm_apply]

中文:
定理 norm_self
  结论: 代数.norm R = 幺半群态射.id R
  证明: by
  ext
  simp [norm_apply]

Depends on / 依赖: norm_apply
-/
theorem norm_self : Algebra.norm R = MonoidHom.id R := by
  ext
  simp [norm_apply]

/--
theorem `norm_eq_one_of_not_exists_basis` / 定理 `norm_eq_one_of_not_exists_basis`

English:
theorem norm_eq_one_of_not_exists_basis
  given: (h : ¬exists s : Finset S, Nonempty (Basis s R S)) (x : S)
  proof: by rw [norm_apply, LinearMap.det]; split_ifs <;> trivial

中文:
定理 norm_eq_one_of_not_存在_basis
  条件: (h : ¬存在 s : 有限集 S, 非空 (基 s R S)) (x : S)
  证明: by rw [norm_apply, LinearMap.det]; split_ifs <;> trivial

Depends on / 依赖: LinearMap, LinearMap.det, norm_apply, split_ifs
-/
theorem norm_eq_one_of_not_exists_basis (h : ¬exists s : Finset S, Nonempty (Basis s R S)) (x : S) :
    norm R x = 1 := by rw [norm_apply, LinearMap.det]; split_ifs <;> trivial

variable {R}

/--
theorem `norm_eq_one_of_not_module_finite` / 定理 `norm_eq_one_of_not_module_finite`

English:
theorem norm_eq_one_of_not_module_finite
  given: (h : ¬Module.Finite R S) (x : S)
  statement: norm R x = 1
  proof: by
  refine norm_eq_one_of_not_exists_basis _ (mt ?_ h) _
  rintro ⟨s, ⟨b⟩⟩
  exact Module.Finite.of_basis b

中文:
定理 norm_eq_one_of_not_module_finite
  条件: (h : ¬模.有限 R S) (x : S)
  结论: norm R x = 1
  证明: by
  refine norm_eq_one_of_not_exists_basis _ (mt ?_ h) _
  rintro ⟨s, ⟨b⟩⟩
  exact Module.Finite.of_basis b

Depends on / 依赖: Finite, Module, Module.Finite.of_basis, norm_eq_one_of_not_exists_basis, of_basis
-/
theorem norm_eq_one_of_not_module_finite (h : ¬Module.Finite R S) (x : S) : norm R x = 1 := by
  refine norm_eq_one_of_not_exists_basis _ (mt ?_ h) _
  rintro ⟨s, ⟨b⟩⟩
  exact Module.Finite.of_basis b

-- Can't be a `simp` lemma because it depends on a choice of basis
/--
theorem `norm_eq_matrix_det` / 定理 `norm_eq_matrix_det`

English:
theorem norm_eq_matrix_det
  given: [Fintype ι] [DecidableEq ι] (b : Basis ι R S) (s : S)
  proof: by
  rw [norm_apply]; rw [← LinearMap.det_toMatrix b]; rw [← toMatrix_lmul_eq]; rfl

中文:
定理 norm_eq_matrix_det
  条件: [有限类型 ι] [DecidableEq ι] (b : 基 ι R S) (s : S)
  证明: by
  rw [norm_apply]; rw [← LinearMap.det_toMatrix b]; rw [← toMatrix_lmul_eq]; rfl

Depends on / 依赖: LinearMap, LinearMap.det_toMatrix, det_toMatrix, norm_apply, toMatrix_lmul_eq
-/
theorem norm_eq_matrix_det [Fintype ι] [DecidableEq ι] (b : Basis ι R S) (s : S) :
    norm R s = Matrix.det (Algebra.leftMulMatrix b s) := by
  rw [norm_apply]; rw [← LinearMap.det_toMatrix b]; rw [← toMatrix_lmul_eq]; rfl

/--
theorem `norm_algebraMap_of_basis` / 定理 `norm_algebraMap_of_basis`

English:
theorem norm_algebraMap_of_basis
  given: [Fintype ι] (b : Basis ι R S) (x : R)
  proof: by
  have := Classical.decEq ι
  rw [norm_apply]; rw [← det_toMatrix b]; rw [lmul_algebraMap]
  simp

中文:
定理 norm_algebraMap_of_basis
  条件: [有限类型 ι] (b : 基 ι R S) (x : R)
  证明: by
  have := Classical.decEq ι
  rw [norm_apply]; rw [← det_toMatrix b]; rw [lmul_algebraMap]
  simp

Depends on / 依赖: Classical, Classical.decEq, det_toMatrix, lmul_algebraMap, norm_apply
-/
theorem norm_algebraMap_of_basis [Fintype ι] (b : Basis ι R S) (x : R) :
    norm R (algebraMap R S x) = x ^ Fintype.card ι := by
  have := Classical.decEq ι
  rw [norm_apply]; rw [← det_toMatrix b]; rw [lmul_algebraMap]
  simp

variable [Free R S]

/-- If `x` is in the base ring `R` and `S` is free over `R`, then the norm is `x ^ [S : R]`.

(If `S` is not finitely generated over `R`, then `norm = 1 = x ^ 0 = x ^ (finrank R S)`.)
-/
@[simp]
/--
theorem `norm_algebraMap` / 定理 `norm_algebraMap`

English:
theorem norm_algebraMap
  given: (x : R)
  statement: norm R (algebraMap R S x) = x ^ finrank R S
  proof: by
  rw [norm_apply]; rw [lmul_algebraMap]; rw [det_lsmul]

中文:
定理 norm_algebraMap
  条件: (x : R)
  结论: norm R (algebraMap R S x) = x ^ finrank R S
  证明: by
  rw [norm_apply]; rw [lmul_algebraMap]; rw [det_lsmul]
-/
protected theorem norm_algebraMap (x : R) : norm R (algebraMap R S x) = x ^ finrank R S := by
  rw [norm_apply]; rw [lmul_algebraMap]; rw [det_lsmul]

variable (R) in
/--
lemma `norm_natCast` / 引理 `norm_natCast`

English:
lemma norm_natCast
  given: (n : Nat)
  statement: norm R (n : S) = n ^ Module.finrank R S
  proof: by
  rw [← map_natCast (algebraMap R S)]; rw [Algebra.norm_algebraMap]

中文:
引理 norm_natCast
  条件: (n : 自然数)
  结论: norm R (n : S) = n ^ 模.finrank R S
  证明: by
  rw [← map_natCast (algebraMap R S)]; rw [Algebra.norm_algebraMap]
-/
protected lemma norm_natCast (n : Nat) : norm R (n : S) = n ^ Module.finrank R S := by
  rw [← map_natCast (algebraMap R S)]; rw [Algebra.norm_algebraMap]

end Algebra
