/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
module

public import Mathlib.LinearAlgebra.Basis.Submodule
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.GroupTheory.GroupAction.Ring

/-!
# Bases and matrices

This file defines the map `Basis.toMatrix` that sends a family of vectors to
the matrix of their coordinates with respect to some basis.

## Main definitions

* `Basis.toMatrix e v` is the matrix whose `i, j`th entry is `e.repr (v j) i`
* `basis.toMatrixEquiv` is `Basis.toMatrix` bundled as a linear equiv

## Main results

* `LinearMap.toMatrix_id_eq_basis_toMatrix`: `LinearMap.toMatrix b c id`
  is equal to `Basis.toMatrix b c`
* `Basis.toMatrix_mul_toMatrix`: multiplying `Basis.toMatrix` with another
  `Basis.toMatrix` gives a `Basis.toMatrix`

## Tags

matrix, basis
-/

@[expose] public section


noncomputable section

open Function LinearMap Matrix Module Set Submodule

variable {ι ι' κ κ' : Type*}
variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
variable {R₂ M₂ : Type*} [CommRing R₂] [AddCommGroup M₂] [Module R₂ M₂]

namespace Module.Basis

/--
Definition of `toMatrix` / `toMatrix` 的定义

English:
definition toMatrix
  signature: (e : Basis ι R M) (v : ι' -> M)
  body: fun i j => e.repr (v j) i

中文:
定义 toMatrix
  签名: (e : 基 ι R M) (v : ι' -> M)
  定义体: fun i j => e.repr (v j) i

Depends on / 依赖: e.repr
-/
def toMatrix (e : Basis ι R M) (v : ι' -> M) : Matrix ι ι' R := fun i j => e.repr (v j) i

variable (e : Basis ι R M) (v : ι' -> M) (i : ι) (j : ι')

/--
theorem `toMatrix_apply` / 定理 `toMatrix_apply`

English:
theorem toMatrix_apply
  statement: e.toMatrix v i j = e.repr (v j) i
  proof: rfl

中文:
定理 toMatrix_apply
  结论: e.toMatrix v i j = e.repr (v j) i
  证明: rfl
-/
theorem toMatrix_apply : e.toMatrix v i j = e.repr (v j) i :=
  rfl

/--
theorem `toMatrix_transpose_apply` / 定理 `toMatrix_transpose_apply`

English:
theorem toMatrix_transpose_apply
  statement: (e.toMatrix v)ᵀ j = e.repr (v j)
  proof: funext fun _ => rfl

中文:
定理 toMatrix_transpose_apply
  结论: (e.toMatrix v)ᵀ j = e.repr (v j)
  证明: funext fun _ => rfl
-/
theorem toMatrix_transpose_apply : (e.toMatrix v)ᵀ j = e.repr (v j) :=
  funext fun _ => rfl

/--
theorem `toMatrix_eq_toMatrix_constr` / 定理 `toMatrix_eq_toMatrix_constr`

English:
theorem toMatrix_eq_toMatrix_constr
  given: [Fintype ι] [DecidableEq ι] (v : ι -> M)
  proof: by
  ext
  rw [Basis.toMatrix_apply]; rw [LinearMap.toMatrix_apply]; rw [Basis.constr_basis]

中文:
定理 toMatrix_eq_toMatrix_constr
  条件: [有限类型 ι] [DecidableEq ι] (v : ι -> M)
  证明: by
  ext
  rw [Basis.toMatrix_apply]; rw [LinearMap.toMatrix_apply]; rw [Basis.constr_basis]

Depends on / 依赖: Basis.constr_basis, Basis.toMatrix_apply, LinearMap, LinearMap.toMatrix_apply, constr_basis, toMatrix_apply
-/
theorem toMatrix_eq_toMatrix_constr [Fintype ι] [DecidableEq ι] (v : ι -> M) :
    e.toMatrix v = LinearMap.toMatrix e e (e.constr Nat v) := by
  ext
  rw [Basis.toMatrix_apply]; rw [LinearMap.toMatrix_apply]; rw [Basis.constr_basis]

-- TODO (maybe) Adjust the definition of `Basis.toMatrix` to eliminate the transpose.
/--
theorem `coePiBasisFun.toMatrix_eq_transpose` / 定理 `coePiBasisFun.toMatrix_eq_transpose`

English:
theorem coePiBasisFun.toMatrix_eq_transpose
  given: [Finite ι]
  proof: by
  ext M i j
  rfl

@[simp]

中文:
定理 coePiBasisFun.toMatrix_eq_transpose
  条件: [有限 ι]
  证明: by
  ext M i j
  rfl

@[simp]
-/
theorem coePiBasisFun.toMatrix_eq_transpose [Finite ι] :
    ((Pi.basisFun R ι).toMatrix : Matrix ι ι R -> Matrix ι ι R) = Matrix.transpose := by
  ext M i j
  rfl

@[simp]
/--
theorem `toMatrix_self` / 定理 `toMatrix_self`

English:
theorem toMatrix_self
  given: [DecidableEq ι]
  statement: e.toMatrix e = 1
  proof: by
  unfold Basis.toMatrix
  ext i j
  simp [Matrix.one_apply, Finsupp.single_apply, eq_comm]

中文:
定理 toMatrix_self
  条件: [DecidableEq ι]
  结论: e.toMatrix e = 1
  证明: by
  unfold Basis.toMatrix
  ext i j
  simp [Matrix.one_apply, Finsupp.single_apply, eq_comm]

Depends on / 依赖: Basis.toMatrix, Finsupp, Finsupp.single_apply, Matrix, Matrix.one_apply, eq_comm, one_apply, single_apply, toMatrix
-/
theorem toMatrix_self [DecidableEq ι] : e.toMatrix e = 1 := by
  unfold Basis.toMatrix
  ext i j
  simp [Matrix.one_apply, Finsupp.single_apply, eq_comm]

/--
theorem `toMatrix_update` / 定理 `toMatrix_update`

English:
theorem toMatrix_update
  given: [DecidableEq ι'] (x : M)
  proof: by
  ext i' k
  rw [Basis.toMatrix]; rw [Matrix.updateCol_apply]; rw [e.toMatrix_apply]
  split_ifs with h
  · rw [h, update_self j x v]
  · rw [update_of_ne h]

中文:
定理 toMatrix_update
  条件: [DecidableEq ι'] (x : M)
  证明: by
  ext i' k
  rw [Basis.toMatrix]; rw [Matrix.updateCol_apply]; rw [e.toMatrix_apply]
  split_ifs with h
  · rw [h, update_self j x v]
  · rw [update_of_ne h]

Depends on / 依赖: Basis.toMatrix, Matrix, Matrix.updateCol_apply, e.toMatrix_apply, split_ifs, toMatrix, toMatrix_apply, updateCol_apply, update_of_ne, update_self
-/
theorem toMatrix_update [DecidableEq ι'] (x : M) :
    e.toMatrix (Function.update v j x) = Matrix.updateCol (e.toMatrix v) j (e.repr x) := by
  ext i' k
  rw [Basis.toMatrix]; rw [Matrix.updateCol_apply]; rw [e.toMatrix_apply]
  split_ifs with h
  · rw [h, update_self j x v]
  · rw [update_of_ne h]

set_option backward.isDefEq.respectTransparency false in
/-- The basis constructed by `unitsSMul` has vectors given by a diagonal matrix. -/
@[simp]
/--
theorem `toMatrix_unitsSMul` / 定理 `toMatrix_unitsSMul`

English:
theorem toMatrix_unitsSMul
  given: [DecidableEq ι] (e : Basis ι R₂ M₂) (w : ι -> R₂ˣ)
  proof: by
  ext i j
  by_cases h : i = j <;>
    simp [h, toMatrix_apply, unitsSMul_apply, Units.smul_def]

中文:
定理 toMatrix_unitsSMul
  条件: [DecidableEq ι] (e : 基 ι R₂ M₂) (w : ι -> R₂ˣ)
  证明: by
  ext i j
  by_cases h : i = j <;>
    simp [h, toMatrix_apply, unitsSMul_apply, Units.smul_def]

Depends on / 依赖: Units.smul_def, smul_def, toMatrix_apply, unitsSMul_apply
-/
theorem toMatrix_unitsSMul [DecidableEq ι] (e : Basis ι R₂ M₂) (w : ι -> R₂ˣ) :
    e.toMatrix (e.unitsSMul w) = diagonal ((↑) ∘ w) := by
  ext i j
  by_cases h : i = j <;>
    simp [h, toMatrix_apply, unitsSMul_apply, Units.smul_def]

/-- The basis constructed by `isUnitSMul` has vectors given by a diagonal matrix. -/
@[simp]
/--
theorem `toMatrix_isUnitSMul` / 定理 `toMatrix_isUnitSMul`

English:
theorem toMatrix_isUnitSMul
  statement: [DecidableEq ι] (e : Basis ι R₂ M₂) {w : ι -> R₂}
  proof: e.toMatrix_unitsSMul _

中文:
定理 toMatrix_isUnitSMul
  结论: [DecidableEq ι] (e : 基 ι R₂ M₂) {w : ι -> R₂}
  证明: e.toMatrix_unitsSMul _

Depends on / 依赖: e.toMatrix_unitsSMul, toMatrix_unitsSMul
-/
theorem toMatrix_isUnitSMul [DecidableEq ι] (e : Basis ι R₂ M₂) {w : ι -> R₂}
    (hw : forall i, IsUnit (w i)) : e.toMatrix (e.isUnitSMul hw) = diagonal w :=
  e.toMatrix_unitsSMul _

/--
theorem `toMatrix_smul_left` / 定理 `toMatrix_smul_left`

English:
theorem toMatrix_smul_left
  given: {G} [Group G] [DistribMulAction G M] [SMulCommClass G R M] (g : G)
  proof: rfl

@[simp]

中文:
定理 toMatrix_smul_left
  条件: {G} [群 G] [分配乘法作用 G M] [标量交换类 G R M] (g : G)
  证明: rfl

@[simp]
-/
theorem toMatrix_smul_left {G} [Group G] [DistribMulAction G M] [SMulCommClass G R M] (g : G) :
    (g • e).toMatrix v = e.toMatrix (g⁻¹ • v) := rfl

@[simp]
/--
theorem `sum_toMatrix_smul_self` / 定理 `sum_toMatrix_smul_self`

English:
theorem sum_toMatrix_smul_self
  given: [Fintype ι]
  statement: ∑ i : ι, e.toMatrix v i j • e i = v j
  proof: by
  simp_rw [e.toMatrix_apply, e.sum_repr]

中文:
定理 sum_toMatrix_smul_self
  条件: [有限类型 ι]
  结论: ∑ i : ι, e.toMatrix v i j • e i = v j
  证明: by
  simp_rw [e.toMatrix_apply, e.sum_repr]

Depends on / 依赖: e.sum_repr, e.toMatrix_apply, simp_rw, sum_repr, toMatrix_apply
-/
theorem sum_toMatrix_smul_self [Fintype ι] : ∑ i : ι, e.toMatrix v i j • e i = v j := by
  simp_rw [e.toMatrix_apply, e.sum_repr]

/--
theorem `toMatrix_smul` / 定理 `toMatrix_smul`

English:
theorem toMatrix_smul
  statement: {R₁ S : Type*} [CommSemiring R₁] [Semiring S] [Algebra R₁ S] [Fintype ι]
  proof: by
  ext
  rw [Basis.toMatrix_apply]; rw [Pi.smul_apply]; rw [smul_eq_mul]; rw [← Algebra.leftMulMatrix_mulVec_repr]
  rfl

中文:
定理 toMatrix_smul
  结论: {R₁ S : 类型} [交换半环 R₁] [半环 S] [代数 R₁ S] [有限类型 ι]
  证明: by
  ext
  rw [Basis.toMatrix_apply]; rw [Pi.smul_apply]; rw [smul_eq_mul]; rw [← Algebra.leftMulMatrix_mulVec_repr]
  rfl

Depends on / 依赖: Algebra, Algebra.leftMulMatrix_mulVec_repr, Basis.toMatrix_apply, Pi.smul_apply, leftMulMatrix_mulVec_repr, smul_apply, smul_eq_mul, toMatrix_apply
-/
theorem toMatrix_smul {R₁ S : Type*} [CommSemiring R₁] [Semiring S] [Algebra R₁ S] [Fintype ι]
    [DecidableEq ι] (x : S) (b : Basis ι R₁ S) (w : ι -> S) :
    (b.toMatrix (x • w)) = (Algebra.leftMulMatrix b x) * (b.toMatrix w) := by
  ext
  rw [Basis.toMatrix_apply]; rw [Pi.smul_apply]; rw [smul_eq_mul]; rw [← Algebra.leftMulMatrix_mulVec_repr]
  rfl

/--
theorem `toMatrix_map_vecMul` / 定理 `toMatrix_map_vecMul`

English:
theorem toMatrix_map_vecMul
  statement: {S : Type*} [Semiring S] [Algebra R S] [Fintype ι] (b : Basis ι R S)
  proof: by
  ext i
  simp_rw [vecMul, dotProduct, Matrix.map_apply, ← Algebra.commutes, ← Algebra.smul_def,
    sum_toMatrix_smul_self]

@[simp]

中文:
定理 toMatrix_map_vecMul
  结论: {S : 类型} [半环 S] [代数 R S] [有限类型 ι] (b : 基 ι R S)
  证明: by
  ext i
  simp_rw [vecMul, dotProduct, Matrix.map_apply, ← Algebra.commutes, ← Algebra.smul_def,
    sum_toMatrix_smul_self]

@[simp]

Depends on / 依赖: Algebra, Algebra.commutes, Algebra.smul_def, Matrix, Matrix.map_apply, commutes, dotProduct, map_apply, simp_rw, smul_def, sum_toMatrix_smul_self, vecMul
-/
theorem toMatrix_map_vecMul {S : Type*} [Semiring S] [Algebra R S] [Fintype ι] (b : Basis ι R S)
    (v : ι' -> S) : b ᵥ* ((b.toMatrix v).map <| algebraMap R S) = v := by
  ext i
  simp_rw [vecMul, dotProduct, Matrix.map_apply, ← Algebra.commutes, ← Algebra.smul_def,
    sum_toMatrix_smul_self]

@[simp]
/--
theorem `toLin_toMatrix` / 定理 `toLin_toMatrix`

English:
theorem toLin_toMatrix
  given: [Finite ι] [Fintype ι'] [DecidableEq ι'] (v : Basis ι' R M)
  proof: v.ext fun i => by cases nonempty_fintype ι; rw [toLin_self, id_apply, e.sum_toMatrix_smul_self]

中文:
定理 toLin_toMatrix
  条件: [有限 ι] [有限类型 ι'] [DecidableEq ι'] (v : 基 ι' R M)
  证明: v.ext fun i => by cases nonempty_fintype ι; rw [toLin_self, id_apply, e.sum_toMatrix_smul_self]

Depends on / 依赖: e.sum_toMatrix_smul_self, id_apply, nonempty_fintype, sum_toMatrix_smul_self, toLin_self, v.ext
-/
theorem toLin_toMatrix [Finite ι] [Fintype ι'] [DecidableEq ι'] (v : Basis ι' R M) :
    Matrix.toLin v e (e.toMatrix v) = LinearMap.id :=
  v.ext fun i => by cases nonempty_fintype ι; rw [toLin_self, id_apply, e.sum_toMatrix_smul_self]

/--
Definition of `toMatrixEquiv` / `toMatrixEquiv` 的定义

English:
definition toMatrixEquiv
  signature: [Fintype ι] (e : Basis ι R M)
  body: e.toMatrix
  map_add' v w := by
    ext i j
    rw [Matrix.add_apply]; rw [e.toMatrix_apply]; rw [Pi.add_apply]; rw [map_add]
    rfl
  map_smul' := by
    intro c v
    ext i j
    rw [e.toMatrix_apply]; rw [Pi.smul_apply]; rw [map_smul]
    rfl
  invFun m j := ∑ i, m i j • e i
  left_inv := by
    intro v
    ext j
    exact e.sum_toMatrix_smul_self v j
  right_inv := by
    intro m
    ext k l
    simp only [e.toMatrix_apply, ← e.equivFun_apply, ← e.equivFun_symm_apply,
      LinearEquiv.apply_symm_apply]

中文:
定义 toMatrixEquiv
  签名: [有限类型 ι] (e : 基 ι R M)
  定义体: e.toMatrix
  map_add' v w := by
    ext i j
    rw [Matrix.add_apply]; rw [e.toMatrix_apply]; rw [Pi.add_apply]; rw [map_add]
    rfl
  map_smul' := by
    intro c v
    ext i j
    rw [e.toMatrix_apply]; rw [Pi.smul_apply]; rw [map_smul]
    rfl
  invFun m j := ∑ i, m i j • e i
  left_inv := by
    intro v
    ext j
    exact e.sum_toMatrix_smul_self v j
  right_inv := by
    intro m
    ext k l
    simp only [e.toMatrix_apply, ← e.equivFun_apply, ← e.equivFun_symm_apply,
      LinearEquiv.apply_symm_apply]

Depends on / 依赖: e.toMatrix, toMatrix
-/
def toMatrixEquiv [Fintype ι] (e : Basis ι R M) : (ι -> M) ≃ₗ[R] Matrix ι ι R where
  toFun := e.toMatrix
  map_add' v w := by
    ext i j
    rw [Matrix.add_apply]; rw [e.toMatrix_apply]; rw [Pi.add_apply]; rw [map_add]
    rfl
  map_smul' := by
    intro c v
    ext i j
    rw [e.toMatrix_apply]; rw [Pi.smul_apply]; rw [map_smul]
    rfl
  invFun m j := ∑ i, m i j • e i
  left_inv := by
    intro v
    ext j
    exact e.sum_toMatrix_smul_self v j
  right_inv := by
    intro m
    ext k l
    simp only [e.toMatrix_apply, ← e.equivFun_apply, ← e.equivFun_symm_apply,
      LinearEquiv.apply_symm_apply]

variable (R₂) in
/--
theorem `restrictScalars_toMatrix` / 定理 `restrictScalars_toMatrix`

English:
theorem restrictScalars_toMatrix
  statement: [Fintype ι] [DecidableEq ι] {S : Type*} [CommRing S] [Nontrivial S]
  proof: by
  ext
  rw [RingHom.mapMatrix_apply]; rw [Matrix.map_apply]; rw [Basis.toMatrix_apply]; rw [Basis.restrictScalars_repr_apply]; rw [Basis.toMatrix_apply]

中文:
定理 restrictScalars_toMatrix
  结论: [有限类型 ι] [DecidableEq ι] {S : 类型} [交换环 S] [非平凡 S]
  证明: by
  ext
  rw [RingHom.mapMatrix_apply]; rw [Matrix.map_apply]; rw [Basis.toMatrix_apply]; rw [Basis.restrictScalars_repr_apply]; rw [Basis.toMatrix_apply]

Depends on / 依赖: Basis.restrictScalars_repr_apply, Basis.toMatrix_apply, Matrix, Matrix.map_apply, RingHom, RingHom.mapMatrix_apply, mapMatrix_apply, map_apply, restrictScalars_repr_apply, toMatrix_apply
-/
theorem restrictScalars_toMatrix [Fintype ι] [DecidableEq ι] {S : Type*} [CommRing S] [Nontrivial S]
    [Algebra R₂ S] [Module S M₂] [IsScalarTower R₂ S M₂] [IsDomain R₂] [IsTorsionFree R₂ S]
    (b : Basis ι S M₂) (v : ι -> span R₂ (Set.range b)) :
    (algebraMap R₂ S).mapMatrix ((b.restrictScalars R₂).toMatrix v) =
      b.toMatrix (fun i => (v i : M₂)) := by
  ext
  rw [RingHom.mapMatrix_apply]; rw [Matrix.map_apply]; rw [Basis.toMatrix_apply]; rw [Basis.restrictScalars_repr_apply]; rw [Basis.toMatrix_apply]

end Module.Basis

section MulLinearMapToMatrix

variable {N : Type*} [AddCommMonoid N] [Module R N]
variable (b : Basis ι R M) (b' : Basis ι' R M) (c : Basis κ R N) (c' : Basis κ' R N)
variable (f : M ->ₗ[R] N)

open LinearMap

section Fintype

/-- A generalization of `LinearMap.toMatrix_id`. -/
@[simp]
/--
theorem `LinearMap.toMatrix_id_eq_basis_toMatrix` / 定理 `LinearMap.toMatrix_id_eq_basis_toMatrix`

English:
theorem LinearMap.toMatrix_id_eq_basis_toMatrix
  given: [Fintype ι] [DecidableEq ι] [Finite ι']
  proof: by
  ext i
  apply LinearMap.toMatrix_apply

中文:
定理 线性映射.toMatrix_id_eq_basis_toMatrix
  条件: [有限类型 ι] [DecidableEq ι] [有限 ι']
  证明: by
  ext i
  apply LinearMap.toMatrix_apply

Depends on / 依赖: LinearMap, LinearMap.toMatrix_apply, toMatrix_apply
-/
theorem LinearMap.toMatrix_id_eq_basis_toMatrix [Fintype ι] [DecidableEq ι] [Finite ι'] :
    LinearMap.toMatrix b b' id = b'.toMatrix b := by
  ext i
  apply LinearMap.toMatrix_apply

variable [Fintype ι']

@[simp]
/--
theorem `basis_toMatrix_mul_linearMap_toMatrix` / 定理 `basis_toMatrix_mul_linearMap_toMatrix`

English:
theorem basis_toMatrix_mul_linearMap_toMatrix
  given: [Finite κ] [Fintype κ'] [DecidableEq ι']
  proof: (Matrix.toLin b' c).injective by
    have := Classical.decEq κ'
    rw [toLin_toMatrix]; rw [toLin_mul b' c' c]; rw [toLin_toMatrix]; rw [c.toLin_toMatrix]; rw [LinearMap.id_comp]

中文:
定理 basis_toMatrix_mul_linearMap_toMatrix
  条件: [有限 κ] [有限类型 κ'] [DecidableEq ι']
  证明: (Matrix.toLin b' c).injective by
    have := Classical.decEq κ'
    rw [toLin_toMatrix]; rw [toLin_mul b' c' c]; rw [toLin_toMatrix]; rw [c.toLin_toMatrix]; rw [LinearMap.id_comp]

Depends on / 依赖: Classical, Classical.decEq, LinearMap, LinearMap.id_comp, Matrix, Matrix.toLin, c.toLin_toMatrix, id_comp, injective, toLin_mul, toLin_toMatrix
-/
theorem basis_toMatrix_mul_linearMap_toMatrix [Finite κ] [Fintype κ'] [DecidableEq ι'] :
    c.toMatrix c' * LinearMap.toMatrix b' c' f = LinearMap.toMatrix b' c f :=
(Matrix.toLin b' c).injective by
    have := Classical.decEq κ'
    rw [toLin_toMatrix]; rw [toLin_mul b' c' c]; rw [toLin_toMatrix]; rw [c.toLin_toMatrix]; rw [LinearMap.id_comp]

/--
theorem `basis_toMatrix_mul` / 定理 `basis_toMatrix_mul`

English:
theorem basis_toMatrix_mul
  statement: [Fintype κ] [Finite ι] [DecidableEq κ]
  proof: by
  have := basis_toMatrix_mul_linearMap_toMatrix b₃ b₁ b₂ (Matrix.toLin b₃ b₂ A)
  rwa [LinearMap.toMatrix_toLin] at this

中文:
定理 basis_toMatrix_mul
  结论: [有限类型 κ] [有限 ι] [DecidableEq κ]
  证明: by
  have := basis_toMatrix_mul_linearMap_toMatrix b₃ b₁ b₂ (Matrix.toLin b₃ b₂ A)
  rwa [LinearMap.toMatrix_toLin] at this

Depends on / 依赖: LinearMap, LinearMap.toMatrix_toLin, Matrix, Matrix.toLin, basis_toMatrix_mul_linearMap_toMatrix, toMatrix_toLin
-/
theorem basis_toMatrix_mul [Fintype κ] [Finite ι] [DecidableEq κ]
    (b₁ : Basis ι R M) (b₂ : Basis ι' R M) (b₃ : Basis κ R N) (A : Matrix ι' κ R) :
    b₁.toMatrix b₂ * A = LinearMap.toMatrix b₃ b₁ (toLin b₃ b₂ A) := by
  have := basis_toMatrix_mul_linearMap_toMatrix b₃ b₁ b₂ (Matrix.toLin b₃ b₂ A)
  rwa [LinearMap.toMatrix_toLin] at this

variable [Finite κ] [Fintype ι]

@[simp]
/--
theorem `linearMap_toMatrix_mul_basis_toMatrix` / 定理 `linearMap_toMatrix_mul_basis_toMatrix`

English:
theorem linearMap_toMatrix_mul_basis_toMatrix
  given: [Finite κ'] [DecidableEq ι] [DecidableEq ι']
  proof: (Matrix.toLin b c').injective by
    rw [toLin_toMatrix]; rw [toLin_mul b b' c']; rw [toLin_toMatrix]; rw [b'.toLin_toMatrix]; rw [LinearMap.comp_id]

中文:
定理 linearMap_toMatrix_mul_basis_toMatrix
  条件: [有限 κ'] [DecidableEq ι] [DecidableEq ι']
  证明: (Matrix.toLin b c').injective by
    rw [toLin_toMatrix]; rw [toLin_mul b b' c']; rw [toLin_toMatrix]; rw [b'.toLin_toMatrix]; rw [LinearMap.comp_id]

Depends on / 依赖: LinearMap, LinearMap.comp_id, Matrix, Matrix.toLin, comp_id, injective, toLin_mul, toLin_toMatrix
-/
theorem linearMap_toMatrix_mul_basis_toMatrix [Finite κ'] [DecidableEq ι] [DecidableEq ι'] :
    LinearMap.toMatrix b' c' f * b'.toMatrix b = LinearMap.toMatrix b c' f :=
(Matrix.toLin b c').injective by
    rw [toLin_toMatrix]; rw [toLin_mul b b' c']; rw [toLin_toMatrix]; rw [b'.toLin_toMatrix]; rw [LinearMap.comp_id]

/--
theorem `basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix` / 定理 `basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix`

English:
theorem basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
  proof: by
  cases nonempty_fintype κ
  rw [basis_toMatrix_mul_linearMap_toMatrix]; rw [linearMap_toMatrix_mul_basis_toMatrix]

中文:
定理 basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
  证明: by
  cases nonempty_fintype κ
  rw [basis_toMatrix_mul_linearMap_toMatrix]; rw [linearMap_toMatrix_mul_basis_toMatrix]

Depends on / 依赖: basis_toMatrix_mul_linearMap_toMatrix, linearMap_toMatrix_mul_basis_toMatrix, nonempty_fintype
-/
theorem basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
    [Fintype κ'] [DecidableEq ι] [DecidableEq ι'] :
    c.toMatrix c' * LinearMap.toMatrix b' c' f * b'.toMatrix b = LinearMap.toMatrix b c f := by
  cases nonempty_fintype κ
  rw [basis_toMatrix_mul_linearMap_toMatrix]; rw [linearMap_toMatrix_mul_basis_toMatrix]

/--
theorem `mul_basis_toMatrix` / 定理 `mul_basis_toMatrix`

English:
theorem mul_basis_toMatrix
  statement: [DecidableEq ι] [DecidableEq ι'] (b₁ : Basis ι R M) (b₂ : Basis ι' R M)
  proof: by
  cases nonempty_fintype κ
  have := linearMap_toMatrix_mul_basis_toMatrix b₂ b₁ b₃ (Matrix.toLin b₁ b₃ A)
  rwa [LinearMap.toMatrix_toLin] at this

中文:
定理 mul_basis_toMatrix
  结论: [DecidableEq ι] [DecidableEq ι'] (b₁ : 基 ι R M) (b₂ : 基 ι' R M)
  证明: by
  cases nonempty_fintype κ
  have := linearMap_toMatrix_mul_basis_toMatrix b₂ b₁ b₃ (Matrix.toLin b₁ b₃ A)
  rwa [LinearMap.toMatrix_toLin] at this

Depends on / 依赖: LinearMap, LinearMap.toMatrix_toLin, Matrix, Matrix.toLin, linearMap_toMatrix_mul_basis_toMatrix, nonempty_fintype, toMatrix_toLin
-/
theorem mul_basis_toMatrix [DecidableEq ι] [DecidableEq ι'] (b₁ : Basis ι R M) (b₂ : Basis ι' R M)
    (b₃ : Basis κ R N) (A : Matrix κ ι R) :
    A * b₁.toMatrix b₂ = LinearMap.toMatrix b₂ b₃ (toLin b₁ b₃ A) := by
  cases nonempty_fintype κ
  have := linearMap_toMatrix_mul_basis_toMatrix b₂ b₁ b₃ (Matrix.toLin b₁ b₃ A)
  rwa [LinearMap.toMatrix_toLin] at this

/--
theorem `basis_toMatrix_basisFun_mul` / 定理 `basis_toMatrix_basisFun_mul`

English:
theorem basis_toMatrix_basisFun_mul
  given: (b : Basis ι R (ι -> R)) (A : Matrix ι ι R)
  proof: by
  classical
  simp only [basis_toMatrix_mul _ _ (Pi.basisFun R ι), Matrix.toLin_eq_toLin']
  ext i j
  rw [LinearMap.toMatrix_apply]; rw [Matrix.toLin'_apply]; rw [Pi.basisFun_apply]; rw [Matrix.mulVec_single_one]; rw [Matrix.of_apply]

中文:
定理 basis_toMatrix_basisFun_mul
  条件: (b : 基 ι R (ι -> R)) (A : 矩阵 ι ι R)
  证明: by
  classical
  simp only [basis_toMatrix_mul _ _ (Pi.basisFun R ι), Matrix.toLin_eq_toLin']
  ext i j
  rw [LinearMap.toMatrix_apply]; rw [Matrix.toLin'_apply]; rw [Pi.basisFun_apply]; rw [Matrix.mulVec_single_one]; rw [Matrix.of_apply]

Depends on / 依赖: LinearMap, LinearMap.toMatrix_apply, Matrix, Matrix.mulVec_single_one, Matrix.of_apply, Matrix.toLin, Matrix.toLin_eq_toLin, Pi.basisFun, Pi.basisFun_apply, _apply, basisFun, basisFun_apply, basis_toMatrix_mul, classical, mulVec_single_one, of_apply, toLin_eq_toLin, toMatrix_apply
-/
theorem basis_toMatrix_basisFun_mul (b : Basis ι R (ι -> R)) (A : Matrix ι ι R) :
    b.toMatrix (Pi.basisFun R ι) * A = of fun i j => b.repr (A.col j) i := by
  classical
  simp only [basis_toMatrix_mul _ _ (Pi.basisFun R ι), Matrix.toLin_eq_toLin']
  ext i j
  rw [LinearMap.toMatrix_apply]; rw [Matrix.toLin'_apply]; rw [Pi.basisFun_apply]; rw [Matrix.mulVec_single_one]; rw [Matrix.of_apply]

namespace Module.Basis

/--
theorem `toMatrix_reindex'` / 定理 `toMatrix_reindex'`

English:
theorem toMatrix_reindex'
  statement: [DecidableEq ι] [DecidableEq ι'] (b : Basis ι R M) (v : ι' -> M)
  proof: by
  ext
  simp [Basis.toMatrix_apply]

omit [Fintype ι'] in
@[simp]

中文:
定理 toMatrix_reindex'
  结论: [DecidableEq ι] [DecidableEq ι'] (b : 基 ι R M) (v : ι' -> M)
  证明: by
  ext
  simp [Basis.toMatrix_apply]

omit [Fintype ι'] in
@[simp]

Depends on / 依赖: Basis.toMatrix_apply, toMatrix_apply
-/
theorem toMatrix_reindex' [DecidableEq ι] [DecidableEq ι'] (b : Basis ι R M) (v : ι' -> M)
    (e : ι ≃ ι') : (b.reindex e).toMatrix v =
    Matrix.reindexAlgEquiv R R e (b.toMatrix (v ∘ e)) := by
  ext
  simp [Basis.toMatrix_apply]

omit [Fintype ι'] in
@[simp]
/--
lemma `toMatrix_mulVec_repr` / 引理 `toMatrix_mulVec_repr`

English:
lemma toMatrix_mulVec_repr
  given: [Finite ι'] (m : M)
  statement: b'.toMatrix b *ᵥ b.repr m = b'.repr m
  proof: by
  classical
  cases nonempty_fintype ι'
  simp [← LinearMap.toMatrix_id_eq_basis_toMatrix, LinearMap.toMatrix_mulVec_repr]

中文:
引理 toMatrix_mulVec_repr
  条件: [有限 ι'] (m : M)
  结论: b'.toMatrix b *ᵥ b.repr m = b'.repr m
  证明: by
  classical
  cases nonempty_fintype ι'
  simp [← LinearMap.toMatrix_id_eq_basis_toMatrix, LinearMap.toMatrix_mulVec_repr]

Depends on / 依赖: LinearMap, LinearMap.toMatrix_id_eq_basis_toMatrix, LinearMap.toMatrix_mulVec_repr, classical, nonempty_fintype, toMatrix_id_eq_basis_toMatrix, toMatrix_mulVec_repr
-/
lemma toMatrix_mulVec_repr [Finite ι'] (m : M) : b'.toMatrix b *ᵥ b.repr m = b'.repr m := by
  classical
  cases nonempty_fintype ι'
  simp [← LinearMap.toMatrix_id_eq_basis_toMatrix, LinearMap.toMatrix_mulVec_repr]

end Module.Basis
end Fintype

namespace Module.Basis

/-- A generalization of `Basis.toMatrix_self`, in the opposite direction. -/
@[simp]
/--
theorem `toMatrix_mul_toMatrix` / 定理 `toMatrix_mul_toMatrix`

English:
theorem toMatrix_mul_toMatrix
  given: {ι'' : Type*} [Fintype ι'] (b'' : ι'' -> M)
  proof: by
  have := Classical.decEq ι
  have := Classical.decEq ι'
  have := Classical.decEq ι''
  ext i j
  simp only [Matrix.mul_apply, toMatrix_apply, sum_repr_mul_repr]

中文:
定理 toMatrix_mul_toMatrix
  条件: {ι'' : 类型} [有限类型 ι'] (b'' : ι'' -> M)
  证明: by
  have := Classical.decEq ι
  have := Classical.decEq ι'
  have := Classical.decEq ι''
  ext i j
  simp only [Matrix.mul_apply, toMatrix_apply, sum_repr_mul_repr]

Depends on / 依赖: Classical, Classical.decEq, Matrix, Matrix.mul_apply, mul_apply, sum_repr_mul_repr, toMatrix_apply
-/
theorem toMatrix_mul_toMatrix {ι'' : Type*} [Fintype ι'] (b'' : ι'' -> M) :
    b.toMatrix b' * b'.toMatrix b'' = b.toMatrix b'' := by
  have := Classical.decEq ι
  have := Classical.decEq ι'
  have := Classical.decEq ι''
  ext i j
  simp only [Matrix.mul_apply, toMatrix_apply, sum_repr_mul_repr]

/--
theorem `toMatrix_mul_toMatrix_flip` / 定理 `toMatrix_mul_toMatrix_flip`

English:
theorem toMatrix_mul_toMatrix_flip
  given: [DecidableEq ι] [Fintype ι']
  proof: by rw [toMatrix_mul_toMatrix, toMatrix_self]

中文:
定理 toMatrix_mul_toMatrix_flip
  条件: [DecidableEq ι] [有限类型 ι']
  证明: by rw [toMatrix_mul_toMatrix, toMatrix_self]

Depends on / 依赖: toMatrix_mul_toMatrix, toMatrix_self
-/
theorem toMatrix_mul_toMatrix_flip [DecidableEq ι] [Fintype ι'] :
    b.toMatrix b' * b'.toMatrix b = 1 := by rw [toMatrix_mul_toMatrix, toMatrix_self]

/-- A matrix whose columns form a basis `b'`, expressed w.r.t. a basis `b`, is invertible. -/
@[instance_reducible]
/--
Definition of `invertibleToMatrix` / `invertibleToMatrix` 的定义

English:
definition invertibleToMatrix
  signature: [DecidableEq ι] [Fintype ι] (b b' : Basis ι R₂ M₂)
  body: ⟨b'.toMatrix b, toMatrix_mul_toMatrix_flip _ _, toMatrix_mul_toMatrix_flip _ _⟩

@[simp]

中文:
定义 invertibleToMatrix
  签名: [DecidableEq ι] [有限类型 ι] (b b' : 基 ι R₂ M₂)
  定义体: ⟨b'.toMatrix b, toMatrix_mul_toMatrix_flip _ _, toMatrix_mul_toMatrix_flip _ _⟩

@[simp]

Depends on / 依赖: toMatrix, toMatrix_mul_toMatrix_flip
-/
def invertibleToMatrix [DecidableEq ι] [Fintype ι] (b b' : Basis ι R₂ M₂) :
    Invertible (b.toMatrix b') :=
  ⟨b'.toMatrix b, toMatrix_mul_toMatrix_flip _ _, toMatrix_mul_toMatrix_flip _ _⟩

@[simp]
/--
theorem `toMatrix_reindex` / 定理 `toMatrix_reindex`

English:
theorem toMatrix_reindex
  given: (b : Basis ι R M) (v : ι' -> M) (e : ι ≃ ι')
  proof: by
  ext
  simp only [toMatrix_apply, repr_reindex, Matrix.submatrix_apply, _root_.id,
    Finsupp.mapDomain_equiv_apply]

@[simp]

中文:
定理 toMatrix_reindex
  条件: (b : 基 ι R M) (v : ι' -> M) (e : ι ≃ ι')
  证明: by
  ext
  simp only [toMatrix_apply, repr_reindex, Matrix.submatrix_apply, _root_.id,
    Finsupp.mapDomain_equiv_apply]

@[simp]

Depends on / 依赖: Finsupp, Finsupp.mapDomain_equiv_apply, Matrix, Matrix.submatrix_apply, _root_, _root_.id, mapDomain_equiv_apply, repr_reindex, submatrix_apply, toMatrix_apply
-/
theorem toMatrix_reindex (b : Basis ι R M) (v : ι' -> M) (e : ι ≃ ι') :
    (b.reindex e).toMatrix v = (b.toMatrix v).submatrix e.symm _root_.id := by
  ext
  simp only [toMatrix_apply, repr_reindex, Matrix.submatrix_apply, _root_.id,
    Finsupp.mapDomain_equiv_apply]

@[simp]
/--
theorem `toMatrix_map` / 定理 `toMatrix_map`

English:
theorem toMatrix_map
  given: (b : Basis ι R M) (f : M ≃ₗ[R] N) (v : ι -> N)
  proof: by
  ext
  simp only [toMatrix_apply, Basis.map, LinearEquiv.trans_apply, (· ∘ ·)]

中文:
定理 toMatrix_map
  条件: (b : 基 ι R M) (f : M ≃ₗ[R] N) (v : ι -> N)
  证明: by
  ext
  simp only [toMatrix_apply, Basis.map, LinearEquiv.trans_apply, (· ∘ ·)]

Depends on / 依赖: Basis.map, LinearEquiv, LinearEquiv.trans_apply, toMatrix_apply, trans_apply
-/
theorem toMatrix_map (b : Basis ι R M) (f : M ≃ₗ[R] N) (v : ι -> N) :
    (b.map f).toMatrix v = b.toMatrix (f.symm ∘ v) := by
  ext
  simp only [toMatrix_apply, Basis.map, LinearEquiv.trans_apply, (· ∘ ·)]

/--
lemma `_root_.LinearMap.toMatrix_eq_basisToMatrix` / 引理 `_root_.LinearMap.toMatrix_eq_basisToMatrix`

English:
lemma _root_.LinearMap.toMatrix_eq_basisToMatrix
  given: [Fintype ι] [DecidableEq ι] [Finite κ]
  proof: by ext; simp [LinearMap.toMatrix_apply, toMatrix_apply]

中文:
引理 _root_.线性映射.toMatrix_eq_basisToMatrix
  条件: [有限类型 ι] [DecidableEq ι] [有限 κ]
  证明: by ext; simp [LinearMap.toMatrix_apply, toMatrix_apply]

Depends on / 依赖: LinearMap, LinearMap.toMatrix_apply, toMatrix_apply
-/
lemma _root_.LinearMap.toMatrix_eq_basisToMatrix [Fintype ι] [DecidableEq ι] [Finite κ] :
    f.toMatrix b c = c.toMatrix (f ∘ b) := by ext; simp [LinearMap.toMatrix_apply, toMatrix_apply]

end Module.Basis
end MulLinearMapToMatrix
