/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.RingTheory.Trace.Basic

/-!
# Discriminant of a family of vectors

Given an `A`-algebra `B` and `b`, an `ι`-indexed family of elements of `B`, we define the
*discriminant* of `b` as the determinant of the matrix whose `(i j)`-th element is the trace of
`b i * b j`.

## Main definition

* `Algebra.discr A b` : the discriminant of `b : ι → B`.

## Main results

* `Algebra.discr_zero_of_not_linearIndependent` : if `b` is not linear independent, then
  `Algebra.discr A b = 0`.
* `Algebra.discr_of_matrix_vecMul` and `Algebra.discr_of_matrix_mulVec` : formulas relating
  `Algebra.discr A ι b` with `Algebra.discr A (b ᵥ* P.map (algebraMap A B))` and
  `Algebra.discr A (P.map (algebraMap A B) *ᵥ b)`.
* `Algebra.discr_not_zero_of_basis` : over a field, if `b` is a basis, then
  `Algebra.discr K b ≠ 0`.
* `Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two` : if `L/K` is a field extension and
  `b : ι → L`, then `discr K b` is the square of the determinant of the matrix whose `(i, j)`
  coefficient is `σⱼ (b i)`, where `σⱼ : L →ₐ[K] E` is the embedding in an algebraically closed
  field `E` corresponding to `j : ι` via a bijection `e : ι ≃ (L →ₐ[K] E)`.
* `Algebra.discr_powerBasis_eq_prod` : the discriminant of a power basis.
* `Algebra.discr_isIntegral` : if `K` and `L` are fields and `IsScalarTower R K L`, if
  `b : ι → L` satisfies `∀ i, IsIntegral R (b i)`, then `IsIntegral R (discr K b)`.
* `Algebra.discr_mul_isIntegral_mem_adjoin` : let `K` be the fraction field of an integrally
  closed domain `R` and let `L` be a finite separable extension of `K`. Let `B : PowerBasis K L`
  be such that `IsIntegral R B.gen`. Then for all, `z : L` we have
  `(discr K B.basis) • z ∈ adjoin R ({B.gen} : Set L)`.

## Implementation details

Our definition works for any `A`-algebra `B`, but note that if `B` is not free as an `A`-module,
then `trace A B = 0` by definition, so `discr A b = 0` for any `b`.
-/

@[expose] public section


universe u v w z

open scoped Matrix

open Matrix Module Fintype Polynomial Finset IntermediateField

namespace Algebra

variable (A : Type u) {B : Type v} (C : Type z) {ι : Type w} [DecidableEq ι]
variable [CommRing A] [CommRing B] [Algebra A B] [CommRing C] [Algebra A C]

section Discr

/--
Definition of `discr` / `discr` 的定义

English:
definition discr
  signature: (A : Type u) {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
  body: (traceMatrix A b).det

中文:
定义 discr
  签名: (A : 类型u) {B : 类型v} [交换环 A] [交换环 B] [代数 A B]
  定义体: (traceMatrix A b).det

Depends on / 依赖: traceMatrix
-/
noncomputable def discr (A : Type u) {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [Fintype ι] (b : ι -> B) := (traceMatrix A b).det

/--
theorem `discr_def` / 定理 `discr_def`

English:
theorem discr_def
  given: [Fintype ι] (b : ι -> B)
  statement: discr A b = (traceMatrix A b).det
  proof: rfl

中文:
定理 discr_def
  条件: [有限类型 ι] (b : ι -> B)
  结论: discr A b = (traceMatrix A b).det
  证明: rfl
-/
theorem discr_def [Fintype ι] (b : ι -> B) : discr A b = (traceMatrix A b).det := rfl

variable {A C} in
/--
theorem `discr_eq_discr_of_algEquiv` / 定理 `discr_eq_discr_of_algEquiv`

English:
theorem discr_eq_discr_of_algEquiv
  given: [Fintype ι] (b : ι -> B) (f : B ≃ₐ[A] C)
  proof: by
  rw [discr_def]; congr; ext
  simp_rw [traceMatrix_apply, traceForm_apply, Function.comp, ← map_mul f, trace_eq_of_algEquiv]

中文:
定理 discr_eq_discr_of_algEquiv
  条件: [有限类型 ι] (b : ι -> B) (f : B ≃ₐ[A] C)
  证明: by
  rw [discr_def]; congr; ext
  simp_rw [traceMatrix_apply, traceForm_apply, Function.comp, ← map_mul f, trace_eq_of_algEquiv]

Depends on / 依赖: Function, Function.comp, discr_def, map_mul, simp_rw, traceForm_apply, traceMatrix_apply, trace_eq_of_algEquiv
-/
theorem discr_eq_discr_of_algEquiv [Fintype ι] (b : ι -> B) (f : B ≃ₐ[A] C) :
    Algebra.discr A b = Algebra.discr A (f ∘ b) := by
  rw [discr_def]; congr; ext
  simp_rw [traceMatrix_apply, traceForm_apply, Function.comp, ← map_mul f, trace_eq_of_algEquiv]

variable {ι' : Type*} [Fintype ι'] [Fintype ι] [DecidableEq ι']

section Basic

@[simp]
/--
theorem `discr_reindex` / 定理 `discr_reindex`

English:
theorem discr_reindex
  given: (b : Basis ι A B) (f : ι ≃ ι')
  statement: discr A (b ∘ ⇑f.symm) = discr A b
  proof: by
  rw [← Basis.coe_reindex]; rw [discr_def]; rw [traceMatrix_reindex]; rw [det_reindex_self]; rw [← discr_def]

中文:
定理 discr_reindex
  条件: (b : 基 ι A B) (f : ι ≃ ι')
  结论: discr A (b ∘ ⇑f.symm) = discr A b
  证明: by
  rw [← Basis.coe_reindex]; rw [discr_def]; rw [traceMatrix_reindex]; rw [det_reindex_self]; rw [← discr_def]

Depends on / 依赖: Basis.coe_reindex, coe_reindex, det_reindex_self, discr_def, traceMatrix_reindex
-/
theorem discr_reindex (b : Basis ι A B) (f : ι ≃ ι') : discr A (b ∘ ⇑f.symm) = discr A b := by
  rw [← Basis.coe_reindex]; rw [discr_def]; rw [traceMatrix_reindex]; rw [det_reindex_self]; rw [← discr_def]

/--
theorem `discr_zero_of_not_linearIndependent` / 定理 `discr_zero_of_not_linearIndependent`

English:
theorem discr_zero_of_not_linearIndependent
  statement: [IsDomain A] {b : ι -> B}
  proof: by
  obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.1 hli
  have : (traceMatrix A b) *ᵥ g = 0 := by
    ext i
    have : forall j, (trace A B) (b i * b j) * g j = (trace A B) (g j • b j * b i) := by
      intro j
      simp [mul_comm]
    simp only [mulVec, dotProduct, traceMatrix_apply, Pi.zero_apply, traceForm_apply, fun j =>
      this j, ← map_sum, ← sum_mul, hg, zero_mul, map_zero]
  by_contra h
  rw [discr_def] at h
  simp [Matrix.eq_zero_of_mulVec_eq_zero h this] at hi

中文:
定理 discr_zero_of_not_linearIndependent
  结论: [是整环 A] {b : ι -> B}
  证明: by
  obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.1 hli
  have : (traceMatrix A b) *ᵥ g = 0 := by
    ext i
    have : forall j, (trace A B) (b i * b j) * g j = (trace A B) (g j • b j * b i) := by
      intro j
      simp [mul_comm]
    simp only [mulVec, dotProduct, traceMatrix_apply, Pi.zero_apply, traceForm_apply, fun j =>
      this j, ← map_sum, ← sum_mul, hg, zero_mul, map_zero]
  by_contra h
  rw [discr_def] at h
  simp [Matrix.eq_zero_of_mulVec_eq_zero h this] at hi

Depends on / 依赖: Fintype, Fintype.not_linearIndependent_iff, Matrix, Matrix.eq_zero_of_mulVec_eq_zero, Pi.zero_apply, discr_def, dotProduct, eq_zero_of_mulVec_eq_zero, map_sum, map_zero, mulVec, mul_comm, not_linearIndependent_iff, sum_mul, traceForm_apply, traceMatrix, traceMatrix_apply, zero_apply, zero_mul
-/
theorem discr_zero_of_not_linearIndependent [IsDomain A] {b : ι -> B}
    (hli : ¬LinearIndependent A b) : discr A b = 0 := by
  obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.1 hli
  have : (traceMatrix A b) *ᵥ g = 0 := by
    ext i
    have : forall j, (trace A B) (b i * b j) * g j = (trace A B) (g j • b j * b i) := by
      intro j
      simp [mul_comm]
    simp only [mulVec, dotProduct, traceMatrix_apply, Pi.zero_apply, traceForm_apply, fun j =>
      this j, ← map_sum, ← sum_mul, hg, zero_mul, map_zero]
  by_contra h
  rw [discr_def] at h
  simp [Matrix.eq_zero_of_mulVec_eq_zero h this] at hi

variable {A}

/--
theorem `discr_of_matrix_vecMul` / 定理 `discr_of_matrix_vecMul`

English:
theorem discr_of_matrix_vecMul
  given: (b : ι -> B) (P : Matrix ι ι A)
  proof: by
  rw [discr_def]; rw [traceMatrix_of_matrix_vecMul]; rw [det_mul]; rw [det_mul]; rw [det_transpose]; rw [mul_comm]; rw [←
    mul_assoc]; rw [discr_def]; rw [pow_two]

中文:
定理 discr_of_matrix_vecMul
  条件: (b : ι -> B) (P : 矩阵 ι ι A)
  证明: by
  rw [discr_def]; rw [traceMatrix_of_matrix_vecMul]; rw [det_mul]; rw [det_mul]; rw [det_transpose]; rw [mul_comm]; rw [←
    mul_assoc]; rw [discr_def]; rw [pow_two]

Depends on / 依赖: det_mul, det_transpose, discr_def, mul_assoc, mul_comm, pow_two, traceMatrix_of_matrix_vecMul
-/
theorem discr_of_matrix_vecMul (b : ι -> B) (P : Matrix ι ι A) :
    discr A (b ᵥ* P.map (algebraMap A B)) = P.det ^ 2 * discr A b := by
  rw [discr_def]; rw [traceMatrix_of_matrix_vecMul]; rw [det_mul]; rw [det_mul]; rw [det_transpose]; rw [mul_comm]; rw [←
    mul_assoc]; rw [discr_def]; rw [pow_two]

/--
theorem `discr_of_matrix_mulVec` / 定理 `discr_of_matrix_mulVec`

English:
theorem discr_of_matrix_mulVec
  given: (b : ι -> B) (P : Matrix ι ι A)
  proof: by
  rw [discr_def]; rw [traceMatrix_of_matrix_mulVec]; rw [det_mul]; rw [det_mul]; rw [det_transpose]; rw [mul_comm]; rw [←
    mul_assoc]; rw [discr_def]; rw [pow_two]

中文:
定理 discr_of_matrix_mulVec
  条件: (b : ι -> B) (P : 矩阵 ι ι A)
  证明: by
  rw [discr_def]; rw [traceMatrix_of_matrix_mulVec]; rw [det_mul]; rw [det_mul]; rw [det_transpose]; rw [mul_comm]; rw [←
    mul_assoc]; rw [discr_def]; rw [pow_two]

Depends on / 依赖: det_mul, det_transpose, discr_def, mul_assoc, mul_comm, pow_two, traceMatrix_of_matrix_mulVec
-/
theorem discr_of_matrix_mulVec (b : ι -> B) (P : Matrix ι ι A) :
    discr A (P.map (algebraMap A B) *ᵥ b) = P.det ^ 2 * discr A b := by
  rw [discr_def]; rw [traceMatrix_of_matrix_mulVec]; rw [det_mul]; rw [det_mul]; rw [det_transpose]; rw [mul_comm]; rw [←
    mul_assoc]; rw [discr_def]; rw [pow_two]

end Basic

section Field

variable (K : Type u) {L : Type v} (E : Type z) [Field K] [Field L] [Field E]
variable [Algebra K L] [Algebra K E]
variable [Module.Finite K L] [IsAlgClosed E]

/--
theorem `discr_not_zero_of_basis` / 定理 `discr_not_zero_of_basis`

English:
theorem discr_not_zero_of_basis
  given: [Algebra.IsSeparable K L] (b : Basis ι K L)
  proof: by
  rw [discr_def]; rw [traceMatrix_of_basis]; rw [← LinearMap.BilinForm.nondegenerate_iff_det_ne_zero]
  exact traceForm_nondegenerate _ _

中文:
定理 discr_not_zero_of_basis
  条件: [代数.是可分 K L] (b : 基 ι K L)
  证明: by
  rw [discr_def]; rw [traceMatrix_of_basis]; rw [← LinearMap.BilinForm.nondegenerate_iff_det_ne_zero]
  exact traceForm_nondegenerate _ _

Depends on / 依赖: BilinForm, LinearMap, LinearMap.BilinForm.nondegenerate_iff_det_ne_zero, discr_def, nondegenerate_iff_det_ne_zero, traceForm_nondegenerate, traceMatrix_of_basis
-/
theorem discr_not_zero_of_basis [Algebra.IsSeparable K L] (b : Basis ι K L) :
    discr K b != 0 := by
  rw [discr_def]; rw [traceMatrix_of_basis]; rw [← LinearMap.BilinForm.nondegenerate_iff_det_ne_zero]
  exact traceForm_nondegenerate _ _

/--
theorem `discr_isUnit_of_basis` / 定理 `discr_isUnit_of_basis`

English:
theorem discr_isUnit_of_basis
  given: [Algebra.IsSeparable K L] (b : Basis ι K L)
  statement: IsUnit (discr K b)
  proof: IsUnit.mk0 _ (discr_not_zero_of_basis _ _)

中文:
定理 discr_isUnit_of_basis
  条件: [代数.是可分 K L] (b : 基 ι K L)
  结论: 是单位 (discr K b)
  证明: IsUnit.mk0 _ (discr_not_zero_of_basis _ _)

Depends on / 依赖: IsUnit, IsUnit.mk0, discr_not_zero_of_basis
-/
theorem discr_isUnit_of_basis [Algebra.IsSeparable K L] (b : Basis ι K L) : IsUnit (discr K b) :=
  IsUnit.mk0 _ (discr_not_zero_of_basis _ _)

variable (b : ι -> L) (pb : PowerBasis K L)

/--
theorem `discr_eq_det_embeddingsMatrixReindex_pow_two` / 定理 `discr_eq_det_embeddingsMatrixReindex_pow_two`

English:
theorem discr_eq_det_embeddingsMatrixReindex_pow_two
  proof: by
  rw [discr_def]; rw [RingHom.map_det]; rw [RingHom.mapMatrix_apply]; rw [traceMatrix_eq_embeddingsMatrixReindex_mul_trans]; rw [det_mul]; rw [det_transpose]; rw [pow_two]

中文:
定理 discr_eq_det_embeddingsMatrixReindex_pow_two
  证明: by
  rw [discr_def]; rw [RingHom.map_det]; rw [RingHom.mapMatrix_apply]; rw [traceMatrix_eq_embeddingsMatrixReindex_mul_trans]; rw [det_mul]; rw [det_transpose]; rw [pow_two]

Depends on / 依赖: RingHom, RingHom.mapMatrix_apply, RingHom.map_det, det_mul, det_transpose, discr_def, mapMatrix_apply, map_det, pow_two, traceMatrix_eq_embeddingsMatrixReindex_mul_trans
-/
theorem discr_eq_det_embeddingsMatrixReindex_pow_two
    [Algebra.IsSeparable K L] (e : ι ≃ (L ->ₐ[K] E)) :
    algebraMap K E (discr K b) = (embeddingsMatrixReindex K E b e).det ^ 2 := by
  rw [discr_def]; rw [RingHom.map_det]; rw [RingHom.mapMatrix_apply]; rw [traceMatrix_eq_embeddingsMatrixReindex_mul_trans]; rw [det_mul]; rw [det_transpose]; rw [pow_two]

/--
theorem `discr_powerBasis_eq_prod` / 定理 `discr_powerBasis_eq_prod`

English:
theorem discr_powerBasis_eq_prod
  given: (e : Fin pb.dim ≃ (L ->ₐ[K] E)) [Algebra.IsSeparable K L]
  proof: by
  rw [discr_eq_det_embeddingsMatrixReindex_pow_two K E pb.basis e]; rw [embeddingsMatrixReindex_eq_vandermonde]; rw [det_transpose]; rw [det_vandermonde]; rw [← prod_pow]
  congr; ext i
  rw [← prod_pow]

中文:
定理 discr_powerBasis_eq_prod
  条件: (e : 有限集 pb.dim ≃ (L ->ₐ[K] E)) [代数.是可分 K L]
  证明: by
  rw [discr_eq_det_embeddingsMatrixReindex_pow_two K E pb.basis e]; rw [embeddingsMatrixReindex_eq_vandermonde]; rw [det_transpose]; rw [det_vandermonde]; rw [← prod_pow]
  congr; ext i
  rw [← prod_pow]

Depends on / 依赖: det_transpose, det_vandermonde, discr_eq_det_embeddingsMatrixReindex_pow_two, embeddingsMatrixReindex_eq_vandermonde, pb.basis, prod_pow
-/
theorem discr_powerBasis_eq_prod (e : Fin pb.dim ≃ (L ->ₐ[K] E)) [Algebra.IsSeparable K L] :
    algebraMap K E (discr K pb.basis) =
      ∏ i : Fin pb.dim, ∏ j in Ioi i, (e j pb.gen - e i pb.gen) ^ 2 := by
  rw [discr_eq_det_embeddingsMatrixReindex_pow_two K E pb.basis e]; rw [embeddingsMatrixReindex_eq_vandermonde]; rw [det_transpose]; rw [det_vandermonde]; rw [← prod_pow]
  congr; ext i
  rw [← prod_pow]

/--
theorem `discr_powerBasis_eq_prod'` / 定理 `discr_powerBasis_eq_prod'`

English:
theorem discr_powerBasis_eq_prod'
  given: [Algebra.IsSeparable K L] (e : Fin pb.dim ≃ (L ->ₐ[K] E))
  proof: by
  rw [discr_powerBasis_eq_prod _ _ _ e]
  congr; ext i; congr; ext j
  ring

local notation "n" => finrank K L

中文:
定理 discr_powerBasis_eq_prod'
  条件: [代数.是可分 K L] (e : 有限集 pb.dim ≃ (L ->ₐ[K] E))
  证明: by
  rw [discr_powerBasis_eq_prod _ _ _ e]
  congr; ext i; congr; ext j
  ring

local notation "n" => finrank K L

Depends on / 依赖: discr_powerBasis_eq_prod
-/
theorem discr_powerBasis_eq_prod' [Algebra.IsSeparable K L] (e : Fin pb.dim ≃ (L ->ₐ[K] E)) :
    algebraMap K E (discr K pb.basis) =
      ∏ i : Fin pb.dim, ∏ j in Ioi i, -((e j pb.gen - e i pb.gen) * (e i pb.gen - e j pb.gen)) := by
  rw [discr_powerBasis_eq_prod _ _ _ e]
  congr; ext i; congr; ext j
  ring

local notation "n" => finrank K L

/--
theorem `discr_powerBasis_eq_prod''` / 定理 `discr_powerBasis_eq_prod''`

English:
theorem discr_powerBasis_eq_prod''
  given: [Algebra.IsSeparable K L] (e : Fin pb.dim ≃ (L ->ₐ[K] E))
  proof: by
  rw [discr_powerBasis_eq_prod' _ _ _ e]
  simp_rw [fun i j => neg_eq_neg_one_mul ((e j pb.gen - e i pb.gen) * (e i pb.gen - e j pb.gen)),
    prod_mul_distrib]
  congr
  simp only [prod_pow_eq_pow_sum, prod_const]
  congr
  rw [← @Nat.cast_inj Rat]; rw [Nat.cast_sum]
  have : forall x : Fin pb.dim, ↑x + 1 <= pb.dim := by simp [Fin.is_lt]
  simp_rw [Fin.card_Ioi, Nat.sub_sub, add_comm 1]
  simp only [Nat.cast_sub, this, Finset.card_fin, nsmul_eq_mul, sum_const, sum_sub_distrib,
    Nat.cast_add, Nat.cast_one, sum_add_distrib, mul_one]
  rw [← Nat.cast_sum]; rw [← @Finset.sum_range Nat _ pb.dim fun i => i]; rw [sum_range_id]
  have hn : n = pb.dim := by
    rw [← AlgHom.card K L E]; rw [← Fintype.card_fin pb.dim]
    -- FIXME: Without the `Fintype` namespace, why does it complain about `Finset.card_congr` being
    -- deprecated?
    exact Fintype.card_congr e.symm
  have h₂ : 2 ∣ pb.dim * (pb.dim - 1) := pb.dim.even_mul_pred_self.two_dvd
  have hne : ((2 : Nat) : Rat) != 0 := by simp
  have hle : 1 <= pb.dim := by
    rw [← hn]; rw [Nat.one_le_iff_ne_zero]; rw [← zero_lt_iff]; rw [Module.finrank_pos_iff]
    infer_instance
  rw [hn]; rw [Nat.cast_div h₂ hne]; rw [Nat.cast_mul]; rw [Nat.cast_sub hle]
  ring

中文:
定理 discr_powerBasis_eq_prod''
  条件: [代数.是可分 K L] (e : 有限集 pb.dim ≃ (L ->ₐ[K] E))
  证明: by
  rw [discr_powerBasis_eq_prod' _ _ _ e]
  simp_rw [fun i j => neg_eq_neg_one_mul ((e j pb.gen - e i pb.gen) * (e i pb.gen - e j pb.gen)),
    prod_mul_distrib]
  congr
  simp only [prod_pow_eq_pow_sum, prod_const]
  congr
  rw [← @Nat.cast_inj Rat]; rw [Nat.cast_sum]
  have : forall x : Fin pb.dim, ↑x + 1 <= pb.dim := by simp [Fin.is_lt]
  simp_rw [Fin.card_Ioi, Nat.sub_sub, add_comm 1]
  simp only [Nat.cast_sub, this, Finset.card_fin, nsmul_eq_mul, sum_const, sum_sub_distrib,
    Nat.cast_add, Nat.cast_one, sum_add_distrib, mul_one]
  rw [← Nat.cast_sum]; rw [← @Finset.sum_range Nat _ pb.dim fun i => i]; rw [sum_range_id]
  have hn : n = pb.dim := by
    rw [← AlgHom.card K L E]; rw [← Fintype.card_fin pb.dim]
    -- FIXME: Without the `Fintype` namespace, why does it complain about `Finset.card_congr` being
    -- deprecated?
    exact Fintype.card_congr e.symm
  have h₂ : 2 ∣ pb.dim * (pb.dim - 1) := pb.dim.even_mul_pred_self.two_dvd
  have hne : ((2 : Nat) : Rat) != 0 := by simp
  have hle : 1 <= pb.dim := by
    rw [← hn]; rw [Nat.one_le_iff_ne_zero]; rw [← zero_lt_iff]; rw [Module.finrank_pos_iff]
    infer_instance
  rw [hn]; rw [Nat.cast_div h₂ hne]; rw [Nat.cast_mul]; rw [Nat.cast_sub hle]
  ring

Depends on / 依赖: Fin.card_Ioi, Fin.is_lt, Finset, Finset.card_fin, Nat.cast_add, Nat.cast_inj, Nat.cast_one, Nat.cast_sub, Nat.cast_sum, Nat.sub_sub, add_comm, card_Ioi, card_fin, cast_add, cast_inj, cast_one, cast_sub, cast_sum, discr_powerBasis_eq_prod, is_lt
-/
theorem discr_powerBasis_eq_prod'' [Algebra.IsSeparable K L] (e : Fin pb.dim ≃ (L ->ₐ[K] E)) :
    algebraMap K E (discr K pb.basis) =
      (-1) ^ (n * (n - 1) / 2) *
        ∏ i : Fin pb.dim, ∏ j in Ioi i, (e j pb.gen - e i pb.gen) * (e i pb.gen - e j pb.gen) := by
  rw [discr_powerBasis_eq_prod' _ _ _ e]
  simp_rw [fun i j => neg_eq_neg_one_mul ((e j pb.gen - e i pb.gen) * (e i pb.gen - e j pb.gen)),
    prod_mul_distrib]
  congr
  simp only [prod_pow_eq_pow_sum, prod_const]
  congr
  rw [← @Nat.cast_inj Rat]; rw [Nat.cast_sum]
  have : forall x : Fin pb.dim, ↑x + 1 <= pb.dim := by simp [Fin.is_lt]
  simp_rw [Fin.card_Ioi, Nat.sub_sub, add_comm 1]
  simp only [Nat.cast_sub, this, Finset.card_fin, nsmul_eq_mul, sum_const, sum_sub_distrib,
    Nat.cast_add, Nat.cast_one, sum_add_distrib, mul_one]
  rw [← Nat.cast_sum]; rw [← @Finset.sum_range Nat _ pb.dim fun i => i]; rw [sum_range_id]
  have hn : n = pb.dim := by
    rw [← AlgHom.card K L E]; rw [← Fintype.card_fin pb.dim]
    -- FIXME: Without the `Fintype` namespace, why does it complain about `Finset.card_congr` being
    -- deprecated?
    exact Fintype.card_congr e.symm
  have h₂ : 2 ∣ pb.dim * (pb.dim - 1) := pb.dim.even_mul_pred_self.two_dvd
  have hne : ((2 : Nat) : Rat) != 0 := by simp
  have hle : 1 <= pb.dim := by
    rw [← hn]; rw [Nat.one_le_iff_ne_zero]; rw [← zero_lt_iff]; rw [Module.finrank_pos_iff]
    infer_instance
  rw [hn]; rw [Nat.cast_div h₂ hne]; rw [Nat.cast_mul]; rw [Nat.cast_sub hle]
  ring

/--
theorem `discr_powerBasis_eq_norm` / 定理 `discr_powerBasis_eq_norm`

English:
theorem discr_powerBasis_eq_norm
  given: [Algebra.IsSeparable K L]
  proof: by
  let E := AlgebraicClosure L
  let := fun a b : E => Classical.propDecidable (Eq a b)
  have e : Fin pb.dim ≃ (L ->ₐ[K] E) := by
    refine equivOfCardEq ?_
    rw [Fintype.card_fin]; rw [AlgHom.card]
    exact (PowerBasis.finrank pb).symm
  have hnodup : ((minpoly K pb.gen).aroots E).Nodup :=
    nodup_roots (Separable.map (Algebra.IsSeparable.isSeparable K pb.gen))
  have hroots : forall σ : L ->ₐ[K] E, σ pb.gen in (minpoly K pb.gen).aroots E := by
    intro σ
    rw [mem_roots]; rw [IsRoot.def]; rw [eval_map_algebraMap]; rw [aeval_algHom_apply]
    repeat' simp [minpoly.ne_zero pb.isIntegral_gen]
  apply (algebraMap K E).injective
  rw [map_mul]; rw [map_pow]; rw [map_neg]; rw [map_one]; rw [discr_powerBasis_eq_prod'' _ _ _ e]
  congr
  rw [norm_eq_prod_embeddings]; rw [prod_prod_Ioi_mul_eq_prod_prod_off_diag]
  conv_rhs =>
    congr
    rfl
    ext σ
    rw [← aeval_algHom_apply]; rw [← eval_map_algebraMap]; rw [← derivative_map]; rw [(IsAlgClosed.splits _).eval_root_derivative ((minpoly.monic pb.isIntegral_gen).map _)
      (hroots σ)]; rw [← Finset.prod_mk _ (hnodup.erase _)]
  rw [Finset.prod_sigma']; rw [Finset.prod_sigma']
  refine prod_bij' (fun i _ => ⟨e i.2, e i.1 pb.gen⟩)
    (fun σ hσ => ⟨e.symm (PowerBasis.lift pb σ.2 ?_), e.symm σ.1⟩) ?_ ?_ ?_ ?_ (fun i _ => by simp)
    <;> simp only [mem_sigma, mem_univ, Finset.mem_mk, hnodup.mem_erase_iff, IsRoot.def,
      mem_roots', mem_singleton, true_and, mem_compl, Sigma.forall, Equiv.apply_symm_apply,
      PowerBasis.lift_gen, implies_true, Equiv.symm_apply_apply,
      Sigma.ext_iff, Equiv.symm_apply_eq, heq_eq_eq, and_true] at *
  · simpa only [aeval_def, eval₂_eq_eval_map] using hσ.2.2
· exact fun a b hba => ⟨fun h => hba e.injective pb.algHom_ext h.symm, hroots _⟩
  · rintro a b hba ha
    rw [ha]; rw [PowerBasis.lift_gen] at hba
    exact hba.1 rfl
· exact fun a b _ => pb.algHom_ext pb.lift_gen _ _

中文:
定理 discr_powerBasis_eq_norm
  条件: [代数.是可分 K L]
  证明: by
  let E := AlgebraicClosure L
  let := fun a b : E => Classical.propDecidable (Eq a b)
  have e : Fin pb.dim ≃ (L ->ₐ[K] E) := by
    refine equivOfCardEq ?_
    rw [Fintype.card_fin]; rw [AlgHom.card]
    exact (PowerBasis.finrank pb).symm
  have hnodup : ((minpoly K pb.gen).aroots E).Nodup :=
    nodup_roots (Separable.map (Algebra.IsSeparable.isSeparable K pb.gen))
  have hroots : forall σ : L ->ₐ[K] E, σ pb.gen in (minpoly K pb.gen).aroots E := by
    intro σ
    rw [mem_roots]; rw [IsRoot.def]; rw [eval_map_algebraMap]; rw [aeval_algHom_apply]
    repeat' simp [minpoly.ne_zero pb.isIntegral_gen]
  apply (algebraMap K E).injective
  rw [map_mul]; rw [map_pow]; rw [map_neg]; rw [map_one]; rw [discr_powerBasis_eq_prod'' _ _ _ e]
  congr
  rw [norm_eq_prod_embeddings]; rw [prod_prod_Ioi_mul_eq_prod_prod_off_diag]
  conv_rhs =>
    congr
    rfl
    ext σ
    rw [← aeval_algHom_apply]; rw [← eval_map_algebraMap]; rw [← derivative_map]; rw [(IsAlgClosed.splits _).eval_root_derivative ((minpoly.monic pb.isIntegral_gen).map _)
      (hroots σ)]; rw [← Finset.prod_mk _ (hnodup.erase _)]
  rw [Finset.prod_sigma']; rw [Finset.prod_sigma']
  refine prod_bij' (fun i _ => ⟨e i.2, e i.1 pb.gen⟩)
    (fun σ hσ => ⟨e.symm (PowerBasis.lift pb σ.2 ?_), e.symm σ.1⟩) ?_ ?_ ?_ ?_ (fun i _ => by simp)
    <;> simp only [mem_sigma, mem_univ, Finset.mem_mk, hnodup.mem_erase_iff, IsRoot.def,
      mem_roots', mem_singleton, true_and, mem_compl, Sigma.forall, Equiv.apply_symm_apply,
      PowerBasis.lift_gen, implies_true, Equiv.symm_apply_apply,
      Sigma.ext_iff, Equiv.symm_apply_eq, heq_eq_eq, and_true] at *
  · simpa only [aeval_def, eval₂_eq_eval_map] using hσ.2.2
· exact fun a b hba => ⟨fun h => hba e.injective pb.algHom_ext h.symm, hroots _⟩
  · rintro a b hba ha
    rw [ha]; rw [PowerBasis.lift_gen] at hba
    exact hba.1 rfl
· exact fun a b _ => pb.algHom_ext pb.lift_gen _ _

Depends on / 依赖: AlgHom, AlgHom.card, Algebra, Algebra.IsSeparable.isSeparable, AlgebraicClosure, Classical, Classical.propDecidable, Fintype, Fintype.card_fin, IsRoot, IsRoot.def, IsSeparable, PowerBasis, PowerBasis.finrank, Separable, Separable.map, aroots, card_fin, equivOfCardEq, eval_map_algebraMap
-/
theorem discr_powerBasis_eq_norm [Algebra.IsSeparable K L] :
    discr K pb.basis =
      (-1) ^ (n * (n - 1) / 2) *
      norm K (aeval pb.gen (minpoly K pb.gen).derivative) := by
  let E := AlgebraicClosure L
  let := fun a b : E => Classical.propDecidable (Eq a b)
  have e : Fin pb.dim ≃ (L ->ₐ[K] E) := by
    refine equivOfCardEq ?_
    rw [Fintype.card_fin]; rw [AlgHom.card]
    exact (PowerBasis.finrank pb).symm
  have hnodup : ((minpoly K pb.gen).aroots E).Nodup :=
    nodup_roots (Separable.map (Algebra.IsSeparable.isSeparable K pb.gen))
  have hroots : forall σ : L ->ₐ[K] E, σ pb.gen in (minpoly K pb.gen).aroots E := by
    intro σ
    rw [mem_roots]; rw [IsRoot.def]; rw [eval_map_algebraMap]; rw [aeval_algHom_apply]
    repeat' simp [minpoly.ne_zero pb.isIntegral_gen]
  apply (algebraMap K E).injective
  rw [map_mul]; rw [map_pow]; rw [map_neg]; rw [map_one]; rw [discr_powerBasis_eq_prod'' _ _ _ e]
  congr
  rw [norm_eq_prod_embeddings]; rw [prod_prod_Ioi_mul_eq_prod_prod_off_diag]
  conv_rhs =>
    congr
    rfl
    ext σ
    rw [← aeval_algHom_apply]; rw [← eval_map_algebraMap]; rw [← derivative_map]; rw [(IsAlgClosed.splits _).eval_root_derivative ((minpoly.monic pb.isIntegral_gen).map _)
      (hroots σ)]; rw [← Finset.prod_mk _ (hnodup.erase _)]
  rw [Finset.prod_sigma']; rw [Finset.prod_sigma']
  refine prod_bij' (fun i _ => ⟨e i.2, e i.1 pb.gen⟩)
    (fun σ hσ => ⟨e.symm (PowerBasis.lift pb σ.2 ?_), e.symm σ.1⟩) ?_ ?_ ?_ ?_ (fun i _ => by simp)
    <;> simp only [mem_sigma, mem_univ, Finset.mem_mk, hnodup.mem_erase_iff, IsRoot.def,
      mem_roots', mem_singleton, true_and, mem_compl, Sigma.forall, Equiv.apply_symm_apply,
      PowerBasis.lift_gen, implies_true, Equiv.symm_apply_apply,
      Sigma.ext_iff, Equiv.symm_apply_eq, heq_eq_eq, and_true] at *
  · simpa only [aeval_def, eval₂_eq_eval_map] using hσ.2.2
· exact fun a b hba => ⟨fun h => hba e.injective pb.algHom_ext h.symm, hroots _⟩
  · rintro a b hba ha
    rw [ha]; rw [PowerBasis.lift_gen] at hba
    exact hba.1 rfl
· exact fun a b _ => pb.algHom_ext pb.lift_gen _ _

section Integral

variable {R : Type z} [CommRing R] [Algebra R K] [Algebra R L] [IsScalarTower R K L]

/--
theorem `discr_isIntegral` / 定理 `discr_isIntegral`

English:
theorem discr_isIntegral
  given: {b : ι -> L} (h : forall i, IsIntegral R (b i))
  statement: IsIntegral R (discr K b)
  proof: by
  rw [discr_def]
  exact IsIntegral.det fun i j => isIntegral_trace ((h i).mul (h j))

中文:
定理 discr_is整数egral
  条件: {b : ι -> L} (h : 对任意 i, 是整 R (b i))
  结论: 是整 R (discr K b)
  证明: by
  rw [discr_def]
  exact IsIntegral.det fun i j => isIntegral_trace ((h i).mul (h j))

Depends on / 依赖: IsIntegral, IsIntegral.det, discr_def, isIntegral_trace
-/
theorem discr_isIntegral {b : ι -> L} (h : forall i, IsIntegral R (b i)) : IsIntegral R (discr K b) := by
  rw [discr_def]
  exact IsIntegral.det fun i j => isIntegral_trace ((h i).mul (h j))

/--
theorem `discr_mul_isIntegral_mem_adjoin` / 定理 `discr_mul_isIntegral_mem_adjoin`

English:
theorem discr_mul_isIntegral_mem_adjoin
  statement: [Algebra.IsSeparable K L] [IsIntegrallyClosed R]
  proof: by
  have hinv : IsUnit (traceMatrix K B.basis).det := by
    simpa [← discr_def] using discr_isUnit_of_basis _ B.basis
  have H :
    (traceMatrix K B.basis).det • (traceMatrix K B.basis) *ᵥ (B.basis.equivFun z) =
      (traceMatrix K B.basis).det • fun i => trace K L (z * B.basis i) := by
    congr; exact traceMatrix_of_basis_mulVec _ _
  have cramer := mulVec_cramer (traceMatrix K B.basis) fun i => trace K L (z * B.basis i)
  suffices forall i, ((traceMatrix K B.basis).det • B.basis.equivFun z) i in (⊥ : Subalgebra R K) by
    rw [← B.basis.sum_repr z]; rw [Finset.smul_sum]
    refine Subalgebra.sum_mem _ fun i _ => ?_
    replace this := this i
    rw [← discr_def]; rw [Pi.smul_apply]; rw [mem_bot] at this
    obtain ⟨r, hr⟩ := this
    rw [Basis.equivFun_apply] at hr
    rw [← smul_assoc]; rw [← hr]; rw [algebraMap_smul]
    refine Subalgebra.smul_mem _ ?_ _
    rw [B.basis_eq_pow i]
    exact Subalgebra.pow_mem _ (subset_adjoin (Set.mem_singleton _)) _
  intro i
  rw [← H]; rw [← mulVec_smul] at cramer
  replace cramer := congr_arg (mulVec (traceMatrix K B.basis)⁻¹) cramer
  rw [mulVec_mulVec]; rw [nonsing_inv_mul _ hinv]; rw [mulVec_mulVec]; rw [nonsing_inv_mul _ hinv]; rw [one_mulVec]; rw [one_mulVec] at cramer
  rw [← congr_fun cramer i]; rw [cramer_apply]; rw [det_apply]
  refine
    Subalgebra.sum_mem _ fun σ _ => Subalgebra.zsmul_mem _ (Subalgebra.prod_mem _ fun j _ => ?_) _
  by_cases hji : j = i
  · simp only [updateCol_apply, hji, PowerBasis.coe_basis]
    exact mem_bot.2 (IsIntegrallyClosed.isIntegral_iff.1 <| isIntegral_trace (hz.mul <| hint.pow _))
  · simp only [updateCol_apply, hji, PowerBasis.coe_basis]
    exact mem_bot.2
      (IsIntegrallyClosed.isIntegral_iff.1 <| isIntegral_trace <| (hint.pow _).mul (hint.pow _))

中文:
定理 discr_mul_is整数egral_mem_adjoin
  结论: [代数.是可分 K L] [是整闭 R]
  证明: by
  have hinv : IsUnit (traceMatrix K B.basis).det := by
    simpa [← discr_def] using discr_isUnit_of_basis _ B.basis
  have H :
    (traceMatrix K B.basis).det • (traceMatrix K B.basis) *ᵥ (B.basis.equivFun z) =
      (traceMatrix K B.basis).det • fun i => trace K L (z * B.basis i) := by
    congr; exact traceMatrix_of_basis_mulVec _ _
  have cramer := mulVec_cramer (traceMatrix K B.basis) fun i => trace K L (z * B.basis i)
  suffices forall i, ((traceMatrix K B.basis).det • B.basis.equivFun z) i in (⊥ : Subalgebra R K) by
    rw [← B.basis.sum_repr z]; rw [Finset.smul_sum]
    refine Subalgebra.sum_mem _ fun i _ => ?_
    replace this := this i
    rw [← discr_def]; rw [Pi.smul_apply]; rw [mem_bot] at this
    obtain ⟨r, hr⟩ := this
    rw [Basis.equivFun_apply] at hr
    rw [← smul_assoc]; rw [← hr]; rw [algebraMap_smul]
    refine Subalgebra.smul_mem _ ?_ _
    rw [B.basis_eq_pow i]
    exact Subalgebra.pow_mem _ (subset_adjoin (Set.mem_singleton _)) _
  intro i
  rw [← H]; rw [← mulVec_smul] at cramer
  replace cramer := congr_arg (mulVec (traceMatrix K B.basis)⁻¹) cramer
  rw [mulVec_mulVec]; rw [nonsing_inv_mul _ hinv]; rw [mulVec_mulVec]; rw [nonsing_inv_mul _ hinv]; rw [one_mulVec]; rw [one_mulVec] at cramer
  rw [← congr_fun cramer i]; rw [cramer_apply]; rw [det_apply]
  refine
    Subalgebra.sum_mem _ fun σ _ => Subalgebra.zsmul_mem _ (Subalgebra.prod_mem _ fun j _ => ?_) _
  by_cases hji : j = i
  · simp only [updateCol_apply, hji, PowerBasis.coe_basis]
    exact mem_bot.2 (IsIntegrallyClosed.isIntegral_iff.1 <| isIntegral_trace (hz.mul <| hint.pow _))
  · simp only [updateCol_apply, hji, PowerBasis.coe_basis]
    exact mem_bot.2
      (IsIntegrallyClosed.isIntegral_iff.1 <| isIntegral_trace <| (hint.pow _).mul (hint.pow _))

Depends on / 依赖: B.basis, B.basis.equivFun, IsUnit, Subalgebra, cramer, discr_def, discr_isUnit_of_basis, equivFun, mulVec_cramer, traceMatrix, traceMatrix_of_basis_mulVec
-/
theorem discr_mul_isIntegral_mem_adjoin [Algebra.IsSeparable K L] [IsIntegrallyClosed R]
    [IsFractionRing R K] {B : PowerBasis K L} (hint : IsIntegral R B.gen) {z : L}
    (hz : IsIntegral R z) : discr K B.basis • z in adjoin R ({B.gen} : Set L) := by
  have hinv : IsUnit (traceMatrix K B.basis).det := by
    simpa [← discr_def] using discr_isUnit_of_basis _ B.basis
  have H :
    (traceMatrix K B.basis).det • (traceMatrix K B.basis) *ᵥ (B.basis.equivFun z) =
      (traceMatrix K B.basis).det • fun i => trace K L (z * B.basis i) := by
    congr; exact traceMatrix_of_basis_mulVec _ _
  have cramer := mulVec_cramer (traceMatrix K B.basis) fun i => trace K L (z * B.basis i)
  suffices forall i, ((traceMatrix K B.basis).det • B.basis.equivFun z) i in (⊥ : Subalgebra R K) by
    rw [← B.basis.sum_repr z]; rw [Finset.smul_sum]
    refine Subalgebra.sum_mem _ fun i _ => ?_
    replace this := this i
    rw [← discr_def]; rw [Pi.smul_apply]; rw [mem_bot] at this
    obtain ⟨r, hr⟩ := this
    rw [Basis.equivFun_apply] at hr
    rw [← smul_assoc]; rw [← hr]; rw [algebraMap_smul]
    refine Subalgebra.smul_mem _ ?_ _
    rw [B.basis_eq_pow i]
    exact Subalgebra.pow_mem _ (subset_adjoin (Set.mem_singleton _)) _
  intro i
  rw [← H]; rw [← mulVec_smul] at cramer
  replace cramer := congr_arg (mulVec (traceMatrix K B.basis)⁻¹) cramer
  rw [mulVec_mulVec]; rw [nonsing_inv_mul _ hinv]; rw [mulVec_mulVec]; rw [nonsing_inv_mul _ hinv]; rw [one_mulVec]; rw [one_mulVec] at cramer
  rw [← congr_fun cramer i]; rw [cramer_apply]; rw [det_apply]
  refine
    Subalgebra.sum_mem _ fun σ _ => Subalgebra.zsmul_mem _ (Subalgebra.prod_mem _ fun j _ => ?_) _
  by_cases hji : j = i
  · simp only [updateCol_apply, hji, PowerBasis.coe_basis]
    exact mem_bot.2 (IsIntegrallyClosed.isIntegral_iff.1 <| isIntegral_trace (hz.mul <| hint.pow _))
  · simp only [updateCol_apply, hji, PowerBasis.coe_basis]
    exact mem_bot.2
      (IsIntegrallyClosed.isIntegral_iff.1 <| isIntegral_trace <| (hint.pow _).mul (hint.pow _))

end Integral

end Field

section Int

/--
theorem `discr_eq_discr` / 定理 `discr_eq_discr`

English:
theorem discr_eq_discr
  given: (b : Basis ι Int A) (b' : Basis ι Int A)
  proof: by
  convert! Algebra.discr_of_matrix_vecMul b' (b'.toMatrix b)
  · rw [Basis.toMatrix_map_vecMul]
  · suffices IsUnit (b'.toMatrix b).det by
      rw [Int.isUnit_iff]; rw [← sq_eq_one_iff] at this
      rw [this]; rw [one_mul]
    rw [← LinearMap.toMatrix_id_eq_basis_toMatrix b b']
    exact LinearEquiv.isUnit_det (LinearEquiv.refl Int A) b b'

中文:
定理 discr_eq_discr
  条件: (b : 基 ι 整数 A) (b' : 基 ι 整数 A)
  证明: by
  convert! Algebra.discr_of_matrix_vecMul b' (b'.toMatrix b)
  · rw [Basis.toMatrix_map_vecMul]
  · suffices IsUnit (b'.toMatrix b).det by
      rw [Int.isUnit_iff]; rw [← sq_eq_one_iff] at this
      rw [this]; rw [one_mul]
    rw [← LinearMap.toMatrix_id_eq_basis_toMatrix b b']
    exact LinearEquiv.isUnit_det (LinearEquiv.refl Int A) b b'

Depends on / 依赖: Algebra, Algebra.discr_of_matrix_vecMul, Basis.toMatrix_map_vecMul, Int.isUnit_iff, IsUnit, LinearEquiv, LinearEquiv.isUnit_det, LinearEquiv.refl, LinearMap, LinearMap.toMatrix_id_eq_basis_toMatrix, convert, discr_of_matrix_vecMul, isUnit_det, isUnit_iff, one_mul, sq_eq_one_iff, toMatrix, toMatrix_id_eq_basis_toMatrix, toMatrix_map_vecMul
-/
theorem discr_eq_discr (b : Basis ι Int A) (b' : Basis ι Int A) :
    Algebra.discr Int b = Algebra.discr Int b' := by
  convert! Algebra.discr_of_matrix_vecMul b' (b'.toMatrix b)
  · rw [Basis.toMatrix_map_vecMul]
  · suffices IsUnit (b'.toMatrix b).det by
      rw [Int.isUnit_iff]; rw [← sq_eq_one_iff] at this
      rw [this]; rw [one_mul]
    rw [← LinearMap.toMatrix_id_eq_basis_toMatrix b b']
    exact LinearEquiv.isUnit_det (LinearEquiv.refl Int A) b b'

end Int

end Discr

end Algebra
