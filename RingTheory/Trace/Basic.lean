/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Minpoly.MinpolyDiv
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.RingTheory.Trace.Defs

/-!
# Trace for (finite) ring extensions.

Suppose we have an `R`-algebra `S` with a finite basis. For each `s : S`,
the trace of the linear map given by multiplying by `s` gives information about
the roots of the minimal polynomial of `s` over `R`.

## Main definitions

* `Algebra.embeddingsMatrix A C b : Matrix κ (B →ₐ[A] C) C` is the matrix whose
  `(i, σ)` coefficient is `σ (b i)`.
* `Algebra.embeddingsMatrixReindex A C b e : Matrix κ κ C` is the matrix whose `(i, j)`
  coefficient is `σⱼ (b i)`, where `σⱼ : B →ₐ[A] C` is the embedding corresponding to `j : κ`
  given by a bijection `e : κ ≃ (B →ₐ[A] C)`.
* `Module.Basis.traceDual`: The dual basis of a basis under the trace form in a finite separable
  extension.

## Main results

* `trace_eq_sum_embeddings`: the trace of `x : K(x)` is the sum of all embeddings of `x` into an
  algebraically closed field
* `traceForm_nondegenerate`: the trace form over a separable extension is a nondegenerate
  bilinear form
* `Module.Basis.traceDual_powerBasis_eq`: The dual basis of a power basis `{1, x, x²...}` under the
  trace form is `aᵢ / f'(x)`, with `f` being the minpoly of `x` and `f / (X - x) = ∑ aᵢxⁱ`.

## References

* https://en.wikipedia.org/wiki/Field_trace

-/

@[expose] public section

universe u v w z

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T]
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable {ι κ : Type w}

open Module

open LinearMap (BilinForm)
open LinearMap

open Matrix

open scoped Matrix

/--
theorem `Algebra.traceForm_toMatrix_powerBasis` / 定理 `Algebra.traceForm_toMatrix_powerBasis`

English:
theorem Algebra.traceForm_toMatrix_powerBasis
  given: (h : PowerBasis R S)
  proof: by
  ext; rw [traceForm_toMatrix, of_apply, pow_add, h.basis_eq_pow, h.basis_eq_pow]

中文:
定理 Algebra.traceForm_toMatrix_powerBasis
  条件: (h : PowerBasis R S)
  证明: by
  ext; rw [traceForm_toMatrix, of_apply, pow_add, h.basis_eq_pow, h.basis_eq_pow]

Depends on / 依赖: basis_eq_pow, h.basis_eq_pow, of_apply, pow_add, traceForm_toMatrix
-/
theorem Algebra.traceForm_toMatrix_powerBasis (h : PowerBasis R S) :
    (traceForm R S).toMatrix h.basis = of fun i j => trace R S (h.gen ^ (i.1 + j.1)) := by
  ext; rw [traceForm_toMatrix, of_apply, pow_add, h.basis_eq_pow, h.basis_eq_pow]

section EqSumRoots

open Algebra Polynomial

variable {F : Type*} [Field F]
variable [Algebra K S] [Algebra K F]

/--
theorem `PowerBasis.trace_gen_eq_nextCoeff_minpoly` / 定理 `PowerBasis.trace_gen_eq_nextCoeff_minpoly`

English:
theorem PowerBasis.trace_gen_eq_nextCoeff_minpoly
  given: [Nontrivial S] (pb : PowerBasis K S)
  proof: by
  have d_pos : 0 < pb.dim := PowerBasis.dim_pos pb
  have d_pos' : 0 < (minpoly K pb.gen).natDegree := by simpa
  have : Nonempty (Fin pb.dim) := ⟨⟨0, d_pos⟩⟩
  rw [trace_eq_matrix_trace pb.basis]; rw [trace_eq_neg_charpoly_coeff]; rw [charpoly_leftMulMatrix]; rw [←
    pb.natDegree_minpoly]; rw 

中文:
定理 PowerBasis.trace_gen_eq_nextCoeff_minpoly
  条件: [Nontrivial S] (pb : PowerBasis K S)
  证明: by
  have d_pos : 0 < pb.dim := PowerBasis.dim_pos pb
  have d_pos' : 0 < (minpoly K pb.gen).natDegree := by simpa
  have : Nonempty (Fin pb.dim) := ⟨⟨0, d_pos⟩⟩
  rw [trace_eq_matrix_trace pb.basis]; rw [trace_eq_neg_charpoly_coeff]; rw [charpoly_leftMulMatrix]; rw [←
    pb.natDegree_minpoly]; rw 

Depends on / 依赖: Fintype, Fintype.card_fin, Nonempty, PowerBasis, PowerBasis.dim_pos, card_fin, charpoly_leftMulMatrix, d_pos, dim_pos, minpoly, natDegree, natDegree_minpoly, nextCoeff_of_natDegree_pos, pb.basis, pb.dim, pb.gen, pb.natDegree_minpoly, trace_eq_matrix_trace, trace_eq_neg_charpoly_coeff
-/
theorem PowerBasis.trace_gen_eq_nextCoeff_minpoly [Nontrivial S] (pb : PowerBasis K S) :
    Algebra.trace K S pb.gen = -(minpoly K pb.gen).nextCoeff := by
  have d_pos : 0 < pb.dim := PowerBasis.dim_pos pb
  have d_pos' : 0 < (minpoly K pb.gen).natDegree := by simpa
  have : Nonempty (Fin pb.dim) := ⟨⟨0, d_pos⟩⟩
  rw [trace_eq_matrix_trace pb.basis]; rw [trace_eq_neg_charpoly_coeff]; rw [charpoly_leftMulMatrix]; rw [←
    pb.natDegree_minpoly]; rw [Fintype.card_fin]; rw [← nextCoeff_of_natDegree_pos d_pos']

/--
theorem `PowerBasis.trace_gen_eq_sum_roots` / 定理 `PowerBasis.trace_gen_eq_sum_roots`

English:
theorem PowerBasis.trace_gen_eq_sum_roots
  statement: [Nontrivial S] (pb : PowerBasis K S)
  proof: by
  rw [PowerBasis.trace_gen_eq_nextCoeff_minpoly]; rw [map_neg]; rw [← nextCoeff_map_eq]; rw [hf.nextCoeff_eq_neg_sum_roots_of_monic
      ((minpoly.monic (PowerBasis.isIntegral_gen _)).map _)]; rw [neg_neg]

中文:
定理 PowerBasis.trace_gen_eq_sum_roots
  结论: [Nontrivial S] (pb : PowerBasis K S)
  证明: by
  rw [PowerBasis.trace_gen_eq_nextCoeff_minpoly]; rw [map_neg]; rw [← nextCoeff_map_eq]; rw [hf.nextCoeff_eq_neg_sum_roots_of_monic
      ((minpoly.monic (PowerBasis.isIntegral_gen _)).map _)]; rw [neg_neg]

Depends on / 依赖: PowerBasis, PowerBasis.isIntegral_gen, PowerBasis.trace_gen_eq_nextCoeff_minpoly, hf.nextCoeff_eq_neg_sum_roots_of_monic, isIntegral_gen, map_neg, minpoly, minpoly.monic, neg_neg, nextCoeff_eq_neg_sum_roots_of_monic, nextCoeff_map_eq, trace_gen_eq_nextCoeff_minpoly
-/
theorem PowerBasis.trace_gen_eq_sum_roots [Nontrivial S] (pb : PowerBasis K S)
    (hf : ((minpoly K pb.gen).map (algebraMap K F)).Splits) :
    algebraMap K F (trace K S pb.gen) = ((minpoly K pb.gen).aroots F).sum := by
  rw [PowerBasis.trace_gen_eq_nextCoeff_minpoly]; rw [map_neg]; rw [← nextCoeff_map_eq]; rw [hf.nextCoeff_eq_neg_sum_roots_of_monic
      ((minpoly.monic (PowerBasis.isIntegral_gen _)).map _)]; rw [neg_neg]

namespace IntermediateField.AdjoinSimple

open IntermediateField

/--
theorem `trace_gen_eq_zero` / 定理 `trace_gen_eq_zero`

English:
theorem trace_gen_eq_zero
  given: {x : L} (hx : ¬IsIntegral K x)
  proof: by
  rw [trace_eq_zero_of_not_exists_basis]; rw [LinearMap.zero_apply]
  contrapose hx
  obtain ⟨s, ⟨b⟩⟩ := hx
  refine .of_mem_of_fg K⟮x⟯.toSubalgebra ?_ x ?_
  · exact (Submodule.fg_iff_finiteDimensional _).mpr (b.finiteDimensional_of_finite)
  · exact subset_adjoin K _ (Set.mem_singleton x)

中文:
定理 trace_gen_eq_zero
  条件: {x : L} (hx : ¬Is整数egral K x)
  证明: by
  rw [trace_eq_zero_of_not_exists_basis]; rw [LinearMap.zero_apply]
  contrapose hx
  obtain ⟨s, ⟨b⟩⟩ := hx
  refine .of_mem_of_fg K⟮x⟯.toSubalgebra ?_ x ?_
  · exact (Submodule.fg_iff_finiteDimensional _).mpr (b.finiteDimensional_of_finite)
  · exact subset_adjoin K _ (Set.mem_singleton x)

Depends on / 依赖: LinearMap, LinearMap.zero_apply, Set.mem_singleton, Submodule, Submodule.fg_iff_finiteDimensional, b.finiteDimensional_of_finite, contrapose, fg_iff_finiteDimensional, finiteDimensional_of_finite, mem_singleton, of_mem_of_fg, subset_adjoin, toSubalgebra, trace_eq_zero_of_not_exists_basis, zero_apply
-/
theorem trace_gen_eq_zero {x : L} (hx : ¬IsIntegral K x) :
    Algebra.trace K K⟮x⟯ (AdjoinSimple.gen K x) = 0 := by
  rw [trace_eq_zero_of_not_exists_basis]; rw [LinearMap.zero_apply]
  contrapose hx
  obtain ⟨s, ⟨b⟩⟩ := hx
  refine .of_mem_of_fg K⟮x⟯.toSubalgebra ?_ x ?_
  · exact (Submodule.fg_iff_finiteDimensional _).mpr (b.finiteDimensional_of_finite)
  · exact subset_adjoin K _ (Set.mem_singleton x)

/--
theorem `trace_gen_eq_sum_roots` / 定理 `trace_gen_eq_sum_roots`

English:
theorem trace_gen_eq_sum_roots
  given: (x : L) (hf : ((minpoly K x).map (algebraMap K F)).Splits)
  proof: by
  have injKxL := (algebraMap K⟮x⟯ L).injective
  by_cases hx : IsIntegral K x; swap
  · simp [minpoly.eq_zero hx, trace_gen_eq_zero hx, aroots_def]
  rw [← adjoin.powerBasis_gen hx]; rw [(adjoin.powerBasis hx).trace_gen_eq_sum_roots] <;>
    rw [adjoin.powerBasis_gen hx]; rw [← minpoly.algebraMap

中文:
定理 trace_gen_eq_sum_roots
  条件: (x : L) (hf : ((minpoly K x).map (algebraMap K F)).Splits)
  证明: by
  have injKxL := (algebraMap K⟮x⟯ L).injective
  by_cases hx : IsIntegral K x; swap
  · simp [minpoly.eq_zero hx, trace_gen_eq_zero hx, aroots_def]
  rw [← adjoin.powerBasis_gen hx]; rw [(adjoin.powerBasis hx).trace_gen_eq_sum_roots] <;>
    rw [adjoin.powerBasis_gen hx]; rw [← minpoly.algebraMap

Depends on / 依赖: AdjoinSimple, AdjoinSimple.algebraMap_gen, IsIntegral, adjoin, adjoin.powerBasis, adjoin.powerBasis_gen, algebraMap, algebraMap_eq, algebraMap_gen, aroots_def, eq_zero, injKxL, injective, minpoly, minpoly.algebraMap_eq, minpoly.eq_zero, powerBasis, powerBasis_gen, trace_gen_eq_sum_roots, trace_gen_eq_zero
-/
theorem trace_gen_eq_sum_roots (x : L) (hf : ((minpoly K x).map (algebraMap K F)).Splits) :
    algebraMap K F (trace K K⟮x⟯ (AdjoinSimple.gen K x)) =
      ((minpoly K x).aroots F).sum := by
  have injKxL := (algebraMap K⟮x⟯ L).injective
  by_cases hx : IsIntegral K x; swap
  · simp [minpoly.eq_zero hx, trace_gen_eq_zero hx, aroots_def]
  rw [← adjoin.powerBasis_gen hx]; rw [(adjoin.powerBasis hx).trace_gen_eq_sum_roots] <;>
    rw [adjoin.powerBasis_gen hx]; rw [← minpoly.algebraMap_eq injKxL] <;>
    try simp only [AdjoinSimple.algebraMap_gen _ _]
  exact hf

end IntermediateField.AdjoinSimple

open IntermediateField

variable (K)

/--
theorem `trace_eq_trace_adjoin` / 定理 `trace_eq_trace_adjoin`

English:
theorem trace_eq_trace_adjoin
  given: [FiniteDimensional K L] (x : L)
  proof: by
  rw [← trace_trace (S := K⟮x⟯)]
  conv in x => rw [← AdjoinSimple.algebraMap_gen K x]
  rw [trace_algebraMap]; rw [LinearMap.map_smul_of_tower]

中文:
定理 trace_eq_trace_adjoin
  条件: [FiniteDimensional K L] (x : L)
  证明: by
  rw [← trace_trace (S := K⟮x⟯)]
  conv in x => rw [← AdjoinSimple.algebraMap_gen K x]
  rw [trace_algebraMap]; rw [LinearMap.map_smul_of_tower]

Depends on / 依赖: AdjoinSimple, AdjoinSimple.algebraMap_gen, LinearMap, LinearMap.map_smul_of_tower, algebraMap_gen, map_smul_of_tower, trace_algebraMap, trace_trace
-/
theorem trace_eq_trace_adjoin [FiniteDimensional K L] (x : L) :
    trace K L x = finrank K⟮x⟯ L • trace K K⟮x⟯ (AdjoinSimple.gen K x) := by
  rw [← trace_trace (S := K⟮x⟯)]
  conv in x => rw [← AdjoinSimple.algebraMap_gen K x]
  rw [trace_algebraMap]; rw [LinearMap.map_smul_of_tower]

variable {K} in
/--
theorem `trace_adjoinSimpleGen` / 定理 `trace_adjoinSimpleGen`

English:
theorem trace_adjoinSimpleGen
  given: {x : L} (hx : IsIntegral K x)
  proof: by
simpa [minpoly_gen K x] using PowerBasis.trace_gen_eq_nextCoeff_minpoly adjoin.powerBasis hx

中文:
定理 trace_adjoinSimpleGen
  条件: {x : L} (hx : Is整数egral K x)
  证明: by
simpa [minpoly_gen K x] using PowerBasis.trace_gen_eq_nextCoeff_minpoly adjoin.powerBasis hx

Depends on / 依赖: PowerBasis, PowerBasis.trace_gen_eq_nextCoeff_minpoly, adjoin, adjoin.powerBasis, minpoly_gen, powerBasis, trace_gen_eq_nextCoeff_minpoly
-/
theorem trace_adjoinSimpleGen {x : L} (hx : IsIntegral K x) :
    trace K K⟮x⟯ (AdjoinSimple.gen K x) = -(minpoly K x).nextCoeff := by
simpa [minpoly_gen K x] using PowerBasis.trace_gen_eq_nextCoeff_minpoly adjoin.powerBasis hx

/--
theorem `trace_eq_finrank_mul_minpoly_nextCoeff` / 定理 `trace_eq_finrank_mul_minpoly_nextCoeff`

English:
theorem trace_eq_finrank_mul_minpoly_nextCoeff
  given: [FiniteDimensional K L] (x : L)
  proof: by
  rw [trace_eq_trace_adjoin]; rw [trace_adjoinSimpleGen (.of_finite K x)]; rw [Algebra.smul_def]; rfl

中文:
定理 trace_eq_finrank_mul_minpoly_nextCoeff
  条件: [FiniteDimensional K L] (x : L)
  证明: by
  rw [trace_eq_trace_adjoin]; rw [trace_adjoinSimpleGen (.of_finite K x)]; rw [Algebra.smul_def]; rfl

Depends on / 依赖: Algebra, Algebra.smul_def, of_finite, smul_def, trace_adjoinSimpleGen, trace_eq_trace_adjoin
-/
theorem trace_eq_finrank_mul_minpoly_nextCoeff [FiniteDimensional K L] (x : L) :
    trace K L x = finrank K⟮x⟯ L * -(minpoly K x).nextCoeff := by
  rw [trace_eq_trace_adjoin]; rw [trace_adjoinSimpleGen (.of_finite K x)]; rw [Algebra.smul_def]; rfl

variable {K}

/--
theorem `trace_eq_sum_roots` / 定理 `trace_eq_sum_roots`

English:
theorem trace_eq_sum_roots
  statement: [FiniteDimensional K L] {x : L}
  proof: by
  rw [trace_eq_trace_adjoin K x]; rw [Algebra.smul_def]; rw [map_mul]; rw [← Algebra.smul_def]; rw [IntermediateField.AdjoinSimple.trace_gen_eq_sum_roots _ hF]; rw [IsScalarTower.algebraMap_smul]

中文:
定理 trace_eq_sum_roots
  结论: [FiniteDimensional K L] {x : L}
  证明: by
  rw [trace_eq_trace_adjoin K x]; rw [Algebra.smul_def]; rw [map_mul]; rw [← Algebra.smul_def]; rw [IntermediateField.AdjoinSimple.trace_gen_eq_sum_roots _ hF]; rw [IsScalarTower.algebraMap_smul]

Depends on / 依赖: AdjoinSimple, Algebra, Algebra.smul_def, IntermediateField, IntermediateField.AdjoinSimple.trace_gen_eq_sum_roots, IsScalarTower, IsScalarTower.algebraMap_smul, algebraMap_smul, map_mul, smul_def, trace_eq_trace_adjoin, trace_gen_eq_sum_roots
-/
theorem trace_eq_sum_roots [FiniteDimensional K L] {x : L}
    (hF : ((minpoly K x).map (algebraMap K F)).Splits) :
    algebraMap K F (Algebra.trace K L x) =
      finrank K⟮x⟯ L • ((minpoly K x).aroots F).sum := by
  rw [trace_eq_trace_adjoin K x]; rw [Algebra.smul_def]; rw [map_mul]; rw [← Algebra.smul_def]; rw [IntermediateField.AdjoinSimple.trace_gen_eq_sum_roots _ hF]; rw [IsScalarTower.algebraMap_smul]

end EqSumRoots

variable {F : Type*} [Field F]
variable [Algebra R L] [Algebra L F] [Algebra R F] [IsScalarTower R L F]

open Polynomial

attribute [-instance] Field.toEuclideanDomain

/--
theorem `Algebra.isIntegral_trace` / 定理 `Algebra.isIntegral_trace`

English:
theorem Algebra.isIntegral_trace
  given: [FiniteDimensional L F] {x : F} (hx : IsIntegral R x)
  proof: by
  have hx' : IsIntegral L x := hx.tower_top
  rw [← isIntegral_algebraMap_iff (algebraMap L (AlgebraicClosure F)).injective]; rw [trace_eq_sum_roots]
  · refine (IsIntegral.multiset_sum ?_).nsmul _
    intro y hy
    rw [mem_roots_map (minpoly.ne_zero hx')] at hy
    use minpoly R x, minpoly.moni

中文:
定理 Algebra.isIntegral_trace
  条件: [FiniteDimensional L F] {x : F} (hx : Is整数egral R x)
  证明: by
  have hx' : IsIntegral L x := hx.tower_top
  rw [← isIntegral_algebraMap_iff (algebraMap L (AlgebraicClosure F)).injective]; rw [trace_eq_sum_roots]
  · refine (IsIntegral.multiset_sum ?_).nsmul _
    intro y hy
    rw [mem_roots_map (minpoly.ne_zero hx')] at hy
    use minpoly R x, minpoly.moni

Depends on / 依赖: AlgebraicClosure, IsAlgClosed, IsAlgClosed.splits, IsIntegral, IsIntegral.multiset_sum, aeval_def, aeval_of_isScalarTower, algebraMap, hx.tower_top, injective, isIntegral_algebraMap_iff, mem_roots_map, minpoly, minpoly.aeval_of_isScalarTower, minpoly.monic, minpoly.ne_zero, multiset_sum, ne_zero, splits, tower_top
-/
theorem Algebra.isIntegral_trace [FiniteDimensional L F] {x : F} (hx : IsIntegral R x) :
    IsIntegral R (Algebra.trace L F x) := by
  have hx' : IsIntegral L x := hx.tower_top
  rw [← isIntegral_algebraMap_iff (algebraMap L (AlgebraicClosure F)).injective]; rw [trace_eq_sum_roots]
  · refine (IsIntegral.multiset_sum ?_).nsmul _
    intro y hy
    rw [mem_roots_map (minpoly.ne_zero hx')] at hy
    use minpoly R x, minpoly.monic hx
    rw [← aeval_def] at hy ⊢
    exact minpoly.aeval_of_isScalarTower R x y hy
  · apply IsAlgClosed.splits

/--
lemma `Algebra.trace_eq_of_algEquiv` / 引理 `Algebra.trace_eq_of_algEquiv`

English:
lemma Algebra.trace_eq_of_algEquiv
  statement: {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  proof: by
  simp_rw [Algebra.trace_apply, ← LinearMap.trace_conj' _ e.toLinearEquiv]
  congr; ext; simp

中文:
引理 Algebra.trace_eq_of_algEquiv
  结论: {A B C : 类型} [CommRing A] [CommRing B] [CommRing C]
  证明: by
  simp_rw [Algebra.trace_apply, ← LinearMap.trace_conj' _ e.toLinearEquiv]
  congr; ext; simp

Depends on / 依赖: Algebra, Algebra.trace_apply, LinearMap, LinearMap.trace_conj, e.toLinearEquiv, simp_rw, toLinearEquiv, trace_apply, trace_conj
-/
lemma Algebra.trace_eq_of_algEquiv {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] (e : B ≃ₐ[A] C) (x) :
    Algebra.trace A C (e x) = Algebra.trace A B x := by
  simp_rw [Algebra.trace_apply, ← LinearMap.trace_conj' _ e.toLinearEquiv]
  congr; ext; simp

set_option backward.isDefEq.respectTransparency false in
/--
lemma `Algebra.trace_eq_of_ringEquiv` / 引理 `Algebra.trace_eq_of_ringEquiv`

English:
lemma Algebra.trace_eq_of_ringEquiv
  statement: {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  proof: by
  classical
  by_cases h : exists s : Finset C, Nonempty (Basis s B C)
  · obtain ⟨s, ⟨b⟩⟩ := h
    let : Algebra A B := RingHom.toAlgebra e
    let : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq' he.symm
    rw [Algebra.trace_eq_matrix_trace b]; rw [Algebra.trace_eq_matrix_trace (b.mapC

中文:
引理 Algebra.trace_eq_of_ringEquiv
  结论: {A B C : 类型} [CommRing A] [CommRing B] [CommRing C]
  证明: by
  classical
  by_cases h : exists s : Finset C, Nonempty (Basis s B C)
  · obtain ⟨s, ⟨b⟩⟩ := h
    let : Algebra A B := RingHom.toAlgebra e
    let : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq' he.symm
    rw [Algebra.trace_eq_matrix_trace b]; rw [Algebra.trace_eq_matrix_trace (b.mapC

Depends on / 依赖: AddMonoidHom, AddMonoidHom.map_trace, Algebra, Algebra.smul_def, Algebra.trace_eq_matrix_trace, Finset, IsScalarTower, IsScalarTower.of_algebraMap_eq, LinearMap, LinearMap.toMatrix_apply, Nonempty, RingHom, RingHom.toAlgebra, b.mapCoeffs, classical, e.symm, he.symm, leftMulMatrix_apply, mapCoeffs, map_trace
-/
lemma Algebra.trace_eq_of_ringEquiv {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A C] [Algebra B C] (e : A ≃+* B) (he : (algebraMap B C).comp e = algebraMap A C) (x) :
    e (Algebra.trace A C x) = Algebra.trace B C x := by
  classical
  by_cases h : exists s : Finset C, Nonempty (Basis s B C)
  · obtain ⟨s, ⟨b⟩⟩ := h
    let : Algebra A B := RingHom.toAlgebra e
    let : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq' he.symm
    rw [Algebra.trace_eq_matrix_trace b]; rw [Algebra.trace_eq_matrix_trace (b.mapCoeffs e.symm (by simp [Algebra.smul_def]; rw [← he]))]
    rw [AddMonoidHom.map_trace]
    congr
    ext i j
    simp [leftMulMatrix_apply, LinearMap.toMatrix_apply]
  rw [trace_eq_zero_of_not_exists_basis _ h]; rw [trace_eq_zero_of_not_exists_basis]; rw [LinearMap.zero_apply]; rw [LinearMap.zero_apply]; rw [map_zero]
  intro ⟨s, ⟨b⟩⟩
  exact h ⟨s, ⟨b.mapCoeffs e (by simp [Algebra.smul_def, ← he])⟩⟩

/--
lemma `Algebra.trace_eq_of_equiv_equiv` / 引理 `Algebra.trace_eq_of_equiv_equiv`

English:
lemma Algebra.trace_eq_of_equiv_equiv
  statement: {A₁ B₁ A₂ B₂ : Type*} [CommRing A₁] [CommRing B₁]
  proof: by
  let := (RingHom.comp (e₂ : B₁ ->+* B₂) (algebraMap A₁ B₁)).toAlgebra
  let e' : B₁ ≃ₐ[A₁] B₂ := { e₂ with commutes' := fun _ => rfl }
  rw [← Algebra.trace_eq_of_ringEquiv e₁ he]; rw [← Algebra.trace_eq_of_algEquiv e']; rw [RingEquiv.symm_apply_apply]
  rfl

中文:
引理 Algebra.trace_eq_of_equiv_equiv
  结论: {A₁ B₁ A₂ B₂ : 类型} [CommRing A₁] [CommRing B₁]
  证明: by
  let := (RingHom.comp (e₂ : B₁ ->+* B₂) (algebraMap A₁ B₁)).toAlgebra
  let e' : B₁ ≃ₐ[A₁] B₂ := { e₂ with commutes' := fun _ => rfl }
  rw [← Algebra.trace_eq_of_ringEquiv e₁ he]; rw [← Algebra.trace_eq_of_algEquiv e']; rw [RingEquiv.symm_apply_apply]
  rfl

Depends on / 依赖: Algebra, Algebra.trace_eq_of_algEquiv, Algebra.trace_eq_of_ringEquiv, RingEquiv, RingEquiv.symm_apply_apply, RingHom, RingHom.comp, algebraMap, commutes, symm_apply_apply, toAlgebra, trace_eq_of_algEquiv, trace_eq_of_ringEquiv
-/
lemma Algebra.trace_eq_of_equiv_equiv {A₁ B₁ A₂ B₂ : Type*} [CommRing A₁] [CommRing B₁]
    [CommRing A₂] [CommRing B₂] [Algebra A₁ B₁] [Algebra A₂ B₂] (e₁ : A₁ ≃+* A₂) (e₂ : B₁ ≃+* B₂)
    (he : RingHom.comp (algebraMap A₂ B₂) ↑e₁ = RingHom.comp ↑e₂ (algebraMap A₁ B₁)) (x) :
    Algebra.trace A₁ B₁ x = e₁.symm (Algebra.trace A₂ B₂ (e₂ x)) := by
  let := (RingHom.comp (e₂ : B₁ ->+* B₂) (algebraMap A₁ B₁)).toAlgebra
  let e' : B₁ ≃ₐ[A₁] B₂ := { e₂ with commutes' := fun _ => rfl }
  rw [← Algebra.trace_eq_of_ringEquiv e₁ he]; rw [← Algebra.trace_eq_of_algEquiv e']; rw [RingEquiv.symm_apply_apply]
  rfl

section EqSumEmbeddings

variable [Algebra K F] [IsScalarTower K L F]

open Algebra IntermediateField

variable (F) (E : Type*) [Field E] [Algebra K E]

/--
theorem `trace_eq_sum_embeddings_gen` / 定理 `trace_eq_sum_embeddings_gen`

English:
theorem trace_eq_sum_embeddings_gen
  statement: (pb : PowerBasis K L)
  proof: by
  let := Classical.decEq E
  let : Fintype (L ->ₐ[K] E) := PowerBasis.AlgHom.fintype pb
  rw [pb.trace_gen_eq_sum_roots hE]; rw [Fintype.sum_equiv pb.liftEquiv']; rw [Finset.sum_mem_multiset]; rw [Finset.sum_eq_multiset_sum]; rw [Multiset.toFinset_val]; rw [Multiset.dedup_eq_self.mpr _]; rw [Mult

中文:
定理 trace_eq_sum_embeddings_gen
  结论: (pb : PowerBasis K L)
  证明: by
  let := Classical.decEq E
  let : Fintype (L ->ₐ[K] E) := PowerBasis.AlgHom.fintype pb
  rw [pb.trace_gen_eq_sum_roots hE]; rw [Fintype.sum_equiv pb.liftEquiv']; rw [Finset.sum_mem_multiset]; rw [Finset.sum_eq_multiset_sum]; rw [Multiset.toFinset_val]; rw [Multiset.dedup_eq_self.mpr _]; rw [Mult

Depends on / 依赖: AlgHom, Classical, Classical.decEq, Finset, Finset.sum_eq_multiset_sum, Finset.sum_mem_multiset, Fintype, Fintype.sum_equiv, Multiset, Multiset.dedup_eq_self.mpr, Multiset.map_id, Multiset.toFinset_val, PowerBasis, PowerBasis.AlgHom.fintype, PowerBasis.liftEquiv, _apply_coe, dedup_eq_self, fintype, id_def, liftEquiv
-/
theorem trace_eq_sum_embeddings_gen (pb : PowerBasis K L)
    (hE : ((minpoly K pb.gen).map (algebraMap K E)).Splits) (hfx : IsSeparable K pb.gen) :
    algebraMap K E (Algebra.trace K L pb.gen) =
      (@Finset.univ _ (PowerBasis.AlgHom.fintype pb)).sum fun σ => σ pb.gen := by
  let := Classical.decEq E
  let : Fintype (L ->ₐ[K] E) := PowerBasis.AlgHom.fintype pb
  rw [pb.trace_gen_eq_sum_roots hE]; rw [Fintype.sum_equiv pb.liftEquiv']; rw [Finset.sum_mem_multiset]; rw [Finset.sum_eq_multiset_sum]; rw [Multiset.toFinset_val]; rw [Multiset.dedup_eq_self.mpr _]; rw [Multiset.map_id]
  · exact nodup_roots ((separable_map _).mpr hfx)
  swap
  · intro x; rfl
  · intro σ
    rw [PowerBasis.liftEquiv'_apply_coe]; rw [id_def]

variable [IsAlgClosed E]

/--
theorem `sum_embeddings_eq_finrank_mul` / 定理 `sum_embeddings_eq_finrank_mul`

English:
theorem sum_embeddings_eq_finrank_mul
  statement: [FiniteDimensional K F] [Algebra.IsSeparable K F]
  proof: by
  have : FiniteDimensional L F := FiniteDimensional.right K L F
  have : Algebra.IsSeparable L F := Algebra.isSeparable_tower_top_of_isSeparable K L F
  let : Fintype (L ->ₐ[K] E) := PowerBasis.AlgHom.fintype pb
  rw [Fintype.sum_equiv algHomEquivSigma (fun σ : F ->ₐ[K] E => _) fun σ => σ.1 pb.ge

中文:
定理 sum_embeddings_eq_finrank_mul
  结论: [FiniteDimensional K F] [Algebra.IsSeparable K F]
  证明: by
  have : FiniteDimensional L F := FiniteDimensional.right K L F
  have : Algebra.IsSeparable L F := Algebra.isSeparable_tower_top_of_isSeparable K L F
  let : Fintype (L ->ₐ[K] E) := PowerBasis.AlgHom.fintype pb
  rw [Fintype.sum_equiv algHomEquivSigma (fun σ : F ->ₐ[K] E => _) fun σ => σ.1 pb.ge

Depends on / 依赖: AlgHom, Algebra, Algebra.IsSeparable, Algebra.isSeparable_tower_top_of_isSeparable, FiniteDimensional, FiniteDimensional.right, Finset, Finset.card_univ, Finset.sum_congr, Finset.sum_const, Finset.sum_nsmul, Finset.sum_sigma, Finset.univ_sigma_univ, Fintype, Fintype.sum_equiv, IsSeparable, PowerBasis, PowerBasis.AlgHom.fintype, algHomEquivSigma, card_univ
-/
theorem sum_embeddings_eq_finrank_mul [FiniteDimensional K F] [Algebra.IsSeparable K F]
    (pb : PowerBasis K L) :
    ∑ σ : F ->ₐ[K] E, σ (algebraMap L F pb.gen) =
      finrank L F •
        (@Finset.univ _ (PowerBasis.AlgHom.fintype pb)).sum fun σ : L ->ₐ[K] E => σ pb.gen := by
  have : FiniteDimensional L F := FiniteDimensional.right K L F
  have : Algebra.IsSeparable L F := Algebra.isSeparable_tower_top_of_isSeparable K L F
  let : Fintype (L ->ₐ[K] E) := PowerBasis.AlgHom.fintype pb
  rw [Fintype.sum_equiv algHomEquivSigma (fun σ : F ->ₐ[K] E => _) fun σ => σ.1 pb.gen,
    ← Finset.univ_sigma_univ, Finset.sum_sigma, ← Finset.sum_nsmul]
  · refine Finset.sum_congr rfl fun σ _ => ?_
    let : Algebra L E := σ.toRingHom.toAlgebra
    simp_rw [Finset.sum_const, Finset.card_univ, ← AlgHom.card L F E]
  · intro σ
    simp only [algHomEquivSigma, Equiv.coe_fn_mk, AlgHom.domRestrict, AlgHom.comp_apply,
      IsScalarTower.coe_toAlgHom']

/--
theorem `trace_eq_sum_embeddings` / 定理 `trace_eq_sum_embeddings`

English:
theorem trace_eq_sum_embeddings
  given: [FiniteDimensional K L] [Algebra.IsSeparable K L] {x : L}
  proof: by
  have hx := Algebra.IsSeparable.isIntegral K x
  let pb := adjoin.powerBasis hx
  rw [trace_eq_trace_adjoin K x]; rw [Algebra.smul_def]; rw [map_mul]; rw [← adjoin.powerBasis_gen hx]; rw [trace_eq_sum_embeddings_gen E pb (IsAlgClosed.splits _)]; rw [← Algebra.smul_def]; rw [algebraMap_smul]
  · 

中文:
定理 trace_eq_sum_embeddings
  条件: [FiniteDimensional K L] [Algebra.IsSeparable K L] {x : L}
  证明: by
  have hx := Algebra.IsSeparable.isIntegral K x
  let pb := adjoin.powerBasis hx
  rw [trace_eq_trace_adjoin K x]; rw [Algebra.smul_def]; rw [map_mul]; rw [← adjoin.powerBasis_gen hx]; rw [trace_eq_sum_embeddings_gen E pb (IsAlgClosed.splits _)]; rw [← Algebra.smul_def]; rw [algebraMap_smul]
  · 

Depends on / 依赖: Algebra, Algebra.IsSeparable.isIntegral, Algebra.IsSeparable.isSeparable, Algebra.isSeparable_tower_bot_of_isSeparable, Algebra.smul_def, IsAlgClosed, IsAlgClosed.splits, IsSeparable, adjoin, adjoin.powerBasis, adjoin.powerBasis_gen, algebraMap_smul, isIntegral, isSeparable, isSeparable_tower_bot_of_isSeparable, map_mul, powerBasis, powerBasis_gen, smul_def, splits
-/
theorem trace_eq_sum_embeddings [FiniteDimensional K L] [Algebra.IsSeparable K L] {x : L} :
    algebraMap K E (Algebra.trace K L x) = ∑ σ : L ->ₐ[K] E, σ x := by
  have hx := Algebra.IsSeparable.isIntegral K x
  let pb := adjoin.powerBasis hx
  rw [trace_eq_trace_adjoin K x]; rw [Algebra.smul_def]; rw [map_mul]; rw [← adjoin.powerBasis_gen hx]; rw [trace_eq_sum_embeddings_gen E pb (IsAlgClosed.splits _)]; rw [← Algebra.smul_def]; rw [algebraMap_smul]
  · exact (sum_embeddings_eq_finrank_mul L E pb).symm
  · have := Algebra.isSeparable_tower_bot_of_isSeparable K K⟮x⟯ L
    exact Algebra.IsSeparable.isSeparable K _

/--
theorem `trace_eq_sum_automorphisms` / 定理 `trace_eq_sum_automorphisms`

English:
theorem trace_eq_sum_automorphisms
  given: (x : L) [FiniteDimensional K L] [IsGalois K L]
  proof: by
  apply FaithfulSMul.algebraMap_injective L (AlgebraicClosure L)
  rw [_root_.map_sum (algebraMap L (AlgebraicClosure L))]
  rw [← Fintype.sum_equiv (Normal.algHomEquivAut K (AlgebraicClosure L) L)]
  · rw [← trace_eq_sum_embeddings (AlgebraicClosure L) (x := x)]
    simp only [algebraMap_eq_smul

中文:
定理 trace_eq_sum_automorphisms
  条件: (x : L) [FiniteDimensional K L] [IsGalois K L]
  证明: by
  apply FaithfulSMul.algebraMap_injective L (AlgebraicClosure L)
  rw [_root_.map_sum (algebraMap L (AlgebraicClosure L))]
  rw [← Fintype.sum_equiv (Normal.algHomEquivAut K (AlgebraicClosure L) L)]
  · rw [← trace_eq_sum_embeddings (AlgebraicClosure L) (x := x)]
    simp only [algebraMap_eq_smul

Depends on / 依赖: AlgEquiv, AlgEquiv.coe_ofBijective, AlgHom, AlgHom.restrictNormal, AlgHom.restrictNormal_commutes, AlgebraicClosure, Equiv.coe_fn_mk, FaithfulSMul, FaithfulSMul.algebraMap_injective, Fintype, Fintype.sum_equiv, Normal, Normal.algHomEquivAut, RingHom, RingHom.id_apply, _root_, _root_.map_sum, algHomEquivAut, algebraMap, algebraMap_eq_smul_one
-/
theorem trace_eq_sum_automorphisms (x : L) [FiniteDimensional K L] [IsGalois K L] :
    algebraMap K L (Algebra.trace K L x) = ∑ σ : Gal(L/K), σ x := by
  apply FaithfulSMul.algebraMap_injective L (AlgebraicClosure L)
  rw [_root_.map_sum (algebraMap L (AlgebraicClosure L))]
  rw [← Fintype.sum_equiv (Normal.algHomEquivAut K (AlgebraicClosure L) L)]
  · rw [← trace_eq_sum_embeddings (AlgebraicClosure L) (x := x)]
    simp only [algebraMap_eq_smul_one, smul_one_smul]
  · intro σ
    simp only [Normal.algHomEquivAut, AlgHom.restrictNormal', Equiv.coe_fn_mk,
      AlgEquiv.coe_ofBijective, AlgHom.restrictNormal_commutes, algebraMap_self, RingHom.id_apply]

end EqSumEmbeddings

section NotIsSeparable

/--
lemma `Algebra.trace_eq_zero_of_not_isSeparable` / 引理 `Algebra.trace_eq_zero_of_not_isSeparable`

English:
lemma Algebra.trace_eq_zero_of_not_isSeparable
  given: (H : ¬ Algebra.IsSeparable K L)
  proof: by
  obtain ⟨p, hp⟩ := ExpChar.exists K
  have := expChar_ne_zero K p
  ext x
  by_cases h₀ : FiniteDimensional K L; swap
  · rw [trace_eq_zero_of_not_exists_basis]
    rintro ⟨s, ⟨b⟩⟩
    exact h₀ (Module.Finite.of_basis b)
  by_cases hx : IsSeparable K x
  · lift x to separableClosure K L using hx

中文:
引理 Algebra.trace_eq_zero_of_not_isSeparable
  条件: (H : ¬ Algebra.IsSeparable K L)
  证明: by
  obtain ⟨p, hp⟩ := ExpChar.exists K
  have := expChar_ne_zero K p
  ext x
  by_cases h₀ : FiniteDimensional K L; swap
  · rw [trace_eq_zero_of_not_exists_basis]
    rintro ⟨s, ⟨b⟩⟩
    exact h₀ (Module.Finite.of_basis b)
  by_cases hx : IsSeparable K x
  · lift x to separableClosure K L using hx

Depends on / 依赖: ExpChar, ExpChar.exists, Finite, FiniteDimensional, IntermediateField, IntermediateField.algebraMap_apply, IsPurelyInseparable, IsPurelyInseparable.finrank_eq_pow, IsSeparable, Module, Module.Finite.of_basis, algebraMap_apply, expChar_ne_zero, finrank_eq_pow, of_basis, separableClosure, trace_algebraMap, trace_eq_zero_of_not_exists_basis, trace_trace
-/
lemma Algebra.trace_eq_zero_of_not_isSeparable (H : ¬ Algebra.IsSeparable K L) :
    trace K L = 0 := by
  obtain ⟨p, hp⟩ := ExpChar.exists K
  have := expChar_ne_zero K p
  ext x
  by_cases h₀ : FiniteDimensional K L; swap
  · rw [trace_eq_zero_of_not_exists_basis]
    rintro ⟨s, ⟨b⟩⟩
    exact h₀ (Module.Finite.of_basis b)
  by_cases hx : IsSeparable K x
  · lift x to separableClosure K L using hx
    rw [← IntermediateField.algebraMap_apply]; rw [← trace_trace (S := separableClosure K L)]; rw [trace_algebraMap]
    obtain ⟨n, hn⟩ := IsPurelyInseparable.finrank_eq_pow (separableClosure K L) L p
    cases n with
    | zero =>
      rw [pow_zero]; rw [IntermediateField.finrank_eq_one_iff_eq_top]; rw [separableClosure.eq_top_iff] at hn
      cases H hn
    | succ n =>
      cases hp with
      | zero =>
        rw [one_pow]; rw [IntermediateField.finrank_eq_one_iff_eq_top]; rw [separableClosure.eq_top_iff] at hn
        cases H hn
      | prime hprime =>
        rw [hn]; rw [pow_succ']; rw [mul_smul]; rw [LinearMap.map_smul_of_tower]; rw [nsmul_eq_mul]; rw [CharP.cast_eq_zero]; rw [zero_mul]; rw [LinearMap.zero_apply]
  · rw [trace_eq_finrank_mul_minpoly_nextCoeff]
    obtain ⟨g, hg₁, m, hg₂⟩ :=
      (minpoly.irreducible (IsIntegral.isIntegral (R := K) x)).hasSeparableContraction p
    cases m with
    | zero =>
      obtain rfl : g = minpoly K x := by simpa using hg₂
      cases hx hg₁
    | succ n =>
      rw [nextCoeff]; rw [if_neg]; rw [← hg₂]; rw [coeff_expand (by positivity)]; rw [if_neg]; rw [neg_zero]; rw [mul_zero]; rw [LinearMap.zero_apply]
      · rw [natDegree_expand]
        intro h
        have := Nat.dvd_sub (dvd_mul_left (p ^ (n + 1)) g.natDegree) h
        rw [tsub_tsub_cancel_of_le]; rw [Nat.dvd_one] at this
        · obtain rfl : g = minpoly K x := by simpa [this] using hg₂
          cases hx hg₁
        · rw [Nat.one_le_iff_ne_zero]
          have : g.natDegree != 0 := fun e => by
            have := congr(natDegree $hg₂)
            rw [natDegree_expand]; rw [e]; rw [zero_mul] at this
            exact (minpoly.natDegree_pos (IsIntegral.isIntegral x)).ne this
          positivity
      · exact (minpoly.natDegree_pos (IsIntegral.isIntegral x)).ne'

end NotIsSeparable

section DetNeZero

namespace Algebra

variable (A : Type u) {B : Type v} (C : Type z)
variable [CommRing A] [CommRing B] [Algebra A B] [CommRing C] [Algebra A C]

open Finset

/--
Definition of `traceMatrix` / `traceMatrix` 的定义

English:
definition traceMatrix
  signature: (b : κ -> B)
  body: of fun i j => traceForm A B (b i) (b j)

中文:
定义 traceMatrix
  签名: (b : κ -> B)
  定义体: of fun i j => traceForm A B (b i) (b j)

Depends on / 依赖: traceForm
-/
noncomputable def traceMatrix (b : κ -> B) : Matrix κ κ A :=
  of fun i j => traceForm A B (b i) (b j)

-- TODO: set as an equation lemma for `traceMatrix`, see https://github.com/leanprover-community/mathlib4/pull/3024
@[simp]
/--
theorem `traceMatrix_apply` / 定理 `traceMatrix_apply`

English:
theorem traceMatrix_apply
  given: (b : κ -> B) (i j)
  statement: traceMatrix A b i j = traceForm A B (b i) (b j)
  proof: rfl

中文:
定理 traceMatrix_apply
  条件: (b : κ -> B) (i j)
  结论: traceMatrix A b i j = traceForm A B (b i) (b j)
  证明: rfl
-/
theorem traceMatrix_apply (b : κ -> B) (i j) : traceMatrix A b i j = traceForm A B (b i) (b j) :=
  rfl

/--
theorem `traceMatrix_reindex` / 定理 `traceMatrix_reindex`

English:
theorem traceMatrix_reindex
  given: {κ' : Type*} (b : Basis κ A B) (f : κ ≃ κ')
  proof: by ext (x y); simp

中文:
定理 traceMatrix_reindex
  条件: {κ' : 类型} (b : Basis κ A B) (f : κ ≃ κ')
  证明: by ext (x y); simp
-/
theorem traceMatrix_reindex {κ' : Type*} (b : Basis κ A B) (f : κ ≃ κ') :
    traceMatrix A (b.reindex f) = reindex f f (traceMatrix A b) := by ext (x y); simp

variable {A}

/--
theorem `traceMatrix_of_matrix_vecMul` / 定理 `traceMatrix_of_matrix_vecMul`

English:
theorem traceMatrix_of_matrix_vecMul
  given: [Fintype κ] (b : κ -> B) (P : Matrix κ κ A)
  proof: by
  ext (α β)
  rw [traceMatrix_apply]; rw [vecMul]; rw [dotProduct]; rw [vecMul]; rw [dotProduct]; rw [Matrix.mul_apply]; rw [BilinForm.sum_left]; rw [Fintype.sum_congr _ _ fun i : κ =>
      BilinForm.sum_right _ _ (b i * P.map (algebraMap A B) i α) fun y : κ =>
        b y * P.map (algebraMap A 

中文:
定理 traceMatrix_of_matrix_vecMul
  条件: [Fintype κ] (b : κ -> B) (P : Matrix κ κ A)
  证明: by
  ext (α β)
  rw [traceMatrix_apply]; rw [vecMul]; rw [dotProduct]; rw [vecMul]; rw [dotProduct]; rw [Matrix.mul_apply]; rw [BilinForm.sum_left]; rw [Fintype.sum_congr _ _ fun i : κ =>
      BilinForm.sum_right _ _ (b i * P.map (algebraMap A B) i α) fun y : κ =>
        b y * P.map (algebraMap A 

Depends on / 依赖: BilinForm, BilinForm.sum_left, BilinForm.sum_right, Fintype, Fintype.sum_congr, Matrix, Matrix.mul_apply, P.map, RingHom, RingHom.id_apply, algebraMap, dotProduct, id_apply, map_apply, mul_apply, mul_comm, smul_def, smul_eq_mul, sum_comm, sum_congr
-/
theorem traceMatrix_of_matrix_vecMul [Fintype κ] (b : κ -> B) (P : Matrix κ κ A) :
    traceMatrix A (b ᵥ* P.map (algebraMap A B)) = Pᵀ * traceMatrix A b * P := by
  ext (α β)
  rw [traceMatrix_apply]; rw [vecMul]; rw [dotProduct]; rw [vecMul]; rw [dotProduct]; rw [Matrix.mul_apply]; rw [BilinForm.sum_left]; rw [Fintype.sum_congr _ _ fun i : κ =>
      BilinForm.sum_right _ _ (b i * P.map (algebraMap A B) i α) fun y : κ =>
        b y * P.map (algebraMap A B) y β]; rw [sum_comm]
  congr; ext x
  rw [Matrix.mul_apply]; rw [sum_mul]
  congr; ext y
  rw [map_apply]; rw [traceForm_apply]; rw [mul_comm (b y)]; rw [← smul_def]
  simp only [smul_eq_mul, RingHom.id_apply, map_apply, transpose_apply, map_smulₛₗ,
    Algebra.smul_mul_assoc]
  rw [mul_comm (b x)]; rw [← smul_def]
  ring_nf
  rw [mul_assoc]
  simp [mul_comm]

/--
theorem `traceMatrix_of_matrix_mulVec` / 定理 `traceMatrix_of_matrix_mulVec`

English:
theorem traceMatrix_of_matrix_mulVec
  given: [Fintype κ] (b : κ -> B) (P : Matrix κ κ A)
  proof: by
  refine AddEquiv.injective (transposeAddEquiv κ κ A) ?_
  rw [transposeAddEquiv_apply]; rw [transposeAddEquiv_apply]; rw [← vecMul_transpose]; rw [← transpose_map]; rw [traceMatrix_of_matrix_vecMul]; rw [transpose_transpose]

中文:
定理 traceMatrix_of_matrix_mulVec
  条件: [Fintype κ] (b : κ -> B) (P : Matrix κ κ A)
  证明: by
  refine AddEquiv.injective (transposeAddEquiv κ κ A) ?_
  rw [transposeAddEquiv_apply]; rw [transposeAddEquiv_apply]; rw [← vecMul_transpose]; rw [← transpose_map]; rw [traceMatrix_of_matrix_vecMul]; rw [transpose_transpose]

Depends on / 依赖: AddEquiv, AddEquiv.injective, injective, traceMatrix_of_matrix_vecMul, transposeAddEquiv, transposeAddEquiv_apply, transpose_map, transpose_transpose, vecMul_transpose
-/
theorem traceMatrix_of_matrix_mulVec [Fintype κ] (b : κ -> B) (P : Matrix κ κ A) :
    traceMatrix A (P.map (algebraMap A B) *ᵥ b) = P * traceMatrix A b * Pᵀ := by
  refine AddEquiv.injective (transposeAddEquiv κ κ A) ?_
  rw [transposeAddEquiv_apply]; rw [transposeAddEquiv_apply]; rw [← vecMul_transpose]; rw [← transpose_map]; rw [traceMatrix_of_matrix_vecMul]; rw [transpose_transpose]

/--
theorem `traceMatrix_of_basis` / 定理 `traceMatrix_of_basis`

English:
theorem traceMatrix_of_basis
  given: [Fintype κ] [DecidableEq κ] (b : Basis κ A B)
  proof: by
  ext (i j)
  rw [traceMatrix_apply]; rw [traceForm_apply]; rw [traceForm_toMatrix]

中文:
定理 traceMatrix_of_basis
  条件: [Fintype κ] [DecidableEq κ] (b : Basis κ A B)
  证明: by
  ext (i j)
  rw [traceMatrix_apply]; rw [traceForm_apply]; rw [traceForm_toMatrix]

Depends on / 依赖: traceForm_apply, traceForm_toMatrix, traceMatrix_apply
-/
theorem traceMatrix_of_basis [Fintype κ] [DecidableEq κ] (b : Basis κ A B) :
    traceMatrix A b = (traceForm A B).toMatrix b := by
  ext (i j)
  rw [traceMatrix_apply]; rw [traceForm_apply]; rw [traceForm_toMatrix]

/--
theorem `traceMatrix_of_basis_mulVec` / 定理 `traceMatrix_of_basis_mulVec`

English:
theorem traceMatrix_of_basis_mulVec
  given: [Fintype ι] (b : Basis ι A B) (z : B)
  proof: by
  ext i
  rw [← replicateCol_apply (ι := Fin 1) (traceMatrix A b *ᵥ b.equivFun z) i 0]; rw [replicateCol_mulVec]; rw [Matrix.mul_apply]; rw [traceMatrix]
  simp only [replicateCol_apply, traceForm_apply]
  conv_lhs =>
    congr
    rfl
    ext
    rw [mul_comm _ (b.equivFun z _)]; rw [← smul_eq_m

中文:
定理 traceMatrix_of_basis_mulVec
  条件: [Fintype ι] (b : Basis ι A B) (z : B)
  证明: by
  ext i
  rw [← replicateCol_apply (ι := Fin 1) (traceMatrix A b *ᵥ b.equivFun z) i 0]; rw [replicateCol_mulVec]; rw [Matrix.mul_apply]; rw [traceMatrix]
  simp only [replicateCol_apply, traceForm_apply]
  conv_lhs =>
    congr
    rfl
    ext
    rw [mul_comm _ (b.equivFun z _)]; rw [← smul_eq_m

Depends on / 依赖: Finset, Finset.mul_sum, Matrix, Matrix.mul_apply, _root_, _root_.map_sum, b.equivFun, b.sum_equivFun, conv_lhs, equivFun, map_smul, map_sum, mul_apply, mul_comm, mul_smul_comm, mul_sum, of_apply, replicateCol_apply, replicateCol_mulVec, smul_eq_mul
-/
theorem traceMatrix_of_basis_mulVec [Fintype ι] (b : Basis ι A B) (z : B) :
    traceMatrix A b *ᵥ b.equivFun z = fun i => trace A B (z * b i) := by
  ext i
  rw [← replicateCol_apply (ι := Fin 1) (traceMatrix A b *ᵥ b.equivFun z) i 0]; rw [replicateCol_mulVec]; rw [Matrix.mul_apply]; rw [traceMatrix]
  simp only [replicateCol_apply, traceForm_apply]
  conv_lhs =>
    congr
    rfl
    ext
    rw [mul_comm _ (b.equivFun z _)]; rw [← smul_eq_mul]; rw [of_apply]; rw [← map_smul]
  rw [← _root_.map_sum]
  congr
  conv_lhs =>
    congr
    rfl
    ext
    rw [← mul_smul_comm]
  rw [← Finset.mul_sum]; rw [mul_comm z]
  congr
  rw [b.sum_equivFun]

variable (A)

/--
Definition of `embeddingsMatrix` / `embeddingsMatrix` 的定义

English:
definition embeddingsMatrix
  signature: (b : κ -> B)
  body: of fun i (σ : B ->ₐ[A] C) => σ (b i)

中文:
定义 embeddingsMatrix
  签名: (b : κ -> B)
  定义体: of fun i (σ : B ->ₐ[A] C) => σ (b i)
-/
def embeddingsMatrix (b : κ -> B) : Matrix κ (B ->ₐ[A] C) C :=
  of fun i (σ : B ->ₐ[A] C) => σ (b i)

-- TODO: set as an equation lemma for `embeddingsMatrix`, see https://github.com/leanprover-community/mathlib4/pull/3024
@[simp]
/--
theorem `embeddingsMatrix_apply` / 定理 `embeddingsMatrix_apply`

English:
theorem embeddingsMatrix_apply
  given: (b : κ -> B) (i) (σ : B ->ₐ[A] C)
  proof: rfl

中文:
定理 embeddingsMatrix_apply
  条件: (b : κ -> B) (i) (σ : B ->ₐ[A] C)
  证明: rfl
-/
theorem embeddingsMatrix_apply (b : κ -> B) (i) (σ : B ->ₐ[A] C) :
    embeddingsMatrix A C b i σ = σ (b i) :=
  rfl

/--
Definition of `embeddingsMatrixReindex` / `embeddingsMatrixReindex` 的定义

English:
definition embeddingsMatrixReindex
  signature: (b : κ -> B) (e : κ ≃ (B ->ₐ[A] C))
  body: reindex (Equiv.refl κ) e.symm (embeddingsMatrix A C b)

中文:
定义 embeddingsMatrixReindex
  签名: (b : κ -> B) (e : κ ≃ (B ->ₐ[A] C))
  定义体: reindex (Equiv.refl κ) e.symm (embeddingsMatrix A C b)

Depends on / 依赖: Equiv.refl, e.symm, embeddingsMatrix, reindex
-/
def embeddingsMatrixReindex (b : κ -> B) (e : κ ≃ (B ->ₐ[A] C)) :=
  reindex (Equiv.refl κ) e.symm (embeddingsMatrix A C b)

variable {A}

/--
theorem `embeddingsMatrixReindex_eq_vandermonde` / 定理 `embeddingsMatrixReindex_eq_vandermonde`

English:
theorem embeddingsMatrixReindex_eq_vandermonde
  statement: (pb : PowerBasis A B)
  proof: by
  ext i j
  simp [embeddingsMatrixReindex, embeddingsMatrix]

中文:
定理 embeddingsMatrixReindex_eq_vandermonde
  结论: (pb : PowerBasis A B)
  证明: by
  ext i j
  simp [embeddingsMatrixReindex, embeddingsMatrix]

Depends on / 依赖: embeddingsMatrix, embeddingsMatrixReindex
-/
theorem embeddingsMatrixReindex_eq_vandermonde (pb : PowerBasis A B)
    (e : Fin pb.dim ≃ (B ->ₐ[A] C)) :
    embeddingsMatrixReindex A C pb.basis e = (vandermonde fun i => e i pb.gen)ᵀ := by
  ext i j
  simp [embeddingsMatrixReindex, embeddingsMatrix]

section Field

variable (K) (E : Type z) [Field E]
variable [Algebra K E]
variable [Module.Finite K L] [Algebra.IsSeparable K L] [IsAlgClosed E]
variable (b : κ -> L) (pb : PowerBasis K L)

/--
theorem `traceMatrix_eq_embeddingsMatrix_mul_trans` / 定理 `traceMatrix_eq_embeddingsMatrix_mul_trans`

English:
theorem traceMatrix_eq_embeddingsMatrix_mul_trans
  statement: (traceMatrix K b).map (algebraMap K E) =
  proof: by
  ext (i j); simp [trace_eq_sum_embeddings, embeddingsMatrix, Matrix.mul_apply]

中文:
定理 traceMatrix_eq_embeddingsMatrix_mul_trans
  结论: (traceMatrix K b).map (algebraMap K E) =
  证明: by
  ext (i j); simp [trace_eq_sum_embeddings, embeddingsMatrix, Matrix.mul_apply]

Depends on / 依赖: Matrix, Matrix.mul_apply, embeddingsMatrix, mul_apply, trace_eq_sum_embeddings
-/
theorem traceMatrix_eq_embeddingsMatrix_mul_trans : (traceMatrix K b).map (algebraMap K E) =
    embeddingsMatrix K E b * (embeddingsMatrix K E b)ᵀ := by
  ext (i j); simp [trace_eq_sum_embeddings, embeddingsMatrix, Matrix.mul_apply]

/--
theorem `traceMatrix_eq_embeddingsMatrixReindex_mul_trans` / 定理 `traceMatrix_eq_embeddingsMatrixReindex_mul_trans`

English:
theorem traceMatrix_eq_embeddingsMatrixReindex_mul_trans
  given: [Fintype κ] (e : κ ≃ (L ->ₐ[K] E))
  proof: by
  rw [traceMatrix_eq_embeddingsMatrix_mul_trans]; rw [embeddingsMatrixReindex]; rw [reindex_apply]; rw [transpose_submatrix]; rw [← submatrix_mul_transpose_submatrix]; rw [← Equiv.coe_refl]; rw [Equiv.refl_symm]

中文:
定理 traceMatrix_eq_embeddingsMatrixReindex_mul_trans
  条件: [Fintype κ] (e : κ ≃ (L ->ₐ[K] E))
  证明: by
  rw [traceMatrix_eq_embeddingsMatrix_mul_trans]; rw [embeddingsMatrixReindex]; rw [reindex_apply]; rw [transpose_submatrix]; rw [← submatrix_mul_transpose_submatrix]; rw [← Equiv.coe_refl]; rw [Equiv.refl_symm]

Depends on / 依赖: Equiv.coe_refl, Equiv.refl_symm, coe_refl, embeddingsMatrixReindex, refl_symm, reindex_apply, submatrix_mul_transpose_submatrix, traceMatrix_eq_embeddingsMatrix_mul_trans, transpose_submatrix
-/
theorem traceMatrix_eq_embeddingsMatrixReindex_mul_trans [Fintype κ] (e : κ ≃ (L ->ₐ[K] E)) :
    (traceMatrix K b).map (algebraMap K E) =
      embeddingsMatrixReindex K E b e * (embeddingsMatrixReindex K E b e)ᵀ := by
  rw [traceMatrix_eq_embeddingsMatrix_mul_trans]; rw [embeddingsMatrixReindex]; rw [reindex_apply]; rw [transpose_submatrix]; rw [← submatrix_mul_transpose_submatrix]; rw [← Equiv.coe_refl]; rw [Equiv.refl_symm]

end Field

end Algebra

open Algebra

variable (pb : PowerBasis K L)

/--
theorem `det_traceMatrix_ne_zero'` / 定理 `det_traceMatrix_ne_zero'`

English:
theorem det_traceMatrix_ne_zero'
  given: [Algebra.IsSeparable K L]
  statement: det (traceMatrix K pb.basis) != 0
  proof: by
  suffices algebraMap K (AlgebraicClosure L) (det (traceMatrix K pb.basis)) != 0 by
    refine mt (fun ht => ?_) this
    rw [ht]; rw [map_zero]
  have : FiniteDimensional K L := pb.finite
  let e : Fin pb.dim ≃ (L ->ₐ[K] AlgebraicClosure L) := (Fintype.equivFinOfCardEq ?_).symm
  · rw [RingHom.m

中文:
定理 det_traceMatrix_ne_zero'
  条件: [Algebra.IsSeparable K L]
  结论: det (traceMatrix K pb.basis) != 0
  证明: by
  suffices algebraMap K (AlgebraicClosure L) (det (traceMatrix K pb.basis)) != 0 by
    refine mt (fun ht => ?_) this
    rw [ht]; rw [map_zero]
  have : FiniteDimensional K L := pb.finite
  let e : Fin pb.dim ≃ (L ->ₐ[K] AlgebraicClosure L) := (Fintype.equivFinOfCardEq ?_).symm
  · rw [RingHom.m

Depends on / 依赖: AlgebraicClosure, FiniteDimensional, Fintype, Fintype.equivFinOfCardEq, RingHom, RingHom.mapMatrix_apply, RingHom.map_det, algebraMap, det_mul, det_transpose, det_vandermonde, embeddingsMatrixReindex_eq_vandermonde, equivFinOfCardEq, finite, mapMatrix_apply, map_det, map_zero, mul_self_eq_zero, mul_self_eq_zero.mp, pb.basis
-/
theorem det_traceMatrix_ne_zero' [Algebra.IsSeparable K L] : det (traceMatrix K pb.basis) != 0 := by
  suffices algebraMap K (AlgebraicClosure L) (det (traceMatrix K pb.basis)) != 0 by
    refine mt (fun ht => ?_) this
    rw [ht]; rw [map_zero]
  have : FiniteDimensional K L := pb.finite
  let e : Fin pb.dim ≃ (L ->ₐ[K] AlgebraicClosure L) := (Fintype.equivFinOfCardEq ?_).symm
  · rw [RingHom.map_det, RingHom.mapMatrix_apply,
      traceMatrix_eq_embeddingsMatrixReindex_mul_trans K _ _ e,
      embeddingsMatrixReindex_eq_vandermonde, det_mul, det_transpose]
    refine mt mul_self_eq_zero.mp ?_
    simp only [det_vandermonde, Finset.prod_eq_zero_iff, not_exists, sub_eq_zero]
    rintro i ⟨_, j, hij, h⟩
    exact (Finset.mem_Ioi.mp hij).ne' (e.injective <| pb.algHom_ext h)
  · rw [AlgHom.card, pb.finrank]

/--
theorem `det_traceForm_ne_zero` / 定理 `det_traceForm_ne_zero`

English:
theorem det_traceForm_ne_zero
  statement: [Algebra.IsSeparable K L] [Fintype ι] [DecidableEq ι]
  proof: by
  have : FiniteDimensional K L := b.finiteDimensional_of_finite
  let pb : PowerBasis K L := Field.powerBasisOfFiniteOfSeparable _ _
  rw [← LinearMap.BilinForm.toMatrix_mul_basis_toMatrix pb.basis b]; rw [←
    det_comm' (pb.basis.toMatrix_mul_toMatrix_flip b) _]; rw [← Matrix.mul_assoc]; rw [de

中文:
定理 det_traceForm_ne_zero
  结论: [Algebra.IsSeparable K L] [Fintype ι] [DecidableEq ι]
  证明: by
  have : FiniteDimensional K L := b.finiteDimensional_of_finite
  let pb : PowerBasis K L := Field.powerBasisOfFiniteOfSeparable _ _
  rw [← LinearMap.BilinForm.toMatrix_mul_basis_toMatrix pb.basis b]; rw [←
    det_comm' (pb.basis.toMatrix_mul_toMatrix_flip b) _]; rw [← Matrix.mul_assoc]; rw [de

Depends on / 依赖: Basis.toMatrix_mul_toMatrix_flip, BilinForm, Field.powerBasisOfFiniteOfSeparable, FiniteDimensional, IsUnit, IsUnit.of_mul_eq_one, LinearMap, LinearMap.BilinForm.toMatrix_mul_basis_toMatrix, Matrix, Matrix.mul_assoc, PowerBasis, b.finiteDimensional_of_finite, b.toMatrix, det_comm, det_mul, finiteDimensional_of_finite, mul_assoc, mul_ne_zero, ne_zero, of_mul_eq_one
-/
theorem det_traceForm_ne_zero [Algebra.IsSeparable K L] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K L) :
    det ((traceForm K L).toMatrix b) != 0 := by
  have : FiniteDimensional K L := b.finiteDimensional_of_finite
  let pb : PowerBasis K L := Field.powerBasisOfFiniteOfSeparable _ _
  rw [← LinearMap.BilinForm.toMatrix_mul_basis_toMatrix pb.basis b]; rw [←
    det_comm' (pb.basis.toMatrix_mul_toMatrix_flip b) _]; rw [← Matrix.mul_assoc]; rw [det_mul]
  swap; · apply Basis.toMatrix_mul_toMatrix_flip
  refine
    mul_ne_zero
      (IsUnit.of_mul_eq_one ((b.toMatrix pb.basis)ᵀ * b.toMatrix pb.basis).det ?_).ne_zero ?_
  · calc
      (pb.basis.toMatrix b * (pb.basis.toMatrix b)ᵀ).det *
            ((b.toMatrix pb.basis)ᵀ * b.toMatrix pb.basis).det =
          (pb.basis.toMatrix b * (b.toMatrix pb.basis * pb.basis.toMatrix b)ᵀ *
              b.toMatrix pb.basis).det := by
        simp only [← det_mul, Matrix.mul_assoc, Matrix.transpose_mul]
      _ = 1 := by
        simp only [Basis.toMatrix_mul_toMatrix_flip, Matrix.transpose_one, Matrix.mul_one,
          Matrix.det_one]
  simpa only [traceMatrix_of_basis] using det_traceMatrix_ne_zero' pb

variable (K L)

/-- Let $L/K$ be a finite extension of fields. If $L/K$ is separable,
then `traceForm` is nondegenerate. -/
@[stacks 0BIL "(1) => (3)"]
/--
theorem `traceForm_nondegenerate` / 定理 `traceForm_nondegenerate`

English:
theorem traceForm_nondegenerate
  given: [FiniteDimensional K L] [Algebra.IsSeparable K L]
  proof: BilinForm.nondegenerate_of_det_ne_zero (traceForm K L) _
    (det_traceForm_ne_zero (Module.finBasis K L))

@[stacks 0BIL]

中文:
定理 traceForm_nondegenerate
  条件: [FiniteDimensional K L] [Algebra.IsSeparable K L]
  证明: BilinForm.nondegenerate_of_det_ne_zero (traceForm K L) _
    (det_traceForm_ne_zero (Module.finBasis K L))

@[stacks 0BIL]

Depends on / 依赖: BilinForm, BilinForm.nondegenerate_of_det_ne_zero, Module, Module.finBasis, det_traceForm_ne_zero, finBasis, nondegenerate_of_det_ne_zero, traceForm
-/
theorem traceForm_nondegenerate [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    (traceForm K L).Nondegenerate :=
  BilinForm.nondegenerate_of_det_ne_zero (traceForm K L) _
    (det_traceForm_ne_zero (Module.finBasis K L))

@[stacks 0BIL]
/--
theorem `traceForm_nondegenerate_tfae` / 定理 `traceForm_nondegenerate_tfae`

English:
theorem traceForm_nondegenerate_tfae
  given: [FiniteDimensional K L]
  proof: by
  tfae_have 1 -> 3 := fun _ => traceForm_nondegenerate K L
  tfae_have 3 -> 2 := fun H₁ H₂ => H₁.ne_zero (by ext; simp [H₂])
  tfae_have 2 -> 1 := not_imp_comm.mp Algebra.trace_eq_zero_of_not_isSeparable
  tfae_finish

中文:
定理 traceForm_nondegenerate_tfae
  条件: [FiniteDimensional K L]
  证明: by
  tfae_have 1 -> 3 := fun _ => traceForm_nondegenerate K L
  tfae_have 3 -> 2 := fun H₁ H₂ => H₁.ne_zero (by ext; simp [H₂])
  tfae_have 2 -> 1 := not_imp_comm.mp Algebra.trace_eq_zero_of_not_isSeparable
  tfae_finish

Depends on / 依赖: Algebra, Algebra.trace_eq_zero_of_not_isSeparable, ne_zero, not_imp_comm, not_imp_comm.mp, tfae_finish, tfae_have, traceForm_nondegenerate, trace_eq_zero_of_not_isSeparable
-/
theorem traceForm_nondegenerate_tfae [FiniteDimensional K L] :
    [Algebra.IsSeparable K L, Algebra.trace K L != 0, (traceForm K L).Nondegenerate].TFAE := by
  tfae_have 1 -> 3 := fun _ => traceForm_nondegenerate K L
  tfae_have 3 -> 2 := fun H₁ H₂ => H₁.ne_zero (by ext; simp [H₂])
  tfae_have 2 -> 1 := not_imp_comm.mp Algebra.trace_eq_zero_of_not_isSeparable
  tfae_finish

/--
theorem `Algebra.trace_ne_zero` / 定理 `Algebra.trace_ne_zero`

English:
theorem Algebra.trace_ne_zero
  given: [FiniteDimensional K L] [Algebra.IsSeparable K L]
  proof: ((traceForm_nondegenerate_tfae K L).out 0 1).mp ‹_›

中文:
定理 Algebra.trace_ne_zero
  条件: [FiniteDimensional K L] [Algebra.IsSeparable K L]
  证明: ((traceForm_nondegenerate_tfae K L).out 0 1).mp ‹_›

Depends on / 依赖: traceForm_nondegenerate_tfae
-/
theorem Algebra.trace_ne_zero [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    Algebra.trace K L != 0 :=
  ((traceForm_nondegenerate_tfae K L).out 0 1).mp ‹_›

/--
theorem `Algebra.trace_surjective` / 定理 `Algebra.trace_surjective`

English:
theorem Algebra.trace_surjective
  given: [FiniteDimensional K L] [Algebra.IsSeparable K L]
  proof: by
  rw [← LinearMap.range_eq_top]
  apply (IsSimpleOrder.eq_bot_or_eq_top (α := Ideal K) _).resolve_left
  rw [LinearMap.range_eq_bot]
  exact Algebra.trace_ne_zero K L

中文:
定理 Algebra.trace_surjective
  条件: [FiniteDimensional K L] [Algebra.IsSeparable K L]
  证明: by
  rw [← LinearMap.range_eq_top]
  apply (IsSimpleOrder.eq_bot_or_eq_top (α := Ideal K) _).resolve_left
  rw [LinearMap.range_eq_bot]
  exact Algebra.trace_ne_zero K L

Depends on / 依赖: Algebra, Algebra.trace_ne_zero, IsSimpleOrder, IsSimpleOrder.eq_bot_or_eq_top, LinearMap, LinearMap.range_eq_bot, LinearMap.range_eq_top, eq_bot_or_eq_top, range_eq_bot, range_eq_top, resolve_left, trace_ne_zero
-/
theorem Algebra.trace_surjective [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    Function.Surjective (Algebra.trace K L) := by
  rw [← LinearMap.range_eq_top]
  apply (IsSimpleOrder.eq_bot_or_eq_top (α := Ideal K) _).resolve_left
  rw [LinearMap.range_eq_bot]
  exact Algebra.trace_ne_zero K L

end DetNeZero

section isNilpotent

namespace Algebra

/--
lemma `isNilpotent_trace_of_isNilpotent` / 引理 `isNilpotent_trace_of_isNilpotent`

English:
lemma isNilpotent_trace_of_isNilpotent
  statement: {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {x : S}
  proof: LinearMap.isNilpotent_trace_of_isNilpotent (hx.map (lmul R S))

中文:
引理 isNilpotent_trace_of_isNilpotent
  结论: {R S : 类型} [CommRing R] [CommRing S] [Algebra R S] {x : S}
  证明: LinearMap.isNilpotent_trace_of_isNilpotent (hx.map (lmul R S))

Depends on / 依赖: LinearMap, LinearMap.isNilpotent_trace_of_isNilpotent, hx.map, isNilpotent_trace_of_isNilpotent
-/
lemma isNilpotent_trace_of_isNilpotent {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {x : S}
    (hx : IsNilpotent x) : IsNilpotent (trace R S x) :=
  LinearMap.isNilpotent_trace_of_isNilpotent (hx.map (lmul R S))

end Algebra

end isNilpotent

section Basis

open Algebra

variable [FiniteDimensional K L] [Algebra.IsSeparable K L] [Finite ι] [DecidableEq ι]
  (b : Basis ι K L)

/--
Definition of `Module.Basis.traceDual` / `Module.Basis.traceDual` 的定义

English:
definition Module.Basis.traceDual
  signature: :
  body: (traceForm K L).dualBasis (traceForm_nondegenerate K L) b

中文:
定义 Module.Basis.traceDual
  签名: :
  定义体: (traceForm K L).dualBasis (traceForm_nondegenerate K L) b

Depends on / 依赖: dualBasis, traceForm, traceForm_nondegenerate
-/
noncomputable def Module.Basis.traceDual :
    Basis ι K L :=
  (traceForm K L).dualBasis (traceForm_nondegenerate K L) b

/--
theorem `Module.Basis.traceDual_def` / 定理 `Module.Basis.traceDual_def`

English:
theorem Module.Basis.traceDual_def
  proof: rfl

@[simp]

中文:
定理 Module.Basis.traceDual_def
  证明: rfl

@[simp]
-/
theorem Module.Basis.traceDual_def :
    b.traceDual = (traceForm K L).dualBasis (traceForm_nondegenerate K L) b := rfl

@[simp]
/--
theorem `Module.Basis.traceDual_repr_apply` / 定理 `Module.Basis.traceDual_repr_apply`

English:
theorem Module.Basis.traceDual_repr_apply
  given: (x : L) (i : ι)
  proof: (traceForm K L).dualBasis_repr_apply _ b _ i

@[simp]

中文:
定理 Module.Basis.traceDual_repr_apply
  条件: (x : L) (i : ι)
  证明: (traceForm K L).dualBasis_repr_apply _ b _ i

@[simp]

Depends on / 依赖: dualBasis_repr_apply, traceForm
-/
theorem Module.Basis.traceDual_repr_apply (x : L) (i : ι) :
    (b.traceDual).repr x i = (traceForm K L x) (b i) :=
  (traceForm K L).dualBasis_repr_apply _ b _ i

@[simp]
/--
theorem `Module.Basis.trace_traceDual_mul` / 定理 `Module.Basis.trace_traceDual_mul`

English:
theorem Module.Basis.trace_traceDual_mul
  given: (i j : ι)
  proof: (traceForm K L).apply_dualBasis_left _ _ i j

@[simp]

中文:
定理 Module.Basis.trace_traceDual_mul
  条件: (i j : ι)
  证明: (traceForm K L).apply_dualBasis_left _ _ i j

@[simp]

Depends on / 依赖: apply_dualBasis_left, traceForm
-/
theorem Module.Basis.trace_traceDual_mul (i j : ι) :
    trace K L ((b.traceDual i) * (b j)) = if j = i then 1 else 0 :=
  (traceForm K L).apply_dualBasis_left _ _ i j

@[simp]
/--
theorem `Module.Basis.trace_mul_traceDual` / 定理 `Module.Basis.trace_mul_traceDual`

English:
theorem Module.Basis.trace_mul_traceDual
  given: (i j : ι)
  proof: (traceForm K L).apply_dualBasis_right _ (traceForm_isSymm K) _ i j

@[simp]

中文:
定理 Module.Basis.trace_mul_traceDual
  条件: (i j : ι)
  证明: (traceForm K L).apply_dualBasis_right _ (traceForm_isSymm K) _ i j

@[simp]

Depends on / 依赖: apply_dualBasis_right, traceForm, traceForm_isSymm
-/
theorem Module.Basis.trace_mul_traceDual (i j : ι) :
    trace K L ((b i) * (b.traceDual j)) = if i = j then 1 else 0 :=
  (traceForm K L).apply_dualBasis_right _ (traceForm_isSymm K) _ i j

@[simp]
/--
theorem `Module.Basis.traceDual_traceDual` / 定理 `Module.Basis.traceDual_traceDual`

English:
theorem Module.Basis.traceDual_traceDual
  proof: (traceForm K L).dualBasis_dualBasis _ (traceForm_isSymm K) _

中文:
定理 Module.Basis.traceDual_traceDual
  证明: (traceForm K L).dualBasis_dualBasis _ (traceForm_isSymm K) _

Depends on / 依赖: dualBasis_dualBasis, traceForm, traceForm_isSymm
-/
theorem Module.Basis.traceDual_traceDual :
    b.traceDual.traceDual = b :=
  (traceForm K L).dualBasis_dualBasis _ (traceForm_isSymm K) _

variable (K L)

/--
theorem `Module.Basis.traceDual_involutive` / 定理 `Module.Basis.traceDual_involutive`

English:
theorem Module.Basis.traceDual_involutive
  proof: (traceForm K L).dualBasis_involutive _ (traceForm_isSymm K)

中文:
定理 Module.Basis.traceDual_involutive
  证明: (traceForm K L).dualBasis_involutive _ (traceForm_isSymm K)

Depends on / 依赖: dualBasis_involutive, traceForm, traceForm_isSymm
-/
theorem Module.Basis.traceDual_involutive :
    Function.Involutive (Basis.traceDual : Basis ι K L -> Basis ι K L) :=
  (traceForm K L).dualBasis_involutive _ (traceForm_isSymm K)

/--
theorem `Module.Basis.traceDual_injective` / 定理 `Module.Basis.traceDual_injective`

English:
theorem Module.Basis.traceDual_injective
  proof: (traceForm K L).dualBasis_injective _ (traceForm_isSymm K)

中文:
定理 Module.Basis.traceDual_injective
  证明: (traceForm K L).dualBasis_injective _ (traceForm_isSymm K)

Depends on / 依赖: dualBasis_injective, traceForm, traceForm_isSymm
-/
theorem Module.Basis.traceDual_injective :
    Function.Injective (Basis.traceDual : Basis ι K L -> Basis ι K L) :=
  (traceForm K L).dualBasis_injective _ (traceForm_isSymm K)

variable {K L b}

@[simp]
/--
theorem `Module.Basis.traceDual_inj` / 定理 `Module.Basis.traceDual_inj`

English:
theorem Module.Basis.traceDual_inj
  given: {b' : Basis ι K L}
  proof: (traceDual_injective K L).eq_iff

中文:
定理 Module.Basis.traceDual_inj
  条件: {b' : Basis ι K L}
  证明: (traceDual_injective K L).eq_iff

Depends on / 依赖: eq_iff, traceDual_injective
-/
theorem Module.Basis.traceDual_inj {b' : Basis ι K L} :
    b.traceDual = b'.traceDual ↔ b = b' :=
  (traceDual_injective K L).eq_iff

/--
A family of vectors `v` is the dual for the trace of the basis `b` if and only if
`∀ i j, Tr(v i * b j) = δ_ij`.
-/
@[simp]
/--
theorem `Module.Basis.traceDual_eq_iff` / 定理 `Module.Basis.traceDual_eq_iff`

English:
theorem Module.Basis.traceDual_eq_iff
  given: {v : ι -> L}
  proof: (traceForm K L).dualBasis_eq_iff (traceForm_nondegenerate K L) b v

中文:
定理 Module.Basis.traceDual_eq_iff
  条件: {v : ι -> L}
  证明: (traceForm K L).dualBasis_eq_iff (traceForm_nondegenerate K L) b v

Depends on / 依赖: dualBasis_eq_iff, traceForm, traceForm_nondegenerate
-/
theorem Module.Basis.traceDual_eq_iff {v : ι -> L} :
    b.traceDual = v ↔ forall i j, traceForm K L (v i) (b j) = if j = i then 1 else 0 :=
  (traceForm K L).dualBasis_eq_iff (traceForm_nondegenerate K L) b v

/--
lemma `Module.Basis.traceDual_powerBasis_eq` / 引理 `Module.Basis.traceDual_powerBasis_eq`

English:
lemma Module.Basis.traceDual_powerBasis_eq
  given: (pb : PowerBasis K L) (i)
  proof: by
  revert i
  rw [← funext_iff]; rw [Basis.traceDual_eq_iff]
  intro i j
  apply (algebraMap K (AlgebraicClosure K)).injective
  have := congr_arg (coeff · i) (sum_smul_minpolyDiv_eq_X_pow (AlgebraicClosure K)
    pb.adjoin_gen_eq_top (r := j) (pb.finrank.symm ▸ j.prop))
  simp only [Polynomial.ma

中文:
引理 Module.Basis.traceDual_powerBasis_eq
  条件: (pb : PowerBasis K L) (i)
  证明: by
  revert i
  rw [← funext_iff]; rw [Basis.traceDual_eq_iff]
  intro i j
  apply (algebraMap K (AlgebraicClosure K)).injective
  have := congr_arg (coeff · i) (sum_smul_minpolyDiv_eq_X_pow (AlgebraicClosure K)
    pb.adjoin_gen_eq_top (r := j) (pb.finrank.symm ▸ j.prop))
  simp only [Polynomial.ma

Depends on / 依赖: AlgebraicClosure, Basis.traceDual_eq_iff, Fin.ext_iff, MonoidWithZeroH, Polynomial, Polynomial.map_smul, PowerBasis, PowerBasis.coe_basis, RingHom, RingHom.coe_coe, adjoin_gen_eq_top, algebraMap, coe_basis, coe_coe, coeff_X_pow, coeff_map, coeff_smul, congr_arg, eq_comm, ext_iff
-/
lemma Module.Basis.traceDual_powerBasis_eq (pb : PowerBasis K L) (i) :
    pb.basis.traceDual i =
      (minpolyDiv K pb.gen).coeff i / aeval pb.gen (derivative <| minpoly K pb.gen) := by
  revert i
  rw [← funext_iff]; rw [Basis.traceDual_eq_iff]
  intro i j
  apply (algebraMap K (AlgebraicClosure K)).injective
  have := congr_arg (coeff · i) (sum_smul_minpolyDiv_eq_X_pow (AlgebraicClosure K)
    pb.adjoin_gen_eq_top (r := j) (pb.finrank.symm ▸ j.prop))
  simp only [Polynomial.map_smul, map_div₀, map_pow, RingHom.coe_coe, finsetSum_coeff, coeff_smul,
    coeff_map, smul_eq_mul, coeff_X_pow, ← Fin.ext_iff, @eq_comm _ i] at this
  rw [PowerBasis.coe_basis]
  simp only [traceForm_apply, MonoidWithZeroHom.map_ite_one_zero]
  rw [← this]; rw [trace_eq_sum_embeddings (E := AlgebraicClosure K)]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [map_mul, map_div₀, map_pow]
  ring

end Basis
