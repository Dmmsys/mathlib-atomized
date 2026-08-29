/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

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

public section


universe u v w

variable {R S T : Type*} [CommRing R] [Ring S]
variable [Algebra R S]
variable {K L F : Type*} [Field K] [Field L] [Field F]
variable [Algebra K L] [Algebra K F]
variable {ι : Type w}

open Module

open LinearMap

open Matrix Polynomial

open scoped Matrix

namespace Algebra

section EqProdRoots

/--
theorem `PowerBasis.norm_gen_eq_coeff_zero_minpoly` / 定理 `PowerBasis.norm_gen_eq_coeff_zero_minpoly`

English:
theorem PowerBasis.norm_gen_eq_coeff_zero_minpoly
  given: (pb : PowerBasis R S)
  proof: by
  rw [norm_eq_matrix_det pb.basis]; rw [det_eq_sign_charpoly_coeff]; rw [charpoly_leftMulMatrix]; rw [Fintype.card_fin]

中文:
定理 PowerBasis.norm_gen_eq_coeff_zero_minpoly
  条件: (pb : PowerBasis R S)
  证明: by
  rw [norm_eq_matrix_det pb.basis]; rw [det_eq_sign_charpoly_coeff]; rw [charpoly_leftMulMatrix]; rw [Fintype.card_fin]

Depends on / 依赖: Fintype, Fintype.card_fin, card_fin, charpoly_leftMulMatrix, det_eq_sign_charpoly_coeff, norm_eq_matrix_det, pb.basis
-/
theorem PowerBasis.norm_gen_eq_coeff_zero_minpoly (pb : PowerBasis R S) :
    norm R pb.gen = (-1) ^ pb.dim * coeff (minpoly R pb.gen) 0 := by
  rw [norm_eq_matrix_det pb.basis]; rw [det_eq_sign_charpoly_coeff]; rw [charpoly_leftMulMatrix]; rw [Fintype.card_fin]

/--
theorem `PowerBasis.norm_gen_eq_prod_roots` / 定理 `PowerBasis.norm_gen_eq_prod_roots`

English:
theorem PowerBasis.norm_gen_eq_prod_roots
  statement: [Algebra R F] (pb : PowerBasis R S)
  proof: by
  have := Module.nontrivial R F
  have := minpoly.monic pb.isIntegral_gen
  rw [PowerBasis.norm_gen_eq_coeff_zero_minpoly]; rw [← pb.natDegree_minpoly]; rw [map_mul]; rw [← coeff_map]; rw [hf.coeff_zero_eq_prod_roots_of_monic (this.map _)]; rw [this.natDegree_map]; rw [map_pow]; rw [← mul_assoc];

中文:
定理 PowerBasis.norm_gen_eq_prod_roots
  结论: [代数 R F] (pb : PowerBasis R S)
  证明: by
  have := Module.nontrivial R F
  have := minpoly.monic pb.isIntegral_gen
  rw [PowerBasis.norm_gen_eq_coeff_zero_minpoly]; rw [← pb.natDegree_minpoly]; rw [map_mul]; rw [← coeff_map]; rw [hf.coeff_zero_eq_prod_roots_of_monic (this.map _)]; rw [this.natDegree_map]; rw [map_pow]; rw [← mul_assoc];

Depends on / 依赖: Module, Module.nontrivial, PowerBasis, PowerBasis.norm_gen_eq_coeff_zero_minpoly, coeff_map, coeff_zero_eq_prod_roots_of_monic, hf.coeff_zero_eq_prod_roots_of_monic, isIntegral_gen, map_mul, map_neg, map_one, map_pow, minpoly, minpoly.monic, mul_assoc, mul_pow, natDegree_map, natDegree_minpoly, neg_mul, neg_neg
-/
theorem PowerBasis.norm_gen_eq_prod_roots [Algebra R F] (pb : PowerBasis R S)
    (hf : ((minpoly R pb.gen).map (algebraMap R F)).Splits) :
    algebraMap R F (norm R pb.gen) = ((minpoly R pb.gen).aroots F).prod := by
  have := Module.nontrivial R F
  have := minpoly.monic pb.isIntegral_gen
  rw [PowerBasis.norm_gen_eq_coeff_zero_minpoly]; rw [← pb.natDegree_minpoly]; rw [map_mul]; rw [← coeff_map]; rw [hf.coeff_zero_eq_prod_roots_of_monic (this.map _)]; rw [this.natDegree_map]; rw [map_pow]; rw [← mul_assoc]; rw [← mul_pow]
  simp only [map_neg, map_one, neg_mul, neg_neg, one_pow, one_mul]

end EqProdRoots

section EqZeroIff

variable [Finite ι]

@[simp]
/--
theorem `norm_zero` / 定理 `norm_zero`

English:
theorem norm_zero
  given: [Nontrivial S] [Module.Free R S] [Module.Finite R S]
  statement: norm R (0 : S) = 0
  proof: by
  nontriviality
  rw [norm_apply]; rw [coe_lmul_eq_mul]; rw [map_zero]; rw [LinearMap.det_zero' (Module.Free.chooseBasis R S)]

@[simp]

中文:
定理 norm_zero
  条件: [非平凡 S] [模.自由 R S] [模.有限 R S]
  结论: norm R (0 : S) = 0
  证明: by
  nontriviality
  rw [norm_apply]; rw [coe_lmul_eq_mul]; rw [map_zero]; rw [LinearMap.det_zero' (Module.Free.chooseBasis R S)]

@[simp]

Depends on / 依赖: LinearMap, LinearMap.det_zero, Module, Module.Free.chooseBasis, chooseBasis, coe_lmul_eq_mul, det_zero, map_zero, nontriviality, norm_apply
-/
theorem norm_zero [Nontrivial S] [Module.Free R S] [Module.Finite R S] : norm R (0 : S) = 0 := by
  nontriviality
  rw [norm_apply]; rw [coe_lmul_eq_mul]; rw [map_zero]; rw [LinearMap.det_zero' (Module.Free.chooseBasis R S)]

@[simp]
/--
theorem `norm_eq_zero_iff` / 定理 `norm_eq_zero_iff`

English:
theorem norm_eq_zero_iff
  given: [IsDomain R] [IsDomain S] [Module.Free R S] [Module.Finite R S] {x : S}
  proof: by
  constructor
  swap
  · rintro rfl; exact norm_zero
  · let b := Module.Free.chooseBasis R S
    let decEq := Classical.decEq (Module.Free.ChooseBasisIndex R S)
    rw [norm_eq_matrix_det b]; rw [← Matrix.exists_mulVec_eq_zero_iff]
    rintro ⟨v, v_ne, hv⟩
    rw [← b.equivFun.apply_symm_apply v

中文:
定理 norm_eq_zero_iff
  条件: [是整环 R] [是整环 S] [模.自由 R S] [模.有限 R S] {x : S}
  证明: by
  constructor
  swap
  · rintro rfl; exact norm_zero
  · let b := Module.Free.chooseBasis R S
    let decEq := Classical.decEq (Module.Free.ChooseBasisIndex R S)
    rw [norm_eq_matrix_det b]; rw [← Matrix.exists_mulVec_eq_zero_iff]
    rintro ⟨v, v_ne, hv⟩
    rw [← b.equivFun.apply_symm_apply v

Depends on / 依赖: ChooseBasisIndex, Classical, Classical.decEq, Matrix, Matrix.exists_mulVec_eq_zero_iff, Module, Module.Free.ChooseBasisIndex, Module.Free.chooseBasis, Pi.zero_app, apply_symm_apply, b.equivFun.apply_symm_apply, b.equivFun_apply, b.equivFun_symm_apply, b.ext_elem, chooseBasis, equivFun, equivFun_apply, equivFun_symm_apply, exists_mulVec_eq_zero_iff, ext_elem
-/
theorem norm_eq_zero_iff [IsDomain R] [IsDomain S] [Module.Free R S] [Module.Finite R S] {x : S} :
    norm R x = 0 ↔ x = 0 := by
  constructor
  swap
  · rintro rfl; exact norm_zero
  · let b := Module.Free.chooseBasis R S
    let decEq := Classical.decEq (Module.Free.ChooseBasisIndex R S)
    rw [norm_eq_matrix_det b]; rw [← Matrix.exists_mulVec_eq_zero_iff]
    rintro ⟨v, v_ne, hv⟩
    rw [← b.equivFun.apply_symm_apply v]; rw [b.equivFun_symm_apply]; rw [b.equivFun_apply]; rw [leftMulMatrix_mulVec_repr] at hv
    refine (mul_eq_zero.mp (b.ext_elem fun i => ?_)).resolve_right (show ∑ i, v i • b i != 0 from ?_)
    · simpa only [map_zero, Pi.zero_apply] using! congr_fun hv i
    · contrapose v_ne with sum_eq
      apply b.equivFun.symm.injective
      rw [b.equivFun_symm_apply]; rw [sum_eq]; rw [map_zero]

/--
theorem `norm_ne_zero_iff` / 定理 `norm_ne_zero_iff`

English:
theorem norm_ne_zero_iff
  given: [IsDomain R] [IsDomain S] [Module.Free R S] [Module.Finite R S] {x : S}
  proof: not_iff_not.mpr norm_eq_zero_iff

中文:
定理 norm_ne_zero_iff
  条件: [是整环 R] [是整环 S] [模.自由 R S] [模.有限 R S] {x : S}
  证明: not_iff_not.mpr norm_eq_zero_iff

Depends on / 依赖: norm_eq_zero_iff, not_iff_not, not_iff_not.mpr
-/
theorem norm_ne_zero_iff [IsDomain R] [IsDomain S] [Module.Free R S] [Module.Finite R S] {x : S} :
    norm R x != 0 ↔ x != 0 := not_iff_not.mpr norm_eq_zero_iff

/-- This is `Algebra.norm_eq_zero_iff` composed with `Algebra.norm_apply`. -/
@[simp]
/--
theorem `norm_eq_zero_iff'` / 定理 `norm_eq_zero_iff'`

English:
theorem norm_eq_zero_iff'
  given: [IsDomain R] [IsDomain S] [Module.Free R S] [Module.Finite R S] {x : S}
  proof: norm_eq_zero_iff

中文:
定理 norm_eq_zero_iff'
  条件: [是整环 R] [是整环 S] [模.自由 R S] [模.有限 R S] {x : S}
  证明: norm_eq_zero_iff

Depends on / 依赖: norm_eq_zero_iff
-/
theorem norm_eq_zero_iff' [IsDomain R] [IsDomain S] [Module.Free R S] [Module.Finite R S] {x : S} :
    LinearMap.det (LinearMap.mul R S x) = 0 ↔ x = 0 := norm_eq_zero_iff

/--
theorem `norm_eq_zero_iff_of_basis` / 定理 `norm_eq_zero_iff_of_basis`

English:
theorem norm_eq_zero_iff_of_basis
  given: [IsDomain R] [IsDomain S] (b : Basis ι R S) {x : S}
  proof: by
  have : Module.Free R S := Module.Free.of_basis b
  have : Module.Finite R S := Module.Finite.of_basis b
  exact norm_eq_zero_iff

中文:
定理 norm_eq_zero_iff_of_basis
  条件: [是整环 R] [是整环 S] (b : 基 ι R S) {x : S}
  证明: by
  have : Module.Free R S := Module.Free.of_basis b
  have : Module.Finite R S := Module.Finite.of_basis b
  exact norm_eq_zero_iff

Depends on / 依赖: Finite, Module, Module.Finite, Module.Finite.of_basis, Module.Free, Module.Free.of_basis, norm_eq_zero_iff, of_basis
-/
theorem norm_eq_zero_iff_of_basis [IsDomain R] [IsDomain S] (b : Basis ι R S) {x : S} :
    Algebra.norm R x = 0 ↔ x = 0 := by
  have : Module.Free R S := Module.Free.of_basis b
  have : Module.Finite R S := Module.Finite.of_basis b
  exact norm_eq_zero_iff

/--
theorem `norm_ne_zero_iff_of_basis` / 定理 `norm_ne_zero_iff_of_basis`

English:
theorem norm_ne_zero_iff_of_basis
  given: [IsDomain R] [IsDomain S] (b : Basis ι R S) {x : S}
  proof: not_iff_not.mpr (norm_eq_zero_iff_of_basis b)

中文:
定理 norm_ne_zero_iff_of_basis
  条件: [是整环 R] [是整环 S] (b : 基 ι R S) {x : S}
  证明: not_iff_not.mpr (norm_eq_zero_iff_of_basis b)

Depends on / 依赖: norm_eq_zero_iff_of_basis, not_iff_not, not_iff_not.mpr
-/
theorem norm_ne_zero_iff_of_basis [IsDomain R] [IsDomain S] (b : Basis ι R S) {x : S} :
    Algebra.norm R x != 0 ↔ x != 0 :=
  not_iff_not.mpr (norm_eq_zero_iff_of_basis b)

end EqZeroIff

section DivisionRing

variable {L : Type*} [DivisionRing L] [Algebra K L] [Module.Finite K L]

/--
theorem `norm_inv` / 定理 `norm_inv`

English:
theorem norm_inv
  given: (x : L)
  statement: Algebra.norm K x⁻¹ = (Algebra.norm K x)⁻¹
  proof: by
  by_cases hx : x = 0
  · simp [hx]
  exact mul_left_injective₀ (norm_ne_zero_iff.mpr hx) (by simp [hx, ← map_mul])

中文:
定理 norm_inv
  条件: (x : L)
  结论: 代数.norm K x⁻¹ = (代数.norm K x)⁻¹
  证明: by
  by_cases hx : x = 0
  · simp [hx]
  exact mul_left_injective₀ (norm_ne_zero_iff.mpr hx) (by simp [hx, ← map_mul])

Depends on / 依赖: map_mul, norm_ne_zero_iff, norm_ne_zero_iff.mpr
-/
theorem norm_inv (x : L) : Algebra.norm K x⁻¹ = (Algebra.norm K x)⁻¹ := by
  by_cases hx : x = 0
  · simp [hx]
  exact mul_left_injective₀ (norm_ne_zero_iff.mpr hx) (by simp [hx, ← map_mul])

/--
theorem `norm_zpow` / 定理 `norm_zpow`

English:
theorem norm_zpow
  given: (x : L) (n : Int)
  statement: Algebra.norm K (x ^ n) = Algebra.norm K x ^ n
  proof: map_zpow' _ norm_inv _ _

中文:
定理 norm_zpow
  条件: (x : L) (n : 整数)
  结论: 代数.norm K (x ^ n) = 代数.norm K x ^ n
  证明: map_zpow' _ norm_inv _ _

Depends on / 依赖: map_zpow, norm_inv
-/
theorem norm_zpow (x : L) (n : Int) : Algebra.norm K (x ^ n) = Algebra.norm K x ^ n :=
  map_zpow' _ norm_inv _ _

end DivisionRing

open IntermediateField

section IntermediateField

/--
theorem `_root_.IntermediateField.AdjoinSimple.norm_gen_eq_one` / 定理 `_root_.IntermediateField.AdjoinSimple.norm_gen_eq_one`

English:
theorem _root_.IntermediateField.AdjoinSimple.norm_gen_eq_one
  given: {x : L} (hx : ¬IsIntegral K x)
  proof: by
  rw [norm_eq_one_of_not_exists_basis]
  contrapose hx
  obtain ⟨s, ⟨b⟩⟩ := hx
  refine .of_mem_of_fg K⟮x⟯.toSubalgebra ?_ x ?_
  · exact (Submodule.fg_iff_finiteDimensional _).mpr (b.finiteDimensional_of_finite)
  · exact IntermediateField.subset_adjoin K _ (Set.mem_singleton x)

中文:
定理 _root_.中间域.AdjoinSimple.norm_gen_eq_one
  条件: {x : L} (hx : ¬是整 K x)
  证明: by
  rw [norm_eq_one_of_not_exists_basis]
  contrapose hx
  obtain ⟨s, ⟨b⟩⟩ := hx
  refine .of_mem_of_fg K⟮x⟯.toSubalgebra ?_ x ?_
  · exact (Submodule.fg_iff_finiteDimensional _).mpr (b.finiteDimensional_of_finite)
  · exact IntermediateField.subset_adjoin K _ (Set.mem_singleton x)

Depends on / 依赖: IntermediateField, IntermediateField.subset_adjoin, Set.mem_singleton, Submodule, Submodule.fg_iff_finiteDimensional, b.finiteDimensional_of_finite, contrapose, fg_iff_finiteDimensional, finiteDimensional_of_finite, mem_singleton, norm_eq_one_of_not_exists_basis, of_mem_of_fg, subset_adjoin, toSubalgebra
-/
theorem _root_.IntermediateField.AdjoinSimple.norm_gen_eq_one {x : L} (hx : ¬IsIntegral K x) :
    norm K (AdjoinSimple.gen K x) = 1 := by
  rw [norm_eq_one_of_not_exists_basis]
  contrapose hx
  obtain ⟨s, ⟨b⟩⟩ := hx
  refine .of_mem_of_fg K⟮x⟯.toSubalgebra ?_ x ?_
  · exact (Submodule.fg_iff_finiteDimensional _).mpr (b.finiteDimensional_of_finite)
  · exact IntermediateField.subset_adjoin K _ (Set.mem_singleton x)

/--
theorem `_root_.IntermediateField.AdjoinSimple.norm_gen_eq_prod_roots` / 定理 `_root_.IntermediateField.AdjoinSimple.norm_gen_eq_prod_roots`

English:
theorem _root_.IntermediateField.AdjoinSimple.norm_gen_eq_prod_roots
  statement: (x : L)
  proof: by
  have injKxL := (algebraMap K⟮x⟯ L).injective
  by_cases hx : IsIntegral K x; swap
  · simp [minpoly.eq_zero hx, IntermediateField.AdjoinSimple.norm_gen_eq_one hx, aroots_def]
  rw [← adjoin.powerBasis_gen hx]; rw [PowerBasis.norm_gen_eq_prod_roots] <;>
    rw [adjoin.powerBasis_gen hx]; rw [← m

中文:
定理 _root_.中间域.AdjoinSimple.norm_gen_eq_prod_roots
  结论: (x : L)
  证明: by
  have injKxL := (algebraMap K⟮x⟯ L).injective
  by_cases hx : IsIntegral K x; swap
  · simp [minpoly.eq_zero hx, IntermediateField.AdjoinSimple.norm_gen_eq_one hx, aroots_def]
  rw [← adjoin.powerBasis_gen hx]; rw [PowerBasis.norm_gen_eq_prod_roots] <;>
    rw [adjoin.powerBasis_gen hx]; rw [← m

Depends on / 依赖: AdjoinSimple, AdjoinSimple.algebraMap_gen, IntermediateField, IntermediateField.AdjoinSimple.norm_gen_eq_one, IsIntegral, PowerBasis, PowerBasis.norm_gen_eq_prod_roots, adjoin, adjoin.powerBasis_gen, algebraMap, algebraMap_eq, algebraMap_gen, aroots_def, eq_zero, injKxL, injective, minpoly, minpoly.algebraMap_eq, minpoly.eq_zero, norm_gen_eq_one
-/
theorem _root_.IntermediateField.AdjoinSimple.norm_gen_eq_prod_roots (x : L)
    (hf : ((minpoly K x).map (algebraMap K F)).Splits) :
    (algebraMap K F) (norm K (AdjoinSimple.gen K x)) =
      ((minpoly K x).aroots F).prod := by
  have injKxL := (algebraMap K⟮x⟯ L).injective
  by_cases hx : IsIntegral K x; swap
  · simp [minpoly.eq_zero hx, IntermediateField.AdjoinSimple.norm_gen_eq_one hx, aroots_def]
  rw [← adjoin.powerBasis_gen hx]; rw [PowerBasis.norm_gen_eq_prod_roots] <;>
    rw [adjoin.powerBasis_gen hx]; rw [← minpoly.algebraMap_eq injKxL] <;>
    simp only [AdjoinSimple.algebraMap_gen _ _, hf]

end IntermediateField

section EqProdEmbeddings

open IntermediateField IntermediateField.AdjoinSimple Polynomial

variable (F) (E : Type*) [Field E] [Algebra K E]

/--
theorem `norm_eq_prod_embeddings_gen` / 定理 `norm_eq_prod_embeddings_gen`

English:
theorem norm_eq_prod_embeddings_gen
  statement: [Algebra R F] (pb : PowerBasis R S)
  proof: by
  let := Classical.decEq F
  rw [PowerBasis.norm_gen_eq_prod_roots pb hE]
  rw [@Fintype.prod_equiv (S ->ₐ[R] F) _ _ (PowerBasis.AlgHom.fintype pb) _ _ pb.liftEquiv'
    (fun σ => σ pb.gen) (fun x => x) ?_]
  · rw [Finset.prod_mem_multiset, Finset.prod_eq_multiset_prod, Multiset.toFinset_val,
   

中文:
定理 norm_eq_prod_embeddings_gen
  结论: [代数 R F] (pb : PowerBasis R S)
  证明: by
  let := Classical.decEq F
  rw [PowerBasis.norm_gen_eq_prod_roots pb hE]
  rw [@Fintype.prod_equiv (S ->ₐ[R] F) _ _ (PowerBasis.AlgHom.fintype pb) _ _ pb.liftEquiv'
    (fun σ => σ pb.gen) (fun x => x) ?_]
  · rw [Finset.prod_mem_multiset, Finset.prod_eq_multiset_prod, Multiset.toFinset_val,
   

Depends on / 依赖: AlgHom, Classical, Classical.decEq, Finset, Finset.prod_eq_multiset_prod, Finset.prod_mem_multiset, Fintype, Fintype.prod_equiv, Multiset, Multiset.dedup_eq_self.mpr, Multiset.map_id, Multiset.toFinset_val, PowerBasis, PowerBasis.AlgHom.fintype, PowerBasis.liftEquiv, PowerBasis.norm_gen_eq_prod_roots, _apply_coe, dedup_eq_self, fintype, liftEquiv
-/
theorem norm_eq_prod_embeddings_gen [Algebra R F] (pb : PowerBasis R S)
    (hE : ((minpoly R pb.gen).map (algebraMap R F)).Splits) (hfx : IsSeparable R pb.gen) :
    algebraMap R F (norm R pb.gen) =
      (@Finset.univ _ (PowerBasis.AlgHom.fintype pb)).prod fun σ => σ pb.gen := by
  let := Classical.decEq F
  rw [PowerBasis.norm_gen_eq_prod_roots pb hE]
  rw [@Fintype.prod_equiv (S ->ₐ[R] F) _ _ (PowerBasis.AlgHom.fintype pb) _ _ pb.liftEquiv'
    (fun σ => σ pb.gen) (fun x => x) ?_]
  · rw [Finset.prod_mem_multiset, Finset.prod_eq_multiset_prod, Multiset.toFinset_val,
      Multiset.dedup_eq_self.mpr, Multiset.map_id]
    · exact nodup_roots (.map hfx)
    · intro x; rfl
  · intro σ; simp only [PowerBasis.liftEquiv'_apply_coe]

/--
theorem `prod_embeddings_eq_finrank_pow` / 定理 `prod_embeddings_eq_finrank_pow`

English:
theorem prod_embeddings_eq_finrank_pow
  statement: [Algebra L F] [IsScalarTower K L F] [IsAlgClosed E]
  proof: by
  have : FiniteDimensional L F := FiniteDimensional.right K L F
  have : Algebra.IsSeparable L F := Algebra.isSeparable_tower_top_of_isSeparable K L F
  let : Fintype (L ->ₐ[K] E) := PowerBasis.AlgHom.fintype pb
  rw [Fintype.prod_equiv algHomEquivSigma (fun σ : F ->ₐ[K] E => _) fun σ => σ.1 pb.g

中文:
定理 prod_embeddings_eq_finrank_pow
  结论: [代数 L F] [标量塔 K L F] [是代数闭 E]
  证明: by
  have : FiniteDimensional L F := FiniteDimensional.right K L F
  have : Algebra.IsSeparable L F := Algebra.isSeparable_tower_top_of_isSeparable K L F
  let : Fintype (L ->ₐ[K] E) := PowerBasis.AlgHom.fintype pb
  rw [Fintype.prod_equiv algHomEquivSigma (fun σ : F ->ₐ[K] E => _) fun σ => σ.1 pb.g

Depends on / 依赖: AlgHom, AlgHom.card, Algebra, Algebra.IsSeparable, Algebra.isSeparable_tower_top_of_isSeparable, FiniteDimensional, FiniteDimensional.right, Finset, Finset.prod_congr, Finset.prod_const, Finset.prod_pow, Finset.prod_sigma, Finset.univ_sigma_univ, Fintype, Fintype.prod_equiv, IsSeparable, PowerBasis, PowerBasis.AlgHom.fintype, algHomEquivSigma, fintype
-/
theorem prod_embeddings_eq_finrank_pow [Algebra L F] [IsScalarTower K L F] [IsAlgClosed E]
    [Algebra.IsSeparable K F] [FiniteDimensional K F] (pb : PowerBasis K L) :
    ∏ σ : F ->ₐ[K] E, σ (algebraMap L F pb.gen) =
      ((@Finset.univ _ (PowerBasis.AlgHom.fintype pb)).prod
        fun σ : L ->ₐ[K] E => σ pb.gen) ^ finrank L F := by
  have : FiniteDimensional L F := FiniteDimensional.right K L F
  have : Algebra.IsSeparable L F := Algebra.isSeparable_tower_top_of_isSeparable K L F
  let : Fintype (L ->ₐ[K] E) := PowerBasis.AlgHom.fintype pb
  rw [Fintype.prod_equiv algHomEquivSigma (fun σ : F ->ₐ[K] E => _) fun σ => σ.1 pb.gen,
    ← Finset.univ_sigma_univ, Finset.prod_sigma, ← Finset.prod_pow]
  · refine Finset.prod_congr rfl fun σ _ => ?_
    let : Algebra L E := σ.toRingHom.toAlgebra
    simp_rw [Finset.prod_const]
    congr
    exact AlgHom.card L F E
  · intro σ
    simp only [algHomEquivSigma, Equiv.coe_fn_mk, AlgHom.domRestrict, AlgHom.comp_apply,
      IsScalarTower.coe_toAlgHom']

/--
lemma `norm_eq_of_algEquiv` / 引理 `norm_eq_of_algEquiv`

English:
lemma norm_eq_of_algEquiv
  given: [Ring T] [Algebra R T] (e : S ≃ₐ[R] T) (x)
  proof: by
  simp_rw [Algebra.norm_apply, ← LinearMap.det_conj _ e.toLinearEquiv]; congr; ext; simp

中文:
引理 norm_eq_of_algEquiv
  条件: [环 T] [代数 R T] (e : S ≃ₐ[R] T) (x)
  证明: by
  simp_rw [Algebra.norm_apply, ← LinearMap.det_conj _ e.toLinearEquiv]; congr; ext; simp

Depends on / 依赖: Algebra, Algebra.norm_apply, LinearMap, LinearMap.det_conj, det_conj, e.toLinearEquiv, norm_apply, simp_rw, toLinearEquiv
-/
lemma norm_eq_of_algEquiv [Ring T] [Algebra R T] (e : S ≃ₐ[R] T) (x) :
    Algebra.norm R (e x) = Algebra.norm R x := by
  simp_rw [Algebra.norm_apply, ← LinearMap.det_conj _ e.toLinearEquiv]; congr; ext; simp

set_option backward.isDefEq.respectTransparency false in
/--
lemma `norm_eq_of_ringEquiv` / 引理 `norm_eq_of_ringEquiv`

English:
lemma norm_eq_of_ringEquiv
  statement: {A B C : Type*} [CommRing A] [CommRing B] [Ring C]
  proof: by
  classical
  by_cases h : exists s : Finset C, Nonempty (Basis s B C)
  · obtain ⟨s, ⟨b⟩⟩ := h
    let : Algebra A B := RingHom.toAlgebra e
    let : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq' he.symm
    rw [Algebra.norm_eq_matrix_det b]; rw [Algebra.norm_eq_matrix_det (b.mapCoeffs 

中文:
引理 norm_eq_of_ringEquiv
  结论: {A B C : 类型} [交换环 A] [交换环 B] [环 C]
  证明: by
  classical
  by_cases h : exists s : Finset C, Nonempty (Basis s B C)
  · obtain ⟨s, ⟨b⟩⟩ := h
    let : Algebra A B := RingHom.toAlgebra e
    let : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq' he.symm
    rw [Algebra.norm_eq_matrix_det b]; rw [Algebra.norm_eq_matrix_det (b.mapCoeffs 

Depends on / 依赖: Algebra, Algebra.norm_eq_matrix_det, Algebra.smul_def, Finset, IsScalarTower, IsScalarTower.of_algebraMap_eq, LinearMap, LinearMap.toMatrix_apply, Nonempty, RingHom, RingHom.toAlgebra, b.mapCoeffs, classical, e.map_det, e.symm, he.symm, leftMulMatrix_apply, mapCoeffs, map_det, map_one
-/
lemma norm_eq_of_ringEquiv {A B C : Type*} [CommRing A] [CommRing B] [Ring C]
    [Algebra A C] [Algebra B C] (e : A ≃+* B) (he : (algebraMap B C).comp e = algebraMap A C)
    (x : C) :
    e (Algebra.norm A x) = Algebra.norm B x := by
  classical
  by_cases h : exists s : Finset C, Nonempty (Basis s B C)
  · obtain ⟨s, ⟨b⟩⟩ := h
    let : Algebra A B := RingHom.toAlgebra e
    let : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq' he.symm
    rw [Algebra.norm_eq_matrix_det b]; rw [Algebra.norm_eq_matrix_det (b.mapCoeffs e.symm (by simp [Algebra.smul_def]; rw [← he])),
      e.map_det]
    congr
    ext i j
    simp [leftMulMatrix_apply, LinearMap.toMatrix_apply]
  rw [norm_eq_one_of_not_exists_basis _ h]; rw [norm_eq_one_of_not_exists_basis]; rw [map_one]
  intro ⟨s, ⟨b⟩⟩
  exact h ⟨s, ⟨b.mapCoeffs e (by simp [Algebra.smul_def, ← he])⟩⟩

/--
lemma `norm_eq_of_equiv_equiv` / 引理 `norm_eq_of_equiv_equiv`

English:
lemma norm_eq_of_equiv_equiv
  statement: {A₁ B₁ A₂ B₂ : Type*} [CommRing A₁] [Ring B₁]
  proof: by
  let := (RingHom.comp (e₂ : B₁ ->+* B₂) (algebraMap A₁ B₁)).toAlgebra' ?_
  · let e' : B₁ ≃ₐ[A₁] B₂ := { e₂ with commutes' := fun _ => rfl }
    rw [← Algebra.norm_eq_of_ringEquiv e₁ he]; rw [← Algebra.norm_eq_of_algEquiv e']
    simp [e']
  intro c x
  apply e₂.symm.injective
  simp only [RingH

中文:
引理 norm_eq_of_equiv_equiv
  结论: {A₁ B₁ A₂ B₂ : 类型} [交换环 A₁] [环 B₁]
  证明: by
  let := (RingHom.comp (e₂ : B₁ ->+* B₂) (algebraMap A₁ B₁)).toAlgebra' ?_
  · let e' : B₁ ≃ₐ[A₁] B₂ := { e₂ with commutes' := fun _ => rfl }
    rw [← Algebra.norm_eq_of_ringEquiv e₁ he]; rw [← Algebra.norm_eq_of_algEquiv e']
    simp [e']
  intro c x
  apply e₂.symm.injective
  simp only [RingH

Depends on / 依赖: Algebra, Algebra.norm_eq_of_algEquiv, Algebra.norm_eq_of_ringEquiv, Function, Function.comp_apply, RingEquiv, RingEquiv.symm_apply_apply, RingHom, RingHom.coe_coe, RingHom.coe_comp, RingHom.comp, algebraMap, coe_coe, coe_comp, commutes, comp_apply, injective, map_mul, norm_eq_of_algEquiv, norm_eq_of_ringEquiv
-/
lemma norm_eq_of_equiv_equiv {A₁ B₁ A₂ B₂ : Type*} [CommRing A₁] [Ring B₁]
    [CommRing A₂] [Ring B₂] [Algebra A₁ B₁] [Algebra A₂ B₂] (e₁ : A₁ ≃+* A₂) (e₂ : B₁ ≃+* B₂)
    (he : RingHom.comp (algebraMap A₂ B₂) ↑e₁ = RingHom.comp ↑e₂ (algebraMap A₁ B₁)) (x) :
    Algebra.norm A₁ x = e₁.symm (Algebra.norm A₂ (e₂ x)) := by
  let := (RingHom.comp (e₂ : B₁ ->+* B₂) (algebraMap A₁ B₁)).toAlgebra' ?_
  · let e' : B₁ ≃ₐ[A₁] B₂ := { e₂ with commutes' := fun _ => rfl }
    rw [← Algebra.norm_eq_of_ringEquiv e₁ he]; rw [← Algebra.norm_eq_of_algEquiv e']
    simp [e']
  intro c x
  apply e₂.symm.injective
  simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, map_mul,
    RingEquiv.symm_apply_apply, commutes]

end EqProdEmbeddings

end Algebra
