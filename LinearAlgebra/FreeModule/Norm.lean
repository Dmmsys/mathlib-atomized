/-
Copyright (c) 2023 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Norm.Defs

/-!
# Norms on free modules over principal ideal domains
-/

public section

open Ideal Module Polynomial

variable {R S ι : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [CommRing S]
  [IsDomain S] [Algebra R S]

section CommRing

variable (F : Type*)

/--
theorem `associated_norm_prod_smith` / 定理 `associated_norm_prod_smith`

English:
theorem associated_norm_prod_smith
  given: [Fintype ι] (b : Basis ι R S) {f : S} (hf : f != 0)
  proof: by
  have hI := span_singleton_eq_bot.not.2 hf
  let b' := ringBasis b (span {f}) hI
  classical
  rw [← Matrix.det_diagonal]; rw [← LinearMap.det_toLin b']
  let e :=
    (b'.equiv ((span {f}).selfBasis b hI) <| Equiv.refl _).trans
      ((LinearEquiv.coord S S f hf).restrictScalars R)
  refine (Li

中文:
定理 associated_norm_prod_smith
  条件: [Fintype ι] (b : Basis ι R S) {f : S} (hf : f != 0)
  证明: by
  have hI := span_singleton_eq_bot.not.2 hf
  let b' := ringBasis b (span {f}) hI
  classical
  rw [← Matrix.det_diagonal]; rw [← LinearMap.det_toLin b']
  let e :=
    (b'.equiv ((span {f}).selfBasis b hI) <| Equiv.refl _).trans
      ((LinearEquiv.coord S S f hf).restrictScalars R)
  refine (Li

Depends on / 依赖: Equiv.refl, LinearEquiv, LinearEquiv.coe_toLinearMap, LinearEquiv.coord, LinearEquiv.trans_apply, LinearMap, LinearMap.associated_det_of_eq_comp, LinearMap.com, LinearMap.comp_apply, LinearMap.det_toLin, LinearMap.ext_iff, Matrix, Matrix.det_diagonal, associated_det_of_eq_comp, classical, coe_toLinearMap, comp_apply, det_diagonal, det_toLin, ext_iff
-/
theorem associated_norm_prod_smith [Fintype ι] (b : Basis ι R S) {f : S} (hf : f != 0) :
    Associated (Algebra.norm R f) (∏ i, smithCoeffs b _ (span_singleton_eq_bot.not.2 hf) i) := by
  have hI := span_singleton_eq_bot.not.2 hf
  let b' := ringBasis b (span {f}) hI
  classical
  rw [← Matrix.det_diagonal]; rw [← LinearMap.det_toLin b']
  let e :=
    (b'.equiv ((span {f}).selfBasis b hI) <| Equiv.refl _).trans
      ((LinearEquiv.coord S S f hf).restrictScalars R)
  refine (LinearMap.associated_det_of_eq_comp e _ _ ?_).symm
  dsimp only [e, LinearEquiv.trans_apply]
  simp_rw [← LinearEquiv.coe_toLinearMap, ← LinearMap.comp_apply, ← LinearMap.ext_iff]
  refine b'.ext fun i => ?_
  simp_rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, Matrix.toLin_apply, Basis.repr_self,
    Finsupp.single_eq_pi_single, Matrix.diagonal_mulVec_single, Pi.single_apply, ite_smul,
    zero_smul, Finset.sum_ite_eq', mul_one, if_pos (Finset.mem_univ _), b'.equiv_apply]
  change _ = f * _
  rw [mul_comm]; rw [← smul_eq_mul]; rw [LinearEquiv.restrictScalars_apply]; rw [LinearEquiv.coord_apply_smul]
  grind [Ideal.selfBasis_def]

end CommRing

section Field

variable {F : Type*} [Field F] [Algebra F[X] S] [Finite ι]

instance (b : Basis ι F[X] S) {I : Ideal S} (hI : I != ⊥) (i : ι) :
    FiniteDimensional F (F[X] ⧸ span ({I.smithCoeffs b hI i} : Set F[X])) :=
PowerBasis.finite AdjoinRoot.powerBasis I.smithCoeffs_ne_zero b hI i

/--
theorem `finrank_quotient_span_eq_natDegree_norm` / 定理 `finrank_quotient_span_eq_natDegree_norm`

English:
theorem finrank_quotient_span_eq_natDegree_norm
  statement: [Algebra F S] [IsScalarTower F F[X] S]
  proof: by
  have := Fintype.ofFinite ι
  have h := span_singleton_eq_bot.not.2 hf
  rw [natDegree_eq_of_degree_eq
      (degree_eq_degree_of_associated <| associated_norm_prod_smith b hf)]
  rw [natDegree_prod _ _ fun i _ => smithCoeffs_ne_zero b _ h i]; rw [finrank_quotient_eq_sum F h b]
  congr with i
  

中文:
定理 finrank_quotient_span_eq_natDegree_norm
  结论: [Algebra F S] [IsScalarTower F F[X] S]
  证明: by
  have := Fintype.ofFinite ι
  have h := span_singleton_eq_bot.not.2 hf
  rw [natDegree_eq_of_degree_eq
      (degree_eq_degree_of_associated <| associated_norm_prod_smith b hf)]
  rw [natDegree_prod _ _ fun i _ => smithCoeffs_ne_zero b _ h i]; rw [finrank_quotient_eq_sum F h b]
  congr with i
  

Depends on / 依赖: AdjoinRoot, AdjoinRoot.powerBasis, Fintype, Fintype.ofFinite, associated_norm_prod_smith, degree_eq_degree_of_associated, finrank, finrank_quotient_eq_sum, natDegree_eq_of_degree_eq, natDegree_prod, ofFinite, powerBasis, smithCoeffs_ne_zero, span_singleton_eq_bot, span_singleton_eq_bot.not
-/
theorem finrank_quotient_span_eq_natDegree_norm [Algebra F S] [IsScalarTower F F[X] S]
    (b : Basis ι F[X] S) {f : S} (hf : f != 0) :
    Module.finrank F (S ⧸ span ({f} : Set S)) = (Algebra.norm F[X] f).natDegree := by
  have := Fintype.ofFinite ι
  have h := span_singleton_eq_bot.not.2 hf
  rw [natDegree_eq_of_degree_eq
      (degree_eq_degree_of_associated <| associated_norm_prod_smith b hf)]
  rw [natDegree_prod _ _ fun i _ => smithCoeffs_ne_zero b _ h i]; rw [finrank_quotient_eq_sum F h b]
  congr with i
  exact (AdjoinRoot.powerBasis <| smithCoeffs_ne_zero b _ h i).finrank

end Field
