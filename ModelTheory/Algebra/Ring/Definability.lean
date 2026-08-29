/-
Copyright (c) 2023 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.ModelTheory.Definability
public import Mathlib.RingTheory.MvPolynomial.FreeCommRing
public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.ModelTheory.Algebra.Ring.FreeCommRing

/-!

# Definable Subsets in the language of rings

This file proves that the set of zeros of a multivariable polynomial is a definable subset.

-/

public section

namespace FirstOrder

namespace Ring

open MvPolynomial Language BoundedFormula

/--
theorem `mvPolynomial_zeroLocus_definable` / 定理 `mvPolynomial_zeroLocus_definable`

English:
theorem mvPolynomial_zeroLocus_definable
  statement: {ι K : Type*} [Field K]
  proof: by
  rw [Set.definable_iff_exists_formula_sum]
  let p' := genericPolyMap (fun p : S => p.1.support)
  let := Classical.decEq ι
  let := Classical.decEq K
  rw [MvPolynomial.zeroLocus_span]
  refine ⟨BoundedFormula.iInf
      (fun i : S => Term.equal
        ((termOfFreeCommRing (p' i)).relabel
    

中文:
定理 mvPolynomial_zeroLocus_definable
  结论: {ι K : 类型} [Field K]
  证明: by
  rw [Set.definable_iff_exists_formula_sum]
  let p' := genericPolyMap (fun p : S => p.1.support)
  let := Classical.decEq ι
  let := Classical.decEq K
  rw [MvPolynomial.zeroLocus_span]
  refine ⟨BoundedFormula.iInf
      (fun i : S => Term.equal
        ((termOfFreeCommRing (p' i)).relabel
    

Depends on / 依赖: BoundedFormula, BoundedFormula.iInf, Classical, Classical.decEq, Formula, Formula.Realize, Function, Function.comp_def, MvPolynomial, MvPolynomial.aeval_eq_eval, MvPolynomial.zeroLocus_span, Realize, Set.definable_iff_exists_formula_sum, Set.mem_iUnion, Set.mem_image_of_mem, Sum.map, Term.equal, comp_def, definable_iff_exists_formula_sum, genericPolyMap
-/
theorem mvPolynomial_zeroLocus_definable {ι K : Type*} [Field K]
    [CompatibleRing K] (S : Finset (MvPolynomial ι K)) :
    Set.Definable (⋃ p in S, p.coeff '' p.support : Set K) Language.ring
      (zeroLocus K (Ideal.span (S : Set (MvPolynomial ι K)))) := by
  rw [Set.definable_iff_exists_formula_sum]
  let p' := genericPolyMap (fun p : S => p.1.support)
  let := Classical.decEq ι
  let := Classical.decEq K
  rw [MvPolynomial.zeroLocus_span]
  refine ⟨BoundedFormula.iInf
      (fun i : S => Term.equal
        ((termOfFreeCommRing (p' i)).relabel
          (Sum.map (fun p => ⟨p.1.1.coeff p.2.1, by
            simp only [Set.mem_iUnion]
            exact ⟨p.1.1, p.1.2, Set.mem_image_of_mem _ p.2.2⟩⟩) id)) 0), ?_⟩
  simp [Formula.Realize, Term.equal, Function.comp_def, p', MvPolynomial.aeval_eq_eval₂Hom]

end Ring

end FirstOrder
