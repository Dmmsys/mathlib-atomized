/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.RingTheory.Trace.Basic
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# The trace and norm maps for finite fields

We state several lemmas about the trace and norm maps for finite fields.

## Main Results

- `trace_to_zmod_nondegenerate`: the trace map from a finite field of characteristic `p` to
  `ZMod p` is nondegenerate.
- `algebraMap_trace_eq_sum_pow`: an explicit formula for the trace map:
  `trace[L/K](x) = ∑ i < [L:K], x ^ ((#K) ^ i)`.
- `algebraMap_norm_eq_prod_pow`: an explicit formula for the norm map:
  `norm[L/K](x) = ∏ i < [L:K], x ^ ((#K) ^ i)`.

## Tags
finite field, trace, norm
-/

public section


namespace FiniteField

open Fintype

/--
theorem `trace_to_zmod_nondegenerate` / 定理 `trace_to_zmod_nondegenerate`

English:
theorem trace_to_zmod_nondegenerate
  statement: (F : Type*) [Field F] [Finite F]
  proof: by
  have : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F _⟩
  have htr := (traceForm_nondegenerate (ZMod (ringChar F)) F).1 a
  simp_rw [Algebra.traceForm_apply] at htr
  by_contra! hf
  exact ha (htr hf)

中文:
定理 trace_to_zmod_nondegenerate
  结论: (F : 类型) [Field F] [Finite F]
  证明: by
  have : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F _⟩
  have htr := (traceForm_nondegenerate (ZMod (ringChar F)) F).1 a
  simp_rw [Algebra.traceForm_apply] at htr
  by_contra! hf
  exact ha (htr hf)

Depends on / 依赖: Algebra, Algebra.traceForm_apply, CharP.char_is_prime, char_is_prime, ringChar, simp_rw, traceForm_apply, traceForm_nondegenerate
-/
theorem trace_to_zmod_nondegenerate (F : Type*) [Field F] [Finite F]
    [Algebra (ZMod (ringChar F)) F] {a : F} (ha : a != 0) :
    exists b : F, Algebra.trace (ZMod (ringChar F)) F (a * b) != 0 := by
  have : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F _⟩
  have htr := (traceForm_nondegenerate (ZMod (ringChar F)) F).1 a
  simp_rw [Algebra.traceForm_apply] at htr
  by_contra! hf
  exact ha (htr hf)

variable (K L : Type*) [Field K] [Field L] [Finite L] [Algebra K L] (x : L)

/--
theorem `algebraMap_trace_eq_sum_pow` / 定理 `algebraMap_trace_eq_sum_pow`

English:
theorem algebraMap_trace_eq_sum_pow
  proof: by
  have := Finite.of_injective _ (FaithfulSMul.algebraMap_injective K L)
  have := ofFinite K
  rw [trace_eq_sum_automorphisms]; rw [Finset.sum_range]
exact Eq.symm sum_bijective _ (bijective_frobeniusAlgEquivOfAlgebraic_pow K L) _ _
    fun i => by rw [AlgEquiv.coe_pow, coe_frobeniusAlgEquivOfAlg

中文:
定理 algebraMap_trace_eq_sum_pow
  证明: by
  have := Finite.of_injective _ (FaithfulSMul.algebraMap_injective K L)
  have := ofFinite K
  rw [trace_eq_sum_automorphisms]; rw [Finset.sum_range]
exact Eq.symm sum_bijective _ (bijective_frobeniusAlgEquivOfAlgebraic_pow K L) _ _
    fun i => by rw [AlgEquiv.coe_pow, coe_frobeniusAlgEquivOfAlg

Depends on / 依赖: AlgEquiv, AlgEquiv.coe_pow, Eq.symm, FaithfulSMul, FaithfulSMul.algebraMap_injective, Finite, Finite.of_injective, Finset, Finset.sum_range, algebraMap_injective, bijective_frobeniusAlgEquivOfAlgebraic_pow, card_eq_nat_card, coe_frobeniusAlgEquivOfAlgebraic_iterate, coe_pow, ofFinite, of_injective, sum_bijective, sum_range, trace_eq_sum_automorphisms
-/
theorem algebraMap_trace_eq_sum_pow :
    algebraMap K L (Algebra.trace K L x) =
      ∑ i in Finset.range (Module.finrank K L), x ^ (Nat.card K ^ i) := by
  have := Finite.of_injective _ (FaithfulSMul.algebraMap_injective K L)
  have := ofFinite K
  rw [trace_eq_sum_automorphisms]; rw [Finset.sum_range]
exact Eq.symm sum_bijective _ (bijective_frobeniusAlgEquivOfAlgebraic_pow K L) _ _
    fun i => by rw [AlgEquiv.coe_pow, coe_frobeniusAlgEquivOfAlgebraic_iterate, card_eq_nat_card]

/--
theorem `algebraMap_norm_eq_prod_pow` / 定理 `algebraMap_norm_eq_prod_pow`

English:
theorem algebraMap_norm_eq_prod_pow
  proof: by
  have := Finite.of_injective _ (FaithfulSMul.algebraMap_injective K L)
  have := ofFinite K
  rw [Algebra.norm_eq_prod_automorphisms]; rw [Finset.prod_range]
exact Eq.symm prod_bijective _ (bijective_frobeniusAlgEquivOfAlgebraic_pow K L) _ _
    fun i => by rw [AlgEquiv.coe_pow, coe_frobeniusAlg

中文:
定理 algebraMap_norm_eq_prod_pow
  证明: by
  have := Finite.of_injective _ (FaithfulSMul.algebraMap_injective K L)
  have := ofFinite K
  rw [Algebra.norm_eq_prod_automorphisms]; rw [Finset.prod_range]
exact Eq.symm prod_bijective _ (bijective_frobeniusAlgEquivOfAlgebraic_pow K L) _ _
    fun i => by rw [AlgEquiv.coe_pow, coe_frobeniusAlg

Depends on / 依赖: AlgEquiv, AlgEquiv.coe_pow, Algebra, Algebra.norm_eq_prod_automorphisms, Eq.symm, FaithfulSMul, FaithfulSMul.algebraMap_injective, Finite, Finite.of_injective, Finset, Finset.prod_range, algebraMap_injective, bijective_frobeniusAlgEquivOfAlgebraic_pow, card_eq_nat_card, coe_frobeniusAlgEquivOfAlgebraic_iterate, coe_pow, norm_eq_prod_automorphisms, ofFinite, of_injective, prod_bijective
-/
theorem algebraMap_norm_eq_prod_pow :
    algebraMap K L (Algebra.norm K x) =
      ∏ i in Finset.range (Module.finrank K L), x ^ (Nat.card K ^ i) := by
  have := Finite.of_injective _ (FaithfulSMul.algebraMap_injective K L)
  have := ofFinite K
  rw [Algebra.norm_eq_prod_automorphisms]; rw [Finset.prod_range]
exact Eq.symm prod_bijective _ (bijective_frobeniusAlgEquivOfAlgebraic_pow K L) _ _
    fun i => by rw [AlgEquiv.coe_pow, coe_frobeniusAlgEquivOfAlgebraic_iterate, card_eq_nat_card]

/--
theorem `algebraMap_norm_eq_pow_sum` / 定理 `algebraMap_norm_eq_pow_sum`

English:
theorem algebraMap_norm_eq_pow_sum
  proof: by
  rw [algebraMap_norm_eq_prod_pow]; rw [Finset.prod_pow_eq_pow_sum]

中文:
定理 algebraMap_norm_eq_pow_sum
  证明: by
  rw [algebraMap_norm_eq_prod_pow]; rw [Finset.prod_pow_eq_pow_sum]

Depends on / 依赖: Finset, Finset.prod_pow_eq_pow_sum, algebraMap_norm_eq_prod_pow, prod_pow_eq_pow_sum
-/
theorem algebraMap_norm_eq_pow_sum :
    algebraMap K L (Algebra.norm K x) =
      x ^ ∑ i in Finset.range (Module.finrank K L), Nat.card K ^ i := by
  rw [algebraMap_norm_eq_prod_pow]; rw [Finset.prod_pow_eq_pow_sum]

end FiniteField
