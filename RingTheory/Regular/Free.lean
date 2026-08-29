/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.Finsupp
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.QuotSMulTop

/-!

# Freeness of `QuotSMulTop` by a regular element

Let `M` be a finitely presented module over a commutative ring `R`. If `x` is in the
Jacobson radical of `R` and `x` is `M`-regular, then `M/xM` is free over `R/(x)` if and only if
`M` is free over `R`.

-/

public section

variable (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Module.Free
  signature: R M] (x
  body: Module.Free.of_equiv ((QuotSMulTop.equivQuotTensor x M).extendScalarsOfSurjective
    Ideal.Quotient.mk_surjective).symm

中文:
实例 [Module.Free
  签名: R M] (x
  定义体: Module.Free.of_equiv ((QuotSMulTop.equivQuotTensor x M).extendScalarsOfSurjective
    Ideal.Quotient.mk_surjective).symm

Depends on / 依赖: Ideal.Quotient.mk_surjective, Module, Module.Free.of_equiv, QuotSMulTop, QuotSMulTop.equivQuotTensor, Quotient, equivQuotTensor, extendScalarsOfSurjective, mk_surjective, of_equiv
-/
instance [Module.Free R M] (x : R) : Module.Free (R ⧸ Ideal.span {x}) (QuotSMulTop x M) :=
  Module.Free.of_equiv ((QuotSMulTop.equivQuotTensor x M).extendScalarsOfSurjective
    Ideal.Quotient.mk_surjective).symm

open Pointwise in
/--
lemma `Module.free_quotSMulTop_iff_free` / 引理 `Module.free_quotSMulTop_iff_free`

English:
lemma Module.free_quotSMulTop_iff_free
  statement: [Module.FinitePresentation R M] {x : R}
  proof: by
  refine ⟨fun free => ?_, fun free => inferInstance⟩
  have := Module.Finite.of_restrictScalars_finite R (R ⧸ Ideal.span {x}) (QuotSMulTop x M)
  let I := Module.Free.ChooseBasisIndex (R ⧸ Ideal.span {x}) (QuotSMulTop x M)
  let b := Module.Free.chooseBasis (R ⧸ Ideal.span {x}) (QuotSMulTop x M)


中文:
引理 Module.free_quotSMulTop_iff_free
  结论: [Module.FinitePresentation R M] {x : R}
  证明: by
  refine ⟨fun free => ?_, fun free => inferInstance⟩
  have := Module.Finite.of_restrictScalars_finite R (R ⧸ Ideal.span {x}) (QuotSMulTop x M)
  let I := Module.Free.ChooseBasisIndex (R ⧸ Ideal.span {x}) (QuotSMulTop x M)
  let b := Module.Free.chooseBasis (R ⧸ Ideal.span {x}) (QuotSMulTop x M)


Depends on / 依赖: ChooseBasisIndex, Finite, Finsupp, Finsupp.mapRange.linearMap, Ideal.span, Module, Module.Finite.of_restrictScalars_finite, Module.Free.ChooseBasisIndex, Module.Free.chooseBasis, Module.projective_liftin, QuotSMulTop, Submodule, Submodule.mkQ, chooseBasis, linearMap, mapRange, of_restrictScalars_finite, projective_liftin, restrictScalars, symm.toLinearMap.comp
-/
lemma Module.free_quotSMulTop_iff_free [Module.FinitePresentation R M] {x : R}
    (mem : x in (⊥ : Ideal R).jacobson) (reg : IsSMulRegular M x) :
    Module.Free (R ⧸ Ideal.span {x}) (QuotSMulTop x M) ↔ Module.Free R M := by
  refine ⟨fun free => ?_, fun free => inferInstance⟩
  have := Module.Finite.of_restrictScalars_finite R (R ⧸ Ideal.span {x}) (QuotSMulTop x M)
  let I := Module.Free.ChooseBasisIndex (R ⧸ Ideal.span {x}) (QuotSMulTop x M)
  let b := Module.Free.chooseBasis (R ⧸ Ideal.span {x}) (QuotSMulTop x M)
  let b' : QuotSMulTop x M ≃ₗ[R] I ->₀ R ⧸ Ideal.span {x} := b.1.restrictScalars R
  let f := b'.symm.toLinearMap.comp (Finsupp.mapRange.linearMap (Submodule.mkQ (Ideal.span {x})))
  rcases Module.projective_lifting_property (Submodule.mkQ (x • (⊤ : Submodule R M))) f
    (Submodule.mkQ_surjective _) with ⟨g, hg⟩
  have surjf : Function.Surjective f := by
    simpa [f] using! Finsupp.mapRange_surjective _ rfl (Submodule.mkQ_surjective (Ideal.span {x}))
  have lejac : Ideal.span {x} <= (⊥ :Ideal R).jacobson := by simpa
  have surjg : Function.Surjective g := by
    apply g.surjective_of_surjective_comp_mkQ (Ideal.span {x}) lejac
    rwa [Submodule.ideal_span_singleton_smul x ⊤, hg]
  have kerf : LinearMap.ker f = x • (⊤ : Submodule R (I ->₀ R)) := by
    simp only [LinearEquiv.ker_comp, f]
    rw [Finsupp.ker_mapRange]; rw [Submodule.ker_mkQ]; rw [← (Ideal.span {x}).mul_top]; rw [← smul_eq_mul]; rw [Finsupp.submodule_smul]
    simp [Submodule.ideal_span_singleton_smul]
  have injg : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot]
    have fg : (LinearMap.ker g).FG := Module.FinitePresentation.fg_ker g surjg
    apply Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (Ideal.span {x}) _ fg _ lejac
    rw [Submodule.ideal_span_singleton_smul]
    intro y hy
    have : y in x • (⊤ : Submodule R (I ->₀ R)) := by simp [← kerf, ← hg, LinearMap.mem_ker.mp hy]
    rcases (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp this with ⟨z, _, hz⟩
    simp only [← hz, LinearMap.mem_ker, map_smul] at hy
    have := LinearMap.mem_ker.mpr (IsSMulRegular.right_eq_zero_of_smul reg hy)
    simpa [hz] using Submodule.smul_mem_pointwise_smul z x _ this
  exact Module.Free.of_equiv (LinearEquiv.ofBijective g ⟨injg, surjg⟩)
