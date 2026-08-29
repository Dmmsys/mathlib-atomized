/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.FractionalIdeal.Norm
public import Mathlib.RingTheory.FractionalIdeal.Operations

/-!

# Fractional ideals of number fields

Prove some results on the fractional ideals of number fields.

## Main definitions and results

* `NumberField.basisOfFractionalIdeal`: A `ℚ`-basis of `K` that spans `I` over `ℤ` where `I` is
  a fractional ideal of a number field `K`.
* `NumberField.det_basisOfFractionalIdeal_eq_absNorm`: for `I` a fractional ideal of a number
  field `K`, the absolute value of the determinant of the base change from `integralBasis` to
  `basisOfFractionalIdeal I` is equal to the norm of `I`.
-/

@[expose] public section

variable (K : Type*) [Field K] [NumberField K]

namespace NumberField

open scoped nonZeroDivisors

section Basis

open Module

instance (I : FractionalIdeal (𝓞 K)⁰ K) : Module.Free Int I := by
  refine Free.of_equiv (LinearEquiv.restrictScalars Int (I.equivNum ?_)).symm
  exact nonZeroDivisors.coe_ne_zero I.den

instance (I : FractionalIdeal (𝓞 K)⁰ K) : Module.Finite Int I := by
  refine Module.Finite.of_surjective
    (LinearEquiv.restrictScalars Int (I.equivNum ?_)).symm.toLinearMap (LinearEquiv.surjective _)
  exact nonZeroDivisors.coe_ne_zero I.den

instance (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    IsLocalizedModule Int⁰ ((Submodule.subtype (I : Submodule (𝓞 K) K)).restrictScalars Int) where
  map_units x := by
    rw [← (Algebra.lmul _ _).commutes]; rw [Algebra.lmul_isUnit_iff]; rw [isUnit_iff_ne_zero]; rw [eq_intCast]; rw [Int.cast_ne_zero]
    exact nonZeroDivisors.coe_ne_zero x
  surj x := by
    obtain ⟨⟨a, _, d, hd, rfl⟩, h⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid (𝓞 K) Int⁰) x
    refine ⟨⟨⟨Ideal.absNorm I.1.num * (algebraMap _ K a), I.1.num_le ?_⟩, d * Ideal.absNorm I.1.num,
      ?_⟩, ?_⟩
    · refine (IsLocalization.mem_coeSubmodule _ _).mpr ⟨Ideal.absNorm I.1.num * a, ?_, ?_⟩
      · exact Ideal.mul_mem_right _ _ I.1.num.absNorm_mem
      · rw [map_mul, map_natCast]
    · refine Submonoid.mul_mem _ hd (mem_nonZeroDivisors_of_ne_zero ?_)
      rw [Nat.cast_ne_zero]; rw [ne_eq]; rw [Ideal.absNorm_eq_zero_iff]
exact FractionalIdeal.num_eq_zero_iff.not.mpr Units.ne_zero I
    · simp_rw [LinearMap.coe_restrictScalars, Submodule.coe_subtype] at h ⊢
      rw [← h]
      simp only [Submonoid.mk_smul, zsmul_eq_mul, Int.cast_mul, Int.cast_natCast, algebraMap_int_eq,
        eq_intCast, map_intCast]
      ring
  exists_of_eq h :=
    ⟨1, by rwa [one_smul, one_smul, ← (Submodule.injective_subtype I.1.coeToSubmodule).eq_iff]⟩

/--
Definition of `fractionalIdealBasis` / `fractionalIdealBasis` 的定义

English:
definition fractionalIdealBasis
  signature: (I : FractionalIdeal (𝓞 K)⁰ K)
  body: Free.chooseBasis Int I

中文:
定义 fractionalIdealBasis
  签名: (I : FractionalIdeal (𝓞 K)⁰ K)
  定义体: Free.chooseBasis Int I

Depends on / 依赖: Free.chooseBasis, chooseBasis
-/
noncomputable def fractionalIdealBasis (I : FractionalIdeal (𝓞 K)⁰ K) :
    Basis (Free.ChooseBasisIndex Int I) Int I := Free.chooseBasis Int I

/--
Definition of `basisOfFractionalIdeal` / `basisOfFractionalIdeal` 的定义

English:
definition basisOfFractionalIdeal
  signature: (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
  body: (fractionalIdealBasis K I.1).ofIsLocalizedModule Rat Int⁰
    ((Submodule.subtype (I : Submodule (𝓞 K) K)).restrictScalars Int)

中文:
定义 basisOfFractionalIdeal
  签名: (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
  定义体: (fractionalIdealBasis K I.1).ofIsLocalizedModule Rat Int⁰
    ((Submodule.subtype (I : Submodule (𝓞 K) K)).restrictScalars Int)

Depends on / 依赖: Submodule, Submodule.subtype, fractionalIdealBasis, ofIsLocalizedModule, restrictScalars, subtype
-/
noncomputable def basisOfFractionalIdeal (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Basis (Free.ChooseBasisIndex Int I) Rat K :=
  (fractionalIdealBasis K I.1).ofIsLocalizedModule Rat Int⁰
    ((Submodule.subtype (I : Submodule (𝓞 K) K)).restrictScalars Int)

/--
theorem `basisOfFractionalIdeal_apply` / 定理 `basisOfFractionalIdeal_apply`

English:
theorem basisOfFractionalIdeal_apply
  statement: (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
  proof: (fractionalIdealBasis K I.1).ofIsLocalizedModule_apply Rat Int⁰ _ i

中文:
定理 basisOfFractionalIdeal_apply
  结论: (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
  证明: (fractionalIdealBasis K I.1).ofIsLocalizedModule_apply Rat Int⁰ _ i

Depends on / 依赖: fractionalIdealBasis, ofIsLocalizedModule_apply
-/
theorem basisOfFractionalIdeal_apply (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (i : Free.ChooseBasisIndex Int I) :
    basisOfFractionalIdeal K I i = fractionalIdealBasis K I.1 i :=
  (fractionalIdealBasis K I.1).ofIsLocalizedModule_apply Rat Int⁰ _ i

/--
theorem `mem_span_basisOfFractionalIdeal` / 定理 `mem_span_basisOfFractionalIdeal`

English:
theorem mem_span_basisOfFractionalIdeal
  given: {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {x : K}
  proof: by
  rw [basisOfFractionalIdeal]; rw [(fractionalIdealBasis K I.1).ofIsLocalizedModule_span Rat Int⁰ _]
  simp

中文:
定理 mem_span_basisOfFractionalIdeal
  条件: {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {x : K}
  证明: by
  rw [basisOfFractionalIdeal]; rw [(fractionalIdealBasis K I.1).ofIsLocalizedModule_span Rat Int⁰ _]
  simp

Depends on / 依赖: basisOfFractionalIdeal, fractionalIdealBasis, ofIsLocalizedModule_span
-/
theorem mem_span_basisOfFractionalIdeal {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {x : K} :
    x in Submodule.span Int (Set.range (basisOfFractionalIdeal K I)) ↔ x in (I : Set K) := by
  rw [basisOfFractionalIdeal]; rw [(fractionalIdealBasis K I.1).ofIsLocalizedModule_span Rat Int⁰ _]
  simp

open Module in
/--
theorem `fractionalIdeal_rank` / 定理 `fractionalIdeal_rank`

English:
theorem fractionalIdeal_rank
  given: (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
  proof: by
  rw [finrank_eq_card_chooseBasisIndex]; rw [RingOfIntegers.rank]; rw [finrank_eq_card_basis (basisOfFractionalIdeal K I)]

中文:
定理 fractionalIdeal_rank
  条件: (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
  证明: by
  rw [finrank_eq_card_chooseBasisIndex]; rw [RingOfIntegers.rank]; rw [finrank_eq_card_basis (basisOfFractionalIdeal K I)]

Depends on / 依赖: RingOfIntegers, RingOfIntegers.rank, basisOfFractionalIdeal, finrank_eq_card_basis, finrank_eq_card_chooseBasisIndex
-/
theorem fractionalIdeal_rank (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    finrank Int I = finrank Int (𝓞 K) := by
  rw [finrank_eq_card_chooseBasisIndex]; rw [RingOfIntegers.rank]; rw [finrank_eq_card_basis (basisOfFractionalIdeal K I)]

end Basis

section Norm

open Module

/--
theorem `det_basisOfFractionalIdeal_eq_absNorm` / 定理 `det_basisOfFractionalIdeal_eq_absNorm`

English:
theorem det_basisOfFractionalIdeal_eq_absNorm
  statement: (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
  proof: by
  rw [← FractionalIdeal.abs_det_basis_change (RingOfIntegers.basis K) I.1
    ((fractionalIdealBasis K I.1).reindex e.symm)]
  congr
  ext
  simpa using basisOfFractionalIdeal_apply K I _

中文:
定理 det_basisOfFractionalIdeal_eq_absNorm
  结论: (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
  证明: by
  rw [← FractionalIdeal.abs_det_basis_change (RingOfIntegers.basis K) I.1
    ((fractionalIdealBasis K I.1).reindex e.symm)]
  congr
  ext
  simpa using basisOfFractionalIdeal_apply K I _

Depends on / 依赖: FractionalIdeal, FractionalIdeal.abs_det_basis_change, RingOfIntegers, RingOfIntegers.basis, abs_det_basis_change, basisOfFractionalIdeal_apply, e.symm, fractionalIdealBasis, reindex
-/
theorem det_basisOfFractionalIdeal_eq_absNorm (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (e : (Free.ChooseBasisIndex Int (𝓞 K)) ≃ (Free.ChooseBasisIndex Int I)) :
    |(integralBasis K).det ((basisOfFractionalIdeal K I).reindex e.symm)| =
      FractionalIdeal.absNorm I.1 := by
  rw [← FractionalIdeal.abs_det_basis_change (RingOfIntegers.basis K) I.1
    ((fractionalIdealBasis K I.1).reindex e.symm)]
  congr
  ext
  simpa using basisOfFractionalIdeal_apply K I _

end Norm

end NumberField
