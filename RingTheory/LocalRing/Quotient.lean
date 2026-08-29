/-
Copyright (c) 2024 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Riccardo Brasca
-/
module

public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Nakayama


/-!

We gather results about the quotients of local rings.

-/

@[expose] public section

open Submodule FiniteDimensional Module

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R] [Module.Finite R S]

namespace IsLocalRing

local notation "p" => maximalIdeal R
local notation "pS" => Ideal.map (algebraMap R S) p

/--
theorem `quotient_span_eq_top_iff_span_eq_top` / 定理 `quotient_span_eq_top_iff_span_eq_top`

English:
theorem quotient_span_eq_top_iff_span_eq_top
  given: (s : Set S)
  proof: by
  have H : (span (R ⧸ p) ((Ideal.Quotient.mk (I := pS)) '' s)).restrictScalars R =
      (span R s).map (IsScalarTower.toAlgHom R S (S ⧸ pS) : S ->ₗ[R] S ⧸ pS) := by
    rw [map_span]; rw [← restrictScalars_span R (R ⧸ p) Ideal.Quotient.mk_surjective]; rw [LinearMap.coe_coe]; rw [IsScalarTower.co

中文:
定理 quotient_span_eq_top_iff_span_eq_top
  条件: (s : 集合 S)
  证明: by
  have H : (span (R ⧸ p) ((Ideal.Quotient.mk (I := pS)) '' s)).restrictScalars R =
      (span R s).map (IsScalarTower.toAlgHom R S (S ⧸ pS) : S ->ₗ[R] S ⧸ pS) := by
    rw [map_span]; rw [← restrictScalars_span R (R ⧸ p) Ideal.Quotient.mk_surjective]; rw [LinearMap.coe_coe]; rw [IsScalarTower.co

Depends on / 依赖: Ideal.Quotient.algebraMap_eq, Ideal.Quotient.mk, Ideal.Quotient.mk_surjective, IsScalarTower, IsScalarTower.coe_toAlgHom, IsScalarTower.toAlgHom, LinearMap, LinearMap.coe_coe, Module, Module.finite_def.mp, Quotient, algebraMap_eq, coe_coe, coe_toAlgHom, finite_def, jacobson_, le_of_le_smul_of_le_jacobson_bot, map_span, mk_surjective, restrictScalars
-/
theorem quotient_span_eq_top_iff_span_eq_top (s : Set S) :
    span (R ⧸ p) ((Ideal.Quotient.mk (I := pS)) '' s) = ⊤ ↔ span R s = ⊤ := by
  have H : (span (R ⧸ p) ((Ideal.Quotient.mk (I := pS)) '' s)).restrictScalars R =
      (span R s).map (IsScalarTower.toAlgHom R S (S ⧸ pS) : S ->ₗ[R] S ⧸ pS) := by
    rw [map_span]; rw [← restrictScalars_span R (R ⧸ p) Ideal.Quotient.mk_surjective]; rw [LinearMap.coe_coe]; rw [IsScalarTower.coe_toAlgHom']; rw [Ideal.Quotient.algebraMap_eq]
  constructor
  · intro hs
    rw [← top_le_iff]
    apply le_of_le_smul_of_le_jacobson_bot
    · exact Module.finite_def.mp ‹_›
    · exact (jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
    · rw [Ideal.smul_top_eq_map]
      rintro x -
      have : LinearMap.ker (IsScalarTower.toAlgHom R S (S ⧸ pS) : S ->ₗ[R] S ⧸ pS) =
          Submodule.restrictScalars R pS := by
        ext; simp [Ideal.Quotient.eq_zero_iff_mem]
      rw [← this]; rw [← comap_map_eq]; rw [mem_comap]; rw [← H]; rw [hs]; rw [restrictScalars_top]
      exact mem_top
  · intro hs
    rwa [hs, Submodule.map_top, LinearMap.range_eq_top.mpr,
      restrictScalars_eq_top_iff] at H
    rw [LinearMap.coe_coe]; rw [IsScalarTower.coe_toAlgHom']; rw [Ideal.Quotient.algebraMap_eq]
    exact Ideal.Quotient.mk_surjective

attribute [local instance] Ideal.Quotient.field

variable [Module.Free R S] {ι : Type*}

/--
theorem `finrank_quotient_map` / 定理 `finrank_quotient_map`

English:
theorem finrank_quotient_map
  proof: by
  have : Module.Finite (R ⧸ p) (S ⧸ pS) := Module.Finite.of_restrictScalars_finite R _ _
  apply le_antisymm
  · let b := Module.Free.chooseBasis R S
    conv_rhs => rw [finrank_eq_card_chooseBasisIndex]
    apply finrank_le_of_span_eq_top
    rw [Set.range_comp]
    apply (quotient_span_eq_top_i

中文:
定理 finrank_quotient_map
  证明: by
  have : Module.Finite (R ⧸ p) (S ⧸ pS) := Module.Finite.of_restrictScalars_finite R _ _
  apply le_antisymm
  · let b := Module.Free.chooseBasis R S
    conv_rhs => rw [finrank_eq_card_chooseBasisIndex]
    apply finrank_le_of_span_eq_top
    rw [Set.range_comp]
    apply (quotient_span_eq_top_i

Depends on / 依赖: Finite, Ideal.Quotient.mk_surjective, Module, Module.Finite, Module.Finite.of_restrictScalars_finite, Module.Free.chooseBasis, Quotient, Set.range_comp, b.span_eq, chooseBasis, conv_rhs, finrank_eq_card_chooseBasisIndex, finrank_le_of_spa, finrank_le_of_span_eq_top, le_antisymm, mk_surjective, of_restrictScalars_finite, quotient_span_eq_top_iff_span_eq_top, range_comp, span_eq
-/
theorem finrank_quotient_map :
    finrank (R ⧸ p) (S ⧸ pS) = finrank R S := by
  have : Module.Finite (R ⧸ p) (S ⧸ pS) := Module.Finite.of_restrictScalars_finite R _ _
  apply le_antisymm
  · let b := Module.Free.chooseBasis R S
    conv_rhs => rw [finrank_eq_card_chooseBasisIndex]
    apply finrank_le_of_span_eq_top
    rw [Set.range_comp]
    apply (quotient_span_eq_top_iff_span_eq_top _).mpr b.span_eq
  · let b := Module.Free.chooseBasis (R ⧸ p) (S ⧸ pS)
    choose b' hb' using fun i => Ideal.Quotient.mk_surjective (b i)
    conv_rhs => rw [finrank_eq_card_chooseBasisIndex]
    refine finrank_le_of_span_eq_top (v := b') ?_
    apply (quotient_span_eq_top_iff_span_eq_top _).mp
    rw [← Set.range_comp]; rw [show Ideal.Quotient.mk pS ∘ b' = ⇑b from funext hb']
    exact b.span_eq

/-- Given a basis of `S`, the induced basis of `S / Ideal.map (algebraMap R S) p`. -/
noncomputable
/--
Definition of `basisQuotient` / `basisQuotient` 的定义

English:
definition basisQuotient
  signature: [Fintype ι] (b : Basis ι R S)
  body: basisOfTopLeSpanOfCardEqFinrank (Ideal.Quotient.mk pS ∘ b)
    (by
      rw [Set.range_comp]
      exact ((quotient_span_eq_top_iff_span_eq_top _).mpr b.span_eq).ge)
    (by rw [finrank_quotient_map, finrank_eq_card_basis b])

中文:
定义 basisQuotient
  签名: [有限类型 ι] (b : 基 ι R S)
  定义体: basisOfTopLeSpanOfCardEqFinrank (Ideal.Quotient.mk pS ∘ b)
    (by
      rw [Set.range_comp]
      exact ((quotient_span_eq_top_iff_span_eq_top _).mpr b.span_eq).ge)
    (by rw [finrank_quotient_map, finrank_eq_card_basis b])

Depends on / 依赖: Ideal.Quotient.mk, Quotient, Set.range_comp, b.span_eq, basisOfTopLeSpanOfCardEqFinrank, finrank_eq_card_basis, finrank_quotient_map, quotient_span_eq_top_iff_span_eq_top, range_comp, span_eq
-/
def basisQuotient [Fintype ι] (b : Basis ι R S) : Basis ι (R ⧸ p) (S ⧸ pS) :=
  basisOfTopLeSpanOfCardEqFinrank (Ideal.Quotient.mk pS ∘ b)
    (by
      rw [Set.range_comp]
      exact ((quotient_span_eq_top_iff_span_eq_top _).mpr b.span_eq).ge)
    (by rw [finrank_quotient_map, finrank_eq_card_basis b])

/--
lemma `basisQuotient_apply` / 引理 `basisQuotient_apply`

English:
lemma basisQuotient_apply
  given: [Fintype ι] (b : Basis ι R S) (i)
  proof: by
  delta basisQuotient
  rw [coe_basisOfTopLeSpanOfCardEqFinrank]; rw [Function.comp_apply]

中文:
引理 basisQuotient_apply
  条件: [有限类型 ι] (b : 基 ι R S) (i)
  证明: by
  delta basisQuotient
  rw [coe_basisOfTopLeSpanOfCardEqFinrank]; rw [Function.comp_apply]

Depends on / 依赖: Function, Function.comp_apply, basisQuotient, coe_basisOfTopLeSpanOfCardEqFinrank, comp_apply
-/
lemma basisQuotient_apply [Fintype ι] (b : Basis ι R S) (i) :
    (basisQuotient b) i = Ideal.Quotient.mk pS (b i) := by
  delta basisQuotient
  rw [coe_basisOfTopLeSpanOfCardEqFinrank]; rw [Function.comp_apply]

/--
lemma `basisQuotient_repr` / 引理 `basisQuotient_repr`

English:
lemma basisQuotient_repr
  given: {ι} [Fintype ι] (b : Basis ι R S) (x) (i)
  proof: by
  refine congr_fun (g := Ideal.Quotient.mk p ∘ b.repr x) ?_ i
  apply (Finsupp.linearEquivFunOnFinite (R ⧸ p) _ _).symm.injective
  apply (basisQuotient b).repr.symm.injective
  simp only [Finsupp.linearEquivFunOnFinite_symm_coe, LinearEquiv.symm_apply_apply,
    Basis.repr_symm_apply]
  rw [Fins

中文:
引理 basisQuotient_repr
  条件: {ι} [有限类型 ι] (b : 基 ι R S) (x) (i)
  证明: by
  refine congr_fun (g := Ideal.Quotient.mk p ∘ b.repr x) ?_ i
  apply (Finsupp.linearEquivFunOnFinite (R ⧸ p) _ _).symm.injective
  apply (basisQuotient b).repr.symm.injective
  simp only [Finsupp.linearEquivFunOnFinite_symm_coe, LinearEquiv.symm_apply_apply,
    Basis.repr_symm_apply]
  rw [Fins

Depends on / 依赖: Algebr, Basis.repr_symm_apply, Finsupp, Finsupp.linearCombination_eq_fintype_linearCombination_apply, Finsupp.linearEquivFunOnFinite, Finsupp.linearEquivFunOnFinite_symm_coe, Fintype, Fintype.linearCombination_apply, Function, Function.comp_apply, H.isNormal, Ideal.Quotient.mk, Ideal.Quotient.mk_smul_mk_quotient_map_quotient, LinearEquiv, LinearEquiv.symm_apply_apply, Quotient, b.repr, basisQuotient, basisQuotient_apply, comp_apply
-/
lemma basisQuotient_repr {ι} [Fintype ι] (b : Basis ι R S) (x) (i) :
    (basisQuotient b).repr (Ideal.Quotient.mk pS x) i =
    Ideal.Quotient.mk p (b.repr x i) := by
  refine congr_fun (g := Ideal.Quotient.mk p ∘ b.repr x) ?_ i
  apply (Finsupp.linearEquivFunOnFinite (R ⧸ p) _ _).symm.injective
  apply (basisQuotient b).repr.symm.injective
  simp only [Finsupp.linearEquivFunOnFinite_symm_coe, LinearEquiv.symm_apply_apply,
    Basis.repr_symm_apply]
  rw [Finsupp.linearCombination_eq_fintype_linearCombination_apply (R ⧸ p)]; rw [Fintype.linearCombination_apply]
  simp only [Function.comp_apply, basisQuotient_apply,
    Ideal.Quotient.mk_smul_mk_quotient_map_quotient, ← Algebra.smul_def]
  rw [← map_sum]; rw [Basis.sum_repr b x]

/--
lemma `exists_maximalIdeal_pow_le_of_isArtinianRing_quotient` / 引理 `exists_maximalIdeal_pow_le_of_isArtinianRing_quotient`

English:
lemma exists_maximalIdeal_pow_le_of_isArtinianRing_quotient
  proof: by
  by_cases hI : I = ⊤
  · simp [hI]
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have := IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have := IsLocalHom.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  obtain ⟨n, hn⟩ :=

中文:
引理 存在_maximalIdeal_pow_le_of_isArtinianRing_quotient
  证明: by
  by_cases hI : I = ⊤
  · simp [hI]
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have := IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have := IsLocalHom.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  obtain ⟨n, hn⟩ :=

Depends on / 依赖: Ideal.Quotient.mk, Ideal.Quotient.mk_surjective, Ideal.Quotient.nontrivial_iff.mpr, IsArtinianRing, IsArtinianRing.isNilpotent_jacobson_bot, IsLocalHom, IsLocalHom.of_surjective, IsLocalRing, IsLocalRing.of_surjective, Nontrivial, Quotient, isNilpotent_jacobson_bot, maximalIdeal, mk_surjective, nontrivial_iff, of_surjective, sup_eq_left, sup_eq_left.mpr
-/
lemma exists_maximalIdeal_pow_le_of_isArtinianRing_quotient
    (I : Ideal R) [IsArtinianRing (R ⧸ I)] : exists n, maximalIdeal R ^ n <= I := by
  by_cases hI : I = ⊤
  · simp [hI]
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have := IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have := IsLocalHom.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R ⧸ I)
  have : (maximalIdeal R).map (Ideal.Quotient.mk I) = maximalIdeal (R ⧸ I) := by
    ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp [sup_eq_left.mpr (le_maximalIdeal hI)]
  rw [jacobson_eq_maximalIdeal _ bot_ne_top]; rw [← this]; rw [← Ideal.map_pow]; rw [Ideal.zero_eq_bot]; rw [Ideal.map_eq_bot_iff_le_ker]; rw [Ideal.mk_ker] at hn
  exact ⟨n, hn⟩

/--
lemma `finite_quotient_iff` / 引理 `finite_quotient_iff`

English:
lemma finite_quotient_iff
  given: [IsNoetherianRing R] [Finite (ResidueField R)] {I : Ideal R}
  proof: by
  refine ⟨fun _ => exists_maximalIdeal_pow_le_of_isArtinianRing_quotient I, ?_⟩
  rintro ⟨n, hn⟩
  have : Finite (R ⧸ maximalIdeal R) := ‹_›
  have := (Ideal.finite_quotient_pow (IsNoetherian.noetherian (maximalIdeal R)) n)
  exact Finite.of_surjective _ (Ideal.Quotient.factor_surjective hn)

中文:
引理 finite_quotient_iff
  条件: [是Noether环 R] [有限 (ResidueField R)] {I : 理想 R}
  证明: by
  refine ⟨fun _ => exists_maximalIdeal_pow_le_of_isArtinianRing_quotient I, ?_⟩
  rintro ⟨n, hn⟩
  have : Finite (R ⧸ maximalIdeal R) := ‹_›
  have := (Ideal.finite_quotient_pow (IsNoetherian.noetherian (maximalIdeal R)) n)
  exact Finite.of_surjective _ (Ideal.Quotient.factor_surjective hn)

Depends on / 依赖: Finite, Finite.of_surjective, Ideal.Quotient.factor_surjective, Ideal.finite_quotient_pow, IsNoetherian, IsNoetherian.noetherian, Quotient, exists_maximalIdeal_pow_le_of_isArtinianRing_quotient, factor_surjective, finite_quotient_pow, maximalIdeal, noetherian, of_surjective
-/
lemma finite_quotient_iff [IsNoetherianRing R] [Finite (ResidueField R)] {I : Ideal R} :
    Finite (R ⧸ I) ↔ exists n, (maximalIdeal R) ^ n <= I := by
  refine ⟨fun _ => exists_maximalIdeal_pow_le_of_isArtinianRing_quotient I, ?_⟩
  rintro ⟨n, hn⟩
  have : Finite (R ⧸ maximalIdeal R) := ‹_›
  have := (Ideal.finite_quotient_pow (IsNoetherian.noetherian (maximalIdeal R)) n)
  exact Finite.of_surjective _ (Ideal.Quotient.factor_surjective hn)

end IsLocalRing
