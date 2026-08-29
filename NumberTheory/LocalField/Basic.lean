/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Valuation.DiscreteValuativeRel
public import Mathlib.Topology.Algebra.Module.Compact
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
public import Mathlib.Topology.Algebra.Valued.ValuativeRel

/-!

# Definition of (Non-archimedean) local fields

Given a topological field `K` equipped with an equivalence class of valuations (a `ValuativeRel`),
we say that it is a non-archimedean local field if the topology comes from the given valuation,
and it is locally compact and non-discrete.

-/

@[expose] public section

/--
Definition of `IsNonarchimedeanLocalField` / `IsNonarchimedeanLocalField` 的定义

English:
class IsNonarchimedeanLocalField
  (no additional axioms)

中文:
类 是NonarchimedeanLocalField
  (无附加公理)
-/
class IsNonarchimedeanLocalField
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] : Prop extends
  IsValuativeTopology K,
  LocallyCompactSpace K,
  ValuativeRel.IsNontrivial K

open ValuativeRel Valued.integer

open scoped WithZero

namespace IsNonarchimedeanLocalField

section TopologicalSpace

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

attribute [local simp] zero_lt_iff

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsTopologicalDivisionRing K
  body: by
  let := IsTopologicalAddGroup.rightUniformSpace K
  have := isUniformAddGroup_of_addCommGroup (G := K)
  infer_instance

中文:
实例 :
  签名: 是TopologicalDivision环 K
  定义体: by
  let := IsTopologicalAddGroup.rightUniformSpace K
  have := isUniformAddGroup_of_addCommGroup (G := K)
  infer_instance

Depends on / 依赖: IsTopologicalAddGroup, IsTopologicalAddGroup.rightUniformSpace, infer_instance, isUniformAddGroup_of_addCommGroup, rightUniformSpace
-/
instance : IsTopologicalDivisionRing K := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  have := isUniformAddGroup_of_addCommGroup (G := K)
  infer_instance

/--
lemma `isCompact_closedBall` / 引理 `isCompact_closedBall`

English:
lemma isCompact_closedBall
  given: (γ : ValueGroupWithZero K)
  statement: IsCompact { x | valuation K x <= γ }
  proof: by
  obtain ⟨γ, rfl⟩ := ValuativeRel.valuation_surjective γ
  by_cases hγ : γ = 0
  · simp [hγ]
  let := IsTopologicalAddGroup.rightUniformSpace K
  let := isUniformAddGroup_of_addCommGroup (G := K)
  obtain ⟨s, hs, -, hs'⟩ := LocallyCompactSpace.local_compact_nhds (0 : K) .univ Filter.univ_mem
  obtain ⟨r, hr, hr1, H⟩ :
      exists r', r' != 0 ∧ valuation K r' < 1 ∧ { x | valuation K x <= valuation K r' } subseteq s := by
    obtain ⟨r, hr, hrs⟩ := (IsValuativeTopology.hasBasis_nhds_zero' K).mem_iff.mp hs
    obtain ⟨r', hr', hr⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation K)
    simp only [ne_eq] at hr'
    obtain hr1 | hr1 := lt_or_ge r 1
    · obtain ⟨r, rfl⟩ := ValuativeRel.valuation_surjective r
      simp only [ne_eq, map_eq_zero] at hr
      refine ⟨r ^ 2, by simpa using hr, by simpa [pow_two], fun x hx => hrs ?_⟩
      simp only [map_pow, Set.mem_ofPred_eq] at hx ⊢
      exact hx.trans_lt (by simpa [pow_two, hr])
    · refine ⟨r', hr', hr, .trans ?_ hrs⟩
      intro x hx
      dsimp at hx ⊢
      exact hx.trans_lt (hr.trans_le hr1)
  simp_rw [← (valuation K).restrict_le_iff] at H ⊢
  convert!
    (hs'.of_isClosed_subset (Valued.isClosed_closedBall K _) H).image
      (Homeomorph.mulLeft₀ (γ / r) (by simp [hr, div_eq_zero_iff, hγ])).continuous using 1
  refine .trans ?_ (Equiv.image_eq_preimage_symm _ _).symm
  ext x
  simp only [Set.mem_ofPred_eq, Homeomorph.coe_symm_toEquiv, Homeomorph.mulLeft₀_symm_apply,
    inv_div, Set.preimage_ofPred_eq, map_mul, map_div₀, Valuation.restrict_le_iff]
  rw [div_mul_eq_mul_div]; rw [div_le_iff₀ (by simp [hγ])]
  simp only [IsValuativeTopology.v_eq_valuation, ← map_mul, Valuation.restrict_le_iff]
  simp [hr]

中文:
引理 isCompact_closedBall
  条件: (γ : ValueGroupWithZero K)
  结论: 是紧集 { x | valuation K x <= γ }
  证明: by
  obtain ⟨γ, rfl⟩ := ValuativeRel.valuation_surjective γ
  by_cases hγ : γ = 0
  · simp [hγ]
  let := IsTopologicalAddGroup.rightUniformSpace K
  let := isUniformAddGroup_of_addCommGroup (G := K)
  obtain ⟨s, hs, -, hs'⟩ := LocallyCompactSpace.local_compact_nhds (0 : K) .univ Filter.univ_mem
  obtain ⟨r, hr, hr1, H⟩ :
      exists r', r' != 0 ∧ valuation K r' < 1 ∧ { x | valuation K x <= valuation K r' } subseteq s := by
    obtain ⟨r, hr, hrs⟩ := (IsValuativeTopology.hasBasis_nhds_zero' K).mem_iff.mp hs
    obtain ⟨r', hr', hr⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation K)
    simp only [ne_eq] at hr'
    obtain hr1 | hr1 := lt_or_ge r 1
    · obtain ⟨r, rfl⟩ := ValuativeRel.valuation_surjective r
      simp only [ne_eq, map_eq_zero] at hr
      refine ⟨r ^ 2, by simpa using hr, by simpa [pow_two], fun x hx => hrs ?_⟩
      simp only [map_pow, Set.mem_ofPred_eq] at hx ⊢
      exact hx.trans_lt (by simpa [pow_two, hr])
    · refine ⟨r', hr', hr, .trans ?_ hrs⟩
      intro x hx
      dsimp at hx ⊢
      exact hx.trans_lt (hr.trans_le hr1)
  simp_rw [← (valuation K).restrict_le_iff] at H ⊢
  convert!
    (hs'.of_isClosed_subset (Valued.isClosed_closedBall K _) H).image
      (Homeomorph.mulLeft₀ (γ / r) (by simp [hr, div_eq_zero_iff, hγ])).continuous using 1
  refine .trans ?_ (Equiv.image_eq_preimage_symm _ _).symm
  ext x
  simp only [Set.mem_ofPred_eq, Homeomorph.coe_symm_toEquiv, Homeomorph.mulLeft₀_symm_apply,
    inv_div, Set.preimage_ofPred_eq, map_mul, map_div₀, Valuation.restrict_le_iff]
  rw [div_mul_eq_mul_div]; rw [div_le_iff₀ (by simp [hγ])]
  simp only [IsValuativeTopology.v_eq_valuation, ← map_mul, Valuation.restrict_le_iff]
  simp [hr]

Depends on / 依赖: Filter, Filter.univ_mem, IsTopologicalAddGroup, IsTopologicalAddGroup.rightUniformSpace, IsValuativeTopology, IsValuativeTopology.hasBasis_nhds_zero, LocallyCompactSpace, LocallyCompactSpace.local_compact_nhds, ValuativeRel, ValuativeRel.valuation_surjective, hasBasis_nhds_zero, isUniformAddGroup_of_addCommGroup, local_compact_nhds, mem_iff, mem_iff.mp, rightUniformSpace, subseteq, univ_mem, valuation, valuation_surjective
-/
lemma isCompact_closedBall (γ : ValueGroupWithZero K) : IsCompact { x | valuation K x <= γ } := by
  obtain ⟨γ, rfl⟩ := ValuativeRel.valuation_surjective γ
  by_cases hγ : γ = 0
  · simp [hγ]
  let := IsTopologicalAddGroup.rightUniformSpace K
  let := isUniformAddGroup_of_addCommGroup (G := K)
  obtain ⟨s, hs, -, hs'⟩ := LocallyCompactSpace.local_compact_nhds (0 : K) .univ Filter.univ_mem
  obtain ⟨r, hr, hr1, H⟩ :
      exists r', r' != 0 ∧ valuation K r' < 1 ∧ { x | valuation K x <= valuation K r' } subseteq s := by
    obtain ⟨r, hr, hrs⟩ := (IsValuativeTopology.hasBasis_nhds_zero' K).mem_iff.mp hs
    obtain ⟨r', hr', hr⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation K)
    simp only [ne_eq] at hr'
    obtain hr1 | hr1 := lt_or_ge r 1
    · obtain ⟨r, rfl⟩ := ValuativeRel.valuation_surjective r
      simp only [ne_eq, map_eq_zero] at hr
      refine ⟨r ^ 2, by simpa using hr, by simpa [pow_two], fun x hx => hrs ?_⟩
      simp only [map_pow, Set.mem_ofPred_eq] at hx ⊢
      exact hx.trans_lt (by simpa [pow_two, hr])
    · refine ⟨r', hr', hr, .trans ?_ hrs⟩
      intro x hx
      dsimp at hx ⊢
      exact hx.trans_lt (hr.trans_le hr1)
  simp_rw [← (valuation K).restrict_le_iff] at H ⊢
  convert!
    (hs'.of_isClosed_subset (Valued.isClosed_closedBall K _) H).image
      (Homeomorph.mulLeft₀ (γ / r) (by simp [hr, div_eq_zero_iff, hγ])).continuous using 1
  refine .trans ?_ (Equiv.image_eq_preimage_symm _ _).symm
  ext x
  simp only [Set.mem_ofPred_eq, Homeomorph.coe_symm_toEquiv, Homeomorph.mulLeft₀_symm_apply,
    inv_div, Set.preimage_ofPred_eq, map_mul, map_div₀, Valuation.restrict_le_iff]
  rw [div_mul_eq_mul_div]; rw [div_le_iff₀ (by simp [hγ])]
  simp only [IsValuativeTopology.v_eq_valuation, ← map_mul, Valuation.restrict_le_iff]
  simp [hr]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompactSpace 𝒪[K]
  body: isCompact_iff_compactSpace.mp (isCompact_closedBall K 1)

中文:
实例 :
  签名: 紧空间 𝒪[K]
  定义体: isCompact_iff_compactSpace.mp (isCompact_closedBall K 1)

Depends on / 依赖: isCompact_closedBall, isCompact_iff_compactSpace, isCompact_iff_compactSpace.mp
-/
instance : CompactSpace 𝒪[K] := isCompact_iff_compactSpace.mp (isCompact_closedBall K 1)

instance (K : Type*) [Field K] [ValuativeRel K] [UniformSpace K] [IsUniformAddGroup K]
    [IsValuativeTopology K] : (Valued.v (R := K) (Γ₀ := ValueGroupWithZero K)).Compatible :=
  inferInstanceAs (valuation K).Compatible

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsDiscreteValuationRing 𝒪[K]
  body: letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  haveI : CompactSpace (Valued.integer K) := inferInstanceAs (CompactSpace 𝒪[K])
  Valued.integer.isDiscreteValuationRing_of_compactSpace

中文:
实例 :
  签名: 是离散赋值环 𝒪[K]
  定义体: letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  haveI : CompactSpace (Valued.integer K) := inferInstanceAs (CompactSpace 𝒪[K])
  Valued.integer.isDiscreteValuationRing_of_compactSpace

Depends on / 依赖: CompactSpace, IsTopologicalAddGroup, IsTopologicalAddGroup.rightUniformSpace, Valued, Valued.integer, Valued.integer.isDiscreteValuationRing_of_compactSpace, integer, isDiscreteValuationRing_of_compactSpace, isUniformAddGroup_of_addCommGroup, rightUniformSpace
-/
instance : IsDiscreteValuationRing 𝒪[K] :=
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  haveI : CompactSpace (Valued.integer K) := inferInstanceAs (CompactSpace 𝒪[K])
  Valued.integer.isDiscreteValuationRing_of_compactSpace

/-- The value group of a local field is (uniquely) isomorphic to `ℤᵐ⁰`. -/
noncomputable
/--
Definition of `valueGroupWithZeroIsoInt` / `valueGroupWithZeroIsoInt` 的定义

English:
definition valueGroupWithZeroIsoInt
  signature: : ValueGroupWithZero K ≃*o Intᵐ⁰
  body: by
  apply Nonempty.some
  let := IsTopologicalAddGroup.rightUniformSpace K
  have := isUniformAddGroup_of_addCommGroup (G := K)
  obtain ⟨_⟩ := Valued.integer.locallyFiniteOrder_units_mrange_of_isCompact_integer
    (isCompact_iff_compactSpace.mpr (inferInstance : CompactSpace 𝒪[K]))
  let e : (MonoidHom.mrange (valuation K)) ≃*o ValueGroupWithZero K :=
    ⟨.ofBijective (MonoidHom.mrange (valuation K)).subtype ⟨Subtype.val_injective, fun x =>
      ⟨⟨x, ValuativeRel.valuation_surjective x⟩, rfl⟩⟩, .rfl⟩
  have : Nontrivial (ValueGroupWithZero K)ˣ := isNontrivial_iff_nontrivial_units.mp inferInstance
  have : Nontrivial (↥(MonoidHom.mrange (valuation K)))ˣ :=
    (Units.map_injective (f := e.symm.toMonoidHom) e.symm.injective).nontrivial
  exact ⟨e.symm.trans (LocallyFiniteOrder.orderMonoidWithZeroEquiv _)⟩

中文:
定义 valueGroupWithZeroIso整数
  签名: : ValueGroupWithZero K ≃*o 整数ᵐ⁰
  定义体: by
  apply Nonempty.some
  let := IsTopologicalAddGroup.rightUniformSpace K
  have := isUniformAddGroup_of_addCommGroup (G := K)
  obtain ⟨_⟩ := Valued.integer.locallyFiniteOrder_units_mrange_of_isCompact_integer
    (isCompact_iff_compactSpace.mpr (inferInstance : CompactSpace 𝒪[K]))
  let e : (MonoidHom.mrange (valuation K)) ≃*o ValueGroupWithZero K :=
    ⟨.ofBijective (MonoidHom.mrange (valuation K)).subtype ⟨Subtype.val_injective, fun x =>
      ⟨⟨x, ValuativeRel.valuation_surjective x⟩, rfl⟩⟩, .rfl⟩
  have : Nontrivial (ValueGroupWithZero K)ˣ := isNontrivial_iff_nontrivial_units.mp inferInstance
  have : Nontrivial (↥(MonoidHom.mrange (valuation K)))ˣ :=
    (Units.map_injective (f := e.symm.toMonoidHom) e.symm.injective).nontrivial
  exact ⟨e.symm.trans (LocallyFiniteOrder.orderMonoidWithZeroEquiv _)⟩

Depends on / 依赖: CompactSpace, IsTopologicalAddGroup, IsTopologicalAddGroup.rightUniformSpace, MonoidHom, MonoidHom.mrange, Nonempty, Nonempty.some, Nontri, Subtype, Subtype.val_injective, ValuativeRel, ValuativeRel.valuation_surjective, ValueGroupWithZero, Valued, Valued.integer.locallyFiniteOrder_units_mrange_of_isCompact_integer, integer, isCompact_iff_compactSpace, isCompact_iff_compactSpace.mpr, isUniformAddGroup_of_addCommGroup, locallyFiniteOrder_units_mrange_of_isCompact_integer
-/
def valueGroupWithZeroIsoInt : ValueGroupWithZero K ≃*o Intᵐ⁰ := by
  apply Nonempty.some
  let := IsTopologicalAddGroup.rightUniformSpace K
  have := isUniformAddGroup_of_addCommGroup (G := K)
  obtain ⟨_⟩ := Valued.integer.locallyFiniteOrder_units_mrange_of_isCompact_integer
    (isCompact_iff_compactSpace.mpr (inferInstance : CompactSpace 𝒪[K]))
  let e : (MonoidHom.mrange (valuation K)) ≃*o ValueGroupWithZero K :=
    ⟨.ofBijective (MonoidHom.mrange (valuation K)).subtype ⟨Subtype.val_injective, fun x =>
      ⟨⟨x, ValuativeRel.valuation_surjective x⟩, rfl⟩⟩, .rfl⟩
  have : Nontrivial (ValueGroupWithZero K)ˣ := isNontrivial_iff_nontrivial_units.mp inferInstance
  have : Nontrivial (↥(MonoidHom.mrange (valuation K)))ˣ :=
    (Units.map_injective (f := e.symm.toMonoidHom) e.symm.injective).nontrivial
  exact ⟨e.symm.trans (LocallyFiniteOrder.orderMonoidWithZeroEquiv _)⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsCyclic (ValueGroupWithZero K)ˣ
  body: (Units.mapEquiv (valueGroupWithZeroIsoInt K).toMulEquiv).isCyclic.mpr inferInstance

中文:
实例 :
  签名: 是循环 (ValueGroupWithZero K)ˣ
  定义体: (Units.mapEquiv (valueGroupWithZeroIsoInt K).toMulEquiv).isCyclic.mpr inferInstance

Depends on / 依赖: Units.mapEquiv, isCyclic, isCyclic.mpr, mapEquiv, toMulEquiv, valueGroupWithZeroIsoInt
-/
instance : IsCyclic (ValueGroupWithZero K)ˣ :=
  (Units.mapEquiv (valueGroupWithZeroIsoInt K).toMulEquiv).isCyclic.mpr inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ValuativeRel.IsDiscrete K
  body: (ValuativeRel.nonempty_orderIso_withZeroMul_int_iff.mp ⟨valueGroupWithZeroIsoInt K⟩).1

中文:
实例 :
  签名: ValuativeRel.是离散 K
  定义体: (ValuativeRel.nonempty_orderIso_withZeroMul_int_iff.mp ⟨valueGroupWithZeroIsoInt K⟩).1

Depends on / 依赖: ValuativeRel, ValuativeRel.nonempty_orderIso_withZeroMul_int_iff.mp, nonempty_orderIso_withZeroMul_int_iff, valueGroupWithZeroIsoInt
-/
instance : ValuativeRel.IsDiscrete K :=
  (ValuativeRel.nonempty_orderIso_withZeroMul_int_iff.mp ⟨valueGroupWithZeroIsoInt K⟩).1

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ValuativeRel.IsRankLeOne K
  body: ValuativeRel.isRankLeOne_iff_mulArchimedean.mpr
    (.comap (valueGroupWithZeroIsoInt K).toMonoidHom (valueGroupWithZeroIsoInt K).strictMono)

中文:
实例 :
  签名: ValuativeRel.是秩不超过一 K
  定义体: ValuativeRel.isRankLeOne_iff_mulArchimedean.mpr
    (.comap (valueGroupWithZeroIsoInt K).toMonoidHom (valueGroupWithZeroIsoInt K).strictMono)

Depends on / 依赖: ValuativeRel, ValuativeRel.isRankLeOne_iff_mulArchimedean.mpr, isRankLeOne_iff_mulArchimedean, strictMono, toMonoidHom, valueGroupWithZeroIsoInt
-/
instance : ValuativeRel.IsRankLeOne K :=
  ValuativeRel.isRankLeOne_iff_mulArchimedean.mpr
    (.comap (valueGroupWithZeroIsoInt K).toMonoidHom (valueGroupWithZeroIsoInt K).strictMono)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Finite 𝓀[K]
  body: letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  letI : (Valued.v (R := K)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  (compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.mp
    (inferInstanceAs (CompactSpace 𝒪[K]))).2.2

中文:
实例 :
  签名: 有限 𝓀[K]
  定义体: letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  letI : (Valued.v (R := K)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  (compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.mp
    (inferInstanceAs (CompactSpace 𝒪[K]))).2.2

Depends on / 依赖: CompactSpace, IsRankLeOne, IsRankLeOne.nonempty.some.emb, IsRankLeOne.nonempty.some.strictMono.comp, IsTopologicalAddGroup, IsTopologicalAddGroup.rightUniformSpace, MonoidWithZeroHom, MonoidWithZeroHom.ValueGroup, RankOne, Valued, Valued.v, compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField, compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.mp, embedding, embedding_strictMono, isUniformAddGroup_of_addCommGroup, nonempty, rightUniformSpace, strictMono
-/
instance : Finite 𝓀[K] :=
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  letI : (Valued.v (R := K)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  (compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.mp
    (inferInstanceAs (CompactSpace 𝒪[K]))).2.2

end TopologicalSpace

section UniformSpace

variable (K : Type*) [Field K] [ValuativeRel K]
  [UniformSpace K] [IsUniformAddGroup K] [IsNonarchimedeanLocalField K]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteSpace K
  body: letI : (Valued.v (R := K)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  open scoped Valued in
  have : ProperSpace K := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K
  (properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField.mp
    inferInstance).1

中文:
实例 :
  签名: 完备空间 K
  定义体: letI : (Valued.v (R := K)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  open scoped Valued in
  have : ProperSpace K := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K
  (properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField.mp
    inferInstance).1

Depends on / 依赖: IsRankLeOne, IsRankLeOne.nonempty.some.emb, IsRankLeOne.nonempty.some.strictMono.comp, MonoidWithZeroHom, MonoidWithZeroHom.ValueGroup, ProperSpace, RankOne, Valued, Valued.v, embedding, embedding_strictMono, nonempty, of_nontriviallyNormedField_of_weaklyLocallyCompactSpace, properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField, properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField.mp, scoped, strictMono
-/
instance : CompleteSpace K :=
  letI : (Valued.v (R := K)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  open scoped Valued in
  have : ProperSpace K := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K
  (properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField.mp
    inferInstance).1

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteSpace 𝒪[K]
  body: letI : (Valued.v (R := K)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  (compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.mp
    (inferInstanceAs (CompactSpace 𝒪[K]))).1

中文:
实例 :
  签名: 完备空间 𝒪[K]
  定义体: letI : (Valued.v (R := K)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  (compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.mp
    (inferInstanceAs (CompactSpace 𝒪[K]))).1

Depends on / 依赖: CompactSpace, IsRankLeOne, IsRankLeOne.nonempty.some.emb, IsRankLeOne.nonempty.some.strictMono.comp, MonoidWithZeroHom, MonoidWithZeroHom.ValueGroup, RankOne, Valued, Valued.v, compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField, compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.mp, embedding, embedding_strictMono, nonempty, strictMono
-/
instance : CompleteSpace 𝒪[K] :=
  letI : (Valued.v (R := K)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  (compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.mp
    (inferInstanceAs (CompactSpace 𝒪[K]))).1

open scoped Pointwise in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsAdicComplete 𝓂[K] 𝒪[K]
  body: by
    let S n : Set 𝒪[K] := f n +ᵥ ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K])
    have hS n : S (n + 1) subseteq S n := by
      apply (Set.vadd_set_subset_vadd_set_iff.mpr (Ideal.pow_le_pow_right n.le_succ)).trans
      simpa [S] using (hf n.le_succ).symm
    have h n : IsClosed (S n) := (IsNoetherianRing.isClosed_ideal (𝓂[K] ^ n)).vadd (f n)
    obtain ⟨L, hL⟩ := (h 0).isCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S hS
      (by simp [S]) h
    refine ⟨L, fun n => ?_⟩
    obtain ⟨y, hy, rfl⟩ := Set.mem_iInter.mp hL n
    simpa [SModEq.sub_mem] using hy

中文:
实例 :
  签名: 是AdicComplete 𝓂[K] 𝒪[K]
  定义体: by
    let S n : Set 𝒪[K] := f n +ᵥ ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K])
    have hS n : S (n + 1) subseteq S n := by
      apply (Set.vadd_set_subset_vadd_set_iff.mpr (Ideal.pow_le_pow_right n.le_succ)).trans
      simpa [S] using (hf n.le_succ).symm
    have h n : IsClosed (S n) := (IsNoetherianRing.isClosed_ideal (𝓂[K] ^ n)).vadd (f n)
    obtain ⟨L, hL⟩ := (h 0).isCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S hS
      (by simp [S]) h
    refine ⟨L, fun n => ?_⟩
    obtain ⟨y, hy, rfl⟩ := Set.mem_iInter.mp hL n
    simpa [SModEq.sub_mem] using hy

Depends on / 依赖: Ideal.pow_le_pow_right, IsClosed, IsNoetherianRing, IsNoetherianRing.isClosed_ideal, Set.mem_iInter.mp, Set.vadd_set_subset_vadd_set_iff.mpr, isClosed_ideal, isCompact, isCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed, le_succ, mem_iInter, n.le_succ, nonempty_iInter_of_sequence_nonempty_isCompact_isClosed, pow_le_pow_right, subseteq, vadd_set_subset_vadd_set_iff
-/
instance : IsAdicComplete 𝓂[K] 𝒪[K] where
  prec' f hf := by
    let S n : Set 𝒪[K] := f n +ᵥ ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K])
    have hS n : S (n + 1) subseteq S n := by
      apply (Set.vadd_set_subset_vadd_set_iff.mpr (Ideal.pow_le_pow_right n.le_succ)).trans
      simpa [S] using (hf n.le_succ).symm
    have h n : IsClosed (S n) := (IsNoetherianRing.isClosed_ideal (𝓂[K] ^ n)).vadd (f n)
    obtain ⟨L, hL⟩ := (h 0).isCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S hS
      (by simp [S]) h
    refine ⟨L, fun n => ?_⟩
    obtain ⟨y, hy, rfl⟩ := Set.mem_iInter.mp hL n
    simpa [SModEq.sub_mem] using hy

end UniformSpace

end IsNonarchimedeanLocalField
