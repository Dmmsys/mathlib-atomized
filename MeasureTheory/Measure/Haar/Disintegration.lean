/-
Copyright (c) 2023 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Pushing a Haar measure by a linear map

We show that the push-forward of an additive Haar measure in a vector space under a surjective
linear map is proportional to the Haar measure on the target space,
in `LinearMap.exists_map_addHaar_eq_smul_addHaar`.

We deduce disintegration properties of the Haar measure: to check that a property is true ae,
it suffices to check that it is true ae along all translates of a given vector subspace.
See `MeasureTheory.ae_mem_of_ae_add_linearMap_mem`.

TODO: this holds more generally in any locally compact group, see
[Fremlin, *Measure Theory* (volume 4, 443Q)][fremlin_vol4]
-/

public section

open MeasureTheory Measure Set

open scoped ENNReal

variable {𝕜 E F : Type*}
  [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [MeasurableSpace F] [BorelSpace F] [NormedSpace 𝕜 F] {L : E ->ₗ[𝕜] F}
  {μ : Measure E} {ν : Measure F}
  [IsAddHaarMeasure μ] [IsAddHaarMeasure ν]

variable [LocallyCompactSpace E]
variable (L μ ν)

/--
theorem `LinearMap.exists_map_addHaar_eq_smul_addHaar'` / 定理 `LinearMap.exists_map_addHaar_eq_smul_addHaar'`

English:
theorem LinearMap.exists_map_addHaar_eq_smul_addHaar'
  given: (h : Function.Surjective L)
  proof: by
  /- This is true for the second projection in product spaces, as the projection of the Haar
  measure `μS.prod μT` is equal to the Haar measure `μT` multiplied by the total mass of `μS`. This
  is also true for linear equivalences, as they map Haar measure to Haar measure. The general case
  fol

中文:
定理 线性映射.存在_map_addHaar_eq_smul_addHaar'
  条件: (h : 函数.满射 L)
  证明: by
  /- This is true for the second projection in product spaces, as the projection of the Haar
  measure `μS.prod μT` is equal to the Haar measure `μT` multiplied by the total mass of `μS`. This
  is also true for linear equivalences, as they map Haar measure to Haar measure. The general case
  fol
-/
theorem LinearMap.exists_map_addHaar_eq_smul_addHaar' (h : Function.Surjective L) :
    exists (c : Real>=0∞), 0 < c ∧ c < ∞ ∧ μ.map L = (c * addHaar (univ : Set (LinearMap.ker L))) • ν := by
  /- This is true for the second projection in product spaces, as the projection of the Haar
  measure `μS.prod μT` is equal to the Haar measure `μT` multiplied by the total mass of `μS`. This
  is also true for linear equivalences, as they map Haar measure to Haar measure. The general case
  follows from these two and linear algebra, as `L` can be interpreted as the composition of the
  projection `P` on a complement `T` to its kernel `S`, together with a linear equivalence. -/
  have : FiniteDimensional 𝕜 E := .of_locallyCompactSpace 𝕜
  have : ProperSpace F := by
    rcases subsingleton_or_nontrivial E with hE | hE
    · have : Subsingleton F := Function.Surjective.subsingleton h
      infer_instance
    · have : ProperSpace 𝕜 := .of_locallyCompact_module 𝕜 E
      have : FiniteDimensional 𝕜 F := Module.Finite.of_surjective L h
      exact FiniteDimensional.proper 𝕜 F
  let S : Submodule 𝕜 E := LinearMap.ker L
  obtain ⟨T, hT⟩ : exists T : Submodule 𝕜 E, IsCompl S T := Submodule.exists_isCompl S
  let M : (S × T) ≃ₗ[𝕜] E := Submodule.prodEquivOfIsCompl S T hT
  have M_cont : Continuous M.symm := LinearMap.continuous_of_finiteDimensional _
  let P : S × T ->ₗ[𝕜] T := LinearMap.snd 𝕜 S T
  have P_cont : Continuous P := LinearMap.continuous_of_finiteDimensional _
  have I : Function.Bijective (LinearMap.domRestrict L T) :=
    ⟨LinearMap.injective_domRestrict_iff.2 hT.disjoint.symm,
    (LinearMap.surjective_domRestrict_iff h).2 hT.symm.codisjoint⟩
  let L' : T ≃ₗ[𝕜] F := LinearEquiv.ofBijective (LinearMap.domRestrict L T) I
  have L'_cont : Continuous L' := LinearMap.continuous_of_finiteDimensional _
  have A : L = (L' : T ->ₗ[𝕜] F).comp (P.comp (M.symm : E ->ₗ[𝕜] (S × T))) := by
    ext x
    obtain ⟨y, z, hyz⟩ : exists (y : S) (z : T), M.symm x = (y, z) := ⟨_, _, rfl⟩
    have : x = M (y, z) := by
      rw [← hyz]; simp only [LinearEquiv.apply_symm_apply]
    simp [L', P, M, this]
  have I : μ.map L = ((μ.map M.symm).map P).map L' := by
    rw [Measure.map_map]; rw [Measure.map_map]; rw [A]
    · rfl
    · exact L'_cont.measurable.comp P_cont.measurable
    · exact M_cont.measurable
    · exact L'_cont.measurable
    · exact P_cont.measurable
  let μS : Measure S := addHaar
  let μT : Measure T := addHaar
  obtain ⟨c₀, c₀_pos, c₀_fin, h₀⟩ :
      exists c₀ : Real>=0∞, c₀ != 0 ∧ c₀ != ∞ ∧ μ.map M.symm = c₀ • μS.prod μT := by
    have : IsAddHaarMeasure (μ.map M.symm) :=
      M.toContinuousLinearEquiv.symm.isAddHaarMeasure_map μ
    refine ⟨addHaarScalarFactor (μ.map M.symm) (μS.prod μT), ?_, ENNReal.coe_ne_top,
      isAddLeftInvariant_eq_smul _ _⟩
    simpa only [ne_eq, ENNReal.coe_eq_zero] using
      (addHaarScalarFactor_pos_of_isAddHaarMeasure (μ.map M.symm) (μS.prod μT)).ne'
  have J : (μS.prod μT).map P = (μS univ) • μT := map_snd_prod
  obtain ⟨c₁, c₁_pos, c₁_fin, h₁⟩ : exists c₁ : Real>=0∞, c₁ != 0 ∧ c₁ != ∞ ∧ μT.map L' = c₁ • ν := by
    have : IsAddHaarMeasure (μT.map L') :=
      L'.toContinuousLinearEquiv.isAddHaarMeasure_map μT
    refine ⟨addHaarScalarFactor (μT.map L') ν, ?_, ENNReal.coe_ne_top,
      isAddLeftInvariant_eq_smul _ _⟩
    simpa only [ne_eq, ENNReal.coe_eq_zero] using
      (addHaarScalarFactor_pos_of_isAddHaarMeasure (μT.map L') ν).ne'
  refine ⟨c₀ * c₁, by simp [pos_iff_ne_zero, c₀_pos, c₁_pos],
    ENNReal.mul_lt_top c₀_fin.lt_top c₁_fin.lt_top, ?_⟩
  simp only [I, h₀, Measure.map_smul, J, smul_smul, h₁]
  rw [mul_assoc]; rw [mul_comm _ c₁]; rw [← mul_assoc]

/--
theorem `LinearMap.exists_map_addHaar_eq_smul_addHaar` / 定理 `LinearMap.exists_map_addHaar_eq_smul_addHaar`

English:
theorem LinearMap.exists_map_addHaar_eq_smul_addHaar
  given: (h : Function.Surjective L)
  proof: by
  rcases L.exists_map_addHaar_eq_smul_addHaar' μ ν h with ⟨c, c_pos, -, hc⟩
  exact ⟨_, by simp [c_pos, NeZero.ne addHaar], hc⟩

中文:
定理 线性映射.存在_map_addHaar_eq_smul_addHaar
  条件: (h : 函数.满射 L)
  证明: by
  rcases L.exists_map_addHaar_eq_smul_addHaar' μ ν h with ⟨c, c_pos, -, hc⟩
  exact ⟨_, by simp [c_pos, NeZero.ne addHaar], hc⟩

Depends on / 依赖: L.exists_map_addHaar_eq_smul_addHaar, NeZero, NeZero.ne, addHaar, c_pos, exists_map_addHaar_eq_smul_addHaar
-/
theorem LinearMap.exists_map_addHaar_eq_smul_addHaar (h : Function.Surjective L) :
    exists (c : Real>=0∞), 0 < c ∧ μ.map L = c • ν := by
  rcases L.exists_map_addHaar_eq_smul_addHaar' μ ν h with ⟨c, c_pos, -, hc⟩
  exact ⟨_, by simp [c_pos, NeZero.ne addHaar], hc⟩

namespace MeasureTheory

/--
lemma `ae_comp_linearMap_mem_iff` / 引理 `ae_comp_linearMap_mem_iff`

English:
lemma ae_comp_linearMap_mem_iff
  given: (h : Function.Surjective L) {s : Set F} (hs : MeasurableSet s)
  proof: by
  have : FiniteDimensional 𝕜 E := .of_locallyCompactSpace 𝕜
  have : AEMeasurable L μ := L.continuous_of_finiteDimensional.aemeasurable
  apply (ae_map_iff this hs).symm.trans
  rcases L.exists_map_addHaar_eq_smul_addHaar μ ν h with ⟨c, c_pos, hc⟩
  rw [hc]
  exact ae_ennreal_smul_measure_iff c_p

中文:
引理 ae_comp_linearMap_mem_iff
  条件: (h : 函数.满射 L) {s : 集合 F} (hs : 可测集 s)
  证明: by
  have : FiniteDimensional 𝕜 E := .of_locallyCompactSpace 𝕜
  have : AEMeasurable L μ := L.continuous_of_finiteDimensional.aemeasurable
  apply (ae_map_iff this hs).symm.trans
  rcases L.exists_map_addHaar_eq_smul_addHaar μ ν h with ⟨c, c_pos, hc⟩
  rw [hc]
  exact ae_ennreal_smul_measure_iff c_p

Depends on / 依赖: AEMeasurable, FiniteDimensional, L.continuous_of_finiteDimensional.aemeasurable, L.exists_map_addHaar_eq_smul_addHaar, ae_ennreal_smul_measure_iff, ae_map_iff, aemeasurable, c_pos, c_pos.ne, continuous_of_finiteDimensional, exists_map_addHaar_eq_smul_addHaar, of_locallyCompactSpace, symm.trans
-/
lemma ae_comp_linearMap_mem_iff (h : Function.Surjective L) {s : Set F} (hs : MeasurableSet s) :
    (forallᵐ x ∂μ, L x in s) ↔ forallᵐ y ∂ν, y in s := by
  have : FiniteDimensional 𝕜 E := .of_locallyCompactSpace 𝕜
  have : AEMeasurable L μ := L.continuous_of_finiteDimensional.aemeasurable
  apply (ae_map_iff this hs).symm.trans
  rcases L.exists_map_addHaar_eq_smul_addHaar μ ν h with ⟨c, c_pos, hc⟩
  rw [hc]
  exact ae_ennreal_smul_measure_iff c_pos.ne'

/--
lemma `ae_ae_add_linearMap_mem_iff` / 引理 `ae_ae_add_linearMap_mem_iff`

English:
lemma ae_ae_add_linearMap_mem_iff
  given: [LocallyCompactSpace F] {s : Set F} (hs : MeasurableSet s)
  proof: by
  have : FiniteDimensional 𝕜 E := .of_locallyCompactSpace 𝕜
  have : FiniteDimensional 𝕜 F := .of_locallyCompactSpace 𝕜
  have : ProperSpace E := .of_locallyCompactSpace 𝕜
  have : ProperSpace F := .of_locallyCompactSpace 𝕜
  let M : F × E ->ₗ[𝕜] F := LinearMap.id.coprod L
  have M_cont : Continu

中文:
引理 ae_ae_add_linearMap_mem_iff
  条件: [局部紧空间 F] {s : 集合 F} (hs : 可测集 s)
  证明: by
  have : FiniteDimensional 𝕜 E := .of_locallyCompactSpace 𝕜
  have : FiniteDimensional 𝕜 F := .of_locallyCompactSpace 𝕜
  have : ProperSpace E := .of_locallyCompactSpace 𝕜
  have : ProperSpace F := .of_locallyCompactSpace 𝕜
  let M : F × E ->ₗ[𝕜] F := LinearMap.id.coprod L
  have M_cont : Continu

Depends on / 依赖: Continuous, FiniteDimensional, LinearMap, LinearMap.id.coprod, M.continuous_of_finiteDimensional, M_cont, ProperSpace, continuous_of_finiteDimensional, coprod, of_locallyCompactSpace
-/
lemma ae_ae_add_linearMap_mem_iff [LocallyCompactSpace F] {s : Set F} (hs : MeasurableSet s) :
    (forallᵐ y ∂ν, forallᵐ x ∂μ, y + L x in s) ↔ forallᵐ y ∂ν, y in s := by
  have : FiniteDimensional 𝕜 E := .of_locallyCompactSpace 𝕜
  have : FiniteDimensional 𝕜 F := .of_locallyCompactSpace 𝕜
  have : ProperSpace E := .of_locallyCompactSpace 𝕜
  have : ProperSpace F := .of_locallyCompactSpace 𝕜
  let M : F × E ->ₗ[𝕜] F := LinearMap.id.coprod L
  have M_cont : Continuous M := M.continuous_of_finiteDimensional
  -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to change `range_eq_top` into
  -- `range_eq_top (f := _)`
  have hM : Function.Surjective M := by
    simp [M, ← LinearMap.range_eq_top (f := _), LinearMap.range_coprod]
  have A : forall x, M x in s ↔ x in M ⁻¹' s := fun x => Iff.rfl
  simp_rw [← ae_comp_linearMap_mem_iff M (ν.prod μ) ν hM hs, A]
  rw [Measure.ae_prod_mem_iff_ae_ae_mem]
  · simp only [M, mem_preimage, LinearMap.coprod_apply, LinearMap.id_coe, id_eq]
  · exact M_cont.measurable hs

/--
lemma `ae_mem_of_ae_add_linearMap_mem` / 引理 `ae_mem_of_ae_add_linearMap_mem`

English:
lemma ae_mem_of_ae_add_linearMap_mem
  statement: [LocallyCompactSpace F] {s : Set F} (hs : MeasurableSet s)
  proof: (ae_ae_add_linearMap_mem_iff L μ ν hs).1 (Filter.Eventually.of_forall h)

中文:
引理 ae_mem_of_ae_add_linearMap_mem
  结论: [局部紧空间 F] {s : 集合 F} (hs : 可测集 s)
  证明: (ae_ae_add_linearMap_mem_iff L μ ν hs).1 (Filter.Eventually.of_forall h)

Depends on / 依赖: Eventually, Filter, Filter.Eventually.of_forall, ae_ae_add_linearMap_mem_iff, of_forall
-/
lemma ae_mem_of_ae_add_linearMap_mem [LocallyCompactSpace F] {s : Set F} (hs : MeasurableSet s)
    (h : forall y, forallᵐ x ∂μ, y + L x in s) : forallᵐ y ∂ν, y in s :=
  (ae_ae_add_linearMap_mem_iff L μ ν hs).1 (Filter.Eventually.of_forall h)

end MeasureTheory
