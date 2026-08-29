/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Scaling Haar measure by a continuous isomorphism

If `G` is a locally compact topological group and `μ` is a regular Haar measure
on `G`, then an isomorphism `φ : G ≃ₜ* G` scales this measure by some positive
real constant which we call `mulEquivHaarChar φ`.

## Main definitions

* `mulEquivHaarChar φ`: the positive real such that `(mulEquivHaarChar φ) • map φ μ = μ`
  for `μ` a regular Haar measure.
* `addEquivAddHaarChar φ`: the additive version.

-/

@[expose] public section

open MeasureTheory.Measure

open scoped NNReal Pointwise ENNReal

namespace MeasureTheory

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]
    [BorelSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]

/-- If `φ : G ≃ₜ* G` then `mulEquivHaarChar φ` is the positive real factor by which
`φ` scales Haar measures on `G`. -/
@[to_additive /-- If `φ : A ≃ₜ+ A` then `addEquivAddHaarChar φ` is the positive
real factor by which `φ` scales Haar measures on `A`. -/]
/--
Definition of `mulEquivHaarChar` / `mulEquivHaarChar` 的定义

English:
definition mulEquivHaarChar
  signature: (φ : G ≃ₜ* G)
  body: haarScalarFactor haar (haar.map φ)

@[to_additive]

中文:
定义 mulEquivHaarChar
  签名: (φ : G ≃ₜ* G)
  定义体: haarScalarFactor haar (haar.map φ)

@[to_additive]

Depends on / 依赖: haar.map, haarScalarFactor
-/
noncomputable def mulEquivHaarChar (φ : G ≃ₜ* G) : Real>=0 :=
  haarScalarFactor haar (haar.map φ)

@[to_additive]
/--
lemma `mulEquivHaarChar_pos` / 引理 `mulEquivHaarChar_pos`

English:
lemma mulEquivHaarChar_pos
  given: (φ : G ≃ₜ* G)
  statement: 0 < mulEquivHaarChar φ
  proof: haarScalarFactor_pos_of_isHaarMeasure _ _

@[to_additive]

中文:
引理 mulEquivHaarChar_pos
  条件: (φ : G ≃ₜ* G)
  结论: 0 < mulEquivHaarChar φ
  证明: haarScalarFactor_pos_of_isHaarMeasure _ _

@[to_additive]

Depends on / 依赖: haarScalarFactor_pos_of_isHaarMeasure
-/
lemma mulEquivHaarChar_pos (φ : G ≃ₜ* G) : 0 < mulEquivHaarChar φ :=
  haarScalarFactor_pos_of_isHaarMeasure _ _

@[to_additive]
/--
lemma `mulEquivHaarChar_eq` / 引理 `mulEquivHaarChar_eq`

English:
lemma mulEquivHaarChar_eq
  statement: (μ : Measure G) [IsHaarMeasure μ]
  proof: by
  have smul := isMulLeftInvariant_eq_smul_of_regular haar μ
  unfold mulEquivHaarChar
  conv =>
    enter [1, 1]
    rw [smul]
  conv =>
    enter [1, 2, 2]
    rw [smul]
  simp_rw [MeasureTheory.Measure.map_smul]
  exact haarScalarFactor_smul_smul _ _ (haarScalarFactor_pos_of_isHaarMeasure haar 

中文:
引理 mulEquivHaarChar_eq
  结论: (μ : Measure G) [IsHaarMeasure μ]
  证明: by
  have smul := isMulLeftInvariant_eq_smul_of_regular haar μ
  unfold mulEquivHaarChar
  conv =>
    enter [1, 1]
    rw [smul]
  conv =>
    enter [1, 2, 2]
    rw [smul]
  simp_rw [MeasureTheory.Measure.map_smul]
  exact haarScalarFactor_smul_smul _ _ (haarScalarFactor_pos_of_isHaarMeasure haar 

Depends on / 依赖: Measure, MeasureTheory, MeasureTheory.Measure.map_smul, haarScalarFactor_pos_of_isHaarMeasure, haarScalarFactor_smul_smul, isMulLeftInvariant_eq_smul_of_regular, map_smul, mulEquivHaarChar, simp_rw
-/
lemma mulEquivHaarChar_eq (μ : Measure G) [IsHaarMeasure μ]
    [Regular μ] (φ : G ≃ₜ* G) :
    mulEquivHaarChar φ = haarScalarFactor μ (μ.map φ) := by
  have smul := isMulLeftInvariant_eq_smul_of_regular haar μ
  unfold mulEquivHaarChar
  conv =>
    enter [1, 1]
    rw [smul]
  conv =>
    enter [1, 2, 2]
    rw [smul]
  simp_rw [MeasureTheory.Measure.map_smul]
  exact haarScalarFactor_smul_smul _ _ (haarScalarFactor_pos_of_isHaarMeasure haar μ).ne'

@[to_additive addEquivAddHaarChar_smul_map]
/--
lemma `mulEquivHaarChar_smul_map` / 引理 `mulEquivHaarChar_smul_map`

English:
lemma mulEquivHaarChar_smul_map
  statement: (μ : Measure G)
  proof: by
  rw [mulEquivHaarChar_eq μ φ]
  have : Regular (map φ μ) := Regular.map φ.toHomeomorph
  exact (isMulLeftInvariant_eq_smul_of_regular μ (map φ μ)).symm

@[to_additive addEquivAddHaarChar_smul_eq_comap]

中文:
引理 mulEquivHaarChar_smul_map
  结论: (μ : Measure G)
  证明: by
  rw [mulEquivHaarChar_eq μ φ]
  have : Regular (map φ μ) := Regular.map φ.toHomeomorph
  exact (isMulLeftInvariant_eq_smul_of_regular μ (map φ μ)).symm

@[to_additive addEquivAddHaarChar_smul_eq_comap]

Depends on / 依赖: Regular, Regular.map, isMulLeftInvariant_eq_smul_of_regular, mulEquivHaarChar_eq, toHomeomorph
-/
lemma mulEquivHaarChar_smul_map (μ : Measure G)
    [IsHaarMeasure μ] [Regular μ] (φ : G ≃ₜ* G) :
    mulEquivHaarChar φ • μ.map φ = μ := by
  rw [mulEquivHaarChar_eq μ φ]
  have : Regular (map φ μ) := Regular.map φ.toHomeomorph
  exact (isMulLeftInvariant_eq_smul_of_regular μ (map φ μ)).symm

@[to_additive addEquivAddHaarChar_smul_eq_comap]
/--
lemma `mulEquivHaarChar_smul_eq_comap` / 引理 `mulEquivHaarChar_smul_eq_comap`

English:
lemma mulEquivHaarChar_smul_eq_comap
  statement: (μ : Measure G)
  proof: by
  let e := φ.toHomeomorph.toMeasurableEquiv
  rw [show ⇑φ = ⇑e from rfl]; rw [← e.map_symm]; rw [show ⇑e.symm = ⇑φ.symm from rfl]
  have : (map (φ.symm) μ).Regular := Regular.map φ.symm.toHomeomorph
  rw [← mulEquivHaarChar_smul_map (map φ.symm μ) φ]; rw [map_map]
  · simp
  · fun_prop
  · fun_pr

中文:
引理 mulEquivHaarChar_smul_eq_comap
  结论: (μ : Measure G)
  证明: by
  let e := φ.toHomeomorph.toMeasurableEquiv
  rw [show ⇑φ = ⇑e from rfl]; rw [← e.map_symm]; rw [show ⇑e.symm = ⇑φ.symm from rfl]
  have : (map (φ.symm) μ).Regular := Regular.map φ.symm.toHomeomorph
  rw [← mulEquivHaarChar_smul_map (map φ.symm μ) φ]; rw [map_map]
  · simp
  · fun_prop
  · fun_pr

Depends on / 依赖: Regular, Regular.map, e.map_symm, e.symm, fun_prop, map_map, map_symm, mulEquivHaarChar_smul_map, symm.toHomeomorph, toHomeomorph, toHomeomorph.toMeasurableEquiv, toMeasurableEquiv
-/
lemma mulEquivHaarChar_smul_eq_comap (μ : Measure G)
    [IsHaarMeasure μ] [Regular μ] (φ : G ≃ₜ* G) :
    (mulEquivHaarChar φ) • μ = μ.comap φ := by
  let e := φ.toHomeomorph.toMeasurableEquiv
  rw [show ⇑φ = ⇑e from rfl]; rw [← e.map_symm]; rw [show ⇑e.symm = ⇑φ.symm from rfl]
  have : (map (φ.symm) μ).Regular := Regular.map φ.symm.toHomeomorph
  rw [← mulEquivHaarChar_smul_map (map φ.symm μ) φ]; rw [map_map]
  · simp
  · fun_prop
  · fun_prop

@[to_additive addEquivAddHaarChar_smul_integral_map]
/--
lemma `mulEquivHaarChar_smul_integral_map` / 引理 `mulEquivHaarChar_smul_integral_map`

English:
lemma mulEquivHaarChar_smul_integral_map
  statement: (μ : Measure G)
  proof: by
  nth_rw 2 [← mulEquivHaarChar_smul_map μ φ]
  simp

@[to_additive integral_comap_eq_addEquivAddHaarChar_smul]

中文:
引理 mulEquivHaarChar_smul_integral_map
  结论: (μ : Measure G)
  证明: by
  nth_rw 2 [← mulEquivHaarChar_smul_map μ φ]
  simp

@[to_additive integral_comap_eq_addEquivAddHaarChar_smul]

Depends on / 依赖: mulEquivHaarChar_smul_map, nth_rw
-/
lemma mulEquivHaarChar_smul_integral_map (μ : Measure G)
    [IsHaarMeasure μ] [Regular μ] {f : G -> Real} (φ : G ≃ₜ* G) :
    mulEquivHaarChar φ • ∫ a, f a ∂(μ.map φ) = ∫ a, f a ∂μ := by
  nth_rw 2 [← mulEquivHaarChar_smul_map μ φ]
  simp

@[to_additive integral_comap_eq_addEquivAddHaarChar_smul]
/--
lemma `integral_comap_eq_mulEquivHaarChar_smul` / 引理 `integral_comap_eq_mulEquivHaarChar_smul`

English:
lemma integral_comap_eq_mulEquivHaarChar_smul
  statement: (μ : Measure G)
  proof: by
  let e := φ.toHomeomorph.toMeasurableEquiv
  change ∫ a, f a ∂(comap e μ) = mulEquivHaarChar φ • ∫ a, f a ∂μ
  have : (map (e.symm) μ).IsHaarMeasure := φ.symm.isHaarMeasure_map μ
  have : (map (e.symm) μ).Regular := Regular.map φ.symm.toHomeomorph
  rw [← e.map_symm]; rw [← mulEquivHaarChar_smul

中文:
引理 integral_comap_eq_mulEquivHaarChar_smul
  结论: (μ : Measure G)
  证明: by
  let e := φ.toHomeomorph.toMeasurableEquiv
  change ∫ a, f a ∂(comap e μ) = mulEquivHaarChar φ • ∫ a, f a ∂μ
  have : (map (e.symm) μ).IsHaarMeasure := φ.symm.isHaarMeasure_map μ
  have : (map (e.symm) μ).Regular := Regular.map φ.symm.toHomeomorph
  rw [← e.map_symm]; rw [← mulEquivHaarChar_smul

Depends on / 依赖: IsHaarMeasure, Regular, Regular.map, e.map_symm, e.symm, e.symm.measurable, isHaarMeasure_map, map_map, map_symm, measurable, mulEquivHaarChar, mulEquivHaarChar_smul_integral_map, symm.isHaarMeasure_map, symm.toHomeomorph, toHomeomorph, toHomeomorph.toMeasurableEquiv, toHomeomorph.toMeasurableEquiv.measurable, toMeasurableEquiv
-/
lemma integral_comap_eq_mulEquivHaarChar_smul (μ : Measure G)
    [IsHaarMeasure μ] [Regular μ] {f : G -> Real} (φ : G ≃ₜ* G) :
    ∫ a, f a ∂(μ.comap φ) = mulEquivHaarChar φ • ∫ a, f a ∂μ := by
  let e := φ.toHomeomorph.toMeasurableEquiv
  change ∫ a, f a ∂(comap e μ) = mulEquivHaarChar φ • ∫ a, f a ∂μ
  have : (map (e.symm) μ).IsHaarMeasure := φ.symm.isHaarMeasure_map μ
  have : (map (e.symm) μ).Regular := Regular.map φ.symm.toHomeomorph
  rw [← e.map_symm]; rw [← mulEquivHaarChar_smul_integral_map (map e.symm μ) φ]; rw [map_map (by exact φ.toHomeomorph.toMeasurableEquiv.measurable) e.symm.measurable]
  -- congr -- breaks to_additive
  rw [show ⇑φ ∘ ⇑e.symm = id by ext; simp [e]]
  simp

@[to_additive addEquivAddHaarChar_smul_preimage]
/--
lemma `mulEquivHaarChar_smul_preimage` / 引理 `mulEquivHaarChar_smul_preimage`

English:
lemma mulEquivHaarChar_smul_preimage
  proof: by
  nth_rw 2 [← mulEquivHaarChar_smul_map μ φ]
  simp only [Measure.smul_apply, nnreal_smul_coe_apply]
exact congr_arg _ (MeasurableEquiv.map_apply φ.toMeasurableEquiv X).symm

@[to_additive (attr := simp)]

中文:
引理 mulEquivHaarChar_smul_preimage
  证明: by
  nth_rw 2 [← mulEquivHaarChar_smul_map μ φ]
  simp only [Measure.smul_apply, nnreal_smul_coe_apply]
exact congr_arg _ (MeasurableEquiv.map_apply φ.toMeasurableEquiv X).symm

@[to_additive (attr := simp)]

Depends on / 依赖: MeasurableEquiv, MeasurableEquiv.map_apply, Measure, Measure.smul_apply, congr_arg, map_apply, mulEquivHaarChar_smul_map, nnreal_smul_coe_apply, nth_rw, smul_apply, toMeasurableEquiv
-/
lemma mulEquivHaarChar_smul_preimage
    (μ : Measure G) [IsHaarMeasure μ] [Regular μ] {X : Set G} (φ : G ≃ₜ* G) :
    mulEquivHaarChar φ • μ (φ ⁻¹' X) = μ X := by
  nth_rw 2 [← mulEquivHaarChar_smul_map μ φ]
  simp only [Measure.smul_apply, nnreal_smul_coe_apply]
exact congr_arg _ (MeasurableEquiv.map_apply φ.toMeasurableEquiv X).symm

@[to_additive (attr := simp)]
/--
lemma `mulEquivHaarChar_refl` / 引理 `mulEquivHaarChar_refl`

English:
lemma mulEquivHaarChar_refl
  proof: by
  simp [mulEquivHaarChar, Function.id_def]

@[to_additive]

中文:
引理 mulEquivHaarChar_refl
  证明: by
  simp [mulEquivHaarChar, Function.id_def]

@[to_additive]

Depends on / 依赖: Function, Function.id_def, id_def, mulEquivHaarChar
-/
lemma mulEquivHaarChar_refl :
    mulEquivHaarChar (ContinuousMulEquiv.refl G) = 1 := by
  simp [mulEquivHaarChar, Function.id_def]

@[to_additive]
/--
lemma `mulEquivHaarChar_trans` / 引理 `mulEquivHaarChar_trans`

English:
lemma mulEquivHaarChar_trans
  given: {φ ψ : G ≃ₜ* G}
  proof: by
  rw [mulEquivHaarChar_eq haar ψ]; rw [mulEquivHaarChar_eq haar (ψ.trans φ)]
  have hφ : Measurable φ := by fun_prop
  have hψ : Measurable ψ := by fun_prop
  simp_rw [ContinuousMulEquiv.coe_trans, ← map_map hφ hψ]
  have h_reg : (haar.map ψ).Regular := Regular.map ψ.toHomeomorph
  rw [MeasureThe

中文:
引理 mulEquivHaarChar_trans
  条件: {φ ψ : G ≃ₜ* G}
  证明: by
  rw [mulEquivHaarChar_eq haar ψ]; rw [mulEquivHaarChar_eq haar (ψ.trans φ)]
  have hφ : Measurable φ := by fun_prop
  have hψ : Measurable ψ := by fun_prop
  simp_rw [ContinuousMulEquiv.coe_trans, ← map_map hφ hψ]
  have h_reg : (haar.map ψ).Regular := Regular.map ψ.toHomeomorph
  rw [MeasureThe

Depends on / 依赖: ContinuousMulEquiv, ContinuousMulEquiv.coe_trans, Measurable, Measure, MeasureTheory, MeasureTheory.Measure.haarScalarFactor_eq_mul, Regular, Regular.map, coe_trans, fun_prop, h_reg, haar.map, haarScalarFactor_eq_mul, map_map, mulEquivHaarChar_eq, simp_rw, toHomeomorph
-/
lemma mulEquivHaarChar_trans {φ ψ : G ≃ₜ* G} :
    mulEquivHaarChar (ψ.trans φ) = mulEquivHaarChar ψ * mulEquivHaarChar φ := by
  rw [mulEquivHaarChar_eq haar ψ]; rw [mulEquivHaarChar_eq haar (ψ.trans φ)]
  have hφ : Measurable φ := by fun_prop
  have hψ : Measurable ψ := by fun_prop
  simp_rw [ContinuousMulEquiv.coe_trans, ← map_map hφ hψ]
  have h_reg : (haar.map ψ).Regular := Regular.map ψ.toHomeomorph
  rw [MeasureTheory.Measure.haarScalarFactor_eq_mul haar (haar.map ψ)]; rw [← mulEquivHaarChar_eq (haar.map ψ)]

@[to_additive]
/--
lemma `mulEquivHaarChar_symm` / 引理 `mulEquivHaarChar_symm`

English:
lemma mulEquivHaarChar_symm
  given: {φ : G ≃ₜ* G}
  proof: by
  symm
  apply inv_eq_of_mul_eq_one_right
  simp [← mulEquivHaarChar_trans]

中文:
引理 mulEquivHaarChar_symm
  条件: {φ : G ≃ₜ* G}
  证明: by
  symm
  apply inv_eq_of_mul_eq_one_right
  simp [← mulEquivHaarChar_trans]

Depends on / 依赖: inv_eq_of_mul_eq_one_right, mulEquivHaarChar_trans
-/
lemma mulEquivHaarChar_symm {φ : G ≃ₜ* G} :
    mulEquivHaarChar φ.symm = (mulEquivHaarChar φ)⁻¹ := by
  symm
  apply inv_eq_of_mul_eq_one_right
  simp [← mulEquivHaarChar_trans]

open TopologicalSpace Set in
@[to_additive addEquivAddHaarChar_eq_one_of_compactSpace]
/--
lemma `mulEquivHaarChar_eq_one_of_compactSpace` / 引理 `mulEquivHaarChar_eq_one_of_compactSpace`

English:
lemma mulEquivHaarChar_eq_one_of_compactSpace
  given: [CompactSpace G] (φ : G ≃ₜ* G)
  proof: by
  set μ := haarMeasure (⟨⟨univ, isCompact_univ⟩, by simp⟩ : PositiveCompacts G)
  have hμ : μ univ = 1 := haarMeasure_self
  rw [mulEquivHaarChar_eq μ]
  suffices (μ.haarScalarFactor (map φ μ) : Real>=0∞) = 1 by exact_mod_cast this
  calc
    _ = μ.haarScalarFactor (map φ μ) • (1 : Real>=0∞) := b

中文:
引理 mulEquivHaarChar_eq_one_of_compactSpace
  条件: [CompactSpace G] (φ : G ≃ₜ* G)
  证明: by
  set μ := haarMeasure (⟨⟨univ, isCompact_univ⟩, by simp⟩ : PositiveCompacts G)
  have hμ : μ univ = 1 := haarMeasure_self
  rw [mulEquivHaarChar_eq μ]
  suffices (μ.haarScalarFactor (map φ μ) : Real>=0∞) = 1 by exact_mod_cast this
  calc
    _ = μ.haarScalarFactor (map φ μ) • (1 : Real>=0∞) := b

Depends on / 依赖: ENNReal, ENNReal.smul_def, PositiveCompacts, Set.preimage_univ, conv_rhs, haarMeasure, haarMeasure_self, haarScalarFactor, isCompact_univ, map_apply, map_continuous, measurable, mulEquivHaarChar_eq, mul_one, preimage_univ, smul_def, smul_eq_mul
-/
lemma mulEquivHaarChar_eq_one_of_compactSpace [CompactSpace G] (φ : G ≃ₜ* G) :
    mulEquivHaarChar φ = 1 := by
  set μ := haarMeasure (⟨⟨univ, isCompact_univ⟩, by simp⟩ : PositiveCompacts G)
  have hμ : μ univ = 1 := haarMeasure_self
  rw [mulEquivHaarChar_eq μ]
  suffices (μ.haarScalarFactor (map φ μ) : Real>=0∞) = 1 by exact_mod_cast this
  calc
    _ = μ.haarScalarFactor (map φ μ) • (1 : Real>=0∞) := by rw [ENNReal.smul_def, smul_eq_mul, mul_one]
    _ = μ.haarScalarFactor (map φ μ) • (map φ μ univ) := by
          rw [map_apply (map_continuous φ).measurable .univ]; rw [Set.preimage_univ]; rw [hμ]
    _ = μ univ := by
          conv_rhs => rw [isMulInvariant_eq_smul_of_compactSpace μ (map φ μ), Measure.smul_apply]
    _ = 1 := hμ

end MeasureTheory
