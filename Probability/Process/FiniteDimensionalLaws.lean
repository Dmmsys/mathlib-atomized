/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Jonas Bayer
-/
module

public import Mathlib.MeasureTheory.Constructions.Projective
public import Mathlib.Probability.IdentDistrib

/-!
# Finite-dimensional distributions of a stochastic process

For a stochastic process `X : T → Ω → 𝓧` and a finite measure `P` on `Ω`, the law of the process is
`P.map (fun ω ↦ (X · ω))`, and its finite-dimensional distributions are
`P.map (fun ω ↦ I.restrict (X · ω))` for `I : Finset T`.

We show that two stochastic processes have the same laws if and only if they have the same
finite-dimensional distributions.

## Main statements

* `map_eq_iff_forall_finset_map_restrict_eq`: two processes have the same law if and only if
  their finite-dimensional distributions are equal.
* `identDistrib_iff_forall_finset_identDistrib`: same statement, but stated in terms of
  `IdentDistrib`.
* `map_restrict_eq_of_forall_ae_eq`: if two processes are modifications of each other, then
  their finite-dimensional distributions are equal.
* `map_eq_of_forall_ae_eq`: if two processes are modifications of each other, then they have the
  same law.

-/

public section

open MeasureTheory

namespace ProbabilityTheory

variable {T Ω : Type*} {𝓧 : T -> Type*} {mΩ : MeasurableSpace Ω} {mα : forall t, MeasurableSpace (𝓧 t)}
  {X Y : (t : T) -> Ω -> 𝓧 t} {P : Measure Ω}

/--
lemma `isProjectiveMeasureFamily_map_restrict` / 引理 `isProjectiveMeasureFamily_map_restrict`

English:
lemma isProjectiveMeasureFamily_map_restrict
  given: (hX : forall t, AEMeasurable (X t) P)
  proof: by
  intro I J hJI
  rw [AEMeasurable.map_map_of_aemeasurable (Finset.measurable_restrict₂ _).aemeasurable]
  · simp [Finset.restrict_def, Finset.restrict₂_def, Function.comp_def]
  · exact aemeasurable_pi_lambda _ fun _ => hX _

中文:
引理 isProjectiveMeasureFamily_map_restrict
  条件: (hX : 对任意 t, 几乎处处可测 (X t) P)
  证明: by
  intro I J hJI
  rw [AEMeasurable.map_map_of_aemeasurable (Finset.measurable_restrict₂ _).aemeasurable]
  · simp [Finset.restrict_def, Finset.restrict₂_def, Function.comp_def]
  · exact aemeasurable_pi_lambda _ fun _ => hX _

Depends on / 依赖: AEMeasurable, AEMeasurable.map_map_of_aemeasurable, Finset, Finset.measurable_restrict, Finset.restrict, Finset.restrict_def, Function, Function.comp_def, aemeasurable, aemeasurable_pi_lambda, comp_def, map_map_of_aemeasurable, restrict_def
-/
lemma isProjectiveMeasureFamily_map_restrict (hX : forall t, AEMeasurable (X t) P) :
    IsProjectiveMeasureFamily (fun I => P.map (fun ω => I.restrict (X · ω))) := by
  intro I J hJI
  rw [AEMeasurable.map_map_of_aemeasurable (Finset.measurable_restrict₂ _).aemeasurable]
  · simp [Finset.restrict_def, Finset.restrict₂_def, Function.comp_def]
  · exact aemeasurable_pi_lambda _ fun _ => hX _

/--
lemma `isProjectiveLimit_map` / 引理 `isProjectiveLimit_map`

English:
lemma isProjectiveLimit_map
  given: (hX : AEMeasurable (fun ω => (X · ω)) P)
  proof: by
  intro I
  rw [AEMeasurable.map_map_of_aemeasurable (Finset.measurable_restrict _).aemeasurable hX]; rw [Function.comp_def]

中文:
引理 isProjectiveLimit_map
  条件: (hX : 几乎处处可测 (fun ω => (X · ω)) P)
  证明: by
  intro I
  rw [AEMeasurable.map_map_of_aemeasurable (Finset.measurable_restrict _).aemeasurable hX]; rw [Function.comp_def]

Depends on / 依赖: AEMeasurable, AEMeasurable.map_map_of_aemeasurable, DistribMulAction, Finset, Finset.measurable_restrict, Function, Function.comp_def, Monoid, aemeasurable, comp_def, isScalarTower_right, map_map_of_aemeasurable, measurable_restrict
-/
lemma isProjectiveLimit_map (hX : AEMeasurable (fun ω => (X · ω)) P) :
    IsProjectiveLimit (P.map (fun ω => (X · ω))) (fun I => P.map (fun ω => I.restrict (X · ω))) := by
  intro I
  rw [AEMeasurable.map_map_of_aemeasurable (Finset.measurable_restrict _).aemeasurable hX]; rw [Function.comp_def]

/--
lemma `map_eq_iff_forall_finset_map_restrict_eq` / 引理 `map_eq_iff_forall_finset_map_restrict_eq`

English:
lemma map_eq_iff_forall_finset_map_restrict_eq
  statement: [IsFiniteMeasure P]
  proof: by
  refine ⟨fun h I => ?_, fun h => ?_⟩
  · have hX' : P.map (fun ω => I.restrict (X · ω)) = (P.map (fun ω => (X · ω))).map I.restrict := by
      rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) hX]; rw [Function.comp_def]
    have hY' : P.map (fun ω => I.restrict (Y · ω)) = (P.map (fun ω =>

中文:
引理 map_eq_iff_对任意_finset_map_restrict_eq
  结论: [是有限测度 P]
  证明: by
  refine ⟨fun h I => ?_, fun h => ?_⟩
  · have hX' : P.map (fun ω => I.restrict (X · ω)) = (P.map (fun ω => (X · ω))).map I.restrict := by
      rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) hX]; rw [Function.comp_def]
    have hY' : P.map (fun ω => I.restrict (Y · ω)) = (P.map (fun ω =>

Depends on / 依赖: AEMeasurable, AEMeasurable.map_map_of_aemeasurable, DistribMulAction, Function, Function.comp_def, I.restrict, Monoid, P.map, comp_def, fun_prop, isProjectiveLimit_map, map_map_of_aemeasurable, restrict, sMulCommClass_right, simp_rw
-/
lemma map_eq_iff_forall_finset_map_restrict_eq [IsFiniteMeasure P]
    (hX : AEMeasurable (fun ω => (X · ω)) P) (hY : AEMeasurable (fun ω => (Y · ω)) P) :
    P.map (fun ω => (X · ω)) = P.map (fun ω => (Y · ω))
    ↔ forall I : Finset T, P.map (fun ω => I.restrict (X · ω)) = P.map (fun ω => I.restrict (Y · ω)) := by
  refine ⟨fun h I => ?_, fun h => ?_⟩
  · have hX' : P.map (fun ω => I.restrict (X · ω)) = (P.map (fun ω => (X · ω))).map I.restrict := by
      rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) hX]; rw [Function.comp_def]
    have hY' : P.map (fun ω => I.restrict (Y · ω)) = (P.map (fun ω => (Y · ω))).map I.restrict := by
      rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) hY]; rw [Function.comp_def]
    rw [hX']; rw [hY']; rw [h]
  · have hX' := isProjectiveLimit_map hX
    simp_rw [h] at hX'
    exact hX'.unique (isProjectiveLimit_map hY)

/--
lemma `identDistrib_iff_forall_finset_identDistrib` / 引理 `identDistrib_iff_forall_finset_identDistrib`

English:
lemma identDistrib_iff_forall_finset_identDistrib
  statement: [IsFiniteMeasure P]
  proof: by
  refine ⟨fun h I => ⟨?_, ?_, ?_⟩, fun h => ⟨hX, hY, ?_⟩⟩
  · exact (Finset.measurable_restrict _).comp_aemeasurable hX
  · exact (Finset.measurable_restrict _).comp_aemeasurable hY
  · exact (map_eq_iff_forall_finset_map_restrict_eq hX hY).mp h.map_eq I
  · exact (map_eq_iff_forall_finset_map_re

中文:
引理 identDistrib_iff_对任意_finset_identDistrib
  结论: [是有限测度 P]
  证明: by
  refine ⟨fun h I => ⟨?_, ?_, ?_⟩, fun h => ⟨hX, hY, ?_⟩⟩
  · exact (Finset.measurable_restrict _).comp_aemeasurable hX
  · exact (Finset.measurable_restrict _).comp_aemeasurable hY
  · exact (map_eq_iff_forall_finset_map_restrict_eq hX hY).mp h.map_eq I
  · exact (map_eq_iff_forall_finset_map_re

Depends on / 依赖: Finset, Finset.measurable_restrict, comp_aemeasurable, h.map_eq, map_eq, map_eq_iff_forall_finset_map_restrict_eq, measurable_restrict
-/
lemma identDistrib_iff_forall_finset_identDistrib [IsFiniteMeasure P]
    (hX : AEMeasurable (fun ω => (X · ω)) P) (hY : AEMeasurable (fun ω => (Y · ω)) P) :
    IdentDistrib (fun ω => (X · ω)) (fun ω => (Y · ω)) P P
      ↔ forall I : Finset T,
        IdentDistrib (fun ω => I.restrict (X · ω)) (fun ω => I.restrict (Y · ω)) P P := by
  refine ⟨fun h I => ⟨?_, ?_, ?_⟩, fun h => ⟨hX, hY, ?_⟩⟩
  · exact (Finset.measurable_restrict _).comp_aemeasurable hX
  · exact (Finset.measurable_restrict _).comp_aemeasurable hY
  · exact (map_eq_iff_forall_finset_map_restrict_eq hX hY).mp h.map_eq I
  · exact (map_eq_iff_forall_finset_map_restrict_eq hX hY).mpr (fun I => (h I).map_eq)

/--
lemma `map_restrict_eq_of_forall_ae_eq` / 引理 `map_restrict_eq_of_forall_ae_eq`

English:
lemma map_restrict_eq_of_forall_ae_eq
  given: (h : forall t, X t =ᵐ[P] Y t) (I : Finset T)
  proof: by
  have h' : forallᵐ ω ∂P, forall (i : I), X i ω = Y i ω := by
    rw [MeasureTheory.ae_all_iff]
    exact fun i => h i
  refine Measure.map_congr ?_
  filter_upwards [h'] with ω h using funext h

中文:
引理 map_restrict_eq_of_对任意_ae_eq
  条件: (h : 对任意 t, X t =ᵐ[P] Y t) (I : 有限集 T)
  证明: by
  have h' : forallᵐ ω ∂P, forall (i : I), X i ω = Y i ω := by
    rw [MeasureTheory.ae_all_iff]
    exact fun i => h i
  refine Measure.map_congr ?_
  filter_upwards [h'] with ω h using funext h

Depends on / 依赖: Measure, Measure.map_congr, MeasureTheory, MeasureTheory.ae_all_iff, ae_all_iff, filter_upwards, map_congr
-/
lemma map_restrict_eq_of_forall_ae_eq (h : forall t, X t =ᵐ[P] Y t) (I : Finset T) :
    P.map (fun ω => I.restrict (X · ω)) = P.map (fun ω => I.restrict (Y · ω)) := by
  have h' : forallᵐ ω ∂P, forall (i : I), X i ω = Y i ω := by
    rw [MeasureTheory.ae_all_iff]
    exact fun i => h i
  refine Measure.map_congr ?_
  filter_upwards [h'] with ω h using funext h

/--
lemma `map_eq_of_forall_ae_eq` / 引理 `map_eq_of_forall_ae_eq`

English:
lemma map_eq_of_forall_ae_eq
  statement: [IsFiniteMeasure P]
  proof: by
  rw [map_eq_iff_forall_finset_map_restrict_eq hX hY]
  exact fun I => map_restrict_eq_of_forall_ae_eq h I

中文:
引理 map_eq_of_对任意_ae_eq
  结论: [是有限测度 P]
  证明: by
  rw [map_eq_iff_forall_finset_map_restrict_eq hX hY]
  exact fun I => map_restrict_eq_of_forall_ae_eq h I

Depends on / 依赖: map_eq_iff_forall_finset_map_restrict_eq, map_restrict_eq_of_forall_ae_eq
-/
lemma map_eq_of_forall_ae_eq [IsFiniteMeasure P]
    (hX : AEMeasurable (fun ω => (X · ω)) P) (hY : AEMeasurable (fun ω => (Y · ω)) P)
    (h : forall t, X t =ᵐ[P] Y t) :
    P.map (fun ω => (X · ω)) = P.map (fun ω => (Y · ω)) := by
  rw [map_eq_iff_forall_finset_map_restrict_eq hX hY]
  exact fun I => map_restrict_eq_of_forall_ae_eq h I

end ProbabilityTheory
