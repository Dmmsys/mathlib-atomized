/-
Copyright (c) 2025 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.InfinitePi

/-!
# Existence of Random Variables

This file contains lemmas that state the existence of random variables with given distributions
and a given dependency structure (currently only mutual independence is considered).
-/

public section

open MeasureTheory Measure

namespace ProbabilityTheory

universe u v

/--
lemma `_root_.MeasureTheory.Measure.exists_hasLaw` / 引理 `_root_.MeasureTheory.Measure.exists_hasLaw`

English:
lemma _root_.MeasureTheory.Measure.exists_hasLaw
  statement: {𝓧 : Type u} {m𝓧 : MeasurableSpace 𝓧}
  proof: ⟨𝓧, m𝓧, μ, id, measurable_id, .id⟩

中文:
引理 _root_.MeasureTheory.Measure.exists_hasLaw
  结论: {𝓧 : 类型u} {m𝓧 : MeasurableSpace 𝓧}
  证明: ⟨𝓧, m𝓧, μ, id, measurable_id, .id⟩

Depends on / 依赖: measurable_id
-/
lemma _root_.MeasureTheory.Measure.exists_hasLaw {𝓧 : Type u} {m𝓧 : MeasurableSpace 𝓧}
    (μ : Measure 𝓧) :
    exists Ω : Type u, exists _ : MeasurableSpace Ω, exists P : Measure Ω, exists X : Ω -> 𝓧,
      Measurable X ∧ HasLaw X μ P :=
  ⟨𝓧, m𝓧, μ, id, measurable_id, .id⟩

/--
lemma `exists_hasLaw_indepFun` / 引理 `exists_hasLaw_indepFun`

English:
lemma exists_hasLaw_indepFun
  statement: {ι : Type v} (𝓧 : ι -> Type u)
  proof: by
  use Π i, (𝓧 i), .pi, infinitePi μ, fun i => Function.eval i
  refine ⟨by fun_prop, fun i => MeasurePreserving.hasLaw (measurePreserving_eval_infinitePi _ _),
    ?_, by infer_instance⟩
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop)]; rw [map_id']
  congr
  funext i
  exact ((measur

中文:
引理 exists_hasLaw_indepFun
  结论: {ι : 类型v} (𝓧 : ι -> 类型u)
  证明: by
  use Π i, (𝓧 i), .pi, infinitePi μ, fun i => Function.eval i
  refine ⟨by fun_prop, fun i => MeasurePreserving.hasLaw (measurePreserving_eval_infinitePi _ _),
    ?_, by infer_instance⟩
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop)]; rw [map_id']
  congr
  funext i
  exact ((measur

Depends on / 依赖: Function, Function.eval, MeasurePreserving, MeasurePreserving.hasLaw, fun_prop, hasLaw, iIndepFun_iff_map_fun_eq_infinitePi_map, infer_instance, infinitePi, map_eq, map_id, measurePreserving_eval_infinitePi
-/
lemma exists_hasLaw_indepFun {ι : Type v} (𝓧 : ι -> Type u)
    {m𝓧 : forall i, MeasurableSpace (𝓧 i)} (μ : (i : ι) -> Measure (𝓧 i))
    [hμ : forall i, IsProbabilityMeasure (μ i)] :
    exists Ω : Type (max u v), exists _ : MeasurableSpace Ω, exists P : Measure Ω, exists X : (i : ι) -> Ω -> (𝓧 i),
      (forall i, Measurable (X i)) ∧ (forall i, HasLaw (X i) (μ i) P)
        ∧ iIndepFun X P ∧ IsProbabilityMeasure P := by
  use Π i, (𝓧 i), .pi, infinitePi μ, fun i => Function.eval i
  refine ⟨by fun_prop, fun i => MeasurePreserving.hasLaw (measurePreserving_eval_infinitePi _ _),
    ?_, by infer_instance⟩
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop)]; rw [map_id']
  congr
  funext i
  exact ((measurePreserving_eval_infinitePi μ i).map_eq).symm

/--
lemma `exists_iid` / 引理 `exists_iid`

English:
lemma exists_iid
  statement: (ι : Type v) {𝓧 : Type u} {m𝓧 : MeasurableSpace 𝓧}
  proof: exists_hasLaw_indepFun (fun _ => 𝓧) (fun _ => μ)

中文:
引理 exists_iid
  结论: (ι : 类型v) {𝓧 : 类型u} {m𝓧 : MeasurableSpace 𝓧}
  证明: exists_hasLaw_indepFun (fun _ => 𝓧) (fun _ => μ)

Depends on / 依赖: exists_hasLaw_indepFun
-/
lemma exists_iid (ι : Type v) {𝓧 : Type u} {m𝓧 : MeasurableSpace 𝓧}
    (μ : Measure 𝓧) [IsProbabilityMeasure μ] :
    exists Ω : Type (max u v), exists _ : MeasurableSpace Ω, exists P : Measure Ω, exists X : ι -> Ω -> 𝓧,
      (forall i, Measurable (X i)) ∧ (forall i, HasLaw (X i) μ P) ∧ iIndepFun X P ∧ IsProbabilityMeasure P :=
  exists_hasLaw_indepFun (fun _ => 𝓧) (fun _ => μ)

end ProbabilityTheory
