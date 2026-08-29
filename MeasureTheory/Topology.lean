/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
public import Mathlib.Topology.DiscreteSubset

/-!
# Theorems combining measure theory and topology

This file gathers theorems that combine measure theory and topology, and cannot easily be added to
the existing files without introducing massive dependencies between the subjects.
-/

public section
open Filter MeasureTheory

/--
theorem `ae_restrict_le_codiscreteWithin` / 定理 `ae_restrict_le_codiscreteWithin`

English:
theorem ae_restrict_le_codiscreteWithin
  proof: by
  intro s hs
  have : DiscreteTopology ↑(sᶜ inter U) := isDiscrete_iff_discreteTopology.mp
 isDiscrete_of_codiscreteWithin ((compl_compl s).symm ▸ hs)
  rw [mem_ae_iff]; rw [Measure.restrict_apply' hU]
  apply Set.Countable.measure_zero (TopologicalSpace.separableSpace_iff_countable.1 inferInstan

中文:
定理 ae_restrict_le_codiscreteWithin
  证明: by
  intro s hs
  have : DiscreteTopology ↑(sᶜ inter U) := isDiscrete_iff_discreteTopology.mp
 isDiscrete_of_codiscreteWithin ((compl_compl s).symm ▸ hs)
  rw [mem_ae_iff]; rw [Measure.restrict_apply' hU]
  apply Set.Countable.measure_zero (TopologicalSpace.separableSpace_iff_countable.1 inferInstan

Depends on / 依赖: Countable, DiscreteTopology, Measure, Measure.restrict_apply, Set.Countable.measure_zero, TopologicalSpace, TopologicalSpace.separableSpace_iff_countable, compl_compl, isDiscrete_iff_discreteTopology, isDiscrete_iff_discreteTopology.mp, isDiscrete_of_codiscreteWithin, measure_zero, mem_ae_iff, restrict_apply, separableSpace_iff_countable
-/
theorem ae_restrict_le_codiscreteWithin
    {α : Type*} [MeasurableSpace α] [TopologicalSpace α] [SecondCountableTopology α]
    {μ : Measure α} [NullSingletonClass μ] {U : Set α} (hU : MeasurableSet U) :
    ae (μ.restrict U) <= codiscreteWithin U := by
  intro s hs
  have : DiscreteTopology ↑(sᶜ inter U) := isDiscrete_iff_discreteTopology.mp
 isDiscrete_of_codiscreteWithin ((compl_compl s).symm ▸ hs)
  rw [mem_ae_iff]; rw [Measure.restrict_apply' hU]
  apply Set.Countable.measure_zero (TopologicalSpace.separableSpace_iff_countable.1 inferInstance)
