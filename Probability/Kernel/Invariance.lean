/-
Copyright (c) 2023 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Matteo Cipollina
-/
module

public import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Invariance of measures along a kernel

We say that a measure `μ` is invariant with respect to a kernel `κ` if its push-forward along the
kernel `μ.bind κ` is the same measure.

## Main definitions

* `ProbabilityTheory.Kernel.Invariant`: invariance of a given measure with respect to a kernel.

-/

@[expose] public section


open MeasureTheory

open scoped MeasureTheory ENNReal ProbabilityTheory

namespace ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

namespace Kernel

/-! ### Invariant measures of kernels -/

/--
Definition of `Invariant` / `Invariant` 的定义

English:
definition Invariant
  signature: (κ : Kernel α α) (μ : Measure α)
  body: μ.bind κ = μ

中文:
定义 Invariant
  签名: (κ : Kernel α α) (μ : Measure α)
  定义体: μ.bind κ = μ
-/
def Invariant (κ : Kernel α α) (μ : Measure α) : Prop :=
  μ.bind κ = μ

variable {κ η : Kernel α α} {μ : Measure α}

/--
theorem `Invariant.def` / 定理 `Invariant.def`

English:
theorem Invariant.def
  given: (hκ : Invariant κ μ)
  statement: μ.bind κ = μ
  proof: hκ

nonrec theorem Invariant.comp_const (hκ : Invariant κ μ) : κ ∘ₖ const α μ = const α μ := by
  rw [comp_const κ μ]; rw [hκ.def]

中文:
定理 Invariant.def
  条件: (hκ : Invariant κ μ)
  结论: μ.bind κ = μ
  证明: hκ

nonrec theorem Invariant.comp_const (hκ : Invariant κ μ) : κ ∘ₖ const α μ = const α μ := by
  rw [comp_const κ μ]; rw [hκ.def]
-/
theorem Invariant.def (hκ : Invariant κ μ) : μ.bind κ = μ :=
  hκ

nonrec theorem Invariant.comp_const (hκ : Invariant κ μ) : κ ∘ₖ const α μ = const α μ := by
  rw [comp_const κ μ]; rw [hκ.def]

/--
theorem `Invariant.comp` / 定理 `Invariant.comp`

English:
theorem Invariant.comp
  given: (hκ : Invariant κ μ) (hη : Invariant η μ)
  proof: by
  rcases isEmpty_or_nonempty α with _ | hα
  · exact Subsingleton.elim _ _
  · rw [Invariant, ← Measure.comp_assoc, hη, hκ]

中文:
定理 Invariant.comp
  条件: (hκ : Invariant κ μ) (hη : Invariant η μ)
  证明: by
  rcases isEmpty_or_nonempty α with _ | hα
  · exact Subsingleton.elim _ _
  · rw [Invariant, ← Measure.comp_assoc, hη, hκ]

Depends on / 依赖: Invariant, Measure, Measure.comp_assoc, Subsingleton, Subsingleton.elim, comp_assoc, isEmpty_or_nonempty
-/
theorem Invariant.comp (hκ : Invariant κ μ) (hη : Invariant η μ) :
    Invariant (κ ∘ₖ η) μ := by
  rcases isEmpty_or_nonempty α with _ | hα
  · exact Subsingleton.elim _ _
  · rw [Invariant, ← Measure.comp_assoc, hη, hκ]

/-! ### Reversibility of kernels -/

/--
Definition of `IsReversible` / `IsReversible` 的定义

English:
definition IsReversible
  signature: (κ : Kernel α α) (π : Measure α)
  body: forall ⦃A B⦄, MeasurableSet A -> MeasurableSet B ->
    ∫⁻ x in A, κ x B ∂π = ∫⁻ x in B, κ x A ∂π

中文:
定义 IsReversible
  签名: (κ : Kernel α α) (π : Measure α)
  定义体: forall ⦃A B⦄, MeasurableSet A -> MeasurableSet B ->
    ∫⁻ x in A, κ x B ∂π = ∫⁻ x in B, κ x A ∂π

Depends on / 依赖: MeasurableSet
-/
def IsReversible (κ : Kernel α α) (π : Measure α) : Prop :=
  forall ⦃A B⦄, MeasurableSet A -> MeasurableSet B ->
    ∫⁻ x in A, κ x B ∂π = ∫⁻ x in B, κ x A ∂π

/--
theorem `IsReversible.invariant` / 定理 `IsReversible.invariant`

English:
theorem IsReversible.invariant
  proof: by
  ext s hs
  calc
    (κ ∘ₘ π) s = ∫⁻ x, κ x s ∂π := by rw [Measure.bind_apply hs (Kernel.aemeasurable _)]
             _ = ∫⁻ x in s, κ x Set.univ ∂π := by simpa [restrict_univ] using (h_rev hs .univ).symm
             _ = π s := by simp

中文:
定理 IsReversible.invariant
  证明: by
  ext s hs
  calc
    (κ ∘ₘ π) s = ∫⁻ x, κ x s ∂π := by rw [Measure.bind_apply hs (Kernel.aemeasurable _)]
             _ = ∫⁻ x in s, κ x Set.univ ∂π := by simpa [restrict_univ] using (h_rev hs .univ).symm
             _ = π s := by simp

Depends on / 依赖: Kernel, Kernel.aemeasurable, Measure, Measure.bind_apply, Set.univ, aemeasurable, bind_apply, h_rev, restrict_univ
-/
theorem IsReversible.invariant
    {κ : Kernel α α} [IsMarkovKernel κ] {π : Measure α}
    (h_rev : IsReversible κ π) : Invariant κ π := by
  ext s hs
  calc
    (κ ∘ₘ π) s = ∫⁻ x, κ x s ∂π := by rw [Measure.bind_apply hs (Kernel.aemeasurable _)]
             _ = ∫⁻ x in s, κ x Set.univ ∂π := by simpa [restrict_univ] using (h_rev hs .univ).symm
             _ = π s := by simp

end Kernel

end ProbabilityTheory
