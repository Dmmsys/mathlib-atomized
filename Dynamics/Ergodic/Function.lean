/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.MeasureTheory.Function.AEEqFun

/-!
# Functions invariant under a (quasi)ergodic map

In this file we prove that an a.e. strongly measurable function `g : α → X`
that is a.e. invariant under a (quasi)ergodic map is a.e. equal to a constant.
We prove several versions of this statement with slightly different measurability assumptions.
We also formulate a version for `MeasureTheory.AEEqFun` functions
with all a.e. equalities replaced with equalities in the quotient space.
-/

public section

open Function Set Filter MeasureTheory Topology TopologicalSpace

variable {α X : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}

/--
theorem `QuasiErgodic.ae_eq_const_of_ae_eq_comp_of_ae_range₀` / 定理 `QuasiErgodic.ae_eq_const_of_ae_eq_comp_of_ae_range₀`

English:
theorem QuasiErgodic.ae_eq_const_of_ae_eq_comp_of_ae_range₀
  statement: [Nonempty X] [MeasurableSpace X]
  proof: by
  refine exists_eventuallyEq_const_of_eventually_mem_of_forall_separating MeasurableSet hs ?_
  refine fun U hU => h.ae_mem_or_ae_notMem₀ (s := g ⁻¹' U) (hgm hU) ?_b
  refine (hg_eq.mono fun x hx => ?_).set_eq
  rw [← preimage_comp]; rw [mem_preimage]; rw [mem_preimage]; rw [hx]

中文:
定理 QuasiErgodic.ae_eq_const_of_ae_eq_comp_of_ae_range₀
  结论: [Nonempty X] [MeasurableSpace X]
  证明: by
  refine exists_eventuallyEq_const_of_eventually_mem_of_forall_separating MeasurableSet hs ?_
  refine fun U hU => h.ae_mem_or_ae_notMem₀ (s := g ⁻¹' U) (hgm hU) ?_b
  refine (hg_eq.mono fun x hx => ?_).set_eq
  rw [← preimage_comp]; rw [mem_preimage]; rw [mem_preimage]; rw [hx]

Depends on / 依赖: MeasurableSet, exists_eventuallyEq_const_of_eventually_mem_of_forall_separating, h.ae_mem_or_ae_notMem, hg_eq, hg_eq.mono, mem_preimage, preimage_comp, set_eq
-/
theorem QuasiErgodic.ae_eq_const_of_ae_eq_comp_of_ae_range₀ [Nonempty X] [MeasurableSpace X]
    {s : Set X} [MeasurableSpace.CountablySeparated s] {f : α -> α} {g : α -> X}
    (h : QuasiErgodic f μ) (hs : forallᵐ x ∂μ, g x in s) (hgm : NullMeasurable g μ)
    (hg_eq : g ∘ f =ᵐ[μ] g) :
    exists c, g =ᵐ[μ] const α c := by
  refine exists_eventuallyEq_const_of_eventually_mem_of_forall_separating MeasurableSet hs ?_
  refine fun U hU => h.ae_mem_or_ae_notMem₀ (s := g ⁻¹' U) (hgm hU) ?_b
  refine (hg_eq.mono fun x hx => ?_).set_eq
  rw [← preimage_comp]; rw [mem_preimage]; rw [mem_preimage]; rw [hx]

section CountableSeparatingOnUniv

variable [Nonempty X] [MeasurableSpace X] [MeasurableSpace.CountablySeparated X]
  {f : α -> α} {g : α -> X}

/--
theorem `PreErgodic.ae_eq_const_of_ae_eq_comp` / 定理 `PreErgodic.ae_eq_const_of_ae_eq_comp`

English:
theorem PreErgodic.ae_eq_const_of_ae_eq_comp
  statement: (h : PreErgodic f μ) (hgm : Measurable g)
  proof: exists_eventuallyEq_const_of_forall_separating MeasurableSet fun U hU =>
h.ae_mem_or_ae_notMem (s := g ⁻¹' U) (hgm hU) by rw [← preimage_comp, hg_eq]

中文:
定理 PreErgodic.ae_eq_const_of_ae_eq_comp
  结论: (h : PreErgodic f μ) (hgm : Measurable g)
  证明: exists_eventuallyEq_const_of_forall_separating MeasurableSet fun U hU =>
h.ae_mem_or_ae_notMem (s := g ⁻¹' U) (hgm hU) by rw [← preimage_comp, hg_eq]

Depends on / 依赖: MeasurableSet, ae_mem_or_ae_notMem, exists_eventuallyEq_const_of_forall_separating, h.ae_mem_or_ae_notMem, hg_eq, preimage_comp
-/
theorem PreErgodic.ae_eq_const_of_ae_eq_comp (h : PreErgodic f μ) (hgm : Measurable g)
    (hg_eq : g ∘ f = g) : exists c, g =ᵐ[μ] const α c :=
  exists_eventuallyEq_const_of_forall_separating MeasurableSet fun U hU =>
h.ae_mem_or_ae_notMem (s := g ⁻¹' U) (hgm hU) by rw [← preimage_comp, hg_eq]

/--
theorem `QuasiErgodic.ae_eq_const_of_ae_eq_comp₀` / 定理 `QuasiErgodic.ae_eq_const_of_ae_eq_comp₀`

English:
theorem QuasiErgodic.ae_eq_const_of_ae_eq_comp₀
  statement: (h : QuasiErgodic f μ) (hgm : NullMeasurable g μ)
  proof: h.ae_eq_const_of_ae_eq_comp_of_ae_range₀ (s := univ) univ_mem hgm hg_eq

中文:
定理 QuasiErgodic.ae_eq_const_of_ae_eq_comp₀
  结论: (h : QuasiErgodic f μ) (hgm : NullMeasurable g μ)
  证明: h.ae_eq_const_of_ae_eq_comp_of_ae_range₀ (s := univ) univ_mem hgm hg_eq

Depends on / 依赖: h.ae_eq_const_of_ae_eq_comp_of_ae_range, hg_eq, univ_mem
-/
theorem QuasiErgodic.ae_eq_const_of_ae_eq_comp₀ (h : QuasiErgodic f μ) (hgm : NullMeasurable g μ)
    (hg_eq : g ∘ f =ᵐ[μ] g) : exists c, g =ᵐ[μ] const α c :=
  h.ae_eq_const_of_ae_eq_comp_of_ae_range₀ (s := univ) univ_mem hgm hg_eq

/--
theorem `Ergodic.ae_eq_const_of_ae_eq_comp₀` / 定理 `Ergodic.ae_eq_const_of_ae_eq_comp₀`

English:
theorem Ergodic.ae_eq_const_of_ae_eq_comp₀
  statement: (h : Ergodic f μ) (hgm : NullMeasurable g μ)
  proof: h.quasiErgodic.ae_eq_const_of_ae_eq_comp₀ hgm hg_eq

中文:
定理 Ergodic.ae_eq_const_of_ae_eq_comp₀
  结论: (h : Ergodic f μ) (hgm : NullMeasurable g μ)
  证明: h.quasiErgodic.ae_eq_const_of_ae_eq_comp₀ hgm hg_eq

Depends on / 依赖: h.quasiErgodic.ae_eq_const_of_ae_eq_comp, hg_eq, quasiErgodic
-/
theorem Ergodic.ae_eq_const_of_ae_eq_comp₀ (h : Ergodic f μ) (hgm : NullMeasurable g μ)
    (hg_eq : g ∘ f =ᵐ[μ] g) : exists c, g =ᵐ[μ] const α c :=
  h.quasiErgodic.ae_eq_const_of_ae_eq_comp₀ hgm hg_eq

end CountableSeparatingOnUniv

variable [TopologicalSpace X] [MetrizableSpace X] [Nonempty X] {f : α -> α}

namespace QuasiErgodic

/--
theorem `ae_eq_const_of_ae_eq_comp_ae` / 定理 `ae_eq_const_of_ae_eq_comp_ae`

English:
theorem ae_eq_const_of_ae_eq_comp_ae
  statement: {g : α -> X} (h : QuasiErgodic f μ)
  proof: by
  borelize X
  rcases hgm.isSeparable_ae_range with ⟨t, ht, hgt⟩
  have := ht.secondCountableTopology
  exact h.ae_eq_const_of_ae_eq_comp_of_ae_range₀ hgt hgm.aemeasurable.nullMeasurable hg_eq

中文:
定理 ae_eq_const_of_ae_eq_comp_ae
  结论: {g : α -> X} (h : QuasiErgodic f μ)
  证明: by
  borelize X
  rcases hgm.isSeparable_ae_range with ⟨t, ht, hgt⟩
  have := ht.secondCountableTopology
  exact h.ae_eq_const_of_ae_eq_comp_of_ae_range₀ hgt hgm.aemeasurable.nullMeasurable hg_eq

Depends on / 依赖: aemeasurable, borelize, h.ae_eq_const_of_ae_eq_comp_of_ae_range, hg_eq, hgm.aemeasurable.nullMeasurable, hgm.isSeparable_ae_range, ht.secondCountableTopology, isSeparable_ae_range, nullMeasurable, secondCountableTopology
-/
theorem ae_eq_const_of_ae_eq_comp_ae {g : α -> X} (h : QuasiErgodic f μ)
    (hgm : AEStronglyMeasurable g μ) (hg_eq : g ∘ f =ᵐ[μ] g) : exists c, g =ᵐ[μ] const α c := by
  borelize X
  rcases hgm.isSeparable_ae_range with ⟨t, ht, hgt⟩
  have := ht.secondCountableTopology
  exact h.ae_eq_const_of_ae_eq_comp_of_ae_range₀ hgt hgm.aemeasurable.nullMeasurable hg_eq

/--
theorem `eq_const_of_compQuasiMeasurePreserving_eq` / 定理 `eq_const_of_compQuasiMeasurePreserving_eq`

English:
theorem eq_const_of_compQuasiMeasurePreserving_eq
  statement: (h : QuasiErgodic f μ) {g : α ->ₘ[μ] X}
  proof: have : g ∘ f =ᵐ[μ] g := (g.coeFn_compQuasiMeasurePreserving h.1).symm.trans
    (hg_eq.symm ▸ .refl _ _)
  let ⟨c, hc⟩ := h.ae_eq_const_of_ae_eq_comp_ae g.aestronglyMeasurable this
⟨c, AEEqFun.ext hc.trans (AEEqFun.coeFn_const _ _).symm⟩

中文:
定理 eq_const_of_compQuasiMeasurePreserving_eq
  结论: (h : QuasiErgodic f μ) {g : α ->ₘ[μ] X}
  证明: have : g ∘ f =ᵐ[μ] g := (g.coeFn_compQuasiMeasurePreserving h.1).symm.trans
    (hg_eq.symm ▸ .refl _ _)
  let ⟨c, hc⟩ := h.ae_eq_const_of_ae_eq_comp_ae g.aestronglyMeasurable this
⟨c, AEEqFun.ext hc.trans (AEEqFun.coeFn_const _ _).symm⟩

Depends on / 依赖: AEEqFun, AEEqFun.coeFn_const, AEEqFun.ext, ae_eq_const_of_ae_eq_comp_ae, aestronglyMeasurable, coeFn_compQuasiMeasurePreserving, coeFn_const, g.aestronglyMeasurable, g.coeFn_compQuasiMeasurePreserving, h.ae_eq_const_of_ae_eq_comp_ae, hc.trans, hg_eq, hg_eq.symm, symm.trans
-/
theorem eq_const_of_compQuasiMeasurePreserving_eq (h : QuasiErgodic f μ) {g : α ->ₘ[μ] X}
    (hg_eq : g.compQuasiMeasurePreserving f h.1 = g) : exists c, g = .const α c :=
  have : g ∘ f =ᵐ[μ] g := (g.coeFn_compQuasiMeasurePreserving h.1).symm.trans
    (hg_eq.symm ▸ .refl _ _)
  let ⟨c, hc⟩ := h.ae_eq_const_of_ae_eq_comp_ae g.aestronglyMeasurable this
⟨c, AEEqFun.ext hc.trans (AEEqFun.coeFn_const _ _).symm⟩

end QuasiErgodic

namespace Ergodic

/--
theorem `ae_eq_const_of_ae_eq_comp_ae` / 定理 `ae_eq_const_of_ae_eq_comp_ae`

English:
theorem ae_eq_const_of_ae_eq_comp_ae
  statement: {g : α -> X} (h : Ergodic f μ) (hgm : AEStronglyMeasurable g μ)
  proof: h.quasiErgodic.ae_eq_const_of_ae_eq_comp_ae hgm hg_eq

中文:
定理 ae_eq_const_of_ae_eq_comp_ae
  结论: {g : α -> X} (h : Ergodic f μ) (hgm : AEStronglyMeasurable g μ)
  证明: h.quasiErgodic.ae_eq_const_of_ae_eq_comp_ae hgm hg_eq

Depends on / 依赖: ae_eq_const_of_ae_eq_comp_ae, h.quasiErgodic.ae_eq_const_of_ae_eq_comp_ae, hg_eq, quasiErgodic
-/
theorem ae_eq_const_of_ae_eq_comp_ae {g : α -> X} (h : Ergodic f μ) (hgm : AEStronglyMeasurable g μ)
    (hg_eq : g ∘ f =ᵐ[μ] g) : exists c, g =ᵐ[μ] const α c :=
  h.quasiErgodic.ae_eq_const_of_ae_eq_comp_ae hgm hg_eq

/--
theorem `eq_const_of_compMeasurePreserving_eq` / 定理 `eq_const_of_compMeasurePreserving_eq`

English:
theorem eq_const_of_compMeasurePreserving_eq
  statement: (h : Ergodic f μ) {g : α ->ₘ[μ] X}
  proof: h.quasiErgodic.eq_const_of_compQuasiMeasurePreserving_eq hg_eq

中文:
定理 eq_const_of_compMeasurePreserving_eq
  结论: (h : Ergodic f μ) {g : α ->ₘ[μ] X}
  证明: h.quasiErgodic.eq_const_of_compQuasiMeasurePreserving_eq hg_eq

Depends on / 依赖: eq_const_of_compQuasiMeasurePreserving_eq, h.quasiErgodic.eq_const_of_compQuasiMeasurePreserving_eq, hg_eq, quasiErgodic
-/
theorem eq_const_of_compMeasurePreserving_eq (h : Ergodic f μ) {g : α ->ₘ[μ] X}
    (hg_eq : g.compMeasurePreserving f h.1 = g) : exists c, g = .const α c :=
  h.quasiErgodic.eq_const_of_compQuasiMeasurePreserving_eq hg_eq

end Ergodic
