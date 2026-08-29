/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
module

public import Mathlib.Analysis.Calculus.TangentCone.Prod
public import Mathlib.Geometry.Manifold.MFDeriv.Defs
public import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Geometry.Manifold.Notation

/-!
# Basic properties of the manifold Fréchet derivative

In this file, we show various properties of the manifold Fréchet derivative,
mimicking the API for Fréchet derivatives.
- basic properties of unique differentiability sets
- various general lemmas about the manifold Fréchet derivative
- deducing differentiability from smoothness,
- deriving continuity from differentiability on manifolds,
- congruence lemmas for derivatives on manifolds
- composition lemmas and the chain rule

-/

public section

noncomputable section

assert_not_exists tangentBundleCore

open scoped Topology Manifold
open Function Set Bundle ChartedSpace

section DerivativesProperties

/-! ### Unique differentiability sets in manifolds -/

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''}
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H'' M'']
  {f f₁ : M -> M'} {x : M} {s t : Set M} {g : M' -> M''} {u : Set M'}

/--
theorem `uniqueMDiffWithinAt_univ` / 定理 `uniqueMDiffWithinAt_univ`

English:
theorem uniqueMDiffWithinAt_univ
  statement: UniqueMDiffAt[(univ : Set M)] x
  proof: by
  unfold UniqueMDiffWithinAt
  simp only [preimage_univ, univ_inter]
  exact I.uniqueDiffOn _ (mem_range_self _)

中文:
定理 uniqueMDiffWithinAt_univ
  结论: UniqueMDiffAt[(univ : 集合 M)] x
  证明: by
  unfold UniqueMDiffWithinAt
  simp only [preimage_univ, univ_inter]
  exact I.uniqueDiffOn _ (mem_range_self _)

Depends on / 依赖: I.uniqueDiffOn, UniqueMDiffWithinAt, mem_range_self, preimage_univ, uniqueDiffOn, univ_inter
-/
theorem uniqueMDiffWithinAt_univ : UniqueMDiffAt[(univ : Set M)] x := by
  unfold UniqueMDiffWithinAt
  simp only [preimage_univ, univ_inter]
  exact I.uniqueDiffOn _ (mem_range_self _)

variable {I}

/--
theorem `uniqueMDiffWithinAt_iff_inter_range` / 定理 `uniqueMDiffWithinAt_iff_inter_range`

English:
theorem uniqueMDiffWithinAt_iff_inter_range
  given: {s : Set M} {x : M}
  proof: Iff.rfl

中文:
定理 uniqueMDiffWithinAt_iff_inter_range
  条件: {s : 集合 M} {x : M}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem uniqueMDiffWithinAt_iff_inter_range {s : Set M} {x : M} :
    UniqueMDiffAt[s] x ↔
      UniqueDiffWithinAt 𝕜 ((extChartAt I x).symm ⁻¹' s inter range I)
        ((extChartAt I x) x) := Iff.rfl

/--
theorem `uniqueMDiffWithinAt_iff` / 定理 `uniqueMDiffWithinAt_iff`

English:
theorem uniqueMDiffWithinAt_iff
  given: {s : Set M} {x : M}
  proof: by
  apply uniqueDiffWithinAt_congr
  rw [nhdsWithin_inter]; rw [nhdsWithin_inter]; rw [nhdsWithin_extChartAt_target_eq]

nonrec theorem UniqueMDiffWithinAt.mono_nhds {s t : Set M} {x : M} (hs : UniqueMDiffAt[s] x)
    (ht : 𝓝[s] x <= 𝓝[t] x) : UniqueMDiffAt[t] x :=
hs.mono_nhds by simpa only [← map_extChartAt_nhdsWithin] using Filter.map_mono ht

中文:
定理 uniqueMDiffWithinAt_iff
  条件: {s : 集合 M} {x : M}
  证明: by
  apply uniqueDiffWithinAt_congr
  rw [nhdsWithin_inter]; rw [nhdsWithin_inter]; rw [nhdsWithin_extChartAt_target_eq]

nonrec theorem UniqueMDiffWithinAt.mono_nhds {s t : Set M} {x : M} (hs : UniqueMDiffAt[s] x)
    (ht : 𝓝[s] x <= 𝓝[t] x) : UniqueMDiffAt[t] x :=
hs.mono_nhds by simpa only [← map_extChartAt_nhdsWithin] using Filter.map_mono ht

Depends on / 依赖: nhdsWithin_extChartAt_target_eq, nhdsWithin_inter, uniqueDiffWithinAt_congr
-/
theorem uniqueMDiffWithinAt_iff {s : Set M} {x : M} :
    UniqueMDiffAt[s] x ↔
      UniqueDiffWithinAt 𝕜 ((extChartAt I x).symm ⁻¹' s inter (extChartAt I x).target)
        ((extChartAt I x) x) := by
  apply uniqueDiffWithinAt_congr
  rw [nhdsWithin_inter]; rw [nhdsWithin_inter]; rw [nhdsWithin_extChartAt_target_eq]

nonrec theorem UniqueMDiffWithinAt.mono_nhds {s t : Set M} {x : M} (hs : UniqueMDiffAt[s] x)
    (ht : 𝓝[s] x <= 𝓝[t] x) : UniqueMDiffAt[t] x :=
hs.mono_nhds by simpa only [← map_extChartAt_nhdsWithin] using Filter.map_mono ht

/--
theorem `UniqueMDiffWithinAt.mono_of_mem_nhdsWithin` / 定理 `UniqueMDiffWithinAt.mono_of_mem_nhdsWithin`

English:
theorem UniqueMDiffWithinAt.mono_of_mem_nhdsWithin
  statement: {s t : Set M} {x : M}
  proof: hs.mono_nhds (nhdsWithin_le_iff.2 ht)

中文:
定理 UniqueMDiffWithinAt.mono_of_mem_nhdsWithin
  结论: {s t : 集合 M} {x : M}
  证明: hs.mono_nhds (nhdsWithin_le_iff.2 ht)

Depends on / 依赖: hs.mono_nhds, mono_nhds, nhdsWithin_le_iff
-/
theorem UniqueMDiffWithinAt.mono_of_mem_nhdsWithin {s t : Set M} {x : M}
    (hs : UniqueMDiffAt[s] x) (ht : t in 𝓝[s] x) : UniqueMDiffAt[t] x :=
  hs.mono_nhds (nhdsWithin_le_iff.2 ht)

/--
theorem `UniqueMDiffWithinAt.mono` / 定理 `UniqueMDiffWithinAt.mono`

English:
theorem UniqueMDiffWithinAt.mono
  given: (h : UniqueMDiffAt[s] x) (st : s subseteq t)
  proof: UniqueDiffWithinAt.mono h inter_subset_inter (preimage_mono st) (Subset.refl _)

中文:
定理 UniqueMDiffWithinAt.mono
  条件: (h : UniqueMDiffAt[s] x) (st : s subseteq t)
  证明: UniqueDiffWithinAt.mono h inter_subset_inter (preimage_mono st) (Subset.refl _)

Depends on / 依赖: Subset, Subset.refl, UniqueDiffWithinAt, UniqueDiffWithinAt.mono, inter_subset_inter, preimage_mono
-/
theorem UniqueMDiffWithinAt.mono (h : UniqueMDiffAt[s] x) (st : s subseteq t) :
    UniqueMDiffAt[t] x :=
UniqueDiffWithinAt.mono h inter_subset_inter (preimage_mono st) (Subset.refl _)

/--
theorem `UniqueMDiffWithinAt.inter'` / 定理 `UniqueMDiffWithinAt.inter'`

English:
theorem UniqueMDiffWithinAt.inter'
  given: (hs : UniqueMDiffAt[s] x) (ht : t in 𝓝[s] x)
  proof: hs.mono_of_mem_nhdsWithin (Filter.inter_mem self_mem_nhdsWithin ht)

中文:
定理 UniqueMDiffWithinAt.inter'
  条件: (hs : UniqueMDiffAt[s] x) (ht : t in 𝓝[s] x)
  证明: hs.mono_of_mem_nhdsWithin (Filter.inter_mem self_mem_nhdsWithin ht)

Depends on / 依赖: Filter, Filter.inter_mem, hs.mono_of_mem_nhdsWithin, inter_mem, mono_of_mem_nhdsWithin, self_mem_nhdsWithin
-/
theorem UniqueMDiffWithinAt.inter' (hs : UniqueMDiffAt[s] x) (ht : t in 𝓝[s] x) :
    UniqueMDiffAt[s inter t] x :=
  hs.mono_of_mem_nhdsWithin (Filter.inter_mem self_mem_nhdsWithin ht)

/--
theorem `UniqueMDiffWithinAt.inter` / 定理 `UniqueMDiffWithinAt.inter`

English:
theorem UniqueMDiffWithinAt.inter
  given: (hs : UniqueMDiffAt[s] x) (ht : t in 𝓝 x)
  proof: hs.inter' (nhdsWithin_le_nhds ht)

中文:
定理 UniqueMDiffWithinAt.inter
  条件: (hs : UniqueMDiffAt[s] x) (ht : t in 𝓝 x)
  证明: hs.inter' (nhdsWithin_le_nhds ht)

Depends on / 依赖: hs.inter, nhdsWithin_le_nhds
-/
theorem UniqueMDiffWithinAt.inter (hs : UniqueMDiffAt[s] x) (ht : t in 𝓝 x) :
    UniqueMDiffAt[s inter t] x :=
  hs.inter' (nhdsWithin_le_nhds ht)

/--
theorem `IsOpen.uniqueMDiffWithinAt` / 定理 `IsOpen.uniqueMDiffWithinAt`

English:
theorem IsOpen.uniqueMDiffWithinAt
  given: (hs : IsOpen s) (xs : x in s)
  statement: UniqueMDiffAt[s] x
  proof: (uniqueMDiffWithinAt_univ I).mono_of_mem_nhdsWithin nhdsWithin_le_nhds hs.mem_nhds xs

中文:
定理 是开集.uniqueMDiffWithinAt
  条件: (hs : 是开集 s) (xs : x in s)
  结论: UniqueMDiffAt[s] x
  证明: (uniqueMDiffWithinAt_univ I).mono_of_mem_nhdsWithin nhdsWithin_le_nhds hs.mem_nhds xs

Depends on / 依赖: hs.mem_nhds, mem_nhds, mono_of_mem_nhdsWithin, nhdsWithin_le_nhds, uniqueMDiffWithinAt_univ
-/
theorem IsOpen.uniqueMDiffWithinAt (hs : IsOpen s) (xs : x in s) : UniqueMDiffAt[s] x :=
(uniqueMDiffWithinAt_univ I).mono_of_mem_nhdsWithin nhdsWithin_le_nhds hs.mem_nhds xs

/--
theorem `UniqueMDiffOn.inter` / 定理 `UniqueMDiffOn.inter`

English:
theorem UniqueMDiffOn.inter
  given: (hs : UniqueMDiff[s]) (ht : IsOpen t)
  statement: UniqueMDiff[s inter t]
  proof: fun _x hx => UniqueMDiffWithinAt.inter (hs _ hx.1) (ht.mem_nhds hx.2)

中文:
定理 UniqueMDiffOn.inter
  条件: (hs : UniqueMDiff[s]) (ht : 是开集 t)
  结论: UniqueMDiff[s inter t]
  证明: fun _x hx => UniqueMDiffWithinAt.inter (hs _ hx.1) (ht.mem_nhds hx.2)

Depends on / 依赖: UniqueMDiffWithinAt, UniqueMDiffWithinAt.inter, ht.mem_nhds, mem_nhds
-/
theorem UniqueMDiffOn.inter (hs : UniqueMDiff[s]) (ht : IsOpen t) : UniqueMDiff[s inter t] :=
  fun _x hx => UniqueMDiffWithinAt.inter (hs _ hx.1) (ht.mem_nhds hx.2)

/--
theorem `IsOpen.uniqueMDiffOn` / 定理 `IsOpen.uniqueMDiffOn`

English:
theorem IsOpen.uniqueMDiffOn
  given: (hs : IsOpen s)
  statement: UniqueMDiff[s]
  proof: fun _x hx => hs.uniqueMDiffWithinAt hx

中文:
定理 是开集.uniqueMDiffOn
  条件: (hs : 是开集 s)
  结论: UniqueMDiff[s]
  证明: fun _x hx => hs.uniqueMDiffWithinAt hx

Depends on / 依赖: hs.uniqueMDiffWithinAt, uniqueMDiffWithinAt
-/
theorem IsOpen.uniqueMDiffOn (hs : IsOpen s) : UniqueMDiff[s] :=
  fun _x hx => hs.uniqueMDiffWithinAt hx

/--
theorem `uniqueMDiffOn_univ` / 定理 `uniqueMDiffOn_univ`

English:
theorem uniqueMDiffOn_univ
  statement: UniqueMDiff[(univ : Set M)]
  proof: isOpen_univ.uniqueMDiffOn

nonrec theorem UniqueMDiffWithinAt.prod {x : M} {y : M'} {s : Set M} {t : Set M'}
    (hs : UniqueMDiffAt[s] x) (ht : UniqueMDiffAt[t] y) : UniqueMDiffAt[s ×ˢ t] (x, y) := by
  refine (hs.prod ht).mono ?_
  rw [ModelWithCorners.range_prod]; rw [← prod_inter_prod]
  rfl

中文:
定理 uniqueMDiffOn_univ
  结论: UniqueMDiff[(univ : 集合 M)]
  证明: isOpen_univ.uniqueMDiffOn

nonrec theorem UniqueMDiffWithinAt.prod {x : M} {y : M'} {s : Set M} {t : Set M'}
    (hs : UniqueMDiffAt[s] x) (ht : UniqueMDiffAt[t] y) : UniqueMDiffAt[s ×ˢ t] (x, y) := by
  refine (hs.prod ht).mono ?_
  rw [ModelWithCorners.range_prod]; rw [← prod_inter_prod]
  rfl

Depends on / 依赖: isOpen_univ, isOpen_univ.uniqueMDiffOn, uniqueMDiffOn
-/
theorem uniqueMDiffOn_univ : UniqueMDiff[(univ : Set M)] :=
  isOpen_univ.uniqueMDiffOn

nonrec theorem UniqueMDiffWithinAt.prod {x : M} {y : M'} {s : Set M} {t : Set M'}
    (hs : UniqueMDiffAt[s] x) (ht : UniqueMDiffAt[t] y) : UniqueMDiffAt[s ×ˢ t] (x, y) := by
  refine (hs.prod ht).mono ?_
  rw [ModelWithCorners.range_prod]; rw [← prod_inter_prod]
  rfl

/--
theorem `UniqueMDiffOn.prod` / 定理 `UniqueMDiffOn.prod`

English:
theorem UniqueMDiffOn.prod
  statement: {s : Set M} {t : Set M'} (hs : UniqueMDiff[s])
  proof: fun x h =>
  (hs x.1 h.1).prod (ht x.2 h.2)

中文:
定理 UniqueMDiffOn.乘积
  结论: {s : 集合 M} {t : 集合 M'} (hs : UniqueMDiff[s])
  证明: fun x h =>
  (hs x.1 h.1).prod (ht x.2 h.2)
-/
theorem UniqueMDiffOn.prod {s : Set M} {t : Set M'} (hs : UniqueMDiff[s])
    (ht : UniqueMDiff[t]) : UniqueMDiff[s ×ˢ t] := fun x h =>
  (hs x.1 h.1).prod (ht x.2 h.2)

/--
theorem `MDifferentiableWithinAt.mono` / 定理 `MDifferentiableWithinAt.mono`

English:
theorem MDifferentiableWithinAt.mono
  given: (hst : s subseteq t) (h : MDiffAt[t] f x)
  statement: MDiffAt[s] f x
  proof: ⟨ContinuousWithinAt.mono h.1 hst, DifferentiableWithinAt.mono
    h.differentiableWithinAt_writtenInExtChartAt
    (inter_subset_inter_left _ (preimage_mono hst))⟩

中文:
定理 MDifferentiableWithinAt.mono
  条件: (hst : s subseteq t) (h : MDiffAt[t] f x)
  结论: MDiffAt[s] f x
  证明: ⟨ContinuousWithinAt.mono h.1 hst, DifferentiableWithinAt.mono
    h.differentiableWithinAt_writtenInExtChartAt
    (inter_subset_inter_left _ (preimage_mono hst))⟩

Depends on / 依赖: ContinuousWithinAt, ContinuousWithinAt.mono, DifferentiableWithinAt, DifferentiableWithinAt.mono, differentiableWithinAt_writtenInExtChartAt, h.differentiableWithinAt_writtenInExtChartAt, inter_subset_inter_left, preimage_mono
-/
theorem MDifferentiableWithinAt.mono (hst : s subseteq t) (h : MDiffAt[t] f x) : MDiffAt[s] f x :=
  ⟨ContinuousWithinAt.mono h.1 hst, DifferentiableWithinAt.mono
    h.differentiableWithinAt_writtenInExtChartAt
    (inter_subset_inter_left _ (preimage_mono hst))⟩

/--
theorem `mdifferentiableWithinAt_univ` / 定理 `mdifferentiableWithinAt_univ`

English:
theorem mdifferentiableWithinAt_univ
  statement: MDiffAt[univ] f x ↔ MDiffAt f x
  proof: by
  simp_rw [MDifferentiableWithinAt, MDifferentiableAt, ChartedSpace.LiftPropAt]

中文:
定理 mdifferentiableWithinAt_univ
  结论: MDiffAt[univ] f x ↔ MDiffAt f x
  证明: by
  simp_rw [MDifferentiableWithinAt, MDifferentiableAt, ChartedSpace.LiftPropAt]

Depends on / 依赖: ChartedSpace, ChartedSpace.LiftPropAt, LiftPropAt, MDifferentiableAt, MDifferentiableWithinAt, simp_rw
-/
theorem mdifferentiableWithinAt_univ : MDiffAt[univ] f x ↔ MDiffAt f x := by
  simp_rw [MDifferentiableWithinAt, MDifferentiableAt, ChartedSpace.LiftPropAt]

/--
theorem `mdifferentiableWithinAt_inter` / 定理 `mdifferentiableWithinAt_inter`

English:
theorem mdifferentiableWithinAt_inter
  given: (ht : t in 𝓝 x)
  statement: MDiffAt[s inter t] f x ↔ MDiffAt[s] f x
  proof: by
  rw [MDifferentiableWithinAt]; rw [MDifferentiableWithinAt]; rw [differentiableWithinAt_localInvariantProp.liftPropWithinAt_inter ht]

中文:
定理 mdifferentiableWithinAt_inter
  条件: (ht : t in 𝓝 x)
  结论: MDiffAt[s inter t] f x ↔ MDiffAt[s] f x
  证明: by
  rw [MDifferentiableWithinAt]; rw [MDifferentiableWithinAt]; rw [differentiableWithinAt_localInvariantProp.liftPropWithinAt_inter ht]

Depends on / 依赖: MDifferentiableWithinAt, differentiableWithinAt_localInvariantProp, differentiableWithinAt_localInvariantProp.liftPropWithinAt_inter, liftPropWithinAt_inter
-/
theorem mdifferentiableWithinAt_inter (ht : t in 𝓝 x) : MDiffAt[s inter t] f x ↔ MDiffAt[s] f x := by
  rw [MDifferentiableWithinAt]; rw [MDifferentiableWithinAt]; rw [differentiableWithinAt_localInvariantProp.liftPropWithinAt_inter ht]

/--
theorem `mdifferentiableWithinAt_inter'` / 定理 `mdifferentiableWithinAt_inter'`

English:
theorem mdifferentiableWithinAt_inter'
  given: (ht : t in 𝓝[s] x)
  statement: MDiffAt[s inter t] f x ↔ MDiffAt[s] f x
  proof: by
  rw [MDifferentiableWithinAt]; rw [MDifferentiableWithinAt]; rw [differentiableWithinAt_localInvariantProp.liftPropWithinAt_inter' ht]

中文:
定理 mdifferentiableWithinAt_inter'
  条件: (ht : t in 𝓝[s] x)
  结论: MDiffAt[s inter t] f x ↔ MDiffAt[s] f x
  证明: by
  rw [MDifferentiableWithinAt]; rw [MDifferentiableWithinAt]; rw [differentiableWithinAt_localInvariantProp.liftPropWithinAt_inter' ht]

Depends on / 依赖: MDifferentiableWithinAt, differentiableWithinAt_localInvariantProp, differentiableWithinAt_localInvariantProp.liftPropWithinAt_inter, liftPropWithinAt_inter
-/
theorem mdifferentiableWithinAt_inter' (ht : t in 𝓝[s] x) : MDiffAt[s inter t] f x ↔ MDiffAt[s] f x := by
  rw [MDifferentiableWithinAt]; rw [MDifferentiableWithinAt]; rw [differentiableWithinAt_localInvariantProp.liftPropWithinAt_inter' ht]

/--
theorem `MDifferentiableAt.mdifferentiableWithinAt` / 定理 `MDifferentiableAt.mdifferentiableWithinAt`

English:
theorem MDifferentiableAt.mdifferentiableWithinAt
  given: (h : MDiffAt f x)
  statement: MDiffAt[s] f x
  proof: MDifferentiableWithinAt.mono (subset_univ _) (mdifferentiableWithinAt_univ.2 h)

中文:
定理 MDifferentiableAt.mdifferentiableWithinAt
  条件: (h : MDiffAt f x)
  结论: MDiffAt[s] f x
  证明: MDifferentiableWithinAt.mono (subset_univ _) (mdifferentiableWithinAt_univ.2 h)

Depends on / 依赖: MDifferentiableWithinAt, MDifferentiableWithinAt.mono, mdifferentiableWithinAt_univ, subset_univ
-/
theorem MDifferentiableAt.mdifferentiableWithinAt (h : MDiffAt f x) : MDiffAt[s] f x :=
  MDifferentiableWithinAt.mono (subset_univ _) (mdifferentiableWithinAt_univ.2 h)

/--
theorem `MDifferentiableWithinAt.mdifferentiableAt` / 定理 `MDifferentiableWithinAt.mdifferentiableAt`

English:
theorem MDifferentiableWithinAt.mdifferentiableAt
  given: (h : MDiffAt[s] f x) (hs : s in 𝓝 x)
  proof: by
  have : s = univ inter s := by rw [univ_inter]
  rwa [this, mdifferentiableWithinAt_inter hs, mdifferentiableWithinAt_univ] at h

中文:
定理 MDifferentiableWithinAt.mdifferentiableAt
  条件: (h : MDiffAt[s] f x) (hs : s in 𝓝 x)
  证明: by
  have : s = univ inter s := by rw [univ_inter]
  rwa [this, mdifferentiableWithinAt_inter hs, mdifferentiableWithinAt_univ] at h

Depends on / 依赖: mdifferentiableWithinAt_inter, mdifferentiableWithinAt_univ, univ_inter
-/
theorem MDifferentiableWithinAt.mdifferentiableAt (h : MDiffAt[s] f x) (hs : s in 𝓝 x) :
    MDiffAt f x := by
  have : s = univ inter s := by rw [univ_inter]
  rwa [this, mdifferentiableWithinAt_inter hs, mdifferentiableWithinAt_univ] at h

/--
theorem `MDifferentiableOn.mono` / 定理 `MDifferentiableOn.mono`

English:
theorem MDifferentiableOn.mono
  given: (h : MDiff[t] f) (st : s subseteq t)
  statement: MDiff[s] f
  proof: fun x hx => (h x (st hx)).mono st

@[simp]

中文:
定理 MDifferentiableOn.mono
  条件: (h : MDiff[t] f) (st : s subseteq t)
  结论: MDiff[s] f
  证明: fun x hx => (h x (st hx)).mono st

@[simp]
-/
theorem MDifferentiableOn.mono (h : MDiff[t] f) (st : s subseteq t) : MDiff[s] f :=
  fun x hx => (h x (st hx)).mono st

@[simp]
/--
theorem `mdifferentiableOn_empty` / 定理 `mdifferentiableOn_empty`

English:
theorem mdifferentiableOn_empty
  statement: MDiff[∅] f
  proof: fun _x hx => hx.elim

中文:
定理 mdifferentiableOn_empty
  结论: MDiff[∅] f
  证明: fun _x hx => hx.elim

Depends on / 依赖: hx.elim
-/
theorem mdifferentiableOn_empty : MDiff[∅] f := fun _x hx => hx.elim

/--
theorem `mdifferentiableOn_univ` / 定理 `mdifferentiableOn_univ`

English:
theorem mdifferentiableOn_univ
  statement: MDiff[univ] f ↔ MDiff f
  proof: by
  simp only [MDifferentiableOn, mdifferentiableWithinAt_univ, mfld_simps]; rfl

中文:
定理 mdifferentiableOn_univ
  结论: MDiff[univ] f ↔ MDiff f
  证明: by
  simp only [MDifferentiableOn, mdifferentiableWithinAt_univ, mfld_simps]; rfl

Depends on / 依赖: MDifferentiableOn, mdifferentiableWithinAt_univ, mfld_simps
-/
theorem mdifferentiableOn_univ : MDiff[univ] f ↔ MDiff f := by
  simp only [MDifferentiableOn, mdifferentiableWithinAt_univ, mfld_simps]; rfl

/--
theorem `MDifferentiableOn.mdifferentiableAt` / 定理 `MDifferentiableOn.mdifferentiableAt`

English:
theorem MDifferentiableOn.mdifferentiableAt
  given: (h : MDiff[s] f) (hx : s in 𝓝 x)
  statement: MDiffAt f x
  proof: (h x (mem_of_mem_nhds hx)).mdifferentiableAt hx

中文:
定理 MDifferentiableOn.mdifferentiableAt
  条件: (h : MDiff[s] f) (hx : s in 𝓝 x)
  结论: MDiffAt f x
  证明: (h x (mem_of_mem_nhds hx)).mdifferentiableAt hx

Depends on / 依赖: mdifferentiableAt, mem_of_mem_nhds
-/
theorem MDifferentiableOn.mdifferentiableAt (h : MDiff[s] f) (hx : s in 𝓝 x) : MDiffAt f x :=
  (h x (mem_of_mem_nhds hx)).mdifferentiableAt hx

/--
theorem `MDifferentiable.mdifferentiableOn` / 定理 `MDifferentiable.mdifferentiableOn`

English:
theorem MDifferentiable.mdifferentiableOn
  given: (h : MDiff f)
  statement: MDiff[s] f
  proof: (mdifferentiableOn_univ.2 h).mono (subset_univ _)

中文:
定理 MDifferentiable.mdifferentiableOn
  条件: (h : MDiff f)
  结论: MDiff[s] f
  证明: (mdifferentiableOn_univ.2 h).mono (subset_univ _)

Depends on / 依赖: mdifferentiableOn_univ, subset_univ
-/
theorem MDifferentiable.mdifferentiableOn (h : MDiff f) : MDiff[s] f :=
  (mdifferentiableOn_univ.2 h).mono (subset_univ _)

/--
theorem `mdifferentiableOn_of_locally_mdifferentiableOn` / 定理 `mdifferentiableOn_of_locally_mdifferentiableOn`

English:
theorem mdifferentiableOn_of_locally_mdifferentiableOn
  proof: by
  intro x xs
  rcases h x xs with ⟨t, t_open, xt, ht⟩
  exact (mdifferentiableWithinAt_inter (t_open.mem_nhds xt)).1 (ht x ⟨xs, xt⟩)

中文:
定理 mdifferentiableOn_of_locally_mdifferentiableOn
  证明: by
  intro x xs
  rcases h x xs with ⟨t, t_open, xt, ht⟩
  exact (mdifferentiableWithinAt_inter (t_open.mem_nhds xt)).1 (ht x ⟨xs, xt⟩)

Depends on / 依赖: mdifferentiableWithinAt_inter, mem_nhds, t_open, t_open.mem_nhds
-/
theorem mdifferentiableOn_of_locally_mdifferentiableOn
    (h : forall x in s, exists u, IsOpen u ∧ x in u ∧ MDiff[s inter u] f) : MDiff[s] f := by
  intro x xs
  rcases h x xs with ⟨t, t_open, xt, ht⟩
  exact (mdifferentiableWithinAt_inter (t_open.mem_nhds xt)).1 (ht x ⟨xs, xt⟩)

/--
theorem `MDifferentiable.mdifferentiableAt` / 定理 `MDifferentiable.mdifferentiableAt`

English:
theorem MDifferentiable.mdifferentiableAt
  given: (hf : MDiff f)
  statement: MDiffAt f x
  proof: hf x

中文:
定理 MDifferentiable.mdifferentiableAt
  条件: (hf : MDiff f)
  结论: MDiffAt f x
  证明: hf x
-/
theorem MDifferentiable.mdifferentiableAt (hf : MDiff f) : MDiffAt f x :=
  hf x


/--
theorem `mdifferentiableWithinAt_iff_target_inter` / 定理 `mdifferentiableWithinAt_iff_target_inter`

English:
theorem mdifferentiableWithinAt_iff_target_inter
  given: {f : M -> M'} {s : Set M} {x : M}
  proof: by
  rw [mdifferentiableWithinAt_iff']
  refine and_congr Iff.rfl (exists_congr fun f' => ?_)
  rw [inter_comm]
  simp only [HasFDerivWithinAt, nhdsWithin_inter, nhdsWithin_extChartAt_target_eq]

中文:
定理 mdifferentiableWithinAt_iff_target_inter
  条件: {f : M -> M'} {s : 集合 M} {x : M}
  证明: by
  rw [mdifferentiableWithinAt_iff']
  refine and_congr Iff.rfl (exists_congr fun f' => ?_)
  rw [inter_comm]
  simp only [HasFDerivWithinAt, nhdsWithin_inter, nhdsWithin_extChartAt_target_eq]

Depends on / 依赖: HasFDerivWithinAt, Iff.rfl, and_congr, exists_congr, inter_comm, mdifferentiableWithinAt_iff, nhdsWithin_extChartAt_target_eq, nhdsWithin_inter
-/
theorem mdifferentiableWithinAt_iff_target_inter {f : M -> M'} {s : Set M} {x : M} :
    MDiffAt[s] f x ↔
      ContinuousWithinAt f s x ∧
        DifferentiableWithinAt 𝕜 (writtenInExtChartAt I I' x f)
          ((extChartAt I x).target inter (extChartAt I x).symm ⁻¹' s) ((extChartAt I x) x) := by
  rw [mdifferentiableWithinAt_iff']
  refine and_congr Iff.rfl (exists_congr fun f' => ?_)
  rw [inter_comm]
  simp only [HasFDerivWithinAt, nhdsWithin_inter, nhdsWithin_extChartAt_target_eq]

/--
theorem `mdifferentiableWithinAt_iff` / 定理 `mdifferentiableWithinAt_iff`

English:
theorem mdifferentiableWithinAt_iff
  proof: by
  simp_rw [MDifferentiableWithinAt, ChartedSpace.liftPropWithinAt_iff']; rfl

中文:
定理 mdifferentiableWithinAt_iff
  证明: by
  simp_rw [MDifferentiableWithinAt, ChartedSpace.liftPropWithinAt_iff']; rfl

Depends on / 依赖: ChartedSpace, ChartedSpace.liftPropWithinAt_iff, MDifferentiableWithinAt, liftPropWithinAt_iff, simp_rw
-/
theorem mdifferentiableWithinAt_iff :
    MDiffAt[s] f x ↔
      ContinuousWithinAt f s x ∧
        DifferentiableWithinAt 𝕜 (extChartAt I' (f x) ∘ f ∘ (extChartAt I x).symm)
          ((extChartAt I x).symm ⁻¹' s inter range I) (extChartAt I x x) := by
  simp_rw [MDifferentiableWithinAt, ChartedSpace.liftPropWithinAt_iff']; rfl

/--
theorem `mdifferentiableWithinAt_iff_target_inter'` / 定理 `mdifferentiableWithinAt_iff_target_inter'`

English:
theorem mdifferentiableWithinAt_iff_target_inter'
  proof: by
  simp only [MDifferentiableWithinAt, liftPropWithinAt_iff']
exact and_congr_right fun hc => differentiableWithinAt_congr_nhds
    hc.nhdsWithin_extChartAt_symm_preimage_inter_range

中文:
定理 mdifferentiableWithinAt_iff_target_inter'
  证明: by
  simp only [MDifferentiableWithinAt, liftPropWithinAt_iff']
exact and_congr_right fun hc => differentiableWithinAt_congr_nhds
    hc.nhdsWithin_extChartAt_symm_preimage_inter_range

Depends on / 依赖: MDifferentiableWithinAt, and_congr_right, differentiableWithinAt_congr_nhds, hc.nhdsWithin_extChartAt_symm_preimage_inter_range, liftPropWithinAt_iff, nhdsWithin_extChartAt_symm_preimage_inter_range
-/
theorem mdifferentiableWithinAt_iff_target_inter' :
    MDiffAt[s] f x ↔
      ContinuousWithinAt f s x ∧
        DifferentiableWithinAt 𝕜 (extChartAt I' (f x) ∘ f ∘ (extChartAt I x).symm)
          ((extChartAt I x).target inter
            (extChartAt I x).symm ⁻¹' (s inter f ⁻¹' (extChartAt I' (f x)).source))
          (extChartAt I x x) := by
  simp only [MDifferentiableWithinAt, liftPropWithinAt_iff']
exact and_congr_right fun hc => differentiableWithinAt_congr_nhds
    hc.nhdsWithin_extChartAt_symm_preimage_inter_range

/--
theorem `mdifferentiableWithinAt_iff_target` / 定理 `mdifferentiableWithinAt_iff_target`

English:
theorem mdifferentiableWithinAt_iff_target
  proof: by
  simp_rw [MDifferentiableWithinAt, liftPropWithinAt_iff', ← and_assoc]
  have cont :
    ContinuousWithinAt f s x ∧ ContinuousWithinAt (extChartAt I' (f x) ∘ f) s x ↔
        ContinuousWithinAt f s x :=
and_iff_left_of_imp (continuousAt_extChartAt _).comp_continuousWithinAt
  simp_rw [cont, DifferentiableWithinAtProp, extChartAt, OpenPartialHomeomorph.extend,
    PartialEquiv.coe_trans, ModelWithCorners.toPartialEquiv_coe,
    OpenPartialHomeomorph.coe_toPartialEquiv, modelWithCornersSelf_coe, chartAt_self_eq,
    OpenPartialHomeomorph.refl_apply]
  rfl

中文:
定理 mdifferentiableWithinAt_iff_target
  证明: by
  simp_rw [MDifferentiableWithinAt, liftPropWithinAt_iff', ← and_assoc]
  have cont :
    ContinuousWithinAt f s x ∧ ContinuousWithinAt (extChartAt I' (f x) ∘ f) s x ↔
        ContinuousWithinAt f s x :=
and_iff_left_of_imp (continuousAt_extChartAt _).comp_continuousWithinAt
  simp_rw [cont, DifferentiableWithinAtProp, extChartAt, OpenPartialHomeomorph.extend,
    PartialEquiv.coe_trans, ModelWithCorners.toPartialEquiv_coe,
    OpenPartialHomeomorph.coe_toPartialEquiv, modelWithCornersSelf_coe, chartAt_self_eq,
    OpenPartialHomeomorph.refl_apply]
  rfl

Depends on / 依赖: ContinuousWithinAt, DifferentiableWithinAtProp, MDifferentiableWithinAt, ModelWithCorners, ModelWithCorners.toPartialEquiv_coe, OpenPa, OpenPartialHomeomorph, OpenPartialHomeomorph.coe_toPartialEquiv, OpenPartialHomeomorph.extend, PartialEquiv, PartialEquiv.coe_trans, and_assoc, and_iff_left_of_imp, chartAt_self_eq, coe_toPartialEquiv, coe_trans, comp_continuousWithinAt, continuousAt_extChartAt, extChartAt, extend
-/
theorem mdifferentiableWithinAt_iff_target :
    MDiffAt[s] f x ↔ ContinuousWithinAt f s x ∧ MDiffAt[s] (extChartAt I' (f x) ∘ f) x := by
  simp_rw [MDifferentiableWithinAt, liftPropWithinAt_iff', ← and_assoc]
  have cont :
    ContinuousWithinAt f s x ∧ ContinuousWithinAt (extChartAt I' (f x) ∘ f) s x ↔
        ContinuousWithinAt f s x :=
and_iff_left_of_imp (continuousAt_extChartAt _).comp_continuousWithinAt
  simp_rw [cont, DifferentiableWithinAtProp, extChartAt, OpenPartialHomeomorph.extend,
    PartialEquiv.coe_trans, ModelWithCorners.toPartialEquiv_coe,
    OpenPartialHomeomorph.coe_toPartialEquiv, modelWithCornersSelf_coe, chartAt_self_eq,
    OpenPartialHomeomorph.refl_apply]
  rfl

/--
theorem `mdifferentiableAt_iff_target` / 定理 `mdifferentiableAt_iff_target`

English:
theorem mdifferentiableAt_iff_target
  given: {x : M}
  proof: by
  rw [← mdifferentiableWithinAt_univ]; rw [← mdifferentiableWithinAt_univ]; rw [mdifferentiableWithinAt_iff_target]; rw [continuousWithinAt_univ]

中文:
定理 mdifferentiableAt_iff_target
  条件: {x : M}
  证明: by
  rw [← mdifferentiableWithinAt_univ]; rw [← mdifferentiableWithinAt_univ]; rw [mdifferentiableWithinAt_iff_target]; rw [continuousWithinAt_univ]

Depends on / 依赖: continuousWithinAt_univ, mdifferentiableWithinAt_iff_target, mdifferentiableWithinAt_univ
-/
theorem mdifferentiableAt_iff_target {x : M} :
    MDiffAt f x ↔ ContinuousAt f x ∧ MDiffAt (extChartAt I' (f x) ∘ f) x := by
  rw [← mdifferentiableWithinAt_univ]; rw [← mdifferentiableWithinAt_univ]; rw [mdifferentiableWithinAt_iff_target]; rw [continuousWithinAt_univ]

section IsManifold

variable {e : OpenPartialHomeomorph M H} {e' : OpenPartialHomeomorph M' H'}

open IsManifold

/--
theorem `mdifferentiableWithinAt_iff_source_of_mem_maximalAtlas` / 定理 `mdifferentiableWithinAt_iff_source_of_mem_maximalAtlas`

English:
theorem mdifferentiableWithinAt_iff_source_of_mem_maximalAtlas
  statement: (he : e in maximalAtlas I 1 M)
  proof: by
  have h2x := hx; rw [← e.extend_source (I := I)] at h2x
  simp_rw [MDifferentiableWithinAt,
    differentiableWithinAt_localInvariantProp.liftPropWithinAt_indep_chart_source he hx,
    StructureGroupoid.liftPropWithinAt_self_source,
    e.extend_symm_continuousWithinAt_comp_right_iff, differentiableWithinAtProp_self_source,
    DifferentiableWithinAtProp, Function.comp, e.left_inv hx, (e.extend I).left_inv h2x]
  rfl

中文:
定理 mdifferentiableWithinAt_iff_source_of_mem_maximalAtlas
  结论: (he : e in maximalAtlas I 1 M)
  证明: by
  have h2x := hx; rw [← e.extend_source (I := I)] at h2x
  simp_rw [MDifferentiableWithinAt,
    differentiableWithinAt_localInvariantProp.liftPropWithinAt_indep_chart_source he hx,
    StructureGroupoid.liftPropWithinAt_self_source,
    e.extend_symm_continuousWithinAt_comp_right_iff, differentiableWithinAtProp_self_source,
    DifferentiableWithinAtProp, Function.comp, e.left_inv hx, (e.extend I).left_inv h2x]
  rfl

Depends on / 依赖: DifferentiableWithinAtProp, Function, Function.comp, MDifferentiableWithinAt, StructureGroupoid, StructureGroupoid.liftPropWithinAt_self_source, differentiableWithinAtProp_self_source, differentiableWithinAt_localInvariantProp, differentiableWithinAt_localInvariantProp.liftPropWithinAt_indep_chart_source, e.extend, e.extend_source, e.extend_symm_continuousWithinAt_comp_right_iff, e.left_inv, extend, extend_source, extend_symm_continuousWithinAt_comp_right_iff, left_inv, liftPropWithinAt_indep_chart_source, liftPropWithinAt_self_source, simp_rw
-/
theorem mdifferentiableWithinAt_iff_source_of_mem_maximalAtlas (he : e in maximalAtlas I 1 M)
    (hx : x in e.source) :
    MDiffAt[s] f x ↔
      MDiffAt[(e.extend I).symm ⁻¹' s inter range I] (f ∘ (e.extend I).symm) (e.extend I x) := by
  have h2x := hx; rw [← e.extend_source (I := I)] at h2x
  simp_rw [MDifferentiableWithinAt,
    differentiableWithinAt_localInvariantProp.liftPropWithinAt_indep_chart_source he hx,
    StructureGroupoid.liftPropWithinAt_self_source,
    e.extend_symm_continuousWithinAt_comp_right_iff, differentiableWithinAtProp_self_source,
    DifferentiableWithinAtProp, Function.comp, e.left_inv hx, (e.extend I).left_inv h2x]
  rfl

/--
theorem `mdifferentiableWithinAt_iff_source_of_mem_source` / 定理 `mdifferentiableWithinAt_iff_source_of_mem_source`

English:
theorem mdifferentiableWithinAt_iff_source_of_mem_source
  proof: mdifferentiableWithinAt_iff_source_of_mem_maximalAtlas (chart_mem_maximalAtlas x) hx'

中文:
定理 mdifferentiableWithinAt_iff_source_of_mem_source
  证明: mdifferentiableWithinAt_iff_source_of_mem_maximalAtlas (chart_mem_maximalAtlas x) hx'

Depends on / 依赖: chart_mem_maximalAtlas, mdifferentiableWithinAt_iff_source_of_mem_maximalAtlas
-/
theorem mdifferentiableWithinAt_iff_source_of_mem_source
    [IsManifold I 1 M] {x' : M} (hx' : x' in (chartAt H x).source) :
    MDiffAt[s] f x' ↔
      MDiffAt[(extChartAt I x).symm ⁻¹' s inter range I] (f ∘ (extChartAt I x).symm)
        (extChartAt I x x') :=
  mdifferentiableWithinAt_iff_source_of_mem_maximalAtlas (chart_mem_maximalAtlas x) hx'

/--
theorem `mdifferentiableAt_iff_source_of_mem_source` / 定理 `mdifferentiableAt_iff_source_of_mem_source`

English:
theorem mdifferentiableAt_iff_source_of_mem_source
  proof: by
  simp_rw [← mdifferentiableWithinAt_univ, mdifferentiableWithinAt_iff_source_of_mem_source hx',
    preimage_univ, univ_inter]

中文:
定理 mdifferentiableAt_iff_source_of_mem_source
  证明: by
  simp_rw [← mdifferentiableWithinAt_univ, mdifferentiableWithinAt_iff_source_of_mem_source hx',
    preimage_univ, univ_inter]

Depends on / 依赖: mdifferentiableWithinAt_iff_source_of_mem_source, mdifferentiableWithinAt_univ, preimage_univ, simp_rw, univ_inter
-/
theorem mdifferentiableAt_iff_source_of_mem_source
    [IsManifold I 1 M] {x' : M} (hx' : x' in (chartAt H x).source) :
    MDiffAt f x' ↔ MDiffAt[range I] (f ∘ (extChartAt I x).symm) (extChartAt I x x') := by
  simp_rw [← mdifferentiableWithinAt_univ, mdifferentiableWithinAt_iff_source_of_mem_source hx',
    preimage_univ, univ_inter]

/--
theorem `mdifferentiableWithinAt_iff_target_of_mem_source` / 定理 `mdifferentiableWithinAt_iff_target_of_mem_source`

English:
theorem mdifferentiableWithinAt_iff_target_of_mem_source
  proof: by
  simp_rw [MDifferentiableWithinAt]
  rw [differentiableWithinAt_localInvariantProp.liftPropWithinAt_indep_chart_target
      (chart_mem_maximalAtlas y) hy]; rw [and_congr_right]
  intro hf
  simp_rw [StructureGroupoid.liftPropWithinAt_self_target]
  simp_rw [((chartAt H' y).continuousAt hy).comp_continuousWithinAt hf]
  rw [← extChartAt_source I'] at hy
  simp_rw [(continuousAt_extChartAt' hy).comp_continuousWithinAt hf]
  rfl

中文:
定理 mdifferentiableWithinAt_iff_target_of_mem_source
  证明: by
  simp_rw [MDifferentiableWithinAt]
  rw [differentiableWithinAt_localInvariantProp.liftPropWithinAt_indep_chart_target
      (chart_mem_maximalAtlas y) hy]; rw [and_congr_right]
  intro hf
  simp_rw [StructureGroupoid.liftPropWithinAt_self_target]
  simp_rw [((chartAt H' y).continuousAt hy).comp_continuousWithinAt hf]
  rw [← extChartAt_source I'] at hy
  simp_rw [(continuousAt_extChartAt' hy).comp_continuousWithinAt hf]
  rfl

Depends on / 依赖: MDifferentiableWithinAt, StructureGroupoid, StructureGroupoid.liftPropWithinAt_self_target, and_congr_right, chartAt, chart_mem_maximalAtlas, comp_continuousWithinAt, continuousAt, continuousAt_extChartAt, differentiableWithinAt_localInvariantProp, differentiableWithinAt_localInvariantProp.liftPropWithinAt_indep_chart_target, extChartAt_source, liftPropWithinAt_indep_chart_target, liftPropWithinAt_self_target, simp_rw
-/
theorem mdifferentiableWithinAt_iff_target_of_mem_source
    [IsManifold I' 1 M'] {x : M} {y : M'} (hy : f x in (chartAt H' y).source) :
    MDiffAt[s] f x ↔ ContinuousWithinAt f s x ∧ MDiffAt[s] (extChartAt I' y ∘ f) x := by
  simp_rw [MDifferentiableWithinAt]
  rw [differentiableWithinAt_localInvariantProp.liftPropWithinAt_indep_chart_target
      (chart_mem_maximalAtlas y) hy]; rw [and_congr_right]
  intro hf
  simp_rw [StructureGroupoid.liftPropWithinAt_self_target]
  simp_rw [((chartAt H' y).continuousAt hy).comp_continuousWithinAt hf]
  rw [← extChartAt_source I'] at hy
  simp_rw [(continuousAt_extChartAt' hy).comp_continuousWithinAt hf]
  rfl

/--
theorem `mdifferentiableAt_iff_target_of_mem_source` / 定理 `mdifferentiableAt_iff_target_of_mem_source`

English:
theorem mdifferentiableAt_iff_target_of_mem_source
  proof: by
  rw [← mdifferentiableWithinAt_univ]; rw [mdifferentiableWithinAt_iff_target_of_mem_source hy]; rw [continuousWithinAt_univ]; rw [← mdifferentiableWithinAt_univ]

中文:
定理 mdifferentiableAt_iff_target_of_mem_source
  证明: by
  rw [← mdifferentiableWithinAt_univ]; rw [mdifferentiableWithinAt_iff_target_of_mem_source hy]; rw [continuousWithinAt_univ]; rw [← mdifferentiableWithinAt_univ]

Depends on / 依赖: continuousWithinAt_univ, mdifferentiableWithinAt_iff_target_of_mem_source, mdifferentiableWithinAt_univ
-/
theorem mdifferentiableAt_iff_target_of_mem_source
    [IsManifold I' 1 M'] {x : M} {y : M'} (hy : f x in (chartAt H' y).source) :
    MDiffAt f x ↔ ContinuousAt f x ∧ MDiffAt (extChartAt I' y ∘ f) x := by
  rw [← mdifferentiableWithinAt_univ]; rw [mdifferentiableWithinAt_iff_target_of_mem_source hy]; rw [continuousWithinAt_univ]; rw [← mdifferentiableWithinAt_univ]

/--
theorem `mdifferentiableWithinAt_iff_of_mem_maximalAtlas` / 定理 `mdifferentiableWithinAt_iff_of_mem_maximalAtlas`

English:
theorem mdifferentiableWithinAt_iff_of_mem_maximalAtlas
  statement: {x : M} (he : e in maximalAtlas I 1 M)
  proof: differentiableWithinAt_localInvariantProp.liftPropWithinAt_indep_chart he hx he' hy

中文:
定理 mdifferentiableWithinAt_iff_of_mem_maximalAtlas
  结论: {x : M} (he : e in maximalAtlas I 1 M)
  证明: differentiableWithinAt_localInvariantProp.liftPropWithinAt_indep_chart he hx he' hy

Depends on / 依赖: differentiableWithinAt_localInvariantProp, differentiableWithinAt_localInvariantProp.liftPropWithinAt_indep_chart, liftPropWithinAt_indep_chart
-/
theorem mdifferentiableWithinAt_iff_of_mem_maximalAtlas {x : M} (he : e in maximalAtlas I 1 M)
    (he' : e' in maximalAtlas I' 1 M') (hx : x in e.source) (hy : f x in e'.source) :
    MDiffAt[s] f x ↔
      ContinuousWithinAt f s x ∧
        DifferentiableWithinAt 𝕜 (e'.extend I' ∘ f ∘ (e.extend I).symm)
          ((e.extend I).symm ⁻¹' s inter range I) (e.extend I x) :=
  differentiableWithinAt_localInvariantProp.liftPropWithinAt_indep_chart he hx he' hy

/--
theorem `mdifferentiableWithinAt_iff_image` / 定理 `mdifferentiableWithinAt_iff_image`

English:
theorem mdifferentiableWithinAt_iff_image
  statement: {x : M} (he : e in maximalAtlas I 1 M)
  proof: by
  rw [mdifferentiableWithinAt_iff_of_mem_maximalAtlas he he' hx hy]; rw [and_congr_right_iff]
  refine fun _ => differentiableWithinAt_congr_nhds ?_
  simp_rw [nhdsWithin_eq_iff_eventuallyEq, e.extend_symm_preimage_inter_range_eventuallyEq hs hx]

中文:
定理 mdifferentiableWithinAt_iff_image
  结论: {x : M} (he : e in maximalAtlas I 1 M)
  证明: by
  rw [mdifferentiableWithinAt_iff_of_mem_maximalAtlas he he' hx hy]; rw [and_congr_right_iff]
  refine fun _ => differentiableWithinAt_congr_nhds ?_
  simp_rw [nhdsWithin_eq_iff_eventuallyEq, e.extend_symm_preimage_inter_range_eventuallyEq hs hx]

Depends on / 依赖: and_congr_right_iff, differentiableWithinAt_congr_nhds, e.extend_symm_preimage_inter_range_eventuallyEq, extend_symm_preimage_inter_range_eventuallyEq, mdifferentiableWithinAt_iff_of_mem_maximalAtlas, nhdsWithin_eq_iff_eventuallyEq, simp_rw
-/
theorem mdifferentiableWithinAt_iff_image {x : M} (he : e in maximalAtlas I 1 M)
    (he' : e' in maximalAtlas I' 1 M') (hs : s subseteq e.source) (hx : x in e.source)
    (hy : f x in e'.source) :
    MDiffAt[s] f x ↔
      ContinuousWithinAt f s x ∧
        DifferentiableWithinAt 𝕜 (e'.extend I' ∘ f ∘ (e.extend I).symm) (e.extend I '' s)
          (e.extend I x) := by
  rw [mdifferentiableWithinAt_iff_of_mem_maximalAtlas he he' hx hy]; rw [and_congr_right_iff]
  refine fun _ => differentiableWithinAt_congr_nhds ?_
  simp_rw [nhdsWithin_eq_iff_eventuallyEq, e.extend_symm_preimage_inter_range_eventuallyEq hs hx]

/--
theorem `mdifferentiableWithinAt_iff_of_mem_source` / 定理 `mdifferentiableWithinAt_iff_of_mem_source`

English:
theorem mdifferentiableWithinAt_iff_of_mem_source
  statement: [IsManifold I 1 M] [IsManifold I' 1 M']
  proof: mdifferentiableWithinAt_iff_of_mem_maximalAtlas (chart_mem_maximalAtlas x)
    (chart_mem_maximalAtlas y) hx hy

中文:
定理 mdifferentiableWithinAt_iff_of_mem_source
  结论: [是流形 I 1 M] [是流形 I' 1 M']
  证明: mdifferentiableWithinAt_iff_of_mem_maximalAtlas (chart_mem_maximalAtlas x)
    (chart_mem_maximalAtlas y) hx hy

Depends on / 依赖: chart_mem_maximalAtlas, mdifferentiableWithinAt_iff_of_mem_maximalAtlas
-/
theorem mdifferentiableWithinAt_iff_of_mem_source [IsManifold I 1 M] [IsManifold I' 1 M']
    {x' : M} {y : M'} (hx : x' in (chartAt H x).source) (hy : f x' in (chartAt H' y).source) :
    MDiffAt[s] f x' ↔
      ContinuousWithinAt f s x' ∧
        DifferentiableWithinAt 𝕜 (extChartAt I' y ∘ f ∘ (extChartAt I x).symm)
          ((extChartAt I x).symm ⁻¹' s inter range I) (extChartAt I x x') :=
  mdifferentiableWithinAt_iff_of_mem_maximalAtlas (chart_mem_maximalAtlas x)
    (chart_mem_maximalAtlas y) hx hy

/--
theorem `mdifferentiableWithinAt_iff_of_mem_source'` / 定理 `mdifferentiableWithinAt_iff_of_mem_source'`

English:
theorem mdifferentiableWithinAt_iff_of_mem_source'
  statement: [IsManifold I 1 M] [IsManifold I' 1 M']
  proof: by
  refine (mdifferentiableWithinAt_iff_of_mem_source hx hy).trans ?_
  rw [← extChartAt_source I] at hx
  rw [← extChartAt_source I'] at hy
  rw [and_congr_right_iff]
  set e := extChartAt I x; set e' := extChartAt I' (f x)
  refine fun hc => differentiableWithinAt_congr_nhds ?_
  rw [← e.image_source_inter_eq']; rw [← map_extChartAt_nhdsWithin_eq_image' hx]; rw [← map_extChartAt_nhdsWithin' hx]; rw [inter_comm]; rw [nhdsWithin_inter_of_mem]
  exact hc (extChartAt_source_mem_nhds' hy)

中文:
定理 mdifferentiableWithinAt_iff_of_mem_source'
  结论: [是流形 I 1 M] [是流形 I' 1 M']
  证明: by
  refine (mdifferentiableWithinAt_iff_of_mem_source hx hy).trans ?_
  rw [← extChartAt_source I] at hx
  rw [← extChartAt_source I'] at hy
  rw [and_congr_right_iff]
  set e := extChartAt I x; set e' := extChartAt I' (f x)
  refine fun hc => differentiableWithinAt_congr_nhds ?_
  rw [← e.image_source_inter_eq']; rw [← map_extChartAt_nhdsWithin_eq_image' hx]; rw [← map_extChartAt_nhdsWithin' hx]; rw [inter_comm]; rw [nhdsWithin_inter_of_mem]
  exact hc (extChartAt_source_mem_nhds' hy)

Depends on / 依赖: and_congr_right_iff, differentiableWithinAt_congr_nhds, e.image_source_inter_eq, extChartAt, extChartAt_source, extChartAt_source_mem_nhds, image_source_inter_eq, inter_comm, map_extChartAt_nhdsWithin, map_extChartAt_nhdsWithin_eq_image, mdifferentiableWithinAt_iff_of_mem_source, nhdsWithin_inter_of_mem
-/
theorem mdifferentiableWithinAt_iff_of_mem_source' [IsManifold I 1 M] [IsManifold I' 1 M']
    {x' : M} {y : M'} (hx : x' in (chartAt H x).source) (hy : f x' in (chartAt H' y).source) :
    MDiffAt[s] f x' ↔
      ContinuousWithinAt f s x' ∧
        DifferentiableWithinAt 𝕜 (extChartAt I' y ∘ f ∘ (extChartAt I x).symm)
          ((extChartAt I x).target inter (extChartAt I x).symm ⁻¹' (s inter f ⁻¹' (extChartAt I' y).source))
          (extChartAt I x x') := by
  refine (mdifferentiableWithinAt_iff_of_mem_source hx hy).trans ?_
  rw [← extChartAt_source I] at hx
  rw [← extChartAt_source I'] at hy
  rw [and_congr_right_iff]
  set e := extChartAt I x; set e' := extChartAt I' (f x)
  refine fun hc => differentiableWithinAt_congr_nhds ?_
  rw [← e.image_source_inter_eq']; rw [← map_extChartAt_nhdsWithin_eq_image' hx]; rw [← map_extChartAt_nhdsWithin' hx]; rw [inter_comm]; rw [nhdsWithin_inter_of_mem]
  exact hc (extChartAt_source_mem_nhds' hy)

/--
theorem `mdifferentiableAt_iff_of_mem_source` / 定理 `mdifferentiableAt_iff_of_mem_source`

English:
theorem mdifferentiableAt_iff_of_mem_source
  statement: [IsManifold I 1 M] [IsManifold I' 1 M']
  proof: (mdifferentiableWithinAt_iff_of_mem_source hx hy).trans by
    rw [continuousWithinAt_univ]; rw [preimage_univ]; rw [univ_inter]

中文:
定理 mdifferentiableAt_iff_of_mem_source
  结论: [是流形 I 1 M] [是流形 I' 1 M']
  证明: (mdifferentiableWithinAt_iff_of_mem_source hx hy).trans by
    rw [continuousWithinAt_univ]; rw [preimage_univ]; rw [univ_inter]

Depends on / 依赖: continuousWithinAt_univ, mdifferentiableWithinAt_iff_of_mem_source, preimage_univ, univ_inter
-/
theorem mdifferentiableAt_iff_of_mem_source [IsManifold I 1 M] [IsManifold I' 1 M']
    {x' : M} {y : M'} (hx : x' in (chartAt H x).source) (hy : f x' in (chartAt H' y).source) :
    MDiffAt f x' ↔
      ContinuousAt f x' ∧
        DifferentiableWithinAt 𝕜 (extChartAt I' y ∘ f ∘ (extChartAt I x).symm) (range I)
          (extChartAt I x x') :=
(mdifferentiableWithinAt_iff_of_mem_source hx hy).trans by
    rw [continuousWithinAt_univ]; rw [preimage_univ]; rw [univ_inter]

/--
theorem `mdifferentiableOn_iff_of_mem_maximalAtlas` / 定理 `mdifferentiableOn_iff_of_mem_maximalAtlas`

English:
theorem mdifferentiableOn_iff_of_mem_maximalAtlas
  statement: (he : e in maximalAtlas I 1 M)
  proof: by
  simp_rw [ContinuousOn, DifferentiableOn, Set.forall_mem_image, ← forall_and, MDifferentiableOn]
  exact forall₂_congr fun x hx => mdifferentiableWithinAt_iff_image he he' hs (hs hx) (h2s hx)

中文:
定理 mdifferentiableOn_iff_of_mem_maximalAtlas
  结论: (he : e in maximalAtlas I 1 M)
  证明: by
  simp_rw [ContinuousOn, DifferentiableOn, Set.forall_mem_image, ← forall_and, MDifferentiableOn]
  exact forall₂_congr fun x hx => mdifferentiableWithinAt_iff_image he he' hs (hs hx) (h2s hx)

Depends on / 依赖: ContinuousOn, DifferentiableOn, MDifferentiableOn, Set.forall_mem_image, forall_and, forall_mem_image, mdifferentiableWithinAt_iff_image, simp_rw
-/
theorem mdifferentiableOn_iff_of_mem_maximalAtlas (he : e in maximalAtlas I 1 M)
    (he' : e' in maximalAtlas I' 1 M') (hs : s subseteq e.source) (h2s : MapsTo f s e'.source) :
    MDiff[s] f ↔
      ContinuousOn f s ∧
        DifferentiableOn 𝕜 (e'.extend I' ∘ f ∘ (e.extend I).symm) (e.extend I '' s) := by
  simp_rw [ContinuousOn, DifferentiableOn, Set.forall_mem_image, ← forall_and, MDifferentiableOn]
  exact forall₂_congr fun x hx => mdifferentiableWithinAt_iff_image he he' hs (hs hx) (h2s hx)

/--
theorem `mdifferentiableOn_iff_of_mem_maximalAtlas'` / 定理 `mdifferentiableOn_iff_of_mem_maximalAtlas'`

English:
theorem mdifferentiableOn_iff_of_mem_maximalAtlas'
  statement: (he : e in maximalAtlas I 1 M)
  proof: (mdifferentiableOn_iff_of_mem_maximalAtlas he he' hs h2s).trans and_iff_right_of_imp fun h =>
    (e.continuousOn_writtenInExtend_iff hs h2s).1 h.continuousOn

中文:
定理 mdifferentiableOn_iff_of_mem_maximalAtlas'
  结论: (he : e in maximalAtlas I 1 M)
  证明: (mdifferentiableOn_iff_of_mem_maximalAtlas he he' hs h2s).trans and_iff_right_of_imp fun h =>
    (e.continuousOn_writtenInExtend_iff hs h2s).1 h.continuousOn

Depends on / 依赖: and_iff_right_of_imp, continuousOn, continuousOn_writtenInExtend_iff, e.continuousOn_writtenInExtend_iff, h.continuousOn, mdifferentiableOn_iff_of_mem_maximalAtlas
-/
theorem mdifferentiableOn_iff_of_mem_maximalAtlas' (he : e in maximalAtlas I 1 M)
    (he' : e' in maximalAtlas I' 1 M') (hs : s subseteq e.source) (h2s : MapsTo f s e'.source) :
    MDiff[s] f ↔
      DifferentiableOn 𝕜 (e'.extend I' ∘ f ∘ (e.extend I).symm) (e.extend I '' s) :=
(mdifferentiableOn_iff_of_mem_maximalAtlas he he' hs h2s).trans and_iff_right_of_imp fun h =>
    (e.continuousOn_writtenInExtend_iff hs h2s).1 h.continuousOn

variable [IsManifold I 1 M] [IsManifold I' 1 M']

/--
theorem `mdifferentiableOn_iff_of_subset_source` / 定理 `mdifferentiableOn_iff_of_subset_source`

English:
theorem mdifferentiableOn_iff_of_subset_source
  proof: mdifferentiableOn_iff_of_mem_maximalAtlas (chart_mem_maximalAtlas x)
    (chart_mem_maximalAtlas y) hs h2s

中文:
定理 mdifferentiableOn_iff_of_subset_source
  证明: mdifferentiableOn_iff_of_mem_maximalAtlas (chart_mem_maximalAtlas x)
    (chart_mem_maximalAtlas y) hs h2s

Depends on / 依赖: chart_mem_maximalAtlas, mdifferentiableOn_iff_of_mem_maximalAtlas
-/
theorem mdifferentiableOn_iff_of_subset_source
    {x : M} {y : M'} (hs : s subseteq (chartAt H x).source) (h2s : MapsTo f s (chartAt H' y).source) :
    MDiff[s] f ↔
      ContinuousOn f s ∧
        DifferentiableOn 𝕜 (extChartAt I' y ∘ f ∘ (extChartAt I x).symm) (extChartAt I x '' s) :=
  mdifferentiableOn_iff_of_mem_maximalAtlas (chart_mem_maximalAtlas x)
    (chart_mem_maximalAtlas y) hs h2s

/--
theorem `mdifferentiableOn_iff_of_subset_source'` / 定理 `mdifferentiableOn_iff_of_subset_source'`

English:
theorem mdifferentiableOn_iff_of_subset_source'
  proof: by
  rw [extChartAt_source] at hs h2s
  exact mdifferentiableOn_iff_of_mem_maximalAtlas' (chart_mem_maximalAtlas x)
    (chart_mem_maximalAtlas y) hs h2s

中文:
定理 mdifferentiableOn_iff_of_subset_source'
  证明: by
  rw [extChartAt_source] at hs h2s
  exact mdifferentiableOn_iff_of_mem_maximalAtlas' (chart_mem_maximalAtlas x)
    (chart_mem_maximalAtlas y) hs h2s

Depends on / 依赖: chart_mem_maximalAtlas, extChartAt_source, mdifferentiableOn_iff_of_mem_maximalAtlas
-/
theorem mdifferentiableOn_iff_of_subset_source'
    {x : M} {y : M'} (hs : s subseteq (extChartAt I x).source)
    (h2s : MapsTo f s (extChartAt I' y).source) :
    MDiff[s] f ↔
        DifferentiableOn 𝕜 (extChartAt I' y ∘ f ∘ (extChartAt I x).symm) (extChartAt I x '' s) := by
  rw [extChartAt_source] at hs h2s
  exact mdifferentiableOn_iff_of_mem_maximalAtlas' (chart_mem_maximalAtlas x)
    (chart_mem_maximalAtlas y) hs h2s

/--
theorem `mdifferentiableOn_iff` / 定理 `mdifferentiableOn_iff`

English:
theorem mdifferentiableOn_iff
  proof: by
  constructor
  · intro h
    refine ⟨fun x hx => (h x hx).1, fun x y z hz => ?_⟩
    simp only [mfld_simps] at hz
    let w := (extChartAt I x).symm z
    have : w in s := by simp only [w, hz, mfld_simps]
    specialize h w this
    have w1 : w in (chartAt H x).source := by simp only [w, hz, mfld_simps]
    have w2 : f w in (chartAt H' y).source := by simp only [w, hz, mfld_simps]
    convert! ((mdifferentiableWithinAt_iff_of_mem_source w1 w2).mp h).2.mono _
    · simp only [w, hz, mfld_simps]
    · mfld_set_tac
  · rintro ⟨hcont, hdiff⟩ x hx
    refine differentiableWithinAt_localInvariantProp.liftPropWithinAt_iff.mpr ?_
    refine ⟨hcont x hx, ?_⟩
    dsimp [DifferentiableWithinAtProp]
    convert! hdiff x (f x) (extChartAt I x x) (by simp only [hx, mfld_simps]) using 1
    mfld_set_tac

中文:
定理 mdifferentiableOn_iff
  证明: by
  constructor
  · intro h
    refine ⟨fun x hx => (h x hx).1, fun x y z hz => ?_⟩
    simp only [mfld_simps] at hz
    let w := (extChartAt I x).symm z
    have : w in s := by simp only [w, hz, mfld_simps]
    specialize h w this
    have w1 : w in (chartAt H x).source := by simp only [w, hz, mfld_simps]
    have w2 : f w in (chartAt H' y).source := by simp only [w, hz, mfld_simps]
    convert! ((mdifferentiableWithinAt_iff_of_mem_source w1 w2).mp h).2.mono _
    · simp only [w, hz, mfld_simps]
    · mfld_set_tac
  · rintro ⟨hcont, hdiff⟩ x hx
    refine differentiableWithinAt_localInvariantProp.liftPropWithinAt_iff.mpr ?_
    refine ⟨hcont x hx, ?_⟩
    dsimp [DifferentiableWithinAtProp]
    convert! hdiff x (f x) (extChartAt I x x) (by simp only [hx, mfld_simps]) using 1
    mfld_set_tac

Depends on / 依赖: chartAt, convert, extChartAt, mdifferentiableWithinAt_iff_of_mem_source, mfld_set_tac, mfld_simps, source, specialize
-/
theorem mdifferentiableOn_iff :
    MDiff[s] f ↔
      ContinuousOn f s ∧
        forall (x : M) (y : M'),
          DifferentiableOn 𝕜 (extChartAt I' y ∘ f ∘ (extChartAt I x).symm)
            ((extChartAt I x).target inter
              (extChartAt I x).symm ⁻¹' (s inter f ⁻¹' (extChartAt I' y).source)) := by
  constructor
  · intro h
    refine ⟨fun x hx => (h x hx).1, fun x y z hz => ?_⟩
    simp only [mfld_simps] at hz
    let w := (extChartAt I x).symm z
    have : w in s := by simp only [w, hz, mfld_simps]
    specialize h w this
    have w1 : w in (chartAt H x).source := by simp only [w, hz, mfld_simps]
    have w2 : f w in (chartAt H' y).source := by simp only [w, hz, mfld_simps]
    convert! ((mdifferentiableWithinAt_iff_of_mem_source w1 w2).mp h).2.mono _
    · simp only [w, hz, mfld_simps]
    · mfld_set_tac
  · rintro ⟨hcont, hdiff⟩ x hx
    refine differentiableWithinAt_localInvariantProp.liftPropWithinAt_iff.mpr ?_
    refine ⟨hcont x hx, ?_⟩
    dsimp [DifferentiableWithinAtProp]
    convert! hdiff x (f x) (extChartAt I x x) (by simp only [hx, mfld_simps]) using 1
    mfld_set_tac

/--
theorem `mdifferentiableOn_iff_target` / 定理 `mdifferentiableOn_iff_target`

English:
theorem mdifferentiableOn_iff_target
  proof: by
  simp only [mdifferentiableOn_iff, ModelWithCorners.source_eq, chartAt_self_eq,
    OpenPartialHomeomorph.refl_partialEquiv, PartialEquiv.refl_trans, extChartAt,
    OpenPartialHomeomorph.extend, Set.preimage_univ, Set.inter_univ, and_congr_right_iff]
  intro h
  constructor
  · refine fun h' y => ⟨?_, fun x _ => h' x y⟩
    have h'' : ContinuousOn _ univ := (ModelWithCorners.continuous I').continuousOn
    convert! (h''.comp_inter (chartAt H' y).continuousOn_toFun).comp_inter h
    simp
  · exact fun h' x y => (h' y).2 x 0

中文:
定理 mdifferentiableOn_iff_target
  证明: by
  simp only [mdifferentiableOn_iff, ModelWithCorners.source_eq, chartAt_self_eq,
    OpenPartialHomeomorph.refl_partialEquiv, PartialEquiv.refl_trans, extChartAt,
    OpenPartialHomeomorph.extend, Set.preimage_univ, Set.inter_univ, and_congr_right_iff]
  intro h
  constructor
  · refine fun h' y => ⟨?_, fun x _ => h' x y⟩
    have h'' : ContinuousOn _ univ := (ModelWithCorners.continuous I').continuousOn
    convert! (h''.comp_inter (chartAt H' y).continuousOn_toFun).comp_inter h
    simp
  · exact fun h' x y => (h' y).2 x 0

Depends on / 依赖: ContinuousOn, ModelWithCorners, ModelWithCorners.continuous, ModelWithCorners.source_eq, OpenPartialHomeomorph, OpenPartialHomeomorph.extend, OpenPartialHomeomorph.refl_partialEquiv, PartialEquiv, PartialEquiv.refl_trans, Set.inter_univ, Set.preimage_univ, and_congr_right_iff, chartAt, chartAt_self_eq, comp_inter, continuous, continuousOn, continuousOn_toFun, convert, extChartAt
-/
theorem mdifferentiableOn_iff_target :
    MDiff[s] f ↔
      ContinuousOn f s ∧
        forall y : M', MDiff[s inter f ⁻¹' (extChartAt I' y).source] (extChartAt I' y ∘ f) := by
  simp only [mdifferentiableOn_iff, ModelWithCorners.source_eq, chartAt_self_eq,
    OpenPartialHomeomorph.refl_partialEquiv, PartialEquiv.refl_trans, extChartAt,
    OpenPartialHomeomorph.extend, Set.preimage_univ, Set.inter_univ, and_congr_right_iff]
  intro h
  constructor
  · refine fun h' y => ⟨?_, fun x _ => h' x y⟩
    have h'' : ContinuousOn _ univ := (ModelWithCorners.continuous I').continuousOn
    convert! (h''.comp_inter (chartAt H' y).continuousOn_toFun).comp_inter h
    simp
  · exact fun h' x y => (h' y).2 x 0

/--
theorem `mdifferentiable_iff` / 定理 `mdifferentiable_iff`

English:
theorem mdifferentiable_iff
  proof: by
  simp [← mdifferentiableOn_univ, mdifferentiableOn_iff, continuousOn_univ]

中文:
定理 mdifferentiable_iff
  证明: by
  simp [← mdifferentiableOn_univ, mdifferentiableOn_iff, continuousOn_univ]

Depends on / 依赖: continuousOn_univ, mdifferentiableOn_iff, mdifferentiableOn_univ
-/
theorem mdifferentiable_iff :
    MDiff f ↔
      Continuous f ∧
        forall (x : M) (y : M'),
          DifferentiableOn 𝕜 (extChartAt I' y ∘ f ∘ (extChartAt I x).symm)
            ((extChartAt I x).target inter
              (extChartAt I x).symm ⁻¹' f ⁻¹' (extChartAt I' y).source) := by
  simp [← mdifferentiableOn_univ, mdifferentiableOn_iff, continuousOn_univ]

/--
theorem `mdifferentiable_iff_target` / 定理 `mdifferentiable_iff_target`

English:
theorem mdifferentiable_iff_target
  proof: by
  rw [← mdifferentiableOn_univ]; rw [mdifferentiableOn_iff_target]
  simp [continuousOn_univ]

中文:
定理 mdifferentiable_iff_target
  证明: by
  rw [← mdifferentiableOn_univ]; rw [mdifferentiableOn_iff_target]
  simp [continuousOn_univ]

Depends on / 依赖: continuousOn_univ, mdifferentiableOn_iff_target, mdifferentiableOn_univ
-/
theorem mdifferentiable_iff_target :
    MDiff f ↔
      Continuous f ∧ forall y : M',
        MDiff[f ⁻¹' (extChartAt I' y).source] (extChartAt I' y ∘ f) := by
  rw [← mdifferentiableOn_univ]; rw [mdifferentiableOn_iff_target]
  simp [continuousOn_univ]

end IsManifold

/-! ### Deducing differentiability from smoothness -/

variable {n : WithTop Nat∞}

/--
theorem `ContMDiffWithinAt.mdifferentiableWithinAt` / 定理 `ContMDiffWithinAt.mdifferentiableWithinAt`

English:
theorem ContMDiffWithinAt.mdifferentiableWithinAt
  given: (hf : CMDiffAt[s] n f x) (hn : n != 0)
  proof: by
  suffices h : MDiffAt[s inter f ⁻¹' (extChartAt I' (f x)).source] f x by
    rwa [mdifferentiableWithinAt_inter'] at h
    apply hf.1.preimage_mem_nhdsWithin
    exact extChartAt_source_mem_nhds (f x)
  rw [mdifferentiableWithinAt_iff]
  exact ⟨hf.1.mono inter_subset_left, (hf.2.differentiableWithinAt hn).mono (by mfld_set_tac)⟩

中文:
定理 ContMDiffWithinAt.mdifferentiableWithinAt
  条件: (hf : CMDiffAt[s] n f x) (hn : n != 0)
  证明: by
  suffices h : MDiffAt[s inter f ⁻¹' (extChartAt I' (f x)).source] f x by
    rwa [mdifferentiableWithinAt_inter'] at h
    apply hf.1.preimage_mem_nhdsWithin
    exact extChartAt_source_mem_nhds (f x)
  rw [mdifferentiableWithinAt_iff]
  exact ⟨hf.1.mono inter_subset_left, (hf.2.differentiableWithinAt hn).mono (by mfld_set_tac)⟩

Depends on / 依赖: MDiffAt, differentiableWithinAt, extChartAt, extChartAt_source_mem_nhds, inter_subset_left, mdifferentiableWithinAt_iff, mdifferentiableWithinAt_inter, mfld_set_tac, preimage_mem_nhdsWithin, source
-/
theorem ContMDiffWithinAt.mdifferentiableWithinAt (hf : CMDiffAt[s] n f x) (hn : n != 0) :
    MDiffAt[s] f x := by
  suffices h : MDiffAt[s inter f ⁻¹' (extChartAt I' (f x)).source] f x by
    rwa [mdifferentiableWithinAt_inter'] at h
    apply hf.1.preimage_mem_nhdsWithin
    exact extChartAt_source_mem_nhds (f x)
  rw [mdifferentiableWithinAt_iff]
  exact ⟨hf.1.mono inter_subset_left, (hf.2.differentiableWithinAt hn).mono (by mfld_set_tac)⟩

/--
theorem `ContMDiffAt.mdifferentiableAt` / 定理 `ContMDiffAt.mdifferentiableAt`

English:
theorem ContMDiffAt.mdifferentiableAt
  given: (hf : CMDiffAt n f x) (hn : n != 0)
  statement: MDiffAt f x
  proof: mdifferentiableWithinAt_univ.1 ContMDiffWithinAt.mdifferentiableWithinAt hf hn

中文:
定理 ContMDiffAt.mdifferentiableAt
  条件: (hf : CMDiffAt n f x) (hn : n != 0)
  结论: MDiffAt f x
  证明: mdifferentiableWithinAt_univ.1 ContMDiffWithinAt.mdifferentiableWithinAt hf hn

Depends on / 依赖: ContMDiffWithinAt, ContMDiffWithinAt.mdifferentiableWithinAt, mdifferentiableWithinAt, mdifferentiableWithinAt_univ
-/
theorem ContMDiffAt.mdifferentiableAt (hf : CMDiffAt n f x) (hn : n != 0) : MDiffAt f x :=
mdifferentiableWithinAt_univ.1 ContMDiffWithinAt.mdifferentiableWithinAt hf hn

/--
theorem `ContMDiff.mdifferentiableAt` / 定理 `ContMDiff.mdifferentiableAt`

English:
theorem ContMDiff.mdifferentiableAt
  given: (hf : CMDiff n f) (hn : n != 0)
  statement: MDiffAt f x
  proof: hf.contMDiffAt.mdifferentiableAt hn

中文:
定理 ContMDiff.mdifferentiableAt
  条件: (hf : CMDiff n f) (hn : n != 0)
  结论: MDiffAt f x
  证明: hf.contMDiffAt.mdifferentiableAt hn

Depends on / 依赖: contMDiffAt, hf.contMDiffAt.mdifferentiableAt, mdifferentiableAt
-/
theorem ContMDiff.mdifferentiableAt (hf : CMDiff n f) (hn : n != 0) : MDiffAt f x :=
  hf.contMDiffAt.mdifferentiableAt hn

/--
theorem `ContMDiff.mdifferentiableWithinAt` / 定理 `ContMDiff.mdifferentiableWithinAt`

English:
theorem ContMDiff.mdifferentiableWithinAt
  given: (hf : CMDiff n f) (hn : n != 0)
  statement: MDiffAt[s] f x
  proof: (hf.contMDiffAt.mdifferentiableAt hn).mdifferentiableWithinAt

中文:
定理 ContMDiff.mdifferentiableWithinAt
  条件: (hf : CMDiff n f) (hn : n != 0)
  结论: MDiffAt[s] f x
  证明: (hf.contMDiffAt.mdifferentiableAt hn).mdifferentiableWithinAt

Depends on / 依赖: contMDiffAt, hf.contMDiffAt.mdifferentiableAt, mdifferentiableAt, mdifferentiableWithinAt
-/
theorem ContMDiff.mdifferentiableWithinAt (hf : CMDiff n f) (hn : n != 0) : MDiffAt[s] f x :=
  (hf.contMDiffAt.mdifferentiableAt hn).mdifferentiableWithinAt

/--
theorem `ContMDiffOn.mdifferentiableOn` / 定理 `ContMDiffOn.mdifferentiableOn`

English:
theorem ContMDiffOn.mdifferentiableOn
  given: (hf : CMDiff[s] n f) (hn : n != 0)
  statement: MDiff[s] f
  proof: fun x hx => (hf x hx).mdifferentiableWithinAt hn

中文:
定理 ContMDiffOn.mdifferentiableOn
  条件: (hf : CMDiff[s] n f) (hn : n != 0)
  结论: MDiff[s] f
  证明: fun x hx => (hf x hx).mdifferentiableWithinAt hn

Depends on / 依赖: mdifferentiableWithinAt
-/
theorem ContMDiffOn.mdifferentiableOn (hf : CMDiff[s] n f) (hn : n != 0) : MDiff[s] f :=
  fun x hx => (hf x hx).mdifferentiableWithinAt hn

/--
theorem `ContMDiff.mdifferentiable` / 定理 `ContMDiff.mdifferentiable`

English:
theorem ContMDiff.mdifferentiable
  given: (hf : CMDiff n f) (hn : n != 0)
  statement: MDiff f
  proof: fun x => (hf x).mdifferentiableAt hn

中文:
定理 ContMDiff.mdifferentiable
  条件: (hf : CMDiff n f) (hn : n != 0)
  结论: MDiff f
  证明: fun x => (hf x).mdifferentiableAt hn

Depends on / 依赖: mdifferentiableAt
-/
theorem ContMDiff.mdifferentiable (hf : CMDiff n f) (hn : n != 0) : MDiff f :=
  fun x => (hf x).mdifferentiableAt hn

/--
theorem `MDifferentiableOn.continuousOn` / 定理 `MDifferentiableOn.continuousOn`

English:
theorem MDifferentiableOn.continuousOn
  given: (h : MDiff[s] f)
  statement: ContinuousOn f s
  proof: fun x hx => (h x hx).continuousWithinAt

中文:
定理 MDifferentiableOn.continuousOn
  条件: (h : MDiff[s] f)
  结论: ContinuousOn f s
  证明: fun x hx => (h x hx).continuousWithinAt

Depends on / 依赖: continuousWithinAt
-/
theorem MDifferentiableOn.continuousOn (h : MDiff[s] f) : ContinuousOn f s :=
  fun x hx => (h x hx).continuousWithinAt

/--
theorem `MDifferentiable.continuous` / 定理 `MDifferentiable.continuous`

English:
theorem MDifferentiable.continuous
  given: (h : MDiff f)
  statement: Continuous f
  proof: continuous_iff_continuousAt.2 fun x => (h x).continuousAt

中文:
定理 MDifferentiable.continuous
  条件: (h : MDiff f)
  结论: 连续 f
  证明: continuous_iff_continuousAt.2 fun x => (h x).continuousAt

Depends on / 依赖: continuousAt, continuous_iff_continuousAt
-/
theorem MDifferentiable.continuous (h : MDiff f) : Continuous f :=
  continuous_iff_continuousAt.2 fun x => (h x).continuousAt


/--
theorem `writtenInExtChartAt_comp` / 定理 `writtenInExtChartAt_comp`

English:
theorem writtenInExtChartAt_comp
  given: (h : ContinuousWithinAt f s x)
  proof: by
  apply
    @Filter.mem_of_superset _ _ (f ∘ (extChartAt I x).symm ⁻¹' (extChartAt I' (f x)).source) _
      (extChartAt_preimage_mem_nhdsWithin
        (h.preimage_mem_nhdsWithin (extChartAt_source_mem_nhds _)))
  mfld_set_tac

中文:
定理 writtenInExtChartAt_comp
  条件: (h : ContinuousWithinAt f s x)
  证明: by
  apply
    @Filter.mem_of_superset _ _ (f ∘ (extChartAt I x).symm ⁻¹' (extChartAt I' (f x)).source) _
      (extChartAt_preimage_mem_nhdsWithin
        (h.preimage_mem_nhdsWithin (extChartAt_source_mem_nhds _)))
  mfld_set_tac

Depends on / 依赖: Filter, Filter.mem_of_superset, extChartAt, extChartAt_preimage_mem_nhdsWithin, extChartAt_source_mem_nhds, h.preimage_mem_nhdsWithin, mem_of_superset, mfld_set_tac, preimage_mem_nhdsWithin, source
-/
theorem writtenInExtChartAt_comp (h : ContinuousWithinAt f s x) :
    writtenInExtChartAt I I'' x (g ∘ f)
      =ᶠ[𝓝[(extChartAt I x).symm ⁻¹' s inter range I] (extChartAt I x x)]
        (writtenInExtChartAt I' I'' (f x) g ∘ writtenInExtChartAt I I' x f) := by
  apply
    @Filter.mem_of_superset _ _ (f ∘ (extChartAt I x).symm ⁻¹' (extChartAt I' (f x)).source) _
      (extChartAt_preimage_mem_nhdsWithin
        (h.preimage_mem_nhdsWithin (extChartAt_source_mem_nhds _)))
  mfld_set_tac

variable {f' f₀' f₁' : TangentSpace% x ->L[𝕜] TangentSpace% (f x)}
  {g' : TangentSpace% (f x) ->L[𝕜] TangentSpace% (g (f x))}

set_option backward.isDefEq.respectTransparency false in
/-- `UniqueMDiffWithinAt` achieves its goal: it implies the uniqueness of the derivative. -/
protected nonrec theorem UniqueMDiffWithinAt.eq (U : UniqueMDiffAt[s] x)
    (h : HasMFDerivAt[s] f x f') (h₁ : HasMFDerivAt[s] f x f₁') : f' = f₁' := by
  -- `by apply` because the instances can be found in the term but not in the goal.
  apply U.eq h.2 h₁.2

/--
theorem `UniqueMDiffOn.eq` / 定理 `UniqueMDiffOn.eq`

English:
theorem UniqueMDiffOn.eq
  statement: (U : UniqueMDiff[s]) (hx : x in s)
  proof: UniqueMDiffWithinAt.eq (U _ hx) h h₁

中文:
定理 UniqueMDiffOn.eq
  结论: (U : UniqueMDiff[s]) (hx : x in s)
  证明: UniqueMDiffWithinAt.eq (U _ hx) h h₁

Depends on / 依赖: HasLeftInverse, HasLeftInverse.injective, Injective, IsStablyFiniteRing, congr_arg, exists_rightInverse_of_surjective, g.exists_rightInverse_of_surjective, injective, injective_iff_surjective, isStablyFiniteRing_iff_isDedekindFiniteMonoid_moduleEnd, isStablyFiniteRing_iff_isDedekindFiniteMonoid_moduleEnd.mpr, mul_assoc, mul_one, one_mul, range_eq_top
-/
protected theorem UniqueMDiffOn.eq (U : UniqueMDiff[s]) (hx : x in s)
    (h : HasMFDerivAt[s] f x f') (h₁ : HasMFDerivAt[s] f x f₁') : f' = f₁' :=
  UniqueMDiffWithinAt.eq (U _ hx) h h₁

/-!
### General lemmas on derivatives of functions between manifolds

We mimic the API for functions between vector spaces
-/

@[simp, mfld_simps]
/--
theorem `mfderivWithin_univ` / 定理 `mfderivWithin_univ`

English:
theorem mfderivWithin_univ
  statement: mfderiv[univ] f = mfderiv% f
  proof: by
  ext x : 1
  simp only [mfderivWithin, mfderiv, mfld_simps]
  rw [mdifferentiableWithinAt_univ]

中文:
定理 mfderivWithin_univ
  结论: mfderiv[univ] f = mfderiv% f
  证明: by
  ext x : 1
  simp only [mfderivWithin, mfderiv, mfld_simps]
  rw [mdifferentiableWithinAt_univ]

Depends on / 依赖: mdifferentiableWithinAt_univ, mfderiv, mfderivWithin, mfld_simps
-/
theorem mfderivWithin_univ : mfderiv[univ] f = mfderiv% f := by
  ext x : 1
  simp only [mfderivWithin, mfderiv, mfld_simps]
  rw [mdifferentiableWithinAt_univ]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `mfderivWithin_zero_of_not_mdifferentiableWithinAt` / 定理 `mfderivWithin_zero_of_not_mdifferentiableWithinAt`

English:
theorem mfderivWithin_zero_of_not_mdifferentiableWithinAt
  given: (h : ¬MDiffAt[s] f x)
  proof: by
  simp only [mfderivWithin, h, if_neg, not_false_iff]

中文:
定理 mfderivWithin_zero_of_not_mdifferentiableWithinAt
  条件: (h : ¬MDiffAt[s] f x)
  证明: by
  simp only [mfderivWithin, h, if_neg, not_false_iff]

Depends on / 依赖: if_neg, mfderivWithin, not_false_iff
-/
theorem mfderivWithin_zero_of_not_mdifferentiableWithinAt (h : ¬MDiffAt[s] f x) :
    mfderiv[s] f x = 0 := by
  simp only [mfderivWithin, h, if_neg, not_false_iff]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `mfderiv_zero_of_not_mdifferentiableAt` / 定理 `mfderiv_zero_of_not_mdifferentiableAt`

English:
theorem mfderiv_zero_of_not_mdifferentiableAt
  given: (h : ¬MDiffAt f x)
  proof: by simp only [mfderiv, h, if_neg, not_false_iff]

@[nontriviality]

中文:
定理 mfderiv_zero_of_not_mdifferentiableAt
  条件: (h : ¬MDiffAt f x)
  证明: by simp only [mfderiv, h, if_neg, not_false_iff]

@[nontriviality]

Depends on / 依赖: if_neg, mfderiv, not_false_iff
-/
theorem mfderiv_zero_of_not_mdifferentiableAt (h : ¬MDiffAt f x) :
    mfderiv% f x = 0 := by simp only [mfderiv, h, if_neg, not_false_iff]

@[nontriviality]
/--
theorem `mdifferentiable_of_subsingleton` / 定理 `mdifferentiable_of_subsingleton`

English:
theorem mdifferentiable_of_subsingleton
  given: [Subsingleton E]
  statement: MDiff f
  proof: by
  intro x
  have : Subsingleton H := I.injective.subsingleton
  have : DiscreteTopology M := discreteTopology H M
  simp only [mdifferentiableAt_iff, continuous_of_discreteTopology.continuousAt, true_and]
  exact (hasFDerivAt_of_subsingleton _ _).differentiableAt.differentiableWithinAt

@[nontriviality]

中文:
定理 mdifferentiable_of_subsingleton
  条件: [子单例 E]
  结论: MDiff f
  证明: by
  intro x
  have : Subsingleton H := I.injective.subsingleton
  have : DiscreteTopology M := discreteTopology H M
  simp only [mdifferentiableAt_iff, continuous_of_discreteTopology.continuousAt, true_and]
  exact (hasFDerivAt_of_subsingleton _ _).differentiableAt.differentiableWithinAt

@[nontriviality]

Depends on / 依赖: DiscreteTopology, I.injective.subsingleton, Subsingleton, continuousAt, continuous_of_discreteTopology, continuous_of_discreteTopology.continuousAt, differentiableAt, differentiableAt.differentiableWithinAt, differentiableWithinAt, discreteTopology, hasFDerivAt_of_subsingleton, injective, mdifferentiableAt_iff, subsingleton, true_and
-/
theorem mdifferentiable_of_subsingleton [Subsingleton E] : MDiff f := by
  intro x
  have : Subsingleton H := I.injective.subsingleton
  have : DiscreteTopology M := discreteTopology H M
  simp only [mdifferentiableAt_iff, continuous_of_discreteTopology.continuousAt, true_and]
  exact (hasFDerivAt_of_subsingleton _ _).differentiableAt.differentiableWithinAt

@[nontriviality]
/--
theorem `mdifferentiableWithinAt_of_subsingleton` / 定理 `mdifferentiableWithinAt_of_subsingleton`

English:
theorem mdifferentiableWithinAt_of_subsingleton
  given: [Subsingleton E]
  statement: MDiffAt[s] f x
  proof: (mdifferentiable_of_subsingleton x).mdifferentiableWithinAt

中文:
定理 mdifferentiableWithinAt_of_subsingleton
  条件: [子单例 E]
  结论: MDiffAt[s] f x
  证明: (mdifferentiable_of_subsingleton x).mdifferentiableWithinAt

Depends on / 依赖: mdifferentiableWithinAt, mdifferentiable_of_subsingleton
-/
theorem mdifferentiableWithinAt_of_subsingleton [Subsingleton E] : MDiffAt[s] f x :=
  (mdifferentiable_of_subsingleton x).mdifferentiableWithinAt

/--
lemma `mdifferentiableWithinAt_of_mfderivWithin_injective` / 引理 `mdifferentiableWithinAt_of_mfderivWithin_injective`

English:
lemma mdifferentiableWithinAt_of_mfderivWithin_injective
  given: (hf : Injective (mfderiv[s] f x))
  proof: by
  nontriviality E
  have : Nontrivial (TangentSpace% x) := inferInstanceAs (Nontrivial E)
  contrapose hf
  rw [mfderivWithin_zero_of_not_mdifferentiableWithinAt hf]
  exact not_injective_const

中文:
引理 mdifferentiableWithinAt_of_mfderivWithin_injective
  条件: (hf : 单射 (mfderiv[s] f x))
  证明: by
  nontriviality E
  have : Nontrivial (TangentSpace% x) := inferInstanceAs (Nontrivial E)
  contrapose hf
  rw [mfderivWithin_zero_of_not_mdifferentiableWithinAt hf]
  exact not_injective_const

Depends on / 依赖: Nontrivial, TangentSpace, contrapose, mfderivWithin_zero_of_not_mdifferentiableWithinAt, nontriviality, not_injective_const
-/
lemma mdifferentiableWithinAt_of_mfderivWithin_injective (hf : Injective (mfderiv[s] f x)) :
    MDiffAt[s] f x := by
  nontriviality E
  have : Nontrivial (TangentSpace% x) := inferInstanceAs (Nontrivial E)
  contrapose hf
  rw [mfderivWithin_zero_of_not_mdifferentiableWithinAt hf]
  exact not_injective_const

/--
lemma `mdifferentiableAt_of_mfderiv_injective` / 引理 `mdifferentiableAt_of_mfderiv_injective`

English:
lemma mdifferentiableAt_of_mfderiv_injective
  given: {f : M -> M'} (hf : Injective (mfderiv% f x))
  proof: by
  simp only [← mdifferentiableWithinAt_univ, ← mfderivWithin_univ] at hf ⊢
  exact mdifferentiableWithinAt_of_mfderivWithin_injective hf

中文:
引理 mdifferentiableAt_of_mfderiv_injective
  条件: {f : M -> M'} (hf : 单射 (mfderiv% f x))
  证明: by
  simp only [← mdifferentiableWithinAt_univ, ← mfderivWithin_univ] at hf ⊢
  exact mdifferentiableWithinAt_of_mfderivWithin_injective hf

Depends on / 依赖: mdifferentiableWithinAt_of_mfderivWithin_injective, mdifferentiableWithinAt_univ, mfderivWithin_univ
-/
lemma mdifferentiableAt_of_mfderiv_injective {f : M -> M'} (hf : Injective (mfderiv% f x)) :
    MDiffAt f x := by
  simp only [← mdifferentiableWithinAt_univ, ← mfderivWithin_univ] at hf ⊢
  exact mdifferentiableWithinAt_of_mfderivWithin_injective hf

/--
theorem `mdifferentiableWithinAt_of_isInvertible_mfderivWithin` / 定理 `mdifferentiableWithinAt_of_isInvertible_mfderivWithin`

English:
theorem mdifferentiableWithinAt_of_isInvertible_mfderivWithin
  given: (hf : (mfderiv[s] f x).IsInvertible)
  proof: mdifferentiableWithinAt_of_mfderivWithin_injective hf.injective

中文:
定理 mdifferentiableWithinAt_of_isInvertible_mfderivWithin
  条件: (hf : (mfderiv[s] f x).IsInvertible)
  证明: mdifferentiableWithinAt_of_mfderivWithin_injective hf.injective

Depends on / 依赖: hf.injective, injective, mdifferentiableWithinAt_of_mfderivWithin_injective
-/
theorem mdifferentiableWithinAt_of_isInvertible_mfderivWithin (hf : (mfderiv[s] f x).IsInvertible) :
    MDiffAt[s] f x :=
  mdifferentiableWithinAt_of_mfderivWithin_injective hf.injective

/--
theorem `mdifferentiableAt_of_isInvertible_mfderiv` / 定理 `mdifferentiableAt_of_isInvertible_mfderiv`

English:
theorem mdifferentiableAt_of_isInvertible_mfderiv
  given: (hf : (mfderiv% f x).IsInvertible)
  proof: mdifferentiableAt_of_mfderiv_injective hf.injective

中文:
定理 mdifferentiableAt_of_isInvertible_mfderiv
  条件: (hf : (mfderiv% f x).IsInvertible)
  证明: mdifferentiableAt_of_mfderiv_injective hf.injective

Depends on / 依赖: hf.injective, injective, mdifferentiableAt_of_mfderiv_injective
-/
theorem mdifferentiableAt_of_isInvertible_mfderiv (hf : (mfderiv% f x).IsInvertible) :
    MDiffAt f x :=
  mdifferentiableAt_of_mfderiv_injective hf.injective

/--
theorem `HasMFDerivWithinAt.mono` / 定理 `HasMFDerivWithinAt.mono`

English:
theorem HasMFDerivWithinAt.mono
  given: (h : HasMFDerivAt[t] f x f') (hst : s subseteq t)
  proof: ⟨ContinuousWithinAt.mono h.1 hst,
    HasFDerivWithinAt.mono h.2 (inter_subset_inter (preimage_mono hst) (Subset.refl _))⟩

中文:
定理 HasMFDerivWithinAt.mono
  条件: (h : HasMFDerivAt[t] f x f') (hst : s subseteq t)
  证明: ⟨ContinuousWithinAt.mono h.1 hst,
    HasFDerivWithinAt.mono h.2 (inter_subset_inter (preimage_mono hst) (Subset.refl _))⟩

Depends on / 依赖: ContinuousWithinAt, ContinuousWithinAt.mono, HasFDerivWithinAt, HasFDerivWithinAt.mono, Subset, Subset.refl, inter_subset_inter, preimage_mono
-/
theorem HasMFDerivWithinAt.mono (h : HasMFDerivAt[t] f x f') (hst : s subseteq t) :
    HasMFDerivAt[s] f x f' :=
  ⟨ContinuousWithinAt.mono h.1 hst,
    HasFDerivWithinAt.mono h.2 (inter_subset_inter (preimage_mono hst) (Subset.refl _))⟩

/--
theorem `HasMFDerivAt.hasMFDerivWithinAt` / 定理 `HasMFDerivAt.hasMFDerivWithinAt`

English:
theorem HasMFDerivAt.hasMFDerivWithinAt
  given: (h : HasMFDerivAt% f x f')
  statement: HasMFDerivAt[s] f x f'
  proof: ⟨ContinuousAt.continuousWithinAt h.1, HasFDerivWithinAt.mono h.2 inter_subset_right⟩

中文:
定理 HasMFDerivAt.hasMFDerivWithinAt
  条件: (h : HasMFDerivAt% f x f')
  结论: HasMFDerivAt[s] f x f'
  证明: ⟨ContinuousAt.continuousWithinAt h.1, HasFDerivWithinAt.mono h.2 inter_subset_right⟩

Depends on / 依赖: ContinuousAt, ContinuousAt.continuousWithinAt, HasFDerivWithinAt, HasFDerivWithinAt.mono, continuousWithinAt, inter_subset_right
-/
theorem HasMFDerivAt.hasMFDerivWithinAt (h : HasMFDerivAt% f x f') : HasMFDerivAt[s] f x f' :=
  ⟨ContinuousAt.continuousWithinAt h.1, HasFDerivWithinAt.mono h.2 inter_subset_right⟩

/--
theorem `HasMFDerivWithinAt.mdifferentiableWithinAt` / 定理 `HasMFDerivWithinAt.mdifferentiableWithinAt`

English:
theorem HasMFDerivWithinAt.mdifferentiableWithinAt
  given: (h : HasMFDerivAt[s] f x f')
  statement: MDiffAt[s] f x
  proof: ⟨h.1, ⟨f', h.2⟩⟩

中文:
定理 HasMFDerivWithinAt.mdifferentiableWithinAt
  条件: (h : HasMFDerivAt[s] f x f')
  结论: MDiffAt[s] f x
  证明: ⟨h.1, ⟨f', h.2⟩⟩
-/
theorem HasMFDerivWithinAt.mdifferentiableWithinAt (h : HasMFDerivAt[s] f x f') : MDiffAt[s] f x :=
  ⟨h.1, ⟨f', h.2⟩⟩

/--
theorem `HasMFDerivAt.mdifferentiableAt` / 定理 `HasMFDerivAt.mdifferentiableAt`

English:
theorem HasMFDerivAt.mdifferentiableAt
  given: (h : HasMFDerivAt% f x f')
  statement: MDiffAt f x
  proof: by
  rw [mdifferentiableAt_iff]
  exact ⟨h.1, ⟨f', h.2⟩⟩

@[simp, mfld_simps]

中文:
定理 HasMFDerivAt.mdifferentiableAt
  条件: (h : HasMFDerivAt% f x f')
  结论: MDiffAt f x
  证明: by
  rw [mdifferentiableAt_iff]
  exact ⟨h.1, ⟨f', h.2⟩⟩

@[simp, mfld_simps]

Depends on / 依赖: mdifferentiableAt_iff
-/
theorem HasMFDerivAt.mdifferentiableAt (h : HasMFDerivAt% f x f') : MDiffAt f x := by
  rw [mdifferentiableAt_iff]
  exact ⟨h.1, ⟨f', h.2⟩⟩

@[simp, mfld_simps]
/--
theorem `hasMFDerivWithinAt_univ` / 定理 `hasMFDerivWithinAt_univ`

English:
theorem hasMFDerivWithinAt_univ
  statement: HasMFDerivAt[univ] f x f' ↔ HasMFDerivAt% f x f'
  proof: by
  simp only [HasMFDerivWithinAt, HasMFDerivAt, continuousWithinAt_univ, mfld_simps]

中文:
定理 hasMFDerivWithinAt_univ
  结论: HasMFDerivAt[univ] f x f' ↔ HasMFDerivAt% f x f'
  证明: by
  simp only [HasMFDerivWithinAt, HasMFDerivAt, continuousWithinAt_univ, mfld_simps]

Depends on / 依赖: HasMFDerivAt, HasMFDerivWithinAt, continuousWithinAt_univ, mfld_simps
-/
theorem hasMFDerivWithinAt_univ : HasMFDerivAt[univ] f x f' ↔ HasMFDerivAt% f x f' := by
  simp only [HasMFDerivWithinAt, HasMFDerivAt, continuousWithinAt_univ, mfld_simps]

/--
theorem `hasMFDerivAt_unique` / 定理 `hasMFDerivAt_unique`

English:
theorem hasMFDerivAt_unique
  given: (h₀ : HasMFDerivAt% f x f₀') (h₁ : HasMFDerivAt% f x f₁')
  proof: by
  rw [← hasMFDerivWithinAt_univ] at h₀ h₁
  exact (uniqueMDiffWithinAt_univ I).eq h₀ h₁

中文:
定理 hasMFDerivAt_unique
  条件: (h₀ : HasMFDerivAt% f x f₀') (h₁ : HasMFDerivAt% f x f₁')
  证明: by
  rw [← hasMFDerivWithinAt_univ] at h₀ h₁
  exact (uniqueMDiffWithinAt_univ I).eq h₀ h₁

Depends on / 依赖: hasMFDerivWithinAt_univ, uniqueMDiffWithinAt_univ
-/
theorem hasMFDerivAt_unique (h₀ : HasMFDerivAt% f x f₀') (h₁ : HasMFDerivAt% f x f₁') :
    f₀' = f₁' := by
  rw [← hasMFDerivWithinAt_univ] at h₀ h₁
  exact (uniqueMDiffWithinAt_univ I).eq h₀ h₁

set_option backward.isDefEq.respectTransparency false in
/--
theorem `hasMFDerivWithinAt_inter'` / 定理 `hasMFDerivWithinAt_inter'`

English:
theorem hasMFDerivWithinAt_inter'
  given: (h : t in 𝓝[s] x)
  proof: by
  rw [HasMFDerivWithinAt]; rw [HasMFDerivWithinAt]; rw [extChartAt_preimage_inter_eq]; rw [hasFDerivWithinAt_inter']; rw [continuousWithinAt_inter' h]
  exact extChartAt_preimage_mem_nhdsWithin h

中文:
定理 hasMFDerivWithinAt_inter'
  条件: (h : t in 𝓝[s] x)
  证明: by
  rw [HasMFDerivWithinAt]; rw [HasMFDerivWithinAt]; rw [extChartAt_preimage_inter_eq]; rw [hasFDerivWithinAt_inter']; rw [continuousWithinAt_inter' h]
  exact extChartAt_preimage_mem_nhdsWithin h

Depends on / 依赖: HasMFDerivWithinAt, continuousWithinAt_inter, extChartAt_preimage_inter_eq, extChartAt_preimage_mem_nhdsWithin, hasFDerivWithinAt_inter
-/
theorem hasMFDerivWithinAt_inter' (h : t in 𝓝[s] x) :
    HasMFDerivAt[s inter t] f x f' ↔ HasMFDerivAt[s] f x f' := by
  rw [HasMFDerivWithinAt]; rw [HasMFDerivWithinAt]; rw [extChartAt_preimage_inter_eq]; rw [hasFDerivWithinAt_inter']; rw [continuousWithinAt_inter' h]
  exact extChartAt_preimage_mem_nhdsWithin h

set_option backward.isDefEq.respectTransparency false in
/--
theorem `hasMFDerivWithinAt_inter` / 定理 `hasMFDerivWithinAt_inter`

English:
theorem hasMFDerivWithinAt_inter
  given: (h : t in 𝓝 x)
  proof: by
  rw [HasMFDerivWithinAt]; rw [HasMFDerivWithinAt]; rw [extChartAt_preimage_inter_eq]; rw [hasFDerivWithinAt_inter]; rw [continuousWithinAt_inter h]
  exact extChartAt_preimage_mem_nhds h

中文:
定理 hasMFDerivWithinAt_inter
  条件: (h : t in 𝓝 x)
  证明: by
  rw [HasMFDerivWithinAt]; rw [HasMFDerivWithinAt]; rw [extChartAt_preimage_inter_eq]; rw [hasFDerivWithinAt_inter]; rw [continuousWithinAt_inter h]
  exact extChartAt_preimage_mem_nhds h

Depends on / 依赖: HasMFDerivWithinAt, continuousWithinAt_inter, extChartAt_preimage_inter_eq, extChartAt_preimage_mem_nhds, hasFDerivWithinAt_inter
-/
theorem hasMFDerivWithinAt_inter (h : t in 𝓝 x) :
    HasMFDerivAt[s inter t] f x f' ↔ HasMFDerivAt[s] f x f' := by
  rw [HasMFDerivWithinAt]; rw [HasMFDerivWithinAt]; rw [extChartAt_preimage_inter_eq]; rw [hasFDerivWithinAt_inter]; rw [continuousWithinAt_inter h]
  exact extChartAt_preimage_mem_nhds h

/--
theorem `HasMFDerivWithinAt.union` / 定理 `HasMFDerivWithinAt.union`

English:
theorem HasMFDerivWithinAt.union
  given: (hs : HasMFDerivAt[s] f x f') (ht : HasMFDerivAt[t] f x f')
  proof: by
  constructor
  · exact ContinuousWithinAt.union hs.1 ht.1
  · convert! HasFDerivWithinAt.union hs.2 ht.2 using 1
    simp only [union_inter_distrib_right, preimage_union]

中文:
定理 HasMFDerivWithinAt.union
  条件: (hs : HasMFDerivAt[s] f x f') (ht : HasMFDerivAt[t] f x f')
  证明: by
  constructor
  · exact ContinuousWithinAt.union hs.1 ht.1
  · convert! HasFDerivWithinAt.union hs.2 ht.2 using 1
    simp only [union_inter_distrib_right, preimage_union]

Depends on / 依赖: ContinuousWithinAt, ContinuousWithinAt.union, HasFDerivWithinAt, HasFDerivWithinAt.union, convert, preimage_union, union_inter_distrib_right
-/
theorem HasMFDerivWithinAt.union (hs : HasMFDerivAt[s] f x f') (ht : HasMFDerivAt[t] f x f') :
    HasMFDerivAt[s union t] f x f' := by
  constructor
  · exact ContinuousWithinAt.union hs.1 ht.1
  · convert! HasFDerivWithinAt.union hs.2 ht.2 using 1
    simp only [union_inter_distrib_right, preimage_union]

/--
theorem `HasMFDerivWithinAt.mono_of_mem_nhdsWithin` / 定理 `HasMFDerivWithinAt.mono_of_mem_nhdsWithin`

English:
theorem HasMFDerivWithinAt.mono_of_mem_nhdsWithin
  given: (h : HasMFDerivAt[s] f x f') (ht : s in 𝓝[t] x)
  proof: (hasMFDerivWithinAt_inter' ht).1 (h.mono inter_subset_right)

中文:
定理 HasMFDerivWithinAt.mono_of_mem_nhdsWithin
  条件: (h : HasMFDerivAt[s] f x f') (ht : s in 𝓝[t] x)
  证明: (hasMFDerivWithinAt_inter' ht).1 (h.mono inter_subset_right)

Depends on / 依赖: h.mono, hasMFDerivWithinAt_inter, inter_subset_right
-/
theorem HasMFDerivWithinAt.mono_of_mem_nhdsWithin (h : HasMFDerivAt[s] f x f') (ht : s in 𝓝[t] x) :
    HasMFDerivAt[t] f x f' :=
  (hasMFDerivWithinAt_inter' ht).1 (h.mono inter_subset_right)

/--
theorem `HasMFDerivWithinAt.hasMFDerivAt` / 定理 `HasMFDerivWithinAt.hasMFDerivAt`

English:
theorem HasMFDerivWithinAt.hasMFDerivAt
  given: (h : HasMFDerivAt[s] f x f') (hs : s in 𝓝 x)
  proof: by
  rwa [← univ_inter s, hasMFDerivWithinAt_inter hs, hasMFDerivWithinAt_univ] at h

中文:
定理 HasMFDerivWithinAt.hasMFDerivAt
  条件: (h : HasMFDerivAt[s] f x f') (hs : s in 𝓝 x)
  证明: by
  rwa [← univ_inter s, hasMFDerivWithinAt_inter hs, hasMFDerivWithinAt_univ] at h

Depends on / 依赖: hasMFDerivWithinAt_inter, hasMFDerivWithinAt_univ, univ_inter
-/
theorem HasMFDerivWithinAt.hasMFDerivAt (h : HasMFDerivAt[s] f x f') (hs : s in 𝓝 x) :
    HasMFDerivAt% f x f' := by
  rwa [← univ_inter s, hasMFDerivWithinAt_inter hs, hasMFDerivWithinAt_univ] at h

/--
theorem `MDifferentiableWithinAt.hasMFDerivWithinAt` / 定理 `MDifferentiableWithinAt.hasMFDerivWithinAt`

English:
theorem MDifferentiableWithinAt.hasMFDerivWithinAt
  given: (h : MDiffAt[s] f x)
  proof: by
  refine ⟨h.1, ?_⟩
  simp only [mfderivWithin, h, mfld_simps]
  exact DifferentiableWithinAt.hasFDerivWithinAt h.2

中文:
定理 MDifferentiableWithinAt.hasMFDerivWithinAt
  条件: (h : MDiffAt[s] f x)
  证明: by
  refine ⟨h.1, ?_⟩
  simp only [mfderivWithin, h, mfld_simps]
  exact DifferentiableWithinAt.hasFDerivWithinAt h.2

Depends on / 依赖: DifferentiableWithinAt, DifferentiableWithinAt.hasFDerivWithinAt, hasFDerivWithinAt, mfderivWithin, mfld_simps
-/
theorem MDifferentiableWithinAt.hasMFDerivWithinAt (h : MDiffAt[s] f x) :
    HasMFDerivAt[s] f x (mfderiv[s] f x) := by
  refine ⟨h.1, ?_⟩
  simp only [mfderivWithin, h, mfld_simps]
  exact DifferentiableWithinAt.hasFDerivWithinAt h.2

/--
theorem `mdifferentiableWithinAt_iff_exists_hasMFDerivWithinAt` / 定理 `mdifferentiableWithinAt_iff_exists_hasMFDerivWithinAt`

English:
theorem mdifferentiableWithinAt_iff_exists_hasMFDerivWithinAt
  proof: by
  refine ⟨fun h => ⟨mfderiv[s] f x, h.hasMFDerivWithinAt⟩, ?_⟩
  rintro ⟨f', hf'⟩
  exact hf'.mdifferentiableWithinAt

中文:
定理 mdifferentiableWithinAt_iff_存在_hasMFDerivWithinAt
  证明: by
  refine ⟨fun h => ⟨mfderiv[s] f x, h.hasMFDerivWithinAt⟩, ?_⟩
  rintro ⟨f', hf'⟩
  exact hf'.mdifferentiableWithinAt

Depends on / 依赖: h.hasMFDerivWithinAt, hasMFDerivWithinAt, mdifferentiableWithinAt, mfderiv
-/
theorem mdifferentiableWithinAt_iff_exists_hasMFDerivWithinAt :
    MDiffAt[s] f x ↔ exists f', HasMFDerivWithinAt I I' f s x f' := by
  refine ⟨fun h => ⟨mfderiv[s] f x, h.hasMFDerivWithinAt⟩, ?_⟩
  rintro ⟨f', hf'⟩
  exact hf'.mdifferentiableWithinAt

/--
theorem `MDifferentiableWithinAt.mono_of_mem_nhdsWithin` / 定理 `MDifferentiableWithinAt.mono_of_mem_nhdsWithin`

English:
theorem MDifferentiableWithinAt.mono_of_mem_nhdsWithin
  statement: (h : MDiffAt[s] f x) {t : Set M}
  proof: (h.hasMFDerivWithinAt.mono_of_mem_nhdsWithin hst).mdifferentiableWithinAt

中文:
定理 MDifferentiableWithinAt.mono_of_mem_nhdsWithin
  结论: (h : MDiffAt[s] f x) {t : 集合 M}
  证明: (h.hasMFDerivWithinAt.mono_of_mem_nhdsWithin hst).mdifferentiableWithinAt

Depends on / 依赖: h.hasMFDerivWithinAt.mono_of_mem_nhdsWithin, hasMFDerivWithinAt, mdifferentiableWithinAt, mono_of_mem_nhdsWithin
-/
theorem MDifferentiableWithinAt.mono_of_mem_nhdsWithin (h : MDiffAt[s] f x) {t : Set M}
    (hst : s in 𝓝[t] x) : MDiffAt[t] f x :=
  (h.hasMFDerivWithinAt.mono_of_mem_nhdsWithin hst).mdifferentiableWithinAt

/--
theorem `MDifferentiableWithinAt.congr_nhds` / 定理 `MDifferentiableWithinAt.congr_nhds`

English:
theorem MDifferentiableWithinAt.congr_nhds
  statement: (h : MDiffAt[s] f x) {t : Set M}
  proof: h.mono_of_mem_nhdsWithin hst ▸ self_mem_nhdsWithin

中文:
定理 MDifferentiableWithinAt.congr_nhds
  结论: (h : MDiffAt[s] f x) {t : 集合 M}
  证明: h.mono_of_mem_nhdsWithin hst ▸ self_mem_nhdsWithin

Depends on / 依赖: h.mono_of_mem_nhdsWithin, mono_of_mem_nhdsWithin, self_mem_nhdsWithin
-/
theorem MDifferentiableWithinAt.congr_nhds (h : MDiffAt[s] f x) {t : Set M}
    (hst : 𝓝[s] x = 𝓝[t] x) : MDiffAt[t] f x :=
h.mono_of_mem_nhdsWithin hst ▸ self_mem_nhdsWithin

/--
theorem `mdifferentiableWithinAt_congr_nhds` / 定理 `mdifferentiableWithinAt_congr_nhds`

English:
theorem mdifferentiableWithinAt_congr_nhds
  given: {t : Set M} (hst : 𝓝[s] x = 𝓝[t] x)
  proof: ⟨fun h => h.congr_nhds hst, fun h => h.congr_nhds hst.symm⟩

中文:
定理 mdifferentiableWithinAt_congr_nhds
  条件: {t : 集合 M} (hst : 𝓝[s] x = 𝓝[t] x)
  证明: ⟨fun h => h.congr_nhds hst, fun h => h.congr_nhds hst.symm⟩

Depends on / 依赖: congr_nhds, h.congr_nhds, hst.symm
-/
theorem mdifferentiableWithinAt_congr_nhds {t : Set M} (hst : 𝓝[s] x = 𝓝[t] x) :
    MDiffAt[s] f x ↔ MDiffAt[t] f x :=
  ⟨fun h => h.congr_nhds hst, fun h => h.congr_nhds hst.symm⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `MDifferentiableWithinAt.mfderivWithin` / 定理 `MDifferentiableWithinAt.mfderivWithin`

English:
theorem MDifferentiableWithinAt.mfderivWithin
  given: (h : MDiffAt[s] f x)
  proof: by
  simp only [mfderivWithin, h, if_pos]

中文:
定理 MDifferentiableWithinAt.mfderivWithin
  条件: (h : MDiffAt[s] f x)
  证明: by
  simp only [mfderivWithin, h, if_pos]
-/
protected theorem MDifferentiableWithinAt.mfderivWithin (h : MDiffAt[s] f x) :
    mfderiv[s] f x =
      fderivWithin 𝕜 (writtenInExtChartAt I I' x f :) ((extChartAt I x).symm ⁻¹' s inter range I)
        ((extChartAt I x) x) := by
  simp only [mfderivWithin, h, if_pos]

/--
theorem `MDifferentiableAt.hasMFDerivAt` / 定理 `MDifferentiableAt.hasMFDerivAt`

English:
theorem MDifferentiableAt.hasMFDerivAt
  given: (h : MDiffAt f x)
  statement: HasMFDerivAt% f x (mfderiv% f x)
  proof: by
  refine ⟨h.continuousAt, ?_⟩
  simp only [mfderiv, h, mfld_simps]
  exact DifferentiableWithinAt.hasFDerivWithinAt h.differentiableWithinAt_writtenInExtChartAt

中文:
定理 MDifferentiableAt.hasMFDerivAt
  条件: (h : MDiffAt f x)
  结论: HasMFDerivAt% f x (mfderiv% f x)
  证明: by
  refine ⟨h.continuousAt, ?_⟩
  simp only [mfderiv, h, mfld_simps]
  exact DifferentiableWithinAt.hasFDerivWithinAt h.differentiableWithinAt_writtenInExtChartAt

Depends on / 依赖: DifferentiableWithinAt, DifferentiableWithinAt.hasFDerivWithinAt, continuousAt, differentiableWithinAt_writtenInExtChartAt, h.continuousAt, h.differentiableWithinAt_writtenInExtChartAt, hasFDerivWithinAt, mfderiv, mfld_simps
-/
theorem MDifferentiableAt.hasMFDerivAt (h : MDiffAt f x) : HasMFDerivAt% f x (mfderiv% f x) := by
  refine ⟨h.continuousAt, ?_⟩
  simp only [mfderiv, h, mfld_simps]
  exact DifferentiableWithinAt.hasFDerivWithinAt h.differentiableWithinAt_writtenInExtChartAt

set_option backward.isDefEq.respectTransparency false in
/--
theorem `MDifferentiableAt.mfderiv` / 定理 `MDifferentiableAt.mfderiv`

English:
theorem MDifferentiableAt.mfderiv
  given: (h : MDiffAt f x)
  proof: by
  simp only [mfderiv, h, if_pos]

中文:
定理 MDifferentiableAt.mfderiv
  条件: (h : MDiffAt f x)
  证明: by
  simp only [mfderiv, h, if_pos]
-/
protected theorem MDifferentiableAt.mfderiv (h : MDiffAt f x) :
    mfderiv% f x =
      fderivWithin 𝕜 (writtenInExtChartAt I I' x f :) (range I) ((extChartAt I x) x) := by
  simp only [mfderiv, h, if_pos]

/--
theorem `HasMFDerivAt.mfderiv` / 定理 `HasMFDerivAt.mfderiv`

English:
theorem HasMFDerivAt.mfderiv
  given: (h : HasMFDerivAt% f x f')
  statement: mfderiv% f x = f'
  proof: (hasMFDerivAt_unique h h.mdifferentiableAt.hasMFDerivAt).symm

中文:
定理 HasMFDerivAt.mfderiv
  条件: (h : HasMFDerivAt% f x f')
  结论: mfderiv% f x = f'
  证明: (hasMFDerivAt_unique h h.mdifferentiableAt.hasMFDerivAt).symm
-/
protected theorem HasMFDerivAt.mfderiv (h : HasMFDerivAt% f x f') : mfderiv% f x = f' :=
  (hasMFDerivAt_unique h h.mdifferentiableAt.hasMFDerivAt).symm

/--
theorem `HasMFDerivWithinAt.mfderivWithin` / 定理 `HasMFDerivWithinAt.mfderivWithin`

English:
theorem HasMFDerivWithinAt.mfderivWithin
  statement: (h : HasMFDerivAt[s] f x f')
  proof: by
  ext
  rw [hxs.eq h h.mdifferentiableWithinAt.hasMFDerivWithinAt]

中文:
定理 HasMFDerivWithinAt.mfderivWithin
  结论: (h : HasMFDerivAt[s] f x f')
  证明: by
  ext
  rw [hxs.eq h h.mdifferentiableWithinAt.hasMFDerivWithinAt]
-/
protected theorem HasMFDerivWithinAt.mfderivWithin (h : HasMFDerivAt[s] f x f')
    (hxs : UniqueMDiffAt[s] x) : mfderiv[s] f x = f' := by
  ext
  rw [hxs.eq h h.mdifferentiableWithinAt.hasMFDerivWithinAt]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `HasMFDerivWithinAt.mfderivWithin_eq_zero` / 定理 `HasMFDerivWithinAt.mfderivWithin_eq_zero`

English:
theorem HasMFDerivWithinAt.mfderivWithin_eq_zero
  given: (h : HasMFDerivWithinAt I I' f s x 0)
  proof: by
  simp only [mfld_simps, mfderivWithin, h.mdifferentiableWithinAt, ↓reduceIte]
  simp only [HasMFDerivWithinAt, mfld_simps] at h
  rw [fderivWithin]; rw [if_pos]
  exact h.2

中文:
定理 HasMFDerivWithinAt.mfderivWithin_eq_zero
  条件: (h : HasMFDerivWithinAt I I' f s x 0)
  证明: by
  simp only [mfld_simps, mfderivWithin, h.mdifferentiableWithinAt, ↓reduceIte]
  simp only [HasMFDerivWithinAt, mfld_simps] at h
  rw [fderivWithin]; rw [if_pos]
  exact h.2

Depends on / 依赖: HasMFDerivWithinAt, fderivWithin, h.mdifferentiableWithinAt, if_pos, mdifferentiableWithinAt, mfderivWithin, mfld_simps, reduceIte
-/
theorem HasMFDerivWithinAt.mfderivWithin_eq_zero (h : HasMFDerivWithinAt I I' f s x 0) :
    mfderiv[s] f x = 0 := by
  simp only [mfld_simps, mfderivWithin, h.mdifferentiableWithinAt, ↓reduceIte]
  simp only [HasMFDerivWithinAt, mfld_simps] at h
  rw [fderivWithin]; rw [if_pos]
  exact h.2

/--
theorem `MDifferentiable.mfderivWithin` / 定理 `MDifferentiable.mfderivWithin`

English:
theorem MDifferentiable.mfderivWithin
  given: (h : MDiffAt f x) (hxs : UniqueMDiffAt[s] x)
  proof: by
  apply HasMFDerivWithinAt.mfderivWithin _ hxs
  exact h.hasMFDerivAt.hasMFDerivWithinAt

中文:
定理 MDifferentiable.mfderivWithin
  条件: (h : MDiffAt f x) (hxs : UniqueMDiffAt[s] x)
  证明: by
  apply HasMFDerivWithinAt.mfderivWithin _ hxs
  exact h.hasMFDerivAt.hasMFDerivWithinAt

Depends on / 依赖: HasMFDerivWithinAt, HasMFDerivWithinAt.mfderivWithin, h.hasMFDerivAt.hasMFDerivWithinAt, hasMFDerivAt, hasMFDerivWithinAt, mfderivWithin
-/
theorem MDifferentiable.mfderivWithin (h : MDiffAt f x) (hxs : UniqueMDiffAt[s] x) :
    mfderiv[s] f x = mfderiv% f x := by
  apply HasMFDerivWithinAt.mfderivWithin _ hxs
  exact h.hasMFDerivAt.hasMFDerivWithinAt

/--
theorem `mfderivWithin_subset` / 定理 `mfderivWithin_subset`

English:
theorem mfderivWithin_subset
  given: (st : s subseteq t) (hs : UniqueMDiffAt[s] x) (h : MDiffAt[t] f x)
  proof: ((MDifferentiableWithinAt.hasMFDerivWithinAt h).mono st).mfderivWithin hs

中文:
定理 mfderivWithin_subset
  条件: (st : s subseteq t) (hs : UniqueMDiffAt[s] x) (h : MDiffAt[t] f x)
  证明: ((MDifferentiableWithinAt.hasMFDerivWithinAt h).mono st).mfderivWithin hs

Depends on / 依赖: MDifferentiableWithinAt, MDifferentiableWithinAt.hasMFDerivWithinAt, hasMFDerivWithinAt, mfderivWithin
-/
theorem mfderivWithin_subset (st : s subseteq t) (hs : UniqueMDiffAt[s] x) (h : MDiffAt[t] f x) :
    mfderiv[s] f x = mfderiv[t] f x :=
  ((MDifferentiableWithinAt.hasMFDerivWithinAt h).mono st).mfderivWithin hs

/--
theorem `mfderivWithin_inter` / 定理 `mfderivWithin_inter`

English:
theorem mfderivWithin_inter
  given: (ht : t in 𝓝 x)
  statement: mfderiv[s inter t] f x = mfderiv[s] f x
  proof: by
  rw [mfderivWithin]; rw [mfderivWithin]; rw [extChartAt_preimage_inter_eq]; rw [mdifferentiableWithinAt_inter ht]; rw [fderivWithin_inter (extChartAt_preimage_mem_nhds ht)]

中文:
定理 mfderivWithin_inter
  条件: (ht : t in 𝓝 x)
  结论: mfderiv[s inter t] f x = mfderiv[s] f x
  证明: by
  rw [mfderivWithin]; rw [mfderivWithin]; rw [extChartAt_preimage_inter_eq]; rw [mdifferentiableWithinAt_inter ht]; rw [fderivWithin_inter (extChartAt_preimage_mem_nhds ht)]

Depends on / 依赖: extChartAt_preimage_inter_eq, extChartAt_preimage_mem_nhds, fderivWithin_inter, mdifferentiableWithinAt_inter, mfderivWithin
-/
theorem mfderivWithin_inter (ht : t in 𝓝 x) : mfderiv[s inter t] f x = mfderiv[s] f x := by
  rw [mfderivWithin]; rw [mfderivWithin]; rw [extChartAt_preimage_inter_eq]; rw [mdifferentiableWithinAt_inter ht]; rw [fderivWithin_inter (extChartAt_preimage_mem_nhds ht)]

/--
theorem `mfderivWithin_of_mem_nhds` / 定理 `mfderivWithin_of_mem_nhds`

English:
theorem mfderivWithin_of_mem_nhds
  given: (h : s in 𝓝 x)
  statement: mfderiv[s] f x = mfderiv% f x
  proof: by
  rw [← mfderivWithin_univ]; rw [← univ_inter s]; rw [mfderivWithin_inter h]

中文:
定理 mfderivWithin_of_mem_nhds
  条件: (h : s in 𝓝 x)
  结论: mfderiv[s] f x = mfderiv% f x
  证明: by
  rw [← mfderivWithin_univ]; rw [← univ_inter s]; rw [mfderivWithin_inter h]

Depends on / 依赖: mfderivWithin_inter, mfderivWithin_univ, univ_inter
-/
theorem mfderivWithin_of_mem_nhds (h : s in 𝓝 x) : mfderiv[s] f x = mfderiv% f x := by
  rw [← mfderivWithin_univ]; rw [← univ_inter s]; rw [mfderivWithin_inter h]

/--
lemma `mfderivWithin_of_isOpen` / 引理 `mfderivWithin_of_isOpen`

English:
lemma mfderivWithin_of_isOpen
  given: (hs : IsOpen s) (hx : x in s)
  statement: mfderiv[s] f x = mfderiv% f x
  proof: mfderivWithin_of_mem_nhds (hs.mem_nhds hx)

中文:
引理 mfderivWithin_of_isOpen
  条件: (hs : 是开集 s) (hx : x in s)
  结论: mfderiv[s] f x = mfderiv% f x
  证明: mfderivWithin_of_mem_nhds (hs.mem_nhds hx)

Depends on / 依赖: hs.mem_nhds, mem_nhds, mfderivWithin_of_mem_nhds
-/
lemma mfderivWithin_of_isOpen (hs : IsOpen s) (hx : x in s) : mfderiv[s] f x = mfderiv% f x :=
  mfderivWithin_of_mem_nhds (hs.mem_nhds hx)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `hasMFDerivWithinAt_insert` / 定理 `hasMFDerivWithinAt_insert`

English:
theorem hasMFDerivWithinAt_insert
  given: {y : M}
  proof: by
  have : T1Space M := I.t1Space M
refine ⟨fun h => h.mono subset_insert y s, fun hf => ?_⟩
  rcases eq_or_ne x y with rfl | h
  · rw [HasMFDerivWithinAt] at hf ⊢
    refine ⟨hf.1.insert, ?_⟩
    have : (extChartAt I x).target in
        𝓝[(extChartAt I x).symm ⁻¹' insert x s inter range I] (extChartAt I x) x :=
      nhdsWithin_mono _ inter_subset_right (extChartAt_target_mem_nhdsWithin x)
    rw [← hasFDerivWithinAt_inter' this]
    apply hf.2.insert.mono
    rintro z ⟨⟨hz, h2z⟩, h'z⟩
    simp only [mem_inter_iff, mem_preimage, mem_insert_iff, mem_range] at hz h2z ⊢
    rcases hz with xz | h'z
    · left
      have : x in (extChartAt I x).source := mem_extChartAt_source x
      exact (((extChartAt I x).eq_symm_apply this h'z).1 xz.symm).symm
    · exact Or.inr ⟨h'z, h2z⟩
  · apply hf.mono_of_mem_nhdsWithin ?_
    simp_rw [nhdsWithin_insert_of_ne h, self_mem_nhdsWithin]

alias ⟨HasMFDerivWithinAt.of_insert, HasMFDerivWithinAt.insert'⟩ := hasMFDerivWithinAt_insert

中文:
定理 hasMFDerivWithinAt_insert
  条件: {y : M}
  证明: by
  have : T1Space M := I.t1Space M
refine ⟨fun h => h.mono subset_insert y s, fun hf => ?_⟩
  rcases eq_or_ne x y with rfl | h
  · rw [HasMFDerivWithinAt] at hf ⊢
    refine ⟨hf.1.insert, ?_⟩
    have : (extChartAt I x).target in
        𝓝[(extChartAt I x).symm ⁻¹' insert x s inter range I] (extChartAt I x) x :=
      nhdsWithin_mono _ inter_subset_right (extChartAt_target_mem_nhdsWithin x)
    rw [← hasFDerivWithinAt_inter' this]
    apply hf.2.insert.mono
    rintro z ⟨⟨hz, h2z⟩, h'z⟩
    simp only [mem_inter_iff, mem_preimage, mem_insert_iff, mem_range] at hz h2z ⊢
    rcases hz with xz | h'z
    · left
      have : x in (extChartAt I x).source := mem_extChartAt_source x
      exact (((extChartAt I x).eq_symm_apply this h'z).1 xz.symm).symm
    · exact Or.inr ⟨h'z, h2z⟩
  · apply hf.mono_of_mem_nhdsWithin ?_
    simp_rw [nhdsWithin_insert_of_ne h, self_mem_nhdsWithin]

alias ⟨HasMFDerivWithinAt.of_insert, HasMFDerivWithinAt.insert'⟩ := hasMFDerivWithinAt_insert

Depends on / 依赖: HasMFDerivWithinAt, I.t1Space, T1Space, eq_or_ne, extChartAt, extChartAt_target_mem_nhdsWithin, h.mono, hasFDerivWithinAt_inter, insert, insert.mono, inter_subset_right, mem_in, mem_inter_iff, mem_preimage, nhdsWithin_mono, subset_insert, t1Space, target
-/
theorem hasMFDerivWithinAt_insert {y : M} :
    HasMFDerivAt[insert y s] f x f' ↔ HasMFDerivAt[s] f x f' := by
  have : T1Space M := I.t1Space M
refine ⟨fun h => h.mono subset_insert y s, fun hf => ?_⟩
  rcases eq_or_ne x y with rfl | h
  · rw [HasMFDerivWithinAt] at hf ⊢
    refine ⟨hf.1.insert, ?_⟩
    have : (extChartAt I x).target in
        𝓝[(extChartAt I x).symm ⁻¹' insert x s inter range I] (extChartAt I x) x :=
      nhdsWithin_mono _ inter_subset_right (extChartAt_target_mem_nhdsWithin x)
    rw [← hasFDerivWithinAt_inter' this]
    apply hf.2.insert.mono
    rintro z ⟨⟨hz, h2z⟩, h'z⟩
    simp only [mem_inter_iff, mem_preimage, mem_insert_iff, mem_range] at hz h2z ⊢
    rcases hz with xz | h'z
    · left
      have : x in (extChartAt I x).source := mem_extChartAt_source x
      exact (((extChartAt I x).eq_symm_apply this h'z).1 xz.symm).symm
    · exact Or.inr ⟨h'z, h2z⟩
  · apply hf.mono_of_mem_nhdsWithin ?_
    simp_rw [nhdsWithin_insert_of_ne h, self_mem_nhdsWithin]

alias ⟨HasMFDerivWithinAt.of_insert, HasMFDerivWithinAt.insert'⟩ := hasMFDerivWithinAt_insert

/--
theorem `HasMFDerivWithinAt.insert` / 定理 `HasMFDerivWithinAt.insert`

English:
theorem HasMFDerivWithinAt.insert
  given: (h : HasMFDerivAt[s] f x f')
  proof: h.insert'

中文:
定理 HasMFDerivWithinAt.insert
  条件: (h : HasMFDerivAt[s] f x f')
  证明: h.insert'
-/
protected theorem HasMFDerivWithinAt.insert (h : HasMFDerivAt[s] f x f') :
    HasMFDerivAt[insert x s] f x f' :=
  h.insert'

/--
theorem `hasMFDerivWithinAt_sdiff_singleton` / 定理 `hasMFDerivWithinAt_sdiff_singleton`

English:
theorem hasMFDerivWithinAt_sdiff_singleton
  given: (y : M)
  proof: by
  rw [← hasMFDerivWithinAt_insert]; rw [insert_sdiff_singleton]; rw [hasMFDerivWithinAt_insert]

@[deprecated (since := "2026-06-03")]
alias hasMFDerivWithinAt_diff_singleton := hasMFDerivWithinAt_sdiff_singleton

中文:
定理 hasMFDerivWithinAt_sdiff_singleton
  条件: (y : M)
  证明: by
  rw [← hasMFDerivWithinAt_insert]; rw [insert_sdiff_singleton]; rw [hasMFDerivWithinAt_insert]

@[deprecated (since := "2026-06-03")]
alias hasMFDerivWithinAt_diff_singleton := hasMFDerivWithinAt_sdiff_singleton

Depends on / 依赖: hasMFDerivWithinAt_insert, insert_sdiff_singleton
-/
theorem hasMFDerivWithinAt_sdiff_singleton (y : M) :
    HasMFDerivAt[s \ {y}] f x f' ↔ HasMFDerivAt[s] f x f' := by
  rw [← hasMFDerivWithinAt_insert]; rw [insert_sdiff_singleton]; rw [hasMFDerivWithinAt_insert]

@[deprecated (since := "2026-06-03")]
alias hasMFDerivWithinAt_diff_singleton := hasMFDerivWithinAt_sdiff_singleton

/--
theorem `mfderivWithin_eq_mfderiv` / 定理 `mfderivWithin_eq_mfderiv`

English:
theorem mfderivWithin_eq_mfderiv
  given: (hs : UniqueMDiffAt[s] x) (h : MDiffAt f x)
  proof: by
  rw [← mfderivWithin_univ]
  exact mfderivWithin_subset (subset_univ _) hs h.mdifferentiableWithinAt

中文:
定理 mfderivWithin_eq_mfderiv
  条件: (hs : UniqueMDiffAt[s] x) (h : MDiffAt f x)
  证明: by
  rw [← mfderivWithin_univ]
  exact mfderivWithin_subset (subset_univ _) hs h.mdifferentiableWithinAt

Depends on / 依赖: h.mdifferentiableWithinAt, mdifferentiableWithinAt, mfderivWithin_subset, mfderivWithin_univ, subset_univ
-/
theorem mfderivWithin_eq_mfderiv (hs : UniqueMDiffAt[s] x) (h : MDiffAt f x) :
    mfderiv[s] f x = mfderiv% f x := by
  rw [← mfderivWithin_univ]
  exact mfderivWithin_subset (subset_univ _) hs h.mdifferentiableWithinAt

/--
theorem `mdifferentiableWithinAt_insert_self` / 定理 `mdifferentiableWithinAt_insert_self`

English:
theorem mdifferentiableWithinAt_insert_self
  statement: MDiffAt[insert x s] f x ↔ MDiffAt[s] f x
  proof: ⟨fun h => h.mono (subset_insert x s), fun h => h.hasMFDerivWithinAt.insert.mdifferentiableWithinAt⟩

中文:
定理 mdifferentiableWithinAt_insert_self
  结论: MDiffAt[insert x s] f x ↔ MDiffAt[s] f x
  证明: ⟨fun h => h.mono (subset_insert x s), fun h => h.hasMFDerivWithinAt.insert.mdifferentiableWithinAt⟩

Depends on / 依赖: h.hasMFDerivWithinAt.insert.mdifferentiableWithinAt, h.mono, hasMFDerivWithinAt, insert, mdifferentiableWithinAt, subset_insert
-/
theorem mdifferentiableWithinAt_insert_self : MDiffAt[insert x s] f x ↔ MDiffAt[s] f x :=
  ⟨fun h => h.mono (subset_insert x s), fun h => h.hasMFDerivWithinAt.insert.mdifferentiableWithinAt⟩

/--
theorem `mdifferentiableWithinAt_insert` / 定理 `mdifferentiableWithinAt_insert`

English:
theorem mdifferentiableWithinAt_insert
  given: {y : M}
  statement: MDiffAt[insert y s] f x ↔ MDiffAt[s] f x
  proof: by
  rcases eq_or_ne x y with (rfl | h)
  · exact mdifferentiableWithinAt_insert_self
  have : T1Space M := I.t1Space M
  apply mdifferentiableWithinAt_congr_nhds
  exact nhdsWithin_insert_of_ne h

alias ⟨MDifferentiableWithinAt.of_insert, MDifferentiableWithinAt.insert'⟩ :=
mdifferentiableWithinAt_insert

中文:
定理 mdifferentiableWithinAt_insert
  条件: {y : M}
  结论: MDiffAt[insert y s] f x ↔ MDiffAt[s] f x
  证明: by
  rcases eq_or_ne x y with (rfl | h)
  · exact mdifferentiableWithinAt_insert_self
  have : T1Space M := I.t1Space M
  apply mdifferentiableWithinAt_congr_nhds
  exact nhdsWithin_insert_of_ne h

alias ⟨MDifferentiableWithinAt.of_insert, MDifferentiableWithinAt.insert'⟩ :=
mdifferentiableWithinAt_insert

Depends on / 依赖: I.t1Space, T1Space, eq_or_ne, mdifferentiableWithinAt_congr_nhds, mdifferentiableWithinAt_insert_self, nhdsWithin_insert_of_ne, t1Space
-/
theorem mdifferentiableWithinAt_insert {y : M} : MDiffAt[insert y s] f x ↔ MDiffAt[s] f x := by
  rcases eq_or_ne x y with (rfl | h)
  · exact mdifferentiableWithinAt_insert_self
  have : T1Space M := I.t1Space M
  apply mdifferentiableWithinAt_congr_nhds
  exact nhdsWithin_insert_of_ne h

alias ⟨MDifferentiableWithinAt.of_insert, MDifferentiableWithinAt.insert'⟩ :=
mdifferentiableWithinAt_insert

/--
theorem `MDifferentiableWithinAt.insert` / 定理 `MDifferentiableWithinAt.insert`

English:
theorem MDifferentiableWithinAt.insert
  given: (h : MDiffAt[s] f x)
  statement: MDiffAt[insert x s] f x
  proof: h.insert'

中文:
定理 MDifferentiableWithinAt.insert
  条件: (h : MDiffAt[s] f x)
  结论: MDiffAt[insert x s] f x
  证明: h.insert'
-/
protected theorem MDifferentiableWithinAt.insert (h : MDiffAt[s] f x) : MDiffAt[insert x s] f x :=
  h.insert'

/-! ### Being differentiable on a union of open sets can be tested on each set -/

section mdifferentiableOn_union

/--
lemma `MDifferentiableOn.union_of_isOpen` / 引理 `MDifferentiableOn.union_of_isOpen`

English:
lemma MDifferentiableOn.union_of_isOpen
  proof: by
  intro x hx
  obtain (hx | hx) := hx
.mdifferentiableWithinAt · exact (hf x hx).mdifferentiableAt (hs.mem_nhds hx)
.mdifferentiableWithinAt · exact (hf' x hx).mdifferentiableAt (ht.mem_nhds hx)

中文:
引理 MDifferentiableOn.union_of_isOpen
  证明: by
  intro x hx
  obtain (hx | hx) := hx
.mdifferentiableWithinAt · exact (hf x hx).mdifferentiableAt (hs.mem_nhds hx)
.mdifferentiableWithinAt · exact (hf' x hx).mdifferentiableAt (ht.mem_nhds hx)

Depends on / 依赖: hs.mem_nhds, ht.mem_nhds, mdifferentiableAt, mdifferentiableWithinAt, mem_nhds
-/
lemma MDifferentiableOn.union_of_isOpen
    (hf : MDiff[s] f) (hf' : MDiff[t] f) (hs : IsOpen s) (ht : IsOpen t) : MDiff[s union t] f := by
  intro x hx
  obtain (hx | hx) := hx
.mdifferentiableWithinAt · exact (hf x hx).mdifferentiableAt (hs.mem_nhds hx)
.mdifferentiableWithinAt · exact (hf' x hx).mdifferentiableAt (ht.mem_nhds hx)

/--
lemma `mdifferentiableOn_union_iff_of_isOpen` / 引理 `mdifferentiableOn_union_iff_of_isOpen`

English:
lemma mdifferentiableOn_union_iff_of_isOpen
  given: (hs : IsOpen s) (ht : IsOpen t)
  proof: ⟨fun h => ⟨h.mono subset_union_left, h.mono subset_union_right⟩,
    fun ⟨hfs, hft⟩ => MDifferentiableOn.union_of_isOpen hfs hft hs ht⟩

中文:
引理 mdifferentiableOn_union_iff_of_isOpen
  条件: (hs : 是开集 s) (ht : 是开集 t)
  证明: ⟨fun h => ⟨h.mono subset_union_left, h.mono subset_union_right⟩,
    fun ⟨hfs, hft⟩ => MDifferentiableOn.union_of_isOpen hfs hft hs ht⟩

Depends on / 依赖: MDifferentiableOn, MDifferentiableOn.union_of_isOpen, h.mono, subset_union_left, subset_union_right, union_of_isOpen
-/
lemma mdifferentiableOn_union_iff_of_isOpen (hs : IsOpen s) (ht : IsOpen t) :
    MDiff[s union t] f ↔ MDiff[s] f ∧ MDiff[t] f :=
  ⟨fun h => ⟨h.mono subset_union_left, h.mono subset_union_right⟩,
    fun ⟨hfs, hft⟩ => MDifferentiableOn.union_of_isOpen hfs hft hs ht⟩

/--
lemma `mdifferentiable_of_mdifferentiableOn_union_of_isOpen` / 引理 `mdifferentiable_of_mdifferentiableOn_union_of_isOpen`

English:
lemma mdifferentiable_of_mdifferentiableOn_union_of_isOpen
  statement: (hf : MDiff[s] f) (hf' : MDiff[t] f)
  proof: by
  rw [← mdifferentiableOn_univ]; rw [← hst]
  exact hf.union_of_isOpen hf' hs ht

中文:
引理 mdifferentiable_of_mdifferentiableOn_union_of_isOpen
  结论: (hf : MDiff[s] f) (hf' : MDiff[t] f)
  证明: by
  rw [← mdifferentiableOn_univ]; rw [← hst]
  exact hf.union_of_isOpen hf' hs ht

Depends on / 依赖: hf.union_of_isOpen, mdifferentiableOn_univ, union_of_isOpen
-/
lemma mdifferentiable_of_mdifferentiableOn_union_of_isOpen (hf : MDiff[s] f) (hf' : MDiff[t] f)
    (hst : s union t = univ) (hs : IsOpen s) (ht : IsOpen t) : MDiff f := by
  rw [← mdifferentiableOn_univ]; rw [← hst]
  exact hf.union_of_isOpen hf' hs ht

/--
lemma `MDifferentiableOn.iUnion_of_isOpen` / 引理 `MDifferentiableOn.iUnion_of_isOpen`

English:
lemma MDifferentiableOn.iUnion_of_isOpen
  proof: by
  rintro x ⟨si, ⟨i, rfl⟩, hxsi⟩
.mdifferentiableWithinAt exact (hf i).mdifferentiableAt ((hs i).mem_nhds hxsi)

中文:
引理 MDifferentiableOn.iUnion_of_isOpen
  证明: by
  rintro x ⟨si, ⟨i, rfl⟩, hxsi⟩
.mdifferentiableWithinAt exact (hf i).mdifferentiableAt ((hs i).mem_nhds hxsi)

Depends on / 依赖: mdifferentiableAt, mdifferentiableWithinAt, mem_nhds
-/
lemma MDifferentiableOn.iUnion_of_isOpen
    {ι : Type*} {s : ι -> Set M} (hf : forall i : ι, MDiff[s i] f) (hs : forall i, IsOpen (s i)) :
    MDiff[⋃ i, s i] f := by
  rintro x ⟨si, ⟨i, rfl⟩, hxsi⟩
.mdifferentiableWithinAt exact (hf i).mdifferentiableAt ((hs i).mem_nhds hxsi)

/--
lemma `mdifferentiableOn_iUnion_iff_of_isOpen` / 引理 `mdifferentiableOn_iUnion_iff_of_isOpen`

English:
lemma mdifferentiableOn_iUnion_iff_of_isOpen
  given: {ι : Type*} {s : ι -> Set M} (hs : forall i, IsOpen (s i))
  proof: ⟨fun h i => h.mono subset_iUnion_of_subset i fun _ a => a,
   fun h => MDifferentiableOn.iUnion_of_isOpen h hs⟩

中文:
引理 mdifferentiableOn_iUnion_iff_of_isOpen
  条件: {ι : 类型} {s : ι -> 集合 M} (hs : 对任意 i, 是开集 (s i))
  证明: ⟨fun h i => h.mono subset_iUnion_of_subset i fun _ a => a,
   fun h => MDifferentiableOn.iUnion_of_isOpen h hs⟩

Depends on / 依赖: MDifferentiableOn, MDifferentiableOn.iUnion_of_isOpen, h.mono, iUnion_of_isOpen, subset_iUnion_of_subset
-/
lemma mdifferentiableOn_iUnion_iff_of_isOpen {ι : Type*} {s : ι -> Set M} (hs : forall i, IsOpen (s i)) :
    MDiff[⋃ i, s i] f ↔ forall i : ι, MDiff[s i] f :=
⟨fun h i => h.mono subset_iUnion_of_subset i fun _ a => a,
   fun h => MDifferentiableOn.iUnion_of_isOpen h hs⟩

/--
lemma `mdifferentiable_of_mdifferentiableOn_iUnion_of_isOpen` / 引理 `mdifferentiable_of_mdifferentiableOn_iUnion_of_isOpen`

English:
lemma mdifferentiable_of_mdifferentiableOn_iUnion_of_isOpen
  statement: {ι : Type*} {s : ι -> Set M}
  proof: by
  rw [← mdifferentiableOn_univ]; rw [← hs']
  exact MDifferentiableOn.iUnion_of_isOpen hf hs

中文:
引理 mdifferentiable_of_mdifferentiableOn_iUnion_of_isOpen
  结论: {ι : 类型} {s : ι -> 集合 M}
  证明: by
  rw [← mdifferentiableOn_univ]; rw [← hs']
  exact MDifferentiableOn.iUnion_of_isOpen hf hs

Depends on / 依赖: MDifferentiableOn, MDifferentiableOn.iUnion_of_isOpen, iUnion_of_isOpen, mdifferentiableOn_univ
-/
lemma mdifferentiable_of_mdifferentiableOn_iUnion_of_isOpen {ι : Type*} {s : ι -> Set M}
    (hf : forall i : ι, MDiff[s i] f) (hs : forall i, IsOpen (s i)) (hs' : ⋃ i, s i = univ) : MDiff f := by
  rw [← mdifferentiableOn_univ]; rw [← hs']
  exact MDifferentiableOn.iUnion_of_isOpen hf hs

end mdifferentiableOn_union


/--
theorem `HasMFDerivWithinAt.continuousWithinAt` / 定理 `HasMFDerivWithinAt.continuousWithinAt`

English:
theorem HasMFDerivWithinAt.continuousWithinAt
  given: (h : HasMFDerivAt[s] f x f')
  proof: h.1

中文:
定理 HasMFDerivWithinAt.continuousWithinAt
  条件: (h : HasMFDerivAt[s] f x f')
  证明: h.1
-/
theorem HasMFDerivWithinAt.continuousWithinAt (h : HasMFDerivAt[s] f x f') :
    ContinuousWithinAt f s x :=
  h.1

/--
theorem `HasMFDerivAt.continuousAt` / 定理 `HasMFDerivAt.continuousAt`

English:
theorem HasMFDerivAt.continuousAt
  given: (h : HasMFDerivAt% f x f')
  statement: ContinuousAt f x
  proof: h.1

中文:
定理 HasMFDerivAt.continuousAt
  条件: (h : HasMFDerivAt% f x f')
  结论: ContinuousAt f x
  证明: h.1
-/
theorem HasMFDerivAt.continuousAt (h : HasMFDerivAt% f x f') : ContinuousAt f x :=
  h.1

/--
theorem `tangentMapWithin_subset` / 定理 `tangentMapWithin_subset`

English:
theorem tangentMapWithin_subset
  proof: by
  simp only [tangentMapWithin, mfld_simps]
  rw [mfderivWithin_subset st hs h]

中文:
定理 tangentMapWithin_subset
  证明: by
  simp only [tangentMapWithin, mfld_simps]
  rw [mfderivWithin_subset st hs h]

Depends on / 依赖: mfderivWithin_subset, mfld_simps, tangentMapWithin
-/
theorem tangentMapWithin_subset
    {p : TangentBundle I M} (st : s subseteq t) (hs : UniqueMDiffAt[s] p.1) (h : MDiffAt[t] f p.1) :
    tangentMap[s] f p = tangentMap[t] f p := by
  simp only [tangentMapWithin, mfld_simps]
  rw [mfderivWithin_subset st hs h]

/--
theorem `tangentMapWithin_univ` / 定理 `tangentMapWithin_univ`

English:
theorem tangentMapWithin_univ
  statement: tangentMap[(univ : Set M)] f = tangentMap% f
  proof: by
  ext p : 1
  simp only [tangentMapWithin, tangentMap, mfld_simps]

中文:
定理 tangentMapWithin_univ
  结论: tangentMap[(univ : 集合 M)] f = tangentMap% f
  证明: by
  ext p : 1
  simp only [tangentMapWithin, tangentMap, mfld_simps]

Depends on / 依赖: mfld_simps, tangentMap, tangentMapWithin
-/
theorem tangentMapWithin_univ : tangentMap[(univ : Set M)] f = tangentMap% f := by
  ext p : 1
  simp only [tangentMapWithin, tangentMap, mfld_simps]

/--
theorem `tangentMapWithin_eq_tangentMap` / 定理 `tangentMapWithin_eq_tangentMap`

English:
theorem tangentMapWithin_eq_tangentMap
  statement: {p : TangentBundle I M} (hs : UniqueMDiffAt[s] p.1)
  proof: by
  rw [← mdifferentiableWithinAt_univ] at h
  rw [← tangentMapWithin_univ]
  exact tangentMapWithin_subset (subset_univ _) hs h

@[simp, mfld_simps]

中文:
定理 tangentMapWithin_eq_tangentMap
  结论: {p : 切丛 I M} (hs : UniqueMDiffAt[s] p.1)
  证明: by
  rw [← mdifferentiableWithinAt_univ] at h
  rw [← tangentMapWithin_univ]
  exact tangentMapWithin_subset (subset_univ _) hs h

@[simp, mfld_simps]

Depends on / 依赖: mdifferentiableWithinAt_univ, subset_univ, tangentMapWithin_subset, tangentMapWithin_univ
-/
theorem tangentMapWithin_eq_tangentMap {p : TangentBundle I M} (hs : UniqueMDiffAt[s] p.1)
    (h : MDiffAt f p.1) : tangentMap[s] f p = tangentMap% f p := by
  rw [← mdifferentiableWithinAt_univ] at h
  rw [← tangentMapWithin_univ]
  exact tangentMapWithin_subset (subset_univ _) hs h

@[simp, mfld_simps]
/--
theorem `tangentMapWithin_proj` / 定理 `tangentMapWithin_proj`

English:
theorem tangentMapWithin_proj
  given: {p : TangentBundle I M}
  statement: (tangentMap[s] f p).proj = f p.proj
  proof: rfl

@[simp, mfld_simps]

中文:
定理 tangentMapWithin_proj
  条件: {p : 切丛 I M}
  结论: (tangentMap[s] f p).proj = f p.proj
  证明: rfl

@[simp, mfld_simps]
-/
theorem tangentMapWithin_proj {p : TangentBundle I M} : (tangentMap[s] f p).proj = f p.proj := rfl

@[simp, mfld_simps]
/--
lemma `tangentMapWithin_snd` / 引理 `tangentMapWithin_snd`

English:
lemma tangentMapWithin_snd
  given: {X : TangentSpace% x}
  statement: (tangentMap[s] f X).2 = (mfderiv[s] f x) X
  proof: rfl

@[simp, mfld_simps]

中文:
引理 tangentMapWithin_snd
  条件: {X : TangentSpace% x}
  结论: (tangentMap[s] f X).2 = (mfderiv[s] f x) X
  证明: rfl

@[simp, mfld_simps]

Depends on / 依赖: Finite, Module, Module.Finite.map
-/
lemma tangentMapWithin_snd {X : TangentSpace% x} : (tangentMap[s] f X).2 = (mfderiv[s] f x) X := rfl

@[simp, mfld_simps]
/--
theorem `tangentMap_proj` / 定理 `tangentMap_proj`

English:
theorem tangentMap_proj
  given: {p : TangentBundle I M}
  statement: (tangentMap% f p).proj = f p.proj
  proof: rfl

@[simp, mfld_simps]

中文:
定理 tangentMap_proj
  条件: {p : 切丛 I M}
  结论: (tangentMap% f p).proj = f p.proj
  证明: rfl

@[simp, mfld_simps]
-/
theorem tangentMap_proj {p : TangentBundle I M} : (tangentMap% f p).proj = f p.proj := rfl

@[simp, mfld_simps]
/--
lemma `tangentMap_snd` / 引理 `tangentMap_snd`

English:
lemma tangentMap_snd
  given: {X : TangentSpace% x}
  statement: (tangentMap% f X).2 = (mfderiv% f x) X
  proof: rfl

中文:
引理 tangentMap_snd
  条件: {X : TangentSpace% x}
  结论: (tangentMap% f X).2 = (mfderiv% f x) X
  证明: rfl
-/
lemma tangentMap_snd {X : TangentSpace% x} : (tangentMap% f X).2 = (mfderiv% f x) X := rfl

/--
theorem `preimage_extChartAt_eventuallyEq_compl_singleton` / 定理 `preimage_extChartAt_eventuallyEq_compl_singleton`

English:
theorem preimage_extChartAt_eventuallyEq_compl_singleton
  given: (y : M) (h : s =ᶠ[𝓝[{y}ᶜ] x] t)
  proof: by
  have : T1Space M := I.t1Space M
  obtain ⟨u, u_mem, hu⟩ : exists u in 𝓝 x, u inter {x}ᶜ subseteq {y | (y in s) = (y in t)} :=
    mem_nhdsWithin_iff_exists_mem_nhds_inter.1 (nhdsWithin_compl_singleton_le x y h)
  rw [← extChartAt_to_inv (I := I) x] at u_mem
  have B : (extChartAt I x).target union (range I)ᶜ in 𝓝 (extChartAt I x x) := by
    rw [← nhdsWithin_univ]; rw [← union_compl_self (range I)]; rw [nhdsWithin_union]
    apply Filter.union_mem_sup (extChartAt_target_mem_nhdsWithin x) self_mem_nhdsWithin
  apply mem_nhdsWithin_iff_exists_mem_nhds_inter.2
    ⟨_, Filter.inter_mem ((continuousAt_extChartAt_symm x).preimage_mem_nhds u_mem) B, ?_⟩
  rintro z ⟨hz, h'z⟩
  simp only [eq_iff_iff, mem_ofPred_eq]
  change z in (extChartAt I x).symm ⁻¹' s inter range I ↔ z in (extChartAt I x).symm ⁻¹' t inter range I
  by_cases hIz : z in range I
  · simp only [mem_inter_iff, mem_preimage, mem_union, mem_compl_iff, hIz, not_true_eq_false,
      or_false, and_true] at hz ⊢
    rw [← eq_iff_iff]
    apply hu ⟨hz.1, ?_⟩
    push _ in _ at h'z ⊢
    rw [eq_comm]; rw [(extChartAt I x).eq_symm_apply (by simp) hz.2]
    exact Ne.symm h'z
  · simp [hIz]

中文:
定理 preimage_extChartAt_eventuallyEq_compl_singleton
  条件: (y : M) (h : s =ᶠ[𝓝[{y}ᶜ] x] t)
  证明: by
  have : T1Space M := I.t1Space M
  obtain ⟨u, u_mem, hu⟩ : exists u in 𝓝 x, u inter {x}ᶜ subseteq {y | (y in s) = (y in t)} :=
    mem_nhdsWithin_iff_exists_mem_nhds_inter.1 (nhdsWithin_compl_singleton_le x y h)
  rw [← extChartAt_to_inv (I := I) x] at u_mem
  have B : (extChartAt I x).target union (range I)ᶜ in 𝓝 (extChartAt I x x) := by
    rw [← nhdsWithin_univ]; rw [← union_compl_self (range I)]; rw [nhdsWithin_union]
    apply Filter.union_mem_sup (extChartAt_target_mem_nhdsWithin x) self_mem_nhdsWithin
  apply mem_nhdsWithin_iff_exists_mem_nhds_inter.2
    ⟨_, Filter.inter_mem ((continuousAt_extChartAt_symm x).preimage_mem_nhds u_mem) B, ?_⟩
  rintro z ⟨hz, h'z⟩
  simp only [eq_iff_iff, mem_ofPred_eq]
  change z in (extChartAt I x).symm ⁻¹' s inter range I ↔ z in (extChartAt I x).symm ⁻¹' t inter range I
  by_cases hIz : z in range I
  · simp only [mem_inter_iff, mem_preimage, mem_union, mem_compl_iff, hIz, not_true_eq_false,
      or_false, and_true] at hz ⊢
    rw [← eq_iff_iff]
    apply hu ⟨hz.1, ?_⟩
    push _ in _ at h'z ⊢
    rw [eq_comm]; rw [(extChartAt I x).eq_symm_apply (by simp) hz.2]
    exact Ne.symm h'z
  · simp [hIz]

Depends on / 依赖: Filter, Filter.union_mem_sup, I.t1Space, T1Space, extChartAt, extChartAt_target_mem_nhdsWithin, extChartAt_to_inv, mem_nhdsWithin_iff_exists_mem_nhds_inter, nhdsWithin_compl_singleton_le, nhdsWithin_union, nhdsWithin_univ, self_mem_nhdsWithin, subseteq, t1Space, target, u_mem, union_compl_self, union_mem_sup
-/
theorem preimage_extChartAt_eventuallyEq_compl_singleton (y : M) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    ((extChartAt I x).symm ⁻¹' s inter range I : Set E) =ᶠ[𝓝[{extChartAt I x x}ᶜ] (extChartAt I x x)]
    ((extChartAt I x).symm ⁻¹' t inter range I : Set E) := by
  have : T1Space M := I.t1Space M
  obtain ⟨u, u_mem, hu⟩ : exists u in 𝓝 x, u inter {x}ᶜ subseteq {y | (y in s) = (y in t)} :=
    mem_nhdsWithin_iff_exists_mem_nhds_inter.1 (nhdsWithin_compl_singleton_le x y h)
  rw [← extChartAt_to_inv (I := I) x] at u_mem
  have B : (extChartAt I x).target union (range I)ᶜ in 𝓝 (extChartAt I x x) := by
    rw [← nhdsWithin_univ]; rw [← union_compl_self (range I)]; rw [nhdsWithin_union]
    apply Filter.union_mem_sup (extChartAt_target_mem_nhdsWithin x) self_mem_nhdsWithin
  apply mem_nhdsWithin_iff_exists_mem_nhds_inter.2
    ⟨_, Filter.inter_mem ((continuousAt_extChartAt_symm x).preimage_mem_nhds u_mem) B, ?_⟩
  rintro z ⟨hz, h'z⟩
  simp only [eq_iff_iff, mem_ofPred_eq]
  change z in (extChartAt I x).symm ⁻¹' s inter range I ↔ z in (extChartAt I x).symm ⁻¹' t inter range I
  by_cases hIz : z in range I
  · simp only [mem_inter_iff, mem_preimage, mem_union, mem_compl_iff, hIz, not_true_eq_false,
      or_false, and_true] at hz ⊢
    rw [← eq_iff_iff]
    apply hu ⟨hz.1, ?_⟩
    push _ in _ at h'z ⊢
    rw [eq_comm]; rw [(extChartAt I x).eq_symm_apply (by simp) hz.2]
    exact Ne.symm h'z
  · simp [hIz]

/-! ### Congruence lemmas for derivatives on manifolds -/

/--
theorem `hasMFDerivWithinAt_congr_set'` / 定理 `hasMFDerivWithinAt_congr_set'`

English:
theorem hasMFDerivWithinAt_congr_set'
  given: (y : M) (h : s =ᶠ[𝓝[{y}ᶜ] x] t)
  proof: by
  have : T1Space M := I.t1Space M
  simp only [HasMFDerivWithinAt]
  refine and_congr ?_ ?_
  · exact continuousWithinAt_congr_set' _ h
  · apply hasFDerivWithinAt_congr_set' (extChartAt I x x)
    exact preimage_extChartAt_eventuallyEq_compl_singleton y h

中文:
定理 hasMFDerivWithinAt_congr_set'
  条件: (y : M) (h : s =ᶠ[𝓝[{y}ᶜ] x] t)
  证明: by
  have : T1Space M := I.t1Space M
  simp only [HasMFDerivWithinAt]
  refine and_congr ?_ ?_
  · exact continuousWithinAt_congr_set' _ h
  · apply hasFDerivWithinAt_congr_set' (extChartAt I x x)
    exact preimage_extChartAt_eventuallyEq_compl_singleton y h

Depends on / 依赖: HasMFDerivWithinAt, I.t1Space, T1Space, and_congr, continuousWithinAt_congr_set, extChartAt, hasFDerivWithinAt_congr_set, preimage_extChartAt_eventuallyEq_compl_singleton, t1Space
-/
theorem hasMFDerivWithinAt_congr_set' (y : M) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    HasMFDerivAt[s] f x f' ↔ HasMFDerivAt[t] f x f' := by
  have : T1Space M := I.t1Space M
  simp only [HasMFDerivWithinAt]
  refine and_congr ?_ ?_
  · exact continuousWithinAt_congr_set' _ h
  · apply hasFDerivWithinAt_congr_set' (extChartAt I x x)
    exact preimage_extChartAt_eventuallyEq_compl_singleton y h

/--
theorem `hasMFDerivWithinAt_congr_set` / 定理 `hasMFDerivWithinAt_congr_set`

English:
theorem hasMFDerivWithinAt_congr_set
  given: (h : s =ᶠ[𝓝 x] t)
  proof: hasMFDerivWithinAt_congr_set' x h.filter_mono inf_le_left

中文:
定理 hasMFDerivWithinAt_congr_set
  条件: (h : s =ᶠ[𝓝 x] t)
  证明: hasMFDerivWithinAt_congr_set' x h.filter_mono inf_le_left

Depends on / 依赖: filter_mono, h.filter_mono, hasMFDerivWithinAt_congr_set, inf_le_left
-/
theorem hasMFDerivWithinAt_congr_set (h : s =ᶠ[𝓝 x] t) :
    HasMFDerivAt[s] f x f' ↔ HasMFDerivAt[t] f x f' :=
hasMFDerivWithinAt_congr_set' x h.filter_mono inf_le_left

/--
theorem `mdifferentiableWithinAt_congr_set'` / 定理 `mdifferentiableWithinAt_congr_set'`

English:
theorem mdifferentiableWithinAt_congr_set'
  given: (y : M) (h : s =ᶠ[𝓝[{y}ᶜ] x] t)
  proof: by
  simp only [mdifferentiableWithinAt_iff_exists_hasMFDerivWithinAt]
  exact exists_congr fun _ => hasMFDerivWithinAt_congr_set' _ h

中文:
定理 mdifferentiableWithinAt_congr_set'
  条件: (y : M) (h : s =ᶠ[𝓝[{y}ᶜ] x] t)
  证明: by
  simp only [mdifferentiableWithinAt_iff_exists_hasMFDerivWithinAt]
  exact exists_congr fun _ => hasMFDerivWithinAt_congr_set' _ h

Depends on / 依赖: exists_congr, hasMFDerivWithinAt_congr_set, mdifferentiableWithinAt_iff_exists_hasMFDerivWithinAt
-/
theorem mdifferentiableWithinAt_congr_set' (y : M) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    MDiffAt[s] f x ↔ MDiffAt[t] f x := by
  simp only [mdifferentiableWithinAt_iff_exists_hasMFDerivWithinAt]
  exact exists_congr fun _ => hasMFDerivWithinAt_congr_set' _ h

/--
theorem `mdifferentiableWithinAt_congr_set` / 定理 `mdifferentiableWithinAt_congr_set`

English:
theorem mdifferentiableWithinAt_congr_set
  given: (h : s =ᶠ[𝓝 x] t)
  statement: MDiffAt[s] f x ↔ MDiffAt[t] f x
  proof: by
  simp only [mdifferentiableWithinAt_iff_exists_hasMFDerivWithinAt]
  exact exists_congr fun _ => hasMFDerivWithinAt_congr_set h

中文:
定理 mdifferentiableWithinAt_congr_set
  条件: (h : s =ᶠ[𝓝 x] t)
  结论: MDiffAt[s] f x ↔ MDiffAt[t] f x
  证明: by
  simp only [mdifferentiableWithinAt_iff_exists_hasMFDerivWithinAt]
  exact exists_congr fun _ => hasMFDerivWithinAt_congr_set h

Depends on / 依赖: exists_congr, hasMFDerivWithinAt_congr_set, mdifferentiableWithinAt_iff_exists_hasMFDerivWithinAt
-/
theorem mdifferentiableWithinAt_congr_set (h : s =ᶠ[𝓝 x] t) : MDiffAt[s] f x ↔ MDiffAt[t] f x := by
  simp only [mdifferentiableWithinAt_iff_exists_hasMFDerivWithinAt]
  exact exists_congr fun _ => hasMFDerivWithinAt_congr_set h

/--
theorem `mfderivWithin_congr_set'` / 定理 `mfderivWithin_congr_set'`

English:
theorem mfderivWithin_congr_set'
  given: (y : M) (h : s =ᶠ[𝓝[{y}ᶜ] x] t)
  proof: by
  by_cases hx : MDiffAt[s] f x
  · simp only [mfderivWithin, hx, (mdifferentiableWithinAt_congr_set' y h).1 hx, ↓reduceIte]
    apply fderivWithin_congr_set' (extChartAt I x x)
    exact preimage_extChartAt_eventuallyEq_compl_singleton y h
  · simp [mfderivWithin, hx, ← mdifferentiableWithinAt_congr_set' y h]

中文:
定理 mfderivWithin_congr_set'
  条件: (y : M) (h : s =ᶠ[𝓝[{y}ᶜ] x] t)
  证明: by
  by_cases hx : MDiffAt[s] f x
  · simp only [mfderivWithin, hx, (mdifferentiableWithinAt_congr_set' y h).1 hx, ↓reduceIte]
    apply fderivWithin_congr_set' (extChartAt I x x)
    exact preimage_extChartAt_eventuallyEq_compl_singleton y h
  · simp [mfderivWithin, hx, ← mdifferentiableWithinAt_congr_set' y h]

Depends on / 依赖: MDiffAt, extChartAt, fderivWithin_congr_set, mdifferentiableWithinAt_congr_set, mfderivWithin, preimage_extChartAt_eventuallyEq_compl_singleton, reduceIte
-/
theorem mfderivWithin_congr_set' (y : M) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    mfderiv[s] f x = mfderiv[t] f x := by
  by_cases hx : MDiffAt[s] f x
  · simp only [mfderivWithin, hx, (mdifferentiableWithinAt_congr_set' y h).1 hx, ↓reduceIte]
    apply fderivWithin_congr_set' (extChartAt I x x)
    exact preimage_extChartAt_eventuallyEq_compl_singleton y h
  · simp [mfderivWithin, hx, ← mdifferentiableWithinAt_congr_set' y h]

/--
theorem `mfderivWithin_congr_set` / 定理 `mfderivWithin_congr_set`

English:
theorem mfderivWithin_congr_set
  given: (h : s =ᶠ[𝓝 x] t)
  statement: mfderiv[s] f x = mfderiv[t] f x
  proof: mfderivWithin_congr_set' x h.filter_mono inf_le_left

中文:
定理 mfderivWithin_congr_set
  条件: (h : s =ᶠ[𝓝 x] t)
  结论: mfderiv[s] f x = mfderiv[t] f x
  证明: mfderivWithin_congr_set' x h.filter_mono inf_le_left

Depends on / 依赖: filter_mono, h.filter_mono, inf_le_left, mfderivWithin_congr_set
-/
theorem mfderivWithin_congr_set (h : s =ᶠ[𝓝 x] t) : mfderiv[s] f x = mfderiv[t] f x :=
mfderivWithin_congr_set' x h.filter_mono inf_le_left

/--
theorem `mfderivWithin_eventually_congr_set'` / 定理 `mfderivWithin_eventually_congr_set'`

English:
theorem mfderivWithin_eventually_congr_set'
  given: (y : M) (h : s =ᶠ[𝓝[{y}ᶜ] x] t)
  proof: (eventually_nhds_nhdsWithin.2 h).mono fun _ => mfderivWithin_congr_set' y

中文:
定理 mfderivWithin_eventually_congr_set'
  条件: (y : M) (h : s =ᶠ[𝓝[{y}ᶜ] x] t)
  证明: (eventually_nhds_nhdsWithin.2 h).mono fun _ => mfderivWithin_congr_set' y

Depends on / 依赖: eventually_nhds_nhdsWithin, mfderivWithin_congr_set
-/
theorem mfderivWithin_eventually_congr_set' (y : M) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    forallᶠ y in 𝓝 x, mfderiv[s] f y = mfderiv[t] f y :=
  (eventually_nhds_nhdsWithin.2 h).mono fun _ => mfderivWithin_congr_set' y

/--
theorem `mfderivWithin_eventually_congr_set` / 定理 `mfderivWithin_eventually_congr_set`

English:
theorem mfderivWithin_eventually_congr_set
  given: (h : s =ᶠ[𝓝 x] t)
  proof: mfderivWithin_eventually_congr_set' x h.filter_mono inf_le_left

中文:
定理 mfderivWithin_eventually_congr_set
  条件: (h : s =ᶠ[𝓝 x] t)
  证明: mfderivWithin_eventually_congr_set' x h.filter_mono inf_le_left

Depends on / 依赖: filter_mono, h.filter_mono, inf_le_left, mfderivWithin_eventually_congr_set
-/
theorem mfderivWithin_eventually_congr_set (h : s =ᶠ[𝓝 x] t) :
    forallᶠ y in 𝓝 x, mfderiv[s] f y = mfderiv[t] f y :=
mfderivWithin_eventually_congr_set' x h.filter_mono inf_le_left

/--
theorem `HasMFDerivAt.congr_mfderiv` / 定理 `HasMFDerivAt.congr_mfderiv`

English:
theorem HasMFDerivAt.congr_mfderiv
  given: (h : HasMFDerivAt% f x f') (h' : f' = f₁')
  proof: h' ▸ h

中文:
定理 HasMFDerivAt.congr_mfderiv
  条件: (h : HasMFDerivAt% f x f') (h' : f' = f₁')
  证明: h' ▸ h
-/
theorem HasMFDerivAt.congr_mfderiv (h : HasMFDerivAt% f x f') (h' : f' = f₁') :
    HasMFDerivAt% f x f₁' :=
  h' ▸ h

/--
theorem `HasMFDerivWithinAt.congr_mfderiv` / 定理 `HasMFDerivWithinAt.congr_mfderiv`

English:
theorem HasMFDerivWithinAt.congr_mfderiv
  given: (h : HasMFDerivAt[s] f x f') (h' : f' = f₁')
  proof: h' ▸ h

中文:
定理 HasMFDerivWithinAt.congr_mfderiv
  条件: (h : HasMFDerivAt[s] f x f') (h' : f' = f₁')
  证明: h' ▸ h
-/
theorem HasMFDerivWithinAt.congr_mfderiv (h : HasMFDerivAt[s] f x f') (h' : f' = f₁') :
    HasMFDerivAt[s] f x f₁' :=
  h' ▸ h

/--
theorem `HasMFDerivWithinAt.congr_of_eventuallyEq` / 定理 `HasMFDerivWithinAt.congr_of_eventuallyEq`

English:
theorem HasMFDerivWithinAt.congr_of_eventuallyEq
  proof: by
  refine ⟨ContinuousWithinAt.congr_of_eventuallyEq h.1 h₁ hx, ?_⟩
  apply HasFDerivWithinAt.congr_of_eventuallyEq h.2
  · have :
      (extChartAt I x).symm ⁻¹' {y | f₁ y = f y} in
        𝓝[(extChartAt I x).symm ⁻¹' s inter range I] (extChartAt I x) x :=
      extChartAt_preimage_mem_nhdsWithin h₁
    apply Filter.mem_of_superset this fun y => _
    simp +contextual only [hx, mfld_simps]
  · simp only [hx, mfld_simps]

中文:
定理 HasMFDerivWithinAt.congr_of_eventuallyEq
  证明: by
  refine ⟨ContinuousWithinAt.congr_of_eventuallyEq h.1 h₁ hx, ?_⟩
  apply HasFDerivWithinAt.congr_of_eventuallyEq h.2
  · have :
      (extChartAt I x).symm ⁻¹' {y | f₁ y = f y} in
        𝓝[(extChartAt I x).symm ⁻¹' s inter range I] (extChartAt I x) x :=
      extChartAt_preimage_mem_nhdsWithin h₁
    apply Filter.mem_of_superset this fun y => _
    simp +contextual only [hx, mfld_simps]
  · simp only [hx, mfld_simps]

Depends on / 依赖: ContinuousWithinAt, ContinuousWithinAt.congr_of_eventuallyEq, Filter, Filter.mem_of_superset, HasFDerivWithinAt, HasFDerivWithinAt.congr_of_eventuallyEq, congr_of_eventuallyEq, contextual, extChartAt, extChartAt_preimage_mem_nhdsWithin, mem_of_superset, mfld_simps
-/
theorem HasMFDerivWithinAt.congr_of_eventuallyEq
    (h : HasMFDerivAt[s] f x f') (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) :
    HasMFDerivAt[s] f₁ x f' := by
  refine ⟨ContinuousWithinAt.congr_of_eventuallyEq h.1 h₁ hx, ?_⟩
  apply HasFDerivWithinAt.congr_of_eventuallyEq h.2
  · have :
      (extChartAt I x).symm ⁻¹' {y | f₁ y = f y} in
        𝓝[(extChartAt I x).symm ⁻¹' s inter range I] (extChartAt I x) x :=
      extChartAt_preimage_mem_nhdsWithin h₁
    apply Filter.mem_of_superset this fun y => _
    simp +contextual only [hx, mfld_simps]
  · simp only [hx, mfld_simps]

/--
theorem `HasMFDerivWithinAt.congr_mono` / 定理 `HasMFDerivWithinAt.congr_mono`

English:
theorem HasMFDerivWithinAt.congr_mono
  proof: (h.mono h₁).congr_of_eventuallyEq (Filter.mem_inf_of_right ht) hx

中文:
定理 HasMFDerivWithinAt.congr_mono
  证明: (h.mono h₁).congr_of_eventuallyEq (Filter.mem_inf_of_right ht) hx

Depends on / 依赖: Filter, Filter.mem_inf_of_right, congr_of_eventuallyEq, h.mono, mem_inf_of_right
-/
theorem HasMFDerivWithinAt.congr_mono
    (h : HasMFDerivAt[s] f x f') (ht : forall x in t, f₁ x = f x) (hx : f₁ x = f x) (h₁ : t subseteq s) :
    HasMFDerivAt[t] f₁ x f' :=
  (h.mono h₁).congr_of_eventuallyEq (Filter.mem_inf_of_right ht) hx

set_option backward.isDefEq.respectTransparency false in
/--
theorem `HasMFDerivAt.congr_of_eventuallyEq` / 定理 `HasMFDerivAt.congr_of_eventuallyEq`

English:
theorem HasMFDerivAt.congr_of_eventuallyEq
  given: (h : HasMFDerivAt% f x f') (h₁ : f₁ =ᶠ[𝓝 x] f)
  proof: by
  rw [← hasMFDerivWithinAt_univ] at h ⊢
  apply h.congr_of_eventuallyEq _ (mem_of_mem_nhds h₁ :)
  rwa [nhdsWithin_univ]

中文:
定理 HasMFDerivAt.congr_of_eventuallyEq
  条件: (h : HasMFDerivAt% f x f') (h₁ : f₁ =ᶠ[𝓝 x] f)
  证明: by
  rw [← hasMFDerivWithinAt_univ] at h ⊢
  apply h.congr_of_eventuallyEq _ (mem_of_mem_nhds h₁ :)
  rwa [nhdsWithin_univ]

Depends on / 依赖: congr_of_eventuallyEq, h.congr_of_eventuallyEq, hasMFDerivWithinAt_univ, mem_of_mem_nhds, nhdsWithin_univ
-/
theorem HasMFDerivAt.congr_of_eventuallyEq (h : HasMFDerivAt% f x f') (h₁ : f₁ =ᶠ[𝓝 x] f) :
    HasMFDerivAt% f₁ x f' := by
  rw [← hasMFDerivWithinAt_univ] at h ⊢
  apply h.congr_of_eventuallyEq _ (mem_of_mem_nhds h₁ :)
  rwa [nhdsWithin_univ]

/--
theorem `mdifferentiableWithinAt_congr` / 定理 `mdifferentiableWithinAt_congr`

English:
theorem mdifferentiableWithinAt_congr
  given: (h₁ : forall y in s, f₁ y = f y) (hx : f₁ x = f x)
  proof: differentiableWithinAt_localInvariantProp.liftPropWithinAt_congr_iff h₁ hx

中文:
定理 mdifferentiableWithinAt_congr
  条件: (h₁ : 对任意 y in s, f₁ y = f y) (hx : f₁ x = f x)
  证明: differentiableWithinAt_localInvariantProp.liftPropWithinAt_congr_iff h₁ hx

Depends on / 依赖: differentiableWithinAt_localInvariantProp, differentiableWithinAt_localInvariantProp.liftPropWithinAt_congr_iff, liftPropWithinAt_congr_iff
-/
theorem mdifferentiableWithinAt_congr (h₁ : forall y in s, f₁ y = f y) (hx : f₁ x = f x) :
    MDiffAt[s] f₁ x ↔ MDiffAt[s] f x :=
  differentiableWithinAt_localInvariantProp.liftPropWithinAt_congr_iff h₁ hx

/--
theorem `MDifferentiableWithinAt.congr_of_mem` / 定理 `MDifferentiableWithinAt.congr_of_mem`

English:
theorem MDifferentiableWithinAt.congr_of_mem
  statement: (h : MDiffAt[s] f x) (h₁ : forall y in s, f₁ y = f y)
  proof: differentiableWithinAt_localInvariantProp.liftPropWithinAt_congr_of_mem h h₁ hx

中文:
定理 MDifferentiableWithinAt.congr_of_mem
  结论: (h : MDiffAt[s] f x) (h₁ : 对任意 y in s, f₁ y = f y)
  证明: differentiableWithinAt_localInvariantProp.liftPropWithinAt_congr_of_mem h h₁ hx

Depends on / 依赖: differentiableWithinAt_localInvariantProp, differentiableWithinAt_localInvariantProp.liftPropWithinAt_congr_of_mem, liftPropWithinAt_congr_of_mem
-/
theorem MDifferentiableWithinAt.congr_of_mem (h : MDiffAt[s] f x) (h₁ : forall y in s, f₁ y = f y)
    (hx : x in s) : MDiffAt[s] f₁ x :=
  differentiableWithinAt_localInvariantProp.liftPropWithinAt_congr_of_mem h h₁ hx

/--
theorem `mdifferentiableWithinAt_congr_of_mem` / 定理 `mdifferentiableWithinAt_congr_of_mem`

English:
theorem mdifferentiableWithinAt_congr_of_mem
  given: (h₁ : forall y in s, f₁ y = f y) (hx : x in s)
  proof: differentiableWithinAt_localInvariantProp.liftPropWithinAt_congr_iff_of_mem h₁ hx

中文:
定理 mdifferentiableWithinAt_congr_of_mem
  条件: (h₁ : 对任意 y in s, f₁ y = f y) (hx : x in s)
  证明: differentiableWithinAt_localInvariantProp.liftPropWithinAt_congr_iff_of_mem h₁ hx

Depends on / 依赖: differentiableWithinAt_localInvariantProp, differentiableWithinAt_localInvariantProp.liftPropWithinAt_congr_iff_of_mem, liftPropWithinAt_congr_iff_of_mem
-/
theorem mdifferentiableWithinAt_congr_of_mem (h₁ : forall y in s, f₁ y = f y) (hx : x in s) :
    MDiffAt[s] f₁ x ↔ MDiffAt[s] f x :=
  differentiableWithinAt_localInvariantProp.liftPropWithinAt_congr_iff_of_mem h₁ hx

/--
theorem `Filter.EventuallyEq.mdifferentiablefWithinAt_iff` / 定理 `Filter.EventuallyEq.mdifferentiablefWithinAt_iff`

English:
theorem Filter.EventuallyEq.mdifferentiablefWithinAt_iff
  given: (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x)
  proof: differentiableWithinAt_localInvariantProp.liftPropWithinAt_congr_iff_of_eventuallyEq h₁ hx

中文:
定理 滤子.EventuallyEq.mdifferentiablefWithinAt_iff
  条件: (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x)
  证明: differentiableWithinAt_localInvariantProp.liftPropWithinAt_congr_iff_of_eventuallyEq h₁ hx

Depends on / 依赖: differentiableWithinAt_localInvariantProp, differentiableWithinAt_localInvariantProp.liftPropWithinAt_congr_iff_of_eventuallyEq, liftPropWithinAt_congr_iff_of_eventuallyEq
-/
theorem Filter.EventuallyEq.mdifferentiablefWithinAt_iff (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) :
    MDiffAt[s] f₁ x ↔ MDiffAt[s] f x :=
  differentiableWithinAt_localInvariantProp.liftPropWithinAt_congr_iff_of_eventuallyEq h₁ hx

/--
theorem `MDifferentiableWithinAt.congr_of_eventuallyEq` / 定理 `MDifferentiableWithinAt.congr_of_eventuallyEq`

English:
theorem MDifferentiableWithinAt.congr_of_eventuallyEq
  statement: (h : MDiffAt[s] f x) (h₁ : f₁ =ᶠ[𝓝[s] x] f)
  proof: (h.hasMFDerivWithinAt.congr_of_eventuallyEq h₁ hx).mdifferentiableWithinAt

中文:
定理 MDifferentiableWithinAt.congr_of_eventuallyEq
  结论: (h : MDiffAt[s] f x) (h₁ : f₁ =ᶠ[𝓝[s] x] f)
  证明: (h.hasMFDerivWithinAt.congr_of_eventuallyEq h₁ hx).mdifferentiableWithinAt

Depends on / 依赖: congr_of_eventuallyEq, h.hasMFDerivWithinAt.congr_of_eventuallyEq, hasMFDerivWithinAt, mdifferentiableWithinAt
-/
theorem MDifferentiableWithinAt.congr_of_eventuallyEq (h : MDiffAt[s] f x) (h₁ : f₁ =ᶠ[𝓝[s] x] f)
    (hx : f₁ x = f x) : MDiffAt[s] f₁ x :=
  (h.hasMFDerivWithinAt.congr_of_eventuallyEq h₁ hx).mdifferentiableWithinAt

/--
theorem `MDifferentiableWithinAt.congr_of_eventuallyEq_of_mem` / 定理 `MDifferentiableWithinAt.congr_of_eventuallyEq_of_mem`

English:
theorem MDifferentiableWithinAt.congr_of_eventuallyEq_of_mem
  proof: h.congr_of_eventuallyEq h₁ (mem_of_mem_nhdsWithin hx h₁ :)

中文:
定理 MDifferentiableWithinAt.congr_of_eventuallyEq_of_mem
  证明: h.congr_of_eventuallyEq h₁ (mem_of_mem_nhdsWithin hx h₁ :)

Depends on / 依赖: congr_of_eventuallyEq, h.congr_of_eventuallyEq, mem_of_mem_nhdsWithin
-/
theorem MDifferentiableWithinAt.congr_of_eventuallyEq_of_mem
    (h : MDiffAt[s] f x) (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : x in s) : MDiffAt[s] f₁ x :=
  h.congr_of_eventuallyEq h₁ (mem_of_mem_nhdsWithin hx h₁ :)

/--
theorem `MDifferentiableWithinAt.congr_of_eventuallyEq_insert` / 定理 `MDifferentiableWithinAt.congr_of_eventuallyEq_insert`

English:
theorem MDifferentiableWithinAt.congr_of_eventuallyEq_insert
  proof: (h.insert.congr_of_eventuallyEq_of_mem h₁ (mem_insert x s)).of_insert

中文:
定理 MDifferentiableWithinAt.congr_of_eventuallyEq_insert
  证明: (h.insert.congr_of_eventuallyEq_of_mem h₁ (mem_insert x s)).of_insert

Depends on / 依赖: congr_of_eventuallyEq_of_mem, h.insert.congr_of_eventuallyEq_of_mem, insert, mem_insert, of_insert
-/
theorem MDifferentiableWithinAt.congr_of_eventuallyEq_insert
    (h : MDiffAt[s] f x) (h₁ : f₁ =ᶠ[𝓝[insert x s] x] f) : MDiffAt[s] f₁ x :=
  (h.insert.congr_of_eventuallyEq_of_mem h₁ (mem_insert x s)).of_insert

/--
theorem `Filter.EventuallyEq.mdifferentiableWithinAt_iff` / 定理 `Filter.EventuallyEq.mdifferentiableWithinAt_iff`

English:
theorem Filter.EventuallyEq.mdifferentiableWithinAt_iff
  given: (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x)
  proof: mdifferentiablefWithinAt_iff h₁.symm hx.symm

中文:
定理 滤子.EventuallyEq.mdifferentiableWithinAt_iff
  条件: (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x)
  证明: mdifferentiablefWithinAt_iff h₁.symm hx.symm

Depends on / 依赖: hx.symm, mdifferentiablefWithinAt_iff
-/
theorem Filter.EventuallyEq.mdifferentiableWithinAt_iff (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) :
    MDiffAt[s] f x ↔ MDiffAt[s] f₁ x :=
  mdifferentiablefWithinAt_iff h₁.symm hx.symm

/--
theorem `MDifferentiableWithinAt.congr_mono` / 定理 `MDifferentiableWithinAt.congr_mono`

English:
theorem MDifferentiableWithinAt.congr_mono
  proof: (HasMFDerivWithinAt.congr_mono h.hasMFDerivWithinAt ht hx h₁).mdifferentiableWithinAt

中文:
定理 MDifferentiableWithinAt.congr_mono
  证明: (HasMFDerivWithinAt.congr_mono h.hasMFDerivWithinAt ht hx h₁).mdifferentiableWithinAt

Depends on / 依赖: HasMFDerivWithinAt, HasMFDerivWithinAt.congr_mono, congr_mono, h.hasMFDerivWithinAt, hasMFDerivWithinAt, mdifferentiableWithinAt
-/
theorem MDifferentiableWithinAt.congr_mono
    (h : MDiffAt[s] f x) (ht : forall x in t, f₁ x = f x) (hx : f₁ x = f x) (h₁ : t subseteq s) :
    MDiffAt[t] f₁ x :=
  (HasMFDerivWithinAt.congr_mono h.hasMFDerivWithinAt ht hx h₁).mdifferentiableWithinAt

/--
theorem `MDifferentiableWithinAt.congr` / 定理 `MDifferentiableWithinAt.congr`

English:
theorem MDifferentiableWithinAt.congr
  proof: (HasMFDerivWithinAt.congr_mono h.hasMFDerivWithinAt ht hx (Subset.refl _)).mdifferentiableWithinAt

中文:
定理 MDifferentiableWithinAt.congr
  证明: (HasMFDerivWithinAt.congr_mono h.hasMFDerivWithinAt ht hx (Subset.refl _)).mdifferentiableWithinAt

Depends on / 依赖: HasMFDerivWithinAt, HasMFDerivWithinAt.congr_mono, Subset, Subset.refl, congr_mono, h.hasMFDerivWithinAt, hasMFDerivWithinAt, mdifferentiableWithinAt
-/
theorem MDifferentiableWithinAt.congr
    (h : MDiffAt[s] f x) (ht : forall x in s, f₁ x = f x) (hx : f₁ x = f x) :
    MDiffAt[s] f₁ x :=
  (HasMFDerivWithinAt.congr_mono h.hasMFDerivWithinAt ht hx (Subset.refl _)).mdifferentiableWithinAt

/--
theorem `MDifferentiableWithinAt.congr'` / 定理 `MDifferentiableWithinAt.congr'`

English:
theorem MDifferentiableWithinAt.congr'
  proof: h.congr (fun _y hy => ht _y (hst hy)) (ht x hxt)

中文:
定理 MDifferentiableWithinAt.congr'
  证明: h.congr (fun _y hy => ht _y (hst hy)) (ht x hxt)

Depends on / 依赖: h.congr
-/
theorem MDifferentiableWithinAt.congr'
    (h : MDiffAt[s] f x) (ht : forall x in t, f₁ x = f x) (hst : s subseteq t) (hxt : x in t) : MDiffAt[s] f₁ x :=
  h.congr (fun _y hy => ht _y (hst hy)) (ht x hxt)

/--
theorem `Filter.EventuallyEq.mdifferentiableAt_iff` / 定理 `Filter.EventuallyEq.mdifferentiableAt_iff`

English:
theorem Filter.EventuallyEq.mdifferentiableAt_iff
  given: (h₁ : f₁ =ᶠ[𝓝 x] f)
  proof: differentiableWithinAt_localInvariantProp.liftPropAt_congr_iff_of_eventuallyEq h₁

中文:
定理 滤子.EventuallyEq.mdifferentiableAt_iff
  条件: (h₁ : f₁ =ᶠ[𝓝 x] f)
  证明: differentiableWithinAt_localInvariantProp.liftPropAt_congr_iff_of_eventuallyEq h₁

Depends on / 依赖: differentiableWithinAt_localInvariantProp, differentiableWithinAt_localInvariantProp.liftPropAt_congr_iff_of_eventuallyEq, liftPropAt_congr_iff_of_eventuallyEq
-/
theorem Filter.EventuallyEq.mdifferentiableAt_iff (h₁ : f₁ =ᶠ[𝓝 x] f) :
    MDiffAt f₁ x ↔ MDiffAt f x :=
  differentiableWithinAt_localInvariantProp.liftPropAt_congr_iff_of_eventuallyEq h₁

/--
theorem `MDifferentiableOn.congr` / 定理 `MDifferentiableOn.congr`

English:
theorem MDifferentiableOn.congr
  given: (h : MDiff[s] f) (h₁ : forall y in s, f₁ y = f y)
  statement: MDiff[s] f₁
  proof: differentiableWithinAt_localInvariantProp.liftPropOn_congr h h₁

中文:
定理 MDifferentiableOn.congr
  条件: (h : MDiff[s] f) (h₁ : 对任意 y in s, f₁ y = f y)
  结论: MDiff[s] f₁
  证明: differentiableWithinAt_localInvariantProp.liftPropOn_congr h h₁

Depends on / 依赖: differentiableWithinAt_localInvariantProp, differentiableWithinAt_localInvariantProp.liftPropOn_congr, liftPropOn_congr
-/
theorem MDifferentiableOn.congr (h : MDiff[s] f) (h₁ : forall y in s, f₁ y = f y) : MDiff[s] f₁ :=
  differentiableWithinAt_localInvariantProp.liftPropOn_congr h h₁

/--
theorem `mdifferentiableOn_congr` / 定理 `mdifferentiableOn_congr`

English:
theorem mdifferentiableOn_congr
  given: (h₁ : forall y in s, f₁ y = f y)
  statement: MDiff[s] f₁ ↔ MDiff[s] f
  proof: differentiableWithinAt_localInvariantProp.liftPropOn_congr_iff h₁

中文:
定理 mdifferentiableOn_congr
  条件: (h₁ : 对任意 y in s, f₁ y = f y)
  结论: MDiff[s] f₁ ↔ MDiff[s] f
  证明: differentiableWithinAt_localInvariantProp.liftPropOn_congr_iff h₁

Depends on / 依赖: differentiableWithinAt_localInvariantProp, differentiableWithinAt_localInvariantProp.liftPropOn_congr_iff, liftPropOn_congr_iff
-/
theorem mdifferentiableOn_congr (h₁ : forall y in s, f₁ y = f y) : MDiff[s] f₁ ↔ MDiff[s] f :=
  differentiableWithinAt_localInvariantProp.liftPropOn_congr_iff h₁

/--
theorem `MDifferentiableOn.congr_mono` / 定理 `MDifferentiableOn.congr_mono`

English:
theorem MDifferentiableOn.congr_mono
  given: (h : MDiff[s] f) (h' : forall x in t, f₁ x = f x) (h₁ : t subseteq s)
  proof: fun x hx =>
  (h x (h₁ hx)).congr_mono h' (h' x hx) h₁

中文:
定理 MDifferentiableOn.congr_mono
  条件: (h : MDiff[s] f) (h' : 对任意 x in t, f₁ x = f x) (h₁ : t subseteq s)
  证明: fun x hx =>
  (h x (h₁ hx)).congr_mono h' (h' x hx) h₁
-/
theorem MDifferentiableOn.congr_mono (h : MDiff[s] f) (h' : forall x in t, f₁ x = f x) (h₁ : t subseteq s) :
    MDiff[t] f₁ := fun x hx =>
  (h x (h₁ hx)).congr_mono h' (h' x hx) h₁

/--
theorem `MDifferentiableAt.congr_of_eventuallyEq` / 定理 `MDifferentiableAt.congr_of_eventuallyEq`

English:
theorem MDifferentiableAt.congr_of_eventuallyEq
  given: (h : MDiffAt f x) (hL : f₁ =ᶠ[𝓝 x] f)
  proof: (h.hasMFDerivAt.congr_of_eventuallyEq hL).mdifferentiableAt

中文:
定理 MDifferentiableAt.congr_of_eventuallyEq
  条件: (h : MDiffAt f x) (hL : f₁ =ᶠ[𝓝 x] f)
  证明: (h.hasMFDerivAt.congr_of_eventuallyEq hL).mdifferentiableAt

Depends on / 依赖: congr_of_eventuallyEq, h.hasMFDerivAt.congr_of_eventuallyEq, hasMFDerivAt, mdifferentiableAt
-/
theorem MDifferentiableAt.congr_of_eventuallyEq (h : MDiffAt f x) (hL : f₁ =ᶠ[𝓝 x] f) :
    MDiffAt f₁ x :=
  (h.hasMFDerivAt.congr_of_eventuallyEq hL).mdifferentiableAt

/--
theorem `MDifferentiableWithinAt.mfderivWithin_congr_mono` / 定理 `MDifferentiableWithinAt.mfderivWithin_congr_mono`

English:
theorem MDifferentiableWithinAt.mfderivWithin_congr_mono
  statement: (h : MDiffAt[s] f x)
  proof: (HasMFDerivWithinAt.congr_mono h.hasMFDerivWithinAt hs hx h₁).mfderivWithin hxt

中文:
定理 MDifferentiableWithinAt.mfderivWithin_congr_mono
  结论: (h : MDiffAt[s] f x)
  证明: (HasMFDerivWithinAt.congr_mono h.hasMFDerivWithinAt hs hx h₁).mfderivWithin hxt

Depends on / 依赖: HasMFDerivWithinAt, HasMFDerivWithinAt.congr_mono, congr_mono, h.hasMFDerivWithinAt, hasMFDerivWithinAt, mfderivWithin
-/
theorem MDifferentiableWithinAt.mfderivWithin_congr_mono (h : MDiffAt[s] f x)
    (hs : forall x in t, f₁ x = f x) (hx : f₁ x = f x) (hxt : UniqueMDiffAt[t] x) (h₁ : t subseteq s) :
    mfderiv[t] f₁ x = mfderiv[s] f x :=
  (HasMFDerivWithinAt.congr_mono h.hasMFDerivWithinAt hs hx h₁).mfderivWithin hxt

/--
theorem `MDifferentiableWithinAt.mfderivWithin_mono` / 定理 `MDifferentiableWithinAt.mfderivWithin_mono`

English:
theorem MDifferentiableWithinAt.mfderivWithin_mono
  proof: h.mfderivWithin_congr_mono (fun _ _ => rfl) rfl hxt h₁

中文:
定理 MDifferentiableWithinAt.mfderivWithin_mono
  证明: h.mfderivWithin_congr_mono (fun _ _ => rfl) rfl hxt h₁

Depends on / 依赖: h.mfderivWithin_congr_mono, mfderivWithin_congr_mono
-/
theorem MDifferentiableWithinAt.mfderivWithin_mono
    (h : MDiffAt[s] f x) (hxt : UniqueMDiffAt[t] x) (h₁ : t subseteq s) :
    mfderiv[t] f x = mfderiv[s] f x :=
  h.mfderivWithin_congr_mono (fun _ _ => rfl) rfl hxt h₁

/--
theorem `MDifferentiableWithinAt.mfderivWithin_mono_of_mem_nhdsWithin` / 定理 `MDifferentiableWithinAt.mfderivWithin_mono_of_mem_nhdsWithin`

English:
theorem MDifferentiableWithinAt.mfderivWithin_mono_of_mem_nhdsWithin
  proof: (HasMFDerivWithinAt.mono_of_mem_nhdsWithin h.hasMFDerivWithinAt h₁).mfderivWithin hxt

中文:
定理 MDifferentiableWithinAt.mfderivWithin_mono_of_mem_nhdsWithin
  证明: (HasMFDerivWithinAt.mono_of_mem_nhdsWithin h.hasMFDerivWithinAt h₁).mfderivWithin hxt

Depends on / 依赖: HasMFDerivWithinAt, HasMFDerivWithinAt.mono_of_mem_nhdsWithin, h.hasMFDerivWithinAt, hasMFDerivWithinAt, mfderivWithin, mono_of_mem_nhdsWithin
-/
theorem MDifferentiableWithinAt.mfderivWithin_mono_of_mem_nhdsWithin
    (h : MDiffAt[s] f x) (hxt : UniqueMDiffAt[t] x) (h₁ : s in 𝓝[t] x) :
    mfderiv[t] f x = mfderiv[s] f x :=
  (HasMFDerivWithinAt.mono_of_mem_nhdsWithin h.hasMFDerivWithinAt h₁).mfderivWithin hxt

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Filter.EventuallyEq.mfderivWithin_eq` / 定理 `Filter.EventuallyEq.mfderivWithin_eq`

English:
theorem Filter.EventuallyEq.mfderivWithin_eq
  given: (hL : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x)
  proof: by
  by_cases h : MDiffAt[s] f x
  · unfold mfderivWithin
    simp only [h, (hL.mdifferentiableWithinAt_iff hx).1 h, ↓reduceIte, writtenInExtChartAt]
    apply Filter.EventuallyEq.fderivWithin_eq; swap
    · simp [hx]
    filter_upwards [extChartAt_preimage_mem_nhdsWithin (I := I) hL] with y hy
    simp only [preimage_ofPred_eq, mem_ofPred_eq] at hy
    simp [-extChartAt, hy, hx]
  · unfold mfderivWithin
    rw [if_neg h]; rw [if_neg]
    rwa [← hL.mdifferentiableWithinAt_iff hx]

中文:
定理 滤子.EventuallyEq.mfderivWithin_eq
  条件: (hL : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x)
  证明: by
  by_cases h : MDiffAt[s] f x
  · unfold mfderivWithin
    simp only [h, (hL.mdifferentiableWithinAt_iff hx).1 h, ↓reduceIte, writtenInExtChartAt]
    apply Filter.EventuallyEq.fderivWithin_eq; swap
    · simp [hx]
    filter_upwards [extChartAt_preimage_mem_nhdsWithin (I := I) hL] with y hy
    simp only [preimage_ofPred_eq, mem_ofPred_eq] at hy
    simp [-extChartAt, hy, hx]
  · unfold mfderivWithin
    rw [if_neg h]; rw [if_neg]
    rwa [← hL.mdifferentiableWithinAt_iff hx]

Depends on / 依赖: EventuallyEq, Filter, Filter.EventuallyEq.fderivWithin_eq, MDiffAt, extChartAt, extChartAt_preimage_mem_nhdsWithin, fderivWithin_eq, filter_upwards, hL.mdifferentiableWithinAt_iff, if_neg, mdifferentiableWithinAt_iff, mem_ofPred_eq, mfderivWithin, preimage_ofPred_eq, reduceIte, writtenInExtChartAt
-/
theorem Filter.EventuallyEq.mfderivWithin_eq (hL : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) :
    mfderiv[s] f₁ x = mfderiv[s] f x := by
  by_cases h : MDiffAt[s] f x
  · unfold mfderivWithin
    simp only [h, (hL.mdifferentiableWithinAt_iff hx).1 h, ↓reduceIte, writtenInExtChartAt]
    apply Filter.EventuallyEq.fderivWithin_eq; swap
    · simp [hx]
    filter_upwards [extChartAt_preimage_mem_nhdsWithin (I := I) hL] with y hy
    simp only [preimage_ofPred_eq, mem_ofPred_eq] at hy
    simp [-extChartAt, hy, hx]
  · unfold mfderivWithin
    rw [if_neg h]; rw [if_neg]
    rwa [← hL.mdifferentiableWithinAt_iff hx]

/--
theorem `Filter.EventuallyEq.mfderivWithin_eq_of_mem` / 定理 `Filter.EventuallyEq.mfderivWithin_eq_of_mem`

English:
theorem Filter.EventuallyEq.mfderivWithin_eq_of_mem
  given: (hL : f₁ =ᶠ[𝓝[s] x] f) (hx : x in s)
  proof: hL.mfderivWithin_eq (mem_of_mem_nhdsWithin hx hL :)

中文:
定理 滤子.EventuallyEq.mfderivWithin_eq_of_mem
  条件: (hL : f₁ =ᶠ[𝓝[s] x] f) (hx : x in s)
  证明: hL.mfderivWithin_eq (mem_of_mem_nhdsWithin hx hL :)

Depends on / 依赖: hL.mfderivWithin_eq, mem_of_mem_nhdsWithin, mfderivWithin_eq
-/
theorem Filter.EventuallyEq.mfderivWithin_eq_of_mem (hL : f₁ =ᶠ[𝓝[s] x] f) (hx : x in s) :
    mfderiv[s] f₁ x = mfderiv[s] f x :=
  hL.mfderivWithin_eq (mem_of_mem_nhdsWithin hx hL :)

/--
theorem `mfderivWithin_congr` / 定理 `mfderivWithin_congr`

English:
theorem mfderivWithin_congr
  given: (hL : forall x in s, f₁ x = f x) (hx : f₁ x = f x)
  proof: Filter.EventuallyEq.mfderivWithin_eq (Filter.eventuallyEq_of_mem self_mem_nhdsWithin hL) hx

中文:
定理 mfderivWithin_congr
  条件: (hL : 对任意 x in s, f₁ x = f x) (hx : f₁ x = f x)
  证明: Filter.EventuallyEq.mfderivWithin_eq (Filter.eventuallyEq_of_mem self_mem_nhdsWithin hL) hx

Depends on / 依赖: EventuallyEq, Filter, Filter.EventuallyEq.mfderivWithin_eq, Filter.eventuallyEq_of_mem, eventuallyEq_of_mem, mfderivWithin_eq, self_mem_nhdsWithin
-/
theorem mfderivWithin_congr (hL : forall x in s, f₁ x = f x) (hx : f₁ x = f x) :
    mfderiv[s] f₁ x = mfderiv[s] f x :=
  Filter.EventuallyEq.mfderivWithin_eq (Filter.eventuallyEq_of_mem self_mem_nhdsWithin hL) hx

/--
theorem `mfderivWithin_congr_of_mem` / 定理 `mfderivWithin_congr_of_mem`

English:
theorem mfderivWithin_congr_of_mem
  given: (hL : forall x in s, f₁ x = f x) (hx : x in s)
  proof: Filter.EventuallyEq.mfderivWithin_eq_of_mem (Filter.eventuallyEq_of_mem self_mem_nhdsWithin hL) hx

中文:
定理 mfderivWithin_congr_of_mem
  条件: (hL : 对任意 x in s, f₁ x = f x) (hx : x in s)
  证明: Filter.EventuallyEq.mfderivWithin_eq_of_mem (Filter.eventuallyEq_of_mem self_mem_nhdsWithin hL) hx

Depends on / 依赖: EventuallyEq, Filter, Filter.EventuallyEq.mfderivWithin_eq_of_mem, Filter.eventuallyEq_of_mem, eventuallyEq_of_mem, mfderivWithin_eq_of_mem, self_mem_nhdsWithin
-/
theorem mfderivWithin_congr_of_mem (hL : forall x in s, f₁ x = f x) (hx : x in s) :
    mfderiv[s] f₁ x = mfderiv[s] f x :=
  Filter.EventuallyEq.mfderivWithin_eq_of_mem (Filter.eventuallyEq_of_mem self_mem_nhdsWithin hL) hx

/--
theorem `tangentMapWithin_congr` / 定理 `tangentMapWithin_congr`

English:
theorem tangentMapWithin_congr
  given: (h : forall x in s, f x = f₁ x) (p : TangentBundle I M) (hp : p.1 in s)
  proof: by
  refine TotalSpace.ext (h p.1 hp) ?_
  rw [tangentMapWithin]; rw [h p.1 hp]; rw [tangentMapWithin]; rw [mfderivWithin_congr h (h _ hp)]

中文:
定理 tangentMapWithin_congr
  条件: (h : 对任意 x in s, f x = f₁ x) (p : 切丛 I M) (hp : p.1 in s)
  证明: by
  refine TotalSpace.ext (h p.1 hp) ?_
  rw [tangentMapWithin]; rw [h p.1 hp]; rw [tangentMapWithin]; rw [mfderivWithin_congr h (h _ hp)]

Depends on / 依赖: FiniteDimensional, TotalSpace, TotalSpace.ext, add_lt_aleph0, f.lift_rank_comap_le, lift_aleph0, lift_lt, lift_lt_aleph0, lift_rank_comap_le, mfderivWithin_congr, rank_lt_aleph0_iff, tangentMapWithin
-/
theorem tangentMapWithin_congr (h : forall x in s, f x = f₁ x) (p : TangentBundle I M) (hp : p.1 in s) :
    tangentMap[s] f p = tangentMap[s] f₁ p := by
  refine TotalSpace.ext (h p.1 hp) ?_
  rw [tangentMapWithin]; rw [h p.1 hp]; rw [tangentMapWithin]; rw [mfderivWithin_congr h (h _ hp)]

/--
theorem `Filter.EventuallyEq.mfderiv_eq` / 定理 `Filter.EventuallyEq.mfderiv_eq`

English:
theorem Filter.EventuallyEq.mfderiv_eq
  given: (hL : f₁ =ᶠ[𝓝 x] f)
  statement: mfderiv% f₁ x = mfderiv% f x
  proof: by
  have A : f₁ x = f x := (mem_of_mem_nhds hL :)
  rw [← mfderivWithin_univ]; rw [← mfderivWithin_univ]
  rw [← nhdsWithin_univ] at hL
  exact hL.mfderivWithin_eq A

中文:
定理 滤子.EventuallyEq.mfderiv_eq
  条件: (hL : f₁ =ᶠ[𝓝 x] f)
  结论: mfderiv% f₁ x = mfderiv% f x
  证明: by
  have A : f₁ x = f x := (mem_of_mem_nhds hL :)
  rw [← mfderivWithin_univ]; rw [← mfderivWithin_univ]
  rw [← nhdsWithin_univ] at hL
  exact hL.mfderivWithin_eq A

Depends on / 依赖: FiniteDimensional, add_lt_aleph0, f.lift_rank_quot_map_le, hL.mfderivWithin_eq, lift_aleph0, lift_lt, lift_lt_aleph0, lift_rank_quot_map_le, mem_of_mem_nhds, mfderivWithin_eq, mfderivWithin_univ, nhdsWithin_univ, rank_lt_aleph0_iff
-/
theorem Filter.EventuallyEq.mfderiv_eq (hL : f₁ =ᶠ[𝓝 x] f) : mfderiv% f₁ x = mfderiv% f x := by
  have A : f₁ x = f x := (mem_of_mem_nhds hL :)
  rw [← mfderivWithin_univ]; rw [← mfderivWithin_univ]
  rw [← nhdsWithin_univ] at hL
  exact hL.mfderivWithin_eq A

/--
theorem `mfderiv_congr_point` / 定理 `mfderiv_congr_point`

English:
theorem mfderiv_congr_point
  given: {x' : M} (h : x = x')
  proof: by subst h; rfl

中文:
定理 mfderiv_congr_point
  条件: {x' : M} (h : x = x')
  证明: by subst h; rfl
-/
theorem mfderiv_congr_point {x' : M} (h : x = x') :
    @Eq (E ->L[𝕜] E') (mfderiv% f x) (mfderiv% f x') := by subst h; rfl

/--
theorem `mfderiv_congr` / 定理 `mfderiv_congr`

English:
theorem mfderiv_congr
  given: {f' : M -> M'} (h : f = f')
  proof: by subst h; rfl

中文:
定理 mfderiv_congr
  条件: {f' : M -> M'} (h : f = f')
  证明: by subst h; rfl
-/
theorem mfderiv_congr {f' : M -> M'} (h : f = f') :
    @Eq (E ->L[𝕜] E') (mfderiv% f x) (mfderiv% f' x) := by subst h; rfl

/-! ### Composition lemmas -/

variable (x)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `HasMFDerivWithinAt.comp` / 定理 `HasMFDerivWithinAt.comp`

English:
theorem HasMFDerivWithinAt.comp
  statement: (hg : HasMFDerivAt[u] g (f x) g')
  proof: by
  refine ⟨ContinuousWithinAt.comp hg.1 hf.1 hst, ?_⟩
  have A :
    HasFDerivWithinAt (writtenInExtChartAt I' I'' (f x) g ∘ writtenInExtChartAt I I' x f)
      (ContinuousLinearMap.comp g' f' : E ->L[𝕜] E'') ((extChartAt I x).symm ⁻¹' s inter range I)
      ((extChartAt I x) x) := by
    have :
      (extChartAt I x).symm ⁻¹' f ⁻¹' (extChartAt I' (f x)).source in
        𝓝[(extChartAt I x).symm ⁻¹' s inter range I] (extChartAt I x) x :=
      extChartAt_preimage_mem_nhdsWithin
        (hf.1.preimage_mem_nhdsWithin (extChartAt_source_mem_nhds _))
    unfold HasMFDerivWithinAt at *
    rw [← hasFDerivWithinAt_inter' this]; rw [← extChartAt_preimage_inter_eq] at hf ⊢
    have : writtenInExtChartAt I I' x f ((extChartAt I x) x) = (extChartAt I' (f x)) (f x) := by
      simp only [mfld_simps]
    rw [← this] at hg
    apply HasFDerivWithinAt.comp ((extChartAt I x) x) hg.2 hf.2 _
    intro y hy
    simp only [mfld_simps] at hy
    have : f (((chartAt H x).symm : H -> M) (I.symm y)) in u := hst hy.1.1
    simp only [hy, this, mfld_simps]
  apply A.congr_of_eventuallyEq (writtenInExtChartAt_comp hf.1)
  simp only [mfld_simps]

中文:
定理 HasMFDerivWithinAt.comp
  结论: (hg : HasMFDerivAt[u] g (f x) g')
  证明: by
  refine ⟨ContinuousWithinAt.comp hg.1 hf.1 hst, ?_⟩
  have A :
    HasFDerivWithinAt (writtenInExtChartAt I' I'' (f x) g ∘ writtenInExtChartAt I I' x f)
      (ContinuousLinearMap.comp g' f' : E ->L[𝕜] E'') ((extChartAt I x).symm ⁻¹' s inter range I)
      ((extChartAt I x) x) := by
    have :
      (extChartAt I x).symm ⁻¹' f ⁻¹' (extChartAt I' (f x)).source in
        𝓝[(extChartAt I x).symm ⁻¹' s inter range I] (extChartAt I x) x :=
      extChartAt_preimage_mem_nhdsWithin
        (hf.1.preimage_mem_nhdsWithin (extChartAt_source_mem_nhds _))
    unfold HasMFDerivWithinAt at *
    rw [← hasFDerivWithinAt_inter' this]; rw [← extChartAt_preimage_inter_eq] at hf ⊢
    have : writtenInExtChartAt I I' x f ((extChartAt I x) x) = (extChartAt I' (f x)) (f x) := by
      simp only [mfld_simps]
    rw [← this] at hg
    apply HasFDerivWithinAt.comp ((extChartAt I x) x) hg.2 hf.2 _
    intro y hy
    simp only [mfld_simps] at hy
    have : f (((chartAt H x).symm : H -> M) (I.symm y)) in u := hst hy.1.1
    simp only [hy, this, mfld_simps]
  apply A.congr_of_eventuallyEq (writtenInExtChartAt_comp hf.1)
  simp only [mfld_simps]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.comp, ContinuousWithinAt, ContinuousWithinAt.comp, HasFDerivWithinAt, extChartAt, extChartAt_preimage_mem_nhdsWithin, extChartAt_source_mem_nhds, preimage_mem_nhdsWithin, source, writtenInExtChartAt
-/
theorem HasMFDerivWithinAt.comp (hg : HasMFDerivAt[u] g (f x) g')
    (hf : HasMFDerivAt[s] f x f') (hst : s subseteq f ⁻¹' u) :
    HasMFDerivAt[s] (g ∘ f) x (g'.comp f') := by
  refine ⟨ContinuousWithinAt.comp hg.1 hf.1 hst, ?_⟩
  have A :
    HasFDerivWithinAt (writtenInExtChartAt I' I'' (f x) g ∘ writtenInExtChartAt I I' x f)
      (ContinuousLinearMap.comp g' f' : E ->L[𝕜] E'') ((extChartAt I x).symm ⁻¹' s inter range I)
      ((extChartAt I x) x) := by
    have :
      (extChartAt I x).symm ⁻¹' f ⁻¹' (extChartAt I' (f x)).source in
        𝓝[(extChartAt I x).symm ⁻¹' s inter range I] (extChartAt I x) x :=
      extChartAt_preimage_mem_nhdsWithin
        (hf.1.preimage_mem_nhdsWithin (extChartAt_source_mem_nhds _))
    unfold HasMFDerivWithinAt at *
    rw [← hasFDerivWithinAt_inter' this]; rw [← extChartAt_preimage_inter_eq] at hf ⊢
    have : writtenInExtChartAt I I' x f ((extChartAt I x) x) = (extChartAt I' (f x)) (f x) := by
      simp only [mfld_simps]
    rw [← this] at hg
    apply HasFDerivWithinAt.comp ((extChartAt I x) x) hg.2 hf.2 _
    intro y hy
    simp only [mfld_simps] at hy
    have : f (((chartAt H x).symm : H -> M) (I.symm y)) in u := hst hy.1.1
    simp only [hy, this, mfld_simps]
  apply A.congr_of_eventuallyEq (writtenInExtChartAt_comp hf.1)
  simp only [mfld_simps]

/--
theorem `HasMFDerivAt.comp` / 定理 `HasMFDerivAt.comp`

English:
theorem HasMFDerivAt.comp
  given: (hg : HasMFDerivAt% g (f x) g') (hf : HasMFDerivAt% f x f')
  proof: by
  rw [← hasMFDerivWithinAt_univ] at *
  exact HasMFDerivWithinAt.comp x (hg.mono (subset_univ _)) hf subset_preimage_univ

中文:
定理 HasMFDerivAt.comp
  条件: (hg : HasMFDerivAt% g (f x) g') (hf : HasMFDerivAt% f x f')
  证明: by
  rw [← hasMFDerivWithinAt_univ] at *
  exact HasMFDerivWithinAt.comp x (hg.mono (subset_univ _)) hf subset_preimage_univ

Depends on / 依赖: HasMFDerivWithinAt, HasMFDerivWithinAt.comp, hasMFDerivWithinAt_univ, hg.mono, subset_preimage_univ, subset_univ
-/
theorem HasMFDerivAt.comp (hg : HasMFDerivAt% g (f x) g') (hf : HasMFDerivAt% f x f') :
    HasMFDerivAt% (g ∘ f) x (g'.comp f') := by
  rw [← hasMFDerivWithinAt_univ] at *
  exact HasMFDerivWithinAt.comp x (hg.mono (subset_univ _)) hf subset_preimage_univ

/--
theorem `HasMFDerivAt.comp_hasMFDerivWithinAt` / 定理 `HasMFDerivAt.comp_hasMFDerivWithinAt`

English:
theorem HasMFDerivAt.comp_hasMFDerivWithinAt
  statement: (hg : HasMFDerivAt% g (f x) g')
  proof: by
  rw [← hasMFDerivWithinAt_univ] at *
  exact HasMFDerivWithinAt.comp x (hg.mono (subset_univ _)) hf subset_preimage_univ

中文:
定理 HasMFDerivAt.comp_hasMFDerivWithinAt
  结论: (hg : HasMFDerivAt% g (f x) g')
  证明: by
  rw [← hasMFDerivWithinAt_univ] at *
  exact HasMFDerivWithinAt.comp x (hg.mono (subset_univ _)) hf subset_preimage_univ

Depends on / 依赖: HasMFDerivWithinAt, HasMFDerivWithinAt.comp, hasMFDerivWithinAt_univ, hg.mono, subset_preimage_univ, subset_univ
-/
theorem HasMFDerivAt.comp_hasMFDerivWithinAt (hg : HasMFDerivAt% g (f x) g')
    (hf : HasMFDerivAt[s] f x f') : HasMFDerivAt[s] (g ∘ f) x (g'.comp f') := by
  rw [← hasMFDerivWithinAt_univ] at *
  exact HasMFDerivWithinAt.comp x (hg.mono (subset_univ _)) hf subset_preimage_univ

/--
theorem `MDifferentiableWithinAt.comp` / 定理 `MDifferentiableWithinAt.comp`

English:
theorem MDifferentiableWithinAt.comp
  statement: (hg : MDiffAt[u] g (f x)) (hf : MDiffAt[s] f x)
  proof: by
  rcases hf.2 with ⟨f', hf'⟩
  have F : HasMFDerivAt[s] f x f' := ⟨hf.1, hf'⟩
  rcases hg.2 with ⟨g', hg'⟩
  have G : HasMFDerivAt[u] g (f x) g' := ⟨hg.1, hg'⟩
  exact (HasMFDerivWithinAt.comp x G F h).mdifferentiableWithinAt

中文:
定理 MDifferentiableWithinAt.comp
  结论: (hg : MDiffAt[u] g (f x)) (hf : MDiffAt[s] f x)
  证明: by
  rcases hf.2 with ⟨f', hf'⟩
  have F : HasMFDerivAt[s] f x f' := ⟨hf.1, hf'⟩
  rcases hg.2 with ⟨g', hg'⟩
  have G : HasMFDerivAt[u] g (f x) g' := ⟨hg.1, hg'⟩
  exact (HasMFDerivWithinAt.comp x G F h).mdifferentiableWithinAt

Depends on / 依赖: HasMFDerivAt, HasMFDerivWithinAt, HasMFDerivWithinAt.comp, mdifferentiableWithinAt
-/
theorem MDifferentiableWithinAt.comp (hg : MDiffAt[u] g (f x)) (hf : MDiffAt[s] f x)
    (h : s subseteq f ⁻¹' u) : MDifferentiableWithinAt I I'' (g ∘ f) s x := by
  rcases hf.2 with ⟨f', hf'⟩
  have F : HasMFDerivAt[s] f x f' := ⟨hf.1, hf'⟩
  rcases hg.2 with ⟨g', hg'⟩
  have G : HasMFDerivAt[u] g (f x) g' := ⟨hg.1, hg'⟩
  exact (HasMFDerivWithinAt.comp x G F h).mdifferentiableWithinAt

/--
theorem `MDifferentiableWithinAt.comp_of_eq` / 定理 `MDifferentiableWithinAt.comp_of_eq`

English:
theorem MDifferentiableWithinAt.comp_of_eq
  proof: by
  subst hy; exact hg.comp _ hf h

中文:
定理 MDifferentiableWithinAt.comp_of_eq
  证明: by
  subst hy; exact hg.comp _ hf h

Depends on / 依赖: hg.comp
-/
theorem MDifferentiableWithinAt.comp_of_eq
    {y : M'} (hg : MDiffAt[u] g y) (hf : MDiffAt[s] f x) (h : s subseteq f ⁻¹' u) (hy : f x = y) :
    MDiffAt[s] (g ∘ f) x := by
  subst hy; exact hg.comp _ hf h

/--
theorem `MDifferentiableWithinAt.comp_of_preimage_mem_nhdsWithin` / 定理 `MDifferentiableWithinAt.comp_of_preimage_mem_nhdsWithin`

English:
theorem MDifferentiableWithinAt.comp_of_preimage_mem_nhdsWithin
  proof: (hg.comp _ (hf.mono inter_subset_right) inter_subset_left).mono_of_mem_nhdsWithin
    (Filter.inter_mem h self_mem_nhdsWithin)

中文:
定理 MDifferentiableWithinAt.comp_of_preimage_mem_nhdsWithin
  证明: (hg.comp _ (hf.mono inter_subset_right) inter_subset_left).mono_of_mem_nhdsWithin
    (Filter.inter_mem h self_mem_nhdsWithin)

Depends on / 依赖: Filter, Filter.inter_mem, hf.mono, hg.comp, inter_mem, inter_subset_left, inter_subset_right, mono_of_mem_nhdsWithin, self_mem_nhdsWithin
-/
theorem MDifferentiableWithinAt.comp_of_preimage_mem_nhdsWithin
    (hg : MDiffAt[u] g (f x)) (hf : MDiffAt[s] f x) (h : f ⁻¹' u in 𝓝[s] x) : MDiffAt[s] (g ∘ f) x :=
  (hg.comp _ (hf.mono inter_subset_right) inter_subset_left).mono_of_mem_nhdsWithin
    (Filter.inter_mem h self_mem_nhdsWithin)

/--
theorem `MDifferentiableWithinAt.comp_of_preimage_mem_nhdsWithin_of_eq` / 定理 `MDifferentiableWithinAt.comp_of_preimage_mem_nhdsWithin_of_eq`

English:
theorem MDifferentiableWithinAt.comp_of_preimage_mem_nhdsWithin_of_eq
  proof: by
  subst hy; exact MDifferentiableWithinAt.comp_of_preimage_mem_nhdsWithin _ hg hf h

中文:
定理 MDifferentiableWithinAt.comp_of_preimage_mem_nhdsWithin_of_eq
  证明: by
  subst hy; exact MDifferentiableWithinAt.comp_of_preimage_mem_nhdsWithin _ hg hf h

Depends on / 依赖: MDifferentiableWithinAt, MDifferentiableWithinAt.comp_of_preimage_mem_nhdsWithin, comp_of_preimage_mem_nhdsWithin
-/
theorem MDifferentiableWithinAt.comp_of_preimage_mem_nhdsWithin_of_eq
    {y : M'} (hg : MDiffAt[u] g y) (hf : MDiffAt[s] f x) (h : f ⁻¹' u in 𝓝[s] x) (hy : f x = y) :
    MDifferentiableWithinAt I I'' (g ∘ f) s x := by
  subst hy; exact MDifferentiableWithinAt.comp_of_preimage_mem_nhdsWithin _ hg hf h

/--
theorem `MDifferentiableAt.comp` / 定理 `MDifferentiableAt.comp`

English:
theorem MDifferentiableAt.comp
  given: (hg : MDiffAt g (f x)) (hf : MDiffAt f x)
  statement: MDiffAt (g ∘ f) x
  proof: (hg.hasMFDerivAt.comp x hf.hasMFDerivAt).mdifferentiableAt

中文:
定理 MDifferentiableAt.comp
  条件: (hg : MDiffAt g (f x)) (hf : MDiffAt f x)
  结论: MDiffAt (g ∘ f) x
  证明: (hg.hasMFDerivAt.comp x hf.hasMFDerivAt).mdifferentiableAt

Depends on / 依赖: hasMFDerivAt, hf.hasMFDerivAt, hg.hasMFDerivAt.comp, mdifferentiableAt
-/
theorem MDifferentiableAt.comp (hg : MDiffAt g (f x)) (hf : MDiffAt f x) : MDiffAt (g ∘ f) x :=
  (hg.hasMFDerivAt.comp x hf.hasMFDerivAt).mdifferentiableAt

/--
theorem `MDifferentiableAt.comp_of_eq` / 定理 `MDifferentiableAt.comp_of_eq`

English:
theorem MDifferentiableAt.comp_of_eq
  given: {y : M'} (hg : MDiffAt g y) (hf : MDiffAt f x) (hy : f x = y)
  proof: by
  subst hy; exact hg.comp _ hf

中文:
定理 MDifferentiableAt.comp_of_eq
  条件: {y : M'} (hg : MDiffAt g y) (hf : MDiffAt f x) (hy : f x = y)
  证明: by
  subst hy; exact hg.comp _ hf

Depends on / 依赖: hg.comp
-/
theorem MDifferentiableAt.comp_of_eq {y : M'} (hg : MDiffAt g y) (hf : MDiffAt f x) (hy : f x = y) :
    MDiffAt (g ∘ f) x := by
  subst hy; exact hg.comp _ hf

/--
theorem `MDifferentiableAt.comp_mdifferentiableWithinAt` / 定理 `MDifferentiableAt.comp_mdifferentiableWithinAt`

English:
theorem MDifferentiableAt.comp_mdifferentiableWithinAt
  proof: by
  rw [← mdifferentiableWithinAt_univ] at hg
  exact hg.comp _ hf (by simp)

中文:
定理 MDifferentiableAt.comp_mdifferentiableWithinAt
  证明: by
  rw [← mdifferentiableWithinAt_univ] at hg
  exact hg.comp _ hf (by simp)

Depends on / 依赖: hg.comp, mdifferentiableWithinAt_univ
-/
theorem MDifferentiableAt.comp_mdifferentiableWithinAt
    (hg : MDiffAt g (f x)) (hf : MDiffAt[s] f x) : MDiffAt[s] (g ∘ f) x := by
  rw [← mdifferentiableWithinAt_univ] at hg
  exact hg.comp _ hf (by simp)

/--
theorem `MDifferentiableAt.comp_mdifferentiableWithinAt_of_eq` / 定理 `MDifferentiableAt.comp_mdifferentiableWithinAt_of_eq`

English:
theorem MDifferentiableAt.comp_mdifferentiableWithinAt_of_eq
  proof: by
  subst hy; exact hg.comp_mdifferentiableWithinAt _ hf

中文:
定理 MDifferentiableAt.comp_mdifferentiableWithinAt_of_eq
  证明: by
  subst hy; exact hg.comp_mdifferentiableWithinAt _ hf

Depends on / 依赖: comp_mdifferentiableWithinAt, hg.comp_mdifferentiableWithinAt
-/
theorem MDifferentiableAt.comp_mdifferentiableWithinAt_of_eq
    {y : M'} (hg : MDiffAt g y) (hf : MDiffAt[s] f x) (hy : f x = y) : MDiffAt[s] (g ∘ f) x := by
  subst hy; exact hg.comp_mdifferentiableWithinAt _ hf

/--
theorem `mfderivWithin_comp` / 定理 `mfderivWithin_comp`

English:
theorem mfderivWithin_comp
  proof: by
  apply HasMFDerivWithinAt.mfderivWithin _ hxs
  exact HasMFDerivWithinAt.comp x hg.hasMFDerivWithinAt hf.hasMFDerivWithinAt h

中文:
定理 mfderivWithin_comp
  证明: by
  apply HasMFDerivWithinAt.mfderivWithin _ hxs
  exact HasMFDerivWithinAt.comp x hg.hasMFDerivWithinAt hf.hasMFDerivWithinAt h

Depends on / 依赖: HasMFDerivWithinAt, HasMFDerivWithinAt.comp, HasMFDerivWithinAt.mfderivWithin, hasMFDerivWithinAt, hf.hasMFDerivWithinAt, hg.hasMFDerivWithinAt, mfderivWithin
-/
theorem mfderivWithin_comp
    (hg : MDiffAt[u] g (f x)) (hf : MDiffAt[s] f x) (h : s subseteq f ⁻¹' u) (hxs : UniqueMDiffAt[s] x) :
    mfderiv[s] (g ∘ f) x = (mfderiv[u] g (f x)).comp (mfderiv[s] f x) := by
  apply HasMFDerivWithinAt.mfderivWithin _ hxs
  exact HasMFDerivWithinAt.comp x hg.hasMFDerivWithinAt hf.hasMFDerivWithinAt h

/--
theorem `mfderivWithin_comp_of_eq` / 定理 `mfderivWithin_comp_of_eq`

English:
theorem mfderivWithin_comp_of_eq
  statement: {x : M} {y : M'} (hg : MDiffAt[u] g y)
  proof: by
  subst hy; exact mfderivWithin_comp x hg hf h hxs

中文:
定理 mfderivWithin_comp_of_eq
  结论: {x : M} {y : M'} (hg : MDiffAt[u] g y)
  证明: by
  subst hy; exact mfderivWithin_comp x hg hf h hxs

Depends on / 依赖: mfderivWithin_comp
-/
theorem mfderivWithin_comp_of_eq {x : M} {y : M'} (hg : MDiffAt[u] g y)
    (hf : MDiffAt[s] f x) (h : s subseteq f ⁻¹' u) (hxs : UniqueMDiffAt[s] x) (hy : f x = y) :
    mfderiv[s] (g ∘ f) x = (mfderiv[u] g y).comp (mfderiv[s] f x) := by
  subst hy; exact mfderivWithin_comp x hg hf h hxs

/--
theorem `mfderivWithin_comp_of_preimage_mem_nhdsWithin` / 定理 `mfderivWithin_comp_of_preimage_mem_nhdsWithin`

English:
theorem mfderivWithin_comp_of_preimage_mem_nhdsWithin
  statement: (hg : MDiffAt[u] g (f x))
  proof: by
  have A : s inter f ⁻¹' u in 𝓝[s] x := Filter.inter_mem self_mem_nhdsWithin h
  have B : mfderiv[s] (g ∘ f) x = mfderiv[s inter f ⁻¹' u] (g ∘ f) x := by
    apply MDifferentiableWithinAt.mfderivWithin_mono_of_mem_nhdsWithin _ hxs A
    exact hg.comp _ (hf.mono inter_subset_left) inter_subset_right
  have C : mfderiv[s] f x = mfderiv[s inter f ⁻¹' u] f x :=
    MDifferentiableWithinAt.mfderivWithin_mono_of_mem_nhdsWithin (hf.mono inter_subset_left) hxs A
  rw [B]; rw [C]
  exact mfderivWithin_comp _ hg (hf.mono inter_subset_left) inter_subset_right (hxs.inter' h)

中文:
定理 mfderivWithin_comp_of_preimage_mem_nhdsWithin
  结论: (hg : MDiffAt[u] g (f x))
  证明: by
  have A : s inter f ⁻¹' u in 𝓝[s] x := Filter.inter_mem self_mem_nhdsWithin h
  have B : mfderiv[s] (g ∘ f) x = mfderiv[s inter f ⁻¹' u] (g ∘ f) x := by
    apply MDifferentiableWithinAt.mfderivWithin_mono_of_mem_nhdsWithin _ hxs A
    exact hg.comp _ (hf.mono inter_subset_left) inter_subset_right
  have C : mfderiv[s] f x = mfderiv[s inter f ⁻¹' u] f x :=
    MDifferentiableWithinAt.mfderivWithin_mono_of_mem_nhdsWithin (hf.mono inter_subset_left) hxs A
  rw [B]; rw [C]
  exact mfderivWithin_comp _ hg (hf.mono inter_subset_left) inter_subset_right (hxs.inter' h)

Depends on / 依赖: Filter, Filter.inter_mem, MDifferentiableWithinAt, MDifferentiableWithinAt.mfderivWithin_mono_of_mem_nhdsWithin, hf.mono, hg.comp, inter_mem, inter_subset_left, inter_subset_right, mfderiv, mfderivWithin_comp, mfderivWithin_mono_of_mem_nhdsWithin, self_mem_nhdsWithin
-/
theorem mfderivWithin_comp_of_preimage_mem_nhdsWithin (hg : MDiffAt[u] g (f x))
    (hf : MDiffAt[s] f x) (h : f ⁻¹' u in 𝓝[s] x) (hxs : UniqueMDiffAt[s] x) :
    mfderiv[s] (g ∘ f) x = (mfderiv[u] g (f x)).comp (mfderiv[s] f x) := by
  have A : s inter f ⁻¹' u in 𝓝[s] x := Filter.inter_mem self_mem_nhdsWithin h
  have B : mfderiv[s] (g ∘ f) x = mfderiv[s inter f ⁻¹' u] (g ∘ f) x := by
    apply MDifferentiableWithinAt.mfderivWithin_mono_of_mem_nhdsWithin _ hxs A
    exact hg.comp _ (hf.mono inter_subset_left) inter_subset_right
  have C : mfderiv[s] f x = mfderiv[s inter f ⁻¹' u] f x :=
    MDifferentiableWithinAt.mfderivWithin_mono_of_mem_nhdsWithin (hf.mono inter_subset_left) hxs A
  rw [B]; rw [C]
  exact mfderivWithin_comp _ hg (hf.mono inter_subset_left) inter_subset_right (hxs.inter' h)

/--
theorem `mfderivWithin_comp_of_preimage_mem_nhdsWithin_of_eq` / 定理 `mfderivWithin_comp_of_preimage_mem_nhdsWithin_of_eq`

English:
theorem mfderivWithin_comp_of_preimage_mem_nhdsWithin_of_eq
  statement: {y : M'}
  proof: by
  subst hy; exact mfderivWithin_comp_of_preimage_mem_nhdsWithin _ hg hf h hxs

中文:
定理 mfderivWithin_comp_of_preimage_mem_nhdsWithin_of_eq
  结论: {y : M'}
  证明: by
  subst hy; exact mfderivWithin_comp_of_preimage_mem_nhdsWithin _ hg hf h hxs

Depends on / 依赖: mfderivWithin_comp_of_preimage_mem_nhdsWithin
-/
theorem mfderivWithin_comp_of_preimage_mem_nhdsWithin_of_eq {y : M'}
    (hg : MDiffAt[u] g y) (hf : MDiffAt[s] f x) (h : f ⁻¹' u in 𝓝[s] x) (hxs : UniqueMDiffAt[s] x)
    (hy : f x = y) : mfderiv[s] (g ∘ f) x = (mfderiv[u] g y).comp (mfderiv[s] f x) := by
  subst hy; exact mfderivWithin_comp_of_preimage_mem_nhdsWithin _ hg hf h hxs

/--
theorem `mfderiv_comp_mfderivWithin` / 定理 `mfderiv_comp_mfderivWithin`

English:
theorem mfderiv_comp_mfderivWithin
  statement: (hg : MDiffAt g (f x)) (hf : MDiffAt[s] f x)
  proof: by
  rw [← mfderivWithin_univ]
  exact mfderivWithin_comp _ hg.mdifferentiableWithinAt hf (by simp) hxs

中文:
定理 mfderiv_comp_mfderivWithin
  结论: (hg : MDiffAt g (f x)) (hf : MDiffAt[s] f x)
  证明: by
  rw [← mfderivWithin_univ]
  exact mfderivWithin_comp _ hg.mdifferentiableWithinAt hf (by simp) hxs

Depends on / 依赖: hg.mdifferentiableWithinAt, mdifferentiableWithinAt, mfderivWithin_comp, mfderivWithin_univ
-/
theorem mfderiv_comp_mfderivWithin (hg : MDiffAt g (f x)) (hf : MDiffAt[s] f x)
    (hxs : UniqueMDiffAt[s] x) :
    mfderiv[s] (g ∘ f) x = (mfderiv% g (f x)).comp (mfderiv[s] f x) := by
  rw [← mfderivWithin_univ]
  exact mfderivWithin_comp _ hg.mdifferentiableWithinAt hf (by simp) hxs

/--
theorem `mfderiv_comp_mfderivWithin_of_eq` / 定理 `mfderiv_comp_mfderivWithin_of_eq`

English:
theorem mfderiv_comp_mfderivWithin_of_eq
  statement: {x : M} {y : M'} (hg : MDiffAt g y)
  proof: by
  subst hy; exact mfderiv_comp_mfderivWithin x hg hf hxs

中文:
定理 mfderiv_comp_mfderivWithin_of_eq
  结论: {x : M} {y : M'} (hg : MDiffAt g y)
  证明: by
  subst hy; exact mfderiv_comp_mfderivWithin x hg hf hxs

Depends on / 依赖: mfderiv_comp_mfderivWithin
-/
theorem mfderiv_comp_mfderivWithin_of_eq {x : M} {y : M'} (hg : MDiffAt g y)
    (hf : MDiffAt[s] f x) (hxs : UniqueMDiffAt[s] x) (hy : f x = y) :
    mfderiv[s] (g ∘ f) x = (mfderiv% g y).comp (mfderiv[s] f x) := by
  subst hy; exact mfderiv_comp_mfderivWithin x hg hf hxs

/--
theorem `mfderiv_comp` / 定理 `mfderiv_comp`

English:
theorem mfderiv_comp
  given: (hg : MDiffAt g (f x)) (hf : MDiffAt f x)
  proof: by
  apply HasMFDerivAt.mfderiv
  exact HasMFDerivAt.comp x hg.hasMFDerivAt hf.hasMFDerivAt

中文:
定理 mfderiv_comp
  条件: (hg : MDiffAt g (f x)) (hf : MDiffAt f x)
  证明: by
  apply HasMFDerivAt.mfderiv
  exact HasMFDerivAt.comp x hg.hasMFDerivAt hf.hasMFDerivAt

Depends on / 依赖: HasMFDerivAt, HasMFDerivAt.comp, HasMFDerivAt.mfderiv, hasMFDerivAt, hf.hasMFDerivAt, hg.hasMFDerivAt, mfderiv
-/
theorem mfderiv_comp (hg : MDiffAt g (f x)) (hf : MDiffAt f x) :
    mfderiv% (g ∘ f) x = (mfderiv% g (f x)).comp (mfderiv% f x) := by
  apply HasMFDerivAt.mfderiv
  exact HasMFDerivAt.comp x hg.hasMFDerivAt hf.hasMFDerivAt

/--
theorem `mfderiv_comp_of_eq` / 定理 `mfderiv_comp_of_eq`

English:
theorem mfderiv_comp_of_eq
  given: {x : M} {y : M'} (hg : MDiffAt g y) (hf : MDiffAt f x) (hy : f x = y)
  proof: by
  subst hy; exact mfderiv_comp x hg hf

中文:
定理 mfderiv_comp_of_eq
  条件: {x : M} {y : M'} (hg : MDiffAt g y) (hf : MDiffAt f x) (hy : f x = y)
  证明: by
  subst hy; exact mfderiv_comp x hg hf

Depends on / 依赖: mfderiv_comp
-/
theorem mfderiv_comp_of_eq {x : M} {y : M'} (hg : MDiffAt g y) (hf : MDiffAt f x) (hy : f x = y) :
    mfderiv% (g ∘ f) x = (mfderiv% g (f x)).comp (mfderiv% f x) := by
  subst hy; exact mfderiv_comp x hg hf

/--
theorem `mfderiv_comp_apply` / 定理 `mfderiv_comp_apply`

English:
theorem mfderiv_comp_apply
  given: (hg : MDiffAt g (f x)) (hf : MDiffAt f x) (v : TangentSpace% x)
  proof: by
  rw [mfderiv_comp _ hg hf]
  rfl

中文:
定理 mfderiv_comp_apply
  条件: (hg : MDiffAt g (f x)) (hf : MDiffAt f x) (v : TangentSpace% x)
  证明: by
  rw [mfderiv_comp _ hg hf]
  rfl

Depends on / 依赖: mfderiv_comp
-/
theorem mfderiv_comp_apply (hg : MDiffAt g (f x)) (hf : MDiffAt f x) (v : TangentSpace% x) :
    mfderiv% (g ∘ f) x v = (mfderiv% g (f x)) ((mfderiv% f x) v) := by
  rw [mfderiv_comp _ hg hf]
  rfl

/--
theorem `mfderiv_comp_apply_of_eq` / 定理 `mfderiv_comp_apply_of_eq`

English:
theorem mfderiv_comp_apply_of_eq
  proof: by
  subst hy; exact mfderiv_comp_apply _ hg hf v

中文:
定理 mfderiv_comp_apply_of_eq
  证明: by
  subst hy; exact mfderiv_comp_apply _ hg hf v

Depends on / 依赖: mfderiv_comp_apply
-/
theorem mfderiv_comp_apply_of_eq
    {y : M'} (hg : MDiffAt g y) (hf : MDiffAt f x) (hy : f x = y) (v : TangentSpace% x) :
    mfderiv% (g ∘ f) x v = (mfderiv% g y) ((mfderiv% f x) v) := by
  subst hy; exact mfderiv_comp_apply _ hg hf v

/--
theorem `MDifferentiableOn.comp` / 定理 `MDifferentiableOn.comp`

English:
theorem MDifferentiableOn.comp
  given: (hg : MDiff[u] g) (hf : MDiff[s] f) (st : s subseteq f ⁻¹' u)
  proof: fun x hx =>
  MDifferentiableWithinAt.comp x (hg (f x) (st hx)) (hf x hx) st

中文:
定理 MDifferentiableOn.comp
  条件: (hg : MDiff[u] g) (hf : MDiff[s] f) (st : s subseteq f ⁻¹' u)
  证明: fun x hx =>
  MDifferentiableWithinAt.comp x (hg (f x) (st hx)) (hf x hx) st
-/
theorem MDifferentiableOn.comp (hg : MDiff[u] g) (hf : MDiff[s] f) (st : s subseteq f ⁻¹' u) :
    MDiff[s] (g ∘ f) := fun x hx =>
  MDifferentiableWithinAt.comp x (hg (f x) (st hx)) (hf x hx) st

/--
theorem `MDifferentiable.comp_mdifferentiableOn` / 定理 `MDifferentiable.comp_mdifferentiableOn`

English:
theorem MDifferentiable.comp_mdifferentiableOn
  given: (hg : MDiff g) (hf : MDiff[s] f)
  proof: by
  rw [← mdifferentiableOn_univ] at hg
  exact hg.comp hf (by simp)

中文:
定理 MDifferentiable.comp_mdifferentiableOn
  条件: (hg : MDiff g) (hf : MDiff[s] f)
  证明: by
  rw [← mdifferentiableOn_univ] at hg
  exact hg.comp hf (by simp)

Depends on / 依赖: addMonoidHom, f.map_smul, f.map_zero, f.toAddMonoidHom, hg.comp, mapRange, mapRange.addMonoidHom, mapRange_smul, map_smul, map_zero, mdifferentiableOn_univ, toAddMonoidHom
-/
theorem MDifferentiable.comp_mdifferentiableOn (hg : MDiff g) (hf : MDiff[s] f) :
    MDiff[s] (g ∘ f) := by
  rw [← mdifferentiableOn_univ] at hg
  exact hg.comp hf (by simp)

/--
theorem `MDifferentiable.comp` / 定理 `MDifferentiable.comp`

English:
theorem MDifferentiable.comp
  given: (hg : MDiff g) (hf : MDiff f)
  statement: MDiff (g ∘ f)
  proof: fun x => MDifferentiableAt.comp x (hg (f x)) (hf x)

中文:
定理 MDifferentiable.comp
  条件: (hg : MDiff g) (hf : MDiff f)
  结论: MDiff (g ∘ f)
  证明: fun x => MDifferentiableAt.comp x (hg (f x)) (hf x)

Depends on / 依赖: LinearMap, LinearMap.ext, MDifferentiableAt, MDifferentiableAt.comp, mapRange_id
-/
theorem MDifferentiable.comp (hg : MDiff g) (hf : MDiff f) : MDiff (g ∘ f) :=
  fun x => MDifferentiableAt.comp x (hg (f x)) (hf x)

/--
theorem `tangentMapWithin_comp_at` / 定理 `tangentMapWithin_comp_at`

English:
theorem tangentMapWithin_comp_at
  statement: (p : TangentBundle I M) (hg : MDiffAt[u] g (f p.1))
  proof: by
  simp only [tangentMapWithin, mfld_simps]
  rw [mfderivWithin_comp p.1 hg hf h hps]
  rfl

中文:
定理 tangentMapWithin_comp_at
  结论: (p : 切丛 I M) (hg : MDiffAt[u] g (f p.1))
  证明: by
  simp only [tangentMapWithin, mfld_simps]
  rw [mfderivWithin_comp p.1 hg hf h hps]
  rfl

Depends on / 依赖: LinearMap, LinearMap.ext, f.map_zero, mapRange_comp, map_zero, mfderivWithin_comp, mfld_simps, tangentMapWithin
-/
theorem tangentMapWithin_comp_at (p : TangentBundle I M) (hg : MDiffAt[u] g (f p.1))
    (hf : MDiffAt[s] f p.1) (h : s subseteq f ⁻¹' u) (hps : UniqueMDiffAt[s] p.1) :
    tangentMap[s] (g ∘ f) p = tangentMap[u] g (tangentMap[s] f p) := by
  simp only [tangentMapWithin, mfld_simps]
  rw [mfderivWithin_comp p.1 hg hf h hps]
  rfl

/--
theorem `tangentMap_comp_at` / 定理 `tangentMap_comp_at`

English:
theorem tangentMap_comp_at
  given: (p : TangentBundle I M) (hg : MDiffAt g (f p.1)) (hf : MDiffAt f p.1)
  proof: by
  simp only [tangentMap, mfld_simps]
  rw [mfderiv_comp p.1 hg hf]
  rfl

中文:
定理 tangentMap_comp_at
  条件: (p : 切丛 I M) (hg : MDiffAt g (f p.1)) (hf : MDiffAt f p.1)
  证明: by
  simp only [tangentMap, mfld_simps]
  rw [mfderiv_comp p.1 hg hf]
  rfl

Depends on / 依赖: mfderiv_comp, mfld_simps, tangentMap
-/
theorem tangentMap_comp_at (p : TangentBundle I M) (hg : MDiffAt g (f p.1)) (hf : MDiffAt f p.1) :
    tangentMap% (g ∘ f) p = tangentMap% g (tangentMap% f p) := by
  simp only [tangentMap, mfld_simps]
  rw [mfderiv_comp p.1 hg hf]
  rfl

/--
theorem `tangentMap_comp` / 定理 `tangentMap_comp`

English:
theorem tangentMap_comp
  given: (hg : MDiff g) (hf : MDiff f)
  proof: by
  ext p : 1; exact tangentMap_comp_at _ (hg _) (hf _)

中文:
定理 tangentMap_comp
  条件: (hg : MDiff g) (hf : MDiff f)
  证明: by
  ext p : 1; exact tangentMap_comp_at _ (hg _) (hf _)

Depends on / 依赖: addEquiv, e.map_zero, e.symm, e.symm.map_zero, e.toAddEquiv, e.toLinearMap, invFun, linearMap, mapRange, mapRange.addEquiv, mapRange.linearMap, map_zero, tangentMap_comp_at, toAddEquiv, toLinearMap
-/
theorem tangentMap_comp (hg : MDiff g) (hf : MDiff f) :
    tangentMap% (g ∘ f) = tangentMap% g ∘ tangentMap% f := by
  ext p : 1; exact tangentMap_comp_at _ (hg _) (hf _)

end DerivativesProperties
