/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Defs

/-!
## Basic properties of `C^n` functions between manifolds

In this file, we show that standard operations on `C^n` maps between manifolds are `C^n` :
* `ContMDiffOn.comp` gives the invariance of the `Cⁿ` property under composition
* `contMDiff_id` gives the smoothness of the identity
* `contMDiff_const` gives the smoothness of constant functions
* `contMDiff_inclusion` shows that the inclusion between open sets of a topological space is `C^n`
* `contMDiff_isOpenEmbedding` shows that if `M` has a `ChartedSpace` structure induced by an open
  embedding `e : M → H`, then `e` is `C^n`.

## Tags
chain rule, manifolds, higher derivative

-/

public section

assert_not_exists mfderiv

open Filter Function Set Topology
open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  -- declare the prerequisites for a charted space `M` over the pair `(E, H)`.
  {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M]
  -- declare the prerequisites for a charted space `M'` over the pair `(E', H')`.
  {E' : Type*}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M' : Type*} [TopologicalSpace M']
  -- declare the prerequisites for a charted space `M''` over the pair `(E'', H'')`.
  {E'' : Type*}
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] {H'' : Type*} [TopologicalSpace H'']
  {I'' : ModelWithCorners 𝕜 E'' H''} {M'' : Type*} [TopologicalSpace M'']

section ChartedSpace
variable [ChartedSpace H M] [ChartedSpace H' M'] [ChartedSpace H'' M'']
  -- declare functions, sets, points and smoothness indices
  {f : M -> M'} {s : Set M} {x : M} {n : Nat∞ω}

/-! ### Regularity of the composition of `C^n` functions between manifolds -/

section Composition

/--
theorem `ContMDiffWithinAt.comp` / 定理 `ContMDiffWithinAt.comp`

English:
theorem ContMDiffWithinAt.comp
  statement: {t : Set M'} {g : M' -> M''} (x : M)
  proof: by
  rw [contMDiffWithinAt_iff] at hg hf ⊢
  refine ⟨hg.1.comp hf.1 st, ?_⟩
  set e := extChartAt I x
  set e' := extChartAt I' (f x)
  have : e' (f x) = (writtenInExtChartAt I I' x f) (e x) := by simp only [e, e', mfld_simps]
  rw [this] at hg
  have A : forallᶠ y in 𝓝[e.symm ⁻¹' s inter range I] e

中文:
定理 ContMDiffWithinAt.comp
  结论: {t : 集合 M'} {g : M' -> M''} (x : M)
  证明: by
  rw [contMDiffWithinAt_iff] at hg hf ⊢
  refine ⟨hg.1.comp hf.1 st, ?_⟩
  set e := extChartAt I x
  set e' := extChartAt I' (f x)
  have : e' (f x) = (writtenInExtChartAt I I' x f) (e x) := by simp only [e, e', mfld_simps]
  rw [this] at hg
  have A : forallᶠ y in 𝓝[e.symm ⁻¹' s inter range I] e

Depends on / 依赖: contMDiffWithinAt_iff, e.symm, eventually_map, extChartAt, extChartAt_source_mem_nhds, filter_upwards, inter_mem_nhdsWithin, map_extChartAt_nhdsWithin, mfld_simps, source, tendsto, writtenInExtChartAt
-/
theorem ContMDiffWithinAt.comp {t : Set M'} {g : M' -> M''} (x : M)
    (hg : ContMDiffWithinAt I' I'' n g t (f x)) (hf : ContMDiffWithinAt I I' n f s x)
    (st : MapsTo f s t) : ContMDiffWithinAt I I'' n (g ∘ f) s x := by
  rw [contMDiffWithinAt_iff] at hg hf ⊢
  refine ⟨hg.1.comp hf.1 st, ?_⟩
  set e := extChartAt I x
  set e' := extChartAt I' (f x)
  have : e' (f x) = (writtenInExtChartAt I I' x f) (e x) := by simp only [e, e', mfld_simps]
  rw [this] at hg
  have A : forallᶠ y in 𝓝[e.symm ⁻¹' s inter range I] e x, f (e.symm y) in t ∧ f (e.symm y) in e'.source := by
    simp only [e, ← map_extChartAt_nhdsWithin, eventually_map]
    filter_upwards [hf.1.tendsto (extChartAt_source_mem_nhds (I := I') (f x)),
      inter_mem_nhdsWithin s (extChartAt_source_mem_nhds (I := I) x)]
    rintro x' (hfx' : f x' in e'.source) ⟨hx's, hx'⟩
    simp only [e, true_and, e.left_inv hx', st hx's, *]
  refine ((hg.2.comp _ (hf.2.mono inter_subset_right)
      ((mapsTo_preimage _ _).mono_left inter_subset_left)).mono_of_mem_nhdsWithin
      (inter_mem ?_ self_mem_nhdsWithin)).congr_of_eventuallyEq ?_ ?_
  · filter_upwards [A]
    rintro x' ⟨ht, hfx'⟩
    simp only [*, e, e', mem_preimage, writtenInExtChartAt, (· ∘ ·), mem_inter_iff, e'.left_inv,
      true_and]
    exact mem_range_self _
  · filter_upwards [A]
    rintro x' ⟨-, hfx'⟩
    simp only [*, e, e', (· ∘ ·), writtenInExtChartAt, e'.left_inv]
  · simp only [e, e', writtenInExtChartAt, (· ∘ ·), mem_extChartAt_source,
      e.left_inv, e'.left_inv]

/--
theorem `ContMDiffWithinAt.comp_of_eq` / 定理 `ContMDiffWithinAt.comp_of_eq`

English:
theorem ContMDiffWithinAt.comp_of_eq
  statement: {t : Set M'} {g : M' -> M''} {x : M} {y : M'}
  proof: by
  subst hx; exact hg.comp x hf st

中文:
定理 ContMDiffWithinAt.comp_of_eq
  结论: {t : 集合 M'} {g : M' -> M''} {x : M} {y : M'}
  证明: by
  subst hx; exact hg.comp x hf st

Depends on / 依赖: hg.comp
-/
theorem ContMDiffWithinAt.comp_of_eq {t : Set M'} {g : M' -> M''} {x : M} {y : M'}
    (hg : ContMDiffWithinAt I' I'' n g t y) (hf : ContMDiffWithinAt I I' n f s x)
    (st : MapsTo f s t) (hx : f x = y) : ContMDiffWithinAt I I'' n (g ∘ f) s x := by
  subst hx; exact hg.comp x hf st

/--
theorem `ContMDiffOn.comp` / 定理 `ContMDiffOn.comp`

English:
theorem ContMDiffOn.comp
  statement: {t : Set M'} {g : M' -> M''} (hg : ContMDiffOn I' I'' n g t)
  proof: fun x hx =>
  (hg _ (st hx)).comp x (hf x hx) st

中文:
定理 ContMDiffOn.comp
  结论: {t : 集合 M'} {g : M' -> M''} (hg : ContMDiffOn I' I'' n g t)
  证明: fun x hx =>
  (hg _ (st hx)).comp x (hf x hx) st
-/
theorem ContMDiffOn.comp {t : Set M'} {g : M' -> M''} (hg : ContMDiffOn I' I'' n g t)
    (hf : ContMDiffOn I I' n f s) (st : s subseteq f ⁻¹' t) : ContMDiffOn I I'' n (g ∘ f) s := fun x hx =>
  (hg _ (st hx)).comp x (hf x hx) st

/--
theorem `ContMDiffOn.comp'` / 定理 `ContMDiffOn.comp'`

English:
theorem ContMDiffOn.comp'
  statement: {t : Set M'} {g : M' -> M''} (hg : ContMDiffOn I' I'' n g t)
  proof: hg.comp (hf.mono inter_subset_left) inter_subset_right

中文:
定理 ContMDiffOn.comp'
  结论: {t : 集合 M'} {g : M' -> M''} (hg : ContMDiffOn I' I'' n g t)
  证明: hg.comp (hf.mono inter_subset_left) inter_subset_right

Depends on / 依赖: hf.mono, hg.comp, inter_subset_left, inter_subset_right
-/
theorem ContMDiffOn.comp' {t : Set M'} {g : M' -> M''} (hg : ContMDiffOn I' I'' n g t)
    (hf : ContMDiffOn I I' n f s) : ContMDiffOn I I'' n (g ∘ f) (s inter f ⁻¹' t) :=
  hg.comp (hf.mono inter_subset_left) inter_subset_right

/--
theorem `ContMDiff.comp` / 定理 `ContMDiff.comp`

English:
theorem ContMDiff.comp
  given: {g : M' -> M''} (hg : ContMDiff I' I'' n g) (hf : ContMDiff I I' n f)
  proof: by
  rw [← contMDiffOn_univ] at hf hg ⊢
  exact hg.comp hf subset_preimage_univ

中文:
定理 ContMDiff.comp
  条件: {g : M' -> M''} (hg : ContMDiff I' I'' n g) (hf : ContMDiff I I' n f)
  证明: by
  rw [← contMDiffOn_univ] at hf hg ⊢
  exact hg.comp hf subset_preimage_univ

Depends on / 依赖: contMDiffOn_univ, hg.comp, subset_preimage_univ
-/
theorem ContMDiff.comp {g : M' -> M''} (hg : ContMDiff I' I'' n g) (hf : ContMDiff I I' n f) :
    ContMDiff I I'' n (g ∘ f) := by
  rw [← contMDiffOn_univ] at hf hg ⊢
  exact hg.comp hf subset_preimage_univ

/--
theorem `ContMDiffWithinAt.comp'` / 定理 `ContMDiffWithinAt.comp'`

English:
theorem ContMDiffWithinAt.comp'
  statement: {t : Set M'} {g : M' -> M''} (x : M)
  proof: hg.comp x (hf.mono inter_subset_left) inter_subset_right

中文:
定理 ContMDiffWithinAt.comp'
  结论: {t : 集合 M'} {g : M' -> M''} (x : M)
  证明: hg.comp x (hf.mono inter_subset_left) inter_subset_right

Depends on / 依赖: hf.mono, hg.comp, inter_subset_left, inter_subset_right
-/
theorem ContMDiffWithinAt.comp' {t : Set M'} {g : M' -> M''} (x : M)
    (hg : ContMDiffWithinAt I' I'' n g t (f x)) (hf : ContMDiffWithinAt I I' n f s x) :
    ContMDiffWithinAt I I'' n (g ∘ f) (s inter f ⁻¹' t) x :=
  hg.comp x (hf.mono inter_subset_left) inter_subset_right

/--
theorem `ContMDiffAt.comp_contMDiffWithinAt` / 定理 `ContMDiffAt.comp_contMDiffWithinAt`

English:
theorem ContMDiffAt.comp_contMDiffWithinAt
  statement: {g : M' -> M''} (x : M)
  proof: hg.comp x hf (mapsTo_univ _ _)

中文:
定理 ContMDiffAt.comp_contMDiffWithinAt
  结论: {g : M' -> M''} (x : M)
  证明: hg.comp x hf (mapsTo_univ _ _)

Depends on / 依赖: hg.comp, mapsTo_univ
-/
theorem ContMDiffAt.comp_contMDiffWithinAt {g : M' -> M''} (x : M)
    (hg : ContMDiffAt I' I'' n g (f x)) (hf : ContMDiffWithinAt I I' n f s x) :
    ContMDiffWithinAt I I'' n (g ∘ f) s x :=
  hg.comp x hf (mapsTo_univ _ _)

/--
theorem `ContMDiffAt.comp_contMDiffWithinAt_of_eq` / 定理 `ContMDiffAt.comp_contMDiffWithinAt_of_eq`

English:
theorem ContMDiffAt.comp_contMDiffWithinAt_of_eq
  statement: {g : M' -> M''} {x : M} {y : M'}
  proof: by
  subst hx; exact hg.comp_contMDiffWithinAt x hf

中文:
定理 ContMDiffAt.comp_contMDiffWithinAt_of_eq
  结论: {g : M' -> M''} {x : M} {y : M'}
  证明: by
  subst hx; exact hg.comp_contMDiffWithinAt x hf

Depends on / 依赖: comp_contMDiffWithinAt, hg.comp_contMDiffWithinAt
-/
theorem ContMDiffAt.comp_contMDiffWithinAt_of_eq {g : M' -> M''} {x : M} {y : M'}
    (hg : ContMDiffAt I' I'' n g y) (hf : ContMDiffWithinAt I I' n f s x) (hx : f x = y) :
    ContMDiffWithinAt I I'' n (g ∘ f) s x := by
  subst hx; exact hg.comp_contMDiffWithinAt x hf

/-- The composition of `C^n` functions at points is `C^n`. -/
nonrec theorem ContMDiffAt.comp {g : M' -> M''} (x : M) (hg : ContMDiffAt I' I'' n g (f x))
    (hf : ContMDiffAt I I' n f x) : ContMDiffAt I I'' n (g ∘ f) x :=
  hg.comp x hf (mapsTo_univ _ _)

/--
theorem `ContMDiffAt.comp_of_eq` / 定理 `ContMDiffAt.comp_of_eq`

English:
theorem ContMDiffAt.comp_of_eq
  statement: {g : M' -> M''} {x : M} {y : M'} (hg : ContMDiffAt I' I'' n g y)
  proof: by
  subst hx; exact hg.comp x hf

中文:
定理 ContMDiffAt.comp_of_eq
  结论: {g : M' -> M''} {x : M} {y : M'} (hg : ContMDiffAt I' I'' n g y)
  证明: by
  subst hx; exact hg.comp x hf

Depends on / 依赖: hg.comp
-/
theorem ContMDiffAt.comp_of_eq {g : M' -> M''} {x : M} {y : M'} (hg : ContMDiffAt I' I'' n g y)
    (hf : ContMDiffAt I I' n f x) (hx : f x = y) : ContMDiffAt I I'' n (g ∘ f) x := by
  subst hx; exact hg.comp x hf

/--
theorem `ContMDiff.comp_contMDiffOn` / 定理 `ContMDiff.comp_contMDiffOn`

English:
theorem ContMDiff.comp_contMDiffOn
  statement: {f : M -> M'} {g : M' -> M''} {s : Set M}
  proof: hg.contMDiffOn.comp hf Set.subset_preimage_univ

中文:
定理 ContMDiff.comp_contMDiffOn
  结论: {f : M -> M'} {g : M' -> M''} {s : 集合 M}
  证明: hg.contMDiffOn.comp hf Set.subset_preimage_univ

Depends on / 依赖: Set.subset_preimage_univ, contMDiffOn, hg.contMDiffOn.comp, subset_preimage_univ
-/
theorem ContMDiff.comp_contMDiffOn {f : M -> M'} {g : M' -> M''} {s : Set M}
    (hg : ContMDiff I' I'' n g) (hf : ContMDiffOn I I' n f s) : ContMDiffOn I I'' n (g ∘ f) s :=
  hg.contMDiffOn.comp hf Set.subset_preimage_univ

/--
theorem `ContMDiffOn.comp_contMDiff` / 定理 `ContMDiffOn.comp_contMDiff`

English:
theorem ContMDiffOn.comp_contMDiff
  statement: {t : Set M'} {g : M' -> M''} (hg : ContMDiffOn I' I'' n g t)
  proof: contMDiffOn_univ.mp hg.comp hf.contMDiffOn fun x _ => ht x

中文:
定理 ContMDiffOn.comp_contMDiff
  结论: {t : 集合 M'} {g : M' -> M''} (hg : ContMDiffOn I' I'' n g t)
  证明: contMDiffOn_univ.mp hg.comp hf.contMDiffOn fun x _ => ht x

Depends on / 依赖: contMDiffOn, contMDiffOn_univ, contMDiffOn_univ.mp, hf.contMDiffOn, hg.comp
-/
theorem ContMDiffOn.comp_contMDiff {t : Set M'} {g : M' -> M''} (hg : ContMDiffOn I' I'' n g t)
    (hf : ContMDiff I I' n f) (ht : forall x, f x in t) : ContMDiff I I'' n (g ∘ f) :=
contMDiffOn_univ.mp hg.comp hf.contMDiffOn fun x _ => ht x

end Composition

/-! ### The identity is `C^n` -/

section id

/--
theorem `contMDiff_id` / 定理 `contMDiff_id`

English:
theorem contMDiff_id
  statement: ContMDiff I I n (id : M -> M)
  proof: ContMDiff.of_le
    ((contDiffWithinAt_localInvariantProp ⊤).liftProp_id contDiffWithinAtProp_id) le_top

中文:
定理 contMDiff_id
  结论: ContMDiff I I n (id : M -> M)
  证明: ContMDiff.of_le
    ((contDiffWithinAt_localInvariantProp ⊤).liftProp_id contDiffWithinAtProp_id) le_top

Depends on / 依赖: ContMDiff, ContMDiff.of_le, contDiffWithinAtProp_id, contDiffWithinAt_localInvariantProp, le_top, liftProp_id, of_le
-/
theorem contMDiff_id : ContMDiff I I n (id : M -> M) :=
  ContMDiff.of_le
    ((contDiffWithinAt_localInvariantProp ⊤).liftProp_id contDiffWithinAtProp_id) le_top

/--
theorem `contMDiffOn_id` / 定理 `contMDiffOn_id`

English:
theorem contMDiffOn_id
  statement: ContMDiffOn I I n (id : M -> M) s
  proof: contMDiff_id.contMDiffOn

中文:
定理 contMDiffOn_id
  结论: ContMDiffOn I I n (id : M -> M) s
  证明: contMDiff_id.contMDiffOn

Depends on / 依赖: contMDiffOn, contMDiff_id, contMDiff_id.contMDiffOn
-/
theorem contMDiffOn_id : ContMDiffOn I I n (id : M -> M) s :=
  contMDiff_id.contMDiffOn

/--
theorem `contMDiffAt_id` / 定理 `contMDiffAt_id`

English:
theorem contMDiffAt_id
  statement: ContMDiffAt I I n (id : M -> M) x
  proof: contMDiff_id.contMDiffAt

中文:
定理 contMDiffAt_id
  结论: ContMDiffAt I I n (id : M -> M) x
  证明: contMDiff_id.contMDiffAt

Depends on / 依赖: contMDiffAt, contMDiff_id, contMDiff_id.contMDiffAt
-/
theorem contMDiffAt_id : ContMDiffAt I I n (id : M -> M) x :=
  contMDiff_id.contMDiffAt

/--
theorem `contMDiffWithinAt_id` / 定理 `contMDiffWithinAt_id`

English:
theorem contMDiffWithinAt_id
  statement: ContMDiffWithinAt I I n (id : M -> M) s x
  proof: contMDiffAt_id.contMDiffWithinAt

中文:
定理 contMDiffWithinAt_id
  结论: ContMDiffWithinAt I I n (id : M -> M) s x
  证明: contMDiffAt_id.contMDiffWithinAt

Depends on / 依赖: contMDiffAt_id, contMDiffAt_id.contMDiffWithinAt, contMDiffWithinAt
-/
theorem contMDiffWithinAt_id : ContMDiffWithinAt I I n (id : M -> M) s x :=
  contMDiffAt_id.contMDiffWithinAt

end id

/-! ### Iterated functions -/

section Iterate

/--
theorem `ContMDiffOn.iterate` / 定理 `ContMDiffOn.iterate`

English:
theorem ContMDiffOn.iterate
  statement: {f : M -> M} (hf : ContMDiffOn I I n f s)
  proof: by
  induction k with
  | zero => simpa using contMDiffOn_id
  | succ k h => simpa using h.comp hf hmaps

中文:
定理 ContMDiffOn.iterate
  结论: {f : M -> M} (hf : ContMDiffOn I I n f s)
  证明: by
  induction k with
  | zero => simpa using contMDiffOn_id
  | succ k h => simpa using h.comp hf hmaps

Depends on / 依赖: contMDiffOn_id, h.comp
-/
theorem ContMDiffOn.iterate {f : M -> M} (hf : ContMDiffOn I I n f s)
    (hmaps : Set.MapsTo f s s) (k : Nat) :
    ContMDiffOn I I n (f^[k]) s := by
  induction k with
  | zero => simpa using contMDiffOn_id
  | succ k h => simpa using h.comp hf hmaps

/--
theorem `ContMDiff.iterate` / 定理 `ContMDiff.iterate`

English:
theorem ContMDiff.iterate
  given: {f : M -> M} (hf : ContMDiff I I n f) (k : Nat)
  proof: contMDiffOn_univ.mp ((contMDiffOn_univ.mpr hf).iterate (univ.mapsTo_univ f) k)

中文:
定理 ContMDiff.iterate
  条件: {f : M -> M} (hf : ContMDiff I I n f) (k : 自然数)
  证明: contMDiffOn_univ.mp ((contMDiffOn_univ.mpr hf).iterate (univ.mapsTo_univ f) k)

Depends on / 依赖: contMDiffOn_univ, contMDiffOn_univ.mp, contMDiffOn_univ.mpr, iterate, mapsTo_univ, univ.mapsTo_univ
-/
theorem ContMDiff.iterate {f : M -> M} (hf : ContMDiff I I n f) (k : Nat) :
    ContMDiff I I n (f^[k]) :=
  contMDiffOn_univ.mp ((contMDiffOn_univ.mpr hf).iterate (univ.mapsTo_univ f) k)

end Iterate

/-! ### Constants are `C^n` -/

section const
variable {c : M'}

/--
theorem `contMDiff_const` / 定理 `contMDiff_const`

English:
theorem contMDiff_const
  statement: ContMDiff I I' n fun _ : M => c
  proof: by
  intro x
  refine ⟨by fun_prop, ?_⟩
  simp only [ContDiffWithinAtProp, Function.comp_def]
  exact contDiffWithinAt_const

@[to_additive]

中文:
定理 contMDiff_const
  结论: ContMDiff I I' n fun _ : M => c
  证明: by
  intro x
  refine ⟨by fun_prop, ?_⟩
  simp only [ContDiffWithinAtProp, Function.comp_def]
  exact contDiffWithinAt_const

@[to_additive]

Depends on / 依赖: ContDiffWithinAtProp, Function, Function.comp_def, comp_def, contDiffWithinAt_const, fun_prop
-/
theorem contMDiff_const : ContMDiff I I' n fun _ : M => c := by
  intro x
  refine ⟨by fun_prop, ?_⟩
  simp only [ContDiffWithinAtProp, Function.comp_def]
  exact contDiffWithinAt_const

@[to_additive]
/--
theorem `contMDiff_one` / 定理 `contMDiff_one`

English:
theorem contMDiff_one
  given: [One M']
  statement: ContMDiff I I' n (1 : M -> M')
  proof: by
  simp only [Pi.one_def, contMDiff_const]

中文:
定理 contMDiff_one
  条件: [幺 M']
  结论: ContMDiff I I' n (1 : M -> M')
  证明: by
  simp only [Pi.one_def, contMDiff_const]

Depends on / 依赖: Pi.one_def, contMDiff_const, one_def
-/
theorem contMDiff_one [One M'] : ContMDiff I I' n (1 : M -> M') := by
  simp only [Pi.one_def, contMDiff_const]

/--
theorem `contMDiffOn_const` / 定理 `contMDiffOn_const`

English:
theorem contMDiffOn_const
  statement: ContMDiffOn I I' n (fun _ : M => c) s
  proof: contMDiff_const.contMDiffOn

@[to_additive]

中文:
定理 contMDiffOn_const
  结论: ContMDiffOn I I' n (fun _ : M => c) s
  证明: contMDiff_const.contMDiffOn

@[to_additive]

Depends on / 依赖: contMDiffOn, contMDiff_const, contMDiff_const.contMDiffOn
-/
theorem contMDiffOn_const : ContMDiffOn I I' n (fun _ : M => c) s :=
  contMDiff_const.contMDiffOn

@[to_additive]
/--
theorem `contMDiffOn_one` / 定理 `contMDiffOn_one`

English:
theorem contMDiffOn_one
  given: [One M']
  statement: ContMDiffOn I I' n (1 : M -> M') s
  proof: contMDiff_one.contMDiffOn

中文:
定理 contMDiffOn_one
  条件: [幺 M']
  结论: ContMDiffOn I I' n (1 : M -> M') s
  证明: contMDiff_one.contMDiffOn

Depends on / 依赖: contMDiffOn, contMDiff_one, contMDiff_one.contMDiffOn
-/
theorem contMDiffOn_one [One M'] : ContMDiffOn I I' n (1 : M -> M') s :=
  contMDiff_one.contMDiffOn

/--
theorem `contMDiffAt_const` / 定理 `contMDiffAt_const`

English:
theorem contMDiffAt_const
  statement: ContMDiffAt I I' n (fun _ : M => c) x
  proof: contMDiff_const.contMDiffAt

@[to_additive]

中文:
定理 contMDiffAt_const
  结论: ContMDiffAt I I' n (fun _ : M => c) x
  证明: contMDiff_const.contMDiffAt

@[to_additive]

Depends on / 依赖: contMDiffAt, contMDiff_const, contMDiff_const.contMDiffAt
-/
theorem contMDiffAt_const : ContMDiffAt I I' n (fun _ : M => c) x :=
  contMDiff_const.contMDiffAt

@[to_additive]
/--
theorem `contMDiffAt_one` / 定理 `contMDiffAt_one`

English:
theorem contMDiffAt_one
  given: [One M']
  statement: ContMDiffAt I I' n (1 : M -> M') x
  proof: contMDiff_one.contMDiffAt

中文:
定理 contMDiffAt_one
  条件: [幺 M']
  结论: ContMDiffAt I I' n (1 : M -> M') x
  证明: contMDiff_one.contMDiffAt

Depends on / 依赖: contMDiffAt, contMDiff_one, contMDiff_one.contMDiffAt
-/
theorem contMDiffAt_one [One M'] : ContMDiffAt I I' n (1 : M -> M') x :=
  contMDiff_one.contMDiffAt

/--
theorem `contMDiffWithinAt_const` / 定理 `contMDiffWithinAt_const`

English:
theorem contMDiffWithinAt_const
  statement: ContMDiffWithinAt I I' n (fun _ : M => c) s x
  proof: contMDiffAt_const.contMDiffWithinAt

@[to_additive]

中文:
定理 contMDiffWithinAt_const
  结论: ContMDiffWithinAt I I' n (fun _ : M => c) s x
  证明: contMDiffAt_const.contMDiffWithinAt

@[to_additive]

Depends on / 依赖: contMDiffAt_const, contMDiffAt_const.contMDiffWithinAt, contMDiffWithinAt
-/
theorem contMDiffWithinAt_const : ContMDiffWithinAt I I' n (fun _ : M => c) s x :=
  contMDiffAt_const.contMDiffWithinAt

@[to_additive]
/--
theorem `contMDiffWithinAt_one` / 定理 `contMDiffWithinAt_one`

English:
theorem contMDiffWithinAt_one
  given: [One M']
  statement: ContMDiffWithinAt I I' n (1 : M -> M') s x
  proof: contMDiffAt_const.contMDiffWithinAt

@[nontriviality]

中文:
定理 contMDiffWithinAt_one
  条件: [幺 M']
  结论: ContMDiffWithinAt I I' n (1 : M -> M') s x
  证明: contMDiffAt_const.contMDiffWithinAt

@[nontriviality]

Depends on / 依赖: contMDiffAt_const, contMDiffAt_const.contMDiffWithinAt, contMDiffWithinAt
-/
theorem contMDiffWithinAt_one [One M'] : ContMDiffWithinAt I I' n (1 : M -> M') s x :=
  contMDiffAt_const.contMDiffWithinAt

@[nontriviality]
/--
theorem `contMDiff_of_subsingleton` / 定理 `contMDiff_of_subsingleton`

English:
theorem contMDiff_of_subsingleton
  given: [Subsingleton M']
  statement: ContMDiff I I' n f
  proof: by
  intro x
  rw [Subsingleton.elim f fun _ => (f x)]
  exact contMDiffAt_const

@[nontriviality]

中文:
定理 contMDiff_of_subsingleton
  条件: [子单例 M']
  结论: ContMDiff I I' n f
  证明: by
  intro x
  rw [Subsingleton.elim f fun _ => (f x)]
  exact contMDiffAt_const

@[nontriviality]

Depends on / 依赖: Subsingleton, Subsingleton.elim, contMDiffAt_const
-/
theorem contMDiff_of_subsingleton [Subsingleton M'] : ContMDiff I I' n f := by
  intro x
  rw [Subsingleton.elim f fun _ => (f x)]
  exact contMDiffAt_const

@[nontriviality]
/--
theorem `contMDiffAt_of_subsingleton` / 定理 `contMDiffAt_of_subsingleton`

English:
theorem contMDiffAt_of_subsingleton
  given: [Subsingleton M']
  statement: ContMDiffAt I I' n f x
  proof: contMDiff_of_subsingleton.contMDiffAt

@[nontriviality]

中文:
定理 contMDiffAt_of_subsingleton
  条件: [子单例 M']
  结论: ContMDiffAt I I' n f x
  证明: contMDiff_of_subsingleton.contMDiffAt

@[nontriviality]

Depends on / 依赖: contMDiffAt, contMDiff_of_subsingleton, contMDiff_of_subsingleton.contMDiffAt
-/
theorem contMDiffAt_of_subsingleton [Subsingleton M'] : ContMDiffAt I I' n f x :=
  contMDiff_of_subsingleton.contMDiffAt

@[nontriviality]
/--
theorem `contMDiffWithinAt_of_subsingleton` / 定理 `contMDiffWithinAt_of_subsingleton`

English:
theorem contMDiffWithinAt_of_subsingleton
  given: [Subsingleton M']
  statement: ContMDiffWithinAt I I' n f s x
  proof: contMDiffAt_of_subsingleton.contMDiffWithinAt

@[nontriviality]

中文:
定理 contMDiffWithinAt_of_subsingleton
  条件: [子单例 M']
  结论: ContMDiffWithinAt I I' n f s x
  证明: contMDiffAt_of_subsingleton.contMDiffWithinAt

@[nontriviality]

Depends on / 依赖: contMDiffAt_of_subsingleton, contMDiffAt_of_subsingleton.contMDiffWithinAt, contMDiffWithinAt
-/
theorem contMDiffWithinAt_of_subsingleton [Subsingleton M'] : ContMDiffWithinAt I I' n f s x :=
  contMDiffAt_of_subsingleton.contMDiffWithinAt

@[nontriviality]
/--
theorem `contMDiffOn_of_subsingleton` / 定理 `contMDiffOn_of_subsingleton`

English:
theorem contMDiffOn_of_subsingleton
  given: [Subsingleton M']
  statement: ContMDiffOn I I' n f s
  proof: contMDiff_of_subsingleton.contMDiffOn

中文:
定理 contMDiffOn_of_subsingleton
  条件: [子单例 M']
  结论: ContMDiffOn I I' n f s
  证明: contMDiff_of_subsingleton.contMDiffOn

Depends on / 依赖: contMDiffOn, contMDiff_of_subsingleton, contMDiff_of_subsingleton.contMDiffOn
-/
theorem contMDiffOn_of_subsingleton [Subsingleton M'] : ContMDiffOn I I' n f s :=
  contMDiff_of_subsingleton.contMDiffOn

/--
lemma `contMDiff_of_discreteTopology` / 引理 `contMDiff_of_discreteTopology`

English:
lemma contMDiff_of_discreteTopology
  given: [DiscreteTopology M]
  proof: by
  intro x
  -- f is locally constant, and constant functions are smooth.
  apply contMDiff_const (c := f x).contMDiffAt.congr_of_eventuallyEq
  simp [EventuallyEq]

中文:
引理 contMDiff_of_discreteTopology
  条件: [离散拓扑 M]
  证明: by
  intro x
  -- f is locally constant, and constant functions are smooth.
  apply contMDiff_const (c := f x).contMDiffAt.congr_of_eventuallyEq
  simp [EventuallyEq]
-/
lemma contMDiff_of_discreteTopology [DiscreteTopology M] :
    ContMDiff I I' n f := by
  intro x
  -- f is locally constant, and constant functions are smooth.
  apply contMDiff_const (c := f x).contMDiffAt.congr_of_eventuallyEq
  simp [EventuallyEq]

end const

/-- `f` is continuously differentiable if it is cont. differentiable at
each `x ∈ mulTSupport f`. -/
@[to_additive /-- `f` is continuously differentiable if it is continuously
differentiable at each `x ∈ tsupport f`. See also `contMDiff_section_of_tsupport`
for a similar result for sections of vector bundles. -/]
/--
theorem `contMDiff_of_mulTSupport` / 定理 `contMDiff_of_mulTSupport`

English:
theorem contMDiff_of_mulTSupport
  statement: [One M'] {f : M -> M'}
  proof: by
  intro x
  by_cases hx : x in mulTSupport f
  · exact hf x hx
  · exact ContMDiffAt.congr_of_eventuallyEq contMDiffAt_const
      (notMem_mulTSupport_iff_eventuallyEq.1 hx)

@[to_additive contMDiffWithinAt_of_notMem]

中文:
定理 contMDiff_of_mulTSupport
  结论: [幺 M'] {f : M -> M'}
  证明: by
  intro x
  by_cases hx : x in mulTSupport f
  · exact hf x hx
  · exact ContMDiffAt.congr_of_eventuallyEq contMDiffAt_const
      (notMem_mulTSupport_iff_eventuallyEq.1 hx)

@[to_additive contMDiffWithinAt_of_notMem]

Depends on / 依赖: ContMDiffAt, ContMDiffAt.congr_of_eventuallyEq, congr_of_eventuallyEq, contMDiffAt_const, mulTSupport, notMem_mulTSupport_iff_eventuallyEq
-/
theorem contMDiff_of_mulTSupport [One M'] {f : M -> M'}
    (hf : forall x in mulTSupport f, ContMDiffAt I I' n f x) : ContMDiff I I' n f := by
  intro x
  by_cases hx : x in mulTSupport f
  · exact hf x hx
  · exact ContMDiffAt.congr_of_eventuallyEq contMDiffAt_const
      (notMem_mulTSupport_iff_eventuallyEq.1 hx)

@[to_additive contMDiffWithinAt_of_notMem]
/--
theorem `contMDiffWithinAt_of_notMem_mulTSupport` / 定理 `contMDiffWithinAt_of_notMem_mulTSupport`

English:
theorem contMDiffWithinAt_of_notMem_mulTSupport
  statement: {f : M -> M'} [One M'] {x : M}
  proof: by
  apply contMDiffWithinAt_const.congr_of_eventuallyEq
    (eventually_nhdsWithin_of_eventually_nhds <| notMem_mulTSupport_iff_eventuallyEq.mp hx)
    (image_eq_one_of_notMem_mulTSupport hx)

中文:
定理 contMDiffWithinAt_of_notMem_mulTSupport
  结论: {f : M -> M'} [幺 M'] {x : M}
  证明: by
  apply contMDiffWithinAt_const.congr_of_eventuallyEq
    (eventually_nhdsWithin_of_eventually_nhds <| notMem_mulTSupport_iff_eventuallyEq.mp hx)
    (image_eq_one_of_notMem_mulTSupport hx)

Depends on / 依赖: congr_of_eventuallyEq, contMDiffWithinAt_const, contMDiffWithinAt_const.congr_of_eventuallyEq, eventually_nhdsWithin_of_eventually_nhds, image_eq_one_of_notMem_mulTSupport, notMem_mulTSupport_iff_eventuallyEq, notMem_mulTSupport_iff_eventuallyEq.mp
-/
theorem contMDiffWithinAt_of_notMem_mulTSupport {f : M -> M'} [One M'] {x : M}
    (hx : x ∉ mulTSupport f) (n : Nat∞ω) (s : Set M) : ContMDiffWithinAt I I' n f s x := by
  apply contMDiffWithinAt_const.congr_of_eventuallyEq
    (eventually_nhdsWithin_of_eventually_nhds <| notMem_mulTSupport_iff_eventuallyEq.mp hx)
    (image_eq_one_of_notMem_mulTSupport hx)

/-- `f` is continuously differentiable at each point outside of its `mulTSupport`. -/
@[to_additive contMDiffAt_of_notMem]
/--
theorem `contMDiffAt_of_notMem_mulTSupport` / 定理 `contMDiffAt_of_notMem_mulTSupport`

English:
theorem contMDiffAt_of_notMem_mulTSupport
  statement: {f : M -> M'} [One M'] {x : M}
  proof: contMDiffWithinAt_of_notMem_mulTSupport hx n univ

中文:
定理 contMDiffAt_of_notMem_mulTSupport
  结论: {f : M -> M'} [幺 M'] {x : M}
  证明: contMDiffWithinAt_of_notMem_mulTSupport hx n univ

Depends on / 依赖: contMDiffWithinAt_of_notMem_mulTSupport
-/
theorem contMDiffAt_of_notMem_mulTSupport {f : M -> M'} [One M'] {x : M}
    (hx : x ∉ mulTSupport f) (n : Nat∞ω) : ContMDiffAt I I' n f x :=
  contMDiffWithinAt_of_notMem_mulTSupport hx n univ

/--
lemma `ContMDiff.piecewise` / 引理 `ContMDiff.piecewise`

English:
lemma ContMDiff.piecewise
  proof: by
  intro x
  by_cases hx : x in interior s
  · apply (hf x).congr_of_eventuallyEq
    filter_upwards [isOpen_interior.mem_nhds hx] with y hy
    rw [piecewise_eq_of_mem]
    apply interior_subset hy
  by_cases h'x : x in closure s
  · have : x in frontier s := ⟨h'x, hx⟩
    apply (hf x).congr_of_e

中文:
引理 ContMDiff.piecewise
  证明: by
  intro x
  by_cases hx : x in interior s
  · apply (hf x).congr_of_eventuallyEq
    filter_upwards [isOpen_interior.mem_nhds hx] with y hy
    rw [piecewise_eq_of_mem]
    apply interior_subset hy
  by_cases h'x : x in closure s
  · have : x in frontier s := ⟨h'x, hx⟩
    apply (hf x).congr_of_e

Depends on / 依赖: Set.piecewise, closure, congr_of_eventuallyEq, contrapose, filter_upwards, frontier, interior, interior_subset, isClosed_closure, isClosed_closure.isOpen_compl.mem_nhds, isOpen_compl, isOpen_interior, isOpen_interior.mem_nhds, mem_nhds, piecewise, piecewise_eq_of_mem, piecewise_eq_of_notMem
-/
lemma ContMDiff.piecewise
    {f g : M -> M'} {s : Set M} [DecidablePred (· in s)]
    (hf : ContMDiff I I' n f) (hg : ContMDiff I I' n g)
    (hfg : forall x in frontier s, f =ᶠ[𝓝 x] g) :
    ContMDiff I I' n (piecewise s f g) := by
  intro x
  by_cases hx : x in interior s
  · apply (hf x).congr_of_eventuallyEq
    filter_upwards [isOpen_interior.mem_nhds hx] with y hy
    rw [piecewise_eq_of_mem]
    apply interior_subset hy
  by_cases h'x : x in closure s
  · have : x in frontier s := ⟨h'x, hx⟩
    apply (hf x).congr_of_eventuallyEq
    filter_upwards [hfg x this] with y hy
    simp [Set.piecewise, hy]
  · apply (hg x).congr_of_eventuallyEq
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds h'x] with y hy
    rw [piecewise_eq_of_notMem]
    contrapose hy
    simpa using subset_closure hy

/--
lemma `ContMDiff.piecewise_Iic` / 引理 `ContMDiff.piecewise_Iic`

English:
lemma ContMDiff.piecewise_Iic
  proof: hf.piecewise hg (by simpa using hfg)

中文:
引理 ContMDiff.piecewise_Iic
  证明: hf.piecewise hg (by simpa using hfg)

Depends on / 依赖: hf.piecewise, piecewise
-/
lemma ContMDiff.piecewise_Iic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners Real E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {f g : Real -> M} {s : Real}
    (hf : ContMDiff 𝓘(Real) I n f) (hg : ContMDiff 𝓘(Real) I n g) (hfg : f =ᶠ[𝓝 s] g) :
    ContMDiff 𝓘(Real) I n (Set.piecewise (Iic s) f g) :=
  hf.piecewise hg (by simpa using hfg)

/-! ### Being `C^k` on a union of open sets can be tested on each set -/
section contMDiff_union

variable {s t : Set M}

/--
lemma `ContMDiffOn.union_of_isOpen` / 引理 `ContMDiffOn.union_of_isOpen`

English:
lemma ContMDiffOn.union_of_isOpen
  statement: (hf : ContMDiffOn I I' n f s) (hf' : ContMDiffOn I I' n f t)
  proof: by
  intro x hx
  obtain (hx | hx) := hx
.contMDiffWithinAt · exact (hf x hx).contMDiffAt (hs.mem_nhds hx)
.contMDiffWithinAt · exact (hf' x hx).contMDiffAt (ht.mem_nhds hx)

中文:
引理 ContMDiffOn.union_of_isOpen
  结论: (hf : ContMDiffOn I I' n f s) (hf' : ContMDiffOn I I' n f t)
  证明: by
  intro x hx
  obtain (hx | hx) := hx
.contMDiffWithinAt · exact (hf x hx).contMDiffAt (hs.mem_nhds hx)
.contMDiffWithinAt · exact (hf' x hx).contMDiffAt (ht.mem_nhds hx)

Depends on / 依赖: contMDiffAt, contMDiffWithinAt, hs.mem_nhds, ht.mem_nhds, mem_nhds
-/
lemma ContMDiffOn.union_of_isOpen (hf : ContMDiffOn I I' n f s) (hf' : ContMDiffOn I I' n f t)
    (hs : IsOpen s) (ht : IsOpen t) :
    ContMDiffOn I I' n f (s union t) := by
  intro x hx
  obtain (hx | hx) := hx
.contMDiffWithinAt · exact (hf x hx).contMDiffAt (hs.mem_nhds hx)
.contMDiffWithinAt · exact (hf' x hx).contMDiffAt (ht.mem_nhds hx)

/--
lemma `contMDiffOn_union_iff_of_isOpen` / 引理 `contMDiffOn_union_iff_of_isOpen`

English:
lemma contMDiffOn_union_iff_of_isOpen
  given: (hs : IsOpen s) (ht : IsOpen t)
  proof: ⟨fun h => ⟨h.mono subset_union_left, h.mono subset_union_right⟩,
   fun ⟨hfs, hft⟩ => ContMDiffOn.union_of_isOpen hfs hft hs ht⟩

中文:
引理 contMDiffOn_union_iff_of_isOpen
  条件: (hs : 是开集 s) (ht : 是开集 t)
  证明: ⟨fun h => ⟨h.mono subset_union_left, h.mono subset_union_right⟩,
   fun ⟨hfs, hft⟩ => ContMDiffOn.union_of_isOpen hfs hft hs ht⟩

Depends on / 依赖: ContMDiffOn, ContMDiffOn.union_of_isOpen, h.mono, subset_union_left, subset_union_right, union_of_isOpen
-/
lemma contMDiffOn_union_iff_of_isOpen (hs : IsOpen s) (ht : IsOpen t) :
    ContMDiffOn I I' n f (s union t) ↔ ContMDiffOn I I' n f s ∧ ContMDiffOn I I' n f t :=
  ⟨fun h => ⟨h.mono subset_union_left, h.mono subset_union_right⟩,
   fun ⟨hfs, hft⟩ => ContMDiffOn.union_of_isOpen hfs hft hs ht⟩

/--
lemma `contMDiff_of_contMDiffOn_union_of_isOpen` / 引理 `contMDiff_of_contMDiffOn_union_of_isOpen`

English:
lemma contMDiff_of_contMDiffOn_union_of_isOpen
  statement: (hf : ContMDiffOn I I' n f s)
  proof: by
  rw [← contMDiffOn_univ]; rw [← hst]
  exact hf.union_of_isOpen hf' hs ht

中文:
引理 contMDiff_of_contMDiffOn_union_of_isOpen
  结论: (hf : ContMDiffOn I I' n f s)
  证明: by
  rw [← contMDiffOn_univ]; rw [← hst]
  exact hf.union_of_isOpen hf' hs ht

Depends on / 依赖: contMDiffOn_univ, hf.union_of_isOpen, union_of_isOpen
-/
lemma contMDiff_of_contMDiffOn_union_of_isOpen (hf : ContMDiffOn I I' n f s)
    (hf' : ContMDiffOn I I' n f t) (hst : s union t = univ) (hs : IsOpen s) (ht : IsOpen t) :
    ContMDiff I I' n f := by
  rw [← contMDiffOn_univ]; rw [← hst]
  exact hf.union_of_isOpen hf' hs ht

/--
lemma `ContMDiffOn.iUnion_of_isOpen` / 引理 `ContMDiffOn.iUnion_of_isOpen`

English:
lemma ContMDiffOn.iUnion_of_isOpen
  statement: {ι : Type*} {s : ι -> Set M}
  proof: by
  rintro x ⟨si, ⟨i, rfl⟩, hxsi⟩
.contMDiffWithinAt exact (hf i).contMDiffAt ((hs i).mem_nhds hxsi)

中文:
引理 ContMDiffOn.iUnion_of_isOpen
  结论: {ι : 类型} {s : ι -> 集合 M}
  证明: by
  rintro x ⟨si, ⟨i, rfl⟩, hxsi⟩
.contMDiffWithinAt exact (hf i).contMDiffAt ((hs i).mem_nhds hxsi)

Depends on / 依赖: contMDiffAt, contMDiffWithinAt, mem_nhds
-/
lemma ContMDiffOn.iUnion_of_isOpen {ι : Type*} {s : ι -> Set M}
    (hf : forall i : ι, ContMDiffOn I I' n f (s i)) (hs : forall i, IsOpen (s i)) :
    ContMDiffOn I I' n f (⋃ i, s i) := by
  rintro x ⟨si, ⟨i, rfl⟩, hxsi⟩
.contMDiffWithinAt exact (hf i).contMDiffAt ((hs i).mem_nhds hxsi)

/--
lemma `contMDiffOn_iUnion_iff_of_isOpen` / 引理 `contMDiffOn_iUnion_iff_of_isOpen`

English:
lemma contMDiffOn_iUnion_iff_of_isOpen
  statement: {ι : Type*} {s : ι -> Set M}
  proof: ⟨fun h i => h.mono subset_iUnion_of_subset i fun _ a => a,
   fun h => ContMDiffOn.iUnion_of_isOpen h hs⟩

中文:
引理 contMDiffOn_iUnion_iff_of_isOpen
  结论: {ι : 类型} {s : ι -> 集合 M}
  证明: ⟨fun h i => h.mono subset_iUnion_of_subset i fun _ a => a,
   fun h => ContMDiffOn.iUnion_of_isOpen h hs⟩

Depends on / 依赖: ContMDiffOn, ContMDiffOn.iUnion_of_isOpen, h.mono, iUnion_of_isOpen, subset_iUnion_of_subset
-/
lemma contMDiffOn_iUnion_iff_of_isOpen {ι : Type*} {s : ι -> Set M}
    (hs : forall i, IsOpen (s i)) :
    ContMDiffOn I I' n f (⋃ i, s i) ↔ forall i : ι, ContMDiffOn I I' n f (s i) :=
⟨fun h i => h.mono subset_iUnion_of_subset i fun _ a => a,
   fun h => ContMDiffOn.iUnion_of_isOpen h hs⟩

/--
lemma `contMDiff_of_contMDiffOn_iUnion_of_isOpen` / 引理 `contMDiff_of_contMDiffOn_iUnion_of_isOpen`

English:
lemma contMDiff_of_contMDiffOn_iUnion_of_isOpen
  statement: {ι : Type*} {s : ι -> Set M}
  proof: by
  rw [← contMDiffOn_univ]; rw [← hs']
  exact ContMDiffOn.iUnion_of_isOpen hf hs

中文:
引理 contMDiff_of_contMDiffOn_iUnion_of_isOpen
  结论: {ι : 类型} {s : ι -> 集合 M}
  证明: by
  rw [← contMDiffOn_univ]; rw [← hs']
  exact ContMDiffOn.iUnion_of_isOpen hf hs

Depends on / 依赖: ContMDiffOn, ContMDiffOn.iUnion_of_isOpen, contMDiffOn_univ, iUnion_of_isOpen
-/
lemma contMDiff_of_contMDiffOn_iUnion_of_isOpen {ι : Type*} {s : ι -> Set M}
    (hf : forall i : ι, ContMDiffOn I I' n f (s i)) (hs : forall i, IsOpen (s i)) (hs' : ⋃ i, s i = univ) :
    ContMDiff I I' n f := by
  rw [← contMDiffOn_univ]; rw [← hs']
  exact ContMDiffOn.iUnion_of_isOpen hf hs

end contMDiff_union


/-! ### The inclusion map from one open set to another is `C^n` -/

section Inclusion

open TopologicalSpace

/--
theorem `contMDiffAt_subtype_iff` / 定理 `contMDiffAt_subtype_iff`

English:
theorem contMDiffAt_subtype_iff
  given: {n : Nat∞ω} {U : Opens M} {f : M -> M'} {x : U}
  proof: ((contDiffWithinAt_localInvariantProp n).liftPropAt_iff_comp_subtype_val _ _).symm

中文:
定理 contMDiffAt_subtype_iff
  条件: {n : 自然数∞ω} {U : Opens M} {f : M -> M'} {x : U}
  证明: ((contDiffWithinAt_localInvariantProp n).liftPropAt_iff_comp_subtype_val _ _).symm

Depends on / 依赖: contDiffWithinAt_localInvariantProp, liftPropAt_iff_comp_subtype_val
-/
theorem contMDiffAt_subtype_iff {n : Nat∞ω} {U : Opens M} {f : M -> M'} {x : U} :
    ContMDiffAt I I' n (fun x : U => f x) x ↔ ContMDiffAt I I' n f x :=
  ((contDiffWithinAt_localInvariantProp n).liftPropAt_iff_comp_subtype_val _ _).symm

/--
theorem `contMDiff_subtype_val` / 定理 `contMDiff_subtype_val`

English:
theorem contMDiff_subtype_val
  given: {n : Nat∞ω} {U : Opens M}
  proof: fun _ => contMDiffAt_subtype_iff.mpr contMDiffAt_id

@[to_additive]

中文:
定理 contMDiff_subtype_val
  条件: {n : 自然数∞ω} {U : Opens M}
  证明: fun _ => contMDiffAt_subtype_iff.mpr contMDiffAt_id

@[to_additive]

Depends on / 依赖: contMDiffAt_id, contMDiffAt_subtype_iff, contMDiffAt_subtype_iff.mpr
-/
theorem contMDiff_subtype_val {n : Nat∞ω} {U : Opens M} :
    ContMDiff I I n (Subtype.val : U -> M) :=
  fun _ => contMDiffAt_subtype_iff.mpr contMDiffAt_id

@[to_additive]
/--
theorem `ContMDiff.extend_one` / 定理 `ContMDiff.extend_one`

English:
theorem ContMDiff.extend_one
  statement: [T2Space M] [One M'] {n : Nat∞ω} {U : Opens M} {f : U -> M'}
  proof: fun x => by
  refine contMDiff_of_mulTSupport (fun x h => ?_) _
  lift x to U using Subtype.coe_image_subset _ _
    (supp.mulTSupport_extend_one_subset continuous_subtype_val h)
  rw [← contMDiffAt_subtype_iff]
  simp_rw [← comp_def]
  rw [extend_comp Subtype.val_injective]
  exact diff.contMDiffAt

中文:
定理 ContMDiff.extend_one
  结论: [T2空间 M] [幺 M'] {n : 自然数∞ω} {U : Opens M} {f : U -> M'}
  证明: fun x => by
  refine contMDiff_of_mulTSupport (fun x h => ?_) _
  lift x to U using Subtype.coe_image_subset _ _
    (supp.mulTSupport_extend_one_subset continuous_subtype_val h)
  rw [← contMDiffAt_subtype_iff]
  simp_rw [← comp_def]
  rw [extend_comp Subtype.val_injective]
  exact diff.contMDiffAt

Depends on / 依赖: Subtype, Subtype.coe_image_subset, Subtype.val_injective, coe_image_subset, comp_def, contMDiffAt, contMDiffAt_subtype_iff, contMDiff_of_mulTSupport, continuous_subtype_val, diff.contMDiffAt, extend_comp, mulTSupport_extend_one_subset, simp_rw, supp.mulTSupport_extend_one_subset, val_injective
-/
theorem ContMDiff.extend_one [T2Space M] [One M'] {n : Nat∞ω} {U : Opens M} {f : U -> M'}
    (supp : HasCompactMulSupport f) (diff : ContMDiff I I' n f) :
    ContMDiff I I' n (Subtype.val.extend f 1) := fun x => by
  refine contMDiff_of_mulTSupport (fun x h => ?_) _
  lift x to U using Subtype.coe_image_subset _ _
    (supp.mulTSupport_extend_one_subset continuous_subtype_val h)
  rw [← contMDiffAt_subtype_iff]
  simp_rw [← comp_def]
  rw [extend_comp Subtype.val_injective]
  exact diff.contMDiffAt

/--
theorem `contMDiff_inclusion` / 定理 `contMDiff_inclusion`

English:
theorem contMDiff_inclusion
  given: {n : Nat∞ω} {U V : Opens M} (h : U <= V)
  proof: fun _ =>
  (contDiffWithinAt_localInvariantProp n).liftProp_inclusion (contDiffWithinAtProp_id ·) _ _

中文:
定理 contMDiff_inclusion
  条件: {n : 自然数∞ω} {U V : Opens M} (h : U <= V)
  证明: fun _ =>
  (contDiffWithinAt_localInvariantProp n).liftProp_inclusion (contDiffWithinAtProp_id ·) _ _
-/
theorem contMDiff_inclusion {n : Nat∞ω} {U V : Opens M} (h : U <= V) :
    ContMDiff I I n (Opens.inclusion h : U -> V) := fun _ =>
  (contDiffWithinAt_localInvariantProp n).liftProp_inclusion (contDiffWithinAtProp_id ·) _ _

end Inclusion

@[simp]
/--
lemma `ContMDiffWithinAt.subtypeVal_comp_iff` / 引理 `ContMDiffWithinAt.subtypeVal_comp_iff`

English:
lemma ContMDiffWithinAt.subtypeVal_comp_iff
  statement: (U : TopologicalSpace.Opens M') (f : M -> U) (s : Set M)
  proof: ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..

@[simp]

中文:
引理 ContMDiffWithinAt.subtypeVal_comp_iff
  结论: (U : 拓扑空间.Opens M') (f : M -> U) (s : 集合 M)
  证明: ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..

@[simp]

Depends on / 依赖: ChartedSpace, ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff, liftPropWithinAt_subtypeVal_comp_iff
-/
lemma ContMDiffWithinAt.subtypeVal_comp_iff (U : TopologicalSpace.Opens M') (f : M -> U) (s : Set M)
    (x : M) :
    ContMDiffWithinAt I I' ∞ (Subtype.val ∘ f) s x ↔ ContMDiffWithinAt I I' ∞ f s x :=
  ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..

@[simp]
/--
lemma `ContMDiffAt.subtypeVal_comp_iff` / 引理 `ContMDiffAt.subtypeVal_comp_iff`

English:
lemma ContMDiffAt.subtypeVal_comp_iff
  given: (U : TopologicalSpace.Opens M') (f : M -> U) (x : M)
  proof: by
  rw [ContMDiffAt]; rw [ContMDiffAt]; rw [ContMDiffWithinAt.subtypeVal_comp_iff]

@[simp]

中文:
引理 ContMDiffAt.subtypeVal_comp_iff
  条件: (U : 拓扑空间.Opens M') (f : M -> U) (x : M)
  证明: by
  rw [ContMDiffAt]; rw [ContMDiffAt]; rw [ContMDiffWithinAt.subtypeVal_comp_iff]

@[simp]

Depends on / 依赖: ContMDiffAt, ContMDiffWithinAt, ContMDiffWithinAt.subtypeVal_comp_iff, subtypeVal_comp_iff
-/
lemma ContMDiffAt.subtypeVal_comp_iff (U : TopologicalSpace.Opens M') (f : M -> U) (x : M) :
    ContMDiffAt I I' ∞ (Subtype.val ∘ f) x ↔ ContMDiffAt I I' ∞ f x := by
  rw [ContMDiffAt]; rw [ContMDiffAt]; rw [ContMDiffWithinAt.subtypeVal_comp_iff]

@[simp]
/--
lemma `ContMDiff.subtypeVal_comp_iff` / 引理 `ContMDiff.subtypeVal_comp_iff`

English:
lemma ContMDiff.subtypeVal_comp_iff
  given: (U : TopologicalSpace.Opens M') (f : M -> U)
  proof: by
  simp_rw [ContMDiff, ContMDiffAt.subtypeVal_comp_iff]

中文:
引理 ContMDiff.subtypeVal_comp_iff
  条件: (U : 拓扑空间.Opens M') (f : M -> U)
  证明: by
  simp_rw [ContMDiff, ContMDiffAt.subtypeVal_comp_iff]

Depends on / 依赖: ContMDiff, ContMDiffAt, ContMDiffAt.subtypeVal_comp_iff, simp_rw, subtypeVal_comp_iff
-/
lemma ContMDiff.subtypeVal_comp_iff (U : TopologicalSpace.Opens M') (f : M -> U) :
    ContMDiff I I' ∞ (Subtype.val ∘ f) ↔ ContMDiff I I' ∞ f := by
  simp_rw [ContMDiff, ContMDiffAt.subtypeVal_comp_iff]

end ChartedSpace

/-! ### Open embeddings and their inverses are `C^n` -/

section

variable {e : M -> H} (h : IsOpenEmbedding e) {n : Nat∞ω}

set_option backward.isDefEq.respectTransparency false in
/--
lemma `contMDiff_isOpenEmbedding` / 引理 `contMDiff_isOpenEmbedding`

English:
lemma contMDiff_isOpenEmbedding
  given: [Nonempty M]
  proof: h.singletonChartedSpace; ContMDiff I I n e := by
  have := h.isManifold_singleton (I := I) (n := ω)
  rw [@contMDiff_iff _ _ _ _ _ _ _ _ _ _ h.singletonChartedSpace]
  use h.continuous
  intro x y
  -- show the function is actually the identity on the range of I ∘ e
  apply contDiffOn_id.congr
  int

中文:
引理 contMDiff_isOpenEmbedding
  条件: [非空 M]
  证明: h.singletonChartedSpace; ContMDiff I I n e := by
  have := h.isManifold_singleton (I := I) (n := ω)
  rw [@contMDiff_iff _ _ _ _ _ _ _ _ _ _ h.singletonChartedSpace]
  use h.continuous
  intro x y
  -- show the function is actually the identity on the range of I ∘ e
  apply contDiffOn_id.congr
  int

Depends on / 依赖: ContMDiff, contMDiff_iff, continuous, h.continuous, h.isManifold_singleton, h.singletonChartedSpace, isManifold_singleton, singletonChartedSpace
-/
lemma contMDiff_isOpenEmbedding [Nonempty M] :
    haveI := h.singletonChartedSpace; ContMDiff I I n e := by
  have := h.isManifold_singleton (I := I) (n := ω)
  rw [@contMDiff_iff _ _ _ _ _ _ _ _ _ _ h.singletonChartedSpace]
  use h.continuous
  intro x y
  -- show the function is actually the identity on the range of I ∘ e
  apply contDiffOn_id.congr
  intro z hz
  -- factorise into the chart `e` and the model `id`
  simp only [mfld_simps]
  rw [h.toOpenPartialHomeomorph_right_inv]
  · rw [I.right_inv]
    apply mem_of_subset_of_mem _ hz.1
    exact letI := h.singletonChartedSpace; extChartAt_target_subset_range (I := I) x
  · -- `hz` implies that `z ∈ range (I ∘ e)`
    have := hz.1
    rw [@extChartAt_target _ _ _ _ _ _ _ _ _ _ h.singletonChartedSpace] at this
    have := this.1
    rw [mem_preimage]; rw [OpenPartialHomeomorph.singletonChartedSpace_chartAt_eq]; rw [h.toOpenPartialHomeomorph_target] at this
    exact this

set_option backward.isDefEq.respectTransparency false in
/--
lemma `contMDiffOn_isOpenEmbedding_symm` / 引理 `contMDiffOn_isOpenEmbedding_symm`

English:
lemma contMDiffOn_isOpenEmbedding_symm
  given: [Nonempty M]
  proof: h.singletonChartedSpace; ContMDiffOn I I
      n (IsOpenEmbedding.toOpenPartialHomeomorph e h).symm (range e) := by
  have := h.isManifold_singleton (I := I) (n := ω)
  rw [@contMDiffOn_iff]
  constructor
  · rw [← h.toOpenPartialHomeomorph_target]
    exact (h.toOpenPartialHomeomorph e).continuousO

中文:
引理 contMDiffOn_isOpenEmbedding_symm
  条件: [非空 M]
  证明: h.singletonChartedSpace; ContMDiffOn I I
      n (IsOpenEmbedding.toOpenPartialHomeomorph e h).symm (range e) := by
  have := h.isManifold_singleton (I := I) (n := ω)
  rw [@contMDiffOn_iff]
  constructor
  · rw [← h.toOpenPartialHomeomorph_target]
    exact (h.toOpenPartialHomeomorph e).continuousO

Depends on / 依赖: ContMDiffOn, h.singletonChartedSpace, singletonChartedSpace
-/
lemma contMDiffOn_isOpenEmbedding_symm [Nonempty M] :
    haveI := h.singletonChartedSpace; ContMDiffOn I I
      n (IsOpenEmbedding.toOpenPartialHomeomorph e h).symm (range e) := by
  have := h.isManifold_singleton (I := I) (n := ω)
  rw [@contMDiffOn_iff]
  constructor
  · rw [← h.toOpenPartialHomeomorph_target]
    exact (h.toOpenPartialHomeomorph e).continuousOn_symm
  · intro z hz
    -- show the function is actually the identity on the range of I ∘ e
    apply contDiffOn_id.congr
    intro z hz
    -- factorise into the chart `e` and the model `id`
    simp only [mfld_simps]
    have : I.symm z in range e := by
      rw [ModelWithCorners.symm]; rw [← mem_preimage]
      exact hz.2.1
    rw [h.toOpenPartialHomeomorph_right_inv e this]
    apply I.right_inv
    exact mem_of_subset_of_mem (extChartAt_target_subset_range _) hz.1

variable [ChartedSpace H M]
variable [Nonempty M'] {e' : M' -> H'} (h' : IsOpenEmbedding e')

/--
lemma `ContMDiff.of_comp_isOpenEmbedding` / 引理 `ContMDiff.of_comp_isOpenEmbedding`

English:
lemma ContMDiff.of_comp_isOpenEmbedding
  given: {f : M -> M'} (hf : ContMDiff I I' n (e' ∘ f))
  proof: h'.singletonChartedSpace; ContMDiff I I' n f := by
  have : f = (h'.toOpenPartialHomeomorph e').symm ∘ e' ∘ f := by
    ext
    rw [Function.comp_apply]; rw [Function.comp_apply]; rw [IsOpenEmbedding.toOpenPartialHomeomorph_left_inv]
  rw [this]
  apply @ContMDiffOn.comp_contMDiff _ _ _ _ _ _ _ _ _ 

中文:
引理 ContMDiff.of_comp_isOpenEmbedding
  条件: {f : M -> M'} (hf : ContMDiff I I' n (e' ∘ f))
  证明: h'.singletonChartedSpace; ContMDiff I I' n f := by
  have : f = (h'.toOpenPartialHomeomorph e').symm ∘ e' ∘ f := by
    ext
    rw [Function.comp_apply]; rw [Function.comp_apply]; rw [IsOpenEmbedding.toOpenPartialHomeomorph_left_inv]
  rw [this]
  apply @ContMDiffOn.comp_contMDiff _ _ _ _ _ _ _ _ _ 

Depends on / 依赖: ContMDiff, ContMDiffOn, ContMDiffOn.comp_contMDiff, Function, Function.comp_apply, IsOpenEmbedding, IsOpenEmbedding.toOpenPartialHomeomorph_left_inv, comp_apply, comp_contMDiff, contMDiffOn_isOpenEmbedding_symm, singletonChartedSpace, toOpenPartialHomeomorph, toOpenPartialHomeomorph_left_inv
-/
lemma ContMDiff.of_comp_isOpenEmbedding {f : M -> M'} (hf : ContMDiff I I' n (e' ∘ f)) :
    haveI := h'.singletonChartedSpace; ContMDiff I I' n f := by
  have : f = (h'.toOpenPartialHomeomorph e').symm ∘ e' ∘ f := by
    ext
    rw [Function.comp_apply]; rw [Function.comp_apply]; rw [IsOpenEmbedding.toOpenPartialHomeomorph_left_inv]
  rw [this]
  apply @ContMDiffOn.comp_contMDiff _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    h'.singletonChartedSpace _ _ (range e') _ (contMDiffOn_isOpenEmbedding_symm h') hf
  simp

end
