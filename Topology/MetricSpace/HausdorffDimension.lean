/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Analysis.Convex.Intrinsic

/-!
# Hausdorff dimension

The Hausdorff dimension of a set `X` in an (extended) metric space is the unique number
`dimH s : ℝ≥0∞` such that for any `d : ℝ≥0` we have

- `μH[d] s = 0` if `dimH s < d`, and
- `μH[d] s = ∞` if `d < dimH s`.

In this file we define `dimH s` to be the Hausdorff dimension of `s`, then prove some basic
properties of Hausdorff dimension.

## Main definitions

* `MeasureTheory.dimH`: the Hausdorff dimension of a set. For the Hausdorff dimension of the whole
  space we use `MeasureTheory.dimH (Set.univ : Set X)`.

## Main results

### Basic properties of Hausdorff dimension

* `hausdorffMeasure_of_lt_dimH`, `dimH_le_of_hausdorffMeasure_ne_top`,
  `le_dimH_of_hausdorffMeasure_eq_top`, `hausdorffMeasure_of_dimH_lt`, `measure_zero_of_dimH_lt`,
  `le_dimH_of_hausdorffMeasure_ne_zero`, `dimH_of_hausdorffMeasure_ne_zero_ne_top`: various forms
  of the characteristic property of the Hausdorff dimension;
* `dimH_union`: the Hausdorff dimension of the union of two sets is the maximum of their Hausdorff
  dimensions.
* `dimH_iUnion`, `dimH_bUnion`, `dimH_sUnion`: the Hausdorff dimension of a countable union of sets
  is the supremum of their Hausdorff dimensions;
* `dimH_empty`, `dimH_singleton`, `Set.Subsingleton.dimH_zero`, `Set.Countable.dimH_zero` : `dimH s
  = 0` whenever `s` is countable;

### (Pre)images under (anti)lipschitz and Hölder continuous maps

* `HolderWith.dimH_image_le` etc: if `f : X → Y` is Hölder continuous with exponent `r > 0`, then
  for any `s`, `dimH (f '' s) ≤ dimH s / r`. We prove versions of this statement for `HolderWith`,
  `HolderOnWith`, and locally Hölder maps, as well as for `Set.image` and `Set.range`.
* `LipschitzWith.dimH_image_le` etc: Lipschitz continuous maps do not increase the Hausdorff
  dimension of sets.
* for a map that is known to be both Lipschitz and antilipschitz (e.g., for an `Isometry` or
  a `ContinuousLinearEquiv`) we also prove `dimH (f '' s) = dimH s`.

### Hausdorff measure in `ℝⁿ`

* `Real.dimH_of_nonempty_interior`: if `s` is a set in a finite-dimensional real vector space `E`
  with nonempty interior, then the Hausdorff dimension of `s` is equal to the dimension of `E`.
* `dense_compl_of_dimH_lt_finrank`: if `s` is a set in a finite-dimensional real vector space `E`
  with Hausdorff dimension strictly less than the dimension of `E`, the `s` has a dense complement.
* `ContDiff.dense_compl_range_of_finrank_lt_finrank`: the complement to the range of a `C¹`
  smooth map is dense provided that the dimension of the domain is strictly less than the dimension
  of the codomain.

## Notation

We use the following notation localized in `MeasureTheory`. It is defined in
`MeasureTheory.Measure.Hausdorff`.

- `μH[d]` : `MeasureTheory.Measure.hausdorffMeasure d`

## Implementation notes

* The definition of `dimH` explicitly uses `borel X` as a measurable space structure. This way we
  can formulate lemmas about Hausdorff dimension without assuming that the environment has a
  `[MeasurableSpace X]` instance that is equal but possibly not defeq to `borel X`.

  Lemma `dimH_def` unfolds this definition using whatever `[MeasurableSpace X]` instance we have in
  the environment (as long as it is equal to `borel X`).

* The definition `dimH` is irreducible; use API lemmas or `dimH_def` instead.

## Tags

Hausdorff measure, Hausdorff dimension, dimension
-/

@[expose] public section


open scoped MeasureTheory ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set TopologicalSpace Module Filter

variable {ι X Y : Type*} [EMetricSpace X] [EMetricSpace Y]

/--
Definition of `dimH` / `dimH` 的定义

English:
definition dimH
  signature: (s : Set X)
  body: by
  borelize X; exact ⨆ (d : Real>=0) (_ : @hausdorffMeasure X _ _ ⟨rfl⟩ d s = ∞), d

中文:
定义 dimH
  签名: (s : Set X)
  定义体: by
  borelize X; exact ⨆ (d : Real>=0) (_ : @hausdorffMeasure X _ _ ⟨rfl⟩ d s = ∞), d
-/
@[irreducible] noncomputable def dimH (s : Set X) : Real>=0∞ := by
  borelize X; exact ⨆ (d : Real>=0) (_ : @hausdorffMeasure X _ _ ⟨rfl⟩ d s = ∞), d

/-!
### Basic properties
-/


section Measurable

variable [MeasurableSpace X] [BorelSpace X]

/--
theorem `dimH_def` / 定理 `dimH_def`

English:
theorem dimH_def
  given: (s : Set X)
  statement: dimH s = ⨆ (d : Real>=0) (_ : μH[d] s = ∞), (d : Real>=0∞)
  proof: by
  borelize X; rw [dimH]

中文:
定理 dimH_def
  条件: (s : Set X)
  结论: dimH s = ⨆ (d : 实数>=0) (_ : μH[d] s = ∞), (d : 实数>=0∞)
  证明: by
  borelize X; rw [dimH]

Depends on / 依赖: borelize
-/
theorem dimH_def (s : Set X) : dimH s = ⨆ (d : Real>=0) (_ : μH[d] s = ∞), (d : Real>=0∞) := by
  borelize X; rw [dimH]

/--
theorem `hausdorffMeasure_of_lt_dimH` / 定理 `hausdorffMeasure_of_lt_dimH`

English:
theorem hausdorffMeasure_of_lt_dimH
  given: {s : Set X} {d : Real>=0} (h : ↑d < dimH s)
  statement: μH[d] s = ∞
  proof: by
  simp only [dimH_def, lt_iSup_iff] at h
  rcases h with ⟨d', hsd', hdd'⟩
  rw [ENNReal.coe_lt_coe]; rw [← NNReal.coe_lt_coe] at hdd'
  exact top_unique (hsd' ▸ hausdorffMeasure_mono hdd'.le _)

中文:
定理 hausdorffMeasure_of_lt_dimH
  条件: {s : Set X} {d : 实数>=0} (h : ↑d < dimH s)
  结论: μH[d] s = ∞
  证明: by
  simp only [dimH_def, lt_iSup_iff] at h
  rcases h with ⟨d', hsd', hdd'⟩
  rw [ENNReal.coe_lt_coe]; rw [← NNReal.coe_lt_coe] at hdd'
  exact top_unique (hsd' ▸ hausdorffMeasure_mono hdd'.le _)

Depends on / 依赖: ENNReal, ENNReal.coe_lt_coe, NNReal, NNReal.coe_lt_coe, coe_lt_coe, dimH_def, hausdorffMeasure_mono, lt_iSup_iff, top_unique
-/
theorem hausdorffMeasure_of_lt_dimH {s : Set X} {d : Real>=0} (h : ↑d < dimH s) : μH[d] s = ∞ := by
  simp only [dimH_def, lt_iSup_iff] at h
  rcases h with ⟨d', hsd', hdd'⟩
  rw [ENNReal.coe_lt_coe]; rw [← NNReal.coe_lt_coe] at hdd'
  exact top_unique (hsd' ▸ hausdorffMeasure_mono hdd'.le _)

/--
theorem `dimH_le` / 定理 `dimH_le`

English:
theorem dimH_le
  given: {s : Set X} {d : Real>=0∞} (H : forall d' : Real>=0, μH[d'] s = ∞ -> ↑d' <= d)
  statement: dimH s <= d
  proof: (dimH_def s).trans_le iSup₂_le H

中文:
定理 dimH_le
  条件: {s : Set X} {d : 实数>=0∞} (H : 对任意 d' : 实数>=0, μH[d'] s = ∞ -> ↑d' <= d)
  结论: dimH s <= d
  证明: (dimH_def s).trans_le iSup₂_le H

Depends on / 依赖: dimH_def, trans_le
-/
theorem dimH_le {s : Set X} {d : Real>=0∞} (H : forall d' : Real>=0, μH[d'] s = ∞ -> ↑d' <= d) : dimH s <= d :=
(dimH_def s).trans_le iSup₂_le H

/--
theorem `dimH_le_of_hausdorffMeasure_ne_top` / 定理 `dimH_le_of_hausdorffMeasure_ne_top`

English:
theorem dimH_le_of_hausdorffMeasure_ne_top
  given: {s : Set X} {d : Real>=0} (h : μH[d] s != ∞)
  statement: dimH s <= d
  proof: le_of_not_gt mt hausdorffMeasure_of_lt_dimH h

中文:
定理 dimH_le_of_hausdorffMeasure_ne_top
  条件: {s : Set X} {d : 实数>=0} (h : μH[d] s != ∞)
  结论: dimH s <= d
  证明: le_of_not_gt mt hausdorffMeasure_of_lt_dimH h

Depends on / 依赖: hausdorffMeasure_of_lt_dimH, le_of_not_gt
-/
theorem dimH_le_of_hausdorffMeasure_ne_top {s : Set X} {d : Real>=0} (h : μH[d] s != ∞) : dimH s <= d :=
le_of_not_gt mt hausdorffMeasure_of_lt_dimH h

/--
theorem `le_dimH_of_hausdorffMeasure_eq_top` / 定理 `le_dimH_of_hausdorffMeasure_eq_top`

English:
theorem le_dimH_of_hausdorffMeasure_eq_top
  given: {s : Set X} {d : Real>=0} (h : μH[d] s = ∞)
  proof: by
  rw [dimH_def]; exact le_iSup₂ (α := Real>=0∞) d h

中文:
定理 le_dimH_of_hausdorffMeasure_eq_top
  条件: {s : Set X} {d : 实数>=0} (h : μH[d] s = ∞)
  证明: by
  rw [dimH_def]; exact le_iSup₂ (α := Real>=0∞) d h

Depends on / 依赖: dimH_def
-/
theorem le_dimH_of_hausdorffMeasure_eq_top {s : Set X} {d : Real>=0} (h : μH[d] s = ∞) :
    ↑d <= dimH s := by
  rw [dimH_def]; exact le_iSup₂ (α := Real>=0∞) d h

/--
theorem `hausdorffMeasure_of_dimH_lt` / 定理 `hausdorffMeasure_of_dimH_lt`

English:
theorem hausdorffMeasure_of_dimH_lt
  given: {s : Set X} {d : Real>=0} (h : dimH s < d)
  statement: μH[d] s = 0
  proof: by
  rw [dimH_def] at h
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 h with ⟨d', hsd', hd'd⟩
  rw [ENNReal.coe_lt_coe]; rw [← NNReal.coe_lt_coe] at hd'd
exact (hausdorffMeasure_zero_or_top hd'd s).resolve_right fun h₂ => hsd'.not_ge
    le_iSup₂ (α := Real>=0∞) d' h₂

中文:
定理 hausdorffMeasure_of_dimH_lt
  条件: {s : Set X} {d : 实数>=0} (h : dimH s < d)
  结论: μH[d] s = 0
  证明: by
  rw [dimH_def] at h
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 h with ⟨d', hsd', hd'd⟩
  rw [ENNReal.coe_lt_coe]; rw [← NNReal.coe_lt_coe] at hd'd
exact (hausdorffMeasure_zero_or_top hd'd s).resolve_right fun h₂ => hsd'.not_ge
    le_iSup₂ (α := Real>=0∞) d' h₂

Depends on / 依赖: ENNReal, ENNReal.coe_lt_coe, ENNReal.lt_iff_exists_nnreal_btwn, NNReal, NNReal.coe_lt_coe, coe_lt_coe, dimH_def, hausdorffMeasure_zero_or_top, lt_iff_exists_nnreal_btwn, not_ge, resolve_right
-/
theorem hausdorffMeasure_of_dimH_lt {s : Set X} {d : Real>=0} (h : dimH s < d) : μH[d] s = 0 := by
  rw [dimH_def] at h
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 h with ⟨d', hsd', hd'd⟩
  rw [ENNReal.coe_lt_coe]; rw [← NNReal.coe_lt_coe] at hd'd
exact (hausdorffMeasure_zero_or_top hd'd s).resolve_right fun h₂ => hsd'.not_ge
    le_iSup₂ (α := Real>=0∞) d' h₂

/--
theorem `measure_zero_of_dimH_lt` / 定理 `measure_zero_of_dimH_lt`

English:
theorem measure_zero_of_dimH_lt
  statement: {μ : Measure X} {d : Real>=0} (h : μ ≪ μH[d]) {s : Set X}
  proof: h hausdorffMeasure_of_dimH_lt hd

中文:
定理 measure_zero_of_dimH_lt
  结论: {μ : Measure X} {d : 实数>=0} (h : μ ≪ μH[d]) {s : Set X}
  证明: h hausdorffMeasure_of_dimH_lt hd

Depends on / 依赖: hausdorffMeasure_of_dimH_lt
-/
theorem measure_zero_of_dimH_lt {μ : Measure X} {d : Real>=0} (h : μ ≪ μH[d]) {s : Set X}
    (hd : dimH s < d) : μ s = 0 :=
h hausdorffMeasure_of_dimH_lt hd

/--
theorem `le_dimH_of_hausdorffMeasure_ne_zero` / 定理 `le_dimH_of_hausdorffMeasure_ne_zero`

English:
theorem le_dimH_of_hausdorffMeasure_ne_zero
  given: {s : Set X} {d : Real>=0} (h : μH[d] s != 0)
  statement: ↑d <= dimH s
  proof: le_of_not_gt mt hausdorffMeasure_of_dimH_lt h

中文:
定理 le_dimH_of_hausdorffMeasure_ne_zero
  条件: {s : Set X} {d : 实数>=0} (h : μH[d] s != 0)
  结论: ↑d <= dimH s
  证明: le_of_not_gt mt hausdorffMeasure_of_dimH_lt h

Depends on / 依赖: hausdorffMeasure_of_dimH_lt, le_of_not_gt
-/
theorem le_dimH_of_hausdorffMeasure_ne_zero {s : Set X} {d : Real>=0} (h : μH[d] s != 0) : ↑d <= dimH s :=
le_of_not_gt mt hausdorffMeasure_of_dimH_lt h

/--
theorem `dimH_of_hausdorffMeasure_ne_zero_ne_top` / 定理 `dimH_of_hausdorffMeasure_ne_zero_ne_top`

English:
theorem dimH_of_hausdorffMeasure_ne_zero_ne_top
  statement: {d : Real>=0} {s : Set X} (h : μH[d] s != 0)
  proof: le_antisymm (dimH_le_of_hausdorffMeasure_ne_top h') (le_dimH_of_hausdorffMeasure_ne_zero h)

中文:
定理 dimH_of_hausdorffMeasure_ne_zero_ne_top
  结论: {d : 实数>=0} {s : Set X} (h : μH[d] s != 0)
  证明: le_antisymm (dimH_le_of_hausdorffMeasure_ne_top h') (le_dimH_of_hausdorffMeasure_ne_zero h)

Depends on / 依赖: dimH_le_of_hausdorffMeasure_ne_top, le_antisymm, le_dimH_of_hausdorffMeasure_ne_zero
-/
theorem dimH_of_hausdorffMeasure_ne_zero_ne_top {d : Real>=0} {s : Set X} (h : μH[d] s != 0)
    (h' : μH[d] s != ∞) : dimH s = d :=
  le_antisymm (dimH_le_of_hausdorffMeasure_ne_top h') (le_dimH_of_hausdorffMeasure_ne_zero h)

/--
theorem `dimH_eq_iInf` / 定理 `dimH_eq_iInf`

English:
theorem dimH_eq_iInf
  given: (s : Set X)
  statement: dimH s = ⨅ (d : Real>=0) (_ : μH[d] s = 0), (d : Real>=0∞)
  proof: by
  apply le_antisymm
  · rw [dimH_def]
    simp only [le_iInf_iff, iSup_le_iff, ENNReal.coe_le_coe]
    intro i hi j hj
    by_contra! hij
    simpa [hi, hj] using hausdorffMeasure_mono hij.le s
  · by_contra! h
    rcases ENNReal.lt_iff_exists_nnreal_btwn.1 h with ⟨d', hdim_lt, hlt⟩
    have h0 :

中文:
定理 dimH_eq_iInf
  条件: (s : Set X)
  结论: dimH s = ⨅ (d : 实数>=0) (_ : μH[d] s = 0), (d : 实数>=0∞)
  证明: by
  apply le_antisymm
  · rw [dimH_def]
    simp only [le_iInf_iff, iSup_le_iff, ENNReal.coe_le_coe]
    intro i hi j hj
    by_contra! hij
    simpa [hi, hj] using hausdorffMeasure_mono hij.le s
  · by_contra! h
    rcases ENNReal.lt_iff_exists_nnreal_btwn.1 h with ⟨d', hdim_lt, hlt⟩
    have h0 :

Depends on / 依赖: ENNReal, ENNReal.coe_le_coe, ENNReal.lt_iff_exists_nnreal_btwn, coe_le_coe, dimH_def, hausdorffMeasure_mono, hausdorffMeasure_of_dimH_lt, hdim_lt, hij.le, hlt.not_ge, iSup_le_iff, le_antisymm, le_iInf_iff, lt_iff_exists_nnreal_btwn, not_ge
-/
theorem dimH_eq_iInf (s : Set X) : dimH s = ⨅ (d : Real>=0) (_ : μH[d] s = 0), (d : Real>=0∞) := by
  apply le_antisymm
  · rw [dimH_def]
    simp only [le_iInf_iff, iSup_le_iff, ENNReal.coe_le_coe]
    intro i hi j hj
    by_contra! hij
    simpa [hi, hj] using hausdorffMeasure_mono hij.le s
  · by_contra! h
    rcases ENNReal.lt_iff_exists_nnreal_btwn.1 h with ⟨d', hdim_lt, hlt⟩
    have h0 : μH[d'] s = 0 := hausdorffMeasure_of_dimH_lt hdim_lt
    exact hlt.not_ge (iInf₂_le d' h0)

end Measurable

@[gcongr, mono]
/--
theorem `dimH_mono` / 定理 `dimH_mono`

English:
theorem dimH_mono
  given: {s t : Set X} (h : s subseteq t)
  statement: dimH s <= dimH t
  proof: by
  borelize X
exact dimH_le fun d hd => le_dimH_of_hausdorffMeasure_eq_top top_unique hd ▸ measure_mono h

中文:
定理 dimH_mono
  条件: {s t : Set X} (h : s subseteq t)
  结论: dimH s <= dimH t
  证明: by
  borelize X
exact dimH_le fun d hd => le_dimH_of_hausdorffMeasure_eq_top top_unique hd ▸ measure_mono h

Depends on / 依赖: borelize, dimH_le, le_dimH_of_hausdorffMeasure_eq_top, measure_mono, top_unique
-/
theorem dimH_mono {s t : Set X} (h : s subseteq t) : dimH s <= dimH t := by
  borelize X
exact dimH_le fun d hd => le_dimH_of_hausdorffMeasure_eq_top top_unique hd ▸ measure_mono h

/--
theorem `dimH_subsingleton` / 定理 `dimH_subsingleton`

English:
theorem dimH_subsingleton
  given: {s : Set X} (h : s.Subsingleton)
  statement: dimH s = 0
  proof: by
  borelize X
  rw [← nonpos_iff_eq_zero]
  apply dimH_le_of_hausdorffMeasure_ne_top
  exact ((hausdorffMeasure_le_one_of_subsingleton h le_rfl).trans_lt ENNReal.one_lt_top).ne

alias Set.Subsingleton.dimH_zero := dimH_subsingleton

@[simp]

中文:
定理 dimH_subsingleton
  条件: {s : Set X} (h : s.Subsingleton)
  结论: dimH s = 0
  证明: by
  borelize X
  rw [← nonpos_iff_eq_zero]
  apply dimH_le_of_hausdorffMeasure_ne_top
  exact ((hausdorffMeasure_le_one_of_subsingleton h le_rfl).trans_lt ENNReal.one_lt_top).ne

alias Set.Subsingleton.dimH_zero := dimH_subsingleton

@[simp]

Depends on / 依赖: ENNReal, ENNReal.one_lt_top, borelize, dimH_le_of_hausdorffMeasure_ne_top, hausdorffMeasure_le_one_of_subsingleton, le_rfl, nonpos_iff_eq_zero, one_lt_top, trans_lt
-/
theorem dimH_subsingleton {s : Set X} (h : s.Subsingleton) : dimH s = 0 := by
  borelize X
  rw [← nonpos_iff_eq_zero]
  apply dimH_le_of_hausdorffMeasure_ne_top
  exact ((hausdorffMeasure_le_one_of_subsingleton h le_rfl).trans_lt ENNReal.one_lt_top).ne

alias Set.Subsingleton.dimH_zero := dimH_subsingleton

@[simp]
/--
theorem `dimH_empty` / 定理 `dimH_empty`

English:
theorem dimH_empty
  statement: dimH (∅ : Set X) = 0
  proof: subsingleton_empty.dimH_zero

@[simp]

中文:
定理 dimH_empty
  结论: dimH (∅ : Set X) = 0
  证明: subsingleton_empty.dimH_zero

@[simp]

Depends on / 依赖: dimH_zero, subsingleton_empty, subsingleton_empty.dimH_zero
-/
theorem dimH_empty : dimH (∅ : Set X) = 0 :=
  subsingleton_empty.dimH_zero

@[simp]
/--
theorem `dimH_singleton` / 定理 `dimH_singleton`

English:
theorem dimH_singleton
  given: (x : X)
  statement: dimH ({x} : Set X) = 0
  proof: subsingleton_singleton.dimH_zero

@[simp]

中文:
定理 dimH_singleton
  条件: (x : X)
  结论: dimH ({x} : Set X) = 0
  证明: subsingleton_singleton.dimH_zero

@[simp]

Depends on / 依赖: dimH_zero, subsingleton_singleton, subsingleton_singleton.dimH_zero
-/
theorem dimH_singleton (x : X) : dimH ({x} : Set X) = 0 :=
  subsingleton_singleton.dimH_zero

@[simp]
/--
theorem `dimH_iUnion` / 定理 `dimH_iUnion`

English:
theorem dimH_iUnion
  given: {ι : Sort*} [Countable ι] (s : ι -> Set X)
  proof: by
  borelize X
  refine le_antisymm (dimH_le fun d hd => ?_) (iSup_le fun i => dimH_mono <| subset_iUnion _ _)
  contrapose! hd
  have : forall i, μH[d] (s i) = 0 := fun i =>
    hausdorffMeasure_of_dimH_lt ((le_iSup (fun i => dimH (s i)) i).trans_lt hd)
  rw [measure_iUnion_null this]
  exact ENNR

中文:
定理 dimH_iUnion
  条件: {ι : Sort*} [Countable ι] (s : ι -> Set X)
  证明: by
  borelize X
  refine le_antisymm (dimH_le fun d hd => ?_) (iSup_le fun i => dimH_mono <| subset_iUnion _ _)
  contrapose! hd
  have : forall i, μH[d] (s i) = 0 := fun i =>
    hausdorffMeasure_of_dimH_lt ((le_iSup (fun i => dimH (s i)) i).trans_lt hd)
  rw [measure_iUnion_null this]
  exact ENNR

Depends on / 依赖: ENNReal, ENNReal.zero_ne_top, borelize, contrapose, dimH_le, dimH_mono, hausdorffMeasure_of_dimH_lt, iSup_le, le_antisymm, le_iSup, measure_iUnion_null, subset_iUnion, trans_lt, zero_ne_top
-/
theorem dimH_iUnion {ι : Sort*} [Countable ι] (s : ι -> Set X) :
    dimH (⋃ i, s i) = ⨆ i, dimH (s i) := by
  borelize X
  refine le_antisymm (dimH_le fun d hd => ?_) (iSup_le fun i => dimH_mono <| subset_iUnion _ _)
  contrapose! hd
  have : forall i, μH[d] (s i) = 0 := fun i =>
    hausdorffMeasure_of_dimH_lt ((le_iSup (fun i => dimH (s i)) i).trans_lt hd)
  rw [measure_iUnion_null this]
  exact ENNReal.zero_ne_top

@[simp]
/--
theorem `dimH_bUnion` / 定理 `dimH_bUnion`

English:
theorem dimH_bUnion
  given: {s : Set ι} (hs : s.Countable) (t : ι -> Set X)
  proof: by
  have := hs.toEncodable
  rw [biUnion_eq_iUnion]; rw [dimH_iUnion]; rw [← iSup_subtype'']

@[simp]

中文:
定理 dimH_bUnion
  条件: {s : Set ι} (hs : s.Countable) (t : ι -> Set X)
  证明: by
  have := hs.toEncodable
  rw [biUnion_eq_iUnion]; rw [dimH_iUnion]; rw [← iSup_subtype'']

@[simp]

Depends on / 依赖: biUnion_eq_iUnion, dimH_iUnion, hs.toEncodable, iSup_subtype, toEncodable
-/
theorem dimH_bUnion {s : Set ι} (hs : s.Countable) (t : ι -> Set X) :
    dimH (⋃ i in s, t i) = ⨆ i in s, dimH (t i) := by
  have := hs.toEncodable
  rw [biUnion_eq_iUnion]; rw [dimH_iUnion]; rw [← iSup_subtype'']

@[simp]
/--
theorem `dimH_sUnion` / 定理 `dimH_sUnion`

English:
theorem dimH_sUnion
  given: {S : Set (Set X)} (hS : S.Countable)
  statement: dimH (⋃₀ S) = ⨆ s in S, dimH s
  proof: by
  rw [sUnion_eq_biUnion]; rw [dimH_bUnion hS]

@[simp]

中文:
定理 dimH_sUnion
  条件: {S : Set (Set X)} (hS : S.Countable)
  结论: dimH (⋃₀ S) = ⨆ s in S, dimH s
  证明: by
  rw [sUnion_eq_biUnion]; rw [dimH_bUnion hS]

@[simp]

Depends on / 依赖: dimH_bUnion, sUnion_eq_biUnion
-/
theorem dimH_sUnion {S : Set (Set X)} (hS : S.Countable) : dimH (⋃₀ S) = ⨆ s in S, dimH s := by
  rw [sUnion_eq_biUnion]; rw [dimH_bUnion hS]

@[simp]
/--
theorem `dimH_union` / 定理 `dimH_union`

English:
theorem dimH_union
  given: (s t : Set X)
  statement: dimH (s union t) = max (dimH s) (dimH t)
  proof: by
  rw [union_eq_iUnion]; rw [dimH_iUnion]; rw [iSup_bool_eq]; rw [cond]; rw [cond]

中文:
定理 dimH_union
  条件: (s t : Set X)
  结论: dimH (s union t) = max (dimH s) (dimH t)
  证明: by
  rw [union_eq_iUnion]; rw [dimH_iUnion]; rw [iSup_bool_eq]; rw [cond]; rw [cond]

Depends on / 依赖: dimH_iUnion, iSup_bool_eq, union_eq_iUnion
-/
theorem dimH_union (s t : Set X) : dimH (s union t) = max (dimH s) (dimH t) := by
  rw [union_eq_iUnion]; rw [dimH_iUnion]; rw [iSup_bool_eq]; rw [cond]; rw [cond]

/--
theorem `dimH_countable` / 定理 `dimH_countable`

English:
theorem dimH_countable
  given: {s : Set X} (hs : s.Countable)
  statement: dimH s = 0
  proof: biUnion_of_singleton s ▸ by simp only [dimH_bUnion hs, dimH_singleton, ENNReal.iSup_zero]

alias Set.Countable.dimH_zero := dimH_countable

中文:
定理 dimH_countable
  条件: {s : Set X} (hs : s.Countable)
  结论: dimH s = 0
  证明: biUnion_of_singleton s ▸ by simp only [dimH_bUnion hs, dimH_singleton, ENNReal.iSup_zero]

alias Set.Countable.dimH_zero := dimH_countable

Depends on / 依赖: ENNReal, ENNReal.iSup_zero, biUnion_of_singleton, dimH_bUnion, dimH_singleton, iSup_zero
-/
theorem dimH_countable {s : Set X} (hs : s.Countable) : dimH s = 0 :=
  biUnion_of_singleton s ▸ by simp only [dimH_bUnion hs, dimH_singleton, ENNReal.iSup_zero]

alias Set.Countable.dimH_zero := dimH_countable

/--
theorem `dimH_finite` / 定理 `dimH_finite`

English:
theorem dimH_finite
  given: {s : Set X} (hs : s.Finite)
  statement: dimH s = 0
  proof: hs.countable.dimH_zero

alias Set.Finite.dimH_zero := dimH_finite

@[simp]

中文:
定理 dimH_finite
  条件: {s : Set X} (hs : s.Finite)
  结论: dimH s = 0
  证明: hs.countable.dimH_zero

alias Set.Finite.dimH_zero := dimH_finite

@[simp]

Depends on / 依赖: countable, dimH_zero, hs.countable.dimH_zero
-/
theorem dimH_finite {s : Set X} (hs : s.Finite) : dimH s = 0 :=
  hs.countable.dimH_zero

alias Set.Finite.dimH_zero := dimH_finite

@[simp]
/--
theorem `dimH_coe_finset` / 定理 `dimH_coe_finset`

English:
theorem dimH_coe_finset
  given: (s : Finset X)
  statement: dimH (s : Set X) = 0
  proof: s.finite_toSet.dimH_zero

alias Finset.dimH_zero := dimH_coe_finset

中文:
定理 dimH_coe_finset
  条件: (s : Finset X)
  结论: dimH (s : Set X) = 0
  证明: s.finite_toSet.dimH_zero

alias Finset.dimH_zero := dimH_coe_finset

Depends on / 依赖: dimH_zero, finite_toSet, s.finite_toSet.dimH_zero
-/
theorem dimH_coe_finset (s : Finset X) : dimH (s : Set X) = 0 :=
  s.finite_toSet.dimH_zero

alias Finset.dimH_zero := dimH_coe_finset

/-!
### Hausdorff dimension as the supremum of local Hausdorff dimensions
-/


section

variable [SecondCountableTopology X]

/--
theorem `exists_mem_nhdsWithin_lt_dimH_of_lt_dimH` / 定理 `exists_mem_nhdsWithin_lt_dimH_of_lt_dimH`

English:
theorem exists_mem_nhdsWithin_lt_dimH_of_lt_dimH
  given: {s : Set X} {r : Real>=0∞} (h : r < dimH s)
  proof: by
  contrapose! h; choose! t htx htr using h
  rcases countable_cover_nhdsWithin htx with ⟨S, hSs, hSc, hSU⟩
  calc
    dimH s <= dimH (⋃ x in S, t x) := dimH_mono hSU
    _ = ⨆ x in S, dimH (t x) := dimH_bUnion hSc _
_ <= r := iSup₂_le fun x hx => htr x hSs hx

中文:
定理 exists_mem_nhdsWithin_lt_dimH_of_lt_dimH
  条件: {s : Set X} {r : 实数>=0∞} (h : r < dimH s)
  证明: by
  contrapose! h; choose! t htx htr using h
  rcases countable_cover_nhdsWithin htx with ⟨S, hSs, hSc, hSU⟩
  calc
    dimH s <= dimH (⋃ x in S, t x) := dimH_mono hSU
    _ = ⨆ x in S, dimH (t x) := dimH_bUnion hSc _
_ <= r := iSup₂_le fun x hx => htr x hSs hx

Depends on / 依赖: contrapose, countable_cover_nhdsWithin, dimH_bUnion, dimH_mono
-/
theorem exists_mem_nhdsWithin_lt_dimH_of_lt_dimH {s : Set X} {r : Real>=0∞} (h : r < dimH s) :
    exists x in s, forall t in 𝓝[s] x, r < dimH t := by
  contrapose! h; choose! t htx htr using h
  rcases countable_cover_nhdsWithin htx with ⟨S, hSs, hSc, hSU⟩
  calc
    dimH s <= dimH (⋃ x in S, t x) := dimH_mono hSU
    _ = ⨆ x in S, dimH (t x) := dimH_bUnion hSc _
_ <= r := iSup₂_le fun x hx => htr x hSs hx

/--
theorem `bsupr_limsup_dimH` / 定理 `bsupr_limsup_dimH`

English:
theorem bsupr_limsup_dimH
  given: (s : Set X)
  statement: ⨆ x in s, limsup dimH (𝓝[s] x).smallSets = dimH s
  proof: by
  refine le_antisymm (iSup₂_le fun x _ => ?_) ?_
  · refine limsup_le_of_le isCobounded_le_of_bot ?_
    exact eventually_smallSets.2 ⟨s, self_mem_nhdsWithin, fun t => dimH_mono⟩
  · refine le_of_forall_lt_imp_le_of_dense fun r hr => ?_
    rcases exists_mem_nhdsWithin_lt_dimH_of_lt_dimH hr with 

中文:
定理 bsupr_limsup_dimH
  条件: (s : Set X)
  结论: ⨆ x in s, limsup dimH (𝓝[s] x).smallSets = dimH s
  证明: by
  refine le_antisymm (iSup₂_le fun x _ => ?_) ?_
  · refine limsup_le_of_le isCobounded_le_of_bot ?_
    exact eventually_smallSets.2 ⟨s, self_mem_nhdsWithin, fun t => dimH_mono⟩
  · refine le_of_forall_lt_imp_le_of_dense fun r hr => ?_
    rcases exists_mem_nhdsWithin_lt_dimH_of_lt_dimH hr with 

Depends on / 依赖: Subset, Subset.rfl, dimH_mono, eventually_smallSets, exists_mem_nhdsWithin_lt_dimH_of_lt_dimH, isCobounded_le_of_bot, le.trans, le_antisymm, le_of_forall_lt_imp_le_of_dense, le_sInf, limsup_eq, limsup_le_of_le, self_mem_nhdsWithin
-/
theorem bsupr_limsup_dimH (s : Set X) : ⨆ x in s, limsup dimH (𝓝[s] x).smallSets = dimH s := by
  refine le_antisymm (iSup₂_le fun x _ => ?_) ?_
  · refine limsup_le_of_le isCobounded_le_of_bot ?_
    exact eventually_smallSets.2 ⟨s, self_mem_nhdsWithin, fun t => dimH_mono⟩
  · refine le_of_forall_lt_imp_le_of_dense fun r hr => ?_
    rcases exists_mem_nhdsWithin_lt_dimH_of_lt_dimH hr with ⟨x, hxs, hxr⟩
    refine le_iSup₂_of_le x hxs ?_; rw [limsup_eq]; refine le_sInf fun b hb => ?_
    rcases eventually_smallSets.1 hb with ⟨t, htx, ht⟩
    exact (hxr t htx).le.trans (ht t Subset.rfl)

/--
theorem `iSup_limsup_dimH` / 定理 `iSup_limsup_dimH`

English:
theorem iSup_limsup_dimH
  given: (s : Set X)
  statement: ⨆ x, limsup dimH (𝓝[s] x).smallSets = dimH s
  proof: by
  refine le_antisymm (iSup_le fun x => ?_) ?_
  · refine limsup_le_of_le isCobounded_le_of_bot ?_
    exact eventually_smallSets.2 ⟨s, self_mem_nhdsWithin, fun t => dimH_mono⟩
  · rw [← bsupr_limsup_dimH]; exact iSup₂_le_iSup _ _

中文:
定理 iSup_limsup_dimH
  条件: (s : Set X)
  结论: ⨆ x, limsup dimH (𝓝[s] x).smallSets = dimH s
  证明: by
  refine le_antisymm (iSup_le fun x => ?_) ?_
  · refine limsup_le_of_le isCobounded_le_of_bot ?_
    exact eventually_smallSets.2 ⟨s, self_mem_nhdsWithin, fun t => dimH_mono⟩
  · rw [← bsupr_limsup_dimH]; exact iSup₂_le_iSup _ _

Depends on / 依赖: bsupr_limsup_dimH, dimH_mono, eventually_smallSets, iSup_le, isCobounded_le_of_bot, le_antisymm, limsup_le_of_le, self_mem_nhdsWithin
-/
theorem iSup_limsup_dimH (s : Set X) : ⨆ x, limsup dimH (𝓝[s] x).smallSets = dimH s := by
  refine le_antisymm (iSup_le fun x => ?_) ?_
  · refine limsup_le_of_le isCobounded_le_of_bot ?_
    exact eventually_smallSets.2 ⟨s, self_mem_nhdsWithin, fun t => dimH_mono⟩
  · rw [← bsupr_limsup_dimH]; exact iSup₂_le_iSup _ _

end

/-!
### Hausdorff dimension and Hölder continuity
-/


variable {C K r : Real>=0} {f : X -> Y} {s : Set X}

/--
theorem `HolderOnWith.dimH_image_le` / 定理 `HolderOnWith.dimH_image_le`

English:
theorem HolderOnWith.dimH_image_le
  given: (h : HolderOnWith C r f s) (hr : 0 < r)
  proof: by
  borelize X Y
  refine dimH_le fun d hd => ?_
  have := h.hausdorffMeasure_image_le hr d.coe_nonneg
  rw [hd]; rw [← ENNReal.coe_rpow_of_nonneg _ d.coe_nonneg]; rw [top_le_iff] at this
  have Hrd : μH[(r * d : Real>=0)] s = ⊤ := by
    contrapose this
    finiteness
  rw [ENNReal.le_div_iff_mul_

中文:
定理 HolderOnWith.dimH_image_le
  条件: (h : HolderOnWith C r f s) (hr : 0 < r)
  证明: by
  borelize X Y
  refine dimH_le fun d hd => ?_
  have := h.hausdorffMeasure_image_le hr d.coe_nonneg
  rw [hd]; rw [← ENNReal.coe_rpow_of_nonneg _ d.coe_nonneg]; rw [top_le_iff] at this
  have Hrd : μH[(r * d : Real>=0)] s = ⊤ := by
    contrapose this
    finiteness
  rw [ENNReal.le_div_iff_mul_

Depends on / 依赖: ENNReal, ENNReal.coe_eq_zero, ENNReal.coe_mul, ENNReal.coe_ne_top, ENNReal.coe_rpow_of_nonneg, ENNReal.le_div_iff_mul_le, Or.inl, borelize, coe_eq_zero, coe_mul, coe_ne_top, coe_nonneg, coe_rpow_of_nonneg, contrapose, d.coe_nonneg, dimH_le, exacts, finiteness, h.hausdorffMeasure_image_le, hausdorffMeasure_image_le
-/
theorem HolderOnWith.dimH_image_le (h : HolderOnWith C r f s) (hr : 0 < r) :
    dimH (f '' s) <= dimH s / r := by
  borelize X Y
  refine dimH_le fun d hd => ?_
  have := h.hausdorffMeasure_image_le hr d.coe_nonneg
  rw [hd]; rw [← ENNReal.coe_rpow_of_nonneg _ d.coe_nonneg]; rw [top_le_iff] at this
  have Hrd : μH[(r * d : Real>=0)] s = ⊤ := by
    contrapose this
    finiteness
  rw [ENNReal.le_div_iff_mul_le]; rw [mul_comm]; rw [← ENNReal.coe_mul]
  exacts [le_dimH_of_hausdorffMeasure_eq_top Hrd, Or.inl (mt ENNReal.coe_eq_zero.1 hr.ne'),
    Or.inl ENNReal.coe_ne_top]

namespace HolderWith

/--
theorem `dimH_image_le` / 定理 `dimH_image_le`

English:
theorem dimH_image_le
  given: (h : HolderWith C r f) (hr : 0 < r) (s : Set X)
  proof: (h.holderOnWith s).dimH_image_le hr

中文:
定理 dimH_image_le
  条件: (h : HolderWith C r f) (hr : 0 < r) (s : Set X)
  证明: (h.holderOnWith s).dimH_image_le hr

Depends on / 依赖: dimH_image_le, h.holderOnWith, holderOnWith
-/
theorem dimH_image_le (h : HolderWith C r f) (hr : 0 < r) (s : Set X) :
    dimH (f '' s) <= dimH s / r :=
  (h.holderOnWith s).dimH_image_le hr

/--
theorem `dimH_range_le` / 定理 `dimH_range_le`

English:
theorem dimH_range_le
  given: (h : HolderWith C r f) (hr : 0 < r)
  proof: @image_univ _ _ f ▸ h.dimH_image_le hr univ

中文:
定理 dimH_range_le
  条件: (h : HolderWith C r f) (hr : 0 < r)
  证明: @image_univ _ _ f ▸ h.dimH_image_le hr univ

Depends on / 依赖: dimH_image_le, h.dimH_image_le, image_univ
-/
theorem dimH_range_le (h : HolderWith C r f) (hr : 0 < r) :
    dimH (range f) <= dimH (univ : Set X) / r :=
  @image_univ _ _ f ▸ h.dimH_image_le hr univ

end HolderWith

/--
theorem `dimH_image_le_of_locally_holder_on` / 定理 `dimH_image_le_of_locally_holder_on`

English:
theorem dimH_image_le_of_locally_holder_on
  statement: [SecondCountableTopology X] {r : Real>=0} {f : X -> Y}
  proof: by
  choose! C t htn hC using hf
  rcases countable_cover_nhdsWithin htn with ⟨u, hus, huc, huU⟩
  replace huU := inter_eq_self_of_subset_left huU; rw [inter_iUnion₂] at huU
  rw [← huU]; rw [image_iUnion₂]; rw [dimH_bUnion huc]; rw [dimH_bUnion huc]; simp only [ENNReal.iSup_div]
  exact iSup₂_mono 

中文:
定理 dimH_image_le_of_locally_holder_on
  结论: [SecondCountableTopology X] {r : 实数>=0} {f : X -> Y}
  证明: by
  choose! C t htn hC using hf
  rcases countable_cover_nhdsWithin htn with ⟨u, hus, huc, huU⟩
  replace huU := inter_eq_self_of_subset_left huU; rw [inter_iUnion₂] at huU
  rw [← huU]; rw [image_iUnion₂]; rw [dimH_bUnion huc]; rw [dimH_bUnion huc]; simp only [ENNReal.iSup_div]
  exact iSup₂_mono 

Depends on / 依赖: ENNReal, ENNReal.iSup_div, countable_cover_nhdsWithin, dimH_bUnion, dimH_image_le, iSup_div, inter_eq_self_of_subset_left, inter_subset_right, replace
-/
theorem dimH_image_le_of_locally_holder_on [SecondCountableTopology X] {r : Real>=0} {f : X -> Y}
    (hr : 0 < r) {s : Set X} (hf : forall x in s, exists C : Real>=0, exists t in 𝓝[s] x, HolderOnWith C r f t) :
    dimH (f '' s) <= dimH s / r := by
  choose! C t htn hC using hf
  rcases countable_cover_nhdsWithin htn with ⟨u, hus, huc, huU⟩
  replace huU := inter_eq_self_of_subset_left huU; rw [inter_iUnion₂] at huU
  rw [← huU]; rw [image_iUnion₂]; rw [dimH_bUnion huc]; rw [dimH_bUnion huc]; simp only [ENNReal.iSup_div]
  exact iSup₂_mono fun x hx => ((hC x (hus hx)).mono inter_subset_right).dimH_image_le hr

/--
theorem `dimH_range_le_of_locally_holder_on` / 定理 `dimH_range_le_of_locally_holder_on`

English:
theorem dimH_range_le_of_locally_holder_on
  statement: [SecondCountableTopology X] {r : Real>=0} {f : X -> Y}
  proof: by
  rw [← image_univ]
  refine dimH_image_le_of_locally_holder_on hr fun x _ => ?_
  simpa only [exists_prop, nhdsWithin_univ] using hf x

中文:
定理 dimH_range_le_of_locally_holder_on
  结论: [SecondCountableTopology X] {r : 实数>=0} {f : X -> Y}
  证明: by
  rw [← image_univ]
  refine dimH_image_le_of_locally_holder_on hr fun x _ => ?_
  simpa only [exists_prop, nhdsWithin_univ] using hf x

Depends on / 依赖: dimH_image_le_of_locally_holder_on, exists_prop, image_univ, nhdsWithin_univ
-/
theorem dimH_range_le_of_locally_holder_on [SecondCountableTopology X] {r : Real>=0} {f : X -> Y}
    (hr : 0 < r) (hf : forall x : X, exists C : Real>=0, exists s in 𝓝 x, HolderOnWith C r f s) :
    dimH (range f) <= dimH (univ : Set X) / r := by
  rw [← image_univ]
  refine dimH_image_le_of_locally_holder_on hr fun x _ => ?_
  simpa only [exists_prop, nhdsWithin_univ] using hf x

/-!
### Hausdorff dimension and Lipschitz continuity
-/


/--
theorem `LipschitzOnWith.dimH_image_le` / 定理 `LipschitzOnWith.dimH_image_le`

English:
theorem LipschitzOnWith.dimH_image_le
  given: (h : LipschitzOnWith K f s)
  statement: dimH (f '' s) <= dimH s
  proof: by
  simpa using h.holderOnWith.dimH_image_le zero_lt_one

中文:
定理 LipschitzOnWith.dimH_image_le
  条件: (h : LipschitzOnWith K f s)
  结论: dimH (f '' s) <= dimH s
  证明: by
  simpa using h.holderOnWith.dimH_image_le zero_lt_one

Depends on / 依赖: dimH_image_le, h.holderOnWith.dimH_image_le, holderOnWith, zero_lt_one
-/
theorem LipschitzOnWith.dimH_image_le (h : LipschitzOnWith K f s) : dimH (f '' s) <= dimH s := by
  simpa using h.holderOnWith.dimH_image_le zero_lt_one

namespace LipschitzWith

/--
theorem `dimH_image_le` / 定理 `dimH_image_le`

English:
theorem dimH_image_le
  given: (h : LipschitzWith K f) (s : Set X)
  statement: dimH (f '' s) <= dimH s
  proof: h.lipschitzOnWith.dimH_image_le

中文:
定理 dimH_image_le
  条件: (h : LipschitzWith K f) (s : Set X)
  结论: dimH (f '' s) <= dimH s
  证明: h.lipschitzOnWith.dimH_image_le

Depends on / 依赖: dimH_image_le, h.lipschitzOnWith.dimH_image_le, lipschitzOnWith
-/
theorem dimH_image_le (h : LipschitzWith K f) (s : Set X) : dimH (f '' s) <= dimH s :=
  h.lipschitzOnWith.dimH_image_le

/--
theorem `dimH_range_le` / 定理 `dimH_range_le`

English:
theorem dimH_range_le
  given: (h : LipschitzWith K f)
  statement: dimH (range f) <= dimH (univ : Set X)
  proof: @image_univ _ _ f ▸ h.dimH_image_le univ

中文:
定理 dimH_range_le
  条件: (h : LipschitzWith K f)
  结论: dimH (range f) <= dimH (univ : Set X)
  证明: @image_univ _ _ f ▸ h.dimH_image_le univ

Depends on / 依赖: dimH_image_le, h.dimH_image_le, image_univ
-/
theorem dimH_range_le (h : LipschitzWith K f) : dimH (range f) <= dimH (univ : Set X) :=
  @image_univ _ _ f ▸ h.dimH_image_le univ

end LipschitzWith

/--
theorem `dimH_image_le_of_locally_lipschitzOn` / 定理 `dimH_image_le_of_locally_lipschitzOn`

English:
theorem dimH_image_le_of_locally_lipschitzOn
  statement: [SecondCountableTopology X] {f : X -> Y} {s : Set X}
  proof: by
  have : forall x in s, exists C : Real>=0, exists t in 𝓝[s] x, HolderOnWith C 1 f t := by
    simpa only [holderOnWith_one] using hf
  simpa only [ENNReal.coe_one, div_one] using dimH_image_le_of_locally_holder_on zero_lt_one this

中文:
定理 dimH_image_le_of_locally_lipschitzOn
  结论: [SecondCountableTopology X] {f : X -> Y} {s : Set X}
  证明: by
  have : forall x in s, exists C : Real>=0, exists t in 𝓝[s] x, HolderOnWith C 1 f t := by
    simpa only [holderOnWith_one] using hf
  simpa only [ENNReal.coe_one, div_one] using dimH_image_le_of_locally_holder_on zero_lt_one this

Depends on / 依赖: ENNReal, ENNReal.coe_one, HolderOnWith, coe_one, dimH_image_le_of_locally_holder_on, div_one, holderOnWith_one, zero_lt_one
-/
theorem dimH_image_le_of_locally_lipschitzOn [SecondCountableTopology X] {f : X -> Y} {s : Set X}
    (hf : forall x in s, exists C : Real>=0, exists t in 𝓝[s] x, LipschitzOnWith C f t) : dimH (f '' s) <= dimH s := by
  have : forall x in s, exists C : Real>=0, exists t in 𝓝[s] x, HolderOnWith C 1 f t := by
    simpa only [holderOnWith_one] using hf
  simpa only [ENNReal.coe_one, div_one] using dimH_image_le_of_locally_holder_on zero_lt_one this

/--
theorem `dimH_range_le_of_locally_lipschitzOn` / 定理 `dimH_range_le_of_locally_lipschitzOn`

English:
theorem dimH_range_le_of_locally_lipschitzOn
  statement: [SecondCountableTopology X] {f : X -> Y}
  proof: by
  rw [← image_univ]
  refine dimH_image_le_of_locally_lipschitzOn fun x _ => ?_
  simpa only [exists_prop, nhdsWithin_univ] using hf x

中文:
定理 dimH_range_le_of_locally_lipschitzOn
  结论: [SecondCountableTopology X] {f : X -> Y}
  证明: by
  rw [← image_univ]
  refine dimH_image_le_of_locally_lipschitzOn fun x _ => ?_
  simpa only [exists_prop, nhdsWithin_univ] using hf x

Depends on / 依赖: dimH_image_le_of_locally_lipschitzOn, exists_prop, image_univ, nhdsWithin_univ
-/
theorem dimH_range_le_of_locally_lipschitzOn [SecondCountableTopology X] {f : X -> Y}
    (hf : forall x : X, exists C : Real>=0, exists s in 𝓝 x, LipschitzOnWith C f s) :
    dimH (range f) <= dimH (univ : Set X) := by
  rw [← image_univ]
  refine dimH_image_le_of_locally_lipschitzOn fun x _ => ?_
  simpa only [exists_prop, nhdsWithin_univ] using hf x

namespace AntilipschitzWith

/--
theorem `dimH_preimage_le` / 定理 `dimH_preimage_le`

English:
theorem dimH_preimage_le
  given: (hf : AntilipschitzWith K f) (s : Set Y)
  statement: dimH (f ⁻¹' s) <= dimH s
  proof: by
  borelize X Y
  refine dimH_le fun d hd => le_dimH_of_hausdorffMeasure_eq_top ?_
  have := hf.hausdorffMeasure_preimage_le d.coe_nonneg s
  rw [hd]; rw [top_le_iff] at this
  contrapose! this
  exact ENNReal.mul_ne_top (by simp) this

中文:
定理 dimH_preimage_le
  条件: (hf : AntilipschitzWith K f) (s : Set Y)
  结论: dimH (f ⁻¹' s) <= dimH s
  证明: by
  borelize X Y
  refine dimH_le fun d hd => le_dimH_of_hausdorffMeasure_eq_top ?_
  have := hf.hausdorffMeasure_preimage_le d.coe_nonneg s
  rw [hd]; rw [top_le_iff] at this
  contrapose! this
  exact ENNReal.mul_ne_top (by simp) this

Depends on / 依赖: ENNReal, ENNReal.mul_ne_top, borelize, coe_nonneg, contrapose, d.coe_nonneg, dimH_le, hausdorffMeasure_preimage_le, hf.hausdorffMeasure_preimage_le, le_dimH_of_hausdorffMeasure_eq_top, mul_ne_top, top_le_iff
-/
theorem dimH_preimage_le (hf : AntilipschitzWith K f) (s : Set Y) : dimH (f ⁻¹' s) <= dimH s := by
  borelize X Y
  refine dimH_le fun d hd => le_dimH_of_hausdorffMeasure_eq_top ?_
  have := hf.hausdorffMeasure_preimage_le d.coe_nonneg s
  rw [hd]; rw [top_le_iff] at this
  contrapose! this
  exact ENNReal.mul_ne_top (by simp) this

/--
theorem `le_dimH_image` / 定理 `le_dimH_image`

English:
theorem le_dimH_image
  given: (hf : AntilipschitzWith K f) (s : Set X)
  statement: dimH s <= dimH (f '' s)
  proof: calc
    dimH s <= dimH (f ⁻¹' f '' s) := dimH_mono (subset_preimage_image _ _)
    _ <= dimH (f '' s) := hf.dimH_preimage_le _

中文:
定理 le_dimH_image
  条件: (hf : AntilipschitzWith K f) (s : Set X)
  结论: dimH s <= dimH (f '' s)
  证明: calc
    dimH s <= dimH (f ⁻¹' f '' s) := dimH_mono (subset_preimage_image _ _)
    _ <= dimH (f '' s) := hf.dimH_preimage_le _

Depends on / 依赖: dimH_mono, dimH_preimage_le, hf.dimH_preimage_le, subset_preimage_image
-/
theorem le_dimH_image (hf : AntilipschitzWith K f) (s : Set X) : dimH s <= dimH (f '' s) :=
  calc
    dimH s <= dimH (f ⁻¹' f '' s) := dimH_mono (subset_preimage_image _ _)
    _ <= dimH (f '' s) := hf.dimH_preimage_le _

end AntilipschitzWith



/--
theorem `Isometry.dimH_image` / 定理 `Isometry.dimH_image`

English:
theorem Isometry.dimH_image
  given: (hf : Isometry f) (s : Set X)
  statement: dimH (f '' s) = dimH s
  proof: le_antisymm (hf.lipschitz.dimH_image_le _) (hf.antilipschitz.le_dimH_image _)

中文:
定理 Isometry.dimH_image
  条件: (hf : Isometry f) (s : Set X)
  结论: dimH (f '' s) = dimH s
  证明: le_antisymm (hf.lipschitz.dimH_image_le _) (hf.antilipschitz.le_dimH_image _)

Depends on / 依赖: antilipschitz, dimH_image_le, hf.antilipschitz.le_dimH_image, hf.lipschitz.dimH_image_le, le_antisymm, le_dimH_image, lipschitz
-/
theorem Isometry.dimH_image (hf : Isometry f) (s : Set X) : dimH (f '' s) = dimH s :=
  le_antisymm (hf.lipschitz.dimH_image_le _) (hf.antilipschitz.le_dimH_image _)

namespace IsometryEquiv

@[simp]
/--
theorem `dimH_image` / 定理 `dimH_image`

English:
theorem dimH_image
  given: (e : X ≃ᵢ Y) (s : Set X)
  statement: dimH (e '' s) = dimH s
  proof: e.isometry.dimH_image s

@[simp]

中文:
定理 dimH_image
  条件: (e : X ≃ᵢ Y) (s : Set X)
  结论: dimH (e '' s) = dimH s
  证明: e.isometry.dimH_image s

@[simp]

Depends on / 依赖: dimH_image, e.isometry.dimH_image, isometry
-/
theorem dimH_image (e : X ≃ᵢ Y) (s : Set X) : dimH (e '' s) = dimH s :=
  e.isometry.dimH_image s

@[simp]
/--
theorem `dimH_preimage` / 定理 `dimH_preimage`

English:
theorem dimH_preimage
  given: (e : X ≃ᵢ Y) (s : Set Y)
  statement: dimH (e ⁻¹' s) = dimH s
  proof: by
  rw [← e.image_symm]; rw [e.symm.dimH_image]

中文:
定理 dimH_preimage
  条件: (e : X ≃ᵢ Y) (s : Set Y)
  结论: dimH (e ⁻¹' s) = dimH s
  证明: by
  rw [← e.image_symm]; rw [e.symm.dimH_image]

Depends on / 依赖: dimH_image, e.image_symm, e.symm.dimH_image, image_symm
-/
theorem dimH_preimage (e : X ≃ᵢ Y) (s : Set Y) : dimH (e ⁻¹' s) = dimH s := by
  rw [← e.image_symm]; rw [e.symm.dimH_image]

/--
theorem `dimH_univ` / 定理 `dimH_univ`

English:
theorem dimH_univ
  given: (e : X ≃ᵢ Y)
  statement: dimH (univ : Set X) = dimH (univ : Set Y)
  proof: by
  rw [← e.dimH_preimage univ]; rw [preimage_univ]

中文:
定理 dimH_univ
  条件: (e : X ≃ᵢ Y)
  结论: dimH (univ : Set X) = dimH (univ : Set Y)
  证明: by
  rw [← e.dimH_preimage univ]; rw [preimage_univ]

Depends on / 依赖: dimH_preimage, e.dimH_preimage, preimage_univ
-/
theorem dimH_univ (e : X ≃ᵢ Y) : dimH (univ : Set X) = dimH (univ : Set Y) := by
  rw [← e.dimH_preimage univ]; rw [preimage_univ]

end IsometryEquiv

namespace ContinuousLinearEquiv

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

@[simp]
/--
theorem `dimH_image` / 定理 `dimH_image`

English:
theorem dimH_image
  given: (e : E ≃L[𝕜] F) (s : Set E)
  statement: dimH (e '' s) = dimH s
  proof: le_antisymm (e.lipschitz.dimH_image_le s) by
    simpa only [e.symm_image_image] using e.symm.lipschitz.dimH_image_le (e '' s)

@[simp]

中文:
定理 dimH_image
  条件: (e : E ≃L[𝕜] F) (s : Set E)
  结论: dimH (e '' s) = dimH s
  证明: le_antisymm (e.lipschitz.dimH_image_le s) by
    simpa only [e.symm_image_image] using e.symm.lipschitz.dimH_image_le (e '' s)

@[simp]

Depends on / 依赖: dimH_image_le, e.lipschitz.dimH_image_le, e.symm.lipschitz.dimH_image_le, e.symm_image_image, le_antisymm, lipschitz, symm_image_image
-/
theorem dimH_image (e : E ≃L[𝕜] F) (s : Set E) : dimH (e '' s) = dimH s :=
le_antisymm (e.lipschitz.dimH_image_le s) by
    simpa only [e.symm_image_image] using e.symm.lipschitz.dimH_image_le (e '' s)

@[simp]
/--
theorem `dimH_preimage` / 定理 `dimH_preimage`

English:
theorem dimH_preimage
  given: (e : E ≃L[𝕜] F) (s : Set F)
  statement: dimH (e ⁻¹' s) = dimH s
  proof: by
  rw [← e.image_symm_eq_preimage]; rw [e.symm.dimH_image]

中文:
定理 dimH_preimage
  条件: (e : E ≃L[𝕜] F) (s : Set F)
  结论: dimH (e ⁻¹' s) = dimH s
  证明: by
  rw [← e.image_symm_eq_preimage]; rw [e.symm.dimH_image]

Depends on / 依赖: dimH_image, e.image_symm_eq_preimage, e.symm.dimH_image, image_symm_eq_preimage
-/
theorem dimH_preimage (e : E ≃L[𝕜] F) (s : Set F) : dimH (e ⁻¹' s) = dimH s := by
  rw [← e.image_symm_eq_preimage]; rw [e.symm.dimH_image]

/--
theorem `dimH_univ` / 定理 `dimH_univ`

English:
theorem dimH_univ
  given: (e : E ≃L[𝕜] F)
  statement: dimH (univ : Set E) = dimH (univ : Set F)
  proof: by
  rw [← e.dimH_preimage]; rw [preimage_univ]

中文:
定理 dimH_univ
  条件: (e : E ≃L[𝕜] F)
  结论: dimH (univ : Set E) = dimH (univ : Set F)
  证明: by
  rw [← e.dimH_preimage]; rw [preimage_univ]

Depends on / 依赖: dimH_preimage, e.dimH_preimage, preimage_univ
-/
theorem dimH_univ (e : E ≃L[𝕜] F) : dimH (univ : Set E) = dimH (univ : Set F) := by
  rw [← e.dimH_preimage]; rw [preimage_univ]

end ContinuousLinearEquiv

/-!
### Hausdorff dimension in a real vector space
-/


namespace Real

variable {E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace Real E] [FiniteDimensional Real E]

/--
theorem `dimH_ball_pi` / 定理 `dimH_ball_pi`

English:
theorem dimH_ball_pi
  given: (x : ι -> Real) {r : Real} (hr : 0 < r)
  proof: by
  cases isEmpty_or_nonempty ι
  · rwa [dimH_subsingleton, eq_comm, Nat.cast_eq_zero, Fintype.card_eq_zero_iff]
    exact fun x _ y _ => Subsingleton.elim x y
  · rw [← ENNReal.coe_natCast]
    have : μH[Fintype.card ι] (Metric.ball x r) = ENNReal.ofReal ((2 * r) ^ Fintype.card ι) := by
      rw [

中文:
定理 dimH_ball_pi
  条件: (x : ι -> 实数) {r : 实数} (hr : 0 < r)
  证明: by
  cases isEmpty_or_nonempty ι
  · rwa [dimH_subsingleton, eq_comm, Nat.cast_eq_zero, Fintype.card_eq_zero_iff]
    exact fun x _ y _ => Subsingleton.elim x y
  · rw [← ENNReal.coe_natCast]
    have : μH[Fintype.card ι] (Metric.ball x r) = ENNReal.ofReal ((2 * r) ^ Fintype.card ι) := by
      rw [

Depends on / 依赖: ENNReal, ENNReal.coe_natCast, ENNReal.ofReal, ENNReal.ofReal_ne_, Fintype, Fintype.card, Fintype.card_eq_zero_iff, Metric, Metric.ball, NNReal, NNReal.coe_natCast, Nat.cast_eq_zero, Real.volume_pi_ball, Subsingleton, Subsingleton.elim, card_eq_zero_iff, cast_eq_zero, coe_natCast, dimH_of_hausdorffMeasure_ne_zero_ne_top, dimH_subsingleton
-/
theorem dimH_ball_pi (x : ι -> Real) {r : Real} (hr : 0 < r) :
    dimH (Metric.ball x r) = Fintype.card ι := by
  cases isEmpty_or_nonempty ι
  · rwa [dimH_subsingleton, eq_comm, Nat.cast_eq_zero, Fintype.card_eq_zero_iff]
    exact fun x _ y _ => Subsingleton.elim x y
  · rw [← ENNReal.coe_natCast]
    have : μH[Fintype.card ι] (Metric.ball x r) = ENNReal.ofReal ((2 * r) ^ Fintype.card ι) := by
      rw [hausdorffMeasure_pi_real]; rw [Real.volume_pi_ball _ hr]
    refine dimH_of_hausdorffMeasure_ne_zero_ne_top ?_ ?_ <;> rw [NNReal.coe_natCast, this]
    · simp [pow_pos (mul_pos (zero_lt_two' Real) hr)]
    · exact ENNReal.ofReal_ne_top

/--
theorem `dimH_ball_pi_fin` / 定理 `dimH_ball_pi_fin`

English:
theorem dimH_ball_pi_fin
  given: {n : Nat} (x : Fin n -> Real) {r : Real} (hr : 0 < r)
  proof: by rw [dimH_ball_pi x hr, Fintype.card_fin]

中文:
定理 dimH_ball_pi_fin
  条件: {n : 自然数} (x : Fin n -> 实数) {r : 实数} (hr : 0 < r)
  证明: by rw [dimH_ball_pi x hr, Fintype.card_fin]

Depends on / 依赖: Fintype, Fintype.card_fin, card_fin, dimH_ball_pi
-/
theorem dimH_ball_pi_fin {n : Nat} (x : Fin n -> Real) {r : Real} (hr : 0 < r) :
    dimH (Metric.ball x r) = n := by rw [dimH_ball_pi x hr, Fintype.card_fin]

/--
theorem `dimH_univ_pi` / 定理 `dimH_univ_pi`

English:
theorem dimH_univ_pi
  given: (ι : Type*) [Fintype ι]
  statement: dimH (univ : Set (ι -> Real)) = Fintype.card ι
  proof: by
  simp only [← Metric.iUnion_ball_nat_succ (0 : ι -> Real), dimH_iUnion,
    dimH_ball_pi _ (Nat.cast_add_one_pos _), iSup_const]

中文:
定理 dimH_univ_pi
  条件: (ι : 类型) [Fintype ι]
  结论: dimH (univ : Set (ι -> 实数)) = Fintype.card ι
  证明: by
  simp only [← Metric.iUnion_ball_nat_succ (0 : ι -> Real), dimH_iUnion,
    dimH_ball_pi _ (Nat.cast_add_one_pos _), iSup_const]

Depends on / 依赖: Metric, Metric.iUnion_ball_nat_succ, Nat.cast_add_one_pos, cast_add_one_pos, dimH_ball_pi, dimH_iUnion, iSup_const, iUnion_ball_nat_succ
-/
theorem dimH_univ_pi (ι : Type*) [Fintype ι] : dimH (univ : Set (ι -> Real)) = Fintype.card ι := by
  simp only [← Metric.iUnion_ball_nat_succ (0 : ι -> Real), dimH_iUnion,
    dimH_ball_pi _ (Nat.cast_add_one_pos _), iSup_const]

/--
theorem `dimH_univ_pi_fin` / 定理 `dimH_univ_pi_fin`

English:
theorem dimH_univ_pi_fin
  given: (n : Nat)
  statement: dimH (univ : Set (Fin n -> Real)) = n
  proof: by
  rw [dimH_univ_pi]; rw [Fintype.card_fin]

中文:
定理 dimH_univ_pi_fin
  条件: (n : 自然数)
  结论: dimH (univ : Set (Fin n -> 实数)) = n
  证明: by
  rw [dimH_univ_pi]; rw [Fintype.card_fin]

Depends on / 依赖: Fintype, Fintype.card_fin, card_fin, dimH_univ_pi
-/
theorem dimH_univ_pi_fin (n : Nat) : dimH (univ : Set (Fin n -> Real)) = n := by
  rw [dimH_univ_pi]; rw [Fintype.card_fin]

/--
theorem `dimH_of_mem_nhds` / 定理 `dimH_of_mem_nhds`

English:
theorem dimH_of_mem_nhds
  given: {x : E} {s : Set E} (h : s in 𝓝 x)
  statement: dimH s = finrank Real E
  proof: by
  have e : E ≃L[Real] Fin (finrank Real E) -> Real :=
    ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun Real).symm
  rw [← e.dimH_image]
  refine le_antisymm ?_ ?_
  · exact (dimH_mono (subset_univ _)).trans_eq (dimH_univ_pi_fin _)
  · have : e '' s in 𝓝 (e x) := by rw [← e.map_nhds_e

中文:
定理 dimH_of_mem_nhds
  条件: {x : E} {s : Set E} (h : s in 𝓝 x)
  结论: dimH s = finrank 实数 E
  证明: by
  have e : E ≃L[Real] Fin (finrank Real E) -> Real :=
    ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun Real).symm
  rw [← e.dimH_image]
  refine le_antisymm ?_ ?_
  · exact (dimH_mono (subset_univ _)).trans_eq (dimH_univ_pi_fin _)
  · have : e '' s in 𝓝 (e x) := by rw [← e.map_nhds_e

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.ofFinrankEq, Metric, Metric.nhds_basis_ball.mem_iff, Module, Module.finrank_fin_fun, dimH_ball_pi_fin, dimH_image, dimH_mono, dimH_univ_pi_fin, e.dimH_image, e.map_nhds_eq, finrank, finrank_fin_fun, image_mem_map, le_antisymm, map_nhds_eq, mem_iff, nhds_basis_ball, ofFinrankEq
-/
theorem dimH_of_mem_nhds {x : E} {s : Set E} (h : s in 𝓝 x) : dimH s = finrank Real E := by
  have e : E ≃L[Real] Fin (finrank Real E) -> Real :=
    ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun Real).symm
  rw [← e.dimH_image]
  refine le_antisymm ?_ ?_
  · exact (dimH_mono (subset_univ _)).trans_eq (dimH_univ_pi_fin _)
  · have : e '' s in 𝓝 (e x) := by rw [← e.map_nhds_eq]; exact image_mem_map h
    rcases Metric.nhds_basis_ball.mem_iff.1 this with ⟨r, hr0, hr⟩
    simpa only [dimH_ball_pi_fin (e x) hr0] using dimH_mono hr

/--
theorem `dimH_of_nonempty_interior` / 定理 `dimH_of_nonempty_interior`

English:
theorem dimH_of_nonempty_interior
  given: {s : Set E} (h : (interior s).Nonempty)
  statement: dimH s = finrank Real E
  proof: let ⟨_, hx⟩ := h
  dimH_of_mem_nhds (mem_interior_iff_mem_nhds.1 hx)

中文:
定理 dimH_of_nonempty_interior
  条件: {s : Set E} (h : (interior s).Nonempty)
  结论: dimH s = finrank 实数 E
  证明: let ⟨_, hx⟩ := h
  dimH_of_mem_nhds (mem_interior_iff_mem_nhds.1 hx)

Depends on / 依赖: dimH_of_mem_nhds, mem_interior_iff_mem_nhds
-/
theorem dimH_of_nonempty_interior {s : Set E} (h : (interior s).Nonempty) : dimH s = finrank Real E :=
  let ⟨_, hx⟩ := h
  dimH_of_mem_nhds (mem_interior_iff_mem_nhds.1 hx)

/--
theorem `Convex.dimH_eq_finrank_vectorSpan` / 定理 `Convex.dimH_eq_finrank_vectorSpan`

English:
theorem Convex.dimH_eq_finrank_vectorSpan
  given: {s : Set E} (hcvx : Convex Real s) (hne : s.Nonempty)
  proof: by
  have := hne.to_subtype
  let φ := AffineIsometryEquiv.constVSub Real
    (⟨hne.some, subset_affineSpan Real s hne.some_mem⟩ : affineSpan Real s)
  have hs_eq : s = (↑) '' ((↑) ⁻¹' s : Set (affineSpan Real s)) :=
    (image_preimage_eq_of_subset <| (subset_affineSpan Real s).trans Subtype.range_

中文:
定理 Convex.dimH_eq_finrank_vectorSpan
  条件: {s : Set E} (hcvx : Convex 实数 s) (hne : s.Nonempty)
  证明: by
  have := hne.to_subtype
  let φ := AffineIsometryEquiv.constVSub Real
    (⟨hne.some, subset_affineSpan Real s hne.some_mem⟩ : affineSpan Real s)
  have hs_eq : s = (↑) '' ((↑) ⁻¹' s : Set (affineSpan Real s)) :=
    (image_preimage_eq_of_subset <| (subset_affineSpan Real s).trans Subtype.range_

Depends on / 依赖: AffineIsometryEquiv, AffineIsometryEquiv.constVSub, Real.dimH_of_nonempty_interior, Subtype, Subtype.range_coe.superset, affineSpan, constVSub, dimH_image, dimH_of_nonempty_interior, direction_affineSpan, hne.some, hne.some_mem, hne.to_subtype, hs_eq, image_preimage_eq_of_subset, isometry, isometry.dimH_image, isometry_subtype_coe, isometry_subtype_coe.dimH_image, range_coe
-/
theorem Convex.dimH_eq_finrank_vectorSpan {s : Set E} (hcvx : Convex Real s) (hne : s.Nonempty) :
    dimH s = finrank Real (vectorSpan Real s) := by
  have := hne.to_subtype
  let φ := AffineIsometryEquiv.constVSub Real
    (⟨hne.some, subset_affineSpan Real s hne.some_mem⟩ : affineSpan Real s)
  have hs_eq : s = (↑) '' ((↑) ⁻¹' s : Set (affineSpan Real s)) :=
    (image_preimage_eq_of_subset <| (subset_affineSpan Real s).trans Subtype.range_coe.superset).symm
  rw [hs_eq]; rw [isometry_subtype_coe.dimH_image]; rw [← φ.isometry.dimH_image]; rw [Real.dimH_of_nonempty_interior]; rw [direction_affineSpan Real s]; rw [← hs_eq]
  simp_rw [← AffineIsometryEquiv.coe_toHomeomorph, ← φ.toHomeomorph.image_interior, image_nonempty]
  simpa [intrinsicInterior] using (intrinsicInterior_nonempty hcvx).mpr hne

variable (E)

/--
theorem `dimH_univ_eq_finrank` / 定理 `dimH_univ_eq_finrank`

English:
theorem dimH_univ_eq_finrank
  statement: dimH (univ : Set E) = finrank Real E
  proof: dimH_of_mem_nhds (@univ_mem _ (𝓝 0))

中文:
定理 dimH_univ_eq_finrank
  结论: dimH (univ : Set E) = finrank 实数 E
  证明: dimH_of_mem_nhds (@univ_mem _ (𝓝 0))

Depends on / 依赖: dimH_of_mem_nhds, univ_mem
-/
theorem dimH_univ_eq_finrank : dimH (univ : Set E) = finrank Real E :=
  dimH_of_mem_nhds (@univ_mem _ (𝓝 0))

/--
theorem `dimH_univ` / 定理 `dimH_univ`

English:
theorem dimH_univ
  statement: dimH (univ : Set Real) = 1
  proof: by
  rw [dimH_univ_eq_finrank Real]; rw [Module.finrank_self]; rw [Nat.cast_one]

中文:
定理 dimH_univ
  结论: dimH (univ : Set 实数) = 1
  证明: by
  rw [dimH_univ_eq_finrank Real]; rw [Module.finrank_self]; rw [Nat.cast_one]

Depends on / 依赖: Module, Module.finrank_self, Nat.cast_one, cast_one, dimH_univ_eq_finrank, finrank_self
-/
theorem dimH_univ : dimH (univ : Set Real) = 1 := by
  rw [dimH_univ_eq_finrank Real]; rw [Module.finrank_self]; rw [Nat.cast_one]

variable {E}

/--
theorem `dimH_lt_top` / 定理 `dimH_lt_top`

English:
theorem dimH_lt_top
  given: (s : Set E)
  statement: dimH s < ⊤
  proof: by calc
  dimH s <= dimH (univ : Set E) := dimH_mono (subset_univ s)
  _ = finrank Real E := dimH_univ_eq_finrank E
  _ < ⊤ := by simp

中文:
定理 dimH_lt_top
  条件: (s : Set E)
  结论: dimH s < ⊤
  证明: by calc
  dimH s <= dimH (univ : Set E) := dimH_mono (subset_univ s)
  _ = finrank Real E := dimH_univ_eq_finrank E
  _ < ⊤ := by simp

Depends on / 依赖: dimH_mono, dimH_univ_eq_finrank, finrank, subset_univ
-/
theorem dimH_lt_top (s : Set E) : dimH s < ⊤ := by calc
  dimH s <= dimH (univ : Set E) := dimH_mono (subset_univ s)
  _ = finrank Real E := dimH_univ_eq_finrank E
  _ < ⊤ := by simp

/--
theorem `dimH_ne_top` / 定理 `dimH_ne_top`

English:
theorem dimH_ne_top
  given: (s : Set E)
  statement: dimH s != ⊤
  proof: (dimH_lt_top s).ne

中文:
定理 dimH_ne_top
  条件: (s : Set E)
  结论: dimH s != ⊤
  证明: (dimH_lt_top s).ne

Depends on / 依赖: dimH_lt_top
-/
theorem dimH_ne_top (s : Set E) : dimH s != ⊤ := (dimH_lt_top s).ne

/--
lemma `hausdorffMeasure_of_finrank_lt` / 引理 `hausdorffMeasure_of_finrank_lt`

English:
lemma hausdorffMeasure_of_finrank_lt
  statement: [MeasurableSpace E] [BorelSpace E] {d : Real}
  proof: by
  lift d to Real>=0 using (Nat.cast_nonneg _).trans hd.le
  rw [← measure_univ_eq_zero]
  apply hausdorffMeasure_of_dimH_lt
  rw [dimH_univ_eq_finrank]
  exact mod_cast hd

中文:
引理 hausdorffMeasure_of_finrank_lt
  结论: [MeasurableSpace E] [BorelSpace E] {d : 实数}
  证明: by
  lift d to Real>=0 using (Nat.cast_nonneg _).trans hd.le
  rw [← measure_univ_eq_zero]
  apply hausdorffMeasure_of_dimH_lt
  rw [dimH_univ_eq_finrank]
  exact mod_cast hd

Depends on / 依赖: Nat.cast_nonneg, cast_nonneg, dimH_univ_eq_finrank, hausdorffMeasure_of_dimH_lt, hd.le, measure_univ_eq_zero, mod_cast
-/
lemma hausdorffMeasure_of_finrank_lt [MeasurableSpace E] [BorelSpace E] {d : Real}
    (hd : finrank Real E < d) : (μH[d] : Measure E) = 0 := by
  lift d to Real>=0 using (Nat.cast_nonneg _).trans hd.le
  rw [← measure_univ_eq_zero]
  apply hausdorffMeasure_of_dimH_lt
  rw [dimH_univ_eq_finrank]
  exact mod_cast hd

/--
theorem `dimH_segment` / 定理 `dimH_segment`

English:
theorem dimH_segment
  given: {x y : E} (h : x != y)
  proof: by
  rw [Convex.dimH_eq_finrank_vectorSpan (convex_segment x y) ⟨x]; rw [left_mem_segment Real x y⟩]; rw [vectorSpan_segment]
  simp [finrank_span_singleton (sub_ne_zero.mpr h.symm)]

中文:
定理 dimH_segment
  条件: {x y : E} (h : x != y)
  证明: by
  rw [Convex.dimH_eq_finrank_vectorSpan (convex_segment x y) ⟨x]; rw [left_mem_segment Real x y⟩]; rw [vectorSpan_segment]
  simp [finrank_span_singleton (sub_ne_zero.mpr h.symm)]

Depends on / 依赖: Convex, Convex.dimH_eq_finrank_vectorSpan, convex_segment, dimH_eq_finrank_vectorSpan, finrank_span_singleton, h.symm, left_mem_segment, sub_ne_zero, sub_ne_zero.mpr, vectorSpan_segment
-/
theorem dimH_segment {x y : E} (h : x != y) :
    dimH (segment Real x y) = 1 := by
  rw [Convex.dimH_eq_finrank_vectorSpan (convex_segment x y) ⟨x]; rw [left_mem_segment Real x y⟩]; rw [vectorSpan_segment]
  simp [finrank_span_singleton (sub_ne_zero.mpr h.symm)]

end Real

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [FiniteDimensional Real E]
  [NormedAddCommGroup F] [NormedSpace Real F]

/--
theorem `dense_compl_of_dimH_lt_finrank` / 定理 `dense_compl_of_dimH_lt_finrank`

English:
theorem dense_compl_of_dimH_lt_finrank
  given: {s : Set E} (hs : dimH s < finrank Real E)
  statement: Dense sᶜ
  proof: by
  refine fun x => mem_closure_iff_nhds.2 fun t ht => nonempty_iff_ne_empty.2 fun he => hs.not_ge ?_
  rw [← sdiff_eq]; rw [sdiff_eq_empty] at he
  rw [← Real.dimH_of_mem_nhds ht]
  exact dimH_mono he

中文:
定理 dense_compl_of_dimH_lt_finrank
  条件: {s : Set E} (hs : dimH s < finrank 实数 E)
  结论: Dense sᶜ
  证明: by
  refine fun x => mem_closure_iff_nhds.2 fun t ht => nonempty_iff_ne_empty.2 fun he => hs.not_ge ?_
  rw [← sdiff_eq]; rw [sdiff_eq_empty] at he
  rw [← Real.dimH_of_mem_nhds ht]
  exact dimH_mono he

Depends on / 依赖: Real.dimH_of_mem_nhds, dimH_mono, dimH_of_mem_nhds, hs.not_ge, mem_closure_iff_nhds, nonempty_iff_ne_empty, not_ge, sdiff_eq, sdiff_eq_empty
-/
theorem dense_compl_of_dimH_lt_finrank {s : Set E} (hs : dimH s < finrank Real E) : Dense sᶜ := by
  refine fun x => mem_closure_iff_nhds.2 fun t ht => nonempty_iff_ne_empty.2 fun he => hs.not_ge ?_
  rw [← sdiff_eq]; rw [sdiff_eq_empty] at he
  rw [← Real.dimH_of_mem_nhds ht]
  exact dimH_mono he

/-!
### Hausdorff dimension and `C¹`-smooth maps

`C¹`-smooth maps are locally Lipschitz continuous, hence they do not increase the Hausdorff
dimension of sets.
-/


/--
theorem `ContDiffOn.dimH_image_le` / 定理 `ContDiffOn.dimH_image_le`

English:
theorem ContDiffOn.dimH_image_le
  statement: {f : E -> F} {s t : Set E} (hf : ContDiffOn Real 1 f s)
  proof: dimH_image_le_of_locally_lipschitzOn fun x hx =>
    let ⟨C, u, hu, hf⟩ := (hf x (ht hx)).exists_lipschitzOnWith hc
    ⟨C, u, nhdsWithin_mono _ ht hu, hf⟩

中文:
定理 ContDiffOn.dimH_image_le
  结论: {f : E -> F} {s t : Set E} (hf : ContDiffOn 实数 1 f s)
  证明: dimH_image_le_of_locally_lipschitzOn fun x hx =>
    let ⟨C, u, hu, hf⟩ := (hf x (ht hx)).exists_lipschitzOnWith hc
    ⟨C, u, nhdsWithin_mono _ ht hu, hf⟩

Depends on / 依赖: dimH_image_le_of_locally_lipschitzOn, exists_lipschitzOnWith, nhdsWithin_mono
-/
theorem ContDiffOn.dimH_image_le {f : E -> F} {s t : Set E} (hf : ContDiffOn Real 1 f s)
    (hc : Convex Real s) (ht : t subseteq s) : dimH (f '' t) <= dimH t :=
  dimH_image_le_of_locally_lipschitzOn fun x hx =>
    let ⟨C, u, hu, hf⟩ := (hf x (ht hx)).exists_lipschitzOnWith hc
    ⟨C, u, nhdsWithin_mono _ ht hu, hf⟩

/--
theorem `ContDiff.dimH_range_le` / 定理 `ContDiff.dimH_range_le`

English:
theorem ContDiff.dimH_range_le
  given: {f : E -> F} (h : ContDiff Real 1 f)
  statement: dimH (range f) <= finrank Real E
  proof: calc
    dimH (range f) = dimH (f '' univ) := by rw [image_univ]
    _ <= dimH (univ : Set E) := h.contDiffOn.dimH_image_le convex_univ Subset.rfl
    _ = finrank Real E := Real.dimH_univ_eq_finrank E

中文:
定理 ContDiff.dimH_range_le
  条件: {f : E -> F} (h : ContDiff 实数 1 f)
  结论: dimH (range f) <= finrank 实数 E
  证明: calc
    dimH (range f) = dimH (f '' univ) := by rw [image_univ]
    _ <= dimH (univ : Set E) := h.contDiffOn.dimH_image_le convex_univ Subset.rfl
    _ = finrank Real E := Real.dimH_univ_eq_finrank E

Depends on / 依赖: Real.dimH_univ_eq_finrank, Subset, Subset.rfl, contDiffOn, convex_univ, dimH_image_le, dimH_univ_eq_finrank, finrank, h.contDiffOn.dimH_image_le, image_univ
-/
theorem ContDiff.dimH_range_le {f : E -> F} (h : ContDiff Real 1 f) : dimH (range f) <= finrank Real E :=
  calc
    dimH (range f) = dimH (f '' univ) := by rw [image_univ]
    _ <= dimH (univ : Set E) := h.contDiffOn.dimH_image_le convex_univ Subset.rfl
    _ = finrank Real E := Real.dimH_univ_eq_finrank E

/--
theorem `ContDiffOn.dense_compl_image_of_dimH_lt_finrank` / 定理 `ContDiffOn.dense_compl_image_of_dimH_lt_finrank`

English:
theorem ContDiffOn.dense_compl_image_of_dimH_lt_finrank
  statement: [FiniteDimensional Real F] {f : E -> F}
  proof: dense_compl_of_dimH_lt_finrank (h.dimH_image_le hc ht).trans_lt htF

中文:
定理 ContDiffOn.dense_compl_image_of_dimH_lt_finrank
  结论: [FiniteDimensional 实数 F] {f : E -> F}
  证明: dense_compl_of_dimH_lt_finrank (h.dimH_image_le hc ht).trans_lt htF

Depends on / 依赖: dense_compl_of_dimH_lt_finrank, dimH_image_le, h.dimH_image_le, trans_lt
-/
theorem ContDiffOn.dense_compl_image_of_dimH_lt_finrank [FiniteDimensional Real F] {f : E -> F}
    {s t : Set E} (h : ContDiffOn Real 1 f s) (hc : Convex Real s) (ht : t subseteq s)
    (htF : dimH t < finrank Real F) : Dense (f '' t)ᶜ :=
dense_compl_of_dimH_lt_finrank (h.dimH_image_le hc ht).trans_lt htF

/--
theorem `ContDiff.dense_compl_range_of_finrank_lt_finrank` / 定理 `ContDiff.dense_compl_range_of_finrank_lt_finrank`

English:
theorem ContDiff.dense_compl_range_of_finrank_lt_finrank
  statement: [FiniteDimensional Real F] {f : E -> F}
  proof: dense_compl_of_dimH_lt_finrank h.dimH_range_le.trans_lt Nat.cast_lt.2 hEF

中文:
定理 ContDiff.dense_compl_range_of_finrank_lt_finrank
  结论: [FiniteDimensional 实数 F] {f : E -> F}
  证明: dense_compl_of_dimH_lt_finrank h.dimH_range_le.trans_lt Nat.cast_lt.2 hEF

Depends on / 依赖: Nat.cast_lt, cast_lt, dense_compl_of_dimH_lt_finrank, dimH_range_le, h.dimH_range_le.trans_lt, trans_lt
-/
theorem ContDiff.dense_compl_range_of_finrank_lt_finrank [FiniteDimensional Real F] {f : E -> F}
    (h : ContDiff Real 1 f) (hEF : finrank Real E < finrank Real F) : Dense (range f)ᶜ :=
dense_compl_of_dimH_lt_finrank h.dimH_range_le.trans_lt Nat.cast_lt.2 hEF

/--
theorem `dimH_orthogonalProjectionOnto_le` / 定理 `dimH_orthogonalProjectionOnto_le`

English:
theorem dimH_orthogonalProjectionOnto_le
  statement: {𝕜 E : Type*} [RCLike 𝕜]
  proof: K.lipschitzWith_orthogonalProjectionOnto.dimH_image_le s

@[deprecated (since := "2026-05-05")] alias dimH_orthogonalProjection_le :=
  dimH_orthogonalProjectionOnto_le

中文:
定理 dimH_orthogonalProjectionOnto_le
  结论: {𝕜 E : 类型} [RCLike 𝕜]
  证明: K.lipschitzWith_orthogonalProjectionOnto.dimH_image_le s

@[deprecated (since := "2026-05-05")] alias dimH_orthogonalProjection_le :=
  dimH_orthogonalProjectionOnto_le

Depends on / 依赖: K.lipschitzWith_orthogonalProjectionOnto.dimH_image_le, dimH_image_le, lipschitzWith_orthogonalProjectionOnto
-/
theorem dimH_orthogonalProjectionOnto_le {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] (s : Set E) :
    dimH (K.orthogonalProjectionOnto '' s) <= dimH s :=
  K.lipschitzWith_orthogonalProjectionOnto.dimH_image_le s

@[deprecated (since := "2026-05-05")] alias dimH_orthogonalProjection_le :=
  dimH_orthogonalProjectionOnto_le
