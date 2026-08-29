/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Markus Himmel, Lorenzo Luccioli, Alessio Rondelli, Etienne Marion
-/
module

public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Set.Card
public import Mathlib.Topology.EMetricSpace.Diam
public import Mathlib.Topology.MetricSpace.MetricSeparated
public import Mathlib.Topology.MetricSpace.Cover

/-!
# Covering numbers

We define covering numbers of sets in a pseudo-metric space, which are minimal cardinalities of
`ε`-covers of sets by closed balls.
We also define the packing number, which is the maximal cardinality of an `ε`-separated set.

We prove inequalities between these covering and packing numbers.

## Main definitions

* `externalCoveringNumber`: the external covering number of a set `A` for radius `ε` is the minimal
  cardinality (in `ℕ∞`) of an `ε`-cover.
* `coveringNumber`: the covering number (or internal covering number) of a set `A` for radius `ε` is
  the minimal cardinality (in `ℕ∞`) of an `ε`-cover contained in `A`.
* `packingNumber`: the packing number of a set `A` for radius `ε` is the maximal cardinality of
  an `ε`-separated set in `A`.

We define sets achieving these minimal/maximal cardinalities when they exist:
* `minimalCover`: a finite internal `ε`-cover of a set `A` by closed balls with minimal cardinality.
* `maximalSeparatedSet`: a finite `ε`-separated subset of a set `A` with maximal cardinality.

## Main statements

We have the following inequalities between covering and packing numbers:
* `externalCoveringNumber_le_coveringNumber`: external covering number ≤ covering number.
* `packingNumber_two_mul_le_externalCoveringNumber`: packing number for `2 * ε` ≤ external covering
  number for `ε`.
* `coveringNumber_le_packingNumber`: covering number ≤ packing number.
* `coveringNumber_two_mul_le_externalCoveringNumber`: covering number for `2 * ε` ≤ external
  covering number for `ε`.

The covering number is not monotone for set inclusion (because the cover must be contained
in the set), but we have the following inequality:
* `coveringNumber_subset_le`: if `A ⊆ B`, then `coveringNumber ε A ≤ coveringNumber (ε / 2) B`.

## References

* [R. Vershynin, *High-dimensional probability*][vershynin2018high]

-/

@[expose] public section

open EMetric Set
open scoped ENNReal NNReal

namespace Metric

variable {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
  {A B C : Set X} {ε δ : Real>=0} {x : X}

section Definitions

/-- The external covering number of a set `A` in `X` for radius `ε` is the minimal cardinality
(in `ℕ∞`) of an `ε`-cover by points in `X` (not necessarily in `A`). -/
noncomputable
/--
Definition of `externalCoveringNumber` / `externalCoveringNumber` 的定义

English:
definition externalCoveringNumber
  signature: (ε : Real>=0) (A : Set X)
  body: ⨅ (C : Set X) (_ : IsCover ε A C), C.encard

中文:
定义 externalCoveringNumber
  签名: (ε : 实数>=0) (A : 集合 X)
  定义体: ⨅ (C : Set X) (_ : IsCover ε A C), C.encard

Depends on / 依赖: C.encard, IsCover, encard
-/
def externalCoveringNumber (ε : Real>=0) (A : Set X) : Nat∞ :=
  ⨅ (C : Set X) (_ : IsCover ε A C), C.encard

/-- The covering number (or internal covering number) of a set `A` for radius `ε` is
the minimal cardinality (in `ℕ∞`) of an `ε`-cover contained in `A`. -/
noncomputable
/--
Definition of `coveringNumber` / `coveringNumber` 的定义

English:
definition coveringNumber
  signature: (ε : Real>=0) (A : Set X)
  body: ⨅ (C : Set X) (_ : C subseteq A) (_ : IsCover ε A C), C.encard

中文:
定义 coveringNumber
  签名: (ε : 实数>=0) (A : 集合 X)
  定义体: ⨅ (C : Set X) (_ : C subseteq A) (_ : IsCover ε A C), C.encard

Depends on / 依赖: C.encard, IsCover, encard, subseteq
-/
def coveringNumber (ε : Real>=0) (A : Set X) : Nat∞ :=
  ⨅ (C : Set X) (_ : C subseteq A) (_ : IsCover ε A C), C.encard

/-- The packing number of a set `A` for radius `ε` is the maximal cardinality (in `ℕ∞`)
of an `ε`-separated set in `A`. -/
noncomputable
/--
Definition of `packingNumber` / `packingNumber` 的定义

English:
definition packingNumber
  signature: (ε : Real>=0) (A : Set X)
  body: ⨆ (C : Set X) (_ : C subseteq A) (_ : IsSeparated ε C), C.encard

中文:
定义 packingNumber
  签名: (ε : 实数>=0) (A : 集合 X)
  定义体: ⨆ (C : Set X) (_ : C subseteq A) (_ : IsSeparated ε C), C.encard

Depends on / 依赖: C.encard, IsSeparated, encard, subseteq
-/
def packingNumber (ε : Real>=0) (A : Set X) : Nat∞ :=
  ⨆ (C : Set X) (_ : C subseteq A) (_ : IsSeparated ε C), C.encard

end Definitions

@[simp]
/--
lemma `externalCoveringNumber_empty` / 引理 `externalCoveringNumber_empty`

English:
lemma externalCoveringNumber_empty
  given: (ε : Real>=0)
  statement: externalCoveringNumber ε (∅ : Set X) = 0
  proof: by
  simp [externalCoveringNumber]

@[simp]

中文:
引理 externalCoveringNumber_empty
  条件: (ε : 实数>=0)
  结论: externalCoveringNumber ε (∅ : 集合 X) = 0
  证明: by
  simp [externalCoveringNumber]

@[simp]

Depends on / 依赖: externalCoveringNumber
-/
lemma externalCoveringNumber_empty (ε : Real>=0) : externalCoveringNumber ε (∅ : Set X) = 0 := by
  simp [externalCoveringNumber]

@[simp]
/--
lemma `coveringNumber_empty` / 引理 `coveringNumber_empty`

English:
lemma coveringNumber_empty
  given: (ε : Real>=0)
  statement: coveringNumber ε (∅ : Set X) = 0
  proof: by simp [coveringNumber]

@[simp]

中文:
引理 coveringNumber_empty
  条件: (ε : 实数>=0)
  结论: coveringNumber ε (∅ : 集合 X) = 0
  证明: by simp [coveringNumber]

@[simp]

Depends on / 依赖: coveringNumber
-/
lemma coveringNumber_empty (ε : Real>=0) : coveringNumber ε (∅ : Set X) = 0 := by simp [coveringNumber]

@[simp]
/--
lemma `packingNumber_empty` / 引理 `packingNumber_empty`

English:
lemma packingNumber_empty
  given: (ε : Real>=0)
  statement: packingNumber ε (∅ : Set X) = 0
  proof: by simp [packingNumber]

@[simp]

中文:
引理 packingNumber_empty
  条件: (ε : 实数>=0)
  结论: packingNumber ε (∅ : 集合 X) = 0
  证明: by simp [packingNumber]

@[simp]

Depends on / 依赖: packingNumber
-/
lemma packingNumber_empty (ε : Real>=0) : packingNumber ε (∅ : Set X) = 0 := by simp [packingNumber]

@[simp]
/--
lemma `externalCoveringNumber_eq_zero` / 引理 `externalCoveringNumber_eq_zero`

English:
lemma externalCoveringNumber_eq_zero
  proof: by simp [externalCoveringNumber]

@[simp]

中文:
引理 externalCoveringNumber_eq_zero
  证明: by simp [externalCoveringNumber]

@[simp]

Depends on / 依赖: externalCoveringNumber
-/
lemma externalCoveringNumber_eq_zero :
    externalCoveringNumber ε A = 0 ↔ A = ∅ := by simp [externalCoveringNumber]

@[simp]
/--
lemma `externalCoveringNumber_pos_iff` / 引理 `externalCoveringNumber_pos_iff`

English:
lemma externalCoveringNumber_pos_iff
  statement: 0 < externalCoveringNumber ε A ↔ A.Nonempty
  proof: by
  rw [← not_iff_not]
  simp [not_nonempty_iff_eq_empty]

@[simp]

中文:
引理 externalCoveringNumber_pos_iff
  结论: 0 < externalCoveringNumber ε A ↔ A.非空
  证明: by
  rw [← not_iff_not]
  simp [not_nonempty_iff_eq_empty]

@[simp]

Depends on / 依赖: not_iff_not, not_nonempty_iff_eq_empty
-/
lemma externalCoveringNumber_pos_iff : 0 < externalCoveringNumber ε A ↔ A.Nonempty := by
  rw [← not_iff_not]
  simp [not_nonempty_iff_eq_empty]

@[simp]
/--
lemma `coveringNumber_eq_zero` / 引理 `coveringNumber_eq_zero`

English:
lemma coveringNumber_eq_zero
  statement: coveringNumber ε A = 0 ↔ A = ∅
  proof: by simp [coveringNumber]

@[simp]

中文:
引理 coveringNumber_eq_zero
  结论: coveringNumber ε A = 0 ↔ A = ∅
  证明: by simp [coveringNumber]

@[simp]

Depends on / 依赖: coveringNumber
-/
lemma coveringNumber_eq_zero : coveringNumber ε A = 0 ↔ A = ∅ := by simp [coveringNumber]

@[simp]
/--
lemma `coveringNumber_pos_iff` / 引理 `coveringNumber_pos_iff`

English:
lemma coveringNumber_pos_iff
  statement: 0 < coveringNumber ε A ↔ A.Nonempty
  proof: by
  rw [← not_iff_not]
  simp [not_nonempty_iff_eq_empty]

@[simp]

中文:
引理 coveringNumber_pos_iff
  结论: 0 < coveringNumber ε A ↔ A.非空
  证明: by
  rw [← not_iff_not]
  simp [not_nonempty_iff_eq_empty]

@[simp]

Depends on / 依赖: not_iff_not, not_nonempty_iff_eq_empty
-/
lemma coveringNumber_pos_iff : 0 < coveringNumber ε A ↔ A.Nonempty := by
  rw [← not_iff_not]
  simp [not_nonempty_iff_eq_empty]

@[simp]
/--
lemma `packingNumber_eq_zero` / 引理 `packingNumber_eq_zero`

English:
lemma packingNumber_eq_zero
  statement: packingNumber ε A = 0 ↔ A = ∅
  proof: by
  simp only [packingNumber, ENat.iSup_eq_zero, encard_eq_zero]
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  by_contra!
  obtain ⟨x, hx⟩ := this
  simpa using h {x} (by simp [hx]) (by simp)

@[simp]

中文:
引理 packingNumber_eq_zero
  结论: packingNumber ε A = 0 ↔ A = ∅
  证明: by
  simp only [packingNumber, ENat.iSup_eq_zero, encard_eq_zero]
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  by_contra!
  obtain ⟨x, hx⟩ := this
  simpa using h {x} (by simp [hx]) (by simp)

@[simp]

Depends on / 依赖: ENat.iSup_eq_zero, encard_eq_zero, iSup_eq_zero, packingNumber
-/
lemma packingNumber_eq_zero : packingNumber ε A = 0 ↔ A = ∅ := by
  simp only [packingNumber, ENat.iSup_eq_zero, encard_eq_zero]
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  by_contra!
  obtain ⟨x, hx⟩ := this
  simpa using h {x} (by simp [hx]) (by simp)

@[simp]
/--
lemma `packingNumber_pos_iff` / 引理 `packingNumber_pos_iff`

English:
lemma packingNumber_pos_iff
  statement: 0 < packingNumber ε A ↔ A.Nonempty
  proof: by
  rw [← not_iff_not]
  simp [not_nonempty_iff_eq_empty]

中文:
引理 packingNumber_pos_iff
  结论: 0 < packingNumber ε A ↔ A.非空
  证明: by
  rw [← not_iff_not]
  simp [not_nonempty_iff_eq_empty]

Depends on / 依赖: not_iff_not, not_nonempty_iff_eq_empty
-/
lemma packingNumber_pos_iff : 0 < packingNumber ε A ↔ A.Nonempty := by
  rw [← not_iff_not]
  simp [not_nonempty_iff_eq_empty]

/--
lemma `externalCoveringNumber_le_coveringNumber` / 引理 `externalCoveringNumber_le_coveringNumber`

English:
lemma externalCoveringNumber_le_coveringNumber
  given: (ε : Real>=0) (A : Set X)
  proof: by
  simp only [externalCoveringNumber, coveringNumber, le_iInf_iff]
  exact fun C _ hC_cover => iInf₂_le C hC_cover

中文:
引理 externalCoveringNumber_le_coveringNumber
  条件: (ε : 实数>=0) (A : 集合 X)
  证明: by
  simp only [externalCoveringNumber, coveringNumber, le_iInf_iff]
  exact fun C _ hC_cover => iInf₂_le C hC_cover

Depends on / 依赖: coveringNumber, externalCoveringNumber, hC_cover, le_iInf_iff
-/
lemma externalCoveringNumber_le_coveringNumber (ε : Real>=0) (A : Set X) :
    externalCoveringNumber ε A <= coveringNumber ε A := by
  simp only [externalCoveringNumber, coveringNumber, le_iInf_iff]
  exact fun C _ hC_cover => iInf₂_le C hC_cover

/--
lemma `IsCover.externalCoveringNumber_le_encard` / 引理 `IsCover.externalCoveringNumber_le_encard`

English:
lemma IsCover.externalCoveringNumber_le_encard
  given: (hC : IsCover ε A C)
  proof: iInf₂_le C hC

中文:
引理 IsCover.externalCoveringNumber_le_encard
  条件: (hC : IsCover ε A C)
  证明: iInf₂_le C hC
-/
lemma IsCover.externalCoveringNumber_le_encard (hC : IsCover ε A C) :
    externalCoveringNumber ε A <= C.encard := iInf₂_le C hC

/--
lemma `IsCover.coveringNumber_le_encard` / 引理 `IsCover.coveringNumber_le_encard`

English:
lemma IsCover.coveringNumber_le_encard
  given: (h_subset : C subseteq A) (hC : IsCover ε A C)
  proof: (iInf₂_le C h_subset).trans (iInf_le _ hC)

中文:
引理 IsCover.coveringNumber_le_encard
  条件: (h_subset : C subseteq A) (hC : IsCover ε A C)
  证明: (iInf₂_le C h_subset).trans (iInf_le _ hC)

Depends on / 依赖: h_subset, iInf_le
-/
lemma IsCover.coveringNumber_le_encard (h_subset : C subseteq A) (hC : IsCover ε A C) :
    coveringNumber ε A <= C.encard := (iInf₂_le C h_subset).trans (iInf_le _ hC)

/--
lemma `IsSeparated.encard_le_packingNumber` / 引理 `IsSeparated.encard_le_packingNumber`

English:
lemma IsSeparated.encard_le_packingNumber
  given: (h_subset : C subseteq A) (hC : IsSeparated ε C)
  proof: le_iSup₂_of_le C h_subset (le_iSup_of_le hC le_rfl)

中文:
引理 是分离.encard_le_packingNumber
  条件: (h_subset : C subseteq A) (hC : 是分离 ε C)
  证明: le_iSup₂_of_le C h_subset (le_iSup_of_le hC le_rfl)

Depends on / 依赖: h_subset, le_iSup_of_le, le_rfl
-/
lemma IsSeparated.encard_le_packingNumber (h_subset : C subseteq A) (hC : IsSeparated ε C) :
    C.encard <= packingNumber ε A := le_iSup₂_of_le C h_subset (le_iSup_of_le hC le_rfl)

/--
lemma `externalCoveringNumber_le_encard_self` / 引理 `externalCoveringNumber_le_encard_self`

English:
lemma externalCoveringNumber_le_encard_self
  given: (A : Set X)
  statement: externalCoveringNumber ε A <= A.encard
  proof: IsCover.externalCoveringNumber_le_encard (by simp)

中文:
引理 externalCoveringNumber_le_encard_self
  条件: (A : 集合 X)
  结论: externalCoveringNumber ε A <= A.encard
  证明: IsCover.externalCoveringNumber_le_encard (by simp)

Depends on / 依赖: IsCover, IsCover.externalCoveringNumber_le_encard, externalCoveringNumber_le_encard
-/
lemma externalCoveringNumber_le_encard_self (A : Set X) : externalCoveringNumber ε A <= A.encard :=
  IsCover.externalCoveringNumber_le_encard (by simp)

/--
lemma `coveringNumber_le_encard_self` / 引理 `coveringNumber_le_encard_self`

English:
lemma coveringNumber_le_encard_self
  given: (A : Set X)
  statement: coveringNumber ε A <= A.encard
  proof: IsCover.coveringNumber_le_encard (by simp) (by simp)

中文:
引理 coveringNumber_le_encard_self
  条件: (A : 集合 X)
  结论: coveringNumber ε A <= A.encard
  证明: IsCover.coveringNumber_le_encard (by simp) (by simp)

Depends on / 依赖: IsCover, IsCover.coveringNumber_le_encard, coveringNumber_le_encard
-/
lemma coveringNumber_le_encard_self (A : Set X) : coveringNumber ε A <= A.encard :=
  IsCover.coveringNumber_le_encard (by simp) (by simp)

/--
lemma `packingNumber_le_encard_self` / 引理 `packingNumber_le_encard_self`

English:
lemma packingNumber_le_encard_self
  given: (A : Set X)
  statement: packingNumber ε A <= A.encard
  proof: by
  simp only [packingNumber, iSup_le_iff]
  exact fun _ hC _ => encard_le_encard hC

中文:
引理 packingNumber_le_encard_self
  条件: (A : 集合 X)
  结论: packingNumber ε A <= A.encard
  证明: by
  simp only [packingNumber, iSup_le_iff]
  exact fun _ hC _ => encard_le_encard hC

Depends on / 依赖: encard_le_encard, iSup_le_iff, packingNumber
-/
lemma packingNumber_le_encard_self (A : Set X) : packingNumber ε A <= A.encard := by
  simp only [packingNumber, iSup_le_iff]
  exact fun _ hC _ => encard_le_encard hC

/--
lemma `externalCoveringNumber_anti` / 引理 `externalCoveringNumber_anti`

English:
lemma externalCoveringNumber_anti
  given: (h : ε <= δ)
  proof: by
  simp_rw [externalCoveringNumber]
  gcongr
  exact iInf_const_mono (fun h_cover => h_cover.mono_radius h)

中文:
引理 externalCoveringNumber_anti
  条件: (h : ε <= δ)
  证明: by
  simp_rw [externalCoveringNumber]
  gcongr
  exact iInf_const_mono (fun h_cover => h_cover.mono_radius h)

Depends on / 依赖: externalCoveringNumber, h_cover, h_cover.mono_radius, iInf_const_mono, mono_radius, simp_rw
-/
lemma externalCoveringNumber_anti (h : ε <= δ) :
    externalCoveringNumber δ A <= externalCoveringNumber ε A := by
  simp_rw [externalCoveringNumber]
  gcongr
  exact iInf_const_mono (fun h_cover => h_cover.mono_radius h)

/--
lemma `coveringNumber_anti` / 引理 `coveringNumber_anti`

English:
lemma coveringNumber_anti
  given: (h : ε <= δ)
  statement: coveringNumber δ A <= coveringNumber ε A
  proof: by
  simp_rw [coveringNumber]
  gcongr
  exact iInf_const_mono (fun h_cover => h_cover.mono_radius h)

中文:
引理 coveringNumber_anti
  条件: (h : ε <= δ)
  结论: coveringNumber δ A <= coveringNumber ε A
  证明: by
  simp_rw [coveringNumber]
  gcongr
  exact iInf_const_mono (fun h_cover => h_cover.mono_radius h)

Depends on / 依赖: coveringNumber, h_cover, h_cover.mono_radius, iInf_const_mono, mono_radius, simp_rw
-/
lemma coveringNumber_anti (h : ε <= δ) : coveringNumber δ A <= coveringNumber ε A := by
  simp_rw [coveringNumber]
  gcongr
  exact iInf_const_mono (fun h_cover => h_cover.mono_radius h)

/--
lemma `externalCoveringNumber_mono_set` / 引理 `externalCoveringNumber_mono_set`

English:
lemma externalCoveringNumber_mono_set
  given: (h : A subseteq B)
  proof: by
  simp only [externalCoveringNumber, le_iInf_iff]
exact fun C hC => iInf_le_of_le C iInf_le_of_le (hC.anti h) le_rfl

@[simp]

中文:
引理 externalCoveringNumber_mono_set
  条件: (h : A subseteq B)
  证明: by
  simp only [externalCoveringNumber, le_iInf_iff]
exact fun C hC => iInf_le_of_le C iInf_le_of_le (hC.anti h) le_rfl

@[simp]

Depends on / 依赖: externalCoveringNumber, hC.anti, iInf_le_of_le, le_iInf_iff, le_rfl
-/
lemma externalCoveringNumber_mono_set (h : A subseteq B) :
    externalCoveringNumber ε A <= externalCoveringNumber ε B := by
  simp only [externalCoveringNumber, le_iInf_iff]
exact fun C hC => iInf_le_of_le C iInf_le_of_le (hC.anti h) le_rfl

@[simp]
/--
lemma `externalCoveringNumber_zero` / 引理 `externalCoveringNumber_zero`

English:
lemma externalCoveringNumber_zero
  given: {E : Type*} [EMetricSpace E] (A : Set E)
  proof: by
  refine le_antisymm (externalCoveringNumber_le_encard_self A) ?_
  refine le_iInf fun C => le_iInf fun hC₁ => ?_
  rw [isCover_zero] at hC₁
  exact encard_le_encard hC₁

@[simp]

中文:
引理 externalCoveringNumber_zero
  条件: {E : 类型} [广义度量空间 E] (A : 集合 E)
  证明: by
  refine le_antisymm (externalCoveringNumber_le_encard_self A) ?_
  refine le_iInf fun C => le_iInf fun hC₁ => ?_
  rw [isCover_zero] at hC₁
  exact encard_le_encard hC₁

@[simp]

Depends on / 依赖: encard_le_encard, externalCoveringNumber_le_encard_self, isCover_zero, le_antisymm, le_iInf
-/
lemma externalCoveringNumber_zero {E : Type*} [EMetricSpace E] (A : Set E) :
    externalCoveringNumber 0 A = A.encard := by
  refine le_antisymm (externalCoveringNumber_le_encard_self A) ?_
  refine le_iInf fun C => le_iInf fun hC₁ => ?_
  rw [isCover_zero] at hC₁
  exact encard_le_encard hC₁

@[simp]
/--
lemma `coveringNumber_zero` / 引理 `coveringNumber_zero`

English:
lemma coveringNumber_zero
  given: {E : Type*} [EMetricSpace E] (A : Set E)
  proof: by
  refine le_antisymm (coveringNumber_le_encard_self A) ?_
  rw [← externalCoveringNumber_zero]
  exact externalCoveringNumber_le_coveringNumber 0 A

@[simp]

中文:
引理 coveringNumber_zero
  条件: {E : 类型} [广义度量空间 E] (A : 集合 E)
  证明: by
  refine le_antisymm (coveringNumber_le_encard_self A) ?_
  rw [← externalCoveringNumber_zero]
  exact externalCoveringNumber_le_coveringNumber 0 A

@[simp]

Depends on / 依赖: coveringNumber_le_encard_self, externalCoveringNumber_le_coveringNumber, externalCoveringNumber_zero, le_antisymm
-/
lemma coveringNumber_zero {E : Type*} [EMetricSpace E] (A : Set E) :
    coveringNumber 0 A = A.encard := by
  refine le_antisymm (coveringNumber_le_encard_self A) ?_
  rw [← externalCoveringNumber_zero]
  exact externalCoveringNumber_le_coveringNumber 0 A

@[simp]
/--
lemma `packingNumber_zero` / 引理 `packingNumber_zero`

English:
lemma packingNumber_zero
  given: {E : Type*} [EMetricSpace E] (A : Set E)
  proof: le_antisymm (packingNumber_le_encard_self A) (le_iSup_of_le A (by simp))

中文:
引理 packingNumber_zero
  条件: {E : 类型} [广义度量空间 E] (A : 集合 E)
  证明: le_antisymm (packingNumber_le_encard_self A) (le_iSup_of_le A (by simp))

Depends on / 依赖: le_antisymm, le_iSup_of_le, packingNumber_le_encard_self
-/
lemma packingNumber_zero {E : Type*} [EMetricSpace E] (A : Set E) :
    packingNumber 0 A = A.encard :=
  le_antisymm (packingNumber_le_encard_self A) (le_iSup_of_le A (by simp))

/--
lemma `coveringNumber_eq_one_of_ediam_le` / 引理 `coveringNumber_eq_one_of_ediam_le`

English:
lemma coveringNumber_eq_one_of_ediam_le
  given: (h_nonempty : A.Nonempty) (hA : ediam A <= ε)
  proof: by
  refine le_antisymm ?_ ?_
  · have ⟨a, ha⟩ := h_nonempty
    calc coveringNumber ε A
      _ <= ({a} : Set X).encard :=
        (IsCover.singleton_of_ediam_le hA ha).coveringNumber_le_encard (by simp [ha])
      _ <= 1 := by simp
  · simpa [Order.one_le_iff_pos]

中文:
引理 coveringNumber_eq_one_of_ediam_le
  条件: (h_nonempty : A.非空) (hA : ediam A <= ε)
  证明: by
  refine le_antisymm ?_ ?_
  · have ⟨a, ha⟩ := h_nonempty
    calc coveringNumber ε A
      _ <= ({a} : Set X).encard :=
        (IsCover.singleton_of_ediam_le hA ha).coveringNumber_le_encard (by simp [ha])
      _ <= 1 := by simp
  · simpa [Order.one_le_iff_pos]

Depends on / 依赖: IsCover, IsCover.singleton_of_ediam_le, Order.one_le_iff_pos, coveringNumber, coveringNumber_le_encard, encard, h_nonempty, le_antisymm, one_le_iff_pos, singleton_of_ediam_le
-/
lemma coveringNumber_eq_one_of_ediam_le (h_nonempty : A.Nonempty) (hA : ediam A <= ε) :
    coveringNumber ε A = 1 := by
  refine le_antisymm ?_ ?_
  · have ⟨a, ha⟩ := h_nonempty
    calc coveringNumber ε A
      _ <= ({a} : Set X).encard :=
        (IsCover.singleton_of_ediam_le hA ha).coveringNumber_le_encard (by simp [ha])
      _ <= 1 := by simp
  · simpa [Order.one_le_iff_pos]

/--
lemma `externalCoveringNumber_eq_one_of_ediam_le` / 引理 `externalCoveringNumber_eq_one_of_ediam_le`

English:
lemma externalCoveringNumber_eq_one_of_ediam_le
  statement: (h_nonempty : A.Nonempty)
  proof: by
  refine le_antisymm ?_ ?_
  · exact (externalCoveringNumber_le_coveringNumber ε A).trans_eq
      (coveringNumber_eq_one_of_ediam_le h_nonempty hA)
  · simpa [Order.one_le_iff_pos]

中文:
引理 externalCoveringNumber_eq_one_of_ediam_le
  结论: (h_nonempty : A.非空)
  证明: by
  refine le_antisymm ?_ ?_
  · exact (externalCoveringNumber_le_coveringNumber ε A).trans_eq
      (coveringNumber_eq_one_of_ediam_le h_nonempty hA)
  · simpa [Order.one_le_iff_pos]

Depends on / 依赖: Order.one_le_iff_pos, coveringNumber_eq_one_of_ediam_le, externalCoveringNumber_le_coveringNumber, h_nonempty, le_antisymm, one_le_iff_pos, trans_eq
-/
lemma externalCoveringNumber_eq_one_of_ediam_le (h_nonempty : A.Nonempty)
    (hA : ediam A <= ε) :
    externalCoveringNumber ε A = 1 := by
  refine le_antisymm ?_ ?_
  · exact (externalCoveringNumber_le_coveringNumber ε A).trans_eq
      (coveringNumber_eq_one_of_ediam_le h_nonempty hA)
  · simpa [Order.one_le_iff_pos]

/--
lemma `externalCoveringNumber_le_one_of_ediam_le` / 引理 `externalCoveringNumber_le_one_of_ediam_le`

English:
lemma externalCoveringNumber_le_one_of_ediam_le
  given: (hA : ediam A <= ε)
  proof: by
  rcases eq_empty_or_nonempty A with h_eq_empty | h_nonempty
  · rw [← externalCoveringNumber_eq_zero (ε := ε)] at h_eq_empty
    simp [h_eq_empty]
  · exact (externalCoveringNumber_eq_one_of_ediam_le h_nonempty hA).le

中文:
引理 externalCoveringNumber_le_one_of_ediam_le
  条件: (hA : ediam A <= ε)
  证明: by
  rcases eq_empty_or_nonempty A with h_eq_empty | h_nonempty
  · rw [← externalCoveringNumber_eq_zero (ε := ε)] at h_eq_empty
    simp [h_eq_empty]
  · exact (externalCoveringNumber_eq_one_of_ediam_le h_nonempty hA).le

Depends on / 依赖: eq_empty_or_nonempty, externalCoveringNumber_eq_one_of_ediam_le, externalCoveringNumber_eq_zero, h_eq_empty, h_nonempty
-/
lemma externalCoveringNumber_le_one_of_ediam_le (hA : ediam A <= ε) :
    externalCoveringNumber ε A <= 1 := by
  rcases eq_empty_or_nonempty A with h_eq_empty | h_nonempty
  · rw [← externalCoveringNumber_eq_zero (ε := ε)] at h_eq_empty
    simp [h_eq_empty]
  · exact (externalCoveringNumber_eq_one_of_ediam_le h_nonempty hA).le

/--
lemma `coveringNumber_le_one_of_ediam_le` / 引理 `coveringNumber_le_one_of_ediam_le`

English:
lemma coveringNumber_le_one_of_ediam_le
  given: (hA : ediam A <= ε)
  statement: coveringNumber ε A <= 1
  proof: by
  rcases eq_empty_or_nonempty A with h_eq_empty | h_nonempty
  · rw [← coveringNumber_eq_zero (ε := ε)] at h_eq_empty
    simp [h_eq_empty]
  · exact (coveringNumber_eq_one_of_ediam_le h_nonempty hA).le

@[simp]

中文:
引理 coveringNumber_le_one_of_ediam_le
  条件: (hA : ediam A <= ε)
  结论: coveringNumber ε A <= 1
  证明: by
  rcases eq_empty_or_nonempty A with h_eq_empty | h_nonempty
  · rw [← coveringNumber_eq_zero (ε := ε)] at h_eq_empty
    simp [h_eq_empty]
  · exact (coveringNumber_eq_one_of_ediam_le h_nonempty hA).le

@[simp]

Depends on / 依赖: coveringNumber_eq_one_of_ediam_le, coveringNumber_eq_zero, eq_empty_or_nonempty, h_eq_empty, h_nonempty
-/
lemma coveringNumber_le_one_of_ediam_le (hA : ediam A <= ε) : coveringNumber ε A <= 1 := by
  rcases eq_empty_or_nonempty A with h_eq_empty | h_nonempty
  · rw [← coveringNumber_eq_zero (ε := ε)] at h_eq_empty
    simp [h_eq_empty]
  · exact (coveringNumber_eq_one_of_ediam_le h_nonempty hA).le

@[simp]
/--
lemma `coveringNumber_singleton` / 引理 `coveringNumber_singleton`

English:
lemma coveringNumber_singleton
  given: (ε : Real>=0) (x : X)
  statement: coveringNumber ε {x} = 1
  proof: coveringNumber_eq_one_of_ediam_le (by simp) (by simp)

@[simp]

中文:
引理 coveringNumber_singleton
  条件: (ε : 实数>=0) (x : X)
  结论: coveringNumber ε {x} = 1
  证明: coveringNumber_eq_one_of_ediam_le (by simp) (by simp)

@[simp]

Depends on / 依赖: coveringNumber_eq_one_of_ediam_le
-/
lemma coveringNumber_singleton (ε : Real>=0) (x : X) : coveringNumber ε {x} = 1 :=
  coveringNumber_eq_one_of_ediam_le (by simp) (by simp)

@[simp]
/--
lemma `externalCoveringNumber_singleton` / 引理 `externalCoveringNumber_singleton`

English:
lemma externalCoveringNumber_singleton
  given: (ε : Real>=0) (x : X)
  statement: externalCoveringNumber ε {x} = 1
  proof: externalCoveringNumber_eq_one_of_ediam_le (by simp) (by simp)

@[simp]

中文:
引理 externalCoveringNumber_singleton
  条件: (ε : 实数>=0) (x : X)
  结论: externalCoveringNumber ε {x} = 1
  证明: externalCoveringNumber_eq_one_of_ediam_le (by simp) (by simp)

@[simp]

Depends on / 依赖: externalCoveringNumber_eq_one_of_ediam_le
-/
lemma externalCoveringNumber_singleton (ε : Real>=0) (x : X) : externalCoveringNumber ε {x} = 1 :=
  externalCoveringNumber_eq_one_of_ediam_le (by simp) (by simp)

@[simp]
/--
lemma `packingNumber_singleton` / 引理 `packingNumber_singleton`

English:
lemma packingNumber_singleton
  given: (ε : Real>=0) (x : X)
  statement: packingNumber ε {x} = 1
  proof: le_antisymm ((packingNumber_le_encard_self {x}).trans_eq (by simp))
le_iSup_of_le {x} le_iSup_of_le (by simp) le_iSup_of_le (by simp) (by simp)

中文:
引理 packingNumber_singleton
  条件: (ε : 实数>=0) (x : X)
  结论: packingNumber ε {x} = 1
  证明: le_antisymm ((packingNumber_le_encard_self {x}).trans_eq (by simp))
le_iSup_of_le {x} le_iSup_of_le (by simp) le_iSup_of_le (by simp) (by simp)

Depends on / 依赖: le_antisymm, le_iSup_of_le, packingNumber_le_encard_self, trans_eq
-/
lemma packingNumber_singleton (ε : Real>=0) (x : X) : packingNumber ε {x} = 1 :=
le_antisymm ((packingNumber_le_encard_self {x}).trans_eq (by simp))
le_iSup_of_le {x} le_iSup_of_le (by simp) le_iSup_of_le (by simp) (by simp)

section MinimalCover

/--
lemma `exists_set_encard_eq_coveringNumber` / 引理 `exists_set_encard_eq_coveringNumber`

English:
lemma exists_set_encard_eq_coveringNumber
  given: (h : coveringNumber ε A != ⊤)
  proof: by
  simp only [coveringNumber, ne_eq, iInf_eq_top, encard_eq_top_iff, not_forall, not_infinite] at h
  obtain ⟨C', hC'_subset, hC'_cover, hC'_fin⟩ := h
  have : Nonempty { s : Set X // s subseteq A ∧ IsCover ε A s } := ⟨C', hC'_subset, hC'_cover⟩
  let h := ENat.exists_eq_iInf (fun C : {s : Set X /

中文:
引理 存在_set_encard_eq_coveringNumber
  条件: (h : coveringNumber ε A != ⊤)
  证明: by
  simp only [coveringNumber, ne_eq, iInf_eq_top, encard_eq_top_iff, not_forall, not_infinite] at h
  obtain ⟨C', hC'_subset, hC'_cover, hC'_fin⟩ := h
  have : Nonempty { s : Set X // s subseteq A ∧ IsCover ε A s } := ⟨C', hC'_subset, hC'_cover⟩
  let h := ENat.exists_eq_iInf (fun C : {s : Set X /

Depends on / 依赖: ENat.exists_eq_iInf, IsCover, Nonempty, Set.encard_lt_top_iff.mp, Subtype, Subtype.exists, _cover, _fin, _subset, coveringNumber, encard, encard_eq_top_iff, encard_lt_top_iff, exists_eq_iInf, iInf_eq_top, iInf_lt_top, ne_eq, not_forall, not_infinite, subseteq
-/
lemma exists_set_encard_eq_coveringNumber (h : coveringNumber ε A != ⊤) :
    exists C, C subseteq A ∧ C.Finite ∧ IsCover ε A C ∧ C.encard = coveringNumber ε A := by
  simp only [coveringNumber, ne_eq, iInf_eq_top, encard_eq_top_iff, not_forall, not_infinite] at h
  obtain ⟨C', hC'_subset, hC'_cover, hC'_fin⟩ := h
  have : Nonempty { s : Set X // s subseteq A ∧ IsCover ε A s } := ⟨C', hC'_subset, hC'_cover⟩
  let h := ENat.exists_eq_iInf (fun C : {s : Set X // s subseteq A ∧ IsCover ε A s} => (C : Set X).encard)
  obtain ⟨C, hC⟩ := h
  refine ⟨C, C.2.1, ?_, C.2.2, ?_⟩
  · refine Set.encard_lt_top_iff.mp ?_
    simp only [hC, iInf_lt_top, encard_lt_top_iff, Subtype.exists, exists_prop]
    exact ⟨C', ⟨hC'_subset, hC'_cover⟩, hC'_fin⟩
  · rw [hC]
    simp_rw [iInf_subtype, iInf_and]
    rfl

/-- A finite internal `ε`-cover of a set `A` by closed balls with minimal cardinality.
It is defined as the empty set if no such finite cover exists. -/
noncomputable
/--
Definition of `minimalCover` / `minimalCover` 的定义

English:
definition minimalCover
  signature: (ε : Real>=0) (A : Set X)
  body: if h : coveringNumber ε A != ⊤ then (exists_set_encard_eq_coveringNumber h).choose else ∅

中文:
定义 minimalCover
  签名: (ε : 实数>=0) (A : 集合 X)
  定义体: if h : coveringNumber ε A != ⊤ then (exists_set_encard_eq_coveringNumber h).choose else ∅

Depends on / 依赖: coveringNumber, exists_set_encard_eq_coveringNumber
-/
def minimalCover (ε : Real>=0) (A : Set X) : Set X :=
  if h : coveringNumber ε A != ⊤ then (exists_set_encard_eq_coveringNumber h).choose else ∅

/--
lemma `minimalCover_subset` / 引理 `minimalCover_subset`

English:
lemma minimalCover_subset
  statement: minimalCover ε A subseteq A
  proof: by grind [minimalCover]

中文:
引理 minimalCover_subset
  结论: minimalCover ε A subseteq A
  证明: by grind [minimalCover]

Depends on / 依赖: minimalCover
-/
lemma minimalCover_subset : minimalCover ε A subseteq A := by grind [minimalCover]

/--
lemma `finite_minimalCover` / 引理 `finite_minimalCover`

English:
lemma finite_minimalCover
  proof: by grind [minimalCover]

中文:
引理 finite_minimalCover
  证明: by grind [minimalCover]

Depends on / 依赖: minimalCover
-/
lemma finite_minimalCover :
    (minimalCover ε A).Finite := by grind [minimalCover]

/--
lemma `isCover_minimalCover` / 引理 `isCover_minimalCover`

English:
lemma isCover_minimalCover
  given: (h : coveringNumber ε A != ⊤)
  proof: by grind [minimalCover]

中文:
引理 isCover_minimalCover
  条件: (h : coveringNumber ε A != ⊤)
  证明: by grind [minimalCover]

Depends on / 依赖: minimalCover
-/
lemma isCover_minimalCover (h : coveringNumber ε A != ⊤) :
    IsCover ε A (minimalCover ε A) := by grind [minimalCover]

/--
lemma `encard_minimalCover` / 引理 `encard_minimalCover`

English:
lemma encard_minimalCover
  given: (h : coveringNumber ε A != ⊤)
  proof: by grind [minimalCover]

中文:
引理 encard_minimalCover
  条件: (h : coveringNumber ε A != ⊤)
  证明: by grind [minimalCover]

Depends on / 依赖: minimalCover
-/
lemma encard_minimalCover (h : coveringNumber ε A != ⊤) :
    (minimalCover ε A).encard = coveringNumber ε A := by grind [minimalCover]

end MinimalCover

section MaximalSeparatedSet

/--
lemma `exists_set_encard_eq_packingNumber` / 引理 `exists_set_encard_eq_packingNumber`

English:
lemma exists_set_encard_eq_packingNumber
  given: (h : packingNumber ε A != ⊤)
  proof: by
  rcases Set.eq_empty_or_nonempty A with hA | hA
  · simp [hA, packingNumber]
  have : Nonempty { s : Set X // s subseteq A ∧ IsSeparated ε s } := by
    obtain ⟨a, ha⟩ := hA
    exact ⟨⟨{a}, by simp [ha], by simp⟩⟩
  let h_exists := ENat.exists_eq_iSup_of_lt_top
    (f := fun C : { s : Set X // 

中文:
引理 存在_set_encard_eq_packingNumber
  条件: (h : packingNumber ε A != ⊤)
  证明: by
  rcases Set.eq_empty_or_nonempty A with hA | hA
  · simp [hA, packingNumber]
  have : Nonempty { s : Set X // s subseteq A ∧ IsSeparated ε s } := by
    obtain ⟨a, ha⟩ := hA
    exact ⟨⟨{a}, by simp [ha], by simp⟩⟩
  let h_exists := ENat.exists_eq_iSup_of_lt_top
    (f := fun C : { s : Set X // 

Depends on / 依赖: ENat.exists_eq_iSup_of_lt_top, IsSeparated, Nonempty, Set.eq_empty_or_nonempty, encard, eq_empty_or_nonempty, exists_eq_iSup_of_lt_top, h.lt_top, h_exists, iSup_and, iSup_subtype, lt_top, packingNumber, simp_rw, specialize, subseteq
-/
lemma exists_set_encard_eq_packingNumber (h : packingNumber ε A != ⊤) :
    exists C, C subseteq A ∧ C.Finite ∧ IsSeparated ε C ∧ C.encard = packingNumber ε A := by
  rcases Set.eq_empty_or_nonempty A with hA | hA
  · simp [hA, packingNumber]
  have : Nonempty { s : Set X // s subseteq A ∧ IsSeparated ε s } := by
    obtain ⟨a, ha⟩ := hA
    exact ⟨⟨{a}, by simp [ha], by simp⟩⟩
  let h_exists := ENat.exists_eq_iSup_of_lt_top
    (f := fun C : { s : Set X // s subseteq A ∧ IsSeparated ε s } => (C : Set X).encard)
  simp_rw [packingNumber] at h ⊢
  simp_rw [iSup_subtype, iSup_and] at h_exists
  specialize h_exists h.lt_top
  obtain ⟨C, hC⟩ := h_exists
  refine ⟨C, C.2.1, ?_, C.2.2, ?_⟩
  · refine Set.encard_ne_top_iff.mp ?_
    rwa [hC]
  · rw [hC]

/-- A finite `ε`-separated subset of a set `A` with maximal cardinality.
It is defined as the empty set if no such finite subset exists. -/
noncomputable
/--
Definition of `maximalSeparatedSet` / `maximalSeparatedSet` 的定义

English:
definition maximalSeparatedSet
  signature: (ε : Real>=0) (A : Set X)
  body: if h : packingNumber ε A != ⊤ then (exists_set_encard_eq_packingNumber h).choose else ∅

中文:
定义 maximalSeparatedSet
  签名: (ε : 实数>=0) (A : 集合 X)
  定义体: if h : packingNumber ε A != ⊤ then (exists_set_encard_eq_packingNumber h).choose else ∅

Depends on / 依赖: exists_set_encard_eq_packingNumber, packingNumber
-/
def maximalSeparatedSet (ε : Real>=0) (A : Set X) : Set X :=
  if h : packingNumber ε A != ⊤ then (exists_set_encard_eq_packingNumber h).choose else ∅

/--
lemma `maximalSeparatedSet_subset` / 引理 `maximalSeparatedSet_subset`

English:
lemma maximalSeparatedSet_subset
  statement: maximalSeparatedSet ε A subseteq A
  proof: by grind [maximalSeparatedSet]

中文:
引理 maximalSeparatedSet_subset
  结论: maximalSeparatedSet ε A subseteq A
  证明: by grind [maximalSeparatedSet]

Depends on / 依赖: maximalSeparatedSet
-/
lemma maximalSeparatedSet_subset : maximalSeparatedSet ε A subseteq A := by grind [maximalSeparatedSet]

/--
lemma `isSeparated_maximalSeparatedSet` / 引理 `isSeparated_maximalSeparatedSet`

English:
lemma isSeparated_maximalSeparatedSet
  proof: by grind [maximalSeparatedSet]

中文:
引理 isSeparated_maximalSeparatedSet
  证明: by grind [maximalSeparatedSet]

Depends on / 依赖: maximalSeparatedSet
-/
lemma isSeparated_maximalSeparatedSet :
    IsSeparated ε (maximalSeparatedSet ε A : Set X) := by grind [maximalSeparatedSet]

/--
lemma `encard_maximalSeparatedSet` / 引理 `encard_maximalSeparatedSet`

English:
lemma encard_maximalSeparatedSet
  given: (h : packingNumber ε A != ⊤)
  proof: by grind [maximalSeparatedSet]

中文:
引理 encard_maximalSeparatedSet
  条件: (h : packingNumber ε A != ⊤)
  证明: by grind [maximalSeparatedSet]

Depends on / 依赖: maximalSeparatedSet
-/
lemma encard_maximalSeparatedSet (h : packingNumber ε A != ⊤) :
    (maximalSeparatedSet ε A).encard = packingNumber ε A := by grind [maximalSeparatedSet]

/--
lemma `encard_le_of_isSeparated` / 引理 `encard_le_of_isSeparated`

English:
lemma encard_le_of_isSeparated
  statement: (h_subset : C subseteq A)
  proof: by
  rw [encard_maximalSeparatedSet h]
exact le_iSup_of_le C le_iSup_of_le h_subset le_iSup_of_le h_sep (by simp)

中文:
引理 encard_le_of_isSeparated
  结论: (h_subset : C subseteq A)
  证明: by
  rw [encard_maximalSeparatedSet h]
exact le_iSup_of_le C le_iSup_of_le h_subset le_iSup_of_le h_sep (by simp)

Depends on / 依赖: encard_maximalSeparatedSet, h_sep, h_subset, le_iSup_of_le
-/
lemma encard_le_of_isSeparated (h_subset : C subseteq A)
    (h_sep : IsSeparated ε C) (h : packingNumber ε A != ⊤) :
    C.encard <= (maximalSeparatedSet ε A).encard := by
  rw [encard_maximalSeparatedSet h]
exact le_iSup_of_le C le_iSup_of_le h_subset le_iSup_of_le h_sep (by simp)

/--
lemma `isCover_maximalSeparatedSet` / 引理 `isCover_maximalSeparatedSet`

English:
lemma isCover_maximalSeparatedSet
  given: (h : packingNumber ε A != ⊤)
  proof: by
  intro x hxA
  by_contra! h_dist
  let C := {x} union maximalSeparatedSet ε A
  have hx_not_mem : x ∉ maximalSeparatedSet ε A := by simpa using h_dist x
  suffices C subseteq A ∧ IsSeparated ε C by
    refine absurd (encard_le_of_isSeparated this.1 this.2 h) ?_
    simp [C, encard_insert_of_notM

中文:
引理 isCover_maximalSeparatedSet
  条件: (h : packingNumber ε A != ⊤)
  证明: by
  intro x hxA
  by_contra! h_dist
  let C := {x} union maximalSeparatedSet ε A
  have hx_not_mem : x ∉ maximalSeparatedSet ε A := by simpa using h_dist x
  suffices C subseteq A ∧ IsSeparated ε C by
    refine absurd (encard_le_of_isSeparated this.1 this.2 h) ?_
    simp [C, encard_insert_of_notM

Depends on / 依赖: ENat.lt_add_one_iff, IsSeparated, Set.insert_subset, absurd, encard_insert_of_notMem, encard_le_of_isSeparated, encard_maximalSeparatedSet, h_dist, hx_not_mem, insert_subset, isSeparated_insert_of_notMem, isSeparated_maxima, lt_add_one_iff, maximalSeparatedSet, maximalSeparatedSet_subset, subseteq
-/
lemma isCover_maximalSeparatedSet (h : packingNumber ε A != ⊤) :
    IsCover ε A (maximalSeparatedSet ε A) := by
  intro x hxA
  by_contra! h_dist
  let C := {x} union maximalSeparatedSet ε A
  have hx_not_mem : x ∉ maximalSeparatedSet ε A := by simpa using h_dist x
  suffices C subseteq A ∧ IsSeparated ε C by
    refine absurd (encard_le_of_isSeparated this.1 this.2 h) ?_
    simp [C, encard_insert_of_notMem hx_not_mem,
      ENat.lt_add_one_iff (encard_maximalSeparatedSet h ▸ h)]
  constructor
  · simp [C, hxA, maximalSeparatedSet_subset, Set.insert_subset]
.mpr · exact isSeparated_insert_of_notMem hx_not_mem
      ⟨isSeparated_maximalSeparatedSet, by simpa using h_dist⟩

end MaximalSeparatedSet

section Comparisons

/--
theorem `packingNumber_two_mul_le_externalCoveringNumber` / 定理 `packingNumber_two_mul_le_externalCoveringNumber`

English:
theorem packingNumber_two_mul_le_externalCoveringNumber
  given: (ε : Real>=0) (A : Set X)
  proof: by
  simp only [packingNumber, ENNReal.coe_mul, ENNReal.coe_ofNat, externalCoveringNumber, le_iInf_iff,
    iSup_le_iff]
  intro C hC_cover D hD_subset hD_separated
  -- For each point in D, choose a point in C which is ε-close to it
  let f : D -> C := fun x =>
    ⟨(hC_cover (hD_subset x.2)).choos

中文:
定理 packingNumber_two_mul_le_externalCoveringNumber
  条件: (ε : 实数>=0) (A : 集合 X)
  证明: by
  simp only [packingNumber, ENNReal.coe_mul, ENNReal.coe_ofNat, externalCoveringNumber, le_iInf_iff,
    iSup_le_iff]
  intro C hC_cover D hD_subset hD_separated
  -- For each point in D, choose a point in C which is ε-close to it
  let f : D -> C := fun x =>
    ⟨(hC_cover (hD_subset x.2)).choos

Depends on / 依赖: ENNReal, ENNReal.coe_mul, ENNReal.coe_ofNat, coe_mul, coe_ofNat, externalCoveringNumber, hC_cover, hD_separated, hD_subset, iSup_le_iff, le_iInf_iff, packingNumber
-/
theorem packingNumber_two_mul_le_externalCoveringNumber (ε : Real>=0) (A : Set X) :
    packingNumber (2 * ε) A <= externalCoveringNumber ε A := by
  simp only [packingNumber, ENNReal.coe_mul, ENNReal.coe_ofNat, externalCoveringNumber, le_iInf_iff,
    iSup_le_iff]
  intro C hC_cover D hD_subset hD_separated
  -- For each point in D, choose a point in C which is ε-close to it
  let f : D -> C := fun x =>
    ⟨(hC_cover (hD_subset x.2)).choose, (hC_cover (hD_subset x.2)).choose_spec.1⟩
  have hf' (x : D) : edist x.1 (f x) <= ε := (hC_cover (hD_subset x.2)).choose_spec.2
  -- `⊢ D.encard ≤ C.encard`
  -- It suffices to prove that `f` is injective
  simp only [← Set.toENat_cardinalMk]
  gcongr
  refine Cardinal.mk_le_of_injective (f := f) fun x y hxy => Subtype.ext ?_
  apply Set.Pairwise.eq hD_separated x.2 y.2
  simp only [not_lt]
  calc
    edist (x : X) y <= edist (x : X) (f x) + edist (f x : X) y := edist_triangle ..
    _ <= 2 * ε := by
      rw [two_mul]
      gcongr
      · exact hf' x
      · simpa [edist_comm, hxy] using hf' y

/--
theorem `coveringNumber_le_packingNumber` / 定理 `coveringNumber_le_packingNumber`

English:
theorem coveringNumber_le_packingNumber
  given: (ε : Real>=0) (A : Set X)
  proof: by
  by_cases! h_top : packingNumber ε A != ⊤
  · rw [← encard_maximalSeparatedSet h_top]
.coveringNumber_le_encard maximalSeparatedSet_subset exact isCover_maximalSeparatedSet h_top
  · simp [h_top]

中文:
定理 coveringNumber_le_packingNumber
  条件: (ε : 实数>=0) (A : 集合 X)
  证明: by
  by_cases! h_top : packingNumber ε A != ⊤
  · rw [← encard_maximalSeparatedSet h_top]
.coveringNumber_le_encard maximalSeparatedSet_subset exact isCover_maximalSeparatedSet h_top
  · simp [h_top]

Depends on / 依赖: coveringNumber_le_encard, encard_maximalSeparatedSet, h_top, isCover_maximalSeparatedSet, maximalSeparatedSet_subset, packingNumber
-/
theorem coveringNumber_le_packingNumber (ε : Real>=0) (A : Set X) :
    coveringNumber ε A <= packingNumber ε A := by
  by_cases! h_top : packingNumber ε A != ⊤
  · rw [← encard_maximalSeparatedSet h_top]
.coveringNumber_le_encard maximalSeparatedSet_subset exact isCover_maximalSeparatedSet h_top
  · simp [h_top]

/--
theorem `coveringNumber_two_mul_le_externalCoveringNumber` / 定理 `coveringNumber_two_mul_le_externalCoveringNumber`

English:
theorem coveringNumber_two_mul_le_externalCoveringNumber
  given: (ε : Real>=0) (A : Set X)
  proof: by
  rcases Set.eq_empty_or_nonempty A with rfl | h_nonempty
  · simp
  refine (coveringNumber_le_packingNumber _ A).trans ?_
  exact packingNumber_two_mul_le_externalCoveringNumber ε A

中文:
定理 coveringNumber_two_mul_le_externalCoveringNumber
  条件: (ε : 实数>=0) (A : 集合 X)
  证明: by
  rcases Set.eq_empty_or_nonempty A with rfl | h_nonempty
  · simp
  refine (coveringNumber_le_packingNumber _ A).trans ?_
  exact packingNumber_two_mul_le_externalCoveringNumber ε A

Depends on / 依赖: Set.eq_empty_or_nonempty, coveringNumber_le_packingNumber, eq_empty_or_nonempty, h_nonempty, packingNumber_two_mul_le_externalCoveringNumber
-/
theorem coveringNumber_two_mul_le_externalCoveringNumber (ε : Real>=0) (A : Set X) :
    coveringNumber (2 * ε) A <= externalCoveringNumber ε A := by
  rcases Set.eq_empty_or_nonempty A with rfl | h_nonempty
  · simp
  refine (coveringNumber_le_packingNumber _ A).trans ?_
  exact packingNumber_two_mul_le_externalCoveringNumber ε A

/--
lemma `coveringNumber_subset_le` / 引理 `coveringNumber_subset_le`

English:
lemma coveringNumber_subset_le
  given: (h : A subseteq B)
  proof: calc
  coveringNumber ε A
  _ <= packingNumber ε A := coveringNumber_le_packingNumber ε A
  _ = packingNumber (2 * (ε / 2)) A := by ring_nf
  _ <= externalCoveringNumber (ε / 2) A :=
    packingNumber_two_mul_le_externalCoveringNumber (ε / 2) A
  _ <= externalCoveringNumber (ε / 2) B := externalCove

中文:
引理 coveringNumber_subset_le
  条件: (h : A subseteq B)
  证明: calc
  coveringNumber ε A
  _ <= packingNumber ε A := coveringNumber_le_packingNumber ε A
  _ = packingNumber (2 * (ε / 2)) A := by ring_nf
  _ <= externalCoveringNumber (ε / 2) A :=
    packingNumber_two_mul_le_externalCoveringNumber (ε / 2) A
  _ <= externalCoveringNumber (ε / 2) B := externalCove
-/
lemma coveringNumber_subset_le (h : A subseteq B) :
    coveringNumber ε A <= coveringNumber (ε / 2) B := calc
  coveringNumber ε A
  _ <= packingNumber ε A := coveringNumber_le_packingNumber ε A
  _ = packingNumber (2 * (ε / 2)) A := by ring_nf
  _ <= externalCoveringNumber (ε / 2) A :=
    packingNumber_two_mul_le_externalCoveringNumber (ε / 2) A
  _ <= externalCoveringNumber (ε / 2) B := externalCoveringNumber_mono_set h
  _ <= coveringNumber (ε / 2) B :=
    externalCoveringNumber_le_coveringNumber (ε / 2) B

end Comparisons

/--
lemma `_root_.Isometry.coveringNumber_image'` / 引理 `_root_.Isometry.coveringNumber_image'`

English:
lemma _root_.Isometry.coveringNumber_image'
  given: {f : X -> Y} (hf : Isometry f) (hf_inj : Set.InjOn f A)
  proof: by
  refine le_antisymm ?_ ?_
  · simp only [coveringNumber, le_iInf_iff]
    intro C hC_subset hC_cover
    refine (iInf_le _ (C.image f)).trans ?_
    simp only [Set.image_subset_iff]
    have : ↑C subseteq f ⁻¹' f '' A := hC_subset.trans (Set.subset_preimage_image f A)
    refine (iInf_le _ this)

中文:
引理 _root_.等距.coveringNumber_image'
  条件: {f : X -> Y} (hf : 等距 f) (hf_inj : 集合.单射限制 f A)
  证明: by
  refine le_antisymm ?_ ?_
  · simp only [coveringNumber, le_iInf_iff]
    intro C hC_subset hC_cover
    refine (iInf_le _ (C.image f)).trans ?_
    simp only [Set.image_subset_iff]
    have : ↑C subseteq f ⁻¹' f '' A := hC_subset.trans (Set.subset_preimage_image f A)
    refine (iInf_le _ this)

Depends on / 依赖: C.image, Set.image_subset_iff, Set.subset_preimage_image, _subset, coveringNumber, encard_image_le, hC_cover, hC_subset, hC_subset.trans, hf.isCover_image_iff, iInf_le, image_subset_iff, isCover_image_iff, le_antisymm, le_iInf_iff, subset_preimage_image, subseteq
-/
lemma _root_.Isometry.coveringNumber_image' {f : X -> Y} (hf : Isometry f) (hf_inj : Set.InjOn f A) :
    coveringNumber ε (f '' A) = coveringNumber ε A := by
  refine le_antisymm ?_ ?_
  · simp only [coveringNumber, le_iInf_iff]
    intro C hC_subset hC_cover
    refine (iInf_le _ (C.image f)).trans ?_
    simp only [Set.image_subset_iff]
    have : ↑C subseteq f ⁻¹' f '' A := hC_subset.trans (Set.subset_preimage_image f A)
    refine (iInf_le _ this).trans ?_
    rw [hf.isCover_image_iff]
    refine (iInf_le _ hC_cover).trans ?_
    exact encard_image_le f C
  · simp only [coveringNumber, le_iInf_iff]
    intro C hC_subset hC_cover
    obtain ⟨C', hC'_subset, rfl⟩ : exists C', C' subseteq A ∧ C = C'.image f := by
      have (x : C) : exists y in A, f y = x := by simpa using hC_subset x.2
      choose g hg_mem hg using this
      refine ⟨Set.range g, ?_, ?_⟩
      · rwa [Set.range_subset_iff]
      · ext
        simp
        grind
refine (iInf_le _ C').trans (iInf_le _ hC'_subset).trans ?_
    simp only [hf.isCover_image_iff] at hC_cover
    refine (iInf_le _ hC_cover).trans ?_
    rw [InjOn.encard_image]
    exact hf_inj.mono hC'_subset

/--
lemma `_root_.Isometry.coveringNumber_image` / 引理 `_root_.Isometry.coveringNumber_image`

English:
lemma _root_.Isometry.coveringNumber_image
  statement: {X : Type*} [EMetricSpace X]
  proof: hf.coveringNumber_image' hf.injective.injOn

中文:
引理 _root_.等距.coveringNumber_image
  结论: {X : 类型} [广义度量空间 X]
  证明: hf.coveringNumber_image' hf.injective.injOn

Depends on / 依赖: coveringNumber_image, hf.coveringNumber_image, hf.injective.injOn, injective
-/
lemma _root_.Isometry.coveringNumber_image {X : Type*} [EMetricSpace X]
    {f : X -> Y} (hf : Isometry f) {A : Set X} :
    coveringNumber ε (f '' A) = coveringNumber ε A :=
  hf.coveringNumber_image' hf.injective.injOn

end Metric
