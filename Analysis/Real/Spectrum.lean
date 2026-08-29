/-
Copyright (c) 2021 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Algebra.Spectrum.Quasispectrum
public import Mathlib.Topology.Instances.NNReal.Lemmas
public import Mathlib.Tactic.ContinuousFunctionalCalculus

/-!
# Some lemmas on the spectrum and quasispectrum of elements and positivity

-/

public section

namespace SpectrumRestricts

open NNReal ENNReal

variable {A : Type*} [Ring A] [Algebra Real A]

/--
lemma `nnreal_iff` / 引理 `nnreal_iff`

English:
lemma nnreal_iff
  given: {a : A}
  proof: by
  refine ⟨fun h x hx => ?_, fun h => ?_⟩
  · obtain ⟨x, -, rfl⟩ := h.algebraMap_image.symm ▸ hx
    exact coe_nonneg x
  · exact .of_subset_range_algebraMap (fun _ => Real.toNNReal_coe) fun x hx => ⟨⟨x, h x hx⟩, rfl⟩

中文:
引理 nnreal_iff
  条件: {a : A}
  证明: by
  refine ⟨fun h x hx => ?_, fun h => ?_⟩
  · obtain ⟨x, -, rfl⟩ := h.algebraMap_image.symm ▸ hx
    exact coe_nonneg x
  · exact .of_subset_range_algebraMap (fun _ => Real.toNNReal_coe) fun x hx => ⟨⟨x, h x hx⟩, rfl⟩

Depends on / 依赖: Real.toNNReal_coe, algebraMap_image, coe_nonneg, h.algebraMap_image.symm, of_subset_range_algebraMap, toNNReal_coe
-/
lemma nnreal_iff {a : A} :
    SpectrumRestricts a ContinuousMap.realToNNReal ↔ forall x in spectrum Real a, 0 <= x := by
  refine ⟨fun h x hx => ?_, fun h => ?_⟩
  · obtain ⟨x, -, rfl⟩ := h.algebraMap_image.symm ▸ hx
    exact coe_nonneg x
  · exact .of_subset_range_algebraMap (fun _ => Real.toNNReal_coe) fun x hx => ⟨⟨x, h x hx⟩, rfl⟩

/--
lemma `nnreal_of_nonneg` / 引理 `nnreal_of_nonneg`

English:
lemma nnreal_of_nonneg
  given: [PartialOrder A] [NonnegSpectrumClass Real A] {a : A} (ha : 0 <= a)
  proof: nnreal_iff.mpr spectrum_nonneg_of_nonneg ha

中文:
引理 nnreal_of_nonneg
  条件: [偏序 A] [NonnegSpectrum类 实数 A] {a : A} (ha : 0 <= a)
  证明: nnreal_iff.mpr spectrum_nonneg_of_nonneg ha

Depends on / 依赖: nnreal_iff, nnreal_iff.mpr, spectrum_nonneg_of_nonneg
-/
lemma nnreal_of_nonneg [PartialOrder A] [NonnegSpectrumClass Real A] {a : A} (ha : 0 <= a) :
    SpectrumRestricts a ContinuousMap.realToNNReal :=
nnreal_iff.mpr spectrum_nonneg_of_nonneg ha

/--
lemma `nnreal_le_iff` / 引理 `nnreal_le_iff`

English:
lemma nnreal_le_iff
  statement: {a : A}
  proof: by
  simp [← ha.algebraMap_image]

中文:
引理 nnreal_le_iff
  结论: {a : A}
  证明: by
  simp [← ha.algebraMap_image]

Depends on / 依赖: algebraMap_image, ha.algebraMap_image
-/
lemma nnreal_le_iff {a : A}
    (ha : SpectrumRestricts a ContinuousMap.realToNNReal) {r : Real>=0} :
    (forall x in spectrum Real>=0 a, r <= x) ↔ forall x in spectrum Real a, r <= x := by
  simp [← ha.algebraMap_image]

/--
lemma `nnreal_lt_iff` / 引理 `nnreal_lt_iff`

English:
lemma nnreal_lt_iff
  statement: {a : A}
  proof: by
  simp [← ha.algebraMap_image]

中文:
引理 nnreal_lt_iff
  结论: {a : A}
  证明: by
  simp [← ha.algebraMap_image]

Depends on / 依赖: algebraMap_image, ha.algebraMap_image
-/
lemma nnreal_lt_iff {a : A}
    (ha : SpectrumRestricts a ContinuousMap.realToNNReal) {r : Real>=0} :
    (forall x in spectrum Real>=0 a, r < x) ↔ forall x in spectrum Real a, r < x := by
  simp [← ha.algebraMap_image]

/--
lemma `le_nnreal_iff` / 引理 `le_nnreal_iff`

English:
lemma le_nnreal_iff
  statement: {a : A}
  proof: by
  simp [← ha.algebraMap_image]

中文:
引理 le_nnreal_iff
  结论: {a : A}
  证明: by
  simp [← ha.algebraMap_image]

Depends on / 依赖: algebraMap_image, ha.algebraMap_image
-/
lemma le_nnreal_iff {a : A}
    (ha : SpectrumRestricts a ContinuousMap.realToNNReal) {r : Real>=0} :
    (forall x in spectrum Real>=0 a, x <= r) ↔ forall x in spectrum Real a, x <= r := by
  simp [← ha.algebraMap_image]

/--
lemma `lt_nnreal_iff` / 引理 `lt_nnreal_iff`

English:
lemma lt_nnreal_iff
  statement: {a : A}
  proof: by
  simp [← ha.algebraMap_image]

中文:
引理 lt_nnreal_iff
  结论: {a : A}
  证明: by
  simp [← ha.algebraMap_image]

Depends on / 依赖: algebraMap_image, ha.algebraMap_image
-/
lemma lt_nnreal_iff {a : A}
    (ha : SpectrumRestricts a ContinuousMap.realToNNReal) {r : Real>=0} :
    (forall x in spectrum Real>=0 a, x < r) ↔ forall x in spectrum Real a, x < r := by
  simp [← ha.algebraMap_image]

end SpectrumRestricts

namespace QuasispectrumRestricts

open NNReal ENNReal
local notation "σₙ" => quasispectrum

variable {A : Type*} [NonUnitalRing A]

/--
lemma `nnreal_iff` / 引理 `nnreal_iff`

English:
lemma nnreal_iff
  given: [Module Real A] [IsScalarTower Real A A] [SMulCommClass Real A A] {a : A}
  proof: by
  rw [quasispectrumRestricts_iff_spectrumRestricts_inr]; rw [Unitization.quasispectrum_eq_spectrum_inr' _ Real]; rw [SpectrumRestricts.nnreal_iff]

中文:
引理 nnreal_iff
  条件: [模 实数 A] [标量塔 实数 A A] [标量交换类 实数 A A] {a : A}
  证明: by
  rw [quasispectrumRestricts_iff_spectrumRestricts_inr]; rw [Unitization.quasispectrum_eq_spectrum_inr' _ Real]; rw [SpectrumRestricts.nnreal_iff]

Depends on / 依赖: SpectrumRestricts, SpectrumRestricts.nnreal_iff, Unitization, Unitization.quasispectrum_eq_spectrum_inr, isRepresentable, nnreal_iff, quasispectrumRestricts_iff_spectrumRestricts_inr, quasispectrum_eq_spectrum_inr, shrinkYonedaRepresentableBy
-/
lemma nnreal_iff [Module Real A] [IsScalarTower Real A A] [SMulCommClass Real A A] {a : A} :
    QuasispectrumRestricts a ContinuousMap.realToNNReal ↔ forall x in σₙ Real a, 0 <= x := by
  rw [quasispectrumRestricts_iff_spectrumRestricts_inr]; rw [Unitization.quasispectrum_eq_spectrum_inr' _ Real]; rw [SpectrumRestricts.nnreal_iff]

/--
lemma `nnreal_of_nonneg` / 引理 `nnreal_of_nonneg`

English:
lemma nnreal_of_nonneg
  statement: [Module Real A] [IsScalarTower Real A A] [SMulCommClass Real A A] [PartialOrder A]
  proof: nnreal_iff.mpr quasispectrum_nonneg_of_nonneg _ ha

中文:
引理 nnreal_of_nonneg
  结论: [模 实数 A] [标量塔 实数 A A] [标量交换类 实数 A A] [偏序 A]
  证明: nnreal_iff.mpr quasispectrum_nonneg_of_nonneg _ ha

Depends on / 依赖: infer_instance, nnreal_iff, nnreal_iff.mpr, quasispectrum_nonneg_of_nonneg
-/
lemma nnreal_of_nonneg [Module Real A] [IsScalarTower Real A A] [SMulCommClass Real A A] [PartialOrder A]
    [NonnegSpectrumClass Real A] {a : A} (ha : 0 <= a) :
    QuasispectrumRestricts a ContinuousMap.realToNNReal :=
nnreal_iff.mpr quasispectrum_nonneg_of_nonneg _ ha

/--
lemma `le_nnreal_iff` / 引理 `le_nnreal_iff`

English:
lemma le_nnreal_iff
  statement: [Module Real A] [IsScalarTower Real A A] [SMulCommClass Real A A] {a : A}
  proof: by
  simp [← ha.algebraMap_image]

中文:
引理 le_nnreal_iff
  结论: [模 实数 A] [标量塔 实数 A A] [标量交换类 实数 A A] {a : A}
  证明: by
  simp [← ha.algebraMap_image]

Depends on / 依赖: algebraMap_image, ha.algebraMap_image
-/
lemma le_nnreal_iff [Module Real A] [IsScalarTower Real A A] [SMulCommClass Real A A] {a : A}
    (ha : QuasispectrumRestricts a ContinuousMap.realToNNReal) {r : Real>=0} :
    (forall x in quasispectrum Real>=0 a, x <= r) ↔ forall x in quasispectrum Real a, x <= r := by
  simp [← ha.algebraMap_image]

/--
lemma `lt_nnreal_iff` / 引理 `lt_nnreal_iff`

English:
lemma lt_nnreal_iff
  statement: [Module Real A] [IsScalarTower Real A A] [SMulCommClass Real A A] {a : A}
  proof: by
  simp [← ha.algebraMap_image]

中文:
引理 lt_nnreal_iff
  结论: [模 实数 A] [标量塔 实数 A A] [标量交换类 实数 A A] {a : A}
  证明: by
  simp [← ha.algebraMap_image]

Depends on / 依赖: algebraMap_image, ha.algebraMap_image
-/
lemma lt_nnreal_iff [Module Real A] [IsScalarTower Real A A] [SMulCommClass Real A A] {a : A}
    (ha : QuasispectrumRestricts a ContinuousMap.realToNNReal) {r : Real>=0} :
    (forall x in quasispectrum Real>=0 a, x < r) ↔ forall x in quasispectrum Real a, x < r := by
  simp [← ha.algebraMap_image]

end QuasispectrumRestricts

variable {A : Type*} [Ring A] [PartialOrder A]

open scoped NNReal

/--
lemma `coe_mem_spectrum_real_of_nonneg` / 引理 `coe_mem_spectrum_real_of_nonneg`

English:
lemma coe_mem_spectrum_real_of_nonneg
  statement: [Algebra Real A] [NonnegSpectrumClass Real A] {a : A} {x : Real>=0}
  proof: by
  simp [← (SpectrumRestricts.nnreal_of_nonneg ha).algebraMap_image, Set.mem_image,
    NNReal.algebraMap_eq_coe]

中文:
引理 coe_mem_spectrum_real_of_nonneg
  结论: [代数 实数 A] [NonnegSpectrum类 实数 A] {a : A} {x : 实数>=0}
  证明: by
  simp [← (SpectrumRestricts.nnreal_of_nonneg ha).algebraMap_image, Set.mem_image,
    NNReal.algebraMap_eq_coe]

Depends on / 依赖: NNReal, NNReal.algebraMap_eq_coe, Set.mem_image, SpectrumRestricts, SpectrumRestricts.nnreal_of_nonneg, algebraMap_eq_coe, algebraMap_image, cfc_tac, mem_image, nnreal_of_nonneg, spectrum
-/
lemma coe_mem_spectrum_real_of_nonneg [Algebra Real A] [NonnegSpectrumClass Real A] {a : A} {x : Real>=0}
    (ha : 0 <= a := by cfc_tac) :
    (x : Real) in spectrum Real a ↔ x in spectrum Real>=0 a := by
  simp [← (SpectrumRestricts.nnreal_of_nonneg ha).algebraMap_image, Set.mem_image,
    NNReal.algebraMap_eq_coe]
