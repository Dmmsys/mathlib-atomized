/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology

/-!

# Connection between adic properties and topological properties

## Main results
- `IsAdic.isPrecomplete_iff`:
  `IsPrecomplete I R` is equivalent to `CompleteSpace R` in the adic topology.
- `IsAdic.isAdicComplete_iff`:
  `IsAdicComplete I R` is equivalent to `CompleteSpace R` and `T2Space R` in the adic topology.

-/

public section

section TopologicalSpace

variable {R : Type*} [CommRing R] [TopologicalSpace R] {I : Ideal R} (hI : IsAdic I)

include hI in
/--
lemma `IsAdic.isHausdorff_iff` / 引理 `IsAdic.isHausdorff_iff`

English:
lemma IsAdic.isHausdorff_iff
  statement: IsHausdorff I R ↔ T2Space R
  proof: by
  rw [I.ringFilterBasis.t2Space_iff_sInter_subset hI.symm]; rw [isHausdorff_iff]
  simp +instances [SModEq.zero, Ideal.ringFilterBasis, RingSubgroupsBasis.toRingFilterBasis]

中文:
引理 IsAdic.isHausdorff_iff
  结论: 是豪斯多夫 I R ↔ T2空间 R
  证明: by
  rw [I.ringFilterBasis.t2Space_iff_sInter_subset hI.symm]; rw [isHausdorff_iff]
  simp +instances [SModEq.zero, Ideal.ringFilterBasis, RingSubgroupsBasis.toRingFilterBasis]
-/
protected lemma IsAdic.isHausdorff_iff : IsHausdorff I R ↔ T2Space R := by
  rw [I.ringFilterBasis.t2Space_iff_sInter_subset hI.symm]; rw [isHausdorff_iff]
  simp +instances [SModEq.zero, Ideal.ringFilterBasis, RingSubgroupsBasis.toRingFilterBasis]

end TopologicalSpace

section UniformSpace

open Topology Uniformity

variable {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
  {I : Ideal R} (hI : IsAdic I)

include hI in
/--
lemma `IsAdic.isPrecomplete_iff` / 引理 `IsAdic.isPrecomplete_iff`

English:
lemma IsAdic.isPrecomplete_iff
  statement: IsPrecomplete I R ↔ CompleteSpace R
  proof: by
  have := hI.hasBasis_nhds_zero.isCountablyGenerated
  have : (𝓤 R).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  simp only [isPrecomplete_iff, smul_eq_mul, Ideal.mul_top, SModEq.sub_mem]
  constructor
  · intro H
    refine UniformSpace.complete_of_cauchySeq_tendsto 

中文:
引理 IsAdic.isPrecomplete_iff
  结论: 是Precomplete I R ↔ 完备空间 R
  证明: by
  have := hI.hasBasis_nhds_zero.isCountablyGenerated
  have : (𝓤 R).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  simp only [isPrecomplete_iff, smul_eq_mul, Ideal.mul_top, SModEq.sub_mem]
  constructor
  · intro H
    refine UniformSpace.complete_of_cauchySeq_tendsto 
-/
protected lemma IsAdic.isPrecomplete_iff : IsPrecomplete I R ↔ CompleteSpace R := by
  have := hI.hasBasis_nhds_zero.isCountablyGenerated
  have : (𝓤 R).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  simp only [isPrecomplete_iff, smul_eq_mul, Ideal.mul_top, SModEq.sub_mem]
  constructor
  · intro H
    refine UniformSpace.complete_of_cauchySeq_tendsto fun u hu => ?_
    have : forall i, exists N, forall m, N <= m -> forall n, N <= n -> u n - u m in I ^ i := by
      simpa using hI.hasBasis_nhds_zero.uniformity_of_nhds_zero.cauchySeq_iff.mp hu
    choose N hN using this
    obtain ⟨L, hL⟩ := H (fun i => u ((Finset.Iic i).sup N))
      fun _ => hN _ _ (Finset.le_sup (by simpa)) _ (Finset.le_sup (by simp))
    use L
    suffices forall i, exists N, forall n, N <= n -> u n - L in I ^ i by
      simpa [(hI.hasBasis_nhds L).tendsto_right_iff, sub_eq_neg_add]
    refine fun i => ⟨(Finset.Iic i).sup N, fun n hn => ?_⟩
    have := Ideal.add_mem _ (hN i ((Finset.Iic i).sup N) (Finset.le_sup (by simp))
      n (.trans (Finset.le_sup (by simp)) hn)) (hL i)
    rwa [sub_add_sub_cancel] at this
  · intro H f hf
    obtain ⟨L, hL⟩ := CompleteSpace.complete (f := Filter.atTop.map f)
      (hI.hasBasis_nhds_zero.uniformity_of_nhds_zero.cauchySeq_iff.mpr fun i _ =>
        ⟨i, fun m hm n hn => by simpa using Ideal.sub_mem _ (hf hm) (hf hn)⟩)
    refine ⟨L, fun i => ?_⟩
    obtain ⟨N, hN⟩ : exists N, forall n, N <= n -> f n - L in I ^ i := by
      simpa [sub_eq_neg_add] using (hI.hasBasis_nhds L).tendsto_right_iff.mp hL i
    simpa using Ideal.add_mem _ (hN (max i N) le_sup_right) (hf (le_max_left i N))

include hI in
/--
lemma `IsAdic.isAdicComplete_iff` / 引理 `IsAdic.isAdicComplete_iff`

English:
lemma IsAdic.isAdicComplete_iff
  statement: IsAdicComplete I R ↔ CompleteSpace R ∧ T2Space R
  proof: by
  rw [isAdicComplete_iff]; rw [hI.isHausdorff_iff]; rw [hI.isPrecomplete_iff]; rw [and_comm]

中文:
引理 IsAdic.isAdicComplete_iff
  结论: 是AdicComplete I R ↔ 完备空间 R ∧ T2空间 R
  证明: by
  rw [isAdicComplete_iff]; rw [hI.isHausdorff_iff]; rw [hI.isPrecomplete_iff]; rw [and_comm]
-/
protected lemma IsAdic.isAdicComplete_iff : IsAdicComplete I R ↔ CompleteSpace R ∧ T2Space R := by
  rw [isAdicComplete_iff]; rw [hI.isHausdorff_iff]; rw [hI.isPrecomplete_iff]; rw [and_comm]

end UniformSpace

section congrRingEquiv

variable {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (e : R ≃+* S)

/--
theorem `IsPrecomplete.congr_ringEquiv` / 定理 `IsPrecomplete.congr_ringEquiv`

English:
theorem IsPrecomplete.congr_ringEquiv
  statement: IsPrecomplete (I.map e) S ↔ IsPrecomplete I R
  proof: by
  let : WithIdeal R := ⟨I⟩
  let : WithIdeal S := ⟨I.map e⟩
  rw [iff_comm]; rw [IsAdic.isPrecomplete_iff (by rfl)]; rw [IsAdic.isPrecomplete_iff (by rfl)]
  exact completeSpace_congr (e := WithIdeal.uniformEquiv e rfl) (by
    simpa using UniformEquiv.isUniformEmbedding ..)

中文:
定理 是Precomplete.congr_ringEquiv
  结论: 是Precomplete (I.map e) S ↔ 是Precomplete I R
  证明: by
  let : WithIdeal R := ⟨I⟩
  let : WithIdeal S := ⟨I.map e⟩
  rw [iff_comm]; rw [IsAdic.isPrecomplete_iff (by rfl)]; rw [IsAdic.isPrecomplete_iff (by rfl)]
  exact completeSpace_congr (e := WithIdeal.uniformEquiv e rfl) (by
    simpa using UniformEquiv.isUniformEmbedding ..)

Depends on / 依赖: I.map, IsAdic, IsAdic.isPrecomplete_iff, UniformEquiv, UniformEquiv.isUniformEmbedding, WithIdeal, WithIdeal.uniformEquiv, completeSpace_congr, iff_comm, isPrecomplete_iff, isUniformEmbedding, uniformEquiv
-/
theorem IsPrecomplete.congr_ringEquiv : IsPrecomplete (I.map e) S ↔ IsPrecomplete I R := by
  let : WithIdeal R := ⟨I⟩
  let : WithIdeal S := ⟨I.map e⟩
  rw [iff_comm]; rw [IsAdic.isPrecomplete_iff (by rfl)]; rw [IsAdic.isPrecomplete_iff (by rfl)]
  exact completeSpace_congr (e := WithIdeal.uniformEquiv e rfl) (by
    simpa using UniformEquiv.isUniformEmbedding ..)

/--
theorem `IsHausdorff.congr_ringEquiv` / 定理 `IsHausdorff.congr_ringEquiv`

English:
theorem IsHausdorff.congr_ringEquiv
  statement: IsHausdorff (I.map e) S ↔ IsHausdorff I R
  proof: by
  let : WithIdeal R := ⟨I⟩
  let : WithIdeal S := ⟨I.map e⟩
  rw [iff_comm]; rw [IsAdic.isHausdorff_iff rfl]; rw [IsAdic.isHausdorff_iff rfl]
  exact ⟨fun _ => (WithIdeal.uniformEquiv e rfl).toHomeomorph.t2Space, fun _ =>
    (WithIdeal.uniformEquiv e rfl).toHomeomorph.symm.t2Space⟩

中文:
定理 是豪斯多夫.congr_ringEquiv
  结论: 是豪斯多夫 (I.map e) S ↔ 是豪斯多夫 I R
  证明: by
  let : WithIdeal R := ⟨I⟩
  let : WithIdeal S := ⟨I.map e⟩
  rw [iff_comm]; rw [IsAdic.isHausdorff_iff rfl]; rw [IsAdic.isHausdorff_iff rfl]
  exact ⟨fun _ => (WithIdeal.uniformEquiv e rfl).toHomeomorph.t2Space, fun _ =>
    (WithIdeal.uniformEquiv e rfl).toHomeomorph.symm.t2Space⟩

Depends on / 依赖: I.map, IsAdic, IsAdic.isHausdorff_iff, WithIdeal, WithIdeal.uniformEquiv, iff_comm, isHausdorff_iff, t2Space, toHomeomorph, toHomeomorph.symm.t2Space, toHomeomorph.t2Space, uniformEquiv
-/
theorem IsHausdorff.congr_ringEquiv : IsHausdorff (I.map e) S ↔ IsHausdorff I R := by
  let : WithIdeal R := ⟨I⟩
  let : WithIdeal S := ⟨I.map e⟩
  rw [iff_comm]; rw [IsAdic.isHausdorff_iff rfl]; rw [IsAdic.isHausdorff_iff rfl]
  exact ⟨fun _ => (WithIdeal.uniformEquiv e rfl).toHomeomorph.t2Space, fun _ =>
    (WithIdeal.uniformEquiv e rfl).toHomeomorph.symm.t2Space⟩

/--
theorem `IsAdicComplete.congr_ringEquiv` / 定理 `IsAdicComplete.congr_ringEquiv`

English:
theorem IsAdicComplete.congr_ringEquiv
  statement: IsAdicComplete (I.map e) S ↔ IsAdicComplete I R
  proof: by
  simp [isAdicComplete_iff, IsHausdorff.congr_ringEquiv, IsPrecomplete.congr_ringEquiv]

中文:
定理 是AdicComplete.congr_ringEquiv
  结论: 是AdicComplete (I.map e) S ↔ 是AdicComplete I R
  证明: by
  simp [isAdicComplete_iff, IsHausdorff.congr_ringEquiv, IsPrecomplete.congr_ringEquiv]

Depends on / 依赖: IsHausdorff, IsHausdorff.congr_ringEquiv, IsPrecomplete, IsPrecomplete.congr_ringEquiv, congr_ringEquiv, isAdicComplete_iff
-/
theorem IsAdicComplete.congr_ringEquiv : IsAdicComplete (I.map e) S ↔ IsAdicComplete I R := by
  simp [isAdicComplete_iff, IsHausdorff.congr_ringEquiv, IsPrecomplete.congr_ringEquiv]

end congrRingEquiv
