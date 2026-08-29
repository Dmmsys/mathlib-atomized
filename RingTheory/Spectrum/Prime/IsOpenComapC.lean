/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
The morphism `Spec R[x] --> Spec R` induced by the natural inclusion `R --> R[x]` is an open map.

The main result is the first part of the statement of Lemma 00FB in the Stacks Project.

https://stacks.math.columbia.edu/tag/00FB
-/

@[expose] public section


open Ideal Polynomial PrimeSpectrum Set

namespace AlgebraicGeometry

namespace Polynomial

variable {R : Type*} [CommRing R] {f : R[X]}


/--
Definition of `imageOfDf` / `imageOfDf` 的定义

English:
definition imageOfDf
  signature: (f : R[X])
  body: { p : PrimeSpectrum R | exists i : Nat, coeff f i ∉ p.asIdeal }

中文:
定义 imageOfDf
  签名: (f : R[X])
  定义体: { p : PrimeSpectrum R | exists i : Nat, coeff f i ∉ p.asIdeal }

Depends on / 依赖: PrimeSpectrum, asIdeal, p.asIdeal
-/
def imageOfDf (f : R[X]) : Set (PrimeSpectrum R) :=
  { p : PrimeSpectrum R | exists i : Nat, coeff f i ∉ p.asIdeal }

/--
theorem `isOpen_imageOfDf` / 定理 `isOpen_imageOfDf`

English:
theorem isOpen_imageOfDf
  statement: IsOpen (imageOfDf f)
  proof: by
  rw [imageOfDf]; rw [ofPred_exists fun i (x : PrimeSpectrum R) => coeff f i ∉ x.asIdeal]
  exact isOpen_iUnion fun i => isOpen_basicOpen

中文:
定理 isOpen_imageOfDf
  结论: 是开集 (imageOfDf f)
  证明: by
  rw [imageOfDf]; rw [ofPred_exists fun i (x : PrimeSpectrum R) => coeff f i ∉ x.asIdeal]
  exact isOpen_iUnion fun i => isOpen_basicOpen

Depends on / 依赖: PrimeSpectrum, asIdeal, imageOfDf, isOpen_basicOpen, isOpen_iUnion, ofPred_exists, x.asIdeal
-/
theorem isOpen_imageOfDf : IsOpen (imageOfDf f) := by
  rw [imageOfDf]; rw [ofPred_exists fun i (x : PrimeSpectrum R) => coeff f i ∉ x.asIdeal]
  exact isOpen_iUnion fun i => isOpen_basicOpen

/--
theorem `comap_C_mem_imageOfDf` / 定理 `comap_C_mem_imageOfDf`

English:
theorem comap_C_mem_imageOfDf
  statement: {I : PrimeSpectrum R[X]}
  proof: exists_C_coeff_notMem (mem_compl_zeroLocus_iff_notMem.mp H)

中文:
定理 comap_C_mem_imageOfDf
  结论: {I : 素谱 R[X]}
  证明: exists_C_coeff_notMem (mem_compl_zeroLocus_iff_notMem.mp H)

Depends on / 依赖: exists_C_coeff_notMem, mem_compl_zeroLocus_iff_notMem, mem_compl_zeroLocus_iff_notMem.mp
-/
theorem comap_C_mem_imageOfDf {I : PrimeSpectrum R[X]}
    (H : I in (zeroLocus {f} : Set (PrimeSpectrum R[X]))ᶜ) :
    PrimeSpectrum.comap (Polynomial.C : R ->+* R[X]) I in imageOfDf f :=
  exists_C_coeff_notMem (mem_compl_zeroLocus_iff_notMem.mp H)

/--
theorem `imageOfDf_eq_comap_C_compl_zeroLocus` / 定理 `imageOfDf_eq_comap_C_compl_zeroLocus`

English:
theorem imageOfDf_eq_comap_C_compl_zeroLocus
  proof: by
  ext x
  refine ⟨fun hx => ⟨⟨map C x.asIdeal, isPrime_map_C_of_isPrime⟩, ⟨?_, ?_⟩⟩, ?_⟩
  · rw [mem_compl_iff, mem_zeroLocus, singleton_subset_iff]
    obtain ⟨i, hi⟩ := hx
    exact fun a => hi (mem_map_C_iff.mp a i)
  · ext x
    refine ⟨fun h => ?_, fun h => subset_span (mem_image_of_mem C.1 h)⟩
    rw [← @coeff_C_zero R x _]
    exact mem_map_C_iff.mp h 0
  · rintro ⟨xli, complement, rfl⟩
    exact comap_C_mem_imageOfDf complement

中文:
定理 imageOfDf_eq_comap_C_compl_zeroLocus
  证明: by
  ext x
  refine ⟨fun hx => ⟨⟨map C x.asIdeal, isPrime_map_C_of_isPrime⟩, ⟨?_, ?_⟩⟩, ?_⟩
  · rw [mem_compl_iff, mem_zeroLocus, singleton_subset_iff]
    obtain ⟨i, hi⟩ := hx
    exact fun a => hi (mem_map_C_iff.mp a i)
  · ext x
    refine ⟨fun h => ?_, fun h => subset_span (mem_image_of_mem C.1 h)⟩
    rw [← @coeff_C_zero R x _]
    exact mem_map_C_iff.mp h 0
  · rintro ⟨xli, complement, rfl⟩
    exact comap_C_mem_imageOfDf complement

Depends on / 依赖: asIdeal, coeff_C_zero, comap_C_mem_imageOfDf, complement, isPrime_map_C_of_isPrime, mem_compl_iff, mem_image_of_mem, mem_map_C_iff, mem_map_C_iff.mp, mem_zeroLocus, singleton_subset_iff, subset_span, x.asIdeal
-/
theorem imageOfDf_eq_comap_C_compl_zeroLocus :
    imageOfDf f = PrimeSpectrum.comap (C : R ->+* R[X]) '' (zeroLocus {f})ᶜ := by
  ext x
  refine ⟨fun hx => ⟨⟨map C x.asIdeal, isPrime_map_C_of_isPrime⟩, ⟨?_, ?_⟩⟩, ?_⟩
  · rw [mem_compl_iff, mem_zeroLocus, singleton_subset_iff]
    obtain ⟨i, hi⟩ := hx
    exact fun a => hi (mem_map_C_iff.mp a i)
  · ext x
    refine ⟨fun h => ?_, fun h => subset_span (mem_image_of_mem C.1 h)⟩
    rw [← @coeff_C_zero R x _]
    exact mem_map_C_iff.mp h 0
  · rintro ⟨xli, complement, rfl⟩
    exact comap_C_mem_imageOfDf complement

/-- The morphism `C⁺ : Spec R[x] → Spec R` is open. -/
@[stacks 00FB "First part"]
/--
theorem `isOpenMap_comap_C` / 定理 `isOpenMap_comap_C`

English:
theorem isOpenMap_comap_C
  statement: IsOpenMap (PrimeSpectrum.comap (C : R ->+* R[X]))
  proof: by
  rintro U ⟨s, z⟩
  rw [← compl_compl U]; rw [← z]; rw [← iUnion_of_singleton_coe s]; rw [zeroLocus_iUnion]; rw [compl_iInter]; rw [image_iUnion]
  simp_rw [← imageOfDf_eq_comap_C_compl_zeroLocus]
  exact isOpen_iUnion fun f => isOpen_imageOfDf

中文:
定理 isOpenMap_comap_C
  结论: 是开映射 (素谱.comap (C : R ->+* R[X]))
  证明: by
  rintro U ⟨s, z⟩
  rw [← compl_compl U]; rw [← z]; rw [← iUnion_of_singleton_coe s]; rw [zeroLocus_iUnion]; rw [compl_iInter]; rw [image_iUnion]
  simp_rw [← imageOfDf_eq_comap_C_compl_zeroLocus]
  exact isOpen_iUnion fun f => isOpen_imageOfDf

Depends on / 依赖: compl_compl, compl_iInter, iUnion_of_singleton_coe, imageOfDf_eq_comap_C_compl_zeroLocus, image_iUnion, isOpen_iUnion, isOpen_imageOfDf, simp_rw, zeroLocus_iUnion
-/
theorem isOpenMap_comap_C : IsOpenMap (PrimeSpectrum.comap (C : R ->+* R[X])) := by
  rintro U ⟨s, z⟩
  rw [← compl_compl U]; rw [← z]; rw [← iUnion_of_singleton_coe s]; rw [zeroLocus_iUnion]; rw [compl_iInter]; rw [image_iUnion]
  simp_rw [← imageOfDf_eq_comap_C_compl_zeroLocus]
  exact isOpen_iUnion fun f => isOpen_imageOfDf

end Polynomial

end AlgebraicGeometry
