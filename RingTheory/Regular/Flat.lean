/-
Copyright (c) 2025 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu, Nailin Guan
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Regular.RegularSequence

/-!
# `RingTheory.Sequence.IsWeaklyRegular` is stable under flat base change

## Main results
* `RingTheory.Sequence.IsWeaklyRegular.of_flat_of_isBaseChange`: Let `R` be a commutative ring,
  `M` be an `R`-module, `S` be a flat `R`-algebra, `N` be the base change of `M` to `S`.
  If `[r₁, …, rₙ]` is a weakly regular `M`-sequence, then its image in `N` is a weakly regular
  `N`-sequence.
-/

public section

namespace RingTheory.Sequence

open Module

variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]

/--
theorem `IsWeaklyRegular.of_flat_of_isBaseChange` / 定理 `IsWeaklyRegular.of_flat_of_isBaseChange`

English:
theorem IsWeaklyRegular.of_flat_of_isBaseChange
  statement: [Flat R S] {f : M ->ₗ[R] N} (hf : IsBaseChange S f)
  proof: by
  induction rs generalizing M N with
  | nil => simp
  | cons x _ ih =>
    simp only [List.map_cons, isWeaklyRegular_cons_iff] at reg ⊢
    have e := (QuotSMulTop.algebraMapTensorEquivTensorQuotSMulTop x M S).symm ≪≫ₗ
      QuotSMulTop.congr ((algebraMap R S) x) hf.equiv
have hg : IsBaseChange S

中文:
定理 是WeaklyRegular.of_flat_of_isBaseChange
  结论: [平坦 R S] {f : M ->ₗ[R] N} (hf : IsBaseChange S f)
  证明: by
  induction rs generalizing M N with
  | nil => simp
  | cons x _ ih =>
    simp only [List.map_cons, isWeaklyRegular_cons_iff] at reg ⊢
    have e := (QuotSMulTop.algebraMapTensorEquivTensorQuotSMulTop x M S).symm ≪≫ₗ
      QuotSMulTop.congr ((algebraMap R S) x) hf.equiv
have hg : IsBaseChange S

Depends on / 依赖: IsBaseChange, IsBaseChange.of_equiv, List.map_cons, QuotSMulTop, QuotSMulTop.algebraMapTensorEquivTensorQuotSMulTop, QuotSMulTop.congr, TensorProduct, TensorProduct.mk, algebraMap, algebraMapTensorEquivTensorQuotSMulTop, e.toLinearMap.restrictScalars, generalizing, hf.equiv, isWeaklyRegular_cons_iff, map_cons, of_equiv, of_flat_of_isBaseChange, restrictScalars, toLinearMap
-/
theorem IsWeaklyRegular.of_flat_of_isBaseChange [Flat R S] {f : M ->ₗ[R] N} (hf : IsBaseChange S f)
    {rs : List R} (reg : IsWeaklyRegular M rs) : IsWeaklyRegular N (rs.map (algebraMap R S)) := by
  induction rs generalizing M N with
  | nil => simp
  | cons x _ ih =>
    simp only [List.map_cons, isWeaklyRegular_cons_iff] at reg ⊢
    have e := (QuotSMulTop.algebraMapTensorEquivTensorQuotSMulTop x M S).symm ≪≫ₗ
      QuotSMulTop.congr ((algebraMap R S) x) hf.equiv
have hg : IsBaseChange S
        e.toLinearMap.restrictScalars R ∘ₗ TensorProduct.mk R S (QuotSMulTop x M) 1 :=
      IsBaseChange.of_equiv e (fun _ => by simp)
    exact ⟨reg.1.of_flat_of_isBaseChange hf, ih hg reg.2⟩

/--
theorem `IsWeaklyRegular.of_flat` / 定理 `IsWeaklyRegular.of_flat`

English:
theorem IsWeaklyRegular.of_flat
  given: [Flat R S] {rs : List R} (reg : IsWeaklyRegular R rs)
  proof: reg.of_flat_of_isBaseChange (IsBaseChange.linearMap R S)

中文:
定理 是WeaklyRegular.of_flat
  条件: [平坦 R S] {rs : 列表 R} (reg : 是WeaklyRegular R rs)
  证明: reg.of_flat_of_isBaseChange (IsBaseChange.linearMap R S)

Depends on / 依赖: IsBaseChange, IsBaseChange.linearMap, linearMap, of_flat_of_isBaseChange, reg.of_flat_of_isBaseChange
-/
theorem IsWeaklyRegular.of_flat [Flat R S] {rs : List R} (reg : IsWeaklyRegular R rs) :
    IsWeaklyRegular S (rs.map (algebraMap R S)) :=
  reg.of_flat_of_isBaseChange (IsBaseChange.linearMap R S)

variable (S) (T : Submonoid R) [IsLocalization T S]

/--
theorem `IsWeaklyRegular.of_isLocalizedModule` / 定理 `IsWeaklyRegular.of_isLocalizedModule`

English:
theorem IsWeaklyRegular.of_isLocalizedModule
  statement: (f : M ->ₗ[R] N) [IsLocalizedModule T f]
  proof: have : Flat R S := IsLocalization.flat S T
  reg.of_flat_of_isBaseChange (IsLocalizedModule.isBaseChange T S f)

include T in

中文:
定理 是WeaklyRegular.of_isLocalizedModule
  结论: (f : M ->ₗ[R] N) [是Localized模 T f]
  证明: have : Flat R S := IsLocalization.flat S T
  reg.of_flat_of_isBaseChange (IsLocalizedModule.isBaseChange T S f)

include T in

Depends on / 依赖: IsLocalization, IsLocalization.flat, IsLocalizedModule, IsLocalizedModule.isBaseChange, isBaseChange, of_flat_of_isBaseChange, reg.of_flat_of_isBaseChange
-/
theorem IsWeaklyRegular.of_isLocalizedModule (f : M ->ₗ[R] N) [IsLocalizedModule T f]
    {rs : List R} (reg : IsWeaklyRegular M rs) : IsWeaklyRegular N (rs.map (algebraMap R S)) :=
  have : Flat R S := IsLocalization.flat S T
  reg.of_flat_of_isBaseChange (IsLocalizedModule.isBaseChange T S f)

include T in
/--
theorem `IsWeaklyRegular.of_isLocalization` / 定理 `IsWeaklyRegular.of_isLocalization`

English:
theorem IsWeaklyRegular.of_isLocalization
  given: {rs : List R} (reg : IsWeaklyRegular R rs)
  proof: reg.of_isLocalizedModule S T (Algebra.linearMap R S)

中文:
定理 是WeaklyRegular.of_isLocalization
  条件: {rs : 列表 R} (reg : 是WeaklyRegular R rs)
  证明: reg.of_isLocalizedModule S T (Algebra.linearMap R S)

Depends on / 依赖: Algebra, Algebra.linearMap, linearMap, of_isLocalizedModule, reg.of_isLocalizedModule
-/
theorem IsWeaklyRegular.of_isLocalization {rs : List R} (reg : IsWeaklyRegular R rs) :
    IsWeaklyRegular S (rs.map (algebraMap R S)) :=
  reg.of_isLocalizedModule S T (Algebra.linearMap R S)

variable (p : Ideal R) [p.IsPrime] [IsLocalization.AtPrime S p]

/--
theorem `IsWeaklyRegular.isRegular_of_isLocalizedModule_of_mem` / 定理 `IsWeaklyRegular.isRegular_of_isLocalizedModule_of_mem`

English:
theorem IsWeaklyRegular.isRegular_of_isLocalizedModule_of_mem
  proof: by
  have : IsLocalRing S := IsLocalization.AtPrime.isLocalRing S p
refine (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal (fun _ hr => ?_)).mpr
    reg.of_isLocalizedModule S p.primeCompl f
  rcases List.mem_map.mp hr with ⟨r, hr, eq⟩
  simpa only [← eq, IsLocalization.AtPrime.to_

中文:
定理 是WeaklyRegular.isRegular_of_isLocalizedModule_of_mem
  证明: by
  have : IsLocalRing S := IsLocalization.AtPrime.isLocalRing S p
refine (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal (fun _ hr => ?_)).mpr
    reg.of_isLocalizedModule S p.primeCompl f
  rcases List.mem_map.mp hr with ⟨r, hr, eq⟩
  simpa only [← eq, IsLocalization.AtPrime.to_

Depends on / 依赖: AtPrime, IsLocalRing, IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal, IsLocalization, IsLocalization.AtPrime.isLocalRing, IsLocalization.AtPrime.to_map_mem_maximal_iff, List.mem_map.mp, isLocalRing, isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal, mem_map, of_isLocalizedModule, p.primeCompl, primeCompl, reg.of_isLocalizedModule, to_map_mem_maximal_iff
-/
theorem IsWeaklyRegular.isRegular_of_isLocalizedModule_of_mem
    [Nontrivial N] [Module.Finite S N] (f : M ->ₗ[R] N) [IsLocalizedModule.AtPrime p f]
    {rs : List R} (reg : IsWeaklyRegular M rs) (mem : forall r in rs, r in p) :
    IsRegular N (rs.map (algebraMap R S)) := by
  have : IsLocalRing S := IsLocalization.AtPrime.isLocalRing S p
refine (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal (fun _ hr => ?_)).mpr
    reg.of_isLocalizedModule S p.primeCompl f
  rcases List.mem_map.mp hr with ⟨r, hr, eq⟩
  simpa only [← eq, IsLocalization.AtPrime.to_map_mem_maximal_iff S p] using mem r hr

/--
theorem `IsWeaklyRegular.isRegular_of_isLocalization_of_mem` / 定理 `IsWeaklyRegular.isRegular_of_isLocalization_of_mem`

English:
theorem IsWeaklyRegular.isRegular_of_isLocalization_of_mem
  proof: have : Nontrivial S := IsLocalization.AtPrime.nontrivial S p
  reg.isRegular_of_isLocalizedModule_of_mem S p (Algebra.linearMap R S) mem

中文:
定理 是WeaklyRegular.isRegular_of_isLocalization_of_mem
  证明: have : Nontrivial S := IsLocalization.AtPrime.nontrivial S p
  reg.isRegular_of_isLocalizedModule_of_mem S p (Algebra.linearMap R S) mem

Depends on / 依赖: Algebra, Algebra.linearMap, AtPrime, IsLocalization, IsLocalization.AtPrime.nontrivial, Nontrivial, isRegular_of_isLocalizedModule_of_mem, linearMap, nontrivial, reg.isRegular_of_isLocalizedModule_of_mem
-/
theorem IsWeaklyRegular.isRegular_of_isLocalization_of_mem
    {rs : List R} (reg : IsWeaklyRegular R rs) (mem : forall r in rs, r in p) :
    IsRegular S (rs.map (algebraMap R S)) :=
  have : Nontrivial S := IsLocalization.AtPrime.nontrivial S p
  reg.isRegular_of_isLocalizedModule_of_mem S p (Algebra.linearMap R S) mem

variable {S} [FaithfullyFlat R S]

/--
theorem `IsRegular.of_faithfullyFlat_of_isBaseChange` / 定理 `IsRegular.of_faithfullyFlat_of_isBaseChange`

English:
theorem IsRegular.of_faithfullyFlat_of_isBaseChange
  statement: {f : M ->ₗ[R] N} (hf : IsBaseChange S f)
  proof: by
  refine ⟨reg.1.of_flat_of_isBaseChange hf, ?_⟩
  rw [← Ideal.map_ofList]
  exact ((hf.map_smul_top_ne_top_iff_of_faithfullyFlat R M _).mpr reg.2.symm).symm

中文:
定理 是正则.of_faithfullyFlat_of_isBaseChange
  结论: {f : M ->ₗ[R] N} (hf : IsBaseChange S f)
  证明: by
  refine ⟨reg.1.of_flat_of_isBaseChange hf, ?_⟩
  rw [← Ideal.map_ofList]
  exact ((hf.map_smul_top_ne_top_iff_of_faithfullyFlat R M _).mpr reg.2.symm).symm

Depends on / 依赖: Ideal.map_ofList, hf.map_smul_top_ne_top_iff_of_faithfullyFlat, map_ofList, map_smul_top_ne_top_iff_of_faithfullyFlat, of_flat_of_isBaseChange
-/
theorem IsRegular.of_faithfullyFlat_of_isBaseChange {f : M ->ₗ[R] N} (hf : IsBaseChange S f)
    {rs : List R} (reg : IsRegular M rs) : IsRegular N (rs.map (algebraMap R S)) := by
  refine ⟨reg.1.of_flat_of_isBaseChange hf, ?_⟩
  rw [← Ideal.map_ofList]
  exact ((hf.map_smul_top_ne_top_iff_of_faithfullyFlat R M _).mpr reg.2.symm).symm

/--
theorem `IsRegular.of_faithfullyFlat` / 定理 `IsRegular.of_faithfullyFlat`

English:
theorem IsRegular.of_faithfullyFlat
  given: {rs : List R} (reg : IsRegular R rs)
  proof: reg.of_faithfullyFlat_of_isBaseChange (IsBaseChange.linearMap R S)

中文:
定理 是正则.of_faithfullyFlat
  条件: {rs : 列表 R} (reg : 是正则 R rs)
  证明: reg.of_faithfullyFlat_of_isBaseChange (IsBaseChange.linearMap R S)

Depends on / 依赖: IsBaseChange, IsBaseChange.linearMap, linearMap, of_faithfullyFlat_of_isBaseChange, reg.of_faithfullyFlat_of_isBaseChange
-/
theorem IsRegular.of_faithfullyFlat {rs : List R} (reg : IsRegular R rs) :
    IsRegular S (rs.map (algebraMap R S)) :=
  reg.of_faithfullyFlat_of_isBaseChange (IsBaseChange.linearMap R S)

end RingTheory.Sequence
