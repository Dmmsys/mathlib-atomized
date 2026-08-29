/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.CompactOpen

/-!
# Second countable topology on `C(X, Y)`

In this file we prove that `C(X, Y)` with compact-open topology has second countable topology, if

- both `X` and `Y` have second countable topology;
- `X` is a locally compact space;
-/

public section

open scoped Topology
open Set Function Filter TopologicalSpace

namespace ContinuousMap

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/--
theorem `compactOpen_eq_generateFrom` / 定理 `compactOpen_eq_generateFrom`

English:
theorem compactOpen_eq_generateFrom
  statement: {S : Set (Set X)} {T : Set (Set Y)}
  proof: by
  apply le_antisymm
  · apply_rules [generateFrom_anti, image2_subset_iff.mpr]
    intro K hK t ht
    exact mem_image2_of_mem (hS₁ K hK) (isOpen_sUnion fun _ h => hT.isOpen <| ht.2 h)
  · refine le_of_nhds_le_nhds fun f => ?_
    simp only [nhds_compactOpen, le_iInf_iff, le_principal_iff]
    intro K (hK : IsCompact K) U (hU : IsOpen U) hfKU
    simp only [TopologicalSpace.nhds_generateFrom]
    obtain ⟨t, htT, htf, hTU, hKT⟩ : exists t subseteq T, t.Finite ∧ (forall V in t, V subseteq U) ∧ f '' K subseteq ⋃₀ t := by
      rw [hT.open_eq_sUnion' hU]; rw [mapsTo_iff_image_subset]; rw [sUnion_eq_biUnion] at hfKU
      obtain ⟨t, ht, hfin, htK⟩ :=
        (hK.image (map_continuous f)).elim_finite_subcover_image (fun V hV => hT.isOpen hV.1) hfKU
      refine ⟨t, fun _ h => (ht h).1, hfin, fun _ h => (ht h).2, ?_⟩
      rwa [sUnion_eq_biUnion]
    rw [image_subset_iff] at hKT
    obtain ⟨s, hsS, hsf, hKs, hst⟩ : exists s subseteq S, s.Finite ∧ K subseteq ⋃₀ s ∧ MapsTo f (⋃₀ s) (⋃₀ t) := by
      have : forall x in K, exists L in S, L in 𝓝 x ∧ MapsTo f L (⋃₀ t) := by
        intro x hx
        rcases hKT hx with ⟨V, hVt, hxV⟩
        rcases hS₂ f x V (htT hVt) hxV with ⟨L, hLS, hLx, hLV⟩
exact ⟨L, hLS, hLx, hLV.mono_right subset_sUnion_of_mem hVt⟩
      choose! L hLS hLmem hLt using this
      rcases hK.elim_nhds_subcover L hLmem with ⟨s, hsK, hs⟩
refine ⟨L '' s, image_subset_iff.2 fun x hx => hLS x hsK x hx, s.finite_toSet.image _,
        by rwa [sUnion_image], ?_⟩
      rw [mapsTo_sUnion]; rw [forall_mem_image]
exact fun x hx => hLt x hsK x hx
    have hsub : (⋂ L in s, {g : C(X, Y) | MapsTo g L (⋃₀ t)}) subseteq {g | MapsTo g K U} := by
      simp only [← ofPred_forall, ← mapsTo_iUnion, ← sUnion_eq_biUnion]
      exact fun g hg => hg.mono hKs (sUnion_subset hTU)
    refine mem_of_superset ((biInter_mem hsf).2 fun L hL => ?_) hsub
refine mem_iInf_of_mem _ mem_iInf_of_mem ?_ mem_principal_self _
    exact ⟨hst.mono_left (subset_sUnion_of_mem hL), mem_image2_of_mem (hsS hL) ⟨htf, htT⟩⟩

中文:
定理 compactOpen_eq_generateFrom
  结论: {S : 集合 (集合 X)} {T : 集合 (集合 Y)}
  证明: by
  apply le_antisymm
  · apply_rules [generateFrom_anti, image2_subset_iff.mpr]
    intro K hK t ht
    exact mem_image2_of_mem (hS₁ K hK) (isOpen_sUnion fun _ h => hT.isOpen <| ht.2 h)
  · refine le_of_nhds_le_nhds fun f => ?_
    simp only [nhds_compactOpen, le_iInf_iff, le_principal_iff]
    intro K (hK : IsCompact K) U (hU : IsOpen U) hfKU
    simp only [TopologicalSpace.nhds_generateFrom]
    obtain ⟨t, htT, htf, hTU, hKT⟩ : exists t subseteq T, t.Finite ∧ (forall V in t, V subseteq U) ∧ f '' K subseteq ⋃₀ t := by
      rw [hT.open_eq_sUnion' hU]; rw [mapsTo_iff_image_subset]; rw [sUnion_eq_biUnion] at hfKU
      obtain ⟨t, ht, hfin, htK⟩ :=
        (hK.image (map_continuous f)).elim_finite_subcover_image (fun V hV => hT.isOpen hV.1) hfKU
      refine ⟨t, fun _ h => (ht h).1, hfin, fun _ h => (ht h).2, ?_⟩
      rwa [sUnion_eq_biUnion]
    rw [image_subset_iff] at hKT
    obtain ⟨s, hsS, hsf, hKs, hst⟩ : exists s subseteq S, s.Finite ∧ K subseteq ⋃₀ s ∧ MapsTo f (⋃₀ s) (⋃₀ t) := by
      have : forall x in K, exists L in S, L in 𝓝 x ∧ MapsTo f L (⋃₀ t) := by
        intro x hx
        rcases hKT hx with ⟨V, hVt, hxV⟩
        rcases hS₂ f x V (htT hVt) hxV with ⟨L, hLS, hLx, hLV⟩
exact ⟨L, hLS, hLx, hLV.mono_right subset_sUnion_of_mem hVt⟩
      choose! L hLS hLmem hLt using this
      rcases hK.elim_nhds_subcover L hLmem with ⟨s, hsK, hs⟩
refine ⟨L '' s, image_subset_iff.2 fun x hx => hLS x hsK x hx, s.finite_toSet.image _,
        by rwa [sUnion_image], ?_⟩
      rw [mapsTo_sUnion]; rw [forall_mem_image]
exact fun x hx => hLt x hsK x hx
    have hsub : (⋂ L in s, {g : C(X, Y) | MapsTo g L (⋃₀ t)}) subseteq {g | MapsTo g K U} := by
      simp only [← ofPred_forall, ← mapsTo_iUnion, ← sUnion_eq_biUnion]
      exact fun g hg => hg.mono hKs (sUnion_subset hTU)
    refine mem_of_superset ((biInter_mem hsf).2 fun L hL => ?_) hsub
refine mem_iInf_of_mem _ mem_iInf_of_mem ?_ mem_principal_self _
    exact ⟨hst.mono_left (subset_sUnion_of_mem hL), mem_image2_of_mem (hsS hL) ⟨htf, htT⟩⟩

Depends on / 依赖: Finite, IsCompact, IsOpen, TopologicalSpace, TopologicalSpace.nhds_generateFrom, apply_rules, generateFrom_anti, hT.isOpen, image2_subset_iff, image2_subset_iff.mpr, isOpen, isOpen_sUnion, le_antisymm, le_iInf_iff, le_of_nhds_le_nhds, le_principal_iff, mem_image2_of_mem, nhds_compactOpen, nhds_generateFrom, subseteq
-/
theorem compactOpen_eq_generateFrom {S : Set (Set X)} {T : Set (Set Y)}
    (hS₁ : forall K in S, IsCompact K) (hT : IsTopologicalBasis T)
    (hS₂ : forall f : C(X, Y), forall x, forall V in T, f x in V -> exists K in S, K in 𝓝 x ∧ MapsTo f K V) :
    compactOpen = .generateFrom (.image2 (fun K t =>
      {f : C(X, Y) | MapsTo f K (⋃₀ t)}) S {t : Set (Set Y) | t.Finite ∧ t subseteq T}) := by
  apply le_antisymm
  · apply_rules [generateFrom_anti, image2_subset_iff.mpr]
    intro K hK t ht
    exact mem_image2_of_mem (hS₁ K hK) (isOpen_sUnion fun _ h => hT.isOpen <| ht.2 h)
  · refine le_of_nhds_le_nhds fun f => ?_
    simp only [nhds_compactOpen, le_iInf_iff, le_principal_iff]
    intro K (hK : IsCompact K) U (hU : IsOpen U) hfKU
    simp only [TopologicalSpace.nhds_generateFrom]
    obtain ⟨t, htT, htf, hTU, hKT⟩ : exists t subseteq T, t.Finite ∧ (forall V in t, V subseteq U) ∧ f '' K subseteq ⋃₀ t := by
      rw [hT.open_eq_sUnion' hU]; rw [mapsTo_iff_image_subset]; rw [sUnion_eq_biUnion] at hfKU
      obtain ⟨t, ht, hfin, htK⟩ :=
        (hK.image (map_continuous f)).elim_finite_subcover_image (fun V hV => hT.isOpen hV.1) hfKU
      refine ⟨t, fun _ h => (ht h).1, hfin, fun _ h => (ht h).2, ?_⟩
      rwa [sUnion_eq_biUnion]
    rw [image_subset_iff] at hKT
    obtain ⟨s, hsS, hsf, hKs, hst⟩ : exists s subseteq S, s.Finite ∧ K subseteq ⋃₀ s ∧ MapsTo f (⋃₀ s) (⋃₀ t) := by
      have : forall x in K, exists L in S, L in 𝓝 x ∧ MapsTo f L (⋃₀ t) := by
        intro x hx
        rcases hKT hx with ⟨V, hVt, hxV⟩
        rcases hS₂ f x V (htT hVt) hxV with ⟨L, hLS, hLx, hLV⟩
exact ⟨L, hLS, hLx, hLV.mono_right subset_sUnion_of_mem hVt⟩
      choose! L hLS hLmem hLt using this
      rcases hK.elim_nhds_subcover L hLmem with ⟨s, hsK, hs⟩
refine ⟨L '' s, image_subset_iff.2 fun x hx => hLS x hsK x hx, s.finite_toSet.image _,
        by rwa [sUnion_image], ?_⟩
      rw [mapsTo_sUnion]; rw [forall_mem_image]
exact fun x hx => hLt x hsK x hx
    have hsub : (⋂ L in s, {g : C(X, Y) | MapsTo g L (⋃₀ t)}) subseteq {g | MapsTo g K U} := by
      simp only [← ofPred_forall, ← mapsTo_iUnion, ← sUnion_eq_biUnion]
      exact fun g hg => hg.mono hKs (sUnion_subset hTU)
    refine mem_of_superset ((biInter_mem hsf).2 fun L hL => ?_) hsub
refine mem_iInf_of_mem _ mem_iInf_of_mem ?_ mem_principal_self _
    exact ⟨hst.mono_left (subset_sUnion_of_mem hL), mem_image2_of_mem (hsS hL) ⟨htf, htT⟩⟩

/--
theorem `secondCountableTopology` / 定理 `secondCountableTopology`

English:
theorem secondCountableTopology
  statement: [SecondCountableTopology Y]
  proof: by
    rcases hX with ⟨S, hScount, hScomp, hS⟩
    refine ⟨_, ?_, compactOpen_eq_generateFrom (S := S) hScomp (isBasis_countableBasis _) ?_⟩
    · exact .image2 hScount (countable_ofPred_finite_subset (countable_countableBasis Y)) _
    · intro f x V hV hx
      apply hS
      exacts [isOpen_of_mem_countableBasis hV, hx]

中文:
定理 secondCountableTopology
  结论: [第二可数拓扑 Y]
  证明: by
    rcases hX with ⟨S, hScount, hScomp, hS⟩
    refine ⟨_, ?_, compactOpen_eq_generateFrom (S := S) hScomp (isBasis_countableBasis _) ?_⟩
    · exact .image2 hScount (countable_ofPred_finite_subset (countable_countableBasis Y)) _
    · intro f x V hV hx
      apply hS
      exacts [isOpen_of_mem_countableBasis hV, hx]

Depends on / 依赖: compactOpen_eq_generateFrom, countable_countableBasis, countable_ofPred_finite_subset, exacts, hScomp, hScount, image2, isBasis_countableBasis, isOpen_of_mem_countableBasis
-/
theorem secondCountableTopology [SecondCountableTopology Y]
    (hX : exists S : Set (Set X), S.Countable ∧ (forall K in S, IsCompact K) ∧
      forall f : C(X, Y), forall V, IsOpen V -> forall x in f ⁻¹' V, exists K in S, K in 𝓝 x ∧ MapsTo f K V) :
    SecondCountableTopology C(X, Y) where
  is_open_generated_countable := by
    rcases hX with ⟨S, hScount, hScomp, hS⟩
    refine ⟨_, ?_, compactOpen_eq_generateFrom (S := S) hScomp (isBasis_countableBasis _) ?_⟩
    · exact .image2 hScount (countable_ofPred_finite_subset (countable_countableBasis Y)) _
    · intro f x V hV hx
      apply hS
      exacts [isOpen_of_mem_countableBasis hV, hx]

/--
Instance `instSecondCountableTopology` / 实例 `instSecondCountableTopology`

English:
instance instSecondCountableTopology
  signature: [SecondCountableTopology X] [LocallyCompactSpace X]
  body: by
  apply secondCountableTopology
  have (U : countableBasis X) : LocallyCompactSpace U.1 :=
    (isOpen_of_mem_countableBasis U.2).locallyCompactSpace
  set K := fun U : countableBasis X => CompactExhaustion.choice U.1
  use ⋃ U : countableBasis X, Set.range fun n => K U n
  refine ⟨countable_iUnion fun _ => countable_range _, ?_, ?_⟩
  · simp only [mem_iUnion, mem_range]
    rintro K ⟨U, n, rfl⟩
    exact ((K U).isCompact _).image continuous_subtype_val
  · intro f V hVo x hxV
    obtain ⟨U, hU, hxU, hUV⟩ : exists U in countableBasis X, x in U ∧ U subseteq f ⁻¹' V := by
      rw [← (isBasis_countableBasis _).mem_nhds_iff]
      exact (hVo.preimage (map_continuous f)).mem_nhds hxV
    lift x to U using hxU
    lift U to countableBasis X using hU
    rcases (K U).exists_mem_nhds x with ⟨n, hn⟩
    refine ⟨K U n, mem_iUnion.2 ⟨U, mem_range_self _⟩, ?_, ?_⟩
    · rw [← map_nhds_subtype_coe_eq_nhds x.2]
      exacts [image_mem_map hn, (isOpen_of_mem_countableBasis U.2).mem_nhds x.2]
    · rw [mapsTo_image_iff]
      exact fun y _ => hUV y.2

中文:
实例 instSecondCountableTopology
  签名: [第二可数拓扑 X] [局部紧空间 X]
  定义体: by
  apply secondCountableTopology
  have (U : countableBasis X) : LocallyCompactSpace U.1 :=
    (isOpen_of_mem_countableBasis U.2).locallyCompactSpace
  set K := fun U : countableBasis X => CompactExhaustion.choice U.1
  use ⋃ U : countableBasis X, Set.range fun n => K U n
  refine ⟨countable_iUnion fun _ => countable_range _, ?_, ?_⟩
  · simp only [mem_iUnion, mem_range]
    rintro K ⟨U, n, rfl⟩
    exact ((K U).isCompact _).image continuous_subtype_val
  · intro f V hVo x hxV
    obtain ⟨U, hU, hxU, hUV⟩ : exists U in countableBasis X, x in U ∧ U subseteq f ⁻¹' V := by
      rw [← (isBasis_countableBasis _).mem_nhds_iff]
      exact (hVo.preimage (map_continuous f)).mem_nhds hxV
    lift x to U using hxU
    lift U to countableBasis X using hU
    rcases (K U).exists_mem_nhds x with ⟨n, hn⟩
    refine ⟨K U n, mem_iUnion.2 ⟨U, mem_range_self _⟩, ?_, ?_⟩
    · rw [← map_nhds_subtype_coe_eq_nhds x.2]
      exacts [image_mem_map hn, (isOpen_of_mem_countableBasis U.2).mem_nhds x.2]
    · rw [mapsTo_image_iff]
      exact fun y _ => hUV y.2

Depends on / 依赖: CompactExhaustion, CompactExhaustion.choice, LocallyCompactSpace, Set.range, choice, continuous_subtype_val, countableBasis, countable_iUnion, countable_range, isCompact, isOpen_of_mem_countableBasis, locallyCompactSpace, mem_iUnion, mem_range, secondCountableTopology
-/
instance instSecondCountableTopology [SecondCountableTopology X] [LocallyCompactSpace X]
    [SecondCountableTopology Y] : SecondCountableTopology C(X, Y) := by
  apply secondCountableTopology
  have (U : countableBasis X) : LocallyCompactSpace U.1 :=
    (isOpen_of_mem_countableBasis U.2).locallyCompactSpace
  set K := fun U : countableBasis X => CompactExhaustion.choice U.1
  use ⋃ U : countableBasis X, Set.range fun n => K U n
  refine ⟨countable_iUnion fun _ => countable_range _, ?_, ?_⟩
  · simp only [mem_iUnion, mem_range]
    rintro K ⟨U, n, rfl⟩
    exact ((K U).isCompact _).image continuous_subtype_val
  · intro f V hVo x hxV
    obtain ⟨U, hU, hxU, hUV⟩ : exists U in countableBasis X, x in U ∧ U subseteq f ⁻¹' V := by
      rw [← (isBasis_countableBasis _).mem_nhds_iff]
      exact (hVo.preimage (map_continuous f)).mem_nhds hxV
    lift x to U using hxU
    lift U to countableBasis X using hU
    rcases (K U).exists_mem_nhds x with ⟨n, hn⟩
    refine ⟨K U n, mem_iUnion.2 ⟨U, mem_range_self _⟩, ?_, ?_⟩
    · rw [← map_nhds_subtype_coe_eq_nhds x.2]
      exacts [image_mem_map hn, (isOpen_of_mem_countableBasis U.2).mem_nhds x.2]
    · rw [mapsTo_image_iff]
      exact fun y _ => hUV y.2

/--
Instance `instSeparableSpace` / 实例 `instSeparableSpace`

English:
instance instSeparableSpace
  signature: [SecondCountableTopology X] [LocallyCompactSpace X]
  body: inferInstance

中文:
实例 instSeparableSpace
  签名: [第二可数拓扑 X] [局部紧空间 X]
  定义体: inferInstance
-/
instance instSeparableSpace [SecondCountableTopology X] [LocallyCompactSpace X]
    [SecondCountableTopology Y] : SeparableSpace C(X, Y) :=
  inferInstance

end ContinuousMap
