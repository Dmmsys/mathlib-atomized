/-
Copyright (c) 2024 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Etienne Marion
-/
module

public import Mathlib.Topology.Compactness.CompactlyCoherentSpace
public import Mathlib.Topology.Maps.Proper.Basic

/-!
# A map is proper iff preimage of compact sets are compact

This file proves that if `Y` is a Hausdorff and compactly generated space, a continuous map
`f : X → Y` is proper if and only if preimage of compact sets are compact.
-/

public section

open Set Filter

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable [T2Space Y] [CompactlyCoherentSpace Y]
variable {f : X -> Y}

/--
theorem `isProperMap_iff_isCompact_preimage` / 定理 `isProperMap_iff_isCompact_preimage`

English:
theorem isProperMap_iff_isCompact_preimage
  proof: ⟨hf.continuous, fun _ => hf.isCompact_preimage⟩
  mpr := fun ⟨hf, h⟩ => isProperMap_iff_isClosedMap_and_compact_fibers.2
    ⟨hf, fun s hs => (CompactlyCoherentSpace.isClosed_iff _).mpr fun K hK => by
        convert! (((h hK).inter_left hs).image hf).isClosed.preimage continuous_subtype_val using 1

中文:
定理 isProperMap_iff_isCompact_preimage
  证明: ⟨hf.continuous, fun _ => hf.isCompact_preimage⟩
  mpr := fun ⟨hf, h⟩ => isProperMap_iff_isClosedMap_and_compact_fibers.2
    ⟨hf, fun s hs => (CompactlyCoherentSpace.isClosed_iff _).mpr fun K hK => by
        convert! (((h hK).inter_left hs).image hf).isClosed.preimage continuous_subtype_val using 1

Depends on / 依赖: continuous, hf.continuous, hf.isCompact_preimage, isCompact_preimage
-/
theorem isProperMap_iff_isCompact_preimage :
    IsProperMap f ↔ Continuous f ∧ forall ⦃K⦄, IsCompact K -> IsCompact (f ⁻¹' K) where
  mp hf := ⟨hf.continuous, fun _ => hf.isCompact_preimage⟩
  mpr := fun ⟨hf, h⟩ => isProperMap_iff_isClosedMap_and_compact_fibers.2
    ⟨hf, fun s hs => (CompactlyCoherentSpace.isClosed_iff _).mpr fun K hK => by
        convert! (((h hK).inter_left hs).image hf).isClosed.preimage continuous_subtype_val using 1
        aesop, fun _ => h isCompact_singleton⟩

/--
lemma `isProperMap_iff_tendsto_cocompact` / 引理 `isProperMap_iff_tendsto_cocompact`

English:
lemma isProperMap_iff_tendsto_cocompact
  proof: by
  simp_rw [isProperMap_iff_isCompact_preimage,
    hasBasis_cocompact.tendsto_right_iff, ← mem_preimage, eventually_mem_set, preimage_compl]
  refine and_congr_right fun f_cont =>
    ⟨fun H K hK => (H hK).compl_mem_cocompact, fun H K hK => ?_⟩
  rcases mem_cocompact.mp (H K hK) with ⟨K', hK', hK

中文:
引理 isProperMap_iff_tendsto_cocompact
  证明: by
  simp_rw [isProperMap_iff_isCompact_preimage,
    hasBasis_cocompact.tendsto_right_iff, ← mem_preimage, eventually_mem_set, preimage_compl]
  refine and_congr_right fun f_cont =>
    ⟨fun H K hK => (H hK).compl_mem_cocompact, fun H K hK => ?_⟩
  rcases mem_cocompact.mp (H K hK) with ⟨K', hK', hK

Depends on / 依赖: and_congr_right, compl_le_compl_iff_le, compl_le_compl_iff_le.mp, compl_mem_cocompact, eventually_mem_set, f_cont, hK.isClosed.preimage, hasBasis_cocompact, hasBasis_cocompact.tendsto_right_iff, isClosed, isProperMap_iff_isCompact_preimage, mem_cocompact, mem_cocompact.mp, mem_preimage, of_isClosed_subset, preimage, preimage_compl, simp_rw, tendsto_right_iff
-/
lemma isProperMap_iff_tendsto_cocompact :
    IsProperMap f ↔ Continuous f ∧ Tendsto f (cocompact X) (cocompact Y) := by
  simp_rw [isProperMap_iff_isCompact_preimage,
    hasBasis_cocompact.tendsto_right_iff, ← mem_preimage, eventually_mem_set, preimage_compl]
  refine and_congr_right fun f_cont =>
    ⟨fun H K hK => (H hK).compl_mem_cocompact, fun H K hK => ?_⟩
  rcases mem_cocompact.mp (H K hK) with ⟨K', hK', hK'y⟩
  exact hK'.of_isClosed_subset (hK.isClosed.preimage f_cont)
    (compl_le_compl_iff_le.mp hK'y)
