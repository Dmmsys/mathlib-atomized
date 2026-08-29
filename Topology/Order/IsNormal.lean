/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Order.IsNormal
public import Mathlib.Topology.Order.IsLUB

/-!
# A normal function is strictly monotone and continuous

We defined the predicate `Order.IsNormal` in terms of `IsLUB`, which avoids having to import
topology in order theory files. This file shows that the predicate is equivalent to the definition
in the literature, being that of a strictly monotonic function, continuous in the order topology.
-/

public section

open Set

namespace Order
variable {α β : Type*}
  [LinearOrder α] [WellFoundedLT α] [TopologicalSpace α] [OrderTopology α]
  [LinearOrder β] [WellFoundedLT β] [TopologicalSpace β] [OrderTopology β]

attribute [local instance]
  WellFoundedLT.toOrderBot WellFoundedLT.conditionallyCompleteLinearOrderBot in
/--
theorem `IsNormal.continuous` / 定理 `IsNormal.continuous`

English:
theorem IsNormal.continuous
  given: {f : α -> β} (hf : IsNormal f)
  statement: Continuous f
  proof: by
  rw [OrderTopology.continuous_iff]
  refine fun b => ⟨?_, ((isLowerSet_Iio b).preimage hf.strictMono.monotone).isOpen⟩
  rw [← isClosed_compl_iff]; rw [← Set.preimage_compl]; rw [Set.compl_Ioi]
  obtain ha | ⟨a, ha⟩ := ((isLowerSet_Iic b).preimage hf.strictMono.monotone).eq_univ_or_Iio
  · exact ha ▸ isClosed_univ
  · obtain h | h := (f ⁻¹' Iic b).eq_empty_or_nonempty
    · exact h ▸ isClosed_empty
    · have : Nonempty α := ⟨a⟩
      have : Nonempty β := ⟨b⟩
      rw [hf.preimage_Iic h (ha ▸ bddAbove_Iio)]
      exact isClosed_Iic

中文:
定理 是正规.continuous
  条件: {f : α -> β} (hf : 是正规 f)
  结论: 连续 f
  证明: by
  rw [OrderTopology.continuous_iff]
  refine fun b => ⟨?_, ((isLowerSet_Iio b).preimage hf.strictMono.monotone).isOpen⟩
  rw [← isClosed_compl_iff]; rw [← Set.preimage_compl]; rw [Set.compl_Ioi]
  obtain ha | ⟨a, ha⟩ := ((isLowerSet_Iic b).preimage hf.strictMono.monotone).eq_univ_or_Iio
  · exact ha ▸ isClosed_univ
  · obtain h | h := (f ⁻¹' Iic b).eq_empty_or_nonempty
    · exact h ▸ isClosed_empty
    · have : Nonempty α := ⟨a⟩
      have : Nonempty β := ⟨b⟩
      rw [hf.preimage_Iic h (ha ▸ bddAbove_Iio)]
      exact isClosed_Iic

Depends on / 依赖: Nonempty, OrderTopology, OrderTopology.continuous_iff, Set.compl_Ioi, Set.preimage_compl, bddAbove_Iio, compl_Ioi, continuous_iff, eq_empty_or_nonempty, eq_univ_or_Iio, hf.preimage_Iic, hf.strictMono.monotone, isClosed_, isClosed_compl_iff, isClosed_empty, isClosed_univ, isLowerSet_Iic, isLowerSet_Iio, isOpen, monotone
-/
theorem IsNormal.continuous {f : α -> β} (hf : IsNormal f) : Continuous f := by
  rw [OrderTopology.continuous_iff]
  refine fun b => ⟨?_, ((isLowerSet_Iio b).preimage hf.strictMono.monotone).isOpen⟩
  rw [← isClosed_compl_iff]; rw [← Set.preimage_compl]; rw [Set.compl_Ioi]
  obtain ha | ⟨a, ha⟩ := ((isLowerSet_Iic b).preimage hf.strictMono.monotone).eq_univ_or_Iio
  · exact ha ▸ isClosed_univ
  · obtain h | h := (f ⁻¹' Iic b).eq_empty_or_nonempty
    · exact h ▸ isClosed_empty
    · have : Nonempty α := ⟨a⟩
      have : Nonempty β := ⟨b⟩
      rw [hf.preimage_Iic h (ha ▸ bddAbove_Iio)]
      exact isClosed_Iic

/--
theorem `isNormal_iff_strictMono_and_continuous` / 定理 `isNormal_iff_strictMono_and_continuous`

English:
theorem isNormal_iff_strictMono_and_continuous
  given: {f : α -> β}
  proof: ⟨hf.strictMono, hf.continuous⟩
  mpr := by
    rintro ⟨hs, hc⟩
    refine ⟨hs, fun {a} ha => (isLUB_of_mem_closure ?_ ?_).2⟩
    · rintro _ ⟨b, hb, rfl⟩
      exact (hs hb).le
    · apply image_closure_subset_closure_image hc (mem_image_of_mem ..)
      exact ha.isLUB_Iio.mem_closure (Iio_nonempty.2 ha.1)

中文:
定理 isNormal_iff_strictMono_and_continuous
  条件: {f : α -> β}
  证明: ⟨hf.strictMono, hf.continuous⟩
  mpr := by
    rintro ⟨hs, hc⟩
    refine ⟨hs, fun {a} ha => (isLUB_of_mem_closure ?_ ?_).2⟩
    · rintro _ ⟨b, hb, rfl⟩
      exact (hs hb).le
    · apply image_closure_subset_closure_image hc (mem_image_of_mem ..)
      exact ha.isLUB_Iio.mem_closure (Iio_nonempty.2 ha.1)

Depends on / 依赖: continuous, hf.continuous, hf.strictMono, strictMono
-/
theorem isNormal_iff_strictMono_and_continuous {f : α -> β} :
    IsNormal f ↔ StrictMono f ∧ Continuous f where
  mp hf := ⟨hf.strictMono, hf.continuous⟩
  mpr := by
    rintro ⟨hs, hc⟩
    refine ⟨hs, fun {a} ha => (isLUB_of_mem_closure ?_ ?_).2⟩
    · rintro _ ⟨b, hb, rfl⟩
      exact (hs hb).le
    · apply image_closure_subset_closure_image hc (mem_image_of_mem ..)
      exact ha.isLUB_Iio.mem_closure (Iio_nonempty.2 ha.1)

end Order
