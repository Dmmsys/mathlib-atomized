/-
Copyright (c) 2024 Mitchell Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Lee
-/
module

public import Mathlib.Topology.Algebra.GroupCompletion
public import Mathlib.Topology.Algebra.InfiniteSum.Group

/-!
# Infinite sums in the completion of a topological group
-/

public section

open UniformSpace.Completion

variable {α β : Type*} [AddCommGroup α] [UniformSpace α] [IsUniformAddGroup α]
  {L : SummationFilter β}

/--
theorem `hasSum_iff_hasSum_compl` / 定理 `hasSum_iff_hasSum_compl`

English:
theorem hasSum_iff_hasSum_compl
  given: (f : β -> α) (a : α)
  proof: (isDenseInducing_toCompl α).hasSum_iff f a

中文:
定理 hasSum_iff_hasSum_compl
  条件: (f : β -> α) (a : α)
  证明: (isDenseInducing_toCompl α).hasSum_iff f a

Depends on / 依赖: hasSum_iff, isDenseInducing_toCompl
-/
theorem hasSum_iff_hasSum_compl (f : β -> α) (a : α) :
    HasSum (toCompl ∘ f) a L ↔ HasSum f a L := (isDenseInducing_toCompl α).hasSum_iff f a

/--
theorem `summable_iff_summable_compl_and_tsum_mem` / 定理 `summable_iff_summable_compl_and_tsum_mem`

English:
theorem summable_iff_summable_compl_and_tsum_mem
  given: (f : β -> α)
  proof: (isDenseInducing_toCompl α).summable_iff_tsum_comp_mem_range f

中文:
定理 summable_iff_summable_compl_and_tsum_mem
  条件: (f : β -> α)
  证明: (isDenseInducing_toCompl α).summable_iff_tsum_comp_mem_range f

Depends on / 依赖: isDenseInducing_toCompl, summable_iff_tsum_comp_mem_range
-/
theorem summable_iff_summable_compl_and_tsum_mem (f : β -> α) :
    Summable f L ↔ Summable (toCompl ∘ f) L ∧ ∑'[L] i, toCompl (f i) in Set.range toCompl :=
  (isDenseInducing_toCompl α).summable_iff_tsum_comp_mem_range f

/--
theorem `summable_iff_cauchySeq_finset_and_tsum_mem` / 定理 `summable_iff_cauchySeq_finset_and_tsum_mem`

English:
theorem summable_iff_cauchySeq_finset_and_tsum_mem
  given: (f : β -> α)
  proof: by
  classical
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨ha.cauchySeq, ((summable_iff_summable_compl_and_tsum_mem f).mp ⟨a, ha⟩).2⟩
  · rintro ⟨h_cauchy, h_tsum⟩
    apply (summable_iff_summable_compl_and_tsum_mem f).mpr
    constructor
    · apply summable_iff_cauchySeq_finset.mpr
      simp_rw [

中文:
定理 summable_iff_cauchySeq_finset_and_tsum_mem
  条件: (f : β -> α)
  证明: by
  classical
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨ha.cauchySeq, ((summable_iff_summable_compl_and_tsum_mem f).mp ⟨a, ha⟩).2⟩
  · rintro ⟨h_cauchy, h_tsum⟩
    apply (summable_iff_summable_compl_and_tsum_mem f).mpr
    constructor
    · apply summable_iff_cauchySeq_finset.mpr
      simp_rw [

Depends on / 依赖: Function, Function.comp_apply, cauchySeq, classical, comp_apply, h_cauchy, h_cauchy.map, h_tsum, ha.cauchySeq, map_sum, simp_rw, summable_iff_cauchySeq_finset, summable_iff_cauchySeq_finset.mpr, summable_iff_summable_compl_and_tsum_mem, uniformContinuous_coe
-/
theorem summable_iff_cauchySeq_finset_and_tsum_mem (f : β -> α) :
    Summable f ↔ CauchySeq (fun s : Finset β => ∑ b in s, f b) ∧
      ∑' i, toCompl (f i) in Set.range toCompl := by
  classical
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨ha.cauchySeq, ((summable_iff_summable_compl_and_tsum_mem f).mp ⟨a, ha⟩).2⟩
  · rintro ⟨h_cauchy, h_tsum⟩
    apply (summable_iff_summable_compl_and_tsum_mem f).mpr
    constructor
    · apply summable_iff_cauchySeq_finset.mpr
      simp_rw [Function.comp_apply, ← map_sum]
      exact h_cauchy.map (uniformContinuous_coe α)
    · exact h_tsum

/--
theorem `Summable.toCompl_tsum` / 定理 `Summable.toCompl_tsum`

English:
theorem Summable.toCompl_tsum
  given: [L.NeBot] {f : β -> α} (hf : Summable f L)
  proof: (hf.map_tsum toCompl (continuous_coe α)).symm

中文:
定理 Summable.toCompl_tsum
  条件: [L.NeBot] {f : β -> α} (hf : Summable f L)
  证明: (hf.map_tsum toCompl (continuous_coe α)).symm

Depends on / 依赖: continuous_coe, hf.map_tsum, map_tsum, toCompl
-/
theorem Summable.toCompl_tsum [L.NeBot] {f : β -> α} (hf : Summable f L) :
    ∑'[L] i, toCompl (f i) = ∑'[L] i, f i :=
  (hf.map_tsum toCompl (continuous_coe α)).symm
