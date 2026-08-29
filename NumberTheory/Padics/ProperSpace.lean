/-
Copyright (c) 2024 Jou Glasheen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jou Glasheen, Kevin Buzzard
-/
module

public import Mathlib.Analysis.Normed.Field.ProperSpace
public import Mathlib.NumberTheory.Padics.RingHoms

/-!
# Properness of the p-adic numbers

In this file, we prove that `ℤ_[p]` is totally bounded and compact,
and that `ℚ_[p]` is proper.

## Main results

- `PadicInt.totallyBounded_univ` : The set of p-adic integers `ℤ_[p]` is totally bounded.
- `PadicInt.compactSpace` : The set of p-adic integers `ℤ_[p]` is a compact topological space.
- `Padic.instProperSpace` : The field of p-adic numbers `ℚ_[p]` is a proper metric space.

## Notation

- `p` : Is a natural prime.

## References

Gouvêa, F. Q. (2020) p-adic Numbers An Introduction. 3rd edition.
  Cham, Springer International Publishing
-/

public section

assert_not_exists FiniteDimensional

open Metric Topology

variable (p : Nat) [Fact (Nat.Prime p)]

namespace PadicInt

set_option backward.isDefEq.respectTransparency false in
/--
theorem `totallyBounded_univ` / 定理 `totallyBounded_univ`

English:
theorem totallyBounded_univ
  statement: TotallyBounded (Set.univ : Set Int_[p])
  proof: by
  refine Metric.totallyBounded_iff.mpr (fun ε hε => ?_)
  obtain ⟨k, hk⟩ := exists_pow_neg_lt p hε
  refine ⟨Nat.cast '' Finset.range (p ^ k), Set.toFinite _, fun z _ => ?_⟩
  simp only [PadicInt, Set.mem_iUnion, Metric.mem_ball, exists_prop, Set.exists_mem_image]
  refine ⟨z.appr k, ?_, ?_⟩
  · simpa only [Finset.mem_coe, Finset.mem_range] using z.appr_lt k
  · exact (((z - z.appr k).norm_le_pow_iff_mem_span_pow k).mpr (z.appr_spec k)).trans_lt hk

中文:
定理 totallyBounded_univ
  结论: 全有界 (集合.univ : 集合 整数_[p])
  证明: by
  refine Metric.totallyBounded_iff.mpr (fun ε hε => ?_)
  obtain ⟨k, hk⟩ := exists_pow_neg_lt p hε
  refine ⟨Nat.cast '' Finset.range (p ^ k), Set.toFinite _, fun z _ => ?_⟩
  simp only [PadicInt, Set.mem_iUnion, Metric.mem_ball, exists_prop, Set.exists_mem_image]
  refine ⟨z.appr k, ?_, ?_⟩
  · simpa only [Finset.mem_coe, Finset.mem_range] using z.appr_lt k
  · exact (((z - z.appr k).norm_le_pow_iff_mem_span_pow k).mpr (z.appr_spec k)).trans_lt hk

Depends on / 依赖: Finset, Finset.mem_coe, Finset.mem_range, Finset.range, Metric, Metric.mem_ball, Metric.totallyBounded_iff.mpr, Nat.cast, PadicInt, Set.exists_mem_image, Set.mem_iUnion, Set.toFinite, appr_lt, appr_spec, exists_mem_image, exists_pow_neg_lt, exists_prop, mem_ball, mem_coe, mem_iUnion
-/
theorem totallyBounded_univ : TotallyBounded (Set.univ : Set Int_[p]) := by
  refine Metric.totallyBounded_iff.mpr (fun ε hε => ?_)
  obtain ⟨k, hk⟩ := exists_pow_neg_lt p hε
  refine ⟨Nat.cast '' Finset.range (p ^ k), Set.toFinite _, fun z _ => ?_⟩
  simp only [PadicInt, Set.mem_iUnion, Metric.mem_ball, exists_prop, Set.exists_mem_image]
  refine ⟨z.appr k, ?_, ?_⟩
  · simpa only [Finset.mem_coe, Finset.mem_range] using z.appr_lt k
  · exact (((z - z.appr k).norm_le_pow_iff_mem_span_pow k).mpr (z.appr_spec k)).trans_lt hk

/--
Instance `compactSpace` / 实例 `compactSpace`

English:
instance compactSpace
  signature: : CompactSpace Int_[p]
  body: by
  rw [← isCompact_univ_iff]; rw [isCompact_iff_totallyBounded_isComplete]
  exact ⟨totallyBounded_univ p, isComplete_univ⟩

中文:
实例 compactSpace
  签名: : 紧空间 整数_[p]
  定义体: by
  rw [← isCompact_univ_iff]; rw [isCompact_iff_totallyBounded_isComplete]
  exact ⟨totallyBounded_univ p, isComplete_univ⟩

Depends on / 依赖: isCompact_iff_totallyBounded_isComplete, isCompact_univ_iff, isComplete_univ, totallyBounded_univ
-/
instance compactSpace : CompactSpace Int_[p] := by
  rw [← isCompact_univ_iff]; rw [isCompact_iff_totallyBounded_isComplete]
  exact ⟨totallyBounded_univ p, isComplete_univ⟩

end PadicInt

namespace Padic

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ProperSpace Rat_[p]
  body: by
  suffices LocallyCompactSpace Rat_[p] from .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace _
  have : closedBall 0 1 in 𝓝 (0 : Rat_[p]) := closedBall_mem_nhds _ zero_lt_one
  simp only [closedBall, dist_eq_norm_sub, sub_zero] at this
  refine IsCompact.locallyCompactSpace_of_mem_nhds_of_addGroup ?_ this
  simpa only [isCompact_iff_compactSpace] using! PadicInt.compactSpace p

中文:
实例 :
  签名: 真空间 Rat_[p]
  定义体: by
  suffices LocallyCompactSpace Rat_[p] from .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace _
  have : closedBall 0 1 in 𝓝 (0 : Rat_[p]) := closedBall_mem_nhds _ zero_lt_one
  simp only [closedBall, dist_eq_norm_sub, sub_zero] at this
  refine IsCompact.locallyCompactSpace_of_mem_nhds_of_addGroup ?_ this
  simpa only [isCompact_iff_compactSpace] using! PadicInt.compactSpace p

Depends on / 依赖: IsCompact, IsCompact.locallyCompactSpace_of_mem_nhds_of_addGroup, LocallyCompactSpace, PadicInt, PadicInt.compactSpace, Rat_, closedBall, closedBall_mem_nhds, compactSpace, dist_eq_norm_sub, isCompact_iff_compactSpace, locallyCompactSpace_of_mem_nhds_of_addGroup, of_nontriviallyNormedField_of_weaklyLocallyCompactSpace, sub_zero, zero_lt_one
-/
instance : ProperSpace Rat_[p] := by
  suffices LocallyCompactSpace Rat_[p] from .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace _
  have : closedBall 0 1 in 𝓝 (0 : Rat_[p]) := closedBall_mem_nhds _ zero_lt_one
  simp only [closedBall, dist_eq_norm_sub, sub_zero] at this
  refine IsCompact.locallyCompactSpace_of_mem_nhds_of_addGroup ?_ this
  simpa only [isCompact_iff_compactSpace] using! PadicInt.compactSpace p

end Padic
