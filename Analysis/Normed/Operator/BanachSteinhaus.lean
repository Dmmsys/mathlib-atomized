/-
Copyright (c) 2021 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.LocallyConvex.Barrelled
public import Mathlib.Topology.Baire.CompleteMetrizable

/-!
# The Banach-Steinhaus theorem: Uniform Boundedness Principle

Herein we prove the Banach-Steinhaus theorem for normed spaces: any collection of bounded linear
maps from a Banach space into a normed space which is pointwise bounded is uniformly bounded.

Note that we prove the more general version about barrelled spaces in
`Analysis.LocallyConvex.Barrelled`, and the usual version below is indeed deduced from the
more general setup.
-/

public section

open Set

variable {E F 𝕜 𝕜₂ : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
  [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F]
  {σ₁₂ : 𝕜 ->+* 𝕜₂} [RingHomIsometric σ₁₂]

/--
theorem `banach_steinhaus` / 定理 `banach_steinhaus`

English:
theorem banach_steinhaus
  statement: {ι : Type*} [CompleteSpace E] {g : ι -> E ->SL[σ₁₂] F}
  proof: by
  rw [show (exists C]; rw [forall i]; rw [‖g i‖ <= C) ↔ _ from (NormedSpace.equicontinuous_TFAE g).out 5 2]
  refine (norm_withSeminorms 𝕜₂ F).banach_steinhaus (fun _ x => ?_)
  simpa [bddAbove_def, forall_mem_range] using h x

中文:
定理 banach_steinhaus
  结论: {ι : 类型} [完备空间 E] {g : ι -> E ->SL[σ₁₂] F}
  证明: by
  rw [show (exists C]; rw [forall i]; rw [‖g i‖ <= C) ↔ _ from (NormedSpace.equicontinuous_TFAE g).out 5 2]
  refine (norm_withSeminorms 𝕜₂ F).banach_steinhaus (fun _ x => ?_)
  simpa [bddAbove_def, forall_mem_range] using h x

Depends on / 依赖: NormedSpace, NormedSpace.equicontinuous_TFAE, banach_steinhaus, bddAbove_def, equicontinuous_TFAE, forall_mem_range, norm_withSeminorms
-/
theorem banach_steinhaus {ι : Type*} [CompleteSpace E] {g : ι -> E ->SL[σ₁₂] F}
    (h : forall x, exists C, forall i, ‖g i x‖ <= C) : exists C', forall i, ‖g i‖ <= C' := by
  rw [show (exists C]; rw [forall i]; rw [‖g i‖ <= C) ↔ _ from (NormedSpace.equicontinuous_TFAE g).out 5 2]
  refine (norm_withSeminorms 𝕜₂ F).banach_steinhaus (fun _ x => ?_)
  simpa [bddAbove_def, forall_mem_range] using h x

open ENNReal

/--
theorem `banach_steinhaus_iSup_nnnorm` / 定理 `banach_steinhaus_iSup_nnnorm`

English:
theorem banach_steinhaus_iSup_nnnorm
  statement: {ι : Type*} [CompleteSpace E] {g : ι -> E ->SL[σ₁₂] F}
  proof: by
  rw [show ((⨆ i]; rw [↑‖g i‖₊) < ∞) ↔ _ from (NormedSpace.equicontinuous_TFAE g).out 8 2]
  refine (norm_withSeminorms 𝕜₂ F).banach_steinhaus (fun _ x => ?_)
  simpa [← NNReal.bddAbove_coe, ← Set.range_comp] using! ENNReal.iSup_coe_lt_top.1 (h x)

中文:
定理 banach_steinhaus_iSup_nnnorm
  结论: {ι : 类型} [完备空间 E] {g : ι -> E ->SL[σ₁₂] F}
  证明: by
  rw [show ((⨆ i]; rw [↑‖g i‖₊) < ∞) ↔ _ from (NormedSpace.equicontinuous_TFAE g).out 8 2]
  refine (norm_withSeminorms 𝕜₂ F).banach_steinhaus (fun _ x => ?_)
  simpa [← NNReal.bddAbove_coe, ← Set.range_comp] using! ENNReal.iSup_coe_lt_top.1 (h x)

Depends on / 依赖: ENNReal, ENNReal.iSup_coe_lt_top, NNReal, NNReal.bddAbove_coe, NormedSpace, NormedSpace.equicontinuous_TFAE, Set.range_comp, banach_steinhaus, bddAbove_coe, equicontinuous_TFAE, iSup_coe_lt_top, norm_withSeminorms, range_comp
-/
theorem banach_steinhaus_iSup_nnnorm {ι : Type*} [CompleteSpace E] {g : ι -> E ->SL[σ₁₂] F}
    (h : forall x, (⨆ i, ↑‖g i x‖₊) < ∞) : (⨆ i, ↑‖g i‖₊) < ∞ := by
  rw [show ((⨆ i]; rw [↑‖g i‖₊) < ∞) ↔ _ from (NormedSpace.equicontinuous_TFAE g).out 8 2]
  refine (norm_withSeminorms 𝕜₂ F).banach_steinhaus (fun _ x => ?_)
  simpa [← NNReal.bddAbove_coe, ← Set.range_comp] using! ENNReal.iSup_coe_lt_top.1 (h x)
