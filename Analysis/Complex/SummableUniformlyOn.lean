/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Topology.Algebra.InfiniteSum.UniformOn

/-!
# Differentiability of uniformly convergent series sums of functions

We collect some results about the differentiability of infinite sums.

-/

public section

/--
lemma `SummableLocallyUniformlyOn.differentiableOn` / 引理 `SummableLocallyUniformlyOn.differentiableOn`

English:
lemma SummableLocallyUniformlyOn.differentiableOn
  statement: {ι E : Type*} [NormedAddCommGroup E]
  proof: by
  obtain ⟨g, hg⟩ := h
  have hc := (hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp hg).differentiableOn ?_ hs
  · apply hc.congr
    apply hg.tsum_eqOn
  · filter_upwards with t r hr using
      DifferentiableWithinAt.fun_sum fun a ha => (hf2 a r hr).differentiableWithinAt

中文:
引理 SummableLocallyUniformlyOn.differentiableOn
  结论: {ι E : 类型} [赋范交换加群 E]
  证明: by
  obtain ⟨g, hg⟩ := h
  have hc := (hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp hg).differentiableOn ?_ hs
  · apply hc.congr
    apply hg.tsum_eqOn
  · filter_upwards with t r hr using
      DifferentiableWithinAt.fun_sum fun a ha => (hf2 a r hr).differentiableWithinAt

Depends on / 依赖: DifferentiableWithinAt, DifferentiableWithinAt.fun_sum, differentiableOn, differentiableWithinAt, filter_upwards, fun_sum, hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn, hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp, hc.congr, hg.tsum_eqOn, tsum_eqOn
-/
lemma SummableLocallyUniformlyOn.differentiableOn {ι E : Type*} [NormedAddCommGroup E]
    [NormedSpace Complex E] [CompleteSpace E] {f : ι -> Complex -> E} {s : Set Complex}
    (hs : IsOpen s) (h : SummableLocallyUniformlyOn f s)
    (hf2 : forall n r, r in s -> DifferentiableAt Complex (f n) r) :
    DifferentiableOn Complex (fun z => ∑' n, f n z) s := by
  obtain ⟨g, hg⟩ := h
  have hc := (hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp hg).differentiableOn ?_ hs
  · apply hc.congr
    apply hg.tsum_eqOn
  · filter_upwards with t r hr using
      DifferentiableWithinAt.fun_sum fun a ha => (hf2 a r hr).differentiableWithinAt
