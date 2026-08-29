/-
Copyright (c) 2022 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
module

public import Mathlib.Analysis.Normed.Group.Uniform

/-!
# Further lemmas about normed groups

This file contains further lemmas about normed groups, requiring heavier imports than
`Mathlib/Analysis/Normed/Group/Basic.lean`.

## TODO

- Move lemmas from `Basic` to other places, including this file.

-/

public section

variable {E : Type*} [SeminormedAddCommGroup E]
open NNReal Topology

/--
theorem `eventually_nnnorm_sub_lt` / 定理 `eventually_nnnorm_sub_lt`

English:
theorem eventually_nnnorm_sub_lt
  given: (x₀ : E) {ε : Real>=0} (ε_pos : 0 < ε)
  proof: (continuousAt_id.sub continuousAt_const).nnnorm (gt_mem_nhds <| by simpa)

中文:
定理 eventually_nnnorm_sub_lt
  条件: (x₀ : E) {ε : 实数>=0} (ε_pos : 0 < ε)
  证明: (continuousAt_id.sub continuousAt_const).nnnorm (gt_mem_nhds <| by simpa)

Depends on / 依赖: continuousAt_const, continuousAt_id, continuousAt_id.sub, gt_mem_nhds, nnnorm
-/
theorem eventually_nnnorm_sub_lt (x₀ : E) {ε : Real>=0} (ε_pos : 0 < ε) :
    forallᶠ x in 𝓝 x₀, ‖x - x₀‖₊ < ε :=
  (continuousAt_id.sub continuousAt_const).nnnorm (gt_mem_nhds <| by simpa)

/--
theorem `eventually_norm_sub_lt` / 定理 `eventually_norm_sub_lt`

English:
theorem eventually_norm_sub_lt
  given: (x₀ : E) {ε : Real} (ε_pos : 0 < ε)
  proof: (continuousAt_id.sub continuousAt_const).norm (gt_mem_nhds <| by simpa)

中文:
定理 eventually_norm_sub_lt
  条件: (x₀ : E) {ε : 实数} (ε_pos : 0 < ε)
  证明: (continuousAt_id.sub continuousAt_const).norm (gt_mem_nhds <| by simpa)

Depends on / 依赖: continuousAt_const, continuousAt_id, continuousAt_id.sub, gt_mem_nhds
-/
theorem eventually_norm_sub_lt (x₀ : E) {ε : Real} (ε_pos : 0 < ε) :
    forallᶠ x in 𝓝 x₀, ‖x - x₀‖ < ε :=
  (continuousAt_id.sub continuousAt_const).norm (gt_mem_nhds <| by simpa)
