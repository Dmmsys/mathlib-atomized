/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Topology.UniformSpace.UniformEmbedding

/-!
# Theory of complete separated uniform spaces.

This file is for elementary lemmas that depend on both Cauchy filters and separation.
-/

public section


open Filter

open Topology Filter

variable {α β : Type*}

/--
theorem `IsComplete.isClosed` / 定理 `IsComplete.isClosed`

English:
theorem IsComplete.isClosed
  given: [UniformSpace α] [T0Space α] {s : Set α} (h : IsComplete s)
  proof: isClosed_iff_clusterPt.2 fun a ha => by
    let f := 𝓝[s] a
    have : Cauchy f := cauchy_nhds.mono' ha inf_le_left
    rcases h f this inf_le_right with ⟨y, ys, fy⟩
    rwa [(tendsto_nhds_unique' ha inf_le_left fy : a = y)]

中文:
定理 IsComplete.isClosed
  条件: [UniformSpace α] [T0Space α] {s : Set α} (h : IsComplete s)
  证明: isClosed_iff_clusterPt.2 fun a ha => by
    let f := 𝓝[s] a
    have : Cauchy f := cauchy_nhds.mono' ha inf_le_left
    rcases h f this inf_le_right with ⟨y, ys, fy⟩
    rwa [(tendsto_nhds_unique' ha inf_le_left fy : a = y)]

Depends on / 依赖: Cauchy, cauchy_nhds, cauchy_nhds.mono, inf_le_left, inf_le_right, isClosed_iff_clusterPt, tendsto_nhds_unique
-/
theorem IsComplete.isClosed [UniformSpace α] [T0Space α] {s : Set α} (h : IsComplete s) :
    IsClosed s :=
  isClosed_iff_clusterPt.2 fun a ha => by
    let f := 𝓝[s] a
    have : Cauchy f := cauchy_nhds.mono' ha inf_le_left
    rcases h f this inf_le_right with ⟨y, ys, fy⟩
    rwa [(tendsto_nhds_unique' ha inf_le_left fy : a = y)]

/--
theorem `IsUniformEmbedding.isClosedEmbedding` / 定理 `IsUniformEmbedding.isClosedEmbedding`

English:
theorem IsUniformEmbedding.isClosedEmbedding
  statement: [UniformSpace α] [UniformSpace β] [CompleteSpace α]
  proof: ⟨hf.isEmbedding, hf.isUniformInducing.isComplete_range.isClosed⟩

中文:
定理 IsUniformEmbedding.isClosedEmbedding
  结论: [UniformSpace α] [UniformSpace β] [CompleteSpace α]
  证明: ⟨hf.isEmbedding, hf.isUniformInducing.isComplete_range.isClosed⟩

Depends on / 依赖: hf.isEmbedding, hf.isUniformInducing.isComplete_range.isClosed, isClosed, isComplete_range, isEmbedding, isUniformInducing
-/
theorem IsUniformEmbedding.isClosedEmbedding [UniformSpace α] [UniformSpace β] [CompleteSpace α]
    [T0Space β] {f : α -> β} (hf : IsUniformEmbedding f) :
    IsClosedEmbedding f :=
  ⟨hf.isEmbedding, hf.isUniformInducing.isComplete_range.isClosed⟩

namespace IsDenseInducing

open Filter

variable [TopologicalSpace α] {β : Type*} [TopologicalSpace β]
variable {γ : Type*} [UniformSpace γ] [CompleteSpace γ] [T0Space γ]

/--
theorem `continuous_extend_of_cauchy` / 定理 `continuous_extend_of_cauchy`

English:
theorem continuous_extend_of_cauchy
  statement: {e : α -> β} {f : α -> γ} (de : IsDenseInducing e)
  proof: de.continuous_extend fun b => CompleteSpace.complete (h b)

中文:
定理 continuous_extend_of_cauchy
  结论: {e : α -> β} {f : α -> γ} (de : IsDenseInducing e)
  证明: de.continuous_extend fun b => CompleteSpace.complete (h b)

Depends on / 依赖: CompleteSpace, CompleteSpace.complete, complete, continuous_extend, de.continuous_extend
-/
theorem continuous_extend_of_cauchy {e : α -> β} {f : α -> γ} (de : IsDenseInducing e)
    (h : forall b : β, Cauchy (map f (comap e <| 𝓝 b))) : Continuous (de.extend f) :=
  de.continuous_extend fun b => CompleteSpace.complete (h b)

end IsDenseInducing
