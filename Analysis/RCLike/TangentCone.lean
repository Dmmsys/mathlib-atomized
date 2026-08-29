/-
Copyright (c) 2025 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Topology.Instances.RealVectorSpace
public import Mathlib.Analysis.Calculus.TangentCone.Real

/-! # Relationships between unique differentiability over `ℝ` and `ℂ`

A set of unique differentiability for `ℝ` is also a set of unique differentiability for `ℂ`
(or for a general field satisfying `IsRCLikeNormedField 𝕜`).
-/

public section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [h𝕜 : IsRCLikeNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace Real E]
  {s : Set E} {x : E}

/--
theorem `tangentConeAt_real_subset_isRCLikeNormedField` / 定理 `tangentConeAt_real_subset_isRCLikeNormedField`

English:
theorem tangentConeAt_real_subset_isRCLikeNormedField
  proof: by
  let := h𝕜.rclike
  exact tangentConeAt_mono_field

中文:
定理 tangentConeAt_real_subset_isRCLikeNormedField
  证明: by
  let := h𝕜.rclike
  exact tangentConeAt_mono_field

Depends on / 依赖: rclike, tangentConeAt_mono_field
-/
theorem tangentConeAt_real_subset_isRCLikeNormedField :
    tangentConeAt Real s x subseteq tangentConeAt 𝕜 s x := by
  let := h𝕜.rclike
  exact tangentConeAt_mono_field

/--
theorem `UniqueDiffWithinAt.of_real` / 定理 `UniqueDiffWithinAt.of_real`

English:
theorem UniqueDiffWithinAt.of_real
  given: (hs : UniqueDiffWithinAt Real s x)
  proof: by
  let := h𝕜.rclike
  exact hs.mono_field

中文:
定理 UniqueDiffWithinAt.of_real
  条件: (hs : UniqueDiffWithinAt 实数 s x)
  证明: by
  let := h𝕜.rclike
  exact hs.mono_field

Depends on / 依赖: hs.mono_field, mono_field, rclike
-/
theorem UniqueDiffWithinAt.of_real (hs : UniqueDiffWithinAt Real s x) :
    UniqueDiffWithinAt 𝕜 s x := by
  let := h𝕜.rclike
  exact hs.mono_field

/--
theorem `UniqueDiffOn.of_real` / 定理 `UniqueDiffOn.of_real`

English:
theorem UniqueDiffOn.of_real
  given: (hs : UniqueDiffOn Real s)
  proof: fun x hx => (hs x hx).of_real

中文:
定理 UniqueDiffOn.of_real
  条件: (hs : UniqueDiffOn 实数 s)
  证明: fun x hx => (hs x hx).of_real

Depends on / 依赖: of_real
-/
theorem UniqueDiffOn.of_real (hs : UniqueDiffOn Real s) :
    UniqueDiffOn 𝕜 s :=
  fun x hx => (hs x hx).of_real

/--
theorem `uniqueDiffWithinAt_convex_of_isRCLikeNormedField` / 定理 `uniqueDiffWithinAt_convex_of_isRCLikeNormedField`

English:
theorem uniqueDiffWithinAt_convex_of_isRCLikeNormedField
  proof: UniqueDiffWithinAt.of_real (uniqueDiffWithinAt_convex conv hs hx)

中文:
定理 uniqueDiffWithinAt_convex_of_isRCLikeNormedField
  证明: UniqueDiffWithinAt.of_real (uniqueDiffWithinAt_convex conv hs hx)

Depends on / 依赖: UniqueDiffWithinAt, UniqueDiffWithinAt.of_real, of_real, uniqueDiffWithinAt_convex
-/
theorem uniqueDiffWithinAt_convex_of_isRCLikeNormedField
    (conv : Convex Real s) (hs : (interior s).Nonempty) (hx : x in closure s) :
    UniqueDiffWithinAt 𝕜 s x :=
  UniqueDiffWithinAt.of_real (uniqueDiffWithinAt_convex conv hs hx)

/--
theorem `uniqueDiffOn_convex_of_isRCLikeNormedField` / 定理 `uniqueDiffOn_convex_of_isRCLikeNormedField`

English:
theorem uniqueDiffOn_convex_of_isRCLikeNormedField
  proof: UniqueDiffOn.of_real (uniqueDiffOn_convex conv hs)

中文:
定理 uniqueDiffOn_convex_of_isRCLikeNormedField
  证明: UniqueDiffOn.of_real (uniqueDiffOn_convex conv hs)

Depends on / 依赖: UniqueDiffOn, UniqueDiffOn.of_real, of_real, uniqueDiffOn_convex
-/
theorem uniqueDiffOn_convex_of_isRCLikeNormedField
    (conv : Convex Real s) (hs : (interior s).Nonempty) : UniqueDiffOn 𝕜 s :=
  UniqueDiffOn.of_real (uniqueDiffOn_convex conv hs)
