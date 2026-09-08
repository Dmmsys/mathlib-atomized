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
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E]
  {s : Set E} {x : E}

/-
**tangentConeAt_real_subset_isRCLikeNormedField** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tangentConeAt_real_subset_isRCLikeNormedField : tangentConeAt Real s x sub
seteq tangentConeAt 𝕜 s x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tangentConeAt_mono_field`：tangentConeAt_mono_field {𝕜' : Type*} [Monoid 
𝕜'] [SMul 𝕜 𝕜'] [MulAction 𝕜' E] [IsScalarTower 𝕜 𝕜' E] : tangentConeAt 𝕜 s x su
bseteq tangent…
· 使用定理 `Real.isScalarTower`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _
root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousSMul ℝ E]   [T2Space 
E] {A : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
-/
theorem tangentConeAt_real_subset_isRCLikeNormedField :
    tangentConeAt ℝ s x ⊆ tangentConeAt 𝕜 s x := by
  let := h𝕜.rclike
  exact tangentConeAt_mono_field
/-
**UniqueDiffWithinAt.of_real** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniqueDiffWithinAt.of_real (hs : UniqueDiffWithinAt Real s x) : UniqueDiff
WithinAt 𝕜 s x
参数：hs : UniqueDiffWithinAt Real s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueDiffWithinAt.mono_field`：UniqueDiffWithinAt.mono_field (hs : Uniqu
eDiffWithinAt 𝕜 s x) : UniqueDiffWithinAt 𝕜' s x
· 使用定理 `Real.isScalarTower`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 : _
root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousSMul ℝ E]   [T2Space 
E] {A : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
-/
theorem UniqueDiffWithinAt.of_real (hs : UniqueDiffWithinAt ℝ s x) :
    UniqueDiffWithinAt 𝕜 s x := by
  let := h𝕜.rclike
  exact hs.mono_field
/-
**UniqueDiffOn.of_real** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniqueDiffOn.of_real (hs : UniqueDiffOn Real s) : UniqueDiffOn 𝕜 s
参数：hs : UniqueDiffOn Real s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueDiffWithinAt.of_real`：UniqueDiffWithinAt.of_real (hs : UniqueDiffW
ithinAt Real s x) : UniqueDiffWithinAt 𝕜 s x
-/
theorem UniqueDiffOn.of_real (hs : UniqueDiffOn ℝ s) :
    UniqueDiffOn 𝕜 s :=
  fun x hx ↦ (hs x hx).of_real

/-- In a real or complex vector space, a convex set with nonempty interior is a set of unique
differentiability. -/
/-
**uniqueDiffWithinAt_convex_of_isRCLikeNormedField** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniqueDiffWithinAt_convex_of_isRCLikeNormedField (conv : Convex Real s) (h
s : (interior s).Nonempty) (hx : x in closure s) : UniqueDiffWithinAt 𝕜 s x
参数：conv : Convex Real s；hs : (interior s).Nonempty；hx : x in closure s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueDiffWithinAt.of_real`：UniqueDiffWithinAt.of_real (hs : UniqueDiffW
ithinAt Real s x) : UniqueDiffWithinAt 𝕜 s x
· 使用定理 `uniqueDiffWithinAt_convex`：uniqueDiffWithinAt_convex (conv : Convex Real
 s) (hs : (interior s).Nonempty) {x : E} (hx : x in closure s) : UniqueDiffWithi
nAt Real s x
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E

--- 原说明 ---
In a real or complex vector space, a convex set with nonempty interior is a set 
of unique
differentiability.
-/
theorem uniqueDiffWithinAt_convex_of_isRCLikeNormedField
    (conv : Convex ℝ s) (hs : (interior s).Nonempty) (hx : x ∈ closure s) :
    UniqueDiffWithinAt 𝕜 s x :=
  UniqueDiffWithinAt.of_real (uniqueDiffWithinAt_convex conv hs hx)

/-- In a real or complex vector space, a convex set with nonempty interior is a set of unique
differentiability. -/
/-
**uniqueDiffOn_convex_of_isRCLikeNormedField** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniqueDiffOn_convex_of_isRCLikeNormedField (conv : Convex Real s) (hs : (i
nterior s).Nonempty) : UniqueDiffOn 𝕜 s
参数：conv : Convex Real s；hs : (interior s).Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueDiffOn.of_real`：UniqueDiffOn.of_real (hs : UniqueDiffOn Real s) : 
UniqueDiffOn 𝕜 s
· 使用定理 `uniqueDiffOn_convex`：uniqueDiffOn_convex (conv : Convex Real s) (hs : (i
nterior s).Nonempty) : UniqueDiffOn Real s
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E

--- 原说明 ---
In a real or complex vector space, a convex set with nonempty interior is a set 
of unique
differentiability.
-/
theorem uniqueDiffOn_convex_of_isRCLikeNormedField
    (conv : Convex ℝ s) (hs : (interior s).Nonempty) : UniqueDiffOn 𝕜 s :=
  UniqueDiffOn.of_real (uniqueDiffOn_convex conv hs)
