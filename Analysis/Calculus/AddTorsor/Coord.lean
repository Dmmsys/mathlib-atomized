/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases

/-!
# Barycentric coordinates are smooth
-/

public section

variable {ι 𝕜 E P : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [MetricSpace P] [NormedAddTorsor E P]
variable [FiniteDimensional 𝕜 E]

/-
**smooth_barycentric_coord** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smooth_barycentric_coord (b : AffineBasis ι 𝕜 E) (i : ι) : ContDiff 𝕜 ⊤ (b
.coord i)
参数：b : AffineBasis ι 𝕜 E；i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAffineMap.contDiff`：contDiff {n : WithTop Nat∞} (f : V ->ᴬ[𝕜] 
W) : ContDiff 𝕜 n f
· 使用定理 `continuous_barycentric_coord`：continuous_barycentric_coord (i : ι) : Con
tinuous (b.coord i)
-/
theorem smooth_barycentric_coord (b : AffineBasis ι 𝕜 E) (i : ι) : ContDiff 𝕜 ⊤ (b.coord i) :=
  (⟨b.coord i, continuous_barycentric_coord b i⟩ : E →ᴬ[𝕜] 𝕜).contDiff
