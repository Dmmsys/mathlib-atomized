/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# Analyticity on `WithLp`
-/

public section

open WithLp

open scoped ENNReal

namespace WithLp

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-
**WithLp.analyticOn_ofLp** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
形式化陈述：analyticOn_ofLp (s : Set (WithLp p (E × F))) : AnalyticOn 𝕜 ofLp s
参数：s : Set (WithLp p (E × F))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.analyticOn`：∀ {𝕜 : Type u_1} [inst : NontriviallyN
ormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedS
pace 𝕜 E] {F : Type u_…
-/
lemma analyticOn_ofLp (s : Set (WithLp p (E × F))) : AnalyticOn 𝕜 ofLp s :=
  (prodContinuousLinearEquiv p 𝕜 E F).analyticOn s
/-
**WithLp.analyticOn_toLp** 是 Mathlib 中的一个引理，位于命名空间 `WithLp`。
形式化陈述：analyticOn_toLp (s : Set (E × F)) : AnalyticOn 𝕜 (toLp p) s
参数：s : Set (E × F)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.analyticOn`：∀ {𝕜 : Type u_1} [inst : NontriviallyN
ormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedS
pace 𝕜 E] {F : Type u_…
-/
lemma analyticOn_toLp (s : Set (E × F)) : AnalyticOn 𝕜 (toLp p) s :=
  (prodContinuousLinearEquiv p 𝕜 E F).symm.analyticOn s

end WithLp

namespace PiLp

variable {𝕜 ι : Type*} [Fintype ι] {E : ι → Type*} [NontriviallyNormedField 𝕜]
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-
**PiLp.analyticOn_ofLp** 是 Mathlib 中的一个引理，位于命名空间 `PiLp`。
形式化陈述：analyticOn_ofLp (s : Set (PiLp p E)) : AnalyticOn 𝕜 ofLp s
参数：s : Set (PiLp p E)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.analyticOn`：∀ {𝕜 : Type u_1} [inst : NontriviallyN
ormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedS
pace 𝕜 E] {F : Type u_…
-/
lemma analyticOn_ofLp (s : Set (PiLp p E)) : AnalyticOn 𝕜 ofLp s :=
  (continuousLinearEquiv p 𝕜 E).analyticOn s
/-
**PiLp.analyticOn_toLp** 是 Mathlib 中的一个引理，位于命名空间 `PiLp`。
形式化陈述：analyticOn_toLp (s : Set (Π i, E i)) : AnalyticOn 𝕜 (toLp p) s
参数：s : Set (Π i, E i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearEquiv.analyticOn`：∀ {𝕜 : Type u_1} [inst : NontriviallyN
ormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedS
pace 𝕜 E] {F : Type u_…
-/
lemma analyticOn_toLp (s : Set (Π i, E i)) : AnalyticOn 𝕜 (toLp p) s :=
  (continuousLinearEquiv p 𝕜 E).symm.analyticOn s

end PiLp

