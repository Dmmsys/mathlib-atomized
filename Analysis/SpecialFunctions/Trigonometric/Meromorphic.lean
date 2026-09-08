/-
Copyright (c) 2026 Xuanji Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuanji Li
-/
module

public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Analysis.Meromorphic.NormalForm
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Meromorphicity of `Complex.tan` and `Complex.tanh`
-/

public section

namespace Complex

/-- The function `tan` is meromorphic in normal form on `Set.univ`. -/
/-
**Complex.meromorphicNFOn_tan** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：meromorphicNFOn_tan : MeromorphicNFOn tan Set.univ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeromorphicNFOn.div`：MeromorphicNFOn.div {f : 𝕜 -> 𝕜} {g : 𝕜 -> 𝕜} {x : 
𝕜} (hf : AnalyticAt 𝕜 f x) (hg : MeromorphicNFAt g x) (hor : g x != 0 ∨ f x != 0
) : Merom…
· 使用引理 `Complex.analyticAt_sin`：analyticAt_sin {x : Complex} : AnalyticAt Comple
x sin x
· 使用定理 `AnalyticAt.meromorphicNFAt`：AnalyticAt.meromorphicNFAt (hf : AnalyticAt 
𝕜 f x) : MeromorphicNFAt f x
· 使用引理 `Complex.analyticAt_cos`：analyticAt_cos {x : Complex} : AnalyticAt Comple
x cos x

--- 原说明 ---
The function `tan` is meromorphic in normal form on `Set.univ`.
-/
theorem meromorphicNFOn_tan : MeromorphicNFOn tan Set.univ := by
  intro x _
  refine MeromorphicNFOn.div analyticAt_sin analyticAt_cos.meromorphicNFAt ?_
  grind [sin_sq_add_cos_sq]

/-- The function `tan` is meromorphic at any `z`. -/
@[fun_prop]
/-
**Complex.meromorphicAt_tan** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：meromorphicAt_tan (z : Complex) : MeromorphicAt tan z
参数：z : Complex。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeromorphicNFAt.meromorphicAt`：MeromorphicNFAt.meromorphicAt (hf : Merom
orphicNFAt f x) : MeromorphicAt f x
· 使用定理 `Complex.meromorphicNFOn_tan`：meromorphicNFOn_tan : MeromorphicNFOn tan S
et.univ
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α

--- 原说明 ---
The function `tan` is meromorphic at any `z`.
-/
theorem meromorphicAt_tan (z : ℂ) : MeromorphicAt tan z :=
  (meromorphicNFOn_tan (Set.mem_univ z)).meromorphicAt

/-- The function `tan` is meromorphic. -/
@[fun_prop]
/-
**Complex.meromorphic_tan** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：meromorphic_tan : Meromorphic tan
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.meromorphicAt_tan`：meromorphicAt_tan (z : Complex) : Meromorphic
At tan z

--- 原说明 ---
The function `tan` is meromorphic.
-/
theorem meromorphic_tan : Meromorphic tan := meromorphicAt_tan

/-- The function `tanh` is meromorphic in normal form on `Set.univ`. -/
/-
**Complex.meromorphicNFOn_tanh** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：meromorphicNFOn_tanh : MeromorphicNFOn tanh Set.univ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeromorphicNFOn.div`：MeromorphicNFOn.div {f : 𝕜 -> 𝕜} {g : 𝕜 -> 𝕜} {x : 
𝕜} (hf : AnalyticAt 𝕜 f x) (hg : MeromorphicNFAt g x) (hor : g x != 0 ∨ f x != 0
) : Merom…
· 使用引理 `Complex.analyticAt_sinh`：analyticAt_sinh {x : Complex} : AnalyticAt Comp
lex sinh x
· 使用定理 `AnalyticAt.meromorphicNFAt`：AnalyticAt.meromorphicNFAt (hf : AnalyticAt 
𝕜 f x) : MeromorphicNFAt f x
· 使用引理 `Complex.analyticAt_cosh`：analyticAt_cosh {x : Complex} : AnalyticAt Comp
lex cosh x

--- 原说明 ---
The function `tanh` is meromorphic in normal form on `Set.univ`.
-/
theorem meromorphicNFOn_tanh : MeromorphicNFOn tanh Set.univ := by
  intro x _
  refine MeromorphicNFOn.div analyticAt_sinh analyticAt_cosh.meromorphicNFAt ?_
  grind [cosh_sq_sub_sinh_sq]

/-- The function `tanh` is meromorphic at any `z`. -/
@[fun_prop]
/-
**Complex.meromorphicAt_tanh** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：meromorphicAt_tanh (z : Complex) : MeromorphicAt tanh z
参数：z : Complex。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeromorphicNFAt.meromorphicAt`：MeromorphicNFAt.meromorphicAt (hf : Merom
orphicNFAt f x) : MeromorphicAt f x
· 使用定理 `Complex.meromorphicNFOn_tanh`：meromorphicNFOn_tanh : MeromorphicNFOn tan
h Set.univ
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α

--- 原说明 ---
The function `tanh` is meromorphic at any `z`.
-/
theorem meromorphicAt_tanh (z : ℂ) : MeromorphicAt tanh z :=
  (meromorphicNFOn_tanh (Set.mem_univ z)).meromorphicAt

/-- The function `tanh` is meromorphic. -/
@[fun_prop]
/-
**Complex.meromorphic_tanh** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：meromorphic_tanh : Meromorphic tanh
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.meromorphicAt_tanh`：meromorphicAt_tanh (z : Complex) : Meromorph
icAt tanh z

--- 原说明 ---
The function `tanh` is meromorphic.
-/
theorem meromorphic_tanh : Meromorphic tanh := meromorphicAt_tanh

end Complex

