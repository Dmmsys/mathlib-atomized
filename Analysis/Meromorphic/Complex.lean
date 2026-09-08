/-
Copyright (c) 2025 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module

public import Mathlib.Analysis.Meromorphic.NormalForm
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# The Gamma function is meromorphic
-/

public section

open Set Complex

/-
**MeromorphicNFOn.Gamma** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MeromorphicNFOn.Gamma : MeromorphicNFOn Gamma univ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `meromorphicNFOn_inv`：meromorphicNFOn_inv {f : 𝕜 -> 𝕜} : MeromorphicNFOn 
f⁻¹ U ↔ MeromorphicNFOn f U where mp h _ hx
· 使用定理 `AnalyticOnNhd.meromorphicNFOn`：AnalyticOnNhd.meromorphicNFOn (h₁f : Anal
yticOnNhd 𝕜 f U) : MeromorphicNFOn f U
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Complex.analyticOnNhd_univ_iff_differentiable`：analyticOnNhd_univ_iff_di
fferentiable {f : Complex -> E} : AnalyticOnNhd Complex f univ ↔ Differentiable 
Complex f
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `Complex.differentiable_one_div_Gamma`：differentiable_one_div_Gamma : Dif
ferentiable Complex fun s : Complex => (Gamma s)⁻¹
-/
lemma MeromorphicNFOn.Gamma : MeromorphicNFOn Gamma univ :=
  meromorphicNFOn_inv.mp <| AnalyticOnNhd.meromorphicNFOn <|
    analyticOnNhd_univ_iff_differentiable.mpr differentiable_one_div_Gamma

-- TODO: restate `MeromorphicNFOn.Gamma` when `MeromorphicNF` is defined
/-
**Meromorphic.Gamma** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Meromorphic.Gamma : Meromorphic Gamma
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `meromorphicOn_univ`：meromorphicOn_univ {f : 𝕜 -> E} : MeromorphicOn f Se
t.univ ↔ Meromorphic f
· 使用定理 `MeromorphicNFOn.meromorphicOn`：MeromorphicNFOn.meromorphicOn (hf : Merom
orphicNFOn f U) : MeromorphicOn f U
· 使用引理 `MeromorphicNFOn.Gamma`：MeromorphicNFOn.Gamma : MeromorphicNFOn Gamma uni
v
-/
lemma Meromorphic.Gamma : Meromorphic Gamma :=
  meromorphicOn_univ.mp MeromorphicNFOn.Gamma.meromorphicOn
/-
**MeromorphicOn.Gamma** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MeromorphicOn.Gamma {s} : MeromorphicOn Gamma s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Meromorphic.meromorphicOn`：meromorphicOn {s : Set 𝕜} (hf : Meromorphic f
) : MeromorphicOn f s
· 使用引理 `Meromorphic.Gamma`：Meromorphic.Gamma : Meromorphic Gamma
-/
lemma MeromorphicOn.Gamma {s} : MeromorphicOn Gamma s :=
  Meromorphic.Gamma.meromorphicOn
