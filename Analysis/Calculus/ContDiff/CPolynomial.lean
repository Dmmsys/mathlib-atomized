/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# Higher smoothness of continuously polynomial functions

We prove that continuously polynomial functions are `C^∞`. In particular, this is the case
of continuous multilinear maps.
-/

public section

open Filter Asymptotics

open scoped ENNReal ContDiff

universe u v

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

section fderiv

variable {p : FormalMultilinearSeries 𝕜 E F} {r : ℝ≥0∞} {n : ℕ}
variable {f : E → F} {x : E} {s : Set E}

/-- A polynomial function is infinitely differentiable. -/
/-
**CPolynomialOn.contDiffOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CPolynomialOn.contDiffOn (h : CPolynomialOn 𝕜 f s) {n : Nat∞ω} : ContDiffO
n 𝕜 n f s
参数：h : CPolynomialOn 𝕜 f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CPolynomialOn.analyticOnNhd`：CPolynomialOn.analyticOnNhd {s : Set E} (hf
 : CPolynomialOn 𝕜 f s) : AnalyticOnNhd 𝕜 f s
· 使用定理 `isOpen_cpolynomialAt`：isOpen_cpolynomialAt : IsOpen { x | CPolynomialAt 
𝕜 f x }
· 使用定理 `AnalyticOnNhd.contDiffOn`：AnalyticOnNhd.contDiffOn (h : AnalyticOnNhd 𝕜 
f s) (hs : UniqueDiffOn 𝕜 s) : ContDiffOn 𝕜 n f s
· 使用定理 `IsOpen.uniqueDiffOn`：IsOpen.uniqueDiffOn (hs : IsOpen s) : UniqueDiffOn 
𝕜 s
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContDiffOn.mono`：ContDiffOn.mono (h : ContDiffOn 𝕜 n f s) {t : Set E} (h
st : t subseteq s) : ContDiffOn 𝕜 n f t

--- 原说明 ---
A polynomial function is infinitely differentiable.
-/
theorem CPolynomialOn.contDiffOn (h : CPolynomialOn 𝕜 f s) {n : ℕ∞ω} :
    ContDiffOn 𝕜 n f s := by
  let t := { x | CPolynomialAt 𝕜 f x }
  suffices ContDiffOn 𝕜 n f t from this.mono h
  suffices AnalyticOnNhd 𝕜 f t by
    have t_open : IsOpen t := isOpen_cpolynomialAt 𝕜 f
    exact AnalyticOnNhd.contDiffOn this t_open.uniqueDiffOn
  have H : CPolynomialOn 𝕜 f t := fun _x hx ↦ hx
  exact H.analyticOnNhd
/-
**CPolynomialAt.contDiffAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CPolynomialAt.contDiffAt (h : CPolynomialAt 𝕜 f x) {n : Nat∞ω} : ContDiffA
t 𝕜 n f x
参数：h : CPolynomialAt 𝕜 f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CPolynomialAt.exists_mem_nhds_cpolynomialOn`：CPolynomialAt.exists_mem_nh
ds_cpolynomialOn {f : E -> F} {x : E} (h : CPolynomialAt 𝕜 f x) : exists s in 𝓝 
x, CPolynomialOn 𝕜 f s
· 使用定理 `ContDiffOn.contDiffAt`：ContDiffOn.contDiffAt (h : ContDiffOn 𝕜 n f s) (h
x : s in 𝓝 x) : ContDiffAt 𝕜 n f x
· 使用定理 `CPolynomialOn.contDiffOn`：CPolynomialOn.contDiffOn (h : CPolynomialOn 𝕜 
f s) {n : Nat∞ω} : ContDiffOn 𝕜 n f s
-/
theorem CPolynomialAt.contDiffAt (h : CPolynomialAt 𝕜 f x) {n : ℕ∞ω} :
    ContDiffAt 𝕜 n f x :=
  let ⟨_, hs, hf⟩ := h.exists_mem_nhds_cpolynomialOn
  hf.contDiffOn.contDiffAt hs

end fderiv

namespace ContinuousMultilinearMap

variable {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  [Fintype ι] (f : ContinuousMultilinearMap 𝕜 E F) {n : ℕ∞ω} {x : Π i, E i}

open FormalMultilinearSeries

/-
**ContinuousMultilinearMap.contDiffAt** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMulti
linearMap`。
形式化陈述：contDiffAt : ContDiffAt 𝕜 n f x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CPolynomialAt.contDiffAt`：CPolynomialAt.contDiffAt (h : CPolynomialAt 𝕜 
f x) {n : Nat∞ω} : ContDiffAt 𝕜 n f x
· 使用引理 `ContinuousMultilinearMap.cpolynomialAt`：cpolynomialAt : CPolynomialAt 𝕜 
f x
-/
lemma contDiffAt : ContDiffAt 𝕜 n f x := f.cpolynomialAt.contDiffAt
/-
**ContinuousMultilinearMap.contDiff** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousMultili
nearMap`。
形式化陈述：contDiff : ContDiff 𝕜 n f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `contDiff_iff_contDiffAt`：contDiff_iff_contDiffAt : ContDiff 𝕜 n f ↔ fora
ll x, ContDiffAt 𝕜 n f x
· 使用引理 `ContinuousMultilinearMap.contDiffAt`：contDiffAt : ContDiffAt 𝕜 n f x
-/
lemma contDiff : ContDiff 𝕜 n f := contDiff_iff_contDiffAt.mpr (fun _ ↦ f.contDiffAt)

end ContinuousMultilinearMap

