/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.LineDeriv.Basic

/-!
# Local extremum and line derivatives

If `f` has a local extremum at a point, then the derivative at this point is zero.
In this file we prove several versions of this fact for line derivatives.
-/

public section

open Function Set Filter
open scoped Topology

section Module

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {f : E → ℝ} {s : Set E} {a b : E} {f' : ℝ}

/-
**IsExtrFilter.hasLineDerivAt_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsExtrFilter.hasLineDerivAt_eq_zero {l : Filter E} (h : IsExtrFilter f l a
) (hd : HasLineDerivAt Real f f' a b) (h' : Tendsto (fun t : Real => a + t • b) 
(𝓝 0) l) : f' = 0
参数：h : IsExtrFilter f l a；hd : HasLineDerivAt Real f f' a b；h' : Tendsto (fun t 
: Real => a + t • b) (𝓝 0) l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalExtr.hasDerivAt_eq_zero`：IsLocalExtr.hasDerivAt_eq_zero (h : IsLo
calExtr f a) : HasDerivAt f f' a -> f' = 0
· 使用定理 `IsExtrFilter.comp_tendsto`：IsExtrFilter.comp_tendsto {g : δ -> α} {l' : 
Filter δ} {b : δ} (hf : IsExtrFilter f l (g b)) (hg : Tendsto g l' l) : IsExtrFi
lter (f ∘ g) l'…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem IsExtrFilter.hasLineDerivAt_eq_zero {l : Filter E} (h : IsExtrFilter f l a)
    (hd : HasLineDerivAt ℝ f f' a b) (h' : Tendsto (fun t : ℝ ↦ a + t • b) (𝓝 0) l) : f' = 0 :=
  IsLocalExtr.hasDerivAt_eq_zero (IsExtrFilter.comp_tendsto (by simpa using h) h') hd
/-
**IsExtrFilter.lineDeriv_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsExtrFilter.lineDeriv_eq_zero {l : Filter E} (h : IsExtrFilter f l a) (h'
 : Tendsto (fun t : Real => a + t • b) (𝓝 0) l) : lineDeriv Real f a b = 0
参数：h : IsExtrFilter f l a；h' : Tendsto (fun t : Real => a + t • b) (𝓝 0) l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsExtrFilter.hasLineDerivAt_eq_zero`：IsExtrFilter.hasLineDerivAt_eq_zero
 {l : Filter E} (h : IsExtrFilter f l a) (hd : HasLineDerivAt Real f f' a b) (h'
 : Tendsto (fun t : Real …
· 使用定理 `LineDifferentiableAt.hasLineDerivAt`：LineDifferentiableAt.hasLineDerivAt
 (h : LineDifferentiableAt 𝕜 f x v) : HasLineDerivAt 𝕜 f (lineDeriv 𝕜 f x v) x v
· 使用定理 `lineDeriv_zero_of_not_lineDifferentiableAt`：lineDeriv_zero_of_not_lineDi
fferentiableAt (h : ¬LineDifferentiableAt 𝕜 f x v) : lineDeriv 𝕜 f x v = 0
-/
theorem IsExtrFilter.lineDeriv_eq_zero {l : Filter E} (h : IsExtrFilter f l a)
    (h' : Tendsto (fun t : ℝ ↦ a + t • b) (𝓝 0) l) : lineDeriv ℝ f a b = 0 := by
  classical
  exact if hd : LineDifferentiableAt ℝ f a b then
    h.hasLineDerivAt_eq_zero hd.hasLineDerivAt h'
  else
    lineDeriv_zero_of_not_lineDifferentiableAt hd
/-
**IsExtrOn.hasLineDerivAt_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsExtrOn.hasLineDerivAt_eq_zero (h : IsExtrOn f s a) (hd : HasLineDerivAt 
Real f f' a b) (h' : forallᶠ t : Real in 𝓝 0, a + t • b in s) : f' = 0
参数：h : IsExtrOn f s a；hd : HasLineDerivAt Real f f' a b；h' : forallᶠ t : Real in
 𝓝 0, a + t • b in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsExtrFilter.hasLineDerivAt_eq_zero`：IsExtrFilter.hasLineDerivAt_eq_zero
 {l : Filter E} (h : IsExtrFilter f l a) (hd : HasLineDerivAt Real f f' a b) (h'
 : Tendsto (fun t : Real …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_principal`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l
 : Filter α} {s : Set β},   Filter.Tendsto f l (Filter.principal s) ↔ ∀ᶠ (a : α)
 in l, f a ∈ s
-/
theorem IsExtrOn.hasLineDerivAt_eq_zero (h : IsExtrOn f s a) (hd : HasLineDerivAt ℝ f f' a b)
    (h' : ∀ᶠ t : ℝ in 𝓝 0, a + t • b ∈ s) : f' = 0 :=
  IsExtrFilter.hasLineDerivAt_eq_zero h hd <| tendsto_principal.2 h'
/-
**IsExtrOn.lineDeriv_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsExtrOn.lineDeriv_eq_zero (h : IsExtrOn f s a) (h' : forallᶠ t : Real in 
𝓝 0, a + t • b in s) : lineDeriv Real f a b = 0
参数：h : IsExtrOn f s a；h' : forallᶠ t : Real in 𝓝 0, a + t • b in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsExtrFilter.lineDeriv_eq_zero`：IsExtrFilter.lineDeriv_eq_zero {l : Filt
er E} (h : IsExtrFilter f l a) (h' : Tendsto (fun t : Real => a + t • b) (𝓝 0) l
) : lineDeriv Real f…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_principal`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l
 : Filter α} {s : Set β},   Filter.Tendsto f l (Filter.principal s) ↔ ∀ᶠ (a : α)
 in l, f a ∈ s
-/
theorem IsExtrOn.lineDeriv_eq_zero (h : IsExtrOn f s a) (h' : ∀ᶠ t : ℝ in 𝓝 0, a + t • b ∈ s) :
    lineDeriv ℝ f a b = 0 :=
  IsExtrFilter.lineDeriv_eq_zero h <| tendsto_principal.2 h'
/-
**IsMinOn.hasLineDerivAt_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMinOn.hasLineDerivAt_eq_zero (h : IsMinOn f s a) (hd : HasLineDerivAt Re
al f f' a b) (h' : forallᶠ t : Real in 𝓝 0, a + t • b in s) : f' = 0
参数：h : IsMinOn f s a；hd : HasLineDerivAt Real f f' a b；h' : forallᶠ t : Real in 
𝓝 0, a + t • b in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsExtrOn.hasLineDerivAt_eq_zero`：IsExtrOn.hasLineDerivAt_eq_zero (h : Is
ExtrOn f s a) (hd : HasLineDerivAt Real f f' a b) (h' : forallᶠ t : Real in 𝓝 0,
 a + t • b in s) : f'…
· 使用定理 `IsMinOn.isExtr`：IsMinOn.isExtr (h : IsMinOn f s a) : IsExtrOn f s a
-/
theorem IsMinOn.hasLineDerivAt_eq_zero (h : IsMinOn f s a) (hd : HasLineDerivAt ℝ f f' a b)
    (h' : ∀ᶠ t : ℝ in 𝓝 0, a + t • b ∈ s) : f' = 0 :=
  h.isExtr.hasLineDerivAt_eq_zero hd h'
/-
**IsMinOn.lineDeriv_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMinOn.lineDeriv_eq_zero (h : IsMinOn f s a) (h' : forallᶠ t : Real in 𝓝 
0, a + t • b in s) : lineDeriv Real f a b = 0
参数：h : IsMinOn f s a；h' : forallᶠ t : Real in 𝓝 0, a + t • b in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsExtrOn.lineDeriv_eq_zero`：IsExtrOn.lineDeriv_eq_zero (h : IsExtrOn f s
 a) (h' : forallᶠ t : Real in 𝓝 0, a + t • b in s) : lineDeriv Real f a b = 0
· 使用定理 `IsMinOn.isExtr`：IsMinOn.isExtr (h : IsMinOn f s a) : IsExtrOn f s a
-/
theorem IsMinOn.lineDeriv_eq_zero (h : IsMinOn f s a) (h' : ∀ᶠ t : ℝ in 𝓝 0, a + t • b ∈ s) :
    lineDeriv ℝ f a b = 0 :=
  h.isExtr.lineDeriv_eq_zero h'
/-
**IsMaxOn.hasLineDerivAt_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMaxOn.hasLineDerivAt_eq_zero (h : IsMaxOn f s a) (hd : HasLineDerivAt Re
al f f' a b) (h' : forallᶠ t : Real in 𝓝 0, a + t • b in s) : f' = 0
参数：h : IsMaxOn f s a；hd : HasLineDerivAt Real f f' a b；h' : forallᶠ t : Real in 
𝓝 0, a + t • b in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsExtrOn.hasLineDerivAt_eq_zero`：IsExtrOn.hasLineDerivAt_eq_zero (h : Is
ExtrOn f s a) (hd : HasLineDerivAt Real f f' a b) (h' : forallᶠ t : Real in 𝓝 0,
 a + t • b in s) : f'…
· 使用定理 `IsMaxOn.isExtr`：IsMaxOn.isExtr (h : IsMaxOn f s a) : IsExtrOn f s a
-/
theorem IsMaxOn.hasLineDerivAt_eq_zero (h : IsMaxOn f s a) (hd : HasLineDerivAt ℝ f f' a b)
    (h' : ∀ᶠ t : ℝ in 𝓝 0, a + t • b ∈ s) : f' = 0 :=
  h.isExtr.hasLineDerivAt_eq_zero hd h'
/-
**IsMaxOn.lineDeriv_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMaxOn.lineDeriv_eq_zero (h : IsMaxOn f s a) (h' : forallᶠ t : Real in 𝓝 
0, a + t • b in s) : lineDeriv Real f a b = 0
参数：h : IsMaxOn f s a；h' : forallᶠ t : Real in 𝓝 0, a + t • b in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsExtrOn.lineDeriv_eq_zero`：IsExtrOn.lineDeriv_eq_zero (h : IsExtrOn f s
 a) (h' : forallᶠ t : Real in 𝓝 0, a + t • b in s) : lineDeriv Real f a b = 0
· 使用定理 `IsMaxOn.isExtr`：IsMaxOn.isExtr (h : IsMaxOn f s a) : IsExtrOn f s a
-/
theorem IsMaxOn.lineDeriv_eq_zero (h : IsMaxOn f s a) (h' : ∀ᶠ t : ℝ in 𝓝 0, a + t • b ∈ s) :
    lineDeriv ℝ f a b = 0 :=
  h.isExtr.lineDeriv_eq_zero h'
/-
**IsExtrOn.hasLineDerivWithinAt_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsExtrOn.hasLineDerivWithinAt_eq_zero (h : IsExtrOn f s a) (hd : HasLineDe
rivWithinAt Real f f' s a b) (h' : forallᶠ t : Real in 𝓝 0, a + t • b in s) : f'
 = 0
参数：h : IsExtrOn f s a；hd : HasLineDerivWithinAt Real f f' s a b；h' : forallᶠ t :
 Real in 𝓝 0, a + t • b in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsExtrOn.hasLineDerivAt_eq_zero`：IsExtrOn.hasLineDerivAt_eq_zero (h : Is
ExtrOn f s a) (hd : HasLineDerivAt Real f f' a b) (h' : forallᶠ t : Real in 𝓝 0,
 a + t • b in s) : f'…
· 使用定理 `HasLineDerivWithinAt.hasLineDerivAt'`：HasLineDerivWithinAt.hasLineDerivA
t' (h : HasLineDerivWithinAt 𝕜 f f' s x v) (hs : forallᶠ t : 𝕜 in 𝓝 0, x + t • v
 in s) : HasLineDerivAt 𝕜 …
-/
theorem IsExtrOn.hasLineDerivWithinAt_eq_zero (h : IsExtrOn f s a)
    (hd : HasLineDerivWithinAt ℝ f f' s a b) (h' : ∀ᶠ t : ℝ in 𝓝 0, a + t • b ∈ s) : f' = 0 :=
  h.hasLineDerivAt_eq_zero (hd.hasLineDerivAt' h') h'
/-
**IsExtrOn.lineDerivWithin_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsExtrOn.lineDerivWithin_eq_zero (h : IsExtrOn f s a) (h' : forallᶠ t : Re
al in 𝓝 0, a + t • b in s) : lineDerivWithin Real f s a b = 0
参数：h : IsExtrOn f s a；h' : forallᶠ t : Real in 𝓝 0, a + t • b in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsExtrOn.hasLineDerivWithinAt_eq_zero`：IsExtrOn.hasLineDerivWithinAt_eq_
zero (h : IsExtrOn f s a) (hd : HasLineDerivWithinAt Real f f' s a b) (h' : fora
llᶠ t : Real in 𝓝 0, a + t …
· 使用定理 `LineDifferentiableWithinAt.hasLineDerivWithinAt`：LineDifferentiableWithi
nAt.hasLineDerivWithinAt (h : LineDifferentiableWithinAt 𝕜 f s x v) : HasLineDer
ivWithinAt 𝕜 f (lineDerivWithin 𝕜 f s…
· 使用定理 `lineDerivWithin_zero_of_not_lineDifferentiableWithinAt`：lineDerivWithin_
zero_of_not_lineDifferentiableWithinAt (h : ¬LineDifferentiableWithinAt 𝕜 f s x 
v) : lineDerivWithin 𝕜 f s x v = 0
-/
theorem IsExtrOn.lineDerivWithin_eq_zero (h : IsExtrOn f s a)
    (h' : ∀ᶠ t : ℝ in 𝓝 0, a + t • b ∈ s) : lineDerivWithin ℝ f s a b = 0 := by
  classical
  exact if hd : LineDifferentiableWithinAt ℝ f s a b then
    h.hasLineDerivWithinAt_eq_zero hd.hasLineDerivWithinAt h'
  else
    lineDerivWithin_zero_of_not_lineDifferentiableWithinAt hd
/-
**IsMinOn.hasLineDerivWithinAt_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMinOn.hasLineDerivWithinAt_eq_zero (h : IsMinOn f s a) (hd : HasLineDeri
vWithinAt Real f f' s a b) (h' : forallᶠ t : Real in 𝓝 0, a + t • b in s) : f' =
 0
参数：h : IsMinOn f s a；hd : HasLineDerivWithinAt Real f f' s a b；h' : forallᶠ t : 
Real in 𝓝 0, a + t • b in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsExtrOn.hasLineDerivWithinAt_eq_zero`：IsExtrOn.hasLineDerivWithinAt_eq_
zero (h : IsExtrOn f s a) (hd : HasLineDerivWithinAt Real f f' s a b) (h' : fora
llᶠ t : Real in 𝓝 0, a + t …
· 使用定理 `IsMinOn.isExtr`：IsMinOn.isExtr (h : IsMinOn f s a) : IsExtrOn f s a
-/
theorem IsMinOn.hasLineDerivWithinAt_eq_zero (h : IsMinOn f s a)
    (hd : HasLineDerivWithinAt ℝ f f' s a b) (h' : ∀ᶠ t : ℝ in 𝓝 0, a + t • b ∈ s) : f' = 0 :=
  h.isExtr.hasLineDerivWithinAt_eq_zero hd h'
/-
**IsMinOn.lineDerivWithin_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMinOn.lineDerivWithin_eq_zero (h : IsMinOn f s a) (h' : forallᶠ t : Real
 in 𝓝 0, a + t • b in s) : lineDerivWithin Real f s a b = 0
参数：h : IsMinOn f s a；h' : forallᶠ t : Real in 𝓝 0, a + t • b in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsExtrOn.lineDerivWithin_eq_zero`：IsExtrOn.lineDerivWithin_eq_zero (h : 
IsExtrOn f s a) (h' : forallᶠ t : Real in 𝓝 0, a + t • b in s) : lineDerivWithin
 Real f s a b = 0
· 使用定理 `IsMinOn.isExtr`：IsMinOn.isExtr (h : IsMinOn f s a) : IsExtrOn f s a
-/
theorem IsMinOn.lineDerivWithin_eq_zero (h : IsMinOn f s a)
    (h' : ∀ᶠ t : ℝ in 𝓝 0, a + t • b ∈ s) : lineDerivWithin ℝ f s a b = 0 :=
  h.isExtr.lineDerivWithin_eq_zero h'
/-
**IsMaxOn.hasLineDerivWithinAt_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMaxOn.hasLineDerivWithinAt_eq_zero (h : IsMaxOn f s a) (hd : HasLineDeri
vWithinAt Real f f' s a b) (h' : forallᶠ t : Real in 𝓝 0, a + t • b in s) : f' =
 0
参数：h : IsMaxOn f s a；hd : HasLineDerivWithinAt Real f f' s a b；h' : forallᶠ t : 
Real in 𝓝 0, a + t • b in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsExtrOn.hasLineDerivWithinAt_eq_zero`：IsExtrOn.hasLineDerivWithinAt_eq_
zero (h : IsExtrOn f s a) (hd : HasLineDerivWithinAt Real f f' s a b) (h' : fora
llᶠ t : Real in 𝓝 0, a + t …
· 使用定理 `IsMaxOn.isExtr`：IsMaxOn.isExtr (h : IsMaxOn f s a) : IsExtrOn f s a
-/
theorem IsMaxOn.hasLineDerivWithinAt_eq_zero (h : IsMaxOn f s a)
    (hd : HasLineDerivWithinAt ℝ f f' s a b) (h' : ∀ᶠ t : ℝ in 𝓝 0, a + t • b ∈ s) : f' = 0 :=
  h.isExtr.hasLineDerivWithinAt_eq_zero hd h'
/-
**IsMaxOn.lineDerivWithin_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMaxOn.lineDerivWithin_eq_zero (h : IsMaxOn f s a) (h' : forallᶠ t : Real
 in 𝓝 0, a + t • b in s) : lineDerivWithin Real f s a b = 0
参数：h : IsMaxOn f s a；h' : forallᶠ t : Real in 𝓝 0, a + t • b in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsExtrOn.lineDerivWithin_eq_zero`：IsExtrOn.lineDerivWithin_eq_zero (h : 
IsExtrOn f s a) (h' : forallᶠ t : Real in 𝓝 0, a + t • b in s) : lineDerivWithin
 Real f s a b = 0
· 使用定理 `IsMaxOn.isExtr`：IsMaxOn.isExtr (h : IsMaxOn f s a) : IsExtrOn f s a
-/
theorem IsMaxOn.lineDerivWithin_eq_zero (h : IsMaxOn f s a)
    (h' : ∀ᶠ t : ℝ in 𝓝 0, a + t • b ∈ s) : lineDerivWithin ℝ f s a b = 0 :=
  h.isExtr.lineDerivWithin_eq_zero h'
end Module

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E]
  {f : E → ℝ} {s : Set E} {a b : E} {f' : ℝ}

/-
**IsLocalExtr.hasLineDerivAt_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalExtr.hasLineDerivAt_eq_zero (h : IsLocalExtr f a) (hd : HasLineDeri
vAt Real f f' a b) : f' = 0
参数：h : IsLocalExtr f a；hd : HasLineDerivAt Real f f' a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsExtrFilter.hasLineDerivAt_eq_zero`：IsExtrFilter.hasLineDerivAt_eq_zero
 {l : Filter E} (h : IsExtrFilter f l a) (hd : HasLineDerivAt Real f f' a b) (h'
 : Tendsto (fun t : Real …
· 使用定理 `Continuous.tendsto'`：Continuous.tendsto' (hf : Continuous f) (x : X) (y 
: Y) (h : f x = y) : Tendsto f (𝓝 x) (𝓝 y)
· 使用定理 `Continuous.const_add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst
_1 : Add M] [SeparatelyContinuousAdd M] {X : Type u_2}   [inst_3 : TopologicalSp
ace X] {f …
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `Continuous.fun_smul`：∀ {M : Type u_1} {X : Type u_2} {Y : Type u_3} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalSpa
ce Y] [in…
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsLocalExtr.hasLineDerivAt_eq_zero (h : IsLocalExtr f a) (hd : HasLineDerivAt ℝ f f' a b) :
    f' = 0 :=
  IsExtrFilter.hasLineDerivAt_eq_zero h hd <| Continuous.tendsto' (by fun_prop) _ _ (by simp)
/-
**IsLocalExtr.lineDeriv_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalExtr.lineDeriv_eq_zero (h : IsLocalExtr f a) : lineDeriv Real f a =
 0
参数：h : IsLocalExtr f a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsExtrFilter.lineDeriv_eq_zero`：IsExtrFilter.lineDeriv_eq_zero {l : Filt
er E} (h : IsExtrFilter f l a) (h' : Tendsto (fun t : Real => a + t • b) (𝓝 0) l
) : lineDeriv Real f…
· 使用定理 `Continuous.tendsto'`：Continuous.tendsto' (hf : Continuous f) (x : X) (y 
: Y) (h : f x = y) : Tendsto f (𝓝 x) (𝓝 y)
· 使用定理 `Continuous.const_add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst
_1 : Add M] [SeparatelyContinuousAdd M] {X : Type u_2}   [inst_3 : TopologicalSp
ace X] {f …
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `Continuous.fun_smul`：∀ {M : Type u_1} {X : Type u_2} {Y : Type u_3} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalSpa
ce Y] [in…
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsLocalExtr.lineDeriv_eq_zero (h : IsLocalExtr f a) : lineDeriv ℝ f a = 0 :=
  funext fun b ↦ IsExtrFilter.lineDeriv_eq_zero h <| Continuous.tendsto' (by fun_prop) _ _ (by simp)
/-
**IsLocalMin.hasLineDerivAt_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalMin.hasLineDerivAt_eq_zero (h : IsLocalMin f a) (hd : HasLineDerivA
t Real f f' a b) : f' = 0
参数：h : IsLocalMin f a；hd : HasLineDerivAt Real f f' a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalExtr.hasLineDerivAt_eq_zero`：IsLocalExtr.hasLineDerivAt_eq_zero (
h : IsLocalExtr f a) (hd : HasLineDerivAt Real f f' a b) : f' = 0
-/
theorem IsLocalMin.hasLineDerivAt_eq_zero (h : IsLocalMin f a) (hd : HasLineDerivAt ℝ f f' a b) :
    f' = 0 :=
  IsLocalExtr.hasLineDerivAt_eq_zero (.inl h) hd
/-
**IsLocalMin.lineDeriv_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalMin.lineDeriv_eq_zero (h : IsLocalMin f a) : lineDeriv Real f a = 0
参数：h : IsLocalMin f a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalExtr.lineDeriv_eq_zero`：IsLocalExtr.lineDeriv_eq_zero (h : IsLoca
lExtr f a) : lineDeriv Real f a = 0
-/
theorem IsLocalMin.lineDeriv_eq_zero (h : IsLocalMin f a) : lineDeriv ℝ f a = 0 :=
  IsLocalExtr.lineDeriv_eq_zero (.inl h)
/-
**IsLocalMax.hasLineDerivAt_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalMax.hasLineDerivAt_eq_zero (h : IsLocalMax f a) (hd : HasLineDerivA
t Real f f' a b) : f' = 0
参数：h : IsLocalMax f a；hd : HasLineDerivAt Real f f' a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalExtr.hasLineDerivAt_eq_zero`：IsLocalExtr.hasLineDerivAt_eq_zero (
h : IsLocalExtr f a) (hd : HasLineDerivAt Real f f' a b) : f' = 0
-/
theorem IsLocalMax.hasLineDerivAt_eq_zero (h : IsLocalMax f a) (hd : HasLineDerivAt ℝ f f' a b) :
    f' = 0 :=
  IsLocalExtr.hasLineDerivAt_eq_zero (.inr h) hd
/-
**IsLocalMax.lineDeriv_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalMax.lineDeriv_eq_zero (h : IsLocalMax f a) : lineDeriv Real f a = 0
参数：h : IsLocalMax f a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalExtr.lineDeriv_eq_zero`：IsLocalExtr.lineDeriv_eq_zero (h : IsLoca
lExtr f a) : lineDeriv Real f a = 0
-/
theorem IsLocalMax.lineDeriv_eq_zero (h : IsLocalMax f a) : lineDeriv ℝ f a = 0 :=
  IsLocalExtr.lineDeriv_eq_zero (.inr h)
