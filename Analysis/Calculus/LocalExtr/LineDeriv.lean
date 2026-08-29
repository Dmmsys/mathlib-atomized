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

variable {E : Type*} [AddCommGroup E] [Module Real E] {f : E -> Real} {s : Set E} {a b : E} {f' : Real}

/--
theorem `IsExtrFilter.hasLineDerivAt_eq_zero` / 定理 `IsExtrFilter.hasLineDerivAt_eq_zero`

English:
theorem IsExtrFilter.hasLineDerivAt_eq_zero
  statement: {l : Filter E} (h : IsExtrFilter f l a)
  proof: IsLocalExtr.hasDerivAt_eq_zero (IsExtrFilter.comp_tendsto (by simpa using h) h') hd

中文:
定理 IsExtrFilter.hasLineDerivAt_eq_zero
  结论: {l : 滤子 E} (h : IsExtrFilter f l a)
  证明: IsLocalExtr.hasDerivAt_eq_zero (IsExtrFilter.comp_tendsto (by simpa using h) h') hd

Depends on / 依赖: IsExtrFilter, IsExtrFilter.comp_tendsto, IsLocalExtr, IsLocalExtr.hasDerivAt_eq_zero, comp_tendsto, hasDerivAt_eq_zero
-/
theorem IsExtrFilter.hasLineDerivAt_eq_zero {l : Filter E} (h : IsExtrFilter f l a)
    (hd : HasLineDerivAt Real f f' a b) (h' : Tendsto (fun t : Real => a + t • b) (𝓝 0) l) : f' = 0 :=
  IsLocalExtr.hasDerivAt_eq_zero (IsExtrFilter.comp_tendsto (by simpa using h) h') hd

/--
theorem `IsExtrFilter.lineDeriv_eq_zero` / 定理 `IsExtrFilter.lineDeriv_eq_zero`

English:
theorem IsExtrFilter.lineDeriv_eq_zero
  statement: {l : Filter E} (h : IsExtrFilter f l a)
  proof: by
  classical
  exact if hd : LineDifferentiableAt Real f a b then
    h.hasLineDerivAt_eq_zero hd.hasLineDerivAt h'
  else
    lineDeriv_zero_of_not_lineDifferentiableAt hd

中文:
定理 IsExtrFilter.lineDeriv_eq_zero
  结论: {l : 滤子 E} (h : IsExtrFilter f l a)
  证明: by
  classical
  exact if hd : LineDifferentiableAt Real f a b then
    h.hasLineDerivAt_eq_zero hd.hasLineDerivAt h'
  else
    lineDeriv_zero_of_not_lineDifferentiableAt hd

Depends on / 依赖: LineDifferentiableAt, classical, h.hasLineDerivAt_eq_zero, hasLineDerivAt, hasLineDerivAt_eq_zero, hd.hasLineDerivAt, lineDeriv_zero_of_not_lineDifferentiableAt
-/
theorem IsExtrFilter.lineDeriv_eq_zero {l : Filter E} (h : IsExtrFilter f l a)
    (h' : Tendsto (fun t : Real => a + t • b) (𝓝 0) l) : lineDeriv Real f a b = 0 := by
  classical
  exact if hd : LineDifferentiableAt Real f a b then
    h.hasLineDerivAt_eq_zero hd.hasLineDerivAt h'
  else
    lineDeriv_zero_of_not_lineDifferentiableAt hd

/--
theorem `IsExtrOn.hasLineDerivAt_eq_zero` / 定理 `IsExtrOn.hasLineDerivAt_eq_zero`

English:
theorem IsExtrOn.hasLineDerivAt_eq_zero
  statement: (h : IsExtrOn f s a) (hd : HasLineDerivAt Real f f' a b)
  proof: IsExtrFilter.hasLineDerivAt_eq_zero h hd tendsto_principal.2 h'

中文:
定理 IsExtrOn.hasLineDerivAt_eq_zero
  结论: (h : IsExtrOn f s a) (hd : HasLineDerivAt 实数 f f' a b)
  证明: IsExtrFilter.hasLineDerivAt_eq_zero h hd tendsto_principal.2 h'

Depends on / 依赖: IsExtrFilter, IsExtrFilter.hasLineDerivAt_eq_zero, hasLineDerivAt_eq_zero, tendsto_principal
-/
theorem IsExtrOn.hasLineDerivAt_eq_zero (h : IsExtrOn f s a) (hd : HasLineDerivAt Real f f' a b)
    (h' : forallᶠ t : Real in 𝓝 0, a + t • b in s) : f' = 0 :=
IsExtrFilter.hasLineDerivAt_eq_zero h hd tendsto_principal.2 h'

/--
theorem `IsExtrOn.lineDeriv_eq_zero` / 定理 `IsExtrOn.lineDeriv_eq_zero`

English:
theorem IsExtrOn.lineDeriv_eq_zero
  given: (h : IsExtrOn f s a) (h' : forallᶠ t : Real in 𝓝 0, a + t • b in s)
  proof: IsExtrFilter.lineDeriv_eq_zero h tendsto_principal.2 h'

中文:
定理 IsExtrOn.lineDeriv_eq_zero
  条件: (h : IsExtrOn f s a) (h' : 对任意ᶠ t : 实数 in 𝓝 0, a + t • b in s)
  证明: IsExtrFilter.lineDeriv_eq_zero h tendsto_principal.2 h'

Depends on / 依赖: IsExtrFilter, IsExtrFilter.lineDeriv_eq_zero, lineDeriv_eq_zero, tendsto_principal
-/
theorem IsExtrOn.lineDeriv_eq_zero (h : IsExtrOn f s a) (h' : forallᶠ t : Real in 𝓝 0, a + t • b in s) :
    lineDeriv Real f a b = 0 :=
IsExtrFilter.lineDeriv_eq_zero h tendsto_principal.2 h'

/--
theorem `IsMinOn.hasLineDerivAt_eq_zero` / 定理 `IsMinOn.hasLineDerivAt_eq_zero`

English:
theorem IsMinOn.hasLineDerivAt_eq_zero
  statement: (h : IsMinOn f s a) (hd : HasLineDerivAt Real f f' a b)
  proof: h.isExtr.hasLineDerivAt_eq_zero hd h'

中文:
定理 IsMinOn.hasLineDerivAt_eq_zero
  结论: (h : IsMinOn f s a) (hd : HasLineDerivAt 实数 f f' a b)
  证明: h.isExtr.hasLineDerivAt_eq_zero hd h'

Depends on / 依赖: h.isExtr.hasLineDerivAt_eq_zero, hasLineDerivAt_eq_zero, isExtr
-/
theorem IsMinOn.hasLineDerivAt_eq_zero (h : IsMinOn f s a) (hd : HasLineDerivAt Real f f' a b)
    (h' : forallᶠ t : Real in 𝓝 0, a + t • b in s) : f' = 0 :=
  h.isExtr.hasLineDerivAt_eq_zero hd h'

/--
theorem `IsMinOn.lineDeriv_eq_zero` / 定理 `IsMinOn.lineDeriv_eq_zero`

English:
theorem IsMinOn.lineDeriv_eq_zero
  given: (h : IsMinOn f s a) (h' : forallᶠ t : Real in 𝓝 0, a + t • b in s)
  proof: h.isExtr.lineDeriv_eq_zero h'

中文:
定理 IsMinOn.lineDeriv_eq_zero
  条件: (h : IsMinOn f s a) (h' : 对任意ᶠ t : 实数 in 𝓝 0, a + t • b in s)
  证明: h.isExtr.lineDeriv_eq_zero h'

Depends on / 依赖: h.isExtr.lineDeriv_eq_zero, isExtr, lineDeriv_eq_zero
-/
theorem IsMinOn.lineDeriv_eq_zero (h : IsMinOn f s a) (h' : forallᶠ t : Real in 𝓝 0, a + t • b in s) :
    lineDeriv Real f a b = 0 :=
  h.isExtr.lineDeriv_eq_zero h'

/--
theorem `IsMaxOn.hasLineDerivAt_eq_zero` / 定理 `IsMaxOn.hasLineDerivAt_eq_zero`

English:
theorem IsMaxOn.hasLineDerivAt_eq_zero
  statement: (h : IsMaxOn f s a) (hd : HasLineDerivAt Real f f' a b)
  proof: h.isExtr.hasLineDerivAt_eq_zero hd h'

中文:
定理 IsMaxOn.hasLineDerivAt_eq_zero
  结论: (h : IsMaxOn f s a) (hd : HasLineDerivAt 实数 f f' a b)
  证明: h.isExtr.hasLineDerivAt_eq_zero hd h'

Depends on / 依赖: h.isExtr.hasLineDerivAt_eq_zero, hasLineDerivAt_eq_zero, isExtr
-/
theorem IsMaxOn.hasLineDerivAt_eq_zero (h : IsMaxOn f s a) (hd : HasLineDerivAt Real f f' a b)
    (h' : forallᶠ t : Real in 𝓝 0, a + t • b in s) : f' = 0 :=
  h.isExtr.hasLineDerivAt_eq_zero hd h'

/--
theorem `IsMaxOn.lineDeriv_eq_zero` / 定理 `IsMaxOn.lineDeriv_eq_zero`

English:
theorem IsMaxOn.lineDeriv_eq_zero
  given: (h : IsMaxOn f s a) (h' : forallᶠ t : Real in 𝓝 0, a + t • b in s)
  proof: h.isExtr.lineDeriv_eq_zero h'

中文:
定理 IsMaxOn.lineDeriv_eq_zero
  条件: (h : IsMaxOn f s a) (h' : 对任意ᶠ t : 实数 in 𝓝 0, a + t • b in s)
  证明: h.isExtr.lineDeriv_eq_zero h'

Depends on / 依赖: h.isExtr.lineDeriv_eq_zero, isExtr, lineDeriv_eq_zero
-/
theorem IsMaxOn.lineDeriv_eq_zero (h : IsMaxOn f s a) (h' : forallᶠ t : Real in 𝓝 0, a + t • b in s) :
    lineDeriv Real f a b = 0 :=
  h.isExtr.lineDeriv_eq_zero h'

/--
theorem `IsExtrOn.hasLineDerivWithinAt_eq_zero` / 定理 `IsExtrOn.hasLineDerivWithinAt_eq_zero`

English:
theorem IsExtrOn.hasLineDerivWithinAt_eq_zero
  statement: (h : IsExtrOn f s a)
  proof: h.hasLineDerivAt_eq_zero (hd.hasLineDerivAt' h') h'

中文:
定理 IsExtrOn.hasLineDerivWithinAt_eq_zero
  结论: (h : IsExtrOn f s a)
  证明: h.hasLineDerivAt_eq_zero (hd.hasLineDerivAt' h') h'

Depends on / 依赖: h.hasLineDerivAt_eq_zero, hasLineDerivAt, hasLineDerivAt_eq_zero, hd.hasLineDerivAt
-/
theorem IsExtrOn.hasLineDerivWithinAt_eq_zero (h : IsExtrOn f s a)
    (hd : HasLineDerivWithinAt Real f f' s a b) (h' : forallᶠ t : Real in 𝓝 0, a + t • b in s) : f' = 0 :=
  h.hasLineDerivAt_eq_zero (hd.hasLineDerivAt' h') h'

/--
theorem `IsExtrOn.lineDerivWithin_eq_zero` / 定理 `IsExtrOn.lineDerivWithin_eq_zero`

English:
theorem IsExtrOn.lineDerivWithin_eq_zero
  statement: (h : IsExtrOn f s a)
  proof: by
  classical
  exact if hd : LineDifferentiableWithinAt Real f s a b then
    h.hasLineDerivWithinAt_eq_zero hd.hasLineDerivWithinAt h'
  else
    lineDerivWithin_zero_of_not_lineDifferentiableWithinAt hd

中文:
定理 IsExtrOn.lineDerivWithin_eq_zero
  结论: (h : IsExtrOn f s a)
  证明: by
  classical
  exact if hd : LineDifferentiableWithinAt Real f s a b then
    h.hasLineDerivWithinAt_eq_zero hd.hasLineDerivWithinAt h'
  else
    lineDerivWithin_zero_of_not_lineDifferentiableWithinAt hd

Depends on / 依赖: LineDifferentiableWithinAt, classical, h.hasLineDerivWithinAt_eq_zero, hasLineDerivWithinAt, hasLineDerivWithinAt_eq_zero, hd.hasLineDerivWithinAt, lineDerivWithin_zero_of_not_lineDifferentiableWithinAt
-/
theorem IsExtrOn.lineDerivWithin_eq_zero (h : IsExtrOn f s a)
    (h' : forallᶠ t : Real in 𝓝 0, a + t • b in s) : lineDerivWithin Real f s a b = 0 := by
  classical
  exact if hd : LineDifferentiableWithinAt Real f s a b then
    h.hasLineDerivWithinAt_eq_zero hd.hasLineDerivWithinAt h'
  else
    lineDerivWithin_zero_of_not_lineDifferentiableWithinAt hd

/--
theorem `IsMinOn.hasLineDerivWithinAt_eq_zero` / 定理 `IsMinOn.hasLineDerivWithinAt_eq_zero`

English:
theorem IsMinOn.hasLineDerivWithinAt_eq_zero
  statement: (h : IsMinOn f s a)
  proof: h.isExtr.hasLineDerivWithinAt_eq_zero hd h'

中文:
定理 IsMinOn.hasLineDerivWithinAt_eq_zero
  结论: (h : IsMinOn f s a)
  证明: h.isExtr.hasLineDerivWithinAt_eq_zero hd h'

Depends on / 依赖: h.isExtr.hasLineDerivWithinAt_eq_zero, hasLineDerivWithinAt_eq_zero, isExtr
-/
theorem IsMinOn.hasLineDerivWithinAt_eq_zero (h : IsMinOn f s a)
    (hd : HasLineDerivWithinAt Real f f' s a b) (h' : forallᶠ t : Real in 𝓝 0, a + t • b in s) : f' = 0 :=
  h.isExtr.hasLineDerivWithinAt_eq_zero hd h'

/--
theorem `IsMinOn.lineDerivWithin_eq_zero` / 定理 `IsMinOn.lineDerivWithin_eq_zero`

English:
theorem IsMinOn.lineDerivWithin_eq_zero
  statement: (h : IsMinOn f s a)
  proof: h.isExtr.lineDerivWithin_eq_zero h'

中文:
定理 IsMinOn.lineDerivWithin_eq_zero
  结论: (h : IsMinOn f s a)
  证明: h.isExtr.lineDerivWithin_eq_zero h'

Depends on / 依赖: h.isExtr.lineDerivWithin_eq_zero, isExtr, lineDerivWithin_eq_zero
-/
theorem IsMinOn.lineDerivWithin_eq_zero (h : IsMinOn f s a)
    (h' : forallᶠ t : Real in 𝓝 0, a + t • b in s) : lineDerivWithin Real f s a b = 0 :=
  h.isExtr.lineDerivWithin_eq_zero h'

/--
theorem `IsMaxOn.hasLineDerivWithinAt_eq_zero` / 定理 `IsMaxOn.hasLineDerivWithinAt_eq_zero`

English:
theorem IsMaxOn.hasLineDerivWithinAt_eq_zero
  statement: (h : IsMaxOn f s a)
  proof: h.isExtr.hasLineDerivWithinAt_eq_zero hd h'

中文:
定理 IsMaxOn.hasLineDerivWithinAt_eq_zero
  结论: (h : IsMaxOn f s a)
  证明: h.isExtr.hasLineDerivWithinAt_eq_zero hd h'

Depends on / 依赖: h.isExtr.hasLineDerivWithinAt_eq_zero, hasLineDerivWithinAt_eq_zero, isExtr
-/
theorem IsMaxOn.hasLineDerivWithinAt_eq_zero (h : IsMaxOn f s a)
    (hd : HasLineDerivWithinAt Real f f' s a b) (h' : forallᶠ t : Real in 𝓝 0, a + t • b in s) : f' = 0 :=
  h.isExtr.hasLineDerivWithinAt_eq_zero hd h'

/--
theorem `IsMaxOn.lineDerivWithin_eq_zero` / 定理 `IsMaxOn.lineDerivWithin_eq_zero`

English:
theorem IsMaxOn.lineDerivWithin_eq_zero
  statement: (h : IsMaxOn f s a)
  proof: h.isExtr.lineDerivWithin_eq_zero h'

中文:
定理 IsMaxOn.lineDerivWithin_eq_zero
  结论: (h : IsMaxOn f s a)
  证明: h.isExtr.lineDerivWithin_eq_zero h'

Depends on / 依赖: h.isExtr.lineDerivWithin_eq_zero, isExtr, lineDerivWithin_eq_zero
-/
theorem IsMaxOn.lineDerivWithin_eq_zero (h : IsMaxOn f s a)
    (h' : forallᶠ t : Real in 𝓝 0, a + t • b in s) : lineDerivWithin Real f s a b = 0 :=
  h.isExtr.lineDerivWithin_eq_zero h'
end Module

variable {E : Type*} [AddCommGroup E] [Module Real E]
  [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul Real E]
  {f : E -> Real} {s : Set E} {a b : E} {f' : Real}

/--
theorem `IsLocalExtr.hasLineDerivAt_eq_zero` / 定理 `IsLocalExtr.hasLineDerivAt_eq_zero`

English:
theorem IsLocalExtr.hasLineDerivAt_eq_zero
  given: (h : IsLocalExtr f a) (hd : HasLineDerivAt Real f f' a b)
  proof: IsExtrFilter.hasLineDerivAt_eq_zero h hd Continuous.tendsto' (by fun_prop) _ _ (by simp)

中文:
定理 IsLocalExtr.hasLineDerivAt_eq_zero
  条件: (h : IsLocalExtr f a) (hd : HasLineDerivAt 实数 f f' a b)
  证明: IsExtrFilter.hasLineDerivAt_eq_zero h hd Continuous.tendsto' (by fun_prop) _ _ (by simp)

Depends on / 依赖: Continuous, Continuous.tendsto, IsExtrFilter, IsExtrFilter.hasLineDerivAt_eq_zero, fun_prop, hasLineDerivAt_eq_zero, tendsto
-/
theorem IsLocalExtr.hasLineDerivAt_eq_zero (h : IsLocalExtr f a) (hd : HasLineDerivAt Real f f' a b) :
    f' = 0 :=
IsExtrFilter.hasLineDerivAt_eq_zero h hd Continuous.tendsto' (by fun_prop) _ _ (by simp)

/--
theorem `IsLocalExtr.lineDeriv_eq_zero` / 定理 `IsLocalExtr.lineDeriv_eq_zero`

English:
theorem IsLocalExtr.lineDeriv_eq_zero
  given: (h : IsLocalExtr f a)
  statement: lineDeriv Real f a = 0
  proof: funext fun b => IsExtrFilter.lineDeriv_eq_zero h Continuous.tendsto' (by fun_prop) _ _ (by simp)

中文:
定理 IsLocalExtr.lineDeriv_eq_zero
  条件: (h : IsLocalExtr f a)
  结论: lineDeriv 实数 f a = 0
  证明: funext fun b => IsExtrFilter.lineDeriv_eq_zero h Continuous.tendsto' (by fun_prop) _ _ (by simp)

Depends on / 依赖: Continuous, Continuous.tendsto, IsExtrFilter, IsExtrFilter.lineDeriv_eq_zero, fun_prop, lineDeriv_eq_zero, tendsto
-/
theorem IsLocalExtr.lineDeriv_eq_zero (h : IsLocalExtr f a) : lineDeriv Real f a = 0 :=
funext fun b => IsExtrFilter.lineDeriv_eq_zero h Continuous.tendsto' (by fun_prop) _ _ (by simp)

/--
theorem `IsLocalMin.hasLineDerivAt_eq_zero` / 定理 `IsLocalMin.hasLineDerivAt_eq_zero`

English:
theorem IsLocalMin.hasLineDerivAt_eq_zero
  given: (h : IsLocalMin f a) (hd : HasLineDerivAt Real f f' a b)
  proof: IsLocalExtr.hasLineDerivAt_eq_zero (.inl h) hd

中文:
定理 IsLocalMin.hasLineDerivAt_eq_zero
  条件: (h : IsLocalMin f a) (hd : HasLineDerivAt 实数 f f' a b)
  证明: IsLocalExtr.hasLineDerivAt_eq_zero (.inl h) hd

Depends on / 依赖: IsLocalExtr, IsLocalExtr.hasLineDerivAt_eq_zero, hasLineDerivAt_eq_zero
-/
theorem IsLocalMin.hasLineDerivAt_eq_zero (h : IsLocalMin f a) (hd : HasLineDerivAt Real f f' a b) :
    f' = 0 :=
  IsLocalExtr.hasLineDerivAt_eq_zero (.inl h) hd

/--
theorem `IsLocalMin.lineDeriv_eq_zero` / 定理 `IsLocalMin.lineDeriv_eq_zero`

English:
theorem IsLocalMin.lineDeriv_eq_zero
  given: (h : IsLocalMin f a)
  statement: lineDeriv Real f a = 0
  proof: IsLocalExtr.lineDeriv_eq_zero (.inl h)

中文:
定理 IsLocalMin.lineDeriv_eq_zero
  条件: (h : IsLocalMin f a)
  结论: lineDeriv 实数 f a = 0
  证明: IsLocalExtr.lineDeriv_eq_zero (.inl h)

Depends on / 依赖: IsLocalExtr, IsLocalExtr.lineDeriv_eq_zero, lineDeriv_eq_zero
-/
theorem IsLocalMin.lineDeriv_eq_zero (h : IsLocalMin f a) : lineDeriv Real f a = 0 :=
  IsLocalExtr.lineDeriv_eq_zero (.inl h)

/--
theorem `IsLocalMax.hasLineDerivAt_eq_zero` / 定理 `IsLocalMax.hasLineDerivAt_eq_zero`

English:
theorem IsLocalMax.hasLineDerivAt_eq_zero
  given: (h : IsLocalMax f a) (hd : HasLineDerivAt Real f f' a b)
  proof: IsLocalExtr.hasLineDerivAt_eq_zero (.inr h) hd

中文:
定理 IsLocalMax.hasLineDerivAt_eq_zero
  条件: (h : IsLocalMax f a) (hd : HasLineDerivAt 实数 f f' a b)
  证明: IsLocalExtr.hasLineDerivAt_eq_zero (.inr h) hd

Depends on / 依赖: IsLocalExtr, IsLocalExtr.hasLineDerivAt_eq_zero, hasLineDerivAt_eq_zero
-/
theorem IsLocalMax.hasLineDerivAt_eq_zero (h : IsLocalMax f a) (hd : HasLineDerivAt Real f f' a b) :
    f' = 0 :=
  IsLocalExtr.hasLineDerivAt_eq_zero (.inr h) hd

/--
theorem `IsLocalMax.lineDeriv_eq_zero` / 定理 `IsLocalMax.lineDeriv_eq_zero`

English:
theorem IsLocalMax.lineDeriv_eq_zero
  given: (h : IsLocalMax f a)
  statement: lineDeriv Real f a = 0
  proof: IsLocalExtr.lineDeriv_eq_zero (.inr h)

中文:
定理 IsLocalMax.lineDeriv_eq_zero
  条件: (h : IsLocalMax f a)
  结论: lineDeriv 实数 f a = 0
  证明: IsLocalExtr.lineDeriv_eq_zero (.inr h)

Depends on / 依赖: IsLocalExtr, IsLocalExtr.lineDeriv_eq_zero, lineDeriv_eq_zero
-/
theorem IsLocalMax.lineDeriv_eq_zero (h : IsLocalMax f a) : lineDeriv Real f a = 0 :=
  IsLocalExtr.lineDeriv_eq_zero (.inr h)
