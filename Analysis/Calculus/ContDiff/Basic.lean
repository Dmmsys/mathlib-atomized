/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Affine

/-!
# Basic properties of continuously-differentiable functions

This file continues the development of the API for `ContDiff`, `ContDiffAt`, etc, covering
constants, products, composition with linear maps, etc.

## Tags

derivative, differentiability, higher derivative, `C^n`, multilinear, Taylor series, formal series
-/

public noncomputable section

open Set Fin Filter Function

open scoped Topology ContDiff

attribute [local instance 1001] NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {s t : Set E} {f : E -> F} {x : E} {b : E × F -> G} {m n : Nat∞ω}
  {p : E -> FormalMultilinearSeries 𝕜 E F}

/-! ### Constants -/
section constants

/--
theorem `iteratedFDerivWithin_succ_const` / 定理 `iteratedFDerivWithin_succ_const`

English:
theorem iteratedFDerivWithin_succ_const
  given: (n : Nat) (c : F)
  proof: by
  induction n with
  | zero =>
    ext1
    simp [iteratedFDerivWithin_succ_eq_comp_left, iteratedFDerivWithin_zero_eq_comp, comp_def]
  | succ n IH =>
    rw [iteratedFDerivWithin_succ_eq_comp_left]; rw [IH]
    simp only [Pi.zero_def, comp_def, fderivWithin_fun_const, map_zero]

@[simp]

中文:
定理 iteratedFDerivWithin_succ_const
  条件: (n : 自然数) (c : F)
  证明: by
  induction n with
  | zero =>
    ext1
    simp [iteratedFDerivWithin_succ_eq_comp_left, iteratedFDerivWithin_zero_eq_comp, comp_def]
  | succ n IH =>
    rw [iteratedFDerivWithin_succ_eq_comp_left]; rw [IH]
    simp only [Pi.zero_def, comp_def, fderivWithin_fun_const, map_zero]

@[simp]

Depends on / 依赖: Pi.zero_def, comp_def, fderivWithin_fun_const, iteratedFDerivWithin_succ_eq_comp_left, iteratedFDerivWithin_zero_eq_comp, map_zero, zero_def
-/
theorem iteratedFDerivWithin_succ_const (n : Nat) (c : F) :
    iteratedFDerivWithin 𝕜 (n + 1) (fun _ : E => c) s = 0 := by
  induction n with
  | zero =>
    ext1
    simp [iteratedFDerivWithin_succ_eq_comp_left, iteratedFDerivWithin_zero_eq_comp, comp_def]
  | succ n IH =>
    rw [iteratedFDerivWithin_succ_eq_comp_left]; rw [IH]
    simp only [Pi.zero_def, comp_def, fderivWithin_fun_const, map_zero]

@[simp]
/--
theorem `iteratedFDerivWithin_zero` / 定理 `iteratedFDerivWithin_zero`

English:
theorem iteratedFDerivWithin_zero
  given: {i : Nat}
  proof: by
  cases i with
  | zero => ext; simp
  | succ i => apply iteratedFDerivWithin_succ_const

@[simp]

中文:
定理 iteratedFDerivWithin_zero
  条件: {i : 自然数}
  证明: by
  cases i with
  | zero => ext; simp
  | succ i => apply iteratedFDerivWithin_succ_const

@[simp]

Depends on / 依赖: iteratedFDerivWithin_succ_const
-/
theorem iteratedFDerivWithin_zero {i : Nat} :
    iteratedFDerivWithin 𝕜 i (0 : E -> F) s = 0 := by
  cases i with
  | zero => ext; simp
  | succ i => apply iteratedFDerivWithin_succ_const

@[simp]
/--
theorem `iteratedFDerivWithin_fun_zero` / 定理 `iteratedFDerivWithin_fun_zero`

English:
theorem iteratedFDerivWithin_fun_zero
  given: {i : Nat}
  proof: by
  apply iteratedFDerivWithin_zero

@[deprecated (since := "2026-03-18")]
alias iteratedFDerivWithin_zero_fun := iteratedFDerivWithin_fun_zero

@[simp]

中文:
定理 iteratedFDerivWithin_fun_zero
  条件: {i : 自然数}
  证明: by
  apply iteratedFDerivWithin_zero

@[deprecated (since := "2026-03-18")]
alias iteratedFDerivWithin_zero_fun := iteratedFDerivWithin_fun_zero

@[simp]

Depends on / 依赖: iteratedFDerivWithin_zero
-/
theorem iteratedFDerivWithin_fun_zero {i : Nat} :
    iteratedFDerivWithin 𝕜 i (fun (_ : E) => (0 : F)) s = 0 := by
  apply iteratedFDerivWithin_zero

@[deprecated (since := "2026-03-18")]
alias iteratedFDerivWithin_zero_fun := iteratedFDerivWithin_fun_zero

@[simp]
/--
theorem `ftaylorSeriesWithin_zero` / 定理 `ftaylorSeriesWithin_zero`

English:
theorem ftaylorSeriesWithin_zero
  proof: by
  ext
  simp [ftaylorSeriesWithin]

@[simp]

中文:
定理 ftaylorSeriesWithin_zero
  证明: by
  ext
  simp [ftaylorSeriesWithin]

@[simp]

Depends on / 依赖: ftaylorSeriesWithin
-/
theorem ftaylorSeriesWithin_zero :
    ftaylorSeriesWithin 𝕜 (0 : E -> F) = 0 := by
  ext
  simp [ftaylorSeriesWithin]

@[simp]
/--
theorem `ftaylorSeriesWithin_fun_zero` / 定理 `ftaylorSeriesWithin_fun_zero`

English:
theorem ftaylorSeriesWithin_fun_zero
  proof: by
  apply ftaylorSeriesWithin_zero

@[simp]

中文:
定理 ftaylorSeriesWithin_fun_zero
  证明: by
  apply ftaylorSeriesWithin_zero

@[simp]

Depends on / 依赖: ftaylorSeriesWithin_zero
-/
theorem ftaylorSeriesWithin_fun_zero :
    ftaylorSeriesWithin 𝕜 (fun (_ : E) => (0 : F)) = 0 := by
  apply ftaylorSeriesWithin_zero

@[simp]
/--
theorem `iteratedFDeriv_zero` / 定理 `iteratedFDeriv_zero`

English:
theorem iteratedFDeriv_zero
  given: {n : Nat}
  proof: funext fun x => by simp only [← iteratedFDerivWithin_univ, iteratedFDerivWithin_zero]

@[simp]

中文:
定理 iteratedFDeriv_zero
  条件: {n : 自然数}
  证明: funext fun x => by simp only [← iteratedFDerivWithin_univ, iteratedFDerivWithin_zero]

@[simp]

Depends on / 依赖: iteratedFDerivWithin_univ, iteratedFDerivWithin_zero
-/
theorem iteratedFDeriv_zero {n : Nat} :
    iteratedFDeriv 𝕜 n (0 : E -> F) = 0 :=
  funext fun x => by simp only [← iteratedFDerivWithin_univ, iteratedFDerivWithin_zero]

@[simp]
/--
theorem `iteratedFDeriv_fun_zero` / 定理 `iteratedFDeriv_fun_zero`

English:
theorem iteratedFDeriv_fun_zero
  given: {n : Nat}
  proof: by
  apply iteratedFDeriv_zero

@[deprecated (since := "2026-03-18")] alias iteratedFDeriv_zero_fun := iteratedFDeriv_fun_zero

@[simp]

中文:
定理 iteratedFDeriv_fun_zero
  条件: {n : 自然数}
  证明: by
  apply iteratedFDeriv_zero

@[deprecated (since := "2026-03-18")] alias iteratedFDeriv_zero_fun := iteratedFDeriv_fun_zero

@[simp]

Depends on / 依赖: iteratedFDeriv_zero
-/
theorem iteratedFDeriv_fun_zero {n : Nat} :
    iteratedFDeriv 𝕜 n (fun (_ : E) => (0 : F)) = 0 := by
  apply iteratedFDeriv_zero

@[deprecated (since := "2026-03-18")] alias iteratedFDeriv_zero_fun := iteratedFDeriv_fun_zero

@[simp]
/--
theorem `ftaylorSeries_zero` / 定理 `ftaylorSeries_zero`

English:
theorem ftaylorSeries_zero
  proof: by
  ext
  simp [ftaylorSeries]

@[simp]

中文:
定理 ftaylorSeries_zero
  证明: by
  ext
  simp [ftaylorSeries]

@[simp]

Depends on / 依赖: ftaylorSeries
-/
theorem ftaylorSeries_zero :
    ftaylorSeries 𝕜 (0 : E -> F) = 0 := by
  ext
  simp [ftaylorSeries]

@[simp]
/--
theorem `ftaylorSeries_fun_zero` / 定理 `ftaylorSeries_fun_zero`

English:
theorem ftaylorSeries_fun_zero
  proof: by
  ext
  simp [ftaylorSeries]

中文:
定理 ftaylorSeries_fun_zero
  证明: by
  ext
  simp [ftaylorSeries]

Depends on / 依赖: ftaylorSeries
-/
theorem ftaylorSeries_fun_zero :
    ftaylorSeries 𝕜 (fun (_ : E) => (0 : F)) = 0 := by
  ext
  simp [ftaylorSeries]

/--
theorem `contDiff_zero_fun` / 定理 `contDiff_zero_fun`

English:
theorem contDiff_zero_fun
  statement: ContDiff 𝕜 n fun _ : E => (0 : F)
  proof: analyticOnNhd_const.contDiff

中文:
定理 contDiff_zero_fun
  结论: 连续可微 𝕜 n fun _ : E => (0 : F)
  证明: analyticOnNhd_const.contDiff

Depends on / 依赖: analyticOnNhd_const, analyticOnNhd_const.contDiff, contDiff
-/
theorem contDiff_zero_fun : ContDiff 𝕜 n fun _ : E => (0 : F) :=
  analyticOnNhd_const.contDiff

/-- Constants are `C^∞`. -/
@[fun_prop]
/--
theorem `contDiff_const` / 定理 `contDiff_const`

English:
theorem contDiff_const
  given: {c : F}
  statement: ContDiff 𝕜 n fun _ : E => c
  proof: analyticOnNhd_const.contDiff

@[fun_prop]

中文:
定理 contDiff_const
  条件: {c : F}
  结论: 连续可微 𝕜 n fun _ : E => c
  证明: analyticOnNhd_const.contDiff

@[fun_prop]

Depends on / 依赖: analyticOnNhd_const, analyticOnNhd_const.contDiff, contDiff
-/
theorem contDiff_const {c : F} : ContDiff 𝕜 n fun _ : E => c :=
  analyticOnNhd_const.contDiff

@[fun_prop]
/--
theorem `contDiffOn_const` / 定理 `contDiffOn_const`

English:
theorem contDiffOn_const
  given: {c : F} {s : Set E}
  statement: ContDiffOn 𝕜 n (fun _ : E => c) s
  proof: contDiff_const.contDiffOn

@[fun_prop]

中文:
定理 contDiffOn_const
  条件: {c : F} {s : 集合 E}
  结论: ContDiffOn 𝕜 n (fun _ : E => c) s
  证明: contDiff_const.contDiffOn

@[fun_prop]

Depends on / 依赖: contDiffOn, contDiff_const, contDiff_const.contDiffOn
-/
theorem contDiffOn_const {c : F} {s : Set E} : ContDiffOn 𝕜 n (fun _ : E => c) s :=
  contDiff_const.contDiffOn

@[fun_prop]
/--
theorem `contDiffAt_const` / 定理 `contDiffAt_const`

English:
theorem contDiffAt_const
  given: {c : F}
  statement: ContDiffAt 𝕜 n (fun _ : E => c) x
  proof: contDiff_const.contDiffAt

@[fun_prop]

中文:
定理 contDiffAt_const
  条件: {c : F}
  结论: ContDiffAt 𝕜 n (fun _ : E => c) x
  证明: contDiff_const.contDiffAt

@[fun_prop]

Depends on / 依赖: contDiffAt, contDiff_const, contDiff_const.contDiffAt
-/
theorem contDiffAt_const {c : F} : ContDiffAt 𝕜 n (fun _ : E => c) x :=
  contDiff_const.contDiffAt

@[fun_prop]
/--
theorem `contDiffWithinAt_const` / 定理 `contDiffWithinAt_const`

English:
theorem contDiffWithinAt_const
  given: {c : F}
  statement: ContDiffWithinAt 𝕜 n (fun _ : E => c) s x
  proof: contDiffAt_const.contDiffWithinAt

@[nontriviality]

中文:
定理 contDiffWithinAt_const
  条件: {c : F}
  结论: ContDiffWithinAt 𝕜 n (fun _ : E => c) s x
  证明: contDiffAt_const.contDiffWithinAt

@[nontriviality]

Depends on / 依赖: contDiffAt_const, contDiffAt_const.contDiffWithinAt, contDiffWithinAt
-/
theorem contDiffWithinAt_const {c : F} : ContDiffWithinAt 𝕜 n (fun _ : E => c) s x :=
  contDiffAt_const.contDiffWithinAt

@[nontriviality]
/--
theorem `contDiff_of_subsingleton` / 定理 `contDiff_of_subsingleton`

English:
theorem contDiff_of_subsingleton
  given: [Subsingleton F]
  statement: ContDiff 𝕜 n f
  proof: by
  rw [Subsingleton.elim f fun _ => 0]; exact contDiff_const

@[nontriviality]

中文:
定理 contDiff_of_subsingleton
  条件: [子单例 F]
  结论: 连续可微 𝕜 n f
  证明: by
  rw [Subsingleton.elim f fun _ => 0]; exact contDiff_const

@[nontriviality]

Depends on / 依赖: Subsingleton, Subsingleton.elim, contDiff_const
-/
theorem contDiff_of_subsingleton [Subsingleton F] : ContDiff 𝕜 n f := by
  rw [Subsingleton.elim f fun _ => 0]; exact contDiff_const

@[nontriviality]
/--
theorem `contDiffAt_of_subsingleton` / 定理 `contDiffAt_of_subsingleton`

English:
theorem contDiffAt_of_subsingleton
  given: [Subsingleton F]
  statement: ContDiffAt 𝕜 n f x
  proof: by
  rw [Subsingleton.elim f fun _ => 0]; exact contDiffAt_const

@[nontriviality]

中文:
定理 contDiffAt_of_subsingleton
  条件: [子单例 F]
  结论: ContDiffAt 𝕜 n f x
  证明: by
  rw [Subsingleton.elim f fun _ => 0]; exact contDiffAt_const

@[nontriviality]

Depends on / 依赖: Subsingleton, Subsingleton.elim, contDiffAt_const
-/
theorem contDiffAt_of_subsingleton [Subsingleton F] : ContDiffAt 𝕜 n f x := by
  rw [Subsingleton.elim f fun _ => 0]; exact contDiffAt_const

@[nontriviality]
/--
theorem `contDiffWithinAt_of_subsingleton` / 定理 `contDiffWithinAt_of_subsingleton`

English:
theorem contDiffWithinAt_of_subsingleton
  given: [Subsingleton F]
  statement: ContDiffWithinAt 𝕜 n f s x
  proof: by
  rw [Subsingleton.elim f fun _ => 0]; exact contDiffWithinAt_const

@[nontriviality]

中文:
定理 contDiffWithinAt_of_subsingleton
  条件: [子单例 F]
  结论: ContDiffWithinAt 𝕜 n f s x
  证明: by
  rw [Subsingleton.elim f fun _ => 0]; exact contDiffWithinAt_const

@[nontriviality]

Depends on / 依赖: Subsingleton, Subsingleton.elim, contDiffWithinAt_const
-/
theorem contDiffWithinAt_of_subsingleton [Subsingleton F] : ContDiffWithinAt 𝕜 n f s x := by
  rw [Subsingleton.elim f fun _ => 0]; exact contDiffWithinAt_const

@[nontriviality]
/--
theorem `contDiffOn_of_subsingleton` / 定理 `contDiffOn_of_subsingleton`

English:
theorem contDiffOn_of_subsingleton
  given: [Subsingleton F]
  statement: ContDiffOn 𝕜 n f s
  proof: by
  rw [Subsingleton.elim f fun _ => 0]; exact contDiffOn_const

中文:
定理 contDiffOn_of_subsingleton
  条件: [子单例 F]
  结论: ContDiffOn 𝕜 n f s
  证明: by
  rw [Subsingleton.elim f fun _ => 0]; exact contDiffOn_const

Depends on / 依赖: Subsingleton, Subsingleton.elim, contDiffOn_const
-/
theorem contDiffOn_of_subsingleton [Subsingleton F] : ContDiffOn 𝕜 n f s := by
  rw [Subsingleton.elim f fun _ => 0]; exact contDiffOn_const

/--
theorem `iteratedFDerivWithin_const_of_ne` / 定理 `iteratedFDerivWithin_const_of_ne`

English:
theorem iteratedFDerivWithin_const_of_ne
  given: {n : Nat} (hn : n != 0) (c : F) (s : Set E)
  proof: by
  cases n with
  | zero => contradiction
  | succ n => exact iteratedFDerivWithin_succ_const n c

中文:
定理 iteratedFDerivWithin_const_of_ne
  条件: {n : 自然数} (hn : n != 0) (c : F) (s : 集合 E)
  证明: by
  cases n with
  | zero => contradiction
  | succ n => exact iteratedFDerivWithin_succ_const n c

Depends on / 依赖: iteratedFDerivWithin_succ_const
-/
theorem iteratedFDerivWithin_const_of_ne {n : Nat} (hn : n != 0) (c : F) (s : Set E) :
    iteratedFDerivWithin 𝕜 n (fun _ : E => c) s = 0 := by
  cases n with
  | zero => contradiction
  | succ n => exact iteratedFDerivWithin_succ_const n c

/--
theorem `iteratedFDeriv_const_of_ne` / 定理 `iteratedFDeriv_const_of_ne`

English:
theorem iteratedFDeriv_const_of_ne
  given: {n : Nat} (hn : n != 0) (c : F)
  proof: by
  simp only [← iteratedFDerivWithin_univ, iteratedFDerivWithin_const_of_ne hn]

中文:
定理 iteratedFDeriv_const_of_ne
  条件: {n : 自然数} (hn : n != 0) (c : F)
  证明: by
  simp only [← iteratedFDerivWithin_univ, iteratedFDerivWithin_const_of_ne hn]

Depends on / 依赖: iteratedFDerivWithin_const_of_ne, iteratedFDerivWithin_univ
-/
theorem iteratedFDeriv_const_of_ne {n : Nat} (hn : n != 0) (c : F) :
    (iteratedFDeriv 𝕜 n fun _ : E => c) = 0 := by
  simp only [← iteratedFDerivWithin_univ, iteratedFDerivWithin_const_of_ne hn]

/--
theorem `iteratedFDeriv_succ_const` / 定理 `iteratedFDeriv_succ_const`

English:
theorem iteratedFDeriv_succ_const
  given: (n : Nat) (c : F)
  proof: iteratedFDeriv_const_of_ne (by simp) _

中文:
定理 iteratedFDeriv_succ_const
  条件: (n : 自然数) (c : F)
  证明: iteratedFDeriv_const_of_ne (by simp) _

Depends on / 依赖: iteratedFDeriv_const_of_ne
-/
theorem iteratedFDeriv_succ_const (n : Nat) (c : F) :
    (iteratedFDeriv 𝕜 (n + 1) fun _ : E => c) = 0 :=
  iteratedFDeriv_const_of_ne (by simp) _

/--
theorem `contDiffWithinAt_singleton` / 定理 `contDiffWithinAt_singleton`

English:
theorem contDiffWithinAt_singleton
  statement: ContDiffWithinAt 𝕜 n f {x} x
  proof: (contDiffWithinAt_const (c := f x)).congr (by simp) rfl

中文:
定理 contDiffWithinAt_singleton
  结论: ContDiffWithinAt 𝕜 n f {x} x
  证明: (contDiffWithinAt_const (c := f x)).congr (by simp) rfl

Depends on / 依赖: contDiffWithinAt_const
-/
theorem contDiffWithinAt_singleton : ContDiffWithinAt 𝕜 n f {x} x :=
  (contDiffWithinAt_const (c := f x)).congr (by simp) rfl

end constants

/-! ### Smoothness of linear functions -/
section linear

/--
theorem `IsBoundedLinearMap.contDiff` / 定理 `IsBoundedLinearMap.contDiff`

English:
theorem IsBoundedLinearMap.contDiff
  given: (hf : IsBoundedLinearMap 𝕜 f)
  statement: ContDiff 𝕜 n f
  proof: (ContinuousLinearMap.analyticOnNhd hf.toContinuousLinearMap univ).contDiff

@[fun_prop]

中文:
定理 是BoundedLinear映射.contDiff
  条件: (hf : 是BoundedLinear映射 𝕜 f)
  结论: 连续可微 𝕜 n f
  证明: (ContinuousLinearMap.analyticOnNhd hf.toContinuousLinearMap univ).contDiff

@[fun_prop]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.analyticOnNhd, analyticOnNhd, contDiff, hf.toContinuousLinearMap, toContinuousLinearMap
-/
theorem IsBoundedLinearMap.contDiff (hf : IsBoundedLinearMap 𝕜 f) : ContDiff 𝕜 n f :=
  (ContinuousLinearMap.analyticOnNhd hf.toContinuousLinearMap univ).contDiff

@[fun_prop]
/--
theorem `ContinuousLinearMap.contDiff` / 定理 `ContinuousLinearMap.contDiff`

English:
theorem ContinuousLinearMap.contDiff
  given: (f : E ->L[𝕜] F)
  statement: ContDiff 𝕜 n f
  proof: f.isBoundedLinearMap.contDiff

@[fun_prop]

中文:
定理 连续线性映射.contDiff
  条件: (f : E ->L[𝕜] F)
  结论: 连续可微 𝕜 n f
  证明: f.isBoundedLinearMap.contDiff

@[fun_prop]

Depends on / 依赖: contDiff, f.isBoundedLinearMap.contDiff, isBoundedLinearMap
-/
theorem ContinuousLinearMap.contDiff (f : E ->L[𝕜] F) : ContDiff 𝕜 n f :=
  f.isBoundedLinearMap.contDiff

@[fun_prop]
/--
theorem `ContinuousLinearEquiv.contDiff` / 定理 `ContinuousLinearEquiv.contDiff`

English:
theorem ContinuousLinearEquiv.contDiff
  given: (f : E ≃L[𝕜] F)
  statement: ContDiff 𝕜 n f
  proof: (f : E ->L[𝕜] F).contDiff

@[fun_prop]

中文:
定理 连续线性等价.contDiff
  条件: (f : E ≃L[𝕜] F)
  结论: 连续可微 𝕜 n f
  证明: (f : E ->L[𝕜] F).contDiff

@[fun_prop]

Depends on / 依赖: contDiff
-/
theorem ContinuousLinearEquiv.contDiff (f : E ≃L[𝕜] F) : ContDiff 𝕜 n f :=
  (f : E ->L[𝕜] F).contDiff

@[fun_prop]
/--
theorem `LinearIsometry.contDiff` / 定理 `LinearIsometry.contDiff`

English:
theorem LinearIsometry.contDiff
  given: (f : E ->ₗᵢ[𝕜] F)
  statement: ContDiff 𝕜 n f
  proof: f.toContinuousLinearMap.contDiff

@[fun_prop]

中文:
定理 线性等距.contDiff
  条件: (f : E ->ₗᵢ[𝕜] F)
  结论: 连续可微 𝕜 n f
  证明: f.toContinuousLinearMap.contDiff

@[fun_prop]

Depends on / 依赖: contDiff, f.toContinuousLinearMap.contDiff, toContinuousLinearMap
-/
theorem LinearIsometry.contDiff (f : E ->ₗᵢ[𝕜] F) : ContDiff 𝕜 n f :=
  f.toContinuousLinearMap.contDiff

@[fun_prop]
/--
theorem `LinearIsometryEquiv.contDiff` / 定理 `LinearIsometryEquiv.contDiff`

English:
theorem LinearIsometryEquiv.contDiff
  given: (f : E ≃ₗᵢ[𝕜] F)
  statement: ContDiff 𝕜 n f
  proof: (f : E ->L[𝕜] F).contDiff

中文:
定理 线性等距等价.contDiff
  条件: (f : E ≃ₗᵢ[𝕜] F)
  结论: 连续可微 𝕜 n f
  证明: (f : E ->L[𝕜] F).contDiff

Depends on / 依赖: contDiff
-/
theorem LinearIsometryEquiv.contDiff (f : E ≃ₗᵢ[𝕜] F) : ContDiff 𝕜 n f :=
  (f : E ->L[𝕜] F).contDiff

/-- The identity is `C^n`. -/
@[to_fun (attr := fun_prop) contDiff_fun_id]
/--
theorem `contDiff_id` / 定理 `contDiff_id`

English:
theorem contDiff_id
  statement: ContDiff 𝕜 n (id : E -> E)
  proof: IsBoundedLinearMap.id.contDiff

@[to_fun (attr := fun_prop) contDiffWithinAt_fun_id]

中文:
定理 contDiff_id
  结论: 连续可微 𝕜 n (id : E -> E)
  证明: IsBoundedLinearMap.id.contDiff

@[to_fun (attr := fun_prop) contDiffWithinAt_fun_id]

Depends on / 依赖: IsBoundedLinearMap, IsBoundedLinearMap.id.contDiff, contDiff
-/
theorem contDiff_id : ContDiff 𝕜 n (id : E -> E) :=
  IsBoundedLinearMap.id.contDiff

@[to_fun (attr := fun_prop) contDiffWithinAt_fun_id]
/--
theorem `contDiffWithinAt_id` / 定理 `contDiffWithinAt_id`

English:
theorem contDiffWithinAt_id
  given: {s x}
  statement: ContDiffWithinAt 𝕜 n (id : E -> E) s x
  proof: contDiff_id.contDiffWithinAt

@[to_fun (attr := fun_prop) contDiffAt_fun_id]

中文:
定理 contDiffWithinAt_id
  条件: {s x}
  结论: ContDiffWithinAt 𝕜 n (id : E -> E) s x
  证明: contDiff_id.contDiffWithinAt

@[to_fun (attr := fun_prop) contDiffAt_fun_id]

Depends on / 依赖: contDiffWithinAt, contDiff_id, contDiff_id.contDiffWithinAt
-/
theorem contDiffWithinAt_id {s x} : ContDiffWithinAt 𝕜 n (id : E -> E) s x :=
  contDiff_id.contDiffWithinAt

@[to_fun (attr := fun_prop) contDiffAt_fun_id]
/--
theorem `contDiffAt_id` / 定理 `contDiffAt_id`

English:
theorem contDiffAt_id
  given: {x}
  statement: ContDiffAt 𝕜 n (id : E -> E) x
  proof: contDiff_id.contDiffAt

@[to_fun (attr := fun_prop) contDiffOn_fun_id]

中文:
定理 contDiffAt_id
  条件: {x}
  结论: ContDiffAt 𝕜 n (id : E -> E) x
  证明: contDiff_id.contDiffAt

@[to_fun (attr := fun_prop) contDiffOn_fun_id]

Depends on / 依赖: contDiffAt, contDiff_id, contDiff_id.contDiffAt
-/
theorem contDiffAt_id {x} : ContDiffAt 𝕜 n (id : E -> E) x :=
  contDiff_id.contDiffAt

@[to_fun (attr := fun_prop) contDiffOn_fun_id]
/--
theorem `contDiffOn_id` / 定理 `contDiffOn_id`

English:
theorem contDiffOn_id
  given: {s}
  statement: ContDiffOn 𝕜 n (id : E -> E) s
  proof: contDiff_id.contDiffOn

中文:
定理 contDiffOn_id
  条件: {s}
  结论: ContDiffOn 𝕜 n (id : E -> E) s
  证明: contDiff_id.contDiffOn

Depends on / 依赖: contDiffOn, contDiff_id, contDiff_id.contDiffOn
-/
theorem contDiffOn_id {s} : ContDiffOn 𝕜 n (id : E -> E) s :=
  contDiff_id.contDiffOn

/--
theorem `IsBoundedBilinearMap.contDiff` / 定理 `IsBoundedBilinearMap.contDiff`

English:
theorem IsBoundedBilinearMap.contDiff
  given: (hb : IsBoundedBilinearMap 𝕜 b)
  statement: ContDiff 𝕜 n b
  proof: (hb.toContinuousLinearMap.analyticOnNhd_bilinear _).contDiff

中文:
定理 是BoundedBilinear映射.contDiff
  条件: (hb : 是BoundedBilinear映射 𝕜 b)
  结论: 连续可微 𝕜 n b
  证明: (hb.toContinuousLinearMap.analyticOnNhd_bilinear _).contDiff

Depends on / 依赖: analyticOnNhd_bilinear, contDiff, hb.toContinuousLinearMap.analyticOnNhd_bilinear, toContinuousLinearMap
-/
theorem IsBoundedBilinearMap.contDiff (hb : IsBoundedBilinearMap 𝕜 b) : ContDiff 𝕜 n b :=
  (hb.toContinuousLinearMap.analyticOnNhd_bilinear _).contDiff

/--
theorem `HasFTaylorSeriesUpToOn.continuousLinearMap_comp` / 定理 `HasFTaylorSeriesUpToOn.continuousLinearMap_comp`

English:
theorem HasFTaylorSeriesUpToOn.continuousLinearMap_comp
  statement: {n : Nat∞ω} (g : F ->L[𝕜] G)
  proof: congr_arg g (hf.zero_eq x hx)
  fderivWithin m hm x hx := (ContinuousLinearMap.compContinuousMultilinearMapL 𝕜
    (fun _ : Fin m => E) F G g).hasFDerivAt.comp_hasFDerivWithinAt x (hf.fderivWithin m hm x hx)
  cont m hm := (ContinuousLinearMap.compContinuousMultilinearMapL 𝕜
    (fun _ : Fin m => E) F G g).continuous.comp_continuousOn (hf.cont m hm)

中文:
定理 有FTaylorSeriesUpToOn.continuousLinearMap_comp
  结论: {n : 自然数∞ω} (g : F ->L[𝕜] G)
  证明: congr_arg g (hf.zero_eq x hx)
  fderivWithin m hm x hx := (ContinuousLinearMap.compContinuousMultilinearMapL 𝕜
    (fun _ : Fin m => E) F G g).hasFDerivAt.comp_hasFDerivWithinAt x (hf.fderivWithin m hm x hx)
  cont m hm := (ContinuousLinearMap.compContinuousMultilinearMapL 𝕜
    (fun _ : Fin m => E) F G g).continuous.comp_continuousOn (hf.cont m hm)

Depends on / 依赖: congr_arg, hf.zero_eq, zero_eq
-/
theorem HasFTaylorSeriesUpToOn.continuousLinearMap_comp {n : Nat∞ω} (g : F ->L[𝕜] G)
    (hf : HasFTaylorSeriesUpToOn n f p s) :
    HasFTaylorSeriesUpToOn n (g ∘ f) (fun x k => g.compContinuousMultilinearMap (p x k)) s where
  zero_eq x hx := congr_arg g (hf.zero_eq x hx)
  fderivWithin m hm x hx := (ContinuousLinearMap.compContinuousMultilinearMapL 𝕜
    (fun _ : Fin m => E) F G g).hasFDerivAt.comp_hasFDerivWithinAt x (hf.fderivWithin m hm x hx)
  cont m hm := (ContinuousLinearMap.compContinuousMultilinearMapL 𝕜
    (fun _ : Fin m => E) F G g).continuous.comp_continuousOn (hf.cont m hm)

/--
theorem `ContDiffWithinAt.continuousLinearMap_comp` / 定理 `ContDiffWithinAt.continuousLinearMap_comp`

English:
theorem ContDiffWithinAt.continuousLinearMap_comp
  statement: (g : F ->L[𝕜] G)
  proof: by
  match n with
  | ω =>
    obtain ⟨u, hu, p, hp, h'p⟩ := hf
    refine ⟨u, hu, _, hp.continuousLinearMap_comp g, fun i => ?_⟩
    change AnalyticOn 𝕜
      (fun x => (ContinuousLinearMap.compContinuousMultilinearMapL 𝕜
      (fun _ : Fin i => E) F G g) (p x i)) u
    apply AnalyticOnNhd.comp_analyticOn _ (h'p i) (Set.mapsTo_univ _ _)
    exact ContinuousLinearMap.analyticOnNhd _ _
  | (n : Nat∞) =>
    intro m hm
    rcases hf m hm with ⟨u, hu, p, hp⟩
    exact ⟨u, hu, _, hp.continuousLinearMap_comp g⟩

中文:
定理 ContDiffWithinAt.continuousLinearMap_comp
  结论: (g : F ->L[𝕜] G)
  证明: by
  match n with
  | ω =>
    obtain ⟨u, hu, p, hp, h'p⟩ := hf
    refine ⟨u, hu, _, hp.continuousLinearMap_comp g, fun i => ?_⟩
    change AnalyticOn 𝕜
      (fun x => (ContinuousLinearMap.compContinuousMultilinearMapL 𝕜
      (fun _ : Fin i => E) F G g) (p x i)) u
    apply AnalyticOnNhd.comp_analyticOn _ (h'p i) (Set.mapsTo_univ _ _)
    exact ContinuousLinearMap.analyticOnNhd _ _
  | (n : Nat∞) =>
    intro m hm
    rcases hf m hm with ⟨u, hu, p, hp⟩
    exact ⟨u, hu, _, hp.continuousLinearMap_comp g⟩

Depends on / 依赖: AnalyticOn, AnalyticOnNhd, AnalyticOnNhd.comp_analyticOn, ContinuousLinearMap, ContinuousLinearMap.analyticOnNhd, ContinuousLinearMap.compContinuousMultilinearMapL, Set.mapsTo_univ, analyticOnNhd, compContinuousMultilinearMapL, comp_analyticOn, continuousLinearMap_comp, hp.continuousLinearMap_comp, mapsTo_univ
-/
theorem ContDiffWithinAt.continuousLinearMap_comp (g : F ->L[𝕜] G)
    (hf : ContDiffWithinAt 𝕜 n f s x) : ContDiffWithinAt 𝕜 n (g ∘ f) s x := by
  match n with
  | ω =>
    obtain ⟨u, hu, p, hp, h'p⟩ := hf
    refine ⟨u, hu, _, hp.continuousLinearMap_comp g, fun i => ?_⟩
    change AnalyticOn 𝕜
      (fun x => (ContinuousLinearMap.compContinuousMultilinearMapL 𝕜
      (fun _ : Fin i => E) F G g) (p x i)) u
    apply AnalyticOnNhd.comp_analyticOn _ (h'p i) (Set.mapsTo_univ _ _)
    exact ContinuousLinearMap.analyticOnNhd _ _
  | (n : Nat∞) =>
    intro m hm
    rcases hf m hm with ⟨u, hu, p, hp⟩
    exact ⟨u, hu, _, hp.continuousLinearMap_comp g⟩

/--
theorem `ContDiffAt.continuousLinearMap_comp` / 定理 `ContDiffAt.continuousLinearMap_comp`

English:
theorem ContDiffAt.continuousLinearMap_comp
  given: (g : F ->L[𝕜] G) (hf : ContDiffAt 𝕜 n f x)
  proof: ContDiffWithinAt.continuousLinearMap_comp g hf

中文:
定理 ContDiffAt.continuousLinearMap_comp
  条件: (g : F ->L[𝕜] G) (hf : ContDiffAt 𝕜 n f x)
  证明: ContDiffWithinAt.continuousLinearMap_comp g hf

Depends on / 依赖: ContDiffWithinAt, ContDiffWithinAt.continuousLinearMap_comp, continuousLinearMap_comp
-/
theorem ContDiffAt.continuousLinearMap_comp (g : F ->L[𝕜] G) (hf : ContDiffAt 𝕜 n f x) :
    ContDiffAt 𝕜 n (g ∘ f) x :=
  ContDiffWithinAt.continuousLinearMap_comp g hf

/--
theorem `ContDiffOn.continuousLinearMap_comp` / 定理 `ContDiffOn.continuousLinearMap_comp`

English:
theorem ContDiffOn.continuousLinearMap_comp
  given: (g : F ->L[𝕜] G) (hf : ContDiffOn 𝕜 n f s)
  proof: fun x hx => (hf x hx).continuousLinearMap_comp g

中文:
定理 ContDiffOn.continuousLinearMap_comp
  条件: (g : F ->L[𝕜] G) (hf : ContDiffOn 𝕜 n f s)
  证明: fun x hx => (hf x hx).continuousLinearMap_comp g

Depends on / 依赖: continuousLinearMap_comp
-/
theorem ContDiffOn.continuousLinearMap_comp (g : F ->L[𝕜] G) (hf : ContDiffOn 𝕜 n f s) :
    ContDiffOn 𝕜 n (g ∘ f) s := fun x hx => (hf x hx).continuousLinearMap_comp g

/--
theorem `ContDiff.continuousLinearMap_comp` / 定理 `ContDiff.continuousLinearMap_comp`

English:
theorem ContDiff.continuousLinearMap_comp
  given: {f : E -> F} (g : F ->L[𝕜] G) (hf : ContDiff 𝕜 n f)
  proof: contDiffOn_univ.1 ContDiffOn.continuousLinearMap_comp _ (contDiffOn_univ.2 hf)

中文:
定理 连续可微.continuousLinearMap_comp
  条件: {f : E -> F} (g : F ->L[𝕜] G) (hf : 连续可微 𝕜 n f)
  证明: contDiffOn_univ.1 ContDiffOn.continuousLinearMap_comp _ (contDiffOn_univ.2 hf)

Depends on / 依赖: ContDiffOn, ContDiffOn.continuousLinearMap_comp, contDiffOn_univ, continuousLinearMap_comp
-/
theorem ContDiff.continuousLinearMap_comp {f : E -> F} (g : F ->L[𝕜] G) (hf : ContDiff 𝕜 n f) :
    ContDiff 𝕜 n fun x => g (f x) :=
contDiffOn_univ.1 ContDiffOn.continuousLinearMap_comp _ (contDiffOn_univ.2 hf)

/--
theorem `ContinuousLinearMap.iteratedFDerivWithin_comp_left` / 定理 `ContinuousLinearMap.iteratedFDerivWithin_comp_left`

English:
theorem ContinuousLinearMap.iteratedFDerivWithin_comp_left
  statement: {f : E -> F} (g : F ->L[𝕜] G)
  proof: by
  rcases hf.contDiffOn' hi (by simp) with ⟨U, hU, hxU, hfU⟩
  rw [← iteratedFDerivWithin_inter_open hU hxU]; rw [← iteratedFDerivWithin_inter_open (f := f) hU hxU]
  rw [insert_eq_of_mem hx] at hfU
exact .symm (hfU.ftaylorSeriesWithin (hs.inter hU)).continuousLinearMap_comp g
.eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl (hs.inter hU) ⟨hx, hxU⟩

中文:
定理 连续线性映射.iteratedFDerivWithin_comp_left
  结论: {f : E -> F} (g : F ->L[𝕜] G)
  证明: by
  rcases hf.contDiffOn' hi (by simp) with ⟨U, hU, hxU, hfU⟩
  rw [← iteratedFDerivWithin_inter_open hU hxU]; rw [← iteratedFDerivWithin_inter_open (f := f) hU hxU]
  rw [insert_eq_of_mem hx] at hfU
exact .symm (hfU.ftaylorSeriesWithin (hs.inter hU)).continuousLinearMap_comp g
.eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl (hs.inter hU) ⟨hx, hxU⟩

Depends on / 依赖: contDiffOn, continuousLinearMap_comp, eq_iteratedFDerivWithin_of_uniqueDiffOn, ftaylorSeriesWithin, hf.contDiffOn, hfU.ftaylorSeriesWithin, hs.inter, insert_eq_of_mem, iteratedFDerivWithin_inter_open, le_rfl
-/
theorem ContinuousLinearMap.iteratedFDerivWithin_comp_left {f : E -> F} (g : F ->L[𝕜] G)
    (hf : ContDiffWithinAt 𝕜 n f s x) (hs : UniqueDiffOn 𝕜 s) (hx : x in s) {i : Nat} (hi : i <= n) :
    iteratedFDerivWithin 𝕜 i (g ∘ f) s x =
      g.compContinuousMultilinearMap (iteratedFDerivWithin 𝕜 i f s x) := by
  rcases hf.contDiffOn' hi (by simp) with ⟨U, hU, hxU, hfU⟩
  rw [← iteratedFDerivWithin_inter_open hU hxU]; rw [← iteratedFDerivWithin_inter_open (f := f) hU hxU]
  rw [insert_eq_of_mem hx] at hfU
exact .symm (hfU.ftaylorSeriesWithin (hs.inter hU)).continuousLinearMap_comp g
.eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl (hs.inter hU) ⟨hx, hxU⟩

/--
theorem `ContinuousLinearMap.iteratedFDeriv_comp_left` / 定理 `ContinuousLinearMap.iteratedFDeriv_comp_left`

English:
theorem ContinuousLinearMap.iteratedFDeriv_comp_left
  statement: {f : E -> F} (g : F ->L[𝕜] G)
  proof: by
  simp only [← iteratedFDerivWithin_univ]
  exact g.iteratedFDerivWithin_comp_left hf.contDiffWithinAt uniqueDiffOn_univ (mem_univ x) hi

中文:
定理 连续线性映射.iteratedFDeriv_comp_left
  结论: {f : E -> F} (g : F ->L[𝕜] G)
  证明: by
  simp only [← iteratedFDerivWithin_univ]
  exact g.iteratedFDerivWithin_comp_left hf.contDiffWithinAt uniqueDiffOn_univ (mem_univ x) hi

Depends on / 依赖: contDiffWithinAt, g.iteratedFDerivWithin_comp_left, hf.contDiffWithinAt, iteratedFDerivWithin_comp_left, iteratedFDerivWithin_univ, mem_univ, uniqueDiffOn_univ
-/
theorem ContinuousLinearMap.iteratedFDeriv_comp_left {f : E -> F} (g : F ->L[𝕜] G)
    (hf : ContDiffAt 𝕜 n f x) {i : Nat} (hi : i <= n) :
    iteratedFDeriv 𝕜 i (g ∘ f) x = g.compContinuousMultilinearMap (iteratedFDeriv 𝕜 i f x) := by
  simp only [← iteratedFDerivWithin_univ]
  exact g.iteratedFDerivWithin_comp_left hf.contDiffWithinAt uniqueDiffOn_univ (mem_univ x) hi

/--
theorem `ContinuousLinearEquiv.iteratedFDerivWithin_comp_left` / 定理 `ContinuousLinearEquiv.iteratedFDerivWithin_comp_left`

English:
theorem ContinuousLinearEquiv.iteratedFDerivWithin_comp_left
  statement: (g : F ≃L[𝕜] G) (f : E -> F)
  proof: by
  induction i generalizing x with ext1 m
  | zero =>
    simp only [iteratedFDerivWithin_zero_apply, comp_apply,
      ContinuousLinearMap.compContinuousMultilinearMap_coe, coe_coe]
  | succ i IH =>
    rw [iteratedFDerivWithin_succ_apply_left]
    have Z : fderivWithin 𝕜 (iteratedFDerivWithin 𝕜 i (g ∘ f) s) s x =
        fderivWithin 𝕜 (g.continuousMultilinearMapCongrRight (fun _ : Fin i => E) ∘
          iteratedFDerivWithin 𝕜 i f s) s x :=
      fderivWithin_congr' (@IH) hx
    simp_rw [Z]
    rw [(g.continuousMultilinearMapCongrRight fun _ : Fin i => E).comp_fderivWithin (hs x hx)]
    simp [iteratedFDerivWithin_succ_apply_left]

中文:
定理 连续线性等价.iteratedFDerivWithin_comp_left
  结论: (g : F ≃L[𝕜] G) (f : E -> F)
  证明: by
  induction i generalizing x with ext1 m
  | zero =>
    simp only [iteratedFDerivWithin_zero_apply, comp_apply,
      ContinuousLinearMap.compContinuousMultilinearMap_coe, coe_coe]
  | succ i IH =>
    rw [iteratedFDerivWithin_succ_apply_left]
    have Z : fderivWithin 𝕜 (iteratedFDerivWithin 𝕜 i (g ∘ f) s) s x =
        fderivWithin 𝕜 (g.continuousMultilinearMapCongrRight (fun _ : Fin i => E) ∘
          iteratedFDerivWithin 𝕜 i f s) s x :=
      fderivWithin_congr' (@IH) hx
    simp_rw [Z]
    rw [(g.continuousMultilinearMapCongrRight fun _ : Fin i => E).comp_fderivWithin (hs x hx)]
    simp [iteratedFDerivWithin_succ_apply_left]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.compContinuousMultilinearMap_coe, coe_coe, compContinuousMultilinearMap_coe, comp_apply, continuousMultilinearMapCongrRight, fderivWithin, fderivWithin_congr, g.continuousMultilinearMapCongrRight, generalizing, iteratedFDerivWithin, iteratedFDerivWithin_succ_apply_left, iteratedFDerivWithin_zero_apply, simp_rw
-/
theorem ContinuousLinearEquiv.iteratedFDerivWithin_comp_left (g : F ≃L[𝕜] G) (f : E -> F)
    (hs : UniqueDiffOn 𝕜 s) (hx : x in s) (i : Nat) :
    iteratedFDerivWithin 𝕜 i (g ∘ f) s x =
      (g : F ->L[𝕜] G).compContinuousMultilinearMap (iteratedFDerivWithin 𝕜 i f s x) := by
  induction i generalizing x with ext1 m
  | zero =>
    simp only [iteratedFDerivWithin_zero_apply, comp_apply,
      ContinuousLinearMap.compContinuousMultilinearMap_coe, coe_coe]
  | succ i IH =>
    rw [iteratedFDerivWithin_succ_apply_left]
    have Z : fderivWithin 𝕜 (iteratedFDerivWithin 𝕜 i (g ∘ f) s) s x =
        fderivWithin 𝕜 (g.continuousMultilinearMapCongrRight (fun _ : Fin i => E) ∘
          iteratedFDerivWithin 𝕜 i f s) s x :=
      fderivWithin_congr' (@IH) hx
    simp_rw [Z]
    rw [(g.continuousMultilinearMapCongrRight fun _ : Fin i => E).comp_fderivWithin (hs x hx)]
    simp [iteratedFDerivWithin_succ_apply_left]

/--
theorem `ContinuousLinearEquiv.iteratedFDeriv_comp_left` / 定理 `ContinuousLinearEquiv.iteratedFDeriv_comp_left`

English:
theorem ContinuousLinearEquiv.iteratedFDeriv_comp_left
  given: {f : E -> F} {x : E} (g : F ≃L[𝕜] G) {i : Nat}
  proof: by
  simp only [← iteratedFDerivWithin_univ]
  apply g.iteratedFDerivWithin_comp_left f uniqueDiffOn_univ trivial

中文:
定理 连续线性等价.iteratedFDeriv_comp_left
  条件: {f : E -> F} {x : E} (g : F ≃L[𝕜] G) {i : 自然数}
  证明: by
  simp only [← iteratedFDerivWithin_univ]
  apply g.iteratedFDerivWithin_comp_left f uniqueDiffOn_univ trivial

Depends on / 依赖: g.iteratedFDerivWithin_comp_left, iteratedFDerivWithin_comp_left, iteratedFDerivWithin_univ, uniqueDiffOn_univ
-/
theorem ContinuousLinearEquiv.iteratedFDeriv_comp_left {f : E -> F} {x : E} (g : F ≃L[𝕜] G) {i : Nat} :
    iteratedFDeriv 𝕜 i (g ∘ f) x =
      g.toContinuousLinearMap.compContinuousMultilinearMap (iteratedFDeriv 𝕜 i f x) := by
  simp only [← iteratedFDerivWithin_univ]
  apply g.iteratedFDerivWithin_comp_left f uniqueDiffOn_univ trivial

/--
theorem `LinearIsometry.norm_iteratedFDerivWithin_comp_left` / 定理 `LinearIsometry.norm_iteratedFDerivWithin_comp_left`

English:
theorem LinearIsometry.norm_iteratedFDerivWithin_comp_left
  statement: {f : E -> F} (g : F ->ₗᵢ[𝕜] G)
  proof: by
  have :
    iteratedFDerivWithin 𝕜 i (g ∘ f) s x =
      g.toContinuousLinearMap.compContinuousMultilinearMap (iteratedFDerivWithin 𝕜 i f s x) :=
    g.toContinuousLinearMap.iteratedFDerivWithin_comp_left hf hs hx hi
  rw [this]
  apply LinearIsometry.norm_compContinuousMultilinearMap

中文:
定理 线性等距.norm_iteratedFDerivWithin_comp_left
  结论: {f : E -> F} (g : F ->ₗᵢ[𝕜] G)
  证明: by
  have :
    iteratedFDerivWithin 𝕜 i (g ∘ f) s x =
      g.toContinuousLinearMap.compContinuousMultilinearMap (iteratedFDerivWithin 𝕜 i f s x) :=
    g.toContinuousLinearMap.iteratedFDerivWithin_comp_left hf hs hx hi
  rw [this]
  apply LinearIsometry.norm_compContinuousMultilinearMap

Depends on / 依赖: LinearIsometry, LinearIsometry.norm_compContinuousMultilinearMap, compContinuousMultilinearMap, g.toContinuousLinearMap.compContinuousMultilinearMap, g.toContinuousLinearMap.iteratedFDerivWithin_comp_left, iteratedFDerivWithin, iteratedFDerivWithin_comp_left, norm_compContinuousMultilinearMap, toContinuousLinearMap
-/
theorem LinearIsometry.norm_iteratedFDerivWithin_comp_left {f : E -> F} (g : F ->ₗᵢ[𝕜] G)
    (hf : ContDiffWithinAt 𝕜 n f s x) (hs : UniqueDiffOn 𝕜 s) (hx : x in s) {i : Nat} (hi : i <= n) :
    ‖iteratedFDerivWithin 𝕜 i (g ∘ f) s x‖ = ‖iteratedFDerivWithin 𝕜 i f s x‖ := by
  have :
    iteratedFDerivWithin 𝕜 i (g ∘ f) s x =
      g.toContinuousLinearMap.compContinuousMultilinearMap (iteratedFDerivWithin 𝕜 i f s x) :=
    g.toContinuousLinearMap.iteratedFDerivWithin_comp_left hf hs hx hi
  rw [this]
  apply LinearIsometry.norm_compContinuousMultilinearMap

/--
theorem `LinearIsometry.norm_iteratedFDeriv_comp_left` / 定理 `LinearIsometry.norm_iteratedFDeriv_comp_left`

English:
theorem LinearIsometry.norm_iteratedFDeriv_comp_left
  statement: {f : E -> F} (g : F ->ₗᵢ[𝕜] G)
  proof: by
  simp only [← iteratedFDerivWithin_univ]
  exact g.norm_iteratedFDerivWithin_comp_left hf.contDiffWithinAt uniqueDiffOn_univ (mem_univ x) hi

中文:
定理 线性等距.norm_iteratedFDeriv_comp_left
  结论: {f : E -> F} (g : F ->ₗᵢ[𝕜] G)
  证明: by
  simp only [← iteratedFDerivWithin_univ]
  exact g.norm_iteratedFDerivWithin_comp_left hf.contDiffWithinAt uniqueDiffOn_univ (mem_univ x) hi

Depends on / 依赖: contDiffWithinAt, g.norm_iteratedFDerivWithin_comp_left, hf.contDiffWithinAt, iteratedFDerivWithin_univ, mem_univ, norm_iteratedFDerivWithin_comp_left, uniqueDiffOn_univ
-/
theorem LinearIsometry.norm_iteratedFDeriv_comp_left {f : E -> F} (g : F ->ₗᵢ[𝕜] G)
    (hf : ContDiffAt 𝕜 n f x) {i : Nat} (hi : i <= n) :
    ‖iteratedFDeriv 𝕜 i (g ∘ f) x‖ = ‖iteratedFDeriv 𝕜 i f x‖ := by
  simp only [← iteratedFDerivWithin_univ]
  exact g.norm_iteratedFDerivWithin_comp_left hf.contDiffWithinAt uniqueDiffOn_univ (mem_univ x) hi

/--
theorem `LinearIsometryEquiv.norm_iteratedFDerivWithin_comp_left` / 定理 `LinearIsometryEquiv.norm_iteratedFDerivWithin_comp_left`

English:
theorem LinearIsometryEquiv.norm_iteratedFDerivWithin_comp_left
  statement: (g : F ≃ₗᵢ[𝕜] G) (f : E -> F)
  proof: by
  have :
    iteratedFDerivWithin 𝕜 i (g ∘ f) s x =
      (g : F ->L[𝕜] G).compContinuousMultilinearMap (iteratedFDerivWithin 𝕜 i f s x) :=
    g.toContinuousLinearEquiv.iteratedFDerivWithin_comp_left f hs hx i
  rw [this]
  apply LinearIsometry.norm_compContinuousMultilinearMap g.toLinearIsometry

中文:
定理 线性等距等价.norm_iteratedFDerivWithin_comp_left
  结论: (g : F ≃ₗᵢ[𝕜] G) (f : E -> F)
  证明: by
  have :
    iteratedFDerivWithin 𝕜 i (g ∘ f) s x =
      (g : F ->L[𝕜] G).compContinuousMultilinearMap (iteratedFDerivWithin 𝕜 i f s x) :=
    g.toContinuousLinearEquiv.iteratedFDerivWithin_comp_left f hs hx i
  rw [this]
  apply LinearIsometry.norm_compContinuousMultilinearMap g.toLinearIsometry

Depends on / 依赖: LinearIsometry, LinearIsometry.norm_compContinuousMultilinearMap, compContinuousMultilinearMap, g.toContinuousLinearEquiv.iteratedFDerivWithin_comp_left, g.toLinearIsometry, iteratedFDerivWithin, iteratedFDerivWithin_comp_left, norm_compContinuousMultilinearMap, toContinuousLinearEquiv, toLinearIsometry
-/
theorem LinearIsometryEquiv.norm_iteratedFDerivWithin_comp_left (g : F ≃ₗᵢ[𝕜] G) (f : E -> F)
    (hs : UniqueDiffOn 𝕜 s) (hx : x in s) (i : Nat) :
    ‖iteratedFDerivWithin 𝕜 i (g ∘ f) s x‖ = ‖iteratedFDerivWithin 𝕜 i f s x‖ := by
  have :
    iteratedFDerivWithin 𝕜 i (g ∘ f) s x =
      (g : F ->L[𝕜] G).compContinuousMultilinearMap (iteratedFDerivWithin 𝕜 i f s x) :=
    g.toContinuousLinearEquiv.iteratedFDerivWithin_comp_left f hs hx i
  rw [this]
  apply LinearIsometry.norm_compContinuousMultilinearMap g.toLinearIsometry

/--
theorem `LinearIsometryEquiv.norm_iteratedFDeriv_comp_left` / 定理 `LinearIsometryEquiv.norm_iteratedFDeriv_comp_left`

English:
theorem LinearIsometryEquiv.norm_iteratedFDeriv_comp_left
  statement: (g : F ≃ₗᵢ[𝕜] G) (f : E -> F) (x : E)
  proof: by
  rw [← iteratedFDerivWithin_univ]; rw [← iteratedFDerivWithin_univ]
  apply g.norm_iteratedFDerivWithin_comp_left f uniqueDiffOn_univ (mem_univ x) i

中文:
定理 线性等距等价.norm_iteratedFDeriv_comp_left
  结论: (g : F ≃ₗᵢ[𝕜] G) (f : E -> F) (x : E)
  证明: by
  rw [← iteratedFDerivWithin_univ]; rw [← iteratedFDerivWithin_univ]
  apply g.norm_iteratedFDerivWithin_comp_left f uniqueDiffOn_univ (mem_univ x) i

Depends on / 依赖: g.norm_iteratedFDerivWithin_comp_left, iteratedFDerivWithin_univ, mem_univ, norm_iteratedFDerivWithin_comp_left, uniqueDiffOn_univ
-/
theorem LinearIsometryEquiv.norm_iteratedFDeriv_comp_left (g : F ≃ₗᵢ[𝕜] G) (f : E -> F) (x : E)
    (i : Nat) : ‖iteratedFDeriv 𝕜 i (g ∘ f) x‖ = ‖iteratedFDeriv 𝕜 i f x‖ := by
  rw [← iteratedFDerivWithin_univ]; rw [← iteratedFDerivWithin_univ]
  apply g.norm_iteratedFDerivWithin_comp_left f uniqueDiffOn_univ (mem_univ x) i

/--
theorem `ContinuousLinearEquiv.comp_contDiffWithinAt_iff` / 定理 `ContinuousLinearEquiv.comp_contDiffWithinAt_iff`

English:
theorem ContinuousLinearEquiv.comp_contDiffWithinAt_iff
  given: (e : F ≃L[𝕜] G)
  proof: ⟨fun H => by
    simpa only [Function.comp_def, e.symm.coe_coe, e.symm_apply_apply] using
      H.continuousLinearMap_comp (e.symm : G ->L[𝕜] F),
    fun H => H.continuousLinearMap_comp (e : F ->L[𝕜] G)⟩

中文:
定理 连续线性等价.comp_contDiffWithinAt_iff
  条件: (e : F ≃L[𝕜] G)
  证明: ⟨fun H => by
    simpa only [Function.comp_def, e.symm.coe_coe, e.symm_apply_apply] using
      H.continuousLinearMap_comp (e.symm : G ->L[𝕜] F),
    fun H => H.continuousLinearMap_comp (e : F ->L[𝕜] G)⟩

Depends on / 依赖: Function, Function.comp_def, H.continuousLinearMap_comp, coe_coe, comp_def, continuousLinearMap_comp, e.symm, e.symm.coe_coe, e.symm_apply_apply, symm_apply_apply
-/
theorem ContinuousLinearEquiv.comp_contDiffWithinAt_iff (e : F ≃L[𝕜] G) :
    ContDiffWithinAt 𝕜 n (e ∘ f) s x ↔ ContDiffWithinAt 𝕜 n f s x :=
  ⟨fun H => by
    simpa only [Function.comp_def, e.symm.coe_coe, e.symm_apply_apply] using
      H.continuousLinearMap_comp (e.symm : G ->L[𝕜] F),
    fun H => H.continuousLinearMap_comp (e : F ->L[𝕜] G)⟩

/--
theorem `ContinuousLinearEquiv.comp_contDiffAt_iff` / 定理 `ContinuousLinearEquiv.comp_contDiffAt_iff`

English:
theorem ContinuousLinearEquiv.comp_contDiffAt_iff
  given: (e : F ≃L[𝕜] G)
  proof: by
  simp only [← contDiffWithinAt_univ, e.comp_contDiffWithinAt_iff]

中文:
定理 连续线性等价.comp_contDiffAt_iff
  条件: (e : F ≃L[𝕜] G)
  证明: by
  simp only [← contDiffWithinAt_univ, e.comp_contDiffWithinAt_iff]

Depends on / 依赖: comp_contDiffWithinAt_iff, contDiffWithinAt_univ, e.comp_contDiffWithinAt_iff
-/
theorem ContinuousLinearEquiv.comp_contDiffAt_iff (e : F ≃L[𝕜] G) :
    ContDiffAt 𝕜 n (e ∘ f) x ↔ ContDiffAt 𝕜 n f x := by
  simp only [← contDiffWithinAt_univ, e.comp_contDiffWithinAt_iff]

/--
theorem `ContinuousLinearEquiv.comp_contDiffOn_iff` / 定理 `ContinuousLinearEquiv.comp_contDiffOn_iff`

English:
theorem ContinuousLinearEquiv.comp_contDiffOn_iff
  given: (e : F ≃L[𝕜] G)
  proof: by
  simp [ContDiffOn, e.comp_contDiffWithinAt_iff]

中文:
定理 连续线性等价.comp_contDiffOn_iff
  条件: (e : F ≃L[𝕜] G)
  证明: by
  simp [ContDiffOn, e.comp_contDiffWithinAt_iff]

Depends on / 依赖: ContDiffOn, comp_contDiffWithinAt_iff, e.comp_contDiffWithinAt_iff
-/
theorem ContinuousLinearEquiv.comp_contDiffOn_iff (e : F ≃L[𝕜] G) :
    ContDiffOn 𝕜 n (e ∘ f) s ↔ ContDiffOn 𝕜 n f s := by
  simp [ContDiffOn, e.comp_contDiffWithinAt_iff]

/--
theorem `ContinuousLinearEquiv.comp_contDiff_iff` / 定理 `ContinuousLinearEquiv.comp_contDiff_iff`

English:
theorem ContinuousLinearEquiv.comp_contDiff_iff
  given: (e : F ≃L[𝕜] G)
  proof: by
  simp only [← contDiffOn_univ, e.comp_contDiffOn_iff]

中文:
定理 连续线性等价.comp_contDiff_iff
  条件: (e : F ≃L[𝕜] G)
  证明: by
  simp only [← contDiffOn_univ, e.comp_contDiffOn_iff]

Depends on / 依赖: comp_contDiffOn_iff, contDiffOn_univ, e.comp_contDiffOn_iff
-/
theorem ContinuousLinearEquiv.comp_contDiff_iff (e : F ≃L[𝕜] G) :
    ContDiff 𝕜 n (e ∘ f) ↔ ContDiff 𝕜 n f := by
  simp only [← contDiffOn_univ, e.comp_contDiffOn_iff]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `HasFTaylorSeriesUpToOn.comp_continuousAffineMap` / 定理 `HasFTaylorSeriesUpToOn.comp_continuousAffineMap`

English:
theorem HasFTaylorSeriesUpToOn.comp_continuousAffineMap
  proof: by
  let A : forall m : Nat, (E [×m]->L[𝕜] F) -> G [×m]->L[𝕜] F :=
    fun m h => h.compContinuousLinearMap fun _ => g.contLinear
  have hA : forall m, IsBoundedLinearMap 𝕜 (A m) := fun m =>
    isBoundedLinearMap_continuousMultilinearMap_comp_linear g.contLinear
  constructor
  · intro x hx
    simp only [(hf.zero_eq (g x) hx).symm, Function.comp_apply]
    change (p (g x) 0 fun _ : Fin 0 => g.contLinear 0) = p (g x) 0 0
    rw [map_zero]
    rfl
  · intro m hm x hx
    convert!
      (hA m).hasFDerivAt.comp_hasFDerivWithinAt x
        ((hf.fderivWithin m hm (g x) hx).comp x g.hasFDerivWithinAt (Subset.refl _))
    ext y v
    change p (g x) (Nat.succ m) (g.contLinear ∘ cons y v)
      = p (g x) m.succ (cons (g.contLinear y) (g.contLinear ∘ v))
    rw [comp_cons]
  · intro m hm
exact (hA m).continuous.comp_continuousOn (hf.cont m hm).comp g.continuous.continuousOn
      Subset.refl _

中文:
定理 有FTaylorSeriesUpToOn.comp_continuousAffineMap
  证明: by
  let A : forall m : Nat, (E [×m]->L[𝕜] F) -> G [×m]->L[𝕜] F :=
    fun m h => h.compContinuousLinearMap fun _ => g.contLinear
  have hA : forall m, IsBoundedLinearMap 𝕜 (A m) := fun m =>
    isBoundedLinearMap_continuousMultilinearMap_comp_linear g.contLinear
  constructor
  · intro x hx
    simp only [(hf.zero_eq (g x) hx).symm, Function.comp_apply]
    change (p (g x) 0 fun _ : Fin 0 => g.contLinear 0) = p (g x) 0 0
    rw [map_zero]
    rfl
  · intro m hm x hx
    convert!
      (hA m).hasFDerivAt.comp_hasFDerivWithinAt x
        ((hf.fderivWithin m hm (g x) hx).comp x g.hasFDerivWithinAt (Subset.refl _))
    ext y v
    change p (g x) (Nat.succ m) (g.contLinear ∘ cons y v)
      = p (g x) m.succ (cons (g.contLinear y) (g.contLinear ∘ v))
    rw [comp_cons]
  · intro m hm
exact (hA m).continuous.comp_continuousOn (hf.cont m hm).comp g.continuous.continuousOn
      Subset.refl _

Depends on / 依赖: Function, Function.comp_apply, IsBoundedLinearMap, compContinuousLinearMap, comp_apply, comp_hasFDerivWithinAt, contLinear, convert, g.contLinear, h.compContinuousLinearMap, hasFDerivAt, hasFDerivAt.comp_hasFDerivWithinAt, hf.fder, hf.zero_eq, isBoundedLinearMap_continuousMultilinearMap_comp_linear, map_zero, zero_eq
-/
theorem HasFTaylorSeriesUpToOn.comp_continuousAffineMap
    (hf : HasFTaylorSeriesUpToOn n f p s) (g : G ->ᴬ[𝕜] E) :
    HasFTaylorSeriesUpToOn n (f ∘ g)
      (fun x k => (p (g x) k).compContinuousLinearMap fun _ => g.contLinear) (g ⁻¹' s) := by
  let A : forall m : Nat, (E [×m]->L[𝕜] F) -> G [×m]->L[𝕜] F :=
    fun m h => h.compContinuousLinearMap fun _ => g.contLinear
  have hA : forall m, IsBoundedLinearMap 𝕜 (A m) := fun m =>
    isBoundedLinearMap_continuousMultilinearMap_comp_linear g.contLinear
  constructor
  · intro x hx
    simp only [(hf.zero_eq (g x) hx).symm, Function.comp_apply]
    change (p (g x) 0 fun _ : Fin 0 => g.contLinear 0) = p (g x) 0 0
    rw [map_zero]
    rfl
  · intro m hm x hx
    convert!
      (hA m).hasFDerivAt.comp_hasFDerivWithinAt x
        ((hf.fderivWithin m hm (g x) hx).comp x g.hasFDerivWithinAt (Subset.refl _))
    ext y v
    change p (g x) (Nat.succ m) (g.contLinear ∘ cons y v)
      = p (g x) m.succ (cons (g.contLinear y) (g.contLinear ∘ v))
    rw [comp_cons]
  · intro m hm
exact (hA m).continuous.comp_continuousOn (hf.cont m hm).comp g.continuous.continuousOn
      Subset.refl _

/--
theorem `HasFTaylorSeriesUpToOn.compContinuousLinearMap` / 定理 `HasFTaylorSeriesUpToOn.compContinuousLinearMap`

English:
theorem HasFTaylorSeriesUpToOn.compContinuousLinearMap
  proof: hf.comp_continuousAffineMap g.toContinuousAffineMap

中文:
定理 有FTaylorSeriesUpToOn.compContinuousLinearMap
  证明: hf.comp_continuousAffineMap g.toContinuousAffineMap

Depends on / 依赖: comp_continuousAffineMap, g.toContinuousAffineMap, hf.comp_continuousAffineMap, toContinuousAffineMap
-/
theorem HasFTaylorSeriesUpToOn.compContinuousLinearMap
    (hf : HasFTaylorSeriesUpToOn n f p s) (g : G ->L[𝕜] E) :
    HasFTaylorSeriesUpToOn n (f ∘ g)
      (fun x k => (p (g x) k).compContinuousLinearMap fun _ => g) (g ⁻¹' s) :=
  hf.comp_continuousAffineMap g.toContinuousAffineMap

/--
theorem `ContDiffWithinAt.comp_continuousLinearMap` / 定理 `ContDiffWithinAt.comp_continuousLinearMap`

English:
theorem ContDiffWithinAt.comp_continuousLinearMap
  statement: {x : G} (g : G ->L[𝕜] E)
  proof: by
  match n with
  | ω =>
    obtain ⟨u, hu, p, hp, h'p⟩ := hf
    refine ⟨g ⁻¹' u, ?_, _, hp.compContinuousLinearMap g, ?_⟩
    · refine g.continuous.continuousWithinAt.tendsto_nhdsWithin ?_ hu
      exact (mapsTo_singleton.2 <| mem_singleton _).union_union (mapsTo_preimage _ _)
    · intro i
      change AnalyticOn 𝕜 (fun x =>
        ContinuousMultilinearMap.compContinuousLinearMapL (fun _ => g) (p (g x) i)) (⇑g ⁻¹' u)
      apply AnalyticOn.comp _ _ (Set.mapsTo_univ _ _)
      · exact ContinuousLinearMap.analyticOn _ _
      · exact (h'p i).comp (g.analyticOn _) (mapsTo_preimage _ _)
  | (n : Nat∞) =>
    intro m hm
    rcases hf m hm with ⟨u, hu, p, hp⟩
    refine ⟨g ⁻¹' u, ?_, _, hp.compContinuousLinearMap g⟩
    refine g.continuous.continuousWithinAt.tendsto_nhdsWithin ?_ hu
    exact (mapsTo_singleton.2 <| mem_singleton _).union_union (mapsTo_preimage _ _)

中文:
定理 ContDiffWithinAt.comp_continuousLinearMap
  结论: {x : G} (g : G ->L[𝕜] E)
  证明: by
  match n with
  | ω =>
    obtain ⟨u, hu, p, hp, h'p⟩ := hf
    refine ⟨g ⁻¹' u, ?_, _, hp.compContinuousLinearMap g, ?_⟩
    · refine g.continuous.continuousWithinAt.tendsto_nhdsWithin ?_ hu
      exact (mapsTo_singleton.2 <| mem_singleton _).union_union (mapsTo_preimage _ _)
    · intro i
      change AnalyticOn 𝕜 (fun x =>
        ContinuousMultilinearMap.compContinuousLinearMapL (fun _ => g) (p (g x) i)) (⇑g ⁻¹' u)
      apply AnalyticOn.comp _ _ (Set.mapsTo_univ _ _)
      · exact ContinuousLinearMap.analyticOn _ _
      · exact (h'p i).comp (g.analyticOn _) (mapsTo_preimage _ _)
  | (n : Nat∞) =>
    intro m hm
    rcases hf m hm with ⟨u, hu, p, hp⟩
    refine ⟨g ⁻¹' u, ?_, _, hp.compContinuousLinearMap g⟩
    refine g.continuous.continuousWithinAt.tendsto_nhdsWithin ?_ hu
    exact (mapsTo_singleton.2 <| mem_singleton _).union_union (mapsTo_preimage _ _)

Depends on / 依赖: AnalyticOn, AnalyticOn.comp, ContinuousLinearMap, ContinuousLinearMap.analyticOn, ContinuousMultilinearMap, ContinuousMultilinearMap.compContinuousLinearMapL, Set.mapsTo_univ, analyticOn, compContinuousLinearMap, compContinuousLinearMapL, continuous, continuousWithinAt, g.continuous.continuousWithinAt.tendsto_nhdsWithin, hp.compContinuousLinearMap, mapsTo_preimage, mapsTo_singleton, mapsTo_univ, mem_singleton, tendsto_nhdsWithin, union_union
-/
theorem ContDiffWithinAt.comp_continuousLinearMap {x : G} (g : G ->L[𝕜] E)
    (hf : ContDiffWithinAt 𝕜 n f s (g x)) : ContDiffWithinAt 𝕜 n (f ∘ g) (g ⁻¹' s) x := by
  match n with
  | ω =>
    obtain ⟨u, hu, p, hp, h'p⟩ := hf
    refine ⟨g ⁻¹' u, ?_, _, hp.compContinuousLinearMap g, ?_⟩
    · refine g.continuous.continuousWithinAt.tendsto_nhdsWithin ?_ hu
      exact (mapsTo_singleton.2 <| mem_singleton _).union_union (mapsTo_preimage _ _)
    · intro i
      change AnalyticOn 𝕜 (fun x =>
        ContinuousMultilinearMap.compContinuousLinearMapL (fun _ => g) (p (g x) i)) (⇑g ⁻¹' u)
      apply AnalyticOn.comp _ _ (Set.mapsTo_univ _ _)
      · exact ContinuousLinearMap.analyticOn _ _
      · exact (h'p i).comp (g.analyticOn _) (mapsTo_preimage _ _)
  | (n : Nat∞) =>
    intro m hm
    rcases hf m hm with ⟨u, hu, p, hp⟩
    refine ⟨g ⁻¹' u, ?_, _, hp.compContinuousLinearMap g⟩
    refine g.continuous.continuousWithinAt.tendsto_nhdsWithin ?_ hu
    exact (mapsTo_singleton.2 <| mem_singleton _).union_union (mapsTo_preimage _ _)

/--
theorem `ContDiffOn.comp_continuousLinearMap` / 定理 `ContDiffOn.comp_continuousLinearMap`

English:
theorem ContDiffOn.comp_continuousLinearMap
  given: (hf : ContDiffOn 𝕜 n f s) (g : G ->L[𝕜] E)
  proof: fun x hx => (hf (g x) hx).comp_continuousLinearMap g

中文:
定理 ContDiffOn.comp_continuousLinearMap
  条件: (hf : ContDiffOn 𝕜 n f s) (g : G ->L[𝕜] E)
  证明: fun x hx => (hf (g x) hx).comp_continuousLinearMap g

Depends on / 依赖: comp_continuousLinearMap
-/
theorem ContDiffOn.comp_continuousLinearMap (hf : ContDiffOn 𝕜 n f s) (g : G ->L[𝕜] E) :
    ContDiffOn 𝕜 n (f ∘ g) (g ⁻¹' s) := fun x hx => (hf (g x) hx).comp_continuousLinearMap g

/--
theorem `ContDiff.comp_continuousLinearMap` / 定理 `ContDiff.comp_continuousLinearMap`

English:
theorem ContDiff.comp_continuousLinearMap
  given: {f : E -> F} {g : G ->L[𝕜] E} (hf : ContDiff 𝕜 n f)
  proof: contDiffOn_univ.1 ContDiffOn.comp_continuousLinearMap (contDiffOn_univ.2 hf) _

中文:
定理 连续可微.comp_continuousLinearMap
  条件: {f : E -> F} {g : G ->L[𝕜] E} (hf : 连续可微 𝕜 n f)
  证明: contDiffOn_univ.1 ContDiffOn.comp_continuousLinearMap (contDiffOn_univ.2 hf) _

Depends on / 依赖: ContDiffOn, ContDiffOn.comp_continuousLinearMap, comp_continuousLinearMap, contDiffOn_univ
-/
theorem ContDiff.comp_continuousLinearMap {f : E -> F} {g : G ->L[𝕜] E} (hf : ContDiff 𝕜 n f) :
    ContDiff 𝕜 n (f ∘ g) :=
contDiffOn_univ.1 ContDiffOn.comp_continuousLinearMap (contDiffOn_univ.2 hf) _

/--
theorem `ContinuousLinearMap.iteratedFDerivWithin_comp_right` / 定理 `ContinuousLinearMap.iteratedFDerivWithin_comp_right`

English:
theorem ContinuousLinearMap.iteratedFDerivWithin_comp_right
  statement: {f : E -> F} (g : G ->L[𝕜] E)
  proof: ((((hf.of_le hi).ftaylorSeriesWithin hs).compContinuousLinearMap
    g).eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl h's hx).symm

中文:
定理 连续线性映射.iteratedFDerivWithin_comp_right
  结论: {f : E -> F} (g : G ->L[𝕜] E)
  证明: ((((hf.of_le hi).ftaylorSeriesWithin hs).compContinuousLinearMap
    g).eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl h's hx).symm

Depends on / 依赖: compContinuousLinearMap, eq_iteratedFDerivWithin_of_uniqueDiffOn, ftaylorSeriesWithin, hf.of_le, le_rfl, of_le
-/
theorem ContinuousLinearMap.iteratedFDerivWithin_comp_right {f : E -> F} (g : G ->L[𝕜] E)
    (hf : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s) (h's : UniqueDiffOn 𝕜 (g ⁻¹' s)) {x : G}
    (hx : g x in s) {i : Nat} (hi : i <= n) :
    iteratedFDerivWithin 𝕜 i (f ∘ g) (g ⁻¹' s) x =
      (iteratedFDerivWithin 𝕜 i f s (g x)).compContinuousLinearMap fun _ => g :=
  ((((hf.of_le hi).ftaylorSeriesWithin hs).compContinuousLinearMap
    g).eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl h's hx).symm

/--
theorem `ContinuousLinearEquiv.iteratedFDerivWithin_comp_right` / 定理 `ContinuousLinearEquiv.iteratedFDerivWithin_comp_right`

English:
theorem ContinuousLinearEquiv.iteratedFDerivWithin_comp_right
  statement: (g : G ≃L[𝕜] E) (f : E -> F)
  proof: by
  induction i generalizing x with ext1 m
  | zero =>
    simp only [iteratedFDerivWithin_zero_apply, comp_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply]
  | succ i IH =>
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousLinearEquiv.coe_coe, iteratedFDerivWithin_succ_apply_left]
    have : fderivWithin 𝕜 (iteratedFDerivWithin 𝕜 i (f ∘ g) (g ⁻¹' s)) (g ⁻¹' s) x =
        fderivWithin 𝕜
          (ContinuousLinearEquiv.continuousMultilinearMapCongrLeft _ (fun _x : Fin i => g) ∘
            (iteratedFDerivWithin 𝕜 i f s ∘ g)) (g ⁻¹' s) x :=
      fderivWithin_congr' (@IH) hx
    rw [this]; rw [ContinuousLinearEquiv.comp_fderivWithin _ (g.uniqueDiffOn_preimage_iff.2 hs x hx)]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.continuousMultilinearMapCongrLeft_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply]
    rw [ContinuousLinearEquiv.comp_right_fderivWithin _ (g.uniqueDiffOn_preimage_iff.2 hs x hx)]; rw [ContinuousLinearMap.comp_apply]; rw [coe_coe]; rw [tail_def]; rw [tail_def]

中文:
定理 连续线性等价.iteratedFDerivWithin_comp_right
  结论: (g : G ≃L[𝕜] E) (f : E -> F)
  证明: by
  induction i generalizing x with ext1 m
  | zero =>
    simp only [iteratedFDerivWithin_zero_apply, comp_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply]
  | succ i IH =>
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousLinearEquiv.coe_coe, iteratedFDerivWithin_succ_apply_left]
    have : fderivWithin 𝕜 (iteratedFDerivWithin 𝕜 i (f ∘ g) (g ⁻¹' s)) (g ⁻¹' s) x =
        fderivWithin 𝕜
          (ContinuousLinearEquiv.continuousMultilinearMapCongrLeft _ (fun _x : Fin i => g) ∘
            (iteratedFDerivWithin 𝕜 i f s ∘ g)) (g ⁻¹' s) x :=
      fderivWithin_congr' (@IH) hx
    rw [this]; rw [ContinuousLinearEquiv.comp_fderivWithin _ (g.uniqueDiffOn_preimage_iff.2 hs x hx)]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.continuousMultilinearMapCongrLeft_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply]
    rw [ContinuousLinearEquiv.comp_right_fderivWithin _ (g.uniqueDiffOn_preimage_iff.2 hs x hx)]; rw [ContinuousLinearMap.comp_apply]; rw [coe_coe]; rw [tail_def]; rw [tail_def]

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.continuousMultilinearMapCongrLeft, ContinuousMultilinearMap, ContinuousMultilinearMap.compContinuousLinearMap_apply, coe_coe, compContinuousLinearMap_apply, comp_apply, continuousMultilinearMapCongrLeft, fderivWithin, generalizing, iteratedFDerivWithin, iteratedFDerivWithin_succ_apply_left, iteratedFDerivWithin_zero_apply
-/
theorem ContinuousLinearEquiv.iteratedFDerivWithin_comp_right (g : G ≃L[𝕜] E) (f : E -> F)
    (hs : UniqueDiffOn 𝕜 s) {x : G} (hx : g x in s) (i : Nat) :
    iteratedFDerivWithin 𝕜 i (f ∘ g) (g ⁻¹' s) x =
      (iteratedFDerivWithin 𝕜 i f s (g x)).compContinuousLinearMap fun _ => g := by
  induction i generalizing x with ext1 m
  | zero =>
    simp only [iteratedFDerivWithin_zero_apply, comp_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply]
  | succ i IH =>
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousLinearEquiv.coe_coe, iteratedFDerivWithin_succ_apply_left]
    have : fderivWithin 𝕜 (iteratedFDerivWithin 𝕜 i (f ∘ g) (g ⁻¹' s)) (g ⁻¹' s) x =
        fderivWithin 𝕜
          (ContinuousLinearEquiv.continuousMultilinearMapCongrLeft _ (fun _x : Fin i => g) ∘
            (iteratedFDerivWithin 𝕜 i f s ∘ g)) (g ⁻¹' s) x :=
      fderivWithin_congr' (@IH) hx
    rw [this]; rw [ContinuousLinearEquiv.comp_fderivWithin _ (g.uniqueDiffOn_preimage_iff.2 hs x hx)]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.continuousMultilinearMapCongrLeft_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply]
    rw [ContinuousLinearEquiv.comp_right_fderivWithin _ (g.uniqueDiffOn_preimage_iff.2 hs x hx)]; rw [ContinuousLinearMap.comp_apply]; rw [coe_coe]; rw [tail_def]; rw [tail_def]

/--
theorem `ContinuousLinearMap.iteratedFDeriv_comp_right` / 定理 `ContinuousLinearMap.iteratedFDeriv_comp_right`

English:
theorem ContinuousLinearMap.iteratedFDeriv_comp_right
  statement: (g : G ->L[𝕜] E) {f : E -> F}
  proof: by
  simp only [← iteratedFDerivWithin_univ]
  exact g.iteratedFDerivWithin_comp_right hf.contDiffOn uniqueDiffOn_univ uniqueDiffOn_univ
      (mem_univ _) hi

中文:
定理 连续线性映射.iteratedFDeriv_comp_right
  结论: (g : G ->L[𝕜] E) {f : E -> F}
  证明: by
  simp only [← iteratedFDerivWithin_univ]
  exact g.iteratedFDerivWithin_comp_right hf.contDiffOn uniqueDiffOn_univ uniqueDiffOn_univ
      (mem_univ _) hi

Depends on / 依赖: contDiffOn, g.iteratedFDerivWithin_comp_right, hf.contDiffOn, iteratedFDerivWithin_comp_right, iteratedFDerivWithin_univ, mem_univ, uniqueDiffOn_univ
-/
theorem ContinuousLinearMap.iteratedFDeriv_comp_right (g : G ->L[𝕜] E) {f : E -> F}
    (hf : ContDiff 𝕜 n f) (x : G) {i : Nat} (hi : i <= n) :
    iteratedFDeriv 𝕜 i (f ∘ g) x =
      (iteratedFDeriv 𝕜 i f (g x)).compContinuousLinearMap fun _ => g := by
  simp only [← iteratedFDerivWithin_univ]
  exact g.iteratedFDerivWithin_comp_right hf.contDiffOn uniqueDiffOn_univ uniqueDiffOn_univ
      (mem_univ _) hi

/--
theorem `LinearIsometryEquiv.norm_iteratedFDerivWithin_comp_right` / 定理 `LinearIsometryEquiv.norm_iteratedFDerivWithin_comp_right`

English:
theorem LinearIsometryEquiv.norm_iteratedFDerivWithin_comp_right
  statement: (g : G ≃ₗᵢ[𝕜] E) (f : E -> F)
  proof: by
  have : iteratedFDerivWithin 𝕜 i (f ∘ g) (g ⁻¹' s) x =
      (iteratedFDerivWithin 𝕜 i f s (g x)).compContinuousLinearMap fun _ => g :=
    g.toContinuousLinearEquiv.iteratedFDerivWithin_comp_right f hs hx i
  rw [this]; rw [ContinuousMultilinearMap.norm_compContinuous_linearIsometryEquiv]

中文:
定理 线性等距等价.norm_iteratedFDerivWithin_comp_right
  结论: (g : G ≃ₗᵢ[𝕜] E) (f : E -> F)
  证明: by
  have : iteratedFDerivWithin 𝕜 i (f ∘ g) (g ⁻¹' s) x =
      (iteratedFDerivWithin 𝕜 i f s (g x)).compContinuousLinearMap fun _ => g :=
    g.toContinuousLinearEquiv.iteratedFDerivWithin_comp_right f hs hx i
  rw [this]; rw [ContinuousMultilinearMap.norm_compContinuous_linearIsometryEquiv]

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.norm_compContinuous_linearIsometryEquiv, compContinuousLinearMap, g.toContinuousLinearEquiv.iteratedFDerivWithin_comp_right, iteratedFDerivWithin, iteratedFDerivWithin_comp_right, norm_compContinuous_linearIsometryEquiv, toContinuousLinearEquiv
-/
theorem LinearIsometryEquiv.norm_iteratedFDerivWithin_comp_right (g : G ≃ₗᵢ[𝕜] E) (f : E -> F)
    (hs : UniqueDiffOn 𝕜 s) {x : G} (hx : g x in s) (i : Nat) :
    ‖iteratedFDerivWithin 𝕜 i (f ∘ g) (g ⁻¹' s) x‖ = ‖iteratedFDerivWithin 𝕜 i f s (g x)‖ := by
  have : iteratedFDerivWithin 𝕜 i (f ∘ g) (g ⁻¹' s) x =
      (iteratedFDerivWithin 𝕜 i f s (g x)).compContinuousLinearMap fun _ => g :=
    g.toContinuousLinearEquiv.iteratedFDerivWithin_comp_right f hs hx i
  rw [this]; rw [ContinuousMultilinearMap.norm_compContinuous_linearIsometryEquiv]

/--
theorem `LinearIsometryEquiv.norm_iteratedFDeriv_comp_right` / 定理 `LinearIsometryEquiv.norm_iteratedFDeriv_comp_right`

English:
theorem LinearIsometryEquiv.norm_iteratedFDeriv_comp_right
  statement: (g : G ≃ₗᵢ[𝕜] E) (f : E -> F) (x : G)
  proof: by
  simp only [← iteratedFDerivWithin_univ]
  apply g.norm_iteratedFDerivWithin_comp_right f uniqueDiffOn_univ (mem_univ (g x)) i

中文:
定理 线性等距等价.norm_iteratedFDeriv_comp_right
  结论: (g : G ≃ₗᵢ[𝕜] E) (f : E -> F) (x : G)
  证明: by
  simp only [← iteratedFDerivWithin_univ]
  apply g.norm_iteratedFDerivWithin_comp_right f uniqueDiffOn_univ (mem_univ (g x)) i

Depends on / 依赖: g.norm_iteratedFDerivWithin_comp_right, iteratedFDerivWithin_univ, mem_univ, norm_iteratedFDerivWithin_comp_right, uniqueDiffOn_univ
-/
theorem LinearIsometryEquiv.norm_iteratedFDeriv_comp_right (g : G ≃ₗᵢ[𝕜] E) (f : E -> F) (x : G)
    (i : Nat) : ‖iteratedFDeriv 𝕜 i (f ∘ g) x‖ = ‖iteratedFDeriv 𝕜 i f (g x)‖ := by
  simp only [← iteratedFDerivWithin_univ]
  apply g.norm_iteratedFDerivWithin_comp_right f uniqueDiffOn_univ (mem_univ (g x)) i

/--
theorem `ContinuousLinearEquiv.contDiffWithinAt_comp_iff` / 定理 `ContinuousLinearEquiv.contDiffWithinAt_comp_iff`

English:
theorem ContinuousLinearEquiv.contDiffWithinAt_comp_iff
  given: (e : G ≃L[𝕜] E)
  proof: by
  constructor
  · intro H
    simpa [← preimage_comp, Function.comp_def] using H.comp_continuousLinearMap (e.symm : E ->L[𝕜] G)
  · intro H
    rw [← e.apply_symm_apply x]; rw [← e.coe_coe] at H
    exact H.comp_continuousLinearMap _

中文:
定理 连续线性等价.contDiffWithinAt_comp_iff
  条件: (e : G ≃L[𝕜] E)
  证明: by
  constructor
  · intro H
    simpa [← preimage_comp, Function.comp_def] using H.comp_continuousLinearMap (e.symm : E ->L[𝕜] G)
  · intro H
    rw [← e.apply_symm_apply x]; rw [← e.coe_coe] at H
    exact H.comp_continuousLinearMap _

Depends on / 依赖: Function, Function.comp_def, H.comp_continuousLinearMap, apply_symm_apply, coe_coe, comp_continuousLinearMap, comp_def, e.apply_symm_apply, e.coe_coe, e.symm, preimage_comp
-/
theorem ContinuousLinearEquiv.contDiffWithinAt_comp_iff (e : G ≃L[𝕜] E) :
    ContDiffWithinAt 𝕜 n (f ∘ e) (e ⁻¹' s) (e.symm x) ↔ ContDiffWithinAt 𝕜 n f s x := by
  constructor
  · intro H
    simpa [← preimage_comp, Function.comp_def] using H.comp_continuousLinearMap (e.symm : E ->L[𝕜] G)
  · intro H
    rw [← e.apply_symm_apply x]; rw [← e.coe_coe] at H
    exact H.comp_continuousLinearMap _

/--
theorem `ContinuousLinearEquiv.contDiffAt_comp_iff` / 定理 `ContinuousLinearEquiv.contDiffAt_comp_iff`

English:
theorem ContinuousLinearEquiv.contDiffAt_comp_iff
  given: (e : G ≃L[𝕜] E)
  proof: by
  rw [← contDiffWithinAt_univ]; rw [← contDiffWithinAt_univ]; rw [← preimage_univ]
  exact e.contDiffWithinAt_comp_iff

中文:
定理 连续线性等价.contDiffAt_comp_iff
  条件: (e : G ≃L[𝕜] E)
  证明: by
  rw [← contDiffWithinAt_univ]; rw [← contDiffWithinAt_univ]; rw [← preimage_univ]
  exact e.contDiffWithinAt_comp_iff

Depends on / 依赖: contDiffWithinAt_comp_iff, contDiffWithinAt_univ, e.contDiffWithinAt_comp_iff, preimage_univ
-/
theorem ContinuousLinearEquiv.contDiffAt_comp_iff (e : G ≃L[𝕜] E) :
    ContDiffAt 𝕜 n (f ∘ e) (e.symm x) ↔ ContDiffAt 𝕜 n f x := by
  rw [← contDiffWithinAt_univ]; rw [← contDiffWithinAt_univ]; rw [← preimage_univ]
  exact e.contDiffWithinAt_comp_iff

/--
theorem `ContinuousLinearEquiv.contDiffOn_comp_iff` / 定理 `ContinuousLinearEquiv.contDiffOn_comp_iff`

English:
theorem ContinuousLinearEquiv.contDiffOn_comp_iff
  given: (e : G ≃L[𝕜] E)
  proof: ⟨fun H => by simpa [Function.comp_def] using H.comp_continuousLinearMap (e.symm : E ->L[𝕜] G),
    fun H => H.comp_continuousLinearMap (e : G ->L[𝕜] E)⟩

中文:
定理 连续线性等价.contDiffOn_comp_iff
  条件: (e : G ≃L[𝕜] E)
  证明: ⟨fun H => by simpa [Function.comp_def] using H.comp_continuousLinearMap (e.symm : E ->L[𝕜] G),
    fun H => H.comp_continuousLinearMap (e : G ->L[𝕜] E)⟩

Depends on / 依赖: Function, Function.comp_def, H.comp_continuousLinearMap, comp_continuousLinearMap, comp_def, e.symm
-/
theorem ContinuousLinearEquiv.contDiffOn_comp_iff (e : G ≃L[𝕜] E) :
    ContDiffOn 𝕜 n (f ∘ e) (e ⁻¹' s) ↔ ContDiffOn 𝕜 n f s :=
  ⟨fun H => by simpa [Function.comp_def] using H.comp_continuousLinearMap (e.symm : E ->L[𝕜] G),
    fun H => H.comp_continuousLinearMap (e : G ->L[𝕜] E)⟩

/--
theorem `ContinuousLinearEquiv.contDiff_comp_iff` / 定理 `ContinuousLinearEquiv.contDiff_comp_iff`

English:
theorem ContinuousLinearEquiv.contDiff_comp_iff
  given: (e : G ≃L[𝕜] E)
  proof: by
  rw [← contDiffOn_univ]; rw [← contDiffOn_univ]; rw [← preimage_univ]
  exact e.contDiffOn_comp_iff

中文:
定理 连续线性等价.contDiff_comp_iff
  条件: (e : G ≃L[𝕜] E)
  证明: by
  rw [← contDiffOn_univ]; rw [← contDiffOn_univ]; rw [← preimage_univ]
  exact e.contDiffOn_comp_iff

Depends on / 依赖: contDiffOn_comp_iff, contDiffOn_univ, e.contDiffOn_comp_iff, preimage_univ
-/
theorem ContinuousLinearEquiv.contDiff_comp_iff (e : G ≃L[𝕜] E) :
    ContDiff 𝕜 n (f ∘ e) ↔ ContDiff 𝕜 n f := by
  rw [← contDiffOn_univ]; rw [← contDiffOn_univ]; rw [← preimage_univ]
  exact e.contDiffOn_comp_iff

end linear

/-! ### The Cartesian product of two C^n functions is C^n. -/
section prod

/--
theorem `HasFTaylorSeriesUpToOn.prodMk` / 定理 `HasFTaylorSeriesUpToOn.prodMk`

English:
theorem HasFTaylorSeriesUpToOn.prodMk
  statement: {n : Nat∞ω}
  proof: by
  set L := fun m => ContinuousMultilinearMap.prodL 𝕜 (fun _ : Fin m => E) F G
  constructor
  · intro x hx; rw [← hf.zero_eq x hx, ← hg.zero_eq x hx]; rfl
  · intro m hm x hx
    convert!
      (L m).hasFDerivAt.comp_hasFDerivWithinAt x
        ((hf.fderivWithin m hm x hx).prodMk (hg.fderivWithin m hm x hx))
  · intro m hm
    exact (L m).continuous.comp_continuousOn ((hf.cont m hm).prodMk (hg.cont m hm))

中文:
定理 有FTaylorSeriesUpToOn.prodMk
  结论: {n : 自然数∞ω}
  证明: by
  set L := fun m => ContinuousMultilinearMap.prodL 𝕜 (fun _ : Fin m => E) F G
  constructor
  · intro x hx; rw [← hf.zero_eq x hx, ← hg.zero_eq x hx]; rfl
  · intro m hm x hx
    convert!
      (L m).hasFDerivAt.comp_hasFDerivWithinAt x
        ((hf.fderivWithin m hm x hx).prodMk (hg.fderivWithin m hm x hx))
  · intro m hm
    exact (L m).continuous.comp_continuousOn ((hf.cont m hm).prodMk (hg.cont m hm))

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.prodL, comp_continuousOn, comp_hasFDerivWithinAt, continuous, continuous.comp_continuousOn, convert, fderivWithin, hasFDerivAt, hasFDerivAt.comp_hasFDerivWithinAt, hf.cont, hf.fderivWithin, hf.zero_eq, hg.cont, hg.fderivWithin, hg.zero_eq, prodMk, zero_eq
-/
theorem HasFTaylorSeriesUpToOn.prodMk {n : Nat∞ω}
    (hf : HasFTaylorSeriesUpToOn n f p s) {g : E -> G}
    {q : E -> FormalMultilinearSeries 𝕜 E G} (hg : HasFTaylorSeriesUpToOn n g q s) :
    HasFTaylorSeriesUpToOn n (fun y => (f y, g y)) (fun y k => (p y k).prod (q y k)) s := by
  set L := fun m => ContinuousMultilinearMap.prodL 𝕜 (fun _ : Fin m => E) F G
  constructor
  · intro x hx; rw [← hf.zero_eq x hx, ← hg.zero_eq x hx]; rfl
  · intro m hm x hx
    convert!
      (L m).hasFDerivAt.comp_hasFDerivWithinAt x
        ((hf.fderivWithin m hm x hx).prodMk (hg.fderivWithin m hm x hx))
  · intro m hm
    exact (L m).continuous.comp_continuousOn ((hf.cont m hm).prodMk (hg.cont m hm))

/-- The Cartesian product of `C^n` functions at a point in a domain is `C^n`. -/
@[fun_prop]
/--
theorem `ContDiffWithinAt.prodMk` / 定理 `ContDiffWithinAt.prodMk`

English:
theorem ContDiffWithinAt.prodMk
  statement: {s : Set E} {f : E -> F} {g : E -> G}
  proof: by
  match n with
  | ω =>
    obtain ⟨u, hu, p, hp, h'p⟩ := hf
    obtain ⟨v, hv, q, hq, h'q⟩ := hg
    refine ⟨u inter v, Filter.inter_mem hu hv, _,
      (hp.mono inter_subset_left).prodMk (hq.mono inter_subset_right), fun i => ?_⟩
    change AnalyticOn 𝕜 (fun x => ContinuousMultilinearMap.prodL _ _ _ _ (p x i, q x i)) (u inter v)
    apply (LinearIsometryEquiv.analyticOnNhd _ _).comp_analyticOn _ (Set.mapsTo_univ _ _)
    exact ((h'p i).mono inter_subset_left).prod ((h'q i).mono inter_subset_right)
  | (n : Nat∞) =>
    intro m hm
    rcases hf m hm with ⟨u, hu, p, hp⟩
    rcases hg m hm with ⟨v, hv, q, hq⟩
    exact ⟨u inter v, Filter.inter_mem hu hv, _,
      (hp.mono inter_subset_left).prodMk (hq.mono inter_subset_right)⟩

中文:
定理 ContDiffWithinAt.prodMk
  结论: {s : 集合 E} {f : E -> F} {g : E -> G}
  证明: by
  match n with
  | ω =>
    obtain ⟨u, hu, p, hp, h'p⟩ := hf
    obtain ⟨v, hv, q, hq, h'q⟩ := hg
    refine ⟨u inter v, Filter.inter_mem hu hv, _,
      (hp.mono inter_subset_left).prodMk (hq.mono inter_subset_right), fun i => ?_⟩
    change AnalyticOn 𝕜 (fun x => ContinuousMultilinearMap.prodL _ _ _ _ (p x i, q x i)) (u inter v)
    apply (LinearIsometryEquiv.analyticOnNhd _ _).comp_analyticOn _ (Set.mapsTo_univ _ _)
    exact ((h'p i).mono inter_subset_left).prod ((h'q i).mono inter_subset_right)
  | (n : Nat∞) =>
    intro m hm
    rcases hf m hm with ⟨u, hu, p, hp⟩
    rcases hg m hm with ⟨v, hv, q, hq⟩
    exact ⟨u inter v, Filter.inter_mem hu hv, _,
      (hp.mono inter_subset_left).prodMk (hq.mono inter_subset_right)⟩

Depends on / 依赖: AnalyticOn, ContinuousMultilinearMap, ContinuousMultilinearMap.prodL, Filter, Filter.inter_mem, LinearIsometryEquiv, LinearIsometryEquiv.analyticOnNhd, Set.mapsTo_univ, analyticOnNhd, comp_analyticOn, hp.mono, hq.mono, inter_mem, inter_subset_left, inter_subset_right, mapsTo_univ, prodMk
-/
theorem ContDiffWithinAt.prodMk {s : Set E} {f : E -> F} {g : E -> G}
    (hf : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s x) :
    ContDiffWithinAt 𝕜 n (fun x : E => (f x, g x)) s x := by
  match n with
  | ω =>
    obtain ⟨u, hu, p, hp, h'p⟩ := hf
    obtain ⟨v, hv, q, hq, h'q⟩ := hg
    refine ⟨u inter v, Filter.inter_mem hu hv, _,
      (hp.mono inter_subset_left).prodMk (hq.mono inter_subset_right), fun i => ?_⟩
    change AnalyticOn 𝕜 (fun x => ContinuousMultilinearMap.prodL _ _ _ _ (p x i, q x i)) (u inter v)
    apply (LinearIsometryEquiv.analyticOnNhd _ _).comp_analyticOn _ (Set.mapsTo_univ _ _)
    exact ((h'p i).mono inter_subset_left).prod ((h'q i).mono inter_subset_right)
  | (n : Nat∞) =>
    intro m hm
    rcases hf m hm with ⟨u, hu, p, hp⟩
    rcases hg m hm with ⟨v, hv, q, hq⟩
    exact ⟨u inter v, Filter.inter_mem hu hv, _,
      (hp.mono inter_subset_left).prodMk (hq.mono inter_subset_right)⟩

/-- The Cartesian product of `C^n` functions on domains is `C^n`. -/
@[fun_prop]
/--
theorem `ContDiffOn.prodMk` / 定理 `ContDiffOn.prodMk`

English:
theorem ContDiffOn.prodMk
  statement: {s : Set E} {f : E -> F} {g : E -> G} (hf : ContDiffOn 𝕜 n f s)
  proof: fun x hx =>
  (hf x hx).prodMk (hg x hx)

中文:
定理 ContDiffOn.prodMk
  结论: {s : 集合 E} {f : E -> F} {g : E -> G} (hf : ContDiffOn 𝕜 n f s)
  证明: fun x hx =>
  (hf x hx).prodMk (hg x hx)
-/
theorem ContDiffOn.prodMk {s : Set E} {f : E -> F} {g : E -> G} (hf : ContDiffOn 𝕜 n f s)
    (hg : ContDiffOn 𝕜 n g s) : ContDiffOn 𝕜 n (fun x : E => (f x, g x)) s := fun x hx =>
  (hf x hx).prodMk (hg x hx)

/-- The Cartesian product of `C^n` functions at a point is `C^n`. -/
@[fun_prop]
/--
theorem `ContDiffAt.prodMk` / 定理 `ContDiffAt.prodMk`

English:
theorem ContDiffAt.prodMk
  statement: {f : E -> F} {g : E -> G} (hf : ContDiffAt 𝕜 n f x)
  proof: contDiffWithinAt_univ.1 hf.contDiffWithinAt.prodMk hg.contDiffWithinAt

中文:
定理 ContDiffAt.prodMk
  结论: {f : E -> F} {g : E -> G} (hf : ContDiffAt 𝕜 n f x)
  证明: contDiffWithinAt_univ.1 hf.contDiffWithinAt.prodMk hg.contDiffWithinAt

Depends on / 依赖: contDiffWithinAt, contDiffWithinAt_univ, hf.contDiffWithinAt.prodMk, hg.contDiffWithinAt, prodMk
-/
theorem ContDiffAt.prodMk {f : E -> F} {g : E -> G} (hf : ContDiffAt 𝕜 n f x)
    (hg : ContDiffAt 𝕜 n g x) : ContDiffAt 𝕜 n (fun x : E => (f x, g x)) x :=
contDiffWithinAt_univ.1 hf.contDiffWithinAt.prodMk hg.contDiffWithinAt

/-- The Cartesian product of `C^n` functions is `C^n`. -/
@[fun_prop]
/--
theorem `ContDiff.prodMk` / 定理 `ContDiff.prodMk`

English:
theorem ContDiff.prodMk
  given: {f : E -> F} {g : E -> G} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g)
  proof: contDiffOn_univ.1 hf.contDiffOn.prodMk hg.contDiffOn

中文:
定理 连续可微.prodMk
  条件: {f : E -> F} {g : E -> G} (hf : 连续可微 𝕜 n f) (hg : 连续可微 𝕜 n g)
  证明: contDiffOn_univ.1 hf.contDiffOn.prodMk hg.contDiffOn

Depends on / 依赖: contDiffOn, contDiffOn_univ, hf.contDiffOn.prodMk, hg.contDiffOn, prodMk
-/
theorem ContDiff.prodMk {f : E -> F} {g : E -> G} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g) :
    ContDiff 𝕜 n fun x : E => (f x, g x) :=
contDiffOn_univ.1 hf.contDiffOn.prodMk hg.contDiffOn

/--
theorem `iteratedFDerivWithin_prodMk` / 定理 `iteratedFDerivWithin_prodMk`

English:
theorem iteratedFDerivWithin_prodMk
  statement: {f : E -> F} {g : E -> G} (hf : ContDiffWithinAt 𝕜 n f s x)
  proof: by
  ext <;>
  · rw [← ContinuousLinearMap.iteratedFDerivWithin_comp_left _ (hf.prodMk hg) hs ha hi]
    simp [Function.comp_def]

中文:
定理 iteratedFDerivWithin_prodMk
  结论: {f : E -> F} {g : E -> G} (hf : ContDiffWithinAt 𝕜 n f s x)
  证明: by
  ext <;>
  · rw [← ContinuousLinearMap.iteratedFDerivWithin_comp_left _ (hf.prodMk hg) hs ha hi]
    simp [Function.comp_def]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.iteratedFDerivWithin_comp_left, Function, Function.comp_def, comp_def, hf.prodMk, iteratedFDerivWithin_comp_left, prodMk
-/
theorem iteratedFDerivWithin_prodMk {f : E -> F} {g : E -> G} (hf : ContDiffWithinAt 𝕜 n f s x)
    (hg : ContDiffWithinAt 𝕜 n g s x) (hs : UniqueDiffOn 𝕜 s) (ha : x in s) {i : Nat} (hi : i <= n) :
    iteratedFDerivWithin 𝕜 i (fun x => (f x, g x)) s x =
      (iteratedFDerivWithin 𝕜 i f s x).prod (iteratedFDerivWithin 𝕜 i g s x) := by
  ext <;>
  · rw [← ContinuousLinearMap.iteratedFDerivWithin_comp_left _ (hf.prodMk hg) hs ha hi]
    simp [Function.comp_def]

/--
theorem `iteratedFDeriv_prodMk` / 定理 `iteratedFDeriv_prodMk`

English:
theorem iteratedFDeriv_prodMk
  statement: {f : E -> F} {g : E -> G} (hf : ContDiffAt 𝕜 n f x)
  proof: by
  simp only [← iteratedFDerivWithin_univ]
  exact iteratedFDerivWithin_prodMk hf.contDiffWithinAt hg.contDiffWithinAt uniqueDiffOn_univ
    (Set.mem_univ _) hi

中文:
定理 iteratedFDeriv_prodMk
  结论: {f : E -> F} {g : E -> G} (hf : ContDiffAt 𝕜 n f x)
  证明: by
  simp only [← iteratedFDerivWithin_univ]
  exact iteratedFDerivWithin_prodMk hf.contDiffWithinAt hg.contDiffWithinAt uniqueDiffOn_univ
    (Set.mem_univ _) hi

Depends on / 依赖: Set.mem_univ, contDiffWithinAt, hf.contDiffWithinAt, hg.contDiffWithinAt, iteratedFDerivWithin_prodMk, iteratedFDerivWithin_univ, mem_univ, uniqueDiffOn_univ
-/
theorem iteratedFDeriv_prodMk {f : E -> F} {g : E -> G} (hf : ContDiffAt 𝕜 n f x)
    (hg : ContDiffAt 𝕜 n g x) {i : Nat} (hi : i <= n) :
    iteratedFDeriv 𝕜 i (fun x => (f x, g x)) x =
      (iteratedFDeriv 𝕜 i f x).prod (iteratedFDeriv 𝕜 i g x) := by
  simp only [← iteratedFDerivWithin_univ]
  exact iteratedFDerivWithin_prodMk hf.contDiffWithinAt hg.contDiffWithinAt uniqueDiffOn_univ
    (Set.mem_univ _) hi

end prod

/-! ### Being `C^k` on a union of open sets can be tested on each set -/
section contDiffOn_union

/--
lemma `ContDiffOn.union_of_isOpen` / 引理 `ContDiffOn.union_of_isOpen`

English:
lemma ContDiffOn.union_of_isOpen
  statement: (hf : ContDiffOn 𝕜 n f s) (hf' : ContDiffOn 𝕜 n f t)
  proof: by
  rintro x (hx | hx)
.contDiffWithinAt · exact (hf x hx).contDiffAt (hs.mem_nhds hx)
.contDiffWithinAt · exact (hf' x hx).contDiffAt (ht.mem_nhds hx)

中文:
引理 ContDiffOn.union_of_isOpen
  结论: (hf : ContDiffOn 𝕜 n f s) (hf' : ContDiffOn 𝕜 n f t)
  证明: by
  rintro x (hx | hx)
.contDiffWithinAt · exact (hf x hx).contDiffAt (hs.mem_nhds hx)
.contDiffWithinAt · exact (hf' x hx).contDiffAt (ht.mem_nhds hx)

Depends on / 依赖: contDiffAt, contDiffWithinAt, hs.mem_nhds, ht.mem_nhds, mem_nhds
-/
lemma ContDiffOn.union_of_isOpen (hf : ContDiffOn 𝕜 n f s) (hf' : ContDiffOn 𝕜 n f t)
    (hs : IsOpen s) (ht : IsOpen t) :
    ContDiffOn 𝕜 n f (s union t) := by
  rintro x (hx | hx)
.contDiffWithinAt · exact (hf x hx).contDiffAt (hs.mem_nhds hx)
.contDiffWithinAt · exact (hf' x hx).contDiffAt (ht.mem_nhds hx)

/--
lemma `contDiffOn_union_iff_of_isOpen` / 引理 `contDiffOn_union_iff_of_isOpen`

English:
lemma contDiffOn_union_iff_of_isOpen
  given: (hs : IsOpen s) (ht : IsOpen t)
  proof: ⟨fun h => ⟨h.mono subset_union_left, h.mono subset_union_right⟩,
   fun ⟨hfs, hft⟩ => ContDiffOn.union_of_isOpen hfs hft hs ht⟩

中文:
引理 contDiffOn_union_iff_of_isOpen
  条件: (hs : 是开集 s) (ht : 是开集 t)
  证明: ⟨fun h => ⟨h.mono subset_union_left, h.mono subset_union_right⟩,
   fun ⟨hfs, hft⟩ => ContDiffOn.union_of_isOpen hfs hft hs ht⟩

Depends on / 依赖: ContDiffOn, ContDiffOn.union_of_isOpen, h.mono, subset_union_left, subset_union_right, union_of_isOpen
-/
lemma contDiffOn_union_iff_of_isOpen (hs : IsOpen s) (ht : IsOpen t) :
    ContDiffOn 𝕜 n f (s union t) ↔ ContDiffOn 𝕜 n f s ∧ ContDiffOn 𝕜 n f t :=
  ⟨fun h => ⟨h.mono subset_union_left, h.mono subset_union_right⟩,
   fun ⟨hfs, hft⟩ => ContDiffOn.union_of_isOpen hfs hft hs ht⟩

/--
lemma `contDiff_of_contDiffOn_union_of_isOpen` / 引理 `contDiff_of_contDiffOn_union_of_isOpen`

English:
lemma contDiff_of_contDiffOn_union_of_isOpen
  statement: (hf : ContDiffOn 𝕜 n f s)
  proof: by
  rw [← contDiffOn_univ]; rw [← hst]
  exact hf.union_of_isOpen hf' hs ht

中文:
引理 contDiff_of_contDiffOn_union_of_isOpen
  结论: (hf : ContDiffOn 𝕜 n f s)
  证明: by
  rw [← contDiffOn_univ]; rw [← hst]
  exact hf.union_of_isOpen hf' hs ht

Depends on / 依赖: contDiffOn_univ, hf.union_of_isOpen, union_of_isOpen
-/
lemma contDiff_of_contDiffOn_union_of_isOpen (hf : ContDiffOn 𝕜 n f s)
    (hf' : ContDiffOn 𝕜 n f t) (hst : s union t = univ) (hs : IsOpen s) (ht : IsOpen t) :
    ContDiff 𝕜 n f := by
  rw [← contDiffOn_univ]; rw [← hst]
  exact hf.union_of_isOpen hf' hs ht

/--
lemma `ContDiffOn.iUnion_of_isOpen` / 引理 `ContDiffOn.iUnion_of_isOpen`

English:
lemma ContDiffOn.iUnion_of_isOpen
  statement: {ι : Type*} {s : ι -> Set E}
  proof: by
  rintro x ⟨si, ⟨i, rfl⟩, hxsi⟩
.contDiffWithinAt exact (hf i).contDiffAt ((hs i).mem_nhds hxsi)

中文:
引理 ContDiffOn.iUnion_of_isOpen
  结论: {ι : 类型} {s : ι -> 集合 E}
  证明: by
  rintro x ⟨si, ⟨i, rfl⟩, hxsi⟩
.contDiffWithinAt exact (hf i).contDiffAt ((hs i).mem_nhds hxsi)

Depends on / 依赖: contDiffAt, contDiffWithinAt, mem_nhds
-/
lemma ContDiffOn.iUnion_of_isOpen {ι : Type*} {s : ι -> Set E}
    (hf : forall i : ι, ContDiffOn 𝕜 n f (s i)) (hs : forall i, IsOpen (s i)) :
    ContDiffOn 𝕜 n f (⋃ i, s i) := by
  rintro x ⟨si, ⟨i, rfl⟩, hxsi⟩
.contDiffWithinAt exact (hf i).contDiffAt ((hs i).mem_nhds hxsi)

/--
lemma `contDiffOn_iUnion_iff_of_isOpen` / 引理 `contDiffOn_iUnion_iff_of_isOpen`

English:
lemma contDiffOn_iUnion_iff_of_isOpen
  statement: {ι : Type*} {s : ι -> Set E}
  proof: ⟨fun h i => h.mono subset_iUnion_of_subset i fun _ a => a,
   fun h => ContDiffOn.iUnion_of_isOpen h hs⟩

中文:
引理 contDiffOn_iUnion_iff_of_isOpen
  结论: {ι : 类型} {s : ι -> 集合 E}
  证明: ⟨fun h i => h.mono subset_iUnion_of_subset i fun _ a => a,
   fun h => ContDiffOn.iUnion_of_isOpen h hs⟩

Depends on / 依赖: ContDiffOn, ContDiffOn.iUnion_of_isOpen, h.mono, iUnion_of_isOpen, subset_iUnion_of_subset
-/
lemma contDiffOn_iUnion_iff_of_isOpen {ι : Type*} {s : ι -> Set E}
    (hs : forall i, IsOpen (s i)) :
    ContDiffOn 𝕜 n f (⋃ i, s i) ↔ forall i : ι, ContDiffOn 𝕜 n f (s i) :=
⟨fun h i => h.mono subset_iUnion_of_subset i fun _ a => a,
   fun h => ContDiffOn.iUnion_of_isOpen h hs⟩

/--
lemma `contDiff_of_contDiffOn_iUnion_of_isOpen` / 引理 `contDiff_of_contDiffOn_iUnion_of_isOpen`

English:
lemma contDiff_of_contDiffOn_iUnion_of_isOpen
  statement: {ι : Type*} {s : ι -> Set E}
  proof: by
  rw [← contDiffOn_univ]; rw [← hs']
  exact ContDiffOn.iUnion_of_isOpen hf hs

中文:
引理 contDiff_of_contDiffOn_iUnion_of_isOpen
  结论: {ι : 类型} {s : ι -> 集合 E}
  证明: by
  rw [← contDiffOn_univ]; rw [← hs']
  exact ContDiffOn.iUnion_of_isOpen hf hs

Depends on / 依赖: ContDiffOn, ContDiffOn.iUnion_of_isOpen, contDiffOn_univ, iUnion_of_isOpen
-/
lemma contDiff_of_contDiffOn_iUnion_of_isOpen {ι : Type*} {s : ι -> Set E}
    (hf : forall i : ι, ContDiffOn 𝕜 n f (s i)) (hs : forall i, IsOpen (s i)) (hs' : ⋃ i, s i = univ) :
    ContDiff 𝕜 n f := by
  rw [← contDiffOn_univ]; rw [← hs']
  exact ContDiffOn.iUnion_of_isOpen hf hs

end contDiffOn_union

/--
theorem `contDiff_prodAssoc` / 定理 `contDiff_prodAssoc`

English:
theorem contDiff_prodAssoc
  given: {n : Nat∞ω}
  statement: ContDiff 𝕜 n Equiv.prodAssoc E F G
  proof: (LinearIsometryEquiv.prodAssoc 𝕜 E F G).contDiff

中文:
定理 contDiff_prodAssoc
  条件: {n : 自然数∞ω}
  结论: 连续可微 𝕜 n 等价.prodAssoc E F G
  证明: (LinearIsometryEquiv.prodAssoc 𝕜 E F G).contDiff

Depends on / 依赖: LinearIsometryEquiv, LinearIsometryEquiv.prodAssoc, contDiff, prodAssoc
-/
theorem contDiff_prodAssoc {n : Nat∞ω} : ContDiff 𝕜 n Equiv.prodAssoc E F G :=
  (LinearIsometryEquiv.prodAssoc 𝕜 E F G).contDiff

/--
theorem `contDiff_prodAssoc_symm` / 定理 `contDiff_prodAssoc_symm`

English:
theorem contDiff_prodAssoc_symm
  given: {n : Nat∞ω}
  statement: ContDiff 𝕜 n (Equiv.prodAssoc E F G).symm
  proof: (LinearIsometryEquiv.prodAssoc 𝕜 E F G).symm.contDiff

中文:
定理 contDiff_prodAssoc_symm
  条件: {n : 自然数∞ω}
  结论: 连续可微 𝕜 n (等价.prodAssoc E F G).symm
  证明: (LinearIsometryEquiv.prodAssoc 𝕜 E F G).symm.contDiff

Depends on / 依赖: LinearIsometryEquiv, LinearIsometryEquiv.prodAssoc, contDiff, prodAssoc, symm.contDiff
-/
theorem contDiff_prodAssoc_symm {n : Nat∞ω} : ContDiff 𝕜 n (Equiv.prodAssoc E F G).symm :=
  (LinearIsometryEquiv.prodAssoc 𝕜 E F G).symm.contDiff
