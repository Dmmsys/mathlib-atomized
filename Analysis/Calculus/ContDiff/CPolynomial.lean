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

variable {p : FormalMultilinearSeries 𝕜 E F} {r : Real>=0∞} {n : Nat}
variable {f : E -> F} {x : E} {s : Set E}

/--
theorem `CPolynomialOn.contDiffOn` / 定理 `CPolynomialOn.contDiffOn`

English:
theorem CPolynomialOn.contDiffOn
  given: (h : CPolynomialOn 𝕜 f s) {n : Nat∞ω}
  proof: by
  let t := { x | CPolynomialAt 𝕜 f x }
  suffices ContDiffOn 𝕜 n f t from this.mono h
  suffices AnalyticOnNhd 𝕜 f t by
    have t_open : IsOpen t := isOpen_cpolynomialAt 𝕜 f
    exact AnalyticOnNhd.contDiffOn this t_open.uniqueDiffOn
  have H : CPolynomialOn 𝕜 f t := fun _x hx => hx
  exact H.an

中文:
定理 CPolynomialOn.contDiffOn
  条件: (h : CPolynomialOn 𝕜 f s) {n : 自然数∞ω}
  证明: by
  let t := { x | CPolynomialAt 𝕜 f x }
  suffices ContDiffOn 𝕜 n f t from this.mono h
  suffices AnalyticOnNhd 𝕜 f t by
    have t_open : IsOpen t := isOpen_cpolynomialAt 𝕜 f
    exact AnalyticOnNhd.contDiffOn this t_open.uniqueDiffOn
  have H : CPolynomialOn 𝕜 f t := fun _x hx => hx
  exact H.an

Depends on / 依赖: AnalyticOnNhd, AnalyticOnNhd.contDiffOn, CPolynomialAt, CPolynomialOn, ContDiffOn, H.analyticOnNhd, IsOpen, analyticOnNhd, contDiffOn, isOpen_cpolynomialAt, t_open, t_open.uniqueDiffOn, this.mono, uniqueDiffOn
-/
theorem CPolynomialOn.contDiffOn (h : CPolynomialOn 𝕜 f s) {n : Nat∞ω} :
    ContDiffOn 𝕜 n f s := by
  let t := { x | CPolynomialAt 𝕜 f x }
  suffices ContDiffOn 𝕜 n f t from this.mono h
  suffices AnalyticOnNhd 𝕜 f t by
    have t_open : IsOpen t := isOpen_cpolynomialAt 𝕜 f
    exact AnalyticOnNhd.contDiffOn this t_open.uniqueDiffOn
  have H : CPolynomialOn 𝕜 f t := fun _x hx => hx
  exact H.analyticOnNhd

/--
theorem `CPolynomialAt.contDiffAt` / 定理 `CPolynomialAt.contDiffAt`

English:
theorem CPolynomialAt.contDiffAt
  given: (h : CPolynomialAt 𝕜 f x) {n : Nat∞ω}
  proof: let ⟨_, hs, hf⟩ := h.exists_mem_nhds_cpolynomialOn
  hf.contDiffOn.contDiffAt hs

中文:
定理 CPolynomialAt.contDiffAt
  条件: (h : CPolynomialAt 𝕜 f x) {n : 自然数∞ω}
  证明: let ⟨_, hs, hf⟩ := h.exists_mem_nhds_cpolynomialOn
  hf.contDiffOn.contDiffAt hs

Depends on / 依赖: contDiffAt, contDiffOn, exists_mem_nhds_cpolynomialOn, h.exists_mem_nhds_cpolynomialOn, hf.contDiffOn.contDiffAt
-/
theorem CPolynomialAt.contDiffAt (h : CPolynomialAt 𝕜 f x) {n : Nat∞ω} :
    ContDiffAt 𝕜 n f x :=
  let ⟨_, hs, hf⟩ := h.exists_mem_nhds_cpolynomialOn
  hf.contDiffOn.contDiffAt hs

end fderiv

namespace ContinuousMultilinearMap

variable {ι : Type*} {E : ι -> Type*} [forall i, NormedAddCommGroup (E i)] [forall i, NormedSpace 𝕜 (E i)]
  [Fintype ι] (f : ContinuousMultilinearMap 𝕜 E F) {n : Nat∞ω} {x : Π i, E i}

open FormalMultilinearSeries

/--
lemma `contDiffAt` / 引理 `contDiffAt`

English:
lemma contDiffAt
  statement: ContDiffAt 𝕜 n f x
  proof: f.cpolynomialAt.contDiffAt

中文:
引理 contDiffAt
  结论: ContDiffAt 𝕜 n f x
  证明: f.cpolynomialAt.contDiffAt

Depends on / 依赖: contDiffAt, cpolynomialAt, f.cpolynomialAt.contDiffAt
-/
lemma contDiffAt : ContDiffAt 𝕜 n f x := f.cpolynomialAt.contDiffAt

/--
lemma `contDiff` / 引理 `contDiff`

English:
lemma contDiff
  statement: ContDiff 𝕜 n f
  proof: contDiff_iff_contDiffAt.mpr (fun _ => f.contDiffAt)

中文:
引理 contDiff
  结论: 连续可微 𝕜 n f
  证明: contDiff_iff_contDiffAt.mpr (fun _ => f.contDiffAt)

Depends on / 依赖: contDiffAt, contDiff_iff_contDiffAt, contDiff_iff_contDiffAt.mpr, f.contDiffAt
-/
lemma contDiff : ContDiff 𝕜 n f := contDiff_iff_contDiffAt.mpr (fun _ => f.contDiffAt)

end ContinuousMultilinearMap
