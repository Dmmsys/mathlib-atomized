/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

/-!
### Restricting Scalars in Iterated Fréchet Derivatives

This file establishes standard theorems on restriction of scalars for iterated Fréchet derivatives,
comparing iterated derivatives with respect to a field `𝕜'` to iterated derivatives with respect to
a subfield `𝕜 ⊆ 𝕜'`. The results are analogous to those found in
`Mathlib.Analysis.Calculus.FDeriv.RestrictScalars`.
-/

public section

variable
  {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace 𝕜' E] [IsScalarTower 𝕜 𝕜' E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace 𝕜' F] [IsScalarTower 𝕜 𝕜' F]
  {x : E} {f : E -> F} {n : Nat} {s : Set E}

open ContinuousMultilinearMap Topology

/--
lemma `fderivWithin_restrictScalars_comp` / 引理 `fderivWithin_restrictScalars_comp`

English:
lemma fderivWithin_restrictScalars_comp
  proof: by
  simp only [← restrictScalarsLinear_apply]
  rw [fderiv_comp_fderivWithin _ (by fun_prop) (h.restrictScalars 𝕜) hs]; rw [ContinuousLinearMap.fderiv]
  ext a b
  simp [h.restrictScalars_fderivWithin 𝕜 hs]

中文:
引理 fderivWithin_restrictScalars_comp
  证明: by
  simp only [← restrictScalarsLinear_apply]
  rw [fderiv_comp_fderivWithin _ (by fun_prop) (h.restrictScalars 𝕜) hs]; rw [ContinuousLinearMap.fderiv]
  ext a b
  simp [h.restrictScalars_fderivWithin 𝕜 hs]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.fderiv, fderiv, fderiv_comp_fderivWithin, fun_prop, h.restrictScalars, h.restrictScalars_fderivWithin, restrictScalars, restrictScalarsLinear_apply, restrictScalars_fderivWithin
-/
lemma fderivWithin_restrictScalars_comp
    {φ : E -> (ContinuousMultilinearMap 𝕜' (fun _ : Fin n => E) F)}
    (h : DifferentiableWithinAt 𝕜' φ s x) (hs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 ((restrictScalars 𝕜) ∘ φ) s x
      = (restrictScalars 𝕜) ∘ ((fderivWithin 𝕜' φ s x).restrictScalars 𝕜) := by
  simp only [← restrictScalarsLinear_apply]
  rw [fderiv_comp_fderivWithin _ (by fun_prop) (h.restrictScalars 𝕜) hs]; rw [ContinuousLinearMap.fderiv]
  ext a b
  simp [h.restrictScalars_fderivWithin 𝕜 hs]

/--
theorem `ContDiffWithinAt.restrictScalars_iteratedFDerivWithin_eventuallyEq` / 定理 `ContDiffWithinAt.restrictScalars_iteratedFDerivWithin_eventuallyEq`

English:
theorem ContDiffWithinAt.restrictScalars_iteratedFDerivWithin_eventuallyEq
  proof: by
  induction n with
  | zero =>
    filter_upwards with a
    ext m
    simp
  | succ n hn =>
    have t₀ := h.of_le (Nat.cast_le.mpr (n.le_add_right 1))
    have t₁ : forallᶠ (y : E) in 𝓝[s] x, ContDiffWithinAt 𝕜' (↑(n + 1)) f s y := by
      nth_rw 2 [← s.insert_eq_of_mem hx]
      apply h.event

中文:
定理 ContDiffWithinAt.restrictScalars_iteratedFDerivWithin_eventuallyEq
  证明: by
  induction n with
  | zero =>
    filter_upwards with a
    ext m
    simp
  | succ n hn =>
    have t₀ := h.of_le (Nat.cast_le.mpr (n.le_add_right 1))
    have t₁ : forallᶠ (y : E) in 𝓝[s] x, ContDiffWithinAt 𝕜' (↑(n + 1)) f s y := by
      nth_rw 2 [← s.insert_eq_of_mem hx]
      apply h.event

Depends on / 依赖: ContDiffWithinAt, EventuallyEq, Filter, Filter.EventuallyEq, Function, Function.comp_apply, Nat.cast_le.mpr, cast_le, coe_restrictScalars, comp_apply, eventually, eventually_eventually_nhdsWithin, eventually_mem_nhdsWithin, filter_upwards, h.eventually, h.of_le, insert_eq_of_mem, le_add_right, n.le_add_right, nth_rw
-/
theorem ContDiffWithinAt.restrictScalars_iteratedFDerivWithin_eventuallyEq
    (h : ContDiffWithinAt 𝕜' n f s x) (hs : UniqueDiffOn 𝕜 s) (hx : x in s) :
    (restrictScalars 𝕜) ∘ (iteratedFDerivWithin 𝕜' n f s)
      =ᶠ[𝓝[s] x] iteratedFDerivWithin 𝕜 n f s := by
  induction n with
  | zero =>
    filter_upwards with a
    ext m
    simp
  | succ n hn =>
    have t₀ := h.of_le (Nat.cast_le.mpr (n.le_add_right 1))
    have t₁ : forallᶠ (y : E) in 𝓝[s] x, ContDiffWithinAt 𝕜' (↑(n + 1)) f s y := by
      nth_rw 2 [← s.insert_eq_of_mem hx]
      apply h.eventually (by simp)
    filter_upwards [eventually_eventually_nhdsWithin.2 (hn t₀), t₁,
      eventually_mem_nhdsWithin (a := x) (s := s)] with a h₁a h₃a h₄a
    rw [← Filter.EventuallyEq] at h₁a
    ext m
    simp only [Function.comp_apply, coe_restrictScalars, iteratedFDerivWithin_succ_apply_left]
    rw [← (h₁a.fderivWithin' (by tauto)).eq_of_nhdsWithin h₄a]; rw [fderivWithin_restrictScalars_comp]
    · simp
    · apply h₃a.differentiableWithinAt_iteratedFDerivWithin
      · rw [Nat.cast_lt]
        simp
      · have : UniqueDiffOn 𝕜' s := hs.mono_field
        simpa [s.insert_eq_of_mem h₄a]
    apply hs a h₄a

/--
theorem `ContDiffAt.restrictScalars_iteratedFDeriv_eventuallyEq` / 定理 `ContDiffAt.restrictScalars_iteratedFDeriv_eventuallyEq`

English:
theorem ContDiffAt.restrictScalars_iteratedFDeriv_eventuallyEq
  given: (h : ContDiffAt 𝕜' n f x)
  proof: by
  have h' : ContDiffWithinAt 𝕜' n f Set.univ x := h
  convert! (h'.restrictScalars_iteratedFDerivWithin_eventuallyEq _ trivial)
  <;> simp [iteratedFDerivWithin_univ.symm, uniqueDiffOn_univ]

中文:
定理 ContDiffAt.restrictScalars_iteratedFDeriv_eventuallyEq
  条件: (h : ContDiffAt 𝕜' n f x)
  证明: by
  have h' : ContDiffWithinAt 𝕜' n f Set.univ x := h
  convert! (h'.restrictScalars_iteratedFDerivWithin_eventuallyEq _ trivial)
  <;> simp [iteratedFDerivWithin_univ.symm, uniqueDiffOn_univ]

Depends on / 依赖: ContDiffWithinAt, Set.univ, convert, iteratedFDerivWithin_univ, iteratedFDerivWithin_univ.symm, restrictScalars_iteratedFDerivWithin_eventuallyEq, uniqueDiffOn_univ
-/
theorem ContDiffAt.restrictScalars_iteratedFDeriv_eventuallyEq (h : ContDiffAt 𝕜' n f x) :
    (restrictScalars 𝕜) ∘ (iteratedFDeriv 𝕜' n f) =ᶠ[𝓝 x] iteratedFDeriv 𝕜 n f := by
  have h' : ContDiffWithinAt 𝕜' n f Set.univ x := h
  convert! (h'.restrictScalars_iteratedFDerivWithin_eventuallyEq _ trivial)
  <;> simp [iteratedFDerivWithin_univ.symm, uniqueDiffOn_univ]

/--
theorem `ContDiffAt.restrictScalars_iteratedFDeriv` / 定理 `ContDiffAt.restrictScalars_iteratedFDeriv`

English:
theorem ContDiffAt.restrictScalars_iteratedFDeriv
  given: (h : ContDiffAt 𝕜' n f x)
  proof: h.restrictScalars_iteratedFDeriv_eventuallyEq.eq_of_nhds

中文:
定理 ContDiffAt.restrictScalars_iteratedFDeriv
  条件: (h : ContDiffAt 𝕜' n f x)
  证明: h.restrictScalars_iteratedFDeriv_eventuallyEq.eq_of_nhds

Depends on / 依赖: eq_of_nhds, h.restrictScalars_iteratedFDeriv_eventuallyEq.eq_of_nhds, restrictScalars_iteratedFDeriv_eventuallyEq
-/
theorem ContDiffAt.restrictScalars_iteratedFDeriv (h : ContDiffAt 𝕜' n f x) :
    ((restrictScalars 𝕜) ∘ iteratedFDeriv 𝕜' n f) x = iteratedFDeriv 𝕜 n f x :=
  h.restrictScalars_iteratedFDeriv_eventuallyEq.eq_of_nhds
