/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# The Fréchet derivative: congruence properties

Lemmas about congruence properties of the Fréchet derivative under change of function, set, etc.

## Tags

derivative, differentiable, Fréchet, calculus

-/

public section

open Filter Asymptotics ContinuousLinearMap Set Metric Topology NNReal ENNReal

noncomputable section

section
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
variable {F : Type*} [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]

variable {f f₀ f₁ g : E -> F}
variable {f' f₀' f₁' g' : E ->L[𝕜] F}
variable {x : E}
variable {s t : Set E}
variable {L : Filter (E × E)}

section congr


/--
theorem `hasFDerivWithinAt_congr_set_nhdsNE` / 定理 `hasFDerivWithinAt_congr_set_nhdsNE`

English:
theorem hasFDerivWithinAt_congr_set_nhdsNE
  given: (h : s =ᶠ[𝓝[!=] x] t)
  proof: calc
    HasFDerivWithinAt f f' s x ↔ HasFDerivWithinAt f f' (s \ {x}) x :=
      hasFDerivWithinAt_sdiff_singleton_self.symm
    _ ↔ HasFDerivWithinAt f f' (t \ {x}) x := by
      suffices 𝓝[s \ {x}] x = 𝓝[t \ {x}] x by simp only [HasFDerivWithinAt, this]
      simpa only [set_eventuallyEq_iff_inf_principal, ← nhdsWithin_inter', sdiff_eq, inter_comm]
        using h
    _ ↔ HasFDerivWithinAt f f' t x := hasFDerivWithinAt_sdiff_singleton_self

中文:
定理 hasFDerivWithinAt_congr_set_nhdsNE
  条件: (h : s =ᶠ[𝓝[!=] x] t)
  证明: calc
    HasFDerivWithinAt f f' s x ↔ HasFDerivWithinAt f f' (s \ {x}) x :=
      hasFDerivWithinAt_sdiff_singleton_self.symm
    _ ↔ HasFDerivWithinAt f f' (t \ {x}) x := by
      suffices 𝓝[s \ {x}] x = 𝓝[t \ {x}] x by simp only [HasFDerivWithinAt, this]
      simpa only [set_eventuallyEq_iff_inf_principal, ← nhdsWithin_inter', sdiff_eq, inter_comm]
        using h
    _ ↔ HasFDerivWithinAt f f' t x := hasFDerivWithinAt_sdiff_singleton_self

Depends on / 依赖: HasFDerivWithinAt, hasFDerivWithinAt_sdiff_singleton_self, hasFDerivWithinAt_sdiff_singleton_self.symm, inter_comm, nhdsWithin_inter, sdiff_eq, set_eventuallyEq_iff_inf_principal
-/
theorem hasFDerivWithinAt_congr_set_nhdsNE (h : s =ᶠ[𝓝[!=] x] t) :
    HasFDerivWithinAt f f' s x ↔ HasFDerivWithinAt f f' t x :=
  calc
    HasFDerivWithinAt f f' s x ↔ HasFDerivWithinAt f f' (s \ {x}) x :=
      hasFDerivWithinAt_sdiff_singleton_self.symm
    _ ↔ HasFDerivWithinAt f f' (t \ {x}) x := by
      suffices 𝓝[s \ {x}] x = 𝓝[t \ {x}] x by simp only [HasFDerivWithinAt, this]
      simpa only [set_eventuallyEq_iff_inf_principal, ← nhdsWithin_inter', sdiff_eq, inter_comm]
        using h
    _ ↔ HasFDerivWithinAt f f' t x := hasFDerivWithinAt_sdiff_singleton_self

/--
theorem `hasFDerivWithinAt_congr_set` / 定理 `hasFDerivWithinAt_congr_set`

English:
theorem hasFDerivWithinAt_congr_set
  given: (h : s =ᶠ[𝓝 x] t)
  proof: hasFDerivWithinAt_congr_set_nhdsNE h.filter_mono inf_le_left

中文:
定理 hasFDerivWithinAt_congr_set
  条件: (h : s =ᶠ[𝓝 x] t)
  证明: hasFDerivWithinAt_congr_set_nhdsNE h.filter_mono inf_le_left

Depends on / 依赖: filter_mono, h.filter_mono, hasFDerivWithinAt_congr_set_nhdsNE, inf_le_left
-/
theorem hasFDerivWithinAt_congr_set (h : s =ᶠ[𝓝 x] t) :
    HasFDerivWithinAt f f' s x ↔ HasFDerivWithinAt f f' t x :=
hasFDerivWithinAt_congr_set_nhdsNE h.filter_mono inf_le_left

/--
theorem `hasFDerivWithinAt_congr_set'` / 定理 `hasFDerivWithinAt_congr_set'`

English:
theorem hasFDerivWithinAt_congr_set'
  statement: [T1Space E] (y : E)
  proof: by
  rcases eq_or_ne x y with rfl | hne
  · exact hasFDerivWithinAt_congr_set_nhdsNE h
  · rw [hne.nhdsWithin_compl_singleton] at h
    exact hasFDerivWithinAt_congr_set h

中文:
定理 hasFDerivWithinAt_congr_set'
  结论: [T1空间 E] (y : E)
  证明: by
  rcases eq_or_ne x y with rfl | hne
  · exact hasFDerivWithinAt_congr_set_nhdsNE h
  · rw [hne.nhdsWithin_compl_singleton] at h
    exact hasFDerivWithinAt_congr_set h

Depends on / 依赖: eq_or_ne, hasFDerivWithinAt_congr_set, hasFDerivWithinAt_congr_set_nhdsNE, hne.nhdsWithin_compl_singleton, nhdsWithin_compl_singleton
-/
theorem hasFDerivWithinAt_congr_set' [T1Space E] (y : E)
    (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    HasFDerivWithinAt f f' s x ↔ HasFDerivWithinAt f f' t x := by
  rcases eq_or_ne x y with rfl | hne
  · exact hasFDerivWithinAt_congr_set_nhdsNE h
  · rw [hne.nhdsWithin_compl_singleton] at h
    exact hasFDerivWithinAt_congr_set h

/--
theorem `differentiableWithinAt_congr_set_nhdsNE` / 定理 `differentiableWithinAt_congr_set_nhdsNE`

English:
theorem differentiableWithinAt_congr_set_nhdsNE
  given: (h : s =ᶠ[𝓝[!=] x] t)
  proof: exists_congr fun _ => hasFDerivWithinAt_congr_set_nhdsNE h

中文:
定理 differentiableWithinAt_congr_set_nhdsNE
  条件: (h : s =ᶠ[𝓝[!=] x] t)
  证明: exists_congr fun _ => hasFDerivWithinAt_congr_set_nhdsNE h

Depends on / 依赖: exists_congr, hasFDerivWithinAt_congr_set_nhdsNE
-/
theorem differentiableWithinAt_congr_set_nhdsNE (h : s =ᶠ[𝓝[!=] x] t) :
    DifferentiableWithinAt 𝕜 f s x ↔ DifferentiableWithinAt 𝕜 f t x :=
  exists_congr fun _ => hasFDerivWithinAt_congr_set_nhdsNE h

/--
theorem `differentiableWithinAt_congr_set'` / 定理 `differentiableWithinAt_congr_set'`

English:
theorem differentiableWithinAt_congr_set'
  given: [T1Space E] (y : E) (h : s =ᶠ[𝓝[{y}ᶜ] x] t)
  proof: exists_congr fun _ => hasFDerivWithinAt_congr_set' _ h

中文:
定理 differentiableWithinAt_congr_set'
  条件: [T1空间 E] (y : E) (h : s =ᶠ[𝓝[{y}ᶜ] x] t)
  证明: exists_congr fun _ => hasFDerivWithinAt_congr_set' _ h

Depends on / 依赖: exists_congr, hasFDerivWithinAt_congr_set
-/
theorem differentiableWithinAt_congr_set' [T1Space E] (y : E) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    DifferentiableWithinAt 𝕜 f s x ↔ DifferentiableWithinAt 𝕜 f t x :=
  exists_congr fun _ => hasFDerivWithinAt_congr_set' _ h

/--
theorem `differentiableWithinAt_congr_set` / 定理 `differentiableWithinAt_congr_set`

English:
theorem differentiableWithinAt_congr_set
  given: (h : s =ᶠ[𝓝 x] t)
  proof: exists_congr fun _ => hasFDerivWithinAt_congr_set h

中文:
定理 differentiableWithinAt_congr_set
  条件: (h : s =ᶠ[𝓝 x] t)
  证明: exists_congr fun _ => hasFDerivWithinAt_congr_set h

Depends on / 依赖: exists_congr, hasFDerivWithinAt_congr_set
-/
theorem differentiableWithinAt_congr_set (h : s =ᶠ[𝓝 x] t) :
    DifferentiableWithinAt 𝕜 f s x ↔ DifferentiableWithinAt 𝕜 f t x :=
  exists_congr fun _ => hasFDerivWithinAt_congr_set h

/--
theorem `fderivWithin_congr_set_nhdsNE` / 定理 `fderivWithin_congr_set_nhdsNE`

English:
theorem fderivWithin_congr_set_nhdsNE
  given: (h : s =ᶠ[𝓝[!=] x] t)
  proof: by
  classical
  simp only [fderivWithin, differentiableWithinAt_congr_set_nhdsNE h,
    hasFDerivWithinAt_congr_set_nhdsNE h]

中文:
定理 fderivWithin_congr_set_nhdsNE
  条件: (h : s =ᶠ[𝓝[!=] x] t)
  证明: by
  classical
  simp only [fderivWithin, differentiableWithinAt_congr_set_nhdsNE h,
    hasFDerivWithinAt_congr_set_nhdsNE h]

Depends on / 依赖: classical, differentiableWithinAt_congr_set_nhdsNE, fderivWithin, hasFDerivWithinAt_congr_set_nhdsNE
-/
theorem fderivWithin_congr_set_nhdsNE (h : s =ᶠ[𝓝[!=] x] t) :
    fderivWithin 𝕜 f s x = fderivWithin 𝕜 f t x := by
  classical
  simp only [fderivWithin, differentiableWithinAt_congr_set_nhdsNE h,
    hasFDerivWithinAt_congr_set_nhdsNE h]

/--
theorem `fderivWithin_congr_set'` / 定理 `fderivWithin_congr_set'`

English:
theorem fderivWithin_congr_set'
  given: [T1Space E] (y : E) (h : s =ᶠ[𝓝[{y}ᶜ] x] t)
  proof: by
  classical
  simp only [fderivWithin, differentiableWithinAt_congr_set' _ h, hasFDerivWithinAt_congr_set' _ h]

中文:
定理 fderivWithin_congr_set'
  条件: [T1空间 E] (y : E) (h : s =ᶠ[𝓝[{y}ᶜ] x] t)
  证明: by
  classical
  simp only [fderivWithin, differentiableWithinAt_congr_set' _ h, hasFDerivWithinAt_congr_set' _ h]

Depends on / 依赖: classical, differentiableWithinAt_congr_set, fderivWithin, hasFDerivWithinAt_congr_set
-/
theorem fderivWithin_congr_set' [T1Space E] (y : E) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    fderivWithin 𝕜 f s x = fderivWithin 𝕜 f t x := by
  classical
  simp only [fderivWithin, differentiableWithinAt_congr_set' _ h, hasFDerivWithinAt_congr_set' _ h]

/--
theorem `fderivWithin_congr_set` / 定理 `fderivWithin_congr_set`

English:
theorem fderivWithin_congr_set
  given: (h : s =ᶠ[𝓝 x] t)
  statement: fderivWithin 𝕜 f s x = fderivWithin 𝕜 f t x
  proof: fderivWithin_congr_set_nhdsNE h.filter_mono inf_le_left

中文:
定理 fderivWithin_congr_set
  条件: (h : s =ᶠ[𝓝 x] t)
  结论: fderivWithin 𝕜 f s x = fderivWithin 𝕜 f t x
  证明: fderivWithin_congr_set_nhdsNE h.filter_mono inf_le_left

Depends on / 依赖: fderivWithin_congr_set_nhdsNE, filter_mono, h.filter_mono, inf_le_left
-/
theorem fderivWithin_congr_set (h : s =ᶠ[𝓝 x] t) : fderivWithin 𝕜 f s x = fderivWithin 𝕜 f t x :=
fderivWithin_congr_set_nhdsNE h.filter_mono inf_le_left

/--
theorem `fderivWithin_eventually_congr_set'` / 定理 `fderivWithin_eventually_congr_set'`

English:
theorem fderivWithin_eventually_congr_set'
  given: [T1Space E] (y : E) (h : s =ᶠ[𝓝[{y}ᶜ] x] t)
  proof: (eventually_nhds_nhdsWithin.2 h).mono fun _ => fderivWithin_congr_set' y

中文:
定理 fderivWithin_eventually_congr_set'
  条件: [T1空间 E] (y : E) (h : s =ᶠ[𝓝[{y}ᶜ] x] t)
  证明: (eventually_nhds_nhdsWithin.2 h).mono fun _ => fderivWithin_congr_set' y

Depends on / 依赖: eventually_nhds_nhdsWithin, fderivWithin_congr_set
-/
theorem fderivWithin_eventually_congr_set' [T1Space E] (y : E) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    fderivWithin 𝕜 f s =ᶠ[𝓝 x] fderivWithin 𝕜 f t :=
  (eventually_nhds_nhdsWithin.2 h).mono fun _ => fderivWithin_congr_set' y

/--
theorem `fderivWithin_eventually_congr_set` / 定理 `fderivWithin_eventually_congr_set`

English:
theorem fderivWithin_eventually_congr_set
  given: (h : s =ᶠ[𝓝 x] t)
  proof: (eventually_eventually_nhds.2 h).mono fun _ => fderivWithin_congr_set

中文:
定理 fderivWithin_eventually_congr_set
  条件: (h : s =ᶠ[𝓝 x] t)
  证明: (eventually_eventually_nhds.2 h).mono fun _ => fderivWithin_congr_set

Depends on / 依赖: eventually_eventually_nhds, fderivWithin_congr_set
-/
theorem fderivWithin_eventually_congr_set (h : s =ᶠ[𝓝 x] t) :
    fderivWithin 𝕜 f s =ᶠ[𝓝 x] fderivWithin 𝕜 f t :=
  (eventually_eventually_nhds.2 h).mono fun _ => fderivWithin_congr_set

/--
theorem `Filter.EventuallyEq.hasFDerivAtFilter_iff` / 定理 `Filter.EventuallyEq.hasFDerivAtFilter_iff`

English:
theorem Filter.EventuallyEq.hasFDerivAtFilter_iff
  statement: (h₀ : Prod.map f₀ f₀ =ᶠ[L] Prod.map f₁ f₁)
  proof: by
  simp only [hasFDerivAtFilter_iff_isLittleOTVS]
  exact isLittleOTVS_congr (h₀.mono fun y hy => by simp_all [Prod.map]) .rfl

中文:
定理 滤子.EventuallyEq.hasFDerivAtFilter_iff
  结论: (h₀ : 积类型.map f₀ f₀ =ᶠ[L] 积类型.map f₁ f₁)
  证明: by
  simp only [hasFDerivAtFilter_iff_isLittleOTVS]
  exact isLittleOTVS_congr (h₀.mono fun y hy => by simp_all [Prod.map]) .rfl

Depends on / 依赖: Prod.map, hasFDerivAtFilter_iff_isLittleOTVS, isLittleOTVS_congr
-/
theorem Filter.EventuallyEq.hasFDerivAtFilter_iff (h₀ : Prod.map f₀ f₀ =ᶠ[L] Prod.map f₁ f₁)
    (h₁ : forall x, f₀' x = f₁' x) : HasFDerivAtFilter f₀ f₀' L ↔ HasFDerivAtFilter f₁ f₁' L := by
  simp only [hasFDerivAtFilter_iff_isLittleOTVS]
  exact isLittleOTVS_congr (h₀.mono fun y hy => by simp_all [Prod.map]) .rfl

/--
theorem `Filter.EventuallyEq.hasStrictFDerivAt_iff` / 定理 `Filter.EventuallyEq.hasStrictFDerivAt_iff`

English:
theorem Filter.EventuallyEq.hasStrictFDerivAt_iff
  given: (h : f₀ =ᶠ[𝓝 x] f₁) (h' : forall y, f₀' y = f₁' y)
  proof: .hasFDerivAtFilter_iff h' h.prodMap_nhds h

中文:
定理 滤子.EventuallyEq.hasStrictFDerivAt_iff
  条件: (h : f₀ =ᶠ[𝓝 x] f₁) (h' : 对任意 y, f₀' y = f₁' y)
  证明: .hasFDerivAtFilter_iff h' h.prodMap_nhds h

Depends on / 依赖: h.prodMap_nhds, hasFDerivAtFilter_iff, prodMap_nhds
-/
theorem Filter.EventuallyEq.hasStrictFDerivAt_iff (h : f₀ =ᶠ[𝓝 x] f₁) (h' : forall y, f₀' y = f₁' y) :
    HasStrictFDerivAt f₀ f₀' x ↔ HasStrictFDerivAt f₁ f₁' x :=
.hasFDerivAtFilter_iff h' h.prodMap_nhds h

/--
theorem `HasStrictFDerivAt.congr_fderiv` / 定理 `HasStrictFDerivAt.congr_fderiv`

English:
theorem HasStrictFDerivAt.congr_fderiv
  given: (h : HasStrictFDerivAt f f' x) (h' : f' = g')
  proof: h' ▸ h

中文:
定理 HasStrictFDerivAt.congr_fderiv
  条件: (h : HasStrictFDerivAt f f' x) (h' : f' = g')
  证明: h' ▸ h
-/
theorem HasStrictFDerivAt.congr_fderiv (h : HasStrictFDerivAt f f' x) (h' : f' = g') :
    HasStrictFDerivAt f g' x :=
  h' ▸ h

/--
theorem `HasFDerivAt.congr_fderiv` / 定理 `HasFDerivAt.congr_fderiv`

English:
theorem HasFDerivAt.congr_fderiv
  given: (h : HasFDerivAt f f' x) (h' : f' = g')
  statement: HasFDerivAt f g' x
  proof: h' ▸ h

中文:
定理 在点处Fréchet可导.congr_fderiv
  条件: (h : 在点处Fréchet可导 f f' x) (h' : f' = g')
  结论: 在点处Fréchet可导 f g' x
  证明: h' ▸ h
-/
theorem HasFDerivAt.congr_fderiv (h : HasFDerivAt f f' x) (h' : f' = g') : HasFDerivAt f g' x :=
  h' ▸ h

/--
theorem `HasFDerivWithinAt.congr_fderiv` / 定理 `HasFDerivWithinAt.congr_fderiv`

English:
theorem HasFDerivWithinAt.congr_fderiv
  given: (h : HasFDerivWithinAt f f' s x) (h' : f' = g')
  proof: h' ▸ h

中文:
定理 HasFDerivWithinAt.congr_fderiv
  条件: (h : HasFDerivWithinAt f f' s x) (h' : f' = g')
  证明: h' ▸ h
-/
theorem HasFDerivWithinAt.congr_fderiv (h : HasFDerivWithinAt f f' s x) (h' : f' = g') :
    HasFDerivWithinAt f g' s x :=
  h' ▸ h

/--
theorem `HasStrictFDerivAt.congr_of_eventuallyEq` / 定理 `HasStrictFDerivAt.congr_of_eventuallyEq`

English:
theorem HasStrictFDerivAt.congr_of_eventuallyEq
  statement: (h : HasStrictFDerivAt f f' x)
  proof: (h₁.hasStrictFDerivAt_iff fun _ => rfl).1 h

中文:
定理 HasStrictFDerivAt.congr_of_eventuallyEq
  结论: (h : HasStrictFDerivAt f f' x)
  证明: (h₁.hasStrictFDerivAt_iff fun _ => rfl).1 h

Depends on / 依赖: hasStrictFDerivAt_iff
-/
theorem HasStrictFDerivAt.congr_of_eventuallyEq (h : HasStrictFDerivAt f f' x)
    (h₁ : f =ᶠ[𝓝 x] f₁) : HasStrictFDerivAt f₁ f' x :=
  (h₁.hasStrictFDerivAt_iff fun _ => rfl).1 h

/--
theorem `HasFDerivAtFilter.congr_of_eventuallyEq` / 定理 `HasFDerivAtFilter.congr_of_eventuallyEq`

English:
theorem HasFDerivAtFilter.congr_of_eventuallyEq
  statement: (h : HasFDerivAtFilter f f' L)
  proof: (hL.hasFDerivAtFilter_iff fun _ => rfl).2 h

中文:
定理 有FDerivAtFilter.congr_of_eventuallyEq
  结论: (h : 有FDerivAtFilter f f' L)
  证明: (hL.hasFDerivAtFilter_iff fun _ => rfl).2 h

Depends on / 依赖: hL.hasFDerivAtFilter_iff, hasFDerivAtFilter_iff
-/
theorem HasFDerivAtFilter.congr_of_eventuallyEq (h : HasFDerivAtFilter f f' L)
    (hL : Prod.map f₁ f₁ =ᶠ[L] Prod.map f f) :
    HasFDerivAtFilter f₁ f' L :=
  (hL.hasFDerivAtFilter_iff fun _ => rfl).2 h

/--
theorem `Filter.EventuallyEq.hasFDerivAt_iff` / 定理 `Filter.EventuallyEq.hasFDerivAt_iff`

English:
theorem Filter.EventuallyEq.hasFDerivAt_iff
  given: (h : f₀ =ᶠ[𝓝 x] f₁)
  proof: .hasFDerivAtFilter_iff fun _ => rfl h.prodMap (h.filter_mono <| pure_le_nhds _)

中文:
定理 滤子.EventuallyEq.hasFDerivAt_iff
  条件: (h : f₀ =ᶠ[𝓝 x] f₁)
  证明: .hasFDerivAtFilter_iff fun _ => rfl h.prodMap (h.filter_mono <| pure_le_nhds _)

Depends on / 依赖: filter_mono, h.filter_mono, h.prodMap, hasFDerivAtFilter_iff, prodMap, pure_le_nhds
-/
theorem Filter.EventuallyEq.hasFDerivAt_iff (h : f₀ =ᶠ[𝓝 x] f₁) :
    HasFDerivAt f₀ f' x ↔ HasFDerivAt f₁ f' x :=
.hasFDerivAtFilter_iff fun _ => rfl h.prodMap (h.filter_mono <| pure_le_nhds _)

/--
theorem `Filter.EventuallyEq.differentiableAt_iff` / 定理 `Filter.EventuallyEq.differentiableAt_iff`

English:
theorem Filter.EventuallyEq.differentiableAt_iff
  given: (h : f₀ =ᶠ[𝓝 x] f₁)
  proof: exists_congr fun _ => h.hasFDerivAt_iff

中文:
定理 滤子.EventuallyEq.differentiableAt_iff
  条件: (h : f₀ =ᶠ[𝓝 x] f₁)
  证明: exists_congr fun _ => h.hasFDerivAt_iff

Depends on / 依赖: exists_congr, h.hasFDerivAt_iff, hasFDerivAt_iff
-/
theorem Filter.EventuallyEq.differentiableAt_iff (h : f₀ =ᶠ[𝓝 x] f₁) :
    DifferentiableAt 𝕜 f₀ x ↔ DifferentiableAt 𝕜 f₁ x :=
  exists_congr fun _ => h.hasFDerivAt_iff

/--
theorem `Filter.EventuallyEq.hasFDerivWithinAt_iff` / 定理 `Filter.EventuallyEq.hasFDerivWithinAt_iff`

English:
theorem Filter.EventuallyEq.hasFDerivWithinAt_iff
  given: (h : f₀ =ᶠ[𝓝[s] x] f₁) (hx : f₀ x = f₁ x)
  proof: .hasFDerivAtFilter_iff fun _ => _root_.rfl h.prodMap (by assumption)

中文:
定理 滤子.EventuallyEq.hasFDerivWithinAt_iff
  条件: (h : f₀ =ᶠ[𝓝[s] x] f₁) (hx : f₀ x = f₁ x)
  证明: .hasFDerivAtFilter_iff fun _ => _root_.rfl h.prodMap (by assumption)

Depends on / 依赖: _root_, _root_.rfl, h.prodMap, hasFDerivAtFilter_iff, prodMap
-/
theorem Filter.EventuallyEq.hasFDerivWithinAt_iff (h : f₀ =ᶠ[𝓝[s] x] f₁) (hx : f₀ x = f₁ x) :
    HasFDerivWithinAt f₀ f' s x ↔ HasFDerivWithinAt f₁ f' s x :=
.hasFDerivAtFilter_iff fun _ => _root_.rfl h.prodMap (by assumption)

/--
theorem `Filter.EventuallyEq.hasFDerivWithinAt_iff_of_mem` / 定理 `Filter.EventuallyEq.hasFDerivWithinAt_iff_of_mem`

English:
theorem Filter.EventuallyEq.hasFDerivWithinAt_iff_of_mem
  given: (h : f₀ =ᶠ[𝓝[s] x] f₁) (hx : x in s)
  proof: h.hasFDerivWithinAt_iff (h.eq_of_nhdsWithin hx)

中文:
定理 滤子.EventuallyEq.hasFDerivWithinAt_iff_of_mem
  条件: (h : f₀ =ᶠ[𝓝[s] x] f₁) (hx : x in s)
  证明: h.hasFDerivWithinAt_iff (h.eq_of_nhdsWithin hx)

Depends on / 依赖: eq_of_nhdsWithin, h.eq_of_nhdsWithin, h.hasFDerivWithinAt_iff, hasFDerivWithinAt_iff
-/
theorem Filter.EventuallyEq.hasFDerivWithinAt_iff_of_mem (h : f₀ =ᶠ[𝓝[s] x] f₁) (hx : x in s) :
    HasFDerivWithinAt f₀ f' s x ↔ HasFDerivWithinAt f₁ f' s x :=
  h.hasFDerivWithinAt_iff (h.eq_of_nhdsWithin hx)

/--
theorem `Filter.EventuallyEq.differentiableWithinAt_iff` / 定理 `Filter.EventuallyEq.differentiableWithinAt_iff`

English:
theorem Filter.EventuallyEq.differentiableWithinAt_iff
  given: (h : f₀ =ᶠ[𝓝[s] x] f₁) (hx : f₀ x = f₁ x)
  proof: exists_congr fun _ => h.hasFDerivWithinAt_iff hx

中文:
定理 滤子.EventuallyEq.differentiableWithinAt_iff
  条件: (h : f₀ =ᶠ[𝓝[s] x] f₁) (hx : f₀ x = f₁ x)
  证明: exists_congr fun _ => h.hasFDerivWithinAt_iff hx

Depends on / 依赖: exists_congr, h.hasFDerivWithinAt_iff, hasFDerivWithinAt_iff
-/
theorem Filter.EventuallyEq.differentiableWithinAt_iff (h : f₀ =ᶠ[𝓝[s] x] f₁) (hx : f₀ x = f₁ x) :
    DifferentiableWithinAt 𝕜 f₀ s x ↔ DifferentiableWithinAt 𝕜 f₁ s x :=
  exists_congr fun _ => h.hasFDerivWithinAt_iff hx

/--
theorem `Filter.EventuallyEq.differentiableWithinAt_iff_of_mem` / 定理 `Filter.EventuallyEq.differentiableWithinAt_iff_of_mem`

English:
theorem Filter.EventuallyEq.differentiableWithinAt_iff_of_mem
  given: (h : f₀ =ᶠ[𝓝[s] x] f₁) (hx : x in s)
  proof: h.differentiableWithinAt_iff (h.eq_of_nhdsWithin hx)

中文:
定理 滤子.EventuallyEq.differentiableWithinAt_iff_of_mem
  条件: (h : f₀ =ᶠ[𝓝[s] x] f₁) (hx : x in s)
  证明: h.differentiableWithinAt_iff (h.eq_of_nhdsWithin hx)

Depends on / 依赖: differentiableWithinAt_iff, eq_of_nhdsWithin, h.differentiableWithinAt_iff, h.eq_of_nhdsWithin
-/
theorem Filter.EventuallyEq.differentiableWithinAt_iff_of_mem (h : f₀ =ᶠ[𝓝[s] x] f₁) (hx : x in s) :
    DifferentiableWithinAt 𝕜 f₀ s x ↔ DifferentiableWithinAt 𝕜 f₁ s x :=
  h.differentiableWithinAt_iff (h.eq_of_nhdsWithin hx)

/--
theorem `HasFDerivWithinAt.congr_of_eventuallyEq` / 定理 `HasFDerivWithinAt.congr_of_eventuallyEq`

English:
theorem HasFDerivWithinAt.congr_of_eventuallyEq
  statement: (h : HasFDerivWithinAt f f' s x)
  proof: .mpr h h₁.hasFDerivWithinAt_iff hx

中文:
定理 HasFDerivWithinAt.congr_of_eventuallyEq
  结论: (h : HasFDerivWithinAt f f' s x)
  证明: .mpr h h₁.hasFDerivWithinAt_iff hx

Depends on / 依赖: hasFDerivWithinAt_iff
-/
theorem HasFDerivWithinAt.congr_of_eventuallyEq (h : HasFDerivWithinAt f f' s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : HasFDerivWithinAt f₁ f' s x :=
.mpr h h₁.hasFDerivWithinAt_iff hx

/--
theorem `HasFDerivWithinAt.congr` / 定理 `HasFDerivWithinAt.congr`

English:
theorem HasFDerivWithinAt.congr
  statement: (h : HasFDerivWithinAt f f' s x) (hs : EqOn f₁ f s)
  proof: h.congr_of_eventuallyEq hs.eventuallyEq_nhdsWithin hx

中文:
定理 HasFDerivWithinAt.congr
  结论: (h : HasFDerivWithinAt f f' s x) (hs : EqOn f₁ f s)
  证明: h.congr_of_eventuallyEq hs.eventuallyEq_nhdsWithin hx

Depends on / 依赖: congr_of_eventuallyEq, eventuallyEq_nhdsWithin, h.congr_of_eventuallyEq, hs.eventuallyEq_nhdsWithin
-/
theorem HasFDerivWithinAt.congr (h : HasFDerivWithinAt f f' s x) (hs : EqOn f₁ f s)
    (hx : f₁ x = f x) : HasFDerivWithinAt f₁ f' s x :=
  h.congr_of_eventuallyEq hs.eventuallyEq_nhdsWithin hx

/--
theorem `HasFDerivWithinAt.congr'` / 定理 `HasFDerivWithinAt.congr'`

English:
theorem HasFDerivWithinAt.congr'
  given: (h : HasFDerivWithinAt f f' s x) (hs : EqOn f₁ f s) (hx : x in s)
  proof: h.congr hs (hs hx)

中文:
定理 HasFDerivWithinAt.congr'
  条件: (h : HasFDerivWithinAt f f' s x) (hs : EqOn f₁ f s) (hx : x in s)
  证明: h.congr hs (hs hx)

Depends on / 依赖: h.congr
-/
theorem HasFDerivWithinAt.congr' (h : HasFDerivWithinAt f f' s x) (hs : EqOn f₁ f s) (hx : x in s) :
    HasFDerivWithinAt f₁ f' s x :=
  h.congr hs (hs hx)

/--
theorem `HasFDerivWithinAt.congr_mono` / 定理 `HasFDerivWithinAt.congr_mono`

English:
theorem HasFDerivWithinAt.congr_mono
  statement: (h : HasFDerivWithinAt f f' s x) (ht : EqOn f₁ f t)
  proof: .congr ht hx h.mono h₁

中文:
定理 HasFDerivWithinAt.congr_mono
  结论: (h : HasFDerivWithinAt f f' s x) (ht : EqOn f₁ f t)
  证明: .congr ht hx h.mono h₁

Depends on / 依赖: h.mono
-/
theorem HasFDerivWithinAt.congr_mono (h : HasFDerivWithinAt f f' s x) (ht : EqOn f₁ f t)
    (hx : f₁ x = f x) (h₁ : t subseteq s) : HasFDerivWithinAt f₁ f' t x :=
.congr ht hx h.mono h₁

/--
theorem `HasFDerivAt.congr_of_eventuallyEq` / 定理 `HasFDerivAt.congr_of_eventuallyEq`

English:
theorem HasFDerivAt.congr_of_eventuallyEq
  given: (h : HasFDerivAt f f' x) (h₁ : f₁ =ᶠ[𝓝 x] f)
  proof: h₁.hasFDerivAt_iff.mpr h

中文:
定理 在点处Fréchet可导.congr_of_eventuallyEq
  条件: (h : 在点处Fréchet可导 f f' x) (h₁ : f₁ =ᶠ[𝓝 x] f)
  证明: h₁.hasFDerivAt_iff.mpr h

Depends on / 依赖: hasFDerivAt_iff, hasFDerivAt_iff.mpr
-/
theorem HasFDerivAt.congr_of_eventuallyEq (h : HasFDerivAt f f' x) (h₁ : f₁ =ᶠ[𝓝 x] f) :
    HasFDerivAt f₁ f' x :=
  h₁.hasFDerivAt_iff.mpr h

/--
theorem `DifferentiableWithinAt.congr_mono` / 定理 `DifferentiableWithinAt.congr_mono`

English:
theorem DifferentiableWithinAt.congr_mono
  statement: (h : DifferentiableWithinAt 𝕜 f s x) (ht : EqOn f₁ f t)
  proof: (HasFDerivWithinAt.congr_mono h.hasFDerivWithinAt ht hx h₁).differentiableWithinAt

中文:
定理 DifferentiableWithinAt.congr_mono
  结论: (h : DifferentiableWithinAt 𝕜 f s x) (ht : EqOn f₁ f t)
  证明: (HasFDerivWithinAt.congr_mono h.hasFDerivWithinAt ht hx h₁).differentiableWithinAt

Depends on / 依赖: HasFDerivWithinAt, HasFDerivWithinAt.congr_mono, congr_mono, differentiableWithinAt, h.hasFDerivWithinAt, hasFDerivWithinAt
-/
theorem DifferentiableWithinAt.congr_mono (h : DifferentiableWithinAt 𝕜 f s x) (ht : EqOn f₁ f t)
    (hx : f₁ x = f x) (h₁ : t subseteq s) : DifferentiableWithinAt 𝕜 f₁ t x :=
  (HasFDerivWithinAt.congr_mono h.hasFDerivWithinAt ht hx h₁).differentiableWithinAt

/--
theorem `DifferentiableWithinAt.congr` / 定理 `DifferentiableWithinAt.congr`

English:
theorem DifferentiableWithinAt.congr
  statement: (h : DifferentiableWithinAt 𝕜 f s x) (ht : forall x in s, f₁ x = f x)
  proof: DifferentiableWithinAt.congr_mono h ht hx (Subset.refl _)

中文:
定理 DifferentiableWithinAt.congr
  结论: (h : DifferentiableWithinAt 𝕜 f s x) (ht : 对任意 x in s, f₁ x = f x)
  证明: DifferentiableWithinAt.congr_mono h ht hx (Subset.refl _)

Depends on / 依赖: DifferentiableWithinAt, DifferentiableWithinAt.congr_mono, Subset, Subset.refl, congr_mono
-/
theorem DifferentiableWithinAt.congr (h : DifferentiableWithinAt 𝕜 f s x) (ht : forall x in s, f₁ x = f x)
    (hx : f₁ x = f x) : DifferentiableWithinAt 𝕜 f₁ s x :=
  DifferentiableWithinAt.congr_mono h ht hx (Subset.refl _)

/--
theorem `DifferentiableWithinAt.congr_of_eventuallyEq` / 定理 `DifferentiableWithinAt.congr_of_eventuallyEq`

English:
theorem DifferentiableWithinAt.congr_of_eventuallyEq
  statement: (h : DifferentiableWithinAt 𝕜 f s x)
  proof: (h.hasFDerivWithinAt.congr_of_eventuallyEq h₁ hx).differentiableWithinAt

中文:
定理 DifferentiableWithinAt.congr_of_eventuallyEq
  结论: (h : DifferentiableWithinAt 𝕜 f s x)
  证明: (h.hasFDerivWithinAt.congr_of_eventuallyEq h₁ hx).differentiableWithinAt

Depends on / 依赖: congr_of_eventuallyEq, differentiableWithinAt, h.hasFDerivWithinAt.congr_of_eventuallyEq, hasFDerivWithinAt
-/
theorem DifferentiableWithinAt.congr_of_eventuallyEq (h : DifferentiableWithinAt 𝕜 f s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : DifferentiableWithinAt 𝕜 f₁ s x :=
  (h.hasFDerivWithinAt.congr_of_eventuallyEq h₁ hx).differentiableWithinAt

/--
theorem `DifferentiableWithinAt.congr_of_eventuallyEq_of_mem` / 定理 `DifferentiableWithinAt.congr_of_eventuallyEq_of_mem`

English:
theorem DifferentiableWithinAt.congr_of_eventuallyEq_of_mem
  statement: (h : DifferentiableWithinAt 𝕜 f s x)
  proof: h.congr_of_eventuallyEq h₁ (mem_of_mem_nhdsWithin hx h₁ :)

中文:
定理 DifferentiableWithinAt.congr_of_eventuallyEq_of_mem
  结论: (h : DifferentiableWithinAt 𝕜 f s x)
  证明: h.congr_of_eventuallyEq h₁ (mem_of_mem_nhdsWithin hx h₁ :)

Depends on / 依赖: congr_of_eventuallyEq, h.congr_of_eventuallyEq, mem_of_mem_nhdsWithin
-/
theorem DifferentiableWithinAt.congr_of_eventuallyEq_of_mem (h : DifferentiableWithinAt 𝕜 f s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : x in s) : DifferentiableWithinAt 𝕜 f₁ s x :=
  h.congr_of_eventuallyEq h₁ (mem_of_mem_nhdsWithin hx h₁ :)

/--
theorem `DifferentiableWithinAt.congr_of_eventuallyEq_insert` / 定理 `DifferentiableWithinAt.congr_of_eventuallyEq_insert`

English:
theorem DifferentiableWithinAt.congr_of_eventuallyEq_insert
  statement: (h : DifferentiableWithinAt 𝕜 f s x)
  proof: (h.insert.congr_of_eventuallyEq_of_mem h₁ (mem_insert _ _)).of_insert

中文:
定理 DifferentiableWithinAt.congr_of_eventuallyEq_insert
  结论: (h : DifferentiableWithinAt 𝕜 f s x)
  证明: (h.insert.congr_of_eventuallyEq_of_mem h₁ (mem_insert _ _)).of_insert

Depends on / 依赖: congr_of_eventuallyEq_of_mem, h.insert.congr_of_eventuallyEq_of_mem, insert, mem_insert, of_insert
-/
theorem DifferentiableWithinAt.congr_of_eventuallyEq_insert (h : DifferentiableWithinAt 𝕜 f s x)
    (h₁ : f₁ =ᶠ[𝓝[insert x s] x] f) : DifferentiableWithinAt 𝕜 f₁ s x :=
  (h.insert.congr_of_eventuallyEq_of_mem h₁ (mem_insert _ _)).of_insert

/--
theorem `DifferentiableOn.congr_mono` / 定理 `DifferentiableOn.congr_mono`

English:
theorem DifferentiableOn.congr_mono
  statement: (h : DifferentiableOn 𝕜 f s) (h' : forall x in t, f₁ x = f x)
  proof: fun x hx => (h x (h₁ hx)).congr_mono h' (h' x hx) h₁

中文:
定理 DifferentiableOn.congr_mono
  结论: (h : DifferentiableOn 𝕜 f s) (h' : 对任意 x in t, f₁ x = f x)
  证明: fun x hx => (h x (h₁ hx)).congr_mono h' (h' x hx) h₁

Depends on / 依赖: congr_mono
-/
theorem DifferentiableOn.congr_mono (h : DifferentiableOn 𝕜 f s) (h' : forall x in t, f₁ x = f x)
    (h₁ : t subseteq s) : DifferentiableOn 𝕜 f₁ t := fun x hx => (h x (h₁ hx)).congr_mono h' (h' x hx) h₁

/--
theorem `DifferentiableOn.congr` / 定理 `DifferentiableOn.congr`

English:
theorem DifferentiableOn.congr
  given: (h : DifferentiableOn 𝕜 f s) (h' : forall x in s, f₁ x = f x)
  proof: fun x hx => (h x hx).congr h' (h' x hx)

中文:
定理 DifferentiableOn.congr
  条件: (h : DifferentiableOn 𝕜 f s) (h' : 对任意 x in s, f₁ x = f x)
  证明: fun x hx => (h x hx).congr h' (h' x hx)
-/
theorem DifferentiableOn.congr (h : DifferentiableOn 𝕜 f s) (h' : forall x in s, f₁ x = f x) :
    DifferentiableOn 𝕜 f₁ s := fun x hx => (h x hx).congr h' (h' x hx)

/--
theorem `differentiableOn_congr` / 定理 `differentiableOn_congr`

English:
theorem differentiableOn_congr
  given: (h' : forall x in s, f₁ x = f x)
  proof: ⟨fun h => DifferentiableOn.congr h fun y hy => (h' y hy).symm, fun h =>
    DifferentiableOn.congr h h'⟩

中文:
定理 differentiableOn_congr
  条件: (h' : 对任意 x in s, f₁ x = f x)
  证明: ⟨fun h => DifferentiableOn.congr h fun y hy => (h' y hy).symm, fun h =>
    DifferentiableOn.congr h h'⟩

Depends on / 依赖: DifferentiableOn, DifferentiableOn.congr
-/
theorem differentiableOn_congr (h' : forall x in s, f₁ x = f x) :
    DifferentiableOn 𝕜 f₁ s ↔ DifferentiableOn 𝕜 f s :=
  ⟨fun h => DifferentiableOn.congr h fun y hy => (h' y hy).symm, fun h =>
    DifferentiableOn.congr h h'⟩

/--
theorem `DifferentiableAt.congr_of_eventuallyEq` / 定理 `DifferentiableAt.congr_of_eventuallyEq`

English:
theorem DifferentiableAt.congr_of_eventuallyEq
  given: (h : DifferentiableAt 𝕜 f x) (hL : f₁ =ᶠ[𝓝 x] f)
  proof: hL.differentiableAt_iff.2 h

中文:
定理 DifferentiableAt.congr_of_eventuallyEq
  条件: (h : DifferentiableAt 𝕜 f x) (hL : f₁ =ᶠ[𝓝 x] f)
  证明: hL.differentiableAt_iff.2 h

Depends on / 依赖: differentiableAt_iff, hL.differentiableAt_iff
-/
theorem DifferentiableAt.congr_of_eventuallyEq (h : DifferentiableAt 𝕜 f x) (hL : f₁ =ᶠ[𝓝 x] f) :
    DifferentiableAt 𝕜 f₁ x :=
  hL.differentiableAt_iff.2 h

/--
theorem `DifferentiableWithinAt.fderivWithin_congr_mono` / 定理 `DifferentiableWithinAt.fderivWithin_congr_mono`

English:
theorem DifferentiableWithinAt.fderivWithin_congr_mono
  proof: (HasFDerivWithinAt.congr_mono h.hasFDerivWithinAt hs hx h₁).fderivWithin hxt

中文:
定理 DifferentiableWithinAt.fderivWithin_congr_mono
  证明: (HasFDerivWithinAt.congr_mono h.hasFDerivWithinAt hs hx h₁).fderivWithin hxt

Depends on / 依赖: HasFDerivWithinAt, HasFDerivWithinAt.congr_mono, congr_mono, fderivWithin, h.hasFDerivWithinAt, hasFDerivWithinAt
-/
theorem DifferentiableWithinAt.fderivWithin_congr_mono
    [ContinuousAdd E] [ContinuousSMul 𝕜 E] [ContinuousAdd F] [ContinuousSMul 𝕜 F] [T2Space F]
    (h : DifferentiableWithinAt 𝕜 f s x)
    (hs : EqOn f₁ f t) (hx : f₁ x = f x) (hxt : UniqueDiffWithinAt 𝕜 t x) (h₁ : t subseteq s) :
    fderivWithin 𝕜 f₁ t x = fderivWithin 𝕜 f s x :=
  (HasFDerivWithinAt.congr_mono h.hasFDerivWithinAt hs hx h₁).fderivWithin hxt

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Filter.EventuallyEq.fderivWithin_eq` / 定理 `Filter.EventuallyEq.fderivWithin_eq`

English:
theorem Filter.EventuallyEq.fderivWithin_eq
  given: (hs : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x)
  proof: by
  classical
  simp only [fderivWithin, DifferentiableWithinAt, hs.hasFDerivWithinAt_iff hx]

中文:
定理 滤子.EventuallyEq.fderivWithin_eq
  条件: (hs : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x)
  证明: by
  classical
  simp only [fderivWithin, DifferentiableWithinAt, hs.hasFDerivWithinAt_iff hx]

Depends on / 依赖: DifferentiableWithinAt, classical, fderivWithin, hasFDerivWithinAt_iff, hs.hasFDerivWithinAt_iff
-/
theorem Filter.EventuallyEq.fderivWithin_eq (hs : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) :
    fderivWithin 𝕜 f₁ s x = fderivWithin 𝕜 f s x := by
  classical
  simp only [fderivWithin, DifferentiableWithinAt, hs.hasFDerivWithinAt_iff hx]

/--
theorem `Filter.EventuallyEq.fderivWithin_eq_of_mem` / 定理 `Filter.EventuallyEq.fderivWithin_eq_of_mem`

English:
theorem Filter.EventuallyEq.fderivWithin_eq_of_mem
  given: (hs : f₁ =ᶠ[𝓝[s] x] f) (hx : x in s)
  proof: hs.fderivWithin_eq (mem_of_mem_nhdsWithin hx hs :)

中文:
定理 滤子.EventuallyEq.fderivWithin_eq_of_mem
  条件: (hs : f₁ =ᶠ[𝓝[s] x] f) (hx : x in s)
  证明: hs.fderivWithin_eq (mem_of_mem_nhdsWithin hx hs :)

Depends on / 依赖: fderivWithin_eq, hs.fderivWithin_eq, mem_of_mem_nhdsWithin
-/
theorem Filter.EventuallyEq.fderivWithin_eq_of_mem (hs : f₁ =ᶠ[𝓝[s] x] f) (hx : x in s) :
    fderivWithin 𝕜 f₁ s x = fderivWithin 𝕜 f s x :=
  hs.fderivWithin_eq (mem_of_mem_nhdsWithin hx hs :)

/--
theorem `Filter.EventuallyEq.fderivWithin_eq_of_insert` / 定理 `Filter.EventuallyEq.fderivWithin_eq_of_insert`

English:
theorem Filter.EventuallyEq.fderivWithin_eq_of_insert
  given: (hs : f₁ =ᶠ[𝓝[insert x s] x] f)
  proof: by
  apply Filter.EventuallyEq.fderivWithin_eq (nhdsWithin_mono _ (subset_insert x s) hs)
  exact (mem_of_mem_nhdsWithin (mem_insert x s) hs :)

中文:
定理 滤子.EventuallyEq.fderivWithin_eq_of_insert
  条件: (hs : f₁ =ᶠ[𝓝[insert x s] x] f)
  证明: by
  apply Filter.EventuallyEq.fderivWithin_eq (nhdsWithin_mono _ (subset_insert x s) hs)
  exact (mem_of_mem_nhdsWithin (mem_insert x s) hs :)

Depends on / 依赖: EventuallyEq, Filter, Filter.EventuallyEq.fderivWithin_eq, fderivWithin_eq, mem_insert, mem_of_mem_nhdsWithin, nhdsWithin_mono, subset_insert
-/
theorem Filter.EventuallyEq.fderivWithin_eq_of_insert (hs : f₁ =ᶠ[𝓝[insert x s] x] f) :
    fderivWithin 𝕜 f₁ s x = fderivWithin 𝕜 f s x := by
  apply Filter.EventuallyEq.fderivWithin_eq (nhdsWithin_mono _ (subset_insert x s) hs)
  exact (mem_of_mem_nhdsWithin (mem_insert x s) hs :)

/--
theorem `Filter.EventuallyEq.fderivWithin'` / 定理 `Filter.EventuallyEq.fderivWithin'`

English:
theorem Filter.EventuallyEq.fderivWithin'
  given: (hs : f₁ =ᶠ[𝓝[s] x] f) (ht : t subseteq s)
  proof: (eventually_eventually_nhdsWithin.2 hs).mp
    eventually_mem_nhdsWithin.mono fun _y hys hs =>
      EventuallyEq.fderivWithin_eq (hs.filter_mono <| nhdsWithin_mono _ ht)
        (hs.self_of_nhdsWithin hys)

中文:
定理 滤子.EventuallyEq.fderivWithin'
  条件: (hs : f₁ =ᶠ[𝓝[s] x] f) (ht : t subseteq s)
  证明: (eventually_eventually_nhdsWithin.2 hs).mp
    eventually_mem_nhdsWithin.mono fun _y hys hs =>
      EventuallyEq.fderivWithin_eq (hs.filter_mono <| nhdsWithin_mono _ ht)
        (hs.self_of_nhdsWithin hys)

Depends on / 依赖: EventuallyEq, EventuallyEq.fderivWithin_eq, eventually_eventually_nhdsWithin, eventually_mem_nhdsWithin, eventually_mem_nhdsWithin.mono, fderivWithin_eq, filter_mono, hs.filter_mono, hs.self_of_nhdsWithin, nhdsWithin_mono, self_of_nhdsWithin
-/
theorem Filter.EventuallyEq.fderivWithin' (hs : f₁ =ᶠ[𝓝[s] x] f) (ht : t subseteq s) :
    fderivWithin 𝕜 f₁ t =ᶠ[𝓝[s] x] fderivWithin 𝕜 f t :=
(eventually_eventually_nhdsWithin.2 hs).mp
    eventually_mem_nhdsWithin.mono fun _y hys hs =>
      EventuallyEq.fderivWithin_eq (hs.filter_mono <| nhdsWithin_mono _ ht)
        (hs.self_of_nhdsWithin hys)

/--
theorem `Filter.EventuallyEq.fderivWithin` / 定理 `Filter.EventuallyEq.fderivWithin`

English:
theorem Filter.EventuallyEq.fderivWithin
  given: (hs : f₁ =ᶠ[𝓝[s] x] f)
  proof: hs.fderivWithin' Subset.rfl

中文:
定理 滤子.EventuallyEq.fderivWithin
  条件: (hs : f₁ =ᶠ[𝓝[s] x] f)
  证明: hs.fderivWithin' Subset.rfl
-/
protected theorem Filter.EventuallyEq.fderivWithin (hs : f₁ =ᶠ[𝓝[s] x] f) :
    fderivWithin 𝕜 f₁ s =ᶠ[𝓝[s] x] fderivWithin 𝕜 f s :=
  hs.fderivWithin' Subset.rfl

/--
theorem `Filter.EventuallyEq.fderivWithin_eq_of_nhds` / 定理 `Filter.EventuallyEq.fderivWithin_eq_of_nhds`

English:
theorem Filter.EventuallyEq.fderivWithin_eq_of_nhds
  given: (h : f₁ =ᶠ[𝓝 x] f)
  proof: (h.filter_mono nhdsWithin_le_nhds).fderivWithin_eq h.self_of_nhds

中文:
定理 滤子.EventuallyEq.fderivWithin_eq_of_nhds
  条件: (h : f₁ =ᶠ[𝓝 x] f)
  证明: (h.filter_mono nhdsWithin_le_nhds).fderivWithin_eq h.self_of_nhds

Depends on / 依赖: fderivWithin_eq, filter_mono, h.filter_mono, h.self_of_nhds, nhdsWithin_le_nhds, self_of_nhds
-/
theorem Filter.EventuallyEq.fderivWithin_eq_of_nhds (h : f₁ =ᶠ[𝓝 x] f) :
    fderivWithin 𝕜 f₁ s x = fderivWithin 𝕜 f s x :=
  (h.filter_mono nhdsWithin_le_nhds).fderivWithin_eq h.self_of_nhds

/--
theorem `fderivWithin_congr` / 定理 `fderivWithin_congr`

English:
theorem fderivWithin_congr
  given: (hs : EqOn f₁ f s) (hx : f₁ x = f x)
  proof: (hs.eventuallyEq.filter_mono inf_le_right).fderivWithin_eq hx

中文:
定理 fderivWithin_congr
  条件: (hs : EqOn f₁ f s) (hx : f₁ x = f x)
  证明: (hs.eventuallyEq.filter_mono inf_le_right).fderivWithin_eq hx

Depends on / 依赖: eventuallyEq, fderivWithin_eq, filter_mono, hs.eventuallyEq.filter_mono, inf_le_right
-/
theorem fderivWithin_congr (hs : EqOn f₁ f s) (hx : f₁ x = f x) :
    fderivWithin 𝕜 f₁ s x = fderivWithin 𝕜 f s x :=
  (hs.eventuallyEq.filter_mono inf_le_right).fderivWithin_eq hx

/--
theorem `fderivWithin_congr'` / 定理 `fderivWithin_congr'`

English:
theorem fderivWithin_congr'
  given: (hs : EqOn f₁ f s) (hx : x in s)
  proof: fderivWithin_congr hs (hs hx)

中文:
定理 fderivWithin_congr'
  条件: (hs : EqOn f₁ f s) (hx : x in s)
  证明: fderivWithin_congr hs (hs hx)

Depends on / 依赖: fderivWithin_congr
-/
theorem fderivWithin_congr' (hs : EqOn f₁ f s) (hx : x in s) :
    fderivWithin 𝕜 f₁ s x = fderivWithin 𝕜 f s x :=
  fderivWithin_congr hs (hs hx)

/--
theorem `Filter.EventuallyEq.fderiv_eq` / 定理 `Filter.EventuallyEq.fderiv_eq`

English:
theorem Filter.EventuallyEq.fderiv_eq
  given: (h : f₁ =ᶠ[𝓝 x] f)
  statement: fderiv 𝕜 f₁ x = fderiv 𝕜 f x
  proof: by
  rw [← fderivWithin_univ]; rw [← fderivWithin_univ]; rw [h.fderivWithin_eq_of_nhds]

中文:
定理 滤子.EventuallyEq.fderiv_eq
  条件: (h : f₁ =ᶠ[𝓝 x] f)
  结论: fderiv 𝕜 f₁ x = fderiv 𝕜 f x
  证明: by
  rw [← fderivWithin_univ]; rw [← fderivWithin_univ]; rw [h.fderivWithin_eq_of_nhds]

Depends on / 依赖: fderivWithin_eq_of_nhds, fderivWithin_univ, h.fderivWithin_eq_of_nhds
-/
theorem Filter.EventuallyEq.fderiv_eq (h : f₁ =ᶠ[𝓝 x] f) : fderiv 𝕜 f₁ x = fderiv 𝕜 f x := by
  rw [← fderivWithin_univ]; rw [← fderivWithin_univ]; rw [h.fderivWithin_eq_of_nhds]

/--
theorem `Filter.EventuallyEq.fderiv` / 定理 `Filter.EventuallyEq.fderiv`

English:
theorem Filter.EventuallyEq.fderiv
  given: (h : f₁ =ᶠ[𝓝 x] f)
  statement: fderiv 𝕜 f₁ =ᶠ[𝓝 x] fderiv 𝕜 f
  proof: h.eventuallyEq_nhds.mono fun _ h => h.fderiv_eq

中文:
定理 滤子.EventuallyEq.fderiv
  条件: (h : f₁ =ᶠ[𝓝 x] f)
  结论: fderiv 𝕜 f₁ =ᶠ[𝓝 x] fderiv 𝕜 f
  证明: h.eventuallyEq_nhds.mono fun _ h => h.fderiv_eq
-/
protected theorem Filter.EventuallyEq.fderiv (h : f₁ =ᶠ[𝓝 x] f) : fderiv 𝕜 f₁ =ᶠ[𝓝 x] fderiv 𝕜 f :=
  h.eventuallyEq_nhds.mono fun _ h => h.fderiv_eq

end congr

end
