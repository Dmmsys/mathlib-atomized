/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Composition.Comp
public import Mathlib.Probability.Kernel.Composition.MapComap

/-!
# Lemmas about compositions and maps of kernels

This file contains results that use both the composition of kernels and the map of a kernel by a
function.

Map and comap are particular cases of composition: they correspond to composition with
a deterministic kernel. See `deterministic_comp_eq_map` and `comp_deterministic_eq_comap`.

-/

public section


open MeasureTheory

open scoped ENNReal

namespace ProbabilityTheory

namespace Kernel

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}


variable {γ δ : Type*} {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ} {f : β -> γ} {g : γ -> α}

/--
theorem `deterministic_comp_eq_map` / 定理 `deterministic_comp_eq_map`

English:
theorem deterministic_comp_eq_map
  given: (hf : Measurable f) (κ : Kernel α β)
  proof: by
  ext a s hs
  simp_rw [map_apply' _ hf _ hs, comp_apply' _ _ _ hs, deterministic_apply' hf _ hs,
    lintegral_indicator_const_comp hf hs, one_mul]

中文:
定理 deterministic_comp_eq_map
  条件: (hf : Measurable f) (κ : Kernel α β)
  证明: by
  ext a s hs
  simp_rw [map_apply' _ hf _ hs, comp_apply' _ _ _ hs, deterministic_apply' hf _ hs,
    lintegral_indicator_const_comp hf hs, one_mul]

Depends on / 依赖: comp_apply, deterministic_apply, lintegral_indicator_const_comp, map_apply, one_mul, simp_rw
-/
theorem deterministic_comp_eq_map (hf : Measurable f) (κ : Kernel α β) :
    deterministic f hf ∘ₖ κ = map κ f := by
  ext a s hs
  simp_rw [map_apply' _ hf _ hs, comp_apply' _ _ _ hs, deterministic_apply' hf _ hs,
    lintegral_indicator_const_comp hf hs, one_mul]

/--
theorem `comp_deterministic_eq_comap` / 定理 `comp_deterministic_eq_comap`

English:
theorem comp_deterministic_eq_comap
  given: (κ : Kernel α β) (hg : Measurable g)
  proof: by
  ext a s hs
  simp_rw [comap_apply' _ _ _ s, comp_apply' _ _ _ hs, deterministic_apply hg a,
    lintegral_dirac' _ (Kernel.measurable_coe κ hs)]

中文:
定理 comp_deterministic_eq_comap
  条件: (κ : Kernel α β) (hg : Measurable g)
  证明: by
  ext a s hs
  simp_rw [comap_apply' _ _ _ s, comp_apply' _ _ _ hs, deterministic_apply hg a,
    lintegral_dirac' _ (Kernel.measurable_coe κ hs)]

Depends on / 依赖: Kernel, Kernel.measurable_coe, comap_apply, comp_apply, deterministic_apply, lintegral_dirac, measurable_coe, simp_rw
-/
theorem comp_deterministic_eq_comap (κ : Kernel α β) (hg : Measurable g) :
    κ ∘ₖ deterministic g hg = comap κ g hg := by
  ext a s hs
  simp_rw [comap_apply' _ _ _ s, comp_apply' _ _ _ hs, deterministic_apply hg a,
    lintegral_dirac' _ (Kernel.measurable_coe κ hs)]

/--
lemma `deterministic_comp_deterministic` / 引理 `deterministic_comp_deterministic`

English:
lemma deterministic_comp_deterministic
  given: (hf : Measurable f) (hg : Measurable g)
  proof: by
  ext; simp [comp_deterministic_eq_comap, comap_apply, deterministic_apply]

@[simp]

中文:
引理 deterministic_comp_deterministic
  条件: (hf : Measurable f) (hg : Measurable g)
  证明: by
  ext; simp [comp_deterministic_eq_comap, comap_apply, deterministic_apply]

@[simp]

Depends on / 依赖: comap_apply, comp_deterministic_eq_comap, deterministic_apply
-/
lemma deterministic_comp_deterministic (hf : Measurable f) (hg : Measurable g) :
    (deterministic g hg) ∘ₖ (deterministic f hf) = deterministic (g ∘ f) (hg.comp hf) := by
  ext; simp [comp_deterministic_eq_comap, comap_apply, deterministic_apply]

@[simp]
/--
lemma `swap_swap` / 引理 `swap_swap`

English:
lemma swap_swap
  statement: (swap α β) ∘ₖ (swap β α) = Kernel.id
  proof: by
  simp_rw [swap, Kernel.deterministic_comp_deterministic, Prod.swap_swap_eq, Kernel.id]

中文:
引理 swap_swap
  结论: (swap α β) ∘ₖ (swap β α) = Kernel.id
  证明: by
  simp_rw [swap, Kernel.deterministic_comp_deterministic, Prod.swap_swap_eq, Kernel.id]

Depends on / 依赖: Kernel, Kernel.deterministic_comp_deterministic, Kernel.id, Prod.swap_swap_eq, deterministic_comp_deterministic, simp_rw, swap_swap_eq
-/
lemma swap_swap : (swap α β) ∘ₖ (swap β α) = Kernel.id := by
  simp_rw [swap, Kernel.deterministic_comp_deterministic, Prod.swap_swap_eq, Kernel.id]

/--
lemma `swap_comp_eq_map` / 引理 `swap_comp_eq_map`

English:
lemma swap_comp_eq_map
  given: {κ : Kernel α (β × γ)}
  statement: (swap β γ) ∘ₖ κ = κ.map Prod.swap
  proof: by
  rw [swap]; rw [deterministic_comp_eq_map]

中文:
引理 swap_comp_eq_map
  条件: {κ : Kernel α (β × γ)}
  结论: (swap β γ) ∘ₖ κ = κ.map Prod.swap
  证明: by
  rw [swap]; rw [deterministic_comp_eq_map]

Depends on / 依赖: deterministic_comp_eq_map
-/
lemma swap_comp_eq_map {κ : Kernel α (β × γ)} : (swap β γ) ∘ₖ κ = κ.map Prod.swap := by
  rw [swap]; rw [deterministic_comp_eq_map]

/--
lemma `map_comp` / 引理 `map_comp`

English:
lemma map_comp
  given: (κ : Kernel α β) (η : Kernel β γ) (f : γ -> δ)
  proof: by
  by_cases hf : Measurable f
  · ext a s hs
    rw [map_apply' _ hf _ hs]; rw [comp_apply']; rw [comp_apply' _ _ _ hs]
    · simp_rw [map_apply' _ hf _ hs]
    · exact hf hs
  · simp [map_of_not_measurable _ hf]

中文:
引理 map_comp
  条件: (κ : Kernel α β) (η : Kernel β γ) (f : γ -> δ)
  证明: by
  by_cases hf : Measurable f
  · ext a s hs
    rw [map_apply' _ hf _ hs]; rw [comp_apply']; rw [comp_apply' _ _ _ hs]
    · simp_rw [map_apply' _ hf _ hs]
    · exact hf hs
  · simp [map_of_not_measurable _ hf]

Depends on / 依赖: Measurable, comp_apply, map_apply, map_of_not_measurable, simp_rw
-/
lemma map_comp (κ : Kernel α β) (η : Kernel β γ) (f : γ -> δ) :
    (η ∘ₖ κ).map f = (η.map f) ∘ₖ κ := by
  by_cases hf : Measurable f
  · ext a s hs
    rw [map_apply' _ hf _ hs]; rw [comp_apply']; rw [comp_apply' _ _ _ hs]
    · simp_rw [map_apply' _ hf _ hs]
    · exact hf hs
  · simp [map_of_not_measurable _ hf]

/--
lemma `comp_map` / 引理 `comp_map`

English:
lemma comp_map
  given: (κ : Kernel α β) (η : Kernel γ δ) {f : β -> γ} (hf : Measurable f)
  proof: by
  ext x s ms
  rw [comp_apply' _ _ _ ms]; rw [lintegral_map _ hf _ (η.measurable_coe ms)]; rw [comp_apply' _ _ _ ms]
  simp_rw [comap_apply']

中文:
引理 comp_map
  条件: (κ : Kernel α β) (η : Kernel γ δ) {f : β -> γ} (hf : Measurable f)
  证明: by
  ext x s ms
  rw [comp_apply' _ _ _ ms]; rw [lintegral_map _ hf _ (η.measurable_coe ms)]; rw [comp_apply' _ _ _ ms]
  simp_rw [comap_apply']

Depends on / 依赖: comap_apply, comp_apply, lintegral_map, measurable_coe, simp_rw
-/
lemma comp_map (κ : Kernel α β) (η : Kernel γ δ) {f : β -> γ} (hf : Measurable f) :
    η ∘ₖ (κ.map f) = (η.comap f hf) ∘ₖ κ := by
  ext x s ms
  rw [comp_apply' _ _ _ ms]; rw [lintegral_map _ hf _ (η.measurable_coe ms)]; rw [comp_apply' _ _ _ ms]
  simp_rw [comap_apply']

/--
lemma `fst_comp` / 引理 `fst_comp`

English:
lemma fst_comp
  given: (κ : Kernel α β) (η : Kernel β (γ × δ))
  statement: (η ∘ₖ κ).fst = η.fst ∘ₖ κ
  proof: by
  simp [fst_eq, map_comp κ η _]

中文:
引理 fst_comp
  条件: (κ : Kernel α β) (η : Kernel β (γ × δ))
  结论: (η ∘ₖ κ).fst = η.fst ∘ₖ κ
  证明: by
  simp [fst_eq, map_comp κ η _]

Depends on / 依赖: fst_eq, map_comp
-/
lemma fst_comp (κ : Kernel α β) (η : Kernel β (γ × δ)) : (η ∘ₖ κ).fst = η.fst ∘ₖ κ := by
  simp [fst_eq, map_comp κ η _]

/--
lemma `snd_comp` / 引理 `snd_comp`

English:
lemma snd_comp
  given: (κ : Kernel α β) (η : Kernel β (γ × δ))
  statement: (η ∘ₖ κ).snd = η.snd ∘ₖ κ
  proof: by
  simp_rw [snd_eq, map_comp κ η _]

中文:
引理 snd_comp
  条件: (κ : Kernel α β) (η : Kernel β (γ × δ))
  结论: (η ∘ₖ κ).snd = η.snd ∘ₖ κ
  证明: by
  simp_rw [snd_eq, map_comp κ η _]

Depends on / 依赖: map_comp, simp_rw, snd_eq
-/
lemma snd_comp (κ : Kernel α β) (η : Kernel β (γ × δ)) : (η ∘ₖ κ).snd = η.snd ∘ₖ κ := by
  simp_rw [snd_eq, map_comp κ η _]

end Kernel
end ProbabilityTheory
