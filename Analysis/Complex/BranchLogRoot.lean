/-
Copyright (c) 2026 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.Connected.LocallyPathConnected
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.UnitDisc.Basic
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Homotopy.Lifting

/-!
# Branches of logarithm and `n`th root on simply connected domains

In this file we prove that for a function `g : X → ℂ` defined on a locally path connected space
that is continuous on an open simply connected set `U` and `0 ∉ g '' U`,
there exist continuous branches of `log (g z)` and `ⁿ√(g z)` on `U`.
-/

public section

open Set

namespace Complex

variable {X : Type*} [TopologicalSpace X] [LocallyPathConnectedSpace X] {U : Set X}

/--
theorem `exists_continuousOn_eqOn_exp_comp` / 定理 `exists_continuousOn_eqOn_exp_comp`

English:
theorem exists_continuousOn_eqOn_exp_comp
  statement: (hUc : IsSimplyConnected U) (hUo : IsOpen U)
  proof: by
  classical
  have := hUc.simplyConnectedSpace
  have := hUo.locallyPathConnectedSpace
  rcases hUc.nonempty with ⟨x₀, hx₀U⟩
  have hx₀ : g x₀ != 0 := ne_of_mem_of_not_mem (mem_image_of_mem g hx₀U) hU₀
  lift x₀ to U using hx₀U
  rcases isCoveringMapOn_exp.existsUnique_continuousMap_lifts
    ⟨U.domRestrict g, continuousOn_iff_continuous_domRestrict.mp hgc⟩ (exp_log hx₀)
    (fun x => ne_of_mem_of_not_mem (mem_image_of_mem g x.2) hU₀) with ⟨f, ⟨-, hf⟩, -⟩
  obtain ⟨g, hg⟩ : exists g : X -> Complex, forall z : U, g z = f z :=
    ⟨fun z => if hz : z in U then f ⟨z, hz⟩ else 0, by simp⟩
  refine ⟨g, ?hg_cont, ?hg_inv⟩
  case hg_cont =>
    rw [continuousOn_iff_continuous_domRestrict]
    convert! map_continuous f
    ext z
    exact hg z
  case hg_inv =>
    intro x hx
    lift x to U using hx
    simpa [hg] using congr($hf x)

中文:
定理 存在_continuousOn_eqOn_exp_comp
  结论: (hUc : IsSimplyConnected U) (hUo : 是开集 U)
  证明: by
  classical
  have := hUc.simplyConnectedSpace
  have := hUo.locallyPathConnectedSpace
  rcases hUc.nonempty with ⟨x₀, hx₀U⟩
  have hx₀ : g x₀ != 0 := ne_of_mem_of_not_mem (mem_image_of_mem g hx₀U) hU₀
  lift x₀ to U using hx₀U
  rcases isCoveringMapOn_exp.existsUnique_continuousMap_lifts
    ⟨U.domRestrict g, continuousOn_iff_continuous_domRestrict.mp hgc⟩ (exp_log hx₀)
    (fun x => ne_of_mem_of_not_mem (mem_image_of_mem g x.2) hU₀) with ⟨f, ⟨-, hf⟩, -⟩
  obtain ⟨g, hg⟩ : exists g : X -> Complex, forall z : U, g z = f z :=
    ⟨fun z => if hz : z in U then f ⟨z, hz⟩ else 0, by simp⟩
  refine ⟨g, ?hg_cont, ?hg_inv⟩
  case hg_cont =>
    rw [continuousOn_iff_continuous_domRestrict]
    convert! map_continuous f
    ext z
    exact hg z
  case hg_inv =>
    intro x hx
    lift x to U using hx
    simpa [hg] using congr($hf x)

Depends on / 依赖: U.domRestrict, classical, continuousOn_iff_continuous_domRestrict, continuousOn_iff_continuous_domRestrict.mp, domRestrict, existsUnique_continuousMap_lifts, exp_log, hUc.nonempty, hUc.simplyConnectedSpace, hUo.locallyPathConnectedSpace, isCoveringMapOn_exp, isCoveringMapOn_exp.existsUnique_continuousMap_lifts, locallyPathConnectedSpace, mem_image_of_mem, ne_of_mem_of_not_mem, nonempty, simplyConnectedSpace
-/
theorem exists_continuousOn_eqOn_exp_comp (hUc : IsSimplyConnected U) (hUo : IsOpen U)
    {g : X -> Complex} (hgc : ContinuousOn g U) (hU₀ : 0 ∉ g '' U) :
    exists f : X -> Complex, ContinuousOn f U ∧ EqOn (exp ∘ f) g U := by
  classical
  have := hUc.simplyConnectedSpace
  have := hUo.locallyPathConnectedSpace
  rcases hUc.nonempty with ⟨x₀, hx₀U⟩
  have hx₀ : g x₀ != 0 := ne_of_mem_of_not_mem (mem_image_of_mem g hx₀U) hU₀
  lift x₀ to U using hx₀U
  rcases isCoveringMapOn_exp.existsUnique_continuousMap_lifts
    ⟨U.domRestrict g, continuousOn_iff_continuous_domRestrict.mp hgc⟩ (exp_log hx₀)
    (fun x => ne_of_mem_of_not_mem (mem_image_of_mem g x.2) hU₀) with ⟨f, ⟨-, hf⟩, -⟩
  obtain ⟨g, hg⟩ : exists g : X -> Complex, forall z : U, g z = f z :=
    ⟨fun z => if hz : z in U then f ⟨z, hz⟩ else 0, by simp⟩
  refine ⟨g, ?hg_cont, ?hg_inv⟩
  case hg_cont =>
    rw [continuousOn_iff_continuous_domRestrict]
    convert! map_continuous f
    ext z
    exact hg z
  case hg_inv =>
    intro x hx
    lift x to U using hx
    simpa [hg] using congr($hf x)

/--
theorem `exists_continuousOn_pow_eq` / 定理 `exists_continuousOn_pow_eq`

English:
theorem exists_continuousOn_pow_eq
  statement: (hUc : IsSimplyConnected U) (hUo : IsOpen U)
  proof: by
  classical
  rcases exists_continuousOn_eqOn_exp_comp hUc hUo hgc hU₀ with ⟨f, hfc, hf⟩
  refine ⟨U.piecewise (exp <| f · / n) (g · ^ (1 / n : Complex)), ?_, fun z => ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict, domRestrict_piecewise,
      ← continuousOn_iff_continuous_domRestrict]
    fun_prop
  · by_cases hz : z in U
    · simp [hz, ← exp_nat_mul, mul_div_cancel₀ (b := ↑n) (f z) (mod_cast hn), ← hf hz,
        Function.comp_apply]
    · simp [hz, ← cpow_mul_nat, hn]

中文:
定理 存在_continuousOn_pow_eq
  结论: (hUc : IsSimplyConnected U) (hUo : 是开集 U)
  证明: by
  classical
  rcases exists_continuousOn_eqOn_exp_comp hUc hUo hgc hU₀ with ⟨f, hfc, hf⟩
  refine ⟨U.piecewise (exp <| f · / n) (g · ^ (1 / n : Complex)), ?_, fun z => ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict, domRestrict_piecewise,
      ← continuousOn_iff_continuous_domRestrict]
    fun_prop
  · by_cases hz : z in U
    · simp [hz, ← exp_nat_mul, mul_div_cancel₀ (b := ↑n) (f z) (mod_cast hn), ← hf hz,
        Function.comp_apply]
    · simp [hz, ← cpow_mul_nat, hn]

Depends on / 依赖: Function, Function.comp_apply, U.piecewise, classical, comp_apply, continuousOn_iff_continuous_domRestrict, cpow_mul_nat, domRestrict_piecewise, exists_continuousOn_eqOn_exp_comp, exp_nat_mul, fun_prop, mod_cast, piecewise
-/
theorem exists_continuousOn_pow_eq (hUc : IsSimplyConnected U) (hUo : IsOpen U)
    {g : X -> Complex} (hgc : ContinuousOn g U) (hU₀ : 0 ∉ g '' U) {n : Nat} (hn : n != 0) :
    exists f : X -> Complex, ContinuousOn f U ∧ forall x, f x ^ n = g x := by
  classical
  rcases exists_continuousOn_eqOn_exp_comp hUc hUo hgc hU₀ with ⟨f, hfc, hf⟩
  refine ⟨U.piecewise (exp <| f · / n) (g · ^ (1 / n : Complex)), ?_, fun z => ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict, domRestrict_piecewise,
      ← continuousOn_iff_continuous_domRestrict]
    fun_prop
  · by_cases hz : z in U
    · simp [hz, ← exp_nat_mul, mul_div_cancel₀ (b := ↑n) (f z) (mod_cast hn), ← hf hz,
        Function.comp_apply]
    · simp [hz, ← cpow_mul_nat, hn]

namespace UnitDisc

/--
theorem `exists_continuousOn_pow_eq` / 定理 `exists_continuousOn_pow_eq`

English:
theorem exists_continuousOn_pow_eq
  proof: by
  rcases exists_continuousOn_pow_eq hUc hUo
    (continuous_coe.comp_continuousOn hgc)
    (by simpa using hU₀) n.ne_zero with ⟨f, hfc, hf⟩
  suffices forall x, ‖f x‖ < 1 by
    lift f to X -> 𝔻 using this
    refine ⟨f, isEmbedding_coe.continuousOn_iff.mpr hfc, fun x => ?_⟩
    simpa only [← coe_pow, Function.comp_apply, coe_inj] using hf x
  intro x
  rw [← pow_lt_one_iff_of_nonneg (norm_nonneg _) n.ne_zero]; rw [← norm_pow]; rw [hf]
  exact (g x).norm_lt_one

中文:
定理 存在_continuousOn_pow_eq
  证明: by
  rcases exists_continuousOn_pow_eq hUc hUo
    (continuous_coe.comp_continuousOn hgc)
    (by simpa using hU₀) n.ne_zero with ⟨f, hfc, hf⟩
  suffices forall x, ‖f x‖ < 1 by
    lift f to X -> 𝔻 using this
    refine ⟨f, isEmbedding_coe.continuousOn_iff.mpr hfc, fun x => ?_⟩
    simpa only [← coe_pow, Function.comp_apply, coe_inj] using hf x
  intro x
  rw [← pow_lt_one_iff_of_nonneg (norm_nonneg _) n.ne_zero]; rw [← norm_pow]; rw [hf]
  exact (g x).norm_lt_one
-/
protected theorem exists_continuousOn_pow_eq
    (hUc : IsSimplyConnected U) (hUo : IsOpen U) {g : X -> 𝔻}
    (hgc : ContinuousOn g U) (hU₀ : 0 ∉ g '' U) (n : Nat+) :
    exists f : X -> 𝔻, ContinuousOn f U ∧ forall x, f x ^ n = g x := by
  rcases exists_continuousOn_pow_eq hUc hUo
    (continuous_coe.comp_continuousOn hgc)
    (by simpa using hU₀) n.ne_zero with ⟨f, hfc, hf⟩
  suffices forall x, ‖f x‖ < 1 by
    lift f to X -> 𝔻 using this
    refine ⟨f, isEmbedding_coe.continuousOn_iff.mpr hfc, fun x => ?_⟩
    simpa only [← coe_pow, Function.comp_apply, coe_inj] using hf x
  intro x
  rw [← pow_lt_one_iff_of_nonneg (norm_nonneg _) n.ne_zero]; rw [← norm_pow]; rw [hf]
  exact (g x).norm_lt_one

end UnitDisc

end Complex
