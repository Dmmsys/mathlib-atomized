/-
Copyright (c) 2025 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
public import Mathlib.Topology.MetricSpace.UniformConvergence
public import Mathlib.Topology.UniformSpace.CompactConvergence

/-! # Continuity of the continuous functional calculus in each variable

The continuous functional calculus is a map which takes a pair `a : A` (`A` is a C⋆-algebra) and
a function `f : C(spectrum R a, R)` where `a` satisfies some predicate `p`, depending on `R` and
returns another element of the algebra `A`. This is the map `cfcHom`. The class
`ContinuousFunctionalCalculus` declares that `cfcHom` is a continuous map from `C(spectrum R a, R)`
to `A`. However, users generally interact with the continuous functional calculus through `cfc`,
which operates on bare functions `f : R → R` instead and takes a junk value when `f` is not
continuous on the spectrum of `a`. In this file we provide some lemma concerning the continuity
of `cfc`, subject to natural hypotheses.

However, the continuous functional calculus is *also* continuous in the variable `a`, but there
are some conditions that must be satisfied. In particular, given a function `f : R → R` the map
`a ↦ cfc f a` is continuous so long as `a` varies over a collection of elements satisfying the
predicate `p` and their spectra are collectively contained in a compact set on which `f` is
continuous. Moreover, it is required that the continuous functional calculus be the isometric
variant.

Under the assumption of `IsometricContinuousFunctionalCalculus`, we show that the continuous
functional calculus is Lipschitz with constant 1 in the variable `f : R →ᵤ[{spectrum R a}] R`
on the set of functions which are continuous on the spectrum of `a`. Combining this with the
continuity of the continuous functional calculus in the variable `a`, we obtain a joint continuity
result for `cfc` in both variables.

Finally, all of this is developed for both the unital and non-unital functional calculi.
The continuity results in the function variable are valid for all scalar rings, but the continuity
results in the variable `a` come in two flavors: those for `RCLike 𝕜` and those for `ℝ≥0`.

## Main results


+ `tendsto_cfc_fun`: If `F : X → R → R` tends to `f : R → R` uniformly on the spectrum of `a`, and
  all these functions are continuous on the spectrum, then `fun x ↦ cfc (F x) a` tends
  to `cfc f a`.
+ `Filter.Tendsto.cfc`: If `f : 𝕜 → 𝕜` is continuous on a compact set `s` and `a : X → A` tends to
  `a₀ : A` along a filter `l` (such that eventually `a x` satisfies the predicate `p` associated to
  `𝕜` and has spectrum contained in `s`, as does `a₀`), then `fun x ↦ cfc f (a x)` tends to
  `cfc f a₀`.
+ `lipschitzOnWith_cfc_fun`: The function `f ↦ cfc f a` is Lipschitz with constant with constant 1
  with respect to supremum metric (on `R →ᵤ[{spectrum R a}] R`) on those functions which are
  continuous on the spectrum.
+ `continuousOn_cfc`: For `f : 𝕜 → 𝕜` continuous on a compact set `s`, `cfc f` is continuous on the
  set of `a : A` satisfying the predicate `p` (associated to `𝕜`) and whose `𝕜`-spectrum is
  contained in `s`.
+ `continuousOn_cfc_setProd`: Let `s : Set 𝕜` be a compact set and consider pairs
  `(f, a) : (𝕜 → 𝕜) × A` where `f` is continuous on `s` and `spectrum 𝕜 a ⊆ s` and `a` satisfies
  the predicate `p a` for the continuous functional calculus. Then `cfc` is jointly continuous in
  both variables (i.e., continuous in its uncurried form) on this set of pairs when the function
  space is equipped with the topology of uniform convergence on `s`.
+ Versions of all of the above for non-unital algebras, and versions over `ℝ≥0` as well.

-/

public section

open scoped UniformConvergence NNReal
open Filter Topology

section Unital

section Left

section Generic

variable {X R A : Type*} {p : A -> Prop} [CommSemiring R] [StarRing R] [MetricSpace R]
    [IsTopologicalSemiring R] [ContinuousStar R] [Ring A] [StarRing A]
    [TopologicalSpace A] [Algebra R A] [ContinuousFunctionalCalculus R A p]

/--
theorem `tendsto_cfc_fun` / 定理 `tendsto_cfc_fun`

English:
theorem tendsto_cfc_fun
  statement: {l : Filter X} {F : X -> R -> R} {f : R -> R} {a : A}
  proof: by
  open scoped ContinuousFunctionalCalculus in
  obtain (rfl | hl) := l.eq_or_neBot
  · simp
  have hf := h_tendsto.continuousOn hF.frequently
  by_cases ha : p a
  · let s : Set X := {x | ContinuousOn (F x) (spectrum R a)}
    rw [← tendsto_comap'_iff (i := ((↑) : s -> X)) (by simpa)]
    conv =>

中文:
定理 tendsto_cfc_fun
  结论: {l : 滤子 X} {F : X -> R -> R} {f : R -> R} {a : A}
  证明: by
  open scoped ContinuousFunctionalCalculus in
  obtain (rfl | hl) := l.eq_or_neBot
  · simp
  have hf := h_tendsto.continuousOn hF.frequently
  by_cases ha : p a
  · let s : Set X := {x | ContinuousOn (F x) (spectrum R a)}
    rw [← tendsto_comap'_iff (i := ((↑) : s -> X)) (by simpa)]
    conv =>

Depends on / 依赖: ContinuousFunctionalCalculus, ContinuousOn, Function, Function.comp_apply, Subtype, Subtype.property, _iff, cfcHom_continuous, cfc_apply, comp_apply, continuousOn, eq_or_neBot, frequently, hF.frequently, h_tendsto, h_tendsto.continuousOn, hf.tendsto_domRestrict_iff_tendstoUniformlyOn, l.eq_or_neBot, property, scoped
-/
theorem tendsto_cfc_fun {l : Filter X} {F : X -> R -> R} {f : R -> R} {a : A}
    (h_tendsto : TendstoUniformlyOn F f l (spectrum R a))
    (hF : forallᶠ x in l, ContinuousOn (F x) (spectrum R a)) :
    Tendsto (fun x => cfc (F x) a) l (𝓝 (cfc f a)) := by
  open scoped ContinuousFunctionalCalculus in
  obtain (rfl | hl) := l.eq_or_neBot
  · simp
  have hf := h_tendsto.continuousOn hF.frequently
  by_cases ha : p a
  · let s : Set X := {x | ContinuousOn (F x) (spectrum R a)}
    rw [← tendsto_comap'_iff (i := ((↑) : s -> X)) (by simpa)]
    conv =>
      enter [1, x]
      rw [Function.comp_apply]; rw [cfc_apply (hf := x.2)]
    rw [cfc_apply ..]
.comp .tendsto _ apply cfcHom_continuous _
    rw [hf.tendsto_domRestrict_iff_tendstoUniformlyOn Subtype.property]
    intro t
    simp only [eventually_comap, Subtype.forall]
    peel h_tendsto t with ht x _
    simp_all
  · simpa [cfc_apply_of_not_predicate a ha] using tendsto_const_nhds

/--
theorem `continuousAt_cfc_fun` / 定理 `continuousAt_cfc_fun`

English:
theorem continuousAt_cfc_fun
  statement: [TopologicalSpace X] {f : X -> R -> R} {a : A}
  proof: tendsto_cfc_fun h_tendsto hf

中文:
定理 continuousAt_cfc_fun
  结论: [拓扑空间 X] {f : X -> R -> R} {a : A}
  证明: tendsto_cfc_fun h_tendsto hf

Depends on / 依赖: h_tendsto, tendsto_cfc_fun
-/
theorem continuousAt_cfc_fun [TopologicalSpace X] {f : X -> R -> R} {a : A}
    {x₀ : X} (h_tendsto : TendstoUniformlyOn f (f x₀) (𝓝 x₀) (spectrum R a))
    (hf : forallᶠ x in 𝓝 x₀, ContinuousOn (f x) (spectrum R a)) :
    ContinuousAt (fun x => cfc (f x) a) x₀ :=
  tendsto_cfc_fun h_tendsto hf

/--
theorem `continuousWithinAt_cfc_fun` / 定理 `continuousWithinAt_cfc_fun`

English:
theorem continuousWithinAt_cfc_fun
  statement: [TopologicalSpace X] {f : X -> R -> R} {a : A}
  proof: tendsto_cfc_fun h_tendsto hf

中文:
定理 continuousWithinAt_cfc_fun
  结论: [拓扑空间 X] {f : X -> R -> R} {a : A}
  证明: tendsto_cfc_fun h_tendsto hf

Depends on / 依赖: h_tendsto, tendsto_cfc_fun
-/
theorem continuousWithinAt_cfc_fun [TopologicalSpace X] {f : X -> R -> R} {a : A}
    {x₀ : X} {s : Set X} (h_tendsto : TendstoUniformlyOn f (f x₀) (𝓝[s] x₀) (spectrum R a))
    (hf : forallᶠ x in 𝓝[s] x₀, ContinuousOn (f x) (spectrum R a)) :
    ContinuousWithinAt (fun x => cfc (f x) a) s x₀ :=
  tendsto_cfc_fun h_tendsto hf

open UniformOnFun in
/--
theorem `ContinuousOn.cfc_fun` / 定理 `ContinuousOn.cfc_fun`

English:
theorem ContinuousOn.cfc_fun
  statement: [TopologicalSpace X] {f : X -> R -> R} {a : A} {s : Set X}
  proof: by
  rw [ContinuousOn] at h_cont ⊢
  simp only [ContinuousWithinAt, UniformOnFun.tendsto_iff_tendstoUniformlyOn, Set.mem_singleton_iff,
    Function.comp_def, toFun_ofFun, forall_eq] at h_cont
  refine fun x hx => continuousWithinAt_cfc_fun (h_cont x hx) ?_
  filter_upwards [self_mem_nhdsWithin] wit

中文:
定理 ContinuousOn.cfc_fun
  结论: [拓扑空间 X] {f : X -> R -> R} {a : A} {s : 集合 X}
  证明: by
  rw [ContinuousOn] at h_cont ⊢
  simp only [ContinuousWithinAt, UniformOnFun.tendsto_iff_tendstoUniformlyOn, Set.mem_singleton_iff,
    Function.comp_def, toFun_ofFun, forall_eq] at h_cont
  refine fun x hx => continuousWithinAt_cfc_fun (h_cont x hx) ?_
  filter_upwards [self_mem_nhdsWithin] wit

Depends on / 依赖: ContinuousOn, ContinuousWithinAt, Function, Function.comp_def, Set.mem_singleton_iff, UniformOnFun, UniformOnFun.tendsto_iff_tendstoUniformlyOn, cfc_cont_tac, comp_def, continuousWithinAt_cfc_fun, filter_upwards, forall_eq, h_cont, mem_singleton_iff, self_mem_nhdsWithin, tendsto_iff_tendstoUniformlyOn, toFun_ofFun
-/
theorem ContinuousOn.cfc_fun [TopologicalSpace X] {f : X -> R -> R} {a : A} {s : Set X}
    (h_cont : ContinuousOn (fun x => ofFun {spectrum R a} (f x)) s)
    (hf : forall x in s, ContinuousOn (f x) (spectrum R a) := by cfc_cont_tac) :
    ContinuousOn (fun x => cfc (f x) a) s := by
  rw [ContinuousOn] at h_cont ⊢
  simp only [ContinuousWithinAt, UniformOnFun.tendsto_iff_tendstoUniformlyOn, Set.mem_singleton_iff,
    Function.comp_def, toFun_ofFun, forall_eq] at h_cont
  refine fun x hx => continuousWithinAt_cfc_fun (h_cont x hx) ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact hf x hx

open UniformOnFun in
/--
theorem `Continuous.cfc_fun` / 定理 `Continuous.cfc_fun`

English:
theorem Continuous.cfc_fun
  statement: [TopologicalSpace X] (f : X -> R -> R) (a : A)
  proof: by
  rw [← continuousOn_univ] at h_cont ⊢
  exact h_cont.cfc_fun (fun x _ => hf x)

中文:
定理 连续.cfc_fun
  结论: [拓扑空间 X] (f : X -> R -> R) (a : A)
  证明: by
  rw [← continuousOn_univ] at h_cont ⊢
  exact h_cont.cfc_fun (fun x _ => hf x)

Depends on / 依赖: Continuous, cfc_cont_tac, cfc_fun, continuousOn_univ, h_cont, h_cont.cfc_fun
-/
theorem Continuous.cfc_fun [TopologicalSpace X] (f : X -> R -> R) (a : A)
    (h_cont : Continuous (fun x => ofFun {spectrum R a} (f x)))
    (hf : forall x, ContinuousOn (f x) (spectrum R a) := by cfc_cont_tac) :
    Continuous fun x => cfc (f x) a := by
  rw [← continuousOn_univ] at h_cont ⊢
  exact h_cont.cfc_fun (fun x _ => hf x)

end Generic

section Isometric

variable {X R A : Type*} {p : A -> Prop} [CommSemiring R] [StarRing R] [MetricSpace R]
    [IsTopologicalSemiring R] [ContinuousStar R] [Ring A] [StarRing A]
    [MetricSpace A] [Algebra R A] [IsometricContinuousFunctionalCalculus R A p]

variable (R) in
open UniformOnFun in
open scoped ContinuousFunctionalCalculus in
/--
lemma `lipschitzOnWith_cfc_fun` / 引理 `lipschitzOnWith_cfc_fun`

English:
lemma lipschitzOnWith_cfc_fun
  given: (a : A)
  proof: by
  by_cases ha : p a
  · intro f hf g hg
    simp only
    rw [cfc_apply ..]; rw [cfc_apply ..]; rw [isometry_cfcHom (R := R) a ha |>.edist_eq]
    simp only [ENNReal.coe_one, one_mul]
    rw [edist_continuousRestrict_of_singleton hf hg]
.lipschitzOnWith · simpa [cfc_apply_of_not_predicate a ha] u

中文:
引理 lipschitzOnWith_cfc_fun
  条件: (a : A)
  证明: by
  by_cases ha : p a
  · intro f hf g hg
    simp only
    rw [cfc_apply ..]; rw [cfc_apply ..]; rw [isometry_cfcHom (R := R) a ha |>.edist_eq]
    simp only [ENNReal.coe_one, one_mul]
    rw [edist_continuousRestrict_of_singleton hf hg]
.lipschitzOnWith · simpa [cfc_apply_of_not_predicate a ha] u

Depends on / 依赖: ENNReal, ENNReal.coe_one, LipschitzWith, LipschitzWith.const, cfc_apply, cfc_apply_of_not_predicate, coe_one, edist_continuousRestrict_of_singleton, edist_eq, isometry_cfcHom, lipschitzOnWith, one_mul
-/
lemma lipschitzOnWith_cfc_fun (a : A) :
    LipschitzOnWith 1 (fun f => cfc (toFun {spectrum R a} f) a)
      {f | ContinuousOn (toFun {spectrum R a} f) (spectrum R a)} := by
  by_cases ha : p a
  · intro f hf g hg
    simp only
    rw [cfc_apply ..]; rw [cfc_apply ..]; rw [isometry_cfcHom (R := R) a ha |>.edist_eq]
    simp only [ENNReal.coe_one, one_mul]
    rw [edist_continuousRestrict_of_singleton hf hg]
.lipschitzOnWith · simpa [cfc_apply_of_not_predicate a ha] using LipschitzWith.const' 0

open UniformOnFun in
open scoped ContinuousFunctionalCalculus in
/--
lemma `lipschitzOnWith_cfc_fun_of_subset` / 引理 `lipschitzOnWith_cfc_fun_of_subset`

English:
lemma lipschitzOnWith_cfc_fun_of_subset
  given: (a : A) {s : Set R} (hs : spectrum R a subseteq s)
  proof: by
  have h₁ := lipschitzOnWith_cfc_fun R a
  have h₂ := lipschitzWith_one_ofFun_toFun' (𝔖 := {spectrum R a}) (𝔗 := {s}) (β := R) (by simpa)
  have h₃ := h₂.lipschitzOnWith (s := {f | ContinuousOn (toFun {s} f) (s)})
  simpa using! h₁.comp h₃ (fun f hf => hf.mono hs)

中文:
引理 lipschitzOnWith_cfc_fun_of_subset
  条件: (a : A) {s : 集合 R} (hs : spectrum R a subseteq s)
  证明: by
  have h₁ := lipschitzOnWith_cfc_fun R a
  have h₂ := lipschitzWith_one_ofFun_toFun' (𝔖 := {spectrum R a}) (𝔗 := {s}) (β := R) (by simpa)
  have h₃ := h₂.lipschitzOnWith (s := {f | ContinuousOn (toFun {s} f) (s)})
  simpa using! h₁.comp h₃ (fun f hf => hf.mono hs)

Depends on / 依赖: ContinuousOn, hf.mono, lipschitzOnWith, lipschitzOnWith_cfc_fun, lipschitzWith_one_ofFun_toFun, spectrum
-/
lemma lipschitzOnWith_cfc_fun_of_subset (a : A) {s : Set R} (hs : spectrum R a subseteq s) :
    LipschitzOnWith 1 (fun f => cfc (toFun {s} f) a)
      {f | ContinuousOn (toFun {s} f) (s)} := by
  have h₁ := lipschitzOnWith_cfc_fun R a
  have h₂ := lipschitzWith_one_ofFun_toFun' (𝔖 := {spectrum R a}) (𝔗 := {s}) (β := R) (by simpa)
  have h₃ := h₂.lipschitzOnWith (s := {f | ContinuousOn (toFun {s} f) (s)})
  simpa using! h₁.comp h₃ (fun f hf => hf.mono hs)

end Isometric

end Left

section Right
section RCLike

variable {X 𝕜 A : Type*} {p : A -> Prop} [RCLike 𝕜] [NormedRing A] [StarRing A]
    [NormedAlgebra 𝕜 A] [IsometricContinuousFunctionalCalculus 𝕜 A p]
    [ContinuousStar A]

/--
theorem `continuous_cfcHomSuperset_left` / 定理 `continuous_cfcHomSuperset_left`

English:
theorem continuous_cfcHomSuperset_left
  proof: by
  open scoped ContinuousFunctionalCalculus in
  have : CompactSpace s := by rwa [isCompact_iff_compactSpace] at hs
  induction f using ContinuousMap.induction_on_of_compact with
  | const r =>
    have : ContinuousMap.const s r = algebraMap 𝕜 C(s, 𝕜) r := rfl
    simpa only [this, AlgHomClass.com

中文:
定理 continuous_cfcHomSuperset_left
  证明: by
  open scoped ContinuousFunctionalCalculus in
  have : CompactSpace s := by rwa [isCompact_iff_compactSpace] at hs
  induction f using ContinuousMap.induction_on_of_compact with
  | const r =>
    have : ContinuousMap.const s r = algebraMap 𝕜 C(s, 𝕜) r := rfl
    simpa only [this, AlgHomClass.com

Depends on / 依赖: AlgHomClass, AlgHomClass.commutes, CompactSpace, Continuous, ContinuousFunctionalCalculus, ContinuousMap, ContinuousMap.const, ContinuousMap.induction_on_of_compact, algebraMap, cfcHomSuperset, cfcHomSuperset_id, cfc_tac, commutes, continuous_const, fun_prop, induction_on_of_compact, isCompact_iff_compactSpace, map_star, scoped, star_id
-/
theorem continuous_cfcHomSuperset_left
    [TopologicalSpace X] {s : Set 𝕜} (hs : IsCompact s) (f : C(s, 𝕜))
    (a : X -> A) (ha_cont : Continuous a) (ha : forall x, spectrum 𝕜 (a x) subseteq s)
    (ha' : forall x, p (a x) := by cfc_tac) :
    Continuous (fun x => cfcHomSuperset (ha' x) (ha x) f) := by
  open scoped ContinuousFunctionalCalculus in
  have : CompactSpace s := by rwa [isCompact_iff_compactSpace] at hs
  induction f using ContinuousMap.induction_on_of_compact with
  | const r =>
    have : ContinuousMap.const s r = algebraMap 𝕜 C(s, 𝕜) r := rfl
    simpa only [this, AlgHomClass.commutes] using! continuous_const
  | id =>
    simp only [cfcHomSuperset_id]
    fun_prop
  | star_id =>
    simp only [map_star, cfcHomSuperset_id]
    fun_prop
  | add f g hf hg => simpa using! hf.add hg
  | mul f g hf hg => simpa using! hf.mul hg
  | frequently f hf =>
    apply continuous_of_uniform_approx_of_continuous
    rw [Metric.uniformity_basis_dist_le.forall_iff (by aesop)]
    intro ε hε
    simp only [Set.mem_ofPred_eq, dist_eq_norm]
    obtain ⟨g, hg, g_cont⟩ := frequently_iff.mp hf (Metric.closedBall_mem_nhds f hε)
    simp only [Metric.mem_closedBall, dist_comm g, dist_eq_norm] at hg
    refine ⟨_, g_cont, fun x => ?_⟩
    rw [← map_sub]; rw [cfcHomSuperset_apply]
    rw [isometry_cfcHom (R := 𝕜) _ (ha' x) |>.norm_map_of_map_zero (map_zero (cfcHom (ha' x)))]
    rw [ContinuousMap.norm_le _ hε.le] at hg ⊢
    aesop

variable (A) in
/--
theorem `continuousOn_cfc` / 定理 `continuousOn_cfc`

English:
theorem continuousOn_cfc
  statement: {s : Set 𝕜} (hs : IsCompact s) (f : 𝕜 -> 𝕜)
  proof: continuousOn_iff_continuous_domRestrict.mpr by
    convert!
      continuous_cfcHomSuperset_left hs ⟨_, hf.domRestrict⟩
        ((↑) : {a | p a ∧ spectrum 𝕜 a subseteq s} -> A)
        continuous_subtype_val (fun x => x.2.2) with
      x
    rw [cfcHomSuperset_apply]; rw [Set.domRestrict_apply]; rw 

中文:
定理 continuousOn_cfc
  结论: {s : 集合 𝕜} (hs : 是紧集 s) (f : 𝕜 -> 𝕜)
  证明: continuousOn_iff_continuous_domRestrict.mpr by
    convert!
      continuous_cfcHomSuperset_left hs ⟨_, hf.domRestrict⟩
        ((↑) : {a | p a ∧ spectrum 𝕜 a subseteq s} -> A)
        continuous_subtype_val (fun x => x.2.2) with
      x
    rw [cfcHomSuperset_apply]; rw [Set.domRestrict_apply]; rw 

Depends on / 依赖: ContinuousOn, Set.domRestrict_apply, cfcHomSuperset_apply, cfc_apply, cfc_cont_tac, continuousOn_iff_continuous_domRestrict, continuousOn_iff_continuous_domRestrict.mpr, continuous_cfcHomSuperset_left, continuous_subtype_val, convert, domRestrict, domRestrict_apply, hf.domRestrict, hf.mono, spectrum, subseteq
-/
theorem continuousOn_cfc {s : Set 𝕜} (hs : IsCompact s) (f : 𝕜 -> 𝕜)
    (hf : ContinuousOn f s := by cfc_cont_tac) :
    ContinuousOn (cfc f) {a | p a ∧ spectrum 𝕜 a subseteq s} :=
continuousOn_iff_continuous_domRestrict.mpr by
    convert!
      continuous_cfcHomSuperset_left hs ⟨_, hf.domRestrict⟩
        ((↑) : {a | p a ∧ spectrum 𝕜 a subseteq s} -> A)
        continuous_subtype_val (fun x => x.2.2) with
      x
    rw [cfcHomSuperset_apply]; rw [Set.domRestrict_apply]; rw [cfc_apply _ _ x.2.1 (hf.mono x.2.2)]
    congr!

open UniformOnFun in
/--
theorem `continuousOn_cfc_setProd` / 定理 `continuousOn_cfc_setProd`

English:
theorem continuousOn_cfc_setProd
  given: {s : Set 𝕜} (hs : IsCompact s)
  proof: continuousOn_prod_of_continuousOn_lipschitzOnWith _ 1
    (fun f hf => continuousOn_cfc A hs ((toFun {s}) f) hf)
    (fun a ⟨_, ha'⟩ => lipschitzOnWith_cfc_fun_of_subset a ha')

中文:
定理 continuousOn_cfc_setProd
  条件: {s : 集合 𝕜} (hs : 是紧集 s)
  证明: continuousOn_prod_of_continuousOn_lipschitzOnWith _ 1
    (fun f hf => continuousOn_cfc A hs ((toFun {s}) f) hf)
    (fun a ⟨_, ha'⟩ => lipschitzOnWith_cfc_fun_of_subset a ha')

Depends on / 依赖: continuousOn_cfc, continuousOn_prod_of_continuousOn_lipschitzOnWith, lipschitzOnWith_cfc_fun_of_subset
-/
theorem continuousOn_cfc_setProd {s : Set 𝕜} (hs : IsCompact s) :
    ContinuousOn (fun fa : (𝕜 ->ᵤ[{s}] 𝕜) × A => cfc (toFun {s} fa.1) fa.2)
      ({f | ContinuousOn (toFun {s} f) s} ×ˢ {a | p a ∧ spectrum 𝕜 a subseteq s}) :=
  continuousOn_prod_of_continuousOn_lipschitzOnWith _ 1
    (fun f hf => continuousOn_cfc A hs ((toFun {s}) f) hf)
    (fun a ⟨_, ha'⟩ => lipschitzOnWith_cfc_fun_of_subset a ha')

open UniformOnFun in
/--
theorem `continuousOn_cfc_setProd_nhdsSet` / 定理 `continuousOn_cfc_setProd_nhdsSet`

English:
theorem continuousOn_cfc_setProd_nhdsSet
  given: [CompleteSpace A] {s : Set 𝕜}
  proof: by
  refine continuousOn_of_locally_continuousOn fun (f, a) ⟨hf, ha, has⟩ => ?_
  have hs := ContinuousFunctionalCalculus.isCompact_spectrum (R := 𝕜) a
  obtain ⟨k, ⟨hka, hk⟩, hks⟩ := hs.nhdsSet_basis_isCompact.mem_iff.mp has
  have := (upperHemicontinuous_spectrum 𝕜 A).isOpen k
  refine ⟨Set.univ ×

中文:
定理 continuousOn_cfc_setProd_nhdsSet
  条件: [完备空间 A] {s : 集合 𝕜}
  证明: by
  refine continuousOn_of_locally_continuousOn fun (f, a) ⟨hf, ha, has⟩ => ?_
  have hs := ContinuousFunctionalCalculus.isCompact_spectrum (R := 𝕜) a
  obtain ⟨k, ⟨hka, hk⟩, hks⟩ := hs.nhdsSet_basis_isCompact.mem_iff.mp has
  have := (upperHemicontinuous_spectrum 𝕜 A).isOpen k
  refine ⟨Set.univ ×

Depends on / 依赖: ContinuousFunctionalCalculus, ContinuousFunctionalCalculus.isCompact_spectrum, IsCompact, Set.univ, continuousOn_cfc_setPr, continuousOn_of_locally_continuousOn, equals, hs.nhdsSet_basis_isCompact.mem_iff.mp, isCompact_spectrum, isOpen, isOpen_univ, isOpen_univ.prod, mem_iff, nhdsSet_basis_isCompact, spectrum, subseteq, upperHemicontinuous_spectrum
-/
theorem continuousOn_cfc_setProd_nhdsSet [CompleteSpace A] {s : Set 𝕜} :
    ContinuousOn (fun fa : (𝕜 ->ᵤ[{t | IsCompact t ∧ t subseteq s}] 𝕜) × A => cfc (toFun {s} fa.1) fa.2)
      ({f | ContinuousOn (toFun {t | IsCompact t ∧ t subseteq s} f) s} ×ˢ
        {a | p a ∧ s in 𝓝ˢ (spectrum 𝕜 a)}) := by
  refine continuousOn_of_locally_continuousOn fun (f, a) ⟨hf, ha, has⟩ => ?_
  have hs := ContinuousFunctionalCalculus.isCompact_spectrum (R := 𝕜) a
  obtain ⟨k, ⟨hka, hk⟩, hks⟩ := hs.nhdsSet_basis_isCompact.mem_iff.mp has
  have := (upperHemicontinuous_spectrum 𝕜 A).isOpen k
  refine ⟨Set.univ ×ˢ {x | k in 𝓝ˢ (spectrum 𝕜 x)}, isOpen_univ.prod this, by simpa, ?_⟩
  conv in cfc _ => equals cfc (toFun {k} (ofFun {k} (toFun {t | IsCompact t ∧ t subseteq s} fa.1))) => rfl
.comp' refine continuousOn_cfc_setProd hk
    (uniformContinuous_ofFun_toFun_of_mem 𝕜 {t | IsCompact t ∧ t subseteq s} _ ⟨hk, hks⟩ |>.prodMap
      uniformContinuous_id).continuous.continuousOn ?_
  intro (f, a) ⟨⟨hf, ha⟩, ⟨_, ha'⟩⟩
  exact ⟨hf.mono hks, ha.1, subset_of_mem_nhdsSet ha'⟩

/--
theorem `Filter.Tendsto.cfc` / 定理 `Filter.Tendsto.cfc`

English:
theorem Filter.Tendsto.cfc
  statement: {s : Set 𝕜} (hs : IsCompact s) (f : 𝕜 -> 𝕜)
  proof: by
.tendsto.comp .continuousWithinAt ⟨ha₀', ha₀⟩ apply continuousOn_cfc A hs f
  rw [tendsto_nhdsWithin_iff]
  exact ⟨ha_tendsto, ha'.and ha⟩

中文:
定理 滤子.收敛.cfc
  结论: {s : 集合 𝕜} (hs : 是紧集 s) (f : 𝕜 -> 𝕜)
  证明: by
.tendsto.comp .continuousWithinAt ⟨ha₀', ha₀⟩ apply continuousOn_cfc A hs f
  rw [tendsto_nhdsWithin_iff]
  exact ⟨ha_tendsto, ha'.and ha⟩
-/
protected theorem Filter.Tendsto.cfc {s : Set 𝕜} (hs : IsCompact s) (f : 𝕜 -> 𝕜)
    {a : X -> A} {a₀ : A} {l : Filter X} (ha_tendsto : Tendsto a l (𝓝 a₀))
    (ha : forallᶠ x in l, spectrum 𝕜 (a x) subseteq s) (ha' : forallᶠ x in l, p (a x))
    (ha₀ : spectrum 𝕜 a₀ subseteq s) (ha₀' : p a₀) (hf : ContinuousOn f s := by cfc_cont_tac) :
    Tendsto (fun x => cfc f (a x)) l (𝓝 (cfc f a₀)) := by
.tendsto.comp .continuousWithinAt ⟨ha₀', ha₀⟩ apply continuousOn_cfc A hs f
  rw [tendsto_nhdsWithin_iff]
  exact ⟨ha_tendsto, ha'.and ha⟩

/--
theorem `ContinuousAt.cfc` / 定理 `ContinuousAt.cfc`

English:
theorem ContinuousAt.cfc
  statement: [TopologicalSpace X] {s : Set 𝕜} (hs : IsCompact s) (f : 𝕜 -> 𝕜)
  proof: ha_cont.tendsto.cfc hs f ha ha' ha.self_of_nhds ha'.self_of_nhds

中文:
定理 ContinuousAt.cfc
  结论: [拓扑空间 X] {s : 集合 𝕜} (hs : 是紧集 s) (f : 𝕜 -> 𝕜)
  证明: ha_cont.tendsto.cfc hs f ha ha' ha.self_of_nhds ha'.self_of_nhds
-/
protected theorem ContinuousAt.cfc [TopologicalSpace X] {s : Set 𝕜} (hs : IsCompact s) (f : 𝕜 -> 𝕜)
    {a : X -> A} {x₀ : X} (ha_cont : ContinuousAt a x₀)
    (ha : forallᶠ x in 𝓝 x₀, spectrum 𝕜 (a x) subseteq s) (ha' : forallᶠ x in 𝓝 x₀, p (a x))
    (hf : ContinuousOn f s := by cfc_cont_tac) :
    ContinuousAt (fun x => cfc f (a x)) x₀ :=
  ha_cont.tendsto.cfc hs f ha ha' ha.self_of_nhds ha'.self_of_nhds

/--
theorem `ContinuousWithinAt.cfc` / 定理 `ContinuousWithinAt.cfc`

English:
theorem ContinuousWithinAt.cfc
  statement: [TopologicalSpace X] {s : Set 𝕜} (hs : IsCompact s)
  proof: ha_cont.tendsto.cfc hs f ha ha' (ha.self_of_nhdsWithin hx₀) (ha'.self_of_nhdsWithin hx₀)

中文:
定理 ContinuousWithinAt.cfc
  结论: [拓扑空间 X] {s : 集合 𝕜} (hs : 是紧集 s)
  证明: ha_cont.tendsto.cfc hs f ha ha' (ha.self_of_nhdsWithin hx₀) (ha'.self_of_nhdsWithin hx₀)
-/
protected theorem ContinuousWithinAt.cfc [TopologicalSpace X] {s : Set 𝕜} (hs : IsCompact s)
    (f : 𝕜 -> 𝕜) {a : X -> A} {x₀ : X} {t : Set X} (hx₀ : x₀ in t)
    (ha_cont : ContinuousWithinAt a t x₀) (ha : forallᶠ x in 𝓝[t] x₀, spectrum 𝕜 (a x) subseteq s)
    (ha' : forallᶠ x in 𝓝[t] x₀, p (a x)) (hf : ContinuousOn f s := by cfc_cont_tac) :
    ContinuousWithinAt (fun x => cfc f (a x)) t x₀ :=
  ha_cont.tendsto.cfc hs f ha ha' (ha.self_of_nhdsWithin hx₀) (ha'.self_of_nhdsWithin hx₀)

/--
theorem `ContinuousOn.cfc` / 定理 `ContinuousOn.cfc`

English:
theorem ContinuousOn.cfc
  statement: [TopologicalSpace X] {s : X -> Set 𝕜} (f : 𝕜 -> 𝕜) {a : X -> A}
  proof: by
  rw [ContinuousOn] at ha_cont ⊢
  refine fun x hx => (ha_cont x hx).cfc (hs x hx) f hx ?_ ?_ (hf x hx)
  all_goals filter_upwards [ha x hx, self_mem_nhdsWithin] with x hx hxt
  exacts [hx, ha' x hxt]

中文:
定理 ContinuousOn.cfc
  结论: [拓扑空间 X] {s : X -> 集合 𝕜} (f : 𝕜 -> 𝕜) {a : X -> A}
  证明: by
  rw [ContinuousOn] at ha_cont ⊢
  refine fun x hx => (ha_cont x hx).cfc (hs x hx) f hx ?_ ?_ (hf x hx)
  all_goals filter_upwards [ha x hx, self_mem_nhdsWithin] with x hx hxt
  exacts [hx, ha' x hxt]
-/
protected theorem ContinuousOn.cfc [TopologicalSpace X] {s : X -> Set 𝕜} (f : 𝕜 -> 𝕜) {a : X -> A}
    {t : Set X} (hs : forall x in t, IsCompact (s x)) (ha_cont : ContinuousOn a t)
    (ha : forall x₀ in t, forallᶠ x in 𝓝[t] x₀, spectrum 𝕜 (a x) subseteq s x₀) (ha' : forall x in t, p (a x))
    (hf : forall x in t, ContinuousOn f (s x) := by cfc_cont_tac) :
    ContinuousOn (fun x => cfc f (a x)) t := by
  rw [ContinuousOn] at ha_cont ⊢
  refine fun x hx => (ha_cont x hx).cfc (hs x hx) f hx ?_ ?_ (hf x hx)
  all_goals filter_upwards [ha x hx, self_mem_nhdsWithin] with x hx hxt
  exacts [hx, ha' x hxt]

/--
theorem `ContinuousOn.cfc'` / 定理 `ContinuousOn.cfc'`

English:
theorem ContinuousOn.cfc'
  statement: [TopologicalSpace X] {s : Set 𝕜} (hs : IsCompact s)
  proof: by
  refine ContinuousOn.cfc _ (fun _ _ => hs) ha_cont (fun _ _ => ?_) ha'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact ha x hx

中文:
定理 ContinuousOn.cfc'
  结论: [拓扑空间 X] {s : 集合 𝕜} (hs : 是紧集 s)
  证明: by
  refine ContinuousOn.cfc _ (fun _ _ => hs) ha_cont (fun _ _ => ?_) ha'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact ha x hx

Depends on / 依赖: ContinuousOn, ContinuousOn.cfc, cfc_cont_tac, filter_upwards, ha_cont, self_mem_nhdsWithin
-/
theorem ContinuousOn.cfc' [TopologicalSpace X] {s : Set 𝕜} (hs : IsCompact s)
    (f : 𝕜 -> 𝕜) {a : X -> A} {t : Set X} (ha_cont : ContinuousOn a t)
    (ha : forall x in t, spectrum 𝕜 (a x) subseteq s) (ha' : forall x in t, p (a x))
    (hf : ContinuousOn f s := by cfc_cont_tac) :
    ContinuousOn (fun x => cfc f (a x)) t := by
  refine ContinuousOn.cfc _ (fun _ _ => hs) ha_cont (fun _ _ => ?_) ha'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact ha x hx

/--
theorem `ContinuousOn.cfc_of_mem_nhdsSet` / 定理 `ContinuousOn.cfc_of_mem_nhdsSet`

English:
theorem ContinuousOn.cfc_of_mem_nhdsSet
  statement: [CompleteSpace A] [TopologicalSpace X] {s : Set 𝕜}
  proof: by
  have hs' := hs
  simp only [nhdsSet_iUnion, mem_iSup] at hs'
  have (x : t) : exists S, IsCompact S ∧ (forallᶠ (x' : A) in 𝓝 (a x), spectrum 𝕜 x' subseteq S) ∧ S subseteq s := by
    obtain ⟨S, ⟨hS₁, hS₂⟩, hS₃⟩ :=
.nhdsSet_basis_isCompact.mem_iff.mp (hs' x x.2) spectrum.isCompact (𝕜 := 𝕜) (a x)

中文:
定理 ContinuousOn.cfc_of_mem_nhdsSet
  结论: [完备空间 A] [拓扑空间 X] {s : 集合 𝕜}
  证明: by
  have hs' := hs
  simp only [nhdsSet_iUnion, mem_iSup] at hs'
  have (x : t) : exists S, IsCompact S ∧ (forallᶠ (x' : A) in 𝓝 (a x), spectrum 𝕜 x' subseteq S) ∧ S subseteq s := by
    obtain ⟨S, ⟨hS₁, hS₂⟩, hS₃⟩ :=
.nhdsSet_basis_isCompact.mem_iff.mp (hs' x x.2) spectrum.isCompact (𝕜 := 𝕜) (a x)

Depends on / 依赖: ContinuousOn, IsCompact, cfc_cont_tac, cfc_tac, isCompact, mem_iSup, mem_iff, nhdsSet_basis_isCompact, nhdsSet_basis_isCompact.mem_iff.mp, nhdsSet_iUnion, spectrum, spectrum.isCompact, subseteq, upperHemicontinuousAt, upperHemicontinuous_spectrum
-/
theorem ContinuousOn.cfc_of_mem_nhdsSet [CompleteSpace A] [TopologicalSpace X] {s : Set 𝕜}
    (f : 𝕜 -> 𝕜) {a : X -> A} {t : Set X} (hs : s in 𝓝ˢ (⋃ x in t, spectrum 𝕜 (a x)))
    (ha_cont : ContinuousOn a t) (ha' : forall x in t, p (a x) := by cfc_tac)
    (hf : ContinuousOn f s := by cfc_cont_tac) :
    ContinuousOn (fun x => cfc f (a x)) t := by
  have hs' := hs
  simp only [nhdsSet_iUnion, mem_iSup] at hs'
  have (x : t) : exists S, IsCompact S ∧ (forallᶠ (x' : A) in 𝓝 (a x), spectrum 𝕜 x' subseteq S) ∧ S subseteq s := by
    obtain ⟨S, ⟨hS₁, hS₂⟩, hS₃⟩ :=
.nhdsSet_basis_isCompact.mem_iff.mp (hs' x x.2) spectrum.isCompact (𝕜 := 𝕜) (a x)
    refine ⟨S, hS₂, ?_, hS₃⟩
.mono .upperHemicontinuousAt (a x) _ hS₁ exact upperHemicontinuous_spectrum 𝕜 A
      fun _ => subset_of_mem_nhdsSet
  choose S hS₁ hS₂ hS₃ using this
  classical
  refine ha_cont.cfc (s := fun x : X => if hx : x in t then S ⟨x, hx⟩ else ∅) f
    (by simpa +contextual using hS₁) ?_ ha' ?_
  all_goals simp +contextual only [↓reduceDIte]
.eventually hS₂ ⟨x₀, hx₀⟩ · exact fun x₀ hx₀ => ha_cont.continuousWithinAt hx₀
· exact fun x hx => hf.mono hS₃ ⟨x, hx⟩

/--
theorem `Continuous.cfc` / 定理 `Continuous.cfc`

English:
theorem Continuous.cfc
  statement: [TopologicalSpace X] {s : X -> Set 𝕜} (f : 𝕜 -> 𝕜) {a : X -> A}
  proof: by
  rw [← continuousOn_univ] at ha_cont ⊢
  exact ha_cont.cfc f (fun x _ => hs x) (fun x _ => by simpa using ha x) (fun x _ => ha' x)

中文:
定理 连续.cfc
  结论: [拓扑空间 X] {s : X -> 集合 𝕜} (f : 𝕜 -> 𝕜) {a : X -> A}
  证明: by
  rw [← continuousOn_univ] at ha_cont ⊢
  exact ha_cont.cfc f (fun x _ => hs x) (fun x _ => by simpa using ha x) (fun x _ => ha' x)
-/
protected theorem Continuous.cfc [TopologicalSpace X] {s : X -> Set 𝕜} (f : 𝕜 -> 𝕜) {a : X -> A}
    (ha_cont : Continuous a) (hs : forall x, IsCompact (s x))
    (ha : forall x₀, forallᶠ x in 𝓝 x₀, spectrum 𝕜 (a x) subseteq s x₀)
    (hf : forall x, ContinuousOn f (s x) := by cfc_cont_tac) (ha' : forall x, p (a x) := by cfc_tac) :
    Continuous (fun x => cfc f (a x)) := by
  rw [← continuousOn_univ] at ha_cont ⊢
  exact ha_cont.cfc f (fun x _ => hs x) (fun x _ => by simpa using ha x) (fun x _ => ha' x)

/--
theorem `Continuous.cfc'` / 定理 `Continuous.cfc'`

English:
theorem Continuous.cfc'
  statement: [TopologicalSpace X] {s : Set 𝕜} (hs : IsCompact s) (f : 𝕜 -> 𝕜)
  proof: by
  rw [← continuousOn_univ] at ha_cont ⊢
  exact ha_cont.cfc' hs f (fun x _ => ha x) (fun x _ => ha' x)

中文:
定理 连续.cfc'
  结论: [拓扑空间 X] {s : 集合 𝕜} (hs : 是紧集 s) (f : 𝕜 -> 𝕜)
  证明: by
  rw [← continuousOn_univ] at ha_cont ⊢
  exact ha_cont.cfc' hs f (fun x _ => ha x) (fun x _ => ha' x)

Depends on / 依赖: Continuous, cfc_cont_tac, cfc_tac, continuousOn_univ, ha_cont, ha_cont.cfc
-/
theorem Continuous.cfc' [TopologicalSpace X] {s : Set 𝕜} (hs : IsCompact s) (f : 𝕜 -> 𝕜)
    {a : X -> A} (ha_cont : Continuous a) (ha : forall x, spectrum 𝕜 (a x) subseteq s)
    (hf : ContinuousOn f s := by cfc_cont_tac) (ha' : forall x, p (a x) := by cfc_tac) :
    Continuous (fun x => cfc f (a x)) := by
  rw [← continuousOn_univ] at ha_cont ⊢
  exact ha_cont.cfc' hs f (fun x _ => ha x) (fun x _ => ha' x)

/--
theorem `Continuous.cfc_of_mem_nhdsSet` / 定理 `Continuous.cfc_of_mem_nhdsSet`

English:
theorem Continuous.cfc_of_mem_nhdsSet
  statement: [CompleteSpace A] [TopologicalSpace X] {s : Set 𝕜}
  proof: by
  rw [← continuousOn_univ] at ha_cont ⊢
  exact ha_cont.cfc_of_mem_nhdsSet f (by simpa) (by simpa)

中文:
定理 连续.cfc_of_mem_nhdsSet
  结论: [完备空间 A] [拓扑空间 X] {s : 集合 𝕜}
  证明: by
  rw [← continuousOn_univ] at ha_cont ⊢
  exact ha_cont.cfc_of_mem_nhdsSet f (by simpa) (by simpa)

Depends on / 依赖: Continuous, ContinuousOn, cfc_cont_tac, cfc_of_mem_nhdsSet, cfc_tac, continuousOn_univ, ha_cont, ha_cont.cfc_of_mem_nhdsSet
-/
theorem Continuous.cfc_of_mem_nhdsSet [CompleteSpace A] [TopologicalSpace X] {s : Set 𝕜}
    (f : 𝕜 -> 𝕜) {a : X -> A} (hs : s in 𝓝ˢ (⋃ x, spectrum 𝕜 (a x))) (ha_cont : Continuous a)
    (ha' : forall x, p (a x) := by cfc_tac) (hf : ContinuousOn f s := by cfc_cont_tac) :
    Continuous (fun x => cfc f (a x)) := by
  rw [← continuousOn_univ] at ha_cont ⊢
  exact ha_cont.cfc_of_mem_nhdsSet f (by simpa) (by simpa)

end RCLike

section NNReal

variable {X A : Type*} [NormedRing A] [StarRing A]
    [NormedAlgebra Real A] [IsometricContinuousFunctionalCalculus Real A IsSelfAdjoint]
    [ContinuousStar A] [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass Real A]
    [T2Space A] [IsSemitopologicalRing A]

variable (A) in
/--
theorem `continuousOn_cfc_nnreal` / 定理 `continuousOn_cfc_nnreal`

English:
theorem continuousOn_cfc_nnreal
  statement: {s : Set Real>=0} (hs : IsCompact s)
  proof: by
  have : {a : A | 0 <= a ∧ spectrum Real>=0 a subseteq s}.EqOn (cfc f) (cfc (fun x : Real => f x.toNNReal)) :=
    fun a ha => cfc_nnreal_eq_real _ _ ha.1
  refine ContinuousOn.congr ?_ this
  replace hf : ContinuousOn (fun x => f x.toNNReal : Real -> Real) (NNReal.toReal '' s) := by
    apply hf

中文:
定理 continuousOn_cfc_nnreal
  结论: {s : 集合 实数>=0} (hs : 是紧集 s)
  证明: by
  have : {a : A | 0 <= a ∧ spectrum Real>=0 a subseteq s}.EqOn (cfc f) (cfc (fun x : Real => f x.toNNReal)) :=
    fun a ha => cfc_nnreal_eq_real _ _ ha.1
  refine ContinuousOn.congr ?_ this
  replace hf : ContinuousOn (fun x => f x.toNNReal : Real -> Real) (NNReal.toReal '' s) := by
    apply hf

Depends on / 依赖: ContinuousOn, ContinuousOn.congr, NNReal, NNReal.toReal, Set.mapsTo_image_iff, cfc_cont_tac, cfc_nnreal_eq_real, continuousOn_cfc, hf.ofReal_map_toNNReal, hs.image, mapsTo_image_iff, ofReal_map_toNNReal, replace, spectrum, subseteq, toNNReal, toReal, x.toNNReal
-/
theorem continuousOn_cfc_nnreal {s : Set Real>=0} (hs : IsCompact s)
    (f : Real>=0 -> Real>=0) (hf : ContinuousOn f s := by cfc_cont_tac) :
    ContinuousOn (cfc f) {a : A | 0 <= a ∧ spectrum Real>=0 a subseteq s} := by
  have : {a : A | 0 <= a ∧ spectrum Real>=0 a subseteq s}.EqOn (cfc f) (cfc (fun x : Real => f x.toNNReal)) :=
    fun a ha => cfc_nnreal_eq_real _ _ ha.1
  refine ContinuousOn.congr ?_ this
  replace hf : ContinuousOn (fun x => f x.toNNReal : Real -> Real) (NNReal.toReal '' s) := by
    apply hf.ofReal_map_toNNReal
    rw [Set.mapsTo_image_iff]
    intro x hx
    simpa
.mono fun a ha => ?_ refine continuousOn_cfc A (hs.image NNReal.continuous_coe) _ hf
  simp only [Set.mem_ofPred_eq, nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts] at ha ⊢
  rw [← SpectrumRestricts] at ha
  refine ⟨ha.1.1, ?_⟩
  rw [← ha.1.2.algebraMap_image]
  exact Set.image_mono ha.2

open UniformOnFun in
/--
theorem `continuousOn_cfc_nnreal_setProd` / 定理 `continuousOn_cfc_nnreal_setProd`

English:
theorem continuousOn_cfc_nnreal_setProd
  given: {s : Set Real>=0} (hs : IsCompact s)
  proof: continuousOn_prod_of_continuousOn_lipschitzOnWith _ 1
    (fun f hf => continuousOn_cfc_nnreal A hs ((toFun {s}) f) hf)
    (fun a ⟨_, ha'⟩ => lipschitzOnWith_cfc_fun_of_subset a ha')

中文:
定理 continuousOn_cfc_nnreal_setProd
  条件: {s : 集合 实数>=0} (hs : 是紧集 s)
  证明: continuousOn_prod_of_continuousOn_lipschitzOnWith _ 1
    (fun f hf => continuousOn_cfc_nnreal A hs ((toFun {s}) f) hf)
    (fun a ⟨_, ha'⟩ => lipschitzOnWith_cfc_fun_of_subset a ha')

Depends on / 依赖: continuousOn_cfc_nnreal, continuousOn_prod_of_continuousOn_lipschitzOnWith, lipschitzOnWith_cfc_fun_of_subset
-/
theorem continuousOn_cfc_nnreal_setProd {s : Set Real>=0} (hs : IsCompact s) :
    ContinuousOn (fun fa : (Real>=0 ->ᵤ[{s}] Real>=0) × A => cfc (toFun {s} fa.1) fa.2)
      ({f | ContinuousOn (toFun {s} f) s} ×ˢ {a | 0 <= a ∧ spectrum Real>=0 a subseteq s}) :=
  continuousOn_prod_of_continuousOn_lipschitzOnWith _ 1
    (fun f hf => continuousOn_cfc_nnreal A hs ((toFun {s}) f) hf)
    (fun a ⟨_, ha'⟩ => lipschitzOnWith_cfc_fun_of_subset a ha')

open UniformOnFun in
/--
theorem `continuousOn_cfc_nnreal_setProd_nhdsSet` / 定理 `continuousOn_cfc_nnreal_setProd_nhdsSet`

English:
theorem continuousOn_cfc_nnreal_setProd_nhdsSet
  given: [CompleteSpace A] {s : Set Real>=0}
  proof: by
  refine continuousOn_of_locally_continuousOn fun (f, a) ⟨hf, ha, has⟩ => ?_
  have hs := ContinuousFunctionalCalculus.isCompact_spectrum (R := Real>=0) a
  obtain ⟨k, ⟨hka, hk⟩, hks⟩ := hs.nhdsSet_basis_isCompact.mem_iff.mp has
  have := (upperHemicontinuous_spectrum_nnreal A).isOpen k
  refine 

中文:
定理 continuousOn_cfc_nnreal_setProd_nhdsSet
  条件: [完备空间 A] {s : 集合 实数>=0}
  证明: by
  refine continuousOn_of_locally_continuousOn fun (f, a) ⟨hf, ha, has⟩ => ?_
  have hs := ContinuousFunctionalCalculus.isCompact_spectrum (R := Real>=0) a
  obtain ⟨k, ⟨hka, hk⟩, hks⟩ := hs.nhdsSet_basis_isCompact.mem_iff.mp has
  have := (upperHemicontinuous_spectrum_nnreal A).isOpen k
  refine 

Depends on / 依赖: ContinuousFunctionalCalculus, ContinuousFunctionalCalculus.isCompact_spectrum, IsCompact, Set.univ, continuousOn_of_locally_continuousOn, equals, hs.nhdsSet_basis_isCompact.mem_iff.mp, isCompact_spectrum, isOpen, isOpen_univ, isOpen_univ.prod, mem_iff, nhdsSet_basis_isCompact, spectrum, subseteq, upperHemicontinuous_spectrum_nnreal
-/
theorem continuousOn_cfc_nnreal_setProd_nhdsSet [CompleteSpace A] {s : Set Real>=0} :
    ContinuousOn (fun fa : (Real>=0 ->ᵤ[{t | IsCompact t ∧ t subseteq s}] Real>=0) × A => cfc (toFun {s} fa.1) fa.2)
      ({f | ContinuousOn (toFun {t | IsCompact t ∧ t subseteq s} f) s} ×ˢ
        {a | 0 <= a ∧ s in 𝓝ˢ (spectrum Real>=0 a)}) := by
  refine continuousOn_of_locally_continuousOn fun (f, a) ⟨hf, ha, has⟩ => ?_
  have hs := ContinuousFunctionalCalculus.isCompact_spectrum (R := Real>=0) a
  obtain ⟨k, ⟨hka, hk⟩, hks⟩ := hs.nhdsSet_basis_isCompact.mem_iff.mp has
  have := (upperHemicontinuous_spectrum_nnreal A).isOpen k
  refine ⟨Set.univ ×ˢ {x | k in 𝓝ˢ (spectrum Real>=0 x)}, isOpen_univ.prod this, by simpa, ?_⟩
  conv in cfc _ => equals cfc (toFun {k} (ofFun {k} (toFun {t | IsCompact t ∧ t subseteq s} fa.1))) => rfl
.comp' refine continuousOn_cfc_nnreal_setProd hk
    (uniformContinuous_ofFun_toFun_of_mem _ {t | IsCompact t ∧ t subseteq s} _ ⟨hk, hks⟩ |>.prodMap
      uniformContinuous_id).continuous.continuousOn ?_
  intro (f, a) ⟨⟨hf, ha⟩, ⟨_, ha'⟩⟩
  exact ⟨hf.mono hks, ha.1, subset_of_mem_nhdsSet ha'⟩

/--
theorem `Filter.Tendsto.cfc_nnreal` / 定理 `Filter.Tendsto.cfc_nnreal`

English:
theorem Filter.Tendsto.cfc_nnreal
  statement: {s : Set Real>=0} (hs : IsCompact s)
  proof: by
.tendsto.comp .continuousWithinAt ⟨ha₀', ha₀⟩ apply continuousOn_cfc_nnreal A hs f
  rw [tendsto_nhdsWithin_iff]
  exact ⟨ha_tendsto, ha'.and ha⟩

中文:
定理 滤子.收敛.cfc_nnreal
  结论: {s : 集合 实数>=0} (hs : 是紧集 s)
  证明: by
.tendsto.comp .continuousWithinAt ⟨ha₀', ha₀⟩ apply continuousOn_cfc_nnreal A hs f
  rw [tendsto_nhdsWithin_iff]
  exact ⟨ha_tendsto, ha'.and ha⟩

Depends on / 依赖: Tendsto, cfc_cont_tac, continuousOn_cfc_nnreal, continuousWithinAt, ha_tendsto, tendsto, tendsto.comp, tendsto_nhdsWithin_iff
-/
theorem Filter.Tendsto.cfc_nnreal {s : Set Real>=0} (hs : IsCompact s)
    (f : Real>=0 -> Real>=0) {a : X -> A} {a₀ : A} {l : Filter X} (ha_tendsto : Tendsto a l (𝓝 a₀))
    (ha : forallᶠ x in l, spectrum Real>=0 (a x) subseteq s) (ha' : forallᶠ x in l, 0 <= a x)
    (ha₀ : spectrum Real>=0 a₀ subseteq s) (ha₀' : 0 <= a₀) (hf : ContinuousOn f s := by cfc_cont_tac) :
    Tendsto (fun x => cfc f (a x)) l (𝓝 (cfc f a₀)) := by
.tendsto.comp .continuousWithinAt ⟨ha₀', ha₀⟩ apply continuousOn_cfc_nnreal A hs f
  rw [tendsto_nhdsWithin_iff]
  exact ⟨ha_tendsto, ha'.and ha⟩

/--
theorem `ContinuousAt.cfc_nnreal` / 定理 `ContinuousAt.cfc_nnreal`

English:
theorem ContinuousAt.cfc_nnreal
  statement: [TopologicalSpace X] {s : Set Real>=0} (hs : IsCompact s)
  proof: ha_cont.tendsto.cfc_nnreal hs f ha ha' ha.self_of_nhds ha'.self_of_nhds

中文:
定理 ContinuousAt.cfc_nnreal
  结论: [拓扑空间 X] {s : 集合 实数>=0} (hs : 是紧集 s)
  证明: ha_cont.tendsto.cfc_nnreal hs f ha ha' ha.self_of_nhds ha'.self_of_nhds

Depends on / 依赖: ContinuousAt, cfc_cont_tac, cfc_nnreal, ha.self_of_nhds, ha_cont, ha_cont.tendsto.cfc_nnreal, self_of_nhds, tendsto
-/
theorem ContinuousAt.cfc_nnreal [TopologicalSpace X] {s : Set Real>=0} (hs : IsCompact s)
    (f : Real>=0 -> Real>=0) {a : X -> A} {x₀ : X} (ha_cont : ContinuousAt a x₀)
    (ha : forallᶠ x in 𝓝 x₀, spectrum Real>=0 (a x) subseteq s) (ha' : forallᶠ x in 𝓝 x₀, 0 <= a x)
    (hf : ContinuousOn f s := by cfc_cont_tac) :
    ContinuousAt (fun x => cfc f (a x)) x₀ :=
  ha_cont.tendsto.cfc_nnreal hs f ha ha' ha.self_of_nhds ha'.self_of_nhds

/--
theorem `ContinuousWithinAt.cfc_nnreal` / 定理 `ContinuousWithinAt.cfc_nnreal`

English:
theorem ContinuousWithinAt.cfc_nnreal
  statement: [TopologicalSpace X] {s : Set Real>=0} (hs : IsCompact s)
  proof: ha_cont.tendsto.cfc_nnreal hs f ha ha' (ha.self_of_nhdsWithin hx₀) (ha'.self_of_nhdsWithin hx₀)

中文:
定理 ContinuousWithinAt.cfc_nnreal
  结论: [拓扑空间 X] {s : 集合 实数>=0} (hs : 是紧集 s)
  证明: ha_cont.tendsto.cfc_nnreal hs f ha ha' (ha.self_of_nhdsWithin hx₀) (ha'.self_of_nhdsWithin hx₀)

Depends on / 依赖: ContinuousWithinAt, cfc_cont_tac, cfc_nnreal, ha.self_of_nhdsWithin, ha_cont, ha_cont.tendsto.cfc_nnreal, self_of_nhdsWithin, tendsto
-/
theorem ContinuousWithinAt.cfc_nnreal [TopologicalSpace X] {s : Set Real>=0} (hs : IsCompact s)
    (f : Real>=0 -> Real>=0) {a : X -> A} {x₀ : X} {t : Set X} (hx₀ : x₀ in t)
    (ha_cont : ContinuousWithinAt a t x₀) (ha : forallᶠ x in 𝓝[t] x₀, spectrum Real>=0 (a x) subseteq s)
    (ha' : forallᶠ x in 𝓝[t] x₀, 0 <= a x) (hf : ContinuousOn f s := by cfc_cont_tac) :
    ContinuousWithinAt (fun x => cfc f (a x)) t x₀ :=
  ha_cont.tendsto.cfc_nnreal hs f ha ha' (ha.self_of_nhdsWithin hx₀) (ha'.self_of_nhdsWithin hx₀)

/--
theorem `ContinuousOn.cfc_nnreal` / 定理 `ContinuousOn.cfc_nnreal`

English:
theorem ContinuousOn.cfc_nnreal
  statement: [TopologicalSpace X] {s : X -> Set Real>=0} (f : Real>=0 -> Real>=0) {a : X -> A}
  proof: by
  rw [ContinuousOn] at ha_cont ⊢
  refine fun x hx => (ha_cont x hx).cfc_nnreal (hs x hx) f hx ?_ ?_ (hf x hx)
  all_goals filter_upwards [ha x hx, self_mem_nhdsWithin] with x hx hxt
  exacts [hx, ha' x hxt]

中文:
定理 ContinuousOn.cfc_nnreal
  结论: [拓扑空间 X] {s : X -> 集合 实数>=0} (f : 实数>=0 -> 实数>=0) {a : X -> A}
  证明: by
  rw [ContinuousOn] at ha_cont ⊢
  refine fun x hx => (ha_cont x hx).cfc_nnreal (hs x hx) f hx ?_ ?_ (hf x hx)
  all_goals filter_upwards [ha x hx, self_mem_nhdsWithin] with x hx hxt
  exacts [hx, ha' x hxt]

Depends on / 依赖: ContinuousOn, all_goals, cfc_cont_tac, cfc_nnreal, exacts, filter_upwards, ha_cont, self_mem_nhdsWithin
-/
theorem ContinuousOn.cfc_nnreal [TopologicalSpace X] {s : X -> Set Real>=0} (f : Real>=0 -> Real>=0) {a : X -> A}
    {t : Set X} (hs : forall x in t, IsCompact (s x)) (ha_cont : ContinuousOn a t)
    (ha : forall x₀ in t, forallᶠ x in 𝓝[t] x₀, spectrum Real>=0 (a x) subseteq s x₀) (ha' : forall x in t, 0 <= a x)
    (hf : forall x in t, ContinuousOn f (s x) := by cfc_cont_tac) :
    ContinuousOn (fun x => cfc f (a x)) t := by
  rw [ContinuousOn] at ha_cont ⊢
  refine fun x hx => (ha_cont x hx).cfc_nnreal (hs x hx) f hx ?_ ?_ (hf x hx)
  all_goals filter_upwards [ha x hx, self_mem_nhdsWithin] with x hx hxt
  exacts [hx, ha' x hxt]

/--
theorem `ContinuousOn.cfc_nnreal'` / 定理 `ContinuousOn.cfc_nnreal'`

English:
theorem ContinuousOn.cfc_nnreal'
  statement: [TopologicalSpace X] {s : Set Real>=0} (hs : IsCompact s)
  proof: by
  refine ContinuousOn.cfc_nnreal _ (fun _ _ => hs) ha_cont (fun _ _ => ?_) ha'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact ha x hx

中文:
定理 ContinuousOn.cfc_nnreal'
  结论: [拓扑空间 X] {s : 集合 实数>=0} (hs : 是紧集 s)
  证明: by
  refine ContinuousOn.cfc_nnreal _ (fun _ _ => hs) ha_cont (fun _ _ => ?_) ha'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact ha x hx

Depends on / 依赖: ContinuousOn, ContinuousOn.cfc_nnreal, cfc_cont_tac, cfc_nnreal, filter_upwards, ha_cont, self_mem_nhdsWithin
-/
theorem ContinuousOn.cfc_nnreal' [TopologicalSpace X] {s : Set Real>=0} (hs : IsCompact s)
    (f : Real>=0 -> Real>=0) {a : X -> A} {t : Set X} (ha_cont : ContinuousOn a t)
    (ha : forall x in t, spectrum Real>=0 (a x) subseteq s) (ha' : forall x in t, 0 <= a x)
    (hf : ContinuousOn f s := by cfc_cont_tac) :
    ContinuousOn (fun x => cfc f (a x)) t := by
  refine ContinuousOn.cfc_nnreal _ (fun _ _ => hs) ha_cont (fun _ _ => ?_) ha'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact ha x hx

/--
theorem `ContinuousOn.cfc_nnreal_of_mem_nhdsSet` / 定理 `ContinuousOn.cfc_nnreal_of_mem_nhdsSet`

English:
theorem ContinuousOn.cfc_nnreal_of_mem_nhdsSet
  statement: [CompleteSpace A] [TopologicalSpace X] {s : Set Real>=0}
  proof: by
  have hs' := hs
  simp only [nhdsSet_iUnion, mem_iSup] at hs'
  have (x : t) : exists S, IsCompact S ∧ (forallᶠ (x' : A) in 𝓝 (a x), spectrum Real>=0 x' subseteq S) ∧ S subseteq s := by
    obtain ⟨S, ⟨hS₁, hS₂⟩, hS₃⟩ :=
.nhdsSet_basis_isCompact.mem_iff.mp (hs' x x.2) spectrum.isCompact_nnreal (

中文:
定理 ContinuousOn.cfc_nnreal_of_mem_nhdsSet
  结论: [完备空间 A] [拓扑空间 X] {s : 集合 实数>=0}
  证明: by
  have hs' := hs
  simp only [nhdsSet_iUnion, mem_iSup] at hs'
  have (x : t) : exists S, IsCompact S ∧ (forallᶠ (x' : A) in 𝓝 (a x), spectrum Real>=0 x' subseteq S) ∧ S subseteq s := by
    obtain ⟨S, ⟨hS₁, hS₂⟩, hS₃⟩ :=
.nhdsSet_basis_isCompact.mem_iff.mp (hs' x x.2) spectrum.isCompact_nnreal (

Depends on / 依赖: ContinuousOn, IsCompact, cfc_cont_tac, cfc_tac, isCompact_nnreal, mem_iSup, mem_iff, nhdsSet_basis_isCompact, nhdsSet_basis_isCompact.mem_iff.mp, nhdsSet_iUnion, spectrum, spectrum.isCompact_nnreal, subseteq, upperHemicontinuousAt, upperHemicontinuous_spectrum_nnreal
-/
theorem ContinuousOn.cfc_nnreal_of_mem_nhdsSet [CompleteSpace A] [TopologicalSpace X] {s : Set Real>=0}
    (f : Real>=0 -> Real>=0) {a : X -> A} {t : Set X} (hs : s in 𝓝ˢ (⋃ x in t, spectrum Real>=0 (a x)))
    (ha_cont : ContinuousOn a t) (ha' : forall x in t, 0 <= a x := by cfc_tac)
    (hf : ContinuousOn f s := by cfc_cont_tac) :
    ContinuousOn (fun x => cfc f (a x)) t := by
  have hs' := hs
  simp only [nhdsSet_iUnion, mem_iSup] at hs'
  have (x : t) : exists S, IsCompact S ∧ (forallᶠ (x' : A) in 𝓝 (a x), spectrum Real>=0 x' subseteq S) ∧ S subseteq s := by
    obtain ⟨S, ⟨hS₁, hS₂⟩, hS₃⟩ :=
.nhdsSet_basis_isCompact.mem_iff.mp (hs' x x.2) spectrum.isCompact_nnreal (a x)
    refine ⟨S, hS₂, ?_, hS₃⟩
.mono .upperHemicontinuousAt (a x) _ hS₁ exact upperHemicontinuous_spectrum_nnreal A
      fun _ => subset_of_mem_nhdsSet
  choose S hS₁ hS₂ hS₃ using this
  classical
  refine ha_cont.cfc_nnreal (s := fun x : X => if hx : x in t then S ⟨x, hx⟩ else ∅) f
    (by simpa +contextual using hS₁) ?_ ha' ?_
  all_goals simp +contextual only [↓reduceDIte]
.eventually hS₂ ⟨x₀, hx₀⟩ · exact fun x₀ hx₀ => ha_cont.continuousWithinAt hx₀
· exact fun x hx => hf.mono hS₃ ⟨x, hx⟩

/--
theorem `Continuous.cfc_nnreal` / 定理 `Continuous.cfc_nnreal`

English:
theorem Continuous.cfc_nnreal
  statement: [TopologicalSpace X] {s : X -> Set Real>=0} (f : Real>=0 -> Real>=0) {a : X -> A}
  proof: by
  rw [← continuousOn_univ] at ha_cont ⊢
  exact ha_cont.cfc_nnreal f (fun x _ => hs x) (fun x _ => by simpa using ha x) (fun x _ => ha' x)

中文:
定理 连续.cfc_nnreal
  结论: [拓扑空间 X] {s : X -> 集合 实数>=0} (f : 实数>=0 -> 实数>=0) {a : X -> A}
  证明: by
  rw [← continuousOn_univ] at ha_cont ⊢
  exact ha_cont.cfc_nnreal f (fun x _ => hs x) (fun x _ => by simpa using ha x) (fun x _ => ha' x)

Depends on / 依赖: Continuous, cfc_cont_tac, cfc_nnreal, cfc_tac, continuousOn_univ, ha_cont, ha_cont.cfc_nnreal
-/
theorem Continuous.cfc_nnreal [TopologicalSpace X] {s : X -> Set Real>=0} (f : Real>=0 -> Real>=0) {a : X -> A}
    (ha_cont : Continuous a) (hs : forall x, IsCompact (s x))
    (ha : forall x₀, forallᶠ x in 𝓝 x₀, spectrum Real>=0 (a x) subseteq s x₀)
    (hf : forall x, ContinuousOn f (s x) := by cfc_cont_tac) (ha' : forall x, 0 <= a x := by cfc_tac) :
    Continuous (fun x => cfc f (a x)) := by
  rw [← continuousOn_univ] at ha_cont ⊢
  exact ha_cont.cfc_nnreal f (fun x _ => hs x) (fun x _ => by simpa using ha x) (fun x _ => ha' x)

/--
theorem `Continuous.cfc_nnreal'` / 定理 `Continuous.cfc_nnreal'`

English:
theorem Continuous.cfc_nnreal'
  statement: [TopologicalSpace X] {s : Set Real>=0} (hs : IsCompact s) (f : Real>=0 -> Real>=0)
  proof: by
  rw [← continuousOn_univ] at ha_cont ⊢
  exact ha_cont.cfc_nnreal' hs f (fun x _ => ha x) (fun x _ => ha' x)

中文:
定理 连续.cfc_nnreal'
  结论: [拓扑空间 X] {s : 集合 实数>=0} (hs : 是紧集 s) (f : 实数>=0 -> 实数>=0)
  证明: by
  rw [← continuousOn_univ] at ha_cont ⊢
  exact ha_cont.cfc_nnreal' hs f (fun x _ => ha x) (fun x _ => ha' x)

Depends on / 依赖: Continuous, cfc_cont_tac, cfc_nnreal, cfc_tac, continuousOn_univ, ha_cont, ha_cont.cfc_nnreal
-/
theorem Continuous.cfc_nnreal' [TopologicalSpace X] {s : Set Real>=0} (hs : IsCompact s) (f : Real>=0 -> Real>=0)
    {a : X -> A} (ha_cont : Continuous a) (ha : forall x, spectrum Real>=0 (a x) subseteq s)
    (hf : ContinuousOn f s := by cfc_cont_tac) (ha' : forall x, 0 <= a x := by cfc_tac) :
    Continuous (fun x => cfc f (a x)) := by
  rw [← continuousOn_univ] at ha_cont ⊢
  exact ha_cont.cfc_nnreal' hs f (fun x _ => ha x) (fun x _ => ha' x)

/--
theorem `Continuous.cfc_nnreal_of_mem_nhdsSet` / 定理 `Continuous.cfc_nnreal_of_mem_nhdsSet`

English:
theorem Continuous.cfc_nnreal_of_mem_nhdsSet
  statement: [CompleteSpace A] [TopologicalSpace X] {s : Set Real>=0}
  proof: by
  rw [← continuousOn_univ] at ha_cont ⊢
  exact ha_cont.cfc_nnreal_of_mem_nhdsSet f (by simpa) (by simpa)

中文:
定理 连续.cfc_nnreal_of_mem_nhdsSet
  结论: [完备空间 A] [拓扑空间 X] {s : 集合 实数>=0}
  证明: by
  rw [← continuousOn_univ] at ha_cont ⊢
  exact ha_cont.cfc_nnreal_of_mem_nhdsSet f (by simpa) (by simpa)

Depends on / 依赖: Continuous, ContinuousOn, cfc_cont_tac, cfc_nnreal_of_mem_nhdsSet, cfc_tac, continuousOn_univ, ha_cont, ha_cont.cfc_nnreal_of_mem_nhdsSet
-/
theorem Continuous.cfc_nnreal_of_mem_nhdsSet [CompleteSpace A] [TopologicalSpace X] {s : Set Real>=0}
    (f : Real>=0 -> Real>=0) {a : X -> A} (hs : s in 𝓝ˢ (⋃ x, spectrum Real>=0 (a x))) (ha_cont : Continuous a)
    (ha' : forall x, 0 <= a x := by cfc_tac) (hf : ContinuousOn f s := by cfc_cont_tac) :
    Continuous (fun x => cfc f (a x)) := by
  rw [← continuousOn_univ] at ha_cont ⊢
  exact ha_cont.cfc_nnreal_of_mem_nhdsSet f (by simpa) (by simpa)

end NNReal

end Right

end Unital

section NonUnital

section Left

section Generic

variable {X R A : Type*} {p : A -> Prop} [CommSemiring R] [StarRing R] [MetricSpace R] [Nontrivial R]
    [IsTopologicalSemiring R] [ContinuousStar R] [NonUnitalRing A] [StarRing A]
    [TopologicalSpace A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
    [NonUnitalContinuousFunctionalCalculus R A p]

/--
theorem `tendsto_cfcₙ_fun` / 定理 `tendsto_cfcₙ_fun`

English:
theorem tendsto_cfcₙ_fun
  statement: {l : Filter X} {F : X -> R -> R} {f : R -> R} {a : A}
  proof: by
  open scoped NonUnitalContinuousFunctionalCalculus in
  obtain (rfl | hl) := l.eq_or_neBot
  · simp
  have hf := h_tendsto.continuousOn hF.frequently
have hf0 : f 0 = 0 := Eq.symm
tendsto_nhds_unique (tendsto_const_nhds.congr' <| .symm hF0)
    h_tendsto.tendsto_at (quasispectrum.zero_mem R a)
 

中文:
定理 tendsto_cfcₙ_fun
  结论: {l : 滤子 X} {F : X -> R -> R} {f : R -> R} {a : A}
  证明: by
  open scoped NonUnitalContinuousFunctionalCalculus in
  obtain (rfl | hl) := l.eq_or_neBot
  · simp
  have hf := h_tendsto.continuousOn hF.frequently
have hf0 : f 0 = 0 := Eq.symm
tendsto_nhds_unique (tendsto_const_nhds.congr' <| .symm hF0)
    h_tendsto.tendsto_at (quasispectrum.zero_mem R a)
 

Depends on / 依赖: ContinuousOn, Eq.symm, NonUnitalContinuousFunctionalCalculus, _iff, continuousOn, eq_or_neBot, frequently, hF.and, hF.frequently, h_tendsto, h_tendsto.continuousOn, h_tendsto.tendsto_at, l.eq_or_neBot, quasispectrum, quasispectrum.zero_mem, scoped, tendsto_at, tendsto_comap, tendsto_const_nhds, tendsto_const_nhds.congr
-/
theorem tendsto_cfcₙ_fun {l : Filter X} {F : X -> R -> R} {f : R -> R} {a : A}
    (h_tendsto : TendstoUniformlyOn F f l (quasispectrum R a))
    (hF : forallᶠ x in l, ContinuousOn (F x) (quasispectrum R a)) (hF0 : forallᶠ x in l, F x 0 = 0) :
    Tendsto (fun x => cfcₙ (F x) a) l (𝓝 (cfcₙ f a)) := by
  open scoped NonUnitalContinuousFunctionalCalculus in
  obtain (rfl | hl) := l.eq_or_neBot
  · simp
  have hf := h_tendsto.continuousOn hF.frequently
have hf0 : f 0 = 0 := Eq.symm
tendsto_nhds_unique (tendsto_const_nhds.congr' <| .symm hF0)
    h_tendsto.tendsto_at (quasispectrum.zero_mem R a)
  by_cases ha : p a
  · let s : Set X := {x | ContinuousOn (F x) (quasispectrum R a) ∧ F x 0 = 0}
    have hs : s in l := hF.and hF0
    rw [← tendsto_comap'_iff (i := ((↑) : s -> X)) (by simpa)]
    conv =>
      enter [1, x]
      rw [Function.comp_apply]; rw [cfcₙ_apply (hf := x.2.1) (hf0 := x.2.2)]
    rw [cfcₙ_apply ..]
.comp .tendsto _ apply cfcₙHom_continuous _
    rw [ContinuousMapZero.isEmbedding_toContinuousMap.isInducing.tendsto_nhds_iff]
    change Tendsto (fun x : s => (⟨_, x.2.1.domRestrict⟩ : C(quasispectrum R a, R))) _
      (𝓝 ⟨_, hf.domRestrict⟩)
    rw [hf.tendsto_domRestrict_iff_tendstoUniformlyOn (fun x => x.2.1)]
    intro t
    simp only [eventually_comap, Subtype.forall]
    peel h_tendsto t with ht x _
    simp_all
  · simpa [cfcₙ_apply_of_not_predicate a ha] using tendsto_const_nhds

/--
theorem `continuousAt_cfcₙ_fun` / 定理 `continuousAt_cfcₙ_fun`

English:
theorem continuousAt_cfcₙ_fun
  statement: [TopologicalSpace X] {f : X -> R -> R} {a : A}
  proof: tendsto_cfcₙ_fun h_tendsto hf hf0

中文:
定理 continuousAt_cfcₙ_fun
  结论: [拓扑空间 X] {f : X -> R -> R} {a : A}
  证明: tendsto_cfcₙ_fun h_tendsto hf hf0

Depends on / 依赖: h_tendsto
-/
theorem continuousAt_cfcₙ_fun [TopologicalSpace X] {f : X -> R -> R} {a : A}
    {x₀ : X} (h_tendsto : TendstoUniformlyOn f (f x₀) (𝓝 x₀) (quasispectrum R a))
    (hf : forallᶠ x in 𝓝 x₀, ContinuousOn (f x) (quasispectrum R a))
    (hf0 : forallᶠ x in 𝓝 x₀, f x 0 = 0) :
    ContinuousAt (fun x => cfcₙ (f x) a) x₀ :=
  tendsto_cfcₙ_fun h_tendsto hf hf0

/--
theorem `continuousWithinAt_cfcₙ_fun` / 定理 `continuousWithinAt_cfcₙ_fun`

English:
theorem continuousWithinAt_cfcₙ_fun
  statement: [TopologicalSpace X] {f : X -> R -> R} {a : A}
  proof: tendsto_cfcₙ_fun h_tendsto hf hf0

中文:
定理 continuousWithinAt_cfcₙ_fun
  结论: [拓扑空间 X] {f : X -> R -> R} {a : A}
  证明: tendsto_cfcₙ_fun h_tendsto hf hf0

Depends on / 依赖: ContinuousWithinAt, cfc_zero_tac, h_tendsto
-/
theorem continuousWithinAt_cfcₙ_fun [TopologicalSpace X] {f : X -> R -> R} {a : A}
    {x₀ : X} {s : Set X} (h_tendsto : TendstoUniformlyOn f (f x₀) (𝓝[s] x₀) (quasispectrum R a))
    (hf : forallᶠ x in 𝓝[s] x₀, ContinuousOn (f x) (quasispectrum R a))
    (hf0 : forallᶠ x in 𝓝[s] x₀, f x 0 = 0 := by cfc_zero_tac) :
    ContinuousWithinAt (fun x => cfcₙ (f x) a) s x₀ :=
  tendsto_cfcₙ_fun h_tendsto hf hf0

open UniformOnFun in
/--
theorem `ContinuousOn.cfcₙ_fun` / 定理 `ContinuousOn.cfcₙ_fun`

English:
theorem ContinuousOn.cfcₙ_fun
  statement: [TopologicalSpace X] {f : X -> R -> R} {a : A} {s : Set X}
  proof: by
  rw [ContinuousOn] at h_cont ⊢
  simp only [ContinuousWithinAt, UniformOnFun.tendsto_iff_tendstoUniformlyOn, Set.mem_singleton_iff,
    Function.comp_def, toFun_ofFun, forall_eq] at h_cont
  refine fun x hx => continuousWithinAt_cfcₙ_fun (h_cont x hx) ?_ ?_
  all_goals filter_upwards [self_mem_n

中文:
定理 ContinuousOn.cfcₙ_fun
  结论: [拓扑空间 X] {f : X -> R -> R} {a : A} {s : 集合 X}
  证明: by
  rw [ContinuousOn] at h_cont ⊢
  simp only [ContinuousWithinAt, UniformOnFun.tendsto_iff_tendstoUniformlyOn, Set.mem_singleton_iff,
    Function.comp_def, toFun_ofFun, forall_eq] at h_cont
  refine fun x hx => continuousWithinAt_cfcₙ_fun (h_cont x hx) ?_ ?_
  all_goals filter_upwards [self_mem_n

Depends on / 依赖: ContinuousOn, ContinuousWithinAt, Function, Function.comp_def, Set.mem_singleton_iff, UniformOnFun, UniformOnFun.tendsto_iff_tendstoUniformlyOn, all_goals, comp_def, exacts, filter_upwards, forall_eq, h_cont, mem_singleton_iff, self_mem_nhdsWithin, tendsto_iff_tendstoUniformlyOn, toFun_ofFun
-/
theorem ContinuousOn.cfcₙ_fun [TopologicalSpace X] {f : X -> R -> R} {a : A} {s : Set X}
    (h_cont : ContinuousOn (fun x => ofFun {quasispectrum R a} (f x)) s)
    (hf : forall x in s, ContinuousOn (f x) (quasispectrum R a))
    (hf0 : forall x in s, f x 0 = 0) :
    ContinuousOn (fun x => cfcₙ (f x) a) s := by
  rw [ContinuousOn] at h_cont ⊢
  simp only [ContinuousWithinAt, UniformOnFun.tendsto_iff_tendstoUniformlyOn, Set.mem_singleton_iff,
    Function.comp_def, toFun_ofFun, forall_eq] at h_cont
  refine fun x hx => continuousWithinAt_cfcₙ_fun (h_cont x hx) ?_ ?_
  all_goals filter_upwards [self_mem_nhdsWithin] with x hx
  exacts [hf x hx, hf0 x hx]

open UniformOnFun in
/--
theorem `Continuous.cfcₙ_fun` / 定理 `Continuous.cfcₙ_fun`

English:
theorem Continuous.cfcₙ_fun
  statement: [TopologicalSpace X] (f : X -> R -> R) (a : A)
  proof: by
  rw [← continuousOn_univ] at h_cont ⊢
  exact h_cont.cfcₙ_fun (fun x _ => hf x) (fun x _ => hf0 x)

中文:
定理 连续.cfcₙ_fun
  结论: [拓扑空间 X] (f : X -> R -> R) (a : A)
  证明: by
  rw [← continuousOn_univ] at h_cont ⊢
  exact h_cont.cfcₙ_fun (fun x _ => hf x) (fun x _ => hf0 x)

Depends on / 依赖: Continuous, cfc_cont_tac, cfc_zero_tac, continuousOn_univ, h_cont, h_cont.cfc
-/
theorem Continuous.cfcₙ_fun [TopologicalSpace X] (f : X -> R -> R) (a : A)
    (h_cont : Continuous (fun x => ofFun {quasispectrum R a} (f x)))
    (hf : forall x, ContinuousOn (f x) (quasispectrum R a) := by cfc_cont_tac)
    (hf0 : forall x, f x 0 = 0 := by cfc_zero_tac) :
    Continuous fun x => cfcₙ (f x) a := by
  rw [← continuousOn_univ] at h_cont ⊢
  exact h_cont.cfcₙ_fun (fun x _ => hf x) (fun x _ => hf0 x)

end Generic

section Isometric

variable {X R A : Type*} {p : A -> Prop} [CommSemiring R] [StarRing R] [MetricSpace R] [Nontrivial R]
    [IsTopologicalSemiring R] [ContinuousStar R] [NonUnitalRing A] [StarRing A]
    [MetricSpace A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
    [NonUnitalIsometricContinuousFunctionalCalculus R A p]

variable (R) in
open UniformOnFun in
open scoped NonUnitalContinuousFunctionalCalculus in
/--
lemma `lipschitzOnWith_cfcₙ_fun` / 引理 `lipschitzOnWith_cfcₙ_fun`

English:
lemma lipschitzOnWith_cfcₙ_fun
  given: (a : A)
  proof: by
  by_cases ha : p a
  · rintro f ⟨hf, hf0⟩ g ⟨hg, hg0⟩
    simp only
    rw [cfcₙ_apply ..]; rw [cfcₙ_apply ..]; rw [isometry_cfcₙHom (R := R) a ha |>.edist_eq]
    simp only [ENNReal.coe_one, one_mul]
    rw [← ContinuousMapZero.isometry_toContinuousMap.edist_eq]; rw [edist_continuousRestrict_of

中文:
引理 lipschitzOnWith_cfcₙ_fun
  条件: (a : A)
  证明: by
  by_cases ha : p a
  · rintro f ⟨hf, hf0⟩ g ⟨hg, hg0⟩
    simp only
    rw [cfcₙ_apply ..]; rw [cfcₙ_apply ..]; rw [isometry_cfcₙHom (R := R) a ha |>.edist_eq]
    simp only [ENNReal.coe_one, one_mul]
    rw [← ContinuousMapZero.isometry_toContinuousMap.edist_eq]; rw [edist_continuousRestrict_of

Depends on / 依赖: ContinuousMapZero, ContinuousMapZero.isometry_toContinuousMap.edist_eq, ENNReal, ENNReal.coe_one, LipschitzWith, LipschitzWith.const, coe_one, edist_continuousRestrict_of_singleton, edist_eq, isometry_toContinuousMap, lipschitzOnWith, one_mul
-/
lemma lipschitzOnWith_cfcₙ_fun (a : A) :
    LipschitzOnWith 1 (fun f => cfcₙ (toFun {quasispectrum R a} f) a)
      {f | ContinuousOn (toFun {quasispectrum R a} f) (quasispectrum R a) ∧ f 0 = 0} := by
  by_cases ha : p a
  · rintro f ⟨hf, hf0⟩ g ⟨hg, hg0⟩
    simp only
    rw [cfcₙ_apply ..]; rw [cfcₙ_apply ..]; rw [isometry_cfcₙHom (R := R) a ha |>.edist_eq]
    simp only [ENNReal.coe_one, one_mul]
    rw [← ContinuousMapZero.isometry_toContinuousMap.edist_eq]; rw [edist_continuousRestrict_of_singleton hf hg]
.lipschitzOnWith · simpa [cfcₙ_apply_of_not_predicate a ha] using LipschitzWith.const' 0

open UniformOnFun in
open scoped ContinuousFunctionalCalculus in
/--
lemma `lipschitzOnWith_cfcₙ_fun_of_subset` / 引理 `lipschitzOnWith_cfcₙ_fun_of_subset`

English:
lemma lipschitzOnWith_cfcₙ_fun_of_subset
  given: (a : A) {s : Set R} (hs : quasispectrum R a subseteq s)
  proof: by
  have h₂ := lipschitzWith_one_ofFun_toFun' (𝔖 := {quasispectrum R a}) (𝔗 := {s}) (β := R)
    (by simpa)
  have h₃ := h₂.lipschitzOnWith (s := {f | ContinuousOn (toFun {s} f) (s) ∧ f 0 = 0})
.comp h₃ (fun f => .imp_left fun hf => hf.mono hs) simpa using! lipschitzOnWith_cfcₙ_fun R a

中文:
引理 lipschitzOnWith_cfcₙ_fun_of_subset
  条件: (a : A) {s : 集合 R} (hs : quasispectrum R a subseteq s)
  证明: by
  have h₂ := lipschitzWith_one_ofFun_toFun' (𝔖 := {quasispectrum R a}) (𝔗 := {s}) (β := R)
    (by simpa)
  have h₃ := h₂.lipschitzOnWith (s := {f | ContinuousOn (toFun {s} f) (s) ∧ f 0 = 0})
.comp h₃ (fun f => .imp_left fun hf => hf.mono hs) simpa using! lipschitzOnWith_cfcₙ_fun R a

Depends on / 依赖: ContinuousOn, hf.mono, imp_left, lipschitzOnWith, lipschitzWith_one_ofFun_toFun, quasispectrum
-/
lemma lipschitzOnWith_cfcₙ_fun_of_subset (a : A) {s : Set R} (hs : quasispectrum R a subseteq s) :
    LipschitzOnWith 1 (fun f => cfcₙ (toFun {s} f) a)
      {f | ContinuousOn (toFun {s} f) (s) ∧ f 0 = 0} := by
  have h₂ := lipschitzWith_one_ofFun_toFun' (𝔖 := {quasispectrum R a}) (𝔗 := {s}) (β := R)
    (by simpa)
  have h₃ := h₂.lipschitzOnWith (s := {f | ContinuousOn (toFun {s} f) (s) ∧ f 0 = 0})
.comp h₃ (fun f => .imp_left fun hf => hf.mono hs) simpa using! lipschitzOnWith_cfcₙ_fun R a

end Isometric

end Left

section Right
section RCLike

variable {X 𝕜 A : Type*} {p : A -> Prop} [RCLike 𝕜] [NonUnitalNormedRing A] [StarRing A]
    [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [ContinuousStar A]
    [NonUnitalIsometricContinuousFunctionalCalculus 𝕜 A p]

open scoped NonUnitalContinuousFunctionalCalculus ContinuousMapZero in
/--
theorem `continuous_cfcₙHomSuperset_left` / 定理 `continuous_cfcₙHomSuperset_left`

English:
theorem continuous_cfcₙHomSuperset_left
  proof: by
  have : CompactSpace s := by rwa [isCompact_iff_compactSpace] at hs
  induction f using ContinuousMapZero.induction_on_of_compact with
  | zero => simpa [map_zero] using! continuous_const
  | id => simpa only [cfcₙHomSuperset_id]
  | star_id => simp only [map_star, cfcₙHomSuperset_id]; fun_prop


中文:
定理 continuous_cfcₙHomSuperset_left
  证明: by
  have : CompactSpace s := by rwa [isCompact_iff_compactSpace] at hs
  induction f using ContinuousMapZero.induction_on_of_compact with
  | zero => simpa [map_zero] using! continuous_const
  | id => simpa only [cfcₙHomSuperset_id]
  | star_id => simp only [map_star, cfcₙHomSuperset_id]; fun_prop


Depends on / 依赖: CompactSpace, Continuous, ContinuousMapZero, ContinuousMapZero.induction_on_of_compact, cfc_tac, continuous_const, fun_prop, hf.add, hf.mul, induction_on_of_compact, isCompact_iff_compactSpace, map_add, map_mul, map_star, map_zero, star_id
-/
theorem continuous_cfcₙHomSuperset_left
    [TopologicalSpace X] {s : Set 𝕜} (hs : IsCompact s) [hs0 : Fact (0 in s)]
    (f : C(s, 𝕜)₀) {a : X -> A} (ha_cont : Continuous a)
    (ha : forall x, quasispectrum 𝕜 (a x) subseteq s) (ha' : forall x, p (a x) := by cfc_tac) :
    Continuous (fun x => cfcₙHomSuperset (ha' x) (ha x) f) := by
  have : CompactSpace s := by rwa [isCompact_iff_compactSpace] at hs
  induction f using ContinuousMapZero.induction_on_of_compact with
  | zero => simpa [map_zero] using! continuous_const
  | id => simpa only [cfcₙHomSuperset_id]
  | star_id => simp only [map_star, cfcₙHomSuperset_id]; fun_prop
  | add f g hf hg => simpa only [map_add] using! hf.add hg
  | mul f g hf hg => simpa only [map_mul] using! hf.mul hg
  | smul r f hf => simpa only [map_smul] using! hf.const_smul r
  | frequently f hf =>
    apply continuous_of_uniform_approx_of_continuous
    rw [Metric.uniformity_basis_dist_le.forall_iff (by aesop)]
    intro ε hε
    simp only [Set.mem_ofPred_eq, dist_eq_norm]
    obtain ⟨g, hg, g_cont⟩ := frequently_iff.mp hf (Metric.closedBall_mem_nhds f hε)
    simp only [Metric.mem_closedBall, dist_comm g, dist_eq_norm] at hg
    refine ⟨_, g_cont, fun x => ?_⟩
    rw [← map_sub]; rw [cfcₙHomSuperset_apply]
    rw [isometry_cfcₙHom (R := 𝕜) _ (ha' x) |>.norm_map_of_map_zero (map_zero (cfcₙHom (ha' x)))]
    rw [ContinuousMapZero.norm_def]; rw [ContinuousMap.norm_le _ hε.le] at hg ⊢
    aesop

variable (A) in
/--
theorem `continuousOn_cfcₙ` / 定理 `continuousOn_cfcₙ`

English:
theorem continuousOn_cfcₙ
  statement: {s : Set 𝕜} (hs : IsCompact s) (f : 𝕜 -> 𝕜)
  proof: by
  by_cases hs0 : 0 in s
  · rw [continuousOn_iff_continuous_domRestrict]
    convert!
      continuous_cfcₙHomSuperset_left hs (hs0 := ⟨hs0⟩) ⟨⟨_, hf.domRestrict⟩, hf0⟩ (X :=
        {a : A | p a ∧ quasispectrum 𝕜 a subseteq s}) continuous_subtype_val (fun x => x.2.2) with
      x
    rw [cfcₙHom

中文:
定理 continuousOn_cfcₙ
  结论: {s : 集合 𝕜} (hs : 是紧集 s) (f : 𝕜 -> 𝕜)
  证明: by
  by_cases hs0 : 0 in s
  · rw [continuousOn_iff_continuous_domRestrict]
    convert!
      continuous_cfcₙHomSuperset_left hs (hs0 := ⟨hs0⟩) ⟨⟨_, hf.domRestrict⟩, hf0⟩ (X :=
        {a : A | p a ∧ quasispectrum 𝕜 a subseteq s}) continuous_subtype_val (fun x => x.2.2) with
      x
    rw [cfcₙHom

Depends on / 依赖: ContinuousOn, Set.domRestrict_apply, cfc_cont_tac, cfc_zero_tac, continuousOn_iff_continuous_domRestrict, continuous_subtype_val, convert, domRestrict, domRestrict_apply, hf.domRestrict, hf.mono, quasispectrum, subseteq
-/
theorem continuousOn_cfcₙ {s : Set 𝕜} (hs : IsCompact s) (f : 𝕜 -> 𝕜)
    (hf : ContinuousOn f s := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac) :
    ContinuousOn (cfcₙ f · : A -> A) {a | p a ∧ quasispectrum 𝕜 a subseteq s} := by
  by_cases hs0 : 0 in s
  · rw [continuousOn_iff_continuous_domRestrict]
    convert!
      continuous_cfcₙHomSuperset_left hs (hs0 := ⟨hs0⟩) ⟨⟨_, hf.domRestrict⟩, hf0⟩ (X :=
        {a : A | p a ∧ quasispectrum 𝕜 a subseteq s}) continuous_subtype_val (fun x => x.2.2) with
      x
    rw [cfcₙHomSuperset_apply]; rw [Set.domRestrict_apply]; rw [cfcₙ_apply _ _ (hf.mono x.2.2) hf0 x.2.1]
    congr!
  · convert! continuousOn_empty _
    rw [Set.eq_empty_iff_forall_notMem]
exact fun a ha => hs0 ha.2 quasispectrum.zero_mem 𝕜 a

open UniformOnFun in
/--
theorem `continuousOn_cfcₙ_setProd` / 定理 `continuousOn_cfcₙ_setProd`

English:
theorem continuousOn_cfcₙ_setProd
  given: {s : Set 𝕜} (hs : IsCompact s)
  proof: continuousOn_prod_of_continuousOn_lipschitzOnWith _ 1
    (fun f hf => continuousOn_cfcₙ A hs ((toFun {s}) f) hf.1 hf.2)
    (fun a ⟨_, ha'⟩ => lipschitzOnWith_cfcₙ_fun_of_subset a ha')

中文:
定理 continuousOn_cfcₙ_setProd
  条件: {s : 集合 𝕜} (hs : 是紧集 s)
  证明: continuousOn_prod_of_continuousOn_lipschitzOnWith _ 1
    (fun f hf => continuousOn_cfcₙ A hs ((toFun {s}) f) hf.1 hf.2)
    (fun a ⟨_, ha'⟩ => lipschitzOnWith_cfcₙ_fun_of_subset a ha')

Depends on / 依赖: continuousOn_prod_of_continuousOn_lipschitzOnWith
-/
theorem continuousOn_cfcₙ_setProd {s : Set 𝕜} (hs : IsCompact s) :
    ContinuousOn (fun fa : (𝕜 ->ᵤ[{s}] 𝕜) × A => cfcₙ (toFun {s} fa.1) fa.2)
      ({f | ContinuousOn (toFun {s} f) s ∧ f 0 = 0} ×ˢ {a | p a ∧ quasispectrum 𝕜 a subseteq s}) :=
  continuousOn_prod_of_continuousOn_lipschitzOnWith _ 1
    (fun f hf => continuousOn_cfcₙ A hs ((toFun {s}) f) hf.1 hf.2)
    (fun a ⟨_, ha'⟩ => lipschitzOnWith_cfcₙ_fun_of_subset a ha')

open UniformOnFun in
/--
theorem `continuousOn_cfcₙ_setProd_nhdsSet` / 定理 `continuousOn_cfcₙ_setProd_nhdsSet`

English:
theorem continuousOn_cfcₙ_setProd_nhdsSet
  given: [CompleteSpace A] {s : Set 𝕜}
  proof: by
  refine continuousOn_of_locally_continuousOn fun (f, a) ⟨hf, ha, has⟩ => ?_
  have hs := NonUnitalContinuousFunctionalCalculus.isCompact_quasispectrum (R := 𝕜) a
  obtain ⟨k, ⟨hka, hk⟩, hks⟩ := hs.nhdsSet_basis_isCompact.mem_iff.mp has
  have := (upperHemicontinuous_quasispectrum 𝕜 A).isOpen k
 

中文:
定理 continuousOn_cfcₙ_setProd_nhdsSet
  条件: [完备空间 A] {s : 集合 𝕜}
  证明: by
  refine continuousOn_of_locally_continuousOn fun (f, a) ⟨hf, ha, has⟩ => ?_
  have hs := NonUnitalContinuousFunctionalCalculus.isCompact_quasispectrum (R := 𝕜) a
  obtain ⟨k, ⟨hka, hk⟩, hks⟩ := hs.nhdsSet_basis_isCompact.mem_iff.mp has
  have := (upperHemicontinuous_quasispectrum 𝕜 A).isOpen k
 

Depends on / 依赖: IsCompact, NonUnitalContinuousFunctionalCalculus, NonUnitalContinuousFunctionalCalculus.isCompact_quasispectrum, Set.univ, continuousOn_of_locally_continuousOn, equals, hs.nhdsSet_basis_isCompact.mem_iff.mp, isCompact_quasispectrum, isOpen, isOpen_univ, isOpen_univ.prod, mem_iff, nhdsSet_basis_isCompact, quasispectrum, subseteq, upperHemicontinuous_quasispectrum
-/
theorem continuousOn_cfcₙ_setProd_nhdsSet [CompleteSpace A] {s : Set 𝕜} :
    ContinuousOn (fun fa : (𝕜 ->ᵤ[{t | IsCompact t ∧ t subseteq s}] 𝕜) × A => cfcₙ (toFun {s} fa.1) fa.2)
      ({f | ContinuousOn (toFun {t | IsCompact t ∧ t subseteq s} f) s ∧ f 0 = 0} ×ˢ
        {a | p a ∧ s in 𝓝ˢ (quasispectrum 𝕜 a)}) := by
  refine continuousOn_of_locally_continuousOn fun (f, a) ⟨hf, ha, has⟩ => ?_
  have hs := NonUnitalContinuousFunctionalCalculus.isCompact_quasispectrum (R := 𝕜) a
  obtain ⟨k, ⟨hka, hk⟩, hks⟩ := hs.nhdsSet_basis_isCompact.mem_iff.mp has
  have := (upperHemicontinuous_quasispectrum 𝕜 A).isOpen k
  refine ⟨Set.univ ×ˢ {x | k in 𝓝ˢ (quasispectrum 𝕜 x)}, isOpen_univ.prod this, by simpa, ?_⟩
  conv in cfcₙ _ =>
    equals cfcₙ (toFun {k} (ofFun {k} (toFun {t | IsCompact t ∧ t subseteq s} fa.1))) => rfl
.comp' refine continuousOn_cfcₙ_setProd hk
    (uniformContinuous_ofFun_toFun_of_mem _ {t | IsCompact t ∧ t subseteq s} _ ⟨hk, hks⟩ |>.prodMap
      uniformContinuous_id).continuous.continuousOn ?_
  intro (f, a) ⟨⟨hf, ha⟩, ⟨_, ha'⟩⟩
  exact ⟨⟨hf.1.mono hks, hf.2⟩, ha.1, subset_of_mem_nhdsSet ha'⟩

/--
theorem `Filter.Tendsto.cfcₙ` / 定理 `Filter.Tendsto.cfcₙ`

English:
theorem Filter.Tendsto.cfcₙ
  statement: {s : Set 𝕜} (hs : IsCompact s) (f : 𝕜 -> 𝕜)
  proof: by
.tendsto.comp .continuousWithinAt ⟨ha₀', ha₀⟩ apply continuousOn_cfcₙ A hs f
  rw [tendsto_nhdsWithin_iff]
  exact ⟨ha_tendsto, ha'.and ha⟩

中文:
定理 滤子.收敛.cfcₙ
  结论: {s : 集合 𝕜} (hs : 是紧集 s) (f : 𝕜 -> 𝕜)
  证明: by
.tendsto.comp .continuousWithinAt ⟨ha₀', ha₀⟩ apply continuousOn_cfcₙ A hs f
  rw [tendsto_nhdsWithin_iff]
  exact ⟨ha_tendsto, ha'.and ha⟩
-/
protected theorem Filter.Tendsto.cfcₙ {s : Set 𝕜} (hs : IsCompact s) (f : 𝕜 -> 𝕜)
    {a : X -> A} {a₀ : A} {l : Filter X} (ha_tendsto : Tendsto a l (𝓝 a₀))
    (ha : forallᶠ x in l, quasispectrum 𝕜 (a x) subseteq s) (ha' : forallᶠ x in l, p (a x))
    (ha₀ : quasispectrum 𝕜 a₀ subseteq s) (ha₀' : p a₀) (hf : ContinuousOn f s := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) :
    Tendsto (fun x => cfcₙ f (a x)) l (𝓝 (cfcₙ f a₀)) := by
.tendsto.comp .continuousWithinAt ⟨ha₀', ha₀⟩ apply continuousOn_cfcₙ A hs f
  rw [tendsto_nhdsWithin_iff]
  exact ⟨ha_tendsto, ha'.and ha⟩

/--
theorem `ContinuousAt.cfcₙ` / 定理 `ContinuousAt.cfcₙ`

English:
theorem ContinuousAt.cfcₙ
  statement: [TopologicalSpace X] {s : Set 𝕜} (hs : IsCompact s) (f : 𝕜 -> 𝕜)
  proof: ha_cont.tendsto.cfcₙ hs f ha ha' ha.self_of_nhds ha'.self_of_nhds

中文:
定理 ContinuousAt.cfcₙ
  结论: [拓扑空间 X] {s : 集合 𝕜} (hs : 是紧集 s) (f : 𝕜 -> 𝕜)
  证明: ha_cont.tendsto.cfcₙ hs f ha ha' ha.self_of_nhds ha'.self_of_nhds
-/
protected theorem ContinuousAt.cfcₙ [TopologicalSpace X] {s : Set 𝕜} (hs : IsCompact s) (f : 𝕜 -> 𝕜)
    {a : X -> A} {x₀ : X} (ha_cont : ContinuousAt a x₀)
    (ha : forallᶠ x in 𝓝 x₀, quasispectrum 𝕜 (a x) subseteq s) (ha' : forallᶠ x in 𝓝 x₀, p (a x))
    (hf : ContinuousOn f s := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac) :
    ContinuousAt (fun x => cfcₙ f (a x)) x₀ :=
  ha_cont.tendsto.cfcₙ hs f ha ha' ha.self_of_nhds ha'.self_of_nhds

/--
theorem `ContinuousWithinAt.cfcₙ` / 定理 `ContinuousWithinAt.cfcₙ`

English:
theorem ContinuousWithinAt.cfcₙ
  statement: [TopologicalSpace X] {s : Set 𝕜} (hs : IsCompact s)
  proof: ha_cont.tendsto.cfcₙ hs f ha ha' (ha.self_of_nhdsWithin hx₀) (ha'.self_of_nhdsWithin hx₀)

中文:
定理 ContinuousWithinAt.cfcₙ
  结论: [拓扑空间 X] {s : 集合 𝕜} (hs : 是紧集 s)
  证明: ha_cont.tendsto.cfcₙ hs f ha ha' (ha.self_of_nhdsWithin hx₀) (ha'.self_of_nhdsWithin hx₀)
-/
protected theorem ContinuousWithinAt.cfcₙ [TopologicalSpace X] {s : Set 𝕜} (hs : IsCompact s)
    (f : 𝕜 -> 𝕜) {a : X -> A} {x₀ : X} {t : Set X} (hx₀ : x₀ in t)
    (ha_cont : ContinuousWithinAt a t x₀) (ha : forallᶠ x in 𝓝[t] x₀, quasispectrum 𝕜 (a x) subseteq s)
    (ha' : forallᶠ x in 𝓝[t] x₀, p (a x)) (hf : ContinuousOn f s := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) :
    ContinuousWithinAt (fun x => cfcₙ f (a x)) t x₀ :=
  ha_cont.tendsto.cfcₙ hs f ha ha' (ha.self_of_nhdsWithin hx₀) (ha'.self_of_nhdsWithin hx₀)

/--
theorem `ContinuousOn.cfcₙ` / 定理 `ContinuousOn.cfcₙ`

English:
theorem ContinuousOn.cfcₙ
  statement: [TopologicalSpace X] {s : X -> Set 𝕜} (f : 𝕜 -> 𝕜) {a : X -> A}
  proof: by
  rw [ContinuousOn] at ha_cont ⊢
  refine fun x hx => (ha_cont x hx).cfcₙ (hs x hx) f hx ?_ ?_ (hf x hx)
  all_goals filter_upwards [ha x hx, self_mem_nhdsWithin] with x hx hxt
  exacts [hx, ha' x hxt]

中文:
定理 ContinuousOn.cfcₙ
  结论: [拓扑空间 X] {s : X -> 集合 𝕜} (f : 𝕜 -> 𝕜) {a : X -> A}
  证明: by
  rw [ContinuousOn] at ha_cont ⊢
  refine fun x hx => (ha_cont x hx).cfcₙ (hs x hx) f hx ?_ ?_ (hf x hx)
  all_goals filter_upwards [ha x hx, self_mem_nhdsWithin] with x hx hxt
  exacts [hx, ha' x hxt]
-/
protected theorem ContinuousOn.cfcₙ [TopologicalSpace X] {s : X -> Set 𝕜} (f : 𝕜 -> 𝕜) {a : X -> A}
    {t : Set X} (hs : forall x in t, IsCompact (s x)) (ha_cont : ContinuousOn a t)
    (ha : forall x₀ in t, forallᶠ x in 𝓝[t] x₀, quasispectrum 𝕜 (a x) subseteq s x₀) (ha' : forall x in t, p (a x))
    (hf : forall x in t, ContinuousOn f (s x) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac) :
    ContinuousOn (fun x => cfcₙ f (a x)) t := by
  rw [ContinuousOn] at ha_cont ⊢
  refine fun x hx => (ha_cont x hx).cfcₙ (hs x hx) f hx ?_ ?_ (hf x hx)
  all_goals filter_upwards [ha x hx, self_mem_nhdsWithin] with x hx hxt
  exacts [hx, ha' x hxt]

/--
theorem `ContinuousOn.cfcₙ'` / 定理 `ContinuousOn.cfcₙ'`

English:
theorem ContinuousOn.cfcₙ'
  statement: [TopologicalSpace X] {s : Set 𝕜} (hs : IsCompact s)
  proof: by
  refine ContinuousOn.cfcₙ _ (fun _ _ => hs) ha_cont (fun _ _ => ?_) ha'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact ha x hx

中文:
定理 ContinuousOn.cfcₙ'
  结论: [拓扑空间 X] {s : 集合 𝕜} (hs : 是紧集 s)
  证明: by
  refine ContinuousOn.cfcₙ _ (fun _ _ => hs) ha_cont (fun _ _ => ?_) ha'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact ha x hx

Depends on / 依赖: ContinuousOn, ContinuousOn.cfc, cfc_cont_tac, cfc_zero_tac, filter_upwards, ha_cont, self_mem_nhdsWithin
-/
theorem ContinuousOn.cfcₙ' [TopologicalSpace X] {s : Set 𝕜} (hs : IsCompact s)
    (f : 𝕜 -> 𝕜) {a : X -> A} {t : Set X} (ha_cont : ContinuousOn a t)
    (ha : forall x in t, quasispectrum 𝕜 (a x) subseteq s) (ha' : forall x in t, p (a x))
    (hf : ContinuousOn f s := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac) :
    ContinuousOn (fun x => cfcₙ f (a x)) t := by
  refine ContinuousOn.cfcₙ _ (fun _ _ => hs) ha_cont (fun _ _ => ?_) ha'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact ha x hx

/--
theorem `ContinuousOn.cfcₙ_of_mem_nhdsSet` / 定理 `ContinuousOn.cfcₙ_of_mem_nhdsSet`

English:
theorem ContinuousOn.cfcₙ_of_mem_nhdsSet
  statement: [CompleteSpace A] [TopologicalSpace X] {s : Set 𝕜}
  proof: by
  have hs' := hs
  simp only [nhdsSet_iUnion, mem_iSup] at hs'
  have (x : t) : exists S, IsCompact S ∧ (forallᶠ (x' : A) in 𝓝 (a x), quasispectrum 𝕜 x' subseteq S) ∧ S subseteq s := by
    obtain ⟨S, ⟨hS₁, hS₂⟩, hS₃⟩ :=
.nhdsSet_basis_isCompact.mem_iff.mp (hs' x x.2) quasispectrum.isCompact (𝕜 :

中文:
定理 ContinuousOn.cfcₙ_of_mem_nhdsSet
  结论: [完备空间 A] [拓扑空间 X] {s : 集合 𝕜}
  证明: by
  have hs' := hs
  simp only [nhdsSet_iUnion, mem_iSup] at hs'
  have (x : t) : exists S, IsCompact S ∧ (forallᶠ (x' : A) in 𝓝 (a x), quasispectrum 𝕜 x' subseteq S) ∧ S subseteq s := by
    obtain ⟨S, ⟨hS₁, hS₂⟩, hS₃⟩ :=
.nhdsSet_basis_isCompact.mem_iff.mp (hs' x x.2) quasispectrum.isCompact (𝕜 :

Depends on / 依赖: ContinuousOn, IsCompact, cfc_cont_tac, cfc_tac, cfc_zero_tac, isCompact, mem_iSup, mem_iff, nhdsSet_basis_isCompact, nhdsSet_basis_isCompact.mem_iff.mp, nhdsSet_iUnion, quasispectrum, quasispectrum.isCompact, subseteq, upperHemicontinuousAt
-/
theorem ContinuousOn.cfcₙ_of_mem_nhdsSet [CompleteSpace A] [TopologicalSpace X] {s : Set 𝕜}
    (f : 𝕜 -> 𝕜) {a : X -> A} {t : Set X} (hs : s in 𝓝ˢ (⋃ x in t, quasispectrum 𝕜 (a x)))
    (ha_cont : ContinuousOn a t) (ha' : forall x in t, p (a x) := by cfc_tac)
    (hf : ContinuousOn f s := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac) :
    ContinuousOn (fun x => cfcₙ f (a x)) t := by
  have hs' := hs
  simp only [nhdsSet_iUnion, mem_iSup] at hs'
  have (x : t) : exists S, IsCompact S ∧ (forallᶠ (x' : A) in 𝓝 (a x), quasispectrum 𝕜 x' subseteq S) ∧ S subseteq s := by
    obtain ⟨S, ⟨hS₁, hS₂⟩, hS₃⟩ :=
.nhdsSet_basis_isCompact.mem_iff.mp (hs' x x.2) quasispectrum.isCompact (𝕜 := 𝕜) (a x)
    refine ⟨S, hS₂, ?_, hS₃⟩
.mono .upperHemicontinuousAt (a x) _ hS₁ exact upperHemicontinuous_quasispectrum 𝕜 A
      fun _ => subset_of_mem_nhdsSet
  choose S hS₁ hS₂ hS₃ using this
  classical
  refine ha_cont.cfcₙ (s := fun x : X => if hx : x in t then S ⟨x, hx⟩ else ∅) f
    (by simpa +contextual using hS₁) ?_ ha' ?_
  all_goals simp +contextual only [↓reduceDIte]
.eventually hS₂ ⟨x₀, hx₀⟩ · exact fun x₀ hx₀ => ha_cont.continuousWithinAt hx₀
· exact fun x hx => hf.mono hS₃ ⟨x, hx⟩

/--
theorem `Continuous.cfcₙ` / 定理 `Continuous.cfcₙ`

English:
theorem Continuous.cfcₙ
  statement: [TopologicalSpace X] {s : X -> Set 𝕜} (f : 𝕜 -> 𝕜) {a : X -> A}
  proof: by
  rw [← continuousOn_univ] at ha_cont ⊢
  exact ha_cont.cfcₙ f (fun x _ => hs x) (fun x _ => by simpa using ha x) (fun x _ => ha' x)

中文:
定理 连续.cfcₙ
  结论: [拓扑空间 X] {s : X -> 集合 𝕜} (f : 𝕜 -> 𝕜) {a : X -> A}
  证明: by
  rw [← continuousOn_univ] at ha_cont ⊢
  exact ha_cont.cfcₙ f (fun x _ => hs x) (fun x _ => by simpa using ha x) (fun x _ => ha' x)
-/
protected theorem Continuous.cfcₙ [TopologicalSpace X] {s : X -> Set 𝕜} (f : 𝕜 -> 𝕜) {a : X -> A}
    (ha_cont : Continuous a) (hs : forall x, IsCompact (s x))
    (ha : forall x₀, forallᶠ x in 𝓝 x₀, quasispectrum 𝕜 (a x) subseteq s x₀)
    (hf : forall x, ContinuousOn f (s x) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac)
    (ha' : forall x, p (a x) := by cfc_tac) :
    Continuous (fun x => cfcₙ f (a x)) := by
  rw [← continuousOn_univ] at ha_cont ⊢
  exact ha_cont.cfcₙ f (fun x _ => hs x) (fun x _ => by simpa using ha x) (fun x _ => ha' x)

/--
theorem `Continuous.cfcₙ'` / 定理 `Continuous.cfcₙ'`

English:
theorem Continuous.cfcₙ'
  statement: [TopologicalSpace X] {s : Set 𝕜} (hs : IsCompact s) (f : 𝕜 -> 𝕜)
  proof: by
  rw [← continuousOn_univ] at ha_cont ⊢
  exact ha_cont.cfcₙ' hs f (fun x _ => ha x) (fun x _ => ha' x)

中文:
定理 连续.cfcₙ'
  结论: [拓扑空间 X] {s : 集合 𝕜} (hs : 是紧集 s) (f : 𝕜 -> 𝕜)
  证明: by
  rw [← continuousOn_univ] at ha_cont ⊢
  exact ha_cont.cfcₙ' hs f (fun x _ => ha x) (fun x _ => ha' x)

Depends on / 依赖: Continuous, cfc_cont_tac, cfc_tac, cfc_zero_tac, continuousOn_univ, ha_cont, ha_cont.cfc
-/
theorem Continuous.cfcₙ' [TopologicalSpace X] {s : Set 𝕜} (hs : IsCompact s) (f : 𝕜 -> 𝕜)
    {a : X -> A} (ha_cont : Continuous a) (ha : forall x, quasispectrum 𝕜 (a x) subseteq s)
    (hf : ContinuousOn f s := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac)
    (ha' : forall x, p (a x) := by cfc_tac) :
    Continuous (fun x => cfcₙ f (a x)) := by
  rw [← continuousOn_univ] at ha_cont ⊢
  exact ha_cont.cfcₙ' hs f (fun x _ => ha x) (fun x _ => ha' x)

/--
theorem `Continuous.cfcₙ_of_mem_nhdsSet` / 定理 `Continuous.cfcₙ_of_mem_nhdsSet`

English:
theorem Continuous.cfcₙ_of_mem_nhdsSet
  statement: [CompleteSpace A] [TopologicalSpace X] {s : Set 𝕜}
  proof: by
  rw [← continuousOn_univ] at ha_cont ⊢
  exact ha_cont.cfcₙ_of_mem_nhdsSet f (by simpa) (by simpa)

中文:
定理 连续.cfcₙ_of_mem_nhdsSet
  结论: [完备空间 A] [拓扑空间 X] {s : 集合 𝕜}
  证明: by
  rw [← continuousOn_univ] at ha_cont ⊢
  exact ha_cont.cfcₙ_of_mem_nhdsSet f (by simpa) (by simpa)

Depends on / 依赖: Continuous, ContinuousOn, cfc_cont_tac, cfc_tac, cfc_zero_tac, continuousOn_univ, ha_cont, ha_cont.cfc
-/
theorem Continuous.cfcₙ_of_mem_nhdsSet [CompleteSpace A] [TopologicalSpace X] {s : Set 𝕜}
    (f : 𝕜 -> 𝕜) {a : X -> A} (hs : s in 𝓝ˢ (⋃ x, quasispectrum 𝕜 (a x))) (ha_cont : Continuous a)
    (ha' : forall x, p (a x) := by cfc_tac) (hf : ContinuousOn f s := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) :
    Continuous (fun x => cfcₙ f (a x)) := by
  rw [← continuousOn_univ] at ha_cont ⊢
  exact ha_cont.cfcₙ_of_mem_nhdsSet f (by simpa) (by simpa)

end RCLike

section NNReal

variable {X A : Type*} [NonUnitalNormedRing A] [StarRing A]
    [NormedSpace Real A] [IsScalarTower Real A A] [SMulCommClass Real A A] [ContinuousStar A]
    [NonUnitalIsometricContinuousFunctionalCalculus Real A IsSelfAdjoint]
    [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass Real A]
    [T2Space A] [IsSemitopologicalRing A]

variable (A) in
/--
theorem `continuousOn_cfcₙ_nnreal` / 定理 `continuousOn_cfcₙ_nnreal`

English:
theorem continuousOn_cfcₙ_nnreal
  statement: {s : Set Real>=0} (hs : IsCompact s) (f : Real>=0 -> Real>=0)
  proof: by
  have : {a : A | 0 <= a ∧ quasispectrum Real>=0 a subseteq s}.EqOn (cfcₙ f)
      (cfcₙ (fun x : Real => f x.toNNReal)) :=
    fun a ha => cfcₙ_nnreal_eq_real _ _ ha.1
  refine ContinuousOn.congr ?_ this
  replace hf : ContinuousOn (fun x => f x.toNNReal : Real -> Real) (NNReal.toReal '' s) := b

中文:
定理 continuousOn_cfcₙ_nnreal
  结论: {s : 集合 实数>=0} (hs : 是紧集 s) (f : 实数>=0 -> 实数>=0)
  证明: by
  have : {a : A | 0 <= a ∧ quasispectrum Real>=0 a subseteq s}.EqOn (cfcₙ f)
      (cfcₙ (fun x : Real => f x.toNNReal)) :=
    fun a ha => cfcₙ_nnreal_eq_real _ _ ha.1
  refine ContinuousOn.congr ?_ this
  replace hf : ContinuousOn (fun x => f x.toNNReal : Real -> Real) (NNReal.toReal '' s) := b

Depends on / 依赖: ContinuousOn, ContinuousOn.congr, NNReal, NNReal.toReal, Set.mapsTo_image_iff, cfc_cont_tac, cfc_zero_tac, hf.ofReal_map_toNNReal, mapsTo_image_iff, ofReal_map_toNNReal, quasispectrum, replace, subseteq, toNNReal, toReal, x.toNNReal
-/
theorem continuousOn_cfcₙ_nnreal {s : Set Real>=0} (hs : IsCompact s) (f : Real>=0 -> Real>=0)
    (hf : ContinuousOn f s := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac) :
    ContinuousOn (cfcₙ f · : A -> A) {a : A | 0 <= a ∧ quasispectrum Real>=0 a subseteq s} := by
  have : {a : A | 0 <= a ∧ quasispectrum Real>=0 a subseteq s}.EqOn (cfcₙ f)
      (cfcₙ (fun x : Real => f x.toNNReal)) :=
    fun a ha => cfcₙ_nnreal_eq_real _ _ ha.1
  refine ContinuousOn.congr ?_ this
  replace hf : ContinuousOn (fun x => f x.toNNReal : Real -> Real) (NNReal.toReal '' s) := by
    apply hf.ofReal_map_toNNReal
    rw [Set.mapsTo_image_iff]
    intro x hx
    simpa
.mono fun a ha => ?_ refine continuousOn_cfcₙ A (hs.image NNReal.continuous_coe) _ hf
  simp only [Set.mem_ofPred_eq, nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts] at ha ⊢
  refine ⟨ha.1.1, ?_⟩
  rw [← ha.1.2.algebraMap_image]
  exact Set.image_mono ha.2

open UniformOnFun in
/--
theorem `continuousOn_cfcₙ_nnreal_setProd` / 定理 `continuousOn_cfcₙ_nnreal_setProd`

English:
theorem continuousOn_cfcₙ_nnreal_setProd
  given: {s : Set Real>=0} (hs : IsCompact s)
  proof: continuousOn_prod_of_continuousOn_lipschitzOnWith _ 1
    (fun f hf => continuousOn_cfcₙ_nnreal A hs ((toFun {s}) f) hf.1 hf.2)
    (fun a ⟨_, ha'⟩ => lipschitzOnWith_cfcₙ_fun_of_subset a ha')

中文:
定理 continuousOn_cfcₙ_nnreal_setProd
  条件: {s : 集合 实数>=0} (hs : 是紧集 s)
  证明: continuousOn_prod_of_continuousOn_lipschitzOnWith _ 1
    (fun f hf => continuousOn_cfcₙ_nnreal A hs ((toFun {s}) f) hf.1 hf.2)
    (fun a ⟨_, ha'⟩ => lipschitzOnWith_cfcₙ_fun_of_subset a ha')

Depends on / 依赖: continuousOn_prod_of_continuousOn_lipschitzOnWith
-/
theorem continuousOn_cfcₙ_nnreal_setProd {s : Set Real>=0} (hs : IsCompact s) :
    ContinuousOn (fun fa : (Real>=0 ->ᵤ[{s}] Real>=0) × A => cfcₙ (toFun {s} fa.1) fa.2)
      ({f | ContinuousOn (toFun {s} f) s ∧ f 0 = 0} ×ˢ {a | 0 <= a ∧ quasispectrum Real>=0 a subseteq s}) :=
  continuousOn_prod_of_continuousOn_lipschitzOnWith _ 1
    (fun f hf => continuousOn_cfcₙ_nnreal A hs ((toFun {s}) f) hf.1 hf.2)
    (fun a ⟨_, ha'⟩ => lipschitzOnWith_cfcₙ_fun_of_subset a ha')

open UniformOnFun in
/--
theorem `continuousOn_cfcₙ_nnreal_setProd_nhdsSet` / 定理 `continuousOn_cfcₙ_nnreal_setProd_nhdsSet`

English:
theorem continuousOn_cfcₙ_nnreal_setProd_nhdsSet
  given: [CompleteSpace A] {s : Set Real>=0}
  proof: by
  refine continuousOn_of_locally_continuousOn fun (f, a) ⟨hf, ha, has⟩ => ?_
  have hs := NonUnitalContinuousFunctionalCalculus.isCompact_quasispectrum (R := Real>=0) a
  obtain ⟨k, ⟨hka, hk⟩, hks⟩ := hs.nhdsSet_basis_isCompact.mem_iff.mp has
  have := (upperHemicontinuous_quasispectrum_nnreal A)

中文:
定理 continuousOn_cfcₙ_nnreal_setProd_nhdsSet
  条件: [完备空间 A] {s : 集合 实数>=0}
  证明: by
  refine continuousOn_of_locally_continuousOn fun (f, a) ⟨hf, ha, has⟩ => ?_
  have hs := NonUnitalContinuousFunctionalCalculus.isCompact_quasispectrum (R := Real>=0) a
  obtain ⟨k, ⟨hka, hk⟩, hks⟩ := hs.nhdsSet_basis_isCompact.mem_iff.mp has
  have := (upperHemicontinuous_quasispectrum_nnreal A)

Depends on / 依赖: IsCompact, NonUnitalContinuousFunctionalCalculus, NonUnitalContinuousFunctionalCalculus.isCompact_quasispectrum, Set.univ, continuousOn_of_locally_continuousOn, equals, hs.nhdsSet_basis_isCompact.mem_iff.mp, isCompact_quasispectrum, isOpen, isOpen_univ, isOpen_univ.prod, mem_iff, nhdsSet_basis_isCompact, quasispectrum, subseteq, upperHemicontinuous_quasispectrum_nnreal
-/
theorem continuousOn_cfcₙ_nnreal_setProd_nhdsSet [CompleteSpace A] {s : Set Real>=0} :
    ContinuousOn (fun fa : (Real>=0 ->ᵤ[{t | IsCompact t ∧ t subseteq s}] Real>=0) × A => cfcₙ (toFun {s} fa.1) fa.2)
      ({f | ContinuousOn (toFun {t | IsCompact t ∧ t subseteq s} f) s ∧ f 0 = 0} ×ˢ
        {a | 0 <= a ∧ s in 𝓝ˢ (quasispectrum Real>=0 a)}) := by
  refine continuousOn_of_locally_continuousOn fun (f, a) ⟨hf, ha, has⟩ => ?_
  have hs := NonUnitalContinuousFunctionalCalculus.isCompact_quasispectrum (R := Real>=0) a
  obtain ⟨k, ⟨hka, hk⟩, hks⟩ := hs.nhdsSet_basis_isCompact.mem_iff.mp has
  have := (upperHemicontinuous_quasispectrum_nnreal A).isOpen k
  refine ⟨Set.univ ×ˢ {x | k in 𝓝ˢ (quasispectrum Real>=0 x)}, isOpen_univ.prod this, by simpa, ?_⟩
  conv in cfcₙ _ =>
    equals cfcₙ (toFun {k} (ofFun {k} (toFun {t | IsCompact t ∧ t subseteq s} fa.1))) => rfl
.comp' refine continuousOn_cfcₙ_nnreal_setProd hk
    (uniformContinuous_ofFun_toFun_of_mem _ {t | IsCompact t ∧ t subseteq s} _ ⟨hk, hks⟩ |>.prodMap
      uniformContinuous_id).continuous.continuousOn ?_
  intro (f, a) ⟨⟨hf, ha⟩, ⟨_, ha'⟩⟩
  exact ⟨⟨hf.1.mono hks, hf.2⟩, ha.1, subset_of_mem_nhdsSet ha'⟩

/--
theorem `Filter.Tendsto.cfcₙ_nnreal` / 定理 `Filter.Tendsto.cfcₙ_nnreal`

English:
theorem Filter.Tendsto.cfcₙ_nnreal
  statement: {s : Set Real>=0} (hs : IsCompact s) (f : Real>=0 -> Real>=0)
  proof: by
.tendsto.comp .continuousWithinAt ⟨ha₀', ha₀⟩ apply continuousOn_cfcₙ_nnreal A hs f
  rw [tendsto_nhdsWithin_iff]
  exact ⟨ha_tendsto, ha'.and ha⟩

中文:
定理 滤子.收敛.cfcₙ_nnreal
  结论: {s : 集合 实数>=0} (hs : 是紧集 s) (f : 实数>=0 -> 实数>=0)
  证明: by
.tendsto.comp .continuousWithinAt ⟨ha₀', ha₀⟩ apply continuousOn_cfcₙ_nnreal A hs f
  rw [tendsto_nhdsWithin_iff]
  exact ⟨ha_tendsto, ha'.and ha⟩

Depends on / 依赖: Tendsto, cfc_cont_tac, cfc_zero_tac, continuousWithinAt, ha_tendsto, tendsto, tendsto.comp, tendsto_nhdsWithin_iff
-/
theorem Filter.Tendsto.cfcₙ_nnreal {s : Set Real>=0} (hs : IsCompact s) (f : Real>=0 -> Real>=0)
    {a : X -> A} {a₀ : A} {l : Filter X} (ha_tendsto : Tendsto a l (𝓝 a₀))
    (ha : forallᶠ x in l, quasispectrum Real>=0 (a x) subseteq s) (ha' : forallᶠ x in l, 0 <= a x)
    (ha₀ : quasispectrum Real>=0 a₀ subseteq s) (ha₀' : 0 <= a₀) (hf : ContinuousOn f s := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) :
    Tendsto (fun x => cfcₙ f (a x)) l (𝓝 (cfcₙ f a₀)) := by
.tendsto.comp .continuousWithinAt ⟨ha₀', ha₀⟩ apply continuousOn_cfcₙ_nnreal A hs f
  rw [tendsto_nhdsWithin_iff]
  exact ⟨ha_tendsto, ha'.and ha⟩

/--
theorem `ContinuousAt.cfcₙ_nnreal` / 定理 `ContinuousAt.cfcₙ_nnreal`

English:
theorem ContinuousAt.cfcₙ_nnreal
  statement: [TopologicalSpace X] {s : Set Real>=0}
  proof: ha_cont.tendsto.cfcₙ_nnreal hs f ha ha' ha.self_of_nhds ha'.self_of_nhds

中文:
定理 ContinuousAt.cfcₙ_nnreal
  结论: [拓扑空间 X] {s : 集合 实数>=0}
  证明: ha_cont.tendsto.cfcₙ_nnreal hs f ha ha' ha.self_of_nhds ha'.self_of_nhds

Depends on / 依赖: ContinuousAt, cfc_cont_tac, cfc_zero_tac, ha.self_of_nhds, ha_cont, ha_cont.tendsto.cfc, self_of_nhds, tendsto
-/
theorem ContinuousAt.cfcₙ_nnreal [TopologicalSpace X] {s : Set Real>=0}
    (hs : IsCompact s) (f : Real>=0 -> Real>=0) {a : X -> A} {x₀ : X} (ha_cont : ContinuousAt a x₀)
    (ha : forallᶠ x in 𝓝 x₀, quasispectrum Real>=0 (a x) subseteq s) (ha' : forallᶠ x in 𝓝 x₀, 0 <= a x)
    (hf : ContinuousOn f s := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac) :
    ContinuousAt (fun x => cfcₙ f (a x)) x₀ :=
  ha_cont.tendsto.cfcₙ_nnreal hs f ha ha' ha.self_of_nhds ha'.self_of_nhds

/--
theorem `ContinuousWithinAt.cfcₙ_nnreal` / 定理 `ContinuousWithinAt.cfcₙ_nnreal`

English:
theorem ContinuousWithinAt.cfcₙ_nnreal
  statement: [TopologicalSpace X] {s : Set Real>=0}
  proof: ha_cont.tendsto.cfcₙ_nnreal hs f ha ha' (ha.self_of_nhdsWithin hx₀) (ha'.self_of_nhdsWithin hx₀)

中文:
定理 ContinuousWithinAt.cfcₙ_nnreal
  结论: [拓扑空间 X] {s : 集合 实数>=0}
  证明: ha_cont.tendsto.cfcₙ_nnreal hs f ha ha' (ha.self_of_nhdsWithin hx₀) (ha'.self_of_nhdsWithin hx₀)

Depends on / 依赖: ContinuousWithinAt, cfc_cont_tac, cfc_zero_tac, ha.self_of_nhdsWithin, ha_cont, ha_cont.tendsto.cfc, self_of_nhdsWithin, tendsto
-/
theorem ContinuousWithinAt.cfcₙ_nnreal [TopologicalSpace X] {s : Set Real>=0}
    (hs : IsCompact s) (f : Real>=0 -> Real>=0) {a : X -> A} {x₀ : X} {t : Set X} (hx₀ : x₀ in t)
    (ha_cont : ContinuousWithinAt a t x₀) (ha : forallᶠ x in 𝓝[t] x₀, quasispectrum Real>=0 (a x) subseteq s)
    (ha' : forallᶠ x in 𝓝[t] x₀, 0 <= a x) (hf : ContinuousOn f s := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) :
    ContinuousWithinAt (fun x => cfcₙ f (a x)) t x₀ :=
  ha_cont.tendsto.cfcₙ_nnreal hs f ha ha' (ha.self_of_nhdsWithin hx₀) (ha'.self_of_nhdsWithin hx₀)

/--
theorem `ContinuousOn.cfcₙ_nnreal` / 定理 `ContinuousOn.cfcₙ_nnreal`

English:
theorem ContinuousOn.cfcₙ_nnreal
  statement: [TopologicalSpace X] {s : X -> Set Real>=0} (f : Real>=0 -> Real>=0) {a : X -> A}
  proof: by
  rw [ContinuousOn] at ha_cont ⊢
  refine fun x hx => (ha_cont x hx).cfcₙ_nnreal (hs x hx) f hx ?_ ?_ (hf x hx)
  all_goals filter_upwards [ha x hx, self_mem_nhdsWithin] with x hx hxt
  exacts [hx, ha' x hxt]

中文:
定理 ContinuousOn.cfcₙ_nnreal
  结论: [拓扑空间 X] {s : X -> 集合 实数>=0} (f : 实数>=0 -> 实数>=0) {a : X -> A}
  证明: by
  rw [ContinuousOn] at ha_cont ⊢
  refine fun x hx => (ha_cont x hx).cfcₙ_nnreal (hs x hx) f hx ?_ ?_ (hf x hx)
  all_goals filter_upwards [ha x hx, self_mem_nhdsWithin] with x hx hxt
  exacts [hx, ha' x hxt]

Depends on / 依赖: ContinuousOn, all_goals, cfc_cont_tac, cfc_zero_tac, exacts, filter_upwards, ha_cont, self_mem_nhdsWithin
-/
theorem ContinuousOn.cfcₙ_nnreal [TopologicalSpace X] {s : X -> Set Real>=0} (f : Real>=0 -> Real>=0) {a : X -> A}
    {t : Set X} (hs : forall x in t, IsCompact (s x)) (ha_cont : ContinuousOn a t)
    (ha : forall x₀ in t, forallᶠ x in 𝓝[t] x₀, quasispectrum Real>=0 (a x) subseteq s x₀) (ha' : forall x in t, 0 <= a x)
    (hf : forall x in t, ContinuousOn f (s x) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac) :
    ContinuousOn (fun x => cfcₙ f (a x)) t := by
  rw [ContinuousOn] at ha_cont ⊢
  refine fun x hx => (ha_cont x hx).cfcₙ_nnreal (hs x hx) f hx ?_ ?_ (hf x hx)
  all_goals filter_upwards [ha x hx, self_mem_nhdsWithin] with x hx hxt
  exacts [hx, ha' x hxt]

/--
theorem `ContinuousOn.cfcₙ_nnreal'` / 定理 `ContinuousOn.cfcₙ_nnreal'`

English:
theorem ContinuousOn.cfcₙ_nnreal'
  statement: [TopologicalSpace X] {s : Set Real>=0} (hs : IsCompact s)
  proof: by
  refine ContinuousOn.cfcₙ_nnreal _ (fun _ _ => hs) ha_cont (fun _ _ => ?_) ha'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact ha x hx

中文:
定理 ContinuousOn.cfcₙ_nnreal'
  结论: [拓扑空间 X] {s : 集合 实数>=0} (hs : 是紧集 s)
  证明: by
  refine ContinuousOn.cfcₙ_nnreal _ (fun _ _ => hs) ha_cont (fun _ _ => ?_) ha'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact ha x hx

Depends on / 依赖: ContinuousOn, ContinuousOn.cfc, cfc_cont_tac, cfc_zero_tac, filter_upwards, ha_cont, self_mem_nhdsWithin
-/
theorem ContinuousOn.cfcₙ_nnreal' [TopologicalSpace X] {s : Set Real>=0} (hs : IsCompact s)
    (f : Real>=0 -> Real>=0) {a : X -> A} {t : Set X} (ha_cont : ContinuousOn a t)
    (ha : forall x in t, quasispectrum Real>=0 (a x) subseteq s) (ha' : forall x in t, 0 <= a x)
    (hf : ContinuousOn f s := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac) :
    ContinuousOn (fun x => cfcₙ f (a x)) t := by
  refine ContinuousOn.cfcₙ_nnreal _ (fun _ _ => hs) ha_cont (fun _ _ => ?_) ha'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact ha x hx

/--
theorem `ContinuousOn.cfcₙ_nnreal_of_mem_nhdsSet` / 定理 `ContinuousOn.cfcₙ_nnreal_of_mem_nhdsSet`

English:
theorem ContinuousOn.cfcₙ_nnreal_of_mem_nhdsSet
  statement: [CompleteSpace A] [TopologicalSpace X] {s : Set Real>=0}
  proof: by
  have hs' := hs
  simp only [nhdsSet_iUnion, mem_iSup] at hs'
  have (x : t) : exists S, IsCompact S ∧ (forallᶠ (x' : A) in 𝓝 (a x), quasispectrum Real>=0 x' subseteq S) ∧ S subseteq s := by
    obtain ⟨S, ⟨hS₁, hS₂⟩, hS₃⟩ :=
.nhdsSet_basis_isCompact.mem_iff.mp (hs' x x.2) quasispectrum.isCompac

中文:
定理 ContinuousOn.cfcₙ_nnreal_of_mem_nhdsSet
  结论: [完备空间 A] [拓扑空间 X] {s : 集合 实数>=0}
  证明: by
  have hs' := hs
  simp only [nhdsSet_iUnion, mem_iSup] at hs'
  have (x : t) : exists S, IsCompact S ∧ (forallᶠ (x' : A) in 𝓝 (a x), quasispectrum Real>=0 x' subseteq S) ∧ S subseteq s := by
    obtain ⟨S, ⟨hS₁, hS₂⟩, hS₃⟩ :=
.nhdsSet_basis_isCompact.mem_iff.mp (hs' x x.2) quasispectrum.isCompac

Depends on / 依赖: ContinuousOn, IsCompact, cfc_cont_tac, cfc_tac, cfc_zero_tac, isCompact_nnreal, mem_iSup, mem_iff, nhdsSet_basis_isCompact, nhdsSet_basis_isCompact.mem_iff.mp, nhdsSet_iUnion, quasispectrum, quasispectrum.isCompact_nnreal, subseteq, upperHemicontinuousAt
-/
theorem ContinuousOn.cfcₙ_nnreal_of_mem_nhdsSet [CompleteSpace A] [TopologicalSpace X] {s : Set Real>=0}
    (f : Real>=0 -> Real>=0) {a : X -> A} {t : Set X} (hs : s in 𝓝ˢ (⋃ x in t, quasispectrum Real>=0 (a x)))
    (ha_cont : ContinuousOn a t) (ha' : forall x in t, 0 <= a x := by cfc_tac)
    (hf : ContinuousOn f s := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac) :
    ContinuousOn (fun x => cfcₙ f (a x)) t := by
  have hs' := hs
  simp only [nhdsSet_iUnion, mem_iSup] at hs'
  have (x : t) : exists S, IsCompact S ∧ (forallᶠ (x' : A) in 𝓝 (a x), quasispectrum Real>=0 x' subseteq S) ∧ S subseteq s := by
    obtain ⟨S, ⟨hS₁, hS₂⟩, hS₃⟩ :=
.nhdsSet_basis_isCompact.mem_iff.mp (hs' x x.2) quasispectrum.isCompact_nnreal (a x)
    refine ⟨S, hS₂, ?_, hS₃⟩
.mono .upperHemicontinuousAt (a x) _ hS₁ exact upperHemicontinuous_quasispectrum_nnreal A
      fun _ => subset_of_mem_nhdsSet
  choose S hS₁ hS₂ hS₃ using this
  classical
  refine ha_cont.cfcₙ_nnreal (s := fun x : X => if hx : x in t then S ⟨x, hx⟩ else ∅) f
    (by simpa +contextual using hS₁) ?_ ha' ?_
  all_goals simp +contextual only [↓reduceDIte]
.eventually hS₂ ⟨x₀, hx₀⟩ · exact fun x₀ hx₀ => ha_cont.continuousWithinAt hx₀
· exact fun x hx => hf.mono hS₃ ⟨x, hx⟩

/--
theorem `Continuous.cfcₙ_nnreal` / 定理 `Continuous.cfcₙ_nnreal`

English:
theorem Continuous.cfcₙ_nnreal
  statement: [TopologicalSpace X] {s : X -> Set Real>=0} (f : Real>=0 -> Real>=0) {a : X -> A}
  proof: by
  rw [← continuousOn_univ] at ha_cont ⊢
  exact ha_cont.cfcₙ_nnreal f (fun x _ => hs x) (fun x _ => by simpa using ha x) (fun x _ => ha' x)

中文:
定理 连续.cfcₙ_nnreal
  结论: [拓扑空间 X] {s : X -> 集合 实数>=0} (f : 实数>=0 -> 实数>=0) {a : X -> A}
  证明: by
  rw [← continuousOn_univ] at ha_cont ⊢
  exact ha_cont.cfcₙ_nnreal f (fun x _ => hs x) (fun x _ => by simpa using ha x) (fun x _ => ha' x)

Depends on / 依赖: Continuous, cfc_cont_tac, cfc_tac, cfc_zero_tac, continuousOn_univ, ha_cont, ha_cont.cfc
-/
theorem Continuous.cfcₙ_nnreal [TopologicalSpace X] {s : X -> Set Real>=0} (f : Real>=0 -> Real>=0) {a : X -> A}
    (ha_cont : Continuous a) (hs : forall x, IsCompact (s x))
    (ha : forall x₀, forallᶠ x in 𝓝 x₀, quasispectrum Real>=0 (a x) subseteq s x₀)
    (hf : forall x, ContinuousOn f (s x) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac)
    (ha' : forall x, 0 <= a x := by cfc_tac) :
    Continuous (fun x => cfcₙ f (a x)) := by
  rw [← continuousOn_univ] at ha_cont ⊢
  exact ha_cont.cfcₙ_nnreal f (fun x _ => hs x) (fun x _ => by simpa using ha x) (fun x _ => ha' x)

/--
theorem `Continuous.cfcₙ_nnreal'` / 定理 `Continuous.cfcₙ_nnreal'`

English:
theorem Continuous.cfcₙ_nnreal'
  statement: [TopologicalSpace X] {s : Set Real>=0} (hs : IsCompact s)
  proof: by
  rw [← continuousOn_univ] at ha_cont ⊢
  exact ha_cont.cfcₙ_nnreal' hs f (fun x _ => ha x) (fun x _ => ha' x)

中文:
定理 连续.cfcₙ_nnreal'
  结论: [拓扑空间 X] {s : 集合 实数>=0} (hs : 是紧集 s)
  证明: by
  rw [← continuousOn_univ] at ha_cont ⊢
  exact ha_cont.cfcₙ_nnreal' hs f (fun x _ => ha x) (fun x _ => ha' x)

Depends on / 依赖: Continuous, cfc_cont_tac, cfc_tac, cfc_zero_tac, continuousOn_univ, ha_cont, ha_cont.cfc
-/
theorem Continuous.cfcₙ_nnreal' [TopologicalSpace X] {s : Set Real>=0} (hs : IsCompact s)
    (f : Real>=0 -> Real>=0) {a : X -> A} (ha_cont : Continuous a) (ha : forall x, quasispectrum Real>=0 (a x) subseteq s)
    (hf : ContinuousOn f s := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac)
    (ha' : forall x, 0 <= a x := by cfc_tac) :
    Continuous (fun x => cfcₙ f (a x)) := by
  rw [← continuousOn_univ] at ha_cont ⊢
  exact ha_cont.cfcₙ_nnreal' hs f (fun x _ => ha x) (fun x _ => ha' x)

/--
theorem `Continuous.cfcₙ_nnreal_of_mem_nhdsSet` / 定理 `Continuous.cfcₙ_nnreal_of_mem_nhdsSet`

English:
theorem Continuous.cfcₙ_nnreal_of_mem_nhdsSet
  statement: [CompleteSpace A] [TopologicalSpace X] {s : Set Real>=0}
  proof: by
  rw [← continuousOn_univ] at ha_cont ⊢
  exact ha_cont.cfcₙ_nnreal_of_mem_nhdsSet f (by simpa) (by simpa)

中文:
定理 连续.cfcₙ_nnreal_of_mem_nhdsSet
  结论: [完备空间 A] [拓扑空间 X] {s : 集合 实数>=0}
  证明: by
  rw [← continuousOn_univ] at ha_cont ⊢
  exact ha_cont.cfcₙ_nnreal_of_mem_nhdsSet f (by simpa) (by simpa)

Depends on / 依赖: Continuous, ContinuousOn, cfc_cont_tac, cfc_tac, cfc_zero_tac, continuousOn_univ, ha_cont, ha_cont.cfc
-/
theorem Continuous.cfcₙ_nnreal_of_mem_nhdsSet [CompleteSpace A] [TopologicalSpace X] {s : Set Real>=0}
    (f : Real>=0 -> Real>=0) {a : X -> A} (hs : s in 𝓝ˢ (⋃ x, quasispectrum Real>=0 (a x)))
    (ha_cont : Continuous a) (ha' : forall x, 0 <= a x := by cfc_tac)
    (hf : ContinuousOn f s := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac) :
    Continuous (fun x => cfcₙ f (a x)) := by
  rw [← continuousOn_univ] at ha_cont ⊢
  exact ha_cont.cfcₙ_nnreal_of_mem_nhdsSet f (by simpa) (by simpa)

end NNReal

end Right

end NonUnital
