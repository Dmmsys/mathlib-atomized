/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Higher differentiability over `ℝ` or `ℂ`
-/

public section

noncomputable section

open Set Fin Filter Function

open scoped NNReal Topology

section Real

/-!
### Results over `ℝ` or `ℂ`
  The results in this section rely on the Mean Value Theorem, and therefore hold only over `ℝ` (and
  its extension fields such as `ℂ`).
-/

variable {n : WithTop Nat∞} {𝕂 : Type*} [RCLike 𝕂] {E' : Type*} [NormedAddCommGroup E']
  [NormedSpace 𝕂 E'] {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕂 F']

/--
theorem `HasFTaylorSeriesUpToOn.hasStrictFDerivAt` / 定理 `HasFTaylorSeriesUpToOn.hasStrictFDerivAt`

English:
theorem HasFTaylorSeriesUpToOn.hasStrictFDerivAt
  statement: {n : WithTop Nat∞}
  proof: hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt (hf.eventually_hasFDerivAt hn hs)
(continuousMultilinearCurryFin1 𝕂 E' F').continuousAt.comp
      (hf.cont 1 <| ENat.one_le_iff_ne_zero_withTop.mpr hn).continuousAt hs

中文:
定理 有FTaylorSeriesUpToOn.hasStrictFDerivAt
  结论: {n : WithTop 自然数∞}
  证明: hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt (hf.eventually_hasFDerivAt hn hs)
(continuousMultilinearCurryFin1 𝕂 E' F').continuousAt.comp
      (hf.cont 1 <| ENat.one_le_iff_ne_zero_withTop.mpr hn).continuousAt hs

Depends on / 依赖: ENat.one_le_iff_ne_zero_withTop.mpr, continuousAt, continuousAt.comp, continuousMultilinearCurryFin1, eventually_hasFDerivAt, hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt, hf.cont, hf.eventually_hasFDerivAt, one_le_iff_ne_zero_withTop
-/
theorem HasFTaylorSeriesUpToOn.hasStrictFDerivAt {n : WithTop Nat∞}
    {s : Set E'} {f : E' -> F'} {x : E'}
    {p : E' -> FormalMultilinearSeries 𝕂 E' F'} (hf : HasFTaylorSeriesUpToOn n f p s) (hn : n != 0)
    (hs : s in 𝓝 x) : HasStrictFDerivAt f ((continuousMultilinearCurryFin1 𝕂 E' F') (p x 1)) x :=
hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt (hf.eventually_hasFDerivAt hn hs)
(continuousMultilinearCurryFin1 𝕂 E' F').continuousAt.comp
      (hf.cont 1 <| ENat.one_le_iff_ne_zero_withTop.mpr hn).continuousAt hs

/--
theorem `ContDiffAt.hasStrictFDerivAt'` / 定理 `ContDiffAt.hasStrictFDerivAt'`

English:
theorem ContDiffAt.hasStrictFDerivAt'
  statement: {f : E' -> F'} {f' : E' ->L[𝕂] F'} {x : E'}
  proof: by
  rcases hf.of_le (ENat.one_le_iff_ne_zero_withTop.mpr hn) 1 le_rfl with ⟨u, H, p, hp⟩
  simp only [nhdsWithin_univ, mem_univ, insert_eq_of_mem] at H
  have := hp.hasStrictFDerivAt one_ne_zero H
  rwa [hf'.unique this.hasFDerivAt]

中文:
定理 ContDiffAt.hasStrictFDerivAt'
  结论: {f : E' -> F'} {f' : E' ->L[𝕂] F'} {x : E'}
  证明: by
  rcases hf.of_le (ENat.one_le_iff_ne_zero_withTop.mpr hn) 1 le_rfl with ⟨u, H, p, hp⟩
  simp only [nhdsWithin_univ, mem_univ, insert_eq_of_mem] at H
  have := hp.hasStrictFDerivAt one_ne_zero H
  rwa [hf'.unique this.hasFDerivAt]

Depends on / 依赖: ENat.one_le_iff_ne_zero_withTop.mpr, hasFDerivAt, hasStrictFDerivAt, hf.of_le, hp.hasStrictFDerivAt, insert_eq_of_mem, le_rfl, mem_univ, nhdsWithin_univ, of_le, one_le_iff_ne_zero_withTop, one_ne_zero, this.hasFDerivAt, unique
-/
theorem ContDiffAt.hasStrictFDerivAt' {f : E' -> F'} {f' : E' ->L[𝕂] F'} {x : E'}
    (hf : ContDiffAt 𝕂 n f x) (hf' : HasFDerivAt f f' x) (hn : n != 0) :
    HasStrictFDerivAt f f' x := by
  rcases hf.of_le (ENat.one_le_iff_ne_zero_withTop.mpr hn) 1 le_rfl with ⟨u, H, p, hp⟩
  simp only [nhdsWithin_univ, mem_univ, insert_eq_of_mem] at H
  have := hp.hasStrictFDerivAt one_ne_zero H
  rwa [hf'.unique this.hasFDerivAt]

/--
theorem `ContDiffAt.hasStrictDerivAt'` / 定理 `ContDiffAt.hasStrictDerivAt'`

English:
theorem ContDiffAt.hasStrictDerivAt'
  statement: {f : 𝕂 -> F'} {f' : F'} {x : 𝕂} (hf : ContDiffAt 𝕂 n f x)
  proof: hf.hasStrictFDerivAt' hf' hn

中文:
定理 ContDiffAt.hasStrictDerivAt'
  结论: {f : 𝕂 -> F'} {f' : F'} {x : 𝕂} (hf : ContDiffAt 𝕂 n f x)
  证明: hf.hasStrictFDerivAt' hf' hn

Depends on / 依赖: hasStrictFDerivAt, hf.hasStrictFDerivAt
-/
theorem ContDiffAt.hasStrictDerivAt' {f : 𝕂 -> F'} {f' : F'} {x : 𝕂} (hf : ContDiffAt 𝕂 n f x)
    (hf' : HasDerivAt f f' x) (hn : n != 0) : HasStrictDerivAt f f' x :=
  hf.hasStrictFDerivAt' hf' hn

/--
theorem `ContDiffAt.hasStrictFDerivAt` / 定理 `ContDiffAt.hasStrictFDerivAt`

English:
theorem ContDiffAt.hasStrictFDerivAt
  given: {f : E' -> F'} {x : E'} (hf : ContDiffAt 𝕂 n f x) (hn : n != 0)
  proof: hf.hasStrictFDerivAt' (hf.differentiableAt hn).hasFDerivAt hn

中文:
定理 ContDiffAt.hasStrictFDerivAt
  条件: {f : E' -> F'} {x : E'} (hf : ContDiffAt 𝕂 n f x) (hn : n != 0)
  证明: hf.hasStrictFDerivAt' (hf.differentiableAt hn).hasFDerivAt hn

Depends on / 依赖: differentiableAt, hasFDerivAt, hasStrictFDerivAt, hf.differentiableAt, hf.hasStrictFDerivAt
-/
theorem ContDiffAt.hasStrictFDerivAt {f : E' -> F'} {x : E'} (hf : ContDiffAt 𝕂 n f x) (hn : n != 0) :
    HasStrictFDerivAt f (fderiv 𝕂 f x) x :=
  hf.hasStrictFDerivAt' (hf.differentiableAt hn).hasFDerivAt hn

/--
theorem `ContDiffAt.hasStrictDerivAt` / 定理 `ContDiffAt.hasStrictDerivAt`

English:
theorem ContDiffAt.hasStrictDerivAt
  given: {f : 𝕂 -> F'} {x : 𝕂} (hf : ContDiffAt 𝕂 n f x) (hn : n != 0)
  proof: (hf.hasStrictFDerivAt hn).hasStrictDerivAt

中文:
定理 ContDiffAt.hasStrictDerivAt
  条件: {f : 𝕂 -> F'} {x : 𝕂} (hf : ContDiffAt 𝕂 n f x) (hn : n != 0)
  证明: (hf.hasStrictFDerivAt hn).hasStrictDerivAt

Depends on / 依赖: hasStrictDerivAt, hasStrictFDerivAt, hf.hasStrictFDerivAt
-/
theorem ContDiffAt.hasStrictDerivAt {f : 𝕂 -> F'} {x : 𝕂} (hf : ContDiffAt 𝕂 n f x) (hn : n != 0) :
    HasStrictDerivAt f (deriv f x) x :=
  (hf.hasStrictFDerivAt hn).hasStrictDerivAt

/--
theorem `ContDiff.hasStrictFDerivAt` / 定理 `ContDiff.hasStrictFDerivAt`

English:
theorem ContDiff.hasStrictFDerivAt
  given: {f : E' -> F'} {x : E'} (hf : ContDiff 𝕂 n f) (hn : n != 0)
  proof: hf.contDiffAt.hasStrictFDerivAt hn

中文:
定理 连续可微.hasStrictFDerivAt
  条件: {f : E' -> F'} {x : E'} (hf : 连续可微 𝕂 n f) (hn : n != 0)
  证明: hf.contDiffAt.hasStrictFDerivAt hn

Depends on / 依赖: contDiffAt, hasStrictFDerivAt, hf.contDiffAt.hasStrictFDerivAt
-/
theorem ContDiff.hasStrictFDerivAt {f : E' -> F'} {x : E'} (hf : ContDiff 𝕂 n f) (hn : n != 0) :
    HasStrictFDerivAt f (fderiv 𝕂 f x) x :=
  hf.contDiffAt.hasStrictFDerivAt hn

/--
theorem `ContDiff.hasStrictDerivAt` / 定理 `ContDiff.hasStrictDerivAt`

English:
theorem ContDiff.hasStrictDerivAt
  given: {f : 𝕂 -> F'} {x : 𝕂} (hf : ContDiff 𝕂 n f) (hn : n != 0)
  proof: hf.contDiffAt.hasStrictDerivAt hn

中文:
定理 连续可微.hasStrictDerivAt
  条件: {f : 𝕂 -> F'} {x : 𝕂} (hf : 连续可微 𝕂 n f) (hn : n != 0)
  证明: hf.contDiffAt.hasStrictDerivAt hn

Depends on / 依赖: contDiffAt, hasStrictDerivAt, hf.contDiffAt.hasStrictDerivAt
-/
theorem ContDiff.hasStrictDerivAt {f : 𝕂 -> F'} {x : 𝕂} (hf : ContDiff 𝕂 n f) (hn : n != 0) :
    HasStrictDerivAt f (deriv f x) x :=
  hf.contDiffAt.hasStrictDerivAt hn

variable {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E] [NormedAddCommGroup F] [NormedSpace Real F] {f : E -> F}
    {p : E -> FormalMultilinearSeries Real E F} {s : Set E} {x : E}

/--
theorem `HasFTaylorSeriesUpToOn.exists_lipschitzOnWith_of_nnnorm_lt` / 定理 `HasFTaylorSeriesUpToOn.exists_lipschitzOnWith_of_nnnorm_lt`

English:
theorem HasFTaylorSeriesUpToOn.exists_lipschitzOnWith_of_nnnorm_lt
  proof: by
  set f' := fun y => continuousMultilinearCurryFin1 Real E F (p y 1)
  have hder : forall y in s, HasFDerivWithinAt f (f' y) s y := fun y hy =>
    (hf.hasFDerivWithinAt one_ne_zero (subset_insert x s hy)).mono (subset_insert x s)
  have hcont : ContinuousWithinAt f' s x :=
    (continuousMultilinearCurryFin1 Real E F).continuousAt.comp_continuousWithinAt
      ((hf.cont _ le_rfl _ (mem_insert _ _)).mono (subset_insert x s))
  replace hK : ‖f' x‖₊ < K := by simpa only [f', LinearIsometryEquiv.nnnorm_map]
  exact
    hs.exists_nhdsWithin_lipschitzOnWith_of_hasFDerivWithinAt_of_nnnorm_lt
      (eventually_nhdsWithin_iff.2 <| Eventually.of_forall hder) hcont K hK

中文:
定理 有FTaylorSeriesUpToOn.存在_lipschitzOnWith_of_nnnorm_lt
  证明: by
  set f' := fun y => continuousMultilinearCurryFin1 Real E F (p y 1)
  have hder : forall y in s, HasFDerivWithinAt f (f' y) s y := fun y hy =>
    (hf.hasFDerivWithinAt one_ne_zero (subset_insert x s hy)).mono (subset_insert x s)
  have hcont : ContinuousWithinAt f' s x :=
    (continuousMultilinearCurryFin1 Real E F).continuousAt.comp_continuousWithinAt
      ((hf.cont _ le_rfl _ (mem_insert _ _)).mono (subset_insert x s))
  replace hK : ‖f' x‖₊ < K := by simpa only [f', LinearIsometryEquiv.nnnorm_map]
  exact
    hs.exists_nhdsWithin_lipschitzOnWith_of_hasFDerivWithinAt_of_nnnorm_lt
      (eventually_nhdsWithin_iff.2 <| Eventually.of_forall hder) hcont K hK

Depends on / 依赖: ContinuousWithinAt, HasFDerivWithinAt, LinearIsometryEquiv, LinearIsometryEquiv.nnnorm_map, comp_continuousWithinAt, continuousAt, continuousAt.comp_continuousWithinAt, continuousMultilinearCurryFin1, hasFDerivWithinAt, hf.cont, hf.hasFDerivWithinAt, le_rfl, mem_insert, nnnorm_map, one_ne_zero, replace, subset_insert
-/
theorem HasFTaylorSeriesUpToOn.exists_lipschitzOnWith_of_nnnorm_lt
    (hf : HasFTaylorSeriesUpToOn 1 f p (insert x s)) (hs : Convex Real s) (K : Real>=0)
    (hK : ‖p x 1‖₊ < K) : exists t in 𝓝[s] x, LipschitzOnWith K f t := by
  set f' := fun y => continuousMultilinearCurryFin1 Real E F (p y 1)
  have hder : forall y in s, HasFDerivWithinAt f (f' y) s y := fun y hy =>
    (hf.hasFDerivWithinAt one_ne_zero (subset_insert x s hy)).mono (subset_insert x s)
  have hcont : ContinuousWithinAt f' s x :=
    (continuousMultilinearCurryFin1 Real E F).continuousAt.comp_continuousWithinAt
      ((hf.cont _ le_rfl _ (mem_insert _ _)).mono (subset_insert x s))
  replace hK : ‖f' x‖₊ < K := by simpa only [f', LinearIsometryEquiv.nnnorm_map]
  exact
    hs.exists_nhdsWithin_lipschitzOnWith_of_hasFDerivWithinAt_of_nnnorm_lt
      (eventually_nhdsWithin_iff.2 <| Eventually.of_forall hder) hcont K hK

/--
theorem `HasFTaylorSeriesUpToOn.exists_lipschitzOnWith` / 定理 `HasFTaylorSeriesUpToOn.exists_lipschitzOnWith`

English:
theorem HasFTaylorSeriesUpToOn.exists_lipschitzOnWith
  proof: (exists_gt _).imp hf.exists_lipschitzOnWith_of_nnnorm_lt hs

中文:
定理 有FTaylorSeriesUpToOn.存在_lipschitzOnWith
  证明: (exists_gt _).imp hf.exists_lipschitzOnWith_of_nnnorm_lt hs

Depends on / 依赖: exists_gt, exists_lipschitzOnWith_of_nnnorm_lt, hf.exists_lipschitzOnWith_of_nnnorm_lt
-/
theorem HasFTaylorSeriesUpToOn.exists_lipschitzOnWith
    (hf : HasFTaylorSeriesUpToOn 1 f p (insert x s)) (hs : Convex Real s) :
    exists K, exists t in 𝓝[s] x, LipschitzOnWith K f t :=
(exists_gt _).imp hf.exists_lipschitzOnWith_of_nnnorm_lt hs

/--
theorem `ContDiffWithinAt.exists_lipschitzOnWith` / 定理 `ContDiffWithinAt.exists_lipschitzOnWith`

English:
theorem ContDiffWithinAt.exists_lipschitzOnWith
  proof: by
  rcases hf 1 le_rfl with ⟨t, hst, p, hp⟩
  rcases Metric.mem_nhdsWithin_iff.mp hst with ⟨ε, ε0, hε⟩
  replace hp : HasFTaylorSeriesUpToOn 1 f p (Metric.ball x ε inter insert x s) := hp.mono hε
  clear hst hε t
  rw [← insert_eq_of_mem (Metric.mem_ball_self ε0)]; rw [← insert_inter_distrib] at hp
  rcases hp.exists_lipschitzOnWith ((convex_ball _ _).inter hs) with ⟨K, t, hst, hft⟩
  rw [inter_comm]; rw [← nhdsWithin_restrict' _ (Metric.ball_mem_nhds _ ε0)] at hst
  exact ⟨K, t, hst, hft⟩

中文:
定理 ContDiffWithinAt.存在_lipschitzOnWith
  证明: by
  rcases hf 1 le_rfl with ⟨t, hst, p, hp⟩
  rcases Metric.mem_nhdsWithin_iff.mp hst with ⟨ε, ε0, hε⟩
  replace hp : HasFTaylorSeriesUpToOn 1 f p (Metric.ball x ε inter insert x s) := hp.mono hε
  clear hst hε t
  rw [← insert_eq_of_mem (Metric.mem_ball_self ε0)]; rw [← insert_inter_distrib] at hp
  rcases hp.exists_lipschitzOnWith ((convex_ball _ _).inter hs) with ⟨K, t, hst, hft⟩
  rw [inter_comm]; rw [← nhdsWithin_restrict' _ (Metric.ball_mem_nhds _ ε0)] at hst
  exact ⟨K, t, hst, hft⟩

Depends on / 依赖: HasFTaylorSeriesUpToOn, Metric, Metric.ball, Metric.ball_mem_nhds, Metric.mem_ball_self, Metric.mem_nhdsWithin_iff.mp, ball_mem_nhds, convex_ball, exists_lipschitzOnWith, hp.exists_lipschitzOnWith, hp.mono, insert, insert_eq_of_mem, insert_inter_distrib, inter_comm, le_rfl, mem_ball_self, mem_nhdsWithin_iff, nhdsWithin_restrict, replace
-/
theorem ContDiffWithinAt.exists_lipschitzOnWith
    (hf : ContDiffWithinAt Real 1 f s x) (hs : Convex Real s) :
    exists K : Real>=0, exists t in 𝓝[s] x, LipschitzOnWith K f t := by
  rcases hf 1 le_rfl with ⟨t, hst, p, hp⟩
  rcases Metric.mem_nhdsWithin_iff.mp hst with ⟨ε, ε0, hε⟩
  replace hp : HasFTaylorSeriesUpToOn 1 f p (Metric.ball x ε inter insert x s) := hp.mono hε
  clear hst hε t
  rw [← insert_eq_of_mem (Metric.mem_ball_self ε0)]; rw [← insert_inter_distrib] at hp
  rcases hp.exists_lipschitzOnWith ((convex_ball _ _).inter hs) with ⟨K, t, hst, hft⟩
  rw [inter_comm]; rw [← nhdsWithin_restrict' _ (Metric.ball_mem_nhds _ ε0)] at hst
  exact ⟨K, t, hst, hft⟩

/--
theorem `ContDiffAt.exists_lipschitzOnWith_of_nnnorm_lt` / 定理 `ContDiffAt.exists_lipschitzOnWith_of_nnnorm_lt`

English:
theorem ContDiffAt.exists_lipschitzOnWith_of_nnnorm_lt
  statement: {f : E' -> F'} {x : E'}
  proof: (hf.hasStrictFDerivAt one_ne_zero).exists_lipschitzOnWith_of_nnnorm_lt K hK

中文:
定理 ContDiffAt.存在_lipschitzOnWith_of_nnnorm_lt
  结论: {f : E' -> F'} {x : E'}
  证明: (hf.hasStrictFDerivAt one_ne_zero).exists_lipschitzOnWith_of_nnnorm_lt K hK

Depends on / 依赖: exists_lipschitzOnWith_of_nnnorm_lt, hasStrictFDerivAt, hf.hasStrictFDerivAt, one_ne_zero
-/
theorem ContDiffAt.exists_lipschitzOnWith_of_nnnorm_lt {f : E' -> F'} {x : E'}
    (hf : ContDiffAt 𝕂 1 f x) (K : Real>=0) (hK : ‖fderiv 𝕂 f x‖₊ < K) :
    exists t in 𝓝 x, LipschitzOnWith K f t :=
  (hf.hasStrictFDerivAt one_ne_zero).exists_lipschitzOnWith_of_nnnorm_lt K hK

/--
theorem `ContDiffAt.exists_lipschitzOnWith` / 定理 `ContDiffAt.exists_lipschitzOnWith`

English:
theorem ContDiffAt.exists_lipschitzOnWith
  given: {f : E' -> F'} {x : E'} (hf : ContDiffAt 𝕂 1 f x)
  proof: (hf.hasStrictFDerivAt one_ne_zero).exists_lipschitzOnWith

中文:
定理 ContDiffAt.存在_lipschitzOnWith
  条件: {f : E' -> F'} {x : E'} (hf : ContDiffAt 𝕂 1 f x)
  证明: (hf.hasStrictFDerivAt one_ne_zero).exists_lipschitzOnWith

Depends on / 依赖: exists_lipschitzOnWith, hasStrictFDerivAt, hf.hasStrictFDerivAt, one_ne_zero
-/
theorem ContDiffAt.exists_lipschitzOnWith {f : E' -> F'} {x : E'} (hf : ContDiffAt 𝕂 1 f x) :
    exists K, exists t in 𝓝 x, LipschitzOnWith K f t :=
  (hf.hasStrictFDerivAt one_ne_zero).exists_lipschitzOnWith

/--
lemma `ContDiffOn.locallyLipschitzOn` / 引理 `ContDiffOn.locallyLipschitzOn`

English:
lemma ContDiffOn.locallyLipschitzOn
  statement: {f : E -> F} {s : Set E} (hs : Convex Real s)
  proof: by
  intro x hx
  obtain ⟨K, t, ht, hf⟩ := ContDiffWithinAt.exists_lipschitzOnWith (hf x hx) hs
  use K, t

中文:
引理 ContDiffOn.locallyLipschitzOn
  结论: {f : E -> F} {s : 集合 E} (hs : 凸 实数 s)
  证明: by
  intro x hx
  obtain ⟨K, t, ht, hf⟩ := ContDiffWithinAt.exists_lipschitzOnWith (hf x hx) hs
  use K, t

Depends on / 依赖: ContDiffWithinAt, ContDiffWithinAt.exists_lipschitzOnWith, exists_lipschitzOnWith
-/
lemma ContDiffOn.locallyLipschitzOn {f : E -> F} {s : Set E} (hs : Convex Real s)
    (hf : ContDiffOn Real 1 f s) : LocallyLipschitzOn s f := by
  intro x hx
  obtain ⟨K, t, ht, hf⟩ := ContDiffWithinAt.exists_lipschitzOnWith (hf x hx) hs
  use K, t

/--
lemma `ContDiff.locallyLipschitz` / 引理 `ContDiff.locallyLipschitz`

English:
lemma ContDiff.locallyLipschitz
  given: {f : E' -> F'} (hf : ContDiff 𝕂 1 f)
  statement: LocallyLipschitz f
  proof: by
  intro x
  rcases hf.contDiffAt.exists_lipschitzOnWith with ⟨K, t, ht, hf⟩
  use K, t

中文:
引理 连续可微.locallyLipschitz
  条件: {f : E' -> F'} (hf : 连续可微 𝕂 1 f)
  结论: LocallyLipschitz f
  证明: by
  intro x
  rcases hf.contDiffAt.exists_lipschitzOnWith with ⟨K, t, ht, hf⟩
  use K, t

Depends on / 依赖: contDiffAt, exists_lipschitzOnWith, hf.contDiffAt.exists_lipschitzOnWith
-/
lemma ContDiff.locallyLipschitz {f : E' -> F'} (hf : ContDiff 𝕂 1 f) : LocallyLipschitz f := by
  intro x
  rcases hf.contDiffAt.exists_lipschitzOnWith with ⟨K, t, ht, hf⟩
  use K, t

/--
theorem `ContDiffOn.exists_lipschitzOnWith` / 定理 `ContDiffOn.exists_lipschitzOnWith`

English:
theorem ContDiffOn.exists_lipschitzOnWith
  statement: {s : Set E} {f : E -> F} {n} (hf : ContDiffOn Real n f s)
  proof: by
  apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hs'
  exact (hf.of_le <| ENat.one_le_iff_ne_zero_withTop.2 hn).locallyLipschitzOn hs

中文:
定理 ContDiffOn.存在_lipschitzOnWith
  结论: {s : 集合 E} {f : E -> F} {n} (hf : ContDiffOn 实数 n f s)
  证明: by
  apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hs'
  exact (hf.of_le <| ENat.one_le_iff_ne_zero_withTop.2 hn).locallyLipschitzOn hs

Depends on / 依赖: ENat.one_le_iff_ne_zero_withTop, LocallyLipschitzOn, LocallyLipschitzOn.exists_lipschitzOnWith_of_compact, exists_lipschitzOnWith_of_compact, hf.of_le, locallyLipschitzOn, of_le, one_le_iff_ne_zero_withTop
-/
theorem ContDiffOn.exists_lipschitzOnWith {s : Set E} {f : E -> F} {n} (hf : ContDiffOn Real n f s)
    (hn : n != 0) (hs : Convex Real s) (hs' : IsCompact s) :
    exists K, LipschitzOnWith K f s := by
  apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hs'
  exact (hf.of_le <| ENat.one_le_iff_ne_zero_withTop.2 hn).locallyLipschitzOn hs

/--
theorem `ContDiff.lipschitzWith_of_hasCompactSupport` / 定理 `ContDiff.lipschitzWith_of_hasCompactSupport`

English:
theorem ContDiff.lipschitzWith_of_hasCompactSupport
  statement: {f : E' -> F'}
  proof: by
  obtain ⟨C, hC⟩ := (hf.fderiv 𝕂).exists_bound_of_continuous (h'f.continuous_fderiv hn)
  refine ⟨.mk (max C 0) (le_max_right _ _), ?_⟩
  apply lipschitzWith_of_nnnorm_fderiv_le (h'f.differentiable hn) (fun x => ?_)
  simp [← NNReal.coe_le_coe, hC x]

中文:
定理 连续可微.lipschitzWith_of_hasCompactSupport
  结论: {f : E' -> F'}
  证明: by
  obtain ⟨C, hC⟩ := (hf.fderiv 𝕂).exists_bound_of_continuous (h'f.continuous_fderiv hn)
  refine ⟨.mk (max C 0) (le_max_right _ _), ?_⟩
  apply lipschitzWith_of_nnnorm_fderiv_le (h'f.differentiable hn) (fun x => ?_)
  simp [← NNReal.coe_le_coe, hC x]

Depends on / 依赖: NNReal, NNReal.coe_le_coe, coe_le_coe, continuous_fderiv, differentiable, exists_bound_of_continuous, f.continuous_fderiv, f.differentiable, fderiv, hf.fderiv, le_max_right, lipschitzWith_of_nnnorm_fderiv_le
-/
theorem ContDiff.lipschitzWith_of_hasCompactSupport {f : E' -> F'}
    (hf : HasCompactSupport f) (h'f : ContDiff 𝕂 n f) (hn : n != 0) :
    exists C, LipschitzWith C f := by
  obtain ⟨C, hC⟩ := (hf.fderiv 𝕂).exists_bound_of_continuous (h'f.continuous_fderiv hn)
  refine ⟨.mk (max C 0) (le_max_right _ _), ?_⟩
  apply lipschitzWith_of_nnnorm_fderiv_le (h'f.differentiable hn) (fun x => ?_)
  simp [← NNReal.coe_le_coe, hC x]

end Real
