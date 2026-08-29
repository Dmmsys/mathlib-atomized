/-
Copyright (c) 2025 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Integral curves of vector fields on a normed vector space

Let `E` be a normed vector space and `v : ℝ → E → E` be a time-dependent vector field on `E`.
An integral curve of `v` is a function `γ : ℝ → E` such that the derivative of `γ` at `t` equals
`v t (γ t)`. The integral curve may only be defined for all `t` within some subset of `ℝ`.

## Main definitions

Let `v : ℝ → E → E` be a time-dependent vector field on `E`, and let `γ : ℝ → E`.
* `IsIntegralCurve γ v`: `γ t` is tangent to `v t (γ t)` for all `t : ℝ`. That is, `γ` is a global
  integral curve of `v`.
* `IsIntegralCurveOn γ v s`: `γ t` is tangent to `v t (γ t)` for all `t ∈ s`, where `s : Set ℝ`.
* `IsIntegralCurveAt γ v t₀`: `γ t` is tangent to `v t (γ t)` for all `t` in some open interval
  around `t₀`. That is, `γ` is a local integral curve of `v`.

## TODO

* Implement `IsIntegralCurveWithinAt`.

## Tags

integral curve, vector field
-/

@[expose] public section

open scoped Topology

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]

/--
Definition of `IsIntegralCurveOn` / `IsIntegralCurveOn` 的定义

English:
definition IsIntegralCurveOn
  signature: (γ : Real -> E) (v : Real -> E -> E) (s : Set Real)
  body: forall t in s, HasDerivWithinAt γ (v t (γ t)) s t

中文:
定义 Is整数egralCurveOn
  签名: (γ : 实数 -> E) (v : 实数 -> E -> E) (s : 集合 实数)
  定义体: forall t in s, HasDerivWithinAt γ (v t (γ t)) s t

Depends on / 依赖: HasDerivWithinAt
-/
def IsIntegralCurveOn (γ : Real -> E) (v : Real -> E -> E) (s : Set Real) : Prop :=
  forall t in s, HasDerivWithinAt γ (v t (γ t)) s t

/--
Definition of `IsIntegralCurveAt` / `IsIntegralCurveAt` 的定义

English:
definition IsIntegralCurveAt
  signature: (γ : Real -> E) (v : Real -> E -> E) (t₀ : Real)
  body: forallᶠ t in 𝓝 t₀, HasDerivAt γ (v t (γ t)) t

中文:
定义 Is整数egralCurveAt
  签名: (γ : 实数 -> E) (v : 实数 -> E -> E) (t₀ : 实数)
  定义体: forallᶠ t in 𝓝 t₀, HasDerivAt γ (v t (γ t)) t

Depends on / 依赖: HasDerivAt
-/
def IsIntegralCurveAt (γ : Real -> E) (v : Real -> E -> E) (t₀ : Real) : Prop :=
  forallᶠ t in 𝓝 t₀, HasDerivAt γ (v t (γ t)) t

/--
Definition of `IsIntegralCurve` / `IsIntegralCurve` 的定义

English:
definition IsIntegralCurve
  signature: (γ : Real -> E) (v : Real -> E -> E)
  body: forall t : Real, HasDerivAt γ (v t (γ t)) t

中文:
定义 Is整数egralCurve
  签名: (γ : 实数 -> E) (v : 实数 -> E -> E)
  定义体: forall t : Real, HasDerivAt γ (v t (γ t)) t

Depends on / 依赖: HasDerivAt
-/
def IsIntegralCurve (γ : Real -> E) (v : Real -> E -> E) : Prop :=
  forall t : Real, HasDerivAt γ (v t (γ t)) t

variable {γ γ' : Real -> E} {v : Real -> E -> E} {s s' : Set Real} {t₀ : Real}

/--
lemma `IsIntegralCurve.isIntegralCurveOn` / 引理 `IsIntegralCurve.isIntegralCurveOn`

English:
lemma IsIntegralCurve.isIntegralCurveOn
  given: (h : IsIntegralCurve γ v) (s : Set Real)
  proof: fun t _ => (h t).hasDerivWithinAt

中文:
引理 Is整数egralCurve.is整数egralCurveOn
  条件: (h : Is整数egralCurve γ v) (s : 集合 实数)
  证明: fun t _ => (h t).hasDerivWithinAt

Depends on / 依赖: hasDerivWithinAt
-/
lemma IsIntegralCurve.isIntegralCurveOn (h : IsIntegralCurve γ v) (s : Set Real) :
    IsIntegralCurveOn γ v s := fun t _ => (h t).hasDerivWithinAt

/--
lemma `isIntegralCurveOn_univ` / 引理 `isIntegralCurveOn_univ`

English:
lemma isIntegralCurveOn_univ
  proof: ⟨fun h t => (h t (mem_univ _)).hasDerivAt Filter.univ_mem, fun h => h.isIntegralCurveOn _⟩

中文:
引理 is整数egralCurveOn_univ
  证明: ⟨fun h t => (h t (mem_univ _)).hasDerivAt Filter.univ_mem, fun h => h.isIntegralCurveOn _⟩

Depends on / 依赖: Filter, Filter.univ_mem, h.isIntegralCurveOn, hasDerivAt, isIntegralCurveOn, mem_univ, univ_mem
-/
lemma isIntegralCurveOn_univ :
    IsIntegralCurveOn γ v univ ↔ IsIntegralCurve γ v :=
  ⟨fun h t => (h t (mem_univ _)).hasDerivAt Filter.univ_mem, fun h => h.isIntegralCurveOn _⟩

/--
lemma `isIntegralCurveAt_iff_exists_mem_nhds` / 引理 `isIntegralCurveAt_iff_exists_mem_nhds`

English:
lemma isIntegralCurveAt_iff_exists_mem_nhds
  proof: by
  rw [IsIntegralCurveAt]; rw [Filter.eventually_iff_exists_mem]
  refine ⟨fun ⟨s, hs, h⟩ => ⟨s, hs, fun t ht => (h t ht).hasDerivWithinAt⟩, ?_⟩
  intro ⟨s, hs, h⟩
  rw [mem_nhds_iff] at hs
  obtain ⟨s', h₁, h₂, h₃⟩ := hs
  refine ⟨s', h₂.mem_nhds h₃, ?_⟩
  intro t ht
  apply (h t (h₁ ht)).hasDerivAt
  rw [mem_nhds_iff]
  exact ⟨s', h₁, h₂, ht⟩

中文:
引理 is整数egralCurveAt_iff_存在_mem_nhds
  证明: by
  rw [IsIntegralCurveAt]; rw [Filter.eventually_iff_exists_mem]
  refine ⟨fun ⟨s, hs, h⟩ => ⟨s, hs, fun t ht => (h t ht).hasDerivWithinAt⟩, ?_⟩
  intro ⟨s, hs, h⟩
  rw [mem_nhds_iff] at hs
  obtain ⟨s', h₁, h₂, h₃⟩ := hs
  refine ⟨s', h₂.mem_nhds h₃, ?_⟩
  intro t ht
  apply (h t (h₁ ht)).hasDerivAt
  rw [mem_nhds_iff]
  exact ⟨s', h₁, h₂, ht⟩

Depends on / 依赖: Filter, Filter.eventually_iff_exists_mem, IsIntegralCurveAt, eventually_iff_exists_mem, hasDerivAt, hasDerivWithinAt, mem_nhds, mem_nhds_iff
-/
lemma isIntegralCurveAt_iff_exists_mem_nhds :
    IsIntegralCurveAt γ v t₀ ↔ exists s in 𝓝 t₀, IsIntegralCurveOn γ v s := by
  rw [IsIntegralCurveAt]; rw [Filter.eventually_iff_exists_mem]
  refine ⟨fun ⟨s, hs, h⟩ => ⟨s, hs, fun t ht => (h t ht).hasDerivWithinAt⟩, ?_⟩
  intro ⟨s, hs, h⟩
  rw [mem_nhds_iff] at hs
  obtain ⟨s', h₁, h₂, h₃⟩ := hs
  refine ⟨s', h₂.mem_nhds h₃, ?_⟩
  intro t ht
  apply (h t (h₁ ht)).hasDerivAt
  rw [mem_nhds_iff]
  exact ⟨s', h₁, h₂, ht⟩

/--
lemma `isIntegralCurveAt_iff_exists_pos` / 引理 `isIntegralCurveAt_iff_exists_pos`

English:
lemma isIntegralCurveAt_iff_exists_pos
  proof: by
  rw [IsIntegralCurveAt]; rw [Metric.eventually_nhds_iff_ball]
  congrm exists ε > 0, forall (y : Real) (hy : y in Metric.ball t₀ ε), ?_
  exact ⟨HasDerivAt.hasDerivWithinAt, fun h => h.hasDerivAt (Metric.isOpen_ball.mem_nhds hy)⟩

中文:
引理 is整数egralCurveAt_iff_存在_pos
  证明: by
  rw [IsIntegralCurveAt]; rw [Metric.eventually_nhds_iff_ball]
  congrm exists ε > 0, forall (y : Real) (hy : y in Metric.ball t₀ ε), ?_
  exact ⟨HasDerivAt.hasDerivWithinAt, fun h => h.hasDerivAt (Metric.isOpen_ball.mem_nhds hy)⟩

Depends on / 依赖: HasDerivAt, HasDerivAt.hasDerivWithinAt, IsIntegralCurveAt, Metric, Metric.ball, Metric.eventually_nhds_iff_ball, Metric.isOpen_ball.mem_nhds, congrm, eventually_nhds_iff_ball, h.hasDerivAt, hasDerivAt, hasDerivWithinAt, isOpen_ball, mem_nhds
-/
lemma isIntegralCurveAt_iff_exists_pos :
    IsIntegralCurveAt γ v t₀ ↔ exists ε > 0, IsIntegralCurveOn γ v (Metric.ball t₀ ε) := by
  rw [IsIntegralCurveAt]; rw [Metric.eventually_nhds_iff_ball]
  congrm exists ε > 0, forall (y : Real) (hy : y in Metric.ball t₀ ε), ?_
  exact ⟨HasDerivAt.hasDerivWithinAt, fun h => h.hasDerivAt (Metric.isOpen_ball.mem_nhds hy)⟩

/--
lemma `IsIntegralCurve.isIntegralCurveAt` / 引理 `IsIntegralCurve.isIntegralCurveAt`

English:
lemma IsIntegralCurve.isIntegralCurveAt
  given: (h : IsIntegralCurve γ v) (t : Real)
  proof: isIntegralCurveAt_iff_exists_mem_nhds.mpr
    ⟨univ, Filter.univ_mem, fun t _ => (h t).hasDerivWithinAt⟩

中文:
引理 Is整数egralCurve.is整数egralCurveAt
  条件: (h : Is整数egralCurve γ v) (t : 实数)
  证明: isIntegralCurveAt_iff_exists_mem_nhds.mpr
    ⟨univ, Filter.univ_mem, fun t _ => (h t).hasDerivWithinAt⟩

Depends on / 依赖: Filter, Filter.univ_mem, hasDerivWithinAt, isIntegralCurveAt_iff_exists_mem_nhds, isIntegralCurveAt_iff_exists_mem_nhds.mpr, univ_mem
-/
lemma IsIntegralCurve.isIntegralCurveAt (h : IsIntegralCurve γ v) (t : Real) :
    IsIntegralCurveAt γ v t :=
  isIntegralCurveAt_iff_exists_mem_nhds.mpr
    ⟨univ, Filter.univ_mem, fun t _ => (h t).hasDerivWithinAt⟩

/--
lemma `isIntegralCurve_iff_isIntegralCurveAt` / 引理 `isIntegralCurve_iff_isIntegralCurveAt`

English:
lemma isIntegralCurve_iff_isIntegralCurveAt
  proof: ⟨fun h => h.isIntegralCurveAt, fun h t => by
    obtain ⟨s, hs, h⟩ := isIntegralCurveAt_iff_exists_mem_nhds.mp (h t)
.hasDerivAt hs⟩ exact h t (mem_of_mem_nhds hs)

中文:
引理 is整数egralCurve_iff_is整数egralCurveAt
  证明: ⟨fun h => h.isIntegralCurveAt, fun h t => by
    obtain ⟨s, hs, h⟩ := isIntegralCurveAt_iff_exists_mem_nhds.mp (h t)
.hasDerivAt hs⟩ exact h t (mem_of_mem_nhds hs)

Depends on / 依赖: h.isIntegralCurveAt, hasDerivAt, isIntegralCurveAt, isIntegralCurveAt_iff_exists_mem_nhds, isIntegralCurveAt_iff_exists_mem_nhds.mp, mem_of_mem_nhds
-/
lemma isIntegralCurve_iff_isIntegralCurveAt :
    IsIntegralCurve γ v ↔ forall t : Real, IsIntegralCurveAt γ v t :=
  ⟨fun h => h.isIntegralCurveAt, fun h t => by
    obtain ⟨s, hs, h⟩ := isIntegralCurveAt_iff_exists_mem_nhds.mp (h t)
.hasDerivAt hs⟩ exact h t (mem_of_mem_nhds hs)

/--
lemma `IsIntegralCurveOn.mono` / 引理 `IsIntegralCurveOn.mono`

English:
lemma IsIntegralCurveOn.mono
  given: (h : IsIntegralCurveOn γ v s) (hs : s' subseteq s)
  proof: fun t ht => h t (hs ht)

中文:
引理 Is整数egralCurveOn.mono
  条件: (h : Is整数egralCurveOn γ v s) (hs : s' subseteq s)
  证明: fun t ht => h t (hs ht)
-/
lemma IsIntegralCurveOn.mono (h : IsIntegralCurveOn γ v s) (hs : s' subseteq s) :
.mono hs IsIntegralCurveOn γ v s' := fun t ht => h t (hs ht)

/--
lemma `IsIntegralCurveAt.hasDerivAt` / 引理 `IsIntegralCurveAt.hasDerivAt`

English:
lemma IsIntegralCurveAt.hasDerivAt
  given: (h : IsIntegralCurveAt γ v t₀)
  proof: have ⟨_, hs, h⟩ := isIntegralCurveAt_iff_exists_mem_nhds.mp h
.hasDerivAt hs h t₀ (mem_of_mem_nhds hs)

中文:
引理 Is整数egralCurveAt.hasDerivAt
  条件: (h : Is整数egralCurveAt γ v t₀)
  证明: have ⟨_, hs, h⟩ := isIntegralCurveAt_iff_exists_mem_nhds.mp h
.hasDerivAt hs h t₀ (mem_of_mem_nhds hs)

Depends on / 依赖: hasDerivAt, isIntegralCurveAt_iff_exists_mem_nhds, isIntegralCurveAt_iff_exists_mem_nhds.mp, mem_of_mem_nhds
-/
lemma IsIntegralCurveAt.hasDerivAt (h : IsIntegralCurveAt γ v t₀) :
    HasDerivAt γ (v t₀ (γ t₀)) t₀ :=
  have ⟨_, hs, h⟩ := isIntegralCurveAt_iff_exists_mem_nhds.mp h
.hasDerivAt hs h t₀ (mem_of_mem_nhds hs)

/--
lemma `IsIntegralCurveOn.isIntegralCurveAt` / 引理 `IsIntegralCurveOn.isIntegralCurveAt`

English:
lemma IsIntegralCurveOn.isIntegralCurveAt
  given: (h : IsIntegralCurveOn γ v s) (hs : s in 𝓝 t₀)
  proof: isIntegralCurveAt_iff_exists_mem_nhds.mpr ⟨s, hs, h⟩

中文:
引理 Is整数egralCurveOn.is整数egralCurveAt
  条件: (h : Is整数egralCurveOn γ v s) (hs : s in 𝓝 t₀)
  证明: isIntegralCurveAt_iff_exists_mem_nhds.mpr ⟨s, hs, h⟩

Depends on / 依赖: isIntegralCurveAt_iff_exists_mem_nhds, isIntegralCurveAt_iff_exists_mem_nhds.mpr
-/
lemma IsIntegralCurveOn.isIntegralCurveAt (h : IsIntegralCurveOn γ v s) (hs : s in 𝓝 t₀) :
    IsIntegralCurveAt γ v t₀ := isIntegralCurveAt_iff_exists_mem_nhds.mpr ⟨s, hs, h⟩

/--
lemma `IsIntegralCurveAt.isIntegralCurveOn` / 引理 `IsIntegralCurveAt.isIntegralCurveOn`

English:
lemma IsIntegralCurveAt.isIntegralCurveOn
  given: (h : forall t in s, IsIntegralCurveAt γ v t)
  proof: by
  intros t ht
  obtain ⟨s', hs', h⟩ := Filter.eventually_iff_exists_mem.mp (h t ht)
.hasDerivWithinAt exact h _ (mem_of_mem_nhds hs')

中文:
引理 Is整数egralCurveAt.is整数egralCurveOn
  条件: (h : 对任意 t in s, Is整数egralCurveAt γ v t)
  证明: by
  intros t ht
  obtain ⟨s', hs', h⟩ := Filter.eventually_iff_exists_mem.mp (h t ht)
.hasDerivWithinAt exact h _ (mem_of_mem_nhds hs')

Depends on / 依赖: Filter, Filter.eventually_iff_exists_mem.mp, eventually_iff_exists_mem, hasDerivWithinAt, intros, mem_of_mem_nhds
-/
lemma IsIntegralCurveAt.isIntegralCurveOn (h : forall t in s, IsIntegralCurveAt γ v t) :
    IsIntegralCurveOn γ v s := by
  intros t ht
  obtain ⟨s', hs', h⟩ := Filter.eventually_iff_exists_mem.mp (h t ht)
.hasDerivWithinAt exact h _ (mem_of_mem_nhds hs')

/--
lemma `isIntegralCurveOn_iff_isIntegralCurveAt` / 引理 `isIntegralCurveOn_iff_isIntegralCurveAt`

English:
lemma isIntegralCurveOn_iff_isIntegralCurveAt
  given: (hs : IsOpen s)
  proof: ⟨fun h _ ht => h.isIntegralCurveAt (hs.mem_nhds ht), IsIntegralCurveAt.isIntegralCurveOn⟩

中文:
引理 is整数egralCurveOn_iff_is整数egralCurveAt
  条件: (hs : 是开集 s)
  证明: ⟨fun h _ ht => h.isIntegralCurveAt (hs.mem_nhds ht), IsIntegralCurveAt.isIntegralCurveOn⟩

Depends on / 依赖: IsIntegralCurveAt, IsIntegralCurveAt.isIntegralCurveOn, h.isIntegralCurveAt, hs.mem_nhds, isIntegralCurveAt, isIntegralCurveOn, mem_nhds
-/
lemma isIntegralCurveOn_iff_isIntegralCurveAt (hs : IsOpen s) :
    IsIntegralCurveOn γ v s ↔ forall t in s, IsIntegralCurveAt γ v t :=
  ⟨fun h _ ht => h.isIntegralCurveAt (hs.mem_nhds ht), IsIntegralCurveAt.isIntegralCurveOn⟩

/--
lemma `IsIntegralCurveOn.continuousWithinAt` / 引理 `IsIntegralCurveOn.continuousWithinAt`

English:
lemma IsIntegralCurveOn.continuousWithinAt
  given: (hγ : IsIntegralCurveOn γ v s) (ht : t₀ in s)
  proof: (hγ t₀ ht).continuousWithinAt

中文:
引理 Is整数egralCurveOn.continuousWithinAt
  条件: (hγ : Is整数egralCurveOn γ v s) (ht : t₀ in s)
  证明: (hγ t₀ ht).continuousWithinAt

Depends on / 依赖: continuousWithinAt
-/
lemma IsIntegralCurveOn.continuousWithinAt (hγ : IsIntegralCurveOn γ v s) (ht : t₀ in s) :
    ContinuousWithinAt γ s t₀ := (hγ t₀ ht).continuousWithinAt

/--
lemma `IsIntegralCurveOn.continuousOn` / 引理 `IsIntegralCurveOn.continuousOn`

English:
lemma IsIntegralCurveOn.continuousOn
  given: (hγ : IsIntegralCurveOn γ v s)
  proof: (hγ · · |>.continuousWithinAt)

中文:
引理 Is整数egralCurveOn.continuousOn
  条件: (hγ : Is整数egralCurveOn γ v s)
  证明: (hγ · · |>.continuousWithinAt)

Depends on / 依赖: continuousWithinAt
-/
lemma IsIntegralCurveOn.continuousOn (hγ : IsIntegralCurveOn γ v s) :
    ContinuousOn γ s := (hγ · · |>.continuousWithinAt)

/--
lemma `IsIntegralCurveAt.continuousAt` / 引理 `IsIntegralCurveAt.continuousAt`

English:
lemma IsIntegralCurveAt.continuousAt
  given: (hγ : IsIntegralCurveAt γ v t₀)
  proof: have ⟨_, hs, hγ⟩ := isIntegralCurveAt_iff_exists_mem_nhds.mp hγ
.continuousAt hs hγ.continuousWithinAt (mem_of_mem_nhds hs)

中文:
引理 Is整数egralCurveAt.continuousAt
  条件: (hγ : Is整数egralCurveAt γ v t₀)
  证明: have ⟨_, hs, hγ⟩ := isIntegralCurveAt_iff_exists_mem_nhds.mp hγ
.continuousAt hs hγ.continuousWithinAt (mem_of_mem_nhds hs)

Depends on / 依赖: continuousAt, continuousWithinAt, isIntegralCurveAt_iff_exists_mem_nhds, isIntegralCurveAt_iff_exists_mem_nhds.mp, mem_of_mem_nhds
-/
lemma IsIntegralCurveAt.continuousAt (hγ : IsIntegralCurveAt γ v t₀) :
    ContinuousAt γ t₀ :=
  have ⟨_, hs, hγ⟩ := isIntegralCurveAt_iff_exists_mem_nhds.mp hγ
.continuousAt hs hγ.continuousWithinAt (mem_of_mem_nhds hs)

/--
lemma `IsIntegralCurve.continuous` / 引理 `IsIntegralCurve.continuous`

English:
lemma IsIntegralCurve.continuous
  given: (hγ : IsIntegralCurve γ v)
  statement: Continuous γ
  proof: continuous_iff_continuousAt.mpr (hγ.isIntegralCurveAt · |>.continuousAt)

中文:
引理 Is整数egralCurve.continuous
  条件: (hγ : Is整数egralCurve γ v)
  结论: 连续 γ
  证明: continuous_iff_continuousAt.mpr (hγ.isIntegralCurveAt · |>.continuousAt)

Depends on / 依赖: continuousAt, continuous_iff_continuousAt, continuous_iff_continuousAt.mpr, isIntegralCurveAt
-/
lemma IsIntegralCurve.continuous (hγ : IsIntegralCurve γ v) : Continuous γ :=
  continuous_iff_continuousAt.mpr (hγ.isIntegralCurveAt · |>.continuousAt)
