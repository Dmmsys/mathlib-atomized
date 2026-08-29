/-
Copyright (c) 2023 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Tangent
public import Mathlib.Geometry.Manifold.Notation

/-!
# Integral curves of vector fields on a manifold

Let `M` be a manifold and `v : (x : M) → TangentSpace I x` be a vector field on `M`. An integral
curve of `v` is a function `γ : ℝ → M` such that the derivative of `γ` at `t` equals `v (γ t)`. The
integral curve may only be defined for all `t` within some subset of `ℝ`.

This is the first of a series of files, organised as follows:
* `Mathlib/Geometry/Manifold/IntegralCurve/Basic.lean` (this file): Basic definitions and lemmas
  relating them to each other and to continuity and differentiability
* `Mathlib/Geometry/Manifold/IntegralCurve/Transform.lean`: Lemmas about translating or scaling the
  domain of an integral curve by a constant
* `Mathlib/Geometry/Manifold/IntegralCurve/ExistUnique.lean`: Local existence and uniqueness
  theorems for integral curves

## Main definitions

Let `v : M → TM` be a vector field on `M`, and let `γ : ℝ → M`.
* `IsMIntegralCurve γ v`: `γ t` is tangent to `v (γ t)` for all `t : ℝ`. That is, `γ` is a global
  integral curve of `v`.
* `IsMIntegralCurveOn γ v s`: `γ t` is tangent to `v (γ t)` for all `t ∈ s`, where `s : Set ℝ`.
* `IsMIntegralCurveAt γ v t₀`: `γ t` is tangent to `v (γ t)` for all `t` in some open interval
  around `t₀`. That is, `γ` is a local integral curve of `v`.

For `IsMIntegralCurveOn γ v s` and `IsMIntegralCurveAt γ v t₀`, even though `γ` is defined for all
time, its value outside of the set `s` or a small interval around `t₀` is irrelevant and considered
junk.

## TODO

* Implement `IsMIntegralCurveWithinAt`.

## Reference

* [Lee, J. M. (2012). _Introduction to Smooth Manifolds_. Springer New York.][lee2012]

## Tags

integral curve, vector field
-/

@[expose] public section

open scoped Manifold Topology

open Set

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/--
Definition of `IsMIntegralCurveOn` / `IsMIntegralCurveOn` 的定义

English:
definition IsMIntegralCurveOn
  signature: (γ : Real -> M) (v : (x : M) -> TangentSpace% x) (s : Set Real)
  body: forall t in s, HasMFDerivAt[s] γ t ((1 : Real ->L[Real] Real).smulRight <| v (γ t))

中文:
定义 IsM整数egralCurveOn
  签名: (γ : 实数 -> M) (v : (x : M) -> TangentSpace% x) (s : 集合 实数)
  定义体: forall t in s, HasMFDerivAt[s] γ t ((1 : Real ->L[Real] Real).smulRight <| v (γ t))

Depends on / 依赖: HasMFDerivAt, finsuppTensorFinsuppLid_symm_single_smul, smulRight
-/
def IsMIntegralCurveOn (γ : Real -> M) (v : (x : M) -> TangentSpace% x) (s : Set Real) : Prop :=
  forall t in s, HasMFDerivAt[s] γ t ((1 : Real ->L[Real] Real).smulRight <| v (γ t))

/--
Definition of `IsMIntegralCurveAt` / `IsMIntegralCurveAt` 的定义

English:
definition IsMIntegralCurveAt
  signature: (γ : Real -> M) (v : (x : M) -> TangentSpace% x) (t₀ : Real)
  body: forallᶠ t in 𝓝 t₀, HasMFDerivAt% γ t ((1 : Real ->L[Real] Real).smulRight <| v (γ t))

中文:
定义 IsM整数egralCurveAt
  签名: (γ : 实数 -> M) (v : (x : M) -> TangentSpace% x) (t₀ : 实数)
  定义体: forallᶠ t in 𝓝 t₀, HasMFDerivAt% γ t ((1 : Real ->L[Real] Real).smulRight <| v (γ t))

Depends on / 依赖: HasMFDerivAt, _symm_single_mul, finsuppTensorFinsupp, nth_rw, one_mul, smulRight
-/
def IsMIntegralCurveAt (γ : Real -> M) (v : (x : M) -> TangentSpace% x) (t₀ : Real) : Prop :=
  forallᶠ t in 𝓝 t₀, HasMFDerivAt% γ t ((1 : Real ->L[Real] Real).smulRight <| v (γ t))

/--
Definition of `IsMIntegralCurve` / `IsMIntegralCurve` 的定义

English:
definition IsMIntegralCurve
  signature: (γ : Real -> M) (v : (x : M) -> TangentSpace% x)
  body: forall t : Real, HasMFDerivAt% γ t ((1 : Real ->L[Real] Real).smulRight (v (γ t)))

中文:
定义 IsM整数egralCurve
  签名: (γ : 实数 -> M) (v : (x : M) -> TangentSpace% x)
  定义体: forall t : Real, HasMFDerivAt% γ t ((1 : Real ->L[Real] Real).smulRight (v (γ t)))

Depends on / 依赖: HasMFDerivAt, _symm_single_mul, finsuppTensorFinsupp, mul_one, nth_rw, smulRight
-/
def IsMIntegralCurve (γ : Real -> M) (v : (x : M) -> TangentSpace% x) : Prop :=
  forall t : Real, HasMFDerivAt% γ t ((1 : Real ->L[Real] Real).smulRight (v (γ t)))

variable {γ γ' : Real -> M} {v : (x : M) -> TangentSpace% x} {s s' : Set Real} {t₀ : Real}

/--
lemma `IsMIntegralCurve.isMIntegralCurveOn` / 引理 `IsMIntegralCurve.isMIntegralCurveOn`

English:
lemma IsMIntegralCurve.isMIntegralCurveOn
  given: (h : IsMIntegralCurve γ v) (s : Set Real)
  proof: fun t _ => (h t).hasMFDerivWithinAt

中文:
引理 IsM整数egralCurve.isM整数egralCurveOn
  条件: (h : IsM整数egralCurve γ v) (s : 集合 实数)
  证明: fun t _ => (h t).hasMFDerivWithinAt

Depends on / 依赖: hasMFDerivWithinAt
-/
lemma IsMIntegralCurve.isMIntegralCurveOn (h : IsMIntegralCurve γ v) (s : Set Real) :
    IsMIntegralCurveOn γ v s := fun t _ => (h t).hasMFDerivWithinAt

/--
lemma `isMIntegralCurve_iff_isMIntegralCurveOn` / 引理 `isMIntegralCurve_iff_isMIntegralCurveOn`

English:
lemma isMIntegralCurve_iff_isMIntegralCurveOn
  proof: ⟨fun h => h.isMIntegralCurveOn _, fun h t => (h t (mem_univ _)).hasMFDerivAt Filter.univ_mem⟩

中文:
引理 isM整数egralCurve_iff_isM整数egralCurveOn
  证明: ⟨fun h => h.isMIntegralCurveOn _, fun h t => (h t (mem_univ _)).hasMFDerivAt Filter.univ_mem⟩

Depends on / 依赖: Filter, Filter.univ_mem, h.isMIntegralCurveOn, hasMFDerivAt, isMIntegralCurveOn, mem_univ, univ_mem
-/
lemma isMIntegralCurve_iff_isMIntegralCurveOn :
    IsMIntegralCurve γ v ↔ IsMIntegralCurveOn γ v univ :=
  ⟨fun h => h.isMIntegralCurveOn _, fun h t => (h t (mem_univ _)).hasMFDerivAt Filter.univ_mem⟩

/--
lemma `isMIntegralCurveAt_iff` / 引理 `isMIntegralCurveAt_iff`

English:
lemma isMIntegralCurveAt_iff
  proof: by
  constructor
  · intro h
    rw [IsMIntegralCurveAt]; rw [Filter.eventually_iff_exists_mem] at h
    obtain ⟨s, hs, h⟩ := h
    exact ⟨s, hs, fun t ht => (h t ht).hasMFDerivWithinAt⟩
  · rintro ⟨s, hs, h⟩
    rw [IsMIntegralCurveAt]; rw [Filter.eventually_iff_exists_mem]
    obtain ⟨s', h1, h2, 

中文:
引理 isM整数egralCurveAt_iff
  证明: by
  constructor
  · intro h
    rw [IsMIntegralCurveAt]; rw [Filter.eventually_iff_exists_mem] at h
    obtain ⟨s, hs, h⟩ := h
    exact ⟨s, hs, fun t ht => (h t ht).hasMFDerivWithinAt⟩
  · rintro ⟨s, hs, h⟩
    rw [IsMIntegralCurveAt]; rw [Filter.eventually_iff_exists_mem]
    obtain ⟨s', h1, h2, 

Depends on / 依赖: Filter, Filter.eventually_iff_exists_mem, IsMIntegralCurveAt, eventually_iff_exists_mem, h2.mem_nhds, hasMFDerivAt, hasMFDerivWithinAt, mem_nhds, mem_nhds_iff, mem_nhds_iff.mp
-/
lemma isMIntegralCurveAt_iff :
    IsMIntegralCurveAt γ v t₀ ↔ exists s in 𝓝 t₀, IsMIntegralCurveOn γ v s := by
  constructor
  · intro h
    rw [IsMIntegralCurveAt]; rw [Filter.eventually_iff_exists_mem] at h
    obtain ⟨s, hs, h⟩ := h
    exact ⟨s, hs, fun t ht => (h t ht).hasMFDerivWithinAt⟩
  · rintro ⟨s, hs, h⟩
    rw [IsMIntegralCurveAt]; rw [Filter.eventually_iff_exists_mem]
    obtain ⟨s', h1, h2, h3⟩ := mem_nhds_iff.mp hs
    refine ⟨s', h2.mem_nhds h3, ?_⟩
    intro t ht
    apply (h t (h1 ht)).hasMFDerivAt
    rw [mem_nhds_iff]
    exact ⟨s', h1, h2, ht⟩

/--
lemma `isMIntegralCurveAt_iff'` / 引理 `isMIntegralCurveAt_iff'`

English:
lemma isMIntegralCurveAt_iff'
  proof: by
  rw [isMIntegralCurveAt_iff]
  constructor
  · intro ⟨s, hs, h⟩
    rw [Metric.mem_nhds_iff] at hs
    obtain ⟨ε, hε, hε'⟩ := hs
    refine ⟨ε, hε, fun t ht => (h t (hε' ht)).mono hε'⟩
  · intro ⟨ε, hε, h⟩
    exact ⟨Metric.ball t₀ ε, Metric.ball_mem_nhds _ hε, h⟩

中文:
引理 isM整数egralCurveAt_iff'
  证明: by
  rw [isMIntegralCurveAt_iff]
  constructor
  · intro ⟨s, hs, h⟩
    rw [Metric.mem_nhds_iff] at hs
    obtain ⟨ε, hε, hε'⟩ := hs
    refine ⟨ε, hε, fun t ht => (h t (hε' ht)).mono hε'⟩
  · intro ⟨ε, hε, h⟩
    exact ⟨Metric.ball t₀ ε, Metric.ball_mem_nhds _ hε, h⟩

Depends on / 依赖: Metric, Metric.ball, Metric.ball_mem_nhds, Metric.mem_nhds_iff, ball_mem_nhds, isMIntegralCurveAt_iff, mem_nhds_iff
-/
lemma isMIntegralCurveAt_iff' :
    IsMIntegralCurveAt γ v t₀ ↔ exists ε > 0, IsMIntegralCurveOn γ v (Metric.ball t₀ ε) := by
  rw [isMIntegralCurveAt_iff]
  constructor
  · intro ⟨s, hs, h⟩
    rw [Metric.mem_nhds_iff] at hs
    obtain ⟨ε, hε, hε'⟩ := hs
    refine ⟨ε, hε, fun t ht => (h t (hε' ht)).mono hε'⟩
  · intro ⟨ε, hε, h⟩
    exact ⟨Metric.ball t₀ ε, Metric.ball_mem_nhds _ hε, h⟩

/--
lemma `IsMIntegralCurve.isMIntegralCurveAt` / 引理 `IsMIntegralCurve.isMIntegralCurveAt`

English:
lemma IsMIntegralCurve.isMIntegralCurveAt
  given: (h : IsMIntegralCurve γ v) (t : Real)
  proof: isMIntegralCurveAt_iff.mpr ⟨univ, Filter.univ_mem, fun t _ => (h t).hasMFDerivWithinAt⟩

中文:
引理 IsM整数egralCurve.isM整数egralCurveAt
  条件: (h : IsM整数egralCurve γ v) (t : 实数)
  证明: isMIntegralCurveAt_iff.mpr ⟨univ, Filter.univ_mem, fun t _ => (h t).hasMFDerivWithinAt⟩

Depends on / 依赖: Filter, Filter.univ_mem, hasMFDerivWithinAt, isMIntegralCurveAt_iff, isMIntegralCurveAt_iff.mpr, univ_mem
-/
lemma IsMIntegralCurve.isMIntegralCurveAt (h : IsMIntegralCurve γ v) (t : Real) :
    IsMIntegralCurveAt γ v t :=
  isMIntegralCurveAt_iff.mpr ⟨univ, Filter.univ_mem, fun t _ => (h t).hasMFDerivWithinAt⟩

/--
lemma `isMIntegralCurve_iff_isMIntegralCurveAt` / 引理 `isMIntegralCurve_iff_isMIntegralCurveAt`

English:
lemma isMIntegralCurve_iff_isMIntegralCurveAt
  proof: ⟨fun h => h.isMIntegralCurveAt, fun h t => by
    obtain ⟨s, hs, h⟩ := isMIntegralCurveAt_iff.mp (h t)
.hasMFDerivAt hs⟩ exact h t (mem_of_mem_nhds hs)

中文:
引理 isM整数egralCurve_iff_isM整数egralCurveAt
  证明: ⟨fun h => h.isMIntegralCurveAt, fun h t => by
    obtain ⟨s, hs, h⟩ := isMIntegralCurveAt_iff.mp (h t)
.hasMFDerivAt hs⟩ exact h t (mem_of_mem_nhds hs)

Depends on / 依赖: h.isMIntegralCurveAt, hasMFDerivAt, isMIntegralCurveAt, isMIntegralCurveAt_iff, isMIntegralCurveAt_iff.mp, mem_of_mem_nhds
-/
lemma isMIntegralCurve_iff_isMIntegralCurveAt :
    IsMIntegralCurve γ v ↔ forall t : Real, IsMIntegralCurveAt γ v t :=
  ⟨fun h => h.isMIntegralCurveAt, fun h t => by
    obtain ⟨s, hs, h⟩ := isMIntegralCurveAt_iff.mp (h t)
.hasMFDerivAt hs⟩ exact h t (mem_of_mem_nhds hs)

/--
lemma `IsMIntegralCurveOn.mono` / 引理 `IsMIntegralCurveOn.mono`

English:
lemma IsMIntegralCurveOn.mono
  given: (h : IsMIntegralCurveOn γ v s) (hs : s' subseteq s)
  proof: fun t ht => (h t (hs ht)).mono hs

中文:
引理 IsM整数egralCurveOn.mono
  条件: (h : IsM整数egralCurveOn γ v s) (hs : s' subseteq s)
  证明: fun t ht => (h t (hs ht)).mono hs
-/
lemma IsMIntegralCurveOn.mono (h : IsMIntegralCurveOn γ v s) (hs : s' subseteq s) :
    IsMIntegralCurveOn γ v s' := fun t ht => (h t (hs ht)).mono hs

/--
lemma `IsMIntegralCurveAt.hasMFDerivAt` / 引理 `IsMIntegralCurveAt.hasMFDerivAt`

English:
lemma IsMIntegralCurveAt.hasMFDerivAt
  given: (h : IsMIntegralCurveAt γ v t₀)
  proof: have ⟨_, hs, h⟩ := isMIntegralCurveAt_iff.mp h
.hasMFDerivAt hs h t₀ (mem_of_mem_nhds hs)

中文:
引理 IsM整数egralCurveAt.hasMFDerivAt
  条件: (h : IsM整数egralCurveAt γ v t₀)
  证明: have ⟨_, hs, h⟩ := isMIntegralCurveAt_iff.mp h
.hasMFDerivAt hs h t₀ (mem_of_mem_nhds hs)

Depends on / 依赖: hasMFDerivAt, isMIntegralCurveAt_iff, isMIntegralCurveAt_iff.mp, mem_of_mem_nhds
-/
lemma IsMIntegralCurveAt.hasMFDerivAt (h : IsMIntegralCurveAt γ v t₀) :
    HasMFDerivAt% γ t₀ ((1 : Real ->L[Real] Real).smulRight (v (γ t₀))) :=
  have ⟨_, hs, h⟩ := isMIntegralCurveAt_iff.mp h
.hasMFDerivAt hs h t₀ (mem_of_mem_nhds hs)

/--
lemma `IsMIntegralCurveOn.isMIntegralCurveAt` / 引理 `IsMIntegralCurveOn.isMIntegralCurveAt`

English:
lemma IsMIntegralCurveOn.isMIntegralCurveAt
  given: (h : IsMIntegralCurveOn γ v s) (hs : s in 𝓝 t₀)
  proof: isMIntegralCurveAt_iff.mpr ⟨s, hs, h⟩

中文:
引理 IsM整数egralCurveOn.isM整数egralCurveAt
  条件: (h : IsM整数egralCurveOn γ v s) (hs : s in 𝓝 t₀)
  证明: isMIntegralCurveAt_iff.mpr ⟨s, hs, h⟩

Depends on / 依赖: isMIntegralCurveAt_iff, isMIntegralCurveAt_iff.mpr
-/
lemma IsMIntegralCurveOn.isMIntegralCurveAt (h : IsMIntegralCurveOn γ v s) (hs : s in 𝓝 t₀) :
    IsMIntegralCurveAt γ v t₀ := isMIntegralCurveAt_iff.mpr ⟨s, hs, h⟩

/--
lemma `IsMIntegralCurveAt.isMIntegralCurveOn` / 引理 `IsMIntegralCurveAt.isMIntegralCurveOn`

English:
lemma IsMIntegralCurveAt.isMIntegralCurveOn
  given: (h : forall t in s, IsMIntegralCurveAt γ v t)
  proof: by
  intro t ht
  apply HasMFDerivAt.hasMFDerivWithinAt
  obtain ⟨s', hs', h⟩ := Filter.eventually_iff_exists_mem.mp (h t ht)
  exact h _ (mem_of_mem_nhds hs')

中文:
引理 IsM整数egralCurveAt.isM整数egralCurveOn
  条件: (h : 对任意 t in s, IsM整数egralCurveAt γ v t)
  证明: by
  intro t ht
  apply HasMFDerivAt.hasMFDerivWithinAt
  obtain ⟨s', hs', h⟩ := Filter.eventually_iff_exists_mem.mp (h t ht)
  exact h _ (mem_of_mem_nhds hs')

Depends on / 依赖: Filter, Filter.eventually_iff_exists_mem.mp, HasMFDerivAt, HasMFDerivAt.hasMFDerivWithinAt, eventually_iff_exists_mem, hasMFDerivWithinAt, mem_of_mem_nhds
-/
lemma IsMIntegralCurveAt.isMIntegralCurveOn (h : forall t in s, IsMIntegralCurveAt γ v t) :
    IsMIntegralCurveOn γ v s := by
  intro t ht
  apply HasMFDerivAt.hasMFDerivWithinAt
  obtain ⟨s', hs', h⟩ := Filter.eventually_iff_exists_mem.mp (h t ht)
  exact h _ (mem_of_mem_nhds hs')

/--
lemma `isMIntegralCurveOn_iff_isMIntegralCurveAt` / 引理 `isMIntegralCurveOn_iff_isMIntegralCurveAt`

English:
lemma isMIntegralCurveOn_iff_isMIntegralCurveAt
  given: (hs : IsOpen s)
  proof: ⟨fun h _ ht => h.isMIntegralCurveAt (hs.mem_nhds ht), IsMIntegralCurveAt.isMIntegralCurveOn⟩

中文:
引理 isM整数egralCurveOn_iff_isM整数egralCurveAt
  条件: (hs : 是开集 s)
  证明: ⟨fun h _ ht => h.isMIntegralCurveAt (hs.mem_nhds ht), IsMIntegralCurveAt.isMIntegralCurveOn⟩

Depends on / 依赖: IsMIntegralCurveAt, IsMIntegralCurveAt.isMIntegralCurveOn, h.isMIntegralCurveAt, hs.mem_nhds, isMIntegralCurveAt, isMIntegralCurveOn, mem_nhds
-/
lemma isMIntegralCurveOn_iff_isMIntegralCurveAt (hs : IsOpen s) :
    IsMIntegralCurveOn γ v s ↔ forall t in s, IsMIntegralCurveAt γ v t :=
  ⟨fun h _ ht => h.isMIntegralCurveAt (hs.mem_nhds ht), IsMIntegralCurveAt.isMIntegralCurveOn⟩

/--
lemma `IsMIntegralCurveOn.continuousWithinAt` / 引理 `IsMIntegralCurveOn.continuousWithinAt`

English:
lemma IsMIntegralCurveOn.continuousWithinAt
  given: (hγ : IsMIntegralCurveOn γ v s) (ht : t₀ in s)
  proof: (hγ t₀ ht).1

中文:
引理 IsM整数egralCurveOn.continuousWithinAt
  条件: (hγ : IsM整数egralCurveOn γ v s) (ht : t₀ in s)
  证明: (hγ t₀ ht).1
-/
lemma IsMIntegralCurveOn.continuousWithinAt (hγ : IsMIntegralCurveOn γ v s) (ht : t₀ in s) :
    ContinuousWithinAt γ s t₀ := (hγ t₀ ht).1

/--
lemma `IsMIntegralCurveOn.continuousOn` / 引理 `IsMIntegralCurveOn.continuousOn`

English:
lemma IsMIntegralCurveOn.continuousOn
  given: (hγ : IsMIntegralCurveOn γ v s)
  proof: fun t ht => (hγ t ht).continuousWithinAt

中文:
引理 IsM整数egralCurveOn.continuousOn
  条件: (hγ : IsM整数egralCurveOn γ v s)
  证明: fun t ht => (hγ t ht).continuousWithinAt

Depends on / 依赖: continuousWithinAt
-/
lemma IsMIntegralCurveOn.continuousOn (hγ : IsMIntegralCurveOn γ v s) :
    ContinuousOn γ s := fun t ht => (hγ t ht).continuousWithinAt

/--
lemma `IsMIntegralCurveAt.continuousAt` / 引理 `IsMIntegralCurveAt.continuousAt`

English:
lemma IsMIntegralCurveAt.continuousAt
  given: (hγ : IsMIntegralCurveAt γ v t₀)
  proof: have ⟨_, hs, hγ⟩ := isMIntegralCurveAt_iff.mp hγ
.continuousAt hs hγ.continuousWithinAt (mem_of_mem_nhds hs)

中文:
引理 IsM整数egralCurveAt.continuousAt
  条件: (hγ : IsM整数egralCurveAt γ v t₀)
  证明: have ⟨_, hs, hγ⟩ := isMIntegralCurveAt_iff.mp hγ
.continuousAt hs hγ.continuousWithinAt (mem_of_mem_nhds hs)

Depends on / 依赖: continuousAt, continuousWithinAt, isMIntegralCurveAt_iff, isMIntegralCurveAt_iff.mp, mem_of_mem_nhds
-/
lemma IsMIntegralCurveAt.continuousAt (hγ : IsMIntegralCurveAt γ v t₀) :
    ContinuousAt γ t₀ :=
  have ⟨_, hs, hγ⟩ := isMIntegralCurveAt_iff.mp hγ
.continuousAt hs hγ.continuousWithinAt (mem_of_mem_nhds hs)

/--
lemma `IsMIntegralCurve.continuous` / 引理 `IsMIntegralCurve.continuous`

English:
lemma IsMIntegralCurve.continuous
  given: (hγ : IsMIntegralCurve γ v)
  statement: Continuous γ
  proof: continuous_iff_continuousAt.mpr fun t => (hγ.isMIntegralCurveAt t).continuousAt

中文:
引理 IsM整数egralCurve.continuous
  条件: (hγ : IsM整数egralCurve γ v)
  结论: 连续 γ
  证明: continuous_iff_continuousAt.mpr fun t => (hγ.isMIntegralCurveAt t).continuousAt

Depends on / 依赖: continuousAt, continuous_iff_continuousAt, continuous_iff_continuousAt.mpr, isMIntegralCurveAt
-/
lemma IsMIntegralCurve.continuous (hγ : IsMIntegralCurve γ v) : Continuous γ :=
  continuous_iff_continuousAt.mpr fun t => (hγ.isMIntegralCurveAt t).continuousAt

variable [IsManifold I 1 M]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `IsMIntegralCurveOn.hasDerivWithinAt` / 引理 `IsMIntegralCurveOn.hasDerivWithinAt`

English:
lemma IsMIntegralCurveOn.hasDerivWithinAt
  statement: (hγ : IsMIntegralCurveOn γ v s) {t : Real} (ht : t in s)
  proof: by
  -- turn `HasDerivWithinAt` into comp of `HasMFDerivWithinAt`
  replace hsrc := extChartAt_source I (γ t₀) ▸ hsrc
  rw [hasDerivWithinAt_iff_hasFDerivWithinAt]; rw [← hasMFDerivWithinAt_iff_hasFDerivWithinAt]
  apply (HasMFDerivWithinAt.comp t (hasMFDerivWithinAt_extChartAt (I := I) hsrc) (hγ _ 

中文:
引理 IsM整数egralCurveOn.hasDerivWithinAt
  结论: (hγ : IsM整数egralCurveOn γ v s) {t : 实数} (ht : t in s)
  证明: by
  -- turn `HasDerivWithinAt` into comp of `HasMFDerivWithinAt`
  replace hsrc := extChartAt_source I (γ t₀) ▸ hsrc
  rw [hasDerivWithinAt_iff_hasFDerivWithinAt]; rw [← hasMFDerivWithinAt_iff_hasFDerivWithinAt]
  apply (HasMFDerivWithinAt.comp t (hasMFDerivWithinAt_extChartAt (I := I) hsrc) (hγ _ 
-/
lemma IsMIntegralCurveOn.hasDerivWithinAt (hγ : IsMIntegralCurveOn γ v s) {t : Real} (ht : t in s)
    (hsrc : γ t in (extChartAt I (γ t₀)).source) :
    HasDerivWithinAt ((extChartAt I (γ t₀)) ∘ γ)
      (tangentCoordChange I (γ t) (γ t₀) (γ t) (v (γ t))) s t := by
  -- turn `HasDerivWithinAt` into comp of `HasMFDerivWithinAt`
  replace hsrc := extChartAt_source I (γ t₀) ▸ hsrc
  rw [hasDerivWithinAt_iff_hasFDerivWithinAt]; rw [← hasMFDerivWithinAt_iff_hasFDerivWithinAt]
  apply (HasMFDerivWithinAt.comp t (hasMFDerivWithinAt_extChartAt (I := I) hsrc) (hγ _ ht)
    (Set.subset_preimage_image _ _)).congr_mfderiv
  rw [ContinuousLinearMap.ext_iff]
  intro a
  rw [ContinuousLinearMap.comp_apply]; rw [ContinuousLinearMap.smulRight_apply]; rw [map_smul]; rw [← one_apply_eq_self (F := TangentSpace 𝓘(Real]; rw [Real) t ->L[Real] TangentSpace 𝓘(Real, Real) t) a,
    ← ContinuousLinearMap.smulRight_apply,
    mfderiv_chartAt_eq_tangentCoordChange hsrc]
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
lemma `IsMIntegralCurveAt.eventually_hasDerivAt` / 引理 `IsMIntegralCurveAt.eventually_hasDerivAt`

English:
lemma IsMIntegralCurveAt.eventually_hasDerivAt
  given: (hγ : IsMIntegralCurveAt γ v t₀)
  proof: by
  apply eventually_mem_nhds_iff.mpr
.mono .and hγ (hγ.continuousAt.preimage_mem_nhds (extChartAt_source_mem_nhds (I := I) _))
  rintro t ⟨ht1, ht2⟩
  have hsrc := mem_of_mem_nhds ht1
  rw [mem_preimage]; rw [extChartAt_source I (γ t₀)] at hsrc
  rw [hasDerivAt_iff_hasFDerivAt]; rw [← hasMFDerivAt

中文:
引理 IsM整数egralCurveAt.eventually_hasDerivAt
  条件: (hγ : IsM整数egralCurveAt γ v t₀)
  证明: by
  apply eventually_mem_nhds_iff.mpr
.mono .and hγ (hγ.continuousAt.preimage_mem_nhds (extChartAt_source_mem_nhds (I := I) _))
  rintro t ⟨ht1, ht2⟩
  have hsrc := mem_of_mem_nhds ht1
  rw [mem_preimage]; rw [extChartAt_source I (γ t₀)] at hsrc
  rw [hasDerivAt_iff_hasFDerivAt]; rw [← hasMFDerivAt

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.comp_apply, ContinuousLinearMap.ext_iff, ContinuousLinearMap.smul, HasMFDerivAt, HasMFDerivAt.comp, comp_apply, congr_mfderiv, continuousAt, continuousAt.preimage_mem_nhds, eventually_mem_nhds_iff, eventually_mem_nhds_iff.mpr, extChartAt_source, extChartAt_source_mem_nhds, ext_iff, hasDerivAt_iff_hasFDerivAt, hasMFDerivAt_extChartAt, hasMFDerivAt_iff_hasFDerivAt, mem_of_mem_nhds, mem_preimage
-/
lemma IsMIntegralCurveAt.eventually_hasDerivAt (hγ : IsMIntegralCurveAt γ v t₀) :
    forallᶠ t in 𝓝 t₀, HasDerivAt ((extChartAt I (γ t₀)) ∘ γ)
      (tangentCoordChange I (γ t) (γ t₀) (γ t) (v (γ t))) t := by
  apply eventually_mem_nhds_iff.mpr
.mono .and hγ (hγ.continuousAt.preimage_mem_nhds (extChartAt_source_mem_nhds (I := I) _))
  rintro t ⟨ht1, ht2⟩
  have hsrc := mem_of_mem_nhds ht1
  rw [mem_preimage]; rw [extChartAt_source I (γ t₀)] at hsrc
  rw [hasDerivAt_iff_hasFDerivAt]; rw [← hasMFDerivAt_iff_hasFDerivAt]
  apply (HasMFDerivAt.comp t (hasMFDerivAt_extChartAt (I := I) hsrc) ht2).congr_mfderiv
  rw [ContinuousLinearMap.ext_iff]
  intro a
  rw [ContinuousLinearMap.comp_apply]; rw [ContinuousLinearMap.smulRight_apply]; rw [map_smul]; rw [← one_apply_eq_self (F := TangentSpace 𝓘(Real]; rw [Real) t ->L[Real] TangentSpace 𝓘(Real, Real) t) a,
    ← ContinuousLinearMap.smulRight_apply,
    mfderiv_chartAt_eq_tangentCoordChange hsrc]
  rfl
