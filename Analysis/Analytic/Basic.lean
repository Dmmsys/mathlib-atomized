/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Analytic.ConvergenceRadius
public import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# Analytic functions

A function is analytic in one dimension around `0` if it can be written as a converging power series
`Σ pₙ zⁿ`. This definition can be extended to any dimension (even in infinite dimension) by
requiring that `pₙ` is a continuous `n`-multilinear map. In general, `pₙ` is not unique (in two
dimensions, taking `p₂ (x, y) (x', y') = x y'` or `y x'` gives the same map when applied to a
vector `(x, y) (x, y)`). A way to guarantee uniqueness is to take a symmetric `pₙ`, but this is not
always possible in nonzero characteristic (in characteristic 2, the previous example has no
symmetric representative). Therefore, we do not insist on symmetry or uniqueness in the definition,
and we only require the existence of a converging series.

The general framework is important to say that the exponential map on bounded operators on a Banach
space is analytic, as well as the inverse on invertible operators.

## Main definitions

Let `p` be a formal multilinear series from `E` to `F`, i.e., `p n` is a multilinear map on `E^n`
for `n : ℕ`.

* `HasFPowerSeriesOnBall f p x r`: on the ball of center `x` with radius `r`,
  `f (x + y) = ∑'_n pₙ yⁿ`.
* `HasFPowerSeriesAt f p x`: on some ball of center `x` with positive radius, holds
  `HasFPowerSeriesOnBall f p x r`.
* `AnalyticAt 𝕜 f x`: there exists a power series `p` such that holds `HasFPowerSeriesAt f p x`.
* `AnalyticOnNhd 𝕜 f s`: the function `f` is analytic at every point of `s`.

We also define versions of `HasFPowerSeriesOnBall`, `AnalyticAt`, and `AnalyticOnNhd` restricted to
a set, similar to `ContinuousWithinAt`.
See `Mathlib/Analysis/Analytic/Within.lean` for basic properties.

* `AnalyticWithinAt 𝕜 f s x` means a power series at `x` converges to `f` on `𝓝[s ∪ {x}] x`.
* `AnalyticOn 𝕜 f s t` means `∀ x ∈ t, AnalyticWithinAt 𝕜 f s x`.

We develop the basic properties of these notions, notably:
* If a function admits a power series, it is continuous (see
  `HasFPowerSeriesOnBall.continuousOn` and `HasFPowerSeriesAt.continuousAt` and
  `AnalyticAt.continuousAt`).
* In a complete space, the sum of a formal power series with positive radius is well defined on the
  disk of convergence, see `FormalMultilinearSeries.hasFPowerSeriesOnBall`.

-/

@[expose] public section

variable {𝕜 E F G : Type*}

variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]

open Topology NNReal Filter ENNReal Set Asymptotics
open scoped Pointwise

/-! ### Expanding a function as a power series -/

section

variable {f g : E -> F} {p pf : FormalMultilinearSeries 𝕜 E F} {s t : Set E} {x : E} {r r' : Real>=0∞}

/--
Definition of `HasFPowerSeriesOnBall` / `HasFPowerSeriesOnBall` 的定义

English:
structure HasFPowerSeriesOnBall
  parameters: (f : E -> F) (p : FormalMultilinearSeries 𝕜 E F) (x : E) (r : Real>=0∞)
  axioms and operations (3):
    - r_le : r <= p.radius
    - r_pos : 0 < r
    - hasSum : forall {y}, y in Metric.eball (0 : E) r -> HasSum (fun n : Nat => p n fun _ : Fin n => y) (f (x + y))

中文:
结构 HasFPowerSeriesOnBall
  参数: (f : E -> F) (p : FormalMultilinearSeries 𝕜 E F) (x : E) (r : 实数>=0∞)
  公理与运算 (3 个):
    - r_le : r <= p.radius
    - r_pos : 0 < r
    - hasSum : 对任意 {y}, y in Metric.eball (0 : E) r -> HasSum (fun n : 自然数 => p n fun _ : Fin n => y) (f (x + y))
-/
structure HasFPowerSeriesOnBall (f : E -> F) (p : FormalMultilinearSeries 𝕜 E F) (x : E) (r : Real>=0∞) :
    Prop where
  r_le : r <= p.radius
  r_pos : 0 < r
  hasSum :
    forall {y}, y in Metric.eball (0 : E) r -> HasSum (fun n : Nat => p n fun _ : Fin n => y) (f (x + y))

/--
Definition of `HasFPowerSeriesWithinOnBall` / `HasFPowerSeriesWithinOnBall` 的定义

English:
structure HasFPowerSeriesWithinOnBall
  parameters: (f : E -> F) (p : FormalMultilinearSeries 𝕜 E F) (s : Set E)
  axioms and operations (3):
    - r_le : r <= p.radius
    - r_pos : 0 < r
    - hasSum : forall {y}, x + y in insert x s -> y in Metric.eball (0 : E) r -> HasSum (fun n : Nat => p n fun _ : Fin n => y) (f (x + y))

中文:
结构 HasFPowerSeriesWithinOnBall
  参数: (f : E -> F) (p : FormalMultilinearSeries 𝕜 E F) (s : Set E)
  公理与运算 (3 个):
    - r_le : r <= p.radius
    - r_pos : 0 < r
    - hasSum : 对任意 {y}, x + y in insert x s -> y in Metric.eball (0 : E) r -> HasSum (fun n : 自然数 => p n fun _ : Fin n => y) (f (x + y))
-/
structure HasFPowerSeriesWithinOnBall (f : E -> F) (p : FormalMultilinearSeries 𝕜 E F) (s : Set E)
    (x : E) (r : Real>=0∞) : Prop where
  /-- `p` converges on `ball 0 r` -/
  r_le : r <= p.radius
  /-- The radius of convergence is positive -/
  r_pos : 0 < r
  /-- `p converges to f` within `s` -/
  hasSum : forall {y}, x + y in insert x s -> y in Metric.eball (0 : E) r ->
    HasSum (fun n : Nat => p n fun _ : Fin n => y) (f (x + y))

/--
Definition of `HasFPowerSeriesAt` / `HasFPowerSeriesAt` 的定义

English:
definition HasFPowerSeriesAt
  signature: (f : E -> F) (p : FormalMultilinearSeries 𝕜 E F) (x : E)
  body: exists r, HasFPowerSeriesOnBall f p x r

中文:
定义 HasFPowerSeriesAt
  签名: (f : E -> F) (p : FormalMultilinearSeries 𝕜 E F) (x : E)
  定义体: exists r, HasFPowerSeriesOnBall f p x r

Depends on / 依赖: HasFPowerSeriesOnBall
-/
def HasFPowerSeriesAt (f : E -> F) (p : FormalMultilinearSeries 𝕜 E F) (x : E) :=
  exists r, HasFPowerSeriesOnBall f p x r

/--
Definition of `HasFPowerSeriesWithinAt` / `HasFPowerSeriesWithinAt` 的定义

English:
definition HasFPowerSeriesWithinAt
  signature: (f : E -> F) (p : FormalMultilinearSeries 𝕜 E F) (s : Set E) (x : E)
  body: exists r, HasFPowerSeriesWithinOnBall f p s x r

中文:
定义 HasFPowerSeriesWithinAt
  签名: (f : E -> F) (p : FormalMultilinearSeries 𝕜 E F) (s : Set E) (x : E)
  定义体: exists r, HasFPowerSeriesWithinOnBall f p s x r

Depends on / 依赖: HasFPowerSeriesWithinOnBall
-/
def HasFPowerSeriesWithinAt (f : E -> F) (p : FormalMultilinearSeries 𝕜 E F) (s : Set E) (x : E) :=
  exists r, HasFPowerSeriesWithinOnBall f p s x r

-- Teach the `bound` tactic that power series have positive radius
attribute [bound_forward] HasFPowerSeriesOnBall.r_pos HasFPowerSeriesWithinOnBall.r_pos

variable (𝕜)

/-- Given a function `f : E → F`, we say that `f` is analytic at `x` if it admits a convergent power
series expansion around `x`. -/
@[fun_prop]
/--
Definition of `AnalyticAt` / `AnalyticAt` 的定义

English:
definition AnalyticAt
  signature: (f : E -> F) (x : E)
  body: exists p : FormalMultilinearSeries 𝕜 E F, HasFPowerSeriesAt f p x

中文:
定义 AnalyticAt
  签名: (f : E -> F) (x : E)
  定义体: exists p : FormalMultilinearSeries 𝕜 E F, HasFPowerSeriesAt f p x

Depends on / 依赖: FormalMultilinearSeries, HasFPowerSeriesAt
-/
def AnalyticAt (f : E -> F) (x : E) :=
  exists p : FormalMultilinearSeries 𝕜 E F, HasFPowerSeriesAt f p x

/--
Definition of `AnalyticWithinAt` / `AnalyticWithinAt` 的定义

English:
definition AnalyticWithinAt
  signature: (f : E -> F) (s : Set E) (x : E)
  body: exists p : FormalMultilinearSeries 𝕜 E F, HasFPowerSeriesWithinAt f p s x

中文:
定义 AnalyticWithinAt
  签名: (f : E -> F) (s : Set E) (x : E)
  定义体: exists p : FormalMultilinearSeries 𝕜 E F, HasFPowerSeriesWithinAt f p s x

Depends on / 依赖: FormalMultilinearSeries, HasFPowerSeriesWithinAt
-/
def AnalyticWithinAt (f : E -> F) (s : Set E) (x : E) : Prop :=
  exists p : FormalMultilinearSeries 𝕜 E F, HasFPowerSeriesWithinAt f p s x

/--
Definition of `AnalyticOnNhd` / `AnalyticOnNhd` 的定义

English:
definition AnalyticOnNhd
  signature: (f : E -> F) (s : Set E)
  body: forall x, x in s -> AnalyticAt 𝕜 f x

中文:
定义 AnalyticOnNhd
  签名: (f : E -> F) (s : Set E)
  定义体: forall x, x in s -> AnalyticAt 𝕜 f x

Depends on / 依赖: AnalyticAt
-/
def AnalyticOnNhd (f : E -> F) (s : Set E) :=
  forall x, x in s -> AnalyticAt 𝕜 f x

/--
Definition of `AnalyticOn` / `AnalyticOn` 的定义

English:
definition AnalyticOn
  signature: (f : E -> F) (s : Set E)
  body: forall x in s, AnalyticWithinAt 𝕜 f s x

中文:
定义 AnalyticOn
  签名: (f : E -> F) (s : Set E)
  定义体: forall x in s, AnalyticWithinAt 𝕜 f s x

Depends on / 依赖: AnalyticWithinAt
-/
def AnalyticOn (f : E -> F) (s : Set E) : Prop :=
  forall x in s, AnalyticWithinAt 𝕜 f s x

/-!
### `HasFPowerSeriesOnBall` and `HasFPowerSeriesWithinOnBall`
-/

variable {𝕜}

/--
theorem `HasFPowerSeriesOnBall.hasFPowerSeriesAt` / 定理 `HasFPowerSeriesOnBall.hasFPowerSeriesAt`

English:
theorem HasFPowerSeriesOnBall.hasFPowerSeriesAt
  given: (hf : HasFPowerSeriesOnBall f p x r)
  proof: ⟨r, hf⟩

中文:
定理 HasFPowerSeriesOnBall.hasFPowerSeriesAt
  条件: (hf : HasFPowerSeriesOnBall f p x r)
  证明: ⟨r, hf⟩
-/
theorem HasFPowerSeriesOnBall.hasFPowerSeriesAt (hf : HasFPowerSeriesOnBall f p x r) :
    HasFPowerSeriesAt f p x :=
  ⟨r, hf⟩

/--
theorem `HasFPowerSeriesAt.analyticAt` / 定理 `HasFPowerSeriesAt.analyticAt`

English:
theorem HasFPowerSeriesAt.analyticAt
  given: (hf : HasFPowerSeriesAt f p x)
  statement: AnalyticAt 𝕜 f x
  proof: ⟨p, hf⟩

中文:
定理 HasFPowerSeriesAt.analyticAt
  条件: (hf : HasFPowerSeriesAt f p x)
  结论: AnalyticAt 𝕜 f x
  证明: ⟨p, hf⟩
-/
theorem HasFPowerSeriesAt.analyticAt (hf : HasFPowerSeriesAt f p x) : AnalyticAt 𝕜 f x :=
  ⟨p, hf⟩

/--
theorem `HasFPowerSeriesOnBall.analyticAt` / 定理 `HasFPowerSeriesOnBall.analyticAt`

English:
theorem HasFPowerSeriesOnBall.analyticAt
  given: (hf : HasFPowerSeriesOnBall f p x r)
  statement: AnalyticAt 𝕜 f x
  proof: hf.hasFPowerSeriesAt.analyticAt

中文:
定理 HasFPowerSeriesOnBall.analyticAt
  条件: (hf : HasFPowerSeriesOnBall f p x r)
  结论: AnalyticAt 𝕜 f x
  证明: hf.hasFPowerSeriesAt.analyticAt

Depends on / 依赖: analyticAt, hasFPowerSeriesAt, hf.hasFPowerSeriesAt.analyticAt
-/
theorem HasFPowerSeriesOnBall.analyticAt (hf : HasFPowerSeriesOnBall f p x r) : AnalyticAt 𝕜 f x :=
  hf.hasFPowerSeriesAt.analyticAt

/--
theorem `HasFPowerSeriesWithinOnBall.hasFPowerSeriesWithinAt` / 定理 `HasFPowerSeriesWithinOnBall.hasFPowerSeriesWithinAt`

English:
theorem HasFPowerSeriesWithinOnBall.hasFPowerSeriesWithinAt
  proof: ⟨r, hf⟩

中文:
定理 HasFPowerSeriesWithinOnBall.hasFPowerSeriesWithinAt
  证明: ⟨r, hf⟩
-/
theorem HasFPowerSeriesWithinOnBall.hasFPowerSeriesWithinAt
    (hf : HasFPowerSeriesWithinOnBall f p s x r) : HasFPowerSeriesWithinAt f p s x :=
  ⟨r, hf⟩

/--
theorem `HasFPowerSeriesWithinAt.analyticWithinAt` / 定理 `HasFPowerSeriesWithinAt.analyticWithinAt`

English:
theorem HasFPowerSeriesWithinAt.analyticWithinAt
  given: (hf : HasFPowerSeriesWithinAt f p s x)
  proof: ⟨p, hf⟩

中文:
定理 HasFPowerSeriesWithinAt.analyticWithinAt
  条件: (hf : HasFPowerSeriesWithinAt f p s x)
  证明: ⟨p, hf⟩
-/
theorem HasFPowerSeriesWithinAt.analyticWithinAt (hf : HasFPowerSeriesWithinAt f p s x) :
    AnalyticWithinAt 𝕜 f s x := ⟨p, hf⟩

/--
theorem `HasFPowerSeriesWithinOnBall.analyticWithinAt` / 定理 `HasFPowerSeriesWithinOnBall.analyticWithinAt`

English:
theorem HasFPowerSeriesWithinOnBall.analyticWithinAt
  given: (hf : HasFPowerSeriesWithinOnBall f p s x r)
  proof: hf.hasFPowerSeriesWithinAt.analyticWithinAt

中文:
定理 HasFPowerSeriesWithinOnBall.analyticWithinAt
  条件: (hf : HasFPowerSeriesWithinOnBall f p s x r)
  证明: hf.hasFPowerSeriesWithinAt.analyticWithinAt

Depends on / 依赖: analyticWithinAt, hasFPowerSeriesWithinAt, hf.hasFPowerSeriesWithinAt.analyticWithinAt
-/
theorem HasFPowerSeriesWithinOnBall.analyticWithinAt (hf : HasFPowerSeriesWithinOnBall f p s x r) :
    AnalyticWithinAt 𝕜 f s x :=
  hf.hasFPowerSeriesWithinAt.analyticWithinAt

/--
theorem `HasFPowerSeriesOnBall.comp_sub` / 定理 `HasFPowerSeriesOnBall.comp_sub`

English:
theorem HasFPowerSeriesOnBall.comp_sub
  given: (hf : HasFPowerSeriesOnBall f p x r) (y : E)
  proof: { r_le := hf.r_le
    r_pos := hf.r_pos
    hasSum := fun {z} hz => by
      convert hf.hasSum hz
      abel }

中文:
定理 HasFPowerSeriesOnBall.comp_sub
  条件: (hf : HasFPowerSeriesOnBall f p x r) (y : E)
  证明: { r_le := hf.r_le
    r_pos := hf.r_pos
    hasSum := fun {z} hz => by
      convert hf.hasSum hz
      abel }

Depends on / 依赖: convert, hasSum, hf.hasSum, hf.r_le, hf.r_pos, r_le, r_pos
-/
theorem HasFPowerSeriesOnBall.comp_sub (hf : HasFPowerSeriesOnBall f p x r) (y : E) :
    HasFPowerSeriesOnBall (fun z => f (z - y)) p (x + y) r :=
  { r_le := hf.r_le
    r_pos := hf.r_pos
    hasSum := fun {z} hz => by
      convert hf.hasSum hz
      abel }

/--
theorem `HasFPowerSeriesWithinOnBall.comp_sub` / 定理 `HasFPowerSeriesWithinOnBall.comp_sub`

English:
theorem HasFPowerSeriesWithinOnBall.comp_sub
  given: (hf : HasFPowerSeriesWithinOnBall f p s x r) (y : E)
  proof: hf.r_le
  r_pos := hf.r_pos
  hasSum {z} hz1 hz2 := by
    have : x + z in insert x s := by
      simp only [add_singleton, image_add_right, mem_insert_iff, add_eq_left, mem_preimage] at hz1 ⊢
      abel_nf at hz1
      assumption
    convert hf.hasSum this hz2
    abel

中文:
定理 HasFPowerSeriesWithinOnBall.comp_sub
  条件: (hf : HasFPowerSeriesWithinOnBall f p s x r) (y : E)
  证明: hf.r_le
  r_pos := hf.r_pos
  hasSum {z} hz1 hz2 := by
    have : x + z in insert x s := by
      simp only [add_singleton, image_add_right, mem_insert_iff, add_eq_left, mem_preimage] at hz1 ⊢
      abel_nf at hz1
      assumption
    convert hf.hasSum this hz2
    abel

Depends on / 依赖: hf.r_le, r_le
-/
theorem HasFPowerSeriesWithinOnBall.comp_sub (hf : HasFPowerSeriesWithinOnBall f p s x r) (y : E) :
    HasFPowerSeriesWithinOnBall (fun z => f (z - y)) p (s + {y}) (x + y) r where
  r_le := hf.r_le
  r_pos := hf.r_pos
  hasSum {z} hz1 hz2 := by
    have : x + z in insert x s := by
      simp only [add_singleton, image_add_right, mem_insert_iff, add_eq_left, mem_preimage] at hz1 ⊢
      abel_nf at hz1
      assumption
    convert hf.hasSum this hz2
    abel

/--
theorem `HasFPowerSeriesAt.comp_sub` / 定理 `HasFPowerSeriesAt.comp_sub`

English:
theorem HasFPowerSeriesAt.comp_sub
  given: (hf : HasFPowerSeriesAt f p x) (y : E)
  proof: by
  obtain ⟨r, hf⟩ := hf
  exact ⟨r, hf.comp_sub _⟩

中文:
定理 HasFPowerSeriesAt.comp_sub
  条件: (hf : HasFPowerSeriesAt f p x) (y : E)
  证明: by
  obtain ⟨r, hf⟩ := hf
  exact ⟨r, hf.comp_sub _⟩

Depends on / 依赖: comp_sub, hf.comp_sub
-/
theorem HasFPowerSeriesAt.comp_sub (hf : HasFPowerSeriesAt f p x) (y : E) :
    HasFPowerSeriesAt (fun z => f (z - y)) p (x + y) := by
  obtain ⟨r, hf⟩ := hf
  exact ⟨r, hf.comp_sub _⟩

/--
theorem `HasFPowerSeriesWithinAt.comp_sub` / 定理 `HasFPowerSeriesWithinAt.comp_sub`

English:
theorem HasFPowerSeriesWithinAt.comp_sub
  given: (hf : HasFPowerSeriesWithinAt f p s x) (y : E)
  proof: by
  obtain ⟨r, hf⟩ := hf
  exact ⟨r, hf.comp_sub _⟩

中文:
定理 HasFPowerSeriesWithinAt.comp_sub
  条件: (hf : HasFPowerSeriesWithinAt f p s x) (y : E)
  证明: by
  obtain ⟨r, hf⟩ := hf
  exact ⟨r, hf.comp_sub _⟩

Depends on / 依赖: comp_sub, hf.comp_sub
-/
theorem HasFPowerSeriesWithinAt.comp_sub (hf : HasFPowerSeriesWithinAt f p s x) (y : E) :
    HasFPowerSeriesWithinAt (fun z => f (z - y)) p (s + {y}) (x + y) := by
  obtain ⟨r, hf⟩ := hf
  exact ⟨r, hf.comp_sub _⟩

/--
theorem `AnalyticAt.comp_sub` / 定理 `AnalyticAt.comp_sub`

English:
theorem AnalyticAt.comp_sub
  given: (hf : AnalyticAt 𝕜 f x) (y : E)
  proof: by
  obtain ⟨p, hf⟩ := hf
  exact ⟨p, hf.comp_sub _⟩

中文:
定理 AnalyticAt.comp_sub
  条件: (hf : AnalyticAt 𝕜 f x) (y : E)
  证明: by
  obtain ⟨p, hf⟩ := hf
  exact ⟨p, hf.comp_sub _⟩

Depends on / 依赖: comp_sub, hf.comp_sub
-/
theorem AnalyticAt.comp_sub (hf : AnalyticAt 𝕜 f x) (y : E) :
    AnalyticAt 𝕜 (fun z => f (z - y)) (x + y) := by
  obtain ⟨p, hf⟩ := hf
  exact ⟨p, hf.comp_sub _⟩

/--
theorem `AnalyticOnNhd.comp_sub` / 定理 `AnalyticOnNhd.comp_sub`

English:
theorem AnalyticOnNhd.comp_sub
  given: (hf : AnalyticOnNhd 𝕜 f s) (y : E)
  proof: by
  intro x hx
  simp only [add_singleton, image_add_right, mem_preimage] at hx
  rw [show x = (x - y) + y by abel]
  apply (hf (x - y) (by convert hx; abel)).comp_sub

中文:
定理 AnalyticOnNhd.comp_sub
  条件: (hf : AnalyticOnNhd 𝕜 f s) (y : E)
  证明: by
  intro x hx
  simp only [add_singleton, image_add_right, mem_preimage] at hx
  rw [show x = (x - y) + y by abel]
  apply (hf (x - y) (by convert hx; abel)).comp_sub

Depends on / 依赖: add_singleton, comp_sub, convert, image_add_right, mem_preimage
-/
theorem AnalyticOnNhd.comp_sub (hf : AnalyticOnNhd 𝕜 f s) (y : E) :
    AnalyticOnNhd 𝕜 (fun z => f (z - y)) (s + {y}) := by
  intro x hx
  simp only [add_singleton, image_add_right, mem_preimage] at hx
  rw [show x = (x - y) + y by abel]
  apply (hf (x - y) (by convert hx; abel)).comp_sub

/--
theorem `AnalyticWithinAt.comp_sub` / 定理 `AnalyticWithinAt.comp_sub`

English:
theorem AnalyticWithinAt.comp_sub
  given: (hf : AnalyticWithinAt 𝕜 f s x) (y : E)
  proof: by
  obtain ⟨p, hf⟩ := hf
  exact ⟨p, hf.comp_sub _⟩

中文:
定理 AnalyticWithinAt.comp_sub
  条件: (hf : AnalyticWithinAt 𝕜 f s x) (y : E)
  证明: by
  obtain ⟨p, hf⟩ := hf
  exact ⟨p, hf.comp_sub _⟩

Depends on / 依赖: comp_sub, hf.comp_sub
-/
theorem AnalyticWithinAt.comp_sub (hf : AnalyticWithinAt 𝕜 f s x) (y : E) :
    AnalyticWithinAt 𝕜 (fun z => f (z - y)) (s + {y}) (x + y) := by
  obtain ⟨p, hf⟩ := hf
  exact ⟨p, hf.comp_sub _⟩

/--
theorem `AnalyticOn.comp_sub` / 定理 `AnalyticOn.comp_sub`

English:
theorem AnalyticOn.comp_sub
  given: (hf : AnalyticOn 𝕜 f s) (y : E)
  proof: by
  intro x hx
  simp only [add_singleton, image_add_right, mem_preimage] at hx
  rw [show x = (x - y) + y by abel]
  apply (hf (x - y) (by convert hx; abel)).comp_sub

中文:
定理 AnalyticOn.comp_sub
  条件: (hf : AnalyticOn 𝕜 f s) (y : E)
  证明: by
  intro x hx
  simp only [add_singleton, image_add_right, mem_preimage] at hx
  rw [show x = (x - y) + y by abel]
  apply (hf (x - y) (by convert hx; abel)).comp_sub

Depends on / 依赖: add_singleton, comp_sub, convert, image_add_right, mem_preimage
-/
theorem AnalyticOn.comp_sub (hf : AnalyticOn 𝕜 f s) (y : E) :
    AnalyticOn 𝕜 (fun z => f (z - y)) (s + {y}) := by
  intro x hx
  simp only [add_singleton, image_add_right, mem_preimage] at hx
  rw [show x = (x - y) + y by abel]
  apply (hf (x - y) (by convert hx; abel)).comp_sub

/--
theorem `HasFPowerSeriesWithinOnBall.hasSum_sub` / 定理 `HasFPowerSeriesWithinOnBall.hasSum_sub`

English:
theorem HasFPowerSeriesWithinOnBall.hasSum_sub
  statement: (hf : HasFPowerSeriesWithinOnBall f p s x r) {y : E}
  proof: by
  have : y - x in Metric.eball 0 r := by simpa [edist_eq_enorm_sub] using hy.2
  simpa only [add_sub_cancel] using hf.hasSum (by simpa only [add_sub_cancel] using hy.1) this

中文:
定理 HasFPowerSeriesWithinOnBall.hasSum_sub
  结论: (hf : HasFPowerSeriesWithinOnBall f p s x r) {y : E}
  证明: by
  have : y - x in Metric.eball 0 r := by simpa [edist_eq_enorm_sub] using hy.2
  simpa only [add_sub_cancel] using hf.hasSum (by simpa only [add_sub_cancel] using hy.1) this

Depends on / 依赖: Metric, Metric.eball, add_sub_cancel, edist_eq_enorm_sub, hasSum, hf.hasSum
-/
theorem HasFPowerSeriesWithinOnBall.hasSum_sub (hf : HasFPowerSeriesWithinOnBall f p s x r) {y : E}
    (hy : y in (insert x s) inter Metric.eball x r) :
    HasSum (fun n : Nat => p n fun _ => y - x) (f y) := by
  have : y - x in Metric.eball 0 r := by simpa [edist_eq_enorm_sub] using hy.2
  simpa only [add_sub_cancel] using hf.hasSum (by simpa only [add_sub_cancel] using hy.1) this

/--
theorem `HasFPowerSeriesOnBall.hasSum_sub` / 定理 `HasFPowerSeriesOnBall.hasSum_sub`

English:
theorem HasFPowerSeriesOnBall.hasSum_sub
  statement: (hf : HasFPowerSeriesOnBall f p x r) {y : E}
  proof: by
  have : y - x in Metric.eball 0 r := by simpa [edist_eq_enorm_sub] using hy
  simpa only [add_sub_cancel] using hf.hasSum this

中文:
定理 HasFPowerSeriesOnBall.hasSum_sub
  结论: (hf : HasFPowerSeriesOnBall f p x r) {y : E}
  证明: by
  have : y - x in Metric.eball 0 r := by simpa [edist_eq_enorm_sub] using hy
  simpa only [add_sub_cancel] using hf.hasSum this

Depends on / 依赖: Metric, Metric.eball, add_sub_cancel, edist_eq_enorm_sub, hasSum, hf.hasSum
-/
theorem HasFPowerSeriesOnBall.hasSum_sub (hf : HasFPowerSeriesOnBall f p x r) {y : E}
    (hy : y in Metric.eball x r) : HasSum (fun n : Nat => p n fun _ => y - x) (f y) := by
  have : y - x in Metric.eball 0 r := by simpa [edist_eq_enorm_sub] using hy
  simpa only [add_sub_cancel] using hf.hasSum this

/--
theorem `HasFPowerSeriesOnBall.radius_pos` / 定理 `HasFPowerSeriesOnBall.radius_pos`

English:
theorem HasFPowerSeriesOnBall.radius_pos
  given: (hf : HasFPowerSeriesOnBall f p x r)
  statement: 0 < p.radius
  proof: lt_of_lt_of_le hf.r_pos hf.r_le

中文:
定理 HasFPowerSeriesOnBall.radius_pos
  条件: (hf : HasFPowerSeriesOnBall f p x r)
  结论: 0 < p.radius
  证明: lt_of_lt_of_le hf.r_pos hf.r_le

Depends on / 依赖: hf.r_le, hf.r_pos, lt_of_lt_of_le, r_le, r_pos
-/
theorem HasFPowerSeriesOnBall.radius_pos (hf : HasFPowerSeriesOnBall f p x r) : 0 < p.radius :=
  lt_of_lt_of_le hf.r_pos hf.r_le

/--
theorem `HasFPowerSeriesWithinOnBall.radius_pos` / 定理 `HasFPowerSeriesWithinOnBall.radius_pos`

English:
theorem HasFPowerSeriesWithinOnBall.radius_pos
  given: (hf : HasFPowerSeriesWithinOnBall f p s x r)
  proof: lt_of_lt_of_le hf.r_pos hf.r_le

中文:
定理 HasFPowerSeriesWithinOnBall.radius_pos
  条件: (hf : HasFPowerSeriesWithinOnBall f p s x r)
  证明: lt_of_lt_of_le hf.r_pos hf.r_le

Depends on / 依赖: hf.r_le, hf.r_pos, lt_of_lt_of_le, r_le, r_pos
-/
theorem HasFPowerSeriesWithinOnBall.radius_pos (hf : HasFPowerSeriesWithinOnBall f p s x r) :
    0 < p.radius :=
  lt_of_lt_of_le hf.r_pos hf.r_le

/--
theorem `HasFPowerSeriesAt.radius_pos` / 定理 `HasFPowerSeriesAt.radius_pos`

English:
theorem HasFPowerSeriesAt.radius_pos
  given: (hf : HasFPowerSeriesAt f p x)
  statement: 0 < p.radius
  proof: let ⟨_, hr⟩ := hf
  hr.radius_pos

中文:
定理 HasFPowerSeriesAt.radius_pos
  条件: (hf : HasFPowerSeriesAt f p x)
  结论: 0 < p.radius
  证明: let ⟨_, hr⟩ := hf
  hr.radius_pos

Depends on / 依赖: hr.radius_pos, radius_pos
-/
theorem HasFPowerSeriesAt.radius_pos (hf : HasFPowerSeriesAt f p x) : 0 < p.radius :=
  let ⟨_, hr⟩ := hf
  hr.radius_pos

/--
theorem `HasFPowerSeriesWithinOnBall.of_le` / 定理 `HasFPowerSeriesWithinOnBall.of_le`

English:
theorem HasFPowerSeriesWithinOnBall.of_le
  proof: ⟨le_trans hr hf.1, r'_pos, fun hy h'y => hf.hasSum hy (Metric.eball_subset_eball hr h'y)⟩

中文:
定理 HasFPowerSeriesWithinOnBall.of_le
  证明: ⟨le_trans hr hf.1, r'_pos, fun hy h'y => hf.hasSum hy (Metric.eball_subset_eball hr h'y)⟩

Depends on / 依赖: Metric, Metric.eball_subset_eball, _pos, eball_subset_eball, hasSum, hf.hasSum, le_trans
-/
theorem HasFPowerSeriesWithinOnBall.of_le
    (hf : HasFPowerSeriesWithinOnBall f p s x r) (r'_pos : 0 < r') (hr : r' <= r) :
    HasFPowerSeriesWithinOnBall f p s x r' :=
  ⟨le_trans hr hf.1, r'_pos, fun hy h'y => hf.hasSum hy (Metric.eball_subset_eball hr h'y)⟩

/--
theorem `HasFPowerSeriesOnBall.mono` / 定理 `HasFPowerSeriesOnBall.mono`

English:
theorem HasFPowerSeriesOnBall.mono
  statement: (hf : HasFPowerSeriesOnBall f p x r) (r'_pos : 0 < r')
  proof: ⟨le_trans hr hf.1, r'_pos, fun hy => hf.hasSum (Metric.eball_subset_eball hr hy)⟩

中文:
定理 HasFPowerSeriesOnBall.mono
  结论: (hf : HasFPowerSeriesOnBall f p x r) (r'_pos : 0 < r')
  证明: ⟨le_trans hr hf.1, r'_pos, fun hy => hf.hasSum (Metric.eball_subset_eball hr hy)⟩

Depends on / 依赖: Metric, Metric.eball_subset_eball, _pos, eball_subset_eball, hasSum, hf.hasSum, le_trans
-/
theorem HasFPowerSeriesOnBall.mono (hf : HasFPowerSeriesOnBall f p x r) (r'_pos : 0 < r')
    (hr : r' <= r) : HasFPowerSeriesOnBall f p x r' :=
  ⟨le_trans hr hf.1, r'_pos, fun hy => hf.hasSum (Metric.eball_subset_eball hr hy)⟩

/--
lemma `HasFPowerSeriesWithinOnBall.congr` / 引理 `HasFPowerSeriesWithinOnBall.congr`

English:
lemma HasFPowerSeriesWithinOnBall.congr
  statement: {f g : E -> F} {p : FormalMultilinearSeries 𝕜 E F}
  proof: by
  refine ⟨h.r_le, h.r_pos, ?_⟩
  intro y hy h'y
  convert h.hasSum hy h'y
  simp only [mem_insert_iff, add_eq_left] at hy
  rcases hy with rfl | hy
  · simpa using h''
  · apply h'
    refine ⟨hy, ?_⟩
    simpa [edist_eq_enorm_sub] using h'y

中文:
引理 HasFPowerSeriesWithinOnBall.congr
  结论: {f g : E -> F} {p : FormalMultilinearSeries 𝕜 E F}
  证明: by
  refine ⟨h.r_le, h.r_pos, ?_⟩
  intro y hy h'y
  convert h.hasSum hy h'y
  simp only [mem_insert_iff, add_eq_left] at hy
  rcases hy with rfl | hy
  · simpa using h''
  · apply h'
    refine ⟨hy, ?_⟩
    simpa [edist_eq_enorm_sub] using h'y

Depends on / 依赖: add_eq_left, convert, edist_eq_enorm_sub, h.hasSum, h.r_le, h.r_pos, hasSum, mem_insert_iff, r_le, r_pos
-/
lemma HasFPowerSeriesWithinOnBall.congr {f g : E -> F} {p : FormalMultilinearSeries 𝕜 E F}
    {s : Set E} {x : E} {r : Real>=0∞} (h : HasFPowerSeriesWithinOnBall f p s x r)
    (h' : EqOn g f (s inter Metric.eball x r)) (h'' : g x = f x) :
    HasFPowerSeriesWithinOnBall g p s x r := by
  refine ⟨h.r_le, h.r_pos, ?_⟩
  intro y hy h'y
  convert h.hasSum hy h'y
  simp only [mem_insert_iff, add_eq_left] at hy
  rcases hy with rfl | hy
  · simpa using h''
  · apply h'
    refine ⟨hy, ?_⟩
    simpa [edist_eq_enorm_sub] using h'y

/--
lemma `HasFPowerSeriesWithinOnBall.congr'` / 引理 `HasFPowerSeriesWithinOnBall.congr'`

English:
lemma HasFPowerSeriesWithinOnBall.congr'
  statement: {f g : E -> F} {p : FormalMultilinearSeries 𝕜 E F}
  proof: by
  refine ⟨h.r_le, h.r_pos, fun {y} hy h'y => ?_⟩
  convert h.hasSum hy h'y
  exact h' ⟨hy, by simpa [edist_eq_enorm_sub] using h'y⟩

中文:
引理 HasFPowerSeriesWithinOnBall.congr'
  结论: {f g : E -> F} {p : FormalMultilinearSeries 𝕜 E F}
  证明: by
  refine ⟨h.r_le, h.r_pos, fun {y} hy h'y => ?_⟩
  convert h.hasSum hy h'y
  exact h' ⟨hy, by simpa [edist_eq_enorm_sub] using h'y⟩

Depends on / 依赖: convert, edist_eq_enorm_sub, h.hasSum, h.r_le, h.r_pos, hasSum, r_le, r_pos
-/
lemma HasFPowerSeriesWithinOnBall.congr' {f g : E -> F} {p : FormalMultilinearSeries 𝕜 E F}
    {s : Set E} {x : E} {r : Real>=0∞} (h : HasFPowerSeriesWithinOnBall f p s x r)
    (h' : EqOn g f (insert x s inter Metric.eball x r)) :
    HasFPowerSeriesWithinOnBall g p s x r := by
  refine ⟨h.r_le, h.r_pos, fun {y} hy h'y => ?_⟩
  convert h.hasSum hy h'y
  exact h' ⟨hy, by simpa [edist_eq_enorm_sub] using h'y⟩

/--
lemma `HasFPowerSeriesWithinAt.congr` / 引理 `HasFPowerSeriesWithinAt.congr`

English:
lemma HasFPowerSeriesWithinAt.congr
  statement: {f g : E -> F} {p : FormalMultilinearSeries 𝕜 E F} {s : Set E}
  proof: by
  rcases h with ⟨r, hr⟩
  obtain ⟨ε, εpos, hε⟩ : exists ε > 0, Metric.eball x ε inter s subseteq {y | g y = f y} :=
    EMetric.mem_nhdsWithin_iff.1 h'
  let r' := min r ε
  refine ⟨r', ?_⟩
  have := hr.of_le (r' := r') (by simp [r', εpos, hr.r_pos]) (min_le_left _ _)
  apply this.congr _ h''
  i

中文:
引理 HasFPowerSeriesWithinAt.congr
  结论: {f g : E -> F} {p : FormalMultilinearSeries 𝕜 E F} {s : Set E}
  证明: by
  rcases h with ⟨r, hr⟩
  obtain ⟨ε, εpos, hε⟩ : exists ε > 0, Metric.eball x ε inter s subseteq {y | g y = f y} :=
    EMetric.mem_nhdsWithin_iff.1 h'
  let r' := min r ε
  refine ⟨r', ?_⟩
  have := hr.of_le (r' := r') (by simp [r', εpos, hr.r_pos]) (min_le_left _ _)
  apply this.congr _ h''
  i

Depends on / 依赖: EMetric, EMetric.mem_nhdsWithin_iff, Metric, Metric.eball, Metric.eball_subset_eball, eball_subset_eball, hr.of_le, hr.r_pos, mem_nhdsWithin_iff, min_le_left, min_le_right, of_le, r_pos, subseteq, this.congr
-/
lemma HasFPowerSeriesWithinAt.congr {f g : E -> F} {p : FormalMultilinearSeries 𝕜 E F} {s : Set E}
    {x : E} (h : HasFPowerSeriesWithinAt f p s x) (h' : g =ᶠ[𝓝[s] x] f) (h'' : g x = f x) :
    HasFPowerSeriesWithinAt g p s x := by
  rcases h with ⟨r, hr⟩
  obtain ⟨ε, εpos, hε⟩ : exists ε > 0, Metric.eball x ε inter s subseteq {y | g y = f y} :=
    EMetric.mem_nhdsWithin_iff.1 h'
  let r' := min r ε
  refine ⟨r', ?_⟩
  have := hr.of_le (r' := r') (by simp [r', εpos, hr.r_pos]) (min_le_left _ _)
  apply this.congr _ h''
  intro z hz
  exact hε ⟨Metric.eball_subset_eball (min_le_right _ _) hz.2, hz.1⟩

/--
theorem `HasFPowerSeriesOnBall.congr` / 定理 `HasFPowerSeriesOnBall.congr`

English:
theorem HasFPowerSeriesOnBall.congr
  statement: (hf : HasFPowerSeriesOnBall f p x r)
  proof: { r_le := hf.r_le
    r_pos := hf.r_pos
    hasSum := fun {y} hy => by
      convert hf.hasSum hy
      apply hg.symm
      simpa [edist_eq_enorm_sub] using hy }

中文:
定理 HasFPowerSeriesOnBall.congr
  结论: (hf : HasFPowerSeriesOnBall f p x r)
  证明: { r_le := hf.r_le
    r_pos := hf.r_pos
    hasSum := fun {y} hy => by
      convert hf.hasSum hy
      apply hg.symm
      simpa [edist_eq_enorm_sub] using hy }

Depends on / 依赖: convert, edist_eq_enorm_sub, hasSum, hf.hasSum, hf.r_le, hf.r_pos, hg.symm, r_le, r_pos
-/
theorem HasFPowerSeriesOnBall.congr (hf : HasFPowerSeriesOnBall f p x r)
    (hg : EqOn f g (Metric.eball x r)) : HasFPowerSeriesOnBall g p x r :=
  { r_le := hf.r_le
    r_pos := hf.r_pos
    hasSum := fun {y} hy => by
      convert hf.hasSum hy
      apply hg.symm
      simpa [edist_eq_enorm_sub] using hy }

/--
theorem `HasFPowerSeriesAt.congr` / 定理 `HasFPowerSeriesAt.congr`

English:
theorem HasFPowerSeriesAt.congr
  given: (hf : HasFPowerSeriesAt f p x) (hg : f =ᶠ[𝓝 x] g)
  proof: by
  rcases hf with ⟨r₁, h₁⟩
  rcases EMetric.mem_nhds_iff.mp hg with ⟨r₂, h₂pos, h₂⟩
  exact ⟨min r₁ r₂,
    (h₁.mono (lt_min h₁.r_pos h₂pos) inf_le_left).congr
      fun y hy => h₂ (Metric.eball_subset_eball inf_le_right hy)⟩

中文:
定理 HasFPowerSeriesAt.congr
  条件: (hf : HasFPowerSeriesAt f p x) (hg : f =ᶠ[𝓝 x] g)
  证明: by
  rcases hf with ⟨r₁, h₁⟩
  rcases EMetric.mem_nhds_iff.mp hg with ⟨r₂, h₂pos, h₂⟩
  exact ⟨min r₁ r₂,
    (h₁.mono (lt_min h₁.r_pos h₂pos) inf_le_left).congr
      fun y hy => h₂ (Metric.eball_subset_eball inf_le_right hy)⟩

Depends on / 依赖: EMetric, EMetric.mem_nhds_iff.mp, Metric, Metric.eball_subset_eball, eball_subset_eball, inf_le_left, inf_le_right, lt_min, mem_nhds_iff, r_pos
-/
theorem HasFPowerSeriesAt.congr (hf : HasFPowerSeriesAt f p x) (hg : f =ᶠ[𝓝 x] g) :
    HasFPowerSeriesAt g p x := by
  rcases hf with ⟨r₁, h₁⟩
  rcases EMetric.mem_nhds_iff.mp hg with ⟨r₂, h₂pos, h₂⟩
  exact ⟨min r₁ r₂,
    (h₁.mono (lt_min h₁.r_pos h₂pos) inf_le_left).congr
      fun y hy => h₂ (Metric.eball_subset_eball inf_le_right hy)⟩

/--
theorem `HasFPowerSeriesWithinOnBall.unique` / 定理 `HasFPowerSeriesWithinOnBall.unique`

English:
theorem HasFPowerSeriesWithinOnBall.unique
  statement: (hf : HasFPowerSeriesWithinOnBall f p s x r)
  proof: fun _ hy =>
  (hf.hasSum_sub hy).unique (hg.hasSum_sub hy)

中文:
定理 HasFPowerSeriesWithinOnBall.unique
  结论: (hf : HasFPowerSeriesWithinOnBall f p s x r)
  证明: fun _ hy =>
  (hf.hasSum_sub hy).unique (hg.hasSum_sub hy)
-/
theorem HasFPowerSeriesWithinOnBall.unique (hf : HasFPowerSeriesWithinOnBall f p s x r)
    (hg : HasFPowerSeriesWithinOnBall g p s x r) :
    (insert x s inter Metric.eball x r).EqOn f g := fun _ hy =>
  (hf.hasSum_sub hy).unique (hg.hasSum_sub hy)

/--
theorem `HasFPowerSeriesOnBall.unique` / 定理 `HasFPowerSeriesOnBall.unique`

English:
theorem HasFPowerSeriesOnBall.unique
  statement: (hf : HasFPowerSeriesOnBall f p x r)
  proof: fun _ hy =>
  (hf.hasSum_sub hy).unique (hg.hasSum_sub hy)

中文:
定理 HasFPowerSeriesOnBall.unique
  结论: (hf : HasFPowerSeriesOnBall f p x r)
  证明: fun _ hy =>
  (hf.hasSum_sub hy).unique (hg.hasSum_sub hy)
-/
theorem HasFPowerSeriesOnBall.unique (hf : HasFPowerSeriesOnBall f p x r)
    (hg : HasFPowerSeriesOnBall g p x r) : (Metric.eball x r).EqOn f g := fun _ hy =>
  (hf.hasSum_sub hy).unique (hg.hasSum_sub hy)

/--
theorem `HasFPowerSeriesWithinAt.eventually` / 定理 `HasFPowerSeriesWithinAt.eventually`

English:
theorem HasFPowerSeriesWithinAt.eventually
  given: (hf : HasFPowerSeriesWithinAt f p s x)
  proof: let ⟨_, hr⟩ := hf
  mem_of_superset (Ioo_mem_nhdsGT hr.r_pos) fun _ hr' => hr.of_le hr'.1 hr'.2.le

中文:
定理 HasFPowerSeriesWithinAt.eventually
  条件: (hf : HasFPowerSeriesWithinAt f p s x)
  证明: let ⟨_, hr⟩ := hf
  mem_of_superset (Ioo_mem_nhdsGT hr.r_pos) fun _ hr' => hr.of_le hr'.1 hr'.2.le
-/
protected theorem HasFPowerSeriesWithinAt.eventually (hf : HasFPowerSeriesWithinAt f p s x) :
    forallᶠ r : Real>=0∞ in 𝓝[>] 0, HasFPowerSeriesWithinOnBall f p s x r :=
  let ⟨_, hr⟩ := hf
  mem_of_superset (Ioo_mem_nhdsGT hr.r_pos) fun _ hr' => hr.of_le hr'.1 hr'.2.le

/--
theorem `HasFPowerSeriesAt.eventually` / 定理 `HasFPowerSeriesAt.eventually`

English:
theorem HasFPowerSeriesAt.eventually
  given: (hf : HasFPowerSeriesAt f p x)
  proof: let ⟨_, hr⟩ := hf
  mem_of_superset (Ioo_mem_nhdsGT hr.r_pos) fun _ hr' => hr.mono hr'.1 hr'.2.le

中文:
定理 HasFPowerSeriesAt.eventually
  条件: (hf : HasFPowerSeriesAt f p x)
  证明: let ⟨_, hr⟩ := hf
  mem_of_superset (Ioo_mem_nhdsGT hr.r_pos) fun _ hr' => hr.mono hr'.1 hr'.2.le
-/
protected theorem HasFPowerSeriesAt.eventually (hf : HasFPowerSeriesAt f p x) :
    forallᶠ r : Real>=0∞ in 𝓝[>] 0, HasFPowerSeriesOnBall f p x r :=
  let ⟨_, hr⟩ := hf
  mem_of_superset (Ioo_mem_nhdsGT hr.r_pos) fun _ hr' => hr.mono hr'.1 hr'.2.le

/--
theorem `HasFPowerSeriesOnBall.eventually_hasSum` / 定理 `HasFPowerSeriesOnBall.eventually_hasSum`

English:
theorem HasFPowerSeriesOnBall.eventually_hasSum
  given: (hf : HasFPowerSeriesOnBall f p x r)
  proof: by
  filter_upwards [Metric.eball_mem_nhds (0 : E) hf.r_pos] using fun _ => hf.hasSum

中文:
定理 HasFPowerSeriesOnBall.eventually_hasSum
  条件: (hf : HasFPowerSeriesOnBall f p x r)
  证明: by
  filter_upwards [Metric.eball_mem_nhds (0 : E) hf.r_pos] using fun _ => hf.hasSum

Depends on / 依赖: Metric, Metric.eball_mem_nhds, eball_mem_nhds, filter_upwards, hasSum, hf.hasSum, hf.r_pos, r_pos
-/
theorem HasFPowerSeriesOnBall.eventually_hasSum (hf : HasFPowerSeriesOnBall f p x r) :
    forallᶠ y in 𝓝 0, HasSum (fun n : Nat => p n fun _ : Fin n => y) (f (x + y)) := by
  filter_upwards [Metric.eball_mem_nhds (0 : E) hf.r_pos] using fun _ => hf.hasSum

/--
theorem `HasFPowerSeriesAt.eventually_hasSum` / 定理 `HasFPowerSeriesAt.eventually_hasSum`

English:
theorem HasFPowerSeriesAt.eventually_hasSum
  given: (hf : HasFPowerSeriesAt f p x)
  proof: let ⟨_, hr⟩ := hf
  hr.eventually_hasSum

中文:
定理 HasFPowerSeriesAt.eventually_hasSum
  条件: (hf : HasFPowerSeriesAt f p x)
  证明: let ⟨_, hr⟩ := hf
  hr.eventually_hasSum

Depends on / 依赖: eventually_hasSum, hr.eventually_hasSum
-/
theorem HasFPowerSeriesAt.eventually_hasSum (hf : HasFPowerSeriesAt f p x) :
    forallᶠ y in 𝓝 0, HasSum (fun n : Nat => p n fun _ : Fin n => y) (f (x + y)) :=
  let ⟨_, hr⟩ := hf
  hr.eventually_hasSum

/--
theorem `HasFPowerSeriesOnBall.eventually_hasSum_sub` / 定理 `HasFPowerSeriesOnBall.eventually_hasSum_sub`

English:
theorem HasFPowerSeriesOnBall.eventually_hasSum_sub
  given: (hf : HasFPowerSeriesOnBall f p x r)
  proof: by
  filter_upwards [Metric.eball_mem_nhds x hf.r_pos] with y using hf.hasSum_sub

中文:
定理 HasFPowerSeriesOnBall.eventually_hasSum_sub
  条件: (hf : HasFPowerSeriesOnBall f p x r)
  证明: by
  filter_upwards [Metric.eball_mem_nhds x hf.r_pos] with y using hf.hasSum_sub

Depends on / 依赖: Metric, Metric.eball_mem_nhds, eball_mem_nhds, filter_upwards, hasSum_sub, hf.hasSum_sub, hf.r_pos, r_pos
-/
theorem HasFPowerSeriesOnBall.eventually_hasSum_sub (hf : HasFPowerSeriesOnBall f p x r) :
    forallᶠ y in 𝓝 x, HasSum (fun n : Nat => p n fun _ : Fin n => y - x) (f y) := by
  filter_upwards [Metric.eball_mem_nhds x hf.r_pos] with y using hf.hasSum_sub

/--
theorem `HasFPowerSeriesAt.eventually_hasSum_sub` / 定理 `HasFPowerSeriesAt.eventually_hasSum_sub`

English:
theorem HasFPowerSeriesAt.eventually_hasSum_sub
  given: (hf : HasFPowerSeriesAt f p x)
  proof: let ⟨_, hr⟩ := hf
  hr.eventually_hasSum_sub

中文:
定理 HasFPowerSeriesAt.eventually_hasSum_sub
  条件: (hf : HasFPowerSeriesAt f p x)
  证明: let ⟨_, hr⟩ := hf
  hr.eventually_hasSum_sub

Depends on / 依赖: eventually_hasSum_sub, hr.eventually_hasSum_sub
-/
theorem HasFPowerSeriesAt.eventually_hasSum_sub (hf : HasFPowerSeriesAt f p x) :
    forallᶠ y in 𝓝 x, HasSum (fun n : Nat => p n fun _ : Fin n => y - x) (f y) :=
  let ⟨_, hr⟩ := hf
  hr.eventually_hasSum_sub

/--
theorem `HasFPowerSeriesOnBall.eventually_eq_zero` / 定理 `HasFPowerSeriesOnBall.eventually_eq_zero`

English:
theorem HasFPowerSeriesOnBall.eventually_eq_zero
  proof: by
  filter_upwards [hf.eventually_hasSum_sub] with z hz using hz.unique hasSum_zero

中文:
定理 HasFPowerSeriesOnBall.eventually_eq_zero
  证明: by
  filter_upwards [hf.eventually_hasSum_sub] with z hz using hz.unique hasSum_zero

Depends on / 依赖: eventually_hasSum_sub, filter_upwards, hasSum_zero, hf.eventually_hasSum_sub, hz.unique, unique
-/
theorem HasFPowerSeriesOnBall.eventually_eq_zero
    (hf : HasFPowerSeriesOnBall f (0 : FormalMultilinearSeries 𝕜 E F) x r) :
    forallᶠ z in 𝓝 x, f z = 0 := by
  filter_upwards [hf.eventually_hasSum_sub] with z hz using hz.unique hasSum_zero

/--
theorem `HasFPowerSeriesAt.eventually_eq_zero` / 定理 `HasFPowerSeriesAt.eventually_eq_zero`

English:
theorem HasFPowerSeriesAt.eventually_eq_zero
  proof: let ⟨_, hr⟩ := hf
  hr.eventually_eq_zero

中文:
定理 HasFPowerSeriesAt.eventually_eq_zero
  证明: let ⟨_, hr⟩ := hf
  hr.eventually_eq_zero

Depends on / 依赖: eventually_eq_zero, hr.eventually_eq_zero
-/
theorem HasFPowerSeriesAt.eventually_eq_zero
    (hf : HasFPowerSeriesAt f (0 : FormalMultilinearSeries 𝕜 E F) x) : forallᶠ z in 𝓝 x, f z = 0 :=
  let ⟨_, hr⟩ := hf
  hr.eventually_eq_zero

/--
lemma `hasFPowerSeriesWithinOnBall_univ` / 引理 `hasFPowerSeriesWithinOnBall_univ`

English:
lemma hasFPowerSeriesWithinOnBall_univ
  proof: by
  constructor
  · intro h
    refine ⟨h.r_le, h.r_pos, fun {y} m => h.hasSum (by simp) m⟩
  · intro h
    exact ⟨h.r_le, h.r_pos, fun {y} _ m => h.hasSum m⟩

中文:
引理 hasFPowerSeriesWithinOnBall_univ
  证明: by
  constructor
  · intro h
    refine ⟨h.r_le, h.r_pos, fun {y} m => h.hasSum (by simp) m⟩
  · intro h
    exact ⟨h.r_le, h.r_pos, fun {y} _ m => h.hasSum m⟩
-/
@[simp] lemma hasFPowerSeriesWithinOnBall_univ :
    HasFPowerSeriesWithinOnBall f p univ x r ↔ HasFPowerSeriesOnBall f p x r := by
  constructor
  · intro h
    refine ⟨h.r_le, h.r_pos, fun {y} m => h.hasSum (by simp) m⟩
  · intro h
    exact ⟨h.r_le, h.r_pos, fun {y} _ m => h.hasSum m⟩

/--
lemma `hasFPowerSeriesWithinAt_univ` / 引理 `hasFPowerSeriesWithinAt_univ`

English:
lemma hasFPowerSeriesWithinAt_univ
  proof: by
  simp only [HasFPowerSeriesWithinAt, hasFPowerSeriesWithinOnBall_univ, HasFPowerSeriesAt]

中文:
引理 hasFPowerSeriesWithinAt_univ
  证明: by
  simp only [HasFPowerSeriesWithinAt, hasFPowerSeriesWithinOnBall_univ, HasFPowerSeriesAt]
-/
@[simp] lemma hasFPowerSeriesWithinAt_univ :
    HasFPowerSeriesWithinAt f p univ x ↔ HasFPowerSeriesAt f p x := by
  simp only [HasFPowerSeriesWithinAt, hasFPowerSeriesWithinOnBall_univ, HasFPowerSeriesAt]

/--
lemma `HasFPowerSeriesWithinOnBall.mono` / 引理 `HasFPowerSeriesWithinOnBall.mono`

English:
lemma HasFPowerSeriesWithinOnBall.mono
  given: (hf : HasFPowerSeriesWithinOnBall f p s x r) (h : t subseteq s)
  proof: hf.r_le
  r_pos := hf.r_pos
  hasSum hy h'y := hf.hasSum (insert_subset_insert h hy) h'y

中文:
引理 HasFPowerSeriesWithinOnBall.mono
  条件: (hf : HasFPowerSeriesWithinOnBall f p s x r) (h : t subseteq s)
  证明: hf.r_le
  r_pos := hf.r_pos
  hasSum hy h'y := hf.hasSum (insert_subset_insert h hy) h'y

Depends on / 依赖: hf.r_le, r_le
-/
lemma HasFPowerSeriesWithinOnBall.mono (hf : HasFPowerSeriesWithinOnBall f p s x r) (h : t subseteq s) :
    HasFPowerSeriesWithinOnBall f p t x r where
  r_le := hf.r_le
  r_pos := hf.r_pos
  hasSum hy h'y := hf.hasSum (insert_subset_insert h hy) h'y

/--
lemma `HasFPowerSeriesOnBall.hasFPowerSeriesWithinOnBall` / 引理 `HasFPowerSeriesOnBall.hasFPowerSeriesWithinOnBall`

English:
lemma HasFPowerSeriesOnBall.hasFPowerSeriesWithinOnBall
  given: (hf : HasFPowerSeriesOnBall f p x r)
  proof: by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  exact hf.mono (subset_univ _)

中文:
引理 HasFPowerSeriesOnBall.hasFPowerSeriesWithinOnBall
  条件: (hf : HasFPowerSeriesOnBall f p x r)
  证明: by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  exact hf.mono (subset_univ _)

Depends on / 依赖: hasFPowerSeriesWithinOnBall_univ, hf.mono, subset_univ
-/
lemma HasFPowerSeriesOnBall.hasFPowerSeriesWithinOnBall (hf : HasFPowerSeriesOnBall f p x r) :
    HasFPowerSeriesWithinOnBall f p s x r := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  exact hf.mono (subset_univ _)

/--
lemma `HasFPowerSeriesWithinAt.mono` / 引理 `HasFPowerSeriesWithinAt.mono`

English:
lemma HasFPowerSeriesWithinAt.mono
  given: (hf : HasFPowerSeriesWithinAt f p s x) (h : t subseteq s)
  proof: by
  obtain ⟨r, hp⟩ := hf
  exact ⟨r, hp.mono h⟩

中文:
引理 HasFPowerSeriesWithinAt.mono
  条件: (hf : HasFPowerSeriesWithinAt f p s x) (h : t subseteq s)
  证明: by
  obtain ⟨r, hp⟩ := hf
  exact ⟨r, hp.mono h⟩

Depends on / 依赖: hp.mono
-/
lemma HasFPowerSeriesWithinAt.mono (hf : HasFPowerSeriesWithinAt f p s x) (h : t subseteq s) :
    HasFPowerSeriesWithinAt f p t x := by
  obtain ⟨r, hp⟩ := hf
  exact ⟨r, hp.mono h⟩

/--
lemma `HasFPowerSeriesAt.hasFPowerSeriesWithinAt` / 引理 `HasFPowerSeriesAt.hasFPowerSeriesWithinAt`

English:
lemma HasFPowerSeriesAt.hasFPowerSeriesWithinAt
  given: (hf : HasFPowerSeriesAt f p x)
  proof: by
  rw [← hasFPowerSeriesWithinAt_univ] at hf
  apply hf.mono (subset_univ _)

中文:
引理 HasFPowerSeriesAt.hasFPowerSeriesWithinAt
  条件: (hf : HasFPowerSeriesAt f p x)
  证明: by
  rw [← hasFPowerSeriesWithinAt_univ] at hf
  apply hf.mono (subset_univ _)

Depends on / 依赖: hasFPowerSeriesWithinAt_univ, hf.mono, subset_univ
-/
lemma HasFPowerSeriesAt.hasFPowerSeriesWithinAt (hf : HasFPowerSeriesAt f p x) :
    HasFPowerSeriesWithinAt f p s x := by
  rw [← hasFPowerSeriesWithinAt_univ] at hf
  apply hf.mono (subset_univ _)

/--
theorem `HasFPowerSeriesWithinAt.mono_of_mem_nhdsWithin` / 定理 `HasFPowerSeriesWithinAt.mono_of_mem_nhdsWithin`

English:
theorem HasFPowerSeriesWithinAt.mono_of_mem_nhdsWithin
  proof: by
  rcases h with ⟨r, hr⟩
  rcases EMetric.mem_nhdsWithin_iff.1 hst with ⟨r', r'_pos, hr'⟩
  refine ⟨min r r', ?_⟩
  have Z := hr.of_le (by simp [r'_pos, hr.r_pos]) (min_le_left r r')
  refine ⟨Z.r_le, Z.r_pos, fun {y} hy h'y => ?_⟩
  apply Z.hasSum ?_ h'y
  simp only [mem_insert_iff, add_eq_left] 

中文:
定理 HasFPowerSeriesWithinAt.mono_of_mem_nhdsWithin
  证明: by
  rcases h with ⟨r, hr⟩
  rcases EMetric.mem_nhdsWithin_iff.1 hst with ⟨r', r'_pos, hr'⟩
  refine ⟨min r r', ?_⟩
  have Z := hr.of_le (by simp [r'_pos, hr.r_pos]) (min_le_left r r')
  refine ⟨Z.r_le, Z.r_pos, fun {y} hy h'y => ?_⟩
  apply Z.hasSum ?_ h'y
  simp only [mem_insert_iff, add_eq_left] 

Depends on / 依赖: EMetric, EMetric.mem_nhdsWithin_iff, Metric, Metric.mem_eball, Z.hasSum, Z.r_le, Z.r_pos, _pos, add_eq_left, add_sub_cancel_left, and_true, edist_eq_enorm_sub, hasSum, hr.of_le, hr.r_pos, lt_min_iff, mem_eball, mem_insert_iff, mem_insert_of_mem, mem_inter_iff
-/
theorem HasFPowerSeriesWithinAt.mono_of_mem_nhdsWithin
    (h : HasFPowerSeriesWithinAt f p s x) (hst : s in 𝓝[t] x) :
    HasFPowerSeriesWithinAt f p t x := by
  rcases h with ⟨r, hr⟩
  rcases EMetric.mem_nhdsWithin_iff.1 hst with ⟨r', r'_pos, hr'⟩
  refine ⟨min r r', ?_⟩
  have Z := hr.of_le (by simp [r'_pos, hr.r_pos]) (min_le_left r r')
  refine ⟨Z.r_le, Z.r_pos, fun {y} hy h'y => ?_⟩
  apply Z.hasSum ?_ h'y
  simp only [mem_insert_iff, add_eq_left] at hy
  rcases hy with rfl | hy
  · simp
  apply mem_insert_of_mem _ (hr' ?_)
  simp only [Metric.mem_eball, edist_eq_enorm_sub, sub_zero, lt_min_iff, mem_inter_iff,
    add_sub_cancel_left, hy, and_true] at h'y ⊢
  exact h'y.2

/--
lemma `hasFPowerSeriesWithinAt_iff_of_nhds` / 引理 `hasFPowerSeriesWithinAt_iff_of_nhds`

English:
lemma hasFPowerSeriesWithinAt_iff_of_nhds
  statement: (f : E -> F) (p : FormalMultilinearSeries 𝕜 E F)
  proof: by
  rw [← hasFPowerSeriesWithinAt_univ]
  exact ⟨fun h => h.mono_of_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds hU),
    fun h => h.mono (subset_univ _)⟩

中文:
引理 hasFPowerSeriesWithinAt_iff_of_nhds
  结论: (f : E -> F) (p : FormalMultilinearSeries 𝕜 E F)
  证明: by
  rw [← hasFPowerSeriesWithinAt_univ]
  exact ⟨fun h => h.mono_of_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds hU),
    fun h => h.mono (subset_univ _)⟩

Depends on / 依赖: h.mono, h.mono_of_mem_nhdsWithin, hasFPowerSeriesWithinAt_univ, mem_nhdsWithin_of_mem_nhds, mono_of_mem_nhdsWithin, subset_univ
-/
lemma hasFPowerSeriesWithinAt_iff_of_nhds (f : E -> F) (p : FormalMultilinearSeries 𝕜 E F)
    {U : Set E} (hU : U in 𝓝 x) :
    HasFPowerSeriesWithinAt f p U x ↔ HasFPowerSeriesAt f p x := by
  rw [← hasFPowerSeriesWithinAt_univ]
  exact ⟨fun h => h.mono_of_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds hU),
    fun h => h.mono (subset_univ _)⟩

/--
lemma `hasFPowerSeriesWithinOnBall_insert_self` / 引理 `hasFPowerSeriesWithinOnBall_insert_self`

English:
lemma hasFPowerSeriesWithinOnBall_insert_self
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩ <;>
  exact ⟨h.r_le, h.r_pos, fun {y} => by simpa only [insert_idem] using h.hasSum (y := y)⟩

中文:
引理 hasFPowerSeriesWithinOnBall_insert_self
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩ <;>
  exact ⟨h.r_le, h.r_pos, fun {y} => by simpa only [insert_idem] using h.hasSum (y := y)⟩
-/
@[simp] lemma hasFPowerSeriesWithinOnBall_insert_self :
    HasFPowerSeriesWithinOnBall f p (insert x s) x r ↔ HasFPowerSeriesWithinOnBall f p s x r := by
  refine ⟨fun h => ?_, fun h => ?_⟩ <;>
  exact ⟨h.r_le, h.r_pos, fun {y} => by simpa only [insert_idem] using h.hasSum (y := y)⟩

/--
theorem `hasFPowerSeriesWithinAt_insert` / 定理 `hasFPowerSeriesWithinAt_insert`

English:
theorem hasFPowerSeriesWithinAt_insert
  given: {y : E}
  proof: by
  rcases eq_or_ne x y with rfl | hy
  · simp [HasFPowerSeriesWithinAt]
  · refine ⟨fun h => h.mono (subset_insert _ _), fun h => ?_⟩
    apply HasFPowerSeriesWithinAt.mono_of_mem_nhdsWithin h
    rw [nhdsWithin_insert_of_ne hy]
    exact self_mem_nhdsWithin

中文:
定理 hasFPowerSeriesWithinAt_insert
  条件: {y : E}
  证明: by
  rcases eq_or_ne x y with rfl | hy
  · simp [HasFPowerSeriesWithinAt]
  · refine ⟨fun h => h.mono (subset_insert _ _), fun h => ?_⟩
    apply HasFPowerSeriesWithinAt.mono_of_mem_nhdsWithin h
    rw [nhdsWithin_insert_of_ne hy]
    exact self_mem_nhdsWithin
-/
@[simp] theorem hasFPowerSeriesWithinAt_insert {y : E} :
    HasFPowerSeriesWithinAt f p (insert y s) x ↔ HasFPowerSeriesWithinAt f p s x := by
  rcases eq_or_ne x y with rfl | hy
  · simp [HasFPowerSeriesWithinAt]
  · refine ⟨fun h => h.mono (subset_insert _ _), fun h => ?_⟩
    apply HasFPowerSeriesWithinAt.mono_of_mem_nhdsWithin h
    rw [nhdsWithin_insert_of_ne hy]
    exact self_mem_nhdsWithin

/--
theorem `HasFPowerSeriesWithinOnBall.coeff_zero` / 定理 `HasFPowerSeriesWithinOnBall.coeff_zero`

English:
theorem HasFPowerSeriesWithinOnBall.coeff_zero
  statement: (hf : HasFPowerSeriesWithinOnBall f pf s x r)
  proof: by
  have v_eq : v = fun i => 0 := Subsingleton.elim _ _
  have zero_mem : (0 : E) in Metric.eball (0 : E) r := by simp [hf.r_pos]
  have : forall i, i != 0 -> (pf i fun _ => 0) = 0 := by
    intro i hi
    have : 0 < i := pos_iff_ne_zero.2 hi
    exact ContinuousMultilinearMap.map_coord_zero _ (⟨0,

中文:
定理 HasFPowerSeriesWithinOnBall.coeff_zero
  结论: (hf : HasFPowerSeriesWithinOnBall f pf s x r)
  证明: by
  have v_eq : v = fun i => 0 := Subsingleton.elim _ _
  have zero_mem : (0 : E) in Metric.eball (0 : E) r := by simp [hf.r_pos]
  have : forall i, i != 0 -> (pf i fun _ => 0) = 0 := by
    intro i hi
    have : 0 < i := pos_iff_ne_zero.2 hi
    exact ContinuousMultilinearMap.map_coord_zero _ (⟨0,

Depends on / 依赖: A.symm, ContinuousMultilinearMap, ContinuousMultilinearMap.map_coord_zero, Metric, Metric.eball, Subsingleton, Subsingleton.elim, hasSum, hasSum_single, hf.hasSum, hf.r_pos, map_coord_zero, pos_iff_ne_zero, r_pos, unique, v_eq, zero_mem
-/
theorem HasFPowerSeriesWithinOnBall.coeff_zero (hf : HasFPowerSeriesWithinOnBall f pf s x r)
    (v : Fin 0 -> E) : pf 0 v = f x := by
  have v_eq : v = fun i => 0 := Subsingleton.elim _ _
  have zero_mem : (0 : E) in Metric.eball (0 : E) r := by simp [hf.r_pos]
  have : forall i, i != 0 -> (pf i fun _ => 0) = 0 := by
    intro i hi
    have : 0 < i := pos_iff_ne_zero.2 hi
    exact ContinuousMultilinearMap.map_coord_zero _ (⟨0, this⟩ : Fin i) rfl
  have A := (hf.hasSum (by simp) zero_mem).unique (hasSum_single _ this)
  simpa [v_eq] using A.symm

/--
theorem `HasFPowerSeriesOnBall.coeff_zero` / 定理 `HasFPowerSeriesOnBall.coeff_zero`

English:
theorem HasFPowerSeriesOnBall.coeff_zero
  statement: (hf : HasFPowerSeriesOnBall f pf x r)
  proof: by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  exact hf.coeff_zero v

中文:
定理 HasFPowerSeriesOnBall.coeff_zero
  结论: (hf : HasFPowerSeriesOnBall f pf x r)
  证明: by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  exact hf.coeff_zero v

Depends on / 依赖: coeff_zero, hasFPowerSeriesWithinOnBall_univ, hf.coeff_zero
-/
theorem HasFPowerSeriesOnBall.coeff_zero (hf : HasFPowerSeriesOnBall f pf x r)
    (v : Fin 0 -> E) : pf 0 v = f x := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  exact hf.coeff_zero v

/--
theorem `HasFPowerSeriesWithinAt.coeff_zero` / 定理 `HasFPowerSeriesWithinAt.coeff_zero`

English:
theorem HasFPowerSeriesWithinAt.coeff_zero
  given: (hf : HasFPowerSeriesWithinAt f pf s x) (v : Fin 0 -> E)
  proof: let ⟨_, hrf⟩ := hf
  hrf.coeff_zero v

中文:
定理 HasFPowerSeriesWithinAt.coeff_zero
  条件: (hf : HasFPowerSeriesWithinAt f pf s x) (v : Fin 0 -> E)
  证明: let ⟨_, hrf⟩ := hf
  hrf.coeff_zero v

Depends on / 依赖: coeff_zero, hrf.coeff_zero
-/
theorem HasFPowerSeriesWithinAt.coeff_zero (hf : HasFPowerSeriesWithinAt f pf s x) (v : Fin 0 -> E) :
    pf 0 v = f x :=
  let ⟨_, hrf⟩ := hf
  hrf.coeff_zero v

/--
theorem `HasFPowerSeriesAt.coeff_zero` / 定理 `HasFPowerSeriesAt.coeff_zero`

English:
theorem HasFPowerSeriesAt.coeff_zero
  given: (hf : HasFPowerSeriesAt f pf x) (v : Fin 0 -> E)
  proof: let ⟨_, hrf⟩ := hf
  hrf.coeff_zero v

中文:
定理 HasFPowerSeriesAt.coeff_zero
  条件: (hf : HasFPowerSeriesAt f pf x) (v : Fin 0 -> E)
  证明: let ⟨_, hrf⟩ := hf
  hrf.coeff_zero v

Depends on / 依赖: coeff_zero, hrf.coeff_zero
-/
theorem HasFPowerSeriesAt.coeff_zero (hf : HasFPowerSeriesAt f pf x) (v : Fin 0 -> E) :
    pf 0 v = f x :=
  let ⟨_, hrf⟩ := hf
  hrf.coeff_zero v


/--
theorem `analyticOn_empty` / 定理 `analyticOn_empty`

English:
theorem analyticOn_empty
  statement: AnalyticOn 𝕜 f ∅
  proof: by intro; simp

中文:
定理 analyticOn_empty
  结论: AnalyticOn 𝕜 f ∅
  证明: by intro; simp
-/
@[simp] theorem analyticOn_empty : AnalyticOn 𝕜 f ∅ := by intro; simp

/--
theorem `analyticOnNhd_empty` / 定理 `analyticOnNhd_empty`

English:
theorem analyticOnNhd_empty
  statement: AnalyticOnNhd 𝕜 f ∅
  proof: by intro; simp

中文:
定理 analyticOnNhd_empty
  结论: AnalyticOnNhd 𝕜 f ∅
  证明: by intro; simp
-/
@[simp] theorem analyticOnNhd_empty : AnalyticOnNhd 𝕜 f ∅ := by intro; simp

/--
lemma `analyticWithinAt_univ` / 引理 `analyticWithinAt_univ`

English:
lemma analyticWithinAt_univ
  proof: by
  simp [AnalyticWithinAt, AnalyticAt]

中文:
引理 analyticWithinAt_univ
  证明: by
  simp [AnalyticWithinAt, AnalyticAt]
-/
@[simp] lemma analyticWithinAt_univ :
    AnalyticWithinAt 𝕜 f univ x ↔ AnalyticAt 𝕜 f x := by
  simp [AnalyticWithinAt, AnalyticAt]

/--
lemma `analyticOn_univ` / 引理 `analyticOn_univ`

English:
lemma analyticOn_univ
  given: {f : E -> F}
  proof: by
  simp only [AnalyticOn, analyticWithinAt_univ, AnalyticOnNhd]

中文:
引理 analyticOn_univ
  条件: {f : E -> F}
  证明: by
  simp only [AnalyticOn, analyticWithinAt_univ, AnalyticOnNhd]
-/
@[simp] lemma analyticOn_univ {f : E -> F} :
    AnalyticOn 𝕜 f univ ↔ AnalyticOnNhd 𝕜 f univ := by
  simp only [AnalyticOn, analyticWithinAt_univ, AnalyticOnNhd]

/--
lemma `AnalyticWithinAt.mono` / 引理 `AnalyticWithinAt.mono`

English:
lemma AnalyticWithinAt.mono
  given: (hf : AnalyticWithinAt 𝕜 f s x) (h : t subseteq s)
  proof: by
  obtain ⟨p, hp⟩ := hf
  exact ⟨p, hp.mono h⟩

中文:
引理 AnalyticWithinAt.mono
  条件: (hf : AnalyticWithinAt 𝕜 f s x) (h : t subseteq s)
  证明: by
  obtain ⟨p, hp⟩ := hf
  exact ⟨p, hp.mono h⟩

Depends on / 依赖: hp.mono
-/
lemma AnalyticWithinAt.mono (hf : AnalyticWithinAt 𝕜 f s x) (h : t subseteq s) :
    AnalyticWithinAt 𝕜 f t x := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨p, hp.mono h⟩

/--
lemma `AnalyticAt.analyticWithinAt` / 引理 `AnalyticAt.analyticWithinAt`

English:
lemma AnalyticAt.analyticWithinAt
  given: (hf : AnalyticAt 𝕜 f x)
  statement: AnalyticWithinAt 𝕜 f s x
  proof: by
  rw [← analyticWithinAt_univ] at hf
  apply hf.mono (subset_univ _)

中文:
引理 AnalyticAt.analyticWithinAt
  条件: (hf : AnalyticAt 𝕜 f x)
  结论: AnalyticWithinAt 𝕜 f s x
  证明: by
  rw [← analyticWithinAt_univ] at hf
  apply hf.mono (subset_univ _)

Depends on / 依赖: analyticWithinAt_univ, hf.mono, subset_univ
-/
lemma AnalyticAt.analyticWithinAt (hf : AnalyticAt 𝕜 f x) : AnalyticWithinAt 𝕜 f s x := by
  rw [← analyticWithinAt_univ] at hf
  apply hf.mono (subset_univ _)

/--
lemma `AnalyticOnNhd.analyticOn` / 引理 `AnalyticOnNhd.analyticOn`

English:
lemma AnalyticOnNhd.analyticOn
  given: (hf : AnalyticOnNhd 𝕜 f s)
  statement: AnalyticOn 𝕜 f s
  proof: fun x hx => (hf x hx).analyticWithinAt

中文:
引理 AnalyticOnNhd.analyticOn
  条件: (hf : AnalyticOnNhd 𝕜 f s)
  结论: AnalyticOn 𝕜 f s
  证明: fun x hx => (hf x hx).analyticWithinAt

Depends on / 依赖: analyticWithinAt
-/
lemma AnalyticOnNhd.analyticOn (hf : AnalyticOnNhd 𝕜 f s) : AnalyticOn 𝕜 f s :=
  fun x hx => (hf x hx).analyticWithinAt

/--
lemma `AnalyticWithinAt.congr_of_eventuallyEq` / 引理 `AnalyticWithinAt.congr_of_eventuallyEq`

English:
lemma AnalyticWithinAt.congr_of_eventuallyEq
  statement: {f g : E -> F} {s : Set E} {x : E}
  proof: by
  rcases hf with ⟨p, hp⟩
  exact ⟨p, hp.congr hs hx⟩

中文:
引理 AnalyticWithinAt.congr_of_eventuallyEq
  结论: {f g : E -> F} {s : Set E} {x : E}
  证明: by
  rcases hf with ⟨p, hp⟩
  exact ⟨p, hp.congr hs hx⟩

Depends on / 依赖: hp.congr
-/
lemma AnalyticWithinAt.congr_of_eventuallyEq {f g : E -> F} {s : Set E} {x : E}
    (hf : AnalyticWithinAt 𝕜 f s x) (hs : g =ᶠ[𝓝[s] x] f) (hx : g x = f x) :
    AnalyticWithinAt 𝕜 g s x := by
  rcases hf with ⟨p, hp⟩
  exact ⟨p, hp.congr hs hx⟩

/--
lemma `AnalyticWithinAt.congr_of_eventuallyEq_insert` / 引理 `AnalyticWithinAt.congr_of_eventuallyEq_insert`

English:
lemma AnalyticWithinAt.congr_of_eventuallyEq_insert
  statement: {f g : E -> F} {s : Set E} {x : E}
  proof: by
  apply hf.congr_of_eventuallyEq (nhdsWithin_mono x (subset_insert x s) hs)
  apply mem_of_mem_nhdsWithin (mem_insert x s) hs

中文:
引理 AnalyticWithinAt.congr_of_eventuallyEq_insert
  结论: {f g : E -> F} {s : Set E} {x : E}
  证明: by
  apply hf.congr_of_eventuallyEq (nhdsWithin_mono x (subset_insert x s) hs)
  apply mem_of_mem_nhdsWithin (mem_insert x s) hs

Depends on / 依赖: congr_of_eventuallyEq, hf.congr_of_eventuallyEq, mem_insert, mem_of_mem_nhdsWithin, nhdsWithin_mono, subset_insert
-/
lemma AnalyticWithinAt.congr_of_eventuallyEq_insert {f g : E -> F} {s : Set E} {x : E}
    (hf : AnalyticWithinAt 𝕜 f s x) (hs : g =ᶠ[𝓝[insert x s] x] f) :
    AnalyticWithinAt 𝕜 g s x := by
  apply hf.congr_of_eventuallyEq (nhdsWithin_mono x (subset_insert x s) hs)
  apply mem_of_mem_nhdsWithin (mem_insert x s) hs

/--
lemma `AnalyticWithinAt.congr` / 引理 `AnalyticWithinAt.congr`

English:
lemma AnalyticWithinAt.congr
  statement: {f g : E -> F} {s : Set E} {x : E}
  proof: hf.congr_of_eventuallyEq hs.eventuallyEq_nhdsWithin hx

中文:
引理 AnalyticWithinAt.congr
  结论: {f g : E -> F} {s : Set E} {x : E}
  证明: hf.congr_of_eventuallyEq hs.eventuallyEq_nhdsWithin hx

Depends on / 依赖: congr_of_eventuallyEq, eventuallyEq_nhdsWithin, hf.congr_of_eventuallyEq, hs.eventuallyEq_nhdsWithin
-/
lemma AnalyticWithinAt.congr {f g : E -> F} {s : Set E} {x : E}
    (hf : AnalyticWithinAt 𝕜 f s x) (hs : EqOn g f s) (hx : g x = f x) :
    AnalyticWithinAt 𝕜 g s x :=
  hf.congr_of_eventuallyEq hs.eventuallyEq_nhdsWithin hx

/--
lemma `AnalyticOn.congr` / 引理 `AnalyticOn.congr`

English:
lemma AnalyticOn.congr
  statement: {f g : E -> F} {s : Set E}
  proof: fun x m => (hf x m).congr hs (hs m)

中文:
引理 AnalyticOn.congr
  结论: {f g : E -> F} {s : Set E}
  证明: fun x m => (hf x m).congr hs (hs m)
-/
lemma AnalyticOn.congr {f g : E -> F} {s : Set E}
    (hf : AnalyticOn 𝕜 f s) (hs : EqOn g f s) :
    AnalyticOn 𝕜 g s :=
  fun x m => (hf x m).congr hs (hs m)

/--
lemma `analyticOn_congr` / 引理 `analyticOn_congr`

English:
lemma analyticOn_congr
  given: (hs : EqOn f g s)
  statement: AnalyticOn 𝕜 f s ↔ AnalyticOn 𝕜 g s
  proof: ⟨fun h => h.congr hs.symm, fun h => h.congr hs⟩

中文:
引理 analyticOn_congr
  条件: (hs : EqOn f g s)
  结论: AnalyticOn 𝕜 f s ↔ AnalyticOn 𝕜 g s
  证明: ⟨fun h => h.congr hs.symm, fun h => h.congr hs⟩

Depends on / 依赖: h.congr, hs.symm
-/
lemma analyticOn_congr (hs : EqOn f g s) : AnalyticOn 𝕜 f s ↔ AnalyticOn 𝕜 g s :=
  ⟨fun h => h.congr hs.symm, fun h => h.congr hs⟩

/--
theorem `AnalyticAt.congr` / 定理 `AnalyticAt.congr`

English:
theorem AnalyticAt.congr
  given: (hf : AnalyticAt 𝕜 f x) (hg : f =ᶠ[𝓝 x] g)
  statement: AnalyticAt 𝕜 g x
  proof: let ⟨_, hpf⟩ := hf
  (hpf.congr hg).analyticAt

中文:
定理 AnalyticAt.congr
  条件: (hf : AnalyticAt 𝕜 f x) (hg : f =ᶠ[𝓝 x] g)
  结论: AnalyticAt 𝕜 g x
  证明: let ⟨_, hpf⟩ := hf
  (hpf.congr hg).analyticAt

Depends on / 依赖: analyticAt, hpf.congr
-/
theorem AnalyticAt.congr (hf : AnalyticAt 𝕜 f x) (hg : f =ᶠ[𝓝 x] g) : AnalyticAt 𝕜 g x :=
  let ⟨_, hpf⟩ := hf
  (hpf.congr hg).analyticAt

/--
theorem `analyticAt_congr` / 定理 `analyticAt_congr`

English:
theorem analyticAt_congr
  given: (h : f =ᶠ[𝓝 x] g)
  statement: AnalyticAt 𝕜 f x ↔ AnalyticAt 𝕜 g x
  proof: ⟨fun hf => hf.congr h, fun hg => hg.congr h.symm⟩

中文:
定理 analyticAt_congr
  条件: (h : f =ᶠ[𝓝 x] g)
  结论: AnalyticAt 𝕜 f x ↔ AnalyticAt 𝕜 g x
  证明: ⟨fun hf => hf.congr h, fun hg => hg.congr h.symm⟩

Depends on / 依赖: h.symm, hf.congr, hg.congr
-/
theorem analyticAt_congr (h : f =ᶠ[𝓝 x] g) : AnalyticAt 𝕜 f x ↔ AnalyticAt 𝕜 g x :=
  ⟨fun hf => hf.congr h, fun hg => hg.congr h.symm⟩

/--
theorem `AnalyticOnNhd.mono` / 定理 `AnalyticOnNhd.mono`

English:
theorem AnalyticOnNhd.mono
  given: {s t : Set E} (hf : AnalyticOnNhd 𝕜 f t) (hst : s subseteq t)
  proof: fun z hz => hf z (hst hz)

中文:
定理 AnalyticOnNhd.mono
  条件: {s t : Set E} (hf : AnalyticOnNhd 𝕜 f t) (hst : s subseteq t)
  证明: fun z hz => hf z (hst hz)
-/
theorem AnalyticOnNhd.mono {s t : Set E} (hf : AnalyticOnNhd 𝕜 f t) (hst : s subseteq t) :
    AnalyticOnNhd 𝕜 f s :=
  fun z hz => hf z (hst hz)

/--
theorem `AnalyticOnNhd.congr'` / 定理 `AnalyticOnNhd.congr'`

English:
theorem AnalyticOnNhd.congr'
  given: (hf : AnalyticOnNhd 𝕜 f s) (hg : f =ᶠ[𝓝ˢ s] g)
  proof: fun z hz => (hf z hz).congr (mem_nhdsSet_iff_forall.mp hg z hz)

中文:
定理 AnalyticOnNhd.congr'
  条件: (hf : AnalyticOnNhd 𝕜 f s) (hg : f =ᶠ[𝓝ˢ s] g)
  证明: fun z hz => (hf z hz).congr (mem_nhdsSet_iff_forall.mp hg z hz)

Depends on / 依赖: mem_nhdsSet_iff_forall, mem_nhdsSet_iff_forall.mp
-/
theorem AnalyticOnNhd.congr' (hf : AnalyticOnNhd 𝕜 f s) (hg : f =ᶠ[𝓝ˢ s] g) :
    AnalyticOnNhd 𝕜 g s :=
  fun z hz => (hf z hz).congr (mem_nhdsSet_iff_forall.mp hg z hz)

/--
theorem `analyticOnNhd_congr'` / 定理 `analyticOnNhd_congr'`

English:
theorem analyticOnNhd_congr'
  given: (h : f =ᶠ[𝓝ˢ s] g)
  statement: AnalyticOnNhd 𝕜 f s ↔ AnalyticOnNhd 𝕜 g s
  proof: ⟨fun hf => hf.congr' h, fun hg => hg.congr' h.symm⟩

中文:
定理 analyticOnNhd_congr'
  条件: (h : f =ᶠ[𝓝ˢ s] g)
  结论: AnalyticOnNhd 𝕜 f s ↔ AnalyticOnNhd 𝕜 g s
  证明: ⟨fun hf => hf.congr' h, fun hg => hg.congr' h.symm⟩

Depends on / 依赖: h.symm, hf.congr, hg.congr
-/
theorem analyticOnNhd_congr' (h : f =ᶠ[𝓝ˢ s] g) : AnalyticOnNhd 𝕜 f s ↔ AnalyticOnNhd 𝕜 g s :=
  ⟨fun hf => hf.congr' h, fun hg => hg.congr' h.symm⟩

/--
theorem `AnalyticOnNhd.congr` / 定理 `AnalyticOnNhd.congr`

English:
theorem AnalyticOnNhd.congr
  given: (hs : IsOpen s) (hf : AnalyticOnNhd 𝕜 f s) (hg : s.EqOn f g)
  proof: hf.congr' mem_nhdsSet_iff_forall.mpr
    (fun _ hz => eventuallyEq_iff_exists_mem.mpr ⟨s, hs.mem_nhds hz, hg⟩)

中文:
定理 AnalyticOnNhd.congr
  条件: (hs : IsOpen s) (hf : AnalyticOnNhd 𝕜 f s) (hg : s.EqOn f g)
  证明: hf.congr' mem_nhdsSet_iff_forall.mpr
    (fun _ hz => eventuallyEq_iff_exists_mem.mpr ⟨s, hs.mem_nhds hz, hg⟩)

Depends on / 依赖: eventuallyEq_iff_exists_mem, eventuallyEq_iff_exists_mem.mpr, hf.congr, hs.mem_nhds, mem_nhds, mem_nhdsSet_iff_forall, mem_nhdsSet_iff_forall.mpr
-/
theorem AnalyticOnNhd.congr (hs : IsOpen s) (hf : AnalyticOnNhd 𝕜 f s) (hg : s.EqOn f g) :
    AnalyticOnNhd 𝕜 g s :=
hf.congr' mem_nhdsSet_iff_forall.mpr
    (fun _ hz => eventuallyEq_iff_exists_mem.mpr ⟨s, hs.mem_nhds hz, hg⟩)

/--
theorem `analyticOnNhd_congr` / 定理 `analyticOnNhd_congr`

English:
theorem analyticOnNhd_congr
  given: (hs : IsOpen s) (h : s.EqOn f g)
  statement: AnalyticOnNhd 𝕜 f s ↔
  proof: ⟨fun hf => hf.congr hs h, fun hg => hg.congr hs h.symm⟩

中文:
定理 analyticOnNhd_congr
  条件: (hs : IsOpen s) (h : s.EqOn f g)
  结论: AnalyticOnNhd 𝕜 f s ↔
  证明: ⟨fun hf => hf.congr hs h, fun hg => hg.congr hs h.symm⟩

Depends on / 依赖: h.symm, hf.congr, hg.congr
-/
theorem analyticOnNhd_congr (hs : IsOpen s) (h : s.EqOn f g) : AnalyticOnNhd 𝕜 f s ↔
    AnalyticOnNhd 𝕜 g s := ⟨fun hf => hf.congr hs h, fun hg => hg.congr hs h.symm⟩

/--
theorem `AnalyticWithinAt.mono_of_mem_nhdsWithin` / 定理 `AnalyticWithinAt.mono_of_mem_nhdsWithin`

English:
theorem AnalyticWithinAt.mono_of_mem_nhdsWithin
  proof: by
  rcases h with ⟨p, hp⟩
  exact ⟨p, hp.mono_of_mem_nhdsWithin hst⟩

中文:
定理 AnalyticWithinAt.mono_of_mem_nhdsWithin
  证明: by
  rcases h with ⟨p, hp⟩
  exact ⟨p, hp.mono_of_mem_nhdsWithin hst⟩

Depends on / 依赖: hp.mono_of_mem_nhdsWithin, mono_of_mem_nhdsWithin
-/
theorem AnalyticWithinAt.mono_of_mem_nhdsWithin
    (h : AnalyticWithinAt 𝕜 f s x) (hst : s in 𝓝[t] x) : AnalyticWithinAt 𝕜 f t x := by
  rcases h with ⟨p, hp⟩
  exact ⟨p, hp.mono_of_mem_nhdsWithin hst⟩

/--
theorem `AnalyticWithinAt.congr_set` / 定理 `AnalyticWithinAt.congr_set`

English:
theorem AnalyticWithinAt.congr_set
  given: (h : AnalyticWithinAt 𝕜 f s x) (hst : s =ᶠ[𝓝 x] t)
  proof: by
  refine h.mono_of_mem_nhdsWithin ?_
  simp [← nhdsWithin_eq_iff_eventuallyEq.mpr hst, self_mem_nhdsWithin]

中文:
定理 AnalyticWithinAt.congr_set
  条件: (h : AnalyticWithinAt 𝕜 f s x) (hst : s =ᶠ[𝓝 x] t)
  证明: by
  refine h.mono_of_mem_nhdsWithin ?_
  simp [← nhdsWithin_eq_iff_eventuallyEq.mpr hst, self_mem_nhdsWithin]

Depends on / 依赖: h.mono_of_mem_nhdsWithin, mono_of_mem_nhdsWithin, nhdsWithin_eq_iff_eventuallyEq, nhdsWithin_eq_iff_eventuallyEq.mpr, self_mem_nhdsWithin
-/
theorem AnalyticWithinAt.congr_set (h : AnalyticWithinAt 𝕜 f s x) (hst : s =ᶠ[𝓝 x] t) :
    AnalyticWithinAt 𝕜 f t x := by
  refine h.mono_of_mem_nhdsWithin ?_
  simp [← nhdsWithin_eq_iff_eventuallyEq.mpr hst, self_mem_nhdsWithin]

/--
lemma `AnalyticOn.mono` / 引理 `AnalyticOn.mono`

English:
lemma AnalyticOn.mono
  statement: {f : E -> F} {s t : Set E} (h : AnalyticOn 𝕜 f t)
  proof: fun _ m => (h _ (hs m)).mono hs

中文:
引理 AnalyticOn.mono
  结论: {f : E -> F} {s t : Set E} (h : AnalyticOn 𝕜 f t)
  证明: fun _ m => (h _ (hs m)).mono hs
-/
lemma AnalyticOn.mono {f : E -> F} {s t : Set E} (h : AnalyticOn 𝕜 f t)
    (hs : s subseteq t) : AnalyticOn 𝕜 f s :=
  fun _ m => (h _ (hs m)).mono hs

/--
theorem `analyticWithinAt_insert` / 定理 `analyticWithinAt_insert`

English:
theorem analyticWithinAt_insert
  given: {f : E -> F} {s : Set E} {x y : E}
  proof: by
  simp [AnalyticWithinAt]

中文:
定理 analyticWithinAt_insert
  条件: {f : E -> F} {s : Set E} {x y : E}
  证明: by
  simp [AnalyticWithinAt]
-/
@[simp] theorem analyticWithinAt_insert {f : E -> F} {s : Set E} {x y : E} :
    AnalyticWithinAt 𝕜 f (insert y s) x ↔ AnalyticWithinAt 𝕜 f s x := by
  simp [AnalyticWithinAt]

/--
lemma `AnalyticOn.analyticAt` / 引理 `AnalyticOn.analyticAt`

English:
lemma AnalyticOn.analyticAt
  statement: {f : E -> F} {z : E} {s : Set E} (hU : s in 𝓝 z)
  proof: by
  obtain ⟨p, hp⟩ := h z (mem_of_mem_nhds hU)
.mp hp⟩ exact ⟨p, hasFPowerSeriesWithinAt_iff_of_nhds f p hU

中文:
引理 AnalyticOn.analyticAt
  结论: {f : E -> F} {z : E} {s : Set E} (hU : s in 𝓝 z)
  证明: by
  obtain ⟨p, hp⟩ := h z (mem_of_mem_nhds hU)
.mp hp⟩ exact ⟨p, hasFPowerSeriesWithinAt_iff_of_nhds f p hU

Depends on / 依赖: hasFPowerSeriesWithinAt_iff_of_nhds, mem_of_mem_nhds
-/
lemma AnalyticOn.analyticAt {f : E -> F} {z : E} {s : Set E} (hU : s in 𝓝 z)
    (h : AnalyticOn 𝕜 f s) : AnalyticAt 𝕜 f z := by
  obtain ⟨p, hp⟩ := h z (mem_of_mem_nhds hU)
.mp hp⟩ exact ⟨p, hasFPowerSeriesWithinAt_iff_of_nhds f p hU

/-!
### Composition with linear maps
-/

/--
theorem `ContinuousLinearMap.comp_hasFPowerSeriesWithinOnBall` / 定理 `ContinuousLinearMap.comp_hasFPowerSeriesWithinOnBall`

English:
theorem ContinuousLinearMap.comp_hasFPowerSeriesWithinOnBall
  statement: (g : F ->L[𝕜] G)
  proof: h.r_le.trans (p.radius_le_radius_continuousLinearMap_comp _)
  r_pos := h.r_pos
  hasSum hy h'y := by
    simpa only [ContinuousLinearMap.compFormalMultilinearSeries_apply,
      ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply] using
      g.hasSum (h.hasSum hy h'y)

中文:
定理 ContinuousLinearMap.comp_hasFPowerSeriesWithinOnBall
  结论: (g : F ->L[𝕜] G)
  证明: h.r_le.trans (p.radius_le_radius_continuousLinearMap_comp _)
  r_pos := h.r_pos
  hasSum hy h'y := by
    simpa only [ContinuousLinearMap.compFormalMultilinearSeries_apply,
      ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply] using
      g.hasSum (h.hasSum hy h'y)

Depends on / 依赖: h.r_le.trans, p.radius_le_radius_continuousLinearMap_comp, r_le, radius_le_radius_continuousLinearMap_comp
-/
theorem ContinuousLinearMap.comp_hasFPowerSeriesWithinOnBall (g : F ->L[𝕜] G)
    (h : HasFPowerSeriesWithinOnBall f p s x r) :
    HasFPowerSeriesWithinOnBall (g ∘ f) (g.compFormalMultilinearSeries p) s x r where
  r_le := h.r_le.trans (p.radius_le_radius_continuousLinearMap_comp _)
  r_pos := h.r_pos
  hasSum hy h'y := by
    simpa only [ContinuousLinearMap.compFormalMultilinearSeries_apply,
      ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply] using
      g.hasSum (h.hasSum hy h'y)

/--
theorem `ContinuousLinearMap.comp_hasFPowerSeriesOnBall` / 定理 `ContinuousLinearMap.comp_hasFPowerSeriesOnBall`

English:
theorem ContinuousLinearMap.comp_hasFPowerSeriesOnBall
  statement: (g : F ->L[𝕜] G)
  proof: by
  rw [← hasFPowerSeriesWithinOnBall_univ] at h ⊢
  exact g.comp_hasFPowerSeriesWithinOnBall h

中文:
定理 ContinuousLinearMap.comp_hasFPowerSeriesOnBall
  结论: (g : F ->L[𝕜] G)
  证明: by
  rw [← hasFPowerSeriesWithinOnBall_univ] at h ⊢
  exact g.comp_hasFPowerSeriesWithinOnBall h

Depends on / 依赖: comp_hasFPowerSeriesWithinOnBall, g.comp_hasFPowerSeriesWithinOnBall, hasFPowerSeriesWithinOnBall_univ
-/
theorem ContinuousLinearMap.comp_hasFPowerSeriesOnBall (g : F ->L[𝕜] G)
    (h : HasFPowerSeriesOnBall f p x r) :
    HasFPowerSeriesOnBall (g ∘ f) (g.compFormalMultilinearSeries p) x r := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at h ⊢
  exact g.comp_hasFPowerSeriesWithinOnBall h

/--
theorem `ContinuousLinearMap.comp_analyticOn` / 定理 `ContinuousLinearMap.comp_analyticOn`

English:
theorem ContinuousLinearMap.comp_analyticOn
  given: (g : F ->L[𝕜] G) (h : AnalyticOn 𝕜 f s)
  proof: by
  rintro x hx
  rcases h x hx with ⟨p, r, hp⟩
  exact ⟨g.compFormalMultilinearSeries p, r, g.comp_hasFPowerSeriesWithinOnBall hp⟩

中文:
定理 ContinuousLinearMap.comp_analyticOn
  条件: (g : F ->L[𝕜] G) (h : AnalyticOn 𝕜 f s)
  证明: by
  rintro x hx
  rcases h x hx with ⟨p, r, hp⟩
  exact ⟨g.compFormalMultilinearSeries p, r, g.comp_hasFPowerSeriesWithinOnBall hp⟩

Depends on / 依赖: compFormalMultilinearSeries, comp_hasFPowerSeriesWithinOnBall, g.compFormalMultilinearSeries, g.comp_hasFPowerSeriesWithinOnBall
-/
theorem ContinuousLinearMap.comp_analyticOn (g : F ->L[𝕜] G) (h : AnalyticOn 𝕜 f s) :
    AnalyticOn 𝕜 (g ∘ f) s := by
  rintro x hx
  rcases h x hx with ⟨p, r, hp⟩
  exact ⟨g.compFormalMultilinearSeries p, r, g.comp_hasFPowerSeriesWithinOnBall hp⟩

/--
theorem `ContinuousLinearMap.comp_analyticOnNhd` / 定理 `ContinuousLinearMap.comp_analyticOnNhd`

English:
theorem ContinuousLinearMap.comp_analyticOnNhd
  proof: by
  rintro x hx
  rcases h x hx with ⟨p, r, hp⟩
  exact ⟨g.compFormalMultilinearSeries p, r, g.comp_hasFPowerSeriesOnBall hp⟩

中文:
定理 ContinuousLinearMap.comp_analyticOnNhd
  证明: by
  rintro x hx
  rcases h x hx with ⟨p, r, hp⟩
  exact ⟨g.compFormalMultilinearSeries p, r, g.comp_hasFPowerSeriesOnBall hp⟩

Depends on / 依赖: compFormalMultilinearSeries, comp_hasFPowerSeriesOnBall, g.compFormalMultilinearSeries, g.comp_hasFPowerSeriesOnBall
-/
theorem ContinuousLinearMap.comp_analyticOnNhd
    {s : Set E} (g : F ->L[𝕜] G) (h : AnalyticOnNhd 𝕜 f s) :
    AnalyticOnNhd 𝕜 (g ∘ f) s := by
  rintro x hx
  rcases h x hx with ⟨p, r, hp⟩
  exact ⟨g.compFormalMultilinearSeries p, r, g.comp_hasFPowerSeriesOnBall hp⟩


/--
theorem `HasFPowerSeriesWithinOnBall.tendsto_partialSum` / 定理 `HasFPowerSeriesWithinOnBall.tendsto_partialSum`

English:
theorem HasFPowerSeriesWithinOnBall.tendsto_partialSum
  proof: (hf.hasSum h'y hy).tendsto_sum_nat

中文:
定理 HasFPowerSeriesWithinOnBall.tendsto_partialSum
  证明: (hf.hasSum h'y hy).tendsto_sum_nat

Depends on / 依赖: hasSum, hf.hasSum, tendsto_sum_nat
-/
theorem HasFPowerSeriesWithinOnBall.tendsto_partialSum
    (hf : HasFPowerSeriesWithinOnBall f p s x r) {y : E} (hy : y in Metric.eball (0 : E) r)
    (h'y : x + y in insert x s) :
    Tendsto (fun n => p.partialSum n y) atTop (𝓝 (f (x + y))) :=
  (hf.hasSum h'y hy).tendsto_sum_nat

/--
theorem `HasFPowerSeriesOnBall.tendsto_partialSum` / 定理 `HasFPowerSeriesOnBall.tendsto_partialSum`

English:
theorem HasFPowerSeriesOnBall.tendsto_partialSum
  proof: (hf.hasSum hy).tendsto_sum_nat

中文:
定理 HasFPowerSeriesOnBall.tendsto_partialSum
  证明: (hf.hasSum hy).tendsto_sum_nat

Depends on / 依赖: hasSum, hf.hasSum, tendsto_sum_nat
-/
theorem HasFPowerSeriesOnBall.tendsto_partialSum
    (hf : HasFPowerSeriesOnBall f p x r) {y : E} (hy : y in Metric.eball (0 : E) r) :
    Tendsto (fun n => p.partialSum n y) atTop (𝓝 (f (x + y))) :=
  (hf.hasSum hy).tendsto_sum_nat

/--
theorem `HasFPowerSeriesAt.tendsto_partialSum` / 定理 `HasFPowerSeriesAt.tendsto_partialSum`

English:
theorem HasFPowerSeriesAt.tendsto_partialSum
  proof: by
  rcases hf with ⟨r, hr⟩
  filter_upwards [Metric.eball_mem_nhds (0 : E) hr.r_pos] with y hy
  exact hr.tendsto_partialSum hy

中文:
定理 HasFPowerSeriesAt.tendsto_partialSum
  证明: by
  rcases hf with ⟨r, hr⟩
  filter_upwards [Metric.eball_mem_nhds (0 : E) hr.r_pos] with y hy
  exact hr.tendsto_partialSum hy

Depends on / 依赖: Metric, Metric.eball_mem_nhds, eball_mem_nhds, filter_upwards, hr.r_pos, hr.tendsto_partialSum, r_pos, tendsto_partialSum
-/
theorem HasFPowerSeriesAt.tendsto_partialSum
    (hf : HasFPowerSeriesAt f p x) :
    forallᶠ y in 𝓝 0, Tendsto (fun n => p.partialSum n y) atTop (𝓝 (f (x + y))) := by
  rcases hf with ⟨r, hr⟩
  filter_upwards [Metric.eball_mem_nhds (0 : E) hr.r_pos] with y hy
  exact hr.tendsto_partialSum hy

open Finset in
/--
theorem `HasFPowerSeriesWithinOnBall.tendsto_partialSum_prod` / 定理 `HasFPowerSeriesWithinOnBall.tendsto_partialSum_prod`

English:
theorem HasFPowerSeriesWithinOnBall.tendsto_partialSum_prod
  statement: {y : E}
  proof: by
  have A : Tendsto (fun (z : Nat × E) => p.partialSum z.1 y) (atTop ×ˢ 𝓝 y) (𝓝 (f (x + y))) := by
    apply (hf.tendsto_partialSum hy h'y).comp tendsto_fst
  suffices Tendsto (fun (z : Nat × E) => p.partialSum z.1 z.2 - p.partialSum z.1 y)
    (atTop ×ˢ 𝓝 y) (𝓝 0) by simpa using A.add this
  appl

中文:
定理 HasFPowerSeriesWithinOnBall.tendsto_partialSum_prod
  结论: {y : E}
  证明: by
  have A : Tendsto (fun (z : Nat × E) => p.partialSum z.1 y) (atTop ×ˢ 𝓝 y) (𝓝 (f (x + y))) := by
    apply (hf.tendsto_partialSum hy h'y).comp tendsto_fst
  suffices Tendsto (fun (z : Nat × E) => p.partialSum z.1 z.2 - p.partialSum z.1 y)
    (atTop ×ˢ 𝓝 y) (𝓝 0) by simpa using A.add this
  appl

Depends on / 依赖: A.add, ENNReal, ENNReal.lt_iff_exists_nnreal_btwn, Metric, Metric.tendsto_nhds, Tendsto, hf.tendsto_partialSum, lt_iff_exists_nnreal_btwn, p.partialSum, partialSum, tendsto_fst, tendsto_nhds, tendsto_partialSum
-/
theorem HasFPowerSeriesWithinOnBall.tendsto_partialSum_prod {y : E}
    (hf : HasFPowerSeriesWithinOnBall f p s x r) (hy : y in Metric.eball (0 : E) r)
    (h'y : x + y in insert x s) :
    Tendsto (fun (z : Nat × E) => p.partialSum z.1 z.2) (atTop ×ˢ 𝓝 y) (𝓝 (f (x + y))) := by
  have A : Tendsto (fun (z : Nat × E) => p.partialSum z.1 y) (atTop ×ˢ 𝓝 y) (𝓝 (f (x + y))) := by
    apply (hf.tendsto_partialSum hy h'y).comp tendsto_fst
  suffices Tendsto (fun (z : Nat × E) => p.partialSum z.1 z.2 - p.partialSum z.1 y)
    (atTop ×ˢ 𝓝 y) (𝓝 0) by simpa using A.add this
  apply Metric.tendsto_nhds.2 (fun ε εpos => ?_)
  obtain ⟨r', yr', r'r⟩ : exists (r' : Real>=0), ‖y‖₊ < r' ∧ r' < r := by
    simp at hy
    simpa using ENNReal.lt_iff_exists_nnreal_btwn.1 hy
  have yr'_2 : ‖y‖ < r' := by simpa [← coe_nnnorm] using yr'
  have S : Summable fun n => ‖p n‖ * ↑r' ^ n := p.summable_norm_mul_pow (r'r.trans_le hf.r_le)
  obtain ⟨k, hk⟩ : exists k, ∑' (n : Nat), ‖p (n + k)‖ * ↑r' ^ (n + k) < ε / 4 := by
    have : Tendsto (fun k => ∑' n, ‖p (n + k)‖ * ↑r' ^ (n + k)) atTop (𝓝 0) := by
      apply _root_.tendsto_sum_nat_add (f := fun n => ‖p n‖ * ↑r' ^ n)
    exact ((tendsto_order.1 this).2 _ (by linarith)).exists
  have A : forallᶠ (z : Nat × E) in atTop ×ˢ 𝓝 y,
      dist (p.partialSum k z.2) (p.partialSum k y) < ε / 4 := by
    have : ContinuousAt (fun z => p.partialSum k z) y := (p.partialSum_continuous k).continuousAt
    exact tendsto_snd (Metric.tendsto_nhds.1 this.tendsto (ε / 4) (by linarith))
  have B : forallᶠ (z : Nat × E) in atTop ×ˢ 𝓝 y, ‖z.2‖₊ < r' := by
    suffices forallᶠ (z : E) in 𝓝 y, ‖z‖₊ < r' from tendsto_snd this
    have : Metric.ball 0 r' in 𝓝 y := Metric.isOpen_ball.mem_nhds (by simpa using yr'_2)
    filter_upwards [this] with a ha using by simpa [← coe_nnnorm] using ha
  have C : forallᶠ (z : Nat × E) in atTop ×ˢ 𝓝 y, k <= z.1 := tendsto_fst (Ici_mem_atTop _)
  filter_upwards [A, B, C]
  rintro ⟨n, z⟩ hz h'z hkn
  simp only [dist_eq_norm, sub_zero] at hz ⊢
  have I (w : E) (hw : ‖w‖₊ < r') : ‖∑ i in Ico k n, p i (fun _ => w)‖ <= ε / 4 := calc
    ‖∑ i in Ico k n, p i (fun _ => w)‖
    _ = ‖∑ i in range (n - k), p (i + k) (fun _ => w)‖ := by
        rw [sum_Ico_eq_sum_range]
        congr with i
        rw [add_comm k]
    _ <= ∑ i in range (n - k), ‖p (i + k) (fun _ => w)‖ := norm_sum_le _ _
    _ <= ∑ i in range (n - k), ‖p (i + k)‖ * ‖w‖ ^ (i + k) := by
        gcongr with i _hi; exact ((p (i + k)).le_opNorm _).trans_eq (by simp)
    _ <= ∑ i in range (n - k), ‖p (i + k)‖ * ↑r' ^ (i + k) := by
        gcongr with i _hi; simpa [← coe_nnnorm] using hw.le
    _ <= ∑' i, ‖p (i + k)‖ * ↑r' ^ (i + k) := by
        apply Summable.sum_le_tsum _ (fun i _hi => by positivity)
        apply ((_root_.summable_nat_add_iff k).2 S)
    _ <= ε / 4 := hk.le
  calc
  ‖p.partialSum n z - p.partialSum n y‖
  _ = ‖∑ i in range n, p i (fun _ => z) - ∑ i in range n, p i (fun _ => y)‖ := rfl
  _ = ‖(∑ i in range k, p i (fun _ => z) + ∑ i in Ico k n, p i (fun _ => z))
        - (∑ i in range k, p i (fun _ => y) + ∑ i in Ico k n, p i (fun _ => y))‖ := by
    simp [sum_range_add_sum_Ico _ hkn]
  _ = ‖(p.partialSum k z - p.partialSum k y) + (∑ i in Ico k n, p i (fun _ => z))
        + (- ∑ i in Ico k n, p i (fun _ => y))‖ := by
    congr 1
    simp only [FormalMultilinearSeries.partialSum]
    abel
  _ <= ‖p.partialSum k z - p.partialSum k y‖ + ‖∑ i in Ico k n, p i (fun _ => z)‖
      + ‖- ∑ i in Ico k n, p i (fun _ => y)‖ := norm_add₃_le
  _ <= ε / 4 + ε / 4 + ε / 4 := by
    gcongr
    · exact I _ h'z
    · simp only [norm_neg]; exact I _ yr'
  _ < ε := by linarith

/--
theorem `HasFPowerSeriesOnBall.tendsto_partialSum_prod` / 定理 `HasFPowerSeriesOnBall.tendsto_partialSum_prod`

English:
theorem HasFPowerSeriesOnBall.tendsto_partialSum_prod
  statement: {y : E}
  proof: (hf.hasFPowerSeriesWithinOnBall (s := univ)).tendsto_partialSum_prod hy (by simp)

中文:
定理 HasFPowerSeriesOnBall.tendsto_partialSum_prod
  结论: {y : E}
  证明: (hf.hasFPowerSeriesWithinOnBall (s := univ)).tendsto_partialSum_prod hy (by simp)

Depends on / 依赖: hasFPowerSeriesWithinOnBall, hf.hasFPowerSeriesWithinOnBall, tendsto_partialSum_prod
-/
theorem HasFPowerSeriesOnBall.tendsto_partialSum_prod {y : E}
    (hf : HasFPowerSeriesOnBall f p x r) (hy : y in Metric.eball (0 : E) r) :
    Tendsto (fun (z : Nat × E) => p.partialSum z.1 z.2) (atTop ×ˢ 𝓝 y) (𝓝 (f (x + y))) :=
  (hf.hasFPowerSeriesWithinOnBall (s := univ)).tendsto_partialSum_prod hy (by simp)

/--
theorem `HasFPowerSeriesWithinOnBall.uniform_geometric_approx'` / 定理 `HasFPowerSeriesWithinOnBall.uniform_geometric_approx'`

English:
theorem HasFPowerSeriesWithinOnBall.uniform_geometric_approx'
  statement: {r' : Real>=0}
  proof: by
  obtain ⟨a, ha, C, hC, hp⟩ : exists a in Ioo (0 : Real) 1, exists C > 0, forall n, ‖p n‖ * (r' : Real) ^ n <= C * a ^ n :=
    p.norm_mul_pow_le_mul_pow_of_lt_radius (h.trans_le hf.r_le)
  refine ⟨a, ha, C / (1 - a), div_pos hC (sub_pos.2 ha.2), fun y hy n ys => ?_⟩
  have yr' : ‖y‖ < r' := by
 

中文:
定理 HasFPowerSeriesWithinOnBall.uniform_geometric_approx'
  结论: {r' : 实数>=0}
  证明: by
  obtain ⟨a, ha, C, hC, hp⟩ : exists a in Ioo (0 : Real) 1, exists C > 0, forall n, ‖p n‖ * (r' : Real) ^ n <= C * a ^ n :=
    p.norm_mul_pow_le_mul_pow_of_lt_radius (h.trans_le hf.r_le)
  refine ⟨a, ha, C / (1 - a), div_pos hC (sub_pos.2 ha.2), fun y hy n ys => ?_⟩
  have yr' : ‖y‖ < r' := by
 

Depends on / 依赖: Metric, Metric.eball, ball_zero_eq, div_pos, h.trans_le, hf.r_le, lt_trans, mem_eball_zero_iff, norm_mul_pow_le_mul_pow_of_lt_radius, norm_nonneg, p.norm_mul_pow_le_mul_pow_of_lt_radius, r_le, sub_pos, trans_le, trans_lt
-/
theorem HasFPowerSeriesWithinOnBall.uniform_geometric_approx' {r' : Real>=0}
    (hf : HasFPowerSeriesWithinOnBall f p s x r) (h : (r' : Real>=0∞) < r) :
    exists a in Ioo (0 : Real) 1, exists C > 0, forall y in Metric.ball (0 : E) r', forall n, x + y in insert x s ->
      ‖f (x + y) - p.partialSum n y‖ <= C * (a * (‖y‖ / r')) ^ n := by
  obtain ⟨a, ha, C, hC, hp⟩ : exists a in Ioo (0 : Real) 1, exists C > 0, forall n, ‖p n‖ * (r' : Real) ^ n <= C * a ^ n :=
    p.norm_mul_pow_le_mul_pow_of_lt_radius (h.trans_le hf.r_le)
  refine ⟨a, ha, C / (1 - a), div_pos hC (sub_pos.2 ha.2), fun y hy n ys => ?_⟩
  have yr' : ‖y‖ < r' := by
    rw [ball_zero_eq] at hy
    exact hy
  have hr'0 : 0 < (r' : Real) := (norm_nonneg _).trans_lt yr'
  have : y in Metric.eball (0 : E) r := by
    refine mem_eball_zero_iff.2 (lt_trans ?_ h)
    simpa [enorm] using! yr'
  rw [norm_sub_rev]; rw [← mul_div_right_comm]
  have ya : a * (‖y‖ / ↑r') <= a :=
    mul_le_of_le_one_right ha.1.le (div_le_one_of_le₀ yr'.le r'.coe_nonneg)
  suffices ‖p.partialSum n y - f (x + y)‖ <= C * (a * (‖y‖ / r')) ^ n / (1 - a * (‖y‖ / r')) by
    refine this.trans ?_
    have : 0 < a := ha.1
    gcongr
    apply_rules [sub_pos.2, ha.2]
  apply norm_sub_le_of_geometric_bound_of_hasSum (ya.trans_lt ha.2) _ (hf.hasSum ys this)
  intro n
  calc
    ‖(p n) fun _ : Fin n => y‖
    _ <= ‖p n‖ * ∏ _i : Fin n, ‖y‖ := ContinuousMultilinearMap.le_opNorm _ _
    _ = ‖p n‖ * (r' : Real) ^ n * (‖y‖ / r') ^ n := by simp [field, div_pow]
    _ <= C * a ^ n * (‖y‖ / r') ^ n := by gcongr ?_ * _; apply hp
    _ <= C * (a * (‖y‖ / r')) ^ n := by rw [mul_pow, mul_assoc]

/--
theorem `HasFPowerSeriesOnBall.uniform_geometric_approx'` / 定理 `HasFPowerSeriesOnBall.uniform_geometric_approx'`

English:
theorem HasFPowerSeriesOnBall.uniform_geometric_approx'
  statement: {r' : Real>=0}
  proof: by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  simpa using hf.uniform_geometric_approx' h

中文:
定理 HasFPowerSeriesOnBall.uniform_geometric_approx'
  结论: {r' : 实数>=0}
  证明: by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  simpa using hf.uniform_geometric_approx' h

Depends on / 依赖: hasFPowerSeriesWithinOnBall_univ, hf.uniform_geometric_approx, uniform_geometric_approx
-/
theorem HasFPowerSeriesOnBall.uniform_geometric_approx' {r' : Real>=0}
    (hf : HasFPowerSeriesOnBall f p x r) (h : (r' : Real>=0∞) < r) :
    exists a in Ioo (0 : Real) 1, exists C > 0, forall y in Metric.ball (0 : E) r', forall n,
      ‖f (x + y) - p.partialSum n y‖ <= C * (a * (‖y‖ / r')) ^ n := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  simpa using hf.uniform_geometric_approx' h

/--
theorem `HasFPowerSeriesWithinOnBall.uniform_geometric_approx` / 定理 `HasFPowerSeriesWithinOnBall.uniform_geometric_approx`

English:
theorem HasFPowerSeriesWithinOnBall.uniform_geometric_approx
  statement: {r' : Real>=0}
  proof: by
  obtain ⟨a, ha, C, hC, hp⟩ : exists a in Ioo (0 : Real) 1, exists C > 0, forall y in Metric.ball (0 : E) r', forall n,
      x + y in insert x s -> ‖f (x + y) - p.partialSum n y‖ <= C * (a * (‖y‖ / r')) ^ n :=
    hf.uniform_geometric_approx' h
  refine ⟨a, ha, C, hC, fun y hy n ys => (hp y hy n

中文:
定理 HasFPowerSeriesWithinOnBall.uniform_geometric_approx
  结论: {r' : 实数>=0}
  证明: by
  obtain ⟨a, ha, C, hC, hp⟩ : exists a in Ioo (0 : Real) 1, exists C > 0, forall y in Metric.ball (0 : E) r', forall n,
      x + y in insert x s -> ‖f (x + y) - p.partialSum n y‖ <= C * (a * (‖y‖ / r')) ^ n :=
    hf.uniform_geometric_approx' h
  refine ⟨a, ha, C, hC, fun y hy n ys => (hp y hy n

Depends on / 依赖: Metric, Metric.ball, ball_zero_eq, coe_non, discharge, hf.uniform_geometric_approx, insert, mul_le_of_le_one_right, needed, p.partialSum, partialSum, uniform_geometric_approx
-/
theorem HasFPowerSeriesWithinOnBall.uniform_geometric_approx {r' : Real>=0}
    (hf : HasFPowerSeriesWithinOnBall f p s x r) (h : (r' : Real>=0∞) < r) :
    exists a in Ioo (0 : Real) 1,
      exists C > 0, forall y in Metric.ball (0 : E) r', forall n, x + y in insert x s ->
      ‖f (x + y) - p.partialSum n y‖ <= C * a ^ n := by
  obtain ⟨a, ha, C, hC, hp⟩ : exists a in Ioo (0 : Real) 1, exists C > 0, forall y in Metric.ball (0 : E) r', forall n,
      x + y in insert x s -> ‖f (x + y) - p.partialSum n y‖ <= C * (a * (‖y‖ / r')) ^ n :=
    hf.uniform_geometric_approx' h
  refine ⟨a, ha, C, hC, fun y hy n ys => (hp y hy n ys).trans ?_⟩
  have yr' : ‖y‖ < r' := by rwa [ball_zero_eq] at hy
  have := ha.1.le -- needed to discharge a side goal on the next line
  gcongr
  exact mul_le_of_le_one_right ha.1.le (div_le_one_of_le₀ yr'.le r'.coe_nonneg)

/--
theorem `HasFPowerSeriesOnBall.uniform_geometric_approx` / 定理 `HasFPowerSeriesOnBall.uniform_geometric_approx`

English:
theorem HasFPowerSeriesOnBall.uniform_geometric_approx
  statement: {r' : Real>=0}
  proof: by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  simpa using hf.uniform_geometric_approx h

中文:
定理 HasFPowerSeriesOnBall.uniform_geometric_approx
  结论: {r' : 实数>=0}
  证明: by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  simpa using hf.uniform_geometric_approx h

Depends on / 依赖: hasFPowerSeriesWithinOnBall_univ, hf.uniform_geometric_approx, uniform_geometric_approx
-/
theorem HasFPowerSeriesOnBall.uniform_geometric_approx {r' : Real>=0}
    (hf : HasFPowerSeriesOnBall f p x r) (h : (r' : Real>=0∞) < r) :
    exists a in Ioo (0 : Real) 1,
      exists C > 0, forall y in Metric.ball (0 : E) r', forall n,
      ‖f (x + y) - p.partialSum n y‖ <= C * a ^ n := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  simpa using hf.uniform_geometric_approx h

/--
theorem `HasFPowerSeriesWithinAt.isBigO_sub_partialSum_pow` / 定理 `HasFPowerSeriesWithinAt.isBigO_sub_partialSum_pow`

English:
theorem HasFPowerSeriesWithinAt.isBigO_sub_partialSum_pow
  proof: by
  rcases hf with ⟨r, hf⟩
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 hf.r_pos with ⟨r', r'0, h⟩
  obtain ⟨a, -, C, -, hp⟩ : exists a in Ioo (0 : Real) 1, exists C > 0, forall y in Metric.ball (0 : E) r', forall n,
      x + y in insert x s -> ‖f (x + y) - p.partialSum n y‖ <= C * (a * (‖y‖ / r')

中文:
定理 HasFPowerSeriesWithinAt.isBigO_sub_partialSum_pow
  证明: by
  rcases hf with ⟨r, hf⟩
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 hf.r_pos with ⟨r', r'0, h⟩
  obtain ⟨a, -, C, -, hp⟩ : exists a in Ioo (0 : Real) 1, exists C > 0, forall y in Metric.ball (0 : E) r', forall n,
      x + y in insert x s -> ‖f (x + y) - p.partialSum n y‖ <= C * (a * (‖y‖ / r')

Depends on / 依赖: ENNReal, ENNReal.lt_iff_exists_nnreal_btwn, Metric, Metric.ball, Metric.ball_mem_nhds, ball_mem_nhds, filter_upwards, hf.r_pos, hf.uniform_geometric_approx, insert, inter_mem_nhdsWithin, isBigO_iff, lt_iff_exists_nnreal_btwn, mod_cast, p.partialSum, partialSum, r_pos, replace, uniform_geometric_approx
-/
theorem HasFPowerSeriesWithinAt.isBigO_sub_partialSum_pow
    (hf : HasFPowerSeriesWithinAt f p s x) (n : Nat) :
    (fun y : E => f (x + y) - p.partialSum n y)
      =O[𝓝[(x + ·) ⁻¹' insert x s] 0] fun y => ‖y‖ ^ n := by
  rcases hf with ⟨r, hf⟩
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 hf.r_pos with ⟨r', r'0, h⟩
  obtain ⟨a, -, C, -, hp⟩ : exists a in Ioo (0 : Real) 1, exists C > 0, forall y in Metric.ball (0 : E) r', forall n,
      x + y in insert x s -> ‖f (x + y) - p.partialSum n y‖ <= C * (a * (‖y‖ / r')) ^ n :=
    hf.uniform_geometric_approx' h
  refine isBigO_iff.2 ⟨C * (a / r') ^ n, ?_⟩
  replace r'0 : 0 < (r' : Real) := mod_cast r'0
  filter_upwards [inter_mem_nhdsWithin _ (Metric.ball_mem_nhds (0 : E) r'0)] with y hy
  simpa [mul_pow, mul_div_assoc, mul_assoc, div_mul_eq_mul_div, div_pow]
    using hp y hy.2 n (by simpa using hy.1)

/--
theorem `HasFPowerSeriesAt.isBigO_sub_partialSum_pow` / 定理 `HasFPowerSeriesAt.isBigO_sub_partialSum_pow`

English:
theorem HasFPowerSeriesAt.isBigO_sub_partialSum_pow
  proof: by
  rw [← hasFPowerSeriesWithinAt_univ] at hf
  simpa using hf.isBigO_sub_partialSum_pow n

中文:
定理 HasFPowerSeriesAt.isBigO_sub_partialSum_pow
  证明: by
  rw [← hasFPowerSeriesWithinAt_univ] at hf
  simpa using hf.isBigO_sub_partialSum_pow n

Depends on / 依赖: hasFPowerSeriesWithinAt_univ, hf.isBigO_sub_partialSum_pow, isBigO_sub_partialSum_pow
-/
theorem HasFPowerSeriesAt.isBigO_sub_partialSum_pow
    (hf : HasFPowerSeriesAt f p x) (n : Nat) :
    (fun y : E => f (x + y) - p.partialSum n y) =O[𝓝 0] fun y => ‖y‖ ^ n := by
  rw [← hasFPowerSeriesWithinAt_univ] at hf
  simpa using hf.isBigO_sub_partialSum_pow n

/--
theorem `HasFPowerSeriesWithinOnBall.isBigO_image_sub_image_sub_deriv_principal` / 定理 `HasFPowerSeriesWithinOnBall.isBigO_image_sub_image_sub_deriv_principal`

English:
theorem HasFPowerSeriesWithinOnBall.isBigO_image_sub_image_sub_deriv_principal
  proof: by
  lift r' to Real>=0 using ne_top_of_lt hr
  rcases eq_zero_or_pos r' with (rfl | hr'0)
  · simp only [ENNReal.coe_zero, Metric.eball_zero, empty_inter, principal_empty, isBigO_bot]
  obtain ⟨a, ha, C, hC : 0 < C, hp⟩ :
      exists a in Ioo (0 : Real) 1, exists C > 0, forall n : Nat, ‖p n‖ * (r'

中文:
定理 HasFPowerSeriesWithinOnBall.isBigO_image_sub_image_sub_deriv_principal
  证明: by
  lift r' to Real>=0 using ne_top_of_lt hr
  rcases eq_zero_or_pos r' with (rfl | hr'0)
  · simp only [ENNReal.coe_zero, Metric.eball_zero, empty_inter, principal_empty, isBigO_bot]
  obtain ⟨a, ha, C, hC : 0 < C, hp⟩ :
      exists a in Ioo (0 : Real) 1, exists C > 0, forall n : Nat, ‖p n‖ * (r'

Depends on / 依赖: ENNReal, ENNReal.coe_zero, Metric, Metric.eball_zero, NNReal, NNReal.coe_pos, coe_pos, coe_zero, eball_zero, empty_inter, eq_zero_or_pos, hf.r_le, hr.trans_le, isBigO_bot, ne_top_of_lt, norm_mul_pow_le_mul_pow_of_lt_radius, p.norm_mul_pow_le_mul_pow_of_lt_radius, pow_pos, principal_empty, r_le
-/
theorem HasFPowerSeriesWithinOnBall.isBigO_image_sub_image_sub_deriv_principal
    (hf : HasFPowerSeriesWithinOnBall f p s x r) (hr : r' < r) :
    (fun y : E × E => f y.1 - f y.2 - p 1 fun _ => y.1 - y.2)
      =O[𝓟 (Metric.eball (x, x) r' inter ((insert x s) ×ˢ (insert x s)))]
      fun y => ‖y - (x, x)‖ * ‖y.1 - y.2‖ := by
  lift r' to Real>=0 using ne_top_of_lt hr
  rcases eq_zero_or_pos r' with (rfl | hr'0)
  · simp only [ENNReal.coe_zero, Metric.eball_zero, empty_inter, principal_empty, isBigO_bot]
  obtain ⟨a, ha, C, hC : 0 < C, hp⟩ :
      exists a in Ioo (0 : Real) 1, exists C > 0, forall n : Nat, ‖p n‖ * (r' : Real) ^ n <= C * a ^ n :=
    p.norm_mul_pow_le_mul_pow_of_lt_radius (hr.trans_le hf.r_le)
  simp only [← le_div_iff₀ (pow_pos (NNReal.coe_pos.2 hr'0) _)] at hp
  set L : E × E -> Real := fun y =>
    C * (a / r') ^ 2 * (‖y - (x, x)‖ * ‖y.1 - y.2‖) * (a / (1 - a) ^ 2 + 2 / (1 - a))
  have hL : forall y in Metric.eball (x, x) r' inter ((insert x s) ×ˢ (insert x s)),
      ‖f y.1 - f y.2 - p 1 fun _ => y.1 - y.2‖ <= L y := by
    intro y ⟨hy', ys⟩
    have hy : y in Metric.eball x r ×ˢ Metric.eball x r := by
      rw [Metric.eball_prod_same]
      exact Metric.eball_subset_eball hr.le hy'
    set A : Nat -> F := fun n => (p n fun _ => y.1 - x) - p n fun _ => y.2 - x
    have hA : HasSum (fun n => A (n + 2)) (f y.1 - f y.2 - p 1 fun _ => y.1 - y.2) := by
      convert
        (hasSum_nat_add_iff' 2).2
          ((hf.hasSum_sub ⟨ys.1, hy.1⟩).sub (hf.hasSum_sub ⟨ys.2, hy.2⟩))
      rw [Finset.sum_range_succ]; rw [Finset.sum_range_one]; rw [hf.coeff_zero]; rw [hf.coeff_zero]; rw [sub_self]; rw [zero_add]; rw [← Subsingleton.pi_single_eq (0 : Fin 1) (y.1 - x)]; rw [Pi.single]; rw [← Subsingleton.pi_single_eq (0 : Fin 1) (y.2 - x)]; rw [Pi.single]; rw [← (p 1).map_update_sub]; rw [← Pi.single]; rw [Subsingleton.pi_single_eq]; rw [sub_sub_sub_cancel_right]
    rw [Metric.mem_eball]; rw [edist_eq_enorm_sub]; rw [enorm_lt_coe] at hy'
    set B : Nat -> Real := fun n => C * (a / r') ^ 2 * (‖y - (x, x)‖ * ‖y.1 - y.2‖) * ((n + 2) * a ^ n)
    have hAB : forall n, ‖A (n + 2)‖ <= B n := fun n =>
      calc
        ‖A (n + 2)‖ <= ‖p (n + 2)‖ * ↑(n + 2) * ‖y - (x, x)‖ ^ (n + 1) * ‖y.1 - y.2‖ := by
          simpa only [Fintype.card_fin, pi_norm_const, Prod.norm_def, Pi.sub_def,
            Prod.fst_sub, Prod.snd_sub, sub_sub_sub_cancel_right] using!
            (p <| n + 2).norm_image_sub_le (fun _ => y.1 - x) fun _ => y.2 - x
        _ = ‖p (n + 2)‖ * ‖y - (x, x)‖ ^ n * (↑(n + 2) * ‖y - (x, x)‖ * ‖y.1 - y.2‖) := by
          rw [pow_succ ‖y - (x]; rw [x)‖]
          ring
        _ <= C * a ^ (n + 2) / r' ^ (n + 2)
            * r' ^ n * (↑(n + 2) * ‖y - (x, x)‖ * ‖y.1 - y.2‖) := by
          have : 0 < a := ha.1
          gcongr
          · apply hp
          · apply hy'.le
        _ = B n := by
          simp [field, B, pow_succ]
    have hBL : HasSum B (L y) := by
      apply HasSum.mul_left
      simp only [add_mul]
      have : ‖a‖ < 1 := by simp only [Real.norm_eq_abs, abs_of_pos ha.1, ha.2]
      rw [div_eq_mul_inv]; rw [div_eq_mul_inv]
      exact (hasSum_coe_mul_geometric_of_norm_lt_one this).add
          ((hasSum_geometric_of_norm_lt_one this).mul_left 2)
    exact hA.norm_le_of_bounded hBL hAB
  suffices L =O[𝓟 (Metric.eball (x, x) r' inter ((insert x s) ×ˢ (insert x s)))]
      fun y => ‖y - (x, x)‖ * ‖y.1 - y.2‖ from
    .trans (.of_norm_eventuallyLE (eventually_principal.2 hL)) this
  simp_rw [L, mul_right_comm _ (_ * _)]
  exact (isBigO_refl _ _).const_mul_left _

/--
theorem `HasFPowerSeriesOnBall.isBigO_image_sub_image_sub_deriv_principal` / 定理 `HasFPowerSeriesOnBall.isBigO_image_sub_image_sub_deriv_principal`

English:
theorem HasFPowerSeriesOnBall.isBigO_image_sub_image_sub_deriv_principal
  proof: by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  simpa using hf.isBigO_image_sub_image_sub_deriv_principal hr

中文:
定理 HasFPowerSeriesOnBall.isBigO_image_sub_image_sub_deriv_principal
  证明: by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  simpa using hf.isBigO_image_sub_image_sub_deriv_principal hr

Depends on / 依赖: hasFPowerSeriesWithinOnBall_univ, hf.isBigO_image_sub_image_sub_deriv_principal, isBigO_image_sub_image_sub_deriv_principal
-/
theorem HasFPowerSeriesOnBall.isBigO_image_sub_image_sub_deriv_principal
    (hf : HasFPowerSeriesOnBall f p x r) (hr : r' < r) :
    (fun y : E × E => f y.1 - f y.2 - p 1 fun _ => y.1 - y.2)
      =O[𝓟 (Metric.eball (x, x) r')] fun y => ‖y - (x, x)‖ * ‖y.1 - y.2‖ := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  simpa using hf.isBigO_image_sub_image_sub_deriv_principal hr

/--
theorem `HasFPowerSeriesWithinOnBall.image_sub_sub_deriv_le` / 定理 `HasFPowerSeriesWithinOnBall.image_sub_sub_deriv_le`

English:
theorem HasFPowerSeriesWithinOnBall.image_sub_sub_deriv_le
  proof: by
  have := hf.isBigO_image_sub_image_sub_deriv_principal hr
  simp only [isBigO_principal, mem_inter_iff, Metric.mem_eball, Prod.edist_eq, max_lt_iff, mem_prod,
    norm_mul, Real.norm_eq_abs, abs_norm, and_imp, Prod.forall, mul_assoc] at this ⊢
  rcases this with ⟨C, hC⟩
  exact ⟨C, fun y ys hy z

中文:
定理 HasFPowerSeriesWithinOnBall.image_sub_sub_deriv_le
  证明: by
  have := hf.isBigO_image_sub_image_sub_deriv_principal hr
  simp only [isBigO_principal, mem_inter_iff, Metric.mem_eball, Prod.edist_eq, max_lt_iff, mem_prod,
    norm_mul, Real.norm_eq_abs, abs_norm, and_imp, Prod.forall, mul_assoc] at this ⊢
  rcases this with ⟨C, hC⟩
  exact ⟨C, fun y ys hy z

Depends on / 依赖: Metric, Metric.mem_eball, Prod.edist_eq, Prod.forall, Real.norm_eq_abs, abs_norm, and_imp, edist_eq, hf.isBigO_image_sub_image_sub_deriv_principal, isBigO_image_sub_image_sub_deriv_principal, isBigO_principal, max_lt_iff, mem_eball, mem_inter_iff, mem_prod, mul_assoc, norm_eq_abs, norm_mul
-/
theorem HasFPowerSeriesWithinOnBall.image_sub_sub_deriv_le
    (hf : HasFPowerSeriesWithinOnBall f p s x r) (hr : r' < r) :
    exists C, forallᵉ (y in insert x s inter Metric.eball x r') (z in insert x s inter Metric.eball x r'),
      ‖f y - f z - p 1 fun _ => y - z‖ <= C * max ‖y - x‖ ‖z - x‖ * ‖y - z‖ := by
  have := hf.isBigO_image_sub_image_sub_deriv_principal hr
  simp only [isBigO_principal, mem_inter_iff, Metric.mem_eball, Prod.edist_eq, max_lt_iff, mem_prod,
    norm_mul, Real.norm_eq_abs, abs_norm, and_imp, Prod.forall, mul_assoc] at this ⊢
  rcases this with ⟨C, hC⟩
  exact ⟨C, fun y ys hy z zs hz => hC y z hy hz ys zs⟩

/--
theorem `HasFPowerSeriesOnBall.image_sub_sub_deriv_le` / 定理 `HasFPowerSeriesOnBall.image_sub_sub_deriv_le`

English:
theorem HasFPowerSeriesOnBall.image_sub_sub_deriv_le
  proof: by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  simpa only [mem_univ, insert_eq_of_mem, univ_inter] using hf.image_sub_sub_deriv_le hr

中文:
定理 HasFPowerSeriesOnBall.image_sub_sub_deriv_le
  证明: by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  simpa only [mem_univ, insert_eq_of_mem, univ_inter] using hf.image_sub_sub_deriv_le hr

Depends on / 依赖: hasFPowerSeriesWithinOnBall_univ, hf.image_sub_sub_deriv_le, image_sub_sub_deriv_le, insert_eq_of_mem, mem_univ, univ_inter
-/
theorem HasFPowerSeriesOnBall.image_sub_sub_deriv_le
    (hf : HasFPowerSeriesOnBall f p x r) (hr : r' < r) :
    exists C, forallᵉ (y in Metric.eball x r') (z in Metric.eball x r'),
      ‖f y - f z - p 1 fun _ => y - z‖ <= C * max ‖y - x‖ ‖z - x‖ * ‖y - z‖ := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  simpa only [mem_univ, insert_eq_of_mem, univ_inter] using hf.image_sub_sub_deriv_le hr

/--
theorem `HasFPowerSeriesWithinAt.isBigO_image_sub_norm_mul_norm_sub` / 定理 `HasFPowerSeriesWithinAt.isBigO_image_sub_norm_mul_norm_sub`

English:
theorem HasFPowerSeriesWithinAt.isBigO_image_sub_norm_mul_norm_sub
  proof: by
  rcases hf with ⟨r, hf⟩
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 hf.r_pos with ⟨r', r'0, h⟩
  refine (hf.isBigO_image_sub_image_sub_deriv_principal h).mono ?_
  rw [inter_comm]
  exact le_principal_iff.2 (inter_mem_nhdsWithin _ (Metric.eball_mem_nhds _ r'0))

中文:
定理 HasFPowerSeriesWithinAt.isBigO_image_sub_norm_mul_norm_sub
  证明: by
  rcases hf with ⟨r, hf⟩
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 hf.r_pos with ⟨r', r'0, h⟩
  refine (hf.isBigO_image_sub_image_sub_deriv_principal h).mono ?_
  rw [inter_comm]
  exact le_principal_iff.2 (inter_mem_nhdsWithin _ (Metric.eball_mem_nhds _ r'0))

Depends on / 依赖: ENNReal, ENNReal.lt_iff_exists_nnreal_btwn, Metric, Metric.eball_mem_nhds, eball_mem_nhds, hf.isBigO_image_sub_image_sub_deriv_principal, hf.r_pos, inter_comm, inter_mem_nhdsWithin, isBigO_image_sub_image_sub_deriv_principal, le_principal_iff, lt_iff_exists_nnreal_btwn, r_pos
-/
theorem HasFPowerSeriesWithinAt.isBigO_image_sub_norm_mul_norm_sub
    (hf : HasFPowerSeriesWithinAt f p s x) :
    (fun y : E × E => f y.1 - f y.2 - p 1 fun _ => y.1 - y.2)
      =O[𝓝[(insert x s) ×ˢ (insert x s)] (x, x)] fun y => ‖y - (x, x)‖ * ‖y.1 - y.2‖ := by
  rcases hf with ⟨r, hf⟩
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 hf.r_pos with ⟨r', r'0, h⟩
  refine (hf.isBigO_image_sub_image_sub_deriv_principal h).mono ?_
  rw [inter_comm]
  exact le_principal_iff.2 (inter_mem_nhdsWithin _ (Metric.eball_mem_nhds _ r'0))

/--
theorem `HasFPowerSeriesAt.isBigO_image_sub_norm_mul_norm_sub` / 定理 `HasFPowerSeriesAt.isBigO_image_sub_norm_mul_norm_sub`

English:
theorem HasFPowerSeriesAt.isBigO_image_sub_norm_mul_norm_sub
  given: (hf : HasFPowerSeriesAt f p x)
  proof: by
  rw [← hasFPowerSeriesWithinAt_univ] at hf
  simpa using hf.isBigO_image_sub_norm_mul_norm_sub

中文:
定理 HasFPowerSeriesAt.isBigO_image_sub_norm_mul_norm_sub
  条件: (hf : HasFPowerSeriesAt f p x)
  证明: by
  rw [← hasFPowerSeriesWithinAt_univ] at hf
  simpa using hf.isBigO_image_sub_norm_mul_norm_sub

Depends on / 依赖: hasFPowerSeriesWithinAt_univ, hf.isBigO_image_sub_norm_mul_norm_sub, isBigO_image_sub_norm_mul_norm_sub
-/
theorem HasFPowerSeriesAt.isBigO_image_sub_norm_mul_norm_sub (hf : HasFPowerSeriesAt f p x) :
    (fun y : E × E => f y.1 - f y.2 - p 1 fun _ => y.1 - y.2) =O[𝓝 (x, x)] fun y =>
      ‖y - (x, x)‖ * ‖y.1 - y.2‖ := by
  rw [← hasFPowerSeriesWithinAt_univ] at hf
  simpa using hf.isBigO_image_sub_norm_mul_norm_sub

/--
theorem `HasFPowerSeriesWithinOnBall.tendstoUniformlyOn` / 定理 `HasFPowerSeriesWithinOnBall.tendstoUniformlyOn`

English:
theorem HasFPowerSeriesWithinOnBall.tendstoUniformlyOn
  statement: {r' : Real>=0}
  proof: by
  obtain ⟨a, ha, C, -, hp⟩ : exists a in Ioo (0 : Real) 1, exists C > 0, forall y in Metric.ball (0 : E) r', forall n,
    x + y in insert x s -> ‖f (x + y) - p.partialSum n y‖ <= C * a ^ n := hf.uniform_geometric_approx h
  refine Metric.tendstoUniformlyOn_iff.2 fun ε εpos => ?_
  have L : Tends

中文:
定理 HasFPowerSeriesWithinOnBall.tendstoUniformlyOn
  结论: {r' : 实数>=0}
  证明: by
  obtain ⟨a, ha, C, -, hp⟩ : exists a in Ioo (0 : Real) 1, exists C > 0, forall y in Metric.ball (0 : E) r', forall n,
    x + y in insert x s -> ‖f (x + y) - p.partialSum n y‖ <= C * a ^ n := hf.uniform_geometric_approx h
  refine Metric.tendstoUniformlyOn_iff.2 fun ε εpos => ?_
  have L : Tends

Depends on / 依赖: L.eventually, Metric, Metric.ball, Metric.tendstoUniformlyOn_iff, Tendsto, eventually, gt_mem_nhds, hf.uniform_geometric_approx, insert, mul_zero, p.partialSum, partialSum, tendstoUniformlyOn_iff, tendsto_const_nhds, tendsto_const_nhds.mul, tendsto_pow_atTop_nhds_zero_of_lt_one, uniform_geometric_approx
-/
theorem HasFPowerSeriesWithinOnBall.tendstoUniformlyOn {r' : Real>=0}
    (hf : HasFPowerSeriesWithinOnBall f p s x r) (h : (r' : Real>=0∞) < r) :
    TendstoUniformlyOn (fun n y => p.partialSum n y) (fun y => f (x + y)) atTop
      ((x + ·) ⁻¹' (insert x s) inter Metric.ball (0 : E) r') := by
  obtain ⟨a, ha, C, -, hp⟩ : exists a in Ioo (0 : Real) 1, exists C > 0, forall y in Metric.ball (0 : E) r', forall n,
    x + y in insert x s -> ‖f (x + y) - p.partialSum n y‖ <= C * a ^ n := hf.uniform_geometric_approx h
  refine Metric.tendstoUniformlyOn_iff.2 fun ε εpos => ?_
  have L : Tendsto (fun n => (C : Real) * a ^ n) atTop (𝓝 ((C : Real) * 0)) :=
    tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one ha.1.le ha.2)
  rw [mul_zero] at L
  refine (L.eventually (gt_mem_nhds εpos)).mono fun n hn y hy => ?_
  rw [dist_eq_norm]
  exact (hp y hy.2 n hy.1).trans_lt hn

/--
theorem `HasFPowerSeriesOnBall.tendstoUniformlyOn` / 定理 `HasFPowerSeriesOnBall.tendstoUniformlyOn`

English:
theorem HasFPowerSeriesOnBall.tendstoUniformlyOn
  statement: {r' : Real>=0} (hf : HasFPowerSeriesOnBall f p x r)
  proof: by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  simpa using hf.tendstoUniformlyOn h

中文:
定理 HasFPowerSeriesOnBall.tendstoUniformlyOn
  结论: {r' : 实数>=0} (hf : HasFPowerSeriesOnBall f p x r)
  证明: by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  simpa using hf.tendstoUniformlyOn h

Depends on / 依赖: hasFPowerSeriesWithinOnBall_univ, hf.tendstoUniformlyOn, tendstoUniformlyOn
-/
theorem HasFPowerSeriesOnBall.tendstoUniformlyOn {r' : Real>=0} (hf : HasFPowerSeriesOnBall f p x r)
    (h : (r' : Real>=0∞) < r) :
    TendstoUniformlyOn (fun n y => p.partialSum n y) (fun y => f (x + y)) atTop
      (Metric.ball (0 : E) r') := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  simpa using hf.tendstoUniformlyOn h

/--
theorem `HasFPowerSeriesWithinOnBall.tendstoLocallyUniformlyOn` / 定理 `HasFPowerSeriesWithinOnBall.tendstoLocallyUniformlyOn`

English:
theorem HasFPowerSeriesWithinOnBall.tendstoLocallyUniformlyOn
  proof: by
  intro u hu y hy
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 hy.2 with ⟨r', yr', hr'⟩
  have : Metric.eball (0 : E) r' in 𝓝 y := IsOpen.mem_nhds Metric.isOpen_eball yr'
  refine ⟨(x + ·)⁻¹' (insert x s) inter Metric.eball (0 : E) r', ?_, ?_⟩
  · rw [nhdsWithin_inter_of_mem']
    · exact inter_m

中文:
定理 HasFPowerSeriesWithinOnBall.tendstoLocallyUniformlyOn
  证明: by
  intro u hu y hy
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 hy.2 with ⟨r', yr', hr'⟩
  have : Metric.eball (0 : E) r' in 𝓝 y := IsOpen.mem_nhds Metric.isOpen_eball yr'
  refine ⟨(x + ·)⁻¹' (insert x s) inter Metric.eball (0 : E) r', ?_, ?_⟩
  · rw [nhdsWithin_inter_of_mem']
    · exact inter_m

Depends on / 依赖: ENNReal, ENNReal.lt_iff_exists_nnreal_btwn, Filter, Filter.mem_of_superset, IsOpen, IsOpen.mem_nhds, Metric, Metric.eball, Metric.eball_coe, Metric.eball_subset_eball, Metric.isOpen_eball, eball_coe, eball_subset_eball, hf.tendstoUniformlyOn, insert, inter_mem_nhdsWithin, isOpen_eball, lt_iff_exists_nnreal_btwn, mem_nhds, mem_nhdsWithin_of_mem_nhds
-/
theorem HasFPowerSeriesWithinOnBall.tendstoLocallyUniformlyOn
    (hf : HasFPowerSeriesWithinOnBall f p s x r) :
    TendstoLocallyUniformlyOn (fun n y => p.partialSum n y) (fun y => f (x + y)) atTop
      ((x + ·) ⁻¹' (insert x s) inter Metric.eball (0 : E) r) := by
  intro u hu y hy
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 hy.2 with ⟨r', yr', hr'⟩
  have : Metric.eball (0 : E) r' in 𝓝 y := IsOpen.mem_nhds Metric.isOpen_eball yr'
  refine ⟨(x + ·)⁻¹' (insert x s) inter Metric.eball (0 : E) r', ?_, ?_⟩
  · rw [nhdsWithin_inter_of_mem']
    · exact inter_mem_nhdsWithin _ this
    · apply mem_nhdsWithin_of_mem_nhds
      apply Filter.mem_of_superset this (Metric.eball_subset_eball hr'.le)
  · simpa [Metric.eball_coe] using hf.tendstoUniformlyOn hr' u hu

/--
theorem `HasFPowerSeriesOnBall.tendstoLocallyUniformlyOn` / 定理 `HasFPowerSeriesOnBall.tendstoLocallyUniformlyOn`

English:
theorem HasFPowerSeriesOnBall.tendstoLocallyUniformlyOn
  given: (hf : HasFPowerSeriesOnBall f p x r)
  proof: by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  simpa using hf.tendstoLocallyUniformlyOn

中文:
定理 HasFPowerSeriesOnBall.tendstoLocallyUniformlyOn
  条件: (hf : HasFPowerSeriesOnBall f p x r)
  证明: by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  simpa using hf.tendstoLocallyUniformlyOn

Depends on / 依赖: hasFPowerSeriesWithinOnBall_univ, hf.tendstoLocallyUniformlyOn, tendstoLocallyUniformlyOn
-/
theorem HasFPowerSeriesOnBall.tendstoLocallyUniformlyOn (hf : HasFPowerSeriesOnBall f p x r) :
    TendstoLocallyUniformlyOn (fun n y => p.partialSum n y) (fun y => f (x + y)) atTop
      (Metric.eball (0 : E) r) := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  simpa using hf.tendstoLocallyUniformlyOn

/--
theorem `HasFPowerSeriesWithinOnBall.tendstoUniformlyOn'` / 定理 `HasFPowerSeriesWithinOnBall.tendstoUniformlyOn'`

English:
theorem HasFPowerSeriesWithinOnBall.tendstoUniformlyOn'
  statement: {r' : Real>=0}
  proof: by
  convert! (hf.tendstoUniformlyOn h).comp fun y => y - x using 1
  · simp [Function.comp_def]
  · ext z
    simp [dist_eq_norm]

中文:
定理 HasFPowerSeriesWithinOnBall.tendstoUniformlyOn'
  结论: {r' : 实数>=0}
  证明: by
  convert! (hf.tendstoUniformlyOn h).comp fun y => y - x using 1
  · simp [Function.comp_def]
  · ext z
    simp [dist_eq_norm]

Depends on / 依赖: Function, Function.comp_def, comp_def, convert, dist_eq_norm, hf.tendstoUniformlyOn, tendstoUniformlyOn
-/
theorem HasFPowerSeriesWithinOnBall.tendstoUniformlyOn' {r' : Real>=0}
    (hf : HasFPowerSeriesWithinOnBall f p s x r) (h : (r' : Real>=0∞) < r) :
    TendstoUniformlyOn (fun n y => p.partialSum n (y - x)) f atTop
      (insert x s inter Metric.ball (x : E) r') := by
  convert! (hf.tendstoUniformlyOn h).comp fun y => y - x using 1
  · simp [Function.comp_def]
  · ext z
    simp [dist_eq_norm]

/--
theorem `HasFPowerSeriesOnBall.tendstoUniformlyOn'` / 定理 `HasFPowerSeriesOnBall.tendstoUniformlyOn'`

English:
theorem HasFPowerSeriesOnBall.tendstoUniformlyOn'
  statement: {r' : Real>=0} (hf : HasFPowerSeriesOnBall f p x r)
  proof: by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  simpa using hf.tendstoUniformlyOn' h

中文:
定理 HasFPowerSeriesOnBall.tendstoUniformlyOn'
  结论: {r' : 实数>=0} (hf : HasFPowerSeriesOnBall f p x r)
  证明: by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  simpa using hf.tendstoUniformlyOn' h

Depends on / 依赖: hasFPowerSeriesWithinOnBall_univ, hf.tendstoUniformlyOn, tendstoUniformlyOn
-/
theorem HasFPowerSeriesOnBall.tendstoUniformlyOn' {r' : Real>=0} (hf : HasFPowerSeriesOnBall f p x r)
    (h : (r' : Real>=0∞) < r) :
    TendstoUniformlyOn (fun n y => p.partialSum n (y - x)) f atTop (Metric.ball (x : E) r') := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  simpa using hf.tendstoUniformlyOn' h

/--
theorem `HasFPowerSeriesWithinOnBall.tendstoLocallyUniformlyOn'` / 定理 `HasFPowerSeriesWithinOnBall.tendstoLocallyUniformlyOn'`

English:
theorem HasFPowerSeriesWithinOnBall.tendstoLocallyUniformlyOn'
  proof: by
  have A : ContinuousOn (fun y : E => y - x) (insert x s inter Metric.eball (x : E) r) := by fun_prop
  convert! hf.tendstoLocallyUniformlyOn.comp (fun y : E => y - x) _ A using 1
  · ext z
    simp
  · intro z
    simp [edist_eq_enorm_sub]

中文:
定理 HasFPowerSeriesWithinOnBall.tendstoLocallyUniformlyOn'
  证明: by
  have A : ContinuousOn (fun y : E => y - x) (insert x s inter Metric.eball (x : E) r) := by fun_prop
  convert! hf.tendstoLocallyUniformlyOn.comp (fun y : E => y - x) _ A using 1
  · ext z
    simp
  · intro z
    simp [edist_eq_enorm_sub]

Depends on / 依赖: ContinuousOn, Metric, Metric.eball, convert, edist_eq_enorm_sub, fun_prop, hf.tendstoLocallyUniformlyOn.comp, insert, tendstoLocallyUniformlyOn
-/
theorem HasFPowerSeriesWithinOnBall.tendstoLocallyUniformlyOn'
    (hf : HasFPowerSeriesWithinOnBall f p s x r) :
    TendstoLocallyUniformlyOn (fun n y => p.partialSum n (y - x)) f atTop
      (insert x s inter Metric.eball (x : E) r) := by
  have A : ContinuousOn (fun y : E => y - x) (insert x s inter Metric.eball (x : E) r) := by fun_prop
  convert! hf.tendstoLocallyUniformlyOn.comp (fun y : E => y - x) _ A using 1
  · ext z
    simp
  · intro z
    simp [edist_eq_enorm_sub]

/--
theorem `HasFPowerSeriesOnBall.tendstoLocallyUniformlyOn'` / 定理 `HasFPowerSeriesOnBall.tendstoLocallyUniformlyOn'`

English:
theorem HasFPowerSeriesOnBall.tendstoLocallyUniformlyOn'
  given: (hf : HasFPowerSeriesOnBall f p x r)
  proof: by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  simpa using hf.tendstoLocallyUniformlyOn'

中文:
定理 HasFPowerSeriesOnBall.tendstoLocallyUniformlyOn'
  条件: (hf : HasFPowerSeriesOnBall f p x r)
  证明: by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  simpa using hf.tendstoLocallyUniformlyOn'

Depends on / 依赖: hasFPowerSeriesWithinOnBall_univ, hf.tendstoLocallyUniformlyOn, tendstoLocallyUniformlyOn
-/
theorem HasFPowerSeriesOnBall.tendstoLocallyUniformlyOn' (hf : HasFPowerSeriesOnBall f p x r) :
    TendstoLocallyUniformlyOn (fun n y => p.partialSum n (y - x)) f atTop
      (Metric.eball (x : E) r) := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  simpa using hf.tendstoLocallyUniformlyOn'

/--
theorem `HasFPowerSeriesWithinOnBall.continuousOn` / 定理 `HasFPowerSeriesWithinOnBall.continuousOn`

English:
theorem HasFPowerSeriesWithinOnBall.continuousOn
  proof: hf.tendstoLocallyUniformlyOn'.continuousOn
    Frequently.of_forall fun n =>
      ((p.partialSum_continuous n).comp (continuous_id.sub continuous_const)).continuousOn

中文:
定理 HasFPowerSeriesWithinOnBall.continuousOn
  证明: hf.tendstoLocallyUniformlyOn'.continuousOn
    Frequently.of_forall fun n =>
      ((p.partialSum_continuous n).comp (continuous_id.sub continuous_const)).continuousOn
-/
protected theorem HasFPowerSeriesWithinOnBall.continuousOn
    (hf : HasFPowerSeriesWithinOnBall f p s x r) :
    ContinuousOn f (insert x s inter Metric.eball x r) :=
hf.tendstoLocallyUniformlyOn'.continuousOn
    Frequently.of_forall fun n =>
      ((p.partialSum_continuous n).comp (continuous_id.sub continuous_const)).continuousOn

/--
theorem `HasFPowerSeriesOnBall.continuousOn` / 定理 `HasFPowerSeriesOnBall.continuousOn`

English:
theorem HasFPowerSeriesOnBall.continuousOn
  given: (hf : HasFPowerSeriesOnBall f p x r)
  proof: by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  simpa using hf.continuousOn

中文:
定理 HasFPowerSeriesOnBall.continuousOn
  条件: (hf : HasFPowerSeriesOnBall f p x r)
  证明: by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  simpa using hf.continuousOn
-/
protected theorem HasFPowerSeriesOnBall.continuousOn (hf : HasFPowerSeriesOnBall f p x r) :
    ContinuousOn f (Metric.eball x r) := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  simpa using hf.continuousOn

/--
theorem `HasFPowerSeriesWithinOnBall.continuousWithinAt_insert` / 定理 `HasFPowerSeriesWithinOnBall.continuousWithinAt_insert`

English:
theorem HasFPowerSeriesWithinOnBall.continuousWithinAt_insert
  proof: by
  apply (hf.continuousOn.continuousWithinAt (x := x) (by simp [hf.r_pos])).mono_of_mem_nhdsWithin
  exact inter_mem_nhdsWithin _ (Metric.eball_mem_nhds x hf.r_pos)

中文:
定理 HasFPowerSeriesWithinOnBall.continuousWithinAt_insert
  证明: by
  apply (hf.continuousOn.continuousWithinAt (x := x) (by simp [hf.r_pos])).mono_of_mem_nhdsWithin
  exact inter_mem_nhdsWithin _ (Metric.eball_mem_nhds x hf.r_pos)
-/
protected theorem HasFPowerSeriesWithinOnBall.continuousWithinAt_insert
    (hf : HasFPowerSeriesWithinOnBall f p s x r) :
    ContinuousWithinAt f (insert x s) x := by
  apply (hf.continuousOn.continuousWithinAt (x := x) (by simp [hf.r_pos])).mono_of_mem_nhdsWithin
  exact inter_mem_nhdsWithin _ (Metric.eball_mem_nhds x hf.r_pos)

/--
theorem `HasFPowerSeriesWithinOnBall.continuousWithinAt` / 定理 `HasFPowerSeriesWithinOnBall.continuousWithinAt`

English:
theorem HasFPowerSeriesWithinOnBall.continuousWithinAt
  proof: hf.continuousWithinAt_insert.mono (subset_insert x s)

中文:
定理 HasFPowerSeriesWithinOnBall.continuousWithinAt
  证明: hf.continuousWithinAt_insert.mono (subset_insert x s)
-/
protected theorem HasFPowerSeriesWithinOnBall.continuousWithinAt
    (hf : HasFPowerSeriesWithinOnBall f p s x r) :
    ContinuousWithinAt f s x :=
  hf.continuousWithinAt_insert.mono (subset_insert x s)

/--
theorem `HasFPowerSeriesWithinAt.continuousWithinAt_insert` / 定理 `HasFPowerSeriesWithinAt.continuousWithinAt_insert`

English:
theorem HasFPowerSeriesWithinAt.continuousWithinAt_insert
  proof: by
  rcases hf with ⟨r, hr⟩
  apply hr.continuousWithinAt_insert

中文:
定理 HasFPowerSeriesWithinAt.continuousWithinAt_insert
  证明: by
  rcases hf with ⟨r, hr⟩
  apply hr.continuousWithinAt_insert
-/
protected theorem HasFPowerSeriesWithinAt.continuousWithinAt_insert
    (hf : HasFPowerSeriesWithinAt f p s x) :
    ContinuousWithinAt f (insert x s) x := by
  rcases hf with ⟨r, hr⟩
  apply hr.continuousWithinAt_insert

/--
theorem `HasFPowerSeriesWithinAt.continuousWithinAt` / 定理 `HasFPowerSeriesWithinAt.continuousWithinAt`

English:
theorem HasFPowerSeriesWithinAt.continuousWithinAt
  proof: hf.continuousWithinAt_insert.mono (subset_insert x s)

中文:
定理 HasFPowerSeriesWithinAt.continuousWithinAt
  证明: hf.continuousWithinAt_insert.mono (subset_insert x s)
-/
protected theorem HasFPowerSeriesWithinAt.continuousWithinAt
    (hf : HasFPowerSeriesWithinAt f p s x) :
    ContinuousWithinAt f s x :=
  hf.continuousWithinAt_insert.mono (subset_insert x s)

/--
theorem `HasFPowerSeriesAt.continuousAt` / 定理 `HasFPowerSeriesAt.continuousAt`

English:
theorem HasFPowerSeriesAt.continuousAt
  given: (hf : HasFPowerSeriesAt f p x)
  proof: let ⟨_, hr⟩ := hf
  hr.continuousOn.continuousAt (Metric.eball_mem_nhds x hr.r_pos)

中文:
定理 HasFPowerSeriesAt.continuousAt
  条件: (hf : HasFPowerSeriesAt f p x)
  证明: let ⟨_, hr⟩ := hf
  hr.continuousOn.continuousAt (Metric.eball_mem_nhds x hr.r_pos)
-/
protected theorem HasFPowerSeriesAt.continuousAt (hf : HasFPowerSeriesAt f p x) :
    ContinuousAt f x :=
  let ⟨_, hr⟩ := hf
  hr.continuousOn.continuousAt (Metric.eball_mem_nhds x hr.r_pos)

/--
theorem `AnalyticWithinAt.continuousWithinAt_insert` / 定理 `AnalyticWithinAt.continuousWithinAt_insert`

English:
theorem AnalyticWithinAt.continuousWithinAt_insert
  given: (hf : AnalyticWithinAt 𝕜 f s x)
  proof: let ⟨_, hp⟩ := hf
  hp.continuousWithinAt_insert

中文:
定理 AnalyticWithinAt.continuousWithinAt_insert
  条件: (hf : AnalyticWithinAt 𝕜 f s x)
  证明: let ⟨_, hp⟩ := hf
  hp.continuousWithinAt_insert
-/
protected theorem AnalyticWithinAt.continuousWithinAt_insert (hf : AnalyticWithinAt 𝕜 f s x) :
    ContinuousWithinAt f (insert x s) x :=
  let ⟨_, hp⟩ := hf
  hp.continuousWithinAt_insert

/--
theorem `AnalyticWithinAt.continuousWithinAt` / 定理 `AnalyticWithinAt.continuousWithinAt`

English:
theorem AnalyticWithinAt.continuousWithinAt
  given: (hf : AnalyticWithinAt 𝕜 f s x)
  proof: hf.continuousWithinAt_insert.mono (subset_insert x s)

@[fun_prop]

中文:
定理 AnalyticWithinAt.continuousWithinAt
  条件: (hf : AnalyticWithinAt 𝕜 f s x)
  证明: hf.continuousWithinAt_insert.mono (subset_insert x s)

@[fun_prop]
-/
protected theorem AnalyticWithinAt.continuousWithinAt (hf : AnalyticWithinAt 𝕜 f s x) :
    ContinuousWithinAt f s x :=
  hf.continuousWithinAt_insert.mono (subset_insert x s)

@[fun_prop]
/--
theorem `AnalyticAt.continuousAt` / 定理 `AnalyticAt.continuousAt`

English:
theorem AnalyticAt.continuousAt
  given: (hf : AnalyticAt 𝕜 f x)
  statement: ContinuousAt f x
  proof: let ⟨_, hp⟩ := hf
  hp.continuousAt

中文:
定理 AnalyticAt.continuousAt
  条件: (hf : AnalyticAt 𝕜 f x)
  结论: ContinuousAt f x
  证明: let ⟨_, hp⟩ := hf
  hp.continuousAt
-/
protected theorem AnalyticAt.continuousAt (hf : AnalyticAt 𝕜 f x) : ContinuousAt f x :=
  let ⟨_, hp⟩ := hf
  hp.continuousAt

/--
theorem `AnalyticAt.eventually_continuousAt` / 定理 `AnalyticAt.eventually_continuousAt`

English:
theorem AnalyticAt.eventually_continuousAt
  given: (hf : AnalyticAt 𝕜 f x)
  proof: by
  rcases hf with ⟨g, r, hg⟩
  have : Metric.eball x r in 𝓝 x := Metric.eball_mem_nhds _ hg.r_pos
  filter_upwards [this] with y hy
  apply hg.continuousOn.continuousAt
  exact Metric.isOpen_eball.mem_nhds hy

中文:
定理 AnalyticAt.eventually_continuousAt
  条件: (hf : AnalyticAt 𝕜 f x)
  证明: by
  rcases hf with ⟨g, r, hg⟩
  have : Metric.eball x r in 𝓝 x := Metric.eball_mem_nhds _ hg.r_pos
  filter_upwards [this] with y hy
  apply hg.continuousOn.continuousAt
  exact Metric.isOpen_eball.mem_nhds hy
-/
protected theorem AnalyticAt.eventually_continuousAt (hf : AnalyticAt 𝕜 f x) :
    forallᶠ y in 𝓝 x, ContinuousAt f y := by
  rcases hf with ⟨g, r, hg⟩
  have : Metric.eball x r in 𝓝 x := Metric.eball_mem_nhds _ hg.r_pos
  filter_upwards [this] with y hy
  apply hg.continuousOn.continuousAt
  exact Metric.isOpen_eball.mem_nhds hy

/--
theorem `AnalyticOnNhd.continuousOn` / 定理 `AnalyticOnNhd.continuousOn`

English:
theorem AnalyticOnNhd.continuousOn
  given: {s : Set E} (hf : AnalyticOnNhd 𝕜 f s)
  proof: fun x hx => (hf x hx).continuousAt.continuousWithinAt

中文:
定理 AnalyticOnNhd.continuousOn
  条件: {s : Set E} (hf : AnalyticOnNhd 𝕜 f s)
  证明: fun x hx => (hf x hx).continuousAt.continuousWithinAt
-/
protected theorem AnalyticOnNhd.continuousOn {s : Set E} (hf : AnalyticOnNhd 𝕜 f s) :
    ContinuousOn f s :=
  fun x hx => (hf x hx).continuousAt.continuousWithinAt

/--
lemma `AnalyticOn.continuousOn` / 引理 `AnalyticOn.continuousOn`

English:
lemma AnalyticOn.continuousOn
  given: {f : E -> F} {s : Set E} (h : AnalyticOn 𝕜 f s)
  proof: fun x m => (h x m).continuousWithinAt

中文:
引理 AnalyticOn.continuousOn
  条件: {f : E -> F} {s : Set E} (h : AnalyticOn 𝕜 f s)
  证明: fun x m => (h x m).continuousWithinAt
-/
protected lemma AnalyticOn.continuousOn {f : E -> F} {s : Set E} (h : AnalyticOn 𝕜 f s) :
    ContinuousOn f s :=
  fun x m => (h x m).continuousWithinAt

/--
theorem `AnalyticOnNhd.continuous` / 定理 `AnalyticOnNhd.continuous`

English:
theorem AnalyticOnNhd.continuous
  given: {f : E -> F} (fa : AnalyticOnNhd 𝕜 f univ)
  statement: Continuous f
  proof: by
  rw [← continuousOn_univ]; exact fa.continuousOn

中文:
定理 AnalyticOnNhd.continuous
  条件: {f : E -> F} (fa : AnalyticOnNhd 𝕜 f univ)
  结论: Continuous f
  证明: by
  rw [← continuousOn_univ]; exact fa.continuousOn

Depends on / 依赖: continuousOn, continuousOn_univ, fa.continuousOn
-/
theorem AnalyticOnNhd.continuous {f : E -> F} (fa : AnalyticOnNhd 𝕜 f univ) : Continuous f := by
  rw [← continuousOn_univ]; exact fa.continuousOn

/--
theorem `FormalMultilinearSeries.hasFPowerSeriesOnBall` / 定理 `FormalMultilinearSeries.hasFPowerSeriesOnBall`

English:
theorem FormalMultilinearSeries.hasFPowerSeriesOnBall
  statement: [CompleteSpace F]
  proof: { r_le := le_rfl
    r_pos := h
    hasSum := fun hy => by
      rw [zero_add]
      exact p.hasSum hy }

中文:
定理 FormalMultilinearSeries.hasFPowerSeriesOnBall
  结论: [CompleteSpace F]
  证明: { r_le := le_rfl
    r_pos := h
    hasSum := fun hy => by
      rw [zero_add]
      exact p.hasSum hy }
-/
protected theorem FormalMultilinearSeries.hasFPowerSeriesOnBall [CompleteSpace F]
    (p : FormalMultilinearSeries 𝕜 E F) (h : 0 < p.radius) :
    HasFPowerSeriesOnBall p.sum p 0 p.radius :=
  { r_le := le_rfl
    r_pos := h
    hasSum := fun hy => by
      rw [zero_add]
      exact p.hasSum hy }

/--
theorem `HasFPowerSeriesWithinOnBall.sum` / 定理 `HasFPowerSeriesWithinOnBall.sum`

English:
theorem HasFPowerSeriesWithinOnBall.sum
  statement: (h : HasFPowerSeriesWithinOnBall f p s x r) {y : E}
  proof: (h.hasSum h'y hy).tsum_eq.symm

中文:
定理 HasFPowerSeriesWithinOnBall.sum
  结论: (h : HasFPowerSeriesWithinOnBall f p s x r) {y : E}
  证明: (h.hasSum h'y hy).tsum_eq.symm

Depends on / 依赖: h.hasSum, hasSum, tsum_eq, tsum_eq.symm
-/
theorem HasFPowerSeriesWithinOnBall.sum (h : HasFPowerSeriesWithinOnBall f p s x r) {y : E}
    (h'y : x + y in insert x s) (hy : y in Metric.eball (0 : E) r) : f (x + y) = p.sum y :=
  (h.hasSum h'y hy).tsum_eq.symm

/--
theorem `HasFPowerSeriesOnBall.sum` / 定理 `HasFPowerSeriesOnBall.sum`

English:
theorem HasFPowerSeriesOnBall.sum
  statement: (h : HasFPowerSeriesOnBall f p x r) {y : E}
  proof: (h.hasSum hy).tsum_eq.symm

中文:
定理 HasFPowerSeriesOnBall.sum
  结论: (h : HasFPowerSeriesOnBall f p x r) {y : E}
  证明: (h.hasSum hy).tsum_eq.symm

Depends on / 依赖: h.hasSum, hasSum, tsum_eq, tsum_eq.symm
-/
theorem HasFPowerSeriesOnBall.sum (h : HasFPowerSeriesOnBall f p x r) {y : E}
    (hy : y in Metric.eball (0 : E) r) : f (x + y) = p.sum y :=
  (h.hasSum hy).tsum_eq.symm

/--
theorem `FormalMultilinearSeries.continuousOn` / 定理 `FormalMultilinearSeries.continuousOn`

English:
theorem FormalMultilinearSeries.continuousOn
  given: [CompleteSpace F]
  proof: by
  rcases eq_zero_or_pos p.radius with h | h
  · simp [h, continuousOn_empty]
  · exact (p.hasFPowerSeriesOnBall h).continuousOn

中文:
定理 FormalMultilinearSeries.continuousOn
  条件: [CompleteSpace F]
  证明: by
  rcases eq_zero_or_pos p.radius with h | h
  · simp [h, continuousOn_empty]
  · exact (p.hasFPowerSeriesOnBall h).continuousOn
-/
protected theorem FormalMultilinearSeries.continuousOn [CompleteSpace F] :
    ContinuousOn p.sum (Metric.eball 0 p.radius) := by
  rcases eq_zero_or_pos p.radius with h | h
  · simp [h, continuousOn_empty]
  · exact (p.hasFPowerSeriesOnBall h).continuousOn

end

section

open FormalMultilinearSeries

variable {p : FormalMultilinearSeries 𝕜 𝕜 E} {f : 𝕜 -> E} {z₀ : 𝕜}

/--
theorem `hasFPowerSeriesAt_iff` / 定理 `hasFPowerSeriesAt_iff`

English:
theorem hasFPowerSeriesAt_iff
  proof: by
  refine ⟨fun ⟨r, _, r_pos, h⟩ =>
    eventually_of_mem (Metric.eball_mem_nhds 0 r_pos) fun _ => by simpa using h, ?_⟩
  simp only [Metric.eventually_nhds_iff]
  rintro ⟨r, r_pos, h⟩
  refine ⟨p.radius ⊓ r.toNNReal, by simp, ?_, ?_⟩
  · simp only [r_pos.lt, lt_inf_iff, ENNReal.coe_pos, Real.toNNR

中文:
定理 hasFPowerSeriesAt_iff
  证明: by
  refine ⟨fun ⟨r, _, r_pos, h⟩ =>
    eventually_of_mem (Metric.eball_mem_nhds 0 r_pos) fun _ => by simpa using h, ?_⟩
  simp only [Metric.eventually_nhds_iff]
  rintro ⟨r, r_pos, h⟩
  refine ⟨p.radius ⊓ r.toNNReal, by simp, ?_, ?_⟩
  · simp only [r_pos.lt, lt_inf_iff, ENNReal.coe_pos, Real.toNNR

Depends on / 依赖: ENNReal, ENNReal.coe_pos, FormalMultilinearSeries, FormalMultilinearSeries.le_radius_of_tendsto, Metric, Metric.eball_mem_nhds, Metric.eventually_nhds_iff, NormedField, NormedField.exists_norm_lt, Real.toNNReal_pos, and_true, coe_pos, dist_zero_right, eball_mem_nhds, eventually_nhds_iff, eventually_of_mem, exists_norm_lt, le_radius_of_tendsto, le_z, lt_inf_iff
-/
theorem hasFPowerSeriesAt_iff :
    HasFPowerSeriesAt f p z₀ ↔ forallᶠ z in 𝓝 0, HasSum (fun n => z ^ n • p.coeff n) (f (z₀ + z)) := by
  refine ⟨fun ⟨r, _, r_pos, h⟩ =>
    eventually_of_mem (Metric.eball_mem_nhds 0 r_pos) fun _ => by simpa using h, ?_⟩
  simp only [Metric.eventually_nhds_iff]
  rintro ⟨r, r_pos, h⟩
  refine ⟨p.radius ⊓ r.toNNReal, by simp, ?_, ?_⟩
  · simp only [r_pos.lt, lt_inf_iff, ENNReal.coe_pos, Real.toNNReal_pos, and_true]
    obtain ⟨z, z_pos, le_z⟩ := NormedField.exists_norm_lt 𝕜 r_pos.lt
    have : (‖z‖₊ : ENNReal) <= p.radius := by
      simp only [dist_zero_right] at h
      apply FormalMultilinearSeries.le_radius_of_tendsto
      convert! tendsto_norm.comp (h le_z).summable.tendsto_atTop_zero
      simp [norm_smul, mul_comm]
    refine lt_of_lt_of_le ?_ this
    simp only [ENNReal.coe_pos]
    exact zero_lt_iff.mpr (nnnorm_ne_zero_iff.mpr (norm_pos_iff.mp z_pos))
  · simp only [Metric.mem_eball, lt_inf_iff, edist_lt_coe, apply_eq_pow_smul_coeff, and_imp,
      dist_zero_right] at h ⊢
    refine fun {y} _ hyr => h ?_
    simpa [nndist_eq_nnnorm, Real.lt_toNNReal_iff_coe_lt] using hyr

/--
theorem `hasFPowerSeriesAt_iff'` / 定理 `hasFPowerSeriesAt_iff'`

English:
theorem hasFPowerSeriesAt_iff'
  proof: by
  rw [← map_add_left_nhds_zero]; rw [eventually_map]; rw [hasFPowerSeriesAt_iff]
  simp_rw [add_sub_cancel_left]

中文:
定理 hasFPowerSeriesAt_iff'
  证明: by
  rw [← map_add_left_nhds_zero]; rw [eventually_map]; rw [hasFPowerSeriesAt_iff]
  simp_rw [add_sub_cancel_left]

Depends on / 依赖: add_sub_cancel_left, eventually_map, hasFPowerSeriesAt_iff, map_add_left_nhds_zero, simp_rw
-/
theorem hasFPowerSeriesAt_iff' :
    HasFPowerSeriesAt f p z₀ ↔ forallᶠ z in 𝓝 z₀, HasSum (fun n => (z - z₀) ^ n • p.coeff n) (f z) := by
  rw [← map_add_left_nhds_zero]; rw [eventually_map]; rw [hasFPowerSeriesAt_iff]
  simp_rw [add_sub_cancel_left]

end
