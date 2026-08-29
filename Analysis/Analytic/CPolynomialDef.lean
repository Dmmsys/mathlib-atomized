/-
Copyright (c) 2023 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.Analysis.Analytic.ChangeOrigin

/-! We specialize the theory of analytic functions to the case of functions that admit a
development given by a *finite* formal multilinear series. We call them "continuously polynomial",
which is abbreviated to `CPolynomial`. One reason to do that is that we no longer need a
completeness assumption on the target space `F` to make the series converge, so some of the results
are more general. The class of continuously polynomial functions includes functions defined by
polynomials on a normed `𝕜`-algebra and continuous multilinear maps.

## Main definitions

Let `p` be a formal multilinear series from `E` to `F`, i.e., `p n` is a multilinear map on `E^n`
for `n : ℕ`, and let `f` be a function from `E` to `F`.

* `HasFiniteFPowerSeriesOnBall f p x n r`: on the ball of center `x` with radius `r`,
  `f (x + y) = ∑'_n pₘ yᵐ`, and moreover `pₘ = 0` if `n ≤ m`.
* `HasFiniteFPowerSeriesAt f p x n`: on some ball of center `x` with positive radius, holds
  `HasFiniteFPowerSeriesOnBall f p x n r`.
* `CPolynomialAt 𝕜 f x`: there exists a power series `p` and a natural number `n` such that
  holds `HasFPowerSeriesAt f p x n`.
* `CPolynomialOn 𝕜 f s`: the function `f` is analytic at every point of `s`.

In this file, we develop the basic properties of these notions, notably:
* If a function is continuously polynomial, then it is analytic, see
  `HasFiniteFPowerSeriesOnBall.hasFPowerSeriesOnBall`, `HasFiniteFPowerSeriesAt.hasFPowerSeriesAt`,
  `CPolynomialAt.analyticAt` and `CPolynomialOn.analyticOnNhd`.
* The sum of a finite formal power series with positive radius is well defined on the whole space,
  see `FormalMultilinearSeries.hasFiniteFPowerSeriesOnBall_of_finite`.
* If a function admits a finite power series in a ball, then it is continuously polynomial at
  any point `y` of this ball, and the power series there can be expressed in terms of the initial
  power series `p` as `p.changeOrigin y`, which is finite (with the same bound as `p`) by
  `changeOrigin_finite_of_finite`. See `HasFiniteFPowerSeriesOnBall.changeOrigin`. It follows in
  particular that the set of points at which a given function is continuously polynomial is open,
  see `isOpen_cpolynomialAt`.

More API is available in the file `Mathlib/Analysis/Analytic/CPolynomial.lean`, with heavier
imports.
-/

@[expose] public section

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]

open scoped Topology
open Set Filter Asymptotics NNReal ENNReal

variable {f g : E -> F} {p pf pg : FormalMultilinearSeries 𝕜 E F} {x : E} {r r' : Real>=0∞} {n m : Nat}

section FiniteFPowerSeries

/--
Definition of `HasFiniteFPowerSeriesOnBall` / `HasFiniteFPowerSeriesOnBall` 的定义

English:
structure HasFiniteFPowerSeriesOnBall
  parameters: (f : E -> F) (p : FormalMultilinearSeries 𝕜 E F) (x : E)
  extends: HasFPowerSeriesOnBall f p x r
  axioms and operations (1):
    - finite : forall (m : Nat), n <= m -> p m = 0

中文:
结构 有FiniteFPowerSeriesOnBall
  参数: (f : E -> F) (p : FormalMultilinearSeries 𝕜 E F) (x : E)
  继承: 有FPowerSeriesOnBall f p x r
  公理与运算 (1 个):
    - finite : 对任意 (m : 自然数), n <= m -> p m = 0
-/
structure HasFiniteFPowerSeriesOnBall (f : E -> F) (p : FormalMultilinearSeries 𝕜 E F) (x : E)
    (n : Nat) (r : Real>=0∞) : Prop extends HasFPowerSeriesOnBall f p x r where
  finite : forall (m : Nat), n <= m -> p m = 0

/--
theorem `HasFiniteFPowerSeriesOnBall.mk'` / 定理 `HasFiniteFPowerSeriesOnBall.mk'`

English:
theorem HasFiniteFPowerSeriesOnBall.mk'
  statement: {f : E -> F} {p : FormalMultilinearSeries 𝕜 E F} {x : E}
  proof: p.radius_eq_top_of_eventually_eq_zero (Filter.eventually_atTop.mpr ⟨n, finite⟩) ▸ le_top
  r_pos := pos
  hasSum hy := sum_eq _ hy ▸ hasSum_sum_of_ne_finset_zero fun m hm => by
    rw [Finset.mem_range]; rw [not_lt] at hm; rw [finite m hm]; rfl
  finite := finite

中文:
定理 有FiniteFPowerSeriesOnBall.mk'
  结论: {f : E -> F} {p : FormalMultilinearSeries 𝕜 E F} {x : E}
  证明: p.radius_eq_top_of_eventually_eq_zero (Filter.eventually_atTop.mpr ⟨n, finite⟩) ▸ le_top
  r_pos := pos
  hasSum hy := sum_eq _ hy ▸ hasSum_sum_of_ne_finset_zero fun m hm => by
    rw [Finset.mem_range]; rw [not_lt] at hm; rw [finite m hm]; rfl
  finite := finite

Depends on / 依赖: Filter, Filter.eventually_atTop.mpr, eventually_atTop, finite, le_top, p.radius_eq_top_of_eventually_eq_zero, radius_eq_top_of_eventually_eq_zero
-/
theorem HasFiniteFPowerSeriesOnBall.mk' {f : E -> F} {p : FormalMultilinearSeries 𝕜 E F} {x : E}
    {n : Nat} {r : Real>=0∞} (finite : forall (m : Nat), n <= m -> p m = 0) (pos : 0 < r)
    (sum_eq : forall y in Metric.eball 0 r, (∑ i in Finset.range n, p i fun _ => y) = f (x + y)) :
    HasFiniteFPowerSeriesOnBall f p x n r where
  r_le := p.radius_eq_top_of_eventually_eq_zero (Filter.eventually_atTop.mpr ⟨n, finite⟩) ▸ le_top
  r_pos := pos
  hasSum hy := sum_eq _ hy ▸ hasSum_sum_of_ne_finset_zero fun m hm => by
    rw [Finset.mem_range]; rw [not_lt] at hm; rw [finite m hm]; rfl
  finite := finite

/--
Definition of `HasFiniteFPowerSeriesAt` / `HasFiniteFPowerSeriesAt` 的定义

English:
definition HasFiniteFPowerSeriesAt
  signature: (f : E -> F) (p : FormalMultilinearSeries 𝕜 E F) (x : E) (n : Nat)
  body: exists r, HasFiniteFPowerSeriesOnBall f p x n r

中文:
定义 HasFiniteFPowerSeriesAt
  签名: (f : E -> F) (p : FormalMultilinearSeries 𝕜 E F) (x : E) (n : 自然数)
  定义体: exists r, HasFiniteFPowerSeriesOnBall f p x n r

Depends on / 依赖: HasFiniteFPowerSeriesOnBall
-/
def HasFiniteFPowerSeriesAt (f : E -> F) (p : FormalMultilinearSeries 𝕜 E F) (x : E) (n : Nat) :=
  exists r, HasFiniteFPowerSeriesOnBall f p x n r

/--
theorem `HasFiniteFPowerSeriesAt.hasFPowerSeriesAt` / 定理 `HasFiniteFPowerSeriesAt.hasFPowerSeriesAt`

English:
theorem HasFiniteFPowerSeriesAt.hasFPowerSeriesAt
  proof: let ⟨r, hf⟩ := hf
  ⟨r, hf.toHasFPowerSeriesOnBall⟩

中文:
定理 HasFiniteFPowerSeriesAt.hasFPowerSeriesAt
  证明: let ⟨r, hf⟩ := hf
  ⟨r, hf.toHasFPowerSeriesOnBall⟩

Depends on / 依赖: hf.toHasFPowerSeriesOnBall, toHasFPowerSeriesOnBall
-/
theorem HasFiniteFPowerSeriesAt.hasFPowerSeriesAt
    (hf : HasFiniteFPowerSeriesAt f p x n) : HasFPowerSeriesAt f p x :=
  let ⟨r, hf⟩ := hf
  ⟨r, hf.toHasFPowerSeriesOnBall⟩

/--
theorem `HasFiniteFPowerSeriesAt.finite` / 定理 `HasFiniteFPowerSeriesAt.finite`

English:
theorem HasFiniteFPowerSeriesAt.finite
  given: (hf : HasFiniteFPowerSeriesAt f p x n)
  proof: let ⟨_, hf⟩ := hf; hf.finite

中文:
定理 HasFiniteFPowerSeriesAt.finite
  条件: (hf : HasFiniteFPowerSeriesAt f p x n)
  证明: let ⟨_, hf⟩ := hf; hf.finite

Depends on / 依赖: finite, hf.finite
-/
theorem HasFiniteFPowerSeriesAt.finite (hf : HasFiniteFPowerSeriesAt f p x n) :
    forall m : Nat, n <= m -> p m = 0 := let ⟨_, hf⟩ := hf; hf.finite

variable (𝕜)

/--
Definition of `CPolynomialAt` / `CPolynomialAt` 的定义

English:
definition CPolynomialAt
  signature: (f : E -> F) (x : E)
  body: exists (p : FormalMultilinearSeries 𝕜 E F) (n : Nat), HasFiniteFPowerSeriesAt f p x n

中文:
定义 CPolynomialAt
  签名: (f : E -> F) (x : E)
  定义体: exists (p : FormalMultilinearSeries 𝕜 E F) (n : Nat), HasFiniteFPowerSeriesAt f p x n

Depends on / 依赖: FormalMultilinearSeries, HasFiniteFPowerSeriesAt
-/
def CPolynomialAt (f : E -> F) (x : E) :=
  exists (p : FormalMultilinearSeries 𝕜 E F) (n : Nat), HasFiniteFPowerSeriesAt f p x n

/--
Definition of `CPolynomialOn` / `CPolynomialOn` 的定义

English:
definition CPolynomialOn
  signature: (f : E -> F) (s : Set E)
  body: forall x, x in s -> CPolynomialAt 𝕜 f x

中文:
定义 CPolynomialOn
  签名: (f : E -> F) (s : 集合 E)
  定义体: forall x, x in s -> CPolynomialAt 𝕜 f x

Depends on / 依赖: CPolynomialAt
-/
def CPolynomialOn (f : E -> F) (s : Set E) :=
  forall x, x in s -> CPolynomialAt 𝕜 f x

variable {𝕜}

/--
theorem `HasFiniteFPowerSeriesOnBall.hasFiniteFPowerSeriesAt` / 定理 `HasFiniteFPowerSeriesOnBall.hasFiniteFPowerSeriesAt`

English:
theorem HasFiniteFPowerSeriesOnBall.hasFiniteFPowerSeriesAt
  proof: ⟨r, hf⟩

中文:
定理 有FiniteFPowerSeriesOnBall.hasFiniteFPowerSeriesAt
  证明: ⟨r, hf⟩
-/
theorem HasFiniteFPowerSeriesOnBall.hasFiniteFPowerSeriesAt
    (hf : HasFiniteFPowerSeriesOnBall f p x n r) :
    HasFiniteFPowerSeriesAt f p x n :=
  ⟨r, hf⟩

/--
theorem `HasFiniteFPowerSeriesAt.cpolynomialAt` / 定理 `HasFiniteFPowerSeriesAt.cpolynomialAt`

English:
theorem HasFiniteFPowerSeriesAt.cpolynomialAt
  given: (hf : HasFiniteFPowerSeriesAt f p x n)
  proof: ⟨p, n, hf⟩

中文:
定理 HasFiniteFPowerSeriesAt.cpolynomialAt
  条件: (hf : HasFiniteFPowerSeriesAt f p x n)
  证明: ⟨p, n, hf⟩
-/
theorem HasFiniteFPowerSeriesAt.cpolynomialAt (hf : HasFiniteFPowerSeriesAt f p x n) :
    CPolynomialAt 𝕜 f x :=
  ⟨p, n, hf⟩

/--
theorem `HasFiniteFPowerSeriesOnBall.cpolynomialAt` / 定理 `HasFiniteFPowerSeriesOnBall.cpolynomialAt`

English:
theorem HasFiniteFPowerSeriesOnBall.cpolynomialAt
  given: (hf : HasFiniteFPowerSeriesOnBall f p x n r)
  proof: hf.hasFiniteFPowerSeriesAt.cpolynomialAt

中文:
定理 有FiniteFPowerSeriesOnBall.cpolynomialAt
  条件: (hf : 有FiniteFPowerSeriesOnBall f p x n r)
  证明: hf.hasFiniteFPowerSeriesAt.cpolynomialAt

Depends on / 依赖: cpolynomialAt, hasFiniteFPowerSeriesAt, hf.hasFiniteFPowerSeriesAt.cpolynomialAt
-/
theorem HasFiniteFPowerSeriesOnBall.cpolynomialAt (hf : HasFiniteFPowerSeriesOnBall f p x n r) :
    CPolynomialAt 𝕜 f x :=
  hf.hasFiniteFPowerSeriesAt.cpolynomialAt

/--
theorem `CPolynomialAt.analyticAt` / 定理 `CPolynomialAt.analyticAt`

English:
theorem CPolynomialAt.analyticAt
  given: (hf : CPolynomialAt 𝕜 f x)
  statement: AnalyticAt 𝕜 f x
  proof: let ⟨p, _, hp⟩ := hf
  ⟨p, hp.hasFPowerSeriesAt⟩

中文:
定理 CPolynomialAt.analyticAt
  条件: (hf : CPolynomialAt 𝕜 f x)
  结论: AnalyticAt 𝕜 f x
  证明: let ⟨p, _, hp⟩ := hf
  ⟨p, hp.hasFPowerSeriesAt⟩

Depends on / 依赖: hasFPowerSeriesAt, hp.hasFPowerSeriesAt
-/
theorem CPolynomialAt.analyticAt (hf : CPolynomialAt 𝕜 f x) : AnalyticAt 𝕜 f x :=
  let ⟨p, _, hp⟩ := hf
  ⟨p, hp.hasFPowerSeriesAt⟩

/--
theorem `CPolynomialAt.analyticWithinAt` / 定理 `CPolynomialAt.analyticWithinAt`

English:
theorem CPolynomialAt.analyticWithinAt
  given: {s : Set E} (hf : CPolynomialAt 𝕜 f x)
  proof: hf.analyticAt.analyticWithinAt

中文:
定理 CPolynomialAt.analyticWithinAt
  条件: {s : 集合 E} (hf : CPolynomialAt 𝕜 f x)
  证明: hf.analyticAt.analyticWithinAt

Depends on / 依赖: analyticAt, analyticWithinAt, hf.analyticAt.analyticWithinAt
-/
theorem CPolynomialAt.analyticWithinAt {s : Set E} (hf : CPolynomialAt 𝕜 f x) :
    AnalyticWithinAt 𝕜 f s x :=
  hf.analyticAt.analyticWithinAt

/--
theorem `CPolynomialOn.analyticOnNhd` / 定理 `CPolynomialOn.analyticOnNhd`

English:
theorem CPolynomialOn.analyticOnNhd
  given: {s : Set E} (hf : CPolynomialOn 𝕜 f s)
  statement: AnalyticOnNhd 𝕜 f s
  proof: fun x hx => (hf x hx).analyticAt

中文:
定理 CPolynomialOn.analyticOnNhd
  条件: {s : 集合 E} (hf : CPolynomialOn 𝕜 f s)
  结论: AnalyticOnNhd 𝕜 f s
  证明: fun x hx => (hf x hx).analyticAt

Depends on / 依赖: analyticAt
-/
theorem CPolynomialOn.analyticOnNhd {s : Set E} (hf : CPolynomialOn 𝕜 f s) : AnalyticOnNhd 𝕜 f s :=
  fun x hx => (hf x hx).analyticAt

/--
theorem `CPolynomialOn.analyticOn` / 定理 `CPolynomialOn.analyticOn`

English:
theorem CPolynomialOn.analyticOn
  given: {s : Set E} (hf : CPolynomialOn 𝕜 f s)
  statement: AnalyticOn 𝕜 f s
  proof: hf.analyticOnNhd.analyticOn

中文:
定理 CPolynomialOn.analyticOn
  条件: {s : 集合 E} (hf : CPolynomialOn 𝕜 f s)
  结论: AnalyticOn 𝕜 f s
  证明: hf.analyticOnNhd.analyticOn

Depends on / 依赖: analyticOn, analyticOnNhd, hf.analyticOnNhd.analyticOn
-/
theorem CPolynomialOn.analyticOn {s : Set E} (hf : CPolynomialOn 𝕜 f s) : AnalyticOn 𝕜 f s :=
  hf.analyticOnNhd.analyticOn

/--
theorem `HasFiniteFPowerSeriesOnBall.congr` / 定理 `HasFiniteFPowerSeriesOnBall.congr`

English:
theorem HasFiniteFPowerSeriesOnBall.congr
  statement: (hf : HasFiniteFPowerSeriesOnBall f p x n r)
  proof: ⟨hf.1.congr hg, hf.finite⟩

中文:
定理 有FiniteFPowerSeriesOnBall.congr
  结论: (hf : 有FiniteFPowerSeriesOnBall f p x n r)
  证明: ⟨hf.1.congr hg, hf.finite⟩

Depends on / 依赖: finite, hf.finite
-/
theorem HasFiniteFPowerSeriesOnBall.congr (hf : HasFiniteFPowerSeriesOnBall f p x n r)
    (hg : EqOn f g (Metric.eball x r)) : HasFiniteFPowerSeriesOnBall g p x n r :=
  ⟨hf.1.congr hg, hf.finite⟩

/--
theorem `HasFiniteFPowerSeriesOnBall.of_le` / 定理 `HasFiniteFPowerSeriesOnBall.of_le`

English:
theorem HasFiniteFPowerSeriesOnBall.of_le
  statement: {m n : Nat}
  proof: ⟨h.toHasFPowerSeriesOnBall, fun i hi => h.finite i (hmn.trans hi)⟩

中文:
定理 有FiniteFPowerSeriesOnBall.of_le
  结论: {m n : 自然数}
  证明: ⟨h.toHasFPowerSeriesOnBall, fun i hi => h.finite i (hmn.trans hi)⟩

Depends on / 依赖: finite, h.finite, h.toHasFPowerSeriesOnBall, hmn.trans, toHasFPowerSeriesOnBall
-/
theorem HasFiniteFPowerSeriesOnBall.of_le {m n : Nat}
    (h : HasFiniteFPowerSeriesOnBall f p x n r) (hmn : n <= m) :
    HasFiniteFPowerSeriesOnBall f p x m r :=
  ⟨h.toHasFPowerSeriesOnBall, fun i hi => h.finite i (hmn.trans hi)⟩

/--
theorem `HasFiniteFPowerSeriesAt.of_le` / 定理 `HasFiniteFPowerSeriesAt.of_le`

English:
theorem HasFiniteFPowerSeriesAt.of_le
  statement: {m n : Nat}
  proof: by
  rcases h with ⟨r, hr⟩
  exact ⟨r, hr.of_le hmn⟩

中文:
定理 HasFiniteFPowerSeriesAt.of_le
  结论: {m n : 自然数}
  证明: by
  rcases h with ⟨r, hr⟩
  exact ⟨r, hr.of_le hmn⟩

Depends on / 依赖: hr.of_le, of_le
-/
theorem HasFiniteFPowerSeriesAt.of_le {m n : Nat}
    (h : HasFiniteFPowerSeriesAt f p x n) (hmn : n <= m) :
    HasFiniteFPowerSeriesAt f p x m := by
  rcases h with ⟨r, hr⟩
  exact ⟨r, hr.of_le hmn⟩

/--
theorem `HasFiniteFPowerSeriesOnBall.comp_sub` / 定理 `HasFiniteFPowerSeriesOnBall.comp_sub`

English:
theorem HasFiniteFPowerSeriesOnBall.comp_sub
  given: (hf : HasFiniteFPowerSeriesOnBall f p x n r) (y : E)
  proof: ⟨hf.1.comp_sub y, hf.finite⟩

中文:
定理 有FiniteFPowerSeriesOnBall.comp_sub
  条件: (hf : 有FiniteFPowerSeriesOnBall f p x n r) (y : E)
  证明: ⟨hf.1.comp_sub y, hf.finite⟩

Depends on / 依赖: comp_sub, finite, hf.finite
-/
theorem HasFiniteFPowerSeriesOnBall.comp_sub (hf : HasFiniteFPowerSeriesOnBall f p x n r) (y : E) :
    HasFiniteFPowerSeriesOnBall (fun z => f (z - y)) p (x + y) n r :=
  ⟨hf.1.comp_sub y, hf.finite⟩

/--
theorem `HasFiniteFPowerSeriesOnBall.mono` / 定理 `HasFiniteFPowerSeriesOnBall.mono`

English:
theorem HasFiniteFPowerSeriesOnBall.mono
  statement: (hf : HasFiniteFPowerSeriesOnBall f p x n r)
  proof: ⟨hf.1.mono r'_pos hr, hf.finite⟩

中文:
定理 有FiniteFPowerSeriesOnBall.mono
  结论: (hf : 有FiniteFPowerSeriesOnBall f p x n r)
  证明: ⟨hf.1.mono r'_pos hr, hf.finite⟩

Depends on / 依赖: _pos, finite, hf.finite
-/
theorem HasFiniteFPowerSeriesOnBall.mono (hf : HasFiniteFPowerSeriesOnBall f p x n r)
    (r'_pos : 0 < r') (hr : r' <= r) : HasFiniteFPowerSeriesOnBall f p x n r' :=
  ⟨hf.1.mono r'_pos hr, hf.finite⟩

/--
theorem `HasFiniteFPowerSeriesAt.congr` / 定理 `HasFiniteFPowerSeriesAt.congr`

English:
theorem HasFiniteFPowerSeriesAt.congr
  given: (hf : HasFiniteFPowerSeriesAt f p x n) (hg : f =ᶠ[𝓝 x] g)
  proof: Exists.imp (fun _ hg => ⟨hg, hf.finite⟩) (hf.hasFPowerSeriesAt.congr hg)

中文:
定理 HasFiniteFPowerSeriesAt.congr
  条件: (hf : HasFiniteFPowerSeriesAt f p x n) (hg : f =ᶠ[𝓝 x] g)
  证明: Exists.imp (fun _ hg => ⟨hg, hf.finite⟩) (hf.hasFPowerSeriesAt.congr hg)

Depends on / 依赖: Exists, Exists.imp, finite, hasFPowerSeriesAt, hf.finite, hf.hasFPowerSeriesAt.congr
-/
theorem HasFiniteFPowerSeriesAt.congr (hf : HasFiniteFPowerSeriesAt f p x n) (hg : f =ᶠ[𝓝 x] g) :
    HasFiniteFPowerSeriesAt g p x n :=
  Exists.imp (fun _ hg => ⟨hg, hf.finite⟩) (hf.hasFPowerSeriesAt.congr hg)

/--
theorem `HasFiniteFPowerSeriesAt.eventually` / 定理 `HasFiniteFPowerSeriesAt.eventually`

English:
theorem HasFiniteFPowerSeriesAt.eventually
  given: (hf : HasFiniteFPowerSeriesAt f p x n)
  proof: hf.hasFPowerSeriesAt.eventually.mono fun _ h => ⟨h, hf.finite⟩

中文:
定理 HasFiniteFPowerSeriesAt.eventually
  条件: (hf : HasFiniteFPowerSeriesAt f p x n)
  证明: hf.hasFPowerSeriesAt.eventually.mono fun _ h => ⟨h, hf.finite⟩
-/
protected theorem HasFiniteFPowerSeriesAt.eventually (hf : HasFiniteFPowerSeriesAt f p x n) :
    forallᶠ r : Real>=0∞ in 𝓝[>] 0, HasFiniteFPowerSeriesOnBall f p x n r :=
  hf.hasFPowerSeriesAt.eventually.mono fun _ h => ⟨h, hf.finite⟩

/--
theorem `CPolynomialAt.congr` / 定理 `CPolynomialAt.congr`

English:
theorem CPolynomialAt.congr
  given: (hf : CPolynomialAt 𝕜 f x) (hg : f =ᶠ[𝓝 x] g)
  statement: CPolynomialAt 𝕜 g x
  proof: let ⟨_, _, hpf⟩ := hf
  (hpf.congr hg).cpolynomialAt

中文:
定理 CPolynomialAt.congr
  条件: (hf : CPolynomialAt 𝕜 f x) (hg : f =ᶠ[𝓝 x] g)
  结论: CPolynomialAt 𝕜 g x
  证明: let ⟨_, _, hpf⟩ := hf
  (hpf.congr hg).cpolynomialAt

Depends on / 依赖: cpolynomialAt, hpf.congr
-/
theorem CPolynomialAt.congr (hf : CPolynomialAt 𝕜 f x) (hg : f =ᶠ[𝓝 x] g) : CPolynomialAt 𝕜 g x :=
  let ⟨_, _, hpf⟩ := hf
  (hpf.congr hg).cpolynomialAt

/--
theorem `CPolynomialAt_congr` / 定理 `CPolynomialAt_congr`

English:
theorem CPolynomialAt_congr
  given: (h : f =ᶠ[𝓝 x] g)
  statement: CPolynomialAt 𝕜 f x ↔ CPolynomialAt 𝕜 g x
  proof: ⟨fun hf => hf.congr h, fun hg => hg.congr h.symm⟩

中文:
定理 CPolynomialAt_congr
  条件: (h : f =ᶠ[𝓝 x] g)
  结论: CPolynomialAt 𝕜 f x ↔ CPolynomialAt 𝕜 g x
  证明: ⟨fun hf => hf.congr h, fun hg => hg.congr h.symm⟩

Depends on / 依赖: h.symm, hf.congr, hg.congr
-/
theorem CPolynomialAt_congr (h : f =ᶠ[𝓝 x] g) : CPolynomialAt 𝕜 f x ↔ CPolynomialAt 𝕜 g x :=
  ⟨fun hf => hf.congr h, fun hg => hg.congr h.symm⟩

/--
theorem `CPolynomialOn.mono` / 定理 `CPolynomialOn.mono`

English:
theorem CPolynomialOn.mono
  given: {s t : Set E} (hf : CPolynomialOn 𝕜 f t) (hst : s subseteq t)
  proof: fun z hz => hf z (hst hz)

中文:
定理 CPolynomialOn.mono
  条件: {s t : 集合 E} (hf : CPolynomialOn 𝕜 f t) (hst : s subseteq t)
  证明: fun z hz => hf z (hst hz)
-/
theorem CPolynomialOn.mono {s t : Set E} (hf : CPolynomialOn 𝕜 f t) (hst : s subseteq t) :
    CPolynomialOn 𝕜 f s :=
  fun z hz => hf z (hst hz)

/--
theorem `CPolynomialOn.congr'` / 定理 `CPolynomialOn.congr'`

English:
theorem CPolynomialOn.congr'
  given: {s : Set E} (hf : CPolynomialOn 𝕜 f s) (hg : f =ᶠ[𝓝ˢ s] g)
  proof: fun z hz => (hf z hz).congr (mem_nhdsSet_iff_forall.mp hg z hz)

中文:
定理 CPolynomialOn.congr'
  条件: {s : 集合 E} (hf : CPolynomialOn 𝕜 f s) (hg : f =ᶠ[𝓝ˢ s] g)
  证明: fun z hz => (hf z hz).congr (mem_nhdsSet_iff_forall.mp hg z hz)

Depends on / 依赖: mem_nhdsSet_iff_forall, mem_nhdsSet_iff_forall.mp
-/
theorem CPolynomialOn.congr' {s : Set E} (hf : CPolynomialOn 𝕜 f s) (hg : f =ᶠ[𝓝ˢ s] g) :
    CPolynomialOn 𝕜 g s :=
  fun z hz => (hf z hz).congr (mem_nhdsSet_iff_forall.mp hg z hz)

/--
theorem `CPolynomialOn_congr'` / 定理 `CPolynomialOn_congr'`

English:
theorem CPolynomialOn_congr'
  given: {s : Set E} (h : f =ᶠ[𝓝ˢ s] g)
  proof: ⟨fun hf => hf.congr' h, fun hg => hg.congr' h.symm⟩

中文:
定理 CPolynomialOn_congr'
  条件: {s : 集合 E} (h : f =ᶠ[𝓝ˢ s] g)
  证明: ⟨fun hf => hf.congr' h, fun hg => hg.congr' h.symm⟩

Depends on / 依赖: h.symm, hf.congr, hg.congr
-/
theorem CPolynomialOn_congr' {s : Set E} (h : f =ᶠ[𝓝ˢ s] g) :
    CPolynomialOn 𝕜 f s ↔ CPolynomialOn 𝕜 g s :=
  ⟨fun hf => hf.congr' h, fun hg => hg.congr' h.symm⟩

/--
theorem `CPolynomialOn.congr` / 定理 `CPolynomialOn.congr`

English:
theorem CPolynomialOn.congr
  statement: {s : Set E} (hs : IsOpen s) (hf : CPolynomialOn 𝕜 f s)
  proof: hf.congr' mem_nhdsSet_iff_forall.mpr
    (fun _ hz => eventuallyEq_iff_exists_mem.mpr ⟨s, hs.mem_nhds hz, hg⟩)

中文:
定理 CPolynomialOn.congr
  结论: {s : 集合 E} (hs : 是开集 s) (hf : CPolynomialOn 𝕜 f s)
  证明: hf.congr' mem_nhdsSet_iff_forall.mpr
    (fun _ hz => eventuallyEq_iff_exists_mem.mpr ⟨s, hs.mem_nhds hz, hg⟩)

Depends on / 依赖: eventuallyEq_iff_exists_mem, eventuallyEq_iff_exists_mem.mpr, hf.congr, hs.mem_nhds, mem_nhds, mem_nhdsSet_iff_forall, mem_nhdsSet_iff_forall.mpr
-/
theorem CPolynomialOn.congr {s : Set E} (hs : IsOpen s) (hf : CPolynomialOn 𝕜 f s)
    (hg : s.EqOn f g) : CPolynomialOn 𝕜 g s :=
hf.congr' mem_nhdsSet_iff_forall.mpr
    (fun _ hz => eventuallyEq_iff_exists_mem.mpr ⟨s, hs.mem_nhds hz, hg⟩)

/--
theorem `CPolynomialOn_congr` / 定理 `CPolynomialOn_congr`

English:
theorem CPolynomialOn_congr
  given: {s : Set E} (hs : IsOpen s) (h : s.EqOn f g)
  proof: ⟨fun hf => hf.congr hs h, fun hg => hg.congr hs h.symm⟩

中文:
定理 CPolynomialOn_congr
  条件: {s : 集合 E} (hs : 是开集 s) (h : s.EqOn f g)
  证明: ⟨fun hf => hf.congr hs h, fun hg => hg.congr hs h.symm⟩

Depends on / 依赖: h.symm, hf.congr, hg.congr
-/
theorem CPolynomialOn_congr {s : Set E} (hs : IsOpen s) (h : s.EqOn f g) :
    CPolynomialOn 𝕜 f s ↔ CPolynomialOn 𝕜 g s :=
  ⟨fun hf => hf.congr hs h, fun hg => hg.congr hs h.symm⟩

/--
theorem `ContinuousLinearMap.comp_hasFiniteFPowerSeriesOnBall` / 定理 `ContinuousLinearMap.comp_hasFiniteFPowerSeriesOnBall`

English:
theorem ContinuousLinearMap.comp_hasFiniteFPowerSeriesOnBall
  statement: (g : F ->L[𝕜] G)
  proof: ⟨g.comp_hasFPowerSeriesOnBall h.1, fun m hm => by
    rw [compFormalMultilinearSeries_apply]; rw [h.finite m hm]
    ext; exact map_zero g⟩

中文:
定理 连续线性映射.comp_hasFiniteFPowerSeriesOnBall
  结论: (g : F ->L[𝕜] G)
  证明: ⟨g.comp_hasFPowerSeriesOnBall h.1, fun m hm => by
    rw [compFormalMultilinearSeries_apply]; rw [h.finite m hm]
    ext; exact map_zero g⟩

Depends on / 依赖: compFormalMultilinearSeries_apply, comp_hasFPowerSeriesOnBall, finite, g.comp_hasFPowerSeriesOnBall, h.finite, map_zero
-/
theorem ContinuousLinearMap.comp_hasFiniteFPowerSeriesOnBall (g : F ->L[𝕜] G)
    (h : HasFiniteFPowerSeriesOnBall f p x n r) :
    HasFiniteFPowerSeriesOnBall (g ∘ f) (g.compFormalMultilinearSeries p) x n r :=
  ⟨g.comp_hasFPowerSeriesOnBall h.1, fun m hm => by
    rw [compFormalMultilinearSeries_apply]; rw [h.finite m hm]
    ext; exact map_zero g⟩

/--
theorem `ContinuousLinearMap.comp_cpolynomialOn` / 定理 `ContinuousLinearMap.comp_cpolynomialOn`

English:
theorem ContinuousLinearMap.comp_cpolynomialOn
  statement: {s : Set E} (g : F ->L[𝕜] G)
  proof: by
  rintro x hx
  rcases h x hx with ⟨p, n, r, hp⟩
  exact ⟨g.compFormalMultilinearSeries p, n, r, g.comp_hasFiniteFPowerSeriesOnBall hp⟩

中文:
定理 连续线性映射.comp_cpolynomialOn
  结论: {s : 集合 E} (g : F ->L[𝕜] G)
  证明: by
  rintro x hx
  rcases h x hx with ⟨p, n, r, hp⟩
  exact ⟨g.compFormalMultilinearSeries p, n, r, g.comp_hasFiniteFPowerSeriesOnBall hp⟩

Depends on / 依赖: compFormalMultilinearSeries, comp_hasFiniteFPowerSeriesOnBall, g.compFormalMultilinearSeries, g.comp_hasFiniteFPowerSeriesOnBall
-/
theorem ContinuousLinearMap.comp_cpolynomialOn {s : Set E} (g : F ->L[𝕜] G)
    (h : CPolynomialOn 𝕜 f s) : CPolynomialOn 𝕜 (g ∘ f) s := by
  rintro x hx
  rcases h x hx with ⟨p, n, r, hp⟩
  exact ⟨g.compFormalMultilinearSeries p, n, r, g.comp_hasFiniteFPowerSeriesOnBall hp⟩

/--
theorem `HasFiniteFPowerSeriesOnBall.eq_partialSum` / 定理 `HasFiniteFPowerSeriesOnBall.eq_partialSum`

English:
theorem HasFiniteFPowerSeriesOnBall.eq_partialSum
  proof: fun y hy m hm => (hf.hasSum hy).unique (hasSum_sum_of_ne_finset_zero
    (f := fun m => p m (fun _ => y)) (s := Finset.range m)
    (fun N hN => by simp only [Finset.mem_range, not_lt] at hN
                    rw [hf.finite _ (le_trans hm hN)]; rw [zero_apply]))

中文:
定理 有FiniteFPowerSeriesOnBall.eq_partialSum
  证明: fun y hy m hm => (hf.hasSum hy).unique (hasSum_sum_of_ne_finset_zero
    (f := fun m => p m (fun _ => y)) (s := Finset.range m)
    (fun N hN => by simp only [Finset.mem_range, not_lt] at hN
                    rw [hf.finite _ (le_trans hm hN)]; rw [zero_apply]))

Depends on / 依赖: Finset, Finset.mem_range, Finset.range, finite, hasSum, hasSum_sum_of_ne_finset_zero, hf.finite, hf.hasSum, le_trans, mem_range, not_lt, unique, zero_apply
-/
theorem HasFiniteFPowerSeriesOnBall.eq_partialSum
    (hf : HasFiniteFPowerSeriesOnBall f p x n r) :
    forall y in Metric.eball (0 : E) r, forall m, n <= m ->
    f (x + y) = p.partialSum m y :=
  fun y hy m hm => (hf.hasSum hy).unique (hasSum_sum_of_ne_finset_zero
    (f := fun m => p m (fun _ => y)) (s := Finset.range m)
    (fun N hN => by simp only [Finset.mem_range, not_lt] at hN
                    rw [hf.finite _ (le_trans hm hN)]; rw [zero_apply]))

/--
theorem `HasFiniteFPowerSeriesOnBall.eq_partialSum'` / 定理 `HasFiniteFPowerSeriesOnBall.eq_partialSum'`

English:
theorem HasFiniteFPowerSeriesOnBall.eq_partialSum'
  proof: by
  intro y hy m hm
  rw [Metric.mem_eball]; rw [edist_eq_enorm_sub]; rw [← mem_eball_zero_iff] at hy
  rw [← (HasFiniteFPowerSeriesOnBall.eq_partialSum hf _ hy m hm)]; rw [add_sub_cancel]

中文:
定理 有FiniteFPowerSeriesOnBall.eq_partialSum'
  证明: by
  intro y hy m hm
  rw [Metric.mem_eball]; rw [edist_eq_enorm_sub]; rw [← mem_eball_zero_iff] at hy
  rw [← (HasFiniteFPowerSeriesOnBall.eq_partialSum hf _ hy m hm)]; rw [add_sub_cancel]

Depends on / 依赖: HasFiniteFPowerSeriesOnBall, HasFiniteFPowerSeriesOnBall.eq_partialSum, Metric, Metric.mem_eball, add_sub_cancel, edist_eq_enorm_sub, eq_partialSum, mem_eball, mem_eball_zero_iff
-/
theorem HasFiniteFPowerSeriesOnBall.eq_partialSum'
    (hf : HasFiniteFPowerSeriesOnBall f p x n r) :
    forall y in Metric.eball x r, forall m, n <= m ->
    f y = p.partialSum m (y - x) := by
  intro y hy m hm
  rw [Metric.mem_eball]; rw [edist_eq_enorm_sub]; rw [← mem_eball_zero_iff] at hy
  rw [← (HasFiniteFPowerSeriesOnBall.eq_partialSum hf _ hy m hm)]; rw [add_sub_cancel]

/-! The particular cases where `f` has a finite power series bounded by `0` or `1`. -/

/--
theorem `HasFiniteFPowerSeriesOnBall.eq_zero_of_bound_zero` / 定理 `HasFiniteFPowerSeriesOnBall.eq_zero_of_bound_zero`

English:
theorem HasFiniteFPowerSeriesOnBall.eq_zero_of_bound_zero
  proof: by
  intro y hy
  rw [hf.eq_partialSum' y hy 0 le_rfl]; rw [FormalMultilinearSeries.partialSum]
  simp only [Finset.range_zero, Finset.sum_empty]

中文:
定理 有FiniteFPowerSeriesOnBall.eq_zero_of_bound_zero
  证明: by
  intro y hy
  rw [hf.eq_partialSum' y hy 0 le_rfl]; rw [FormalMultilinearSeries.partialSum]
  simp only [Finset.range_zero, Finset.sum_empty]

Depends on / 依赖: Finset, Finset.range_zero, Finset.sum_empty, FormalMultilinearSeries, FormalMultilinearSeries.partialSum, eq_partialSum, hf.eq_partialSum, le_rfl, partialSum, range_zero, sum_empty
-/
theorem HasFiniteFPowerSeriesOnBall.eq_zero_of_bound_zero
    (hf : HasFiniteFPowerSeriesOnBall f pf x 0 r) : forall y in Metric.eball x r, f y = 0 := by
  intro y hy
  rw [hf.eq_partialSum' y hy 0 le_rfl]; rw [FormalMultilinearSeries.partialSum]
  simp only [Finset.range_zero, Finset.sum_empty]

/--
theorem `HasFiniteFPowerSeriesOnBall.bound_zero_of_eq_zero` / 定理 `HasFiniteFPowerSeriesOnBall.bound_zero_of_eq_zero`

English:
theorem HasFiniteFPowerSeriesOnBall.bound_zero_of_eq_zero
  statement: (hf : forall y in Metric.eball x r, f y = 0)
  proof: by
  refine ⟨⟨?_, r_pos, ?_⟩, fun n _ => hp n⟩
  · rw [p.radius_eq_top_of_forall_image_add_eq_zero 0 (fun n => by rw [add_zero]; exact hp n)]
    exact le_top
  · intro y hy
    rw [hf (x + y)]
    · convert! hasSum_zero
      rw [hp]; rw [zero_apply]
    · rwa [Metric.mem_eball, edist_eq_enorm_sub, add_comm, add_sub_cancel_right,
        ← edist_zero_right, ← Metric.mem_eball]

中文:
定理 有FiniteFPowerSeriesOnBall.bound_zero_of_eq_zero
  结论: (hf : 对任意 y in Metric.eball x r, f y = 0)
  证明: by
  refine ⟨⟨?_, r_pos, ?_⟩, fun n _ => hp n⟩
  · rw [p.radius_eq_top_of_forall_image_add_eq_zero 0 (fun n => by rw [add_zero]; exact hp n)]
    exact le_top
  · intro y hy
    rw [hf (x + y)]
    · convert! hasSum_zero
      rw [hp]; rw [zero_apply]
    · rwa [Metric.mem_eball, edist_eq_enorm_sub, add_comm, add_sub_cancel_right,
        ← edist_zero_right, ← Metric.mem_eball]

Depends on / 依赖: Metric, Metric.mem_eball, add_comm, add_sub_cancel_right, add_zero, convert, edist_eq_enorm_sub, edist_zero_right, hasSum_zero, le_top, mem_eball, p.radius_eq_top_of_forall_image_add_eq_zero, r_pos, radius_eq_top_of_forall_image_add_eq_zero, zero_apply
-/
theorem HasFiniteFPowerSeriesOnBall.bound_zero_of_eq_zero (hf : forall y in Metric.eball x r, f y = 0)
    (r_pos : 0 < r) (hp : forall n, p n = 0) : HasFiniteFPowerSeriesOnBall f p x 0 r := by
  refine ⟨⟨?_, r_pos, ?_⟩, fun n _ => hp n⟩
  · rw [p.radius_eq_top_of_forall_image_add_eq_zero 0 (fun n => by rw [add_zero]; exact hp n)]
    exact le_top
  · intro y hy
    rw [hf (x + y)]
    · convert! hasSum_zero
      rw [hp]; rw [zero_apply]
    · rwa [Metric.mem_eball, edist_eq_enorm_sub, add_comm, add_sub_cancel_right,
        ← edist_zero_right, ← Metric.mem_eball]

/--
theorem `HasFiniteFPowerSeriesAt.eventually_zero_of_bound_zero` / 定理 `HasFiniteFPowerSeriesAt.eventually_zero_of_bound_zero`

English:
theorem HasFiniteFPowerSeriesAt.eventually_zero_of_bound_zero
  proof: Filter.eventuallyEq_iff_exists_mem.mpr (let ⟨r, hf⟩ := hf; ⟨Metric.eball x r,
    Metric.eball_mem_nhds x hf.r_pos, fun y hy => hf.eq_zero_of_bound_zero y hy⟩)

中文:
定理 HasFiniteFPowerSeriesAt.eventually_zero_of_bound_zero
  证明: Filter.eventuallyEq_iff_exists_mem.mpr (let ⟨r, hf⟩ := hf; ⟨Metric.eball x r,
    Metric.eball_mem_nhds x hf.r_pos, fun y hy => hf.eq_zero_of_bound_zero y hy⟩)

Depends on / 依赖: Filter, Filter.eventuallyEq_iff_exists_mem.mpr, Metric, Metric.eball, Metric.eball_mem_nhds, eball_mem_nhds, eq_zero_of_bound_zero, eventuallyEq_iff_exists_mem, hf.eq_zero_of_bound_zero, hf.r_pos, r_pos
-/
theorem HasFiniteFPowerSeriesAt.eventually_zero_of_bound_zero
    (hf : HasFiniteFPowerSeriesAt f pf x 0) : f =ᶠ[𝓝 x] 0 :=
  Filter.eventuallyEq_iff_exists_mem.mpr (let ⟨r, hf⟩ := hf; ⟨Metric.eball x r,
    Metric.eball_mem_nhds x hf.r_pos, fun y hy => hf.eq_zero_of_bound_zero y hy⟩)

/--
theorem `HasFiniteFPowerSeriesOnBall.eq_const_of_bound_one` / 定理 `HasFiniteFPowerSeriesOnBall.eq_const_of_bound_one`

English:
theorem HasFiniteFPowerSeriesOnBall.eq_const_of_bound_one
  proof: by
  intro y hy
  rw [hf.eq_partialSum' y hy 1 le_rfl]; rw [hf.eq_partialSum' x
    (by rw [Metric.mem_eball]; rw [edist_self]; exact hf.r_pos) 1 le_rfl]
  simp only [FormalMultilinearSeries.partialSum, Finset.range_one, Finset.sum_singleton]
  congr
  apply funext
  simp only [IsEmpty.forall_iff]

中文:
定理 有FiniteFPowerSeriesOnBall.eq_const_of_bound_one
  证明: by
  intro y hy
  rw [hf.eq_partialSum' y hy 1 le_rfl]; rw [hf.eq_partialSum' x
    (by rw [Metric.mem_eball]; rw [edist_self]; exact hf.r_pos) 1 le_rfl]
  simp only [FormalMultilinearSeries.partialSum, Finset.range_one, Finset.sum_singleton]
  congr
  apply funext
  simp only [IsEmpty.forall_iff]

Depends on / 依赖: Finset, Finset.range_one, Finset.sum_singleton, FormalMultilinearSeries, FormalMultilinearSeries.partialSum, IsEmpty, IsEmpty.forall_iff, Metric, Metric.mem_eball, edist_self, eq_partialSum, forall_iff, hf.eq_partialSum, hf.r_pos, le_rfl, mem_eball, partialSum, r_pos, range_one, sum_singleton
-/
theorem HasFiniteFPowerSeriesOnBall.eq_const_of_bound_one
    (hf : HasFiniteFPowerSeriesOnBall f pf x 1 r) : forall y in Metric.eball x r, f y = f x := by
  intro y hy
  rw [hf.eq_partialSum' y hy 1 le_rfl]; rw [hf.eq_partialSum' x
    (by rw [Metric.mem_eball]; rw [edist_self]; exact hf.r_pos) 1 le_rfl]
  simp only [FormalMultilinearSeries.partialSum, Finset.range_one, Finset.sum_singleton]
  congr
  apply funext
  simp only [IsEmpty.forall_iff]

/--
theorem `HasFiniteFPowerSeriesAt.eventually_const_of_bound_one` / 定理 `HasFiniteFPowerSeriesAt.eventually_const_of_bound_one`

English:
theorem HasFiniteFPowerSeriesAt.eventually_const_of_bound_one
  proof: Filter.eventuallyEq_iff_exists_mem.mpr (let ⟨r, hf⟩ := hf; ⟨Metric.eball x r,
    Metric.eball_mem_nhds x hf.r_pos, fun y hy => hf.eq_const_of_bound_one y hy⟩)

中文:
定理 HasFiniteFPowerSeriesAt.eventually_const_of_bound_one
  证明: Filter.eventuallyEq_iff_exists_mem.mpr (let ⟨r, hf⟩ := hf; ⟨Metric.eball x r,
    Metric.eball_mem_nhds x hf.r_pos, fun y hy => hf.eq_const_of_bound_one y hy⟩)

Depends on / 依赖: Filter, Filter.eventuallyEq_iff_exists_mem.mpr, Metric, Metric.eball, Metric.eball_mem_nhds, eball_mem_nhds, eq_const_of_bound_one, eventuallyEq_iff_exists_mem, hf.eq_const_of_bound_one, hf.r_pos, r_pos
-/
theorem HasFiniteFPowerSeriesAt.eventually_const_of_bound_one
    (hf : HasFiniteFPowerSeriesAt f pf x 1) : f =ᶠ[𝓝 x] (fun _ => f x) :=
  Filter.eventuallyEq_iff_exists_mem.mpr (let ⟨r, hf⟩ := hf; ⟨Metric.eball x r,
    Metric.eball_mem_nhds x hf.r_pos, fun y hy => hf.eq_const_of_bound_one y hy⟩)

/--
theorem `HasFiniteFPowerSeriesOnBall.continuousOn` / 定理 `HasFiniteFPowerSeriesOnBall.continuousOn`

English:
theorem HasFiniteFPowerSeriesOnBall.continuousOn
  proof: hf.1.continuousOn

中文:
定理 有FiniteFPowerSeriesOnBall.continuousOn
  证明: hf.1.continuousOn
-/
protected theorem HasFiniteFPowerSeriesOnBall.continuousOn
    (hf : HasFiniteFPowerSeriesOnBall f p x n r) :
    ContinuousOn f (Metric.eball x r) := hf.1.continuousOn

/--
theorem `HasFiniteFPowerSeriesAt.continuousAt` / 定理 `HasFiniteFPowerSeriesAt.continuousAt`

English:
theorem HasFiniteFPowerSeriesAt.continuousAt
  given: (hf : HasFiniteFPowerSeriesAt f p x n)
  proof: hf.hasFPowerSeriesAt.continuousAt

中文:
定理 HasFiniteFPowerSeriesAt.continuousAt
  条件: (hf : HasFiniteFPowerSeriesAt f p x n)
  证明: hf.hasFPowerSeriesAt.continuousAt
-/
protected theorem HasFiniteFPowerSeriesAt.continuousAt (hf : HasFiniteFPowerSeriesAt f p x n) :
    ContinuousAt f x := hf.hasFPowerSeriesAt.continuousAt

/--
theorem `CPolynomialAt.continuousAt` / 定理 `CPolynomialAt.continuousAt`

English:
theorem CPolynomialAt.continuousAt
  given: (hf : CPolynomialAt 𝕜 f x)
  statement: ContinuousAt f x
  proof: hf.analyticAt.continuousAt

中文:
定理 CPolynomialAt.continuousAt
  条件: (hf : CPolynomialAt 𝕜 f x)
  结论: ContinuousAt f x
  证明: hf.analyticAt.continuousAt
-/
protected theorem CPolynomialAt.continuousAt (hf : CPolynomialAt 𝕜 f x) : ContinuousAt f x :=
  hf.analyticAt.continuousAt

/--
theorem `CPolynomialOn.continuousOn` / 定理 `CPolynomialOn.continuousOn`

English:
theorem CPolynomialOn.continuousOn
  given: {s : Set E} (hf : CPolynomialOn 𝕜 f s)
  proof: hf.analyticOnNhd.continuousOn

中文:
定理 CPolynomialOn.continuousOn
  条件: {s : 集合 E} (hf : CPolynomialOn 𝕜 f s)
  证明: hf.analyticOnNhd.continuousOn
-/
protected theorem CPolynomialOn.continuousOn {s : Set E} (hf : CPolynomialOn 𝕜 f s) :
    ContinuousOn f s :=
  hf.analyticOnNhd.continuousOn

/--
theorem `CPolynomialOn.continuous` / 定理 `CPolynomialOn.continuous`

English:
theorem CPolynomialOn.continuous
  given: {f : E -> F} (fa : CPolynomialOn 𝕜 f univ)
  statement: Continuous f
  proof: by
  rw [← continuousOn_univ]; exact fa.continuousOn

中文:
定理 CPolynomialOn.continuous
  条件: {f : E -> F} (fa : CPolynomialOn 𝕜 f univ)
  结论: 连续 f
  证明: by
  rw [← continuousOn_univ]; exact fa.continuousOn

Depends on / 依赖: continuousOn, continuousOn_univ, fa.continuousOn
-/
theorem CPolynomialOn.continuous {f : E -> F} (fa : CPolynomialOn 𝕜 f univ) : Continuous f := by
  rw [← continuousOn_univ]; exact fa.continuousOn

/--
theorem `FormalMultilinearSeries.sum_of_finite` / 定理 `FormalMultilinearSeries.sum_of_finite`

English:
theorem FormalMultilinearSeries.sum_of_finite
  statement: (p : FormalMultilinearSeries 𝕜 E F)
  proof: tsum_eq_sum fun m hm => by rw [Finset.mem_range, not_lt] at hm; rw [hn m hm]; rfl

中文:
定理 FormalMultilinearSeries.sum_of_finite
  结论: (p : FormalMultilinearSeries 𝕜 E F)
  证明: tsum_eq_sum fun m hm => by rw [Finset.mem_range, not_lt] at hm; rw [hn m hm]; rfl
-/
protected theorem FormalMultilinearSeries.sum_of_finite (p : FormalMultilinearSeries 𝕜 E F)
    {n : Nat} (hn : forall m, n <= m -> p m = 0) (x : E) :
    p.sum x = p.partialSum n x :=
  tsum_eq_sum fun m hm => by rw [Finset.mem_range, not_lt] at hm; rw [hn m hm]; rfl

/--
theorem `FormalMultilinearSeries.hasSum_of_finite` / 定理 `FormalMultilinearSeries.hasSum_of_finite`

English:
theorem FormalMultilinearSeries.hasSum_of_finite
  statement: (p : FormalMultilinearSeries 𝕜 E F)
  proof: summable_of_ne_finset_zero (s := .range n)
    (fun m hm => by rw [Finset.mem_range, not_lt] at hm; rw [hn m hm]; rfl)
.hasSum

中文:
定理 FormalMultilinearSeries.hasSum_of_finite
  结论: (p : FormalMultilinearSeries 𝕜 E F)
  证明: summable_of_ne_finset_zero (s := .range n)
    (fun m hm => by rw [Finset.mem_range, not_lt] at hm; rw [hn m hm]; rfl)
.hasSum
-/
protected theorem FormalMultilinearSeries.hasSum_of_finite (p : FormalMultilinearSeries 𝕜 E F)
    {n : Nat} (hn : forall m, n <= m -> p m = 0) (x : E) :
    HasSum (fun n : Nat => p n fun _ => x) (p.sum x) :=
  summable_of_ne_finset_zero (s := .range n)
    (fun m hm => by rw [Finset.mem_range, not_lt] at hm; rw [hn m hm]; rfl)
.hasSum

/--
theorem `FormalMultilinearSeries.hasFiniteFPowerSeriesOnBall_of_finite` / 定理 `FormalMultilinearSeries.hasFiniteFPowerSeriesOnBall_of_finite`

English:
theorem FormalMultilinearSeries.hasFiniteFPowerSeriesOnBall_of_finite
  proof: by rw [radius_eq_top_of_forall_image_add_eq_zero p n fun _ => hn _ (Nat.le_add_left _ _)]
  r_pos := zero_lt_top
  finite := hn
  hasSum {y} _ := by rw [zero_add]; exact p.hasSum_of_finite hn y

中文:
定理 FormalMultilinearSeries.hasFiniteFPowerSeriesOnBall_of_finite
  证明: by rw [radius_eq_top_of_forall_image_add_eq_zero p n fun _ => hn _ (Nat.le_add_left _ _)]
  r_pos := zero_lt_top
  finite := hn
  hasSum {y} _ := by rw [zero_add]; exact p.hasSum_of_finite hn y
-/
protected theorem FormalMultilinearSeries.hasFiniteFPowerSeriesOnBall_of_finite
    (p : FormalMultilinearSeries 𝕜 E F) {n : Nat} (hn : forall m, n <= m -> p m = 0) :
    HasFiniteFPowerSeriesOnBall p.sum p 0 n ⊤ where
  r_le := by rw [radius_eq_top_of_forall_image_add_eq_zero p n fun _ => hn _ (Nat.le_add_left _ _)]
  r_pos := zero_lt_top
  finite := hn
  hasSum {y} _ := by rw [zero_add]; exact p.hasSum_of_finite hn y

/--
theorem `HasFiniteFPowerSeriesOnBall.sum` / 定理 `HasFiniteFPowerSeriesOnBall.sum`

English:
theorem HasFiniteFPowerSeriesOnBall.sum
  statement: (h : HasFiniteFPowerSeriesOnBall f p x n r) {y : E}
  proof: (h.hasSum hy).tsum_eq.symm

中文:
定理 有FiniteFPowerSeriesOnBall.求和
  结论: (h : 有FiniteFPowerSeriesOnBall f p x n r) {y : E}
  证明: (h.hasSum hy).tsum_eq.symm

Depends on / 依赖: h.hasSum, hasSum, tsum_eq, tsum_eq.symm
-/
theorem HasFiniteFPowerSeriesOnBall.sum (h : HasFiniteFPowerSeriesOnBall f p x n r) {y : E}
    (hy : y in Metric.eball (0 : E) r) : f (x + y) = p.sum y :=
  (h.hasSum hy).tsum_eq.symm

/--
theorem `FormalMultilinearSeries.continuousOn_of_finite` / 定理 `FormalMultilinearSeries.continuousOn_of_finite`

English:
theorem FormalMultilinearSeries.continuousOn_of_finite
  proof: by
  rw [← continuousOn_univ]; rw [← Metric.eball_top]
  exact (p.hasFiniteFPowerSeriesOnBall_of_finite hn).continuousOn

中文:
定理 FormalMultilinearSeries.continuousOn_of_finite
  证明: by
  rw [← continuousOn_univ]; rw [← Metric.eball_top]
  exact (p.hasFiniteFPowerSeriesOnBall_of_finite hn).continuousOn
-/
protected theorem FormalMultilinearSeries.continuousOn_of_finite
    (p : FormalMultilinearSeries 𝕜 E F) {n : Nat} (hn : forall m, n <= m -> p m = 0) :
    Continuous p.sum := by
  rw [← continuousOn_univ]; rw [← Metric.eball_top]
  exact (p.hasFiniteFPowerSeriesOnBall_of_finite hn).continuousOn

end FiniteFPowerSeries

namespace FormalMultilinearSeries

section

/-! We study what happens when we change the origin of a finite formal multilinear series `p`. The
main point is that the new series `p.changeOrigin x` is still finite, with the same bound. -/

/--
lemma `changeOriginSeriesTerm_bound` / 引理 `changeOriginSeriesTerm_bound`

English:
lemma changeOriginSeriesTerm_bound
  statement: (p : FormalMultilinearSeries 𝕜 E F) {n : Nat}
  proof: by
  rw [changeOriginSeriesTerm]; rw [hn _ hkl]; rw [map_zero]

中文:
引理 changeOriginSeriesTerm_bound
  结论: (p : FormalMultilinearSeries 𝕜 E F) {n : 自然数}
  证明: by
  rw [changeOriginSeriesTerm]; rw [hn _ hkl]; rw [map_zero]

Depends on / 依赖: changeOriginSeriesTerm, map_zero
-/
lemma changeOriginSeriesTerm_bound (p : FormalMultilinearSeries 𝕜 E F) {n : Nat}
    (hn : forall (m : Nat), n <= m -> p m = 0) (k l : Nat) {s : Finset (Fin (k + l))}
    (hs : s.card = l) (hkl : n <= k + l) :
    p.changeOriginSeriesTerm k l s hs = 0 := by
  rw [changeOriginSeriesTerm]; rw [hn _ hkl]; rw [map_zero]

/--
lemma `changeOriginSeries_finite_of_finite` / 引理 `changeOriginSeries_finite_of_finite`

English:
lemma changeOriginSeries_finite_of_finite
  statement: (p : FormalMultilinearSeries 𝕜 E F) {n : Nat}
  proof: by
  intro m hm
  rw [changeOriginSeries]
  exact Finset.sum_eq_zero (fun _ _ => p.changeOriginSeriesTerm_bound hn _ _ _ hm)

中文:
引理 changeOriginSeries_finite_of_finite
  结论: (p : FormalMultilinearSeries 𝕜 E F) {n : 自然数}
  证明: by
  intro m hm
  rw [changeOriginSeries]
  exact Finset.sum_eq_zero (fun _ _ => p.changeOriginSeriesTerm_bound hn _ _ _ hm)

Depends on / 依赖: Finset, Finset.sum_eq_zero, changeOriginSeries, changeOriginSeriesTerm_bound, p.changeOriginSeriesTerm_bound, sum_eq_zero
-/
lemma changeOriginSeries_finite_of_finite (p : FormalMultilinearSeries 𝕜 E F) {n : Nat}
    (hn : forall (m : Nat), n <= m -> p m = 0) (k : Nat) : forall {m : Nat}, n <= k + m ->
    p.changeOriginSeries k m = 0 := by
  intro m hm
  rw [changeOriginSeries]
  exact Finset.sum_eq_zero (fun _ _ => p.changeOriginSeriesTerm_bound hn _ _ _ hm)

/--
lemma `changeOriginSeries_sum_eq_partialSum_of_finite` / 引理 `changeOriginSeries_sum_eq_partialSum_of_finite`

English:
lemma changeOriginSeries_sum_eq_partialSum_of_finite
  statement: (p : FormalMultilinearSeries 𝕜 E F) {n : Nat}
  proof: by
  ext x
  rw [partialSum]; rw [FormalMultilinearSeries.sum]; rw [tsum_eq_sum (f := fun m => p.changeOriginSeries k m (fun _ => x)) (s := Finset.range (n - k))]
  intro m hm
  rw [Finset.mem_range]; rw [not_lt] at hm
  rw [p.changeOriginSeries_finite_of_finite hn k (by rw [add_comm]; exact Nat.le_add_of_sub_le hm),
    _root_.zero_apply]

中文:
引理 changeOriginSeries_sum_eq_partialSum_of_finite
  结论: (p : FormalMultilinearSeries 𝕜 E F) {n : 自然数}
  证明: by
  ext x
  rw [partialSum]; rw [FormalMultilinearSeries.sum]; rw [tsum_eq_sum (f := fun m => p.changeOriginSeries k m (fun _ => x)) (s := Finset.range (n - k))]
  intro m hm
  rw [Finset.mem_range]; rw [not_lt] at hm
  rw [p.changeOriginSeries_finite_of_finite hn k (by rw [add_comm]; exact Nat.le_add_of_sub_le hm),
    _root_.zero_apply]

Depends on / 依赖: Finset, Finset.mem_range, Finset.range, FormalMultilinearSeries, FormalMultilinearSeries.sum, Nat.le_add_of_sub_le, _root_, _root_.zero_apply, add_comm, changeOriginSeries, changeOriginSeries_finite_of_finite, le_add_of_sub_le, mem_range, not_lt, p.changeOriginSeries, p.changeOriginSeries_finite_of_finite, partialSum, tsum_eq_sum, zero_apply
-/
lemma changeOriginSeries_sum_eq_partialSum_of_finite (p : FormalMultilinearSeries 𝕜 E F) {n : Nat}
    (hn : forall (m : Nat), n <= m -> p m = 0) (k : Nat) :
    (p.changeOriginSeries k).sum = (p.changeOriginSeries k).partialSum (n - k) := by
  ext x
  rw [partialSum]; rw [FormalMultilinearSeries.sum]; rw [tsum_eq_sum (f := fun m => p.changeOriginSeries k m (fun _ => x)) (s := Finset.range (n - k))]
  intro m hm
  rw [Finset.mem_range]; rw [not_lt] at hm
  rw [p.changeOriginSeries_finite_of_finite hn k (by rw [add_comm]; exact Nat.le_add_of_sub_le hm),
    _root_.zero_apply]

/--
lemma `changeOrigin_finite_of_finite` / 引理 `changeOrigin_finite_of_finite`

English:
lemma changeOrigin_finite_of_finite
  statement: (p : FormalMultilinearSeries 𝕜 E F) {n : Nat}
  proof: by
  rw [changeOrigin]; rw [p.changeOriginSeries_sum_eq_partialSum_of_finite hn]
  apply Finset.sum_eq_zero
  intro m hm
  rw [Finset.mem_range] at hm
  rw [p.changeOriginSeries_finite_of_finite hn k (le_add_of_le_left hk)]; rw [_root_.zero_apply]

中文:
引理 changeOrigin_finite_of_finite
  结论: (p : FormalMultilinearSeries 𝕜 E F) {n : 自然数}
  证明: by
  rw [changeOrigin]; rw [p.changeOriginSeries_sum_eq_partialSum_of_finite hn]
  apply Finset.sum_eq_zero
  intro m hm
  rw [Finset.mem_range] at hm
  rw [p.changeOriginSeries_finite_of_finite hn k (le_add_of_le_left hk)]; rw [_root_.zero_apply]

Depends on / 依赖: Finset, Finset.mem_range, Finset.sum_eq_zero, _root_, _root_.zero_apply, changeOrigin, changeOriginSeries_finite_of_finite, changeOriginSeries_sum_eq_partialSum_of_finite, le_add_of_le_left, mem_range, p.changeOriginSeries_finite_of_finite, p.changeOriginSeries_sum_eq_partialSum_of_finite, sum_eq_zero, zero_apply
-/
lemma changeOrigin_finite_of_finite (p : FormalMultilinearSeries 𝕜 E F) {n : Nat}
    (hn : forall (m : Nat), n <= m -> p m = 0) {k : Nat} (hk : n <= k) :
    p.changeOrigin x k = 0 := by
  rw [changeOrigin]; rw [p.changeOriginSeries_sum_eq_partialSum_of_finite hn]
  apply Finset.sum_eq_zero
  intro m hm
  rw [Finset.mem_range] at hm
  rw [p.changeOriginSeries_finite_of_finite hn k (le_add_of_le_left hk)]; rw [_root_.zero_apply]

/--
theorem `hasFiniteFPowerSeriesOnBall_changeOrigin` / 定理 `hasFiniteFPowerSeriesOnBall_changeOrigin`

English:
theorem hasFiniteFPowerSeriesOnBall_changeOrigin
  statement: (p : FormalMultilinearSeries 𝕜 E F) {n : Nat}
  proof: (p.changeOriginSeries k).hasFiniteFPowerSeriesOnBall_of_finite
fun _ hm => p.changeOriginSeries_finite_of_finite hn k by grw [hm, add_comm]

中文:
定理 hasFiniteFPowerSeriesOnBall_changeOrigin
  结论: (p : FormalMultilinearSeries 𝕜 E F) {n : 自然数}
  证明: (p.changeOriginSeries k).hasFiniteFPowerSeriesOnBall_of_finite
fun _ hm => p.changeOriginSeries_finite_of_finite hn k by grw [hm, add_comm]

Depends on / 依赖: add_comm, changeOriginSeries, changeOriginSeries_finite_of_finite, hasFiniteFPowerSeriesOnBall_of_finite, p.changeOriginSeries, p.changeOriginSeries_finite_of_finite
-/
theorem hasFiniteFPowerSeriesOnBall_changeOrigin (p : FormalMultilinearSeries 𝕜 E F) {n : Nat}
    (k : Nat) (hn : forall (m : Nat), n + k <= m -> p m = 0) :
    HasFiniteFPowerSeriesOnBall (p.changeOrigin · k) (p.changeOriginSeries k) 0 n ⊤ :=
  (p.changeOriginSeries k).hasFiniteFPowerSeriesOnBall_of_finite
fun _ hm => p.changeOriginSeries_finite_of_finite hn k by grw [hm, add_comm]

/--
theorem `changeOrigin_eval_of_finite` / 定理 `changeOrigin_eval_of_finite`

English:
theorem changeOrigin_eval_of_finite
  statement: (p : FormalMultilinearSeries 𝕜 E F) {n : Nat}
  proof: by
  let f (s : Σ k l : Nat, { s : Finset (Fin (k + l)) // s.card = l }) : F :=
    p.changeOriginSeriesTerm s.1 s.2.1 s.2.2 s.2.2.2 (fun _ => x) fun _ => y
  have finsupp : f.support.Finite := by
    apply Set.Finite.subset (s := changeOriginIndexEquiv ⁻¹' Sigma.fst ⁻¹' {m | m < n})
    · apply Set.Finite.preimage (Equiv.injective _).injOn
      simp_rw [← {m | m < n}.iUnion_of_singleton_coe, preimage_iUnion, ← range_sigmaMk]
      exact finite_iUnion fun _ => finite_range _
    · refine fun s => Not.imp_symm fun hs => ?_
      simp only [preimage_ofPred_eq, changeOriginIndexEquiv_apply_fst, mem_ofPred, not_lt] at hs
      dsimp only [f]
      rw [changeOriginSeriesTerm_bound p hn _ _ _ hs]; rw [_root_.zero_apply]; rw [_root_.zero_apply]
  have hfkl k l : HasSum (f ⟨k, l, ·⟩) (changeOriginSeries p k l (fun _ => x) fun _ => y) := by
    simp_rw [changeOriginSeries, sum_apply]; apply hasSum_fintype
  have hfk k : HasSum (f ⟨k, ·⟩) (changeOrigin p x k fun _ => y) := by
    have (m) (hm : m ∉ Finset.range n) : changeOriginSeries p k m (fun _ => x) = 0 := by
      rw [Finset.mem_range]; rw [not_lt] at hm
      rw [changeOriginSeries_finite_of_finite _ hn _ (le_add_of_le_right hm)]; rw [_root_.zero_apply]
    rw [changeOrigin]; rw [FormalMultilinearSeries.sum]; rw [ContinuousMultilinearMap.tsum_eval (summable_of_ne_finset_zero this)]
    refine (summable_of_ne_finset_zero (s := Finset.range n) fun m hm => ?_).hasSum.sigma_of_hasSum
      (hfkl k) (summable_of_hasFiniteSupport <| finsupp.preimage sigma_mk_injective.injOn)
    rw [this m hm]; rw [_root_.zero_apply]
  have hf : HasSum f ((p.changeOrigin x).sum y) :=
    ((p.changeOrigin x).hasSum_of_finite (fun _ => changeOrigin_finite_of_finite p hn) _)
.sigma_of_hasSum hfk (summable_of_hasFiniteSupport finsupp)
  refine hf.unique (changeOriginIndexEquiv.symm.hasSum_iff.1 ?_)
  refine (p.hasSum_of_finite hn (x + y)).sigma_of_hasSum (fun n => ?_)
    (changeOriginIndexEquiv.symm.summable_iff.2 hf.summable)
  rw [← Pi.add_def]; rw [(p n).map_add_univ (fun _ => x) fun _ => y]
  simp_rw [← changeOriginSeriesTerm_changeOriginIndexEquiv_symm]
  exact hasSum_fintype fun c => f (changeOriginIndexEquiv.symm ⟨n, c⟩)

中文:
定理 changeOrigin_eval_of_finite
  结论: (p : FormalMultilinearSeries 𝕜 E F) {n : 自然数}
  证明: by
  let f (s : Σ k l : Nat, { s : Finset (Fin (k + l)) // s.card = l }) : F :=
    p.changeOriginSeriesTerm s.1 s.2.1 s.2.2 s.2.2.2 (fun _ => x) fun _ => y
  have finsupp : f.support.Finite := by
    apply Set.Finite.subset (s := changeOriginIndexEquiv ⁻¹' Sigma.fst ⁻¹' {m | m < n})
    · apply Set.Finite.preimage (Equiv.injective _).injOn
      simp_rw [← {m | m < n}.iUnion_of_singleton_coe, preimage_iUnion, ← range_sigmaMk]
      exact finite_iUnion fun _ => finite_range _
    · refine fun s => Not.imp_symm fun hs => ?_
      simp only [preimage_ofPred_eq, changeOriginIndexEquiv_apply_fst, mem_ofPred, not_lt] at hs
      dsimp only [f]
      rw [changeOriginSeriesTerm_bound p hn _ _ _ hs]; rw [_root_.zero_apply]; rw [_root_.zero_apply]
  have hfkl k l : HasSum (f ⟨k, l, ·⟩) (changeOriginSeries p k l (fun _ => x) fun _ => y) := by
    simp_rw [changeOriginSeries, sum_apply]; apply hasSum_fintype
  have hfk k : HasSum (f ⟨k, ·⟩) (changeOrigin p x k fun _ => y) := by
    have (m) (hm : m ∉ Finset.range n) : changeOriginSeries p k m (fun _ => x) = 0 := by
      rw [Finset.mem_range]; rw [not_lt] at hm
      rw [changeOriginSeries_finite_of_finite _ hn _ (le_add_of_le_right hm)]; rw [_root_.zero_apply]
    rw [changeOrigin]; rw [FormalMultilinearSeries.sum]; rw [ContinuousMultilinearMap.tsum_eval (summable_of_ne_finset_zero this)]
    refine (summable_of_ne_finset_zero (s := Finset.range n) fun m hm => ?_).hasSum.sigma_of_hasSum
      (hfkl k) (summable_of_hasFiniteSupport <| finsupp.preimage sigma_mk_injective.injOn)
    rw [this m hm]; rw [_root_.zero_apply]
  have hf : HasSum f ((p.changeOrigin x).sum y) :=
    ((p.changeOrigin x).hasSum_of_finite (fun _ => changeOrigin_finite_of_finite p hn) _)
.sigma_of_hasSum hfk (summable_of_hasFiniteSupport finsupp)
  refine hf.unique (changeOriginIndexEquiv.symm.hasSum_iff.1 ?_)
  refine (p.hasSum_of_finite hn (x + y)).sigma_of_hasSum (fun n => ?_)
    (changeOriginIndexEquiv.symm.summable_iff.2 hf.summable)
  rw [← Pi.add_def]; rw [(p n).map_add_univ (fun _ => x) fun _ => y]
  simp_rw [← changeOriginSeriesTerm_changeOriginIndexEquiv_symm]
  exact hasSum_fintype fun c => f (changeOriginIndexEquiv.symm ⟨n, c⟩)

Depends on / 依赖: Equiv.injective, Finite, Finset, Not.imp_symm, Set.Finite.preimage, Set.Finite.subset, Sigma.fst, changeOriginIndexEquiv, changeOriginSeriesTerm, f.support.Finite, finite_iUnion, finite_range, finsupp, iUnion_of_singleton_coe, imp_symm, injective, p.changeOriginSeriesTerm, preimage, preimage_iUnion, range_sigmaMk
-/
theorem changeOrigin_eval_of_finite (p : FormalMultilinearSeries 𝕜 E F) {n : Nat}
    (hn : forall (m : Nat), n <= m -> p m = 0) (x y : E) :
    (p.changeOrigin x).sum y = p.sum (x + y) := by
  let f (s : Σ k l : Nat, { s : Finset (Fin (k + l)) // s.card = l }) : F :=
    p.changeOriginSeriesTerm s.1 s.2.1 s.2.2 s.2.2.2 (fun _ => x) fun _ => y
  have finsupp : f.support.Finite := by
    apply Set.Finite.subset (s := changeOriginIndexEquiv ⁻¹' Sigma.fst ⁻¹' {m | m < n})
    · apply Set.Finite.preimage (Equiv.injective _).injOn
      simp_rw [← {m | m < n}.iUnion_of_singleton_coe, preimage_iUnion, ← range_sigmaMk]
      exact finite_iUnion fun _ => finite_range _
    · refine fun s => Not.imp_symm fun hs => ?_
      simp only [preimage_ofPred_eq, changeOriginIndexEquiv_apply_fst, mem_ofPred, not_lt] at hs
      dsimp only [f]
      rw [changeOriginSeriesTerm_bound p hn _ _ _ hs]; rw [_root_.zero_apply]; rw [_root_.zero_apply]
  have hfkl k l : HasSum (f ⟨k, l, ·⟩) (changeOriginSeries p k l (fun _ => x) fun _ => y) := by
    simp_rw [changeOriginSeries, sum_apply]; apply hasSum_fintype
  have hfk k : HasSum (f ⟨k, ·⟩) (changeOrigin p x k fun _ => y) := by
    have (m) (hm : m ∉ Finset.range n) : changeOriginSeries p k m (fun _ => x) = 0 := by
      rw [Finset.mem_range]; rw [not_lt] at hm
      rw [changeOriginSeries_finite_of_finite _ hn _ (le_add_of_le_right hm)]; rw [_root_.zero_apply]
    rw [changeOrigin]; rw [FormalMultilinearSeries.sum]; rw [ContinuousMultilinearMap.tsum_eval (summable_of_ne_finset_zero this)]
    refine (summable_of_ne_finset_zero (s := Finset.range n) fun m hm => ?_).hasSum.sigma_of_hasSum
      (hfkl k) (summable_of_hasFiniteSupport <| finsupp.preimage sigma_mk_injective.injOn)
    rw [this m hm]; rw [_root_.zero_apply]
  have hf : HasSum f ((p.changeOrigin x).sum y) :=
    ((p.changeOrigin x).hasSum_of_finite (fun _ => changeOrigin_finite_of_finite p hn) _)
.sigma_of_hasSum hfk (summable_of_hasFiniteSupport finsupp)
  refine hf.unique (changeOriginIndexEquiv.symm.hasSum_iff.1 ?_)
  refine (p.hasSum_of_finite hn (x + y)).sigma_of_hasSum (fun n => ?_)
    (changeOriginIndexEquiv.symm.summable_iff.2 hf.summable)
  rw [← Pi.add_def]; rw [(p n).map_add_univ (fun _ => x) fun _ => y]
  simp_rw [← changeOriginSeriesTerm_changeOriginIndexEquiv_symm]
  exact hasSum_fintype fun c => f (changeOriginIndexEquiv.symm ⟨n, c⟩)

/--
theorem `cpolynomialAt_changeOrigin_of_finite` / 定理 `cpolynomialAt_changeOrigin_of_finite`

English:
theorem cpolynomialAt_changeOrigin_of_finite
  statement: (p : FormalMultilinearSeries 𝕜 E F)
  proof: (p.hasFiniteFPowerSeriesOnBall_changeOrigin k fun _ h => hn _ (le_self_add.trans h)).cpolynomialAt

中文:
定理 cpolynomialAt_changeOrigin_of_finite
  结论: (p : FormalMultilinearSeries 𝕜 E F)
  证明: (p.hasFiniteFPowerSeriesOnBall_changeOrigin k fun _ h => hn _ (le_self_add.trans h)).cpolynomialAt

Depends on / 依赖: cpolynomialAt, hasFiniteFPowerSeriesOnBall_changeOrigin, le_self_add, le_self_add.trans, p.hasFiniteFPowerSeriesOnBall_changeOrigin
-/
theorem cpolynomialAt_changeOrigin_of_finite (p : FormalMultilinearSeries 𝕜 E F)
    {n : Nat} (hn : forall (m : Nat), n <= m -> p m = 0) (k : Nat) :
    CPolynomialAt 𝕜 (p.changeOrigin · k) 0 :=
  (p.hasFiniteFPowerSeriesOnBall_changeOrigin k fun _ h => hn _ (le_self_add.trans h)).cpolynomialAt

end

end FormalMultilinearSeries

section

variable {x y : E}

/--
theorem `HasFiniteFPowerSeriesOnBall.changeOrigin` / 定理 `HasFiniteFPowerSeriesOnBall.changeOrigin`

English:
theorem HasFiniteFPowerSeriesOnBall.changeOrigin
  statement: (hf : HasFiniteFPowerSeriesOnBall f p x n r)
  proof: (tsub_le_tsub_right hf.r_le _).trans p.changeOrigin_radius
  r_pos := by simp [h]
  finite _ hm := p.changeOrigin_finite_of_finite hf.finite hm
  hasSum {z} hz := by
    have : f (x + y + z) =
        FormalMultilinearSeries.sum (FormalMultilinearSeries.changeOrigin p y) z := by
      rw [mem_eball_zero_iff]; rw [lt_tsub_iff_right]; rw [add_comm] at hz
      rw [p.changeOrigin_eval_of_finite hf.finite]; rw [add_assoc]; rw [hf.sum]
      exact mem_eball_zero_iff.2 ((enorm_add_le _ _).trans_lt hz)
    rw [this]
    apply (p.changeOrigin y).hasSum_of_finite fun _ => p.changeOrigin_finite_of_finite hf.finite

中文:
定理 有FiniteFPowerSeriesOnBall.changeOrigin
  结论: (hf : 有FiniteFPowerSeriesOnBall f p x n r)
  证明: (tsub_le_tsub_right hf.r_le _).trans p.changeOrigin_radius
  r_pos := by simp [h]
  finite _ hm := p.changeOrigin_finite_of_finite hf.finite hm
  hasSum {z} hz := by
    have : f (x + y + z) =
        FormalMultilinearSeries.sum (FormalMultilinearSeries.changeOrigin p y) z := by
      rw [mem_eball_zero_iff]; rw [lt_tsub_iff_right]; rw [add_comm] at hz
      rw [p.changeOrigin_eval_of_finite hf.finite]; rw [add_assoc]; rw [hf.sum]
      exact mem_eball_zero_iff.2 ((enorm_add_le _ _).trans_lt hz)
    rw [this]
    apply (p.changeOrigin y).hasSum_of_finite fun _ => p.changeOrigin_finite_of_finite hf.finite

Depends on / 依赖: changeOrigin_radius, hf.r_le, p.changeOrigin_radius, r_le, tsub_le_tsub_right
-/
theorem HasFiniteFPowerSeriesOnBall.changeOrigin (hf : HasFiniteFPowerSeriesOnBall f p x n r)
    (h : (‖y‖₊ : Real>=0∞) < r) :
    HasFiniteFPowerSeriesOnBall f (p.changeOrigin y) (x + y) n (r - ‖y‖₊) where
  r_le := (tsub_le_tsub_right hf.r_le _).trans p.changeOrigin_radius
  r_pos := by simp [h]
  finite _ hm := p.changeOrigin_finite_of_finite hf.finite hm
  hasSum {z} hz := by
    have : f (x + y + z) =
        FormalMultilinearSeries.sum (FormalMultilinearSeries.changeOrigin p y) z := by
      rw [mem_eball_zero_iff]; rw [lt_tsub_iff_right]; rw [add_comm] at hz
      rw [p.changeOrigin_eval_of_finite hf.finite]; rw [add_assoc]; rw [hf.sum]
      exact mem_eball_zero_iff.2 ((enorm_add_le _ _).trans_lt hz)
    rw [this]
    apply (p.changeOrigin y).hasSum_of_finite fun _ => p.changeOrigin_finite_of_finite hf.finite

/--
theorem `HasFiniteFPowerSeriesOnBall.cpolynomialAt_of_mem` / 定理 `HasFiniteFPowerSeriesOnBall.cpolynomialAt_of_mem`

English:
theorem HasFiniteFPowerSeriesOnBall.cpolynomialAt_of_mem
  proof: by
  have : (‖y - x‖₊ : Real>=0∞) < r := by simpa [edist_eq_enorm_sub] using! h
  have := hf.changeOrigin this
  rw [add_sub_cancel] at this
  exact this.cpolynomialAt

中文:
定理 有FiniteFPowerSeriesOnBall.cpolynomialAt_of_mem
  证明: by
  have : (‖y - x‖₊ : Real>=0∞) < r := by simpa [edist_eq_enorm_sub] using! h
  have := hf.changeOrigin this
  rw [add_sub_cancel] at this
  exact this.cpolynomialAt

Depends on / 依赖: add_sub_cancel, changeOrigin, cpolynomialAt, edist_eq_enorm_sub, hf.changeOrigin, this.cpolynomialAt
-/
theorem HasFiniteFPowerSeriesOnBall.cpolynomialAt_of_mem
    (hf : HasFiniteFPowerSeriesOnBall f p x n r) (h : y in Metric.eball x r) :
    CPolynomialAt 𝕜 f y := by
  have : (‖y - x‖₊ : Real>=0∞) < r := by simpa [edist_eq_enorm_sub] using! h
  have := hf.changeOrigin this
  rw [add_sub_cancel] at this
  exact this.cpolynomialAt

/--
theorem `HasFiniteFPowerSeriesOnBall.cpolynomialOn` / 定理 `HasFiniteFPowerSeriesOnBall.cpolynomialOn`

English:
theorem HasFiniteFPowerSeriesOnBall.cpolynomialOn
  given: (hf : HasFiniteFPowerSeriesOnBall f p x n r)
  proof: fun _y hy => hf.cpolynomialAt_of_mem hy

中文:
定理 有FiniteFPowerSeriesOnBall.cpolynomialOn
  条件: (hf : 有FiniteFPowerSeriesOnBall f p x n r)
  证明: fun _y hy => hf.cpolynomialAt_of_mem hy

Depends on / 依赖: cpolynomialAt_of_mem, hf.cpolynomialAt_of_mem
-/
theorem HasFiniteFPowerSeriesOnBall.cpolynomialOn (hf : HasFiniteFPowerSeriesOnBall f p x n r) :
    CPolynomialOn 𝕜 f (Metric.eball x r) :=
  fun _y hy => hf.cpolynomialAt_of_mem hy

variable (𝕜 f)

/--
theorem `isOpen_cpolynomialAt` / 定理 `isOpen_cpolynomialAt`

English:
theorem isOpen_cpolynomialAt
  statement: IsOpen { x | CPolynomialAt 𝕜 f x }
  proof: by
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨p, n, r, hr⟩
  exact mem_of_superset (Metric.eball_mem_nhds _ hr.r_pos) fun y hy => hr.cpolynomialAt_of_mem hy

中文:
定理 isOpen_cpolynomialAt
  结论: 是开集 { x | CPolynomialAt 𝕜 f x }
  证明: by
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨p, n, r, hr⟩
  exact mem_of_superset (Metric.eball_mem_nhds _ hr.r_pos) fun y hy => hr.cpolynomialAt_of_mem hy

Depends on / 依赖: Metric, Metric.eball_mem_nhds, cpolynomialAt_of_mem, eball_mem_nhds, hr.cpolynomialAt_of_mem, hr.r_pos, isOpen_iff_mem_nhds, mem_of_superset, r_pos
-/
theorem isOpen_cpolynomialAt : IsOpen { x | CPolynomialAt 𝕜 f x } := by
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨p, n, r, hr⟩
  exact mem_of_superset (Metric.eball_mem_nhds _ hr.r_pos) fun y hy => hr.cpolynomialAt_of_mem hy

variable {𝕜}

/--
theorem `CPolynomialAt.eventually_cpolynomialAt` / 定理 `CPolynomialAt.eventually_cpolynomialAt`

English:
theorem CPolynomialAt.eventually_cpolynomialAt
  given: {f : E -> F} {x : E} (h : CPolynomialAt 𝕜 f x)
  proof: (isOpen_cpolynomialAt 𝕜 f).mem_nhds h

中文:
定理 CPolynomialAt.eventually_cpolynomialAt
  条件: {f : E -> F} {x : E} (h : CPolynomialAt 𝕜 f x)
  证明: (isOpen_cpolynomialAt 𝕜 f).mem_nhds h

Depends on / 依赖: isOpen_cpolynomialAt, mem_nhds
-/
theorem CPolynomialAt.eventually_cpolynomialAt {f : E -> F} {x : E} (h : CPolynomialAt 𝕜 f x) :
    forallᶠ y in 𝓝 x, CPolynomialAt 𝕜 f y :=
  (isOpen_cpolynomialAt 𝕜 f).mem_nhds h

/--
theorem `CPolynomialAt.exists_mem_nhds_cpolynomialOn` / 定理 `CPolynomialAt.exists_mem_nhds_cpolynomialOn`

English:
theorem CPolynomialAt.exists_mem_nhds_cpolynomialOn
  given: {f : E -> F} {x : E} (h : CPolynomialAt 𝕜 f x)
  proof: h.eventually_cpolynomialAt.exists_mem

中文:
定理 CPolynomialAt.存在_mem_nhds_cpolynomialOn
  条件: {f : E -> F} {x : E} (h : CPolynomialAt 𝕜 f x)
  证明: h.eventually_cpolynomialAt.exists_mem

Depends on / 依赖: eventually_cpolynomialAt, exists_mem, h.eventually_cpolynomialAt.exists_mem
-/
theorem CPolynomialAt.exists_mem_nhds_cpolynomialOn {f : E -> F} {x : E} (h : CPolynomialAt 𝕜 f x) :
    exists s in 𝓝 x, CPolynomialOn 𝕜 f s :=
  h.eventually_cpolynomialAt.exists_mem

/--
theorem `CPolynomialAt.exists_ball_cpolynomialOn` / 定理 `CPolynomialAt.exists_ball_cpolynomialOn`

English:
theorem CPolynomialAt.exists_ball_cpolynomialOn
  given: {f : E -> F} {x : E} (h : CPolynomialAt 𝕜 f x)
  proof: Metric.isOpen_iff.mp (isOpen_cpolynomialAt _ _) _ h

中文:
定理 CPolynomialAt.存在_ball_cpolynomialOn
  条件: {f : E -> F} {x : E} (h : CPolynomialAt 𝕜 f x)
  证明: Metric.isOpen_iff.mp (isOpen_cpolynomialAt _ _) _ h

Depends on / 依赖: Metric, Metric.isOpen_iff.mp, isOpen_cpolynomialAt, isOpen_iff
-/
theorem CPolynomialAt.exists_ball_cpolynomialOn {f : E -> F} {x : E} (h : CPolynomialAt 𝕜 f x) :
    exists r : Real, 0 < r ∧ CPolynomialOn 𝕜 f (Metric.ball x r) :=
  Metric.isOpen_iff.mp (isOpen_cpolynomialAt _ _) _ h

end
