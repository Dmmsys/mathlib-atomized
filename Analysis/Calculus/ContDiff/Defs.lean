/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Analytic.Within
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

/-!
# Higher differentiability

A function is `C^1` on a domain if it is differentiable there, and its derivative is continuous.
By induction, it is `C^n` if it is `C^{n-1}` and its (n-1)-th derivative is `C^1` there or,
equivalently, if it is `C^1` and its derivative is `C^{n-1}`.
It is `C^∞` if it is `C^n` for all n.
Finally, it is `C^ω` if it is analytic (as well as all its derivative, which is automatic if the
space is complete).

We formalize these notions with predicates `ContDiffWithinAt`, `ContDiffAt`, `ContDiffOn` and
`ContDiff` saying that the function is `C^n` within a set at a point, at a point, on a set
and on the whole space respectively.

To avoid the issue of choice when choosing a derivative in sets where the derivative is not
necessarily unique, `ContDiffOn` is not defined directly in terms of the
regularity of the specific choice `iteratedFDerivWithin 𝕜 n f s` inside `s`, but in terms of the
existence of a nice sequence of derivatives, expressed with a predicate
`HasFTaylorSeriesUpToOn` defined in the file `FTaylorSeries`.

We prove basic properties of these notions.

## Main definitions and results
Let `f : E → F` be a map between normed vector spaces over a nontrivially normed field `𝕜`.

* `ContDiff 𝕜 n f`: expresses that `f` is `C^n`, i.e., it admits a Taylor series up to
  rank `n`.
* `ContDiffOn 𝕜 n f s`: expresses that `f` is `C^n` in `s`.
* `ContDiffAt 𝕜 n f x`: expresses that `f` is `C^n` around `x`.
* `ContDiffWithinAt 𝕜 n f s x`: expresses that `f` is `C^n` around `x` within the set `s`.

In sets of unique differentiability, `ContDiffOn 𝕜 n f s` can be expressed in terms of the
properties of `iteratedFDerivWithin 𝕜 m f s` for `m ≤ n`. In the whole space,
`ContDiff 𝕜 n f` can be expressed in terms of the properties of `iteratedFDeriv 𝕜 m f`
for `m ≤ n`.

## Implementation notes

The definitions in this file are designed to work on any field `𝕜`. They are sometimes slightly more
complicated than the naive definitions one would guess from the intuition over the real or complex
numbers, but they are designed to circumvent the lack of gluing properties and partitions of unity
in general. In the usual situations, they coincide with the usual definitions.

### Definition of `C^n` functions in domains

One could define `C^n` functions in a domain `s` by fixing an arbitrary choice of derivatives (this
is what we do with `iteratedFDerivWithin`) and requiring that all these derivatives up to `n` are
continuous. If the derivative is not unique, this could lead to strange behavior like two `C^n`
functions `f` and `g` on `s` whose sum is not `C^n`. A better definition is thus to say that a
function is `C^n` inside `s` if it admits a sequence of derivatives up to `n` inside `s`.

This definition still has the problem that a function which is locally `C^n` would not need to
be `C^n`, as different choices of sequences of derivatives around different points might possibly
not be glued together to give a globally defined sequence of derivatives. (Note that this issue
cannot happen over the real numbers, thanks to partitions of unity, but the behavior over a general
field is not so clear, and we want a definition for general fields). Also, there are locality
problems for the order parameter: one could image a function which, for each `n`, has a nice
sequence of derivatives up to order `n`, but they do not coincide for varying `n` and can therefore
not be glued to give rise to an infinite sequence of derivatives. This would give a function
which is `C^n` for all `n`, but not `C^∞`. We solve this issue by putting locality conditions
in space and order in our definition of `ContDiffWithinAt` and `ContDiffOn`.
The resulting definition is slightly more complicated to work with (in fact not so much), but it
gives rise to completely satisfactory theorems.

For instance, with this definition, a real function which is `C^m` (but not better) on `(-1/m, 1/m)`
for each natural `m` is by definition `C^∞` at `0`.

There is another issue with the definition of `ContDiffWithinAt 𝕜 n f s x`. We can
require the existence and good behavior of derivatives up to order `n` on a neighborhood of `x`
within `s`. However, this does not imply continuity or differentiability within `s` of the function
at `x` when `x` does not belong to `s`. Therefore, we require such existence and good behavior on
a neighborhood of `x` within `s ∪ {x}` (which appears as `insert x s` in this file).

## Notation

We use the notation `E [×n]→L[𝕜] F` for the space of continuous multilinear maps on `E^n` with
values in `F`. This is the space in which the `n`-th derivative of a function from `E` to `F` lives.

In this file, we denote `WithTop ℕ∞` with `ℕ∞ω`, `(⊤ : ℕ∞) : ℕ∞ω` with `∞` and `⊤ : ℕ∞ω` with `ω`.
To avoid ambiguities with the two tops, the theorem names use either `infty` or `omega`.
These notations are scoped in `ContDiff`.

## Tags

derivative, differentiability, higher derivative, `C^n`, multilinear, Taylor series, formal series
-/

@[expose] public section

noncomputable section

open Set Fin Filter Function
open scoped NNReal Topology ContDiff

universe u uE uF uG uX

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] {E : Type uE} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type uG}
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] {X : Type uX} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  {s s₁ t u : Set E} {f f₁ : E -> F} {g : F -> G} {x x₀ : E} {c : F} {m n : Nat∞ω}
  {p : E -> FormalMultilinearSeries 𝕜 E F}

/-! ### Smooth functions within a set around a point -/

variable (𝕜) in
/-- A function is continuously differentiable up to order `n` within a set `s` at a point `x` if
it admits continuous derivatives up to order `n` in a neighborhood of `x` in `s ∪ {x}`.
The parameter `n` belongs to `ℕ∞ω` (accessible in the `ContDiff` scope), i.e. it can be a natural
number, `∞`, or `ω`.
For `n = ∞`, we only require that this holds up to any finite order (where the neighborhood may
depend on the finite order we consider).
For `n = ω`, we require the function to be analytic within `s` at `x`. The precise definition we
give (all the derivatives should be analytic) is more involved to work around issues when the space
is not complete, but it is equivalent when the space is complete.

For instance, a real function which is `C^m` on `(-1/m, 1/m)` for each natural `m`, but not
better, is `C^∞` at `0` within `univ`.
-/
@[fun_prop]
/--
Definition of `ContDiffWithinAt` / `ContDiffWithinAt` 的定义

English:
definition ContDiffWithinAt
  signature: (n : Nat∞ω) (f : E -> F) (s : Set E) (x : E)
  body: match n with
  | ω => exists u in 𝓝[insert x s] x, exists p : E -> FormalMultilinearSeries 𝕜 E F,
      HasFTaylorSeriesUpToOn ω f p u ∧ forall i, AnalyticOn 𝕜 (fun x => p x i) u
  | (n : Nat∞) => forall m : Nat, m <= n -> exists u in 𝓝[insert x s] x,
      exists p : E -> FormalMultilinearSeries 𝕜 E F, HasFTaylorSeriesUpToOn m f p u

中文:
定义 ContDiffWithinAt
  签名: (n : 自然数∞ω) (f : E -> F) (s : 集合 E) (x : E)
  定义体: match n with
  | ω => exists u in 𝓝[insert x s] x, exists p : E -> FormalMultilinearSeries 𝕜 E F,
      HasFTaylorSeriesUpToOn ω f p u ∧ forall i, AnalyticOn 𝕜 (fun x => p x i) u
  | (n : Nat∞) => forall m : Nat, m <= n -> exists u in 𝓝[insert x s] x,
      exists p : E -> FormalMultilinearSeries 𝕜 E F, HasFTaylorSeriesUpToOn m f p u

Depends on / 依赖: AnalyticOn, FormalMultilinearSeries, HasFTaylorSeriesUpToOn, insert
-/
def ContDiffWithinAt (n : Nat∞ω) (f : E -> F) (s : Set E) (x : E) : Prop :=
  match n with
  | ω => exists u in 𝓝[insert x s] x, exists p : E -> FormalMultilinearSeries 𝕜 E F,
      HasFTaylorSeriesUpToOn ω f p u ∧ forall i, AnalyticOn 𝕜 (fun x => p x i) u
  | (n : Nat∞) => forall m : Nat, m <= n -> exists u in 𝓝[insert x s] x,
      exists p : E -> FormalMultilinearSeries 𝕜 E F, HasFTaylorSeriesUpToOn m f p u

/--
lemma `HasFTaylorSeriesUpToOn.analyticOn` / 引理 `HasFTaylorSeriesUpToOn.analyticOn`

English:
lemma HasFTaylorSeriesUpToOn.analyticOn
  proof: by
  have : AnalyticOn 𝕜 (fun x => (continuousMultilinearCurryFin0 𝕜 E F) (p x 0)) s :=
    (LinearIsometryEquiv.analyticOnNhd _ _).comp_analyticOn
      h (Set.mapsTo_univ _ _)
  exact this.congr (fun y hy => (hf.zero_eq _ hy).symm)

中文:
引理 有FTaylorSeriesUpToOn.analyticOn
  证明: by
  have : AnalyticOn 𝕜 (fun x => (continuousMultilinearCurryFin0 𝕜 E F) (p x 0)) s :=
    (LinearIsometryEquiv.analyticOnNhd _ _).comp_analyticOn
      h (Set.mapsTo_univ _ _)
  exact this.congr (fun y hy => (hf.zero_eq _ hy).symm)

Depends on / 依赖: AnalyticOn, LinearIsometryEquiv, LinearIsometryEquiv.analyticOnNhd, Set.mapsTo_univ, analyticOnNhd, comp_analyticOn, continuousMultilinearCurryFin0, hf.zero_eq, mapsTo_univ, this.congr, zero_eq
-/
lemma HasFTaylorSeriesUpToOn.analyticOn
    (hf : HasFTaylorSeriesUpToOn ω f p s) (h : AnalyticOn 𝕜 (fun x => p x 0) s) :
    AnalyticOn 𝕜 f s := by
  have : AnalyticOn 𝕜 (fun x => (continuousMultilinearCurryFin0 𝕜 E F) (p x 0)) s :=
    (LinearIsometryEquiv.analyticOnNhd _ _).comp_analyticOn
      h (Set.mapsTo_univ _ _)
  exact this.congr (fun y hy => (hf.zero_eq _ hy).symm)

/--
lemma `ContDiffWithinAt.analyticOn` / 引理 `ContDiffWithinAt.analyticOn`

English:
lemma ContDiffWithinAt.analyticOn
  given: (h : ContDiffWithinAt 𝕜 ω f s x)
  proof: by
  obtain ⟨u, hu, p, hp, h'p⟩ := h
  exact ⟨u, hu, hp.analyticOn (h'p 0)⟩

中文:
引理 ContDiffWithinAt.analyticOn
  条件: (h : ContDiffWithinAt 𝕜 ω f s x)
  证明: by
  obtain ⟨u, hu, p, hp, h'p⟩ := h
  exact ⟨u, hu, hp.analyticOn (h'p 0)⟩

Depends on / 依赖: analyticOn, hp.analyticOn
-/
lemma ContDiffWithinAt.analyticOn (h : ContDiffWithinAt 𝕜 ω f s x) :
    exists u in 𝓝[insert x s] x, AnalyticOn 𝕜 f u := by
  obtain ⟨u, hu, p, hp, h'p⟩ := h
  exact ⟨u, hu, hp.analyticOn (h'p 0)⟩

/--
lemma `ContDiffWithinAt.analyticWithinAt` / 引理 `ContDiffWithinAt.analyticWithinAt`

English:
lemma ContDiffWithinAt.analyticWithinAt
  given: (h : ContDiffWithinAt 𝕜 ω f s x)
  proof: by
  obtain ⟨u, hu, hf⟩ := h.analyticOn
  have xu : x in u := mem_of_mem_nhdsWithin (by simp) hu
  exact (hf x xu).mono_of_mem_nhdsWithin (nhdsWithin_mono _ (subset_insert _ _) hu)

中文:
引理 ContDiffWithinAt.analyticWithinAt
  条件: (h : ContDiffWithinAt 𝕜 ω f s x)
  证明: by
  obtain ⟨u, hu, hf⟩ := h.analyticOn
  have xu : x in u := mem_of_mem_nhdsWithin (by simp) hu
  exact (hf x xu).mono_of_mem_nhdsWithin (nhdsWithin_mono _ (subset_insert _ _) hu)

Depends on / 依赖: analyticOn, h.analyticOn, mem_of_mem_nhdsWithin, mono_of_mem_nhdsWithin, nhdsWithin_mono, subset_insert
-/
lemma ContDiffWithinAt.analyticWithinAt (h : ContDiffWithinAt 𝕜 ω f s x) :
    AnalyticWithinAt 𝕜 f s x := by
  obtain ⟨u, hu, hf⟩ := h.analyticOn
  have xu : x in u := mem_of_mem_nhdsWithin (by simp) hu
  exact (hf x xu).mono_of_mem_nhdsWithin (nhdsWithin_mono _ (subset_insert _ _) hu)

/--
theorem `contDiffWithinAt_omega_iff_analyticWithinAt` / 定理 `contDiffWithinAt_omega_iff_analyticWithinAt`

English:
theorem contDiffWithinAt_omega_iff_analyticWithinAt
  given: [CompleteSpace F]
  proof: by
  refine ⟨fun h => h.analyticWithinAt, fun h => ?_⟩
  obtain ⟨u, hu, p, hp, h'p⟩ := h.exists_hasFTaylorSeriesUpToOn ω
  exact ⟨u, hu, p, hp.of_le le_top, fun i => h'p i⟩

中文:
定理 contDiffWithinAt_omega_iff_analyticWithinAt
  条件: [完备空间 F]
  证明: by
  refine ⟨fun h => h.analyticWithinAt, fun h => ?_⟩
  obtain ⟨u, hu, p, hp, h'p⟩ := h.exists_hasFTaylorSeriesUpToOn ω
  exact ⟨u, hu, p, hp.of_le le_top, fun i => h'p i⟩

Depends on / 依赖: analyticWithinAt, exists_hasFTaylorSeriesUpToOn, h.analyticWithinAt, h.exists_hasFTaylorSeriesUpToOn, hp.of_le, le_top, of_le
-/
theorem contDiffWithinAt_omega_iff_analyticWithinAt [CompleteSpace F] :
    ContDiffWithinAt 𝕜 ω f s x ↔ AnalyticWithinAt 𝕜 f s x := by
  refine ⟨fun h => h.analyticWithinAt, fun h => ?_⟩
  obtain ⟨u, hu, p, hp, h'p⟩ := h.exists_hasFTaylorSeriesUpToOn ω
  exact ⟨u, hu, p, hp.of_le le_top, fun i => h'p i⟩

/--
theorem `contDiffWithinAt_nat` / 定理 `contDiffWithinAt_nat`

English:
theorem contDiffWithinAt_nat
  given: {n : Nat}
  proof: ⟨fun H => H n le_rfl, fun ⟨u, hu, p, hp⟩ _m hm => ⟨u, hu, p, hp.of_le (mod_cast hm)⟩⟩

中文:
定理 contDiffWithinAt_nat
  条件: {n : 自然数}
  证明: ⟨fun H => H n le_rfl, fun ⟨u, hu, p, hp⟩ _m hm => ⟨u, hu, p, hp.of_le (mod_cast hm)⟩⟩

Depends on / 依赖: hp.of_le, le_rfl, mod_cast, of_le
-/
theorem contDiffWithinAt_nat {n : Nat} :
    ContDiffWithinAt 𝕜 n f s x ↔ exists u in 𝓝[insert x s] x,
      exists p : E -> FormalMultilinearSeries 𝕜 E F, HasFTaylorSeriesUpToOn n f p u :=
  ⟨fun H => H n le_rfl, fun ⟨u, hu, p, hp⟩ _m hm => ⟨u, hu, p, hp.of_le (mod_cast hm)⟩⟩

/--
lemma `contDiffWithinAt_iff_of_ne_infty` / 引理 `contDiffWithinAt_iff_of_ne_infty`

English:
lemma contDiffWithinAt_iff_of_ne_infty
  given: (hn : n != ∞)
  proof: by
  match n with
  | ω => simp [ContDiffWithinAt]
  | ∞ => simp at hn
  | (n : Nat) => simp [contDiffWithinAt_nat]

@[fun_prop]

中文:
引理 contDiffWithinAt_iff_of_ne_infty
  条件: (hn : n != ∞)
  证明: by
  match n with
  | ω => simp [ContDiffWithinAt]
  | ∞ => simp at hn
  | (n : Nat) => simp [contDiffWithinAt_nat]

@[fun_prop]

Depends on / 依赖: ContDiffWithinAt, contDiffWithinAt_nat
-/
lemma contDiffWithinAt_iff_of_ne_infty (hn : n != ∞) :
    ContDiffWithinAt 𝕜 n f s x ↔ exists u in 𝓝[insert x s] x,
      exists p : E -> FormalMultilinearSeries 𝕜 E F, HasFTaylorSeriesUpToOn n f p u ∧
        (n = ω -> forall i, AnalyticOn 𝕜 (fun x => p x i) u) := by
  match n with
  | ω => simp [ContDiffWithinAt]
  | ∞ => simp at hn
  | (n : Nat) => simp [contDiffWithinAt_nat]

@[fun_prop]
/--
theorem `ContDiffWithinAt.of_le` / 定理 `ContDiffWithinAt.of_le`

English:
theorem ContDiffWithinAt.of_le
  given: (h : ContDiffWithinAt 𝕜 n f s x) (hmn : m <= n)
  proof: by
  match n with
  | ω => match m with
    | ω => exact h
    | (m : Nat∞) =>
      intro k _
      obtain ⟨u, hu, p, hp, -⟩ := h
      exact ⟨u, hu, p, hp.of_le le_top⟩
  | (n : Nat∞) => match m with
    | ω => simp at hmn
    | (m : Nat∞) => exact fun k hk => h k (le_trans hk (mod_cast hmn))

中文:
定理 ContDiffWithinAt.of_le
  条件: (h : ContDiffWithinAt 𝕜 n f s x) (hmn : m <= n)
  证明: by
  match n with
  | ω => match m with
    | ω => exact h
    | (m : Nat∞) =>
      intro k _
      obtain ⟨u, hu, p, hp, -⟩ := h
      exact ⟨u, hu, p, hp.of_le le_top⟩
  | (n : Nat∞) => match m with
    | ω => simp at hmn
    | (m : Nat∞) => exact fun k hk => h k (le_trans hk (mod_cast hmn))

Depends on / 依赖: hp.of_le, le_top, le_trans, mod_cast, of_le
-/
theorem ContDiffWithinAt.of_le (h : ContDiffWithinAt 𝕜 n f s x) (hmn : m <= n) :
    ContDiffWithinAt 𝕜 m f s x := by
  match n with
  | ω => match m with
    | ω => exact h
    | (m : Nat∞) =>
      intro k _
      obtain ⟨u, hu, p, hp, -⟩ := h
      exact ⟨u, hu, p, hp.of_le le_top⟩
  | (n : Nat∞) => match m with
    | ω => simp at hmn
    | (m : Nat∞) => exact fun k hk => h k (le_trans hk (mod_cast hmn))

/--
theorem `AnalyticWithinAt.contDiffWithinAt` / 定理 `AnalyticWithinAt.contDiffWithinAt`

English:
theorem AnalyticWithinAt.contDiffWithinAt
  given: [CompleteSpace F] (h : AnalyticWithinAt 𝕜 f s x)
  proof: (contDiffWithinAt_omega_iff_analyticWithinAt.2 h).of_le le_top

中文:
定理 AnalyticWithinAt.contDiffWithinAt
  条件: [完备空间 F] (h : AnalyticWithinAt 𝕜 f s x)
  证明: (contDiffWithinAt_omega_iff_analyticWithinAt.2 h).of_le le_top

Depends on / 依赖: contDiffWithinAt_omega_iff_analyticWithinAt, le_top, of_le
-/
theorem AnalyticWithinAt.contDiffWithinAt [CompleteSpace F] (h : AnalyticWithinAt 𝕜 f s x) :
    ContDiffWithinAt 𝕜 n f s x :=
  (contDiffWithinAt_omega_iff_analyticWithinAt.2 h).of_le le_top

/--
theorem `contDiffWithinAt_iff_forall_nat_le` / 定理 `contDiffWithinAt_iff_forall_nat_le`

English:
theorem contDiffWithinAt_iff_forall_nat_le
  given: {n : Nat∞}
  proof: ⟨fun H _ hm => H.of_le (mod_cast hm), fun H m hm => H m hm _ le_rfl⟩

中文:
定理 contDiffWithinAt_iff_对任意_nat_le
  条件: {n : 自然数∞}
  证明: ⟨fun H _ hm => H.of_le (mod_cast hm), fun H m hm => H m hm _ le_rfl⟩

Depends on / 依赖: H.of_le, le_rfl, mod_cast, of_le
-/
theorem contDiffWithinAt_iff_forall_nat_le {n : Nat∞} :
    ContDiffWithinAt 𝕜 n f s x ↔ forall m : Nat, ↑m <= n -> ContDiffWithinAt 𝕜 m f s x :=
  ⟨fun H _ hm => H.of_le (mod_cast hm), fun H m hm => H m hm _ le_rfl⟩

/--
theorem `contDiffWithinAt_infty` / 定理 `contDiffWithinAt_infty`

English:
theorem contDiffWithinAt_infty
  proof: contDiffWithinAt_iff_forall_nat_le.trans by simp only [forall_prop_of_true, le_top]

中文:
定理 contDiffWithinAt_infty
  证明: contDiffWithinAt_iff_forall_nat_le.trans by simp only [forall_prop_of_true, le_top]

Depends on / 依赖: contDiffWithinAt_iff_forall_nat_le, contDiffWithinAt_iff_forall_nat_le.trans, forall_prop_of_true, le_top
-/
theorem contDiffWithinAt_infty :
    ContDiffWithinAt 𝕜 ∞ f s x ↔ forall n : Nat, ContDiffWithinAt 𝕜 n f s x :=
contDiffWithinAt_iff_forall_nat_le.trans by simp only [forall_prop_of_true, le_top]

/--
theorem `ContDiffWithinAt.continuousWithinAt` / 定理 `ContDiffWithinAt.continuousWithinAt`

English:
theorem ContDiffWithinAt.continuousWithinAt
  given: (h : ContDiffWithinAt 𝕜 n f s x)
  proof: by
  have := h.of_le zero_le
  simp only [ContDiffWithinAt, nonpos_iff_eq_zero, Nat.cast_eq_zero, forall_eq, CharP.cast_eq_zero]
    at this
  rcases this with ⟨u, hu, p, H⟩
  rw [mem_nhdsWithin_insert] at hu
  exact (H.continuousOn.continuousWithinAt hu.1).mono_of_mem_nhdsWithin hu.2

中文:
定理 ContDiffWithinAt.continuousWithinAt
  条件: (h : ContDiffWithinAt 𝕜 n f s x)
  证明: by
  have := h.of_le zero_le
  simp only [ContDiffWithinAt, nonpos_iff_eq_zero, Nat.cast_eq_zero, forall_eq, CharP.cast_eq_zero]
    at this
  rcases this with ⟨u, hu, p, H⟩
  rw [mem_nhdsWithin_insert] at hu
  exact (H.continuousOn.continuousWithinAt hu.1).mono_of_mem_nhdsWithin hu.2

Depends on / 依赖: CharP.cast_eq_zero, ContDiffWithinAt, H.continuousOn.continuousWithinAt, Nat.cast_eq_zero, cast_eq_zero, continuousOn, continuousWithinAt, forall_eq, h.of_le, mem_nhdsWithin_insert, mono_of_mem_nhdsWithin, nonpos_iff_eq_zero, of_le, zero_le
-/
theorem ContDiffWithinAt.continuousWithinAt (h : ContDiffWithinAt 𝕜 n f s x) :
    ContinuousWithinAt f s x := by
  have := h.of_le zero_le
  simp only [ContDiffWithinAt, nonpos_iff_eq_zero, Nat.cast_eq_zero, forall_eq, CharP.cast_eq_zero]
    at this
  rcases this with ⟨u, hu, p, H⟩
  rw [mem_nhdsWithin_insert] at hu
  exact (H.continuousOn.continuousWithinAt hu.1).mono_of_mem_nhdsWithin hu.2

/--
theorem `ContDiffWithinAt.congr_of_eventuallyEq` / 定理 `ContDiffWithinAt.congr_of_eventuallyEq`

English:
theorem ContDiffWithinAt.congr_of_eventuallyEq
  statement: (h : ContDiffWithinAt 𝕜 n f s x)
  proof: by
  match n with
  | ω =>
    obtain ⟨u, hu, p, H, H'⟩ := h
    exact ⟨{x in u | f₁ x = f x}, Filter.inter_mem hu (mem_nhdsWithin_insert.2 ⟨hx, h₁⟩), p,
      (H.mono (sep_subset _ _)).congr fun _ => And.right,
      fun i => (H' i).mono (sep_subset _ _)⟩
  | (n : Nat∞) =>
    intro m hm
    let ⟨u, hu, p, H⟩ := h m hm
    exact ⟨{ x in u | f₁ x = f x }, Filter.inter_mem hu (mem_nhdsWithin_insert.2 ⟨hx, h₁⟩), p,
      (H.mono (sep_subset _ _)).congr fun _ => And.right⟩

中文:
定理 ContDiffWithinAt.congr_of_eventuallyEq
  结论: (h : ContDiffWithinAt 𝕜 n f s x)
  证明: by
  match n with
  | ω =>
    obtain ⟨u, hu, p, H, H'⟩ := h
    exact ⟨{x in u | f₁ x = f x}, Filter.inter_mem hu (mem_nhdsWithin_insert.2 ⟨hx, h₁⟩), p,
      (H.mono (sep_subset _ _)).congr fun _ => And.right,
      fun i => (H' i).mono (sep_subset _ _)⟩
  | (n : Nat∞) =>
    intro m hm
    let ⟨u, hu, p, H⟩ := h m hm
    exact ⟨{ x in u | f₁ x = f x }, Filter.inter_mem hu (mem_nhdsWithin_insert.2 ⟨hx, h₁⟩), p,
      (H.mono (sep_subset _ _)).congr fun _ => And.right⟩

Depends on / 依赖: And.right, Filter, Filter.inter_mem, H.mono, inter_mem, mem_nhdsWithin_insert, sep_subset
-/
theorem ContDiffWithinAt.congr_of_eventuallyEq (h : ContDiffWithinAt 𝕜 n f s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : ContDiffWithinAt 𝕜 n f₁ s x := by
  match n with
  | ω =>
    obtain ⟨u, hu, p, H, H'⟩ := h
    exact ⟨{x in u | f₁ x = f x}, Filter.inter_mem hu (mem_nhdsWithin_insert.2 ⟨hx, h₁⟩), p,
      (H.mono (sep_subset _ _)).congr fun _ => And.right,
      fun i => (H' i).mono (sep_subset _ _)⟩
  | (n : Nat∞) =>
    intro m hm
    let ⟨u, hu, p, H⟩ := h m hm
    exact ⟨{ x in u | f₁ x = f x }, Filter.inter_mem hu (mem_nhdsWithin_insert.2 ⟨hx, h₁⟩), p,
      (H.mono (sep_subset _ _)).congr fun _ => And.right⟩

/--
theorem `Filter.EventuallyEq.congr_contDiffWithinAt` / 定理 `Filter.EventuallyEq.congr_contDiffWithinAt`

English:
theorem Filter.EventuallyEq.congr_contDiffWithinAt
  given: (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x)
  proof: ⟨fun H => H.congr_of_eventuallyEq h₁.symm hx.symm, fun H => H.congr_of_eventuallyEq h₁ hx⟩

中文:
定理 滤子.EventuallyEq.congr_contDiffWithinAt
  条件: (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x)
  证明: ⟨fun H => H.congr_of_eventuallyEq h₁.symm hx.symm, fun H => H.congr_of_eventuallyEq h₁ hx⟩

Depends on / 依赖: H.congr_of_eventuallyEq, congr_of_eventuallyEq, hx.symm
-/
theorem Filter.EventuallyEq.congr_contDiffWithinAt (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) :
    ContDiffWithinAt 𝕜 n f₁ s x ↔ ContDiffWithinAt 𝕜 n f s x :=
  ⟨fun H => H.congr_of_eventuallyEq h₁.symm hx.symm, fun H => H.congr_of_eventuallyEq h₁ hx⟩

/--
theorem `ContDiffWithinAt.congr_of_eventuallyEq_insert` / 定理 `ContDiffWithinAt.congr_of_eventuallyEq_insert`

English:
theorem ContDiffWithinAt.congr_of_eventuallyEq_insert
  statement: (h : ContDiffWithinAt 𝕜 n f s x)
  proof: h.congr_of_eventuallyEq (nhdsWithin_mono x (subset_insert x s) h₁)
    (mem_of_mem_nhdsWithin (mem_insert x s) h₁ :)

中文:
定理 ContDiffWithinAt.congr_of_eventuallyEq_insert
  结论: (h : ContDiffWithinAt 𝕜 n f s x)
  证明: h.congr_of_eventuallyEq (nhdsWithin_mono x (subset_insert x s) h₁)
    (mem_of_mem_nhdsWithin (mem_insert x s) h₁ :)

Depends on / 依赖: congr_of_eventuallyEq, h.congr_of_eventuallyEq, mem_insert, mem_of_mem_nhdsWithin, nhdsWithin_mono, subset_insert
-/
theorem ContDiffWithinAt.congr_of_eventuallyEq_insert (h : ContDiffWithinAt 𝕜 n f s x)
    (h₁ : f₁ =ᶠ[𝓝[insert x s] x] f) : ContDiffWithinAt 𝕜 n f₁ s x :=
  h.congr_of_eventuallyEq (nhdsWithin_mono x (subset_insert x s) h₁)
    (mem_of_mem_nhdsWithin (mem_insert x s) h₁ :)

/--
theorem `Filter.EventuallyEq.congr_contDiffWithinAt_of_insert` / 定理 `Filter.EventuallyEq.congr_contDiffWithinAt_of_insert`

English:
theorem Filter.EventuallyEq.congr_contDiffWithinAt_of_insert
  given: (h₁ : f₁ =ᶠ[𝓝[insert x s] x] f)
  proof: ⟨fun H => H.congr_of_eventuallyEq_insert h₁.symm, fun H => H.congr_of_eventuallyEq_insert h₁⟩

中文:
定理 滤子.EventuallyEq.congr_contDiffWithinAt_of_insert
  条件: (h₁ : f₁ =ᶠ[𝓝[insert x s] x] f)
  证明: ⟨fun H => H.congr_of_eventuallyEq_insert h₁.symm, fun H => H.congr_of_eventuallyEq_insert h₁⟩

Depends on / 依赖: H.congr_of_eventuallyEq_insert, congr_of_eventuallyEq_insert
-/
theorem Filter.EventuallyEq.congr_contDiffWithinAt_of_insert (h₁ : f₁ =ᶠ[𝓝[insert x s] x] f) :
    ContDiffWithinAt 𝕜 n f₁ s x ↔ ContDiffWithinAt 𝕜 n f s x :=
  ⟨fun H => H.congr_of_eventuallyEq_insert h₁.symm, fun H => H.congr_of_eventuallyEq_insert h₁⟩

/--
theorem `ContDiffWithinAt.congr_of_eventuallyEq_of_mem` / 定理 `ContDiffWithinAt.congr_of_eventuallyEq_of_mem`

English:
theorem ContDiffWithinAt.congr_of_eventuallyEq_of_mem
  statement: (h : ContDiffWithinAt 𝕜 n f s x)
  proof: h.congr_of_eventuallyEq h₁ h₁.self_of_nhdsWithin hx

中文:
定理 ContDiffWithinAt.congr_of_eventuallyEq_of_mem
  结论: (h : ContDiffWithinAt 𝕜 n f s x)
  证明: h.congr_of_eventuallyEq h₁ h₁.self_of_nhdsWithin hx

Depends on / 依赖: congr_of_eventuallyEq, h.congr_of_eventuallyEq, self_of_nhdsWithin
-/
theorem ContDiffWithinAt.congr_of_eventuallyEq_of_mem (h : ContDiffWithinAt 𝕜 n f s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : x in s) : ContDiffWithinAt 𝕜 n f₁ s x :=
h.congr_of_eventuallyEq h₁ h₁.self_of_nhdsWithin hx

/--
theorem `Filter.EventuallyEq.congr_contDiffWithinAt_of_mem` / 定理 `Filter.EventuallyEq.congr_contDiffWithinAt_of_mem`

English:
theorem Filter.EventuallyEq.congr_contDiffWithinAt_of_mem
  given: (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : x in s)
  proof: ⟨fun H => H.congr_of_eventuallyEq_of_mem h₁.symm hx, fun H => H.congr_of_eventuallyEq_of_mem h₁ hx⟩

中文:
定理 滤子.EventuallyEq.congr_contDiffWithinAt_of_mem
  条件: (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : x in s)
  证明: ⟨fun H => H.congr_of_eventuallyEq_of_mem h₁.symm hx, fun H => H.congr_of_eventuallyEq_of_mem h₁ hx⟩

Depends on / 依赖: H.congr_of_eventuallyEq_of_mem, congr_of_eventuallyEq_of_mem
-/
theorem Filter.EventuallyEq.congr_contDiffWithinAt_of_mem (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : x in s) :
    ContDiffWithinAt 𝕜 n f₁ s x ↔ ContDiffWithinAt 𝕜 n f s x :=
  ⟨fun H => H.congr_of_eventuallyEq_of_mem h₁.symm hx, fun H => H.congr_of_eventuallyEq_of_mem h₁ hx⟩

/--
theorem `ContDiffWithinAt.congr` / 定理 `ContDiffWithinAt.congr`

English:
theorem ContDiffWithinAt.congr
  statement: (h : ContDiffWithinAt 𝕜 n f s x) (h₁ : forall y in s, f₁ y = f y)
  proof: h.congr_of_eventuallyEq (Filter.eventuallyEq_of_mem self_mem_nhdsWithin h₁) hx

中文:
定理 ContDiffWithinAt.congr
  结论: (h : ContDiffWithinAt 𝕜 n f s x) (h₁ : 对任意 y in s, f₁ y = f y)
  证明: h.congr_of_eventuallyEq (Filter.eventuallyEq_of_mem self_mem_nhdsWithin h₁) hx

Depends on / 依赖: Filter, Filter.eventuallyEq_of_mem, congr_of_eventuallyEq, eventuallyEq_of_mem, h.congr_of_eventuallyEq, self_mem_nhdsWithin
-/
theorem ContDiffWithinAt.congr (h : ContDiffWithinAt 𝕜 n f s x) (h₁ : forall y in s, f₁ y = f y)
    (hx : f₁ x = f x) : ContDiffWithinAt 𝕜 n f₁ s x :=
  h.congr_of_eventuallyEq (Filter.eventuallyEq_of_mem self_mem_nhdsWithin h₁) hx

/--
theorem `ContDiffWithinAt.congr'` / 定理 `ContDiffWithinAt.congr'`

English:
theorem ContDiffWithinAt.congr'
  statement: (h : ContDiffWithinAt 𝕜 n f s x) (h₁ : forall y in t, f₁ y = f y)
  proof: h.congr (fun _y hy => h₁ _ (hst hy)) (h₁ x hxt)

中文:
定理 ContDiffWithinAt.congr'
  结论: (h : ContDiffWithinAt 𝕜 n f s x) (h₁ : 对任意 y in t, f₁ y = f y)
  证明: h.congr (fun _y hy => h₁ _ (hst hy)) (h₁ x hxt)

Depends on / 依赖: h.congr
-/
theorem ContDiffWithinAt.congr' (h : ContDiffWithinAt 𝕜 n f s x) (h₁ : forall y in t, f₁ y = f y)
    (hst : s subseteq t) (hxt : x in t) :
    ContDiffWithinAt 𝕜 n f₁ s x :=
  h.congr (fun _y hy => h₁ _ (hst hy)) (h₁ x hxt)

/--
theorem `contDiffWithinAt_congr` / 定理 `contDiffWithinAt_congr`

English:
theorem contDiffWithinAt_congr
  given: (h₁ : forall y in s, f₁ y = f y) (hx : f₁ x = f x)
  proof: ⟨fun h' => h'.congr (fun x hx => (h₁ x hx).symm) hx.symm, fun h' => h'.congr h₁ hx⟩

中文:
定理 contDiffWithinAt_congr
  条件: (h₁ : 对任意 y in s, f₁ y = f y) (hx : f₁ x = f x)
  证明: ⟨fun h' => h'.congr (fun x hx => (h₁ x hx).symm) hx.symm, fun h' => h'.congr h₁ hx⟩

Depends on / 依赖: hx.symm
-/
theorem contDiffWithinAt_congr (h₁ : forall y in s, f₁ y = f y) (hx : f₁ x = f x) :
    ContDiffWithinAt 𝕜 n f₁ s x ↔ ContDiffWithinAt 𝕜 n f s x :=
  ⟨fun h' => h'.congr (fun x hx => (h₁ x hx).symm) hx.symm, fun h' => h'.congr h₁ hx⟩

/--
theorem `ContDiffWithinAt.congr_of_mem` / 定理 `ContDiffWithinAt.congr_of_mem`

English:
theorem ContDiffWithinAt.congr_of_mem
  statement: (h : ContDiffWithinAt 𝕜 n f s x) (h₁ : forall y in s, f₁ y = f y)
  proof: h.congr h₁ (h₁ _ hx)

中文:
定理 ContDiffWithinAt.congr_of_mem
  结论: (h : ContDiffWithinAt 𝕜 n f s x) (h₁ : 对任意 y in s, f₁ y = f y)
  证明: h.congr h₁ (h₁ _ hx)

Depends on / 依赖: h.congr
-/
theorem ContDiffWithinAt.congr_of_mem (h : ContDiffWithinAt 𝕜 n f s x) (h₁ : forall y in s, f₁ y = f y)
    (hx : x in s) : ContDiffWithinAt 𝕜 n f₁ s x :=
  h.congr h₁ (h₁ _ hx)

/--
theorem `contDiffWithinAt_congr_of_mem` / 定理 `contDiffWithinAt_congr_of_mem`

English:
theorem contDiffWithinAt_congr_of_mem
  given: (h₁ : forall y in s, f₁ y = f y) (hx : x in s)
  proof: contDiffWithinAt_congr h₁ (h₁ x hx)

中文:
定理 contDiffWithinAt_congr_of_mem
  条件: (h₁ : 对任意 y in s, f₁ y = f y) (hx : x in s)
  证明: contDiffWithinAt_congr h₁ (h₁ x hx)

Depends on / 依赖: contDiffWithinAt_congr
-/
theorem contDiffWithinAt_congr_of_mem (h₁ : forall y in s, f₁ y = f y) (hx : x in s) :
    ContDiffWithinAt 𝕜 n f₁ s x ↔ ContDiffWithinAt 𝕜 n f s x :=
  contDiffWithinAt_congr h₁ (h₁ x hx)

/--
theorem `ContDiffWithinAt.congr_of_insert` / 定理 `ContDiffWithinAt.congr_of_insert`

English:
theorem ContDiffWithinAt.congr_of_insert
  statement: (h : ContDiffWithinAt 𝕜 n f s x)
  proof: h.congr (fun y hy => h₁ y (mem_insert_of_mem _ hy)) (h₁ x (mem_insert _ _))

中文:
定理 ContDiffWithinAt.congr_of_insert
  结论: (h : ContDiffWithinAt 𝕜 n f s x)
  证明: h.congr (fun y hy => h₁ y (mem_insert_of_mem _ hy)) (h₁ x (mem_insert _ _))

Depends on / 依赖: h.congr, mem_insert, mem_insert_of_mem
-/
theorem ContDiffWithinAt.congr_of_insert (h : ContDiffWithinAt 𝕜 n f s x)
    (h₁ : forall y in insert x s, f₁ y = f y) : ContDiffWithinAt 𝕜 n f₁ s x :=
  h.congr (fun y hy => h₁ y (mem_insert_of_mem _ hy)) (h₁ x (mem_insert _ _))

/--
theorem `contDiffWithinAt_congr_of_insert` / 定理 `contDiffWithinAt_congr_of_insert`

English:
theorem contDiffWithinAt_congr_of_insert
  given: (h₁ : forall y in insert x s, f₁ y = f y)
  proof: contDiffWithinAt_congr (fun y hy => h₁ y (mem_insert_of_mem _ hy)) (h₁ x (mem_insert _ _))

中文:
定理 contDiffWithinAt_congr_of_insert
  条件: (h₁ : 对任意 y in insert x s, f₁ y = f y)
  证明: contDiffWithinAt_congr (fun y hy => h₁ y (mem_insert_of_mem _ hy)) (h₁ x (mem_insert _ _))

Depends on / 依赖: contDiffWithinAt_congr, mem_insert, mem_insert_of_mem
-/
theorem contDiffWithinAt_congr_of_insert (h₁ : forall y in insert x s, f₁ y = f y) :
    ContDiffWithinAt 𝕜 n f₁ s x ↔ ContDiffWithinAt 𝕜 n f s x :=
  contDiffWithinAt_congr (fun y hy => h₁ y (mem_insert_of_mem _ hy)) (h₁ x (mem_insert _ _))

/--
theorem `ContDiffWithinAt.mono_of_mem_nhdsWithin` / 定理 `ContDiffWithinAt.mono_of_mem_nhdsWithin`

English:
theorem ContDiffWithinAt.mono_of_mem_nhdsWithin
  statement: (h : ContDiffWithinAt 𝕜 n f s x) {t : Set E}
  proof: by
  match n with
  | ω =>
    obtain ⟨u, hu, p, H, H'⟩ := h
    exact ⟨u, nhdsWithin_le_of_mem (insert_mem_nhdsWithin_insert hst) hu, p, H, H'⟩
  | (n : Nat∞) =>
    intro m hm
    rcases h m hm with ⟨u, hu, p, H⟩
    exact ⟨u, nhdsWithin_le_of_mem (insert_mem_nhdsWithin_insert hst) hu, p, H⟩

中文:
定理 ContDiffWithinAt.mono_of_mem_nhdsWithin
  结论: (h : ContDiffWithinAt 𝕜 n f s x) {t : 集合 E}
  证明: by
  match n with
  | ω =>
    obtain ⟨u, hu, p, H, H'⟩ := h
    exact ⟨u, nhdsWithin_le_of_mem (insert_mem_nhdsWithin_insert hst) hu, p, H, H'⟩
  | (n : Nat∞) =>
    intro m hm
    rcases h m hm with ⟨u, hu, p, H⟩
    exact ⟨u, nhdsWithin_le_of_mem (insert_mem_nhdsWithin_insert hst) hu, p, H⟩

Depends on / 依赖: insert_mem_nhdsWithin_insert, nhdsWithin_le_of_mem
-/
theorem ContDiffWithinAt.mono_of_mem_nhdsWithin (h : ContDiffWithinAt 𝕜 n f s x) {t : Set E}
    (hst : s in 𝓝[t] x) : ContDiffWithinAt 𝕜 n f t x := by
  match n with
  | ω =>
    obtain ⟨u, hu, p, H, H'⟩ := h
    exact ⟨u, nhdsWithin_le_of_mem (insert_mem_nhdsWithin_insert hst) hu, p, H, H'⟩
  | (n : Nat∞) =>
    intro m hm
    rcases h m hm with ⟨u, hu, p, H⟩
    exact ⟨u, nhdsWithin_le_of_mem (insert_mem_nhdsWithin_insert hst) hu, p, H⟩

/--
theorem `ContDiffWithinAt.mono` / 定理 `ContDiffWithinAt.mono`

English:
theorem ContDiffWithinAt.mono
  given: (h : ContDiffWithinAt 𝕜 n f s x) {t : Set E} (hst : t subseteq s)
  proof: h.mono_of_mem_nhdsWithin Filter.mem_of_superset self_mem_nhdsWithin hst

中文:
定理 ContDiffWithinAt.mono
  条件: (h : ContDiffWithinAt 𝕜 n f s x) {t : 集合 E} (hst : t subseteq s)
  证明: h.mono_of_mem_nhdsWithin Filter.mem_of_superset self_mem_nhdsWithin hst

Depends on / 依赖: Filter, Filter.mem_of_superset, h.mono_of_mem_nhdsWithin, mem_of_superset, mono_of_mem_nhdsWithin, self_mem_nhdsWithin
-/
theorem ContDiffWithinAt.mono (h : ContDiffWithinAt 𝕜 n f s x) {t : Set E} (hst : t subseteq s) :
    ContDiffWithinAt 𝕜 n f t x :=
h.mono_of_mem_nhdsWithin Filter.mem_of_superset self_mem_nhdsWithin hst

/--
theorem `ContDiffWithinAt.congr_mono` / 定理 `ContDiffWithinAt.congr_mono`

English:
theorem ContDiffWithinAt.congr_mono
  proof: (h.mono h₁).congr h' hx

中文:
定理 ContDiffWithinAt.congr_mono
  证明: (h.mono h₁).congr h' hx

Depends on / 依赖: h.mono
-/
theorem ContDiffWithinAt.congr_mono
    (h : ContDiffWithinAt 𝕜 n f s x) (h' : EqOn f₁ f s₁) (h₁ : s₁ subseteq s) (hx : f₁ x = f x) :
    ContDiffWithinAt 𝕜 n f₁ s₁ x :=
  (h.mono h₁).congr h' hx

/--
theorem `ContDiffWithinAt.congr_set` / 定理 `ContDiffWithinAt.congr_set`

English:
theorem ContDiffWithinAt.congr_set
  statement: (h : ContDiffWithinAt 𝕜 n f s x) {t : Set E}
  proof: by
  rw [← nhdsWithin_eq_iff_eventuallyEq] at hst
apply h.mono_of_mem_nhdsWithin hst ▸ self_mem_nhdsWithin

中文:
定理 ContDiffWithinAt.congr_set
  结论: (h : ContDiffWithinAt 𝕜 n f s x) {t : 集合 E}
  证明: by
  rw [← nhdsWithin_eq_iff_eventuallyEq] at hst
apply h.mono_of_mem_nhdsWithin hst ▸ self_mem_nhdsWithin

Depends on / 依赖: h.mono_of_mem_nhdsWithin, mono_of_mem_nhdsWithin, nhdsWithin_eq_iff_eventuallyEq, self_mem_nhdsWithin
-/
theorem ContDiffWithinAt.congr_set (h : ContDiffWithinAt 𝕜 n f s x) {t : Set E}
    (hst : s =ᶠ[𝓝 x] t) : ContDiffWithinAt 𝕜 n f t x := by
  rw [← nhdsWithin_eq_iff_eventuallyEq] at hst
apply h.mono_of_mem_nhdsWithin hst ▸ self_mem_nhdsWithin

/--
theorem `contDiffWithinAt_congr_set` / 定理 `contDiffWithinAt_congr_set`

English:
theorem contDiffWithinAt_congr_set
  given: {t : Set E} (hst : s =ᶠ[𝓝 x] t)
  proof: ⟨fun h => h.congr_set hst, fun h => h.congr_set hst.symm⟩

中文:
定理 contDiffWithinAt_congr_set
  条件: {t : 集合 E} (hst : s =ᶠ[𝓝 x] t)
  证明: ⟨fun h => h.congr_set hst, fun h => h.congr_set hst.symm⟩

Depends on / 依赖: congr_set, h.congr_set, hst.symm
-/
theorem contDiffWithinAt_congr_set {t : Set E} (hst : s =ᶠ[𝓝 x] t) :
    ContDiffWithinAt 𝕜 n f s x ↔ ContDiffWithinAt 𝕜 n f t x :=
  ⟨fun h => h.congr_set hst, fun h => h.congr_set hst.symm⟩

/--
theorem `contDiffWithinAt_inter'` / 定理 `contDiffWithinAt_inter'`

English:
theorem contDiffWithinAt_inter'
  given: (h : t in 𝓝[s] x)
  proof: contDiffWithinAt_congr_set (mem_nhdsWithin_iff_eventuallyEq.1 h).symm

中文:
定理 contDiffWithinAt_inter'
  条件: (h : t in 𝓝[s] x)
  证明: contDiffWithinAt_congr_set (mem_nhdsWithin_iff_eventuallyEq.1 h).symm

Depends on / 依赖: contDiffWithinAt_congr_set, mem_nhdsWithin_iff_eventuallyEq
-/
theorem contDiffWithinAt_inter' (h : t in 𝓝[s] x) :
    ContDiffWithinAt 𝕜 n f (s inter t) x ↔ ContDiffWithinAt 𝕜 n f s x :=
  contDiffWithinAt_congr_set (mem_nhdsWithin_iff_eventuallyEq.1 h).symm

/--
theorem `contDiffWithinAt_inter` / 定理 `contDiffWithinAt_inter`

English:
theorem contDiffWithinAt_inter
  given: (h : t in 𝓝 x)
  proof: contDiffWithinAt_inter' (mem_nhdsWithin_of_mem_nhds h)

中文:
定理 contDiffWithinAt_inter
  条件: (h : t in 𝓝 x)
  证明: contDiffWithinAt_inter' (mem_nhdsWithin_of_mem_nhds h)

Depends on / 依赖: contDiffWithinAt_inter, mem_nhdsWithin_of_mem_nhds
-/
theorem contDiffWithinAt_inter (h : t in 𝓝 x) :
    ContDiffWithinAt 𝕜 n f (s inter t) x ↔ ContDiffWithinAt 𝕜 n f s x :=
  contDiffWithinAt_inter' (mem_nhdsWithin_of_mem_nhds h)

/--
theorem `contDiffWithinAt_insert_self` / 定理 `contDiffWithinAt_insert_self`

English:
theorem contDiffWithinAt_insert_self
  proof: by
  match n with
  | ω => simp [ContDiffWithinAt]
  | (n : Nat∞) => simp_rw [ContDiffWithinAt, insert_idem]

中文:
定理 contDiffWithinAt_insert_self
  证明: by
  match n with
  | ω => simp [ContDiffWithinAt]
  | (n : Nat∞) => simp_rw [ContDiffWithinAt, insert_idem]

Depends on / 依赖: ContDiffWithinAt, insert_idem, simp_rw
-/
theorem contDiffWithinAt_insert_self :
    ContDiffWithinAt 𝕜 n f (insert x s) x ↔ ContDiffWithinAt 𝕜 n f s x := by
  match n with
  | ω => simp [ContDiffWithinAt]
  | (n : Nat∞) => simp_rw [ContDiffWithinAt, insert_idem]

/--
theorem `contDiffWithinAt_insert` / 定理 `contDiffWithinAt_insert`

English:
theorem contDiffWithinAt_insert
  given: {y : E}
  proof: by
  rcases eq_or_ne x y with (rfl | hx)
  · exact contDiffWithinAt_insert_self
  refine ⟨fun h => h.mono (subset_insert _ _), fun h => ?_⟩
  apply h.mono_of_mem_nhdsWithin
  simp [nhdsWithin_insert_of_ne hx, self_mem_nhdsWithin]

alias ⟨ContDiffWithinAt.of_insert, ContDiffWithinAt.insert'⟩ := contDiffWithinAt_insert

中文:
定理 contDiffWithinAt_insert
  条件: {y : E}
  证明: by
  rcases eq_or_ne x y with (rfl | hx)
  · exact contDiffWithinAt_insert_self
  refine ⟨fun h => h.mono (subset_insert _ _), fun h => ?_⟩
  apply h.mono_of_mem_nhdsWithin
  simp [nhdsWithin_insert_of_ne hx, self_mem_nhdsWithin]

alias ⟨ContDiffWithinAt.of_insert, ContDiffWithinAt.insert'⟩ := contDiffWithinAt_insert

Depends on / 依赖: contDiffWithinAt_insert_self, eq_or_ne, h.mono, h.mono_of_mem_nhdsWithin, mono_of_mem_nhdsWithin, nhdsWithin_insert_of_ne, self_mem_nhdsWithin, subset_insert
-/
theorem contDiffWithinAt_insert {y : E} :
    ContDiffWithinAt 𝕜 n f (insert y s) x ↔ ContDiffWithinAt 𝕜 n f s x := by
  rcases eq_or_ne x y with (rfl | hx)
  · exact contDiffWithinAt_insert_self
  refine ⟨fun h => h.mono (subset_insert _ _), fun h => ?_⟩
  apply h.mono_of_mem_nhdsWithin
  simp [nhdsWithin_insert_of_ne hx, self_mem_nhdsWithin]

alias ⟨ContDiffWithinAt.of_insert, ContDiffWithinAt.insert'⟩ := contDiffWithinAt_insert

/--
theorem `ContDiffWithinAt.insert` / 定理 `ContDiffWithinAt.insert`

English:
theorem ContDiffWithinAt.insert
  given: (h : ContDiffWithinAt 𝕜 n f s x)
  proof: h.insert'

中文:
定理 ContDiffWithinAt.insert
  条件: (h : ContDiffWithinAt 𝕜 n f s x)
  证明: h.insert'
-/
protected theorem ContDiffWithinAt.insert (h : ContDiffWithinAt 𝕜 n f s x) :
    ContDiffWithinAt 𝕜 n f (insert x s) x :=
  h.insert'

/--
theorem `contDiffWithinAt_sdiff_singleton` / 定理 `contDiffWithinAt_sdiff_singleton`

English:
theorem contDiffWithinAt_sdiff_singleton
  given: {y : E}
  proof: by
  rw [← contDiffWithinAt_insert]; rw [insert_sdiff_singleton]; rw [contDiffWithinAt_insert]

@[deprecated (since := "2026-06-03")]
alias contDiffWithinAt_diff_singleton := contDiffWithinAt_sdiff_singleton

中文:
定理 contDiffWithinAt_sdiff_singleton
  条件: {y : E}
  证明: by
  rw [← contDiffWithinAt_insert]; rw [insert_sdiff_singleton]; rw [contDiffWithinAt_insert]

@[deprecated (since := "2026-06-03")]
alias contDiffWithinAt_diff_singleton := contDiffWithinAt_sdiff_singleton

Depends on / 依赖: contDiffWithinAt_insert, insert_sdiff_singleton
-/
theorem contDiffWithinAt_sdiff_singleton {y : E} :
    ContDiffWithinAt 𝕜 n f (s \ {y}) x ↔ ContDiffWithinAt 𝕜 n f s x := by
  rw [← contDiffWithinAt_insert]; rw [insert_sdiff_singleton]; rw [contDiffWithinAt_insert]

@[deprecated (since := "2026-06-03")]
alias contDiffWithinAt_diff_singleton := contDiffWithinAt_sdiff_singleton

/--
theorem `ContDiffWithinAt.differentiableWithinAt'` / 定理 `ContDiffWithinAt.differentiableWithinAt'`

English:
theorem ContDiffWithinAt.differentiableWithinAt'
  given: (h : ContDiffWithinAt 𝕜 n f s x) (hn : n != 0)
  proof: by
  rcases contDiffWithinAt_nat.1 (h.of_le <| ENat.one_le_iff_ne_zero_withTop.mpr hn)
    with ⟨u, hu, p, H⟩
  rcases mem_nhdsWithin.1 hu with ⟨t, t_open, xt, tu⟩
  rw [inter_comm] at tu
exact (differentiableWithinAt_inter (IsOpen.mem_nhds t_open xt)).1
    ((H.mono tu).differentiableOn one_ne_zero) x ⟨mem_insert x s, xt⟩

中文:
定理 ContDiffWithinAt.differentiableWithinAt'
  条件: (h : ContDiffWithinAt 𝕜 n f s x) (hn : n != 0)
  证明: by
  rcases contDiffWithinAt_nat.1 (h.of_le <| ENat.one_le_iff_ne_zero_withTop.mpr hn)
    with ⟨u, hu, p, H⟩
  rcases mem_nhdsWithin.1 hu with ⟨t, t_open, xt, tu⟩
  rw [inter_comm] at tu
exact (differentiableWithinAt_inter (IsOpen.mem_nhds t_open xt)).1
    ((H.mono tu).differentiableOn one_ne_zero) x ⟨mem_insert x s, xt⟩

Depends on / 依赖: ENat.one_le_iff_ne_zero_withTop.mpr, H.mono, IsOpen, IsOpen.mem_nhds, contDiffWithinAt_nat, differentiableOn, differentiableWithinAt_inter, h.of_le, inter_comm, mem_insert, mem_nhds, mem_nhdsWithin, of_le, one_le_iff_ne_zero_withTop, one_ne_zero, t_open
-/
theorem ContDiffWithinAt.differentiableWithinAt' (h : ContDiffWithinAt 𝕜 n f s x) (hn : n != 0) :
    DifferentiableWithinAt 𝕜 f (insert x s) x := by
  rcases contDiffWithinAt_nat.1 (h.of_le <| ENat.one_le_iff_ne_zero_withTop.mpr hn)
    with ⟨u, hu, p, H⟩
  rcases mem_nhdsWithin.1 hu with ⟨t, t_open, xt, tu⟩
  rw [inter_comm] at tu
exact (differentiableWithinAt_inter (IsOpen.mem_nhds t_open xt)).1
    ((H.mono tu).differentiableOn one_ne_zero) x ⟨mem_insert x s, xt⟩

/--
theorem `ContDiffWithinAt.differentiableWithinAt` / 定理 `ContDiffWithinAt.differentiableWithinAt`

English:
theorem ContDiffWithinAt.differentiableWithinAt
  given: (h : ContDiffWithinAt 𝕜 n f s x) (hn : n != 0)
  proof: (h.differentiableWithinAt' hn).mono (subset_insert x s)

中文:
定理 ContDiffWithinAt.differentiableWithinAt
  条件: (h : ContDiffWithinAt 𝕜 n f s x) (hn : n != 0)
  证明: (h.differentiableWithinAt' hn).mono (subset_insert x s)

Depends on / 依赖: differentiableWithinAt, h.differentiableWithinAt, subset_insert
-/
theorem ContDiffWithinAt.differentiableWithinAt (h : ContDiffWithinAt 𝕜 n f s x) (hn : n != 0) :
    DifferentiableWithinAt 𝕜 f s x :=
  (h.differentiableWithinAt' hn).mono (subset_insert x s)

/--
theorem `contDiffWithinAt_succ_iff_hasFDerivWithinAt` / 定理 `contDiffWithinAt_succ_iff_hasFDerivWithinAt`

English:
theorem contDiffWithinAt_succ_iff_hasFDerivWithinAt
  given: (hn : n != ∞)
  proof: by
  have h'n : n + 1 != ∞ := by simpa using hn
  constructor
  · intro h
    rcases (contDiffWithinAt_iff_of_ne_infty h'n).1 h with ⟨u, hu, p, Hp, H'p⟩
    refine ⟨u, hu, ?_, fun y => (continuousMultilinearCurryFin1 𝕜 E F) (p y 1),
        fun y hy => Hp.hasFDerivWithinAt (by simp) hy, ?_⟩
    · rintro rfl
      exact Hp.analyticOn (H'p rfl 0)
    apply (contDiffWithinAt_iff_of_ne_infty hn).2
    refine ⟨u, ?_, fun y : E => (p y).shift, ?_⟩
    · convert! @self_mem_nhdsWithin _ _ x u
      have : x in insert x s := by simp
      exact insert_eq_of_mem (mem_of_mem_nhdsWithin this hu)
    · rw [hasFTaylorSeriesUpToOn_succ_iff_right] at Hp
      refine ⟨Hp.2.2, ?_⟩
      rintro rfl i
      change AnalyticOn 𝕜
        (fun x => (continuousMultilinearCurryRightEquiv' 𝕜 i E F) (p x (i + 1))) u
      apply (LinearIsometryEquiv.analyticOnNhd _ _).comp_analyticOn
        ?_ (Set.mapsTo_univ _ _)
      exact H'p rfl _
  · rintro ⟨u, hu, hf, f', f'_eq_deriv, Hf'⟩
    rw [contDiffWithinAt_iff_of_ne_infty h'n]
    rcases (contDiffWithinAt_iff_of_ne_infty hn).1 Hf' with ⟨v, hv, p', Hp', p'_an⟩
    refine ⟨v inter u, ?_, fun x => (p' x).unshift (f x), ?_, ?_⟩
    · apply Filter.inter_mem _ hu
      apply nhdsWithin_le_of_mem hu
      exact nhdsWithin_mono _ (subset_insert x u) hv
    · rw [hasFTaylorSeriesUpToOn_succ_iff_right]
      refine ⟨fun y _ => rfl, fun y hy => ?_, ?_⟩
      · change
          HasFDerivWithinAt (fun z => (continuousMultilinearCurryFin0 𝕜 E F).symm (f z))
            (FormalMultilinearSeries.unshift (p' y) (f y) 1).curryLeft (v inter u) y
        rw [← Function.comp_def _ f]; rw [LinearIsometryEquiv.comp_hasFDerivWithinAt_iff']
        convert! (f'_eq_deriv y hy.2).mono inter_subset_right
        rw [← Hp'.zero_eq y hy.1]
        ext z
        change ((p' y 0) (init (@cons 0 (fun _ => E) z 0))) (@cons 0 (fun _ => E) z 0 (last 0)) =
          ((p' y 0) 0) z
        congr
        norm_num [eq_iff_true_of_subsingleton]
      · convert! (Hp'.mono inter_subset_left).congr fun x hx => Hp'.zero_eq x hx.1 using 1
        · ext x y
          change p' x 0 (init (@snoc 0 (fun _ : Fin 1 => E) 0 y)) y = p' x 0 0 y
          rw [init_snoc]
        · ext x k v y
          change p' x k (init (@snoc k (fun _ : Fin k.succ => E) v y))
            (@snoc k (fun _ : Fin k.succ => E) v y (last k)) = p' x k v y
          rw [snoc_last]; rw [init_snoc]
    · intro h i
      simp only [WithTop.add_eq_top, WithTop.one_ne_top, or_false] at h
      match i with
      | 0 =>
        simp only [FormalMultilinearSeries.unshift]
        apply AnalyticOnNhd.comp_analyticOn _ ((hf h).mono inter_subset_right)
          (Set.mapsTo_univ _ _)
        exact LinearIsometryEquiv.analyticOnNhd _ _
      | i + 1 =>
        simp only [FormalMultilinearSeries.unshift, Nat.succ_eq_add_one]
        apply AnalyticOnNhd.comp_analyticOn _ ((p'_an h i).mono inter_subset_left)
          (Set.mapsTo_univ _ _)
        exact LinearIsometryEquiv.analyticOnNhd _ _

中文:
定理 contDiffWithinAt_succ_iff_hasFDerivWithinAt
  条件: (hn : n != ∞)
  证明: by
  have h'n : n + 1 != ∞ := by simpa using hn
  constructor
  · intro h
    rcases (contDiffWithinAt_iff_of_ne_infty h'n).1 h with ⟨u, hu, p, Hp, H'p⟩
    refine ⟨u, hu, ?_, fun y => (continuousMultilinearCurryFin1 𝕜 E F) (p y 1),
        fun y hy => Hp.hasFDerivWithinAt (by simp) hy, ?_⟩
    · rintro rfl
      exact Hp.analyticOn (H'p rfl 0)
    apply (contDiffWithinAt_iff_of_ne_infty hn).2
    refine ⟨u, ?_, fun y : E => (p y).shift, ?_⟩
    · convert! @self_mem_nhdsWithin _ _ x u
      have : x in insert x s := by simp
      exact insert_eq_of_mem (mem_of_mem_nhdsWithin this hu)
    · rw [hasFTaylorSeriesUpToOn_succ_iff_right] at Hp
      refine ⟨Hp.2.2, ?_⟩
      rintro rfl i
      change AnalyticOn 𝕜
        (fun x => (continuousMultilinearCurryRightEquiv' 𝕜 i E F) (p x (i + 1))) u
      apply (LinearIsometryEquiv.analyticOnNhd _ _).comp_analyticOn
        ?_ (Set.mapsTo_univ _ _)
      exact H'p rfl _
  · rintro ⟨u, hu, hf, f', f'_eq_deriv, Hf'⟩
    rw [contDiffWithinAt_iff_of_ne_infty h'n]
    rcases (contDiffWithinAt_iff_of_ne_infty hn).1 Hf' with ⟨v, hv, p', Hp', p'_an⟩
    refine ⟨v inter u, ?_, fun x => (p' x).unshift (f x), ?_, ?_⟩
    · apply Filter.inter_mem _ hu
      apply nhdsWithin_le_of_mem hu
      exact nhdsWithin_mono _ (subset_insert x u) hv
    · rw [hasFTaylorSeriesUpToOn_succ_iff_right]
      refine ⟨fun y _ => rfl, fun y hy => ?_, ?_⟩
      · change
          HasFDerivWithinAt (fun z => (continuousMultilinearCurryFin0 𝕜 E F).symm (f z))
            (FormalMultilinearSeries.unshift (p' y) (f y) 1).curryLeft (v inter u) y
        rw [← Function.comp_def _ f]; rw [LinearIsometryEquiv.comp_hasFDerivWithinAt_iff']
        convert! (f'_eq_deriv y hy.2).mono inter_subset_right
        rw [← Hp'.zero_eq y hy.1]
        ext z
        change ((p' y 0) (init (@cons 0 (fun _ => E) z 0))) (@cons 0 (fun _ => E) z 0 (last 0)) =
          ((p' y 0) 0) z
        congr
        norm_num [eq_iff_true_of_subsingleton]
      · convert! (Hp'.mono inter_subset_left).congr fun x hx => Hp'.zero_eq x hx.1 using 1
        · ext x y
          change p' x 0 (init (@snoc 0 (fun _ : Fin 1 => E) 0 y)) y = p' x 0 0 y
          rw [init_snoc]
        · ext x k v y
          change p' x k (init (@snoc k (fun _ : Fin k.succ => E) v y))
            (@snoc k (fun _ : Fin k.succ => E) v y (last k)) = p' x k v y
          rw [snoc_last]; rw [init_snoc]
    · intro h i
      simp only [WithTop.add_eq_top, WithTop.one_ne_top, or_false] at h
      match i with
      | 0 =>
        simp only [FormalMultilinearSeries.unshift]
        apply AnalyticOnNhd.comp_analyticOn _ ((hf h).mono inter_subset_right)
          (Set.mapsTo_univ _ _)
        exact LinearIsometryEquiv.analyticOnNhd _ _
      | i + 1 =>
        simp only [FormalMultilinearSeries.unshift, Nat.succ_eq_add_one]
        apply AnalyticOnNhd.comp_analyticOn _ ((p'_an h i).mono inter_subset_left)
          (Set.mapsTo_univ _ _)
        exact LinearIsometryEquiv.analyticOnNhd _ _

Depends on / 依赖: Hp.analyticOn, Hp.hasFDerivWithinAt, analyticOn, contDiffWithinAt_iff_of_ne_infty, continuousMultilinearCurryFin1, convert, hasFDerivWithinAt, insert, insert_eq_of_m, self_mem_nhdsWithin
-/
theorem contDiffWithinAt_succ_iff_hasFDerivWithinAt (hn : n != ∞) :
    ContDiffWithinAt 𝕜 (n + 1) f s x ↔ exists u in 𝓝[insert x s] x, (n = ω -> AnalyticOn 𝕜 f u) ∧
      exists f' : E -> E ->L[𝕜] F,
      (forall x in u, HasFDerivWithinAt f (f' x) u x) ∧ ContDiffWithinAt 𝕜 n f' u x := by
  have h'n : n + 1 != ∞ := by simpa using hn
  constructor
  · intro h
    rcases (contDiffWithinAt_iff_of_ne_infty h'n).1 h with ⟨u, hu, p, Hp, H'p⟩
    refine ⟨u, hu, ?_, fun y => (continuousMultilinearCurryFin1 𝕜 E F) (p y 1),
        fun y hy => Hp.hasFDerivWithinAt (by simp) hy, ?_⟩
    · rintro rfl
      exact Hp.analyticOn (H'p rfl 0)
    apply (contDiffWithinAt_iff_of_ne_infty hn).2
    refine ⟨u, ?_, fun y : E => (p y).shift, ?_⟩
    · convert! @self_mem_nhdsWithin _ _ x u
      have : x in insert x s := by simp
      exact insert_eq_of_mem (mem_of_mem_nhdsWithin this hu)
    · rw [hasFTaylorSeriesUpToOn_succ_iff_right] at Hp
      refine ⟨Hp.2.2, ?_⟩
      rintro rfl i
      change AnalyticOn 𝕜
        (fun x => (continuousMultilinearCurryRightEquiv' 𝕜 i E F) (p x (i + 1))) u
      apply (LinearIsometryEquiv.analyticOnNhd _ _).comp_analyticOn
        ?_ (Set.mapsTo_univ _ _)
      exact H'p rfl _
  · rintro ⟨u, hu, hf, f', f'_eq_deriv, Hf'⟩
    rw [contDiffWithinAt_iff_of_ne_infty h'n]
    rcases (contDiffWithinAt_iff_of_ne_infty hn).1 Hf' with ⟨v, hv, p', Hp', p'_an⟩
    refine ⟨v inter u, ?_, fun x => (p' x).unshift (f x), ?_, ?_⟩
    · apply Filter.inter_mem _ hu
      apply nhdsWithin_le_of_mem hu
      exact nhdsWithin_mono _ (subset_insert x u) hv
    · rw [hasFTaylorSeriesUpToOn_succ_iff_right]
      refine ⟨fun y _ => rfl, fun y hy => ?_, ?_⟩
      · change
          HasFDerivWithinAt (fun z => (continuousMultilinearCurryFin0 𝕜 E F).symm (f z))
            (FormalMultilinearSeries.unshift (p' y) (f y) 1).curryLeft (v inter u) y
        rw [← Function.comp_def _ f]; rw [LinearIsometryEquiv.comp_hasFDerivWithinAt_iff']
        convert! (f'_eq_deriv y hy.2).mono inter_subset_right
        rw [← Hp'.zero_eq y hy.1]
        ext z
        change ((p' y 0) (init (@cons 0 (fun _ => E) z 0))) (@cons 0 (fun _ => E) z 0 (last 0)) =
          ((p' y 0) 0) z
        congr
        norm_num [eq_iff_true_of_subsingleton]
      · convert! (Hp'.mono inter_subset_left).congr fun x hx => Hp'.zero_eq x hx.1 using 1
        · ext x y
          change p' x 0 (init (@snoc 0 (fun _ : Fin 1 => E) 0 y)) y = p' x 0 0 y
          rw [init_snoc]
        · ext x k v y
          change p' x k (init (@snoc k (fun _ : Fin k.succ => E) v y))
            (@snoc k (fun _ : Fin k.succ => E) v y (last k)) = p' x k v y
          rw [snoc_last]; rw [init_snoc]
    · intro h i
      simp only [WithTop.add_eq_top, WithTop.one_ne_top, or_false] at h
      match i with
      | 0 =>
        simp only [FormalMultilinearSeries.unshift]
        apply AnalyticOnNhd.comp_analyticOn _ ((hf h).mono inter_subset_right)
          (Set.mapsTo_univ _ _)
        exact LinearIsometryEquiv.analyticOnNhd _ _
      | i + 1 =>
        simp only [FormalMultilinearSeries.unshift, Nat.succ_eq_add_one]
        apply AnalyticOnNhd.comp_analyticOn _ ((p'_an h i).mono inter_subset_left)
          (Set.mapsTo_univ _ _)
        exact LinearIsometryEquiv.analyticOnNhd _ _

/--
theorem `contDiffWithinAt_succ_iff_hasFDerivWithinAt'` / 定理 `contDiffWithinAt_succ_iff_hasFDerivWithinAt'`

English:
theorem contDiffWithinAt_succ_iff_hasFDerivWithinAt'
  given: (hn : n != ∞)
  proof: by
  refine ⟨fun hf => ?_, ?_⟩
  · obtain ⟨u, hu, f_an, f', huf', hf'⟩ := (contDiffWithinAt_succ_iff_hasFDerivWithinAt hn).mp hf
    obtain ⟨w, hw, hxw, hwu⟩ := mem_nhdsWithin.mp hu
    rw [inter_comm] at hwu
    refine ⟨insert x s inter w, inter_mem_nhdsWithin _ (hw.mem_nhds hxw), inter_subset_left, ?_, f',
      fun y hy => ?_, ?_⟩
    · intro h
      apply (f_an h).mono hwu
    · refine ((huf' y <| hwu hy).mono hwu).mono_of_mem_nhdsWithin ?_
      grw [← subset_insert]
      exact inter_mem_nhdsWithin _ (hw.mem_nhds hy.2)
    · exact hf'.mono_of_mem_nhdsWithin (nhdsWithin_mono _ (subset_insert _ _) hu)
  · rw [← contDiffWithinAt_insert, contDiffWithinAt_succ_iff_hasFDerivWithinAt hn,
      insert_eq_of_mem (mem_insert _ _)]
    rintro ⟨u, hu, hus, f_an, f', huf', hf'⟩
    exact ⟨u, hu, f_an, f', fun y hy => (huf' y hy).insert'.mono hus, hf'.insert.mono hus⟩

中文:
定理 contDiffWithinAt_succ_iff_hasFDerivWithinAt'
  条件: (hn : n != ∞)
  证明: by
  refine ⟨fun hf => ?_, ?_⟩
  · obtain ⟨u, hu, f_an, f', huf', hf'⟩ := (contDiffWithinAt_succ_iff_hasFDerivWithinAt hn).mp hf
    obtain ⟨w, hw, hxw, hwu⟩ := mem_nhdsWithin.mp hu
    rw [inter_comm] at hwu
    refine ⟨insert x s inter w, inter_mem_nhdsWithin _ (hw.mem_nhds hxw), inter_subset_left, ?_, f',
      fun y hy => ?_, ?_⟩
    · intro h
      apply (f_an h).mono hwu
    · refine ((huf' y <| hwu hy).mono hwu).mono_of_mem_nhdsWithin ?_
      grw [← subset_insert]
      exact inter_mem_nhdsWithin _ (hw.mem_nhds hy.2)
    · exact hf'.mono_of_mem_nhdsWithin (nhdsWithin_mono _ (subset_insert _ _) hu)
  · rw [← contDiffWithinAt_insert, contDiffWithinAt_succ_iff_hasFDerivWithinAt hn,
      insert_eq_of_mem (mem_insert _ _)]
    rintro ⟨u, hu, hus, f_an, f', huf', hf'⟩
    exact ⟨u, hu, f_an, f', fun y hy => (huf' y hy).insert'.mono hus, hf'.insert.mono hus⟩

Depends on / 依赖: contDiffWithinAt_succ_iff_hasFDerivWithinAt, f_an, hw.mem_nhds, insert, inter_comm, inter_mem_nhdsWithin, inter_subset_left, mem_nhds, mem_nhdsWithin, mem_nhdsWithin.mp, mono_, mono_of_mem_nhdsWithin, subset_insert
-/
theorem contDiffWithinAt_succ_iff_hasFDerivWithinAt' (hn : n != ∞) :
    ContDiffWithinAt 𝕜 (n + 1) f s x ↔
      exists u in 𝓝[insert x s] x, u subseteq insert x s ∧ (n = ω -> AnalyticOn 𝕜 f u) ∧
      exists f' : E -> E ->L[𝕜] F,
        (forall x in u, HasFDerivWithinAt f (f' x) s x) ∧ ContDiffWithinAt 𝕜 n f' s x := by
  refine ⟨fun hf => ?_, ?_⟩
  · obtain ⟨u, hu, f_an, f', huf', hf'⟩ := (contDiffWithinAt_succ_iff_hasFDerivWithinAt hn).mp hf
    obtain ⟨w, hw, hxw, hwu⟩ := mem_nhdsWithin.mp hu
    rw [inter_comm] at hwu
    refine ⟨insert x s inter w, inter_mem_nhdsWithin _ (hw.mem_nhds hxw), inter_subset_left, ?_, f',
      fun y hy => ?_, ?_⟩
    · intro h
      apply (f_an h).mono hwu
    · refine ((huf' y <| hwu hy).mono hwu).mono_of_mem_nhdsWithin ?_
      grw [← subset_insert]
      exact inter_mem_nhdsWithin _ (hw.mem_nhds hy.2)
    · exact hf'.mono_of_mem_nhdsWithin (nhdsWithin_mono _ (subset_insert _ _) hu)
  · rw [← contDiffWithinAt_insert, contDiffWithinAt_succ_iff_hasFDerivWithinAt hn,
      insert_eq_of_mem (mem_insert _ _)]
    rintro ⟨u, hu, hus, f_an, f', huf', hf'⟩
    exact ⟨u, hu, f_an, f', fun y hy => (huf' y hy).insert'.mono hus, hf'.insert.mono hus⟩


/-! ### Smooth functions within a set -/

variable (𝕜) in
/-- A function is continuously differentiable up to `n` on `s` if, for any point `x` in `s`, it
admits continuous derivatives up to order `n` on a neighborhood of `x` in `s`.
The parameter `n` belongs to `ℕ∞ω` (accessible in the `ContDiff` scope), i.e. it can be a natural
number, `∞`, or `ω`.

For `n = ∞`, we only require that this holds up to any finite order (where the neighborhood may
depend on the finite order we consider).
For `n = ω`, we require the function to be analytic within `s` at every point of `s`. The precise
definition we give (all the derivatives should be analytic) is more involved to work around issues
when the space is not complete, but it is equivalent when the space is complete.
-/
@[fun_prop]
/--
Definition of `ContDiffOn` / `ContDiffOn` 的定义

English:
definition ContDiffOn
  signature: (n : Nat∞ω) (f : E -> F) (s : Set E)
  body: forall x in s, ContDiffWithinAt 𝕜 n f s x

中文:
定义 ContDiffOn
  签名: (n : 自然数∞ω) (f : E -> F) (s : 集合 E)
  定义体: forall x in s, ContDiffWithinAt 𝕜 n f s x

Depends on / 依赖: ContDiffWithinAt
-/
def ContDiffOn (n : Nat∞ω) (f : E -> F) (s : Set E) : Prop :=
  forall x in s, ContDiffWithinAt 𝕜 n f s x

/--
theorem `HasFTaylorSeriesUpToOn.contDiffOn` / 定理 `HasFTaylorSeriesUpToOn.contDiffOn`

English:
theorem HasFTaylorSeriesUpToOn.contDiffOn
  statement: {n : Nat∞} {f' : E -> FormalMultilinearSeries 𝕜 E F}
  proof: by
  intro x hx m hm
  use s
  simp only [Set.insert_eq_of_mem hx, self_mem_nhdsWithin, true_and]
  exact ⟨f', hf.of_le (mod_cast hm)⟩

中文:
定理 有FTaylorSeriesUpToOn.contDiffOn
  结论: {n : 自然数∞} {f' : E -> FormalMultilinearSeries 𝕜 E F}
  证明: by
  intro x hx m hm
  use s
  simp only [Set.insert_eq_of_mem hx, self_mem_nhdsWithin, true_and]
  exact ⟨f', hf.of_le (mod_cast hm)⟩

Depends on / 依赖: Set.insert_eq_of_mem, hf.of_le, insert_eq_of_mem, mod_cast, of_le, self_mem_nhdsWithin, true_and
-/
theorem HasFTaylorSeriesUpToOn.contDiffOn {n : Nat∞} {f' : E -> FormalMultilinearSeries 𝕜 E F}
    (hf : HasFTaylorSeriesUpToOn n f f' s) : ContDiffOn 𝕜 n f s := by
  intro x hx m hm
  use s
  simp only [Set.insert_eq_of_mem hx, self_mem_nhdsWithin, true_and]
  exact ⟨f', hf.of_le (mod_cast hm)⟩

/--
theorem `ContDiffOn.contDiffWithinAt` / 定理 `ContDiffOn.contDiffWithinAt`

English:
theorem ContDiffOn.contDiffWithinAt
  given: (h : ContDiffOn 𝕜 n f s) (hx : x in s)
  proof: h x hx

@[fun_prop]

中文:
定理 ContDiffOn.contDiffWithinAt
  条件: (h : ContDiffOn 𝕜 n f s) (hx : x in s)
  证明: h x hx

@[fun_prop]
-/
theorem ContDiffOn.contDiffWithinAt (h : ContDiffOn 𝕜 n f s) (hx : x in s) :
    ContDiffWithinAt 𝕜 n f s x :=
  h x hx

@[fun_prop]
/--
theorem `ContDiffOn.of_le` / 定理 `ContDiffOn.of_le`

English:
theorem ContDiffOn.of_le
  given: (h : ContDiffOn 𝕜 n f s) (hmn : m <= n)
  statement: ContDiffOn 𝕜 m f s
  proof: fun x hx =>
  (h x hx).of_le hmn

中文:
定理 ContDiffOn.of_le
  条件: (h : ContDiffOn 𝕜 n f s) (hmn : m <= n)
  结论: ContDiffOn 𝕜 m f s
  证明: fun x hx =>
  (h x hx).of_le hmn
-/
theorem ContDiffOn.of_le (h : ContDiffOn 𝕜 n f s) (hmn : m <= n) : ContDiffOn 𝕜 m f s := fun x hx =>
  (h x hx).of_le hmn

/--
theorem `ContDiffWithinAt.contDiffOn'` / 定理 `ContDiffWithinAt.contDiffOn'`

English:
theorem ContDiffWithinAt.contDiffOn'
  statement: (hm : m <= n) (h' : m = ∞ -> n = ω)
  proof: by
  rcases eq_or_ne n ω with rfl | hn
  · obtain ⟨t, ht, p, hp, h'p⟩ := h
    rcases mem_nhdsWithin.1 ht with ⟨u, huo, hxu, hut⟩
    rw [inter_comm] at hut
    refine ⟨u, huo, hxu, ?_⟩
    suffices ContDiffOn 𝕜 ω f (insert x s inter u) from this.of_le le_top
    intro y hy
    refine ⟨insert x s inter u, ?_, p, hp.mono hut, fun i => (h'p i).mono hut⟩
    simp only [insert_eq_of_mem, hy, self_mem_nhdsWithin]
  · match m with
    | ω => simp [hn] at hm
    | ∞ => exact (hn (h' rfl)).elim
    | (m : Nat) =>
      rcases contDiffWithinAt_nat.1 (h.of_le hm) with ⟨t, ht, p, hp⟩
      rcases mem_nhdsWithin.1 ht with ⟨u, huo, hxu, hut⟩
      rw [inter_comm] at hut
      exact ⟨u, huo, hxu, (hp.mono hut).contDiffOn⟩

中文:
定理 ContDiffWithinAt.contDiffOn'
  结论: (hm : m <= n) (h' : m = ∞ -> n = ω)
  证明: by
  rcases eq_or_ne n ω with rfl | hn
  · obtain ⟨t, ht, p, hp, h'p⟩ := h
    rcases mem_nhdsWithin.1 ht with ⟨u, huo, hxu, hut⟩
    rw [inter_comm] at hut
    refine ⟨u, huo, hxu, ?_⟩
    suffices ContDiffOn 𝕜 ω f (insert x s inter u) from this.of_le le_top
    intro y hy
    refine ⟨insert x s inter u, ?_, p, hp.mono hut, fun i => (h'p i).mono hut⟩
    simp only [insert_eq_of_mem, hy, self_mem_nhdsWithin]
  · match m with
    | ω => simp [hn] at hm
    | ∞ => exact (hn (h' rfl)).elim
    | (m : Nat) =>
      rcases contDiffWithinAt_nat.1 (h.of_le hm) with ⟨t, ht, p, hp⟩
      rcases mem_nhdsWithin.1 ht with ⟨u, huo, hxu, hut⟩
      rw [inter_comm] at hut
      exact ⟨u, huo, hxu, (hp.mono hut).contDiffOn⟩

Depends on / 依赖: ContDiffOn, contDiffWithinAt_nat, eq_or_ne, h.of, hp.mono, insert, insert_eq_of_mem, inter_comm, le_top, mem_nhdsWithin, of_le, self_mem_nhdsWithin, this.of_le
-/
theorem ContDiffWithinAt.contDiffOn' (hm : m <= n) (h' : m = ∞ -> n = ω)
    (h : ContDiffWithinAt 𝕜 n f s x) :
    exists u, IsOpen u ∧ x in u ∧ ContDiffOn 𝕜 m f (insert x s inter u) := by
  rcases eq_or_ne n ω with rfl | hn
  · obtain ⟨t, ht, p, hp, h'p⟩ := h
    rcases mem_nhdsWithin.1 ht with ⟨u, huo, hxu, hut⟩
    rw [inter_comm] at hut
    refine ⟨u, huo, hxu, ?_⟩
    suffices ContDiffOn 𝕜 ω f (insert x s inter u) from this.of_le le_top
    intro y hy
    refine ⟨insert x s inter u, ?_, p, hp.mono hut, fun i => (h'p i).mono hut⟩
    simp only [insert_eq_of_mem, hy, self_mem_nhdsWithin]
  · match m with
    | ω => simp [hn] at hm
    | ∞ => exact (hn (h' rfl)).elim
    | (m : Nat) =>
      rcases contDiffWithinAt_nat.1 (h.of_le hm) with ⟨t, ht, p, hp⟩
      rcases mem_nhdsWithin.1 ht with ⟨u, huo, hxu, hut⟩
      rw [inter_comm] at hut
      exact ⟨u, huo, hxu, (hp.mono hut).contDiffOn⟩

/--
theorem `ContDiffWithinAt.contDiffOn` / 定理 `ContDiffWithinAt.contDiffOn`

English:
theorem ContDiffWithinAt.contDiffOn
  statement: (hm : m <= n) (h' : m = ∞ -> n = ω)
  proof: by
  obtain ⟨_u, uo, xu, h⟩ := h.contDiffOn' hm h'
  exact ⟨_, inter_mem_nhdsWithin _ (uo.mem_nhds xu), inter_subset_left, h⟩

中文:
定理 ContDiffWithinAt.contDiffOn
  结论: (hm : m <= n) (h' : m = ∞ -> n = ω)
  证明: by
  obtain ⟨_u, uo, xu, h⟩ := h.contDiffOn' hm h'
  exact ⟨_, inter_mem_nhdsWithin _ (uo.mem_nhds xu), inter_subset_left, h⟩

Depends on / 依赖: contDiffOn, h.contDiffOn, inter_mem_nhdsWithin, inter_subset_left, mem_nhds, uo.mem_nhds
-/
theorem ContDiffWithinAt.contDiffOn (hm : m <= n) (h' : m = ∞ -> n = ω)
    (h : ContDiffWithinAt 𝕜 n f s x) :
    exists u in 𝓝[insert x s] x, u subseteq insert x s ∧ ContDiffOn 𝕜 m f u := by
  obtain ⟨_u, uo, xu, h⟩ := h.contDiffOn' hm h'
  exact ⟨_, inter_mem_nhdsWithin _ (uo.mem_nhds xu), inter_subset_left, h⟩

/--
theorem `ContDiffOn.analyticOn` / 定理 `ContDiffOn.analyticOn`

English:
theorem ContDiffOn.analyticOn
  given: (h : ContDiffOn 𝕜 ω f s)
  statement: AnalyticOn 𝕜 f s
  proof: fun x hx => (h x hx).analyticWithinAt

中文:
定理 ContDiffOn.analyticOn
  条件: (h : ContDiffOn 𝕜 ω f s)
  结论: AnalyticOn 𝕜 f s
  证明: fun x hx => (h x hx).analyticWithinAt

Depends on / 依赖: analyticWithinAt
-/
theorem ContDiffOn.analyticOn (h : ContDiffOn 𝕜 ω f s) : AnalyticOn 𝕜 f s :=
  fun x hx => (h x hx).analyticWithinAt

/--
theorem `contDiffWithinAt_iff_contDiffOn_nhds` / 定理 `contDiffWithinAt_iff_contDiffOn_nhds`

English:
theorem contDiffWithinAt_iff_contDiffOn_nhds
  given: (hn : n != ∞)
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h.contDiffOn le_rfl (by simp [hn]) with ⟨u, hu, h'u⟩
    exact ⟨u, hu, h'u.2⟩
  · rcases h with ⟨u, u_mem, hu⟩
    have : x in u := mem_of_mem_nhdsWithin (mem_insert x s) u_mem
    exact (hu x this).mono_of_mem_nhdsWithin (nhdsWithin_mono _ (subset_insert x s) u_mem)

中文:
定理 contDiffWithinAt_iff_contDiffOn_nhds
  条件: (hn : n != ∞)
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h.contDiffOn le_rfl (by simp [hn]) with ⟨u, hu, h'u⟩
    exact ⟨u, hu, h'u.2⟩
  · rcases h with ⟨u, u_mem, hu⟩
    have : x in u := mem_of_mem_nhdsWithin (mem_insert x s) u_mem
    exact (hu x this).mono_of_mem_nhdsWithin (nhdsWithin_mono _ (subset_insert x s) u_mem)

Depends on / 依赖: contDiffOn, h.contDiffOn, le_rfl, mem_insert, mem_of_mem_nhdsWithin, mono_of_mem_nhdsWithin, nhdsWithin_mono, subset_insert, u_mem
-/
theorem contDiffWithinAt_iff_contDiffOn_nhds (hn : n != ∞) :
    ContDiffWithinAt 𝕜 n f s x ↔ exists u in 𝓝[insert x s] x, ContDiffOn 𝕜 n f u := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h.contDiffOn le_rfl (by simp [hn]) with ⟨u, hu, h'u⟩
    exact ⟨u, hu, h'u.2⟩
  · rcases h with ⟨u, u_mem, hu⟩
    have : x in u := mem_of_mem_nhdsWithin (mem_insert x s) u_mem
    exact (hu x this).mono_of_mem_nhdsWithin (nhdsWithin_mono _ (subset_insert x s) u_mem)

/--
theorem `ContDiffWithinAt.eventually` / 定理 `ContDiffWithinAt.eventually`

English:
theorem ContDiffWithinAt.eventually
  given: (h : ContDiffWithinAt 𝕜 n f s x) (hn : n != ∞)
  proof: by
  rcases h.contDiffOn le_rfl (by simp [hn]) with ⟨u, hu, _, hd⟩
  have : forallᶠ y : E in 𝓝[insert x s] x, u in 𝓝[insert x s] y ∧ y in u :=
    (eventually_eventually_nhdsWithin.2 hu).and hu
  refine this.mono fun y hy => (hd y hy.2).mono_of_mem_nhdsWithin ?_
  exact nhdsWithin_mono y (subset_insert _ _) hy.1

中文:
定理 ContDiffWithinAt.eventually
  条件: (h : ContDiffWithinAt 𝕜 n f s x) (hn : n != ∞)
  证明: by
  rcases h.contDiffOn le_rfl (by simp [hn]) with ⟨u, hu, _, hd⟩
  have : forallᶠ y : E in 𝓝[insert x s] x, u in 𝓝[insert x s] y ∧ y in u :=
    (eventually_eventually_nhdsWithin.2 hu).and hu
  refine this.mono fun y hy => (hd y hy.2).mono_of_mem_nhdsWithin ?_
  exact nhdsWithin_mono y (subset_insert _ _) hy.1
-/
protected theorem ContDiffWithinAt.eventually (h : ContDiffWithinAt 𝕜 n f s x) (hn : n != ∞) :
    forallᶠ y in 𝓝[insert x s] x, ContDiffWithinAt 𝕜 n f s y := by
  rcases h.contDiffOn le_rfl (by simp [hn]) with ⟨u, hu, _, hd⟩
  have : forallᶠ y : E in 𝓝[insert x s] x, u in 𝓝[insert x s] y ∧ y in u :=
    (eventually_eventually_nhdsWithin.2 hu).and hu
  refine this.mono fun y hy => (hd y hy.2).mono_of_mem_nhdsWithin ?_
  exact nhdsWithin_mono y (subset_insert _ _) hy.1

/--
theorem `ContDiffOn.of_succ` / 定理 `ContDiffOn.of_succ`

English:
theorem ContDiffOn.of_succ
  given: (h : ContDiffOn 𝕜 (n + 1) f s)
  statement: ContDiffOn 𝕜 n f s
  proof: h.of_le le_self_add

中文:
定理 ContDiffOn.of_succ
  条件: (h : ContDiffOn 𝕜 (n + 1) f s)
  结论: ContDiffOn 𝕜 n f s
  证明: h.of_le le_self_add

Depends on / 依赖: h.of_le, le_self_add, of_le
-/
theorem ContDiffOn.of_succ (h : ContDiffOn 𝕜 (n + 1) f s) : ContDiffOn 𝕜 n f s :=
  h.of_le le_self_add

/--
theorem `ContDiffOn.one_of_succ` / 定理 `ContDiffOn.one_of_succ`

English:
theorem ContDiffOn.one_of_succ
  given: (h : ContDiffOn 𝕜 (n + 1) f s)
  statement: ContDiffOn 𝕜 1 f s
  proof: h.of_le le_add_self

中文:
定理 ContDiffOn.one_of_succ
  条件: (h : ContDiffOn 𝕜 (n + 1) f s)
  结论: ContDiffOn 𝕜 1 f s
  证明: h.of_le le_add_self

Depends on / 依赖: h.of_le, le_add_self, of_le
-/
theorem ContDiffOn.one_of_succ (h : ContDiffOn 𝕜 (n + 1) f s) : ContDiffOn 𝕜 1 f s :=
  h.of_le le_add_self

/--
theorem `contDiffOn_iff_forall_nat_le` / 定理 `contDiffOn_iff_forall_nat_le`

English:
theorem contDiffOn_iff_forall_nat_le
  given: {n : Nat∞}
  proof: ⟨fun H _ hm => H.of_le (mod_cast hm), fun H x hx m hm => H m hm x hx m le_rfl⟩

中文:
定理 contDiffOn_iff_对任意_nat_le
  条件: {n : 自然数∞}
  证明: ⟨fun H _ hm => H.of_le (mod_cast hm), fun H x hx m hm => H m hm x hx m le_rfl⟩

Depends on / 依赖: H.of_le, le_rfl, mod_cast, of_le
-/
theorem contDiffOn_iff_forall_nat_le {n : Nat∞} :
    ContDiffOn 𝕜 n f s ↔ forall m : Nat, ↑m <= n -> ContDiffOn 𝕜 m f s :=
  ⟨fun H _ hm => H.of_le (mod_cast hm), fun H x hx m hm => H m hm x hx m le_rfl⟩

/--
theorem `contDiffOn_infty` / 定理 `contDiffOn_infty`

English:
theorem contDiffOn_infty
  statement: ContDiffOn 𝕜 ∞ f s ↔ forall n : Nat, ContDiffOn 𝕜 n f s
  proof: contDiffOn_iff_forall_nat_le.trans by simp only [le_top, forall_prop_of_true]

中文:
定理 contDiffOn_infty
  结论: ContDiffOn 𝕜 ∞ f s ↔ 对任意 n : 自然数, ContDiffOn 𝕜 n f s
  证明: contDiffOn_iff_forall_nat_le.trans by simp only [le_top, forall_prop_of_true]

Depends on / 依赖: contDiffOn_iff_forall_nat_le, contDiffOn_iff_forall_nat_le.trans, forall_prop_of_true, le_top
-/
theorem contDiffOn_infty : ContDiffOn 𝕜 ∞ f s ↔ forall n : Nat, ContDiffOn 𝕜 n f s :=
contDiffOn_iff_forall_nat_le.trans by simp only [le_top, forall_prop_of_true]

/--
theorem `contDiffOn_all_iff_nat` / 定理 `contDiffOn_all_iff_nat`

English:
theorem contDiffOn_all_iff_nat
  proof: by
  refine ⟨fun H n => H n, ?_⟩
  rintro H (_ | n)
  exacts [contDiffOn_infty.2 H, H n]

中文:
定理 contDiffOn_all_iff_nat
  证明: by
  refine ⟨fun H n => H n, ?_⟩
  rintro H (_ | n)
  exacts [contDiffOn_infty.2 H, H n]

Depends on / 依赖: contDiffOn_infty, exacts
-/
theorem contDiffOn_all_iff_nat :
    (forall (n : Nat∞), ContDiffOn 𝕜 n f s) ↔ forall n : Nat, ContDiffOn 𝕜 n f s := by
  refine ⟨fun H n => H n, ?_⟩
  rintro H (_ | n)
  exacts [contDiffOn_infty.2 H, H n]

/--
theorem `ContDiffOn.continuousOn` / 定理 `ContDiffOn.continuousOn`

English:
theorem ContDiffOn.continuousOn
  given: (h : ContDiffOn 𝕜 n f s)
  statement: ContinuousOn f s
  proof: fun x hx =>
  (h x hx).continuousWithinAt

@[fun_prop]

中文:
定理 ContDiffOn.continuousOn
  条件: (h : ContDiffOn 𝕜 n f s)
  结论: ContinuousOn f s
  证明: fun x hx =>
  (h x hx).continuousWithinAt

@[fun_prop]
-/
theorem ContDiffOn.continuousOn (h : ContDiffOn 𝕜 n f s) : ContinuousOn f s := fun x hx =>
  (h x hx).continuousWithinAt

@[fun_prop]
/--
theorem `ContDiffOn.continuousOn_zero` / 定理 `ContDiffOn.continuousOn_zero`

English:
theorem ContDiffOn.continuousOn_zero
  given: (h : ContDiffOn 𝕜 0 f s)
  statement: ContinuousOn f s
  proof: fun x hx =>
  (h x hx).continuousWithinAt

中文:
定理 ContDiffOn.continuousOn_zero
  条件: (h : ContDiffOn 𝕜 0 f s)
  结论: ContinuousOn f s
  证明: fun x hx =>
  (h x hx).continuousWithinAt
-/
theorem ContDiffOn.continuousOn_zero (h : ContDiffOn 𝕜 0 f s) : ContinuousOn f s := fun x hx =>
  (h x hx).continuousWithinAt

/--
theorem `ContDiffOn.congr` / 定理 `ContDiffOn.congr`

English:
theorem ContDiffOn.congr
  given: (h : ContDiffOn 𝕜 n f s) (h₁ : forall x in s, f₁ x = f x)
  proof: fun x hx => (h x hx).congr h₁ (h₁ x hx)

中文:
定理 ContDiffOn.congr
  条件: (h : ContDiffOn 𝕜 n f s) (h₁ : 对任意 x in s, f₁ x = f x)
  证明: fun x hx => (h x hx).congr h₁ (h₁ x hx)
-/
theorem ContDiffOn.congr (h : ContDiffOn 𝕜 n f s) (h₁ : forall x in s, f₁ x = f x) :
    ContDiffOn 𝕜 n f₁ s := fun x hx => (h x hx).congr h₁ (h₁ x hx)

/--
theorem `contDiffOn_congr` / 定理 `contDiffOn_congr`

English:
theorem contDiffOn_congr
  given: (h₁ : forall x in s, f₁ x = f x)
  statement: ContDiffOn 𝕜 n f₁ s ↔ ContDiffOn 𝕜 n f s
  proof: ⟨fun H => H.congr fun x hx => (h₁ x hx).symm, fun H => H.congr h₁⟩

中文:
定理 contDiffOn_congr
  条件: (h₁ : 对任意 x in s, f₁ x = f x)
  结论: ContDiffOn 𝕜 n f₁ s ↔ ContDiffOn 𝕜 n f s
  证明: ⟨fun H => H.congr fun x hx => (h₁ x hx).symm, fun H => H.congr h₁⟩

Depends on / 依赖: H.congr
-/
theorem contDiffOn_congr (h₁ : forall x in s, f₁ x = f x) : ContDiffOn 𝕜 n f₁ s ↔ ContDiffOn 𝕜 n f s :=
  ⟨fun H => H.congr fun x hx => (h₁ x hx).symm, fun H => H.congr h₁⟩

/--
theorem `ContDiffOn.mono` / 定理 `ContDiffOn.mono`

English:
theorem ContDiffOn.mono
  given: (h : ContDiffOn 𝕜 n f s) {t : Set E} (hst : t subseteq s)
  statement: ContDiffOn 𝕜 n f t
  proof: fun x hx => (h x (hst hx)).mono hst

中文:
定理 ContDiffOn.mono
  条件: (h : ContDiffOn 𝕜 n f s) {t : 集合 E} (hst : t subseteq s)
  结论: ContDiffOn 𝕜 n f t
  证明: fun x hx => (h x (hst hx)).mono hst
-/
theorem ContDiffOn.mono (h : ContDiffOn 𝕜 n f s) {t : Set E} (hst : t subseteq s) : ContDiffOn 𝕜 n f t :=
  fun x hx => (h x (hst hx)).mono hst

/--
theorem `ContDiffOn.congr_mono` / 定理 `ContDiffOn.congr_mono`

English:
theorem ContDiffOn.congr_mono
  given: (hf : ContDiffOn 𝕜 n f s) (h₁ : forall x in s₁, f₁ x = f x) (hs : s₁ subseteq s)
  proof: (hf.mono hs).congr h₁

中文:
定理 ContDiffOn.congr_mono
  条件: (hf : ContDiffOn 𝕜 n f s) (h₁ : 对任意 x in s₁, f₁ x = f x) (hs : s₁ subseteq s)
  证明: (hf.mono hs).congr h₁

Depends on / 依赖: hf.mono
-/
theorem ContDiffOn.congr_mono (hf : ContDiffOn 𝕜 n f s) (h₁ : forall x in s₁, f₁ x = f x) (hs : s₁ subseteq s) :
    ContDiffOn 𝕜 n f₁ s₁ :=
  (hf.mono hs).congr h₁

/--
theorem `ContDiffOn.differentiableOn` / 定理 `ContDiffOn.differentiableOn`

English:
theorem ContDiffOn.differentiableOn
  given: (h : ContDiffOn 𝕜 n f s) (hn : n != 0)
  proof: fun x hx => (h x hx).differentiableWithinAt hn

@[fun_prop]

中文:
定理 ContDiffOn.differentiableOn
  条件: (h : ContDiffOn 𝕜 n f s) (hn : n != 0)
  证明: fun x hx => (h x hx).differentiableWithinAt hn

@[fun_prop]

Depends on / 依赖: differentiableWithinAt
-/
theorem ContDiffOn.differentiableOn (h : ContDiffOn 𝕜 n f s) (hn : n != 0) :
    DifferentiableOn 𝕜 f s := fun x hx => (h x hx).differentiableWithinAt hn

@[fun_prop]
/--
theorem `ContDiffOn.differentiableOn_one` / 定理 `ContDiffOn.differentiableOn_one`

English:
theorem ContDiffOn.differentiableOn_one
  given: (h : ContDiffOn 𝕜 1 f s)
  proof: fun x hx => (h x hx).differentiableWithinAt one_ne_zero

中文:
定理 ContDiffOn.differentiableOn_one
  条件: (h : ContDiffOn 𝕜 1 f s)
  证明: fun x hx => (h x hx).differentiableWithinAt one_ne_zero

Depends on / 依赖: differentiableWithinAt, one_ne_zero
-/
theorem ContDiffOn.differentiableOn_one (h : ContDiffOn 𝕜 1 f s) :
    DifferentiableOn 𝕜 f s := fun x hx => (h x hx).differentiableWithinAt one_ne_zero

/--
theorem `contDiffOn_of_locally_contDiffOn` / 定理 `contDiffOn_of_locally_contDiffOn`

English:
theorem contDiffOn_of_locally_contDiffOn
  proof: by
  intro x xs
  rcases h x xs with ⟨u, u_open, xu, hu⟩
  apply (contDiffWithinAt_inter _).1 (hu x ⟨xs, xu⟩)
  exact IsOpen.mem_nhds u_open xu

中文:
定理 contDiffOn_of_locally_contDiffOn
  证明: by
  intro x xs
  rcases h x xs with ⟨u, u_open, xu, hu⟩
  apply (contDiffWithinAt_inter _).1 (hu x ⟨xs, xu⟩)
  exact IsOpen.mem_nhds u_open xu

Depends on / 依赖: IsOpen, IsOpen.mem_nhds, contDiffWithinAt_inter, mem_nhds, u_open
-/
theorem contDiffOn_of_locally_contDiffOn
    (h : forall x in s, exists u, IsOpen u ∧ x in u ∧ ContDiffOn 𝕜 n f (s inter u)) : ContDiffOn 𝕜 n f s := by
  intro x xs
  rcases h x xs with ⟨u, u_open, xu, hu⟩
  apply (contDiffWithinAt_inter _).1 (hu x ⟨xs, xu⟩)
  exact IsOpen.mem_nhds u_open xu

/--
theorem `contDiffOn_succ_iff_hasFDerivWithinAt` / 定理 `contDiffOn_succ_iff_hasFDerivWithinAt`

English:
theorem contDiffOn_succ_iff_hasFDerivWithinAt
  given: (hn : n != ∞)
  proof: by
  constructor
  · intro h x hx
    rcases (contDiffWithinAt_succ_iff_hasFDerivWithinAt hn).1 (h x hx) with
      ⟨u, hu, f_an, f', hf', Hf'⟩
    rcases Hf'.contDiffOn le_rfl (by simp [hn]) with ⟨v, vu, v'u, hv⟩
    rw [insert_eq_of_mem hx] at hu ⊢
    have xu : x in u := mem_of_mem_nhdsWithin hx hu
    rw [insert_eq_of_mem xu] at vu v'u
    exact ⟨v, nhdsWithin_le_of_mem hu vu, fun h => (f_an h).mono v'u, f',
      fun y hy => (hf' y (v'u hy)).mono v'u, hv⟩
  · intro h x hx
    rw [contDiffWithinAt_succ_iff_hasFDerivWithinAt hn]
    rcases h x hx with ⟨u, u_nhbd, f_an, f', hu, hf'⟩
    have : x in u := mem_of_mem_nhdsWithin (mem_insert _ _) u_nhbd
    exact ⟨u, u_nhbd, f_an, f', hu, hf' x this⟩

中文:
定理 contDiffOn_succ_iff_hasFDerivWithinAt
  条件: (hn : n != ∞)
  证明: by
  constructor
  · intro h x hx
    rcases (contDiffWithinAt_succ_iff_hasFDerivWithinAt hn).1 (h x hx) with
      ⟨u, hu, f_an, f', hf', Hf'⟩
    rcases Hf'.contDiffOn le_rfl (by simp [hn]) with ⟨v, vu, v'u, hv⟩
    rw [insert_eq_of_mem hx] at hu ⊢
    have xu : x in u := mem_of_mem_nhdsWithin hx hu
    rw [insert_eq_of_mem xu] at vu v'u
    exact ⟨v, nhdsWithin_le_of_mem hu vu, fun h => (f_an h).mono v'u, f',
      fun y hy => (hf' y (v'u hy)).mono v'u, hv⟩
  · intro h x hx
    rw [contDiffWithinAt_succ_iff_hasFDerivWithinAt hn]
    rcases h x hx with ⟨u, u_nhbd, f_an, f', hu, hf'⟩
    have : x in u := mem_of_mem_nhdsWithin (mem_insert _ _) u_nhbd
    exact ⟨u, u_nhbd, f_an, f', hu, hf' x this⟩

Depends on / 依赖: contDiffOn, contDiffWithinAt_succ_iff_hasFDerivWithinAt, f_an, insert_eq_of_mem, le_rfl, mem_of_mem_nhdsWithin, nhdsWithin_le_of_mem
-/
theorem contDiffOn_succ_iff_hasFDerivWithinAt (hn : n != ∞) :
    ContDiffOn 𝕜 (n + 1) f s ↔
      forall x in s, exists u in 𝓝[insert x s] x, (n = ω -> AnalyticOn 𝕜 f u) ∧ exists f' : E -> E ->L[𝕜] F,
        (forall x in u, HasFDerivWithinAt f (f' x) u x) ∧ ContDiffOn 𝕜 n f' u := by
  constructor
  · intro h x hx
    rcases (contDiffWithinAt_succ_iff_hasFDerivWithinAt hn).1 (h x hx) with
      ⟨u, hu, f_an, f', hf', Hf'⟩
    rcases Hf'.contDiffOn le_rfl (by simp [hn]) with ⟨v, vu, v'u, hv⟩
    rw [insert_eq_of_mem hx] at hu ⊢
    have xu : x in u := mem_of_mem_nhdsWithin hx hu
    rw [insert_eq_of_mem xu] at vu v'u
    exact ⟨v, nhdsWithin_le_of_mem hu vu, fun h => (f_an h).mono v'u, f',
      fun y hy => (hf' y (v'u hy)).mono v'u, hv⟩
  · intro h x hx
    rw [contDiffWithinAt_succ_iff_hasFDerivWithinAt hn]
    rcases h x hx with ⟨u, u_nhbd, f_an, f', hu, hf'⟩
    have : x in u := mem_of_mem_nhdsWithin (mem_insert _ _) u_nhbd
    exact ⟨u, u_nhbd, f_an, f', hu, hf' x this⟩


/-! ### Iterated derivative within a set -/

@[simp]
/--
theorem `contDiffOn_zero` / 定理 `contDiffOn_zero`

English:
theorem contDiffOn_zero
  statement: ContDiffOn 𝕜 0 f s ↔ ContinuousOn f s
  proof: by
  refine ⟨fun H => H.continuousOn, fun H => fun x hx m hm => ?_⟩
  have : (m : Nat∞ω) = 0 := le_antisymm (mod_cast hm) bot_le
  rw [this]
  refine ⟨insert x s, self_mem_nhdsWithin, ftaylorSeriesWithin 𝕜 f s, ?_⟩
  rw [hasFTaylorSeriesUpToOn_zero_iff]
  exact ⟨by rwa [insert_eq_of_mem hx], fun x _ => by simp [ftaylorSeriesWithin]⟩

中文:
定理 contDiffOn_zero
  结论: ContDiffOn 𝕜 0 f s ↔ ContinuousOn f s
  证明: by
  refine ⟨fun H => H.continuousOn, fun H => fun x hx m hm => ?_⟩
  have : (m : Nat∞ω) = 0 := le_antisymm (mod_cast hm) bot_le
  rw [this]
  refine ⟨insert x s, self_mem_nhdsWithin, ftaylorSeriesWithin 𝕜 f s, ?_⟩
  rw [hasFTaylorSeriesUpToOn_zero_iff]
  exact ⟨by rwa [insert_eq_of_mem hx], fun x _ => by simp [ftaylorSeriesWithin]⟩

Depends on / 依赖: H.continuousOn, bot_le, continuousOn, ftaylorSeriesWithin, hasFTaylorSeriesUpToOn_zero_iff, insert, insert_eq_of_mem, le_antisymm, mod_cast, self_mem_nhdsWithin
-/
theorem contDiffOn_zero : ContDiffOn 𝕜 0 f s ↔ ContinuousOn f s := by
  refine ⟨fun H => H.continuousOn, fun H => fun x hx m hm => ?_⟩
  have : (m : Nat∞ω) = 0 := le_antisymm (mod_cast hm) bot_le
  rw [this]
  refine ⟨insert x s, self_mem_nhdsWithin, ftaylorSeriesWithin 𝕜 f s, ?_⟩
  rw [hasFTaylorSeriesUpToOn_zero_iff]
  exact ⟨by rwa [insert_eq_of_mem hx], fun x _ => by simp [ftaylorSeriesWithin]⟩

/--
theorem `contDiffWithinAt_zero` / 定理 `contDiffWithinAt_zero`

English:
theorem contDiffWithinAt_zero
  given: (hx : x in s)
  proof: by
  constructor
  · intro h
    obtain ⟨u, H, p, hp⟩ := h 0 le_rfl
    refine ⟨u, ?_, ?_⟩
    · simpa [hx] using H
    · simp only [Nat.cast_zero, hasFTaylorSeriesUpToOn_zero_iff] at hp
      exact hp.1.mono inter_subset_right
  · rintro ⟨u, H, hu⟩
    rw [← contDiffWithinAt_inter' H]
    have h' : x in s inter u := ⟨hx, mem_of_mem_nhdsWithin hx H⟩
    exact (contDiffOn_zero.mpr hu).contDiffWithinAt h'

中文:
定理 contDiffWithinAt_zero
  条件: (hx : x in s)
  证明: by
  constructor
  · intro h
    obtain ⟨u, H, p, hp⟩ := h 0 le_rfl
    refine ⟨u, ?_, ?_⟩
    · simpa [hx] using H
    · simp only [Nat.cast_zero, hasFTaylorSeriesUpToOn_zero_iff] at hp
      exact hp.1.mono inter_subset_right
  · rintro ⟨u, H, hu⟩
    rw [← contDiffWithinAt_inter' H]
    have h' : x in s inter u := ⟨hx, mem_of_mem_nhdsWithin hx H⟩
    exact (contDiffOn_zero.mpr hu).contDiffWithinAt h'

Depends on / 依赖: Nat.cast_zero, cast_zero, contDiffOn_zero, contDiffOn_zero.mpr, contDiffWithinAt, contDiffWithinAt_inter, hasFTaylorSeriesUpToOn_zero_iff, inter_subset_right, le_rfl, mem_of_mem_nhdsWithin
-/
theorem contDiffWithinAt_zero (hx : x in s) :
    ContDiffWithinAt 𝕜 0 f s x ↔ exists u in 𝓝[s] x, ContinuousOn f (s inter u) := by
  constructor
  · intro h
    obtain ⟨u, H, p, hp⟩ := h 0 le_rfl
    refine ⟨u, ?_, ?_⟩
    · simpa [hx] using H
    · simp only [Nat.cast_zero, hasFTaylorSeriesUpToOn_zero_iff] at hp
      exact hp.1.mono inter_subset_right
  · rintro ⟨u, H, hu⟩
    rw [← contDiffWithinAt_inter' H]
    have h' : x in s inter u := ⟨hx, mem_of_mem_nhdsWithin hx H⟩
    exact (contDiffOn_zero.mpr hu).contDiffWithinAt h'

/--
theorem `ContDiffOn.ftaylorSeriesWithin` / 定理 `ContDiffOn.ftaylorSeriesWithin`

English:
theorem ContDiffOn.ftaylorSeriesWithin
  proof: by
  constructor
  · intro x _
    simp only [ftaylorSeriesWithin, ContinuousMultilinearMap.curry0_apply,
      iteratedFDerivWithin_zero_apply]
  · intro m hm x hx
    have : (m + 1 : Nat) <= n := ENat.add_one_natCast_le_withTop_of_lt hm
    rcases (h x hx).of_le this _ le_rfl with ⟨u, hu, p, Hp⟩
    rw [insert_eq_of_mem hx] at hu
    rcases mem_nhdsWithin.1 hu with ⟨o, o_open, xo, ho⟩
    rw [inter_comm] at ho
    have : p x m.succ = ftaylorSeriesWithin 𝕜 f s x m.succ := by
      change p x m.succ = iteratedFDerivWithin 𝕜 m.succ f s x
      rw [← iteratedFDerivWithin_inter_open o_open xo]
      exact (Hp.mono ho).eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl (hs.inter o_open) ⟨hx, xo⟩
    rw [← this]; rw [← hasFDerivWithinAt_inter (IsOpen.mem_nhds o_open xo)]
    have A : forall y in s inter o, p y m = ftaylorSeriesWithin 𝕜 f s y m := by
      rintro y ⟨hy, yo⟩
      change p y m = iteratedFDerivWithin 𝕜 m f s y
      rw [← iteratedFDerivWithin_inter_open o_open yo]
      exact
        (Hp.mono ho).eq_iteratedFDerivWithin_of_uniqueDiffOn (mod_cast Nat.le_succ m)
          (hs.inter o_open) ⟨hy, yo⟩
    exact
      ((Hp.mono ho).fderivWithin m (mod_cast lt_add_one m) x ⟨hx, xo⟩).congr
        (fun y hy => (A y hy).symm) (A x ⟨hx, xo⟩).symm
  · intro m hm
    apply continuousOn_of_locally_continuousOn
    intro x hx
    rcases (h x hx).of_le hm _ le_rfl with ⟨u, hu, p, Hp⟩
    rcases mem_nhdsWithin.1 hu with ⟨o, o_open, xo, ho⟩
    rw [insert_eq_of_mem hx] at ho
    rw [inter_comm] at ho
    refine ⟨o, o_open, xo, ?_⟩
    have A : forall y in s inter o, p y m = ftaylorSeriesWithin 𝕜 f s y m := by
      rintro y ⟨hy, yo⟩
      change p y m = iteratedFDerivWithin 𝕜 m f s y
      rw [← iteratedFDerivWithin_inter_open o_open yo]
      exact (Hp.mono ho).eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl (hs.inter o_open) ⟨hy, yo⟩
    exact ((Hp.mono ho).cont m le_rfl).congr fun y hy => (A y hy).symm

中文:
定理 ContDiffOn.ftaylorSeriesWithin
  证明: by
  constructor
  · intro x _
    simp only [ftaylorSeriesWithin, ContinuousMultilinearMap.curry0_apply,
      iteratedFDerivWithin_zero_apply]
  · intro m hm x hx
    have : (m + 1 : Nat) <= n := ENat.add_one_natCast_le_withTop_of_lt hm
    rcases (h x hx).of_le this _ le_rfl with ⟨u, hu, p, Hp⟩
    rw [insert_eq_of_mem hx] at hu
    rcases mem_nhdsWithin.1 hu with ⟨o, o_open, xo, ho⟩
    rw [inter_comm] at ho
    have : p x m.succ = ftaylorSeriesWithin 𝕜 f s x m.succ := by
      change p x m.succ = iteratedFDerivWithin 𝕜 m.succ f s x
      rw [← iteratedFDerivWithin_inter_open o_open xo]
      exact (Hp.mono ho).eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl (hs.inter o_open) ⟨hx, xo⟩
    rw [← this]; rw [← hasFDerivWithinAt_inter (IsOpen.mem_nhds o_open xo)]
    have A : forall y in s inter o, p y m = ftaylorSeriesWithin 𝕜 f s y m := by
      rintro y ⟨hy, yo⟩
      change p y m = iteratedFDerivWithin 𝕜 m f s y
      rw [← iteratedFDerivWithin_inter_open o_open yo]
      exact
        (Hp.mono ho).eq_iteratedFDerivWithin_of_uniqueDiffOn (mod_cast Nat.le_succ m)
          (hs.inter o_open) ⟨hy, yo⟩
    exact
      ((Hp.mono ho).fderivWithin m (mod_cast lt_add_one m) x ⟨hx, xo⟩).congr
        (fun y hy => (A y hy).symm) (A x ⟨hx, xo⟩).symm
  · intro m hm
    apply continuousOn_of_locally_continuousOn
    intro x hx
    rcases (h x hx).of_le hm _ le_rfl with ⟨u, hu, p, Hp⟩
    rcases mem_nhdsWithin.1 hu with ⟨o, o_open, xo, ho⟩
    rw [insert_eq_of_mem hx] at ho
    rw [inter_comm] at ho
    refine ⟨o, o_open, xo, ?_⟩
    have A : forall y in s inter o, p y m = ftaylorSeriesWithin 𝕜 f s y m := by
      rintro y ⟨hy, yo⟩
      change p y m = iteratedFDerivWithin 𝕜 m f s y
      rw [← iteratedFDerivWithin_inter_open o_open yo]
      exact (Hp.mono ho).eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl (hs.inter o_open) ⟨hy, yo⟩
    exact ((Hp.mono ho).cont m le_rfl).congr fun y hy => (A y hy).symm
-/
protected theorem ContDiffOn.ftaylorSeriesWithin
    (h : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s) :
    HasFTaylorSeriesUpToOn n f (ftaylorSeriesWithin 𝕜 f s) s := by
  constructor
  · intro x _
    simp only [ftaylorSeriesWithin, ContinuousMultilinearMap.curry0_apply,
      iteratedFDerivWithin_zero_apply]
  · intro m hm x hx
    have : (m + 1 : Nat) <= n := ENat.add_one_natCast_le_withTop_of_lt hm
    rcases (h x hx).of_le this _ le_rfl with ⟨u, hu, p, Hp⟩
    rw [insert_eq_of_mem hx] at hu
    rcases mem_nhdsWithin.1 hu with ⟨o, o_open, xo, ho⟩
    rw [inter_comm] at ho
    have : p x m.succ = ftaylorSeriesWithin 𝕜 f s x m.succ := by
      change p x m.succ = iteratedFDerivWithin 𝕜 m.succ f s x
      rw [← iteratedFDerivWithin_inter_open o_open xo]
      exact (Hp.mono ho).eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl (hs.inter o_open) ⟨hx, xo⟩
    rw [← this]; rw [← hasFDerivWithinAt_inter (IsOpen.mem_nhds o_open xo)]
    have A : forall y in s inter o, p y m = ftaylorSeriesWithin 𝕜 f s y m := by
      rintro y ⟨hy, yo⟩
      change p y m = iteratedFDerivWithin 𝕜 m f s y
      rw [← iteratedFDerivWithin_inter_open o_open yo]
      exact
        (Hp.mono ho).eq_iteratedFDerivWithin_of_uniqueDiffOn (mod_cast Nat.le_succ m)
          (hs.inter o_open) ⟨hy, yo⟩
    exact
      ((Hp.mono ho).fderivWithin m (mod_cast lt_add_one m) x ⟨hx, xo⟩).congr
        (fun y hy => (A y hy).symm) (A x ⟨hx, xo⟩).symm
  · intro m hm
    apply continuousOn_of_locally_continuousOn
    intro x hx
    rcases (h x hx).of_le hm _ le_rfl with ⟨u, hu, p, Hp⟩
    rcases mem_nhdsWithin.1 hu with ⟨o, o_open, xo, ho⟩
    rw [insert_eq_of_mem hx] at ho
    rw [inter_comm] at ho
    refine ⟨o, o_open, xo, ?_⟩
    have A : forall y in s inter o, p y m = ftaylorSeriesWithin 𝕜 f s y m := by
      rintro y ⟨hy, yo⟩
      change p y m = iteratedFDerivWithin 𝕜 m f s y
      rw [← iteratedFDerivWithin_inter_open o_open yo]
      exact (Hp.mono ho).eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl (hs.inter o_open) ⟨hy, yo⟩
    exact ((Hp.mono ho).cont m le_rfl).congr fun y hy => (A y hy).symm

/--
theorem `iteratedFDerivWithin_subset` / 定理 `iteratedFDerivWithin_subset`

English:
theorem iteratedFDerivWithin_subset
  statement: {n : Nat} (st : s subseteq t) (hs : UniqueDiffOn 𝕜 s)
  proof: (((h.ftaylorSeriesWithin ht).mono st).eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl hs hx).symm

中文:
定理 iteratedFDerivWithin_subset
  结论: {n : 自然数} (st : s subseteq t) (hs : UniqueDiffOn 𝕜 s)
  证明: (((h.ftaylorSeriesWithin ht).mono st).eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl hs hx).symm

Depends on / 依赖: eq_iteratedFDerivWithin_of_uniqueDiffOn, ftaylorSeriesWithin, h.ftaylorSeriesWithin, le_rfl
-/
theorem iteratedFDerivWithin_subset {n : Nat} (st : s subseteq t) (hs : UniqueDiffOn 𝕜 s)
    (ht : UniqueDiffOn 𝕜 t) (h : ContDiffOn 𝕜 n f t) (hx : x in s) :
    iteratedFDerivWithin 𝕜 n f s x = iteratedFDerivWithin 𝕜 n f t x :=
  (((h.ftaylorSeriesWithin ht).mono st).eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl hs hx).symm

/--
theorem `ContDiffWithinAt.eventually_hasFTaylorSeriesUpToOn` / 定理 `ContDiffWithinAt.eventually_hasFTaylorSeriesUpToOn`

English:
theorem ContDiffWithinAt.eventually_hasFTaylorSeriesUpToOn
  statement: {f : E -> F} {s : Set E} {a : E}
  proof: by
  rcases h.contDiffOn' hm (by simp) with ⟨U, hUo, haU, hfU⟩
  have : forallᶠ t in (𝓝[s] a).smallSets, t subseteq s inter U := by
    rw [eventually_smallSets_subset]
exact inter_mem_nhdsWithin _ hUo.mem_nhds haU
  refine this.mono fun t ht => .mono ?_ ht
  rw [insert_eq_of_mem ha] at hfU
  refine (hfU.ftaylorSeriesWithin (hs.inter hUo)).congr_series fun k hk x hx => ?_
  exact iteratedFDerivWithin_inter_open hUo hx.2

中文:
定理 ContDiffWithinAt.eventually_hasFTaylorSeriesUpToOn
  结论: {f : E -> F} {s : 集合 E} {a : E}
  证明: by
  rcases h.contDiffOn' hm (by simp) with ⟨U, hUo, haU, hfU⟩
  have : forallᶠ t in (𝓝[s] a).smallSets, t subseteq s inter U := by
    rw [eventually_smallSets_subset]
exact inter_mem_nhdsWithin _ hUo.mem_nhds haU
  refine this.mono fun t ht => .mono ?_ ht
  rw [insert_eq_of_mem ha] at hfU
  refine (hfU.ftaylorSeriesWithin (hs.inter hUo)).congr_series fun k hk x hx => ?_
  exact iteratedFDerivWithin_inter_open hUo hx.2

Depends on / 依赖: congr_series, contDiffOn, eventually_smallSets_subset, ftaylorSeriesWithin, h.contDiffOn, hUo.mem_nhds, hfU.ftaylorSeriesWithin, hs.inter, insert_eq_of_mem, inter_mem_nhdsWithin, iteratedFDerivWithin_inter_open, mem_nhds, smallSets, subseteq, this.mono
-/
theorem ContDiffWithinAt.eventually_hasFTaylorSeriesUpToOn {f : E -> F} {s : Set E} {a : E}
    (h : ContDiffWithinAt 𝕜 n f s a) (hs : UniqueDiffOn 𝕜 s) (ha : a in s) {m : Nat} (hm : m <= n) :
    forallᶠ t in (𝓝[s] a).smallSets, HasFTaylorSeriesUpToOn m f (ftaylorSeriesWithin 𝕜 f s) t := by
  rcases h.contDiffOn' hm (by simp) with ⟨U, hUo, haU, hfU⟩
  have : forallᶠ t in (𝓝[s] a).smallSets, t subseteq s inter U := by
    rw [eventually_smallSets_subset]
exact inter_mem_nhdsWithin _ hUo.mem_nhds haU
  refine this.mono fun t ht => .mono ?_ ht
  rw [insert_eq_of_mem ha] at hfU
  refine (hfU.ftaylorSeriesWithin (hs.inter hUo)).congr_series fun k hk x hx => ?_
  exact iteratedFDerivWithin_inter_open hUo hx.2

/--
theorem `AnalyticOn.contDiffOn` / 定理 `AnalyticOn.contDiffOn`

English:
theorem AnalyticOn.contDiffOn
  given: (h : AnalyticOn 𝕜 f s) (hs : UniqueDiffOn 𝕜 s)
  proof: by
  suffices ContDiffOn 𝕜 ω f s from this.of_le le_top
  rcases h.exists_hasFTaylorSeriesUpToOn hs with ⟨p, hp⟩
  intro x hx
  refine ⟨s, ?_, p, hp⟩
  rw [insert_eq_of_mem hx]
  exact self_mem_nhdsWithin

中文:
定理 AnalyticOn.contDiffOn
  条件: (h : AnalyticOn 𝕜 f s) (hs : UniqueDiffOn 𝕜 s)
  证明: by
  suffices ContDiffOn 𝕜 ω f s from this.of_le le_top
  rcases h.exists_hasFTaylorSeriesUpToOn hs with ⟨p, hp⟩
  intro x hx
  refine ⟨s, ?_, p, hp⟩
  rw [insert_eq_of_mem hx]
  exact self_mem_nhdsWithin

Depends on / 依赖: ContDiffOn, exists_hasFTaylorSeriesUpToOn, h.exists_hasFTaylorSeriesUpToOn, insert_eq_of_mem, le_top, of_le, self_mem_nhdsWithin, this.of_le
-/
theorem AnalyticOn.contDiffOn (h : AnalyticOn 𝕜 f s) (hs : UniqueDiffOn 𝕜 s) :
    ContDiffOn 𝕜 n f s := by
  suffices ContDiffOn 𝕜 ω f s from this.of_le le_top
  rcases h.exists_hasFTaylorSeriesUpToOn hs with ⟨p, hp⟩
  intro x hx
  refine ⟨s, ?_, p, hp⟩
  rw [insert_eq_of_mem hx]
  exact self_mem_nhdsWithin

/--
theorem `AnalyticOnNhd.contDiffOn` / 定理 `AnalyticOnNhd.contDiffOn`

English:
theorem AnalyticOnNhd.contDiffOn
  given: (h : AnalyticOnNhd 𝕜 f s) (hs : UniqueDiffOn 𝕜 s)
  proof: h.analyticOn.contDiffOn hs

中文:
定理 AnalyticOnNhd.contDiffOn
  条件: (h : AnalyticOnNhd 𝕜 f s) (hs : UniqueDiffOn 𝕜 s)
  证明: h.analyticOn.contDiffOn hs

Depends on / 依赖: analyticOn, contDiffOn, h.analyticOn.contDiffOn
-/
theorem AnalyticOnNhd.contDiffOn (h : AnalyticOnNhd 𝕜 f s) (hs : UniqueDiffOn 𝕜 s) :
    ContDiffOn 𝕜 n f s := h.analyticOn.contDiffOn hs

/--
theorem `AnalyticOn.contDiffOn_of_completeSpace` / 定理 `AnalyticOn.contDiffOn_of_completeSpace`

English:
theorem AnalyticOn.contDiffOn_of_completeSpace
  given: [CompleteSpace F] (h : AnalyticOn 𝕜 f s)
  proof: fun x hx => (h x hx).contDiffWithinAt

中文:
定理 AnalyticOn.contDiffOn_of_completeSpace
  条件: [完备空间 F] (h : AnalyticOn 𝕜 f s)
  证明: fun x hx => (h x hx).contDiffWithinAt

Depends on / 依赖: contDiffWithinAt
-/
theorem AnalyticOn.contDiffOn_of_completeSpace [CompleteSpace F] (h : AnalyticOn 𝕜 f s) :
    ContDiffOn 𝕜 n f s :=
  fun x hx => (h x hx).contDiffWithinAt

/--
theorem `AnalyticOnNhd.contDiffOn_of_completeSpace` / 定理 `AnalyticOnNhd.contDiffOn_of_completeSpace`

English:
theorem AnalyticOnNhd.contDiffOn_of_completeSpace
  given: [CompleteSpace F] (h : AnalyticOnNhd 𝕜 f s)
  proof: h.analyticOn.contDiffOn_of_completeSpace

中文:
定理 AnalyticOnNhd.contDiffOn_of_completeSpace
  条件: [完备空间 F] (h : AnalyticOnNhd 𝕜 f s)
  证明: h.analyticOn.contDiffOn_of_completeSpace

Depends on / 依赖: analyticOn, contDiffOn_of_completeSpace, h.analyticOn.contDiffOn_of_completeSpace
-/
theorem AnalyticOnNhd.contDiffOn_of_completeSpace [CompleteSpace F] (h : AnalyticOnNhd 𝕜 f s) :
    ContDiffOn 𝕜 n f s :=
  h.analyticOn.contDiffOn_of_completeSpace

/--
theorem `contDiffOn_of_continuousOn_differentiableOn` / 定理 `contDiffOn_of_continuousOn_differentiableOn`

English:
theorem contDiffOn_of_continuousOn_differentiableOn
  statement: {n : Nat∞}
  proof: by
  intro x hx m hm
  rw [insert_eq_of_mem hx]
  refine ⟨s, self_mem_nhdsWithin, ftaylorSeriesWithin 𝕜 f s, ?_⟩
  constructor
  · intro y _
    simp only [ftaylorSeriesWithin, ContinuousMultilinearMap.curry0_apply,
      iteratedFDerivWithin_zero_apply]
  · intro k hk y hy
    convert! (Hdiff k (lt_of_lt_of_le (mod_cast hk) (mod_cast hm)) y hy).hasFDerivWithinAt
  · intro k hk
    exact Hcont k (le_trans (mod_cast hk) (mod_cast hm))

中文:
定理 contDiffOn_of_continuousOn_differentiableOn
  结论: {n : 自然数∞}
  证明: by
  intro x hx m hm
  rw [insert_eq_of_mem hx]
  refine ⟨s, self_mem_nhdsWithin, ftaylorSeriesWithin 𝕜 f s, ?_⟩
  constructor
  · intro y _
    simp only [ftaylorSeriesWithin, ContinuousMultilinearMap.curry0_apply,
      iteratedFDerivWithin_zero_apply]
  · intro k hk y hy
    convert! (Hdiff k (lt_of_lt_of_le (mod_cast hk) (mod_cast hm)) y hy).hasFDerivWithinAt
  · intro k hk
    exact Hcont k (le_trans (mod_cast hk) (mod_cast hm))

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.curry0_apply, convert, curry0_apply, ftaylorSeriesWithin, hasFDerivWithinAt, insert_eq_of_mem, iteratedFDerivWithin_zero_apply, le_trans, lt_of_lt_of_le, mod_cast, self_mem_nhdsWithin
-/
theorem contDiffOn_of_continuousOn_differentiableOn {n : Nat∞}
    (Hcont : forall m : Nat, m <= n -> ContinuousOn (fun x => iteratedFDerivWithin 𝕜 m f s x) s)
    (Hdiff : forall m : Nat, m < n ->
      DifferentiableOn 𝕜 (fun x => iteratedFDerivWithin 𝕜 m f s x) s) :
    ContDiffOn 𝕜 n f s := by
  intro x hx m hm
  rw [insert_eq_of_mem hx]
  refine ⟨s, self_mem_nhdsWithin, ftaylorSeriesWithin 𝕜 f s, ?_⟩
  constructor
  · intro y _
    simp only [ftaylorSeriesWithin, ContinuousMultilinearMap.curry0_apply,
      iteratedFDerivWithin_zero_apply]
  · intro k hk y hy
    convert! (Hdiff k (lt_of_lt_of_le (mod_cast hk) (mod_cast hm)) y hy).hasFDerivWithinAt
  · intro k hk
    exact Hcont k (le_trans (mod_cast hk) (mod_cast hm))

/--
theorem `contDiffOn_of_differentiableOn` / 定理 `contDiffOn_of_differentiableOn`

English:
theorem contDiffOn_of_differentiableOn
  statement: {n : Nat∞}
  proof: contDiffOn_of_continuousOn_differentiableOn (fun m hm => (h m hm).continuousOn) fun m hm =>
    h m (le_of_lt hm)

中文:
定理 contDiffOn_of_differentiableOn
  结论: {n : 自然数∞}
  证明: contDiffOn_of_continuousOn_differentiableOn (fun m hm => (h m hm).continuousOn) fun m hm =>
    h m (le_of_lt hm)

Depends on / 依赖: contDiffOn_of_continuousOn_differentiableOn, continuousOn, le_of_lt
-/
theorem contDiffOn_of_differentiableOn {n : Nat∞}
    (h : forall m : Nat, m <= n -> DifferentiableOn 𝕜 (iteratedFDerivWithin 𝕜 m f s) s) :
    ContDiffOn 𝕜 n f s :=
  contDiffOn_of_continuousOn_differentiableOn (fun m hm => (h m hm).continuousOn) fun m hm =>
    h m (le_of_lt hm)

/--
theorem `contDiffOn_of_analyticOn_iteratedFDerivWithin` / 定理 `contDiffOn_of_analyticOn_iteratedFDerivWithin`

English:
theorem contDiffOn_of_analyticOn_iteratedFDerivWithin
  proof: by
  suffices ContDiffOn 𝕜 ω f s from this.of_le le_top
  intro x hx
  refine ⟨insert x s, self_mem_nhdsWithin, ftaylorSeriesWithin 𝕜 f s, ?_, ?_⟩
  · rw [insert_eq_of_mem hx]
    constructor
    · intro y _
      simp only [ftaylorSeriesWithin, ContinuousMultilinearMap.curry0_apply,
        iteratedFDerivWithin_zero_apply]
    · intro k _ y hy
      exact ((h k).differentiableOn y hy).hasFDerivWithinAt
    · intro k _
      exact (h k).continuousOn
  · intro i
    rw [insert_eq_of_mem hx]
    exact h i

中文:
定理 contDiffOn_of_analyticOn_iteratedFDerivWithin
  证明: by
  suffices ContDiffOn 𝕜 ω f s from this.of_le le_top
  intro x hx
  refine ⟨insert x s, self_mem_nhdsWithin, ftaylorSeriesWithin 𝕜 f s, ?_, ?_⟩
  · rw [insert_eq_of_mem hx]
    constructor
    · intro y _
      simp only [ftaylorSeriesWithin, ContinuousMultilinearMap.curry0_apply,
        iteratedFDerivWithin_zero_apply]
    · intro k _ y hy
      exact ((h k).differentiableOn y hy).hasFDerivWithinAt
    · intro k _
      exact (h k).continuousOn
  · intro i
    rw [insert_eq_of_mem hx]
    exact h i

Depends on / 依赖: ContDiffOn, ContinuousMultilinearMap, ContinuousMultilinearMap.curry0_apply, continuousOn, curry0_apply, differentiableOn, ftaylorSeriesWithin, hasFDerivWithinAt, insert, insert_eq_of_mem, iteratedFDerivWithin_zero_apply, le_top, of_le, self_mem_nhdsWithin, this.of_le
-/
theorem contDiffOn_of_analyticOn_iteratedFDerivWithin
    (h : forall m, AnalyticOn 𝕜 (iteratedFDerivWithin 𝕜 m f s) s) :
    ContDiffOn 𝕜 n f s := by
  suffices ContDiffOn 𝕜 ω f s from this.of_le le_top
  intro x hx
  refine ⟨insert x s, self_mem_nhdsWithin, ftaylorSeriesWithin 𝕜 f s, ?_, ?_⟩
  · rw [insert_eq_of_mem hx]
    constructor
    · intro y _
      simp only [ftaylorSeriesWithin, ContinuousMultilinearMap.curry0_apply,
        iteratedFDerivWithin_zero_apply]
    · intro k _ y hy
      exact ((h k).differentiableOn y hy).hasFDerivWithinAt
    · intro k _
      exact (h k).continuousOn
  · intro i
    rw [insert_eq_of_mem hx]
    exact h i

/--
theorem `contDiffOn_omega_iff_analyticOn` / 定理 `contDiffOn_omega_iff_analyticOn`

English:
theorem contDiffOn_omega_iff_analyticOn
  given: (hs : UniqueDiffOn 𝕜 s)
  proof: ⟨fun h m => h.analyticOn m, fun h => h.contDiffOn hs⟩

中文:
定理 contDiffOn_omega_iff_analyticOn
  条件: (hs : UniqueDiffOn 𝕜 s)
  证明: ⟨fun h m => h.analyticOn m, fun h => h.contDiffOn hs⟩

Depends on / 依赖: analyticOn, contDiffOn, h.analyticOn, h.contDiffOn
-/
theorem contDiffOn_omega_iff_analyticOn (hs : UniqueDiffOn 𝕜 s) :
    ContDiffOn 𝕜 ω f s ↔ AnalyticOn 𝕜 f s :=
  ⟨fun h m => h.analyticOn m, fun h => h.contDiffOn hs⟩

/--
theorem `ContDiffOn.continuousOn_iteratedFDerivWithin` / 定理 `ContDiffOn.continuousOn_iteratedFDerivWithin`

English:
theorem ContDiffOn.continuousOn_iteratedFDerivWithin
  statement: {m : Nat} (h : ContDiffOn 𝕜 n f s)
  proof: ((h.of_le hmn).ftaylorSeriesWithin hs).cont m le_rfl

中文:
定理 ContDiffOn.continuousOn_iteratedFDerivWithin
  结论: {m : 自然数} (h : ContDiffOn 𝕜 n f s)
  证明: ((h.of_le hmn).ftaylorSeriesWithin hs).cont m le_rfl

Depends on / 依赖: ftaylorSeriesWithin, h.of_le, le_rfl, of_le
-/
theorem ContDiffOn.continuousOn_iteratedFDerivWithin {m : Nat} (h : ContDiffOn 𝕜 n f s)
    (hmn : m <= n) (hs : UniqueDiffOn 𝕜 s) : ContinuousOn (iteratedFDerivWithin 𝕜 m f s) s :=
  ((h.of_le hmn).ftaylorSeriesWithin hs).cont m le_rfl

/--
theorem `ContDiffOn.differentiableOn_iteratedFDerivWithin` / 定理 `ContDiffOn.differentiableOn_iteratedFDerivWithin`

English:
theorem ContDiffOn.differentiableOn_iteratedFDerivWithin
  statement: {m : Nat} (h : ContDiffOn 𝕜 n f s)
  proof: by
  intro x hx
  have : (m + 1 : Nat) <= n := ENat.add_one_natCast_le_withTop_of_lt hmn
  apply (((h.of_le this).ftaylorSeriesWithin hs).fderivWithin m ?_ x hx).differentiableWithinAt
  exact_mod_cast lt_add_one m

中文:
定理 ContDiffOn.differentiableOn_iteratedFDerivWithin
  结论: {m : 自然数} (h : ContDiffOn 𝕜 n f s)
  证明: by
  intro x hx
  have : (m + 1 : Nat) <= n := ENat.add_one_natCast_le_withTop_of_lt hmn
  apply (((h.of_le this).ftaylorSeriesWithin hs).fderivWithin m ?_ x hx).differentiableWithinAt
  exact_mod_cast lt_add_one m

Depends on / 依赖: ENat.add_one_natCast_le_withTop_of_lt, add_one_natCast_le_withTop_of_lt, differentiableWithinAt, fderivWithin, ftaylorSeriesWithin, h.of_le, lt_add_one, of_le
-/
theorem ContDiffOn.differentiableOn_iteratedFDerivWithin {m : Nat} (h : ContDiffOn 𝕜 n f s)
    (hmn : m < n) (hs : UniqueDiffOn 𝕜 s) :
    DifferentiableOn 𝕜 (iteratedFDerivWithin 𝕜 m f s) s := by
  intro x hx
  have : (m + 1 : Nat) <= n := ENat.add_one_natCast_le_withTop_of_lt hmn
  apply (((h.of_le this).ftaylorSeriesWithin hs).fderivWithin m ?_ x hx).differentiableWithinAt
  exact_mod_cast lt_add_one m

/--
theorem `ContDiffWithinAt.differentiableWithinAt_iteratedFDerivWithin` / 定理 `ContDiffWithinAt.differentiableWithinAt_iteratedFDerivWithin`

English:
theorem ContDiffWithinAt.differentiableWithinAt_iteratedFDerivWithin
  statement: {m : Nat}
  proof: by
  have : (m + 1 : Nat∞ω) != ∞ := Ne.symm (ne_of_beq_false rfl)
  rcases h.contDiffOn' (ENat.add_one_natCast_le_withTop_of_lt hmn) (by simp [this])
    with ⟨u, uo, xu, hu⟩
  set t := insert x s inter u
  have A : t =ᶠ[𝓝[!=] x] s := by
    simp only [set_eventuallyEq_iff_inf_principal, ← nhdsWithin_inter']
    rw [← inter_assoc]; rw [nhdsWithin_inter_of_mem']; rw [← sdiff_eq_compl_inter]; rw [insert_sdiff_of_mem]; rw [sdiff_eq_compl_inter]
    exacts [rfl, mem_nhdsWithin_of_mem_nhds (uo.mem_nhds xu)]
  have B : iteratedFDerivWithin 𝕜 m f s =ᶠ[𝓝 x] iteratedFDerivWithin 𝕜 m f t :=
    iteratedFDerivWithin_eventually_congr_set' _ A.symm _
  have C : DifferentiableWithinAt 𝕜 (iteratedFDerivWithin 𝕜 m f t) t x :=
    hu.differentiableOn_iteratedFDerivWithin (Nat.cast_lt.2 m.lt_succ_self) (hs.inter uo) x
      ⟨mem_insert _ _, xu⟩
  rw [differentiableWithinAt_congr_set' _ A] at C
  exact C.congr_of_eventuallyEq (B.filter_mono inf_le_left) B.self_of_nhds

中文:
定理 ContDiffWithinAt.differentiableWithinAt_iteratedFDerivWithin
  结论: {m : 自然数}
  证明: by
  have : (m + 1 : Nat∞ω) != ∞ := Ne.symm (ne_of_beq_false rfl)
  rcases h.contDiffOn' (ENat.add_one_natCast_le_withTop_of_lt hmn) (by simp [this])
    with ⟨u, uo, xu, hu⟩
  set t := insert x s inter u
  have A : t =ᶠ[𝓝[!=] x] s := by
    simp only [set_eventuallyEq_iff_inf_principal, ← nhdsWithin_inter']
    rw [← inter_assoc]; rw [nhdsWithin_inter_of_mem']; rw [← sdiff_eq_compl_inter]; rw [insert_sdiff_of_mem]; rw [sdiff_eq_compl_inter]
    exacts [rfl, mem_nhdsWithin_of_mem_nhds (uo.mem_nhds xu)]
  have B : iteratedFDerivWithin 𝕜 m f s =ᶠ[𝓝 x] iteratedFDerivWithin 𝕜 m f t :=
    iteratedFDerivWithin_eventually_congr_set' _ A.symm _
  have C : DifferentiableWithinAt 𝕜 (iteratedFDerivWithin 𝕜 m f t) t x :=
    hu.differentiableOn_iteratedFDerivWithin (Nat.cast_lt.2 m.lt_succ_self) (hs.inter uo) x
      ⟨mem_insert _ _, xu⟩
  rw [differentiableWithinAt_congr_set' _ A] at C
  exact C.congr_of_eventuallyEq (B.filter_mono inf_le_left) B.self_of_nhds

Depends on / 依赖: ENat.add_one_natCast_le_withTop_of_lt, Ne.symm, add_one_natCast_le_withTop_of_lt, contDiffOn, exacts, h.contDiffOn, insert, insert_sdiff_of_mem, inter_assoc, iterate, mem_nhds, mem_nhdsWithin_of_mem_nhds, ne_of_beq_false, nhdsWithin_inter, nhdsWithin_inter_of_mem, sdiff_eq_compl_inter, set_eventuallyEq_iff_inf_principal, uo.mem_nhds
-/
theorem ContDiffWithinAt.differentiableWithinAt_iteratedFDerivWithin {m : Nat}
    (h : ContDiffWithinAt 𝕜 n f s x) (hmn : m < n) (hs : UniqueDiffOn 𝕜 (insert x s)) :
    DifferentiableWithinAt 𝕜 (iteratedFDerivWithin 𝕜 m f s) s x := by
  have : (m + 1 : Nat∞ω) != ∞ := Ne.symm (ne_of_beq_false rfl)
  rcases h.contDiffOn' (ENat.add_one_natCast_le_withTop_of_lt hmn) (by simp [this])
    with ⟨u, uo, xu, hu⟩
  set t := insert x s inter u
  have A : t =ᶠ[𝓝[!=] x] s := by
    simp only [set_eventuallyEq_iff_inf_principal, ← nhdsWithin_inter']
    rw [← inter_assoc]; rw [nhdsWithin_inter_of_mem']; rw [← sdiff_eq_compl_inter]; rw [insert_sdiff_of_mem]; rw [sdiff_eq_compl_inter]
    exacts [rfl, mem_nhdsWithin_of_mem_nhds (uo.mem_nhds xu)]
  have B : iteratedFDerivWithin 𝕜 m f s =ᶠ[𝓝 x] iteratedFDerivWithin 𝕜 m f t :=
    iteratedFDerivWithin_eventually_congr_set' _ A.symm _
  have C : DifferentiableWithinAt 𝕜 (iteratedFDerivWithin 𝕜 m f t) t x :=
    hu.differentiableOn_iteratedFDerivWithin (Nat.cast_lt.2 m.lt_succ_self) (hs.inter uo) x
      ⟨mem_insert _ _, xu⟩
  rw [differentiableWithinAt_congr_set' _ A] at C
  exact C.congr_of_eventuallyEq (B.filter_mono inf_le_left) B.self_of_nhds

/--
theorem `contDiffOn_iff_continuousOn_differentiableOn` / 定理 `contDiffOn_iff_continuousOn_differentiableOn`

English:
theorem contDiffOn_iff_continuousOn_differentiableOn
  given: {n : Nat∞} (hs : UniqueDiffOn 𝕜 s)
  proof: ⟨fun h => ⟨fun _m hm => h.continuousOn_iteratedFDerivWithin (mod_cast hm) hs,
      fun _m hm => h.differentiableOn_iteratedFDerivWithin (mod_cast hm) hs⟩,
    fun h => contDiffOn_of_continuousOn_differentiableOn h.1 h.2⟩

中文:
定理 contDiffOn_iff_continuousOn_differentiableOn
  条件: {n : 自然数∞} (hs : UniqueDiffOn 𝕜 s)
  证明: ⟨fun h => ⟨fun _m hm => h.continuousOn_iteratedFDerivWithin (mod_cast hm) hs,
      fun _m hm => h.differentiableOn_iteratedFDerivWithin (mod_cast hm) hs⟩,
    fun h => contDiffOn_of_continuousOn_differentiableOn h.1 h.2⟩

Depends on / 依赖: contDiffOn_of_continuousOn_differentiableOn, continuousOn_iteratedFDerivWithin, differentiableOn_iteratedFDerivWithin, h.continuousOn_iteratedFDerivWithin, h.differentiableOn_iteratedFDerivWithin, mod_cast
-/
theorem contDiffOn_iff_continuousOn_differentiableOn {n : Nat∞} (hs : UniqueDiffOn 𝕜 s) :
    ContDiffOn 𝕜 n f s ↔
      (forall m : Nat, m <= n -> ContinuousOn (fun x => iteratedFDerivWithin 𝕜 m f s x) s) ∧
        forall m : Nat, m < n -> DifferentiableOn 𝕜 (fun x => iteratedFDerivWithin 𝕜 m f s x) s :=
  ⟨fun h => ⟨fun _m hm => h.continuousOn_iteratedFDerivWithin (mod_cast hm) hs,
      fun _m hm => h.differentiableOn_iteratedFDerivWithin (mod_cast hm) hs⟩,
    fun h => contDiffOn_of_continuousOn_differentiableOn h.1 h.2⟩

/--
theorem `contDiffOn_nat_iff_continuousOn_differentiableOn` / 定理 `contDiffOn_nat_iff_continuousOn_differentiableOn`

English:
theorem contDiffOn_nat_iff_continuousOn_differentiableOn
  given: {n : Nat} (hs : UniqueDiffOn 𝕜 s)
  proof: by
  rw [← WithTop.coe_natCast]; rw [contDiffOn_iff_continuousOn_differentiableOn hs]
  simp

中文:
定理 contDiffOn_nat_iff_continuousOn_differentiableOn
  条件: {n : 自然数} (hs : UniqueDiffOn 𝕜 s)
  证明: by
  rw [← WithTop.coe_natCast]; rw [contDiffOn_iff_continuousOn_differentiableOn hs]
  simp

Depends on / 依赖: WithTop, WithTop.coe_natCast, coe_natCast, contDiffOn_iff_continuousOn_differentiableOn
-/
theorem contDiffOn_nat_iff_continuousOn_differentiableOn {n : Nat} (hs : UniqueDiffOn 𝕜 s) :
    ContDiffOn 𝕜 n f s ↔
      (forall m : Nat, m <= n -> ContinuousOn (fun x => iteratedFDerivWithin 𝕜 m f s x) s) ∧
        forall m : Nat, m < n -> DifferentiableOn 𝕜 (fun x => iteratedFDerivWithin 𝕜 m f s x) s := by
  rw [← WithTop.coe_natCast]; rw [contDiffOn_iff_continuousOn_differentiableOn hs]
  simp

/--
theorem `contDiffOn_succ_of_fderivWithin` / 定理 `contDiffOn_succ_of_fderivWithin`

English:
theorem contDiffOn_succ_of_fderivWithin
  statement: (hf : DifferentiableOn 𝕜 f s)
  proof: by
  rcases eq_or_ne n ∞ with rfl | hn
  · rw [ENat.coe_top_add_one, contDiffOn_infty]
    intro m x hx
    apply ContDiffWithinAt.of_le _ (show (m : Nat∞ω) <= m + 1 from le_self_add)
    rw [contDiffWithinAt_succ_iff_hasFDerivWithinAt (by simp)]; rw [insert_eq_of_mem hx]
    exact ⟨s, self_mem_nhdsWithin, (by simp), fderivWithin 𝕜 f s,
      fun y hy => (hf y hy).hasFDerivWithinAt, (h x hx).of_le (mod_cast le_top)⟩
  · intro x hx
    rw [contDiffWithinAt_succ_iff_hasFDerivWithinAt hn]; rw [insert_eq_of_mem hx]
    exact ⟨s, self_mem_nhdsWithin, h', fderivWithin 𝕜 f s,
      fun y hy => (hf y hy).hasFDerivWithinAt, h x hx⟩

中文:
定理 contDiffOn_succ_of_fderivWithin
  结论: (hf : DifferentiableOn 𝕜 f s)
  证明: by
  rcases eq_or_ne n ∞ with rfl | hn
  · rw [ENat.coe_top_add_one, contDiffOn_infty]
    intro m x hx
    apply ContDiffWithinAt.of_le _ (show (m : Nat∞ω) <= m + 1 from le_self_add)
    rw [contDiffWithinAt_succ_iff_hasFDerivWithinAt (by simp)]; rw [insert_eq_of_mem hx]
    exact ⟨s, self_mem_nhdsWithin, (by simp), fderivWithin 𝕜 f s,
      fun y hy => (hf y hy).hasFDerivWithinAt, (h x hx).of_le (mod_cast le_top)⟩
  · intro x hx
    rw [contDiffWithinAt_succ_iff_hasFDerivWithinAt hn]; rw [insert_eq_of_mem hx]
    exact ⟨s, self_mem_nhdsWithin, h', fderivWithin 𝕜 f s,
      fun y hy => (hf y hy).hasFDerivWithinAt, h x hx⟩

Depends on / 依赖: ContDiffWithinAt, ContDiffWithinAt.of_le, ENat.coe_top_add_one, coe_top_add_one, contDiffOn_infty, contDiffWithinAt_succ_iff_hasFDerivWithinAt, eq_or_ne, fderivWithin, hasFDerivWithinAt, insert_eq_of_mem, le_self_add, le_top, mod_cast, of_le, self_, self_mem_nhdsWithin
-/
theorem contDiffOn_succ_of_fderivWithin (hf : DifferentiableOn 𝕜 f s)
    (h' : n = ω -> AnalyticOn 𝕜 f s)
    (h : ContDiffOn 𝕜 n (fun y => fderivWithin 𝕜 f s y) s) : ContDiffOn 𝕜 (n + 1) f s := by
  rcases eq_or_ne n ∞ with rfl | hn
  · rw [ENat.coe_top_add_one, contDiffOn_infty]
    intro m x hx
    apply ContDiffWithinAt.of_le _ (show (m : Nat∞ω) <= m + 1 from le_self_add)
    rw [contDiffWithinAt_succ_iff_hasFDerivWithinAt (by simp)]; rw [insert_eq_of_mem hx]
    exact ⟨s, self_mem_nhdsWithin, (by simp), fderivWithin 𝕜 f s,
      fun y hy => (hf y hy).hasFDerivWithinAt, (h x hx).of_le (mod_cast le_top)⟩
  · intro x hx
    rw [contDiffWithinAt_succ_iff_hasFDerivWithinAt hn]; rw [insert_eq_of_mem hx]
    exact ⟨s, self_mem_nhdsWithin, h', fderivWithin 𝕜 f s,
      fun y hy => (hf y hy).hasFDerivWithinAt, h x hx⟩

/--
theorem `contDiffOn_of_analyticOn_of_fderivWithin` / 定理 `contDiffOn_of_analyticOn_of_fderivWithin`

English:
theorem contDiffOn_of_analyticOn_of_fderivWithin
  statement: (hf : AnalyticOn 𝕜 f s)
  proof: by
  suffices ContDiffOn 𝕜 (ω + 1) f s from this.of_le le_top
  exact contDiffOn_succ_of_fderivWithin hf.differentiableOn (fun _ => hf) h

中文:
定理 contDiffOn_of_analyticOn_of_fderivWithin
  结论: (hf : AnalyticOn 𝕜 f s)
  证明: by
  suffices ContDiffOn 𝕜 (ω + 1) f s from this.of_le le_top
  exact contDiffOn_succ_of_fderivWithin hf.differentiableOn (fun _ => hf) h

Depends on / 依赖: ContDiffOn, contDiffOn_succ_of_fderivWithin, differentiableOn, hf.differentiableOn, le_top, of_le, this.of_le
-/
theorem contDiffOn_of_analyticOn_of_fderivWithin (hf : AnalyticOn 𝕜 f s)
    (h : ContDiffOn 𝕜 ω (fun y => fderivWithin 𝕜 f s y) s) : ContDiffOn 𝕜 n f s := by
  suffices ContDiffOn 𝕜 (ω + 1) f s from this.of_le le_top
  exact contDiffOn_succ_of_fderivWithin hf.differentiableOn (fun _ => hf) h

/--
theorem `contDiffOn_succ_iff_fderivWithin` / 定理 `contDiffOn_succ_iff_fderivWithin`

English:
theorem contDiffOn_succ_iff_fderivWithin
  given: (hs : UniqueDiffOn 𝕜 s)
  proof: by
  refine ⟨fun H => ?_, fun h => contDiffOn_succ_of_fderivWithin h.1 h.2.1 h.2.2⟩
  refine ⟨H.differentiableOn (by simp), ?_, fun x hx => ?_⟩
  · rintro rfl
    exact H.analyticOn
  have A (m : Nat) (hm : m <= n) : ContDiffWithinAt 𝕜 m (fun y => fderivWithin 𝕜 f s y) s x := by
    rcases (contDiffWithinAt_succ_iff_hasFDerivWithinAt (n := m) (ne_of_beq_false rfl)).1
      (H.of_le (by gcongr) x hx) with ⟨u, hu, -, f', hff', hf'⟩
    rcases mem_nhdsWithin.1 hu with ⟨o, o_open, xo, ho⟩
    rw [inter_comm]; rw [insert_eq_of_mem hx] at ho
    have := hf'.mono ho
    rw [contDiffWithinAt_inter' (mem_nhdsWithin_of_mem_nhds (IsOpen.mem_nhds o_open xo))] at this
    apply this.congr_of_eventuallyEq_of_mem _ hx
    have : o inter s in 𝓝[s] x := mem_nhdsWithin.2 ⟨o, o_open, xo, Subset.refl _⟩
    rw [inter_comm] at this
    refine Filter.eventuallyEq_of_mem this fun y hy => ?_
    have A : fderivWithin 𝕜 f (s inter o) y = f' y :=
      ((hff' y (ho hy)).mono ho).fderivWithin (hs.inter o_open y hy)
    rwa [fderivWithin_inter (o_open.mem_nhds hy.2)] at A
  match n with
  | ω => exact (H.analyticOn.fderivWithin hs).contDiffOn hs (n := ω) x hx
  | ∞ => exact contDiffWithinAt_infty.2 (fun m => A m (mod_cast le_top))
  | (n : Nat) => exact A n le_rfl

中文:
定理 contDiffOn_succ_iff_fderivWithin
  条件: (hs : UniqueDiffOn 𝕜 s)
  证明: by
  refine ⟨fun H => ?_, fun h => contDiffOn_succ_of_fderivWithin h.1 h.2.1 h.2.2⟩
  refine ⟨H.differentiableOn (by simp), ?_, fun x hx => ?_⟩
  · rintro rfl
    exact H.analyticOn
  have A (m : Nat) (hm : m <= n) : ContDiffWithinAt 𝕜 m (fun y => fderivWithin 𝕜 f s y) s x := by
    rcases (contDiffWithinAt_succ_iff_hasFDerivWithinAt (n := m) (ne_of_beq_false rfl)).1
      (H.of_le (by gcongr) x hx) with ⟨u, hu, -, f', hff', hf'⟩
    rcases mem_nhdsWithin.1 hu with ⟨o, o_open, xo, ho⟩
    rw [inter_comm]; rw [insert_eq_of_mem hx] at ho
    have := hf'.mono ho
    rw [contDiffWithinAt_inter' (mem_nhdsWithin_of_mem_nhds (IsOpen.mem_nhds o_open xo))] at this
    apply this.congr_of_eventuallyEq_of_mem _ hx
    have : o inter s in 𝓝[s] x := mem_nhdsWithin.2 ⟨o, o_open, xo, Subset.refl _⟩
    rw [inter_comm] at this
    refine Filter.eventuallyEq_of_mem this fun y hy => ?_
    have A : fderivWithin 𝕜 f (s inter o) y = f' y :=
      ((hff' y (ho hy)).mono ho).fderivWithin (hs.inter o_open y hy)
    rwa [fderivWithin_inter (o_open.mem_nhds hy.2)] at A
  match n with
  | ω => exact (H.analyticOn.fderivWithin hs).contDiffOn hs (n := ω) x hx
  | ∞ => exact contDiffWithinAt_infty.2 (fun m => A m (mod_cast le_top))
  | (n : Nat) => exact A n le_rfl

Depends on / 依赖: ContDiffWithinAt, H.analyticOn, H.differentiableOn, H.of_le, analyticOn, contDiffOn_succ_of_fderivWithin, contDiffWithinAt_succ_iff_hasFDerivWithinAt, differentiableOn, fderivWithin, insert_eq_of_me, inter_comm, mem_nhdsWithin, ne_of_beq_false, o_open, of_le
-/
theorem contDiffOn_succ_iff_fderivWithin (hs : UniqueDiffOn 𝕜 s) :
    ContDiffOn 𝕜 (n + 1) f s ↔
      DifferentiableOn 𝕜 f s ∧ (n = ω -> AnalyticOn 𝕜 f s) ∧
      ContDiffOn 𝕜 n (fderivWithin 𝕜 f s) s := by
  refine ⟨fun H => ?_, fun h => contDiffOn_succ_of_fderivWithin h.1 h.2.1 h.2.2⟩
  refine ⟨H.differentiableOn (by simp), ?_, fun x hx => ?_⟩
  · rintro rfl
    exact H.analyticOn
  have A (m : Nat) (hm : m <= n) : ContDiffWithinAt 𝕜 m (fun y => fderivWithin 𝕜 f s y) s x := by
    rcases (contDiffWithinAt_succ_iff_hasFDerivWithinAt (n := m) (ne_of_beq_false rfl)).1
      (H.of_le (by gcongr) x hx) with ⟨u, hu, -, f', hff', hf'⟩
    rcases mem_nhdsWithin.1 hu with ⟨o, o_open, xo, ho⟩
    rw [inter_comm]; rw [insert_eq_of_mem hx] at ho
    have := hf'.mono ho
    rw [contDiffWithinAt_inter' (mem_nhdsWithin_of_mem_nhds (IsOpen.mem_nhds o_open xo))] at this
    apply this.congr_of_eventuallyEq_of_mem _ hx
    have : o inter s in 𝓝[s] x := mem_nhdsWithin.2 ⟨o, o_open, xo, Subset.refl _⟩
    rw [inter_comm] at this
    refine Filter.eventuallyEq_of_mem this fun y hy => ?_
    have A : fderivWithin 𝕜 f (s inter o) y = f' y :=
      ((hff' y (ho hy)).mono ho).fderivWithin (hs.inter o_open y hy)
    rwa [fderivWithin_inter (o_open.mem_nhds hy.2)] at A
  match n with
  | ω => exact (H.analyticOn.fderivWithin hs).contDiffOn hs (n := ω) x hx
  | ∞ => exact contDiffWithinAt_infty.2 (fun m => A m (mod_cast le_top))
  | (n : Nat) => exact A n le_rfl

/--
theorem `contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn` / 定理 `contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn`

English:
theorem contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
  given: (hs : UniqueDiffOn 𝕜 s)
  proof: by
  rw [contDiffOn_succ_iff_fderivWithin hs]
  refine ⟨fun h => ⟨h.2.1, fderivWithin 𝕜 f s, h.2.2,
    fun x hx => (h.1 x hx).hasFDerivWithinAt⟩, fun ⟨f_an, h⟩ => ?_⟩
  rcases h with ⟨f', h1, h2⟩
  refine ⟨fun x hx => (h2 x hx).differentiableWithinAt, f_an, fun x hx => ?_⟩
  exact (h1 x hx).congr_of_mem (fun y hy => (h2 y hy).fderivWithin (hs y hy)) hx

中文:
定理 contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
  条件: (hs : UniqueDiffOn 𝕜 s)
  证明: by
  rw [contDiffOn_succ_iff_fderivWithin hs]
  refine ⟨fun h => ⟨h.2.1, fderivWithin 𝕜 f s, h.2.2,
    fun x hx => (h.1 x hx).hasFDerivWithinAt⟩, fun ⟨f_an, h⟩ => ?_⟩
  rcases h with ⟨f', h1, h2⟩
  refine ⟨fun x hx => (h2 x hx).differentiableWithinAt, f_an, fun x hx => ?_⟩
  exact (h1 x hx).congr_of_mem (fun y hy => (h2 y hy).fderivWithin (hs y hy)) hx

Depends on / 依赖: congr_of_mem, contDiffOn_succ_iff_fderivWithin, differentiableWithinAt, f_an, fderivWithin, hasFDerivWithinAt
-/
theorem contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (hs : UniqueDiffOn 𝕜 s) :
    ContDiffOn 𝕜 (n + 1) f s ↔ (n = ω -> AnalyticOn 𝕜 f s) ∧
      exists f' : E -> E ->L[𝕜] F, ContDiffOn 𝕜 n f' s ∧ forall x, x in s -> HasFDerivWithinAt f (f' x) s x := by
  rw [contDiffOn_succ_iff_fderivWithin hs]
  refine ⟨fun h => ⟨h.2.1, fderivWithin 𝕜 f s, h.2.2,
    fun x hx => (h.1 x hx).hasFDerivWithinAt⟩, fun ⟨f_an, h⟩ => ?_⟩
  rcases h with ⟨f', h1, h2⟩
  refine ⟨fun x hx => (h2 x hx).differentiableWithinAt, f_an, fun x hx => ?_⟩
  exact (h1 x hx).congr_of_mem (fun y hy => (h2 y hy).fderivWithin (hs y hy)) hx

/--
theorem `contDiffOn_infty_iff_fderivWithin` / 定理 `contDiffOn_infty_iff_fderivWithin`

English:
theorem contDiffOn_infty_iff_fderivWithin
  given: (hs : UniqueDiffOn 𝕜 s)
  proof: by
  rw [← ENat.coe_top_add_one]; rw [contDiffOn_succ_iff_fderivWithin hs]
  simp

中文:
定理 contDiffOn_infty_iff_fderivWithin
  条件: (hs : UniqueDiffOn 𝕜 s)
  证明: by
  rw [← ENat.coe_top_add_one]; rw [contDiffOn_succ_iff_fderivWithin hs]
  simp

Depends on / 依赖: ENat.coe_top_add_one, coe_top_add_one, contDiffOn_succ_iff_fderivWithin
-/
theorem contDiffOn_infty_iff_fderivWithin (hs : UniqueDiffOn 𝕜 s) :
    ContDiffOn 𝕜 ∞ f s ↔ DifferentiableOn 𝕜 f s ∧ ContDiffOn 𝕜 ∞ (fderivWithin 𝕜 f s) s := by
  rw [← ENat.coe_top_add_one]; rw [contDiffOn_succ_iff_fderivWithin hs]
  simp

/--
theorem `contDiffOn_succ_iff_fderiv_of_isOpen` / 定理 `contDiffOn_succ_iff_fderiv_of_isOpen`

English:
theorem contDiffOn_succ_iff_fderiv_of_isOpen
  given: (hs : IsOpen s)
  proof: by
  rw [contDiffOn_succ_iff_fderivWithin hs.uniqueDiffOn]; rw [contDiffOn_congr fun x hx => fderivWithin_of_isOpen hs hx]

中文:
定理 contDiffOn_succ_iff_fderiv_of_isOpen
  条件: (hs : 是开集 s)
  证明: by
  rw [contDiffOn_succ_iff_fderivWithin hs.uniqueDiffOn]; rw [contDiffOn_congr fun x hx => fderivWithin_of_isOpen hs hx]

Depends on / 依赖: contDiffOn_congr, contDiffOn_succ_iff_fderivWithin, fderivWithin_of_isOpen, hs.uniqueDiffOn, uniqueDiffOn
-/
theorem contDiffOn_succ_iff_fderiv_of_isOpen (hs : IsOpen s) :
    ContDiffOn 𝕜 (n + 1) f s ↔
      DifferentiableOn 𝕜 f s ∧ (n = ω -> AnalyticOn 𝕜 f s) ∧
      ContDiffOn 𝕜 n (fderiv 𝕜 f) s := by
  rw [contDiffOn_succ_iff_fderivWithin hs.uniqueDiffOn]; rw [contDiffOn_congr fun x hx => fderivWithin_of_isOpen hs hx]

/--
theorem `contDiffOn_infty_iff_fderiv_of_isOpen` / 定理 `contDiffOn_infty_iff_fderiv_of_isOpen`

English:
theorem contDiffOn_infty_iff_fderiv_of_isOpen
  given: (hs : IsOpen s)
  proof: by
  rw [← ENat.coe_top_add_one]; rw [contDiffOn_succ_iff_fderiv_of_isOpen hs]
  simp

中文:
定理 contDiffOn_infty_iff_fderiv_of_isOpen
  条件: (hs : 是开集 s)
  证明: by
  rw [← ENat.coe_top_add_one]; rw [contDiffOn_succ_iff_fderiv_of_isOpen hs]
  simp

Depends on / 依赖: ENat.coe_top_add_one, coe_top_add_one, contDiffOn_succ_iff_fderiv_of_isOpen
-/
theorem contDiffOn_infty_iff_fderiv_of_isOpen (hs : IsOpen s) :
    ContDiffOn 𝕜 ∞ f s ↔ DifferentiableOn 𝕜 f s ∧ ContDiffOn 𝕜 ∞ (fderiv 𝕜 f) s := by
  rw [← ENat.coe_top_add_one]; rw [contDiffOn_succ_iff_fderiv_of_isOpen hs]
  simp

/--
theorem `ContDiffOn.fderivWithin` / 定理 `ContDiffOn.fderivWithin`

English:
theorem ContDiffOn.fderivWithin
  statement: (hf : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s)
  proof: ((contDiffOn_succ_iff_fderivWithin hs).1 (hf.of_le hmn)).2.2

中文:
定理 ContDiffOn.fderivWithin
  结论: (hf : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s)
  证明: ((contDiffOn_succ_iff_fderivWithin hs).1 (hf.of_le hmn)).2.2
-/
protected theorem ContDiffOn.fderivWithin (hf : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s)
    (hmn : m + 1 <= n) : ContDiffOn 𝕜 m (fderivWithin 𝕜 f s) s :=
  ((contDiffOn_succ_iff_fderivWithin hs).1 (hf.of_le hmn)).2.2

/--
theorem `ContDiffOn.fderiv_of_isOpen` / 定理 `ContDiffOn.fderiv_of_isOpen`

English:
theorem ContDiffOn.fderiv_of_isOpen
  given: (hf : ContDiffOn 𝕜 n f s) (hs : IsOpen s) (hmn : m + 1 <= n)
  proof: (hf.fderivWithin hs.uniqueDiffOn hmn).congr fun _ hx => (fderivWithin_of_isOpen hs hx).symm

中文:
定理 ContDiffOn.fderiv_of_isOpen
  条件: (hf : ContDiffOn 𝕜 n f s) (hs : 是开集 s) (hmn : m + 1 <= n)
  证明: (hf.fderivWithin hs.uniqueDiffOn hmn).congr fun _ hx => (fderivWithin_of_isOpen hs hx).symm

Depends on / 依赖: fderivWithin, fderivWithin_of_isOpen, hf.fderivWithin, hs.uniqueDiffOn, uniqueDiffOn
-/
theorem ContDiffOn.fderiv_of_isOpen (hf : ContDiffOn 𝕜 n f s) (hs : IsOpen s) (hmn : m + 1 <= n) :
    ContDiffOn 𝕜 m (fderiv 𝕜 f) s :=
  (hf.fderivWithin hs.uniqueDiffOn hmn).congr fun _ hx => (fderivWithin_of_isOpen hs hx).symm

/--
theorem `ContDiffOn.continuousOn_fderivWithin` / 定理 `ContDiffOn.continuousOn_fderivWithin`

English:
theorem ContDiffOn.continuousOn_fderivWithin
  statement: (h : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s)
  proof: ((contDiffOn_succ_iff_fderivWithin hs).1
    (h.of_le (show 0 + (1 : Nat∞ω) <= n from hn))).2.2.continuousOn

中文:
定理 ContDiffOn.continuousOn_fderivWithin
  结论: (h : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s)
  证明: ((contDiffOn_succ_iff_fderivWithin hs).1
    (h.of_le (show 0 + (1 : Nat∞ω) <= n from hn))).2.2.continuousOn

Depends on / 依赖: contDiffOn_succ_iff_fderivWithin, continuousOn, h.of_le, of_le
-/
theorem ContDiffOn.continuousOn_fderivWithin (h : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s)
    (hn : 1 <= n) : ContinuousOn (fderivWithin 𝕜 f s) s :=
  ((contDiffOn_succ_iff_fderivWithin hs).1
    (h.of_le (show 0 + (1 : Nat∞ω) <= n from hn))).2.2.continuousOn

/--
theorem `ContDiffOn.continuousOn_fderiv_of_isOpen` / 定理 `ContDiffOn.continuousOn_fderiv_of_isOpen`

English:
theorem ContDiffOn.continuousOn_fderiv_of_isOpen
  statement: (h : ContDiffOn 𝕜 n f s) (hs : IsOpen s)
  proof: ((contDiffOn_succ_iff_fderiv_of_isOpen hs).1
    (h.of_le (show 0 + (1 : Nat∞ω) <= n from hn))).2.2.continuousOn

中文:
定理 ContDiffOn.continuousOn_fderiv_of_isOpen
  结论: (h : ContDiffOn 𝕜 n f s) (hs : 是开集 s)
  证明: ((contDiffOn_succ_iff_fderiv_of_isOpen hs).1
    (h.of_le (show 0 + (1 : Nat∞ω) <= n from hn))).2.2.continuousOn

Depends on / 依赖: contDiffOn_succ_iff_fderiv_of_isOpen, continuousOn, h.of_le, of_le
-/
theorem ContDiffOn.continuousOn_fderiv_of_isOpen (h : ContDiffOn 𝕜 n f s) (hs : IsOpen s)
    (hn : 1 <= n) : ContinuousOn (fderiv 𝕜 f) s :=
  ((contDiffOn_succ_iff_fderiv_of_isOpen hs).1
    (h.of_le (show 0 + (1 : Nat∞ω) <= n from hn))).2.2.continuousOn

/-! ### Smooth functions at a point -/

variable (𝕜) in
/-- A function is continuously differentiable up to `n` at a point `x` if, for any integer `k ≤ n`,
there is a neighborhood of `x` where `f` admits derivatives up to order `n`, which are continuous.
The parameter `n` belongs to `ℕ∞ω` (accessible in the `ContDiff` scope), i.e. it can be a natural
number, `∞`, or `ω`.

For `n = ∞`, we only require that this holds up to any finite order (where the neighborhood may
depend on the finite order we consider).
For `n = ω`, we require the function to be analytic at `x`. The precise
definition we give (all the derivatives should be analytic) is more involved to work around issues
when the space is not complete, but it is equivalent when the space is complete.
-/
@[fun_prop]
/--
Definition of `ContDiffAt` / `ContDiffAt` 的定义

English:
definition ContDiffAt
  signature: (n : Nat∞ω) (f : E -> F) (x : E)
  body: ContDiffWithinAt 𝕜 n f univ x

中文:
定义 ContDiffAt
  签名: (n : 自然数∞ω) (f : E -> F) (x : E)
  定义体: ContDiffWithinAt 𝕜 n f univ x

Depends on / 依赖: ContDiffWithinAt
-/
def ContDiffAt (n : Nat∞ω) (f : E -> F) (x : E) : Prop :=
  ContDiffWithinAt 𝕜 n f univ x

/--
theorem `contDiffWithinAt_univ` / 定理 `contDiffWithinAt_univ`

English:
theorem contDiffWithinAt_univ
  statement: ContDiffWithinAt 𝕜 n f univ x ↔ ContDiffAt 𝕜 n f x
  proof: Iff.rfl

中文:
定理 contDiffWithinAt_univ
  结论: ContDiffWithinAt 𝕜 n f univ x ↔ ContDiffAt 𝕜 n f x
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem contDiffWithinAt_univ : ContDiffWithinAt 𝕜 n f univ x ↔ ContDiffAt 𝕜 n f x :=
  Iff.rfl

/--
theorem `contDiffAt_infty` / 定理 `contDiffAt_infty`

English:
theorem contDiffAt_infty
  statement: ContDiffAt 𝕜 ∞ f x ↔ forall n : Nat, ContDiffAt 𝕜 n f x
  proof: by
  simp [← contDiffWithinAt_univ, contDiffWithinAt_infty]

@[fun_prop]

中文:
定理 contDiffAt_infty
  结论: ContDiffAt 𝕜 ∞ f x ↔ 对任意 n : 自然数, ContDiffAt 𝕜 n f x
  证明: by
  simp [← contDiffWithinAt_univ, contDiffWithinAt_infty]

@[fun_prop]

Depends on / 依赖: contDiffWithinAt_infty, contDiffWithinAt_univ
-/
theorem contDiffAt_infty : ContDiffAt 𝕜 ∞ f x ↔ forall n : Nat, ContDiffAt 𝕜 n f x := by
  simp [← contDiffWithinAt_univ, contDiffWithinAt_infty]

@[fun_prop]
/--
theorem `ContDiffAt.contDiffWithinAt` / 定理 `ContDiffAt.contDiffWithinAt`

English:
theorem ContDiffAt.contDiffWithinAt
  given: (h : ContDiffAt 𝕜 n f x)
  statement: ContDiffWithinAt 𝕜 n f s x
  proof: h.mono (subset_univ _)

@[fun_prop]

中文:
定理 ContDiffAt.contDiffWithinAt
  条件: (h : ContDiffAt 𝕜 n f x)
  结论: ContDiffWithinAt 𝕜 n f s x
  证明: h.mono (subset_univ _)

@[fun_prop]

Depends on / 依赖: h.mono, subset_univ
-/
theorem ContDiffAt.contDiffWithinAt (h : ContDiffAt 𝕜 n f x) : ContDiffWithinAt 𝕜 n f s x :=
  h.mono (subset_univ _)

@[fun_prop]
/--
theorem `ContDiffWithinAt.contDiffAt` / 定理 `ContDiffWithinAt.contDiffAt`

English:
theorem ContDiffWithinAt.contDiffAt
  given: (h : ContDiffWithinAt 𝕜 n f s x) (hx : s in 𝓝 x)
  proof: by rwa [ContDiffAt, ← contDiffWithinAt_inter hx, univ_inter]

中文:
定理 ContDiffWithinAt.contDiffAt
  条件: (h : ContDiffWithinAt 𝕜 n f s x) (hx : s in 𝓝 x)
  证明: by rwa [ContDiffAt, ← contDiffWithinAt_inter hx, univ_inter]

Depends on / 依赖: ContDiffAt, contDiffWithinAt_inter, univ_inter
-/
theorem ContDiffWithinAt.contDiffAt (h : ContDiffWithinAt 𝕜 n f s x) (hx : s in 𝓝 x) :
    ContDiffAt 𝕜 n f x := by rwa [ContDiffAt, ← contDiffWithinAt_inter hx, univ_inter]

/--
theorem `contDiffWithinAt_iff_contDiffAt` / 定理 `contDiffWithinAt_iff_contDiffAt`

English:
theorem contDiffWithinAt_iff_contDiffAt
  given: (h : s in 𝓝 x)
  proof: by
  rw [← univ_inter s]; rw [contDiffWithinAt_inter h]; rw [contDiffWithinAt_univ]

中文:
定理 contDiffWithinAt_iff_contDiffAt
  条件: (h : s in 𝓝 x)
  证明: by
  rw [← univ_inter s]; rw [contDiffWithinAt_inter h]; rw [contDiffWithinAt_univ]

Depends on / 依赖: contDiffWithinAt_inter, contDiffWithinAt_univ, univ_inter
-/
theorem contDiffWithinAt_iff_contDiffAt (h : s in 𝓝 x) :
    ContDiffWithinAt 𝕜 n f s x ↔ ContDiffAt 𝕜 n f x := by
  rw [← univ_inter s]; rw [contDiffWithinAt_inter h]; rw [contDiffWithinAt_univ]

/--
theorem `IsOpen.contDiffOn_iff` / 定理 `IsOpen.contDiffOn_iff`

English:
theorem IsOpen.contDiffOn_iff
  given: (hs : IsOpen s)
  proof: forall₂_congr fun _ => contDiffWithinAt_iff_contDiffAt ∘ hs.mem_nhds

@[fun_prop]

中文:
定理 是开集.contDiffOn_iff
  条件: (hs : 是开集 s)
  证明: forall₂_congr fun _ => contDiffWithinAt_iff_contDiffAt ∘ hs.mem_nhds

@[fun_prop]

Depends on / 依赖: contDiffWithinAt_iff_contDiffAt, hs.mem_nhds, mem_nhds
-/
theorem IsOpen.contDiffOn_iff (hs : IsOpen s) :
    ContDiffOn 𝕜 n f s ↔ forall ⦃a⦄, a in s -> ContDiffAt 𝕜 n f a :=
  forall₂_congr fun _ => contDiffWithinAt_iff_contDiffAt ∘ hs.mem_nhds

@[fun_prop]
/--
theorem `ContDiffOn.contDiffAt` / 定理 `ContDiffOn.contDiffAt`

English:
theorem ContDiffOn.contDiffAt
  given: (h : ContDiffOn 𝕜 n f s) (hx : s in 𝓝 x)
  proof: (h _ (mem_of_mem_nhds hx)).contDiffAt hx

中文:
定理 ContDiffOn.contDiffAt
  条件: (h : ContDiffOn 𝕜 n f s) (hx : s in 𝓝 x)
  证明: (h _ (mem_of_mem_nhds hx)).contDiffAt hx

Depends on / 依赖: contDiffAt, mem_of_mem_nhds
-/
theorem ContDiffOn.contDiffAt (h : ContDiffOn 𝕜 n f s) (hx : s in 𝓝 x) :
    ContDiffAt 𝕜 n f x :=
  (h _ (mem_of_mem_nhds hx)).contDiffAt hx

/--
theorem `ContDiffAt.congr_of_eventuallyEq` / 定理 `ContDiffAt.congr_of_eventuallyEq`

English:
theorem ContDiffAt.congr_of_eventuallyEq
  given: (h : ContDiffAt 𝕜 n f x) (hg : f₁ =ᶠ[𝓝 x] f)
  proof: h.congr_of_eventuallyEq_of_mem (by rwa [nhdsWithin_univ]) (mem_univ x)

中文:
定理 ContDiffAt.congr_of_eventuallyEq
  条件: (h : ContDiffAt 𝕜 n f x) (hg : f₁ =ᶠ[𝓝 x] f)
  证明: h.congr_of_eventuallyEq_of_mem (by rwa [nhdsWithin_univ]) (mem_univ x)

Depends on / 依赖: congr_of_eventuallyEq_of_mem, h.congr_of_eventuallyEq_of_mem, mem_univ, nhdsWithin_univ
-/
theorem ContDiffAt.congr_of_eventuallyEq (h : ContDiffAt 𝕜 n f x) (hg : f₁ =ᶠ[𝓝 x] f) :
    ContDiffAt 𝕜 n f₁ x :=
  h.congr_of_eventuallyEq_of_mem (by rwa [nhdsWithin_univ]) (mem_univ x)

/--
theorem `ContDiffAt.of_le` / 定理 `ContDiffAt.of_le`

English:
theorem ContDiffAt.of_le
  given: (h : ContDiffAt 𝕜 n f x) (hmn : m <= n)
  statement: ContDiffAt 𝕜 m f x
  proof: ContDiffWithinAt.of_le h hmn

@[fun_prop]

中文:
定理 ContDiffAt.of_le
  条件: (h : ContDiffAt 𝕜 n f x) (hmn : m <= n)
  结论: ContDiffAt 𝕜 m f x
  证明: ContDiffWithinAt.of_le h hmn

@[fun_prop]

Depends on / 依赖: ContDiffWithinAt, ContDiffWithinAt.of_le, of_le
-/
theorem ContDiffAt.of_le (h : ContDiffAt 𝕜 n f x) (hmn : m <= n) : ContDiffAt 𝕜 m f x :=
  ContDiffWithinAt.of_le h hmn

@[fun_prop]
/--
theorem `ContDiffAt.continuousAt` / 定理 `ContDiffAt.continuousAt`

English:
theorem ContDiffAt.continuousAt
  given: (h : ContDiffAt 𝕜 n f x)
  statement: ContinuousAt f x
  proof: by
  simpa [continuousWithinAt_univ] using h.continuousWithinAt

中文:
定理 ContDiffAt.continuousAt
  条件: (h : ContDiffAt 𝕜 n f x)
  结论: ContinuousAt f x
  证明: by
  simpa [continuousWithinAt_univ] using h.continuousWithinAt

Depends on / 依赖: continuousWithinAt, continuousWithinAt_univ, h.continuousWithinAt
-/
theorem ContDiffAt.continuousAt (h : ContDiffAt 𝕜 n f x) : ContinuousAt f x := by
  simpa [continuousWithinAt_univ] using h.continuousWithinAt

/--
theorem `ContDiffAt.analyticAt` / 定理 `ContDiffAt.analyticAt`

English:
theorem ContDiffAt.analyticAt
  given: (h : ContDiffAt 𝕜 ω f x)
  statement: AnalyticAt 𝕜 f x
  proof: by
  rw [← contDiffWithinAt_univ] at h
  rw [← analyticWithinAt_univ]
  exact h.analyticWithinAt

中文:
定理 ContDiffAt.analyticAt
  条件: (h : ContDiffAt 𝕜 ω f x)
  结论: AnalyticAt 𝕜 f x
  证明: by
  rw [← contDiffWithinAt_univ] at h
  rw [← analyticWithinAt_univ]
  exact h.analyticWithinAt

Depends on / 依赖: analyticWithinAt, analyticWithinAt_univ, contDiffWithinAt_univ, h.analyticWithinAt
-/
theorem ContDiffAt.analyticAt (h : ContDiffAt 𝕜 ω f x) : AnalyticAt 𝕜 f x := by
  rw [← contDiffWithinAt_univ] at h
  rw [← analyticWithinAt_univ]
  exact h.analyticWithinAt

/--
theorem `AnalyticAt.contDiffAt` / 定理 `AnalyticAt.contDiffAt`

English:
theorem AnalyticAt.contDiffAt
  given: [CompleteSpace F] (h : AnalyticAt 𝕜 f x)
  proof: by
  rw [← contDiffWithinAt_univ]
  rw [← analyticWithinAt_univ] at h
  exact h.contDiffWithinAt

@[simp]

中文:
定理 AnalyticAt.contDiffAt
  条件: [完备空间 F] (h : AnalyticAt 𝕜 f x)
  证明: by
  rw [← contDiffWithinAt_univ]
  rw [← analyticWithinAt_univ] at h
  exact h.contDiffWithinAt

@[simp]

Depends on / 依赖: analyticWithinAt_univ, contDiffWithinAt, contDiffWithinAt_univ, h.contDiffWithinAt
-/
theorem AnalyticAt.contDiffAt [CompleteSpace F] (h : AnalyticAt 𝕜 f x) :
    ContDiffAt 𝕜 n f x := by
  rw [← contDiffWithinAt_univ]
  rw [← analyticWithinAt_univ] at h
  exact h.contDiffWithinAt

@[simp]
/--
theorem `contDiffWithinAt_compl_self` / 定理 `contDiffWithinAt_compl_self`

English:
theorem contDiffWithinAt_compl_self
  proof: by
  rw [compl_eq_univ_sdiff]; rw [contDiffWithinAt_sdiff_singleton]; rw [contDiffWithinAt_univ]

中文:
定理 contDiffWithinAt_compl_self
  证明: by
  rw [compl_eq_univ_sdiff]; rw [contDiffWithinAt_sdiff_singleton]; rw [contDiffWithinAt_univ]

Depends on / 依赖: compl_eq_univ_sdiff, contDiffWithinAt_sdiff_singleton, contDiffWithinAt_univ
-/
theorem contDiffWithinAt_compl_self :
    ContDiffWithinAt 𝕜 n f {x}ᶜ x ↔ ContDiffAt 𝕜 n f x := by
  rw [compl_eq_univ_sdiff]; rw [contDiffWithinAt_sdiff_singleton]; rw [contDiffWithinAt_univ]

/--
theorem `ContDiffAt.differentiableAt` / 定理 `ContDiffAt.differentiableAt`

English:
theorem ContDiffAt.differentiableAt
  given: (h : ContDiffAt 𝕜 n f x) (hn : n != 0)
  proof: by
  simpa [hn, differentiableWithinAt_univ] using h.differentiableWithinAt

中文:
定理 ContDiffAt.differentiableAt
  条件: (h : ContDiffAt 𝕜 n f x) (hn : n != 0)
  证明: by
  simpa [hn, differentiableWithinAt_univ] using h.differentiableWithinAt

Depends on / 依赖: differentiableWithinAt, differentiableWithinAt_univ, h.differentiableWithinAt
-/
theorem ContDiffAt.differentiableAt (h : ContDiffAt 𝕜 n f x) (hn : n != 0) :
    DifferentiableAt 𝕜 f x := by
  simpa [hn, differentiableWithinAt_univ] using h.differentiableWithinAt

/--
theorem `ContDiffAt.differentiableAt_iteratedFDeriv` / 定理 `ContDiffAt.differentiableAt_iteratedFDeriv`

English:
theorem ContDiffAt.differentiableAt_iteratedFDeriv
  proof: by
  rw [← differentiableWithinAt_univ]
  convert! (h.differentiableWithinAt_iteratedFDerivWithin hmn (by simp [uniqueDiffOn_univ]))
  exact iteratedFDerivWithin_univ.symm

@[fun_prop]

中文:
定理 ContDiffAt.differentiableAt_iteratedFDeriv
  证明: by
  rw [← differentiableWithinAt_univ]
  convert! (h.differentiableWithinAt_iteratedFDerivWithin hmn (by simp [uniqueDiffOn_univ]))
  exact iteratedFDerivWithin_univ.symm

@[fun_prop]

Depends on / 依赖: convert, differentiableWithinAt_iteratedFDerivWithin, differentiableWithinAt_univ, h.differentiableWithinAt_iteratedFDerivWithin, iteratedFDerivWithin_univ, iteratedFDerivWithin_univ.symm, uniqueDiffOn_univ
-/
theorem ContDiffAt.differentiableAt_iteratedFDeriv
    {f : E -> F} {n : Nat∞ω} {m : Nat} {x : E} (h : ContDiffAt 𝕜 n f x) (hmn : ↑m < n) :
    DifferentiableAt 𝕜 (iteratedFDeriv 𝕜 m f) x := by
  rw [← differentiableWithinAt_univ]
  convert! (h.differentiableWithinAt_iteratedFDerivWithin hmn (by simp [uniqueDiffOn_univ]))
  exact iteratedFDerivWithin_univ.symm

@[fun_prop]
/--
theorem `ContDiffAt.differentiableAt_one` / 定理 `ContDiffAt.differentiableAt_one`

English:
theorem ContDiffAt.differentiableAt_one
  given: (h : ContDiffAt 𝕜 1 f x)
  proof: by
  simpa [(le_refl 1), differentiableWithinAt_univ] using h.differentiableWithinAt

nonrec lemma ContDiffAt.contDiffOn (h : ContDiffAt 𝕜 n f x) (hm : m <= n) (h' : m = ∞ -> n = ω) :
    exists u in 𝓝 x, ContDiffOn 𝕜 m f u := by
  simpa [nhdsWithin_univ] using h.contDiffOn hm h'

中文:
定理 ContDiffAt.differentiableAt_one
  条件: (h : ContDiffAt 𝕜 1 f x)
  证明: by
  simpa [(le_refl 1), differentiableWithinAt_univ] using h.differentiableWithinAt

nonrec lemma ContDiffAt.contDiffOn (h : ContDiffAt 𝕜 n f x) (hm : m <= n) (h' : m = ∞ -> n = ω) :
    exists u in 𝓝 x, ContDiffOn 𝕜 m f u := by
  simpa [nhdsWithin_univ] using h.contDiffOn hm h'

Depends on / 依赖: differentiableWithinAt, differentiableWithinAt_univ, h.differentiableWithinAt, le_refl
-/
theorem ContDiffAt.differentiableAt_one (h : ContDiffAt 𝕜 1 f x) :
    DifferentiableAt 𝕜 f x := by
  simpa [(le_refl 1), differentiableWithinAt_univ] using h.differentiableWithinAt

nonrec lemma ContDiffAt.contDiffOn (h : ContDiffAt 𝕜 n f x) (hm : m <= n) (h' : m = ∞ -> n = ω) :
    exists u in 𝓝 x, ContDiffOn 𝕜 m f u := by
  simpa [nhdsWithin_univ] using h.contDiffOn hm h'

/--
theorem `contDiffAt_succ_iff_hasFDerivAt` / 定理 `contDiffAt_succ_iff_hasFDerivAt`

English:
theorem contDiffAt_succ_iff_hasFDerivAt
  given: {n : Nat}
  proof: by
  rw [← contDiffWithinAt_univ]; rw [contDiffWithinAt_succ_iff_hasFDerivWithinAt (by simp)]
  simp only [nhdsWithin_univ, mem_univ, insert_eq_of_mem]
  constructor
  · rintro ⟨u, H, -, f', h_fderiv, h_cont_diff⟩
    rcases mem_nhds_iff.mp H with ⟨t, htu, ht, hxt⟩
    refine ⟨f', ⟨t, ?_⟩, h_cont_diff.contDiffAt H⟩
    refine ⟨mem_nhds_iff.mpr ⟨t, Subset.rfl, ht, hxt⟩, ?_⟩
    intro y hyt
    refine (h_fderiv y (htu hyt)).hasFDerivAt ?_
    exact mem_nhds_iff.mpr ⟨t, htu, ht, hyt⟩
  · rintro ⟨f', ⟨u, H, h_fderiv⟩, h_cont_diff⟩
    refine ⟨u, H, by simp, f', fun x hxu => ?_, h_cont_diff.contDiffWithinAt⟩
    exact (h_fderiv x hxu).hasFDerivWithinAt

中文:
定理 contDiffAt_succ_iff_hasFDerivAt
  条件: {n : 自然数}
  证明: by
  rw [← contDiffWithinAt_univ]; rw [contDiffWithinAt_succ_iff_hasFDerivWithinAt (by simp)]
  simp only [nhdsWithin_univ, mem_univ, insert_eq_of_mem]
  constructor
  · rintro ⟨u, H, -, f', h_fderiv, h_cont_diff⟩
    rcases mem_nhds_iff.mp H with ⟨t, htu, ht, hxt⟩
    refine ⟨f', ⟨t, ?_⟩, h_cont_diff.contDiffAt H⟩
    refine ⟨mem_nhds_iff.mpr ⟨t, Subset.rfl, ht, hxt⟩, ?_⟩
    intro y hyt
    refine (h_fderiv y (htu hyt)).hasFDerivAt ?_
    exact mem_nhds_iff.mpr ⟨t, htu, ht, hyt⟩
  · rintro ⟨f', ⟨u, H, h_fderiv⟩, h_cont_diff⟩
    refine ⟨u, H, by simp, f', fun x hxu => ?_, h_cont_diff.contDiffWithinAt⟩
    exact (h_fderiv x hxu).hasFDerivWithinAt

Depends on / 依赖: Subset, Subset.rfl, contDiffAt, contDiffWithinAt_succ_iff_hasFDerivWithinAt, contDiffWithinAt_univ, h_cont_diff, h_cont_diff.contDiffAt, h_fderiv, hasFDerivAt, insert_eq_of_mem, mem_nhds_iff, mem_nhds_iff.mp, mem_nhds_iff.mpr, mem_univ, nhdsWithin_univ
-/
theorem contDiffAt_succ_iff_hasFDerivAt {n : Nat} :
    ContDiffAt 𝕜 (n + 1) f x ↔ exists f' : E -> E ->L[𝕜] F,
      (exists u in 𝓝 x, forall x in u, HasFDerivAt f (f' x) x) ∧ ContDiffAt 𝕜 n f' x := by
  rw [← contDiffWithinAt_univ]; rw [contDiffWithinAt_succ_iff_hasFDerivWithinAt (by simp)]
  simp only [nhdsWithin_univ, mem_univ, insert_eq_of_mem]
  constructor
  · rintro ⟨u, H, -, f', h_fderiv, h_cont_diff⟩
    rcases mem_nhds_iff.mp H with ⟨t, htu, ht, hxt⟩
    refine ⟨f', ⟨t, ?_⟩, h_cont_diff.contDiffAt H⟩
    refine ⟨mem_nhds_iff.mpr ⟨t, Subset.rfl, ht, hxt⟩, ?_⟩
    intro y hyt
    refine (h_fderiv y (htu hyt)).hasFDerivAt ?_
    exact mem_nhds_iff.mpr ⟨t, htu, ht, hyt⟩
  · rintro ⟨f', ⟨u, H, h_fderiv⟩, h_cont_diff⟩
    refine ⟨u, H, by simp, f', fun x hxu => ?_, h_cont_diff.contDiffWithinAt⟩
    exact (h_fderiv x hxu).hasFDerivWithinAt

/--
theorem `ContDiffAt.eventually` / 定理 `ContDiffAt.eventually`

English:
theorem ContDiffAt.eventually
  given: (h : ContDiffAt 𝕜 n f x) (h' : n != ∞)
  proof: by
  simpa [nhdsWithin_univ] using! ContDiffWithinAt.eventually h h'

中文:
定理 ContDiffAt.eventually
  条件: (h : ContDiffAt 𝕜 n f x) (h' : n != ∞)
  证明: by
  simpa [nhdsWithin_univ] using! ContDiffWithinAt.eventually h h'
-/
protected theorem ContDiffAt.eventually (h : ContDiffAt 𝕜 n f x) (h' : n != ∞) :
    forallᶠ y in 𝓝 x, ContDiffAt 𝕜 n f y := by
  simpa [nhdsWithin_univ] using! ContDiffWithinAt.eventually h h'

/--
theorem `iteratedFDerivWithin_eq_iteratedFDeriv` / 定理 `iteratedFDerivWithin_eq_iteratedFDeriv`

English:
theorem iteratedFDerivWithin_eq_iteratedFDeriv
  statement: {n : Nat}
  proof: by
  rw [← iteratedFDerivWithin_univ]
  rcases h.contDiffOn' le_rfl (by simp) with ⟨u, u_open, xu, hu⟩
  rw [← iteratedFDerivWithin_inter_open u_open xu]; rw [← iteratedFDerivWithin_inter_open u_open xu (s := univ)]
  apply iteratedFDerivWithin_subset
  · exact inter_subset_inter_left _ (subset_univ _)
  · exact hs.inter u_open
  · apply uniqueDiffOn_univ.inter u_open
  · simpa using hu
  · exact ⟨hx, xu⟩

中文:
定理 iteratedFDerivWithin_eq_iteratedFDeriv
  结论: {n : 自然数}
  证明: by
  rw [← iteratedFDerivWithin_univ]
  rcases h.contDiffOn' le_rfl (by simp) with ⟨u, u_open, xu, hu⟩
  rw [← iteratedFDerivWithin_inter_open u_open xu]; rw [← iteratedFDerivWithin_inter_open u_open xu (s := univ)]
  apply iteratedFDerivWithin_subset
  · exact inter_subset_inter_left _ (subset_univ _)
  · exact hs.inter u_open
  · apply uniqueDiffOn_univ.inter u_open
  · simpa using hu
  · exact ⟨hx, xu⟩

Depends on / 依赖: contDiffOn, h.contDiffOn, hs.inter, inter_subset_inter_left, iteratedFDerivWithin_inter_open, iteratedFDerivWithin_subset, iteratedFDerivWithin_univ, le_rfl, subset_univ, u_open, uniqueDiffOn_univ, uniqueDiffOn_univ.inter
-/
theorem iteratedFDerivWithin_eq_iteratedFDeriv {n : Nat}
    (hs : UniqueDiffOn 𝕜 s) (h : ContDiffAt 𝕜 n f x) (hx : x in s) :
    iteratedFDerivWithin 𝕜 n f s x = iteratedFDeriv 𝕜 n f x := by
  rw [← iteratedFDerivWithin_univ]
  rcases h.contDiffOn' le_rfl (by simp) with ⟨u, u_open, xu, hu⟩
  rw [← iteratedFDerivWithin_inter_open u_open xu]; rw [← iteratedFDerivWithin_inter_open u_open xu (s := univ)]
  apply iteratedFDerivWithin_subset
  · exact inter_subset_inter_left _ (subset_univ _)
  · exact hs.inter u_open
  · apply uniqueDiffOn_univ.inter u_open
  · simpa using hu
  · exact ⟨hx, xu⟩

/-! ### Smooth functions -/

variable (𝕜) in
/-- A function is continuously differentiable up to `n` if it admits derivatives up to
order `n`, which are continuous. Contrary to the case of definitions in domains (where derivatives
might not be unique) we do not need to localize the definition in space or time.
The parameter `n` belongs to `ℕ∞ω` (accessible in the `ContDiff` scope), i.e. it can be a natural
number, `∞`, or `ω`.

For `n = ω`, we require the function to be analytic. The precise
definition we give (all the derivatives should be analytic) is more involved to work around issues
when the space is not complete, but it is equivalent when the space is complete.
-/
@[fun_prop]
/--
Definition of `ContDiff` / `ContDiff` 的定义

English:
definition ContDiff
  signature: (n : Nat∞ω) (f : E -> F)
  body: match n with
  | ω => exists p : E -> FormalMultilinearSeries 𝕜 E F, HasFTaylorSeriesUpTo ⊤ f p
      ∧ forall i, AnalyticOnNhd 𝕜 (fun x => p x i) univ
  | (n : Nat∞) => exists p : E -> FormalMultilinearSeries 𝕜 E F, HasFTaylorSeriesUpTo n f p

中文:
定义 连续可微
  签名: (n : 自然数∞ω) (f : E -> F)
  定义体: match n with
  | ω => exists p : E -> FormalMultilinearSeries 𝕜 E F, HasFTaylorSeriesUpTo ⊤ f p
      ∧ forall i, AnalyticOnNhd 𝕜 (fun x => p x i) univ
  | (n : Nat∞) => exists p : E -> FormalMultilinearSeries 𝕜 E F, HasFTaylorSeriesUpTo n f p

Depends on / 依赖: AnalyticOnNhd, FormalMultilinearSeries, HasFTaylorSeriesUpTo
-/
def ContDiff (n : Nat∞ω) (f : E -> F) : Prop :=
  match n with
  | ω => exists p : E -> FormalMultilinearSeries 𝕜 E F, HasFTaylorSeriesUpTo ⊤ f p
      ∧ forall i, AnalyticOnNhd 𝕜 (fun x => p x i) univ
  | (n : Nat∞) => exists p : E -> FormalMultilinearSeries 𝕜 E F, HasFTaylorSeriesUpTo n f p

/--
theorem `HasFTaylorSeriesUpTo.contDiff` / 定理 `HasFTaylorSeriesUpTo.contDiff`

English:
theorem HasFTaylorSeriesUpTo.contDiff
  statement: {n : Nat∞} {f' : E -> FormalMultilinearSeries 𝕜 E F}
  proof: ⟨f', hf⟩

中文:
定理 有FTaylorSeriesUpTo.contDiff
  结论: {n : 自然数∞} {f' : E -> FormalMultilinearSeries 𝕜 E F}
  证明: ⟨f', hf⟩
-/
theorem HasFTaylorSeriesUpTo.contDiff {n : Nat∞} {f' : E -> FormalMultilinearSeries 𝕜 E F}
    (hf : HasFTaylorSeriesUpTo n f f') : ContDiff 𝕜 n f :=
  ⟨f', hf⟩

/--
theorem `contDiffOn_empty` / 定理 `contDiffOn_empty`

English:
theorem contDiffOn_empty
  statement: ContDiffOn 𝕜 n f ∅
  proof: fun _x hx => hx.elim

中文:
定理 contDiffOn_empty
  结论: ContDiffOn 𝕜 n f ∅
  证明: fun _x hx => hx.elim
-/
@[simp, fun_prop] theorem contDiffOn_empty : ContDiffOn 𝕜 n f ∅ := fun _x hx => hx.elim

/--
theorem `contDiffOn_univ` / 定理 `contDiffOn_univ`

English:
theorem contDiffOn_univ
  statement: ContDiffOn 𝕜 n f univ ↔ ContDiff 𝕜 n f
  proof: by
  match n with
  | ω =>
    constructor
    · intro H
      use ftaylorSeriesWithin 𝕜 f univ
      rw [← hasFTaylorSeriesUpToOn_univ_iff]
      refine ⟨H.ftaylorSeriesWithin uniqueDiffOn_univ, fun i => ?_⟩
      rw [← analyticOn_univ]
      exact H.analyticOn.iteratedFDerivWithin uniqueDiffOn_univ _
    · rintro ⟨p, hp, h'p⟩ x _
      exact ⟨univ, Filter.univ_sets _, p, (hp.hasFTaylorSeriesUpToOn univ).of_le le_top,
        fun i => (h'p i).analyticOn⟩
  | (n : Nat∞) =>
    constructor
    · intro H
      use ftaylorSeriesWithin 𝕜 f univ
      rw [← hasFTaylorSeriesUpToOn_univ_iff]
      exact H.ftaylorSeriesWithin uniqueDiffOn_univ
    · rintro ⟨p, hp⟩ x _ m hm
      exact ⟨univ, Filter.univ_sets _, p,
        (hp.hasFTaylorSeriesUpToOn univ).of_le (mod_cast hm)⟩

中文:
定理 contDiffOn_univ
  结论: ContDiffOn 𝕜 n f univ ↔ 连续可微 𝕜 n f
  证明: by
  match n with
  | ω =>
    constructor
    · intro H
      use ftaylorSeriesWithin 𝕜 f univ
      rw [← hasFTaylorSeriesUpToOn_univ_iff]
      refine ⟨H.ftaylorSeriesWithin uniqueDiffOn_univ, fun i => ?_⟩
      rw [← analyticOn_univ]
      exact H.analyticOn.iteratedFDerivWithin uniqueDiffOn_univ _
    · rintro ⟨p, hp, h'p⟩ x _
      exact ⟨univ, Filter.univ_sets _, p, (hp.hasFTaylorSeriesUpToOn univ).of_le le_top,
        fun i => (h'p i).analyticOn⟩
  | (n : Nat∞) =>
    constructor
    · intro H
      use ftaylorSeriesWithin 𝕜 f univ
      rw [← hasFTaylorSeriesUpToOn_univ_iff]
      exact H.ftaylorSeriesWithin uniqueDiffOn_univ
    · rintro ⟨p, hp⟩ x _ m hm
      exact ⟨univ, Filter.univ_sets _, p,
        (hp.hasFTaylorSeriesUpToOn univ).of_le (mod_cast hm)⟩

Depends on / 依赖: Filter, Filter.univ_sets, H.analyticOn.iteratedFDerivWithin, H.ftaylorSeriesWithin, analyticOn, analyticOn_univ, ftaylorSeriesWithin, hasFTaylorSeriesUpToOn, hasFTaylorSeriesUpToOn_, hasFTaylorSeriesUpToOn_univ_iff, hp.hasFTaylorSeriesUpToOn, iteratedFDerivWithin, le_top, of_le, uniqueDiffOn_univ, univ_sets
-/
theorem contDiffOn_univ : ContDiffOn 𝕜 n f univ ↔ ContDiff 𝕜 n f := by
  match n with
  | ω =>
    constructor
    · intro H
      use ftaylorSeriesWithin 𝕜 f univ
      rw [← hasFTaylorSeriesUpToOn_univ_iff]
      refine ⟨H.ftaylorSeriesWithin uniqueDiffOn_univ, fun i => ?_⟩
      rw [← analyticOn_univ]
      exact H.analyticOn.iteratedFDerivWithin uniqueDiffOn_univ _
    · rintro ⟨p, hp, h'p⟩ x _
      exact ⟨univ, Filter.univ_sets _, p, (hp.hasFTaylorSeriesUpToOn univ).of_le le_top,
        fun i => (h'p i).analyticOn⟩
  | (n : Nat∞) =>
    constructor
    · intro H
      use ftaylorSeriesWithin 𝕜 f univ
      rw [← hasFTaylorSeriesUpToOn_univ_iff]
      exact H.ftaylorSeriesWithin uniqueDiffOn_univ
    · rintro ⟨p, hp⟩ x _ m hm
      exact ⟨univ, Filter.univ_sets _, p,
        (hp.hasFTaylorSeriesUpToOn univ).of_le (mod_cast hm)⟩

/--
theorem `contDiff_iff_contDiffAt` / 定理 `contDiff_iff_contDiffAt`

English:
theorem contDiff_iff_contDiffAt
  statement: ContDiff 𝕜 n f ↔ forall x, ContDiffAt 𝕜 n f x
  proof: by
  simp [← contDiffOn_univ, ContDiffOn, ContDiffAt]

@[fun_prop]

中文:
定理 contDiff_iff_contDiffAt
  结论: 连续可微 𝕜 n f ↔ 对任意 x, ContDiffAt 𝕜 n f x
  证明: by
  simp [← contDiffOn_univ, ContDiffOn, ContDiffAt]

@[fun_prop]

Depends on / 依赖: ContDiffAt, ContDiffOn, contDiffOn_univ
-/
theorem contDiff_iff_contDiffAt : ContDiff 𝕜 n f ↔ forall x, ContDiffAt 𝕜 n f x := by
  simp [← contDiffOn_univ, ContDiffOn, ContDiffAt]

@[fun_prop]
/--
theorem `ContDiff.contDiffAt` / 定理 `ContDiff.contDiffAt`

English:
theorem ContDiff.contDiffAt
  given: (h : ContDiff 𝕜 n f)
  statement: ContDiffAt 𝕜 n f x
  proof: contDiff_iff_contDiffAt.1 h x

@[fun_prop]

中文:
定理 连续可微.contDiffAt
  条件: (h : 连续可微 𝕜 n f)
  结论: ContDiffAt 𝕜 n f x
  证明: contDiff_iff_contDiffAt.1 h x

@[fun_prop]

Depends on / 依赖: contDiff_iff_contDiffAt
-/
theorem ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiffAt 𝕜 n f x :=
  contDiff_iff_contDiffAt.1 h x

@[fun_prop]
/--
theorem `ContDiff.contDiffWithinAt` / 定理 `ContDiff.contDiffWithinAt`

English:
theorem ContDiff.contDiffWithinAt
  given: (h : ContDiff 𝕜 n f)
  statement: ContDiffWithinAt 𝕜 n f s x
  proof: h.contDiffAt.contDiffWithinAt

中文:
定理 连续可微.contDiffWithinAt
  条件: (h : 连续可微 𝕜 n f)
  结论: ContDiffWithinAt 𝕜 n f s x
  证明: h.contDiffAt.contDiffWithinAt

Depends on / 依赖: contDiffAt, contDiffWithinAt, h.contDiffAt.contDiffWithinAt
-/
theorem ContDiff.contDiffWithinAt (h : ContDiff 𝕜 n f) : ContDiffWithinAt 𝕜 n f s x :=
  h.contDiffAt.contDiffWithinAt

/--
theorem `contDiff_infty` / 定理 `contDiff_infty`

English:
theorem contDiff_infty
  statement: ContDiff 𝕜 ∞ f ↔ forall n : Nat, ContDiff 𝕜 n f
  proof: by
  simp [contDiffOn_univ.symm, contDiffOn_infty]

中文:
定理 contDiff_infty
  结论: 连续可微 𝕜 ∞ f ↔ 对任意 n : 自然数, 连续可微 𝕜 n f
  证明: by
  simp [contDiffOn_univ.symm, contDiffOn_infty]

Depends on / 依赖: contDiffOn_infty, contDiffOn_univ, contDiffOn_univ.symm
-/
theorem contDiff_infty : ContDiff 𝕜 ∞ f ↔ forall n : Nat, ContDiff 𝕜 n f := by
  simp [contDiffOn_univ.symm, contDiffOn_infty]

/--
theorem `contDiff_all_iff_nat` / 定理 `contDiff_all_iff_nat`

English:
theorem contDiff_all_iff_nat
  statement: (forall n : Nat∞, ContDiff 𝕜 n f) ↔ forall n : Nat, ContDiff 𝕜 n f
  proof: by
  simp only [← contDiffOn_univ, contDiffOn_all_iff_nat]

@[fun_prop]

中文:
定理 contDiff_all_iff_nat
  结论: (对任意 n : 自然数∞, 连续可微 𝕜 n f) ↔ 对任意 n : 自然数, 连续可微 𝕜 n f
  证明: by
  simp only [← contDiffOn_univ, contDiffOn_all_iff_nat]

@[fun_prop]

Depends on / 依赖: contDiffOn_all_iff_nat, contDiffOn_univ
-/
theorem contDiff_all_iff_nat : (forall n : Nat∞, ContDiff 𝕜 n f) ↔ forall n : Nat, ContDiff 𝕜 n f := by
  simp only [← contDiffOn_univ, contDiffOn_all_iff_nat]

@[fun_prop]
/--
theorem `ContDiff.contDiffOn` / 定理 `ContDiff.contDiffOn`

English:
theorem ContDiff.contDiffOn
  given: (h : ContDiff 𝕜 n f)
  statement: ContDiffOn 𝕜 n f s
  proof: (contDiffOn_univ.2 h).mono (subset_univ _)

@[simp]

中文:
定理 连续可微.contDiffOn
  条件: (h : 连续可微 𝕜 n f)
  结论: ContDiffOn 𝕜 n f s
  证明: (contDiffOn_univ.2 h).mono (subset_univ _)

@[simp]

Depends on / 依赖: contDiffOn_univ, subset_univ
-/
theorem ContDiff.contDiffOn (h : ContDiff 𝕜 n f) : ContDiffOn 𝕜 n f s :=
  (contDiffOn_univ.2 h).mono (subset_univ _)

@[simp]
/--
theorem `contDiff_zero` / 定理 `contDiff_zero`

English:
theorem contDiff_zero
  statement: ContDiff 𝕜 0 f ↔ Continuous f
  proof: by
  rw [← contDiffOn_univ]; rw [← continuousOn_univ]
  exact contDiffOn_zero

中文:
定理 contDiff_zero
  结论: 连续可微 𝕜 0 f ↔ 连续 f
  证明: by
  rw [← contDiffOn_univ]; rw [← continuousOn_univ]
  exact contDiffOn_zero

Depends on / 依赖: contDiffOn_univ, contDiffOn_zero, continuousOn_univ
-/
theorem contDiff_zero : ContDiff 𝕜 0 f ↔ Continuous f := by
  rw [← contDiffOn_univ]; rw [← continuousOn_univ]
  exact contDiffOn_zero

/--
theorem `contDiffAt_zero` / 定理 `contDiffAt_zero`

English:
theorem contDiffAt_zero
  statement: ContDiffAt 𝕜 0 f x ↔ exists u in 𝓝 x, ContinuousOn f u
  proof: by
  rw [← contDiffWithinAt_univ]; simp [contDiffWithinAt_zero, nhdsWithin_univ]

中文:
定理 contDiffAt_zero
  结论: ContDiffAt 𝕜 0 f x ↔ 存在 u in 𝓝 x, ContinuousOn f u
  证明: by
  rw [← contDiffWithinAt_univ]; simp [contDiffWithinAt_zero, nhdsWithin_univ]

Depends on / 依赖: contDiffWithinAt_univ, contDiffWithinAt_zero, nhdsWithin_univ
-/
theorem contDiffAt_zero : ContDiffAt 𝕜 0 f x ↔ exists u in 𝓝 x, ContinuousOn f u := by
  rw [← contDiffWithinAt_univ]; simp [contDiffWithinAt_zero, nhdsWithin_univ]

/--
theorem `contDiffAt_one_iff` / 定理 `contDiffAt_one_iff`

English:
theorem contDiffAt_one_iff
  proof: by
  rw [show (1 : Nat∞ω) = (0 : Nat) + 1 from rfl]
  simp_rw [contDiffAt_succ_iff_hasFDerivAt, show ((0 : Nat) : Nat∞ω) = 0 from rfl,
    contDiffAt_zero, exists_mem_and_iff antitone_bforall antitone_continuousOn, and_comm]

@[fun_prop]

中文:
定理 contDiffAt_one_iff
  证明: by
  rw [show (1 : Nat∞ω) = (0 : Nat) + 1 from rfl]
  simp_rw [contDiffAt_succ_iff_hasFDerivAt, show ((0 : Nat) : Nat∞ω) = 0 from rfl,
    contDiffAt_zero, exists_mem_and_iff antitone_bforall antitone_continuousOn, and_comm]

@[fun_prop]

Depends on / 依赖: and_comm, antitone_bforall, antitone_continuousOn, contDiffAt_succ_iff_hasFDerivAt, contDiffAt_zero, exists_mem_and_iff, simp_rw
-/
theorem contDiffAt_one_iff :
    ContDiffAt 𝕜 1 f x ↔
      exists f' : E -> E ->L[𝕜] F, exists u in 𝓝 x, ContinuousOn f' u ∧ forall x in u, HasFDerivAt f (f' x) x := by
  rw [show (1 : Nat∞ω) = (0 : Nat) + 1 from rfl]
  simp_rw [contDiffAt_succ_iff_hasFDerivAt, show ((0 : Nat) : Nat∞ω) = 0 from rfl,
    contDiffAt_zero, exists_mem_and_iff antitone_bforall antitone_continuousOn, and_comm]

@[fun_prop]
/--
theorem `ContDiff.of_le` / 定理 `ContDiff.of_le`

English:
theorem ContDiff.of_le
  given: (h : ContDiff 𝕜 n f) (hmn : m <= n)
  statement: ContDiff 𝕜 m f
  proof: contDiffOn_univ.1 (contDiffOn_univ.2 h).of_le hmn

中文:
定理 连续可微.of_le
  条件: (h : 连续可微 𝕜 n f) (hmn : m <= n)
  结论: 连续可微 𝕜 m f
  证明: contDiffOn_univ.1 (contDiffOn_univ.2 h).of_le hmn

Depends on / 依赖: contDiffOn_univ, of_le
-/
theorem ContDiff.of_le (h : ContDiff 𝕜 n f) (hmn : m <= n) : ContDiff 𝕜 m f :=
contDiffOn_univ.1 (contDiffOn_univ.2 h).of_le hmn

/--
theorem `ContDiff.of_succ` / 定理 `ContDiff.of_succ`

English:
theorem ContDiff.of_succ
  given: (h : ContDiff 𝕜 (n + 1) f)
  statement: ContDiff 𝕜 n f
  proof: h.of_le le_self_add

中文:
定理 连续可微.of_succ
  条件: (h : 连续可微 𝕜 (n + 1) f)
  结论: 连续可微 𝕜 n f
  证明: h.of_le le_self_add

Depends on / 依赖: h.of_le, le_self_add, of_le
-/
theorem ContDiff.of_succ (h : ContDiff 𝕜 (n + 1) f) : ContDiff 𝕜 n f :=
  h.of_le le_self_add

/--
theorem `ContDiff.one_of_succ` / 定理 `ContDiff.one_of_succ`

English:
theorem ContDiff.one_of_succ
  given: (h : ContDiff 𝕜 (n + 1) f)
  statement: ContDiff 𝕜 1 f
  proof: by
  apply h.of_le le_add_self

@[fun_prop]

中文:
定理 连续可微.one_of_succ
  条件: (h : 连续可微 𝕜 (n + 1) f)
  结论: 连续可微 𝕜 1 f
  证明: by
  apply h.of_le le_add_self

@[fun_prop]

Depends on / 依赖: h.of_le, le_add_self, of_le
-/
theorem ContDiff.one_of_succ (h : ContDiff 𝕜 (n + 1) f) : ContDiff 𝕜 1 f := by
  apply h.of_le le_add_self

@[fun_prop]
/--
theorem `ContDiff.continuous` / 定理 `ContDiff.continuous`

English:
theorem ContDiff.continuous
  given: (h : ContDiff 𝕜 n f)
  statement: Continuous f
  proof: contDiff_zero.1 (h.of_le bot_le)

@[fun_prop]

中文:
定理 连续可微.continuous
  条件: (h : 连续可微 𝕜 n f)
  结论: 连续 f
  证明: contDiff_zero.1 (h.of_le bot_le)

@[fun_prop]

Depends on / 依赖: bot_le, contDiff_zero, h.of_le, of_le
-/
theorem ContDiff.continuous (h : ContDiff 𝕜 n f) : Continuous f :=
  contDiff_zero.1 (h.of_le bot_le)

@[fun_prop]
/--
theorem `ContDiff.continuous_zero` / 定理 `ContDiff.continuous_zero`

English:
theorem ContDiff.continuous_zero
  given: (h : ContDiff 𝕜 0 f)
  statement: Continuous f
  proof: contDiff_zero.1 (h.of_le bot_le)

中文:
定理 连续可微.continuous_zero
  条件: (h : 连续可微 𝕜 0 f)
  结论: 连续 f
  证明: contDiff_zero.1 (h.of_le bot_le)

Depends on / 依赖: bot_le, contDiff_zero, h.of_le, of_le
-/
theorem ContDiff.continuous_zero (h : ContDiff 𝕜 0 f) : Continuous f :=
  contDiff_zero.1 (h.of_le bot_le)

/-- If a function is `C^n` with `n ≥ 1`, then it is differentiable. -/
@[fun_prop]
/--
theorem `ContDiff.differentiable` / 定理 `ContDiff.differentiable`

English:
theorem ContDiff.differentiable
  given: (h : ContDiff 𝕜 n f) (hn : n != 0)
  statement: Differentiable 𝕜 f
  proof: differentiableOn_univ.1 (contDiffOn_univ.2 h).differentiableOn hn

@[fun_prop]

中文:
定理 连续可微.differentiable
  条件: (h : 连续可微 𝕜 n f) (hn : n != 0)
  结论: 可微 𝕜 f
  证明: differentiableOn_univ.1 (contDiffOn_univ.2 h).differentiableOn hn

@[fun_prop]

Depends on / 依赖: contDiffOn_univ, differentiableOn, differentiableOn_univ
-/
theorem ContDiff.differentiable (h : ContDiff 𝕜 n f) (hn : n != 0) : Differentiable 𝕜 f :=
differentiableOn_univ.1 (contDiffOn_univ.2 h).differentiableOn hn

@[fun_prop]
/--
theorem `ContDiff.differentiable_one` / 定理 `ContDiff.differentiable_one`

English:
theorem ContDiff.differentiable_one
  given: (h : ContDiff 𝕜 1 f)
  statement: Differentiable 𝕜 f
  proof: differentiableOn_univ.1 (contDiffOn_univ.2 h).differentiableOn one_ne_zero

中文:
定理 连续可微.differentiable_one
  条件: (h : 连续可微 𝕜 1 f)
  结论: 可微 𝕜 f
  证明: differentiableOn_univ.1 (contDiffOn_univ.2 h).differentiableOn one_ne_zero

Depends on / 依赖: contDiffOn_univ, differentiableOn, differentiableOn_univ, one_ne_zero
-/
theorem ContDiff.differentiable_one (h : ContDiff 𝕜 1 f) : Differentiable 𝕜 f :=
differentiableOn_univ.1 (contDiffOn_univ.2 h).differentiableOn one_ne_zero

/--
theorem `contDiff_iff_forall_nat_le` / 定理 `contDiff_iff_forall_nat_le`

English:
theorem contDiff_iff_forall_nat_le
  given: {n : Nat∞}
  proof: by
  simp_rw [← contDiffOn_univ]; exact contDiffOn_iff_forall_nat_le

中文:
定理 contDiff_iff_对任意_nat_le
  条件: {n : 自然数∞}
  证明: by
  simp_rw [← contDiffOn_univ]; exact contDiffOn_iff_forall_nat_le

Depends on / 依赖: contDiffOn_iff_forall_nat_le, contDiffOn_univ, simp_rw
-/
theorem contDiff_iff_forall_nat_le {n : Nat∞} :
    ContDiff 𝕜 n f ↔ forall m : Nat, ↑m <= n -> ContDiff 𝕜 m f := by
  simp_rw [← contDiffOn_univ]; exact contDiffOn_iff_forall_nat_le

/--
theorem `contDiff_succ_iff_hasFDerivAt` / 定理 `contDiff_succ_iff_hasFDerivAt`

English:
theorem contDiff_succ_iff_hasFDerivAt
  given: {n : Nat}
  proof: by
  simp only [← contDiffOn_univ, ← hasFDerivWithinAt_univ, Set.mem_univ, forall_true_left,
    contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn uniqueDiffOn_univ,
    WithTop.natCast_ne_top, analyticOn_univ, false_implies, true_and]

中文:
定理 contDiff_succ_iff_hasFDerivAt
  条件: {n : 自然数}
  证明: by
  simp only [← contDiffOn_univ, ← hasFDerivWithinAt_univ, Set.mem_univ, forall_true_left,
    contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn uniqueDiffOn_univ,
    WithTop.natCast_ne_top, analyticOn_univ, false_implies, true_and]

Depends on / 依赖: Set.mem_univ, WithTop, WithTop.natCast_ne_top, analyticOn_univ, contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn, contDiffOn_univ, false_implies, forall_true_left, hasFDerivWithinAt_univ, mem_univ, natCast_ne_top, true_and, uniqueDiffOn_univ
-/
theorem contDiff_succ_iff_hasFDerivAt {n : Nat} :
    ContDiff 𝕜 (n + 1) f ↔
      exists f' : E -> E ->L[𝕜] F, ContDiff 𝕜 n f' ∧ forall x, HasFDerivAt f (f' x) x := by
  simp only [← contDiffOn_univ, ← hasFDerivWithinAt_univ, Set.mem_univ, forall_true_left,
    contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn uniqueDiffOn_univ,
    WithTop.natCast_ne_top, analyticOn_univ, false_implies, true_and]

/--
theorem `contDiff_one_iff_hasFDerivAt` / 定理 `contDiff_one_iff_hasFDerivAt`

English:
theorem contDiff_one_iff_hasFDerivAt
  statement: ContDiff 𝕜 1 f ↔
  proof: by
  convert! contDiff_succ_iff_hasFDerivAt using 4; simp

中文:
定理 contDiff_one_iff_hasFDerivAt
  结论: 连续可微 𝕜 1 f ↔
  证明: by
  convert! contDiff_succ_iff_hasFDerivAt using 4; simp

Depends on / 依赖: contDiff_succ_iff_hasFDerivAt, convert
-/
theorem contDiff_one_iff_hasFDerivAt : ContDiff 𝕜 1 f ↔
    exists f' : E -> E ->L[𝕜] F, Continuous f' ∧ forall x, HasFDerivAt f (f' x) x := by
  convert! contDiff_succ_iff_hasFDerivAt using 4; simp

/--
theorem `AnalyticOn.contDiff` / 定理 `AnalyticOn.contDiff`

English:
theorem AnalyticOn.contDiff
  given: (hf : AnalyticOn 𝕜 f univ)
  statement: ContDiff 𝕜 n f
  proof: by
  rw [← contDiffOn_univ]
  exact hf.contDiffOn (n := n) uniqueDiffOn_univ

中文:
定理 AnalyticOn.contDiff
  条件: (hf : AnalyticOn 𝕜 f univ)
  结论: 连续可微 𝕜 n f
  证明: by
  rw [← contDiffOn_univ]
  exact hf.contDiffOn (n := n) uniqueDiffOn_univ

Depends on / 依赖: contDiffOn, contDiffOn_univ, hf.contDiffOn, uniqueDiffOn_univ
-/
theorem AnalyticOn.contDiff (hf : AnalyticOn 𝕜 f univ) : ContDiff 𝕜 n f := by
  rw [← contDiffOn_univ]
  exact hf.contDiffOn (n := n) uniqueDiffOn_univ

/--
theorem `AnalyticOnNhd.contDiff` / 定理 `AnalyticOnNhd.contDiff`

English:
theorem AnalyticOnNhd.contDiff
  given: (hf : AnalyticOnNhd 𝕜 f univ)
  statement: ContDiff 𝕜 n f
  proof: hf.analyticOn.contDiff

中文:
定理 AnalyticOnNhd.contDiff
  条件: (hf : AnalyticOnNhd 𝕜 f univ)
  结论: 连续可微 𝕜 n f
  证明: hf.analyticOn.contDiff

Depends on / 依赖: analyticOn, contDiff, hf.analyticOn.contDiff
-/
theorem AnalyticOnNhd.contDiff (hf : AnalyticOnNhd 𝕜 f univ) : ContDiff 𝕜 n f :=
  hf.analyticOn.contDiff

/--
theorem `ContDiff.analyticOnNhd` / 定理 `ContDiff.analyticOnNhd`

English:
theorem ContDiff.analyticOnNhd
  given: (h : ContDiff 𝕜 ω f)
  statement: AnalyticOnNhd 𝕜 f s
  proof: by
  rw [← contDiffOn_univ] at h
  have := h.analyticOn
  rw [analyticOn_univ] at this
  exact this.mono (subset_univ _)

中文:
定理 连续可微.analyticOnNhd
  条件: (h : 连续可微 𝕜 ω f)
  结论: AnalyticOnNhd 𝕜 f s
  证明: by
  rw [← contDiffOn_univ] at h
  have := h.analyticOn
  rw [analyticOn_univ] at this
  exact this.mono (subset_univ _)

Depends on / 依赖: analyticOn, analyticOn_univ, contDiffOn_univ, h.analyticOn, subset_univ, this.mono
-/
theorem ContDiff.analyticOnNhd (h : ContDiff 𝕜 ω f) : AnalyticOnNhd 𝕜 f s := by
  rw [← contDiffOn_univ] at h
  have := h.analyticOn
  rw [analyticOn_univ] at this
  exact this.mono (subset_univ _)

/--
theorem `contDiff_omega_iff_analyticOnNhd` / 定理 `contDiff_omega_iff_analyticOnNhd`

English:
theorem contDiff_omega_iff_analyticOnNhd
  proof: ⟨fun h => h.analyticOnNhd, fun h => h.contDiff⟩

中文:
定理 contDiff_omega_iff_analyticOnNhd
  证明: ⟨fun h => h.analyticOnNhd, fun h => h.contDiff⟩

Depends on / 依赖: analyticOnNhd, contDiff, h.analyticOnNhd, h.contDiff
-/
theorem contDiff_omega_iff_analyticOnNhd :
    ContDiff 𝕜 ω f ↔ AnalyticOnNhd 𝕜 f univ :=
  ⟨fun h => h.analyticOnNhd, fun h => h.contDiff⟩

/-! ### Iterated derivative -/

/--
theorem `ContDiff.ftaylorSeries` / 定理 `ContDiff.ftaylorSeries`

English:
theorem ContDiff.ftaylorSeries
  given: (hf : ContDiff 𝕜 n f)
  proof: by
  simp only [← contDiffOn_univ, ← hasFTaylorSeriesUpToOn_univ_iff, ← ftaylorSeriesWithin_univ]
    at hf ⊢
  exact ContDiffOn.ftaylorSeriesWithin hf uniqueDiffOn_univ

中文:
定理 连续可微.ftaylorSeries
  条件: (hf : 连续可微 𝕜 n f)
  证明: by
  simp only [← contDiffOn_univ, ← hasFTaylorSeriesUpToOn_univ_iff, ← ftaylorSeriesWithin_univ]
    at hf ⊢
  exact ContDiffOn.ftaylorSeriesWithin hf uniqueDiffOn_univ

Depends on / 依赖: ContDiffOn, ContDiffOn.ftaylorSeriesWithin, contDiffOn_univ, ftaylorSeriesWithin, ftaylorSeriesWithin_univ, hasFTaylorSeriesUpToOn_univ_iff, uniqueDiffOn_univ
-/
theorem ContDiff.ftaylorSeries (hf : ContDiff 𝕜 n f) :
    HasFTaylorSeriesUpTo n f (ftaylorSeries 𝕜 f) := by
  simp only [← contDiffOn_univ, ← hasFTaylorSeriesUpToOn_univ_iff, ← ftaylorSeriesWithin_univ]
    at hf ⊢
  exact ContDiffOn.ftaylorSeriesWithin hf uniqueDiffOn_univ

/--
theorem `contDiff_iff_ftaylorSeries` / 定理 `contDiff_iff_ftaylorSeries`

English:
theorem contDiff_iff_ftaylorSeries
  given: {n : Nat∞}
  proof: by
  constructor
  · rw [← contDiffOn_univ, ← hasFTaylorSeriesUpToOn_univ_iff, ← ftaylorSeriesWithin_univ]
    exact fun h => ContDiffOn.ftaylorSeriesWithin h uniqueDiffOn_univ
  · exact fun h => ⟨ftaylorSeries 𝕜 f, h⟩

中文:
定理 contDiff_iff_ftaylorSeries
  条件: {n : 自然数∞}
  证明: by
  constructor
  · rw [← contDiffOn_univ, ← hasFTaylorSeriesUpToOn_univ_iff, ← ftaylorSeriesWithin_univ]
    exact fun h => ContDiffOn.ftaylorSeriesWithin h uniqueDiffOn_univ
  · exact fun h => ⟨ftaylorSeries 𝕜 f, h⟩

Depends on / 依赖: ContDiffOn, ContDiffOn.ftaylorSeriesWithin, contDiffOn_univ, ftaylorSeries, ftaylorSeriesWithin, ftaylorSeriesWithin_univ, hasFTaylorSeriesUpToOn_univ_iff, uniqueDiffOn_univ
-/
theorem contDiff_iff_ftaylorSeries {n : Nat∞} :
    ContDiff 𝕜 n f ↔ HasFTaylorSeriesUpTo n f (ftaylorSeries 𝕜 f) := by
  constructor
  · rw [← contDiffOn_univ, ← hasFTaylorSeriesUpToOn_univ_iff, ← ftaylorSeriesWithin_univ]
    exact fun h => ContDiffOn.ftaylorSeriesWithin h uniqueDiffOn_univ
  · exact fun h => ⟨ftaylorSeries 𝕜 f, h⟩

/--
theorem `contDiff_iff_continuous_differentiable` / 定理 `contDiff_iff_continuous_differentiable`

English:
theorem contDiff_iff_continuous_differentiable
  given: {n : Nat∞}
  proof: by
  simp [contDiffOn_univ.symm, continuousOn_univ, differentiableOn_univ.symm,
    iteratedFDerivWithin_univ, contDiffOn_iff_continuousOn_differentiableOn uniqueDiffOn_univ]

中文:
定理 contDiff_iff_continuous_differentiable
  条件: {n : 自然数∞}
  证明: by
  simp [contDiffOn_univ.symm, continuousOn_univ, differentiableOn_univ.symm,
    iteratedFDerivWithin_univ, contDiffOn_iff_continuousOn_differentiableOn uniqueDiffOn_univ]

Depends on / 依赖: contDiffOn_iff_continuousOn_differentiableOn, contDiffOn_univ, contDiffOn_univ.symm, continuousOn_univ, differentiableOn_univ, differentiableOn_univ.symm, iteratedFDerivWithin_univ, uniqueDiffOn_univ
-/
theorem contDiff_iff_continuous_differentiable {n : Nat∞} :
    ContDiff 𝕜 n f ↔
      (forall m : Nat, m <= n -> Continuous fun x => iteratedFDeriv 𝕜 m f x) ∧
        forall m : Nat, m < n -> Differentiable 𝕜 fun x => iteratedFDeriv 𝕜 m f x := by
  simp [contDiffOn_univ.symm, continuousOn_univ, differentiableOn_univ.symm,
    iteratedFDerivWithin_univ, contDiffOn_iff_continuousOn_differentiableOn uniqueDiffOn_univ]

/--
theorem `contDiff_nat_iff_continuous_differentiable` / 定理 `contDiff_nat_iff_continuous_differentiable`

English:
theorem contDiff_nat_iff_continuous_differentiable
  given: {n : Nat}
  proof: by
  rw [← WithTop.coe_natCast]; rw [contDiff_iff_continuous_differentiable]
  simp

中文:
定理 contDiff_nat_iff_continuous_differentiable
  条件: {n : 自然数}
  证明: by
  rw [← WithTop.coe_natCast]; rw [contDiff_iff_continuous_differentiable]
  simp

Depends on / 依赖: WithTop, WithTop.coe_natCast, coe_natCast, contDiff_iff_continuous_differentiable
-/
theorem contDiff_nat_iff_continuous_differentiable {n : Nat} :
    ContDiff 𝕜 n f ↔
      (forall m : Nat, m <= n -> Continuous fun x => iteratedFDeriv 𝕜 m f x) ∧
        forall m : Nat, m < n -> Differentiable 𝕜 fun x => iteratedFDeriv 𝕜 m f x := by
  rw [← WithTop.coe_natCast]; rw [contDiff_iff_continuous_differentiable]
  simp

/--
theorem `ContDiff.continuous_iteratedFDeriv` / 定理 `ContDiff.continuous_iteratedFDeriv`

English:
theorem ContDiff.continuous_iteratedFDeriv
  given: {m : Nat} (hm : m <= n) (hf : ContDiff 𝕜 n f)
  proof: (contDiff_iff_continuous_differentiable.mp (hf.of_le hm)).1 m le_rfl

@[fun_prop]

中文:
定理 连续可微.continuous_iteratedFDeriv
  条件: {m : 自然数} (hm : m <= n) (hf : 连续可微 𝕜 n f)
  证明: (contDiff_iff_continuous_differentiable.mp (hf.of_le hm)).1 m le_rfl

@[fun_prop]

Depends on / 依赖: contDiff_iff_continuous_differentiable, contDiff_iff_continuous_differentiable.mp, hf.of_le, le_rfl, of_le
-/
theorem ContDiff.continuous_iteratedFDeriv {m : Nat} (hm : m <= n) (hf : ContDiff 𝕜 n f) :
    Continuous fun x => iteratedFDeriv 𝕜 m f x :=
  (contDiff_iff_continuous_differentiable.mp (hf.of_le hm)).1 m le_rfl

@[fun_prop]
/--
theorem `ContDiff.continuous_iteratedFDeriv'` / 定理 `ContDiff.continuous_iteratedFDeriv'`

English:
theorem ContDiff.continuous_iteratedFDeriv'
  given: {m : Nat} (hf : ContDiff 𝕜 m f)
  proof: (contDiff_iff_continuous_differentiable.mp hf).1 m le_rfl

中文:
定理 连续可微.continuous_iteratedFDeriv'
  条件: {m : 自然数} (hf : 连续可微 𝕜 m f)
  证明: (contDiff_iff_continuous_differentiable.mp hf).1 m le_rfl

Depends on / 依赖: contDiff_iff_continuous_differentiable, contDiff_iff_continuous_differentiable.mp, le_rfl
-/
theorem ContDiff.continuous_iteratedFDeriv' {m : Nat} (hf : ContDiff 𝕜 m f) :
    Continuous fun x => iteratedFDeriv 𝕜 m f x :=
  (contDiff_iff_continuous_differentiable.mp hf).1 m le_rfl

/--
theorem `ContDiff.differentiable_iteratedFDeriv` / 定理 `ContDiff.differentiable_iteratedFDeriv`

English:
theorem ContDiff.differentiable_iteratedFDeriv
  given: {m : Nat} (hm : m < n) (hf : ContDiff 𝕜 n f)
  proof: (contDiff_iff_continuous_differentiable.mp
    (hf.of_le (ENat.add_one_natCast_le_withTop_of_lt hm))).2 m (mod_cast lt_add_one m)

中文:
定理 连续可微.differentiable_iteratedFDeriv
  条件: {m : 自然数} (hm : m < n) (hf : 连续可微 𝕜 n f)
  证明: (contDiff_iff_continuous_differentiable.mp
    (hf.of_le (ENat.add_one_natCast_le_withTop_of_lt hm))).2 m (mod_cast lt_add_one m)

Depends on / 依赖: ENat.add_one_natCast_le_withTop_of_lt, add_one_natCast_le_withTop_of_lt, contDiff_iff_continuous_differentiable, contDiff_iff_continuous_differentiable.mp, hf.of_le, lt_add_one, mod_cast, of_le
-/
theorem ContDiff.differentiable_iteratedFDeriv {m : Nat} (hm : m < n) (hf : ContDiff 𝕜 n f) :
    Differentiable 𝕜 fun x => iteratedFDeriv 𝕜 m f x :=
  (contDiff_iff_continuous_differentiable.mp
    (hf.of_le (ENat.add_one_natCast_le_withTop_of_lt hm))).2 m (mod_cast lt_add_one m)

/--
theorem `contDiff_of_differentiable_iteratedFDeriv` / 定理 `contDiff_of_differentiable_iteratedFDeriv`

English:
theorem contDiff_of_differentiable_iteratedFDeriv
  statement: {n : Nat∞}
  proof: contDiff_iff_continuous_differentiable.2
    ⟨fun m hm => (h m hm).continuous, fun m hm => h m (le_of_lt hm)⟩

中文:
定理 contDiff_of_differentiable_iteratedFDeriv
  结论: {n : 自然数∞}
  证明: contDiff_iff_continuous_differentiable.2
    ⟨fun m hm => (h m hm).continuous, fun m hm => h m (le_of_lt hm)⟩

Depends on / 依赖: contDiff_iff_continuous_differentiable, continuous, le_of_lt
-/
theorem contDiff_of_differentiable_iteratedFDeriv {n : Nat∞}
    (h : forall m : Nat, m <= n -> Differentiable 𝕜 (iteratedFDeriv 𝕜 m f)) : ContDiff 𝕜 n f :=
  contDiff_iff_continuous_differentiable.2
    ⟨fun m hm => (h m hm).continuous, fun m hm => h m (le_of_lt hm)⟩

/--
theorem `contDiff_succ_iff_fderiv` / 定理 `contDiff_succ_iff_fderiv`

English:
theorem contDiff_succ_iff_fderiv
  proof: by
  simp only [← contDiffOn_univ, ← differentiableOn_univ, ← fderivWithin_univ,
    contDiffOn_succ_iff_fderivWithin uniqueDiffOn_univ, analyticOn_univ]

中文:
定理 contDiff_succ_iff_fderiv
  证明: by
  simp only [← contDiffOn_univ, ← differentiableOn_univ, ← fderivWithin_univ,
    contDiffOn_succ_iff_fderivWithin uniqueDiffOn_univ, analyticOn_univ]

Depends on / 依赖: analyticOn_univ, contDiffOn_succ_iff_fderivWithin, contDiffOn_univ, differentiableOn_univ, fderivWithin_univ, uniqueDiffOn_univ
-/
theorem contDiff_succ_iff_fderiv :
    ContDiff 𝕜 (n + 1) f ↔ Differentiable 𝕜 f ∧ (n = ω -> AnalyticOnNhd 𝕜 f univ) ∧
      ContDiff 𝕜 n (fderiv 𝕜 f) := by
  simp only [← contDiffOn_univ, ← differentiableOn_univ, ← fderivWithin_univ,
    contDiffOn_succ_iff_fderivWithin uniqueDiffOn_univ, analyticOn_univ]

/--
theorem `contDiff_one_iff_fderiv` / 定理 `contDiff_one_iff_fderiv`

English:
theorem contDiff_one_iff_fderiv
  proof: by
  rw [← zero_add 1]; rw [contDiff_succ_iff_fderiv]
  simp

中文:
定理 contDiff_one_iff_fderiv
  证明: by
  rw [← zero_add 1]; rw [contDiff_succ_iff_fderiv]
  simp

Depends on / 依赖: contDiff_succ_iff_fderiv, zero_add
-/
theorem contDiff_one_iff_fderiv :
    ContDiff 𝕜 1 f ↔ Differentiable 𝕜 f ∧ Continuous (fderiv 𝕜 f) := by
  rw [← zero_add 1]; rw [contDiff_succ_iff_fderiv]
  simp

/--
theorem `contDiff_infty_iff_fderiv` / 定理 `contDiff_infty_iff_fderiv`

English:
theorem contDiff_infty_iff_fderiv
  proof: by
  rw [← ENat.coe_top_add_one]; rw [contDiff_succ_iff_fderiv]
  simp

中文:
定理 contDiff_infty_iff_fderiv
  证明: by
  rw [← ENat.coe_top_add_one]; rw [contDiff_succ_iff_fderiv]
  simp

Depends on / 依赖: ENat.coe_top_add_one, coe_top_add_one, contDiff_succ_iff_fderiv
-/
theorem contDiff_infty_iff_fderiv :
    ContDiff 𝕜 ∞ f ↔ Differentiable 𝕜 f ∧ ContDiff 𝕜 ∞ (fderiv 𝕜 f) := by
  rw [← ENat.coe_top_add_one]; rw [contDiff_succ_iff_fderiv]
  simp

/--
theorem `ContDiff.continuous_fderiv` / 定理 `ContDiff.continuous_fderiv`

English:
theorem ContDiff.continuous_fderiv
  given: (h : ContDiff 𝕜 n f) (hn : n != 0)
  proof: (contDiff_one_iff_fderiv.1 (h.of_le <| ENat.one_le_iff_ne_zero_withTop.mpr hn)).2

中文:
定理 连续可微.continuous_fderiv
  条件: (h : 连续可微 𝕜 n f) (hn : n != 0)
  证明: (contDiff_one_iff_fderiv.1 (h.of_le <| ENat.one_le_iff_ne_zero_withTop.mpr hn)).2

Depends on / 依赖: ENat.one_le_iff_ne_zero_withTop.mpr, contDiff_one_iff_fderiv, h.of_le, of_le, one_le_iff_ne_zero_withTop
-/
theorem ContDiff.continuous_fderiv (h : ContDiff 𝕜 n f) (hn : n != 0) :
    Continuous (fderiv 𝕜 f) :=
  (contDiff_one_iff_fderiv.1 (h.of_le <| ENat.one_le_iff_ne_zero_withTop.mpr hn)).2

/--
theorem `ContDiff.continuous_fderiv_apply` / 定理 `ContDiff.continuous_fderiv_apply`

English:
theorem ContDiff.continuous_fderiv_apply
  given: (h : ContDiff 𝕜 n f) (hn : n != 0)
  proof: have A : Continuous fun q : (E ->L[𝕜] F) × E => q.1 q.2 := isBoundedBilinearMap_apply.continuous
  have B : Continuous fun p : E × E => (fderiv 𝕜 f p.1, p.2) :=
    ((h.continuous_fderiv hn).comp continuous_fst).prodMk continuous_snd
  A.comp B

中文:
定理 连续可微.continuous_fderiv_apply
  条件: (h : 连续可微 𝕜 n f) (hn : n != 0)
  证明: have A : Continuous fun q : (E ->L[𝕜] F) × E => q.1 q.2 := isBoundedBilinearMap_apply.continuous
  have B : Continuous fun p : E × E => (fderiv 𝕜 f p.1, p.2) :=
    ((h.continuous_fderiv hn).comp continuous_fst).prodMk continuous_snd
  A.comp B

Depends on / 依赖: A.comp, Continuous, continuous, continuous_fderiv, continuous_fst, continuous_snd, fderiv, h.continuous_fderiv, isBoundedBilinearMap_apply, isBoundedBilinearMap_apply.continuous, prodMk
-/
theorem ContDiff.continuous_fderiv_apply (h : ContDiff 𝕜 n f) (hn : n != 0) :
    Continuous fun p : E × E => (fderiv 𝕜 f p.1 : E -> F) p.2 :=
  have A : Continuous fun q : (E ->L[𝕜] F) × E => q.1 q.2 := isBoundedBilinearMap_apply.continuous
  have B : Continuous fun p : E × E => (fderiv 𝕜 f p.1, p.2) :=
    ((h.continuous_fderiv hn).comp continuous_fst).prodMk continuous_snd
  A.comp B
