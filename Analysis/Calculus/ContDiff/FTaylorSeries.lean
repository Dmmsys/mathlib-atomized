/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Calculus.FormalMultilinearSeries
public import Mathlib.Data.ENat.Lattice

/-!
# Iterated derivatives of a function

In this file, we define iteratively the `n+1`-th derivative of a function as the
derivative of the `n`-th derivative. It is called `iteratedFDeriv 𝕜 n f x` where `𝕜` is the
field, `n` is the number of iterations, `f` is the function and `x` is the point, and it is given
as an `n`-multilinear map. We also define a version `iteratedFDerivWithin` relative to a domain.
Note that, in domains, there may be several choices of possible derivative, so we make some
arbitrary choice in the definition.

We also define a predicate `HasFTaylorSeriesUpTo` (and its localized version
`HasFTaylorSeriesUpToOn`), saying that a sequence of multilinear maps is *a* sequence of
derivatives of `f`. Contrary to `iteratedFDerivWithin`, it accommodates well the
non-uniqueness of derivatives.

## Main definitions and results

Let `f : E → F` be a map between normed vector spaces over a nontrivially normed field `𝕜`.

* `HasFTaylorSeriesUpTo n f p`: expresses that the formal multilinear series `p` is a sequence
  of iterated derivatives of `f`, up to the `n`-th term (where `n` is a natural number or `∞`).
* `HasFTaylorSeriesUpToOn n f p s`: same thing, but inside a set `s`. The notion of derivative
  is now taken inside `s`. In particular, derivatives don't have to be unique.

* `iteratedFDerivWithin 𝕜 n f s x` is an `n`-th derivative of `f` over the field `𝕜` on the
  set `s` at the point `x`. It is a continuous multilinear map from `E^n` to `F`, defined as a
  derivative within `s` of `iteratedFDerivWithin 𝕜 (n-1) f s` if one exists, and `0` otherwise.
* `iteratedFDeriv 𝕜 n f x` is the `n`-th derivative of `f` over the field `𝕜` at the point `x`.
  It is a continuous multilinear map from `E^n` to `F`, defined as a derivative of
  `iteratedFDeriv 𝕜 (n-1) f` if one exists, and `0` otherwise.


### Side of the composition, and universe issues

With a naïve direct definition, the `n`-th derivative of a function belongs to the space
`E →L[𝕜] (E →L[𝕜] (E ... F)...)))` where there are n iterations of `E →L[𝕜]`. This space
may also be seen as the space of continuous multilinear functions on `n` copies of `E` with
values in `F`, by uncurrying. This is the point of view that is usually adopted in textbooks,
and that we also use. This means that the definition and the first proofs are slightly involved,
as one has to keep track of the uncurrying operation. The uncurrying can be done from the
left or from the right, amounting to defining the `n+1`-th derivative either as the derivative of
the `n`-th derivative, or as the `n`-th derivative of the derivative.
For proofs, it would be more convenient to use the latter approach (from the right),
as it means to prove things at the `n+1`-th step we only need to understand well enough the
derivative in `E →L[𝕜] F` (contrary to the approach from the left, where one would need to know
enough on the `n`-th derivative to deduce things on the `n+1`-th derivative).

However, the definition from the right leads to a universe polymorphism problem: if we define
`iteratedFDeriv 𝕜 (n + 1) f x = iteratedFDeriv 𝕜 n (fderiv 𝕜 f) x` by induction, we need to
generalize over all spaces (as `f` and `fderiv 𝕜 f` don't take values in the same space). It is
only possible to generalize over all spaces in some fixed universe in an inductive definition.
For `f : E → F`, then `fderiv 𝕜 f` is a map `E → (E →L[𝕜] F)`. Therefore, the definition will only
work if `F` and `E →L[𝕜] F` are in the same universe.

This issue does not appear with the definition from the left, where one does not need to generalize
over all spaces. Therefore, we use the definition from the left. This means some proofs later on
become a little bit more complicated: to prove that a function is `C^n`, the most efficient approach
is to exhibit a formula for its `n`-th derivative and prove it is continuous (contrary to the
inductive approach where one would prove smoothness statements without giving a formula for the
derivative). In the end, this approach is still satisfactory as it is good to have formulas for the
iterated derivatives in various constructions.

One point where this explicit approach is particularly delicate is in the proof of smoothness of a
composition: there is a formula for the `n`-th derivative of a composition (Faà di Bruno's formula),
but it is very complicated, while the inductive proof is very simple. The inductive proof would
be good enough for `C^n` functions with `n ∈ ℕ ∪ {∞}` (modulo polymorphism issues, i.e., one would
need to first prove inductively the result when all spaces belong to the same universe, and then
prove the general result by lifting all the spaces to a common universe). However, it would not
work for `C^ω` functions. Therefore, we give the proof based on Faà di Bruno's formula, which is
more complicated but more general.

### Variables management

The textbook definitions and proofs use various identifications and abuse of notations, for instance
when saying that the natural space in which the derivative lives, i.e.,
`E →L[𝕜] (E →L[𝕜] ( ... →L[𝕜] F))`, is the same as a space of multilinear maps. When doing things
formally, we need to provide explicit maps for these identifications, and chase some diagrams to see
everything is compatible with the identifications. In particular, one needs to check that taking the
derivative and then doing the identification, or first doing the identification and then taking the
derivative, gives the same result. The key point for this is that taking the derivative commutes
with continuous linear equivalences. Therefore, we need to implement all our identifications with
continuous linear equivs.

## Notation

We use the notation `E [×n]→L[𝕜] F` for the space of continuous multilinear maps on `E^n` with
values in `F`. This is the space in which the `n`-th derivative of a function from `E` to `F` lives.

In this file, we denote `WithTop ℕ∞` with `ℕ∞ω`, `(⊤ : ℕ∞) : ℕ∞ω` with `∞` and `⊤ : ℕ∞ω` with `ω`.
-/

@[expose] public section


noncomputable section

open ENat NNReal Topology Filter Set Fin Filter Function

/-- The type of smoothness exponents, consisting of all natural numbers and two special terms `∞`
and `ω`.
Natural numbers `n` correspond to `n`-fold continuous differentiability, `∞` to smoothness, and `ω`
to analyticity. -/
scoped[ContDiff] notation "Nat∞ω" => WithTop Nat∞
/-- Smoothness exponent for analytic functions. -/
scoped[ContDiff] notation3 "ω" => (⊤ : WithTop Nat∞)
/-- Smoothness exponent for infinitely differentiable functions. -/
scoped[ContDiff] notation3 "∞" => ((⊤ : Nat∞) : WithTop Nat∞)

open scoped ContDiff Pointwise

universe u uE uF

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] {E : Type uE} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {s t u : Set E} {f f₁ : E -> F} {x : E} {m n N : Nat∞ω}
  {p : E -> FormalMultilinearSeries 𝕜 E F}

/-! ### Functions with a Taylor series on a domain -/

/--
Definition of `HasFTaylorSeriesUpToOn` / `HasFTaylorSeriesUpToOn` 的定义

English:
structure HasFTaylorSeriesUpToOn
  axioms and operations (3):
    - zero_eq : forall x in s, (p x 0).curry0 = f x
    - fderivWithin : forall m : Nat, m < n -> forall x in s, HasFDerivWithinAt (p · m) (p x m.succ).curryLeft s x
    - cont : forall m : Nat, m <= n -> ContinuousOn (p · m) s

中文:
结构 HasFTaylorSeriesUpToOn
  公理与运算 (3 个):
    - zero_eq : 对任意 x in s, (p x 0).curry0 = f x
    - fderivWithin : 对任意 m : 自然数, m < n -> 对任意 x in s, HasFDerivWithinAt (p · m) (p x m.succ).curryLeft s x
    - cont : 对任意 m : 自然数, m <= n -> ContinuousOn (p · m) s
-/
structure HasFTaylorSeriesUpToOn
  (n : Nat∞ω) (f : E -> F) (p : E -> FormalMultilinearSeries 𝕜 E F) (s : Set E) : Prop where
  zero_eq : forall x in s, (p x 0).curry0 = f x
  protected fderivWithin : forall m : Nat, m < n -> forall x in s,
    HasFDerivWithinAt (p · m) (p x m.succ).curryLeft s x
  cont : forall m : Nat, m <= n -> ContinuousOn (p · m) s

/--
theorem `HasFTaylorSeriesUpToOn.zero_eq'` / 定理 `HasFTaylorSeriesUpToOn.zero_eq'`

English:
theorem HasFTaylorSeriesUpToOn.zero_eq'
  given: (h : HasFTaylorSeriesUpToOn n f p s) {x : E} (hx : x in s)
  proof: by
  rw [← h.zero_eq x hx]
  exact (p x 0).uncurry0_curry0.symm

中文:
定理 HasFTaylorSeriesUpToOn.zero_eq'
  条件: (h : HasFTaylorSeriesUpToOn n f p s) {x : E} (hx : x in s)
  证明: by
  rw [← h.zero_eq x hx]
  exact (p x 0).uncurry0_curry0.symm

Depends on / 依赖: h.zero_eq, uncurry0_curry0, uncurry0_curry0.symm, zero_eq
-/
theorem HasFTaylorSeriesUpToOn.zero_eq' (h : HasFTaylorSeriesUpToOn n f p s) {x : E} (hx : x in s) :
    p x 0 = (continuousMultilinearCurryFin0 𝕜 E F).symm (f x) := by
  rw [← h.zero_eq x hx]
  exact (p x 0).uncurry0_curry0.symm

/--
theorem `hasFTaylorSeriesUpToOn_empty` / 定理 `hasFTaylorSeriesUpToOn_empty`

English:
theorem hasFTaylorSeriesUpToOn_empty
  statement: HasFTaylorSeriesUpToOn n f p ∅
  proof: by
  constructor <;> simp

中文:
定理 hasFTaylorSeriesUpToOn_empty
  结论: HasFTaylorSeriesUpToOn n f p ∅
  证明: by
  constructor <;> simp
-/
@[simp] theorem hasFTaylorSeriesUpToOn_empty : HasFTaylorSeriesUpToOn n f p ∅ := by
  constructor <;> simp

/--
theorem `HasFTaylorSeriesUpToOn.congr` / 定理 `HasFTaylorSeriesUpToOn.congr`

English:
theorem HasFTaylorSeriesUpToOn.congr
  statement: (h : HasFTaylorSeriesUpToOn n f p s)
  proof: by
  refine ⟨fun x hx => ?_, h.fderivWithin, h.cont⟩
  rw [h₁ x hx]
  exact h.zero_eq x hx

中文:
定理 HasFTaylorSeriesUpToOn.congr
  结论: (h : HasFTaylorSeriesUpToOn n f p s)
  证明: by
  refine ⟨fun x hx => ?_, h.fderivWithin, h.cont⟩
  rw [h₁ x hx]
  exact h.zero_eq x hx

Depends on / 依赖: fderivWithin, h.cont, h.fderivWithin, h.zero_eq, zero_eq
-/
theorem HasFTaylorSeriesUpToOn.congr (h : HasFTaylorSeriesUpToOn n f p s)
    (h₁ : forall x in s, f₁ x = f x) : HasFTaylorSeriesUpToOn n f₁ p s := by
  refine ⟨fun x hx => ?_, h.fderivWithin, h.cont⟩
  rw [h₁ x hx]
  exact h.zero_eq x hx

/--
theorem `HasFTaylorSeriesUpToOn.congr_series` / 定理 `HasFTaylorSeriesUpToOn.congr_series`

English:
theorem HasFTaylorSeriesUpToOn.congr_series
  statement: {q} (hp : HasFTaylorSeriesUpToOn n f p s)
  proof: by simp only [← hpq 0 zero_le hx, hp.zero_eq x hx]
  fderivWithin m hm x hx := by
    refine ((hp.fderivWithin m hm x hx).congr' (hpq m hm.le).symm hx).congr_fderiv ?_
    refine congrArg _ (hpq (m + 1) ?_ hx)
    exact ENat.add_one_natCast_le_withTop_of_lt hm
  cont m hm := (hp.cont m hm).congr (hp

中文:
定理 HasFTaylorSeriesUpToOn.congr_series
  结论: {q} (hp : HasFTaylorSeriesUpToOn n f p s)
  证明: by simp only [← hpq 0 zero_le hx, hp.zero_eq x hx]
  fderivWithin m hm x hx := by
    refine ((hp.fderivWithin m hm x hx).congr' (hpq m hm.le).symm hx).congr_fderiv ?_
    refine congrArg _ (hpq (m + 1) ?_ hx)
    exact ENat.add_one_natCast_le_withTop_of_lt hm
  cont m hm := (hp.cont m hm).congr (hp

Depends on / 依赖: ENat.add_one_natCast_le_withTop_of_lt, add_one_natCast_le_withTop_of_lt, congr_fderiv, fderivWithin, hm.le, hp.cont, hp.fderivWithin, hp.zero_eq, zero_eq, zero_le
-/
theorem HasFTaylorSeriesUpToOn.congr_series {q} (hp : HasFTaylorSeriesUpToOn n f p s)
    (hpq : forall m : Nat, m <= n -> EqOn (p · m) (q · m) s) :
    HasFTaylorSeriesUpToOn n f q s where
  zero_eq x hx := by simp only [← hpq 0 zero_le hx, hp.zero_eq x hx]
  fderivWithin m hm x hx := by
    refine ((hp.fderivWithin m hm x hx).congr' (hpq m hm.le).symm hx).congr_fderiv ?_
    refine congrArg _ (hpq (m + 1) ?_ hx)
    exact ENat.add_one_natCast_le_withTop_of_lt hm
  cont m hm := (hp.cont m hm).congr (hpq m hm).symm

/--
theorem `HasFTaylorSeriesUpToOn.mono` / 定理 `HasFTaylorSeriesUpToOn.mono`

English:
theorem HasFTaylorSeriesUpToOn.mono
  given: (h : HasFTaylorSeriesUpToOn n f p s) {t : Set E} (hst : t subseteq s)
  proof: ⟨fun x hx => h.zero_eq x (hst hx), fun m hm x hx => (h.fderivWithin m hm x (hst hx)).mono hst,
    fun m hm => (h.cont m hm).mono hst⟩

中文:
定理 HasFTaylorSeriesUpToOn.mono
  条件: (h : HasFTaylorSeriesUpToOn n f p s) {t : Set E} (hst : t subseteq s)
  证明: ⟨fun x hx => h.zero_eq x (hst hx), fun m hm x hx => (h.fderivWithin m hm x (hst hx)).mono hst,
    fun m hm => (h.cont m hm).mono hst⟩

Depends on / 依赖: fderivWithin, h.cont, h.fderivWithin, h.zero_eq, zero_eq
-/
theorem HasFTaylorSeriesUpToOn.mono (h : HasFTaylorSeriesUpToOn n f p s) {t : Set E} (hst : t subseteq s) :
    HasFTaylorSeriesUpToOn n f p t :=
  ⟨fun x hx => h.zero_eq x (hst hx), fun m hm x hx => (h.fderivWithin m hm x (hst hx)).mono hst,
    fun m hm => (h.cont m hm).mono hst⟩

/--
theorem `HasFTaylorSeriesUpToOn.of_le` / 定理 `HasFTaylorSeriesUpToOn.of_le`

English:
theorem HasFTaylorSeriesUpToOn.of_le
  given: (h : HasFTaylorSeriesUpToOn n f p s) (hmn : m <= n)
  proof: ⟨h.zero_eq, fun k hk x hx => h.fderivWithin k (lt_of_lt_of_le hk hmn) x hx, fun k hk =>
    h.cont k (le_trans hk hmn)⟩

中文:
定理 HasFTaylorSeriesUpToOn.of_le
  条件: (h : HasFTaylorSeriesUpToOn n f p s) (hmn : m <= n)
  证明: ⟨h.zero_eq, fun k hk x hx => h.fderivWithin k (lt_of_lt_of_le hk hmn) x hx, fun k hk =>
    h.cont k (le_trans hk hmn)⟩

Depends on / 依赖: fderivWithin, h.cont, h.fderivWithin, h.zero_eq, le_trans, lt_of_lt_of_le, zero_eq
-/
theorem HasFTaylorSeriesUpToOn.of_le (h : HasFTaylorSeriesUpToOn n f p s) (hmn : m <= n) :
    HasFTaylorSeriesUpToOn m f p s :=
  ⟨h.zero_eq, fun k hk x hx => h.fderivWithin k (lt_of_lt_of_le hk hmn) x hx, fun k hk =>
    h.cont k (le_trans hk hmn)⟩

/--
theorem `HasFTaylorSeriesUpToOn.continuousOn` / 定理 `HasFTaylorSeriesUpToOn.continuousOn`

English:
theorem HasFTaylorSeriesUpToOn.continuousOn
  given: (h : HasFTaylorSeriesUpToOn n f p s)
  proof: by
  have := (h.cont 0 bot_le).congr fun x hx => (h.zero_eq' hx).symm
  rwa [← (continuousMultilinearCurryFin0 𝕜 E F).symm.comp_continuousOn_iff]

中文:
定理 HasFTaylorSeriesUpToOn.continuousOn
  条件: (h : HasFTaylorSeriesUpToOn n f p s)
  证明: by
  have := (h.cont 0 bot_le).congr fun x hx => (h.zero_eq' hx).symm
  rwa [← (continuousMultilinearCurryFin0 𝕜 E F).symm.comp_continuousOn_iff]

Depends on / 依赖: bot_le, comp_continuousOn_iff, continuousMultilinearCurryFin0, h.cont, h.zero_eq, symm.comp_continuousOn_iff, zero_eq
-/
theorem HasFTaylorSeriesUpToOn.continuousOn (h : HasFTaylorSeriesUpToOn n f p s) :
    ContinuousOn f s := by
  have := (h.cont 0 bot_le).congr fun x hx => (h.zero_eq' hx).symm
  rwa [← (continuousMultilinearCurryFin0 𝕜 E F).symm.comp_continuousOn_iff]

/--
theorem `hasFTaylorSeriesUpToOn_zero_iff` / 定理 `hasFTaylorSeriesUpToOn_zero_iff`

English:
theorem hasFTaylorSeriesUpToOn_zero_iff
  proof: by
  refine ⟨fun H => ⟨H.continuousOn, H.zero_eq⟩, fun H =>
      ⟨H.2, fun m hm => False.elim (not_le.2 hm bot_le), fun m hm => ?_⟩⟩
  obtain rfl : m = 0 := mod_cast hm.antisymm zero_le
  have : EqOn (p · 0) ((continuousMultilinearCurryFin0 𝕜 E F).symm ∘ f) s := fun x hx =>
    (continuousMultiline

中文:
定理 hasFTaylorSeriesUpToOn_zero_iff
  证明: by
  refine ⟨fun H => ⟨H.continuousOn, H.zero_eq⟩, fun H =>
      ⟨H.2, fun m hm => False.elim (not_le.2 hm bot_le), fun m hm => ?_⟩⟩
  obtain rfl : m = 0 := mod_cast hm.antisymm zero_le
  have : EqOn (p · 0) ((continuousMultilinearCurryFin0 𝕜 E F).symm ∘ f) s := fun x hx =>
    (continuousMultiline

Depends on / 依赖: False.elim, H.continuousOn, H.zero_eq, LinearIsometryEquiv, LinearIsometryEquiv.comp_continuousOn_iff, antisymm, bot_le, comp_continuousOn_iff, continuousMultilinearCurryFin0, continuousOn, continuousOn_congr, eq_symm_apply, hm.antisymm, mod_cast, not_le, zero_eq, zero_le
-/
theorem hasFTaylorSeriesUpToOn_zero_iff :
    HasFTaylorSeriesUpToOn 0 f p s ↔ ContinuousOn f s ∧ forall x in s, (p x 0).curry0 = f x := by
  refine ⟨fun H => ⟨H.continuousOn, H.zero_eq⟩, fun H =>
      ⟨H.2, fun m hm => False.elim (not_le.2 hm bot_le), fun m hm => ?_⟩⟩
  obtain rfl : m = 0 := mod_cast hm.antisymm zero_le
  have : EqOn (p · 0) ((continuousMultilinearCurryFin0 𝕜 E F).symm ∘ f) s := fun x hx =>
    (continuousMultilinearCurryFin0 𝕜 E F).eq_symm_apply.2 (H.2 x hx)
  rw [continuousOn_congr this]; rw [LinearIsometryEquiv.comp_continuousOn_iff]
  exact H.1

/--
theorem `hasFTaylorSeriesUpToOn_top_iff_add` / 定理 `hasFTaylorSeriesUpToOn_top_iff_add`

English:
theorem hasFTaylorSeriesUpToOn_top_iff_add
  given: (hN : ∞ <= N) (k : Nat)
  proof: by
  constructor
  · intro H n
    apply H.of_le (natCast_le_of_coe_top_le_withTop hN _)
  · intro H
    constructor
    · exact (H 0).zero_eq
    · intro m _
      apply (H m.succ).fderivWithin m (by norm_cast; lia)
    · intro m _
      apply (H m).cont m (by simp)

中文:
定理 hasFTaylorSeriesUpToOn_top_iff_add
  条件: (hN : ∞ <= N) (k : 自然数)
  证明: by
  constructor
  · intro H n
    apply H.of_le (natCast_le_of_coe_top_le_withTop hN _)
  · intro H
    constructor
    · exact (H 0).zero_eq
    · intro m _
      apply (H m.succ).fderivWithin m (by norm_cast; lia)
    · intro m _
      apply (H m).cont m (by simp)

Depends on / 依赖: H.of_le, fderivWithin, m.succ, natCast_le_of_coe_top_le_withTop, of_le, zero_eq
-/
theorem hasFTaylorSeriesUpToOn_top_iff_add (hN : ∞ <= N) (k : Nat) :
    HasFTaylorSeriesUpToOn N f p s ↔ forall n : Nat, HasFTaylorSeriesUpToOn (n + k : Nat) f p s := by
  constructor
  · intro H n
    apply H.of_le (natCast_le_of_coe_top_le_withTop hN _)
  · intro H
    constructor
    · exact (H 0).zero_eq
    · intro m _
      apply (H m.succ).fderivWithin m (by norm_cast; lia)
    · intro m _
      apply (H m).cont m (by simp)

/--
theorem `hasFTaylorSeriesUpToOn_top_iff` / 定理 `hasFTaylorSeriesUpToOn_top_iff`

English:
theorem hasFTaylorSeriesUpToOn_top_iff
  given: (hN : ∞ <= N)
  proof: by
  simpa using hasFTaylorSeriesUpToOn_top_iff_add hN 0

中文:
定理 hasFTaylorSeriesUpToOn_top_iff
  条件: (hN : ∞ <= N)
  证明: by
  simpa using hasFTaylorSeriesUpToOn_top_iff_add hN 0

Depends on / 依赖: hasFTaylorSeriesUpToOn_top_iff_add
-/
theorem hasFTaylorSeriesUpToOn_top_iff (hN : ∞ <= N) :
    HasFTaylorSeriesUpToOn N f p s ↔ forall n : Nat, HasFTaylorSeriesUpToOn n f p s := by
  simpa using hasFTaylorSeriesUpToOn_top_iff_add hN 0

/--
theorem `hasFTaylorSeriesUpToOn_top_iff'` / 定理 `hasFTaylorSeriesUpToOn_top_iff'`

English:
theorem hasFTaylorSeriesUpToOn_top_iff'
  given: (hN : ∞ <= N)
  proof: by
  -- Everything except for the continuity is trivial:
  refine ⟨fun h => ⟨h.1, fun m => h.2 m (natCast_lt_of_coe_top_le_withTop hN _)⟩, fun h =>
    ⟨h.1, fun m _ => h.2 m, fun m _ x hx =>
      -- The continuity follows from the existence of a derivative:
      (h.2 m x hx).continuousWithinAt⟩⟩

中文:
定理 hasFTaylorSeriesUpToOn_top_iff'
  条件: (hN : ∞ <= N)
  证明: by
  -- Everything except for the continuity is trivial:
  refine ⟨fun h => ⟨h.1, fun m => h.2 m (natCast_lt_of_coe_top_le_withTop hN _)⟩, fun h =>
    ⟨h.1, fun m _ => h.2 m, fun m _ x hx =>
      -- The continuity follows from the existence of a derivative:
      (h.2 m x hx).continuousWithinAt⟩⟩
-/
theorem hasFTaylorSeriesUpToOn_top_iff' (hN : ∞ <= N) :
    HasFTaylorSeriesUpToOn N f p s ↔
      (forall x in s, (p x 0).curry0 = f x) ∧
        forall m : Nat, forall x in s, HasFDerivWithinAt (fun y => p y m) (p x m.succ).curryLeft s x := by
  -- Everything except for the continuity is trivial:
  refine ⟨fun h => ⟨h.1, fun m => h.2 m (natCast_lt_of_coe_top_le_withTop hN _)⟩, fun h =>
    ⟨h.1, fun m _ => h.2 m, fun m _ x hx =>
      -- The continuity follows from the existence of a derivative:
      (h.2 m x hx).continuousWithinAt⟩⟩

/--
theorem `HasFTaylorSeriesUpToOn.hasFDerivWithinAt` / 定理 `HasFTaylorSeriesUpToOn.hasFDerivWithinAt`

English:
theorem HasFTaylorSeriesUpToOn.hasFDerivWithinAt
  statement: (h : HasFTaylorSeriesUpToOn n f p s) (hn : n != 0)
  proof: by
  have A : forall y in s, f y = (continuousMultilinearCurryFin0 𝕜 E F) (p y 0) := fun y hy =>
    (h.zero_eq y hy).symm
  suffices H : HasFDerivWithinAt (continuousMultilinearCurryFin0 𝕜 E F ∘ (p · 0))
    (continuousMultilinearCurryFin1 𝕜 E F (p x 1)) s x from H.congr A (A x hx)
  rw [LinearIsom

中文:
定理 HasFTaylorSeriesUpToOn.hasFDerivWithinAt
  结论: (h : HasFTaylorSeriesUpToOn n f p s) (hn : n != 0)
  证明: by
  have A : forall y in s, f y = (continuousMultilinearCurryFin0 𝕜 E F) (p y 0) := fun y hy =>
    (h.zero_eq y hy).symm
  suffices H : HasFDerivWithinAt (continuousMultilinearCurryFin0 𝕜 E F ∘ (p · 0))
    (continuousMultilinearCurryFin1 𝕜 E F (p x 1)) s x from H.congr A (A x hx)
  rw [LinearIsom

Depends on / 依赖: H.congr, HasFDerivWithinAt, LinearIsometryEquiv, LinearIsometryEquiv.comp_hasFDerivWithinAt_iff, Unique, Unique.eq_d, comp_hasFDerivWithinAt_iff, continuousMultilinearCurryFin0, continuousMultilinearCurryFin1, convert, eq_d, fderivWithin, h.fderivWithin, h.zero_eq, pos_iff_ne_zero, pos_iff_ne_zero.mpr, zero_eq
-/
theorem HasFTaylorSeriesUpToOn.hasFDerivWithinAt (h : HasFTaylorSeriesUpToOn n f p s) (hn : n != 0)
    (hx : x in s) : HasFDerivWithinAt f (continuousMultilinearCurryFin1 𝕜 E F (p x 1)) s x := by
  have A : forall y in s, f y = (continuousMultilinearCurryFin0 𝕜 E F) (p y 0) := fun y hy =>
    (h.zero_eq y hy).symm
  suffices H : HasFDerivWithinAt (continuousMultilinearCurryFin0 𝕜 E F ∘ (p · 0))
    (continuousMultilinearCurryFin1 𝕜 E F (p x 1)) s x from H.congr A (A x hx)
  rw [LinearIsometryEquiv.comp_hasFDerivWithinAt_iff']
  have : ((0 : Nat) : Nat∞) < n := pos_iff_ne_zero.mpr hn
  convert! h.fderivWithin _ this x hx
  ext y v
  change (p x 1) (snoc 0 y) = (p x 1) (cons y v)
  congr with i
  rw [Unique.eq_default (α := Fin 1) i]
  rfl

/--
theorem `HasFTaylorSeriesUpToOn.differentiableOn` / 定理 `HasFTaylorSeriesUpToOn.differentiableOn`

English:
theorem HasFTaylorSeriesUpToOn.differentiableOn
  given: (h : HasFTaylorSeriesUpToOn n f p s) (hn : n != 0)
  proof: fun _x hx => (h.hasFDerivWithinAt hn hx).differentiableWithinAt

中文:
定理 HasFTaylorSeriesUpToOn.differentiableOn
  条件: (h : HasFTaylorSeriesUpToOn n f p s) (hn : n != 0)
  证明: fun _x hx => (h.hasFDerivWithinAt hn hx).differentiableWithinAt

Depends on / 依赖: differentiableWithinAt, h.hasFDerivWithinAt, hasFDerivWithinAt
-/
theorem HasFTaylorSeriesUpToOn.differentiableOn (h : HasFTaylorSeriesUpToOn n f p s) (hn : n != 0) :
    DifferentiableOn 𝕜 f s := fun _x hx => (h.hasFDerivWithinAt hn hx).differentiableWithinAt

/--
theorem `HasFTaylorSeriesUpToOn.hasFDerivAt` / 定理 `HasFTaylorSeriesUpToOn.hasFDerivAt`

English:
theorem HasFTaylorSeriesUpToOn.hasFDerivAt
  statement: (h : HasFTaylorSeriesUpToOn n f p s) (hn : n != 0)
  proof: (h.hasFDerivWithinAt hn (mem_of_mem_nhds hx)).hasFDerivAt hx

中文:
定理 HasFTaylorSeriesUpToOn.hasFDerivAt
  结论: (h : HasFTaylorSeriesUpToOn n f p s) (hn : n != 0)
  证明: (h.hasFDerivWithinAt hn (mem_of_mem_nhds hx)).hasFDerivAt hx

Depends on / 依赖: h.hasFDerivWithinAt, hasFDerivAt, hasFDerivWithinAt, mem_of_mem_nhds
-/
theorem HasFTaylorSeriesUpToOn.hasFDerivAt (h : HasFTaylorSeriesUpToOn n f p s) (hn : n != 0)
    (hx : s in 𝓝 x) : HasFDerivAt f (continuousMultilinearCurryFin1 𝕜 E F (p x 1)) x :=
  (h.hasFDerivWithinAt hn (mem_of_mem_nhds hx)).hasFDerivAt hx

/--
theorem `HasFTaylorSeriesUpToOn.eventually_hasFDerivAt` / 定理 `HasFTaylorSeriesUpToOn.eventually_hasFDerivAt`

English:
theorem HasFTaylorSeriesUpToOn.eventually_hasFDerivAt
  statement: (h : HasFTaylorSeriesUpToOn n f p s)
  proof: (eventually_eventually_nhds.2 hx).mono fun _y hy => h.hasFDerivAt hn hy

中文:
定理 HasFTaylorSeriesUpToOn.eventually_hasFDerivAt
  结论: (h : HasFTaylorSeriesUpToOn n f p s)
  证明: (eventually_eventually_nhds.2 hx).mono fun _y hy => h.hasFDerivAt hn hy

Depends on / 依赖: eventually_eventually_nhds, h.hasFDerivAt, hasFDerivAt
-/
theorem HasFTaylorSeriesUpToOn.eventually_hasFDerivAt (h : HasFTaylorSeriesUpToOn n f p s)
    (hn : n != 0) (hx : s in 𝓝 x) :
    forallᶠ y in 𝓝 x, HasFDerivAt f (continuousMultilinearCurryFin1 𝕜 E F (p y 1)) y :=
  (eventually_eventually_nhds.2 hx).mono fun _y hy => h.hasFDerivAt hn hy

/--
theorem `HasFTaylorSeriesUpToOn.differentiableAt` / 定理 `HasFTaylorSeriesUpToOn.differentiableAt`

English:
theorem HasFTaylorSeriesUpToOn.differentiableAt
  statement: (h : HasFTaylorSeriesUpToOn n f p s) (hn : n != 0)
  proof: (h.hasFDerivAt hn hx).differentiableAt

中文:
定理 HasFTaylorSeriesUpToOn.differentiableAt
  结论: (h : HasFTaylorSeriesUpToOn n f p s) (hn : n != 0)
  证明: (h.hasFDerivAt hn hx).differentiableAt

Depends on / 依赖: differentiableAt, h.hasFDerivAt, hasFDerivAt
-/
theorem HasFTaylorSeriesUpToOn.differentiableAt (h : HasFTaylorSeriesUpToOn n f p s) (hn : n != 0)
    (hx : s in 𝓝 x) : DifferentiableAt 𝕜 f x :=
  (h.hasFDerivAt hn hx).differentiableAt

/--
theorem `hasFTaylorSeriesUpToOn_succ_iff_left` / 定理 `hasFTaylorSeriesUpToOn_succ_iff_left`

English:
theorem hasFTaylorSeriesUpToOn_succ_iff_left
  given: {n : Nat}
  proof: by
  constructor
  · exact fun h => ⟨h.of_le (mod_cast Nat.le_succ n),
      h.fderivWithin _ (mod_cast lt_add_one n), h.cont (n + 1) le_rfl⟩
  · intro h
    constructor
    · exact h.1.zero_eq
    · intro m hm
      by_cases h' : m < n
      · exact h.1.fderivWithin m (mod_cast h')
      · have : m

中文:
定理 hasFTaylorSeriesUpToOn_succ_iff_left
  条件: {n : 自然数}
  证明: by
  constructor
  · exact fun h => ⟨h.of_le (mod_cast Nat.le_succ n),
      h.fderivWithin _ (mod_cast lt_add_one n), h.cont (n + 1) le_rfl⟩
  · intro h
    constructor
    · exact h.1.zero_eq
    · intro m hm
      by_cases h' : m < n
      · exact h.1.fderivWithin m (mod_cast h')
      · have : m

Depends on / 依赖: Nat.eq_of_lt_succ_of_not_lt, Nat.le_succ, eq_of_lt_succ_of_not_lt, fderivWithin, h.cont, h.fderivWithin, h.of_le, le_antisymm, le_rfl, le_succ, lt_add_one, mod_cast, not_le, of_le, zero_eq
-/
theorem hasFTaylorSeriesUpToOn_succ_iff_left {n : Nat} :
    HasFTaylorSeriesUpToOn (n + 1) f p s ↔
      HasFTaylorSeriesUpToOn n f p s ∧
        (forall x in s, HasFDerivWithinAt (fun y => p y n) (p x n.succ).curryLeft s x) ∧
          ContinuousOn (fun x => p x (n + 1)) s := by
  constructor
  · exact fun h => ⟨h.of_le (mod_cast Nat.le_succ n),
      h.fderivWithin _ (mod_cast lt_add_one n), h.cont (n + 1) le_rfl⟩
  · intro h
    constructor
    · exact h.1.zero_eq
    · intro m hm
      by_cases h' : m < n
      · exact h.1.fderivWithin m (mod_cast h')
      · have : m = n := Nat.eq_of_lt_succ_of_not_lt (mod_cast hm) h'
        rw [this]
        exact h.2.1
    · intro m hm
      by_cases h' : m <= n
      · apply h.1.cont m (mod_cast h')
      · have : m = n + 1 := le_antisymm (mod_cast hm) (not_le.1 h')
        rw [this]
        exact h.2.2

/--
theorem `HasFTaylorSeriesUpToOn.shift_of_succ` / 定理 `HasFTaylorSeriesUpToOn.shift_of_succ`

English:
theorem HasFTaylorSeriesUpToOn.shift_of_succ
  proof: by
  constructor
  · intro x _
    rfl
  · intro m (hm : (m : Nat∞ω) < n) x (hx : x in s)
    have A : (m.succ : Nat∞ω) < n.succ := by
      rw [Nat.cast_lt] at hm ⊢
      exact Nat.succ_lt_succ hm
    change HasFDerivWithinAt (continuousMultilinearCurryRightEquiv' 𝕜 m E F ∘ (p · m.succ))
      (p x

中文:
定理 HasFTaylorSeriesUpToOn.shift_of_succ
  证明: by
  constructor
  · intro x _
    rfl
  · intro m (hm : (m : Nat∞ω) < n) x (hx : x in s)
    have A : (m.succ : Nat∞ω) < n.succ := by
      rw [Nat.cast_lt] at hm ⊢
      exact Nat.succ_lt_succ hm
    change HasFDerivWithinAt (continuousMultilinearCurryRightEquiv' 𝕜 m E F ∘ (p · m.succ))
      (p x

Depends on / 依赖: H.fderivWithin, HasFDerivWithinAt, Nat.cast_lt, Nat.succ_lt_succ, cast_lt, comp_hasFDerivWithinAt_iff, continuousMultilinearCurryRightEquiv, convert, curryLeft, curryRight, curryRight.curryLeft, fderivWithin, m.succ, m.succ.succ, n.succ, succ_lt_succ
-/
theorem HasFTaylorSeriesUpToOn.shift_of_succ
    {n : Nat} (H : HasFTaylorSeriesUpToOn (n + 1 : Nat) f p s) :
    (HasFTaylorSeriesUpToOn n (fun x => continuousMultilinearCurryFin1 𝕜 E F (p x 1))
      (fun x => (p x).shift)) s := by
  constructor
  · intro x _
    rfl
  · intro m (hm : (m : Nat∞ω) < n) x (hx : x in s)
    have A : (m.succ : Nat∞ω) < n.succ := by
      rw [Nat.cast_lt] at hm ⊢
      exact Nat.succ_lt_succ hm
    change HasFDerivWithinAt (continuousMultilinearCurryRightEquiv' 𝕜 m E F ∘ (p · m.succ))
      (p x m.succ.succ).curryRight.curryLeft s x
    rw [(continuousMultilinearCurryRightEquiv' 𝕜 m E F).comp_hasFDerivWithinAt_iff']
    convert! H.fderivWithin _ A x hx
    ext y v
    change p x (m + 2) (snoc (cons y (init v)) (v (last _))) = p x (m + 2) (cons y v)
    rw [← cons_snoc_eq_snoc_cons]; rw [snoc_init_self]
  · intro m (hm : (m : Nat∞ω) <= n)
    suffices A : ContinuousOn (p · (m + 1)) s from
      (continuousMultilinearCurryRightEquiv' 𝕜 m E F).continuous.comp_continuousOn A
    refine H.cont _ ?_
    rw [Nat.cast_le] at hm ⊢
    exact Nat.succ_le_succ hm

/--
theorem `hasFTaylorSeriesUpToOn_succ_nat_iff_right` / 定理 `hasFTaylorSeriesUpToOn_succ_nat_iff_right`

English:
theorem hasFTaylorSeriesUpToOn_succ_nat_iff_right
  given: {n : Nat}
  proof: by
  constructor
  · intro H
    refine ⟨H.zero_eq, H.fderivWithin 0 (Nat.cast_lt.2 (Nat.succ_pos n)), ?_⟩
    exact H.shift_of_succ
  · rintro ⟨Hzero_eq, Hfderiv_zero, Htaylor⟩
    constructor
    · exact Hzero_eq
    · intro m (hm : (m : Nat∞ω) < n.succ) x (hx : x in s)
      rcases m with - | m
 

中文:
定理 hasFTaylorSeriesUpToOn_succ_nat_iff_right
  条件: {n : 自然数}
  证明: by
  constructor
  · intro H
    refine ⟨H.zero_eq, H.fderivWithin 0 (Nat.cast_lt.2 (Nat.succ_pos n)), ?_⟩
    exact H.shift_of_succ
  · rintro ⟨Hzero_eq, Hfderiv_zero, Htaylor⟩
    constructor
    · exact Hzero_eq
    · intro m (hm : (m : Nat∞ω) < n.succ) x (hx : x in s)
      rcases m with - | m
 

Depends on / 依赖: H.fderivWithin, H.shift_of_succ, H.zero_eq, HasFDerivWithinAt, Hfderiv_zero, Htaylor, Hzero_eq, Nat.cast_lt, Nat.lt_of_succ_lt_succ, Nat.succ_pos, cast_lt, continuousMultilinearCurryRightEquiv, fderivWithin, lt_of_succ_lt_succ, m.succ, n.succ, shift_of_succ, succ_pos, zero_eq
-/
theorem hasFTaylorSeriesUpToOn_succ_nat_iff_right {n : Nat} :
    HasFTaylorSeriesUpToOn (n + 1 : Nat) f p s ↔
      (forall x in s, (p x 0).curry0 = f x) ∧
        (forall x in s, HasFDerivWithinAt (fun y => p y 0) (p x 1).curryLeft s x) ∧
          HasFTaylorSeriesUpToOn n (fun x => continuousMultilinearCurryFin1 𝕜 E F (p x 1))
            (fun x => (p x).shift) s := by
  constructor
  · intro H
    refine ⟨H.zero_eq, H.fderivWithin 0 (Nat.cast_lt.2 (Nat.succ_pos n)), ?_⟩
    exact H.shift_of_succ
  · rintro ⟨Hzero_eq, Hfderiv_zero, Htaylor⟩
    constructor
    · exact Hzero_eq
    · intro m (hm : (m : Nat∞ω) < n.succ) x (hx : x in s)
      rcases m with - | m
      · exact Hfderiv_zero x hx
      · have A : (m : Nat∞ω) < n := by
          rw [Nat.cast_lt] at hm ⊢
          exact Nat.lt_of_succ_lt_succ hm
        have :
          HasFDerivWithinAt (𝕜 := 𝕜) (continuousMultilinearCurryRightEquiv' 𝕜 m E F ∘ (p · m.succ))
            ((p x).shift m.succ).curryLeft s x := Htaylor.fderivWithin _ A x hx
        rw [LinearIsometryEquiv.comp_hasFDerivWithinAt_iff'
            (f' := ((p x).shift m.succ).curryLeft)] at this
        convert! this
        ext y v
        change
          (p x (Nat.succ (Nat.succ m))) (cons y v) =
            (p x m.succ.succ) (snoc (cons y (init v)) (v (last _)))
        rw [← cons_snoc_eq_snoc_cons]; rw [snoc_init_self]
    · intro m (hm : (m : Nat∞ω) <= n.succ)
      rcases m with - | m
      · have : DifferentiableOn 𝕜 (fun x => p x 0) s := fun x hx =>
          (Hfderiv_zero x hx).differentiableWithinAt
        exact this.continuousOn
      · refine (continuousMultilinearCurryRightEquiv' 𝕜 m E F).comp_continuousOn_iff.mp ?_
        refine Htaylor.cont _ ?_
        rw [Nat.cast_le] at hm ⊢
        exact Nat.lt_succ_iff.mp hm

/--
theorem `hasFTaylorSeriesUpToOn_top_iff_right` / 定理 `hasFTaylorSeriesUpToOn_top_iff_right`

English:
theorem hasFTaylorSeriesUpToOn_top_iff_right
  given: (hN : ∞ <= N)
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [hasFTaylorSeriesUpToOn_top_iff_add hN 1] at h
    rw [hasFTaylorSeriesUpToOn_top_iff hN]
    exact ⟨(hasFTaylorSeriesUpToOn_succ_nat_iff_right.1 (h 1)).1,
      (hasFTaylorSeriesUpToOn_succ_nat_iff_right.1 (h 1)).2.1,
      fun n => (hasFTaylorSeriesUpT

中文:
定理 hasFTaylorSeriesUpToOn_top_iff_right
  条件: (hN : ∞ <= N)
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [hasFTaylorSeriesUpToOn_top_iff_add hN 1] at h
    rw [hasFTaylorSeriesUpToOn_top_iff hN]
    exact ⟨(hasFTaylorSeriesUpToOn_succ_nat_iff_right.1 (h 1)).1,
      (hasFTaylorSeriesUpToOn_succ_nat_iff_right.1 (h 1)).2.1,
      fun n => (hasFTaylorSeriesUpT

Depends on / 依赖: hasFTaylorSeriesUpToOn_succ_nat_iff_right, hasFTaylorSeriesUpToOn_top_iff, hasFTaylorSeriesUpToOn_top_iff_add, natCast_le_of_coe_top_le_withTo, of_le
-/
theorem hasFTaylorSeriesUpToOn_top_iff_right (hN : ∞ <= N) :
    HasFTaylorSeriesUpToOn N f p s ↔
      (forall x in s, (p x 0).curry0 = f x) ∧
        (forall x in s, HasFDerivWithinAt (fun y => p y 0) (p x 1).curryLeft s x) ∧
          HasFTaylorSeriesUpToOn N (fun x => continuousMultilinearCurryFin1 𝕜 E F (p x 1))
            (fun x => (p x).shift) s := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [hasFTaylorSeriesUpToOn_top_iff_add hN 1] at h
    rw [hasFTaylorSeriesUpToOn_top_iff hN]
    exact ⟨(hasFTaylorSeriesUpToOn_succ_nat_iff_right.1 (h 1)).1,
      (hasFTaylorSeriesUpToOn_succ_nat_iff_right.1 (h 1)).2.1,
      fun n => (hasFTaylorSeriesUpToOn_succ_nat_iff_right.1 (h n)).2.2⟩
  · apply (hasFTaylorSeriesUpToOn_top_iff_add hN 1).2 (fun n => ?_)
    rw [hasFTaylorSeriesUpToOn_succ_nat_iff_right]
    exact ⟨h.1, h.2.1, (h.2.2).of_le (m := n) (natCast_le_of_coe_top_le_withTop hN n)⟩

/--
theorem `hasFTaylorSeriesUpToOn_succ_iff_right` / 定理 `hasFTaylorSeriesUpToOn_succ_iff_right`

English:
theorem hasFTaylorSeriesUpToOn_succ_iff_right
  proof: by
  match n with
  | ⊤ => exact hasFTaylorSeriesUpToOn_top_iff_right (by simp)
  | (⊤ : Nat∞) => exact hasFTaylorSeriesUpToOn_top_iff_right (by simp)
  | (n : Nat) => exact hasFTaylorSeriesUpToOn_succ_nat_iff_right

中文:
定理 hasFTaylorSeriesUpToOn_succ_iff_right
  证明: by
  match n with
  | ⊤ => exact hasFTaylorSeriesUpToOn_top_iff_right (by simp)
  | (⊤ : Nat∞) => exact hasFTaylorSeriesUpToOn_top_iff_right (by simp)
  | (n : Nat) => exact hasFTaylorSeriesUpToOn_succ_nat_iff_right

Depends on / 依赖: hasFTaylorSeriesUpToOn_succ_nat_iff_right, hasFTaylorSeriesUpToOn_top_iff_right
-/
theorem hasFTaylorSeriesUpToOn_succ_iff_right :
    HasFTaylorSeriesUpToOn (n + 1) f p s ↔
      (forall x in s, (p x 0).curry0 = f x) ∧
        (forall x in s, HasFDerivWithinAt (fun y => p y 0) (p x 1).curryLeft s x) ∧
          HasFTaylorSeriesUpToOn n (fun x => continuousMultilinearCurryFin1 𝕜 E F (p x 1))
            (fun x => (p x).shift) s := by
  match n with
  | ⊤ => exact hasFTaylorSeriesUpToOn_top_iff_right (by simp)
  | (⊤ : Nat∞) => exact hasFTaylorSeriesUpToOn_top_iff_right (by simp)
  | (n : Nat) => exact hasFTaylorSeriesUpToOn_succ_nat_iff_right

/-! ### Iterated derivative within a set -/


variable (𝕜)

/--
Definition of `iteratedFDerivWithin` / `iteratedFDerivWithin` 的定义

English:
definition iteratedFDerivWithin
  signature: (n : Nat) (f : E -> F) (s : Set E)
  body: Nat.recOn n (fun x => ContinuousMultilinearMap.uncurry0 𝕜 E (f x)) fun _ rec x =>
    ContinuousLinearMap.uncurryLeft (fderivWithin 𝕜 rec s x)

中文:
定义 iteratedFDerivWithin
  签名: (n : 自然数) (f : E -> F) (s : Set E)
  定义体: Nat.recOn n (fun x => ContinuousMultilinearMap.uncurry0 𝕜 E (f x)) fun _ rec x =>
    ContinuousLinearMap.uncurryLeft (fderivWithin 𝕜 rec s x)

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.uncurryLeft, ContinuousMultilinearMap, ContinuousMultilinearMap.uncurry0, Nat.recOn, fderivWithin, uncurry0, uncurryLeft
-/
noncomputable def iteratedFDerivWithin (n : Nat) (f : E -> F) (s : Set E) : E -> E [×n]->L[𝕜] F :=
  Nat.recOn n (fun x => ContinuousMultilinearMap.uncurry0 𝕜 E (f x)) fun _ rec x =>
    ContinuousLinearMap.uncurryLeft (fderivWithin 𝕜 rec s x)

/--
Definition of `ftaylorSeriesWithin` / `ftaylorSeriesWithin` 的定义

English:
definition ftaylorSeriesWithin
  signature: (f : E -> F) (s : Set E) (x : E)
  body: fun n =>
  iteratedFDerivWithin 𝕜 n f s x

中文:
定义 ftaylorSeriesWithin
  签名: (f : E -> F) (s : Set E) (x : E)
  定义体: fun n =>
  iteratedFDerivWithin 𝕜 n f s x
-/
def ftaylorSeriesWithin (f : E -> F) (s : Set E) (x : E) : FormalMultilinearSeries 𝕜 E F := fun n =>
  iteratedFDerivWithin 𝕜 n f s x

variable {𝕜}

@[simp]
/--
theorem `iteratedFDerivWithin_zero_apply` / 定理 `iteratedFDerivWithin_zero_apply`

English:
theorem iteratedFDerivWithin_zero_apply
  given: (m : Fin 0 -> E)
  proof: rfl

中文:
定理 iteratedFDerivWithin_zero_apply
  条件: (m : Fin 0 -> E)
  证明: rfl
-/
theorem iteratedFDerivWithin_zero_apply (m : Fin 0 -> E) :
    (iteratedFDerivWithin 𝕜 0 f s x : (Fin 0 -> E) -> F) m = f x :=
  rfl

/--
theorem `iteratedFDerivWithin_zero_eq_comp` / 定理 `iteratedFDerivWithin_zero_eq_comp`

English:
theorem iteratedFDerivWithin_zero_eq_comp
  proof: rfl

@[simp]

中文:
定理 iteratedFDerivWithin_zero_eq_comp
  证明: rfl

@[simp]
-/
theorem iteratedFDerivWithin_zero_eq_comp :
    iteratedFDerivWithin 𝕜 0 f s = (continuousMultilinearCurryFin0 𝕜 E F).symm ∘ f :=
  rfl

@[simp]
/--
theorem `dist_iteratedFDerivWithin_zero` / 定理 `dist_iteratedFDerivWithin_zero`

English:
theorem dist_iteratedFDerivWithin_zero
  statement: (f : E -> F) (s : Set E) (x : E)
  proof: by
  simp only [iteratedFDerivWithin_zero_eq_comp, comp_apply, LinearIsometryEquiv.dist_map]

@[simp]

中文:
定理 dist_iteratedFDerivWithin_zero
  结论: (f : E -> F) (s : Set E) (x : E)
  证明: by
  simp only [iteratedFDerivWithin_zero_eq_comp, comp_apply, LinearIsometryEquiv.dist_map]

@[simp]

Depends on / 依赖: LinearIsometryEquiv, LinearIsometryEquiv.dist_map, comp_apply, dist_map, iteratedFDerivWithin_zero_eq_comp
-/
theorem dist_iteratedFDerivWithin_zero (f : E -> F) (s : Set E) (x : E)
    (g : E -> F) (t : Set E) (y : E) :
    dist (iteratedFDerivWithin 𝕜 0 f s x) (iteratedFDerivWithin 𝕜 0 g t y) = dist (f x) (g y) := by
  simp only [iteratedFDerivWithin_zero_eq_comp, comp_apply, LinearIsometryEquiv.dist_map]

@[simp]
/--
theorem `norm_iteratedFDerivWithin_zero` / 定理 `norm_iteratedFDerivWithin_zero`

English:
theorem norm_iteratedFDerivWithin_zero
  statement: ‖iteratedFDerivWithin 𝕜 0 f s x‖ = ‖f x‖
  proof: by
  rw [iteratedFDerivWithin_zero_eq_comp]; rw [comp_apply]; rw [LinearIsometryEquiv.norm_map]

中文:
定理 norm_iteratedFDerivWithin_zero
  结论: ‖iteratedFDerivWithin 𝕜 0 f s x‖ = ‖f x‖
  证明: by
  rw [iteratedFDerivWithin_zero_eq_comp]; rw [comp_apply]; rw [LinearIsometryEquiv.norm_map]

Depends on / 依赖: LinearIsometryEquiv, LinearIsometryEquiv.norm_map, comp_apply, iteratedFDerivWithin_zero_eq_comp, norm_map
-/
theorem norm_iteratedFDerivWithin_zero : ‖iteratedFDerivWithin 𝕜 0 f s x‖ = ‖f x‖ := by
  rw [iteratedFDerivWithin_zero_eq_comp]; rw [comp_apply]; rw [LinearIsometryEquiv.norm_map]

/--
theorem `iteratedFDerivWithin_succ_apply_left` / 定理 `iteratedFDerivWithin_succ_apply_left`

English:
theorem iteratedFDerivWithin_succ_apply_left
  given: {n : Nat} (m : Fin (n + 1) -> E)
  proof: rfl

中文:
定理 iteratedFDerivWithin_succ_apply_left
  条件: {n : 自然数} (m : Fin (n + 1) -> E)
  证明: rfl
-/
theorem iteratedFDerivWithin_succ_apply_left {n : Nat} (m : Fin (n + 1) -> E) :
    (iteratedFDerivWithin 𝕜 (n + 1) f s x : (Fin (n + 1) -> E) -> F) m =
      (fderivWithin 𝕜 (iteratedFDerivWithin 𝕜 n f s) s x : E -> E [×n]->L[𝕜] F) (m 0) (tail m) :=
  rfl

/--
theorem `iteratedFDerivWithin_succ_eq_comp_left` / 定理 `iteratedFDerivWithin_succ_eq_comp_left`

English:
theorem iteratedFDerivWithin_succ_eq_comp_left
  given: {n : Nat}
  proof: rfl

中文:
定理 iteratedFDerivWithin_succ_eq_comp_left
  条件: {n : 自然数}
  证明: rfl
-/
theorem iteratedFDerivWithin_succ_eq_comp_left {n : Nat} :
    iteratedFDerivWithin 𝕜 (n + 1) f s =
      (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) => E) F).symm ∘
        fderivWithin 𝕜 (iteratedFDerivWithin 𝕜 n f s) s :=
  rfl

/--
theorem `fderivWithin_iteratedFDerivWithin` / 定理 `fderivWithin_iteratedFDerivWithin`

English:
theorem fderivWithin_iteratedFDerivWithin
  given: {s : Set E} {n : Nat}
  proof: rfl

中文:
定理 fderivWithin_iteratedFDerivWithin
  条件: {s : Set E} {n : 自然数}
  证明: rfl
-/
theorem fderivWithin_iteratedFDerivWithin {s : Set E} {n : Nat} :
    fderivWithin 𝕜 (iteratedFDerivWithin 𝕜 n f s) s =
      (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) => E) F) ∘
        iteratedFDerivWithin 𝕜 (n + 1) f s :=
  rfl

/--
theorem `norm_fderivWithin_iteratedFDerivWithin` / 定理 `norm_fderivWithin_iteratedFDerivWithin`

English:
theorem norm_fderivWithin_iteratedFDerivWithin
  given: {n : Nat}
  proof: by
  rw [iteratedFDerivWithin_succ_eq_comp_left]; rw [comp_apply]; rw [LinearIsometryEquiv.norm_map]

@[simp]

中文:
定理 norm_fderivWithin_iteratedFDerivWithin
  条件: {n : 自然数}
  证明: by
  rw [iteratedFDerivWithin_succ_eq_comp_left]; rw [comp_apply]; rw [LinearIsometryEquiv.norm_map]

@[simp]

Depends on / 依赖: LinearIsometryEquiv, LinearIsometryEquiv.norm_map, comp_apply, iteratedFDerivWithin_succ_eq_comp_left, norm_map
-/
theorem norm_fderivWithin_iteratedFDerivWithin {n : Nat} :
    ‖fderivWithin 𝕜 (iteratedFDerivWithin 𝕜 n f s) s x‖ =
      ‖iteratedFDerivWithin 𝕜 (n + 1) f s x‖ := by
  rw [iteratedFDerivWithin_succ_eq_comp_left]; rw [comp_apply]; rw [LinearIsometryEquiv.norm_map]

@[simp]
/--
theorem `dist_iteratedFDerivWithin_one` / 定理 `dist_iteratedFDerivWithin_one`

English:
theorem dist_iteratedFDerivWithin_one
  statement: (f g : E -> F) {y}
  proof: by
  simp only [iteratedFDerivWithin_succ_eq_comp_left, comp_apply,
    LinearIsometryEquiv.dist_map, iteratedFDerivWithin_zero_eq_comp,
    LinearIsometryEquiv.comp_fderivWithin, hsx, hyt]
  apply (continuousMultilinearCurryFin0 𝕜 E F).symm.toLinearIsometry.postcomp.dist_map

@[simp]

中文:
定理 dist_iteratedFDerivWithin_one
  结论: (f g : E -> F) {y}
  证明: by
  simp only [iteratedFDerivWithin_succ_eq_comp_left, comp_apply,
    LinearIsometryEquiv.dist_map, iteratedFDerivWithin_zero_eq_comp,
    LinearIsometryEquiv.comp_fderivWithin, hsx, hyt]
  apply (continuousMultilinearCurryFin0 𝕜 E F).symm.toLinearIsometry.postcomp.dist_map

@[simp]

Depends on / 依赖: LinearIsometryEquiv, LinearIsometryEquiv.comp_fderivWithin, LinearIsometryEquiv.dist_map, comp_apply, comp_fderivWithin, continuousMultilinearCurryFin0, dist_map, iteratedFDerivWithin_succ_eq_comp_left, iteratedFDerivWithin_zero_eq_comp, postcomp, symm.toLinearIsometry.postcomp.dist_map, toLinearIsometry
-/
theorem dist_iteratedFDerivWithin_one (f g : E -> F) {y}
    (hsx : UniqueDiffWithinAt 𝕜 s x) (hyt : UniqueDiffWithinAt 𝕜 t y) :
    dist (iteratedFDerivWithin 𝕜 1 f s x) (iteratedFDerivWithin 𝕜 1 g t y)
      = dist (fderivWithin 𝕜 f s x) (fderivWithin 𝕜 g t y) := by
  simp only [iteratedFDerivWithin_succ_eq_comp_left, comp_apply,
    LinearIsometryEquiv.dist_map, iteratedFDerivWithin_zero_eq_comp,
    LinearIsometryEquiv.comp_fderivWithin, hsx, hyt]
  apply (continuousMultilinearCurryFin0 𝕜 E F).symm.toLinearIsometry.postcomp.dist_map

@[simp]
/--
theorem `norm_iteratedFDerivWithin_one` / 定理 `norm_iteratedFDerivWithin_one`

English:
theorem norm_iteratedFDerivWithin_one
  given: (f : E -> F) (h : UniqueDiffWithinAt 𝕜 s x)
  proof: by
  simp only [← norm_fderivWithin_iteratedFDerivWithin,
    iteratedFDerivWithin_zero_eq_comp, LinearIsometryEquiv.comp_fderivWithin _ h]
  apply (continuousMultilinearCurryFin0 𝕜 E F).symm.toLinearIsometry.norm_toContinuousLinearMap_comp

中文:
定理 norm_iteratedFDerivWithin_one
  条件: (f : E -> F) (h : UniqueDiffWithinAt 𝕜 s x)
  证明: by
  simp only [← norm_fderivWithin_iteratedFDerivWithin,
    iteratedFDerivWithin_zero_eq_comp, LinearIsometryEquiv.comp_fderivWithin _ h]
  apply (continuousMultilinearCurryFin0 𝕜 E F).symm.toLinearIsometry.norm_toContinuousLinearMap_comp

Depends on / 依赖: LinearIsometryEquiv, LinearIsometryEquiv.comp_fderivWithin, comp_fderivWithin, continuousMultilinearCurryFin0, iteratedFDerivWithin_zero_eq_comp, norm_fderivWithin_iteratedFDerivWithin, norm_toContinuousLinearMap_comp, symm.toLinearIsometry.norm_toContinuousLinearMap_comp, toLinearIsometry
-/
theorem norm_iteratedFDerivWithin_one (f : E -> F) (h : UniqueDiffWithinAt 𝕜 s x) :
    ‖iteratedFDerivWithin 𝕜 1 f s x‖ = ‖fderivWithin 𝕜 f s x‖ := by
  simp only [← norm_fderivWithin_iteratedFDerivWithin,
    iteratedFDerivWithin_zero_eq_comp, LinearIsometryEquiv.comp_fderivWithin _ h]
  apply (continuousMultilinearCurryFin0 𝕜 E F).symm.toLinearIsometry.norm_toContinuousLinearMap_comp

/--
theorem `iteratedFDerivWithin_succ_apply_right` / 定理 `iteratedFDerivWithin_succ_apply_right`

English:
theorem iteratedFDerivWithin_succ_apply_right
  statement: {n : Nat} (hs : UniqueDiffOn 𝕜 s) (hx : x in s)
  proof: by
  induction n generalizing x with
  | zero =>
    rw [iteratedFDerivWithin_succ_eq_comp_left]; rw [iteratedFDerivWithin_zero_eq_comp]; rw [iteratedFDerivWithin_zero_apply]; rw [Function.comp_apply]; rw [LinearIsometryEquiv.comp_fderivWithin _ (hs x hx)]
    simp
  | succ n IH =>
    let I := (con

中文:
定理 iteratedFDerivWithin_succ_apply_right
  结论: {n : 自然数} (hs : UniqueDiffOn 𝕜 s) (hx : x in s)
  证明: by
  induction n generalizing x with
  | zero =>
    rw [iteratedFDerivWithin_succ_eq_comp_left]; rw [iteratedFDerivWithin_zero_eq_comp]; rw [iteratedFDerivWithin_zero_apply]; rw [Function.comp_apply]; rw [LinearIsometryEquiv.comp_fderivWithin _ (hs x hx)]
    simp
  | succ n IH =>
    let I := (con

Depends on / 依赖: Function, Function.comp_apply, LinearIsometryEquiv, LinearIsometryEquiv.comp_fderivWithin, comp_apply, comp_fderivWithin, continuousMultilinearCurryRightEquiv, fderivWithin, generalizing, iteratedFDerivWithin, iteratedFDerivWithin_succ_eq_comp_left, iteratedFDerivWithin_zero_apply, iteratedFDerivWithin_zero_eq_comp, n.succ
-/
theorem iteratedFDerivWithin_succ_apply_right {n : Nat} (hs : UniqueDiffOn 𝕜 s) (hx : x in s)
    (m : Fin (n + 1) -> E) :
    (iteratedFDerivWithin 𝕜 (n + 1) f s x : (Fin (n + 1) -> E) -> F) m =
      iteratedFDerivWithin 𝕜 n (fun y => fderivWithin 𝕜 f s y) s x (init m) (m (last n)) := by
  induction n generalizing x with
  | zero =>
    rw [iteratedFDerivWithin_succ_eq_comp_left]; rw [iteratedFDerivWithin_zero_eq_comp]; rw [iteratedFDerivWithin_zero_apply]; rw [Function.comp_apply]; rw [LinearIsometryEquiv.comp_fderivWithin _ (hs x hx)]
    simp
  | succ n IH =>
    let I := (continuousMultilinearCurryRightEquiv' 𝕜 n E F).symm
    have A : forall y in s, iteratedFDerivWithin 𝕜 n.succ f s y =
        (I ∘ iteratedFDerivWithin 𝕜 n (fun y => fderivWithin 𝕜 f s y) s) y := fun y hy => by
      ext m
      simp [IH hy m, I]
    calc
      (iteratedFDerivWithin 𝕜 (n + 2) f s x : (Fin (n + 2) -> E) -> F) m =
          (fderivWithin 𝕜 (iteratedFDerivWithin 𝕜 n.succ f s) s x : E -> E [×n + 1]->L[𝕜] F) (m 0)
            (tail m) := by
        simp [iteratedFDerivWithin_succ_eq_comp_left]
      _ = (fderivWithin 𝕜 (I ∘ iteratedFDerivWithin 𝕜 n (fderivWithin 𝕜 f s) s) s x :
              E -> E [×n + 1]->L[𝕜] F) (m 0) (tail m) := by
        rw [fderivWithin_congr A (A x hx)]
      _ = (I ∘ fderivWithin 𝕜 (iteratedFDerivWithin 𝕜 n (fderivWithin 𝕜 f s) s) s x :
              E -> E [×n + 1]->L[𝕜] F) (m 0) (tail m) := by
        simp [LinearIsometryEquiv.comp_fderivWithin _ (hs x hx)]
      _ = (fderivWithin 𝕜 (iteratedFDerivWithin 𝕜 n (fun y => fderivWithin 𝕜 f s y) s) s x :
              E -> E [×n]->L[𝕜] E ->L[𝕜] F) (m 0) (init (tail m)) ((tail m) (last n)) := by
        simp [I]
      _ = iteratedFDerivWithin 𝕜 (Nat.succ n) (fun y => fderivWithin 𝕜 f s y) s x (init m)
            (m (last (n + 1))) := by
        rw [iteratedFDerivWithin_succ_apply_left]; rw [tail_init_eq_init_tail]
        simp [init, tail]

/--
theorem `iteratedFDerivWithin_succ_eq_comp_right` / 定理 `iteratedFDerivWithin_succ_eq_comp_right`

English:
theorem iteratedFDerivWithin_succ_eq_comp_right
  given: {n : Nat} (hs : UniqueDiffOn 𝕜 s) (hx : x in s)
  proof: by
  ext m; simp [iteratedFDerivWithin_succ_apply_right hs hx]

中文:
定理 iteratedFDerivWithin_succ_eq_comp_right
  条件: {n : 自然数} (hs : UniqueDiffOn 𝕜 s) (hx : x in s)
  证明: by
  ext m; simp [iteratedFDerivWithin_succ_apply_right hs hx]

Depends on / 依赖: iteratedFDerivWithin_succ_apply_right
-/
theorem iteratedFDerivWithin_succ_eq_comp_right {n : Nat} (hs : UniqueDiffOn 𝕜 s) (hx : x in s) :
    iteratedFDerivWithin 𝕜 (n + 1) f s x =
      ((continuousMultilinearCurryRightEquiv' 𝕜 n E F).symm ∘
          iteratedFDerivWithin 𝕜 n (fun y => fderivWithin 𝕜 f s y) s)
        x := by
  ext m; simp [iteratedFDerivWithin_succ_apply_right hs hx]

/--
theorem `norm_iteratedFDerivWithin_fderivWithin` / 定理 `norm_iteratedFDerivWithin_fderivWithin`

English:
theorem norm_iteratedFDerivWithin_fderivWithin
  given: {n : Nat} (hs : UniqueDiffOn 𝕜 s) (hx : x in s)
  proof: by
  rw [iteratedFDerivWithin_succ_eq_comp_right hs hx]; rw [comp_apply]; rw [LinearIsometryEquiv.norm_map]

@[simp]

中文:
定理 norm_iteratedFDerivWithin_fderivWithin
  条件: {n : 自然数} (hs : UniqueDiffOn 𝕜 s) (hx : x in s)
  证明: by
  rw [iteratedFDerivWithin_succ_eq_comp_right hs hx]; rw [comp_apply]; rw [LinearIsometryEquiv.norm_map]

@[simp]

Depends on / 依赖: LinearIsometryEquiv, LinearIsometryEquiv.norm_map, comp_apply, iteratedFDerivWithin_succ_eq_comp_right, norm_map
-/
theorem norm_iteratedFDerivWithin_fderivWithin {n : Nat} (hs : UniqueDiffOn 𝕜 s) (hx : x in s) :
    ‖iteratedFDerivWithin 𝕜 n (fderivWithin 𝕜 f s) s x‖ =
      ‖iteratedFDerivWithin 𝕜 (n + 1) f s x‖ := by
  rw [iteratedFDerivWithin_succ_eq_comp_right hs hx]; rw [comp_apply]; rw [LinearIsometryEquiv.norm_map]

@[simp]
/--
theorem `iteratedFDerivWithin_one_apply` / 定理 `iteratedFDerivWithin_one_apply`

English:
theorem iteratedFDerivWithin_one_apply
  given: (h : UniqueDiffWithinAt 𝕜 s x) (m : Fin 1 -> E)
  proof: by
  simp [iteratedFDerivWithin_succ_apply_left, iteratedFDerivWithin_zero_eq_comp,
    (continuousMultilinearCurryFin0 𝕜 E F).symm.comp_fderivWithin h]

中文:
定理 iteratedFDerivWithin_one_apply
  条件: (h : UniqueDiffWithinAt 𝕜 s x) (m : Fin 1 -> E)
  证明: by
  simp [iteratedFDerivWithin_succ_apply_left, iteratedFDerivWithin_zero_eq_comp,
    (continuousMultilinearCurryFin0 𝕜 E F).symm.comp_fderivWithin h]

Depends on / 依赖: comp_fderivWithin, continuousMultilinearCurryFin0, iteratedFDerivWithin_succ_apply_left, iteratedFDerivWithin_zero_eq_comp, symm.comp_fderivWithin
-/
theorem iteratedFDerivWithin_one_apply (h : UniqueDiffWithinAt 𝕜 s x) (m : Fin 1 -> E) :
    iteratedFDerivWithin 𝕜 1 f s x m = fderivWithin 𝕜 f s x (m 0) := by
  simp [iteratedFDerivWithin_succ_apply_left, iteratedFDerivWithin_zero_eq_comp,
    (continuousMultilinearCurryFin0 𝕜 E F).symm.comp_fderivWithin h]

/--
lemma `iteratedFDerivWithin_two_apply` / 引理 `iteratedFDerivWithin_two_apply`

English:
lemma iteratedFDerivWithin_two_apply
  statement: (f : E -> F) {z : E} (hs : UniqueDiffOn 𝕜 s) (hz : z in s)
  proof: by
  simp only [iteratedFDerivWithin_succ_apply_right hs hz]
  rfl

中文:
引理 iteratedFDerivWithin_two_apply
  结论: (f : E -> F) {z : E} (hs : UniqueDiffOn 𝕜 s) (hz : z in s)
  证明: by
  simp only [iteratedFDerivWithin_succ_apply_right hs hz]
  rfl

Depends on / 依赖: iteratedFDerivWithin_succ_apply_right
-/
lemma iteratedFDerivWithin_two_apply (f : E -> F) {z : E} (hs : UniqueDiffOn 𝕜 s) (hz : z in s)
    (m : Fin 2 -> E) :
    iteratedFDerivWithin 𝕜 2 f s z m = fderivWithin 𝕜 (fderivWithin 𝕜 f s) s z (m 0) (m 1) := by
  simp only [iteratedFDerivWithin_succ_apply_right hs hz]
  rfl

/--
lemma `iteratedFDerivWithin_two_apply'` / 引理 `iteratedFDerivWithin_two_apply'`

English:
lemma iteratedFDerivWithin_two_apply'
  statement: (f : E -> F) {z : E} (hs : UniqueDiffOn 𝕜 s) (hz : z in s)
  proof: iteratedFDerivWithin_two_apply f hs hz _

中文:
引理 iteratedFDerivWithin_two_apply'
  结论: (f : E -> F) {z : E} (hs : UniqueDiffOn 𝕜 s) (hz : z in s)
  证明: iteratedFDerivWithin_two_apply f hs hz _

Depends on / 依赖: iteratedFDerivWithin_two_apply
-/
lemma iteratedFDerivWithin_two_apply' (f : E -> F) {z : E} (hs : UniqueDiffOn 𝕜 s) (hz : z in s)
    (v w : E) :
    iteratedFDerivWithin 𝕜 2 f s z ![v, w] = fderivWithin 𝕜 (fderivWithin 𝕜 f s) s z v w :=
  iteratedFDerivWithin_two_apply f hs hz _

/--
theorem `Filter.EventuallyEq.iteratedFDerivWithin'` / 定理 `Filter.EventuallyEq.iteratedFDerivWithin'`

English:
theorem Filter.EventuallyEq.iteratedFDerivWithin'
  given: (h : f₁ =ᶠ[𝓝[s] x] f) (ht : t subseteq s) (n : Nat)
  proof: by
  induction n with
  | zero => exact h.mono fun y hy => DFunLike.ext _ _ fun _ => hy
  | succ n ihn =>
    have : fderivWithin 𝕜 _ t =ᶠ[𝓝[s] x] fderivWithin 𝕜 _ t := ihn.fderivWithin' ht
    refine this.mono fun y hy => ?_
    simp only [iteratedFDerivWithin_succ_eq_comp_left, hy, (· ∘ ·)]

中文:
定理 Filter.EventuallyEq.iteratedFDerivWithin'
  条件: (h : f₁ =ᶠ[𝓝[s] x] f) (ht : t subseteq s) (n : 自然数)
  证明: by
  induction n with
  | zero => exact h.mono fun y hy => DFunLike.ext _ _ fun _ => hy
  | succ n ihn =>
    have : fderivWithin 𝕜 _ t =ᶠ[𝓝[s] x] fderivWithin 𝕜 _ t := ihn.fderivWithin' ht
    refine this.mono fun y hy => ?_
    simp only [iteratedFDerivWithin_succ_eq_comp_left, hy, (· ∘ ·)]

Depends on / 依赖: DFunLike, DFunLike.ext, fderivWithin, h.mono, ihn.fderivWithin, iteratedFDerivWithin_succ_eq_comp_left, this.mono
-/
theorem Filter.EventuallyEq.iteratedFDerivWithin' (h : f₁ =ᶠ[𝓝[s] x] f) (ht : t subseteq s) (n : Nat) :
    iteratedFDerivWithin 𝕜 n f₁ t =ᶠ[𝓝[s] x] iteratedFDerivWithin 𝕜 n f t := by
  induction n with
  | zero => exact h.mono fun y hy => DFunLike.ext _ _ fun _ => hy
  | succ n ihn =>
    have : fderivWithin 𝕜 _ t =ᶠ[𝓝[s] x] fderivWithin 𝕜 _ t := ihn.fderivWithin' ht
    refine this.mono fun y hy => ?_
    simp only [iteratedFDerivWithin_succ_eq_comp_left, hy, (· ∘ ·)]

variable (𝕜) in
/--
theorem `Filter.EventuallyEq.iteratedFDerivWithin` / 定理 `Filter.EventuallyEq.iteratedFDerivWithin`

English:
theorem Filter.EventuallyEq.iteratedFDerivWithin
  given: (h : f₁ =ᶠ[𝓝[s] x] f) (n : Nat)
  proof: h.iteratedFDerivWithin' Subset.rfl n

中文:
定理 Filter.EventuallyEq.iteratedFDerivWithin
  条件: (h : f₁ =ᶠ[𝓝[s] x] f) (n : 自然数)
  证明: h.iteratedFDerivWithin' Subset.rfl n
-/
protected theorem Filter.EventuallyEq.iteratedFDerivWithin (h : f₁ =ᶠ[𝓝[s] x] f) (n : Nat) :
    iteratedFDerivWithin 𝕜 n f₁ s =ᶠ[𝓝[s] x] iteratedFDerivWithin 𝕜 n f s :=
  h.iteratedFDerivWithin' Subset.rfl n

variable (𝕜) in
/--
theorem `Filter.EventuallyEq.ftaylorSeriesWithin` / 定理 `Filter.EventuallyEq.ftaylorSeriesWithin`

English:
theorem Filter.EventuallyEq.ftaylorSeriesWithin
  given: (h : f₁ =ᶠ[𝓝[s] x] f)
  proof: by
  filter_upwards [eventually_eventually_nhdsWithin.2 h, self_mem_nhdsWithin] with x₁ h₁x₁ h₂x₁
  ext n : 1
  apply (Filter.EventuallyEq.iteratedFDerivWithin (𝕜 := 𝕜) h₁x₁ n).eq_of_nhdsWithin h₂x₁

中文:
定理 Filter.EventuallyEq.ftaylorSeriesWithin
  条件: (h : f₁ =ᶠ[𝓝[s] x] f)
  证明: by
  filter_upwards [eventually_eventually_nhdsWithin.2 h, self_mem_nhdsWithin] with x₁ h₁x₁ h₂x₁
  ext n : 1
  apply (Filter.EventuallyEq.iteratedFDerivWithin (𝕜 := 𝕜) h₁x₁ n).eq_of_nhdsWithin h₂x₁
-/
protected theorem Filter.EventuallyEq.ftaylorSeriesWithin (h : f₁ =ᶠ[𝓝[s] x] f) :
    ftaylorSeriesWithin 𝕜 f₁ s =ᶠ[𝓝[s] x] ftaylorSeriesWithin 𝕜 f s := by
  filter_upwards [eventually_eventually_nhdsWithin.2 h, self_mem_nhdsWithin] with x₁ h₁x₁ h₂x₁
  ext n : 1
  apply (Filter.EventuallyEq.iteratedFDerivWithin (𝕜 := 𝕜) h₁x₁ n).eq_of_nhdsWithin h₂x₁

/--
theorem `Filter.EventuallyEq.iteratedFDerivWithin_eq` / 定理 `Filter.EventuallyEq.iteratedFDerivWithin_eq`

English:
theorem Filter.EventuallyEq.iteratedFDerivWithin_eq
  statement: (h : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x)
  proof: have : f₁ =ᶠ[𝓝[insert x s] x] f := by simpa [EventuallyEq, hx]
  (this.iteratedFDerivWithin' (subset_insert _ _) n).self_of_nhdsWithin (mem_insert _ _)

中文:
定理 Filter.EventuallyEq.iteratedFDerivWithin_eq
  结论: (h : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x)
  证明: have : f₁ =ᶠ[𝓝[insert x s] x] f := by simpa [EventuallyEq, hx]
  (this.iteratedFDerivWithin' (subset_insert _ _) n).self_of_nhdsWithin (mem_insert _ _)

Depends on / 依赖: EventuallyEq, insert, iteratedFDerivWithin, mem_insert, self_of_nhdsWithin, subset_insert, this.iteratedFDerivWithin
-/
theorem Filter.EventuallyEq.iteratedFDerivWithin_eq (h : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x)
    (n : Nat) : iteratedFDerivWithin 𝕜 n f₁ s x = iteratedFDerivWithin 𝕜 n f s x :=
  have : f₁ =ᶠ[𝓝[insert x s] x] f := by simpa [EventuallyEq, hx]
  (this.iteratedFDerivWithin' (subset_insert _ _) n).self_of_nhdsWithin (mem_insert _ _)

/--
theorem `iteratedFDerivWithin_congr` / 定理 `iteratedFDerivWithin_congr`

English:
theorem iteratedFDerivWithin_congr
  given: (hs : EqOn f₁ f s) (hx : x in s) (n : Nat)
  proof: (hs.eventuallyEq.filter_mono inf_le_right).iteratedFDerivWithin_eq (hs hx) _

中文:
定理 iteratedFDerivWithin_congr
  条件: (hs : EqOn f₁ f s) (hx : x in s) (n : 自然数)
  证明: (hs.eventuallyEq.filter_mono inf_le_right).iteratedFDerivWithin_eq (hs hx) _

Depends on / 依赖: eventuallyEq, filter_mono, hs.eventuallyEq.filter_mono, inf_le_right, iteratedFDerivWithin_eq
-/
theorem iteratedFDerivWithin_congr (hs : EqOn f₁ f s) (hx : x in s) (n : Nat) :
    iteratedFDerivWithin 𝕜 n f₁ s x = iteratedFDerivWithin 𝕜 n f s x :=
  (hs.eventuallyEq.filter_mono inf_le_right).iteratedFDerivWithin_eq (hs hx) _

/--
theorem `Set.EqOn.iteratedFDerivWithin` / 定理 `Set.EqOn.iteratedFDerivWithin`

English:
theorem Set.EqOn.iteratedFDerivWithin
  given: (hs : EqOn f₁ f s) (n : Nat)
  proof: fun _x hx =>
  iteratedFDerivWithin_congr hs hx n

中文:
定理 Set.EqOn.iteratedFDerivWithin
  条件: (hs : EqOn f₁ f s) (n : 自然数)
  证明: fun _x hx =>
  iteratedFDerivWithin_congr hs hx n
-/
protected theorem Set.EqOn.iteratedFDerivWithin (hs : EqOn f₁ f s) (n : Nat) :
    EqOn (iteratedFDerivWithin 𝕜 n f₁ s) (iteratedFDerivWithin 𝕜 n f s) s := fun _x hx =>
  iteratedFDerivWithin_congr hs hx n

/--
theorem `iteratedFDerivWithin_eventually_congr_set'` / 定理 `iteratedFDerivWithin_eventually_congr_set'`

English:
theorem iteratedFDerivWithin_eventually_congr_set'
  given: (y : E) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) (n : Nat)
  proof: by
  induction n generalizing x with
  | zero => rfl
  | succ n ihn =>
    refine (eventually_nhds_nhdsWithin.2 h).mono fun y hy => ?_
    simp only [iteratedFDerivWithin_succ_eq_comp_left, (· ∘ ·)]
    rw [(ihn hy).fderivWithin_eq_of_nhds]; rw [fderivWithin_congr_set' _ hy]

中文:
定理 iteratedFDerivWithin_eventually_congr_set'
  条件: (y : E) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) (n : 自然数)
  证明: by
  induction n generalizing x with
  | zero => rfl
  | succ n ihn =>
    refine (eventually_nhds_nhdsWithin.2 h).mono fun y hy => ?_
    simp only [iteratedFDerivWithin_succ_eq_comp_left, (· ∘ ·)]
    rw [(ihn hy).fderivWithin_eq_of_nhds]; rw [fderivWithin_congr_set' _ hy]

Depends on / 依赖: eventually_nhds_nhdsWithin, fderivWithin_congr_set, fderivWithin_eq_of_nhds, generalizing, iteratedFDerivWithin_succ_eq_comp_left
-/
theorem iteratedFDerivWithin_eventually_congr_set' (y : E) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) (n : Nat) :
    iteratedFDerivWithin 𝕜 n f s =ᶠ[𝓝 x] iteratedFDerivWithin 𝕜 n f t := by
  induction n generalizing x with
  | zero => rfl
  | succ n ihn =>
    refine (eventually_nhds_nhdsWithin.2 h).mono fun y hy => ?_
    simp only [iteratedFDerivWithin_succ_eq_comp_left, (· ∘ ·)]
    rw [(ihn hy).fderivWithin_eq_of_nhds]; rw [fderivWithin_congr_set' _ hy]

/--
theorem `iteratedFDerivWithin_eventually_congr_set` / 定理 `iteratedFDerivWithin_eventually_congr_set`

English:
theorem iteratedFDerivWithin_eventually_congr_set
  given: (h : s =ᶠ[𝓝 x] t) (n : Nat)
  proof: iteratedFDerivWithin_eventually_congr_set' x (h.filter_mono inf_le_left) n

中文:
定理 iteratedFDerivWithin_eventually_congr_set
  条件: (h : s =ᶠ[𝓝 x] t) (n : 自然数)
  证明: iteratedFDerivWithin_eventually_congr_set' x (h.filter_mono inf_le_left) n

Depends on / 依赖: filter_mono, h.filter_mono, inf_le_left, iteratedFDerivWithin_eventually_congr_set
-/
theorem iteratedFDerivWithin_eventually_congr_set (h : s =ᶠ[𝓝 x] t) (n : Nat) :
    iteratedFDerivWithin 𝕜 n f s =ᶠ[𝓝 x] iteratedFDerivWithin 𝕜 n f t :=
  iteratedFDerivWithin_eventually_congr_set' x (h.filter_mono inf_le_left) n

/--
theorem `iteratedFDerivWithin_congr_set'` / 定理 `iteratedFDerivWithin_congr_set'`

English:
theorem iteratedFDerivWithin_congr_set'
  given: {y} (h : s =ᶠ[𝓝[{y}ᶜ] x] t) (n : Nat)
  proof: (iteratedFDerivWithin_eventually_congr_set' y h n).self_of_nhds

@[simp]

中文:
定理 iteratedFDerivWithin_congr_set'
  条件: {y} (h : s =ᶠ[𝓝[{y}ᶜ] x] t) (n : 自然数)
  证明: (iteratedFDerivWithin_eventually_congr_set' y h n).self_of_nhds

@[simp]

Depends on / 依赖: iteratedFDerivWithin_eventually_congr_set, self_of_nhds
-/
theorem iteratedFDerivWithin_congr_set' {y} (h : s =ᶠ[𝓝[{y}ᶜ] x] t) (n : Nat) :
    iteratedFDerivWithin 𝕜 n f s x = iteratedFDerivWithin 𝕜 n f t x :=
  (iteratedFDerivWithin_eventually_congr_set' y h n).self_of_nhds

@[simp]
/--
theorem `iteratedFDerivWithin_insert` / 定理 `iteratedFDerivWithin_insert`

English:
theorem iteratedFDerivWithin_insert
  given: {n y}
  proof: iteratedFDerivWithin_congr_set' (y := x)
    (eventually_mem_nhdsWithin.mono <| by intros; simp_all).set_eq _

中文:
定理 iteratedFDerivWithin_insert
  条件: {n y}
  证明: iteratedFDerivWithin_congr_set' (y := x)
    (eventually_mem_nhdsWithin.mono <| by intros; simp_all).set_eq _

Depends on / 依赖: eventually_mem_nhdsWithin, eventually_mem_nhdsWithin.mono, intros, iteratedFDerivWithin_congr_set, set_eq
-/
theorem iteratedFDerivWithin_insert {n y} :
    iteratedFDerivWithin 𝕜 n f (insert x s) y = iteratedFDerivWithin 𝕜 n f s y :=
  iteratedFDerivWithin_congr_set' (y := x)
    (eventually_mem_nhdsWithin.mono <| by intros; simp_all).set_eq _

/--
theorem `iteratedFDerivWithin_congr_set` / 定理 `iteratedFDerivWithin_congr_set`

English:
theorem iteratedFDerivWithin_congr_set
  given: (h : s =ᶠ[𝓝 x] t) (n : Nat)
  proof: (iteratedFDerivWithin_eventually_congr_set h n).self_of_nhds

@[simp]

中文:
定理 iteratedFDerivWithin_congr_set
  条件: (h : s =ᶠ[𝓝 x] t) (n : 自然数)
  证明: (iteratedFDerivWithin_eventually_congr_set h n).self_of_nhds

@[simp]

Depends on / 依赖: iteratedFDerivWithin_eventually_congr_set, self_of_nhds
-/
theorem iteratedFDerivWithin_congr_set (h : s =ᶠ[𝓝 x] t) (n : Nat) :
    iteratedFDerivWithin 𝕜 n f s x = iteratedFDerivWithin 𝕜 n f t x :=
  (iteratedFDerivWithin_eventually_congr_set h n).self_of_nhds

@[simp]
/--
theorem `ftaylorSeriesWithin_insert` / 定理 `ftaylorSeriesWithin_insert`

English:
theorem ftaylorSeriesWithin_insert
  proof: by
  ext y n : 2
  apply iteratedFDerivWithin_insert

中文:
定理 ftaylorSeriesWithin_insert
  证明: by
  ext y n : 2
  apply iteratedFDerivWithin_insert

Depends on / 依赖: iteratedFDerivWithin_insert
-/
theorem ftaylorSeriesWithin_insert :
    ftaylorSeriesWithin 𝕜 f (insert x s) = ftaylorSeriesWithin 𝕜 f s := by
  ext y n : 2
  apply iteratedFDerivWithin_insert

/--
theorem `iteratedFDerivWithin_inter'` / 定理 `iteratedFDerivWithin_inter'`

English:
theorem iteratedFDerivWithin_inter'
  given: {n : Nat} (hu : u in 𝓝[s] x)
  proof: iteratedFDerivWithin_congr_set (nhdsWithin_eq_iff_eventuallyEq.1 <| nhdsWithin_inter_of_mem' hu) _

中文:
定理 iteratedFDerivWithin_inter'
  条件: {n : 自然数} (hu : u in 𝓝[s] x)
  证明: iteratedFDerivWithin_congr_set (nhdsWithin_eq_iff_eventuallyEq.1 <| nhdsWithin_inter_of_mem' hu) _

Depends on / 依赖: iteratedFDerivWithin_congr_set, nhdsWithin_eq_iff_eventuallyEq, nhdsWithin_inter_of_mem
-/
theorem iteratedFDerivWithin_inter' {n : Nat} (hu : u in 𝓝[s] x) :
    iteratedFDerivWithin 𝕜 n f (s inter u) x = iteratedFDerivWithin 𝕜 n f s x :=
  iteratedFDerivWithin_congr_set (nhdsWithin_eq_iff_eventuallyEq.1 <| nhdsWithin_inter_of_mem' hu) _

/--
theorem `iteratedFDerivWithin_inter` / 定理 `iteratedFDerivWithin_inter`

English:
theorem iteratedFDerivWithin_inter
  given: {n : Nat} (hu : u in 𝓝 x)
  proof: iteratedFDerivWithin_inter' (mem_nhdsWithin_of_mem_nhds hu)

中文:
定理 iteratedFDerivWithin_inter
  条件: {n : 自然数} (hu : u in 𝓝 x)
  证明: iteratedFDerivWithin_inter' (mem_nhdsWithin_of_mem_nhds hu)

Depends on / 依赖: iteratedFDerivWithin_inter, mem_nhdsWithin_of_mem_nhds
-/
theorem iteratedFDerivWithin_inter {n : Nat} (hu : u in 𝓝 x) :
    iteratedFDerivWithin 𝕜 n f (s inter u) x = iteratedFDerivWithin 𝕜 n f s x :=
  iteratedFDerivWithin_inter' (mem_nhdsWithin_of_mem_nhds hu)

/--
theorem `iteratedFDerivWithin_inter_open` / 定理 `iteratedFDerivWithin_inter_open`

English:
theorem iteratedFDerivWithin_inter_open
  given: {n : Nat} (hu : IsOpen u) (hx : x in u)
  proof: iteratedFDerivWithin_inter (hu.mem_nhds hx)

中文:
定理 iteratedFDerivWithin_inter_open
  条件: {n : 自然数} (hu : IsOpen u) (hx : x in u)
  证明: iteratedFDerivWithin_inter (hu.mem_nhds hx)

Depends on / 依赖: hu.mem_nhds, iteratedFDerivWithin_inter, mem_nhds
-/
theorem iteratedFDerivWithin_inter_open {n : Nat} (hu : IsOpen u) (hx : x in u) :
    iteratedFDerivWithin 𝕜 n f (s inter u) x = iteratedFDerivWithin 𝕜 n f s x :=
  iteratedFDerivWithin_inter (hu.mem_nhds hx)

/--
theorem `HasFTaylorSeriesUpToOn.eq_iteratedFDerivWithin_of_uniqueDiffOn` / 定理 `HasFTaylorSeriesUpToOn.eq_iteratedFDerivWithin_of_uniqueDiffOn`

English:
theorem HasFTaylorSeriesUpToOn.eq_iteratedFDerivWithin_of_uniqueDiffOn
  proof: by
  induction m generalizing x with
  | zero => rw [h.zero_eq' hx, iteratedFDerivWithin_zero_eq_comp, comp_apply]
  | succ m IH =>
    have A : m < n := lt_of_lt_of_le (mod_cast lt_add_one m) hmn
    have :
      HasFDerivWithinAt (fun y : E => iteratedFDerivWithin 𝕜 m f s y)
        (ContinuousMul

中文:
定理 HasFTaylorSeriesUpToOn.eq_iteratedFDerivWithin_of_uniqueDiffOn
  证明: by
  induction m generalizing x with
  | zero => rw [h.zero_eq' hx, iteratedFDerivWithin_zero_eq_comp, comp_apply]
  | succ m IH =>
    have A : m < n := lt_of_lt_of_le (mod_cast lt_add_one m) hmn
    have :
      HasFDerivWithinAt (fun y : E => iteratedFDerivWithin 𝕜 m f s y)
        (ContinuousMul

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.curryLeft, Function, Function.comp_apply, HasFDerivWithinAt, Nat.succ, comp_apply, curryLeft, fderivWithin, generalizing, h.fderivWithin, h.zero_eq, iteratedFDerivWithin, iteratedFDerivWithin_succ_eq_comp_left, iteratedFDerivWithin_zero_eq_comp, le_of_lt, lt_add_one, lt_of_lt_of_le, mod_cast, this.f
-/
theorem HasFTaylorSeriesUpToOn.eq_iteratedFDerivWithin_of_uniqueDiffOn
    (h : HasFTaylorSeriesUpToOn n f p s) {m : Nat} (hmn : m <= n) (hs : UniqueDiffOn 𝕜 s)
    (hx : x in s) : p x m = iteratedFDerivWithin 𝕜 m f s x := by
  induction m generalizing x with
  | zero => rw [h.zero_eq' hx, iteratedFDerivWithin_zero_eq_comp, comp_apply]
  | succ m IH =>
    have A : m < n := lt_of_lt_of_le (mod_cast lt_add_one m) hmn
    have :
      HasFDerivWithinAt (fun y : E => iteratedFDerivWithin 𝕜 m f s y)
        (ContinuousMultilinearMap.curryLeft (p x (Nat.succ m))) s x :=
      (h.fderivWithin m A x hx).congr (fun y hy => (IH (le_of_lt A) hy).symm)
        (IH (le_of_lt A) hx).symm
    rw [iteratedFDerivWithin_succ_eq_comp_left]; rw [Function.comp_apply]; rw [this.fderivWithin (hs x hx)]
    exact (ContinuousMultilinearMap.uncurry_curryLeft _).symm

/--
lemma `iteratedFDerivWithin_comp_add_left'` / 引理 `iteratedFDerivWithin_comp_add_left'`

English:
lemma iteratedFDerivWithin_comp_add_left'
  given: (n : Nat) (a : E)
  proof: by
  induction n with
  | zero => simp [iteratedFDerivWithin]
  | succ n IH =>
    ext v
    simp [iteratedFDerivWithin_succ_eq_comp_left, IH, fderivWithin_comp_add_left]

中文:
引理 iteratedFDerivWithin_comp_add_left'
  条件: (n : 自然数) (a : E)
  证明: by
  induction n with
  | zero => simp [iteratedFDerivWithin]
  | succ n IH =>
    ext v
    simp [iteratedFDerivWithin_succ_eq_comp_left, IH, fderivWithin_comp_add_left]

Depends on / 依赖: fderivWithin_comp_add_left, iteratedFDerivWithin, iteratedFDerivWithin_succ_eq_comp_left
-/
lemma iteratedFDerivWithin_comp_add_left' (n : Nat) (a : E) :
    iteratedFDerivWithin 𝕜 n (fun z => f (a + z)) s =
      fun x => iteratedFDerivWithin 𝕜 n f (a +ᵥ s) (a + x) := by
  induction n with
  | zero => simp [iteratedFDerivWithin]
  | succ n IH =>
    ext v
    simp [iteratedFDerivWithin_succ_eq_comp_left, IH, fderivWithin_comp_add_left]

/--
lemma `iteratedFDerivWithin_comp_add_left` / 引理 `iteratedFDerivWithin_comp_add_left`

English:
lemma iteratedFDerivWithin_comp_add_left
  given: (n : Nat) (a : E) (x : E)
  proof: by
  simp [iteratedFDerivWithin_comp_add_left']

中文:
引理 iteratedFDerivWithin_comp_add_left
  条件: (n : 自然数) (a : E) (x : E)
  证明: by
  simp [iteratedFDerivWithin_comp_add_left']

Depends on / 依赖: iteratedFDerivWithin_comp_add_left
-/
lemma iteratedFDerivWithin_comp_add_left (n : Nat) (a : E) (x : E) :
    iteratedFDerivWithin 𝕜 n (fun z => f (a + z)) s x =
      iteratedFDerivWithin 𝕜 n f (a +ᵥ s) (a + x) := by
  simp [iteratedFDerivWithin_comp_add_left']

/--
lemma `iteratedFDerivWithin_comp_add_right'` / 引理 `iteratedFDerivWithin_comp_add_right'`

English:
lemma iteratedFDerivWithin_comp_add_right'
  given: (n : Nat) (a : E)
  proof: by
  simpa [add_comm a] using iteratedFDerivWithin_comp_add_left' n a

中文:
引理 iteratedFDerivWithin_comp_add_right'
  条件: (n : 自然数) (a : E)
  证明: by
  simpa [add_comm a] using iteratedFDerivWithin_comp_add_left' n a

Depends on / 依赖: add_comm, iteratedFDerivWithin_comp_add_left
-/
lemma iteratedFDerivWithin_comp_add_right' (n : Nat) (a : E) :
    iteratedFDerivWithin 𝕜 n (fun z => f (z + a)) s =
      fun x => iteratedFDerivWithin 𝕜 n f (a +ᵥ s) (x + a) := by
  simpa [add_comm a] using iteratedFDerivWithin_comp_add_left' n a

/--
lemma `iteratedFDerivWithin_comp_add_right` / 引理 `iteratedFDerivWithin_comp_add_right`

English:
lemma iteratedFDerivWithin_comp_add_right
  given: (n : Nat) (a : E) (x : E)
  proof: by
  simp [iteratedFDerivWithin_comp_add_right']

中文:
引理 iteratedFDerivWithin_comp_add_right
  条件: (n : 自然数) (a : E) (x : E)
  证明: by
  simp [iteratedFDerivWithin_comp_add_right']

Depends on / 依赖: iteratedFDerivWithin_comp_add_right
-/
lemma iteratedFDerivWithin_comp_add_right (n : Nat) (a : E) (x : E) :
    iteratedFDerivWithin 𝕜 n (fun z => f (z + a)) s x =
      iteratedFDerivWithin 𝕜 n f (a +ᵥ s) (x + a) := by
  simp [iteratedFDerivWithin_comp_add_right']

/--
lemma `iteratedFDerivWithin_comp_sub'` / 引理 `iteratedFDerivWithin_comp_sub'`

English:
lemma iteratedFDerivWithin_comp_sub'
  given: (n : Nat) (a : E)
  proof: by
  simpa [sub_eq_add_neg] using iteratedFDerivWithin_comp_add_right' n (-a)

中文:
引理 iteratedFDerivWithin_comp_sub'
  条件: (n : 自然数) (a : E)
  证明: by
  simpa [sub_eq_add_neg] using iteratedFDerivWithin_comp_add_right' n (-a)

Depends on / 依赖: iteratedFDerivWithin_comp_add_right, sub_eq_add_neg
-/
lemma iteratedFDerivWithin_comp_sub' (n : Nat) (a : E) :
    iteratedFDerivWithin 𝕜 n (fun z => f (z - a)) s =
      fun x => iteratedFDerivWithin 𝕜 n f (-a +ᵥ s) (x - a) := by
  simpa [sub_eq_add_neg] using iteratedFDerivWithin_comp_add_right' n (-a)

/--
lemma `iteratedFDerivWithin_comp_sub` / 引理 `iteratedFDerivWithin_comp_sub`

English:
lemma iteratedFDerivWithin_comp_sub
  given: (n : Nat) (a : E)
  proof: by
  simp [iteratedFDerivWithin_comp_sub']

中文:
引理 iteratedFDerivWithin_comp_sub
  条件: (n : 自然数) (a : E)
  证明: by
  simp [iteratedFDerivWithin_comp_sub']

Depends on / 依赖: iteratedFDerivWithin_comp_sub
-/
lemma iteratedFDerivWithin_comp_sub (n : Nat) (a : E) :
    iteratedFDerivWithin 𝕜 n (fun z => f (z - a)) s x =
      iteratedFDerivWithin 𝕜 n f (-a +ᵥ s) (x - a) := by
  simp [iteratedFDerivWithin_comp_sub']

/-! ### Functions with a Taylor series on the whole space -/

/--
Definition of `HasFTaylorSeriesUpTo` / `HasFTaylorSeriesUpTo` 的定义

English:
structure HasFTaylorSeriesUpTo
  axioms and operations (3):
    - zero_eq : forall x, (p x 0).curry0 = f x
    - fderiv : forall m : Nat, m < n -> forall x, HasFDerivAt (fun y => p y m) (p x m.succ).curryLeft x
    - cont : forall m : Nat, m <= n -> Continuous fun x => p x m

中文:
结构 HasFTaylorSeriesUpTo
  公理与运算 (3 个):
    - zero_eq : 对任意 x, (p x 0).curry0 = f x
    - fderiv : 对任意 m : 自然数, m < n -> 对任意 x, HasFDerivAt (fun y => p y m) (p x m.succ).curryLeft x
    - cont : 对任意 m : 自然数, m <= n -> Continuous fun x => p x m
-/
structure HasFTaylorSeriesUpTo
  (n : Nat∞ω) (f : E -> F) (p : E -> FormalMultilinearSeries 𝕜 E F) : Prop where
  zero_eq : forall x, (p x 0).curry0 = f x
  protected fderiv : forall m : Nat, m < n -> forall x, HasFDerivAt (fun y => p y m) (p x m.succ).curryLeft x
  cont : forall m : Nat, m <= n -> Continuous fun x => p x m

/--
theorem `HasFTaylorSeriesUpTo.zero_eq'` / 定理 `HasFTaylorSeriesUpTo.zero_eq'`

English:
theorem HasFTaylorSeriesUpTo.zero_eq'
  given: (h : HasFTaylorSeriesUpTo n f p) (x : E)
  proof: by
  rw [← h.zero_eq x]
  exact (p x 0).uncurry0_curry0.symm

中文:
定理 HasFTaylorSeriesUpTo.zero_eq'
  条件: (h : HasFTaylorSeriesUpTo n f p) (x : E)
  证明: by
  rw [← h.zero_eq x]
  exact (p x 0).uncurry0_curry0.symm

Depends on / 依赖: h.zero_eq, uncurry0_curry0, uncurry0_curry0.symm, zero_eq
-/
theorem HasFTaylorSeriesUpTo.zero_eq' (h : HasFTaylorSeriesUpTo n f p) (x : E) :
    p x 0 = (continuousMultilinearCurryFin0 𝕜 E F).symm (f x) := by
  rw [← h.zero_eq x]
  exact (p x 0).uncurry0_curry0.symm

/--
lemma `HasFTaylorSeriesUpTo.fderiv_eq` / 引理 `HasFTaylorSeriesUpTo.fderiv_eq`

English:
lemma HasFTaylorSeriesUpTo.fderiv_eq
  statement: (h : HasFTaylorSeriesUpTo n f p)
  proof: .fderiv h.fderiv m hmn x

中文:
引理 HasFTaylorSeriesUpTo.fderiv_eq
  结论: (h : HasFTaylorSeriesUpTo n f p)
  证明: .fderiv h.fderiv m hmn x

Depends on / 依赖: fderiv, h.fderiv
-/
lemma HasFTaylorSeriesUpTo.fderiv_eq (h : HasFTaylorSeriesUpTo n f p)
    {m : Nat} (hmn : m < n) (x : E) : fderiv 𝕜 (p · m) x = (p x m.succ).curryLeft :=
.fderiv h.fderiv m hmn x

/--
theorem `hasFTaylorSeriesUpToOn_univ_iff` / 定理 `hasFTaylorSeriesUpToOn_univ_iff`

English:
theorem hasFTaylorSeriesUpToOn_univ_iff
  proof: by
  constructor <;> refine fun H => ⟨by simpa using H.zero_eq, ?_, by simpa using H.cont⟩
  · simpa using H.fderivWithin
  · simpa using H.fderiv

中文:
定理 hasFTaylorSeriesUpToOn_univ_iff
  证明: by
  constructor <;> refine fun H => ⟨by simpa using H.zero_eq, ?_, by simpa using H.cont⟩
  · simpa using H.fderivWithin
  · simpa using H.fderiv

Depends on / 依赖: H.cont, H.fderiv, H.fderivWithin, H.zero_eq, fderiv, fderivWithin, zero_eq
-/
theorem hasFTaylorSeriesUpToOn_univ_iff :
    HasFTaylorSeriesUpToOn n f p univ ↔ HasFTaylorSeriesUpTo n f p := by
  constructor <;> refine fun H => ⟨by simpa using H.zero_eq, ?_, by simpa using H.cont⟩
  · simpa using H.fderivWithin
  · simpa using H.fderiv

/--
theorem `HasFTaylorSeriesUpTo.hasFTaylorSeriesUpToOn` / 定理 `HasFTaylorSeriesUpTo.hasFTaylorSeriesUpToOn`

English:
theorem HasFTaylorSeriesUpTo.hasFTaylorSeriesUpToOn
  given: (h : HasFTaylorSeriesUpTo n f p) (s : Set E)
  proof: (hasFTaylorSeriesUpToOn_univ_iff.2 h).mono (subset_univ _)

中文:
定理 HasFTaylorSeriesUpTo.hasFTaylorSeriesUpToOn
  条件: (h : HasFTaylorSeriesUpTo n f p) (s : Set E)
  证明: (hasFTaylorSeriesUpToOn_univ_iff.2 h).mono (subset_univ _)

Depends on / 依赖: hasFTaylorSeriesUpToOn_univ_iff, subset_univ
-/
theorem HasFTaylorSeriesUpTo.hasFTaylorSeriesUpToOn (h : HasFTaylorSeriesUpTo n f p) (s : Set E) :
    HasFTaylorSeriesUpToOn n f p s :=
  (hasFTaylorSeriesUpToOn_univ_iff.2 h).mono (subset_univ _)

/--
theorem `HasFTaylorSeriesUpTo.of_le` / 定理 `HasFTaylorSeriesUpTo.of_le`

English:
theorem HasFTaylorSeriesUpTo.of_le
  given: (h : HasFTaylorSeriesUpTo n f p) (hmn : m <= n)
  proof: by
  rw [← hasFTaylorSeriesUpToOn_univ_iff] at h ⊢; exact h.of_le hmn

中文:
定理 HasFTaylorSeriesUpTo.of_le
  条件: (h : HasFTaylorSeriesUpTo n f p) (hmn : m <= n)
  证明: by
  rw [← hasFTaylorSeriesUpToOn_univ_iff] at h ⊢; exact h.of_le hmn

Depends on / 依赖: h.of_le, hasFTaylorSeriesUpToOn_univ_iff, of_le
-/
theorem HasFTaylorSeriesUpTo.of_le (h : HasFTaylorSeriesUpTo n f p) (hmn : m <= n) :
    HasFTaylorSeriesUpTo m f p := by
  rw [← hasFTaylorSeriesUpToOn_univ_iff] at h ⊢; exact h.of_le hmn

/--
theorem `HasFTaylorSeriesUpTo.continuous` / 定理 `HasFTaylorSeriesUpTo.continuous`

English:
theorem HasFTaylorSeriesUpTo.continuous
  given: (h : HasFTaylorSeriesUpTo n f p)
  statement: Continuous f
  proof: by
  rw [← hasFTaylorSeriesUpToOn_univ_iff] at h
  rw [← continuousOn_univ]
  exact h.continuousOn

中文:
定理 HasFTaylorSeriesUpTo.continuous
  条件: (h : HasFTaylorSeriesUpTo n f p)
  结论: Continuous f
  证明: by
  rw [← hasFTaylorSeriesUpToOn_univ_iff] at h
  rw [← continuousOn_univ]
  exact h.continuousOn

Depends on / 依赖: continuousOn, continuousOn_univ, h.continuousOn, hasFTaylorSeriesUpToOn_univ_iff
-/
theorem HasFTaylorSeriesUpTo.continuous (h : HasFTaylorSeriesUpTo n f p) : Continuous f := by
  rw [← hasFTaylorSeriesUpToOn_univ_iff] at h
  rw [← continuousOn_univ]
  exact h.continuousOn

/--
theorem `hasFTaylorSeriesUpTo_zero_iff` / 定理 `hasFTaylorSeriesUpTo_zero_iff`

English:
theorem hasFTaylorSeriesUpTo_zero_iff
  proof: by
  simp [hasFTaylorSeriesUpToOn_univ_iff.symm, continuousOn_univ,
    hasFTaylorSeriesUpToOn_zero_iff]

中文:
定理 hasFTaylorSeriesUpTo_zero_iff
  证明: by
  simp [hasFTaylorSeriesUpToOn_univ_iff.symm, continuousOn_univ,
    hasFTaylorSeriesUpToOn_zero_iff]

Depends on / 依赖: continuousOn_univ, hasFTaylorSeriesUpToOn_univ_iff, hasFTaylorSeriesUpToOn_univ_iff.symm, hasFTaylorSeriesUpToOn_zero_iff
-/
theorem hasFTaylorSeriesUpTo_zero_iff :
    HasFTaylorSeriesUpTo 0 f p ↔ Continuous f ∧ forall x, (p x 0).curry0 = f x := by
  simp [hasFTaylorSeriesUpToOn_univ_iff.symm, continuousOn_univ,
    hasFTaylorSeriesUpToOn_zero_iff]

/--
theorem `hasFTaylorSeriesUpTo_top_iff` / 定理 `hasFTaylorSeriesUpTo_top_iff`

English:
theorem hasFTaylorSeriesUpTo_top_iff
  given: (hN : ∞ <= N)
  proof: by
  simp only [← hasFTaylorSeriesUpToOn_univ_iff, hasFTaylorSeriesUpToOn_top_iff hN]

中文:
定理 hasFTaylorSeriesUpTo_top_iff
  条件: (hN : ∞ <= N)
  证明: by
  simp only [← hasFTaylorSeriesUpToOn_univ_iff, hasFTaylorSeriesUpToOn_top_iff hN]

Depends on / 依赖: hasFTaylorSeriesUpToOn_top_iff, hasFTaylorSeriesUpToOn_univ_iff
-/
theorem hasFTaylorSeriesUpTo_top_iff (hN : ∞ <= N) :
    HasFTaylorSeriesUpTo N f p ↔ forall n : Nat, HasFTaylorSeriesUpTo n f p := by
  simp only [← hasFTaylorSeriesUpToOn_univ_iff, hasFTaylorSeriesUpToOn_top_iff hN]

/--
theorem `hasFTaylorSeriesUpTo_top_iff'` / 定理 `hasFTaylorSeriesUpTo_top_iff'`

English:
theorem hasFTaylorSeriesUpTo_top_iff'
  given: (hN : ∞ <= N)
  proof: by
  simp only [← hasFTaylorSeriesUpToOn_univ_iff, hasFTaylorSeriesUpToOn_top_iff' hN, mem_univ,
    forall_true_left, hasFDerivWithinAt_univ]

中文:
定理 hasFTaylorSeriesUpTo_top_iff'
  条件: (hN : ∞ <= N)
  证明: by
  simp only [← hasFTaylorSeriesUpToOn_univ_iff, hasFTaylorSeriesUpToOn_top_iff' hN, mem_univ,
    forall_true_left, hasFDerivWithinAt_univ]

Depends on / 依赖: forall_true_left, hasFDerivWithinAt_univ, hasFTaylorSeriesUpToOn_top_iff, hasFTaylorSeriesUpToOn_univ_iff, mem_univ
-/
theorem hasFTaylorSeriesUpTo_top_iff' (hN : ∞ <= N) :
    HasFTaylorSeriesUpTo N f p ↔
      (forall x, (p x 0).curry0 = f x) ∧
        forall (m : Nat) (x), HasFDerivAt (fun y => p y m) (p x m.succ).curryLeft x := by
  simp only [← hasFTaylorSeriesUpToOn_univ_iff, hasFTaylorSeriesUpToOn_top_iff' hN, mem_univ,
    forall_true_left, hasFDerivWithinAt_univ]

/--
theorem `HasFTaylorSeriesUpTo.hasFDerivAt` / 定理 `HasFTaylorSeriesUpTo.hasFDerivAt`

English:
theorem HasFTaylorSeriesUpTo.hasFDerivAt
  given: (h : HasFTaylorSeriesUpTo n f p) (hn : n != 0) (x : E)
  proof: by
  rw [← hasFDerivWithinAt_univ]
  exact (hasFTaylorSeriesUpToOn_univ_iff.2 h).hasFDerivWithinAt hn (mem_univ _)

中文:
定理 HasFTaylorSeriesUpTo.hasFDerivAt
  条件: (h : HasFTaylorSeriesUpTo n f p) (hn : n != 0) (x : E)
  证明: by
  rw [← hasFDerivWithinAt_univ]
  exact (hasFTaylorSeriesUpToOn_univ_iff.2 h).hasFDerivWithinAt hn (mem_univ _)

Depends on / 依赖: hasFDerivWithinAt, hasFDerivWithinAt_univ, hasFTaylorSeriesUpToOn_univ_iff, mem_univ
-/
theorem HasFTaylorSeriesUpTo.hasFDerivAt (h : HasFTaylorSeriesUpTo n f p) (hn : n != 0) (x : E) :
    HasFDerivAt f (continuousMultilinearCurryFin1 𝕜 E F (p x 1)) x := by
  rw [← hasFDerivWithinAt_univ]
  exact (hasFTaylorSeriesUpToOn_univ_iff.2 h).hasFDerivWithinAt hn (mem_univ _)

/--
theorem `HasFTaylorSeriesUpTo.differentiable` / 定理 `HasFTaylorSeriesUpTo.differentiable`

English:
theorem HasFTaylorSeriesUpTo.differentiable
  given: (h : HasFTaylorSeriesUpTo n f p) (hn : n != 0)
  proof: fun x => (h.hasFDerivAt hn x).differentiableAt

中文:
定理 HasFTaylorSeriesUpTo.differentiable
  条件: (h : HasFTaylorSeriesUpTo n f p) (hn : n != 0)
  证明: fun x => (h.hasFDerivAt hn x).differentiableAt

Depends on / 依赖: differentiableAt, h.hasFDerivAt, hasFDerivAt
-/
theorem HasFTaylorSeriesUpTo.differentiable (h : HasFTaylorSeriesUpTo n f p) (hn : n != 0) :
    Differentiable 𝕜 f := fun x => (h.hasFDerivAt hn x).differentiableAt

/--
theorem `hasFTaylorSeriesUpTo_succ_nat_iff_right` / 定理 `hasFTaylorSeriesUpTo_succ_nat_iff_right`

English:
theorem hasFTaylorSeriesUpTo_succ_nat_iff_right
  given: {n : Nat}
  proof: by
  simp only [hasFTaylorSeriesUpToOn_succ_nat_iff_right, ← hasFTaylorSeriesUpToOn_univ_iff, mem_univ,
    forall_true_left, hasFDerivWithinAt_univ]

中文:
定理 hasFTaylorSeriesUpTo_succ_nat_iff_right
  条件: {n : 自然数}
  证明: by
  simp only [hasFTaylorSeriesUpToOn_succ_nat_iff_right, ← hasFTaylorSeriesUpToOn_univ_iff, mem_univ,
    forall_true_left, hasFDerivWithinAt_univ]

Depends on / 依赖: forall_true_left, hasFDerivWithinAt_univ, hasFTaylorSeriesUpToOn_succ_nat_iff_right, hasFTaylorSeriesUpToOn_univ_iff, mem_univ
-/
theorem hasFTaylorSeriesUpTo_succ_nat_iff_right {n : Nat} :
    HasFTaylorSeriesUpTo (n + 1 : Nat) f p ↔
      (forall x, (p x 0).curry0 = f x) ∧
        (forall x, HasFDerivAt (fun y => p y 0) (p x 1).curryLeft x) ∧
          HasFTaylorSeriesUpTo n (fun x => continuousMultilinearCurryFin1 𝕜 E F (p x 1)) fun x =>
            (p x).shift := by
  simp only [hasFTaylorSeriesUpToOn_succ_nat_iff_right, ← hasFTaylorSeriesUpToOn_univ_iff, mem_univ,
    forall_true_left, hasFDerivWithinAt_univ]

/--
lemma `HasFTaylorSeriesUpTo.tsupport_mono` / 引理 `HasFTaylorSeriesUpTo.tsupport_mono`

English:
lemma HasFTaylorSeriesUpTo.tsupport_mono
  statement: {k m : Nat} (h : k <= m) (h2 : m <= n)
  proof: by
  induction h with
  | refl => rfl
  | @step l h ih =>
    have hl : l < n := lt_of_lt_of_le (mod_cast lt_add_one l) h2
    refine subset_trans ?_ (ih hl.le)
    refine Eq.trans_subset ?_ (tsupport_fderiv_subset 𝕜)
    rw [funext <| hf.fderiv_eq (mod_cast hl)]
.symm refine tsupport_comp_eq (g := 

中文:
引理 HasFTaylorSeriesUpTo.tsupport_mono
  结论: {k m : 自然数} (h : k <= m) (h2 : m <= n)
  证明: by
  induction h with
  | refl => rfl
  | @step l h ih =>
    have hl : l < n := lt_of_lt_of_le (mod_cast lt_add_one l) h2
    refine subset_trans ?_ (ih hl.le)
    refine Eq.trans_subset ?_ (tsupport_fderiv_subset 𝕜)
    rw [funext <| hf.fderiv_eq (mod_cast hl)]
.symm refine tsupport_comp_eq (g := 

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.curryLeft, Eq.trans_subset, continuousMultilinearCurryLeftEquiv, curryLeft, fderiv_eq, hf.fderiv_eq, hl.le, lt_add_one, lt_of_lt_of_le, map_eq_zero_iff, mod_cast, subset_trans, trans_subset, tsupport_comp_eq, tsupport_fderiv_subset
-/
lemma HasFTaylorSeriesUpTo.tsupport_mono {k m : Nat} (h : k <= m) (h2 : m <= n)
    (hf : HasFTaylorSeriesUpTo n f p) :
    tsupport (p · m) subseteq tsupport (p · k) := by
  induction h with
  | refl => rfl
  | @step l h ih =>
    have hl : l < n := lt_of_lt_of_le (mod_cast lt_add_one l) h2
    refine subset_trans ?_ (ih hl.le)
    refine Eq.trans_subset ?_ (tsupport_fderiv_subset 𝕜)
    rw [funext <| hf.fderiv_eq (mod_cast hl)]
.symm refine tsupport_comp_eq (g := ContinuousMultilinearMap.curryLeft) (fun {x} => ?_) _
    exact (continuousMultilinearCurryLeftEquiv _ _ _).map_eq_zero_iff (x := x)

/--
lemma `HasFTaylorSeriesUpTo.tsupport_subset` / 引理 `HasFTaylorSeriesUpTo.tsupport_subset`

English:
lemma HasFTaylorSeriesUpTo.tsupport_subset
  statement: {m : Nat} (h : m <= n)
  proof: by
  refine (hf.tsupport_mono zero_le h).trans_eq ?_
  rw [← funext hf.zero_eq]
.symm refine tsupport_comp_eq (g := ContinuousMultilinearMap.curry0) (fun {x} => ?_) _
  exact (continuousMultilinearCurryFin0 _ _ _).map_eq_zero_iff (x := x)

中文:
引理 HasFTaylorSeriesUpTo.tsupport_subset
  结论: {m : 自然数} (h : m <= n)
  证明: by
  refine (hf.tsupport_mono zero_le h).trans_eq ?_
  rw [← funext hf.zero_eq]
.symm refine tsupport_comp_eq (g := ContinuousMultilinearMap.curry0) (fun {x} => ?_) _
  exact (continuousMultilinearCurryFin0 _ _ _).map_eq_zero_iff (x := x)

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.curry0, continuousMultilinearCurryFin0, curry0, hf.tsupport_mono, hf.zero_eq, map_eq_zero_iff, trans_eq, tsupport_comp_eq, tsupport_mono, zero_eq, zero_le
-/
lemma HasFTaylorSeriesUpTo.tsupport_subset {m : Nat} (h : m <= n)
    (hf : HasFTaylorSeriesUpTo n f p) :
    tsupport (p · m) subseteq tsupport f := by
  refine (hf.tsupport_mono zero_le h).trans_eq ?_
  rw [← funext hf.zero_eq]
.symm refine tsupport_comp_eq (g := ContinuousMultilinearMap.curry0) (fun {x} => ?_) _
  exact (continuousMultilinearCurryFin0 _ _ _).map_eq_zero_iff (x := x)

/-! ### Iterated derivative -/


variable (𝕜)

/--
Definition of `iteratedFDeriv` / `iteratedFDeriv` 的定义

English:
definition iteratedFDeriv
  signature: (n : Nat) (f : E -> F)
  body: Nat.recOn n (fun x => ContinuousMultilinearMap.uncurry0 𝕜 E (f x)) fun _ rec x =>
    ContinuousLinearMap.uncurryLeft (fderiv 𝕜 rec x)

中文:
定义 iteratedFDeriv
  签名: (n : 自然数) (f : E -> F)
  定义体: Nat.recOn n (fun x => ContinuousMultilinearMap.uncurry0 𝕜 E (f x)) fun _ rec x =>
    ContinuousLinearMap.uncurryLeft (fderiv 𝕜 rec x)

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.uncurryLeft, ContinuousMultilinearMap, ContinuousMultilinearMap.uncurry0, Nat.recOn, fderiv, uncurry0, uncurryLeft
-/
noncomputable def iteratedFDeriv (n : Nat) (f : E -> F) : E -> E [×n]->L[𝕜] F :=
  Nat.recOn n (fun x => ContinuousMultilinearMap.uncurry0 𝕜 E (f x)) fun _ rec x =>
    ContinuousLinearMap.uncurryLeft (fderiv 𝕜 rec x)

/--
Definition of `ftaylorSeries` / `ftaylorSeries` 的定义

English:
definition ftaylorSeries
  signature: (f : E -> F) (x : E)
  body: fun n =>
  iteratedFDeriv 𝕜 n f x

中文:
定义 ftaylorSeries
  签名: (f : E -> F) (x : E)
  定义体: fun n =>
  iteratedFDeriv 𝕜 n f x
-/
def ftaylorSeries (f : E -> F) (x : E) : FormalMultilinearSeries 𝕜 E F := fun n =>
  iteratedFDeriv 𝕜 n f x

variable {𝕜}

@[simp]
/--
theorem `iteratedFDeriv_zero_apply` / 定理 `iteratedFDeriv_zero_apply`

English:
theorem iteratedFDeriv_zero_apply
  given: (m : Fin 0 -> E)
  proof: rfl

中文:
定理 iteratedFDeriv_zero_apply
  条件: (m : Fin 0 -> E)
  证明: rfl
-/
theorem iteratedFDeriv_zero_apply (m : Fin 0 -> E) :
    (iteratedFDeriv 𝕜 0 f x : (Fin 0 -> E) -> F) m = f x :=
  rfl

/--
theorem `iteratedFDeriv_zero_eq_comp` / 定理 `iteratedFDeriv_zero_eq_comp`

English:
theorem iteratedFDeriv_zero_eq_comp
  proof: rfl

@[simp]

中文:
定理 iteratedFDeriv_zero_eq_comp
  证明: rfl

@[simp]
-/
theorem iteratedFDeriv_zero_eq_comp :
    iteratedFDeriv 𝕜 0 f = (continuousMultilinearCurryFin0 𝕜 E F).symm ∘ f :=
  rfl

@[simp]
/--
theorem `norm_iteratedFDeriv_zero` / 定理 `norm_iteratedFDeriv_zero`

English:
theorem norm_iteratedFDeriv_zero
  statement: ‖iteratedFDeriv 𝕜 0 f x‖ = ‖f x‖
  proof: by
  rw [iteratedFDeriv_zero_eq_comp]; rw [comp_apply]; rw [LinearIsometryEquiv.norm_map]

中文:
定理 norm_iteratedFDeriv_zero
  结论: ‖iteratedFDeriv 𝕜 0 f x‖ = ‖f x‖
  证明: by
  rw [iteratedFDeriv_zero_eq_comp]; rw [comp_apply]; rw [LinearIsometryEquiv.norm_map]

Depends on / 依赖: LinearIsometryEquiv, LinearIsometryEquiv.norm_map, comp_apply, iteratedFDeriv_zero_eq_comp, norm_map
-/
theorem norm_iteratedFDeriv_zero : ‖iteratedFDeriv 𝕜 0 f x‖ = ‖f x‖ := by
  rw [iteratedFDeriv_zero_eq_comp]; rw [comp_apply]; rw [LinearIsometryEquiv.norm_map]

/--
theorem `iteratedFDerivWithin_zero_eq` / 定理 `iteratedFDerivWithin_zero_eq`

English:
theorem iteratedFDerivWithin_zero_eq
  statement: iteratedFDerivWithin 𝕜 0 f s = iteratedFDeriv 𝕜 0 f
  proof: rfl

中文:
定理 iteratedFDerivWithin_zero_eq
  结论: iteratedFDerivWithin 𝕜 0 f s = iteratedFDeriv 𝕜 0 f
  证明: rfl
-/
theorem iteratedFDerivWithin_zero_eq : iteratedFDerivWithin 𝕜 0 f s = iteratedFDeriv 𝕜 0 f := rfl

/--
theorem `iteratedFDeriv_succ_apply_left` / 定理 `iteratedFDeriv_succ_apply_left`

English:
theorem iteratedFDeriv_succ_apply_left
  given: {n : Nat} (m : Fin (n + 1) -> E)
  proof: rfl

中文:
定理 iteratedFDeriv_succ_apply_left
  条件: {n : 自然数} (m : Fin (n + 1) -> E)
  证明: rfl
-/
theorem iteratedFDeriv_succ_apply_left {n : Nat} (m : Fin (n + 1) -> E) :
    (iteratedFDeriv 𝕜 (n + 1) f x : (Fin (n + 1) -> E) -> F) m =
      (fderiv 𝕜 (iteratedFDeriv 𝕜 n f) x : E -> E [×n]->L[𝕜] F) (m 0) (tail m) :=
  rfl

/--
theorem `DifferentiableAt.iteratedFDeriv_succ_apply_left'` / 定理 `DifferentiableAt.iteratedFDeriv_succ_apply_left'`

English:
theorem DifferentiableAt.iteratedFDeriv_succ_apply_left'
  statement: {n : Nat} {m : Fin (n + 1) -> E}
  proof: by
  convert iteratedFDeriv_succ_apply_left m
  simp [fderiv_continuousMultilinear_apply_const hf]

中文:
定理 DifferentiableAt.iteratedFDeriv_succ_apply_left'
  结论: {n : 自然数} {m : Fin (n + 1) -> E}
  证明: by
  convert iteratedFDeriv_succ_apply_left m
  simp [fderiv_continuousMultilinear_apply_const hf]

Depends on / 依赖: convert, fderiv_continuousMultilinear_apply_const, iteratedFDeriv_succ_apply_left
-/
theorem DifferentiableAt.iteratedFDeriv_succ_apply_left' {n : Nat} {m : Fin (n + 1) -> E}
    (hf : DifferentiableAt 𝕜 (iteratedFDeriv 𝕜 n f) x) :
    iteratedFDeriv 𝕜 (n + 1) f x m =
    fderiv 𝕜 (fun y => iteratedFDeriv 𝕜 n f y (Fin.tail m)) x (m 0) := by
  convert iteratedFDeriv_succ_apply_left m
  simp [fderiv_continuousMultilinear_apply_const hf]

/--
theorem `iteratedFDeriv_succ_eq_comp_left` / 定理 `iteratedFDeriv_succ_eq_comp_left`

English:
theorem iteratedFDeriv_succ_eq_comp_left
  given: {n : Nat}
  proof: rfl

中文:
定理 iteratedFDeriv_succ_eq_comp_left
  条件: {n : 自然数}
  证明: rfl
-/
theorem iteratedFDeriv_succ_eq_comp_left {n : Nat} :
    iteratedFDeriv 𝕜 (n + 1) f =
      (continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) => E) F).symm ∘
        fderiv 𝕜 (iteratedFDeriv 𝕜 n f) :=
  rfl

/--
theorem `fderiv_iteratedFDeriv` / 定理 `fderiv_iteratedFDeriv`

English:
theorem fderiv_iteratedFDeriv
  given: {n : Nat}
  proof: rfl

中文:
定理 fderiv_iteratedFDeriv
  条件: {n : 自然数}
  证明: rfl
-/
theorem fderiv_iteratedFDeriv {n : Nat} :
    fderiv 𝕜 (iteratedFDeriv 𝕜 n f) =
      continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (n + 1) => E) F ∘
        iteratedFDeriv 𝕜 (n + 1) f :=
  rfl

/--
theorem `tsupport_iteratedFDeriv_subset` / 定理 `tsupport_iteratedFDeriv_subset`

English:
theorem tsupport_iteratedFDeriv_subset
  given: (n : Nat)
  statement: tsupport (iteratedFDeriv 𝕜 n f) subseteq tsupport f
  proof: by
  induction n with
  | zero =>
    rw [iteratedFDeriv_zero_eq_comp]
    exact closure_minimal ((support_comp_subset (map_zero _) _).trans subset_closure)
      isClosed_closure
  | succ n IH =>
    rw [iteratedFDeriv_succ_eq_comp_left]
    exact closure_minimal ((support_comp_subset (map_zero _) 

中文:
定理 tsupport_iteratedFDeriv_subset
  条件: (n : 自然数)
  结论: tsupport (iteratedFDeriv 𝕜 n f) subseteq tsupport f
  证明: by
  induction n with
  | zero =>
    rw [iteratedFDeriv_zero_eq_comp]
    exact closure_minimal ((support_comp_subset (map_zero _) _).trans subset_closure)
      isClosed_closure
  | succ n IH =>
    rw [iteratedFDeriv_succ_eq_comp_left]
    exact closure_minimal ((support_comp_subset (map_zero _) 

Depends on / 依赖: closure_minimal, isClosed_closure, iteratedFDeriv_succ_eq_comp_left, iteratedFDeriv_zero_eq_comp, map_zero, subset_closure, support_comp_subset, support_fderiv_subset
-/
theorem tsupport_iteratedFDeriv_subset (n : Nat) : tsupport (iteratedFDeriv 𝕜 n f) subseteq tsupport f := by
  induction n with
  | zero =>
    rw [iteratedFDeriv_zero_eq_comp]
    exact closure_minimal ((support_comp_subset (map_zero _) _).trans subset_closure)
      isClosed_closure
  | succ n IH =>
    rw [iteratedFDeriv_succ_eq_comp_left]
    exact closure_minimal ((support_comp_subset (map_zero _) _).trans
      ((support_fderiv_subset 𝕜).trans IH)) isClosed_closure

/--
theorem `support_iteratedFDeriv_subset` / 定理 `support_iteratedFDeriv_subset`

English:
theorem support_iteratedFDeriv_subset
  given: (n : Nat)
  statement: support (iteratedFDeriv 𝕜 n f) subseteq tsupport f
  proof: subset_closure.trans (tsupport_iteratedFDeriv_subset n)

中文:
定理 support_iteratedFDeriv_subset
  条件: (n : 自然数)
  结论: support (iteratedFDeriv 𝕜 n f) subseteq tsupport f
  证明: subset_closure.trans (tsupport_iteratedFDeriv_subset n)

Depends on / 依赖: subset_closure, subset_closure.trans, tsupport_iteratedFDeriv_subset
-/
theorem support_iteratedFDeriv_subset (n : Nat) : support (iteratedFDeriv 𝕜 n f) subseteq tsupport f :=
  subset_closure.trans (tsupport_iteratedFDeriv_subset n)

/--
theorem `HasCompactSupport.iteratedFDeriv` / 定理 `HasCompactSupport.iteratedFDeriv`

English:
theorem HasCompactSupport.iteratedFDeriv
  given: (hf : HasCompactSupport f) (n : Nat)
  proof: hf.of_isClosed_subset isClosed_closure (tsupport_iteratedFDeriv_subset n)

中文:
定理 HasCompactSupport.iteratedFDeriv
  条件: (hf : HasCompactSupport f) (n : 自然数)
  证明: hf.of_isClosed_subset isClosed_closure (tsupport_iteratedFDeriv_subset n)

Depends on / 依赖: hf.of_isClosed_subset, isClosed_closure, of_isClosed_subset, tsupport_iteratedFDeriv_subset
-/
theorem HasCompactSupport.iteratedFDeriv (hf : HasCompactSupport f) (n : Nat) :
    HasCompactSupport (iteratedFDeriv 𝕜 n f) :=
  hf.of_isClosed_subset isClosed_closure (tsupport_iteratedFDeriv_subset n)

/--
theorem `norm_fderiv_iteratedFDeriv` / 定理 `norm_fderiv_iteratedFDeriv`

English:
theorem norm_fderiv_iteratedFDeriv
  given: {n : Nat}
  proof: by
  rw [iteratedFDeriv_succ_eq_comp_left]; rw [comp_apply]; rw [LinearIsometryEquiv.norm_map]

中文:
定理 norm_fderiv_iteratedFDeriv
  条件: {n : 自然数}
  证明: by
  rw [iteratedFDeriv_succ_eq_comp_left]; rw [comp_apply]; rw [LinearIsometryEquiv.norm_map]

Depends on / 依赖: LinearIsometryEquiv, LinearIsometryEquiv.norm_map, comp_apply, iteratedFDeriv_succ_eq_comp_left, norm_map
-/
theorem norm_fderiv_iteratedFDeriv {n : Nat} :
    ‖fderiv 𝕜 (iteratedFDeriv 𝕜 n f) x‖ = ‖iteratedFDeriv 𝕜 (n + 1) f x‖ := by
  rw [iteratedFDeriv_succ_eq_comp_left]; rw [comp_apply]; rw [LinearIsometryEquiv.norm_map]

/--
theorem `iteratedFDerivWithin_univ` / 定理 `iteratedFDerivWithin_univ`

English:
theorem iteratedFDerivWithin_univ
  given: {n : Nat}
  proof: by
  simp [iteratedFDerivWithin, iteratedFDeriv]

中文:
定理 iteratedFDerivWithin_univ
  条件: {n : 自然数}
  证明: by
  simp [iteratedFDerivWithin, iteratedFDeriv]

Depends on / 依赖: iteratedFDeriv, iteratedFDerivWithin
-/
theorem iteratedFDerivWithin_univ {n : Nat} :
    iteratedFDerivWithin 𝕜 n f univ = iteratedFDeriv 𝕜 n f := by
  simp [iteratedFDerivWithin, iteratedFDeriv]

variable (𝕜) in
/--
theorem `Filter.EventuallyEq.iteratedFDeriv` / 定理 `Filter.EventuallyEq.iteratedFDeriv`

English:
theorem Filter.EventuallyEq.iteratedFDeriv
  proof: by
  simp_all [← nhdsWithin_univ, ← iteratedFDerivWithin_univ, EventuallyEq.iteratedFDerivWithin]

中文:
定理 Filter.EventuallyEq.iteratedFDeriv
  证明: by
  simp_all [← nhdsWithin_univ, ← iteratedFDerivWithin_univ, EventuallyEq.iteratedFDerivWithin]
-/
protected theorem Filter.EventuallyEq.iteratedFDeriv
    {f₁ f₂ : E -> F} {x : E} (h : f₁ =ᶠ[𝓝 x] f₂) (n : Nat) :
    iteratedFDeriv 𝕜 n f₁ =ᶠ[𝓝 x] iteratedFDeriv 𝕜 n f₂ := by
  simp_all [← nhdsWithin_univ, ← iteratedFDerivWithin_univ, EventuallyEq.iteratedFDerivWithin]

variable (𝕜) in
/--
theorem `Filter.EventuallyEq.ftaylorSeries` / 定理 `Filter.EventuallyEq.ftaylorSeries`

English:
theorem Filter.EventuallyEq.ftaylorSeries
  given: (h : f₁ =ᶠ[𝓝 x] f)
  proof: by
  filter_upwards [eventually_eventuallyEq_nhds.2 h] with e₁ he₁
  ext n : 1
  exact (he₁.iteratedFDeriv 𝕜 n).eq_of_nhds

中文:
定理 Filter.EventuallyEq.ftaylorSeries
  条件: (h : f₁ =ᶠ[𝓝 x] f)
  证明: by
  filter_upwards [eventually_eventuallyEq_nhds.2 h] with e₁ he₁
  ext n : 1
  exact (he₁.iteratedFDeriv 𝕜 n).eq_of_nhds
-/
protected theorem Filter.EventuallyEq.ftaylorSeries (h : f₁ =ᶠ[𝓝 x] f) :
    ftaylorSeries 𝕜 f₁ =ᶠ[𝓝 x] ftaylorSeries 𝕜 f := by
  filter_upwards [eventually_eventuallyEq_nhds.2 h] with e₁ he₁
  ext n : 1
  exact (he₁.iteratedFDeriv 𝕜 n).eq_of_nhds

/--
theorem `HasFTaylorSeriesUpTo.eq_iteratedFDeriv` / 定理 `HasFTaylorSeriesUpTo.eq_iteratedFDeriv`

English:
theorem HasFTaylorSeriesUpTo.eq_iteratedFDeriv
  proof: by
  rw [← iteratedFDerivWithin_univ]
  rw [← hasFTaylorSeriesUpToOn_univ_iff] at h
  exact h.eq_iteratedFDerivWithin_of_uniqueDiffOn hmn uniqueDiffOn_univ (mem_univ _)

中文:
定理 HasFTaylorSeriesUpTo.eq_iteratedFDeriv
  证明: by
  rw [← iteratedFDerivWithin_univ]
  rw [← hasFTaylorSeriesUpToOn_univ_iff] at h
  exact h.eq_iteratedFDerivWithin_of_uniqueDiffOn hmn uniqueDiffOn_univ (mem_univ _)

Depends on / 依赖: eq_iteratedFDerivWithin_of_uniqueDiffOn, h.eq_iteratedFDerivWithin_of_uniqueDiffOn, hasFTaylorSeriesUpToOn_univ_iff, iteratedFDerivWithin_univ, mem_univ, uniqueDiffOn_univ
-/
theorem HasFTaylorSeriesUpTo.eq_iteratedFDeriv
    (h : HasFTaylorSeriesUpTo n f p) {m : Nat} (hmn : m <= n) (x : E) :
    p x m = iteratedFDeriv 𝕜 m f x := by
  rw [← iteratedFDerivWithin_univ]
  rw [← hasFTaylorSeriesUpToOn_univ_iff] at h
  exact h.eq_iteratedFDerivWithin_of_uniqueDiffOn hmn uniqueDiffOn_univ (mem_univ _)

/--
theorem `iteratedFDerivWithin_of_isOpen` / 定理 `iteratedFDerivWithin_of_isOpen`

English:
theorem iteratedFDerivWithin_of_isOpen
  given: (n : Nat) (hs : IsOpen s)
  proof: by
  intro x hx
  rw [← iteratedFDerivWithin_univ]
  exact iteratedFDerivWithin_congr_set (Filter.eventuallyEq_univ.mpr <| hs.mem_nhds hx) n

中文:
定理 iteratedFDerivWithin_of_isOpen
  条件: (n : 自然数) (hs : IsOpen s)
  证明: by
  intro x hx
  rw [← iteratedFDerivWithin_univ]
  exact iteratedFDerivWithin_congr_set (Filter.eventuallyEq_univ.mpr <| hs.mem_nhds hx) n

Depends on / 依赖: Filter, Filter.eventuallyEq_univ.mpr, eventuallyEq_univ, hs.mem_nhds, iteratedFDerivWithin_congr_set, iteratedFDerivWithin_univ, mem_nhds
-/
theorem iteratedFDerivWithin_of_isOpen (n : Nat) (hs : IsOpen s) :
    EqOn (iteratedFDerivWithin 𝕜 n f s) (iteratedFDeriv 𝕜 n f) s := by
  intro x hx
  rw [← iteratedFDerivWithin_univ]
  exact iteratedFDerivWithin_congr_set (Filter.eventuallyEq_univ.mpr <| hs.mem_nhds hx) n

/--
theorem `ftaylorSeriesWithin_univ` / 定理 `ftaylorSeriesWithin_univ`

English:
theorem ftaylorSeriesWithin_univ
  statement: ftaylorSeriesWithin 𝕜 f univ = ftaylorSeries 𝕜 f
  proof: by
  ext1 x; ext1 n
  change iteratedFDerivWithin 𝕜 n f univ x = iteratedFDeriv 𝕜 n f x
  rw [iteratedFDerivWithin_univ]

中文:
定理 ftaylorSeriesWithin_univ
  结论: ftaylorSeriesWithin 𝕜 f univ = ftaylorSeries 𝕜 f
  证明: by
  ext1 x; ext1 n
  change iteratedFDerivWithin 𝕜 n f univ x = iteratedFDeriv 𝕜 n f x
  rw [iteratedFDerivWithin_univ]

Depends on / 依赖: iteratedFDeriv, iteratedFDerivWithin, iteratedFDerivWithin_univ
-/
theorem ftaylorSeriesWithin_univ : ftaylorSeriesWithin 𝕜 f univ = ftaylorSeries 𝕜 f := by
  ext1 x; ext1 n
  change iteratedFDerivWithin 𝕜 n f univ x = iteratedFDeriv 𝕜 n f x
  rw [iteratedFDerivWithin_univ]

/--
theorem `iteratedFDeriv_succ_apply_right` / 定理 `iteratedFDeriv_succ_apply_right`

English:
theorem iteratedFDeriv_succ_apply_right
  given: {n : Nat} (m : Fin (n + 1) -> E)
  proof: by
  rw [← iteratedFDerivWithin_univ]; rw [← iteratedFDerivWithin_univ]; rw [← fderivWithin_univ]
  exact iteratedFDerivWithin_succ_apply_right uniqueDiffOn_univ (mem_univ _) _

中文:
定理 iteratedFDeriv_succ_apply_right
  条件: {n : 自然数} (m : Fin (n + 1) -> E)
  证明: by
  rw [← iteratedFDerivWithin_univ]; rw [← iteratedFDerivWithin_univ]; rw [← fderivWithin_univ]
  exact iteratedFDerivWithin_succ_apply_right uniqueDiffOn_univ (mem_univ _) _

Depends on / 依赖: fderivWithin_univ, iteratedFDerivWithin_succ_apply_right, iteratedFDerivWithin_univ, mem_univ, uniqueDiffOn_univ
-/
theorem iteratedFDeriv_succ_apply_right {n : Nat} (m : Fin (n + 1) -> E) :
    (iteratedFDeriv 𝕜 (n + 1) f x : (Fin (n + 1) -> E) -> F) m =
      iteratedFDeriv 𝕜 n (fun y => fderiv 𝕜 f y) x (init m) (m (last n)) := by
  rw [← iteratedFDerivWithin_univ]; rw [← iteratedFDerivWithin_univ]; rw [← fderivWithin_univ]
  exact iteratedFDerivWithin_succ_apply_right uniqueDiffOn_univ (mem_univ _) _

/--
theorem `iteratedFDeriv_succ_eq_comp_right` / 定理 `iteratedFDeriv_succ_eq_comp_right`

English:
theorem iteratedFDeriv_succ_eq_comp_right
  given: {n : Nat}
  proof: by
  ext m
  rw [iteratedFDeriv_succ_apply_right]; rw [comp_apply]; rw [continuousMultilinearCurryRightEquiv_symm_apply']

中文:
定理 iteratedFDeriv_succ_eq_comp_right
  条件: {n : 自然数}
  证明: by
  ext m
  rw [iteratedFDeriv_succ_apply_right]; rw [comp_apply]; rw [continuousMultilinearCurryRightEquiv_symm_apply']

Depends on / 依赖: comp_apply, continuousMultilinearCurryRightEquiv_symm_apply, iteratedFDeriv_succ_apply_right
-/
theorem iteratedFDeriv_succ_eq_comp_right {n : Nat} :
    iteratedFDeriv 𝕜 (n + 1) f x =
      ((continuousMultilinearCurryRightEquiv' 𝕜 n E F).symm ∘
          iteratedFDeriv 𝕜 n fun y => fderiv 𝕜 f y) x := by
  ext m
  rw [iteratedFDeriv_succ_apply_right]; rw [comp_apply]; rw [continuousMultilinearCurryRightEquiv_symm_apply']

/--
theorem `norm_iteratedFDeriv_fderiv` / 定理 `norm_iteratedFDeriv_fderiv`

English:
theorem norm_iteratedFDeriv_fderiv
  given: {n : Nat}
  proof: by
  rw [iteratedFDeriv_succ_eq_comp_right]; rw [comp_apply]; rw [LinearIsometryEquiv.norm_map]

@[simp]

中文:
定理 norm_iteratedFDeriv_fderiv
  条件: {n : 自然数}
  证明: by
  rw [iteratedFDeriv_succ_eq_comp_right]; rw [comp_apply]; rw [LinearIsometryEquiv.norm_map]

@[simp]

Depends on / 依赖: LinearIsometryEquiv, LinearIsometryEquiv.norm_map, comp_apply, iteratedFDeriv_succ_eq_comp_right, norm_map
-/
theorem norm_iteratedFDeriv_fderiv {n : Nat} :
    ‖iteratedFDeriv 𝕜 n (fderiv 𝕜 f) x‖ = ‖iteratedFDeriv 𝕜 (n + 1) f x‖ := by
  rw [iteratedFDeriv_succ_eq_comp_right]; rw [comp_apply]; rw [LinearIsometryEquiv.norm_map]

@[simp]
/--
theorem `iteratedFDeriv_one_apply` / 定理 `iteratedFDeriv_one_apply`

English:
theorem iteratedFDeriv_one_apply
  given: (m : Fin 1 -> E)
  proof: by
  rw [iteratedFDeriv_succ_apply_right]; rw [iteratedFDeriv_zero_apply]; rw [last_zero]

@[simp]

中文:
定理 iteratedFDeriv_one_apply
  条件: (m : Fin 1 -> E)
  证明: by
  rw [iteratedFDeriv_succ_apply_right]; rw [iteratedFDeriv_zero_apply]; rw [last_zero]

@[simp]

Depends on / 依赖: iteratedFDeriv_succ_apply_right, iteratedFDeriv_zero_apply, last_zero
-/
theorem iteratedFDeriv_one_apply (m : Fin 1 -> E) :
    iteratedFDeriv 𝕜 1 f x m = fderiv 𝕜 f x (m 0) := by
  rw [iteratedFDeriv_succ_apply_right]; rw [iteratedFDeriv_zero_apply]; rw [last_zero]

@[simp]
/--
theorem `norm_iteratedFDeriv_one` / 定理 `norm_iteratedFDeriv_one`

English:
theorem norm_iteratedFDeriv_one
  given: (f : E -> F)
  proof: by
  rw [← iteratedFDerivWithin_univ]; rw [← fderivWithin_univ]
  exact norm_iteratedFDerivWithin_one f uniqueDiffWithinAt_univ

中文:
定理 norm_iteratedFDeriv_one
  条件: (f : E -> F)
  证明: by
  rw [← iteratedFDerivWithin_univ]; rw [← fderivWithin_univ]
  exact norm_iteratedFDerivWithin_one f uniqueDiffWithinAt_univ

Depends on / 依赖: fderivWithin_univ, iteratedFDerivWithin_univ, norm_iteratedFDerivWithin_one, uniqueDiffWithinAt_univ
-/
theorem norm_iteratedFDeriv_one (f : E -> F) :
    ‖iteratedFDeriv 𝕜 1 f x‖ = ‖fderiv 𝕜 f x‖ := by
  rw [← iteratedFDerivWithin_univ]; rw [← fderivWithin_univ]
  exact norm_iteratedFDerivWithin_one f uniqueDiffWithinAt_univ

/--
lemma `iteratedFDeriv_two_apply` / 引理 `iteratedFDeriv_two_apply`

English:
lemma iteratedFDeriv_two_apply
  given: (f : E -> F) (z : E) (m : Fin 2 -> E)
  proof: by
  simp [iteratedFDeriv_succ_apply_right, init]

中文:
引理 iteratedFDeriv_two_apply
  条件: (f : E -> F) (z : E) (m : Fin 2 -> E)
  证明: by
  simp [iteratedFDeriv_succ_apply_right, init]

Depends on / 依赖: iteratedFDeriv_succ_apply_right
-/
lemma iteratedFDeriv_two_apply (f : E -> F) (z : E) (m : Fin 2 -> E) :
    iteratedFDeriv 𝕜 2 f z m = fderiv 𝕜 (fderiv 𝕜 f) z (m 0) (m 1) := by
  simp [iteratedFDeriv_succ_apply_right, init]

/--
lemma `iteratedFDeriv_comp_add_left'` / 引理 `iteratedFDeriv_comp_add_left'`

English:
lemma iteratedFDeriv_comp_add_left'
  given: (n : Nat) (a : E)
  proof: by
  simpa [← iteratedFDerivWithin_univ] using iteratedFDerivWithin_comp_add_left' n a (s := univ)

中文:
引理 iteratedFDeriv_comp_add_left'
  条件: (n : 自然数) (a : E)
  证明: by
  simpa [← iteratedFDerivWithin_univ] using iteratedFDerivWithin_comp_add_left' n a (s := univ)

Depends on / 依赖: iteratedFDerivWithin_comp_add_left, iteratedFDerivWithin_univ
-/
lemma iteratedFDeriv_comp_add_left' (n : Nat) (a : E) :
    iteratedFDeriv 𝕜 n (fun z => f (a + z)) = fun x => iteratedFDeriv 𝕜 n f (a + x) := by
  simpa [← iteratedFDerivWithin_univ] using iteratedFDerivWithin_comp_add_left' n a (s := univ)

/--
lemma `iteratedFDeriv_comp_add_left` / 引理 `iteratedFDeriv_comp_add_left`

English:
lemma iteratedFDeriv_comp_add_left
  given: (n : Nat) (a : E) (x : E)
  proof: by
  simp [iteratedFDeriv_comp_add_left']

中文:
引理 iteratedFDeriv_comp_add_left
  条件: (n : 自然数) (a : E) (x : E)
  证明: by
  simp [iteratedFDeriv_comp_add_left']

Depends on / 依赖: iteratedFDeriv_comp_add_left
-/
lemma iteratedFDeriv_comp_add_left (n : Nat) (a : E) (x : E) :
    iteratedFDeriv 𝕜 n (fun z => f (a + z)) x = iteratedFDeriv 𝕜 n f (a + x) := by
  simp [iteratedFDeriv_comp_add_left']

/--
lemma `iteratedFDeriv_comp_add_right'` / 引理 `iteratedFDeriv_comp_add_right'`

English:
lemma iteratedFDeriv_comp_add_right'
  given: (n : Nat) (a : E)
  proof: by
  simpa [add_comm a] using iteratedFDeriv_comp_add_left' n a

中文:
引理 iteratedFDeriv_comp_add_right'
  条件: (n : 自然数) (a : E)
  证明: by
  simpa [add_comm a] using iteratedFDeriv_comp_add_left' n a

Depends on / 依赖: add_comm, iteratedFDeriv_comp_add_left
-/
lemma iteratedFDeriv_comp_add_right' (n : Nat) (a : E) :
    iteratedFDeriv 𝕜 n (fun z => f (z + a)) = fun x => iteratedFDeriv 𝕜 n f (x + a) := by
  simpa [add_comm a] using iteratedFDeriv_comp_add_left' n a

/--
lemma `iteratedFDeriv_comp_add_right` / 引理 `iteratedFDeriv_comp_add_right`

English:
lemma iteratedFDeriv_comp_add_right
  given: (n : Nat) (a : E) (x : E)
  proof: by
  simp [iteratedFDeriv_comp_add_right']

中文:
引理 iteratedFDeriv_comp_add_right
  条件: (n : 自然数) (a : E) (x : E)
  证明: by
  simp [iteratedFDeriv_comp_add_right']

Depends on / 依赖: iteratedFDeriv_comp_add_right
-/
lemma iteratedFDeriv_comp_add_right (n : Nat) (a : E) (x : E) :
    iteratedFDeriv 𝕜 n (fun z => f (z + a)) x = iteratedFDeriv 𝕜 n f (x + a) := by
  simp [iteratedFDeriv_comp_add_right']

/--
lemma `iteratedFDeriv_comp_sub'` / 引理 `iteratedFDeriv_comp_sub'`

English:
lemma iteratedFDeriv_comp_sub'
  given: (n : Nat) (a : E)
  proof: by
  simpa [sub_eq_add_neg] using iteratedFDeriv_comp_add_right' n (-a)

中文:
引理 iteratedFDeriv_comp_sub'
  条件: (n : 自然数) (a : E)
  证明: by
  simpa [sub_eq_add_neg] using iteratedFDeriv_comp_add_right' n (-a)

Depends on / 依赖: iteratedFDeriv_comp_add_right, sub_eq_add_neg
-/
lemma iteratedFDeriv_comp_sub' (n : Nat) (a : E) :
    iteratedFDeriv 𝕜 n (fun z => f (z - a)) = fun x => iteratedFDeriv 𝕜 n f (x - a) := by
  simpa [sub_eq_add_neg] using iteratedFDeriv_comp_add_right' n (-a)

/--
lemma `iteratedFDeriv_comp_sub` / 引理 `iteratedFDeriv_comp_sub`

English:
lemma iteratedFDeriv_comp_sub
  given: (n : Nat) (a : E) (x : E)
  proof: by
  simp [iteratedFDeriv_comp_sub']

中文:
引理 iteratedFDeriv_comp_sub
  条件: (n : 自然数) (a : E) (x : E)
  证明: by
  simp [iteratedFDeriv_comp_sub']

Depends on / 依赖: iteratedFDeriv_comp_sub
-/
lemma iteratedFDeriv_comp_sub (n : Nat) (a : E) (x : E) :
    iteratedFDeriv 𝕜 n (fun z => f (z - a)) x = iteratedFDeriv 𝕜 n f (x - a) := by
  simp [iteratedFDeriv_comp_sub']

/--
lemma `iteratedFDerivWithin_comp_neg` / 引理 `iteratedFDerivWithin_comp_neg`

English:
lemma iteratedFDerivWithin_comp_neg
  given: {f : 𝕜 -> F} {s : Set 𝕜} (n : Nat) (a : 𝕜)
  proof: by
  induction n generalizing a with
  | zero => simp [iteratedFDerivWithin]
  | succ n ih =>
    have ih' : iteratedFDerivWithin 𝕜 n (fun x => f (-x)) s
        = fun a => (-1 : 𝕜) ^ n • iteratedFDerivWithin 𝕜 n f (-s) (-a) := by
      ext b
      rw [ih b]
    set g := fun a => iteratedFDerivWithi

中文:
引理 iteratedFDerivWithin_comp_neg
  条件: {f : 𝕜 -> F} {s : Set 𝕜} (n : 自然数) (a : 𝕜)
  证明: by
  induction n generalizing a with
  | zero => simp [iteratedFDerivWithin]
  | succ n ih =>
    have ih' : iteratedFDerivWithin 𝕜 n (fun x => f (-x)) s
        = fun a => (-1 : 𝕜) ^ n • iteratedFDerivWithin 𝕜 n f (-s) (-a) := by
      ext b
      rw [ih b]
    set g := fun a => iteratedFDerivWithi

Depends on / 依赖: Function, Function.comp_apply, Pi.smul_def, comp_apply, fderivWithin_const_smul_field, generalizing, iteratedFDerivWithin, iteratedFDerivWithin_succ_eq_comp_left, smul_def
-/
lemma iteratedFDerivWithin_comp_neg {f : 𝕜 -> F} {s : Set 𝕜} (n : Nat) (a : 𝕜) :
    iteratedFDerivWithin 𝕜 n (fun x => f (-x)) s a
      = (-1 : 𝕜) ^ n • iteratedFDerivWithin 𝕜 n f (-s) (-a) := by
  induction n generalizing a with
  | zero => simp [iteratedFDerivWithin]
  | succ n ih =>
    have ih' : iteratedFDerivWithin 𝕜 n (fun x => f (-x)) s
        = fun a => (-1 : 𝕜) ^ n • iteratedFDerivWithin 𝕜 n f (-s) (-a) := by
      ext b
      rw [ih b]
    set g := fun a => iteratedFDerivWithin 𝕜 n f (-s) a
    rw [iteratedFDerivWithin_succ_eq_comp_left]; rw [iteratedFDerivWithin_succ_eq_comp_left]; rw [Function.comp_apply]; rw [Function.comp_apply]; rw [ih']; rw [← Pi.smul_def]; rw [fderivWithin_const_smul_field' ((-1 : 𝕜) ^ n) (f := fun a => g (-a))]; rw [fderivWithin_comp_neg (f := g)]; rw [← neg_one_smul 𝕜 (fderivWithin 𝕜 _ (-s) (-a))]; rw [← mul_smul _ (-1)]; rw [← pow_succ (-1) n]; rw [map_smul]

/--
theorem `iteratedFDerivWithin_comp_const_sub` / 定理 `iteratedFDerivWithin_comp_const_sub`

English:
theorem iteratedFDerivWithin_comp_const_sub
  given: {f : 𝕜 -> F} {s : Set 𝕜} (n : Nat) (c : 𝕜)
  proof: by
  ext a
  have : (fun z : 𝕜 => f (c - z)) = fun z => (fun w => f (c + w)) (-z) := by
    simp only [sub_eq_add_neg]
  rw [this]; rw [iteratedFDerivWithin_comp_neg (f := fun w => f (c + w)) n a]; rw [iteratedFDerivWithin_comp_add_left]
  ring_nf

中文:
定理 iteratedFDerivWithin_comp_const_sub
  条件: {f : 𝕜 -> F} {s : Set 𝕜} (n : 自然数) (c : 𝕜)
  证明: by
  ext a
  have : (fun z : 𝕜 => f (c - z)) = fun z => (fun w => f (c + w)) (-z) := by
    simp only [sub_eq_add_neg]
  rw [this]; rw [iteratedFDerivWithin_comp_neg (f := fun w => f (c + w)) n a]; rw [iteratedFDerivWithin_comp_add_left]
  ring_nf

Depends on / 依赖: iteratedFDerivWithin_comp_add_left, iteratedFDerivWithin_comp_neg, ring_nf, sub_eq_add_neg
-/
theorem iteratedFDerivWithin_comp_const_sub {f : 𝕜 -> F} {s : Set 𝕜} (n : Nat) (c : 𝕜) :
    iteratedFDerivWithin 𝕜 n (fun z => f (c - z)) s =
      fun x => (-1 : 𝕜) ^ n • iteratedFDerivWithin 𝕜 n f (c +ᵥ -s) (c - x) := by
  ext a
  have : (fun z : 𝕜 => f (c - z)) = fun z => (fun w => f (c + w)) (-z) := by
    simp only [sub_eq_add_neg]
  rw [this]; rw [iteratedFDerivWithin_comp_neg (f := fun w => f (c + w)) n a]; rw [iteratedFDerivWithin_comp_add_left]
  ring_nf
