/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, David Ledvinka
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
public import Mathlib.Order.CompletePartialOrder

/-!
# Pair Reduction

The goal of this file is to prove the theorem `pair_reduction`. This is essentially Lemma 6.1 in
[kratschmer_urusov2023] which is an extension of Lemma B.2.7. in [talagrand2014].
Given pseudometric spaces `T` and `E`, `c ≥ 0`, and a finite subset `J` of `T` such that
`|J| ≤ aⁿ` for some `a ≥ 0` and `n : ℕ`, `pair_reduction` states that there exists a set `K ⊆ J²`
such that for any function `f : T → E`:

1. `|K| ≤ a|J|`
2. `∀ (s, t) ∈ K, d(s, t) ≤ cn`
3. `sup_{s, t ∈ J : d(s, t) ≤ c} d(f(s), f(t)) ≤ 2 sup_{(s, t) ∈ K} d(f(s), f(t))`

When applying the chaining technique for bounding the supremum of the increments of stochastic
processes, `pair_reduction` is used to reduce the order of the dependence of the bound on the
covering numbers of the pseudometric space. As a simple example of how it could be used, suppose
`T` has an `ε`-covering number `N` and suppose `J` is an `ε`-covering of `T` with `|J| = N`.
Let `f : Ω → T → E` be any stochastic process such that `𝔼 d(f(s), f(t)) ≤ d (s, t)` for all
`s, t ∈ T`. Then naively
```
  𝔼[sup_{(s, t) ∈ J} : d(s, t) ≤ c} d(f(s), f(t))]
    ≤ ∑_{(s, t) ∈ J² : d(s, t) ≤ c} 𝔼[d(f(s), f(t))]
    ≤ |J|² c
    = c N²
```
but applying `pair_reduction` with `n = log |J|` we get
```
  𝔼[sup_{(s, t) ∈ J : d(s, t) ≤ c} d(f(s), f(t))]
    ≤ 2 𝔼[sup_{(s, t) ∈ K} d(f(s), f(t))]
    ≤ 2 ∑_{(s, t) ∈ K} 𝔼[d(f(s), f(t))]
    ≤ 2 a |J| c log |J|
    ≤ 2 a c N log N
```
`pair_reduction` is used in [kratschmer_urusov2023] to prove a form of the Kolmogorov-Chentsov
theorem that applies to stochastic processes which satisfy the Kolmogorov condition but works
on very general metric spaces.

## Implementation

In this section we sketch a proof of `pair_reduction` with references to the corresponding steps
in the lean code.

For any `V : Finset T` and `t : T` we define the log-size radius of `t` in `V` to be the smallest
natural number `k` greater than zero such that `|{x ∈ V | d(t, x) ≤ kc}| ≤ aᵏ`.
(see `logSizeRadius`)

We construct a sequence `Vᵢ` of subsets of `J`, a sequence `tᵢ ∈ Vᵢ` and a sequence of `rᵢ : ℕ`
inductively as follows (see `logSizeBallSeq`):

* `V₀ = J`, `t₀` is chosen arbitrarily in `J`, `r₀` is the log-size radius of `t₀` in `V₀`
* `Vᵢ₊₁ = Vᵢ \ Bᵢ` where `Bᵢ := {x ∈ V | d(t, x) ≤ (rᵢ - 1) c}`, `tᵢ₊₁` is chosen arbitrarily in
  `Vᵢ₊₁` (if it is nonempty), `rᵢ₊₁` is the log-size radius of `tᵢ₊₁` in `Vᵢ₊₁`.

Then `Vᵢ` is a strictly decreasing sequence (see `card_finset_logSizeBallSeq_add_one_lt`) until
`Vᵢ` is empty. In particular `Vᵢ = ∅` for `i ≥ |J|`
(see `card_finset_logSizeBallSeq_card_eq_zero`).

We will show that `K = ⋃_{i=1}^|J| {tᵢ} × {x ∈ Vᵢ | d(tᵢ, x) ≤ crᵢ}` suffices
(see `pairSet` and `pairSetSeq`).

To prove (1) we have that
```
  |K| ≤ ∑_{i=0}^|J| |{x ∈ Vᵢ : d(t, x) ≤ crᵢ}|
      ≤ ∑_{i=0}^|J| a ^ rᵢ (by definition of `rᵢ`)
      = a ∑_{i=0}^|J| a ^ (rᵢ - 1)
      ≤ a ∑_{i=0}^|J| |Bᵢ| (by definition of `rᵢ`)
      ≤ a |J| (since the `Bᵢ` are disjoint (see `disjoint_smallBall_logSizeBallSeq`))
```
(see `card_pairSet_le`).

(2) follows easily from the definition of K and the fact that `rᵢ ≤ n` for each `i`
(see `edist_le_of_mem_pairSet` and `radius_logSizeBallSeq_le`)

Finally we prove (3). Let `s, t ∈ J` such that `d(s, t) ≤ c`. Let `i` be the largest integer
such that both `s, t ∈ Vᵢ`. WLOG suppose `s ∉ Vᵢ₊₁` so that in particular `s ∈ Bᵢ` which means
by definition that `d(tᵢ, s) ≤ (rᵢ - 1)c`. Then we also have
```
d(tᵢ, t) ≤ d(tᵢ, s) + d(s, t) ≤ (rᵢ - 1)c + c = rᵢc
```
hence `(tᵢ, s), (tᵢ, t) ∈ K`. Furthermore
```
d(f(s), f(t)) ≤ d(f(tᵢ), f(s)) + d(f(tᵢ), f(t))
```
taking supremums completes the proof (see `iSup_edist_pairSet`).

## References

* [V. Krätschmer, M. Urusov, *A Kolmogorov–Chentsov Type Theorem on General Metric Spaces with
  Applications to Limit Theorems for Banach-Valued Processes*][kratschmer_urusov2023]
* [M. Talagrand, *Upper and Lower Bounds for Stochastic Processes*][talagrand2014]

-/

@[expose] public section

open scoped ENNReal NNReal Finset

variable {T : Type*} [PseudoEMetricSpace T] {a c : Real>=0∞} {n : Nat} {V J : Finset T} {t : T}

namespace PairReduction

/--
lemma `exists_radius_le` / 引理 `exists_radius_le`

English:
lemma exists_radius_le
  given: (t : T) (V : Finset T) (ha : 1 < a) (c : Real>=0∞)
  proof: by
  have := ENNReal.tendsto_nhds_top_iff_nat.1
    ((ENNReal.tendsto_rpow_atTop_of_one_lt_base ha).comp tendsto_natCast_atTop_atTop) #V
  simp only [Function.comp_apply, ENNReal.rpow_natCast, Filter.eventually_atTop] at this
  obtain ⟨r, hr⟩ := this
  exact ⟨max r 1, le_max_right r 1,
    le_trans 

中文:
引理 exists_radius_le
  条件: (t : T) (V : Finset T) (ha : 1 < a) (c : 实数>=0∞)
  证明: by
  have := ENNReal.tendsto_nhds_top_iff_nat.1
    ((ENNReal.tendsto_rpow_atTop_of_one_lt_base ha).comp tendsto_natCast_atTop_atTop) #V
  simp only [Function.comp_apply, ENNReal.rpow_natCast, Filter.eventually_atTop] at this
  obtain ⟨r, hr⟩ := this
  exact ⟨max r 1, le_max_right r 1,
    le_trans 

Depends on / 依赖: ENNReal, ENNReal.rpow_natCast, ENNReal.tendsto_nhds_top_iff_nat, ENNReal.tendsto_rpow_atTop_of_one_lt_base, Filter, Filter.eventually_atTop, Finset, Finset.card_filter_le, Function, Function.comp_apply, card_filter_le, comp_apply, eventually_atTop, le_max_left, le_max_right, le_trans, mod_cast, rpow_natCast, tendsto_natCast_atTop_atTop, tendsto_nhds_top_iff_nat
-/
lemma exists_radius_le (t : T) (V : Finset T) (ha : 1 < a) (c : Real>=0∞) :
    exists r : Nat, 1 <= r ∧ #(V.filter fun x => edist t x <= r * c) <= a ^ r := by
  have := ENNReal.tendsto_nhds_top_iff_nat.1
    ((ENNReal.tendsto_rpow_atTop_of_one_lt_base ha).comp tendsto_natCast_atTop_atTop) #V
  simp only [Function.comp_apply, ENNReal.rpow_natCast, Filter.eventually_atTop] at this
  obtain ⟨r, hr⟩ := this
  exact ⟨max r 1, le_max_right r 1,
    le_trans (mod_cast Finset.card_filter_le V _) (hr (max r 1) (le_max_left r 1)).le⟩

/-- The log-size radius of `t` in `V` is the smallest natural number n greater than zero such that
`|{x ∈ V | d(t, x) ≤ nc}| ≤ aⁿ`. -/
noncomputable
/--
Definition of `logSizeRadius` / `logSizeRadius` 的定义

English:
definition logSizeRadius
  signature: (t : T) (V : Finset T) (a c : Real>=0∞)
  body: if h : 1 < a then Nat.find (exists_radius_le t V h c) else 0

中文:
定义 logSizeRadius
  签名: (t : T) (V : Finset T) (a c : 实数>=0∞)
  定义体: if h : 1 < a then Nat.find (exists_radius_le t V h c) else 0

Depends on / 依赖: Nat.find, exists_radius_le
-/
def logSizeRadius (t : T) (V : Finset T) (a c : Real>=0∞) : Nat :=
  if h : 1 < a then Nat.find (exists_radius_le t V h c) else 0

/--
lemma `one_le_logSizeRadius` / 引理 `one_le_logSizeRadius`

English:
lemma one_le_logSizeRadius
  given: (ha : 1 < a)
  proof: by
  rw [logSizeRadius]; rw [dif_pos ha]
  exact (Nat.find_spec (exists_radius_le t V ha c)).1

中文:
引理 one_le_logSizeRadius
  条件: (ha : 1 < a)
  证明: by
  rw [logSizeRadius]; rw [dif_pos ha]
  exact (Nat.find_spec (exists_radius_le t V ha c)).1

Depends on / 依赖: Nat.find_spec, dif_pos, exists_radius_le, find_spec, logSizeRadius
-/
lemma one_le_logSizeRadius (ha : 1 < a) :
    1 <= logSizeRadius t V a c := by
  rw [logSizeRadius]; rw [dif_pos ha]
  exact (Nat.find_spec (exists_radius_le t V ha c)).1

/--
lemma `card_le_logSizeRadius_le_pow_logSizeRadius` / 引理 `card_le_logSizeRadius_le_pow_logSizeRadius`

English:
lemma card_le_logSizeRadius_le_pow_logSizeRadius
  given: (ha : 1 < a)
  proof: by
  rw [logSizeRadius]; rw [dif_pos ha]
  exact (Nat.find_spec (exists_radius_le t V ha c)).2

中文:
引理 card_le_logSizeRadius_le_pow_logSizeRadius
  条件: (ha : 1 < a)
  证明: by
  rw [logSizeRadius]; rw [dif_pos ha]
  exact (Nat.find_spec (exists_radius_le t V ha c)).2

Depends on / 依赖: Nat.find_spec, dif_pos, exists_radius_le, find_spec, logSizeRadius
-/
lemma card_le_logSizeRadius_le_pow_logSizeRadius (ha : 1 < a) :
    #(V.filter fun x => edist t x <= logSizeRadius t V a c * c) <= a ^ (logSizeRadius t V a c) := by
  rw [logSizeRadius]; rw [dif_pos ha]
  exact (Nat.find_spec (exists_radius_le t V ha c)).2

/--
lemma `pow_logSizeRadius_le_card_le_logSizeRadius` / 引理 `pow_logSizeRadius_le_card_le_logSizeRadius`

English:
lemma pow_logSizeRadius_le_card_le_logSizeRadius
  given: (ha : 1 < a) (ht : t in V)
  proof: by
  by_cases h_one : logSizeRadius t V a c = 1
  · simp only [h_one, tsub_self, pow_zero, Nat.cast_one, zero_mul, nonpos_iff_eq_zero,
      Nat.one_le_cast, Finset.one_le_card]
    exact ⟨t, by simpa⟩
  rw [logSizeRadius]; rw [dif_pos ha] at h_one ⊢
  have : Nat.find (exists_radius_le t V ha c) - 1

中文:
引理 pow_logSizeRadius_le_card_le_logSizeRadius
  条件: (ha : 1 < a) (ht : t in V)
  证明: by
  by_cases h_one : logSizeRadius t V a c = 1
  · simp only [h_one, tsub_self, pow_zero, Nat.cast_one, zero_mul, nonpos_iff_eq_zero,
      Nat.one_le_cast, Finset.one_le_card]
    exact ⟨t, by simpa⟩
  rw [logSizeRadius]; rw [dif_pos ha] at h_one ⊢
  have : Nat.find (exists_radius_le t V ha c) - 1

Depends on / 依赖: ENNReal, ENNReal.natCast_sub, Finset, Finset.one_le_card, Nat.cast_one, Nat.find, Nat.find_min, Nat.one_le_cast, cast_one, dif_pos, exists_radius_le, find_min, h_one, logSizeRadius, natCast_sub, nonpos_iff_eq_zero, not_and, not_le, one_le_card, one_le_cast
-/
lemma pow_logSizeRadius_le_card_le_logSizeRadius (ha : 1 < a) (ht : t in V) :
    a ^ (logSizeRadius t V a c - 1)
      <= #(V.filter fun x => edist t x <= (logSizeRadius t V a c - 1) * c) := by
  by_cases h_one : logSizeRadius t V a c = 1
  · simp only [h_one, tsub_self, pow_zero, Nat.cast_one, zero_mul, nonpos_iff_eq_zero,
      Nat.one_le_cast, Finset.one_le_card]
    exact ⟨t, by simpa⟩
  rw [logSizeRadius]; rw [dif_pos ha] at h_one ⊢
  have : Nat.find (exists_radius_le t V ha c) - 1 < Nat.find (exists_radius_le t V ha c) := by
    simp
  have h := Nat.find_min (exists_radius_le t V ha c) this
  simp only [ENNReal.natCast_sub, Nat.cast_one, not_and, not_le] at h
  exact (h (by lia)).le

/--
Definition of `logSizeBallStruct` / `logSizeBallStruct` 的定义

English:
structure logSizeBallStruct
  parameters: (T : Type*)
  axioms and operations (3):
    - finset : Finset T
    - point : T
    - radius : Nat

中文:
结构 logSizeBallStruct
  参数: (T : 类型)
  公理与运算 (3 个):
    - finset : Finset T
    - point : T
    - radius : 自然数
-/
structure logSizeBallStruct (T : Type*) where
  /-- The underlying finite set of a `logSizeBallStruct` -/
  finset : Finset T
  /-- The underlying point of a `logSizeBallStruct` (typically a point in the underlying finite
  set) -/
  point : T
  /-- The underlying radius of a `logSizeBallStruct` (typically the log-size radius of the
  underlying point in the underlying finite set) -/
  radius : Nat

/-- If `(V, t, r)` is a `logSizeBallStruct` then `logSizeBallStruct.smallBall`
  is `{x ∈ V | d(t, x) ≤ (r - 1)c}`. -/
noncomputable
/--
Definition of `logSizeBallStruct.smallBall` / `logSizeBallStruct.smallBall` 的定义

English:
definition logSizeBallStruct.smallBall
  signature: (struct : logSizeBallStruct T) (c : Real>=0∞)
  body: struct.finset.filter fun x => edist struct.point x <= (struct.radius - 1) * c

中文:
定义 logSizeBallStruct.smallBall
  签名: (struct : logSizeBallStruct T) (c : 实数>=0∞)
  定义体: struct.finset.filter fun x => edist struct.point x <= (struct.radius - 1) * c

Depends on / 依赖: filter, finset, radius, struct, struct.finset.filter, struct.point, struct.radius
-/
def logSizeBallStruct.smallBall (struct : logSizeBallStruct T) (c : Real>=0∞) :
    Finset T :=
  struct.finset.filter fun x => edist struct.point x <= (struct.radius - 1) * c

/-- If `(V, t, r)` is a `logSizeBallStruct` then `logSizeBallStruct.ball`
  is `{x ∈ V | d(t, x) ≤ rc}`. -/
noncomputable
/--
Definition of `logSizeBallStruct.ball` / `logSizeBallStruct.ball` 的定义

English:
definition logSizeBallStruct.ball
  signature: (struct : logSizeBallStruct T) (c : Real>=0∞)
  body: struct.finset.filter fun x => edist struct.point x <= struct.radius * c

中文:
定义 logSizeBallStruct.ball
  签名: (struct : logSizeBallStruct T) (c : 实数>=0∞)
  定义体: struct.finset.filter fun x => edist struct.point x <= struct.radius * c

Depends on / 依赖: filter, finset, radius, struct, struct.finset.filter, struct.point, struct.radius
-/
def logSizeBallStruct.ball (struct : logSizeBallStruct T) (c : Real>=0∞) :
    Finset T :=
  struct.finset.filter fun x => edist struct.point x <= struct.radius * c

variable [DecidableEq T]

/-- We recursively define a log-size ball sequence `(Vᵢ, tᵢ, rᵢ)` by
  * `V₀ = J`, `t₀` is chosen arbitrarily in `J`, `r₀` is the log-size radius of `t₀` in `V₀`
  * `Vᵢ₊₁ = Vᵢ \ {x ∈ V | d(t, x) ≤ (rᵢ - 1)c}`, `tᵢ₊₁` is chosen arbitrarily in `Vᵢ₊₁`, `rᵢ₊₁` is
    the log-size radius of `tᵢ₊₁` in `Vᵢ₊₁`. -/
noncomputable
/--
Definition of `logSizeBallSeq` / `logSizeBallSeq` 的定义

English:
definition logSizeBallSeq
  signature: (J : Finset T) (hJ : J.Nonempty) (a c : Real>=0∞)
  body: (logSizeBallSeq J hJ a c n).finset \ ((logSizeBallSeq J hJ a c n).smallBall c)
    let t' := if hV' : V'.Nonempty then hV'.choose else (logSizeBallSeq J hJ a c n).point
    { finset := V',
      point := t',
      radius := logSizeRadius t' V' a c }

中文:
定义 logSizeBallSeq
  签名: (J : Finset T) (hJ : J.Nonempty) (a c : 实数>=0∞)
  定义体: (logSizeBallSeq J hJ a c n).finset \ ((logSizeBallSeq J hJ a c n).smallBall c)
    let t' := if hV' : V'.Nonempty then hV'.choose else (logSizeBallSeq J hJ a c n).point
    { finset := V',
      point := t',
      radius := logSizeRadius t' V' a c }

Depends on / 依赖: hJ.choose, logSizeRadius, radius
-/
def logSizeBallSeq (J : Finset T) (hJ : J.Nonempty) (a c : Real>=0∞) : Nat -> logSizeBallStruct T
  | 0 => { finset := J, point := hJ.choose, radius := logSizeRadius hJ.choose J a c }
  | n + 1 =>
    let V' := (logSizeBallSeq J hJ a c n).finset \ ((logSizeBallSeq J hJ a c n).smallBall c)
    let t' := if hV' : V'.Nonempty then hV'.choose else (logSizeBallSeq J hJ a c n).point
    { finset := V',
      point := t',
      radius := logSizeRadius t' V' a c }

/--
lemma `finset_logSizeBallSeq_zero` / 引理 `finset_logSizeBallSeq_zero`

English:
lemma finset_logSizeBallSeq_zero
  given: (hJ : J.Nonempty)
  proof: rfl

中文:
引理 finset_logSizeBallSeq_zero
  条件: (hJ : J.Nonempty)
  证明: rfl
-/
lemma finset_logSizeBallSeq_zero (hJ : J.Nonempty) :
    (logSizeBallSeq J hJ a c 0).finset = J := rfl

/--
lemma `point_logSizeBallSeq_zero` / 引理 `point_logSizeBallSeq_zero`

English:
lemma point_logSizeBallSeq_zero
  given: (hJ : J.Nonempty)
  proof: rfl

中文:
引理 point_logSizeBallSeq_zero
  条件: (hJ : J.Nonempty)
  证明: rfl
-/
lemma point_logSizeBallSeq_zero (hJ : J.Nonempty) :
    (logSizeBallSeq J hJ a c 0).point = hJ.choose := rfl

/--
lemma `radius_logSizeBallSeq_zero` / 引理 `radius_logSizeBallSeq_zero`

English:
lemma radius_logSizeBallSeq_zero
  given: (hJ : J.Nonempty)
  proof: rfl

中文:
引理 radius_logSizeBallSeq_zero
  条件: (hJ : J.Nonempty)
  证明: rfl
-/
lemma radius_logSizeBallSeq_zero (hJ : J.Nonempty) :
    (logSizeBallSeq J hJ a c 0).radius = logSizeRadius hJ.choose J a c := rfl

/--
lemma `finset_logSizeBallSeq_add_one` / 引理 `finset_logSizeBallSeq_add_one`

English:
lemma finset_logSizeBallSeq_add_one
  given: (hJ : J.Nonempty) (i : Nat)
  proof: rfl

中文:
引理 finset_logSizeBallSeq_add_one
  条件: (hJ : J.Nonempty) (i : 自然数)
  证明: rfl
-/
lemma finset_logSizeBallSeq_add_one (hJ : J.Nonempty) (i : Nat) :
    (logSizeBallSeq J hJ a c (i + 1)).finset =
      (logSizeBallSeq J hJ a c i).finset \ (logSizeBallSeq J hJ a c i).smallBall c := rfl

/--
lemma `point_logSizeBallSeq_add_one` / 引理 `point_logSizeBallSeq_add_one`

English:
lemma point_logSizeBallSeq_add_one
  given: (hJ : J.Nonempty) (i : Nat)
  proof: rfl

中文:
引理 point_logSizeBallSeq_add_one
  条件: (hJ : J.Nonempty) (i : 自然数)
  证明: rfl
-/
lemma point_logSizeBallSeq_add_one (hJ : J.Nonempty) (i : Nat) :
    (logSizeBallSeq J hJ a c (i + 1)).point
      = if hV' : (logSizeBallSeq J hJ a c (i + 1)).finset.Nonempty then hV'.choose
        else (logSizeBallSeq J hJ a c i).point := rfl

/--
lemma `radius_logSizeBallSeq_add_one` / 引理 `radius_logSizeBallSeq_add_one`

English:
lemma radius_logSizeBallSeq_add_one
  given: (hJ : J.Nonempty) (i : Nat)
  proof: rfl

中文:
引理 radius_logSizeBallSeq_add_one
  条件: (hJ : J.Nonempty) (i : 自然数)
  证明: rfl
-/
lemma radius_logSizeBallSeq_add_one (hJ : J.Nonempty) (i : Nat) :
    (logSizeBallSeq J hJ a c (i + 1)).radius
      = logSizeRadius (logSizeBallSeq J hJ a c (i + 1)).point
          (logSizeBallSeq J hJ a c (i + 1)).finset a c := rfl

/--
lemma `finset_logSizeBallSeq_add_one_subset` / 引理 `finset_logSizeBallSeq_add_one_subset`

English:
lemma finset_logSizeBallSeq_add_one_subset
  given: (hJ : J.Nonempty) (i : Nat)
  proof: by
  simp [finset_logSizeBallSeq_add_one]

中文:
引理 finset_logSizeBallSeq_add_one_subset
  条件: (hJ : J.Nonempty) (i : 自然数)
  证明: by
  simp [finset_logSizeBallSeq_add_one]

Depends on / 依赖: finset_logSizeBallSeq_add_one
-/
lemma finset_logSizeBallSeq_add_one_subset (hJ : J.Nonempty) (i : Nat) :
    (logSizeBallSeq J hJ a c (i + 1)).finset subseteq (logSizeBallSeq J hJ a c i).finset := by
  simp [finset_logSizeBallSeq_add_one]

/--
lemma `antitone_logSizeBallSeq_add_one_subset` / 引理 `antitone_logSizeBallSeq_add_one_subset`

English:
lemma antitone_logSizeBallSeq_add_one_subset
  given: (hJ : J.Nonempty)
  proof: antitone_nat_of_succ_le (finset_logSizeBallSeq_add_one_subset hJ)

中文:
引理 antitone_logSizeBallSeq_add_one_subset
  条件: (hJ : J.Nonempty)
  证明: antitone_nat_of_succ_le (finset_logSizeBallSeq_add_one_subset hJ)

Depends on / 依赖: antitone_nat_of_succ_le, finset_logSizeBallSeq_add_one_subset
-/
lemma antitone_logSizeBallSeq_add_one_subset (hJ : J.Nonempty) :
    Antitone (fun i => (logSizeBallSeq J hJ a c i).finset) :=
  antitone_nat_of_succ_le (finset_logSizeBallSeq_add_one_subset hJ)

/--
lemma `finset_logSizeBallSeq_subset_logSizeBallSeq_init` / 引理 `finset_logSizeBallSeq_subset_logSizeBallSeq_init`

English:
lemma finset_logSizeBallSeq_subset_logSizeBallSeq_init
  given: (hJ : J.Nonempty) (i : Nat)
  proof: by
apply subset_trans antitone_logSizeBallSeq_add_one_subset hJ zero_le
  simp [finset_logSizeBallSeq_zero]

中文:
引理 finset_logSizeBallSeq_subset_logSizeBallSeq_init
  条件: (hJ : J.Nonempty) (i : 自然数)
  证明: by
apply subset_trans antitone_logSizeBallSeq_add_one_subset hJ zero_le
  simp [finset_logSizeBallSeq_zero]

Depends on / 依赖: antitone_logSizeBallSeq_add_one_subset, finset_logSizeBallSeq_zero, subset_trans, zero_le
-/
lemma finset_logSizeBallSeq_subset_logSizeBallSeq_init (hJ : J.Nonempty) (i : Nat) :
    (logSizeBallSeq J hJ a c i).finset subseteq J := by
apply subset_trans antitone_logSizeBallSeq_add_one_subset hJ zero_le
  simp [finset_logSizeBallSeq_zero]

/--
lemma `radius_logSizeBallSeq_le` / 引理 `radius_logSizeBallSeq_le`

English:
lemma radius_logSizeBallSeq_le
  statement: (hJ : J.Nonempty) (ha : 1 < a) (hn : 1 <= n) (hJ_card : #J <= a ^ n)
  proof: by
  match i with
  | 0 =>
    simp only [radius_logSizeBallSeq_zero, logSizeRadius, ha, ↓reduceDIte]
    exact Nat.find_min' _ ⟨hn, le_trans (by gcongr; apply Finset.filter_subset) hJ_card⟩
  | i + 1 =>
    simp only [radius_logSizeBallSeq_add_one, logSizeRadius, ha, ↓reduceDIte]
    refine Nat.fin

中文:
引理 radius_logSizeBallSeq_le
  结论: (hJ : J.Nonempty) (ha : 1 < a) (hn : 1 <= n) (hJ_card : #J <= a ^ n)
  证明: by
  match i with
  | 0 =>
    simp only [radius_logSizeBallSeq_zero, logSizeRadius, ha, ↓reduceDIte]
    exact Nat.find_min' _ ⟨hn, le_trans (by gcongr; apply Finset.filter_subset) hJ_card⟩
  | i + 1 =>
    simp only [radius_logSizeBallSeq_add_one, logSizeRadius, ha, ↓reduceDIte]
    refine Nat.fin

Depends on / 依赖: Finset, Finset.filter_subset, Nat.find_min, filter_subset, find_min, finset_logSizeBallSeq_subset_logSizeBallSeq_init, hJ_card, le_trans, logSizeRadius, radius_logSizeBallSeq_add_one, radius_logSizeBallSeq_zero, reduceDIte
-/
lemma radius_logSizeBallSeq_le (hJ : J.Nonempty) (ha : 1 < a) (hn : 1 <= n) (hJ_card : #J <= a ^ n)
    (i : Nat) : (logSizeBallSeq J hJ a c i).radius <= n := by
  match i with
  | 0 =>
    simp only [radius_logSizeBallSeq_zero, logSizeRadius, ha, ↓reduceDIte]
    exact Nat.find_min' _ ⟨hn, le_trans (by gcongr; apply Finset.filter_subset) hJ_card⟩
  | i + 1 =>
    simp only [radius_logSizeBallSeq_add_one, logSizeRadius, ha, ↓reduceDIte]
    refine Nat.find_min' _ ⟨hn, le_trans ?_ hJ_card⟩
    gcongr
    exact (Finset.filter_subset _ _).trans (finset_logSizeBallSeq_subset_logSizeBallSeq_init _ _)

/--
lemma `one_le_radius_logSizeBallSeq` / 引理 `one_le_radius_logSizeBallSeq`

English:
lemma one_le_radius_logSizeBallSeq
  given: (hJ : J.Nonempty) (ha : 1 < a) (i : Nat)
  proof: by
  match i with
  | 0 => exact one_le_logSizeRadius ha
  | i + 1 => exact one_le_logSizeRadius ha

中文:
引理 one_le_radius_logSizeBallSeq
  条件: (hJ : J.Nonempty) (ha : 1 < a) (i : 自然数)
  证明: by
  match i with
  | 0 => exact one_le_logSizeRadius ha
  | i + 1 => exact one_le_logSizeRadius ha

Depends on / 依赖: one_le_logSizeRadius
-/
lemma one_le_radius_logSizeBallSeq (hJ : J.Nonempty) (ha : 1 < a) (i : Nat) :
    1 <= (logSizeBallSeq J hJ a c i).radius := by
  match i with
  | 0 => exact one_le_logSizeRadius ha
  | i + 1 => exact one_le_logSizeRadius ha

set_option backward.isDefEq.respectTransparency false in
/--
lemma `point_mem_finset_logSizeBallSeq` / 引理 `point_mem_finset_logSizeBallSeq`

English:
lemma point_mem_finset_logSizeBallSeq
  statement: (hJ : J.Nonempty) (i : Nat)
  proof: by
  match i with
  | 0 => simp [point_logSizeBallSeq_zero, finset_logSizeBallSeq_zero, Exists.choose_spec]
  | i + 1 => simp [point_logSizeBallSeq_add_one, h, Exists.choose_spec]

中文:
引理 point_mem_finset_logSizeBallSeq
  结论: (hJ : J.Nonempty) (i : 自然数)
  证明: by
  match i with
  | 0 => simp [point_logSizeBallSeq_zero, finset_logSizeBallSeq_zero, Exists.choose_spec]
  | i + 1 => simp [point_logSizeBallSeq_add_one, h, Exists.choose_spec]

Depends on / 依赖: Exists, Exists.choose_spec, choose_spec, finset_logSizeBallSeq_zero, point_logSizeBallSeq_add_one, point_logSizeBallSeq_zero
-/
lemma point_mem_finset_logSizeBallSeq (hJ : J.Nonempty) (i : Nat)
    (h : (logSizeBallSeq J hJ a c i).finset.Nonempty) :
    (logSizeBallSeq J hJ a c i).point in (logSizeBallSeq J hJ a c i).finset := by
  match i with
  | 0 => simp [point_logSizeBallSeq_zero, finset_logSizeBallSeq_zero, Exists.choose_spec]
  | i + 1 => simp [point_logSizeBallSeq_add_one, h, Exists.choose_spec]

/--
lemma `point_mem_logSizeBallSeq_init` / 引理 `point_mem_logSizeBallSeq_init`

English:
lemma point_mem_logSizeBallSeq_init
  given: (hJ : J.Nonempty) (i : Nat)
  proof: by
  induction i with
  | zero => exact point_mem_finset_logSizeBallSeq hJ 0 hJ
  | succ i ih =>
    by_cases h : (logSizeBallSeq J hJ a c (i + 1)).finset.Nonempty
    · refine Finset.mem_of_subset ?_ (point_mem_finset_logSizeBallSeq hJ (i + 1) h)
      apply finset_logSizeBallSeq_subset_logSizeBall

中文:
引理 point_mem_logSizeBallSeq_init
  条件: (hJ : J.Nonempty) (i : 自然数)
  证明: by
  induction i with
  | zero => exact point_mem_finset_logSizeBallSeq hJ 0 hJ
  | succ i ih =>
    by_cases h : (logSizeBallSeq J hJ a c (i + 1)).finset.Nonempty
    · refine Finset.mem_of_subset ?_ (point_mem_finset_logSizeBallSeq hJ (i + 1) h)
      apply finset_logSizeBallSeq_subset_logSizeBall

Depends on / 依赖: Finset, Finset.mem_of_subset, Nonempty, finset, finset.Nonempty, finset_logSizeBallSeq_subset_logSizeBallSeq_init, logSizeBallSeq, mem_of_subset, point_logSizeBallSeq_add_one, point_mem_finset_logSizeBallSeq
-/
lemma point_mem_logSizeBallSeq_init (hJ : J.Nonempty) (i : Nat) :
    (logSizeBallSeq J hJ a c i).point in J := by
  induction i with
  | zero => exact point_mem_finset_logSizeBallSeq hJ 0 hJ
  | succ i ih =>
    by_cases h : (logSizeBallSeq J hJ a c (i + 1)).finset.Nonempty
    · refine Finset.mem_of_subset ?_ (point_mem_finset_logSizeBallSeq hJ (i + 1) h)
      apply finset_logSizeBallSeq_subset_logSizeBallSeq_init
    simp [point_logSizeBallSeq_add_one, ih, h]

/--
lemma `point_notMem_finset_logSizeBallSeq_add_one` / 引理 `point_notMem_finset_logSizeBallSeq_add_one`

English:
lemma point_notMem_finset_logSizeBallSeq_add_one
  given: (hJ : J.Nonempty) (i : Nat)
  proof: by
  simp [finset_logSizeBallSeq_add_one, logSizeBallStruct.smallBall]

中文:
引理 point_notMem_finset_logSizeBallSeq_add_one
  条件: (hJ : J.Nonempty) (i : 自然数)
  证明: by
  simp [finset_logSizeBallSeq_add_one, logSizeBallStruct.smallBall]

Depends on / 依赖: finset_logSizeBallSeq_add_one, logSizeBallStruct, logSizeBallStruct.smallBall, smallBall
-/
lemma point_notMem_finset_logSizeBallSeq_add_one (hJ : J.Nonempty) (i : Nat) :
    (logSizeBallSeq J hJ a c i).point ∉ (logSizeBallSeq J hJ a c (i + 1)).finset := by
  simp [finset_logSizeBallSeq_add_one, logSizeBallStruct.smallBall]

/--
lemma `finset_logSizeBallSeq_add_one_ssubset` / 引理 `finset_logSizeBallSeq_add_one_ssubset`

English:
lemma finset_logSizeBallSeq_add_one_ssubset
  statement: (hJ : J.Nonempty) (i : Nat)
  proof: by
    apply ssubset_of_subset_not_subset
    · simp [finset_logSizeBallSeq_add_one]
    refine Set.not_subset.mpr ⟨(logSizeBallSeq J hJ a c i).point, ?_, ?_⟩
    · exact point_mem_finset_logSizeBallSeq hJ i h
    · exact point_notMem_finset_logSizeBallSeq_add_one hJ i

中文:
引理 finset_logSizeBallSeq_add_one_ssubset
  结论: (hJ : J.Nonempty) (i : 自然数)
  证明: by
    apply ssubset_of_subset_not_subset
    · simp [finset_logSizeBallSeq_add_one]
    refine Set.not_subset.mpr ⟨(logSizeBallSeq J hJ a c i).point, ?_, ?_⟩
    · exact point_mem_finset_logSizeBallSeq hJ i h
    · exact point_notMem_finset_logSizeBallSeq_add_one hJ i

Depends on / 依赖: Set.not_subset.mpr, finset_logSizeBallSeq_add_one, logSizeBallSeq, not_subset, point_mem_finset_logSizeBallSeq, point_notMem_finset_logSizeBallSeq_add_one, ssubset_of_subset_not_subset
-/
lemma finset_logSizeBallSeq_add_one_ssubset (hJ : J.Nonempty) (i : Nat)
    (h : (logSizeBallSeq J hJ a c i).finset.Nonempty) :
    (logSizeBallSeq J hJ a c (i + 1)).finset ⊂ (logSizeBallSeq J hJ a c i).finset := by
    apply ssubset_of_subset_not_subset
    · simp [finset_logSizeBallSeq_add_one]
    refine Set.not_subset.mpr ⟨(logSizeBallSeq J hJ a c i).point, ?_, ?_⟩
    · exact point_mem_finset_logSizeBallSeq hJ i h
    · exact point_notMem_finset_logSizeBallSeq_add_one hJ i

/--
lemma `card_finset_logSizeBallSeq_add_one_lt` / 引理 `card_finset_logSizeBallSeq_add_one_lt`

English:
lemma card_finset_logSizeBallSeq_add_one_lt
  statement: (hJ : J.Nonempty) (i : Nat)
  proof: by
  simp [Finset.card_lt_card, finset_logSizeBallSeq_add_one_ssubset hJ i h]

中文:
引理 card_finset_logSizeBallSeq_add_one_lt
  结论: (hJ : J.Nonempty) (i : 自然数)
  证明: by
  simp [Finset.card_lt_card, finset_logSizeBallSeq_add_one_ssubset hJ i h]

Depends on / 依赖: Finset, Finset.card_lt_card, card_lt_card, finset_logSizeBallSeq_add_one_ssubset
-/
lemma card_finset_logSizeBallSeq_add_one_lt (hJ : J.Nonempty) (i : Nat)
    (h : (logSizeBallSeq J hJ a c i).finset.Nonempty) :
    #(logSizeBallSeq J hJ a c (i + 1)).finset < #(logSizeBallSeq J hJ a c i).finset := by
  simp [Finset.card_lt_card, finset_logSizeBallSeq_add_one_ssubset hJ i h]

/--
lemma `card_finset_logSizeBallSeq_le` / 引理 `card_finset_logSizeBallSeq_le`

English:
lemma card_finset_logSizeBallSeq_le
  given: (hJ : J.Nonempty) (i : Nat)
  proof: by
  induction i with
  | zero => simp [finset_logSizeBallSeq_zero]
  | succ i ih =>
    by_cases h : (logSizeBallSeq J hJ a c i).finset.Nonempty
    · have := card_finset_logSizeBallSeq_add_one_lt hJ i h
      lia
apply le_trans Finset.card_le_card (finset_logSizeBallSeq_add_one_subset hJ i)
    su

中文:
引理 card_finset_logSizeBallSeq_le
  条件: (hJ : J.Nonempty) (i : 自然数)
  证明: by
  induction i with
  | zero => simp [finset_logSizeBallSeq_zero]
  | succ i ih =>
    by_cases h : (logSizeBallSeq J hJ a c i).finset.Nonempty
    · have := card_finset_logSizeBallSeq_add_one_lt hJ i h
      lia
apply le_trans Finset.card_le_card (finset_logSizeBallSeq_add_one_subset hJ i)
    su

Depends on / 依赖: Finset, Finset.card_le_card, Finset.card_ne_zero.not, Nonempty, card_finset_logSizeBallSeq_add_one_lt, card_le_card, card_ne_zero, finset, finset.Nonempty, finset_logSizeBallSeq_add_one_subset, finset_logSizeBallSeq_zero, le_trans, logSizeBallSeq, not_ne_iff
-/
lemma card_finset_logSizeBallSeq_le (hJ : J.Nonempty) (i : Nat) :
    #(logSizeBallSeq J hJ a c i).finset <= #J - i := by
  induction i with
  | zero => simp [finset_logSizeBallSeq_zero]
  | succ i ih =>
    by_cases h : (logSizeBallSeq J hJ a c i).finset.Nonempty
    · have := card_finset_logSizeBallSeq_add_one_lt hJ i h
      lia
apply le_trans Finset.card_le_card (finset_logSizeBallSeq_add_one_subset hJ i)
    suffices #(logSizeBallSeq J hJ a c i).finset = 0 by simp [this]
    rwa [← not_ne_iff, Finset.card_ne_zero.not]

/--
lemma `card_finset_logSizeBallSeq_card_eq_zero` / 引理 `card_finset_logSizeBallSeq_card_eq_zero`

English:
lemma card_finset_logSizeBallSeq_card_eq_zero
  given: (hJ : J.Nonempty)
  proof: by
  rw [← Nat.le_zero]; rw [← tsub_self #J]
  exact card_finset_logSizeBallSeq_le hJ #J

中文:
引理 card_finset_logSizeBallSeq_card_eq_zero
  条件: (hJ : J.Nonempty)
  证明: by
  rw [← Nat.le_zero]; rw [← tsub_self #J]
  exact card_finset_logSizeBallSeq_le hJ #J

Depends on / 依赖: Nat.le_zero, card_finset_logSizeBallSeq_le, le_zero, tsub_self
-/
lemma card_finset_logSizeBallSeq_card_eq_zero (hJ : J.Nonempty) :
    #(logSizeBallSeq J hJ a c #J).finset = 0 := by
  rw [← Nat.le_zero]; rw [← tsub_self #J]
  exact card_finset_logSizeBallSeq_le hJ #J

/--
lemma `disjoint_smallBall_logSizeBallSeq` / 引理 `disjoint_smallBall_logSizeBallSeq`

English:
lemma disjoint_smallBall_logSizeBallSeq
  given: (hJ : J.Nonempty) {i j : Nat} (hij : i != j)
  proof: by
  wlog! h : i < j generalizing i j
· exact Disjoint.symm this hij.symm (ne_iff_lt_iff_le.mpr h).mp hij.symm
  apply Finset.disjoint_of_subset_right
  · exact (Finset.filter_subset _ _).trans (antitone_logSizeBallSeq_add_one_subset hJ h)
  simp [finset_logSizeBallSeq_add_one, Finset.disjoint_sdiff

中文:
引理 disjoint_smallBall_logSizeBallSeq
  条件: (hJ : J.Nonempty) {i j : 自然数} (hij : i != j)
  证明: by
  wlog! h : i < j generalizing i j
· exact Disjoint.symm this hij.symm (ne_iff_lt_iff_le.mpr h).mp hij.symm
  apply Finset.disjoint_of_subset_right
  · exact (Finset.filter_subset _ _).trans (antitone_logSizeBallSeq_add_one_subset hJ h)
  simp [finset_logSizeBallSeq_add_one, Finset.disjoint_sdiff

Depends on / 依赖: Disjoint, Disjoint.symm, Finset, Finset.disjoint_of_subset_right, Finset.disjoint_sdiff, Finset.filter_subset, antitone_logSizeBallSeq_add_one_subset, disjoint_of_subset_right, disjoint_sdiff, filter_subset, finset_logSizeBallSeq_add_one, generalizing, hij.symm, ne_iff_lt_iff_le, ne_iff_lt_iff_le.mpr
-/
lemma disjoint_smallBall_logSizeBallSeq (hJ : J.Nonempty) {i j : Nat} (hij : i != j) :
    Disjoint
      ((logSizeBallSeq J hJ a c i).smallBall c) ((logSizeBallSeq J hJ a c j).smallBall c) := by
  wlog! h : i < j generalizing i j
· exact Disjoint.symm this hij.symm (ne_iff_lt_iff_le.mpr h).mp hij.symm
  apply Finset.disjoint_of_subset_right
  · exact (Finset.filter_subset _ _).trans (antitone_logSizeBallSeq_add_one_subset hJ h)
  simp [finset_logSizeBallSeq_add_one, Finset.disjoint_sdiff]

/-- Given a log-size ball sequence `(Vᵢ, tᵢ, rᵢ)`, we define the pair set sequence by
`Kᵢ = {tᵢ} × {x ∈ Vᵢ | dist(tᵢ, x) ≤ rᵢc}`. -/
noncomputable
/--
Definition of `pairSetSeq` / `pairSetSeq` 的定义

English:
definition pairSetSeq
  signature: (J : Finset T) (a c : Real>=0∞) (n : Nat)
  body: if hJ : J.Nonempty then
    Finset.product {(logSizeBallSeq J hJ a c n).point} ((logSizeBallSeq J hJ a c n).ball c)
  else ∅

中文:
定义 pairSetSeq
  签名: (J : Finset T) (a c : 实数>=0∞) (n : 自然数)
  定义体: if hJ : J.Nonempty then
    Finset.product {(logSizeBallSeq J hJ a c n).point} ((logSizeBallSeq J hJ a c n).ball c)
  else ∅

Depends on / 依赖: Finset, Finset.product, J.Nonempty, Nonempty, logSizeBallSeq, product
-/
def pairSetSeq (J : Finset T) (a c : Real>=0∞) (n : Nat) : Finset (T × T) :=
  if hJ : J.Nonempty then
    Finset.product {(logSizeBallSeq J hJ a c n).point} ((logSizeBallSeq J hJ a c n).ball c)
  else ∅

/-- Given the pair set sequence Kᵢ we define the pair set `K` by `K = ⋃ i, Kᵢ`. -/
noncomputable
/--
Definition of `pairSet` / `pairSet` 的定义

English:
definition pairSet
  signature: (J : Finset T) (a c : Real>=0∞)
  body: Finset.biUnion (Finset.range #J) (pairSetSeq J a c)

中文:
定义 pairSet
  签名: (J : Finset T) (a c : 实数>=0∞)
  定义体: Finset.biUnion (Finset.range #J) (pairSetSeq J a c)

Depends on / 依赖: Finset, Finset.biUnion, Finset.range, biUnion, pairSetSeq
-/
def pairSet (J : Finset T) (a c : Real>=0∞) : Finset (T × T) :=
  Finset.biUnion (Finset.range #J) (pairSetSeq J a c)

/--
lemma `pairSet_empty_eq_empty` / 引理 `pairSet_empty_eq_empty`

English:
lemma pairSet_empty_eq_empty
  given: (a c : Real>=0∞)
  statement: pairSet (∅ : Finset T) a c = ∅
  proof: rfl

中文:
引理 pairSet_empty_eq_empty
  条件: (a c : 实数>=0∞)
  结论: pairSet (∅ : Finset T) a c = ∅
  证明: rfl
-/
lemma pairSet_empty_eq_empty (a c : Real>=0∞) : pairSet (∅ : Finset T) a c = ∅ := rfl

/--
lemma `pairSet_subset` / 引理 `pairSet_subset`

English:
lemma pairSet_subset
  statement: pairSet J a c subseteq J ×ˢ J
  proof: by
  unfold pairSet
  rw [Finset.biUnion_subset_iff_forall_subset]
  intro i hi
  by_cases hJ : J.Nonempty
  · simp only [pairSetSeq, hJ, ↓reduceDIte]
    apply Finset.product_subset_product
    · exact Finset.singleton_subset_iff.mpr (point_mem_logSizeBallSeq_init hJ _)
    exact (Finset.filter_sub

中文:
引理 pairSet_subset
  结论: pairSet J a c subseteq J ×ˢ J
  证明: by
  unfold pairSet
  rw [Finset.biUnion_subset_iff_forall_subset]
  intro i hi
  by_cases hJ : J.Nonempty
  · simp only [pairSetSeq, hJ, ↓reduceDIte]
    apply Finset.product_subset_product
    · exact Finset.singleton_subset_iff.mpr (point_mem_logSizeBallSeq_init hJ _)
    exact (Finset.filter_sub

Depends on / 依赖: Finset, Finset.biUnion_subset_iff_forall_subset, Finset.filter_subset, Finset.product_subset_product, Finset.singleton_subset_iff.mpr, J.Nonempty, Nonempty, biUnion_subset_iff_forall_subset, filter_subset, finset_logSizeBallSeq_subset_logSizeBallSeq_init, pairSet, pairSetSeq, point_mem_logSizeBallSeq_init, product_subset_product, reduceDIte, singleton_subset_iff
-/
lemma pairSet_subset : pairSet J a c subseteq J ×ˢ J := by
  unfold pairSet
  rw [Finset.biUnion_subset_iff_forall_subset]
  intro i hi
  by_cases hJ : J.Nonempty
  · simp only [pairSetSeq, hJ, ↓reduceDIte]
    apply Finset.product_subset_product
    · exact Finset.singleton_subset_iff.mpr (point_mem_logSizeBallSeq_init hJ _)
    exact (Finset.filter_subset _ _).trans (finset_logSizeBallSeq_subset_logSizeBallSeq_init _ _)
  simp [pairSetSeq, hJ]

/--
lemma `card_pairSetSeq_le_logSizeRadius_mul` / 引理 `card_pairSetSeq_le_logSizeRadius_mul`

English:
lemma card_pairSetSeq_le_logSizeRadius_mul
  given: (hJ : J.Nonempty) (i : Nat) (ha : 1 < a)
  proof: by
  induction i with
  | zero =>
    simpa [pairSetSeq, hJ, finset_logSizeBallSeq_zero, logSizeBallStruct.ball,
      radius_logSizeBallSeq_zero] using! card_le_logSizeRadius_le_pow_logSizeRadius ha
  | succ i ih =>
    by_cases! h : (logSizeBallSeq J hJ a c (i + 1)).finset.Nonempty
    · simpa [pa

中文:
引理 card_pairSetSeq_le_logSizeRadius_mul
  条件: (hJ : J.Nonempty) (i : 自然数) (ha : 1 < a)
  证明: by
  induction i with
  | zero =>
    simpa [pairSetSeq, hJ, finset_logSizeBallSeq_zero, logSizeBallStruct.ball,
      radius_logSizeBallSeq_zero] using! card_le_logSizeRadius_le_pow_logSizeRadius ha
  | succ i ih =>
    by_cases! h : (logSizeBallSeq J hJ a c (i + 1)).finset.Nonempty
    · simpa [pa

Depends on / 依赖: Nonempty, card_le_logSizeRadius_le_pow_logSizeRadius, finset, finset.Nonempty, finset_logSizeBallSeq_zero, logSizeBallSeq, logSizeBallStruct, logSizeBallStruct.ball, pairSetSeq, radius_logSizeBallSeq_zero
-/
lemma card_pairSetSeq_le_logSizeRadius_mul (hJ : J.Nonempty) (i : Nat) (ha : 1 < a) :
    ↑(#(pairSetSeq J a c i)) <= (if (logSizeBallSeq J hJ a c i).finset.Nonempty then 1 else 0)
    * a ^ (logSizeBallSeq J hJ a c i).radius := by
  induction i with
  | zero =>
    simpa [pairSetSeq, hJ, finset_logSizeBallSeq_zero, logSizeBallStruct.ball,
      radius_logSizeBallSeq_zero] using! card_le_logSizeRadius_le_pow_logSizeRadius ha
  | succ i ih =>
    by_cases! h : (logSizeBallSeq J hJ a c (i + 1)).finset.Nonempty
    · simpa [pairSetSeq, logSizeBallStruct.ball, h, hJ]
        using! card_le_logSizeRadius_le_pow_logSizeRadius ha
    simp [pairSetSeq, logSizeBallStruct.ball, h, hJ]

/--
lemma `logSizeRadius_le_card_smallBall` / 引理 `logSizeRadius_le_card_smallBall`

English:
lemma logSizeRadius_le_card_smallBall
  given: (hJ : J.Nonempty) (i : Nat) (ha : 1 < a)
  proof: by
  match i with
  | 0 =>
    simpa [finset_logSizeBallSeq_zero, hJ, logSizeBallStruct.smallBall, radius_logSizeBallSeq_zero]
      using! pow_logSizeRadius_le_card_le_logSizeRadius ha (Exists.choose_spec hJ)
  | i + 1 =>
    by_cases! h : (logSizeBallSeq J hJ a c (i + 1)).finset.Nonempty
    · sim

中文:
引理 logSizeRadius_le_card_smallBall
  条件: (hJ : J.Nonempty) (i : 自然数) (ha : 1 < a)
  证明: by
  match i with
  | 0 =>
    simpa [finset_logSizeBallSeq_zero, hJ, logSizeBallStruct.smallBall, radius_logSizeBallSeq_zero]
      using! pow_logSizeRadius_le_card_le_logSizeRadius ha (Exists.choose_spec hJ)
  | i + 1 =>
    by_cases! h : (logSizeBallSeq J hJ a c (i + 1)).finset.Nonempty
    · sim

Depends on / 依赖: Exists, Exists.choose_spec, Nonempty, choose_spec, finset, finset.Nonempty, finset_logSizeBallSeq_zero, logSizeBallSeq, logSizeBallStruct, logSizeBallStruct.smallBall, point_mem_finset_logSizeBallSeq, pow_logSizeRadius_le_card_le_logSizeRadius, radius_logSizeBallSeq_add_one, radius_logSizeBallSeq_zero, smallBall
-/
lemma logSizeRadius_le_card_smallBall (hJ : J.Nonempty) (i : Nat) (ha : 1 < a) :
    (if (logSizeBallSeq J hJ a c i).finset.Nonempty then 1 else 0) *
    a ^ ((logSizeBallSeq J hJ a c i).radius - 1) <= #((logSizeBallSeq J hJ a c i).smallBall c) := by
  match i with
  | 0 =>
    simpa [finset_logSizeBallSeq_zero, hJ, logSizeBallStruct.smallBall, radius_logSizeBallSeq_zero]
      using! pow_logSizeRadius_le_card_le_logSizeRadius ha (Exists.choose_spec hJ)
  | i + 1 =>
    by_cases! h : (logSizeBallSeq J hJ a c (i + 1)).finset.Nonempty
    · simpa [h, logSizeBallStruct.smallBall, radius_logSizeBallSeq_add_one] using!
        pow_logSizeRadius_le_card_le_logSizeRadius ha
          (point_mem_finset_logSizeBallSeq hJ _ h)
    simp [h]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `card_pairSet_le` / 引理 `card_pairSet_le`

English:
lemma card_pairSet_le
  given: (ha : 1 < a)
  statement: #(pairSet J a c) <= a * #J
  proof: by
  wlog hJ : J.Nonempty
  · simp [Finset.not_nonempty_iff_eq_empty.mp hJ]
  unfold pairSet
  grw [Finset.card_biUnion_le, Nat.cast_sum,
    Finset.sum_le_sum fun i _ => card_pairSetSeq_le_logSizeRadius_mul hJ i ha,
    Finset.sum_le_sum fun _ _ => mul_le_mul_right (pow_le_pow_right₀ ha.le le_tsub_

中文:
引理 card_pairSet_le
  条件: (ha : 1 < a)
  结论: #(pairSet J a c) <= a * #J
  证明: by
  wlog hJ : J.Nonempty
  · simp [Finset.not_nonempty_iff_eq_empty.mp hJ]
  unfold pairSet
  grw [Finset.card_biUnion_le, Nat.cast_sum,
    Finset.sum_le_sum fun i _ => card_pairSetSeq_le_logSizeRadius_mul hJ i ha,
    Finset.sum_le_sum fun _ _ => mul_le_mul_right (pow_le_pow_right₀ ha.le le_tsub_

Depends on / 依赖: Finset, Finset.car, Finset.card_biUnion_le, Finset.mul_sum, Finset.not_nonempty_iff_eq_empty.mp, Finset.sum_le_sum, J.Nonempty, Nat.cast_sum, Nonempty, card_biUnion_le, card_pairSetSeq_le_logSizeRadius_mul, cast_sum, conv_lhs, ha.le, le_tsub_add, logSizeRadius_le_card_smallBall, mul_assoc, mul_comm, mul_le_mul_right, mul_sum
-/
lemma card_pairSet_le (ha : 1 < a) : #(pairSet J a c) <= a * #J := by
  wlog hJ : J.Nonempty
  · simp [Finset.not_nonempty_iff_eq_empty.mp hJ]
  unfold pairSet
  grw [Finset.card_biUnion_le, Nat.cast_sum,
    Finset.sum_le_sum fun i _ => card_pairSetSeq_le_logSizeRadius_mul hJ i ha,
    Finset.sum_le_sum fun _ _ => mul_le_mul_right (pow_le_pow_right₀ ha.le le_tsub_add) _]
  conv_lhs => enter [2]; ext _; rw [pow_add, pow_one, ← mul_assoc, mul_comm]
  grw [← Finset.mul_sum]
  gcongr
  grw [Finset.sum_le_sum fun i _ => logSizeRadius_le_card_smallBall hJ i ha, ← Nat.cast_sum,
    ← Finset.card_biUnion fun _ _ _ _ => disjoint_smallBall_logSizeBallSeq hJ]
  gcongr
  unfold logSizeBallStruct.smallBall
  rw [Finset.biUnion_subset_iff_forall_subset]
  intro i _
  exact (Finset.filter_subset _ _).trans (finset_logSizeBallSeq_subset_logSizeBallSeq_init _ _)

/--
lemma `edist_le_of_mem_pairSet` / 引理 `edist_le_of_mem_pairSet`

English:
lemma edist_le_of_mem_pairSet
  statement: (ha : 1 < a) (hJ_card : #J <= a ^ n) {s t : T}
  proof: by
  obtain ⟨i, hiJ, h'⟩ : exists i < #J, (s, t) in pairSetSeq J a c i := by simpa [pairSet] using h
  have hJ : J.Nonempty := Finset.card_pos.mp (Nat.zero_lt_of_lt hiJ)
  wlog! hn : 1 <= n
  · suffices s = t by simp [this]
    simp only [Nat.lt_one_iff.mp hn, pow_zero, Nat.cast_le_one] at hJ_card
 

中文:
引理 edist_le_of_mem_pairSet
  结论: (ha : 1 < a) (hJ_card : #J <= a ^ n) {s t : T}
  证明: by
  obtain ⟨i, hiJ, h'⟩ : exists i < #J, (s, t) in pairSetSeq J a c i := by simpa [pairSet] using h
  have hJ : J.Nonempty := Finset.card_pos.mp (Nat.zero_lt_of_lt hiJ)
  wlog! hn : 1 <= n
  · suffices s = t by simp [this]
    simp only [Nat.lt_one_iff.mp hn, pow_zero, Nat.cast_le_one] at hJ_card
 

Depends on / 依赖: Finset, Finset.card_le_one_iff.mp, Finset.card_pos.mp, Finset.mem_product.mp, Finset.product_eq_sprod, Finset.singleton_pro, J.Nonempty, Nat.cast_le_one, Nat.lt_one_iff.mp, Nat.zero_lt_of_lt, Nonempty, card_le_one_iff, card_pos, cast_le_one, hJ_card, logSizeBallStruct, logSizeBallStruct.ball, lt_one_iff, mem_product, pairSet
-/
lemma edist_le_of_mem_pairSet (ha : 1 < a) (hJ_card : #J <= a ^ n) {s t : T}
    (h : (s, t) in pairSet J a c) : edist s t <= n * c := by
  obtain ⟨i, hiJ, h'⟩ : exists i < #J, (s, t) in pairSetSeq J a c i := by simpa [pairSet] using h
  have hJ : J.Nonempty := Finset.card_pos.mp (Nat.zero_lt_of_lt hiJ)
  wlog! hn : 1 <= n
  · suffices s = t by simp [this]
    simp only [Nat.lt_one_iff.mp hn, pow_zero, Nat.cast_le_one] at hJ_card
    have ⟨hs, ht⟩ := Finset.mem_product.mp (pairSet_subset h)
    exact Finset.card_le_one_iff.mp hJ_card hs ht
  simp only [pairSetSeq, hJ, ↓reduceDIte, logSizeBallStruct.ball, Finset.product_eq_sprod,
    Finset.singleton_product, Finset.mem_map, Finset.mem_filter, Function.Embedding.coeFn_mk,
    Prod.mk.injEq, exists_eq_right_right] at h'
  obtain ⟨⟨ht, hdist⟩, rfl⟩ := h'
  grw [hdist, radius_logSizeBallSeq_le hJ ha hn hJ_card i]

/--
lemma `iSup_edist_pairSet` / 引理 `iSup_edist_pairSet`

English:
lemma iSup_edist_pairSet
  given: {E : Type*} [PseudoEMetricSpace E] (ha : 1 < a) (f : T -> E)
  proof: by
  rw [iSup_le_iff]; rintro ⟨s, hs⟩
  rw [iSup_le_iff]; rintro ⟨⟨t, ht⟩, hst⟩
  have hJ : J.Nonempty := ⟨s, hs⟩
  let P (l : Nat) := s in (logSizeBallSeq J hJ a c l).finset ∧ t in (logSizeBallSeq J hJ a c l).finset
  let l := Nat.findGreatest P (#J - 1)
  obtain ⟨hsV, htV⟩ : P l := by
    apply Na

中文:
引理 iSup_edist_pairSet
  条件: {E : 类型} [PseudoEMetricSpace E] (ha : 1 < a) (f : T -> E)
  证明: by
  rw [iSup_le_iff]; rintro ⟨s, hs⟩
  rw [iSup_le_iff]; rintro ⟨⟨t, ht⟩, hst⟩
  have hJ : J.Nonempty := ⟨s, hs⟩
  let P (l : Nat) := s in (logSizeBallSeq J hJ a c l).finset ∧ t in (logSizeBallSeq J hJ a c l).finset
  let l := Nat.findGreatest P (#J - 1)
  obtain ⟨hsV, htV⟩ : P l := by
    apply Na

Depends on / 依赖: J.Nonempty, Nat.findGreatest, Nat.findGreatest_spec, Nonempty, findGreatest, findGreatest_spec, finset, finset_logSizeBallSeq_zero, generalizing, iSup_le_iff, logSizeBallSeq, zero_le
-/
lemma iSup_edist_pairSet {E : Type*} [PseudoEMetricSpace E] (ha : 1 < a) (f : T -> E) :
    ⨆ (s : J) (t : { t : J // edist s t <= c}), edist (f s) (f t)
        <= 2 * ⨆ p : pairSet J a c, edist (f p.1.1) (f p.1.2) := by
  rw [iSup_le_iff]; rintro ⟨s, hs⟩
  rw [iSup_le_iff]; rintro ⟨⟨t, ht⟩, hst⟩
  have hJ : J.Nonempty := ⟨s, hs⟩
  let P (l : Nat) := s in (logSizeBallSeq J hJ a c l).finset ∧ t in (logSizeBallSeq J hJ a c l).finset
  let l := Nat.findGreatest P (#J - 1)
  obtain ⟨hsV, htV⟩ : P l := by
    apply Nat.findGreatest_spec zero_le
    simpa [P, finset_logSizeBallSeq_zero] using ⟨hs, ht⟩
  wlog h : s ∉ (logSizeBallSeq J hJ a c (l + 1)).finset generalizing s t
  · have h' : t ∉ (logSizeBallSeq J hJ a c (l + 1)).finset := by
      have hl : l < #J - 1 := by
        by_contra hl
        simp only [not_lt, tsub_le_iff_right] at hl
        have hlJ : l + 1 = #J := by
          refine Nat.le_antisymm_iff.mpr ⟨?_, hl⟩
          dsimp [l]
          grw [← Nat.sub_add_cancel <| Order.one_le_iff_pos.mpr (Finset.card_pos.mpr hJ),
            Nat.findGreatest_le]
          rfl
        apply h
        suffices h_emp : (logSizeBallSeq J hJ a c (l + 1)).finset = ∅ from by simp [h_emp]
        rw [← Finset.card_eq_zero]; rw [← Nat.le_zero]; rw [← Nat.sub_self #J]; rw [hlJ]
        apply card_finset_logSizeBallSeq_le
      simp only [Decidable.not_not] at h
      have hP := Nat.findGreatest_is_greatest (lt_add_one l) (Nat.add_one_le_of_lt hl)
      simpa [P, h] using hP
    have hts : edist t s <= c := by rw [edist_comm]; exact hst
    rw [edist_comm]
    have hP : P = (fun l =>
      t in (logSizeBallSeq J hJ a c l).finset ∧ s in (logSizeBallSeq J hJ a c l).finset) := by
        ext; simp [P, and_comm]
    simp only [hP, l] at htV hsV h'
    exact this t ht s hs hts htV hsV h'
  simp only [finset_logSizeBallSeq_add_one, logSizeBallStruct.smallBall, Finset.mem_sdiff, hsV,
    Finset.mem_filter, true_and, not_le, not_lt] at h
  have hsB : s in (logSizeBallSeq J hJ a c l).ball c := by
    simp only [logSizeBallStruct.ball, Finset.mem_filter, hsV, true_and]
    grw [h, tsub_le_self]
  have htB : t in (logSizeBallSeq J hJ a c l).ball c := by
    simp only [logSizeBallStruct.ball, Finset.mem_filter, htV, true_and]
    apply le_trans (edist_triangle _ s _)
    apply le_of_le_of_eq (add_le_add h hst)
    nth_rw 3 [← one_mul c]
    rw [← add_mul]
    congr
    rw [ENNReal.sub_add_eq_add_sub _ (ENNReal.one_ne_top)]; rw [ENNReal.add_sub_cancel_right (ENNReal.one_ne_top)]
    rw [← Nat.cast_one]
    gcongr
    exact one_le_radius_logSizeBallSeq hJ ha l
  have hsP : ((logSizeBallSeq J hJ a c l).point, s) in pairSetSeq J a c l := by
    simp [pairSetSeq, hJ, hsB]
  have htP : ((logSizeBallSeq J hJ a c l).point, t) in pairSetSeq J a c l := by
    simp [pairSetSeq, hJ, htB]
  have sup_bound {x y : T} (hxy : (x, y) in pairSetSeq J a c l) :
    edist (f x) (f y) <= ⨆ p : pairSet J a c, edist (f p.1.1) (f p.1.2) := by
    simp only [iSup_subtype]
    apply le_iSup_of_le (i := (x, y))
    apply le_iSup_of_le
    · exact le_rfl
    refine Finset.mem_biUnion.mpr ⟨l, ?_, hxy⟩
refine Finset.mem_range.mpr lt_of_le_of_lt (Nat.findGreatest_le (#J - 1)) ?_
    exact Nat.sub_lt (Finset.card_pos.mpr hJ) zero_lt_one
  rw [two_mul]
  apply le_trans (edist_triangle _ (f (logSizeBallSeq J hJ a c l).point) _)
  rw [edist_comm]
  apply add_le_add (sup_bound hsP) (sup_bound htP)

end PairReduction

open PairReduction in
/--
theorem `EMetric.pair_reduction` / 定理 `EMetric.pair_reduction`

English:
theorem EMetric.pair_reduction
  proof: by
  classical
  rcases le_or_gt a 1 with ha1 | ha1
  · rcases isEmpty_or_nonempty J with hJ | hJ
    · simp only [Finset.isEmpty_coe_sort] at hJ
      simp [hJ]
    obtain ⟨x₀, rfl⟩ : exists x₀, J = {x₀} := by
      rw [← Finset.card_eq_one]
      refine le_antisymm ?_ ?_
      · suffices (#J : ENN

中文:
定理 EMetric.pair_reduction
  证明: by
  classical
  rcases le_or_gt a 1 with ha1 | ha1
  · rcases isEmpty_or_nonempty J with hJ | hJ
    · simp only [Finset.isEmpty_coe_sort] at hJ
      simp [hJ]
    obtain ⟨x₀, rfl⟩ : exists x₀, J = {x₀} := by
      rw [← Finset.card_eq_one]
      refine le_antisymm ?_ ?_
      · suffices (#J : ENN

Depends on / 依赖: ENNReal, ENNReal.pow_le_pow_left, Finset, Finset.card_eq_one, Finset.isEmpty_coe_sort, Finset.nonempty_coe_sort, Finset.one_le_card, card_eq_one, card_pairSet_le, classical, conv_rhs, hJ_card, hJ_card.trans, isEmpty_coe_sort, isEmpty_or_nonempty, le_antisymm, le_or_gt, nonempty_coe_sort, one_le_card, one_pow
-/
theorem EMetric.pair_reduction
    (hJ_card : #J <= a ^ n) (c : Real>=0∞) (E : Type*) [PseudoEMetricSpace E] :
    exists K : Finset (T × T), K subseteq J ×ˢ J
      ∧ #K <= a * #J
      ∧ (forall s t, (s, t) in K -> edist s t <= n * c)
      ∧ (forall f : T -> E,
        ⨆ (s : J) (t : { t : J // edist s t <= c}), edist (f s) (f t)
        <= 2 * ⨆ p : K, edist (f p.1.1) (f p.1.2)) := by
  classical
  rcases le_or_gt a 1 with ha1 | ha1
  · rcases isEmpty_or_nonempty J with hJ | hJ
    · simp only [Finset.isEmpty_coe_sort] at hJ
      simp [hJ]
    obtain ⟨x₀, rfl⟩ : exists x₀, J = {x₀} := by
      rw [← Finset.card_eq_one]
      refine le_antisymm ?_ ?_
      · suffices (#J : ENNReal) <= 1 by norm_cast at this
        refine hJ_card.trans ?_
        conv_rhs => rw [← one_pow n]
        exact ENNReal.pow_le_pow_left ha1
      · rwa [Finset.one_le_card, ← Finset.nonempty_coe_sort]
    simp_all
  · exact ⟨pairSet J a c, pairSet_subset, card_pairSet_le ha1,
      fun _ _ => edist_le_of_mem_pairSet ha1 hJ_card, iSup_edist_pairSet ha1⟩
