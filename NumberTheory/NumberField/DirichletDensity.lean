/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Riccardo Brasca, Xavier Roblot
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
# Dirichlet density of a set of prime ideals

Let `K` be a number field. Given a set `S` of nonzero prime ideals of `𝓞 K`, its Dirichlet
density is
$$
\delta(S) = \lim_{s \to 1^+}
  \frac{\sum_{\mathfrak p \in S} \operatorname{N} \mathfrak p^{-s}}
    {\sum_{\mathfrak p} \operatorname{N} \mathfrak p^{-s}},
$$
when this limit exists. The sum in the denominator runs over all nonzero prime ideals of `𝓞 K`.

This is captured by the predicate `HasDirichletDensity S δ`, stating that the ratio tends to `δ`,
and by the definition `dirichletDensity S`, the density as a real number (with junk value `0` when
it does not exist).

## Main results

* `NumberField.primeIdealZetaSum_le_card_of_finite` — for a finite `S`, the partial sum is bounded
  above by the number of elements of `S`.
* `NumberField.hasDirichletDensity_empty` — the empty set has Dirichlet density `0`.
* `NumberField.dirichletDensity_nonneg` — the Dirichlet density is nonnegative.
* `NumberField.dirichletDensity_le_one` — the Dirichlet density is at most `1`.

-/

public section

noncomputable section

open Filter IsDedekindDomain Topology Set

namespace NumberField.Set

open NumberField

variable {K : Type*} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))

/--
Definition of `primeIdealZetaSum` / `primeIdealZetaSum` 的定义

English:
definition primeIdealZetaSum
  signature: (S : Set (HeightOneSpectrum (𝓞 K))) (s : Real)
  body: ∑' 𝔭 : S, (Ideal.absNorm 𝔭.1.asIdeal : Real) ^ (-s)

中文:
定义 primeIdealZetaSum
  签名: (S : Set (HeightOneSpectrum (𝓞 K))) (s : 实数)
  定义体: ∑' 𝔭 : S, (Ideal.absNorm 𝔭.1.asIdeal : Real) ^ (-s)

Depends on / 依赖: Ideal.absNorm, absNorm, asIdeal
-/
def primeIdealZetaSum (S : Set (HeightOneSpectrum (𝓞 K))) (s : Real) : Real :=
  ∑' 𝔭 : S, (Ideal.absNorm 𝔭.1.asIdeal : Real) ^ (-s)

/--
theorem `primeIdealZetaSum_def` / 定理 `primeIdealZetaSum_def`

English:
theorem primeIdealZetaSum_def
  given: (s : Real)
  proof: by rfl

中文:
定理 primeIdealZetaSum_def
  条件: (s : 实数)
  证明: by rfl
-/
theorem primeIdealZetaSum_def (s : Real) :
    S.primeIdealZetaSum s = ∑' 𝔭 : S, (Ideal.absNorm 𝔭.1.asIdeal : Real) ^ (-s) := by rfl

/--
theorem `primeIdealZetaSum_nonneg` / 定理 `primeIdealZetaSum_nonneg`

English:
theorem primeIdealZetaSum_nonneg
  given: (s : Real)
  proof: tsum_nonneg fun _ => by positivity

中文:
定理 primeIdealZetaSum_nonneg
  条件: (s : 实数)
  证明: tsum_nonneg fun _ => by positivity

Depends on / 依赖: tsum_nonneg
-/
theorem primeIdealZetaSum_nonneg (s : Real) :
    0 <= S.primeIdealZetaSum s :=
  tsum_nonneg fun _ => by positivity

variable {S} in
/--
theorem `primeIdealZetaSum_le_card_of_finite` / 定理 `primeIdealZetaSum_le_card_of_finite`

English:
theorem primeIdealZetaSum_le_card_of_finite
  given: (hS : S.Finite) {s : Real} (hs : 0 <= s)
  proof: by
  replace hS := hS.to_subtype
  grw [primeIdealZetaSum_def, Real.rpow_le_one_of_one_le_of_nonpos] <;>
  simp [Summable.of_finite, Nat.one_le_iff_ne_zero,
    Ideal.absNorm_eq_zero_iff, hs, HeightOneSpectrum.ne_bot]

中文:
定理 primeIdealZetaSum_le_card_of_finite
  条件: (hS : S.Finite) {s : 实数} (hs : 0 <= s)
  证明: by
  replace hS := hS.to_subtype
  grw [primeIdealZetaSum_def, Real.rpow_le_one_of_one_le_of_nonpos] <;>
  simp [Summable.of_finite, Nat.one_le_iff_ne_zero,
    Ideal.absNorm_eq_zero_iff, hs, HeightOneSpectrum.ne_bot]

Depends on / 依赖: HeightOneSpectrum, HeightOneSpectrum.ne_bot, Ideal.absNorm_eq_zero_iff, Nat.one_le_iff_ne_zero, Real.rpow_le_one_of_one_le_of_nonpos, Summable, Summable.of_finite, absNorm_eq_zero_iff, hS.to_subtype, ne_bot, of_finite, one_le_iff_ne_zero, primeIdealZetaSum_def, replace, rpow_le_one_of_one_le_of_nonpos, to_subtype
-/
theorem primeIdealZetaSum_le_card_of_finite (hS : S.Finite) {s : Real} (hs : 0 <= s) :
    S.primeIdealZetaSum s <= S.ncard := by
  replace hS := hS.to_subtype
  grw [primeIdealZetaSum_def, Real.rpow_le_one_of_one_le_of_nonpos] <;>
  simp [Summable.of_finite, Nat.one_le_iff_ne_zero,
    Ideal.absNorm_eq_zero_iff, hs, HeightOneSpectrum.ne_bot]

/--
Definition of `HasDirichletDensity` / `HasDirichletDensity` 的定义

English:
definition HasDirichletDensity
  signature: (δ : Real)
  body: Tendsto (fun s : Real => S.primeIdealZetaSum s /
    primeIdealZetaSum (univ : Set (HeightOneSpectrum (𝓞 K))) s) (𝓝[>] 1) (𝓝 δ)

中文:
定义 HasDirichletDensity
  签名: (δ : 实数)
  定义体: Tendsto (fun s : Real => S.primeIdealZetaSum s /
    primeIdealZetaSum (univ : Set (HeightOneSpectrum (𝓞 K))) s) (𝓝[>] 1) (𝓝 δ)

Depends on / 依赖: HeightOneSpectrum, S.primeIdealZetaSum, Tendsto, primeIdealZetaSum
-/
def HasDirichletDensity (δ : Real) : Prop :=
  Tendsto (fun s : Real => S.primeIdealZetaSum s /
    primeIdealZetaSum (univ : Set (HeightOneSpectrum (𝓞 K))) s) (𝓝[>] 1) (𝓝 δ)

open scoped Classical in
/--
Definition of `dirichletDensity` / `dirichletDensity` 的定义

English:
definition dirichletDensity
  signature: : Real
  body: if h : exists δ, S.HasDirichletDensity δ then h.choose else 0

中文:
定义 dirichletDensity
  签名: : 实数
  定义体: if h : exists δ, S.HasDirichletDensity δ then h.choose else 0

Depends on / 依赖: HasDirichletDensity, S.HasDirichletDensity, h.choose
-/
def dirichletDensity : Real :=
  if h : exists δ, S.HasDirichletDensity δ then h.choose else 0

variable {S}

/--
theorem `dirichletDensity_eq_zero_of_not_hasDirichletDensity` / 定理 `dirichletDensity_eq_zero_of_not_hasDirichletDensity`

English:
theorem dirichletDensity_eq_zero_of_not_hasDirichletDensity
  proof: by
  rw [dirichletDensity]; rw [dif_neg (not_exists.mpr h)]

中文:
定理 dirichletDensity_eq_zero_of_not_hasDirichletDensity
  证明: by
  rw [dirichletDensity]; rw [dif_neg (not_exists.mpr h)]

Depends on / 依赖: dif_neg, dirichletDensity, not_exists, not_exists.mpr
-/
theorem dirichletDensity_eq_zero_of_not_hasDirichletDensity
    (h : forall δ, ¬ S.HasDirichletDensity δ) : S.dirichletDensity = 0 := by
  rw [dirichletDensity]; rw [dif_neg (not_exists.mpr h)]

/--
theorem `HasDirichletDensity.dirichletDensity_eq` / 定理 `HasDirichletDensity.dirichletDensity_eq`

English:
theorem HasDirichletDensity.dirichletDensity_eq
  given: {δ : Real} (h : S.HasDirichletDensity δ)
  proof: by
  rw [dirichletDensity]; rw [dif_pos ⟨δ]; rw [h⟩]; rw [tendsto_nhds_unique (Exists.choose_spec ⟨δ]; rw [h⟩) h]

中文:
定理 HasDirichletDensity.dirichletDensity_eq
  条件: {δ : 实数} (h : S.HasDirichletDensity δ)
  证明: by
  rw [dirichletDensity]; rw [dif_pos ⟨δ]; rw [h⟩]; rw [tendsto_nhds_unique (Exists.choose_spec ⟨δ]; rw [h⟩) h]

Depends on / 依赖: Exists, Exists.choose_spec, choose_spec, dif_pos, dirichletDensity, tendsto_nhds_unique
-/
theorem HasDirichletDensity.dirichletDensity_eq {δ : Real} (h : S.HasDirichletDensity δ) :
    S.dirichletDensity = δ := by
  rw [dirichletDensity]; rw [dif_pos ⟨δ]; rw [h⟩]; rw [tendsto_nhds_unique (Exists.choose_spec ⟨δ]; rw [h⟩) h]

/--
theorem `hasDirichletDensity_empty` / 定理 `hasDirichletDensity_empty`

English:
theorem hasDirichletDensity_empty
  proof: by
  simp [HasDirichletDensity, primeIdealZetaSum_def]

中文:
定理 hasDirichletDensity_empty
  证明: by
  simp [HasDirichletDensity, primeIdealZetaSum_def]

Depends on / 依赖: HasDirichletDensity, primeIdealZetaSum_def
-/
theorem hasDirichletDensity_empty :
    HasDirichletDensity (∅ : Set (HeightOneSpectrum (𝓞 K))) 0 := by
  simp [HasDirichletDensity, primeIdealZetaSum_def]

/-- The Dirichlet density of the empty set is `0`. -/
@[simp]
/--
theorem `dirichletDensity_empty` / 定理 `dirichletDensity_empty`

English:
theorem dirichletDensity_empty
  proof: hasDirichletDensity_empty.dirichletDensity_eq

中文:
定理 dirichletDensity_empty
  证明: hasDirichletDensity_empty.dirichletDensity_eq

Depends on / 依赖: dirichletDensity_eq, hasDirichletDensity_empty, hasDirichletDensity_empty.dirichletDensity_eq
-/
theorem dirichletDensity_empty :
    dirichletDensity (∅ : Set (HeightOneSpectrum (𝓞 K))) = 0 :=
  hasDirichletDensity_empty.dirichletDensity_eq

/--
theorem `HasDirichletDensity.nonneg` / 定理 `HasDirichletDensity.nonneg`

English:
theorem HasDirichletDensity.nonneg
  given: {δ : Real} (h : S.HasDirichletDensity δ)
  proof: ge_of_tendsto h Eventually.of_forall fun s =>
    div_nonneg (S.primeIdealZetaSum_nonneg s) (univ.primeIdealZetaSum_nonneg s)

中文:
定理 HasDirichletDensity.nonneg
  条件: {δ : 实数} (h : S.HasDirichletDensity δ)
  证明: ge_of_tendsto h Eventually.of_forall fun s =>
    div_nonneg (S.primeIdealZetaSum_nonneg s) (univ.primeIdealZetaSum_nonneg s)

Depends on / 依赖: Eventually, Eventually.of_forall, S.primeIdealZetaSum_nonneg, div_nonneg, ge_of_tendsto, of_forall, primeIdealZetaSum_nonneg, univ.primeIdealZetaSum_nonneg
-/
theorem HasDirichletDensity.nonneg {δ : Real} (h : S.HasDirichletDensity δ) :
    0 <= δ :=
ge_of_tendsto h Eventually.of_forall fun s =>
    div_nonneg (S.primeIdealZetaSum_nonneg s) (univ.primeIdealZetaSum_nonneg s)

variable (S) in
/--
theorem `dirichletDensity_nonneg` / 定理 `dirichletDensity_nonneg`

English:
theorem dirichletDensity_nonneg
  statement: 0 <= S.dirichletDensity
  proof: by
  rw [dirichletDensity]
  split_ifs with h
  · exact h.choose_spec.nonneg
  · exact le_rfl

中文:
定理 dirichletDensity_nonneg
  结论: 0 <= S.dirichletDensity
  证明: by
  rw [dirichletDensity]
  split_ifs with h
  · exact h.choose_spec.nonneg
  · exact le_rfl

Depends on / 依赖: choose_spec, dirichletDensity, h.choose_spec.nonneg, le_rfl, nonneg, split_ifs
-/
theorem dirichletDensity_nonneg : 0 <= S.dirichletDensity := by
  rw [dirichletDensity]
  split_ifs with h
  · exact h.choose_spec.nonneg
  · exact le_rfl

/--
theorem `HasDirichletDensity.le_one` / 定理 `HasDirichletDensity.le_one`

English:
theorem HasDirichletDensity.le_one
  given: {δ : Real} (h : S.HasDirichletDensity δ)
  proof: by
  refine le_of_tendsto h (Eventually.of_forall fun s => ?_)
  rw [primeIdealZetaSum_def]; rw [primeIdealZetaSum_def]; rw [tsum_univ fun 𝔭 : HeightOneSpectrum (𝓞 K) => (𝔭.asIdeal.absNorm : Real) ^ (-s)]
  by_cases hs : Summable fun 𝔭 : HeightOneSpectrum (𝓞 K) => (𝔭.asIdeal.absNorm : Real) ^ (-s)
 

中文:
定理 HasDirichletDensity.le_one
  条件: {δ : 实数} (h : S.HasDirichletDensity δ)
  证明: by
  refine le_of_tendsto h (Eventually.of_forall fun s => ?_)
  rw [primeIdealZetaSum_def]; rw [primeIdealZetaSum_def]; rw [tsum_univ fun 𝔭 : HeightOneSpectrum (𝓞 K) => (𝔭.asIdeal.absNorm : Real) ^ (-s)]
  by_cases hs : Summable fun 𝔭 : HeightOneSpectrum (𝓞 K) => (𝔭.asIdeal.absNorm : Real) ^ (-s)
 

Depends on / 依赖: Eventually, Eventually.of_forall, HeightOneSpectrum, Summable, absNorm, asIdeal, asIdeal.absNorm, div_zero, hs.tsum_subtype_le, le_of_tendsto, of_forall, primeIdealZetaSum_def, tsum_eq_zero_of_not_summable, tsum_nonneg, tsum_subtype_le, tsum_univ, zero_le_one
-/
theorem HasDirichletDensity.le_one {δ : Real} (h : S.HasDirichletDensity δ) :
    δ <= 1 := by
  refine le_of_tendsto h (Eventually.of_forall fun s => ?_)
  rw [primeIdealZetaSum_def]; rw [primeIdealZetaSum_def]; rw [tsum_univ fun 𝔭 : HeightOneSpectrum (𝓞 K) => (𝔭.asIdeal.absNorm : Real) ^ (-s)]
  by_cases hs : Summable fun 𝔭 : HeightOneSpectrum (𝓞 K) => (𝔭.asIdeal.absNorm : Real) ^ (-s)
  · exact div_le_one_of_le₀ (hs.tsum_subtype_le _ S (fun _ => by positivity))
      (tsum_nonneg fun _ => by positivity)
  · grw [tsum_eq_zero_of_not_summable hs, div_zero, zero_le_one]

variable (S) in
/--
theorem `dirichletDensity_le_one` / 定理 `dirichletDensity_le_one`

English:
theorem dirichletDensity_le_one
  statement: S.dirichletDensity <= 1
  proof: by
  rw [dirichletDensity]
  split_ifs with h
  · exact h.choose_spec.le_one
  · exact zero_le_one

中文:
定理 dirichletDensity_le_one
  结论: S.dirichletDensity <= 1
  证明: by
  rw [dirichletDensity]
  split_ifs with h
  · exact h.choose_spec.le_one
  · exact zero_le_one

Depends on / 依赖: choose_spec, dirichletDensity, h.choose_spec.le_one, le_one, split_ifs, zero_le_one
-/
theorem dirichletDensity_le_one : S.dirichletDensity <= 1 := by
  rw [dirichletDensity]
  split_ifs with h
  · exact h.choose_spec.le_one
  · exact zero_le_one

end NumberField.Set
