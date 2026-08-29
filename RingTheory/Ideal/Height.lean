/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wanyi He, Jiedong Jiang, Jingting Wang, Andrew Yang, Shouxin Zhang
-/
module

public import Mathlib.Algebra.Module.SpanRank
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# The Height of an Ideal

In this file, we define the height of a prime ideal and the height of an ideal.

## Main definitions

* `Ideal.height` : The height of an ideal. We defined it as the infimum of the `primeHeight` of the
  minimal prime ideals of I.

-/

public section

variable {R : Type*} [CommRing R] (I : Ideal R)

open Ideal

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def Ideal.primeHeight [hI : I.IsPrime]
  body: Order.height (⟨I, hI⟩ : PrimeSpectrum R)

中文:
定义 noncomputable
  签名: def 理想.primeHeight [hI : I.是素]
  定义体: Order.height (⟨I, hI⟩ : PrimeSpectrum R)
-/
private noncomputable def Ideal.primeHeight [hI : I.IsPrime] : Nat∞ :=
  Order.height (⟨I, hI⟩ : PrimeSpectrum R)

/--
Definition of `Ideal.height` / `Ideal.height` 的定义

English:
definition Ideal.height
  signature: : Nat∞
  body: ⨅ J in I.minimalPrimes, @Ideal.primeHeight _ _ J ‹J in I.minimalPrimes›.isPrime

中文:
定义 理想.height
  签名: : 自然数∞
  定义体: ⨅ J in I.minimalPrimes, @Ideal.primeHeight _ _ J ‹J in I.minimalPrimes›.isPrime

Depends on / 依赖: I.minimalPrimes, Ideal.primeHeight, isPrime, minimalPrimes, primeHeight
-/
noncomputable def Ideal.height : Nat∞ :=
  ⨅ J in I.minimalPrimes, @Ideal.primeHeight _ _ J ‹J in I.minimalPrimes›.isPrime

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `Ideal.height_eq_primeHeight` / 引理 `Ideal.height_eq_primeHeight`

English:
lemma Ideal.height_eq_primeHeight
  given: [I.IsPrime]
  statement: I.height = I.primeHeight
  proof: by
  simp [height, primeHeight, Ideal.minimalPrimes_eq_subsingleton_self]

中文:
引理 理想.height_eq_primeHeight
  条件: [I.是素]
  结论: I.height = I.primeHeight
  证明: by
  simp [height, primeHeight, Ideal.minimalPrimes_eq_subsingleton_self]
-/
private lemma Ideal.height_eq_primeHeight [I.IsPrime] : I.height = I.primeHeight := by
  simp [height, primeHeight, Ideal.minimalPrimes_eq_subsingleton_self]

/--
lemma `PrimeSpectrum.height_eq_orderHeight` / 引理 `PrimeSpectrum.height_eq_orderHeight`

English:
lemma PrimeSpectrum.height_eq_orderHeight
  given: (p : PrimeSpectrum R)
  proof: p.asIdeal.height_eq_primeHeight

中文:
引理 素谱.height_eq_orderHeight
  条件: (p : 素谱 R)
  证明: p.asIdeal.height_eq_primeHeight

Depends on / 依赖: asIdeal, height_eq_primeHeight, p.asIdeal.height_eq_primeHeight
-/
lemma PrimeSpectrum.height_eq_orderHeight (p : PrimeSpectrum R) :
    p.asIdeal.height = Order.height p :=
  p.asIdeal.height_eq_primeHeight

/--
lemma `Ideal.height_eq_inf_minimalPrimes` / 引理 `Ideal.height_eq_inf_minimalPrimes`

English:
lemma Ideal.height_eq_inf_minimalPrimes
  statement: I.height = ⨅ J in I.minimalPrimes, J.height
  proof: by
  apply iInf_congr (fun p => iInf_congr fun hp => ?_)
  have := hp.isPrime
  exact (Ideal.height_eq_primeHeight _).symm

中文:
引理 理想.height_eq_inf_minimalPrimes
  结论: I.height = ⨅ J in I.minimalPrimes, J.height
  证明: by
  apply iInf_congr (fun p => iInf_congr fun hp => ?_)
  have := hp.isPrime
  exact (Ideal.height_eq_primeHeight _).symm

Depends on / 依赖: Ideal.height_eq_primeHeight, height_eq_primeHeight, hp.isPrime, iInf_congr, isPrime
-/
lemma Ideal.height_eq_inf_minimalPrimes : I.height = ⨅ J in I.minimalPrimes, J.height := by
  apply iInf_congr (fun p => iInf_congr fun hp => ?_)
  have := hp.isPrime
  exact (Ideal.height_eq_primeHeight _).symm

/--
lemma `Ideal.exists_isPrime_height_eq` / 引理 `Ideal.exists_isPrime_height_eq`

English:
lemma Ideal.exists_isPrime_height_eq
  given: {I : Ideal R} {n : Nat} (hI : I.height = n)
  proof: by
  simp only [Ideal.height, ENat.iInf_eq_natCast_iff] at hI
  rcases hI with ⟨⟨p, ⟨⟨⟨hpp, hIp⟩, _⟩, h⟩, -⟩, -⟩
  exact ⟨p, hpp, hIp, h ▸ p.height_eq_primeHeight⟩

中文:
引理 理想.存在_isPrime_height_eq
  条件: {I : 理想 R} {n : 自然数} (hI : I.height = n)
  证明: by
  simp only [Ideal.height, ENat.iInf_eq_natCast_iff] at hI
  rcases hI with ⟨⟨p, ⟨⟨⟨hpp, hIp⟩, _⟩, h⟩, -⟩, -⟩
  exact ⟨p, hpp, hIp, h ▸ p.height_eq_primeHeight⟩

Depends on / 依赖: ENat.iInf_eq_natCast_iff, Ideal.height, height, height_eq_primeHeight, iInf_eq_natCast_iff, p.height_eq_primeHeight
-/
lemma Ideal.exists_isPrime_height_eq {I : Ideal R} {n : Nat} (hI : I.height = n) :
    exists (p : Ideal R) (_ : p.IsPrime) (_ : I <= p), p.height = n := by
  simp only [Ideal.height, ENat.iInf_eq_natCast_iff] at hI
  rcases hI with ⟨⟨p, ⟨⟨⟨hpp, hIp⟩, _⟩, h⟩, -⟩, -⟩
  exact ⟨p, hpp, hIp, h ▸ p.height_eq_primeHeight⟩

/-- An ideal has finite height if it is either the unit ideal or its height is finite.
We include the unit ideal in order to have the instance `IsNoetherianRing R → FiniteHeight I`. -/
@[mk_iff]
/--
Definition of `Ideal.FiniteHeight` / `Ideal.FiniteHeight` 的定义

English:
class Ideal.FiniteHeight
  parameters: : Prop where
  axioms and operations (1):
    - eq_top_or_height_ne_top : I = ⊤ ∨ I.height != ⊤

中文:
类 理想.FiniteHeight
  参数: : 命题 where
  公理与运算 (1 个):
    - eq_top_or_height_ne_top : I = ⊤ ∨ I.height != ⊤
-/
class Ideal.FiniteHeight : Prop where
  eq_top_or_height_ne_top : I = ⊤ ∨ I.height != ⊤

/--
lemma `Ideal.finiteHeight_iff_lt` / 引理 `Ideal.finiteHeight_iff_lt`

English:
lemma Ideal.finiteHeight_iff_lt
  given: {I : Ideal R}
  proof: by
  rw [Ideal.finiteHeight_iff]; rw [lt_top_iff_ne_top]

中文:
引理 理想.finiteHeight_iff_lt
  条件: {I : 理想 R}
  证明: by
  rw [Ideal.finiteHeight_iff]; rw [lt_top_iff_ne_top]

Depends on / 依赖: Ideal.finiteHeight_iff, finiteHeight_iff, lt_top_iff_ne_top
-/
lemma Ideal.finiteHeight_iff_lt {I : Ideal R} :
    Ideal.FiniteHeight I ↔ I = ⊤ ∨ I.height < ⊤ := by
  rw [Ideal.finiteHeight_iff]; rw [lt_top_iff_ne_top]

/--
lemma `Ideal.height_ne_top` / 引理 `Ideal.height_ne_top`

English:
lemma Ideal.height_ne_top
  given: {I : Ideal R} (hI : I != ⊤) [I.FiniteHeight]
  proof: (‹I.FiniteHeight›.eq_top_or_height_ne_top).resolve_left hI

中文:
引理 理想.height_ne_top
  条件: {I : 理想 R} (hI : I != ⊤) [I.FiniteHeight]
  证明: (‹I.FiniteHeight›.eq_top_or_height_ne_top).resolve_left hI

Depends on / 依赖: FiniteHeight, I.FiniteHeight, eq_top_or_height_ne_top, resolve_left
-/
lemma Ideal.height_ne_top {I : Ideal R} (hI : I != ⊤) [I.FiniteHeight] :
    I.height != ⊤ :=
  (‹I.FiniteHeight›.eq_top_or_height_ne_top).resolve_left hI

/--
lemma `Ideal.height_lt_top` / 引理 `Ideal.height_lt_top`

English:
lemma Ideal.height_lt_top
  given: {I : Ideal R} (hI : I != ⊤) [I.FiniteHeight]
  proof: (Ideal.height_ne_top hI).lt_top

中文:
引理 理想.height_lt_top
  条件: {I : 理想 R} (hI : I != ⊤) [I.FiniteHeight]
  证明: (Ideal.height_ne_top hI).lt_top

Depends on / 依赖: Ideal.height_ne_top, height_ne_top, lt_top
-/
lemma Ideal.height_lt_top {I : Ideal R} (hI : I != ⊤) [I.FiniteHeight] :
    I.height < ⊤ :=
  (Ideal.height_ne_top hI).lt_top

/--
lemma `Ideal.height_ne_top_of_isPrime` / 引理 `Ideal.height_ne_top_of_isPrime`

English:
lemma Ideal.height_ne_top_of_isPrime
  given: {I : Ideal R} [I.FiniteHeight] [I.IsPrime]
  proof: Ideal.height_ne_top ‹I.IsPrime›.ne_top

@[deprecated "Use `Ideal.height_ne_top_of_isPrime` instead." (since := "2026-04-04")]

中文:
引理 理想.height_ne_top_of_isPrime
  条件: {I : 理想 R} [I.FiniteHeight] [I.是素]
  证明: Ideal.height_ne_top ‹I.IsPrime›.ne_top

@[deprecated "Use `Ideal.height_ne_top_of_isPrime` instead." (since := "2026-04-04")]

Depends on / 依赖: I.IsPrime, Ideal.height_ne_top, IsPrime, height_ne_top, ne_top
-/
lemma Ideal.height_ne_top_of_isPrime {I : Ideal R} [I.FiniteHeight] [I.IsPrime] :
    I.height != ⊤ :=
  Ideal.height_ne_top ‹I.IsPrime›.ne_top

@[deprecated "Use `Ideal.height_ne_top_of_isPrime` instead." (since := "2026-04-04")]
/--
lemma `Ideal.primeHeight_ne_top` / 引理 `Ideal.primeHeight_ne_top`

English:
lemma Ideal.primeHeight_ne_top
  given: (I : Ideal R) [I.FiniteHeight] [I.IsPrime]
  proof: by
  rw [← I.height_eq_primeHeight]
  exact Ideal.height_ne_top ‹I.IsPrime›.ne_top

中文:
引理 理想.primeHeight_ne_top
  条件: (I : 理想 R) [I.FiniteHeight] [I.是素]
  证明: by
  rw [← I.height_eq_primeHeight]
  exact Ideal.height_ne_top ‹I.IsPrime›.ne_top
-/
private lemma Ideal.primeHeight_ne_top (I : Ideal R) [I.FiniteHeight] [I.IsPrime] :
    I.primeHeight != ⊤ := by
  rw [← I.height_eq_primeHeight]
  exact Ideal.height_ne_top ‹I.IsPrime›.ne_top

/--
lemma `Ideal.height_lt_top_of_isPrime` / 引理 `Ideal.height_lt_top_of_isPrime`

English:
lemma Ideal.height_lt_top_of_isPrime
  given: {I : Ideal R} [I.FiniteHeight] [I.IsPrime]
  proof: Ideal.height_lt_top ‹I.IsPrime›.ne_top

@[deprecated "Use `Ideal.height_lt_top_of_isPrime` instead." (since := "2026-04-04")]

中文:
引理 理想.height_lt_top_of_isPrime
  条件: {I : 理想 R} [I.FiniteHeight] [I.是素]
  证明: Ideal.height_lt_top ‹I.IsPrime›.ne_top

@[deprecated "Use `Ideal.height_lt_top_of_isPrime` instead." (since := "2026-04-04")]

Depends on / 依赖: I.IsPrime, Ideal.height_lt_top, IsPrime, height_lt_top, ne_top
-/
lemma Ideal.height_lt_top_of_isPrime {I : Ideal R} [I.FiniteHeight] [I.IsPrime] :
    I.height < ⊤ :=
  Ideal.height_lt_top ‹I.IsPrime›.ne_top

@[deprecated "Use `Ideal.height_lt_top_of_isPrime` instead." (since := "2026-04-04")]
/--
lemma `Ideal.primeHeight_lt_top` / 引理 `Ideal.primeHeight_lt_top`

English:
lemma Ideal.primeHeight_lt_top
  given: (I : Ideal R) [I.FiniteHeight] [I.IsPrime]
  proof: by
  rw [← I.height_eq_primeHeight]
  exact Ideal.height_lt_top ‹I.IsPrime›.ne_top

中文:
引理 理想.primeHeight_lt_top
  条件: (I : 理想 R) [I.FiniteHeight] [I.是素]
  证明: by
  rw [← I.height_eq_primeHeight]
  exact Ideal.height_lt_top ‹I.IsPrime›.ne_top
-/
private lemma Ideal.primeHeight_lt_top (I : Ideal R) [I.FiniteHeight] [I.IsPrime] :
    I.primeHeight < ⊤ := by
  rw [← I.height_eq_primeHeight]
  exact Ideal.height_lt_top ‹I.IsPrime›.ne_top

/--
lemma `Ideal.exists_ltSeries_length_eq_height` / 引理 `Ideal.exists_ltSeries_length_eq_height`

English:
lemma Ideal.exists_ltSeries_length_eq_height
  given: (p : Ideal R) [p.IsPrime] [p.FiniteHeight]
  proof: by
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (p.height_ne_top (IsPrime.ne_top ‹_›))
  rw [Ideal.height_eq_primeHeight]; rw [Ideal.primeHeight] at hn ⊢
  obtain ⟨l, last, len⟩ := Order.exists_series_of_height_eq_coe (⟨p, ‹_›⟩ : PrimeSpectrum R) hn.symm
  exact ⟨l, last, len ▸ hn⟩

中文:
引理 理想.存在_ltSeries_length_eq_height
  条件: (p : 理想 R) [p.是素] [p.FiniteHeight]
  证明: by
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (p.height_ne_top (IsPrime.ne_top ‹_›))
  rw [Ideal.height_eq_primeHeight]; rw [Ideal.primeHeight] at hn ⊢
  obtain ⟨l, last, len⟩ := Order.exists_series_of_height_eq_coe (⟨p, ‹_›⟩ : PrimeSpectrum R) hn.symm
  exact ⟨l, last, len ▸ hn⟩

Depends on / 依赖: ENat.ne_top_iff_exists.mp, Ideal.height_eq_primeHeight, Ideal.primeHeight, IsPrime, IsPrime.ne_top, Order.exists_series_of_height_eq_coe, PrimeSpectrum, exists_series_of_height_eq_coe, height_eq_primeHeight, height_ne_top, hn.symm, ne_top, ne_top_iff_exists, p.height_ne_top, primeHeight
-/
lemma Ideal.exists_ltSeries_length_eq_height (p : Ideal R) [p.IsPrime] [p.FiniteHeight] :
    exists (l : LTSeries (PrimeSpectrum R)),
      RelSeries.last l = ⟨p, inferInstance⟩ ∧ l.length = p.height := by
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (p.height_ne_top (IsPrime.ne_top ‹_›))
  rw [Ideal.height_eq_primeHeight]; rw [Ideal.primeHeight] at hn ⊢
  obtain ⟨l, last, len⟩ := Order.exists_series_of_height_eq_coe (⟨p, ‹_›⟩ : PrimeSpectrum R) hn.symm
  exact ⟨l, last, len ▸ hn⟩

/--
lemma `Ideal.height_mono_of_isPrime` / 引理 `Ideal.height_mono_of_isPrime`

English:
lemma Ideal.height_mono_of_isPrime
  given: {I J : Ideal R} [I.IsPrime] [J.IsPrime] (h : I <= J)
  proof: by
  simp only [Ideal.height_eq_primeHeight, Ideal.primeHeight]
  gcongr
  exact h

@[deprecated "Use `Ideal.height_mono_of_isPrime` instead." (since := "2026-04-04")]

中文:
引理 理想.height_mono_of_isPrime
  条件: {I J : 理想 R} [I.是素] [J.是素] (h : I <= J)
  证明: by
  simp only [Ideal.height_eq_primeHeight, Ideal.primeHeight]
  gcongr
  exact h

@[deprecated "Use `Ideal.height_mono_of_isPrime` instead." (since := "2026-04-04")]
-/
private lemma Ideal.height_mono_of_isPrime {I J : Ideal R} [I.IsPrime] [J.IsPrime] (h : I <= J) :
    I.height <= J.height := by
  simp only [Ideal.height_eq_primeHeight, Ideal.primeHeight]
  gcongr
  exact h

@[deprecated "Use `Ideal.height_mono_of_isPrime` instead." (since := "2026-04-04")]
/--
lemma `Ideal.primeHeight_mono` / 引理 `Ideal.primeHeight_mono`

English:
lemma Ideal.primeHeight_mono
  given: {I J : Ideal R} [I.IsPrime] [J.IsPrime] (h : I <= J)
  proof: by
  simpa [Ideal.height_eq_primeHeight] using Ideal.height_mono_of_isPrime h

中文:
引理 理想.primeHeight_mono
  条件: {I J : 理想 R} [I.是素] [J.是素] (h : I <= J)
  证明: by
  simpa [Ideal.height_eq_primeHeight] using Ideal.height_mono_of_isPrime h
-/
private lemma Ideal.primeHeight_mono {I J : Ideal R} [I.IsPrime] [J.IsPrime] (h : I <= J) :
    I.primeHeight <= J.primeHeight := by
  simpa [Ideal.height_eq_primeHeight] using Ideal.height_mono_of_isPrime h

/--
lemma `Ideal.height_add_one_le_of_lt_of_isPrime` / 引理 `Ideal.height_add_one_le_of_lt_of_isPrime`

English:
lemma Ideal.height_add_one_le_of_lt_of_isPrime
  given: {I J : Ideal R} [I.IsPrime] [J.IsPrime] (h : I < J)
  proof: by
  simp only [Ideal.height_eq_primeHeight, Ideal.primeHeight]
  exact Order.height_add_one_le h

@[deprecated "Use `Ideal.height_add_one_le_of_lt_of_isPrime` instead." (since := "2026-04-04")]

中文:
引理 理想.height_add_one_le_of_lt_of_isPrime
  条件: {I J : 理想 R} [I.是素] [J.是素] (h : I < J)
  证明: by
  simp only [Ideal.height_eq_primeHeight, Ideal.primeHeight]
  exact Order.height_add_one_le h

@[deprecated "Use `Ideal.height_add_one_le_of_lt_of_isPrime` instead." (since := "2026-04-04")]

Depends on / 依赖: Ideal.height_eq_primeHeight, Ideal.primeHeight, Order.height_add_one_le, height_add_one_le, height_eq_primeHeight, primeHeight
-/
lemma Ideal.height_add_one_le_of_lt_of_isPrime {I J : Ideal R} [I.IsPrime] [J.IsPrime] (h : I < J) :
    I.height + 1 <= J.height := by
  simp only [Ideal.height_eq_primeHeight, Ideal.primeHeight]
  exact Order.height_add_one_le h

@[deprecated "Use `Ideal.height_add_one_le_of_lt_of_isPrime` instead." (since := "2026-04-04")]
/--
lemma `Ideal.primeHeight_add_one_le_of_lt` / 引理 `Ideal.primeHeight_add_one_le_of_lt`

English:
lemma Ideal.primeHeight_add_one_le_of_lt
  statement: {I J : Ideal R} [I.IsPrime] [J.IsPrime]
  proof: by
  simpa [Ideal.height_eq_primeHeight] using Ideal.height_add_one_le_of_lt_of_isPrime h

@[simp]

中文:
引理 理想.primeHeight_add_one_le_of_lt
  结论: {I J : 理想 R} [I.是素] [J.是素]
  证明: by
  simpa [Ideal.height_eq_primeHeight] using Ideal.height_add_one_le_of_lt_of_isPrime h

@[simp]
-/
private lemma Ideal.primeHeight_add_one_le_of_lt {I J : Ideal R} [I.IsPrime] [J.IsPrime]
    (h : I < J) : I.primeHeight + 1 <= J.primeHeight := by
  simpa [Ideal.height_eq_primeHeight] using Ideal.height_add_one_le_of_lt_of_isPrime h

@[simp]
/--
theorem `Ideal.height_top` / 定理 `Ideal.height_top`

English:
theorem Ideal.height_top
  statement: (⊤ : Ideal R).height = ⊤
  proof: by
  simp [height, minimalPrimes_top]

@[gcongr]

中文:
定理 理想.height_top
  结论: (⊤ : 理想 R).height = ⊤
  证明: by
  simp [height, minimalPrimes_top]

@[gcongr]

Depends on / 依赖: height, minimalPrimes_top
-/
theorem Ideal.height_top : (⊤ : Ideal R).height = ⊤ := by
  simp [height, minimalPrimes_top]

@[gcongr]
/--
theorem `Ideal.height_mono` / 定理 `Ideal.height_mono`

English:
theorem Ideal.height_mono
  given: {I J : Ideal R} (h : I <= J)
  statement: I.height <= J.height
  proof: by
  simp only [I.height_eq_inf_minimalPrimes, J.height_eq_inf_minimalPrimes]
  refine le_iInf₂ (fun p hp => ?_)
  have := hp.isPrime
  obtain ⟨q, hq, e⟩ := Ideal.exists_minimalPrimes_le (h.trans hp.le)
  have := hq.isPrime
  exact (iInf₂_le q hq).trans (Ideal.height_mono_of_isPrime e)

@[gcongr]

中文:
定理 理想.height_mono
  条件: {I J : 理想 R} (h : I <= J)
  结论: I.height <= J.height
  证明: by
  simp only [I.height_eq_inf_minimalPrimes, J.height_eq_inf_minimalPrimes]
  refine le_iInf₂ (fun p hp => ?_)
  have := hp.isPrime
  obtain ⟨q, hq, e⟩ := Ideal.exists_minimalPrimes_le (h.trans hp.le)
  have := hq.isPrime
  exact (iInf₂_le q hq).trans (Ideal.height_mono_of_isPrime e)

@[gcongr]

Depends on / 依赖: I.height_eq_inf_minimalPrimes, Ideal.exists_minimalPrimes_le, Ideal.height_mono_of_isPrime, J.height_eq_inf_minimalPrimes, exists_minimalPrimes_le, h.trans, height_eq_inf_minimalPrimes, height_mono_of_isPrime, hp.isPrime, hp.le, hq.isPrime, isPrime
-/
theorem Ideal.height_mono {I J : Ideal R} (h : I <= J) : I.height <= J.height := by
  simp only [I.height_eq_inf_minimalPrimes, J.height_eq_inf_minimalPrimes]
  refine le_iInf₂ (fun p hp => ?_)
  have := hp.isPrime
  obtain ⟨q, hq, e⟩ := Ideal.exists_minimalPrimes_le (h.trans hp.le)
  have := hq.isPrime
  exact (iInf₂_le q hq).trans (Ideal.height_mono_of_isPrime e)

@[gcongr]
/--
lemma `Ideal.height_strict_mono_of_isPrime` / 引理 `Ideal.height_strict_mono_of_isPrime`

English:
lemma Ideal.height_strict_mono_of_isPrime
  statement: {I J : Ideal R} [I.IsPrime]
  proof: by
  by_cases hJ : J = ⊤
  · grw [hJ, height_top]
    exact I.height_lt_top IsPrime.ne_top'
  · rw [← ENat.add_one_le_iff (I.height_ne_top IsPrime.ne_top'), J.height_eq_inf_minimalPrimes]
    refine le_iInf₂ (fun K hK => ?_)
    have := hK.isPrime
    have : I < K := lt_of_lt_of_le h hK.le
    exact

中文:
引理 理想.height_strict_mono_of_isPrime
  结论: {I J : 理想 R} [I.是素]
  证明: by
  by_cases hJ : J = ⊤
  · grw [hJ, height_top]
    exact I.height_lt_top IsPrime.ne_top'
  · rw [← ENat.add_one_le_iff (I.height_ne_top IsPrime.ne_top'), J.height_eq_inf_minimalPrimes]
    refine le_iInf₂ (fun K hK => ?_)
    have := hK.isPrime
    have : I < K := lt_of_lt_of_le h hK.le
    exact

Depends on / 依赖: ENat.add_one_le_iff, I.height_lt_top, I.height_ne_top, Ideal.height_add_one_le_of_lt_of_isPrime, IsPrime, IsPrime.ne_top, J.height_eq_inf_minimalPrimes, add_one_le_iff, hK.isPrime, hK.le, height_add_one_le_of_lt_of_isPrime, height_eq_inf_minimalPrimes, height_lt_top, height_ne_top, height_top, isPrime, lt_of_lt_of_le, ne_top
-/
lemma Ideal.height_strict_mono_of_isPrime {I J : Ideal R} [I.IsPrime]
    (h : I < J) [I.FiniteHeight] : I.height < J.height := by
  by_cases hJ : J = ⊤
  · grw [hJ, height_top]
    exact I.height_lt_top IsPrime.ne_top'
  · rw [← ENat.add_one_le_iff (I.height_ne_top IsPrime.ne_top'), J.height_eq_inf_minimalPrimes]
    refine le_iInf₂ (fun K hK => ?_)
    have := hK.isPrime
    have : I < K := lt_of_lt_of_le h hK.le
    exact Ideal.height_add_one_le_of_lt_of_isPrime this

/--
lemma `Ideal.height_strict_mono_of_isPrime_of_isPrime` / 引理 `Ideal.height_strict_mono_of_isPrime_of_isPrime`

English:
lemma Ideal.height_strict_mono_of_isPrime_of_isPrime
  statement: {I J : Ideal R} [I.IsPrime] [J.IsPrime]
  proof: by
  have : I.FiniteHeight := I.finiteHeight_iff.mpr
    (Or.inr (lt_of_le_of_lt (Ideal.height_mono h.le) (J.height_lt_top IsPrime.ne_top')).ne)
  exact Ideal.height_strict_mono_of_isPrime h

@[deprecated (since := "2026-04-02")]
alias Ideal.height_strict_mono_of_isPrime_of_is_prime :=
  Ideal.heigh

中文:
引理 理想.height_strict_mono_of_isPrime_of_isPrime
  结论: {I J : 理想 R} [I.是素] [J.是素]
  证明: by
  have : I.FiniteHeight := I.finiteHeight_iff.mpr
    (Or.inr (lt_of_le_of_lt (Ideal.height_mono h.le) (J.height_lt_top IsPrime.ne_top')).ne)
  exact Ideal.height_strict_mono_of_isPrime h

@[deprecated (since := "2026-04-02")]
alias Ideal.height_strict_mono_of_isPrime_of_is_prime :=
  Ideal.heigh

Depends on / 依赖: FiniteHeight, I.FiniteHeight, I.finiteHeight_iff.mpr, Ideal.height_mono, Ideal.height_strict_mono_of_isPrime, IsPrime, IsPrime.ne_top, J.height_lt_top, Or.inr, finiteHeight_iff, h.le, height_lt_top, height_mono, height_strict_mono_of_isPrime, lt_of_le_of_lt, ne_top
-/
lemma Ideal.height_strict_mono_of_isPrime_of_isPrime {I J : Ideal R} [I.IsPrime] [J.IsPrime]
    (h : I < J) [J.FiniteHeight] : I.height < J.height := by
  have : I.FiniteHeight := I.finiteHeight_iff.mpr
    (Or.inr (lt_of_le_of_lt (Ideal.height_mono h.le) (J.height_lt_top IsPrime.ne_top')).ne)
  exact Ideal.height_strict_mono_of_isPrime h

@[deprecated (since := "2026-04-02")]
alias Ideal.height_strict_mono_of_isPrime_of_is_prime :=
  Ideal.height_strict_mono_of_isPrime_of_isPrime

@[deprecated "Use `Ideal.height_strict_mono_of_isPrime_of_isPrime` instead."
  (since := "2026-04-02")]
/--
lemma `Ideal.primeHeight_strict_mono` / 引理 `Ideal.primeHeight_strict_mono`

English:
lemma Ideal.primeHeight_strict_mono
  statement: {I J : Ideal R} [I.IsPrime] [J.IsPrime] (h : I < J)
  proof: by
  simpa [← Ideal.height_eq_primeHeight] using Ideal.height_strict_mono_of_isPrime_of_isPrime h

中文:
引理 理想.primeHeight_strict_mono
  结论: {I J : 理想 R} [I.是素] [J.是素] (h : I < J)
  证明: by
  simpa [← Ideal.height_eq_primeHeight] using Ideal.height_strict_mono_of_isPrime_of_isPrime h
-/
private lemma Ideal.primeHeight_strict_mono {I J : Ideal R} [I.IsPrime] [J.IsPrime] (h : I < J)
    [J.FiniteHeight] : I.primeHeight < J.primeHeight := by
  simpa [← Ideal.height_eq_primeHeight] using Ideal.height_strict_mono_of_isPrime_of_isPrime h

/--
lemma `Ideal.height_le_ringKrullDim_of_isPrime` / 引理 `Ideal.height_le_ringKrullDim_of_isPrime`

English:
lemma Ideal.height_le_ringKrullDim_of_isPrime
  given: {I : Ideal R} [I.IsPrime]
  proof: by
  rw [Ideal.height_eq_primeHeight]; rw [Ideal.primeHeight]
  exact Order.height_le_krullDim _

中文:
引理 理想.height_le_ringKrullDim_of_isPrime
  条件: {I : 理想 R} [I.是素]
  证明: by
  rw [Ideal.height_eq_primeHeight]; rw [Ideal.primeHeight]
  exact Order.height_le_krullDim _

Depends on / 依赖: Ideal.height_eq_primeHeight, Ideal.primeHeight, Order.height_le_krullDim, height_eq_primeHeight, height_le_krullDim, primeHeight
-/
lemma Ideal.height_le_ringKrullDim_of_isPrime {I : Ideal R} [I.IsPrime] :
    I.height <= ringKrullDim R := by
  rw [Ideal.height_eq_primeHeight]; rw [Ideal.primeHeight]
  exact Order.height_le_krullDim _

/--
lemma `Ideal.eq_of_le_of_height_le` / 引理 `Ideal.eq_of_le_of_height_le`

English:
lemma Ideal.eq_of_le_of_height_le
  statement: [I.IsPrime] [I.FiniteHeight]
  proof: eq_of_le_of_not_lt h fun hlt => not_le.mpr (Ideal.height_strict_mono_of_isPrime hlt) h_height

@[deprecated "Use `Ideal.height_le_ringKrullDim_of_isPrime` instead." (since := "2026-04-04")]

中文:
引理 理想.eq_of_le_of_height_le
  结论: [I.是素] [I.FiniteHeight]
  证明: eq_of_le_of_not_lt h fun hlt => not_le.mpr (Ideal.height_strict_mono_of_isPrime hlt) h_height

@[deprecated "Use `Ideal.height_le_ringKrullDim_of_isPrime` instead." (since := "2026-04-04")]

Depends on / 依赖: Ideal.height_strict_mono_of_isPrime, eq_of_le_of_not_lt, h_height, height_strict_mono_of_isPrime, not_le, not_le.mpr
-/
lemma Ideal.eq_of_le_of_height_le [I.IsPrime] [I.FiniteHeight]
    {J : Ideal R} (h : I <= J) (h_height : J.height <= I.height) : I = J :=
  eq_of_le_of_not_lt h fun hlt => not_le.mpr (Ideal.height_strict_mono_of_isPrime hlt) h_height

@[deprecated "Use `Ideal.height_le_ringKrullDim_of_isPrime` instead." (since := "2026-04-04")]
/--
lemma `Ideal.primeHeight_le_ringKrullDim` / 引理 `Ideal.primeHeight_le_ringKrullDim`

English:
lemma Ideal.primeHeight_le_ringKrullDim
  given: {I : Ideal R} [I.IsPrime]
  proof: Order.height_le_krullDim _

中文:
引理 理想.primeHeight_le_ringKrullDim
  条件: {I : 理想 R} [I.是素]
  证明: Order.height_le_krullDim _

Depends on / 依赖: le_lift, mem_of_superset, subset_closure
-/
private lemma Ideal.primeHeight_le_ringKrullDim {I : Ideal R} [I.IsPrime] :
    I.primeHeight <= ringKrullDim R := Order.height_le_krullDim _

/--
lemma `Ideal.height_le_ringKrullDim_of_ne_top` / 引理 `Ideal.height_le_ringKrullDim_of_ne_top`

English:
lemma Ideal.height_le_ringKrullDim_of_ne_top
  given: {I : Ideal R} (h : I != ⊤)
  proof: by
  obtain ⟨P, hP⟩ : Nonempty (I.minimalPrimes) := Ideal.nonempty_minimalPrimes h
  rw [I.height_eq_inf_minimalPrimes]
  have := hP.isPrime
  refine (WithBot.coe_le_coe.mpr (iInf₂_le _ hP)).trans P.height_le_ringKrullDim_of_isPrime

中文:
引理 理想.height_le_ringKrullDim_of_ne_top
  条件: {I : 理想 R} (h : I != ⊤)
  证明: by
  obtain ⟨P, hP⟩ : Nonempty (I.minimalPrimes) := Ideal.nonempty_minimalPrimes h
  rw [I.height_eq_inf_minimalPrimes]
  have := hP.isPrime
  refine (WithBot.coe_le_coe.mpr (iInf₂_le _ hP)).trans P.height_le_ringKrullDim_of_isPrime

Depends on / 依赖: I.height_eq_inf_minimalPrimes, I.minimalPrimes, Ideal.nonempty_minimalPrimes, Nonempty, P.height_le_ringKrullDim_of_isPrime, WithBot, WithBot.coe_le_coe.mpr, coe_le_coe, h.lift, hP.isPrime, height_eq_inf_minimalPrimes, height_le_ringKrullDim_of_isPrime, isPrime, minimalPrimes, monotone_closure, nonempty_minimalPrimes
-/
lemma Ideal.height_le_ringKrullDim_of_ne_top {I : Ideal R} (h : I != ⊤) :
    I.height <= ringKrullDim R := by
  obtain ⟨P, hP⟩ : Nonempty (I.minimalPrimes) := Ideal.nonempty_minimalPrimes h
  rw [I.height_eq_inf_minimalPrimes]
  have := hP.isPrime
  refine (WithBot.coe_le_coe.mpr (iInf₂_le _ hP)).trans P.height_le_ringKrullDim_of_isPrime

/--
lemma `Ideal.exists_isMaximal_height` / 引理 `Ideal.exists_isMaximal_height`

English:
lemma Ideal.exists_isMaximal_height
  given: [FiniteRingKrullDim R]
  proof: by
  let l := LTSeries.longestOf (PrimeSpectrum R)
  obtain ⟨m, hm, hle⟩ := l.last.asIdeal.exists_le_maximal IsPrime.ne_top'
  refine ⟨m, hm, le_antisymm (height_le_ringKrullDim_of_ne_top IsPrime.ne_top') ?_⟩
  trans (l.last.asIdeal.height : WithBot Nat∞)
  · rw [Ideal.height_eq_primeHeight]
    exa

中文:
引理 理想.存在_isMaximal_height
  条件: [FiniteRingKrullDim R]
  证明: by
  let l := LTSeries.longestOf (PrimeSpectrum R)
  obtain ⟨m, hm, hle⟩ := l.last.asIdeal.exists_le_maximal IsPrime.ne_top'
  refine ⟨m, hm, le_antisymm (height_le_ringKrullDim_of_ne_top IsPrime.ne_top') ?_⟩
  trans (l.last.asIdeal.height : WithBot Nat∞)
  · rw [Ideal.height_eq_primeHeight]
    exa

Depends on / 依赖: Ideal.height_eq_primeHeight, IsPrime, IsPrime.ne_top, LTSeries, LTSeries.height_last_longestOf.symm.le, LTSeries.longestOf, PrimeSpectrum, WithBot, _closure, asIdeal, closure_eq, exists_le_maximal, ge_iff, h.ge_iff, h.mem_of_mem, height, height_eq_primeHeight, height_last_longestOf, height_le_ringKrullDim_of_ne_top, height_mono
-/
lemma Ideal.exists_isMaximal_height [FiniteRingKrullDim R] :
    exists (p : Ideal R), p.IsMaximal ∧ p.height = ringKrullDim R := by
  let l := LTSeries.longestOf (PrimeSpectrum R)
  obtain ⟨m, hm, hle⟩ := l.last.asIdeal.exists_le_maximal IsPrime.ne_top'
  refine ⟨m, hm, le_antisymm (height_le_ringKrullDim_of_ne_top IsPrime.ne_top') ?_⟩
  trans (l.last.asIdeal.height : WithBot Nat∞)
  · rw [Ideal.height_eq_primeHeight]
    exact LTSeries.height_last_longestOf.symm.le
  · norm_cast
    exact height_mono hle

instance (priority := 900) Ideal.finiteHeight_of_finiteRingKrullDim {I : Ideal R}
    [FiniteRingKrullDim R] : I.FiniteHeight := by
  rw [finiteHeight_iff]; rw [or_iff_not_imp_left]; rw [← lt_top_iff_ne_top]; rw [← WithBot.coe_lt_coe]
  exact fun h => lt_of_le_of_lt (Ideal.height_le_ringKrullDim_of_ne_top h) ringKrullDim_lt_top

/--
lemma `Ideal.finiteHeight_of_le` / 引理 `Ideal.finiteHeight_of_le`

English:
lemma Ideal.finiteHeight_of_le
  given: {I J : Ideal R} (e : I <= J) (hJ : J != ⊤) [FiniteHeight J]
  proof: Or.inr
    lt_top_iff_ne_top.mp ((height_mono e).trans_lt (height_lt_top hJ))

中文:
引理 理想.finiteHeight_of_le
  条件: {I J : 理想 R} (e : I <= J) (hJ : J != ⊤) [FiniteHeight J]
  证明: Or.inr
    lt_top_iff_ne_top.mp ((height_mono e).trans_lt (height_lt_top hJ))

Depends on / 依赖: Or.inr, _bot, _closure, bot_unique, closure_empty, h.symm, l.le_lift, le_lift, monotone_closure, principal_empty
-/
lemma Ideal.finiteHeight_of_le {I J : Ideal R} (e : I <= J) (hJ : J != ⊤) [FiniteHeight J] :
    FiniteHeight I where
eq_top_or_height_ne_top := Or.inr
    lt_top_iff_ne_top.mp ((height_mono e).trans_lt (height_lt_top hJ))

/--
lemma `Ideal.mem_minimalPrimes_of_height_le` / 引理 `Ideal.mem_minimalPrimes_of_height_le`

English:
lemma Ideal.mem_minimalPrimes_of_height_le
  statement: {I J : Ideal R} (e : I <= J) [J.IsPrime]
  proof: by
  obtain ⟨p, h₁, h₂⟩ := Ideal.exists_minimalPrimes_le e
  convert! h₁
  refine (eq_of_le_of_not_lt h₂ fun h₃ => ?_).symm
  have := h₁.isPrime
  have := finiteHeight_of_le h₂ IsPrime.ne_top'
  exact lt_irrefl _ ((height_strict_mono_of_isPrime h₃).trans_le
    (e'.trans <| height_mono h₁.le))

@[de

中文:
引理 理想.mem_minimalPrimes_of_height_le
  结论: {I J : 理想 R} (e : I <= J) [J.是素]
  证明: by
  obtain ⟨p, h₁, h₂⟩ := Ideal.exists_minimalPrimes_le e
  convert! h₁
  refine (eq_of_le_of_not_lt h₂ fun h₃ => ?_).symm
  have := h₁.isPrime
  have := finiteHeight_of_le h₂ IsPrime.ne_top'
  exact lt_irrefl _ ((height_strict_mono_of_isPrime h₃).trans_le
    (e'.trans <| height_mono h₁.le))

@[de

Depends on / 依赖: Ideal.exists_minimalPrimes_le, IsPrime, IsPrime.ne_top, convert, eq_of_le_of_not_lt, exists_minimalPrimes_le, finiteHeight_of_le, height_mono, height_strict_mono_of_isPrime, isPrime, lt_irrefl, ne_top, trans_le
-/
lemma Ideal.mem_minimalPrimes_of_height_le {I J : Ideal R} (e : I <= J) [J.IsPrime]
    [FiniteHeight J] (e' : J.height <= I.height) : J in I.minimalPrimes := by
  obtain ⟨p, h₁, h₂⟩ := Ideal.exists_minimalPrimes_le e
  convert! h₁
  refine (eq_of_le_of_not_lt h₂ fun h₃ => ?_).symm
  have := h₁.isPrime
  have := finiteHeight_of_le h₂ IsPrime.ne_top'
  exact lt_irrefl _ ((height_strict_mono_of_isPrime h₃).trans_le
    (e'.trans <| height_mono h₁.le))

@[deprecated (since := "2026-07-28")]
alias Ideal.mem_minimalPrimes_of_height_eq := Ideal.mem_minimalPrimes_of_height_le

/--
lemma `Ideal.height_eq_zero_iff` / 引理 `Ideal.height_eq_zero_iff`

English:
lemma Ideal.height_eq_zero_iff
  given: {I : Ideal R} [I.IsPrime]
  statement: height I = 0 ↔ I in minimalPrimes R
  proof: by
  rw [Ideal.height_eq_primeHeight]; rw [Ideal.primeHeight]; rw [Order.height_eq_zero]; rw [minimalPrimes_eq_minimals]
  refine ⟨fun h => ⟨‹_›, ?_⟩, fun ⟨hI, hI'⟩ b hb => hI' b.isPrime hb⟩
  by_contra! ⟨P, ⟨hP₁, ⟨hP₂, hP₃⟩⟩⟩
  exact hP₃ (h (b := ⟨P, hP₁⟩) hP₂)

@[deprecated "Use `Ideal.height_eq_z

中文:
引理 理想.height_eq_zero_iff
  条件: {I : 理想 R} [I.是素]
  结论: height I = 0 ↔ I in minimalPrimes R
  证明: by
  rw [Ideal.height_eq_primeHeight]; rw [Ideal.primeHeight]; rw [Order.height_eq_zero]; rw [minimalPrimes_eq_minimals]
  refine ⟨fun h => ⟨‹_›, ?_⟩, fun ⟨hI, hI'⟩ b hb => hI' b.isPrime hb⟩
  by_contra! ⟨P, ⟨hP₁, ⟨hP₂, hP₃⟩⟩⟩
  exact hP₃ (h (b := ⟨P, hP₁⟩) hP₂)

@[deprecated "Use `Ideal.height_eq_z

Depends on / 依赖: Ideal.height_eq_primeHeight, Ideal.primeHeight, Order.height_eq_zero, b.isPrime, height_eq_primeHeight, height_eq_zero, isPrime, minimalPrimes_eq_minimals, primeHeight
-/
lemma Ideal.height_eq_zero_iff {I : Ideal R} [I.IsPrime] : height I = 0 ↔ I in minimalPrimes R := by
  rw [Ideal.height_eq_primeHeight]; rw [Ideal.primeHeight]; rw [Order.height_eq_zero]; rw [minimalPrimes_eq_minimals]
  refine ⟨fun h => ⟨‹_›, ?_⟩, fun ⟨hI, hI'⟩ b hb => hI' b.isPrime hb⟩
  by_contra! ⟨P, ⟨hP₁, ⟨hP₂, hP₃⟩⟩⟩
  exact hP₃ (h (b := ⟨P, hP₁⟩) hP₂)

@[deprecated "Use `Ideal.height_eq_zero_iff` instead." (since := "2026-04-02")]
/--
lemma `Ideal.primeHeight_eq_zero_iff` / 引理 `Ideal.primeHeight_eq_zero_iff`

English:
lemma Ideal.primeHeight_eq_zero_iff
  given: {I : Ideal R} [I.IsPrime]
  proof: by
  rw [← Ideal.height_eq_primeHeight]; rw [Ideal.height_eq_zero_iff]

中文:
引理 理想.primeHeight_eq_zero_iff
  条件: {I : 理想 R} [I.是素]
  证明: by
  rw [← Ideal.height_eq_primeHeight]; rw [Ideal.height_eq_zero_iff]
-/
private lemma Ideal.primeHeight_eq_zero_iff {I : Ideal R} [I.IsPrime] :
    primeHeight I = 0 ↔ I in minimalPrimes R := by
  rw [← Ideal.height_eq_primeHeight]; rw [Ideal.height_eq_zero_iff]

/--
lemma `Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors` / 引理 `Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors`

English:
lemma Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors
  proof: by
  rw [Ideal.height_eq_inf_minimalPrimes]
  refine le_iInf₂ fun q hq => ?_
  have : q.IsPrime := hq.isPrime
  rw [Order.one_le_iff_ne_zero]; rw [Ne]; rw [height_eq_zero_iff]
  intro hmin
exact absurd hx notMem_nonZeroDivisors_of_mem_mem_minimalPrimes
    (hq.1.2 <| Ideal.mem_span_singleton.mpr <| 

中文:
引理 理想.one_le_height_span_singleton_of_mem_nonZeroDivisors
  证明: by
  rw [Ideal.height_eq_inf_minimalPrimes]
  refine le_iInf₂ fun q hq => ?_
  have : q.IsPrime := hq.isPrime
  rw [Order.one_le_iff_ne_zero]; rw [Ne]; rw [height_eq_zero_iff]
  intro hmin
exact absurd hx notMem_nonZeroDivisors_of_mem_mem_minimalPrimes
    (hq.1.2 <| Ideal.mem_span_singleton.mpr <| 

Depends on / 依赖: Ideal.height_eq_inf_minimalPrimes, Ideal.mem_span_singleton.mpr, IsPrime, Order.one_le_iff_ne_zero, absurd, dvd_refl, height_eq_inf_minimalPrimes, height_eq_zero_iff, hq.isPrime, isPrime, mem_span_singleton, notMem_nonZeroDivisors_of_mem_mem_minimalPrimes, one_le_iff_ne_zero, q.IsPrime
-/
lemma Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors
    {x : R} (hx : x in nonZeroDivisors R) : 1 <= (span {x}).height := by
  rw [Ideal.height_eq_inf_minimalPrimes]
  refine le_iInf₂ fun q hq => ?_
  have : q.IsPrime := hq.isPrime
  rw [Order.one_le_iff_ne_zero]; rw [Ne]; rw [height_eq_zero_iff]
  intro hmin
exact absurd hx notMem_nonZeroDivisors_of_mem_mem_minimalPrimes
    (hq.1.2 <| Ideal.mem_span_singleton.mpr <| dvd_refl x) hmin

@[simp]
/--
lemma `Ideal.height_bot` / 引理 `Ideal.height_bot`

English:
lemma Ideal.height_bot
  given: [Nontrivial R]
  statement: (⊥ : Ideal R).height = 0
  proof: by
  obtain ⟨p, hp⟩ := Ideal.nonempty_minimalPrimes (R := R) (I := ⊥) top_ne_bot.symm
  rw [Ideal.height_eq_inf_minimalPrimes]
  simp only [ENat.iInf_eq_zero]
  refine ⟨p, hp, haveI := hp.isPrime; height_eq_zero_iff.mpr hp⟩

@[simp]

中文:
引理 理想.height_bot
  条件: [非平凡 R]
  结论: (⊥ : 理想 R).height = 0
  证明: by
  obtain ⟨p, hp⟩ := Ideal.nonempty_minimalPrimes (R := R) (I := ⊥) top_ne_bot.symm
  rw [Ideal.height_eq_inf_minimalPrimes]
  simp only [ENat.iInf_eq_zero]
  refine ⟨p, hp, haveI := hp.isPrime; height_eq_zero_iff.mpr hp⟩

@[simp]

Depends on / 依赖: ENat.iInf_eq_zero, Ideal.height_eq_inf_minimalPrimes, Ideal.nonempty_minimalPrimes, height_eq_inf_minimalPrimes, height_eq_zero_iff, height_eq_zero_iff.mpr, hp.isPrime, iInf_eq_zero, isPrime, nonempty_minimalPrimes, top_ne_bot, top_ne_bot.symm
-/
lemma Ideal.height_bot [Nontrivial R] : (⊥ : Ideal R).height = 0 := by
  obtain ⟨p, hp⟩ := Ideal.nonempty_minimalPrimes (R := R) (I := ⊥) top_ne_bot.symm
  rw [Ideal.height_eq_inf_minimalPrimes]
  simp only [ENat.iInf_eq_zero]
  refine ⟨p, hp, haveI := hp.isPrime; height_eq_zero_iff.mpr hp⟩

@[simp]
/--
lemma `Ideal.height_eq_zero_iff_eq_bot` / 引理 `Ideal.height_eq_zero_iff_eq_bot`

English:
lemma Ideal.height_eq_zero_iff_eq_bot
  given: [IsDomain R] {I : Ideal R}
  statement: I.height = 0 ↔ I = ⊥
  proof: by
  refine ⟨fun hI => ?_, fun hI0 => by simp [hI0]⟩
  rcases exists_isPrime_height_eq hI with ⟨p, _, hIp, hp0⟩
  rw [CharP.cast_eq_zero]; rw [height_eq_zero_iff]; rw [IsDomain.minimalPrimes_eq_singleton_bot]; rw [Set.mem_singleton_iff] at hp0
  exact bot_unique (hIp.trans_eq hp0)

中文:
引理 理想.height_eq_zero_iff_eq_bot
  条件: [是整环 R] {I : 理想 R}
  结论: I.height = 0 ↔ I = ⊥
  证明: by
  refine ⟨fun hI => ?_, fun hI0 => by simp [hI0]⟩
  rcases exists_isPrime_height_eq hI with ⟨p, _, hIp, hp0⟩
  rw [CharP.cast_eq_zero]; rw [height_eq_zero_iff]; rw [IsDomain.minimalPrimes_eq_singleton_bot]; rw [Set.mem_singleton_iff] at hp0
  exact bot_unique (hIp.trans_eq hp0)

Depends on / 依赖: CharP.cast_eq_zero, IsDomain, IsDomain.minimalPrimes_eq_singleton_bot, Set.mem_singleton_iff, bot_unique, cast_eq_zero, exists_isPrime_height_eq, hIp.trans_eq, height_eq_zero_iff, mem_singleton_iff, minimalPrimes_eq_singleton_bot, trans_eq
-/
lemma Ideal.height_eq_zero_iff_eq_bot [IsDomain R] {I : Ideal R} : I.height = 0 ↔ I = ⊥ := by
  refine ⟨fun hI => ?_, fun hI0 => by simp [hI0]⟩
  rcases exists_isPrime_height_eq hI with ⟨p, _, hIp, hp0⟩
  rw [CharP.cast_eq_zero]; rw [height_eq_zero_iff]; rw [IsDomain.minimalPrimes_eq_singleton_bot]; rw [Set.mem_singleton_iff] at hp0
  exact bot_unique (hIp.trans_eq hp0)

/--
theorem `Ideal.ne_bot_of_height_eq_one` / 定理 `Ideal.ne_bot_of_height_eq_one`

English:
theorem Ideal.ne_bot_of_height_eq_one
  given: [IsDomain R] {I : Ideal R} (h : I.height = 1)
  statement: I != ⊥
  proof: I.height_eq_zero_iff_eq_bot.not.mp (ne_zero_of_eq_one h)

中文:
定理 理想.ne_bot_of_height_eq_one
  条件: [是整环 R] {I : 理想 R} (h : I.height = 1)
  结论: I != ⊥
  证明: I.height_eq_zero_iff_eq_bot.not.mp (ne_zero_of_eq_one h)

Depends on / 依赖: I.height_eq_zero_iff_eq_bot.not.mp, height_eq_zero_iff_eq_bot, ne_zero_of_eq_one
-/
theorem Ideal.ne_bot_of_height_eq_one [IsDomain R] {I : Ideal R} (h : I.height = 1) : I != ⊥ :=
  I.height_eq_zero_iff_eq_bot.not.mp (ne_zero_of_eq_one h)

/-- In a trivial commutative ring, the height of any ideal is `∞`. -/
@[simp, nontriviality]
/--
lemma `Ideal.height_of_subsingleton` / 引理 `Ideal.height_of_subsingleton`

English:
lemma Ideal.height_of_subsingleton
  given: [Subsingleton R]
  statement: I.height = ⊤
  proof: by
  rw [Subsingleton.elim I ⊤]; rw [Ideal.height_top]

中文:
引理 理想.height_of_subsingleton
  条件: [子单例 R]
  结论: I.height = ⊤
  证明: by
  rw [Subsingleton.elim I ⊤]; rw [Ideal.height_top]

Depends on / 依赖: Ideal.height_top, Subsingleton, Subsingleton.elim, height_top
-/
lemma Ideal.height_of_subsingleton [Subsingleton R] : I.height = ⊤ := by
  rw [Subsingleton.elim I ⊤]; rw [Ideal.height_top]

/--
theorem `Ideal.isMaximal_of_height_eq_ringKrullDim` / 定理 `Ideal.isMaximal_of_height_eq_ringKrullDim`

English:
theorem Ideal.isMaximal_of_height_eq_ringKrullDim
  statement: {I : Ideal R} [I.IsPrime]
  proof: by
  have h : I != ⊤ := Ideal.IsPrime.ne_top'
  obtain ⟨M, hM, hM'⟩ := Ideal.exists_le_maximal I h
  rcases lt_or_eq_of_le hM' with (hM' | hM')
  · have h1 := Ideal.height_strict_mono_of_isPrime hM'
    have h2 := e ▸ M.height_le_ringKrullDim_of_ne_top hM.ne_top
    simp [← not_lt, h1] at h2
  · exa

中文:
定理 理想.isMaximal_of_height_eq_ringKrullDim
  结论: {I : 理想 R} [I.是素]
  证明: by
  have h : I != ⊤ := Ideal.IsPrime.ne_top'
  obtain ⟨M, hM, hM'⟩ := Ideal.exists_le_maximal I h
  rcases lt_or_eq_of_le hM' with (hM' | hM')
  · have h1 := Ideal.height_strict_mono_of_isPrime hM'
    have h2 := e ▸ M.height_le_ringKrullDim_of_ne_top hM.ne_top
    simp [← not_lt, h1] at h2
  · exa

Depends on / 依赖: Ideal.IsPrime.ne_top, Ideal.exists_le_maximal, Ideal.height_strict_mono_of_isPrime, IsPrime, M.height_le_ringKrullDim_of_ne_top, exists_le_maximal, hM.ne_top, height_le_ringKrullDim_of_ne_top, height_strict_mono_of_isPrime, lt_or_eq_of_le, ne_top, not_lt
-/
theorem Ideal.isMaximal_of_height_eq_ringKrullDim {I : Ideal R} [I.IsPrime]
    [FiniteRingKrullDim R] (e : I.height = ringKrullDim R) : I.IsMaximal := by
  have h : I != ⊤ := Ideal.IsPrime.ne_top'
  obtain ⟨M, hM, hM'⟩ := Ideal.exists_le_maximal I h
  rcases lt_or_eq_of_le hM' with (hM' | hM')
  · have h1 := Ideal.height_strict_mono_of_isPrime hM'
    have h2 := e ▸ M.height_le_ringKrullDim_of_ne_top hM.ne_top
    simp [← not_lt, h1] at h2
  · exact hM' ▸ hM

@[deprecated "Use `Ideal.isMaximal_of_height_eq_ringKrullDim` instead." (since := "2026-04-02")]
/--
theorem `Ideal.isMaximal_of_primeHeight_eq_ringKrullDim` / 定理 `Ideal.isMaximal_of_primeHeight_eq_ringKrullDim`

English:
theorem Ideal.isMaximal_of_primeHeight_eq_ringKrullDim
  statement: {I : Ideal R} [I.IsPrime]
  proof: Ideal.isMaximal_of_height_eq_ringKrullDim (by simpa [Ideal.height_eq_primeHeight])

中文:
定理 理想.isMaximal_of_primeHeight_eq_ringKrullDim
  结论: {I : 理想 R} [I.是素]
  证明: Ideal.isMaximal_of_height_eq_ringKrullDim (by simpa [Ideal.height_eq_primeHeight])
-/
private theorem Ideal.isMaximal_of_primeHeight_eq_ringKrullDim {I : Ideal R} [I.IsPrime]
    [FiniteRingKrullDim R] (e : I.primeHeight = ringKrullDim R) : I.IsMaximal :=
  Ideal.isMaximal_of_height_eq_ringKrullDim (by simpa [Ideal.height_eq_primeHeight])

/-- The height of the maximal ideal equals the Krull dimension in a local ring. -/
@[simp]
/--
theorem `IsLocalRing.maximalIdeal_height_eq_ringKrullDim` / 定理 `IsLocalRing.maximalIdeal_height_eq_ringKrullDim`

English:
theorem IsLocalRing.maximalIdeal_height_eq_ringKrullDim
  given: [IsLocalRing R]
  proof: by
  rw [Ideal.height_eq_primeHeight]; rw [Ideal.primeHeight]
  exact Order.height_top_eq_krullDim

@[deprecated "Use `IsLocalRing.maximalIdeal_height_eq_ringKrullDim` instead."
  (since := "2026-04-04")]

中文:
定理 是局部环.maximalIdeal_height_eq_ringKrullDim
  条件: [是局部环 R]
  证明: by
  rw [Ideal.height_eq_primeHeight]; rw [Ideal.primeHeight]
  exact Order.height_top_eq_krullDim

@[deprecated "Use `IsLocalRing.maximalIdeal_height_eq_ringKrullDim` instead."
  (since := "2026-04-04")]

Depends on / 依赖: Ideal.height_eq_primeHeight, Ideal.primeHeight, Order.height_top_eq_krullDim, height_eq_primeHeight, height_top_eq_krullDim, primeHeight
-/
theorem IsLocalRing.maximalIdeal_height_eq_ringKrullDim [IsLocalRing R] :
    (IsLocalRing.maximalIdeal R).height = ringKrullDim R := by
  rw [Ideal.height_eq_primeHeight]; rw [Ideal.primeHeight]
  exact Order.height_top_eq_krullDim

@[deprecated "Use `IsLocalRing.maximalIdeal_height_eq_ringKrullDim` instead."
  (since := "2026-04-04")]
/--
theorem `IsLocalRing.maximalIdeal_primeHeight_eq_ringKrullDim` / 定理 `IsLocalRing.maximalIdeal_primeHeight_eq_ringKrullDim`

English:
theorem IsLocalRing.maximalIdeal_primeHeight_eq_ringKrullDim
  given: [IsLocalRing R]
  proof: by
  simp [← Ideal.height_eq_primeHeight]

中文:
定理 是局部环.maximalIdeal_primeHeight_eq_ringKrullDim
  条件: [是局部环 R]
  证明: by
  simp [← Ideal.height_eq_primeHeight]
-/
private theorem IsLocalRing.maximalIdeal_primeHeight_eq_ringKrullDim [IsLocalRing R] :
    (IsLocalRing.maximalIdeal R).primeHeight = ringKrullDim R := by
  simp [← Ideal.height_eq_primeHeight]

/--
theorem `Ideal.height_eq_ringKrullDim_iff` / 定理 `Ideal.height_eq_ringKrullDim_iff`

English:
theorem Ideal.height_eq_ringKrullDim_iff
  statement: [FiniteRingKrullDim R] [IsLocalRing R] {I : Ideal R}
  proof: by
  constructor
  · intro h
    exact IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_of_height_eq_ringKrullDim h)
  · rintro rfl
    exact IsLocalRing.maximalIdeal_height_eq_ringKrullDim

@[deprecated "Use `Ideal.height_eq_ringKrullDim_iff` instead." (since := "2026-04-02")]

中文:
定理 理想.height_eq_ringKrullDim_iff
  结论: [FiniteRingKrullDim R] [是局部环 R] {I : 理想 R}
  证明: by
  constructor
  · intro h
    exact IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_of_height_eq_ringKrullDim h)
  · rintro rfl
    exact IsLocalRing.maximalIdeal_height_eq_ringKrullDim

@[deprecated "Use `Ideal.height_eq_ringKrullDim_iff` instead." (since := "2026-04-02")]

Depends on / 依赖: Ideal.isMaximal_of_height_eq_ringKrullDim, IsLocalRing, IsLocalRing.eq_maximalIdeal, IsLocalRing.maximalIdeal_height_eq_ringKrullDim, eq_maximalIdeal, isMaximal_of_height_eq_ringKrullDim, maximalIdeal_height_eq_ringKrullDim
-/
theorem Ideal.height_eq_ringKrullDim_iff [FiniteRingKrullDim R] [IsLocalRing R] {I : Ideal R}
    [I.IsPrime] : I.height = ringKrullDim R ↔ I = IsLocalRing.maximalIdeal R := by
  constructor
  · intro h
    exact IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_of_height_eq_ringKrullDim h)
  · rintro rfl
    exact IsLocalRing.maximalIdeal_height_eq_ringKrullDim

@[deprecated "Use `Ideal.height_eq_ringKrullDim_iff` instead." (since := "2026-04-02")]
/--
theorem `Ideal.primeHeight_eq_ringKrullDim_iff` / 定理 `Ideal.primeHeight_eq_ringKrullDim_iff`

English:
theorem Ideal.primeHeight_eq_ringKrullDim_iff
  statement: [FiniteRingKrullDim R] [IsLocalRing R]
  proof: by
  rw [← Ideal.height_eq_primeHeight]; rw [Ideal.height_eq_ringKrullDim_iff]

中文:
定理 理想.primeHeight_eq_ringKrullDim_iff
  结论: [FiniteRingKrullDim R] [是局部环 R]
  证明: by
  rw [← Ideal.height_eq_primeHeight]; rw [Ideal.height_eq_ringKrullDim_iff]
-/
private theorem Ideal.primeHeight_eq_ringKrullDim_iff [FiniteRingKrullDim R] [IsLocalRing R]
    {I : Ideal R} [I.IsPrime] :
    Ideal.primeHeight I = ringKrullDim R ↔ I = IsLocalRing.maximalIdeal R := by
  rw [← Ideal.height_eq_primeHeight]; rw [Ideal.height_eq_ringKrullDim_iff]

/--
lemma `Ideal.height_le_iff` / 引理 `Ideal.height_le_iff`

English:
lemma Ideal.height_le_iff
  given: {p : Ideal R} {n : Nat} [p.IsPrime]
  proof: by
  rw [height_eq_primeHeight]; rw [primeHeight]; rw [Order.height_le_coe_iff]; rw [(PrimeSpectrum.equivSubtype R).forall_congr_left]; rw [Subtype.forall]
  congr!
  rw [height_eq_primeHeight]; rw [primeHeight]
  rfl

中文:
引理 理想.height_le_iff
  条件: {p : 理想 R} {n : 自然数} [p.是素]
  证明: by
  rw [height_eq_primeHeight]; rw [primeHeight]; rw [Order.height_le_coe_iff]; rw [(PrimeSpectrum.equivSubtype R).forall_congr_left]; rw [Subtype.forall]
  congr!
  rw [height_eq_primeHeight]; rw [primeHeight]
  rfl

Depends on / 依赖: Order.height_le_coe_iff, PrimeSpectrum, PrimeSpectrum.equivSubtype, Subtype, Subtype.forall, equivSubtype, forall_congr_left, height_eq_primeHeight, height_le_coe_iff, primeHeight
-/
lemma Ideal.height_le_iff {p : Ideal R} {n : Nat} [p.IsPrime] :
    p.height <= n ↔ forall q : Ideal R, q.IsPrime -> q < p -> q.height < n := by
  rw [height_eq_primeHeight]; rw [primeHeight]; rw [Order.height_le_coe_iff]; rw [(PrimeSpectrum.equivSubtype R).forall_congr_left]; rw [Subtype.forall]
  congr!
  rw [height_eq_primeHeight]; rw [primeHeight]
  rfl

/--
lemma `Ideal.height_le_iff_covBy` / 引理 `Ideal.height_le_iff_covBy`

English:
lemma Ideal.height_le_iff_covBy
  given: {p : Ideal R} {n : Nat} [p.IsPrime] [IsNoetherianRing R]
  proof: by
  rw [Ideal.height_le_iff]
  constructor
  · intro H q hq e _
    exact H q hq e
  · intro H q hq e
    obtain ⟨⟨x, hx⟩, hqx, hxp⟩ :=
      @exists_le_covBy_of_lt { I : Ideal R // I.IsPrime } ⟨q, hq⟩ ⟨p, ‹_›⟩ _ _ e
    exact (Ideal.height_mono hqx).trans_lt
      (H _ hx hxp.1 (fun I hI e => hxp.

中文:
引理 理想.height_le_iff_covBy
  条件: {p : 理想 R} {n : 自然数} [p.是素] [是Noether环 R]
  证明: by
  rw [Ideal.height_le_iff]
  constructor
  · intro H q hq e _
    exact H q hq e
  · intro H q hq e
    obtain ⟨⟨x, hx⟩, hqx, hxp⟩ :=
      @exists_le_covBy_of_lt { I : Ideal R // I.IsPrime } ⟨q, hq⟩ ⟨p, ‹_›⟩ _ _ e
    exact (Ideal.height_mono hqx).trans_lt
      (H _ hx hxp.1 (fun I hI e => hxp.

Depends on / 依赖: I.IsPrime, Ideal.height_le_iff, Ideal.height_mono, IsPrime, Subtype, Subtype.mk, exists_le_covBy_of_lt, height_le_iff, height_mono, trans_lt
-/
lemma Ideal.height_le_iff_covBy {p : Ideal R} {n : Nat} [p.IsPrime] [IsNoetherianRing R] :
    p.height <= n ↔ forall q : Ideal R, q.IsPrime -> q < p ->
      (forall q' : Ideal R, q'.IsPrime -> q < q' -> ¬ q' < p) -> q.height < n := by
  rw [Ideal.height_le_iff]
  constructor
  · intro H q hq e _
    exact H q hq e
  · intro H q hq e
    obtain ⟨⟨x, hx⟩, hqx, hxp⟩ :=
      @exists_le_covBy_of_lt { I : Ideal R // I.IsPrime } ⟨q, hq⟩ ⟨p, ‹_›⟩ _ _ e
    exact (Ideal.height_mono hqx).trans_lt
      (H _ hx hxp.1 (fun I hI e => hxp.2 (show Subtype.mk x hx < ⟨I, hI⟩ from e)))

/--
lemma `RingEquiv.height_comap_of_isPrime` / 引理 `RingEquiv.height_comap_of_isPrime`

English:
lemma RingEquiv.height_comap_of_isPrime
  statement: {S : Type*} [CommRing S] (e : R ≃+* S)
  proof: by
  rw [height_eq_primeHeight]; rw [height_eq_primeHeight]; rw [primeHeight]; rw [primeHeight]; rw [← Order.height_orderIso (PrimeSpectrum.comapEquiv e.symm) ⟨p]; rw [‹_›⟩]
  have := p.map_comap_of_equiv e.symm
  congr

@[simp]

中文:
引理 环等价.height_comap_of_isPrime
  结论: {S : 类型} [交换环 S] (e : R ≃+* S)
  证明: by
  rw [height_eq_primeHeight]; rw [height_eq_primeHeight]; rw [primeHeight]; rw [primeHeight]; rw [← Order.height_orderIso (PrimeSpectrum.comapEquiv e.symm) ⟨p]; rw [‹_›⟩]
  have := p.map_comap_of_equiv e.symm
  congr

@[simp]
-/
private lemma RingEquiv.height_comap_of_isPrime {S : Type*} [CommRing S] (e : R ≃+* S)
    (p : Ideal S) [p.IsPrime] : (p.comap e).height = p.height := by
  rw [height_eq_primeHeight]; rw [height_eq_primeHeight]; rw [primeHeight]; rw [primeHeight]; rw [← Order.height_orderIso (PrimeSpectrum.comapEquiv e.symm) ⟨p]; rw [‹_›⟩]
  have := p.map_comap_of_equiv e.symm
  congr

@[simp]
/--
lemma `RingEquiv.height_comap` / 引理 `RingEquiv.height_comap`

English:
lemma RingEquiv.height_comap
  given: {S : Type*} [CommRing S] (e : R ≃+* S) (I : Ideal S)
  proof: by
  refine (Equiv.iInf_congr e.idealComapOrderIso fun J => (Equiv.iInf_congr ?_ fun h => ?_).symm).symm
  · refine .ofIff ?_
    rw [← Ideal.comap_coe]; rw [Ideal.comap_minimalPrimes_eq_of_surjective (f := (↑e : R ->+* S)) e.surjective]
    exact e.idealComapOrderIso.injective.mem_set_image.symm
  

中文:
引理 环等价.height_comap
  条件: {S : 类型} [交换环 S] (e : R ≃+* S) (I : 理想 S)
  证明: by
  refine (Equiv.iInf_congr e.idealComapOrderIso fun J => (Equiv.iInf_congr ?_ fun h => ?_).symm).symm
  · refine .ofIff ?_
    rw [← Ideal.comap_coe]; rw [Ideal.comap_minimalPrimes_eq_of_surjective (f := (↑e : R ->+* S)) e.surjective]
    exact e.idealComapOrderIso.injective.mem_set_image.symm
  

Depends on / 依赖: Equiv.iInf_congr, EquivLike, EquivLike.coe_coe, Ideal.comap_coe, Ideal.comap_minimalPrimes_eq_of_surjective, Ideal.height_eq_primeHeight, IsPrime, J.IsPrime, RingEquiv, RingEquiv.height_comap_of_isPrime, RingEquiv.idealComapOrderIso_apply, coe_coe, comap_coe, comap_minimalPrimes_eq_of_surjective, e.idealComapOrderIso, e.idealComapOrderIso.injective.mem_set_image.symm, e.surjective, h.isPrime, height_comap_of_isPrime, height_eq_primeHeight
-/
lemma RingEquiv.height_comap {S : Type*} [CommRing S] (e : R ≃+* S) (I : Ideal S) :
    (I.comap e).height = I.height := by
  refine (Equiv.iInf_congr e.idealComapOrderIso fun J => (Equiv.iInf_congr ?_ fun h => ?_).symm).symm
  · refine .ofIff ?_
    rw [← Ideal.comap_coe]; rw [Ideal.comap_minimalPrimes_eq_of_surjective (f := (↑e : R ->+* S)) e.surjective]
    exact e.idealComapOrderIso.injective.mem_set_image.symm
  · have : J.IsPrime := h.isPrime
    simp only [EquivLike.coe_coe, RingEquiv.idealComapOrderIso_apply,
      ← Ideal.height_eq_primeHeight, RingEquiv.height_comap_of_isPrime]

@[simp]
/--
lemma `RingEquiv.height_map` / 引理 `RingEquiv.height_map`

English:
lemma RingEquiv.height_map
  given: {S : Type*} [CommRing S] (e : R ≃+* S) (I : Ideal R)
  proof: by
  rw [← Ideal.comap_symm e]; rw [height_comap]

中文:
引理 环等价.height_map
  条件: {S : 类型} [交换环 S] (e : R ≃+* S) (I : 理想 R)
  证明: by
  rw [← Ideal.comap_symm e]; rw [height_comap]

Depends on / 依赖: Ideal.comap_symm, comap_symm, height_comap
-/
lemma RingEquiv.height_map {S : Type*} [CommRing S] (e : R ≃+* S) (I : Ideal R) :
    (I.map e).height = I.height := by
  rw [← Ideal.comap_symm e]; rw [height_comap]

/--
lemma `ringKrullDim_le_iff_height_le` / 引理 `ringKrullDim_le_iff_height_le`

English:
lemma ringKrullDim_le_iff_height_le
  given: {R : Type*} [CommRing R] (n : WithBot Nat∞)
  proof: by
  rw [ringKrullDim]; rw [Order.krullDim_eq_iSup_height]; rw [iSup_le_iff]
  refine ⟨fun h p hp => ?_, fun h p => ?_⟩
  · rw [Ideal.height_eq_primeHeight]
    exact h ⟨p, hp⟩
  · specialize h p.2
    rwa [Ideal.height_eq_primeHeight] at h

中文:
引理 ringKrullDim_le_iff_height_le
  条件: {R : 类型} [交换环 R] (n : WithBot 自然数∞)
  证明: by
  rw [ringKrullDim]; rw [Order.krullDim_eq_iSup_height]; rw [iSup_le_iff]
  refine ⟨fun h p hp => ?_, fun h p => ?_⟩
  · rw [Ideal.height_eq_primeHeight]
    exact h ⟨p, hp⟩
  · specialize h p.2
    rwa [Ideal.height_eq_primeHeight] at h

Depends on / 依赖: Ideal.height_eq_primeHeight, Order.krullDim_eq_iSup_height, height_eq_primeHeight, iSup_le_iff, krullDim_eq_iSup_height, ringKrullDim, specialize
-/
lemma ringKrullDim_le_iff_height_le {R : Type*} [CommRing R] (n : WithBot Nat∞) :
    ringKrullDim R <= n ↔ forall ⦃p : Ideal R⦄, p.IsPrime -> p.height <= n := by
  rw [ringKrullDim]; rw [Order.krullDim_eq_iSup_height]; rw [iSup_le_iff]
  refine ⟨fun h p hp => ?_, fun h p => ?_⟩
  · rw [Ideal.height_eq_primeHeight]
    exact h ⟨p, hp⟩
  · specialize h p.2
    rwa [Ideal.height_eq_primeHeight] at h

/--
lemma `ringKrullDim_le_iff_isMaximal_height_le` / 引理 `ringKrullDim_le_iff_isMaximal_height_le`

English:
lemma ringKrullDim_le_iff_isMaximal_height_le
  given: {R : Type*} [CommRing R] (n : WithBot Nat∞)
  proof: by
  rw [ringKrullDim_le_iff_height_le]
  refine ⟨fun h m hm => h hm.isPrime, fun h p hp => ?_⟩
  obtain ⟨m, hm, hle⟩ := p.exists_le_maximal hp.ne_top
  refine le_trans ?_ (h hm)
  norm_cast
  exact Ideal.height_mono hle

中文:
引理 ringKrullDim_le_iff_isMaximal_height_le
  条件: {R : 类型} [交换环 R] (n : WithBot 自然数∞)
  证明: by
  rw [ringKrullDim_le_iff_height_le]
  refine ⟨fun h m hm => h hm.isPrime, fun h p hp => ?_⟩
  obtain ⟨m, hm, hle⟩ := p.exists_le_maximal hp.ne_top
  refine le_trans ?_ (h hm)
  norm_cast
  exact Ideal.height_mono hle

Depends on / 依赖: Ideal.height_mono, exists_le_maximal, height_mono, hm.isPrime, hp.ne_top, isPrime, le_trans, ne_top, p.exists_le_maximal, ringKrullDim_le_iff_height_le
-/
lemma ringKrullDim_le_iff_isMaximal_height_le {R : Type*} [CommRing R] (n : WithBot Nat∞) :
    ringKrullDim R <= n ↔ forall ⦃m : Ideal R⦄, m.IsMaximal -> m.height <= n := by
  rw [ringKrullDim_le_iff_height_le]
  refine ⟨fun h m hm => h hm.isPrime, fun h p hp => ?_⟩
  obtain ⟨m, hm, hle⟩ := p.exists_le_maximal hp.ne_top
  refine le_trans ?_ (h hm)
  norm_cast
  exact Ideal.height_mono hle

/--
theorem `IsLocalization.height_under_eq_of_isPrime` / 定理 `IsLocalization.height_under_eq_of_isPrime`

English:
theorem IsLocalization.height_under_eq_of_isPrime
  statement: (S : Submonoid R) {A : Type*} [CommRing A]
  proof: by
  rw [eq_comm]; rw [Ideal.height_eq_primeHeight]; rw [Ideal.height_eq_primeHeight]; rw [Ideal.primeHeight]; rw [Ideal.primeHeight]; rw [← WithBot.coe_inj]; rw [Order.height_eq_krullDim_Iic]; rw [Order.height_eq_krullDim_Iic]
  let e := IsLocalization.orderIsoOfPrime S A
  have H (p : Ideal R) (hp

中文:
定理 是Localization.height_under_eq_of_isPrime
  结论: (S : 子幺半群 R) {A : 类型} [交换环 A]
  证明: by
  rw [eq_comm]; rw [Ideal.height_eq_primeHeight]; rw [Ideal.height_eq_primeHeight]; rw [Ideal.primeHeight]; rw [Ideal.primeHeight]; rw [← WithBot.coe_inj]; rw [Order.height_eq_krullDim_Iic]; rw [Order.height_eq_krullDim_Iic]
  let e := IsLocalization.orderIsoOfPrime S A
  have H (p : Ideal R) (hp
-/
private theorem IsLocalization.height_under_eq_of_isPrime (S : Submonoid R) {A : Type*} [CommRing A]
    [Algebra R A] [IsLocalization S A] (J : Ideal A) [J.IsPrime] :
    (J.comap (algebraMap R A)).height = J.height := by
  rw [eq_comm]; rw [Ideal.height_eq_primeHeight]; rw [Ideal.height_eq_primeHeight]; rw [Ideal.primeHeight]; rw [Ideal.primeHeight]; rw [← WithBot.coe_inj]; rw [Order.height_eq_krullDim_Iic]; rw [Order.height_eq_krullDim_Iic]
  let e := IsLocalization.orderIsoOfPrime S A
  have H (p : Ideal R) (hp : p <= J.comap (algebraMap R A)) : Disjoint (S : Set R) p :=
    Set.disjoint_of_subset_right hp (e ⟨_, ‹J.IsPrime›⟩).2.2
  exact Order.krullDim_eq_of_orderIso
    { toFun I := ⟨⟨I.1.1.comap (algebraMap R A), (e ⟨_, I.1.2⟩).2.1⟩, Ideal.comap_mono I.2⟩
      invFun I := ⟨⟨_, (e.symm ⟨_, I.1.2, H _ I.2⟩).2⟩, Ideal.map_le_iff_le_comap.mpr I.2⟩
left_inv I := Subtype.ext PrimeSpectrum.ext_iff.mpr
        congrArg (fun I => I.1) (e.left_inv ⟨_, I.1.2⟩)
right_inv I := Subtype.ext PrimeSpectrum.ext_iff.mpr
        congrArg (fun I => I.1) (e.right_inv ⟨_, I.1.2, H _ I.2⟩)
      map_rel_iff' {I₁ I₂} := @RelIso.map_rel_iff _ _ _ _ e ⟨_, I₁.1.2⟩ ⟨_, I₂.1.2⟩ }

@[deprecated "Use `Ideal.height_ne_top_of_isPrime` instead." (since := "2026-04-04")]
/--
theorem `IsLocalization.primeHeight_comap` / 定理 `IsLocalization.primeHeight_comap`

English:
theorem IsLocalization.primeHeight_comap
  statement: (S : Submonoid R) {A : Type*} [CommRing A]
  proof: by
  simpa [Ideal.height_eq_primeHeight] using IsLocalization.height_under_eq_of_isPrime S J

中文:
定理 是Localization.primeHeight_comap
  结论: (S : 子幺半群 R) {A : 类型} [交换环 A]
  证明: by
  simpa [Ideal.height_eq_primeHeight] using IsLocalization.height_under_eq_of_isPrime S J
-/
private theorem IsLocalization.primeHeight_comap (S : Submonoid R) {A : Type*} [CommRing A]
    [Algebra R A] [IsLocalization S A] (J : Ideal A) [J.IsPrime] :
    (J.comap (algebraMap R A)).primeHeight = J.primeHeight := by
  simpa [Ideal.height_eq_primeHeight] using IsLocalization.height_under_eq_of_isPrime S J

/--
theorem `IsLocalization.height_under` / 定理 `IsLocalization.height_under`

English:
theorem IsLocalization.height_under
  statement: (S : Submonoid R) {A : Type*} [CommRing A] [Algebra R A]
  proof: by
  rw [(J.comap _).height_eq_inf_minimalPrimes]; rw [J.height_eq_inf_minimalPrimes]
  simp only [IsLocalization.minimalPrimes_comap S A, iInf_image]
  apply iInf_congr (fun p => iInf_congr fun hp => ?_)
  have := hp.isPrime
  exact IsLocalization.height_under_eq_of_isPrime S _

@[deprecated (since

中文:
定理 是Localization.height_under
  结论: (S : 子幺半群 R) {A : 类型} [交换环 A] [代数 R A]
  证明: by
  rw [(J.comap _).height_eq_inf_minimalPrimes]; rw [J.height_eq_inf_minimalPrimes]
  simp only [IsLocalization.minimalPrimes_comap S A, iInf_image]
  apply iInf_congr (fun p => iInf_congr fun hp => ?_)
  have := hp.isPrime
  exact IsLocalization.height_under_eq_of_isPrime S _

@[deprecated (since

Depends on / 依赖: IsLocalization, IsLocalization.height_under_eq_of_isPrime, IsLocalization.minimalPrimes_comap, J.comap, J.height_eq_inf_minimalPrimes, height_eq_inf_minimalPrimes, height_under_eq_of_isPrime, hp.isPrime, iInf_congr, iInf_image, isPrime, minimalPrimes_comap
-/
theorem IsLocalization.height_under (S : Submonoid R) {A : Type*} [CommRing A] [Algebra R A]
    [IsLocalization S A] (J : Ideal A) : (J.under R).height = J.height := by
  rw [(J.comap _).height_eq_inf_minimalPrimes]; rw [J.height_eq_inf_minimalPrimes]
  simp only [IsLocalization.minimalPrimes_comap S A, iInf_image]
  apply iInf_congr (fun p => iInf_congr fun hp => ?_)
  have := hp.isPrime
  exact IsLocalization.height_under_eq_of_isPrime S _

@[deprecated (since := "2026-04-09")] alias IsLocalization.height_comap :=
  IsLocalization.height_under

/--
theorem `IsLocalization.AtPrime.ringKrullDim_eq_height` / 定理 `IsLocalization.AtPrime.ringKrullDim_eq_height`

English:
theorem IsLocalization.AtPrime.ringKrullDim_eq_height
  statement: (I : Ideal R) [I.IsPrime] (A : Type*)
  proof: by
  have := IsLocalization.AtPrime.isLocalRing A I
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]; rw [← IsLocalization.height_under I.primeCompl]; rw [← IsLocalization.AtPrime.under_maximalIdeal A I]

中文:
定理 是Localization.AtPrime.ringKrullDim_eq_height
  结论: (I : 理想 R) [I.是素] (A : 类型)
  证明: by
  have := IsLocalization.AtPrime.isLocalRing A I
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]; rw [← IsLocalization.height_under I.primeCompl]; rw [← IsLocalization.AtPrime.under_maximalIdeal A I]

Depends on / 依赖: AtPrime, I.primeCompl, IsLocalRing, IsLocalRing.maximalIdeal_height_eq_ringKrullDim, IsLocalization, IsLocalization.AtPrime.isLocalRing, IsLocalization.AtPrime.under_maximalIdeal, IsLocalization.height_under, height_under, isLocalRing, maximalIdeal_height_eq_ringKrullDim, primeCompl, under_maximalIdeal
-/
theorem IsLocalization.AtPrime.ringKrullDim_eq_height (I : Ideal R) [I.IsPrime] (A : Type*)
    [CommRing A] [Algebra R A] [IsLocalization.AtPrime A I] :
    ringKrullDim A = I.height := by
  have := IsLocalization.AtPrime.isLocalRing A I
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]; rw [← IsLocalization.height_under I.primeCompl]; rw [← IsLocalization.AtPrime.under_maximalIdeal A I]

/--
lemma `IsLocalization.height_map_of_disjoint` / 引理 `IsLocalization.height_map_of_disjoint`

English:
lemma IsLocalization.height_map_of_disjoint
  statement: {S : Type*} [CommRing S] [Algebra R S] (M : Submonoid R)
  proof: by
  let P := p.map (algebraMap R S)
  have : P.IsPrime := isPrime_of_isPrime_disjoint M S p ‹_› h
  have := isLocalization_isLocalization_atPrime_isLocalization (M := M) (Localization.AtPrime P) P
  simp_rw [P, under_map_of_isPrime_disjoint M S _ h] at this
  have := ringKrullDim_eq_of_ringEquiv (I

中文:
引理 是Localization.height_map_of_disjoint
  结论: {S : 类型} [交换环 S] [代数 R S] (M : 子幺半群 R)
  证明: by
  let P := p.map (algebraMap R S)
  have : P.IsPrime := isPrime_of_isPrime_disjoint M S p ‹_› h
  have := isLocalization_isLocalization_atPrime_isLocalization (M := M) (Localization.AtPrime P) P
  simp_rw [P, under_map_of_isPrime_disjoint M S _ h] at this
  have := ringKrullDim_eq_of_ringEquiv (I

Depends on / 依赖: AtPrime, AtPrime.ringKrullDim_eq_height, IsLocalization, IsLocalization.algEquiv, IsPrime, Localization, Localization.AtPrime, P.IsPrime, WithBot, WithBot.coe_eq_coe.m, algEquiv, algebraMap, coe_eq_coe, isLocalization_isLocalization_atPrime_isLocalization, isPrime_of_isPrime_disjoint, p.map, p.primeCompl, primeCompl, ringKrullDim_eq_height, ringKrullDim_eq_of_ringEquiv
-/
lemma IsLocalization.height_map_of_disjoint {S : Type*} [CommRing S] [Algebra R S] (M : Submonoid R)
    [IsLocalization M S] (p : Ideal R) [p.IsPrime] (h : Disjoint (M : Set R) (p : Set R)) :
    (p.map <| algebraMap R S).height = p.height := by
  let P := p.map (algebraMap R S)
  have : P.IsPrime := isPrime_of_isPrime_disjoint M S p ‹_› h
  have := isLocalization_isLocalization_atPrime_isLocalization (M := M) (Localization.AtPrime P) P
  simp_rw [P, under_map_of_isPrime_disjoint M S _ h] at this
  have := ringKrullDim_eq_of_ringEquiv (IsLocalization.algEquiv p.primeCompl
    (Localization.AtPrime P) (Localization.AtPrime p)).toRingEquiv
  rw [AtPrime.ringKrullDim_eq_height P]; rw [AtPrime.ringKrullDim_eq_height p] at this
  exact WithBot.coe_eq_coe.mp this

@[deprecated "Use `mem_minimalPrimes_of_height_le` instead." (since := "2026-04-02")]
/--
lemma `mem_minimalPrimes_of_primeHeight_eq_height` / 引理 `mem_minimalPrimes_of_primeHeight_eq_height`

English:
lemma mem_minimalPrimes_of_primeHeight_eq_height
  statement: {I J : Ideal R} [J.IsPrime] (e : I <= J)
  proof: by
  rw [← J.height_eq_primeHeight] at e'
  exact mem_minimalPrimes_of_height_le e (e' ▸ le_refl _)

中文:
引理 mem_minimalPrimes_of_primeHeight_eq_height
  结论: {I J : 理想 R} [J.是素] (e : I <= J)
  证明: by
  rw [← J.height_eq_primeHeight] at e'
  exact mem_minimalPrimes_of_height_le e (e' ▸ le_refl _)
-/
private lemma mem_minimalPrimes_of_primeHeight_eq_height {I J : Ideal R} [J.IsPrime] (e : I <= J)
    (e' : J.primeHeight = I.height) [J.FiniteHeight] : J in I.minimalPrimes := by
  rw [← J.height_eq_primeHeight] at e'
  exact mem_minimalPrimes_of_height_le e (e' ▸ le_refl _)

/--
lemma `exists_spanRank_le_and_le_height_of_le_height` / 引理 `exists_spanRank_le_and_le_height_of_le_height`

English:
lemma exists_spanRank_le_and_le_height_of_le_height
  statement: [IsNoetherianRing R] (I : Ideal R) (r : Nat)
  proof: by
  induction r with
  | zero => simp
  | succ r ih =>
    obtain ⟨J, h₁, h₂, h₃⟩ := ih ((WithTop.coe_le_coe.mpr r.le_succ).trans hr)
    let S := { K | K in J.minimalPrimes ∧ Ideal.height K = r }
    have hS : Set.Finite S := Set.Finite.subset J.finite_minimalPrimes_of_isNoetherianRing
      (fun 

中文:
引理 存在_spanRank_le_and_le_height_of_le_height
  结论: [是Noether环 R] (I : 理想 R) (r : 自然数)
  证明: by
  induction r with
  | zero => simp
  | succ r ih =>
    obtain ⟨J, h₁, h₂, h₃⟩ := ih ((WithTop.coe_le_coe.mpr r.le_succ).trans hr)
    let S := { K | K in J.minimalPrimes ∧ Ideal.height K = r }
    have hS : Set.Finite S := Set.Finite.subset J.finite_minimalPrimes_of_isNoetherianRing
      (fun 

Depends on / 依赖: Finite, Ideal.height, Ideal.subset_union_prime, J.finite_minimalPrimes_of_isNoetherianRing, J.minimalPrimes, Set.Finite, Set.Finite.mem_toFinset, Set.Finite.subset, WithTop, WithTop.coe_le_coe.mpr, coe_le_coe, finite_minimalPrimes_of_isNoetherianRing, hS.toFinset, height, isPrime, le_succ, mem_toFinset, minimalPrimes, not.mpr, r.le_succ
-/
lemma exists_spanRank_le_and_le_height_of_le_height [IsNoetherianRing R] (I : Ideal R) (r : Nat)
    (hr : r <= I.height) : exists J <= I, J.spanRank <= r ∧ r <= J.height := by
  induction r with
  | zero => simp
  | succ r ih =>
    obtain ⟨J, h₁, h₂, h₃⟩ := ih ((WithTop.coe_le_coe.mpr r.le_succ).trans hr)
    let S := { K | K in J.minimalPrimes ∧ Ideal.height K = r }
    have hS : Set.Finite S := Set.Finite.subset J.finite_minimalPrimes_of_isNoetherianRing
      (fun _ h => h.1)
    have : ¬(I : Set R) subseteq ⋃ K in hS.toFinset, (K : Set R) := by
      refine (Ideal.subset_union_prime ⊥ ⊥ ?_).not.mpr ?_
      · rintro K hK - -
        rw [Set.Finite.mem_toFinset] at hK
        exact hK.1.isPrime
      · push Not
        intro K hK e
        have := hr.trans (Ideal.height_mono e)
        rw [Set.Finite.mem_toFinset] at hK
        rw [hK.2]; rw [← not_lt] at this
        norm_cast at this
        exact this r.lt_succ_self
    simp_rw [Set.not_subset, Set.mem_iUnion, not_exists, Set.Finite.mem_toFinset] at this
    obtain ⟨x, hx₁, hx₂⟩ := this
    refine ⟨J ⊔ Ideal.span {x}, sup_le h₁ ?_, ?_, ?_⟩
    · rwa [Ideal.span_le, Set.singleton_subset_iff]
    · apply Submodule.spanRank_sup_le_sum_spanRank.trans
      push_cast
      exact add_le_add h₂ ((Submodule.spanRank_span_le_card _).trans (by simp))
    · refine le_iInf₂ (fun p hp => ?_)
      have := hp.isPrime
      rw [← p.height_eq_primeHeight]
      by_cases h : p.height = ⊤
      · exact le_of_le_of_eq le_top h.symm
      have : p.FiniteHeight := ⟨Or.inr h⟩
      have := Ideal.height_mono (le_sup_left.trans hp.le)
      suffices h : (r : Nat∞) != p.height by
        exact Order.add_one_le_of_lt (lt_of_le_of_ne (h₃.trans this) h)
      intro e
      apply hx₂ p
      · refine ⟨mem_minimalPrimes_of_height_le (le_sup_left.trans hp.le) (e.symm.trans_le h₃),
          e.symm⟩
· apply hp.le Ideal.mem_sup_right mem_span_singleton_self x

/--
lemma `Ideal.sup_height_eq_ringKrullDim` / 引理 `Ideal.sup_height_eq_ringKrullDim`

English:
lemma Ideal.sup_height_eq_ringKrullDim
  given: [Nontrivial R]
  proof: by
  apply le_antisymm
  · rw [WithBot.coe_iSup ⟨⊤, fun _ _ => le_top⟩]
    refine iSup_le fun I => ?_
    by_cases h : I = ⊤
    · simp [h, ringKrullDim_nonneg_of_nontrivial]
    · simp [h, height_le_ringKrullDim_of_ne_top]
  · refine iSup_le fun p => WithBot.coe_le_coe.mpr (le_trans (b := p.last.a

中文:
引理 理想.sup_height_eq_ringKrullDim
  条件: [非平凡 R]
  证明: by
  apply le_antisymm
  · rw [WithBot.coe_iSup ⟨⊤, fun _ _ => le_top⟩]
    refine iSup_le fun I => ?_
    by_cases h : I = ⊤
    · simp [h, ringKrullDim_nonneg_of_nontrivial]
    · simp [h, height_le_ringKrullDim_of_ne_top]
  · refine iSup_le fun p => WithBot.coe_le_coe.mpr (le_trans (b := p.last.a

Depends on / 依赖: WithBot, WithBot.coe_iSup, WithBot.coe_le_coe.mpr, asIdeal, coe_iSup, coe_le_coe, height, height_eq_primeHeight, height_le_ringKrullDim_of_ne_top, iSup_le, le_antisymm, le_iSup, le_rfl, le_top, le_trans, length, p.last, p.last.asIdeal.height, p.length, ringKrullDim_nonneg_of_nontrivial
-/
lemma Ideal.sup_height_eq_ringKrullDim [Nontrivial R] :
    ↑(⨆ (I : Ideal R) (_ : I != ⊤), I.height) = ringKrullDim R := by
  apply le_antisymm
  · rw [WithBot.coe_iSup ⟨⊤, fun _ _ => le_top⟩]
    refine iSup_le fun I => ?_
    by_cases h : I = ⊤
    · simp [h, ringKrullDim_nonneg_of_nontrivial]
    · simp [h, height_le_ringKrullDim_of_ne_top]
  · refine iSup_le fun p => WithBot.coe_le_coe.mpr (le_trans (b := p.last.asIdeal.height) ?_ ?_)
    · rw [height_eq_primeHeight]
      apply le_trans (b := ⨆ (_ : p.last <= p.last), ↑p.length)
      · exact le_iSup (fun _ => (↑p.length : Nat∞)) le_rfl
      · exact le_iSup (fun p' => (⨆ _, p'.length : Nat∞)) p
    · apply le_trans (b := ⨆ (_ : (p.last).asIdeal != ⊤), p.last.asIdeal.height)
      · exact le_iSup_of_le p.last.isPrime.ne_top' le_rfl
      · exact le_iSup (fun I => ⨆ _, I.height) p.last.asIdeal

/--
lemma `Ideal.sup_isPrime_height_eq_ringKrullDim` / 引理 `Ideal.sup_isPrime_height_eq_ringKrullDim`

English:
lemma Ideal.sup_isPrime_height_eq_ringKrullDim
  given: [Nontrivial R]
  proof: by
  rw [← sup_height_eq_ringKrullDim]; rw [WithBot.coe_inj]
  apply le_antisymm
  · exact iSup_mono fun I => iSup_mono' fun hI => ⟨hI.ne_top, le_refl _⟩
  · refine iSup_mono' fun I => ?_
    by_cases I_top : I = ⊤
    · exact ⟨⊥, by simp [I_top]⟩
    · obtain ⟨P, hP⟩ := Set.nonempty_coe_sort.mp (no

中文:
引理 理想.sup_isPrime_height_eq_ringKrullDim
  条件: [非平凡 R]
  证明: by
  rw [← sup_height_eq_ringKrullDim]; rw [WithBot.coe_inj]
  apply le_antisymm
  · exact iSup_mono fun I => iSup_mono' fun hI => ⟨hI.ne_top, le_refl _⟩
  · refine iSup_mono' fun I => ?_
    by_cases I_top : I = ⊤
    · exact ⟨⊥, by simp [I_top]⟩
    · obtain ⟨P, hP⟩ := Set.nonempty_coe_sort.mp (no

Depends on / 依赖: I_top, Ideal.height_eq_primeHeight, Set.nonempty_coe_sort.mp, WithBot, WithBot.coe_inj, coe_inj, ge_of_eq, hI.ne_top, hP.isPrime, hP.left.left, height_eq_primeHeight, iInf_le_of_le, iSup_mono, iSup_pos, isPrime, le_antisymm, le_iSup_of_le, le_refl, ne_top, nonempty_coe_sort
-/
lemma Ideal.sup_isPrime_height_eq_ringKrullDim [Nontrivial R] :
    ↑(⨆ (I : Ideal R) (_ : I.IsPrime), I.height) = ringKrullDim R := by
  rw [← sup_height_eq_ringKrullDim]; rw [WithBot.coe_inj]
  apply le_antisymm
  · exact iSup_mono fun I => iSup_mono' fun hI => ⟨hI.ne_top, le_refl _⟩
  · refine iSup_mono' fun I => ?_
    by_cases I_top : I = ⊤
    · exact ⟨⊥, by simp [I_top]⟩
    · obtain ⟨P, hP⟩ := Set.nonempty_coe_sort.mp (nonempty_minimalPrimes I_top)
      refine ⟨P, iSup_pos (α := Nat∞) I_top ▸ le_iSup_of_le (hP.left.left) ?_⟩
      have := hP.isPrime
      exact iInf_le_of_le P (iInf_le_of_le hP (ge_of_eq (Ideal.height_eq_primeHeight P)))

@[deprecated "Use `Ideal.sup_height_isPrime_eq_ringKrullDim` instead." (since := "2026-04-02")]
/--
lemma `Ideal.sup_primeHeight_eq_ringKrullDim` / 引理 `Ideal.sup_primeHeight_eq_ringKrullDim`

English:
lemma Ideal.sup_primeHeight_eq_ringKrullDim
  given: [Nontrivial R]
  proof: by
  simp [← Ideal.height_eq_primeHeight, Ideal.sup_isPrime_height_eq_ringKrullDim]

中文:
引理 理想.sup_primeHeight_eq_ringKrullDim
  条件: [非平凡 R]
  证明: by
  simp [← Ideal.height_eq_primeHeight, Ideal.sup_isPrime_height_eq_ringKrullDim]
-/
private lemma Ideal.sup_primeHeight_eq_ringKrullDim [Nontrivial R] :
    ↑(⨆ (I : Ideal R) (_ : I.IsPrime), I.primeHeight) = ringKrullDim R := by
  simp [← Ideal.height_eq_primeHeight, Ideal.sup_isPrime_height_eq_ringKrullDim]

/--
lemma `Ideal.sup_isMaximal_height_eq_ringKrullDim` / 引理 `Ideal.sup_isMaximal_height_eq_ringKrullDim`

English:
lemma Ideal.sup_isMaximal_height_eq_ringKrullDim
  given: [Nontrivial R]
  proof: by
  rw [← Ideal.sup_height_eq_ringKrullDim]; rw [WithBot.coe_inj]
  apply le_antisymm
  · exact iSup_mono fun I => iSup_mono' fun hI => ⟨hI.isPrime.ne_top , le_rfl⟩
  · refine iSup_mono' fun I => ?_
    obtain rfl | I_top := eq_or_ne I ⊤
    · exact ⟨⊥, by grind [iSup_le_iff, Ideal.IsPrime.ne_top]⟩

中文:
引理 理想.sup_isMaximal_height_eq_ringKrullDim
  条件: [非平凡 R]
  证明: by
  rw [← Ideal.sup_height_eq_ringKrullDim]; rw [WithBot.coe_inj]
  apply le_antisymm
  · exact iSup_mono fun I => iSup_mono' fun hI => ⟨hI.isPrime.ne_top , le_rfl⟩
  · refine iSup_mono' fun I => ?_
    obtain rfl | I_top := eq_or_ne I ⊤
    · exact ⟨⊥, by grind [iSup_le_iff, Ideal.IsPrime.ne_top]⟩

Depends on / 依赖: I_top, Ideal.IsPrime.ne_top, Ideal.sup_height_eq_ringKrullDim, IsPrime, WithBot, WithBot.coe_inj, coe_inj, eq_or_ne, exists_le_maximal, hI.isPrime.ne_top, height_mono, iSup_le_iff, iSup_mono, isPrime, le_antisymm, le_rfl, ne_top, sup_height_eq_ringKrullDim
-/
lemma Ideal.sup_isMaximal_height_eq_ringKrullDim [Nontrivial R] :
    ↑(⨆ (I : Ideal R) (_ : I.IsMaximal), I.height) = ringKrullDim R := by
  rw [← Ideal.sup_height_eq_ringKrullDim]; rw [WithBot.coe_inj]
  apply le_antisymm
  · exact iSup_mono fun I => iSup_mono' fun hI => ⟨hI.isPrime.ne_top , le_rfl⟩
  · refine iSup_mono' fun I => ?_
    obtain rfl | I_top := eq_or_ne I ⊤
    · exact ⟨⊥, by grind [iSup_le_iff, Ideal.IsPrime.ne_top]⟩
    · obtain ⟨M, hM, hIM⟩ := exists_le_maximal I I_top
      exact ⟨M, iSup_mono' (fun hI => ⟨hM, height_mono hIM⟩)⟩

@[deprecated "Use `Ideal.sup_height_of_maximal_eq_ringKrullDim` instead." (since := "2026-04-02")]
/--
lemma `Ideal.sup_primeHeight_of_maximal_eq_ringKrullDim` / 引理 `Ideal.sup_primeHeight_of_maximal_eq_ringKrullDim`

English:
lemma Ideal.sup_primeHeight_of_maximal_eq_ringKrullDim
  given: [Nontrivial R]
  proof: by
  simp_rw [← Ideal.height_eq_primeHeight, Ideal.sup_isMaximal_height_eq_ringKrullDim]

中文:
引理 理想.sup_primeHeight_of_maximal_eq_ringKrullDim
  条件: [非平凡 R]
  证明: by
  simp_rw [← Ideal.height_eq_primeHeight, Ideal.sup_isMaximal_height_eq_ringKrullDim]
-/
private lemma Ideal.sup_primeHeight_of_maximal_eq_ringKrullDim [Nontrivial R] :
    ↑(⨆ (I : Ideal R) (_ : I.IsMaximal), I.primeHeight) = ringKrullDim R := by
  simp_rw [← Ideal.height_eq_primeHeight, Ideal.sup_isMaximal_height_eq_ringKrullDim]

section isLocalization

variable
  (Rₚ : forall (P : Ideal R) [P.IsMaximal], Type*)
  [forall (P : Ideal R) [P.IsMaximal], CommRing (Rₚ P)]
  [forall (P : Ideal R) [P.IsMaximal], Algebra R (Rₚ P)]
  [forall (P : Ideal R) [P.IsMaximal], IsLocalization.AtPrime (Rₚ P) P]

/--
lemma `Ring.krullDimLE_of_isLocalization_maximal` / 引理 `Ring.krullDimLE_of_isLocalization_maximal`

English:
lemma Ring.krullDimLE_of_isLocalization_maximal
  statement: {n : Nat}
  proof: by
  simp_rw [Ring.krullDimLE_iff] at h ⊢
  nontriviality R
  rw [← Ideal.sup_isMaximal_height_eq_ringKrullDim]
  refine (WithBot.coe_le_coe).mpr (iSup₂_le_iff.mpr fun P hP => ?_)
  rw [← WithBot.coe_le_coe]; rw [← IsLocalization.AtPrime.ringKrullDim_eq_height P (Rₚ P)]
  exact h P

中文:
引理 环.krullDimLE_of_isLocalization_maximal
  结论: {n : 自然数}
  证明: by
  simp_rw [Ring.krullDimLE_iff] at h ⊢
  nontriviality R
  rw [← Ideal.sup_isMaximal_height_eq_ringKrullDim]
  refine (WithBot.coe_le_coe).mpr (iSup₂_le_iff.mpr fun P hP => ?_)
  rw [← WithBot.coe_le_coe]; rw [← IsLocalization.AtPrime.ringKrullDim_eq_height P (Rₚ P)]
  exact h P

Depends on / 依赖: AtPrime, Ideal.sup_isMaximal_height_eq_ringKrullDim, IsLocalization, IsLocalization.AtPrime.ringKrullDim_eq_height, Ring.krullDimLE_iff, WithBot, WithBot.coe_le_coe, _le_iff.mpr, coe_le_coe, krullDimLE_iff, nontriviality, ringKrullDim_eq_height, simp_rw, sup_isMaximal_height_eq_ringKrullDim
-/
lemma Ring.krullDimLE_of_isLocalization_maximal {n : Nat}
    (h : forall (P : Ideal R) [P.IsMaximal], Ring.KrullDimLE n (Rₚ P)) :
    Ring.KrullDimLE n R := by
  simp_rw [Ring.krullDimLE_iff] at h ⊢
  nontriviality R
  rw [← Ideal.sup_isMaximal_height_eq_ringKrullDim]
  refine (WithBot.coe_le_coe).mpr (iSup₂_le_iff.mpr fun P hP => ?_)
  rw [← WithBot.coe_le_coe]; rw [← IsLocalization.AtPrime.ringKrullDim_eq_height P (Rₚ P)]
  exact h P

end isLocalization

/--
lemma `Ideal.eq_span_singleton_of_height_eq_one` / 引理 `Ideal.eq_span_singleton_of_height_eq_one`

English:
lemma Ideal.eq_span_singleton_of_height_eq_one
  statement: [IsDomain R] {p : Ideal R} [p.IsPrime]
  proof: by
  have : (span {x}).IsPrime := by simp [span_singleton_prime hxp.ne_zero, hxp]
  have : p.FiniteHeight := by simp [p.finiteHeight_iff, h1]
  by_contra! hne
  apply hxp.ne_zero
  rw [← span_singleton_eq_bot]; rw [← height_eq_zero_iff_eq_bot]; rw [← Order.lt_one_iff]; rw [← h1]
  refine height_stri

中文:
引理 理想.eq_span_singleton_of_height_eq_one
  结论: [是整环 R] {p : 理想 R} [p.是素]
  证明: by
  have : (span {x}).IsPrime := by simp [span_singleton_prime hxp.ne_zero, hxp]
  have : p.FiniteHeight := by simp [p.finiteHeight_iff, h1]
  by_contra! hne
  apply hxp.ne_zero
  rw [← span_singleton_eq_bot]; rw [← height_eq_zero_iff_eq_bot]; rw [← Order.lt_one_iff]; rw [← h1]
  refine height_stri

Depends on / 依赖: FiniteHeight, IsPrime, Order.lt_one_iff, finiteHeight_iff, height_eq_zero_iff_eq_bot, height_strict_mono_of_isPrime_of_isPrime, hne.symm, hxp.ne_zero, lt_of_le_of_ne, lt_one_iff, ne_zero, p.FiniteHeight, p.finiteHeight_iff, p.span_singleton_le_iff_mem, span_singleton_eq_bot, span_singleton_le_iff_mem, span_singleton_prime
-/
lemma Ideal.eq_span_singleton_of_height_eq_one [IsDomain R] {p : Ideal R} [p.IsPrime]
    (h1 : p.height = 1) {x : R} (hx : x in p) (hxp : Prime x) : p = span {x} := by
  have : (span {x}).IsPrime := by simp [span_singleton_prime hxp.ne_zero, hxp]
  have : p.FiniteHeight := by simp [p.finiteHeight_iff, h1]
  by_contra! hne
  apply hxp.ne_zero
  rw [← span_singleton_eq_bot]; rw [← height_eq_zero_iff_eq_bot]; rw [← Order.lt_one_iff]; rw [← h1]
  refine height_strict_mono_of_isPrime_of_isPrime (lt_of_le_of_ne ?_ hne.symm)
  simp only [p.span_singleton_le_iff_mem, hx]
