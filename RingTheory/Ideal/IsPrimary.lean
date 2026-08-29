/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yakov Pechersky
-/
module

public import Mathlib.RingTheory.IsPrimary
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Primary ideals

A proper ideal `I` is primary iff `xy ∈ I` implies `x ∈ I` or `y ∈ radical I`.

## Main definitions

- `Ideal.IsPrimary`

## Implementation details

Uses a specialized phrasing of `Submodule.IsPrimary` to have better API-piercing usage.

-/

public section

namespace Ideal

variable {R S : Type*} [CommSemiring R] [CommSemiring S]

/--
Definition of `IsPrimary` / `IsPrimary` 的定义

English:
abbreviation IsPrimary
  signature: (I : Ideal R)
  body: Submodule.IsPrimary I

中文:
缩写 IsPrimary
  签名: (I : Ideal R)
  定义体: Submodule.IsPrimary I

Depends on / 依赖: IsPrimary, Submodule, Submodule.IsPrimary
-/
abbrev IsPrimary (I : Ideal R) : Prop :=
  Submodule.IsPrimary I

/--
lemma `isPrimary_iff` / 引理 `isPrimary_iff`

English:
lemma isPrimary_iff
  given: {I : Ideal R}
  proof: by
  rw [IsPrimary]; rw [Submodule.IsPrimary]; rw [forall_comm]
  simp only [mul_comm, mem_radical_iff,
    ← Submodule.ideal_span_singleton_smul, smul_eq_mul, mul_top, span_singleton_le_iff_mem]

中文:
引理 isPrimary_iff
  条件: {I : Ideal R}
  证明: by
  rw [IsPrimary]; rw [Submodule.IsPrimary]; rw [forall_comm]
  simp only [mul_comm, mem_radical_iff,
    ← Submodule.ideal_span_singleton_smul, smul_eq_mul, mul_top, span_singleton_le_iff_mem]

Depends on / 依赖: IsPrimary, Submodule, Submodule.IsPrimary, Submodule.ideal_span_singleton_smul, forall_comm, ideal_span_singleton_smul, mem_radical_iff, mul_comm, mul_top, smul_eq_mul, span_singleton_le_iff_mem
-/
lemma isPrimary_iff {I : Ideal R} :
    I.IsPrimary ↔ I != ⊤ ∧ forall {x y : R}, x * y in I -> x in I ∨ y in radical I := by
  rw [IsPrimary]; rw [Submodule.IsPrimary]; rw [forall_comm]
  simp only [mul_comm, mem_radical_iff,
    ← Submodule.ideal_span_singleton_smul, smul_eq_mul, mul_top, span_singleton_le_iff_mem]

/--
theorem `IsPrime.isPrimary` / 定理 `IsPrime.isPrimary`

English:
theorem IsPrime.isPrimary
  given: {I : Ideal R} (hi : IsPrime I)
  statement: I.IsPrimary
  proof: isPrimary_iff.mpr
  ⟨hi.1, fun {_ _} hxy => (hi.mem_or_mem hxy).imp id fun hyi => le_radical hyi⟩

中文:
定理 IsPrime.isPrimary
  条件: {I : Ideal R} (hi : IsPrime I)
  结论: I.IsPrimary
  证明: isPrimary_iff.mpr
  ⟨hi.1, fun {_ _} hxy => (hi.mem_or_mem hxy).imp id fun hyi => le_radical hyi⟩

Depends on / 依赖: hi.mem_or_mem, isPrimary_iff, isPrimary_iff.mpr, le_radical, mem_or_mem
-/
theorem IsPrime.isPrimary {I : Ideal R} (hi : IsPrime I) : I.IsPrimary :=
  isPrimary_iff.mpr
  ⟨hi.1, fun {_ _} hxy => (hi.mem_or_mem hxy).imp id fun hyi => le_radical hyi⟩

/--
theorem `isPrime_radical` / 定理 `isPrime_radical`

English:
theorem isPrime_radical
  given: {I : Ideal R} (hi : I.IsPrimary)
  statement: IsPrime (radical I)
  proof: I.colon_univ ▸ hi.isPrime_radical_colon

中文:
定理 isPrime_radical
  条件: {I : Ideal R} (hi : I.IsPrimary)
  结论: IsPrime (radical I)
  证明: I.colon_univ ▸ hi.isPrime_radical_colon

Depends on / 依赖: I.colon_univ, colon_univ, hi.isPrime_radical_colon, isPrime_radical_colon
-/
theorem isPrime_radical {I : Ideal R} (hi : I.IsPrimary) : IsPrime (radical I) :=
  I.colon_univ ▸ hi.isPrime_radical_colon

/--
theorem `isPrimary_of_isMaximal_radical` / 定理 `isPrimary_of_isMaximal_radical`

English:
theorem isPrimary_of_isMaximal_radical
  given: {I : Ideal R} (hi : IsMaximal (radical I))
  proof: by
  rw [isPrimary_iff]
  constructor
  · rintro rfl
    exact (radical_top R ▸ hi).ne_top rfl
  · intro x y hxy
    by_cases h : I + span {y} = ⊤
    · rw [← span_singleton_le_iff_mem, ← mul_top (span {x}), ← h, mul_add,
        span_singleton_mul_span_singleton, add_le_iff, span_singleton_le_iff_m

中文:
定理 isPrimary_of_isMaximal_radical
  条件: {I : Ideal R} (hi : IsMaximal (radical I))
  证明: by
  rw [isPrimary_iff]
  constructor
  · rintro rfl
    exact (radical_top R ▸ hi).ne_top rfl
  · intro x y hxy
    by_cases h : I + span {y} = ⊤
    · rw [← span_singleton_le_iff_mem, ← mul_top (span {x}), ← h, mul_add,
        span_singleton_mul_span_singleton, add_le_iff, span_singleton_le_iff_m

Depends on / 依赖: Or.inl, Or.inr, add_le_iff, eq_of_le, exists_le_maximal, hi.eq_of_le, hm.isPrime.radical_le_iff, hm.ne_top, isPrimary_iff, isPrime, mul_add, mul_le_right, mul_top, ne_top, radical_le_iff, radical_top, span_singleton_le_iff_mem, span_singleton_mul_span_singleton
-/
theorem isPrimary_of_isMaximal_radical {I : Ideal R} (hi : IsMaximal (radical I)) :
    I.IsPrimary := by
  rw [isPrimary_iff]
  constructor
  · rintro rfl
    exact (radical_top R ▸ hi).ne_top rfl
  · intro x y hxy
    by_cases h : I + span {y} = ⊤
    · rw [← span_singleton_le_iff_mem, ← mul_top (span {x}), ← h, mul_add,
        span_singleton_mul_span_singleton, add_le_iff, span_singleton_le_iff_mem]
      exact Or.inl ⟨mul_le_right, hxy⟩
    · obtain ⟨m, hm, hy⟩ := exists_le_maximal (I + span {y}) h
      rw [add_le_iff]; rw [span_singleton_le_iff_mem]; rw [← hm.isPrime.radical_le_iff] at hy
      exact Or.inr (hi.eq_of_le hm.ne_top hy.1 ▸ hy.2)

/--
theorem `IsPrimary.inf` / 定理 `IsPrimary.inf`

English:
theorem IsPrimary.inf
  statement: {I J : Ideal R} (hi : I.IsPrimary) (hj : J.IsPrimary)
  proof: Submodule.IsPrimary.inf hi hj (by simpa)

中文:
定理 IsPrimary.inf
  结论: {I J : Ideal R} (hi : I.IsPrimary) (hj : J.IsPrimary)
  证明: Submodule.IsPrimary.inf hi hj (by simpa)

Depends on / 依赖: IsPrimary, Submodule, Submodule.IsPrimary.inf
-/
theorem IsPrimary.inf {I J : Ideal R} (hi : I.IsPrimary) (hj : J.IsPrimary)
    (hij : radical I = radical J) : (I ⊓ J).IsPrimary :=
  Submodule.IsPrimary.inf hi hj (by simpa)

/--
lemma `isPrimary_finsetInf` / 引理 `isPrimary_finsetInf`

English:
lemma isPrimary_finsetInf
  statement: {ι} {s : Finset ι} {f : ι -> Ideal R} {i : ι} (hi : i in s)
  proof: Submodule.isPrimary_finsetInf hi hs (by simpa)

@[deprecated (since := "2026-01-19")]
alias isPrimary_finset_inf := isPrimary_finsetInf

中文:
引理 isPrimary_finsetInf
  结论: {ι} {s : Finset ι} {f : ι -> Ideal R} {i : ι} (hi : i in s)
  证明: Submodule.isPrimary_finsetInf hi hs (by simpa)

@[deprecated (since := "2026-01-19")]
alias isPrimary_finset_inf := isPrimary_finsetInf

Depends on / 依赖: Submodule, Submodule.isPrimary_finsetInf, isPrimary_finsetInf
-/
lemma isPrimary_finsetInf {ι} {s : Finset ι} {f : ι -> Ideal R} {i : ι} (hi : i in s)
    (hs : forall ⦃y⦄, y in s -> (f y).IsPrimary)
    (hs' : forall ⦃y⦄, y in s -> (f y).radical = (f i).radical) :
    IsPrimary (s.inf f) :=
  Submodule.isPrimary_finsetInf hi hs (by simpa)

@[deprecated (since := "2026-01-19")]
alias isPrimary_finset_inf := isPrimary_finsetInf

/--
lemma `IsPrimary.comap` / 引理 `IsPrimary.comap`

English:
lemma IsPrimary.comap
  given: {I : Ideal S} (hI : I.IsPrimary) (φ : R ->+* S)
  statement: (I.comap φ).IsPrimary
  proof: by
  rw [isPrimary_iff] at hI ⊢
  refine hI.imp (comap_ne_top φ) fun h => ?_
  simp only [mem_comap, map_mul, ← comap_radical]
  exact h

中文:
引理 IsPrimary.comap
  条件: {I : Ideal S} (hI : I.IsPrimary) (φ : R ->+* S)
  结论: (I.comap φ).IsPrimary
  证明: by
  rw [isPrimary_iff] at hI ⊢
  refine hI.imp (comap_ne_top φ) fun h => ?_
  simp only [mem_comap, map_mul, ← comap_radical]
  exact h

Depends on / 依赖: comap_ne_top, comap_radical, hI.imp, isPrimary_iff, map_mul, mem_comap
-/
lemma IsPrimary.comap {I : Ideal S} (hI : I.IsPrimary) (φ : R ->+* S) : (I.comap φ).IsPrimary := by
  rw [isPrimary_iff] at hI ⊢
  refine hI.imp (comap_ne_top φ) fun h => ?_
  simp only [mem_comap, map_mul, ← comap_radical]
  exact h

end Ideal
