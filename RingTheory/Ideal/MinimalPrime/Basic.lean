/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Ideal.IsPrimary
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.Order.Minimal

/-!

# Minimal primes

We provide various results concerning the minimal primes above an ideal.

## Main results
- `Ideal.minimalPrimes`: `I.minimalPrimes` is the set of ideals that are minimal primes over `I`.
- `minimalPrimes`: `minimalPrimes R` is the set of minimal primes of `R`.
- `Ideal.exists_minimalPrimes_le`: Every prime ideal over `I` contains a minimal prime over `I`.
- `Ideal.radical_minimalPrimes`: The minimal primes over `I.radical` are precisely
  the minimal primes over `I`.
- `Ideal.sInf_minimalPrimes`: The intersection of minimal primes over `I` is `I.radical`.

Further results that need the theory of localizations can be found in
`Mathlib/RingTheory/Ideal/MinimalPrime/Localization.lean`.

-/

@[expose] public section

assert_not_exists Localization -- See `Mathlib/RingTheory/Ideal/MinimalPrime/Localization.lean`

section

variable {R S : Type*} [CommSemiring R] [CommSemiring S] (I J : Ideal R)

/--
Definition of `Ideal.IsMinimalPrime` / `Ideal.IsMinimalPrime` 的定义

English:
definition Ideal.IsMinimalPrime
  signature: (p : Ideal R)
  body: Minimal (fun q => q.IsPrime ∧ I <= q) p

中文:
定义 Ideal.IsMinimalPrime
  签名: (p : Ideal R)
  定义体: Minimal (fun q => q.IsPrime ∧ I <= q) p
-/
protected def Ideal.IsMinimalPrime (p : Ideal R) : Prop := Minimal (fun q => q.IsPrime ∧ I <= q) p

variable {I} in
/--
lemma `Ideal.IsMinimalPrime.isPrime` / 引理 `Ideal.IsMinimalPrime.isPrime`

English:
lemma Ideal.IsMinimalPrime.isPrime
  given: {p : Ideal R} (h : I.IsMinimalPrime p)
  statement: p.IsPrime
  proof: h.1.1

中文:
引理 Ideal.IsMinimalPrime.isPrime
  条件: {p : Ideal R} (h : I.IsMinimalPrime p)
  结论: p.IsPrime
  证明: h.1.1
-/
lemma Ideal.IsMinimalPrime.isPrime {p : Ideal R} (h : I.IsMinimalPrime p) : p.IsPrime := h.1.1

variable {I} in
/--
lemma `Ideal.IsMinimalPrime.le` / 引理 `Ideal.IsMinimalPrime.le`

English:
lemma Ideal.IsMinimalPrime.le
  given: {p : Ideal R} (h : I.IsMinimalPrime p)
  statement: I <= p
  proof: h.1.2

中文:
引理 Ideal.IsMinimalPrime.le
  条件: {p : Ideal R} (h : I.IsMinimalPrime p)
  结论: I <= p
  证明: h.1.2
-/
lemma Ideal.IsMinimalPrime.le {p : Ideal R} (h : I.IsMinimalPrime p) : I <= p := h.1.2

/--
Definition of `IsMinimalPrime` / `IsMinimalPrime` 的定义

English:
abbreviation IsMinimalPrime
  signature: (p : Ideal R)
  body: (⊥ : Ideal R).IsMinimalPrime p

中文:
缩写 IsMinimalPrime
  签名: (p : Ideal R)
  定义体: (⊥ : Ideal R).IsMinimalPrime p

Depends on / 依赖: IsMinimalPrime
-/
abbrev IsMinimalPrime (p : Ideal R) : Prop := (⊥ : Ideal R).IsMinimalPrime p

/--
lemma `IsMinimalPrime.isPrime` / 引理 `IsMinimalPrime.isPrime`

English:
lemma IsMinimalPrime.isPrime
  given: {p : Ideal R} (h : IsMinimalPrime p)
  statement: p.IsPrime
  proof: h.1.1

中文:
引理 IsMinimalPrime.isPrime
  条件: {p : Ideal R} (h : IsMinimalPrime p)
  结论: p.IsPrime
  证明: h.1.1
-/
lemma IsMinimalPrime.isPrime {p : Ideal R} (h : IsMinimalPrime p) : p.IsPrime := h.1.1

/--
lemma `IsMinimalPrime.iff_minimal` / 引理 `IsMinimalPrime.iff_minimal`

English:
lemma IsMinimalPrime.iff_minimal
  given: (p : Ideal R)
  statement: IsMinimalPrime p ↔ Minimal Ideal.IsPrime p
  proof: by
  simp [Ideal.IsMinimalPrime]

中文:
引理 IsMinimalPrime.iff_minimal
  条件: (p : Ideal R)
  结论: IsMinimalPrime p ↔ Minimal Ideal.IsPrime p
  证明: by
  simp [Ideal.IsMinimalPrime]

Depends on / 依赖: Ideal.IsMinimalPrime, IsMinimalPrime
-/
lemma IsMinimalPrime.iff_minimal (p : Ideal R) : IsMinimalPrime p ↔ Minimal Ideal.IsPrime p := by
  simp [Ideal.IsMinimalPrime]

/--
Definition of `Ideal.minimalPrimes` / `Ideal.minimalPrimes` 的定义

English:
abbreviation Ideal.minimalPrimes
  signature: : Set (Ideal R)
  body: {p | I.IsMinimalPrime p}

中文:
缩写 Ideal.minimalPrimes
  签名: : Set (Ideal R)
  定义体: {p | I.IsMinimalPrime p}
-/
protected abbrev Ideal.minimalPrimes : Set (Ideal R) :=
  {p | I.IsMinimalPrime p}

variable (R) in
/--
Definition of `minimalPrimes` / `minimalPrimes` 的定义

English:
abbreviation minimalPrimes
  signature: : Set (Ideal R)
  body: {p | IsMinimalPrime p}

中文:
缩写 minimalPrimes
  签名: : Set (Ideal R)
  定义体: {p | IsMinimalPrime p}

Depends on / 依赖: IsMinimalPrime
-/
abbrev minimalPrimes : Set (Ideal R) :=
  {p | IsMinimalPrime p}

/--
lemma `minimalPrimes_eq_minimals` / 引理 `minimalPrimes_eq_minimals`

English:
lemma minimalPrimes_eq_minimals
  statement: minimalPrimes R = {x | Minimal Ideal.IsPrime x}
  proof: congr_arg Minimal (by simp)

中文:
引理 minimalPrimes_eq_minimals
  结论: minimalPrimes R = {x | Minimal Ideal.IsPrime x}
  证明: congr_arg Minimal (by simp)

Depends on / 依赖: Minimal, congr_arg
-/
lemma minimalPrimes_eq_minimals : minimalPrimes R = {x | Minimal Ideal.IsPrime x} :=
  congr_arg Minimal (by simp)

variable {I J}

@[deprecated "Use `Ideal.IsMinimalPrime.isPrime` instead." (since := "2026-05-08")]
/--
theorem `Ideal.minimalPrimes_isPrime` / 定理 `Ideal.minimalPrimes_isPrime`

English:
theorem Ideal.minimalPrimes_isPrime
  given: {p : Ideal R} (h : p in minimalPrimes R)
  statement: p.IsPrime
  proof: h.1.1

中文:
定理 Ideal.minimalPrimes_isPrime
  条件: {p : Ideal R} (h : p in minimalPrimes R)
  结论: p.IsPrime
  证明: h.1.1
-/
theorem Ideal.minimalPrimes_isPrime {p : Ideal R} (h : p in minimalPrimes R) : p.IsPrime :=
  h.1.1

/--
theorem `Ideal.exists_minimalPrimes_le` / 定理 `Ideal.exists_minimalPrimes_le`

English:
theorem Ideal.exists_minimalPrimes_le
  given: [J.IsPrime] (e : I <= J)
  statement: exists p in I.minimalPrimes, p <= J
  proof: by
  set S := { p : (Ideal R)ᵒᵈ | Ideal.IsPrime p ∧ I <= OrderDual.ofDual p }
  suffices h : exists m, OrderDual.toDual J <= m ∧ Maximal (· in S) m by
    obtain ⟨p, hJp, hp⟩ := h
    exact ⟨p, ⟨hp.prop, fun q hq hle => hp.le_of_ge hq hle⟩, hJp⟩
  apply zorn_le_nonempty₀
  swap
  · refine ⟨show J.Is

中文:
定理 Ideal.exists_minimalPrimes_le
  条件: [J.IsPrime] (e : I <= J)
  结论: 存在 p in I.minimalPrimes, p <= J
  证明: by
  set S := { p : (Ideal R)ᵒᵈ | Ideal.IsPrime p ∧ I <= OrderDual.ofDual p }
  suffices h : exists m, OrderDual.toDual J <= m ∧ Maximal (· in S) m by
    obtain ⟨p, hJp, hp⟩ := h
    exact ⟨p, ⟨hp.prop, fun q hq hle => hp.le_of_ge hq hle⟩, hJp⟩
  apply zorn_le_nonempty₀
  swap
  · refine ⟨show J.Is

Depends on / 依赖: Ideal.IsPrime, Ideal.sInf_isPrime_of_isChain, IsPrime, J.IsPrime, Maximal, OrderDual, OrderDual.ofDual, OrderDual.ofDual_toDual, OrderDual.toDual, hp.le_of_ge, hp.prop, infer_instance, le_of_ge, ofDual, ofDual_toDual, sInf_isPrime_of_isChain, toDual
-/
theorem Ideal.exists_minimalPrimes_le [J.IsPrime] (e : I <= J) : exists p in I.minimalPrimes, p <= J := by
  set S := { p : (Ideal R)ᵒᵈ | Ideal.IsPrime p ∧ I <= OrderDual.ofDual p }
  suffices h : exists m, OrderDual.toDual J <= m ∧ Maximal (· in S) m by
    obtain ⟨p, hJp, hp⟩ := h
    exact ⟨p, ⟨hp.prop, fun q hq hle => hp.le_of_ge hq hle⟩, hJp⟩
  apply zorn_le_nonempty₀
  swap
  · refine ⟨show J.IsPrime by infer_instance, e⟩
  rintro (c : Set (Ideal R)) hc hc' J' hJ'
  refine
    ⟨OrderDual.toDual (sInf c),
      ⟨Ideal.sInf_isPrime_of_isChain ⟨J', hJ'⟩ hc'.symm fun x hx => (hc hx).1, ?_⟩, ?_⟩
  · rw [OrderDual.ofDual_toDual, le_sInf_iff]
    exact fun _ hx => (hc hx).2
  · rintro z hz
    rw [OrderDual.le_toDual]
    exact sInf_le hz

/--
theorem `Ideal.nonempty_minimalPrimes` / 定理 `Ideal.nonempty_minimalPrimes`

English:
theorem Ideal.nonempty_minimalPrimes
  given: (h : I != ⊤)
  statement: Nonempty I.minimalPrimes
  proof: by
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal I h
  obtain ⟨p, hp, -⟩ := Ideal.exists_minimalPrimes_le hle
  exact ⟨p, hp⟩

中文:
定理 Ideal.nonempty_minimalPrimes
  条件: (h : I != ⊤)
  结论: Nonempty I.minimalPrimes
  证明: by
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal I h
  obtain ⟨p, hp, -⟩ := Ideal.exists_minimalPrimes_le hle
  exact ⟨p, hp⟩

Depends on / 依赖: Ideal.exists_le_maximal, Ideal.exists_minimalPrimes_le, exists_le_maximal, exists_minimalPrimes_le
-/
theorem Ideal.nonempty_minimalPrimes (h : I != ⊤) : Nonempty I.minimalPrimes := by
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal I h
  obtain ⟨p, hp, -⟩ := Ideal.exists_minimalPrimes_le hle
  exact ⟨p, hp⟩

/--
theorem `Ideal.eq_bot_of_minimalPrimes_eq_empty` / 定理 `Ideal.eq_bot_of_minimalPrimes_eq_empty`

English:
theorem Ideal.eq_bot_of_minimalPrimes_eq_empty
  given: (h : I.minimalPrimes = ∅)
  statement: I = ⊤
  proof: by
  by_contra hI
  obtain ⟨p, hp⟩ := Ideal.nonempty_minimalPrimes hI
  exact Set.notMem_empty p (h ▸ hp)

@[simp]

中文:
定理 Ideal.eq_bot_of_minimalPrimes_eq_empty
  条件: (h : I.minimalPrimes = ∅)
  结论: I = ⊤
  证明: by
  by_contra hI
  obtain ⟨p, hp⟩ := Ideal.nonempty_minimalPrimes hI
  exact Set.notMem_empty p (h ▸ hp)

@[simp]

Depends on / 依赖: Ideal.nonempty_minimalPrimes, Set.notMem_empty, nonempty_minimalPrimes, notMem_empty
-/
theorem Ideal.eq_bot_of_minimalPrimes_eq_empty (h : I.minimalPrimes = ∅) : I = ⊤ := by
  by_contra hI
  obtain ⟨p, hp⟩ := Ideal.nonempty_minimalPrimes hI
  exact Set.notMem_empty p (h ▸ hp)

@[simp]
/--
theorem `Ideal.radical_minimalPrimes` / 定理 `Ideal.radical_minimalPrimes`

English:
theorem Ideal.radical_minimalPrimes
  statement: I.radical.minimalPrimes = I.minimalPrimes
  proof: by
  rw [Ideal.minimalPrimes]; rw [Ideal.minimalPrimes]
  ext p
  refine ⟨?_, ?_⟩ <;> rintro ⟨⟨a, ha⟩, b⟩
  · refine ⟨⟨a, a.radical_le_iff.1 ha⟩, ?_⟩
    simp only [and_imp] at *
    exact fun _ h2 h3 h4 => b h2 (h2.radical_le_iff.2 h3) h4
  · refine ⟨⟨a, a.radical_le_iff.2 ha⟩, ?_⟩
    simp only [a

中文:
定理 Ideal.radical_minimalPrimes
  结论: I.radical.minimalPrimes = I.minimalPrimes
  证明: by
  rw [Ideal.minimalPrimes]; rw [Ideal.minimalPrimes]
  ext p
  refine ⟨?_, ?_⟩ <;> rintro ⟨⟨a, ha⟩, b⟩
  · refine ⟨⟨a, a.radical_le_iff.1 ha⟩, ?_⟩
    simp only [and_imp] at *
    exact fun _ h2 h3 h4 => b h2 (h2.radical_le_iff.2 h3) h4
  · refine ⟨⟨a, a.radical_le_iff.2 ha⟩, ?_⟩
    simp only [a

Depends on / 依赖: Ideal.minimalPrimes, a.radical_le_iff, and_imp, h2.radical_le_iff, minimalPrimes, radical_le_iff
-/
theorem Ideal.radical_minimalPrimes : I.radical.minimalPrimes = I.minimalPrimes := by
  rw [Ideal.minimalPrimes]; rw [Ideal.minimalPrimes]
  ext p
  refine ⟨?_, ?_⟩ <;> rintro ⟨⟨a, ha⟩, b⟩
  · refine ⟨⟨a, a.radical_le_iff.1 ha⟩, ?_⟩
    simp only [and_imp] at *
    exact fun _ h2 h3 h4 => b h2 (h2.radical_le_iff.2 h3) h4
  · refine ⟨⟨a, a.radical_le_iff.2 ha⟩, ?_⟩
    simp only [and_imp] at *
    exact fun _ h2 h3 h4 => b h2 (h2.radical_le_iff.1 h3) h4

@[simp]
/--
theorem `Ideal.sInf_minimalPrimes` / 定理 `Ideal.sInf_minimalPrimes`

English:
theorem Ideal.sInf_minimalPrimes
  statement: sInf I.minimalPrimes = I.radical
  proof: by
  rw [I.radical_eq_sInf]
  apply le_antisymm
  · intro x hx
    rw [Ideal.mem_sInf] at hx ⊢
    rintro J ⟨e, hJ⟩
    obtain ⟨p, hp, hp'⟩ := Ideal.exists_minimalPrimes_le e
    exact hp' (hx hp)
  · apply sInf_le_sInf _
    intro I hI
    exact hI.1.symm

中文:
定理 Ideal.sInf_minimalPrimes
  结论: sInf I.minimalPrimes = I.radical
  证明: by
  rw [I.radical_eq_sInf]
  apply le_antisymm
  · intro x hx
    rw [Ideal.mem_sInf] at hx ⊢
    rintro J ⟨e, hJ⟩
    obtain ⟨p, hp, hp'⟩ := Ideal.exists_minimalPrimes_le e
    exact hp' (hx hp)
  · apply sInf_le_sInf _
    intro I hI
    exact hI.1.symm

Depends on / 依赖: I.radical_eq_sInf, Ideal.exists_minimalPrimes_le, Ideal.mem_sInf, exists_minimalPrimes_le, le_antisymm, mem_sInf, radical_eq_sInf, sInf_le_sInf
-/
theorem Ideal.sInf_minimalPrimes : sInf I.minimalPrimes = I.radical := by
  rw [I.radical_eq_sInf]
  apply le_antisymm
  · intro x hx
    rw [Ideal.mem_sInf] at hx ⊢
    rintro J ⟨e, hJ⟩
    obtain ⟨p, hp, hp'⟩ := Ideal.exists_minimalPrimes_le e
    exact hp' (hx hp)
  · apply sInf_le_sInf _
    intro I hI
    exact hI.1.symm

end

section

variable {R S : Type*} [CommSemiring R] [CommSemiring S] {I J : Ideal R}

/--
theorem `Ideal.minimalPrimes_eq_subsingleton` / 定理 `Ideal.minimalPrimes_eq_subsingleton`

English:
theorem Ideal.minimalPrimes_eq_subsingleton
  given: (hI : I.IsPrimary)
  statement: I.minimalPrimes = {I.radical}
  proof: by
  ext J
  constructor
  · intro H
    have le := H.out.isPrime.radical_le_iff.mpr H.le
    exact (H.2 ⟨Ideal.isPrime_radical hI, Ideal.le_radical⟩ le).antisymm le
  · rintro (rfl : J = I.radical)
    exact ⟨⟨Ideal.isPrime_radical hI, Ideal.le_radical⟩, fun _ H _ => H.1.radical_le_iff.mpr H.2⟩

中文:
定理 Ideal.minimalPrimes_eq_subsingleton
  条件: (hI : I.IsPrimary)
  结论: I.minimalPrimes = {I.radical}
  证明: by
  ext J
  constructor
  · intro H
    have le := H.out.isPrime.radical_le_iff.mpr H.le
    exact (H.2 ⟨Ideal.isPrime_radical hI, Ideal.le_radical⟩ le).antisymm le
  · rintro (rfl : J = I.radical)
    exact ⟨⟨Ideal.isPrime_radical hI, Ideal.le_radical⟩, fun _ H _ => H.1.radical_le_iff.mpr H.2⟩

Depends on / 依赖: H.le, H.out.isPrime.radical_le_iff.mpr, I.radical, Ideal.isPrime_radical, Ideal.le_radical, antisymm, isPrime, isPrime_radical, le_radical, radical, radical_le_iff, radical_le_iff.mpr
-/
theorem Ideal.minimalPrimes_eq_subsingleton (hI : I.IsPrimary) : I.minimalPrimes = {I.radical} := by
  ext J
  constructor
  · intro H
    have le := H.out.isPrime.radical_le_iff.mpr H.le
    exact (H.2 ⟨Ideal.isPrime_radical hI, Ideal.le_radical⟩ le).antisymm le
  · rintro (rfl : J = I.radical)
    exact ⟨⟨Ideal.isPrime_radical hI, Ideal.le_radical⟩, fun _ H _ => H.1.radical_le_iff.mpr H.2⟩

/--
theorem `Ideal.minimalPrimes_eq_subsingleton_self` / 定理 `Ideal.minimalPrimes_eq_subsingleton_self`

English:
theorem Ideal.minimalPrimes_eq_subsingleton_self
  given: [I.IsPrime]
  statement: I.minimalPrimes = {I}
  proof: by
  ext J
  refine ⟨fun H => (H.2 ⟨inferInstance, rfl.le⟩ H.le).antisymm H.le, ?_⟩
  rintro (rfl : J = I)
  exact ⟨⟨inferInstance, rfl.le⟩, fun _ h _ => h.2⟩

中文:
定理 Ideal.minimalPrimes_eq_subsingleton_self
  条件: [I.IsPrime]
  结论: I.minimalPrimes = {I}
  证明: by
  ext J
  refine ⟨fun H => (H.2 ⟨inferInstance, rfl.le⟩ H.le).antisymm H.le, ?_⟩
  rintro (rfl : J = I)
  exact ⟨⟨inferInstance, rfl.le⟩, fun _ h _ => h.2⟩

Depends on / 依赖: H.le, antisymm, rfl.le
-/
theorem Ideal.minimalPrimes_eq_subsingleton_self [I.IsPrime] : I.minimalPrimes = {I} := by
  ext J
  refine ⟨fun H => (H.2 ⟨inferInstance, rfl.le⟩ H.le).antisymm H.le, ?_⟩
  rintro (rfl : J = I)
  exact ⟨⟨inferInstance, rfl.le⟩, fun _ h _ => h.2⟩

variable (R) in
/--
theorem `IsDomain.minimalPrimes_eq_singleton_bot` / 定理 `IsDomain.minimalPrimes_eq_singleton_bot`

English:
theorem IsDomain.minimalPrimes_eq_singleton_bot
  given: [IsDomain R]
  proof: Ideal.minimalPrimes_eq_subsingleton_self

中文:
定理 IsDomain.minimalPrimes_eq_singleton_bot
  条件: [IsDomain R]
  证明: Ideal.minimalPrimes_eq_subsingleton_self

Depends on / 依赖: Ideal.minimalPrimes_eq_subsingleton_self, minimalPrimes_eq_subsingleton_self
-/
theorem IsDomain.minimalPrimes_eq_singleton_bot [IsDomain R] :
    minimalPrimes R = {⊥} :=
  Ideal.minimalPrimes_eq_subsingleton_self

end

section

variable {R : Type*} [CommSemiring R]

/--
theorem `Ideal.minimalPrimes_top` / 定理 `Ideal.minimalPrimes_top`

English:
theorem Ideal.minimalPrimes_top
  statement: (⊤ : Ideal R).minimalPrimes = ∅
  proof: by
  ext p
  simp only [Set.notMem_empty, iff_false]
  intro h
  exact h.isPrime.ne_top (top_le_iff.mp h.le)

中文:
定理 Ideal.minimalPrimes_top
  结论: (⊤ : Ideal R).minimalPrimes = ∅
  证明: by
  ext p
  simp only [Set.notMem_empty, iff_false]
  intro h
  exact h.isPrime.ne_top (top_le_iff.mp h.le)

Depends on / 依赖: Set.notMem_empty, h.isPrime.ne_top, h.le, iff_false, isPrime, ne_top, notMem_empty, top_le_iff, top_le_iff.mp
-/
theorem Ideal.minimalPrimes_top : (⊤ : Ideal R).minimalPrimes = ∅ := by
  ext p
  simp only [Set.notMem_empty, iff_false]
  intro h
  exact h.isPrime.ne_top (top_le_iff.mp h.le)

/--
theorem `Ideal.minimalPrimes_eq_empty_iff` / 定理 `Ideal.minimalPrimes_eq_empty_iff`

English:
theorem Ideal.minimalPrimes_eq_empty_iff
  given: (I : Ideal R)
  proof: by
  constructor
  · intro e
    by_contra h
    have ⟨M, hM, hM'⟩ := Ideal.exists_le_maximal I h
    have ⟨p, hp⟩ := Ideal.exists_minimalPrimes_le hM'
    rw [e] at hp
    apply Set.notMem_empty _ hp.1
  · rintro rfl
    exact Ideal.minimalPrimes_top

中文:
定理 Ideal.minimalPrimes_eq_empty_iff
  条件: (I : Ideal R)
  证明: by
  constructor
  · intro e
    by_contra h
    have ⟨M, hM, hM'⟩ := Ideal.exists_le_maximal I h
    have ⟨p, hp⟩ := Ideal.exists_minimalPrimes_le hM'
    rw [e] at hp
    apply Set.notMem_empty _ hp.1
  · rintro rfl
    exact Ideal.minimalPrimes_top

Depends on / 依赖: Ideal.exists_le_maximal, Ideal.exists_minimalPrimes_le, Ideal.minimalPrimes_top, Set.notMem_empty, exists_le_maximal, exists_minimalPrimes_le, minimalPrimes_top, notMem_empty
-/
theorem Ideal.minimalPrimes_eq_empty_iff (I : Ideal R) :
    I.minimalPrimes = ∅ ↔ I = ⊤ := by
  constructor
  · intro e
    by_contra h
    have ⟨M, hM, hM'⟩ := Ideal.exists_le_maximal I h
    have ⟨p, hp⟩ := Ideal.exists_minimalPrimes_le hM'
    rw [e] at hp
    apply Set.notMem_empty _ hp.1
  · rintro rfl
    exact Ideal.minimalPrimes_top

/--
lemma `Ideal.mem_minimalPrimes_sup` / 引理 `Ideal.mem_minimalPrimes_sup`

English:
lemma Ideal.mem_minimalPrimes_sup
  statement: {R : Type*} [CommRing R] {p I J : Ideal R} [p.IsPrime]
  proof: by
  refine ⟨⟨‹_›, ?_⟩, fun q ⟨_, hq⟩ hqp => ?_⟩
  · rw [sup_le_iff]
    refine ⟨hle, by simpa [hle] using Ideal.comap_mono (f := Ideal.Quotient.mk I) h.le⟩
  · rw [sup_le_iff] at hq
    have h2 : p.map (Quotient.mk I) <= q.map (Quotient.mk I) :=
      h.2 ⟨isPrime_map_quotientMk_of_isPrime hq.1, ma

中文:
引理 Ideal.mem_minimalPrimes_sup
  结论: {R : 类型} [CommRing R] {p I J : Ideal R} [p.IsPrime]
  证明: by
  refine ⟨⟨‹_›, ?_⟩, fun q ⟨_, hq⟩ hqp => ?_⟩
  · rw [sup_le_iff]
    refine ⟨hle, by simpa [hle] using Ideal.comap_mono (f := Ideal.Quotient.mk I) h.le⟩
  · rw [sup_le_iff] at hq
    have h2 : p.map (Quotient.mk I) <= q.map (Quotient.mk I) :=
      h.2 ⟨isPrime_map_quotientMk_of_isPrime hq.1, ma

Depends on / 依赖: Ideal.Quotient.mk, Ideal.comap_mono, Quotient, Quotient.mk, comap_map_quotientMk, comap_mono, h.le, isPrime_map_quotientMk_of_isPrime, map_mono, p.map, q.map, sup_le_iff
-/
lemma Ideal.mem_minimalPrimes_sup {R : Type*} [CommRing R] {p I J : Ideal R} [p.IsPrime]
    (hle : I <= p) (h : p.map (Ideal.Quotient.mk I) in (J.map (Ideal.Quotient.mk I)).minimalPrimes) :
    p in (I ⊔ J).minimalPrimes := by
  refine ⟨⟨‹_›, ?_⟩, fun q ⟨_, hq⟩ hqp => ?_⟩
  · rw [sup_le_iff]
    refine ⟨hle, by simpa [hle] using Ideal.comap_mono (f := Ideal.Quotient.mk I) h.le⟩
  · rw [sup_le_iff] at hq
    have h2 : p.map (Quotient.mk I) <= q.map (Quotient.mk I) :=
      h.2 ⟨isPrime_map_quotientMk_of_isPrime hq.1, map_mono hq.2⟩ (map_mono hqp)
    simpa [comap_map_quotientMk, hq.1, sup_le_iff] using comap_mono (f := Ideal.Quotient.mk I) h2

variable {S : Type*} [CommRing S] [Algebra R S]

/--
lemma `Ideal.map_sup_mem_minimalPrimes_of_map_quotientMk_mem_minimalPrimes` / 引理 `Ideal.map_sup_mem_minimalPrimes_of_map_quotientMk_mem_minimalPrimes`

English:
lemma Ideal.map_sup_mem_minimalPrimes_of_map_quotientMk_mem_minimalPrimes
  proof: by
  refine ⟨⟨inferInstance, sup_le_iff.mpr ?_⟩, fun q ⟨_, hleq⟩ hqle => ?_⟩
  · refine ⟨?_, hJP⟩
    rw [Ideal.map_le_iff_le_comap]; rw [← Ideal.under_def]; rw [← Ideal.over_def P p]
    exact hI.le
  · simp only [sup_le_iff] at hleq
    have h1 : p.map (algebraMap R S) <= q := by
      rw [Ideal.m

中文:
引理 Ideal.map_sup_mem_minimalPrimes_of_map_quotientMk_mem_minimalPrimes
  证明: by
  refine ⟨⟨inferInstance, sup_le_iff.mpr ?_⟩, fun q ⟨_, hleq⟩ hqle => ?_⟩
  · refine ⟨?_, hJP⟩
    rw [Ideal.map_le_iff_le_comap]; rw [← Ideal.under_def]; rw [← Ideal.over_def P p]
    exact hI.le
  · simp only [sup_le_iff] at hleq
    have h1 : p.map (algebraMap R S) <= q := by
      rw [Ideal.m

Depends on / 依赖: Ideal.LiesOver.over, Ideal.Quotient.mk, Ideal.comap_mono, Ideal.le_comap_map, Ideal.map_le_iff_le_comap, Ideal.over_def, Ideal.under_def, LiesOver, P.map, Quotient, algebraMap, comap_mono, convert, hI.le, le_comap_map, le_trans, map_le_iff_le_comap, over_def, p.map, sup_le_iff
-/
lemma Ideal.map_sup_mem_minimalPrimes_of_map_quotientMk_mem_minimalPrimes
    {I p : Ideal R} {P : Ideal S} [P.IsPrime] [P.LiesOver p]
    (hI : p in I.minimalPrimes) {J : Ideal S} (hJP : J <= P)
    (hJ : P.map (Ideal.Quotient.mk _) in
      (J.map (Ideal.Quotient.mk (p.map (algebraMap R S)))).minimalPrimes) :
    P in (I.map (algebraMap R S) ⊔ J).minimalPrimes := by
  refine ⟨⟨inferInstance, sup_le_iff.mpr ?_⟩, fun q ⟨_, hleq⟩ hqle => ?_⟩
  · refine ⟨?_, hJP⟩
    rw [Ideal.map_le_iff_le_comap]; rw [← Ideal.under_def]; rw [← Ideal.over_def P p]
    exact hI.le
  · simp only [sup_le_iff] at hleq
    have h1 : p.map (algebraMap R S) <= q := by
      rw [Ideal.map_le_iff_le_comap]
      refine hI.2 ⟨inferInstance, le_trans Ideal.le_comap_map (Ideal.comap_mono hleq.1)⟩ ?_
      convert! Ideal.comap_mono hqle
      exact Ideal.LiesOver.over
    have h2 : P.map (Ideal.Quotient.mk (p.map (algebraMap R S))) <=
        q.map (Ideal.Quotient.mk (p.map (algebraMap R S))) :=
      hJ.2 ⟨Ideal.isPrime_map_quotientMk_of_isPrime h1, Ideal.map_mono hleq.2⟩
        (Ideal.map_mono hqle)
    simpa [h1] using Ideal.comap_mono (f := Ideal.Quotient.mk (p.map (algebraMap R S))) h2

end
