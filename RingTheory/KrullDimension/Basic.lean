/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fangming Li, Jujian Zhang
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic -- shake: keep (used in `proof_wanted` only)
public import Mathlib.Order.KrullDimension
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Jacobson.Radical
public import Mathlib.RingTheory.Spectrum.Prime.Basic

/-!
# Krull dimensions of (commutative) rings

Given a commutative ring, its ring-theoretic Krull dimension is the order-theoretic Krull dimension
of its prime spectrum. Unfolding this definition, it is the length of the longest sequence(s) of
prime ideals ordered by strict inclusion.
-/

@[expose] public section

open Order

/--
Definition of `ringKrullDim` / `ringKrullDim` 的定义

English:
definition ringKrullDim
  signature: (R : Type*) [CommSemiring R]
  body: krullDim (PrimeSpectrum R)

中文:
定义 ringKrullDim
  签名: (R : 类型) [CommSemiring R]
  定义体: krullDim (PrimeSpectrum R)

Depends on / 依赖: PrimeSpectrum, krullDim
-/
noncomputable def ringKrullDim (R : Type*) [CommSemiring R] : WithBot Nat∞ :=
  krullDim (PrimeSpectrum R)

/--
Definition of `Ring.KrullDimLE` / `Ring.KrullDimLE` 的定义

English:
abbreviation Ring.KrullDimLE
  signature: (n : Nat) (R : Type*) [CommSemiring R]
  body: Order.KrullDimLE n (PrimeSpectrum R)

中文:
缩写 Ring.KrullDimLE
  签名: (n : 自然数) (R : 类型) [CommSemiring R]
  定义体: Order.KrullDimLE n (PrimeSpectrum R)

Depends on / 依赖: KrullDimLE, Order.KrullDimLE, PrimeSpectrum
-/
abbrev Ring.KrullDimLE (n : Nat) (R : Type*) [CommSemiring R] : Prop :=
  Order.KrullDimLE n (PrimeSpectrum R)

variable {R S : Type*} [CommSemiring R] [CommSemiring S]

/--
lemma `Ring.krullDimLE_iff` / 引理 `Ring.krullDimLE_iff`

English:
lemma Ring.krullDimLE_iff
  given: {n : Nat}
  proof: Order.krullDimLE_iff n (PrimeSpectrum R)

@[nontriviality]

中文:
引理 Ring.krullDimLE_iff
  条件: {n : 自然数}
  证明: Order.krullDimLE_iff n (PrimeSpectrum R)

@[nontriviality]

Depends on / 依赖: Order.krullDimLE_iff, PrimeSpectrum, krullDimLE_iff
-/
lemma Ring.krullDimLE_iff {n : Nat} :
    KrullDimLE n R ↔ ringKrullDim R <= n := Order.krullDimLE_iff n (PrimeSpectrum R)

@[nontriviality]
/--
lemma `ringKrullDim_eq_bot_of_subsingleton` / 引理 `ringKrullDim_eq_bot_of_subsingleton`

English:
lemma ringKrullDim_eq_bot_of_subsingleton
  given: [Subsingleton R]
  proof: krullDim_eq_bot

中文:
引理 ringKrullDim_eq_bot_of_subsingleton
  条件: [Subsingleton R]
  证明: krullDim_eq_bot

Depends on / 依赖: krullDim_eq_bot
-/
lemma ringKrullDim_eq_bot_of_subsingleton [Subsingleton R] :
    ringKrullDim R = ⊥ :=
  krullDim_eq_bot

/--
lemma `ringKrullDim_nonneg_of_nontrivial` / 引理 `ringKrullDim_nonneg_of_nontrivial`

English:
lemma ringKrullDim_nonneg_of_nontrivial
  given: [Nontrivial R]
  proof: krullDim_nonneg

中文:
引理 ringKrullDim_nonneg_of_nontrivial
  条件: [Nontrivial R]
  证明: krullDim_nonneg

Depends on / 依赖: krullDim_nonneg
-/
lemma ringKrullDim_nonneg_of_nontrivial [Nontrivial R] :
    0 <= ringKrullDim R :=
  krullDim_nonneg

/--
theorem `ringKrullDim_le_of_surjective` / 定理 `ringKrullDim_le_of_surjective`

English:
theorem ringKrullDim_le_of_surjective
  given: (f : R ->+* S) (hf : Function.Surjective f)
  proof: krullDim_le_of_strictMono (fun I => ⟨Ideal.comap f I.asIdeal, inferInstance⟩)
    (Monotone.strictMono_of_injective (fun _ _ hab => Ideal.comap_mono hab)
      (fun _ _ h => PrimeSpectrum.ext_iff.mpr <| Ideal.comap_injective_of_surjective f hf <| by
        simpa using h))

中文:
定理 ringKrullDim_le_of_surjective
  条件: (f : R ->+* S) (hf : Function.Surjective f)
  证明: krullDim_le_of_strictMono (fun I => ⟨Ideal.comap f I.asIdeal, inferInstance⟩)
    (Monotone.strictMono_of_injective (fun _ _ hab => Ideal.comap_mono hab)
      (fun _ _ h => PrimeSpectrum.ext_iff.mpr <| Ideal.comap_injective_of_surjective f hf <| by
        simpa using h))

Depends on / 依赖: I.asIdeal, Ideal.comap, Ideal.comap_injective_of_surjective, Ideal.comap_mono, Monotone, Monotone.strictMono_of_injective, PrimeSpectrum, PrimeSpectrum.ext_iff.mpr, asIdeal, comap_injective_of_surjective, comap_mono, ext_iff, krullDim_le_of_strictMono, strictMono_of_injective
-/
theorem ringKrullDim_le_of_surjective (f : R ->+* S) (hf : Function.Surjective f) :
    ringKrullDim S <= ringKrullDim R :=
  krullDim_le_of_strictMono (fun I => ⟨Ideal.comap f I.asIdeal, inferInstance⟩)
    (Monotone.strictMono_of_injective (fun _ _ hab => Ideal.comap_mono hab)
      (fun _ _ h => PrimeSpectrum.ext_iff.mpr <| Ideal.comap_injective_of_surjective f hf <| by
        simpa using h))

/--
theorem `ringKrullDim_quotient_le` / 定理 `ringKrullDim_quotient_le`

English:
theorem ringKrullDim_quotient_le
  given: {R : Type*} [CommRing R] (I : Ideal R)
  proof: ringKrullDim_le_of_surjective _ Ideal.Quotient.mk_surjective

中文:
定理 ringKrullDim_quotient_le
  条件: {R : 类型} [CommRing R] (I : Ideal R)
  证明: ringKrullDim_le_of_surjective _ Ideal.Quotient.mk_surjective

Depends on / 依赖: Ideal.Quotient.mk_surjective, Quotient, mk_surjective, ringKrullDim_le_of_surjective
-/
theorem ringKrullDim_quotient_le {R : Type*} [CommRing R] (I : Ideal R) :
    ringKrullDim (R ⧸ I) <= ringKrullDim R :=
  ringKrullDim_le_of_surjective _ Ideal.Quotient.mk_surjective

/--
theorem `ringKrullDim_eq_of_ringEquiv` / 定理 `ringKrullDim_eq_of_ringEquiv`

English:
theorem ringKrullDim_eq_of_ringEquiv
  given: (e : R ≃+* S)
  proof: le_antisymm (ringKrullDim_le_of_surjective e.symm e.symm.surjective)
    (ringKrullDim_le_of_surjective e e.surjective)

alias RingEquiv.ringKrullDim := ringKrullDim_eq_of_ringEquiv

中文:
定理 ringKrullDim_eq_of_ringEquiv
  条件: (e : R ≃+* S)
  证明: le_antisymm (ringKrullDim_le_of_surjective e.symm e.symm.surjective)
    (ringKrullDim_le_of_surjective e e.surjective)

alias RingEquiv.ringKrullDim := ringKrullDim_eq_of_ringEquiv

Depends on / 依赖: e.surjective, e.symm, e.symm.surjective, le_antisymm, ringKrullDim_le_of_surjective, surjective
-/
theorem ringKrullDim_eq_of_ringEquiv (e : R ≃+* S) :
    ringKrullDim R = ringKrullDim S :=
  le_antisymm (ringKrullDim_le_of_surjective e.symm e.symm.surjective)
    (ringKrullDim_le_of_surjective e e.surjective)

alias RingEquiv.ringKrullDim := ringKrullDim_eq_of_ringEquiv

/--
Definition of `FiniteRingKrullDim` / `FiniteRingKrullDim` 的定义

English:
abbreviation FiniteRingKrullDim
  signature: (R : Type*) [CommSemiring R]
  body: FiniteDimensionalOrder (PrimeSpectrum R)

中文:
缩写 FiniteRingKrullDim
  签名: (R : 类型) [CommSemiring R]
  定义体: FiniteDimensionalOrder (PrimeSpectrum R)

Depends on / 依赖: FiniteDimensionalOrder, PrimeSpectrum
-/
abbrev FiniteRingKrullDim (R : Type*) [CommSemiring R] :=
  FiniteDimensionalOrder (PrimeSpectrum R)

/--
lemma `ringKrullDim_ne_top` / 引理 `ringKrullDim_ne_top`

English:
lemma ringKrullDim_ne_top
  given: [FiniteRingKrullDim R]
  proof: krullDim_ne_top_of_finiteDimensionalOrder

中文:
引理 ringKrullDim_ne_top
  条件: [FiniteRingKrullDim R]
  证明: krullDim_ne_top_of_finiteDimensionalOrder

Depends on / 依赖: krullDim_ne_top_of_finiteDimensionalOrder
-/
lemma ringKrullDim_ne_top [FiniteRingKrullDim R] :
    ringKrullDim R != ⊤ := krullDim_ne_top_of_finiteDimensionalOrder

/--
lemma `ringKrullDim_lt_top` / 引理 `ringKrullDim_lt_top`

English:
lemma ringKrullDim_lt_top
  given: [FiniteRingKrullDim R]
  proof: ringKrullDim_ne_top.lt_top

中文:
引理 ringKrullDim_lt_top
  条件: [FiniteRingKrullDim R]
  证明: ringKrullDim_ne_top.lt_top

Depends on / 依赖: lt_top, ringKrullDim_ne_top, ringKrullDim_ne_top.lt_top
-/
lemma ringKrullDim_lt_top [FiniteRingKrullDim R] :
    ringKrullDim R < ⊤ := ringKrullDim_ne_top.lt_top

/--
lemma `ringKrullDim_ne_bot` / 引理 `ringKrullDim_ne_bot`

English:
lemma ringKrullDim_ne_bot
  given: [FiniteRingKrullDim R]
  proof: krullDim_ne_bot_of_finiteDimensionalOrder

中文:
引理 ringKrullDim_ne_bot
  条件: [FiniteRingKrullDim R]
  证明: krullDim_ne_bot_of_finiteDimensionalOrder

Depends on / 依赖: krullDim_ne_bot_of_finiteDimensionalOrder
-/
lemma ringKrullDim_ne_bot [FiniteRingKrullDim R] :
    ringKrullDim R != ⊥ := krullDim_ne_bot_of_finiteDimensionalOrder

/--
lemma `finiteRingKrullDim_iff_ne_bot_and_top` / 引理 `finiteRingKrullDim_iff_ne_bot_and_top`

English:
lemma finiteRingKrullDim_iff_ne_bot_and_top
  proof: (Order.finiteDimensionalOrder_iff_krullDim_ne_bot_and_top (α := PrimeSpectrum R))

中文:
引理 finiteRingKrullDim_iff_ne_bot_and_top
  证明: (Order.finiteDimensionalOrder_iff_krullDim_ne_bot_and_top (α := PrimeSpectrum R))

Depends on / 依赖: Order.finiteDimensionalOrder_iff_krullDim_ne_bot_and_top, PrimeSpectrum, finiteDimensionalOrder_iff_krullDim_ne_bot_and_top
-/
lemma finiteRingKrullDim_iff_ne_bot_and_top :
    FiniteRingKrullDim R ↔ (ringKrullDim R != ⊥ ∧ ringKrullDim R != ⊤) :=
  (Order.finiteDimensionalOrder_iff_krullDim_ne_bot_and_top (α := PrimeSpectrum R))

/--
lemma `Nontrivial.of_finiteRingKrullDim` / 引理 `Nontrivial.of_finiteRingKrullDim`

English:
lemma Nontrivial.of_finiteRingKrullDim
  given: [FiniteRingKrullDim R]
  statement: Nontrivial R
  proof: by
  rw [← PrimeSpectrum.nonempty_iff_nontrivial]
  exact LTSeries.nonempty_of_finiteDimensionalOrder _

proof_wanted MvPolynomial.fin_ringKrullDim_eq_add_of_isNoetherianRing
    [IsNoetherianRing R] (n : Nat) :
    ringKrullDim (MvPolynomial (Fin n) R) = ringKrullDim R + n

中文:
引理 Nontrivial.of_finiteRingKrullDim
  条件: [FiniteRingKrullDim R]
  结论: Nontrivial R
  证明: by
  rw [← PrimeSpectrum.nonempty_iff_nontrivial]
  exact LTSeries.nonempty_of_finiteDimensionalOrder _

proof_wanted MvPolynomial.fin_ringKrullDim_eq_add_of_isNoetherianRing
    [IsNoetherianRing R] (n : Nat) :
    ringKrullDim (MvPolynomial (Fin n) R) = ringKrullDim R + n

Depends on / 依赖: LTSeries, LTSeries.nonempty_of_finiteDimensionalOrder, PrimeSpectrum, PrimeSpectrum.nonempty_iff_nontrivial, nonempty_iff_nontrivial, nonempty_of_finiteDimensionalOrder
-/
lemma Nontrivial.of_finiteRingKrullDim [FiniteRingKrullDim R] : Nontrivial R := by
  rw [← PrimeSpectrum.nonempty_iff_nontrivial]
  exact LTSeries.nonempty_of_finiteDimensionalOrder _

proof_wanted MvPolynomial.fin_ringKrullDim_eq_add_of_isNoetherianRing
    [IsNoetherianRing R] (n : Nat) :
    ringKrullDim (MvPolynomial (Fin n) R) = ringKrullDim R + n

section Zero

-- See `Mathlib/RingTheory/KrullDimension/Zero.lean` for further results.

/--
lemma `Ring.krullDimLE_zero_iff` / 引理 `Ring.krullDimLE_zero_iff`

English:
lemma Ring.krullDimLE_zero_iff
  statement: Ring.KrullDimLE 0 R ↔ forall I : Ideal R, I.IsPrime -> I.IsMaximal
  proof: by
  simp_rw [Ring.KrullDimLE, Order.krullDimLE_iff, Nat.cast_zero,
    Order.krullDim_nonpos_iff_forall_isMax,
    (PrimeSpectrum.equivSubtype R).forall_congr_left, Subtype.forall, PrimeSpectrum.isMax_iff]
  rfl

中文:
引理 Ring.krullDimLE_zero_iff
  结论: Ring.KrullDimLE 0 R ↔ 对任意 I : Ideal R, I.IsPrime -> I.IsMaximal
  证明: by
  simp_rw [Ring.KrullDimLE, Order.krullDimLE_iff, Nat.cast_zero,
    Order.krullDim_nonpos_iff_forall_isMax,
    (PrimeSpectrum.equivSubtype R).forall_congr_left, Subtype.forall, PrimeSpectrum.isMax_iff]
  rfl

Depends on / 依赖: KrullDimLE, Nat.cast_zero, Order.krullDimLE_iff, Order.krullDim_nonpos_iff_forall_isMax, PrimeSpectrum, PrimeSpectrum.equivSubtype, PrimeSpectrum.isMax_iff, Ring.KrullDimLE, Subtype, Subtype.forall, cast_zero, equivSubtype, forall_congr_left, isMax_iff, krullDimLE_iff, krullDim_nonpos_iff_forall_isMax, simp_rw
-/
lemma Ring.krullDimLE_zero_iff : Ring.KrullDimLE 0 R ↔ forall I : Ideal R, I.IsPrime -> I.IsMaximal := by
  simp_rw [Ring.KrullDimLE, Order.krullDimLE_iff, Nat.cast_zero,
    Order.krullDim_nonpos_iff_forall_isMax,
    (PrimeSpectrum.equivSubtype R).forall_congr_left, Subtype.forall, PrimeSpectrum.isMax_iff]
  rfl

/--
theorem `Ring.krullDimLE_zero_iff_forall_minimalPrimes_isMaximal` / 定理 `Ring.krullDimLE_zero_iff_forall_minimalPrimes_isMaximal`

English:
theorem Ring.krullDimLE_zero_iff_forall_minimalPrimes_isMaximal
  proof: by
  refine Ring.krullDimLE_zero_iff.trans ⟨fun h I hI => h I hI.1.1, fun h I hI => ?_⟩
  obtain ⟨J, hJ, hle⟩ := Ideal.exists_minimalPrimes_le bot_le (J := I)
  exact (h J hJ).eq_of_le hI.ne_top hle ▸ h J hJ

中文:
定理 Ring.krullDimLE_zero_iff_forall_minimalPrimes_isMaximal
  证明: by
  refine Ring.krullDimLE_zero_iff.trans ⟨fun h I hI => h I hI.1.1, fun h I hI => ?_⟩
  obtain ⟨J, hJ, hle⟩ := Ideal.exists_minimalPrimes_le bot_le (J := I)
  exact (h J hJ).eq_of_le hI.ne_top hle ▸ h J hJ

Depends on / 依赖: Ideal.exists_minimalPrimes_le, Ring.krullDimLE_zero_iff.trans, bot_le, eq_of_le, exists_minimalPrimes_le, hI.ne_top, krullDimLE_zero_iff, ne_top
-/
theorem Ring.krullDimLE_zero_iff_forall_minimalPrimes_isMaximal :
    Ring.KrullDimLE 0 R ↔ forall I in minimalPrimes R, I.IsMaximal := by
  refine Ring.krullDimLE_zero_iff.trans ⟨fun h I hI => h I hI.1.1, fun h I hI => ?_⟩
  obtain ⟨J, hJ, hle⟩ := Ideal.exists_minimalPrimes_le bot_le (J := I)
  exact (h J hJ).eq_of_le hI.ne_top hle ▸ h J hJ

/--
lemma `Ring.KrullDimLE.mk₀` / 引理 `Ring.KrullDimLE.mk₀`

English:
lemma Ring.KrullDimLE.mk₀
  given: (H : forall I : Ideal R, I.IsPrime -> I.IsMaximal)
  statement: Ring.KrullDimLE 0 R
  proof: by
  rwa [Ring.krullDimLE_zero_iff]

中文:
引理 Ring.KrullDimLE.mk₀
  条件: (H : 对任意 I : Ideal R, I.IsPrime -> I.IsMaximal)
  结论: Ring.KrullDimLE 0 R
  证明: by
  rwa [Ring.krullDimLE_zero_iff]

Depends on / 依赖: Ring.krullDimLE_zero_iff, krullDimLE_zero_iff
-/
lemma Ring.KrullDimLE.mk₀ (H : forall I : Ideal R, I.IsPrime -> I.IsMaximal) : Ring.KrullDimLE 0 R := by
  rwa [Ring.krullDimLE_zero_iff]

/--
lemma `Ideal.isMaximal_of_isPrime` / 引理 `Ideal.isMaximal_of_isPrime`

English:
lemma Ideal.isMaximal_of_isPrime
  given: [Ring.KrullDimLE 0 R] (I : Ideal R) [I.IsPrime]
  statement: I.IsMaximal
  proof: Ring.krullDimLE_zero_iff.mp ‹_› I ‹_›

中文:
引理 Ideal.isMaximal_of_isPrime
  条件: [Ring.KrullDimLE 0 R] (I : Ideal R) [I.IsPrime]
  结论: I.IsMaximal
  证明: Ring.krullDimLE_zero_iff.mp ‹_› I ‹_›

Depends on / 依赖: Ring.krullDimLE_zero_iff.mp, krullDimLE_zero_iff
-/
lemma Ideal.isMaximal_of_isPrime [Ring.KrullDimLE 0 R] (I : Ideal R) [I.IsPrime] : I.IsMaximal :=
  Ring.krullDimLE_zero_iff.mp ‹_› I ‹_›

/--
lemma `Ideal.IsPrime.isMaximal'` / 引理 `Ideal.IsPrime.isMaximal'`

English:
lemma Ideal.IsPrime.isMaximal'
  given: [Ring.KrullDimLE 0 R] {I : Ideal R} (hI : I.IsPrime)
  statement: I.IsMaximal
  proof: I.isMaximal_of_isPrime

中文:
引理 Ideal.IsPrime.isMaximal'
  条件: [Ring.KrullDimLE 0 R] {I : Ideal R} (hI : I.IsPrime)
  结论: I.IsMaximal
  证明: I.isMaximal_of_isPrime

Depends on / 依赖: I.isMaximal_of_isPrime, isMaximal_of_isPrime
-/
lemma Ideal.IsPrime.isMaximal' [Ring.KrullDimLE 0 R] {I : Ideal R} (hI : I.IsPrime) : I.IsMaximal :=
  I.isMaximal_of_isPrime

instance (priority := 100) (I : Ideal R) [I.IsPrime] [Ring.KrullDimLE 0 R] : I.IsMaximal :=
  I.isMaximal_of_isPrime

/--
lemma `Ideal.isMaximal_iff_isPrime` / 引理 `Ideal.isMaximal_iff_isPrime`

English:
lemma Ideal.isMaximal_iff_isPrime
  given: [Ring.KrullDimLE 0 R] {I : Ideal R}
  statement: I.IsMaximal ↔ I.IsPrime
  proof: ⟨IsMaximal.isPrime, fun _ => inferInstance⟩

中文:
引理 Ideal.isMaximal_iff_isPrime
  条件: [Ring.KrullDimLE 0 R] {I : Ideal R}
  结论: I.IsMaximal ↔ I.IsPrime
  证明: ⟨IsMaximal.isPrime, fun _ => inferInstance⟩

Depends on / 依赖: IsMaximal, IsMaximal.isPrime, isPrime
-/
lemma Ideal.isMaximal_iff_isPrime [Ring.KrullDimLE 0 R] {I : Ideal R} : I.IsMaximal ↔ I.IsPrime :=
  ⟨IsMaximal.isPrime, fun _ => inferInstance⟩

/--
lemma `Ideal.mem_minimalPrimes_of_krullDimLE_zero` / 引理 `Ideal.mem_minimalPrimes_of_krullDimLE_zero`

English:
lemma Ideal.mem_minimalPrimes_of_krullDimLE_zero
  statement: [Ring.KrullDimLE 0 R]
  proof: minimalPrimes_eq_minimals (R := R) ▸
    ⟨‹_›, fun J hJ hJI => (IsMaximal.eq_of_le inferInstance IsPrime.ne_top' hJI).ge⟩

中文:
引理 Ideal.mem_minimalPrimes_of_krullDimLE_zero
  结论: [Ring.KrullDimLE 0 R]
  证明: minimalPrimes_eq_minimals (R := R) ▸
    ⟨‹_›, fun J hJ hJI => (IsMaximal.eq_of_le inferInstance IsPrime.ne_top' hJI).ge⟩

Depends on / 依赖: IsMaximal, IsMaximal.eq_of_le, IsPrime, IsPrime.ne_top, eq_of_le, minimalPrimes_eq_minimals, ne_top
-/
lemma Ideal.mem_minimalPrimes_of_krullDimLE_zero [Ring.KrullDimLE 0 R]
    (I : Ideal R) [I.IsPrime] : I in minimalPrimes R :=
  minimalPrimes_eq_minimals (R := R) ▸
    ⟨‹_›, fun J hJ hJI => (IsMaximal.eq_of_le inferInstance IsPrime.ne_top' hJI).ge⟩

/--
lemma `Ideal.mem_minimalPrimes_iff_isPrime` / 引理 `Ideal.mem_minimalPrimes_iff_isPrime`

English:
lemma Ideal.mem_minimalPrimes_iff_isPrime
  given: [Ring.KrullDimLE 0 R] {I : Ideal R}
  proof: ⟨(·.1.1), fun _ => I.mem_minimalPrimes_of_krullDimLE_zero⟩

中文:
引理 Ideal.mem_minimalPrimes_iff_isPrime
  条件: [Ring.KrullDimLE 0 R] {I : Ideal R}
  证明: ⟨(·.1.1), fun _ => I.mem_minimalPrimes_of_krullDimLE_zero⟩

Depends on / 依赖: I.mem_minimalPrimes_of_krullDimLE_zero, mem_minimalPrimes_of_krullDimLE_zero
-/
lemma Ideal.mem_minimalPrimes_iff_isPrime [Ring.KrullDimLE 0 R] {I : Ideal R} :
    I in minimalPrimes R ↔ I.IsPrime :=
  ⟨(·.1.1), fun _ => I.mem_minimalPrimes_of_krullDimLE_zero⟩

/--
theorem `nilradical_le_jacobson` / 定理 `nilradical_le_jacobson`

English:
theorem nilradical_le_jacobson
  given: (R) [CommRing R]
  statement: nilradical R <= Ring.jacobson R
  proof: nilradical_eq_sInf R ▸ le_sInf fun _I hI => sInf_le (Ideal.IsMaximal.isPrime ⟨hI⟩)

中文:
定理 nilradical_le_jacobson
  条件: (R) [CommRing R]
  结论: nilradical R <= Ring.jacobson R
  证明: nilradical_eq_sInf R ▸ le_sInf fun _I hI => sInf_le (Ideal.IsMaximal.isPrime ⟨hI⟩)

Depends on / 依赖: Ideal.IsMaximal.isPrime, IsMaximal, isPrime, le_sInf, nilradical_eq_sInf, sInf_le
-/
theorem nilradical_le_jacobson (R) [CommRing R] : nilradical R <= Ring.jacobson R :=
  nilradical_eq_sInf R ▸ le_sInf fun _I hI => sInf_le (Ideal.IsMaximal.isPrime ⟨hI⟩)

/--
theorem `Ring.jacobson_eq_nilradical_of_krullDimLE_zero` / 定理 `Ring.jacobson_eq_nilradical_of_krullDimLE_zero`

English:
theorem Ring.jacobson_eq_nilradical_of_krullDimLE_zero
  given: (R) [CommRing R] [KrullDimLE 0 R]
  proof: (nilradical_le_jacobson R).antisymm' nilradical_eq_sInf R ▸ le_sInf fun I (_ : I.IsPrime) =>
    sInf_le Ideal.IsMaximal.out

中文:
定理 Ring.jacobson_eq_nilradical_of_krullDimLE_zero
  条件: (R) [CommRing R] [KrullDimLE 0 R]
  证明: (nilradical_le_jacobson R).antisymm' nilradical_eq_sInf R ▸ le_sInf fun I (_ : I.IsPrime) =>
    sInf_le Ideal.IsMaximal.out

Depends on / 依赖: I.IsPrime, Ideal.IsMaximal.out, IsMaximal, IsPrime, antisymm, le_sInf, nilradical_eq_sInf, nilradical_le_jacobson, sInf_le
-/
theorem Ring.jacobson_eq_nilradical_of_krullDimLE_zero (R) [CommRing R] [KrullDimLE 0 R] :
    jacobson R = nilradical R :=
(nilradical_le_jacobson R).antisymm' nilradical_eq_sInf R ▸ le_sInf fun I (_ : I.IsPrime) =>
    sInf_le Ideal.IsMaximal.out

end Zero

section One

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Ring.KrullDimLE
  signature: 0 R] : Ring.KrullDimLE 1 R
  body: .mono zero_le_one _

中文:
实例 [Ring.KrullDimLE
  签名: 0 R] : Ring.KrullDimLE 1 R
  定义体: .mono zero_le_one _
-/
instance [Ring.KrullDimLE 0 R] : Ring.KrullDimLE 1 R := .mono zero_le_one _

/--
lemma `Ring.krullDimLE_one_iff` / 引理 `Ring.krullDimLE_one_iff`

English:
lemma Ring.krullDimLE_one_iff
  statement: Ring.KrullDimLE 1 R ↔
  proof: by
  simp_rw [Ring.KrullDimLE, Order.krullDimLE_iff, Nat.cast_one,
    Order.krullDim_le_one_iff, (PrimeSpectrum.equivSubtype R).forall_congr_left,
    Subtype.forall, PrimeSpectrum.isMax_iff, PrimeSpectrum.isMin_iff]
  rfl

中文:
引理 Ring.krullDimLE_one_iff
  结论: Ring.KrullDimLE 1 R ↔
  证明: by
  simp_rw [Ring.KrullDimLE, Order.krullDimLE_iff, Nat.cast_one,
    Order.krullDim_le_one_iff, (PrimeSpectrum.equivSubtype R).forall_congr_left,
    Subtype.forall, PrimeSpectrum.isMax_iff, PrimeSpectrum.isMin_iff]
  rfl

Depends on / 依赖: KrullDimLE, Nat.cast_one, Order.krullDimLE_iff, Order.krullDim_le_one_iff, PrimeSpectrum, PrimeSpectrum.equivSubtype, PrimeSpectrum.isMax_iff, PrimeSpectrum.isMin_iff, Ring.KrullDimLE, Subtype, Subtype.forall, cast_one, equivSubtype, forall_congr_left, isMax_iff, isMin_iff, krullDimLE_iff, krullDim_le_one_iff, simp_rw
-/
lemma Ring.krullDimLE_one_iff : Ring.KrullDimLE 1 R ↔
    forall I : Ideal R, I.IsPrime -> I in minimalPrimes R ∨ I.IsMaximal := by
  simp_rw [Ring.KrullDimLE, Order.krullDimLE_iff, Nat.cast_one,
    Order.krullDim_le_one_iff, (PrimeSpectrum.equivSubtype R).forall_congr_left,
    Subtype.forall, PrimeSpectrum.isMax_iff, PrimeSpectrum.isMin_iff]
  rfl

/--
lemma `Ring.KrullDimLE.mk₁` / 引理 `Ring.KrullDimLE.mk₁`

English:
lemma Ring.KrullDimLE.mk₁
  given: (H : forall I : Ideal R, I.IsPrime -> I in minimalPrimes R ∨ I.IsMaximal)
  proof: by
  rwa [Ring.krullDimLE_one_iff]

中文:
引理 Ring.KrullDimLE.mk₁
  条件: (H : 对任意 I : Ideal R, I.IsPrime -> I in minimalPrimes R ∨ I.IsMaximal)
  证明: by
  rwa [Ring.krullDimLE_one_iff]

Depends on / 依赖: Ring.krullDimLE_one_iff, krullDimLE_one_iff
-/
lemma Ring.KrullDimLE.mk₁ (H : forall I : Ideal R, I.IsPrime -> I in minimalPrimes R ∨ I.IsMaximal) :
    Ring.KrullDimLE 1 R := by
  rwa [Ring.krullDimLE_one_iff]

/--
lemma `Ring.krullDimLE_one_iff_of_isPrime_bot` / 引理 `Ring.krullDimLE_one_iff_of_isPrime_bot`

English:
lemma Ring.krullDimLE_one_iff_of_isPrime_bot
  given: [(⊥ : Ideal R).IsPrime]
  proof: by
  let : OrderBot (PrimeSpectrum R) := { bot := ⟨⊥, ‹_›⟩, bot_le I := bot_le (a := I.1) }
  simp_rw [Ring.KrullDimLE, Order.krullDimLE_iff, Nat.cast_one,
    Order.krullDim_le_one_iff_forall_isMax, (PrimeSpectrum.equivSubtype R).forall_congr_left,
    Subtype.forall, PrimeSpectrum.isMax_iff, foral

中文:
引理 Ring.krullDimLE_one_iff_of_isPrime_bot
  条件: [(⊥ : Ideal R).IsPrime]
  证明: by
  let : OrderBot (PrimeSpectrum R) := { bot := ⟨⊥, ‹_›⟩, bot_le I := bot_le (a := I.1) }
  simp_rw [Ring.KrullDimLE, Order.krullDimLE_iff, Nat.cast_one,
    Order.krullDim_le_one_iff_forall_isMax, (PrimeSpectrum.equivSubtype R).forall_congr_left,
    Subtype.forall, PrimeSpectrum.isMax_iff, foral

Depends on / 依赖: KrullDimLE, Nat.cast_one, Order.krullDimLE_iff, Order.krullDim_le_one_iff_forall_isMax, OrderBot, PrimeSpectrum, PrimeSpectrum.equivSubtype, PrimeSpectrum.ext_iff, PrimeSpectrum.isMax_iff, Ring.KrullDimLE, Subtype, Subtype.forall, bot_le, cast_one, equivSubtype, ext_iff, forall_comm, forall_congr_left, isMax_iff, krullDimLE_iff
-/
lemma Ring.krullDimLE_one_iff_of_isPrime_bot [(⊥ : Ideal R).IsPrime] :
    Ring.KrullDimLE 1 R ↔ forall I : Ideal R, I != ⊥ -> I.IsPrime -> I.IsMaximal := by
  let : OrderBot (PrimeSpectrum R) := { bot := ⟨⊥, ‹_›⟩, bot_le I := bot_le (a := I.1) }
  simp_rw [Ring.KrullDimLE, Order.krullDimLE_iff, Nat.cast_one,
    Order.krullDim_le_one_iff_forall_isMax, (PrimeSpectrum.equivSubtype R).forall_congr_left,
    Subtype.forall, PrimeSpectrum.isMax_iff, forall_comm (α := _ != ⊥),
    ne_eq, PrimeSpectrum.ext_iff]
  rfl

/--
lemma `Ring.krullDimLE_one_iff_of_noZeroDivisors` / 引理 `Ring.krullDimLE_one_iff_of_noZeroDivisors`

English:
lemma Ring.krullDimLE_one_iff_of_noZeroDivisors
  given: [NoZeroDivisors R]
  proof: by
  cases subsingleton_or_nontrivial R
  · exact iff_of_true inferInstance fun I h => (h <| Subsingleton.elim ..).elim
  exact Ring.krullDimLE_one_iff_of_isPrime_bot

中文:
引理 Ring.krullDimLE_one_iff_of_noZeroDivisors
  条件: [NoZeroDivisors R]
  证明: by
  cases subsingleton_or_nontrivial R
  · exact iff_of_true inferInstance fun I h => (h <| Subsingleton.elim ..).elim
  exact Ring.krullDimLE_one_iff_of_isPrime_bot

Depends on / 依赖: Ring.krullDimLE_one_iff_of_isPrime_bot, Subsingleton, Subsingleton.elim, iff_of_true, krullDimLE_one_iff_of_isPrime_bot, subsingleton_or_nontrivial
-/
lemma Ring.krullDimLE_one_iff_of_noZeroDivisors [NoZeroDivisors R] :
    Ring.KrullDimLE 1 R ↔ forall I : Ideal R, I != ⊥ -> I.IsPrime -> I.IsMaximal := by
  cases subsingleton_or_nontrivial R
  · exact iff_of_true inferInstance fun I h => (h <| Subsingleton.elim ..).elim
  exact Ring.krullDimLE_one_iff_of_isPrime_bot

/--
lemma `Ideal.IsPrime.isMaximal_of_ne_bot` / 引理 `Ideal.IsPrime.isMaximal_of_ne_bot`

English:
lemma Ideal.IsPrime.isMaximal_of_ne_bot
  statement: [NoZeroDivisors R] [Ring.KrullDimLE 1 R]
  proof: Ring.krullDimLE_one_iff_of_noZeroDivisors.mp ‹_› _ hI' hI

中文:
引理 Ideal.IsPrime.isMaximal_of_ne_bot
  结论: [NoZeroDivisors R] [Ring.KrullDimLE 1 R]
  证明: Ring.krullDimLE_one_iff_of_noZeroDivisors.mp ‹_› _ hI' hI

Depends on / 依赖: Ring.krullDimLE_one_iff_of_noZeroDivisors.mp, krullDimLE_one_iff_of_noZeroDivisors
-/
lemma Ideal.IsPrime.isMaximal_of_ne_bot [NoZeroDivisors R] [Ring.KrullDimLE 1 R]
    {I : Ideal R} (hI : I.IsPrime) (hI' : I != ⊥) :
    I.IsMaximal :=
  Ring.krullDimLE_one_iff_of_noZeroDivisors.mp ‹_› _ hI' hI

/--
lemma `Ideal.isMaximal_of_isPrime_of_ne_bot` / 引理 `Ideal.isMaximal_of_isPrime_of_ne_bot`

English:
lemma Ideal.isMaximal_of_isPrime_of_ne_bot
  statement: [NoZeroDivisors R] [Ring.KrullDimLE 1 R]
  proof: Ideal.IsPrime.isMaximal_of_ne_bot ‹_› hI'

中文:
引理 Ideal.isMaximal_of_isPrime_of_ne_bot
  结论: [NoZeroDivisors R] [Ring.KrullDimLE 1 R]
  证明: Ideal.IsPrime.isMaximal_of_ne_bot ‹_› hI'

Depends on / 依赖: Ideal.IsPrime.isMaximal_of_ne_bot, IsPrime, isMaximal_of_ne_bot
-/
lemma Ideal.isMaximal_of_isPrime_of_ne_bot [NoZeroDivisors R] [Ring.KrullDimLE 1 R]
    (I : Ideal R) [I.IsPrime] (hI' : I != ⊥) :
    I.IsMaximal :=
  Ideal.IsPrime.isMaximal_of_ne_bot ‹_› hI'

/--
lemma `Ring.KrullDimLE.mk₁'` / 引理 `Ring.KrullDimLE.mk₁'`

English:
lemma Ring.KrullDimLE.mk₁'
  given: (H : forall I : Ideal R, I != ⊥ -> I.IsPrime -> I.IsMaximal)
  proof: by
  by_cases hR : (⊥ : Ideal R).IsPrime
  · rwa [Ring.krullDimLE_one_iff_of_isPrime_bot]
  suffices Ring.KrullDimLE 0 R from inferInstance
  exact .mk₀ fun I hI => H I (fun e => hR (e ▸ hI)) hI

中文:
引理 Ring.KrullDimLE.mk₁'
  条件: (H : 对任意 I : Ideal R, I != ⊥ -> I.IsPrime -> I.IsMaximal)
  证明: by
  by_cases hR : (⊥ : Ideal R).IsPrime
  · rwa [Ring.krullDimLE_one_iff_of_isPrime_bot]
  suffices Ring.KrullDimLE 0 R from inferInstance
  exact .mk₀ fun I hI => H I (fun e => hR (e ▸ hI)) hI

Depends on / 依赖: IsPrime, KrullDimLE, Ring.KrullDimLE, Ring.krullDimLE_one_iff_of_isPrime_bot, krullDimLE_one_iff_of_isPrime_bot
-/
lemma Ring.KrullDimLE.mk₁' (H : forall I : Ideal R, I != ⊥ -> I.IsPrime -> I.IsMaximal) :
    Ring.KrullDimLE 1 R := by
  by_cases hR : (⊥ : Ideal R).IsPrime
  · rwa [Ring.krullDimLE_one_iff_of_isPrime_bot]
  suffices Ring.KrullDimLE 0 R from inferInstance
  exact .mk₀ fun I hI => H I (fun e => hR (e ▸ hI)) hI

/--
lemma `Prime.isMaximal_span_singleton` / 引理 `Prime.isMaximal_span_singleton`

English:
lemma Prime.isMaximal_span_singleton
  statement: [NoZeroDivisors R] [Ring.KrullDimLE 1 R]
  proof: ((Ideal.span_singleton_prime ha.ne_zero).mpr ha).isMaximal_of_ne_bot (by simpa using ha.ne_zero)

中文:
引理 Prime.isMaximal_span_singleton
  结论: [NoZeroDivisors R] [Ring.KrullDimLE 1 R]
  证明: ((Ideal.span_singleton_prime ha.ne_zero).mpr ha).isMaximal_of_ne_bot (by simpa using ha.ne_zero)

Depends on / 依赖: Ideal.span_singleton_prime, ha.ne_zero, isMaximal_of_ne_bot, ne_zero, span_singleton_prime
-/
lemma Prime.isMaximal_span_singleton [NoZeroDivisors R] [Ring.KrullDimLE 1 R]
    {a : R} (ha : Prime a) : (Ideal.span {a}).IsMaximal :=
  ((Ideal.span_singleton_prime ha.ne_zero).mpr ha).isMaximal_of_ne_bot (by simpa using ha.ne_zero)

/--
lemma `Ideal.liesOver_span_iff` / 引理 `Ideal.liesOver_span_iff`

English:
lemma Ideal.liesOver_span_iff
  statement: [NoZeroDivisors R] [Ring.KrullDimLE 1 R] [Algebra R S]
  proof: by
  have hP : P.under R != ⊤ := Ideal.comap_ne_top _ hP
  simp [Ideal.liesOver_iff, Ideal.IsMaximal.eq_iff_le hp.isMaximal_span_singleton hP]

中文:
引理 Ideal.liesOver_span_iff
  结论: [NoZeroDivisors R] [Ring.KrullDimLE 1 R] [Algebra R S]
  证明: by
  have hP : P.under R != ⊤ := Ideal.comap_ne_top _ hP
  simp [Ideal.liesOver_iff, Ideal.IsMaximal.eq_iff_le hp.isMaximal_span_singleton hP]

Depends on / 依赖: Ideal.IsMaximal.eq_iff_le, Ideal.comap_ne_top, Ideal.liesOver_iff, IsMaximal, P.under, comap_ne_top, eq_iff_le, hp.isMaximal_span_singleton, isMaximal_span_singleton, liesOver_iff
-/
lemma Ideal.liesOver_span_iff [NoZeroDivisors R] [Ring.KrullDimLE 1 R] [Algebra R S]
    {P : Ideal S} {p : R} (hP : P != ⊤) (hp : Prime p) :
      P.LiesOver (.span {p}) ↔ algebraMap R S p in P := by
  have hP : P.under R != ⊤ := Ideal.comap_ne_top _ hP
  simp [Ideal.liesOver_iff, Ideal.IsMaximal.eq_iff_le hp.isMaximal_span_singleton hP]

end One
