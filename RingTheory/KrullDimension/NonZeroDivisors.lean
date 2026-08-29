/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.Algebra.MvPolynomial.CommRing

/-!

# Krull dimension and non-zero-divisors

## Main results
- `ringKrullDim_quotient_succ_le_of_nonZeroDivisor`: If `r` is not a zero divisor, then
  `dim R/r + 1 ≤ dim R`.
- `ringKrullDim_succ_le_ringKrullDim_polynomial`: `dim R + 1 ≤ dim R[X]`.
- `ringKrullDim_add_enatCard_le_ringKrullDim_mvPolynomial`: `dim R + #σ ≤ dim R[σ]`.
-/

public section

open scoped nonZeroDivisors

variable {R S : Type*} [CommRing R] [CommRing S]

/--
lemma `ringKrullDim_quotient` / 引理 `ringKrullDim_quotient`

English:
lemma ringKrullDim_quotient
  given: (I : Ideal R)
  proof: by
  rw [ringKrullDim]; rw [Order.krullDim_eq_of_orderIso I.primeSpectrumQuotientOrderIsoZeroLocus]

中文:
引理 ringKrullDim_quotient
  条件: (I : 理想 R)
  证明: by
  rw [ringKrullDim]; rw [Order.krullDim_eq_of_orderIso I.primeSpectrumQuotientOrderIsoZeroLocus]

Depends on / 依赖: I.primeSpectrumQuotientOrderIsoZeroLocus, Order.krullDim_eq_of_orderIso, krullDim_eq_of_orderIso, primeSpectrumQuotientOrderIsoZeroLocus, ringKrullDim
-/
lemma ringKrullDim_quotient (I : Ideal R) :
    ringKrullDim (R ⧸ I) = Order.krullDim (PrimeSpectrum.zeroLocus (R := R) I) := by
  rw [ringKrullDim]; rw [Order.krullDim_eq_of_orderIso I.primeSpectrumQuotientOrderIsoZeroLocus]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `ringKrullDim_quotient_succ_le_of_nonZeroDivisor` / 引理 `ringKrullDim_quotient_succ_le_of_nonZeroDivisor`

English:
lemma ringKrullDim_quotient_succ_le_of_nonZeroDivisor
  proof: by
  by_cases hr' : Ideal.span {r} = ⊤
  · rw [hr', ringKrullDim_eq_bot_of_subsingleton]
    simp
  have : Nonempty (PrimeSpectrum.zeroLocus (R := R) (Ideal.span {r})) := by
    rwa [Set.nonempty_coe_sort, Set.nonempty_iff_ne_empty, ne_eq,
      PrimeSpectrum.zeroLocus_empty_iff_eq_top]
  have := Ideal.Quotient.nontrivial_iff.mpr hr'
  have := (Ideal.Quotient.mk (Ideal.span {r})).domain_nontrivial
  rw [ringKrullDim_quotient]; rw [Order.krullDim_eq_iSup_length]; rw [ringKrullDim]; rw [Order.krullDim_eq_iSup_length]; rw [← WithBot.coe_one]; rw [← WithBot.coe_add]; rw [ENat.iSup_add]; rw [WithBot.coe_le_coe]; rw [iSup_le_iff]
  intro l
  obtain ⟨p, hp, hp'⟩ := Ideal.exists_minimalPrimes_le (J := l.head.1.asIdeal) bot_le
  let p' : PrimeSpectrum R := ⟨p, hp.1.1⟩
  have hp' : p' < l.head := lt_of_le_of_ne hp' fun h => Set.disjoint_iff.mp
    (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hp)
    ⟨show r in p by simpa [← h] using l.head.2, hr⟩
  refine le_trans ?_ (le_iSup _ ((l.map Subtype.val (fun _ _ => id)).cons p' hp'))
  simp

中文:
引理 ringKrullDim_quotient_succ_le_of_nonZeroDivisor
  证明: by
  by_cases hr' : Ideal.span {r} = ⊤
  · rw [hr', ringKrullDim_eq_bot_of_subsingleton]
    simp
  have : Nonempty (PrimeSpectrum.zeroLocus (R := R) (Ideal.span {r})) := by
    rwa [Set.nonempty_coe_sort, Set.nonempty_iff_ne_empty, ne_eq,
      PrimeSpectrum.zeroLocus_empty_iff_eq_top]
  have := Ideal.Quotient.nontrivial_iff.mpr hr'
  have := (Ideal.Quotient.mk (Ideal.span {r})).domain_nontrivial
  rw [ringKrullDim_quotient]; rw [Order.krullDim_eq_iSup_length]; rw [ringKrullDim]; rw [Order.krullDim_eq_iSup_length]; rw [← WithBot.coe_one]; rw [← WithBot.coe_add]; rw [ENat.iSup_add]; rw [WithBot.coe_le_coe]; rw [iSup_le_iff]
  intro l
  obtain ⟨p, hp, hp'⟩ := Ideal.exists_minimalPrimes_le (J := l.head.1.asIdeal) bot_le
  let p' : PrimeSpectrum R := ⟨p, hp.1.1⟩
  have hp' : p' < l.head := lt_of_le_of_ne hp' fun h => Set.disjoint_iff.mp
    (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hp)
    ⟨show r in p by simpa [← h] using l.head.2, hr⟩
  refine le_trans ?_ (le_iSup _ ((l.map Subtype.val (fun _ _ => id)).cons p' hp'))
  simp

Depends on / 依赖: Ideal.Quotient.mk, Ideal.Quotient.nontrivial_iff.mpr, Ideal.span, Nonempty, Order.krullDim_eq_iSup_length, PrimeSpectrum, PrimeSpectrum.zeroLocus, PrimeSpectrum.zeroLocus_empty_iff_eq_top, Quotient, Set.nonempty_coe_sort, Set.nonempty_iff_ne_empty, domain_nontrivial, krullDim_eq_iSup_length, ne_eq, nonempty_coe_sort, nonempty_iff_ne_empty, nontrivial_iff, ringKrullDim, ringKrullDim_eq_bot_of_subsingleton, ringKrullDim_quotient
-/
lemma ringKrullDim_quotient_succ_le_of_nonZeroDivisor
    {r : R} (hr : r in R⁰) :
    ringKrullDim (R ⧸ Ideal.span {r}) + 1 <= ringKrullDim R := by
  by_cases hr' : Ideal.span {r} = ⊤
  · rw [hr', ringKrullDim_eq_bot_of_subsingleton]
    simp
  have : Nonempty (PrimeSpectrum.zeroLocus (R := R) (Ideal.span {r})) := by
    rwa [Set.nonempty_coe_sort, Set.nonempty_iff_ne_empty, ne_eq,
      PrimeSpectrum.zeroLocus_empty_iff_eq_top]
  have := Ideal.Quotient.nontrivial_iff.mpr hr'
  have := (Ideal.Quotient.mk (Ideal.span {r})).domain_nontrivial
  rw [ringKrullDim_quotient]; rw [Order.krullDim_eq_iSup_length]; rw [ringKrullDim]; rw [Order.krullDim_eq_iSup_length]; rw [← WithBot.coe_one]; rw [← WithBot.coe_add]; rw [ENat.iSup_add]; rw [WithBot.coe_le_coe]; rw [iSup_le_iff]
  intro l
  obtain ⟨p, hp, hp'⟩ := Ideal.exists_minimalPrimes_le (J := l.head.1.asIdeal) bot_le
  let p' : PrimeSpectrum R := ⟨p, hp.1.1⟩
  have hp' : p' < l.head := lt_of_le_of_ne hp' fun h => Set.disjoint_iff.mp
    (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hp)
    ⟨show r in p by simpa [← h] using l.head.2, hr⟩
  refine le_trans ?_ (le_iSup _ ((l.map Subtype.val (fun _ _ => id)).cons p' hp'))
  simp

/--
lemma `ringKrullDim_succ_le_of_surjective` / 引理 `ringKrullDim_succ_le_of_surjective`

English:
lemma ringKrullDim_succ_le_of_surjective
  statement: (f : R ->+* S) (hf : Function.Surjective f)
  proof: by
  refine le_trans ?_ (ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr)
  gcongr
  exact ringKrullDim_le_of_surjective (Ideal.Quotient.lift _ f (RingHom.ker f
.span_singleton_le_iff_mem.mpr hr')) (Ideal.Quotient.lift_surjective_of_surjective _ _ hf)

中文:
引理 ringKrullDim_succ_le_of_surjective
  结论: (f : R ->+* S) (hf : 函数.满射 f)
  证明: by
  refine le_trans ?_ (ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr)
  gcongr
  exact ringKrullDim_le_of_surjective (Ideal.Quotient.lift _ f (RingHom.ker f
.span_singleton_le_iff_mem.mpr hr')) (Ideal.Quotient.lift_surjective_of_surjective _ _ hf)

Depends on / 依赖: Ideal.Quotient.lift, Ideal.Quotient.lift_surjective_of_surjective, Quotient, RingHom, RingHom.ker, le_trans, lift_surjective_of_surjective, ringKrullDim_le_of_surjective, ringKrullDim_quotient_succ_le_of_nonZeroDivisor, span_singleton_le_iff_mem, span_singleton_le_iff_mem.mpr
-/
lemma ringKrullDim_succ_le_of_surjective (f : R ->+* S) (hf : Function.Surjective f)
    {r : R} (hr : r in R⁰) (hr' : f r = 0) : ringKrullDim S + 1 <= ringKrullDim R := by
  refine le_trans ?_ (ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr)
  gcongr
  exact ringKrullDim_le_of_surjective (Ideal.Quotient.lift _ f (RingHom.ker f
.span_singleton_le_iff_mem.mpr hr')) (Ideal.Quotient.lift_surjective_of_surjective _ _ hf)

open Polynomial in
/--
lemma `ringKrullDim_succ_le_ringKrullDim_polynomial` / 引理 `ringKrullDim_succ_le_ringKrullDim_polynomial`

English:
lemma ringKrullDim_succ_le_ringKrullDim_polynomial
  proof: ringKrullDim_succ_le_of_surjective constantCoeff (⟨C ·, coeff_C_zero⟩)
    X_mem_nonzeroDivisors coeff_X_zero

中文:
引理 ringKrullDim_succ_le_ringKrullDim_polynomial
  证明: ringKrullDim_succ_le_of_surjective constantCoeff (⟨C ·, coeff_C_zero⟩)
    X_mem_nonzeroDivisors coeff_X_zero

Depends on / 依赖: X_mem_nonzeroDivisors, coeff_C_zero, coeff_X_zero, constantCoeff, ringKrullDim_succ_le_of_surjective
-/
lemma ringKrullDim_succ_le_ringKrullDim_polynomial :
    ringKrullDim R + 1 <= ringKrullDim R[X] :=
  ringKrullDim_succ_le_of_surjective constantCoeff (⟨C ·, coeff_C_zero⟩)
    X_mem_nonzeroDivisors coeff_X_zero

open MvPolynomial in
@[simp]
/--
lemma `ringKrullDim_mvPolynomial_of_isEmpty` / 引理 `ringKrullDim_mvPolynomial_of_isEmpty`

English:
lemma ringKrullDim_mvPolynomial_of_isEmpty
  given: (σ : Type*) [IsEmpty σ]
  proof: ringKrullDim_eq_of_ringEquiv (isEmptyRingEquiv _ _)

中文:
引理 ringKrullDim_mvPolynomial_of_isEmpty
  条件: (σ : 类型) [是空 σ]
  证明: ringKrullDim_eq_of_ringEquiv (isEmptyRingEquiv _ _)

Depends on / 依赖: isEmptyRingEquiv, ringKrullDim_eq_of_ringEquiv
-/
lemma ringKrullDim_mvPolynomial_of_isEmpty (σ : Type*) [IsEmpty σ] :
    ringKrullDim (MvPolynomial σ R) = ringKrullDim R :=
  ringKrullDim_eq_of_ringEquiv (isEmptyRingEquiv _ _)

open MvPolynomial in
/--
lemma `ringKrullDim_add_natCard_le_ringKrullDim_mvPolynomial` / 引理 `ringKrullDim_add_natCard_le_ringKrullDim_mvPolynomial`

English:
lemma ringKrullDim_add_natCard_le_ringKrullDim_mvPolynomial
  given: (σ : Type*) [Finite σ]
  proof: by
  induction σ using Finite.induction_empty_option with
  | of_equiv e H =>
    convert! ← H using 1
    · rw [Nat.card_congr e]
    · exact ringKrullDim_eq_of_ringEquiv (renameEquiv _ e).toRingEquiv
  | h_empty => simp
  | h_option IH =>
    simp only [Nat.card_eq_fintype_card, Fintype.card_option, Nat.cast_add, Nat.cast_one,
      ← add_assoc] at IH ⊢
    grw [IH, ringKrullDim_succ_le_ringKrullDim_polynomial]
    exact (ringKrullDim_eq_of_ringEquiv (MvPolynomial.optionEquivLeft _ _).toRingEquiv).ge

中文:
引理 ringKrullDim_add_natCard_le_ringKrullDim_mvPolynomial
  条件: (σ : 类型) [有限 σ]
  证明: by
  induction σ using Finite.induction_empty_option with
  | of_equiv e H =>
    convert! ← H using 1
    · rw [Nat.card_congr e]
    · exact ringKrullDim_eq_of_ringEquiv (renameEquiv _ e).toRingEquiv
  | h_empty => simp
  | h_option IH =>
    simp only [Nat.card_eq_fintype_card, Fintype.card_option, Nat.cast_add, Nat.cast_one,
      ← add_assoc] at IH ⊢
    grw [IH, ringKrullDim_succ_le_ringKrullDim_polynomial]
    exact (ringKrullDim_eq_of_ringEquiv (MvPolynomial.optionEquivLeft _ _).toRingEquiv).ge

Depends on / 依赖: Finite, Finite.induction_empty_option, Fintype, Fintype.card_option, MvPolynomial, MvPolynomial.optionEquivLeft, Nat.card_congr, Nat.card_eq_fintype_card, Nat.cast_add, Nat.cast_one, add_assoc, card_congr, card_eq_fintype_card, card_option, cast_add, cast_one, convert, h_empty, h_option, induction_empty_option
-/
lemma ringKrullDim_add_natCard_le_ringKrullDim_mvPolynomial (σ : Type*) [Finite σ] :
    ringKrullDim R + Nat.card σ <= ringKrullDim (MvPolynomial σ R) := by
  induction σ using Finite.induction_empty_option with
  | of_equiv e H =>
    convert! ← H using 1
    · rw [Nat.card_congr e]
    · exact ringKrullDim_eq_of_ringEquiv (renameEquiv _ e).toRingEquiv
  | h_empty => simp
  | h_option IH =>
    simp only [Nat.card_eq_fintype_card, Fintype.card_option, Nat.cast_add, Nat.cast_one,
      ← add_assoc] at IH ⊢
    grw [IH, ringKrullDim_succ_le_ringKrullDim_polynomial]
    exact (ringKrullDim_eq_of_ringEquiv (MvPolynomial.optionEquivLeft _ _).toRingEquiv).ge

open MvPolynomial in
/--
lemma `ringKrullDim_add_enatCard_le_ringKrullDim_mvPolynomial` / 引理 `ringKrullDim_add_enatCard_le_ringKrullDim_mvPolynomial`

English:
lemma ringKrullDim_add_enatCard_le_ringKrullDim_mvPolynomial
  given: (σ : Type*)
  proof: by
  nontriviality R
  cases finite_or_infinite σ
  · rw [ENat.card_eq_coe_natCard]
    push_cast
    exact ringKrullDim_add_natCard_le_ringKrullDim_mvPolynomial _
  · simp only [ENat.card_eq_top_of_infinite, WithBot.coe_top]
    suffices ringKrullDim (MvPolynomial σ R) = ⊤ by simp_all
    rw [ENat.WithBot.eq_top_iff_forall_ge]
    intro n
    let ι := Infinite.natEmbedding σ ∘ Fin.val (n := n + 1)
    have := Function.invFun_surjective (f := ι) ((Infinite.natEmbedding σ).2.comp Fin.val_injective)
    refine le_trans ?_ (ringKrullDim_le_of_surjective
      (rename (R := R) _).toRingHom (rename_surjective _ this))
    refine le_trans ?_ (ringKrullDim_add_natCard_le_ringKrullDim_mvPolynomial _)
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin, Nat.cast_add, Nat.cast_one]
    trans n + 1
    · norm_cast
      simp
    · exact WithBot.le_add_self Order.bot_lt_krullDim.ne' _

中文:
引理 ringKrullDim_add_enatCard_le_ringKrullDim_mvPolynomial
  条件: (σ : 类型)
  证明: by
  nontriviality R
  cases finite_or_infinite σ
  · rw [ENat.card_eq_coe_natCard]
    push_cast
    exact ringKrullDim_add_natCard_le_ringKrullDim_mvPolynomial _
  · simp only [ENat.card_eq_top_of_infinite, WithBot.coe_top]
    suffices ringKrullDim (MvPolynomial σ R) = ⊤ by simp_all
    rw [ENat.WithBot.eq_top_iff_forall_ge]
    intro n
    let ι := Infinite.natEmbedding σ ∘ Fin.val (n := n + 1)
    have := Function.invFun_surjective (f := ι) ((Infinite.natEmbedding σ).2.comp Fin.val_injective)
    refine le_trans ?_ (ringKrullDim_le_of_surjective
      (rename (R := R) _).toRingHom (rename_surjective _ this))
    refine le_trans ?_ (ringKrullDim_add_natCard_le_ringKrullDim_mvPolynomial _)
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin, Nat.cast_add, Nat.cast_one]
    trans n + 1
    · norm_cast
      simp
    · exact WithBot.le_add_self Order.bot_lt_krullDim.ne' _

Depends on / 依赖: ENat.WithBot.eq_top_iff_forall_ge, ENat.card_eq_coe_natCard, ENat.card_eq_top_of_infinite, Fin.val, Fin.val_injective, Function, Function.invFun_surjective, Infinite, Infinite.natEmbedding, MvPolynomial, WithBot, WithBot.coe_top, card_eq_coe_natCard, card_eq_top_of_infinite, coe_top, eq_top_iff_forall_ge, finite_or_infinite, invFun_surjective, le_trans, natEmbedding
-/
lemma ringKrullDim_add_enatCard_le_ringKrullDim_mvPolynomial (σ : Type*) :
    ringKrullDim R + ENat.card σ <= ringKrullDim (MvPolynomial σ R) := by
  nontriviality R
  cases finite_or_infinite σ
  · rw [ENat.card_eq_coe_natCard]
    push_cast
    exact ringKrullDim_add_natCard_le_ringKrullDim_mvPolynomial _
  · simp only [ENat.card_eq_top_of_infinite, WithBot.coe_top]
    suffices ringKrullDim (MvPolynomial σ R) = ⊤ by simp_all
    rw [ENat.WithBot.eq_top_iff_forall_ge]
    intro n
    let ι := Infinite.natEmbedding σ ∘ Fin.val (n := n + 1)
    have := Function.invFun_surjective (f := ι) ((Infinite.natEmbedding σ).2.comp Fin.val_injective)
    refine le_trans ?_ (ringKrullDim_le_of_surjective
      (rename (R := R) _).toRingHom (rename_surjective _ this))
    refine le_trans ?_ (ringKrullDim_add_natCard_le_ringKrullDim_mvPolynomial _)
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin, Nat.cast_add, Nat.cast_one]
    trans n + 1
    · norm_cast
      simp
    · exact WithBot.le_add_self Order.bot_lt_krullDim.ne' _

open PowerSeries in
/--
lemma `ringKrullDim_succ_le_ringKrullDim_powerseries` / 引理 `ringKrullDim_succ_le_ringKrullDim_powerseries`

English:
lemma ringKrullDim_succ_le_ringKrullDim_powerseries
  proof: ringKrullDim_succ_le_of_surjective constantCoeff (⟨C ·, rfl⟩)
    MvPowerSeries.X_mem_nonzeroDivisors constantCoeff_X

中文:
引理 ringKrullDim_succ_le_ringKrullDim_powerseries
  证明: ringKrullDim_succ_le_of_surjective constantCoeff (⟨C ·, rfl⟩)
    MvPowerSeries.X_mem_nonzeroDivisors constantCoeff_X

Depends on / 依赖: MvPowerSeries, MvPowerSeries.X_mem_nonzeroDivisors, X_mem_nonzeroDivisors, constantCoeff, constantCoeff_X, ringKrullDim_succ_le_of_surjective
-/
lemma ringKrullDim_succ_le_ringKrullDim_powerseries :
    ringKrullDim R + 1 <= ringKrullDim (PowerSeries R) :=
  ringKrullDim_succ_le_of_surjective constantCoeff (⟨C ·, rfl⟩)
    MvPowerSeries.X_mem_nonzeroDivisors constantCoeff_X
