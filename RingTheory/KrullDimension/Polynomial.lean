/-
Copyright (c) 2025 Jingting Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang, Sihan Su, Yi Song, Christian Merten
-/
module

public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.RingTheory.KrullDimension.PID
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

/-!
# Krull dimension of polynomial ring

This file proves properties of the Krull dimension of the polynomial ring over a commutative ring

## Main results

* `Polynomial.ringKrullDim_le`: the Krull dimension of the polynomial ring over a commutative ring
  `R` is less than `2 * (ringKrullDim R) + 1`.

For noetherian rings:
* `Polynomial.ringKrullDim_of_isNoetherianRing`: the Krull dimension of `R[X]` is `dim R + 1`.
* `MvPolynomial.ringKrullDim_of_isNoetherianRing`: the Krull dimension of `R[X₁, ..., Xₙ]` is
  `dim R + n`.
-/

public section

/--
theorem `Polynomial.ringKrullDim_le` / 定理 `Polynomial.ringKrullDim_le`

English:
theorem Polynomial.ringKrullDim_le
  given: {R : Type*} [CommRing R]
  proof: by
  rw [ringKrullDim]; rw [ringKrullDim]
  apply Order.krullDim_le_of_krullDim_preimage_le' (PrimeSpectrum.comap C) ?_ (fun p => ?_)
  · exact fun {a b} h => Ideal.comap_mono h
  · rw [show C = (algebraMap R (Polynomial R)) from rfl, Order.krullDim_eq_of_orderIso
      (PrimeSpectrum.preimageOrderIsoFiber R (Polynomial R) p), ← ringKrullDim,
      ← ringKrullDim_eq_of_ringEquiv (polyEquivTensor R (p.asIdeal.ResidueField)).toRingEquiv,
      ← Ring.krullDimLE_iff]
    infer_instance

中文:
定理 多项式.ringKrullDim_le
  条件: {R : 类型} [交换环 R]
  证明: by
  rw [ringKrullDim]; rw [ringKrullDim]
  apply Order.krullDim_le_of_krullDim_preimage_le' (PrimeSpectrum.comap C) ?_ (fun p => ?_)
  · exact fun {a b} h => Ideal.comap_mono h
  · rw [show C = (algebraMap R (Polynomial R)) from rfl, Order.krullDim_eq_of_orderIso
      (PrimeSpectrum.preimageOrderIsoFiber R (Polynomial R) p), ← ringKrullDim,
      ← ringKrullDim_eq_of_ringEquiv (polyEquivTensor R (p.asIdeal.ResidueField)).toRingEquiv,
      ← Ring.krullDimLE_iff]
    infer_instance

Depends on / 依赖: Ideal.comap_mono, Order.krullDim_eq_of_orderIso, Order.krullDim_le_of_krullDim_preimage_le, Polynomial, PrimeSpectrum, PrimeSpectrum.comap, PrimeSpectrum.preimageOrderIsoFiber, ResidueField, Ring.krullDimLE_iff, algebraMap, asIdeal, comap_mono, infer_instance, krullDimLE_iff, krullDim_eq_of_orderIso, krullDim_le_of_krullDim_preimage_le, p.asIdeal.ResidueField, polyEquivTensor, preimageOrderIsoFiber, ringKrullDim
-/
theorem Polynomial.ringKrullDim_le {R : Type*} [CommRing R] :
    ringKrullDim (Polynomial R) <= 2 * (ringKrullDim R) + 1 := by
  rw [ringKrullDim]; rw [ringKrullDim]
  apply Order.krullDim_le_of_krullDim_preimage_le' (PrimeSpectrum.comap C) ?_ (fun p => ?_)
  · exact fun {a b} h => Ideal.comap_mono h
  · rw [show C = (algebraMap R (Polynomial R)) from rfl, Order.krullDim_eq_of_orderIso
      (PrimeSpectrum.preimageOrderIsoFiber R (Polynomial R) p), ← ringKrullDim,
      ← ringKrullDim_eq_of_ringEquiv (polyEquivTensor R (p.asIdeal.ResidueField)).toRingEquiv,
      ← Ring.krullDimLE_iff]
    infer_instance

variable {R : Type*} [CommRing R] [IsNoetherianRing R]

namespace Polynomial

open Ideal IsLocalization

/--
lemma `height_eq_height_add_one_of_isMaximal` / 引理 `height_eq_height_add_one_of_isMaximal`

English:
lemma height_eq_height_add_one_of_isMaximal
  statement: (p : Ideal R) [p.IsMaximal] (P : Ideal R[X])
  proof: by
  let _ : Field (R ⧸ p) := Quotient.field p
  suffices h : (P.map (Ideal.Quotient.mk (Ideal.map (algebraMap R R[X]) p))).height = 1 by
    rw [height_eq_height_add_of_liesOver_of_hasGoingDown p]; rw [h]
  let e : (R[X] ⧸ (p.map (algebraMap R R[X]))) ≃+* (R ⧸ p)[X] :=
    (polynomialQuotientEquivQuotientPolynomial p).symm
let P' : Ideal (R ⧸ p)[X] := Ideal.map e P.map (Ideal.Quotient.mk <| p.map (algebraMap R R[X]))
  have : (P.map (Ideal.Quotient.mk <| p.map (algebraMap R R[X]))).IsMaximal := by
    refine .map_of_surjective_of_ker_le Quotient.mk_surjective ?_
    rw [mk_ker]; rw [LiesOver.over (P := P) (p := p)]
    exact map_comap_le
  have : P'.IsMaximal := map_isMaximal_of_equiv e
  have : P'.height = 1 :=
    IsPrincipalIdealRing.height_eq_one_of_isMaximal P' (Polynomial.not_isField (R ⧸ p))
  rwa [← e.height_map <| P.map (Ideal.Quotient.mk <| p.map (algebraMap R R[X]))]

中文:
引理 height_eq_height_add_one_of_isMaximal
  结论: (p : 理想 R) [p.是极大] (P : 理想 R[X])
  证明: by
  let _ : Field (R ⧸ p) := Quotient.field p
  suffices h : (P.map (Ideal.Quotient.mk (Ideal.map (algebraMap R R[X]) p))).height = 1 by
    rw [height_eq_height_add_of_liesOver_of_hasGoingDown p]; rw [h]
  let e : (R[X] ⧸ (p.map (algebraMap R R[X]))) ≃+* (R ⧸ p)[X] :=
    (polynomialQuotientEquivQuotientPolynomial p).symm
let P' : Ideal (R ⧸ p)[X] := Ideal.map e P.map (Ideal.Quotient.mk <| p.map (algebraMap R R[X]))
  have : (P.map (Ideal.Quotient.mk <| p.map (algebraMap R R[X]))).IsMaximal := by
    refine .map_of_surjective_of_ker_le Quotient.mk_surjective ?_
    rw [mk_ker]; rw [LiesOver.over (P := P) (p := p)]
    exact map_comap_le
  have : P'.IsMaximal := map_isMaximal_of_equiv e
  have : P'.height = 1 :=
    IsPrincipalIdealRing.height_eq_one_of_isMaximal P' (Polynomial.not_isField (R ⧸ p))
  rwa [← e.height_map <| P.map (Ideal.Quotient.mk <| p.map (algebraMap R R[X]))]
-/
private lemma height_eq_height_add_one_of_isMaximal (p : Ideal R) [p.IsMaximal] (P : Ideal R[X])
    [P.IsMaximal] [P.LiesOver p] : P.height = p.height + 1 := by
  let _ : Field (R ⧸ p) := Quotient.field p
  suffices h : (P.map (Ideal.Quotient.mk (Ideal.map (algebraMap R R[X]) p))).height = 1 by
    rw [height_eq_height_add_of_liesOver_of_hasGoingDown p]; rw [h]
  let e : (R[X] ⧸ (p.map (algebraMap R R[X]))) ≃+* (R ⧸ p)[X] :=
    (polynomialQuotientEquivQuotientPolynomial p).symm
let P' : Ideal (R ⧸ p)[X] := Ideal.map e P.map (Ideal.Quotient.mk <| p.map (algebraMap R R[X]))
  have : (P.map (Ideal.Quotient.mk <| p.map (algebraMap R R[X]))).IsMaximal := by
    refine .map_of_surjective_of_ker_le Quotient.mk_surjective ?_
    rw [mk_ker]; rw [LiesOver.over (P := P) (p := p)]
    exact map_comap_le
  have : P'.IsMaximal := map_isMaximal_of_equiv e
  have : P'.height = 1 :=
    IsPrincipalIdealRing.height_eq_one_of_isMaximal P' (Polynomial.not_isField (R ⧸ p))
  rwa [← e.height_map <| P.map (Ideal.Quotient.mk <| p.map (algebraMap R R[X]))]

/--
lemma `height_map_C` / 引理 `height_map_C`

English:
lemma height_map_C
  given: (p : Ideal R) [p.IsMaximal]
  statement: (p.map C).height = p.height
  proof: by
  have : (p.map C).LiesOver p := ⟨IsMaximal.eq_of_le inferInstance IsPrime.ne_top' le_comap_map⟩
  simp [height_eq_height_add_of_liesOver_of_hasGoingDown p]

中文:
引理 height_map_C
  条件: (p : 理想 R) [p.是极大]
  结论: (p.map C).height = p.height
  证明: by
  have : (p.map C).LiesOver p := ⟨IsMaximal.eq_of_le inferInstance IsPrime.ne_top' le_comap_map⟩
  simp [height_eq_height_add_of_liesOver_of_hasGoingDown p]

Depends on / 依赖: IsMaximal, IsMaximal.eq_of_le, IsPrime, IsPrime.ne_top, LiesOver, eq_of_le, height_eq_height_add_of_liesOver_of_hasGoingDown, le_comap_map, ne_top, p.map
-/
lemma height_map_C (p : Ideal R) [p.IsMaximal] : (p.map C).height = p.height := by
  have : (p.map C).LiesOver p := ⟨IsMaximal.eq_of_le inferInstance IsPrime.ne_top' le_comap_map⟩
  simp [height_eq_height_add_of_liesOver_of_hasGoingDown p]

attribute [local instance] Polynomial.algebra Polynomial.isLocalization in
/--
lemma `height_eq_height_add_one` / 引理 `height_eq_height_add_one`

English:
lemma height_eq_height_add_one
  statement: (p : Ideal R)
  proof: by
  have : p.IsPrime := by rw [P.over_def p]; infer_instance
  let Rₚ := Localization.AtPrime p
  set p' : Ideal Rₚ := p.map (algebraMap R Rₚ) with p'_def
  have : p'.IsMaximal := by
    rw [p'_def]; rw [Localization.AtPrime.map_eq_maximalIdeal]
    exact IsLocalRing.maximalIdeal.isMaximal Rₚ
  let P' : Ideal Rₚ[X] := P.map (algebraMap R[X] Rₚ[X])
  have disj : Disjoint (p.primeCompl.map C : Set R[X]) P := by
    refine Set.disjoint_left.mpr fun a ⟨b, hb⟩ ha => hb.1 ?_
    rwa [SetLike.mem_coe, LiesOver.over (P := P) (p := p), mem_comap, algebraMap_eq, hb.2]
  have eq := under_map_of_isPrime_disjoint _ Rₚ[X] ‹P.IsMaximal›.isPrime disj
  have : (P'.under R[X]).IsMaximal := eq.symm ▸ ‹P.IsMaximal›
  have : P'.IsMaximal := .of_isLocalization_of_disjoint (p.primeCompl.map C)
  have : P'.LiesOver p' := liesOver_of_isPrime_of_disjoint p.primeCompl _ _ disj
  have eq1 : p.height = p'.height := by
    rw [height_map_of_disjoint p.primeCompl]
exact Disjoint.symm Set.disjoint_left.mpr fun _ a b => b a
  have eq2 : P.height = P'.height := by
    rw [height_map_of_disjoint (Submonoid.map C <| p.primeCompl) _ disj]
  rw [eq1]; rw [eq2]
  apply height_eq_height_add_one_of_isMaximal p' P'

中文:
引理 height_eq_height_add_one
  结论: (p : 理想 R)
  证明: by
  have : p.IsPrime := by rw [P.over_def p]; infer_instance
  let Rₚ := Localization.AtPrime p
  set p' : Ideal Rₚ := p.map (algebraMap R Rₚ) with p'_def
  have : p'.IsMaximal := by
    rw [p'_def]; rw [Localization.AtPrime.map_eq_maximalIdeal]
    exact IsLocalRing.maximalIdeal.isMaximal Rₚ
  let P' : Ideal Rₚ[X] := P.map (algebraMap R[X] Rₚ[X])
  have disj : Disjoint (p.primeCompl.map C : Set R[X]) P := by
    refine Set.disjoint_left.mpr fun a ⟨b, hb⟩ ha => hb.1 ?_
    rwa [SetLike.mem_coe, LiesOver.over (P := P) (p := p), mem_comap, algebraMap_eq, hb.2]
  have eq := under_map_of_isPrime_disjoint _ Rₚ[X] ‹P.IsMaximal›.isPrime disj
  have : (P'.under R[X]).IsMaximal := eq.symm ▸ ‹P.IsMaximal›
  have : P'.IsMaximal := .of_isLocalization_of_disjoint (p.primeCompl.map C)
  have : P'.LiesOver p' := liesOver_of_isPrime_of_disjoint p.primeCompl _ _ disj
  have eq1 : p.height = p'.height := by
    rw [height_map_of_disjoint p.primeCompl]
exact Disjoint.symm Set.disjoint_left.mpr fun _ a b => b a
  have eq2 : P.height = P'.height := by
    rw [height_map_of_disjoint (Submonoid.map C <| p.primeCompl) _ disj]
  rw [eq1]; rw [eq2]
  apply height_eq_height_add_one_of_isMaximal p' P'

Depends on / 依赖: AtPrime, Disjoint, IsLocalRing, IsLocalRing.maximalIdeal.isMaximal, IsMaximal, IsPrime, LiesOver, LiesOver.over, Localization, Localization.AtPrime, Localization.AtPrime.map_eq_maximalIdeal, P.map, P.over_def, Set.disjoint_left.mpr, SetLike, SetLike.mem_coe, _def, algebraMap, disjoint_left, infer_instance
-/
lemma height_eq_height_add_one (p : Ideal R)
    (P : Ideal R[X]) [P.IsMaximal] [P.LiesOver p] :
    P.height = p.height + 1 := by
  have : p.IsPrime := by rw [P.over_def p]; infer_instance
  let Rₚ := Localization.AtPrime p
  set p' : Ideal Rₚ := p.map (algebraMap R Rₚ) with p'_def
  have : p'.IsMaximal := by
    rw [p'_def]; rw [Localization.AtPrime.map_eq_maximalIdeal]
    exact IsLocalRing.maximalIdeal.isMaximal Rₚ
  let P' : Ideal Rₚ[X] := P.map (algebraMap R[X] Rₚ[X])
  have disj : Disjoint (p.primeCompl.map C : Set R[X]) P := by
    refine Set.disjoint_left.mpr fun a ⟨b, hb⟩ ha => hb.1 ?_
    rwa [SetLike.mem_coe, LiesOver.over (P := P) (p := p), mem_comap, algebraMap_eq, hb.2]
  have eq := under_map_of_isPrime_disjoint _ Rₚ[X] ‹P.IsMaximal›.isPrime disj
  have : (P'.under R[X]).IsMaximal := eq.symm ▸ ‹P.IsMaximal›
  have : P'.IsMaximal := .of_isLocalization_of_disjoint (p.primeCompl.map C)
  have : P'.LiesOver p' := liesOver_of_isPrime_of_disjoint p.primeCompl _ _ disj
  have eq1 : p.height = p'.height := by
    rw [height_map_of_disjoint p.primeCompl]
exact Disjoint.symm Set.disjoint_left.mpr fun _ a b => b a
  have eq2 : P.height = P'.height := by
    rw [height_map_of_disjoint (Submonoid.map C <| p.primeCompl) _ disj]
  rw [eq1]; rw [eq2]
  apply height_eq_height_add_one_of_isMaximal p' P'

/-- If `R` is Noetherian, `dim R[X] = dim R + 1`. -/
@[simp]
/--
lemma `ringKrullDim_of_isNoetherianRing` / 引理 `ringKrullDim_of_isNoetherianRing`

English:
lemma ringKrullDim_of_isNoetherianRing
  statement: ringKrullDim R[X] = ringKrullDim R + 1
  proof: by
  refine le_antisymm ?_ ?_
  · nontriviality R[X]
    refine (ringKrullDim_le_iff_isMaximal_height_le (ringKrullDim R + 1)).mpr fun M hM => ?_
    rw [height_eq_height_add_one (M.under R) M]; rw [WithBot.coe_add]; rw [WithBot.coe_one]
    gcongr
    exact Ideal.height_le_ringKrullDim_of_ne_top Ideal.IsPrime.ne_top'
  · exact ringKrullDim_succ_le_ringKrullDim_polynomial

中文:
引理 ringKrullDim_of_isNoetherianRing
  结论: ringKrullDim R[X] = ringKrullDim R + 1
  证明: by
  refine le_antisymm ?_ ?_
  · nontriviality R[X]
    refine (ringKrullDim_le_iff_isMaximal_height_le (ringKrullDim R + 1)).mpr fun M hM => ?_
    rw [height_eq_height_add_one (M.under R) M]; rw [WithBot.coe_add]; rw [WithBot.coe_one]
    gcongr
    exact Ideal.height_le_ringKrullDim_of_ne_top Ideal.IsPrime.ne_top'
  · exact ringKrullDim_succ_le_ringKrullDim_polynomial

Depends on / 依赖: Ideal.IsPrime.ne_top, Ideal.height_le_ringKrullDim_of_ne_top, IsPrime, M.under, WithBot, WithBot.coe_add, WithBot.coe_one, coe_add, coe_one, height_eq_height_add_one, height_le_ringKrullDim_of_ne_top, le_antisymm, ne_top, nontriviality, ringKrullDim, ringKrullDim_le_iff_isMaximal_height_le, ringKrullDim_succ_le_ringKrullDim_polynomial
-/
lemma ringKrullDim_of_isNoetherianRing : ringKrullDim R[X] = ringKrullDim R + 1 := by
  refine le_antisymm ?_ ?_
  · nontriviality R[X]
    refine (ringKrullDim_le_iff_isMaximal_height_le (ringKrullDim R + 1)).mpr fun M hM => ?_
    rw [height_eq_height_add_one (M.under R) M]; rw [WithBot.coe_add]; rw [WithBot.coe_one]
    gcongr
    exact Ideal.height_le_ringKrullDim_of_ne_top Ideal.IsPrime.ne_top'
  · exact ringKrullDim_succ_le_ringKrullDim_polynomial

end Polynomial

/-- If `R` is Noetherian, `dim R[X₁, ..., Xₙ] = dim R + n`. -/
@[simp]
/--
lemma `MvPolynomial.ringKrullDim_of_isNoetherianRing` / 引理 `MvPolynomial.ringKrullDim_of_isNoetherianRing`

English:
lemma MvPolynomial.ringKrullDim_of_isNoetherianRing
  given: {ι : Type*} [Finite ι]
  proof: by
  induction ι using Finite.induction_empty_option with
  | of_equiv e H =>
    convert! ← H using 1
    · exact ringKrullDim_eq_of_ringEquiv (renameEquiv _ e).toRingEquiv
    · rw [Nat.card_congr e]
  | h_empty => simp
  | h_option IH =>
    simp only [Nat.card_eq_fintype_card, Fintype.card_option, Nat.cast_add, Nat.cast_one,
      ← add_assoc] at IH ⊢
    rw [ringKrullDim_eq_of_ringEquiv (MvPolynomial.optionEquivLeft _ _).toRingEquiv]; rw [Polynomial.ringKrullDim_of_isNoetherianRing]; rw [IH]

中文:
引理 多元多项式.ringKrullDim_of_isNoetherianRing
  条件: {ι : 类型} [有限 ι]
  证明: by
  induction ι using Finite.induction_empty_option with
  | of_equiv e H =>
    convert! ← H using 1
    · exact ringKrullDim_eq_of_ringEquiv (renameEquiv _ e).toRingEquiv
    · rw [Nat.card_congr e]
  | h_empty => simp
  | h_option IH =>
    simp only [Nat.card_eq_fintype_card, Fintype.card_option, Nat.cast_add, Nat.cast_one,
      ← add_assoc] at IH ⊢
    rw [ringKrullDim_eq_of_ringEquiv (MvPolynomial.optionEquivLeft _ _).toRingEquiv]; rw [Polynomial.ringKrullDim_of_isNoetherianRing]; rw [IH]

Depends on / 依赖: Finite, Finite.induction_empty_option, Fintype, Fintype.card_option, MvPolynomial, MvPolynomial.optionEquivLeft, Nat.card_congr, Nat.card_eq_fintype_card, Nat.cast_add, Nat.cast_one, Polynomial, Polynomial.ringKrullDim_of_isNoetherianRing, add_assoc, card_congr, card_eq_fintype_card, card_option, cast_add, cast_one, convert, h_empty
-/
lemma MvPolynomial.ringKrullDim_of_isNoetherianRing {ι : Type*} [Finite ι] :
    ringKrullDim (MvPolynomial ι R) = ringKrullDim R + Nat.card ι := by
  induction ι using Finite.induction_empty_option with
  | of_equiv e H =>
    convert! ← H using 1
    · exact ringKrullDim_eq_of_ringEquiv (renameEquiv _ e).toRingEquiv
    · rw [Nat.card_congr e]
  | h_empty => simp
  | h_option IH =>
    simp only [Nat.card_eq_fintype_card, Fintype.card_option, Nat.cast_add, Nat.cast_one,
      ← add_assoc] at IH ⊢
    rw [ringKrullDim_eq_of_ringEquiv (MvPolynomial.optionEquivLeft _ _).toRingEquiv]; rw [Polynomial.ringKrullDim_of_isNoetherianRing]; rw [IH]
