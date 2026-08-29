/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Group.AEStabilizer

/-!
# Measure-theoretic results about the additive circle

The file is a place to collect measure-theoretic results about the additive circle.

## Main definitions:

* `AddCircle.closedBall_ae_eq_ball`: open and closed balls in the additive circle are almost
  equal
* `AddCircle.isAddFundamentalDomain_of_ae_ball`: a ball is a fundamental domain for rational
  angle rotation in the additive circle

-/

public section


open Set Function Filter MeasureTheory MeasureTheory.Measure Metric

open scoped Finset MeasureTheory Pointwise Topology ENNReal

namespace AddCircle

variable {T : Real} [hT : Fact (0 < T)]

/--
theorem `closedBall_ae_eq_ball` / 定理 `closedBall_ae_eq_ball`

English:
theorem closedBall_ae_eq_ball
  given: {x : AddCircle T} {ε : Real}
  statement: closedBall x ε =ᵐ[volume] ball x ε
  proof: by
  rcases le_or_gt ε 0 with hε | hε
  · rw [ball_eq_empty.mpr hε, ae_eq_empty, volume_closedBall,
      min_eq_right (by linarith [hT.out] : 2 * ε <= T), ENNReal.ofReal_eq_zero]
    exact mul_nonpos_of_nonneg_of_nonpos zero_le_two hε
  · suffices volume (closedBall x ε) <= volume (ball x ε) from
      (ae_eq_of_subset_of_measure_ge ball_subset_closedBall this
        measurableSet_ball.nullMeasurableSet (measure_ne_top _ _)).symm
    have : Tendsto (fun δ => volume (closedBall x δ)) (𝓝[<] ε) (𝓝 <| volume (closedBall x ε)) := by
      simp_rw [volume_closedBall]
      refine ENNReal.tendsto_ofReal (Tendsto.min tendsto_const_nhds <| Tendsto.const_mul _ ?_)
      exact nhdsWithin_le_nhds
refine le_of_tendsto this mem_of_superset (Ioo_mem_nhdsLT hε) fun r hr => ?_
    exact measure_mono (closedBall_subset_ball hr.2)

中文:
定理 closedBall_ae_eq_ball
  条件: {x : AddCircle T} {ε : 实数}
  结论: closedBall x ε =ᵐ[volume] ball x ε
  证明: by
  rcases le_or_gt ε 0 with hε | hε
  · rw [ball_eq_empty.mpr hε, ae_eq_empty, volume_closedBall,
      min_eq_right (by linarith [hT.out] : 2 * ε <= T), ENNReal.ofReal_eq_zero]
    exact mul_nonpos_of_nonneg_of_nonpos zero_le_two hε
  · suffices volume (closedBall x ε) <= volume (ball x ε) from
      (ae_eq_of_subset_of_measure_ge ball_subset_closedBall this
        measurableSet_ball.nullMeasurableSet (measure_ne_top _ _)).symm
    have : Tendsto (fun δ => volume (closedBall x δ)) (𝓝[<] ε) (𝓝 <| volume (closedBall x ε)) := by
      simp_rw [volume_closedBall]
      refine ENNReal.tendsto_ofReal (Tendsto.min tendsto_const_nhds <| Tendsto.const_mul _ ?_)
      exact nhdsWithin_le_nhds
refine le_of_tendsto this mem_of_superset (Ioo_mem_nhdsLT hε) fun r hr => ?_
    exact measure_mono (closedBall_subset_ball hr.2)

Depends on / 依赖: ENNReal, ENNReal.ofReal_eq_zero, Tendsto, ae_eq_empty, ae_eq_of_subset_of_measure_ge, ball_eq_empty, ball_eq_empty.mpr, ball_subset_closedBall, closedBall, hT.out, le_or_gt, measurableSet_ball, measurableSet_ball.nullMeasurableSet, measure_ne_top, min_eq_right, mul_nonpos_of_nonneg_of_nonpos, nullMeasurableSet, ofReal_eq_zero, volume, volume_closedBall
-/
theorem closedBall_ae_eq_ball {x : AddCircle T} {ε : Real} : closedBall x ε =ᵐ[volume] ball x ε := by
  rcases le_or_gt ε 0 with hε | hε
  · rw [ball_eq_empty.mpr hε, ae_eq_empty, volume_closedBall,
      min_eq_right (by linarith [hT.out] : 2 * ε <= T), ENNReal.ofReal_eq_zero]
    exact mul_nonpos_of_nonneg_of_nonpos zero_le_two hε
  · suffices volume (closedBall x ε) <= volume (ball x ε) from
      (ae_eq_of_subset_of_measure_ge ball_subset_closedBall this
        measurableSet_ball.nullMeasurableSet (measure_ne_top _ _)).symm
    have : Tendsto (fun δ => volume (closedBall x δ)) (𝓝[<] ε) (𝓝 <| volume (closedBall x ε)) := by
      simp_rw [volume_closedBall]
      refine ENNReal.tendsto_ofReal (Tendsto.min tendsto_const_nhds <| Tendsto.const_mul _ ?_)
      exact nhdsWithin_le_nhds
refine le_of_tendsto this mem_of_superset (Ioo_mem_nhdsLT hε) fun r hr => ?_
    exact measure_mono (closedBall_subset_ball hr.2)

/--
theorem `isAddFundamentalDomain_of_ae_ball` / 定理 `isAddFundamentalDomain_of_ae_ball`

English:
theorem isAddFundamentalDomain_of_ae_ball
  statement: (I : Set <| AddCircle T) (u x : AddCircle T)
  proof: by
  set G := AddSubgroup.zmultiples u
  set n := addOrderOf u
  set B := ball x (T / (2 * n))
  have hn : 1 <= (n : Real) := by norm_cast; linarith [hu.addOrderOf_pos]
  refine IsAddFundamentalDomain.mk_of_measure_univ_le ?_ ?_ ?_ ?_
  · -- `NullMeasurableSet I volume`
    exact measurableSet_ball.nullMeasurableSet.congr hI.symm
  · -- `∀ (g : G), g ≠ 0 → AEDisjoint volume (g +ᵥ I) I`
    rintro ⟨g, hg⟩ hg'
    replace hg' : g != 0 := by simpa only [Ne, AddSubgroup.mk_eq_zero] using hg'
    change AEDisjoint volume (g +ᵥ I) I
    refine AEDisjoint.congr (Disjoint.aedisjoint ?_)
      ((quasiMeasurePreserving_add_left volume (-g)).vadd_ae_eq_of_ae_eq g hI) hI
    have hBg : g +ᵥ B = ball (g + x) (T / (2 * n)) := by
      rw [add_comm g x]; rw [← singleton_add_ball _ x g]; rw [add_ball]; rw [thickening_singleton]
    rw [hBg]
    apply ball_disjoint_ball
    rw [dist_eq_norm]; rw [add_sub_cancel_right]; rw [div_mul_eq_div_div]; rw [← add_div]; rw [← add_div]; rw [add_self_div_two]; rw [div_le_iff₀' (by positivity : 0 < (n : Real))]; rw [← nsmul_eq_mul]
    refine (le_add_order_smul_norm_of_isOfFinAddOrder (hu.of_mem_zmultiples hg) hg').trans
      (nsmul_le_nsmul_left (norm_nonneg g) ?_)
    exact Nat.le_of_dvd (addOrderOf_pos_iff.mpr hu) (addOrderOf_dvd_of_mem_zmultiples hg)
  · -- `∀ (g : G), QuasiMeasurePreserving (VAdd.vadd g) volume volume`
    exact fun g => quasiMeasurePreserving_add_left (G := AddCircle T) volume g
  · -- `volume univ ≤ ∑' (g : G), volume (g +ᵥ I)`
    replace hI := hI.trans closedBall_ae_eq_ball.symm
    have : Fintype G := @Fintype.ofFinite _ hu.finite_zmultiples.to_subtype
    have hG_card : #(Finset.univ : Finset G) = n := by
      change _ = addOrderOf u
      rw [← Nat.card_zmultiples]; rw [Nat.card_eq_fintype_card]; rfl
    simp_rw [measure_vadd]
    rw [AddCircle.measure_univ]; rw [tsum_fintype]; rw [Finset.sum_const]; rw [measure_congr hI]; rw [volume_closedBall]; rw [← ENNReal.ofReal_nsmul]; rw [mul_div]; rw [mul_div_mul_comm]; rw [div_self]; rw [one_mul]; rw [min_eq_right (div_le_self hT.out.le hn)]; rw [hG_card]; rw [nsmul_eq_mul]; rw [mul_div_cancel₀ T (lt_of_lt_of_le zero_lt_one hn).ne.symm]
    exact two_ne_zero

中文:
定理 isAddFundamentalDomain_of_ae_ball
  结论: (I : 集合 <| AddCircle T) (u x : AddCircle T)
  证明: by
  set G := AddSubgroup.zmultiples u
  set n := addOrderOf u
  set B := ball x (T / (2 * n))
  have hn : 1 <= (n : Real) := by norm_cast; linarith [hu.addOrderOf_pos]
  refine IsAddFundamentalDomain.mk_of_measure_univ_le ?_ ?_ ?_ ?_
  · -- `NullMeasurableSet I volume`
    exact measurableSet_ball.nullMeasurableSet.congr hI.symm
  · -- `∀ (g : G), g ≠ 0 → AEDisjoint volume (g +ᵥ I) I`
    rintro ⟨g, hg⟩ hg'
    replace hg' : g != 0 := by simpa only [Ne, AddSubgroup.mk_eq_zero] using hg'
    change AEDisjoint volume (g +ᵥ I) I
    refine AEDisjoint.congr (Disjoint.aedisjoint ?_)
      ((quasiMeasurePreserving_add_left volume (-g)).vadd_ae_eq_of_ae_eq g hI) hI
    have hBg : g +ᵥ B = ball (g + x) (T / (2 * n)) := by
      rw [add_comm g x]; rw [← singleton_add_ball _ x g]; rw [add_ball]; rw [thickening_singleton]
    rw [hBg]
    apply ball_disjoint_ball
    rw [dist_eq_norm]; rw [add_sub_cancel_right]; rw [div_mul_eq_div_div]; rw [← add_div]; rw [← add_div]; rw [add_self_div_two]; rw [div_le_iff₀' (by positivity : 0 < (n : Real))]; rw [← nsmul_eq_mul]
    refine (le_add_order_smul_norm_of_isOfFinAddOrder (hu.of_mem_zmultiples hg) hg').trans
      (nsmul_le_nsmul_left (norm_nonneg g) ?_)
    exact Nat.le_of_dvd (addOrderOf_pos_iff.mpr hu) (addOrderOf_dvd_of_mem_zmultiples hg)
  · -- `∀ (g : G), QuasiMeasurePreserving (VAdd.vadd g) volume volume`
    exact fun g => quasiMeasurePreserving_add_left (G := AddCircle T) volume g
  · -- `volume univ ≤ ∑' (g : G), volume (g +ᵥ I)`
    replace hI := hI.trans closedBall_ae_eq_ball.symm
    have : Fintype G := @Fintype.ofFinite _ hu.finite_zmultiples.to_subtype
    have hG_card : #(Finset.univ : Finset G) = n := by
      change _ = addOrderOf u
      rw [← Nat.card_zmultiples]; rw [Nat.card_eq_fintype_card]; rfl
    simp_rw [measure_vadd]
    rw [AddCircle.measure_univ]; rw [tsum_fintype]; rw [Finset.sum_const]; rw [measure_congr hI]; rw [volume_closedBall]; rw [← ENNReal.ofReal_nsmul]; rw [mul_div]; rw [mul_div_mul_comm]; rw [div_self]; rw [one_mul]; rw [min_eq_right (div_le_self hT.out.le hn)]; rw [hG_card]; rw [nsmul_eq_mul]; rw [mul_div_cancel₀ T (lt_of_lt_of_le zero_lt_one hn).ne.symm]
    exact two_ne_zero

Depends on / 依赖: AEDisjoint, AddSubgroup, AddSubgroup.mk_eq_zero, AddSubgroup.zmultiples, IsAddFundamentalDomain, IsAddFundamentalDomain.mk_of_measure_univ_le, NullMeasurableSet, addOrderOf, addOrderOf_pos, hI.symm, hu.addOrderOf_pos, measurableSet_ball, measurableSet_ball.nullMeasurableSet.congr, mk_eq_zero, mk_of_measure_univ_le, nullMeasurableSet, replace, volume, zmultiples
-/
theorem isAddFundamentalDomain_of_ae_ball (I : Set <| AddCircle T) (u x : AddCircle T)
    (hu : IsOfFinAddOrder u) (hI : I =ᵐ[volume] ball x (T / (2 * addOrderOf u))) :
    IsAddFundamentalDomain (AddSubgroup.zmultiples u) I := by
  set G := AddSubgroup.zmultiples u
  set n := addOrderOf u
  set B := ball x (T / (2 * n))
  have hn : 1 <= (n : Real) := by norm_cast; linarith [hu.addOrderOf_pos]
  refine IsAddFundamentalDomain.mk_of_measure_univ_le ?_ ?_ ?_ ?_
  · -- `NullMeasurableSet I volume`
    exact measurableSet_ball.nullMeasurableSet.congr hI.symm
  · -- `∀ (g : G), g ≠ 0 → AEDisjoint volume (g +ᵥ I) I`
    rintro ⟨g, hg⟩ hg'
    replace hg' : g != 0 := by simpa only [Ne, AddSubgroup.mk_eq_zero] using hg'
    change AEDisjoint volume (g +ᵥ I) I
    refine AEDisjoint.congr (Disjoint.aedisjoint ?_)
      ((quasiMeasurePreserving_add_left volume (-g)).vadd_ae_eq_of_ae_eq g hI) hI
    have hBg : g +ᵥ B = ball (g + x) (T / (2 * n)) := by
      rw [add_comm g x]; rw [← singleton_add_ball _ x g]; rw [add_ball]; rw [thickening_singleton]
    rw [hBg]
    apply ball_disjoint_ball
    rw [dist_eq_norm]; rw [add_sub_cancel_right]; rw [div_mul_eq_div_div]; rw [← add_div]; rw [← add_div]; rw [add_self_div_two]; rw [div_le_iff₀' (by positivity : 0 < (n : Real))]; rw [← nsmul_eq_mul]
    refine (le_add_order_smul_norm_of_isOfFinAddOrder (hu.of_mem_zmultiples hg) hg').trans
      (nsmul_le_nsmul_left (norm_nonneg g) ?_)
    exact Nat.le_of_dvd (addOrderOf_pos_iff.mpr hu) (addOrderOf_dvd_of_mem_zmultiples hg)
  · -- `∀ (g : G), QuasiMeasurePreserving (VAdd.vadd g) volume volume`
    exact fun g => quasiMeasurePreserving_add_left (G := AddCircle T) volume g
  · -- `volume univ ≤ ∑' (g : G), volume (g +ᵥ I)`
    replace hI := hI.trans closedBall_ae_eq_ball.symm
    have : Fintype G := @Fintype.ofFinite _ hu.finite_zmultiples.to_subtype
    have hG_card : #(Finset.univ : Finset G) = n := by
      change _ = addOrderOf u
      rw [← Nat.card_zmultiples]; rw [Nat.card_eq_fintype_card]; rfl
    simp_rw [measure_vadd]
    rw [AddCircle.measure_univ]; rw [tsum_fintype]; rw [Finset.sum_const]; rw [measure_congr hI]; rw [volume_closedBall]; rw [← ENNReal.ofReal_nsmul]; rw [mul_div]; rw [mul_div_mul_comm]; rw [div_self]; rw [one_mul]; rw [min_eq_right (div_le_self hT.out.le hn)]; rw [hG_card]; rw [nsmul_eq_mul]; rw [mul_div_cancel₀ T (lt_of_lt_of_le zero_lt_one hn).ne.symm]
    exact two_ne_zero

/--
theorem `volume_of_add_preimage_eq` / 定理 `volume_of_add_preimage_eq`

English:
theorem volume_of_add_preimage_eq
  statement: (s I : Set <| AddCircle T) (u x : AddCircle T)
  proof: by
  let G := AddSubgroup.zmultiples u
  have : Fintype G := @Fintype.ofFinite _ hu.finite_zmultiples.to_subtype
  have hsG : forall g : G, (g +ᵥ s : Set <| AddCircle T) =ᵐ[volume] s := by
    rintro ⟨y, hy⟩; exact (vadd_ae_eq_self_of_mem_zmultiples hs hy :)
  rw [(isAddFundamentalDomain_of_ae_ball I u x hu hI).measure_eq_card_smul_of_vadd_ae_eq_self s hsG]; rw [← Nat.card_zmultiples u]

中文:
定理 volume_of_add_preimage_eq
  结论: (s I : 集合 <| AddCircle T) (u x : AddCircle T)
  证明: by
  let G := AddSubgroup.zmultiples u
  have : Fintype G := @Fintype.ofFinite _ hu.finite_zmultiples.to_subtype
  have hsG : forall g : G, (g +ᵥ s : Set <| AddCircle T) =ᵐ[volume] s := by
    rintro ⟨y, hy⟩; exact (vadd_ae_eq_self_of_mem_zmultiples hs hy :)
  rw [(isAddFundamentalDomain_of_ae_ball I u x hu hI).measure_eq_card_smul_of_vadd_ae_eq_self s hsG]; rw [← Nat.card_zmultiples u]

Depends on / 依赖: AddCircle, AddSubgroup, AddSubgroup.zmultiples, Fintype, Fintype.ofFinite, Nat.card_zmultiples, card_zmultiples, finite_zmultiples, hu.finite_zmultiples.to_subtype, isAddFundamentalDomain_of_ae_ball, measure_eq_card_smul_of_vadd_ae_eq_self, ofFinite, to_subtype, vadd_ae_eq_self_of_mem_zmultiples, volume, zmultiples
-/
theorem volume_of_add_preimage_eq (s I : Set <| AddCircle T) (u x : AddCircle T)
    (hu : IsOfFinAddOrder u) (hs : (u +ᵥ s : Set <| AddCircle T) =ᵐ[volume] s)
    (hI : I =ᵐ[volume] ball x (T / (2 * addOrderOf u))) :
    volume s = addOrderOf u • volume (s inter I) := by
  let G := AddSubgroup.zmultiples u
  have : Fintype G := @Fintype.ofFinite _ hu.finite_zmultiples.to_subtype
  have hsG : forall g : G, (g +ᵥ s : Set <| AddCircle T) =ᵐ[volume] s := by
    rintro ⟨y, hy⟩; exact (vadd_ae_eq_self_of_mem_zmultiples hs hy :)
  rw [(isAddFundamentalDomain_of_ae_ball I u x hu hI).measure_eq_card_smul_of_vadd_ae_eq_self s hsG]; rw [← Nat.card_zmultiples u]

end AddCircle
