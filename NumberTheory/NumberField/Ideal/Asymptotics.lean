/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.NormLeOne
public import Mathlib.NumberTheory.NumberField.ClassNumber

/-!
# Asymptotics on integral ideals of a number field

We prove several asymptotics involving integral ideals of a number field.

## Main results

* `NumberField.ideal.tendsto_norm_le_and_mk_eq_div_atTop`: asymptotics for the number of (nonzero)
  integral ideals of bounded norm in a fixed class of the class group.
* `NumberField.ideal.tendsto_norm_le_div_atTop`: asymptotics for the number of integral ideals
  of bounded norm.

-/

@[expose] public section

noncomputable section

open Ideal

variable (K : Type*) [Field K] [NumberField K]

namespace NumberField.Ideal

open scoped nonZeroDivisors Real

open Filter InfinitePlace mixedEmbedding euclidean fundamentalCone Submodule Topology
open NumberField.Units

variable {C : ClassGroup (𝓞 K)} {J : (Ideal (𝓞 K))⁰} {s : Real}

/--
theorem `tendsto_norm_le_and_mk_eq_div_atTop_aux₁` / 定理 `tendsto_norm_le_and_mk_eq_div_atTop_aux₁`

English:
theorem tendsto_norm_le_and_mk_eq_div_atTop_aux₁
  given: (hJ : ClassGroup.mk0 J = C⁻¹)
  proof: by
  simp_rw [← nonZeroDivisors_dvd_iff_dvd_coe]
  refine Nat.card_congr ?_
  refine ((Equiv.dvd J).subtypeEquiv fun I => ?_).trans
    (Equiv.subtypeSubtypeEquivSubtypeInter (fun I : (Ideal (𝓞 K))⁰ => J ∣ I) _)
  rw [← ClassGroup.mk0_eq_one_iff (SetLike.coe_mem _)]
  simp_rw [Equiv.dvd_apply, Submo

中文:
定理 tendsto_norm_le_and_mk_eq_div_atTop_aux₁
  条件: (hJ : ClassGroup.mk0 J = C⁻¹)
  证明: by
  simp_rw [← nonZeroDivisors_dvd_iff_dvd_coe]
  refine Nat.card_congr ?_
  refine ((Equiv.dvd J).subtypeEquiv fun I => ?_).trans
    (Equiv.subtypeSubtypeEquivSubtypeInter (fun I : (Ideal (𝓞 K))⁰ => J ∣ I) _)
  rw [← ClassGroup.mk0_eq_one_iff (SetLike.coe_mem _)]
  simp_rw [Equiv.dvd_apply, Submo
-/
private theorem tendsto_norm_le_and_mk_eq_div_atTop_aux₁ (hJ : ClassGroup.mk0 J = C⁻¹) :
    Nat.card {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) <= s ∧ ClassGroup.mk0 I = C}
      = Nat.card {I : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ I ∧ IsPrincipal (I : Ideal (𝓞 K)) ∧
        absNorm (I : Ideal (𝓞 K)) <= s * absNorm (J : Ideal (𝓞 K))} := by
  simp_rw [← nonZeroDivisors_dvd_iff_dvd_coe]
  refine Nat.card_congr ?_
  refine ((Equiv.dvd J).subtypeEquiv fun I => ?_).trans
    (Equiv.subtypeSubtypeEquivSubtypeInter (fun I : (Ideal (𝓞 K))⁰ => J ∣ I) _)
  rw [← ClassGroup.mk0_eq_one_iff (SetLike.coe_mem _)]
  simp_rw [Equiv.dvd_apply, Submonoid.coe_mul, ← Submonoid.mul_def, _root_.map_mul, hJ,
    inv_mul_eq_one, Nat.cast_mul, mul_comm s, eq_comm, and_comm, and_congr_left_iff]
  exact fun _ =>
    (mul_le_mul_iff_of_pos_left (Nat.cast_pos.mpr (absNorm_pos_of_nonZeroDivisors J))).symm

open scoped Classical in
/--
Definition of `tendsto_norm_le_and_mk_eq_div_atTop_aux₂` / `tendsto_norm_le_and_mk_eq_div_atTop_aux₂` 的定义

English:
definition tendsto_norm_le_and_mk_eq_div_atTop_aux₂
  signature: :
  body: by
  rw [ZLattice.coe_comap]
  refine (((toMixed K).toEquiv.image _).trans (Equiv.subtypeEquivProp ?_)).trans
    (Equiv.subtypeSubtypeEquivSubtypeInter _ (mixedEmbedding.norm · <= s)).symm
  ext
  simp_rw [mem_idealSet, Set.mem_image, Set.mem_inter_iff, Set.mem_preimage, SetLike.mem_coe,
    mem_id

中文:
定义 tendsto_norm_le_and_mk_eq_div_atTop_aux₂
  签名: :
  定义体: by
  rw [ZLattice.coe_comap]
  refine (((toMixed K).toEquiv.image _).trans (Equiv.subtypeEquivProp ?_)).trans
    (Equiv.subtypeSubtypeEquivSubtypeInter _ (mixedEmbedding.norm · <= s)).symm
  ext
  simp_rw [mem_idealSet, Set.mem_image, Set.mem_inter_iff, Set.mem_preimage, SetLike.mem_coe,
    mem_id
-/
private def tendsto_norm_le_and_mk_eq_div_atTop_aux₂ :
    ↑({x | x in (toMixed K) ⁻¹' fundamentalCone K ∧ mixedEmbedding.norm ((toMixed K) x) <= s} inter
      (ZLattice.comap Real (idealLattice K ((FractionalIdeal.mk0 K) J)) (toMixed K).toLinearMap))
        ≃ {a : idealSet K J // mixedEmbedding.norm (a : mixedSpace K) <= s} := by
  rw [ZLattice.coe_comap]
  refine (((toMixed K).toEquiv.image _).trans (Equiv.subtypeEquivProp ?_)).trans
    (Equiv.subtypeSubtypeEquivSubtypeInter _ (mixedEmbedding.norm · <= s)).symm
  ext
  simp_rw [mem_idealSet, Set.mem_image, Set.mem_inter_iff, Set.mem_preimage, SetLike.mem_coe,
    mem_idealLattice, FractionalIdeal.coe_mk0]
  constructor
  · rintro ⟨_, ⟨⟨hx₁, hx₂⟩, _, ⟨x, hx₃, rfl⟩, h⟩, rfl⟩
    exact ⟨⟨hx₁, x, hx₃, h⟩, hx₂⟩
  · rintro ⟨⟨hx₁, ⟨x, hx₂, rfl⟩⟩, hx₃⟩
    exact ⟨(toMixed K).symm (mixedEmbedding K x), ⟨⟨hx₁, hx₃⟩, ⟨(x : K), by simp [hx₂], rfl⟩⟩, rfl⟩

variable (C) in
/--
theorem `tendsto_norm_le_and_mk_eq_div_atTop` / 定理 `tendsto_norm_le_and_mk_eq_div_atTop`

English:
theorem tendsto_norm_le_and_mk_eq_div_atTop
  proof: by
  classical
  have h₁ : forall s : Real,
    {x | x in toMixed K ⁻¹' fundamentalCone K ∧ mixedEmbedding.norm (toMixed K x) <= s} =
      toMixed K ⁻¹' {x | x in fundamentalCone K ∧ mixedEmbedding.norm x <= s} := fun _ => rfl
  have h₂ : {x | x in fundamentalCone K ∧ mixedEmbedding.norm x <= 1} = 

中文:
定理 tendsto_norm_le_and_mk_eq_div_atTop
  证明: by
  classical
  have h₁ : forall s : Real,
    {x | x in toMixed K ⁻¹' fundamentalCone K ∧ mixedEmbedding.norm (toMixed K x) <= s} =
      toMixed K ⁻¹' {x | x in fundamentalCone K ∧ mixedEmbedding.norm x <= s} := fun _ => rfl
  have h₂ : {x | x in fundamentalCone K ∧ mixedEmbedding.norm x <= 1} = 

Depends on / 依赖: ClassGroup, ClassGroup.mk0_surjective, Nat.cast_ne_zero.mpr, ZLattice, ZLattice.covolume.tendsto_ca, absNorm, absNorm_ne_zero_of_nonZeroDivisors, cast_ne_zero, classical, convert, covolume, fundamentalCone, mixedEmbedding, mixedEmbedding.norm, mk0_surjective, normLeOne, tendsto_ca, toMixed
-/
theorem tendsto_norm_le_and_mk_eq_div_atTop :
    Tendsto (fun s : Real =>
      (Nat.card {I : (Ideal (𝓞 K))⁰ //
        absNorm (I : Ideal (𝓞 K)) <= s ∧ ClassGroup.mk0 I = C} : Real) / s) atTop
          (𝓝 ((2 ^ nrRealPlaces K * (2 * π) ^ nrComplexPlaces K * regulator K) /
            (torsionOrder K * Real.sqrt |discr K|))) := by
  classical
  have h₁ : forall s : Real,
    {x | x in toMixed K ⁻¹' fundamentalCone K ∧ mixedEmbedding.norm (toMixed K x) <= s} =
      toMixed K ⁻¹' {x | x in fundamentalCone K ∧ mixedEmbedding.norm x <= s} := fun _ => rfl
  have h₂ : {x | x in fundamentalCone K ∧ mixedEmbedding.norm x <= 1} = normLeOne K := by ext; simp
  obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective C⁻¹
  have h₃ : (absNorm J.1 : Real) != 0 := (Nat.cast_ne_zero.mpr (absNorm_ne_zero_of_nonZeroDivisors J))
  convert!
    ((ZLattice.covolume.tendsto_card_le_div'
              (ZLattice.comap Real (mixedEmbedding.idealLattice K (FractionalIdeal.mk0 K J))
                (toMixed K).toLinearMap)
              (F := fun x => mixedEmbedding.norm (toMixed K x)) (X :=
              (toMixed K) ⁻¹' (fundamentalCone K)) (fun _ _ _ h => ?_) (fun _ _ h => ?_)
              ((toMixed K).antilipschitz.isBounded_preimage (isBounded_normLeOne K)) ?_ ?_).mul
          (tendsto_const_nhds (x := (absNorm (J : Ideal (𝓞 K)) : Real) * (torsionOrder K : Real)⁻¹))).comp
      (tendsto_id.atTop_mul_const' <| Nat.cast_pos.mpr (absNorm_pos_of_nonZeroDivisors J)) using
    2 with s
  · simp_rw [Ideal.tendsto_norm_le_and_mk_eq_div_atTop_aux₁ K hJ, id_eq,
      Nat.card_congr (Ideal.tendsto_norm_le_and_mk_eq_div_atTop_aux₂ K),
      ← card_isPrincipal_dvd_norm_le, Function.comp_def, Nat.cast_mul, div_eq_mul_inv, mul_inv,
      ← mul_assoc, mul_comm _ (torsionOrder K : Real)⁻¹, mul_comm _ (torsionOrder K : Real), mul_assoc]
    rw [inv_mul_cancel_left₀ (Nat.cast_ne_zero.mpr (torsionOrder_ne_zero K))]; rw [inv_mul_cancel₀ h₃]; rw [mul_one]
  · rw [h₁, h₂, MeasureTheory.measureReal_def, (volumePreserving_toMixed K).measure_preimage
      (measurableSet_normLeOne K).nullMeasurableSet, volume_normLeOne, ZLattice.covolume_comap
      _ _ _ (volumePreserving_toMixed K), covolume_idealLattice, ENNReal.toReal_mul,
      ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_pow, ENNReal.toReal_ofNat,
      ENNReal.coe_toReal, NNReal.coe_real_pi, ENNReal.toReal_ofReal (regulator_pos K).le,
      FractionalIdeal.coe_mk0, FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast, div_eq_mul_inv,
      div_eq_mul_inv, mul_inv, mul_inv, mul_inv, inv_pow, inv_inv]
    ring_nf
    rw [mul_inv_cancel_right₀ h₃]
  · rwa [Set.mem_preimage, map_smul, smul_mem_iff_mem h.ne']
  · rw [map_smul, mixedEmbedding.norm_smul, euclidean.finrank, abs_of_nonneg h]
  · exact (toMixed K).continuous.measurable (measurableSet_normLeOne K)
  · rw [h₁, ← (toMixed K).coe_toHomeomorph, ← Homeomorph.preimage_frontier,
      (toMixed K).coe_toHomeomorph, (volumePreserving_toMixed K).measure_preimage
      measurableSet_frontier.nullMeasurableSet, h₂, volume_frontier_normLeOne]

/--
theorem `tendsto_norm_le_div_atTop₀` / 定理 `tendsto_norm_le_div_atTop₀`

English:
theorem tendsto_norm_le_div_atTop₀
  proof: by
  classical
  convert!
    Filter.Tendsto.congr' ?_
      (tendsto_finsetSum Finset.univ (fun C _ => tendsto_norm_le_and_mk_eq_div_atTop K C))
  · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, classNumber]
    ring
  · filter_upwards [eventually_ge_atTop 0] with s hs
    have : Fintype {I

中文:
定理 tendsto_norm_le_div_atTop₀
  证明: by
  classical
  convert!
    Filter.Tendsto.congr' ?_
      (tendsto_finsetSum Finset.univ (fun C _ => tendsto_norm_le_and_mk_eq_div_atTop K C))
  · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, classNumber]
    ring
  · filter_upwards [eventually_ge_atTop 0] with s hs
    have : Fintype {I

Depends on / 依赖: ClassGroup, Equiv.subtypeSubtypeEquivSubtypeInt, Filter, Filter.Tendsto.congr, Finset, Finset.card_univ, Finset.sum_const, Finset.univ, Fintype, Fintype.ofFinite, Nat.le_floor_iff, Tendsto, absNorm, card_univ, classNumber, classical, convert, eventually_ge_atTop, filter_upwards, le_floor_iff
-/
theorem tendsto_norm_le_div_atTop₀ :
    Tendsto (fun s : Real =>
      (Nat.card {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) <= s} : Real) / s) atTop
          (𝓝 ((2 ^ nrRealPlaces K * (2 * π) ^ nrComplexPlaces K * regulator K * classNumber K) /
            (torsionOrder K * Real.sqrt |discr K|))) := by
  classical
  convert!
    Filter.Tendsto.congr' ?_
      (tendsto_finsetSum Finset.univ (fun C _ => tendsto_norm_le_and_mk_eq_div_atTop K C))
  · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, classNumber]
    ring
  · filter_upwards [eventually_ge_atTop 0] with s hs
    have : Fintype {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) <= s} := by
      simp_rw [← Nat.le_floor_iff hs]
      refine @Fintype.ofFinite _ (finite_setOfPred_absNorm_le₀ ⌊s⌋₊)
    let e := fun C : ClassGroup (𝓞 K) => Equiv.subtypeSubtypeEquivSubtypeInter
      (fun I : (Ideal (𝓞 K))⁰ => absNorm I.1 <= s) (fun I => ClassGroup.mk0 I = C)
    simp_rw [← Nat.card_congr (e _), Nat.card_eq_fintype_card, Fintype.subtype_card]
    rw [Fintype.card]; rw [Finset.card_eq_sum_card_fiberwise (f := fun I => ClassGroup.mk0 I.1)
      (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]; rw [Nat.cast_sum]; rw [Finset.sum_div]

/--
theorem `tendsto_norm_le_div_atTop` / 定理 `tendsto_norm_le_div_atTop`

English:
theorem tendsto_norm_le_div_atTop
  proof: by
  have := (tendsto_norm_le_div_atTop₀ K).add tendsto_inv_atTop_zero
  rw [add_zero] at this
  apply this.congr'
  filter_upwards [eventually_ge_atTop 0] with s hs
  simp_rw [← Nat.le_floor_iff hs]
  rw [Ideal.card_norm_le_eq_card_norm_le_add_one]; rw [Nat.cast_add]; rw [Nat.cast_one]; rw [add_div

中文:
定理 tendsto_norm_le_div_atTop
  证明: by
  have := (tendsto_norm_le_div_atTop₀ K).add tendsto_inv_atTop_zero
  rw [add_zero] at this
  apply this.congr'
  filter_upwards [eventually_ge_atTop 0] with s hs
  simp_rw [← Nat.le_floor_iff hs]
  rw [Ideal.card_norm_le_eq_card_norm_le_add_one]; rw [Nat.cast_add]; rw [Nat.cast_one]; rw [add_div

Depends on / 依赖: Ideal.card_norm_le_eq_card_norm_le_add_one, Nat.cast_add, Nat.cast_one, Nat.le_floor_iff, add_div, add_zero, card_norm_le_eq_card_norm_le_add_one, cast_add, cast_one, eventually_ge_atTop, filter_upwards, le_floor_iff, one_div, simp_rw, tendsto_inv_atTop_zero, this.congr
-/
theorem tendsto_norm_le_div_atTop :
    Tendsto (fun s : Real => (Nat.card {I : Ideal (𝓞 K) // absNorm I <= s} : Real) / s) atTop
      (𝓝 ((2 ^ nrRealPlaces K * (2 * π) ^ nrComplexPlaces K * regulator K * classNumber K) /
        (torsionOrder K * Real.sqrt |discr K|))) := by
  have := (tendsto_norm_le_div_atTop₀ K).add tendsto_inv_atTop_zero
  rw [add_zero] at this
  apply this.congr'
  filter_upwards [eventually_ge_atTop 0] with s hs
  simp_rw [← Nat.le_floor_iff hs]
  rw [Ideal.card_norm_le_eq_card_norm_le_add_one]; rw [Nat.cast_add]; rw [Nat.cast_one]; rw [add_div]; rw [one_div]

end NumberField.Ideal
