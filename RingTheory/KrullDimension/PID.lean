/-
Copyright (c) 2025 Jingting Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang
-/
module

public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# The Krull dimension of a principal ideal domain

In this file, we proved some results about the dimension of a principal ideal domain.
-/

public section

/--
Instance `IsPrincipalIdealRing.krullDimLE_one` / 实例 `IsPrincipalIdealRing.krullDimLE_one`

English:
instance IsPrincipalIdealRing.krullDimLE_one
  signature: (R : Type*) [CommRing R]
  body: by
  refine Ring.krullDimLE_one_iff.2 fun I hI => or_iff_not_imp_left.2 fun hI' => ?_
  rw [minimalPrimes_eq_minimals]; rw [Set.notMem_ofPred_iff]; rw [not_minimal_iff_exists_lt hI] at hI'
  obtain ⟨P, hlt, hP⟩ := hI'
  have := IsPrincipalIdealRing.of_surjective (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  have : (I.map (Ideal.Quotient.mk P)).IsMaximal := by
    have := Ideal.map_isPrime_of_surjective (f := Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
      (I := I) (by simpa using hlt.le)
    refine IsPrime.to_maximal_ideal ?_
    rw [ne_eq]; rw [Ideal.map_eq_bot_iff_le_ker]; rw [Ideal.mk_ker]
    exact hlt.not_ge
  have := Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
    (K := I.map (Ideal.Quotient.mk P))
  simpa [Ideal.comap_map_of_surjective' (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective,
    hlt.le] using this

中文:
实例 是主理想环.krullDimLE_one
  签名: (R : 类型) [交换环 R]
  定义体: by
  refine Ring.krullDimLE_one_iff.2 fun I hI => or_iff_not_imp_left.2 fun hI' => ?_
  rw [minimalPrimes_eq_minimals]; rw [Set.notMem_ofPred_iff]; rw [not_minimal_iff_exists_lt hI] at hI'
  obtain ⟨P, hlt, hP⟩ := hI'
  have := IsPrincipalIdealRing.of_surjective (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  have : (I.map (Ideal.Quotient.mk P)).IsMaximal := by
    have := Ideal.map_isPrime_of_surjective (f := Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
      (I := I) (by simpa using hlt.le)
    refine IsPrime.to_maximal_ideal ?_
    rw [ne_eq]; rw [Ideal.map_eq_bot_iff_le_ker]; rw [Ideal.mk_ker]
    exact hlt.not_ge
  have := Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
    (K := I.map (Ideal.Quotient.mk P))
  simpa [Ideal.comap_map_of_surjective' (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective,
    hlt.le] using this

Depends on / 依赖: I.map, Ideal.Quotient.mk, Ideal.Quotient.mk_surjective, Ideal.map_isPrime_of_surjective, IsMaximal, IsPrincipalIdealRing, IsPrincipalIdealRing.of_surjective, QuasiSeparatedSpace, Quotient, Ring.krullDimLE_one_iff, Set.notMem_ofPred_iff, T2Space, T2Space.to_quasiSeparatedSpace, hlt.le, krullDimLE_one_iff, map_isPrime_of_surjective, minimalPrimes_eq_minimals, mk_surjective, notMem_ofPred_iff, not_minimal_iff_exists_lt
-/
instance IsPrincipalIdealRing.krullDimLE_one (R : Type*) [CommRing R]
    [IsPrincipalIdealRing R] : Ring.KrullDimLE 1 R := by
  refine Ring.krullDimLE_one_iff.2 fun I hI => or_iff_not_imp_left.2 fun hI' => ?_
  rw [minimalPrimes_eq_minimals]; rw [Set.notMem_ofPred_iff]; rw [not_minimal_iff_exists_lt hI] at hI'
  obtain ⟨P, hlt, hP⟩ := hI'
  have := IsPrincipalIdealRing.of_surjective (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  have : (I.map (Ideal.Quotient.mk P)).IsMaximal := by
    have := Ideal.map_isPrime_of_surjective (f := Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
      (I := I) (by simpa using hlt.le)
    refine IsPrime.to_maximal_ideal ?_
    rw [ne_eq]; rw [Ideal.map_eq_bot_iff_le_ker]; rw [Ideal.mk_ker]
    exact hlt.not_ge
  have := Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
    (K := I.map (Ideal.Quotient.mk P))
  simpa [Ideal.comap_map_of_surjective' (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective,
    hlt.le] using this

/--
theorem `IsPrincipalIdealRing.ringKrullDim_eq_one` / 定理 `IsPrincipalIdealRing.ringKrullDim_eq_one`

English:
theorem IsPrincipalIdealRing.ringKrullDim_eq_one
  statement: (R : Type*) [CommRing R] [IsDomain R]
  proof: by
  apply eq_of_le_of_not_lt ?_ fun h' => h ?_
  · rw [← Nat.cast_one, ← Ring.krullDimLE_iff]
    infer_instance
  · have h'' : ringKrullDim R <= 0 := Order.le_of_lt_succ h'
    rw [← Nat.cast_zero]; rw [← Ring.krullDimLE_iff] at h''
    exact Ring.KrullDimLE.isField_of_isDomain

中文:
定理 是主理想环.ringKrullDim_eq_one
  结论: (R : 类型) [交换环 R] [是整环 R]
  证明: by
  apply eq_of_le_of_not_lt ?_ fun h' => h ?_
  · rw [← Nat.cast_one, ← Ring.krullDimLE_iff]
    infer_instance
  · have h'' : ringKrullDim R <= 0 := Order.le_of_lt_succ h'
    rw [← Nat.cast_zero]; rw [← Ring.krullDimLE_iff] at h''
    exact Ring.KrullDimLE.isField_of_isDomain

Depends on / 依赖: KrullDimLE, Nat.cast_one, Nat.cast_zero, NoetherianSpace, NoetherianSpace.to_quasiSeparatedSpace, Order.le_of_lt_succ, Ring.KrullDimLE.isField_of_isDomain, Ring.krullDimLE_iff, cast_one, cast_zero, eq_of_le_of_not_lt, infer_instance, isField_of_isDomain, krullDimLE_iff, le_of_lt_succ, ringKrullDim, to_quasiSeparatedSpace
-/
theorem IsPrincipalIdealRing.ringKrullDim_eq_one (R : Type*) [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] (h : ¬ IsField R) : ringKrullDim R = 1 := by
  apply eq_of_le_of_not_lt ?_ fun h' => h ?_
  · rw [← Nat.cast_one, ← Ring.krullDimLE_iff]
    infer_instance
  · have h'' : ringKrullDim R <= 0 := Order.le_of_lt_succ h'
    rw [← Nat.cast_zero]; rw [← Ring.krullDimLE_iff] at h''
    exact Ring.KrullDimLE.isField_of_isDomain

/--
lemma `IsPrincipalIdealRing.height_eq_one_of_isMaximal` / 引理 `IsPrincipalIdealRing.height_eq_one_of_isMaximal`

English:
lemma IsPrincipalIdealRing.height_eq_one_of_isMaximal
  statement: {R : Type*} [CommRing R] [IsDomain R]
  proof: by
  refine le_antisymm ?_ ?_
  · suffices h : (m.height : WithBot Nat∞) <= 1 by norm_cast at h
    rw [← IsPrincipalIdealRing.ringKrullDim_eq_one _ h]
    exact Ideal.height_le_ringKrullDim_of_ne_top Ideal.IsPrime.ne_top'
  · apply le_of_eq_of_le _ (Ideal.height_add_one_le_of_lt_of_isPrime (Ideal.bot_lt_of_maximal m h))
    simp

中文:
引理 是主理想环.height_eq_one_of_isMaximal
  结论: {R : 类型} [交换环 R] [是整环 R]
  证明: by
  refine le_antisymm ?_ ?_
  · suffices h : (m.height : WithBot Nat∞) <= 1 by norm_cast at h
    rw [← IsPrincipalIdealRing.ringKrullDim_eq_one _ h]
    exact Ideal.height_le_ringKrullDim_of_ne_top Ideal.IsPrime.ne_top'
  · apply le_of_eq_of_le _ (Ideal.height_add_one_le_of_lt_of_isPrime (Ideal.bot_lt_of_maximal m h))
    simp

Depends on / 依赖: Ideal.IsPrime.ne_top, Ideal.bot_lt_of_maximal, Ideal.height_add_one_le_of_lt_of_isPrime, Ideal.height_le_ringKrullDim_of_ne_top, IsPrime, IsPrincipalIdealRing, IsPrincipalIdealRing.ringKrullDim_eq_one, WithBot, bot_lt_of_maximal, height, height_add_one_le_of_lt_of_isPrime, height_le_ringKrullDim_of_ne_top, le_antisymm, le_of_eq_of_le, m.height, ne_top, ringKrullDim_eq_one
-/
lemma IsPrincipalIdealRing.height_eq_one_of_isMaximal {R : Type*} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] (m : Ideal R) [m.IsMaximal] (h : ¬ IsField R) :
    m.height = 1 := by
  refine le_antisymm ?_ ?_
  · suffices h : (m.height : WithBot Nat∞) <= 1 by norm_cast at h
    rw [← IsPrincipalIdealRing.ringKrullDim_eq_one _ h]
    exact Ideal.height_le_ringKrullDim_of_ne_top Ideal.IsPrime.ne_top'
  · apply le_of_eq_of_le _ (Ideal.height_add_one_le_of_lt_of_isPrime (Ideal.bot_lt_of_maximal m h))
    simp
