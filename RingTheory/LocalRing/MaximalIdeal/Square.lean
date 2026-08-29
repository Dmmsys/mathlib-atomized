/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Nakayama

/-!

# Lemmas about square of maximal ideal of local ring

-/

public section

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

variable (R) in
/--
lemma `IsLocalRing.maximalIdeal_sq_lt_maximalIdeal` / 引理 `IsLocalRing.maximalIdeal_sq_lt_maximalIdeal`

English:
lemma IsLocalRing.maximalIdeal_sq_lt_maximalIdeal
  proof: by
  trans ¬ maximalIdeal R ^ 2 = maximalIdeal R
  · simp [lt_iff_le_and_ne, Ideal.pow_le_self]
  · rw [IsLocalRing.isField_iff_maximalIdeal_eq, pow_two]
    refine Iff.not ⟨fun h => ?_, fun h => by simp [h]⟩
    exact Submodule.eq_bot_of_eq_ideal_smul_of_le_jacobson_annihilator (IsNoetherian.noethe

中文:
引理 IsLocalRing.maximalIdeal_sq_lt_maximalIdeal
  证明: by
  trans ¬ maximalIdeal R ^ 2 = maximalIdeal R
  · simp [lt_iff_le_and_ne, Ideal.pow_le_self]
  · rw [IsLocalRing.isField_iff_maximalIdeal_eq, pow_two]
    refine Iff.not ⟨fun h => ?_, fun h => by simp [h]⟩
    exact Submodule.eq_bot_of_eq_ideal_smul_of_le_jacobson_annihilator (IsNoetherian.noethe

Depends on / 依赖: Ideal.pow_le_self, Iff.not, IsLocalRing, IsLocalRing.isField_iff_maximalIdeal_eq, IsNoetherian, IsNoetherian.noetherian, Submodule, Submodule.eq_bot_of_eq_ideal_smul_of_le_jacobson_annihilator, eq_bot_of_eq_ideal_smul_of_le_jacobson_annihilator, h.symm, isField_iff_maximalIdeal_eq, lt_iff_le_and_ne, maximalIdeal, maximalIdeal_le_jacobson, noetherian, pow_le_self, pow_two
-/
lemma IsLocalRing.maximalIdeal_sq_lt_maximalIdeal :
    maximalIdeal R ^ 2 < maximalIdeal R ↔ ¬ IsField R := by
  trans ¬ maximalIdeal R ^ 2 = maximalIdeal R
  · simp [lt_iff_le_and_ne, Ideal.pow_le_self]
  · rw [IsLocalRing.isField_iff_maximalIdeal_eq, pow_two]
    refine Iff.not ⟨fun h => ?_, fun h => by simp [h]⟩
    exact Submodule.eq_bot_of_eq_ideal_smul_of_le_jacobson_annihilator (IsNoetherian.noetherian _)
      h.symm (maximalIdeal_le_jacobson _)

/--
lemma `IsLocalRing.maximalIdeal_sq_lt_of_ringKrullDim_ne_zero` / 引理 `IsLocalRing.maximalIdeal_sq_lt_of_ringKrullDim_ne_zero`

English:
lemma IsLocalRing.maximalIdeal_sq_lt_of_ringKrullDim_ne_zero
  given: (h : ringKrullDim R != 0)
  proof: (maximalIdeal_sq_lt_maximalIdeal R).mpr (ringKrullDim_eq_zero_of_isField.mt h)

@[deprecated "Use `IsLocalRing.maximalIdeal_sq_lt_of_ringKrullDim_ne_zero` instead"
  (since := "2026-05-13")]

中文:
引理 IsLocalRing.maximalIdeal_sq_lt_of_ringKrullDim_ne_zero
  条件: (h : ringKrullDim R != 0)
  证明: (maximalIdeal_sq_lt_maximalIdeal R).mpr (ringKrullDim_eq_zero_of_isField.mt h)

@[deprecated "Use `IsLocalRing.maximalIdeal_sq_lt_of_ringKrullDim_ne_zero` instead"
  (since := "2026-05-13")]

Depends on / 依赖: maximalIdeal_sq_lt_maximalIdeal, ringKrullDim_eq_zero_of_isField, ringKrullDim_eq_zero_of_isField.mt
-/
lemma IsLocalRing.maximalIdeal_sq_lt_of_ringKrullDim_ne_zero (h : ringKrullDim R != 0) :
    (maximalIdeal R) ^ 2 < maximalIdeal R :=
  (maximalIdeal_sq_lt_maximalIdeal R).mpr (ringKrullDim_eq_zero_of_isField.mt h)

@[deprecated "Use `IsLocalRing.maximalIdeal_sq_lt_of_ringKrullDim_ne_zero` instead"
  (since := "2026-05-13")]
/--
lemma `IsLocalRing.maximalIdeal_sq_lt` / 引理 `IsLocalRing.maximalIdeal_sq_lt`

English:
lemma IsLocalRing.maximalIdeal_sq_lt
  given: (h : 0 < ringKrullDim R)
  proof: IsLocalRing.maximalIdeal_sq_lt_of_ringKrullDim_ne_zero h.ne.symm

中文:
引理 IsLocalRing.maximalIdeal_sq_lt
  条件: (h : 0 < ringKrullDim R)
  证明: IsLocalRing.maximalIdeal_sq_lt_of_ringKrullDim_ne_zero h.ne.symm

Depends on / 依赖: IsLocalRing, IsLocalRing.maximalIdeal_sq_lt_of_ringKrullDim_ne_zero, h.ne.symm, maximalIdeal_sq_lt_of_ringKrullDim_ne_zero
-/
lemma IsLocalRing.maximalIdeal_sq_lt (h : 0 < ringKrullDim R) :
    (maximalIdeal R) ^ 2 < maximalIdeal R :=
  IsLocalRing.maximalIdeal_sq_lt_of_ringKrullDim_ne_zero h.ne.symm
