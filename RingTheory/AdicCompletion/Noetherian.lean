/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.HopkinsLevitzki

/-!
# Hausdorff-ness for Noetherian rings
-/

public section

open IsLocalRing Module

variable {R : Type*} [CommRing R] (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M]
variable [IsNoetherianRing R] [Module.Finite R M]

/--
lemma `IsHausdorff.of_le_jacobson` / 引理 `IsHausdorff.of_le_jacobson`

English:
lemma IsHausdorff.of_le_jacobson
  given: (h : I <= Ideal.jacobson ⊥)
  statement: IsHausdorff I M
  proof: ⟨fun x hx => (Ideal.iInf_pow_smul_eq_bot_of_le_jacobson I h).le (by simpa [SModEq.zero] using hx)⟩

中文:
引理 IsHausdorff.of_le_jacobson
  条件: (h : I <= Ideal.jacobson ⊥)
  结论: IsHausdorff I M
  证明: ⟨fun x hx => (Ideal.iInf_pow_smul_eq_bot_of_le_jacobson I h).le (by simpa [SModEq.zero] using hx)⟩

Depends on / 依赖: Ideal.iInf_pow_smul_eq_bot_of_le_jacobson, SModEq, SModEq.zero, iInf_pow_smul_eq_bot_of_le_jacobson
-/
lemma IsHausdorff.of_le_jacobson (h : I <= Ideal.jacobson ⊥) : IsHausdorff I M :=
  ⟨fun x hx => (Ideal.iInf_pow_smul_eq_bot_of_le_jacobson I h).le (by simpa [SModEq.zero] using hx)⟩

/--
theorem `IsHausdorff.of_isLocalRing` / 定理 `IsHausdorff.of_isLocalRing`

English:
theorem IsHausdorff.of_isLocalRing
  given: [IsLocalRing R] (h : I != ⊤)
  statement: IsHausdorff I M
  proof: of_le_jacobson I M ((le_maximalIdeal h).trans (maximalIdeal_le_jacobson _))

中文:
定理 IsHausdorff.of_isLocalRing
  条件: [IsLocalRing R] (h : I != ⊤)
  结论: IsHausdorff I M
  证明: of_le_jacobson I M ((le_maximalIdeal h).trans (maximalIdeal_le_jacobson _))

Depends on / 依赖: le_maximalIdeal, maximalIdeal_le_jacobson, of_le_jacobson
-/
theorem IsHausdorff.of_isLocalRing [IsLocalRing R] (h : I != ⊤) : IsHausdorff I M :=
  of_le_jacobson I M ((le_maximalIdeal h).trans (maximalIdeal_le_jacobson _))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsLocalRing
  signature: R] : IsHausdorff (maximalIdeal R) M
  body: .of_le_jacobson _ _ (maximalIdeal_le_jacobson _)

中文:
实例 [IsLocalRing
  签名: R] : IsHausdorff (maximalIdeal R) M
  定义体: .of_le_jacobson _ _ (maximalIdeal_le_jacobson _)

Depends on / 依赖: maximalIdeal_le_jacobson, of_le_jacobson
-/
instance [IsLocalRing R] : IsHausdorff (maximalIdeal R) M :=
  .of_le_jacobson _ _ (maximalIdeal_le_jacobson _)

/--
lemma `IsHausdorff.of_isTorsionFree` / 引理 `IsHausdorff.of_isTorsionFree`

English:
lemma IsHausdorff.of_isTorsionFree
  given: [IsDomain R] [IsTorsionFree R M] (h : I != ⊤)
  statement: IsHausdorff I M
  proof: ⟨fun x hx => (I.iInf_pow_smul_eq_bot_of_isTorsionFree h).le (by simpa [SModEq.zero] using hx)⟩

中文:
引理 IsHausdorff.of_isTorsionFree
  条件: [IsDomain R] [IsTorsionFree R M] (h : I != ⊤)
  结论: IsHausdorff I M
  证明: ⟨fun x hx => (I.iInf_pow_smul_eq_bot_of_isTorsionFree h).le (by simpa [SModEq.zero] using hx)⟩

Depends on / 依赖: I.iInf_pow_smul_eq_bot_of_isTorsionFree, SModEq, SModEq.zero, iInf_pow_smul_eq_bot_of_isTorsionFree
-/
lemma IsHausdorff.of_isTorsionFree [IsDomain R] [IsTorsionFree R M] (h : I != ⊤) : IsHausdorff I M :=
  ⟨fun x hx => (I.iInf_pow_smul_eq_bot_of_isTorsionFree h).le (by simpa [SModEq.zero] using hx)⟩

/--
theorem `IsHausdorff.of_isDomain` / 定理 `IsHausdorff.of_isDomain`

English:
theorem IsHausdorff.of_isDomain
  given: [IsDomain R] (h : I != ⊤)
  statement: IsHausdorff I R
  proof: .of_isTorsionFree I R h

中文:
定理 IsHausdorff.of_isDomain
  条件: [IsDomain R] (h : I != ⊤)
  结论: IsHausdorff I R
  证明: .of_isTorsionFree I R h

Depends on / 依赖: of_isTorsionFree
-/
theorem IsHausdorff.of_isDomain [IsDomain R] (h : I != ⊤) : IsHausdorff I R :=
  .of_isTorsionFree I R h

instance (priority := 100) {A : Type*} [CommRing A] [IsArtinianRing A] [IsLocalRing A] :
    IsAdicComplete (IsLocalRing.maximalIdeal A) A where
  prec' f hf := by
    obtain ⟨n, hn⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal A).mp ‹_›
    use f n; intro m
    by_cases h : m <= n
    · exact hf h
    specialize hf (show n <= m by lia)
    rw [hn]; rw [zero_smul]; rw [Ideal.zero_eq_bot]; rw [SModEq.bot] at hf
    rw [hf]
