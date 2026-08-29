/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.LocalProperties.Basic
public import Mathlib.RingTheory.Localization.Integral

/-!

# The meta properties of integral ring homomorphisms.

-/

public section


namespace RingHom

open scoped TensorProduct

open TensorProduct Algebra.TensorProduct

/--
theorem `isIntegral_stableUnderComposition` / 定理 `isIntegral_stableUnderComposition`

English:
theorem isIntegral_stableUnderComposition
  statement: StableUnderComposition fun f => f.IsIntegral
  proof: by
  introv R hf hg; exact hf.trans _ _ hg

中文:
定理 is整数egral_stableUnderComposition
  结论: StableUnderComposition fun f => f.是整
  证明: by
  introv R hf hg; exact hf.trans _ _ hg

Depends on / 依赖: hf.trans, introv
-/
theorem isIntegral_stableUnderComposition : StableUnderComposition fun f => f.IsIntegral := by
  introv R hf hg; exact hf.trans _ _ hg

/--
theorem `isIntegral_respectsIso` / 定理 `isIntegral_respectsIso`

English:
theorem isIntegral_respectsIso
  statement: RespectsIso fun f => f.IsIntegral
  proof: by
  apply isIntegral_stableUnderComposition.respectsIso
  introv x
  rw [← e.apply_symm_apply x]
  apply RingHom.isIntegralElem_map

中文:
定理 is整数egral_respectsIso
  结论: RespectsIso fun f => f.是整
  证明: by
  apply isIntegral_stableUnderComposition.respectsIso
  introv x
  rw [← e.apply_symm_apply x]
  apply RingHom.isIntegralElem_map

Depends on / 依赖: RingHom, RingHom.isIntegralElem_map, apply_symm_apply, e.apply_symm_apply, introv, isIntegralElem_map, isIntegral_stableUnderComposition, isIntegral_stableUnderComposition.respectsIso, respectsIso
-/
theorem isIntegral_respectsIso : RespectsIso fun f => f.IsIntegral := by
  apply isIntegral_stableUnderComposition.respectsIso
  introv x
  rw [← e.apply_symm_apply x]
  apply RingHom.isIntegralElem_map

/--
theorem `isIntegral_isStableUnderBaseChange` / 定理 `isIntegral_isStableUnderBaseChange`

English:
theorem isIntegral_isStableUnderBaseChange
  statement: IsStableUnderBaseChange fun f => f.IsIntegral
  proof: by
  refine IsStableUnderBaseChange.mk isIntegral_respectsIso ?_
  introv int
  rw [algebraMap_isIntegral_iff] at int ⊢
  infer_instance

中文:
定理 is整数egral_isStableUnderBaseChange
  结论: 是StableUnderBaseChange fun f => f.是整
  证明: by
  refine IsStableUnderBaseChange.mk isIntegral_respectsIso ?_
  introv int
  rw [algebraMap_isIntegral_iff] at int ⊢
  infer_instance

Depends on / 依赖: IsStableUnderBaseChange, IsStableUnderBaseChange.mk, algebraMap_isIntegral_iff, infer_instance, introv, isIntegral_respectsIso
-/
theorem isIntegral_isStableUnderBaseChange : IsStableUnderBaseChange fun f => f.IsIntegral := by
  refine IsStableUnderBaseChange.mk isIntegral_respectsIso ?_
  introv int
  rw [algebraMap_isIntegral_iff] at int ⊢
  infer_instance

open Polynomial in
/--
theorem `isIntegral_ofLocalizationSpan` / 定理 `isIntegral_ofLocalizationSpan`

English:
theorem isIntegral_ofLocalizationSpan
  proof: by
  introv R hs H r
  let := f.toAlgebra
  change r in (integralClosure R S).toSubmodule
  apply Submodule.mem_of_span_eq_top_of_smul_pow_mem _ s hs
  rintro ⟨t, ht⟩
  let := (Localization.awayMap f t).toAlgebra
  have : IsScalarTower R (Localization.Away t) (Localization.Away (f t)) := .of_algebraMap_eq'
    (IsLocalization.lift_comp _).symm
  have : _root_.IsIntegral (Localization.Away t) (algebraMap S (Localization.Away (f t)) r) :=
    H ⟨t, ht⟩ (algebraMap _ _ r)
  obtain ⟨⟨_, n, rfl⟩, p, hp, hp'⟩ := this.exists_multiple_integral_of_isLocalization (.powers t)
  rw [IsScalarTower.algebraMap_eq R S]; rw [Submonoid.smul_def]; rw [Algebra.smul_def]; rw [IsScalarTower.algebraMap_apply R S]; rw [← map_mul]; rw [← hom_eval₂]; rw [IsLocalization.map_eq_zero_iff (.powers (f t))] at hp'
  obtain ⟨⟨x, m, (rfl : algebraMap R S t ^ m = x)⟩, e⟩ := hp'
  by_cases hp' : 1 <= p.natDegree; swap
  · obtain rfl : p = 1 := eq_one_of_monic_natDegree_zero hp (by lia)
    exact ⟨m, by simp [Algebra.smul_def, show algebraMap R S t ^ m = 0 by simpa using e]⟩
  refine ⟨m + n, p.scaleRoots (t ^ m), (monic_scaleRoots_iff _).mpr hp, ?_⟩
  have := p.scaleRoots_eval₂_mul (algebraMap R S) (t ^ n • r) (t ^ m)
  simp only [pow_add, ← Algebra.smul_def, mul_smul, ← map_pow] at e this ⊢
  rw [this]; rw [← tsub_add_cancel_of_le hp']; rw [pow_succ]; rw [mul_smul]; rw [e]; rw [smul_zero]

中文:
定理 is整数egral_ofLocalizationSpan
  证明: by
  introv R hs H r
  let := f.toAlgebra
  change r in (integralClosure R S).toSubmodule
  apply Submodule.mem_of_span_eq_top_of_smul_pow_mem _ s hs
  rintro ⟨t, ht⟩
  let := (Localization.awayMap f t).toAlgebra
  have : IsScalarTower R (Localization.Away t) (Localization.Away (f t)) := .of_algebraMap_eq'
    (IsLocalization.lift_comp _).symm
  have : _root_.IsIntegral (Localization.Away t) (algebraMap S (Localization.Away (f t)) r) :=
    H ⟨t, ht⟩ (algebraMap _ _ r)
  obtain ⟨⟨_, n, rfl⟩, p, hp, hp'⟩ := this.exists_multiple_integral_of_isLocalization (.powers t)
  rw [IsScalarTower.algebraMap_eq R S]; rw [Submonoid.smul_def]; rw [Algebra.smul_def]; rw [IsScalarTower.algebraMap_apply R S]; rw [← map_mul]; rw [← hom_eval₂]; rw [IsLocalization.map_eq_zero_iff (.powers (f t))] at hp'
  obtain ⟨⟨x, m, (rfl : algebraMap R S t ^ m = x)⟩, e⟩ := hp'
  by_cases hp' : 1 <= p.natDegree; swap
  · obtain rfl : p = 1 := eq_one_of_monic_natDegree_zero hp (by lia)
    exact ⟨m, by simp [Algebra.smul_def, show algebraMap R S t ^ m = 0 by simpa using e]⟩
  refine ⟨m + n, p.scaleRoots (t ^ m), (monic_scaleRoots_iff _).mpr hp, ?_⟩
  have := p.scaleRoots_eval₂_mul (algebraMap R S) (t ^ n • r) (t ^ m)
  simp only [pow_add, ← Algebra.smul_def, mul_smul, ← map_pow] at e this ⊢
  rw [this]; rw [← tsub_add_cancel_of_le hp']; rw [pow_succ]; rw [mul_smul]; rw [e]; rw [smul_zero]

Depends on / 依赖: IsIntegral, IsLocalization, IsLocalization.lift_comp, IsScalarTower, Localization, Localization.Away, Localization.awayMap, Submodule, Submodule.mem_of_span_eq_top_of_smul_pow_mem, _root_, _root_.IsIntegral, algebraMap, awayMap, exists_mu, f.toAlgebra, integralClosure, introv, lift_comp, mem_of_span_eq_top_of_smul_pow_mem, of_algebraMap_eq
-/
theorem isIntegral_ofLocalizationSpan :
    OfLocalizationSpan (RingHom.IsIntegral ·) := by
  introv R hs H r
  let := f.toAlgebra
  change r in (integralClosure R S).toSubmodule
  apply Submodule.mem_of_span_eq_top_of_smul_pow_mem _ s hs
  rintro ⟨t, ht⟩
  let := (Localization.awayMap f t).toAlgebra
  have : IsScalarTower R (Localization.Away t) (Localization.Away (f t)) := .of_algebraMap_eq'
    (IsLocalization.lift_comp _).symm
  have : _root_.IsIntegral (Localization.Away t) (algebraMap S (Localization.Away (f t)) r) :=
    H ⟨t, ht⟩ (algebraMap _ _ r)
  obtain ⟨⟨_, n, rfl⟩, p, hp, hp'⟩ := this.exists_multiple_integral_of_isLocalization (.powers t)
  rw [IsScalarTower.algebraMap_eq R S]; rw [Submonoid.smul_def]; rw [Algebra.smul_def]; rw [IsScalarTower.algebraMap_apply R S]; rw [← map_mul]; rw [← hom_eval₂]; rw [IsLocalization.map_eq_zero_iff (.powers (f t))] at hp'
  obtain ⟨⟨x, m, (rfl : algebraMap R S t ^ m = x)⟩, e⟩ := hp'
  by_cases hp' : 1 <= p.natDegree; swap
  · obtain rfl : p = 1 := eq_one_of_monic_natDegree_zero hp (by lia)
    exact ⟨m, by simp [Algebra.smul_def, show algebraMap R S t ^ m = 0 by simpa using e]⟩
  refine ⟨m + n, p.scaleRoots (t ^ m), (monic_scaleRoots_iff _).mpr hp, ?_⟩
  have := p.scaleRoots_eval₂_mul (algebraMap R S) (t ^ n • r) (t ^ m)
  simp only [pow_add, ← Algebra.smul_def, mul_smul, ← map_pow] at e this ⊢
  rw [this]; rw [← tsub_add_cancel_of_le hp']; rw [pow_succ]; rw [mul_smul]; rw [e]; rw [smul_zero]

end RingHom
