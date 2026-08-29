/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Jujian Zhang
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Basic

/-!
# Localization of modules is an exact functor

## Main definitions

- `LocalizedModule.map_exact`: Localization of modules is an exact functor.
- `IsLocalizedModule.map_exact`: A variant expressed in terms of `IsLocalizedModule`.

-/

public section

section

open IsLocalizedModule Function Submonoid

variable {R : Type*} [CommSemiring R] (S : Submonoid R)
variable {M₀ M₀'} [AddCommMonoid M₀] [AddCommMonoid M₀'] [Module R M₀] [Module R M₀']
variable (f₀ : M₀ ->ₗ[R] M₀') [IsLocalizedModule S f₀]
variable {M₁ M₁'} [AddCommMonoid M₁] [AddCommMonoid M₁'] [Module R M₁] [Module R M₁']
variable (f₁ : M₁ ->ₗ[R] M₁') [IsLocalizedModule S f₁]
variable {M₂ M₂'} [AddCommMonoid M₂] [AddCommMonoid M₂'] [Module R M₂] [Module R M₂']
variable (f₂ : M₂ ->ₗ[R] M₂') [IsLocalizedModule S f₂]

/--
lemma `LocalizedModule.map_exact` / 引理 `LocalizedModule.map_exact`

English:
lemma LocalizedModule.map_exact
  given: (g : M₀ ->ₗ[R] M₁) (h : M₁ ->ₗ[R] M₂) (ex : Exact g h)
  proof: fun y => Iff.intro
    (induction_on
      (fun m s hy => by
        rw [map_LocalizedModules]; rw [← zero_mk 1]; rw [mk_eq]; rw [one_smul]; rw [smul_zero] at hy
        obtain ⟨a, aS, ha⟩ := Subtype.exists.1 hy
        rw [smul_zero]; rw [mk_smul]; rw [← map_smul]; rw [ex (a • m)] at ha
        rca

中文:
引理 LocalizedModule.map_exact
  条件: (g : M₀ ->ₗ[R] M₁) (h : M₁ ->ₗ[R] M₂) (ex : Exact g h)
  证明: fun y => Iff.intro
    (induction_on
      (fun m s hy => by
        rw [map_LocalizedModules]; rw [← zero_mk 1]; rw [mk_eq]; rw [one_smul]; rw [smul_zero] at hy
        obtain ⟨a, aS, ha⟩ := Subtype.exists.1 hy
        rw [smul_zero]; rw [mk_smul]; rw [← map_smul]; rw [ex (a • m)] at ha
        rca

Depends on / 依赖: Iff.intro, Subtype, Subtype.exists, induction_on, map_LocalizedMo, map_LocalizedModules, map_smul, mk_cancel_common_left, mk_eq, mk_smul, one_smul, revert, smul_zero, zero_mk
-/
lemma LocalizedModule.map_exact (g : M₀ ->ₗ[R] M₁) (h : M₁ ->ₗ[R] M₂) (ex : Exact g h) :
    Exact (map S (mkLinearMap S M₀) (mkLinearMap S M₁) g)
    (map S (mkLinearMap S M₁) (mkLinearMap S M₂) h) :=
  fun y => Iff.intro
    (induction_on
      (fun m s hy => by
        rw [map_LocalizedModules]; rw [← zero_mk 1]; rw [mk_eq]; rw [one_smul]; rw [smul_zero] at hy
        obtain ⟨a, aS, ha⟩ := Subtype.exists.1 hy
        rw [smul_zero]; rw [mk_smul]; rw [← map_smul]; rw [ex (a • m)] at ha
        rcases ha with ⟨x, hx⟩
        use mk x (⟨a, aS⟩ * s)
        rw [map_LocalizedModules]; rw [hx]; rw [← mk_cancel_common_left ⟨a]; rw [aS⟩ s m]; rw [mk_smul])
      y)
    fun ⟨x, hx⟩ => by
      revert hx
      refine induction_on (fun m s hx => ?_) x
      rw [← hx]; rw [map_LocalizedModules]; rw [map_LocalizedModules]; rw [(ex (g m)).2 ⟨m]; rw [rfl⟩]; rw [zero_mk]

/--
theorem `IsLocalizedModule.map_exact` / 定理 `IsLocalizedModule.map_exact`

English:
theorem IsLocalizedModule.map_exact
  given: (g : M₀ ->ₗ[R] M₁) (h : M₁ ->ₗ[R] M₂) (ex : Function.Exact g h)
  proof: Function.Exact.of_ladder_linearEquiv_of_exact
    (map_iso_commute S f₀ f₁ g) (map_iso_commute S f₁ f₂ h) (LocalizedModule.map_exact S g h ex)

中文:
定理 IsLocalizedModule.map_exact
  条件: (g : M₀ ->ₗ[R] M₁) (h : M₁ ->ₗ[R] M₂) (ex : Function.Exact g h)
  证明: Function.Exact.of_ladder_linearEquiv_of_exact
    (map_iso_commute S f₀ f₁ g) (map_iso_commute S f₁ f₂ h) (LocalizedModule.map_exact S g h ex)

Depends on / 依赖: Function, Function.Exact.of_ladder_linearEquiv_of_exact, LocalizedModule, LocalizedModule.map_exact, map_exact, map_iso_commute, of_ladder_linearEquiv_of_exact
-/
theorem IsLocalizedModule.map_exact (g : M₀ ->ₗ[R] M₁) (h : M₁ ->ₗ[R] M₂) (ex : Function.Exact g h) :
    Function.Exact (map S f₀ f₁ g) (map S f₁ f₂ h) :=
  Function.Exact.of_ladder_linearEquiv_of_exact
    (map_iso_commute S f₀ f₁ g) (map_iso_commute S f₁ f₂ h) (LocalizedModule.map_exact S g h ex)

end
