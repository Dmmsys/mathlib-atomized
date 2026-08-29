/-
Copyright (c) 2026 Sihan Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sihan Su, Yongle Hu, Yi Song
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Localization.Finiteness

/-!
# `Module.FinitePresentation` is a local property

In this file, we prove that `Module.FinitePresentation` is a local property.

## Main results
* `Module.FinitePresentation.of_localizationSpan` : If there exists a set `{ r }` of `R` that
  generates the unit ideal and such that `Mᵣ` is a finitely presented `Rᵣ`-module for each `r`,
  then `M` is a finitely presented `R`-module.
-/

public section

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] (s : Set R)

/--
theorem `Module.FinitePresentation.of_localizationSpan'` / 定理 `Module.FinitePresentation.of_localizationSpan'`

English:
theorem Module.FinitePresentation.of_localizationSpan'
  statement: (hs : Ideal.span s = ⊤)
  proof: by
  have : Module.Finite R M :=
    Module.Finite.of_localizationSpan' (Rₚ := Rₚ) s hs ϕ (fun _ => inferInstance)
  obtain ⟨n, f, fsurj⟩ := Module.Finite.exists_fin' R M
  rw [← Module.FinitePresentation.fg_ker_iff f fsurj]
  refine f.ker.of_localizationSpan' s hs (Rₚ := Rₚ)
    (fun g => TensorPro

中文:
定理 Module.FinitePresentation.of_localizationSpan'
  结论: (hs : Ideal.span s = ⊤)
  证明: by
  have : Module.Finite R M :=
    Module.Finite.of_localizationSpan' (Rₚ := Rₚ) s hs ϕ (fun _ => inferInstance)
  obtain ⟨n, f, fsurj⟩ := Module.Finite.exists_fin' R M
  rw [← Module.FinitePresentation.fg_ker_iff f fsurj]
  refine f.ker.of_localizationSpan' s hs (Rₚ := Rₚ)
    (fun g => TensorPro

Depends on / 依赖: Finite, FinitePresentation, LinearMap, LinearMap.localized, LinearMap.range_eq_top, Module, Module.Finite, Module.Finite.exists_fin, Module.Finite.of_localizationSpan, Module.FinitePresentation.fg_ker, Module.FinitePresentation.fg_ker_iff, Submonoid, Submonoid.powers, TensorProduct, TensorProduct.mk, _ker_eq_ker_localizedMap, exists_fin, f.ker.of_localizationSpan, fg_ker, fg_ker_iff
-/
theorem Module.FinitePresentation.of_localizationSpan' (hs : Ideal.span s = ⊤)
    {Mₚ : forall (_ : s), Type*} [forall (g : s), AddCommGroup (Mₚ g)] [forall (g : s), Module R (Mₚ g)]
    {Rₚ : forall (_ : s), Type*} [forall (g : s), CommRing (Rₚ g)] [forall (g : s), Algebra R (Rₚ g)]
    [forall (g : s), IsLocalization.Away g.val (Rₚ g)]
    [forall (g : s), Module (Rₚ g) (Mₚ g)] [forall (g : s), IsScalarTower R (Rₚ g) (Mₚ g)]
    (ϕ : forall (g : s), M ->ₗ[R] Mₚ g) [forall (g : s), IsLocalizedModule (Submonoid.powers g.val) (ϕ g)]
    (h : forall (g : s), Module.FinitePresentation (Rₚ g) (Mₚ g)) :
    Module.FinitePresentation R M := by
  have : Module.Finite R M :=
    Module.Finite.of_localizationSpan' (Rₚ := Rₚ) s hs ϕ (fun _ => inferInstance)
  obtain ⟨n, f, fsurj⟩ := Module.Finite.exists_fin' R M
  rw [← Module.FinitePresentation.fg_ker_iff f fsurj]
  refine f.ker.of_localizationSpan' s hs (Rₚ := Rₚ)
    (fun g => TensorProduct.mk R (Rₚ g) (Fin n -> R) 1) (fun g => ?_)
  rw [LinearMap.localized'_ker_eq_ker_localizedMap (Rₚ g) (Submonoid.powers g.1) _ (ϕ g) f]
  apply Module.FinitePresentation.fg_ker
  rw [← LinearMap.range_eq_top] at fsurj ⊢
  simp [← LinearMap.localized'_range_eq_range_localizedMap (Rₚ g) (Submonoid.powers g.1), fsurj]

/--
theorem `Module.FinitePresentation.of_localizationSpan` / 定理 `Module.FinitePresentation.of_localizationSpan`

English:
theorem Module.FinitePresentation.of_localizationSpan
  statement: (hs : Ideal.span s = ⊤)
  proof: of_localizationSpan' s hs (fun g => LocalizedModule.mkLinearMap (Submonoid.powers g.1) M) h

中文:
定理 Module.FinitePresentation.of_localizationSpan
  结论: (hs : Ideal.span s = ⊤)
  证明: of_localizationSpan' s hs (fun g => LocalizedModule.mkLinearMap (Submonoid.powers g.1) M) h

Depends on / 依赖: LocalizedModule, LocalizedModule.mkLinearMap, Submonoid, Submonoid.powers, mkLinearMap, of_localizationSpan, powers
-/
theorem Module.FinitePresentation.of_localizationSpan (hs : Ideal.span s = ⊤)
    (h : forall g : s, Module.FinitePresentation (Localization.Away g.1) (LocalizedModule.Away g.1 M)) :
    Module.FinitePresentation R M :=
  of_localizationSpan' s hs (fun g => LocalizedModule.mkLinearMap (Submonoid.powers g.1) M) h
