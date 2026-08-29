/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.LocalProperties.Basic

/-!

# The meta properties of surjective ring homomorphisms.

## Main results

Let `R` be a commutative ring, `M` be a submonoid of `R`.

* `surjective_localizationPreserves` : `M⁻¹R →+* M⁻¹S` is surjective if `R →+* S` is surjective.
* `surjective_ofLocalizationSpan` : `R →+* S` is surjective if there exists a set `{ r }` that
  spans `R` such that `Rᵣ →+* Sᵣ` is surjective.
* `surjective_localRingHom_of_surjective` : A surjective ring homomorphism `R →+* S` induces a
  surjective homomorphism `R_{f⁻¹(P)} →+* S_P` for every prime ideal `P` of `S`.

-/

public section


namespace RingHom

open scoped TensorProduct

open TensorProduct Algebra.TensorProduct

universe u

local notation "surjective" => fun {X Y : Type _} [CommRing X] [CommRing Y] => fun f : X ->+* Y =>
  Function.Surjective f

/--
theorem `surjective_stableUnderComposition` / 定理 `surjective_stableUnderComposition`

English:
theorem surjective_stableUnderComposition
  statement: StableUnderComposition surjective
  proof: by
  introv R hf hg; exact hg.comp hf

中文:
定理 surjective_stableUnderComposition
  结论: StableUnderComposition surjective
  证明: by
  introv R hf hg; exact hg.comp hf

Depends on / 依赖: hg.comp, introv
-/
theorem surjective_stableUnderComposition : StableUnderComposition surjective := by
  introv R hf hg; exact hg.comp hf

/--
theorem `surjective_respectsIso` / 定理 `surjective_respectsIso`

English:
theorem surjective_respectsIso
  statement: RespectsIso surjective
  proof: by
  apply surjective_stableUnderComposition.respectsIso
  intro _ _ _ _ e
  exact e.surjective

中文:
定理 surjective_respectsIso
  结论: RespectsIso surjective
  证明: by
  apply surjective_stableUnderComposition.respectsIso
  intro _ _ _ _ e
  exact e.surjective

Depends on / 依赖: e.surjective, respectsIso, surjective, surjective_stableUnderComposition, surjective_stableUnderComposition.respectsIso
-/
theorem surjective_respectsIso : RespectsIso surjective := by
  apply surjective_stableUnderComposition.respectsIso
  intro _ _ _ _ e
  exact e.surjective

/--
theorem `surjective_isStableUnderBaseChange` / 定理 `surjective_isStableUnderBaseChange`

English:
theorem surjective_isStableUnderBaseChange
  statement: IsStableUnderBaseChange surjective
  proof: by
  refine IsStableUnderBaseChange.mk surjective_respectsIso ?_
  introv h x
  induction x with
  | zero => exact ⟨0, map_zero _⟩
  | tmul x y =>
    obtain ⟨y, rfl⟩ := h y; use y • x; dsimp
    rw [TensorProduct.smul_tmul]; rw [Algebra.algebraMap_eq_smul_one]
  | add x y ex ey => obtain ⟨⟨x, rfl⟩,

中文:
定理 surjective_isStableUnderBaseChange
  结论: 是StableUnderBaseChange surjective
  证明: by
  refine IsStableUnderBaseChange.mk surjective_respectsIso ?_
  introv h x
  induction x with
  | zero => exact ⟨0, map_zero _⟩
  | tmul x y =>
    obtain ⟨y, rfl⟩ := h y; use y • x; dsimp
    rw [TensorProduct.smul_tmul]; rw [Algebra.algebraMap_eq_smul_one]
  | add x y ex ey => obtain ⟨⟨x, rfl⟩,

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, IsStableUnderBaseChange, IsStableUnderBaseChange.mk, TensorProduct, TensorProduct.smul_tmul, algebraMap_eq_smul_one, introv, map_add, map_zero, smul_tmul, surjective_respectsIso
-/
theorem surjective_isStableUnderBaseChange : IsStableUnderBaseChange surjective := by
  refine IsStableUnderBaseChange.mk surjective_respectsIso ?_
  introv h x
  induction x with
  | zero => exact ⟨0, map_zero _⟩
  | tmul x y =>
    obtain ⟨y, rfl⟩ := h y; use y • x; dsimp
    rw [TensorProduct.smul_tmul]; rw [Algebra.algebraMap_eq_smul_one]
  | add x y ex ey => obtain ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩ := ex, ey; exact ⟨x + y, map_add _ x y⟩

/--
theorem `surjective_localizationPreserves` / 定理 `surjective_localizationPreserves`

English:
theorem surjective_localizationPreserves
  proof: by
  introv R H x
  obtain ⟨x, ⟨_, s, hs, rfl⟩, rfl⟩ := IsLocalization.exists_mk'_eq (M.map f) x
  obtain ⟨y, rfl⟩ := H x
  use IsLocalization.mk' R' y ⟨s, hs⟩
  rw [IsLocalization.map_mk']

中文:
定理 surjective_localizationPreserves
  证明: by
  introv R H x
  obtain ⟨x, ⟨_, s, hs, rfl⟩, rfl⟩ := IsLocalization.exists_mk'_eq (M.map f) x
  obtain ⟨y, rfl⟩ := H x
  use IsLocalization.mk' R' y ⟨s, hs⟩
  rw [IsLocalization.map_mk']

Depends on / 依赖: IsLocalization, IsLocalization.exists_mk, IsLocalization.map_mk, IsLocalization.mk, M.map, exists_mk, introv, map_mk
-/
theorem surjective_localizationPreserves :
    LocalizationPreserves surjective := by
  introv R H x
  obtain ⟨x, ⟨_, s, hs, rfl⟩, rfl⟩ := IsLocalization.exists_mk'_eq (M.map f) x
  obtain ⟨y, rfl⟩ := H x
  use IsLocalization.mk' R' y ⟨s, hs⟩
  rw [IsLocalization.map_mk']

/--
theorem `surjective_ofLocalizationSpan` / 定理 `surjective_ofLocalizationSpan`

English:
theorem surjective_ofLocalizationSpan
  statement: OfLocalizationSpan surjective
  proof: by
  introv R e H
  rw [← Set.range_eq_univ]; rw [Set.eq_univ_iff_forall]
  let := f.toAlgebra
  intro x
  apply Submodule.mem_of_span_eq_top_of_smul_pow_mem
    (LinearMap.range (Algebra.linearMap R S)) s e
  intro r
  obtain ⟨a, e'⟩ := H r (algebraMap _ _ x)
  obtain ⟨b, ⟨_, n, rfl⟩, rfl⟩ := IsLoc

中文:
定理 surjective_ofLocalizationSpan
  结论: OfLocalizationSpan surjective
  证明: by
  introv R e H
  rw [← Set.range_eq_univ]; rw [Set.eq_univ_iff_forall]
  let := f.toAlgebra
  intro x
  apply Submodule.mem_of_span_eq_top_of_smul_pow_mem
    (LinearMap.range (Algebra.linearMap R S)) s e
  intro r
  obtain ⟨a, e'⟩ := H r (algebraMap _ _ x)
  obtain ⟨b, ⟨_, n, rfl⟩, rfl⟩ := IsLoc

Depends on / 依赖: Algebra, Algebra.linearMap, IsLocalization, IsLocalization.Away.map, IsLocalization.eq_mk, IsLocalization.exists_mk, IsLocalization.map_mk, LinearMap, LinearMap.range, Localization, Localization.awayMap, Set.eq_univ_iff_forall, Set.range_eq_univ, Submodule, Submodule.mem_of_span_eq_top_of_smul_pow_mem, Submonoid, Submonoid.powers, Subtype, Subtype.coe_mk, _iff_mul_eq
-/
theorem surjective_ofLocalizationSpan : OfLocalizationSpan surjective := by
  introv R e H
  rw [← Set.range_eq_univ]; rw [Set.eq_univ_iff_forall]
  let := f.toAlgebra
  intro x
  apply Submodule.mem_of_span_eq_top_of_smul_pow_mem
    (LinearMap.range (Algebra.linearMap R S)) s e
  intro r
  obtain ⟨a, e'⟩ := H r (algebraMap _ _ x)
  obtain ⟨b, ⟨_, n, rfl⟩, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers (r : R)) a
  rw [Localization.awayMap]; rw [IsLocalization.Away.map]; rw [IsLocalization.map_mk']; rw [eq_comm]; rw [IsLocalization.eq_mk'_iff_mul_eq]; rw [Subtype.coe_mk]; rw [Subtype.coe_mk]; rw [← map_mul] at e'
  obtain ⟨⟨_, n', rfl⟩, e''⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers (f r)) _).mp e'
  dsimp only at e''
  rw [mul_comm x]; rw [← mul_assoc]; rw [← map_pow]; rw [← map_mul]; rw [← map_mul]; rw [← pow_add] at e''
  exact ⟨n' + n, _, e''.symm⟩

/--
theorem `surjective_localRingHom_of_surjective` / 定理 `surjective_localRingHom_of_surjective`

English:
theorem surjective_localRingHom_of_surjective
  statement: {R S : Type u} [CommRing R] [CommRing S]
  proof: have : IsLocalization (Submonoid.map f (Ideal.comap f P).primeCompl) (Localization.AtPrime P) :=
    (Submonoid.map_comap_eq_of_surjective h P.primeCompl).symm ▸ Localization.isLocalization
  surjective_localizationPreserves _ _ _ _ h

中文:
定理 surjective_localRingHom_of_surjective
  结论: {R S : 类型u} [交换环 R] [交换环 S]
  证明: have : IsLocalization (Submonoid.map f (Ideal.comap f P).primeCompl) (Localization.AtPrime P) :=
    (Submonoid.map_comap_eq_of_surjective h P.primeCompl).symm ▸ Localization.isLocalization
  surjective_localizationPreserves _ _ _ _ h

Depends on / 依赖: AtPrime, Ideal.comap, IsLocalization, Localization, Localization.AtPrime, Localization.isLocalization, P.primeCompl, Submonoid, Submonoid.map, Submonoid.map_comap_eq_of_surjective, isLocalization, map_comap_eq_of_surjective, primeCompl, surjective_localizationPreserves
-/
theorem surjective_localRingHom_of_surjective {R S : Type u} [CommRing R] [CommRing S]
    (f : R ->+* S) (h : Function.Surjective f) (P : Ideal S) [P.IsPrime] :
    Function.Surjective (Localization.localRingHom (P.comap f) P f rfl) :=
  have : IsLocalization (Submonoid.map f (Ideal.comap f P).primeCompl) (Localization.AtPrime P) :=
    (Submonoid.map_comap_eq_of_surjective h P.primeCompl).symm ▸ Localization.isLocalization
  surjective_localizationPreserves _ _ _ _ h

end RingHom
