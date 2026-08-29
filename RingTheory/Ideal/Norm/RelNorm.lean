/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best
-/
module

public import Mathlib.Algebra.GroupWithZero.Torsion
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.DedekindDomain.Instances
public import Mathlib.RingTheory.Ideal.Int
public import Mathlib.RingTheory.NormalClosure

/-!

# Ideal norms

This file defines the relative ideal norm `Ideal.spanNorm R (I : Ideal S) : Ideal S` as the ideal
spanned by the norms of elements in `I`.

## Main definitions

* `Ideal.spanNorm R (I : Ideal S)`: the ideal spanned by the norms of elements in `I`.
  This is used to define `Ideal.relNorm`.
* `Ideal.relNorm R (I : Ideal S)`: the relative ideal norm as a bundled monoid-with-zero morphism,
  defined as the ideal spanned by the norms of elements in `I`.

## Main results

* `map_mul Ideal.relNorm`: multiplicativity of the relative ideal norm
* `relNorm_relNorm`: transitivity of the relative ideal norm

-/

@[expose] public section

open Module
open scoped nonZeroDivisors

section SpanNorm

namespace Ideal

open Submodule

variable (R S : Type*) [CommRing R] [IsDomain R] {S : Type*} [CommRing S] [IsDomain S]
variable [IsIntegrallyClosed R] [IsIntegrallyClosed S] [Algebra R S] [Module.Finite R S]
variable [IsTorsionFree R S]

attribute [local instance] FractionRing.liftAlgebra

/--
Definition of `spanNorm` / `spanNorm` 的定义

English:
definition spanNorm
  signature: (I : Ideal S)
  body: Ideal.map (Algebra.intNorm R S) I

@[simp]

中文:
定义 spanNorm
  签名: (I : 理想 S)
  定义体: Ideal.map (Algebra.intNorm R S) I

@[simp]

Depends on / 依赖: Algebra, Algebra.intNorm, Ideal.map, intNorm
-/
noncomputable def spanNorm (I : Ideal S) : Ideal R :=
  Ideal.map (Algebra.intNorm R S) I

@[simp]
/--
theorem `spanNorm_bot` / 定理 `spanNorm_bot`

English:
theorem spanNorm_bot
  proof: span_eq_bot.mpr fun x hx => by simpa using hx

中文:
定理 spanNorm_bot
  证明: span_eq_bot.mpr fun x hx => by simpa using hx

Depends on / 依赖: span_eq_bot, span_eq_bot.mpr
-/
theorem spanNorm_bot :
    spanNorm R (⊥ : Ideal S) = ⊥ := span_eq_bot.mpr fun x hx => by simpa using hx

variable {R} in
@[simp]
/--
theorem `spanNorm_eq_bot_iff` / 定理 `spanNorm_eq_bot_iff`

English:
theorem spanNorm_eq_bot_iff
  given: {I : Ideal S}
  statement: spanNorm R I = ⊥ ↔ I = ⊥
  proof: by
  simp only [spanNorm, span_eq_bot, Set.mem_image, SetLike.mem_coe, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, Algebra.intNorm_eq_zero, @eq_bot_iff _ _ _ I, SetLike.le_def, map,
    mem_bot]

中文:
定理 spanNorm_eq_bot_iff
  条件: {I : 理想 S}
  结论: spanNorm R I = ⊥ ↔ I = ⊥
  证明: by
  simp only [spanNorm, span_eq_bot, Set.mem_image, SetLike.mem_coe, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, Algebra.intNorm_eq_zero, @eq_bot_iff _ _ _ I, SetLike.le_def, map,
    mem_bot]

Depends on / 依赖: Algebra, Algebra.intNorm_eq_zero, Set.mem_image, SetLike, SetLike.le_def, SetLike.mem_coe, and_imp, eq_bot_iff, forall_exists_index, intNorm_eq_zero, le_def, mem_bot, mem_coe, mem_image, spanNorm, span_eq_bot
-/
theorem spanNorm_eq_bot_iff {I : Ideal S} : spanNorm R I = ⊥ ↔ I = ⊥ := by
  simp only [spanNorm, span_eq_bot, Set.mem_image, SetLike.mem_coe, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, Algebra.intNorm_eq_zero, @eq_bot_iff _ _ _ I, SetLike.le_def, map,
    mem_bot]

/--
theorem `intNorm_mem_spanNorm` / 定理 `intNorm_mem_spanNorm`

English:
theorem intNorm_mem_spanNorm
  given: {I : Ideal S} {x : S} (hx : x in I)
  proof: subset_span (Set.mem_image_of_mem _ hx)

中文:
定理 intNorm_mem_spanNorm
  条件: {I : 理想 S} {x : S} (hx : x in I)
  证明: subset_span (Set.mem_image_of_mem _ hx)

Depends on / 依赖: Set.mem_image_of_mem, mem_image_of_mem, subset_span
-/
theorem intNorm_mem_spanNorm {I : Ideal S} {x : S} (hx : x in I) :
    Algebra.intNorm R S x in I.spanNorm R :=
  subset_span (Set.mem_image_of_mem _ hx)

/--
theorem `norm_mem_spanNorm` / 定理 `norm_mem_spanNorm`

English:
theorem norm_mem_spanNorm
  given: [Module.Free R S] {I : Ideal S} (x : S) (hx : x in I)
  proof: by
  refine subset_span ⟨x, hx, ?_⟩
  rw [Algebra.intNorm_eq_norm]

@[simp]

中文:
定理 norm_mem_spanNorm
  条件: [模.自由 R S] {I : 理想 S} (x : S) (hx : x in I)
  证明: by
  refine subset_span ⟨x, hx, ?_⟩
  rw [Algebra.intNorm_eq_norm]

@[simp]

Depends on / 依赖: Algebra, Algebra.intNorm_eq_norm, intNorm_eq_norm, subset_span
-/
theorem norm_mem_spanNorm [Module.Free R S] {I : Ideal S} (x : S) (hx : x in I) :
    Algebra.norm R x in I.spanNorm R := by
  refine subset_span ⟨x, hx, ?_⟩
  rw [Algebra.intNorm_eq_norm]

@[simp]
/--
theorem `spanNorm_singleton` / 定理 `spanNorm_singleton`

English:
theorem spanNorm_singleton
  given: {r : S}
  proof: le_antisymm
    (span_le.mpr fun x hx =>
      mem_span_singleton.mpr
        (by
          obtain ⟨x, hx', rfl⟩ := (Set.mem_image _ _ _).mp hx
          exact map_dvd _ (mem_span_singleton.mp hx')))
    ((span_singleton_le_iff_mem _).mpr (intNorm_mem_spanNorm _ (mem_span_singleton_self _)))

@[simp]

中文:
定理 spanNorm_singleton
  条件: {r : S}
  证明: le_antisymm
    (span_le.mpr fun x hx =>
      mem_span_singleton.mpr
        (by
          obtain ⟨x, hx', rfl⟩ := (Set.mem_image _ _ _).mp hx
          exact map_dvd _ (mem_span_singleton.mp hx')))
    ((span_singleton_le_iff_mem _).mpr (intNorm_mem_spanNorm _ (mem_span_singleton_self _)))

@[simp]

Depends on / 依赖: Set.mem_image, intNorm_mem_spanNorm, le_antisymm, map_dvd, mem_image, mem_span_singleton, mem_span_singleton.mp, mem_span_singleton.mpr, mem_span_singleton_self, span_le, span_le.mpr, span_singleton_le_iff_mem
-/
theorem spanNorm_singleton {r : S} :
    spanNorm R (span ({r} : Set S)) = span {Algebra.intNorm R S r} :=
  le_antisymm
    (span_le.mpr fun x hx =>
      mem_span_singleton.mpr
        (by
          obtain ⟨x, hx', rfl⟩ := (Set.mem_image _ _ _).mp hx
          exact map_dvd _ (mem_span_singleton.mp hx')))
    ((span_singleton_le_iff_mem _).mpr (intNorm_mem_spanNorm _ (mem_span_singleton_self _)))

@[simp]
/--
theorem `spanNorm_top` / 定理 `spanNorm_top`

English:
theorem spanNorm_top
  statement: spanNorm R (⊤ : Ideal S) = ⊤
  proof: by
  simp [← Ideal.span_singleton_one]

中文:
定理 spanNorm_top
  结论: spanNorm R (⊤ : 理想 S) = ⊤
  证明: by
  simp [← Ideal.span_singleton_one]

Depends on / 依赖: Ideal.span_singleton_one, span_singleton_one
-/
theorem spanNorm_top : spanNorm R (⊤ : Ideal S) = ⊤ := by
  simp [← Ideal.span_singleton_one]

/--
theorem `map_spanIntNorm` / 定理 `map_spanIntNorm`

English:
theorem map_spanIntNorm
  given: (I : Ideal S) {T : Type*} [Semiring T] (f : R ->+* T)
  proof: by
  rw [spanNorm]
  nth_rw 2 [map]
  simp [map_span, Set.image_image]

@[gcongr, mono]

中文:
定理 map_span整数Norm
  条件: (I : 理想 S) {T : 类型} [半环 T] (f : R ->+* T)
  证明: by
  rw [spanNorm]
  nth_rw 2 [map]
  simp [map_span, Set.image_image]

@[gcongr, mono]

Depends on / 依赖: Set.image_image, image_image, map_span, nth_rw, spanNorm
-/
theorem map_spanIntNorm (I : Ideal S) {T : Type*} [Semiring T] (f : R ->+* T) :
    map f (spanNorm R I) = span (f ∘ Algebra.intNorm R S '' (I : Set S)) := by
  rw [spanNorm]
  nth_rw 2 [map]
  simp [map_span, Set.image_image]

@[gcongr, mono]
/--
theorem `spanNorm_mono` / 定理 `spanNorm_mono`

English:
theorem spanNorm_mono
  given: {I J : Ideal S} (h : I <= J)
  statement: spanNorm R I <= spanNorm R J
  proof: Ideal.span_mono (Set.monotone_image h)

中文:
定理 spanNorm_mono
  条件: {I J : 理想 S} (h : I <= J)
  结论: spanNorm R I <= spanNorm R J
  证明: Ideal.span_mono (Set.monotone_image h)

Depends on / 依赖: Ideal.span_mono, Set.monotone_image, monotone_image, span_mono
-/
theorem spanNorm_mono {I J : Ideal S} (h : I <= J) : spanNorm R I <= spanNorm R J :=
  Ideal.span_mono (Set.monotone_image h)

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `spanIntNorm_localization` / 定理 `spanIntNorm_localization`

English:
theorem spanIntNorm_localization
  statement: (I : Ideal S) (M : Submonoid R) (hM : M <= R⁰)
  proof: by
  let K := FractionRing R
  let f : Rₘ ->+* K := IsLocalization.map _ (T := R⁰) (RingHom.id R) hM
  let L := FractionRing S
  let g : Sₘ ->+* L := IsLocalization.map _ (M := Algebra.algebraMapSubmonoid S M) (T := S⁰)
      (RingHom.id S) (Submonoid.map_le_of_le_comap _ <| hM.trans
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (FaithfulSMul.algebraMap_injective _ _)))
  algebraize [f, g, (algebraMap K L).comp f]
  have : IsScalarTower R Rₘ K := IsScalarTower.of_algebraMap_eq'
    (by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp, RingHomCompTriple.comp_eq])
  let _ := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization M Rₘ K
  have : IsScalarTower S Sₘ L := IsScalarTower.of_algebraMap_eq'
    (by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp, RingHomCompTriple.comp_eq])
  have : IsScalarTower Rₘ Sₘ L := by
    apply IsScalarTower.of_algebraMap_eq'
    apply IsLocalization.ringHom_ext M
    rw [RingHom.algebraMap_toAlgebra]; rw [RingHom.algebraMap_toAlgebra (R := Sₘ)]; rw [RingHom.comp_assoc]; rw [RingHom.comp_assoc]; rw [← IsScalarTower.algebraMap_eq]; rw [IsScalarTower.algebraMap_eq R S Sₘ]; rw [IsLocalization.map_comp]; rw [RingHom.comp_id]; rw [← RingHom.comp_assoc]; rw [IsLocalization.map_comp]; rw [RingHom.comp_id]; rw [← IsScalarTower.algebraMap_eq]; rw [← IsScalarTower.algebraMap_eq]
  let _ := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (Algebra.algebraMapSubmonoid S M) Sₘ L
  rw [map_spanIntNorm]
  refine span_eq_span (Set.image_subset_iff.mpr ?_) (Set.image_subset_iff.mpr ?_)
  · intro a' ha'
    simp only [Set.mem_preimage, submodule_span_eq, ← map_spanIntNorm, SetLike.mem_coe,
      IsLocalization.mem_map_algebraMap_iff (Algebra.algebraMapSubmonoid S M) Sₘ,
      IsLocalization.mem_map_algebraMap_iff M Rₘ, Prod.exists] at ha' ⊢
    obtain ⟨⟨a, ha⟩, ⟨_, ⟨s, hs, rfl⟩⟩, has⟩ := ha'
    refine ⟨⟨Algebra.intNorm R S a, intNorm_mem_spanNorm _ ha⟩,
      ⟨s ^ Module.finrank K L, pow_mem hs _⟩, ?_⟩
    simp only [map_pow] at has ⊢
    apply_fun algebraMap _ L at has
    apply_fun Algebra.norm K at has
    simp only [map_mul] at has
    rw [← IsScalarTower.algebraMap_apply]; rw [← IsScalarTower.algebraMap_apply]; rw [← IsScalarTower.algebraMap_apply]; rw [IsScalarTower.algebraMap_apply R K L]; rw [Algebra.norm_algebraMap] at has
    apply IsFractionRing.injective Rₘ K
    simp only [map_mul, map_pow]
    rwa [Algebra.algebraMap_intNorm (L := L), ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply, Algebra.algebraMap_intNorm (L := L)]
  · intro a ha
    rw [Set.mem_preimage]; rw [Function.comp_apply]; rw [Algebra.intNorm_eq_of_isLocalization M (Bₘ := Sₘ)]
    exact subset_span (Set.mem_image_of_mem _ (mem_map_of_mem _ ha))

中文:
定理 span整数Norm_localization
  结论: (I : 理想 S) (M : 子幺半群 R) (hM : M <= R⁰)
  证明: by
  let K := FractionRing R
  let f : Rₘ ->+* K := IsLocalization.map _ (T := R⁰) (RingHom.id R) hM
  let L := FractionRing S
  let g : Sₘ ->+* L := IsLocalization.map _ (M := Algebra.algebraMapSubmonoid S M) (T := S⁰)
      (RingHom.id S) (Submonoid.map_le_of_le_comap _ <| hM.trans
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (FaithfulSMul.algebraMap_injective _ _)))
  algebraize [f, g, (algebraMap K L).comp f]
  have : IsScalarTower R Rₘ K := IsScalarTower.of_algebraMap_eq'
    (by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp, RingHomCompTriple.comp_eq])
  let _ := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization M Rₘ K
  have : IsScalarTower S Sₘ L := IsScalarTower.of_algebraMap_eq'
    (by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp, RingHomCompTriple.comp_eq])
  have : IsScalarTower Rₘ Sₘ L := by
    apply IsScalarTower.of_algebraMap_eq'
    apply IsLocalization.ringHom_ext M
    rw [RingHom.algebraMap_toAlgebra]; rw [RingHom.algebraMap_toAlgebra (R := Sₘ)]; rw [RingHom.comp_assoc]; rw [RingHom.comp_assoc]; rw [← IsScalarTower.algebraMap_eq]; rw [IsScalarTower.algebraMap_eq R S Sₘ]; rw [IsLocalization.map_comp]; rw [RingHom.comp_id]; rw [← RingHom.comp_assoc]; rw [IsLocalization.map_comp]; rw [RingHom.comp_id]; rw [← IsScalarTower.algebraMap_eq]; rw [← IsScalarTower.algebraMap_eq]
  let _ := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (Algebra.algebraMapSubmonoid S M) Sₘ L
  rw [map_spanIntNorm]
  refine span_eq_span (Set.image_subset_iff.mpr ?_) (Set.image_subset_iff.mpr ?_)
  · intro a' ha'
    simp only [Set.mem_preimage, submodule_span_eq, ← map_spanIntNorm, SetLike.mem_coe,
      IsLocalization.mem_map_algebraMap_iff (Algebra.algebraMapSubmonoid S M) Sₘ,
      IsLocalization.mem_map_algebraMap_iff M Rₘ, Prod.exists] at ha' ⊢
    obtain ⟨⟨a, ha⟩, ⟨_, ⟨s, hs, rfl⟩⟩, has⟩ := ha'
    refine ⟨⟨Algebra.intNorm R S a, intNorm_mem_spanNorm _ ha⟩,
      ⟨s ^ Module.finrank K L, pow_mem hs _⟩, ?_⟩
    simp only [map_pow] at has ⊢
    apply_fun algebraMap _ L at has
    apply_fun Algebra.norm K at has
    simp only [map_mul] at has
    rw [← IsScalarTower.algebraMap_apply]; rw [← IsScalarTower.algebraMap_apply]; rw [← IsScalarTower.algebraMap_apply]; rw [IsScalarTower.algebraMap_apply R K L]; rw [Algebra.norm_algebraMap] at has
    apply IsFractionRing.injective Rₘ K
    simp only [map_mul, map_pow]
    rwa [Algebra.algebraMap_intNorm (L := L), ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply, Algebra.algebraMap_intNorm (L := L)]
  · intro a ha
    rw [Set.mem_preimage]; rw [Function.comp_apply]; rw [Algebra.intNorm_eq_of_isLocalization M (Bₘ := Sₘ)]
    exact subset_span (Set.mem_image_of_mem _ (mem_map_of_mem _ ha))

Depends on / 依赖: Algebra, Algebra.algebraMapSubmonoid, FaithfulSMul, FaithfulSMul.algebraMap_injective, FractionRing, IsLocalization, IsLocalization.map, IsScalarTower, IsScalarTower.of_algebraMap_eq, RingHom, RingHom.algebraM, RingHom.id, Submonoid, Submonoid.map_le_of_le_comap, algebraM, algebraMap, algebraMapSubmonoid, algebraMap_injective, algebraize, hM.trans
-/
theorem spanIntNorm_localization (I : Ideal S) (M : Submonoid R) (hM : M <= R⁰)
    {Rₘ : Type*} (Sₘ : Type*) [CommRing Rₘ] [Algebra R Rₘ] [CommRing Sₘ] [Algebra S Sₘ]
    [Algebra Rₘ Sₘ] [Algebra R Sₘ] [IsScalarTower R Rₘ Sₘ] [IsScalarTower R S Sₘ]
    [IsLocalization M Rₘ] [IsLocalization (Algebra.algebraMapSubmonoid S M) Sₘ]
    [IsIntegrallyClosed Rₘ] [IsDomain Rₘ] [IsDomain Sₘ] [IsTorsionFree Rₘ Sₘ]
    [Module.Finite Rₘ Sₘ] [IsIntegrallyClosed Sₘ] :
    spanNorm Rₘ (I.map (algebraMap S Sₘ)) = (spanNorm R I).map (algebraMap R Rₘ) := by
  let K := FractionRing R
  let f : Rₘ ->+* K := IsLocalization.map _ (T := R⁰) (RingHom.id R) hM
  let L := FractionRing S
  let g : Sₘ ->+* L := IsLocalization.map _ (M := Algebra.algebraMapSubmonoid S M) (T := S⁰)
      (RingHom.id S) (Submonoid.map_le_of_le_comap _ <| hM.trans
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (FaithfulSMul.algebraMap_injective _ _)))
  algebraize [f, g, (algebraMap K L).comp f]
  have : IsScalarTower R Rₘ K := IsScalarTower.of_algebraMap_eq'
    (by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp, RingHomCompTriple.comp_eq])
  let _ := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization M Rₘ K
  have : IsScalarTower S Sₘ L := IsScalarTower.of_algebraMap_eq'
    (by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp, RingHomCompTriple.comp_eq])
  have : IsScalarTower Rₘ Sₘ L := by
    apply IsScalarTower.of_algebraMap_eq'
    apply IsLocalization.ringHom_ext M
    rw [RingHom.algebraMap_toAlgebra]; rw [RingHom.algebraMap_toAlgebra (R := Sₘ)]; rw [RingHom.comp_assoc]; rw [RingHom.comp_assoc]; rw [← IsScalarTower.algebraMap_eq]; rw [IsScalarTower.algebraMap_eq R S Sₘ]; rw [IsLocalization.map_comp]; rw [RingHom.comp_id]; rw [← RingHom.comp_assoc]; rw [IsLocalization.map_comp]; rw [RingHom.comp_id]; rw [← IsScalarTower.algebraMap_eq]; rw [← IsScalarTower.algebraMap_eq]
  let _ := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (Algebra.algebraMapSubmonoid S M) Sₘ L
  rw [map_spanIntNorm]
  refine span_eq_span (Set.image_subset_iff.mpr ?_) (Set.image_subset_iff.mpr ?_)
  · intro a' ha'
    simp only [Set.mem_preimage, submodule_span_eq, ← map_spanIntNorm, SetLike.mem_coe,
      IsLocalization.mem_map_algebraMap_iff (Algebra.algebraMapSubmonoid S M) Sₘ,
      IsLocalization.mem_map_algebraMap_iff M Rₘ, Prod.exists] at ha' ⊢
    obtain ⟨⟨a, ha⟩, ⟨_, ⟨s, hs, rfl⟩⟩, has⟩ := ha'
    refine ⟨⟨Algebra.intNorm R S a, intNorm_mem_spanNorm _ ha⟩,
      ⟨s ^ Module.finrank K L, pow_mem hs _⟩, ?_⟩
    simp only [map_pow] at has ⊢
    apply_fun algebraMap _ L at has
    apply_fun Algebra.norm K at has
    simp only [map_mul] at has
    rw [← IsScalarTower.algebraMap_apply]; rw [← IsScalarTower.algebraMap_apply]; rw [← IsScalarTower.algebraMap_apply]; rw [IsScalarTower.algebraMap_apply R K L]; rw [Algebra.norm_algebraMap] at has
    apply IsFractionRing.injective Rₘ K
    simp only [map_mul, map_pow]
    rwa [Algebra.algebraMap_intNorm (L := L), ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply, Algebra.algebraMap_intNorm (L := L)]
  · intro a ha
    rw [Set.mem_preimage]; rw [Function.comp_apply]; rw [Algebra.intNorm_eq_of_isLocalization M (Bₘ := Sₘ)]
    exact subset_span (Set.mem_image_of_mem _ (mem_map_of_mem _ ha))

/--
theorem `spanNorm_mul_spanNorm_le` / 定理 `spanNorm_mul_spanNorm_le`

English:
theorem spanNorm_mul_spanNorm_le
  given: (I J : Ideal S)
  proof: by
  rw [spanNorm]; rw [spanNorm]; rw [spanNorm]
  nth_rw 1 [map]; nth_rw 1 [map]
  rw [Ideal.span_mul_span']; rw [← Set.image_mul]
  refine Ideal.span_mono (Set.monotone_image ?_)
  rintro _ ⟨x, hxI, y, hyJ, rfl⟩
  exact Ideal.mul_mem_mul hxI hyJ

中文:
定理 spanNorm_mul_spanNorm_le
  条件: (I J : 理想 S)
  证明: by
  rw [spanNorm]; rw [spanNorm]; rw [spanNorm]
  nth_rw 1 [map]; nth_rw 1 [map]
  rw [Ideal.span_mul_span']; rw [← Set.image_mul]
  refine Ideal.span_mono (Set.monotone_image ?_)
  rintro _ ⟨x, hxI, y, hyJ, rfl⟩
  exact Ideal.mul_mem_mul hxI hyJ

Depends on / 依赖: Ideal.mul_mem_mul, Ideal.span_mono, Ideal.span_mul_span, Set.image_mul, Set.monotone_image, image_mul, monotone_image, mul_mem_mul, nth_rw, spanNorm, span_mono, span_mul_span
-/
theorem spanNorm_mul_spanNorm_le (I J : Ideal S) :
    spanNorm R I * spanNorm R J <= spanNorm R (I * J) := by
  rw [spanNorm]; rw [spanNorm]; rw [spanNorm]
  nth_rw 1 [map]; nth_rw 1 [map]
  rw [Ideal.span_mul_span']; rw [← Set.image_mul]
  refine Ideal.span_mono (Set.monotone_image ?_)
  rintro _ ⟨x, hxI, y, hyJ, rfl⟩
  exact Ideal.mul_mem_mul hxI hyJ

/--
theorem `spanNorm_mul_of_bot_or_top` / 定理 `spanNorm_mul_of_bot_or_top`

English:
theorem spanNorm_mul_of_bot_or_top
  given: (eq_bot_or_top : forall I : Ideal R, I = ⊥ ∨ I = ⊤) (I J : Ideal S)
  proof: by
  refine le_antisymm ?_ (spanNorm_mul_spanNorm_le R _ _)
  rcases eq_bot_or_top (spanNorm R I) with hI | hI
  · rw [hI, spanNorm_eq_bot_iff.mp hI, bot_mul, spanNorm_bot]
    exact bot_le
  rw [hI]; rw [Ideal.top_mul]
  rcases eq_bot_or_top (spanNorm R J) with hJ | hJ
  · rw [hJ, spanNorm_eq_bot_iff.mp hJ, mul_bot, spanNorm_bot]
  rw [hJ]
  exact le_top

中文:
定理 spanNorm_mul_of_bot_or_top
  条件: (eq_bot_or_top : 对任意 I : 理想 R, I = ⊥ ∨ I = ⊤) (I J : 理想 S)
  证明: by
  refine le_antisymm ?_ (spanNorm_mul_spanNorm_le R _ _)
  rcases eq_bot_or_top (spanNorm R I) with hI | hI
  · rw [hI, spanNorm_eq_bot_iff.mp hI, bot_mul, spanNorm_bot]
    exact bot_le
  rw [hI]; rw [Ideal.top_mul]
  rcases eq_bot_or_top (spanNorm R J) with hJ | hJ
  · rw [hJ, spanNorm_eq_bot_iff.mp hJ, mul_bot, spanNorm_bot]
  rw [hJ]
  exact le_top

Depends on / 依赖: Ideal.top_mul, bot_le, bot_mul, eq_bot_or_top, le_antisymm, le_top, mul_bot, spanNorm, spanNorm_bot, spanNorm_eq_bot_iff, spanNorm_eq_bot_iff.mp, spanNorm_mul_spanNorm_le, top_mul
-/
theorem spanNorm_mul_of_bot_or_top (eq_bot_or_top : forall I : Ideal R, I = ⊥ ∨ I = ⊤) (I J : Ideal S) :
    spanNorm R (I * J) = spanNorm R I * spanNorm R J := by
  refine le_antisymm ?_ (spanNorm_mul_spanNorm_le R _ _)
  rcases eq_bot_or_top (spanNorm R I) with hI | hI
  · rw [hI, spanNorm_eq_bot_iff.mp hI, bot_mul, spanNorm_bot]
    exact bot_le
  rw [hI]; rw [Ideal.top_mul]
  rcases eq_bot_or_top (spanNorm R J) with hJ | hJ
  · rw [hJ, spanNorm_eq_bot_iff.mp hJ, mul_bot, spanNorm_bot]
  rw [hJ]
  exact le_top

/--
theorem `spanNorm_le_comap` / 定理 `spanNorm_le_comap`

English:
theorem spanNorm_le_comap
  given: (I : Ideal S)
  statement: spanNorm R I <= comap (algebraMap R S) I
  proof: by
  rw [spanNorm]; rw [Ideal.map]; rw [Ideal.span_le]; rw [← Submodule.span_le]
  intro x hx
  induction hx using Submodule.span_induction with
  | mem _ h =>
      obtain ⟨x, hx, rfl⟩ := h
exact mem_comap.mpr mem_of_dvd _ (Algebra.dvd_algebraMap_intNorm_self _ _ x) hx
  | zero => simp
  | add _ _ _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul _ _ _ hx => exact Submodule.smul_mem _ _ hx

中文:
定理 spanNorm_le_comap
  条件: (I : 理想 S)
  结论: spanNorm R I <= comap (algebraMap R S) I
  证明: by
  rw [spanNorm]; rw [Ideal.map]; rw [Ideal.span_le]; rw [← Submodule.span_le]
  intro x hx
  induction hx using Submodule.span_induction with
  | mem _ h =>
      obtain ⟨x, hx, rfl⟩ := h
exact mem_comap.mpr mem_of_dvd _ (Algebra.dvd_algebraMap_intNorm_self _ _ x) hx
  | zero => simp
  | add _ _ _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul _ _ _ hx => exact Submodule.smul_mem _ _ hx

Depends on / 依赖: Algebra, Algebra.dvd_algebraMap_intNorm_self, Ideal.map, Ideal.span_le, Submodule, Submodule.add_mem, Submodule.smul_mem, Submodule.span_induction, Submodule.span_le, add_mem, dvd_algebraMap_intNorm_self, mem_comap, mem_comap.mpr, mem_of_dvd, smul_mem, spanNorm, span_induction, span_le
-/
theorem spanNorm_le_comap (I : Ideal S) : spanNorm R I <= comap (algebraMap R S) I := by
  rw [spanNorm]; rw [Ideal.map]; rw [Ideal.span_le]; rw [← Submodule.span_le]
  intro x hx
  induction hx using Submodule.span_induction with
  | mem _ h =>
      obtain ⟨x, hx, rfl⟩ := h
exact mem_comap.mpr mem_of_dvd _ (Algebra.dvd_algebraMap_intNorm_self _ _ x) hx
  | zero => simp
  | add _ _ _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul _ _ _ hx => exact Submodule.smul_mem _ _ hx

set_option linter.overlappingInstances false

/--
theorem `spanNorm_mul` / 定理 `spanNorm_mul`

English:
theorem spanNorm_mul
  given: [IsDedekindDomain R] [IsDedekindDomain S] (I J : Ideal S)
  proof: by
  nontriviality R
  cases subsingleton_or_nontrivial S
  · have : forall I : Ideal S, I = ⊤ := fun I => Subsingleton.elim I ⊤
    simp [this I, this J]
  refine eq_of_localization_maximal (fun P hP => ?_)
  by_cases hP0 : P = ⊥
  · subst hP0
    rw [spanNorm_mul_of_bot_or_top]
    intro I
    exact or_iff_not_imp_right.mpr fun hI => (hP.eq_of_le hI bot_le).symm
  have : NeZero P := ⟨hP0⟩
  let P' := Algebra.algebraMapSubmonoid S P.primeCompl
  simp only [Ideal.map_mul, ← spanIntNorm_localization (R := R) (Sₘ := Localization P')
    _ _ P.primeCompl_le_nonZeroDivisors]
  rw [← (I.map _).span_singleton_generator]; rw [← (J.map _).span_singleton_generator]; rw [span_singleton_mul_span_singleton]; rw [spanNorm_singleton]; rw [spanNorm_singleton]; rw [spanNorm_singleton]; rw [span_singleton_mul_span_singleton]; rw [map_mul]

中文:
定理 spanNorm_mul
  条件: [是Dedekind整环 R] [是Dedekind整环 S] (I J : 理想 S)
  证明: by
  nontriviality R
  cases subsingleton_or_nontrivial S
  · have : forall I : Ideal S, I = ⊤ := fun I => Subsingleton.elim I ⊤
    simp [this I, this J]
  refine eq_of_localization_maximal (fun P hP => ?_)
  by_cases hP0 : P = ⊥
  · subst hP0
    rw [spanNorm_mul_of_bot_or_top]
    intro I
    exact or_iff_not_imp_right.mpr fun hI => (hP.eq_of_le hI bot_le).symm
  have : NeZero P := ⟨hP0⟩
  let P' := Algebra.algebraMapSubmonoid S P.primeCompl
  simp only [Ideal.map_mul, ← spanIntNorm_localization (R := R) (Sₘ := Localization P')
    _ _ P.primeCompl_le_nonZeroDivisors]
  rw [← (I.map _).span_singleton_generator]; rw [← (J.map _).span_singleton_generator]; rw [span_singleton_mul_span_singleton]; rw [spanNorm_singleton]; rw [spanNorm_singleton]; rw [spanNorm_singleton]; rw [span_singleton_mul_span_singleton]; rw [map_mul]

Depends on / 依赖: Algebra, Algebra.algebraMapSubmonoid, Ideal.map_mul, Localization, NeZero, P.primeCompl, Subsingleton, Subsingleton.elim, algebraMapSubmonoid, bot_le, eq_of_le, eq_of_localization_maximal, hP.eq_of_le, map_mul, nontriviality, or_iff_not_imp_right, or_iff_not_imp_right.mpr, primeCompl, spanIntNorm_localization, spanNorm_mul_of_bot_or_top
-/
theorem spanNorm_mul [IsDedekindDomain R] [IsDedekindDomain S] (I J : Ideal S) :
    spanNorm R (I * J) = spanNorm R I * spanNorm R J := by
  nontriviality R
  cases subsingleton_or_nontrivial S
  · have : forall I : Ideal S, I = ⊤ := fun I => Subsingleton.elim I ⊤
    simp [this I, this J]
  refine eq_of_localization_maximal (fun P hP => ?_)
  by_cases hP0 : P = ⊥
  · subst hP0
    rw [spanNorm_mul_of_bot_or_top]
    intro I
    exact or_iff_not_imp_right.mpr fun hI => (hP.eq_of_le hI bot_le).symm
  have : NeZero P := ⟨hP0⟩
  let P' := Algebra.algebraMapSubmonoid S P.primeCompl
  simp only [Ideal.map_mul, ← spanIntNorm_localization (R := R) (Sₘ := Localization P')
    _ _ P.primeCompl_le_nonZeroDivisors]
  rw [← (I.map _).span_singleton_generator]; rw [← (J.map _).span_singleton_generator]; rw [span_singleton_mul_span_singleton]; rw [spanNorm_singleton]; rw [spanNorm_singleton]; rw [spanNorm_singleton]; rw [span_singleton_mul_span_singleton]; rw [map_mul]

section spanNorm_spanNorm

variable (T : Type*) [CommRing T] [IsDomain T] [IsIntegrallyClosed T] [Algebra R T] [Algebra T S]
  [Module.Finite R T] [Module.Finite T S] [IsTorsionFree R T] [IsTorsionFree T S]
  [IsScalarTower R T S]

open _root_.Algebra

/--
theorem `le_spanNorm_spanNorm` / 定理 `le_spanNorm_spanNorm`

English:
theorem le_spanNorm_spanNorm
  given: (I : Ideal S)
  statement: spanNorm R I <= spanNorm R (spanNorm T I)
  proof: by
  simp_rw [spanNorm, map]
  refine span_mono ?_
  rintro _ ⟨x, hx, rfl⟩
exact ⟨intNorm T S x, subset_span Set.mem_image_of_mem _ hx, by rw [intNorm_intNorm]⟩

中文:
定理 le_spanNorm_spanNorm
  条件: (I : 理想 S)
  结论: spanNorm R I <= spanNorm R (spanNorm T I)
  证明: by
  simp_rw [spanNorm, map]
  refine span_mono ?_
  rintro _ ⟨x, hx, rfl⟩
exact ⟨intNorm T S x, subset_span Set.mem_image_of_mem _ hx, by rw [intNorm_intNorm]⟩

Depends on / 依赖: Set.mem_image_of_mem, intNorm, intNorm_intNorm, mem_image_of_mem, simp_rw, spanNorm, span_mono, subset_span
-/
theorem le_spanNorm_spanNorm (I : Ideal S) : spanNorm R I <= spanNorm R (spanNorm T I) := by
  simp_rw [spanNorm, map]
  refine span_mono ?_
  rintro _ ⟨x, hx, rfl⟩
exact ⟨intNorm T S x, subset_span Set.mem_image_of_mem _ hx, by rw [intNorm_intNorm]⟩

/--
theorem `spanNorm_spanNorm_of_bot_or_top` / 定理 `spanNorm_spanNorm_of_bot_or_top`

English:
theorem spanNorm_spanNorm_of_bot_or_top
  statement: (eq_bot_or_top : forall I : Ideal R, I = ⊥ ∨ I = ⊤)
  proof: by
  obtain h | h := eq_bot_or_top (spanNorm R I)
  · rw [h, spanNorm_eq_bot_iff, spanNorm_eq_bot_iff, spanNorm_eq_bot_iff.mp h]
· exact h ▸ (eq_top_iff_one _).mpr le_spanNorm_spanNorm R T I (eq_top_iff_one _).mp h

中文:
定理 spanNorm_spanNorm_of_bot_or_top
  结论: (eq_bot_or_top : 对任意 I : 理想 R, I = ⊥ ∨ I = ⊤)
  证明: by
  obtain h | h := eq_bot_or_top (spanNorm R I)
  · rw [h, spanNorm_eq_bot_iff, spanNorm_eq_bot_iff, spanNorm_eq_bot_iff.mp h]
· exact h ▸ (eq_top_iff_one _).mpr le_spanNorm_spanNorm R T I (eq_top_iff_one _).mp h

Depends on / 依赖: eq_bot_or_top, eq_top_iff_one, le_spanNorm_spanNorm, spanNorm, spanNorm_eq_bot_iff, spanNorm_eq_bot_iff.mp
-/
theorem spanNorm_spanNorm_of_bot_or_top (eq_bot_or_top : forall I : Ideal R, I = ⊥ ∨ I = ⊤)
    (I : Ideal S) : spanNorm R (spanNorm T I) = spanNorm R I := by
  obtain h | h := eq_bot_or_top (spanNorm R I)
  · rw [h, spanNorm_eq_bot_iff, spanNorm_eq_bot_iff, spanNorm_eq_bot_iff.mp h]
· exact h ▸ (eq_top_iff_one _).mpr le_spanNorm_spanNorm R T I (eq_top_iff_one _).mp h

attribute [local instance] Localization.AtPrime.algebra_localization_localization

/--
theorem `spanNorm_spanNorm` / 定理 `spanNorm_spanNorm`

English:
theorem spanNorm_spanNorm
  statement: [IsDedekindDomain R] [IsDedekindDomain T] [IsDedekindDomain S]
  proof: by
  refine eq_of_localization_maximal fun P hP => ?_
  by_cases hP : P = ⊥
  · subst hP
    rw [spanNorm_spanNorm_of_bot_or_top]
    exact fun I => or_iff_not_imp_right.mpr fun hI => (hP.eq_of_le hI bot_le).symm
  let Rₚ := Localization.AtPrime P
  let Tₚ := Localization (algebraMapSubmonoid T P.primeCompl)
  let Sₚ := Localization (algebraMapSubmonoid S P.primeCompl)
  have : NeZero P := ⟨hP⟩
  have h : algebraMapSubmonoid T P.primeCompl <= T⁰ :=
      algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul _ (primeCompl_le_nonZeroDivisors P)
  rw [← spanIntNorm_localization R (spanNorm T I) _ (primeCompl_le_nonZeroDivisors P) Tₚ]; rw [← spanIntNorm_localization T (Rₘ := Tₚ) I _ h Sₚ]; rw [← spanIntNorm_localization R (Rₘ := Rₚ) I _
    (primeCompl_le_nonZeroDivisors P) Sₚ]; rw [← (I.map _).span_singleton_generator]; rw [spanNorm_singleton]; rw [spanNorm_singleton]; rw [intNorm_intNorm]; rw [spanNorm_singleton]

中文:
定理 spanNorm_spanNorm
  结论: [是Dedekind整环 R] [是Dedekind整环 T] [是Dedekind整环 S]
  证明: by
  refine eq_of_localization_maximal fun P hP => ?_
  by_cases hP : P = ⊥
  · subst hP
    rw [spanNorm_spanNorm_of_bot_or_top]
    exact fun I => or_iff_not_imp_right.mpr fun hI => (hP.eq_of_le hI bot_le).symm
  let Rₚ := Localization.AtPrime P
  let Tₚ := Localization (algebraMapSubmonoid T P.primeCompl)
  let Sₚ := Localization (algebraMapSubmonoid S P.primeCompl)
  have : NeZero P := ⟨hP⟩
  have h : algebraMapSubmonoid T P.primeCompl <= T⁰ :=
      algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul _ (primeCompl_le_nonZeroDivisors P)
  rw [← spanIntNorm_localization R (spanNorm T I) _ (primeCompl_le_nonZeroDivisors P) Tₚ]; rw [← spanIntNorm_localization T (Rₘ := Tₚ) I _ h Sₚ]; rw [← spanIntNorm_localization R (Rₘ := Rₚ) I _
    (primeCompl_le_nonZeroDivisors P) Sₚ]; rw [← (I.map _).span_singleton_generator]; rw [spanNorm_singleton]; rw [spanNorm_singleton]; rw [intNorm_intNorm]; rw [spanNorm_singleton]

Depends on / 依赖: AtPrime, Localization, Localization.AtPrime, NeZero, P.primeCompl, algebraMapSubmonoid, algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul, bot_le, eq_of_le, eq_of_localization_maximal, hP.eq_of_le, or_iff_not_imp_right, or_iff_not_imp_right.mpr, primeCompl, primeCompl_le, spanNorm_spanNorm_of_bot_or_top
-/
theorem spanNorm_spanNorm [IsDedekindDomain R] [IsDedekindDomain T] [IsDedekindDomain S]
    (I : Ideal S) : spanNorm R (spanNorm T I) = spanNorm R I := by
  refine eq_of_localization_maximal fun P hP => ?_
  by_cases hP : P = ⊥
  · subst hP
    rw [spanNorm_spanNorm_of_bot_or_top]
    exact fun I => or_iff_not_imp_right.mpr fun hI => (hP.eq_of_le hI bot_le).symm
  let Rₚ := Localization.AtPrime P
  let Tₚ := Localization (algebraMapSubmonoid T P.primeCompl)
  let Sₚ := Localization (algebraMapSubmonoid S P.primeCompl)
  have : NeZero P := ⟨hP⟩
  have h : algebraMapSubmonoid T P.primeCompl <= T⁰ :=
      algebraMapSubmonoid_le_nonZeroDivisors_of_faithfulSMul _ (primeCompl_le_nonZeroDivisors P)
  rw [← spanIntNorm_localization R (spanNorm T I) _ (primeCompl_le_nonZeroDivisors P) Tₚ]; rw [← spanIntNorm_localization T (Rₘ := Tₚ) I _ h Sₚ]; rw [← spanIntNorm_localization R (Rₘ := Rₚ) I _
    (primeCompl_le_nonZeroDivisors P) Sₚ]; rw [← (I.map _).span_singleton_generator]; rw [spanNorm_singleton]; rw [spanNorm_singleton]; rw [intNorm_intNorm]; rw [spanNorm_singleton]

end spanNorm_spanNorm

variable [IsDedekindDomain R] [IsDedekindDomain S]

/--
Definition of `relNorm` / `relNorm` 的定义

English:
definition relNorm
  signature: : Ideal S ->*₀ Ideal R where
  body: spanNorm R
  map_zero' := spanNorm_bot R
  map_one' := by rw [one_eq_top, spanNorm_top R, one_eq_top]
  map_mul' := spanNorm_mul R

中文:
定义 relNorm
  签名: : 理想 S ->*₀ 理想 R where
  定义体: spanNorm R
  map_zero' := spanNorm_bot R
  map_one' := by rw [one_eq_top, spanNorm_top R, one_eq_top]
  map_mul' := spanNorm_mul R

Depends on / 依赖: spanNorm
-/
noncomputable def relNorm : Ideal S ->*₀ Ideal R where
  toFun := spanNorm R
  map_zero' := spanNorm_bot R
  map_one' := by rw [one_eq_top, spanNorm_top R, one_eq_top]
  map_mul' := spanNorm_mul R

/--
theorem `relNorm_apply` / 定理 `relNorm_apply`

English:
theorem relNorm_apply
  given: (I : Ideal S)
  proof: rfl

@[simp]

中文:
定理 relNorm_apply
  条件: (I : 理想 S)
  证明: rfl

@[simp]
-/
theorem relNorm_apply (I : Ideal S) :
    relNorm R I = span (Algebra.intNorm R S '' (I : Set S) : Set R) :=
  rfl

@[simp]
/--
theorem `spanNorm_eq` / 定理 `spanNorm_eq`

English:
theorem spanNorm_eq
  given: (I : Ideal S)
  statement: spanNorm R I = relNorm R I
  proof: rfl

@[simp]

中文:
定理 spanNorm_eq
  条件: (I : 理想 S)
  结论: spanNorm R I = relNorm R I
  证明: rfl

@[simp]
-/
theorem spanNorm_eq (I : Ideal S) : spanNorm R I = relNorm R I := rfl

@[simp]
/--
theorem `relNorm_bot` / 定理 `relNorm_bot`

English:
theorem relNorm_bot
  statement: relNorm R (⊥ : Ideal S) = ⊥
  proof: by
  simpa only [zero_eq_bot] using map_zero (relNorm R : Ideal S ->*₀ _)

@[simp]

中文:
定理 relNorm_bot
  结论: relNorm R (⊥ : 理想 S) = ⊥
  证明: by
  simpa only [zero_eq_bot] using map_zero (relNorm R : Ideal S ->*₀ _)

@[simp]

Depends on / 依赖: map_zero, relNorm, zero_eq_bot
-/
theorem relNorm_bot : relNorm R (⊥ : Ideal S) = ⊥ := by
  simpa only [zero_eq_bot] using map_zero (relNorm R : Ideal S ->*₀ _)

@[simp]
/--
theorem `relNorm_top` / 定理 `relNorm_top`

English:
theorem relNorm_top
  statement: relNorm R (⊤ : Ideal S) = ⊤
  proof: by
  simpa only [one_eq_top] using map_one (relNorm R : Ideal S ->*₀ _)

中文:
定理 relNorm_top
  结论: relNorm R (⊤ : 理想 S) = ⊤
  证明: by
  simpa only [one_eq_top] using map_one (relNorm R : Ideal S ->*₀ _)

Depends on / 依赖: map_one, one_eq_top, relNorm
-/
theorem relNorm_top : relNorm R (⊤ : Ideal S) = ⊤ := by
  simpa only [one_eq_top] using map_one (relNorm R : Ideal S ->*₀ _)

variable {R} in
@[simp]
/--
theorem `relNorm_eq_bot_iff` / 定理 `relNorm_eq_bot_iff`

English:
theorem relNorm_eq_bot_iff
  given: {I : Ideal S}
  statement: relNorm R I = ⊥ ↔ I = ⊥
  proof: spanNorm_eq_bot_iff

中文:
定理 relNorm_eq_bot_iff
  条件: {I : 理想 S}
  结论: relNorm R I = ⊥ ↔ I = ⊥
  证明: spanNorm_eq_bot_iff

Depends on / 依赖: spanNorm_eq_bot_iff
-/
theorem relNorm_eq_bot_iff {I : Ideal S} : relNorm R I = ⊥ ↔ I = ⊥ :=
  spanNorm_eq_bot_iff

/--
theorem `norm_mem_relNorm` / 定理 `norm_mem_relNorm`

English:
theorem norm_mem_relNorm
  given: [Module.Free R S] (I : Ideal S) {x : S} (hx : x in I)
  proof: norm_mem_spanNorm R x hx

@[simp]

中文:
定理 norm_mem_relNorm
  条件: [模.自由 R S] (I : 理想 S) {x : S} (hx : x in I)
  证明: norm_mem_spanNorm R x hx

@[simp]

Depends on / 依赖: norm_mem_spanNorm
-/
theorem norm_mem_relNorm [Module.Free R S] (I : Ideal S) {x : S} (hx : x in I) :
    Algebra.norm R x in relNorm R I :=
  norm_mem_spanNorm R x hx

@[simp]
/--
theorem `relNorm_singleton` / 定理 `relNorm_singleton`

English:
theorem relNorm_singleton
  given: (r : S)
  statement: relNorm R (span ({r} : Set S)) = span {Algebra.intNorm R S r}
  proof: spanNorm_singleton R

中文:
定理 relNorm_singleton
  条件: (r : S)
  结论: relNorm R (span ({r} : 集合 S)) = span {代数.intNorm R S r}
  证明: spanNorm_singleton R

Depends on / 依赖: spanNorm_singleton
-/
theorem relNorm_singleton (r : S) : relNorm R (span ({r} : Set S)) = span {Algebra.intNorm R S r} :=
  spanNorm_singleton R

/--
theorem `map_relNorm` / 定理 `map_relNorm`

English:
theorem map_relNorm
  given: (I : Ideal S) {T : Type*} [Semiring T] (f : R ->+* T)
  proof: map_spanIntNorm R I f

@[gcongr, mono]

中文:
定理 map_relNorm
  条件: (I : 理想 S) {T : 类型} [半环 T] (f : R ->+* T)
  证明: map_spanIntNorm R I f

@[gcongr, mono]

Depends on / 依赖: map_spanIntNorm
-/
theorem map_relNorm (I : Ideal S) {T : Type*} [Semiring T] (f : R ->+* T) :
    map f (relNorm R I) = span (f ∘ Algebra.intNorm R S '' (I : Set S)) :=
  map_spanIntNorm R I f

@[gcongr, mono]
/--
theorem `relNorm_mono` / 定理 `relNorm_mono`

English:
theorem relNorm_mono
  given: {I J : Ideal S} (h : I <= J)
  statement: relNorm R I <= relNorm R J
  proof: spanNorm_mono R h

中文:
定理 relNorm_mono
  条件: {I J : 理想 S} (h : I <= J)
  结论: relNorm R I <= relNorm R J
  证明: spanNorm_mono R h

Depends on / 依赖: spanNorm_mono
-/
theorem relNorm_mono {I J : Ideal S} (h : I <= J) : relNorm R I <= relNorm R J :=
  spanNorm_mono R h

variable {R}

/--
theorem `relNorm_map_algEquiv_aux` / 定理 `relNorm_map_algEquiv_aux`

English:
theorem relNorm_map_algEquiv_aux
  statement: {T : Type*} [CommRing T] [IsDedekindDomain T]
  proof: span_mono fun _ ⟨x, hx₁, hx₂⟩ => ⟨σ.toRingEquiv.symm x,
    by rwa [SetLike.mem_coe, Ideal.symm_apply_mem_of_equiv_iff],
    hx₂ ▸ Algebra.intNorm_map_algEquiv _ x σ.symm⟩

@[simp]

中文:
定理 relNorm_map_algEquiv_aux
  结论: {T : 类型} [交换环 T] [是Dedekind整环 T]
  证明: span_mono fun _ ⟨x, hx₁, hx₂⟩ => ⟨σ.toRingEquiv.symm x,
    by rwa [SetLike.mem_coe, Ideal.symm_apply_mem_of_equiv_iff],
    hx₂ ▸ Algebra.intNorm_map_algEquiv _ x σ.symm⟩

@[simp]
-/
private theorem relNorm_map_algEquiv_aux {T : Type*} [CommRing T] [IsDedekindDomain T]
    [IsIntegrallyClosed T] [Algebra R T] [Module.Finite R T] [IsTorsionFree R T]
    (σ : S ≃ₐ[R] T) (I : Ideal S) : relNorm R (I.map σ) <= relNorm R I :=
  span_mono fun _ ⟨x, hx₁, hx₂⟩ => ⟨σ.toRingEquiv.symm x,
    by rwa [SetLike.mem_coe, Ideal.symm_apply_mem_of_equiv_iff],
    hx₂ ▸ Algebra.intNorm_map_algEquiv _ x σ.symm⟩

@[simp]
/--
theorem `relNorm_map_algEquiv` / 定理 `relNorm_map_algEquiv`

English:
theorem relNorm_map_algEquiv
  statement: {T : Type*} [CommRing T] [IsDedekindDomain T] [IsIntegrallyClosed T]
  proof: by
  refine le_antisymm (relNorm_map_algEquiv_aux σ I) ?_
  convert! relNorm_map_algEquiv_aux σ.symm (I.map σ)
  change I = map σ.symm.toAlgHom (map σ.toAlgHom I)
  simp [map_mapₐ]

@[simp]

中文:
定理 relNorm_map_algEquiv
  结论: {T : 类型} [交换环 T] [是Dedekind整环 T] [是整闭 T]
  证明: by
  refine le_antisymm (relNorm_map_algEquiv_aux σ I) ?_
  convert! relNorm_map_algEquiv_aux σ.symm (I.map σ)
  change I = map σ.symm.toAlgHom (map σ.toAlgHom I)
  simp [map_mapₐ]

@[simp]

Depends on / 依赖: I.map, convert, le_antisymm, relNorm_map_algEquiv_aux, symm.toAlgHom, toAlgHom
-/
theorem relNorm_map_algEquiv {T : Type*} [CommRing T] [IsDedekindDomain T] [IsIntegrallyClosed T]
    [Algebra R T] [Module.Finite R T] [IsTorsionFree R T] (σ : S ≃ₐ[R] T) (I : Ideal S) :
    relNorm R (I.map σ) = relNorm R I := by
  refine le_antisymm (relNorm_map_algEquiv_aux σ I) ?_
  convert! relNorm_map_algEquiv_aux σ.symm (I.map σ)
  change I = map σ.symm.toAlgHom (map σ.toAlgHom I)
  simp [map_mapₐ]

@[simp]
/--
theorem `relNorm_comap_algEquiv` / 定理 `relNorm_comap_algEquiv`

English:
theorem relNorm_comap_algEquiv
  statement: {T : Type*} [CommRing T] [IsDedekindDomain T] [IsIntegrallyClosed T]
  proof: map_symm σ.toRingEquiv ▸ relNorm_map_algEquiv σ.symm I

中文:
定理 relNorm_comap_algEquiv
  结论: {T : 类型} [交换环 T] [是Dedekind整环 T] [是整闭 T]
  证明: map_symm σ.toRingEquiv ▸ relNorm_map_algEquiv σ.symm I

Depends on / 依赖: map_symm, relNorm_map_algEquiv, toRingEquiv
-/
theorem relNorm_comap_algEquiv {T : Type*} [CommRing T] [IsDedekindDomain T] [IsIntegrallyClosed T]
    [Algebra R T] [Module.Finite R T] [IsTorsionFree R T] (σ : S ≃ₐ[R] T) (I : Ideal T) :
    relNorm R (I.comap σ) = relNorm R I := map_symm σ.toRingEquiv ▸ relNorm_map_algEquiv σ.symm I

variable (R)

open MulSemiringAction Pointwise in
@[simp]
/--
theorem `relNorm_smul` / 定理 `relNorm_smul`

English:
theorem relNorm_smul
  statement: {G : Type*} [Group G] [MulSemiringAction G S] [SMulCommClass G R S] (g : G)
  proof: relNorm_map_algEquiv (toAlgEquiv R S g) I

中文:
定理 relNorm_smul
  结论: {G : 类型} [群 G] [MulSemiring作用 G S] [标量交换类 G R S] (g : G)
  证明: relNorm_map_algEquiv (toAlgEquiv R S g) I

Depends on / 依赖: relNorm_map_algEquiv, toAlgEquiv
-/
theorem relNorm_smul {G : Type*} [Group G] [MulSemiringAction G S] [SMulCommClass G R S] (g : G)
    (I : Ideal S) : relNorm R (g • I) = relNorm R I := relNorm_map_algEquiv (toAlgEquiv R S g) I

/--
theorem `relNorm_le_comap` / 定理 `relNorm_le_comap`

English:
theorem relNorm_le_comap
  given: (I : Ideal S)
  statement: relNorm R I <= comap (algebraMap R S) I
  proof: spanNorm_le_comap R I

中文:
定理 relNorm_le_comap
  条件: (I : 理想 S)
  结论: relNorm R I <= comap (algebraMap R S) I
  证明: spanNorm_le_comap R I

Depends on / 依赖: spanNorm_le_comap
-/
theorem relNorm_le_comap (I : Ideal S) : relNorm R I <= comap (algebraMap R S) I :=
  spanNorm_le_comap R I

/--
theorem `relNorm_relNorm` / 定理 `relNorm_relNorm`

English:
theorem relNorm_relNorm
  statement: (T : Type*) [CommRing T] [IsDedekindDomain T] [IsIntegrallyClosed T]
  proof: spanNorm_spanNorm _ _ _

中文:
定理 relNorm_relNorm
  结论: (T : 类型) [交换环 T] [是Dedekind整环 T] [是整闭 T]
  证明: spanNorm_spanNorm _ _ _

Depends on / 依赖: spanNorm_spanNorm
-/
theorem relNorm_relNorm (T : Type*) [CommRing T] [IsDedekindDomain T] [IsIntegrallyClosed T]
    [Algebra R T] [Algebra T S] [IsScalarTower R T S] [Module.Finite R T] [Module.Finite T S]
    [IsTorsionFree R T] [IsTorsionFree T S]
    (I : Ideal S) : relNorm R (relNorm T I) = relNorm R I :=
  spanNorm_spanNorm _ _ _

variable {R} (S)

attribute [local instance] Localization.AtPrime.liftAlgebra in
/--
theorem `relNorm_algebraMap` / 定理 `relNorm_algebraMap`

English:
theorem relNorm_algebraMap
  given: (I : Ideal R)
  proof: by
  rw [← spanNorm_eq]
  refine eq_of_localization_maximal (fun P hPd => ?_)
  let P' := Algebra.algebraMapSubmonoid S P.primeCompl
  let Rₚ := Localization.AtPrime P
  let K := FractionRing R
  rw [← spanIntNorm_localization R _ _ P.primeCompl_le_nonZeroDivisors (Localization P')]; rw [Ideal.map_pow]; rw [I.map_map]; rw [← IsScalarTower.algebraMap_eq]; rw [IsScalarTower.algebraMap_eq R Rₚ]; rw [← I.map_map]; rw [← (I.map _).span_singleton_generator]; rw [Ideal.map_span]; rw [Set.image_singleton]; rw [spanNorm_singleton]; rw [Ideal.span_singleton_pow]
  congr 2
  apply IsFractionRing.injective Rₚ K
  rw [Algebra.algebraMap_intNorm (L := FractionRing S)]; rw [← IsScalarTower.algebraMap_apply]; rw [IsScalarTower.algebraMap_apply Rₚ K]; rw [Algebra.norm_algebraMap]; rw [map_pow]; rw [IsFractionRing.finrank_eq R (FractionRing R) S (FractionRing S)]

中文:
定理 relNorm_algebraMap
  条件: (I : 理想 R)
  证明: by
  rw [← spanNorm_eq]
  refine eq_of_localization_maximal (fun P hPd => ?_)
  let P' := Algebra.algebraMapSubmonoid S P.primeCompl
  let Rₚ := Localization.AtPrime P
  let K := FractionRing R
  rw [← spanIntNorm_localization R _ _ P.primeCompl_le_nonZeroDivisors (Localization P')]; rw [Ideal.map_pow]; rw [I.map_map]; rw [← IsScalarTower.algebraMap_eq]; rw [IsScalarTower.algebraMap_eq R Rₚ]; rw [← I.map_map]; rw [← (I.map _).span_singleton_generator]; rw [Ideal.map_span]; rw [Set.image_singleton]; rw [spanNorm_singleton]; rw [Ideal.span_singleton_pow]
  congr 2
  apply IsFractionRing.injective Rₚ K
  rw [Algebra.algebraMap_intNorm (L := FractionRing S)]; rw [← IsScalarTower.algebraMap_apply]; rw [IsScalarTower.algebraMap_apply Rₚ K]; rw [Algebra.norm_algebraMap]; rw [map_pow]; rw [IsFractionRing.finrank_eq R (FractionRing R) S (FractionRing S)]

Depends on / 依赖: Algebra, Algebra.algebraMapSubmonoid, AtPrime, FractionRing, I.map, I.map_map, Ideal.map_pow, Ideal.map_span, IsScalarTower, IsScalarTower.algebraMap_eq, Localization, Localization.AtPrime, P.primeCompl, P.primeCompl_le_nonZeroDivisors, Set.image_singleton, algebraMapSubmonoid, algebraMap_eq, eq_of_localization_maximal, image_singleton, map_map
-/
theorem relNorm_algebraMap (I : Ideal R) :
    relNorm R (I.map (algebraMap R S)) = I ^ finrank R S := by
  rw [← spanNorm_eq]
  refine eq_of_localization_maximal (fun P hPd => ?_)
  let P' := Algebra.algebraMapSubmonoid S P.primeCompl
  let Rₚ := Localization.AtPrime P
  let K := FractionRing R
  rw [← spanIntNorm_localization R _ _ P.primeCompl_le_nonZeroDivisors (Localization P')]; rw [Ideal.map_pow]; rw [I.map_map]; rw [← IsScalarTower.algebraMap_eq]; rw [IsScalarTower.algebraMap_eq R Rₚ]; rw [← I.map_map]; rw [← (I.map _).span_singleton_generator]; rw [Ideal.map_span]; rw [Set.image_singleton]; rw [spanNorm_singleton]; rw [Ideal.span_singleton_pow]
  congr 2
  apply IsFractionRing.injective Rₚ K
  rw [Algebra.algebraMap_intNorm (L := FractionRing S)]; rw [← IsScalarTower.algebraMap_apply]; rw [IsScalarTower.algebraMap_apply Rₚ K]; rw [Algebra.norm_algebraMap]; rw [map_pow]; rw [IsFractionRing.finrank_eq R (FractionRing R) S (FractionRing S)]

variable (R)

/--
theorem `relNorm_algebraMap'` / 定理 `relNorm_algebraMap'`

English:
theorem relNorm_algebraMap'
  statement: {R'} [CommRing R'] (I : Ideal R') [Algebra R' R]
  proof: by
  rw [← relNorm_algebraMap]; rw [Ideal.map_map]; rw [IsScalarTower.algebraMap_eq R' R S]

中文:
定理 relNorm_algebraMap'
  结论: {R'} [交换环 R'] (I : 理想 R') [代数 R' R]
  证明: by
  rw [← relNorm_algebraMap]; rw [Ideal.map_map]; rw [IsScalarTower.algebraMap_eq R' R S]

Depends on / 依赖: Ideal.map_map, IsScalarTower, IsScalarTower.algebraMap_eq, algebraMap_eq, map_map, relNorm_algebraMap
-/
theorem relNorm_algebraMap' {R'} [CommRing R'] (I : Ideal R') [Algebra R' R]
    [Algebra R' S] [IsScalarTower R' R S] :
    relNorm R (I.map (algebraMap R' S)) = I.map (algebraMap R' R) ^ finrank R S := by
  rw [← relNorm_algebraMap]; rw [Ideal.map_map]; rw [IsScalarTower.algebraMap_eq R' R S]

section relNorm_prime

variable {R} {S} (P : Ideal S) (p : Ideal R) [hPp : P.LiesOver p]

/--
theorem `exists_relNorm_eq_pow_of_isPrime` / 定理 `exists_relNorm_eq_pow_of_isPrime`

English:
theorem exists_relNorm_eq_pow_of_isPrime
  given: [p.IsPrime]
  statement: exists s, relNorm R P = p ^ s
  proof: by
  by_cases hp : p = ⊥
  · refine ⟨1, ?_⟩
    have : P.LiesOver ⊥ := hp ▸ hPp
    rw [hp]; rw [eq_bot_of_liesOver_bot R P]; rw [relNorm_bot]; rw [bot_pow (one_ne_zero)]
  have h : relNorm R (map (algebraMap R S) p) <= relNorm R P :=
relNorm_mono _ map_le_iff_le_comap.mpr le_of_eq (liesOver_iff _ _).mp hPp
  rw [relNorm_algebraMap S]; rw [← dvd_iff_le]; rw [dvd_prime_pow (prime_of_isPrime hp inferInstance)] at h
  obtain ⟨s, _, hs⟩ := h
  exact ⟨s, by rwa [associated_iff_eq] at hs⟩

中文:
定理 存在_relNorm_eq_pow_of_isPrime
  条件: [p.是素]
  结论: 存在 s, relNorm R P = p ^ s
  证明: by
  by_cases hp : p = ⊥
  · refine ⟨1, ?_⟩
    have : P.LiesOver ⊥ := hp ▸ hPp
    rw [hp]; rw [eq_bot_of_liesOver_bot R P]; rw [relNorm_bot]; rw [bot_pow (one_ne_zero)]
  have h : relNorm R (map (algebraMap R S) p) <= relNorm R P :=
relNorm_mono _ map_le_iff_le_comap.mpr le_of_eq (liesOver_iff _ _).mp hPp
  rw [relNorm_algebraMap S]; rw [← dvd_iff_le]; rw [dvd_prime_pow (prime_of_isPrime hp inferInstance)] at h
  obtain ⟨s, _, hs⟩ := h
  exact ⟨s, by rwa [associated_iff_eq] at hs⟩

Depends on / 依赖: LiesOver, P.LiesOver, algebraMap, associated_iff_eq, bot_pow, dvd_iff_le, dvd_prime_pow, eq_bot_of_liesOver_bot, le_of_eq, liesOver_iff, map_le_iff_le_comap, map_le_iff_le_comap.mpr, one_ne_zero, prime_of_isPrime, relNorm, relNorm_algebraMap, relNorm_bot, relNorm_mono
-/
theorem exists_relNorm_eq_pow_of_isPrime [p.IsPrime] : exists s, relNorm R P = p ^ s := by
  by_cases hp : p = ⊥
  · refine ⟨1, ?_⟩
    have : P.LiesOver ⊥ := hp ▸ hPp
    rw [hp]; rw [eq_bot_of_liesOver_bot R P]; rw [relNorm_bot]; rw [bot_pow (one_ne_zero)]
  have h : relNorm R (map (algebraMap R S) p) <= relNorm R P :=
relNorm_mono _ map_le_iff_le_comap.mpr le_of_eq (liesOver_iff _ _).mp hPp
  rw [relNorm_algebraMap S]; rw [← dvd_iff_le]; rw [dvd_prime_pow (prime_of_isPrime hp inferInstance)] at h
  obtain ⟨s, _, hs⟩ := h
  exact ⟨s, by rwa [associated_iff_eq] at hs⟩

/--
theorem `relNorm_eq_pow_of_isPrime_isGalois` / 定理 `relNorm_eq_pow_of_isPrime_isGalois`

English:
theorem relNorm_eq_pow_of_isPrime_isGalois
  statement: [p.IsMaximal] [P.IsPrime]
  proof: by
  have : P.IsMaximal := IsMaximal.of_liesOver_isMaximal P p
  let G := Gal(FractionRing S/FractionRing R)
  let := IsIntegralClosure.MulSemiringAction R (FractionRing R) (FractionRing S) S
  have := IsGaloisGroup.of_isFractionRing G R S (FractionRing R) (FractionRing S)
  by_cases hp : p = ⊥
  · have h : P.inertiaDeg R != 0 := (inertiaDeg_pos P R).ne'
    have hP : P = ⊥ := by
      rw [hp] at hPp
      exact eq_bot_of_liesOver_bot R P
    rw [hp]; rw [hP]; rw [relNorm_bot]; rw [bot_pow]
    rwa [hP] at h
  obtain ⟨s, hs⟩ := exists_relNorm_eq_pow_of_isPrime P p
  suffices s = P.inertiaDeg R by rwa [this] at hs
  have h₀ : forall Q in (p.primesOver S).toFinset,
      relNorm R Q ^ Q.ramificationIdx R = p ^ ((p.ramificationIdxIn S) * s) := by
    intro Q hQ
    rw [Set.mem_toFinset] at hQ
    have : Q.IsPrime := hQ.1
    have : Q.LiesOver p := hQ.2
    rw [← ramificationIdxIn_eq_ramificationIdx p Q G]
    obtain ⟨σ, rfl⟩ := Ideal.exists_smul_eq_of_isGaloisGroup p P Q G
    rw [relNorm_smul]; rw [hs]; rw [← pow_mul]; rw [mul_comm]
  have h := (congr_arg (relNorm R ·) <|
    map_algebraMap_eq_finsetProd_pow hp).symm.trans <| relNorm_algebraMap S p
  simp +contextual only [map_prod, map_pow, h₀, Finset.prod_const, ← pow_mul] at h
  rwa [← IsGaloisGroup.card_eq_finrank' G R S,
    ← Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p S G, mul_comm,
    ← Set.ncard_eq_toFinset_card',
    ((IsLeftCancelMulZero.mul_left_cancel_of_ne_zero hp).pow_injective _).eq_iff,
    mul_right_inj' (IsDedekindDomain.primesOver_ncard_ne_zero p S),
    mul_right_inj' (ramificationIdxIn_ne_zero G), inertiaDegIn_eq_inertiaDeg p P G] at h
  rw [one_eq_top]
  exact IsMaximal.ne_top inferInstance

中文:
定理 relNorm_eq_pow_of_isPrime_isGalois
  结论: [p.是极大] [P.是素]
  证明: by
  have : P.IsMaximal := IsMaximal.of_liesOver_isMaximal P p
  let G := Gal(FractionRing S/FractionRing R)
  let := IsIntegralClosure.MulSemiringAction R (FractionRing R) (FractionRing S) S
  have := IsGaloisGroup.of_isFractionRing G R S (FractionRing R) (FractionRing S)
  by_cases hp : p = ⊥
  · have h : P.inertiaDeg R != 0 := (inertiaDeg_pos P R).ne'
    have hP : P = ⊥ := by
      rw [hp] at hPp
      exact eq_bot_of_liesOver_bot R P
    rw [hp]; rw [hP]; rw [relNorm_bot]; rw [bot_pow]
    rwa [hP] at h
  obtain ⟨s, hs⟩ := exists_relNorm_eq_pow_of_isPrime P p
  suffices s = P.inertiaDeg R by rwa [this] at hs
  have h₀ : forall Q in (p.primesOver S).toFinset,
      relNorm R Q ^ Q.ramificationIdx R = p ^ ((p.ramificationIdxIn S) * s) := by
    intro Q hQ
    rw [Set.mem_toFinset] at hQ
    have : Q.IsPrime := hQ.1
    have : Q.LiesOver p := hQ.2
    rw [← ramificationIdxIn_eq_ramificationIdx p Q G]
    obtain ⟨σ, rfl⟩ := Ideal.exists_smul_eq_of_isGaloisGroup p P Q G
    rw [relNorm_smul]; rw [hs]; rw [← pow_mul]; rw [mul_comm]
  have h := (congr_arg (relNorm R ·) <|
    map_algebraMap_eq_finsetProd_pow hp).symm.trans <| relNorm_algebraMap S p
  simp +contextual only [map_prod, map_pow, h₀, Finset.prod_const, ← pow_mul] at h
  rwa [← IsGaloisGroup.card_eq_finrank' G R S,
    ← Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p S G, mul_comm,
    ← Set.ncard_eq_toFinset_card',
    ((IsLeftCancelMulZero.mul_left_cancel_of_ne_zero hp).pow_injective _).eq_iff,
    mul_right_inj' (IsDedekindDomain.primesOver_ncard_ne_zero p S),
    mul_right_inj' (ramificationIdxIn_ne_zero G), inertiaDegIn_eq_inertiaDeg p P G] at h
  rw [one_eq_top]
  exact IsMaximal.ne_top inferInstance

Depends on / 依赖: FractionRing, IsGaloisGroup, IsGaloisGroup.of_isFractionRing, IsIntegralClosure, IsIntegralClosure.MulSemiringAction, IsMaximal, IsMaximal.of_liesOver_isMaximal, MulSemiringAction, P.IsMaximal, P.inertiaDeg, bot_pow, eq_bot_of_liesOver_bot, inertiaDeg, inertiaDeg_pos, of_isFractionRing, of_liesOver_isMaximal, relNorm_bot
-/
theorem relNorm_eq_pow_of_isPrime_isGalois [p.IsMaximal] [P.IsPrime]
    [IsGalois (FractionRing R) (FractionRing S)] : relNorm R P = p ^ P.inertiaDeg R := by
  have : P.IsMaximal := IsMaximal.of_liesOver_isMaximal P p
  let G := Gal(FractionRing S/FractionRing R)
  let := IsIntegralClosure.MulSemiringAction R (FractionRing R) (FractionRing S) S
  have := IsGaloisGroup.of_isFractionRing G R S (FractionRing R) (FractionRing S)
  by_cases hp : p = ⊥
  · have h : P.inertiaDeg R != 0 := (inertiaDeg_pos P R).ne'
    have hP : P = ⊥ := by
      rw [hp] at hPp
      exact eq_bot_of_liesOver_bot R P
    rw [hp]; rw [hP]; rw [relNorm_bot]; rw [bot_pow]
    rwa [hP] at h
  obtain ⟨s, hs⟩ := exists_relNorm_eq_pow_of_isPrime P p
  suffices s = P.inertiaDeg R by rwa [this] at hs
  have h₀ : forall Q in (p.primesOver S).toFinset,
      relNorm R Q ^ Q.ramificationIdx R = p ^ ((p.ramificationIdxIn S) * s) := by
    intro Q hQ
    rw [Set.mem_toFinset] at hQ
    have : Q.IsPrime := hQ.1
    have : Q.LiesOver p := hQ.2
    rw [← ramificationIdxIn_eq_ramificationIdx p Q G]
    obtain ⟨σ, rfl⟩ := Ideal.exists_smul_eq_of_isGaloisGroup p P Q G
    rw [relNorm_smul]; rw [hs]; rw [← pow_mul]; rw [mul_comm]
  have h := (congr_arg (relNorm R ·) <|
    map_algebraMap_eq_finsetProd_pow hp).symm.trans <| relNorm_algebraMap S p
  simp +contextual only [map_prod, map_pow, h₀, Finset.prod_const, ← pow_mul] at h
  rwa [← IsGaloisGroup.card_eq_finrank' G R S,
    ← Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p S G, mul_comm,
    ← Set.ncard_eq_toFinset_card',
    ((IsLeftCancelMulZero.mul_left_cancel_of_ne_zero hp).pow_injective _).eq_iff,
    mul_right_inj' (IsDedekindDomain.primesOver_ncard_ne_zero p S),
    mul_right_inj' (ramificationIdxIn_ne_zero G), inertiaDegIn_eq_inertiaDeg p P G] at h
  rw [one_eq_top]
  exact IsMaximal.ne_top inferInstance

/--
theorem `relNorm_eq_pow_of_isMaximal` / 定理 `relNorm_eq_pow_of_isMaximal`

English:
theorem relNorm_eq_pow_of_isMaximal
  given: [PerfectField (FractionRing R)] [P.IsMaximal] [p.IsMaximal]
  proof: by
  let T := Ring.NormalClosure R S
  obtain ⟨Q, hQ₁, hQ₂⟩ : exists Q : Ideal T, Q.IsMaximal ∧ Q.LiesOver P :=
    exists_maximal_ideal_liesOver_of_isIntegral P
  have : Q.LiesOver p := LiesOver.trans Q P p
  have h := relNorm_eq_pow_of_isPrime_isGalois Q p
  have : IsGalois (FractionRing S) (FractionRing T) :=
    IsGalois.tower_top_of_isGalois (FractionRing R) (FractionRing S) (FractionRing T)
  rwa [← relNorm_relNorm R S, relNorm_eq_pow_of_isPrime_isGalois Q P, map_pow,
    inertiaDeg_tower (R := R) P Q, pow_mul, pow_left_inj (inertiaDeg_pos Q S).ne'] at h

中文:
定理 relNorm_eq_pow_of_isMaximal
  条件: [完美域 (FractionRing R)] [P.是极大] [p.是极大]
  证明: by
  let T := Ring.NormalClosure R S
  obtain ⟨Q, hQ₁, hQ₂⟩ : exists Q : Ideal T, Q.IsMaximal ∧ Q.LiesOver P :=
    exists_maximal_ideal_liesOver_of_isIntegral P
  have : Q.LiesOver p := LiesOver.trans Q P p
  have h := relNorm_eq_pow_of_isPrime_isGalois Q p
  have : IsGalois (FractionRing S) (FractionRing T) :=
    IsGalois.tower_top_of_isGalois (FractionRing R) (FractionRing S) (FractionRing T)
  rwa [← relNorm_relNorm R S, relNorm_eq_pow_of_isPrime_isGalois Q P, map_pow,
    inertiaDeg_tower (R := R) P Q, pow_mul, pow_left_inj (inertiaDeg_pos Q S).ne'] at h

Depends on / 依赖: FractionRing, IsGalois, IsGalois.tower_top_of_isGalois, IsMaximal, LiesOver, LiesOver.trans, NormalClosure, Q.IsMaximal, Q.LiesOver, Ring.NormalClosure, exists_maximal_ideal_liesOver_of_isIntegral, inertiaDeg_tower, map_pow, pow_mul, relNorm_eq_pow_of_isPrime_isGalois, relNorm_relNorm, tower_top_of_isGalois
-/
theorem relNorm_eq_pow_of_isMaximal [PerfectField (FractionRing R)] [P.IsMaximal] [p.IsMaximal] :
    relNorm R P = p ^ P.inertiaDeg R := by
  let T := Ring.NormalClosure R S
  obtain ⟨Q, hQ₁, hQ₂⟩ : exists Q : Ideal T, Q.IsMaximal ∧ Q.LiesOver P :=
    exists_maximal_ideal_liesOver_of_isIntegral P
  have : Q.LiesOver p := LiesOver.trans Q P p
  have h := relNorm_eq_pow_of_isPrime_isGalois Q p
  have : IsGalois (FractionRing S) (FractionRing T) :=
    IsGalois.tower_top_of_isGalois (FractionRing R) (FractionRing S) (FractionRing T)
  rwa [← relNorm_relNorm R S, relNorm_eq_pow_of_isPrime_isGalois Q P, map_pow,
    inertiaDeg_tower (R := R) P Q, pow_mul, pow_left_inj (inertiaDeg_pos Q S).ne'] at h

end relNorm_prime

section absNorm

variable [Module.Free Int R] [Module.Free Int S] [Module.Finite Int S]

open UniqueFactorizationMonoid in
/--
theorem `absNorm_relNorm` / 定理 `absNorm_relNorm`

English:
theorem absNorm_relNorm
  given: [PerfectField (FractionRing R)] (I : Ideal S)
  proof: by
  have : Module.Finite Int R := Module.Finite.left Int R S
  by_cases hI : I = ⊥
  · simp [hI]
  rw [← prod_normalizedFactors_eq_self hI]
  refine Multiset.prod_induction (fun I => absNorm (relNorm R I) = absNorm I) _ ?_ ?_ ?_
  · intro _ _ hx hy
    rw [map_mul]; rw [map_mul]; rw [map_mul]; rw [hx]; rw [hy]
  · simp
  · intro Q hQ
    have hQ' : Q != ⊥ := ne_zero_of_mem_normalizedFactors hQ
    rw [Ideal.mem_normalizedFactors_iff hI] at hQ
    have : Q.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hQ' hQ.1
    let P := under R Q
    let p := absNorm (under Int P)
    have : Q.LiesOver (span {(p : Int)}) := LiesOver.trans Q P _
    rw [relNorm_eq_pow_of_isMaximal Q P]; rw [map_pow]; rw [← pow_inertiaDeg p]; rw [← pow_inertiaDeg p]; rw [← pow_mul]; rw [← inertiaDeg_tower]

中文:
定理 absNorm_relNorm
  条件: [完美域 (FractionRing R)] (I : 理想 S)
  证明: by
  have : Module.Finite Int R := Module.Finite.left Int R S
  by_cases hI : I = ⊥
  · simp [hI]
  rw [← prod_normalizedFactors_eq_self hI]
  refine Multiset.prod_induction (fun I => absNorm (relNorm R I) = absNorm I) _ ?_ ?_ ?_
  · intro _ _ hx hy
    rw [map_mul]; rw [map_mul]; rw [map_mul]; rw [hx]; rw [hy]
  · simp
  · intro Q hQ
    have hQ' : Q != ⊥ := ne_zero_of_mem_normalizedFactors hQ
    rw [Ideal.mem_normalizedFactors_iff hI] at hQ
    have : Q.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hQ' hQ.1
    let P := under R Q
    let p := absNorm (under Int P)
    have : Q.LiesOver (span {(p : Int)}) := LiesOver.trans Q P _
    rw [relNorm_eq_pow_of_isMaximal Q P]; rw [map_pow]; rw [← pow_inertiaDeg p]; rw [← pow_inertiaDeg p]; rw [← pow_mul]; rw [← inertiaDeg_tower]

Depends on / 依赖: DimensionLEOne, Finite, Ideal.mem_normalizedFactors_iff, IsMaximal, Module, Module.Finite, Module.Finite.left, Multiset, Multiset.prod_induction, Q.IsMaximal, Ring.DimensionLEOne.maximalOfPrime, absNorm, map_mul, maximalOfPrime, mem_normalizedFactors_iff, ne_zero_of_mem_normalizedFactors, prod_induction, prod_normalizedFactors_eq_self, relNorm
-/
theorem absNorm_relNorm [PerfectField (FractionRing R)] (I : Ideal S) :
    absNorm (relNorm R I) = absNorm I := by
  have : Module.Finite Int R := Module.Finite.left Int R S
  by_cases hI : I = ⊥
  · simp [hI]
  rw [← prod_normalizedFactors_eq_self hI]
  refine Multiset.prod_induction (fun I => absNorm (relNorm R I) = absNorm I) _ ?_ ?_ ?_
  · intro _ _ hx hy
    rw [map_mul]; rw [map_mul]; rw [map_mul]; rw [hx]; rw [hy]
  · simp
  · intro Q hQ
    have hQ' : Q != ⊥ := ne_zero_of_mem_normalizedFactors hQ
    rw [Ideal.mem_normalizedFactors_iff hI] at hQ
    have : Q.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hQ' hQ.1
    let P := under R Q
    let p := absNorm (under Int P)
    have : Q.LiesOver (span {(p : Int)}) := LiesOver.trans Q P _
    rw [relNorm_eq_pow_of_isMaximal Q P]; rw [map_pow]; rw [← pow_inertiaDeg p]; rw [← pow_inertiaDeg p]; rw [← pow_mul]; rw [← inertiaDeg_tower]

/--
theorem `relNorm_int` / 定理 `relNorm_int`

English:
theorem relNorm_int
  given: (I : Ideal S)
  proof: by
  rw [← Int.ideal_span_absNorm_eq_self (relNorm Int I)]; rw [absNorm_relNorm]

中文:
定理 relNorm_int
  条件: (I : 理想 S)
  证明: by
  rw [← Int.ideal_span_absNorm_eq_self (relNorm Int I)]; rw [absNorm_relNorm]

Depends on / 依赖: Int.ideal_span_absNorm_eq_self, absNorm_relNorm, ideal_span_absNorm_eq_self, relNorm
-/
theorem relNorm_int (I : Ideal S) :
    relNorm Int I = Ideal.span {(absNorm I : Int)} := by
  rw [← Int.ideal_span_absNorm_eq_self (relNorm Int I)]; rw [absNorm_relNorm]

/--
theorem `absNorm_algebraMap` / 定理 `absNorm_algebraMap`

English:
theorem absNorm_algebraMap
  given: (I : Ideal R) [Module.Finite Int R]
  proof: by
  rw [← absNorm_relNorm Int]; rw [← relNorm_relNorm Int R]; rw [relNorm_algebraMap]; rw [absNorm_relNorm]; rw [map_pow]

中文:
定理 absNorm_algebraMap
  条件: (I : 理想 R) [模.有限 整数 R]
  证明: by
  rw [← absNorm_relNorm Int]; rw [← relNorm_relNorm Int R]; rw [relNorm_algebraMap]; rw [absNorm_relNorm]; rw [map_pow]

Depends on / 依赖: absNorm_relNorm, map_pow, relNorm_algebraMap, relNorm_relNorm
-/
theorem absNorm_algebraMap (I : Ideal R) [Module.Finite Int R] :
    absNorm (I.map (algebraMap R S)) = absNorm I ^ finrank R S := by
  rw [← absNorm_relNorm Int]; rw [← relNorm_relNorm Int R]; rw [relNorm_algebraMap]; rw [absNorm_relNorm]; rw [map_pow]

end absNorm

end Ideal

end SpanNorm
