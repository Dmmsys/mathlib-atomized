/-
Copyright (c) 2022 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Eric Rodriguez
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Localization.NormTrace
public import Mathlib.RingTheory.Norm.Transitivity

/-!
# Norm in number fields

Given a finite extension of number fields, we define the norm morphism as a function between the
rings of integers.

## Main definitions
* `RingOfIntegers.norm K` : `Algebra.norm` as a morphism `(𝓞 L) →* (𝓞 K)`.

## Main results
* `RingOfIntegers.dvd_norm` : if `L/K` is a finite Galois extension of fields, then, for all
  `(x : 𝓞 L)` we have that `x ∣ algebraMap (𝓞 K) (𝓞 L) (norm K x)`.

-/

@[expose] public section


open scoped NumberField

open Finset NumberField Algebra Module IntermediateField

section Rat

variable {K : Type*} [Field K] [NumberField K] (x : 𝓞 K)

/--
theorem `Algebra.coe_norm_int` / 定理 `Algebra.coe_norm_int`

English:
theorem Algebra.coe_norm_int
  statement: (Algebra.norm Int x : Rat) = Algebra.norm Rat (x : K)
  proof: (Algebra.norm_localization (R := Int) (Rₘ := Rat) (S := 𝓞 K) (Sₘ := K) (nonZeroDivisors Int) x).symm

中文:
定理 Algebra.coe_norm_int
  结论: (Algebra.norm 整数 x : Rat) = Algebra.norm Rat (x : K)
  证明: (Algebra.norm_localization (R := Int) (Rₘ := Rat) (S := 𝓞 K) (Sₘ := K) (nonZeroDivisors Int) x).symm

Depends on / 依赖: Algebra, Algebra.norm_localization, nonZeroDivisors, norm_localization
-/
theorem Algebra.coe_norm_int : (Algebra.norm Int x : Rat) = Algebra.norm Rat (x : K) :=
  (Algebra.norm_localization (R := Int) (Rₘ := Rat) (S := 𝓞 K) (Sₘ := K) (nonZeroDivisors Int) x).symm

/--
theorem `Algebra.coe_trace_int` / 定理 `Algebra.coe_trace_int`

English:
theorem Algebra.coe_trace_int
  statement: (Algebra.trace Int _ x : Rat) = Algebra.trace Rat K (x : K)
  proof: (Algebra.trace_localization (R := Int) (Rₘ := Rat) (S := 𝓞 K) (Sₘ := K) (nonZeroDivisors Int) x).symm

中文:
定理 Algebra.coe_trace_int
  结论: (Algebra.trace 整数 _ x : Rat) = Algebra.trace Rat K (x : K)
  证明: (Algebra.trace_localization (R := Int) (Rₘ := Rat) (S := 𝓞 K) (Sₘ := K) (nonZeroDivisors Int) x).symm

Depends on / 依赖: Algebra, Algebra.trace_localization, nonZeroDivisors, trace_localization
-/
theorem Algebra.coe_trace_int : (Algebra.trace Int _ x : Rat) = Algebra.trace Rat K (x : K) :=
  (Algebra.trace_localization (R := Int) (Rₘ := Rat) (S := 𝓞 K) (Sₘ := K) (nonZeroDivisors Int) x).symm

end Rat

namespace RingOfIntegers

variable {L : Type*} (K : Type*) [Field K] [Field L] [Algebra K L]

/--
Definition of `norm` / `norm` 的定义

English:
definition norm
  signature: : 𝓞 L ->* 𝓞 K
  body: RingOfIntegers.restrict_monoidHom
    ((Algebra.norm K).comp (algebraMap (𝓞 L) L : (𝓞 L) ->* L))
    fun x => isIntegral_norm K x.2

中文:
定义 norm
  签名: : 𝓞 L ->* 𝓞 K
  定义体: RingOfIntegers.restrict_monoidHom
    ((Algebra.norm K).comp (algebraMap (𝓞 L) L : (𝓞 L) ->* L))
    fun x => isIntegral_norm K x.2

Depends on / 依赖: Algebra, Algebra.norm, RingOfIntegers, RingOfIntegers.restrict_monoidHom, algebraMap, isIntegral_norm, restrict_monoidHom
-/
noncomputable def norm : 𝓞 L ->* 𝓞 K :=
  RingOfIntegers.restrict_monoidHom
    ((Algebra.norm K).comp (algebraMap (𝓞 L) L : (𝓞 L) ->* L))
    fun x => isIntegral_norm K x.2

/--
lemma `coe_norm` / 引理 `coe_norm`

English:
lemma coe_norm
  given: (x : 𝓞 L)
  statement: norm K x = Algebra.norm K (x : L)
  proof: rfl

中文:
引理 coe_norm
  条件: (x : 𝓞 L)
  结论: norm K x = Algebra.norm K (x : L)
  证明: rfl
-/
@[simp] lemma coe_norm (x : 𝓞 L) : norm K x = Algebra.norm K (x : L) :=
  rfl

/--
theorem `coe_algebraMap_norm` / 定理 `coe_algebraMap_norm`

English:
theorem coe_algebraMap_norm
  given: (x : 𝓞 L)
  proof: rfl

中文:
定理 coe_algebraMap_norm
  条件: (x : 𝓞 L)
  证明: rfl
-/
theorem coe_algebraMap_norm (x : 𝓞 L) :
    (algebraMap (𝓞 K) (𝓞 L) (norm K x) : L) = algebraMap K L (Algebra.norm K (x : L)) :=
  rfl

/--
theorem `algebraMap_norm_algebraMap` / 定理 `algebraMap_norm_algebraMap`

English:
theorem algebraMap_norm_algebraMap
  given: (x : 𝓞 K)
  proof: rfl

中文:
定理 algebraMap_norm_algebraMap
  条件: (x : 𝓞 K)
  证明: rfl
-/
theorem algebraMap_norm_algebraMap (x : 𝓞 K) :
    algebraMap _ K (norm K (algebraMap (𝓞 K) (𝓞 L) x)) =
      Algebra.norm K (algebraMap K L (algebraMap _ _ x)) :=
  rfl

/--
theorem `norm_algebraMap` / 定理 `norm_algebraMap`

English:
theorem norm_algebraMap
  given: (x : 𝓞 K)
  statement: norm K (algebraMap (𝓞 K) (𝓞 L) x) = x ^ finrank K L
  proof: by
  rw [RingOfIntegers.ext_iff]; rw [RingOfIntegers.coe_eq_algebraMap]; rw [RingOfIntegers.algebraMap_norm_algebraMap]; rw [Algebra.norm_algebraMap]; rw [RingOfIntegers.coe_eq_algebraMap]; rw [map_pow]

中文:
定理 norm_algebraMap
  条件: (x : 𝓞 K)
  结论: norm K (algebraMap (𝓞 K) (𝓞 L) x) = x ^ finrank K L
  证明: by
  rw [RingOfIntegers.ext_iff]; rw [RingOfIntegers.coe_eq_algebraMap]; rw [RingOfIntegers.algebraMap_norm_algebraMap]; rw [Algebra.norm_algebraMap]; rw [RingOfIntegers.coe_eq_algebraMap]; rw [map_pow]

Depends on / 依赖: Algebra, Algebra.norm_algebraMap, RingOfIntegers, RingOfIntegers.algebraMap_norm_algebraMap, RingOfIntegers.coe_eq_algebraMap, RingOfIntegers.ext_iff, algebraMap_norm_algebraMap, coe_eq_algebraMap, ext_iff, map_pow, norm_algebraMap
-/
theorem norm_algebraMap (x : 𝓞 K) : norm K (algebraMap (𝓞 K) (𝓞 L) x) = x ^ finrank K L := by
  rw [RingOfIntegers.ext_iff]; rw [RingOfIntegers.coe_eq_algebraMap]; rw [RingOfIntegers.algebraMap_norm_algebraMap]; rw [Algebra.norm_algebraMap]; rw [RingOfIntegers.coe_eq_algebraMap]; rw [map_pow]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `dvd_norm` / 定理 `dvd_norm`

English:
theorem dvd_norm
  given: [FiniteDimensional K L] [IsGalois K L] (x : 𝓞 L)
  proof: by
  classical
  have hint :
    IsIntegral Int (∏ σ in univ.erase (AlgEquiv.refl : Gal(L/K)), σ x) :=
    IsIntegral.prod _ (fun σ _ =>
      ((RingOfIntegers.isIntegral_coe x).map σ))
  refine ⟨⟨_, hint⟩, ?_⟩
  ext
  rw [coe_algebraMap_norm K x]; rw [norm_eq_prod_automorphisms]
  simp [← Finset.mu

中文:
定理 dvd_norm
  条件: [FiniteDimensional K L] [IsGalois K L] (x : 𝓞 L)
  证明: by
  classical
  have hint :
    IsIntegral Int (∏ σ in univ.erase (AlgEquiv.refl : Gal(L/K)), σ x) :=
    IsIntegral.prod _ (fun σ _ =>
      ((RingOfIntegers.isIntegral_coe x).map σ))
  refine ⟨⟨_, hint⟩, ?_⟩
  ext
  rw [coe_algebraMap_norm K x]; rw [norm_eq_prod_automorphisms]
  simp [← Finset.mu

Depends on / 依赖: AlgEquiv, AlgEquiv.refl, Finset, Finset.mul_prod_erase, IsIntegral, IsIntegral.prod, RingOfIntegers, RingOfIntegers.isIntegral_coe, classical, coe_algebraMap_norm, isIntegral_coe, mem_univ, mul_prod_erase, norm_eq_prod_automorphisms, univ.erase
-/
theorem dvd_norm [FiniteDimensional K L] [IsGalois K L] (x : 𝓞 L) :
    x ∣ algebraMap (𝓞 K) (𝓞 L) (norm K x) := by
  classical
  have hint :
    IsIntegral Int (∏ σ in univ.erase (AlgEquiv.refl : Gal(L/K)), σ x) :=
    IsIntegral.prod _ (fun σ _ =>
      ((RingOfIntegers.isIntegral_coe x).map σ))
  refine ⟨⟨_, hint⟩, ?_⟩
  ext
  rw [coe_algebraMap_norm K x]; rw [norm_eq_prod_automorphisms]
  simp [← Finset.mul_prod_erase _ _ (mem_univ AlgEquiv.refl)]

/--
theorem `isUnit_norm_of_isGalois` / 定理 `isUnit_norm_of_isGalois`

English:
theorem isUnit_norm_of_isGalois
  given: [FiniteDimensional K L] [IsGalois K L] {x : 𝓞 L}
  proof: ⟨fun hx => isUnit_of_dvd_unit (dvd_norm K x) (hx.map _), IsUnit.map _⟩

中文:
定理 isUnit_norm_of_isGalois
  条件: [FiniteDimensional K L] [IsGalois K L] {x : 𝓞 L}
  证明: ⟨fun hx => isUnit_of_dvd_unit (dvd_norm K x) (hx.map _), IsUnit.map _⟩

Depends on / 依赖: IsUnit, IsUnit.map, dvd_norm, hx.map, isUnit_of_dvd_unit
-/
theorem isUnit_norm_of_isGalois [FiniteDimensional K L] [IsGalois K L] {x : 𝓞 L} :
    IsUnit (norm K x) ↔ IsUnit x :=
  ⟨fun hx => isUnit_of_dvd_unit (dvd_norm K x) (hx.map _), IsUnit.map _⟩

variable (F : Type*) [Field F] [Algebra K F] [FiniteDimensional K F]

/--
theorem `norm_norm` / 定理 `norm_norm`

English:
theorem norm_norm
  given: [Algebra F L] [FiniteDimensional F L] [IsScalarTower K F L] (x : 𝓞 L)
  proof: by
  rw [RingOfIntegers.ext_iff]; rw [coe_norm]; rw [coe_norm]; rw [coe_norm]; rw [Algebra.norm_norm]

中文:
定理 norm_norm
  条件: [Algebra F L] [FiniteDimensional F L] [IsScalarTower K F L] (x : 𝓞 L)
  证明: by
  rw [RingOfIntegers.ext_iff]; rw [coe_norm]; rw [coe_norm]; rw [coe_norm]; rw [Algebra.norm_norm]

Depends on / 依赖: Algebra, Algebra.norm_norm, RingOfIntegers, RingOfIntegers.ext_iff, coe_norm, ext_iff, norm_norm
-/
theorem norm_norm [Algebra F L] [FiniteDimensional F L] [IsScalarTower K F L] (x : 𝓞 L) :
    norm K (norm F x) = norm K x := by
  rw [RingOfIntegers.ext_iff]; rw [coe_norm]; rw [coe_norm]; rw [coe_norm]; rw [Algebra.norm_norm]

variable {F}

/--
theorem `isUnit_norm` / 定理 `isUnit_norm`

English:
theorem isUnit_norm
  given: [CharZero K] {x : 𝓞 F}
  statement: IsUnit (norm K x) ↔ IsUnit x
  proof: by
  let : Algebra K (AlgebraicClosure K) := AlgebraicClosure.instAlgebra K
  let L := normalClosure K F (AlgebraicClosure F)
  have : FiniteDimensional F L := FiniteDimensional.right K F L
  have : IsGalois F L := IsGalois.tower_top_of_isGalois K F L
  calc
    IsUnit (norm K x) ↔ IsUnit ((norm K) 

中文:
定理 isUnit_norm
  条件: [CharZero K] {x : 𝓞 F}
  结论: IsUnit (norm K x) ↔ IsUnit x
  证明: by
  let : Algebra K (AlgebraicClosure K) := AlgebraicClosure.instAlgebra K
  let L := normalClosure K F (AlgebraicClosure F)
  have : FiniteDimensional F L := FiniteDimensional.right K F L
  have : IsGalois F L := IsGalois.tower_top_of_isGalois K F L
  calc
    IsUnit (norm K x) ↔ IsUnit ((norm K) 

Depends on / 依赖: Algebra, AlgebraicClosure, AlgebraicClosure.instAlgebra, FiniteDimensional, FiniteDimensional.right, IsGalois, IsGalois.tower_top_of_isGalois, IsUnit, algebraMap, finrank, finrank_pos, instAlgebra, isUnit_pow_iff, map_pow, norm_algebraMap, norm_norm, normalClosure, pos_iff_ne_zero, pos_iff_ne_zero.mp, tower_top_of_isGalois
-/
theorem isUnit_norm [CharZero K] {x : 𝓞 F} : IsUnit (norm K x) ↔ IsUnit x := by
  let : Algebra K (AlgebraicClosure K) := AlgebraicClosure.instAlgebra K
  let L := normalClosure K F (AlgebraicClosure F)
  have : FiniteDimensional F L := FiniteDimensional.right K F L
  have : IsGalois F L := IsGalois.tower_top_of_isGalois K F L
  calc
    IsUnit (norm K x) ↔ IsUnit ((norm K) x ^ finrank F L) :=
      (isUnit_pow_iff (pos_iff_ne_zero.mp finrank_pos)).symm
    _ ↔ IsUnit (norm K (algebraMap (𝓞 F) (𝓞 L) x)) := by
      rw [← norm_norm K F (algebraMap (𝓞 F) (𝓞 L) x)]; rw [norm_algebraMap F _]; rw [map_pow]
    _ ↔ IsUnit (algebraMap (𝓞 F) (𝓞 L) x) := isUnit_norm_of_isGalois K
    _ ↔ IsUnit (norm F (algebraMap (𝓞 F) (𝓞 L) x)) := (isUnit_norm_of_isGalois F).symm
    _ ↔ IsUnit (x ^ finrank F L) := (congr_arg IsUnit (norm_algebraMap F _)).to_iff
    _ ↔ IsUnit x := isUnit_pow_iff (pos_iff_ne_zero.mp finrank_pos)

end RingOfIntegers
