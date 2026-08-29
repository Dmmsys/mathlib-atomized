/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.LocalProperties.Basic
public import Mathlib.RingTheory.TensorProduct.Finite

/-!

# The meta properties of finite ring homomorphisms.

## Main results

Let `R` be a commutative ring, `S` is an `R`-algebra, `M` be a submonoid of `R`.

* `finite_localizationPreserves` : If `S` is a finite `R`-algebra, then `S' = M⁻¹S` is a
  finite `R' = M⁻¹R`-algebra.
* `finite_ofLocalizationSpan` : `S` is a finite `R`-algebra if there exists
  a set `{ r }` that spans `R` such that `Sᵣ` is a finite `Rᵣ`-algebra.

-/

public section


namespace RingHom

open scoped TensorProduct

open TensorProduct Algebra.TensorProduct

/--
theorem `finite_stableUnderComposition` / 定理 `finite_stableUnderComposition`

English:
theorem finite_stableUnderComposition
  statement: StableUnderComposition @Finite
  proof: by
  introv R hf hg
  exact hg.comp hf

中文:
定理 finite_stableUnderComposition
  结论: StableUnderComposition @Finite
  证明: by
  introv R hf hg
  exact hg.comp hf

Depends on / 依赖: hg.comp, introv
-/
theorem finite_stableUnderComposition : StableUnderComposition @Finite := by
  introv R hf hg
  exact hg.comp hf

/--
theorem `finite_respectsIso` / 定理 `finite_respectsIso`

English:
theorem finite_respectsIso
  statement: RespectsIso @Finite
  proof: by
  apply finite_stableUnderComposition.respectsIso
  intros
  exact Finite.of_surjective _ (RingEquiv.toEquiv _).surjective

中文:
定理 finite_respectsIso
  结论: RespectsIso @Finite
  证明: by
  apply finite_stableUnderComposition.respectsIso
  intros
  exact Finite.of_surjective _ (RingEquiv.toEquiv _).surjective

Depends on / 依赖: Finite, Finite.of_surjective, RingEquiv, RingEquiv.toEquiv, finite_stableUnderComposition, finite_stableUnderComposition.respectsIso, intros, of_surjective, respectsIso, surjective, toEquiv
-/
theorem finite_respectsIso : RespectsIso @Finite := by
  apply finite_stableUnderComposition.respectsIso
  intros
  exact Finite.of_surjective _ (RingEquiv.toEquiv _).surjective

/--
lemma `finite_containsIdentities` / 引理 `finite_containsIdentities`

English:
lemma finite_containsIdentities
  statement: ContainsIdentities @Finite
  proof: Finite.id

中文:
引理 finite_containsIdentities
  结论: ContainsIdentities @Finite
  证明: Finite.id

Depends on / 依赖: Finite, Finite.id
-/
lemma finite_containsIdentities : ContainsIdentities @Finite := Finite.id

/--
theorem `finite_isStableUnderBaseChange` / 定理 `finite_isStableUnderBaseChange`

English:
theorem finite_isStableUnderBaseChange
  statement: IsStableUnderBaseChange @Finite
  proof: by
  refine IsStableUnderBaseChange.mk finite_respectsIso ?_
  simp only [finite_algebraMap]
  intros
  infer_instance

中文:
定理 finite_isStableUnderBaseChange
  结论: IsStableUnderBaseChange @Finite
  证明: by
  refine IsStableUnderBaseChange.mk finite_respectsIso ?_
  simp only [finite_algebraMap]
  intros
  infer_instance

Depends on / 依赖: IsStableUnderBaseChange, IsStableUnderBaseChange.mk, finite_algebraMap, finite_respectsIso, infer_instance, intros
-/
theorem finite_isStableUnderBaseChange : IsStableUnderBaseChange @Finite := by
  refine IsStableUnderBaseChange.mk finite_respectsIso ?_
  simp only [finite_algebraMap]
  intros
  infer_instance

end RingHom

open scoped Pointwise

universe u

variable {R S : Type*} [CommRing R] [CommRing S] (M : Submonoid R) (f : R ->+* S)
variable (R' S' : Type*) [CommRing R'] [CommRing S']
variable [Algebra R R'] [Algebra S S']

/--
theorem `RingHom.finite_localizationPreserves` / 定理 `RingHom.finite_localizationPreserves`

English:
theorem RingHom.finite_localizationPreserves
  statement: RingHom.LocalizationPreserves @RingHom.Finite
  proof: by
  introv R hf
  let := f.toAlgebra
  let := ((algebraMap S S').comp f).toAlgebra
  let f' : R' ->+* S' := IsLocalization.map S' f (Submonoid.le_comap_map M)
  let := f'.toAlgebra
  have : IsScalarTower R R' S' := IsScalarTower.of_algebraMap_eq'
    (IsLocalization.map_comp M.le_comap_map).symm
  

中文:
定理 RingHom.finite_localizationPreserves
  结论: RingHom.LocalizationPreserves @RingHom.Finite
  证明: by
  introv R hf
  let := f.toAlgebra
  let := ((algebraMap S S').comp f).toAlgebra
  let f' : R' ->+* S' := IsLocalization.map S' f (Submonoid.le_comap_map M)
  let := f'.toAlgebra
  have : IsScalarTower R R' S' := IsScalarTower.of_algebraMap_eq'
    (IsLocalization.map_comp M.le_comap_map).symm
  

Depends on / 依赖: Algebra, Algebra.algebraMapSubmonoid, Finite, IsLocalization, IsLocalization.map, IsLocalization.map_comp, IsScalarTower, IsScalarTower.of_algebraMap_eq, M.le_comap_map, Module, Module.Finite, RingHom, RingHom.algebraMap_toAlgebra, Submonoid, Submonoid.le_comap_map, algebraMap, algebraMapSubmonoid, algebraMap_toAlgebra, f.toAlgebra, introv
-/
theorem RingHom.finite_localizationPreserves : RingHom.LocalizationPreserves @RingHom.Finite := by
  introv R hf
  let := f.toAlgebra
  let := ((algebraMap S S').comp f).toAlgebra
  let f' : R' ->+* S' := IsLocalization.map S' f (Submonoid.le_comap_map M)
  let := f'.toAlgebra
  have : IsScalarTower R R' S' := IsScalarTower.of_algebraMap_eq'
    (IsLocalization.map_comp M.le_comap_map).symm
  have : IsScalarTower R S S' := IsScalarTower.of_algebraMap_eq' rfl
  have : IsLocalization (Algebra.algebraMapSubmonoid S M) S' := by
    rwa [Algebra.algebraMapSubmonoid, RingHom.algebraMap_toAlgebra]
  have : Module.Finite R S := hf
  exact .of_isLocalization R S M

/--
theorem `RingHom.localization_away_map_finite` / 定理 `RingHom.localization_away_map_finite`

English:
theorem RingHom.localization_away_map_finite
  statement: (R S R' S' : Type u) [CommRing R] [CommRing S]
  proof: finite_localizationPreserves.away f r _ _ hf

中文:
定理 RingHom.localization_away_map_finite
  结论: (R S R' S' : 类型u) [CommRing R] [CommRing S]
  证明: finite_localizationPreserves.away f r _ _ hf

Depends on / 依赖: finite_localizationPreserves, finite_localizationPreserves.away
-/
theorem RingHom.localization_away_map_finite (R S R' S' : Type u) [CommRing R] [CommRing S]
    [CommRing R'] [CommRing S'] [Algebra R R'] (f : R ->+* S) [Algebra S S']
    (r : R) [IsLocalization.Away r R']
    [IsLocalization.Away (f r) S'] (hf : f.Finite) : (IsLocalization.Away.map R' S' f r).Finite :=
  finite_localizationPreserves.away f r _ _ hf

/--
theorem `RingHom.finite_ofLocalizationSpan` / 定理 `RingHom.finite_ofLocalizationSpan`

English:
theorem RingHom.finite_ofLocalizationSpan
  statement: RingHom.OfLocalizationSpan @RingHom.Finite
  proof: by
  classical
  rw [RingHom.ofLocalizationSpan_iff_finite]
  introv R hs H
  -- We first setup the instances
  let := f.toAlgebra
  let := fun r : s => (Localization.awayMap f r).toAlgebra
  have (r : s) : IsLocalization ((Submonoid.powers (r : R)).map (algebraMap R S))
      (Localization.Away (f 

中文:
定理 RingHom.finite_ofLocalizationSpan
  结论: RingHom.OfLocalizationSpan @RingHom.Finite
  证明: by
  classical
  rw [RingHom.ofLocalizationSpan_iff_finite]
  introv R hs H
  -- We first setup the instances
  let := f.toAlgebra
  let := fun r : s => (Localization.awayMap f r).toAlgebra
  have (r : s) : IsLocalization ((Submonoid.powers (r : R)).map (algebraMap R S))
      (Localization.Away (f 

Depends on / 依赖: RingHom, RingHom.ofLocalizationSpan_iff_finite, classical, introv, ofLocalizationSpan_iff_finite
-/
theorem RingHom.finite_ofLocalizationSpan : RingHom.OfLocalizationSpan @RingHom.Finite := by
  classical
  rw [RingHom.ofLocalizationSpan_iff_finite]
  introv R hs H
  -- We first setup the instances
  let := f.toAlgebra
  let := fun r : s => (Localization.awayMap f r).toAlgebra
  have (r : s) : IsLocalization ((Submonoid.powers (r : R)).map (algebraMap R S))
      (Localization.Away (f r)) := by
    rw [Submonoid.map_powers]; exact Localization.isLocalization
  have : forall r : s, IsScalarTower R (Localization.Away (r : R)) (Localization.Away (f r)) :=
    fun r => IsScalarTower.of_algebraMap_eq'
      (IsLocalization.map_comp (Submonoid.powers (r : R)).le_comap_map).symm
  -- By the hypothesis, we may find a finite generating set for each `Sᵣ`. This set can then be
  -- lifted into `R` by multiplying a sufficiently large power of `r`. I claim that the union of
  -- these generates `S`.
  constructor
  replace H := fun r => (H r).1
  choose s₁ s₂ using H
  let sf := fun x : s => IsLocalization.finsetIntegerMultiple (Submonoid.powers (f x)) (s₁ x)
  use s.attach.biUnion sf
  rw [Submodule.span_attach_biUnion]; rw [eq_top_iff]
  -- It suffices to show that `r ^ n • x ∈ span T` for each `r : s`, since `{ r ^ n }` spans `R`.
  -- This then follows from the fact that each `x : R` is a linear combination of the generating set
  -- of `Sᵣ`. By multiplying a sufficiently large power of `r`, we can cancel out the `r`s in the
  -- denominators of both the generating set and the coefficients.
  rintro x -
  apply Submodule.mem_of_span_eq_top_of_smul_pow_mem _ (s : Set R) hs _ _
  intro r
  obtain ⟨⟨_, n₁, rfl⟩, hn₁⟩ :=
    multiple_mem_span_of_mem_localization_span (Submonoid.powers (r : R))
      (Localization.Away (r : R)) (s₁ r : Set (Localization.Away (f r))) (algebraMap S _ x)
      (by rw [s₂ r]; trivial)
  dsimp only at hn₁
  rw [Submonoid.smul_def]; rw [Algebra.smul_def]; rw [IsScalarTower.algebraMap_apply R S]; rw [← map_mul] at hn₁
  obtain ⟨⟨_, n₂, rfl⟩, hn₂⟩ :=
    IsLocalization.smul_mem_finsetIntegerMultiple_span (Submonoid.powers (r : R))
      (Localization.Away (f r)) _ (s₁ r) hn₁
  rw [Submonoid.smul_def]; rw [← Algebra.smul_def]; rw [smul_smul]; rw [← pow_add] at hn₂
  simp_rw [Submonoid.map_powers] at hn₂
  use n₂ + n₁
  exact le_iSup (fun x : s => Submodule.span R (sf x : Set S)) r hn₂
