/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Properties

/-!
# Function field of integral schemes

We define the function field of an irreducible scheme as the stalk of the generic point.
This is a field when the scheme is integral.

## Main definition
* `AlgebraicGeometry.Scheme.functionField`: The function field of an integral scheme.
* `AlgebraicGeometry.Scheme.germToFunctionField`: The canonical map from a component into the
  function field. This map is injective.
-/

public section

-- Explicit universe annotations were used in this file to improve performance https://github.com/leanprover-community/mathlib4/issues/12737


universe u v

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits TopCat

namespace AlgebraicGeometry

variable (X : Scheme)

/--
Definition of `Scheme.functionField` / `Scheme.functionField` 的定义

English:
abbreviation Scheme.functionField
  signature: [IrreducibleSpace X]
  body: X.presheaf.stalk (genericPoint X)

中文:
缩写 Scheme.functionField
  签名: [IrreducibleSpace X]
  定义体: X.presheaf.stalk (genericPoint X)

Depends on / 依赖: X.presheaf.stalk, genericPoint, presheaf
-/
noncomputable abbrev Scheme.functionField [IrreducibleSpace X] : CommRingCat :=
  X.presheaf.stalk (genericPoint X)

/--
Definition of `Scheme.germToFunctionField` / `Scheme.germToFunctionField` 的定义

English:
abbreviation Scheme.germToFunctionField
  signature: [IrreducibleSpace X] (U : X.Opens)
  body: X.presheaf.germ U
    (genericPoint X)
      (((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using h))

中文:
缩写 Scheme.germToFunctionField
  签名: [IrreducibleSpace X] (U : X.Opens)
  定义体: X.presheaf.germ U
    (genericPoint X)
      (((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using h))

Depends on / 依赖: U.isOpen, X.presheaf.germ, genericPoint, genericPoint_spec, isOpen, mem_open_set_iff, presheaf
-/
noncomputable abbrev Scheme.germToFunctionField [IrreducibleSpace X] (U : X.Opens)
    [h : Nonempty U] : Γ(X, U) ⟶ X.functionField :=
  X.presheaf.germ U
    (genericPoint X)
      (((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using h))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IrreducibleSpace
  signature: X] (U
  body: (X.germToFunctionField U).hom.toAlgebra

中文:
实例 [IrreducibleSpace
  签名: X] (U
  定义体: (X.germToFunctionField U).hom.toAlgebra

Depends on / 依赖: X.germToFunctionField, germToFunctionField, hom.toAlgebra, toAlgebra
-/
noncomputable instance [IrreducibleSpace X] (U : X.Opens) [Nonempty U] :
    Algebra Γ(X, U) X.functionField :=
  (X.germToFunctionField U).hom.toAlgebra

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsIntegral
  signature: X] : Field X.functionField
  body: (isField_stalk_of_closure_mem_irreducibleComponents X _
    (by simp [irreducibleComponents_eq_singleton])).toField

中文:
实例 [IsIntegral
  签名: X] : Field X.functionField
  定义体: (isField_stalk_of_closure_mem_irreducibleComponents X _
    (by simp [irreducibleComponents_eq_singleton])).toField

Depends on / 依赖: irreducibleComponents_eq_singleton, isField_stalk_of_closure_mem_irreducibleComponents, toField
-/
noncomputable instance [IsIntegral X] : Field X.functionField :=
  (isField_stalk_of_closure_mem_irreducibleComponents X _
    (by simp [irreducibleComponents_eq_singleton])).toField

/--
theorem `germ_injective_of_isIntegral` / 定理 `germ_injective_of_isIntegral`

English:
theorem germ_injective_of_isIntegral
  given: [IsIntegral X] {U : X.Opens} (x : X) (hx : x in U)
  proof: by
  rw [injective_iff_map_eq_zero]
  intro y hy
  rw [← (X.presheaf.germ U x hx).hom.map_zero] at hy
  obtain ⟨W, hW, iU, iV, e⟩ := X.presheaf.germ_eq _ hx hx _ _ hy
  cases Subsingleton.elim iU iV
  have : Nonempty W := ⟨⟨_, hW⟩⟩
  exact map_injective_of_isIntegral X iU e

中文:
定理 germ_injective_of_isIntegral
  条件: [Is整数egral X] {U : X.Opens} (x : X) (hx : x in U)
  证明: by
  rw [injective_iff_map_eq_zero]
  intro y hy
  rw [← (X.presheaf.germ U x hx).hom.map_zero] at hy
  obtain ⟨W, hW, iU, iV, e⟩ := X.presheaf.germ_eq _ hx hx _ _ hy
  cases Subsingleton.elim iU iV
  have : Nonempty W := ⟨⟨_, hW⟩⟩
  exact map_injective_of_isIntegral X iU e

Depends on / 依赖: Nonempty, Subsingleton, Subsingleton.elim, X.presheaf.germ, X.presheaf.germ_eq, germ_eq, hom.map_zero, injective_iff_map_eq_zero, map_injective_of_isIntegral, map_zero, presheaf
-/
theorem germ_injective_of_isIntegral [IsIntegral X] {U : X.Opens} (x : X) (hx : x in U) :
    Function.Injective (X.presheaf.germ U x hx) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  rw [← (X.presheaf.germ U x hx).hom.map_zero] at hy
  obtain ⟨W, hW, iU, iV, e⟩ := X.presheaf.germ_eq _ hx hx _ _ hy
  cases Subsingleton.elim iU iV
  have : Nonempty W := ⟨⟨_, hW⟩⟩
  exact map_injective_of_isIntegral X iU e

/--
theorem `Scheme.germToFunctionField_injective` / 定理 `Scheme.germToFunctionField_injective`

English:
theorem Scheme.germToFunctionField_injective
  given: [IsIntegral X] (U : X.Opens) [Nonempty U]
  proof: germ_injective_of_isIntegral _ _ _

中文:
定理 Scheme.germToFunctionField_injective
  条件: [Is整数egral X] (U : X.Opens) [Nonempty U]
  证明: germ_injective_of_isIntegral _ _ _

Depends on / 依赖: germ_injective_of_isIntegral
-/
theorem Scheme.germToFunctionField_injective [IsIntegral X] (U : X.Opens) [Nonempty U] :
    Function.Injective (X.germToFunctionField U) :=
  germ_injective_of_isIntegral _ _ _

/--
theorem `genericPoint_eq_of_isOpenImmersion` / 定理 `genericPoint_eq_of_isOpenImmersion`

English:
theorem genericPoint_eq_of_isOpenImmersion
  statement: {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f]
  proof: by
  apply ((genericPoint_spec Y).eq _).symm
  convert! (genericPoint_spec X).image f.continuous
  symm
  rw [← Set.univ_subset_iff]
  convert! subset_closure_inter_of_isPreirreducible_of_isOpen _ f.isOpenEmbedding.isOpen_range _
  · rw [Set.univ_inter, Set.image_univ]
  · apply PreirreducibleSpace.

中文:
定理 genericPoint_eq_of_isOpenImmersion
  结论: {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f]
  证明: by
  apply ((genericPoint_spec Y).eq _).symm
  convert! (genericPoint_spec X).image f.continuous
  symm
  rw [← Set.univ_subset_iff]
  convert! subset_closure_inter_of_isPreirreducible_of_isOpen _ f.isOpenEmbedding.isOpen_range _
  · rw [Set.univ_inter, Set.image_univ]
  · apply PreirreducibleSpace.

Depends on / 依赖: PreirreducibleSpace, PreirreducibleSpace.isPreirreducible_univ, Set.image_univ, Set.mem_range_self, Set.univ_inter, Set.univ_subset_iff, continuous, convert, f.continuous, f.isOpenEmbedding.isOpen_range, genericPoint_spec, image_univ, isOpenEmbedding, isOpen_range, isPreirreducible_univ, mem_range_self, subset_closure_inter_of_isPreirreducible_of_isOpen, univ_inter, univ_subset_iff
-/
theorem genericPoint_eq_of_isOpenImmersion {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f]
    [hX : IrreducibleSpace X] [IrreducibleSpace Y] :
    f (genericPoint X) = genericPoint Y := by
  apply ((genericPoint_spec Y).eq _).symm
  convert! (genericPoint_spec X).image f.continuous
  symm
  rw [← Set.univ_subset_iff]
  convert! subset_closure_inter_of_isPreirreducible_of_isOpen _ f.isOpenEmbedding.isOpen_range _
  · rw [Set.univ_inter, Set.image_univ]
  · apply PreirreducibleSpace.isPreirreducible_univ (X := Y)
  · exact ⟨_, trivial, Set.mem_range_self hX.2.some⟩

/--
Instance `stalkFunctionFieldAlgebra` / 实例 `stalkFunctionFieldAlgebra`

English:
instance stalkFunctionFieldAlgebra
  signature: [IrreducibleSpace X] (x : X)
  body: by
  -- TODO: can we write this normally after the refactor finishes?
  apply RingHom.toAlgebra
  exact (X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial)).hom

中文:
实例 stalkFunctionFieldAlgebra
  签名: [IrreducibleSpace X] (x : X)
  定义体: by
  -- TODO: can we write this normally after the refactor finishes?
  apply RingHom.toAlgebra
  exact (X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial)).hom
-/
noncomputable instance stalkFunctionFieldAlgebra [IrreducibleSpace X] (x : X) :
    Algebra (X.presheaf.stalk x) X.functionField := by
  -- TODO: can we write this normally after the refactor finishes?
  apply RingHom.toAlgebra
  exact (X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial)).hom

/--
Instance `functionField_isScalarTower` / 实例 `functionField_isScalarTower`

English:
instance functionField_isScalarTower
  signature: [IrreducibleSpace X] (U : X.Opens) (x : U)
  body: by
  apply IsScalarTower.of_algebraMap_eq'
  simp_rw [RingHom.algebraMap_toAlgebra]
  change _ = (X.presheaf.germ U x x.2 ≫ _).hom
  rw [X.presheaf.germ_stalkSpecializes]

@[simp]

中文:
实例 functionField_isScalarTower
  签名: [IrreducibleSpace X] (U : X.Opens) (x : U)
  定义体: by
  apply IsScalarTower.of_algebraMap_eq'
  simp_rw [RingHom.algebraMap_toAlgebra]
  change _ = (X.presheaf.germ U x x.2 ≫ _).hom
  rw [X.presheaf.germ_stalkSpecializes]

@[simp]

Depends on / 依赖: IsScalarTower, IsScalarTower.of_algebraMap_eq, RingHom, RingHom.algebraMap_toAlgebra, X.presheaf.germ, X.presheaf.germ_stalkSpecializes, algebraMap_toAlgebra, germ_stalkSpecializes, of_algebraMap_eq, presheaf, simp_rw
-/
instance functionField_isScalarTower [IrreducibleSpace X] (U : X.Opens) (x : U)
    [Nonempty U] : IsScalarTower Γ(X, U) (X.presheaf.stalk x) X.functionField := by
  apply IsScalarTower.of_algebraMap_eq'
  simp_rw [RingHom.algebraMap_toAlgebra]
  change _ = (X.presheaf.germ U x x.2 ≫ _).hom
  rw [X.presheaf.germ_stalkSpecializes]

@[simp]
/--
lemma `Scheme.algebraMap_germ_eq_germToFunctionField` / 引理 `Scheme.algebraMap_germ_eq_germToFunctionField`

English:
lemma Scheme.algebraMap_germ_eq_germToFunctionField
  statement: [IrreducibleSpace X]
  proof: by
  simp [RingHom.algebraMap_toAlgebra, ← ConcreteCategory.comp_apply]

中文:
引理 Scheme.algebraMap_germ_eq_germToFunctionField
  结论: [IrreducibleSpace X]
  证明: by
  simp [RingHom.algebraMap_toAlgebra, ← ConcreteCategory.comp_apply]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.comp_apply, RingHom, RingHom.algebraMap_toAlgebra, algebraMap_toAlgebra, comp_apply
-/
lemma Scheme.algebraMap_germ_eq_germToFunctionField [IrreducibleSpace X]
    {U : X.Opens} [Nonempty U] {x : X} (hx : x in U) (f : Γ(X, U)) :
    algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ U x hx f) =
      X.germToFunctionField U f := by
  simp [RingHom.algebraMap_toAlgebra, ← ConcreteCategory.comp_apply]

noncomputable instance (R : CommRingCat.{u}) [IsDomain R] :
    Algebra R (Spec R).functionField :=
  -- TODO: can we write this normally after the refactor finishes?
RingHom.toAlgebra by apply CommRingCat.Hom.hom; apply StructureSheaf.toStalk

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `genericPoint_eq_bot_of_affine` / 定理 `genericPoint_eq_bot_of_affine`

English:
theorem genericPoint_eq_bot_of_affine
  given: (R : CommRingCat) [IsDomain R]
  proof: by
  apply (genericPoint_spec (Spec R)).eq
  rw [isGenericPoint_def]
  rw [← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]; rw [PrimeSpectrum.vanishingIdeal_singleton]
  rw [← PrimeSpectrum.zeroLocus_singleton_zero]
  rfl

中文:
定理 genericPoint_eq_bot_of_affine
  条件: (R : CommRingCat) [IsDomain R]
  证明: by
  apply (genericPoint_spec (Spec R)).eq
  rw [isGenericPoint_def]
  rw [← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]; rw [PrimeSpectrum.vanishingIdeal_singleton]
  rw [← PrimeSpectrum.zeroLocus_singleton_zero]
  rfl

Depends on / 依赖: PrimeSpectrum, PrimeSpectrum.vanishingIdeal_singleton, PrimeSpectrum.zeroLocus_singleton_zero, PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, genericPoint_spec, isGenericPoint_def, vanishingIdeal_singleton, zeroLocus_singleton_zero, zeroLocus_vanishingIdeal_eq_closure
-/
theorem genericPoint_eq_bot_of_affine (R : CommRingCat) [IsDomain R] :
    genericPoint (Spec R) = (⊥ : PrimeSpectrum R) := by
  apply (genericPoint_spec (Spec R)).eq
  rw [isGenericPoint_def]
  rw [← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]; rw [PrimeSpectrum.vanishingIdeal_singleton]
  rw [← PrimeSpectrum.zeroLocus_singleton_zero]
  rfl

/--
Instance `functionField_isFractionRing_of_affine` / 实例 `functionField_isFractionRing_of_affine`

English:
instance functionField_isFractionRing_of_affine
  signature: (R : CommRingCat.{u}) [IsDomain R]
  body: by
  convert! StructureSheaf.IsLocalization.to_stalk R (genericPoint (Spec R))
  delta IsFractionRing IsLocalization.AtPrime
  -- Porting note: `congr` does not work for `Iff`
  apply Eq.to_iff
  congr 1
  rw [genericPoint_eq_bot_of_affine]
  ext
  exact mem_nonZeroDivisors_iff_ne_zero

中文:
实例 functionField_isFractionRing_of_affine
  签名: (R : CommRingCat.{u}) [IsDomain R]
  定义体: by
  convert! StructureSheaf.IsLocalization.to_stalk R (genericPoint (Spec R))
  delta IsFractionRing IsLocalization.AtPrime
  -- Porting note: `congr` does not work for `Iff`
  apply Eq.to_iff
  congr 1
  rw [genericPoint_eq_bot_of_affine]
  ext
  exact mem_nonZeroDivisors_iff_ne_zero

Depends on / 依赖: AtPrime, IsFractionRing, IsLocalization, IsLocalization.AtPrime, StructureSheaf, StructureSheaf.IsLocalization.to_stalk, convert, genericPoint, to_stalk
-/
instance functionField_isFractionRing_of_affine (R : CommRingCat.{u}) [IsDomain R] :
    IsFractionRing R (Spec R).functionField := by
  convert! StructureSheaf.IsLocalization.to_stalk R (genericPoint (Spec R))
  delta IsFractionRing IsLocalization.AtPrime
  -- Porting note: `congr` does not work for `Iff`
  apply Eq.to_iff
  congr 1
  rw [genericPoint_eq_bot_of_affine]
  ext
  exact mem_nonZeroDivisors_iff_ne_zero

instance {X : Scheme} [IsIntegral X] {U : X.Opens} [Nonempty U] :
    IsIntegral U :=
  isIntegral_of_isOpenImmersion U.ι

set_option backward.isDefEq.respectTransparency false in
/--
theorem `IsAffineOpen.primeIdealOf_genericPoint` / 定理 `IsAffineOpen.primeIdealOf_genericPoint`

English:
theorem IsAffineOpen.primeIdealOf_genericPoint
  statement: {X : Scheme} [IsIntegral X] {U : X.Opens}
  proof: by
  delta IsAffineOpen.primeIdealOf
  convert!
    genericPoint_eq_of_isOpenImmersion
      (U.toScheme.isoSpec.hom ≫ Spec.map (X.presheaf.map (eqToHom U.isOpenEmbedding_obj_top).op))
        -- Porting note: this was `ext1`

  -- Porting note: this was `ext1`
  apply Subtype.ext
  exact (genericPo

中文:
定理 IsAffineOpen.primeIdealOf_genericPoint
  结论: {X : Scheme} [Is整数egral X] {U : X.Opens}
  证明: by
  delta IsAffineOpen.primeIdealOf
  convert!
    genericPoint_eq_of_isOpenImmersion
      (U.toScheme.isoSpec.hom ≫ Spec.map (X.presheaf.map (eqToHom U.isOpenEmbedding_obj_top).op))
        -- Porting note: this was `ext1`

  -- Porting note: this was `ext1`
  apply Subtype.ext
  exact (genericPo

Depends on / 依赖: IsAffineOpen, IsAffineOpen.primeIdealOf, Spec.map, U.isOpenEmbedding_obj_top, U.toScheme.isoSpec.hom, X.presheaf.map, convert, eqToHom, genericPoint_eq_of_isOpenImmersion, isOpenEmbedding_obj_top, isoSpec, presheaf, primeIdealOf, toScheme
-/
theorem IsAffineOpen.primeIdealOf_genericPoint {X : Scheme} [IsIntegral X] {U : X.Opens}
    (hU : IsAffineOpen U) [h : Nonempty U] :
    hU.primeIdealOf
        ⟨genericPoint X,
          ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using h)⟩ =
      genericPoint (Spec Γ(X, U)) := by
  delta IsAffineOpen.primeIdealOf
  convert!
    genericPoint_eq_of_isOpenImmersion
      (U.toScheme.isoSpec.hom ≫ Spec.map (X.presheaf.map (eqToHom U.isOpenEmbedding_obj_top).op))
        -- Porting note: this was `ext1`

  -- Porting note: this was `ext1`
  apply Subtype.ext
  exact (genericPoint_eq_of_isOpenImmersion U.ι).symm

/--
theorem `functionField_isFractionRing_of_isAffineOpen` / 定理 `functionField_isFractionRing_of_isAffineOpen`

English:
theorem functionField_isFractionRing_of_isAffineOpen
  statement: [IsIntegral X] (U : X.Opens)
  proof: by
  delta IsFractionRing Scheme.functionField
  convert!
    hU.isLocalization_stalk
      ⟨genericPoint X,
        (((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›))⟩
    using 1
  rw [hU.primeIdealOf_genericPoint]; rw [genericPoint_eq_bot_of_affine]
  ext; exact

中文:
定理 functionField_isFractionRing_of_isAffineOpen
  结论: [Is整数egral X] (U : X.Opens)
  证明: by
  delta IsFractionRing Scheme.functionField
  convert!
    hU.isLocalization_stalk
      ⟨genericPoint X,
        (((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›))⟩
    using 1
  rw [hU.primeIdealOf_genericPoint]; rw [genericPoint_eq_bot_of_affine]
  ext; exact

Depends on / 依赖: IsFractionRing, Nonempty, Scheme, Scheme.functionField, U.isOpen, convert, functionField, genericPoint, genericPoint_eq_bot_of_affine, genericPoint_spec, hU.isLocalization_stalk, hU.primeIdealOf_genericPoint, isLocalization_stalk, isOpen, mem_nonZeroDivisors_iff_ne_zero, mem_open_set_iff, primeIdealOf_genericPoint
-/
theorem functionField_isFractionRing_of_isAffineOpen [IsIntegral X] (U : X.Opens)
    (hU : IsAffineOpen U) [Nonempty U] :
    IsFractionRing Γ(X, U) X.functionField := by
  delta IsFractionRing Scheme.functionField
  convert!
    hU.isLocalization_stalk
      ⟨genericPoint X,
        (((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›))⟩
    using 1
  rw [hU.primeIdealOf_genericPoint]; rw [genericPoint_eq_bot_of_affine]
  ext; exact mem_nonZeroDivisors_iff_ne_zero

instance (x : X) : IsAffine (X.affineCover.X x) :=
  AlgebraicGeometry.isAffine_Spec _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsIntegral
  signature: X] (x
  body: let U : X.Opens := (X.affineCover.f ((X.affineCover.idx x))).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange (X.affineCover.f _)
  let x : U := ⟨x, X.affineCover.covers x⟩
  have : Nonempty U := ⟨x⟩
  let M := (hU.primeIdealOf x).asIdeal.primeCompl
  have := hU.isLocalization_stalk 

中文:
实例 [IsIntegral
  签名: X] (x
  定义体: let U : X.Opens := (X.affineCover.f ((X.affineCover.idx x))).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange (X.affineCover.f _)
  let x : U := ⟨x, X.affineCover.covers x⟩
  have : Nonempty U := ⟨x⟩
  let M := (hU.primeIdealOf x).asIdeal.primeCompl
  have := hU.isLocalization_stalk 

Depends on / 依赖: IsAffineOpen, Nonempty, X.Opens, X.affineCover.covers, X.affineCover.f, X.affineCover.idx, affineCover, asIdeal, asIdeal.primeCompl, covers, functionField_isFractionRing_of_isAffineOpen, hU.isLocalization_stalk, hU.primeIdealOf, isAffineOpen_opensRange, isLocalization_stalk, opensRange, primeCompl, primeIdealOf
-/
instance [IsIntegral X] (x : X) :
    IsFractionRing (X.presheaf.stalk x) X.functionField :=
  let U : X.Opens := (X.affineCover.f ((X.affineCover.idx x))).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange (X.affineCover.f _)
  let x : U := ⟨x, X.affineCover.covers x⟩
  have : Nonempty U := ⟨x⟩
  let M := (hU.primeIdealOf x).asIdeal.primeCompl
  have := hU.isLocalization_stalk x
  have := functionField_isFractionRing_of_isAffineOpen X U hU
  -- Porting note: the following two lines were not needed.
  let _hA := Presheaf.algebra_section_stalk X.presheaf x
  have := functionField_isScalarTower X U x
  .isFractionRing_of_isDomain_of_isLocalization M ↑(Presheaf.stalk X.presheaf x)
    (Scheme.functionField X)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsIntegral
  signature: X] {x
  body: Function.Injective.isDomain _ (IsFractionRing.injective (X.presheaf.stalk x) (X.functionField))

中文:
实例 [IsIntegral
  签名: X] {x
  定义体: Function.Injective.isDomain _ (IsFractionRing.injective (X.presheaf.stalk x) (X.functionField))

Depends on / 依赖: Function, Function.Injective.isDomain, Injective, IsFractionRing, IsFractionRing.injective, X.functionField, X.presheaf.stalk, functionField, injective, isDomain, presheaf
-/
instance [IsIntegral X] {x : X} : IsDomain (X.presheaf.stalk x) :=
  Function.Injective.isDomain _ (IsFractionRing.injective (X.presheaf.stalk x) (X.functionField))

/--
lemma `exists_isUnit_germ_eq` / 引理 `exists_isUnit_germ_eq`

English:
lemma exists_isUnit_germ_eq
  given: [IsIntegral X] (f : X.functionField) (hf : f != 0)
  proof: by
  obtain ⟨U, hU, g, hg⟩ := X.presheaf.exists_germ_eq f
  obtain ⟨_, ⟨A, hA, rfl⟩, hxA, hAU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hU U.isOpen
  have : Nonempty A := ⟨_, hxA⟩
  let gA : Γ(X, A) := X.presheaf.map (homOfLE hAU).op g
  have h_germ_gA : X.presheaf.germ A (genericPoint

中文:
引理 exists_isUnit_germ_eq
  条件: [Is整数egral X] (f : X.functionField) (hf : f != 0)
  证明: by
  obtain ⟨U, hU, g, hg⟩ := X.presheaf.exists_germ_eq f
  obtain ⟨_, ⟨A, hA, rfl⟩, hxA, hAU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hU U.isOpen
  have : Nonempty A := ⟨_, hxA⟩
  let gA : Γ(X, A) := X.presheaf.map (homOfLE hAU).op g
  have h_germ_gA : X.presheaf.germ A (genericPoint

Depends on / 依赖: Nonempty, Scheme, Scheme.mem_basicOpen, U.isOpen, X.basicOpen, X.isBasis_affineOpens.exists_subset_of_mem_open, X.presheaf.exists_germ_eq, X.presheaf.germ, X.presheaf.germ_res_apply, X.presheaf.map, basicOpen, exists_germ_eq, exists_subset_of_mem_open, genericPoint, germ_res_apply, h_germ_gA, homOfLE, isBasis_affineOpens, isOpen, mem_basicOpen
-/
lemma exists_isUnit_germ_eq [IsIntegral X] (f : X.functionField) (hf : f != 0) :
    exists U in X.affineOpens, exists f' : Γ(X, U), exists _ : Nonempty U,
      X.germToFunctionField U f' = f ∧ IsUnit f' := by
  obtain ⟨U, hU, g, hg⟩ := X.presheaf.exists_germ_eq f
  obtain ⟨_, ⟨A, hA, rfl⟩, hxA, hAU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hU U.isOpen
  have : Nonempty A := ⟨_, hxA⟩
  let gA : Γ(X, A) := X.presheaf.map (homOfLE hAU).op g
  have h_germ_gA : X.presheaf.germ A (genericPoint X) hxA gA = f := by
    simp only [← hg, ← X.presheaf.germ_res_apply (homOfLE hAU) (genericPoint X) hxA g, gA]
    rfl
  have hxV : genericPoint X in X.basicOpen gA := by
    rwa [Scheme.mem_basicOpen X gA (genericPoint X) hxA, h_germ_gA, isUnit_iff_ne_zero]
  have : Nonempty (X.basicOpen gA) := ⟨⟨_, hxV⟩⟩
  refine ⟨X.basicOpen gA, hA.basicOpen gA,
    X.presheaf.map (X.basicOpen_le gA).hom.op gA, ‹_›, ?_,
    X.toRingedSpace.isUnit_res_basicOpen gA⟩
  simpa using h_germ_gA

end AlgebraicGeometry
