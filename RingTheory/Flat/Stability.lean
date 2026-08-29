/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.Algebra.Module.LocalizedModule.Basic

/-!
# Flatness is stable under composition and base change

We show that flatness is stable under composition and base change.

## Main theorems

* `Module.Flat.trans`: if `S` is a flat `R`-algebra and `M` is a flat `S`-module,
                      then `M` is a flat `R`-module
* `Module.Flat.baseChange`: if `M` is a flat `R`-module and `S` is any `R`-algebra,
                            then `S ⊗[R] M` is `S`-flat.
* `Module.Flat.of_isLocalizedModule`: if `M` is a flat `R`-module and `S` is a submonoid of `R`
                                          then the localization of `M` at `S` is flat as a module
                                          for the localization of `R` at `S`.
-/

public section

universe u v w t t'

open Function (Injective Surjective)

open LinearMap (lsmul rTensor lTensor)

open TensorProduct

namespace Module.Flat

section Composition

/-! ### Composition

Let `R` be a ring, `S` a flat `R`-algebra and `M` a flat `S`-module. To show that `M` is flat
as an `R`-module, we show that the inclusion of an `R`-submodule `N` into an `R`-module `P`
tensored on the left with `M` is injective. For this consider the composition of natural maps

`M ⊗[R] N ≃ M ⊗[S] (S ⊗[R] N) → M ⊗[S] (S ⊗[R] P) ≃ M ⊗[R] P`;

`S ⊗[R] N → S ⊗[R] P` is injective by `R`-flatness of `S`,
so the middle map is injective by `S`-flatness of `M`.
-/

variable (R : Type u) (S : Type v) (M : Type w)
  [CommSemiring R] [CommSemiring S] [Algebra R S]
  [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M]

open AlgebraTensorModule in
/--
theorem `trans` / 定理 `trans`

English:
theorem trans
  given: [Flat R S] [Flat S M]
  statement: Flat R M
  proof: by
  rw [Flat.iff_lTensor_injectiveₛ]
  introv
  rw [← coe_lTensor (A := S)]; rw [← EquivLike.injective_comp (cancelBaseChange R S S _ _)]; rw [← LinearEquiv.coe_coe]; rw [← LinearMap.coe_comp]; rw [lTensor_comp_cancelBaseChange]; rw [LinearMap.coe_comp]; rw [LinearEquiv.coe_coe]; rw [EquivLike.comp

中文:
定理 trans
  条件: [Flat R S] [Flat S M]
  结论: Flat R M
  证明: by
  rw [Flat.iff_lTensor_injectiveₛ]
  introv
  rw [← coe_lTensor (A := S)]; rw [← EquivLike.injective_comp (cancelBaseChange R S S _ _)]; rw [← LinearEquiv.coe_coe]; rw [← LinearMap.coe_comp]; rw [lTensor_comp_cancelBaseChange]; rw [LinearMap.coe_comp]; rw [LinearEquiv.coe_coe]; rw [EquivLike.comp

Depends on / 依赖: EquivLike, EquivLike.comp_injective, EquivLike.injective_comp, Flat.iff_lTensor_injective, Flat.lTensor_preserves_injective_linearMap, LinearEquiv, LinearEquiv.coe_coe, LinearMap, LinearMap.coe_comp, Subtype, Subtype.val_injective, _of_ne_zero_right, cancelBaseChange, coe_coe, coe_comp, coe_lTensor, comp_injective, injective_comp, introv, iterate
-/
theorem trans [Flat R S] [Flat S M] : Flat R M := by
  rw [Flat.iff_lTensor_injectiveₛ]
  introv
  rw [← coe_lTensor (A := S)]; rw [← EquivLike.injective_comp (cancelBaseChange R S S _ _)]; rw [← LinearEquiv.coe_coe]; rw [← LinearMap.coe_comp]; rw [lTensor_comp_cancelBaseChange]; rw [LinearMap.coe_comp]; rw [LinearEquiv.coe_coe]; rw [EquivLike.comp_injective]
  iterate 2 apply Flat.lTensor_preserves_injective_linearMap
  exact Subtype.val_injective

variable {R M} in
@[simp]
/--
lemma `ulift_left_iff` / 引理 `ulift_left_iff`

English:
lemma ulift_left_iff
  statement: Flat (ULift.{t} R) M ↔ Flat R M
  proof: by
  refine ⟨fun h => .trans _ (ULift R) _, fun h => ?_⟩
  have : Module.Flat (ULift.{t} R) R := .of_ulift
  let _ := ULift.algebra'
  exact .trans _ R _

中文:
引理 ulift_left_iff
  结论: Flat (ULift.{t} R) M ↔ Flat R M
  证明: by
  refine ⟨fun h => .trans _ (ULift R) _, fun h => ?_⟩
  have : Module.Flat (ULift.{t} R) R := .of_ulift
  let _ := ULift.algebra'
  exact .trans _ R _

Depends on / 依赖: Module, Module.Flat, ULift.algebra, algebra, of_ulift
-/
lemma ulift_left_iff : Flat (ULift.{t} R) M ↔ Flat R M := by
  refine ⟨fun h => .trans _ (ULift R) _, fun h => ?_⟩
  have : Module.Flat (ULift.{t} R) R := .of_ulift
  let _ := ULift.algebra'
  exact .trans _ R _

variable {R M} in
@[simp]
/--
lemma `ulift_right_iff` / 引理 `ulift_right_iff`

English:
lemma ulift_right_iff
  statement: Flat R (ULift.{t} M) ↔ Flat R M
  proof: Flat.equiv_iff ULift.moduleEquiv

中文:
引理 ulift_right_iff
  结论: Flat R (ULift.{t} M) ↔ Flat R M
  证明: Flat.equiv_iff ULift.moduleEquiv

Depends on / 依赖: Flat.equiv_iff, ULift.moduleEquiv, equiv_iff, moduleEquiv
-/
lemma ulift_right_iff : Flat R (ULift.{t} M) ↔ Flat R M :=
  Flat.equiv_iff ULift.moduleEquiv

end Composition

section BaseChange

/-! ### Base change

Let `R` be a ring, `M` a flat `R`-module and `S` an `R`-algebra, then
`S ⊗[R] M` is a flat `S`-module. This is a special case of `Module.Flat.instTensorProduct`.

-/

variable (R : Type u) (S : Type v) (M : Type w)
  [CommSemiring R] [CommSemiring S] [Algebra R S]
  [AddCommMonoid M] [Module R M]

/--
Instance `baseChange` / 实例 `baseChange`

English:
instance baseChange
  signature: [Flat R M]
  body: inferInstance

中文:
实例 baseChange
  签名: [Flat R M]
  定义体: inferInstance
-/
instance baseChange [Flat R M] : Flat S (S otimes[R] M) := inferInstance

/--
theorem `isBaseChange` / 定理 `isBaseChange`

English:
theorem isBaseChange
  statement: [Flat R M] (N : Type t) [AddCommMonoid N] [Module R N] [Module S N]
  proof: of_linearEquiv (IsBaseChange.equiv h).symm

中文:
定理 isBaseChange
  结论: [Flat R M] (N : Type t) [AddCommMonoid N] [Module R N] [Module S N]
  证明: of_linearEquiv (IsBaseChange.equiv h).symm

Depends on / 依赖: IsBaseChange, IsBaseChange.equiv, of_linearEquiv
-/
theorem isBaseChange [Flat R M] (N : Type t) [AddCommMonoid N] [Module R N] [Module S N]
    [IsScalarTower R S N] {f : M ->ₗ[R] N} (h : IsBaseChange S f) :
    Flat S N :=
  of_linearEquiv (IsBaseChange.equiv h).symm

end BaseChange

section Localization

variable {R : Type u} {M Mp : Type*} (Rp : Type v)
  [CommSemiring R] [AddCommMonoid M] [Module R M] [CommSemiring Rp] [Algebra R Rp]
  [AddCommMonoid Mp] [Module R Mp] [Module Rp Mp] [IsScalarTower R Rp Mp]

/--
Instance `localizedModule` / 实例 `localizedModule`

English:
instance localizedModule
  signature: [Flat R M] (S : Submonoid R)
  body: by
  apply Flat.isBaseChange (R := R) (S := Localization S)
    (f := LocalizedModule.mkLinearMap S M)
  rw [← isLocalizedModule_iff_isBaseChange S]
  exact localizedModuleIsLocalizedModule S

中文:
实例 localizedModule
  签名: [Flat R M] (S : Submonoid R)
  定义体: by
  apply Flat.isBaseChange (R := R) (S := Localization S)
    (f := LocalizedModule.mkLinearMap S M)
  rw [← isLocalizedModule_iff_isBaseChange S]
  exact localizedModuleIsLocalizedModule S

Depends on / 依赖: Flat.isBaseChange, Localization, LocalizedModule, LocalizedModule.mkLinearMap, isBaseChange, isLocalizedModule_iff_isBaseChange, localizedModuleIsLocalizedModule, mkLinearMap
-/
instance localizedModule [Flat R M] (S : Submonoid R) :
    Flat (Localization S) (LocalizedModule S M) := by
  apply Flat.isBaseChange (R := R) (S := Localization S)
    (f := LocalizedModule.mkLinearMap S M)
  rw [← isLocalizedModule_iff_isBaseChange S]
  exact localizedModuleIsLocalizedModule S

/--
theorem `of_isLocalizedModule` / 定理 `of_isLocalizedModule`

English:
theorem of_isLocalizedModule
  statement: [Flat R M] (S : Submonoid R) [IsLocalization S Rp]
  proof: by
  fapply Flat.isBaseChange (R := R) (M := M) (S := Rp) (N := Mp)
  exact (isLocalizedModule_iff_isBaseChange S Rp f).mp h

中文:
定理 of_isLocalizedModule
  结论: [Flat R M] (S : Submonoid R) [IsLocalization S Rp]
  证明: by
  fapply Flat.isBaseChange (R := R) (M := M) (S := Rp) (N := Mp)
  exact (isLocalizedModule_iff_isBaseChange S Rp f).mp h

Depends on / 依赖: Flat.isBaseChange, fapply, isBaseChange, isLocalizedModule_iff_isBaseChange
-/
theorem of_isLocalizedModule [Flat R M] (S : Submonoid R) [IsLocalization S Rp]
    (f : M ->ₗ[R] Mp) [h : IsLocalizedModule S f] : Flat Rp Mp := by
  fapply Flat.isBaseChange (R := R) (M := M) (S := Rp) (N := Mp)
  exact (isLocalizedModule_iff_isBaseChange S Rp f).mp h

instance {A : Type*} [CommSemiring A] [Algebra R A] [Flat R A] (S : Submonoid R) :
    Flat (Localization S) (Localization (Algebra.algebraMapSubmonoid A S)) :=
  of_isLocalizedModule _ S (IsScalarTower.toAlgHom R A _).toLinearMap

end Localization

end Module.Flat
