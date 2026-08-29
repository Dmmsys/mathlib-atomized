/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Jujian Zhang
-/
module

public import Mathlib.Algebra.Module.CharacterModule
public import Mathlib.RingTheory.Flat.Basic

/-!
# Flat modules

`M` is flat if `· ⊗ M` preserves finite limits (equivalently, pullbacks, or equalizers).
If `R` is a ring, an `R`-module `M` is flat if and only if it is mono-flat, and to show
a module is flat, it suffices to check inclusions of finitely generated ideals into `R`.
See <https://stacks.math.columbia.edu/tag/00HD>.

## Main theorems

* `Module.Flat.iff_characterModule_injective`: `CharacterModule M` is an injective module iff
  `M` is flat.
* `Module.Flat.iff_lTensor_injective`, `Module.Flat.iff_rTensor_injective`,
  `Module.Flat.iff_lTensor_injective'`, `Module.Flat.iff_rTensor_injective'`:
  A module `M` over a ring `R` is flat iff for all (finitely generated) ideals `I` of `R`, the
  tensor product of the inclusion `I → R` and the identity `M → M` is injective.
-/

public section

universe u v

namespace Module.Flat

open Function (Surjective)

open LinearMap

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

/--
lemma `injective_characterModule_iff_rTensor_preserves_injective_linearMap` / 引理 `injective_characterModule_iff_rTensor_preserves_injective_linearMap`

English:
lemma injective_characterModule_iff_rTensor_preserves_injective_linearMap
  proof: by
  simp_rw [injective_iff, rTensor_injective_iff_lcomp_surjective, Surjective, DFunLike.ext_iff]; rfl

中文:
引理 injective_characterModule_iff_rTensor_preserves_injective_linearMap
  证明: by
  simp_rw [injective_iff, rTensor_injective_iff_lcomp_surjective, Surjective, DFunLike.ext_iff]; rfl

Depends on / 依赖: DFunLike, DFunLike.ext_iff, Surjective, ext_iff, injective_iff, rTensor_injective_iff_lcomp_surjective, simp_rw
-/
lemma injective_characterModule_iff_rTensor_preserves_injective_linearMap :
    Module.Injective R (CharacterModule M) ↔
    forall ⦃N N' : Type v⦄ [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N']
      (f : N ->ₗ[R] N'), Function.Injective f -> Function.Injective (f.rTensor M) := by
  simp_rw [injective_iff, rTensor_injective_iff_lcomp_surjective, Surjective, DFunLike.ext_iff]; rfl

/--
theorem `iff_characterModule_injective` / 定理 `iff_characterModule_injective`

English:
theorem iff_characterModule_injective
  given: [Small.{v} R]
  proof: by
  rw [injective_characterModule_iff_rTensor_preserves_injective_linearMap]; rw [iff_rTensor_preserves_injective_linearMap']

中文:
定理 iff_characterModule_injective
  条件: [Small.{v} R]
  证明: by
  rw [injective_characterModule_iff_rTensor_preserves_injective_linearMap]; rw [iff_rTensor_preserves_injective_linearMap']

Depends on / 依赖: iff_rTensor_preserves_injective_linearMap, injective_characterModule_iff_rTensor_preserves_injective_linearMap
-/
theorem iff_characterModule_injective [Small.{v} R] :
    Flat R M ↔ Module.Injective R (CharacterModule M) := by
  rw [injective_characterModule_iff_rTensor_preserves_injective_linearMap]; rw [iff_rTensor_preserves_injective_linearMap']

/--
theorem `iff_characterModule_baer` / 定理 `iff_characterModule_baer`

English:
theorem iff_characterModule_baer
  statement: Flat R M ↔ Baer R (CharacterModule M)
  proof: by
  rw [equiv_iff (N := ULift.{u} M) ULift.moduleEquiv.symm]; rw [iff_characterModule_injective]; rw [← Baer.iff_injective]; rw [Baer.congr (CharacterModule.congr ULift.moduleEquiv)]

中文:
定理 iff_characterModule_baer
  结论: 平坦 R M ↔ Baer R (CharacterModule M)
  证明: by
  rw [equiv_iff (N := ULift.{u} M) ULift.moduleEquiv.symm]; rw [iff_characterModule_injective]; rw [← Baer.iff_injective]; rw [Baer.congr (CharacterModule.congr ULift.moduleEquiv)]

Depends on / 依赖: Baer.congr, Baer.iff_injective, CharacterModule, CharacterModule.congr, ULift.moduleEquiv, ULift.moduleEquiv.symm, equiv_iff, iff_characterModule_injective, iff_injective, moduleEquiv
-/
theorem iff_characterModule_baer : Flat R M ↔ Baer R (CharacterModule M) := by
  rw [equiv_iff (N := ULift.{u} M) ULift.moduleEquiv.symm]; rw [iff_characterModule_injective]; rw [← Baer.iff_injective]; rw [Baer.congr (CharacterModule.congr ULift.moduleEquiv)]

/--
theorem `iff_rTensor_injective'` / 定理 `iff_rTensor_injective'`

English:
theorem iff_rTensor_injective'
  proof: by
  simp_rw [iff_characterModule_baer, Baer, rTensor_injective_iff_lcomp_surjective,
    Surjective, DFunLike.ext_iff, Subtype.forall, lcomp_apply, Submodule.subtype_apply]

中文:
定理 iff_rTensor_injective'
  证明: by
  simp_rw [iff_characterModule_baer, Baer, rTensor_injective_iff_lcomp_surjective,
    Surjective, DFunLike.ext_iff, Subtype.forall, lcomp_apply, Submodule.subtype_apply]

Depends on / 依赖: DFunLike, DFunLike.ext_iff, Submodule, Submodule.subtype_apply, Subtype, Subtype.forall, Surjective, ext_iff, iff_characterModule_baer, lcomp_apply, rTensor_injective_iff_lcomp_surjective, simp_rw, subtype_apply
-/
theorem iff_rTensor_injective' :
    Flat R M ↔ forall I : Ideal R, Function.Injective (rTensor M I.subtype) := by
  simp_rw [iff_characterModule_baer, Baer, rTensor_injective_iff_lcomp_surjective,
    Surjective, DFunLike.ext_iff, Subtype.forall, lcomp_apply, Submodule.subtype_apply]

/--
theorem `iff_lTensor_injective'` / 定理 `iff_lTensor_injective'`

English:
theorem iff_lTensor_injective'
  proof: by
  simpa [← comm_comp_rTensor_comp_comm_eq] using iff_rTensor_injective'

中文:
定理 iff_lTensor_injective'
  证明: by
  simpa [← comm_comp_rTensor_comp_comm_eq] using iff_rTensor_injective'

Depends on / 依赖: comm_comp_rTensor_comp_comm_eq, iff_rTensor_injective
-/
theorem iff_lTensor_injective' :
    Flat R M ↔ forall (I : Ideal R), Function.Injective (lTensor M I.subtype) := by
  simpa [← comm_comp_rTensor_comp_comm_eq] using iff_rTensor_injective'

/--
lemma `iff_rTensor_injective` / 引理 `iff_rTensor_injective`

English:
lemma iff_rTensor_injective
  proof: by
  refine iff_rTensor_injective'.trans ⟨fun h I _ => h I,
    fun h I => (injective_iff_map_eq_zero _).mpr fun x hx => ?_⟩
  obtain ⟨J, hfg, hle, y, rfl⟩ := Submodule.exists_fg_le_eq_rTensor_inclusion x
  rw [← rTensor_comp_apply] at hx
  rw [(injective_iff_map_eq_zero _).mp (h hfg) y hx]; rw [map

中文:
引理 iff_rTensor_injective
  证明: by
  refine iff_rTensor_injective'.trans ⟨fun h I _ => h I,
    fun h I => (injective_iff_map_eq_zero _).mpr fun x hx => ?_⟩
  obtain ⟨J, hfg, hle, y, rfl⟩ := Submodule.exists_fg_le_eq_rTensor_inclusion x
  rw [← rTensor_comp_apply] at hx
  rw [(injective_iff_map_eq_zero _).mp (h hfg) y hx]; rw [map

Depends on / 依赖: Submodule, Submodule.exists_fg_le_eq_rTensor_inclusion, exists_fg_le_eq_rTensor_inclusion, iff_rTensor_injective, injective_iff_map_eq_zero, map_zero, rTensor_comp_apply
-/
lemma iff_rTensor_injective :
    Flat R M ↔ forall ⦃I : Ideal R⦄, I.FG -> Function.Injective (I.subtype.rTensor M) := by
  refine iff_rTensor_injective'.trans ⟨fun h I _ => h I,
    fun h I => (injective_iff_map_eq_zero _).mpr fun x hx => ?_⟩
  obtain ⟨J, hfg, hle, y, rfl⟩ := Submodule.exists_fg_le_eq_rTensor_inclusion x
  rw [← rTensor_comp_apply] at hx
  rw [(injective_iff_map_eq_zero _).mp (h hfg) y hx]; rw [map_zero]

/--
theorem `iff_lTensor_injective` / 定理 `iff_lTensor_injective`

English:
theorem iff_lTensor_injective
  proof: by
  simpa [← comm_comp_rTensor_comp_comm_eq] using iff_rTensor_injective

中文:
定理 iff_lTensor_injective
  证明: by
  simpa [← comm_comp_rTensor_comp_comm_eq] using iff_rTensor_injective

Depends on / 依赖: comm_comp_rTensor_comp_comm_eq, iff_rTensor_injective
-/
theorem iff_lTensor_injective :
    Flat R M ↔ forall ⦃I : Ideal R⦄, I.FG -> Function.Injective (I.subtype.lTensor M) := by
  simpa [← comm_comp_rTensor_comp_comm_eq] using iff_rTensor_injective

/--
lemma `iff_lift_lsmul_comp_subtype_injective` / 引理 `iff_lift_lsmul_comp_subtype_injective`

English:
lemma iff_lift_lsmul_comp_subtype_injective
  statement: Flat R M ↔ forall ⦃I : Ideal R⦄, I.FG ->
  proof: by
  simp [iff_rTensor_injective, ← lid_comp_rTensor]

中文:
引理 iff_lift_lsmul_comp_subtype_injective
  结论: 平坦 R M ↔ 对任意 ⦃I : 理想 R⦄, I.FG ->
  证明: by
  simp [iff_rTensor_injective, ← lid_comp_rTensor]

Depends on / 依赖: iff_rTensor_injective, lid_comp_rTensor
-/
lemma iff_lift_lsmul_comp_subtype_injective : Flat R M ↔ forall ⦃I : Ideal R⦄, I.FG ->
    Function.Injective (TensorProduct.lift ((lsmul R M).comp I.subtype)) := by
  simp [iff_rTensor_injective, ← lid_comp_rTensor]

end Module.Flat
