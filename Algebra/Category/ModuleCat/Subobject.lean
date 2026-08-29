/-
Copyright (c) 2021 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.CategoryTheory.Subobject.WellPowered
public import Mathlib.CategoryTheory.Subobject.Limits

/-!
# Subobjects in the category of `R`-modules

We construct an explicit order isomorphism between the categorical subobjects of an `R`-module `M`
and its submodules. This immediately implies that the category of `R`-modules is well-powered.

-/

@[expose] public section

open CategoryTheory Subobject Limits

universe v u

namespace ModuleCat

variable {R : Type u} [Ring R] (M : ModuleCat.{v} R)

/--
Definition of `subobjectModule` / `subobjectModule` 的定义

English:
definition subobjectModule
  signature: : Subobject M ≃o Submodule R M
  body: OrderIso.symm
    { invFun := fun S => LinearMap.range S.arrow.hom
      toFun := fun N => Subobject.mk (ofHom N.subtype)
      right_inv := fun S => Eq.symm (by
        fapply eq_mk_of_comm
        · apply LinearEquiv.toModuleIso
          apply LinearEquiv.ofBijective (LinearMap.codRestrict
            (LinearMap.range S.arrow.hom) S.arrow.hom _)
          constructor
          · simp [← LinearMap.ker_eq_bot, ker_eq_bot_of_mono]
          · rw [← LinearMap.range_eq_top, LinearMap.range_codRestrict,
              Submodule.comap_subtype_self]
            exact LinearMap.mem_range_self _
        · ext x
          rfl)
      left_inv := fun N => by
        convert!
          congr_arg LinearMap.range
            (ModuleCat.hom_ext_iff.mp (underlyingIso_arrow (ofHom N.subtype))) using 1
        · have :
            (underlyingIso (ofHom N.subtype)).inv =
              ofHom (underlyingIso (ofHom N.subtype)).symm.toLinearEquiv.toLinearMap := by
              ext x
              rfl
          rw [this]; rw [hom_comp]; rw [hom_ofHom]; rw [LinearEquiv.range_comp]
        · exact (Submodule.range_subtype _).symm
      map_rel_iff' := fun {S T} => by
        refine ⟨fun h => ?_, fun h => mk_le_mk_of_comm (↟(Submodule.inclusion h)) rfl⟩
        convert! LinearMap.range_comp_le_range (ofMkLEMk _ _ h).hom (ofHom T.subtype).hom
        · rw [← hom_comp, ofMkLEMk_comp]
          exact (Submodule.range_subtype _).symm
        · exact (Submodule.range_subtype _).symm }

中文:
定义 subobjectModule
  签名: : Subobject M ≃o 子模 R M
  定义体: OrderIso.symm
    { invFun := fun S => LinearMap.range S.arrow.hom
      toFun := fun N => Subobject.mk (ofHom N.subtype)
      right_inv := fun S => Eq.symm (by
        fapply eq_mk_of_comm
        · apply LinearEquiv.toModuleIso
          apply LinearEquiv.ofBijective (LinearMap.codRestrict
            (LinearMap.range S.arrow.hom) S.arrow.hom _)
          constructor
          · simp [← LinearMap.ker_eq_bot, ker_eq_bot_of_mono]
          · rw [← LinearMap.range_eq_top, LinearMap.range_codRestrict,
              Submodule.comap_subtype_self]
            exact LinearMap.mem_range_self _
        · ext x
          rfl)
      left_inv := fun N => by
        convert!
          congr_arg LinearMap.range
            (ModuleCat.hom_ext_iff.mp (underlyingIso_arrow (ofHom N.subtype))) using 1
        · have :
            (underlyingIso (ofHom N.subtype)).inv =
              ofHom (underlyingIso (ofHom N.subtype)).symm.toLinearEquiv.toLinearMap := by
              ext x
              rfl
          rw [this]; rw [hom_comp]; rw [hom_ofHom]; rw [LinearEquiv.range_comp]
        · exact (Submodule.range_subtype _).symm
      map_rel_iff' := fun {S T} => by
        refine ⟨fun h => ?_, fun h => mk_le_mk_of_comm (↟(Submodule.inclusion h)) rfl⟩
        convert! LinearMap.range_comp_le_range (ofMkLEMk _ _ h).hom (ofHom T.subtype).hom
        · rw [← hom_comp, ofMkLEMk_comp]
          exact (Submodule.range_subtype _).symm
        · exact (Submodule.range_subtype _).symm }

Depends on / 依赖: Eq.symm, LinearEquiv, LinearEquiv.ofBijective, LinearEquiv.toModuleIso, LinearMap, LinearMap.codRestrict, LinearMap.ker_eq_bot, LinearMap.mem_range_self, LinearMap.range, LinearMap.range_codRestrict, LinearMap.range_eq_top, N.subtype, OrderIso, OrderIso.symm, S.arrow.hom, Submodule, Submodule.comap_subtype_self, Subobject, Subobject.mk, codRestrict
-/
noncomputable def subobjectModule : Subobject M ≃o Submodule R M :=
  OrderIso.symm
    { invFun := fun S => LinearMap.range S.arrow.hom
      toFun := fun N => Subobject.mk (ofHom N.subtype)
      right_inv := fun S => Eq.symm (by
        fapply eq_mk_of_comm
        · apply LinearEquiv.toModuleIso
          apply LinearEquiv.ofBijective (LinearMap.codRestrict
            (LinearMap.range S.arrow.hom) S.arrow.hom _)
          constructor
          · simp [← LinearMap.ker_eq_bot, ker_eq_bot_of_mono]
          · rw [← LinearMap.range_eq_top, LinearMap.range_codRestrict,
              Submodule.comap_subtype_self]
            exact LinearMap.mem_range_self _
        · ext x
          rfl)
      left_inv := fun N => by
        convert!
          congr_arg LinearMap.range
            (ModuleCat.hom_ext_iff.mp (underlyingIso_arrow (ofHom N.subtype))) using 1
        · have :
            (underlyingIso (ofHom N.subtype)).inv =
              ofHom (underlyingIso (ofHom N.subtype)).symm.toLinearEquiv.toLinearMap := by
              ext x
              rfl
          rw [this]; rw [hom_comp]; rw [hom_ofHom]; rw [LinearEquiv.range_comp]
        · exact (Submodule.range_subtype _).symm
      map_rel_iff' := fun {S T} => by
        refine ⟨fun h => ?_, fun h => mk_le_mk_of_comm (↟(Submodule.inclusion h)) rfl⟩
        convert! LinearMap.range_comp_le_range (ofMkLEMk _ _ h).hom (ofHom T.subtype).hom
        · rw [← hom_comp, ofMkLEMk_comp]
          exact (Submodule.range_subtype _).symm
        · exact (Submodule.range_subtype _).symm }

/--
Instance `wellPowered_moduleCat` / 实例 `wellPowered_moduleCat`

English:
instance wellPowered_moduleCat
  signature: : WellPowered.{v} (ModuleCat.{v} R)
  body: ⟨fun M => ⟨⟨_, ⟨(subobjectModule M).toEquiv⟩⟩⟩⟩

中文:
实例 wellPowered_moduleCat
  签名: : 良幂.{v} (模范畴.{v} R)
  定义体: ⟨fun M => ⟨⟨_, ⟨(subobjectModule M).toEquiv⟩⟩⟩⟩

Depends on / 依赖: subobjectModule, toEquiv
-/
instance wellPowered_moduleCat : WellPowered.{v} (ModuleCat.{v} R) :=
  ⟨fun M => ⟨⟨_, ⟨(subobjectModule M).toEquiv⟩⟩⟩⟩

attribute [local instance] hasKernels_moduleCat

/--
Definition of `toKernelSubobject` / `toKernelSubobject` 的定义

English:
definition toKernelSubobject
  signature: {M N : ModuleCat.{v} R} {f : M ⟶ N}
  body: (kernelSubobjectIso f ≪≫ ModuleCat.kernelIsoKer f).inv.hom

@[simp]

中文:
定义 toKernelSubobject
  签名: {M N : 模范畴.{v} R} {f : M ⟶ N}
  定义体: (kernelSubobjectIso f ≪≫ ModuleCat.kernelIsoKer f).inv.hom

@[simp]

Depends on / 依赖: ModuleCat, ModuleCat.kernelIsoKer, inv.hom, kernelIsoKer, kernelSubobjectIso
-/
noncomputable def toKernelSubobject {M N : ModuleCat.{v} R} {f : M ⟶ N} :
    LinearMap.ker f.hom ->ₗ[R] kernelSubobject f :=
  (kernelSubobjectIso f ≪≫ ModuleCat.kernelIsoKer f).inv.hom

@[simp]
/--
theorem `toKernelSubobject_arrow` / 定理 `toKernelSubobject_arrow`

English:
theorem toKernelSubobject_arrow
  given: {M N : ModuleCat R} {f : M ⟶ N} (x : LinearMap.ker f.hom)
  proof: by
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/10959): the whole proof was just `simp [toKernelSubobject]`.
  simp [toKernelSubobject, -hom_comp, ← CategoryTheory.comp_apply]

中文:
定理 toKernelSubobject_arrow
  条件: {M N : 模范畴 R} {f : M ⟶ N} (x : 线性映射.ker f.hom)
  证明: by
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/10959): the whole proof was just `simp [toKernelSubobject]`.
  simp [toKernelSubobject, -hom_comp, ← CategoryTheory.comp_apply]
-/
theorem toKernelSubobject_arrow {M N : ModuleCat R} {f : M ⟶ N} (x : LinearMap.ker f.hom) :
    (kernelSubobject f).arrow (toKernelSubobject x) = x.1 := by
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/10959): the whole proof was just `simp [toKernelSubobject]`.
  simp [toKernelSubobject, -hom_comp, ← CategoryTheory.comp_apply]

/--
theorem `cokernel_π_imageSubobject_ext` / 定理 `cokernel_π_imageSubobject_ext`

English:
theorem cokernel_π_imageSubobject_ext
  statement: {L M N : ModuleCat.{v} R} (f : L ⟶ M) [HasImage f]
  proof: by
  subst w
  simp

中文:
定理 cokernel_π_imageSubobject_ext
  结论: {L M N : 模范畴.{v} R} (f : L ⟶ M) [有像 f]
  证明: by
  subst w
  simp
-/
theorem cokernel_π_imageSubobject_ext {L M N : ModuleCat.{v} R} (f : L ⟶ M) [HasImage f]
    (g : (imageSubobject f : ModuleCat.{v} R) ⟶ N) [HasCokernel g] {x y : N} (l : L)
    (w : x = y + g (factorThruImageSubobject f l)) : cokernel.π g x = cokernel.π g y := by
  subst w
  simp

end ModuleCat
