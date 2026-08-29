/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.CategoryTheory.ConcreteCategory.Elementwise
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The concrete (co)kernels in the category of modules are (co)kernels in the categorical sense.
-/

@[expose] public section


open CategoryTheory CategoryTheory.Limits

universe u v

namespace ModuleCat

variable {R : Type u} [Ring R]

section

variable {M N P : ModuleCat.{v} R} (f : M ⟶ N)

/--
Definition of `kernelCone` / `kernelCone` 的定义

English:
definition kernelCone
  signature: : KernelFork f
  body: KernelFork.ofι (ofHom (LinearMap.ker f.hom).subtype) by aesop

中文:
定义 kernelCone
  签名: : KernelFork f
  定义体: KernelFork.ofι (ofHom (LinearMap.ker f.hom).subtype) by aesop

Depends on / 依赖: KernelFork, KernelFork.of, LinearMap, LinearMap.ker, f.hom, subtype
-/
def kernelCone : KernelFork f :=
KernelFork.ofι (ofHom (LinearMap.ker f.hom).subtype) by aesop

/--
Definition of `kernelIsLimit` / `kernelIsLimit` 的定义

English:
definition kernelIsLimit
  signature: : IsLimit (kernelCone f)
  body: Fork.IsLimit.mk _
    (fun s => ofHom <|
      LinearMap.codRestrict f.hom.ker (Fork.ι s).hom fun c =>
LinearMap.mem_ker.2 by simp [← ConcreteCategory.comp_apply])
    (fun _ => hom_ext <| LinearMap.subtype_comp_codRestrict _ _ _) fun s m h =>
hom_ext LinearMap.ext fun x => Subtype.ext_iff.2 (by sim

中文:
定义 kernelIsLimit
  签名: : IsLimit (kernelCone f)
  定义体: Fork.IsLimit.mk _
    (fun s => ofHom <|
      LinearMap.codRestrict f.hom.ker (Fork.ι s).hom fun c =>
LinearMap.mem_ker.2 by simp [← ConcreteCategory.comp_apply])
    (fun _ => hom_ext <| LinearMap.subtype_comp_codRestrict _ _ _) fun s m h =>
hom_ext LinearMap.ext fun x => Subtype.ext_iff.2 (by sim

Depends on / 依赖: ConcreteCategory, ConcreteCategory.comp_apply, Fork.IsLimit.mk, IsLimit, LinearMap, LinearMap.codRestrict, LinearMap.ext, LinearMap.mem_ker, LinearMap.subtype_comp_codRestrict, Subtype, Subtype.ext_iff, codRestrict, comp_apply, ext_iff, f.hom.ker, hom_ext, mem_ker, subtype_comp_codRestrict
-/
def kernelIsLimit : IsLimit (kernelCone f) :=
  Fork.IsLimit.mk _
    (fun s => ofHom <|
      LinearMap.codRestrict f.hom.ker (Fork.ι s).hom fun c =>
LinearMap.mem_ker.2 by simp [← ConcreteCategory.comp_apply])
    (fun _ => hom_ext <| LinearMap.subtype_comp_codRestrict _ _ _) fun s m h =>
hom_ext LinearMap.ext fun x => Subtype.ext_iff.2 (by simp [← h]; rfl)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Construct an `IsLimit` structure of kernels given `Function.Exact`. -/
noncomputable
/--
Definition of `isLimitKernelFork` / `isLimitKernelFork` 的定义

English:
definition isLimitKernelFork
  signature: (f : M ⟶ N) (g : N ⟶ P) (H : Function.Exact f.hom g.hom)
  body: by
refine IsLimit.ofIsoLimit (kernelIsLimit g)
    Cone.ext ((LinearEquiv.ofInjective _ H₂).trans
        (LinearEquiv.ofEq _ _ (LinearMap.exact_iff.mp H).symm)).toModuleIso.symm ?_
  · rintro ⟨⟩ <;> ext x <;> simp [kernelCone]

中文:
定义 isLimitKernelFork
  签名: (f : M ⟶ N) (g : N ⟶ P) (H : Function.Exact f.hom g.hom)
  定义体: by
refine IsLimit.ofIsoLimit (kernelIsLimit g)
    Cone.ext ((LinearEquiv.ofInjective _ H₂).trans
        (LinearEquiv.ofEq _ _ (LinearMap.exact_iff.mp H).symm)).toModuleIso.symm ?_
  · rintro ⟨⟩ <;> ext x <;> simp [kernelCone]

Depends on / 依赖: Cone.ext, H.apply_apply_eq_zero, IsLimit, IsLimit.ofIsoLimit, LinearEquiv, LinearEquiv.ofEq, LinearEquiv.ofInjective, LinearMap, LinearMap.exact_iff.mp, apply_apply_eq_zero, exact_iff, kernelCone, kernelIsLimit, ofInjective, ofIsoLimit, toModuleIso, toModuleIso.symm
-/
def isLimitKernelFork (f : M ⟶ N) (g : N ⟶ P) (H : Function.Exact f.hom g.hom)
    (H₂ : Function.Injective f.hom) :
    IsLimit (KernelFork.ofι (f := g) f (by ext; exact H.apply_apply_eq_zero _)) := by
refine IsLimit.ofIsoLimit (kernelIsLimit g)
    Cone.ext ((LinearEquiv.ofInjective _ H₂).trans
        (LinearEquiv.ofEq _ _ (LinearMap.exact_iff.mp H).symm)).toModuleIso.symm ?_
  · rintro ⟨⟩ <;> ext x <;> simp [kernelCone]

/--
Definition of `cokernelCocone` / `cokernelCocone` 的定义

English:
definition cokernelCocone
  signature: : CokernelCofork f
  body: CokernelCofork.ofπ (ofHom (LinearMap.range f.hom).mkQ) hom_ext LinearMap.range_mkQ_comp _

中文:
定义 cokernelCocone
  签名: : CokernelCofork f
  定义体: CokernelCofork.ofπ (ofHom (LinearMap.range f.hom).mkQ) hom_ext LinearMap.range_mkQ_comp _

Depends on / 依赖: CokernelCofork, CokernelCofork.of, LinearMap, LinearMap.range, LinearMap.range_mkQ_comp, f.hom, hom_ext, range_mkQ_comp
-/
def cokernelCocone : CokernelCofork f :=
CokernelCofork.ofπ (ofHom (LinearMap.range f.hom).mkQ) hom_ext LinearMap.range_mkQ_comp _

/--
Definition of `cokernelIsColimit` / `cokernelIsColimit` 的定义

English:
definition cokernelIsColimit
  signature: : IsColimit (cokernelCocone f)
  body: Cofork.IsColimit.mk _
    (fun s => ofHom <| (LinearMap.range f.hom).liftQ (Cofork.π s).hom <|
LinearMap.range_le_ker_iff.2 ModuleCat.hom_ext_iff.mp CokernelCofork.condition s)
    (fun s => hom_ext <| (LinearMap.range f.hom).liftQ_mkQ (Cofork.π s).hom _) fun s m h => by
    have : Epi (ofHom f.hom.

中文:
定义 cokernelIsColimit
  签名: : IsColimit (cokernelCocone f)
  定义体: Cofork.IsColimit.mk _
    (fun s => ofHom <| (LinearMap.range f.hom).liftQ (Cofork.π s).hom <|
LinearMap.range_le_ker_iff.2 ModuleCat.hom_ext_iff.mp CokernelCofork.condition s)
    (fun s => hom_ext <| (LinearMap.range f.hom).liftQ_mkQ (Cofork.π s).hom _) fun s m h => by
    have : Epi (ofHom f.hom.

Depends on / 依赖: Cofork, Cofork.IsColimit.mk, CokernelCofork, CokernelCofork.condition, IsColimit, LinearMap, LinearMap.range, LinearMap.range_le_ker_iff, ModuleCat, ModuleCat.hom_ext_iff.mp, Submodule, Submodule.range_mkQ, cancel_epi, condition, epi_iff_range_eq_top, f.hom, f.hom.range.mkQ, hom_ext, hom_ext_iff, liftQ_mkQ
-/
def cokernelIsColimit : IsColimit (cokernelCocone f) :=
  Cofork.IsColimit.mk _
    (fun s => ofHom <| (LinearMap.range f.hom).liftQ (Cofork.π s).hom <|
LinearMap.range_le_ker_iff.2 ModuleCat.hom_ext_iff.mp CokernelCofork.condition s)
    (fun s => hom_ext <| (LinearMap.range f.hom).liftQ_mkQ (Cofork.π s).hom _) fun s m h => by
    have : Epi (ofHom f.hom.range.mkQ) :=
      (epi_iff_range_eq_top _).mpr (Submodule.range_mkQ _)
    apply (cancel_epi (ofHom f.hom.range.mkQ)).1
    exact h

/-- Construct an `IsColimit` structure of cokernels given `Function.Exact`. -/
noncomputable
/--
Definition of `isColimitCokernelCofork` / `isColimitCokernelCofork` 的定义

English:
definition isColimitCokernelCofork
  signature: (f : M ⟶ N) (g : N ⟶ P) (H : Function.Exact f.hom g.hom)
  body: by
refine IsColimit.ofIsoColimit (ModuleCat.cokernelIsColimit f)
    Cocone.ext (((Submodule.quotEquivOfEq _ _ (LinearMap.exact_iff.mp H)).toModuleIso).symm
    ≪≫ ((LinearMap.quotKerEquivOfSurjective _ H₂).toModuleIso)) ?_
  · rintro ⟨⟩ <;> ext x
    · simpa using! (Function.Exact.apply_apply_eq_ze

中文:
定义 isColimitCokernelCofork
  签名: (f : M ⟶ N) (g : N ⟶ P) (H : Function.Exact f.hom g.hom)
  定义体: by
refine IsColimit.ofIsoColimit (ModuleCat.cokernelIsColimit f)
    Cocone.ext (((Submodule.quotEquivOfEq _ _ (LinearMap.exact_iff.mp H)).toModuleIso).symm
    ≪≫ ((LinearMap.quotKerEquivOfSurjective _ H₂).toModuleIso)) ?_
  · rintro ⟨⟩ <;> ext x
    · simpa using! (Function.Exact.apply_apply_eq_ze

Depends on / 依赖: Cocone, Cocone.ext, Function, Function.Exact.apply_apply_eq_zero, H.apply_apply_eq_zero, IsColimit, IsColimit.ofIsoColimit, LinearMap, LinearMap.exact_iff.mp, LinearMap.quotKerEquivOfSurjective, ModuleCat, ModuleCat.cokernelIsColimit, Submodule, Submodule.quotEquivOfEq, apply_apply_eq_zero, cokernelIsColimit, exact_iff, ofIsoColimit, quotEquivOfEq, quotKerEquivOfSurjective
-/
def isColimitCokernelCofork (f : M ⟶ N) (g : N ⟶ P) (H : Function.Exact f.hom g.hom)
    (H₂ : Function.Surjective g.hom) :
    IsColimit (CokernelCofork.ofπ (f := f) g (by ext; exact H.apply_apply_eq_zero _)) := by
refine IsColimit.ofIsoColimit (ModuleCat.cokernelIsColimit f)
    Cocone.ext (((Submodule.quotEquivOfEq _ _ (LinearMap.exact_iff.mp H)).toModuleIso).symm
    ≪≫ ((LinearMap.quotKerEquivOfSurjective _ H₂).toModuleIso)) ?_
  · rintro ⟨⟩ <;> ext x
    · simpa using! (Function.Exact.apply_apply_eq_zero H x).symm
    · rfl

end

/--
theorem `hasKernels_moduleCat` / 定理 `hasKernels_moduleCat`

English:
theorem hasKernels_moduleCat
  statement: HasKernels (ModuleCat R)
  proof: ⟨fun f => HasLimit.mk ⟨_, kernelIsLimit f⟩⟩

中文:
定理 hasKernels_moduleCat
  结论: HasKernels (ModuleCat R)
  证明: ⟨fun f => HasLimit.mk ⟨_, kernelIsLimit f⟩⟩

Depends on / 依赖: HasLimit, HasLimit.mk, kernelIsLimit
-/
theorem hasKernels_moduleCat : HasKernels (ModuleCat R) :=
  ⟨fun f => HasLimit.mk ⟨_, kernelIsLimit f⟩⟩

/--
theorem `hasCokernels_moduleCat` / 定理 `hasCokernels_moduleCat`

English:
theorem hasCokernels_moduleCat
  statement: HasCokernels (ModuleCat R)
  proof: ⟨fun f => HasColimit.mk ⟨_, cokernelIsColimit f⟩⟩

中文:
定理 hasCokernels_moduleCat
  结论: HasCokernels (ModuleCat R)
  证明: ⟨fun f => HasColimit.mk ⟨_, cokernelIsColimit f⟩⟩

Depends on / 依赖: HasColimit, HasColimit.mk, cokernelIsColimit
-/
theorem hasCokernels_moduleCat : HasCokernels (ModuleCat R) :=
  ⟨fun f => HasColimit.mk ⟨_, cokernelIsColimit f⟩⟩

open ModuleCat

attribute [local instance] hasKernels_moduleCat

attribute [local instance] hasCokernels_moduleCat

variable {G H : ModuleCat.{v} R} (f : G ⟶ H)

/--
Definition of `kernelIsoKer` / `kernelIsoKer` 的定义

English:
definition kernelIsoKer
  signature: {G H : ModuleCat.{v} R} (f : G ⟶ H)
  body: limit.isoLimitCone ⟨_, kernelIsLimit f⟩

中文:
定义 kernelIsoKer
  签名: {G H : ModuleCat.{v} R} (f : G ⟶ H)
  定义体: limit.isoLimitCone ⟨_, kernelIsLimit f⟩

Depends on / 依赖: isoLimitCone, kernelIsLimit, limit.isoLimitCone
-/
noncomputable def kernelIsoKer {G H : ModuleCat.{v} R} (f : G ⟶ H) :
    kernel f ≅ ModuleCat.of R f.hom.ker :=
  limit.isoLimitCone ⟨_, kernelIsLimit f⟩

-- We now show this isomorphism commutes with the inclusion of the kernel into the source.
@[simp, elementwise]
/--
theorem `kernelIsoKer_inv_kernel_ι` / 定理 `kernelIsoKer_inv_kernel_ι`

English:
theorem kernelIsoKer_inv_kernel_ι
  statement: (kernelIsoKer f).inv ≫ kernel.ι f = ofHom f.hom.ker.subtype
  proof: limit.isoLimitCone_inv_π _ _

@[simp, elementwise]

中文:
定理 kernelIsoKer_inv_kernel_ι
  结论: (kernelIsoKer f).inv ≫ kernel.ι f = ofHom f.hom.ker.subtype
  证明: limit.isoLimitCone_inv_π _ _

@[simp, elementwise]

Depends on / 依赖: limit.isoLimitCone_inv_
-/
theorem kernelIsoKer_inv_kernel_ι : (kernelIsoKer f).inv ≫ kernel.ι f = ofHom f.hom.ker.subtype :=
  limit.isoLimitCone_inv_π _ _

@[simp, elementwise]
/--
theorem `kernelIsoKer_hom_ker_subtype` / 定理 `kernelIsoKer_hom_ker_subtype`

English:
theorem kernelIsoKer_hom_ker_subtype
  proof: IsLimit.conePointUniqueUpToIso_inv_comp _ (limit.isLimit _) WalkingParallelPair.zero

中文:
定理 kernelIsoKer_hom_ker_subtype
  证明: IsLimit.conePointUniqueUpToIso_inv_comp _ (limit.isLimit _) WalkingParallelPair.zero

Depends on / 依赖: IsLimit, IsLimit.conePointUniqueUpToIso_inv_comp, WalkingParallelPair, WalkingParallelPair.zero, conePointUniqueUpToIso_inv_comp, isLimit, limit.isLimit
-/
theorem kernelIsoKer_hom_ker_subtype :
    (kernelIsoKer f).hom ≫ ofHom f.hom.ker.subtype = kernel.ι f :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ (limit.isLimit _) WalkingParallelPair.zero

/--
Definition of `cokernelIsoRangeQuotient` / `cokernelIsoRangeQuotient` 的定义

English:
definition cokernelIsoRangeQuotient
  signature: {G H : ModuleCat.{v} R} (f : G ⟶ H)
  body: colimit.isoColimitCocone ⟨_, cokernelIsColimit f⟩

中文:
定义 cokernelIsoRangeQuotient
  签名: {G H : ModuleCat.{v} R} (f : G ⟶ H)
  定义体: colimit.isoColimitCocone ⟨_, cokernelIsColimit f⟩

Depends on / 依赖: cokernelIsColimit, colimit, colimit.isoColimitCocone, isoColimitCocone
-/
noncomputable def cokernelIsoRangeQuotient {G H : ModuleCat.{v} R} (f : G ⟶ H) :
    cokernel f ≅ ModuleCat.of R (H ⧸ f.hom.range) :=
  colimit.isoColimitCocone ⟨_, cokernelIsColimit f⟩

-- We now show this isomorphism commutes with the projection of target to the cokernel.
@[simp, elementwise]
/--
theorem `cokernel_π_cokernelIsoRangeQuotient_hom` / 定理 `cokernel_π_cokernelIsoRangeQuotient_hom`

English:
theorem cokernel_π_cokernelIsoRangeQuotient_hom
  proof: colimit.isoColimitCocone_ι_hom _ _

@[simp, elementwise]

中文:
定理 cokernel_π_cokernelIsoRangeQuotient_hom
  证明: colimit.isoColimitCocone_ι_hom _ _

@[simp, elementwise]

Depends on / 依赖: colimit, colimit.isoColimitCocone_
-/
theorem cokernel_π_cokernelIsoRangeQuotient_hom :
    cokernel.π f ≫ (cokernelIsoRangeQuotient f).hom = ofHom (LinearMap.range f.hom).mkQ :=
  colimit.isoColimitCocone_ι_hom _ _

@[simp, elementwise]
/--
theorem `range_mkQ_cokernelIsoRangeQuotient_inv` / 定理 `range_mkQ_cokernelIsoRangeQuotient_inv`

English:
theorem range_mkQ_cokernelIsoRangeQuotient_inv
  proof: colimit.isoColimitCocone_ι_inv ⟨_, cokernelIsColimit f⟩ WalkingParallelPair.one

中文:
定理 range_mkQ_cokernelIsoRangeQuotient_inv
  证明: colimit.isoColimitCocone_ι_inv ⟨_, cokernelIsColimit f⟩ WalkingParallelPair.one

Depends on / 依赖: WalkingParallelPair, WalkingParallelPair.one, cokernelIsColimit, colimit, colimit.isoColimitCocone_
-/
theorem range_mkQ_cokernelIsoRangeQuotient_inv :
    ofHom (LinearMap.range f.hom).mkQ ≫ (cokernelIsoRangeQuotient f).inv = cokernel.π f :=
  colimit.isoColimitCocone_ι_inv ⟨_, cokernelIsColimit f⟩ WalkingParallelPair.one

/--
theorem `cokernel_π_ext` / 定理 `cokernel_π_ext`

English:
theorem cokernel_π_ext
  given: {M N : ModuleCat.{u} R} (f : M ⟶ N) {x y : N} (m : M) (w : x = y + f m)
  proof: by
  subst w
  simpa only [map_add, add_eq_left] using! cokernel.condition_apply f m

中文:
定理 cokernel_π_ext
  条件: {M N : ModuleCat.{u} R} (f : M ⟶ N) {x y : N} (m : M) (w : x = y + f m)
  证明: by
  subst w
  simpa only [map_add, add_eq_left] using! cokernel.condition_apply f m

Depends on / 依赖: add_eq_left, cokernel, cokernel.condition_apply, condition_apply, map_add
-/
theorem cokernel_π_ext {M N : ModuleCat.{u} R} (f : M ⟶ N) {x y : N} (m : M) (w : x = y + f m) :
    cokernel.π f x = cokernel.π f y := by
  subst w
  simpa only [map_add, add_eq_left] using! cokernel.condition_apply f m

end ModuleCat
