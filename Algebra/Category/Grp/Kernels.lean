/-
Copyright (c) 2023 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata, Moritz Firsching, Nikolas Kuhn
-/
module

public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# The concrete (co)kernels in the category of abelian groups are categorical (co)kernels.
-/

@[expose] public section

namespace AddCommGrpCat

open AddMonoidHom CategoryTheory Limits QuotientAddGroup

universe u

variable {G H : AddCommGrpCat.{u}} (f : G ⟶ H)

/--
Definition of `kernelCone` / `kernelCone` 的定义

English:
definition kernelCone
  signature: : KernelFork f
  body: KernelFork.ofι (Z := of f.hom.ker) (ofHom f.hom.ker.subtype) ext fun x =>
    x.casesOn fun _ hx => hx

中文:
定义 kernelCone
  签名: : KernelFork f
  定义体: KernelFork.ofι (Z := of f.hom.ker) (ofHom f.hom.ker.subtype) ext fun x =>
    x.casesOn fun _ hx => hx

Depends on / 依赖: KernelFork, KernelFork.of, casesOn, f.hom.ker, f.hom.ker.subtype, subtype, x.casesOn
-/
def kernelCone : KernelFork f :=
KernelFork.ofι (Z := of f.hom.ker) (ofHom f.hom.ker.subtype) ext fun x =>
    x.casesOn fun _ hx => hx

/--
Definition of `kernelIsLimit` / `kernelIsLimit` 的定义

English:
definition kernelIsLimit
  signature: : IsLimit kernelCone f
  body: Fork.IsLimit.mk _
    (fun s => ofHom <| s.ι.hom.codRestrict _ fun c => mem_ker.mpr <|
      ConcreteCategory.congr_hom s.condition c)
    (fun _ => by rfl)
    (fun _ _ h => ext fun x => Subtype.ext_iff.mpr <| ConcreteCategory.congr_hom h x)

中文:
定义 kernelIsLimit
  签名: : IsLimit kernelCone f
  定义体: Fork.IsLimit.mk _
    (fun s => ofHom <| s.ι.hom.codRestrict _ fun c => mem_ker.mpr <|
      ConcreteCategory.congr_hom s.condition c)
    (fun _ => by rfl)
    (fun _ _ h => ext fun x => Subtype.ext_iff.mpr <| ConcreteCategory.congr_hom h x)

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, Fork.IsLimit.mk, IsLimit, Subtype, Subtype.ext_iff.mpr, codRestrict, condition, congr_hom, ext_iff, hom.codRestrict, mem_ker, mem_ker.mpr, s.condition
-/
def kernelIsLimit : IsLimit kernelCone f :=
  Fork.IsLimit.mk _
    (fun s => ofHom <| s.ι.hom.codRestrict _ fun c => mem_ker.mpr <|
      ConcreteCategory.congr_hom s.condition c)
    (fun _ => by rfl)
    (fun _ _ h => ext fun x => Subtype.ext_iff.mpr <| ConcreteCategory.congr_hom h x)

/--
Definition of `cokernelCocone` / `cokernelCocone` 的定义

English:
definition cokernelCocone
  signature: : CokernelCofork f
  body: CokernelCofork.ofπ (Z := of <| H ⧸ f.hom.range) (ofHom (mk' f.hom.range)) ext fun x =>
    (eq_zero_iff _).mpr ⟨x, rfl⟩

中文:
定义 cokernelCocone
  签名: : CokernelCofork f
  定义体: CokernelCofork.ofπ (Z := of <| H ⧸ f.hom.range) (ofHom (mk' f.hom.range)) ext fun x =>
    (eq_zero_iff _).mpr ⟨x, rfl⟩

Depends on / 依赖: CokernelCofork, CokernelCofork.of, eq_zero_iff, f.hom.range
-/
def cokernelCocone : CokernelCofork f :=
CokernelCofork.ofπ (Z := of <| H ⧸ f.hom.range) (ofHom (mk' f.hom.range)) ext fun x =>
    (eq_zero_iff _).mpr ⟨x, rfl⟩

/--
Definition of `cokernelIsColimit` / `cokernelIsColimit` 的定义

English:
definition cokernelIsColimit
  signature: : IsColimit cokernelCocone f
  body: Cofork.IsColimit.mk _
    (fun s => ofHom <| lift _ _ <| (range_le_ker_iff _ _).mpr <|
      congr_arg Hom.hom (CokernelCofork.condition s))
    (fun _ => rfl)
    (fun _ _ h => have : Epi (cokernelCocone f).π := (epi_iff_surjective _).mpr <| mk'_surjective _
(cancel_epi (cokernelCocone f).π).mp by 

中文:
定义 cokernelIsColimit
  签名: : IsColimit cokernelCocone f
  定义体: Cofork.IsColimit.mk _
    (fun s => ofHom <| lift _ _ <| (range_le_ker_iff _ _).mpr <|
      congr_arg Hom.hom (CokernelCofork.condition s))
    (fun _ => rfl)
    (fun _ _ h => have : Epi (cokernelCocone f).π := (epi_iff_surjective _).mpr <| mk'_surjective _
(cancel_epi (cokernelCocone f).π).mp by 

Depends on / 依赖: Cofork, Cofork.IsColimit.mk, CokernelCofork, CokernelCofork.condition, Hom.hom, IsColimit, _surjective, cancel_epi, cokernelCocone, condition, congr_arg, epi_iff_surjective, parallelPair_obj_one, range_le_ker_iff
-/
def cokernelIsColimit : IsColimit cokernelCocone f :=
  Cofork.IsColimit.mk _
    (fun s => ofHom <| lift _ _ <| (range_le_ker_iff _ _).mpr <|
      congr_arg Hom.hom (CokernelCofork.condition s))
    (fun _ => rfl)
    (fun _ _ h => have : Epi (cokernelCocone f).π := (epi_iff_surjective _).mpr <| mk'_surjective _
(cancel_epi (cokernelCocone f).π).mp by simpa only [parallelPair_obj_one] using! h)

end AddCommGrpCat
