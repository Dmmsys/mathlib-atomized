/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
module

public import Mathlib.Algebra.Module.Injective
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-!
# Injective objects in the category of $R$-modules
-/

public section

open CategoryTheory

universe u v
variable (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M]
namespace Module

/--
theorem `injective_object_of_injective_module` / 定理 `injective_object_of_injective_module`

English:
theorem injective_object_of_injective_module
  given: [inj : Injective R M]
  proof: have ⟨l, h⟩ := inj.out f.hom ((ModuleCat.mono_iff_injective f).mp m) g.hom
    ⟨ModuleCat.ofHom l, by ext x; simpa using h x⟩

中文:
定理 injective_object_of_injective_module
  条件: [inj : Injective R M]
  证明: have ⟨l, h⟩ := inj.out f.hom ((ModuleCat.mono_iff_injective f).mp m) g.hom
    ⟨ModuleCat.ofHom l, by ext x; simpa using h x⟩

Depends on / 依赖: ModuleCat, ModuleCat.mono_iff_injective, ModuleCat.ofHom, f.hom, g.hom, inj.out, mono_iff_injective
-/
theorem injective_object_of_injective_module [inj : Injective R M] :
    CategoryTheory.Injective (ModuleCat.of R M) where
  factors g f m :=
    have ⟨l, h⟩ := inj.out f.hom ((ModuleCat.mono_iff_injective f).mp m) g.hom
    ⟨ModuleCat.ofHom l, by ext x; simpa using h x⟩

/--
theorem `injective_module_of_injective_object` / 定理 `injective_module_of_injective_object`

English:
theorem injective_module_of_injective_object
  proof: by
    have : CategoryTheory.Mono (ModuleCat.ofHom f) := (ModuleCat.mono_iff_injective _).mpr hf
    obtain ⟨l, h⟩ := inj.factors (ModuleCat.ofHom g) (ModuleCat.ofHom f)
    obtain rfl := ModuleCat.hom_ext_iff.mp h
    exact ⟨l.hom, fun _ => rfl⟩

中文:
定理 injective_module_of_injective_object
  证明: by
    have : CategoryTheory.Mono (ModuleCat.ofHom f) := (ModuleCat.mono_iff_injective _).mpr hf
    obtain ⟨l, h⟩ := inj.factors (ModuleCat.ofHom g) (ModuleCat.ofHom f)
    obtain rfl := ModuleCat.hom_ext_iff.mp h
    exact ⟨l.hom, fun _ => rfl⟩

Depends on / 依赖: CategoryTheory, CategoryTheory.Mono, ModuleCat, ModuleCat.hom_ext_iff.mp, ModuleCat.mono_iff_injective, ModuleCat.ofHom, factors, hom_ext_iff, inj.factors, l.hom, mono_iff_injective
-/
theorem injective_module_of_injective_object
    [inj : CategoryTheory.Injective <| ModuleCat.of R M] :
    Module.Injective R M where
  out X Y _ _ _ _ f hf g := by
    have : CategoryTheory.Mono (ModuleCat.ofHom f) := (ModuleCat.mono_iff_injective _).mpr hf
    obtain ⟨l, h⟩ := inj.factors (ModuleCat.ofHom g) (ModuleCat.ofHom f)
    obtain rfl := ModuleCat.hom_ext_iff.mp h
    exact ⟨l.hom, fun _ => rfl⟩

/--
theorem `injective_iff_injective_object` / 定理 `injective_iff_injective_object`

English:
theorem injective_iff_injective_object
  proof: ⟨fun _ => injective_object_of_injective_module R M,
   fun _ => injective_module_of_injective_object R M⟩

中文:
定理 injective_iff_injective_object
  证明: ⟨fun _ => injective_object_of_injective_module R M,
   fun _ => injective_module_of_injective_object R M⟩

Depends on / 依赖: injective_module_of_injective_object, injective_object_of_injective_module
-/
theorem injective_iff_injective_object :
    Module.Injective R M ↔
    CategoryTheory.Injective (ModuleCat.of R M) :=
  ⟨fun _ => injective_object_of_injective_module R M,
   fun _ => injective_module_of_injective_object R M⟩

end Module

/--
Instance `ModuleCat.ulift_injective_of_injective.` / 实例 `ModuleCat.ulift_injective_of_injective.`

English:
instance ModuleCat.ulift_injective_of_injective.{v'}
  signature: [Small.{v} R]
  body: Module.injective_object_of_injective_module
    (inj := Module.ulift_injective_of_injective
      (inj := Module.injective_module_of_injective_object _ _))

中文:
实例 ModuleCat.ulift_injective_of_injective.{v'}
  签名: [Small.{v} R]
  定义体: Module.injective_object_of_injective_module
    (inj := Module.ulift_injective_of_injective
      (inj := Module.injective_module_of_injective_object _ _))

Depends on / 依赖: Module, Module.injective_module_of_injective_object, Module.injective_object_of_injective_module, Module.ulift_injective_of_injective, injective_module_of_injective_object, injective_object_of_injective_module, ulift_injective_of_injective
-/
instance ModuleCat.ulift_injective_of_injective.{v'} [Small.{v} R]
    [CategoryTheory.Injective <| ModuleCat.of R M] :
CategoryTheory.Injective ModuleCat.of R (ULift.{v'} M) :=
  Module.injective_object_of_injective_module
    (inj := Module.ulift_injective_of_injective
      (inj := Module.injective_module_of_injective_object _ _))
