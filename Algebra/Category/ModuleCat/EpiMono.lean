/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
# Monomorphisms in `Module R`

This file shows that an `R`-linear map is a monomorphism in the category of `R`-modules
if and only if it is injective, and similarly an epimorphism if and only if it is surjective.
-/

@[expose] public section


universe v u

open CategoryTheory

namespace ModuleCat

variable {R : Type u} [Ring R] {X Y : ModuleCat.{v} R} (f : X ⟶ Y)
variable {M : Type v} [AddCommGroup M] [Module R M]

/--
theorem `ker_eq_bot_of_mono` / 定理 `ker_eq_bot_of_mono`

English:
theorem ker_eq_bot_of_mono
  given: [Mono f]
  statement: LinearMap.ker f.hom = ⊥
  proof: LinearMap.ker_eq_bot_of_cancel fun u v h => ModuleCat.hom_ext_iff.mp
(@cancel_mono _ _ _ _ _ f _ (↟u) (↟v)).1 ModuleCat.hom_ext_iff.mpr h

中文:
定理 ker_eq_bot_of_mono
  条件: [单态射 f]
  结论: 线性映射.ker f.hom = ⊥
  证明: LinearMap.ker_eq_bot_of_cancel fun u v h => ModuleCat.hom_ext_iff.mp
(@cancel_mono _ _ _ _ _ f _ (↟u) (↟v)).1 ModuleCat.hom_ext_iff.mpr h

Depends on / 依赖: LinearMap, LinearMap.ker_eq_bot_of_cancel, ModuleCat, ModuleCat.hom_ext_iff.mp, ModuleCat.hom_ext_iff.mpr, cancel_mono, hom_ext_iff, ker_eq_bot_of_cancel
-/
theorem ker_eq_bot_of_mono [Mono f] : LinearMap.ker f.hom = ⊥ :=
LinearMap.ker_eq_bot_of_cancel fun u v h => ModuleCat.hom_ext_iff.mp
(@cancel_mono _ _ _ _ _ f _ (↟u) (↟v)).1 ModuleCat.hom_ext_iff.mpr h

/--
theorem `range_eq_top_of_epi` / 定理 `range_eq_top_of_epi`

English:
theorem range_eq_top_of_epi
  given: [Epi f]
  statement: LinearMap.range f.hom = ⊤
  proof: LinearMap.range_eq_top_of_cancel fun u v h => ModuleCat.hom_ext_iff.mp
(@cancel_epi _ _ _ _ _ f _ (↟u) (↟v)).1 ModuleCat.hom_ext_iff.mpr h

中文:
定理 range_eq_top_of_epi
  条件: [满态射 f]
  结论: 线性映射.range f.hom = ⊤
  证明: LinearMap.range_eq_top_of_cancel fun u v h => ModuleCat.hom_ext_iff.mp
(@cancel_epi _ _ _ _ _ f _ (↟u) (↟v)).1 ModuleCat.hom_ext_iff.mpr h

Depends on / 依赖: LinearMap, LinearMap.range_eq_top_of_cancel, ModuleCat, ModuleCat.hom_ext_iff.mp, ModuleCat.hom_ext_iff.mpr, cancel_epi, hom_ext_iff, range_eq_top_of_cancel
-/
theorem range_eq_top_of_epi [Epi f] : LinearMap.range f.hom = ⊤ :=
LinearMap.range_eq_top_of_cancel fun u v h => ModuleCat.hom_ext_iff.mp
(@cancel_epi _ _ _ _ _ f _ (↟u) (↟v)).1 ModuleCat.hom_ext_iff.mpr h

/--
theorem `mono_iff_ker_eq_bot` / 定理 `mono_iff_ker_eq_bot`

English:
theorem mono_iff_ker_eq_bot
  statement: Mono f ↔ LinearMap.ker f.hom = ⊥
  proof: ⟨fun _ => ker_eq_bot_of_mono _, fun hf =>
ConcreteCategory.mono_of_injective _ by convert! LinearMap.ker_eq_bot.1 hf⟩

中文:
定理 mono_iff_ker_eq_bot
  结论: 单态射 f ↔ 线性映射.ker f.hom = ⊥
  证明: ⟨fun _ => ker_eq_bot_of_mono _, fun hf =>
ConcreteCategory.mono_of_injective _ by convert! LinearMap.ker_eq_bot.1 hf⟩

Depends on / 依赖: ConcreteCategory, ConcreteCategory.mono_of_injective, LinearMap, LinearMap.ker_eq_bot, convert, ker_eq_bot, ker_eq_bot_of_mono, mono_of_injective
-/
theorem mono_iff_ker_eq_bot : Mono f ↔ LinearMap.ker f.hom = ⊥ :=
  ⟨fun _ => ker_eq_bot_of_mono _, fun hf =>
ConcreteCategory.mono_of_injective _ by convert! LinearMap.ker_eq_bot.1 hf⟩

/--
theorem `mono_iff_injective` / 定理 `mono_iff_injective`

English:
theorem mono_iff_injective
  statement: Mono f ↔ Function.Injective f
  proof: by
  rw [mono_iff_ker_eq_bot]; rw [LinearMap.ker_eq_bot]

中文:
定理 mono_iff_injective
  结论: 单态射 f ↔ 函数.单射 f
  证明: by
  rw [mono_iff_ker_eq_bot]; rw [LinearMap.ker_eq_bot]

Depends on / 依赖: LinearMap, LinearMap.ker_eq_bot, ker_eq_bot, mono_iff_ker_eq_bot
-/
theorem mono_iff_injective : Mono f ↔ Function.Injective f := by
  rw [mono_iff_ker_eq_bot]; rw [LinearMap.ker_eq_bot]

/--
theorem `epi_iff_range_eq_top` / 定理 `epi_iff_range_eq_top`

English:
theorem epi_iff_range_eq_top
  statement: Epi f ↔ LinearMap.range f.hom = ⊤
  proof: ⟨fun _ => range_eq_top_of_epi _, fun hf =>
ConcreteCategory.epi_of_surjective _ by convert! LinearMap.range_eq_top.1 hf⟩

中文:
定理 epi_iff_range_eq_top
  结论: 满态射 f ↔ 线性映射.range f.hom = ⊤
  证明: ⟨fun _ => range_eq_top_of_epi _, fun hf =>
ConcreteCategory.epi_of_surjective _ by convert! LinearMap.range_eq_top.1 hf⟩

Depends on / 依赖: ConcreteCategory, ConcreteCategory.epi_of_surjective, LinearMap, LinearMap.range_eq_top, convert, epi_of_surjective, range_eq_top, range_eq_top_of_epi
-/
theorem epi_iff_range_eq_top : Epi f ↔ LinearMap.range f.hom = ⊤ :=
  ⟨fun _ => range_eq_top_of_epi _, fun hf =>
ConcreteCategory.epi_of_surjective _ by convert! LinearMap.range_eq_top.1 hf⟩

/--
theorem `epi_iff_surjective` / 定理 `epi_iff_surjective`

English:
theorem epi_iff_surjective
  statement: Epi f ↔ Function.Surjective f
  proof: by
  rw [epi_iff_range_eq_top]; rw [LinearMap.range_eq_top]

中文:
定理 epi_iff_surjective
  结论: 满态射 f ↔ 函数.满射 f
  证明: by
  rw [epi_iff_range_eq_top]; rw [LinearMap.range_eq_top]

Depends on / 依赖: LinearMap, LinearMap.range_eq_top, epi_iff_range_eq_top, range_eq_top
-/
theorem epi_iff_surjective : Epi f ↔ Function.Surjective f := by
  rw [epi_iff_range_eq_top]; rw [LinearMap.range_eq_top]

/-- If the zero morphism is an epi then the codomain is trivial. -/
@[instance_reducible]
/--
Definition of `uniqueOfEpiZero` / `uniqueOfEpiZero` 的定义

English:
definition uniqueOfEpiZero
  signature: (X) [h : Epi (0 : X ⟶ of R M)]
  body: uniqueOfSurjectiveZero X ((ModuleCat.epi_iff_surjective _).mp h)

中文:
定义 uniqueOfEpiZero
  签名: (X) [h : 满态射 (0 : X ⟶ of R M)]
  定义体: uniqueOfSurjectiveZero X ((ModuleCat.epi_iff_surjective _).mp h)

Depends on / 依赖: ModuleCat, ModuleCat.epi_iff_surjective, epi_iff_surjective, uniqueOfSurjectiveZero
-/
def uniqueOfEpiZero (X) [h : Epi (0 : X ⟶ of R M)] : Unique M :=
  uniqueOfSurjectiveZero X ((ModuleCat.epi_iff_surjective _).mp h)

/--
Instance `mono_as_hom'_subtype` / 实例 `mono_as_hom'_subtype`

English:
instance mono_as_hom'_subtype
  signature: (U : Submodule R X)
  body: (mono_iff_ker_eq_bot _).mpr (Submodule.ker_subtype U)

中文:
实例 mono_as_hom'_subtype
  签名: (U : 子模 R X)
  定义体: (mono_iff_ker_eq_bot _).mpr (Submodule.ker_subtype U)

Depends on / 依赖: Submodule, Submodule.ker_subtype, ker_subtype, mono_iff_ker_eq_bot
-/
instance mono_as_hom'_subtype (U : Submodule R X) : Mono (ModuleCat.ofHom U.subtype) :=
  (mono_iff_ker_eq_bot _).mpr (Submodule.ker_subtype U)

/--
Instance `epi_as_hom''_mkQ` / 实例 `epi_as_hom''_mkQ`

English:
instance epi_as_hom''_mkQ
  signature: (U : Submodule R X)
  body: (epi_iff_range_eq_top _).mpr Submodule.range_mkQ _

中文:
实例 epi_as_hom''_mkQ
  签名: (U : 子模 R X)
  定义体: (epi_iff_range_eq_top _).mpr Submodule.range_mkQ _

Depends on / 依赖: Submodule, Submodule.range_mkQ, epi_iff_range_eq_top, range_mkQ
-/
instance epi_as_hom''_mkQ (U : Submodule R X) : Epi (ModuleCat.ofHom U.mkQ) :=
(epi_iff_range_eq_top _).mpr Submodule.range_mkQ _

/--
Instance `forget_preservesEpimorphisms` / 实例 `forget_preservesEpimorphisms`

English:
instance forget_preservesEpimorphisms
  signature: : (forget (ModuleCat.{v} R)).PreservesEpimorphisms where
  body: by
      rw [CategoryTheory.ofHom_epi_iff_surjective]; rw [← epi_iff_surjective]
      exact hf

中文:
实例 forget_preservesEpimorphisms
  签名: : (forget (模范畴.{v} R)).保持Epimorphisms where
  定义体: by
      rw [CategoryTheory.ofHom_epi_iff_surjective]; rw [← epi_iff_surjective]
      exact hf

Depends on / 依赖: CategoryTheory, CategoryTheory.ofHom_epi_iff_surjective, epi_iff_surjective, ofHom_epi_iff_surjective
-/
instance forget_preservesEpimorphisms : (forget (ModuleCat.{v} R)).PreservesEpimorphisms where
    preserves f hf := by
      rw [CategoryTheory.ofHom_epi_iff_surjective]; rw [← epi_iff_surjective]
      exact hf

/--
Instance `forget_preservesMonomorphisms` / 实例 `forget_preservesMonomorphisms`

English:
instance forget_preservesMonomorphisms
  signature: : (forget (ModuleCat.{v} R)).PreservesMonomorphisms where
  body: by
      rw [CategoryTheory.ofHom_mono_iff_injective]; rw [← mono_iff_injective]
      exact hf

中文:
实例 forget_preservesMonomorphisms
  签名: : (forget (模范畴.{v} R)).保持Monomorphisms where
  定义体: by
      rw [CategoryTheory.ofHom_mono_iff_injective]; rw [← mono_iff_injective]
      exact hf

Depends on / 依赖: CategoryTheory, CategoryTheory.ofHom_mono_iff_injective, mono_iff_injective, ofHom_mono_iff_injective
-/
instance forget_preservesMonomorphisms : (forget (ModuleCat.{v} R)).PreservesMonomorphisms where
    preserves f hf := by
      rw [CategoryTheory.ofHom_mono_iff_injective]; rw [← mono_iff_injective]
      exact hf

end ModuleCat
