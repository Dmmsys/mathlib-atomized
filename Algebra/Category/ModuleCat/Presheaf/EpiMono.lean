/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits

/-!
# Epimorphisms and monomorphisms in the category of presheaves of modules

In this file, we give characterizations of epimorphisms and monomorphisms
in the category of presheaves of modules.

-/

public section

universe v v₁ u₁ u

open CategoryTheory

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
  {M₁ M₂ : PresheafOfModules.{v} R} {f : M₁ ⟶ M₂}

/--
lemma `epi_of_surjective` / 引理 `epi_of_surjective`

English:
lemma epi_of_surjective
  given: (hf : forall ⦃X : Cᵒᵖ⦄, Function.Surjective (f.app X))
  statement: Epi f where
  proof: by
    ext X m₂
    obtain ⟨m₁, rfl⟩ := hf m₂
    exact ConcreteCategory.congr_hom ((evaluation R X ⋙ forget _).congr_map hg) m₁

中文:
引理 epi_of_surjective
  条件: (hf : 对任意 ⦃X : Cᵒᵖ⦄, 函数.满射 (f.app X))
  结论: 满态射 f where
  证明: by
    ext X m₂
    obtain ⟨m₁, rfl⟩ := hf m₂
    exact ConcreteCategory.congr_hom ((evaluation R X ⋙ forget _).congr_map hg) m₁

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, congr_hom, congr_map, evaluation, forget
-/
lemma epi_of_surjective (hf : forall ⦃X : Cᵒᵖ⦄, Function.Surjective (f.app X)) : Epi f where
  left_cancellation g₁ g₂ hg := by
    ext X m₂
    obtain ⟨m₁, rfl⟩ := hf m₂
    exact ConcreteCategory.congr_hom ((evaluation R X ⋙ forget _).congr_map hg) m₁

/--
lemma `mono_of_injective` / 引理 `mono_of_injective`

English:
lemma mono_of_injective
  given: (hf : forall ⦃X : Cᵒᵖ⦄, Function.Injective (f.app X))
  statement: Mono f where
  proof: by
    ext X m
    exact hf (ConcreteCategory.congr_hom ((evaluation R X ⋙ forget _).congr_map hg) m)

中文:
引理 mono_of_injective
  条件: (hf : 对任意 ⦃X : Cᵒᵖ⦄, 函数.单射 (f.app X))
  结论: 单态射 f where
  证明: by
    ext X m
    exact hf (ConcreteCategory.congr_hom ((evaluation R X ⋙ forget _).congr_map hg) m)

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, congr_hom, congr_map, evaluation, forget
-/
lemma mono_of_injective (hf : forall ⦃X : Cᵒᵖ⦄, Function.Injective (f.app X)) : Mono f where
  right_cancellation {M} g₁ g₂ hg := by
    ext X m
    exact hf (ConcreteCategory.congr_hom ((evaluation R X ⋙ forget _).congr_map hg) m)

variable (f)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Epi
  signature: f] (X
  body: inferInstanceAs (Epi ((evaluation R X).map f))

中文:
实例 [满态射
  签名: f] (X
  定义体: inferInstanceAs (Epi ((evaluation R X).map f))

Depends on / 依赖: evaluation
-/
instance [Epi f] (X : Cᵒᵖ) : Epi (f.app X) :=
  inferInstanceAs (Epi ((evaluation R X).map f))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Mono
  signature: f] (X
  body: inferInstanceAs (Mono ((evaluation R X).map f))

中文:
实例 [单态射
  签名: f] (X
  定义体: inferInstanceAs (Mono ((evaluation R X).map f))

Depends on / 依赖: evaluation
-/
instance [Mono f] (X : Cᵒᵖ) : Mono (f.app X) :=
  inferInstanceAs (Mono ((evaluation R X).map f))

/--
lemma `surjective_of_epi` / 引理 `surjective_of_epi`

English:
lemma surjective_of_epi
  given: [Epi f] (X : Cᵒᵖ)
  proof: by
  rw [← ModuleCat.epi_iff_surjective]
  infer_instance

中文:
引理 surjective_of_epi
  条件: [满态射 f] (X : Cᵒᵖ)
  证明: by
  rw [← ModuleCat.epi_iff_surjective]
  infer_instance

Depends on / 依赖: ModuleCat, ModuleCat.epi_iff_surjective, epi_iff_surjective, infer_instance
-/
lemma surjective_of_epi [Epi f] (X : Cᵒᵖ) :
    Function.Surjective (f.app X) := by
  rw [← ModuleCat.epi_iff_surjective]
  infer_instance

/--
lemma `injective_of_mono` / 引理 `injective_of_mono`

English:
lemma injective_of_mono
  given: [Mono f] (X : Cᵒᵖ)
  proof: by
  rw [← ModuleCat.mono_iff_injective]
  infer_instance

中文:
引理 injective_of_mono
  条件: [单态射 f] (X : Cᵒᵖ)
  证明: by
  rw [← ModuleCat.mono_iff_injective]
  infer_instance

Depends on / 依赖: ModuleCat, ModuleCat.mono_iff_injective, infer_instance, mono_iff_injective
-/
lemma injective_of_mono [Mono f] (X : Cᵒᵖ) :
    Function.Injective (f.app X) := by
  rw [← ModuleCat.mono_iff_injective]
  infer_instance

/--
lemma `epi_iff_surjective` / 引理 `epi_iff_surjective`

English:
lemma epi_iff_surjective
  proof: ⟨fun _ => surjective_of_epi f, epi_of_surjective⟩

中文:
引理 epi_iff_surjective
  证明: ⟨fun _ => surjective_of_epi f, epi_of_surjective⟩

Depends on / 依赖: epi_of_surjective, surjective_of_epi
-/
lemma epi_iff_surjective :
    Epi f ↔ forall ⦃X : Cᵒᵖ⦄, Function.Surjective (f.app X) :=
  ⟨fun _ => surjective_of_epi f, epi_of_surjective⟩

/--
lemma `mono_iff_surjective` / 引理 `mono_iff_surjective`

English:
lemma mono_iff_surjective
  proof: ⟨fun _ => injective_of_mono f, mono_of_injective⟩

中文:
引理 mono_iff_surjective
  证明: ⟨fun _ => injective_of_mono f, mono_of_injective⟩

Depends on / 依赖: injective_of_mono, mono_of_injective
-/
lemma mono_iff_surjective :
    Mono f ↔ forall ⦃X : Cᵒᵖ⦄, Function.Injective (f.app X) :=
  ⟨fun _ => injective_of_mono f, mono_of_injective⟩

end PresheafOfModules
