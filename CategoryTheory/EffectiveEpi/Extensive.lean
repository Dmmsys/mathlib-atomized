/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.EffectiveEpi.Preserves
public import Mathlib.CategoryTheory.EffectiveEpi.Coproduct
public import Mathlib.CategoryTheory.Extensive
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
/-!

# Preserving and reflecting effective epis on extensive categories

We prove that a functor between `FinitaryPreExtensive` categories preserves (resp. reflects) finite
effective epi families if it preserves (resp. reflects) effective epis.
-/

public section

namespace CategoryTheory

open Limits

variable {C : Type*} [Category* C] [FinitaryPreExtensive C]

/--
theorem `effectiveEpi_desc_iff_effectiveEpiFamily` / 定理 `effectiveEpi_desc_iff_effectiveEpiFamily`

English:
theorem effectiveEpi_desc_iff_effectiveEpiFamily
  statement: {α : Type} [Finite α]
  proof: by
  exact ⟨fun h => ⟨⟨@effectiveEpiFamilyStructOfEffectiveEpiDesc _ _ _ _ X π _ h _ _ (fun g =>
    (FinitaryPreExtensive.isIso_sigmaDesc_fst (fun a => Sigma.ι X a) g inferInstance).epi_of_iso)⟩⟩,
    fun _ => inferInstance⟩

中文:
定理 effectiveEpi_desc_iff_effectiveEpiFamily
  结论: {α : 类型} [有限 α]
  证明: by
  exact ⟨fun h => ⟨⟨@effectiveEpiFamilyStructOfEffectiveEpiDesc _ _ _ _ X π _ h _ _ (fun g =>
    (FinitaryPreExtensive.isIso_sigmaDesc_fst (fun a => Sigma.ι X a) g inferInstance).epi_of_iso)⟩⟩,
    fun _ => inferInstance⟩

Depends on / 依赖: FinitaryPreExtensive, FinitaryPreExtensive.isIso_sigmaDesc_fst, effectiveEpiFamilyStructOfEffectiveEpiDesc, epi_of_iso, isIso_sigmaDesc_fst
-/
theorem effectiveEpi_desc_iff_effectiveEpiFamily {α : Type} [Finite α]
    {B : C} (X : α -> C) (π : (a : α) -> X a ⟶ B) :
    EffectiveEpi (Sigma.desc π) ↔ EffectiveEpiFamily X π := by
  exact ⟨fun h => ⟨⟨@effectiveEpiFamilyStructOfEffectiveEpiDesc _ _ _ _ X π _ h _ _ (fun g =>
    (FinitaryPreExtensive.isIso_sigmaDesc_fst (fun a => Sigma.ι X a) g inferInstance).epi_of_iso)⟩⟩,
    fun _ => inferInstance⟩

variable {D : Type*} [Category* D] [FinitaryPreExtensive D]
variable (F : C ⥤ D) [PreservesFiniteCoproducts F]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [F.ReflectsEffectiveEpis]
  signature: : F.ReflectsFiniteEffectiveEpiFamilies where
  body: by
    simp only [← effectiveEpi_desc_iff_effectiveEpiFamily]
    apply F.effectiveEpi_of_map
    convert!
      (inferInstance :
        EffectiveEpi (inv (sigmaComparison F X) ≫ (Sigma.desc (fun a => F.map (π a)))))
    simp

中文:
实例 [F.ReflectsEffectiveEpis]
  签名: : F.ReflectsFiniteEffectiveEpiFamilies where
  定义体: by
    simp only [← effectiveEpi_desc_iff_effectiveEpiFamily]
    apply F.effectiveEpi_of_map
    convert!
      (inferInstance :
        EffectiveEpi (inv (sigmaComparison F X) ≫ (Sigma.desc (fun a => F.map (π a)))))
    simp

Depends on / 依赖: EffectiveEpi, F.effectiveEpi_of_map, F.map, Sigma.desc, convert, effectiveEpi_desc_iff_effectiveEpiFamily, effectiveEpi_of_map, sigmaComparison
-/
instance [F.ReflectsEffectiveEpis] : F.ReflectsFiniteEffectiveEpiFamilies where
  reflects {α _ B} X π h := by
    simp only [← effectiveEpi_desc_iff_effectiveEpiFamily]
    apply F.effectiveEpi_of_map
    convert!
      (inferInstance :
        EffectiveEpi (inv (sigmaComparison F X) ≫ (Sigma.desc (fun a => F.map (π a)))))
    simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [F.PreservesEffectiveEpis]
  signature: : F.PreservesFiniteEffectiveEpiFamilies where
  body: by
    simp only [← effectiveEpi_desc_iff_effectiveEpiFamily]
    convert! (inferInstance : EffectiveEpi ((sigmaComparison F X) ≫ (F.map (Sigma.desc π))))
    simp

中文:
实例 [F.保持EffectiveEpis]
  签名: : F.保持FiniteEffectiveEpiFamilies where
  定义体: by
    simp only [← effectiveEpi_desc_iff_effectiveEpiFamily]
    convert! (inferInstance : EffectiveEpi ((sigmaComparison F X) ≫ (F.map (Sigma.desc π))))
    simp

Depends on / 依赖: EffectiveEpi, F.map, Sigma.desc, convert, effectiveEpi_desc_iff_effectiveEpiFamily, sigmaComparison
-/
instance [F.PreservesEffectiveEpis] : F.PreservesFiniteEffectiveEpiFamilies where
  preserves {α _ B} X π h := by
    simp only [← effectiveEpi_desc_iff_effectiveEpiFamily]
    convert! (inferInstance : EffectiveEpi ((sigmaComparison F X) ≫ (F.map (Sigma.desc π))))
    simp

end CategoryTheory
