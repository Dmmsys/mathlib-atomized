/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
module

public import Mathlib.CategoryTheory.Sites.Canonical
public import Mathlib.CategoryTheory.Sites.Coherent.Basic
public import Mathlib.CategoryTheory.Sites.EffectiveEpimorphic
/-!

# Sheaves for the coherent topology

This file characterises sheaves for the coherent topology

## Main result

* `isSheaf_coherent`: a presheaf of types is a sheaf for the coherent topology if and only
  if it satisfies the sheaf condition with respect to every presieve consisting of a finite
  effective epimorphic family.
-/

public section

namespace CategoryTheory

variable {C : Type*} [Category* C] [Precoherent C]

universe w in
/--
lemma `isSheaf_coherent` / 引理 `isSheaf_coherent`

English:
lemma isSheaf_coherent
  given: (P : Cᵒᵖ ⥤ Type w)
  proof: by
  constructor
  · intro hP B α _ X π h
    simp only [coherentTopology, Presieve.isSheaf_coverage] at hP
    apply hP
    exact ⟨α, inferInstance, X, π, rfl, h⟩
  · intro h
    simp only [coherentTopology, Presieve.isSheaf_coverage]
    rintro B S ⟨α, _, X, π, rfl, hS⟩
    exact h _ _ _ _ hS

中文:
引理 isSheaf_coherent
  条件: (P : Cᵒᵖ ⥤ Type w)
  证明: by
  constructor
  · intro hP B α _ X π h
    simp only [coherentTopology, Presieve.isSheaf_coverage] at hP
    apply hP
    exact ⟨α, inferInstance, X, π, rfl, h⟩
  · intro h
    simp only [coherentTopology, Presieve.isSheaf_coverage]
    rintro B S ⟨α, _, X, π, rfl, hS⟩
    exact h _ _ _ _ hS

Depends on / 依赖: Presieve, Presieve.isSheaf_coverage, coherentTopology, isSheaf_coverage
-/
lemma isSheaf_coherent (P : Cᵒᵖ ⥤ Type w) :
    Presieve.IsSheaf (coherentTopology C) P ↔
    (forall (B : C) (α : Type) [Finite α] (X : α -> C) (π : (a : α) -> (X a ⟶ B)),
      EffectiveEpiFamily X π -> (Presieve.ofArrows X π).IsSheafFor P) := by
  constructor
  · intro hP B α _ X π h
    simp only [coherentTopology, Presieve.isSheaf_coverage] at hP
    apply hP
    exact ⟨α, inferInstance, X, π, rfl, h⟩
  · intro h
    simp only [coherentTopology, Presieve.isSheaf_coverage]
    rintro B S ⟨α, _, X, π, rfl, hS⟩
    exact h _ _ _ _ hS

namespace coherentTopology

/--
theorem `isSheaf_yoneda_obj` / 定理 `isSheaf_yoneda_obj`

English:
theorem isSheaf_yoneda_obj
  given: (W : C)
  statement: Presieve.IsSheaf (coherentTopology C) (yoneda.obj W)
  proof: by
  rw [isSheaf_coherent]
  intro X α _ Y π H
  have h_colim := isColimitOfEffectiveEpiFamilyStruct Y π H.effectiveEpiFamily.some
  rw [← Sieve.generateFamily_eq] at h_colim
  intro x hx
  let x_ext := Presieve.FamilyOfElements.sieveExtend x
  have hx_ext := Presieve.FamilyOfElements.Compatible.sie

中文:
定理 isSheaf_yoneda_obj
  条件: (W : C)
  结论: Presieve.IsSheaf (coherentTopology C) (yoneda.obj W)
  证明: by
  rw [isSheaf_coherent]
  intro X α _ Y π H
  have h_colim := isColimitOfEffectiveEpiFamilyStruct Y π H.effectiveEpiFamily.some
  rw [← Sieve.generateFamily_eq] at h_colim
  intro x hx
  let x_ext := Presieve.FamilyOfElements.sieveExtend x
  have hx_ext := Presieve.FamilyOfElements.Compatible.sie

Depends on / 依赖: Compatible, FamilyOfElements, H.effectiveEpiFamily.some, IsAmalgamation, Presieve, Presieve.FamilyOfElements.Compatible.sieveExtend, Presieve.FamilyOfElements.sieveExtend, Presieve.ofArrows, Sieve.forallYonedaIsSheaf_iff_colimit, Sieve.generate, Sieve.generateFamily_eq, effectiveEpiFamily, forallYonedaIsSheaf_iff_colimit, generate, generateFamily_eq, h_colim, hx_ext, isColimitOfEffectiveEpiFamilyStruct, isSheaf_coherent, ofArrows
-/
theorem isSheaf_yoneda_obj (W : C) : Presieve.IsSheaf (coherentTopology C) (yoneda.obj W) := by
  rw [isSheaf_coherent]
  intro X α _ Y π H
  have h_colim := isColimitOfEffectiveEpiFamilyStruct Y π H.effectiveEpiFamily.some
  rw [← Sieve.generateFamily_eq] at h_colim
  intro x hx
  let x_ext := Presieve.FamilyOfElements.sieveExtend x
  have hx_ext := Presieve.FamilyOfElements.Compatible.sieveExtend hx
  let S := Sieve.generate (Presieve.ofArrows Y π)
  obtain ⟨t, t_amalg, t_uniq⟩ : exists! t, x_ext.IsAmalgamation t :=
    (Sieve.forallYonedaIsSheaf_iff_colimit S).mpr ⟨h_colim⟩ W x_ext hx_ext
  refine ⟨t, ?_, ?_⟩
  · convert!
    Presieve.isAmalgamation_restrict (Sieve.le_generate (Presieve.ofArrows Y π)) _ _ t_amalg
    exact (Presieve.restrict_extend hx).symm
· exact fun y hy => t_uniq y Presieve.isAmalgamation_sieveExtend x y hy

variable (C) in
/--
Instance `subcanonical` / 实例 `subcanonical`

English:
instance subcanonical
  signature: : (coherentTopology C).Subcanonical
  body: GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj _ isSheaf_yoneda_obj

中文:
实例 subcanonical
  签名: : (coherentTopology C).Subcanonical
  定义体: GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj _ isSheaf_yoneda_obj

Depends on / 依赖: GrothendieckTopology, GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj, Subcanonical, isSheaf_yoneda_obj, of_isSheaf_yoneda_obj
-/
instance subcanonical : (coherentTopology C).Subcanonical :=
  GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj _ isSheaf_yoneda_obj

end coherentTopology

end CategoryTheory
