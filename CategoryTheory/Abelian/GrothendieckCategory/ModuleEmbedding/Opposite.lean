/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Abelian.Yoneda
public import Mathlib.CategoryTheory.Generator.Abelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-!
# Embedding opposites of Grothendieck categories

If `C` is Grothendieck abelian and `F : D ⥤ Cᵒᵖ` is a functor from a small category, we construct
an object `G : Cᵒᵖ` such that `preadditiveCoyonedaObj G : Cᵒᵖ ⥤ ModuleCat (End G)ᵐᵒᵖ` is faithful
and exact and its precomposition with `F` is full if `F` is.
-/

@[expose] public section

universe v u

open CategoryTheory Limits Opposite ZeroObject

namespace CategoryTheory.Abelian.IsGrothendieckAbelian

variable {C : Type u} [Category.{v} C] {D : Type v} [SmallCategory D] (F : D ⥤ Cᵒᵖ)

namespace OppositeModuleEmbedding

variable [Abelian C] [IsGrothendieckAbelian.{v} C]

variable (C) in
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def projectiveSeparator
  body: (has_projective_separator (coseparator Cᵒᵖ) (isCoseparator_coseparator Cᵒᵖ)).choose

中文:
定义 noncomputable
  签名: def projectiveSeparator
  定义体: (has_projective_separator (coseparator Cᵒᵖ) (isCoseparator_coseparator Cᵒᵖ)).choose
-/
private noncomputable def projectiveSeparator : Cᵒᵖ :=
  (has_projective_separator (coseparator Cᵒᵖ) (isCoseparator_coseparator Cᵒᵖ)).choose

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Projective (projectiveSeparator C)
  body: (has_projective_separator (coseparator Cᵒᵖ) (isCoseparator_coseparator Cᵒᵖ)).choose_spec.1

中文:
实例 :
  签名: Projective (projectiveSeparator C)
  定义体: (has_projective_separator (coseparator Cᵒᵖ) (isCoseparator_coseparator Cᵒᵖ)).choose_spec.1

Depends on / 依赖: StructuredArrow, StructuredArrow.preEquivalence, isConnected_of_equivalent, preEquivalence
-/
private instance : Projective (projectiveSeparator C) :=
  (has_projective_separator (coseparator Cᵒᵖ) (isCoseparator_coseparator Cᵒᵖ)).choose_spec.1

/--
theorem `isSeparator_projectiveSeparator` / 定理 `isSeparator_projectiveSeparator`

English:
theorem isSeparator_projectiveSeparator
  statement: IsSeparator (projectiveSeparator C)
  proof: (has_projective_separator (coseparator Cᵒᵖ) (isCoseparator_coseparator Cᵒᵖ)).choose_spec.2

中文:
定理 isSeparator_projectiveSeparator
  结论: IsSeparator (projectiveSeparator C)
  证明: (has_projective_separator (coseparator Cᵒᵖ) (isCoseparator_coseparator Cᵒᵖ)).choose_spec.2

Depends on / 依赖: CostructuredArrow, CostructuredArrow.preEquivalence, isConnected_of_equivalent, preEquivalence
-/
private theorem isSeparator_projectiveSeparator : IsSeparator (projectiveSeparator C) :=
  (has_projective_separator (coseparator Cᵒᵖ) (isCoseparator_coseparator Cᵒᵖ)).choose_spec.2

set_option backward.privateInPublic true in
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def generator
  body: ∐ (fun (X : D) => ∐ fun (_ : projectiveSeparator C ⟶ F.obj X) => projectiveSeparator C)

中文:
定义 noncomputable
  签名: def generator
  定义体: ∐ (fun (X : D) => ∐ fun (_ : projectiveSeparator C ⟶ F.obj X) => projectiveSeparator C)

Depends on / 依赖: A.hom, G.map, IsCofiltered, IsCofiltered.min, IsCofiltered.minToLeft, IsCofiltered.nonempty, IsCofilteredOrEmpty, Nonempty, StructuredArrow, StructuredArrow.pre, T.obj, U.right, Y.hom, Y.right, minToLeft, nonempty
-/
private noncomputable def generator : Cᵒᵖ :=
  ∐ (fun (X : D) => ∐ fun (_ : projectiveSeparator C ⟶ F.obj X) => projectiveSeparator C)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `exists_epi` / 定理 `exists_epi`

English:
theorem exists_epi
  given: (X : D)
  statement: exists f : generator F ⟶ F.obj X, Epi f
  proof: by
  classical
  refine ⟨Sigma.desc (Pi.single X (𝟙 _)) ≫ Sigma.desc (fun f => f), ?_⟩
  have h := (isSeparator_iff_epi (projectiveSeparator C)).1
    isSeparator_projectiveSeparator (F.obj X)
  suffices Epi (Sigma.desc (Pi.single X (𝟙 _))) from epi_comp' this h
  exact SplitEpi.epi ⟨Sigma.ι (fun (X

中文:
定理 exists_epi
  条件: (X : D)
  结论: 存在 f : generator F ⟶ F.obj X, Epi f
  证明: by
  classical
  refine ⟨Sigma.desc (Pi.single X (𝟙 _)) ≫ Sigma.desc (fun f => f), ?_⟩
  have h := (isSeparator_iff_epi (projectiveSeparator C)).1
    isSeparator_projectiveSeparator (F.obj X)
  suffices Epi (Sigma.desc (Pi.single X (𝟙 _))) from epi_comp' this h
  exact SplitEpi.epi ⟨Sigma.ι (fun (X

Depends on / 依赖: F.op, G.op, IsCofiltered, IsCofiltered.iff_of_equivalence, StructuredArrow, costructuredArrowOpEquivalence, iff_of_equivalence, isCofiltered_op_iff_isFiltered
-/
private theorem exists_epi (X : D) : exists f : generator F ⟶ F.obj X, Epi f := by
  classical
  refine ⟨Sigma.desc (Pi.single X (𝟙 _)) ≫ Sigma.desc (fun f => f), ?_⟩
  have h := (isSeparator_iff_epi (projectiveSeparator C)).1
    isSeparator_projectiveSeparator (F.obj X)
  suffices Epi (Sigma.desc (Pi.single X (𝟙 _))) from epi_comp' this h
  exact SplitEpi.epi ⟨Sigma.ι (fun (X : D) => ∐ fun _ => projectiveSeparator C) X, by simp⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Projective (generator F)
  body: by
  rw [generator]
  infer_instance

中文:
实例 :
  签名: Projective (generator F)
  定义体: by
  rw [generator]
  infer_instance

Depends on / 依赖: CategoryOfElements, CategoryOfElements.structuredArrowEquivalence, IsCofiltered, StructuredArrow, infer_instance, of_equivalence, structuredArrowEquivalence
-/
private instance : Projective (generator F) := by
  rw [generator]
  infer_instance

/--
theorem `isSeparator` / 定理 `isSeparator`

English:
theorem isSeparator
  given: [Nonempty D]
  statement: IsSeparator (generator F)
  proof: by
  apply isSeparator_sigma_of_isSeparator _ Classical.ofNonempty
  apply isSeparator_sigma_of_isSeparator _ 0
  exact isSeparator_projectiveSeparator

中文:
定理 isSeparator
  条件: [Nonempty D]
  结论: IsSeparator (generator F)
  证明: by
  apply isSeparator_sigma_of_isSeparator _ Classical.ofNonempty
  apply isSeparator_sigma_of_isSeparator _ 0
  exact isSeparator_projectiveSeparator
-/
private theorem isSeparator [Nonempty D] : IsSeparator (generator F) := by
  apply isSeparator_sigma_of_isSeparator _ Classical.ofNonempty
  apply isSeparator_sigma_of_isSeparator _ 0
  exact isSeparator_projectiveSeparator

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `EmbeddingRing` / `EmbeddingRing` 的定义

English:
definition EmbeddingRing
  signature: : Type v
  body: (End (generator F))ᵐᵒᵖ

中文:
定义 EmbeddingRing
  签名: : 类型v
  定义体: (End (generator F))ᵐᵒᵖ

Depends on / 依赖: generator
-/
def EmbeddingRing : Type v := (End (generator F))ᵐᵒᵖ

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Ring (EmbeddingRing F)
  body: inferInstanceAs Ring (End (generator F))ᵐᵒᵖ

中文:
实例 :
  签名: Ring (EmbeddingRing F)
  定义体: inferInstanceAs Ring (End (generator F))ᵐᵒᵖ

Depends on / 依赖: generator
-/
noncomputable instance : Ring (EmbeddingRing F) :=
inferInstanceAs Ring (End (generator F))ᵐᵒᵖ

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `embedding` / `embedding` 的定义

English:
definition embedding
  signature: : Cᵒᵖ ⥤ ModuleCat.{v} (EmbeddingRing F)
  body: preadditiveCoyonedaObj (generator F)

中文:
定义 embedding
  签名: : Cᵒᵖ ⥤ ModuleCat.{v} (EmbeddingRing F)
  定义体: preadditiveCoyonedaObj (generator F)

Depends on / 依赖: generator, preadditiveCoyonedaObj
-/
noncomputable def embedding : Cᵒᵖ ⥤ ModuleCat.{v} (EmbeddingRing F) :=
  preadditiveCoyonedaObj (generator F)

/--
Instance `faithful_embedding` / 实例 `faithful_embedding`

English:
instance faithful_embedding
  signature: [Nonempty D]
  body: (isSeparator_iff_faithful_preadditiveCoyonedaObj _).1 (isSeparator F)

中文:
实例 faithful_embedding
  签名: [Nonempty D]
  定义体: (isSeparator_iff_faithful_preadditiveCoyonedaObj _).1 (isSeparator F)

Depends on / 依赖: isSeparator, isSeparator_iff_faithful_preadditiveCoyonedaObj
-/
instance faithful_embedding [Nonempty D] : (embedding F).Faithful :=
  (isSeparator_iff_faithful_preadditiveCoyonedaObj _).1 (isSeparator F)

/--
Instance `full_embedding` / 实例 `full_embedding`

English:
instance full_embedding
  signature: [Nonempty D] [F.Full]
  body: full_comp_preadditiveCoyonedaObj _ (isSeparator F) (exists_epi F)

中文:
实例 full_embedding
  签名: [Nonempty D] [F.Full]
  定义体: full_comp_preadditiveCoyonedaObj _ (isSeparator F) (exists_epi F)

Depends on / 依赖: exists_epi, full_comp_preadditiveCoyonedaObj, isSeparator
-/
instance full_embedding [Nonempty D] [F.Full] : (F ⋙ embedding F).Full :=
  full_comp_preadditiveCoyonedaObj _ (isSeparator F) (exists_epi F)

set_option backward.isDefEq.respectTransparency false in
/--
Instance `preservesFiniteLimits_embedding` / 实例 `preservesFiniteLimits_embedding`

English:
instance preservesFiniteLimits_embedding
  signature: : PreservesFiniteLimits (embedding F)
  body: by
  rw [embedding]
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize
  infer_instance

中文:
实例 preservesFiniteLimits_embedding
  签名: : PreservesFiniteLimits (embedding F)
  定义体: by
  rw [embedding]
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize
  infer_instance

Depends on / 依赖: embedding, infer_instance, preservesFiniteLimits_of_preservesFiniteLimitsOfSize
-/
instance preservesFiniteLimits_embedding : PreservesFiniteLimits (embedding F) := by
  rw [embedding]
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize
  infer_instance

/--
Instance `preservesFiniteColimits_embedding` / 实例 `preservesFiniteColimits_embedding`

English:
instance preservesFiniteColimits_embedding
  signature: : PreservesFiniteColimits (embedding F)
  body: by
  apply preservesFiniteColimits_preadditiveCoyonedaObj_of_projective

中文:
实例 preservesFiniteColimits_embedding
  签名: : PreservesFiniteColimits (embedding F)
  定义体: by
  apply preservesFiniteColimits_preadditiveCoyonedaObj_of_projective

Depends on / 依赖: preservesFiniteColimits_preadditiveCoyonedaObj_of_projective
-/
instance preservesFiniteColimits_embedding : PreservesFiniteColimits (embedding F) := by
  apply preservesFiniteColimits_preadditiveCoyonedaObj_of_projective

end OppositeModuleEmbedding

end CategoryTheory.Abelian.IsGrothendieckAbelian
