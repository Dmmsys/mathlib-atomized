/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Double
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Generator.Basic

/-!
# Generators of the category of homological complexes

Let `c : ComplexShape ι` be a complex shape with no loop.
If a category `C` has a separator, then `HomologicalComplex C c`
has a separating family, and a separator when suitable coproducts exist.

-/

@[expose] public section

universe t w v u

open CategoryTheory Limits

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] {ι : Type w} (c : ComplexShape ι) [c.HasNoLoop]

section

variable [HasZeroMorphisms C] [HasZeroObject C]

variable {α : Type t} {X : α -> C} (hX : ObjectProperty.IsSeparating (.ofObj X))

variable (X) in
/--
Definition of `separatingFamily` / `separatingFamily` 的定义

English:
definition separatingFamily
  signature: (j : α × ι)
  body: evalCompCoyonedaCorepresentative c (X j.1) j.2

中文:
定义 separatingFamily
  签名: (j : α × ι)
  定义体: evalCompCoyonedaCorepresentative c (X j.1) j.2

Depends on / 依赖: evalCompCoyonedaCorepresentative
-/
noncomputable def separatingFamily (j : α × ι) : HomologicalComplex C c :=
  evalCompCoyonedaCorepresentative c (X j.1) j.2

set_option backward.isDefEq.respectTransparency false in
include hX in
/--
lemma `isSeparating_separatingFamily` / 引理 `isSeparating_separatingFamily`

English:
lemma isSeparating_separatingFamily
  proof: by
  intro K L f g h
  ext j
  apply hX
  rintro _ ⟨a⟩ p
  have H := evalCompCoyonedaCorepresentable c (X a) j
  apply H.homEquiv.symm.injective
  simpa only [H.homEquiv_symm_comp] using! h _
    (ObjectProperty.ofObj_apply _ ⟨a, j⟩) (H.homEquiv.symm p)

中文:
引理 isSeparating_separatingFamily
  证明: by
  intro K L f g h
  ext j
  apply hX
  rintro _ ⟨a⟩ p
  have H := evalCompCoyonedaCorepresentable c (X a) j
  apply H.homEquiv.symm.injective
  simpa only [H.homEquiv_symm_comp] using! h _
    (ObjectProperty.ofObj_apply _ ⟨a, j⟩) (H.homEquiv.symm p)

Depends on / 依赖: H.homEquiv.symm, H.homEquiv.symm.injective, H.homEquiv_symm_comp, ObjectProperty, ObjectProperty.ofObj_apply, evalCompCoyonedaCorepresentable, homEquiv, homEquiv_symm_comp, injective, ofObj_apply
-/
lemma isSeparating_separatingFamily :
    ObjectProperty.IsSeparating (.ofObj (separatingFamily c X)) := by
  intro K L f g h
  ext j
  apply hX
  rintro _ ⟨a⟩ p
  have H := evalCompCoyonedaCorepresentable c (X a) j
  apply H.homEquiv.symm.injective
  simpa only [H.homEquiv_symm_comp] using! h _
    (ObjectProperty.ofObj_apply _ ⟨a, j⟩) (H.homEquiv.symm p)

end

variable [HasCoproductsOfShape ι C] [Preadditive C] [HasZeroObject C]

/--
lemma `isSeparator_coproduct_separatingFamily` / 引理 `isSeparator_coproduct_separatingFamily`

English:
lemma isSeparator_coproduct_separatingFamily
  given: {X : C} (hX : IsSeparator X)
  proof: by
  let φ (i : ι) := separatingFamily c (fun (_ : Unit) => X) ⟨⟨⟩, i⟩
  refine isSeparator_of_isColimit_cofan
    (isSeparating_separatingFamily c (X := fun (_ : Unit) => X) (by simpa using! hX))
      (c := Cofan.mk (∐ φ) (fun ⟨_, i⟩ => Sigma.ι φ i)) ?_
  exact IsColimit.ofWhiskerEquivalence
    (

中文:
引理 isSeparator_coproduct_separatingFamily
  条件: {X : C} (hX : IsSeparator X)
  证明: by
  let φ (i : ι) := separatingFamily c (fun (_ : Unit) => X) ⟨⟨⟩, i⟩
  refine isSeparator_of_isColimit_cofan
    (isSeparating_separatingFamily c (X := fun (_ : Unit) => X) (by simpa using! hX))
      (c := Cofan.mk (∐ φ) (fun ⟨_, i⟩ => Sigma.ι φ i)) ?_
  exact IsColimit.ofWhiskerEquivalence
    (

Depends on / 依赖: Cofan.mk, Discrete, Discrete.equivalence, Equiv.punitProd, HasSplitCoequalizer, IsColimit, IsColimit.ofWhiskerEquivalence, coproductIsCoproduct, equivalence, hasCoequalizer_of_hasSplitCoequalizer, isSeparating_separatingFamily, isSeparator_of_isColimit_cofan, ofWhiskerEquivalence, punitProd, separatingFamily
-/
lemma isSeparator_coproduct_separatingFamily {X : C} (hX : IsSeparator X) :
    IsSeparator (∐ (fun i => separatingFamily c (fun (_ : Unit) => X) ⟨⟨⟩, i⟩)) := by
  let φ (i : ι) := separatingFamily c (fun (_ : Unit) => X) ⟨⟨⟩, i⟩
  refine isSeparator_of_isColimit_cofan
    (isSeparating_separatingFamily c (X := fun (_ : Unit) => X) (by simpa using! hX))
      (c := Cofan.mk (∐ φ) (fun ⟨_, i⟩ => Sigma.ι φ i)) ?_
  exact IsColimit.ofWhiskerEquivalence
    (Discrete.equivalence (Equiv.punitProd.{0} ι).symm) (coproductIsCoproduct φ)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasSeparator
  signature: C] : HasSeparator (HomologicalComplex C c)
  body: ⟨_, isSeparator_coproduct_separatingFamily c (isSeparator_separator C)⟩

中文:
实例 [HasSeparator
  签名: C] : HasSeparator (HomologicalComplex C c)
  定义体: ⟨_, isSeparator_coproduct_separatingFamily c (isSeparator_separator C)⟩

Depends on / 依赖: isSeparator_coproduct_separatingFamily, isSeparator_separator
-/
instance [HasSeparator C] : HasSeparator (HomologicalComplex C c) :=
  ⟨_, isSeparator_coproduct_separatingFamily c (isSeparator_separator C)⟩

end HomologicalComplex
