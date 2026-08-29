/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomotopyCofiber
public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Localization.Composition
public import Mathlib.CategoryTheory.Localization.HasLocalization

/-! # The category of homological complexes up to quasi-isomorphisms

Given a category `C` with homology and any complex shape `c`, we define
the category `HomologicalComplexUpToQuasiIso C c` which is the localized
category of `HomologicalComplex C c` with respect to quasi-isomorphisms.
When `C` is abelian, this will be the derived category of `C` in the
particular case of the complex shape `ComplexShape.up ℤ`.

Under suitable assumptions on `c` (e.g. chain complexes, or cochain
complexes indexed by `ℤ`), we shall show that `HomologicalComplexUpToQuasiIso C c`
is also the localized category of `HomotopyCategory C c` with respect to
the class of quasi-isomorphisms.

-/

@[expose] public section

open CategoryTheory Limits

section

variable (C : Type*) [Category* C] {ι : Type*} (c : ComplexShape ι) [HasZeroMorphisms C]
  [CategoryWithHomology C]

set_option backward.defeqAttrib.useBackward true in
/--
lemma `HomologicalComplex.homologyFunctor_inverts_quasiIso` / 引理 `HomologicalComplex.homologyFunctor_inverts_quasiIso`

English:
lemma HomologicalComplex.homologyFunctor_inverts_quasiIso
  given: (i : ι)
  proof: fun _ _ _ hf => by
  rw [mem_quasiIso_iff] at hf
  dsimp
  infer_instance

中文:
引理 同调复形.homologyFunctor_inverts_quasiIso
  条件: (i : ι)
  证明: fun _ _ _ hf => by
  rw [mem_quasiIso_iff] at hf
  dsimp
  infer_instance

Depends on / 依赖: infer_instance, mem_quasiIso_iff
-/
lemma HomologicalComplex.homologyFunctor_inverts_quasiIso (i : ι) :
    (quasiIso C c).IsInvertedBy (homologyFunctor C c i) := fun _ _ _ hf => by
  rw [mem_quasiIso_iff] at hf
  dsimp
  infer_instance

variable [(HomologicalComplex.quasiIso C c).HasLocalization]

/--
Definition of `HomologicalComplexUpToQuasiIso` / `HomologicalComplexUpToQuasiIso` 的定义

English:
abbreviation HomologicalComplexUpToQuasiIso
  body: (HomologicalComplex.quasiIso C c).Localization'

中文:
缩写 HomologicalComplexUpToQuasiIso
  定义体: (HomologicalComplex.quasiIso C c).Localization'

Depends on / 依赖: HomologicalComplex, HomologicalComplex.quasiIso, Localization, quasiIso
-/
abbrev HomologicalComplexUpToQuasiIso := (HomologicalComplex.quasiIso C c).Localization'

variable {C c} in
/--
Definition of `HomologicalComplexUpToQuasiIso.Q` / `HomologicalComplexUpToQuasiIso.Q` 的定义

English:
abbreviation HomologicalComplexUpToQuasiIso.Q
  signature: :
  body: (HomologicalComplex.quasiIso C c).Q'

中文:
缩写 HomologicalComplexUpToQuasiIso.Q
  签名: :
  定义体: (HomologicalComplex.quasiIso C c).Q'

Depends on / 依赖: HomologicalComplex, HomologicalComplex.quasiIso, quasiIso
-/
abbrev HomologicalComplexUpToQuasiIso.Q :
    HomologicalComplex C c ⥤ HomologicalComplexUpToQuasiIso C c :=
  (HomologicalComplex.quasiIso C c).Q'

namespace HomologicalComplexUpToQuasiIso

/--
Definition of `homologyFunctor` / `homologyFunctor` 的定义

English:
definition homologyFunctor
  signature: (i : ι)
  body: Localization.lift _ (HomologicalComplex.homologyFunctor_inverts_quasiIso C c i) Q

中文:
定义 homologyFunctor
  签名: (i : ι)
  定义体: Localization.lift _ (HomologicalComplex.homologyFunctor_inverts_quasiIso C c i) Q

Depends on / 依赖: F.map_comp, Functor, Functor.mapIso, HomologicalComplex, HomologicalComplex.homologyFunctor_inverts_quasiIso, Iso.symm, Iso.trans, Localization, Localization.lift, RightHomologyData, RightHomologyData.map_rightHomologyMap, RightHomologyData.rightHomologyIso_hom_naturality_assoc, RightHomologyData.rightHomologyIso_inv_naturality, homologyData, homologyFunctor_inverts_quasiIso, mapHomologyIso, mapIso, map_comp, map_rightHomologyMap, right.map
-/
noncomputable def homologyFunctor (i : ι) : HomologicalComplexUpToQuasiIso C c ⥤ C :=
  Localization.lift _ (HomologicalComplex.homologyFunctor_inverts_quasiIso C c i) Q

/--
Definition of `homologyFunctorFactors` / `homologyFunctorFactors` 的定义

English:
definition homologyFunctorFactors
  signature: (i : ι)
  body: Localization.fac _ (HomologicalComplex.homologyFunctor_inverts_quasiIso C c i) Q

中文:
定义 homologyFunctorFactors
  签名: (i : ι)
  定义体: Localization.fac _ (HomologicalComplex.homologyFunctor_inverts_quasiIso C c i) Q

Depends on / 依赖: HomologicalComplex, HomologicalComplex.homologyFunctor_inverts_quasiIso, Iso.hom_inv_id, Iso.hom_inv_id_assoc, Localization, Localization.fac, _hom_naturality_assoc, cancel_epi, comp_id, hom_inv_id, hom_inv_id_assoc, homologyFunctor_inverts_quasiIso, mapHomologyIso
-/
noncomputable def homologyFunctorFactors (i : ι) :
    Q ⋙ homologyFunctor C c i ≅ HomologicalComplex.homologyFunctor C c i :=
  Localization.fac _ (HomologicalComplex.homologyFunctor_inverts_quasiIso C c i) Q

variable {C c}

set_option backward.defeqAttrib.useBackward true in
/--
lemma `isIso_Q_map_iff_mem_quasiIso` / 引理 `isIso_Q_map_iff_mem_quasiIso`

English:
lemma isIso_Q_map_iff_mem_quasiIso
  given: {K L : HomologicalComplex C c} (f : K ⟶ L)
  proof: by
  constructor
  · intro h
    rw [HomologicalComplex.mem_quasiIso_iff]; rw [quasiIso_iff]
    intro i
    rw [quasiIsoAt_iff_isIso_homologyMap]
    refine (NatIso.isIso_map_iff (homologyFunctorFactors C c i) f).1 ?_
    dsimp
    infer_instance
  · intro h
    exact Localization.inverts Q (HomologicalComplex.quasiIso C c) _ h

中文:
引理 isIso_Q_map_iff_mem_quasiIso
  条件: {K L : 同调复形 C c} (f : K ⟶ L)
  证明: by
  constructor
  · intro h
    rw [HomologicalComplex.mem_quasiIso_iff]; rw [quasiIso_iff]
    intro i
    rw [quasiIsoAt_iff_isIso_homologyMap]
    refine (NatIso.isIso_map_iff (homologyFunctorFactors C c i) f).1 ?_
    dsimp
    infer_instance
  · intro h
    exact Localization.inverts Q (HomologicalComplex.quasiIso C c) _ h

Depends on / 依赖: Functor, Functor.mapIso, Functor.mapShortCompl, Functor.map_comp, HomologicalComplex, HomologicalComplex.mem_quasiIso_iff, HomologicalComplex.quasiIso, Iso.refl, Iso.symm, Iso.trans, LeftHomologyData, LeftHomologyData.homologyIso, LeftHomologyData.leftHomologyIso, Localization, Localization.inverts, NatIso, NatIso.isIso_map_iff, RightHomologyData, RightHomologyData.homologyIso, RightHomologyData.map_H
-/
lemma isIso_Q_map_iff_mem_quasiIso {K L : HomologicalComplex C c} (f : K ⟶ L) :
    IsIso (Q.map f) ↔ HomologicalComplex.quasiIso C c f := by
  constructor
  · intro h
    rw [HomologicalComplex.mem_quasiIso_iff]; rw [quasiIso_iff]
    intro i
    rw [quasiIsoAt_iff_isIso_homologyMap]
    refine (NatIso.isIso_map_iff (homologyFunctorFactors C c i) f).1 ?_
    dsimp
    infer_instance
  · intro h
    exact Localization.inverts Q (HomologicalComplex.quasiIso C c) _ h

end HomologicalComplexUpToQuasiIso

end

section

variable (C : Type*) [Category* C] {ι : Type*} (c : ComplexShape ι) [Preadditive C]
  [CategoryWithHomology C]

/--
lemma `HomologicalComplexUpToQuasiIso.Q_inverts_homotopyEquivalences` / 引理 `HomologicalComplexUpToQuasiIso.Q_inverts_homotopyEquivalences`

English:
lemma HomologicalComplexUpToQuasiIso.Q_inverts_homotopyEquivalences
  proof: MorphismProperty.IsInvertedBy.of_le _ _ _
    (Localization.inverts Q (HomologicalComplex.quasiIso C c))
    (homotopyEquivalences_le_quasiIso C c)

中文:
引理 HomologicalComplexUpToQuasiIso.Q_inverts_homotopyEquivalences
  证明: MorphismProperty.IsInvertedBy.of_le _ _ _
    (Localization.inverts Q (HomologicalComplex.quasiIso C c))
    (homotopyEquivalences_le_quasiIso C c)

Depends on / 依赖: HomologicalComplex, HomologicalComplex.quasiIso, IsInvertedBy, Localization, Localization.inverts, MorphismProperty, MorphismProperty.IsInvertedBy.of_le, homotopyEquivalences_le_quasiIso, inverts, of_le, quasiIso
-/
lemma HomologicalComplexUpToQuasiIso.Q_inverts_homotopyEquivalences
    [(HomologicalComplex.quasiIso C c).HasLocalization] :
    (HomologicalComplex.homotopyEquivalences C c).IsInvertedBy
      HomologicalComplexUpToQuasiIso.Q :=
  MorphismProperty.IsInvertedBy.of_le _ _ _
    (Localization.inverts Q (HomologicalComplex.quasiIso C c))
    (homotopyEquivalences_le_quasiIso C c)

namespace HomotopyCategory

/--
Definition of `quasiIso` / `quasiIso` 的定义

English:
definition quasiIso
  signature: : MorphismProperty (HomotopyCategory C c)
  body: fun _ _ f => forall (i : ι), IsIso ((homologyFunctor C c i).map f)

中文:
定义 quasiIso
  签名: : MorphismProperty (HomotopyCategory C c)
  定义体: fun _ _ f => forall (i : ι), IsIso ((homologyFunctor C c i).map f)

Depends on / 依赖: homologyFunctor
-/
def quasiIso : MorphismProperty (HomotopyCategory C c) :=
  fun _ _ f => forall (i : ι), IsIso ((homologyFunctor C c i).map f)

variable {C c}

/--
lemma `mem_quasiIso_iff` / 引理 `mem_quasiIso_iff`

English:
lemma mem_quasiIso_iff
  given: {X Y : HomotopyCategory C c} (f : X ⟶ Y)
  proof: by
  rfl

中文:
引理 mem_quasiIso_iff
  条件: {X Y : HomotopyCategory C c} (f : X ⟶ Y)
  证明: by
  rfl
-/
lemma mem_quasiIso_iff {X Y : HomotopyCategory C c} (f : X ⟶ Y) :
    quasiIso C c f ↔ forall (n : ι), IsIso ((homologyFunctor _ _ n).map f) := by
  rfl

set_option backward.defeqAttrib.useBackward true in
/--
lemma `quotient_map_mem_quasiIso_iff` / 引理 `quotient_map_mem_quasiIso_iff`

English:
lemma quotient_map_mem_quasiIso_iff
  given: {K L : HomologicalComplex C c} (f : K ⟶ L)
  proof: by
  have eq := fun (i : ι) => NatIso.isIso_map_iff (homologyFunctorFactors C c i) f
  dsimp at eq
  simp only [HomologicalComplex.mem_quasiIso_iff, mem_quasiIso_iff, quasiIso_iff,
    quasiIsoAt_iff_isIso_homologyMap, eq]

中文:
引理 quotient_map_mem_quasiIso_iff
  条件: {K L : 同调复形 C c} (f : K ⟶ L)
  证明: by
  have eq := fun (i : ι) => NatIso.isIso_map_iff (homologyFunctorFactors C c i) f
  dsimp at eq
  simp only [HomologicalComplex.mem_quasiIso_iff, mem_quasiIso_iff, quasiIso_iff,
    quasiIsoAt_iff_isIso_homologyMap, eq]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.mem_quasiIso_iff, NatIso, NatIso.isIso_map_iff, homologyFunctorFactors, isIso_map_iff, mem_quasiIso_iff, quasiIsoAt_iff_isIso_homologyMap, quasiIso_iff
-/
lemma quotient_map_mem_quasiIso_iff {K L : HomologicalComplex C c} (f : K ⟶ L) :
    quasiIso C c ((quotient C c).map f) ↔ HomologicalComplex.quasiIso C c f := by
  have eq := fun (i : ι) => NatIso.isIso_map_iff (homologyFunctorFactors C c i) f
  dsimp at eq
  simp only [HomologicalComplex.mem_quasiIso_iff, mem_quasiIso_iff, quasiIso_iff,
    quasiIsoAt_iff_isIso_homologyMap, eq]

variable (C c)

/--
Instance `respectsIso_quasiIso` / 实例 `respectsIso_quasiIso`

English:
instance respectsIso_quasiIso
  signature: : (quasiIso C c).RespectsIso
  body: by
  apply MorphismProperty.RespectsIso.of_respects_arrow_iso
  intro f g e hf i
  exact ((MorphismProperty.isomorphisms C).arrow_mk_iso_iff
    ((homologyFunctor C c i).mapArrow.mapIso e)).1 (hf i)

中文:
实例 respectsIso_quasiIso
  签名: : (quasiIso C c).RespectsIso
  定义体: by
  apply MorphismProperty.RespectsIso.of_respects_arrow_iso
  intro f g e hf i
  exact ((MorphismProperty.isomorphisms C).arrow_mk_iso_iff
    ((homologyFunctor C c i).mapArrow.mapIso e)).1 (hf i)

Depends on / 依赖: MorphismProperty, MorphismProperty.RespectsIso.of_respects_arrow_iso, MorphismProperty.isomorphisms, RespectsIso, arrow_mk_iso_iff, homologyFunctor, isomorphisms, mapArrow, mapArrow.mapIso, mapIso, of_respects_arrow_iso
-/
instance respectsIso_quasiIso : (quasiIso C c).RespectsIso := by
  apply MorphismProperty.RespectsIso.of_respects_arrow_iso
  intro f g e hf i
  exact ((MorphismProperty.isomorphisms C).arrow_mk_iso_iff
    ((homologyFunctor C c i).mapArrow.mapIso e)).1 (hf i)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (quasiIso C c).IsMultiplicative
  body: by
    rw [mem_quasiIso_iff]
    infer_instance
  comp_mem f g hf hg := by
    rw [mem_quasiIso_iff] at hf hg ⊢
    simp only [Functor.map_comp]
    infer_instance

中文:
实例 :
  签名: (quasiIso C c).是Multiplicative
  定义体: by
    rw [mem_quasiIso_iff]
    infer_instance
  comp_mem f g hf hg := by
    rw [mem_quasiIso_iff] at hf hg ⊢
    simp only [Functor.map_comp]
    infer_instance

Depends on / 依赖: Functor, Functor.map_comp, comp_mem, infer_instance, map_comp, mem_quasiIso_iff
-/
instance : (quasiIso C c).IsMultiplicative where
  id_mem K := by
    rw [mem_quasiIso_iff]
    infer_instance
  comp_mem f g hf hg := by
    rw [mem_quasiIso_iff] at hf hg ⊢
    simp only [Functor.map_comp]
    infer_instance

/--
lemma `homologyFunctor_inverts_quasiIso` / 引理 `homologyFunctor_inverts_quasiIso`

English:
lemma homologyFunctor_inverts_quasiIso
  given: (i : ι)
  proof: fun _ _ _ hf => hf i

中文:
引理 homologyFunctor_inverts_quasiIso
  条件: (i : ι)
  证明: fun _ _ _ hf => hf i
-/
lemma homologyFunctor_inverts_quasiIso (i : ι) :
    (quasiIso C c).IsInvertedBy (homologyFunctor C c i) := fun _ _ _ hf => hf i

set_option backward.isDefEq.respectTransparency false in
/--
lemma `quasiIso_eq_quasiIso_map_quotient` / 引理 `quasiIso_eq_quasiIso_map_quotient`

English:
lemma quasiIso_eq_quasiIso_map_quotient
  proof: by
  ext ⟨K⟩ ⟨L⟩ f
  obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient C c).map_surjective f
  constructor
  · intro hf
    rw [quotient_map_mem_quasiIso_iff] at hf
    exact MorphismProperty.map_mem_map _ _ _ hf
  · rintro ⟨K', L', g, h, ⟨e⟩⟩
    rw [← quotient_map_mem_quasiIso_iff] at h
    exact ((quasiIso C c).arrow_mk_iso_iff e).1 h

中文:
引理 quasiIso_eq_quasiIso_map_quotient
  证明: by
  ext ⟨K⟩ ⟨L⟩ f
  obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient C c).map_surjective f
  constructor
  · intro hf
    rw [quotient_map_mem_quasiIso_iff] at hf
    exact MorphismProperty.map_mem_map _ _ _ hf
  · rintro ⟨K', L', g, h, ⟨e⟩⟩
    rw [← quotient_map_mem_quasiIso_iff] at h
    exact ((quasiIso C c).arrow_mk_iso_iff e).1 h

Depends on / 依赖: HomotopyCategory, HomotopyCategory.quotient, MorphismProperty, MorphismProperty.map_mem_map, arrow_mk_iso_iff, map_mem_map, map_surjective, quasiIso, quotient, quotient_map_mem_quasiIso_iff
-/
lemma quasiIso_eq_quasiIso_map_quotient :
    quasiIso C c = (HomologicalComplex.quasiIso C c).map (quotient C c) := by
  ext ⟨K⟩ ⟨L⟩ f
  obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient C c).map_surjective f
  constructor
  · intro hf
    rw [quotient_map_mem_quasiIso_iff] at hf
    exact MorphismProperty.map_mem_map _ _ _ hf
  · rintro ⟨K', L', g, h, ⟨e⟩⟩
    rw [← quotient_map_mem_quasiIso_iff] at h
    exact ((quasiIso C c).arrow_mk_iso_iff e).1 h

end HomotopyCategory

/--
Definition of `ComplexShape.QFactorsThroughHomotopy` / `ComplexShape.QFactorsThroughHomotopy` 的定义

English:
class ComplexShape.QFactorsThroughHomotopy
  parameters: {ι : Type*} (c : ComplexShape ι)
  axioms and operations (1):
    - areEqualizedByLocalization({K L : HomologicalComplex C c} {f g : K ⟶ L} (h : Homotopy f g)) : AreEqualizedByLocalization (HomologicalComplex.quasiIso C c) f g

中文:
类 余mplexShape.QFactorsThroughHomotopy
  参数: {ι : 类型} (c : 余mplexShape ι)
  公理与运算 (1 个):
    - areEqualizedByLocalization({K L : 同调复形 C c} {f g : K ⟶ L} (h : 同伦 f g)) : AreEqualizedByLocalization (同调复形.quasiIso C c) f g
-/
class ComplexShape.QFactorsThroughHomotopy {ι : Type*} (c : ComplexShape ι)
    (C : Type*) [Category* C] [Preadditive C]
    [CategoryWithHomology C] : Prop where
  areEqualizedByLocalization {K L : HomologicalComplex C c} {f g : K ⟶ L} (h : Homotopy f g) :
    AreEqualizedByLocalization (HomologicalComplex.quasiIso C c) f g

namespace HomologicalComplexUpToQuasiIso

variable {C c}
variable [(HomologicalComplex.quasiIso C c).HasLocalization] [c.QFactorsThroughHomotopy C]

/--
lemma `Q_map_eq_of_homotopy` / 引理 `Q_map_eq_of_homotopy`

English:
lemma Q_map_eq_of_homotopy
  given: {K L : HomologicalComplex C c} {f g : K ⟶ L} (h : Homotopy f g)
  proof: (ComplexShape.QFactorsThroughHomotopy.areEqualizedByLocalization h).map_eq Q

中文:
引理 Q_map_eq_of_homotopy
  条件: {K L : 同调复形 C c} {f g : K ⟶ L} (h : 同伦 f g)
  证明: (ComplexShape.QFactorsThroughHomotopy.areEqualizedByLocalization h).map_eq Q

Depends on / 依赖: ComplexShape, ComplexShape.QFactorsThroughHomotopy.areEqualizedByLocalization, QFactorsThroughHomotopy, areEqualizedByLocalization, map_eq
-/
lemma Q_map_eq_of_homotopy {K L : HomologicalComplex C c} {f g : K ⟶ L} (h : Homotopy f g) :
    Q.map f = Q.map g :=
  (ComplexShape.QFactorsThroughHomotopy.areEqualizedByLocalization h).map_eq Q

/--
Definition of `Qh` / `Qh` 的定义

English:
definition Qh
  signature: : HomotopyCategory C c ⥤ HomologicalComplexUpToQuasiIso C c
  body: CategoryTheory.Quotient.lift _ HomologicalComplexUpToQuasiIso.Q (by
    intro K L f g ⟨h⟩
    exact Q_map_eq_of_homotopy h)

中文:
定义 Qh
  签名: : HomotopyCategory C c ⥤ HomologicalComplexUpToQuasiIso C c
  定义体: CategoryTheory.Quotient.lift _ HomologicalComplexUpToQuasiIso.Q (by
    intro K L f g ⟨h⟩
    exact Q_map_eq_of_homotopy h)

Depends on / 依赖: CategoryTheory, CategoryTheory.Quotient.lift, HomologicalComplexUpToQuasiIso, HomologicalComplexUpToQuasiIso.Q, Q_map_eq_of_homotopy, Quotient
-/
def Qh : HomotopyCategory C c ⥤ HomologicalComplexUpToQuasiIso C c :=
  CategoryTheory.Quotient.lift _ HomologicalComplexUpToQuasiIso.Q (by
    intro K L f g ⟨h⟩
    exact Q_map_eq_of_homotopy h)

variable (C c)

/--
Definition of `quotientCompQhIso` / `quotientCompQhIso` 的定义

English:
definition quotientCompQhIso
  signature: : HomotopyCategory.quotient C c ⋙ Qh ≅ Q
  body: by
  apply Quotient.lift.isLift

中文:
定义 quotientCompQhIso
  签名: : HomotopyCategory.quotient C c ⋙ Qh ≅ Q
  定义体: by
  apply Quotient.lift.isLift

Depends on / 依赖: Quotient, Quotient.lift.isLift, isLift
-/
def quotientCompQhIso : HomotopyCategory.quotient C c ⋙ Qh ≅ Q := by
  apply Quotient.lift.isLift

set_option backward.isDefEq.respectTransparency false in
/--
lemma `Qh_inverts_quasiIso` / 引理 `Qh_inverts_quasiIso`

English:
lemma Qh_inverts_quasiIso
  statement: (HomotopyCategory.quasiIso C c).IsInvertedBy Qh
  proof: by
  rintro ⟨K⟩ ⟨L⟩ φ
  obtain ⟨φ, rfl⟩ := (HomotopyCategory.quotient C c).map_surjective φ
  rw [HomotopyCategory.quotient_map_mem_quasiIso_iff φ]; rw [← HomologicalComplexUpToQuasiIso.isIso_Q_map_iff_mem_quasiIso]
  exact (NatIso.isIso_map_iff (quotientCompQhIso C c) φ).2

中文:
引理 Qh_inverts_quasiIso
  结论: (HomotopyCategory.quasiIso C c).IsInvertedBy Qh
  证明: by
  rintro ⟨K⟩ ⟨L⟩ φ
  obtain ⟨φ, rfl⟩ := (HomotopyCategory.quotient C c).map_surjective φ
  rw [HomotopyCategory.quotient_map_mem_quasiIso_iff φ]; rw [← HomologicalComplexUpToQuasiIso.isIso_Q_map_iff_mem_quasiIso]
  exact (NatIso.isIso_map_iff (quotientCompQhIso C c) φ).2

Depends on / 依赖: HomologicalComplexUpToQuasiIso, HomologicalComplexUpToQuasiIso.isIso_Q_map_iff_mem_quasiIso, HomotopyCategory, HomotopyCategory.quotient, HomotopyCategory.quotient_map_mem_quasiIso_iff, NatIso, NatIso.isIso_map_iff, isIso_Q_map_iff_mem_quasiIso, isIso_map_iff, map_surjective, quotient, quotientCompQhIso, quotient_map_mem_quasiIso_iff
-/
lemma Qh_inverts_quasiIso : (HomotopyCategory.quasiIso C c).IsInvertedBy Qh := by
  rintro ⟨K⟩ ⟨L⟩ φ
  obtain ⟨φ, rfl⟩ := (HomotopyCategory.quotient C c).map_surjective φ
  rw [HomotopyCategory.quotient_map_mem_quasiIso_iff φ]; rw [← HomologicalComplexUpToQuasiIso.isIso_Q_map_iff_mem_quasiIso]
  exact (NatIso.isIso_map_iff (quotientCompQhIso C c) φ).2

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (HomotopyCategory.quotient C c ⋙ Qh).IsLocalization
  body: Functor.IsLocalization.of_iso _ (quotientCompQhIso C c).symm

中文:
实例 :
  签名: (HomotopyCategory.quotient C c ⋙ Qh).是Localization
  定义体: Functor.IsLocalization.of_iso _ (quotientCompQhIso C c).symm

Depends on / 依赖: Functor, Functor.IsLocalization.of_iso, IsLocalization, of_iso, quotientCompQhIso
-/
instance : (HomotopyCategory.quotient C c ⋙ Qh).IsLocalization
    (HomologicalComplex.quasiIso C c) :=
  Functor.IsLocalization.of_iso _ (quotientCompQhIso C c).symm

/--
Definition of `homologyFunctorFactorsh` / `homologyFunctorFactorsh` 的定义

English:
definition homologyFunctorFactorsh
  signature: (i : ι)
  body: Quotient.natIsoLift _ ((Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (quotientCompQhIso C c) _ ≪≫
    homologyFunctorFactors C c i ≪≫ (HomotopyCategory.homologyFunctorFactors C c i).symm)

中文:
定义 homologyFunctorFactorsh
  签名: (i : ι)
  定义体: Quotient.natIsoLift _ ((Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (quotientCompQhIso C c) _ ≪≫
    homologyFunctorFactors C c i ≪≫ (HomotopyCategory.homologyFunctorFactors C c i).symm)

Depends on / 依赖: Functor, Functor.associator, Functor.isoWhiskerRight, HomotopyCategory, HomotopyCategory.homologyFunctorFactors, Quotient, Quotient.natIsoLift, associator, homologyFunctorFactors, isoWhiskerRight, natIsoLift, quotientCompQhIso
-/
noncomputable def homologyFunctorFactorsh (i : ι) :
    Qh ⋙ homologyFunctor C c i ≅ HomotopyCategory.homologyFunctor C c i :=
  Quotient.natIsoLift _ ((Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (quotientCompQhIso C c) _ ≪≫
    homologyFunctorFactors C c i ≪≫ (HomotopyCategory.homologyFunctorFactors C c i).symm)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `homologyFunctorFactorsh_hom_app_quotient_obj` / 引理 `homologyFunctorFactorsh_hom_app_quotient_obj`

English:
lemma homologyFunctorFactorsh_hom_app_quotient_obj
  proof: (Quotient.natTransLift_app ..).trans (by simp)

中文:
引理 homologyFunctorFactorsh_hom_app_quotient_obj
  证明: (Quotient.natTransLift_app ..).trans (by simp)

Depends on / 依赖: Quotient, Quotient.natTransLift_app, natTransLift_app
-/
lemma homologyFunctorFactorsh_hom_app_quotient_obj
    (K : HomologicalComplex C c) (i : ι) :
    (homologyFunctorFactorsh C c i).hom.app ((HomotopyCategory.quotient _ _).obj K) =
    (homologyFunctor C c i).map ((quotientCompQhIso C c).hom.app K) ≫
      (homologyFunctorFactors C c i).hom.app K ≫
        (HomotopyCategory.homologyFunctorFactors C c i).inv.app K :=
  (Quotient.natTransLift_app ..).trans (by simp)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `homologyFunctorFactorsh_inv_app_quotient_obj` / 引理 `homologyFunctorFactorsh_inv_app_quotient_obj`

English:
lemma homologyFunctorFactorsh_inv_app_quotient_obj
  proof: (Quotient.natTransLift_app ..).trans (by simp)

中文:
引理 homologyFunctorFactorsh_inv_app_quotient_obj
  证明: (Quotient.natTransLift_app ..).trans (by simp)

Depends on / 依赖: Quotient, Quotient.natTransLift_app, natTransLift_app
-/
lemma homologyFunctorFactorsh_inv_app_quotient_obj
    (K : HomologicalComplex C c) (i : ι) :
    (homologyFunctorFactorsh C c i).inv.app ((HomotopyCategory.quotient _ _).obj K) =
    (HomotopyCategory.homologyFunctorFactors C c i).hom.app K ≫
      (homologyFunctorFactors C c i).inv.app K ≫
        (homologyFunctor C c i).map ((quotientCompQhIso C c).inv.app K) :=
  (Quotient.natTransLift_app ..).trans (by simp)

section

variable [(HomotopyCategory.quotient C c).IsLocalization
  (HomologicalComplex.homotopyEquivalences C c)]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HomologicalComplexUpToQuasiIso.Qh.IsLocalization (HomotopyCategory.quasiIso C c)
  body: Functor.IsLocalization.of_comp (HomotopyCategory.quotient C c)
    Qh (HomologicalComplex.homotopyEquivalences C c)
    (HomotopyCategory.quasiIso C c) (HomologicalComplex.quasiIso C c)
    (homotopyEquivalences_le_quasiIso C c)
    (HomotopyCategory.quasiIso_eq_quasiIso_map_quotient C c)

中文:
实例 :
  签名: HomologicalComplexUpToQuasiIso.Qh.是Localization (HomotopyCategory.quasiIso C c)
  定义体: Functor.IsLocalization.of_comp (HomotopyCategory.quotient C c)
    Qh (HomologicalComplex.homotopyEquivalences C c)
    (HomotopyCategory.quasiIso C c) (HomologicalComplex.quasiIso C c)
    (homotopyEquivalences_le_quasiIso C c)
    (HomotopyCategory.quasiIso_eq_quasiIso_map_quotient C c)

Depends on / 依赖: Functor, Functor.IsLocalization.of_comp, HomologicalComplex, HomologicalComplex.homotopyEquivalences, HomologicalComplex.quasiIso, HomotopyCategory, HomotopyCategory.quasiIso, HomotopyCategory.quasiIso_eq_quasiIso_map_quotient, HomotopyCategory.quotient, IsLocalization, homotopyEquivalences, homotopyEquivalences_le_quasiIso, of_comp, quasiIso, quasiIso_eq_quasiIso_map_quotient, quotient
-/
instance : HomologicalComplexUpToQuasiIso.Qh.IsLocalization (HomotopyCategory.quasiIso C c) :=
  Functor.IsLocalization.of_comp (HomotopyCategory.quotient C c)
    Qh (HomologicalComplex.homotopyEquivalences C c)
    (HomotopyCategory.quasiIso C c) (HomologicalComplex.quasiIso C c)
    (homotopyEquivalences_le_quasiIso C c)
    (HomotopyCategory.quasiIso_eq_quasiIso_map_quotient C c)

end

end HomologicalComplexUpToQuasiIso

end

section Cylinder

variable {ι : Type*} (c : ComplexShape ι) (hc : forall j, exists i, c.Rel i j)
  (C : Type*) [Category* C] [Preadditive C] [HasBinaryBiproducts C]
include hc

/--
Definition of `ComplexShape.strictUniversalPropertyFixedTargetQuotient` / `ComplexShape.strictUniversalPropertyFixedTargetQuotient` 的定义

English:
definition ComplexShape.strictUniversalPropertyFixedTargetQuotient
  signature: (E : Type*) [Category* E]
  body: HomotopyCategory.quotient_inverts_homotopyEquivalences C c
  lift F hF := CategoryTheory.Quotient.lift _ F (by
    intro K L f g ⟨h⟩
    have : DecidableRel c.Rel := by classical infer_instance
    exact h.map_eq_of_inverts_homotopyEquivalences hc F hF)
  fac _ _ := rfl
  uniq _ _ h := Quotient.lift_unique' _ _ _ h

中文:
定义 余mplexShape.strictUniversalPropertyFixedTargetQuotient
  签名: (E : 类型) [范畴* E]
  定义体: HomotopyCategory.quotient_inverts_homotopyEquivalences C c
  lift F hF := CategoryTheory.Quotient.lift _ F (by
    intro K L f g ⟨h⟩
    have : DecidableRel c.Rel := by classical infer_instance
    exact h.map_eq_of_inverts_homotopyEquivalences hc F hF)
  fac _ _ := rfl
  uniq _ _ h := Quotient.lift_unique' _ _ _ h

Depends on / 依赖: HomotopyCategory, HomotopyCategory.quotient_inverts_homotopyEquivalences, quotient_inverts_homotopyEquivalences
-/
def ComplexShape.strictUniversalPropertyFixedTargetQuotient (E : Type*) [Category* E] :
    Localization.StrictUniversalPropertyFixedTarget (HomotopyCategory.quotient C c)
      (HomologicalComplex.homotopyEquivalences C c) E where
  inverts := HomotopyCategory.quotient_inverts_homotopyEquivalences C c
  lift F hF := CategoryTheory.Quotient.lift _ F (by
    intro K L f g ⟨h⟩
    have : DecidableRel c.Rel := by classical infer_instance
    exact h.map_eq_of_inverts_homotopyEquivalences hc F hF)
  fac _ _ := rfl
  uniq _ _ h := Quotient.lift_unique' _ _ _ h

/--
lemma `ComplexShape.quotient_isLocalization` / 引理 `ComplexShape.quotient_isLocalization`

English:
lemma ComplexShape.quotient_isLocalization
  proof: by
  apply Functor.IsLocalization.mk'
  all_goals apply c.strictUniversalPropertyFixedTargetQuotient hc

中文:
引理 余mplexShape.quotient_isLocalization
  证明: by
  apply Functor.IsLocalization.mk'
  all_goals apply c.strictUniversalPropertyFixedTargetQuotient hc

Depends on / 依赖: Functor, Functor.IsLocalization.mk, IsLocalization, all_goals, c.strictUniversalPropertyFixedTargetQuotient, strictUniversalPropertyFixedTargetQuotient
-/
lemma ComplexShape.quotient_isLocalization :
    (HomotopyCategory.quotient C c).IsLocalization
      (HomologicalComplex.homotopyEquivalences _ _) := by
  apply Functor.IsLocalization.mk'
  all_goals apply c.strictUniversalPropertyFixedTargetQuotient hc

/--
lemma `ComplexShape.QFactorsThroughHomotopy_of_exists_prev` / 引理 `ComplexShape.QFactorsThroughHomotopy_of_exists_prev`

English:
lemma ComplexShape.QFactorsThroughHomotopy_of_exists_prev
  given: [CategoryWithHomology C]
  proof: by
    exact h.map_eq_of_inverts_homotopyEquivalences hc _
      (MorphismProperty.IsInvertedBy.of_le _ _ _
        (Localization.inverts _ (HomologicalComplex.quasiIso C _))
        (homotopyEquivalences_le_quasiIso C _))

中文:
引理 余mplexShape.QFactorsThroughHomotopy_of_存在_prev
  条件: [带同调范畴 C]
  证明: by
    exact h.map_eq_of_inverts_homotopyEquivalences hc _
      (MorphismProperty.IsInvertedBy.of_le _ _ _
        (Localization.inverts _ (HomologicalComplex.quasiIso C _))
        (homotopyEquivalences_le_quasiIso C _))

Depends on / 依赖: HomologicalComplex, HomologicalComplex.quasiIso, IsInvertedBy, Localization, Localization.inverts, MorphismProperty, MorphismProperty.IsInvertedBy.of_le, h.map_eq_of_inverts_homotopyEquivalences, homotopyEquivalences_le_quasiIso, inverts, map_eq_of_inverts_homotopyEquivalences, of_le, quasiIso
-/
lemma ComplexShape.QFactorsThroughHomotopy_of_exists_prev [CategoryWithHomology C] :
    c.QFactorsThroughHomotopy C where
  areEqualizedByLocalization {K L f g} h := by
    exact h.map_eq_of_inverts_homotopyEquivalences hc _
      (MorphismProperty.IsInvertedBy.of_le _ _ _
        (Localization.inverts _ (HomologicalComplex.quasiIso C _))
        (homotopyEquivalences_le_quasiIso C _))

end Cylinder

section ChainComplex

variable (C : Type*) [Category* C] {ι : Type*} [Preadditive C]
  [AddRightCancelSemigroup ι] [One ι] [HasBinaryBiproducts C]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (HomotopyCategory.quotient C (ComplexShape.down ι)).IsLocalization
  body: (ComplexShape.down ι).quotient_isLocalization (fun _ => ⟨_, rfl⟩) C

中文:
实例 :
  签名: (HomotopyCategory.quotient C (余mplexShape.down ι)).是Localization
  定义体: (ComplexShape.down ι).quotient_isLocalization (fun _ => ⟨_, rfl⟩) C

Depends on / 依赖: ComplexShape, ComplexShape.down, quotient_isLocalization
-/
instance : (HomotopyCategory.quotient C (ComplexShape.down ι)).IsLocalization
    (HomologicalComplex.homotopyEquivalences _ _) :=
  (ComplexShape.down ι).quotient_isLocalization (fun _ => ⟨_, rfl⟩) C

variable [CategoryWithHomology C]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (ComplexShape.down ι).QFactorsThroughHomotopy C
  body: (ComplexShape.down ι).QFactorsThroughHomotopy_of_exists_prev (fun _ => ⟨_, rfl⟩) C

example [(HomologicalComplex.quasiIso C (ComplexShape.down ι)).HasLocalization] :
    HomologicalComplexUpToQuasiIso.Qh.IsLocalization
    (HomotopyCategory.quasiIso C (ComplexShape.down ι)) :=
  inferInstance

中文:
实例 :
  签名: (余mplexShape.down ι).QFactorsThroughHomotopy C
  定义体: (ComplexShape.down ι).QFactorsThroughHomotopy_of_exists_prev (fun _ => ⟨_, rfl⟩) C

example [(HomologicalComplex.quasiIso C (ComplexShape.down ι)).HasLocalization] :
    HomologicalComplexUpToQuasiIso.Qh.IsLocalization
    (HomotopyCategory.quasiIso C (ComplexShape.down ι)) :=
  inferInstance

Depends on / 依赖: ComplexShape, ComplexShape.down, QFactorsThroughHomotopy_of_exists_prev
-/
instance : (ComplexShape.down ι).QFactorsThroughHomotopy C :=
  (ComplexShape.down ι).QFactorsThroughHomotopy_of_exists_prev (fun _ => ⟨_, rfl⟩) C

example [(HomologicalComplex.quasiIso C (ComplexShape.down ι)).HasLocalization] :
    HomologicalComplexUpToQuasiIso.Qh.IsLocalization
    (HomotopyCategory.quasiIso C (ComplexShape.down ι)) :=
  inferInstance

/- By duality, the results obtained here for chain complexes could be dualized in
order to obtain similar results for general cochain complexes. However, the case of
interest for the construction of the derived category (cochain complexes indexed by `ℤ`)
can also be obtained directly, which is done below. -/

end ChainComplex

section CochainComplex

variable (C : Type*) [Category* C] {ι : Type*} [Preadditive C] [HasBinaryBiproducts C]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (HomotopyCategory.quotient C (ComplexShape.up Int)).IsLocalization
  body: (ComplexShape.up Int).quotient_isLocalization (fun n => ⟨n - 1, by simp⟩) C

中文:
实例 :
  签名: (HomotopyCategory.quotient C (余mplexShape.up 整数)).是Localization
  定义体: (ComplexShape.up Int).quotient_isLocalization (fun n => ⟨n - 1, by simp⟩) C

Depends on / 依赖: ComplexShape, ComplexShape.up, quotient_isLocalization
-/
instance : (HomotopyCategory.quotient C (ComplexShape.up Int)).IsLocalization
    (HomologicalComplex.homotopyEquivalences _ _) :=
  (ComplexShape.up Int).quotient_isLocalization (fun n => ⟨n - 1, by simp⟩) C

variable [CategoryWithHomology C]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (ComplexShape.up Int).QFactorsThroughHomotopy C
  body: (ComplexShape.up Int).QFactorsThroughHomotopy_of_exists_prev (fun n => ⟨n - 1, by simp⟩) C

中文:
实例 :
  签名: (余mplexShape.up 整数).QFactorsThroughHomotopy C
  定义体: (ComplexShape.up Int).QFactorsThroughHomotopy_of_exists_prev (fun n => ⟨n - 1, by simp⟩) C

Depends on / 依赖: ComplexShape, ComplexShape.up, QFactorsThroughHomotopy_of_exists_prev
-/
instance : (ComplexShape.up Int).QFactorsThroughHomotopy C :=
  (ComplexShape.up Int).QFactorsThroughHomotopy_of_exists_prev (fun n => ⟨n - 1, by simp⟩) C

/-- When we define the derived category as `HomologicalComplexUpToQuasiIso C (ComplexShape.up ℤ)`,
i.e. as the localization of cochain complexes with respect to quasi-isomorphisms, this
example shall say that the derived category is also the localization of the homotopy
category with respect to quasi-isomorphisms. -/
example [(HomologicalComplex.quasiIso C (ComplexShape.up Int)).HasLocalization] :
    HomologicalComplexUpToQuasiIso.Qh.IsLocalization
      (HomotopyCategory.quasiIso C (ComplexShape.up Int)) :=
  inferInstance

end CochainComplex

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
  {ι : Type*} (c : ComplexShape ι)

section

variable [Preadditive C] [Preadditive D]
  [CategoryWithHomology C] [CategoryWithHomology D]
  [(HomologicalComplex.quasiIso D c).HasLocalization]
  [F.Additive] [F.PreservesHomology]

/-- The localizer morphism which expresses that `F.mapHomologicalComplex c` preserves
quasi-isomorphisms. -/
@[simps]
/--
Definition of `mapHomologicalComplexUpToQuasiIsoLocalizerMorphism` / `mapHomologicalComplexUpToQuasiIsoLocalizerMorphism` 的定义

English:
definition mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
  signature: :
  body: F.mapHomologicalComplex c
  map _ _ f (_ : QuasiIso f) := HomologicalComplex.quasiIso_map_of_preservesHomology _ _

中文:
定义 mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
  签名: :
  定义体: F.mapHomologicalComplex c
  map _ _ f (_ : QuasiIso f) := HomologicalComplex.quasiIso_map_of_preservesHomology _ _

Depends on / 依赖: F.mapHomologicalComplex, mapHomologicalComplex
-/
def mapHomologicalComplexUpToQuasiIsoLocalizerMorphism :
    LocalizerMorphism (HomologicalComplex.quasiIso C c) (HomologicalComplex.quasiIso D c) where
  functor := F.mapHomologicalComplex c
  map _ _ f (_ : QuasiIso f) := HomologicalComplex.quasiIso_map_of_preservesHomology _ _

/--
lemma `mapHomologicalComplex_upToQuasiIso_Q_inverts_quasiIso` / 引理 `mapHomologicalComplex_upToQuasiIso_Q_inverts_quasiIso`

English:
lemma mapHomologicalComplex_upToQuasiIso_Q_inverts_quasiIso
  proof: by
  apply (F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism c).inverts

中文:
引理 mapHomologicalComplex_upToQuasiIso_Q_inverts_quasiIso
  证明: by
  apply (F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism c).inverts

Depends on / 依赖: F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism, inverts, mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
-/
lemma mapHomologicalComplex_upToQuasiIso_Q_inverts_quasiIso :
    (HomologicalComplex.quasiIso C c).IsInvertedBy
      (F.mapHomologicalComplex c ⋙ HomologicalComplexUpToQuasiIso.Q) := by
  apply (F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism c).inverts

variable [(HomologicalComplex.quasiIso C c).HasLocalization]

/--
Definition of `mapHomologicalComplexUpToQuasiIso` / `mapHomologicalComplexUpToQuasiIso` 的定义

English:
definition mapHomologicalComplexUpToQuasiIso
  signature: :
  body: (F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism c).localizedFunctor
    HomologicalComplexUpToQuasiIso.Q HomologicalComplexUpToQuasiIso.Q

中文:
定义 mapHomologicalComplexUpToQuasiIso
  签名: :
  定义体: (F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism c).localizedFunctor
    HomologicalComplexUpToQuasiIso.Q HomologicalComplexUpToQuasiIso.Q

Depends on / 依赖: F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism, HomologicalComplexUpToQuasiIso, HomologicalComplexUpToQuasiIso.Q, localizedFunctor, mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
-/
noncomputable def mapHomologicalComplexUpToQuasiIso :
    HomologicalComplexUpToQuasiIso C c ⥤ HomologicalComplexUpToQuasiIso D c :=
  (F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism c).localizedFunctor
    HomologicalComplexUpToQuasiIso.Q HomologicalComplexUpToQuasiIso.Q

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  body: (F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism c).liftingLocalizedFunctor _ _

中文:
实例 :
  定义体: (F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism c).liftingLocalizedFunctor _ _

Depends on / 依赖: F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism, liftingLocalizedFunctor, mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
-/
noncomputable instance :
    Localization.Lifting HomologicalComplexUpToQuasiIso.Q
      (HomologicalComplex.quasiIso C c)
      (F.mapHomologicalComplex c ⋙ HomologicalComplexUpToQuasiIso.Q)
      (F.mapHomologicalComplexUpToQuasiIso c) :=
  (F.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism c).liftingLocalizedFunctor _ _

/--
Definition of `mapHomologicalComplexUpToQuasiIsoFactors` / `mapHomologicalComplexUpToQuasiIsoFactors` 的定义

English:
definition mapHomologicalComplexUpToQuasiIsoFactors
  signature: :
  body: Localization.Lifting.iso HomologicalComplexUpToQuasiIso.Q
      (HomologicalComplex.quasiIso C c) _ _

中文:
定义 mapHomologicalComplexUpToQuasiIsoFactors
  签名: :
  定义体: Localization.Lifting.iso HomologicalComplexUpToQuasiIso.Q
      (HomologicalComplex.quasiIso C c) _ _

Depends on / 依赖: HomologicalComplex, HomologicalComplex.quasiIso, HomologicalComplexUpToQuasiIso, HomologicalComplexUpToQuasiIso.Q, Lifting, Localization, Localization.Lifting.iso, quasiIso
-/
noncomputable def mapHomologicalComplexUpToQuasiIsoFactors :
    HomologicalComplexUpToQuasiIso.Q ⋙ F.mapHomologicalComplexUpToQuasiIso c ≅
      F.mapHomologicalComplex c ⋙ HomologicalComplexUpToQuasiIso.Q :=
  Localization.Lifting.iso HomologicalComplexUpToQuasiIso.Q
      (HomologicalComplex.quasiIso C c) _ _

variable [c.QFactorsThroughHomotopy C] [c.QFactorsThroughHomotopy D]
  [(HomotopyCategory.quotient C c).IsLocalization
    (HomologicalComplex.homotopyEquivalences C c)]

/--
Definition of `mapHomologicalComplexUpToQuasiIsoFactorsh` / `mapHomologicalComplexUpToQuasiIsoFactorsh` 的定义

English:
definition mapHomologicalComplexUpToQuasiIsoFactorsh
  signature: :
  body: Localization.liftNatIso (HomotopyCategory.quotient C c)
    (HomologicalComplex.homotopyEquivalences C c)
    (HomotopyCategory.quotient C c ⋙ HomologicalComplexUpToQuasiIso.Qh ⋙
      F.mapHomologicalComplexUpToQuasiIso c)
    (HomotopyCategory.quotient C c ⋙ F.mapHomotopyCategory c ⋙
      HomologicalComplexUpToQuasiIso.Qh) _ _
      (F.mapHomologicalComplexUpToQuasiIsoFactors c)

中文:
定义 mapHomologicalComplexUpToQuasiIsoFactorsh
  签名: :
  定义体: Localization.liftNatIso (HomotopyCategory.quotient C c)
    (HomologicalComplex.homotopyEquivalences C c)
    (HomotopyCategory.quotient C c ⋙ HomologicalComplexUpToQuasiIso.Qh ⋙
      F.mapHomologicalComplexUpToQuasiIso c)
    (HomotopyCategory.quotient C c ⋙ F.mapHomotopyCategory c ⋙
      HomologicalComplexUpToQuasiIso.Qh) _ _
      (F.mapHomologicalComplexUpToQuasiIsoFactors c)

Depends on / 依赖: F.mapHomologicalComplexUpToQuasiIso, F.mapHomologicalComplexUpToQuasiIsoFactors, F.mapHomotopyCategory, HomologicalComplex, HomologicalComplex.homotopyEquivalences, HomologicalComplexUpToQuasiIso, HomologicalComplexUpToQuasiIso.Qh, HomotopyCategory, HomotopyCategory.quotient, Localization, Localization.liftNatIso, homotopyEquivalences, liftNatIso, mapHomologicalComplexUpToQuasiIso, mapHomologicalComplexUpToQuasiIsoFactors, mapHomotopyCategory, quotient
-/
noncomputable def mapHomologicalComplexUpToQuasiIsoFactorsh :
    HomologicalComplexUpToQuasiIso.Qh ⋙ F.mapHomologicalComplexUpToQuasiIso c ≅
      F.mapHomotopyCategory c ⋙ HomologicalComplexUpToQuasiIso.Qh :=
  Localization.liftNatIso (HomotopyCategory.quotient C c)
    (HomologicalComplex.homotopyEquivalences C c)
    (HomotopyCategory.quotient C c ⋙ HomologicalComplexUpToQuasiIso.Qh ⋙
      F.mapHomologicalComplexUpToQuasiIso c)
    (HomotopyCategory.quotient C c ⋙ F.mapHomotopyCategory c ⋙
      HomologicalComplexUpToQuasiIso.Qh) _ _
      (F.mapHomologicalComplexUpToQuasiIsoFactors c)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  body: ⟨F.mapHomologicalComplexUpToQuasiIsoFactorsh c⟩

中文:
实例 :
  定义体: ⟨F.mapHomologicalComplexUpToQuasiIsoFactorsh c⟩

Depends on / 依赖: F.mapHomologicalComplexUpToQuasiIsoFactorsh, mapHomologicalComplexUpToQuasiIsoFactorsh
-/
noncomputable instance :
    Localization.Lifting HomologicalComplexUpToQuasiIso.Qh (HomotopyCategory.quasiIso C c)
      (F.mapHomotopyCategory c ⋙ HomologicalComplexUpToQuasiIso.Qh)
      (F.mapHomologicalComplexUpToQuasiIso c) :=
  ⟨F.mapHomologicalComplexUpToQuasiIsoFactorsh c⟩

variable {c}

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/--
lemma `mapHomologicalComplexUpToQuasiIsoFactorsh_hom_app` / 引理 `mapHomologicalComplexUpToQuasiIsoFactorsh_hom_app`

English:
lemma mapHomologicalComplexUpToQuasiIsoFactorsh_hom_app
  given: (K : HomologicalComplex C c)
  proof: by
  dsimp [mapHomologicalComplexUpToQuasiIsoFactorsh]
  rw [Localization.liftNatTrans_app]
  dsimp
  simp only [Category.comp_id, Category.id_comp]
  change _ = (F.mapHomologicalComplexUpToQuasiIso c).map (𝟙 _) ≫ _ ≫ 𝟙 _ ≫
    HomologicalComplexUpToQuasiIso.Qh.map (𝟙 _)
  simp only [map_id, Category.comp_id, Category.id_comp]

中文:
引理 mapHomologicalComplexUpToQuasiIsoFactorsh_hom_app
  条件: (K : 同调复形 C c)
  证明: by
  dsimp [mapHomologicalComplexUpToQuasiIsoFactorsh]
  rw [Localization.liftNatTrans_app]
  dsimp
  simp only [Category.comp_id, Category.id_comp]
  change _ = (F.mapHomologicalComplexUpToQuasiIso c).map (𝟙 _) ≫ _ ≫ 𝟙 _ ≫
    HomologicalComplexUpToQuasiIso.Qh.map (𝟙 _)
  simp only [map_id, Category.comp_id, Category.id_comp]

Depends on / 依赖: Category, Category.comp_id, Category.id_comp, F.mapHomologicalComplexUpToQuasiIso, HomologicalComplexUpToQuasiIso, HomologicalComplexUpToQuasiIso.Qh.map, Localization, Localization.liftNatTrans_app, comp_id, id_comp, liftNatTrans_app, mapHomologicalComplexUpToQuasiIso, mapHomologicalComplexUpToQuasiIsoFactorsh, map_id
-/
lemma mapHomologicalComplexUpToQuasiIsoFactorsh_hom_app (K : HomologicalComplex C c) :
    (F.mapHomologicalComplexUpToQuasiIsoFactorsh c).hom.app
        ((HomotopyCategory.quotient _ _).obj K) =
      (F.mapHomologicalComplexUpToQuasiIso c).map
          ((HomologicalComplexUpToQuasiIso.quotientCompQhIso C c).hom.app K) ≫
        (F.mapHomologicalComplexUpToQuasiIsoFactors c).hom.app K ≫
          (HomologicalComplexUpToQuasiIso.quotientCompQhIso D c).inv.app _ ≫
            HomologicalComplexUpToQuasiIso.Qh.map
              ((F.mapHomotopyCategoryFactors c).inv.app K) := by
  dsimp [mapHomologicalComplexUpToQuasiIsoFactorsh]
  rw [Localization.liftNatTrans_app]
  dsimp
  simp only [Category.comp_id, Category.id_comp]
  change _ = (F.mapHomologicalComplexUpToQuasiIso c).map (𝟙 _) ≫ _ ≫ 𝟙 _ ≫
    HomologicalComplexUpToQuasiIso.Qh.map (𝟙 _)
  simp only [map_id, Category.comp_id, Category.id_comp]

end

end CategoryTheory.Functor
