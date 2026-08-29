/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Nikolas Kuhn, Dagur Asgeirsson
-/
module

public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import Mathlib.Topology.Category.Stonean.EffectiveEpi
public import Mathlib.Condensed.Basic
public import Mathlib.CategoryTheory.Sites.Coherent.SheafComparison
/-!

# Sheaves on CompHaus are equivalent to sheaves on Stonean

The forgetful functor from extremally disconnected spaces `Stonean` to compact
Hausdorff spaces `CompHaus` has the marvellous property that it induces an equivalence of categories
between sheaves on these two sites. With the terminology of nLab, `Stonean` is a
*dense subsite* of `CompHaus`: see https://ncatlab.org/nlab/show/dense+sub-site

Since Stonean spaces are the projective objects in `CompHaus`, which has enough projectives,
and the notions of effective epimorphism, epimorphism and surjective continuous map are equivalent
in `CompHaus` and `Stonean`, we can use the general setup in
`Mathlib/CategoryTheory/Sites/Coherent/SheafComparison.lean` to deduce the equivalence of
categories. We give the corresponding statements for `Profinite` as well.

## Main results

* `Condensed.StoneanCompHaus.equivalence`: the equivalence from coherent sheaves on `Stonean` to
  coherent sheaves on `CompHaus` (i.e. condensed sets).
* `Condensed.StoneanProfinite.equivalence`: the equivalence from coherent sheaves on `Stonean` to
  coherent sheaves on `Profinite`.
* `Condensed.ProfiniteCompHaus.equivalence`: the equivalence from coherent sheaves on `Profinite` to
  coherent sheaves on `CompHaus` (i.e. condensed sets).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace Condensed

namespace StoneanCompHaus

/-- The equivalence from coherent sheaves on `Stonean` to coherent sheaves on `CompHaus`
    (i.e. condensed sets). -/
noncomputable
/--
Definition of `equivalence` / `equivalence` 的定义

English:
definition equivalence
  signature: (A : Type*) [Category* A]
  body: coherentTopology.equivalence' Stonean.toCompHaus A

中文:
定义 equivalence
  签名: (A : 类型) [范畴* A]
  定义体: coherentTopology.equivalence' Stonean.toCompHaus A

Depends on / 依赖: Stonean, Stonean.toCompHaus, coherentTopology, coherentTopology.equivalence, equivalence, toCompHaus
-/
def equivalence (A : Type*) [Category* A]
    [forall X, HasLimitsOfShape (StructuredArrow X Stonean.toCompHaus.op) A] :
    Sheaf (coherentTopology Stonean) A ≌ Condensed.{u} A :=
  coherentTopology.equivalence' Stonean.toCompHaus A

end StoneanCompHaus

namespace StoneanProfinite

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Stonean.toProfinite.PreservesEffectiveEpis
  body: ((Profinite.effectiveEpi_tfae _).out 0 2).mpr (((Stonean.effectiveEpi_tfae _).out 0 2).mp h)

中文:
实例 :
  签名: Stonean.toProfinite.保持EffectiveEpis
  定义体: ((Profinite.effectiveEpi_tfae _).out 0 2).mpr (((Stonean.effectiveEpi_tfae _).out 0 2).mp h)

Depends on / 依赖: Profinite, Profinite.effectiveEpi_tfae, Stonean, Stonean.effectiveEpi_tfae, effectiveEpi_tfae
-/
instance : Stonean.toProfinite.PreservesEffectiveEpis where
  preserves f h :=
    ((Profinite.effectiveEpi_tfae _).out 0 2).mpr (((Stonean.effectiveEpi_tfae _).out 0 2).mp h)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Stonean.toProfinite.ReflectsEffectiveEpis
  body: ((Stonean.effectiveEpi_tfae f).out 0 2).mpr (((Profinite.effectiveEpi_tfae _).out 0 2).mp h)

中文:
实例 :
  签名: Stonean.toProfinite.ReflectsEffectiveEpis
  定义体: ((Stonean.effectiveEpi_tfae f).out 0 2).mpr (((Profinite.effectiveEpi_tfae _).out 0 2).mp h)

Depends on / 依赖: Profinite, Profinite.effectiveEpi_tfae, Stonean, Stonean.effectiveEpi_tfae, effectiveEpi_tfae
-/
instance : Stonean.toProfinite.ReflectsEffectiveEpis where
  reflects f h :=
    ((Stonean.effectiveEpi_tfae f).out 0 2).mpr (((Profinite.effectiveEpi_tfae _).out 0 2).mp h)

/--
Definition of `stoneanToProfiniteEffectivePresentation` / `stoneanToProfiniteEffectivePresentation` 的定义

English:
definition stoneanToProfiniteEffectivePresentation
  signature: (X : Profinite)
  body: X.presentation
  f := Profinite.presentation.π X
  effectiveEpi := ((Profinite.effectiveEpi_tfae _).out 0 1).mpr (inferInstance : Epi _)

中文:
定义 stoneanToProfiniteEffectivePresentation
  签名: (X : Profinite)
  定义体: X.presentation
  f := Profinite.presentation.π X
  effectiveEpi := ((Profinite.effectiveEpi_tfae _).out 0 1).mpr (inferInstance : Epi _)

Depends on / 依赖: X.presentation, presentation
-/
noncomputable def stoneanToProfiniteEffectivePresentation (X : Profinite) :
    Stonean.toProfinite.EffectivePresentation X where
  p := X.presentation
  f := Profinite.presentation.π X
  effectiveEpi := ((Profinite.effectiveEpi_tfae _).out 0 1).mpr (inferInstance : Epi _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Stonean.toProfinite.EffectivelyEnough
  body: ⟨stoneanToProfiniteEffectivePresentation X⟩

中文:
实例 :
  签名: Stonean.toProfinite.EffectivelyEnough
  定义体: ⟨stoneanToProfiniteEffectivePresentation X⟩

Depends on / 依赖: stoneanToProfiniteEffectivePresentation
-/
instance : Stonean.toProfinite.EffectivelyEnough where
  presentation X := ⟨stoneanToProfiniteEffectivePresentation X⟩

/-- The equivalence from coherent sheaves on `Stonean` to coherent sheaves on `Profinite`. -/
noncomputable
/--
Definition of `equivalence` / `equivalence` 的定义

English:
definition equivalence
  signature: (A : Type*) [Category* A]
  body: coherentTopology.equivalence' Stonean.toProfinite A

中文:
定义 equivalence
  签名: (A : 类型) [范畴* A]
  定义体: coherentTopology.equivalence' Stonean.toProfinite A

Depends on / 依赖: Stonean, Stonean.toProfinite, coherentTopology, coherentTopology.equivalence, equivalence, toProfinite
-/
def equivalence (A : Type*) [Category* A]
    [forall X, HasLimitsOfShape (StructuredArrow X Stonean.toProfinite.op) A] :
    Sheaf (coherentTopology Stonean) A ≌ Sheaf (coherentTopology Profinite) A :=
  coherentTopology.equivalence' Stonean.toProfinite A

end StoneanProfinite

namespace ProfiniteCompHaus

/-- The equivalence from coherent sheaves on `Profinite` to coherent sheaves on `CompHaus`
(i.e. condensed sets). -/
noncomputable
/--
Definition of `equivalence` / `equivalence` 的定义

English:
definition equivalence
  signature: (A : Type*) [Category* A]
  body: coherentTopology.equivalence' profiniteToCompHaus A

中文:
定义 equivalence
  签名: (A : 类型) [范畴* A]
  定义体: coherentTopology.equivalence' profiniteToCompHaus A

Depends on / 依赖: coherentTopology, coherentTopology.equivalence, equivalence, profiniteToCompHaus
-/
def equivalence (A : Type*) [Category* A]
    [forall X, HasLimitsOfShape (StructuredArrow X profiniteToCompHaus.op) A] :
    Sheaf (coherentTopology Profinite) A ≌ Condensed.{u} A :=
  coherentTopology.equivalence' profiniteToCompHaus A

end ProfiniteCompHaus

variable {A : Type*} [Category* A] (X : Condensed.{u} A)

/--
lemma `isSheafProfinite` / 引理 `isSheafProfinite`

English:
lemma isSheafProfinite
  proof: ((ProfiniteCompHaus.equivalence A).inverse.obj X).property

中文:
引理 isSheafProfinite
  证明: ((ProfiniteCompHaus.equivalence A).inverse.obj X).property

Depends on / 依赖: ProfiniteCompHaus, ProfiniteCompHaus.equivalence, equivalence, inverse, inverse.obj, property
-/
lemma isSheafProfinite
    [forall Y, HasLimitsOfShape (StructuredArrow Y profiniteToCompHaus.{u}.op) A] :
    Presheaf.IsSheaf (coherentTopology Profinite)
    (profiniteToCompHaus.op ⋙ X.obj) :=
  ((ProfiniteCompHaus.equivalence A).inverse.obj X).property

/--
lemma `isSheafStonean` / 引理 `isSheafStonean`

English:
lemma isSheafStonean
  proof: ((StoneanCompHaus.equivalence A).inverse.obj X).property

中文:
引理 isSheafStonean
  证明: ((StoneanCompHaus.equivalence A).inverse.obj X).property

Depends on / 依赖: StoneanCompHaus, StoneanCompHaus.equivalence, equivalence, inverse, inverse.obj, property
-/
lemma isSheafStonean
    [forall Y, HasLimitsOfShape (StructuredArrow Y Stonean.toCompHaus.{u}.op) A] :
    Presheaf.IsSheaf (coherentTopology Stonean)
    (Stonean.toCompHaus.op ⋙ X.obj) :=
  ((StoneanCompHaus.equivalence A).inverse.obj X).property

end Condensed
