/-
Copyright (c) 2023 Emily Witt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emily Witt, Kim Morrison, Jake Levinson, Sam van Gool
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Abelian.Ext
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Ideal.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Noetherian.Defs

/-!
# Local cohomology.

This file defines the `i`-th local cohomology module of an `R`-module `M` with support in an
ideal `I` of `R`, where `R` is a commutative ring, as the direct limit of Ext modules:

Given a collection of ideals cofinal with the powers of `I`, consider the directed system of
quotients of `R` by these ideals, and take the direct limit of the system induced on the `i`-th
Ext into `M`. One can, of course, take the collection to simply be the integral powers of `I`.

## References

* [M. Hochster, *Local cohomology*][hochsterunpublished]
  <https://dept.math.lsa.umich.edu/~hochster/615W22/lcc.pdf>
* [R. Hartshorne, *Local cohomology: A seminar given by A. Grothendieck*][hartshorne61]
* [M. Brodmann and R. Sharp, *Local cohomology: An algebraic introduction with geometric
  applications*][brodmannsharp13]
* [S. Iyengar, G. Leuschke, A. Leykin, Anton, C. Miller, E. Miller, A. Singh, U. Walther,
  *Twenty-four hours of local cohomology*][iyengaretal13]

## Tags

local cohomology, local cohomology modules

## Future work

* Prove that this definition is equivalent to:
    * the right-derived functor definition
    * the characterization as the limit of Koszul homology
    * the characterization as the cohomology of a Cech-like complex
* Establish long exact sequence(s) in local cohomology
-/

@[expose] public section

open Opposite CategoryTheory Limits

noncomputable section

universe u v v'

namespace localCohomology

-- We define local cohomology, implemented as a direct limit of `Ext(R/J, -)`.
section

variable {R : Type u} [CommRing R] {D : Type v} [SmallCategory D]

/--
Definition of `ringModIdeals` / `ringModIdeals` 的定义

English:
definition ringModIdeals
  signature: (I : D ⥤ Ideal R)
  body: ModuleCat.of R R ⧸ I.obj t
map w := ModuleCat.ofHom Submodule.mapQ _ _ LinearMap.id (I.map w).down.down

中文:
定义 ringModIdeals
  签名: (I : D ⥤ 理想 R)
  定义体: ModuleCat.of R R ⧸ I.obj t
map w := ModuleCat.ofHom Submodule.mapQ _ _ LinearMap.id (I.map w).down.down

Depends on / 依赖: I.obj, ModuleCat, ModuleCat.of
-/
def ringModIdeals (I : D ⥤ Ideal R) : D ⥤ ModuleCat.{u} R where
obj t := ModuleCat.of R R ⧸ I.obj t
map w := ModuleCat.ofHom Submodule.mapQ _ _ LinearMap.id (I.map w).down.down

/--
Definition of `diagram` / `diagram` 的定义

English:
definition diagram
  signature: (I : D ⥤ Ideal R) (i : Nat)
  body: (ringModIdeals I).op ⋙ Ext R (ModuleCat.{u} R) i

中文:
定义 diagram
  签名: (I : D ⥤ 理想 R) (i : 自然数)
  定义体: (ringModIdeals I).op ⋙ Ext R (ModuleCat.{u} R) i

Depends on / 依赖: ModuleCat, ringModIdeals
-/
def diagram (I : D ⥤ Ideal R) (i : Nat) : Dᵒᵖ ⥤ ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  (ringModIdeals I).op ⋙ Ext R (ModuleCat.{u} R) i

end

section

-- We momentarily need to work with a type inequality, as later we will take colimits
-- along diagrams either in Type, or in the same universe as the ring, and we need to cover both.
variable {R : Type max u v} [CommRing R] {D : Type v} [SmallCategory D]

/--
lemma `hasColimitDiagram` / 引理 `hasColimitDiagram`

English:
lemma hasColimitDiagram
  given: (I : D ⥤ Ideal R) (i : Nat)
  proof: inferInstance

中文:
引理 hasColimitDiagram
  条件: (I : D ⥤ 理想 R) (i : 自然数)
  证明: inferInstance
-/
lemma hasColimitDiagram (I : D ⥤ Ideal R) (i : Nat) :
    HasColimit (diagram I i) := inferInstance

/-
In this definition we do not assume any special property of the diagram `I`, but the relevant case
will be where `I` is (cofinal with) the diagram of powers of a single given ideal.

Below, we give two equivalent definitions of the usual local cohomology with support
in an ideal `J`, `localCohomology` and `localCohomology.ofSelfLERadical`.
-/
/--
Definition of `ofDiagram` / `ofDiagram` 的定义

English:
definition ofDiagram
  signature: (I : D ⥤ Ideal R) (i : Nat)
  body: have := hasColimitDiagram.{u, v} I i
  colimit (diagram I i)

中文:
定义 ofDiagram
  签名: (I : D ⥤ 理想 R) (i : 自然数)
  定义体: have := hasColimitDiagram.{u, v} I i
  colimit (diagram I i)

Depends on / 依赖: colimit, diagram, hasColimitDiagram
-/
def ofDiagram (I : D ⥤ Ideal R) (i : Nat) : ModuleCat.{max u v} R ⥤ ModuleCat.{max u v} R :=
  have := hasColimitDiagram.{u, v} I i
  colimit (diagram I i)

end

section

variable {R : Type max u v v'} [CommRing R] {D : Type v} [SmallCategory D]
variable {E : Type v'} [SmallCategory E] (I' : E ⥤ D) (I : D ⥤ Ideal R)

/--
Definition of `diagramComp` / `diagramComp` 的定义

English:
definition diagramComp
  signature: (i : Nat)
  body: Iso.refl _

中文:
定义 diagramComp
  签名: (i : 自然数)
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def diagramComp (i : Nat) : diagram (I' ⋙ I) i ≅ I'.op ⋙ diagram I i :=
  Iso.refl _

/-- Local cohomology agrees along precomposition with a cofinal diagram. -/
@[nolint unusedHavesSuffices]
/--
Definition of `isoOfFinal` / `isoOfFinal` 的定义

English:
definition isoOfFinal
  signature: [Functor.Initial I'] (i : Nat)
  body: have := hasColimitDiagram.{max u v', v} I i
  have := hasColimitDiagram.{max u v, v'} (I' ⋙ I) i
  HasColimit.isoOfNatIso (diagramComp.{u} I' I i) ≪≫ Functor.Final.colimitIso _ _

中文:
定义 isoOfFinal
  签名: [函子.初始 I'] (i : 自然数)
  定义体: have := hasColimitDiagram.{max u v', v} I i
  have := hasColimitDiagram.{max u v, v'} (I' ⋙ I) i
  HasColimit.isoOfNatIso (diagramComp.{u} I' I i) ≪≫ Functor.Final.colimitIso _ _

Depends on / 依赖: Functor, Functor.Final.colimitIso, HasColimit, HasColimit.isoOfNatIso, colimitIso, diagramComp, hasColimitDiagram, isoOfNatIso
-/
def isoOfFinal [Functor.Initial I'] (i : Nat) :
    ofDiagram.{max u v, v'} (I' ⋙ I) i ≅ ofDiagram.{max u v', v} I i :=
  have := hasColimitDiagram.{max u v', v} I i
  have := hasColimitDiagram.{max u v, v'} (I' ⋙ I) i
  HasColimit.isoOfNatIso (diagramComp.{u} I' I i) ≪≫ Functor.Final.colimitIso _ _

end

section Diagrams

variable {R : Type u} [CommRing R]

/--
Definition of `idealPowersDiagram` / `idealPowersDiagram` 的定义

English:
definition idealPowersDiagram
  signature: (J : Ideal R)
  body: J ^ unop t
  map w := ⟨⟨Ideal.pow_le_pow_right w.unop.down.down⟩⟩

中文:
定义 idealPowersDiagram
  签名: (J : 理想 R)
  定义体: J ^ unop t
  map w := ⟨⟨Ideal.pow_le_pow_right w.unop.down.down⟩⟩
-/
def idealPowersDiagram (J : Ideal R) : Natᵒᵖ ⥤ Ideal R where
  obj t := J ^ unop t
  map w := ⟨⟨Ideal.pow_le_pow_right w.unop.down.down⟩⟩

/--
Definition of `SelfLERadical` / `SelfLERadical` 的定义

English:
definition SelfLERadical
  signature: (J : Ideal R)
  body: ObjectProperty.FullSubcategory fun J' : Ideal R => J <= J'.radical
deriving Category

中文:
定义 SelfLERadical
  签名: (J : 理想 R)
  定义体: ObjectProperty.FullSubcategory fun J' : Ideal R => J <= J'.radical
deriving Category

Depends on / 依赖: FullSubcategory, ObjectProperty, ObjectProperty.FullSubcategory, radical
-/
def SelfLERadical (J : Ideal R) : Type u :=
  ObjectProperty.FullSubcategory fun J' : Ideal R => J <= J'.radical
deriving Category

/--
Instance `SelfLERadical.inhabited` / 实例 `SelfLERadical.inhabited`

English:
instance SelfLERadical.inhabited
  signature: (J : Ideal R)
  body: ⟨J, Ideal.le_radical⟩

中文:
实例 SelfLERadical.inhabited
  签名: (J : 理想 R)
  定义体: ⟨J, Ideal.le_radical⟩

Depends on / 依赖: Ideal.le_radical, le_radical
-/
instance SelfLERadical.inhabited (J : Ideal R) : Inhabited (SelfLERadical J) where
  default := ⟨J, Ideal.le_radical⟩

/--
Definition of `selfLERadicalDiagram` / `selfLERadicalDiagram` 的定义

English:
definition selfLERadicalDiagram
  signature: (J : Ideal R)
  body: ObjectProperty.ι _

中文:
定义 selfLERadicalDiagram
  签名: (J : 理想 R)
  定义体: ObjectProperty.ι _

Depends on / 依赖: ObjectProperty
-/
def selfLERadicalDiagram (J : Ideal R) : SelfLERadical J ⥤ Ideal R :=
  ObjectProperty.ι _

end Diagrams

end localCohomology

/-! We give two models for the local cohomology with support in an ideal `J`: first in terms of
the powers of `J` (`localCohomology`), then in terms of *all* ideals with radical
containing `J` (`localCohomology.ofSelfLERadical`). -/


section ModelsForLocalCohomology

open localCohomology

variable {R : Type u} [CommRing R]

/--
Definition of `localCohomology` / `localCohomology` 的定义

English:
definition localCohomology
  signature: (J : Ideal R) (i : Nat)
  body: ofDiagram (idealPowersDiagram J) i

中文:
定义 localCohomology
  签名: (J : 理想 R) (i : 自然数)
  定义体: ofDiagram (idealPowersDiagram J) i

Depends on / 依赖: idealPowersDiagram, ofDiagram
-/
def localCohomology (J : Ideal R) (i : Nat) : ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  ofDiagram (idealPowersDiagram J) i

/--
Definition of `localCohomology.ofSelfLERadical` / `localCohomology.ofSelfLERadical` 的定义

English:
definition localCohomology.ofSelfLERadical
  signature: (J : Ideal R) (i : Nat)
  body: ofDiagram.{u} (selfLERadicalDiagram.{u} J) i

中文:
定义 localCohomology.ofSelfLERadical
  签名: (J : 理想 R) (i : 自然数)
  定义体: ofDiagram.{u} (selfLERadicalDiagram.{u} J) i

Depends on / 依赖: ofDiagram, selfLERadicalDiagram
-/
def localCohomology.ofSelfLERadical (J : Ideal R) (i : Nat) : ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  ofDiagram.{u} (selfLERadicalDiagram.{u} J) i

end ModelsForLocalCohomology

namespace localCohomology

/-!
Showing equivalence of different definitions of local cohomology.
  * `localCohomology.isoSelfLERadical` gives the isomorphism
      `localCohomology J i ≅ localCohomology.ofSelfLERadical J i`
  * `localCohomology.isoOfSameRadical` gives the isomorphism
      `localCohomology J i ≅ localCohomology K i` when `J.radical = K.radical`.
-/

section LocalCohomologyEquiv

variable {R : Type u} [CommRing R]

/--
Definition of `idealPowersToSelfLERadical` / `idealPowersToSelfLERadical` 的定义

English:
definition idealPowersToSelfLERadical
  signature: (J : Ideal R)
  body: ObjectProperty.lift _ (idealPowersDiagram J) fun k => by
    change _ <= (J ^ unop k).radical
    rcases unop k with - | n
    · simp [Ideal.radical_top, pow_zero, Ideal.one_eq_top, le_top]
    · simp only [J.radical_pow n.succ_ne_zero, Ideal.le_radical]

中文:
定义 idealPowersToSelfLERadical
  签名: (J : 理想 R)
  定义体: ObjectProperty.lift _ (idealPowersDiagram J) fun k => by
    change _ <= (J ^ unop k).radical
    rcases unop k with - | n
    · simp [Ideal.radical_top, pow_zero, Ideal.one_eq_top, le_top]
    · simp only [J.radical_pow n.succ_ne_zero, Ideal.le_radical]

Depends on / 依赖: Ideal.le_radical, Ideal.one_eq_top, Ideal.radical_top, J.radical_pow, ObjectProperty, ObjectProperty.lift, idealPowersDiagram, le_radical, le_top, n.succ_ne_zero, one_eq_top, pow_zero, radical, radical_pow, radical_top, succ_ne_zero
-/
def idealPowersToSelfLERadical (J : Ideal R) : Natᵒᵖ ⥤ SelfLERadical J :=
  ObjectProperty.lift _ (idealPowersDiagram J) fun k => by
    change _ <= (J ^ unop k).radical
    rcases unop k with - | n
    · simp [Ideal.radical_top, pow_zero, Ideal.one_eq_top, le_top]
    · simp only [J.radical_pow n.succ_ne_zero, Ideal.le_radical]

variable {I J K : Ideal R}

/--
Instance `ideal_powers_initial` / 实例 `ideal_powers_initial`

English:
instance ideal_powers_initial
  signature: [hR : IsNoetherian R R]
  body: by
    apply +allowSynthFailures zigzag_isConnected
    · obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg J'.2 (isNoetherian_def.mp hR _)
      exact ⟨CostructuredArrow.mk (⟨⟨⟨hk⟩⟩⟩ : (idealPowersToSelfLERadical J).obj (op k) ⟶ J')⟩
    · intro j1 j2
      apply Relation.ReflTransGen.single
      -- The inclusions `J^n1 ≤ J'` and `J^n2 ≤ J'` always form a triangle, based on
      -- which exponent is larger.
      rcases le_total (unop j1.left) (unop j2.left) with h | h
      · right; exact ⟨CostructuredArrow.homMk (homOfLE h).op rfl⟩
      · left; exact ⟨CostructuredArrow.homMk (homOfLE h).op rfl⟩

example : HasColimitsOfSize.{0, 0, u, u + 1} (ModuleCat.{u, u} R) := inferInstance

中文:
实例 ideal_powers_initial
  签名: [hR : 是Noether R R]
  定义体: by
    apply +allowSynthFailures zigzag_isConnected
    · obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg J'.2 (isNoetherian_def.mp hR _)
      exact ⟨CostructuredArrow.mk (⟨⟨⟨hk⟩⟩⟩ : (idealPowersToSelfLERadical J).obj (op k) ⟶ J')⟩
    · intro j1 j2
      apply Relation.ReflTransGen.single
      -- The inclusions `J^n1 ≤ J'` and `J^n2 ≤ J'` always form a triangle, based on
      -- which exponent is larger.
      rcases le_total (unop j1.left) (unop j2.left) with h | h
      · right; exact ⟨CostructuredArrow.homMk (homOfLE h).op rfl⟩
      · left; exact ⟨CostructuredArrow.homMk (homOfLE h).op rfl⟩

example : HasColimitsOfSize.{0, 0, u, u + 1} (ModuleCat.{u, u} R) := inferInstance

Depends on / 依赖: CostructuredArrow, CostructuredArrow.mk, Ideal.exists_pow_le_of_le_radical_of_fg, ReflTransGen, Relation, Relation.ReflTransGen.single, allowSynthFailures, exists_pow_le_of_le_radical_of_fg, idealPowersToSelfLERadical, isNoetherian_def, isNoetherian_def.mp, single, zigzag_isConnected
-/
instance ideal_powers_initial [hR : IsNoetherian R R] :
    Functor.Initial (idealPowersToSelfLERadical J) where
  out J' := by
    apply +allowSynthFailures zigzag_isConnected
    · obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg J'.2 (isNoetherian_def.mp hR _)
      exact ⟨CostructuredArrow.mk (⟨⟨⟨hk⟩⟩⟩ : (idealPowersToSelfLERadical J).obj (op k) ⟶ J')⟩
    · intro j1 j2
      apply Relation.ReflTransGen.single
      -- The inclusions `J^n1 ≤ J'` and `J^n2 ≤ J'` always form a triangle, based on
      -- which exponent is larger.
      rcases le_total (unop j1.left) (unop j2.left) with h | h
      · right; exact ⟨CostructuredArrow.homMk (homOfLE h).op rfl⟩
      · left; exact ⟨CostructuredArrow.homMk (homOfLE h).op rfl⟩

example : HasColimitsOfSize.{0, 0, u, u + 1} (ModuleCat.{u, u} R) := inferInstance
/--
Definition of `isoSelfLERadical` / `isoSelfLERadical` 的定义

English:
definition isoSelfLERadical
  signature: (J : Ideal.{u} R) [IsNoetherian.{u, u} R R] (i : Nat)
  body: (localCohomology.isoOfFinal.{u, u, 0} (idealPowersToSelfLERadical.{u} J)
    (selfLERadicalDiagram.{u} J) i).symm ≪≫
      HasColimit.isoOfNatIso.{0, 0, u + 1, u + 1} (Iso.refl.{u + 1, u + 1} _)

中文:
定义 isoSelfLERadical
  签名: (J : 理想.{u} R) [是Noether.{u, u} R R] (i : 自然数)
  定义体: (localCohomology.isoOfFinal.{u, u, 0} (idealPowersToSelfLERadical.{u} J)
    (selfLERadicalDiagram.{u} J) i).symm ≪≫
      HasColimit.isoOfNatIso.{0, 0, u + 1, u + 1} (Iso.refl.{u + 1, u + 1} _)

Depends on / 依赖: HasColimit, HasColimit.isoOfNatIso, Iso.refl, idealPowersToSelfLERadical, isoOfFinal, isoOfNatIso, localCohomology, localCohomology.isoOfFinal, selfLERadicalDiagram
-/
def isoSelfLERadical (J : Ideal.{u} R) [IsNoetherian.{u, u} R R] (i : Nat) :
    localCohomology.ofSelfLERadical.{u} J i ≅ localCohomology.{u} J i :=
  (localCohomology.isoOfFinal.{u, u, 0} (idealPowersToSelfLERadical.{u} J)
    (selfLERadicalDiagram.{u} J) i).symm ≪≫
      HasColimit.isoOfNatIso.{0, 0, u + 1, u + 1} (Iso.refl.{u + 1, u + 1} _)

/--
Definition of `SelfLERadical.cast` / `SelfLERadical.cast` 的定义

English:
definition SelfLERadical.cast
  signature: (hJK : J.radical = K.radical)
  body: ObjectProperty.ιOfLE fun L hL => by
    rw [← Ideal.radical_le_radical_iff] at hL ⊢
    exact hJK.symm.trans_le hL

中文:
定义 SelfLERadical.cast
  签名: (hJK : J.radical = K.radical)
  定义体: ObjectProperty.ιOfLE fun L hL => by
    rw [← Ideal.radical_le_radical_iff] at hL ⊢
    exact hJK.symm.trans_le hL

Depends on / 依赖: Ideal.radical_le_radical_iff, ObjectProperty, hJK.symm.trans_le, radical_le_radical_iff, trans_le
-/
def SelfLERadical.cast (hJK : J.radical = K.radical) : SelfLERadical J ⥤ SelfLERadical K :=
  ObjectProperty.ιOfLE fun L hL => by
    rw [← Ideal.radical_le_radical_iff] at hL ⊢
    exact hJK.symm.trans_le hL

-- TODO generalize this to the equivalence of full categories for any `iff`.
/--
Definition of `SelfLERadical.castEquivalence` / `SelfLERadical.castEquivalence` 的定义

English:
definition SelfLERadical.castEquivalence
  signature: (hJK : J.radical = K.radical)
  body: SelfLERadical.cast hJK
  inverse := SelfLERadical.cast hJK.symm
  unitIso := Iso.refl _
  counitIso := Iso.refl _

中文:
定义 SelfLERadical.castEquivalence
  签名: (hJK : J.radical = K.radical)
  定义体: SelfLERadical.cast hJK
  inverse := SelfLERadical.cast hJK.symm
  unitIso := Iso.refl _
  counitIso := Iso.refl _

Depends on / 依赖: SelfLERadical, SelfLERadical.cast
-/
def SelfLERadical.castEquivalence (hJK : J.radical = K.radical) :
    SelfLERadical J ≌ SelfLERadical K where
  functor := SelfLERadical.cast hJK
  inverse := SelfLERadical.cast hJK.symm
  unitIso := Iso.refl _
  counitIso := Iso.refl _

/--
Instance `SelfLERadical.cast_isEquivalence` / 实例 `SelfLERadical.cast_isEquivalence`

English:
instance SelfLERadical.cast_isEquivalence
  signature: (hJK : J.radical = K.radical)
  body: (castEquivalence hJK).isEquivalence_functor

中文:
实例 SelfLERadical.cast_isEquivalence
  签名: (hJK : J.radical = K.radical)
  定义体: (castEquivalence hJK).isEquivalence_functor

Depends on / 依赖: castEquivalence, isEquivalence_functor
-/
instance SelfLERadical.cast_isEquivalence (hJK : J.radical = K.radical) :
    (SelfLERadical.cast hJK).IsEquivalence :=
  (castEquivalence hJK).isEquivalence_functor

/--
Definition of `SelfLERadical.isoOfSameRadical` / `SelfLERadical.isoOfSameRadical` 的定义

English:
definition SelfLERadical.isoOfSameRadical
  signature: (hJK : J.radical = K.radical) (i : Nat)
  body: (isoOfFinal.{u, u, u} (SelfLERadical.cast hJK.symm) _ _).symm

中文:
定义 SelfLERadical.isoOfSameRadical
  签名: (hJK : J.radical = K.radical) (i : 自然数)
  定义体: (isoOfFinal.{u, u, u} (SelfLERadical.cast hJK.symm) _ _).symm

Depends on / 依赖: SelfLERadical, SelfLERadical.cast, hJK.symm, isoOfFinal
-/
def SelfLERadical.isoOfSameRadical (hJK : J.radical = K.radical) (i : Nat) :
    ofSelfLERadical J i ≅ ofSelfLERadical K i :=
  (isoOfFinal.{u, u, u} (SelfLERadical.cast hJK.symm) _ _).symm

/--
Definition of `isoOfSameRadical` / `isoOfSameRadical` 的定义

English:
definition isoOfSameRadical
  signature: [IsNoetherian R R] (hJK : J.radical = K.radical) (i : Nat)
  body: (isoSelfLERadical J i).symm ≪≫ SelfLERadical.isoOfSameRadical hJK i ≪≫ isoSelfLERadical K i

中文:
定义 isoOfSameRadical
  签名: [是Noether R R] (hJK : J.radical = K.radical) (i : 自然数)
  定义体: (isoSelfLERadical J i).symm ≪≫ SelfLERadical.isoOfSameRadical hJK i ≪≫ isoSelfLERadical K i

Depends on / 依赖: SelfLERadical, SelfLERadical.isoOfSameRadical, isoOfSameRadical, isoSelfLERadical
-/
def isoOfSameRadical [IsNoetherian R R] (hJK : J.radical = K.radical) (i : Nat) :
    localCohomology J i ≅ localCohomology K i :=
  (isoSelfLERadical J i).symm ≪≫ SelfLERadical.isoOfSameRadical hJK i ≪≫ isoSelfLERadical K i

end LocalCohomologyEquiv

end localCohomology
