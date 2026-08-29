/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.EffectiveEpi
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Sites.SheafQuasiCompact
public import Mathlib.CategoryTheory.Sites.EffectiveEpimorphic

/-!
# Fpqc topology

In this file we define the fpqc topology and show it is subcanonical. It is the quasi-compact
topology for flat morphisms.

## Main declarations

- `fppfPrecoverage`: The precoverage given by jointly-surjective families of flat
  morphisms, locally of finite presentation.
- `fpqcPrecoverage`: The precoverage given by quasi-compact, jointly-surjective families of
  flat morphisms.
- The fpqc topology is subcanonical. This is available by `inferInstance`.

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `fppfPrecoverage` / `fppfPrecoverage` 的定义

English:
definition fppfPrecoverage
  signature: : Precoverage Scheme.{u}
  body: precoverage (@Flat ⊓ @LocallyOfFinitePresentation)
  deriving Precoverage.IsStableUnderBaseChange, Precoverage.IsStableUnderComposition

中文:
定义 fppfPrecoverage
  签名: : Precoverage Scheme.{u}
  定义体: precoverage (@Flat ⊓ @LocallyOfFinitePresentation)
  deriving Precoverage.IsStableUnderBaseChange, Precoverage.IsStableUnderComposition

Depends on / 依赖: LocallyOfFinitePresentation, precoverage
-/
def fppfPrecoverage : Precoverage Scheme.{u} :=
  precoverage (@Flat ⊓ @LocallyOfFinitePresentation)
  deriving Precoverage.IsStableUnderBaseChange, Precoverage.IsStableUnderComposition

/--
lemma `zariskiPrecoverage_le_fppfPrecoverage` / 引理 `zariskiPrecoverage_le_fppfPrecoverage`

English:
lemma zariskiPrecoverage_le_fppfPrecoverage
  proof: precoverage_mono fun _ _ _ _ => ⟨inferInstance, inferInstance⟩

中文:
引理 zariskiPrecoverage_le_fppfPrecoverage
  证明: precoverage_mono fun _ _ _ _ => ⟨inferInstance, inferInstance⟩

Depends on / 依赖: precoverage_mono
-/
lemma zariskiPrecoverage_le_fppfPrecoverage :
    zariskiPrecoverage <= fppfPrecoverage :=
  precoverage_mono fun _ _ _ _ => ⟨inferInstance, inferInstance⟩

/--
lemma `fppfPrecoverage_eq_inf` / 引理 `fppfPrecoverage_eq_inf`

English:
lemma fppfPrecoverage_eq_inf
  proof: by
  grind [fppfPrecoverage, precoverage, precoverage, MorphismProperty.precoverage_inf]

中文:
引理 fppfPrecoverage_eq_inf
  证明: by
  grind [fppfPrecoverage, precoverage, precoverage, MorphismProperty.precoverage_inf]

Depends on / 依赖: MorphismProperty, MorphismProperty.precoverage_inf, fppfPrecoverage, precoverage, precoverage_inf
-/
lemma fppfPrecoverage_eq_inf :
    fppfPrecoverage = precoverage @Flat ⊓ precoverage @LocallyOfFinitePresentation := by
  grind [fppfPrecoverage, precoverage, precoverage, MorphismProperty.precoverage_inf]

/--
Definition of `fppfTopology` / `fppfTopology` 的定义

English:
abbreviation fppfTopology
  signature: : GrothendieckTopology Scheme.{u}
  body: fppfPrecoverage.toGrothendieck

中文:
缩写 fppfTopology
  签名: : GrothendieckTopology Scheme.{u}
  定义体: fppfPrecoverage.toGrothendieck

Depends on / 依赖: fppfPrecoverage, fppfPrecoverage.toGrothendieck, toGrothendieck
-/
abbrev fppfTopology : GrothendieckTopology Scheme.{u} :=
  fppfPrecoverage.toGrothendieck

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `fpqcPrecoverage` / `fpqcPrecoverage` 的定义

English:
definition fpqcPrecoverage
  signature: : Precoverage Scheme.{u}
  body: propQCPrecoverage @Flat
  deriving Precoverage.HasIsos, Precoverage.IsStableUnderBaseChange,
    Precoverage.IsStableUnderComposition

中文:
定义 fpqcPrecoverage
  签名: : Precoverage Scheme.{u}
  定义体: propQCPrecoverage @Flat
  deriving Precoverage.HasIsos, Precoverage.IsStableUnderBaseChange,
    Precoverage.IsStableUnderComposition

Depends on / 依赖: propQCPrecoverage
-/
def fpqcPrecoverage : Precoverage Scheme.{u} :=
  propQCPrecoverage @Flat
  deriving Precoverage.HasIsos, Precoverage.IsStableUnderBaseChange,
    Precoverage.IsStableUnderComposition

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `fppfPrecoverage_le_fpqcPrecoverage` / 引理 `fppfPrecoverage_le_fpqcPrecoverage`

English:
lemma fppfPrecoverage_le_fpqcPrecoverage
  statement: fppfPrecoverage <= fpqcPrecoverage
  proof: by
  rw [fpqcPrecoverage]; rw [propQCPrecoverage]; rw [le_inf_iff]
  refine ⟨?_, precoverage_mono fun X Y f ⟨hf, _⟩ => inferInstance⟩
  exact precoverage_le_qcPrecoverage_of_isOpenMap fun X Y f ⟨_, _⟩ => f.isOpenMap

中文:
引理 fppfPrecoverage_le_fpqcPrecoverage
  结论: fppfPrecoverage <= fpqcPrecoverage
  证明: by
  rw [fpqcPrecoverage]; rw [propQCPrecoverage]; rw [le_inf_iff]
  refine ⟨?_, precoverage_mono fun X Y f ⟨hf, _⟩ => inferInstance⟩
  exact precoverage_le_qcPrecoverage_of_isOpenMap fun X Y f ⟨_, _⟩ => f.isOpenMap

Depends on / 依赖: f.isOpenMap, fpqcPrecoverage, isOpenMap, le_inf_iff, precoverage_le_qcPrecoverage_of_isOpenMap, precoverage_mono, propQCPrecoverage
-/
lemma fppfPrecoverage_le_fpqcPrecoverage : fppfPrecoverage <= fpqcPrecoverage := by
  rw [fpqcPrecoverage]; rw [propQCPrecoverage]; rw [le_inf_iff]
  refine ⟨?_, precoverage_mono fun X Y f ⟨hf, _⟩ => inferInstance⟩
  exact precoverage_le_qcPrecoverage_of_isOpenMap fun X Y f ⟨_, _⟩ => f.isOpenMap

/--
lemma `zariskiPrecoverage_le_fpqcPrecoverage` / 引理 `zariskiPrecoverage_le_fpqcPrecoverage`

English:
lemma zariskiPrecoverage_le_fpqcPrecoverage
  statement: zariskiPrecoverage <= fpqcPrecoverage
  proof: le_trans zariskiPrecoverage_le_fppfPrecoverage fppfPrecoverage_le_fpqcPrecoverage

中文:
引理 zariskiPrecoverage_le_fpqcPrecoverage
  结论: zariskiPrecoverage <= fpqcPrecoverage
  证明: le_trans zariskiPrecoverage_le_fppfPrecoverage fppfPrecoverage_le_fpqcPrecoverage

Depends on / 依赖: fppfPrecoverage_le_fpqcPrecoverage, le_trans, zariskiPrecoverage_le_fppfPrecoverage
-/
lemma zariskiPrecoverage_le_fpqcPrecoverage : zariskiPrecoverage <= fpqcPrecoverage :=
  le_trans zariskiPrecoverage_le_fppfPrecoverage fppfPrecoverage_le_fpqcPrecoverage

/--
Definition of `fpqcTopology` / `fpqcTopology` 的定义

English:
abbreviation fpqcTopology
  signature: : GrothendieckTopology Scheme.{u}
  body: fpqcPrecoverage.toGrothendieck

中文:
缩写 fpqcTopology
  签名: : GrothendieckTopology Scheme.{u}
  定义体: fpqcPrecoverage.toGrothendieck

Depends on / 依赖: fpqcPrecoverage, fpqcPrecoverage.toGrothendieck, toGrothendieck
-/
abbrev fpqcTopology : GrothendieckTopology Scheme.{u} :=
  fpqcPrecoverage.toGrothendieck

/--
lemma `fpqcTopology_eq_propQCTopology` / 引理 `fpqcTopology_eq_propQCTopology`

English:
lemma fpqcTopology_eq_propQCTopology
  statement: fpqcTopology = Scheme.propQCTopology @Flat
  proof: rfl

中文:
引理 fpqcTopology_eq_propQCTopology
  结论: fpqcTopology = Scheme.propQCTopology @Flat
  证明: rfl
-/
lemma fpqcTopology_eq_propQCTopology : fpqcTopology = Scheme.propQCTopology @Flat := rfl

/--
lemma `zariskiTopology_le_fpqcTopology` / 引理 `zariskiTopology_le_fpqcTopology`

English:
lemma zariskiTopology_le_fpqcTopology
  statement: zariskiTopology <= fpqcTopology
  proof: Precoverage.toGrothendieck_mono zariskiPrecoverage_le_fpqcPrecoverage

中文:
引理 zariskiTopology_le_fpqcTopology
  结论: zariskiTopology <= fpqcTopology
  证明: Precoverage.toGrothendieck_mono zariskiPrecoverage_le_fpqcPrecoverage

Depends on / 依赖: Precoverage, Precoverage.toGrothendieck_mono, toGrothendieck_mono, zariskiPrecoverage_le_fpqcPrecoverage
-/
lemma zariskiTopology_le_fpqcTopology : zariskiTopology <= fpqcTopology :=
  Precoverage.toGrothendieck_mono zariskiPrecoverage_le_fpqcPrecoverage

/--
lemma `fppfTopology_le_fpqcTopology` / 引理 `fppfTopology_le_fpqcTopology`

English:
lemma fppfTopology_le_fpqcTopology
  statement: fppfTopology <= fpqcTopology
  proof: Precoverage.toGrothendieck_mono fppfPrecoverage_le_fpqcPrecoverage

中文:
引理 fppfTopology_le_fpqcTopology
  结论: fppfTopology <= fpqcTopology
  证明: Precoverage.toGrothendieck_mono fppfPrecoverage_le_fpqcPrecoverage

Depends on / 依赖: Precoverage, Precoverage.toGrothendieck_mono, fppfPrecoverage_le_fpqcPrecoverage, toGrothendieck_mono
-/
lemma fppfTopology_le_fpqcTopology : fppfTopology <= fpqcTopology :=
  Precoverage.toGrothendieck_mono fppfPrecoverage_le_fpqcPrecoverage

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: fpqcTopology.Subcanonical
  body: by
  refine GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj _ fun X => ?_
  rw [fpqcTopology_eq_propQCTopology]; rw [isSheaf_type_propQCTopology_iff]
  refine ⟨?_, ?_⟩
  · exact GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _
  · intro R S f hf₁ hf₂
    have : IsRegularEpi (Sp

中文:
实例 :
  签名: fpqcTopology.Subcanonical
  定义体: by
  refine GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj _ fun X => ?_
  rw [fpqcTopology_eq_propQCTopology]; rw [isSheaf_type_propQCTopology_iff]
  refine ⟨?_, ?_⟩
  · exact GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _
  · intro R S f hf₁ hf₂
    have : IsRegularEpi (Sp

Depends on / 依赖: GrothendieckTopology, GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable, GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj, IsRegularEpi, Spec.map, Subcanonical, fpqcTopology_eq_propQCTopology, isRegularEpi_of_flat_of_surjective_of_isAffine, isSheaf_of_isRepresentable, isSheaf_type_propQCTopology_iff, of_isSheaf_yoneda_obj, singleton_of_isRepresentable_of_effectiveEpi
-/
instance : fpqcTopology.Subcanonical := by
  refine GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj _ fun X => ?_
  rw [fpqcTopology_eq_propQCTopology]; rw [isSheaf_type_propQCTopology_iff]
  refine ⟨?_, ?_⟩
  · exact GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _
  · intro R S f hf₁ hf₂
    have : IsRegularEpi (Spec.map f) :=
      isRegularEpi_of_flat_of_surjective_of_isAffine _
    exact .singleton_of_isRepresentable_of_effectiveEpi _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: fppfTopology.Subcanonical
  body: .of_le fppfTopology_le_fpqcTopology

@[simp]

中文:
实例 :
  签名: fppfTopology.Subcanonical
  定义体: .of_le fppfTopology_le_fpqcTopology

@[simp]

Depends on / 依赖: fppfTopology_le_fpqcTopology, of_le
-/
instance : fppfTopology.Subcanonical :=
  .of_le fppfTopology_le_fpqcTopology

@[simp]
/--
lemma `Hom.singleton_mem_fppfPrecoverage` / 引理 `Hom.singleton_mem_fppfPrecoverage`

English:
lemma Hom.singleton_mem_fppfPrecoverage
  statement: {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [Surjective f]
  proof: by
  rw [← Presieve.ofArrows_pUnit.{0}]
  exact (f.cover (P := @Flat ⊓ @LocallyOfFinitePresentation) ⟨‹_›, ‹_›⟩).mem₀

@[simp]

中文:
引理 Hom.singleton_mem_fppfPrecoverage
  结论: {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [Surjective f]
  证明: by
  rw [← Presieve.ofArrows_pUnit.{0}]
  exact (f.cover (P := @Flat ⊓ @LocallyOfFinitePresentation) ⟨‹_›, ‹_›⟩).mem₀

@[simp]

Depends on / 依赖: LocallyOfFinitePresentation, Presieve, Presieve.ofArrows_pUnit, f.cover, ofArrows_pUnit
-/
lemma Hom.singleton_mem_fppfPrecoverage {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [Surjective f]
    [LocallyOfFinitePresentation f] :
    Presieve.singleton f in fppfPrecoverage Y := by
  rw [← Presieve.ofArrows_pUnit.{0}]
  exact (f.cover (P := @Flat ⊓ @LocallyOfFinitePresentation) ⟨‹_›, ‹_›⟩).mem₀

@[simp]
/--
lemma `Hom.singleton_mem_fpqcPrecoverage` / 引理 `Hom.singleton_mem_fpqcPrecoverage`

English:
lemma Hom.singleton_mem_fpqcPrecoverage
  statement: {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [Surjective f]
  proof: Hom.singleton_mem_propQCPrecoverage ‹_›

中文:
引理 Hom.singleton_mem_fpqcPrecoverage
  结论: {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [Surjective f]
  证明: Hom.singleton_mem_propQCPrecoverage ‹_›

Depends on / 依赖: Hom.singleton_mem_propQCPrecoverage, singleton_mem_propQCPrecoverage
-/
lemma Hom.singleton_mem_fpqcPrecoverage {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [Surjective f]
    [QuasiCompact f] :
    Presieve.singleton f in fpqcPrecoverage Y :=
  Hom.singleton_mem_propQCPrecoverage ‹_›

/-- Any surjective, quasi-compact and flat morphism is an effective epimorphism. -/
instance {X Y : Scheme} (f : X ⟶ Y) [QuasiCompact f] [Surjective f] [Flat f] : EffectiveEpi f := by
  rw [← Sieve.effectiveEpimorphic_singleton]; rw [Presieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda]
  intro Z
  exact (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _).isSheafFor _
    (Precoverage.generate_mem_toGrothendieck f.singleton_mem_fpqcPrecoverage)

/-- Any surjective, flat morphism locally of finite presentation is an effective epimorphism.
In particular, étale surjections satisfy this. -/
instance {X Y : Scheme} (f : X ⟶ Y) [LocallyOfFinitePresentation f] [Surjective f] [Flat f] :
    EffectiveEpi f := by
  rw [← Sieve.effectiveEpimorphic_singleton]; rw [Presieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda]
  intro Z
  exact (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _).isSheafFor _
    (Precoverage.generate_mem_toGrothendieck f.singleton_mem_fppfPrecoverage)

end AlgebraicGeometry.Scheme
