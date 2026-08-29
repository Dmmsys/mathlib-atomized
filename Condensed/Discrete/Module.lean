/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Condensed.Discrete.LocallyConstant
public import Mathlib.Condensed.Light.Module
public import Mathlib.Condensed.Module
public import Mathlib.Topology.LocallyConstant.Algebra
/-!

# Discrete condensed `R`-modules

This file provides the necessary API to prove that a condensed `R`-module is discrete if and only
if the underlying condensed set is (both for light condensed and condensed).

That is, it defines the functor `CondensedMod.LocallyConstant.functor` which takes an `R`-module to
the condensed `R`-modules given by locally constant maps to it, and proves that this functor is
naturally isomorphic to the constant sheaf functor (and the analogues for light condensed modules).
-/

@[expose] public section

universe w u

open CategoryTheory LocallyConstant CompHausLike Functor Category Functor Opposite

variable {P : TopCat.{u} -> Prop}

namespace CompHausLike.LocallyConstantModule

variable (R : Type (max u w)) [Ring R]

/--
The functor from the category of `R`-modules to presheaves on `CompHausLike P` given by locally
constant maps.
-/
@[simps]
/--
Definition of `functorToPresheaves` / `functorToPresheaves` 的定义

English:
definition functorToPresheaves
  signature: : ModuleCat.{max u w} R ⥤ ((CompHausLike.{u} P)ᵒᵖ ⥤ ModuleCat R) where
  body: {
    obj := fun ⟨S⟩ => ModuleCat.of R (LocallyConstant S X)
    map := fun f => ModuleCat.ofHom (comapₗ R f.unop.hom.hom) }
  map f := { app := fun S => ModuleCat.ofHom (mapₗ R f.hom) }

中文:
定义 functorToPresheaves
  签名: : 模范畴.{最大值 u w} R ⥤ ((余mpHausLike.{u} P)ᵒᵖ ⥤ 模范畴 R) where
  定义体: {
    obj := fun ⟨S⟩ => ModuleCat.of R (LocallyConstant S X)
    map := fun f => ModuleCat.ofHom (comapₗ R f.unop.hom.hom) }
  map f := { app := fun S => ModuleCat.ofHom (mapₗ R f.hom) }

Depends on / 依赖: FunLike, toFunLike
-/
def functorToPresheaves : ModuleCat.{max u w} R ⥤ ((CompHausLike.{u} P)ᵒᵖ ⥤ ModuleCat R) where
  obj X := {
    obj := fun ⟨S⟩ => ModuleCat.of R (LocallyConstant S X)
    map := fun f => ModuleCat.ofHom (comapₗ R f.unop.hom.hom) }
  map f := { app := fun S => ModuleCat.ofHom (mapₗ R f.hom) }

variable [HasExplicitFiniteCoproducts.{0} P] [HasExplicitPullbacks.{u} P]
  (hs : forall ⦃X Y : CompHausLike P⦄ (f : X ⟶ Y), EffectiveEpi f -> Function.Surjective f)

/-- `CompHausLike.LocallyConstantModule.functorToPresheaves` lands in sheaves. -/
@[simps!]
/--
Definition of `functor` / `functor` 的定义

English:
definition functor
  signature: : haveI
  body: CompHausLike.preregular hs
    ModuleCat R ⥤ Sheaf (coherentTopology (CompHausLike.{u} P)) (ModuleCat R) :=
  ObjectProperty.lift _ (functorToPresheaves.{w, u} R) (fun X => by
    have := CompHausLike.preregular hs
    apply Presheaf.isSheaf_coherent_of_hasPullbacks_of_comp
      (s := CategoryTheory.forget (ModuleCat R))
    exact ((CompHausLike.LocallyConstant.functor P hs).obj _).property)

中文:
定义 functor
  签名: : haveI
  定义体: CompHausLike.preregular hs
    ModuleCat R ⥤ Sheaf (coherentTopology (CompHausLike.{u} P)) (ModuleCat R) :=
  ObjectProperty.lift _ (functorToPresheaves.{w, u} R) (fun X => by
    have := CompHausLike.preregular hs
    apply Presheaf.isSheaf_coherent_of_hasPullbacks_of_comp
      (s := CategoryTheory.forget (ModuleCat R))
    exact ((CompHausLike.LocallyConstant.functor P hs).obj _).property)

Depends on / 依赖: CompHausLike, CompHausLike.preregular, preregular
-/
def functor : haveI := CompHausLike.preregular hs
    ModuleCat R ⥤ Sheaf (coherentTopology (CompHausLike.{u} P)) (ModuleCat R) :=
  ObjectProperty.lift _ (functorToPresheaves.{w, u} R) (fun X => by
    have := CompHausLike.preregular hs
    apply Presheaf.isSheaf_coherent_of_hasPullbacks_of_comp
      (s := CategoryTheory.forget (ModuleCat R))
    exact ((CompHausLike.LocallyConstant.functor P hs).obj _).property)

end CompHausLike.LocallyConstantModule

namespace CondensedMod.LocallyConstant

open Condensed

variable (R : Type (u + 1)) [Ring R]

/--
Definition of `functorToPresheaves` / `functorToPresheaves` 的定义

English:
abbreviation functorToPresheaves
  signature: : ModuleCat.{u + 1} R ⥤ (CompHaus.{u}ᵒᵖ ⥤ ModuleCat R)
  body: CompHausLike.LocallyConstantModule.functorToPresheaves.{u + 1, u} R

中文:
缩写 functorToPresheaves
  签名: : 模范畴.{u + 1} R ⥤ (CompHaus.{u}ᵒᵖ ⥤ 模范畴 R)
  定义体: CompHausLike.LocallyConstantModule.functorToPresheaves.{u + 1, u} R

Depends on / 依赖: CompHausLike, CompHausLike.LocallyConstantModule.functorToPresheaves, EmbeddingLike, LocallyConstantModule, functorToPresheaves, toEmbeddingLike
-/
abbrev functorToPresheaves : ModuleCat.{u + 1} R ⥤ (CompHaus.{u}ᵒᵖ ⥤ ModuleCat R) :=
  CompHausLike.LocallyConstantModule.functorToPresheaves.{u + 1, u} R

/--
Definition of `functor` / `functor` 的定义

English:
abbreviation functor
  signature: : ModuleCat R ⥤ CondensedMod.{u} R
  body: CompHausLike.LocallyConstantModule.functor.{u + 1, u} R
    (fun _ _ _ => ((CompHaus.effectiveEpi_tfae _).out 0 2).mp)

中文:
缩写 functor
  签名: : 模范畴 R ⥤ CondensedMod.{u} R
  定义体: CompHausLike.LocallyConstantModule.functor.{u + 1, u} R
    (fun _ _ _ => ((CompHaus.effectiveEpi_tfae _).out 0 2).mp)

Depends on / 依赖: CompHaus, CompHaus.effectiveEpi_tfae, CompHausLike, CompHausLike.LocallyConstantModule.functor, LocallyConstantModule, effectiveEpi_tfae, functor
-/
abbrev functor : ModuleCat R ⥤ CondensedMod.{u} R :=
  CompHausLike.LocallyConstantModule.functor.{u + 1, u} R
    (fun _ _ _ => ((CompHaus.effectiveEpi_tfae _).out 0 2).mp)

/--
Definition of `functorIsoDiscreteAux₁` / `functorIsoDiscreteAux₁` 的定义

English:
definition functorIsoDiscreteAux₁
  signature: (M : ModuleCat.{u + 1} R)
  body: ModuleCat.ofHom (constₗ R)
  inv := ModuleCat.ofHom (evalₗ R PUnit.unit)

中文:
定义 functorIsoDiscreteAux₁
  签名: (M : 模范畴.{u + 1} R)
  定义体: ModuleCat.ofHom (constₗ R)
  inv := ModuleCat.ofHom (evalₗ R PUnit.unit)

Depends on / 依赖: ModuleCat, ModuleCat.ofHom
-/
noncomputable def functorIsoDiscreteAux₁ (M : ModuleCat.{u + 1} R) :
    M ≅ (ModuleCat.of R (LocallyConstant (CompHaus.of PUnit.{u + 1}) M)) where
  hom := ModuleCat.ofHom (constₗ R)
  inv := ModuleCat.ofHom (evalₗ R PUnit.unit)

/--
Definition of `functorIsoDiscreteAux₂` / `functorIsoDiscreteAux₂` 的定义

English:
definition functorIsoDiscreteAux₂
  signature: (M : ModuleCat R)
  body: (discrete _).mapIso (functorIsoDiscreteAux₁ R M)

中文:
定义 functorIsoDiscreteAux₂
  签名: (M : 模范畴 R)
  定义体: (discrete _).mapIso (functorIsoDiscreteAux₁ R M)

Depends on / 依赖: discrete, mapIso
-/
noncomputable def functorIsoDiscreteAux₂ (M : ModuleCat R) :
    (discrete _).obj M ≅ (discrete _).obj
      (ModuleCat.of R (LocallyConstant (CompHaus.of PUnit.{u + 1}) M)) :=
  (discrete _).mapIso (functorIsoDiscreteAux₁ R M)

set_option backward.isDefEq.respectTransparency false in
instance (M : ModuleCat R) : IsIso ((forget R).map
    ((discreteUnderlyingAdj (ModuleCat R)).counit.app ((functor R).obj M))) := by
  dsimp [Condensed.forget, discreteUnderlyingAdj]
  rw [← constantSheafAdj_counit_w]
  refine IsIso.comp_isIso' inferInstance ?_
  have : (constantSheaf (coherentTopology CompHaus) (Type (u + 1))).Faithful :=
    inferInstanceAs (discrete _).Faithful
  have : (constantSheaf (coherentTopology CompHaus) (Type (u + 1))).Full :=
    inferInstanceAs (discrete _).Full
  rw [← Sheaf.isConstant_iff_isIso_counit_app]
  constructor
  change (discrete _).essImage _
  rw [essImage_eq_of_natIso CondensedSet.LocallyConstant.iso.symm]
  exact obj_mem_essImage CondensedSet.LocallyConstant.functor M

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `functorIsoDiscreteComponents` / `functorIsoDiscreteComponents` 的定义

English:
definition functorIsoDiscreteComponents
  signature: (M : ModuleCat R)
  body: have : (Condensed.forget R).ReflectsIsomorphisms :=
    inferInstanceAs (sheafCompose _ _).ReflectsIsomorphisms
  have : IsIso ((discreteUnderlyingAdj (ModuleCat R)).counit.app ((functor R).obj M)) :=
    isIso_of_reflects_iso _ (Condensed.forget R)
  functorIsoDiscreteAux₂ R M ≪≫ asIso ((discreteUnderlyingAdj _).counit.app ((functor R).obj M))

中文:
定义 functorIsoDiscreteComponents
  签名: (M : 模范畴 R)
  定义体: have : (Condensed.forget R).ReflectsIsomorphisms :=
    inferInstanceAs (sheafCompose _ _).ReflectsIsomorphisms
  have : IsIso ((discreteUnderlyingAdj (ModuleCat R)).counit.app ((functor R).obj M)) :=
    isIso_of_reflects_iso _ (Condensed.forget R)
  functorIsoDiscreteAux₂ R M ≪≫ asIso ((discreteUnderlyingAdj _).counit.app ((functor R).obj M))

Depends on / 依赖: Condensed, Condensed.forget, ModuleCat, ReflectsIsomorphisms, counit, counit.app, discreteUnderlyingAdj, forget, functor, isIso_of_reflects_iso, sheafCompose
-/
noncomputable def functorIsoDiscreteComponents (M : ModuleCat R) :
    (discrete _).obj M ≅ (functor R).obj M :=
  have : (Condensed.forget R).ReflectsIsomorphisms :=
    inferInstanceAs (sheafCompose _ _).ReflectsIsomorphisms
  have : IsIso ((discreteUnderlyingAdj (ModuleCat R)).counit.app ((functor R).obj M)) :=
    isIso_of_reflects_iso _ (Condensed.forget R)
  functorIsoDiscreteAux₂ R M ≪≫ asIso ((discreteUnderlyingAdj _).counit.app ((functor R).obj M))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `functorIsoDiscrete` / `functorIsoDiscrete` 的定义

English:
definition functorIsoDiscrete
  signature: : functor R ≅ discrete _
  body: NatIso.ofComponents (fun M => (functorIsoDiscreteComponents R M).symm) fun f => by
    dsimp
    rw [Iso.eq_inv_comp]; rw [← Category.assoc]; rw [Iso.comp_inv_eq]
    dsimp [functorIsoDiscreteComponents]
    rw [assoc]; rw [← Iso.eq_inv_comp]; rw [← (discreteUnderlyingAdj (ModuleCat R)).counit_naturality]
    simp only [← assoc]
    congr 1
    rw [← Iso.comp_inv_eq]
    apply Sheaf.hom_ext
    simp [functorIsoDiscreteAux₂, ← Functor.map_comp]
    rfl

中文:
定义 functorIsoDiscrete
  签名: : functor R ≅ discrete _
  定义体: NatIso.ofComponents (fun M => (functorIsoDiscreteComponents R M).symm) fun f => by
    dsimp
    rw [Iso.eq_inv_comp]; rw [← Category.assoc]; rw [Iso.comp_inv_eq]
    dsimp [functorIsoDiscreteComponents]
    rw [assoc]; rw [← Iso.eq_inv_comp]; rw [← (discreteUnderlyingAdj (ModuleCat R)).counit_naturality]
    simp only [← assoc]
    congr 1
    rw [← Iso.comp_inv_eq]
    apply Sheaf.hom_ext
    simp [functorIsoDiscreteAux₂, ← Functor.map_comp]
    rfl

Depends on / 依赖: Category, Category.assoc, Functor, Functor.map_comp, Iso.comp_inv_eq, Iso.eq_inv_comp, ModuleCat, NatIso, NatIso.ofComponents, Sheaf.hom_ext, comp_inv_eq, counit_naturality, discreteUnderlyingAdj, eq_inv_comp, functorIsoDiscreteComponents, hom_ext, map_comp, ofComponents
-/
noncomputable def functorIsoDiscrete : functor R ≅ discrete _ :=
  NatIso.ofComponents (fun M => (functorIsoDiscreteComponents R M).symm) fun f => by
    dsimp
    rw [Iso.eq_inv_comp]; rw [← Category.assoc]; rw [Iso.comp_inv_eq]
    dsimp [functorIsoDiscreteComponents]
    rw [assoc]; rw [← Iso.eq_inv_comp]; rw [← (discreteUnderlyingAdj (ModuleCat R)).counit_naturality]
    simp only [← assoc]
    congr 1
    rw [← Iso.comp_inv_eq]
    apply Sheaf.hom_ext
    simp [functorIsoDiscreteAux₂, ← Functor.map_comp]
    rfl

/--
Definition of `adjunction` / `adjunction` 的定义

English:
definition adjunction
  signature: : functor R ⊣ underlying (ModuleCat R)
  body: Adjunction.ofNatIsoLeft (discreteUnderlyingAdj _) (functorIsoDiscrete R).symm

中文:
定义 adjunction
  签名: : functor R ⊣ underlying (模范畴 R)
  定义体: Adjunction.ofNatIsoLeft (discreteUnderlyingAdj _) (functorIsoDiscrete R).symm

Depends on / 依赖: Adjunction, Adjunction.ofNatIsoLeft, discreteUnderlyingAdj, functorIsoDiscrete, ofNatIsoLeft
-/
noncomputable def adjunction : functor R ⊣ underlying (ModuleCat R) :=
  Adjunction.ofNatIsoLeft (discreteUnderlyingAdj _) (functorIsoDiscrete R).symm

/--
Definition of `fullyFaithfulFunctor` / `fullyFaithfulFunctor` 的定义

English:
definition fullyFaithfulFunctor
  signature: : (functor R).FullyFaithful
  body: (adjunction R).fullyFaithfulLOfCompIsoId
    (NatIso.ofComponents fun M => (functorIsoDiscreteAux₁ R _).symm)

中文:
定义 fullyFaithfulFunctor
  签名: : (functor R).满忠实
  定义体: (adjunction R).fullyFaithfulLOfCompIsoId
    (NatIso.ofComponents fun M => (functorIsoDiscreteAux₁ R _).symm)

Depends on / 依赖: NatIso, NatIso.ofComponents, adjunction, fullyFaithfulLOfCompIsoId, ofComponents
-/
noncomputable def fullyFaithfulFunctor : (functor R).FullyFaithful :=
  (adjunction R).fullyFaithfulLOfCompIsoId
    (NatIso.ofComponents fun M => (functorIsoDiscreteAux₁ R _).symm)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (functor R).Faithful
  body: (fullyFaithfulFunctor R).faithful

中文:
实例 :
  签名: (functor R).忠实
  定义体: (fullyFaithfulFunctor R).faithful

Depends on / 依赖: faithful, fullyFaithfulFunctor
-/
instance : (functor R).Faithful := (fullyFaithfulFunctor R).faithful

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (functor R).Full
  body: (fullyFaithfulFunctor R).full

中文:
实例 :
  签名: (functor R).满
  定义体: (fullyFaithfulFunctor R).full

Depends on / 依赖: fullyFaithfulFunctor
-/
instance : (functor R).Full := (fullyFaithfulFunctor R).full

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (discrete (ModuleCat R)).Faithful
  body: Functor.Faithful.of_iso (functorIsoDiscrete R)

中文:
实例 :
  签名: (discrete (模范畴 R)).忠实
  定义体: Functor.Faithful.of_iso (functorIsoDiscrete R)

Depends on / 依赖: Faithful, Functor, Functor.Faithful.of_iso, functorIsoDiscrete, of_iso
-/
instance : (discrete (ModuleCat R)).Faithful :=
  Functor.Faithful.of_iso (functorIsoDiscrete R)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (constantSheaf (coherentTopology CompHaus) (ModuleCat.{u + 1} R)).Faithful
  body: inferInstanceAs (discrete (ModuleCat R)).Faithful

中文:
实例 :
  签名: (constantSheaf (coherentTopology CompHaus) (模范畴.{u + 1} R)).忠实
  定义体: inferInstanceAs (discrete (ModuleCat R)).Faithful

Depends on / 依赖: Faithful, ModuleCat, discrete
-/
instance : (constantSheaf (coherentTopology CompHaus) (ModuleCat.{u + 1} R)).Faithful :=
  inferInstanceAs (discrete (ModuleCat R)).Faithful

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (discrete (ModuleCat R)).Full
  body: Functor.Full.of_iso (functorIsoDiscrete R)

中文:
实例 :
  签名: (discrete (模范畴 R)).满
  定义体: Functor.Full.of_iso (functorIsoDiscrete R)

Depends on / 依赖: Functor, Functor.Full.of_iso, functorIsoDiscrete, of_iso
-/
instance : (discrete (ModuleCat R)).Full :=
  Functor.Full.of_iso (functorIsoDiscrete R)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (constantSheaf (coherentTopology CompHaus) (ModuleCat.{u + 1} R)).Full
  body: inferInstanceAs (discrete (ModuleCat R)).Full

中文:
实例 :
  签名: (constantSheaf (coherentTopology CompHaus) (模范畴.{u + 1} R)).满
  定义体: inferInstanceAs (discrete (ModuleCat R)).Full

Depends on / 依赖: ModuleCat, discrete
-/
instance : (constantSheaf (coherentTopology CompHaus) (ModuleCat.{u + 1} R)).Full :=
  inferInstanceAs (discrete (ModuleCat R)).Full

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (constantSheaf (coherentTopology CompHaus) (Type (u + 1))).Faithful
  body: inferInstanceAs (discrete (Type (u + 1))).Faithful

中文:
实例 :
  签名: (constantSheaf (coherentTopology CompHaus) (类型 (u + 1))).忠实
  定义体: inferInstanceAs (discrete (Type (u + 1))).Faithful

Depends on / 依赖: Faithful, discrete
-/
instance : (constantSheaf (coherentTopology CompHaus) (Type (u + 1))).Faithful :=
  inferInstanceAs (discrete (Type (u + 1))).Faithful

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (constantSheaf (coherentTopology CompHaus) (Type (u + 1))).Full
  body: inferInstanceAs (discrete (Type (u + 1))).Full

中文:
实例 :
  签名: (constantSheaf (coherentTopology CompHaus) (类型 (u + 1))).满
  定义体: inferInstanceAs (discrete (Type (u + 1))).Full

Depends on / 依赖: FunLike, FunLike.toDecidableEq, discrete, toDecidableEq
-/
instance : (constantSheaf (coherentTopology CompHaus) (Type (u + 1))).Full :=
  inferInstanceAs (discrete (Type (u + 1))).Full

end CondensedMod.LocallyConstant

namespace LightCondMod.LocallyConstant

open LightCondensed

variable (R : Type u) [Ring R]

/--
Definition of `functorToPresheaves` / `functorToPresheaves` 的定义

English:
abbreviation functorToPresheaves
  signature: : ModuleCat.{u} R ⥤ (LightProfinite.{u}ᵒᵖ ⥤ ModuleCat R)
  body: CompHausLike.LocallyConstantModule.functorToPresheaves.{u, u} R

中文:
缩写 functorToPresheaves
  签名: : 模范畴.{u} R ⥤ (LightProfinite.{u}ᵒᵖ ⥤ 模范畴 R)
  定义体: CompHausLike.LocallyConstantModule.functorToPresheaves.{u, u} R

Depends on / 依赖: CompHausLike, CompHausLike.LocallyConstantModule.functorToPresheaves, LocallyConstantModule, functorToPresheaves
-/
abbrev functorToPresheaves : ModuleCat.{u} R ⥤ (LightProfinite.{u}ᵒᵖ ⥤ ModuleCat R) :=
  CompHausLike.LocallyConstantModule.functorToPresheaves.{u, u} R

/--
Definition of `functor` / `functor` 的定义

English:
abbreviation functor
  signature: : ModuleCat R ⥤ LightCondMod.{u} R
  body: CompHausLike.LocallyConstantModule.functor.{u, u} R
    (fun _ _ _ => (LightProfinite.effectiveEpi_iff_surjective _).mp)

中文:
缩写 functor
  签名: : 模范畴 R ⥤ LightCondMod.{u} R
  定义体: CompHausLike.LocallyConstantModule.functor.{u, u} R
    (fun _ _ _ => (LightProfinite.effectiveEpi_iff_surjective _).mp)

Depends on / 依赖: CompHausLike, CompHausLike.LocallyConstantModule.functor, LightProfinite, LightProfinite.effectiveEpi_iff_surjective, LocallyConstantModule, effectiveEpi_iff_surjective, functor
-/
abbrev functor : ModuleCat R ⥤ LightCondMod.{u} R :=
  CompHausLike.LocallyConstantModule.functor.{u, u} R
    (fun _ _ _ => (LightProfinite.effectiveEpi_iff_surjective _).mp)

/--
Definition of `functorIsoDiscreteAux₁` / `functorIsoDiscreteAux₁` 的定义

English:
definition functorIsoDiscreteAux₁
  signature: (M : ModuleCat.{u} R)
  body: ModuleCat.ofHom (constₗ R)
  inv := ModuleCat.ofHom (evalₗ R PUnit.unit)

中文:
定义 functorIsoDiscreteAux₁
  签名: (M : 模范畴.{u} R)
  定义体: ModuleCat.ofHom (constₗ R)
  inv := ModuleCat.ofHom (evalₗ R PUnit.unit)

Depends on / 依赖: GradedEquivLike, GradedEquivLike.toGradedFunLike, GradedFunLike, ModuleCat, ModuleCat.ofHom, toGradedFunLike
-/
noncomputable def functorIsoDiscreteAux₁ (M : ModuleCat.{u} R) :
    M ≅ (ModuleCat.of R (LocallyConstant (LightProfinite.of PUnit.{u + 1}) M)) where
  hom := ModuleCat.ofHom (constₗ R)
  inv := ModuleCat.ofHom (evalₗ R PUnit.unit)

/--
Definition of `functorIsoDiscreteAux₂` / `functorIsoDiscreteAux₂` 的定义

English:
definition functorIsoDiscreteAux₂
  signature: (M : ModuleCat.{u} R)
  body: (discrete _).mapIso (functorIsoDiscreteAux₁ R M)

中文:
定义 functorIsoDiscreteAux₂
  签名: (M : 模范畴.{u} R)
  定义体: (discrete _).mapIso (functorIsoDiscreteAux₁ R M)

Depends on / 依赖: discrete, mapIso
-/
noncomputable def functorIsoDiscreteAux₂ (M : ModuleCat.{u} R) :
    (discrete _).obj M ≅ (discrete _).obj
      (ModuleCat.of R (LocallyConstant (LightProfinite.of PUnit.{u + 1}) M)) :=
  (discrete _).mapIso (functorIsoDiscreteAux₁ R M)

-- Not stating this explicitly causes timeouts below.
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasSheafify (coherentTopology LightProfinite.{u}) (ModuleCat.{u} R)
  body: inferInstance

中文:
实例 :
  签名: 有Sheafify (coherentTopology LightProfinite.{u}) (模范畴.{u} R)
  定义体: inferInstance
-/
instance : HasSheafify (coherentTopology LightProfinite.{u}) (ModuleCat.{u} R) :=
  inferInstance

set_option backward.isDefEq.respectTransparency false in
instance (M : ModuleCat R) :
    IsIso ((LightCondensed.forget R).map
    ((discreteUnderlyingAdj (ModuleCat R)).counit.app
      ((functor R).obj M))) := by
  dsimp [LightCondensed.forget, discreteUnderlyingAdj]
  rw [← constantSheafAdj_counit_w]
  refine IsIso.comp_isIso' inferInstance ?_
  have : (constantSheaf (coherentTopology LightProfinite.{u}) (Type u)).Faithful :=
    inferInstanceAs (discrete _).Faithful
  have : (constantSheaf (coherentTopology LightProfinite.{u}) (Type u)).Full :=
    inferInstanceAs (discrete (Type u)).Full
  rw [← Sheaf.isConstant_iff_isIso_counit_app]
  constructor
  change (discrete _).essImage _
  rw [essImage_eq_of_natIso LightCondSet.LocallyConstant.iso.symm]
  exact obj_mem_essImage LightCondSet.LocallyConstant.functor M

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `functorIsoDiscreteComponents` / `functorIsoDiscreteComponents` 的定义

English:
definition functorIsoDiscreteComponents
  signature: (M : ModuleCat R)
  body: have : (LightCondensed.forget R).ReflectsIsomorphisms :=
    inferInstanceAs (sheafCompose _ _).ReflectsIsomorphisms
  have : IsIso ((discreteUnderlyingAdj (ModuleCat R)).counit.app ((functor R).obj M)) :=
    isIso_of_reflects_iso _ (LightCondensed.forget R)
  functorIsoDiscreteAux₂ R M ≪≫ asIso ((discreteUnderlyingAdj _).counit.app ((functor R).obj M))

中文:
定义 functorIsoDiscreteComponents
  签名: (M : 模范畴 R)
  定义体: have : (LightCondensed.forget R).ReflectsIsomorphisms :=
    inferInstanceAs (sheafCompose _ _).ReflectsIsomorphisms
  have : IsIso ((discreteUnderlyingAdj (ModuleCat R)).counit.app ((functor R).obj M)) :=
    isIso_of_reflects_iso _ (LightCondensed.forget R)
  functorIsoDiscreteAux₂ R M ≪≫ asIso ((discreteUnderlyingAdj _).counit.app ((functor R).obj M))

Depends on / 依赖: LightCondensed, LightCondensed.forget, ModuleCat, ReflectsIsomorphisms, counit, counit.app, discreteUnderlyingAdj, forget, functor, isIso_of_reflects_iso, sheafCompose
-/
noncomputable def functorIsoDiscreteComponents (M : ModuleCat R) :
    (discrete _).obj M ≅ (functor R).obj M :=
  have : (LightCondensed.forget R).ReflectsIsomorphisms :=
    inferInstanceAs (sheafCompose _ _).ReflectsIsomorphisms
  have : IsIso ((discreteUnderlyingAdj (ModuleCat R)).counit.app ((functor R).obj M)) :=
    isIso_of_reflects_iso _ (LightCondensed.forget R)
  functorIsoDiscreteAux₂ R M ≪≫ asIso ((discreteUnderlyingAdj _).counit.app ((functor R).obj M))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `functorIsoDiscrete` / `functorIsoDiscrete` 的定义

English:
definition functorIsoDiscrete
  signature: : functor R ≅ discrete _
  body: NatIso.ofComponents (fun M => (functorIsoDiscreteComponents R M).symm) fun f => by
    dsimp
    rw [Iso.eq_inv_comp]; rw [← Category.assoc]; rw [Iso.comp_inv_eq]
    dsimp [functorIsoDiscreteComponents]
    rw [Category.assoc]; rw [← Iso.eq_inv_comp]; rw [← (discreteUnderlyingAdj (ModuleCat R)).counit_naturality]
    simp only [← assoc]
    congr 1
    rw [← Iso.comp_inv_eq]
    apply Sheaf.hom_ext
    simp [functorIsoDiscreteAux₂, ← Functor.map_comp]
    rfl

中文:
定义 functorIsoDiscrete
  签名: : functor R ≅ discrete _
  定义体: NatIso.ofComponents (fun M => (functorIsoDiscreteComponents R M).symm) fun f => by
    dsimp
    rw [Iso.eq_inv_comp]; rw [← Category.assoc]; rw [Iso.comp_inv_eq]
    dsimp [functorIsoDiscreteComponents]
    rw [Category.assoc]; rw [← Iso.eq_inv_comp]; rw [← (discreteUnderlyingAdj (ModuleCat R)).counit_naturality]
    simp only [← assoc]
    congr 1
    rw [← Iso.comp_inv_eq]
    apply Sheaf.hom_ext
    simp [functorIsoDiscreteAux₂, ← Functor.map_comp]
    rfl

Depends on / 依赖: Category, Category.assoc, Functor, Functor.map_comp, Iso.comp_inv_eq, Iso.eq_inv_comp, ModuleCat, NatIso, NatIso.ofComponents, Sheaf.hom_ext, comp_inv_eq, counit_naturality, discreteUnderlyingAdj, eq_inv_comp, functorIsoDiscreteComponents, hom_ext, map_comp, ofComponents
-/
noncomputable def functorIsoDiscrete : functor R ≅ discrete _ :=
  NatIso.ofComponents (fun M => (functorIsoDiscreteComponents R M).symm) fun f => by
    dsimp
    rw [Iso.eq_inv_comp]; rw [← Category.assoc]; rw [Iso.comp_inv_eq]
    dsimp [functorIsoDiscreteComponents]
    rw [Category.assoc]; rw [← Iso.eq_inv_comp]; rw [← (discreteUnderlyingAdj (ModuleCat R)).counit_naturality]
    simp only [← assoc]
    congr 1
    rw [← Iso.comp_inv_eq]
    apply Sheaf.hom_ext
    simp [functorIsoDiscreteAux₂, ← Functor.map_comp]
    rfl

/--
Definition of `adjunction` / `adjunction` 的定义

English:
definition adjunction
  signature: : functor R ⊣ underlying (ModuleCat R)
  body: Adjunction.ofNatIsoLeft (discreteUnderlyingAdj _) (functorIsoDiscrete R).symm

中文:
定义 adjunction
  签名: : functor R ⊣ underlying (模范畴 R)
  定义体: Adjunction.ofNatIsoLeft (discreteUnderlyingAdj _) (functorIsoDiscrete R).symm

Depends on / 依赖: Adjunction, Adjunction.ofNatIsoLeft, discreteUnderlyingAdj, functorIsoDiscrete, ofNatIsoLeft
-/
noncomputable def adjunction : functor R ⊣ underlying (ModuleCat R) :=
  Adjunction.ofNatIsoLeft (discreteUnderlyingAdj _) (functorIsoDiscrete R).symm

/--
Definition of `fullyFaithfulFunctor` / `fullyFaithfulFunctor` 的定义

English:
definition fullyFaithfulFunctor
  signature: : (functor R).FullyFaithful
  body: (adjunction R).fullyFaithfulLOfCompIsoId
    (NatIso.ofComponents fun M => (functorIsoDiscreteAux₁ R _).symm)

中文:
定义 fullyFaithfulFunctor
  签名: : (functor R).满忠实
  定义体: (adjunction R).fullyFaithfulLOfCompIsoId
    (NatIso.ofComponents fun M => (functorIsoDiscreteAux₁ R _).symm)

Depends on / 依赖: NatIso, NatIso.ofComponents, adjunction, fullyFaithfulLOfCompIsoId, ofComponents
-/
noncomputable def fullyFaithfulFunctor : (functor R).FullyFaithful :=
  (adjunction R).fullyFaithfulLOfCompIsoId
    (NatIso.ofComponents fun M => (functorIsoDiscreteAux₁ R _).symm)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (functor R).Faithful
  body: (fullyFaithfulFunctor R).faithful

中文:
实例 :
  签名: (functor R).忠实
  定义体: (fullyFaithfulFunctor R).faithful

Depends on / 依赖: faithful, fullyFaithfulFunctor
-/
instance : (functor R).Faithful := (fullyFaithfulFunctor R).faithful

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (functor R).Full
  body: (fullyFaithfulFunctor R).full

中文:
实例 :
  签名: (functor R).满
  定义体: (fullyFaithfulFunctor R).full

Depends on / 依赖: fullyFaithfulFunctor
-/
instance : (functor R).Full := (fullyFaithfulFunctor R).full

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (discrete.{u} (ModuleCat R)).Faithful
  body: Functor.Faithful.of_iso (functorIsoDiscrete R)

中文:
实例 :
  签名: (discrete.{u} (模范畴 R)).忠实
  定义体: Functor.Faithful.of_iso (functorIsoDiscrete R)

Depends on / 依赖: Faithful, Functor, Functor.Faithful.of_iso, functorIsoDiscrete, of_iso
-/
instance : (discrete.{u} (ModuleCat R)).Faithful := Functor.Faithful.of_iso (functorIsoDiscrete R)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (constantSheaf (coherentTopology LightProfinite.{u}) (ModuleCat.{u} R)).Faithful
  body: inferInstanceAs (discrete.{u} (ModuleCat R)).Faithful

中文:
实例 :
  签名: (constantSheaf (coherentTopology LightProfinite.{u}) (模范畴.{u} R)).忠实
  定义体: inferInstanceAs (discrete.{u} (ModuleCat R)).Faithful

Depends on / 依赖: Faithful, ModuleCat, discrete
-/
instance : (constantSheaf (coherentTopology LightProfinite.{u}) (ModuleCat.{u} R)).Faithful :=
  inferInstanceAs (discrete.{u} (ModuleCat R)).Faithful

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (discrete (ModuleCat.{u} R)).Full
  body: Functor.Full.of_iso (functorIsoDiscrete R)

中文:
实例 :
  签名: (discrete (模范畴.{u} R)).满
  定义体: Functor.Full.of_iso (functorIsoDiscrete R)

Depends on / 依赖: Functor, Functor.Full.of_iso, functorIsoDiscrete, of_iso
-/
instance : (discrete (ModuleCat.{u} R)).Full :=
  Functor.Full.of_iso (functorIsoDiscrete R)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (constantSheaf (coherentTopology LightProfinite.{u}) (ModuleCat.{u} R)).Full
  body: inferInstanceAs (discrete.{u} (ModuleCat.{u} R)).Full

中文:
实例 :
  签名: (constantSheaf (coherentTopology LightProfinite.{u}) (模范畴.{u} R)).满
  定义体: inferInstanceAs (discrete.{u} (ModuleCat.{u} R)).Full

Depends on / 依赖: Finset, Finset.induction_on, ModuleCat, discrete, induction_on, insert
-/
instance : (constantSheaf (coherentTopology LightProfinite.{u}) (ModuleCat.{u} R)).Full :=
  inferInstanceAs (discrete.{u} (ModuleCat.{u} R)).Full

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (constantSheaf (coherentTopology LightProfinite.{u}) (Type u)).Faithful
  body: inferInstanceAs (discrete (Type u)).Faithful

中文:
实例 :
  签名: (constantSheaf (coherentTopology LightProfinite.{u}) (类型u)).忠实
  定义体: inferInstanceAs (discrete (Type u)).Faithful

Depends on / 依赖: Faithful, discrete
-/
instance : (constantSheaf (coherentTopology LightProfinite.{u}) (Type u)).Faithful :=
  inferInstanceAs (discrete (Type u)).Faithful

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (constantSheaf (coherentTopology LightProfinite.{u}) (Type u)).Full
  body: inferInstanceAs (discrete (Type u)).Full

中文:
实例 :
  签名: (constantSheaf (coherentTopology LightProfinite.{u}) (类型u)).满
  定义体: inferInstanceAs (discrete (Type u)).Full

Depends on / 依赖: discrete
-/
instance : (constantSheaf (coherentTopology LightProfinite.{u}) (Type u)).Full :=
  inferInstanceAs (discrete (Type u)).Full

end LightCondMod.LocallyConstant
