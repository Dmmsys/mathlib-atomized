/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Generator.HomologicalComplex
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# Homological complexes in a Grothendieck abelian category

Let `c : ComplexShape ι` be a complex shape with no loop, and
such that `Small.{w} ι`. Then, if `C` is a Grothendieck abelian
category (with `IsGrothendieckAbelian.{w} C`), the category
`HomologicalComplex C c` is Grothendieck abelian.

-/

public section

universe w w' t v u

open CategoryTheory Limits

namespace HomologicalComplex

variable (C : Type u) [Category.{v} C] {ι : Type t} (c : ComplexShape ι)

section HasZeroMorphisms

variable [HasZeroMorphisms C]

/--
Instance `locallySmall` / 实例 `locallySmall`

English:
instance locallySmall
  signature: [LocallySmall.{w} C] [Small.{w} ι]
  body: by
    let emb (f : K ⟶ L) (i : Shrink.{w} ι) := (equivShrink.{w} _) (f.f ((equivShrink _).symm i))
    have hemb : Function.Injective emb := fun f g h => by
      ext i
      obtain ⟨i, rfl⟩ := (equivShrink.{w} _).symm.surjective i
      simpa [emb] using congr_fun h i
    apply small_of_injective 

中文:
实例 locallySmall
  签名: [LocallySmall.{w} C] [Small.{w} ι]
  定义体: by
    let emb (f : K ⟶ L) (i : Shrink.{w} ι) := (equivShrink.{w} _) (f.f ((equivShrink _).symm i))
    have hemb : Function.Injective emb := fun f g h => by
      ext i
      obtain ⟨i, rfl⟩ := (equivShrink.{w} _).symm.surjective i
      simpa [emb] using congr_fun h i
    apply small_of_injective 

Depends on / 依赖: Function, Function.Injective, Injective, Shrink, congr_fun, equivShrink, small_of_injective, surjective, symm.surjective
-/
instance locallySmall [LocallySmall.{w} C] [Small.{w} ι] :
    LocallySmall.{w} (HomologicalComplex C c) where
  hom_small K L := by
    let emb (f : K ⟶ L) (i : Shrink.{w} ι) := (equivShrink.{w} _) (f.f ((equivShrink _).symm i))
    have hemb : Function.Injective emb := fun f g h => by
      ext i
      obtain ⟨i, rfl⟩ := (equivShrink.{w} _).symm.surjective i
      simpa [emb] using congr_fun h i
    apply small_of_injective hemb

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasFilteredColimitsOfSize.{w,
  signature: w'} C] :
  body: by infer_instance

中文:
实例 [有FilteredColimitsOfSize.{w,
  签名: w'} C] :
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance [HasFilteredColimitsOfSize.{w, w'} C] :
    HasFilteredColimitsOfSize.{w, w'} (HomologicalComplex C c) where
  HasColimitsOfShape J _ _ := by infer_instance

/--
Instance `hasExactColimitsOfShape` / 实例 `hasExactColimitsOfShape`

English:
instance hasExactColimitsOfShape
  signature: (J : Type w) [Category.{w'} J] [HasFiniteLimits C]
  body: ⟨fun K _ _ => ⟨fun {F} => ⟨fun hc => ⟨isLimitOfEval _ _ (fun i => by
      let e := preservesColimitNatIso (J := J) (eval C c i)
      exact (IsLimit.postcomposeHomEquiv (Functor.isoWhiskerLeft F e) _).1
        (IsLimit.ofIsoLimit
          (isLimitOfPreserves ((Functor.whiskeringRight J _ _).obj (

中文:
实例 hasExactColimitsOfShape
  签名: (J : 类型 w) [范畴.{w'} J] [有有限极限 C]
  定义体: ⟨fun K _ _ => ⟨fun {F} => ⟨fun hc => ⟨isLimitOfEval _ _ (fun i => by
      let e := preservesColimitNatIso (J := J) (eval C c i)
      exact (IsLimit.postcomposeHomEquiv (Functor.isoWhiskerLeft F e) _).1
        (IsLimit.ofIsoLimit
          (isLimitOfPreserves ((Functor.whiskeringRight J _ _).obj (

Depends on / 依赖: Cone.ext, Functor, Functor.isoWhiskerLeft, Functor.whiskeringRight, IsLimit, IsLimit.ofIsoLimit, IsLimit.postcomposeHomEquiv, NatIso, NatIso.naturality_2, e.symm, e.symm.app, isLimitOfEval, isLimitOfPreserves, isoWhiskerLeft, naturality_2, ofIsoLimit, postcomposeHomEquiv, preservesColimitNatIso, whiskeringRight
-/
instance hasExactColimitsOfShape (J : Type w) [Category.{w'} J] [HasFiniteLimits C]
    [HasColimitsOfShape J C] [HasExactColimitsOfShape J C] :
    HasExactColimitsOfShape J (HomologicalComplex C c) where
  preservesFiniteLimits :=
    ⟨fun K _ _ => ⟨fun {F} => ⟨fun hc => ⟨isLimitOfEval _ _ (fun i => by
      let e := preservesColimitNatIso (J := J) (eval C c i)
      exact (IsLimit.postcomposeHomEquiv (Functor.isoWhiskerLeft F e) _).1
        (IsLimit.ofIsoLimit
          (isLimitOfPreserves ((Functor.whiskeringRight J _ _).obj (eval C c i) ⋙ colim) hc)
          (Cone.ext (e.symm.app _) (fun k => (NatIso.naturality_2 e.symm _).symm))))⟩⟩⟩⟩

/--
Instance `ab5OfSize` / 实例 `ab5OfSize`

English:
instance ab5OfSize
  signature: [HasFilteredColimitsOfSize.{w', w} C] [HasFiniteLimits C]
  body: by infer_instance

中文:
实例 ab5OfSize
  签名: [有FilteredColimitsOfSize.{w', w} C] [有有限极限 C]
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance ab5OfSize [HasFilteredColimitsOfSize.{w', w} C] [HasFiniteLimits C]
    [AB5OfSize.{w', w} C] :
    AB5OfSize.{w', w} (HomologicalComplex C c) where
  ofShape J _ _ := by infer_instance

end HasZeroMorphisms

/--
Instance `isGrothendieckAbelian` / 实例 `isGrothendieckAbelian`

English:
instance isGrothendieckAbelian
  signature: [Abelian C] [IsGrothendieckAbelian.{w} C]
  body: by
    have : HasCoproductsOfShape ι C :=
      hasColimitsOfShape_of_equivalence (Discrete.equivalence (equivShrink.{w} ι)).symm
    infer_instance

中文:
实例 isGrothendieckAbelian
  签名: [交换 C] [是GrothendieckAbelian.{w} C]
  定义体: by
    have : HasCoproductsOfShape ι C :=
      hasColimitsOfShape_of_equivalence (Discrete.equivalence (equivShrink.{w} ι)).symm
    infer_instance

Depends on / 依赖: Discrete, Discrete.equivalence, HasCoproductsOfShape, equivShrink, equivalence, hasColimitsOfShape_of_equivalence, infer_instance
-/
instance isGrothendieckAbelian [Abelian C] [IsGrothendieckAbelian.{w} C]
    [c.HasNoLoop] [Small.{w} ι] :
    IsGrothendieckAbelian.{w} (HomologicalComplex C c) where
  hasSeparator := by
    have : HasCoproductsOfShape ι C :=
      hasColimitsOfShape_of_equivalence (Discrete.equivalence (equivShrink.{w} ι)).symm
    infer_instance

end HomologicalComplex
