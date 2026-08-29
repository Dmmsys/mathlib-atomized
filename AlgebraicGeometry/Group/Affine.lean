/-
Copyright (c) 2025 Yaël Dillies, Christian Merten, Michał Mrugała, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Christian Merten, Michał Mrugała, Andrew Yang
-/
module

public import Mathlib.Algebra.Category.CommHopfAlgCat
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
public import Mathlib.RingTheory.Bialgebra.TensorProduct

/-!
# The equivalence between Hopf algebras and affine group schemes

This file constructs `Spec` as a functor from `R`-Hopf algebras to group schemes over `Spec R`,
shows it is full and faithful, and has affine group schemes as essential image.

We want to show that affine group schemes correspond to Hopf algebras. This can easily be done
categorically assuming both categories on either side are defined thoughtfully. However, the
categorical version will not be workable with if we do not also have links to the non-categorical
notions. Therefore, one solution would be to build the left, top and right edges of the following
diagram so that the bottom edge can be obtained by composing the three.

```
  Cogrp Mod_R ≌ Grp AffSch_{Spec R} ≌ Aff Grp Sch_{Spec R}
      ↑ ↓ ↑ ↓
R-Hopf algebras ⇄ Affine group schemes over Spec R
```

If we do not care about going back from affine group schemes over `Spec R` to `R`-Hopf algebras
(e.g. because all our affine group schemes are given as the `Spec` of some algebra), then we can
follow the following simpler diagram:

```
  Cogrp Mod_R ⥤ Grp Sch_{Spec R}
      ↑ ↓ ↓
R-Hopf algebras → Affine group schemes over Spec R
```
where the top `⥤` comes from the essentially surjective functor `Cogrp Mod_R ⥤ Grp Sch_{Spec R}`,
so that in particular we do not easily know that its inverse is given by `Γ`.
-/

@[expose] public section

suppress_compilation

open AlgebraicGeometry Coalgebra Scheme CategoryTheory MonoidalCategory CartesianMonoidalCategory
  Functor Monoidal Opposite TensorProduct MonObj GrpObj
open Limits hiding prodComparison

universe w v u
variable {R : CommRingCat.{u}}

/-!
### Left edge: `R`-Hopf algebras correspond to cogroup objects under `R`

Ways to turn an unbundled `R`-Hopf algebra into a bundled cogroup object under `R`, and vice versa,
are already provided in `Mathlib.Algebra.Category.CommHopfAlgCat`.

### Top edge: `Spec` as a functor on Hopf algebras

In this section we bundle `Spec` as a functor from `R`-Hopf algebras to affine group schemes over
`Spec R`.
-/

namespace AlgebraicGeometry

section topEdge

variable (R) in
/--
Definition of `algSpec` / `algSpec` 的定义

English:
definition algSpec
  signature: : (CommAlgCat R)ᵒᵖ ⥤ Over (Spec R)
  body: (commAlgCatEquivUnder R).op.functor ⋙ (Over.opEquivOpUnder R).inverse ⋙ Over.post Scheme.Spec

中文:
定义 algSpec
  签名: : (CommAlgCat R)ᵒᵖ ⥤ Over (Spec R)
  定义体: (commAlgCatEquivUnder R).op.functor ⋙ (Over.opEquivOpUnder R).inverse ⋙ Over.post Scheme.Spec
-/
@[implicit_reducible] def algSpec : (CommAlgCat R)ᵒᵖ ⥤ Over (Spec R) :=
  (commAlgCatEquivUnder R).op.functor ⋙ (Over.opEquivOpUnder R).inverse ⋙ Over.post Scheme.Spec

variable (R) in
/--
Definition of `algΓ` / `algΓ` 的定义

English:
definition algΓ
  signature: : Over (Spec R) ⥤ (CommAlgCat R)ᵒᵖ
  body: Over.post Γ.rightOp ⋙ Over.map (ΓSpecIso R).inv.op ⋙
    (Over.opEquivOpUnder R).functor ⋙ (commAlgCatEquivUnder R).inverse.op

中文:
定义 algΓ
  签名: : Over (Spec R) ⥤ (CommAlgCat R)ᵒᵖ
  定义体: Over.post Γ.rightOp ⋙ Over.map (ΓSpecIso R).inv.op ⋙
    (Over.opEquivOpUnder R).functor ⋙ (commAlgCatEquivUnder R).inverse.op
-/
@[implicit_reducible] def algΓ : Over (Spec R) ⥤ (CommAlgCat R)ᵒᵖ :=
  Over.post Γ.rightOp ⋙ Over.map (ΓSpecIso R).inv.op ⋙
    (Over.opEquivOpUnder R).functor ⋙ (commAlgCatEquivUnder R).inverse.op

/--
Instance `preservesLimitsOfSize_algSpec` / 实例 `preservesLimitsOfSize_algSpec`

English:
instance preservesLimitsOfSize_algSpec
  signature: : PreservesLimitsOfSize.{w, v} (algSpec R)
  body: inferInstanceAs PreservesLimitsOfSize.{w, v}
    (commAlgCatEquivUnder R).op.functor ⋙ (Over.opEquivOpUnder R).inverse ⋙ Over.post Scheme.Spec

中文:
实例 preservesLimitsOfSize_algSpec
  签名: : PreservesLimitsOfSize.{w, v} (algSpec R)
  定义体: inferInstanceAs PreservesLimitsOfSize.{w, v}
    (commAlgCatEquivUnder R).op.functor ⋙ (Over.opEquivOpUnder R).inverse ⋙ Over.post Scheme.Spec

Depends on / 依赖: Over.opEquivOpUnder, Over.post, PreservesLimitsOfSize, Scheme, Scheme.Spec, commAlgCatEquivUnder, functor, inverse, op.functor, opEquivOpUnder
-/
instance preservesLimitsOfSize_algSpec : PreservesLimitsOfSize.{w, v} (algSpec R) :=
inferInstanceAs PreservesLimitsOfSize.{w, v}
    (commAlgCatEquivUnder R).op.functor ⋙ (Over.opEquivOpUnder R).inverse ⋙ Over.post Scheme.Spec

set_option backward.isDefEq.respectTransparency false in
/--
Instance `preservesColimitsOfSize_algΓ` / 实例 `preservesColimitsOfSize_algΓ`

English:
instance preservesColimitsOfSize_algΓ
  signature: : PreservesColimitsOfSize.{w, v} (algΓ R)
  body: by
  unfold algΓ; infer_instance

中文:
实例 preservesColimitsOfSize_algΓ
  签名: : PreservesColimitsOfSize.{w, v} (algΓ R)
  定义体: by
  unfold algΓ; infer_instance

Depends on / 依赖: infer_instance
-/
instance preservesColimitsOfSize_algΓ : PreservesColimitsOfSize.{w, v} (algΓ R) := by
  unfold algΓ; infer_instance

/--
lemma `algSpec_obj_hom` / 引理 `algSpec_obj_hom`

English:
lemma algSpec_obj_hom
  given: (X : (CommAlgCat R)ᵒᵖ)
  proof: rfl

中文:
引理 algSpec_obj_hom
  条件: (X : (CommAlgCat R)ᵒᵖ)
  证明: rfl
-/
@[simp] lemma algSpec_obj_hom (X : (CommAlgCat R)ᵒᵖ) :
    ((algSpec R).obj X).hom = Spec.map (CommRingCat.ofHom (algebraMap R X.unop)) := rfl

/--
lemma `algSpec_map_left` / 引理 `algSpec_map_left`

English:
lemma algSpec_map_left
  given: {X Y : (CommAlgCat R)ᵒᵖ} (f : X ⟶ Y)
  proof: rfl

中文:
引理 algSpec_map_left
  条件: {X Y : (CommAlgCat R)ᵒᵖ} (f : X ⟶ Y)
  证明: rfl
-/
@[simp] lemma algSpec_map_left {X Y : (CommAlgCat R)ᵒᵖ} (f : X ⟶ Y) :
    ((algSpec R).map f).left = Spec.map ((commAlgCatEquivUnder R).functor.map f.unop).right := rfl

/--
lemma `preservesTerminalIso_algSpec` / 引理 `preservesTerminalIso_algSpec`

English:
lemma preservesTerminalIso_algSpec
  proof: by
  ext : 1; exact toUnit_unique ..

中文:
引理 preservesTerminalIso_algSpec
  证明: by
  ext : 1; exact toUnit_unique ..

Depends on / 依赖: toUnit_unique
-/
lemma preservesTerminalIso_algSpec :
    preservesTerminalIso (algSpec R) = Over.isoMk (.refl (Spec R)) := by
  ext : 1; exact toUnit_unique ..

/--
lemma `preservesTerminalIso_algSpec_inv_left` / 引理 `preservesTerminalIso_algSpec_inv_left`

English:
lemma preservesTerminalIso_algSpec_inv_left
  proof: by
  rw [preservesTerminalIso_algSpec]; rfl

@[simp]

中文:
引理 preservesTerminalIso_algSpec_inv_left
  证明: by
  rw [preservesTerminalIso_algSpec]; rfl

@[simp]
-/
@[simp] lemma preservesTerminalIso_algSpec_inv_left :
    (preservesTerminalIso (algSpec R)).inv.left = 𝟙 (Spec R) := by
  rw [preservesTerminalIso_algSpec]; rfl

@[simp]
/--
lemma `prodComparison_algSpec_left` / 引理 `prodComparison_algSpec_left`

English:
lemma prodComparison_algSpec_left
  given: (X Y : (CommAlgCat R)ᵒᵖ)
  proof: rfl

@[simp]

中文:
引理 prodComparison_algSpec_left
  条件: (X Y : (CommAlgCat R)ᵒᵖ)
  证明: rfl

@[simp]
-/
lemma prodComparison_algSpec_left (X Y : (CommAlgCat R)ᵒᵖ) :
    (prodComparison (algSpec R) X Y).left = (pullbackSpecIso R X.unop Y.unop).inv := rfl

@[simp]
/--
lemma `prodComparisonIso_algSpec_inv_left` / 引理 `prodComparisonIso_algSpec_inv_left`

English:
lemma prodComparisonIso_algSpec_inv_left
  given: (X Y : (CommAlgCat R)ᵒᵖ)
  proof: by
  have : (Over.forget (Spec R)).mapIso (prodComparisonIso (algSpec R) X Y) =
      (pullbackSpecIso R X.unop Y.unop).symm :=
    Iso.ext (prodComparison_algSpec_left X Y)
  exact congrArg Iso.inv this

中文:
引理 prodComparisonIso_algSpec_inv_left
  条件: (X Y : (CommAlgCat R)ᵒᵖ)
  证明: by
  have : (Over.forget (Spec R)).mapIso (prodComparisonIso (algSpec R) X Y) =
      (pullbackSpecIso R X.unop Y.unop).symm :=
    Iso.ext (prodComparison_algSpec_left X Y)
  exact congrArg Iso.inv this

Depends on / 依赖: Iso.ext, Iso.inv, Over.forget, X.unop, Y.unop, algSpec, forget, mapIso, prodComparisonIso, prodComparison_algSpec_left, pullbackSpecIso
-/
lemma prodComparisonIso_algSpec_inv_left (X Y : (CommAlgCat R)ᵒᵖ) :
    (prodComparisonIso (algSpec R) X Y).inv.left = (pullbackSpecIso R X.unop Y.unop).hom := by
  have : (Over.forget (Spec R)).mapIso (prodComparisonIso (algSpec R) X Y) =
      (pullbackSpecIso R X.unop Y.unop).symm :=
    Iso.ext (prodComparison_algSpec_left X Y)
  exact congrArg Iso.inv this

attribute [local simp] ε_of_cartesianMonoidalCategory μ_of_cartesianMonoidalCategory in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `braidedAlgSpec` / 实例 `braidedAlgSpec`

English:
instance braidedAlgSpec
  signature: : (algSpec R).Braided
  body: .copy (.ofChosenFiniteProducts _)
    (Over.homMk <| 𝟙 <| Spec R)
    (fun X Y => Over.homMk (pullbackSpecIso R X.unop Y.unop).hom)
    (Over.homMk <| 𝟙 <| Spec R)
    (fun X Y => Over.homMk (pullbackSpecIso R X.unop Y.unop).inv <| by
      simpa using Over.w (prodComparison (algSpec R) X Y))
    (O

中文:
实例 braidedAlgSpec
  签名: : (algSpec R).Braided
  定义体: .copy (.ofChosenFiniteProducts _)
    (Over.homMk <| 𝟙 <| Spec R)
    (fun X Y => Over.homMk (pullbackSpecIso R X.unop Y.unop).hom)
    (Over.homMk <| 𝟙 <| Spec R)
    (fun X Y => Over.homMk (pullbackSpecIso R X.unop Y.unop).inv <| by
      simpa using Over.w (prodComparison (algSpec R) X Y))
    (O

Depends on / 依赖: Functor, Functor.OplaxMonoidal, OplaxMonoidal, Over.OverMorphism.ext, Over.homMk, Over.w, OverMorphism, X.unop, Y.unop, algSpec, ofChosenFiniteProducts, preservesTerminalIso_hom, prodComparison, pullbackSpecIso
-/
instance braidedAlgSpec : (algSpec R).Braided :=
  .copy (.ofChosenFiniteProducts _)
    (Over.homMk <| 𝟙 <| Spec R)
    (fun X Y => Over.homMk (pullbackSpecIso R X.unop Y.unop).hom)
    (Over.homMk <| 𝟙 <| Spec R)
    (fun X Y => Over.homMk (pullbackSpecIso R X.unop Y.unop).inv <| by
      simpa using Over.w (prodComparison (algSpec R) X Y))
    (Over.OverMorphism.ext (by simp))
    (funext fun X => funext fun Y => Over.OverMorphism.ext (by simp))
    (Over.OverMorphism.ext (by
      rw [Functor.OplaxMonoidal.η_of_cartesianMonoidalCategory]; rw [← preservesTerminalIso_hom]; rw [preservesTerminalIso_algSpec]; rfl))
    (funext fun X => funext fun Y => Over.OverMorphism.ext (by
      rw [Functor.OplaxMonoidal.δ_of_cartesianMonoidalCategory]; rw [prodComparison_algSpec_left]; rfl))

/--
lemma `ε_algSpec_left` / 引理 `ε_algSpec_left`

English:
lemma ε_algSpec_left
  statement: (LaxMonoidal.ε (algSpec R)).left = 𝟙 (Spec R)
  proof: rfl

中文:
引理 ε_algSpec_left
  结论: (LaxMonoidal.ε (algSpec R)).left = 𝟙 (Spec R)
  证明: rfl
-/
@[simp] lemma ε_algSpec_left : (LaxMonoidal.ε (algSpec R)).left = 𝟙 (Spec R) := rfl
/--
lemma `η_algSpec_left` / 引理 `η_algSpec_left`

English:
lemma η_algSpec_left
  statement: (OplaxMonoidal.η (algSpec R)).left = 𝟙 (Spec R)
  proof: rfl

中文:
引理 η_algSpec_left
  结论: (OplaxMonoidal.η (algSpec R)).left = 𝟙 (Spec R)
  证明: rfl
-/
@[simp] lemma η_algSpec_left : (OplaxMonoidal.η (algSpec R)).left = 𝟙 (Spec R) := rfl

/--
lemma `δ_algSpec_left` / 引理 `δ_algSpec_left`

English:
lemma δ_algSpec_left
  given: (X Y : (CommAlgCat R)ᵒᵖ)
  proof: rfl

中文:
引理 δ_algSpec_left
  条件: (X Y : (CommAlgCat R)ᵒᵖ)
  证明: rfl
-/
@[simp] lemma δ_algSpec_left (X Y : (CommAlgCat R)ᵒᵖ) :
    (OplaxMonoidal.δ (algSpec R) X Y).left = (pullbackSpecIso R X.unop Y.unop).inv := rfl

/--
lemma `μ_algSpec_left` / 引理 `μ_algSpec_left`

English:
lemma μ_algSpec_left
  given: (X Y : (CommAlgCat R)ᵒᵖ)
  proof: rfl

中文:
引理 μ_algSpec_left
  条件: (X Y : (CommAlgCat R)ᵒᵖ)
  证明: rfl
-/
@[simp] lemma μ_algSpec_left (X Y : (CommAlgCat R)ᵒᵖ) :
    (LaxMonoidal.μ (algSpec R) X Y).left = (pullbackSpecIso R X.unop Y.unop).hom := rfl

/--
Instance `algSpec.instFull` / 实例 `algSpec.instFull`

English:
instance algSpec.instFull
  signature: : (algSpec R).Full
  body: inferInstanceAs Functor.Full
    (commAlgCatEquivUnder R).op.functor ⋙ (Over.opEquivOpUnder R).inverse ⋙ Over.post Scheme.Spec

中文:
实例 algSpec.instFull
  签名: : (algSpec R).Full
  定义体: inferInstanceAs Functor.Full
    (commAlgCatEquivUnder R).op.functor ⋙ (Over.opEquivOpUnder R).inverse ⋙ Over.post Scheme.Spec

Depends on / 依赖: Functor, Functor.Full, Over.opEquivOpUnder, Over.post, Scheme, Scheme.Spec, commAlgCatEquivUnder, functor, inverse, op.functor, opEquivOpUnder
-/
instance algSpec.instFull : (algSpec R).Full :=
inferInstanceAs Functor.Full
    (commAlgCatEquivUnder R).op.functor ⋙ (Over.opEquivOpUnder R).inverse ⋙ Over.post Scheme.Spec

/--
Instance `algSpec.instFaithful` / 实例 `algSpec.instFaithful`

English:
instance algSpec.instFaithful
  signature: : (algSpec R).Faithful
  body: inferInstanceAs Functor.Faithful
    (commAlgCatEquivUnder R).op.functor ⋙ (Over.opEquivOpUnder R).inverse ⋙ Over.post Scheme.Spec

中文:
实例 algSpec.instFaithful
  签名: : (algSpec R).Faithful
  定义体: inferInstanceAs Functor.Faithful
    (commAlgCatEquivUnder R).op.functor ⋙ (Over.opEquivOpUnder R).inverse ⋙ Over.post Scheme.Spec

Depends on / 依赖: Faithful, Functor, Functor.Faithful, Over.opEquivOpUnder, Over.post, Scheme, Scheme.Spec, commAlgCatEquivUnder, functor, inverse, op.functor, opEquivOpUnder
-/
instance algSpec.instFaithful : (algSpec R).Faithful :=
inferInstanceAs Functor.Faithful
    (commAlgCatEquivUnder R).op.functor ⋙ (Over.opEquivOpUnder R).inverse ⋙ Over.post Scheme.Spec

/--
Definition of `algSpec.fullyFaithful` / `algSpec.fullyFaithful` 的定义

English:
definition algSpec.fullyFaithful
  signature: : (algSpec R).FullyFaithful
  body: ((commAlgCatEquivUnder R).op.trans (Over.opEquivOpUnder R).symm).fullyFaithfulFunctor.comp
    Spec.fullyFaithful.over _

中文:
定义 algSpec.fullyFaithful
  签名: : (algSpec R).FullyFaithful
  定义体: ((commAlgCatEquivUnder R).op.trans (Over.opEquivOpUnder R).symm).fullyFaithfulFunctor.comp
    Spec.fullyFaithful.over _

Depends on / 依赖: Over.opEquivOpUnder, Spec.fullyFaithful.over, commAlgCatEquivUnder, fullyFaithful, fullyFaithfulFunctor, fullyFaithfulFunctor.comp, op.trans, opEquivOpUnder
-/
def algSpec.fullyFaithful : (algSpec R).FullyFaithful :=
((commAlgCatEquivUnder R).op.trans (Over.opEquivOpUnder R).symm).fullyFaithfulFunctor.comp
    Spec.fullyFaithful.over _

variable (R) in
/--
Definition of `bialgSpec` / `bialgSpec` 的定义

English:
abbreviation bialgSpec
  signature: : (CommBialgCat R)ᵒᵖ ⥤ Mon (Over <| Spec R)
  body: (commBialgCatEquivComonCommAlgCat R).functor.leftOp ⋙ (algSpec R).mapMon

中文:
缩写 bialgSpec
  签名: : (CommBialgCat R)ᵒᵖ ⥤ Mon (Over <| Spec R)
  定义体: (commBialgCatEquivComonCommAlgCat R).functor.leftOp ⋙ (algSpec R).mapMon

Depends on / 依赖: algSpec, commBialgCatEquivComonCommAlgCat, functor, functor.leftOp, leftOp, mapMon
-/
abbrev bialgSpec : (CommBialgCat R)ᵒᵖ ⥤ Mon (Over <| Spec R) :=
  (commBialgCatEquivComonCommAlgCat R).functor.leftOp ⋙ (algSpec R).mapMon

/--
Instance `bialgSpec.instFull` / 实例 `bialgSpec.instFull`

English:
instance bialgSpec.instFull
  signature: : (bialgSpec R).Full
  body: inferInstance

中文:
实例 bialgSpec.instFull
  签名: : (bialgSpec R).Full
  定义体: inferInstance
-/
instance bialgSpec.instFull : (bialgSpec R).Full := inferInstance

/--
Instance `bialgSpec.instFaithful` / 实例 `bialgSpec.instFaithful`

English:
instance bialgSpec.instFaithful
  signature: : (bialgSpec R).Faithful
  body: inferInstance

中文:
实例 bialgSpec.instFaithful
  签名: : (bialgSpec R).Faithful
  定义体: inferInstance
-/
instance bialgSpec.instFaithful : (bialgSpec R).Faithful := inferInstance

/--
Definition of `bialgSpec.fullyFaithful` / `bialgSpec.fullyFaithful` 的定义

English:
definition bialgSpec.fullyFaithful
  signature: : (bialgSpec R).FullyFaithful
  body: (commBialgCatEquivComonCommAlgCat R).fullyFaithfulFunctor.leftOp.comp algSpec.fullyFaithful.mapMon

中文:
定义 bialgSpec.fullyFaithful
  签名: : (bialgSpec R).FullyFaithful
  定义体: (commBialgCatEquivComonCommAlgCat R).fullyFaithfulFunctor.leftOp.comp algSpec.fullyFaithful.mapMon

Depends on / 依赖: algSpec, algSpec.fullyFaithful.mapMon, commBialgCatEquivComonCommAlgCat, fullyFaithful, fullyFaithfulFunctor, fullyFaithfulFunctor.leftOp.comp, leftOp, mapMon
-/
def bialgSpec.fullyFaithful : (bialgSpec R).FullyFaithful :=
  (commBialgCatEquivComonCommAlgCat R).fullyFaithfulFunctor.leftOp.comp algSpec.fullyFaithful.mapMon

variable (R) in
/--
Definition of `hopfSpec` / `hopfSpec` 的定义

English:
abbreviation hopfSpec
  signature: : (CommHopfAlgCat R)ᵒᵖ ⥤ Grp (Over <| Spec R)
  body: (commHopfAlgCatEquivCogrpCommAlgCat R).functor.leftOp ⋙ (algSpec R).mapGrp

中文:
缩写 hopfSpec
  签名: : (CommHopfAlgCat R)ᵒᵖ ⥤ Grp (Over <| Spec R)
  定义体: (commHopfAlgCatEquivCogrpCommAlgCat R).functor.leftOp ⋙ (algSpec R).mapGrp

Depends on / 依赖: algSpec, commHopfAlgCatEquivCogrpCommAlgCat, functor, functor.leftOp, leftOp, mapGrp
-/
abbrev hopfSpec : (CommHopfAlgCat R)ᵒᵖ ⥤ Grp (Over <| Spec R) :=
  (commHopfAlgCatEquivCogrpCommAlgCat R).functor.leftOp ⋙ (algSpec R).mapGrp

/--
Instance `hopfSpec.instFull` / 实例 `hopfSpec.instFull`

English:
instance hopfSpec.instFull
  signature: : (hopfSpec R).Full
  body: inferInstance

中文:
实例 hopfSpec.instFull
  签名: : (hopfSpec R).Full
  定义体: inferInstance
-/
instance hopfSpec.instFull : (hopfSpec R).Full := inferInstance

/--
Instance `hopfSpec.instFaithful` / 实例 `hopfSpec.instFaithful`

English:
instance hopfSpec.instFaithful
  signature: : (hopfSpec R).Faithful
  body: inferInstance

中文:
实例 hopfSpec.instFaithful
  签名: : (hopfSpec R).Faithful
  定义体: inferInstance
-/
instance hopfSpec.instFaithful : (hopfSpec R).Faithful := inferInstance

/--
Definition of `hopfSpec.fullyFaithful` / `hopfSpec.fullyFaithful` 的定义

English:
definition hopfSpec.fullyFaithful
  signature: : (hopfSpec R).FullyFaithful
  body: (commHopfAlgCatEquivCogrpCommAlgCat R).fullyFaithfulFunctor.leftOp.comp
    algSpec.fullyFaithful.mapGrp

中文:
定义 hopfSpec.fullyFaithful
  签名: : (hopfSpec R).FullyFaithful
  定义体: (commHopfAlgCatEquivCogrpCommAlgCat R).fullyFaithfulFunctor.leftOp.comp
    algSpec.fullyFaithful.mapGrp

Depends on / 依赖: algSpec, algSpec.fullyFaithful.mapGrp, commHopfAlgCatEquivCogrpCommAlgCat, fullyFaithful, fullyFaithfulFunctor, fullyFaithfulFunctor.leftOp.comp, leftOp, mapGrp
-/
def hopfSpec.fullyFaithful : (hopfSpec R).FullyFaithful :=
  (commHopfAlgCatEquivCogrpCommAlgCat R).fullyFaithfulFunctor.leftOp.comp
    algSpec.fullyFaithful.mapGrp

section universe_polymorphic
variable {R A : CommRingCat.{u}}

-- Note that this creates a diamond with `instOverClass`. We keep it for convenience.
-- Once `OverClass` is refactored (see https://github.com/leanprover-community/mathlib4/pull/41542),
-- the diamond will be downgraded to the invariant about the `outParam` argument of `OverClass`
-- being determined by the first two arguments being broken.
@[simps -isSimp]
/--
Instance `specOverSpec` / 实例 `specOverSpec`

English:
instance specOverSpec
  signature: [Algebra R A]
  body: Spec.map CommRingCat.ofHom algebraMap ..

中文:
实例 specOverSpec
  签名: [Algebra R A]
  定义体: Spec.map CommRingCat.ofHom algebraMap ..

Depends on / 依赖: CommRingCat, CommRingCat.ofHom, Spec.map, algebraMap
-/
instance specOverSpec [Algebra R A] : (Spec A).Over (Spec R) where
hom := Spec.map CommRingCat.ofHom algebraMap ..

/--
Instance `locallyOfFiniteType_specOverSpec` / 实例 `locallyOfFiniteType_specOverSpec`

English:
instance locallyOfFiniteType_specOverSpec
  signature: [Algebra R A] [Algebra.FiniteType R A]
  body: by
  rw [specOverSpec_over]; rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  simpa [RingHom.finiteType_algebraMap]

中文:
实例 locallyOfFiniteType_specOverSpec
  签名: [Algebra R A] [Algebra.FiniteType R A]
  定义体: by
  rw [specOverSpec_over]; rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  simpa [RingHom.finiteType_algebraMap]

Depends on / 依赖: HasRingHomProperty, HasRingHomProperty.Spec_iff, LocallyOfFiniteType, RingHom, RingHom.finiteType_algebraMap, Spec_iff, finiteType_algebraMap, specOverSpec_over
-/
instance locallyOfFiniteType_specOverSpec [Algebra R A] [Algebra.FiniteType R A] :
    LocallyOfFiniteType (Spec A ↘ Spec R) := by
  rw [specOverSpec_over]; rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  simpa [RingHom.finiteType_algebraMap]

attribute [local simp] AlgHom.toUnder in
@[simps! one]
/--
Instance `instMonObjSpecAsOverSpec` / 实例 `instMonObjSpecAsOverSpec`

English:
instance instMonObjSpecAsOverSpec
  signature: [Bialgebra R A]
  body: ((bialgSpec R).obj <| .op <| .of R A).mon

中文:
实例 instMonObjSpecAsOverSpec
  签名: [Bialgebra R A]
  定义体: ((bialgSpec R).obj <| .op <| .of R A).mon

Depends on / 依赖: bialgSpec
-/
instance instMonObjSpecAsOverSpec [Bialgebra R A] : MonObj ((Spec A).asOver (Spec R)) :=
  ((bialgSpec R).obj <| .op <| .of R A).mon

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `one_spec_asOver_spec` / 引理 `one_spec_asOver_spec`

English:
lemma one_spec_asOver_spec
  given: [Bialgebra R A]
  proof: rfl

中文:
引理 one_spec_asOver_spec
  条件: [Bialgebra R A]
  证明: rfl

Depends on / 依赖: asOver
-/
lemma one_spec_asOver_spec [Bialgebra R A] :
    η[(Spec A).asOver (Spec R)] = LaxMonoidal.ε (algSpec R) ≫
      Over.homMk (V := (Spec A).asOver (Spec R))
        (Spec.map <| CommRingCat.ofHom <| Bialgebra.counitAlgHom R A)
          (by simp [specOverSpec_over, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
            CommRingCat.of_carrier]) := rfl

/--
lemma `one_spec_asOver_spec_left` / 引理 `one_spec_asOver_spec_left`

English:
lemma one_spec_asOver_spec_left
  given: [Bialgebra R A]
  proof: rfl

中文:
引理 one_spec_asOver_spec_left
  条件: [Bialgebra R A]
  证明: rfl
-/
lemma one_spec_asOver_spec_left [Bialgebra R A] :
    η[(Spec A).asOver (Spec R)].left =
      (Spec.map <| CommRingCat.ofHom <| Bialgebra.counitAlgHom R A) := rfl

/--
lemma `mul_spec_asOver_spec_left` / 引理 `mul_spec_asOver_spec_left`

English:
lemma mul_spec_asOver_spec_left
  given: [Bialgebra R A]
  proof: rfl

中文:
引理 mul_spec_asOver_spec_left
  条件: [Bialgebra R A]
  证明: rfl
-/
lemma mul_spec_asOver_spec_left [Bialgebra R A] :
    μ[(Spec A).asOver (Spec R)].left =
      (pullbackSpecIso R A A).hom ≫ Spec.map (CommRingCat.ofHom (Bialgebra.comulAlgHom R A)) := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `isCommMonObj_spec_asOver_spec` / 实例 `isCommMonObj_spec_asOver_spec`

English:
instance isCommMonObj_spec_asOver_spec
  signature: [Bialgebra R A] [IsCocomm R A]
  body: by
    ext
    have := congr((pullbackSpecIso R A A).hom ≫ ((bialgSpec R).map <| .op <| CommBialgCat.ofHom <|
 (Bialgebra.comm_comp_comulBialgHom (R := R) (A := A))).hom.left)
    dsimp [commBialgCatEquivComonCommAlgCat] at this ⊢
    have h₁ : (Algebra.TensorProduct.includeRight : A ->ₐ[R] A otimes

中文:
实例 isCommMonObj_spec_asOver_spec
  签名: [Bialgebra R A] [IsCocomm R A]
  定义体: by
    ext
    have := congr((pullbackSpecIso R A A).hom ≫ ((bialgSpec R).map <| .op <| CommBialgCat.ofHom <|
 (Bialgebra.comm_comp_comulBialgHom (R := R) (A := A))).hom.left)
    dsimp [commBialgCatEquivComonCommAlgCat] at this ⊢
    have h₁ : (Algebra.TensorProduct.includeRight : A ->ₐ[R] A otimes

Depends on / 依赖: Algebra, Algebra.TensorProduct.includeLeftRingHom, Algebra.TensorProduct.includeRight, Bialgebra, Bialgebra.Ten, Bialgebra.TensorProduct.comm, Bialgebra.comm_comp_comulBialgHom, CommBialgCat, CommBialgCat.ofHom, RingHomClass, RingHomClass.toRingHom, TensorProduct, bialgSpec, commBialgCatEquivComonCommAlgCat, comm_comp_comulBialgHom, hom.left, includeLeftRingHom, includeRight, otimes, pullbackSpecIso
-/
instance isCommMonObj_spec_asOver_spec [Bialgebra R A] [IsCocomm R A] :
    IsCommMonObj ((Spec A).asOver (Spec R)) where
  mul_comm := by
    ext
    have := congr((pullbackSpecIso R A A).hom ≫ ((bialgSpec R).map <| .op <| CommBialgCat.ofHom <|
 (Bialgebra.comm_comp_comulBialgHom (R := R) (A := A))).hom.left)
    dsimp [commBialgCatEquivComonCommAlgCat] at this ⊢
    have h₁ : (Algebra.TensorProduct.includeRight : A ->ₐ[R] A otimes[R] A) =
      (RingHomClass.toRingHom (Bialgebra.TensorProduct.comm R A A)).comp
        Algebra.TensorProduct.includeLeftRingHom := rfl
    have h₂ : (Algebra.TensorProduct.includeLeftRingHom) =
      (RingHomClass.toRingHom (Bialgebra.TensorProduct.comm R A A)).comp
       (Algebra.TensorProduct.includeRight : A ->ₐ[R] A otimes[R] A) := rfl
    convert! this using 1
    simp only [mul_spec_asOver_spec_left, ← Category.assoc, algSpec, Equivalence.op_functor,
      comp_obj, op_obj, commAlgCatEquivUnder_functor_obj, Over.opEquivOpUnder_inverse_obj,
      CommRingCat.mkUnder_hom, Over.post_obj, Spec_obj, Over.mk_left, Over.mk_hom, Spec_map,
      Quiver.Hom.unop_op, Spec.map_comp]
    congr 1
    rw [← Iso.eq_comp_inv]; rw [Category.assoc]; rw [← Iso.inv_comp_eq]
    ext
    · simp [AlgHom.toUnder, specOverSpec, over, OverClass.hom, h₁]; rfl
    · simp [AlgHom.toUnder, specOverSpec, over, OverClass.hom, h₂]; rfl

/--
Instance `instGrpObjSpecAsOverSpec` / 实例 `instGrpObjSpecAsOverSpec`

English:
instance instGrpObjSpecAsOverSpec
  signature: [HopfAlgebra R A]
  body: instMonObjSpecAsOverSpec
  __ := ((hopfSpec R).obj <| .op <| .of R A).grp

中文:
实例 instGrpObjSpecAsOverSpec
  签名: [HopfAlgebra R A]
  定义体: instMonObjSpecAsOverSpec
  __ := ((hopfSpec R).obj <| .op <| .of R A).grp

Depends on / 依赖: instMonObjSpecAsOverSpec
-/
instance instGrpObjSpecAsOverSpec [HopfAlgebra R A] : GrpObj ((Spec A).asOver (Spec R)) where
  __ := instMonObjSpecAsOverSpec
  __ := ((hopfSpec R).obj <| .op <| .of R A).grp

/--
Instance `instCommGrpObjSpecAsOverSpec` / 实例 `instCommGrpObjSpecAsOverSpec`

English:
instance instCommGrpObjSpecAsOverSpec
  signature: [HopfAlgebra R A] [IsCocomm R A]

中文:
实例 instCommGrpObjSpecAsOverSpec
  签名: [HopfAlgebra R A] [IsCocomm R A]
-/
instance instCommGrpObjSpecAsOverSpec [HopfAlgebra R A] [IsCocomm R A] :
    CommGrpObj ((Spec A).asOver (Spec R)) where

instance {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (f : S ->ₐ[R] T) : (Spec.map (CommRingCat.ofHom f.toRingHom)).IsOver (Spec (.of R)) where
  comp_over := by simp [specOverSpec_over, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `Spec.mapMulEquiv` / `Spec.mapMulEquiv` 的定义

English:
definition Spec.mapMulEquiv
  signature: {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] [Bialgebra R S]
  body: (Spec.map (CommRingCat.ofHom f.ofConv.toRingHom)).asOver _
  invFun f := ⟨(Spec.preimage f.left).hom, by
    suffices CommRingCat.ofHom (algebraMap R S) ≫ Spec.preimage f.left =
      CommRingCat.ofHom (algebraMap R T) from fun r => congr($this r)
    apply Spec.map_injective
    simpa [-comp_over] 

中文:
定义 Spec.mapMulEquiv
  签名: {R S T : 类型u} [CommRing R] [CommRing S] [CommRing T] [Bialgebra R S]
  定义体: (Spec.map (CommRingCat.ofHom f.ofConv.toRingHom)).asOver _
  invFun f := ⟨(Spec.preimage f.left).hom, by
    suffices CommRingCat.ofHom (algebraMap R S) ≫ Spec.preimage f.left =
      CommRingCat.ofHom (algebraMap R T) from fun r => congr($this r)
    apply Spec.map_injective
    simpa [-comp_over] 

Depends on / 依赖: CommRingCat, CommRingCat.ofHom, Spec.map, asOver, f.ofConv.toRingHom, ofConv, toRingHom
-/
def Spec.mapMulEquiv {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] [Bialgebra R S]
    [Algebra R T] :
    WithConv (S ->ₐ[R] T) ≃*
      ((Spec (.of T)).asOver (Spec (.of R)) ⟶ (Spec (.of S)).asOver (Spec (.of R))) where
  toFun f := (Spec.map (CommRingCat.ofHom f.ofConv.toRingHom)).asOver _
  invFun f := ⟨(Spec.preimage f.left).hom, by
    suffices CommRingCat.ofHom (algebraMap R S) ≫ Spec.preimage f.left =
      CommRingCat.ofHom (algebraMap R T) from fun r => congr($this r)
    apply Spec.map_injective
    simpa [-comp_over] using! f.w⟩
  left_inv f := by
    apply WithConv.ofConv_injective
    apply AlgHom.coe_ringHom_injective
    simp
  right_inv f := by ext1; simp
  map_mul' f g := by
    ext1
    dsimp [AlgHom.convMul_def, AlgHom.comp_toRingHom, Hom.mul_def]
    simp only [← Category.assoc, Spec.map_comp, mul_spec_asOver_spec_left]
    congr 1
    rw [← Iso.comp_inv_eq]
    ext
    all_goals
    · simp only [specOverSpec_over, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← AlgHom.comp_toRingHom, Category.assoc, pullbackSpecIso_inv_fst, pullbackSpecIso_inv_snd,
      limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app]
      congr 3
      ext; simp

/--
Definition of `algΓAlgSpecAdjunction` / `algΓAlgSpecAdjunction` 的定义

English:
definition algΓAlgSpecAdjunction
  signature: (R : CommRingCat.{u})
  body: by
  have overAdjunction := Over.postAdjunctionRight (Y := .op <| R) ΓSpec.adjunction
  have overEquivAlg := ((Over.opEquivOpUnder R).trans (commAlgCatEquivUnder R).op.symm).toAdjunction
  simpa using! overAdjunction.comp overEquivAlg

中文:
定义 algΓAlgSpecAdjunction
  签名: (R : CommRingCat.{u})
  定义体: by
  have overAdjunction := Over.postAdjunctionRight (Y := .op <| R) ΓSpec.adjunction
  have overEquivAlg := ((Over.opEquivOpUnder R).trans (commAlgCatEquivUnder R).op.symm).toAdjunction
  simpa using! overAdjunction.comp overEquivAlg

Depends on / 依赖: Over.opEquivOpUnder, Over.postAdjunctionRight, Spec.adjunction, adjunction, commAlgCatEquivUnder, op.symm, opEquivOpUnder, overAdjunction, overAdjunction.comp, overEquivAlg, postAdjunctionRight, toAdjunction
-/
def algΓAlgSpecAdjunction (R : CommRingCat.{u}) : algΓ R ⊣ algSpec R := by
  have overAdjunction := Over.postAdjunctionRight (Y := .op <| R) ΓSpec.adjunction
  have overEquivAlg := ((Over.opEquivOpUnder R).trans (commAlgCatEquivUnder R).op.symm).toAdjunction
  simpa using! overAdjunction.comp overEquivAlg

end universe_polymorphic

section universe_monomorphic
variable {R A : CommRingCat.{u}} {X M G : Scheme.{u}}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [X.Over
  signature: (Spec R)] [IsAffine X] : Algebra R Γ(X, ⊤)
  body: ((commAlgCatEquivUnder R).inverse.obj <|
    .mk (Spec.fullyFaithful.preimage <| X.isoSpec.inv ≫ X ↘ Spec R).unop).algebra

中文:
实例 [X.Over
  签名: (Spec R)] [IsAffine X] : Algebra R Γ(X, ⊤)
  定义体: ((commAlgCatEquivUnder R).inverse.obj <|
    .mk (Spec.fullyFaithful.preimage <| X.isoSpec.inv ≫ X ↘ Spec R).unop).algebra

Depends on / 依赖: Spec.fullyFaithful.preimage, X.isoSpec.inv, algebra, commAlgCatEquivUnder, fullyFaithful, inverse, inverse.obj, isoSpec, preimage
-/
instance [X.Over (Spec R)] [IsAffine X] : Algebra R Γ(X, ⊤) :=
  ((commAlgCatEquivUnder R).inverse.obj <|
    .mk (Spec.fullyFaithful.preimage <| X.isoSpec.inv ≫ X ↘ Spec R).unop).algebra

/--
lemma `algebraMap_presheafObj` / 引理 `algebraMap_presheafObj`

English:
lemma algebraMap_presheafObj
  given: [X.Over (Spec R)] [IsAffine X]
  proof: rfl

中文:
引理 algebraMap_presheafObj
  条件: [X.Over (Spec R)] [IsAffine X]
  证明: rfl
-/
lemma algebraMap_presheafObj [X.Over (Spec R)] [IsAffine X] :
    algebraMap R Γ(X, ⊤) = (Spec.fullyFaithful.preimage <| X.isoSpec.inv ≫ X ↘ Spec R).unop.hom :=
  rfl

attribute [local simp] specOverSpec_over algebraMap_presheafObj in
attribute [-simp] Hom.isOver_iff in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [X.Over
  signature: (Spec R)] [IsAffine X] : X.toSpecΓ.IsOver (Spec R) where

中文:
实例 [X.Over
  签名: (Spec R)] [IsAffine X] : X.toSpecΓ.IsOver (Spec R) where
-/
instance [X.Over (Spec R)] [IsAffine X] : X.toSpecΓ.IsOver (Spec R) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [X.Over
  signature: (Spec R)] [IsAffine X] : X.isoSpec.hom.IsOver (Spec R)
  body: inferInstanceAs (X.toSpecΓ.IsOver (Spec R))

中文:
实例 [X.Over
  签名: (Spec R)] [IsAffine X] : X.isoSpec.hom.IsOver (Spec R)
  定义体: inferInstanceAs (X.toSpecΓ.IsOver (Spec R))

Depends on / 依赖: IsOver, X.toSpec
-/
instance [X.Over (Spec R)] [IsAffine X] : X.isoSpec.hom.IsOver (Spec R) :=
  inferInstanceAs (X.toSpecΓ.IsOver (Spec R))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [M.Over
  signature: (Spec R)] [MonObj (M.asOver (Spec R))] [IsAffine M] :
  body: by
  have : MonObj ((algSpec R).obj <| .op <| CommAlgCat.of R Γ(M, ⊤)) :=
.ofIso M.isoSpec.asOver (Spec R)
  have : MonObj (op <| CommAlgCat.of R Γ(M, ⊤)) := algSpec.fullyFaithful.monObj _
  exact ((commBialgCatEquivComonCommAlgCat R).inverse.obj <|
.op .mk .op .of R Γ(M, ⊤)).bialgebra

中文:
实例 [M.Over
  签名: (Spec R)] [MonObj (M.asOver (Spec R))] [IsAffine M] :
  定义体: by
  have : MonObj ((algSpec R).obj <| .op <| CommAlgCat.of R Γ(M, ⊤)) :=
.ofIso M.isoSpec.asOver (Spec R)
  have : MonObj (op <| CommAlgCat.of R Γ(M, ⊤)) := algSpec.fullyFaithful.monObj _
  exact ((commBialgCatEquivComonCommAlgCat R).inverse.obj <|
.op .mk .op .of R Γ(M, ⊤)).bialgebra

Depends on / 依赖: CommAlgCat, CommAlgCat.of, M.isoSpec.asOver, MonObj, algSpec, algSpec.fullyFaithful.monObj, asOver, bialgebra, commBialgCatEquivComonCommAlgCat, fullyFaithful, inverse, inverse.obj, isoSpec, monObj
-/
instance [M.Over (Spec R)] [MonObj (M.asOver (Spec R))] [IsAffine M] :
    Bialgebra R Γ(M, ⊤) := by
  have : MonObj ((algSpec R).obj <| .op <| CommAlgCat.of R Γ(M, ⊤)) :=
.ofIso M.isoSpec.asOver (Spec R)
  have : MonObj (op <| CommAlgCat.of R Γ(M, ⊤)) := algSpec.fullyFaithful.monObj _
  exact ((commBialgCatEquivComonCommAlgCat R).inverse.obj <|
.op .mk .op .of R Γ(M, ⊤)).bialgebra

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [G.Over
  signature: (Spec R)] [GrpObj (G.asOver (Spec R))] [IsAffine G] :
  body: by
  have : GrpObj ((algSpec R).obj <| .op <| CommAlgCat.of R Γ(G, ⊤)) :=
.ofIso G.isoSpec.asOver (Spec R)
  have : GrpObj (op <| CommAlgCat.of R Γ(G, ⊤)) := algSpec.fullyFaithful.grpObj _
  exact ((commHopfAlgCatEquivCogrpCommAlgCat R).inverse.obj <|
.op .mk .op .of R Γ(G, ⊤)).hopfAlgebra

中文:
实例 [G.Over
  签名: (Spec R)] [GrpObj (G.asOver (Spec R))] [IsAffine G] :
  定义体: by
  have : GrpObj ((algSpec R).obj <| .op <| CommAlgCat.of R Γ(G, ⊤)) :=
.ofIso G.isoSpec.asOver (Spec R)
  have : GrpObj (op <| CommAlgCat.of R Γ(G, ⊤)) := algSpec.fullyFaithful.grpObj _
  exact ((commHopfAlgCatEquivCogrpCommAlgCat R).inverse.obj <|
.op .mk .op .of R Γ(G, ⊤)).hopfAlgebra

Depends on / 依赖: CommAlgCat, CommAlgCat.of, G.isoSpec.asOver, GrpObj, algSpec, algSpec.fullyFaithful.grpObj, asOver, commHopfAlgCatEquivCogrpCommAlgCat, fullyFaithful, grpObj, hopfAlgebra, inverse, inverse.obj, isoSpec
-/
instance [G.Over (Spec R)] [GrpObj (G.asOver (Spec R))] [IsAffine G] :
    HopfAlgebra R Γ(G, ⊤) := by
  have : GrpObj ((algSpec R).obj <| .op <| CommAlgCat.of R Γ(G, ⊤)) :=
.ofIso G.isoSpec.asOver (Spec R)
  have : GrpObj (op <| CommAlgCat.of R Γ(G, ⊤)) := algSpec.fullyFaithful.grpObj _
  exact ((commHopfAlgCatEquivCogrpCommAlgCat R).inverse.obj <|
.op .mk .op .of R Γ(G, ⊤)).hopfAlgebra

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] [Algebra R S]

open TensorProduct Algebra.TensorProduct CommRingCat RingHomClass

variable (R S T) in
/--
Definition of `pullbackSpecIso'` / `pullbackSpecIso'` 的定义

English:
definition pullbackSpecIso'
  signature: [Algebra R T]
  body: pullbackSpecIso ..

中文:
定义 pullbackSpecIso'
  签名: [Algebra R T]
  定义体: pullbackSpecIso ..

Depends on / 依赖: pullbackSpecIso
-/
def pullbackSpecIso' [Algebra R T] :
    pullback (Spec (.of S) ↘ Spec (.of R)) (Spec (.of T) ↘ Spec (.of R)) ≅
      Spec (.of <| S otimes[R] T) := pullbackSpecIso ..

set_option backward.defeqAttrib.useBackward true in
/--
lemma `pullbackSpecIso'_symmetry` / 引理 `pullbackSpecIso'_symmetry`

English:
lemma pullbackSpecIso'_symmetry
  given: [Algebra R T]
  proof: by
  simp_rw [Iso.trans_hom, ← Iso.eq_comp_inv, Category.assoc, ← Iso.inv_comp_eq]
  ext
  · have : (RingHomClass.toRingHom (Algebra.TensorProduct.comm R S T)).comp
      Algebra.TensorProduct.includeLeftRingHom =
      RingHomClass.toRingHom Algebra.TensorProduct.includeRight := rfl
    rw [Categor

中文:
引理 pullbackSpecIso'_symmetry
  条件: [Algebra R T]
  证明: by
  simp_rw [Iso.trans_hom, ← Iso.eq_comp_inv, Category.assoc, ← Iso.inv_comp_eq]
  ext
  · have : (RingHomClass.toRingHom (Algebra.TensorProduct.comm R S T)).comp
      Algebra.TensorProduct.includeLeftRingHom =
      RingHomClass.toRingHom Algebra.TensorProduct.includeRight := rfl
    rw [Categor
-/
lemma pullbackSpecIso'_symmetry [Algebra R T] :
    (pullbackSymmetry .. ≪≫ pullbackSpecIso' R S T).hom =
      (pullbackSpecIso' ..).hom ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.comm R S T)) := by
  simp_rw [Iso.trans_hom, ← Iso.eq_comp_inv, Category.assoc, ← Iso.inv_comp_eq]
  ext
  · have : (RingHomClass.toRingHom (Algebra.TensorProduct.comm R S T)).comp
      Algebra.TensorProduct.includeLeftRingHom =
      RingHomClass.toRingHom Algebra.TensorProduct.includeRight := rfl
    rw [Category.assoc]; rw [pullbackSymmetry_hom_comp_fst]
    simp only [pullbackSpecIso', specOverSpec_over, pullbackSpecIso_inv_snd, Category.assoc,
      pullbackSpecIso_inv_fst, ← Spec.map_comp, ← CommRingCat.ofHom_comp, this]
  have : (RingHomClass.toRingHom (Algebra.TensorProduct.comm R S T)).comp
      (RingHomClass.toRingHom Algebra.TensorProduct.includeRight) =
      Algebra.TensorProduct.includeLeftRingHom := rfl
  rw [Category.assoc]; rw [pullbackSymmetry_hom_comp_snd]
  simp only [pullbackSpecIso', specOverSpec_over, pullbackSpecIso_inv_fst, Category.assoc,
    pullbackSpecIso_inv_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp, this]

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Algebra
  signature: R T] :
  body: by
    rw [← cancel_epi (pullbackSymmetry .. ≪≫ pullbackSpecIso' ..).inv]; rw [Scheme.canonicallyOverPullback_over]; rw [Iso.inv_hom_id_assoc]; rw [Iso.trans_inv]; rw [Category.assoc]; rw [pullbackSymmetry_inv_comp_snd]
    exact (pullbackSpecIso_inv_fst ..).symm

中文:
实例 [Algebra
  签名: R T] :
  定义体: by
    rw [← cancel_epi (pullbackSymmetry .. ≪≫ pullbackSpecIso' ..).inv]; rw [Scheme.canonicallyOverPullback_over]; rw [Iso.inv_hom_id_assoc]; rw [Iso.trans_inv]; rw [Category.assoc]; rw [pullbackSymmetry_inv_comp_snd]
    exact (pullbackSpecIso_inv_fst ..).symm

Depends on / 依赖: Category, Category.assoc, Iso.inv_hom_id_assoc, Iso.trans_inv, Scheme, Scheme.canonicallyOverPullback_over, cancel_epi, canonicallyOverPullback_over, inv_hom_id_assoc, pullbackSpecIso, pullbackSpecIso_inv_fst, pullbackSymmetry, pullbackSymmetry_inv_comp_snd, trans_inv
-/
instance [Algebra R T] :
    (pullbackSymmetry .. ≪≫ pullbackSpecIso' R S T).hom.IsOver (Spec (.of S)) where
  comp_over := by
    rw [← cancel_epi (pullbackSymmetry .. ≪≫ pullbackSpecIso' ..).inv]; rw [Scheme.canonicallyOverPullback_over]; rw [Iso.inv_hom_id_assoc]; rw [Iso.trans_inv]; rw [Category.assoc]; rw [pullbackSymmetry_inv_comp_snd]
    exact (pullbackSpecIso_inv_fst ..).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option linter.flexible false in
-- The `simp` calls are non-terminal merely because the `erw` calls are necessary.
-- If this proof breaks because of a non-terminal `simp` in the future, it is likely that one can
-- simply remove the following `erw`.
variable (R S T) in
/--
lemma `μ_pullback_left_fst` / 引理 `μ_pullback_left_fst`

English:
lemma μ_pullback_left_fst
  given: [Algebra R T]
  proof: by
  simp
  ext <;> simp
  · simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      Algebra.TensorProduct.mapRingHom_comp_includeLeftRingHom]
    simp [specOverSpec_over]
    erw [Over.tensorHom_left_fst_assoc]
    simp [pullbackSpecIso']
    rfl
  · simp only [← Spec.map_comp, ← CommRingCat.of

中文:
引理 μ_pullback_left_fst
  条件: [Algebra R T]
  证明: by
  simp
  ext <;> simp
  · simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      Algebra.TensorProduct.mapRingHom_comp_includeLeftRingHom]
    simp [specOverSpec_over]
    erw [Over.tensorHom_left_fst_assoc]
    simp [pullbackSpecIso']
    rfl
  · simp only [← Spec.map_comp, ← CommRingCat.of

Depends on / 依赖: Algebra, Algebra.TensorProduct.mapRingHom_comp_includeLeftRingHom, Algebra.TensorProduct.mapRingHom_comp_includeRight, CommRingCat, CommRingCat.ofHom_comp, Over.tensorHom_left_fst_assoc, Over.tensorHom_left_snd_assoc, Spec.map_comp, TensorProduct, mapRingHom_comp_includeLeftRingHom, mapRingHom_comp_includeRight, map_comp, ofHom_comp, pullbackSpecIso, specOverSpec_over, tensorHom_left_fst_assoc, tensorHom_left_snd_assoc
-/
lemma μ_pullback_left_fst [Algebra R T] :
    (LaxMonoidal.μ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S))))
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R T))))
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R T))))).left ≫
        pullback.fst _ _ =
    (((pullbackSymmetry .. ≪≫ pullbackSpecIso' R S T).hom.asOver (Spec (.of S)) otimesₘ
        ((pullbackSymmetry .. ≪≫ pullbackSpecIso' R S T).hom.asOver (Spec (.of S)))).left) ≫
          (pullbackSpecIso S (S otimes[R] T) (S otimes[R] T)).hom ≫
            Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.mapRingHom (algebraMap _ _)
              Algebra.TensorProduct.includeRight.toRingHom
              Algebra.TensorProduct.includeRight.toRingHom
              (by simp [← IsScalarTower.algebraMap_eq])
              (by simp [← IsScalarTower.algebraMap_eq]))) ≫ (pullbackSpecIso R T T).inv := by
  simp
  ext <;> simp
  · simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      Algebra.TensorProduct.mapRingHom_comp_includeLeftRingHom]
    simp [specOverSpec_over]
    erw [Over.tensorHom_left_fst_assoc]
    simp [pullbackSpecIso']
    rfl
  · simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      Algebra.TensorProduct.mapRingHom_comp_includeRight]
    simp [specOverSpec_over]
    erw [Over.tensorHom_left_snd_assoc]
    simp [pullbackSpecIso']
    rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Bialgebra
  signature: R T] :
  body: by
    ext
    rw [← cancel_mono (pullbackSpecIso' ..).inv]
    ext
    · simp [Scheme.monObjAsOverPullback_one, ε_algSpec_left (R := CommRingCat.of _),
        pullbackSpecIso', specOverSpec_over, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        AlgHom.toUnder, Under.homMk_right, Bialgebra.Tensor

中文:
实例 [Bialgebra
  签名: R T] :
  定义体: by
    ext
    rw [← cancel_mono (pullbackSpecIso' ..).inv]
    ext
    · simp [Scheme.monObjAsOverPullback_one, ε_algSpec_left (R := CommRingCat.of _),
        pullbackSpecIso', specOverSpec_over, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        AlgHom.toUnder, Under.homMk_right, Bialgebra.Tensor

Depends on / 依赖: AlgHom, AlgHom.comp_toRingHom, AlgHom.toUnder, Bialgebra, Bialgebra.TensorProduct.counitAlgHom_def, CommRingCat, CommRingCat.of, CommRingCat.ofHom_comp, RingHom, RingHom.comp_assoc, Scheme, Scheme.monObjAsOverPullback_one, Spec.map_comp, TensorProduct, Under.homMk_right, cancel_mono, comp_assoc, comp_toRingHom, counitAlgHom_def, homMk_right
-/
instance [Bialgebra R T] :
IsMonHom (pullbackSymmetry .. ≪≫ pullbackSpecIso' R S T).hom.asOver (Spec (.of S)) where
  one_hom := by
    ext
    rw [← cancel_mono (pullbackSpecIso' ..).inv]
    ext
    · simp [Scheme.monObjAsOverPullback_one, ε_algSpec_left (R := CommRingCat.of _),
        pullbackSpecIso', specOverSpec_over, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        AlgHom.toUnder, Under.homMk_right, Bialgebra.TensorProduct.counitAlgHom_def,
        AlgHom.comp_toRingHom, RingHom.comp_assoc]
    · simp [Scheme.monObjAsOverPullback_one, ε_algSpec_left (R := CommRingCat.of _),
        pullbackSpecIso', specOverSpec_over, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        AlgHom.toUnder, Under.homMk_right,
        ← AlgHom.coe_restrictScalars R (Bialgebra.counitAlgHom S _), -AlgHom.coe_restrictScalars,
        ← AlgHom.comp_toRingHom, Bialgebra.counitAlgHom_comp_includeRight]
      simp [AlgHom.comp_toRingHom, Algebra.toRingHom_ofId]
  mul_hom := by
    ext
    rw [← cancel_mono (pullbackSpecIso' ..).inv]
    ext
    · have : includeLeftRingHom = algebraMap S (S otimes[R] T) := rfl
      simp [Scheme.monObjAsOverPullback_mul, pullbackSpecIso', specOverSpec_over, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, OverClass.asOver, mul_spec_asOver_spec_left, this, Hom.asOver,
        OverClass.asOverHom, pullback.condition]
      rfl
    · convert! congr($(μ_pullback_left_fst R S T) ≫ (pullbackSpecIso R T T).hom ≫
        Spec.map (CommRingCat.ofHom (Bialgebra.comulAlgHom R T).toRingHom)) using 1
      · simp [Scheme.monObjAsOverPullback_mul, pullbackSpecIso', specOverSpec_over,
          OverClass.asOver, Hom.asOver, OverClass.asOverHom, mul_spec_asOver_spec_left]
      · simp [pullbackSpecIso', specOverSpec_over, OverClass.asOver, Hom.asOver, ← Spec.map_comp,
          OverClass.asOverHom, mul_spec_asOver_spec_left, ← CommRingCat.ofHom_comp,
          ← Bialgebra.comul_includeRight]

end universe_monomorphic
end topEdge

/-!
### Right edge: The essential image of `Spec` on Hopf algebras

In this section we show that the essential image of `R`-Hopf algebras under `Spec` is precisely
affine group schemes over `Spec R`.
-/

section rightEdge

/-- The essential image of `R`-algebras under `Spec` is precisely affine schemes over `Spec R`. -/
@[simp]
/--
lemma `essImage_algSpec` / 引理 `essImage_algSpec`

English:
lemma essImage_algSpec
  given: {G : Over <| Spec R}
  statement: (algSpec R).essImage G ↔ IsAffine G.left
  proof: by
  simp [algSpec, Functor.essImage_overPost (F := Scheme.Spec)]

中文:
引理 essImage_algSpec
  条件: {G : Over <| Spec R}
  结论: (algSpec R).essImage G ↔ IsAffine G.left
  证明: by
  simp [algSpec, Functor.essImage_overPost (F := Scheme.Spec)]

Depends on / 依赖: Functor, Functor.essImage_overPost, Scheme, Scheme.Spec, algSpec, essImage_overPost
-/
lemma essImage_algSpec {G : Over <| Spec R} : (algSpec R).essImage G ↔ IsAffine G.left := by
  simp [algSpec, Functor.essImage_overPost (F := Scheme.Spec)]

/-- The essential image of `R`-bialgebras under `Spec` is precisely affine monoid schemes over
`Spec R`. -/
@[simp]
/--
lemma `essImage_bialgSpec` / 引理 `essImage_bialgSpec`

English:
lemma essImage_bialgSpec
  given: {G : Mon <| Over <| Spec R}
  proof: by simp

中文:
引理 essImage_bialgSpec
  条件: {G : Mon <| Over <| Spec R}
  证明: by simp
-/
lemma essImage_bialgSpec {G : Mon <| Over <| Spec R} :
    (bialgSpec R).essImage G ↔ IsAffine G.X.left := by simp

/-- The essential image of `R`-Hopf algebras under `Spec` is precisely affine group schemes over
`Spec R`. -/
@[simp]
/--
lemma `essImage_hopfSpec` / 引理 `essImage_hopfSpec`

English:
lemma essImage_hopfSpec
  given: {G : Grp <| Over <| Spec R}
  proof: by simp

中文:
引理 essImage_hopfSpec
  条件: {G : Grp <| Over <| Spec R}
  证明: by simp
-/
lemma essImage_hopfSpec {G : Grp <| Over <| Spec R} :
    (hopfSpec R).essImage G ↔ IsAffine G.X.left := by simp

end rightEdge

end AlgebraicGeometry
