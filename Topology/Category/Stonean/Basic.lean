/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Dagur Asgeirsson
-/
module

public import Mathlib.Topology.ExtremallyDisconnected
public import Mathlib.Topology.Category.CompHaus.Projective
public import Mathlib.Topology.Category.Profinite.Basic
/-!
# Extremally disconnected sets

This file develops some of the basic theory of extremally disconnected compact Hausdorff spaces.

## Overview

This file defines the type `Stonean` of all extremally (note: not "extremely"!)
disconnected compact Hausdorff spaces, gives it the structure of a large category,
and proves some basic observations about this category and various functors from it.

The Lean implementation: a term of type `Stonean` is a pair, considering of
a term of type `CompHaus` (i.e. a compact Hausdorff topological space) plus
a proof that the space is extremally disconnected.
This is equivalent to the assertion that the term is projective in `CompHaus`,
in the sense of category theory (i.e., such that morphisms out of the object
can be lifted along epimorphisms).

## Main definitions

* `Stonean` : the category of extremally disconnected compact Hausdorff spaces.
* `Stonean.toCompHaus` : the forgetful functor `Stonean ⥤ CompHaus` from Stonean
  spaces to compact Hausdorff spaces
* `Stonean.toProfinite` : the functor from Stonean spaces to profinite spaces.

## Implementation

The category `Stonean` is defined using the structure `CompHausLike`. See the file
`CompHausLike.Basic` for more information.

-/

@[expose] public section
universe u

open CategoryTheory
open scoped Topology

/--
Definition of `Stonean` / `Stonean` 的定义

English:
abbreviation Stonean
  body: CompHausLike (fun X => ExtremallyDisconnected X)

中文:
缩写 Stonean
  定义体: CompHausLike (fun X => ExtremallyDisconnected X)

Depends on / 依赖: CompHausLike, ExtremallyDisconnected
-/
abbrev Stonean := CompHausLike (fun X => ExtremallyDisconnected X)

namespace CompHaus

/-- `Projective` implies `ExtremallyDisconnected`. -/
instance (X : CompHaus.{u}) [Projective X] : ExtremallyDisconnected X := by
  apply CompactT2.Projective.extremallyDisconnected
  intro A B _ _ _ _ _ _ f g hf hg hsurj
  let A' : CompHaus := CompHaus.of A
  let B' : CompHaus := CompHaus.of B
  let f' : X ⟶ B' := CompHausLike.ofHom _ ⟨f, hf⟩
  let g' : A' ⟶ B' := CompHausLike.ofHom _ ⟨g,hg⟩
  have : Epi g' := by
    rw [CompHaus.epi_iff_surjective]
    assumption
  obtain ⟨h, hh⟩ := Projective.factors f' g'
  refine ⟨h, h.hom.hom.2, ?_⟩
  ext t
  apply_fun (fun e => e t) at hh
  exact hh

/-- `Projective` implies `Stonean`. -/
@[simps!]
/--
Definition of `toStonean` / `toStonean` 的定义

English:
definition toStonean
  signature: (X : CompHaus.{u}) [Projective X]
  body: X.toTop
  prop := inferInstance

中文:
定义 toStonean
  签名: (X : CompHaus.{u}) [投射 X]
  定义体: X.toTop
  prop := inferInstance

Depends on / 依赖: X.toTop
-/
def toStonean (X : CompHaus.{u}) [Projective X] :
    Stonean where
  toTop := X.toTop
  prop := inferInstance

end CompHaus

namespace Stonean

/--
Definition of `toCompHaus` / `toCompHaus` 的定义

English:
abbreviation toCompHaus
  signature: : Stonean.{u} ⥤ CompHaus.{u}
  body: compHausLikeToCompHaus _

中文:
缩写 toCompHaus
  签名: : Stonean.{u} ⥤ CompHaus.{u}
  定义体: compHausLikeToCompHaus _

Depends on / 依赖: compHausLikeToCompHaus
-/
abbrev toCompHaus : Stonean.{u} ⥤ CompHaus.{u} :=
  compHausLikeToCompHaus _

/--
Definition of `fullyFaithfulToCompHaus` / `fullyFaithfulToCompHaus` 的定义

English:
abbreviation fullyFaithfulToCompHaus
  signature: : toCompHaus.FullyFaithful
  body: CompHausLike.fullyFaithfulToCompHausLike _

中文:
缩写 fullyFaithfulToCompHaus
  签名: : toCompHaus.满忠实
  定义体: CompHausLike.fullyFaithfulToCompHausLike _

Depends on / 依赖: CompHausLike, CompHausLike.fullyFaithfulToCompHausLike, fullyFaithfulToCompHausLike
-/
abbrev fullyFaithfulToCompHaus : toCompHaus.FullyFaithful :=
  CompHausLike.fullyFaithfulToCompHausLike _

open CompHausLike

instance (X : Type*) [TopologicalSpace X]
    [ExtremallyDisconnected X] : HasProp (fun Y => ExtremallyDisconnected Y) X :=
  ⟨(inferInstance : ExtremallyDisconnected X)⟩

/--
Definition of `of` / `of` 的定义

English:
abbreviation of
  signature: (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
  body: CompHausLike.of _ X

中文:
缩写 of
  签名: (X : 类型) [拓扑空间 X] [紧空间 X] [T2空间 X]
  定义体: CompHausLike.of _ X

Depends on / 依赖: CompHausLike, CompHausLike.of
-/
abbrev of (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ExtremallyDisconnected X] : Stonean := CompHausLike.of _ X

instance (X : Stonean.{u}) : ExtremallyDisconnected X := X.prop

/--
Definition of `toProfinite` / `toProfinite` 的定义

English:
abbreviation toProfinite
  signature: : Stonean.{u} ⥤ Profinite.{u}
  body: CompHausLike.toCompHausLike (fun _ => inferInstance)

中文:
缩写 toProfinite
  签名: : Stonean.{u} ⥤ Profinite.{u}
  定义体: CompHausLike.toCompHausLike (fun _ => inferInstance)

Depends on / 依赖: CompHausLike, CompHausLike.toCompHausLike, toCompHausLike
-/
abbrev toProfinite : Stonean.{u} ⥤ Profinite.{u} :=
  CompHausLike.toCompHausLike (fun _ => inferInstance)

/--
Definition of `mkFinite` / `mkFinite` 的定义

English:
definition mkFinite
  signature: (X : Type*) [Finite X] [TopologicalSpace X] [DiscreteTopology X]
  body: (CompHaus.of X).toTop
  prop := by
    dsimp
    constructor
    intro U _
    apply isOpen_discrete (closure U)

中文:
定义 mkFinite
  签名: (X : 类型) [有限 X] [拓扑空间 X] [离散拓扑 X]
  定义体: (CompHaus.of X).toTop
  prop := by
    dsimp
    constructor
    intro U _
    apply isOpen_discrete (closure U)

Depends on / 依赖: CompHaus, CompHaus.of
-/
def mkFinite (X : Type*) [Finite X] [TopologicalSpace X] [DiscreteTopology X] : Stonean where
  toTop := (CompHaus.of X).toTop
  prop := by
    dsimp
    constructor
    intro U _
    apply isOpen_discrete (closure U)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `epi_iff_surjective` / 引理 `epi_iff_surjective`

English:
lemma epi_iff_surjective
  given: {X Y : Stonean} (f : X ⟶ Y)
  proof: by
  refine ⟨?_, fun h => ConcreteCategory.epi_of_surjective f h⟩
  dsimp [Function.Surjective]
  intro h y
  by_contra! hy
  let C := Set.range f
  have hC : IsClosed C := (isCompact_range f.hom.hom.continuous).isClosed
  let U := Cᶜ
  have hUy : U in 𝓝 y := by
    simp only [U, C, Set.mem_range, hy, exists_false, not_false_eq_true, hC.compl_mem_nhds]
  obtain ⟨V, hV, hyV, hVU⟩ := isTopologicalBasis_isClopen.mem_nhds_iff.mp hUy
  classical
  let g : Y ⟶ mkFinite (ULift (Fin 2)) := ConcreteCategory.ofHom
    ⟨(LocallyConstant.ofIsClopen hV).map ULift.up, LocallyConstant.continuous _⟩
  let h : Y ⟶ mkFinite (ULift (Fin 2)) := ConcreteCategory.ofHom ⟨fun _ => ⟨1⟩, continuous_const⟩
  have H : h = g := by
    rw [← cancel_epi f]
    ext x
    apply ULift.ext -- why is `ext` not doing this automatically?
    change 1 = ite _ _ _ -- why is `dsimp` not getting me here?
    rw [if_neg]
    refine mt (hVU ·) ?_ -- what would be an idiomatic tactic for this step?
    simpa only [U, Set.mem_compl_iff, Set.mem_range, not_exists, not_forall, not_not]
      using! exists_apply_eq_apply f x
  apply_fun fun e => (e y).down at H
  change 1 = ite _ _ _ at H -- why is `dsimp at H` not getting me here?
  rw [if_pos hyV] at H
  exact one_ne_zero H

中文:
引理 epi_iff_surjective
  条件: {X Y : Stonean} (f : X ⟶ Y)
  证明: by
  refine ⟨?_, fun h => ConcreteCategory.epi_of_surjective f h⟩
  dsimp [Function.Surjective]
  intro h y
  by_contra! hy
  let C := Set.range f
  have hC : IsClosed C := (isCompact_range f.hom.hom.continuous).isClosed
  let U := Cᶜ
  have hUy : U in 𝓝 y := by
    simp only [U, C, Set.mem_range, hy, exists_false, not_false_eq_true, hC.compl_mem_nhds]
  obtain ⟨V, hV, hyV, hVU⟩ := isTopologicalBasis_isClopen.mem_nhds_iff.mp hUy
  classical
  let g : Y ⟶ mkFinite (ULift (Fin 2)) := ConcreteCategory.ofHom
    ⟨(LocallyConstant.ofIsClopen hV).map ULift.up, LocallyConstant.continuous _⟩
  let h : Y ⟶ mkFinite (ULift (Fin 2)) := ConcreteCategory.ofHom ⟨fun _ => ⟨1⟩, continuous_const⟩
  have H : h = g := by
    rw [← cancel_epi f]
    ext x
    apply ULift.ext -- why is `ext` not doing this automatically?
    change 1 = ite _ _ _ -- why is `dsimp` not getting me here?
    rw [if_neg]
    refine mt (hVU ·) ?_ -- what would be an idiomatic tactic for this step?
    simpa only [U, Set.mem_compl_iff, Set.mem_range, not_exists, not_forall, not_not]
      using! exists_apply_eq_apply f x
  apply_fun fun e => (e y).down at H
  change 1 = ite _ _ _ at H -- why is `dsimp at H` not getting me here?
  rw [if_pos hyV] at H
  exact one_ne_zero H

Depends on / 依赖: ConcreteCategory, ConcreteCategory.epi_of_surjective, ConcreteCategory.ofHom, Function, Function.Surjective, IsClosed, LocallyConstan, Set.mem_range, Set.range, Surjective, classical, compl_mem_nhds, continuous, epi_of_surjective, exists_false, f.hom.hom.continuous, hC.compl_mem_nhds, isClosed, isCompact_range, isTopologicalBasis_isClopen
-/
lemma epi_iff_surjective {X Y : Stonean} (f : X ⟶ Y) :
    Epi f ↔ Function.Surjective f := by
  refine ⟨?_, fun h => ConcreteCategory.epi_of_surjective f h⟩
  dsimp [Function.Surjective]
  intro h y
  by_contra! hy
  let C := Set.range f
  have hC : IsClosed C := (isCompact_range f.hom.hom.continuous).isClosed
  let U := Cᶜ
  have hUy : U in 𝓝 y := by
    simp only [U, C, Set.mem_range, hy, exists_false, not_false_eq_true, hC.compl_mem_nhds]
  obtain ⟨V, hV, hyV, hVU⟩ := isTopologicalBasis_isClopen.mem_nhds_iff.mp hUy
  classical
  let g : Y ⟶ mkFinite (ULift (Fin 2)) := ConcreteCategory.ofHom
    ⟨(LocallyConstant.ofIsClopen hV).map ULift.up, LocallyConstant.continuous _⟩
  let h : Y ⟶ mkFinite (ULift (Fin 2)) := ConcreteCategory.ofHom ⟨fun _ => ⟨1⟩, continuous_const⟩
  have H : h = g := by
    rw [← cancel_epi f]
    ext x
    apply ULift.ext -- why is `ext` not doing this automatically?
    change 1 = ite _ _ _ -- why is `dsimp` not getting me here?
    rw [if_neg]
    refine mt (hVU ·) ?_ -- what would be an idiomatic tactic for this step?
    simpa only [U, Set.mem_compl_iff, Set.mem_range, not_exists, not_forall, not_not]
      using! exists_apply_eq_apply f x
  apply_fun fun e => (e y).down at H
  change 1 = ite _ _ _ at H -- why is `dsimp at H` not getting me here?
  rw [if_pos hyV] at H
  exact one_ne_zero H

/--
Instance `instProjectiveCompHausCompHaus` / 实例 `instProjectiveCompHausCompHaus`

English:
instance instProjectiveCompHausCompHaus
  signature: (X : Stonean)
  body: by
    intro B C φ f _
    have : ExtremallyDisconnected (toCompHaus.obj X).toTop := X.prop
    have hf : Function.Surjective f := by rwa [← CompHaus.epi_iff_surjective]
    obtain ⟨f', h⟩ := CompactT2.ExtremallyDisconnected.projective φ.hom.hom.continuous
      f.hom.hom.continuous
      hf
    use ofHom _ ⟨f', h.left⟩
    ext
    exact congr_fun h.right _

中文:
实例 instProjectiveCompHausCompHaus
  签名: (X : Stonean)
  定义体: by
    intro B C φ f _
    have : ExtremallyDisconnected (toCompHaus.obj X).toTop := X.prop
    have hf : Function.Surjective f := by rwa [← CompHaus.epi_iff_surjective]
    obtain ⟨f', h⟩ := CompactT2.ExtremallyDisconnected.projective φ.hom.hom.continuous
      f.hom.hom.continuous
      hf
    use ofHom _ ⟨f', h.left⟩
    ext
    exact congr_fun h.right _

Depends on / 依赖: CompHaus, CompHaus.epi_iff_surjective, CompactT2, CompactT2.ExtremallyDisconnected.projective, ExtremallyDisconnected, Function, Function.Surjective, Surjective, X.prop, congr_fun, continuous, epi_iff_surjective, f.hom.hom.continuous, h.left, h.right, hom.hom.continuous, projective, toCompHaus, toCompHaus.obj
-/
instance instProjectiveCompHausCompHaus (X : Stonean) : Projective (toCompHaus.obj X) where
  factors := by
    intro B C φ f _
    have : ExtremallyDisconnected (toCompHaus.obj X).toTop := X.prop
    have hf : Function.Surjective f := by rwa [← CompHaus.epi_iff_surjective]
    obtain ⟨f', h⟩ := CompactT2.ExtremallyDisconnected.projective φ.hom.hom.continuous
      f.hom.hom.continuous
      hf
    use ofHom _ ⟨f', h.left⟩
    ext
    exact congr_fun h.right _

/-- Every Stonean space is projective in `Profinite` -/
instance (X : Stonean) : Projective (toProfinite.obj X) where
  factors := by
    intro B C φ f _
    have : ExtremallyDisconnected (toProfinite.obj X) := X.prop
    have hf : Function.Surjective f := by rwa [← Profinite.epi_iff_surjective]
    obtain ⟨f', h⟩ := CompactT2.ExtremallyDisconnected.projective φ.hom.hom.continuous
      f.hom.hom.continuous
      hf
    use ofHom _ ⟨f', h.left⟩
    ext
    exact congr_fun h.right _

/-- Every Stonean space is projective in `Stonean`. -/
instance (X : Stonean) : Projective X where
  factors := by
    intro B C φ f _
    have : ExtremallyDisconnected X.toTop := X.prop
    have hf : Function.Surjective f := by rwa [← Stonean.epi_iff_surjective]
    obtain ⟨f', h⟩ := CompactT2.ExtremallyDisconnected.projective φ.hom.hom.continuous
      f.hom.hom.continuous
      hf
    use ofHom _ ⟨f', h.left⟩
    ext
    exact congr_fun h.right _

end Stonean

namespace CompHaus

/-- If `X` is compact Hausdorff, `presentation X` is a Stonean space equipped with an epimorphism
  down to `X` (see `CompHaus.presentation.π` and `CompHaus.presentation.epi_π`). It is a
  "constructive" witness to the fact that `CompHaus` has enough projectives. -/
noncomputable
/--
Definition of `presentation` / `presentation` 的定义

English:
definition presentation
  signature: (X : CompHaus)
  body: (projectivePresentation X).p.1
  prop := instExtremallyDisconnectedCarrierToTopTrueOfProjective X.projectivePresentation.p

中文:
定义 presentation
  签名: (X : CompHaus)
  定义体: (projectivePresentation X).p.1
  prop := instExtremallyDisconnectedCarrierToTopTrueOfProjective X.projectivePresentation.p

Depends on / 依赖: projectivePresentation
-/
def presentation (X : CompHaus) : Stonean where
  toTop := (projectivePresentation X).p.1
  prop := instExtremallyDisconnectedCarrierToTopTrueOfProjective X.projectivePresentation.p

/-- The morphism from `presentation X` to `X`. -/
noncomputable
/--
Definition of `presentation.π` / `presentation.π` 的定义

English:
definition presentation.π
  signature: (X : CompHaus)
  body: (projectivePresentation X).f

中文:
定义 presentation.π
  签名: (X : CompHaus)
  定义体: (projectivePresentation X).f

Depends on / 依赖: projectivePresentation
-/
def presentation.π (X : CompHaus) : Stonean.toCompHaus.obj X.presentation ⟶ X :=
  (projectivePresentation X).f

/-- The morphism from `presentation X` to `X` is an epimorphism. -/
noncomputable
/--
Instance `presentation.epi_π` / 实例 `presentation.epi_π`

English:
instance presentation.epi_π
  signature: (X : CompHaus)
  body: (projectivePresentation X).epi

中文:
实例 presentation.epi_π
  签名: (X : CompHaus)
  定义体: (projectivePresentation X).epi

Depends on / 依赖: projectivePresentation
-/
instance presentation.epi_π (X : CompHaus) : Epi (π X) :=
  (projectivePresentation X).epi

/--
Definition of `_root_.Stonean.compHaus` / `_root_.Stonean.compHaus` 的定义

English:
abbreviation _root_.Stonean.compHaus
  signature: (X : Stonean)
  body: Stonean.toCompHaus.obj X

中文:
缩写 _root_.Stonean.compHaus
  签名: (X : Stonean)
  定义体: Stonean.toCompHaus.obj X

Depends on / 依赖: Stonean, Stonean.toCompHaus.obj, toCompHaus
-/
abbrev _root_.Stonean.compHaus (X : Stonean) := Stonean.toCompHaus.obj X

/--
```
               X
               |
              (f)
               |
               \/
  Z ---(e)---> Y
```
If `Z` is a Stonean space, `f : X ⟶ Y` an epi in `CompHaus` and `e : Z ⟶ Y` is arbitrary, then
`lift e f` is a fixed (but arbitrary) lift of `e` to a morphism `Z ⟶ X`. It exists because
`Z` is a projective object in `CompHaus`.
-/
noncomputable
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: {X Y : CompHaus} {Z : Stonean} (e : Z.compHaus ⟶ Y) (f : X ⟶ Y) [Epi f]
  body: Projective.factorThru e f

@[simp, reassoc]

中文:
定义 lift
  签名: {X Y : CompHaus} {Z : Stonean} (e : Z.compHaus ⟶ Y) (f : X ⟶ Y) [满态射 f]
  定义体: Projective.factorThru e f

@[simp, reassoc]

Depends on / 依赖: Projective, Projective.factorThru, factorThru
-/
def lift {X Y : CompHaus} {Z : Stonean} (e : Z.compHaus ⟶ Y) (f : X ⟶ Y) [Epi f] :
    Z.compHaus ⟶ X :=
  Projective.factorThru e f

@[simp, reassoc]
/--
lemma `lift_lifts` / 引理 `lift_lifts`

English:
lemma lift_lifts
  given: {X Y : CompHaus} {Z : Stonean} (e : Z.compHaus ⟶ Y) (f : X ⟶ Y) [Epi f]
  proof: by simp [lift]

中文:
引理 lift_lifts
  条件: {X Y : CompHaus} {Z : Stonean} (e : Z.compHaus ⟶ Y) (f : X ⟶ Y) [满态射 f]
  证明: by simp [lift]
-/
lemma lift_lifts {X Y : CompHaus} {Z : Stonean} (e : Z.compHaus ⟶ Y) (f : X ⟶ Y) [Epi f] :
    lift e f ≫ f = e := by simp [lift]

/--
lemma `Gleason` / 引理 `Gleason`

English:
lemma Gleason
  given: (X : CompHaus.{u})
  proof: by
  constructor
  · intro h
    change ExtremallyDisconnected X.toStonean
    infer_instance
  · intro h
    let X' : Stonean := ⟨X.toTop, inferInstance⟩
    change Projective X'.compHaus
    apply Stonean.instProjectiveCompHausCompHaus

中文:
引理 Gleason
  条件: (X : CompHaus.{u})
  证明: by
  constructor
  · intro h
    change ExtremallyDisconnected X.toStonean
    infer_instance
  · intro h
    let X' : Stonean := ⟨X.toTop, inferInstance⟩
    change Projective X'.compHaus
    apply Stonean.instProjectiveCompHausCompHaus

Depends on / 依赖: ExtremallyDisconnected, Projective, Stonean, Stonean.instProjectiveCompHausCompHaus, X.toStonean, X.toTop, compHaus, infer_instance, instProjectiveCompHausCompHaus, toStonean
-/
lemma Gleason (X : CompHaus.{u}) :
    Projective X ↔ ExtremallyDisconnected X := by
  constructor
  · intro h
    change ExtremallyDisconnected X.toStonean
    infer_instance
  · intro h
    let X' : Stonean := ⟨X.toTop, inferInstance⟩
    change Projective X'.compHaus
    apply Stonean.instProjectiveCompHausCompHaus

end CompHaus

namespace Profinite

/-- If `X` is profinite, `presentation X` is a Stonean space equipped with an epimorphism down to
`X` (see `Profinite.presentation.π` and `Profinite.presentation.epi_π`). -/
noncomputable
/--
Definition of `presentation` / `presentation` 的定义

English:
definition presentation
  signature: (X : Profinite)
  body: (profiniteToCompHaus.obj X).projectivePresentation.p.toTop
  prop := (profiniteToCompHaus.obj X).presentation.prop

中文:
定义 presentation
  签名: (X : Profinite)
  定义体: (profiniteToCompHaus.obj X).projectivePresentation.p.toTop
  prop := (profiniteToCompHaus.obj X).presentation.prop

Depends on / 依赖: profiniteToCompHaus, profiniteToCompHaus.obj, projectivePresentation, projectivePresentation.p.toTop
-/
def presentation (X : Profinite) : Stonean where
  toTop := (profiniteToCompHaus.obj X).projectivePresentation.p.toTop
  prop := (profiniteToCompHaus.obj X).presentation.prop

/-- The morphism from `presentation X` to `X`. -/
noncomputable
/--
Definition of `presentation.π` / `presentation.π` 的定义

English:
definition presentation.π
  signature: (X : Profinite)
  body: InducedCategory.homMk (profiniteToCompHaus.obj X).projectivePresentation.f.hom

中文:
定义 presentation.π
  签名: (X : Profinite)
  定义体: InducedCategory.homMk (profiniteToCompHaus.obj X).projectivePresentation.f.hom
-/
def presentation.π (X : Profinite) : Stonean.toProfinite.obj X.presentation ⟶ X :=
  InducedCategory.homMk (profiniteToCompHaus.obj X).projectivePresentation.f.hom

/-- The morphism from `presentation X` to `X` is an epimorphism. -/
noncomputable
/--
Instance `presentation.epi_π` / 实例 `presentation.epi_π`

English:
instance presentation.epi_π
  signature: (X : Profinite)
  body: by
  have := (profiniteToCompHaus.obj X).projectivePresentation.epi
  rw [CompHaus.epi_iff_surjective] at this
  rw [epi_iff_surjective]
  exact this

中文:
实例 presentation.epi_π
  签名: (X : Profinite)
  定义体: by
  have := (profiniteToCompHaus.obj X).projectivePresentation.epi
  rw [CompHaus.epi_iff_surjective] at this
  rw [epi_iff_surjective]
  exact this
-/
instance presentation.epi_π (X : Profinite) : Epi (π X) := by
  have := (profiniteToCompHaus.obj X).projectivePresentation.epi
  rw [CompHaus.epi_iff_surjective] at this
  rw [epi_iff_surjective]
  exact this

/--
```
               X
               |
              (f)
               |
               \/
  Z ---(e)---> Y
```
If `Z` is a Stonean space, `f : X ⟶ Y` an epi in `Profinite` and `e : Z ⟶ Y` is arbitrary,
then `lift e f` is a fixed (but arbitrary) lift of `e` to a morphism `Z ⟶ X`. It is
`CompHaus.lift e f` as a morphism in `Profinite`.
-/
noncomputable
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: {X Y : Profinite} {Z : Stonean} (e : Stonean.toProfinite.obj Z ⟶ Y) (f : X ⟶ Y) [Epi f]
  body: Projective.factorThru e f

@[simp, reassoc]

中文:
定义 lift
  签名: {X Y : Profinite} {Z : Stonean} (e : Stonean.toProfinite.obj Z ⟶ Y) (f : X ⟶ Y) [满态射 f]
  定义体: Projective.factorThru e f

@[simp, reassoc]

Depends on / 依赖: Projective, Projective.factorThru, factorThru
-/
def lift {X Y : Profinite} {Z : Stonean} (e : Stonean.toProfinite.obj Z ⟶ Y) (f : X ⟶ Y) [Epi f] :
    Stonean.toProfinite.obj Z ⟶ X := Projective.factorThru e f

@[simp, reassoc]
/--
lemma `lift_lifts` / 引理 `lift_lifts`

English:
lemma lift_lifts
  statement: {X Y : Profinite} {Z : Stonean} (e : Stonean.toProfinite.obj Z ⟶ Y) (f : X ⟶ Y)
  proof: by simp [lift]

中文:
引理 lift_lifts
  结论: {X Y : Profinite} {Z : Stonean} (e : Stonean.toProfinite.obj Z ⟶ Y) (f : X ⟶ Y)
  证明: by simp [lift]
-/
lemma lift_lifts {X Y : Profinite} {Z : Stonean} (e : Stonean.toProfinite.obj Z ⟶ Y) (f : X ⟶ Y)
    [Epi f] : lift e f ≫ f = e := by simp [lift]

/--
lemma `projective_of_extrDisc` / 引理 `projective_of_extrDisc`

English:
lemma projective_of_extrDisc
  given: {X : Profinite.{u}} (hX : ExtremallyDisconnected X)
  proof: by
  change Projective (Stonean.toProfinite.obj ⟨X.toTop, inferInstance⟩)
  exact inferInstance

中文:
引理 projective_of_extrDisc
  条件: {X : Profinite.{u}} (hX : ExtremallyDisconnected X)
  证明: by
  change Projective (Stonean.toProfinite.obj ⟨X.toTop, inferInstance⟩)
  exact inferInstance

Depends on / 依赖: Projective, Stonean, Stonean.toProfinite.obj, X.toTop, toProfinite
-/
lemma projective_of_extrDisc {X : Profinite.{u}} (hX : ExtremallyDisconnected X) :
    Projective X := by
  change Projective (Stonean.toProfinite.obj ⟨X.toTop, inferInstance⟩)
  exact inferInstance

end Profinite
