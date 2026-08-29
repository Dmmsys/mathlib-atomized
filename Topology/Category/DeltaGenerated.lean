/-
Copyright (c) 2024 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Monad.Limits
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.Compactness.DeltaGeneratedSpace
public import Mathlib.Topology.Convenient.Category

/-!
# Delta-generated topological spaces

This file defines the category `DeltaGenerated` of delta-generated spaces.
This is a particular case of the construction in the file
`Mathlib/Topology/Convenient/Category.Lean`: this is the category of
`X`-generated spaces where `X` is the family of spaces `Fin n → ℝ`
for all `n : ℕ`.

## TODO
* `DeltaGenerated` is Cartesian closed (@joelriou).

## References
* https://ncatlab.org/nlab/show/Delta-generated+topological+space

-/

@[expose] public section

universe u

open CategoryTheory

/--
Definition of `DeltaGenerated` / `DeltaGenerated` 的定义

English:
abbreviation DeltaGenerated
  body: GeneratedByTopCat.{u} (fun n => Fin n -> Real)

中文:
缩写 DeltaGenerated
  定义体: GeneratedByTopCat.{u} (fun n => Fin n -> Real)

Depends on / 依赖: GeneratedByTopCat
-/
abbrev DeltaGenerated := GeneratedByTopCat.{u} (fun n => Fin n -> Real)

/--
Definition of `TopCat.toDeltaGenerated` / `TopCat.toDeltaGenerated` 的定义

English:
abbreviation TopCat.toDeltaGenerated
  signature: : TopCat.{u} ⥤ DeltaGenerated.{u}
  body: TopCat.toGeneratedByTopCat

中文:
缩写 顶元素范畴.toDeltaGenerated
  签名: : 顶元素范畴.{u} ⥤ DeltaGenerated.{u}
  定义体: TopCat.toGeneratedByTopCat

Depends on / 依赖: TopCat, TopCat.toGeneratedByTopCat, toGeneratedByTopCat
-/
abbrev TopCat.toDeltaGenerated : TopCat.{u} ⥤ DeltaGenerated.{u} :=
  TopCat.toGeneratedByTopCat

namespace DeltaGenerated

/--
Definition of `of` / `of` 的定义

English:
abbreviation of
  signature: (X : Type u) [TopologicalSpace X] [DeltaGeneratedSpace X]
  body: GeneratedByTopCat.of X

中文:
缩写 of
  签名: (X : 类型u) [拓扑空间 X] [DeltaGeneratedSpace X]
  定义体: GeneratedByTopCat.of X

Depends on / 依赖: GeneratedByTopCat, GeneratedByTopCat.of
-/
abbrev of (X : Type u) [TopologicalSpace X] [DeltaGeneratedSpace X] : DeltaGenerated.{u} :=
  GeneratedByTopCat.of X

/--
Definition of `deltaGeneratedToTop` / `deltaGeneratedToTop` 的定义

English:
abbreviation deltaGeneratedToTop
  signature: : DeltaGenerated.{u} ⥤ TopCat.{u}
  body: GeneratedByTopCat.toTopCat

中文:
缩写 deltaGeneratedToTop
  签名: : DeltaGenerated.{u} ⥤ 顶元素范畴.{u}
  定义体: GeneratedByTopCat.toTopCat

Depends on / 依赖: GeneratedByTopCat, GeneratedByTopCat.toTopCat, toTopCat
-/
abbrev deltaGeneratedToTop : DeltaGenerated.{u} ⥤ TopCat.{u} :=
  GeneratedByTopCat.toTopCat

/--
Definition of `fullyFaithfulDeltaGeneratedToTop` / `fullyFaithfulDeltaGeneratedToTop` 的定义

English:
abbreviation fullyFaithfulDeltaGeneratedToTop
  signature: : deltaGeneratedToTop.{u}.FullyFaithful
  body: GeneratedByTopCat.fullyFaithfulToTopCat _

@[deprecated (since := "2026-04-23")] alias topToDeltaGenerated := TopCat.toDeltaGenerated

中文:
缩写 fullyFaithfulDeltaGeneratedToTop
  签名: : deltaGeneratedToTop.{u}.满忠实
  定义体: GeneratedByTopCat.fullyFaithfulToTopCat _

@[deprecated (since := "2026-04-23")] alias topToDeltaGenerated := TopCat.toDeltaGenerated

Depends on / 依赖: GeneratedByTopCat, GeneratedByTopCat.fullyFaithfulToTopCat, fullyFaithfulToTopCat
-/
abbrev fullyFaithfulDeltaGeneratedToTop : deltaGeneratedToTop.{u}.FullyFaithful :=
  GeneratedByTopCat.fullyFaithfulToTopCat _

@[deprecated (since := "2026-04-23")] alias topToDeltaGenerated := TopCat.toDeltaGenerated

/--
Definition of `coreflectorAdjunction` / `coreflectorAdjunction` 的定义

English:
abbreviation coreflectorAdjunction
  signature: : deltaGeneratedToTop ⊣ TopCat.toDeltaGenerated
  body: GeneratedByTopCat.adj

中文:
缩写 coreflectorAdjunction
  签名: : deltaGeneratedToTop ⊣ 顶元素范畴.toDeltaGenerated
  定义体: GeneratedByTopCat.adj

Depends on / 依赖: GeneratedByTopCat, GeneratedByTopCat.adj
-/
abbrev coreflectorAdjunction : deltaGeneratedToTop ⊣ TopCat.toDeltaGenerated :=
  GeneratedByTopCat.adj

end DeltaGenerated
