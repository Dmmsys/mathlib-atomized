/-
Copyright (c) 2023 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
module

public import Mathlib.Geometry.Manifold.LocalInvariantProperties
public import Mathlib.Topology.Sheaves.LocalPredicate

/-! # Generic construction of a sheaf from a `LocalInvariantProp` on a manifold

This file constructs the sheaf-of-types of functions `f : M → M'` (for charted spaces `M`, `M'`)
which satisfy the lifted property `LiftProp P` associated to some locally invariant (in the sense
of `StructureGroupoid.LocalInvariantProp`) property `P` on the model spaces of `M` and `M'`. For
example, differentiability and smoothness are locally invariant properties in this sense, so this
construction can be used to construct the sheaf of differentiable functions on a manifold and the
sheaf of smooth functions on a manifold.

The mathematical work is in associating a `TopCat.LocalPredicate` to a
`StructureGroupoid.LocalInvariantProp`: that is, showing that a differential-geometric "locally
invariant" property is preserved under restriction and gluing.

## Main definitions

* `StructureGroupoid.LocalInvariantProp.localPredicate`: the `TopCat.LocalPredicate` (in the
  sheaf-theoretic sense) on functions from open subsets of `M` into `M'`, which states whether
  such functions satisfy `LiftProp P`.
* `StructureGroupoid.LocalInvariantProp.sheaf`: the sheaf-of-types of functions `f : M → M'`
  which satisfy the lifted property `LiftProp P`.
-/

@[expose] public section


open scoped Manifold Topology

open Set TopologicalSpace StructureGroupoid StructureGroupoid.LocalInvariantProp Opposite

universe u

variable {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {G : StructureGroupoid H} {G' : StructureGroupoid H'} {P : (H -> H') -> Set H -> H -> Prop}
  (M : Type u) [TopologicalSpace M] [ChartedSpace H M] (M' : Type u) [TopologicalSpace M']
  [ChartedSpace H' M']

/--
Instance `TopCat.of.chartedSpace` / 实例 `TopCat.of.chartedSpace`

English:
instance TopCat.of.chartedSpace
  signature: : ChartedSpace H (TopCat.of M)
  body: inferInstanceAs ChartedSpace H M

中文:
实例 TopCat.of.chartedSpace
  签名: : ChartedSpace H (TopCat.of M)
  定义体: inferInstanceAs ChartedSpace H M

Depends on / 依赖: ChartedSpace
-/
instance TopCat.of.chartedSpace : ChartedSpace H (TopCat.of M) :=
inferInstanceAs ChartedSpace H M

/--
Instance `TopCat.of.hasGroupoid` / 实例 `TopCat.of.hasGroupoid`

English:
instance TopCat.of.hasGroupoid
  signature: [HasGroupoid M G]
  body: inferInstanceAs HasGroupoid M G

中文:
实例 TopCat.of.hasGroupoid
  签名: [HasGroupoid M G]
  定义体: inferInstanceAs HasGroupoid M G

Depends on / 依赖: HasGroupoid
-/
instance TopCat.of.hasGroupoid [HasGroupoid M G] : HasGroupoid (TopCat.of M) G :=
inferInstanceAs HasGroupoid M G

/--
Definition of `StructureGroupoid.LocalInvariantProp.localPredicate` / `StructureGroupoid.LocalInvariantProp.localPredicate` 的定义

English:
definition StructureGroupoid.LocalInvariantProp.localPredicate
  signature: (hG : LocalInvariantProp G G' P)
  body: fun f : U -> M' => ChartedSpace.LiftProp P f
  res := by
    intro U V i f h x
    have hUV : U <= V := CategoryTheory.leOfHom i
    change ChartedSpace.LiftPropAt P (f ∘ Opens.inclusion hUV) x
    rw [← hG.liftPropAt_iff_comp_inclusion hUV]
    apply h
  locality := by
    intro V f h x
    obtain 

中文:
定义 StructureGroupoid.LocalInvariantProp.localPredicate
  签名: (hG : LocalInvariant命题 G G' P)
  定义体: fun f : U -> M' => ChartedSpace.LiftProp P f
  res := by
    intro U V i f h x
    have hUV : U <= V := CategoryTheory.leOfHom i
    change ChartedSpace.LiftPropAt P (f ∘ Opens.inclusion hUV) x
    rw [← hG.liftPropAt_iff_comp_inclusion hUV]
    apply h
  locality := by
    intro V f h x
    obtain 

Depends on / 依赖: ChartedSpace, ChartedSpace.LiftProp, LiftProp
-/
def StructureGroupoid.LocalInvariantProp.localPredicate (hG : LocalInvariantProp G G' P) :
    TopCat.LocalPredicate fun _ : TopCat.of M => M' where
  pred {U : Opens (TopCat.of M)} := fun f : U -> M' => ChartedSpace.LiftProp P f
  res := by
    intro U V i f h x
    have hUV : U <= V := CategoryTheory.leOfHom i
    change ChartedSpace.LiftPropAt P (f ∘ Opens.inclusion hUV) x
    rw [← hG.liftPropAt_iff_comp_inclusion hUV]
    apply h
  locality := by
    intro V f h x
    obtain ⟨U, hxU, i, hU : ChartedSpace.LiftProp P (f ∘ _)⟩ := h x
    let x' : U := ⟨x, hxU⟩
    have hUV : U <= V := CategoryTheory.leOfHom i
    have : ChartedSpace.LiftPropAt P f (Opens.inclusion hUV x') := by
      rw [hG.liftPropAt_iff_comp_inclusion hUV]
      exact hU x'
    convert! this

/--
Definition of `StructureGroupoid.LocalInvariantProp.sheaf` / `StructureGroupoid.LocalInvariantProp.sheaf` 的定义

English:
definition StructureGroupoid.LocalInvariantProp.sheaf
  signature: (hG : LocalInvariantProp G G' P)
  body: TopCat.subsheafToTypes (hG.localPredicate M M')

中文:
定义 StructureGroupoid.LocalInvariantProp.sheaf
  签名: (hG : LocalInvariant命题 G G' P)
  定义体: TopCat.subsheafToTypes (hG.localPredicate M M')

Depends on / 依赖: TopCat, TopCat.subsheafToTypes, hG.localPredicate, localPredicate, subsheafToTypes
-/
def StructureGroupoid.LocalInvariantProp.sheaf (hG : LocalInvariantProp G G' P) :
    TopCat.Sheaf (Type u) (TopCat.of M) :=
  TopCat.subsheafToTypes (hG.localPredicate M M')

/--
Instance `StructureGroupoid.LocalInvariantProp.sheafHasCoeToFun` / 实例 `StructureGroupoid.LocalInvariantProp.sheafHasCoeToFun`

English:
instance StructureGroupoid.LocalInvariantProp.sheafHasCoeToFun
  signature: (hG : LocalInvariantProp G G' P)
  body: a.1

中文:
实例 StructureGroupoid.LocalInvariantProp.sheafHasCoeToFun
  签名: (hG : LocalInvariant命题 G G' P)
  定义体: a.1
-/
instance StructureGroupoid.LocalInvariantProp.sheafHasCoeToFun (hG : LocalInvariantProp G G' P)
    (U : (Opens (TopCat.of M))ᵒᵖ) : CoeFun ((hG.sheaf M M').obj.obj U) fun _ => ↑(unop U) -> M' where
  coe a := a.1

/--
theorem `StructureGroupoid.LocalInvariantProp.section_spec` / 定理 `StructureGroupoid.LocalInvariantProp.section_spec`

English:
theorem StructureGroupoid.LocalInvariantProp.section_spec
  statement: (hG : LocalInvariantProp G G' P)
  proof: f.2

中文:
定理 StructureGroupoid.LocalInvariantProp.section_spec
  结论: (hG : LocalInvariant命题 G G' P)
  证明: f.2
-/
theorem StructureGroupoid.LocalInvariantProp.section_spec (hG : LocalInvariantProp G G' P)
    (U : (Opens (TopCat.of M))ᵒᵖ) (f : (hG.sheaf M M').obj.obj U) : ChartedSpace.LiftProp P f :=
  f.2
