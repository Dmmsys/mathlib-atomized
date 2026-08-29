/-
Copyright (c) 2023 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Adam Topaz
-/
module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
public import Mathlib.Geometry.Manifold.Sheaf.Basic
public import Mathlib.Topology.Sheaves.Functors

/-! # The sheaf of smooth functions on a manifold

The sheaf of `𝕜`-smooth functions from a manifold `M` to a manifold `N` can be defined as a sheaf of
types using the construction `StructureGroupoid.LocalInvariantProp.sheaf` from the file
`Mathlib/Geometry/Manifold/Sheaf/Basic.lean`. In this file we write that down (a one-liner), then
do the work of upgrading this to a sheaf of [groups]/[abelian groups]/[rings]/[commutative rings]
when `N` carries more algebraic structure. For example, if `N` is `𝕜` then the sheaf of smooth
functions from `M` to `𝕜` is a sheaf of commutative rings, the *structure sheaf* of `M`.

## Main definitions

* `smoothSheaf`: The sheaf of smooth functions from `M` to `N`, as a sheaf of types
* `smoothSheaf.eval`: Canonical map onto `N` from the stalk of `smoothSheaf IM I M N` at `x`,
  given by evaluating sections at `x`
* `smoothSheafGroup`, `smoothSheafCommGroup`, `smoothSheafRing`, `smoothSheafCommRing`: The
  sheaf of smooth functions into a [Lie group]/[abelian Lie group]/[smooth ring]/[smooth commutative
  ring], as a sheaf of [groups]/[abelian groups]/[rings]/[commutative rings]
* `smoothSheafCommRing.forgetStalk`: Identify the stalk at a point of the sheaf-of-commutative-rings
  of functions from `M` to `R` (for `R` a smooth ring) with the stalk at that point of the
  corresponding sheaf of types.
* `smoothSheafCommRing.eval`: upgrade `smoothSheaf.eval` to a ring homomorphism when considering the
  sheaf of smooth functions into a smooth commutative ring
* `smoothSheafCommGroup.compLeft`: For a manifold `M` and a smooth homomorphism `φ` between
  abelian Lie groups `A`, `A'`, the 'postcomposition-by-`φ`' morphism of sheaves from
  `smoothSheafCommGroup IM I M A` to `smoothSheafCommGroup IM I' M A'`

## Main results

* `smoothSheaf.eval_surjective`: `smoothSheaf.eval` is surjective.
* `smoothSheafCommRing.eval_surjective`: `smoothSheafCommRing.eval` is surjective.

## TODO

There are variants of `smoothSheafCommGroup.compLeft` for `GrpCat`, `RingCat`, `CommRingCat`;
this is just boilerplate and can be added as needed.

Similarly, there are variants of `smoothSheafCommRing.forgetStalk` and `smoothSheafCommRing.eval`
for `GrpCat`, `CommGrpCat` and `RingCat` which can be added as needed.

Currently there is a universe restriction: one can consider the sheaf of smooth functions from `M`
to `N` only if `M` and `N` are in the same universe. For example, since `ℂ` is in `Type`, we can
only consider the structure sheaf of complex manifolds in `Type`, which is unsatisfactory. The
obstacle here is in the underlying category theory constructions, which are not sufficiently
universe polymorphic. A direct attempt to generalize the universes worked in Lean 3 but was
reverted because it was hard to port to Lean 4, see
https://github.com/leanprover-community/mathlib/pull/19230
The current (Oct 2023) proposal to permit these generalizations is to use the new `UnivLE`
typeclass, and some (but not all) of the underlying category theory constructions have now been
generalized by this method: see https://github.com/leanprover-community/mathlib4/pull/5724,
https://github.com/leanprover-community/mathlib4/pull/5726.
-/

@[expose] public section


noncomputable section
open TopologicalSpace Opposite
open scoped ContDiff

universe u

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  {HM : Type*} [TopologicalSpace HM] (IM : ModelWithCorners 𝕜 EM HM)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {H' : Type*} [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 E H')
  (M : Type u) [TopologicalSpace M] [ChartedSpace HM M]
  (N G A A' R : Type u) [TopologicalSpace N] [ChartedSpace H N]
  [TopologicalSpace G] [ChartedSpace H G] [TopologicalSpace A] [ChartedSpace H A]
  [TopologicalSpace A'] [ChartedSpace H' A'] [TopologicalSpace R] [ChartedSpace H R]
variable {EP : Type*} [NormedAddCommGroup EP] [NormedSpace 𝕜 EP]
  {HP : Type*} [TopologicalSpace HP] (IP : ModelWithCorners 𝕜 EP HP)
  (P : Type u) [TopologicalSpace P] [ChartedSpace HP P]

section TypeCat

/--
Definition of `smoothSheaf` / `smoothSheaf` 的定义

English:
definition smoothSheaf
  signature: : TopCat.Sheaf (Type u) (TopCat.of M)
  body: (contDiffWithinAt_localInvariantProp (I := IM) (I' := I) ∞).sheaf M N

中文:
定义 smoothSheaf
  签名: : TopCat.Sheaf (类型u) (TopCat.of M)
  定义体: (contDiffWithinAt_localInvariantProp (I := IM) (I' := I) ∞).sheaf M N

Depends on / 依赖: contDiffWithinAt_localInvariantProp
-/
def smoothSheaf : TopCat.Sheaf (Type u) (TopCat.of M) :=
  (contDiffWithinAt_localInvariantProp (I := IM) (I' := I) ∞).sheaf M N

variable {M}

/--
Instance `smoothSheaf.coeFun` / 实例 `smoothSheaf.coeFun`

English:
instance smoothSheaf.coeFun
  signature: (U : (Opens (TopCat.of M))ᵒᵖ)
  body: a.1

中文:
实例 smoothSheaf.coeFun
  签名: (U : (Opens (TopCat.of M))ᵒᵖ)
  定义体: a.1
-/
instance smoothSheaf.coeFun (U : (Opens (TopCat.of M))ᵒᵖ) :
    CoeFun ((smoothSheaf IM I M N).presheaf.obj U) (fun _ => ↑(unop U) -> N) where
  coe a := a.1

open Manifold in
/--
lemma `smoothSheaf.obj_eq` / 引理 `smoothSheaf.obj_eq`

English:
lemma smoothSheaf.obj_eq
  given: (U : (Opens (TopCat.of M))ᵒᵖ)
  proof: rfl

中文:
引理 smoothSheaf.obj_eq
  条件: (U : (Opens (TopCat.of M))ᵒᵖ)
  证明: rfl
-/
lemma smoothSheaf.obj_eq (U : (Opens (TopCat.of M))ᵒᵖ) :
    (smoothSheaf IM I M N).presheaf.obj U = C^∞⟮IM, (unop U : Opens M); I, N⟯ := rfl

/--
Definition of `smoothSheaf.eval` / `smoothSheaf.eval` 的定义

English:
definition smoothSheaf.eval
  signature: (x : M)
  body: TopCat.stalkToFiber (StructureGroupoid.LocalInvariantProp.localPredicate M N _) x

中文:
定义 smoothSheaf.eval
  签名: (x : M)
  定义体: TopCat.stalkToFiber (StructureGroupoid.LocalInvariantProp.localPredicate M N _) x

Depends on / 依赖: LocalInvariantProp, StructureGroupoid, StructureGroupoid.LocalInvariantProp.localPredicate, TopCat, TopCat.stalkToFiber, localPredicate, stalkToFiber
-/
def smoothSheaf.eval (x : M) : (smoothSheaf IM I M N).presheaf.stalk x -> N :=
  TopCat.stalkToFiber (StructureGroupoid.LocalInvariantProp.localPredicate M N _) x

/--
Definition of `smoothSheaf.evalHom` / `smoothSheaf.evalHom` 的定义

English:
definition smoothSheaf.evalHom
  signature: (x : TopCat.of M)
  body: TopCat.stalkToFiber (StructureGroupoid.LocalInvariantProp.localPredicate M N _) x

中文:
定义 smoothSheaf.evalHom
  签名: (x : TopCat.of M)
  定义体: TopCat.stalkToFiber (StructureGroupoid.LocalInvariantProp.localPredicate M N _) x

Depends on / 依赖: LocalInvariantProp, StructureGroupoid, StructureGroupoid.LocalInvariantProp.localPredicate, TopCat, TopCat.stalkToFiber, localPredicate, stalkToFiber
-/
def smoothSheaf.evalHom (x : TopCat.of M) :
    (smoothSheaf IM I M N).presheaf.stalk x ⟶ N :=
  TopCat.stalkToFiber (StructureGroupoid.LocalInvariantProp.localPredicate M N _) x

open CategoryTheory Limits

/--
Definition of `smoothSheaf.evalAt` / `smoothSheaf.evalAt` 的定义

English:
definition smoothSheaf.evalAt
  signature: (x : TopCat.of M) (U : OpenNhds x)
  body: i.1 ⟨x, U.2⟩

#adaptation_note

中文:
定义 smoothSheaf.evalAt
  签名: (x : TopCat.of M) (U : OpenNhds x)
  定义体: i.1 ⟨x, U.2⟩

#adaptation_note
-/
def smoothSheaf.evalAt (x : TopCat.of M) (U : OpenNhds x)
    (i : (smoothSheaf IM I M N).presheaf.obj (Opposite.op U.val)) : N :=
  i.1 ⟨x, U.2⟩

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `smoothSheaf.ι_evalHom` / 引理 `smoothSheaf.ι_evalHom`

English:
lemma smoothSheaf.ι_evalHom
  given: (x : TopCat.of M) (U)
  proof: colimit.ι_desc _ _

中文:
引理 smoothSheaf.ι_evalHom
  条件: (x : TopCat.of M) (U)
  证明: colimit.ι_desc _ _
-/
@[simp, reassoc, elementwise] lemma smoothSheaf.ι_evalHom (x : TopCat.of M) (U) :
    colimit.ι ((OpenNhds.inclusion x).op ⋙ (smoothSheaf IM I M N).obj) U ≫
    smoothSheaf.evalHom IM I N x =
    ↾(smoothSheaf.evalAt IM I N x (unop U)) :=
  colimit.ι_desc _ _

/--
lemma `smoothSheaf.eval_surjective` / 引理 `smoothSheaf.eval_surjective`

English:
lemma smoothSheaf.eval_surjective
  given: (x : M)
  statement: Function.Surjective (smoothSheaf.eval IM I N x)
  proof: by
  apply TopCat.stalkToFiber_surjective
  intro n
  exact ⟨⊤, fun _ => n, contMDiff_const, rfl⟩

中文:
引理 smoothSheaf.eval_surjective
  条件: (x : M)
  结论: Function.Surjective (smoothSheaf.eval IM I N x)
  证明: by
  apply TopCat.stalkToFiber_surjective
  intro n
  exact ⟨⊤, fun _ => n, contMDiff_const, rfl⟩

Depends on / 依赖: TopCat, TopCat.stalkToFiber_surjective, contMDiff_const, stalkToFiber_surjective
-/
lemma smoothSheaf.eval_surjective (x : M) : Function.Surjective (smoothSheaf.eval IM I N x) := by
  apply TopCat.stalkToFiber_surjective
  intro n
  exact ⟨⊤, fun _ => n, contMDiff_const, rfl⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nontrivial
  signature: N] (x
  body: (smoothSheaf.eval_surjective IM I N x).nontrivial

中文:
实例 [Nontrivial
  签名: N] (x
  定义体: (smoothSheaf.eval_surjective IM I N x).nontrivial

Depends on / 依赖: eval_surjective, nontrivial, smoothSheaf, smoothSheaf.eval_surjective
-/
instance [Nontrivial N] (x : M) : Nontrivial ((smoothSheaf IM I M N).presheaf.stalk x) :=
  (smoothSheaf.eval_surjective IM I N x).nontrivial

variable {IM I N}

/--
lemma `smoothSheaf.eval_germ` / 引理 `smoothSheaf.eval_germ`

English:
lemma smoothSheaf.eval_germ
  statement: (U : Opens M) (x : M) (hx : x in U)
  proof: TopCat.stalkToFiber_germ ((contDiffWithinAt_localInvariantProp ∞).localPredicate M N) _ _ _ _

中文:
引理 smoothSheaf.eval_germ
  结论: (U : Opens M) (x : M) (hx : x in U)
  证明: TopCat.stalkToFiber_germ ((contDiffWithinAt_localInvariantProp ∞).localPredicate M N) _ _ _ _
-/
@[simp] lemma smoothSheaf.eval_germ (U : Opens M) (x : M) (hx : x in U)
    (f : (smoothSheaf IM I M N).presheaf.obj (op U)) :
    smoothSheaf.eval IM I N (x : M) ((smoothSheaf IM I M N).presheaf.germ U x hx f) = f ⟨x, hx⟩ :=
  TopCat.stalkToFiber_germ ((contDiffWithinAt_localInvariantProp ∞).localPredicate M N) _ _ _ _

/--
lemma `smoothSheaf.contMDiff_section` / 引理 `smoothSheaf.contMDiff_section`

English:
lemma smoothSheaf.contMDiff_section
  statement: {U : (Opens (TopCat.of M))ᵒᵖ}
  proof: (contDiffWithinAt_localInvariantProp ∞).section_spec _ _ _ _

中文:
引理 smoothSheaf.contMDiff_section
  结论: {U : (Opens (TopCat.of M))ᵒᵖ}
  证明: (contDiffWithinAt_localInvariantProp ∞).section_spec _ _ _ _

Depends on / 依赖: contDiffWithinAt_localInvariantProp, section_spec
-/
lemma smoothSheaf.contMDiff_section {U : (Opens (TopCat.of M))ᵒᵖ}
    (f : (smoothSheaf IM I M N).presheaf.obj U) :
    ContMDiff IM I ∞ f :=
  (contDiffWithinAt_localInvariantProp ∞).section_spec _ _ _ _

set_option backward.isDefEq.respectTransparency.types false in
/-- A smooth function `f : M → N` induces a morphism of sheaves (of types) `𝒪_N ⟶ f_* 𝒪_M`
by pre-composing with `f`. -/
@[simps! -isSimp hom_app_hom]
/--
Definition of `ContMDiff.smoothSheafHom` / `ContMDiff.smoothSheafHom` 的定义

English:
definition ContMDiff.smoothSheafHom
  signature: (f : M -> P) (hf : ContMDiff IM IP ∞ f)
  body: ↾fun g => ⟨g ∘ Set.restrictPreimage _ f, by
    apply ContMDiff.comp (I' := IP) g.2
    rw [← ContMDiff.subtypeVal_comp_iff]
    exact hf.comp contMDiff_subtype_val⟩

@[deprecated (since := "2026-04-06")] alias ContMDiff.smoothSheafHom_hom_app_coe :=
  ContMDiff.smoothSheafHom_hom_app_hom

中文:
定义 ContMDiff.smoothSheafHom
  签名: (f : M -> P) (hf : ContMDiff IM IP ∞ f)
  定义体: ↾fun g => ⟨g ∘ Set.restrictPreimage _ f, by
    apply ContMDiff.comp (I' := IP) g.2
    rw [← ContMDiff.subtypeVal_comp_iff]
    exact hf.comp contMDiff_subtype_val⟩

@[deprecated (since := "2026-04-06")] alias ContMDiff.smoothSheafHom_hom_app_coe :=
  ContMDiff.smoothSheafHom_hom_app_hom

Depends on / 依赖: ContMDiff, ContMDiff.comp, ContMDiff.subtypeVal_comp_iff, Set.restrictPreimage, contMDiff_subtype_val, hf.comp, restrictPreimage, subtypeVal_comp_iff
-/
def ContMDiff.smoothSheafHom (f : M -> P) (hf : ContMDiff IM IP ∞ f) :
    smoothSheaf IP I P N ⟶ (TopCat.Sheaf.pushforward _ (TopCat.ofHom ⟨f, hf.continuous⟩)).obj
      (smoothSheaf IM I M N) where
  hom.app U := ↾fun g => ⟨g ∘ Set.restrictPreimage _ f, by
    apply ContMDiff.comp (I' := IP) g.2
    rw [← ContMDiff.subtypeVal_comp_iff]
    exact hf.comp contMDiff_subtype_val⟩

@[deprecated (since := "2026-04-06")] alias ContMDiff.smoothSheafHom_hom_app_coe :=
  ContMDiff.smoothSheafHom_hom_app_hom

end TypeCat

section LieGroup
variable [Group G] [LieGroup I ∞ G]

open Manifold in
@[to_additive]
noncomputable instance (U : (Opens (TopCat.of M))ᵒᵖ) :
    Group ((smoothSheaf IM I M G).presheaf.obj U) :=
inferInstanceAs Group C^∞⟮IM, (unop U : Opens M); I, G⟯

/-- The presheaf of smooth functions from `M` to `G`, for `G` a Lie group, as a presheaf of groups.
-/
@[to_additive /-- The presheaf of smooth functions from `M` to `G`, for `G` an additive Lie group,
as a presheaf of additive groups. -/]
/--
Definition of `smoothPresheafGroup` / `smoothPresheafGroup` 的定义

English:
definition smoothPresheafGroup
  signature: : TopCat.Presheaf GrpCat.{u} (TopCat.of M)
  body: { obj := fun U => GrpCat.of ((smoothSheaf IM I M G).presheaf.obj U)
map := fun h => GrpCat.ofHom
ContMDiffMap.restrictMonoidHom IM I G CategoryTheory.leOfHom h.unop
    map_id := fun _ => rfl
    map_comp := fun _ _ => rfl }

中文:
定义 smoothPresheafGroup
  签名: : TopCat.Presheaf GrpCat.{u} (TopCat.of M)
  定义体: { obj := fun U => GrpCat.of ((smoothSheaf IM I M G).presheaf.obj U)
map := fun h => GrpCat.ofHom
ContMDiffMap.restrictMonoidHom IM I G CategoryTheory.leOfHom h.unop
    map_id := fun _ => rfl
    map_comp := fun _ _ => rfl }

Depends on / 依赖: CategoryTheory, CategoryTheory.leOfHom, ContMDiffMap, ContMDiffMap.restrictMonoidHom, GrpCat, GrpCat.of, GrpCat.ofHom, h.unop, leOfHom, map_comp, map_id, presheaf, presheaf.obj, restrictMonoidHom, smoothSheaf
-/
noncomputable def smoothPresheafGroup : TopCat.Presheaf GrpCat.{u} (TopCat.of M) :=
  { obj := fun U => GrpCat.of ((smoothSheaf IM I M G).presheaf.obj U)
map := fun h => GrpCat.ofHom
ContMDiffMap.restrictMonoidHom IM I G CategoryTheory.leOfHom h.unop
    map_id := fun _ => rfl
    map_comp := fun _ _ => rfl }

/-- The sheaf of smooth functions from `M` to `G`, for `G` a Lie group, as a sheaf of
groups. -/
@[to_additive /-- The sheaf of smooth functions from `M` to `G`, for `G` an additive Lie group, as a
sheaf of additive groups. -/]
/--
Definition of `smoothSheafGroup` / `smoothSheafGroup` 的定义

English:
definition smoothSheafGroup
  signature: : TopCat.Sheaf GrpCat.{u} (TopCat.of M)
  body: { obj := smoothPresheafGroup IM I M G
    property := by
      rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _ (CategoryTheory.forget GrpCat)]
      exact (smoothSheaf IM I M G).property }

中文:
定义 smoothSheafGroup
  签名: : TopCat.Sheaf GrpCat.{u} (TopCat.of M)
  定义体: { obj := smoothPresheafGroup IM I M G
    property := by
      rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _ (CategoryTheory.forget GrpCat)]
      exact (smoothSheaf IM I M G).property }

Depends on / 依赖: CategoryTheory, CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget, CategoryTheory.forget, GrpCat, Presheaf, forget, isSheaf_iff_isSheaf_forget, property, smoothPresheafGroup, smoothSheaf
-/
noncomputable def smoothSheafGroup : TopCat.Sheaf GrpCat.{u} (TopCat.of M) :=
  { obj := smoothPresheafGroup IM I M G
    property := by
      rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _ (CategoryTheory.forget GrpCat)]
      exact (smoothSheaf IM I M G).property }

end LieGroup

section CommLieGroup
variable [CommGroup A] [CommGroup A'] [LieGroup I ∞ A] [LieGroup I' ∞ A']

open Manifold in
@[to_additive] noncomputable instance (U : (Opens (TopCat.of M))ᵒᵖ) :
    CommGroup ((smoothSheaf IM I M A).presheaf.obj U) :=
inferInstanceAs CommGroup C^∞⟮IM, (unop U : Opens M); I, A⟯

/-- The presheaf of smooth functions from `M` to `A`, for `A` an abelian Lie group, as a
presheaf of abelian groups. -/
@[to_additive /-- The presheaf of smooth functions from `M` to `A`, for `A` an additive abelian Lie
group, as a presheaf of additive abelian groups. -/]
/--
Definition of `smoothPresheafCommGroup` / `smoothPresheafCommGroup` 的定义

English:
definition smoothPresheafCommGroup
  signature: : TopCat.Presheaf CommGrpCat.{u} (TopCat.of M)
  body: { obj := fun U => CommGrpCat.of ((smoothSheaf IM I M A).presheaf.obj U)
map := fun h => CommGrpCat.ofHom
ContMDiffMap.restrictMonoidHom IM I A CategoryTheory.leOfHom h.unop
    map_id := fun _ => rfl
    map_comp := fun _ _ => rfl }

中文:
定义 smoothPresheafCommGroup
  签名: : TopCat.Presheaf CommGrpCat.{u} (TopCat.of M)
  定义体: { obj := fun U => CommGrpCat.of ((smoothSheaf IM I M A).presheaf.obj U)
map := fun h => CommGrpCat.ofHom
ContMDiffMap.restrictMonoidHom IM I A CategoryTheory.leOfHom h.unop
    map_id := fun _ => rfl
    map_comp := fun _ _ => rfl }

Depends on / 依赖: CategoryTheory, CategoryTheory.leOfHom, CommGrpCat, CommGrpCat.of, CommGrpCat.ofHom, ContMDiffMap, ContMDiffMap.restrictMonoidHom, h.unop, leOfHom, map_comp, map_id, presheaf, presheaf.obj, restrictMonoidHom, smoothSheaf
-/
noncomputable def smoothPresheafCommGroup : TopCat.Presheaf CommGrpCat.{u} (TopCat.of M) :=
  { obj := fun U => CommGrpCat.of ((smoothSheaf IM I M A).presheaf.obj U)
map := fun h => CommGrpCat.ofHom
ContMDiffMap.restrictMonoidHom IM I A CategoryTheory.leOfHom h.unop
    map_id := fun _ => rfl
    map_comp := fun _ _ => rfl }

/-- The sheaf of smooth functions from `M` to `A`, for `A` an abelian Lie group, as a
sheaf of abelian groups. -/
@[to_additive /-- The sheaf of smooth functions from `M` to
`A`, for `A` an abelian additive Lie group, as a sheaf of abelian additive groups. -/]
/--
Definition of `smoothSheafCommGroup` / `smoothSheafCommGroup` 的定义

English:
definition smoothSheafCommGroup
  signature: : TopCat.Sheaf CommGrpCat.{u} (TopCat.of M)
  body: { obj := smoothPresheafCommGroup IM I M A
    property := by
      rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _
        (CategoryTheory.forget CommGrpCat)]
      exact (smoothSheaf IM I M A).property }

中文:
定义 smoothSheafCommGroup
  签名: : TopCat.Sheaf CommGrpCat.{u} (TopCat.of M)
  定义体: { obj := smoothPresheafCommGroup IM I M A
    property := by
      rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _
        (CategoryTheory.forget CommGrpCat)]
      exact (smoothSheaf IM I M A).property }

Depends on / 依赖: CategoryTheory, CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget, CategoryTheory.forget, CommGrpCat, Presheaf, forget, isSheaf_iff_isSheaf_forget, property, smoothPresheafCommGroup, smoothSheaf
-/
noncomputable def smoothSheafCommGroup : TopCat.Sheaf CommGrpCat.{u} (TopCat.of M) :=
  { obj := smoothPresheafCommGroup IM I M A
    property := by
      rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _
        (CategoryTheory.forget CommGrpCat)]
      exact (smoothSheaf IM I M A).property }

open scoped Manifold in
/-- For a manifold `M` and a smooth homomorphism `φ` between abelian Lie groups `A`, `A'`, the
'left-composition-by-`φ`' morphism of sheaves from `smoothSheafCommGroup IM I M A` to
`smoothSheafCommGroup IM I' M A'`. -/
@[to_additive /-- For a manifold `M` and a smooth homomorphism `φ` between abelian additive Lie
groups `A`, `A'`, the 'left-composition-by-`φ`' morphism of sheaves from
`smoothSheafAddCommGroup IM I M A` to `smoothSheafAddCommGroup IM I' M A'`. -/]
/--
Definition of `smoothSheafCommGroup.compLeft` / `smoothSheafCommGroup.compLeft` 的定义

English:
definition smoothSheafCommGroup.compLeft
  signature: (φ : A ->* A') (hφ : CMDiff ∞ φ)
  body: CategoryTheory.ObjectProperty.homMk
  { app := fun _ => CommGrpCat.ofHom <| ContMDiffMap.compLeftMonoidHom _ _ φ hφ
    naturality := fun _ _ _ => rfl }

中文:
定义 smoothSheafCommGroup.compLeft
  签名: (φ : A ->* A') (hφ : CMDiff ∞ φ)
  定义体: CategoryTheory.ObjectProperty.homMk
  { app := fun _ => CommGrpCat.ofHom <| ContMDiffMap.compLeftMonoidHom _ _ φ hφ
    naturality := fun _ _ _ => rfl }

Depends on / 依赖: CategoryTheory, CategoryTheory.ObjectProperty.homMk, CommGrpCat, CommGrpCat.ofHom, ContMDiffMap, ContMDiffMap.compLeftMonoidHom, ObjectProperty, compLeftMonoidHom, naturality
-/
noncomputable def smoothSheafCommGroup.compLeft (φ : A ->* A') (hφ : CMDiff ∞ φ) :
    smoothSheafCommGroup IM I M A ⟶ smoothSheafCommGroup IM I' M A' :=
CategoryTheory.ObjectProperty.homMk
  { app := fun _ => CommGrpCat.ofHom <| ContMDiffMap.compLeftMonoidHom _ _ φ hφ
    naturality := fun _ _ _ => rfl }

end CommLieGroup

section ContMDiffRing
variable [Ring R] [ContMDiffRing I ∞ R]

open Manifold in
instance (U : (Opens (TopCat.of M))ᵒᵖ) : Ring ((smoothSheaf IM I M R).presheaf.obj U) :=
inferInstanceAs Ring C^∞⟮IM, (unop U : Opens M); I, R⟯

/--
Definition of `smoothPresheafRing` / `smoothPresheafRing` 的定义

English:
definition smoothPresheafRing
  signature: : TopCat.Presheaf RingCat.{u} (TopCat.of M)
  body: { obj := fun U => RingCat.of ((smoothSheaf IM I M R).presheaf.obj U)
map := fun h => RingCat.ofHom
ContMDiffMap.restrictRingHom IM I R CategoryTheory.leOfHom h.unop
    map_id := fun _ => rfl
    map_comp := fun _ _ => rfl }

中文:
定义 smoothPresheafRing
  签名: : TopCat.Presheaf RingCat.{u} (TopCat.of M)
  定义体: { obj := fun U => RingCat.of ((smoothSheaf IM I M R).presheaf.obj U)
map := fun h => RingCat.ofHom
ContMDiffMap.restrictRingHom IM I R CategoryTheory.leOfHom h.unop
    map_id := fun _ => rfl
    map_comp := fun _ _ => rfl }

Depends on / 依赖: CategoryTheory, CategoryTheory.leOfHom, ContMDiffMap, ContMDiffMap.restrictRingHom, RingCat, RingCat.of, RingCat.ofHom, h.unop, leOfHom, map_comp, map_id, presheaf, presheaf.obj, restrictRingHom, smoothSheaf
-/
def smoothPresheafRing : TopCat.Presheaf RingCat.{u} (TopCat.of M) :=
  { obj := fun U => RingCat.of ((smoothSheaf IM I M R).presheaf.obj U)
map := fun h => RingCat.ofHom
ContMDiffMap.restrictRingHom IM I R CategoryTheory.leOfHom h.unop
    map_id := fun _ => rfl
    map_comp := fun _ _ => rfl }

/--
Definition of `smoothSheafRing` / `smoothSheafRing` 的定义

English:
definition smoothSheafRing
  signature: : TopCat.Sheaf RingCat.{u} (TopCat.of M) where
  body: smoothPresheafRing IM I M R
  property := by
    rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _ (CategoryTheory.forget RingCat)]
    exact (smoothSheaf IM I M R).property

中文:
定义 smoothSheafRing
  签名: : TopCat.Sheaf RingCat.{u} (TopCat.of M) where
  定义体: smoothPresheafRing IM I M R
  property := by
    rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _ (CategoryTheory.forget RingCat)]
    exact (smoothSheaf IM I M R).property

Depends on / 依赖: smoothPresheafRing
-/
def smoothSheafRing : TopCat.Sheaf RingCat.{u} (TopCat.of M) where
  obj := smoothPresheafRing IM I M R
  property := by
    rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _ (CategoryTheory.forget RingCat)]
    exact (smoothSheaf IM I M R).property

end ContMDiffRing

section SmoothCommRing
variable [CommRing R] [ContMDiffRing I ∞ R]

open Manifold in
instance (U : (Opens (TopCat.of M))ᵒᵖ) : CommRing ((smoothSheaf IM I M R).presheaf.obj U) :=
inferInstanceAs CommRing C^∞⟮IM, (unop U : Opens M); I, R⟯

/--
Definition of `smoothPresheafCommRing` / `smoothPresheafCommRing` 的定义

English:
definition smoothPresheafCommRing
  signature: : TopCat.Presheaf CommRingCat.{u} (TopCat.of M)
  body: { obj := fun U => CommRingCat.of ((smoothSheaf IM I M R).presheaf.obj U)
map := fun h => CommRingCat.ofHom
ContMDiffMap.restrictRingHom IM I R CategoryTheory.leOfHom h.unop
    map_id := fun _ => rfl
    map_comp := fun _ _ => rfl }

中文:
定义 smoothPresheafCommRing
  签名: : TopCat.Presheaf CommRingCat.{u} (TopCat.of M)
  定义体: { obj := fun U => CommRingCat.of ((smoothSheaf IM I M R).presheaf.obj U)
map := fun h => CommRingCat.ofHom
ContMDiffMap.restrictRingHom IM I R CategoryTheory.leOfHom h.unop
    map_id := fun _ => rfl
    map_comp := fun _ _ => rfl }

Depends on / 依赖: CategoryTheory, CategoryTheory.leOfHom, CommRingCat, CommRingCat.of, CommRingCat.ofHom, ContMDiffMap, ContMDiffMap.restrictRingHom, h.unop, leOfHom, map_comp, map_id, presheaf, presheaf.obj, restrictRingHom, smoothSheaf
-/
def smoothPresheafCommRing : TopCat.Presheaf CommRingCat.{u} (TopCat.of M) :=
  { obj := fun U => CommRingCat.of ((smoothSheaf IM I M R).presheaf.obj U)
map := fun h => CommRingCat.ofHom
ContMDiffMap.restrictRingHom IM I R CategoryTheory.leOfHom h.unop
    map_id := fun _ => rfl
    map_comp := fun _ _ => rfl }

/-- The sheaf of smooth functions from `M` to `R`, for `R` a smooth commutative ring, as a sheaf of
commutative rings. -/
@[implicit_reducible]
/--
Definition of `smoothSheafCommRing` / `smoothSheafCommRing` 的定义

English:
definition smoothSheafCommRing
  signature: : TopCat.Sheaf CommRingCat.{u} (TopCat.of M) where
  body: smoothPresheafCommRing IM I M R
  property := by
    rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _
      (CategoryTheory.forget CommRingCat)]
    exact (smoothSheaf IM I M R).property

中文:
定义 smoothSheafCommRing
  签名: : TopCat.Sheaf CommRingCat.{u} (TopCat.of M) where
  定义体: smoothPresheafCommRing IM I M R
  property := by
    rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _
      (CategoryTheory.forget CommRingCat)]
    exact (smoothSheaf IM I M R).property

Depends on / 依赖: smoothPresheafCommRing
-/
def smoothSheafCommRing : TopCat.Sheaf CommRingCat.{u} (TopCat.of M) where
  obj := smoothPresheafCommRing IM I M R
  property := by
    rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _
      (CategoryTheory.forget CommRingCat)]
    exact (smoothSheaf IM I M R).property

-- sanity check: applying the `CommRingCat`-to-`Type` forgetful functor to the sheaf-of-rings of
-- smooth functions gives the sheaf-of-types of smooth functions.
example : (CategoryTheory.sheafCompose _ (CategoryTheory.forget CommRingCat.{u})).obj
    (smoothSheafCommRing IM I M R) = (smoothSheaf IM I M R) := rfl

/--
Instance `smoothSheafCommRing.coeFun` / 实例 `smoothSheafCommRing.coeFun`

English:
instance smoothSheafCommRing.coeFun
  signature: (U : (Opens (TopCat.of M))ᵒᵖ)
  body: a.1

中文:
实例 smoothSheafCommRing.coeFun
  签名: (U : (Opens (TopCat.of M))ᵒᵖ)
  定义体: a.1
-/
instance smoothSheafCommRing.coeFun (U : (Opens (TopCat.of M))ᵒᵖ) :
    CoeFun ((smoothSheafCommRing IM I M R).presheaf.obj U) (fun _ => ↑(unop U) -> R) where
  coe a := a.1

open CategoryTheory Limits

/--
Definition of `smoothSheafCommRing.forgetStalk` / `smoothSheafCommRing.forgetStalk` 的定义

English:
definition smoothSheafCommRing.forgetStalk
  signature: (x : TopCat.of M)
  body: preservesColimitIso (forget CommRingCat) _

中文:
定义 smoothSheafCommRing.forgetStalk
  签名: (x : TopCat.of M)
  定义体: preservesColimitIso (forget CommRingCat) _

Depends on / 依赖: CommRingCat, forget, preservesColimitIso
-/
def smoothSheafCommRing.forgetStalk (x : TopCat.of M) :
    ((smoothSheafCommRing IM I M R).presheaf.stalk x).carrier ≅
    (smoothSheaf IM I M R).presheaf.stalk x :=
  preservesColimitIso (forget CommRingCat) _

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `smoothSheafCommRing.ι_forgetStalk_hom` / 引理 `smoothSheafCommRing.ι_forgetStalk_hom`

English:
lemma smoothSheafCommRing.ι_forgetStalk_hom
  given: (x : TopCat.of M) (U)
  proof: ι_preservesColimitIso_hom (forget CommRingCat) _ _

中文:
引理 smoothSheafCommRing.ι_forgetStalk_hom
  条件: (x : TopCat.of M) (U)
  证明: ι_preservesColimitIso_hom (forget CommRingCat) _ _
-/
@[simp, reassoc, elementwise] lemma smoothSheafCommRing.ι_forgetStalk_hom (x : TopCat.of M) (U) :
    dsimp% ↾(colimit.ι ((OpenNhds.inclusion x).op ⋙
      (smoothSheafCommRing IM I M R).presheaf) U).hom ≫ (forgetStalk IM I M R x).hom =
    colimit.ι ((OpenNhds.inclusion x).op ⋙ (smoothSheaf IM I M R).presheaf) U :=
  ι_preservesColimitIso_hom (forget CommRingCat) _ _

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `smoothSheafCommRing.ι_forgetStalk_inv` / 引理 `smoothSheafCommRing.ι_forgetStalk_inv`

English:
lemma smoothSheafCommRing.ι_forgetStalk_inv
  given: (x : TopCat.of M) (U)
  proof: by
  dsimp
  rw [Iso.comp_inv_eq]; rw [← smoothSheafCommRing.ι_forgetStalk_hom]
  rfl

中文:
引理 smoothSheafCommRing.ι_forgetStalk_inv
  条件: (x : TopCat.of M) (U)
  证明: by
  dsimp
  rw [Iso.comp_inv_eq]; rw [← smoothSheafCommRing.ι_forgetStalk_hom]
  rfl
-/
@[simp, reassoc, elementwise] lemma smoothSheafCommRing.ι_forgetStalk_inv (x : TopCat.of M) (U) :
    colimit.ι ((OpenNhds.inclusion x).op ⋙ (smoothSheaf IM I M R).presheaf) U ≫
    (smoothSheafCommRing.forgetStalk IM I M R x).inv =
    ↾(colimit.ι ((OpenNhds.inclusion x).op ⋙
      (smoothSheafCommRing IM I M R).presheaf) U).hom := by
  dsimp
  rw [Iso.comp_inv_eq]; rw [← smoothSheafCommRing.ι_forgetStalk_hom]
  rfl

/--
Definition of `smoothSheafCommRing.evalAt` / `smoothSheafCommRing.evalAt` 的定义

English:
definition smoothSheafCommRing.evalAt
  signature: (x : TopCat.of M) (U : OpenNhds x)
  body: CommRingCat.ofHom (ContMDiffMap.evalRingHom ⟨x, U.2⟩)

中文:
定义 smoothSheafCommRing.evalAt
  签名: (x : TopCat.of M) (U : OpenNhds x)
  定义体: CommRingCat.ofHom (ContMDiffMap.evalRingHom ⟨x, U.2⟩)

Depends on / 依赖: CommRingCat, CommRingCat.ofHom, ContMDiffMap, ContMDiffMap.evalRingHom, evalRingHom
-/
def smoothSheafCommRing.evalAt (x : TopCat.of M) (U : OpenNhds x) :
    (smoothSheafCommRing IM I M R).presheaf.obj (Opposite.op U.1) ⟶ CommRingCat.of R :=
  CommRingCat.ofHom (ContMDiffMap.evalRingHom ⟨x, U.2⟩)

/--
Definition of `smoothSheafCommRing.evalHom` / `smoothSheafCommRing.evalHom` 的定义

English:
definition smoothSheafCommRing.evalHom
  signature: (x : TopCat.of M)
  body: by
  refine CategoryTheory.Limits.colimit.desc _ ⟨_, ⟨fun U => ?_, ?_⟩⟩
  · apply smoothSheafCommRing.evalAt
  · cat_disch

中文:
定义 smoothSheafCommRing.evalHom
  签名: (x : TopCat.of M)
  定义体: by
  refine CategoryTheory.Limits.colimit.desc _ ⟨_, ⟨fun U => ?_, ?_⟩⟩
  · apply smoothSheafCommRing.evalAt
  · cat_disch

Depends on / 依赖: CategoryTheory, CategoryTheory.Limits.colimit.desc, Finset, Finset.sum_const_zero, Finset.sum_sub_distrib, Limits, Pi.sub_apply, Pi.zero_apply, cat_disch, colimit, convert, evalAt, linearIndependent_iff, simp_rw, smoothSheafCommRing, smoothSheafCommRing.evalAt, sub_apply, sub_eq_zero, sub_smul, sum_const_zero
-/
def smoothSheafCommRing.evalHom (x : TopCat.of M) :
    (smoothSheafCommRing IM I M R).presheaf.stalk x ⟶ CommRingCat.of R := by
  refine CategoryTheory.Limits.colimit.desc _ ⟨_, ⟨fun U => ?_, ?_⟩⟩
  · apply smoothSheafCommRing.evalAt
  · cat_disch

/--
Definition of `smoothSheafCommRing.eval` / `smoothSheafCommRing.eval` 的定义

English:
definition smoothSheafCommRing.eval
  signature: (x : M)
  body: (smoothSheafCommRing.evalHom IM I M R x).hom

#adaptation_note

中文:
定义 smoothSheafCommRing.eval
  签名: (x : M)
  定义体: (smoothSheafCommRing.evalHom IM I M R x).hom

#adaptation_note

Depends on / 依赖: Finset, Finset.sum_extend_by_zero, classical, convert, evalHom, if_neg, if_pos, ite_smul, linearIndependent_iff, simp_rw, smoothSheafCommRing, smoothSheafCommRing.evalHom, sum_extend_by_zero, zero_smul
-/
def smoothSheafCommRing.eval (x : M) : (smoothSheafCommRing IM I M R).presheaf.stalk x ->+* R :=
  (smoothSheafCommRing.evalHom IM I M R x).hom

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `smoothSheafCommRing.ι_evalHom` / 引理 `smoothSheafCommRing.ι_evalHom`

English:
lemma smoothSheafCommRing.ι_evalHom
  given: (x : TopCat.of M) (U)
  proof: colimit.ι_desc _ _

中文:
引理 smoothSheafCommRing.ι_evalHom
  条件: (x : TopCat.of M) (U)
  证明: colimit.ι_desc _ _
-/
@[simp, reassoc, elementwise] lemma smoothSheafCommRing.ι_evalHom (x : TopCat.of M) (U) :
    colimit.ι ((OpenNhds.inclusion x).op ⋙ _) U ≫ smoothSheafCommRing.evalHom IM I M R x =
    smoothSheafCommRing.evalAt _ _ _ _ _ _ :=
  colimit.ι_desc _ _

/--
lemma `smoothSheafCommRing.evalHom_germ` / 引理 `smoothSheafCommRing.evalHom_germ`

English:
lemma smoothSheafCommRing.evalHom_germ
  statement: (U : Opens (TopCat.of M)) (x : M) (hx : x in U)
  proof: congr_arg (fun a => a f) smoothSheafCommRing.ι_evalHom IM I M R x ⟨U, hx⟩

中文:
引理 smoothSheafCommRing.evalHom_germ
  结论: (U : Opens (TopCat.of M)) (x : M) (hx : x in U)
  证明: congr_arg (fun a => a f) smoothSheafCommRing.ι_evalHom IM I M R x ⟨U, hx⟩
-/
@[simp] lemma smoothSheafCommRing.evalHom_germ (U : Opens (TopCat.of M)) (x : M) (hx : x in U)
    (f : (smoothSheafCommRing IM I M R).presheaf.obj (op U)) :
    smoothSheafCommRing.evalHom IM I M R (x : TopCat.of M)
      ((smoothSheafCommRing IM I M R).presheaf.germ U x hx f)
    = f ⟨x, hx⟩ :=
congr_arg (fun a => a f) smoothSheafCommRing.ι_evalHom IM I M R x ⟨U, hx⟩

set_option backward.isDefEq.respectTransparency false in
/--
lemma `smoothSheafCommRing.forgetStalk_inv_comp_eval` / 引理 `smoothSheafCommRing.forgetStalk_inv_comp_eval`

English:
lemma smoothSheafCommRing.forgetStalk_inv_comp_eval
  proof: by
  apply Limits.colimit.hom_ext
  intro U
  change (colimit.ι _ U) ≫ _ = colimit.ι ((OpenNhds.inclusion x).op ⋙ _) U ≫ _
  rw [smoothSheafCommRing.ι_forgetStalk_inv_assoc]; rw [smoothSheaf.ι_evalHom]
  ext x
  exact CategoryTheory.congr_fun (smoothSheafCommRing.ι_evalHom ..) x

中文:
引理 smoothSheafCommRing.forgetStalk_inv_comp_eval
  证明: by
  apply Limits.colimit.hom_ext
  intro U
  change (colimit.ι _ U) ≫ _ = colimit.ι ((OpenNhds.inclusion x).op ⋙ _) U ≫ _
  rw [smoothSheafCommRing.ι_forgetStalk_inv_assoc]; rw [smoothSheaf.ι_evalHom]
  ext x
  exact CategoryTheory.congr_fun (smoothSheafCommRing.ι_evalHom ..) x
-/
@[simp, reassoc, elementwise] lemma smoothSheafCommRing.forgetStalk_inv_comp_eval
    (x : TopCat.of M) :
    (smoothSheafCommRing.forgetStalk IM I M R x).inv ≫
      ↾(smoothSheafCommRing.evalHom IM I M R x).hom =
    smoothSheaf.evalHom _ _ _ _ := by
  apply Limits.colimit.hom_ext
  intro U
  change (colimit.ι _ U) ≫ _ = colimit.ι ((OpenNhds.inclusion x).op ⋙ _) U ≫ _
  rw [smoothSheafCommRing.ι_forgetStalk_inv_assoc]; rw [smoothSheaf.ι_evalHom]
  ext x
  exact CategoryTheory.congr_fun (smoothSheafCommRing.ι_evalHom ..) x

/--
lemma `smoothSheafCommRing.forgetStalk_hom_comp_evalHom` / 引理 `smoothSheafCommRing.forgetStalk_hom_comp_evalHom`

English:
lemma smoothSheafCommRing.forgetStalk_hom_comp_evalHom
  proof: by
  simp_rw [← CategoryTheory.Iso.eq_inv_comp]
  rw [← smoothSheafCommRing.forgetStalk_inv_comp_eval]

中文:
引理 smoothSheafCommRing.forgetStalk_hom_comp_evalHom
  证明: by
  simp_rw [← CategoryTheory.Iso.eq_inv_comp]
  rw [← smoothSheafCommRing.forgetStalk_inv_comp_eval]
-/
@[simp, reassoc, elementwise] lemma smoothSheafCommRing.forgetStalk_hom_comp_evalHom
    (x : TopCat.of M) :
    (smoothSheafCommRing.forgetStalk IM I M R x).hom ≫ (smoothSheaf.evalHom IM I R x) =
      ↾(smoothSheafCommRing.evalHom _ _ _ _ _) := by
  simp_rw [← CategoryTheory.Iso.eq_inv_comp]
  rw [← smoothSheafCommRing.forgetStalk_inv_comp_eval]

/--
lemma `smoothSheafCommRing.eval_surjective` / 引理 `smoothSheafCommRing.eval_surjective`

English:
lemma smoothSheafCommRing.eval_surjective
  given: (x)
  proof: by
  intro r
  obtain ⟨y, rfl⟩ := smoothSheaf.eval_surjective IM I R x r
  use (smoothSheafCommRing.forgetStalk IM I M R x).inv y
  apply smoothSheafCommRing.forgetStalk_inv_comp_eval_apply

中文:
引理 smoothSheafCommRing.eval_surjective
  条件: (x)
  证明: by
  intro r
  obtain ⟨y, rfl⟩ := smoothSheaf.eval_surjective IM I R x r
  use (smoothSheafCommRing.forgetStalk IM I M R x).inv y
  apply smoothSheafCommRing.forgetStalk_inv_comp_eval_apply

Depends on / 依赖: eval_surjective, forgetStalk, forgetStalk_inv_comp_eval_apply, smoothSheaf, smoothSheaf.eval_surjective, smoothSheafCommRing, smoothSheafCommRing.forgetStalk, smoothSheafCommRing.forgetStalk_inv_comp_eval_apply
-/
lemma smoothSheafCommRing.eval_surjective (x) :
    Function.Surjective (smoothSheafCommRing.eval IM I M R x) := by
  intro r
  obtain ⟨y, rfl⟩ := smoothSheaf.eval_surjective IM I R x r
  use (smoothSheafCommRing.forgetStalk IM I M R x).inv y
  apply smoothSheafCommRing.forgetStalk_inv_comp_eval_apply

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nontrivial
  signature: R] (x
  body: (smoothSheafCommRing.eval_surjective IM I M R x).nontrivial

中文:
实例 [Nontrivial
  签名: R] (x
  定义体: (smoothSheafCommRing.eval_surjective IM I M R x).nontrivial

Depends on / 依赖: eval_surjective, nontrivial, smoothSheafCommRing, smoothSheafCommRing.eval_surjective
-/
instance [Nontrivial R] (x : M) : Nontrivial ((smoothSheafCommRing IM I M R).presheaf.stalk x) :=
  (smoothSheafCommRing.eval_surjective IM I M R x).nontrivial

variable {IM I M R}

/--
lemma `smoothSheafCommRing.eval_germ` / 引理 `smoothSheafCommRing.eval_germ`

English:
lemma smoothSheafCommRing.eval_germ
  statement: (U : Opens M) (x : M) (hx : x in U)
  proof: smoothSheafCommRing.evalHom_germ IM I M R U x hx f

中文:
引理 smoothSheafCommRing.eval_germ
  结论: (U : Opens M) (x : M) (hx : x in U)
  证明: smoothSheafCommRing.evalHom_germ IM I M R U x hx f
-/
@[simp] lemma smoothSheafCommRing.eval_germ (U : Opens M) (x : M) (hx : x in U)
    (f : (smoothSheafCommRing IM I M R).presheaf.obj (op U)) :
    smoothSheafCommRing.eval IM I M R x ((smoothSheafCommRing IM I M R).presheaf.germ U x hx f)
    = f ⟨x, hx⟩ :=
  smoothSheafCommRing.evalHom_germ IM I M R U x hx f

set_option backward.isDefEq.respectTransparency.types false in
/-- A smooth function `f : M → N` induces a morphism of sheaves (of rings) `𝒪_N ⟶ f_* 𝒪_M`,
by pre-composing with `f`. -/
@[simps! -isSimp hom_app_hom_apply]
/--
Definition of `ContMDiff.smoothSheafCommRingHom` / `ContMDiff.smoothSheafCommRingHom` 的定义

English:
definition ContMDiff.smoothSheafCommRingHom
  signature: (f : M -> P) (hf : ContMDiff IM IP ∞ f)
  body: CommRingCat.ofHom
    { toFun := (hf.smoothSheafHom _ _ f).hom.app U
      map_one' := rfl
      map_mul' _ _ := rfl
      map_zero' := rfl
      map_add' _ _ := rfl }

中文:
定义 ContMDiff.smoothSheafCommRingHom
  签名: (f : M -> P) (hf : ContMDiff IM IP ∞ f)
  定义体: CommRingCat.ofHom
    { toFun := (hf.smoothSheafHom _ _ f).hom.app U
      map_one' := rfl
      map_mul' _ _ := rfl
      map_zero' := rfl
      map_add' _ _ := rfl }

Depends on / 依赖: CommRingCat, CommRingCat.ofHom
-/
def ContMDiff.smoothSheafCommRingHom (f : M -> P) (hf : ContMDiff IM IP ∞ f) :
    smoothSheafCommRing IP I P R ⟶
      (TopCat.Sheaf.pushforward _ (TopCat.ofHom ⟨f, hf.continuous⟩)).obj
        (smoothSheafCommRing IM I M R) where
  hom.app U := CommRingCat.ofHom
    { toFun := (hf.smoothSheafHom _ _ f).hom.app U
      map_one' := rfl
      map_mul' _ _ := rfl
      map_zero' := rfl
      map_add' _ _ := rfl }

end SmoothCommRing
