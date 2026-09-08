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
`Mathlib/Geometry/Manifold/Sheaf/Basic.lean`.  In this file we write that down (a one-liner), then
do the work of upgrading this to a sheaf of [groups]/[abelian groups]/[rings]/[commutative rings]
when `N` carries more algebraic structure.  For example, if `N` is `𝕜` then the sheaf of smooth
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
to `N` only if `M` and `N` are in the same universe.  For example, since `ℂ` is in `Type`, we can
only consider the structure sheaf of complex manifolds in `Type`, which is unsatisfactory. The
obstacle here is in the underlying category theory constructions, which are not sufficiently
universe polymorphic.  A direct attempt to generalize the universes worked in Lean 3 but was
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

/-- The sheaf of smooth functions from `M` to `N`, as a sheaf of types. -/
/-
**smoothSheaf** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：smoothSheaf : TopCat.Sheaf (Type u) (TopCat.of M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sheaf of smooth functions from `M` to `N`, as a sheaf of types.
-/
def smoothSheaf : TopCat.Sheaf (Type u) (TopCat.of M) :=
  (contDiffWithinAt_localInvariantProp (I := IM) (I' := I) ∞).sheaf M N

variable {M}
/-
**smoothSheaf.coeFun** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：smoothSheaf.coeFun (U : (Opens (TopCat.of M))ᵒᵖ) : CoeFun ((smoothSheaf IM
 I M N).presheaf.obj U) (fun _ => ↑(unop U) -> N) where coe a
参数：U : (Opens (TopCat.of M))ᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance smoothSheaf.coeFun (U : (Opens (TopCat.of M))ᵒᵖ) :
    CoeFun ((smoothSheaf IM I M N).presheaf.obj U) (fun _ ↦ ↑(unop U) → N) where
  coe a := a.1

open Manifold in
/-- The object of `smoothSheaf IM I M N` for the open set `U` in `M` is
`C^∞⟮IM, (unop U : Opens M); I, N⟯`, the `(IM, I)`-smooth functions from `U` to `N`.  This is not
just a "moral" equality but a literal and definitional equality! -/
/-
**smoothSheaf.obj_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smoothSheaf.obj_eq (U : (Opens (TopCat.of M))ᵒᵖ) : (smoothSheaf IM I M N).
presheaf.obj U = C^∞⟮IM, (unop U : Opens M); I, N⟯
参数：U : (Opens (TopCat.of M))ᵒᵖ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The object of `smoothSheaf IM I M N` for the open set `U` in `M` is
`C^∞⟮IM, (unop U : Opens M); I, N⟯`, the `(IM, I)`-smooth functions from `U` to 
`N`.  This is not
just a "moral" equality but a literal and definitional equality!
-/
lemma smoothSheaf.obj_eq (U : (Opens (TopCat.of M))ᵒᵖ) :
    (smoothSheaf IM I M N).presheaf.obj U = C^∞⟮IM, (unop U : Opens M); I, N⟯ := rfl

/-- Canonical map from the stalk of `smoothSheaf IM I M N` at `x` to `N`, given by evaluating
sections at `x`. -/
/-
**smoothSheaf.eval** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：smoothSheaf.eval (x : M) : (smoothSheaf IM I M N).presheaf.stalk x -> N
参数：x : M。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Types.hasColimitsOfSize`：∀ [UnivLE.{v, u}], Catego
ryTheory.Limits.HasColimitsOfSize.{w, v, u, u + 1} (Type u)

--- 原说明 ---
Canonical map from the stalk of `smoothSheaf IM I M N` at `x` to `N`, given by e
valuating
sections at `x`.
-/
def smoothSheaf.eval (x : M) : (smoothSheaf IM I M N).presheaf.stalk x → N :=
  TopCat.stalkToFiber (StructureGroupoid.LocalInvariantProp.localPredicate M N _) x

/-- Canonical map from the stalk of `smoothSheaf IM I M N` at `x` to `N`, given by evaluating
sections at `x`, considered as a morphism in the category of types. -/
/-
**smoothSheaf.evalHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：smoothSheaf.evalHom (x : TopCat.of M) : (smoothSheaf IM I M N).presheaf.st
alk x ⟶ N
参数：x : TopCat.of M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Canonical map from the stalk of `smoothSheaf IM I M N` at `x` to `N`, given by e
valuating
sections at `x`, considered as a morphism in the category of types.
-/
def smoothSheaf.evalHom (x : TopCat.of M) :
    (smoothSheaf IM I M N).presheaf.stalk x ⟶ N :=
  TopCat.stalkToFiber (StructureGroupoid.LocalInvariantProp.localPredicate M N _) x

open CategoryTheory Limits

/-- Given manifolds `M`, `N` and an open neighbourhood `U` of a point `x : M`, the evaluation-at-`x`
map to `N` from smooth functions from  `U` to `N`. -/
/-
**smoothSheaf.evalAt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：smoothSheaf.evalAt (x : TopCat.of M) (U : OpenNhds x) (i : (smoothSheaf IM
 I M N).presheaf.obj (Opposite.op U.val)) : N
参数：x : TopCat.of M；U : OpenNhds x；i : (smoothSheaf IM I M N).presheaf.obj (Oppos
ite.op U.val)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given manifolds `M`, `N` and an open neighbourhood `U` of a point `x : M`, the e
valuation-at-`x`
map to `N` from smooth functions from  `U` to `N`.
-/
def smoothSheaf.evalAt (x : TopCat.of M) (U : OpenNhds x)
    (i : (smoothSheaf IM I M N).presheaf.obj (Opposite.op U.val)) : N :=
  i.1 ⟨x, U.2⟩

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-
**smoothSheaf.** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
@[simp, reassoc, elementwise] lemma smoothSheaf.ι_evalHom (x : TopCat.of M) (U) :
    colimit.ι ((OpenNhds.inclusion x).op ⋙ (smoothSheaf IM I M N).obj) U ≫
    smoothSheaf.evalHom IM I N x =
    ↾(smoothSheaf.evalAt IM I N x (unop U))  :=
  colimit.ι_desc _ _

/-- The `eval` map is surjective at `x`. -/
/-
**smoothSheaf.eval_surjective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smoothSheaf.eval_surjective (x : M) : Function.Surjective (smoothSheaf.eva
l IM I N x)
参数：x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopCat.stalkToFiber_surjective`：stalkToFiber_surjective (P : LocalPredic
ate T) (x : X) (w : forall t : T x, exists (U : OpenNhds x) (f : forall y : U.1,
 T y) (_ : P.pred f)…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `contMDiff_const`：contMDiff_const : ContMDiff I I' n fun _ : M => c

--- 原说明 ---
The `eval` map is surjective at `x`.
-/
lemma smoothSheaf.eval_surjective (x : M) : Function.Surjective (smoothSheaf.eval IM I N x) := by
  apply TopCat.stalkToFiber_surjective
  intro n
  exact ⟨⊤, fun _ ↦ n, contMDiff_const, rfl⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nontrivial N] (x : M) : Nontrivial ((smoothSheaf IM I M N).presheaf.stalk x) :=
  (smoothSheaf.eval_surjective IM I N x).nontrivial

variable {IM I N}
/-
**smoothSheaf.eval_germ** 是 Mathlib 中的一个定理，位于命名空间 `smoothSheaf`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {EM : Type u_2} [inst_
1 : NormedAddCommGroup EM]   [inst_2 : NormedSpace 𝕜 EM] {HM : Type u_3} [inst_3
 : TopologicalSpace HM] {IM : ModelWithCorners 𝕜 EM HM}   {E : Type u_4} [inst_4
 : NormedAddCommGroup E] [inst_5 : NormedSpace 𝕜 E] {H : Type u_5} [inst_6 : Top
ologicalSpace H]   {I : ModelWithCorners 𝕜 E H} {M : Type u} [inst_7 : Topologic
alSpace M] [inst_8 : ChartedSpace HM M] {N : Type u}   [inst_9 : TopologicalSpac
e N] [inst_10 : ChartedSpace H N] (U : TopologicalSpace.Opens M) (x : M) (hx : x
 ∈ U)   (f : (smoothSheaf IM I M N).presheaf.obj (Opposite.op U)),   smoothSheaf
.eval IM I N x ((CategoryTheory.ConcreteCategory.hom ((smoothSheaf IM I M N).pre
sheaf.germ U x hx)) f) =     ↑f ⟨x, hx⟩
参数：U : TopologicalSpace.Opens M；x : M；hx : x ∈ U；f : (smoothSheaf IM I M N).pres
heaf.obj (Opposite.op U)；(CategoryTheory.ConcreteCategory.hom ((smoothSheaf IM I
 M N).presheaf.germ U x hx)) f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopCat.stalkToFiber_germ`：stalkToFiber_germ (P : LocalPredicate T) (U : 
Opens X) (x : X) (hx : x in U) (f) : stalkToFiber P x ((subsheafToTypes P).presh
eaf.germ U x h…
· 使用定理 `contDiffWithinAt_localInvariantProp`：contDiffWithinAt_localInvariantProp
 (n : Nat∞ω) : (contDiffGroupoid n I).LocalInvariantProp (contDiffGroupoid n I')
 (ContDiffWithinAtProp I …
-/
@[simp] lemma smoothSheaf.eval_germ (U : Opens M) (x : M) (hx : x ∈ U)
    (f : (smoothSheaf IM I M N).presheaf.obj (op U)) :
    smoothSheaf.eval IM I N (x : M) ((smoothSheaf IM I M N).presheaf.germ U x hx f) = f ⟨x, hx⟩ :=
  TopCat.stalkToFiber_germ ((contDiffWithinAt_localInvariantProp ∞).localPredicate M N) _ _ _ _
/-
**smoothSheaf.contMDiff_section** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smoothSheaf.contMDiff_section {U : (Opens (TopCat.of M))ᵒᵖ} (f : (smoothSh
eaf IM I M N).presheaf.obj U) : ContMDiff IM I ∞ f
参数：Opens (TopCat.of M)；f : (smoothSheaf IM I M N).presheaf.obj U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.LocalInvariantProp.section_spec`：StructureGroupoid.Loc
alInvariantProp.section_spec (hG : LocalInvariantProp G G' P) (U : (Opens (TopCa
t.of M))ᵒᵖ) (f : (hG.sheaf M M').obj.ob…
· 使用定理 `contDiffWithinAt_localInvariantProp`：contDiffWithinAt_localInvariantProp
 (n : Nat∞ω) : (contDiffGroupoid n I).LocalInvariantProp (contDiffGroupoid n I')
 (ContDiffWithinAtProp I …
-/
lemma smoothSheaf.contMDiff_section {U : (Opens (TopCat.of M))ᵒᵖ}
    (f : (smoothSheaf IM I M N).presheaf.obj U) :
    ContMDiff IM I ∞ f :=
  (contDiffWithinAt_localInvariantProp ∞).section_spec _ _ _ _

set_option backward.isDefEq.respectTransparency.types false in
/-- A smooth function `f : M → N` induces a morphism of sheaves (of types) `𝒪_N ⟶ f_* 𝒪_M`
by pre-composing with `f`. -/
@[simps! -isSimp hom_app_hom]
/-
**ContMDiff.smoothSheafHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ContMDiff.smoothSheafHom (f : M -> P) (hf : ContMDiff IM IP ∞ f) : smoothS
heaf IP I P N ⟶ (TopCat.Sheaf.pushforward _ (TopCat.ofHom ⟨f, hf.continuous⟩)).o
bj (smoothSheaf IM I M N) where hom.app U
参数：f : M -> P；hf : ContMDiff IM IP ∞ f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A smooth function `f : M → N` induces a morphism of sheaves (of types) `𝒪_N ⟶ f_
* 𝒪_M`
by pre-composing with `f`.
-/
def ContMDiff.smoothSheafHom (f : M → P) (hf : ContMDiff IM IP ∞ f) :
    smoothSheaf IP I P N ⟶ (TopCat.Sheaf.pushforward _ (TopCat.ofHom ⟨f, hf.continuous⟩)).obj
      (smoothSheaf IM I M N) where
  hom.app U := ↾fun g ↦ ⟨g ∘ Set.restrictPreimage _ f, by
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
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance (U : (Opens (TopCat.of M))ᵒᵖ) :
    Group ((smoothSheaf IM I M G).presheaf.obj U) :=
  inferInstanceAs <| Group C^∞⟮IM, (unop U : Opens M); I, G⟯

/-- The presheaf of smooth functions from `M` to `G`, for `G` a Lie group, as a presheaf of groups.
-/
@[to_additive /-- The presheaf of smooth functions from `M` to `G`, for `G` an additive Lie group,
as a presheaf of additive groups. -/]
/-
**smoothPresheafGroup** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：smoothPresheafGroup : TopCat.Presheaf GrpCat.{u} (TopCat.of M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def smoothPresheafGroup : TopCat.Presheaf GrpCat.{u} (TopCat.of M) :=
  { obj := fun U ↦ GrpCat.of ((smoothSheaf IM I M G).presheaf.obj U)
    map := fun h ↦ GrpCat.ofHom <|
      ContMDiffMap.restrictMonoidHom IM I G <| CategoryTheory.leOfHom h.unop
    map_id := fun _ ↦ rfl
    map_comp := fun _ _ ↦ rfl }

/-- The sheaf of smooth functions from `M` to `G`, for `G` a Lie group, as a sheaf of
groups. -/
@[to_additive /-- The sheaf of smooth functions from `M` to `G`, for `G` an additive Lie group, as a
sheaf of additive groups. -/]
/-
**smoothSheafGroup** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：smoothSheafGroup : TopCat.Sheaf GrpCat.{u} (TopCat.of M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] noncomputable instance (U : (Opens (TopCat.of M))ᵒᵖ) :
    CommGroup ((smoothSheaf IM I M A).presheaf.obj U) :=
  inferInstanceAs <| CommGroup C^∞⟮IM, (unop U : Opens M); I, A⟯

/-- The presheaf of smooth functions from `M` to `A`, for `A` an abelian Lie group, as a
presheaf of abelian groups. -/
@[to_additive /-- The presheaf of smooth functions from `M` to `A`, for `A` an additive abelian Lie
group, as a presheaf of additive abelian groups. -/]
/-
**smoothPresheafCommGroup** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：smoothPresheafCommGroup : TopCat.Presheaf CommGrpCat.{u} (TopCat.of M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def smoothPresheafCommGroup : TopCat.Presheaf CommGrpCat.{u} (TopCat.of M) :=
  { obj := fun U ↦ CommGrpCat.of ((smoothSheaf IM I M A).presheaf.obj U)
    map := fun h ↦ CommGrpCat.ofHom <|
      ContMDiffMap.restrictMonoidHom IM I A <| CategoryTheory.leOfHom h.unop
    map_id := fun _ ↦ rfl
    map_comp := fun _ _ ↦ rfl }

/-- The sheaf of smooth functions from `M` to `A`, for `A` an abelian Lie group, as a
sheaf of abelian groups. -/
@[to_additive /-- The sheaf of smooth functions from `M` to
`A`, for `A` an abelian additive Lie group, as a sheaf of abelian additive groups. -/]
/-
**smoothSheafCommGroup** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：smoothSheafCommGroup : TopCat.Sheaf CommGrpCat.{u} (TopCat.of M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**smoothSheafCommGroup.compLeft** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：smoothSheafCommGroup.compLeft (φ : A ->* A') (hφ : CMDiff ∞ φ) : smoothShe
afCommGroup IM I M A ⟶ smoothSheafCommGroup IM I' M A'
参数：φ : A ->* A'；hφ : CMDiff ∞ φ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def smoothSheafCommGroup.compLeft (φ : A →* A') (hφ : CMDiff ∞ φ) :
    smoothSheafCommGroup IM I M A ⟶ smoothSheafCommGroup IM I' M A' :=
  CategoryTheory.ObjectProperty.homMk <|
  { app := fun _ ↦ CommGrpCat.ofHom <| ContMDiffMap.compLeftMonoidHom _ _ φ hφ
    naturality := fun _ _ _ ↦ rfl }

end CommLieGroup

section ContMDiffRing
variable [Ring R] [ContMDiffRing I ∞ R]

open Manifold in
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (U : (Opens (TopCat.of M))ᵒᵖ) : Ring ((smoothSheaf IM I M R).presheaf.obj U) :=
  inferInstanceAs <| Ring C^∞⟮IM, (unop U : Opens M); I, R⟯

/-- The presheaf of smooth functions from `M` to `R`, for `R` a smooth ring, as a presheaf
of rings. -/
/-
**smoothPresheafRing** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：smoothPresheafRing : TopCat.Presheaf RingCat.{u} (TopCat.of M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The presheaf of smooth functions from `M` to `R`, for `R` a smooth ring, as a pr
esheaf
of rings.
-/
def smoothPresheafRing : TopCat.Presheaf RingCat.{u} (TopCat.of M) :=
  { obj := fun U ↦ RingCat.of ((smoothSheaf IM I M R).presheaf.obj U)
    map := fun h ↦ RingCat.ofHom <|
      ContMDiffMap.restrictRingHom IM I R <| CategoryTheory.leOfHom h.unop
    map_id := fun _ ↦ rfl
    map_comp := fun _ _ ↦ rfl }

/-- The sheaf of smooth functions from `M` to `R`, for `R` a smooth ring, as a sheaf of
rings. -/
/-
**smoothSheafRing** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：smoothSheafRing : TopCat.Sheaf RingCat.{u} (TopCat.of M) where obj
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sheaf of smooth functions from `M` to `R`, for `R` a smooth ring, as a sheaf
 of
rings.
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
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (U : (Opens (TopCat.of M))ᵒᵖ) : CommRing ((smoothSheaf IM I M R).presheaf.obj U) :=
  inferInstanceAs <| CommRing C^∞⟮IM, (unop U : Opens M); I, R⟯

/-- The presheaf of smooth functions from `M` to `R`, for `R` a smooth commutative ring, as a
presheaf of commutative rings. -/
/-
**smoothPresheafCommRing** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：smoothPresheafCommRing : TopCat.Presheaf CommRingCat.{u} (TopCat.of M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The presheaf of smooth functions from `M` to `R`, for `R` a smooth commutative r
ing, as a
presheaf of commutative rings.
-/
def smoothPresheafCommRing : TopCat.Presheaf CommRingCat.{u} (TopCat.of M) :=
  { obj := fun U ↦ CommRingCat.of ((smoothSheaf IM I M R).presheaf.obj U)
    map := fun h ↦ CommRingCat.ofHom <|
      ContMDiffMap.restrictRingHom IM I R <| CategoryTheory.leOfHom h.unop
    map_id := fun _ ↦ rfl
    map_comp := fun _ _ ↦ rfl }

/-- The sheaf of smooth functions from `M` to `R`, for `R` a smooth commutative ring, as a sheaf of
commutative rings. -/
@[implicit_reducible]
/-
**smoothSheafCommRing** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：smoothSheafCommRing : TopCat.Sheaf CommRingCat.{u} (TopCat.of M) where obj
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sheaf of smooth functions from `M` to `R`, for `R` a smooth commutative ring
, as a sheaf of
commutative rings.
-/
def smoothSheafCommRing : TopCat.Sheaf CommRingCat.{u} (TopCat.of M) where
  obj := smoothPresheafCommRing IM I M R
  property := by
    rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _
      (CategoryTheory.forget CommRingCat)]
    exact (smoothSheaf IM I M R).property

-- sanity check: applying the `CommRingCat`-to-`Type` forgetful functor to the sheaf-of-rings of
-- smooth functions gives the sheaf-of-types of smooth functions.
/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : (CategoryTheory.sheafCompose _ (CategoryTheory.forget CommRingCat.{u})).obj
    (smoothSheafCommRing IM I M R) = (smoothSheaf IM I M R) := rfl
/-
**smoothSheafCommRing.coeFun** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：smoothSheafCommRing.coeFun (U : (Opens (TopCat.of M))ᵒᵖ) : CoeFun ((smooth
SheafCommRing IM I M R).presheaf.obj U) (fun _ => ↑(unop U) -> R) where coe a
参数：U : (Opens (TopCat.of M))ᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance smoothSheafCommRing.coeFun (U : (Opens (TopCat.of M))ᵒᵖ) :
    CoeFun ((smoothSheafCommRing IM I M R).presheaf.obj U) (fun _ ↦ ↑(unop U) → R) where
  coe a := a.1

open CategoryTheory Limits

/-- Identify the stalk at a point of the sheaf-of-commutative-rings of functions from `M` to `R`
(for `R` a smooth ring) with the stalk at that point of the corresponding sheaf of types. -/
/-
**smoothSheafCommRing.forgetStalk** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：smoothSheafCommRing.forgetStalk (x : TopCat.of M) : ((smoothSheafCommRing 
IM I M R).presheaf.stalk x).carrier ≅ (smoothSheaf IM I M R).presheaf.stalk x
参数：x : TopCat.of M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Identify the stalk at a point of the sheaf-of-commutative-rings of functions fro
m `M` to `R`
(for `R` a smooth ring) with the stalk at that point of the corresponding sheaf 
of types.
-/
def smoothSheafCommRing.forgetStalk (x : TopCat.of M) :
    ((smoothSheafCommRing IM I M R).presheaf.stalk x).carrier ≅
    (smoothSheaf IM I M R).presheaf.stalk x :=
  preservesColimitIso (forget CommRingCat) _

set_option backward.isDefEq.respectTransparency.types false in
/-
**smoothSheafCommRing.** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, reassoc, elementwise] lemma smoothSheafCommRing.ι_forgetStalk_hom (x : TopCat.of M) (U) :
    dsimp% ↾(colimit.ι ((OpenNhds.inclusion x).op ⋙
      (smoothSheafCommRing IM I M R).presheaf) U).hom ≫ (forgetStalk IM I M R x).hom =
    colimit.ι ((OpenNhds.inclusion x).op ⋙ (smoothSheaf IM I M R).presheaf) U :=
  ι_preservesColimitIso_hom (forget CommRingCat) _ _

set_option backward.isDefEq.respectTransparency.types false in
/-
**smoothSheafCommRing.** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, reassoc, elementwise] lemma smoothSheafCommRing.ι_forgetStalk_inv (x : TopCat.of M) (U) :
    colimit.ι ((OpenNhds.inclusion x).op ⋙ (smoothSheaf IM I M R).presheaf) U ≫
    (smoothSheafCommRing.forgetStalk IM I M R x).inv =
    ↾(colimit.ι ((OpenNhds.inclusion x).op ⋙
      (smoothSheafCommRing IM I M R).presheaf) U).hom  := by
  dsimp
  rw [Iso.comp_inv_eq, ← smoothSheafCommRing.ι_forgetStalk_hom]
  rfl

/-- Given a smooth commutative ring `R` and a manifold `M`, and an open neighbourhood `U` of a point
`x : M`, the evaluation-at-`x` map to `R` from smooth functions from  `U` to `R`. -/
/-
**smoothSheafCommRing.evalAt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：smoothSheafCommRing.evalAt (x : TopCat.of M) (U : OpenNhds x) : (smoothShe
afCommRing IM I M R).presheaf.obj (Opposite.op U.1) ⟶ CommRingCat.of R
参数：x : TopCat.of M；U : OpenNhds x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a smooth commutative ring `R` and a manifold `M`, and an open neighbourhoo
d `U` of a point
`x : M`, the evaluation-at-`x` map to `R` from smooth functions from  `U` to `R`
.
-/
def smoothSheafCommRing.evalAt (x : TopCat.of M) (U : OpenNhds x) :
    (smoothSheafCommRing IM I M R).presheaf.obj (Opposite.op U.1) ⟶ CommRingCat.of R :=
  CommRingCat.ofHom (ContMDiffMap.evalRingHom ⟨x, U.2⟩)

/-- Canonical ring homomorphism from the stalk of `smoothSheafCommRing IM I M R` at `x` to `R`,
given by evaluating sections at `x`, considered as a morphism in the category of commutative rings.
-/
/-
**smoothSheafCommRing.evalHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：smoothSheafCommRing.evalHom (x : TopCat.of M) : (smoothSheafCommRing IM I 
M R).presheaf.stalk x ⟶ CommRingCat.of R
参数：x : TopCat.of M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Canonical ring homomorphism from the stalk of `smoothSheafCommRing IM I M R` at 
`x` to `R`,
given by evaluating sections at `x`, considered as a morphism in the category of
 commutative rings.
-/
def smoothSheafCommRing.evalHom (x : TopCat.of M) :
    (smoothSheafCommRing IM I M R).presheaf.stalk x ⟶ CommRingCat.of R := by
  refine CategoryTheory.Limits.colimit.desc _ ⟨_, ⟨fun U ↦ ?_, ?_⟩⟩
  · apply smoothSheafCommRing.evalAt
  · cat_disch

/-- Canonical ring homomorphism from the stalk of `smoothSheafCommRing IM I M R` at `x` to `R`,
given by evaluating sections at `x`. -/
/-
**smoothSheafCommRing.eval** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：smoothSheafCommRing.eval (x : M) : (smoothSheafCommRing IM I M R).presheaf
.stalk x ->+* R
参数：x : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Canonical ring homomorphism from the stalk of `smoothSheafCommRing IM I M R` at 
`x` to `R`,
given by evaluating sections at `x`.
-/
def smoothSheafCommRing.eval (x : M) : (smoothSheafCommRing IM I M R).presheaf.stalk x →+* R :=
  (smoothSheafCommRing.evalHom IM I M R x).hom

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-
**smoothSheafCommRing.** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
@[simp, reassoc, elementwise] lemma smoothSheafCommRing.ι_evalHom (x : TopCat.of M) (U) :
    colimit.ι ((OpenNhds.inclusion x).op ⋙ _) U ≫ smoothSheafCommRing.evalHom IM I M R x =
    smoothSheafCommRing.evalAt _ _ _ _ _ _ :=
  colimit.ι_desc _ _
/-
**smoothSheafCommRing.evalHom_germ** 是 Mathlib 中的一个定理，位于命名空间 `smoothSheafCommRin
g`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {EM : Type u_2} [inst_
1 : NormedAddCommGroup EM]   [inst_2 : NormedSpace 𝕜 EM] {HM : Type u_3} [inst_3
 : TopologicalSpace HM] (IM : ModelWithCorners 𝕜 EM HM)   {E : Type u_4} [inst_4
 : NormedAddCommGroup E] [inst_5 : NormedSpace 𝕜 E] {H : Type u_5} [inst_6 : Top
ologicalSpace H]   (I : ModelWithCorners 𝕜 E H) (M : Type u) [inst_7 : Topologic
alSpace M] [inst_8 : ChartedSpace HM M] (R : Type u)   [inst_9 : TopologicalSpac
e R] [inst_10 : ChartedSpace H R] [inst_11 : CommRing R] [inst_12 : ContMDiffRin
g I (↑⊤) R]   (U : TopologicalSpace.Opens ↑(TopCat.of M)) (x : M) (hx : x ∈ U)  
 (f : ↑((smoothSheafCommRing IM I M R).presheaf.obj (Opposite.op U))),   (Catego
ryTheory.ConcreteCategory.hom (smoothSheafCommRing.evalHom IM I M R x))       ((
CategoryTheory.ConcreteCategory.hom ((smoothSheafCommRing IM I M R).presheaf.ger
m U x hx)) f) =     ↑f ⟨x, hx⟩
参数：IM : ModelWithCorners 𝕜 EM HM；I : ModelWithCorners 𝕜 E H；M : Type u；R : Type 
u；↑⊤；U : TopologicalSpace.Opens ↑(TopCat.of M)；x : M；hx : x ∈ U；f : ↑((smoothShe
afCommRing IM I M R).presheaf.obj (Opposite.op U))；CategoryTheory.ConcreteCatego
ry.hom (smoothSheafCommRing.evalHom IM I M R x)；(CategoryTheory.ConcreteCategory
.hom ((smoothSheafCommRing IM I M R).presheaf.germ U x hx)) f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `smoothSheafCommRing.ι_evalHom`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {EM : Type u_2} [inst_1 : NormedAddCommGroup EM]   [inst_2 : NormedSp
ace 𝕜 EM] {HM : Typ…
-/
@[simp] lemma smoothSheafCommRing.evalHom_germ (U : Opens (TopCat.of M)) (x : M) (hx : x ∈ U)
    (f : (smoothSheafCommRing IM I M R).presheaf.obj (op U)) :
    smoothSheafCommRing.evalHom IM I M R (x : TopCat.of M)
      ((smoothSheafCommRing IM I M R).presheaf.germ U x hx f)
    = f ⟨x, hx⟩ :=
  congr_arg (fun a ↦ a f) <| smoothSheafCommRing.ι_evalHom IM I M R x ⟨U, hx⟩

set_option backward.isDefEq.respectTransparency false in
/-
**smoothSheafCommRing.forgetStalk_inv_comp_eval** 是 Mathlib 中的一个定理，位于命名空间 `smoot
hSheafCommRing`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {EM : Type u_2} [inst_
1 : NormedAddCommGroup EM]   [inst_2 : NormedSpace 𝕜 EM] {HM : Type u_3} [inst_3
 : TopologicalSpace HM] (IM : ModelWithCorners 𝕜 EM HM)   {E : Type u_4} [inst_4
 : NormedAddCommGroup E] [inst_5 : NormedSpace 𝕜 E] {H : Type u_5} [inst_6 : Top
ologicalSpace H]   (I : ModelWithCorners 𝕜 E H) (M : Type u) [inst_7 : Topologic
alSpace M] [inst_8 : ChartedSpace HM M] (R : Type u)   [inst_9 : TopologicalSpac
e R] [inst_10 : ChartedSpace H R] [inst_11 : CommRing R] [inst_12 : ContMDiffRin
g I (↑⊤) R]   (x : ↑(TopCat.of M)),   CategoryTheory.CategoryStruct.comp (smooth
SheafCommRing.forgetStalk IM I M R x).inv       (TypeCat.ofHom ⇑(CommRingCat.Hom
.hom (smoothSheafCommRing.evalHom IM I M R x))) =     smoothSheaf.evalHom IM I R
 x
参数：IM : ModelWithCorners 𝕜 EM HM；I : ModelWithCorners 𝕜 E H；M : Type u；R : Type 
u；↑⊤；x : ↑(TopCat.of M)；smoothSheafCommRing.forgetStalk IM I M R x；TypeCat.ofHom
 ⇑(CommRingCat.Hom.hom (smoothSheafCommRing.evalHom IM I M R x))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.colimit.hom_ext`：∀ {J : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u}
 C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.Types.hasColimitsOfSize`：∀ [UnivLE.{v, u}], Catego
ryTheory.Limits.HasColimitsOfSize.{w, v, u, u + 1} (Type u)
· 使用定理 `CategoryTheory.Limits.instHasColimitsOfShapeOfHasColimitsOfSize`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : Catego
ryTheory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `smoothSheafCommRing.ι_forgetStalk_inv_assoc`：∀ {𝕜 : Type u_1} [inst : No
ntriviallyNormedField 𝕜] {EM : Type u_2} [inst_1 : NormedAddCommGroup EM]   [ins
t_2 : NormedSpace 𝕜 EM] {HM : Typ…
· 使用定理 `smoothSheaf.ι_evalHom`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {EM : Type u_2} [inst_1 : NormedAddCommGroup EM]   [inst_2 : NormedSpace 𝕜 EM
] {HM : Typ…
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `TypeCat.Fun.ext`：∀ {X : Type u_1} {Y : Type u_2} {x y : TypeCat.Fun X Y}
, x.toFun = y.toFun → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.congr_fun`：∀ {C : Type u_1} [inst : CategoryTheory.Catego
ry.{v_1, u_1} C] {FC : outParam (C → C → Type u_2)}   {CC : outParam (C → Type w
)} [inst_1 : o…
· 使用定理 `smoothSheafCommRing.ι_evalHom`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {EM : Type u_2} [inst_1 : NormedAddCommGroup EM]   [inst_2 : NormedSp
ace 𝕜 EM] {HM : Typ…
-/
@[simp, reassoc, elementwise] lemma smoothSheafCommRing.forgetStalk_inv_comp_eval
    (x : TopCat.of M) :
    (smoothSheafCommRing.forgetStalk IM I M R x).inv ≫
      ↾(smoothSheafCommRing.evalHom IM I M R x).hom =
    smoothSheaf.evalHom _ _ _ _ := by
  apply Limits.colimit.hom_ext
  intro U
  change (colimit.ι _ U) ≫ _ = colimit.ι ((OpenNhds.inclusion x).op ⋙ _) U ≫ _
  rw [smoothSheafCommRing.ι_forgetStalk_inv_assoc, smoothSheaf.ι_evalHom]
  ext x
  exact CategoryTheory.congr_fun (smoothSheafCommRing.ι_evalHom ..) x
/-
**smoothSheafCommRing.forgetStalk_hom_comp_evalHom** 是 Mathlib 中的一个定理，位于命名空间 `sm
oothSheafCommRing`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {EM : Type u_2} [inst_
1 : NormedAddCommGroup EM]   [inst_2 : NormedSpace 𝕜 EM] {HM : Type u_3} [inst_3
 : TopologicalSpace HM] (IM : ModelWithCorners 𝕜 EM HM)   {E : Type u_4} [inst_4
 : NormedAddCommGroup E] [inst_5 : NormedSpace 𝕜 E] {H : Type u_5} [inst_6 : Top
ologicalSpace H]   (I : ModelWithCorners 𝕜 E H) (M : Type u) [inst_7 : Topologic
alSpace M] [inst_8 : ChartedSpace HM M] (R : Type u)   [inst_9 : TopologicalSpac
e R] [inst_10 : ChartedSpace H R] [inst_11 : CommRing R] [inst_12 : ContMDiffRin
g I (↑⊤) R]   (x : ↑(TopCat.of M)),   CategoryTheory.CategoryStruct.comp (smooth
SheafCommRing.forgetStalk IM I M R x).hom (smoothSheaf.evalHom IM I R x) =     T
ypeCat.ofHom ⇑(CategoryTheory.ConcreteCategory.hom (smoothSheafCommRing.evalHom 
IM I M R x))
参数：IM : ModelWithCorners 𝕜 EM HM；I : ModelWithCorners 𝕜 E H；M : Type u；R : Type 
u；↑⊤；x : ↑(TopCat.of M)；smoothSheafCommRing.forgetStalk IM I M R x；smoothSheaf.e
valHom IM I R x；CategoryTheory.ConcreteCategory.hom (smoothSheafCommRing.evalHom
 IM I M R x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Types.hasColimitsOfSize`：∀ [UnivLE.{v, u}], Catego
ryTheory.Limits.HasColimitsOfSize.{w, v, u, u + 1} (Type u)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `smoothSheafCommRing.forgetStalk_inv_comp_eval`：∀ {𝕜 : Type u_1} [inst : 
NontriviallyNormedField 𝕜] {EM : Type u_2} [inst_1 : NormedAddCommGroup EM]   [i
nst_2 : NormedSpace 𝕜 EM] {HM : Typ…
-/
@[simp, reassoc, elementwise] lemma smoothSheafCommRing.forgetStalk_hom_comp_evalHom
    (x : TopCat.of M) :
    (smoothSheafCommRing.forgetStalk IM I M R x).hom ≫ (smoothSheaf.evalHom IM I R x) =
      ↾(smoothSheafCommRing.evalHom _ _ _ _ _) := by
  simp_rw [← CategoryTheory.Iso.eq_inv_comp]
  rw [← smoothSheafCommRing.forgetStalk_inv_comp_eval]
/-
**smoothSheafCommRing.eval_surjective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smoothSheafCommRing.eval_surjective (x) : Function.Surjective (smoothSheaf
CommRing.eval IM I M R x)
参数：x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Types.hasColimitsOfSize`：∀ [UnivLE.{v, u}], Catego
ryTheory.Limits.HasColimitsOfSize.{w, v, u, u + 1} (Type u)
· 使用引理 `smoothSheaf.eval_surjective`：smoothSheaf.eval_surjective (x : M) : Funct
ion.Surjective (smoothSheaf.eval IM I N x)
· 使用定理 `smoothSheafCommRing.forgetStalk_inv_comp_eval_apply`：∀ {𝕜 : Type u_1} [i
nst : NontriviallyNormedField 𝕜] {EM : Type u_2} [inst_1 : NormedAddCommGroup EM
]   [inst_2 : NormedSpace 𝕜 EM] {HM : Typ…
-/
lemma smoothSheafCommRing.eval_surjective (x) :
    Function.Surjective (smoothSheafCommRing.eval IM I M R x) := by
  intro r
  obtain ⟨y, rfl⟩ := smoothSheaf.eval_surjective IM I R x r
  use (smoothSheafCommRing.forgetStalk IM I M R x).inv y
  apply smoothSheafCommRing.forgetStalk_inv_comp_eval_apply
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nontrivial R] (x : M) : Nontrivial ((smoothSheafCommRing IM I M R).presheaf.stalk x) :=
  (smoothSheafCommRing.eval_surjective IM I M R x).nontrivial

variable {IM I M R}
/-
**smoothSheafCommRing.eval_germ** 是 Mathlib 中的一个定理，位于命名空间 `smoothSheafCommRing`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {EM : Type u_2} [inst_
1 : NormedAddCommGroup EM]   [inst_2 : NormedSpace 𝕜 EM] {HM : Type u_3} [inst_3
 : TopologicalSpace HM] {IM : ModelWithCorners 𝕜 EM HM}   {E : Type u_4} [inst_4
 : NormedAddCommGroup E] [inst_5 : NormedSpace 𝕜 E] {H : Type u_5} [inst_6 : Top
ologicalSpace H]   {I : ModelWithCorners 𝕜 E H} {M : Type u} [inst_7 : Topologic
alSpace M] [inst_8 : ChartedSpace HM M] {R : Type u}   [inst_9 : TopologicalSpac
e R] [inst_10 : ChartedSpace H R] [inst_11 : CommRing R] [inst_12 : ContMDiffRin
g I (↑⊤) R]   (U : TopologicalSpace.Opens M) (x : M) (hx : x ∈ U)   (f : ↑((smoo
thSheafCommRing IM I M R).presheaf.obj (Opposite.op U))),   (smoothSheafCommRing
.eval IM I M R x)       ((CategoryTheory.ConcreteCategory.hom ((smoothSheafCommR
ing IM I M R).presheaf.germ U x hx)) f) =     ↑f ⟨x, hx⟩
参数：↑⊤；U : TopologicalSpace.Opens M；x : M；hx : x ∈ U；f : ↑((smoothSheafCommRing I
M I M R).presheaf.obj (Opposite.op U))；smoothSheafCommRing.eval IM I M R x；(Cate
goryTheory.ConcreteCategory.hom ((smoothSheafCommRing IM I M R).presheaf.germ U 
x hx)) f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `smoothSheafCommRing.evalHom_germ`：∀ {𝕜 : Type u_1} [inst : NontriviallyN
ormedField 𝕜] {EM : Type u_2} [inst_1 : NormedAddCommGroup EM]   [inst_2 : Norme
dSpace 𝕜 EM] {HM : Typ…
-/
@[simp] lemma smoothSheafCommRing.eval_germ (U : Opens M) (x : M) (hx : x ∈ U)
    (f : (smoothSheafCommRing IM I M R).presheaf.obj (op U)) :
    smoothSheafCommRing.eval IM I M R x ((smoothSheafCommRing IM I M R).presheaf.germ U x hx f)
    = f ⟨x, hx⟩ :=
  smoothSheafCommRing.evalHom_germ IM I M R U x hx f

set_option backward.isDefEq.respectTransparency.types false in
/-- A smooth function `f : M → N` induces a morphism of sheaves (of rings) `𝒪_N ⟶ f_* 𝒪_M`,
by pre-composing with `f`. -/
@[simps! -isSimp hom_app_hom_apply]
/-
**ContMDiff.smoothSheafCommRingHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ContMDiff.smoothSheafCommRingHom (f : M -> P) (hf : ContMDiff IM IP ∞ f) :
 smoothSheafCommRing IP I P R ⟶ (TopCat.Sheaf.pushforward _ (TopCat.ofHom ⟨f, hf
.continuous⟩)).obj (smoothSheafCommRing IM I M R) where hom.app U
参数：f : M -> P；hf : ContMDiff IM IP ∞ f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A smooth function `f : M → N` induces a morphism of sheaves (of rings) `𝒪_N ⟶ f_
* 𝒪_M`,
by pre-composing with `f`.
-/
def ContMDiff.smoothSheafCommRingHom (f : M → P) (hf : ContMDiff IM IP ∞ f) :
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

