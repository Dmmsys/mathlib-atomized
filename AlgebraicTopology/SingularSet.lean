/-
Copyright (c) 2023 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kim Morrison, Adam Topaz
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.AlgebraicTopology.TopologicalSimplex
public import Mathlib.CategoryTheory.Limits.Presheaf
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.Category.TopCat.ULift

/-!
# The singular simplicial set of a topological space and geometric realization of a simplicial set

The *singular simplicial set* `TopCat.toSSet.obj X` of a topological space `X`
has `n`-simplices which identify to continuous maps `stdSimplex ℝ (Fin (n + 1)) → X`,
where `stdSimplex ℝ (Fin (n + 1))` is the standard topological `n`-simplex,
defined as the subtype of `Fin (n + 1) → ℝ` consisting of functions `f`
such that `0 ≤ f i` for all `i` and `∑ i, f i = 1`.

The *geometric realization* functor `SSet.toTop` is left adjoint to `TopCat.toSSet`.
It is the left Kan extension of `SimplexCategory.toTop` along the Yoneda embedding.

## Main definitions

* `TopCat.toSSet : TopCat ⥤ SSet` is the functor
  assigning the singular simplicial set to a topological space.
* `SSet.toTop : SSet ⥤ TopCat` is the functor
  assigning the geometric realization to a simplicial set.
* `sSetTopAdj : SSet.toTop ⊣ TopCat.toSSet` is the adjunction between these two functors.

## TODO (@joelriou)

- Show that the singular simplicial set is a Kan complex.
- Show the adjunction `sSetTopAdj` is a Quillen equivalence.

-/

@[expose] public section

universe u

open CategoryTheory

/--
Definition of `TopCat.toSSet` / `TopCat.toSSet` 的定义

English:
definition TopCat.toSSet
  signature: : TopCat.{u} ⥤ SSet.{u}
  body: Presheaf.restrictedULiftYoneda.{0} SimplexCategory.toTop.{u}

中文:
定义 顶元素范畴.toSSet
  签名: : 顶元素范畴.{u} ⥤ SSet.{u}
  定义体: Presheaf.restrictedULiftYoneda.{0} SimplexCategory.toTop.{u}

Depends on / 依赖: Presheaf, Presheaf.restrictedULiftYoneda, SimplexCategory, SimplexCategory.toTop, restrictedULiftYoneda
-/
noncomputable def TopCat.toSSet : TopCat.{u} ⥤ SSet.{u} :=
  Presheaf.restrictedULiftYoneda.{0} SimplexCategory.toTop.{u}

/--
Definition of `TopCat.toSSetObjEquiv` / `TopCat.toSSetObjEquiv` 的定义

English:
definition TopCat.toSSetObjEquiv
  signature: (X : TopCat.{u}) (n : SimplexCategoryᵒᵖ)
  body: Equiv.ulift.{0}.trans (ConcreteCategory.homEquiv.trans
    (Homeomorph.ulift.continuousMapCongr (.refl _)))

中文:
定义 顶元素范畴.toSSetObjEquiv
  签名: (X : 顶元素范畴.{u}) (n : SimplexCategoryᵒᵖ)
  定义体: Equiv.ulift.{0}.trans (ConcreteCategory.homEquiv.trans
    (Homeomorph.ulift.continuousMapCongr (.refl _)))

Depends on / 依赖: ConcreteCategory, ConcreteCategory.homEquiv.trans, Equiv.ulift, Homeomorph, Homeomorph.ulift.continuousMapCongr, continuousMapCongr, homEquiv
-/
noncomputable def TopCat.toSSetObjEquiv (X : TopCat.{u}) (n : SimplexCategoryᵒᵖ) :
    (toSSet.obj X).obj n ≃ C(stdSimplex Real (Fin (n.unop.len + 1)), X) :=
  Equiv.ulift.{0}.trans (ConcreteCategory.homEquiv.trans
    (Homeomorph.ulift.continuousMapCongr (.refl _)))

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `SSet.toTop` / `SSet.toTop` 的定义

English:
definition SSet.toTop
  signature: : SSet.{u} ⥤ TopCat.{u}
  body: stdSimplex.{u}.leftKanExtension SimplexCategory.toTop

中文:
定义 SSet.toTop
  签名: : SSet.{u} ⥤ 顶元素范畴.{u}
  定义体: stdSimplex.{u}.leftKanExtension SimplexCategory.toTop

Depends on / 依赖: SimplexCategory, SimplexCategory.toTop, leftKanExtension, stdSimplex
-/
noncomputable def SSet.toTop : SSet.{u} ⥤ TopCat.{u} :=
  stdSimplex.{u}.leftKanExtension SimplexCategory.toTop

/-- The geometric realization of a simplicial set. -/
scoped[Simplicial] notation "|" X "|" => SSet.toTop.obj X

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `sSetTopAdj` / `sSetTopAdj` 的定义

English:
definition sSetTopAdj
  signature: : SSet.toTop.{u} ⊣ TopCat.toSSet.{u}
  body: Presheaf.uliftYonedaAdjunction
    (SSet.stdSimplex.{u}.leftKanExtension SimplexCategory.toTop)
    (SSet.stdSimplex.{u}.leftKanExtensionUnit SimplexCategory.toTop)

中文:
定义 sSetTopAdj
  签名: : SSet.toTop.{u} ⊣ 顶元素范畴.toSSet.{u}
  定义体: Presheaf.uliftYonedaAdjunction
    (SSet.stdSimplex.{u}.leftKanExtension SimplexCategory.toTop)
    (SSet.stdSimplex.{u}.leftKanExtensionUnit SimplexCategory.toTop)

Depends on / 依赖: Presheaf, Presheaf.uliftYonedaAdjunction, SSet.stdSimplex, SimplexCategory, SimplexCategory.toTop, leftKanExtension, leftKanExtensionUnit, stdSimplex, uliftYonedaAdjunction
-/
noncomputable def sSetTopAdj : SSet.toTop.{u} ⊣ TopCat.toSSet.{u} :=
  Presheaf.uliftYonedaAdjunction
    (SSet.stdSimplex.{u}.leftKanExtension SimplexCategory.toTop)
    (SSet.stdSimplex.{u}.leftKanExtensionUnit SimplexCategory.toTop)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SSet.toTop.{u}.IsLeftAdjoint
  body: sSetTopAdj.isLeftAdjoint

中文:
实例 :
  签名: SSet.toTop.{u}.是左伴随
  定义体: sSetTopAdj.isLeftAdjoint

Depends on / 依赖: isLeftAdjoint, sSetTopAdj, sSetTopAdj.isLeftAdjoint
-/
instance : SSet.toTop.{u}.IsLeftAdjoint := sSetTopAdj.isLeftAdjoint
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: TopCat.toSSet.{u}.IsRightAdjoint
  body: sSetTopAdj.isRightAdjoint

中文:
实例 :
  签名: 顶元素范畴.toSSet.{u}.是右伴随
  定义体: sSetTopAdj.isRightAdjoint

Depends on / 依赖: isRightAdjoint, sSetTopAdj, sSetTopAdj.isRightAdjoint
-/
instance : TopCat.toSSet.{u}.IsRightAdjoint := sSetTopAdj.isRightAdjoint

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `SSet.toTopSimplex` / `SSet.toTopSimplex` 的定义

English:
definition SSet.toTopSimplex
  signature: :
  body: Presheaf.isExtensionAlongULiftYoneda _

中文:
定义 SSet.toTopSimplex
  签名: :
  定义体: Presheaf.isExtensionAlongULiftYoneda _

Depends on / 依赖: Presheaf, Presheaf.isExtensionAlongULiftYoneda, isExtensionAlongULiftYoneda
-/
noncomputable def SSet.toTopSimplex :
    SSet.stdSimplex.{u} ⋙ SSet.toTop ≅ SimplexCategory.toTop :=
  Presheaf.isExtensionAlongULiftYoneda _

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SSet.toTop.{u}.IsLeftKanExtension SSet.toTopSimplex.inv
  body: inferInstanceAs (Functor.IsLeftKanExtension _
    (SSet.stdSimplex.{u}.leftKanExtensionUnit SimplexCategory.toTop.{u}))

中文:
实例 :
  签名: SSet.toTop.{u}.是LeftKanExtension SSet.toTopSimplex.inv
  定义体: inferInstanceAs (Functor.IsLeftKanExtension _
    (SSet.stdSimplex.{u}.leftKanExtensionUnit SimplexCategory.toTop.{u}))

Depends on / 依赖: Functor, Functor.IsLeftKanExtension, IsLeftKanExtension, SSet.stdSimplex, SimplexCategory, SimplexCategory.toTop, leftKanExtensionUnit, stdSimplex
-/
instance : SSet.toTop.{u}.IsLeftKanExtension SSet.toTopSimplex.inv :=
  inferInstanceAs (Functor.IsLeftKanExtension _
    (SSet.stdSimplex.{u}.leftKanExtensionUnit SimplexCategory.toTop.{u}))

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `sSetTopAdj_unit_app_app_down` / 引理 `sSetTopAdj_unit_app_app_down`

English:
lemma sSetTopAdj_unit_app_app_down
  given: (S : SSet) (m : SimplexCategoryᵒᵖ) (a : S.obj m)
  proof: by
  cat_disch

中文:
引理 sSetTopAdj_unit_app_app_down
  条件: (S : SSet) (m : SimplexCategoryᵒᵖ) (a : S.obj m)
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma sSetTopAdj_unit_app_app_down (S : SSet) (m : SimplexCategoryᵒᵖ) (a : S.obj m) :
    ((sSetTopAdj.unit.app S).app m a).down =
      SSet.toTopSimplex.inv.app _ ≫ SSet.toTop.map (SSet.yonedaEquiv.symm a) := by
  cat_disch

/--
Definition of `TopCat.toSSetIsoConst` / `TopCat.toSSetIsoConst` 的定义

English:
definition TopCat.toSSetIsoConst
  signature: (X : TopCat.{u}) [TotallyDisconnectedSpace X]
  body: (NatIso.ofComponents (fun n => Equiv.toIso
    ((TotallyDisconnectedSpace.continuousMapEquivOfConnectedSpace _ X).symm.trans
      (X.toSSetObjEquiv n).symm))).symm

#adaptation_note

中文:
定义 顶元素范畴.toSSetIsoConst
  签名: (X : 顶元素范畴.{u}) [全不连通空间 X]
  定义体: (NatIso.ofComponents (fun n => Equiv.toIso
    ((TotallyDisconnectedSpace.continuousMapEquivOfConnectedSpace _ X).symm.trans
      (X.toSSetObjEquiv n).symm))).symm

#adaptation_note

Depends on / 依赖: Equiv.toIso, NatIso, NatIso.ofComponents, TotallyDisconnectedSpace, TotallyDisconnectedSpace.continuousMapEquivOfConnectedSpace, X.toSSetObjEquiv, continuousMapEquivOfConnectedSpace, ofComponents, symm.trans, toSSetObjEquiv
-/
noncomputable def TopCat.toSSetIsoConst (X : TopCat.{u}) [TotallyDisconnectedSpace X] :
    TopCat.toSSet.obj X ≅ (Functor.const _).obj X :=
  (NatIso.ofComponents (fun n => Equiv.toIso
    ((TotallyDisconnectedSpace.continuousMapEquivOfConnectedSpace _ X).symm.trans
      (X.toSSetObjEquiv n).symm))).symm

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `SSet.stdSimplexToTop` / `SSet.stdSimplexToTop` 的定义

English:
definition SSet.stdSimplexToTop
  signature: :
  body: SSet.stdSimplex.whiskerLeft sSetTopAdj.unit ≫
    Functor.whiskerRight SSet.toTopSimplex.hom TopCat.toSSet

中文:
定义 SSet.stdSimplexToTop
  签名: :
  定义体: SSet.stdSimplex.whiskerLeft sSetTopAdj.unit ≫
    Functor.whiskerRight SSet.toTopSimplex.hom TopCat.toSSet
-/
@[simps! -isSimp] noncomputable def SSet.stdSimplexToTop :
    SSet.stdSimplex.{u} ⟶ SimplexCategory.toTop ⋙ TopCat.toSSet :=
  SSet.stdSimplex.whiskerLeft sSetTopAdj.unit ≫
    Functor.whiskerRight SSet.toTopSimplex.hom TopCat.toSSet
