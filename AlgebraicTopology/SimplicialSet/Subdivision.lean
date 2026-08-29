/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.CategoryTheory.Limits.Presheaf
public import Mathlib.Order.NonemptyFiniteChains

/-!
# The subdivision functors

In this file, we define the subdivision functor `sd : SSet ⥤ SSet`
and its right adjoint `ex`.

## TODO (@joelriou)
* define another functor `SSet.B : SSet ⥤ SSet` by sending `X` to
the nerve of the partially ordered type `X.N` of nondegenerate
simplices in `X`, define a natural transformation `sd ⟶ B`,
and show that on suitable simplicial sets `X`, this natural
transformation is an isomorphism.

## References
* [J. F. Jardine, *Simplicial approximation*][jardine-2004]

-/

@[expose] public section

universe v u

open CategoryTheory

/--
Definition of `SimplexCategory.sd` / `SimplexCategory.sd` 的定义

English:
definition SimplexCategory.sd
  signature: : SimplexCategory ⥤ SSet.{u}
  body: toPartOrd ⋙ PartOrd.nonemptyFiniteChainsFunctor ⋙ PartOrd.nerveFunctor

中文:
定义 SimplexCategory.sd
  签名: : SimplexCategory ⥤ SSet.{u}
  定义体: toPartOrd ⋙ PartOrd.nonemptyFiniteChainsFunctor ⋙ PartOrd.nerveFunctor

Depends on / 依赖: PartOrd, PartOrd.nerveFunctor, PartOrd.nonemptyFiniteChainsFunctor, nerveFunctor, nonemptyFiniteChainsFunctor, toPartOrd
-/
noncomputable def SimplexCategory.sd : SimplexCategory ⥤ SSet.{u} :=
  toPartOrd ⋙ PartOrd.nonemptyFiniteChainsFunctor ⋙ PartOrd.nerveFunctor

namespace SSet

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `sd` / `sd` 的定义

English:
definition sd
  signature: : SSet.{u} ⥤ SSet.{u}
  body: stdSimplex.leftKanExtension SimplexCategory.sd

中文:
定义 sd
  签名: : SSet.{u} ⥤ SSet.{u}
  定义体: stdSimplex.leftKanExtension SimplexCategory.sd

Depends on / 依赖: SimplexCategory, SimplexCategory.sd, leftKanExtension, stdSimplex, stdSimplex.leftKanExtension
-/
noncomputable def sd : SSet.{u} ⥤ SSet.{u} :=
  stdSimplex.leftKanExtension SimplexCategory.sd

/--
Definition of `ex` / `ex` 的定义

English:
definition ex
  signature: : SSet.{u} ⥤ SSet.{u}
  body: Presheaf.restrictedULiftYoneda.{0} SimplexCategory.sd

中文:
定义 ex
  签名: : SSet.{u} ⥤ SSet.{u}
  定义体: Presheaf.restrictedULiftYoneda.{0} SimplexCategory.sd

Depends on / 依赖: Presheaf, Presheaf.restrictedULiftYoneda, SimplexCategory, SimplexCategory.sd, restrictedULiftYoneda
-/
noncomputable def ex : SSet.{u} ⥤ SSet.{u} :=
  Presheaf.restrictedULiftYoneda.{0} SimplexCategory.sd

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `sdExAdjunction` / `sdExAdjunction` 的定义

English:
definition sdExAdjunction
  signature: : sd.{u} ⊣ ex
  body: Presheaf.uliftYonedaAdjunction.{0}
    (SSet.stdSimplex.{u}.leftKanExtension SimplexCategory.sd)
    (SSet.stdSimplex.{u}.leftKanExtensionUnit SimplexCategory.sd)

中文:
定义 sdExAdjunction
  签名: : sd.{u} ⊣ ex
  定义体: Presheaf.uliftYonedaAdjunction.{0}
    (SSet.stdSimplex.{u}.leftKanExtension SimplexCategory.sd)
    (SSet.stdSimplex.{u}.leftKanExtensionUnit SimplexCategory.sd)

Depends on / 依赖: Presheaf, Presheaf.uliftYonedaAdjunction, SSet.stdSimplex, SimplexCategory, SimplexCategory.sd, leftKanExtension, leftKanExtensionUnit, stdSimplex, uliftYonedaAdjunction
-/
noncomputable def sdExAdjunction : sd.{u} ⊣ ex :=
  Presheaf.uliftYonedaAdjunction.{0}
    (SSet.stdSimplex.{u}.leftKanExtension SimplexCategory.sd)
    (SSet.stdSimplex.{u}.leftKanExtensionUnit SimplexCategory.sd)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: sd.{u}.IsLeftAdjoint
  body: sdExAdjunction.isLeftAdjoint

中文:
实例 :
  签名: sd.{u}.IsLeftAdjoint
  定义体: sdExAdjunction.isLeftAdjoint

Depends on / 依赖: isLeftAdjoint, sdExAdjunction, sdExAdjunction.isLeftAdjoint
-/
instance : sd.{u}.IsLeftAdjoint := sdExAdjunction.isLeftAdjoint

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ex.{u}.IsRightAdjoint
  body: sdExAdjunction.isRightAdjoint

中文:
实例 :
  签名: ex.{u}.IsRightAdjoint
  定义体: sdExAdjunction.isRightAdjoint

Depends on / 依赖: isRightAdjoint, sdExAdjunction, sdExAdjunction.isRightAdjoint
-/
instance : ex.{u}.IsRightAdjoint := sdExAdjunction.isRightAdjoint

namespace stdSimplex

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `sdIso` / `sdIso` 的定义

English:
definition sdIso
  signature: : stdSimplex.{u} ⋙ sd ≅ SimplexCategory.sd
  body: Presheaf.isExtensionAlongULiftYoneda _

中文:
定义 sdIso
  签名: : stdSimplex.{u} ⋙ sd ≅ SimplexCategory.sd
  定义体: Presheaf.isExtensionAlongULiftYoneda _

Depends on / 依赖: Presheaf, Presheaf.isExtensionAlongULiftYoneda, isExtensionAlongULiftYoneda
-/
noncomputable def sdIso : stdSimplex.{u} ⋙ sd ≅ SimplexCategory.sd :=
  Presheaf.isExtensionAlongULiftYoneda _

end stdSimplex

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: sd.{u}.IsLeftKanExtension stdSimplex.sdIso.inv
  body: inferInstanceAs (Functor.IsLeftKanExtension _
    (SSet.stdSimplex.leftKanExtensionUnit SimplexCategory.sd.{u}))

中文:
实例 :
  签名: sd.{u}.IsLeftKanExtension stdSimplex.sdIso.inv
  定义体: inferInstanceAs (Functor.IsLeftKanExtension _
    (SSet.stdSimplex.leftKanExtensionUnit SimplexCategory.sd.{u}))

Depends on / 依赖: Functor, Functor.IsLeftKanExtension, IsLeftKanExtension, SSet.stdSimplex.leftKanExtensionUnit, SimplexCategory, SimplexCategory.sd, leftKanExtensionUnit, stdSimplex
-/
instance : sd.{u}.IsLeftKanExtension stdSimplex.sdIso.inv :=
  inferInstanceAs (Functor.IsLeftKanExtension _
    (SSet.stdSimplex.leftKanExtensionUnit SimplexCategory.sd.{u}))

end SSet
