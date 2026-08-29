/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.ConeCategory
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Localization.Adjunction
public import Mathlib.CategoryTheory.Localization.HasLocalization
public import Mathlib.CategoryTheory.Localization.Pi
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-! # The localized category has finite products

In this file, it is shown that if `L : C ⥤ D` is
a localization functor for `W : MorphismProperty C` and that
`W` is stable under finite products, then `D` has finite
products, and `L` preserves finite products.

-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Limits CategoryTheory.Functor

namespace Localization

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] (L : C ⥤ D)
  (W : MorphismProperty C) [L.IsLocalization W]

namespace HasProductsOfShapeAux

variable (J : Type) [HasProductsOfShape J C] [W.IsStableUnderProductsOfShape J]

/--
lemma `inverts` / 引理 `inverts`

English:
lemma inverts
  proof: fun _ _ f hf => Localization.inverts L W _ (MorphismProperty.limMap f hf)

中文:
引理 inverts
  证明: fun _ _ f hf => Localization.inverts L W _ (MorphismProperty.limMap f hf)

Depends on / 依赖: Localization, Localization.inverts, MorphismProperty, MorphismProperty.limMap, inverts, limMap
-/
lemma inverts :
    (W.functorCategory (Discrete J)).IsInvertedBy (lim ⋙ L) :=
  fun _ _ f hf => Localization.inverts L W _ (MorphismProperty.limMap f hf)

variable [W.ContainsIdentities] [Finite J]

/--
Definition of `limitFunctor` / `limitFunctor` 的定义

English:
abbreviation limitFunctor
  signature: :
  body: Localization.lift _ (inverts L W J)
    ((whiskeringRight (Discrete J) C D).obj L)

中文:
缩写 limitFunctor
  签名: :
  定义体: Localization.lift _ (inverts L W J)
    ((whiskeringRight (Discrete J) C D).obj L)

Depends on / 依赖: Discrete, Localization, Localization.lift, inverts, whiskeringRight
-/
noncomputable abbrev limitFunctor :
    (Discrete J ⥤ D) ⥤ D :=
  Localization.lift _ (inverts L W J)
    ((whiskeringRight (Discrete J) C D).obj L)

/--
Definition of `compLimitFunctorIso` / `compLimitFunctorIso` 的定义

English:
definition compLimitFunctorIso
  signature: :
  body: by
  apply Localization.fac

中文:
定义 compLimitFunctorIso
  签名: :
  定义体: by
  apply Localization.fac

Depends on / 依赖: Localization, Localization.fac
-/
noncomputable def compLimitFunctorIso :
    ((whiskeringRight (Discrete J) C D).obj L) ⋙ limitFunctor L W J ≅
      lim ⋙ L := by
  apply Localization.fac

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  body: (Functor.compConstIso _ _).symm

中文:
实例 :
  定义体: (Functor.compConstIso _ _).symm

Depends on / 依赖: Functor, Functor.compConstIso, compConstIso
-/
instance :
    CatCommSq (Functor.const (Discrete J)) L
      ((whiskeringRight (Discrete J) C D).obj L) (Functor.const (Discrete J)) where
  iso := (Functor.compConstIso _ _).symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  body: (compLimitFunctorIso L W J).symm

中文:
实例 :
  定义体: (compLimitFunctorIso L W J).symm

Depends on / 依赖: compLimitFunctorIso
-/
noncomputable instance :
    CatCommSq lim ((whiskeringRight (Discrete J) C D).obj L) L (limitFunctor L W J) where
  iso := (compLimitFunctorIso L W J).symm

/--
Definition of `adj` / `adj` 的定义

English:
definition adj
  signature: :
  body: constLimAdj.localization L W ((whiskeringRight (Discrete J) C D).obj L)
    (W.functorCategory (Discrete J)) (Functor.const _) (limitFunctor L W J)

中文:
定义 adj
  签名: :
  定义体: constLimAdj.localization L W ((whiskeringRight (Discrete J) C D).obj L)
    (W.functorCategory (Discrete J)) (Functor.const _) (limitFunctor L W J)

Depends on / 依赖: Category, Category.id_comp, Discrete, Functor, Functor.const, W.functorCategory, constLimAdj, constLimAdj.localization, functorCategory, id_comp, limitFunctor, localization, whiskeringRight
-/
noncomputable def adj :
    Functor.const _ ⊣ limitFunctor L W J :=
  constLimAdj.localization L W ((whiskeringRight (Discrete J) C D).obj L)
    (W.functorCategory (Discrete J)) (Functor.const _) (limitFunctor L W J)

/--
lemma `adj_counit_app` / 引理 `adj_counit_app`

English:
lemma adj_counit_app
  given: (F : Discrete J ⥤ C)
  proof: by
  apply constLimAdj.localization_counit_app

中文:
引理 adj_counit_app
  条件: (F : Discrete J ⥤ C)
  证明: by
  apply constLimAdj.localization_counit_app

Depends on / 依赖: constLimAdj, constLimAdj.localization_counit_app, localization_counit_app
-/
lemma adj_counit_app (F : Discrete J ⥤ C) :
    (adj L W J).counit.app (F ⋙ L) =
      (Functor.const (Discrete J)).map ((compLimitFunctorIso L W J).hom.app F) ≫
        (Functor.compConstIso (Discrete J) L).hom.app (lim.obj F) ≫
        whiskerRight (constLimAdj.counit.app F) L := by
  apply constLimAdj.localization_counit_app

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `isLimitMapCone` / `isLimitMapCone` 的定义

English:
definition isLimitMapCone
  signature: (F : Discrete J ⥤ C)
  body: IsLimit.ofIsoLimit (isLimitConeOfAdj (adj L W J) (F ⋙ L))
    (Cone.ext ((compLimitFunctorIso L W J).app F) (by simp [adj_counit_app, constLimAdj]))

中文:
定义 isLimitMapCone
  签名: (F : Discrete J ⥤ C)
  定义体: IsLimit.ofIsoLimit (isLimitConeOfAdj (adj L W J) (F ⋙ L))
    (Cone.ext ((compLimitFunctorIso L W J).app F) (by simp [adj_counit_app, constLimAdj]))

Depends on / 依赖: Cone.ext, IsLimit, IsLimit.ofIsoLimit, adj_counit_app, compLimitFunctorIso, constLimAdj, isLimitConeOfAdj, ofIsoLimit
-/
noncomputable def isLimitMapCone (F : Discrete J ⥤ C) :
    IsLimit (L.mapCone (limit.cone F)) :=
  IsLimit.ofIsoLimit (isLimitConeOfAdj (adj L W J) (F ⋙ L))
    (Cone.ext ((compLimitFunctorIso L W J).app F) (by simp [adj_counit_app, constLimAdj]))

end HasProductsOfShapeAux

variable [W.ContainsIdentities]

include L
/--
lemma `hasProductsOfShape` / 引理 `hasProductsOfShape`

English:
lemma hasProductsOfShape
  statement: (J : Type) [Finite J] [HasProductsOfShape J C]
  proof: hasLimitsOfShape_iff_isLeftAdjoint_const.2
    (HasProductsOfShapeAux.adj L W J).isLeftAdjoint

中文:
引理 hasProductsOfShape
  结论: (J : Type) [Finite J] [HasProductsOfShape J C]
  证明: hasLimitsOfShape_iff_isLeftAdjoint_const.2
    (HasProductsOfShapeAux.adj L W J).isLeftAdjoint

Depends on / 依赖: HasProductsOfShapeAux, HasProductsOfShapeAux.adj, hasLimitsOfShape_iff_isLeftAdjoint_const, isLeftAdjoint
-/
lemma hasProductsOfShape (J : Type) [Finite J] [HasProductsOfShape J C]
    [W.IsStableUnderProductsOfShape J] :
    HasProductsOfShape J D :=
  hasLimitsOfShape_iff_isLeftAdjoint_const.2
    (HasProductsOfShapeAux.adj L W J).isLeftAdjoint

/--
lemma `preservesProductsOfShape` / 引理 `preservesProductsOfShape`

English:
lemma preservesProductsOfShape
  statement: (J : Type) [Finite J]
  proof: preservesLimit_of_preserves_limit_cone (limit.isLimit F)
    (HasProductsOfShapeAux.isLimitMapCone L W J F)

中文:
引理 preservesProductsOfShape
  结论: (J : Type) [Finite J]
  证明: preservesLimit_of_preserves_limit_cone (limit.isLimit F)
    (HasProductsOfShapeAux.isLimitMapCone L W J F)

Depends on / 依赖: isLimit, limit.isLimit, preservesLimit_of_preserves_limit_cone
-/
lemma preservesProductsOfShape (J : Type) [Finite J]
    [HasProductsOfShape J C] [W.IsStableUnderProductsOfShape J] :
    PreservesLimitsOfShape (Discrete J) L where
  preservesLimit {F} := preservesLimit_of_preserves_limit_cone (limit.isLimit F)
    (HasProductsOfShapeAux.isLimitMapCone L W J F)

variable [HasFiniteProducts C] [W.IsStableUnderFiniteProducts]

include W in
/--
lemma `hasFiniteProducts` / 引理 `hasFiniteProducts`

English:
lemma hasFiniteProducts
  statement: HasFiniteProducts D
  proof: ⟨fun _ => hasProductsOfShape L W _⟩

include W in

中文:
引理 hasFiniteProducts
  结论: HasFiniteProducts D
  证明: ⟨fun _ => hasProductsOfShape L W _⟩

include W in

Depends on / 依赖: hasProductsOfShape
-/
lemma hasFiniteProducts : HasFiniteProducts D :=
  ⟨fun _ => hasProductsOfShape L W _⟩

include W in
/--
lemma `preservesFiniteProducts` / 引理 `preservesFiniteProducts`

English:
lemma preservesFiniteProducts
  proof: preservesProductsOfShape L W _

中文:
引理 preservesFiniteProducts
  证明: preservesProductsOfShape L W _

Depends on / 依赖: Category, Category.id_comp, Discrete, Discrete.addMonoidal_leftUnitor, addMonoidal_leftUnitor, eqToHom_app, eqToHom_map, eqToIso, eqToIso.inv, id_comp, preservesProductsOfShape, shiftFunctor, shiftFunctorAdd, shiftFunctorZero
-/
lemma preservesFiniteProducts :
    PreservesFiniteProducts L where
  preserves _ := preservesProductsOfShape L W _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasFiniteProducts (W.Localization)
  body: hasFiniteProducts W.Q W

中文:
实例 :
  签名: HasFiniteProducts (W.Localization)
  定义体: hasFiniteProducts W.Q W

Depends on / 依赖: Category, Category.id_comp, Discrete, Discrete.addMonoidal_rightUnitor, addMonoidal_rightUnitor, eqToHom_app, eqToHom_map, eqToIso, eqToIso.inv, hasFiniteProducts, id_comp, shiftFunctor, shiftFunctorAdd, shiftFunctorZero
-/
instance : HasFiniteProducts (W.Localization) := hasFiniteProducts W.Q W

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesFiniteProducts W.Q
  body: preservesFiniteProducts W.Q W

中文:
实例 :
  签名: PreservesFiniteProducts W.Q
  定义体: preservesFiniteProducts W.Q W

Depends on / 依赖: Category, Category.assoc, Category.comp_id, Discrete, Discrete.addMonoidal_associator, _eq_shiftFunctorAdd, addMonoidal_associator, comp_id, eqToHom_app, eqToHom_map, eqToIso, eqToIso.hom, preservesFiniteProducts, shiftFunctor, shiftFunctorAdd
-/
noncomputable instance : PreservesFiniteProducts W.Q := preservesFiniteProducts W.Q W

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [W.HasLocalization]
  signature: :
  body: hasFiniteProducts W.Q' W

中文:
实例 [W.HasLocalization]
  签名: :
  定义体: hasFiniteProducts W.Q' W

Depends on / 依赖: hasFiniteProducts
-/
instance [W.HasLocalization] :
    HasFiniteProducts (W.Localization') :=
  hasFiniteProducts W.Q' W

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [W.HasLocalization]
  signature: :
  body: preservesFiniteProducts W.Q' W

中文:
实例 [W.HasLocalization]
  签名: :
  定义体: preservesFiniteProducts W.Q' W

Depends on / 依赖: Iso.hom, NatTrans, NatTrans.congr_app, _zero_add, congr_app, congr_arg, preservesFiniteProducts, shiftFunctorAdd
-/
noncomputable instance [W.HasLocalization] :
    PreservesFiniteProducts W.Q' :=
  preservesFiniteProducts W.Q' W

end Localization

end CategoryTheory
