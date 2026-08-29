/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.CatCommSq
public import Mathlib.CategoryTheory.Comma.Arrow

/-!
# 2-commutative squares of categories of arrows

-/

@[expose] public section

namespace CategoryTheory.Arrow

@[simps]
/--
Instance `catCommSq` / 实例 `catCommSq`

English:
instance catCommSq
  body: (Functor.mapArrowFunctor _ _).mapIso (CatCommSq.iso T L R B)

中文:
实例 catCommSq
  定义体: (Functor.mapArrowFunctor _ _).mapIso (CatCommSq.iso T L R B)

Depends on / 依赖: CatCommSq, CatCommSq.iso, Functor, Functor.mapArrowFunctor, mapArrowFunctor, mapIso
-/
instance catCommSq
    {C₁ C₂ D₁ D₂ : Type*} [Category C₁] [Category C₂] [Category D₁] [Category D₂]
    (T : C₁ ⥤ C₂) (L : C₁ ⥤ D₁) (R : C₂ ⥤ D₂) (B : D₁ ⥤ D₂) [CatCommSq T L R B] :
    CatCommSq T.mapArrow L.mapArrow R.mapArrow B.mapArrow where
  iso := (Functor.mapArrowFunctor _ _).mapIso (CatCommSq.iso T L R B)

end CategoryTheory.Arrow
