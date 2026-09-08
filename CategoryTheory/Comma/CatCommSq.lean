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
/-
**CategoryTheory.Arrow.catCommSq** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Arrow
`。
形式化陈述：catCommSq {C₁ C₂ D₁ D₂ : Type*} [Category C₁] [Category C₂] [Category D₁] 
[Category D₂] (T : C₁ ⥤ C₂) (L : C₁ ⥤ D₁) (R : C₂ ⥤ D₂) (B : D₁ ⥤ D₂) [CatCommSq
 T L R B] : CatCommSq T.mapArrow L.mapArrow R.mapArrow B.mapArrow where iso
参数：T : C₁ ⥤ C₂；L : C₁ ⥤ D₁；R : C₂ ⥤ D₂；B : D₁ ⥤ D₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance catCommSq
    {C₁ C₂ D₁ D₂ : Type*} [Category C₁] [Category C₂] [Category D₁] [Category D₂]
    (T : C₁ ⥤ C₂) (L : C₁ ⥤ D₁) (R : C₂ ⥤ D₂) (B : D₁ ⥤ D₂) [CatCommSq T L R B] :
    CatCommSq T.mapArrow L.mapArrow R.mapArrow B.mapArrow where
  iso := (Functor.mapArrowFunctor _ _).mapIso (CatCommSq.iso T L R B)

end CategoryTheory.Arrow

