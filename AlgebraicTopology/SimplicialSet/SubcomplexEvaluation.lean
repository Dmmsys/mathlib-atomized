/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import Mathlib.CategoryTheory.Limits.Preorder
public import Mathlib.CategoryTheory.Limits.Set

/-!
# The evaluation functor on subcomplexes

We define an evaluation functor `SSet.Subcomplex.evaluation : X.Subcomplex ⥤ Set (X.obj j)`
when `X : SSet` and `j : SimplexCategoryᵒᵖ`. We use it to show that the functor
`Subcomplex.toSSetFunctor : X.Subcomplex ⥤ SSet` preserves filtered colimits.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace SSet.Subcomplex

/-- The evaluation functor `X.Subcomplex ⥤ Set (X.obj j)` when `X : SSet`
and `j : SimplexCategoryᵒᵖ`. -/
@[simps]
/-
**SSet.Subcomplex.evaluation** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Subcomplex`。
形式化陈述：evaluation (X : SSet.{u}) (j : SimplexCategoryᵒᵖ) : X.Subcomplex ⥤ Set (X.
obj j) where obj A
参数：X : SSet.{u}；j : SimplexCategoryᵒᵖ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The evaluation functor `X.Subcomplex ⥤ Set (X.obj j)` when `X : SSet`
and `j : SimplexCategoryᵒᵖ`.
-/
def evaluation (X : SSet.{u}) (j : SimplexCategoryᵒᵖ) :
    X.Subcomplex ⥤ Set (X.obj j) where
  obj A := A.obj j
  map f := CategoryTheory.homOfLE (leOfHom f j)
/-
**SSet.Subcomplex.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.Subcomplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {J : Type*} [Category* J] {X : SSet.{u}} [IsFilteredOrEmpty J] :
    PreservesColimitsOfShape J (Subcomplex.toSSetFunctor (X := X)) where
  preservesColimit {F} :=
    preservesColimit_of_preserves_colimit_cocone
      (Preorder.colimitCoconeOfIsLUB F isLUB_iSup).isColimit
        (evaluationJointlyReflectsColimits _ (fun j ↦ IsColimit.ofIsoColimit
          (isColimitOfPreserves Set.functorToTypes
              ((Preorder.colimitCoconeOfIsLUB (F ⋙ evaluation _ j) isLUB_iSup).isColimit))
                (Cocone.ext (Set.functorToTypes.mapIso
                  (CategoryTheory.eqToIso (by cat_disch))))))

end SSet.Subcomplex

