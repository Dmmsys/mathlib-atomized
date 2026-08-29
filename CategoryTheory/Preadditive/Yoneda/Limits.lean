/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Limits.Yoneda

/-!
# The Yoneda embedding for preadditive categories preserves limits

The Yoneda embedding for preadditive categories preserves limits.

## Implementation notes

This is in a separate file to avoid having to import the development of the abelian structure on
`ModuleCat` in the main file about the preadditive Yoneda embedding.

-/

public section


universe v u

open CategoryTheory.Preadditive Opposite CategoryTheory.Limits

noncomputable section

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]

/--
Instance `preservesLimits_preadditiveYonedaObj` / 实例 `preservesLimits_preadditiveYonedaObj`

English:
instance preservesLimits_preadditiveYonedaObj
  signature: (X : C)
  body: have : PreservesLimits (preadditiveYonedaObj X ⋙ forget _) :=
    (inferInstance : PreservesLimits (yoneda.obj X))
  preservesLimits_of_reflects_of_preserves _ (forget _)

中文:
实例 preservesLimits_preadditiveYonedaObj
  签名: (X : C)
  定义体: have : PreservesLimits (preadditiveYonedaObj X ⋙ forget _) :=
    (inferInstance : PreservesLimits (yoneda.obj X))
  preservesLimits_of_reflects_of_preserves _ (forget _)

Depends on / 依赖: PreservesLimits, forget, preadditiveYonedaObj, preservesLimits_of_reflects_of_preserves, yoneda, yoneda.obj
-/
instance preservesLimits_preadditiveYonedaObj (X : C) : PreservesLimits (preadditiveYonedaObj X) :=
  have : PreservesLimits (preadditiveYonedaObj X ⋙ forget _) :=
    (inferInstance : PreservesLimits (yoneda.obj X))
  preservesLimits_of_reflects_of_preserves _ (forget _)

/--
Instance `preservesLimits_preadditiveCoyonedaObj` / 实例 `preservesLimits_preadditiveCoyonedaObj`

English:
instance preservesLimits_preadditiveCoyonedaObj
  signature: (X : C)
  body: have : PreservesLimits (preadditiveCoyonedaObj X ⋙ forget _) :=
    (inferInstance : PreservesLimits (coyoneda.obj (op X)))
  preservesLimits_of_reflects_of_preserves _ (forget _)

中文:
实例 preservesLimits_preadditiveCoyonedaObj
  签名: (X : C)
  定义体: have : PreservesLimits (preadditiveCoyonedaObj X ⋙ forget _) :=
    (inferInstance : PreservesLimits (coyoneda.obj (op X)))
  preservesLimits_of_reflects_of_preserves _ (forget _)

Depends on / 依赖: PreservesLimits, coyoneda, coyoneda.obj, forget, preadditiveCoyonedaObj, preservesLimits_of_reflects_of_preserves
-/
instance preservesLimits_preadditiveCoyonedaObj (X : C) :
    PreservesLimits (preadditiveCoyonedaObj X) :=
  have : PreservesLimits (preadditiveCoyonedaObj X ⋙ forget _) :=
    (inferInstance : PreservesLimits (coyoneda.obj (op X)))
  preservesLimits_of_reflects_of_preserves _ (forget _)

/--
Instance `preservesLimits_preadditiveYoneda_obj` / 实例 `preservesLimits_preadditiveYoneda_obj`

English:
instance preservesLimits_preadditiveYoneda_obj
  signature: (X : C)
  body: show PreservesLimits (preadditiveYonedaObj X ⋙ forget₂ _ _) from inferInstance

中文:
实例 preservesLimits_preadditiveYoneda_obj
  签名: (X : C)
  定义体: show PreservesLimits (preadditiveYonedaObj X ⋙ forget₂ _ _) from inferInstance

Depends on / 依赖: PreservesLimits, preadditiveYonedaObj
-/
instance preservesLimits_preadditiveYoneda_obj (X : C) :
    PreservesLimits (preadditiveYoneda.obj X) :=
  show PreservesLimits (preadditiveYonedaObj X ⋙ forget₂ _ _) from inferInstance

/--
Instance `preservesLimits_preadditiveCoyoneda_obj` / 实例 `preservesLimits_preadditiveCoyoneda_obj`

English:
instance preservesLimits_preadditiveCoyoneda_obj
  signature: (X : Cᵒᵖ)
  body: show PreservesLimits (preadditiveCoyonedaObj (unop X) ⋙ forget₂ _ _) from inferInstance

中文:
实例 preservesLimits_preadditiveCoyoneda_obj
  签名: (X : Cᵒᵖ)
  定义体: show PreservesLimits (preadditiveCoyonedaObj (unop X) ⋙ forget₂ _ _) from inferInstance

Depends on / 依赖: PreservesLimits, preadditiveCoyonedaObj
-/
instance preservesLimits_preadditiveCoyoneda_obj (X : Cᵒᵖ) :
    PreservesLimits (preadditiveCoyoneda.obj X) :=
  show PreservesLimits (preadditiveCoyonedaObj (unop X) ⋙ forget₂ _ _) from inferInstance

end CategoryTheory
