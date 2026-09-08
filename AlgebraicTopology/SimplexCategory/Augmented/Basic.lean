/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.WithTerminal.Basic
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic

/-!
# The Augmented simplex category

This file defines the `AugmentedSimplexCategory` as the category obtained by adding an initial
object to `SimplexCategory` (using `CategoryTheory.WithInitial`).

This definition provides a canonical full and faithful inclusion functor
`inclusion : SimplexCategory ⥤ AugmentedSimplexCategory`.

We prove that functors out of `AugmentedSimplexCategory` are equivalent to augmented cosimplicial
objects and that functors out of `AugmentedSimplexCategoryᵒᵖ` are equivalent to augmented simplicial
objects, and we provide a translation of the main constructions on augmented (co)simplicial objects
(i.e `drop`, `point` and `toArrow`) in terms of these equivalences.

-/

@[expose] public section

open CategoryTheory

/-- The `AugmentedSimplexCategory` is the category obtained from `SimplexCategory` by adjoining an
initial object. -/
/-
**AugmentedSimplexCategory** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：AugmentedSimplexCategory
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `AugmentedSimplexCategory` is the category obtained from `SimplexCategory` b
y adjoining an
initial object.
-/
abbrev AugmentedSimplexCategory := WithInitial SimplexCategory

namespace AugmentedSimplexCategory

variable {C : Type*} [Category* C]

/-- The canonical inclusion from `SimplexCategory` to `AugmentedSimplexCategory`. -/
@[simps!]
/-
**AugmentedSimplexCategory.inclusion** 是 Mathlib 中的一个定义，位于命名空间 `AugmentedSimplex
Category`。
形式化陈述：inclusion : SimplexCategory ⥤ AugmentedSimplexCategory
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical inclusion from `SimplexCategory` to `AugmentedSimplexCategory`.
-/
def inclusion : SimplexCategory ⥤ AugmentedSimplexCategory := WithInitial.incl
/-
**AugmentedSimplexCategory.** 是 Mathlib 中的一个实例，位于命名空间 `AugmentedSimplexCategory`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : inclusion.Full := inferInstanceAs WithInitial.incl.Full
/-
**AugmentedSimplexCategory.** 是 Mathlib 中的一个实例，位于命名空间 `AugmentedSimplexCategory`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : inclusion.Faithful := inferInstanceAs WithInitial.incl.Faithful
/-
**AugmentedSimplexCategory.** 是 Mathlib 中的一个实例，位于命名空间 `AugmentedSimplexCategory`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Limits.HasInitial AugmentedSimplexCategory :=
  inferInstanceAs <| Limits.HasInitial <| WithInitial _

/-- The equivalence between functors out of `AugmentedSimplexCategory` and augmented
cosimplicial objects. -/
@[simps!]
/-
**AugmentedSimplexCategory.equivAugmentedCosimplicialObject** 是 Mathlib 中的一个定义，位
于命名空间 `AugmentedSimplexCategory`。
形式化陈述：equivAugmentedCosimplicialObject : (AugmentedSimplexCategory ⥤ C) ≌ Cosimp
licialObject.Augmented C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between functors out of `AugmentedSimplexCategory` and augmented
cosimplicial objects.
-/
def equivAugmentedCosimplicialObject :
    (AugmentedSimplexCategory ⥤ C) ≌ CosimplicialObject.Augmented C :=
  WithInitial.equivComma

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- Through the equivalence `(AugmentedSimplexCategory ⥤ C) ≌ CosimplicialObject.Augmented C`,
dropping the augmentation corresponds to precomposition with
`inclusion : SimplexCategory ⥤ AugmentedSimplexCategory`. -/
@[simps!]
/-
**AugmentedSimplexCategory.equivAugmentedCosimplicialObjectFunctorCompDropIso** 
是 Mathlib 中的一个定义，位于命名空间 `AugmentedSimplexCategory`。
形式化陈述：equivAugmentedCosimplicialObjectFunctorCompDropIso : equivAugmentedCosimpl
icialObject.functor ⋙ CosimplicialObject.Augmented.drop ≅ (Functor.whiskeringLef
t _ _ C).obj inclusion
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Through the equivalence `(AugmentedSimplexCategory ⥤ C) ≌ CosimplicialObject.Aug
mented C`,
dropping the augmentation corresponds to precomposition with
`inclusion : SimplexCategory ⥤ AugmentedSimplexCategory`.
-/
def equivAugmentedCosimplicialObjectFunctorCompDropIso :
    equivAugmentedCosimplicialObject.functor ⋙ CosimplicialObject.Augmented.drop ≅
    (Functor.whiskeringLeft _ _ C).obj inclusion :=
  .refl _

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- Through the equivalence `(AugmentedSimplexCategory ⥤ C) ≌ CosimplicialObject.Augmented C`,
taking the point of the augmentation corresponds to evaluation at the initial object. -/
@[simps!]
/-
**AugmentedSimplexCategory.equivAugmentedCosimplicialObjectFunctorCompPointIso**
 是 Mathlib 中的一个定义，位于命名空间 `AugmentedSimplexCategory`。
形式化陈述：equivAugmentedCosimplicialObjectFunctorCompPointIso : equivAugmentedCosimp
licialObject.functor ⋙ CosimplicialObject.Augmented.point ≅ ((evaluation _ _).ob
j .star : (AugmentedSimplexCategory ⥤ C) ⥤ C)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Through the equivalence `(AugmentedSimplexCategory ⥤ C) ≌ CosimplicialObject.Aug
mented C`,
taking the point of the augmentation corresponds to evaluation at the initial ob
ject.
-/
def equivAugmentedCosimplicialObjectFunctorCompPointIso :
    equivAugmentedCosimplicialObject.functor ⋙ CosimplicialObject.Augmented.point ≅
    ((evaluation _ _).obj .star : (AugmentedSimplexCategory ⥤ C) ⥤ C) :=
  .refl _

/-- Through the equivalence `(AugmentedSimplexCategory ⥤ C) ≌ CosimplicialObject.Augmented C`,
the arrow attached to the cosimplicial object is the one obtained by evaluation at the unique arrow
`star ⟶ of [0]`. -/
@[simps!]
/-
**AugmentedSimplexCategory.equivAugmentedCosimplicialObjectFunctorCompToArrowIso
** 是 Mathlib 中的一个定义，位于命名空间 `AugmentedSimplexCategory`。
形式化陈述：equivAugmentedCosimplicialObjectFunctorCompToArrowIso : equivAugmentedCosi
mplicialObject.functor ⋙ CosimplicialObject.Augmented.toArrow ≅ Functor.mapArrow
Functor _ C ⋙ (evaluation _ _ |>.obj <| .mk <| WithInitial.homTo <| .mk 0)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Through the equivalence `(AugmentedSimplexCategory ⥤ C) ≌ CosimplicialObject.Aug
mented C`,
the arrow attached to the cosimplicial object is the one obtained by evaluation 
at the unique arrow
`star ⟶ of [0]`.
-/
def equivAugmentedCosimplicialObjectFunctorCompToArrowIso :
    equivAugmentedCosimplicialObject.functor ⋙ CosimplicialObject.Augmented.toArrow ≅
    Functor.mapArrowFunctor _ C ⋙
      (evaluation _ _ |>.obj <| .mk <| WithInitial.homTo <| .mk 0) :=
  .refl _

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The equivalence between functors out of `AugmentedSimplexCategory` and augmented simplicial
objects. -/
@[simps!]
/-
**AugmentedSimplexCategory.equivAugmentedSimplicialObject** 是 Mathlib 中的一个定义，位于命
名空间 `AugmentedSimplexCategory`。
形式化陈述：equivAugmentedSimplicialObject : (AugmentedSimplexCategoryᵒᵖ ⥤ C) ≌ Simpli
cialObject.Augmented C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between functors out of `AugmentedSimplexCategory` and augmented
 simplicial
objects.
-/
def equivAugmentedSimplicialObject :
    (AugmentedSimplexCategoryᵒᵖ ⥤ C) ≌ SimplicialObject.Augmented C :=
  WithInitial.opEquiv SimplexCategory |>.congrLeft |>.trans WithTerminal.equivComma

/-- Through the equivalence `(AugmentedSimplexCategoryᵒᵖ ⥤ C) ≌ SimplicialObject.Augmented C`,
dropping the augmentation corresponds to precomposition with
`inclusionᵒᵖ : SimplexCategoryᵒᵖ ⥤ AugmentedSimplexCategoryᵒᵖ`. -/
@[simps!]
/-
**AugmentedSimplexCategory.equivAugmentedSimplicialObjectFunctorCompDropIso** 是 
Mathlib 中的一个定义，位于命名空间 `AugmentedSimplexCategory`。
形式化陈述：equivAugmentedSimplicialObjectFunctorCompDropIso : equivAugmentedSimplicia
lObject.functor ⋙ SimplicialObject.Augmented.drop ≅ (Functor.whiskeringLeft _ _ 
C).obj inclusion.op
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Through the equivalence `(AugmentedSimplexCategoryᵒᵖ ⥤ C) ≌ SimplicialObject.Aug
mented C`,
dropping the augmentation corresponds to precomposition with
`inclusionᵒᵖ : SimplexCategoryᵒᵖ ⥤ AugmentedSimplexCategoryᵒᵖ`.
-/
def equivAugmentedSimplicialObjectFunctorCompDropIso :
    equivAugmentedSimplicialObject.functor ⋙ SimplicialObject.Augmented.drop ≅
    (Functor.whiskeringLeft _ _ C).obj inclusion.op :=
  .refl _

/-- Through the equivalence `(AugmentedSimplexCategory ⥤ C) ≌ CosimplicialObject.Augmented C`,
taking the point of the augmentation corresponds to evaluation at the initial object. -/
@[simps!]
/-
**AugmentedSimplexCategory.equivAugmentedSimplicialObjectFunctorCompPointIso** 是
 Mathlib 中的一个定义，位于命名空间 `AugmentedSimplexCategory`。
形式化陈述：equivAugmentedSimplicialObjectFunctorCompPointIso : equivAugmentedSimplici
alObject.functor ⋙ SimplicialObject.Augmented.point ≅ (evaluation _ C).obj (.op 
.star)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Through the equivalence `(AugmentedSimplexCategory ⥤ C) ≌ CosimplicialObject.Aug
mented C`,
taking the point of the augmentation corresponds to evaluation at the initial ob
ject.
-/
def equivAugmentedSimplicialObjectFunctorCompPointIso :
    equivAugmentedSimplicialObject.functor ⋙ SimplicialObject.Augmented.point ≅
    (evaluation _ C).obj (.op .star) :=
  .refl _

/-- Through the equivalence `(AugmentedSimplexCategory ⥤ C) ≌ CosimplicialObject.Augmented C`,
the arrow attached to the cosimplicial object is the one obtained by evaluation at the unique arrow
`star ⟶ of [0]`. -/
@[simps!]
/-
**AugmentedSimplexCategory.equivAugmentedSimplicialObjectFunctorCompToArrowIso**
 是 Mathlib 中的一个定义，位于命名空间 `AugmentedSimplexCategory`。
形式化陈述：equivAugmentedSimplicialObjectFunctorCompToArrowIso : equivAugmentedSimpli
cialObject.functor ⋙ SimplicialObject.Augmented.toArrow ≅ Functor.mapArrowFuncto
r _ C ⋙ (evaluation _ _ |>.obj <| .mk <| .op <| WithInitial.homTo <| .mk 0)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Through the equivalence `(AugmentedSimplexCategory ⥤ C) ≌ CosimplicialObject.Aug
mented C`,
the arrow attached to the cosimplicial object is the one obtained by evaluation 
at the unique arrow
`star ⟶ of [0]`.
-/
def equivAugmentedSimplicialObjectFunctorCompToArrowIso :
    equivAugmentedSimplicialObject.functor ⋙ SimplicialObject.Augmented.toArrow ≅
    Functor.mapArrowFunctor _ C ⋙
      (evaluation _ _ |>.obj <| .mk <| .op <| WithInitial.homTo <| .mk 0) :=
  .refl _

end AugmentedSimplexCategory

