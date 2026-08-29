/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Adjunction.Lifting.Right
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Groupoid
public import Mathlib.CategoryTheory.Groupoid.Discrete
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Monad.Comonadicity
/-!

# Functors into a complete monoidal closed category form a monoidal closed category.

TODO (in progress by Joël Riou): make a more explicit construction of the internal hom in functor
categories.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory MonoidalClosed Limits

noncomputable section

namespace CategoryTheory.Functor

section
variable (I : Type u₂) [Category.{v₂} I]

set_option backward.privateInPublic true in
/--
Definition of `incl` / `incl` 的定义

English:
abbreviation incl
  signature: : Discrete I ⥤ I
  body: Discrete.functor id

中文:
缩写 incl
  签名: : 离散 I ⥤ I
  定义体: Discrete.functor id
-/
private abbrev incl : Discrete I ⥤ I := Discrete.functor id

variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C] [MonoidalClosed C]

variable [forall (F : Discrete I ⥤ C), (Discrete.functor id).HasRightKanExtension F]
-- is also implied by: `[HasLimitsOfSize.{u₂, max u₂ v₂} C]`

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ReflectsIsomorphisms (whiskeringLeft _ _ C).obj (incl I)
  body: by
    simp only [NatTrans.isIso_iff_isIso_app] at *
    intro X
    exact h ⟨X⟩

中文:
实例 :
  签名: 反映同构 (whiskeringLeft _ _ C).obj (incl I)
  定义体: by
    simp only [NatTrans.isIso_iff_isIso_app] at *
    intro X
    exact h ⟨X⟩

Depends on / 依赖: NatTrans, NatTrans.isIso_iff_isIso_app, isIso_iff_isIso_app
-/
instance : ReflectsIsomorphisms (whiskeringLeft _ _ C).obj (incl I) where
  reflects f h := by
    simp only [NatTrans.isIso_iff_isIso_app] at *
    intro X
    exact h ⟨X⟩

variable [HasLimitsOfShape WalkingParallelPair C]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Comonad.PreservesLimitOfIsCoreflexivePair ((whiskeringLeft _ _ C).obj (incl I))
  body: ⟨inferInstance⟩

中文:
实例 :
  签名: 余单子.保持LimitOfIsCoreflexivePair ((whiskeringLeft _ _ C).obj (incl I))
  定义体: ⟨inferInstance⟩

Depends on / 依赖: precoherent
-/
instance : Comonad.PreservesLimitOfIsCoreflexivePair ((whiskeringLeft _ _ C).obj (incl I)) :=
  ⟨inferInstance⟩

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ComonadicLeftAdjoint ((whiskeringLeft _ _ C).obj (incl I))
  body: Comonad.comonadicOfHasPreservesCoreflexiveEqualizersOfReflectsIsomorphisms
    ((incl I).ranAdjunction C)

中文:
实例 :
  签名: 余monadicLeftAdjoint ((whiskeringLeft _ _ C).obj (incl I))
  定义体: Comonad.comonadicOfHasPreservesCoreflexiveEqualizersOfReflectsIsomorphisms
    ((incl I).ranAdjunction C)

Depends on / 依赖: Comonad, Comonad.comonadicOfHasPreservesCoreflexiveEqualizersOfReflectsIsomorphisms, comonadicOfHasPreservesCoreflexiveEqualizersOfReflectsIsomorphisms, ranAdjunction
-/
instance : ComonadicLeftAdjoint ((whiskeringLeft _ _ C).obj (incl I)) :=
  Comonad.comonadicOfHasPreservesCoreflexiveEqualizersOfReflectsIsomorphisms
    ((incl I).ranAdjunction C)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
instance (F : I ⥤ C) : IsLeftAdjoint (tensorLeft (incl I ⋙ F)) :=
  (ihom.adjunction (incl I ⋙ F)).isLeftAdjoint

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Auxiliary definition for `functorCategoryMonoidalClosed` -/
@[instance_reducible]
/--
Definition of `functorCategoryClosed` / `functorCategoryClosed` 的定义

English:
definition functorCategoryClosed
  signature: (F : I ⥤ C)
  body: have := (ihom.adjunction (incl I ⋙ F)).isLeftAdjoint
  have := isLeftAdjoint_square_lift_comonadic (tensorLeft F) ((whiskeringLeft _ _ C).obj (incl I))
    ((whiskeringLeft _ _ C).obj (incl I)) (tensorLeft (incl I ⋙ F)) (Iso.refl _)
  { rightAdj := (tensorLeft F).rightAdjoint
    adj := Adjunction.o

中文:
定义 functorCategoryClosed
  签名: (F : I ⥤ C)
  定义体: have := (ihom.adjunction (incl I ⋙ F)).isLeftAdjoint
  have := isLeftAdjoint_square_lift_comonadic (tensorLeft F) ((whiskeringLeft _ _ C).obj (incl I))
    ((whiskeringLeft _ _ C).obj (incl I)) (tensorLeft (incl I ⋙ F)) (Iso.refl _)
  { rightAdj := (tensorLeft F).rightAdjoint
    adj := Adjunction.o

Depends on / 依赖: Adjunction, Adjunction.ofIsLeftAdjoint, Iso.refl, adjunction, ihom.adjunction, isLeftAdjoint, isLeftAdjoint_square_lift_comonadic, ofIsLeftAdjoint, rightAdj, rightAdjoint, tensorLeft, whiskeringLeft
-/
def functorCategoryClosed (F : I ⥤ C) : Closed F :=
  have := (ihom.adjunction (incl I ⋙ F)).isLeftAdjoint
  have := isLeftAdjoint_square_lift_comonadic (tensorLeft F) ((whiskeringLeft _ _ C).obj (incl I))
    ((whiskeringLeft _ _ C).obj (incl I)) (tensorLeft (incl I ⋙ F)) (Iso.refl _)
  { rightAdj := (tensorLeft F).rightAdjoint
    adj := Adjunction.ofIsLeftAdjoint (tensorLeft F) }

/--
Assuming the existence of certain limits, functors into a monoidal closed category form a
monoidal closed category.

Note: this is defined completely abstractly, and does not have any good definitional properties.
See the TODO in the module docstring.
-/
@[instance_reducible]
/--
Definition of `functorCategoryMonoidalClosed` / `functorCategoryMonoidalClosed` 的定义

English:
definition functorCategoryMonoidalClosed
  signature: : MonoidalClosed (I ⥤ C) where
  body: functorCategoryClosed I C F

中文:
定义 functorCategoryMonoidalClosed
  签名: : 幺半群闭 (I ⥤ C) where
  定义体: functorCategoryClosed I C F

Depends on / 依赖: functorCategoryClosed
-/
def functorCategoryMonoidalClosed : MonoidalClosed (I ⥤ C) where
  closed F := functorCategoryClosed I C F

end

end CategoryTheory.Functor
