/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.EffectiveEpi.Basic
/-!

# Effectively enough objects in the image of a functor

We define the class `F.EffectivelyEnough` on a functor `F : C ⥤ D` which says that for every object
in `D`, there exists an effective epi to it from an object in the image of `F`.
-/

@[expose] public section

namespace CategoryTheory

open Limits

variable {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)

namespace Functor

/--
Definition of `EffectivePresentation` / `EffectivePresentation` 的定义

English:
structure EffectivePresentation
  parameters: (X : D)
  axioms and operations (3):
    - p : C
    - f : F.obj p ⟶ X
    - effectiveEpi : EffectiveEpi f

中文:
结构 EffectivePresentation
  参数: (X : D)
  公理与运算 (3 个):
    - p : C
    - f : F.obj p ⟶ X
    - effectiveEpi : EffectiveEpi f
-/
structure EffectivePresentation (X : D) where
  /-- The object of `C` giving the source of the effective epi -/
  p : C
  /-- The morphism `F.obj p ⟶ X` -/
  f : F.obj p ⟶ X
  /-- `f` is an effective epi -/
  effectiveEpi : EffectiveEpi f

/--
Definition of `EffectivelyEnough` / `EffectivelyEnough` 的定义

English:
class EffectivelyEnough
  parameters: : Prop where
  axioms and operations (1):
    - presentation : forall (X : D), Nonempty (F.EffectivePresentation X)

中文:
类 EffectivelyEnough
  参数: : 命题 where
  公理与运算 (1 个):
    - presentation : 对任意 (X : D), Nonempty (F.EffectivePresentation X)
-/
class EffectivelyEnough : Prop where
  /-- For every `X : D`, there exists an object `p` of `C` with an effective epi `F.obj p ⟶ X`. -/
  presentation : forall (X : D), Nonempty (F.EffectivePresentation X)

variable [F.EffectivelyEnough]

/--
Definition of `effectiveEpiOverObj` / `effectiveEpiOverObj` 的定义

English:
definition effectiveEpiOverObj
  signature: (X : D)
  body: F.obj (EffectivelyEnough.presentation (F := F) X).some.p

中文:
定义 effectiveEpiOverObj
  签名: (X : D)
  定义体: F.obj (EffectivelyEnough.presentation (F := F) X).some.p

Depends on / 依赖: EffectivelyEnough, EffectivelyEnough.presentation, F.obj, presentation, some.p
-/
noncomputable def effectiveEpiOverObj (X : D) : D :=
  F.obj (EffectivelyEnough.presentation (F := F) X).some.p

/--
Definition of `effectiveEpiOver` / `effectiveEpiOver` 的定义

English:
definition effectiveEpiOver
  signature: (X : D)
  body: (EffectivelyEnough.presentation X).some.f

中文:
定义 effectiveEpiOver
  签名: (X : D)
  定义体: (EffectivelyEnough.presentation X).some.f

Depends on / 依赖: EffectivelyEnough, EffectivelyEnough.presentation, presentation, some.f
-/
noncomputable def effectiveEpiOver (X : D) : F.effectiveEpiOverObj X ⟶ X :=
  (EffectivelyEnough.presentation X).some.f

instance (X : D) : EffectiveEpi (F.effectiveEpiOver X) :=
  (EffectivelyEnough.presentation X).some.effectiveEpi

/--
Definition of `equivalenceEffectivePresentation` / `equivalenceEffectivePresentation` 的定义

English:
definition equivalenceEffectivePresentation
  signature: (e : C ≌ D) (X : D)
  body: e.inverse.obj X
  f := e.counit.app _
  effectiveEpi := inferInstance

中文:
定义 equivalenceEffectivePresentation
  签名: (e : C ≌ D) (X : D)
  定义体: e.inverse.obj X
  f := e.counit.app _
  effectiveEpi := inferInstance

Depends on / 依赖: e.inverse.obj, inverse
-/
def equivalenceEffectivePresentation (e : C ≌ D) (X : D) :
    EffectivePresentation e.functor X where
  p := e.inverse.obj X
  f := e.counit.app _
  effectiveEpi := inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsEquivalence
  signature: F] : EffectivelyEnough F where
  body: ⟨equivalenceEffectivePresentation F.asEquivalence X⟩

中文:
实例 [IsEquivalence
  签名: F] : EffectivelyEnough F where
  定义体: ⟨equivalenceEffectivePresentation F.asEquivalence X⟩

Depends on / 依赖: F.asEquivalence, asEquivalence, equivalenceEffectivePresentation
-/
instance [IsEquivalence F] : EffectivelyEnough F where
  presentation X := ⟨equivalenceEffectivePresentation F.asEquivalence X⟩

end Functor

end CategoryTheory
