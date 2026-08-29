/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Jonas van der Schaaf
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Retract

/-!

# Internal projectivity

This file defines internal projectivity of objects `P` in a category `C` as a class
`InternallyProjective P`. This means that the functor taking internal homs out of `P`
preserves epimorphisms. It also proves that a retract of an internally projective object
is internally projective (see `InternallyProjective.ofRetract`).

This property is important in the setting of light condensed abelian groups, when establishing
the solid theory (see the lecture series on analytic stacks:
https://www.youtube.com/playlist?list=PLx5f8IelFRgGmu6gmL-Kf_Rl_6Mm7juZO).
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed Limits Functor

namespace CategoryTheory

variable {C : Type*} [Category* C] [MonoidalCategory C] [MonoidalClosed C]

/--
Definition of `isInternallyProjective` / `isInternallyProjective` 的定义

English:
definition isInternallyProjective
  signature: : ObjectProperty C
  body: fun P => (ihom P).PreservesEpimorphisms

中文:
定义 is整数ernallyProjective
  签名: : ObjectProperty C
  定义体: fun P => (ihom P).PreservesEpimorphisms

Depends on / 依赖: PreservesEpimorphisms
-/
def isInternallyProjective : ObjectProperty C := fun P => (ihom P).PreservesEpimorphisms

/--
Definition of `InternallyProjective` / `InternallyProjective` 的定义

English:
abbreviation InternallyProjective
  signature: (P : C)
  body: isInternallyProjective.Is P

中文:
缩写 整数ernallyProjective
  签名: (P : C)
  定义体: isInternallyProjective.Is P

Depends on / 依赖: isInternallyProjective, isInternallyProjective.Is
-/
abbrev InternallyProjective (P : C) := isInternallyProjective.Is P

/--
Instance `InternallyProjective.preserves_epi` / 实例 `InternallyProjective.preserves_epi`

English:
instance InternallyProjective.preserves_epi
  signature: (P : C) [InternallyProjective P]
  body: isInternallyProjective.prop_of_is P

中文:
实例 整数ernallyProjective.preserves_epi
  签名: (P : C) [整数ernallyProjective P]
  定义体: isInternallyProjective.prop_of_is P

Depends on / 依赖: isInternallyProjective, isInternallyProjective.prop_of_is, prop_of_is
-/
instance InternallyProjective.preserves_epi (P : C) [InternallyProjective P] :
    (ihom P).PreservesEpimorphisms :=
  isInternallyProjective.prop_of_is P

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (isInternallyProjective (C := C)).IsStableUnderRetracts
  body: have : InternallyProjective X := ⟨h⟩
    have : Retract (ihom Y) (ihom X) := r.op.map internalHom
    PreservesEpimorphisms.ofRetract this

中文:
实例 :
  签名: (is整数ernallyProjective (C := C)).是StableUnderRetracts
  定义体: have : InternallyProjective X := ⟨h⟩
    have : Retract (ihom Y) (ihom X) := r.op.map internalHom
    PreservesEpimorphisms.ofRetract this

Depends on / 依赖: IsStableUnderRetracts
-/
instance : (isInternallyProjective (C := C)).IsStableUnderRetracts where
  of_retract {Y X} r h :=
    have : InternallyProjective X := ⟨h⟩
    have : Retract (ihom Y) (ihom X) := r.op.map internalHom
    PreservesEpimorphisms.ofRetract this

namespace InternallyProjective

/--
lemma `ofRetract` / 引理 `ofRetract`

English:
lemma ofRetract
  given: {X Y : C} (r : Retract Y X) [InternallyProjective X]
  statement: InternallyProjective Y
  proof: ⟨isInternallyProjective.prop_of_retract r (isInternallyProjective.prop_of_is _)⟩

中文:
引理 ofRetract
  条件: {X Y : C} (r : 收缩 Y X) [整数ernallyProjective X]
  结论: 整数ernallyProjective Y
  证明: ⟨isInternallyProjective.prop_of_retract r (isInternallyProjective.prop_of_is _)⟩

Depends on / 依赖: isInternallyProjective, isInternallyProjective.prop_of_is, isInternallyProjective.prop_of_retract, prop_of_is, prop_of_retract
-/
lemma ofRetract {X Y : C} (r : Retract Y X) [InternallyProjective X] : InternallyProjective Y :=
  ⟨isInternallyProjective.prop_of_retract r (isInternallyProjective.prop_of_is _)⟩

end CategoryTheory.InternallyProjective
