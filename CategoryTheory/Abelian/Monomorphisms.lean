/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Monomorphisms are stable under cobase change

In an abelian category `C`, the class of morphisms
`monomorphisms C` is stable under cobase change and
`epimorphisms C` is stable under base change.

-/

public section

universe v u

namespace CategoryTheory.Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]

open MorphismProperty

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (monomorphisms C).IsStableUnderCobaseChange
  body: IsStableUnderCobaseChange.mk' (fun _ _ _ f g _ hf => by
    simp only [monomorphisms.iff] at hf ⊢
    infer_instance)

中文:
实例 :
  签名: (monomorphisms C).IsStableUnderCobaseChange
  定义体: IsStableUnderCobaseChange.mk' (fun _ _ _ f g _ hf => by
    simp only [monomorphisms.iff] at hf ⊢
    infer_instance)

Depends on / 依赖: IsStableUnderCobaseChange, IsStableUnderCobaseChange.mk, infer_instance, monomorphisms, monomorphisms.iff
-/
instance : (monomorphisms C).IsStableUnderCobaseChange :=
  IsStableUnderCobaseChange.mk' (fun _ _ _ f g _ hf => by
    simp only [monomorphisms.iff] at hf ⊢
    infer_instance)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (epimorphisms C).IsStableUnderBaseChange
  body: IsStableUnderBaseChange.mk' (fun _ _ _ f g _ hf => by
    simp only [epimorphisms.iff] at hf ⊢
    infer_instance)

中文:
实例 :
  签名: (epimorphisms C).IsStableUnderBaseChange
  定义体: IsStableUnderBaseChange.mk' (fun _ _ _ f g _ hf => by
    simp only [epimorphisms.iff] at hf ⊢
    infer_instance)

Depends on / 依赖: IsStableUnderBaseChange, IsStableUnderBaseChange.mk, epimorphisms, epimorphisms.iff, infer_instance
-/
instance : (epimorphisms C).IsStableUnderBaseChange :=
  IsStableUnderBaseChange.mk' (fun _ _ _ f g _ hf => by
    simp only [epimorphisms.iff] at hf ⊢
    infer_instance)

end CategoryTheory.Abelian
