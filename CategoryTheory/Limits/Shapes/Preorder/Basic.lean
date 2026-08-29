/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Preorder

/-!
# Limits and colimits indexed by preorders

In this file, we obtain the following very basic results
about limits and colimits indexed by a preordered type `J`:
* a least element in `J` implies the existence of all limits indexed by `J`
* a greatest element in `J` implies the existence of all colimits indexed by `J`

-/

public section

universe v v' u u' w

open CategoryTheory Limits

variable (C : Type u) [Category.{v} C] (J : Type w) [Preorder J]

namespace Preorder

section OrderBot

variable [OrderBot J]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasLimitsOfShape J C
  body: ⟨fun _ => by infer_instance⟩

中文:
实例 :
  签名: HasLimitsOfShape J C
  定义体: ⟨fun _ => by infer_instance⟩

Depends on / 依赖: infer_instance
-/
instance : HasLimitsOfShape J C := ⟨fun _ => by infer_instance⟩

end OrderBot

section OrderTop

variable [OrderTop J]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasColimitsOfShape J C
  body: ⟨fun _ => by infer_instance⟩

中文:
实例 :
  签名: HasColimitsOfShape J C
  定义体: ⟨fun _ => by infer_instance⟩

Depends on / 依赖: infer_instance
-/
instance : HasColimitsOfShape J C := ⟨fun _ => by infer_instance⟩

end OrderTop

end Preorder
