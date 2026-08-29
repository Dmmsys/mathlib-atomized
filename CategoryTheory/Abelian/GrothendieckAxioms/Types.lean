/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

/-!
# The category of types satisfies Grothendieck's AB5 axiom

This is of course just the well-known fact that filtered colimits commute with finite limits in
the category of types.
-/

public section

universe v

namespace CategoryTheory.Limits

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AB5 (Type v)
  body: ⟨inferInstance⟩

中文:
实例 :
  签名: AB5 (类型v)
  定义体: ⟨inferInstance⟩
-/
instance : AB5 (Type v) where
  ofShape _ _ _ := ⟨inferInstance⟩

end CategoryTheory.Limits
