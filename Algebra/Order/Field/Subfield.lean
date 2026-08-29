/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Order.Ring.InjSurj

/-!
# Ordered instances on subfields
-/

public section

namespace Subfield
variable {K : Type*}

/--
Instance `toIsStrictOrderedRing` / 实例 `toIsStrictOrderedRing`

English:
instance toIsStrictOrderedRing
  signature: [Field K] [LinearOrder K] [IsStrictOrderedRing K] (s : Subfield K)
  body: Function.Injective.isStrictOrderedRing
    Subtype.val rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) .rfl .rfl

中文:
实例 toIsStrictOrderedRing
  签名: [Field K] [LinearOrder K] [IsStrictOrderedRing K] (s : Subfield K)
  定义体: Function.Injective.isStrictOrderedRing
    Subtype.val rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) .rfl .rfl

Depends on / 依赖: Function, Function.Injective.isStrictOrderedRing, Injective, Subtype, Subtype.val, isStrictOrderedRing
-/
instance toIsStrictOrderedRing [Field K] [LinearOrder K] [IsStrictOrderedRing K] (s : Subfield K) :
    IsStrictOrderedRing s :=
  Function.Injective.isStrictOrderedRing
    Subtype.val rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) .rfl .rfl

end Subfield
