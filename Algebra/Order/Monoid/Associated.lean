/-
Copyright (c) 2022 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
module

public import Mathlib.Algebra.GroupWithZero.Associated
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs

/-!
# Order on associates

This file shows that divisibility makes associates into a canonically ordered monoid.
-/

public section

variable {M : Type*} [CommMonoidWithZero M]

namespace Associates

/--
Instance `instIsOrderedMonoid` / 实例 `instIsOrderedMonoid`

English:
instance instIsOrderedMonoid
  signature: : IsOrderedMonoid (Associates M) where
  body: by rintro a _ ⟨d, rfl⟩ c; exact ⟨d, mul_right_comm ..⟩

中文:
实例 instIsOrderedMonoid
  签名: : IsOrderedMonoid (Associates M) where
  定义体: by rintro a _ ⟨d, rfl⟩ c; exact ⟨d, mul_right_comm ..⟩

Depends on / 依赖: mul_right_comm
-/
instance instIsOrderedMonoid : IsOrderedMonoid (Associates M) where
  mul_le_mul_left := by rintro a _ ⟨d, rfl⟩ c; exact ⟨d, mul_right_comm ..⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CanonicallyOrderedMul (Associates M)
  body: h
  le_mul_self _ b := ⟨b, mul_comm ..⟩
  le_self_mul _ b := ⟨b, rfl⟩

中文:
实例 :
  签名: CanonicallyOrderedMul (Associates M)
  定义体: h
  le_mul_self _ b := ⟨b, mul_comm ..⟩
  le_self_mul _ b := ⟨b, rfl⟩
-/
instance : CanonicallyOrderedMul (Associates M) where
  exists_mul_of_le h := h
  le_mul_self _ b := ⟨b, mul_comm ..⟩
  le_self_mul _ b := ⟨b, rfl⟩

end Associates
