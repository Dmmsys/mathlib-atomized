/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Yury Kudryashov, Neil Strickland
-/
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.GroupWithZero.Regular
public import Mathlib.Algebra.Ring.Defs

/-!
# Lemmas about regular elements in rings.
-/

public section


variable {α : Type*}

/--
theorem `isLeftRegular_of_non_zero_divisor` / 定理 `isLeftRegular_of_non_zero_divisor`

English:
theorem isLeftRegular_of_non_zero_divisor
  statement: [NonUnitalNonAssocRing α] (k : α)
  proof: by
  refine fun x y (h' : k * x = k * y) => sub_eq_zero.mp (h _ ?_)
  rw [mul_sub]; rw [sub_eq_zero]; rw [h']

中文:
定理 isLeftRegular_of_non_zero_divisor
  结论: [非幺非结合环 α] (k : α)
  证明: by
  refine fun x y (h' : k * x = k * y) => sub_eq_zero.mp (h _ ?_)
  rw [mul_sub]; rw [sub_eq_zero]; rw [h']

Depends on / 依赖: mul_sub, sub_eq_zero, sub_eq_zero.mp
-/
theorem isLeftRegular_of_non_zero_divisor [NonUnitalNonAssocRing α] (k : α)
    (h : forall x : α, k * x = 0 -> x = 0) : IsLeftRegular k := by
  refine fun x y (h' : k * x = k * y) => sub_eq_zero.mp (h _ ?_)
  rw [mul_sub]; rw [sub_eq_zero]; rw [h']

/--
theorem `isRightRegular_of_non_zero_divisor` / 定理 `isRightRegular_of_non_zero_divisor`

English:
theorem isRightRegular_of_non_zero_divisor
  statement: [NonUnitalNonAssocRing α] (k : α)
  proof: by
  refine fun x y (h' : x * k = y * k) => sub_eq_zero.mp (h _ ?_)
  rw [sub_mul]; rw [sub_eq_zero]; rw [h']

中文:
定理 isRightRegular_of_non_zero_divisor
  结论: [非幺非结合环 α] (k : α)
  证明: by
  refine fun x y (h' : x * k = y * k) => sub_eq_zero.mp (h _ ?_)
  rw [sub_mul]; rw [sub_eq_zero]; rw [h']

Depends on / 依赖: sub_eq_zero, sub_eq_zero.mp, sub_mul
-/
theorem isRightRegular_of_non_zero_divisor [NonUnitalNonAssocRing α] (k : α)
    (h : forall x : α, x * k = 0 -> x = 0) : IsRightRegular k := by
  refine fun x y (h' : x * k = y * k) => sub_eq_zero.mp (h _ ?_)
  rw [sub_mul]; rw [sub_eq_zero]; rw [h']

/--
theorem `IsRegular.of_ne_zero'` / 定理 `IsRegular.of_ne_zero'`

English:
theorem IsRegular.of_ne_zero'
  given: [NonUnitalNonAssocRing α] [NoZeroDivisors α] {k : α} (hk : k != 0)
  proof: ⟨isLeftRegular_of_non_zero_divisor k fun _ h =>
      (NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero h).resolve_left hk,
    isRightRegular_of_non_zero_divisor k fun _ h =>
      (NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero h).resolve_right hk⟩

@[deprecated (since := "2026-01-21")] alias isRegular_of_ne_zero' := IsRegular.of_ne_zero'

中文:
定理 是正则.of_ne_zero'
  条件: [非幺非结合环 α] [无零因子 α] {k : α} (hk : k != 0)
  证明: ⟨isLeftRegular_of_non_zero_divisor k fun _ h =>
      (NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero h).resolve_left hk,
    isRightRegular_of_non_zero_divisor k fun _ h =>
      (NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero h).resolve_right hk⟩

@[deprecated (since := "2026-01-21")] alias isRegular_of_ne_zero' := IsRegular.of_ne_zero'

Depends on / 依赖: NoZeroDivisors, NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero, eq_zero_or_eq_zero_of_mul_eq_zero, isLeftRegular_of_non_zero_divisor, isRightRegular_of_non_zero_divisor, resolve_left, resolve_right
-/
theorem IsRegular.of_ne_zero' [NonUnitalNonAssocRing α] [NoZeroDivisors α] {k : α} (hk : k != 0) :
    IsRegular k :=
  ⟨isLeftRegular_of_non_zero_divisor k fun _ h =>
      (NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero h).resolve_left hk,
    isRightRegular_of_non_zero_divisor k fun _ h =>
      (NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero h).resolve_right hk⟩

@[deprecated (since := "2026-01-21")] alias isRegular_of_ne_zero' := IsRegular.of_ne_zero'

/--
theorem `isRegular_iff_ne_zero'` / 定理 `isRegular_iff_ne_zero'`

English:
theorem isRegular_iff_ne_zero'
  statement: [Nontrivial α] [NonUnitalNonAssocRing α] [NoZeroDivisors α]
  proof: ⟨fun h => by
    rintro rfl
    exact not_not.mpr h.left not_isLeftRegular_zero, .of_ne_zero'⟩

中文:
定理 isRegular_iff_ne_zero'
  结论: [非平凡 α] [非幺非结合环 α] [无零因子 α]
  证明: ⟨fun h => by
    rintro rfl
    exact not_not.mpr h.left not_isLeftRegular_zero, .of_ne_zero'⟩

Depends on / 依赖: h.left, not_isLeftRegular_zero, not_not, not_not.mpr, of_ne_zero
-/
theorem isRegular_iff_ne_zero' [Nontrivial α] [NonUnitalNonAssocRing α] [NoZeroDivisors α]
    {k : α} : IsRegular k ↔ k != 0 :=
  ⟨fun h => by
    rintro rfl
    exact not_not.mpr h.left not_isLeftRegular_zero, .of_ne_zero'⟩

/--
lemma `NoZeroDivisors.toIsCancelMulZero` / 引理 `NoZeroDivisors.toIsCancelMulZero`

English:
lemma NoZeroDivisors.toIsCancelMulZero
  given: [NonUnitalNonAssocRing α] [NoZeroDivisors α]
  proof: (IsRegular.of_ne_zero' ha).1
  mul_right_cancel_of_ne_zero hb := (IsRegular.of_ne_zero' hb).2

中文:
引理 无零因子.toIsCancelMulZero
  条件: [非幺非结合环 α] [无零因子 α]
  证明: (IsRegular.of_ne_zero' ha).1
  mul_right_cancel_of_ne_zero hb := (IsRegular.of_ne_zero' hb).2

Depends on / 依赖: IsRegular, IsRegular.of_ne_zero, of_ne_zero
-/
lemma NoZeroDivisors.toIsCancelMulZero [NonUnitalNonAssocRing α] [NoZeroDivisors α] :
    IsCancelMulZero α where
  mul_left_cancel_of_ne_zero ha := (IsRegular.of_ne_zero' ha).1
  mul_right_cancel_of_ne_zero hb := (IsRegular.of_ne_zero' hb).2

namespace IsDedekindFiniteMonoid

variable [Ring α]

/--
theorem `iff_eq_of_mul_left_eq_one` / 定理 `iff_eq_of_mul_left_eq_one`

English:
theorem iff_eq_of_mul_left_eq_one
  proof: by
  refine (isDedekindFiniteMonoid_iff _).trans ⟨fun h x y z hxy hxz => ?_, fun h x y eq => ?_⟩
  · simpa [← mul_assoc, h hxz] using congr_arg (z * ·) hxy
have := h _ _ (1 - y * x + y) eq by
    rw [mul_add]; rw [mul_sub]; rw [← mul_assoc]; rw [eq]; rw [mul_one]; rw [one_mul]; rw [sub_self]; rw [zero_add]
  rwa [right_eq_add, sub_eq_zero, eq_comm] at this

中文:
定理 iff_eq_of_mul_left_eq_one
  证明: by
  refine (isDedekindFiniteMonoid_iff _).trans ⟨fun h x y z hxy hxz => ?_, fun h x y eq => ?_⟩
  · simpa [← mul_assoc, h hxz] using congr_arg (z * ·) hxy
have := h _ _ (1 - y * x + y) eq by
    rw [mul_add]; rw [mul_sub]; rw [← mul_assoc]; rw [eq]; rw [mul_one]; rw [one_mul]; rw [sub_self]; rw [zero_add]
  rwa [right_eq_add, sub_eq_zero, eq_comm] at this

Depends on / 依赖: congr_arg, eq_comm, isDedekindFiniteMonoid_iff, mul_add, mul_assoc, mul_one, mul_sub, one_mul, right_eq_add, sub_eq_zero, sub_self, zero_add
-/
theorem iff_eq_of_mul_left_eq_one :
    IsDedekindFiniteMonoid α ↔ forall x y z : α, x * y = 1 -> x * z = 1 -> y = z := by
  refine (isDedekindFiniteMonoid_iff _).trans ⟨fun h x y z hxy hxz => ?_, fun h x y eq => ?_⟩
  · simpa [← mul_assoc, h hxz] using congr_arg (z * ·) hxy
have := h _ _ (1 - y * x + y) eq by
    rw [mul_add]; rw [mul_sub]; rw [← mul_assoc]; rw [eq]; rw [mul_one]; rw [one_mul]; rw [sub_self]; rw [zero_add]
  rwa [right_eq_add, sub_eq_zero, eq_comm] at this

/--
theorem `iff_eq_of_mul_right_eq_one` / 定理 `iff_eq_of_mul_right_eq_one`

English:
theorem iff_eq_of_mul_right_eq_one
  proof: by
  refine (isDedekindFiniteMonoid_iff _).trans ⟨fun h x y z hxz hyz => ?_, fun h x y eq => ?_⟩
  · simpa [mul_assoc, h hyz] using congr_arg (· * y) hxz
have := h _ (1 - y * x + x) _ eq by
    rw [add_mul]; rw [sub_mul]; rw [mul_assoc]; rw [eq]; rw [one_mul]; rw [mul_one]; rw [sub_self]; rw [zero_add]
  rwa [right_eq_add, sub_eq_zero, eq_comm] at this

中文:
定理 iff_eq_of_mul_right_eq_one
  证明: by
  refine (isDedekindFiniteMonoid_iff _).trans ⟨fun h x y z hxz hyz => ?_, fun h x y eq => ?_⟩
  · simpa [mul_assoc, h hyz] using congr_arg (· * y) hxz
have := h _ (1 - y * x + x) _ eq by
    rw [add_mul]; rw [sub_mul]; rw [mul_assoc]; rw [eq]; rw [one_mul]; rw [mul_one]; rw [sub_self]; rw [zero_add]
  rwa [right_eq_add, sub_eq_zero, eq_comm] at this

Depends on / 依赖: add_mul, congr_arg, eq_comm, isDedekindFiniteMonoid_iff, mul_assoc, mul_one, one_mul, right_eq_add, sub_eq_zero, sub_mul, sub_self, zero_add
-/
theorem iff_eq_of_mul_right_eq_one :
    IsDedekindFiniteMonoid α ↔ forall x y z : α, x * z = 1 -> y * z = 1 -> x = y := by
  refine (isDedekindFiniteMonoid_iff _).trans ⟨fun h x y z hxz hyz => ?_, fun h x y eq => ?_⟩
  · simpa [mul_assoc, h hyz] using congr_arg (· * y) hxz
have := h _ (1 - y * x + x) _ eq by
    rw [add_mul]; rw [sub_mul]; rw [mul_assoc]; rw [eq]; rw [one_mul]; rw [mul_one]; rw [sub_self]; rw [zero_add]
  rwa [right_eq_add, sub_eq_zero, eq_comm] at this

end IsDedekindFiniteMonoid
