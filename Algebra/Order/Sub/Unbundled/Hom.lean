/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Order.Sub.Unbundled.Basic
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Order.Hom.Basic
/-!
# Lemmas about subtraction in unbundled canonically ordered monoids
-/

public section


variable {α β : Type*}

section Add

variable [Preorder α] [Add α] [Sub α] [OrderedSub α]

/--
theorem `AddHom.le_map_tsub` / 定理 `AddHom.le_map_tsub`

English:
theorem AddHom.le_map_tsub
  statement: [Preorder β] [Add β] [Sub β] [OrderedSub β] (f : AddHom α β)
  proof: by
  rw [tsub_le_iff_right]; rw [← f.map_add]
  exact hf le_tsub_add

中文:
定理 加法半群态射.le_map_tsub
  结论: [预序 β] [加法 β] [减法 β] [OrderedSub β] (f : 加法半群态射 α β)
  证明: by
  rw [tsub_le_iff_right]; rw [← f.map_add]
  exact hf le_tsub_add

Depends on / 依赖: f.map_add, le_tsub_add, map_add, tsub_le_iff_right
-/
theorem AddHom.le_map_tsub [Preorder β] [Add β] [Sub β] [OrderedSub β] (f : AddHom α β)
    (hf : Monotone f) (a b : α) : f a - f b <= f (a - b) := by
  rw [tsub_le_iff_right]; rw [← f.map_add]
  exact hf le_tsub_add

/--
theorem `le_mul_tsub` / 定理 `le_mul_tsub`

English:
theorem le_mul_tsub
  statement: {R : Type*} [Distrib R] [Preorder R] [Sub R] [OrderedSub R]
  proof: (AddHom.mulLeft a).le_map_tsub (monotone_id.const_mul' a) _ _

中文:
定理 le_mul_tsub
  结论: {R : 类型} [Distrib R] [预序 R] [减法 R] [OrderedSub R]
  证明: (AddHom.mulLeft a).le_map_tsub (monotone_id.const_mul' a) _ _

Depends on / 依赖: AddHom, AddHom.mulLeft, const_mul, le_map_tsub, monotone_id, monotone_id.const_mul, mulLeft
-/
theorem le_mul_tsub {R : Type*} [Distrib R] [Preorder R] [Sub R] [OrderedSub R]
    [MulLeftMono R] {a b c : R} : a * b - a * c <= a * (b - c) :=
  (AddHom.mulLeft a).le_map_tsub (monotone_id.const_mul' a) _ _

/--
theorem `le_tsub_mul` / 定理 `le_tsub_mul`

English:
theorem le_tsub_mul
  statement: {R : Type*} [NonUnitalCommSemiring R] [Preorder R] [Sub R] [OrderedSub R]
  proof: by
  simpa only [mul_comm _ c] using le_mul_tsub

中文:
定理 le_tsub_mul
  结论: {R : 类型} [非幺交换半环 R] [预序 R] [减法 R] [OrderedSub R]
  证明: by
  simpa only [mul_comm _ c] using le_mul_tsub

Depends on / 依赖: le_mul_tsub, mul_comm
-/
theorem le_tsub_mul {R : Type*} [NonUnitalCommSemiring R] [Preorder R] [Sub R] [OrderedSub R]
    [MulLeftMono R] {a b c : R} : a * c - b * c <= (a - b) * c := by
  simpa only [mul_comm _ c] using le_mul_tsub

end Add

/--
theorem `map_tsub_of_le` / 定理 `map_tsub_of_le`

English:
theorem map_tsub_of_le
  statement: {F : Type*} [PartialOrder α] [AddCommSemigroup α] [ExistsAddOfLE α]
  proof: by
  conv => lhs; rw [← tsub_add_cancel_of_le h]
  rw [map_add]; rw [add_tsub_cancel_right]

中文:
定理 map_tsub_of_le
  结论: {F : 类型} [偏序 α] [加法交换半群 α] [ExistsAddOfLE α]
  证明: by
  conv => lhs; rw [← tsub_add_cancel_of_le h]
  rw [map_add]; rw [add_tsub_cancel_right]

Depends on / 依赖: add_tsub_cancel_right, map_add, tsub_add_cancel_of_le
-/
theorem map_tsub_of_le {F : Type*} [PartialOrder α] [AddCommSemigroup α] [ExistsAddOfLE α]
    [AddLeftMono α] [Sub α] [OrderedSub α] [PartialOrder β] [AddCommSemigroup β] [Sub β]
    [OrderedSub β] [AddLeftReflectLE β] [FunLike F α β] [AddHomClass F α β]
    (f : F) (a b : α) (h : b <= a) : f a - f b = f (a - b) := by
  conv => lhs; rw [← tsub_add_cancel_of_le h]
  rw [map_add]; rw [add_tsub_cancel_right]

/--
theorem `OrderIso.map_tsub` / 定理 `OrderIso.map_tsub`

English:
theorem OrderIso.map_tsub
  statement: {M N : Type*} [Preorder M] [Add M] [Sub M] [OrderedSub M]
  proof: by
  let e_add : M ≃+ N := { e with map_add' := h_add }
  refine le_antisymm ?_ (e_add.toAddHom.le_map_tsub e.monotone a b)
  suffices e (e.symm (e a) - e.symm (e b)) <= e (e.symm (e a - e b)) by simpa
  exact e.monotone (e_add.symm.toAddHom.le_map_tsub e.symm.monotone _ _)

中文:
定理 OrderIso.map_tsub
  结论: {M N : 类型} [预序 M] [加法 M] [减法 M] [OrderedSub M]
  证明: by
  let e_add : M ≃+ N := { e with map_add' := h_add }
  refine le_antisymm ?_ (e_add.toAddHom.le_map_tsub e.monotone a b)
  suffices e (e.symm (e a) - e.symm (e b)) <= e (e.symm (e a - e b)) by simpa
  exact e.monotone (e_add.symm.toAddHom.le_map_tsub e.symm.monotone _ _)

Depends on / 依赖: e.monotone, e.symm, e.symm.monotone, e_add, e_add.symm.toAddHom.le_map_tsub, e_add.toAddHom.le_map_tsub, h_add, le_antisymm, le_map_tsub, map_add, monotone, toAddHom
-/
theorem OrderIso.map_tsub {M N : Type*} [Preorder M] [Add M] [Sub M] [OrderedSub M]
    [PartialOrder N] [Add N] [Sub N] [OrderedSub N] (e : M ≃o N)
    (h_add : forall a b, e (a + b) = e a + e b) (a b : M) : e (a - b) = e a - e b := by
  let e_add : M ≃+ N := { e with map_add' := h_add }
  refine le_antisymm ?_ (e_add.toAddHom.le_map_tsub e.monotone a b)
  suffices e (e.symm (e a) - e.symm (e b)) <= e (e.symm (e a - e b)) by simpa
  exact e.monotone (e_add.symm.toAddHom.le_map_tsub e.symm.monotone _ _)

/-! ### Preorder -/


section Preorder

variable [Preorder α]
variable [AddCommMonoid α] [Sub α] [OrderedSub α]

/--
theorem `AddMonoidHom.le_map_tsub` / 定理 `AddMonoidHom.le_map_tsub`

English:
theorem AddMonoidHom.le_map_tsub
  statement: [Preorder β] [AddZeroClass β] [Sub β] [OrderedSub β] (f : α ->+ β)
  proof: f.toAddHom.le_map_tsub hf a b

中文:
定理 加法幺半群态射.le_map_tsub
  结论: [预序 β] [加法零类 β] [减法 β] [OrderedSub β] (f : α ->+ β)
  证明: f.toAddHom.le_map_tsub hf a b

Depends on / 依赖: f.toAddHom.le_map_tsub, le_map_tsub, toAddHom
-/
theorem AddMonoidHom.le_map_tsub [Preorder β] [AddZeroClass β] [Sub β] [OrderedSub β] (f : α ->+ β)
    (hf : Monotone f) (a b : α) : f a - f b <= f (a - b) :=
  f.toAddHom.le_map_tsub hf a b

end Preorder
