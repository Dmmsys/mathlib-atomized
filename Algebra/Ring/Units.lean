/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Yury Kudryashov, Neil Strickland
-/
module

public import Mathlib.Algebra.Ring.InjSurj
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.Ring.Hom.Defs

/-!
# Units in semirings and rings

-/

public section


universe u v w x

variable {α : Type u} {β : Type v} {R : Type x}

open Function

namespace Units

section HasDistribNeg

variable [Monoid α] [HasDistribNeg α]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Neg αˣ
  body: ⟨fun u => ⟨-↑u, -↑u⁻¹, by simp, by simp⟩⟩

中文:
实例 :
  签名: 取负 αˣ
  定义体: ⟨fun u => ⟨-↑u, -↑u⁻¹, by simp, by simp⟩⟩
-/
instance : Neg αˣ :=
  ⟨fun u => ⟨-↑u, -↑u⁻¹, by simp, by simp⟩⟩

/-- Representing an element of a ring's unit group as an element of the ring commutes with
mapping this element to its additive inverse. -/
@[simp, norm_cast]
/--
theorem `val_neg` / 定理 `val_neg`

English:
theorem val_neg
  given: (u : αˣ)
  statement: (↑(-u) : α) = -u
  proof: rfl

@[simp, norm_cast]

中文:
定理 val_neg
  条件: (u : αˣ)
  结论: (↑(-u) : α) = -u
  证明: rfl

@[simp, norm_cast]
-/
protected theorem val_neg (u : αˣ) : (↑(-u) : α) = -u :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_neg_one` / 定理 `coe_neg_one`

English:
theorem coe_neg_one
  statement: ((-1 : αˣ) : α) = -1
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_neg_one
  结论: ((-1 : αˣ) : α) = -1
  证明: rfl

@[simp, norm_cast]
-/
protected theorem coe_neg_one : ((-1 : αˣ) : α) = -1 :=
  rfl

@[simp, norm_cast]
/--
theorem `val_eq_neg_one` / 定理 `val_eq_neg_one`

English:
theorem val_eq_neg_one
  given: {a : αˣ}
  statement: (a : α) = -1 ↔ a = -1
  proof: by
  rw [← Units.coe_neg_one]; rw [val_inj]

中文:
定理 val_eq_neg_one
  条件: {a : αˣ}
  结论: (a : α) = -1 ↔ a = -1
  证明: by
  rw [← Units.coe_neg_one]; rw [val_inj]

Depends on / 依赖: Units.coe_neg_one, coe_neg_one, val_inj
-/
theorem val_eq_neg_one {a : αˣ} : (a : α) = -1 ↔ a = -1 := by
  rw [← Units.coe_neg_one]; rw [val_inj]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasDistribNeg αˣ
  body: val_injective.hasDistribNeg _ Units.val_neg val_mul

中文:
实例 :
  签名: 有DistribNeg αˣ
  定义体: val_injective.hasDistribNeg _ Units.val_neg val_mul

Depends on / 依赖: Units.val_neg, hasDistribNeg, val_injective, val_injective.hasDistribNeg, val_mul, val_neg
-/
instance : HasDistribNeg αˣ := val_injective.hasDistribNeg _ Units.val_neg val_mul

/--
theorem `neg_divp` / 定理 `neg_divp`

English:
theorem neg_divp
  given: (a : α) (u : αˣ)
  statement: -(a /ₚ u) = -a /ₚ u
  proof: by simp only [divp, neg_mul]

中文:
定理 neg_divp
  条件: (a : α) (u : αˣ)
  结论: -(a /ₚ u) = -a /ₚ u
  证明: by simp only [divp, neg_mul]

Depends on / 依赖: neg_mul
-/
theorem neg_divp (a : α) (u : αˣ) : -(a /ₚ u) = -a /ₚ u := by simp only [divp, neg_mul]

end HasDistribNeg

section Semiring

variable [Semiring α]

/--
theorem `divp_add_divp_same` / 定理 `divp_add_divp_same`

English:
theorem divp_add_divp_same
  given: (a b : α) (u : αˣ)
  statement: a /ₚ u + b /ₚ u = (a + b) /ₚ u
  proof: by
  simp only [divp, add_mul]

中文:
定理 divp_add_divp_same
  条件: (a b : α) (u : αˣ)
  结论: a /ₚ u + b /ₚ u = (a + b) /ₚ u
  证明: by
  simp only [divp, add_mul]

Depends on / 依赖: add_mul
-/
theorem divp_add_divp_same (a b : α) (u : αˣ) : a /ₚ u + b /ₚ u = (a + b) /ₚ u := by
  simp only [divp, add_mul]

/--
theorem `add_divp` / 定理 `add_divp`

English:
theorem add_divp
  given: (a b : α) (u : αˣ)
  statement: a + b /ₚ u = (a * u + b) /ₚ u
  proof: by
  simp only [divp, add_mul, Units.mul_inv_cancel_right]

中文:
定理 add_divp
  条件: (a b : α) (u : αˣ)
  结论: a + b /ₚ u = (a * u + b) /ₚ u
  证明: by
  simp only [divp, add_mul, Units.mul_inv_cancel_right]

Depends on / 依赖: Units.mul_inv_cancel_right, add_mul, mul_inv_cancel_right
-/
theorem add_divp (a b : α) (u : αˣ) : a + b /ₚ u = (a * u + b) /ₚ u := by
  simp only [divp, add_mul, Units.mul_inv_cancel_right]

/--
theorem `divp_add` / 定理 `divp_add`

English:
theorem divp_add
  given: (a b : α) (u : αˣ)
  statement: a /ₚ u + b = (a + b * u) /ₚ u
  proof: by
  simp only [divp, add_mul, Units.mul_inv_cancel_right]

中文:
定理 divp_add
  条件: (a b : α) (u : αˣ)
  结论: a /ₚ u + b = (a + b * u) /ₚ u
  证明: by
  simp only [divp, add_mul, Units.mul_inv_cancel_right]

Depends on / 依赖: Units.mul_inv_cancel_right, add_mul, mul_inv_cancel_right
-/
theorem divp_add (a b : α) (u : αˣ) : a /ₚ u + b = (a + b * u) /ₚ u := by
  simp only [divp, add_mul, Units.mul_inv_cancel_right]

end Semiring

section Ring

variable [Ring α]

/--
theorem `divp_sub_divp_same` / 定理 `divp_sub_divp_same`

English:
theorem divp_sub_divp_same
  given: (a b : α) (u : αˣ)
  statement: a /ₚ u - b /ₚ u = (a - b) /ₚ u
  proof: by
  rw [sub_eq_add_neg]; rw [sub_eq_add_neg]; rw [neg_divp]; rw [divp_add_divp_same]

中文:
定理 divp_sub_divp_same
  条件: (a b : α) (u : αˣ)
  结论: a /ₚ u - b /ₚ u = (a - b) /ₚ u
  证明: by
  rw [sub_eq_add_neg]; rw [sub_eq_add_neg]; rw [neg_divp]; rw [divp_add_divp_same]

Depends on / 依赖: divp_add_divp_same, neg_divp, sub_eq_add_neg
-/
theorem divp_sub_divp_same (a b : α) (u : αˣ) : a /ₚ u - b /ₚ u = (a - b) /ₚ u := by
  rw [sub_eq_add_neg]; rw [sub_eq_add_neg]; rw [neg_divp]; rw [divp_add_divp_same]

/--
theorem `sub_divp` / 定理 `sub_divp`

English:
theorem sub_divp
  given: (a b : α) (u : αˣ)
  statement: a - b /ₚ u = (a * u - b) /ₚ u
  proof: by
  simp only [divp, sub_mul, Units.mul_inv_cancel_right]

中文:
定理 sub_divp
  条件: (a b : α) (u : αˣ)
  结论: a - b /ₚ u = (a * u - b) /ₚ u
  证明: by
  simp only [divp, sub_mul, Units.mul_inv_cancel_right]

Depends on / 依赖: Units.mul_inv_cancel_right, mul_inv_cancel_right, sub_mul
-/
theorem sub_divp (a b : α) (u : αˣ) : a - b /ₚ u = (a * u - b) /ₚ u := by
  simp only [divp, sub_mul, Units.mul_inv_cancel_right]

/--
theorem `divp_sub` / 定理 `divp_sub`

English:
theorem divp_sub
  given: (a b : α) (u : αˣ)
  statement: a /ₚ u - b = (a - b * u) /ₚ u
  proof: by
  simp only [divp, sub_mul, sub_right_inj]
  rw [mul_assoc]; rw [Units.mul_inv]; rw [mul_one]

@[simp]

中文:
定理 divp_sub
  条件: (a b : α) (u : αˣ)
  结论: a /ₚ u - b = (a - b * u) /ₚ u
  证明: by
  simp only [divp, sub_mul, sub_right_inj]
  rw [mul_assoc]; rw [Units.mul_inv]; rw [mul_one]

@[simp]

Depends on / 依赖: Units.mul_inv, mul_assoc, mul_inv, mul_one, sub_mul, sub_right_inj
-/
theorem divp_sub (a b : α) (u : αˣ) : a /ₚ u - b = (a - b * u) /ₚ u := by
  simp only [divp, sub_mul, sub_right_inj]
  rw [mul_assoc]; rw [Units.mul_inv]; rw [mul_one]

@[simp]
/--
theorem `map_neg` / 定理 `map_neg`

English:
theorem map_neg
  statement: {F : Type*} [Ring β] [FunLike F α β] [RingHomClass F α β]
  proof: ext (by simp only [coe_map, Units.val_neg, MonoidHom.coe_coe, map_neg])

中文:
定理 map_neg
  结论: {F : 类型} [环 β] [函数状 F α β] [环态射类 F α β]
  证明: ext (by simp only [coe_map, Units.val_neg, MonoidHom.coe_coe, map_neg])
-/
protected theorem map_neg {F : Type*} [Ring β] [FunLike F α β] [RingHomClass F α β]
    (f : F) (u : αˣ) : map (f : α ->* β) (-u) = -map (f : α ->* β) u :=
  ext (by simp only [coe_map, Units.val_neg, MonoidHom.coe_coe, map_neg])

/--
theorem `map_neg_one` / 定理 `map_neg_one`

English:
theorem map_neg_one
  statement: {F : Type*} [Ring β] [FunLike F α β] [RingHomClass F α β]
  proof: by
  simp only [Units.map_neg, map_one]

中文:
定理 map_neg_one
  结论: {F : 类型} [环 β] [函数状 F α β] [环态射类 F α β]
  证明: by
  simp only [Units.map_neg, map_one]
-/
protected theorem map_neg_one {F : Type*} [Ring β] [FunLike F α β] [RingHomClass F α β]
    (f : F) : map (f : α ->* β) (-1) = -1 := by
  simp only [Units.map_neg, map_one]

end Ring

end Units

/--
theorem `IsUnit.neg` / 定理 `IsUnit.neg`

English:
theorem IsUnit.neg
  given: [Monoid α] [HasDistribNeg α] {a : α}
  statement: IsUnit a -> IsUnit (-a)

中文:
定理 是单位.neg
  条件: [幺半群 α] [有DistribNeg α] {a : α}
  结论: 是单位 a -> 是单位 (-a)
-/
theorem IsUnit.neg [Monoid α] [HasDistribNeg α] {a : α} : IsUnit a -> IsUnit (-a)
  | ⟨x, hx⟩ => hx ▸ (-x).isUnit

@[simp]
/--
theorem `IsUnit.neg_iff` / 定理 `IsUnit.neg_iff`

English:
theorem IsUnit.neg_iff
  given: [Monoid α] [HasDistribNeg α] (a : α)
  statement: IsUnit (-a) ↔ IsUnit a
  proof: ⟨fun h => neg_neg a ▸ h.neg, IsUnit.neg⟩

中文:
定理 是单位.neg_iff
  条件: [幺半群 α] [有DistribNeg α] (a : α)
  结论: 是单位 (-a) ↔ 是单位 a
  证明: ⟨fun h => neg_neg a ▸ h.neg, IsUnit.neg⟩

Depends on / 依赖: IsUnit, IsUnit.neg, h.neg, neg_neg
-/
theorem IsUnit.neg_iff [Monoid α] [HasDistribNeg α] (a : α) : IsUnit (-a) ↔ IsUnit a :=
  ⟨fun h => neg_neg a ▸ h.neg, IsUnit.neg⟩

/--
theorem `isUnit_neg_one` / 定理 `isUnit_neg_one`

English:
theorem isUnit_neg_one
  given: [Monoid α] [HasDistribNeg α]
  statement: IsUnit (-1 : α)
  proof: isUnit_one.neg

中文:
定理 isUnit_neg_one
  条件: [幺半群 α] [有DistribNeg α]
  结论: 是单位 (-1 : α)
  证明: isUnit_one.neg

Depends on / 依赖: isUnit_one, isUnit_one.neg
-/
theorem isUnit_neg_one [Monoid α] [HasDistribNeg α] : IsUnit (-1 : α) := isUnit_one.neg

/--
theorem `IsUnit.sub_iff` / 定理 `IsUnit.sub_iff`

English:
theorem IsUnit.sub_iff
  given: [Ring α] {x y : α}
  statement: IsUnit (x - y) ↔ IsUnit (y - x)
  proof: (IsUnit.neg_iff _).symm.trans neg_sub x y ▸ Iff.rfl

中文:
定理 是单位.sub_iff
  条件: [环 α] {x y : α}
  结论: 是单位 (x - y) ↔ 是单位 (y - x)
  证明: (IsUnit.neg_iff _).symm.trans neg_sub x y ▸ Iff.rfl

Depends on / 依赖: Iff.rfl, IsUnit, IsUnit.neg_iff, neg_iff, neg_sub, symm.trans
-/
theorem IsUnit.sub_iff [Ring α] {x y : α} : IsUnit (x - y) ↔ IsUnit (y - x) :=
(IsUnit.neg_iff _).symm.trans neg_sub x y ▸ Iff.rfl

namespace Units

/--
theorem `divp_add_divp` / 定理 `divp_add_divp`

English:
theorem divp_add_divp
  given: [CommSemiring α] (a b : α) (u₁ u₂ : αˣ)
  proof: by
  simp only [divp, add_mul, mul_inv_rev, val_mul]
  rw [mul_comm (↑u₁ * b)]; rw [mul_comm b]
  rw [← mul_assoc]; rw [← mul_assoc]; rw [mul_assoc a]; rw [mul_assoc (↑u₂⁻¹ : α)]; rw [mul_inv]; rw [inv_mul]; rw [mul_one]; rw [mul_one]
  -- Porting note: `assoc_rw` not ported: `assoc_rw [mul_inv, mul

中文:
定理 divp_add_divp
  条件: [交换半环 α] (a b : α) (u₁ u₂ : αˣ)
  证明: by
  simp only [divp, add_mul, mul_inv_rev, val_mul]
  rw [mul_comm (↑u₁ * b)]; rw [mul_comm b]
  rw [← mul_assoc]; rw [← mul_assoc]; rw [mul_assoc a]; rw [mul_assoc (↑u₂⁻¹ : α)]; rw [mul_inv]; rw [inv_mul]; rw [mul_one]; rw [mul_one]
  -- Porting note: `assoc_rw` not ported: `assoc_rw [mul_inv, mul

Depends on / 依赖: add_mul, inv_mul, mul_assoc, mul_comm, mul_inv, mul_inv_rev, mul_one, val_mul
-/
theorem divp_add_divp [CommSemiring α] (a b : α) (u₁ u₂ : αˣ) :
    a /ₚ u₁ + b /ₚ u₂ = (a * u₂ + u₁ * b) /ₚ (u₁ * u₂) := by
  simp only [divp, add_mul, mul_inv_rev, val_mul]
  rw [mul_comm (↑u₁ * b)]; rw [mul_comm b]
  rw [← mul_assoc]; rw [← mul_assoc]; rw [mul_assoc a]; rw [mul_assoc (↑u₂⁻¹ : α)]; rw [mul_inv]; rw [inv_mul]; rw [mul_one]; rw [mul_one]
  -- Porting note: `assoc_rw` not ported: `assoc_rw [mul_inv, mul_inv, mul_one, mul_one]`

/--
theorem `divp_sub_divp` / 定理 `divp_sub_divp`

English:
theorem divp_sub_divp
  given: [CommRing α] (a b : α) (u₁ u₂ : αˣ)
  proof: by
  simp only [sub_eq_add_neg, neg_divp, divp_add_divp, mul_neg]

中文:
定理 divp_sub_divp
  条件: [交换环 α] (a b : α) (u₁ u₂ : αˣ)
  证明: by
  simp only [sub_eq_add_neg, neg_divp, divp_add_divp, mul_neg]

Depends on / 依赖: divp_add_divp, mul_neg, neg_divp, sub_eq_add_neg
-/
theorem divp_sub_divp [CommRing α] (a b : α) (u₁ u₂ : αˣ) :
    a /ₚ u₁ - b /ₚ u₂ = (a * u₂ - u₁ * b) /ₚ (u₁ * u₂) := by
  simp only [sub_eq_add_neg, neg_divp, divp_add_divp, mul_neg]

/--
theorem `add_eq_mul_one_add_div` / 定理 `add_eq_mul_one_add_div`

English:
theorem add_eq_mul_one_add_div
  given: [Semiring R] {a : Rˣ} {b : R}
  statement: ↑a + b = a * (1 + ↑a⁻¹ * b)
  proof: by
  rw [mul_add]; rw [mul_one]; rw [← mul_assoc]; rw [Units.mul_inv]; rw [one_mul]

中文:
定理 add_eq_mul_one_add_div
  条件: [半环 R] {a : Rˣ} {b : R}
  结论: ↑a + b = a * (1 + ↑a⁻¹ * b)
  证明: by
  rw [mul_add]; rw [mul_one]; rw [← mul_assoc]; rw [Units.mul_inv]; rw [one_mul]

Depends on / 依赖: Units.mul_inv, mul_add, mul_assoc, mul_inv, mul_one, one_mul
-/
theorem add_eq_mul_one_add_div [Semiring R] {a : Rˣ} {b : R} : ↑a + b = a * (1 + ↑a⁻¹ * b) := by
  rw [mul_add]; rw [mul_one]; rw [← mul_assoc]; rw [Units.mul_inv]; rw [one_mul]

end Units

namespace RingHom

section Semiring

variable [Semiring α] [Semiring β]

/--
theorem `isUnit_map` / 定理 `isUnit_map`

English:
theorem isUnit_map
  given: (f : α ->+* β) {a : α}
  statement: IsUnit a -> IsUnit (f a)
  proof: IsUnit.map f

中文:
定理 isUnit_map
  条件: (f : α ->+* β) {a : α}
  结论: 是单位 a -> 是单位 (f a)
  证明: IsUnit.map f

Depends on / 依赖: IsUnit, IsUnit.map
-/
theorem isUnit_map (f : α ->+* β) {a : α} : IsUnit a -> IsUnit (f a) :=
  IsUnit.map f

end Semiring

end RingHom
