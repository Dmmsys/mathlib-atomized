/-
Copyright (c) 2022 Alex J. Best, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best, Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.Hom.Ring

/-!
### Uniqueness of ring homomorphisms to archimedean fields.

There is at most one ordered ring homomorphism from a linear ordered field to an archimedean linear
ordered field. Reciprocally, such an ordered ring homomorphism exists when the codomain is further
conditionally complete.
-/

public section

assert_not_exists Finset

variable {α β : Type*} [Field α] [LinearOrder α] [Field β] [LinearOrder β]

/--
Instance `OrderRingHom.subsingleton` / 实例 `OrderRingHom.subsingleton`

English:
instance OrderRingHom.subsingleton
  signature: [IsStrictOrderedRing β] [Archimedean β]
  body: ⟨fun f g => by
    ext x
    by_contra h' : f x != g x
    wlog h : f x < g x with h₂
    · exact h₂ g f x (Ne.symm h') (h'.lt_or_gt.resolve_left h)
    obtain ⟨q, hf, hg⟩ := exists_rat_btwn h
    rw [← map_ratCast f] at hf
    rw [← map_ratCast g] at hg
    exact
      (lt_asymm ((OrderHomClass.mon

中文:
实例 OrderRingHom.subsingleton
  签名: [IsStrictOrderedRing β] [Archimedean β]
  定义体: ⟨fun f g => by
    ext x
    by_contra h' : f x != g x
    wlog h : f x < g x with h₂
    · exact h₂ g f x (Ne.symm h') (h'.lt_or_gt.resolve_left h)
    obtain ⟨q, hf, hg⟩ := exists_rat_btwn h
    rw [← map_ratCast f] at hf
    rw [← map_ratCast g] at hg
    exact
      (lt_asymm ((OrderHomClass.mon

Depends on / 依赖: Ne.symm, OrderHomClass, OrderHomClass.mono, exists_rat_btwn, lt_asymm, lt_or_gt, lt_or_gt.resolve_left, map_ratCast, reflect_lt, resolve_left
-/
instance OrderRingHom.subsingleton [IsStrictOrderedRing β] [Archimedean β] :
    Subsingleton (α ->+*o β) :=
  ⟨fun f g => by
    ext x
    by_contra h' : f x != g x
    wlog h : f x < g x with h₂
    · exact h₂ g f x (Ne.symm h') (h'.lt_or_gt.resolve_left h)
    obtain ⟨q, hf, hg⟩ := exists_rat_btwn h
    rw [← map_ratCast f] at hf
    rw [← map_ratCast g] at hg
    exact
      (lt_asymm ((OrderHomClass.mono g).reflect_lt hg) <|
          (OrderHomClass.mono f).reflect_lt hf).elim⟩

/--
Instance `OrderRingIso.subsingleton_right` / 实例 `OrderRingIso.subsingleton_right`

English:
instance OrderRingIso.subsingleton_right
  signature: [IsStrictOrderedRing β] [Archimedean β]
  body: OrderRingIso.toOrderRingHom_injective.subsingleton

中文:
实例 OrderRingIso.subsingleton_right
  签名: [IsStrictOrderedRing β] [Archimedean β]
  定义体: OrderRingIso.toOrderRingHom_injective.subsingleton

Depends on / 依赖: OrderRingIso, OrderRingIso.toOrderRingHom_injective.subsingleton, subsingleton, toOrderRingHom_injective
-/
instance OrderRingIso.subsingleton_right [IsStrictOrderedRing β] [Archimedean β] :
    Subsingleton (α ≃+*o β) :=
  OrderRingIso.toOrderRingHom_injective.subsingleton

/--
Instance `OrderRingIso.subsingleton_left` / 实例 `OrderRingIso.subsingleton_left`

English:
instance OrderRingIso.subsingleton_left
  signature: [IsStrictOrderedRing α] [Archimedean α]
  body: OrderRingIso.symm_bijective.injective.subsingleton

中文:
实例 OrderRingIso.subsingleton_left
  签名: [IsStrictOrderedRing α] [Archimedean α]
  定义体: OrderRingIso.symm_bijective.injective.subsingleton

Depends on / 依赖: OrderRingIso, OrderRingIso.symm_bijective.injective.subsingleton, injective, subsingleton, symm_bijective
-/
instance OrderRingIso.subsingleton_left [IsStrictOrderedRing α] [Archimedean α] :
    Subsingleton (α ≃+*o β) :=
  OrderRingIso.symm_bijective.injective.subsingleton

/--
theorem `OrderRingHom.eq_id` / 定理 `OrderRingHom.eq_id`

English:
theorem OrderRingHom.eq_id
  given: [IsStrictOrderedRing α] [Archimedean α] (f : α ->+*o α)
  statement: f = .id _
  proof: Subsingleton.elim ..

中文:
定理 OrderRingHom.eq_id
  条件: [IsStrictOrderedRing α] [Archimedean α] (f : α ->+*o α)
  结论: f = .id _
  证明: Subsingleton.elim ..

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
theorem OrderRingHom.eq_id [IsStrictOrderedRing α] [Archimedean α] (f : α ->+*o α) : f = .id _ :=
  Subsingleton.elim ..

/--
theorem `OrderRingIso.eq_refl` / 定理 `OrderRingIso.eq_refl`

English:
theorem OrderRingIso.eq_refl
  given: [IsStrictOrderedRing α] [Archimedean α] (f : α ≃+*o α)
  statement: f = .refl _
  proof: Subsingleton.elim ..

中文:
定理 OrderRingIso.eq_refl
  条件: [IsStrictOrderedRing α] [Archimedean α] (f : α ≃+*o α)
  结论: f = .refl _
  证明: Subsingleton.elim ..

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
theorem OrderRingIso.eq_refl [IsStrictOrderedRing α] [Archimedean α] (f : α ≃+*o α) : f = .refl _ :=
  Subsingleton.elim ..

/--
theorem `OrderRingHom.apply_eq_self` / 定理 `OrderRingHom.apply_eq_self`

English:
theorem OrderRingHom.apply_eq_self
  given: [IsStrictOrderedRing α] [Archimedean α] (f : α ->+*o α) (x : α)
  proof: by
  rw [f.eq_id]; rfl

中文:
定理 OrderRingHom.apply_eq_self
  条件: [IsStrictOrderedRing α] [Archimedean α] (f : α ->+*o α) (x : α)
  证明: by
  rw [f.eq_id]; rfl

Depends on / 依赖: eq_id, f.eq_id
-/
theorem OrderRingHom.apply_eq_self [IsStrictOrderedRing α] [Archimedean α] (f : α ->+*o α) (x : α) :
    f x = x := by
  rw [f.eq_id]; rfl

/--
theorem `OrderRingIso.apply_eq_self` / 定理 `OrderRingIso.apply_eq_self`

English:
theorem OrderRingIso.apply_eq_self
  given: [IsStrictOrderedRing α] [Archimedean α] (f : α ≃+*o α) (x : α)
  proof: f.toOrderRingHom.apply_eq_self x

中文:
定理 OrderRingIso.apply_eq_self
  条件: [IsStrictOrderedRing α] [Archimedean α] (f : α ≃+*o α) (x : α)
  证明: f.toOrderRingHom.apply_eq_self x

Depends on / 依赖: apply_eq_self, f.toOrderRingHom.apply_eq_self, toOrderRingHom
-/
theorem OrderRingIso.apply_eq_self [IsStrictOrderedRing α] [Archimedean α] (f : α ≃+*o α) (x : α) :
    f x = x :=
  f.toOrderRingHom.apply_eq_self x
