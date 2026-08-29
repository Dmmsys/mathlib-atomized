/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Algebra.Order.Kleene
public import Mathlib.Algebra.Order.Ring.Canonical
public import Mathlib.Data.Set.BooleanAlgebra
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!
# Sets as a semiring under union

This file defines `SetSemiring α`, an alias of `Set α`, which we endow with `∪` as addition and
pointwise `*` as multiplication. If `α` is a (commutative) monoid, `SetSemiring α` is a
(commutative) semiring.
-/

@[expose] public section


open Function Set

open scoped Pointwise

variable {α β : Type*}

/--
Definition of `SetSemiring` / `SetSemiring` 的定义

English:
definition SetSemiring
  signature: (α : Type*)
  body: Set α
deriving Inhabited, PartialOrder, OrderBot

中文:
定义 SetSemiring
  签名: (α : 类型)
  定义体: Set α
deriving Inhabited, PartialOrder, OrderBot
-/
def SetSemiring (α : Type*) : Type _ :=
  Set α
deriving Inhabited, PartialOrder, OrderBot

/--
Definition of `Set.up` / `Set.up` 的定义

English:
definition Set.up
  signature: : Set α ≃ SetSemiring α
  body: Equiv.refl _

中文:
定义 Set.up
  签名: : Set α ≃ SetSemiring α
  定义体: Equiv.refl _
-/
protected def Set.up : Set α ≃ SetSemiring α :=
  Equiv.refl _

namespace SetSemiring

/--
Definition of `down` / `down` 的定义

English:
definition down
  signature: : SetSemiring α ≃ Set α
  body: Equiv.refl _

中文:
定义 down
  签名: : SetSemiring α ≃ Set α
  定义体: Equiv.refl _
-/
protected def down : SetSemiring α ≃ Set α :=
  Equiv.refl _

open SetSemiring (down)
open Set (up)

@[simp]
/--
theorem `down_up` / 定理 `down_up`

English:
theorem down_up
  given: (s : Set α)
  statement: s.up.down = s
  proof: rfl

@[simp]

中文:
定理 down_up
  条件: (s : Set α)
  结论: s.up.down = s
  证明: rfl

@[simp]
-/
protected theorem down_up (s : Set α) : s.up.down = s :=
  rfl

@[simp]
/--
theorem `up_down` / 定理 `up_down`

English:
theorem up_down
  given: (s : SetSemiring α)
  statement: s.down.up = s
  proof: rfl

中文:
定理 up_down
  条件: (s : SetSemiring α)
  结论: s.down.up = s
  证明: rfl
-/
protected theorem up_down (s : SetSemiring α) : s.down.up = s :=
  rfl

-- TODO: These lemmas should be tagged `simp`
/--
theorem `up_le_up` / 定理 `up_le_up`

English:
theorem up_le_up
  given: {s t : Set α}
  statement: s.up <= t.up ↔ s subseteq t
  proof: Iff.rfl

中文:
定理 up_le_up
  条件: {s t : Set α}
  结论: s.up <= t.up ↔ s subseteq t
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem up_le_up {s t : Set α} : s.up <= t.up ↔ s subseteq t :=
  Iff.rfl

/--
theorem `up_lt_up` / 定理 `up_lt_up`

English:
theorem up_lt_up
  given: {s t : Set α}
  statement: s.up < t.up ↔ s ⊂ t
  proof: Iff.rfl

@[simp]

中文:
定理 up_lt_up
  条件: {s t : Set α}
  结论: s.up < t.up ↔ s ⊂ t
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem up_lt_up {s t : Set α} : s.up < t.up ↔ s ⊂ t :=
  Iff.rfl

@[simp]
/--
theorem `down_subset_down` / 定理 `down_subset_down`

English:
theorem down_subset_down
  given: {s t : SetSemiring α}
  statement: s.down subseteq t.down ↔ s <= t
  proof: Iff.rfl

@[simp]

中文:
定理 down_subset_down
  条件: {s t : SetSemiring α}
  结论: s.down subseteq t.down ↔ s <= t
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem down_subset_down {s t : SetSemiring α} : s.down subseteq t.down ↔ s <= t :=
  Iff.rfl

@[simp]
/--
theorem `down_ssubset_down` / 定理 `down_ssubset_down`

English:
theorem down_ssubset_down
  given: {s t : SetSemiring α}
  statement: s.down ⊂ t.down ↔ s < t
  proof: Iff.rfl

中文:
定理 down_ssubset_down
  条件: {s t : SetSemiring α}
  结论: s.down ⊂ t.down ↔ s < t
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem down_ssubset_down {s t : SetSemiring α} : s.down ⊂ t.down ↔ s < t :=
  Iff.rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (SetSemiring α)
  body: (∅ : Set α).up

中文:
实例 :
  签名: Zero (SetSemiring α)
  定义体: (∅ : Set α).up
-/
instance : Zero (SetSemiring α) where zero := (∅ : Set α).up

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add (SetSemiring α)
  body: (s.down union t.down).up

中文:
实例 :
  签名: Add (SetSemiring α)
  定义体: (s.down union t.down).up

Depends on / 依赖: s.down, t.down
-/
instance : Add (SetSemiring α) where add s t := (s.down union t.down).up

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommMonoid (SetSemiring α)
  body: union_assoc
  zero_add := empty_union
  add_zero := union_empty
  add_comm := union_comm
  nsmul := nsmulRec

中文:
实例 :
  签名: AddCommMonoid (SetSemiring α)
  定义体: union_assoc
  zero_add := empty_union
  add_zero := union_empty
  add_comm := union_comm
  nsmul := nsmulRec

Depends on / 依赖: union_assoc
-/
instance : AddCommMonoid (SetSemiring α) where
  add_assoc := union_assoc
  zero_add := empty_union
  add_zero := union_empty
  add_comm := union_comm
  nsmul := nsmulRec

/--
theorem `zero_def` / 定理 `zero_def`

English:
theorem zero_def
  statement: (0 : SetSemiring α) = Set.up ∅
  proof: rfl

@[simp]

中文:
定理 zero_def
  结论: (0 : SetSemiring α) = Set.up ∅
  证明: rfl

@[simp]
-/
theorem zero_def : (0 : SetSemiring α) = Set.up ∅ :=
  rfl

@[simp]
/--
theorem `down_zero` / 定理 `down_zero`

English:
theorem down_zero
  statement: (0 : SetSemiring α).down = ∅
  proof: rfl

@[simp]

中文:
定理 down_zero
  结论: (0 : SetSemiring α).down = ∅
  证明: rfl

@[simp]
-/
theorem down_zero : (0 : SetSemiring α).down = ∅ :=
  rfl

@[simp]
/--
theorem `_root_.Set.up_empty` / 定理 `_root_.Set.up_empty`

English:
theorem _root_.Set.up_empty
  statement: (∅ : Set α).up = 0
  proof: rfl

中文:
定理 _root_.Set.up_empty
  结论: (∅ : Set α).up = 0
  证明: rfl
-/
theorem _root_.Set.up_empty : (∅ : Set α).up = 0 :=
  rfl

/--
theorem `add_def` / 定理 `add_def`

English:
theorem add_def
  given: (s t : SetSemiring α)
  statement: s + t = (s.down union t.down).up
  proof: rfl

@[simp]

中文:
定理 add_def
  条件: (s t : SetSemiring α)
  结论: s + t = (s.down union t.down).up
  证明: rfl

@[simp]

Depends on / 依赖: Finite, Finite.surjective_of_injective, isLeftRegular_of_mul_eq_one, left_inv_eq_right_inv, surjective_of_injective
-/
theorem add_def (s t : SetSemiring α) : s + t = (s.down union t.down).up :=
  rfl

@[simp]
/--
theorem `down_add` / 定理 `down_add`

English:
theorem down_add
  given: (s t : SetSemiring α)
  statement: (s + t).down = s.down union t.down
  proof: rfl

@[simp]

中文:
定理 down_add
  条件: (s t : SetSemiring α)
  结论: (s + t).down = s.down union t.down
  证明: rfl

@[simp]
-/
theorem down_add (s t : SetSemiring α) : (s + t).down = s.down union t.down :=
  rfl

@[simp]
/--
theorem `_root_.Set.up_union` / 定理 `_root_.Set.up_union`

English:
theorem _root_.Set.up_union
  given: (s t : Set α)
  statement: (s union t).up = s.up + t.up
  proof: rfl

中文:
定理 _root_.Set.up_union
  条件: (s t : Set α)
  结论: (s union t).up = s.up + t.up
  证明: rfl
-/
theorem _root_.Set.up_union (s t : Set α) : (s union t).up = s.up + t.up :=
  rfl

/--
Instance `addLeftMono` / 实例 `addLeftMono`

English:
instance addLeftMono
  signature: : AddLeftMono (SetSemiring α)
  body: ⟨fun _ _ _ => union_subset_union_right _⟩

中文:
实例 addLeftMono
  签名: : AddLeftMono (SetSemiring α)
  定义体: ⟨fun _ _ _ => union_subset_union_right _⟩

Depends on / 依赖: union_subset_union_right
-/
instance addLeftMono : AddLeftMono (SetSemiring α) :=
  ⟨fun _ _ _ => union_subset_union_right _⟩

section Mul

variable [Mul α]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NonUnitalNonAssocSemiring (SetSemiring α)
  body: fun s t => (image2 (· * ·) s.down t.down).up
  zero_mul := fun _ => empty_mul
  mul_zero := fun _ => mul_empty
  left_distrib := fun _ _ _ => mul_union
  right_distrib := fun _ _ _ => union_mul

中文:
实例 :
  签名: NonUnitalNonAssocSemiring (SetSemiring α)
  定义体: fun s t => (image2 (· * ·) s.down t.down).up
  zero_mul := fun _ => empty_mul
  mul_zero := fun _ => mul_empty
  left_distrib := fun _ _ _ => mul_union
  right_distrib := fun _ _ _ => union_mul

Depends on / 依赖: image2, s.down, t.down
-/
instance : NonUnitalNonAssocSemiring (SetSemiring α) where
  mul := fun s t => (image2 (· * ·) s.down t.down).up
  zero_mul := fun _ => empty_mul
  mul_zero := fun _ => mul_empty
  left_distrib := fun _ _ _ => mul_union
  right_distrib := fun _ _ _ => union_mul

/--
theorem `mul_def` / 定理 `mul_def`

English:
theorem mul_def
  given: (s t : SetSemiring α)
  statement: s * t = (s.down * t.down).up
  proof: rfl

@[simp]

中文:
定理 mul_def
  条件: (s t : SetSemiring α)
  结论: s * t = (s.down * t.down).up
  证明: rfl

@[simp]
-/
theorem mul_def (s t : SetSemiring α) : s * t = (s.down * t.down).up :=
  rfl

@[simp]
/--
theorem `down_mul` / 定理 `down_mul`

English:
theorem down_mul
  given: (s t : SetSemiring α)
  statement: (s * t).down = s.down * t.down
  proof: rfl

@[simp]

中文:
定理 down_mul
  条件: (s t : SetSemiring α)
  结论: (s * t).down = s.down * t.down
  证明: rfl

@[simp]
-/
theorem down_mul (s t : SetSemiring α) : (s * t).down = s.down * t.down :=
  rfl

@[simp]
/--
theorem `_root_.Set.up_mul` / 定理 `_root_.Set.up_mul`

English:
theorem _root_.Set.up_mul
  given: (s t : Set α)
  statement: (s * t).up = s.up * t.up
  proof: rfl

中文:
定理 _root_.Set.up_mul
  条件: (s t : Set α)
  结论: (s * t).up = s.up * t.up
  证明: rfl
-/
theorem _root_.Set.up_mul (s t : Set α) : (s * t).up = s.up * t.up :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NoZeroDivisors (SetSemiring α)
  body: ⟨fun {a b} ab =>
    a.eq_empty_or_nonempty.imp_right fun ha =>
      b.eq_empty_or_nonempty.resolve_right fun hb =>
        Nonempty.ne_empty ⟨_, mul_mem_mul ha.some_mem hb.some_mem⟩ ab⟩

中文:
实例 :
  签名: NoZeroDivisors (SetSemiring α)
  定义体: ⟨fun {a b} ab =>
    a.eq_empty_or_nonempty.imp_right fun ha =>
      b.eq_empty_or_nonempty.resolve_right fun hb =>
        Nonempty.ne_empty ⟨_, mul_mem_mul ha.some_mem hb.some_mem⟩ ab⟩

Depends on / 依赖: Nonempty, Nonempty.ne_empty, a.eq_empty_or_nonempty.imp_right, b.eq_empty_or_nonempty.resolve_right, eq_empty_or_nonempty, ha.some_mem, hb.some_mem, imp_right, mul_mem_mul, ne_empty, resolve_right, some_mem
-/
instance : NoZeroDivisors (SetSemiring α) :=
  ⟨fun {a b} ab =>
    a.eq_empty_or_nonempty.imp_right fun ha =>
      b.eq_empty_or_nonempty.resolve_right fun hb =>
        Nonempty.ne_empty ⟨_, mul_mem_mul ha.some_mem hb.some_mem⟩ ab⟩

/--
Instance `mulLeftMono` / 实例 `mulLeftMono`

English:
instance mulLeftMono
  signature: : MulLeftMono (SetSemiring α)
  body: ⟨fun _ _ _ => mul_subset_mul_left⟩

中文:
实例 mulLeftMono
  签名: : MulLeftMono (SetSemiring α)
  定义体: ⟨fun _ _ _ => mul_subset_mul_left⟩

Depends on / 依赖: mul_subset_mul_left
-/
instance mulLeftMono : MulLeftMono (SetSemiring α) :=
  ⟨fun _ _ _ => mul_subset_mul_left⟩

/--
Instance `mulRightMono` / 实例 `mulRightMono`

English:
instance mulRightMono
  signature: : MulRightMono (SetSemiring α)
  body: ⟨fun _ _ _ => mul_subset_mul_right⟩

中文:
实例 mulRightMono
  签名: : MulRightMono (SetSemiring α)
  定义体: ⟨fun _ _ _ => mul_subset_mul_right⟩

Depends on / 依赖: mul_subset_mul_right
-/
instance mulRightMono : MulRightMono (SetSemiring α) :=
  ⟨fun _ _ _ => mul_subset_mul_right⟩

end Mul


section One

variable [One α]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One (SetSemiring α)
  body: (1 : Set α).up

中文:
实例 :
  签名: One (SetSemiring α)
  定义体: (1 : Set α).up
-/
instance : One (SetSemiring α) where one := (1 : Set α).up

/--
theorem `one_def` / 定理 `one_def`

English:
theorem one_def
  statement: (1 : SetSemiring α) = Set.up 1
  proof: rfl

@[simp]

中文:
定理 one_def
  结论: (1 : SetSemiring α) = Set.up 1
  证明: rfl

@[simp]
-/
theorem one_def : (1 : SetSemiring α) = Set.up 1 :=
  rfl

@[simp]
/--
theorem `down_one` / 定理 `down_one`

English:
theorem down_one
  statement: (1 : SetSemiring α).down = 1
  proof: rfl

@[simp]

中文:
定理 down_one
  结论: (1 : SetSemiring α).down = 1
  证明: rfl

@[simp]
-/
theorem down_one : (1 : SetSemiring α).down = 1 :=
  rfl

@[simp]
/--
theorem `_root_.Set.up_one` / 定理 `_root_.Set.up_one`

English:
theorem _root_.Set.up_one
  statement: (1 : Set α).up = 1
  proof: rfl

中文:
定理 _root_.Set.up_one
  结论: (1 : Set α).up = 1
  证明: rfl

Depends on / 依赖: CharZero, DivisionRing, divisibleByIntOfCharZero
-/
theorem _root_.Set.up_one : (1 : Set α).up = 1 :=
  rfl

end One

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MulOneClass
  signature: α] : MulOneClass (SetSemiring α)
  body: inferInstanceAs MulOneClass (Set α)

中文:
实例 [MulOneClass
  签名: α] : MulOneClass (SetSemiring α)
  定义体: inferInstanceAs MulOneClass (Set α)

Depends on / 依赖: MulOneClass
-/
instance [MulOneClass α] : MulOneClass (SetSemiring α) :=
inferInstanceAs MulOneClass (Set α)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MulOneClass
  signature: α] : NonAssocSemiring (SetSemiring α) where

中文:
实例 [MulOneClass
  签名: α] : NonAssocSemiring (SetSemiring α) where
-/
noncomputable instance [MulOneClass α] : NonAssocSemiring (SetSemiring α) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Semigroup
  signature: α] : Semigroup (SetSemiring α)
  body: inferInstanceAs Semigroup (Set α)

中文:
实例 [Semigroup
  签名: α] : Semigroup (SetSemiring α)
  定义体: inferInstanceAs Semigroup (Set α)

Depends on / 依赖: Semigroup
-/
instance [Semigroup α] : Semigroup (SetSemiring α) :=
inferInstanceAs Semigroup (Set α)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Semigroup
  signature: α] : NonUnitalSemiring (SetSemiring α) where

中文:
实例 [Semigroup
  签名: α] : NonUnitalSemiring (SetSemiring α) where
-/
instance [Semigroup α] : NonUnitalSemiring (SetSemiring α) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteBooleanAlgebra (SetSemiring α)
  body: inferInstanceAs CompleteBooleanAlgebra (Set α)

中文:
实例 :
  签名: Complete布尔eanAlgebra (SetSemiring α)
  定义体: inferInstanceAs CompleteBooleanAlgebra (Set α)

Depends on / 依赖: CompleteBooleanAlgebra
-/
instance : CompleteBooleanAlgebra (SetSemiring α) :=
inferInstanceAs CompleteBooleanAlgebra (Set α)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: α] : IdemSemiring (SetSemiring α)
  body: { (inferInstance : NonAssocSemiring (SetSemiring α)),
    (inferInstance : NonUnitalSemiring (SetSemiring α)),
    (inferInstance : CompleteBooleanAlgebra (SetSemiring α)) with }

中文:
实例 [Monoid
  签名: α] : IdemSemiring (SetSemiring α)
  定义体: { (inferInstance : NonAssocSemiring (SetSemiring α)),
    (inferInstance : NonUnitalSemiring (SetSemiring α)),
    (inferInstance : CompleteBooleanAlgebra (SetSemiring α)) with }

Depends on / 依赖: CompleteBooleanAlgebra, NonAssocSemiring, NonUnitalSemiring, SetSemiring
-/
noncomputable instance [Monoid α] : IdemSemiring (SetSemiring α) :=
  { (inferInstance : NonAssocSemiring (SetSemiring α)),
    (inferInstance : NonUnitalSemiring (SetSemiring α)),
    (inferInstance : CompleteBooleanAlgebra (SetSemiring α)) with }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommSemigroup
  signature: α] : CommSemigroup (SetSemiring α)
  body: inferInstanceAs CommSemigroup (Set α)

中文:
实例 [CommSemigroup
  签名: α] : CommSemigroup (SetSemiring α)
  定义体: inferInstanceAs CommSemigroup (Set α)

Depends on / 依赖: CommSemigroup
-/
instance [CommSemigroup α] : CommSemigroup (SetSemiring α) :=
inferInstanceAs CommSemigroup (Set α)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommSemigroup
  signature: α] : NonUnitalCommSemiring (SetSemiring α) where

中文:
实例 [CommSemigroup
  签名: α] : NonUnitalCommSemiring (SetSemiring α) where
-/
instance [CommSemigroup α] : NonUnitalCommSemiring (SetSemiring α) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommMonoid
  signature: α] : CommMonoid (SetSemiring α)
  body: inferInstanceAs CommMonoid (Set α)

中文:
实例 [CommMonoid
  签名: α] : CommMonoid (SetSemiring α)
  定义体: inferInstanceAs CommMonoid (Set α)

Depends on / 依赖: CommMonoid
-/
noncomputable instance [CommMonoid α] : CommMonoid (SetSemiring α) :=
inferInstanceAs CommMonoid (Set α)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommMonoid
  signature: α] : IdemCommSemiring (SetSemiring α) where

中文:
实例 [CommMonoid
  签名: α] : IdemCommSemiring (SetSemiring α) where
-/
noncomputable instance [CommMonoid α] : IdemCommSemiring (SetSemiring α) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CanonicallyOrderedAdd (SetSemiring α)
  body: ⟨b, (union_eq_right.2 ab).symm⟩
  le_add_self _ _ := subset_union_right
  le_self_add _ _ := subset_union_left

中文:
实例 :
  签名: CanonicallyOrderedAdd (SetSemiring α)
  定义体: ⟨b, (union_eq_right.2 ab).symm⟩
  le_add_self _ _ := subset_union_right
  le_self_add _ _ := subset_union_left

Depends on / 依赖: union_eq_right
-/
instance : CanonicallyOrderedAdd (SetSemiring α) where
  exists_add_of_le {_ b} ab := ⟨b, (union_eq_right.2 ab).symm⟩
  le_add_self _ _ := subset_union_right
  le_self_add _ _ := subset_union_left

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommMonoid
  signature: α] : IsOrderedRing (SetSemiring α)
  body: CanonicallyOrderedAdd.toIsOrderedRing

中文:
实例 [CommMonoid
  签名: α] : IsOrderedRing (SetSemiring α)
  定义体: CanonicallyOrderedAdd.toIsOrderedRing

Depends on / 依赖: CanonicallyOrderedAdd, CanonicallyOrderedAdd.toIsOrderedRing, toIsOrderedRing
-/
noncomputable instance [CommMonoid α] : IsOrderedRing (SetSemiring α) :=
  CanonicallyOrderedAdd.toIsOrderedRing

/--
Definition of `singletonMonoidHom` / `singletonMonoidHom` 的定义

English:
definition singletonMonoidHom
  signature: [Monoid α]
  body: up {a}
  map_one' := rfl
  map_mul' _ _ := image2_singleton.symm

中文:
定义 singletonMonoidHom
  签名: [Monoid α]
  定义体: up {a}
  map_one' := rfl
  map_mul' _ _ := image2_singleton.symm
-/
noncomputable def singletonMonoidHom [Monoid α] : α ->* SetSemiring α where
  toFun a := up {a}
  map_one' := rfl
  map_mul' _ _ := image2_singleton.symm

/--
Definition of `imageHom` / `imageHom` 的定义

English:
definition imageHom
  signature: [MulOneClass α] [MulOneClass β] (f : α ->* β)
  body: (image f s.down).up
  map_zero' := image_empty _
  map_one' := by
    rw [down_one]; rw [image_one]; rw [map_one]; rw [singleton_one]; rw [up_one]
  map_add' := image_union _
  map_mul' _ _ := image_mul f

中文:
定义 imageHom
  签名: [MulOneClass α] [MulOneClass β] (f : α ->* β)
  定义体: (image f s.down).up
  map_zero' := image_empty _
  map_one' := by
    rw [down_one]; rw [image_one]; rw [map_one]; rw [singleton_one]; rw [up_one]
  map_add' := image_union _
  map_mul' _ _ := image_mul f

Depends on / 依赖: s.down
-/
noncomputable def imageHom [MulOneClass α] [MulOneClass β] (f : α ->* β) :
    SetSemiring α ->+* SetSemiring β where
  toFun s := (image f s.down).up
  map_zero' := image_empty _
  map_one' := by
    rw [down_one]; rw [image_one]; rw [map_one]; rw [singleton_one]; rw [up_one]
  map_add' := image_union _
  map_mul' _ _ := image_mul f

/--
lemma `imageHom_def` / 引理 `imageHom_def`

English:
lemma imageHom_def
  given: [MulOneClass α] [MulOneClass β] (f : α ->* β) (s : SetSemiring α)
  proof: rfl

@[simp]

中文:
引理 imageHom_def
  条件: [MulOneClass α] [MulOneClass β] (f : α ->* β) (s : SetSemiring α)
  证明: rfl

@[simp]
-/
lemma imageHom_def [MulOneClass α] [MulOneClass β] (f : α ->* β) (s : SetSemiring α) :
    imageHom f s = (image f s.down).up :=
  rfl

@[simp]
/--
lemma `down_imageHom` / 引理 `down_imageHom`

English:
lemma down_imageHom
  given: [MulOneClass α] [MulOneClass β] (f : α ->* β) (s : SetSemiring α)
  proof: rfl

@[simp]

中文:
引理 down_imageHom
  条件: [MulOneClass α] [MulOneClass β] (f : α ->* β) (s : SetSemiring α)
  证明: rfl

@[simp]
-/
lemma down_imageHom [MulOneClass α] [MulOneClass β] (f : α ->* β) (s : SetSemiring α) :
    (imageHom f s).down = f '' s.down :=
  rfl

@[simp]
/--
lemma `_root_.Set.up_image` / 引理 `_root_.Set.up_image`

English:
lemma _root_.Set.up_image
  given: [MulOneClass α] [MulOneClass β] (f : α ->* β) (s : Set α)
  proof: rfl

中文:
引理 _root_.Set.up_image
  条件: [MulOneClass α] [MulOneClass β] (f : α ->* β) (s : Set α)
  证明: rfl
-/
lemma _root_.Set.up_image [MulOneClass α] [MulOneClass β] (f : α ->* β) (s : Set α) :
    (f '' s).up = imageHom f s.up :=
  rfl

end SetSemiring
