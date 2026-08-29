/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot
-/
module

public import Mathlib.Algebra.Notation.Lemmas
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Pi

/-!
# Pi instances for ordered groups and monoids

This file defines instances for ordered group, monoid, and related structures on Pi types.
-/

@[expose] public section

variable {I α β γ : Type*}

-- The indexing type
variable {f : I -> Type*}

namespace Pi

/-- The product of a family of ordered commutative monoids is an ordered commutative monoid. -/
@[to_additive
      /-- The product of a family of ordered additive commutative monoids is
an ordered additive commutative monoid. -/]
/--
Instance `isOrderedMonoid` / 实例 `isOrderedMonoid`

English:
instance isOrderedMonoid
  signature: {ι : Type*} {Z : ι -> Type*} [forall i, CommMonoid (Z i)]
  body: fun i => mul_le_mul_left (w i) _

@[to_additive]

中文:
实例 isOrderedMonoid
  签名: {ι : 类型} {Z : ι -> 类型} [对任意 i, 交换幺半群 (Z i)]
  定义体: fun i => mul_le_mul_left (w i) _

@[to_additive]

Depends on / 依赖: mul_le_mul_left
-/
instance isOrderedMonoid {ι : Type*} {Z : ι -> Type*} [forall i, CommMonoid (Z i)]
    [forall i, Preorder (Z i)] [forall i, IsOrderedMonoid (Z i)] :
    IsOrderedMonoid (forall i, Z i) where
  mul_le_mul_left _ _ w _ := fun i => mul_le_mul_left (w i) _

@[to_additive]
/--
Instance `existsMulOfLe` / 实例 `existsMulOfLe`

English:
instance existsMulOfLe
  signature: {ι : Type*} {α : ι -> Type*} [forall i, LE (α i)] [forall i, Mul (α i)]
  body: ⟨fun h =>
    ⟨fun i => (exists_mul_of_le <| h i).choose,
      funext fun i => (exists_mul_of_le <| h i).choose_spec⟩⟩

中文:
实例 存在MulOfLe
  签名: {ι : 类型} {α : ι -> 类型} [对任意 i, LE (α i)] [对任意 i, 乘法 (α i)]
  定义体: ⟨fun h =>
    ⟨fun i => (exists_mul_of_le <| h i).choose,
      funext fun i => (exists_mul_of_le <| h i).choose_spec⟩⟩

Depends on / 依赖: choose_spec, exists_mul_of_le
-/
instance existsMulOfLe {ι : Type*} {α : ι -> Type*} [forall i, LE (α i)] [forall i, Mul (α i)]
    [forall i, ExistsMulOfLE (α i)] : ExistsMulOfLE (forall i, α i) :=
  ⟨fun h =>
    ⟨fun i => (exists_mul_of_le <| h i).choose,
      funext fun i => (exists_mul_of_le <| h i).choose_spec⟩⟩

/-- The product of a family of canonically ordered monoids is a canonically ordered monoid. -/
@[to_additive
      /-- The product of a family of canonically ordered additive monoids is
a canonically ordered additive monoid. -/]
instance {ι : Type*} {Z : ι -> Type*} [forall i, Monoid (Z i)] [forall i, PartialOrder (Z i)]
    [forall i, CanonicallyOrderedMul (Z i)] :
    CanonicallyOrderedMul (forall i, Z i) where
  __ := Pi.existsMulOfLe
  le_mul_self _ _ := fun _ => le_mul_self
  le_self_mul _ _ := fun _ => le_self_mul

@[to_additive]
/--
Instance `isOrderedCancelMonoid` / 实例 `isOrderedCancelMonoid`

English:
instance isOrderedCancelMonoid
  signature: [forall i, CommMonoid <| f i] [forall i, Preorder <| f i]
  body: le_of_mul_le_mul_left' (h i)

中文:
实例 isOrderedCancelMonoid
  签名: [对任意 i, 交换幺半群 <| f i] [对任意 i, 预序 <| f i]
  定义体: le_of_mul_le_mul_left' (h i)

Depends on / 依赖: le_of_mul_le_mul_left
-/
instance isOrderedCancelMonoid [forall i, CommMonoid <| f i] [forall i, Preorder <| f i]
    [forall i, IsOrderedCancelMonoid <| f i] :
    IsOrderedCancelMonoid (forall i : I, f i) where
  le_of_mul_le_mul_left _ _ _ h i := le_of_mul_le_mul_left' (h i)

/--
Instance `isOrderedRing` / 实例 `isOrderedRing`

English:
instance isOrderedRing
  signature: [forall i, Semiring (f i)] [forall i, PartialOrder (f i)] [forall i, IsOrderedRing (f i)]
  body: fun _ => add_le_add_left (hab _) _
  zero_le_one := fun i => zero_le_one (α := f i)
mul_le_mul_of_nonneg_left _ hc _ _ hab := fun _ => mul_le_mul_of_nonneg_left (hab _) hc _
mul_le_mul_of_nonneg_right _ hc _ _ hab := fun _ => mul_le_mul_of_nonneg_right (hab _) hc _

中文:
实例 isOrderedRing
  签名: [对任意 i, 半环 (f i)] [对任意 i, 偏序 (f i)] [对任意 i, 是Ordered环 (f i)]
  定义体: fun _ => add_le_add_left (hab _) _
  zero_le_one := fun i => zero_le_one (α := f i)
mul_le_mul_of_nonneg_left _ hc _ _ hab := fun _ => mul_le_mul_of_nonneg_left (hab _) hc _
mul_le_mul_of_nonneg_right _ hc _ _ hab := fun _ => mul_le_mul_of_nonneg_right (hab _) hc _

Depends on / 依赖: add_le_add_left
-/
instance isOrderedRing [forall i, Semiring (f i)] [forall i, PartialOrder (f i)] [forall i, IsOrderedRing (f i)] :
    IsOrderedRing (forall i, f i) where
  add_le_add_left _ _ hab _ := fun _ => add_le_add_left (hab _) _
  zero_le_one := fun i => zero_le_one (α := f i)
mul_le_mul_of_nonneg_left _ hc _ _ hab := fun _ => mul_le_mul_of_nonneg_left (hab _) hc _
mul_le_mul_of_nonneg_right _ hc _ _ hab := fun _ => mul_le_mul_of_nonneg_right (hab _) hc _

end Pi

namespace Function
section const
variable (β) [One α] [Preorder α] {a : α}

@[to_additive const_nonneg_of_nonneg]
/--
theorem `one_le_const_of_one_le` / 定理 `one_le_const_of_one_le`

English:
theorem one_le_const_of_one_le
  given: (ha : 1 <= a)
  statement: 1 <= const β a
  proof: fun _ => ha

@[to_additive]

中文:
定理 one_le_const_of_one_le
  条件: (ha : 1 <= a)
  结论: 1 <= const β a
  证明: fun _ => ha

@[to_additive]
-/
theorem one_le_const_of_one_le (ha : 1 <= a) : 1 <= const β a := fun _ => ha

@[to_additive]
/--
theorem `const_le_one_of_le_one` / 定理 `const_le_one_of_le_one`

English:
theorem const_le_one_of_le_one
  given: (ha : a <= 1)
  statement: const β a <= 1
  proof: fun _ => ha

中文:
定理 const_le_one_of_le_one
  条件: (ha : a <= 1)
  结论: const β a <= 1
  证明: fun _ => ha
-/
theorem const_le_one_of_le_one (ha : a <= 1) : const β a <= 1 := fun _ => ha

variable {β} [Nonempty β]

@[to_additive (attr := simp) const_nonneg]
/--
theorem `one_le_const` / 定理 `one_le_const`

English:
theorem one_le_const
  statement: 1 <= const β a ↔ 1 <= a
  proof: const_le_const

@[to_additive (attr := simp) const_pos]

中文:
定理 one_le_const
  结论: 1 <= const β a ↔ 1 <= a
  证明: const_le_const

@[to_additive (attr := simp) const_pos]

Depends on / 依赖: const_le_const
-/
theorem one_le_const : 1 <= const β a ↔ 1 <= a :=
  const_le_const

@[to_additive (attr := simp) const_pos]
/--
theorem `one_lt_const` / 定理 `one_lt_const`

English:
theorem one_lt_const
  statement: 1 < const β a ↔ 1 < a
  proof: const_lt_const

@[to_additive (attr := simp)]

中文:
定理 one_lt_const
  结论: 1 < const β a ↔ 1 < a
  证明: const_lt_const

@[to_additive (attr := simp)]

Depends on / 依赖: const_lt_const
-/
theorem one_lt_const : 1 < const β a ↔ 1 < a :=
  const_lt_const

@[to_additive (attr := simp)]
/--
theorem `const_le_one` / 定理 `const_le_one`

English:
theorem const_le_one
  statement: const β a <= 1 ↔ a <= 1
  proof: const_le_const

@[to_additive (attr := simp) const_neg']

中文:
定理 const_le_one
  结论: const β a <= 1 ↔ a <= 1
  证明: const_le_const

@[to_additive (attr := simp) const_neg']

Depends on / 依赖: const_le_const
-/
theorem const_le_one : const β a <= 1 ↔ a <= 1 :=
  const_le_const

@[to_additive (attr := simp) const_neg']
/--
theorem `const_lt_one` / 定理 `const_lt_one`

English:
theorem const_lt_one
  statement: const β a < 1 ↔ a < 1
  proof: const_lt_const

中文:
定理 const_lt_one
  结论: const β a < 1 ↔ a < 1
  证明: const_lt_const

Depends on / 依赖: const_lt_const
-/
theorem const_lt_one : const β a < 1 ↔ a < 1 :=
  const_lt_const

end const

section extend
variable [One γ] [LE γ] {f : α -> β} {g : α -> γ} {e : β -> γ}

/--
lemma `one_le_extend` / 引理 `one_le_extend`

English:
lemma one_le_extend
  given: (hg : 1 <= g) (he : 1 <= e)
  statement: 1 <= extend f g e
  proof: fun _b => by classical exact one_le_dite (fun _ => hg _) (fun _ => he _)

中文:
引理 one_le_extend
  条件: (hg : 1 <= g) (he : 1 <= e)
  结论: 1 <= extend f g e
  证明: fun _b => by classical exact one_le_dite (fun _ => hg _) (fun _ => he _)
-/
@[to_additive extend_nonneg] lemma one_le_extend (hg : 1 <= g) (he : 1 <= e) : 1 <= extend f g e :=
  fun _b => by classical exact one_le_dite (fun _ => hg _) (fun _ => he _)

/--
lemma `extend_le_one` / 引理 `extend_le_one`

English:
lemma extend_le_one
  given: (hg : g <= 1) (he : e <= 1)
  statement: extend f g e <= 1
  proof: fun _b => by classical exact dite_le_one (fun _ => hg _) (fun _ => he _)

中文:
引理 extend_le_one
  条件: (hg : g <= 1) (he : e <= 1)
  结论: extend f g e <= 1
  证明: fun _b => by classical exact dite_le_one (fun _ => hg _) (fun _ => he _)
-/
@[to_additive] lemma extend_le_one (hg : g <= 1) (he : e <= 1) : extend f g e <= 1 :=
  fun _b => by classical exact dite_le_one (fun _ => hg _) (fun _ => he _)

end extend
end Function

namespace Pi
variable {ι : Type*} {α : ι -> Type*} [DecidableEq ι] [forall i, One (α i)] [forall i, Preorder (α i)] {i : ι}
  {a b : α i}

@[to_additive (attr := simp, gcongr)]
/--
lemma `mulSingle_le_mulSingle` / 引理 `mulSingle_le_mulSingle`

English:
lemma mulSingle_le_mulSingle
  statement: mulSingle i a <= mulSingle i b ↔ a <= b
  proof: by
  simp [mulSingle]

@[to_additive (attr := simp) single_nonneg]

中文:
引理 mulSingle_le_mulSingle
  结论: mulSingle i a <= mulSingle i b ↔ a <= b
  证明: by
  simp [mulSingle]

@[to_additive (attr := simp) single_nonneg]

Depends on / 依赖: mulSingle
-/
lemma mulSingle_le_mulSingle : mulSingle i a <= mulSingle i b ↔ a <= b := by
  simp [mulSingle]

@[to_additive (attr := simp) single_nonneg]
/--
lemma `one_le_mulSingle` / 引理 `one_le_mulSingle`

English:
lemma one_le_mulSingle
  statement: 1 <= mulSingle i a ↔ 1 <= a
  proof: by simp [mulSingle]

@[to_additive (attr := simp) single_pos]

中文:
引理 one_le_mulSingle
  结论: 1 <= mulSingle i a ↔ 1 <= a
  证明: by simp [mulSingle]

@[to_additive (attr := simp) single_pos]

Depends on / 依赖: mulSingle
-/
lemma one_le_mulSingle : 1 <= mulSingle i a ↔ 1 <= a := by simp [mulSingle]

@[to_additive (attr := simp) single_pos]
/--
lemma `one_lt_mulSingle` / 引理 `one_lt_mulSingle`

English:
lemma one_lt_mulSingle
  statement: 1 < mulSingle i a ↔ 1 < a
  proof: by simp [mulSingle]

@[to_additive (attr := simp)]

中文:
引理 one_lt_mulSingle
  结论: 1 < mulSingle i a ↔ 1 < a
  证明: by simp [mulSingle]

@[to_additive (attr := simp)]

Depends on / 依赖: mulSingle
-/
lemma one_lt_mulSingle : 1 < mulSingle i a ↔ 1 < a := by simp [mulSingle]

@[to_additive (attr := simp)]
/--
lemma `mulSingle_le_one` / 引理 `mulSingle_le_one`

English:
lemma mulSingle_le_one
  statement: mulSingle i a <= 1 ↔ a <= 1
  proof: by simp [mulSingle]

中文:
引理 mulSingle_le_one
  结论: mulSingle i a <= 1 ↔ a <= 1
  证明: by simp [mulSingle]

Depends on / 依赖: mulSingle
-/
lemma mulSingle_le_one : mulSingle i a <= 1 ↔ a <= 1 := by simp [mulSingle]

end Pi

-- Porting note: Tactic code not ported yet
-- namespace Tactic

-- open Function

-- variable (ι) [Zero α] {a : α}

-- private theorem function_const_nonneg_of_pos [Preorder α] (ha : 0 < a) : 0 ≤ const ι a :=
-- const_nonneg_of_nonneg _ ha.le

-- variable [Nonempty ι]

-- private theorem function_const_ne_zero : a ≠ 0 → const ι a ≠ 0 :=
-- const_ne_zero.2

-- private theorem function_const_pos [Preorder α] : 0 < a → 0 < const ι a :=
-- const_pos.2

-- /-- Extension for the `positivity` tactic: `Function.const` is positive/nonnegative/nonzero if
-- its input is. -/
-- @[positivity]
-- unsafe def positivity_const : expr → tactic strictness
-- | q(Function.const $(ι) $(a)) => do
-- let strict_a ← core a
-- match strict_a with
-- | positive p =>
-- positive <$> to_expr ``(function_const_pos $(ι) $(p)) <|>
-- nonnegative <$> to_expr ``(function_const_nonneg_of_pos $(ι) $(p))
-- | nonnegative p => nonnegative <$> to_expr ``(const_nonneg_of_nonneg $(ι) $(p))
-- | nonzero p => nonzero <$> to_expr ``(function_const_ne_zero $(ι) $(p))
-- | e =>
-- pp e >>= fail ∘ format.bracket "The expression `" "` is not of the form `Function.const ι a`"

-- end Tactic
