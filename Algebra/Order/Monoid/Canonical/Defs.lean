/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl, Yuyang Zhao
-/
module

public import Mathlib.Algebra.Group.Units.Basic
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
public import Mathlib.Algebra.NeZero
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.Interval.Set.Defs

/-!
# Canonically ordered monoids
-/

public section

universe u

variable {α : Type u}

/--
Definition of `CanonicallyOrderedAdd` / `CanonicallyOrderedAdd` 的定义

English:
class CanonicallyOrderedAdd
  parameters: (α : Type*) [Add α] [LE α]
  extends: ExistsAddOfLE α
  axioms and operations (2):
    - le_add_self : forall a b : α, a <= b + a
    - le_self_add : forall a b : α, a <= a + b

中文:
类 典范有序加法
  参数: (α : 类型) [加法 α] [LE α]
  继承: ExistsAddOfLE α
  公理与运算 (2 个):
    - le_add_self : 对任意 a b : α, a <= b + a
    - le_self_add : 对任意 a b : α, a <= a + b
-/
class CanonicallyOrderedAdd (α : Type*) [Add α] [LE α] : Prop
    extends ExistsAddOfLE α where
  /-- For any `a` and `b`, `a ≤ a + b` -/
  protected le_add_self : forall a b : α, a <= b + a
  protected le_self_add : forall a b : α, a <= a + b

attribute [instance 50] CanonicallyOrderedAdd.toExistsAddOfLE

/-- An ordered monoid is `CanonicallyOrderedMul`
  if the ordering coincides with the divisibility relation,
  which is to say, `a ≤ b` iff there exists `c` with `b = a * c`.
  Examples seem rare; it seems more likely that the `OrderDual`
  of a naturally-occurring lattice satisfies this than the lattice
  itself (for example, dual of the lattice of ideals of a PID or
  Dedekind domain satisfy this; collections of all things ≤ 1 seem to
  be more natural that collections of all things ≥ 1). -/
@[to_additive]
/--
Definition of `CanonicallyOrderedMul` / `CanonicallyOrderedMul` 的定义

English:
class CanonicallyOrderedMul
  parameters: (α : Type*) [Mul α] [LE α]
  extends: ExistsMulOfLE α
  axioms and operations (2):
    - le_mul_self : forall a b : α, a <= b * a
    - le_self_mul : forall a b : α, a <= a * b

中文:
类 典范有序乘法
  参数: (α : 类型) [乘法 α] [LE α]
  继承: ExistsMulOfLE α
  公理与运算 (2 个):
    - le_mul_self : 对任意 a b : α, a <= b * a
    - le_self_mul : 对任意 a b : α, a <= a * b
-/
class CanonicallyOrderedMul (α : Type*) [Mul α] [LE α] : Prop
    extends ExistsMulOfLE α where
  /-- For any `a` and `b`, `a ≤ a * b` -/
  protected le_mul_self : forall a b : α, a <= b * a
  protected le_self_mul : forall a b : α, a <= a * b

attribute [instance 50] CanonicallyOrderedMul.toExistsMulOfLE

section Mul
variable [Mul α]

section LE
variable [LE α] [CanonicallyOrderedMul α] {a b c : α}

@[to_additive]
/--
theorem `le_mul_self` / 定理 `le_mul_self`

English:
theorem le_mul_self
  statement: a <= b * a
  proof: CanonicallyOrderedMul.le_mul_self _ _

@[to_additive]

中文:
定理 le_mul_self
  结论: a <= b * a
  证明: CanonicallyOrderedMul.le_mul_self _ _

@[to_additive]

Depends on / 依赖: CanonicallyOrderedMul, CanonicallyOrderedMul.le_mul_self, le_mul_self
-/
theorem le_mul_self : a <= b * a :=
  CanonicallyOrderedMul.le_mul_self _ _

@[to_additive]
/--
theorem `le_self_mul` / 定理 `le_self_mul`

English:
theorem le_self_mul
  statement: a <= a * b
  proof: CanonicallyOrderedMul.le_self_mul _ _

@[to_additive (attr := simp)]

中文:
定理 le_self_mul
  结论: a <= a * b
  证明: CanonicallyOrderedMul.le_self_mul _ _

@[to_additive (attr := simp)]

Depends on / 依赖: CanonicallyOrderedMul, CanonicallyOrderedMul.le_self_mul, le_self_mul
-/
theorem le_self_mul : a <= a * b :=
  CanonicallyOrderedMul.le_self_mul _ _

@[to_additive (attr := simp)]
/--
theorem `self_le_mul_left` / 定理 `self_le_mul_left`

English:
theorem self_le_mul_left
  given: (a b : α)
  statement: a <= b * a
  proof: le_mul_self

@[to_additive (attr := simp)]

中文:
定理 self_le_mul_left
  条件: (a b : α)
  结论: a <= b * a
  证明: le_mul_self

@[to_additive (attr := simp)]

Depends on / 依赖: le_mul_self
-/
theorem self_le_mul_left (a b : α) : a <= b * a :=
  le_mul_self

@[to_additive (attr := simp)]
/--
theorem `self_le_mul_right` / 定理 `self_le_mul_right`

English:
theorem self_le_mul_right
  given: (a b : α)
  statement: a <= a * b
  proof: le_self_mul

@[to_additive]

中文:
定理 self_le_mul_right
  条件: (a b : α)
  结论: a <= a * b
  证明: le_self_mul

@[to_additive]

Depends on / 依赖: le_self_mul
-/
theorem self_le_mul_right (a b : α) : a <= a * b :=
  le_self_mul

@[to_additive]
/--
theorem `le_iff_exists_mul` / 定理 `le_iff_exists_mul`

English:
theorem le_iff_exists_mul
  statement: a <= b ↔ exists c, b = a * c
  proof: ⟨exists_mul_of_le, by
    rintro ⟨c, rfl⟩
    exact le_self_mul⟩

中文:
定理 le_iff_存在_mul
  结论: a <= b ↔ 存在 c, b = a * c
  证明: ⟨exists_mul_of_le, by
    rintro ⟨c, rfl⟩
    exact le_self_mul⟩

Depends on / 依赖: exists_mul_of_le, le_self_mul
-/
theorem le_iff_exists_mul : a <= b ↔ exists c, b = a * c :=
  ⟨exists_mul_of_le, by
    rintro ⟨c, rfl⟩
    exact le_self_mul⟩

end LE

section Preorder
variable [Preorder α] [CanonicallyOrderedMul α] {a b c : α}

@[to_additive]
/--
theorem `le_of_mul_le_left` / 定理 `le_of_mul_le_left`

English:
theorem le_of_mul_le_left
  statement: a * b <= c -> a <= c
  proof: le_self_mul.trans

@[to_additive]

中文:
定理 le_of_mul_le_left
  结论: a * b <= c -> a <= c
  证明: le_self_mul.trans

@[to_additive]

Depends on / 依赖: le_self_mul, le_self_mul.trans
-/
theorem le_of_mul_le_left : a * b <= c -> a <= c :=
  le_self_mul.trans

@[to_additive]
/--
theorem `le_mul_of_le_left` / 定理 `le_mul_of_le_left`

English:
theorem le_mul_of_le_left
  statement: a <= b -> a <= b * c
  proof: le_self_mul.trans'

@[to_additive]

中文:
定理 le_mul_of_le_left
  结论: a <= b -> a <= b * c
  证明: le_self_mul.trans'

@[to_additive]

Depends on / 依赖: le_self_mul, le_self_mul.trans
-/
theorem le_mul_of_le_left : a <= b -> a <= b * c :=
  le_self_mul.trans'

@[to_additive]
/--
theorem `le_of_mul_le_right` / 定理 `le_of_mul_le_right`

English:
theorem le_of_mul_le_right
  statement: a * b <= c -> b <= c
  proof: le_mul_self.trans

@[to_additive]

中文:
定理 le_of_mul_le_right
  结论: a * b <= c -> b <= c
  证明: le_mul_self.trans

@[to_additive]

Depends on / 依赖: le_mul_self, le_mul_self.trans
-/
theorem le_of_mul_le_right : a * b <= c -> b <= c :=
  le_mul_self.trans

@[to_additive]
/--
theorem `le_mul_of_le_right` / 定理 `le_mul_of_le_right`

English:
theorem le_mul_of_le_right
  statement: a <= c -> a <= b * c
  proof: le_mul_self.trans'

@[to_additive] alias le_mul_left := le_mul_of_le_right
@[to_additive] alias le_mul_right := le_mul_of_le_left

中文:
定理 le_mul_of_le_right
  结论: a <= c -> a <= b * c
  证明: le_mul_self.trans'

@[to_additive] alias le_mul_left := le_mul_of_le_right
@[to_additive] alias le_mul_right := le_mul_of_le_left

Depends on / 依赖: le_mul_self, le_mul_self.trans
-/
theorem le_mul_of_le_right : a <= c -> a <= b * c :=
  le_mul_self.trans'

@[to_additive] alias le_mul_left := le_mul_of_le_right
@[to_additive] alias le_mul_right := le_mul_of_le_left

end Preorder

end Mul

section CommMagma
variable [CommMagma α] [Preorder α] [CanonicallyOrderedMul α] {a b c : α}

@[to_additive]
/--
theorem `le_iff_exists_mul'` / 定理 `le_iff_exists_mul'`

English:
theorem le_iff_exists_mul'
  statement: a <= b ↔ exists c, b = c * a
  proof: by
  simp only [mul_comm _ a, le_iff_exists_mul]

中文:
定理 le_iff_存在_mul'
  结论: a <= b ↔ 存在 c, b = c * a
  证明: by
  simp only [mul_comm _ a, le_iff_exists_mul]

Depends on / 依赖: le_iff_exists_mul, mul_comm
-/
theorem le_iff_exists_mul' : a <= b ↔ exists c, b = c * a := by
  simp only [mul_comm _ a, le_iff_exists_mul]

end CommMagma

section MulOneClass
variable [MulOneClass α]

section LE
variable [LE α] [CanonicallyOrderedMul α] {a b : α}

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsBotOneClass α
  body: le_self_mul.trans_eq (one_mul _)

中文:
实例 :
  签名: 是BotOne类 α
  定义体: le_self_mul.trans_eq (one_mul _)

Depends on / 依赖: le_self_mul, le_self_mul.trans_eq, one_mul, trans_eq
-/
instance : IsBotOneClass α where
  isBot_one _ := le_self_mul.trans_eq (one_mul _)

end LE

section PartialOrder
variable [PartialOrder α] [CanonicallyOrderedMul α] {a b c : α}

@[to_additive]
/--
theorem `exists_one_lt_mul_of_lt` / 定理 `exists_one_lt_mul_of_lt`

English:
theorem exists_one_lt_mul_of_lt
  given: (h : a < b)
  statement: exists (c : _) (_ : 1 < c), a * c = b
  proof: by
  obtain ⟨c, hc⟩ := le_iff_exists_mul.1 h.le
  refine ⟨c, one_lt_iff_ne_one.2 ?_, hc.symm⟩
  rintro rfl
  simp [hc] at h

@[to_additive]

中文:
定理 存在_one_lt_mul_of_lt
  条件: (h : a < b)
  结论: 存在 (c : _) (_ : 1 < c), a * c = b
  证明: by
  obtain ⟨c, hc⟩ := le_iff_exists_mul.1 h.le
  refine ⟨c, one_lt_iff_ne_one.2 ?_, hc.symm⟩
  rintro rfl
  simp [hc] at h

@[to_additive]

Depends on / 依赖: h.le, hc.symm, le_iff_exists_mul, one_lt_iff_ne_one
-/
theorem exists_one_lt_mul_of_lt (h : a < b) : exists (c : _) (_ : 1 < c), a * c = b := by
  obtain ⟨c, hc⟩ := le_iff_exists_mul.1 h.le
  refine ⟨c, one_lt_iff_ne_one.2 ?_, hc.symm⟩
  rintro rfl
  simp [hc] at h

@[to_additive]
/--
theorem `lt_iff_exists_mul` / 定理 `lt_iff_exists_mul`

English:
theorem lt_iff_exists_mul
  given: [MulLeftStrictMono α]
  statement: a < b ↔ exists c > 1, b = a * c
  proof: by
  rw [lt_iff_le_and_ne]; rw [le_iff_exists_mul]; rw [← exists_and_right]
  apply exists_congr
  intro c
  rw [and_comm]; rw [and_congr_left_iff]; rw [gt_iff_lt]
  rintro rfl
  constructor
  · rw [one_lt_iff_ne_one]
    apply mt
    rintro rfl
    rw [mul_one]
  · rw [← (self_le_mul_right a c).lt_

中文:
定理 lt_iff_存在_mul
  条件: [MulLeftStrictMono α]
  结论: a < b ↔ 存在 c > 1, b = a * c
  证明: by
  rw [lt_iff_le_and_ne]; rw [le_iff_exists_mul]; rw [← exists_and_right]
  apply exists_congr
  intro c
  rw [and_comm]; rw [and_congr_left_iff]; rw [gt_iff_lt]
  rintro rfl
  constructor
  · rw [one_lt_iff_ne_one]
    apply mt
    rintro rfl
    rw [mul_one]
  · rw [← (self_le_mul_right a c).lt_

Depends on / 依赖: and_comm, and_congr_left_iff, exists_and_right, exists_congr, gt_iff_lt, le_iff_exists_mul, lt_iff_le_and_ne, lt_iff_ne, lt_mul_of_one_lt_right, mul_one, one_lt_iff_ne_one, self_le_mul_right
-/
theorem lt_iff_exists_mul [MulLeftStrictMono α] : a < b ↔ exists c > 1, b = a * c := by
  rw [lt_iff_le_and_ne]; rw [le_iff_exists_mul]; rw [← exists_and_right]
  apply exists_congr
  intro c
  rw [and_comm]; rw [and_congr_left_iff]; rw [gt_iff_lt]
  rintro rfl
  constructor
  · rw [one_lt_iff_ne_one]
    apply mt
    rintro rfl
    rw [mul_one]
  · rw [← (self_le_mul_right a c).lt_iff_ne]
    apply lt_mul_of_one_lt_right'

end PartialOrder

end MulOneClass

section Semigroup
variable [Semigroup α]

section LE
variable [LE α] [CanonicallyOrderedMul α]

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 10) CanonicallyOrderedMul.toMulLeftMono :
    MulLeftMono α where
  elim a b c hbc := by
    obtain ⟨c, hc, rfl⟩ := exists_mul_of_le hbc
    rw [le_iff_exists_mul]
    exact ⟨c, (mul_assoc _ _ _).symm⟩

end LE

end Semigroup

-- TODO: make it an instance
@[to_additive]
/--
lemma `CanonicallyOrderedMul.toIsOrderedMonoid` / 引理 `CanonicallyOrderedMul.toIsOrderedMonoid`

English:
lemma CanonicallyOrderedMul.toIsOrderedMonoid
  proof: mul_le_mul_left

中文:
引理 典范有序乘法.toIsOrderedMonoid
  证明: mul_le_mul_left

Depends on / 依赖: mul_le_mul_left
-/
lemma CanonicallyOrderedMul.toIsOrderedMonoid
    [CommMonoid α] [Preorder α] [CanonicallyOrderedMul α] : IsOrderedMonoid α where
  mul_le_mul_left _ _ := mul_le_mul_left

section Monoid
variable [Monoid α]

section PartialOrder
variable [PartialOrder α] [CanonicallyOrderedMul α] {a b c : α}

/--
Instance `CanonicallyOrderedCommMonoid.toUniqueUnits` / 实例 `CanonicallyOrderedCommMonoid.toUniqueUnits`

English:
instance CanonicallyOrderedCommMonoid.toUniqueUnits
  signature: : Unique αˣ where
  body: Units.ext le_one_iff_eq_one.mp (le_of_mul_le_left a.mul_inv.le)

中文:
实例 CanonicallyOrderedCommMonoid.toUniqueUnits
  签名: : 唯一 αˣ where
  定义体: Units.ext le_one_iff_eq_one.mp (le_of_mul_le_left a.mul_inv.le)
-/
@[to_additive] instance CanonicallyOrderedCommMonoid.toUniqueUnits : Unique αˣ where
uniq a := Units.ext le_one_iff_eq_one.mp (le_of_mul_le_left a.mul_inv.le)

end PartialOrder

end Monoid

section CommMonoid
variable [CommMonoid α]

section PartialOrder
variable [PartialOrder α] [CanonicallyOrderedMul α] {a b c : α}

@[to_additive (attr := simp) add_pos_iff]
/--
theorem `one_lt_mul_iff` / 定理 `one_lt_mul_iff`

English:
theorem one_lt_mul_iff
  statement: 1 < a * b ↔ 1 < a ∨ 1 < b
  proof: by
  simp only [one_lt_iff_ne_one, Ne, mul_eq_one, not_and_or]

中文:
定理 one_lt_mul_iff
  结论: 1 < a * b ↔ 1 < a ∨ 1 < b
  证明: by
  simp only [one_lt_iff_ne_one, Ne, mul_eq_one, not_and_or]

Depends on / 依赖: mul_eq_one, not_and_or, one_lt_iff_ne_one
-/
theorem one_lt_mul_iff : 1 < a * b ↔ 1 < a ∨ 1 < b := by
  simp only [one_lt_iff_ne_one, Ne, mul_eq_one, not_and_or]

end PartialOrder

end CommMonoid

section CanonicallyLinearOrderedMonoid

variable [Monoid α] [LinearOrder α] [CanonicallyOrderedMul α]

@[to_additive]
/--
theorem `min_mul_distrib` / 定理 `min_mul_distrib`

English:
theorem min_mul_distrib
  given: (a b c : α)
  statement: min a (b * c) = min a (min a b * min a c)
  proof: by
  rcases le_total a b with hb | hb
  · simp [hb, le_mul_right]
  · rcases le_total a c with hc | hc
    · simp [hc, le_mul_left]
    · simp [hb, hc]

@[to_additive]

中文:
定理 min_mul_distrib
  条件: (a b c : α)
  结论: 最小值 a (b * c) = 最小值 a (最小值 a b * 最小值 a c)
  证明: by
  rcases le_total a b with hb | hb
  · simp [hb, le_mul_right]
  · rcases le_total a c with hc | hc
    · simp [hc, le_mul_left]
    · simp [hb, hc]

@[to_additive]

Depends on / 依赖: le_mul_left, le_mul_right, le_total
-/
theorem min_mul_distrib (a b c : α) : min a (b * c) = min a (min a b * min a c) := by
  rcases le_total a b with hb | hb
  · simp [hb, le_mul_right]
  · rcases le_total a c with hc | hc
    · simp [hc, le_mul_left]
    · simp [hb, hc]

@[to_additive]
/--
theorem `min_mul_distrib'` / 定理 `min_mul_distrib'`

English:
theorem min_mul_distrib'
  given: (a b c : α)
  statement: min (a * b) c = min (min a c * min b c) c
  proof: by
  simpa [min_comm _ c] using min_mul_distrib c a b

中文:
定理 min_mul_distrib'
  条件: (a b c : α)
  结论: 最小值 (a * b) c = 最小值 (最小值 a c * 最小值 b c) c
  证明: by
  simpa [min_comm _ c] using min_mul_distrib c a b

Depends on / 依赖: min_comm, min_mul_distrib
-/
theorem min_mul_distrib' (a b c : α) : min (a * b) c = min (min a c * min b c) c := by
  simpa [min_comm _ c] using min_mul_distrib c a b

/-- In a linearly ordered monoid, we are happy for `bot_eq_one` to be a `@[simp]` lemma. -/
@[to_additive (attr := simp)
/-- In a linearly ordered monoid, we are happy for `bot_eq_zero` to be a `@[simp]` lemma -/]
/--
theorem `bot_eq_one'` / 定理 `bot_eq_one'`

English:
theorem bot_eq_one'
  given: [OrderBot α]
  statement: (⊥ : α) = 1
  proof: bot_eq_one

中文:
定理 bot_eq_one'
  条件: [有底序 α]
  结论: (⊥ : α) = 1
  证明: bot_eq_one

Depends on / 依赖: bot_eq_one
-/
theorem bot_eq_one' [OrderBot α] : (⊥ : α) = 1 :=
  bot_eq_one

end CanonicallyLinearOrderedMonoid
