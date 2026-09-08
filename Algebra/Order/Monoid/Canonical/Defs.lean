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

/-- An ordered additive monoid is `CanonicallyOrderedAdd`
if the ordering coincides with the subtractibility relation,
which is to say, `a ≤ b` iff there exists `c` with `b = a + c`.
This is satisfied by the natural numbers, for example, but not
the integers or other nontrivial ordered groups.

We have `a ≤ b + a` and `a ≤ a + b` as separate fields. In the commutative case the second field
is redundant, but in the noncommutative case (satisfied most relevantly by the ordinals), this
extra field allows us to prove more things without the extra commutativity assumption. -/
/-
**CanonicallyOrderedAdd** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_1) → [Add α] → [LE α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An ordered additive monoid is `CanonicallyOrderedAdd`
if the ordering coincides with the subtractibility relation,
which is to say, `a ≤ b` iff there exists `c` with `b = a + c`.
This is satisfied by the natural numbers, for example, but not
the integers or other nontrivial ordered groups.

We have `a ≤ b + a` and `a ≤ a + b` as separate fields. In the commutative case 
the second field
is redundant, but in the noncommutative case (satisfied most relevantly by the o
rdinals), this
extra field allows us to prove more things without the extra commutativity assum
ption.
-/
class CanonicallyOrderedAdd (α : Type*) [Add α] [LE α] : Prop
    extends ExistsAddOfLE α where
  /-- For any `a` and `b`, `a ≤ a + b` -/
  protected le_add_self : ∀ a b : α, a ≤ b + a
  protected le_self_add : ∀ a b : α, a ≤ a + b

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
/-
**CanonicallyOrderedMul** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_1) → [Mul α] → [LE α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An ordered monoid is `CanonicallyOrderedMul`
  if the ordering coincides with the divisibility relation,
  which is to say, `a ≤ b` iff there exists `c` with `b = a * c`.
  Examples seem rare; it seems more likely that the `OrderDual`
  of a naturally-occurring lattice satisfies this than the lattice
  itself (for example, dual of the lattice of ideals of a PID or
  Dedekind domain satisfy this; collections of all things ≤ 1 seem to
  be more natural that collections of all things ≥ 1).
-/
class CanonicallyOrderedMul (α : Type*) [Mul α] [LE α] : Prop
    extends ExistsMulOfLE α where
  /-- For any `a` and `b`, `a ≤ a * b` -/
  protected le_mul_self : ∀ a b : α, a ≤ b * a
  protected le_self_mul : ∀ a b : α, a ≤ a * b

attribute [instance 50] CanonicallyOrderedMul.toExistsMulOfLE

section Mul
variable [Mul α]

section LE
variable [LE α] [CanonicallyOrderedMul α] {a b c : α}

@[to_additive]
/-
**le_mul_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_mul_self : a <= b * a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanonicallyOrderedMul.le_mul_self`：∀ {α : Type u_1} {inst : Mul α} {inst
_1 : LE α} [self : CanonicallyOrderedMul α] (a b : α), a ≤ b * a
-/
theorem le_mul_self : a ≤ b * a :=
  CanonicallyOrderedMul.le_mul_self _ _

@[to_additive]
/-
**le_self_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_self_mul : a <= a * b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanonicallyOrderedMul.le_self_mul`：∀ {α : Type u_1} {inst : Mul α} {inst
_1 : LE α} [self : CanonicallyOrderedMul α] (a b : α), a ≤ a * b
-/
theorem le_self_mul : a ≤ a * b :=
  CanonicallyOrderedMul.le_self_mul _ _

@[to_additive (attr := simp)]
/-
**self_le_mul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：self_le_mul_left (a b : α) : a <= b * a
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_mul_self`：le_mul_self : a <= b * a
-/
theorem self_le_mul_left (a b : α) : a ≤ b * a :=
  le_mul_self

@[to_additive (attr := simp)]
/-
**self_le_mul_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：self_le_mul_right (a b : α) : a <= a * b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_self_mul`：le_self_mul : a <= a * b
-/
theorem self_le_mul_right (a b : α) : a ≤ a * b :=
  le_self_mul

@[to_additive]
/-
**le_iff_exists_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_iff_exists_mul : a <= b ↔ exists c, b = a * c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ExistsMulOfLE.exists_mul_of_le`：∀ {α : Type u} {inst : Mul α} {inst_1 : 
LE α} [self : ExistsMulOfLE α] {a b : α}, a ≤ b → ∃ c, b = a * c
· 使用定理 `CanonicallyOrderedMul.toExistsMulOfLE`：∀ {α : Type u_1} {inst : Mul α} {
inst_1 : LE α} [self : CanonicallyOrderedMul α], ExistsMulOfLE α
· 使用定理 `le_self_mul`：le_self_mul : a <= a * b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem le_iff_exists_mul : a ≤ b ↔ ∃ c, b = a * c :=
  ⟨exists_mul_of_le, by
    rintro ⟨c, rfl⟩
    exact le_self_mul⟩

end LE

section Preorder
variable [Preorder α] [CanonicallyOrderedMul α] {a b c : α}

@[to_additive]
/-
**le_of_mul_le_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_of_mul_le_left : a * b <= c -> a <= c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_self_mul`：le_self_mul : a <= a * b
-/
theorem le_of_mul_le_left : a * b ≤ c → a ≤ c :=
  le_self_mul.trans

@[to_additive]
/-
**le_mul_of_le_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_mul_of_le_left : a <= b -> a <= b * c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b ≤ a → 
c ≤ b → c ≤ a
· 使用定理 `le_self_mul`：le_self_mul : a <= a * b
-/
theorem le_mul_of_le_left : a ≤ b → a ≤ b * c :=
  le_self_mul.trans'

@[to_additive]
/-
**le_of_mul_le_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_of_mul_le_right : a * b <= c -> b <= c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_mul_self`：le_mul_self : a <= b * a
-/
theorem le_of_mul_le_right : a * b ≤ c → b ≤ c :=
  le_mul_self.trans

@[to_additive]
/-
**le_mul_of_le_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_mul_of_le_right : a <= c -> a <= b * c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b ≤ a → 
c ≤ b → c ≤ a
· 使用定理 `le_mul_self`：le_mul_self : a <= b * a
-/
theorem le_mul_of_le_right : a ≤ c → a ≤ b * c :=
  le_mul_self.trans'

@[to_additive] alias le_mul_left := le_mul_of_le_right
@[to_additive] alias le_mul_right := le_mul_of_le_left

end Preorder

end Mul

section CommMagma
variable [CommMagma α] [Preorder α] [CanonicallyOrderedMul α] {a b c : α}

@[to_additive]
/-
**le_iff_exists_mul'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_iff_exists_mul' : a <= b ↔ exists c, b = c * a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem le_iff_exists_mul' : a ≤ b ↔ ∃ c, b = c * a := by
  simp only [mul_comm _ a, le_iff_exists_mul]

end CommMagma

section MulOneClass
variable [MulOneClass α]

section LE
variable [LE α] [CanonicallyOrderedMul α] {a b : α}

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsBotOneClass α where
  isBot_one _ := le_self_mul.trans_eq (one_mul _)

end LE

section PartialOrder
variable [PartialOrder α] [CanonicallyOrderedMul α] {a b c : α}

@[to_additive]
/-
**exists_one_lt_mul_of_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_one_lt_mul_of_lt (h : a < b) : exists (c : _) (_ : 1 < c), a * c = 
b
参数：h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_iff_exists_mul`：le_iff_exists_mul : a <= b ↔ exists c, b = a * c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `one_lt_iff_ne_one`：one_lt_iff_ne_one : 1 < a ↔ a != 1
· 使用定理 `instIsBotOneClass`：∀ {α : Type u} [inst : MulOneClass α] [inst_1 : LE α]
 [CanonicallyOrderedMul α], IsBotOneClass α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem exists_one_lt_mul_of_lt (h : a < b) : ∃ (c : _) (_ : 1 < c), a * c = b := by
  obtain ⟨c, hc⟩ := le_iff_exists_mul.1 h.le
  refine ⟨c, one_lt_iff_ne_one.2 ?_, hc.symm⟩
  rintro rfl
  simp [hc] at h

@[to_additive]
/-
**lt_iff_exists_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_iff_exists_mul [MulLeftStrictMono α] : a < b ↔ exists c > 1, b = a * c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `lt_iff_le_and_ne`：lt_iff_le_and_ne : a < b ↔ a <= b ∧ a != b
· 使用定理 `le_iff_exists_mul`：le_iff_exists_mul : a <= b ↔ exists c, b = a * c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `exists_and_right`：∀ {α : Sort u_1} {p : α → Prop} {b : Prop}, (∃ x, p x 
∧ b) ↔ (∃ x, p x) ∧ b
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `and_congr_left_iff`：∀ {a c b : Prop}, (a ∧ c ↔ b ∧ c) ↔ c → (a ↔ b)
· 使用定理 `gt_iff_lt`：∀ {α : Type u_1} [inst : LT α] {x y : α}, x > y ↔ y < x
· 使用定理 `one_lt_iff_ne_one`：one_lt_iff_ne_one : 1 < a ↔ a != 1
· 使用定理 `instIsBotOneClass`：∀ {α : Type u} [inst : MulOneClass α] [inst_1 : LE α]
 [CanonicallyOrderedMul α], IsBotOneClass α
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `LE.le.lt_iff_ne`：lt_iff_ne (h : a <= b) : a < b ↔ a != b
· 使用定理 `self_le_mul_right`：self_le_mul_right (a b : α) : a <= a * b
· 使用定理 `lt_mul_of_one_lt_right'`：lt_mul_of_one_lt_right' [MulLeftStrictMono α] (
a : α) {b : α} (h : 1 < b) : a < a * b
-/
theorem lt_iff_exists_mul [MulLeftStrictMono α] : a < b ↔ ∃ c > 1, b = a * c := by
  rw [lt_iff_le_and_ne, le_iff_exists_mul, ← exists_and_right]
  apply exists_congr
  intro c
  rw [and_comm, and_congr_left_iff, gt_iff_lt]
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
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
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
/-
**CanonicallyOrderedMul.toIsOrderedMonoid** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CanonicallyOrderedMul.toIsOrderedMonoid [CommMonoid α] [Preorder α] [Canon
icallyOrderedMul α] : IsOrderedMonoid α where mul_le_mul_left _ _
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_le_mul_left`：mul_le_mul_left [i : MulRightMono α] {b c : α} (bc : b 
<= c) (a : α) : b * a <= c * a
· 使用定理 `CanonicallyOrderedMul.toMulLeftMono`：∀ {α : Type u} [inst : Semigroup α]
 [inst_1 : LE α] [CanonicallyOrderedMul α], MulLeftMono α
-/
lemma CanonicallyOrderedMul.toIsOrderedMonoid
    [CommMonoid α] [Preorder α] [CanonicallyOrderedMul α] : IsOrderedMonoid α where
  mul_le_mul_left _ _ := mul_le_mul_left

section Monoid
variable [Monoid α]

section PartialOrder
variable [PartialOrder α] [CanonicallyOrderedMul α] {a b c : α}

/-
**CanonicallyOrderedCommMonoid.toUniqueUnits** 是 Mathlib 中的一个定义，位于命名空间 `Canonica
llyOrderedCommMonoid`。
形式化陈述：{α : Type u} → [inst : Monoid α] → [inst_1 : PartialOrder α] → [Canonicall
yOrderedMul α] → Unique αˣ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance CanonicallyOrderedCommMonoid.toUniqueUnits : Unique αˣ where
  uniq a := Units.ext <| le_one_iff_eq_one.mp (le_of_mul_le_left a.mul_inv.le)

end PartialOrder

end Monoid

section CommMonoid
variable [CommMonoid α]

section PartialOrder
variable [PartialOrder α] [CanonicallyOrderedMul α] {a b c : α}

@[to_additive (attr := simp) add_pos_iff]
/-
**one_lt_mul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：one_lt_mul_iff : 1 < a * b ↔ 1 < a ∨ 1 < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsBotOneClass`：∀ {α : Type u} [inst : MulOneClass α] [inst_1 : LE α]
 [CanonicallyOrderedMul α], IsBotOneClass α
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem one_lt_mul_iff : 1 < a * b ↔ 1 < a ∨ 1 < b := by
  simp only [one_lt_iff_ne_one, Ne, mul_eq_one, not_and_or]

end PartialOrder

end CommMonoid

section CanonicallyLinearOrderedMonoid

variable [Monoid α] [LinearOrder α] [CanonicallyOrderedMul α]

@[to_additive]
/-
**min_mul_distrib** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：min_mul_distrib (a b c : α) : min a (b * c) = min a (min a b * min a c)
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
-/
theorem min_mul_distrib (a b c : α) : min a (b * c) = min a (min a b * min a c) := by
  rcases le_total a b with hb | hb
  · simp [hb, le_mul_right]
  · rcases le_total a c with hc | hc
    · simp [hc, le_mul_left]
    · simp [hb, hc]

@[to_additive]
/-
**min_mul_distrib'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：min_mul_distrib' (a b c : α) : min (a * b) c = min (min a c * min b c) c
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `min_comm`：min_comm (a b : α) : min a b = min b a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `min_mul_distrib`：min_mul_distrib (a b c : α) : min a (b * c) = min a (mi
n a b * min a c)
-/
theorem min_mul_distrib' (a b c : α) : min (a * b) c = min (min a c * min b c) c := by
  simpa [min_comm _ c] using min_mul_distrib c a b

/-- In a linearly ordered monoid, we are happy for `bot_eq_one` to be a `@[simp]` lemma. -/
@[to_additive (attr := simp)
/-- In a linearly ordered monoid, we are happy for `bot_eq_zero` to be a `@[simp]` lemma -/]
/-
**bot_eq_one'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bot_eq_one' [OrderBot α] : (⊥ : α) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_eq_one`：bot_eq_one [OrderBot α] : (⊥ : α) = 1
· 使用定理 `instIsBotOneClass`：∀ {α : Type u} [inst : MulOneClass α] [inst_1 : LE α]
 [CanonicallyOrderedMul α], IsBotOneClass α
-/
theorem bot_eq_one' [OrderBot α] : (⊥ : α) = 1 :=
  bot_eq_one

end CanonicallyLinearOrderedMonoid

