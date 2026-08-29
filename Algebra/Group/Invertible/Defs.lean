/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.Algebra.Group.Defs

/-!
# Invertible elements

This file defines a typeclass `Invertible a` for elements `a` with a two-sided
multiplicative inverse.

The intent of the typeclass is to provide a way to write e.g. `⅟2` in a ring
like `ℤ[1/2]` where some inverses exist but there is no general `⁻¹` operator;
or to specify that a field has characteristic `≠ 2`.
It is the `Type`-valued analogue to the `Prop`-valued `IsUnit`.

For constructions of the invertible element given a characteristic, see
`Algebra/CharP/Invertible` and other lemmas in that file.

## Notation

* `⅟a` is `Invertible.invOf a`, the inverse of `a`

## Implementation notes

The `Invertible` class lives in `Type`, not `Prop`, to make computation easier.
If multiplication is associative, `Invertible` is a subsingleton anyway.

The `simp` normal form tries to normalize `⅟a` to `a ⁻¹`. Otherwise, it pushes
`⅟` inside the expression as much as possible.

Since `Invertible a` is not a `Prop` (but it is a `Subsingleton`), we have to be careful about
coherence issues: we should avoid having multiple non-defeq instances for `Invertible a` in the
same context. This file plays it safe and uses `def` rather than `instance` for most definitions,
users can choose which instances to use at the point of use.

For example, here's how you can use an `Invertible 1` instance:
```lean
variable {α : Type*} [Monoid α]

def something_that_needs_inverses (x : α) [Invertible x] := sorry

section
attribute [local instance] invertibleOne
def something_one := something_that_needs_inverses 1
end
```

### Typeclass search vs. unification for `simp` lemmas

Note that since typeclass search searches the local context first, an instance argument like
`[Invertible a]` might sometimes be filled by a different term than the one we'd find by
unification (i.e., the one that's used as an implicit argument to `⅟`).

This can cause issues with `simp`. Therefore, some lemmas are duplicated, with the `@[simp]`
versions using unification and the user-facing ones using typeclass search.

Since unification can make backwards rewriting (e.g. `rw [← mylemma]`) impractical, we still want
the instance-argument versions; therefore the user-facing versions retain the instance arguments
and the original lemma name, whereas the `@[simp]`/unification ones acquire a `'` at the end of
their name.

We modify this file according to the above pattern only as needed; therefore, most `@[simp]` lemmas
here are not part of such a duplicate pair. This is not (yet) intended as a permanent solution.

See Zulip: [https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Invertible.201.20simps/near/320558233]

## Tags

invertible, inverse element, invOf, a half, one half, a third, one third, ½, ⅓

-/

@[expose] public section

assert_not_exists MonoidWithZero DenselyOrdered

universe u

variable {α : Type u}

/--
Definition of `Invertible` / `Invertible` 的定义

English:
class Invertible
  parameters: [Mul α] [One α] (a : α)
  axioms and operations (3):
    - invOf : α
    - invOf_mul_self : invOf * a = 1
    - mul_invOf_self : a * invOf = 1

中文:
类 可逆
  参数: [乘法 α] [幺 α] (a : α)
  公理与运算 (3 个):
    - invOf : α
    - invOf_mul_self : invOf * a = 1
    - mul_invOf_self : a * invOf = 1
-/
class Invertible [Mul α] [One α] (a : α) : Type u where
  /-- The inverse of an `Invertible` element -/
  invOf : α
  /-- `invOf a` is a left inverse of `a` -/
  invOf_mul_self : invOf * a = 1
  /-- `invOf a` is a right inverse of `a` -/
  mul_invOf_self : a * invOf = 1

/-- The inverse of an `Invertible` element -/
-- This notation has the same precedence as `Inv.inv`.
prefix:max "⅟" => Invertible.invOf

@[simp]
/--
theorem `invOf_mul_self'` / 定理 `invOf_mul_self'`

English:
theorem invOf_mul_self'
  given: [Mul α] [One α] (a : α) {_ : Invertible a}
  statement: ⅟a * a = 1
  proof: Invertible.invOf_mul_self

中文:
定理 invOf_mul_self'
  条件: [乘法 α] [幺 α] (a : α) {_ : 可逆 a}
  结论: ⅟a * a = 1
  证明: Invertible.invOf_mul_self

Depends on / 依赖: Invertible, Invertible.invOf_mul_self, invOf_mul_self
-/
theorem invOf_mul_self' [Mul α] [One α] (a : α) {_ : Invertible a} : ⅟a * a = 1 :=
  Invertible.invOf_mul_self

/--
theorem `invOf_mul_self` / 定理 `invOf_mul_self`

English:
theorem invOf_mul_self
  given: [Mul α] [One α] (a : α) [Invertible a]
  statement: ⅟a * a = 1
  proof: invOf_mul_self' _

@[simp]

中文:
定理 invOf_mul_self
  条件: [乘法 α] [幺 α] (a : α) [可逆 a]
  结论: ⅟a * a = 1
  证明: invOf_mul_self' _

@[simp]

Depends on / 依赖: invOf_mul_self
-/
theorem invOf_mul_self [Mul α] [One α] (a : α) [Invertible a] : ⅟a * a = 1 := invOf_mul_self' _

@[simp]
/--
theorem `mul_invOf_self'` / 定理 `mul_invOf_self'`

English:
theorem mul_invOf_self'
  given: [Mul α] [One α] (a : α) {_ : Invertible a}
  statement: a * ⅟a = 1
  proof: Invertible.mul_invOf_self

中文:
定理 mul_invOf_self'
  条件: [乘法 α] [幺 α] (a : α) {_ : 可逆 a}
  结论: a * ⅟a = 1
  证明: Invertible.mul_invOf_self

Depends on / 依赖: Invertible, Invertible.mul_invOf_self, mul_invOf_self
-/
theorem mul_invOf_self' [Mul α] [One α] (a : α) {_ : Invertible a} : a * ⅟a = 1 :=
  Invertible.mul_invOf_self

/--
theorem `mul_invOf_self` / 定理 `mul_invOf_self`

English:
theorem mul_invOf_self
  given: [Mul α] [One α] (a : α) [Invertible a]
  statement: a * ⅟a = 1
  proof: mul_invOf_self' _

中文:
定理 mul_invOf_self
  条件: [乘法 α] [幺 α] (a : α) [可逆 a]
  结论: a * ⅟a = 1
  证明: mul_invOf_self' _

Depends on / 依赖: mul_invOf_self
-/
theorem mul_invOf_self [Mul α] [One α] (a : α) [Invertible a] : a * ⅟a = 1 := mul_invOf_self' _

section Monoid

variable [Monoid α] (a b : α)

@[simp]
/--
theorem `invOf_mul_cancel_left'` / 定理 `invOf_mul_cancel_left'`

English:
theorem invOf_mul_cancel_left'
  given: {_ : Invertible a}
  statement: ⅟a * (a * b) = b
  proof: by
  rw [← mul_assoc]; rw [invOf_mul_self]; rw [one_mul]
example {G} [Group G] (a b : G) : a⁻¹ * (a * b) = b := inv_mul_cancel_left a b

中文:
定理 invOf_mul_cancel_left'
  条件: {_ : 可逆 a}
  结论: ⅟a * (a * b) = b
  证明: by
  rw [← mul_assoc]; rw [invOf_mul_self]; rw [one_mul]
example {G} [Group G] (a b : G) : a⁻¹ * (a * b) = b := inv_mul_cancel_left a b

Depends on / 依赖: example, invOf_mul_self, inv_mul_cancel_left, mul_assoc, one_mul
-/
theorem invOf_mul_cancel_left' {_ : Invertible a} : ⅟a * (a * b) = b := by
  rw [← mul_assoc]; rw [invOf_mul_self]; rw [one_mul]
example {G} [Group G] (a b : G) : a⁻¹ * (a * b) = b := inv_mul_cancel_left a b

/--
theorem `invOf_mul_cancel_left` / 定理 `invOf_mul_cancel_left`

English:
theorem invOf_mul_cancel_left
  given: [Invertible a]
  statement: ⅟a * (a * b) = b
  proof: invOf_mul_cancel_left' _ _

@[simp]

中文:
定理 invOf_mul_cancel_left
  条件: [可逆 a]
  结论: ⅟a * (a * b) = b
  证明: invOf_mul_cancel_left' _ _

@[simp]

Depends on / 依赖: invOf_mul_cancel_left
-/
theorem invOf_mul_cancel_left [Invertible a] : ⅟a * (a * b) = b :=
  invOf_mul_cancel_left' _ _

@[simp]
/--
theorem `mul_invOf_cancel_left'` / 定理 `mul_invOf_cancel_left'`

English:
theorem mul_invOf_cancel_left'
  given: {_ : Invertible a}
  statement: a * (⅟a * b) = b
  proof: by
  rw [← mul_assoc]; rw [mul_invOf_self]; rw [one_mul]
example {G} [Group G] (a b : G) : a * (a⁻¹ * b) = b := mul_inv_cancel_left a b

中文:
定理 mul_invOf_cancel_left'
  条件: {_ : 可逆 a}
  结论: a * (⅟a * b) = b
  证明: by
  rw [← mul_assoc]; rw [mul_invOf_self]; rw [one_mul]
example {G} [Group G] (a b : G) : a * (a⁻¹ * b) = b := mul_inv_cancel_left a b

Depends on / 依赖: example, mul_assoc, mul_invOf_self, mul_inv_cancel_left, one_mul
-/
theorem mul_invOf_cancel_left' {_ : Invertible a} : a * (⅟a * b) = b := by
  rw [← mul_assoc]; rw [mul_invOf_self]; rw [one_mul]
example {G} [Group G] (a b : G) : a * (a⁻¹ * b) = b := mul_inv_cancel_left a b

/--
theorem `mul_invOf_cancel_left` / 定理 `mul_invOf_cancel_left`

English:
theorem mul_invOf_cancel_left
  given: [Invertible a]
  statement: a * (⅟a * b) = b
  proof: mul_invOf_cancel_left' a b

@[simp]

中文:
定理 mul_invOf_cancel_left
  条件: [可逆 a]
  结论: a * (⅟a * b) = b
  证明: mul_invOf_cancel_left' a b

@[simp]

Depends on / 依赖: mul_invOf_cancel_left
-/
theorem mul_invOf_cancel_left [Invertible a] : a * (⅟a * b) = b :=
  mul_invOf_cancel_left' a b

@[simp]
/--
theorem `invOf_mul_cancel_right'` / 定理 `invOf_mul_cancel_right'`

English:
theorem invOf_mul_cancel_right'
  given: {_ : Invertible b}
  statement: a * ⅟b * b = a
  proof: by
  simp [mul_assoc]
example {G} [Group G] (a b : G) : a * b⁻¹ * b = a := inv_mul_cancel_right a b

中文:
定理 invOf_mul_cancel_right'
  条件: {_ : 可逆 b}
  结论: a * ⅟b * b = a
  证明: by
  simp [mul_assoc]
example {G} [Group G] (a b : G) : a * b⁻¹ * b = a := inv_mul_cancel_right a b

Depends on / 依赖: example, inv_mul_cancel_right, mul_assoc
-/
theorem invOf_mul_cancel_right' {_ : Invertible b} : a * ⅟b * b = a := by
  simp [mul_assoc]
example {G} [Group G] (a b : G) : a * b⁻¹ * b = a := inv_mul_cancel_right a b

/--
theorem `invOf_mul_cancel_right` / 定理 `invOf_mul_cancel_right`

English:
theorem invOf_mul_cancel_right
  given: [Invertible b]
  statement: a * ⅟b * b = a
  proof: invOf_mul_cancel_right' _ _

@[simp]

中文:
定理 invOf_mul_cancel_right
  条件: [可逆 b]
  结论: a * ⅟b * b = a
  证明: invOf_mul_cancel_right' _ _

@[simp]

Depends on / 依赖: invOf_mul_cancel_right
-/
theorem invOf_mul_cancel_right [Invertible b] : a * ⅟b * b = a :=
  invOf_mul_cancel_right' _ _

@[simp]
/--
theorem `mul_invOf_cancel_right'` / 定理 `mul_invOf_cancel_right'`

English:
theorem mul_invOf_cancel_right'
  given: {_ : Invertible b}
  statement: a * b * ⅟b = a
  proof: by
  simp [mul_assoc]
example {G} [Group G] (a b : G) : a * b * b⁻¹ = a := mul_inv_cancel_right a b

中文:
定理 mul_invOf_cancel_right'
  条件: {_ : 可逆 b}
  结论: a * b * ⅟b = a
  证明: by
  simp [mul_assoc]
example {G} [Group G] (a b : G) : a * b * b⁻¹ = a := mul_inv_cancel_right a b

Depends on / 依赖: example, mul_assoc, mul_inv_cancel_right
-/
theorem mul_invOf_cancel_right' {_ : Invertible b} : a * b * ⅟b = a := by
  simp [mul_assoc]
example {G} [Group G] (a b : G) : a * b * b⁻¹ = a := mul_inv_cancel_right a b

/--
theorem `mul_invOf_cancel_right` / 定理 `mul_invOf_cancel_right`

English:
theorem mul_invOf_cancel_right
  given: [Invertible b]
  statement: a * b * ⅟b = a
  proof: mul_invOf_cancel_right' _ _

中文:
定理 mul_invOf_cancel_right
  条件: [可逆 b]
  结论: a * b * ⅟b = a
  证明: mul_invOf_cancel_right' _ _

Depends on / 依赖: mul_invOf_cancel_right
-/
theorem mul_invOf_cancel_right [Invertible b] : a * b * ⅟b = a :=
  mul_invOf_cancel_right' _ _

variable {a b}

/--
theorem `invOf_eq_right_inv` / 定理 `invOf_eq_right_inv`

English:
theorem invOf_eq_right_inv
  given: [Invertible a] (hac : a * b = 1)
  statement: ⅟a = b
  proof: left_inv_eq_right_inv (invOf_mul_self _) hac

中文:
定理 invOf_eq_right_inv
  条件: [可逆 a] (hac : a * b = 1)
  结论: ⅟a = b
  证明: left_inv_eq_right_inv (invOf_mul_self _) hac

Depends on / 依赖: invOf_mul_self, left_inv_eq_right_inv
-/
theorem invOf_eq_right_inv [Invertible a] (hac : a * b = 1) : ⅟a = b :=
  left_inv_eq_right_inv (invOf_mul_self _) hac

/--
theorem `invOf_eq_left_inv` / 定理 `invOf_eq_left_inv`

English:
theorem invOf_eq_left_inv
  given: [Invertible a] (hac : b * a = 1)
  statement: ⅟a = b
  proof: (left_inv_eq_right_inv hac (mul_invOf_self _)).symm

中文:
定理 invOf_eq_left_inv
  条件: [可逆 a] (hac : b * a = 1)
  结论: ⅟a = b
  证明: (left_inv_eq_right_inv hac (mul_invOf_self _)).symm

Depends on / 依赖: left_inv_eq_right_inv, mul_invOf_self
-/
theorem invOf_eq_left_inv [Invertible a] (hac : b * a = 1) : ⅟a = b :=
  (left_inv_eq_right_inv hac (mul_invOf_self _)).symm

/--
theorem `invOf_eq_iff_right` / 定理 `invOf_eq_iff_right`

English:
theorem invOf_eq_iff_right
  given: [Invertible a]
  statement: ⅟a = b ↔ a * b = 1
  proof: ⟨fun h => by rw [← h, mul_invOf_self], invOf_eq_right_inv⟩

中文:
定理 invOf_eq_iff_right
  条件: [可逆 a]
  结论: ⅟a = b ↔ a * b = 1
  证明: ⟨fun h => by rw [← h, mul_invOf_self], invOf_eq_right_inv⟩

Depends on / 依赖: invOf_eq_right_inv, mul_invOf_self
-/
theorem invOf_eq_iff_right [Invertible a] : ⅟a = b ↔ a * b = 1 :=
  ⟨fun h => by rw [← h, mul_invOf_self], invOf_eq_right_inv⟩

/--
theorem `invOf_eq_iff_left` / 定理 `invOf_eq_iff_left`

English:
theorem invOf_eq_iff_left
  given: [Invertible a]
  statement: ⅟a = b ↔ b * a = 1
  proof: ⟨fun h => by rw [← h, invOf_mul_self], invOf_eq_left_inv⟩

中文:
定理 invOf_eq_iff_left
  条件: [可逆 a]
  结论: ⅟a = b ↔ b * a = 1
  证明: ⟨fun h => by rw [← h, invOf_mul_self], invOf_eq_left_inv⟩

Depends on / 依赖: invOf_eq_left_inv, invOf_mul_self
-/
theorem invOf_eq_iff_left [Invertible a] : ⅟a = b ↔ b * a = 1 :=
  ⟨fun h => by rw [← h, invOf_mul_self], invOf_eq_left_inv⟩

variable (a b)

/--
theorem `invertible_unique` / 定理 `invertible_unique`

English:
theorem invertible_unique
  statement: [Invertible a] [Invertible b]
  proof: by
  apply invOf_eq_right_inv
  rw [h]; rw [mul_invOf_self]

中文:
定理 invertible_unique
  结论: [可逆 a] [可逆 b]
  证明: by
  apply invOf_eq_right_inv
  rw [h]; rw [mul_invOf_self]

Depends on / 依赖: invOf_eq_right_inv, mul_invOf_self
-/
theorem invertible_unique [Invertible a] [Invertible b]
    (h : a = b) : ⅟a = ⅟b := by
  apply invOf_eq_right_inv
  rw [h]; rw [mul_invOf_self]

/--
Instance `Invertible.subsingleton` / 实例 `Invertible.subsingleton`

English:
instance Invertible.subsingleton
  signature: : Subsingleton (Invertible a)
  body: ⟨fun ⟨b, hba, hab⟩ ⟨c, _, hac⟩ => by
    congr
    exact left_inv_eq_right_inv hba hac⟩

中文:
实例 可逆.subsingleton
  签名: : 子单例 (可逆 a)
  定义体: ⟨fun ⟨b, hba, hab⟩ ⟨c, _, hac⟩ => by
    congr
    exact left_inv_eq_right_inv hba hac⟩

Depends on / 依赖: left_inv_eq_right_inv
-/
instance Invertible.subsingleton : Subsingleton (Invertible a) :=
  ⟨fun ⟨b, hba, hab⟩ ⟨c, _, hac⟩ => by
    congr
    exact left_inv_eq_right_inv hba hac⟩

/-- If `a` is invertible and `a = b`, then `⅟a = ⅟b`. -/
@[congr]
/--
theorem `Invertible.congr` / 定理 `Invertible.congr`

English:
theorem Invertible.congr
  given: [Invertible a] [Invertible b] (h : a = b)
  proof: invertible_unique a b h

中文:
定理 可逆.congr
  条件: [可逆 a] [可逆 b] (h : a = b)
  证明: invertible_unique a b h

Depends on / 依赖: invertible_unique
-/
theorem Invertible.congr [Invertible a] [Invertible b] (h : a = b) :
    ⅟a = ⅟b :=
  invertible_unique a b h

end Monoid

/-- If `r` is invertible and `s = r` and `si = ⅟r`, then `s` is invertible with `⅟s = si`. -/
@[instance_reducible]
/--
Definition of `Invertible.copy'` / `Invertible.copy'` 的定义

English:
definition Invertible.copy'
  signature: [MulOneClass α] {r : α} (hr : Invertible r) (s : α) (si : α) (hs : s = r)
  body: si
  invOf_mul_self := by rw [hs, hsi, invOf_mul_self]
  mul_invOf_self := by rw [hs, hsi, mul_invOf_self]

中文:
定义 可逆.copy'
  签名: [MulOne类 α] {r : α} (hr : 可逆 r) (s : α) (si : α) (hs : s = r)
  定义体: si
  invOf_mul_self := by rw [hs, hsi, invOf_mul_self]
  mul_invOf_self := by rw [hs, hsi, mul_invOf_self]
-/
def Invertible.copy' [MulOneClass α] {r : α} (hr : Invertible r) (s : α) (si : α) (hs : s = r)
    (hsi : si = ⅟r) : Invertible s where
  invOf := si
  invOf_mul_self := by rw [hs, hsi, invOf_mul_self]
  mul_invOf_self := by rw [hs, hsi, mul_invOf_self]

/--
Definition of `Invertible.copy` / `Invertible.copy` 的定义

English:
abbreviation Invertible.copy
  signature: [MulOneClass α] {r : α} (hr : Invertible r) (s : α) (hs : s = r)
  body: hr.copy' _ _ hs rfl

中文:
缩写 可逆.copy
  签名: [MulOne类 α] {r : α} (hr : 可逆 r) (s : α) (hs : s = r)
  定义体: hr.copy' _ _ hs rfl

Depends on / 依赖: hr.copy
-/
abbrev Invertible.copy [MulOneClass α] {r : α} (hr : Invertible r) (s : α) (hs : s = r) :
    Invertible s :=
  hr.copy' _ _ hs rfl

/-- Each element of a group is invertible. -/
@[instance_reducible]
/--
Definition of `invertibleOfGroup` / `invertibleOfGroup` 的定义

English:
definition invertibleOfGroup
  signature: [Group α] (a : α)
  body: ⟨a⁻¹, inv_mul_cancel a, mul_inv_cancel a⟩

@[simp]

中文:
定义 invertibleOfGroup
  签名: [群 α] (a : α)
  定义体: ⟨a⁻¹, inv_mul_cancel a, mul_inv_cancel a⟩

@[simp]

Depends on / 依赖: inv_mul_cancel, mul_inv_cancel
-/
def invertibleOfGroup [Group α] (a : α) : Invertible a :=
  ⟨a⁻¹, inv_mul_cancel a, mul_inv_cancel a⟩

@[simp]
/--
theorem `invOf_eq_group_inv` / 定理 `invOf_eq_group_inv`

English:
theorem invOf_eq_group_inv
  given: [Group α] (a : α) [Invertible a]
  statement: ⅟a = a⁻¹
  proof: invOf_eq_right_inv (mul_inv_cancel a)

中文:
定理 invOf_eq_group_inv
  条件: [群 α] (a : α) [可逆 a]
  结论: ⅟a = a⁻¹
  证明: invOf_eq_right_inv (mul_inv_cancel a)

Depends on / 依赖: invOf_eq_right_inv, mul_inv_cancel
-/
theorem invOf_eq_group_inv [Group α] (a : α) [Invertible a] : ⅟a = a⁻¹ :=
  invOf_eq_right_inv (mul_inv_cancel a)

/-- `1` is the inverse of itself -/
@[instance_reducible]
/--
Definition of `invertibleOne` / `invertibleOne` 的定义

English:
definition invertibleOne
  signature: [Monoid α]
  body: ⟨1, mul_one _, one_mul _⟩

@[simp]

中文:
定义 invertibleOne
  签名: [幺半群 α]
  定义体: ⟨1, mul_one _, one_mul _⟩

@[simp]

Depends on / 依赖: mul_one, one_mul
-/
def invertibleOne [Monoid α] : Invertible (1 : α) :=
  ⟨1, mul_one _, one_mul _⟩

@[simp]
/--
theorem `invOf_one'` / 定理 `invOf_one'`

English:
theorem invOf_one'
  given: [Monoid α] {_ : Invertible (1 : α)}
  statement: ⅟(1 : α) = 1
  proof: invOf_eq_right_inv (mul_one _)

中文:
定理 invOf_one'
  条件: [幺半群 α] {_ : 可逆 (1 : α)}
  结论: ⅟(1 : α) = 1
  证明: invOf_eq_right_inv (mul_one _)

Depends on / 依赖: invOf_eq_right_inv, mul_one
-/
theorem invOf_one' [Monoid α] {_ : Invertible (1 : α)} : ⅟(1 : α) = 1 :=
  invOf_eq_right_inv (mul_one _)

/--
theorem `invOf_one` / 定理 `invOf_one`

English:
theorem invOf_one
  given: [Monoid α] [Invertible (1 : α)]
  statement: ⅟(1 : α) = 1
  proof: invOf_one'

中文:
定理 invOf_one
  条件: [幺半群 α] [可逆 (1 : α)]
  结论: ⅟(1 : α) = 1
  证明: invOf_one'

Depends on / 依赖: invOf_one
-/
theorem invOf_one [Monoid α] [Invertible (1 : α)] : ⅟(1 : α) = 1 := invOf_one'

/--
Instance `invertibleInvOf` / 实例 `invertibleInvOf`

English:
instance invertibleInvOf
  signature: [One α] [Mul α] {a : α} [Invertible a]
  body: ⟨a, mul_invOf_self a, invOf_mul_self a⟩

@[simp]

中文:
实例 invertibleInvOf
  签名: [幺 α] [乘法 α] {a : α} [可逆 a]
  定义体: ⟨a, mul_invOf_self a, invOf_mul_self a⟩

@[simp]

Depends on / 依赖: invOf_mul_self, mul_invOf_self
-/
instance invertibleInvOf [One α] [Mul α] {a : α} [Invertible a] : Invertible (⅟a) :=
  ⟨a, mul_invOf_self a, invOf_mul_self a⟩

@[simp]
/--
theorem `invOf_invOf` / 定理 `invOf_invOf`

English:
theorem invOf_invOf
  given: [Monoid α] (a : α) [Invertible a] [Invertible (⅟a)]
  statement: ⅟(⅟a) = a
  proof: invOf_eq_right_inv (invOf_mul_self _)

@[simp]

中文:
定理 invOf_invOf
  条件: [幺半群 α] (a : α) [可逆 a] [可逆 (⅟a)]
  结论: ⅟(⅟a) = a
  证明: invOf_eq_right_inv (invOf_mul_self _)

@[simp]

Depends on / 依赖: invOf_eq_right_inv, invOf_mul_self
-/
theorem invOf_invOf [Monoid α] (a : α) [Invertible a] [Invertible (⅟a)] : ⅟(⅟a) = a :=
  invOf_eq_right_inv (invOf_mul_self _)

@[simp]
/--
theorem `invOf_inj` / 定理 `invOf_inj`

English:
theorem invOf_inj
  given: [Monoid α] {a b : α} [Invertible a] [Invertible b]
  statement: ⅟a = ⅟b ↔ a = b
  proof: ⟨invertible_unique _ _, invertible_unique _ _⟩

中文:
定理 invOf_inj
  条件: [幺半群 α] {a b : α} [可逆 a] [可逆 b]
  结论: ⅟a = ⅟b ↔ a = b
  证明: ⟨invertible_unique _ _, invertible_unique _ _⟩

Depends on / 依赖: invertible_unique
-/
theorem invOf_inj [Monoid α] {a b : α} [Invertible a] [Invertible b] : ⅟a = ⅟b ↔ a = b :=
  ⟨invertible_unique _ _, invertible_unique _ _⟩

/-- `⅟b * ⅟a` is the inverse of `a * b` -/
@[instance_reducible]
/--
Definition of `invertibleMul` / `invertibleMul` 的定义

English:
definition invertibleMul
  signature: [Monoid α] (a b : α) [Invertible a] [Invertible b]
  body: ⟨⅟b * ⅟a, by simp [← mul_assoc], by simp [← mul_assoc]⟩

@[simp]

中文:
定义 invertibleMul
  签名: [幺半群 α] (a b : α) [可逆 a] [可逆 b]
  定义体: ⟨⅟b * ⅟a, by simp [← mul_assoc], by simp [← mul_assoc]⟩

@[simp]

Depends on / 依赖: mul_assoc
-/
def invertibleMul [Monoid α] (a b : α) [Invertible a] [Invertible b] : Invertible (a * b) :=
  ⟨⅟b * ⅟a, by simp [← mul_assoc], by simp [← mul_assoc]⟩

@[simp]
/--
theorem `invOf_mul` / 定理 `invOf_mul`

English:
theorem invOf_mul
  given: [Monoid α] (a b : α) [Invertible a] [Invertible b] [Invertible (a * b)]
  proof: invOf_eq_right_inv (by simp [← mul_assoc])

中文:
定理 invOf_mul
  条件: [幺半群 α] (a b : α) [可逆 a] [可逆 b] [可逆 (a * b)]
  证明: invOf_eq_right_inv (by simp [← mul_assoc])

Depends on / 依赖: invOf_eq_right_inv, mul_assoc
-/
theorem invOf_mul [Monoid α] (a b : α) [Invertible a] [Invertible b] [Invertible (a * b)] :
    ⅟(a * b) = ⅟b * ⅟a :=
  invOf_eq_right_inv (by simp [← mul_assoc])

/--
Definition of `Invertible.mul` / `Invertible.mul` 的定义

English:
abbreviation Invertible.mul
  signature: [Monoid α] {a b : α} (_ : Invertible a) (_ : Invertible b)
  body: invertibleMul _ _

中文:
缩写 可逆.mul
  签名: [幺半群 α] {a b : α} (_ : 可逆 a) (_ : 可逆 b)
  定义体: invertibleMul _ _

Depends on / 依赖: invertibleMul
-/
abbrev Invertible.mul [Monoid α] {a b : α} (_ : Invertible a) (_ : Invertible b) :
    Invertible (a * b) :=
  invertibleMul _ _

section
variable [Monoid α] {a b c : α} [Invertible c]

variable (c) in
/--
theorem `mul_left_inj_of_invertible` / 定理 `mul_left_inj_of_invertible`

English:
theorem mul_left_inj_of_invertible
  statement: a * c = b * c ↔ a = b
  proof: ⟨fun h => by simpa using congr_arg (· * ⅟c) h, congr_arg (· * _)⟩

中文:
定理 mul_left_inj_of_invertible
  结论: a * c = b * c ↔ a = b
  证明: ⟨fun h => by simpa using congr_arg (· * ⅟c) h, congr_arg (· * _)⟩

Depends on / 依赖: congr_arg
-/
theorem mul_left_inj_of_invertible : a * c = b * c ↔ a = b :=
  ⟨fun h => by simpa using congr_arg (· * ⅟c) h, congr_arg (· * _)⟩

variable (c) in
/--
theorem `mul_right_inj_of_invertible` / 定理 `mul_right_inj_of_invertible`

English:
theorem mul_right_inj_of_invertible
  statement: c * a = c * b ↔ a = b
  proof: ⟨fun h => by simpa using congr_arg (⅟c * ·) h, congr_arg (_ * ·)⟩

中文:
定理 mul_right_inj_of_invertible
  结论: c * a = c * b ↔ a = b
  证明: ⟨fun h => by simpa using congr_arg (⅟c * ·) h, congr_arg (_ * ·)⟩

Depends on / 依赖: congr_arg
-/
theorem mul_right_inj_of_invertible : c * a = c * b ↔ a = b :=
  ⟨fun h => by simpa using congr_arg (⅟c * ·) h, congr_arg (_ * ·)⟩

/--
theorem `invOf_mul_eq_iff_eq_mul_left` / 定理 `invOf_mul_eq_iff_eq_mul_left`

English:
theorem invOf_mul_eq_iff_eq_mul_left
  statement: ⅟c * a = b ↔ a = c * b
  proof: by
  rw [← mul_right_inj_of_invertible (c := c)]; rw [mul_invOf_cancel_left]

中文:
定理 invOf_mul_eq_iff_eq_mul_left
  结论: ⅟c * a = b ↔ a = c * b
  证明: by
  rw [← mul_right_inj_of_invertible (c := c)]; rw [mul_invOf_cancel_left]

Depends on / 依赖: mul_invOf_cancel_left, mul_right_inj_of_invertible
-/
theorem invOf_mul_eq_iff_eq_mul_left : ⅟c * a = b ↔ a = c * b := by
  rw [← mul_right_inj_of_invertible (c := c)]; rw [mul_invOf_cancel_left]

/--
theorem `mul_left_eq_iff_eq_invOf_mul` / 定理 `mul_left_eq_iff_eq_invOf_mul`

English:
theorem mul_left_eq_iff_eq_invOf_mul
  statement: c * a = b ↔ a = ⅟c * b
  proof: by
  rw [← mul_right_inj_of_invertible (c := ⅟c)]; rw [invOf_mul_cancel_left]

中文:
定理 mul_left_eq_iff_eq_invOf_mul
  结论: c * a = b ↔ a = ⅟c * b
  证明: by
  rw [← mul_right_inj_of_invertible (c := ⅟c)]; rw [invOf_mul_cancel_left]

Depends on / 依赖: invOf_mul_cancel_left, mul_right_inj_of_invertible
-/
theorem mul_left_eq_iff_eq_invOf_mul : c * a = b ↔ a = ⅟c * b := by
  rw [← mul_right_inj_of_invertible (c := ⅟c)]; rw [invOf_mul_cancel_left]

/--
theorem `mul_invOf_eq_iff_eq_mul_right` / 定理 `mul_invOf_eq_iff_eq_mul_right`

English:
theorem mul_invOf_eq_iff_eq_mul_right
  statement: a * ⅟c = b ↔ a = b * c
  proof: by
  rw [← mul_left_inj_of_invertible (c := c)]; rw [invOf_mul_cancel_right]

中文:
定理 mul_invOf_eq_iff_eq_mul_right
  结论: a * ⅟c = b ↔ a = b * c
  证明: by
  rw [← mul_left_inj_of_invertible (c := c)]; rw [invOf_mul_cancel_right]

Depends on / 依赖: invOf_mul_cancel_right, mul_left_inj_of_invertible
-/
theorem mul_invOf_eq_iff_eq_mul_right : a * ⅟c = b ↔ a = b * c := by
  rw [← mul_left_inj_of_invertible (c := c)]; rw [invOf_mul_cancel_right]

/--
theorem `mul_right_eq_iff_eq_mul_invOf` / 定理 `mul_right_eq_iff_eq_mul_invOf`

English:
theorem mul_right_eq_iff_eq_mul_invOf
  statement: a * c = b ↔ a = b * ⅟c
  proof: by
  rw [← mul_left_inj_of_invertible (c := ⅟c)]; rw [mul_invOf_cancel_right]

中文:
定理 mul_right_eq_iff_eq_mul_invOf
  结论: a * c = b ↔ a = b * ⅟c
  证明: by
  rw [← mul_left_inj_of_invertible (c := ⅟c)]; rw [mul_invOf_cancel_right]

Depends on / 依赖: mul_invOf_cancel_right, mul_left_inj_of_invertible
-/
theorem mul_right_eq_iff_eq_mul_invOf : a * c = b ↔ a = b * ⅟c := by
  rw [← mul_left_inj_of_invertible (c := ⅟c)]; rw [mul_invOf_cancel_right]

variable [IsDedekindFiniteMonoid α] (a b : α)

/-- An element in a Dedekind-finite monoid is invertible if it has a left inverse. -/
@[instance_reducible]
/--
Definition of `invertibleOfLeftInverse` / `invertibleOfLeftInverse` 的定义

English:
definition invertibleOfLeftInverse
  signature: (h : b * a = 1)
  body: ⟨b, h, mul_eq_one_symm h⟩

中文:
定义 invertibleOfLeftInverse
  签名: (h : b * a = 1)
  定义体: ⟨b, h, mul_eq_one_symm h⟩

Depends on / 依赖: mul_eq_one_symm
-/
def invertibleOfLeftInverse (h : b * a = 1) : Invertible a :=
  ⟨b, h, mul_eq_one_symm h⟩

/-- An element in a Dedekind-finite monoid is invertible if it has a right inverse. -/
@[instance_reducible]
/--
Definition of `invertibleOfRightInverse` / `invertibleOfRightInverse` 的定义

English:
definition invertibleOfRightInverse
  signature: (h : a * b = 1)
  body: ⟨b, mul_eq_one_symm h, h⟩

中文:
定义 invertibleOfRightInverse
  签名: (h : a * b = 1)
  定义体: ⟨b, mul_eq_one_symm h, h⟩

Depends on / 依赖: mul_eq_one_symm
-/
def invertibleOfRightInverse (h : a * b = 1) : Invertible a :=
  ⟨b, mul_eq_one_symm h, h⟩

end
