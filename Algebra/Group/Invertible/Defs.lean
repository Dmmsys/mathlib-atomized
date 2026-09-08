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
same context.  This file plays it safe and uses `def` rather than `instance` for most definitions,
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

/-- `Invertible a` gives a two-sided multiplicative inverse of `a`. -/
/-
**Invertible** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{α : Type u} → [Mul α] → [One α] → α → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Invertible a` gives a two-sided multiplicative inverse of `a`.
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
/-
**invOf_mul_self'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：invOf_mul_self' [Mul α] [One α] (a : α) {_ : Invertible a} : ⅟a * a = 1
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Invertible.invOf_mul_self`：∀ {α : Type u} {inst : Mul α} {inst_1 : One α
} {a : α} [self : Invertible a], ⅟a * a = 1
-/
theorem invOf_mul_self' [Mul α] [One α] (a : α) {_ : Invertible a} : ⅟a * a = 1 :=
  Invertible.invOf_mul_self
/-
**invOf_mul_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：invOf_mul_self [Mul α] [One α] (a : α) [Invertible a] : ⅟a * a = 1
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `invOf_mul_self'`：invOf_mul_self' [Mul α] [One α] (a : α) {_ : Invertible
 a} : ⅟a * a = 1
-/
theorem invOf_mul_self [Mul α] [One α] (a : α) [Invertible a] : ⅟a * a = 1 := invOf_mul_self' _

@[simp]
/-
**mul_invOf_self'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_invOf_self' [Mul α] [One α] (a : α) {_ : Invertible a} : a * ⅟a = 1
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Invertible.mul_invOf_self`：∀ {α : Type u} {inst : Mul α} {inst_1 : One α
} {a : α} [self : Invertible a], a * ⅟a = 1
-/
theorem mul_invOf_self' [Mul α] [One α] (a : α) {_ : Invertible a} : a * ⅟a = 1 :=
  Invertible.mul_invOf_self
/-
**mul_invOf_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_invOf_self [Mul α] [One α] (a : α) [Invertible a] : a * ⅟a = 1
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_invOf_self'`：mul_invOf_self' [Mul α] [One α] (a : α) {_ : Invertible
 a} : a * ⅟a = 1
-/
theorem mul_invOf_self [Mul α] [One α] (a : α) [Invertible a] : a * ⅟a = 1 := mul_invOf_self' _

section Monoid

variable [Monoid α] (a b : α)

@[simp]
/-
**invOf_mul_cancel_left'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：invOf_mul_cancel_left' {_ : Invertible a} : ⅟a * (a * b) = b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `invOf_mul_self`：invOf_mul_self [Mul α] [One α] (a : α) [Invertible a] : 
⅟a * a = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem invOf_mul_cancel_left' {_ : Invertible a} : ⅟a * (a * b) = b := by
  rw [← mul_assoc, invOf_mul_self, one_mul]
/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example {G} [Group G] (a b : G) : a⁻¹ * (a * b) = b := inv_mul_cancel_left a b
/-
**invOf_mul_cancel_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：invOf_mul_cancel_left [Invertible a] : ⅟a * (a * b) = b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `invOf_mul_cancel_left'`：invOf_mul_cancel_left' {_ : Invertible a} : ⅟a *
 (a * b) = b
-/
theorem invOf_mul_cancel_left [Invertible a] : ⅟a * (a * b) = b :=
  invOf_mul_cancel_left' _ _

@[simp]
/-
**mul_invOf_cancel_left'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_invOf_cancel_left' {_ : Invertible a} : a * (⅟a * b) = b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_invOf_self`：mul_invOf_self [Mul α] [One α] (a : α) [Invertible a] : 
a * ⅟a = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem mul_invOf_cancel_left' {_ : Invertible a} : a * (⅟a * b) = b := by
  rw [← mul_assoc, mul_invOf_self, one_mul]
/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example {G} [Group G] (a b : G) : a * (a⁻¹ * b) = b := mul_inv_cancel_left a b
/-
**mul_invOf_cancel_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_invOf_cancel_left [Invertible a] : a * (⅟a * b) = b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_invOf_cancel_left'`：mul_invOf_cancel_left' {_ : Invertible a} : a * 
(⅟a * b) = b
-/
theorem mul_invOf_cancel_left [Invertible a] : a * (⅟a * b) = b :=
  mul_invOf_cancel_left' a b

@[simp]
/-
**invOf_mul_cancel_right'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：invOf_mul_cancel_right' {_ : Invertible b} : a * ⅟b * b = a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `invOf_mul_self'`：invOf_mul_self' [Mul α] [One α] (a : α) {_ : Invertible
 a} : ⅟a * a = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem invOf_mul_cancel_right' {_ : Invertible b} : a * ⅟b * b = a := by
  simp [mul_assoc]
/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example {G} [Group G] (a b : G) : a * b⁻¹ * b = a := inv_mul_cancel_right a b
/-
**invOf_mul_cancel_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：invOf_mul_cancel_right [Invertible b] : a * ⅟b * b = a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `invOf_mul_cancel_right'`：invOf_mul_cancel_right' {_ : Invertible b} : a 
* ⅟b * b = a
-/
theorem invOf_mul_cancel_right [Invertible b] : a * ⅟b * b = a :=
  invOf_mul_cancel_right' _ _

@[simp]
/-
**mul_invOf_cancel_right'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_invOf_cancel_right' {_ : Invertible b} : a * b * ⅟b = a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_invOf_self'`：mul_invOf_self' [Mul α] [One α] (a : α) {_ : Invertible
 a} : a * ⅟a = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mul_invOf_cancel_right' {_ : Invertible b} : a * b * ⅟b = a := by
  simp [mul_assoc]
/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example {G} [Group G] (a b : G) : a * b * b⁻¹ = a := mul_inv_cancel_right a b
/-
**mul_invOf_cancel_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_invOf_cancel_right [Invertible b] : a * b * ⅟b = a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_invOf_cancel_right'`：mul_invOf_cancel_right' {_ : Invertible b} : a 
* b * ⅟b = a
-/
theorem mul_invOf_cancel_right [Invertible b] : a * b * ⅟b = a :=
  mul_invOf_cancel_right' _ _

variable {a b}
/-
**invOf_eq_right_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：invOf_eq_right_inv [Invertible a] (hac : a * b = 1) : ⅟a = b
参数：hac : a * b = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `left_inv_eq_right_inv`：∀ {M : Type u_2} [inst : Monoid M] {a b c : M}, b
 * a = 1 → a * c = 1 → b = c
· 使用定理 `invOf_mul_self`：invOf_mul_self [Mul α] [One α] (a : α) [Invertible a] : 
⅟a * a = 1
-/
theorem invOf_eq_right_inv [Invertible a] (hac : a * b = 1) : ⅟a = b :=
  left_inv_eq_right_inv (invOf_mul_self _) hac
/-
**invOf_eq_left_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：invOf_eq_left_inv [Invertible a] (hac : b * a = 1) : ⅟a = b
参数：hac : b * a = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `left_inv_eq_right_inv`：∀ {M : Type u_2} [inst : Monoid M] {a b c : M}, b
 * a = 1 → a * c = 1 → b = c
· 使用定理 `mul_invOf_self`：mul_invOf_self [Mul α] [One α] (a : α) [Invertible a] : 
a * ⅟a = 1
-/
theorem invOf_eq_left_inv [Invertible a] (hac : b * a = 1) : ⅟a = b :=
  (left_inv_eq_right_inv hac (mul_invOf_self _)).symm
/-
**invOf_eq_iff_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：invOf_eq_iff_right [Invertible a] : ⅟a = b ↔ a * b = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_invOf_self`：mul_invOf_self [Mul α] [One α] (a : α) [Invertible a] : 
a * ⅟a = 1
· 使用定理 `invOf_eq_right_inv`：invOf_eq_right_inv [Invertible a] (hac : a * b = 1) 
: ⅟a = b
-/
theorem invOf_eq_iff_right [Invertible a] : ⅟a = b ↔ a * b = 1 :=
  ⟨fun h ↦ by rw [← h, mul_invOf_self], invOf_eq_right_inv⟩
/-
**invOf_eq_iff_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：invOf_eq_iff_left [Invertible a] : ⅟a = b ↔ b * a = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `invOf_mul_self`：invOf_mul_self [Mul α] [One α] (a : α) [Invertible a] : 
⅟a * a = 1
· 使用定理 `invOf_eq_left_inv`：invOf_eq_left_inv [Invertible a] (hac : b * a = 1) : 
⅟a = b
-/
theorem invOf_eq_iff_left [Invertible a] : ⅟a = b ↔ b * a = 1 :=
  ⟨fun h ↦ by rw [← h, invOf_mul_self], invOf_eq_left_inv⟩

variable (a b)
/-
**invertible_unique** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：invertible_unique [Invertible a] [Invertible b] (h : a = b) : ⅟a = ⅟b
参数：h : a = b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `invOf_eq_right_inv`：invOf_eq_right_inv [Invertible a] (hac : a * b = 1) 
: ⅟a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_invOf_self`：mul_invOf_self [Mul α] [One α] (a : α) [Invertible a] : 
a * ⅟a = 1
-/
theorem invertible_unique [Invertible a] [Invertible b]
    (h : a = b) : ⅟a = ⅟b := by
  apply invOf_eq_right_inv
  rw [h, mul_invOf_self]
/-
**Invertible.subsingleton** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Invertible.subsingleton : Subsingleton (Invertible a)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `left_inv_eq_right_inv`：∀ {M : Type u_2} [inst : Monoid M] {a b c : M}, b
 * a = 1 → a * c = 1 → b = c
-/
instance Invertible.subsingleton : Subsingleton (Invertible a) :=
  ⟨fun ⟨b, hba, hab⟩ ⟨c, _, hac⟩ => by
    congr
    exact left_inv_eq_right_inv hba hac⟩

/-- If `a` is invertible and `a = b`, then `⅟a = ⅟b`. -/
@[congr]
/-
**Invertible.congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Invertible.congr [Invertible a] [Invertible b] (h : a = b) : ⅟a = ⅟b
参数：h : a = b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `invertible_unique`：invertible_unique [Invertible a] [Invertible b] (h : 
a = b) : ⅟a = ⅟b

--- 原说明 ---
If `a` is invertible and `a = b`, then `⅟a = ⅟b`.
-/
theorem Invertible.congr [Invertible a] [Invertible b] (h : a = b) :
    ⅟a = ⅟b :=
  invertible_unique a b h

end Monoid

/-- If `r` is invertible and `s = r` and `si = ⅟r`, then `s` is invertible with `⅟s = si`. -/
@[instance_reducible]
/-
**Invertible.copy'** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Invertible.copy' [MulOneClass α] {r : α} (hr : Invertible r) (s : α) (si :
 α) (hs : s = r) (hsi : si = ⅟r) : Invertible s where invOf
参数：hr : Invertible r；s : α；si : α；hs : s = r；hsi : si = ⅟r。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `r` is invertible and `s = r` and `si = ⅟r`, then `s` is invertible with `⅟s 
= si`.
-/
def Invertible.copy' [MulOneClass α] {r : α} (hr : Invertible r) (s : α) (si : α) (hs : s = r)
    (hsi : si = ⅟r) : Invertible s where
  invOf := si
  invOf_mul_self := by rw [hs, hsi, invOf_mul_self]
  mul_invOf_self := by rw [hs, hsi, mul_invOf_self]

/-- If `r` is invertible and `s = r`, then `s` is invertible. -/
/-
**Invertible.copy** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Invertible.copy [MulOneClass α] {r : α} (hr : Invertible r) (s : α) (hs : 
s = r) : Invertible s
参数：hr : Invertible r；s : α；hs : s = r。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `r` is invertible and `s = r`, then `s` is invertible.
-/
abbrev Invertible.copy [MulOneClass α] {r : α} (hr : Invertible r) (s : α) (hs : s = r) :
    Invertible s :=
  hr.copy' _ _ hs rfl

/-- Each element of a group is invertible. -/
@[instance_reducible]
/-
**invertibleOfGroup** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：invertibleOfGroup [Group α] (a : α) : Invertible a
参数：a : α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1

--- 原说明 ---
Each element of a group is invertible.
-/
def invertibleOfGroup [Group α] (a : α) : Invertible a :=
  ⟨a⁻¹, inv_mul_cancel a, mul_inv_cancel a⟩

@[simp]
/-
**invOf_eq_group_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：invOf_eq_group_inv [Group α] (a : α) [Invertible a] : ⅟a = a⁻¹
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `invOf_eq_right_inv`：invOf_eq_right_inv [Invertible a] (hac : a * b = 1) 
: ⅟a = b
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
-/
theorem invOf_eq_group_inv [Group α] (a : α) [Invertible a] : ⅟a = a⁻¹ :=
  invOf_eq_right_inv (mul_inv_cancel a)

/-- `1` is the inverse of itself -/
@[instance_reducible]
/-
**invertibleOne** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：invertibleOne [Monoid α] : Invertible (1 : α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`1` is the inverse of itself
-/
def invertibleOne [Monoid α] : Invertible (1 : α) :=
  ⟨1, mul_one _, one_mul _⟩

@[simp]
/-
**invOf_one'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：invOf_one' [Monoid α] {_ : Invertible (1 : α)} : ⅟(1 : α) = 1
参数：1 : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `invOf_eq_right_inv`：invOf_eq_right_inv [Invertible a] (hac : a * b = 1) 
: ⅟a = b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem invOf_one' [Monoid α] {_ : Invertible (1 : α)} : ⅟(1 : α) = 1 :=
  invOf_eq_right_inv (mul_one _)
/-
**invOf_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：invOf_one [Monoid α] [Invertible (1 : α)] : ⅟(1 : α) = 1
参数：1 : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `invOf_one'`：invOf_one' [Monoid α] {_ : Invertible (1 : α)} : ⅟(1 : α) = 
1
-/
theorem invOf_one [Monoid α] [Invertible (1 : α)] : ⅟(1 : α) = 1 := invOf_one'

/-- `a` is the inverse of `⅟a`. -/
/-
**invertibleInvOf** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：invertibleInvOf [One α] [Mul α] {a : α} [Invertible a] : Invertible (⅟a)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_invOf_self`：mul_invOf_self [Mul α] [One α] (a : α) [Invertible a] : 
a * ⅟a = 1
· 使用定理 `invOf_mul_self`：invOf_mul_self [Mul α] [One α] (a : α) [Invertible a] : 
⅟a * a = 1

--- 原说明 ---
`a` is the inverse of `⅟a`.
-/
instance invertibleInvOf [One α] [Mul α] {a : α} [Invertible a] : Invertible (⅟a) :=
  ⟨a, mul_invOf_self a, invOf_mul_self a⟩

@[simp]
/-
**invOf_invOf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：invOf_invOf [Monoid α] (a : α) [Invertible a] [Invertible (⅟a)] : ⅟(⅟a) = 
a
参数：a : α；⅟a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `invOf_eq_right_inv`：invOf_eq_right_inv [Invertible a] (hac : a * b = 1) 
: ⅟a = b
· 使用定理 `invOf_mul_self`：invOf_mul_self [Mul α] [One α] (a : α) [Invertible a] : 
⅟a * a = 1
-/
theorem invOf_invOf [Monoid α] (a : α) [Invertible a] [Invertible (⅟a)] : ⅟(⅟a) = a :=
  invOf_eq_right_inv (invOf_mul_self _)

@[simp]
/-
**invOf_inj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：invOf_inj [Monoid α] {a b : α} [Invertible a] [Invertible b] : ⅟a = ⅟b ↔ a
 = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `invertible_unique`：invertible_unique [Invertible a] [Invertible b] (h : 
a = b) : ⅟a = ⅟b
-/
theorem invOf_inj [Monoid α] {a b : α} [Invertible a] [Invertible b] : ⅟a = ⅟b ↔ a = b :=
  ⟨invertible_unique _ _, invertible_unique _ _⟩

/-- `⅟b * ⅟a` is the inverse of `a * b` -/
@[instance_reducible]
/-
**invertibleMul** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：invertibleMul [Monoid α] (a b : α) [Invertible a] [Invertible b] : Inverti
ble (a * b)
参数：a b : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`⅟b * ⅟a` is the inverse of `a * b`
-/
def invertibleMul [Monoid α] (a b : α) [Invertible a] [Invertible b] : Invertible (a * b) :=
  ⟨⅟b * ⅟a, by simp [← mul_assoc], by simp [← mul_assoc]⟩

@[simp]
/-
**invOf_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：invOf_mul [Monoid α] (a b : α) [Invertible a] [Invertible b] [Invertible (
a * b)] : ⅟(a * b) = ⅟b * ⅟a
参数：a b : α；a * b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `invOf_eq_right_inv`：invOf_eq_right_inv [Invertible a] (hac : a * b = 1) 
: ⅟a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_invOf_cancel_right'`：mul_invOf_cancel_right' {_ : Invertible b} : a 
* b * ⅟b = a
· 使用定理 `mul_invOf_self'`：mul_invOf_self' [Mul α] [One α] (a : α) {_ : Invertible
 a} : a * ⅟a = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem invOf_mul [Monoid α] (a b : α) [Invertible a] [Invertible b] [Invertible (a * b)] :
    ⅟(a * b) = ⅟b * ⅟a :=
  invOf_eq_right_inv (by simp [← mul_assoc])

/-- A copy of `invertibleMul` for dot notation. -/
/-
**Invertible.mul** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Invertible.mul [Monoid α] {a b : α} (_ : Invertible a) (_ : Invertible b) 
: Invertible (a * b)
参数：_ : Invertible a；_ : Invertible b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A copy of `invertibleMul` for dot notation.
-/
abbrev Invertible.mul [Monoid α] {a b : α} (_ : Invertible a) (_ : Invertible b) :
    Invertible (a * b) :=
  invertibleMul _ _

section
variable [Monoid α] {a b c : α} [Invertible c]

variable (c) in
/-
**mul_left_inj_of_invertible** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_left_inj_of_invertible : a * c = b * c ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_invOf_cancel_right'`：mul_invOf_cancel_right' {_ : Invertible b} : a 
* b * ⅟b = a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem mul_left_inj_of_invertible : a * c = b * c ↔ a = b :=
  ⟨fun h => by simpa using congr_arg (· * ⅟c) h, congr_arg (· * _)⟩

variable (c) in
/-
**mul_right_inj_of_invertible** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_right_inj_of_invertible : c * a = c * b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `invOf_mul_cancel_left'`：invOf_mul_cancel_left' {_ : Invertible a} : ⅟a *
 (a * b) = b
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem mul_right_inj_of_invertible : c * a = c * b ↔ a = b :=
  ⟨fun h => by simpa using congr_arg (⅟c * ·) h, congr_arg (_ * ·)⟩
/-
**invOf_mul_eq_iff_eq_mul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：invOf_mul_eq_iff_eq_mul_left : ⅟c * a = b ↔ a = c * b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_right_inj_of_invertible`：mul_right_inj_of_invertible : c * a = c * b
 ↔ a = b
· 使用定理 `mul_invOf_cancel_left`：mul_invOf_cancel_left [Invertible a] : a * (⅟a * 
b) = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem invOf_mul_eq_iff_eq_mul_left : ⅟c * a = b ↔ a = c * b := by
  rw [← mul_right_inj_of_invertible (c := c), mul_invOf_cancel_left]
/-
**mul_left_eq_iff_eq_invOf_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_left_eq_iff_eq_invOf_mul : c * a = b ↔ a = ⅟c * b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_right_inj_of_invertible`：mul_right_inj_of_invertible : c * a = c * b
 ↔ a = b
· 使用定理 `invOf_mul_cancel_left`：invOf_mul_cancel_left [Invertible a] : ⅟a * (a * 
b) = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mul_left_eq_iff_eq_invOf_mul : c * a = b ↔ a = ⅟c * b := by
  rw [← mul_right_inj_of_invertible (c := ⅟c), invOf_mul_cancel_left]
/-
**mul_invOf_eq_iff_eq_mul_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_invOf_eq_iff_eq_mul_right : a * ⅟c = b ↔ a = b * c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_left_inj_of_invertible`：mul_left_inj_of_invertible : a * c = b * c ↔
 a = b
· 使用定理 `invOf_mul_cancel_right`：invOf_mul_cancel_right [Invertible b] : a * ⅟b *
 b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mul_invOf_eq_iff_eq_mul_right : a * ⅟c = b ↔ a = b * c := by
  rw [← mul_left_inj_of_invertible (c := c), invOf_mul_cancel_right]
/-
**mul_right_eq_iff_eq_mul_invOf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_right_eq_iff_eq_mul_invOf : a * c = b ↔ a = b * ⅟c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_left_inj_of_invertible`：mul_left_inj_of_invertible : a * c = b * c ↔
 a = b
· 使用定理 `mul_invOf_cancel_right`：mul_invOf_cancel_right [Invertible b] : a * b * 
⅟b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mul_right_eq_iff_eq_mul_invOf : a * c = b ↔ a = b * ⅟c := by
  rw [← mul_left_inj_of_invertible (c := ⅟c), mul_invOf_cancel_right]

variable [IsDedekindFiniteMonoid α] (a b : α)

/-- An element in a Dedekind-finite monoid is invertible if it has a left inverse. -/
@[instance_reducible]
/-
**invertibleOfLeftInverse** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：invertibleOfLeftInverse (h : b * a = 1) : Invertible a
参数：h : b * a = 1。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An element in a Dedekind-finite monoid is invertible if it has a left inverse.
-/
def invertibleOfLeftInverse (h : b * a = 1) : Invertible a :=
  ⟨b, h, mul_eq_one_symm h⟩

/-- An element in a Dedekind-finite monoid is invertible if it has a right inverse. -/
@[instance_reducible]
/-
**invertibleOfRightInverse** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：invertibleOfRightInverse (h : a * b = 1) : Invertible a
参数：h : a * b = 1。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An element in a Dedekind-finite monoid is invertible if it has a right inverse.
-/
def invertibleOfRightInverse (h : a * b = 1) : Invertible a :=
  ⟨b, mul_eq_one_symm h, h⟩

end

