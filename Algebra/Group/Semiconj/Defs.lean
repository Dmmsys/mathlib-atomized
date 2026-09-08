/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
-- Some proofs and docs came from mathlib3 `src/algebra/commute.lean` (c) Neil Strickland
module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Order.Defs.Unbundled

/-!
# Semiconjugate elements of a semigroup

## Main definitions

We say that `x` is semiconjugate to `y` by `a` (`SemiconjBy a x y`), if `a * x = y * a`.
In this file we provide operations on `SemiconjBy _ _ _`.

In the names of these operations, we treat `a` as the “left” argument, and both `x` and `y` as
“right” arguments. This way most names in this file agree with the names of the corresponding lemmas
for `Commute a b = SemiconjBy a b b`. As a side effect, some lemmas have only `_right` version.

Lean does not immediately recognise these terms as equations, so for rewriting we need syntax like
`rw [(h.pow_right 5).eq]` rather than just `rw [h.pow_right 5]`.

This file provides only basic operations (`mul_left`, `mul_right`, `inv_right` etc). Other
operations (`pow_right`, field inverse etc) are in the files that define corresponding notions.
-/

@[expose] public section

assert_not_exists MonoidWithZero DenselyOrdered

variable {S M G : Type*}

/-- `x` is semiconjugate to `y` by `a`, if `a * x = y * a`. -/
@[to_additive /-- `x` is additive semiconjugate to `y` by `a` if `a + x = y + a` -/]
/-
**SemiconjBy** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：SemiconjBy [Mul M] (a x y : M) : Prop
参数：a x y : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`x` is semiconjugate to `y` by `a`, if `a * x = y * a`.
-/
def SemiconjBy [Mul M] (a x y : M) : Prop :=
  a * x = y * a

namespace SemiconjBy

/-- Equality behind `SemiconjBy a x y`; useful for rewriting. -/
@[to_additive /-- Equality behind `AddSemiconjBy a x y`; useful for rewriting. -/]
/-
**SemiconjBy.eq** 是 Mathlib 中的一个定理，位于命名空间 `SemiconjBy`。
形式化陈述：∀ {S : Type u_1} [inst : Mul S] {a x y : S}, SemiconjBy a x y → a * x = y 
* a
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equality behind `SemiconjBy a x y`; useful for rewriting.
-/
protected theorem eq [Mul S] {a x y : S} (h : SemiconjBy a x y) : a * x = y * a :=
  h

section Semigroup

variable [Semigroup S] {a b x y z x' y' : S}

/-- If `a` semiconjugates `x` to `y` and `x'` to `y'`,
then it semiconjugates `x * x'` to `y * y'`. -/
@[to_additive (attr := simp) /-- If `a` semiconjugates `x` to `y` and `x'` to `y'`,
then it semiconjugates `x + x'` to `y + y'`. -/]
/-
**SemiconjBy.mul_right** 是 Mathlib 中的一个定理，位于命名空间 `SemiconjBy`。
形式化陈述：mul_right (h : SemiconjBy a x y) (h' : SemiconjBy a x' y') : SemiconjBy a 
(x * x') (y * y')
参数：h : SemiconjBy a x y；h' : SemiconjBy a x' y'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `SemiconjBy.eq`：∀ {S : Type u_1} [inst : Mul S] {a x y : S}, SemiconjBy a
 x y → a * x = y * a
-/
theorem mul_right (h : SemiconjBy a x y) (h' : SemiconjBy a x' y') :
    SemiconjBy a (x * x') (y * y') := by
  unfold SemiconjBy
  -- TODO this could be done using `assoc_rw` if/when this is ported to mathlib4
  rw [← mul_assoc, h.eq, mul_assoc, h'.eq, ← mul_assoc]

/-- If `b` semiconjugates `x` to `y` and `a` semiconjugates `y` to `z`, then `a * b`
semiconjugates `x` to `z`. -/
@[to_additive /-- If `b` semiconjugates `x` to `y` and `a` semiconjugates `y` to `z`, then `a + b`
semiconjugates `x` to `z`. -/]
/-
**SemiconjBy.mul_left** 是 Mathlib 中的一个定理，位于命名空间 `SemiconjBy`。
形式化陈述：mul_left (ha : SemiconjBy a y z) (hb : SemiconjBy b x y) : SemiconjBy (a *
 b) x z
参数：ha : SemiconjBy a y z；hb : SemiconjBy b x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `SemiconjBy.eq`：∀ {S : Type u_1} [inst : Mul S] {a x y : S}, SemiconjBy a
 x y → a * x = y * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem mul_left (ha : SemiconjBy a y z) (hb : SemiconjBy b x y) : SemiconjBy (a * b) x z := by
  unfold SemiconjBy
  rw [mul_assoc, hb.eq, ← mul_assoc, ha.eq, mul_assoc]

/-- The relation “there exists an element that semiconjugates `a` to `b`” on a semigroup
is transitive. -/
@[to_additive /-- The relation “there exists an element that semiconjugates `a` to `b`” on an
additive semigroup is transitive. -/]
/-
**SemiconjBy.isTrans** 是 Mathlib 中的一个定理，位于命名空间 `SemiconjBy`。
形式化陈述：∀ {S : Type u_1} [inst : Semigroup S], IsTrans S fun a b => ∃ c, SemiconjB
y c a b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemiconjBy.mul_left`：mul_left (ha : SemiconjBy a y z) (hb : SemiconjBy b
 x y) : SemiconjBy (a * b) x z
-/
protected theorem isTrans : IsTrans S fun a b ↦ ∃ c, SemiconjBy c a b :=
  ⟨fun _ _ _ ⟨x, hx⟩ ⟨y, hy⟩ ↦ ⟨y * x, hy.mul_left hx⟩⟩

@[deprecated (since := "2026-02-20")]
protected alias _root_.AddSemiconjBy.transitive := AddSemiconjBy.isTrans
@[to_additive existing, deprecated (since := "2026-02-20")]
protected alias transitive := SemiconjBy.isTrans

end Semigroup

section MulOneClass

variable [MulOneClass M]

/-- Any element semiconjugates `1` to `1`. -/
@[to_additive (attr := simp) /-- Any element semiconjugates `0` to `0`. -/]
/-
**SemiconjBy.one_right** 是 Mathlib 中的一个定理，位于命名空间 `SemiconjBy`。
形式化陈述：one_right (a : M) : SemiconjBy a 1 1
参数：a : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SemiconjBy.eq_1`：∀ {M : Type u_2} [inst : Mul M] (a x y : M), SemiconjBy
 a x y = (a * x = y * a)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a

--- 原说明 ---
Any element semiconjugates `1` to `1`.
-/
theorem one_right (a : M) : SemiconjBy a 1 1 := by rw [SemiconjBy, mul_one, one_mul]

/-- One semiconjugates any element to itself. -/
@[to_additive (attr := simp) /-- Zero semiconjugates any element to itself. -/]
/-
**SemiconjBy.one_left** 是 Mathlib 中的一个定理，位于命名空间 `SemiconjBy`。
形式化陈述：one_left (x : M) : SemiconjBy 1 x x
参数：x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SemiconjBy.one_right`：one_right (a : M) : SemiconjBy a 1 1

--- 原说明 ---
One semiconjugates any element to itself.
-/
theorem one_left (x : M) : SemiconjBy 1 x x :=
  Eq.symm <| one_right x

/-- The relation “there exists an element that semiconjugates `a` to `b`” on a monoid (or, more
generally, on `MulOneClass` type) is reflexive. -/
@[to_additive /-- The relation “there exists an element that semiconjugates `a` to `b`” on an
additive monoid (or, more generally, on an `AddZeroClass` type) is reflexive. -/]
/-
**SemiconjBy.refl** 是 Mathlib 中的一个定理，位于命名空间 `SemiconjBy`。
形式化陈述：∀ {M : Type u_2} [inst : MulOneClass M], Std.Refl fun a b => ∃ c, Semiconj
By c a b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemiconjBy.one_left`：one_left (x : M) : SemiconjBy 1 x x
-/
protected theorem refl : Std.Refl fun a b : M ↦ ∃ c, SemiconjBy c a b where
  refl a := ⟨1, one_left a⟩

@[deprecated (since := "2026-03-27")] protected alias reflexive := SemiconjBy.refl

end MulOneClass

section Monoid

variable [Monoid M]

@[to_additive (attr := simp)]
/-
**SemiconjBy.pow_right** 是 Mathlib 中的一个定理，位于命名空间 `SemiconjBy`。
形式化陈述：pow_right {a x y : M} (h : SemiconjBy a x y) (n : Nat) : SemiconjBy a (x ^
 n) (y ^ n)
参数：h : SemiconjBy a x y；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `SemiconjBy.one_right`：one_right (a : M) : SemiconjBy a 1 1
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `SemiconjBy.mul_right`：mul_right (h : SemiconjBy a x y) (h' : SemiconjBy 
a x' y') : SemiconjBy a (x * x') (y * y')
-/
theorem pow_right {a x y : M} (h : SemiconjBy a x y) (n : ℕ) : SemiconjBy a (x ^ n) (y ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero]
    exact SemiconjBy.one_right _
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact ih.mul_right h

end Monoid

section Group

variable [Group G]

/-- `a` semiconjugates `x` to `a * x * a⁻¹`. -/
@[to_additive /-- `a` semiconjugates `x` to `a + x + -a`. -/]
/-
**SemiconjBy.conj_mk** 是 Mathlib 中的一个定理，位于命名空间 `SemiconjBy`。
形式化陈述：conj_mk (a x : G) : SemiconjBy a x (a * x * a⁻¹)
参数：a x : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a

--- 原说明 ---
`a` semiconjugates `x` to `a * x * a⁻¹`.
-/
theorem conj_mk (a x : G) : SemiconjBy a x (a * x * a⁻¹) := by
  unfold SemiconjBy; rw [mul_assoc, inv_mul_cancel, mul_one]

@[to_additive (attr := simp)]
/-
**SemiconjBy.conj_iff** 是 Mathlib 中的一个定理，位于命名空间 `SemiconjBy`。
形式化陈述：conj_iff {a x y b : G} : SemiconjBy (b * a * b⁻¹) (b * x * b⁻¹) (b * y * b
⁻¹) ↔ SemiconjBy a x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_left_cancel_iff`：mul_left_cancel_iff : a * b = a * c ↔ b = c
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_right_cancel_iff`：mul_right_cancel_iff : b * a = c * a ↔ b = c
· 使用定理 `RightCancelSemigroup.toIsRightCancelMul`：∀ {G : Type u} [self : RightCan
celSemigroup G], IsRightCancelMul G
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem conj_iff {a x y b : G} :
    SemiconjBy (b * a * b⁻¹) (b * x * b⁻¹) (b * y * b⁻¹) ↔ SemiconjBy a x y := by
  unfold SemiconjBy
  simp only [← mul_assoc, inv_mul_cancel_right]
  repeat rw [mul_assoc]
  rw [mul_left_cancel_iff, ← mul_assoc, ← mul_assoc, mul_right_cancel_iff]

end Group

end SemiconjBy

@[to_additive (attr := simp)]
/-
**semiconjBy_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：semiconjBy_iff_eq [CancelCommMonoid M] {a x y : M} : SemiconjBy a x y ↔ x 
= y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_left_cancel`：mul_left_cancel : a * b = a * c -> b = c
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SemiconjBy.eq_1`：∀ {M : Type u_2} [inst : Mul M] (a x y : M), SemiconjBy
 a x y = (a * x = y * a)
-/
theorem semiconjBy_iff_eq [CancelCommMonoid M] {a x y : M} : SemiconjBy a x y ↔ x = y :=
  ⟨fun h => mul_left_cancel (h.trans (mul_comm _ _)), fun h => by rw [h, SemiconjBy, mul_comm]⟩
