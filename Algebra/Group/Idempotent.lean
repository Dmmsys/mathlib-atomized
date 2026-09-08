/-
Copyright (c) 2022 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Commute.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Data.Subtype
public import Mathlib.Tactic.Conv

/-!
# Idempotents

This file defines idempotents for an arbitrary multiplication and proves some basic results,
including:

* `IsIdempotentElem.mul_of_commute`: In a semigroup, the product of two commuting idempotents is
  an idempotent;
* `IsIdempotentElem.pow_succ_eq`: In a monoid `a ^ (n+1) = a` for `a` an idempotent and `n` a
  natural number.

## Tags

projection, idempotent
-/

@[expose] public section

assert_not_exists GroupWithZero

variable {M N S : Type*}

/-- An element `a` is said to be idempotent if `a * a = a`. -/
/-
**IsIdempotentElem** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsIdempotentElem [Mul M] (a : M) : Prop
参数：a : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An element `a` is said to be idempotent if `a * a = a`.
-/
def IsIdempotentElem [Mul M] (a : M) : Prop := a * a = a
/-
**isIdempotentElem_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isIdempotentElem_iff [Mul M] {a : M} : IsIdempotentElem a ↔ a * a = a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isIdempotentElem_iff [Mul M] {a : M} : IsIdempotentElem a ↔ a * a = a := Iff.rfl

namespace IsIdempotentElem
section Mul
variable [Mul M] {a : M}

/-
**IsIdempotentElem.of_isIdempotent** 是 Mathlib 中的一个引理，位于命名空间 `IsIdempotentElem`。
形式化陈述：of_isIdempotent [Std.IdempotentOp (α
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Std.IdempotentOp.idempotent`：∀ {α : Sort u} {op : α → α → α} [self : Std
.IdempotentOp op] (x : α), op x x = x
-/
lemma of_isIdempotent [Std.IdempotentOp (α := M) (· * ·)] (a : M) : IsIdempotentElem a :=
  Std.IdempotentOp.idempotent a
/-
**IsIdempotentElem.eq** 是 Mathlib 中的一个引理，位于命名空间 `IsIdempotentElem`。
形式化陈述：eq (ha : IsIdempotentElem a) : a * a = a
参数：ha : IsIdempotentElem a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma eq (ha : IsIdempotentElem a) : a * a = a := ha

end Mul

section Semigroup
variable [Semigroup S] {a b : S}

/-
**IsIdempotentElem.mul_of_commute** 是 Mathlib 中的一个引理，位于命名空间 `IsIdempotentElem`。
形式化陈述：mul_of_commute (hab : Commute a b) (ha : IsIdempotentElem a) (hb : IsIdemp
otentElem b) : IsIdempotentElem (a * b)
参数：hab : Commute a b；ha : IsIdempotentElem a；hb : IsIdempotentElem b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsIdempotentElem.eq_1`：∀ {M : Type u_1} [inst : Mul M] (a : M), IsIdempo
tentElem a = (a * a = a)
· 使用定理 `Commute.mul_mul_mul_comm`：∀ {S : Type u_3} [inst : Semigroup S] {b c : S
}, Commute b c → ∀ (a d : S), a * b * (c * d) = a * c * (b * d)
· 使用定理 `Commute.symm`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → C
ommute b a
· 使用引理 `IsIdempotentElem.eq`：eq (ha : IsIdempotentElem a) : a * a = a
-/
lemma mul_of_commute (hab : Commute a b) (ha : IsIdempotentElem a) (hb : IsIdempotentElem b) :
    IsIdempotentElem (a * b) := by rw [IsIdempotentElem, hab.symm.mul_mul_mul_comm, ha.eq, hb.eq]

end Semigroup

section CommSemigroup
variable [CommSemigroup S] {a b : S}

/-
**IsIdempotentElem.mul** 是 Mathlib 中的一个引理，位于命名空间 `IsIdempotentElem`。
形式化陈述：mul (ha : IsIdempotentElem a) (hb : IsIdempotentElem b) : IsIdempotentElem
 (a * b)
参数：ha : IsIdempotentElem a；hb : IsIdempotentElem b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsIdempotentElem.mul_of_commute`：mul_of_commute (hab : Commute a b) (ha 
: IsIdempotentElem a) (hb : IsIdempotentElem b) : IsIdempotentElem (a * b)
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
-/
lemma mul (ha : IsIdempotentElem a) (hb : IsIdempotentElem b) : IsIdempotentElem (a * b) :=
  ha.mul_of_commute (.all ..) hb

end CommSemigroup

section MulOneClass
variable [MulOneClass M] {a : M}

/-
**IsIdempotentElem.one** 是 Mathlib 中的一个引理，位于命名空间 `IsIdempotentElem`。
形式化陈述：one : IsIdempotentElem (1 : M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
lemma one : IsIdempotentElem (1 : M) := mul_one _
/-
**IsIdempotentElem.** 是 Mathlib 中的一个实例，位于命名空间 `IsIdempotentElem`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One {a : M // IsIdempotentElem a} where one := ⟨1, one⟩
/-
**IsIdempotentElem.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `IsIdempotentElem`。
形式化陈述：∀ {M : Type u_1} [inst : MulOneClass M], ↑1 = 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_one : ↑(1 : {a : M // IsIdempotentElem a}) = (1 : M) := rfl

end MulOneClass

section Monoid
variable [Monoid M] {a : M}

/-
**IsIdempotentElem.pow** 是 Mathlib 中的一个引理，位于命名空间 `IsIdempotentElem`。
形式化陈述：pow (n : Nat) (h : IsIdempotentElem a) : IsIdempotentElem (a ^ n)
参数：n : Nat；h : IsIdempotentElem a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsIdempotentElem.one`：one : IsIdempotentElem (1 : M)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IsIdempotentElem.eq`：eq (ha : IsIdempotentElem a) : a * a = a
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用引理 `pow_mul'`：pow_mul' (a : M) (m n : Nat) : a ^ (m * n) = (a ^ n) ^ m
-/
lemma pow (n : ℕ) (h : IsIdempotentElem a) : IsIdempotentElem (a ^ n) :=
  Nat.recOn n ((pow_zero a).symm ▸ one) fun n _ =>
    show a ^ n.succ * a ^ n.succ = a ^ n.succ by
      conv_rhs => rw [← h.eq]
      rw [← sq, ← sq, ← pow_mul, ← pow_mul']
/-
**IsIdempotentElem.pow_succ_eq** 是 Mathlib 中的一个引理，位于命名空间 `IsIdempotentElem`。
形式化陈述：pow_succ_eq (n : Nat) (h : IsIdempotentElem a) : a ^ (n + 1) = a
参数：n : Nat；h : IsIdempotentElem a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用引理 `IsIdempotentElem.eq`：eq (ha : IsIdempotentElem a) : a * a = a
-/
lemma pow_succ_eq (n : ℕ) (h : IsIdempotentElem a) : a ^ (n + 1) = a :=
  Nat.recOn n ((Nat.zero_add 1).symm ▸ pow_one a) fun n ih => by rw [pow_succ, ih, h.eq]
/-
**IsIdempotentElem.pow_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsIdempotentElem`。
形式化陈述：pow_eq (h : IsIdempotentElem a) {n : Nat} (hn : n != 0) : a ^ n = a
参数：h : IsIdempotentElem a；hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.exists_eq_add_one_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → ∃ k, n = k + 1
· 使用引理 `IsIdempotentElem.pow_succ_eq`：pow_succ_eq (n : Nat) (h : IsIdempotentEle
m a) : a ^ (n + 1) = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem pow_eq (h : IsIdempotentElem a) {n : ℕ} (hn : n ≠ 0) : a ^ n = a := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn
  exact h.pow_succ_eq _
/-
**IsIdempotentElem.iff_eq_one_of_isUnit** 是 Mathlib 中的一个定理，位于命名空间 `IsIdempotentE
lem`。
形式化陈述：iff_eq_one_of_isUnit (h : IsUnit a) : IsIdempotentElem a ↔ a = 1 where mp 
idem
参数：h : IsUnit a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsUnit.exists_left_inv`：IsUnit.exists_left_inv {a : M} (h : IsUnit a) : 
exists b, b * a = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `IsIdempotentElem.eq`：eq (ha : IsIdempotentElem a) : a * a = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `IsIdempotentElem.one`：one : IsIdempotentElem (1 : M)
-/
theorem iff_eq_one_of_isUnit (h : IsUnit a) : IsIdempotentElem a ↔ a = 1 where
  mp idem := by
    have ⟨q, eq⟩ := h.exists_left_inv
    rw [← eq, ← idem.eq, ← mul_assoc, eq, one_mul, idem.eq]
  mpr := by rintro rfl; exact .one

end Monoid

section CancelMonoid
variable [CancelMonoid M] {a : M}

/-
**IsIdempotentElem.iff_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `IsIdempotentElem`。
形式化陈述：∀ {M : Type u_1} [inst : CancelMonoid M] {a : M}, IsIdempotentElem a ↔ a =
 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma iff_eq_one : IsIdempotentElem a ↔ a = 1 := by simp [IsIdempotentElem]

end CancelMonoid

/-
**IsIdempotentElem.map** 是 Mathlib 中的一个引理，位于命名空间 `IsIdempotentElem`。
形式化陈述：map {M N F} [Mul M] [Mul N] [FunLike F M N] [MulHomClass F M N] {e : M} (h
e : IsIdempotentElem e) (f : F) : IsIdempotentElem (f e)
参数：he : IsIdempotentElem e；f : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsIdempotentElem.eq_1`：∀ {M : Type u_1} [inst : Mul M] (a : M), IsIdempo
tentElem a = (a * a = a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用引理 `IsIdempotentElem.eq`：eq (ha : IsIdempotentElem a) : a * a = a
-/
lemma map {M N F} [Mul M] [Mul N] [FunLike F M N] [MulHomClass F M N] {e : M}
    (he : IsIdempotentElem e) (f : F) : IsIdempotentElem (f e) := by
  rw [IsIdempotentElem, ← map_mul, he.eq]
/-
**IsIdempotentElem.mul_mul_self** 是 Mathlib 中的一个引理，位于命名空间 `IsIdempotentElem`。
形式化陈述：mul_mul_self {M : Type*} [Semigroup M] {x : M} (hx : IsIdempotentElem x) (
y : M) : y * x * x = y * x
参数：hx : IsIdempotentElem x；y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IsIdempotentElem.eq`：eq (ha : IsIdempotentElem a) : a * a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
lemma mul_mul_self {M : Type*} [Semigroup M] {x : M}
    (hx : IsIdempotentElem x) (y : M) : y * x * x = y * x :=
  mul_assoc y x x ▸ congrArg (y * ·) hx.eq
/-
**IsIdempotentElem.mul_self_mul** 是 Mathlib 中的一个引理，位于命名空间 `IsIdempotentElem`。
形式化陈述：mul_self_mul {M : Type*} [Semigroup M] {x : M} (hx : IsIdempotentElem x) (
y : M) : x * (x * y) = x * y
参数：hx : IsIdempotentElem x；y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IsIdempotentElem.eq`：eq (ha : IsIdempotentElem a) : a * a = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
lemma mul_self_mul {M : Type*} [Semigroup M] {x : M}
    (hx : IsIdempotentElem x) (y : M) : x * (x * y) = x * y :=
  mul_assoc x x y ▸ congrArg (· * y) hx.eq

end IsIdempotentElem

