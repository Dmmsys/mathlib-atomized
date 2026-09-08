/-
Copyright (c) 2022 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
module

public import Mathlib.Algebra.GroupWithZero.Idempotent
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Order.Notation
public import Mathlib.Tactic.Convert
public import Mathlib.Algebra.Group.Torsion

/-!
# Idempotent elements of a ring

This file proves result about idempotent elements of a ring, like:
* `IsIdempotentElem.one_sub_iff`: In a (non-associative) ring, `a` is an idempotent if and only if
  `1 - a` is an idempotent.
-/

public section

variable {R : Type*}

namespace IsIdempotentElem
section NonAssocRing
variable [NonAssocRing R] {a : R}

/-
**IsIdempotentElem.one_sub** 是 Mathlib 中的一个引理，位于命名空间 `IsIdempotentElem`。
形式化陈述：one_sub (h : IsIdempotentElem a) : IsIdempotentElem (1 - a)
参数：h : IsIdempotentElem a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsIdempotentElem.eq_1`：∀ {M : Type u_1} [inst : Mul M] (a : M), IsIdempo
tentElem a = (a * a = a)
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `IsIdempotentElem.eq`：eq (ha : IsIdempotentElem a) : a * a = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
-/
lemma one_sub (h : IsIdempotentElem a) : IsIdempotentElem (1 - a) := by
  rw [IsIdempotentElem, mul_sub, mul_one, sub_mul, one_mul, h.eq, sub_self, sub_zero]

@[simp]
/-
**IsIdempotentElem.one_sub_iff** 是 Mathlib 中的一个引理，位于命名空间 `IsIdempotentElem`。
形式化陈述：one_sub_iff : IsIdempotentElem (1 - a) ↔ IsIdempotentElem a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsIdempotentElem.one_sub`：one_sub (h : IsIdempotentElem a) : IsIdempoten
tElem (1 - a)
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
-/
lemma one_sub_iff : IsIdempotentElem (1 - a) ↔ IsIdempotentElem a :=
  ⟨fun h => sub_sub_cancel 1 a ▸ h.one_sub, IsIdempotentElem.one_sub⟩

@[simp]
/-
**IsIdempotentElem.mul_one_sub_self** 是 Mathlib 中的一个引理，位于命名空间 `IsIdempotentElem`
。
形式化陈述：mul_one_sub_self (h : IsIdempotentElem a) : a * (1 - a) = 0
参数：h : IsIdempotentElem a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `IsIdempotentElem.eq`：eq (ha : IsIdempotentElem a) : a * a = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
-/
lemma mul_one_sub_self (h : IsIdempotentElem a) : a * (1 - a) = 0 := by
  rw [mul_sub, mul_one, h.eq, sub_self]

@[simp]
/-
**IsIdempotentElem.one_sub_mul_self** 是 Mathlib 中的一个引理，位于命名空间 `IsIdempotentElem`
。
形式化陈述：one_sub_mul_self (h : IsIdempotentElem a) : (1 - a) * a = 0
参数：h : IsIdempotentElem a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `IsIdempotentElem.eq`：eq (ha : IsIdempotentElem a) : a * a = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
-/
lemma one_sub_mul_self (h : IsIdempotentElem a) : (1 - a) * a = 0 := by
  rw [sub_mul, one_mul, h.eq, sub_self]
/-
**IsIdempotentElem._root_.isIdempotentElem_iff_mul_one_sub_self** 是 Mathlib 中的一个
引理，位于命名空间 `IsIdempotentElem`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.isIdempotentElem_iff_mul_one_sub_self :
    IsIdempotentElem a ↔ a * (1 - a) = 0 := by
  rw [mul_sub, mul_one, sub_eq_zero, eq_comm, IsIdempotentElem]
/-
**IsIdempotentElem._root_.isIdempotentElem_iff_one_sub_mul_self** 是 Mathlib 中的一个
引理，位于命名空间 `IsIdempotentElem`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.isIdempotentElem_iff_one_sub_mul_self :
    IsIdempotentElem a ↔ (1 - a) * a = 0 := by
  rw [sub_mul, one_mul, sub_eq_zero, eq_comm, IsIdempotentElem]
/-
**IsIdempotentElem.** 是 Mathlib 中的一个实例，位于命名空间 `IsIdempotentElem`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Compl {a : R // IsIdempotentElem a} where compl a := ⟨1 - a, a.prop.one_sub⟩
/-
**IsIdempotentElem.coe_compl** 是 Mathlib 中的一个定理，位于命名空间 `IsIdempotentElem`。
形式化陈述：∀ {R : Type u_1} [inst : NonAssocRing R] (a : { a // IsIdempotentElem a })
, ↑aᶜ = 1 - ↑a
参数：a : { a // IsIdempotentElem a }。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_compl (a : {a : R // IsIdempotentElem a}) : ↑aᶜ = (1 : R) - ↑a := rfl
/-
**IsIdempotentElem.compl_compl** 是 Mathlib 中的一个定理，位于命名空间 `IsIdempotentElem`。
形式化陈述：∀ {R : Type u_1} [inst : NonAssocRing R] (a : { a // IsIdempotentElem a })
, aᶜᶜ = a
参数：a : { a // IsIdempotentElem a }。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma compl_compl (a : {a : R // IsIdempotentElem a}) : aᶜᶜ = a := by ext; simp
/-
**IsIdempotentElem.zero_compl** 是 Mathlib 中的一个定理，位于命名空间 `IsIdempotentElem`。
形式化陈述：∀ {R : Type u_1} [inst : NonAssocRing R], 0ᶜ = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma zero_compl : (0 : {a : R // IsIdempotentElem a})ᶜ = 1 := by ext; simp
/-
**IsIdempotentElem.one_compl** 是 Mathlib 中的一个定理，位于命名空间 `IsIdempotentElem`。
形式化陈述：∀ {R : Type u_1} [inst : NonAssocRing R], 1ᶜ = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma one_compl : (1 : {a : R // IsIdempotentElem a})ᶜ = 0 := by ext; simp

end NonAssocRing

section Semiring
variable [Semiring R] {a b : R}

/-
**IsIdempotentElem.of_mul_add** 是 Mathlib 中的一个引理，位于命名空间 `IsIdempotentElem`。
形式化陈述：of_mul_add (mul : a * b = 0) (add : a + b = 1) : IsIdempotentElem a ∧ IsId
empotentElem b
参数：mul : a * b = 0；add : a + b = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
lemma of_mul_add (mul : a * b = 0) (add : a + b = 1) : IsIdempotentElem a ∧ IsIdempotentElem b := by
  simp_rw [IsIdempotentElem]; constructor
  · conv_rhs => rw [← mul_one a, ← add, mul_add, mul, add_zero]
  · conv_rhs => rw [← one_mul b, ← add, add_mul, mul, zero_add]

end Semiring

section NonUnitalRing
variable [NonUnitalRing R] {a b : R}

/-
**IsIdempotentElem.add_sub_mul_of_commute** 是 Mathlib 中的一个引理，位于命名空间 `IsIdempoten
tElem`。
形式化陈述：add_sub_mul_of_commute (h : Commute a b) (ha : IsIdempotentElem a) (hb : I
sIdempotentElem b) : IsIdempotentElem (a + b - a * b)
参数：h : Commute a b；ha : IsIdempotentElem a；hb : IsIdempotentElem b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `IsIdempotentElem.eq`：eq (ha : IsIdempotentElem a) : a * a = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用引理 `IsIdempotentElem.mul_self_mul`：mul_self_mul {M : Type*} [Semigroup M] {x
 : M} (hx : IsIdempotentElem x) (y : M) : x * (x * y) = x * y
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma add_sub_mul_of_commute (h : Commute a b) (ha : IsIdempotentElem a) (hb : IsIdempotentElem b) :
    IsIdempotentElem (a + b - a * b) := by
  simp only [IsIdempotentElem, h.eq, mul_sub, mul_add, sub_mul, add_mul, ha.eq,
    mul_assoc, add_sub_cancel_right, hb.eq, hb.mul_self_mul, add_sub_cancel_left, sub_right_inj]
  rw [← h.eq, ha.mul_self_mul, h.eq, hb.mul_self_mul, add_sub_cancel_right]

end NonUnitalRing

section CommRing
variable [CommRing R] {a b : R}

/-
**IsIdempotentElem.add_sub_mul** 是 Mathlib 中的一个引理，位于命名空间 `IsIdempotentElem`。
形式化陈述：add_sub_mul (hp : IsIdempotentElem a) (hq : IsIdempotentElem b) : IsIdempo
tentElem (a + b - a * b)
参数：hp : IsIdempotentElem a；hq : IsIdempotentElem b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsIdempotentElem.add_sub_mul_of_commute`：add_sub_mul_of_commute (h : Com
mute a b) (ha : IsIdempotentElem a) (hb : IsIdempotentElem b) : IsIdempotentElem
 (a + b - a * b)
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
-/
lemma add_sub_mul (hp : IsIdempotentElem a) (hq : IsIdempotentElem b) :
    IsIdempotentElem (a + b - a * b) := add_sub_mul_of_commute (.all ..) hp hq

end CommRing

/-- `a + b` is idempotent when `a` and `b` anti-commute. -/
/-
**IsIdempotentElem.add** 是 Mathlib 中的一个定理，位于命名空间 `IsIdempotentElem`。
形式化陈述：add [NonUnitalNonAssocSemiring R] {a b : R} (ha : IsIdempotentElem a) (hb 
: IsIdempotentElem b) (hab : a * b + b * a = 0) : IsIdempotentElem (a + b)
参数：ha : IsIdempotentElem a；hb : IsIdempotentElem b；hab : a * b + b * a = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用引理 `IsIdempotentElem.eq`：eq (ha : IsIdempotentElem a) : a * a = a
· 使用定理 `add_add_add_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c d 
: G), a + b + (c + d) = a + c + (b + d)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`a + b` is idempotent when `a` and `b` anti-commute.
-/
theorem add [NonUnitalNonAssocSemiring R]
    {a b : R} (ha : IsIdempotentElem a) (hb : IsIdempotentElem b)
    (hab : a * b + b * a = 0) : IsIdempotentElem (a + b) := by
  simp_rw [IsIdempotentElem, mul_add, add_mul, ha.eq, hb.eq, add_add_add_comm, ← add_assoc,
    add_assoc a, hab, zero_add]

/-- `a + b` is idempotent if and only if `a` and `b` anti-commute. -/
/-
**IsIdempotentElem.add_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsIdempotentElem`。
形式化陈述：add_iff [NonUnitalNonAssocSemiring R] [IsCancelAdd R] {a b : R} (ha : IsId
empotentElem a) (hb : IsIdempotentElem b) : IsIdempotentElem (a + b) ↔ a * b + b
 * a = 0
参数：ha : IsIdempotentElem a；hb : IsIdempotentElem b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_right_cancel_iff`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd 
G] {a b c : G}, b + a = c + a ↔ b = c
· 使用定理 `IsCancelAdd.toIsRightCancelAdd`：∀ {G : Type u} {inst : Add G} [self : Is
CancelAdd G], IsRightCancelAdd G
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_left_cancel_iff`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G]
 {a b c : G}, a + b = a + c ↔ b = c
· 使用定理 `IsCancelAdd.toIsLeftCancelAdd`：∀ {G : Type u} {inst : Add G} [self : IsC
ancelAdd G], IsLeftCancelAdd G
· 使用定理 `add_add_add_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c d 
: G), a + b + (c + d) = a + c + (b + d)
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用引理 `IsIdempotentElem.eq`：eq (ha : IsIdempotentElem a) : a * a = a
· 使用定理 `IsIdempotentElem.add`：add [NonUnitalNonAssocSemiring R] {a b : R} (ha : 
IsIdempotentElem a) (hb : IsIdempotentElem b) (hab : a * b + b * a = 0) : IsIdem
potentElem…

--- 原说明 ---
`a + b` is idempotent if and only if `a` and `b` anti-commute.
-/
theorem add_iff [NonUnitalNonAssocSemiring R] [IsCancelAdd R]
    {a b : R} (ha : IsIdempotentElem a) (hb : IsIdempotentElem b) :
    IsIdempotentElem (a + b) ↔ a * b + b * a = 0 := by
  refine ⟨fun h ↦ ?_, ha.add hb⟩
  rw [← add_right_cancel_iff (a := b), add_assoc, ← add_left_cancel_iff (a := a),
    ← add_assoc, add_add_add_comm]
  simpa [add_mul, mul_add, ha.eq, hb.eq] using h.eq

/-- `b - a` is idempotent when `a * b = a` and `b * a = a`. -/
/-
**IsIdempotentElem.sub** 是 Mathlib 中的一个引理，位于命名空间 `IsIdempotentElem`。
形式化陈述：sub [NonUnitalNonAssocRing R] {a b : R} (ha : IsIdempotentElem a) (hb : Is
IdempotentElem b) (hab : a * b = a) (hba : b * a = a) : IsIdempotentElem (b - a)
参数：ha : IsIdempotentElem a；hb : IsIdempotentElem b；hab : a * b = a；hba : b * a =
 a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用引理 `IsIdempotentElem.eq`：eq (ha : IsIdempotentElem a) : a * a = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`b - a` is idempotent when `a * b = a` and `b * a = a`.
-/
lemma sub [NonUnitalNonAssocRing R] {a b : R} (ha : IsIdempotentElem a)
    (hb : IsIdempotentElem b) (hab : a * b = a) (hba : b * a = a) : IsIdempotentElem (b - a) := by
  simp_rw [IsIdempotentElem, sub_mul, mul_sub, hab, hba, ha.eq, hb.eq, sub_self, sub_zero]

/-- If idempotent `a` and element `b` anti-commute, then their product is zero. -/
/-
**IsIdempotentElem.mul_eq_zero_of_anticommute** 是 Mathlib 中的一个定理，位于命名空间 `IsIdemp
otentElem`。
形式化陈述：mul_eq_zero_of_anticommute {a b : R} [NonUnitalSemiring R] [IsAddTorsionFr
ee R] (ha : IsIdempotentElem a) (hab : a * b + b * a = 0) : a * b = 0
参数：ha : IsIdempotentElem a；hab : a * b + b * a = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nsmul_right_inj`：∀ {M : Type u_1} [inst : AddMonoid M] [IsAddTorsionFree
 M] {n : ℕ} {a b : M}, n ≠ 0 → (n • a = n • b ↔ a = b)
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Nat.zero_ne_add_one`：∀ (n : ℕ), 0 ≠ n + 1
· 使用定理 `nsmul_zero`：∀ {M : Type u_2} [inst : AddMonoid M] (n : ℕ), n • 0 = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `IsIdempotentElem.eq`：eq (ha : IsIdempotentElem a) : a * a = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a

--- 原说明 ---
If idempotent `a` and element `b` anti-commute, then their product is zero.
-/
theorem mul_eq_zero_of_anticommute {a b : R} [NonUnitalSemiring R] [IsAddTorsionFree R]
    (ha : IsIdempotentElem a) (hab : a * b + b * a = 0) : a * b = 0 := by
  have h : a * b * a = 0 := by
    rw [← nsmul_right_inj ((Nat.zero_ne_add_one 1).symm), nsmul_zero]
    have : a * (a * b + b * a) * a = 0 := by rw [hab, mul_zero, zero_mul]
    simp_rw [mul_add, add_mul, mul_assoc, ha.eq, ← mul_assoc, ha.eq, ← two_nsmul] at this
    exact this
  suffices a * a * b + a * b * a = 0 by rwa [h, add_zero, ha.eq] at this
  rw [mul_assoc, mul_assoc, ← mul_add, hab, mul_zero]

/-- If idempotent `a` and element `b` anti-commute, then they commute.
So anti-commutativity implies commutativity when one of them is idempotent. -/
/-
**IsIdempotentElem.commute_of_anticommute** 是 Mathlib 中的一个引理，位于命名空间 `IsIdempoten
tElem`。
形式化陈述：commute_of_anticommute {a b : R} [NonUnitalSemiring R] [IsAddTorsionFree R
] (ha : IsIdempotentElem a) (hab : a * b + b * a = 0) : Commute a b
参数：ha : IsIdempotentElem a；hab : a * b + b * a = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIdempotentElem.mul_eq_zero_of_anticommute`：mul_eq_zero_of_anticommute 
{a b : R} [NonUnitalSemiring R] [IsAddTorsionFree R] (ha : IsIdempotentElem a) (
hab : a * b + b * a = 0) : a * b …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Commute.eq_1`：∀ {S : Type u_3} [inst : Mul S] (a b : S), Commute a b = S
emiconjBy a b b
· 使用定理 `SemiconjBy.eq_1`：∀ {M : Type u_2} [inst : Mul M] (a x y : M), SemiconjBy
 a x y = (a * x = y * a)
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a

--- 原说明 ---
If idempotent `a` and element `b` anti-commute, then they commute.
So anti-commutativity implies commutativity when one of them is idempotent.
-/
lemma commute_of_anticommute {a b : R} [NonUnitalSemiring R] [IsAddTorsionFree R]
    (ha : IsIdempotentElem a) (hab : a * b + b * a = 0) : Commute a b := by
  have := mul_eq_zero_of_anticommute ha hab
  rw [this, zero_add] at hab
  rw [Commute, SemiconjBy, hab, this]
/-
**IsIdempotentElem.sub_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsIdempotentElem`。
形式化陈述：sub_iff [NonUnitalRing R] [IsAddTorsionFree R] {p q : R} (hp : IsIdempoten
tElem p) (hq : IsIdempotentElem q) : IsIdempotentElem (q - p) ↔ p * q = p ∧ q * 
p = p
参数：hp : IsIdempotentElem p；hq : IsIdempotentElem q。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsIdempotentElem.add_iff`：add_iff [NonUnitalNonAssocSemiring R] [IsCance
lAdd R] {a b : R} (ha : IsIdempotentElem a) (hb : IsIdempotentElem b) : IsIdempo
tentElem (a + …
· 使用定理 `AddCancelMonoid.toIsCancelAdd`：∀ (M : Type u) [inst : AddCancelMonoid M]
, IsCancelAdd M
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_sub`：∀ {G : Type u_3} [inst : SubNegMonoid G] (a b c : G), a + (b - 
c) = a + b - c
· 使用引理 `IsIdempotentElem.eq`：eq (ha : IsIdempotentElem a) : a * a = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `nsmul_right_inj`：∀ {M : Type u_1} [inst : AddMonoid M] [IsAddTorsionFree
 M] {n : ℕ} {a b : M}, n ≠ 0 → (n • a = n • b ↔ a = b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
（共 37 条，此处仅展示前 30 条）
-/
theorem sub_iff [NonUnitalRing R] [IsAddTorsionFree R] {p q : R}
    (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) :
    IsIdempotentElem (q - p) ↔ p * q = p ∧ q * p = p := by
  refine ⟨fun hqp ↦ ?_, fun ⟨h1, h2⟩ => hp.sub hq h1 h2⟩
  have h : p * (q - p) + (q - p) * p = 0 := hp.add_iff hqp |>.mp ((add_sub_cancel p q).symm ▸ hq)
  have hpq : Commute p q := by
    simp_rw [IsIdempotentElem, mul_sub, sub_mul,
    hp.eq, hq.eq, ← sub_add_eq_sub_sub, sub_right_inj, add_sub] at hqp
    have h1 := congr_arg (q * ·) hqp
    have h2 := congr_arg (· * q) hqp
    simp_rw [mul_sub, mul_add, ← mul_assoc, hq.eq, add_sub_cancel_right] at h1
    simp_rw [sub_mul, add_mul, mul_assoc, hq.eq, add_sub_cancel_left, ← mul_assoc] at h2
    exact h2.symm.trans h1
  rw [hpq.eq, and_self, ← nsmul_right_inj (by simp : 2 ≠ 0), ← zero_add (2 • p)]
  convert congrArg (· + 2 • p) h
  simp [sub_mul, mul_sub, hp.eq, hpq.eq, two_nsmul, sub_add, sub_sub]

end IsIdempotentElem

