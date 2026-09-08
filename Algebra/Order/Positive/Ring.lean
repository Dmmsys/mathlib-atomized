/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.InjSurj
public import Mathlib.Tactic.FastInstance

/-!
# Algebraic structures on the set of positive numbers

In this file we define various instances (`AddSemigroup`, `IsOrderedMonoid` etc) on the
type `{x : R // 0 < x}`. In each case we try to require the weakest possible typeclass
assumptions on `R` but possibly, there is a room for improvements.
-/

public section


open Function

namespace Positive

variable {M R : Type*}

section AddBasic

variable [AddMonoid M] [Preorder M] [AddLeftStrictMono M]

/-
**Positive.** 是 Mathlib 中的一个实例，位于命名空间 `Positive`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add { x : M // 0 < x } :=
  ⟨fun x y => ⟨x + y, add_pos x.2 y.2⟩⟩

@[simp, norm_cast]
/-
**Positive.coe_add** 是 Mathlib 中的一个定理，位于命名空间 `Positive`。
形式化陈述：coe_add (x y : { x : M // 0 < x }) : ↑(x + y) = (x + y : M)
参数：x y : { x : M // 0 < x }。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_add (x y : { x : M // 0 < x }) : ↑(x + y) = (x + y : M) :=
  rfl
/-
**Positive.addSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `Positive`。
形式化陈述：addSemigroup : AddSemigroup { x : M // 0 < x }
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addSemigroup : AddSemigroup { x : M // 0 < x } := fast_instance%
  Subtype.coe_injective.addSemigroup _ coe_add
/-
**Positive.addCommSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `Positive`。
形式化陈述：addCommSemigroup {M : Type*} [AddCommMonoid M] [Preorder M] [AddLeftStrict
Mono M] : AddCommSemigroup { x : M // 0 < x }
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addCommSemigroup {M : Type*} [AddCommMonoid M] [Preorder M]
    [AddLeftStrictMono M] : AddCommSemigroup { x : M // 0 < x } := fast_instance%
  Subtype.coe_injective.addCommSemigroup _ coe_add
/-
**Positive.addLeftCancelSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `Positive`。
形式化陈述：addLeftCancelSemigroup {M : Type*} [AddLeftCancelMonoid M] [Preorder M] [A
ddLeftStrictMono M] : AddLeftCancelSemigroup { x : M // 0 < x }
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addLeftCancelSemigroup {M : Type*} [AddLeftCancelMonoid M] [Preorder M]
    [AddLeftStrictMono M] : AddLeftCancelSemigroup { x : M // 0 < x } := fast_instance%
  Subtype.coe_injective.addLeftCancelSemigroup _ coe_add
/-
**Positive.addRightCancelSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `Positive`。
形式化陈述：addRightCancelSemigroup {M : Type*} [AddRightCancelMonoid M] [Preorder M] 
[AddLeftStrictMono M] : AddRightCancelSemigroup { x : M // 0 < x }
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addRightCancelSemigroup {M : Type*} [AddRightCancelMonoid M] [Preorder M]
    [AddLeftStrictMono M] : AddRightCancelSemigroup { x : M // 0 < x } := fast_instance%
  Subtype.coe_injective.addRightCancelSemigroup _ coe_add
/-
**Positive.addLeftStrictMono** 是 Mathlib 中的一个实例，位于命名空间 `Positive`。
形式化陈述：addLeftStrictMono : AddLeftStrictMono { x : M // 0 < x }
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.coe_lt_coe`：coe_lt_coe [LT α] {p : α -> Prop} {x y : Subtype p} 
: (x : α) < y ↔ x < y
· 使用定理 `add_lt_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [AddLe
ftStrictMono α] {b c : α}, b < c → ∀ (a : α), a + b < a + c
-/
instance addLeftStrictMono : AddLeftStrictMono { x : M // 0 < x } :=
  ⟨fun _ y z hyz => Subtype.coe_lt_coe.1 <| add_lt_add_right (show (y : M) < z from hyz) _⟩
/-
**Positive.addRightStrictMono** 是 Mathlib 中的一个实例，位于命名空间 `Positive`。
形式化陈述：addRightStrictMono [AddRightStrictMono M] : AddRightStrictMono { x : M // 
0 < x }
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.coe_lt_coe`：coe_lt_coe [LT α] {p : α -> Prop} {x y : Subtype p} 
: (x : α) < y ↔ x < y
· 使用定理 `add_lt_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [i : Ad
dRightStrictMono α] {b c : α}, b < c → ∀ (a : α), b + a < c + a
-/
instance addRightStrictMono [AddRightStrictMono M] : AddRightStrictMono { x : M // 0 < x } :=
  ⟨fun _ y z hyz => Subtype.coe_lt_coe.1 <| add_lt_add_left (show (y : M) < z from hyz) _⟩
/-
**Positive.addLeftReflectLT** 是 Mathlib 中的一个实例，位于命名空间 `Positive`。
形式化陈述：addLeftReflectLT [AddLeftReflectLT M] : AddLeftReflectLT { x : M // 0 < x 
}
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.coe_lt_coe`：coe_lt_coe [LT α] {p : α -> Prop} {x y : Subtype p} 
: (x : α) < y ↔ x < y
· 使用定理 `lt_of_add_lt_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [
AddLeftReflectLT α] {a b c : α}, a + b < a + c → b < c
-/
instance addLeftReflectLT [AddLeftReflectLT M] : AddLeftReflectLT { x : M // 0 < x } :=
  ⟨fun _ _ _ h => Subtype.coe_lt_coe.1 <| lt_of_add_lt_add_left h⟩
/-
**Positive.addRightReflectLT** 是 Mathlib 中的一个实例，位于命名空间 `Positive`。
形式化陈述：addRightReflectLT [AddRightReflectLT M] : AddRightReflectLT { x : M // 0 <
 x }
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.coe_lt_coe`：coe_lt_coe [LT α] {p : α -> Prop} {x y : Subtype p} 
: (x : α) < y ↔ x < y
· 使用定理 `lt_of_add_lt_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] 
[i : AddRightReflectLT α] {a b c : α}, b + a < c + a → b < c
-/
instance addRightReflectLT [AddRightReflectLT M] : AddRightReflectLT { x : M // 0 < x } :=
  ⟨fun _ _ _ h => Subtype.coe_lt_coe.1 <| lt_of_add_lt_add_right h⟩
/-
**Positive.addLeftReflectLE** 是 Mathlib 中的一个实例，位于命名空间 `Positive`。
形式化陈述：addLeftReflectLE [AddLeftReflectLE M] : AddLeftReflectLE { x : M // 0 < x 
} where le_of_add_le_add_left h
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.coe_le_coe`：coe_le_coe [LE α] {p : α -> Prop} {x y : Subtype p} 
: (x : α) <= y ↔ x <= y
· 使用定理 `le_of_add_le_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [
AddLeftReflectLE α] {a b c : α}, a + b ≤ a + c → b ≤ c
-/
instance addLeftReflectLE [AddLeftReflectLE M] : AddLeftReflectLE { x : M // 0 < x } where
  le_of_add_le_add_left h := Subtype.coe_le_coe.mp <| le_of_add_le_add_left h
/-
**Positive.addRightReflectLE** 是 Mathlib 中的一个实例，位于命名空间 `Positive`。
形式化陈述：addRightReflectLE [AddRightReflectLE M] : AddRightReflectLE { x : M // 0 <
 x } where le_of_add_le_add_right h
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.coe_le_coe`：coe_le_coe [LE α] {p : α -> Prop} {x y : Subtype p} 
: (x : α) <= y ↔ x <= y
· 使用定理 `le_of_add_le_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] 
[AddRightReflectLE α] {a b c : α}, b + a ≤ c + a → b ≤ c
-/
instance addRightReflectLE [AddRightReflectLE M] : AddRightReflectLE { x : M // 0 < x } where
  le_of_add_le_add_right h := Subtype.coe_le_coe.mp <| le_of_add_le_add_right h

end AddBasic

/-
**Positive.addLeftMono** 是 Mathlib 中的一个实例，位于命名空间 `Positive`。
形式化陈述：addLeftMono [AddMonoid M] [PartialOrder M] [AddLeftStrictMono M] : AddLeft
Mono { x : M // 0 < x }
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `add_lt_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [AddLe
ftStrictMono α] {b c : α}, b < c → ∀ (a : α), a + b < a + c
-/
instance addLeftMono [AddMonoid M] [PartialOrder M] [AddLeftStrictMono M] :
    AddLeftMono { x : M // 0 < x } :=
  ⟨@fun _ _ _ h₁ => StrictMono.monotone (fun _ _ h => add_lt_add_right h _) h₁⟩

section Mul

variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]

/-
**Positive.** 是 Mathlib 中的一个实例，位于命名空间 `Positive`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mul { x : R // 0 < x } :=
  ⟨fun x y => ⟨x * y, mul_pos x.2 y.2⟩⟩

@[simp]
/-
**Positive.val_mul** 是 Mathlib 中的一个定理，位于命名空间 `Positive`。
形式化陈述：val_mul (x y : { x : R // 0 < x }) : ↑(x * y) = (x * y : R)
参数：x y : { x : R // 0 < x }。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem val_mul (x y : { x : R // 0 < x }) : ↑(x * y) = (x * y : R) :=
  rfl
/-
**Positive.** 是 Mathlib 中的一个实例，位于命名空间 `Positive`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Pow { x : R // 0 < x } ℕ :=
  ⟨fun x n => ⟨(x : R) ^ n, pow_pos x.2 n⟩⟩

@[simp]
/-
**Positive.val_pow** 是 Mathlib 中的一个定理，位于命名空间 `Positive`。
形式化陈述：val_pow (x : { x : R // 0 < x }) (n : Nat) : ↑(x ^ n) = (x : R) ^ n
参数：x : { x : R // 0 < x }；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem val_pow (x : { x : R // 0 < x }) (n : ℕ) :
    ↑(x ^ n) = (x : R) ^ n :=
  rfl
/-
**Positive.** 是 Mathlib 中的一个实例，位于命名空间 `Positive`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Semigroup { x : R // 0 < x } := fast_instance%
  Subtype.coe_injective.semigroup Subtype.val val_mul
/-
**Positive.** 是 Mathlib 中的一个实例，位于命名空间 `Positive`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Distrib { x : R // 0 < x } := fast_instance%
  Subtype.coe_injective.distrib _ coe_add val_mul
/-
**Positive.** 是 Mathlib 中的一个实例，位于命名空间 `Positive`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One { x : R // 0 < x } :=
  ⟨⟨1, one_pos⟩⟩

@[simp]
/-
**Positive.val_one** 是 Mathlib 中的一个定理，位于命名空间 `Positive`。
形式化陈述：val_one : ((1 : { x : R // 0 < x }) : R) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem val_one : ((1 : { x : R // 0 < x }) : R) = 1 :=
  rfl
/-
**Positive.** 是 Mathlib 中的一个实例，位于命名空间 `Positive`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Monoid { x : R // 0 < x } := fast_instance%
  Subtype.coe_injective.monoid _ val_one val_mul val_pow

end Mul

section mul_comm

/-
**Positive.commMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Positive`。
形式化陈述：commMonoid [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R] : Com
mMonoid { x : R // 0 < x }
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance commMonoid [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R] :
    CommMonoid { x : R // 0 < x } := fast_instance%
  Subtype.coe_injective.commMonoid (M₂ := R) (Subtype.val) val_one val_mul val_pow
/-
**Positive.isOrderedMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Positive`。
形式化陈述：isOrderedMonoid [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R] 
: IsOrderedMonoid { x : R // 0 < x } where mul_le_mul_left _ _ hxy c
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.coe_le_coe`：coe_le_coe [LE α] {p : α -> Prop} {x y : Subtype p} 
: (x : α) <= y ↔ x <= y
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
instance isOrderedMonoid [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R] :
    IsOrderedMonoid { x : R // 0 < x } where
  mul_le_mul_left _ _ hxy c := Subtype.coe_le_coe.1 <| mul_le_mul_of_nonneg_right hxy c.2.le

/-- If `R` is a nontrivial linear ordered commutative semiring, then `{x : R // 0 < x}` is a linear
ordered cancellative commutative monoid. -/
/-
**Positive.isOrderedCancelMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Positive`。
形式化陈述：isOrderedCancelMonoid [CommSemiring R] [LinearOrder R] [IsStrictOrderedRin
g R] : IsOrderedCancelMonoid { x : R // 0 < x } where le_of_mul_le_mul_left a _ 
_
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_le_mul_iff_right₀`：mul_le_mul_iff_right₀ [PosMulMono α] [PosMulRefle
ctLE α] (a0 : 0 < a) : a * b <= a * c ↔ b <= c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
If `R` is a nontrivial linear ordered commutative semiring, then `{x : R // 0 < 
x}` is a linear
ordered cancellative commutative monoid.
-/
instance isOrderedCancelMonoid [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R] :
    IsOrderedCancelMonoid { x : R // 0 < x } where
  le_of_mul_le_mul_left a _ _ := (mul_le_mul_iff_right₀ a.2).1

end mul_comm

end Positive

