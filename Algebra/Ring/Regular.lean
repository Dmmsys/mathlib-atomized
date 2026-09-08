/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Yury Kudryashov, Neil Strickland
-/
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.GroupWithZero.Regular
public import Mathlib.Algebra.Ring.Defs

/-!
# Lemmas about regular elements in rings.
-/

public section


variable {α : Type*}

/-- Left `Mul` by a `k : α` over `[Ring α]` is injective, if `k` is not a zero divisor.
The typeclass that restricts all terms of `α` to have this property is `NoZeroDivisors`. -/
/-
**isLeftRegular_of_non_zero_divisor** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLeftRegular_of_non_zero_divisor [NonUnitalNonAssocRing α] (k : α) (h : f
orall x : α, k * x = 0 -> x = 0) : IsLeftRegular k
参数：k : α；h : forall x : α, k * x = 0 -> x = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c

--- 原说明 ---
Left `Mul` by a `k : α` over `[Ring α]` is injective, if `k` is not a zero divis
or.
The typeclass that restricts all terms of `α` to have this property is `NoZeroDi
visors`.
-/
theorem isLeftRegular_of_non_zero_divisor [NonUnitalNonAssocRing α] (k : α)
    (h : ∀ x : α, k * x = 0 → x = 0) : IsLeftRegular k := by
  refine fun x y (h' : k * x = k * y) => sub_eq_zero.mp (h _ ?_)
  rw [mul_sub, sub_eq_zero, h']

/-- Right `Mul` by a `k : α` over `[Ring α]` is injective, if `k` is not a zero divisor.
The typeclass that restricts all terms of `α` to have this property is `NoZeroDivisors`. -/
/-
**isRightRegular_of_non_zero_divisor** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isRightRegular_of_non_zero_divisor [NonUnitalNonAssocRing α] (k : α) (h : 
forall x : α, x * k = 0 -> x = 0) : IsRightRegular k
参数：k : α；h : forall x : α, x * k = 0 -> x = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c

--- 原说明 ---
Right `Mul` by a `k : α` over `[Ring α]` is injective, if `k` is not a zero divi
sor.
The typeclass that restricts all terms of `α` to have this property is `NoZeroDi
visors`.
-/
theorem isRightRegular_of_non_zero_divisor [NonUnitalNonAssocRing α] (k : α)
    (h : ∀ x : α, x * k = 0 → x = 0) : IsRightRegular k := by
  refine fun x y (h' : x * k = y * k) => sub_eq_zero.mp (h _ ?_)
  rw [sub_mul, sub_eq_zero, h']
/-
**IsRegular.of_ne_zero'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsRegular.of_ne_zero' [NonUnitalNonAssocRing α] [NoZeroDivisors α] {k : α}
 (hk : k != 0) : IsRegular k
参数：hk : k != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isLeftRegular_of_non_zero_divisor`：isLeftRegular_of_non_zero_divisor [No
nUnitalNonAssocRing α] (k : α) (h : forall x : α, k * x = 0 -> x = 0) : IsLeftRe
gular k
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero`：∀ {M₀ : Type u_2} {ins
t : Mul M₀} {inst_1 : Zero M₀} [self : NoZeroDivisors M₀] {a b : M₀}, a * b = 0 
→ a = 0 ∨ b = 0
· 使用定理 `isRightRegular_of_non_zero_divisor`：isRightRegular_of_non_zero_divisor [
NonUnitalNonAssocRing α] (k : α) (h : forall x : α, x * k = 0 -> x = 0) : IsRigh
tRegular k
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
-/
theorem IsRegular.of_ne_zero' [NonUnitalNonAssocRing α] [NoZeroDivisors α] {k : α} (hk : k ≠ 0) :
    IsRegular k :=
  ⟨isLeftRegular_of_non_zero_divisor k fun _ h =>
      (NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero h).resolve_left hk,
    isRightRegular_of_non_zero_divisor k fun _ h =>
      (NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero h).resolve_right hk⟩

@[deprecated (since := "2026-01-21")] alias isRegular_of_ne_zero' := IsRegular.of_ne_zero'
/-
**isRegular_iff_ne_zero'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isRegular_iff_ne_zero' [Nontrivial α] [NonUnitalNonAssocRing α] [NoZeroDiv
isors α] {k : α} : IsRegular k ↔ k != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `IsRegular.left`：∀ {R : Type u_1} [inst : Mul R] {c : R}, IsRegular c → I
sLeftRegular c
· 使用定理 `not_isLeftRegular_zero`：not_isLeftRegular_zero [nR : Nontrivial R] : ¬Is
LeftRegular (0 : R)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsRegular.of_ne_zero'`：IsRegular.of_ne_zero' [NonUnitalNonAssocRing α] [
NoZeroDivisors α] {k : α} (hk : k != 0) : IsRegular k
-/
theorem isRegular_iff_ne_zero' [Nontrivial α] [NonUnitalNonAssocRing α] [NoZeroDivisors α]
    {k : α} : IsRegular k ↔ k ≠ 0 :=
  ⟨fun h => by
    rintro rfl
    exact not_not.mpr h.left not_isLeftRegular_zero, .of_ne_zero'⟩

/-- A ring with no zero divisors is a cancellative `MonoidWithZero`.

Note this is not an instance as it forms a typeclass loop. -/
/-
**NoZeroDivisors.toIsCancelMulZero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：NoZeroDivisors.toIsCancelMulZero [NonUnitalNonAssocRing α] [NoZeroDivisors
 α] : IsCancelMulZero α where mul_left_cancel_of_ne_zero ha
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRegular.left`：∀ {R : Type u_1} [inst : Mul R] {c : R}, IsRegular c → I
sLeftRegular c
· 使用定理 `IsRegular.of_ne_zero'`：IsRegular.of_ne_zero' [NonUnitalNonAssocRing α] [
NoZeroDivisors α] {k : α} (hk : k != 0) : IsRegular k
· 使用定理 `IsRegular.right`：∀ {R : Type u_1} [inst : Mul R] {c : R}, IsRegular c → 
IsRightRegular c

--- 原说明 ---
A ring with no zero divisors is a cancellative `MonoidWithZero`.

Note this is not an instance as it forms a typeclass loop.
-/
lemma NoZeroDivisors.toIsCancelMulZero [NonUnitalNonAssocRing α] [NoZeroDivisors α] :
    IsCancelMulZero α where
  mul_left_cancel_of_ne_zero ha := (IsRegular.of_ne_zero' ha).1
  mul_right_cancel_of_ne_zero hb := (IsRegular.of_ne_zero' hb).2

namespace IsDedekindFiniteMonoid

variable [Ring α]

/-- A ring is Dedekind-finite if and only if every element has at most one right inverse. -/
/-
**IsDedekindFiniteMonoid.iff_eq_of_mul_left_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Is
DedekindFiniteMonoid`。
形式化陈述：iff_eq_of_mul_left_eq_one : IsDedekindFiniteMonoid α ↔ forall x y z : α, x
 * y = 1 -> x * z = 1 -> y = z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `isDedekindFiniteMonoid_iff`：∀ (M : Type u_2) [inst : MulOne M], IsDedeki
ndFiniteMonoid M ↔ ∀ {a b : M}, a * b = 1 → b * a = 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `right_eq_add`：∀ {M : Type u_4} [inst : AddMonoid M] [IsRightCancelAdd M]
 {a b : M}, b = a + b ↔ a = 0
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G

--- 原说明 ---
A ring is Dedekind-finite if and only if every element has at most one right inv
erse.
-/
theorem iff_eq_of_mul_left_eq_one :
    IsDedekindFiniteMonoid α ↔ ∀ x y z : α, x * y = 1 → x * z = 1 → y = z := by
  refine (isDedekindFiniteMonoid_iff _).trans ⟨fun h x y z hxy hxz ↦ ?_, fun h x y eq ↦ ?_⟩
  · simpa [← mul_assoc, h hxz] using congr_arg (z * ·) hxy
  have := h _ _ (1 - y * x + y) eq <| by
    rw [mul_add, mul_sub, ← mul_assoc, eq, mul_one, one_mul, sub_self, zero_add]
  rwa [right_eq_add, sub_eq_zero, eq_comm] at this

/-- A ring is Dedekind-finite if and only if every element has at most one left inverse. -/
/-
**IsDedekindFiniteMonoid.iff_eq_of_mul_right_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `I
sDedekindFiniteMonoid`。
形式化陈述：iff_eq_of_mul_right_eq_one : IsDedekindFiniteMonoid α ↔ forall x y z : α, 
x * z = 1 -> y * z = 1 -> x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `isDedekindFiniteMonoid_iff`：∀ (M : Type u_2) [inst : MulOne M], IsDedeki
ndFiniteMonoid M ↔ ∀ {a b : M}, a * b = 1 → b * a = 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `right_eq_add`：∀ {M : Type u_4} [inst : AddMonoid M] [IsRightCancelAdd M]
 {a b : M}, b = a + b ↔ a = 0
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G

--- 原说明 ---
A ring is Dedekind-finite if and only if every element has at most one left inve
rse.
-/
theorem iff_eq_of_mul_right_eq_one :
    IsDedekindFiniteMonoid α ↔ ∀ x y z : α, x * z = 1 → y * z = 1 → x = y := by
  refine (isDedekindFiniteMonoid_iff _).trans ⟨fun h x y z hxz hyz ↦ ?_, fun h x y eq ↦ ?_⟩
  · simpa [mul_assoc, h hyz] using congr_arg (· * y) hxz
  have := h _ (1 - y * x + x) _ eq <| by
    rw [add_mul, sub_mul, mul_assoc, eq, one_mul, mul_one, sub_self, zero_add]
  rwa [right_eq_add, sub_eq_zero, eq_comm] at this

end IsDedekindFiniteMonoid

