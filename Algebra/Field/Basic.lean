/-
Copyright (c) 2014 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Leonardo de Moura, Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Ring.GrindInstances
public import Mathlib.Algebra.Ring.Commute
public import Mathlib.Algebra.Ring.Invertible
public import Mathlib.Order.OrderDual
public import Mathlib.Order.Lex
public import Mathlib.Algebra.Order.Ring.Synonym
public import Mathlib.Algebra.Order.GroupWithZero.Synonym

import Mathlib.Tactic.Tauto

/-!
# Lemmas about division (semi)rings and (semi)fields

-/

@[expose] public section

open Function OrderDual Set

universe u

variable {K L : Type*}

section DivisionSemiring

variable [DivisionSemiring K] {a b c d : K}

/-
**add_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：add_div (a b c : K) : (a + b) / c = a / c + b / c
参数：a b c : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem add_div (a b c : K) : (a + b) / c = a / c + b / c := by simp_rw [div_eq_mul_inv, add_mul]
/-
**same_add_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：same_add_div (h : b != 0) : (b + a) / b = 1 + a / b
参数：h : b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `add_div`：add_div (a b c : K) : (a + b) / c = a / c + b / c
-/
theorem same_add_div (h : b ≠ 0) : (b + a) / b = 1 + a / b := by rw [← div_self h, add_div]
/-
**div_add_same** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_add_same (h : b != 0) : (a + b) / b = a / b + 1
参数：h : b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `add_div`：add_div (a b c : K) : (a + b) / c = a / c + b / c
-/
theorem div_add_same (h : b ≠ 0) : (a + b) / b = a / b + 1 := by rw [← div_self h, add_div]
/-
**one_add_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：one_add_div (h : b != 0) : 1 + a / b = (b + a) / b
参数：h : b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `same_add_div`：same_add_div (h : b != 0) : (b + a) / b = 1 + a / b
-/
theorem one_add_div (h : b ≠ 0) : 1 + a / b = (b + a) / b :=
  (same_add_div h).symm
/-
**div_add_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_add_one (h : b != 0) : a / b + 1 = (a + b) / b
参数：h : b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_add_same`：div_add_same (h : b != 0) : (a + b) / b = a / b + 1
-/
theorem div_add_one (h : b ≠ 0) : a / b + 1 = (a + b) / b :=
  (div_add_same h).symm

/-- See `inv_add_inv` for the more convenient version when `K` is commutative. -/
/-
**inv_add_inv'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_add_inv' (ha : a != 0) (hb : b != 0) : a⁻¹ + b⁻¹ = a⁻¹ * (a + b) * b⁻¹
参数：ha : a != 0；hb : b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `invOf_add_invOf`：invOf_add_invOf [Semiring R] (a b : R) [Invertible a] [
Invertible b] : ⅟a + ⅟b = ⅟a * (a + b) * ⅟b

--- 原说明 ---
See `inv_add_inv` for the more convenient version when `K` is commutative.
-/
theorem inv_add_inv' (ha : a ≠ 0) (hb : b ≠ 0) :
    a⁻¹ + b⁻¹ = a⁻¹ * (a + b) * b⁻¹ :=
  let _ := invertibleOfNonzero ha; let _ := invertibleOfNonzero hb; invOf_add_invOf a b
/-
**one_div_mul_add_mul_one_div_eq_one_div_add_one_div** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：one_div_mul_add_mul_one_div_eq_one_div_add_one_div (ha : a != 0) (hb : b !
= 0) : 1 / a * (a + b) * (1 / b) = 1 / a + 1 / b
参数：ha : a != 0；hb : b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_add_inv'`：inv_add_inv' (ha : a != 0) (hb : b != 0) : a⁻¹ + b⁻¹ = a⁻¹
 * (a + b) * b⁻¹
-/
theorem one_div_mul_add_mul_one_div_eq_one_div_add_one_div (ha : a ≠ 0) (hb : b ≠ 0) :
    1 / a * (a + b) * (1 / b) = 1 / a + 1 / b := by
  simpa only [one_div] using (inv_add_inv' ha hb).symm
/-
**add_div_eq_mul_add_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：add_div_eq_mul_add_div (a b : K) (hc : c != 0) : a + b / c = (a * c + b) /
 c
参数：a b : K；hc : c != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `eq_div_iff_mul_eq`：eq_div_iff_mul_eq (hc : c != 0) : a = b / c ↔ a * c =
 b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `right_distrib`：right_distrib [Mul R] [Add R] [RightDistribClass R] (a b 
c : R) : (a + b) * c = a * c + b * c
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用引理 `div_mul_cancel₀`：div_mul_cancel₀ (a : G₀) (h : b != 0) : a / b * b = a
-/
theorem add_div_eq_mul_add_div (a b : K) (hc : c ≠ 0) : a + b / c = (a * c + b) / c :=
  (eq_div_iff_mul_eq hc).2 <| by rw [right_distrib, div_mul_cancel₀ _ hc]
/-
**add_div'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：add_div' (a b c : K) (hc : c != 0) : b + a / c = (b * c + a) / c
参数：a b c : K；hc : c != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_div`：add_div (a b c : K) : (a + b) / c = a / c + b / c
· 使用定理 `mul_div_cancel_right₀`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [ins
t_1 : Div M₀] [MulDivCancelClass M₀] (a : M₀) {b : M₀},   b ≠ 0 → a * b / b = a
· 使用定理 `GroupWithZero.toMulDivCancelClass`：∀ {G₀ : Type u} [inst : GroupWithZero
 G₀], MulDivCancelClass G₀
-/
theorem add_div' (a b c : K) (hc : c ≠ 0) : b + a / c = (b * c + a) / c := by
  rw [add_div, mul_div_cancel_right₀ _ hc]
/-
**div_add'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_add' (a b c : K) (hc : c != 0) : a / c + b = (a + b * c) / c
参数：a b c : K；hc : c != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_div'`：add_div' (a b c : K) (hc : c != 0) : b + a / c = (b * c + a) /
 c
-/
theorem div_add' (a b c : K) (hc : c ≠ 0) : a / c + b = (a + b * c) / c := by
  rwa [add_comm, add_div', add_comm]
/-
**Commute.div_add_div** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：∀ {K : Type u_1} [inst : DivisionSemiring K] {a b c d : K},   Commute b c 
→ Commute b d → b ≠ 0 → d ≠ 0 → a / b + c / d = (a * d + b * c) / (b * d)
参数：a * d + b * c；b * d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_div`：add_div (a b c : K) : (a + b) / c = a / c + b / c
· 使用引理 `mul_div_mul_right`：mul_div_mul_right (a b : G₀) (hc : c != 0) : a * c / 
(b * c) = a / b
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
-/
protected theorem Commute.div_add_div (hbc : Commute b c) (hbd : Commute b d) (hb : b ≠ 0)
    (hd : d ≠ 0) : a / b + c / d = (a * d + b * c) / (b * d) := by
  rw [add_div, mul_div_mul_right _ b hd, hbc.eq, hbd.eq, mul_div_mul_right c d hb]
/-
**Commute.one_div_add_one_div** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：∀ {K : Type u_1} [inst : DivisionSemiring K] {a b : K}, Commute a b → a ≠ 
0 → b ≠ 0 → 1 / a + 1 / b = (a + b) / (a * b)
参数：a + b；a * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Commute.div_add_div`：∀ {K : Type u_1} [inst : DivisionSemiring K] {a b c
 d : K},   Commute b c → Commute b d → b ≠ 0 → d ≠ 0 → a / b + c / d = (a * d + 
b * c) / …
· 使用定理 `Commute.one_right`：one_right (a : M) : Commute a 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
protected theorem Commute.one_div_add_one_div (hab : Commute a b) (ha : a ≠ 0) (hb : b ≠ 0) :
    1 / a + 1 / b = (a + b) / (a * b) := by
  rw [(Commute.one_right a).div_add_div hab ha hb, one_mul, mul_one, add_comm]
/-
**Commute.inv_add_inv** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：∀ {K : Type u_1} [inst : DivisionSemiring K] {a b : K}, Commute a b → a ≠ 
0 → b ≠ 0 → a⁻¹ + b⁻¹ = (a + b) / (a * b)
参数：a + b；a * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_eq_one_div`：inv_eq_one_div (x : G) : x⁻¹ = 1 / x
· 使用定理 `Commute.one_div_add_one_div`：∀ {K : Type u_1} [inst : DivisionSemiring K
] {a b : K}, Commute a b → a ≠ 0 → b ≠ 0 → 1 / a + 1 / b = (a + b) / (a * b)
-/
protected theorem Commute.inv_add_inv (hab : Commute a b) (ha : a ≠ 0) (hb : b ≠ 0) :
    a⁻¹ + b⁻¹ = (a + b) / (a * b) := by
  rw [inv_eq_one_div, inv_eq_one_div, hab.one_div_add_one_div ha hb]

variable [NeZero (2 : K)]
/-
**add_self_div_two** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {K : Type u_1} [inst : DivisionSemiring K] [NeZero 2] (a : K), (a + a) /
 2 = a
参数：a : K；a + a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_two`：mul_two (n : α) : n * 2 = n + n
· 使用定理 `mul_div_cancel_right₀`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [ins
t_1 : Div M₀] [MulDivCancelClass M₀] (a : M₀) {b : M₀},   b ≠ 0 → a * b / b = a
· 使用定理 `GroupWithZero.toMulDivCancelClass`：∀ {G₀ : Type u} [inst : GroupWithZero
 G₀], MulDivCancelClass G₀
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
-/
@[simp] lemma add_self_div_two (a : K) : (a + a) / 2 = a := by
  rw [← mul_two, mul_div_cancel_right₀ a two_ne_zero]
/-
**add_halves** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {K : Type u_1} [inst : DivisionSemiring K] [NeZero 2] (a : K), a / 2 + a
 / 2 = a
参数：a : K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_div`：add_div (a b c : K) : (a + b) / c = a / c + b / c
· 使用定理 `add_self_div_two`：∀ {K : Type u_1} [inst : DivisionSemiring K] [NeZero 2
] (a : K), (a + a) / 2 = a
-/
@[simp] lemma add_halves (a : K) : a / 2 + a / 2 = a := by rw [← add_div, add_self_div_two]

end DivisionSemiring

section DivisionRing

variable [DivisionRing K] {a b c d : K}

@[simp]
/-
**div_neg_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_neg_self {a : K} (h : a != 0) : a / -a = -1
参数：h : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `div_neg_eq_neg_div`：div_neg_eq_neg_div (a b : R) : b / -a = -(b / a)
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
-/
theorem div_neg_self {a : K} (h : a ≠ 0) : a / -a = -1 := by rw [div_neg_eq_neg_div, div_self h]

@[simp]
/-
**neg_div_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：neg_div_self {a : K} (h : a != 0) : -a / a = -1
参数：h : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `neg_div`：neg_div (a b : R) : -b / a = -(b / a)
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
-/
theorem neg_div_self {a : K} (h : a ≠ 0) : -a / a = -1 := by rw [neg_div, div_self h]
/-
**div_sub_div_same** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_sub_div_same (a b c : K) : a / c - b / c = (a - b) / c
参数：a b c : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `neg_div`：neg_div (a b : R) : -b / a = -(b / a)
· 使用定理 `add_div`：add_div (a b c : K) : (a + b) / c = a / c + b / c
-/
theorem div_sub_div_same (a b c : K) : a / c - b / c = (a - b) / c := by
  rw [sub_eq_add_neg, ← neg_div, ← add_div, sub_eq_add_neg]
/-
**same_sub_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：same_sub_div {a b : K} (h : b != 0) : (b - a) / b = 1 - a / b
参数：h : b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `div_sub_div_same`：div_sub_div_same (a b c : K) : a / c - b / c = (a - b)
 / c
-/
theorem same_sub_div {a b : K} (h : b ≠ 0) : (b - a) / b = 1 - a / b := by
  simpa only [← @div_self _ _ b h] using (div_sub_div_same b a b).symm
/-
**one_sub_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：one_sub_div {a b : K} (h : b != 0) : 1 - a / b = (b - a) / b
参数：h : b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `same_sub_div`：same_sub_div {a b : K} (h : b != 0) : (b - a) / b = 1 - a 
/ b
-/
theorem one_sub_div {a b : K} (h : b ≠ 0) : 1 - a / b = (b - a) / b :=
  (same_sub_div h).symm
/-
**div_sub_same** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_sub_same {a b : K} (h : b != 0) : (a - b) / b = a / b - 1
参数：h : b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `div_sub_div_same`：div_sub_div_same (a b c : K) : a / c - b / c = (a - b)
 / c
-/
theorem div_sub_same {a b : K} (h : b ≠ 0) : (a - b) / b = a / b - 1 := by
  simpa only [← @div_self _ _ b h] using (div_sub_div_same a b b).symm
/-
**div_sub_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_sub_one {a b : K} (h : b != 0) : a / b - 1 = (a - b) / b
参数：h : b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_sub_same`：div_sub_same {a b : K} (h : b != 0) : (a - b) / b = a / b 
- 1
-/
theorem div_sub_one {a b : K} (h : b ≠ 0) : a / b - 1 = (a - b) / b :=
  (div_sub_same h).symm
/-
**sub_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sub_div (a b c : K) : (a - b) / c = a / c - b / c
参数：a b c : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_sub_div_same`：div_sub_div_same (a b c : K) : a / c - b / c = (a - b)
 / c
-/
theorem sub_div (a b c : K) : (a - b) / c = a / c - b / c :=
  (div_sub_div_same _ _ _).symm

/-- See `inv_sub_inv` for the more convenient version when `K` is commutative. -/
/-
**inv_sub_inv'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_sub_inv' {a b : K} (ha : a != 0) (hb : b != 0) : a⁻¹ - b⁻¹ = a⁻¹ * (b 
- a) * b⁻¹
参数：ha : a != 0；hb : b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `invOf_sub_invOf`：invOf_sub_invOf [Ring R] (a b : R) [Invertible a] [Inve
rtible b] : ⅟a - ⅟b = ⅟a * (b - a) * ⅟b

--- 原说明 ---
See `inv_sub_inv` for the more convenient version when `K` is commutative.
-/
theorem inv_sub_inv' {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) : a⁻¹ - b⁻¹ = a⁻¹ * (b - a) * b⁻¹ :=
  let _ := invertibleOfNonzero ha; let _ := invertibleOfNonzero hb; invOf_sub_invOf a b
/-
**one_div_mul_sub_mul_one_div_eq_one_div_add_one_div** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：one_div_mul_sub_mul_one_div_eq_one_div_add_one_div (ha : a != 0) (hb : b !
= 0) : 1 / a * (b - a) * (1 / b) = 1 / a - 1 / b
参数：ha : a != 0；hb : b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_sub_inv'`：inv_sub_inv' {a b : K} (ha : a != 0) (hb : b != 0) : a⁻¹ -
 b⁻¹ = a⁻¹ * (b - a) * b⁻¹
-/
theorem one_div_mul_sub_mul_one_div_eq_one_div_add_one_div (ha : a ≠ 0) (hb : b ≠ 0) :
    1 / a * (b - a) * (1 / b) = 1 / a - 1 / b := by
  simpa only [one_div] using (inv_sub_inv' ha hb).symm
/-
**inv_eq_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {G : Type u_2} [inst : Group G] [IsMulTorsionFree G] {a : G}, a⁻¹ = a ↔ 
a = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `self_eq_inv`：∀ {G : Type u_2} [inst : Group G] [IsMulTorsionFree G] {a :
 G}, a = a⁻¹ ↔ a = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem inv_eq_self₀ {a : K} : a⁻¹ = a ↔ a = -1 ∨ a = 0 ∨ a = 1 := by
  obtain rfl | ha := eq_or_ne a 0; · simp
  rw [← mul_eq_one_iff_inv_eq₀ ha, ← pow_two, sq_eq_one_iff]
  tauto
/-
**self_eq_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {G : Type u_2} [inst : Group G] [IsMulTorsionFree G] {a : G}, a = a⁻¹ ↔ 
a = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `sq_eq_one`：sq_eq_one : a ^ 2 = 1 ↔ a = 1
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `mul_eq_one_iff_eq_inv`：mul_eq_one_iff_eq_inv : a * b = 1 ↔ a = b⁻¹
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem self_eq_inv₀ {a : K} : a = a⁻¹ ↔ a = -1 ∨ a = 0 ∨ a = 1 := by
  rw [eq_comm, inv_eq_self₀]

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) DivisionRing.isDomain : IsDomain K :=
  NoZeroDivisors.to_isDomain _
/-
**Commute.div_sub_div** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：∀ {K : Type u_1} [inst : DivisionRing K] {a b c d : K},   Commute b c → Co
mmute b d → b ≠ 0 → d ≠ 0 → a / b - c / d = (a * d - b * c) / (b * d)
参数：a * d - b * c；b * d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `neg_div`：neg_div (a b : R) : -b / a = -(b / a)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `Commute.div_add_div`：∀ {K : Type u_1} [inst : DivisionSemiring K] {a b c
 d : K},   Commute b c → Commute b d → b ≠ 0 → d ≠ 0 → a / b + c / d = (a * d + 
b * c) / …
· 使用定理 `Commute.neg_right`：neg_right : Commute a b -> Commute a (-b)
-/
protected theorem Commute.div_sub_div (hbc : Commute b c) (hbd : Commute b d) (hb : b ≠ 0)
    (hd : d ≠ 0) : a / b - c / d = (a * d - b * c) / (b * d) := by
  simpa only [mul_neg, neg_div, ← sub_eq_add_neg] using hbc.neg_right.div_add_div hbd hb hd
/-
**Commute.inv_sub_inv** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：∀ {K : Type u_1} [inst : DivisionRing K] {a b : K}, Commute a b → a ≠ 0 → 
b ≠ 0 → a⁻¹ - b⁻¹ = (b - a) / (a * b)
参数：b - a；a * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inv_eq_one_div`：inv_eq_one_div (x : G) : x⁻¹ = 1 / x
· 使用定理 `Commute.div_sub_div`：∀ {K : Type u_1} [inst : DivisionRing K] {a b c d :
 K},   Commute b c → Commute b d → b ≠ 0 → d ≠ 0 → a / b - c / d = (a * d - b * 
c) / (b *…
· 使用定理 `Commute.one_right`：one_right (a : M) : Commute a 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem Commute.inv_sub_inv (hab : Commute a b) (ha : a ≠ 0) (hb : b ≠ 0) :
    a⁻¹ - b⁻¹ = (b - a) / (a * b) := by
  simp only [inv_eq_one_div, (Commute.one_right a).div_sub_div hab ha hb, one_mul, mul_one]

variable [NeZero (2 : K)]
/-
**sub_half** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sub_half (a : K) : a - a / 2 = a / 2
参数：a : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_iff_eq_add`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a -
 b = c ↔ a = c + b
· 使用定理 `add_halves`：∀ {K : Type u_1} [inst : DivisionSemiring K] [NeZero 2] (a :
 K), a / 2 + a / 2 = a
-/
lemma sub_half (a : K) : a - a / 2 = a / 2 := by rw [sub_eq_iff_eq_add, add_halves]
/-
**half_sub** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：half_sub (a : K) : a / 2 - a = -(a / 2)
参数：a : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用引理 `sub_half`：sub_half (a : K) : a - a / 2 = a / 2
-/
lemma half_sub (a : K) : a / 2 - a = -(a / 2) := by rw [← neg_sub, sub_half]

end DivisionRing

section Semifield

variable [Semifield K] {a b d : K}

/-
**div_add_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_add_div (a : K) (c : K) (hb : b != 0) (hd : d != 0) : a / b + c / d = 
(a * d + b * c) / (b * d)
参数：a : K；c : K；hb : b != 0；hd : d != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.div_add_div`：∀ {K : Type u_1} [inst : DivisionSemiring K] {a b c
 d : K},   Commute b c → Commute b d → b ≠ 0 → d ≠ 0 → a / b + c / d = (a * d + 
b * c) / …
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
-/
theorem div_add_div (a : K) (c : K) (hb : b ≠ 0) (hd : d ≠ 0) :
    a / b + c / d = (a * d + b * c) / (b * d) :=
  (Commute.all b _).div_add_div (Commute.all _ _) hb hd
/-
**one_div_add_one_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：one_div_add_one_div (ha : a != 0) (hb : b != 0) : 1 / a + 1 / b = (a + b) 
/ (a * b)
参数：ha : a != 0；hb : b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.one_div_add_one_div`：∀ {K : Type u_1} [inst : DivisionSemiring K
] {a b : K}, Commute a b → a ≠ 0 → b ≠ 0 → 1 / a + 1 / b = (a + b) / (a * b)
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
-/
theorem one_div_add_one_div (ha : a ≠ 0) (hb : b ≠ 0) : 1 / a + 1 / b = (a + b) / (a * b) :=
  (Commute.all a _).one_div_add_one_div ha hb
/-
**inv_add_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_add_inv (ha : a != 0) (hb : b != 0) : a⁻¹ + b⁻¹ = (a + b) / (a * b)
参数：ha : a != 0；hb : b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.inv_add_inv`：∀ {K : Type u_1} [inst : DivisionSemiring K] {a b :
 K}, Commute a b → a ≠ 0 → b ≠ 0 → a⁻¹ + b⁻¹ = (a + b) / (a * b)
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
-/
theorem inv_add_inv (ha : a ≠ 0) (hb : b ≠ 0) : a⁻¹ + b⁻¹ = (a + b) / (a * b) :=
  (Commute.all a _).inv_add_inv ha hb

end Semifield

section Field

variable [Field K]

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) Field.toGrindField : Lean.Grind.Field K :=
  { CommRing.toGrindCommRing K, ‹Field K› with
    zpow := ⟨fun a n => a^n⟩
    zpow_zero a := by simp
    zpow_succ a n := by
      by_cases h : a = 0
      · rw [← Int.natCast_add_one, zpow_natCast, zpow_natCast, pow_succ]
      · rw [zpow_add_one₀ h]
    zpow_neg a n := by simp
    zero_ne_one := zero_ne_one }

attribute [local simp] mul_assoc mul_comm mul_left_comm
/-
**div_sub_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_sub_div (a : K) {b : K} (c : K) {d : K} (hb : b != 0) (hd : d != 0) : 
a / b - c / d = (a * d - b * c) / (b * d)
参数：a : K；c : K；hb : b != 0；hd : d != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.div_sub_div`：∀ {K : Type u_1} [inst : DivisionRing K] {a b c d :
 K},   Commute b c → Commute b d → b ≠ 0 → d ≠ 0 → a / b - c / d = (a * d - b * 
c) / (b *…
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
-/
theorem div_sub_div (a : K) {b : K} (c : K) {d : K} (hb : b ≠ 0) (hd : d ≠ 0) :
    a / b - c / d = (a * d - b * c) / (b * d) :=
  (Commute.all b _).div_sub_div (Commute.all _ _) hb hd
/-
**inv_sub_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_sub_inv {a b : K} (ha : a != 0) (hb : b != 0) : a⁻¹ - b⁻¹ = (b - a) / 
(a * b)
参数：ha : a != 0；hb : b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_eq_one_div`：inv_eq_one_div (x : G) : x⁻¹ = 1 / x
· 使用定理 `div_sub_div`：div_sub_div (a : K) {b : K} (c : K) {d : K} (hb : b != 0) (
hd : d != 0) : a / b - c / d = (a * d - b * c) / (b * d)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem inv_sub_inv {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) : a⁻¹ - b⁻¹ = (b - a) / (a * b) := by
  rw [inv_eq_one_div, inv_eq_one_div, div_sub_div _ _ ha hb, one_mul, mul_one]
/-
**sub_div'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sub_div' {a b c : K} (hc : c != 0) : b - a / c = (b * c - a) / c
参数：hc : c != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `div_sub_div`：div_sub_div (a : K) {b : K} (c : K) {d : K} (hb : b != 0) (
hd : d != 0) : a / b - c / d = (a * d - b * c) / (b * d)
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
-/
theorem sub_div' {a b c : K} (hc : c ≠ 0) : b - a / c = (b * c - a) / c := by
  simpa using div_sub_div b a one_ne_zero hc
/-
**div_sub'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：div_sub' {a b c : K} (hc : c != 0) : a / c - b = (a - c * b) / c
参数：hc : c != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `div_sub_div`：div_sub_div (a : K) {b : K} (c : K) {d : K} (hb : b != 0) (
hd : d != 0) : a / b - c / d = (a * d - b * c) / (b * d)
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
-/
theorem div_sub' {a b c : K} (hc : c ≠ 0) : a / c - b = (a - c * b) / c := by
  simpa using div_sub_div a b hc one_ne_zero

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) Field.isDomain : IsDomain K :=
  { DivisionRing.isDomain with }

end Field

section NoncomputableDefs

variable {R : Type*} [Nontrivial R]

/-- Constructs a `DivisionRing` structure on a `Ring` consisting only of units and 0. -/
-- See note [reducible non-instances]
/-
**DivisionRing.ofIsUnitOrEqZero** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：DivisionRing.ofIsUnitOrEqZero [Ring R] (h : forall a : R, IsUnit a ∨ a = 0
) : DivisionRing R where toRing
参数：h : forall a : R, IsUnit a ∨ a = 0。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `GroupWithZero.div_eq_mul_inv`：∀ {G₀ : Type u} [self : GroupWithZero G₀] 
(a b : G₀), a / b = a * b⁻¹
· 使用定理 `GroupWithZero.zpow_zero'`：∀ {G₀ : Type u} [self : GroupWithZero G₀] (a :
 G₀), a ^ 0 = 1
· 使用定理 `GroupWithZero.zpow_succ'`：∀ {G₀ : Type u} [self : GroupWithZero G₀] (n :
 ℕ) (a : G₀), a ^ ↑n.succ = a ^ ↑n * a
· 使用定理 `GroupWithZero.zpow_neg'`：∀ {G₀ : Type u} [self : GroupWithZero G₀] (n : 
ℕ) (a : G₀), a ^ Int.negSucc n = (a ^ ↑n.succ)⁻¹
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `GroupWithZero.mul_inv_cancel`：∀ {G₀ : Type u} [self : GroupWithZero G₀] 
(a : G₀), a ≠ 0 → a * a⁻¹ = 1
· 使用定理 `GroupWithZero.inv_zero`：∀ {G₀ : Type u} [self : GroupWithZero G₀], 0⁻¹ =
 0
-/
noncomputable abbrev DivisionRing.ofIsUnitOrEqZero [Ring R] (h : ∀ a : R, IsUnit a ∨ a = 0) :
    DivisionRing R where
  toRing := ‹Ring R›
  __ := groupWithZeroOfIsUnitOrEqZero h
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

/-- Constructs a `Field` structure on a `CommRing` consisting only of units and 0. -/
-- See note [reducible non-instances]
/-
**Field.ofIsUnitOrEqZero** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Field.ofIsUnitOrEqZero [CommRing R] (h : forall a : R, IsUnit a ∨ a = 0) :
 Field R where toCommRing
参数：h : forall a : R, IsUnit a ∨ a = 0。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `DivisionRing.div_eq_mul_inv`：∀ {K : Type u_2} [self : DivisionRing K] (a
 b : K), a / b = a * b⁻¹
· 使用定理 `DivisionRing.zpow_zero'`：∀ {K : Type u_2} [self : DivisionRing K] (a : K
), a ^ 0 = 1
· 使用定理 `DivisionRing.zpow_succ'`：∀ {K : Type u_2} [self : DivisionRing K] (n : ℕ
) (a : K), a ^ ↑n.succ = a ^ ↑n * a
· 使用定理 `DivisionRing.zpow_neg'`：∀ {K : Type u_2} [self : DivisionRing K] (n : ℕ)
 (a : K), a ^ Int.negSucc n = (a ^ ↑n.succ)⁻¹
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `DivisionRing.mul_inv_cancel`：∀ {K : Type u_2} [self : DivisionRing K] (a
 : K), a ≠ 0 → a * a⁻¹ = 1
· 使用定理 `DivisionRing.inv_zero`：∀ {K : Type u_2} [self : DivisionRing K], 0⁻¹ = 0
· 使用定理 `DivisionRing.nnratCast_def`：∀ {K : Type u_2} [self : DivisionRing K] (q 
: ℚ≥0), ↑q = ↑q.num / ↑q.den
· 使用定理 `DivisionRing.nnqsmul_def`：∀ {K : Type u_2} [self : DivisionRing K] (q : 
ℚ≥0) (a : K), DivisionRing.nnqsmul q a = ↑q * a
· 使用定理 `DivisionRing.ratCast_def`：∀ {K : Type u_2} [self : DivisionRing K] (q : 
ℚ), ↑q = ↑q.num / ↑q.den
· 使用定理 `DivisionRing.qsmul_def`：∀ {K : Type u_2} [self : DivisionRing K] (a : ℚ)
 (x : K), DivisionRing.qsmul a x = ↑a * x
-/
noncomputable abbrev Field.ofIsUnitOrEqZero [CommRing R] (h : ∀ a : R, IsUnit a ∨ a = 0) :
    Field R where
  toCommRing := ‹CommRing R›
  __ := DivisionRing.ofIsUnitOrEqZero h

end NoncomputableDefs

namespace Function.Injective
variable [Zero K] [Add K] [Neg K] [Sub K] [One K] [Mul K] [Inv K] [Div K] [SMul ℕ K] [SMul ℤ K]
  [SMul ℚ≥0 K] [SMul ℚ K] [Pow K ℕ] [Pow K ℤ] [NatCast K] [IntCast K] [NNRatCast K] [RatCast K]
  (f : K → L) (hf : Injective f)

/-- Pullback a `DivisionSemiring` along an injective function. -/
-- See note [reducible non-instances]
/-
**Function.Injective.divisionSemiring** 是 Mathlib 中的一个定义，位于命名空间 `Function.Inject
ive`。
形式化陈述：{K : Type u_1} →   {L : Type u_2} →     [inst : Zero K] →       [inst_1 : 
Add K] →         [inst_2 : One K] →           [inst_3 : Mul K] →             [in
st_4 : Inv K] →               [inst_5 : Div K] →                 [inst_6 : SMul 
ℕ K] →                   [inst_7 : SMul ℚ≥0 K] →                     [inst_8 : P
ow K ℕ] →                       [inst_9 : Pow K ℤ] →                         [in
st_10 : NatCast K] →                           [inst_11 : NNRatCast K] →        
                     (f : K → L) →                               Function.Inject
ive f →                                 [inst_12 : DivisionSemiring L] →        
                           f 0 = 0 →                                     f 1 = 1
 →                                       (∀ (x y : K), f (x + y) = f x + f y) → 
                                        (∀ (x y : K), f (x * y) = f x * f y) →  
                                         (∀ (x : K), f x⁻¹ = (f x)⁻¹) →         
                                    (∀ (x y : K), f (x / y) = f x / f y) →      
                                         (∀ (n : ℕ) (x : K), f (n • x) = n • f x
) →                                                 (∀ (q : ℚ≥0) (x : K), f (q •
 x) = q • f x) →                                                   (∀ (x : K) (n
 : ℕ), f (x ^ n) = f x ^ n) →                                                   
  (∀ (x : K) (n : ℤ), f (x ^ n) = f x ^ n) →                                    
                   (∀ (n : ℕ), f ↑n = ↑n) →                                     
                    (∀ (q : ℚ≥0), f ↑q = ↑q) → DivisionSemiring K
参数：f : K → L；∀ (x y : K), f (x + y) = f x + f y；∀ (x y : K), f (x * y) = f x * f
 y；∀ (x : K), f x⁻¹ = (f x)⁻¹；∀ (x y : K), f (x / y) = f x / f y；∀ (n : ℕ) (x : 
K), f (n • x) = n • f x；∀ (q : ℚ≥0) (x : K), f (q • x) = q • f x；∀ (x : K) (n : 
ℕ), f (x ^ n) = f x ^ n；∀ (x : K) (n : ℤ), f (x ^ n) = f x ^ n；∀ (n : ℕ), f ↑n =
 ↑n；∀ (q : ℚ≥0), f ↑q = ↑q。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `GroupWithZero.div_eq_mul_inv`：∀ {G₀ : Type u} [self : GroupWithZero G₀] 
(a b : G₀), a / b = a * b⁻¹
· 使用定理 `GroupWithZero.zpow_zero'`：∀ {G₀ : Type u} [self : GroupWithZero G₀] (a :
 G₀), a ^ 0 = 1
· 使用定理 `GroupWithZero.zpow_succ'`：∀ {G₀ : Type u} [self : GroupWithZero G₀] (n :
 ℕ) (a : G₀), a ^ ↑n.succ = a ^ ↑n * a
· 使用定理 `GroupWithZero.zpow_neg'`：∀ {G₀ : Type u} [self : GroupWithZero G₀] (n : 
ℕ) (a : G₀), a ^ Int.negSucc n = (a ^ ↑n.succ)⁻¹
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `GroupWithZero.inv_zero`：∀ {G₀ : Type u} [self : GroupWithZero G₀], 0⁻¹ =
 0
· 使用定理 `GroupWithZero.mul_inv_cancel`：∀ {G₀ : Type u} [self : GroupWithZero G₀] 
(a : G₀), a ≠ 0 → a * a⁻¹ = 1
-/
protected abbrev divisionSemiring [DivisionSemiring L] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (inv : ∀ x, f x⁻¹ = (f x)⁻¹) (div : ∀ x y, f (x / y) = f x / f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (nnqsmul : ∀ (q : ℚ≥0) (x), f (q • x) = q • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n)
    (natCast : ∀ n : ℕ, f n = n) (nnratCast : ∀ q : ℚ≥0, f q = q) : DivisionSemiring K where
  toSemiring := hf.semiring f zero one add mul nsmul npow natCast
  __ := hf.groupWithZero f zero one mul inv div npow zpow
  nnratCast_def q := hf <| by rw [nnratCast, NNRat.cast_def, div, natCast, natCast]
  nnqsmul := (· • ·)
  nnqsmul_def q a := hf <| by rw [nnqsmul, NNRat.smul_def, mul, nnratCast]

/-- Pullback a `DivisionSemiring` along an injective function. -/
-- See note [reducible non-instances]
/-
**Function.Injective.divisionRing** 是 Mathlib 中的一个定义，位于命名空间 `Function.Injective`
。
形式化陈述：{K : Type u_1} →   {L : Type u_2} →     [inst : Zero K] →       [inst_1 : 
Add K] →         [inst_2 : Neg K] →           [inst_3 : Sub K] →             [in
st_4 : One K] →               [inst_5 : Mul K] →                 [inst_6 : Inv K
] →                   [inst_7 : Div K] →                     [inst_8 : SMul ℕ K]
 →                       [inst_9 : SMul ℤ K] →                         [inst_10 
: SMul ℚ≥0 K] →                           [inst_11 : SMul ℚ K] →                
             [inst_12 : Pow K ℕ] →                               [inst_13 : Pow 
K ℤ] →                                 [inst_14 : NatCast K] →                  
                 [inst_15 : IntCast K] →                                     [in
st_16 : NNRatCast K] →                                       [inst_17 : RatCast 
K] →                                         (f : K → L) →                      
                     Function.Injective f →                                     
        [inst_18 : DivisionRing L] →                                            
   f 0 = 0 →                                                 f 1 = 1 →          
                                         (∀ (x y : K), f (x + y) = f x + f y) → 
                                                    (∀ (x y : K), f (x * y) = f 
x * f y) →                                                       (∀ (x : K), f (
-x) = -f x) →                                                         (∀ (x y : 
K), f (x - y) = f x - f y) →                                                    
       (∀ (x : K), f x⁻¹ = (f x)⁻¹) →                                           
                  (∀ (x y : K), f (x / y) = f x / f y) →                        
                                       (∀ (n : ℕ) (x : K), f (n • x) = n • f x) 
→                                                                 (∀ (n : ℤ) (x 
: K), f (n • x) = n • f x) →                                                    
               (∀ (q : ℚ≥0) (x : K), f (q • x) = q • f x) →                     
                                                (∀ (q : ℚ) (x : K), f (q • x) = 
q • f x) →                                                                      
 (∀ (x : K) (n : ℕ), f (x ^ n) = f x ^ n) →                                     
                                    (∀ (x : K) (n : ℤ), f (x ^ n) = f x ^ n) →  
                                                                         (∀ (n :
 ℕ), f ↑n = ↑n) →                                                               
              (∀ (n : ℤ), f ↑n = ↑n) →                                          
                                     (∀ (q : ℚ≥0), f ↑q = ↑q) →                 
                                                                (∀ (q : ℚ), f ↑q
 = ↑q) → DivisionRing K
参数：f : K → L；∀ (x y : K), f (x + y) = f x + f y；∀ (x y : K), f (x * y) = f x * f
 y；∀ (x : K), f (-x) = -f x；∀ (x y : K), f (x - y) = f x - f y；∀ (x : K), f x⁻¹ 
= (f x)⁻¹；∀ (x y : K), f (x / y) = f x / f y；∀ (n : ℕ) (x : K), f (n • x) = n • 
f x；∀ (n : ℤ) (x : K), f (n • x) = n • f x；∀ (q : ℚ≥0) (x : K), f (q • x) = q • 
f x；∀ (q : ℚ) (x : K), f (q • x) = q • f x；∀ (x : K) (n : ℕ), f (x ^ n) = f x ^ 
n；∀ (x : K) (n : ℤ), f (x ^ n) = f x ^ n；∀ (n : ℕ), f ↑n = ↑n；∀ (n : ℤ), f ↑n = 
↑n；∀ (q : ℚ≥0), f ↑q = ↑q；∀ (q : ℚ), f ↑q = ↑q。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `GroupWithZero.div_eq_mul_inv`：∀ {G₀ : Type u} [self : GroupWithZero G₀] 
(a b : G₀), a / b = a * b⁻¹
· 使用定理 `GroupWithZero.zpow_zero'`：∀ {G₀ : Type u} [self : GroupWithZero G₀] (a :
 G₀), a ^ 0 = 1
· 使用定理 `GroupWithZero.zpow_succ'`：∀ {G₀ : Type u} [self : GroupWithZero G₀] (n :
 ℕ) (a : G₀), a ^ ↑n.succ = a ^ ↑n * a
· 使用定理 `GroupWithZero.zpow_neg'`：∀ {G₀ : Type u} [self : GroupWithZero G₀] (n : 
ℕ) (a : G₀), a ^ Int.negSucc n = (a ^ ↑n.succ)⁻¹
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `GroupWithZero.mul_inv_cancel`：∀ {G₀ : Type u} [self : GroupWithZero G₀] 
(a : G₀), a ≠ 0 → a * a⁻¹ = 1
· 使用定理 `GroupWithZero.inv_zero`：∀ {G₀ : Type u} [self : GroupWithZero G₀], 0⁻¹ =
 0
· 使用定理 `DivisionSemiring.nnratCast_def`：∀ {K : Type u_2} [self : DivisionSemirin
g K] (q : ℚ≥0), ↑q = ↑q.num / ↑q.den
· 使用定理 `DivisionSemiring.nnqsmul_def`：∀ {K : Type u_2} [self : DivisionSemiring 
K] (q : ℚ≥0) (a : K), DivisionSemiring.nnqsmul q a = ↑q * a
-/
protected abbrev divisionRing [DivisionRing L] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x)
    (nnqsmul : ∀ (q : ℚ≥0) (x), f (q • x) = q • f x) (qsmul : ∀ (q : ℚ) (x), f (q • x) = q • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n)
    (natCast : ∀ n : ℕ, f n = n) (intCast : ∀ n : ℤ, f n = n) (nnratCast : ∀ q : ℚ≥0, f q = q)
    (ratCast : ∀ q : ℚ, f q = q) : DivisionRing K where
  toRing := hf.ring f zero one add mul neg sub nsmul zsmul npow natCast intCast
  __ := hf.groupWithZero f zero one mul inv div npow zpow
  __ := hf.divisionSemiring f zero one add mul inv div nsmul nnqsmul npow zpow natCast nnratCast
  ratCast_def q := hf <| by rw [ratCast, div, intCast, natCast, Rat.cast_def]
  qsmul := (· • ·)
  qsmul_def q a := hf <| by rw [qsmul, mul, Rat.smul_def, ratCast]

/-- Pullback a `Field` along an injective function. -/
-- See note [reducible non-instances]
/-
**Function.Injective.semifield** 是 Mathlib 中的一个定义，位于命名空间 `Function.Injective`。
形式化陈述：{K : Type u_1} →   {L : Type u_2} →     [inst : Zero K] →       [inst_1 : 
Add K] →         [inst_2 : One K] →           [inst_3 : Mul K] →             [in
st_4 : Inv K] →               [inst_5 : Div K] →                 [inst_6 : SMul 
ℕ K] →                   [inst_7 : SMul ℚ≥0 K] →                     [inst_8 : P
ow K ℕ] →                       [inst_9 : Pow K ℤ] →                         [in
st_10 : NatCast K] →                           [inst_11 : NNRatCast K] →        
                     (f : K → L) →                               Function.Inject
ive f →                                 [inst_12 : Semifield L] →               
                    f 0 = 0 →                                     f 1 = 1 →     
                                  (∀ (x y : K), f (x + y) = f x + f y) →        
                                 (∀ (x y : K), f (x * y) = f x * f y) →         
                                  (∀ (x : K), f x⁻¹ = (f x)⁻¹) →                
                             (∀ (x y : K), f (x / y) = f x / f y) →             
                                  (∀ (n : ℕ) (x : K), f (n • x) = n • f x) →    
                                             (∀ (q : ℚ≥0) (x : K), f (q • x) = q
 • f x) →                                                   (∀ (x : K) (n : ℕ), 
f (x ^ n) = f x ^ n) →                                                     (∀ (x
 : K) (n : ℤ), f (x ^ n) = f x ^ n) →                                           
            (∀ (n : ℕ), f ↑n = ↑n) → (∀ (q : ℚ≥0), f ↑q = ↑q) → Semifield K
参数：f : K → L；∀ (x y : K), f (x + y) = f x + f y；∀ (x y : K), f (x * y) = f x * f
 y；∀ (x : K), f x⁻¹ = (f x)⁻¹；∀ (x y : K), f (x / y) = f x / f y；∀ (n : ℕ) (x : 
K), f (n • x) = n • f x；∀ (q : ℚ≥0) (x : K), f (q • x) = q • f x；∀ (x : K) (n : 
ℕ), f (x ^ n) = f x ^ n；∀ (x : K) (n : ℤ), f (x ^ n) = f x ^ n；∀ (n : ℕ), f ↑n =
 ↑n；∀ (q : ℚ≥0), f ↑q = ↑q。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CommGroupWithZero.div_eq_mul_inv`：∀ {G₀ : Type u_2} [self : CommGroupWit
hZero G₀] (a b : G₀), a / b = a * b⁻¹
· 使用定理 `CommGroupWithZero.zpow_zero'`：∀ {G₀ : Type u_2} [self : CommGroupWithZer
o G₀] (a : G₀), a ^ 0 = 1
· 使用定理 `CommGroupWithZero.zpow_succ'`：∀ {G₀ : Type u_2} [self : CommGroupWithZer
o G₀] (n : ℕ) (a : G₀), a ^ ↑n.succ = a ^ ↑n * a
· 使用定理 `CommGroupWithZero.zpow_neg'`：∀ {G₀ : Type u_2} [self : CommGroupWithZero
 G₀] (n : ℕ) (a : G₀), a ^ Int.negSucc n = (a ^ ↑n.succ)⁻¹
· 使用定理 `CommGroupWithZero.toNontrivial`：∀ {G₀ : Type u_2} [self : CommGroupWithZ
ero G₀], Nontrivial G₀
· 使用定理 `CommGroupWithZero.inv_zero`：∀ {G₀ : Type u_2} [self : CommGroupWithZero 
G₀], 0⁻¹ = 0
· 使用定理 `CommGroupWithZero.mul_inv_cancel`：∀ {G₀ : Type u_2} [self : CommGroupWit
hZero G₀] (a : G₀), a ≠ 0 → a * a⁻¹ = 1
· 使用定理 `DivisionSemiring.nnratCast_def`：∀ {K : Type u_2} [self : DivisionSemirin
g K] (q : ℚ≥0), ↑q = ↑q.num / ↑q.den
· 使用定理 `DivisionSemiring.nnqsmul_def`：∀ {K : Type u_2} [self : DivisionSemiring 
K] (q : ℚ≥0) (a : K), DivisionSemiring.nnqsmul q a = ↑q * a
-/
protected abbrev semifield [Semifield L] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (inv : ∀ x, f x⁻¹ = (f x)⁻¹) (div : ∀ x y, f (x / y) = f x / f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (nnqsmul : ∀ (q : ℚ≥0) (x), f (q • x) = q • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n)
    (natCast : ∀ n : ℕ, f n = n) (nnratCast : ∀ q : ℚ≥0, f q = q) : Semifield K where
  toCommSemiring := hf.commSemiring f zero one add mul nsmul npow natCast
  __ := hf.commGroupWithZero f zero one mul inv div npow zpow
  __ := hf.divisionSemiring f zero one add mul inv div nsmul nnqsmul npow zpow natCast nnratCast

/-- Pullback a `Field` along an injective function. -/
-- See note [reducible non-instances]
/-
**Function.Injective.field** 是 Mathlib 中的一个定义，位于命名空间 `Function.Injective`。
形式化陈述：{K : Type u_1} →   {L : Type u_2} →     [inst : Zero K] →       [inst_1 : 
Add K] →         [inst_2 : Neg K] →           [inst_3 : Sub K] →             [in
st_4 : One K] →               [inst_5 : Mul K] →                 [inst_6 : Inv K
] →                   [inst_7 : Div K] →                     [inst_8 : SMul ℕ K]
 →                       [inst_9 : SMul ℤ K] →                         [inst_10 
: SMul ℚ≥0 K] →                           [inst_11 : SMul ℚ K] →                
             [inst_12 : Pow K ℕ] →                               [inst_13 : Pow 
K ℤ] →                                 [inst_14 : NatCast K] →                  
                 [inst_15 : IntCast K] →                                     [in
st_16 : NNRatCast K] →                                       [inst_17 : RatCast 
K] →                                         (f : K → L) →                      
                     Function.Injective f →                                     
        [inst_18 : Field L] →                                               f 0 
= 0 →                                                 f 1 = 1 →                 
                                  (∀ (x y : K), f (x + y) = f x + f y) →        
                                             (∀ (x y : K), f (x * y) = f x * f y
) →                                                       (∀ (x : K), f (-x) = -
f x) →                                                         (∀ (x y : K), f (
x - y) = f x - f y) →                                                           
(∀ (x : K), f x⁻¹ = (f x)⁻¹) →                                                  
           (∀ (x y : K), f (x / y) = f x / f y) →                               
                                (∀ (n : ℕ) (x : K), f (n • x) = n • f x) →      
                                                           (∀ (n : ℤ) (x : K), f
 (n • x) = n • f x) →                                                           
        (∀ (q : ℚ≥0) (x : K), f (q • x) = q • f x) →                            
                                         (∀ (q : ℚ) (x : K), f (q • x) = q • f x
) →                                                                       (∀ (x 
: K) (n : ℕ), f (x ^ n) = f x ^ n) →                                            
                             (∀ (x : K) (n : ℤ), f (x ^ n) = f x ^ n) →         
                                                                  (∀ (n : ℕ), f 
↑n = ↑n) →                                                                      
       (∀ (n : ℤ), f ↑n = ↑n) →                                                 
                              (∀ (q : ℚ≥0), f ↑q = ↑q) →                        
                                                         (∀ (q : ℚ), f ↑q = ↑q) 
→ Field K
参数：f : K → L；∀ (x y : K), f (x + y) = f x + f y；∀ (x y : K), f (x * y) = f x * f
 y；∀ (x : K), f (-x) = -f x；∀ (x y : K), f (x - y) = f x - f y；∀ (x : K), f x⁻¹ 
= (f x)⁻¹；∀ (x y : K), f (x / y) = f x / f y；∀ (n : ℕ) (x : K), f (n • x) = n • 
f x；∀ (n : ℤ) (x : K), f (n • x) = n • f x；∀ (q : ℚ≥0) (x : K), f (q • x) = q • 
f x；∀ (q : ℚ) (x : K), f (q • x) = q • f x；∀ (x : K) (n : ℕ), f (x ^ n) = f x ^ 
n；∀ (x : K) (n : ℤ), f (x ^ n) = f x ^ n；∀ (n : ℕ), f ↑n = ↑n；∀ (n : ℤ), f ↑n = 
↑n；∀ (q : ℚ≥0), f ↑q = ↑q；∀ (q : ℚ), f ↑q = ↑q。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `DivisionRing.div_eq_mul_inv`：∀ {K : Type u_2} [self : DivisionRing K] (a
 b : K), a / b = a * b⁻¹
· 使用定理 `DivisionRing.zpow_zero'`：∀ {K : Type u_2} [self : DivisionRing K] (a : K
), a ^ 0 = 1
· 使用定理 `DivisionRing.zpow_succ'`：∀ {K : Type u_2} [self : DivisionRing K] (n : ℕ
) (a : K), a ^ ↑n.succ = a ^ ↑n * a
· 使用定理 `DivisionRing.zpow_neg'`：∀ {K : Type u_2} [self : DivisionRing K] (n : ℕ)
 (a : K), a ^ Int.negSucc n = (a ^ ↑n.succ)⁻¹
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `DivisionRing.mul_inv_cancel`：∀ {K : Type u_2} [self : DivisionRing K] (a
 : K), a ≠ 0 → a * a⁻¹ = 1
· 使用定理 `DivisionRing.inv_zero`：∀ {K : Type u_2} [self : DivisionRing K], 0⁻¹ = 0
· 使用定理 `DivisionRing.nnratCast_def`：∀ {K : Type u_2} [self : DivisionRing K] (q 
: ℚ≥0), ↑q = ↑q.num / ↑q.den
· 使用定理 `DivisionRing.nnqsmul_def`：∀ {K : Type u_2} [self : DivisionRing K] (q : 
ℚ≥0) (a : K), DivisionRing.nnqsmul q a = ↑q * a
· 使用定理 `DivisionRing.ratCast_def`：∀ {K : Type u_2} [self : DivisionRing K] (q : 
ℚ), ↑q = ↑q.num / ↑q.den
· 使用定理 `DivisionRing.qsmul_def`：∀ {K : Type u_2} [self : DivisionRing K] (a : ℚ)
 (x : K), DivisionRing.qsmul a x = ↑a * x
-/
protected abbrev field [Field L] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x)
    (nnqsmul : ∀ (q : ℚ≥0) (x), f (q • x) = q • f x) (qsmul : ∀ (q : ℚ) (x), f (q • x) = q • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n)
    (natCast : ∀ n : ℕ, f n = n) (intCast : ∀ n : ℤ, f n = n) (nnratCast : ∀ q : ℚ≥0, f q = q)
    (ratCast : ∀ q : ℚ, f q = q) :
    Field K where
  toCommRing := hf.commRing f zero one add mul neg sub nsmul zsmul npow natCast intCast
  __ := hf.divisionRing f zero one add mul neg sub inv div nsmul zsmul nnqsmul qsmul npow zpow
    natCast intCast nnratCast ratCast

end Function.Injective

/-! ### Order dual -/

namespace OrderDual

/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [RatCast K] : RatCast Kᵒᵈ := inferInstanceAs <| RatCast K
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NNRatCast K] : NNRatCast Kᵒᵈ := inferInstanceAs <| NNRatCast K
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DivisionSemiring K] : DivisionSemiring Kᵒᵈ := inferInstanceAs <| DivisionSemiring K
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DivisionRing K] : DivisionRing Kᵒᵈ := inferInstanceAs <| DivisionRing K
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Semifield K] : Semifield Kᵒᵈ := inferInstanceAs <| Semifield K
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Field K] : Field Kᵒᵈ := inferInstanceAs <| Field K

end OrderDual

/-
**toDual_ratCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {K : Type u_1} [inst : RatCast K] (n : ℚ), OrderDual.toDual ↑n = ↑n
参数：n : ℚ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toDual_ratCast [RatCast K] (n : ℚ) : toDual (n : K) = n := rfl
/-
**ofDual_ratCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {K : Type u_1} [inst : RatCast K] (n : ℚ), OrderDual.ofDual ↑n = ↑n
参数：n : ℚ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofDual_ratCast [RatCast K] (n : ℚ) : (ofDual n : K) = n := rfl

/-! ### Lexicographic order -/

namespace Lex

/-
**Lex.** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [RatCast K] : RatCast (Lex K) := inferInstanceAs <| RatCast K
/-
**Lex.** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DivisionSemiring K] : DivisionSemiring (Lex K) := inferInstanceAs <| DivisionSemiring K
/-
**Lex.** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DivisionRing K] : DivisionRing (Lex K) := inferInstanceAs <| DivisionRing K
/-
**Lex.** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Semifield K] : Semifield (Lex K) := inferInstanceAs <| Semifield K
/-
**Lex.** 是 Mathlib 中的一个实例，位于命名空间 `Lex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Field K] : Field (Lex K) := inferInstanceAs <| Field K

end Lex

/-
**toLex_ratCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {K : Type u_1} [inst : RatCast K] (n : ℚ), toLex ↑n = ↑n
参数：n : ℚ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toLex_ratCast [RatCast K] (n : ℚ) : toLex (n : K) = n := rfl
/-
**ofLex_ratCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {K : Type u_1} [inst : RatCast K] (n : ℚ), ofLex ↑n = ↑n
参数：n : ℚ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofLex_ratCast [RatCast K] (n : ℚ) : (ofLex n : K) = n := rfl
