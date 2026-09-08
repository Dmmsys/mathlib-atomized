/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Finite
public import Mathlib.Data.Set.Card

/-!
# Cardinalities of pointwise operations on sets
-/

public section

assert_not_exists Field

open scoped Cardinal Pointwise

namespace Set
variable {G M α : Type*}

section Mul
variable [Mul M] {s t : Set M}

@[to_additive]
/-
**Set._root_.Cardinal.mk_mul_le** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Cardinal.mk_mul_le : #(s * t) ≤ #s * #t := by
  rw [← image2_mul]; exact Cardinal.mk_image2_le

variable [IsCancelMul M]

@[to_additive]
/-
**Set.natCard_mul_le** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：natCard_mul_le : Nat.card (s * t) <= Nat.card s * Nat.card t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.infinite_or_finite`：∀ {α : Type u} (s : Set α), s.Infinite ∨ s.Finit
e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Infinite.card_eq_zero`：∀ {α : Type u_1} {s : Set α}, s.Infinite → Na
t.card ↑s = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Cardinal.toNat_le_toNat`：toNat_le_toNat (hcd : c <= d) (hd : d < ℵ₀) : t
oNat c <= toNat d
· 使用定理 `Cardinal.mk_mul_le`：∀ {M : Type u_2} [inst : Mul M] {s t : Set M}, Cardi
nal.mk ↑(s * t) ≤ Cardinal.mk ↑s * Cardinal.mk ↑t
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsCancelMul.toIsLeftCancelMul`：∀ {G : Type u} {inst : Mul G} [self : IsC
ancelMul G], IsLeftCancelMul G
· 使用定理 `IsCancelMul.toIsRightCancelMul`：∀ {G : Type u} {inst : Mul G} [self : Is
CancelMul G], IsRightCancelMul G
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Cardinal.mk_eq_zero`：mk_eq_zero (α : Type u) [IsEmpty α] : #α = 0
· 使用定理 `Set.instIsEmptyElemEmptyCollection`：∀ (α : Type u), IsEmpty ↑∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
lemma natCard_mul_le : Nat.card (s * t) ≤ Nat.card s * Nat.card t := by
  obtain h | h := (s * t).infinite_or_finite
  · simp [Set.Infinite.card_eq_zero h]
  simp only [Nat.card, ← Cardinal.toNat_mul]
  refine Cardinal.toNat_le_toNat Cardinal.mk_mul_le ?_
  aesop (add simp [Cardinal.mul_lt_aleph0_iff, finite_mul])

end Mul

section InvolutiveInv
variable [InvolutiveInv G]

@[to_additive (attr := simp)]
/-
**Set._root_.Cardinal.mk_inv** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Cardinal.mk_inv (s : Set G) : #↥(s⁻¹) = #s := by
  rw [← image_inv_eq_inv, Cardinal.mk_image_eq_of_injOn _ _ inv_injective.injOn]

@[to_additive (attr := simp)]
/-
**Set.encard_inv** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：encard_inv (s : Set G) : s⁻¹.encard = s.encard
参数：s : Set G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_inv`：∀ {G : Type u_1} [inst : InvolutiveInv G] (s : Set G), 
Cardinal.mk ↑s⁻¹ = Cardinal.mk ↑s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma encard_inv (s : Set G) : s⁻¹.encard = s.encard := by
  simp [← toENat_cardinalMk]

@[to_additive (attr := simp)]
/-
**Set.ncard_inv** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：ncard_inv (s : Set G) : s⁻¹.ncard = s.ncard
参数：s : Set G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.encard_inv`：encard_inv (s : Set G) : s⁻¹.encard = s.encard
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ncard_inv (s : Set G) : s⁻¹.ncard = s.ncard := by simp [ncard]

@[to_additive]
/-
**Set.natCard_inv** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：natCard_inv (s : Set G) : Nat.card ↥(s⁻¹) = Nat.card s
参数：s : Set G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.ncard_inv`：ncard_inv (s : Set G) : s⁻¹.ncard = s.ncard
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma natCard_inv (s : Set G) : Nat.card ↥(s⁻¹) = Nat.card s := by simp

end InvolutiveInv

section DivInvMonoid
variable [DivInvMonoid M] {s t : Set M}

@[to_additive]
/-
**Set._root_.Cardinal.mk_div_le** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Cardinal.mk_div_le : #(s / t) ≤ #s * #t := by
  rw [← image2_div]; exact Cardinal.mk_image2_le

end DivInvMonoid

section Group
variable [Group G] {s t : Set G}

@[to_additive]
/-
**Set.natCard_div_le** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：natCard_div_le : Nat.card (s / t) <= Nat.card s * Nat.card t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.natCard_inv`：natCard_inv (s : Set G) : Nat.card ↥(s⁻¹) = Nat.card s
· 使用引理 `Set.natCard_mul_le`：natCard_mul_le : Nat.card (s * t) <= Nat.card s * Na
t.card t
· 使用定理 `CancelMonoid.toIsCancelMul`：∀ (M : Type u) [inst : CancelMonoid M], IsCa
ncelMul M
-/
lemma natCard_div_le : Nat.card (s / t) ≤ Nat.card s * Nat.card t := by
  rw [div_eq_mul_inv, ← natCard_inv t]; exact natCard_mul_le

variable [MulAction G α]

@[to_additive (attr := simp)]
/-
**Set._root_.Cardinal.mk_smul_set** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Cardinal.mk_smul_set (a : G) (s : Set α) : #↥(a • s) = #s :=
  Cardinal.mk_image_eq_of_injOn _ _ (MulAction.injective a).injOn

@[to_additive (attr := simp)]
/-
**Set.encard_smul_set** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：encard_smul_set (a : G) (s : Set α) : (a • s).encard = s.encard
参数：a : G；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_smul_set`：∀ {G : Type u_1} {α : Type u_3} [inst : Group G] [
inst_1 : MulAction G α] (a : G) (s : Set α),   Cardinal.mk ↑(a • s) = Cardinal.m
k ↑s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma encard_smul_set (a : G) (s : Set α) : (a • s).encard = s.encard := by
  simp [← toENat_cardinalMk]

@[to_additive (attr := simp)]
/-
**Set.ncard_smul_set** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：ncard_smul_set (a : G) (s : Set α) : (a • s).ncard = s.ncard
参数：a : G；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.encard_smul_set`：encard_smul_set (a : G) (s : Set α) : (a • s).encar
d = s.encard
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ncard_smul_set (a : G) (s : Set α) : (a • s).ncard = s.ncard := by simp [ncard]

@[to_additive]
/-
**Set.natCard_smul_set** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：natCard_smul_set (a : G) (s : Set α) : Nat.card ↥(a • s) = Nat.card s
参数：a : G；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.ncard_smul_set`：ncard_smul_set (a : G) (s : Set α) : (a • s).ncard =
 s.ncard
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma natCard_smul_set (a : G) (s : Set α) : Nat.card ↥(a • s) = Nat.card s := by
  simp

end Group
end Set

