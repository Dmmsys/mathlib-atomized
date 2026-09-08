/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Order.Module.Defs
public import Mathlib.Algebra.Order.Module.Synonym
public import Mathlib.Algebra.Order.Monoid.OrderDual
public import Mathlib.Order.Monotone.Monovary

/-!
# Monovarying functions and algebraic operations

This file characterises the interaction of ordered algebraic structures with monovariance
of functions.

## See also

`Mathlib.Algebra.Order.Rearrangement` for the n-ary rearrangement inequality
-/

public section

variable {ι α β : Type*}

/-! ### Algebraic operations on monovarying functions -/

section OrderedCommGroup

section
variable [CommGroup α] [Preorder α] [IsOrderedMonoid α] [PartialOrder β]
  {s : Set ι} {f f₁ f₂ : ι → α} {g : ι → β}

@[to_additive (attr := simp)]
/-
**monovaryOn_inv_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：monovaryOn_inv_left : MonovaryOn f⁻¹ g s ↔ AntivaryOn f g s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma monovaryOn_inv_left : MonovaryOn f⁻¹ g s ↔ AntivaryOn f g s := by
  simp [MonovaryOn, AntivaryOn]

@[to_additive (attr := simp)]
/-
**antivaryOn_inv_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：antivaryOn_inv_left : AntivaryOn f⁻¹ g s ↔ MonovaryOn f g s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma antivaryOn_inv_left : AntivaryOn f⁻¹ g s ↔ MonovaryOn f g s := by
  simp [MonovaryOn, AntivaryOn]
/-
**monovary_inv_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} [inst : CommGroup α] [inst_
1 : Preorder α] [IsOrderedMonoid α]   [inst_3 : PartialOrder β] {f : ι → α} {g :
 ι → β}, Monovary f⁻¹ g ↔ Antivary f g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[to_additive (attr := simp)] lemma monovary_inv_left : Monovary f⁻¹ g ↔ Antivary f g := by
  simp [Monovary, Antivary]
/-
**antivary_inv_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} [inst : CommGroup α] [inst_
1 : Preorder α] [IsOrderedMonoid α]   [inst_3 : PartialOrder β] {f : ι → α} {g :
 ι → β}, Antivary f⁻¹ g ↔ Monovary f g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[to_additive (attr := simp)] lemma antivary_inv_left : Antivary f⁻¹ g ↔ Monovary f g := by
  simp [Monovary, Antivary]
/-
**MonovaryOn.mul_left** 是 Mathlib 中的一个定理，位于命名空间 `MonovaryOn`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} [inst : CommGroup α] [inst_
1 : Preorder α] [IsOrderedMonoid α]   [inst_3 : PartialOrder β] {s : Set ι} {f₁ 
f₂ : ι → α} {g : ι → β},   MonovaryOn f₁ g s → MonovaryOn f₂ g s → MonovaryOn (f
₁ * f₂) g s
参数：f₁ * f₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
@[to_additive] lemma MonovaryOn.mul_left (h₁ : MonovaryOn f₁ g s) (h₂ : MonovaryOn f₂ g s) :
    MonovaryOn (f₁ * f₂) g s := fun _i hi _j hj hij ↦ mul_le_mul' (h₁ hi hj hij) (h₂ hi hj hij)
/-
**AntivaryOn.mul_left** 是 Mathlib 中的一个定理，位于命名空间 `AntivaryOn`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} [inst : CommGroup α] [inst_
1 : Preorder α] [IsOrderedMonoid α]   [inst_3 : PartialOrder β] {s : Set ι} {f₁ 
f₂ : ι → α} {g : ι → β},   AntivaryOn f₁ g s → AntivaryOn f₂ g s → AntivaryOn (f
₁ * f₂) g s
参数：f₁ * f₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
@[to_additive] lemma AntivaryOn.mul_left (h₁ : AntivaryOn f₁ g s) (h₂ : AntivaryOn f₂ g s) :
    AntivaryOn (f₁ * f₂) g s := fun _i hi _j hj hij ↦ mul_le_mul' (h₁ hi hj hij) (h₂ hi hj hij)
/-
**MonovaryOn.div_left** 是 Mathlib 中的一个定理，位于命名空间 `MonovaryOn`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} [inst : CommGroup α] [inst_
1 : Preorder α] [IsOrderedMonoid α]   [inst_3 : PartialOrder β] {s : Set ι} {f₁ 
f₂ : ι → α} {g : ι → β},   MonovaryOn f₁ g s → AntivaryOn f₂ g s → MonovaryOn (f
₁ / f₂) g s
参数：f₁ / f₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `div_le_div''`：div_le_div'' (hab : a <= b) (hcd : c <= d) : a / d <= b / 
c
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
@[to_additive] lemma MonovaryOn.div_left (h₁ : MonovaryOn f₁ g s) (h₂ : AntivaryOn f₂ g s) :
    MonovaryOn (f₁ / f₂) g s := fun _i hi _j hj hij ↦ div_le_div'' (h₁ hi hj hij) (h₂ hi hj hij)
/-
**AntivaryOn.div_left** 是 Mathlib 中的一个定理，位于命名空间 `AntivaryOn`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} [inst : CommGroup α] [inst_
1 : Preorder α] [IsOrderedMonoid α]   [inst_3 : PartialOrder β] {s : Set ι} {f₁ 
f₂ : ι → α} {g : ι → β},   AntivaryOn f₁ g s → MonovaryOn f₂ g s → AntivaryOn (f
₁ / f₂) g s
参数：f₁ / f₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `div_le_div''`：div_le_div'' (hab : a <= b) (hcd : c <= d) : a / d <= b / 
c
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
@[to_additive] lemma AntivaryOn.div_left (h₁ : AntivaryOn f₁ g s) (h₂ : MonovaryOn f₂ g s) :
    AntivaryOn (f₁ / f₂) g s := fun _i hi _j hj hij ↦ div_le_div'' (h₁ hi hj hij) (h₂ hi hj hij)
/-
**MonovaryOn.pow_left** 是 Mathlib 中的一个定理，位于命名空间 `MonovaryOn`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} [inst : CommGroup α] [inst_
1 : Preorder α] [IsOrderedMonoid α]   [inst_3 : PartialOrder β] {s : Set ι} {f :
 ι → α} {g : ι → β}, MonovaryOn f g s → ∀ (n : ℕ), MonovaryOn (f ^ n) g s
参数：n : ℕ；f ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pow_le_pow_left'`：∀ {M : Type u_3} [inst : Monoid M] [inst_1 : Preorder 
M] [MulLeftMono M] [MulRightMono M] {a b : M},   a ≤ b → ∀ (i : ℕ), a ^ i ≤ b ^ 
i
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
@[to_additive] lemma MonovaryOn.pow_left (hfg : MonovaryOn f g s) (n : ℕ) :
    MonovaryOn (f ^ n) g s := fun _i hi _j hj hij ↦ pow_le_pow_left' (hfg hi hj hij) _
/-
**AntivaryOn.pow_left** 是 Mathlib 中的一个定理，位于命名空间 `AntivaryOn`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} [inst : CommGroup α] [inst_
1 : Preorder α] [IsOrderedMonoid α]   [inst_3 : PartialOrder β] {s : Set ι} {f :
 ι → α} {g : ι → β}, AntivaryOn f g s → ∀ (n : ℕ), AntivaryOn (f ^ n) g s
参数：n : ℕ；f ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pow_le_pow_left'`：∀ {M : Type u_3} [inst : Monoid M] [inst_1 : Preorder 
M] [MulLeftMono M] [MulRightMono M] {a b : M},   a ≤ b → ∀ (i : ℕ), a ^ i ≤ b ^ 
i
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
@[to_additive] lemma AntivaryOn.pow_left (hfg : AntivaryOn f g s) (n : ℕ) :
    AntivaryOn (f ^ n) g s := fun _i hi _j hj hij ↦ pow_le_pow_left' (hfg hi hj hij) _

@[to_additive]
/-
**Monovary.mul_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Monovary.mul_left (h₁ : Monovary f₁ g) (h₂ : Monovary f₂ g) : Monovary (f₁
 * f₂) g
参数：h₁ : Monovary f₁ g；h₂ : Monovary f₂ g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
lemma Monovary.mul_left (h₁ : Monovary f₁ g) (h₂ : Monovary f₂ g) : Monovary (f₁ * f₂) g :=
  fun _i _j hij ↦ mul_le_mul' (h₁ hij) (h₂ hij)

@[to_additive]
/-
**Antivary.mul_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Antivary.mul_left (h₁ : Antivary f₁ g) (h₂ : Antivary f₂ g) : Antivary (f₁
 * f₂) g
参数：h₁ : Antivary f₁ g；h₂ : Antivary f₂ g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
lemma Antivary.mul_left (h₁ : Antivary f₁ g) (h₂ : Antivary f₂ g) : Antivary (f₁ * f₂) g :=
  fun _i _j hij ↦ mul_le_mul' (h₁ hij) (h₂ hij)

@[to_additive]
/-
**Monovary.div_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Monovary.div_left (h₁ : Monovary f₁ g) (h₂ : Antivary f₂ g) : Monovary (f₁
 / f₂) g
参数：h₁ : Monovary f₁ g；h₂ : Antivary f₂ g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `div_le_div''`：div_le_div'' (hab : a <= b) (hcd : c <= d) : a / d <= b / 
c
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
lemma Monovary.div_left (h₁ : Monovary f₁ g) (h₂ : Antivary f₂ g) : Monovary (f₁ / f₂) g :=
  fun _i _j hij ↦ div_le_div'' (h₁ hij) (h₂ hij)

@[to_additive]
/-
**Antivary.div_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Antivary.div_left (h₁ : Antivary f₁ g) (h₂ : Monovary f₂ g) : Antivary (f₁
 / f₂) g
参数：h₁ : Antivary f₁ g；h₂ : Monovary f₂ g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `div_le_div''`：div_le_div'' (hab : a <= b) (hcd : c <= d) : a / d <= b / 
c
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
lemma Antivary.div_left (h₁ : Antivary f₁ g) (h₂ : Monovary f₂ g) : Antivary (f₁ / f₂) g :=
  fun _i _j hij ↦ div_le_div'' (h₁ hij) (h₂ hij)
/-
**Monovary.pow_left** 是 Mathlib 中的一个定理，位于命名空间 `Monovary`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} [inst : CommGroup α] [inst_
1 : Preorder α] [IsOrderedMonoid α]   [inst_3 : PartialOrder β] {f : ι → α} {g :
 ι → β}, Monovary f g → ∀ (n : ℕ), Monovary (f ^ n) g
参数：n : ℕ；f ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pow_le_pow_left'`：∀ {M : Type u_3} [inst : Monoid M] [inst_1 : Preorder 
M] [MulLeftMono M] [MulRightMono M] {a b : M},   a ≤ b → ∀ (i : ℕ), a ^ i ≤ b ^ 
i
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
@[to_additive] lemma Monovary.pow_left (hfg : Monovary f g) (n : ℕ) : Monovary (f ^ n) g :=
  fun _i _j hij ↦ pow_le_pow_left' (hfg hij) _
/-
**Antivary.pow_left** 是 Mathlib 中的一个定理，位于命名空间 `Antivary`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} [inst : CommGroup α] [inst_
1 : Preorder α] [IsOrderedMonoid α]   [inst_3 : PartialOrder β] {f : ι → α} {g :
 ι → β}, Antivary f g → ∀ (n : ℕ), Antivary (f ^ n) g
参数：n : ℕ；f ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pow_le_pow_left'`：∀ {M : Type u_3} [inst : Monoid M] [inst_1 : Preorder 
M] [MulLeftMono M] [MulRightMono M] {a b : M},   a ≤ b → ∀ (i : ℕ), a ^ i ≤ b ^ 
i
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
@[to_additive] lemma Antivary.pow_left (hfg : Antivary f g) (n : ℕ) : Antivary (f ^ n) g :=
  fun _i _j hij ↦ pow_le_pow_left' (hfg hij) _

end

section
variable [PartialOrder α] [CommGroup β] [PartialOrder β] [IsOrderedMonoid β]
  {s : Set ι} {f f₁ f₂ : ι → α} {g : ι → β}

@[to_additive (attr := simp)]
/-
**monovaryOn_inv_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：monovaryOn_inv_right : MonovaryOn f g⁻¹ s ↔ AntivaryOn f g s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `instIsRightCancelMulOfMulRightReflectLE`：∀ {α : Type u_1} [inst : Mul α]
 [inst_1 : PartialOrder α] [MulRightReflectLE α], IsRightCancelMul α
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `IsOrderedCancelMonoid.toMulLeftReflectLT`：∀ {α : Type u_1} [inst : CommM
onoid α] [inst_1 : PartialOrder α] [IsOrderedCancelMonoid α], MulLeftReflectLT α
· 使用定理 `IsOrderedMonoid.toIsOrderedCancelMonoid`：∀ {α : Type u} [inst : CommGrou
p α] [inst_1 : Preorder α] [IsOrderedMonoid α], IsOrderedCancelMonoid α
· 使用定理 `forall₂_comm`：forall₂_comm {ι₁ ι₂ : Sort*} {κ₁ : ι₁ -> Sort*} {κ₂ : ι₂ -
> Sort*} {p : forall i₁, κ₁ i₁ -> forall i₂, κ₂ i₂ -> Prop} : (forall i₁ j₁ i₂ j
₂,…
-/
lemma monovaryOn_inv_right : MonovaryOn f g⁻¹ s ↔ AntivaryOn f g s := by
  simpa [MonovaryOn, AntivaryOn] using forall₂_comm

@[to_additive (attr := simp)]
/-
**antivaryOn_inv_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：antivaryOn_inv_right : AntivaryOn f g⁻¹ s ↔ MonovaryOn f g s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `instIsRightCancelMulOfMulRightReflectLE`：∀ {α : Type u_1} [inst : Mul α]
 [inst_1 : PartialOrder α] [MulRightReflectLE α], IsRightCancelMul α
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `IsOrderedCancelMonoid.toMulLeftReflectLT`：∀ {α : Type u_1} [inst : CommM
onoid α] [inst_1 : PartialOrder α] [IsOrderedCancelMonoid α], MulLeftReflectLT α
· 使用定理 `IsOrderedMonoid.toIsOrderedCancelMonoid`：∀ {α : Type u} [inst : CommGrou
p α] [inst_1 : Preorder α] [IsOrderedMonoid α], IsOrderedCancelMonoid α
· 使用定理 `forall₂_comm`：forall₂_comm {ι₁ ι₂ : Sort*} {κ₁ : ι₁ -> Sort*} {κ₂ : ι₂ -
> Sort*} {p : forall i₁, κ₁ i₁ -> forall i₂, κ₂ i₂ -> Prop} : (forall i₁ j₁ i₂ j
₂,…
-/
lemma antivaryOn_inv_right : AntivaryOn f g⁻¹ s ↔ MonovaryOn f g s := by
  simpa [MonovaryOn, AntivaryOn] using forall₂_comm
/-
**monovary_inv_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} [inst : PartialOrder α] [in
st_1 : CommGroup β] [inst_2 : PartialOrder β]   [IsOrderedMonoid β] {f : ι → α} 
{g : ι → β}, Monovary f g⁻¹ ↔ Antivary f g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `instIsRightCancelMulOfMulRightReflectLE`：∀ {α : Type u_1} [inst : Mul α]
 [inst_1 : PartialOrder α] [MulRightReflectLE α], IsRightCancelMul α
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `IsOrderedCancelMonoid.toMulLeftReflectLT`：∀ {α : Type u_1} [inst : CommM
onoid α] [inst_1 : PartialOrder α] [IsOrderedCancelMonoid α], MulLeftReflectLT α
· 使用定理 `IsOrderedMonoid.toIsOrderedCancelMonoid`：∀ {α : Type u} [inst : CommGrou
p α] [inst_1 : Preorder α] [IsOrderedMonoid α], IsOrderedCancelMonoid α
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
-/
@[to_additive (attr := simp)] lemma monovary_inv_right : Monovary f g⁻¹ ↔ Antivary f g := by
  simpa [Monovary, Antivary] using forall_comm
/-
**antivary_inv_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} [inst : PartialOrder α] [in
st_1 : CommGroup β] [inst_2 : PartialOrder β]   [IsOrderedMonoid β] {f : ι → α} 
{g : ι → β}, Antivary f g⁻¹ ↔ Monovary f g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `instIsRightCancelMulOfMulRightReflectLE`：∀ {α : Type u_1} [inst : Mul α]
 [inst_1 : PartialOrder α] [MulRightReflectLE α], IsRightCancelMul α
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `IsOrderedCancelMonoid.toMulLeftReflectLT`：∀ {α : Type u_1} [inst : CommM
onoid α] [inst_1 : PartialOrder α] [IsOrderedCancelMonoid α], MulLeftReflectLT α
· 使用定理 `IsOrderedMonoid.toIsOrderedCancelMonoid`：∀ {α : Type u} [inst : CommGrou
p α] [inst_1 : Preorder α] [IsOrderedMonoid α], IsOrderedCancelMonoid α
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
-/
@[to_additive (attr := simp)] lemma antivary_inv_right : Antivary f g⁻¹ ↔ Monovary f g := by
  simpa [Monovary, Antivary] using forall_comm
end

section
variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α]
  [CommGroup β] [PartialOrder β] [IsOrderedMonoid β]
  {s : Set ι} {f f₁ f₂ : ι → α} {g : ι → β}

/-
**monovaryOn_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} [inst : CommGroup α] [inst_
1 : PartialOrder α] [IsOrderedMonoid α]   [inst_3 : CommGroup β] [inst_4 : Parti
alOrder β] [IsOrderedMonoid β] {s : Set ι} {f : ι → α} {g : ι → β},   MonovaryOn
 f⁻¹ g⁻¹ s ↔ MonovaryOn f g s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[to_additive] lemma monovaryOn_inv : MonovaryOn f⁻¹ g⁻¹ s ↔ MonovaryOn f g s := by simp
/-
**antivaryOn_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} [inst : CommGroup α] [inst_
1 : PartialOrder α] [IsOrderedMonoid α]   [inst_3 : CommGroup β] [inst_4 : Parti
alOrder β] [IsOrderedMonoid β] {s : Set ι} {f : ι → α} {g : ι → β},   AntivaryOn
 f⁻¹ g⁻¹ s ↔ AntivaryOn f g s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[to_additive] lemma antivaryOn_inv : AntivaryOn f⁻¹ g⁻¹ s ↔ AntivaryOn f g s := by simp
/-
**monovary_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} [inst : CommGroup α] [inst_
1 : PartialOrder α] [IsOrderedMonoid α]   [inst_3 : CommGroup β] [inst_4 : Parti
alOrder β] [IsOrderedMonoid β] {f : ι → α} {g : ι → β},   Monovary f⁻¹ g⁻¹ ↔ Mon
ovary f g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[to_additive] lemma monovary_inv : Monovary f⁻¹ g⁻¹ ↔ Monovary f g := by simp
/-
**antivary_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} [inst : CommGroup α] [inst_
1 : PartialOrder α] [IsOrderedMonoid α]   [inst_3 : CommGroup β] [inst_4 : Parti
alOrder β] [IsOrderedMonoid β] {f : ι → α} {g : ι → β},   Antivary f⁻¹ g⁻¹ ↔ Ant
ivary f g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[to_additive] lemma antivary_inv : Antivary f⁻¹ g⁻¹ ↔ Antivary f g := by simp

end

@[to_additive] alias ⟨MonovaryOn.of_inv_left, AntivaryOn.inv_left⟩ := monovaryOn_inv_left
@[to_additive] alias ⟨AntivaryOn.of_inv_left, MonovaryOn.inv_left⟩ := antivaryOn_inv_left
@[to_additive] alias ⟨MonovaryOn.of_inv_right, AntivaryOn.inv_right⟩ := monovaryOn_inv_right
@[to_additive] alias ⟨AntivaryOn.of_inv_right, MonovaryOn.inv_right⟩ := antivaryOn_inv_right
@[to_additive] alias ⟨MonovaryOn.of_inv, MonovaryOn.inv⟩ := monovaryOn_inv
@[to_additive] alias ⟨AntivaryOn.of_inv, AntivaryOn.inv⟩ := antivaryOn_inv
@[to_additive] alias ⟨Monovary.of_inv_left, Antivary.inv_left⟩ := monovary_inv_left
@[to_additive] alias ⟨Antivary.of_inv_left, Monovary.inv_left⟩ := antivary_inv_left
@[to_additive] alias ⟨Monovary.of_inv_right, Antivary.inv_right⟩ := monovary_inv_right
@[to_additive] alias ⟨Antivary.of_inv_right, Monovary.inv_right⟩ := antivary_inv_right
@[to_additive] alias ⟨Monovary.of_inv, Monovary.inv⟩ := monovary_inv
@[to_additive] alias ⟨Antivary.of_inv, Antivary.inv⟩ := antivary_inv

end OrderedCommGroup

section LinearOrderedCommGroup
variable [Preorder α] [CommGroup β] [LinearOrder β] [IsOrderedMonoid β] {s : Set ι} {f : ι → α}
  {g g₁ g₂ : ι → β}

/-
**MonovaryOn.mul_right** 是 Mathlib 中的一个定理，位于命名空间 `MonovaryOn`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst_1
 : CommGroup β] [inst_2 : LinearOrder β]   [IsOrderedMonoid β] {s : Set ι} {f : 
ι → α} {g₁ g₂ : ι → β},   MonovaryOn f g₁ s → MonovaryOn f g₂ s → MonovaryOn f (
g₁ * g₂) s
参数：g₁ * g₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `lt_or_lt_of_mul_lt_mul`：lt_or_lt_of_mul_lt_mul [MulLeftMono α] [MulRight
Mono α] {a₁ a₂ b₁ b₂ : α} : a₁ * b₁ < a₂ * b₂ -> a₁ < a₂ ∨ b₁ < b₂
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
@[to_additive] lemma MonovaryOn.mul_right (h₁ : MonovaryOn f g₁ s) (h₂ : MonovaryOn f g₂ s) :
    MonovaryOn f (g₁ * g₂) s :=
  fun _i hi _j hj hij ↦ (lt_or_lt_of_mul_lt_mul hij).elim (h₁ hi hj) <| h₂ hi hj
/-
**AntivaryOn.mul_right** 是 Mathlib 中的一个定理，位于命名空间 `AntivaryOn`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst_1
 : CommGroup β] [inst_2 : LinearOrder β]   [IsOrderedMonoid β] {s : Set ι} {f : 
ι → α} {g₁ g₂ : ι → β},   AntivaryOn f g₁ s → AntivaryOn f g₂ s → AntivaryOn f (
g₁ * g₂) s
参数：g₁ * g₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `lt_or_lt_of_mul_lt_mul`：lt_or_lt_of_mul_lt_mul [MulLeftMono α] [MulRight
Mono α] {a₁ a₂ b₁ b₂ : α} : a₁ * b₁ < a₂ * b₂ -> a₁ < a₂ ∨ b₁ < b₂
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
@[to_additive] lemma AntivaryOn.mul_right (h₁ : AntivaryOn f g₁ s) (h₂ : AntivaryOn f g₂ s) :
    AntivaryOn f (g₁ * g₂) s :=
  fun _i hi _j hj hij ↦ (lt_or_lt_of_mul_lt_mul hij).elim (h₁ hi hj) <| h₂ hi hj
/-
**MonovaryOn.div_right** 是 Mathlib 中的一个定理，位于命名空间 `MonovaryOn`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst_1
 : CommGroup β] [inst_2 : LinearOrder β]   [IsOrderedMonoid β] {s : Set ι} {f : 
ι → α} {g₁ g₂ : ι → β},   MonovaryOn f g₁ s → AntivaryOn f g₂ s → MonovaryOn f (
g₁ / g₂) s
参数：g₁ / g₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `lt_or_lt_of_div_lt_div`：∀ {α : Type u} [inst : CommGroup α] [inst_1 : Li
nearOrder α] [MulLeftMono α] {a b c d : α},   a / d < b / c → a < b ∨ c < d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
@[to_additive] lemma MonovaryOn.div_right (h₁ : MonovaryOn f g₁ s) (h₂ : AntivaryOn f g₂ s) :
    MonovaryOn f (g₁ / g₂) s :=
  fun _i hi _j hj hij ↦ (lt_or_lt_of_div_lt_div hij).elim (h₁ hi hj) <| h₂ hj hi
/-
**AntivaryOn.div_right** 是 Mathlib 中的一个定理，位于命名空间 `AntivaryOn`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst_1
 : CommGroup β] [inst_2 : LinearOrder β]   [IsOrderedMonoid β] {s : Set ι} {f : 
ι → α} {g₁ g₂ : ι → β},   AntivaryOn f g₁ s → MonovaryOn f g₂ s → AntivaryOn f (
g₁ / g₂) s
参数：g₁ / g₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `lt_or_lt_of_div_lt_div`：∀ {α : Type u} [inst : CommGroup α] [inst_1 : Li
nearOrder α] [MulLeftMono α] {a b c d : α},   a / d < b / c → a < b ∨ c < d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
@[to_additive] lemma AntivaryOn.div_right (h₁ : AntivaryOn f g₁ s) (h₂ : MonovaryOn f g₂ s) :
    AntivaryOn f (g₁ / g₂) s :=
  fun _i hi _j hj hij ↦ (lt_or_lt_of_div_lt_div hij).elim (h₁ hi hj) <| h₂ hj hi
/-
**MonovaryOn.pow_right** 是 Mathlib 中的一个定理，位于命名空间 `MonovaryOn`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst_1
 : CommGroup β] [inst_2 : LinearOrder β]   [IsOrderedMonoid β] {s : Set ι} {f : 
ι → α} {g : ι → β}, MonovaryOn f g s → ∀ (n : ℕ), MonovaryOn f (g ^ n) s
参数：n : ℕ；g ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_pow_lt_pow_left'`：lt_of_pow_lt_pow_left' {a b : M} (n : Nat) : a ^
 n < b ^ n -> a < b
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
@[to_additive] lemma MonovaryOn.pow_right (hfg : MonovaryOn f g s) (n : ℕ) :
    MonovaryOn f (g ^ n) s := fun _i hi _j hj hij ↦ hfg hi hj <| lt_of_pow_lt_pow_left' _ hij
/-
**AntivaryOn.pow_right** 是 Mathlib 中的一个定理，位于命名空间 `AntivaryOn`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst_1
 : CommGroup β] [inst_2 : LinearOrder β]   [IsOrderedMonoid β] {s : Set ι} {f : 
ι → α} {g : ι → β}, AntivaryOn f g s → ∀ (n : ℕ), AntivaryOn f (g ^ n) s
参数：n : ℕ；g ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_pow_lt_pow_left'`：lt_of_pow_lt_pow_left' {a b : M} (n : Nat) : a ^
 n < b ^ n -> a < b
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
@[to_additive] lemma AntivaryOn.pow_right (hfg : AntivaryOn f g s) (n : ℕ) :
    AntivaryOn f (g ^ n) s := fun _i hi _j hj hij ↦ hfg hi hj <| lt_of_pow_lt_pow_left' _ hij
/-
**Monovary.mul_right** 是 Mathlib 中的一个定理，位于命名空间 `Monovary`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst_1
 : CommGroup β] [inst_2 : LinearOrder β]   [IsOrderedMonoid β] {f : ι → α} {g₁ g
₂ : ι → β}, Monovary f g₁ → Monovary f g₂ → Monovary f (g₁ * g₂)
参数：g₁ * g₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `lt_or_lt_of_mul_lt_mul`：lt_or_lt_of_mul_lt_mul [MulLeftMono α] [MulRight
Mono α] {a₁ a₂ b₁ b₂ : α} : a₁ * b₁ < a₂ * b₂ -> a₁ < a₂ ∨ b₁ < b₂
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
@[to_additive] lemma Monovary.mul_right (h₁ : Monovary f g₁) (h₂ : Monovary f g₂) :
    Monovary f (g₁ * g₂) :=
  fun _i _j hij ↦ (lt_or_lt_of_mul_lt_mul hij).elim (fun h ↦ h₁ h) fun h ↦ h₂ h
/-
**Antivary.mul_right** 是 Mathlib 中的一个定理，位于命名空间 `Antivary`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst_1
 : CommGroup β] [inst_2 : LinearOrder β]   [IsOrderedMonoid β] {f : ι → α} {g₁ g
₂ : ι → β}, Antivary f g₁ → Antivary f g₂ → Antivary f (g₁ * g₂)
参数：g₁ * g₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `lt_or_lt_of_mul_lt_mul`：lt_or_lt_of_mul_lt_mul [MulLeftMono α] [MulRight
Mono α] {a₁ a₂ b₁ b₂ : α} : a₁ * b₁ < a₂ * b₂ -> a₁ < a₂ ∨ b₁ < b₂
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
@[to_additive] lemma Antivary.mul_right (h₁ : Antivary f g₁) (h₂ : Antivary f g₂) :
    Antivary f (g₁ * g₂) :=
  fun _i _j hij ↦ (lt_or_lt_of_mul_lt_mul hij).elim (fun h ↦ h₁ h) fun h ↦ h₂ h
/-
**Monovary.div_right** 是 Mathlib 中的一个定理，位于命名空间 `Monovary`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst_1
 : CommGroup β] [inst_2 : LinearOrder β]   [IsOrderedMonoid β] {f : ι → α} {g₁ g
₂ : ι → β}, Monovary f g₁ → Antivary f g₂ → Monovary f (g₁ / g₂)
参数：g₁ / g₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `lt_or_lt_of_div_lt_div`：∀ {α : Type u} [inst : CommGroup α] [inst_1 : Li
nearOrder α] [MulLeftMono α] {a b c d : α},   a / d < b / c → a < b ∨ c < d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
@[to_additive] lemma Monovary.div_right (h₁ : Monovary f g₁) (h₂ : Antivary f g₂) :
    Monovary f (g₁ / g₂) :=
  fun _i _j hij ↦ (lt_or_lt_of_div_lt_div hij).elim (fun h ↦ h₁ h) fun h ↦ h₂ h
/-
**Antivary.div_right** 是 Mathlib 中的一个定理，位于命名空间 `Antivary`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst_1
 : CommGroup β] [inst_2 : LinearOrder β]   [IsOrderedMonoid β] {f : ι → α} {g₁ g
₂ : ι → β}, Antivary f g₁ → Monovary f g₂ → Antivary f (g₁ / g₂)
参数：g₁ / g₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `lt_or_lt_of_div_lt_div`：∀ {α : Type u} [inst : CommGroup α] [inst_1 : Li
nearOrder α] [MulLeftMono α] {a b c d : α},   a / d < b / c → a < b ∨ c < d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
@[to_additive] lemma Antivary.div_right (h₁ : Antivary f g₁) (h₂ : Monovary f g₂) :
    Antivary f (g₁ / g₂) :=
  fun _i _j hij ↦ (lt_or_lt_of_div_lt_div hij).elim (fun h ↦ h₁ h) fun h ↦ h₂ h
/-
**Monovary.pow_right** 是 Mathlib 中的一个定理，位于命名空间 `Monovary`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst_1
 : CommGroup β] [inst_2 : LinearOrder β]   [IsOrderedMonoid β] {f : ι → α} {g : 
ι → β}, Monovary f g → ∀ (n : ℕ), Monovary f (g ^ n)
参数：n : ℕ；g ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_pow_lt_pow_left'`：lt_of_pow_lt_pow_left' {a b : M} (n : Nat) : a ^
 n < b ^ n -> a < b
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
@[to_additive] lemma Monovary.pow_right (hfg : Monovary f g) (n : ℕ) : Monovary f (g ^ n) :=
  fun _i _j hij ↦ hfg <| lt_of_pow_lt_pow_left' _ hij
/-
**Antivary.pow_right** 是 Mathlib 中的一个定理，位于命名空间 `Antivary`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst_1
 : CommGroup β] [inst_2 : LinearOrder β]   [IsOrderedMonoid β] {f : ι → α} {g : 
ι → β}, Antivary f g → ∀ (n : ℕ), Antivary f (g ^ n)
参数：n : ℕ；g ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_pow_lt_pow_left'`：lt_of_pow_lt_pow_left' {a b : M} (n : Nat) : a ^
 n < b ^ n -> a < b
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
@[to_additive] lemma Antivary.pow_right (hfg : Antivary f g) (n : ℕ) : Antivary f (g ^ n) :=
  fun _i _j hij ↦ hfg <| lt_of_pow_lt_pow_left' _ hij

end LinearOrderedCommGroup

section OrderedSemiring
variable [Semiring α] [PartialOrder α] [IsOrderedRing α] [PartialOrder β]
  {s : Set ι} {f f₁ f₂ : ι → α} {g : ι → β}

/-
**MonovaryOn.mul_left** 是 Mathlib 中的一个定理，位于命名空间 `MonovaryOn`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} [inst : CommGroup α] [inst_
1 : Preorder α] [IsOrderedMonoid α]   [inst_3 : PartialOrder β] {s : Set ι} {f₁ 
f₂ : ι → α} {g : ι → β},   MonovaryOn f₁ g s → MonovaryOn f₂ g s → MonovaryOn (f
₁ * f₂) g s
参数：f₁ * f₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
lemma MonovaryOn.mul_left₀ (hf₁ : ∀ i ∈ s, 0 ≤ f₁ i) (hf₂ : ∀ i ∈ s, 0 ≤ f₂ i)
    (h₁ : MonovaryOn f₁ g s) (h₂ : MonovaryOn f₂ g s) : MonovaryOn (f₁ * f₂) g s :=
  fun _i hi _j hj hij ↦ mul_le_mul (h₁ hi hj hij) (h₂ hi hj hij) (hf₂ _ hi) (hf₁ _ hj)
/-
**AntivaryOn.mul_left** 是 Mathlib 中的一个定理，位于命名空间 `AntivaryOn`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} [inst : CommGroup α] [inst_
1 : Preorder α] [IsOrderedMonoid α]   [inst_3 : PartialOrder β] {s : Set ι} {f₁ 
f₂ : ι → α} {g : ι → β},   AntivaryOn f₁ g s → AntivaryOn f₂ g s → AntivaryOn (f
₁ * f₂) g s
参数：f₁ * f₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
lemma AntivaryOn.mul_left₀ (hf₁ : ∀ i ∈ s, 0 ≤ f₁ i) (hf₂ : ∀ i ∈ s, 0 ≤ f₂ i)
    (h₁ : AntivaryOn f₁ g s) (h₂ : AntivaryOn f₂ g s) : AntivaryOn (f₁ * f₂) g s :=
  fun _i hi _j hj hij ↦ mul_le_mul (h₁ hi hj hij) (h₂ hi hj hij) (hf₂ _ hj) (hf₁ _ hi)
/-
**MonovaryOn.pow_left** 是 Mathlib 中的一个定理，位于命名空间 `MonovaryOn`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} [inst : CommGroup α] [inst_
1 : Preorder α] [IsOrderedMonoid α]   [inst_3 : PartialOrder β] {s : Set ι} {f :
 ι → α} {g : ι → β}, MonovaryOn f g s → ∀ (n : ℕ), MonovaryOn (f ^ n) g s
参数：n : ℕ；f ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pow_le_pow_left'`：∀ {M : Type u_3} [inst : Monoid M] [inst_1 : Preorder 
M] [MulLeftMono M] [MulRightMono M] {a b : M},   a ≤ b → ∀ (i : ℕ), a ^ i ≤ b ^ 
i
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
lemma MonovaryOn.pow_left₀ (hf : ∀ i ∈ s, 0 ≤ f i) (hfg : MonovaryOn f g s) (n : ℕ) :
    MonovaryOn (f ^ n) g s :=
  fun _i hi _j hj hij ↦ pow_le_pow_left₀ (hf _ hi) (hfg hi hj hij) _
/-
**AntivaryOn.pow_left** 是 Mathlib 中的一个定理，位于命名空间 `AntivaryOn`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} [inst : CommGroup α] [inst_
1 : Preorder α] [IsOrderedMonoid α]   [inst_3 : PartialOrder β] {s : Set ι} {f :
 ι → α} {g : ι → β}, AntivaryOn f g s → ∀ (n : ℕ), AntivaryOn (f ^ n) g s
参数：n : ℕ；f ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pow_le_pow_left'`：∀ {M : Type u_3} [inst : Monoid M] [inst_1 : Preorder 
M] [MulLeftMono M] [MulRightMono M] {a b : M},   a ≤ b → ∀ (i : ℕ), a ^ i ≤ b ^ 
i
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
lemma AntivaryOn.pow_left₀ (hf : ∀ i ∈ s, 0 ≤ f i) (hfg : AntivaryOn f g s) (n : ℕ) :
    AntivaryOn (f ^ n) g s :=
  fun _i hi _j hj hij ↦ pow_le_pow_left₀ (hf _ hj) (hfg hi hj hij) _
/-
**Monovary.mul_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Monovary.mul_left (h₁ : Monovary f₁ g) (h₂ : Monovary f₂ g) : Monovary (f₁
 * f₂) g
参数：h₁ : Monovary f₁ g；h₂ : Monovary f₂ g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
lemma Monovary.mul_left₀ (hf₁ : 0 ≤ f₁) (hf₂ : 0 ≤ f₂) (h₁ : Monovary f₁ g) (h₂ : Monovary f₂ g) :
    Monovary (f₁ * f₂) g := fun _i _j hij ↦ mul_le_mul (h₁ hij) (h₂ hij) (hf₂ _) (hf₁ _)
/-
**Antivary.mul_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Antivary.mul_left (h₁ : Antivary f₁ g) (h₂ : Antivary f₂ g) : Antivary (f₁
 * f₂) g
参数：h₁ : Antivary f₁ g；h₂ : Antivary f₂ g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
lemma Antivary.mul_left₀ (hf₁ : 0 ≤ f₁) (hf₂ : 0 ≤ f₂) (h₁ : Antivary f₁ g) (h₂ : Antivary f₂ g) :
    Antivary (f₁ * f₂) g := fun _i _j hij ↦ mul_le_mul (h₁ hij) (h₂ hij) (hf₂ _) (hf₁ _)
/-
**Monovary.pow_left** 是 Mathlib 中的一个定理，位于命名空间 `Monovary`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} [inst : CommGroup α] [inst_
1 : Preorder α] [IsOrderedMonoid α]   [inst_3 : PartialOrder β] {f : ι → α} {g :
 ι → β}, Monovary f g → ∀ (n : ℕ), Monovary (f ^ n) g
参数：n : ℕ；f ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pow_le_pow_left'`：∀ {M : Type u_3} [inst : Monoid M] [inst_1 : Preorder 
M] [MulLeftMono M] [MulRightMono M] {a b : M},   a ≤ b → ∀ (i : ℕ), a ^ i ≤ b ^ 
i
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
lemma Monovary.pow_left₀ (hf : 0 ≤ f) (hfg : Monovary f g) (n : ℕ) : Monovary (f ^ n) g :=
  fun _i _j hij ↦ pow_le_pow_left₀ (hf _) (hfg hij) _
/-
**Antivary.pow_left** 是 Mathlib 中的一个定理，位于命名空间 `Antivary`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} [inst : CommGroup α] [inst_
1 : Preorder α] [IsOrderedMonoid α]   [inst_3 : PartialOrder β] {f : ι → α} {g :
 ι → β}, Antivary f g → ∀ (n : ℕ), Antivary (f ^ n) g
参数：n : ℕ；f ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pow_le_pow_left'`：∀ {M : Type u_3} [inst : Monoid M] [inst_1 : Preorder 
M] [MulLeftMono M] [MulRightMono M] {a b : M},   a ≤ b → ∀ (i : ℕ), a ^ i ≤ b ^ 
i
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
lemma Antivary.pow_left₀ (hf : 0 ≤ f) (hfg : Antivary f g) (n : ℕ) : Antivary (f ^ n) g :=
  fun _i _j hij ↦ pow_le_pow_left₀ (hf _) (hfg hij) _

end OrderedSemiring

section LinearOrderedSemiring
variable [LinearOrder α] [Semiring β] [LinearOrder β] [IsStrictOrderedRing β]
  {s : Set ι} {f : ι → α} {g g₁ g₂ : ι → β}

/-
**MonovaryOn.mul_right** 是 Mathlib 中的一个定理，位于命名空间 `MonovaryOn`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst_1
 : CommGroup β] [inst_2 : LinearOrder β]   [IsOrderedMonoid β] {s : Set ι} {f : 
ι → α} {g₁ g₂ : ι → β},   MonovaryOn f g₁ s → MonovaryOn f g₂ s → MonovaryOn f (
g₁ * g₂) s
参数：g₁ * g₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `lt_or_lt_of_mul_lt_mul`：lt_or_lt_of_mul_lt_mul [MulLeftMono α] [MulRight
Mono α] {a₁ a₂ b₁ b₂ : α} : a₁ * b₁ < a₂ * b₂ -> a₁ < a₂ ∨ b₁ < b₂
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
lemma MonovaryOn.mul_right₀ (hg₁ : ∀ i ∈ s, 0 ≤ g₁ i) (hg₂ : ∀ i ∈ s, 0 ≤ g₂ i)
    (h₁ : MonovaryOn f g₁ s) (h₂ : MonovaryOn f g₂ s) : MonovaryOn f (g₁ * g₂) s :=
  (h₁.symm.mul_left₀ hg₁ hg₂ h₂.symm).symm
/-
**AntivaryOn.mul_right** 是 Mathlib 中的一个定理，位于命名空间 `AntivaryOn`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst_1
 : CommGroup β] [inst_2 : LinearOrder β]   [IsOrderedMonoid β] {s : Set ι} {f : 
ι → α} {g₁ g₂ : ι → β},   AntivaryOn f g₁ s → AntivaryOn f g₂ s → AntivaryOn f (
g₁ * g₂) s
参数：g₁ * g₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `lt_or_lt_of_mul_lt_mul`：lt_or_lt_of_mul_lt_mul [MulLeftMono α] [MulRight
Mono α] {a₁ a₂ b₁ b₂ : α} : a₁ * b₁ < a₂ * b₂ -> a₁ < a₂ ∨ b₁ < b₂
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
lemma AntivaryOn.mul_right₀ (hg₁ : ∀ i ∈ s, 0 ≤ g₁ i) (hg₂ : ∀ i ∈ s, 0 ≤ g₂ i)
    (h₁ : AntivaryOn f g₁ s) (h₂ : AntivaryOn f g₂ s) : AntivaryOn f (g₁ * g₂) s :=
  (h₁.symm.mul_left₀ hg₁ hg₂ h₂.symm).symm
/-
**MonovaryOn.pow_right** 是 Mathlib 中的一个定理，位于命名空间 `MonovaryOn`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst_1
 : CommGroup β] [inst_2 : LinearOrder β]   [IsOrderedMonoid β] {s : Set ι} {f : 
ι → α} {g : ι → β}, MonovaryOn f g s → ∀ (n : ℕ), MonovaryOn f (g ^ n) s
参数：n : ℕ；g ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_pow_lt_pow_left'`：lt_of_pow_lt_pow_left' {a b : M} (n : Nat) : a ^
 n < b ^ n -> a < b
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
lemma MonovaryOn.pow_right₀ (hg : ∀ i ∈ s, 0 ≤ g i) (hfg : MonovaryOn f g s) (n : ℕ) :
    MonovaryOn f (g ^ n) s := (hfg.symm.pow_left₀ hg _).symm
/-
**AntivaryOn.pow_right** 是 Mathlib 中的一个定理，位于命名空间 `AntivaryOn`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst_1
 : CommGroup β] [inst_2 : LinearOrder β]   [IsOrderedMonoid β] {s : Set ι} {f : 
ι → α} {g : ι → β}, AntivaryOn f g s → ∀ (n : ℕ), AntivaryOn f (g ^ n) s
参数：n : ℕ；g ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_pow_lt_pow_left'`：lt_of_pow_lt_pow_left' {a b : M} (n : Nat) : a ^
 n < b ^ n -> a < b
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
lemma AntivaryOn.pow_right₀ (hg : ∀ i ∈ s, 0 ≤ g i) (hfg : AntivaryOn f g s) (n : ℕ) :
    AntivaryOn f (g ^ n) s := (hfg.symm.pow_left₀ hg _).symm
/-
**Monovary.mul_right** 是 Mathlib 中的一个定理，位于命名空间 `Monovary`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst_1
 : CommGroup β] [inst_2 : LinearOrder β]   [IsOrderedMonoid β] {f : ι → α} {g₁ g
₂ : ι → β}, Monovary f g₁ → Monovary f g₂ → Monovary f (g₁ * g₂)
参数：g₁ * g₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `lt_or_lt_of_mul_lt_mul`：lt_or_lt_of_mul_lt_mul [MulLeftMono α] [MulRight
Mono α] {a₁ a₂ b₁ b₂ : α} : a₁ * b₁ < a₂ * b₂ -> a₁ < a₂ ∨ b₁ < b₂
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
lemma Monovary.mul_right₀ (hg₁ : 0 ≤ g₁) (hg₂ : 0 ≤ g₂) (h₁ : Monovary f g₁) (h₂ : Monovary f g₂) :
    Monovary f (g₁ * g₂) := (h₁.symm.mul_left₀ hg₁ hg₂ h₂.symm).symm
/-
**Antivary.mul_right** 是 Mathlib 中的一个定理，位于命名空间 `Antivary`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst_1
 : CommGroup β] [inst_2 : LinearOrder β]   [IsOrderedMonoid β] {f : ι → α} {g₁ g
₂ : ι → β}, Antivary f g₁ → Antivary f g₂ → Antivary f (g₁ * g₂)
参数：g₁ * g₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `lt_or_lt_of_mul_lt_mul`：lt_or_lt_of_mul_lt_mul [MulLeftMono α] [MulRight
Mono α] {a₁ a₂ b₁ b₂ : α} : a₁ * b₁ < a₂ * b₂ -> a₁ < a₂ ∨ b₁ < b₂
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
lemma Antivary.mul_right₀ (hg₁ : 0 ≤ g₁) (hg₂ : 0 ≤ g₂) (h₁ : Antivary f g₁) (h₂ : Antivary f g₂) :
    Antivary f (g₁ * g₂) := (h₁.symm.mul_left₀ hg₁ hg₂ h₂.symm).symm
/-
**Monovary.pow_right** 是 Mathlib 中的一个定理，位于命名空间 `Monovary`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst_1
 : CommGroup β] [inst_2 : LinearOrder β]   [IsOrderedMonoid β] {f : ι → α} {g : 
ι → β}, Monovary f g → ∀ (n : ℕ), Monovary f (g ^ n)
参数：n : ℕ；g ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_pow_lt_pow_left'`：lt_of_pow_lt_pow_left' {a b : M} (n : Nat) : a ^
 n < b ^ n -> a < b
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
lemma Monovary.pow_right₀ (hg : 0 ≤ g) (hfg : Monovary f g) (n : ℕ) : Monovary f (g ^ n) :=
  (hfg.symm.pow_left₀ hg _).symm
/-
**Antivary.pow_right** 是 Mathlib 中的一个定理，位于命名空间 `Antivary`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst_1
 : CommGroup β] [inst_2 : LinearOrder β]   [IsOrderedMonoid β] {f : ι → α} {g : 
ι → β}, Antivary f g → ∀ (n : ℕ), Antivary f (g ^ n)
参数：n : ℕ；g ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_pow_lt_pow_left'`：lt_of_pow_lt_pow_left' {a b : M} (n : Nat) : a ^
 n < b ^ n -> a < b
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
lemma Antivary.pow_right₀ (hg : 0 ≤ g) (hfg : Antivary f g) (n : ℕ) : Antivary f (g ^ n) :=
  (hfg.symm.pow_left₀ hg _).symm

end LinearOrderedSemiring

section LinearOrderedSemifield

section
variable [Semifield α] [LinearOrder α] [IsStrictOrderedRing α] [LinearOrder β]
  {s : Set ι} {f f₁ f₂ : ι → α} {g g₁ g₂ : ι → β}

@[simp]
/-
**monovaryOn_inv_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：monovaryOn_inv_left : MonovaryOn f⁻¹ g s ↔ AntivaryOn f g s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma monovaryOn_inv_left₀ (hf : ∀ i ∈ s, 0 < f i) : MonovaryOn f⁻¹ g s ↔ AntivaryOn f g s :=
  forall₅_congr fun _i hi _j hj _ ↦ inv_le_inv₀ (hf _ hi) (hf _ hj)

@[simp]
/-
**antivaryOn_inv_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：antivaryOn_inv_left : AntivaryOn f⁻¹ g s ↔ MonovaryOn f g s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma antivaryOn_inv_left₀ (hf : ∀ i ∈ s, 0 < f i) : AntivaryOn f⁻¹ g s ↔ MonovaryOn f g s :=
  forall₅_congr fun _i hi _j hj _ ↦ inv_le_inv₀ (hf _ hj) (hf _ hi)
/-
**monovary_inv_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} [inst : CommGroup α] [inst_
1 : Preorder α] [IsOrderedMonoid α]   [inst_3 : PartialOrder β] {f : ι → α} {g :
 ι → β}, Monovary f⁻¹ g ↔ Antivary f g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma monovary_inv_left₀ (hf : StrongLT 0 f) : Monovary f⁻¹ g ↔ Antivary f g :=
  forall₃_congr fun _i _j _ ↦ inv_le_inv₀ (hf _) (hf _)
/-
**antivary_inv_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} [inst : CommGroup α] [inst_
1 : Preorder α] [IsOrderedMonoid α]   [inst_3 : PartialOrder β] {f : ι → α} {g :
 ι → β}, Antivary f⁻¹ g ↔ Monovary f g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma antivary_inv_left₀ (hf : StrongLT 0 f) : Antivary f⁻¹ g ↔ Monovary f g :=
  forall₃_congr fun _i _j _ ↦ inv_le_inv₀ (hf _) (hf _)
/-
**MonovaryOn.div_left** 是 Mathlib 中的一个定理，位于命名空间 `MonovaryOn`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} [inst : CommGroup α] [inst_
1 : Preorder α] [IsOrderedMonoid α]   [inst_3 : PartialOrder β] {s : Set ι} {f₁ 
f₂ : ι → α} {g : ι → β},   MonovaryOn f₁ g s → AntivaryOn f₂ g s → MonovaryOn (f
₁ / f₂) g s
参数：f₁ / f₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `div_le_div''`：div_le_div'' (hab : a <= b) (hcd : c <= d) : a / d <= b / 
c
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
lemma MonovaryOn.div_left₀ (hf₁ : ∀ i ∈ s, 0 ≤ f₁ i) (hf₂ : ∀ i ∈ s, 0 < f₂ i)
    (h₁ : MonovaryOn f₁ g s) (h₂ : AntivaryOn f₂ g s) : MonovaryOn (f₁ / f₂) g s :=
  fun _i hi _j hj hij ↦ div_le_div₀ (hf₁ _ hj) (h₁ hi hj hij) (hf₂ _ hj) <| h₂ hi hj hij
/-
**AntivaryOn.div_left** 是 Mathlib 中的一个定理，位于命名空间 `AntivaryOn`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} [inst : CommGroup α] [inst_
1 : Preorder α] [IsOrderedMonoid α]   [inst_3 : PartialOrder β] {s : Set ι} {f₁ 
f₂ : ι → α} {g : ι → β},   AntivaryOn f₁ g s → MonovaryOn f₂ g s → AntivaryOn (f
₁ / f₂) g s
参数：f₁ / f₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `div_le_div''`：div_le_div'' (hab : a <= b) (hcd : c <= d) : a / d <= b / 
c
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
lemma AntivaryOn.div_left₀ (hf₁ : ∀ i ∈ s, 0 ≤ f₁ i) (hf₂ : ∀ i ∈ s, 0 < f₂ i)
    (h₁ : AntivaryOn f₁ g s) (h₂ : MonovaryOn f₂ g s) : AntivaryOn (f₁ / f₂) g s :=
  fun _i hi _j hj hij ↦ div_le_div₀ (hf₁ _ hi) (h₁ hi hj hij) (hf₂ _ hi) <| h₂ hi hj hij
/-
**Monovary.div_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Monovary.div_left (h₁ : Monovary f₁ g) (h₂ : Antivary f₂ g) : Monovary (f₁
 / f₂) g
参数：h₁ : Monovary f₁ g；h₂ : Antivary f₂ g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `div_le_div''`：div_le_div'' (hab : a <= b) (hcd : c <= d) : a / d <= b / 
c
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
lemma Monovary.div_left₀ (hf₁ : 0 ≤ f₁) (hf₂ : StrongLT 0 f₂) (h₁ : Monovary f₁ g)
    (h₂ : Antivary f₂ g) : Monovary (f₁ / f₂) g :=
  fun _i _j hij ↦ div_le_div₀ (hf₁ _) (h₁ hij) (hf₂ _) <| h₂ hij
/-
**Antivary.div_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Antivary.div_left (h₁ : Antivary f₁ g) (h₂ : Monovary f₂ g) : Antivary (f₁
 / f₂) g
参数：h₁ : Antivary f₁ g；h₂ : Monovary f₂ g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `div_le_div''`：div_le_div'' (hab : a <= b) (hcd : c <= d) : a / d <= b / 
c
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
lemma Antivary.div_left₀ (hf₁ : 0 ≤ f₁) (hf₂ : StrongLT 0 f₂) (h₁ : Antivary f₁ g)
    (h₂ : Monovary f₂ g) : Antivary (f₁ / f₂) g :=
  fun _i _j hij ↦ div_le_div₀ (hf₁ _) (h₁ hij) (hf₂ _) <| h₂ hij

end

section
variable [LinearOrder α] [Semifield β] [LinearOrder β] [IsStrictOrderedRing β]
  {s : Set ι} {f f₁ f₂ : ι → α} {g g₁ g₂ : ι → β}

@[simp]
/-
**monovaryOn_inv_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：monovaryOn_inv_right : MonovaryOn f g⁻¹ s ↔ AntivaryOn f g s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `instIsRightCancelMulOfMulRightReflectLE`：∀ {α : Type u_1} [inst : Mul α]
 [inst_1 : PartialOrder α] [MulRightReflectLE α], IsRightCancelMul α
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `IsOrderedCancelMonoid.toMulLeftReflectLT`：∀ {α : Type u_1} [inst : CommM
onoid α] [inst_1 : PartialOrder α] [IsOrderedCancelMonoid α], MulLeftReflectLT α
· 使用定理 `IsOrderedMonoid.toIsOrderedCancelMonoid`：∀ {α : Type u} [inst : CommGrou
p α] [inst_1 : Preorder α] [IsOrderedMonoid α], IsOrderedCancelMonoid α
· 使用定理 `forall₂_comm`：forall₂_comm {ι₁ ι₂ : Sort*} {κ₁ : ι₁ -> Sort*} {κ₂ : ι₂ -
> Sort*} {p : forall i₁, κ₁ i₁ -> forall i₂, κ₂ i₂ -> Prop} : (forall i₁ j₁ i₂ j
₂,…
-/
lemma monovaryOn_inv_right₀ (hg : ∀ i ∈ s, 0 < g i) : MonovaryOn f g⁻¹ s ↔ AntivaryOn f g s :=
  forall₂_comm.trans <| forall₄_congr fun i hi j hj ↦ by simp [inv_lt_inv₀ (hg _ hj) (hg _ hi)]

@[simp]
/-
**antivaryOn_inv_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：antivaryOn_inv_right : AntivaryOn f g⁻¹ s ↔ MonovaryOn f g s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `instIsRightCancelMulOfMulRightReflectLE`：∀ {α : Type u_1} [inst : Mul α]
 [inst_1 : PartialOrder α] [MulRightReflectLE α], IsRightCancelMul α
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `IsOrderedCancelMonoid.toMulLeftReflectLT`：∀ {α : Type u_1} [inst : CommM
onoid α] [inst_1 : PartialOrder α] [IsOrderedCancelMonoid α], MulLeftReflectLT α
· 使用定理 `IsOrderedMonoid.toIsOrderedCancelMonoid`：∀ {α : Type u} [inst : CommGrou
p α] [inst_1 : Preorder α] [IsOrderedMonoid α], IsOrderedCancelMonoid α
· 使用定理 `forall₂_comm`：forall₂_comm {ι₁ ι₂ : Sort*} {κ₁ : ι₁ -> Sort*} {κ₂ : ι₂ -
> Sort*} {p : forall i₁, κ₁ i₁ -> forall i₂, κ₂ i₂ -> Prop} : (forall i₁ j₁ i₂ j
₂,…
-/
lemma antivaryOn_inv_right₀ (hg : ∀ i ∈ s, 0 < g i) : AntivaryOn f g⁻¹ s ↔ MonovaryOn f g s :=
  forall₂_comm.trans <| forall₄_congr fun i hi j hj ↦ by simp [inv_lt_inv₀ (hg _ hj) (hg _ hi)]
/-
**monovary_inv_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} [inst : PartialOrder α] [in
st_1 : CommGroup β] [inst_2 : PartialOrder β]   [IsOrderedMonoid β] {f : ι → α} 
{g : ι → β}, Monovary f g⁻¹ ↔ Antivary f g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `instIsRightCancelMulOfMulRightReflectLE`：∀ {α : Type u_1} [inst : Mul α]
 [inst_1 : PartialOrder α] [MulRightReflectLE α], IsRightCancelMul α
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `IsOrderedCancelMonoid.toMulLeftReflectLT`：∀ {α : Type u_1} [inst : CommM
onoid α] [inst_1 : PartialOrder α] [IsOrderedCancelMonoid α], MulLeftReflectLT α
· 使用定理 `IsOrderedMonoid.toIsOrderedCancelMonoid`：∀ {α : Type u} [inst : CommGrou
p α] [inst_1 : Preorder α] [IsOrderedMonoid α], IsOrderedCancelMonoid α
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
-/
@[simp] lemma monovary_inv_right₀ (hg : StrongLT 0 g) : Monovary f g⁻¹ ↔ Antivary f g :=
  forall_comm.trans <| forall₂_congr fun i j ↦ by simp [inv_lt_inv₀ (hg _) (hg _)]
/-
**antivary_inv_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} [inst : PartialOrder α] [in
st_1 : CommGroup β] [inst_2 : PartialOrder β]   [IsOrderedMonoid β] {f : ι → α} 
{g : ι → β}, Antivary f g⁻¹ ↔ Monovary f g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `instIsRightCancelMulOfMulRightReflectLE`：∀ {α : Type u_1} [inst : Mul α]
 [inst_1 : PartialOrder α] [MulRightReflectLE α], IsRightCancelMul α
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `IsOrderedCancelMonoid.toMulLeftReflectLT`：∀ {α : Type u_1} [inst : CommM
onoid α] [inst_1 : PartialOrder α] [IsOrderedCancelMonoid α], MulLeftReflectLT α
· 使用定理 `IsOrderedMonoid.toIsOrderedCancelMonoid`：∀ {α : Type u} [inst : CommGrou
p α] [inst_1 : Preorder α] [IsOrderedMonoid α], IsOrderedCancelMonoid α
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
-/
@[simp] lemma antivary_inv_right₀ (hg : StrongLT 0 g) : Antivary f g⁻¹ ↔ Monovary f g :=
  forall_comm.trans <| forall₂_congr fun i j ↦ by simp [inv_lt_inv₀ (hg _) (hg _)]
/-
**MonovaryOn.div_right** 是 Mathlib 中的一个定理，位于命名空间 `MonovaryOn`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst_1
 : CommGroup β] [inst_2 : LinearOrder β]   [IsOrderedMonoid β] {s : Set ι} {f : 
ι → α} {g₁ g₂ : ι → β},   MonovaryOn f g₁ s → AntivaryOn f g₂ s → MonovaryOn f (
g₁ / g₂) s
参数：g₁ / g₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `lt_or_lt_of_div_lt_div`：∀ {α : Type u} [inst : CommGroup α] [inst_1 : Li
nearOrder α] [MulLeftMono α] {a b c d : α},   a / d < b / c → a < b ∨ c < d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
lemma MonovaryOn.div_right₀ (hg₁ : ∀ i ∈ s, 0 ≤ g₁ i) (hg₂ : ∀ i ∈ s, 0 < g₂ i)
    (h₁ : MonovaryOn f g₁ s) (h₂ : AntivaryOn f g₂ s) : MonovaryOn f (g₁ / g₂) s :=
  (h₁.symm.div_left₀ hg₁ hg₂ h₂.symm).symm
/-
**AntivaryOn.div_right** 是 Mathlib 中的一个定理，位于命名空间 `AntivaryOn`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst_1
 : CommGroup β] [inst_2 : LinearOrder β]   [IsOrderedMonoid β] {s : Set ι} {f : 
ι → α} {g₁ g₂ : ι → β},   AntivaryOn f g₁ s → MonovaryOn f g₂ s → AntivaryOn f (
g₁ / g₂) s
参数：g₁ / g₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `lt_or_lt_of_div_lt_div`：∀ {α : Type u} [inst : CommGroup α] [inst_1 : Li
nearOrder α] [MulLeftMono α] {a b c d : α},   a / d < b / c → a < b ∨ c < d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
lemma AntivaryOn.div_right₀ (hg₁ : ∀ i ∈ s, 0 ≤ g₁ i) (hg₂ : ∀ i ∈ s, 0 < g₂ i)
    (h₁ : AntivaryOn f g₁ s) (h₂ : MonovaryOn f g₂ s) : AntivaryOn f (g₁ / g₂) s :=
  (h₁.symm.div_left₀ hg₁ hg₂ h₂.symm).symm
/-
**Monovary.div_right** 是 Mathlib 中的一个定理，位于命名空间 `Monovary`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst_1
 : CommGroup β] [inst_2 : LinearOrder β]   [IsOrderedMonoid β] {f : ι → α} {g₁ g
₂ : ι → β}, Monovary f g₁ → Antivary f g₂ → Monovary f (g₁ / g₂)
参数：g₁ / g₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `lt_or_lt_of_div_lt_div`：∀ {α : Type u} [inst : CommGroup α] [inst_1 : Li
nearOrder α] [MulLeftMono α] {a b c d : α},   a / d < b / c → a < b ∨ c < d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
lemma Monovary.div_right₀ (hg₁ : 0 ≤ g₁) (hg₂ : StrongLT 0 g₂) (h₁ : Monovary f g₁)
    (h₂ : Antivary f g₂) : Monovary f (g₁ / g₂) := (h₁.symm.div_left₀ hg₁ hg₂ h₂.symm).symm
/-
**Antivary.div_right** 是 Mathlib 中的一个定理，位于命名空间 `Antivary`。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst_1
 : CommGroup β] [inst_2 : LinearOrder β]   [IsOrderedMonoid β] {f : ι → α} {g₁ g
₂ : ι → β}, Antivary f g₁ → Monovary f g₂ → Antivary f (g₁ / g₂)
参数：g₁ / g₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `lt_or_lt_of_div_lt_div`：∀ {α : Type u} [inst : CommGroup α] [inst_1 : Li
nearOrder α] [MulLeftMono α] {a b c d : α},   a / d < b / c → a < b ∨ c < d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
lemma Antivary.div_right₀ (hg₁ : 0 ≤ g₁) (hg₂ : StrongLT 0 g₂) (h₁ : Antivary f g₁)
    (h₂ : Monovary f g₂) : Antivary f (g₁ / g₂) := (h₁.symm.div_left₀ hg₁ hg₂ h₂.symm).symm

end

section
variable [Semifield α] [LinearOrder α] [IsStrictOrderedRing α]
  [Semifield β] [LinearOrder β] [IsStrictOrderedRing β]
  {s : Set ι} {f f₁ f₂ : ι → α} {g g₁ g₂ : ι → β}

/-
**monovaryOn_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} [inst : CommGroup α] [inst_
1 : PartialOrder α] [IsOrderedMonoid α]   [inst_3 : CommGroup β] [inst_4 : Parti
alOrder β] [IsOrderedMonoid β] {s : Set ι} {f : ι → α} {g : ι → β},   MonovaryOn
 f⁻¹ g⁻¹ s ↔ MonovaryOn f g s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma monovaryOn_inv₀ (hf : ∀ i ∈ s, 0 < f i) (hg : ∀ i ∈ s, 0 < g i) :
    MonovaryOn f⁻¹ g⁻¹ s ↔ MonovaryOn f g s := by
  rw [monovaryOn_inv_left₀ hf, antivaryOn_inv_right₀ hg]
/-
**antivaryOn_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} [inst : CommGroup α] [inst_
1 : PartialOrder α] [IsOrderedMonoid α]   [inst_3 : CommGroup β] [inst_4 : Parti
alOrder β] [IsOrderedMonoid β] {s : Set ι} {f : ι → α} {g : ι → β},   AntivaryOn
 f⁻¹ g⁻¹ s ↔ AntivaryOn f g s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma antivaryOn_inv₀ (hf : ∀ i ∈ s, 0 < f i) (hg : ∀ i ∈ s, 0 < g i) :
    AntivaryOn f⁻¹ g⁻¹ s ↔ AntivaryOn f g s := by
  rw [antivaryOn_inv_left₀ hf, monovaryOn_inv_right₀ hg]
/-
**monovary_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} [inst : CommGroup α] [inst_
1 : PartialOrder α] [IsOrderedMonoid α]   [inst_3 : CommGroup β] [inst_4 : Parti
alOrder β] [IsOrderedMonoid β] {f : ι → α} {g : ι → β},   Monovary f⁻¹ g⁻¹ ↔ Mon
ovary f g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma monovary_inv₀ (hf : StrongLT 0 f) (hg : StrongLT 0 g) : Monovary f⁻¹ g⁻¹ ↔ Monovary f g := by
  rw [monovary_inv_left₀ hf, antivary_inv_right₀ hg]
/-
**antivary_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {ι : Type u_1} {α : Type u_2} {β : Type u_3} [inst : CommGroup α] [inst_
1 : PartialOrder α] [IsOrderedMonoid α]   [inst_3 : CommGroup β] [inst_4 : Parti
alOrder β] [IsOrderedMonoid β] {f : ι → α} {g : ι → β},   Antivary f⁻¹ g⁻¹ ↔ Ant
ivary f g
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma antivary_inv₀ (hf : StrongLT 0 f) (hg : StrongLT 0 g) : Antivary f⁻¹ g⁻¹ ↔ Antivary f g := by
  rw [antivary_inv_left₀ hf, monovary_inv_right₀ hg]

end

alias ⟨MonovaryOn.of_inv_left₀, AntivaryOn.inv_left₀⟩ := monovaryOn_inv_left₀
alias ⟨AntivaryOn.of_inv_left₀, MonovaryOn.inv_left₀⟩ := antivaryOn_inv_left₀
alias ⟨MonovaryOn.of_inv_right₀, AntivaryOn.inv_right₀⟩ := monovaryOn_inv_right₀
alias ⟨AntivaryOn.of_inv_right₀, MonovaryOn.inv_right₀⟩ := antivaryOn_inv_right₀
alias ⟨MonovaryOn.of_inv₀, MonovaryOn.inv₀⟩ := monovaryOn_inv₀
alias ⟨AntivaryOn.of_inv₀, AntivaryOn.inv₀⟩ := antivaryOn_inv₀
alias ⟨Monovary.of_inv_left₀, Antivary.inv_left₀⟩ := monovary_inv_left₀
alias ⟨Antivary.of_inv_left₀, Monovary.inv_left₀⟩ := antivary_inv_left₀
alias ⟨Monovary.of_inv_right₀, Antivary.inv_right₀⟩ := monovary_inv_right₀
alias ⟨Antivary.of_inv_right₀, Monovary.inv_right₀⟩ := antivary_inv_right₀
alias ⟨Monovary.of_inv₀, Monovary.inv₀⟩ := monovary_inv₀
alias ⟨Antivary.of_inv₀, Antivary.inv₀⟩ := antivary_inv₀

end LinearOrderedSemifield

/-! ### Rearrangement inequality characterisation -/

section LinearOrderedAddCommGroup
variable [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [AddCommGroup β] [LinearOrder β] [IsOrderedAddMonoid β] [Module α β]
  [IsStrictOrderedModule α β] {f : ι → α} {g : ι → β} {s : Set ι}

/-
**monovaryOn_iff_forall_smul_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：monovaryOn_iff_forall_smul_nonneg : MonovaryOn f g s ↔ forall ⦃i⦄, i in s 
-> forall ⦃j⦄, j in s -> 0 <= (f j - f i) • (g j - g i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsStrictOrderedModule.toPosSMulStrictMono`：∀ {α : Type u_1} {β : Type u_
2} {inst : SMul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero 
α}   {inst_4 : Zero β} [self : …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `and_iff_right_of_imp`：∀ {b a : Prop}, (b → a) → (a ∧ b ↔ b)
· 使用定理 `MonovaryOn.symm`：∀ {ι : Type u_1} {α : Type u_3} {β : Type u_4} [inst : 
Preorder α] [inst_1 : LinearOrder β] {f : ι → α} {g : ι → β}   {s : Set ι}, Mono
varyO…
-/
lemma monovaryOn_iff_forall_smul_nonneg :
    MonovaryOn f g s ↔ ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ s → 0 ≤ (f j - f i) • (g j - g i) := by
  simp_rw [smul_nonneg_iff_pos_imp_nonneg, sub_pos, sub_nonneg, forall_and]
  exact (and_iff_right_of_imp MonovaryOn.symm).symm
/-
**antivaryOn_iff_forall_smul_nonpos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：antivaryOn_iff_forall_smul_nonpos : AntivaryOn f g s ↔ forall ⦃i⦄, i in s 
-> forall ⦃j⦄, j in s -> (f j - f i) • (g j - g i) <= 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `monovaryOn_toDual_right`：monovaryOn_toDual_right : MonovaryOn f (toDual 
∘ g) s ↔ AntivaryOn f g s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `monovaryOn_iff_forall_smul_nonneg`：monovaryOn_iff_forall_smul_nonneg : M
onovaryOn f g s ↔ forall ⦃i⦄, i in s -> forall ⦃j⦄, j in s -> 0 <= (f j - f i) •
 (g j - g i)
· 使用定理 `OrderDual.isOrderedAddMonoid`：∀ {α : Type u} [inst : AddCommMonoid α] [i
nst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedAddMonoid αᵒᵈ
· 使用定理 `OrderDual.instIsStrictOrderedModule`：∀ {α : Type u_1} {β : Type u_2} [in
st : Preorder α] [inst_1 : MonoidWithZero α] [inst_2 : AddCommGroup β]   [inst_3
 : PartialOrder β] [IsOrd…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma antivaryOn_iff_forall_smul_nonpos :
    AntivaryOn f g s ↔ ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ s → (f j - f i) • (g j - g i) ≤ 0 :=
  monovaryOn_toDual_right.symm.trans <| by rw [monovaryOn_iff_forall_smul_nonneg]; rfl
/-
**monovary_iff_forall_smul_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：monovary_iff_forall_smul_nonneg : Monovary f g ↔ forall i j, 0 <= (f j - f
 i) • (g j - g i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `monovaryOn_univ`：monovaryOn_univ : MonovaryOn f g univ ↔ Monovary f g
· 使用引理 `monovaryOn_iff_forall_smul_nonneg`：monovaryOn_iff_forall_smul_nonneg : M
onovaryOn f g s ↔ forall ⦃i⦄, i in s -> forall ⦃j⦄, j in s -> 0 <= (f j - f i) •
 (g j - g i)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma monovary_iff_forall_smul_nonneg : Monovary f g ↔ ∀ i j, 0 ≤ (f j - f i) • (g j - g i) :=
  monovaryOn_univ.symm.trans <| monovaryOn_iff_forall_smul_nonneg.trans <| by
    simp only [Set.mem_univ, forall_true_left]
/-
**antivary_iff_forall_smul_nonpos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：antivary_iff_forall_smul_nonpos : Antivary f g ↔ forall i j, (f j - f i) •
 (g j - g i) <= 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `monovary_toDual_right`：monovary_toDual_right : Monovary f (toDual ∘ g) ↔
 Antivary f g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `monovary_iff_forall_smul_nonneg`：monovary_iff_forall_smul_nonneg : Monov
ary f g ↔ forall i j, 0 <= (f j - f i) • (g j - g i)
· 使用定理 `OrderDual.isOrderedAddMonoid`：∀ {α : Type u} [inst : AddCommMonoid α] [i
nst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedAddMonoid αᵒᵈ
· 使用定理 `OrderDual.instIsStrictOrderedModule`：∀ {α : Type u_1} {β : Type u_2} [in
st : Preorder α] [inst_1 : MonoidWithZero α] [inst_2 : AddCommGroup β]   [inst_3
 : PartialOrder β] [IsOrd…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma antivary_iff_forall_smul_nonpos : Antivary f g ↔ ∀ i j, (f j - f i) • (g j - g i) ≤ 0 :=
monovary_toDual_right.symm.trans <| by rw [monovary_iff_forall_smul_nonneg]; rfl

/-- Two functions monovary iff the rearrangement inequality holds. -/
/-
**monovaryOn_iff_smul_rearrangement** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：monovaryOn_iff_smul_rearrangement : MonovaryOn f g s ↔ forall ⦃i⦄, i in s 
-> forall ⦃j⦄, j in s -> f i • g j + f j • g i <= f i • g i + f j • g j
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `monovaryOn_iff_forall_smul_nonneg`：monovaryOn_iff_forall_smul_nonneg : M
onovaryOn f g s ↔ forall ⦃i⦄, i in s -> forall ⦃j⦄, j in s -> 0 <= (f j - f i) •
 (g j - g i)
· 使用定理 `forall₄_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → 
Sort u_3} {δ : (a : α) → (b : β a) → γ a b → Sort u_4}   {p q : (a : α) → (b : β
 a)…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `AddGroup.toOrderedSub`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LE
 α] [AddRightMono α], OrderedSub α
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Two functions monovary iff the rearrangement inequality holds.
-/
lemma monovaryOn_iff_smul_rearrangement :
    MonovaryOn f g s ↔
      ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ s → f i • g j + f j • g i ≤ f i • g i + f j • g j :=
  monovaryOn_iff_forall_smul_nonneg.trans <| forall₄_congr fun i _ j _ ↦ by
    simp [smul_sub, sub_smul, ← add_sub_right_comm, le_sub_iff_add_le, add_comm (f i • g i),
      add_comm (f i • g j)]

/-- Two functions antivary iff the rearrangement inequality holds. -/
/-
**antivaryOn_iff_smul_rearrangement** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：antivaryOn_iff_smul_rearrangement : AntivaryOn f g s ↔ forall ⦃i⦄, i in s 
-> forall ⦃j⦄, j in s -> f i • g i + f j • g j <= f i • g j + f j • g i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `monovaryOn_toDual_right`：monovaryOn_toDual_right : MonovaryOn f (toDual 
∘ g) s ↔ AntivaryOn f g s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `monovaryOn_iff_smul_rearrangement`：monovaryOn_iff_smul_rearrangement : M
onovaryOn f g s ↔ forall ⦃i⦄, i in s -> forall ⦃j⦄, j in s -> f i • g j + f j • 
g i <= f i • g i + f j …
· 使用定理 `OrderDual.isOrderedAddMonoid`：∀ {α : Type u} [inst : AddCommMonoid α] [i
nst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedAddMonoid αᵒᵈ
· 使用定理 `OrderDual.instIsStrictOrderedModule`：∀ {α : Type u_1} {β : Type u_2} [in
st : Preorder α] [inst_1 : MonoidWithZero α] [inst_2 : AddCommGroup β]   [inst_3
 : PartialOrder β] [IsOrd…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Two functions antivary iff the rearrangement inequality holds.
-/
lemma antivaryOn_iff_smul_rearrangement :
    AntivaryOn f g s ↔
      ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ s → f i • g i + f j • g j ≤ f i • g j + f j • g i :=
  monovaryOn_toDual_right.symm.trans <| by rw [monovaryOn_iff_smul_rearrangement]; rfl

/-- Two functions monovary iff the rearrangement inequality holds. -/
/-
**monovary_iff_smul_rearrangement** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：monovary_iff_smul_rearrangement : Monovary f g ↔ forall i j, f i • g j + f
 j • g i <= f i • g i + f j • g j
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `monovaryOn_univ`：monovaryOn_univ : MonovaryOn f g univ ↔ Monovary f g
· 使用引理 `monovaryOn_iff_smul_rearrangement`：monovaryOn_iff_smul_rearrangement : M
onovaryOn f g s ↔ forall ⦃i⦄, i in s -> forall ⦃j⦄, j in s -> f i • g j + f j • 
g i <= f i • g i + f j …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Two functions monovary iff the rearrangement inequality holds.
-/
lemma monovary_iff_smul_rearrangement :
    Monovary f g ↔ ∀ i j, f i • g j + f j • g i ≤ f i • g i + f j • g j :=
  monovaryOn_univ.symm.trans <| monovaryOn_iff_smul_rearrangement.trans <| by
    simp only [Set.mem_univ, forall_true_left]

/-- Two functions antivary iff the rearrangement inequality holds. -/
/-
**antivary_iff_smul_rearrangement** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：antivary_iff_smul_rearrangement : Antivary f g ↔ forall i j, f i • g i + f
 j • g j <= f i • g j + f j • g i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `monovary_toDual_right`：monovary_toDual_right : Monovary f (toDual ∘ g) ↔
 Antivary f g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `monovary_iff_smul_rearrangement`：monovary_iff_smul_rearrangement : Monov
ary f g ↔ forall i j, f i • g j + f j • g i <= f i • g i + f j • g j
· 使用定理 `OrderDual.isOrderedAddMonoid`：∀ {α : Type u} [inst : AddCommMonoid α] [i
nst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedAddMonoid αᵒᵈ
· 使用定理 `OrderDual.instIsStrictOrderedModule`：∀ {α : Type u_1} {β : Type u_2} [in
st : Preorder α] [inst_1 : MonoidWithZero α] [inst_2 : AddCommGroup β]   [inst_3
 : PartialOrder β] [IsOrd…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Two functions antivary iff the rearrangement inequality holds.
-/
lemma antivary_iff_smul_rearrangement :
    Antivary f g ↔ ∀ i j, f i • g i + f j • g j ≤ f i • g j + f j • g i :=
  monovary_toDual_right.symm.trans <| by rw [monovary_iff_smul_rearrangement]; rfl

alias ⟨MonovaryOn.sub_smul_sub_nonneg, _⟩ := monovaryOn_iff_forall_smul_nonneg
alias ⟨AntivaryOn.sub_smul_sub_nonpos, _⟩ := antivaryOn_iff_forall_smul_nonpos
alias ⟨Monovary.sub_smul_sub_nonneg, _⟩ := monovary_iff_forall_smul_nonneg
alias ⟨Antivary.sub_smul_sub_nonpos, _⟩ := antivary_iff_forall_smul_nonpos
alias ⟨Monovary.smul_add_smul_le_smul_add_smul, _⟩ := monovary_iff_smul_rearrangement
alias ⟨Antivary.smul_add_smul_le_smul_add_smul, _⟩ := antivary_iff_smul_rearrangement
alias ⟨MonovaryOn.smul_add_smul_le_smul_add_smul, _⟩ := monovaryOn_iff_smul_rearrangement
alias ⟨AntivaryOn.smul_add_smul_le_smul_add_smul, _⟩ := antivaryOn_iff_smul_rearrangement

end LinearOrderedAddCommGroup

section LinearOrderedRing
variable [Ring α] [LinearOrder α] [IsStrictOrderedRing α] {f g : ι → α} {s : Set ι}

/-
**monovaryOn_iff_forall_mul_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：monovaryOn_iff_forall_mul_nonneg : MonovaryOn f g s ↔ forall ⦃i⦄, i in s -
> forall ⦃j⦄, j in s -> 0 <= (f j - f i) * (g j - g i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma monovaryOn_iff_forall_mul_nonneg :
    MonovaryOn f g s ↔ ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ s → 0 ≤ (f j - f i) * (g j - g i) := by
  simp only [smul_eq_mul, monovaryOn_iff_forall_smul_nonneg]
/-
**antivaryOn_iff_forall_mul_nonpos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：antivaryOn_iff_forall_mul_nonpos : AntivaryOn f g s ↔ forall ⦃i⦄, i in s -
> forall ⦃j⦄, j in s -> (f j - f i) * (g j - g i) <= 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma antivaryOn_iff_forall_mul_nonpos :
    AntivaryOn f g s ↔ ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ s → (f j - f i) * (g j - g i) ≤ 0 := by
  simp only [smul_eq_mul, antivaryOn_iff_forall_smul_nonpos]
/-
**monovary_iff_forall_mul_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：monovary_iff_forall_mul_nonneg : Monovary f g ↔ forall i j, 0 <= (f j - f 
i) * (g j - g i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma monovary_iff_forall_mul_nonneg : Monovary f g ↔ ∀ i j, 0 ≤ (f j - f i) * (g j - g i) := by
  simp only [smul_eq_mul, monovary_iff_forall_smul_nonneg]
/-
**antivary_iff_forall_mul_nonpos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：antivary_iff_forall_mul_nonpos : Antivary f g ↔ forall i j, (f j - f i) * 
(g j - g i) <= 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma antivary_iff_forall_mul_nonpos : Antivary f g ↔ ∀ i j, (f j - f i) * (g j - g i) ≤ 0 := by
  simp only [smul_eq_mul, antivary_iff_forall_smul_nonpos]

/-- Two functions monovary iff the rearrangement inequality holds. -/
/-
**monovaryOn_iff_mul_rearrangement** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：monovaryOn_iff_mul_rearrangement : MonovaryOn f g s ↔ forall ⦃i⦄, i in s -
> forall ⦃j⦄, j in s -> f i * g j + f j * g i <= f i * g i + f j * g j
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Two functions monovary iff the rearrangement inequality holds.
-/
lemma monovaryOn_iff_mul_rearrangement :
    MonovaryOn f g s ↔
      ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ s → f i * g j + f j * g i ≤ f i * g i + f j * g j := by
  simp only [smul_eq_mul, monovaryOn_iff_smul_rearrangement]

/-- Two functions antivary iff the rearrangement inequality holds. -/
/-
**antivaryOn_iff_mul_rearrangement** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：antivaryOn_iff_mul_rearrangement : AntivaryOn f g s ↔ forall ⦃i⦄, i in s -
> forall ⦃j⦄, j in s -> f i * g i + f j * g j <= f i * g j + f j * g i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Two functions antivary iff the rearrangement inequality holds.
-/
lemma antivaryOn_iff_mul_rearrangement :
    AntivaryOn f g s ↔
      ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ s → f i * g i + f j * g j ≤ f i * g j + f j * g i := by
  simp only [smul_eq_mul, antivaryOn_iff_smul_rearrangement]

/-- Two functions monovary iff the rearrangement inequality holds. -/
/-
**monovary_iff_mul_rearrangement** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：monovary_iff_mul_rearrangement : Monovary f g ↔ forall i j, f i * g j + f 
j * g i <= f i * g i + f j * g j
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Two functions monovary iff the rearrangement inequality holds.
-/
lemma monovary_iff_mul_rearrangement :
    Monovary f g ↔ ∀ i j, f i * g j + f j * g i ≤ f i * g i + f j * g j := by
  simp only [smul_eq_mul, monovary_iff_smul_rearrangement]

/-- Two functions antivary iff the rearrangement inequality holds. -/
/-
**antivary_iff_mul_rearrangement** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：antivary_iff_mul_rearrangement : Antivary f g ↔ forall i j, f i * g i + f 
j * g j <= f i * g j + f j * g i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Two functions antivary iff the rearrangement inequality holds.
-/
lemma antivary_iff_mul_rearrangement :
    Antivary f g ↔ ∀ i j, f i * g i + f j * g j ≤ f i * g j + f j * g i := by
  simp only [smul_eq_mul, antivary_iff_smul_rearrangement]

alias ⟨MonovaryOn.sub_mul_sub_nonneg, _⟩ := monovaryOn_iff_forall_mul_nonneg
alias ⟨AntivaryOn.sub_mul_sub_nonpos, _⟩ := antivaryOn_iff_forall_mul_nonpos
alias ⟨Monovary.sub_mul_sub_nonneg, _⟩ := monovary_iff_forall_mul_nonneg
alias ⟨Antivary.sub_mul_sub_nonpos, _⟩ := antivary_iff_forall_mul_nonpos
alias ⟨Monovary.mul_add_mul_le_mul_add_mul, _⟩ := monovary_iff_mul_rearrangement
alias ⟨Antivary.mul_add_mul_le_mul_add_mul, _⟩ := antivary_iff_mul_rearrangement
alias ⟨MonovaryOn.mul_add_mul_le_mul_add_mul, _⟩ := monovaryOn_iff_mul_rearrangement
alias ⟨AntivaryOn.mul_add_mul_le_mul_add_mul, _⟩ := antivaryOn_iff_mul_rearrangement

end LinearOrderedRing

