/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot, Yury Kudryashov, Rémy Degenne
-/
module

public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Data.Set.Subsingleton
public import Mathlib.Order.BooleanAlgebra.Set
public import Mathlib.Order.Interval.Set.Defs

/-!
# Intervals

In any preorder, we define intervals (which on each side can be either infinite, open or closed)
using the following naming conventions:

- `i`: infinite
- `o`: open
- `c`: closed

Each interval has the name `I` + letter for left side + letter for right side.
For instance, `Ioc a b` denotes the interval `(a, b]`.
The definitions can be found in `Mathlib/Order/Interval/Set/Defs.lean`.

This file contains basic facts on inclusion of and set operations on intervals
(where the precise statements depend on the order's properties;
statements requiring `LinearOrder` are in `Mathlib/Order/Interval/Set/LinearOrder.lean`).

A conscious decision was made not to list all possible inclusion relations.
Monotonicity results and "self" results *are* included.
Most use cases can suffice with a transitive combination of those, for example:
```
theorem Ico_subset_Ici (h : a₂ ≤ a₁) : Ico a₁ b₁ ⊆ Ici a₂ :=
  (Ico_subset_Ico_left h).trans Ico_subset_Ici_self
```
Logical equivalences, such as `Icc_subset_Ici_iff`, are however stated.
-/

public section

assert_not_exists RelIso

open Function

open OrderDual (toDual ofDual)

variable {α : Type*}

namespace Set

section Preorder

variable [Preorder α] {a a₁ a₂ b b₁ b₂ c x : α}

@[to_dual]
/-
**Set.decidableMemIio** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：decidableMemIio [Decidable (x < b)] : Decidable (x in Iio b)
参数：x < b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableMemIio [Decidable (x < b)] : Decidable (x ∈ Iio b) := by assumption

@[to_dual]
/-
**Set.decidableMemIic** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：decidableMemIic [Decidable (x <= b)] : Decidable (x in Iic b)
参数：x <= b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableMemIic [Decidable (x ≤ b)] : Decidable (x ∈ Iic b) := by assumption

@[to_dual self (reorder := a b, 6 7)]
/-
**Set.decidableMemIoo** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：decidableMemIoo [Decidable (a < x)] [Decidable (x < b)] : Decidable (x in 
Ioo a b)
参数：a < x；x < b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableMemIoo [Decidable (a < x)] [Decidable (x < b)] : Decidable (x ∈ Ioo a b) :=
  instDecidableAnd
/-
**Set.decidableMemIco** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：decidableMemIco [Decidable (a <= x)] [Decidable (x < b)] : Decidable (x in
 Ico a b)
参数：a <= x；x < b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableMemIco [Decidable (a ≤ x)] [Decidable (x < b)] : Decidable (x ∈ Ico a b) :=
  instDecidableAnd

@[to_dual self (reorder := a b, 6 7)]
/-
**Set.decidableMemIcc** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：decidableMemIcc [Decidable (a <= x)] [Decidable (x <= b)] : Decidable (x i
n Icc a b)
参数：a <= x；x <= b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableMemIcc [Decidable (a ≤ x)] [Decidable (x ≤ b)] : Decidable (x ∈ Icc a b) :=
  instDecidableAnd

@[to_dual existing (reorder := a b, 6 7)]
/-
**Set.decidableMemIoc** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：decidableMemIoc [Decidable (a < x)] [Decidable (x <= b)] : Decidable (x in
 Ioc a b)
参数：a < x；x <= b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableMemIoc [Decidable (a < x)] [Decidable (x ≤ b)] : Decidable (x ∈ Ioc a b) :=
  instDecidableAnd
/-
**Set.self_notMem_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {a : α}, a ∉ Set.Iio a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
@[to_dual] theorem self_notMem_Iio : a ∉ Iio a := by simp
/-
**Set.self_mem_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {a : α}, a ∈ Set.Iic a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
@[to_dual] theorem self_mem_Iic : a ∈ Iic a := by simp

@[to_dual right_notMem_Ioo]
/-
**Set.left_notMem_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：left_notMem_Ioo : a ∉ Ioo a b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem left_notMem_Ioo : a ∉ Ioo a b := by simp

@[to_dual right_notMem_Ico]
/-
**Set.left_notMem_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：left_notMem_Ioc : a ∉ Ioc a b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem left_notMem_Ioc : a ∉ Ioc a b := by simp
/-
**Set.left_mem_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ Set.Ico a b ↔ a < b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[to_dual right_mem_Ioc] theorem left_mem_Ico : a ∈ Ico a b ↔ a < b := by simp
/-
**Set.left_mem_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ Set.Icc a b ↔ a ≤ b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[to_dual right_mem_Icc] theorem left_mem_Icc : a ∈ Icc a b ↔ a ≤ b := by simp

@[to_dual (attr := simp)]
/-
**Set.Iio_toDual** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iio_toDual : Iio (toDual a) = ofDual ⁻¹' Ioi a
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Iio_toDual : Iio (toDual a) = ofDual ⁻¹' Ioi a :=
  rfl

@[to_dual (attr := simp)]
/-
**Set.Iic_toDual** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iic_toDual : Iic (toDual a) = ofDual ⁻¹' Ici a
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Iic_toDual : Iic (toDual a) = ofDual ⁻¹' Ici a :=
  rfl

@[simp, to_dual self]
/-
**Set.Icc_toDual** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Icc_toDual : Icc (toDual a) (toDual b) = ofDual ⁻¹' Icc b a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
-/
theorem Icc_toDual : Icc (toDual a) (toDual b) = ofDual ⁻¹' Icc b a :=
  Set.ext fun _ => and_comm

@[to_dual (attr := simp)]
/-
**Set.Ico_toDual** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ico_toDual : Ico (toDual a) (toDual b) = ofDual ⁻¹' Ioc b a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
-/
theorem Ico_toDual : Ico (toDual a) (toDual b) = ofDual ⁻¹' Ioc b a :=
  Set.ext fun _ => and_comm

@[simp, to_dual self]
/-
**Set.Ioo_toDual** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioo_toDual : Ioo (toDual a) (toDual b) = ofDual ⁻¹' Ioo b a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
-/
theorem Ioo_toDual : Ioo (toDual a) (toDual b) = ofDual ⁻¹' Ioo b a :=
  Set.ext fun _ => and_comm

@[to_dual (attr := simp)]
/-
**Set.Iio_ofDual** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iio_ofDual {x : αᵒᵈ} : Iio (ofDual x) = toDual ⁻¹' Ioi x
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Iio_ofDual {x : αᵒᵈ} : Iio (ofDual x) = toDual ⁻¹' Ioi x :=
  rfl

@[to_dual (attr := simp)]
/-
**Set.Iic_ofDual** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iic_ofDual {x : αᵒᵈ} : Iic (ofDual x) = toDual ⁻¹' Ici x
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Iic_ofDual {x : αᵒᵈ} : Iic (ofDual x) = toDual ⁻¹' Ici x :=
  rfl

@[simp, to_dual self]
/-
**Set.Icc_ofDual** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Icc_ofDual {x y : αᵒᵈ} : Icc (ofDual y) (ofDual x) = toDual ⁻¹' Icc x y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
-/
theorem Icc_ofDual {x y : αᵒᵈ} : Icc (ofDual y) (ofDual x) = toDual ⁻¹' Icc x y :=
  Set.ext fun _ => and_comm

@[to_dual (attr := simp)]
/-
**Set.Ico_ofDual** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ico_ofDual {x y : αᵒᵈ} : Ico (ofDual y) (ofDual x) = toDual ⁻¹' Ioc x y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
-/
theorem Ico_ofDual {x y : αᵒᵈ} : Ico (ofDual y) (ofDual x) = toDual ⁻¹' Ioc x y :=
  Set.ext fun _ => and_comm

@[simp, to_dual self]
/-
**Set.Ioo_ofDual** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioo_ofDual {x y : αᵒᵈ} : Ioo (ofDual y) (ofDual x) = toDual ⁻¹' Ioo x y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
-/
theorem Ioo_ofDual {x y : αᵒᵈ} : Ioo (ofDual y) (ofDual x) = toDual ⁻¹' Ioo x y :=
  Set.ext fun _ => and_comm

@[to_dual (attr := simp)]
/-
**Set.nonempty_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：nonempty_Iio [NoMinOrder α] : (Iio a).Nonempty
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NoMinOrder.exists_lt`：∀ {α : Type u_3} {inst : LT α} [self : NoMinOrder 
α] (a : α), ∃ b, b < a
-/
theorem nonempty_Iio [NoMinOrder α] : (Iio a).Nonempty :=
  exists_lt a

@[to_dual (attr := simp)]
/-
**Set.nonempty_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：nonempty_Iic : (Iic a).Nonempty
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.self_mem_Iic`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, a ∈ Set.
Iic a
-/
theorem nonempty_Iic : (Iic a).Nonempty :=
  ⟨a, self_mem_Iic⟩

@[simp, to_dual self]
/-
**Set.nonempty_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：nonempty_Icc : (Icc a b).Nonempty ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.left_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ Se
t.Icc a b ↔ a ≤ b
-/
theorem nonempty_Icc : (Icc a b).Nonempty ↔ a ≤ b :=
  ⟨fun ⟨_, hx⟩ => hx.1.trans hx.2, fun h => ⟨a, left_mem_Icc.2 h⟩⟩

@[to_dual (attr := simp)]
/-
**Set.nonempty_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：nonempty_Ico : (Ico a b).Nonempty ↔ a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.left_mem_Ico`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ Se
t.Ico a b ↔ a < b
-/
theorem nonempty_Ico : (Ico a b).Nonempty ↔ a < b :=
  ⟨fun ⟨_, hx⟩ => hx.1.trans_lt hx.2, fun h => ⟨a, left_mem_Ico.2 h⟩⟩


@[simp, to_dual self]
/-
**Set.nonempty_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：nonempty_Ioo [DenselyOrdered α] : (Ioo a b).Nonempty ↔ a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
-/
theorem nonempty_Ioo [DenselyOrdered α] : (Ioo a b).Nonempty ↔ a < b :=
  ⟨fun ⟨_, ha, hb⟩ => ha.trans hb, exists_between⟩

/-- In an order without minimal elements, the intervals `Iio` are nonempty. -/
@[to_dual /-- In an order without maximal elements, the intervals `Ioi` are nonempty. -/]
/-
**Set.nonempty_Iio_subtype** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：nonempty_Iio_subtype [NoMinOrder α] : Nonempty (Iio a)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.to_subtype`：∀ {α : Type u} {s : Set α}, s.Nonempty → Nonemp
ty ↑s
· 使用定理 `Set.nonempty_Iio`：nonempty_Iio [NoMinOrder α] : (Iio a).Nonempty

--- 原说明 ---
In an order without minimal elements, the intervals `Iio` are nonempty.
-/
instance nonempty_Iio_subtype [NoMinOrder α] : Nonempty (Iio a) :=
  Nonempty.to_subtype nonempty_Iio

/-- An interval `Iic a` is nonempty. -/
@[to_dual /-- An interval `Ici a` is nonempty. -/]
/-
**Set.nonempty_Iic_subtype** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：nonempty_Iic_subtype : Nonempty (Iic a)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.to_subtype`：∀ {α : Type u} {s : Set α}, s.Nonempty → Nonemp
ty ↑s
· 使用定理 `Set.nonempty_Iic`：nonempty_Iic : (Iic a).Nonempty

--- 原说明 ---
An interval `Iic a` is nonempty.
-/
instance nonempty_Iic_subtype : Nonempty (Iic a) :=
  Nonempty.to_subtype nonempty_Iic

@[to_dual self]
/-
**Set.nonempty_Icc_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：nonempty_Icc_subtype (h : a <= b) : Nonempty (Icc a b)
参数：h : a <= b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.to_subtype`：∀ {α : Type u} {s : Set α}, s.Nonempty → Nonemp
ty ↑s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.nonempty_Icc`：nonempty_Icc : (Icc a b).Nonempty ↔ a <= b
-/
theorem nonempty_Icc_subtype (h : a ≤ b) : Nonempty (Icc a b) :=
  Nonempty.to_subtype (nonempty_Icc.mpr h)

@[to_dual]
/-
**Set.nonempty_Ioc_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：nonempty_Ioc_subtype (h : a < b) : Nonempty (Ioc a b)
参数：h : a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.to_subtype`：∀ {α : Type u} {s : Set α}, s.Nonempty → Nonemp
ty ↑s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.nonempty_Ioc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, (Set.I
oc b a).Nonempty ↔ b < a
-/
theorem nonempty_Ioc_subtype (h : a < b) : Nonempty (Ioc a b) :=
  Nonempty.to_subtype (nonempty_Ioc.mpr h)

@[to_dual self]
/-
**Set.nonempty_Ioo_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：nonempty_Ioo_subtype [DenselyOrdered α] (h : a < b) : Nonempty (Ioo a b)
参数：h : a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.to_subtype`：∀ {α : Type u} {s : Set α}, s.Nonempty → Nonemp
ty ↑s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.nonempty_Ioo`：nonempty_Ioo [DenselyOrdered α] : (Ioo a b).Nonempty ↔
 a < b
-/
theorem nonempty_Ioo_subtype [DenselyOrdered α] (h : a < b) : Nonempty (Ioo a b) :=
  Nonempty.to_subtype (nonempty_Ioo.mpr h)

@[to_additive (attr := simp)]
/-
**Set.Iio_one_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iio_one_eq_empty [One α] [IsBotOneClass α] : Set.Iio (1 : α) = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Iio_one_eq_empty [One α] [IsBotOneClass α] : Set.Iio (1 : α) = ∅ := by
  ext; simp

@[to_additive]
/-
**Set.isEmpty_Iio_one** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：isEmpty_Iio_one [One α] [IsBotOneClass α] : IsEmpty (Set.Iio (1 : α))
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Iio_one_eq_empty`：Iio_one_eq_empty [One α] [IsBotOneClass α] : Set.I
io (1 : α) = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance isEmpty_Iio_one [One α] [IsBotOneClass α] : IsEmpty (Set.Iio (1 : α)) := by
  simp

@[to_dual]
/-
**Set.** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NoMinOrder α] : NoMinOrder (Iio a) :=
  ⟨fun a =>
    let ⟨b, hb⟩ := exists_lt (a : α)
    ⟨⟨b, lt_trans hb a.2⟩, hb⟩⟩

@[to_dual]
/-
**Set.** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NoMinOrder α] : NoMinOrder (Iic a) :=
  ⟨fun a =>
    let ⟨b, hb⟩ := exists_lt (a : α)
    ⟨⟨b, hb.le.trans a.2⟩, hb⟩⟩

@[simp, to_dual self]
/-
**Set.Icc_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Icc_eq_empty (h : ¬a <= b) : Icc a b = ∅
参数：h : ¬a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.eq_empty_iff_forall_notMem`：eq_empty_iff_forall_notMem {s : Set α} :
 s = ∅ ↔ forall x, x ∉ s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem Icc_eq_empty (h : ¬a ≤ b) : Icc a b = ∅ :=
  eq_empty_iff_forall_notMem.2 fun _ ⟨ha, hb⟩ => h (ha.trans hb)

@[to_dual (attr := simp)]
/-
**Set.Ico_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ico_eq_empty (h : ¬a < b) : Ico a b = ∅
参数：h : ¬a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.eq_empty_iff_forall_notMem`：eq_empty_iff_forall_notMem {s : Set α} :
 s = ∅ ↔ forall x, x ∉ s
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Ico_eq_empty (h : ¬a < b) : Ico a b = ∅ :=
  eq_empty_iff_forall_notMem.2 fun _ hab => h (hab.1.trans_lt hab.2)

@[simp, to_dual self]
/-
**Set.Ioo_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioo_eq_empty (h : ¬a < b) : Ioo a b = ∅
参数：h : ¬a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.eq_empty_iff_forall_notMem`：eq_empty_iff_forall_notMem {s : Set α} :
 s = ∅ ↔ forall x, x ∉ s
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
-/
theorem Ioo_eq_empty (h : ¬a < b) : Ioo a b = ∅ :=
  eq_empty_iff_forall_notMem.2 fun _ ⟨ha, hb⟩ => h (ha.trans hb)

@[simp, to_dual self]
/-
**Set.Icc_eq_empty_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Icc_eq_empty_of_lt (h : b < a) : Icc a b = ∅
参数：h : b < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Icc_eq_empty`：Icc_eq_empty (h : ¬a <= b) : Icc a b = ∅
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
-/
theorem Icc_eq_empty_of_lt (h : b < a) : Icc a b = ∅ :=
  Icc_eq_empty h.not_ge

@[to_dual (attr := simp)]
/-
**Set.Ico_eq_empty_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ico_eq_empty_of_le (h : b <= a) : Ico a b = ∅
参数：h : b <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Ico_eq_empty`：Ico_eq_empty (h : ¬a < b) : Ico a b = ∅
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
-/
theorem Ico_eq_empty_of_le (h : b ≤ a) : Ico a b = ∅ :=
  Ico_eq_empty h.not_gt

@[simp, to_dual self]
/-
**Set.Ioo_eq_empty_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioo_eq_empty_of_le (h : b <= a) : Ioo a b = ∅
参数：h : b <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Ioo_eq_empty`：Ioo_eq_empty (h : ¬a < b) : Ioo a b = ∅
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
-/
theorem Ioo_eq_empty_of_le (h : b ≤ a) : Ioo a b = ∅ :=
  Ioo_eq_empty h.not_gt

@[to_dual]
/-
**Set.Ico_self** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ico_self (a : α) : Ico a a = ∅
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Ico_eq_empty`：Ico_eq_empty (h : ¬a < b) : Ico a b = ∅
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
-/
theorem Ico_self (a : α) : Ico a a = ∅ :=
  Ico_eq_empty <| lt_irrefl _
/-
**Set.Ioo_self** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioo_self (a : α) : Ioo a a = ∅
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Ioo_eq_empty`：Ioo_eq_empty (h : ¬a < b) : Ioo a b = ∅
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
-/
theorem Ioo_self (a : α) : Ioo a a = ∅ :=
  Ioo_eq_empty <| lt_irrefl _

/-- If `a ≤ b`, then `(-∞, a) ⊆ (-∞, b)`. In preorders, this is just an implication. If you need
the equivalence in linear orders, use `Iio_subset_Iio_iff`. -/
@[to_dual (attr := gcongr)
/-- If `a ≤ b`, then `(b, +∞) ⊆ (a, +∞)`. In preorders, this is just an implication. If you need
the equivalence in linear orders, use `Ioi_subset_Ioi_iff`. -/]
/-
**Set.Iio_subset_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iio_subset_Iio (h : a <= b) : Iio a subseteq Iio b
参数：h : a <= b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
-/
theorem Iio_subset_Iio (h : a ≤ b) : Iio a ⊆ Iio b := fun _ hx => lt_of_lt_of_le hx h

/-- If `a < b`, then `(-∞, a) ⊂ (-∞, b)`. In preorders, this is just an implication. If you need
the equivalence in linear orders, use `Iio_ssubset_Iio_iff`. -/
@[to_dual (attr := gcongr)
/-- If `a < b`, then `(b, +∞) ⊂ (a, +∞)`. In preorders, this is just an implication. If you need
the equivalence in linear orders, use `Ioi_ssubset_Ioi_iff`. -/]
/-
**Set.Iio_ssubset_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iio_ssubset_Iio (h : a < b) : Iio a ⊂ Iio b
参数：h : a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.ssubset_iff_of_subset`：ssubset_iff_of_subset {s t : Set α} (h : s su
bseteq t) : s ⊂ t ↔ exists x in t, x ∉ s
· 使用定理 `Set.Iio_subset_Iio`：Iio_subset_Iio (h : a <= b) : Iio a subseteq Iio b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
-/
theorem Iio_ssubset_Iio (h : a < b) : Iio a ⊂ Iio b :=
  (ssubset_iff_of_subset (Iio_subset_Iio h.le)).mpr ⟨a, h, lt_irrefl a⟩

@[to_dual (attr := simp, gcongr)]
/-
**Set.Iic_subset_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iic_subset_Iic : Iic a subseteq Iic b ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.self_mem_Ici`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, a ∈ Set.
Ici a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem Iic_subset_Iic : Iic a ⊆ Iic b ↔ a ≤ b :=
  ⟨fun h => h self_mem_Ici, fun h _ hx ↦ hx.trans h⟩

@[to_dual (attr := simp, gcongr)]
/-
**Set.Iic_ssubset_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iic_ssubset_Iic : Iic a ⊂ Iic b ↔ a < b where mp h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.ssubset_iff_exists`：ssubset_iff_exists {s t : Set α} : s ⊂ t ↔ s sub
seteq t ∧ exists x in t, x ∉ s
· 使用引理 `lt_of_le_not_ge`：lt_of_le_not_ge (hab : a <= b) (hba : ¬ b <= a) : a < b
· 使用定理 `Set.Iic_subset_Iic`：Iic_subset_Iic : Iic a subseteq Iic b ↔ a <= b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.ssubset_iff_of_subset`：ssubset_iff_of_subset {s t : Set α} (h : s su
bseteq t) : s ⊂ t ↔ exists x in t, x ∉ s
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Set.self_mem_Iic`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, a ∈ Set.
Iic a
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
-/
theorem Iic_ssubset_Iic : Iic a ⊂ Iic b ↔ a < b where
  mp h := by
    obtain ⟨ab, c, cb, ac⟩ := ssubset_iff_exists.mp h
    exact lt_of_le_not_ge (Iic_subset_Iic.mp ab) (fun h' ↦ ac (cb.trans h'))
  mpr h := (ssubset_iff_of_subset (Iic_subset_Iic.mpr h.le)).mpr
    ⟨b, self_mem_Iic, fun h' => h.not_ge h'⟩

@[to_dual (attr := simp, gcongr strict)]
/-
**Set.Iic_subset_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iic_subset_Iio : Iic a subseteq Iio b ↔ a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.self_mem_Iic`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, a ∈ Set.
Iic a
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
-/
theorem Iic_subset_Iio : Iic a ⊆ Iio b ↔ a < b :=
  ⟨fun h => h self_mem_Iic, fun h _ hx => lt_of_le_of_lt hx h⟩

@[to_dual]
/-
**Set.Iio_subset_Iic_self** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iio_subset_Iic_self : Iio a subseteq Iic a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem Iio_subset_Iic_self : Iio a ⊆ Iic a := fun _ hx => le_of_lt hx

/-- If `a ≤ b`, then `(-∞, a) ⊆ (-∞, b]`. In preorders, this is just an implication. If you need
the equivalence in dense linear orders, use `Iio_subset_Iic_iff`. -/
@[to_dual
/-- If `a ≤ b`, then `(b, +∞) ⊆ [a, +∞)`. In preorders, this is just an implication. If you need
the equivalence in dense linear orders, use `Ioi_subset_Ici_iff`. -/]
/-
**Set.Iio_subset_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iio_subset_Iic (h : a <= b) : Iio a subseteq Iic b
参数：h : a <= b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.Iio_subset_Iio`：Iio_subset_Iio (h : a <= b) : Iio a subseteq Iio b
· 使用定理 `Set.Iio_subset_Iic_self`：Iio_subset_Iic_self : Iio a subseteq Iic a
-/
theorem Iio_subset_Iic (h : a ≤ b) : Iio a ⊆ Iic b :=
  (Iio_subset_Iio h).trans Iio_subset_Iic_self

@[to_dual]
/-
**Set.Iio_ssubset_Iic_self** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iio_ssubset_Iic_self : Iio a ⊂ Iic a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Iio_subset_Iic_self`：Iio_subset_Iic_self : Iio a subseteq Iic a
· 使用定理 `LT.lt.false`：∀ {α : Type u_2} [inst : Preorder α] {a : α}, a < a → False
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem Iio_ssubset_Iic_self : Iio a ⊂ Iic a :=
  ⟨Iio_subset_Iic_self, fun h => (h le_rfl).false⟩

@[gcongr, to_dual self (reorder := a₁ b₁, a₂ b₂, ha hb)]
/-
**Set.Ioo_subset_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioo_subset_Ioo (ha : a₂ <= a₁) (hb : b₁ <= b₂) : Ioo a₁ b₁ subseteq Ioo a₂
 b₂
参数：ha : a₂ <= a₁；hb : b₁ <= b₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
-/
theorem Ioo_subset_Ioo (ha : a₂ ≤ a₁) (hb : b₁ ≤ b₂) : Ioo a₁ b₁ ⊆ Ioo a₂ b₂ := fun _ ⟨hx₁, hx₂⟩ =>
  ⟨ha.trans_lt hx₁, hx₂.trans_le hb⟩

to_dual_name_hint Left Right

@[to_dual]
/-
**Set.Ioo_subset_Ioo_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioo_subset_Ioo_left (h : a₁ <= a₂) : Ioo a₂ b subseteq Ioo a₁ b
参数：h : a₁ <= a₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Ioo_subset_Ioo`：Ioo_subset_Ioo (ha : a₂ <= a₁) (hb : b₁ <= b₂) : Ioo
 a₁ b₁ subseteq Ioo a₂ b₂
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem Ioo_subset_Ioo_left (h : a₁ ≤ a₂) : Ioo a₂ b ⊆ Ioo a₁ b :=
  Ioo_subset_Ioo h le_rfl

@[to_dual (attr := gcongr) (reorder := ha hb)]
/-
**Set.Ico_subset_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ico_subset_Ico (ha : a₂ <= a₁) (hb : b₁ <= b₂) : Ico a₁ b₁ subseteq Ico a₂
 b₂
参数：ha : a₂ <= a₁；hb : b₁ <= b₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Ico_subset_Ico (ha : a₂ ≤ a₁) (hb : b₁ ≤ b₂) : Ico a₁ b₁ ⊆ Ico a₂ b₂ := fun _ hx =>
  ⟨ha.trans hx.1, hx.2.trans_le hb⟩

@[to_dual]
/-
**Set.Ico_subset_Ico_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ico_subset_Ico_left (h : a₁ <= a₂) : Ico a₂ b subseteq Ico a₁ b
参数：h : a₁ <= a₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Ico_subset_Ico`：Ico_subset_Ico (ha : a₂ <= a₁) (hb : b₁ <= b₂) : Ico
 a₁ b₁ subseteq Ico a₂ b₂
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem Ico_subset_Ico_left (h : a₁ ≤ a₂) : Ico a₂ b ⊆ Ico a₁ b :=
  Ico_subset_Ico h le_rfl

@[to_dual]
/-
**Set.Ioc_subset_Ioc_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioc_subset_Ioc_left (h : a₁ <= a₂) : Ioc a₂ b subseteq Ioc a₁ b
参数：h : a₁ <= a₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Ioc_subset_Ioc`：∀ {α : Type u_1} [inst : Preorder α] {a₁ a₂ b₁ b₂ : 
α}, b₂ ≤ b₁ → a₁ ≤ a₂ → Set.Ioc b₁ a₁ ⊆ Set.Ioc b₂ a₂
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem Ioc_subset_Ioc_left (h : a₁ ≤ a₂) : Ioc a₂ b ⊆ Ioc a₁ b :=
  Ioc_subset_Ioc h le_rfl

@[gcongr, to_dual self (reorder := a₁ b₁, a₂ b₂, ha hb)]
/-
**Set.Icc_subset_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Icc_subset_Icc (ha : a₂ <= a₁) (hb : b₁ <= b₂) : Icc a₁ b₁ subseteq Icc a₂
 b₂
参数：ha : a₂ <= a₁；hb : b₁ <= b₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
-/
theorem Icc_subset_Icc (ha : a₂ ≤ a₁) (hb : b₁ ≤ b₂) : Icc a₁ b₁ ⊆ Icc a₂ b₂ := fun _ ⟨hx₁, hx₂⟩ =>
  ⟨ha.trans hx₁, le_trans hx₂ hb⟩

@[to_dual]
/-
**Set.Icc_subset_Icc_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Icc_subset_Icc_left (h : a₁ <= a₂) : Icc a₂ b subseteq Icc a₁ b
参数：h : a₁ <= a₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Icc_subset_Icc`：Icc_subset_Icc (ha : a₂ <= a₁) (hb : b₁ <= b₂) : Icc
 a₁ b₁ subseteq Icc a₂ b₂
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem Icc_subset_Icc_left (h : a₁ ≤ a₂) : Icc a₂ b ⊆ Icc a₁ b :=
  Icc_subset_Icc h le_rfl

@[to_dual (reorder := ha hb)]
/-
**Set.Icc_ssubset_Icc_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Icc_ssubset_Icc_left (h₂ : a₂ <= b₂) (ha : a₂ < a₁) (hb : b₁ <= b₂) : Icc 
a₁ b₁ ⊂ Icc a₂ b₂
参数：h₂ : a₂ <= b₂；ha : a₂ < a₁；hb : b₁ <= b₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.ssubset_iff_of_subset`：ssubset_iff_of_subset {s t : Set α} (h : s su
bseteq t) : s ⊂ t ↔ exists x in t, x ∉ s
· 使用定理 `Set.Icc_subset_Icc`：Icc_subset_Icc (ha : a₂ <= a₁) (hb : b₁ <= b₂) : Icc
 a₁ b₁ subseteq Icc a₂ b₂
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Set.left_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ Se
t.Icc a b ↔ a ≤ b
· 使用定理 `not_and`：∀ {a b : Prop}, ¬(a ∧ b) ↔ a → ¬b
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
-/
theorem Icc_ssubset_Icc_left (h₂ : a₂ ≤ b₂) (ha : a₂ < a₁) (hb : b₁ ≤ b₂) : Icc a₁ b₁ ⊂ Icc a₂ b₂ :=
  (ssubset_iff_of_subset (Icc_subset_Icc (le_of_lt ha) hb)).mpr
    ⟨a₂, left_mem_Icc.mpr h₂, not_and.mpr fun f _ => lt_irrefl a₂ (ha.trans_le f)⟩

@[to_dual (reorder := ha hb)]
/-
**Set.Ico_subset_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ico_subset_Ioo (ha : a₂ < a₁) (hb : b₁ <= b₂) : Ico a₁ b₁ subseteq Ioo a₂ 
b₂
参数：ha : a₂ < a₁；hb : b₁ <= b₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Ico_subset_Ioo (ha : a₂ < a₁) (hb : b₁ ≤ b₂) : Ico a₁ b₁ ⊆ Ioo a₂ b₂ := fun _ hx ↦
  ⟨ha.trans_le hx.1, hx.2.trans_le hb⟩

@[to_dual (attr := gcongr strict)]
/-
**Set.Ico_subset_Ioo_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ico_subset_Ioo_left (h : a₁ < a₂) : Ico a₂ b subseteq Ioo a₁ b
参数：h : a₁ < a₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Ico_subset_Ioo`：Ico_subset_Ioo (ha : a₂ < a₁) (hb : b₁ <= b₂) : Ico 
a₁ b₁ subseteq Ioo a₂ b₂
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem Ico_subset_Ioo_left (h : a₁ < a₂) : Ico a₂ b ⊆ Ioo a₁ b :=
  Ico_subset_Ioo h le_rfl

@[to_dual (reorder := ha hb)]
/-
**Set.Icc_subset_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Icc_subset_Ioc (ha : a₂ < a₁) (hb : b₁ <= b₂) : Icc a₁ b₁ subseteq Ioc a₂ 
b₂
参数：ha : a₂ < a₁；hb : b₁ <= b₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Icc_subset_Ioc (ha : a₂ < a₁) (hb : b₁ ≤ b₂) : Icc a₁ b₁ ⊆ Ioc a₂ b₂ := fun _ hx ↦
  ⟨ha.trans_le hx.1, hx.2.trans hb⟩

@[to_dual (attr := gcongr strict)]
/-
**Set.Icc_subset_Ioc_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Icc_subset_Ioc_left (h : a₁ < a₂) : Icc a₂ b subseteq Ioc a₁ b
参数：h : a₁ < a₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Icc_subset_Ioc`：Icc_subset_Ioc (ha : a₂ < a₁) (hb : b₁ <= b₂) : Icc 
a₁ b₁ subseteq Ioc a₂ b₂
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem Icc_subset_Ioc_left (h : a₁ < a₂) : Icc a₂ b ⊆ Ioc a₁ b :=
  Icc_subset_Ioc h le_rfl

@[to_dual self (reorder := a₁ b₁, a₂ b₂, ha hb)]
/-
**Set.Icc_subset_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Icc_subset_Ioo (ha : a₂ < a₁) (hb : b₁ < b₂) : Icc a₁ b₁ subseteq Ioo a₂ b
₂
参数：ha : a₂ < a₁；hb : b₁ < b₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.Icc_subset_Ioc_left`：Icc_subset_Ioc_left (h : a₁ < a₂) : Icc a₂ b su
bseteq Ioc a₁ b
· 使用定理 `Set.Ioc_subset_Ioo_right`：∀ {α : Type u_1} [inst : Preorder α] {a₁ a₂ b 
: α}, a₂ < a₁ → Set.Ioc b a₂ ⊆ Set.Ioo b a₁
-/
theorem Icc_subset_Ioo (ha : a₂ < a₁) (hb : b₁ < b₂) : Icc a₁ b₁ ⊆ Ioo a₂ b₂ :=
  (Icc_subset_Ioc_left ha).trans (Ioc_subset_Ioo_right hb)
/-
**Set.Ico_subset_Iio_self** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.Ico a b ⊆ Set.Iio b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
@[to_dual] theorem Ico_subset_Iio_self : Ico a b ⊆ Iio b := fun _ => And.right
/-
**Set.Ioo_subset_Iio_self** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.Ioo a b ⊆ Set.Iio b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
@[to_dual] theorem Ioo_subset_Iio_self : Ioo a b ⊆ Iio b := fun _ => And.right
/-
**Set.Ioc_subset_Iic_self** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.Ioc a b ⊆ Set.Iic b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
@[to_dual] theorem Ioc_subset_Iic_self : Ioc a b ⊆ Iic b := fun _ => And.right
/-
**Set.Icc_subset_Iic_self** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.Icc a b ⊆ Set.Iic b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
@[to_dual] theorem Icc_subset_Iic_self : Icc a b ⊆ Iic b := fun _ => And.right
/-
**Set.Ioo_subset_Ico_self** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.Ioo a b ⊆ Set.Ico a b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.imp_left`：∀ {a b c : Prop}, (a → b) → a ∧ c → b ∧ c
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
@[to_dual] theorem Ioo_subset_Ico_self : Ioo a b ⊆ Ico a b := fun _ => And.imp_left le_of_lt
/-
**Set.Ioc_subset_Icc_self** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.Ioc a b ⊆ Set.Icc a b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.imp_left`：∀ {a b c : Prop}, (a → b) → a ∧ c → b ∧ c
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
@[to_dual] theorem Ioc_subset_Icc_self : Ioc a b ⊆ Icc a b := fun _ => And.imp_left le_of_lt

@[to_dual self]
/-
**Set.Ioo_subset_Icc_self** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioo_subset_Icc_self : Ioo a b subseteq Icc a b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.Ioo_subset_Ico_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo a b ⊆ Set.Ico a b
· 使用定理 `Set.Ico_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ico b a ⊆ Set.Icc b a
-/
theorem Ioo_subset_Icc_self : Ioo a b ⊆ Icc a b :=
  Ioo_subset_Ico_self.trans Ico_subset_Icc_self

@[to_dual none]
/-
**Set.Icc_subset_Icc_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Icc_subset_Icc_iff (h₁ : a₁ <= b₁) : Icc a₁ b₁ subseteq Icc a₂ b₂ ↔ a₂ <= 
a₁ ∧ b₁ <= b₂
参数：h₁ : a₁ <= b₁。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem Icc_subset_Icc_iff (h₁ : a₁ ≤ b₁) : Icc a₁ b₁ ⊆ Icc a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ ≤ b₂ :=
  ⟨fun h => ⟨(h ⟨le_rfl, h₁⟩).1, (h ⟨h₁, le_rfl⟩).2⟩, fun ⟨h, h'⟩ _ hx =>
    ⟨h.trans hx.1, hx.2.trans h'⟩⟩

@[to_dual none]
/-
**Set.Icc_subset_Ioo_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Icc_subset_Ioo_iff (h₁ : a₁ <= b₁) : Icc a₁ b₁ subseteq Ioo a₂ b₂ ↔ a₂ < a
₁ ∧ b₁ < b₂
参数：h₁ : a₁ <= b₁。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
-/
theorem Icc_subset_Ioo_iff (h₁ : a₁ ≤ b₁) : Icc a₁ b₁ ⊆ Ioo a₂ b₂ ↔ a₂ < a₁ ∧ b₁ < b₂ :=
  ⟨fun h => ⟨(h ⟨le_rfl, h₁⟩).1, (h ⟨h₁, le_rfl⟩).2⟩, fun ⟨h, h'⟩ _ hx =>
    ⟨h.trans_le hx.1, hx.2.trans_lt h'⟩⟩

@[to_dual none]
/-
**Set.Icc_subset_Ico_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Icc_subset_Ico_iff (h₁ : a₁ <= b₁) : Icc a₁ b₁ subseteq Ico a₂ b₂ ↔ a₂ <= 
a₁ ∧ b₁ < b₂
参数：h₁ : a₁ <= b₁。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
-/
theorem Icc_subset_Ico_iff (h₁ : a₁ ≤ b₁) : Icc a₁ b₁ ⊆ Ico a₂ b₂ ↔ a₂ ≤ a₁ ∧ b₁ < b₂ :=
  ⟨fun h => ⟨(h ⟨le_rfl, h₁⟩).1, (h ⟨h₁, le_rfl⟩).2⟩, fun ⟨h, h'⟩ _ hx =>
    ⟨h.trans hx.1, hx.2.trans_lt h'⟩⟩

@[to_dual none]
/-
**Set.Icc_subset_Ioc_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Icc_subset_Ioc_iff (h₁ : a₁ <= b₁) : Icc a₁ b₁ subseteq Ioc a₂ b₂ ↔ a₂ < a
₁ ∧ b₁ <= b₂
参数：h₁ : a₁ <= b₁。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem Icc_subset_Ioc_iff (h₁ : a₁ ≤ b₁) : Icc a₁ b₁ ⊆ Ioc a₂ b₂ ↔ a₂ < a₁ ∧ b₁ ≤ b₂ :=
  ⟨fun h => ⟨(h ⟨le_rfl, h₁⟩).1, (h ⟨h₁, le_rfl⟩).2⟩, fun ⟨h, h'⟩ _ hx =>
    ⟨h.trans_le hx.1, hx.2.trans h'⟩⟩

@[to_dual]
/-
**Set.Icc_subset_Ioi_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Icc_subset_Ioi_iff (h₁ : a₁ <= b₁) : Icc a₁ b₁ subseteq Ioi a₂ ↔ a₂ < a₁
参数：h₁ : a₁ <= b₁。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem Icc_subset_Ioi_iff (h₁ : a₁ ≤ b₁) : Icc a₁ b₁ ⊆ Ioi a₂ ↔ a₂ < a₁ :=
  ⟨fun h => h ⟨le_rfl, h₁⟩, fun h _ hx => h.trans_le hx.1⟩

@[to_dual]
/-
**Set.Icc_subset_Ici_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Icc_subset_Ici_iff (h₁ : a₁ <= b₁) : Icc a₁ b₁ subseteq Ici a₂ ↔ a₂ <= a₁
参数：h₁ : a₁ <= b₁。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem Icc_subset_Ici_iff (h₁ : a₁ ≤ b₁) : Icc a₁ b₁ ⊆ Ici a₂ ↔ a₂ ≤ a₁ :=
  ⟨fun h => h ⟨le_rfl, h₁⟩, fun h _ hx => h.trans hx.1⟩
/-
**Set.Ici_inter_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.Ici a ∩ Set.Iic b = Se
t.Icc a b
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_dual] theorem Ici_inter_Iic : Ici a ∩ Iic b = Icc a b := rfl
/-
**Set.Ici_inter_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.Ici a ∩ Set.Iio b = Se
t.Ico a b
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_dual] theorem Ici_inter_Iio : Ici a ∩ Iio b = Ico a b := rfl
/-
**Set.Ioi_inter_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.Ioi a ∩ Set.Iic b = Se
t.Ioc a b
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_dual] theorem Ioi_inter_Iic : Ioi a ∩ Iic b = Ioc a b := rfl
/-
**Set.Ioi_inter_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.Ioi a ∩ Set.Iio b = Se
t.Ioo a b
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_dual] theorem Ioi_inter_Iio : Ioi a ∩ Iio b = Ioo a b := rfl
/-
**Set.mem_Icc_of_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.Ioo a b → x ∈ Se
t.Icc a b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Ioo_subset_Icc_self`：Ioo_subset_Icc_self : Ioo a b subseteq Icc a b
-/
@[to_dual self] theorem mem_Icc_of_Ioo (h : x ∈ Ioo a b) : x ∈ Icc a b := Ioo_subset_Icc_self h
/-
**Set.mem_Ico_of_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.Ioo a b → x ∈ Se
t.Ico a b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Ioo_subset_Ico_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo a b ⊆ Set.Ico a b
-/
@[to_dual] theorem mem_Ico_of_Ioo (h : x ∈ Ioo a b) : x ∈ Ico a b := Ioo_subset_Ico_self h
/-
**Set.mem_Icc_of_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.Ioc a b → x ∈ Se
t.Icc a b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Ioc_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc a b ⊆ Set.Icc a b
-/
@[to_dual] theorem mem_Icc_of_Ioc (h : x ∈ Ioc a b) : x ∈ Icc a b := Ioc_subset_Icc_self h
/-
**Set.mem_Iic_of_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {a x : α}, x ∈ Set.Iio a → x ∈ Set.Ii
c a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Iio_subset_Iic_self`：Iio_subset_Iic_self : Iio a subseteq Iic a
-/
@[to_dual] theorem mem_Iic_of_Iio (h : x ∈ Iio a) : x ∈ Iic a := Iio_subset_Iic_self h

@[to_dual self]
/-
**Set.Icc_eq_empty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Icc_eq_empty_iff : Icc a b = ∅ ↔ ¬a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₃`：contrapose_iff₃ {p q : Prop} 
: (¬ p ↔ q) -> (p ↔ ¬ q)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.nonempty_Icc`：nonempty_Icc : (Icc a b).Nonempty ↔ a <= b
-/
theorem Icc_eq_empty_iff : Icc a b = ∅ ↔ ¬a ≤ b := by
  contrapose!; exact nonempty_Icc

@[to_dual]
/-
**Set.Ico_eq_empty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ico_eq_empty_iff : Ico a b = ∅ ↔ ¬a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₃`：contrapose_iff₃ {p q : Prop} 
: (¬ p ↔ q) -> (p ↔ ¬ q)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.nonempty_Ico`：nonempty_Ico : (Ico a b).Nonempty ↔ a < b
-/
theorem Ico_eq_empty_iff : Ico a b = ∅ ↔ ¬a < b := by
  contrapose!; exact nonempty_Ico

@[to_dual self]
/-
**Set.Ioo_eq_empty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioo_eq_empty_iff [DenselyOrdered α] : Ioo a b = ∅ ↔ ¬a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₃`：contrapose_iff₃ {p q : Prop} 
: (¬ p ↔ q) -> (p ↔ ¬ q)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.nonempty_Ioo`：nonempty_Ioo [DenselyOrdered α] : (Ioo a b).Nonempty ↔
 a < b
-/
theorem Ioo_eq_empty_iff [DenselyOrdered α] : Ioo a b = ∅ ↔ ¬a < b := by
  contrapose!; exact nonempty_Ioo

@[to_dual]
/-
**Set._root_.IsTop.Iic_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsTop.Iic_eq (h : IsTop a) : Iic a = univ :=
  eq_univ_of_forall h

@[to_dual (attr := simp)]
/-
**Set.Iio_eq_empty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iio_eq_empty_iff : Iio a = ∅ ↔ IsMin a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Iio_eq_empty_iff : Iio a = ∅ ↔ IsMin a := by
  simp only [isMin_iff_forall_not_lt, eq_empty_iff_forall_notMem, mem_Iio]

@[to_dual (attr := simp)] alias ⟨_, _root_.IsMin.Iio_eq⟩ := Iio_eq_empty_iff

@[to_dual (attr := simp)]
/-
**Set.Iio_nonempty** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：Iio_nonempty : (Iio a).Nonempty ↔ ¬ IsMin a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Iio_nonempty : (Iio a).Nonempty ↔ ¬ IsMin a := by simp [nonempty_iff_ne_empty]

@[to_dual]
/-
**Set.Iic_inter_Ioc_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iic_inter_Ioc_of_le (h : a <= c) : Iic a inter Ioc b c = Ioc b a
参数：h : a <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem Iic_inter_Ioc_of_le (h : a ≤ c) : Iic a ∩ Ioc b c = Ioc b a :=
  ext fun _ => ⟨fun H => ⟨H.2.1, H.1⟩, fun H => ⟨H.2, H.1, H.2.trans h⟩⟩

@[to_dual notMem_Icc_of_gt]
/-
**Set.notMem_Icc_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：notMem_Icc_of_lt (ha : c < a) : c ∉ Icc a b
参数：ha : c < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem notMem_Icc_of_lt (ha : c < a) : c ∉ Icc a b := fun h => ha.not_ge h.1

@[to_dual notMem_Ioc_of_gt]
/-
**Set.notMem_Ico_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：notMem_Ico_of_lt (ha : c < a) : c ∉ Ico a b
参数：ha : c < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem notMem_Ico_of_lt (ha : c < a) : c ∉ Ico a b := fun h => ha.not_ge h.1

@[deprecated (since := "2026-02-10")] alias notMem_Ioi_self := self_notMem_Ioi

@[deprecated (since := "2026-02-10")] alias notMem_Iio_self := self_notMem_Iio

@[to_dual notMem_Ico_of_ge]
/-
**Set.notMem_Ioc_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：notMem_Ioc_of_le (ha : c <= a) : c ∉ Ioc a b
参数：ha : c <= a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem notMem_Ioc_of_le (ha : c ≤ a) : c ∉ Ioc a b := fun h => lt_irrefl _ <| h.1.trans_le ha

@[to_dual notMem_Ioo_of_ge]
/-
**Set.notMem_Ioo_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：notMem_Ioo_of_le (ha : c <= a) : c ∉ Ioo a b
参数：ha : c <= a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem notMem_Ioo_of_le (ha : c ≤ a) : c ∉ Ioo a b := fun h => lt_irrefl _ <| h.1.trans_le ha

section matched_intervals

/-
**Set.Icc_eq_Ioc_same_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.Icc a b = Set.Ioc a b 
↔ ¬a ≤ b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.ext_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ ∀ (x : α), x ∈ a ↔ x 
∈ b
· 使用定理 `Set.Icc_eq_empty`：Icc_eq_empty (h : ¬a <= b) : Icc a b = ∅
· 使用定理 `Set.Ioc_eq_empty`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, ¬b < a
 → Set.Ioc b a = ∅
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
@[to_dual (attr := simp)] theorem Icc_eq_Ioc_same_iff : Icc a b = Ioc a b ↔ ¬a ≤ b where
  mp h := by simpa using Set.ext_iff.mp h a
  mpr h := by rw [Icc_eq_empty h, Ioc_eq_empty (mt le_of_lt h)]
/-
**Set.Ioc_eq_Icc_same_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.Ioc a b = Set.Icc a b 
↔ ¬a ≤ b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Set.Icc_eq_Ioc_same_iff`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Icc a b = Set.Ioc a b ↔ ¬a ≤ b
-/
@[to_dual (attr := simp)] theorem Ioc_eq_Icc_same_iff : Ioc a b = Icc a b ↔ ¬a ≤ b :=
  eq_comm.trans Icc_eq_Ioc_same_iff
/-
**Set.Icc_eq_Ioo_same_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.Icc a b = Set.Ioo a b 
↔ ¬a ≤ b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.ext_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ ∀ (x : α), x ∈ a ↔ x 
∈ b
· 使用定理 `Set.Icc_eq_empty`：Icc_eq_empty (h : ¬a <= b) : Icc a b = ∅
· 使用定理 `Set.Ioo_eq_empty`：Ioo_eq_empty (h : ¬a < b) : Ioo a b = ∅
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
@[simp, to_dual self] theorem Icc_eq_Ioo_same_iff : Icc a b = Ioo a b ↔ ¬a ≤ b where
  mp h := by simpa using Set.ext_iff.mp h b
  mpr h := by rw [Icc_eq_empty h, Ioo_eq_empty (mt le_of_lt h)]
/-
**Set.Ioo_eq_Icc_same_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.Ioo a b = Set.Icc a b 
↔ ¬a ≤ b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Set.Icc_eq_Ioo_same_iff`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Icc a b = Set.Ioo a b ↔ ¬a ≤ b
-/
@[simp, to_dual self] theorem Ioo_eq_Icc_same_iff : Ioo a b = Icc a b ↔ ¬a ≤ b :=
  eq_comm.trans Icc_eq_Ioo_same_iff
/-
**Set.Ioc_eq_Ico_same_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.Ioc a b = Set.Ico a b 
↔ ¬a < b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `false_iff`：∀ (p : Prop), (False ↔ p) = ¬p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.ext_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ ∀ (x : α), x ∈ a ↔ x 
∈ b
· 使用定理 `Set.Ioc_eq_empty`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, ¬b < a
 → Set.Ioc b a = ∅
· 使用定理 `Set.Ico_eq_empty`：Ico_eq_empty (h : ¬a < b) : Ico a b = ∅
-/
@[to_dual (attr := simp)] theorem Ioc_eq_Ico_same_iff : Ioc a b = Ico a b ↔ ¬a < b where
  mp h := by simpa using Set.ext_iff.mp h a
  mpr h := by rw [Ioc_eq_empty h, Ico_eq_empty h]
/-
**Set.Ioo_eq_Ioc_same_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.Ioo a b = Set.Ioc a b 
↔ ¬a < b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `false_iff`：∀ (p : Prop), (False ↔ p) = ¬p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.ext_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ ∀ (x : α), x ∈ a ↔ x 
∈ b
· 使用定理 `Set.Ioo_eq_empty`：Ioo_eq_empty (h : ¬a < b) : Ioo a b = ∅
· 使用定理 `Set.Ioc_eq_empty`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, ¬b < a
 → Set.Ioc b a = ∅
-/
@[to_dual (attr := simp)] theorem Ioo_eq_Ioc_same_iff : Ioo a b = Ioc a b ↔ ¬a < b where
  mp h := by simpa using Set.ext_iff.mp h b
  mpr h := by rw [Ioo_eq_empty h, Ioc_eq_empty h]
/-
**Set.Ioc_eq_Ioo_same_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.Ioc a b = Set.Ioo a b 
↔ ¬a < b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Set.Ioo_eq_Ioc_same_iff`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo a b = Set.Ioc a b ↔ ¬a < b
-/
@[to_dual (attr := simp)] theorem Ioc_eq_Ioo_same_iff : Ioc a b = Ioo a b ↔ ¬a < b :=
  eq_comm.trans Ioo_eq_Ioc_same_iff

end matched_intervals

@[to_additive (attr := simp)]
/-
**Set.Ici_one_eq_univ** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：Ici_one_eq_univ [One α] [IsBotOneClass α] : Ici (1 : α) = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Ici_one_eq_univ [One α] [IsBotOneClass α] : Ici (1 : α) = univ := by ext; simp

end Preorder

section PartialOrder

variable [PartialOrder α] {a b c : α}

@[simp]
/-
**Set.Icc_self** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Icc_self (a : α) : Icc a a = {a}
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem Icc_self (a : α) : Icc a a = {a} :=
  Set.ext <| by simp [Icc, le_antisymm_iff, and_comm]
/-
**Set.instIccUnique** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：instIccUnique : Unique (Icc a a) where default
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instIccUnique : Unique (Icc a a) where
  default := ⟨a, by simp⟩
  uniq y := Subtype.ext <| by simpa using y.2

@[simp, to_dual none]
/-
**Set.Icc_eq_singleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Icc_eq_singleton_iff : Icc a b = {c} ↔ a = c ∧ b = c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.nonempty_Icc`：nonempty_Icc : (Icc a b).Nonempty ↔ a <= b
· 使用定理 `Eq.subst`：∀ {α : Sort u} {motive : α → Prop} {a b : α}, a = b → motive a
 → motive b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.singleton_nonempty`：singleton_nonempty (a : α) : ({a} : Set α).Nonem
pty
· 使用定理 `Set.eq_of_mem_singleton`：eq_of_mem_singleton {x y : α} (h : x in ({y} : 
Set α)) : x = y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.left_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ Se
t.Icc a b ↔ a ≤ b
· 使用定理 `Set.right_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ S
et.Icc b a ↔ b ≤ a
· 使用定理 `Set.Icc_self`：Icc_self (a : α) : Icc a a = {a}
-/
theorem Icc_eq_singleton_iff : Icc a b = {c} ↔ a = c ∧ b = c := by
  refine ⟨fun h => ?_, ?_⟩
  · have hab : a ≤ b := nonempty_Icc.1 (h.symm.subst <| singleton_nonempty c)
    exact
      ⟨eq_of_mem_singleton <| h ▸ left_mem_Icc.2 hab,
        eq_of_mem_singleton <| h ▸ right_mem_Icc.2 hab⟩
  · rintro ⟨rfl, rfl⟩
    exact Icc_self _

@[to_dual self]
/-
**Set.subsingleton_Icc_of_ge** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：subsingleton_Icc_of_ge (hba : b <= a) : Set.Subsingleton (Icc a b)
参数：hba : b <= a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
-/
lemma subsingleton_Icc_of_ge (hba : b ≤ a) : Set.Subsingleton (Icc a b) :=
  fun _x ⟨hax, hxb⟩ _y ⟨hay, hyb⟩ ↦ le_antisymm
    (le_imp_le_of_le_of_le hxb hay hba) (le_imp_le_of_le_of_le hyb hax hba)

@[simp, to_dual self]
/-
**Set.subsingleton_Icc_iff** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：subsingleton_Icc_iff {α : Type*} [LinearOrder α] {a b : α} : Set.Subsingle
ton (Icc a b) ↔ b <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用引理 `Set.subsingleton_Icc_of_ge`：subsingleton_Icc_of_ge (hba : b <= a) : Set.
Subsingleton (Icc a b)
-/
lemma subsingleton_Icc_iff {α : Type*} [LinearOrder α] {a b : α} :
    Set.Subsingleton (Icc a b) ↔ b ≤ a := by
  refine ⟨fun h ↦ ?_, subsingleton_Icc_of_ge⟩
  contrapose! h
  exact ⟨a, ⟨le_refl _, h.le⟩, b, ⟨h.le, le_refl _⟩, h.ne⟩

@[to_dual (attr := simp)]
/-
**Set.Icc_sdiff_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Icc_sdiff_left : Icc a b \ {a} = Ioc a b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Icc_sdiff_left : Icc a b \ {a} = Ioc a b :=
  ext fun x => by simp [lt_iff_le_and_ne, eq_comm, and_right_comm]

@[deprecated (since := "2026-06-03")] alias Icc_diff_left := Icc_sdiff_left

@[to_dual (attr := simp)]
/-
**Set.Ico_sdiff_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ico_sdiff_left : Ico a b \ {a} = Ioo a b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Ico_sdiff_left : Ico a b \ {a} = Ioo a b :=
  ext fun x => by simp [and_right_comm, ← lt_iff_le_and_ne, eq_comm]

@[deprecated (since := "2026-06-03")] alias Ico_diff_left := Ico_sdiff_left

@[simp, to_dual none]
/-
**Set.Icc_sdiff_both** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Icc_sdiff_both : Icc a b \ {a, b} = Ioo a b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.insert_eq`：insert_eq (x : α) (s : Set α) : insert x s = ({x} : Set α
) union s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sdiff_sdiff`：sdiff_sdiff {u : Set α} : (s \ t) \ u = s \ (t union u)
· 使用定理 `Set.Icc_sdiff_left`：Icc_sdiff_left : Icc a b \ {a} = Ioc a b
· 使用定理 `Set.Ioc_sdiff_right`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α},
 Set.Ioc b a \ {a} = Set.Ioo b a
-/
theorem Icc_sdiff_both : Icc a b \ {a, b} = Ioo a b := by
  rw [insert_eq, ← sdiff_sdiff, Icc_sdiff_left, Ioc_sdiff_right]

@[deprecated (since := "2026-06-03")] alias Icc_diff_both := Icc_sdiff_both

@[to_dual (attr := simp)]
/-
**Set.Iic_sdiff_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iic_sdiff_right : Iic a \ {a} = Iio a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Iic_sdiff_right : Iic a \ {a} = Iio a :=
  ext fun x => by simp [lt_iff_le_and_ne]

@[deprecated (since := "2026-06-03")] alias Iic_diff_right := Iic_sdiff_right

@[to_dual (attr := simp)]
/-
**Set.Ico_sdiff_Ioo_same** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ico_sdiff_Ioo_same (h : a < b) : Ico a b \ Ioo a b = {a}
参数：h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Ico_sdiff_left`：Ico_sdiff_left : Ico a b \ {a} = Ioo a b
· 使用定理 `Set.sdiff_sdiff_cancel_left`：sdiff_sdiff_cancel_left {s t : Set α} (h : 
s subseteq t) : t \ (t \ s) = s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `Set.left_mem_Ico`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ Se
t.Ico a b ↔ a < b
-/
theorem Ico_sdiff_Ioo_same (h : a < b) : Ico a b \ Ioo a b = {a} := by
  rw [← Ico_sdiff_left, sdiff_sdiff_cancel_left (singleton_subset_iff.2 <| left_mem_Ico.2 h)]

@[deprecated (since := "2026-06-03")] alias Ico_diff_Ioo_same := Ico_sdiff_Ioo_same

@[to_dual (attr := simp)]
/-
**Set.Icc_sdiff_Ico_same** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Icc_sdiff_Ico_same (h : a <= b) : Icc a b \ Ico a b = {b}
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Icc_sdiff_right`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α},
 Set.Icc b a \ {a} = Set.Ico b a
· 使用定理 `Set.sdiff_sdiff_cancel_left`：sdiff_sdiff_cancel_left {s t : Set α} (h : 
s subseteq t) : t \ (t \ s) = s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `Set.right_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ S
et.Icc b a ↔ b ≤ a
-/
theorem Icc_sdiff_Ico_same (h : a ≤ b) : Icc a b \ Ico a b = {b} := by
  rw [← Icc_sdiff_right, sdiff_sdiff_cancel_left (singleton_subset_iff.2 <| right_mem_Icc.2 h)]

@[deprecated (since := "2026-06-03")] alias Icc_diff_Ico_same := Icc_sdiff_Ico_same

@[simp, to_dual none]
/-
**Set.Icc_sdiff_Ioo_same** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Icc_sdiff_Ioo_same (h : a <= b) : Icc a b \ Ioo a b = {a, b}
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Icc_sdiff_both`：Icc_sdiff_both : Icc a b \ {a, b} = Ioo a b
· 使用定理 `Set.sdiff_sdiff_cancel_left`：sdiff_sdiff_cancel_left {s t : Set α} (h : 
s subseteq t) : t \ (t \ s) = s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem Icc_sdiff_Ioo_same (h : a ≤ b) : Icc a b \ Ioo a b = {a, b} := by
  rw [← Icc_sdiff_both, sdiff_sdiff_cancel_left]
  simp [insert_subset_iff, h]

@[deprecated (since := "2026-06-03")] alias Icc_diff_Ioo_same := Icc_sdiff_Ioo_same

@[to_dual (attr := simp)]
/-
**Set.Iic_sdiff_Iio_same** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iic_sdiff_Iio_same : Iic a \ Iio a = {a}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Iic_sdiff_right`：Iic_sdiff_right : Iic a \ {a} = Iio a
· 使用定理 `Set.sdiff_sdiff_cancel_left`：sdiff_sdiff_cancel_left {s t : Set α} (h : 
s subseteq t) : t \ (t \ s) = s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `Set.self_mem_Iic`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, a ∈ Set.
Iic a
-/
theorem Iic_sdiff_Iio_same : Iic a \ Iio a = {a} := by
  rw [← Iic_sdiff_right, sdiff_sdiff_cancel_left (singleton_subset_iff.2 self_mem_Iic)]

@[deprecated (since := "2026-06-03")] alias Iic_diff_Iio_same := Iic_sdiff_Iio_same

@[to_dual]
/-
**Set.Iio_union_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iio_union_right : Iio a union {a} = Iic a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `le_iff_lt_or_eq`：le_iff_lt_or_eq : a <= b ↔ a < b ∨ a = b
-/
theorem Iio_union_right : Iio a ∪ {a} = Iic a :=
  ext fun _ => le_iff_lt_or_eq.symm

@[to_dual]
/-
**Set.Ioo_union_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioo_union_left (hab : a < b) : Ioo a b union {a} = Ico a b
参数：hab : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Ico_sdiff_left`：Ico_sdiff_left : Ico a b \ {a} = Ioo a b
· 使用定理 `Set.sdiff_union_self`：sdiff_union_self {s t : Set α} : s \ t union t = s
 union t
· 使用定理 `Set.union_eq_self_of_subset_right`：union_eq_self_of_subset_right {s t : 
Set α} (h : t subseteq s) : s union t = s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `Set.left_mem_Ico`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ Se
t.Ico a b ↔ a < b
-/
theorem Ioo_union_left (hab : a < b) : Ioo a b ∪ {a} = Ico a b := by
  rw [← Ico_sdiff_left, sdiff_union_self,
    union_eq_self_of_subset_right (singleton_subset_iff.2 <| left_mem_Ico.2 hab)]

@[to_dual none]
/-
**Set.Ioo_union_both** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioo_union_both (h : a <= b) : Ioo a b union {a, b} = Icc a b
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.sdiff_union_of_subset`：sdiff_union_of_subset {s t : Set α} (h : t su
bseteq s) : s \ t union t = s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.left_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ Se
t.Icc a b ↔ a ≤ b
· 使用定理 `Set.right_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ S
et.Icc b a ↔ b ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Icc_sdiff_both`：Icc_sdiff_both : Icc a b \ {a, b} = Ioo a b
-/
theorem Ioo_union_both (h : a ≤ b) : Ioo a b ∪ {a, b} = Icc a b := by
  have : (Icc a b \ {a, b}) ∪ {a, b} = Icc a b := sdiff_union_of_subset fun
    | x, .inl rfl => left_mem_Icc.mpr h
    | x, .inr rfl => right_mem_Icc.mpr h
  rw [← this, Icc_sdiff_both]

@[to_dual]
/-
**Set.Ioc_union_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioc_union_left (hab : a <= b) : Ioc a b union {a} = Icc a b
参数：hab : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Icc_sdiff_left`：Icc_sdiff_left : Icc a b \ {a} = Ioc a b
· 使用定理 `Set.sdiff_union_self`：sdiff_union_self {s t : Set α} : s \ t union t = s
 union t
· 使用定理 `Set.union_eq_self_of_subset_right`：union_eq_self_of_subset_right {s t : 
Set α} (h : t subseteq s) : s union t = s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `Set.left_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ Se
t.Icc a b ↔ a ≤ b
-/
theorem Ioc_union_left (hab : a ≤ b) : Ioc a b ∪ {a} = Icc a b := by
  rw [← Icc_sdiff_left, sdiff_union_self,
    union_eq_self_of_subset_right (singleton_subset_iff.2 <| left_mem_Icc.2 hab)]

@[to_dual (attr := simp)]
/-
**Set.Ico_insert_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ico_insert_right (h : a <= b) : insert b (Ico a b) = Icc a b
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.insert_eq`：insert_eq (x : α) (s : Set α) : insert x s = ({x} : Set α
) union s
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
· 使用定理 `Set.Ico_union_right`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α},
 b ≤ a → Set.Ico b a ∪ {a} = Set.Icc b a
-/
theorem Ico_insert_right (h : a ≤ b) : insert b (Ico a b) = Icc a b := by
  rw [insert_eq, union_comm, Ico_union_right h]

@[to_dual (attr := simp)]
/-
**Set.Ioo_insert_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioo_insert_left (h : a < b) : insert a (Ioo a b) = Ico a b
参数：h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.insert_eq`：insert_eq (x : α) (s : Set α) : insert x s = ({x} : Set α
) union s
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
· 使用定理 `Set.Ioo_union_left`：Ioo_union_left (hab : a < b) : Ioo a b union {a} = I
co a b
-/
theorem Ioo_insert_left (h : a < b) : insert a (Ioo a b) = Ico a b := by
  rw [insert_eq, union_comm, Ioo_union_left h]

@[to_dual (attr := simp)]
/-
**Set.Iio_insert** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iio_insert : insert a (Iio a) = Iic a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `le_iff_eq_or_lt`：le_iff_eq_or_lt : a <= b ↔ a = b ∨ a < b
-/
theorem Iio_insert : insert a (Iio a) = Iic a :=
  ext fun _ => le_iff_eq_or_lt.symm

@[to_dual]
/-
**Set.mem_Iic_Iio_of_subset_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_Iic_Iio_of_subset_of_subset {s : Set α} (ho : Iio a subseteq s) (hc : 
s subseteq Iic a) : s in ({Iic a, Iio a} : Set (Set α))
参数：ho : Iio a subseteq s；hc : s subseteq Iic a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `by_cases`：by_cases {p q : Prop} (hpq : p -> q) (hnpq : ¬p -> q) : q
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Iio_union_right`：Iio_union_right : Iio a union {a} = Iic a
· 使用定理 `Set.union_subset_iff`：union_subset_iff {s t u : Set α} : s union t subse
teq u ↔ s subseteq u ∧ t subseteq u
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
-/
theorem mem_Iic_Iio_of_subset_of_subset {s : Set α} (ho : Iio a ⊆ s) (hc : s ⊆ Iic a) :
    s ∈ ({Iic a, Iio a} : Set (Set α)) :=
  by_cases
    (fun h : a ∈ s =>
      Or.inl <| Subset.antisymm hc <| by rw [← Iio_union_right, union_subset_iff]; simp [*])
    fun h =>
    Or.inr <| Subset.antisymm (fun _ hx => lt_of_le_of_ne (hc hx) fun heq => h <| heq.symm ▸ hx) ho
/-
**Set.mem_Icc_Ico_Ioc_Ioo_of_subset_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_Icc_Ico_Ioc_Ioo_of_subset_of_subset {s : Set α} (ho : Ioo a b subseteq
 s) (hc : s subseteq Icc a b) : s in ({Icc a b, Ico a b, Ioc a b, Ioo a b} : Set
 (Set α))
参数：ho : Ioo a b subseteq s；hc : s subseteq Icc a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用引理 `Set.sdiff_singleton_subset_iff`：sdiff_singleton_subset_iff : s \ {a} sub
seteq t ↔ s subseteq insert a t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Icc_sdiff_right`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α},
 Set.Icc b a \ {a} = Set.Ico b a
· 使用定理 `Set.Ico_sdiff_left`：Ico_sdiff_left : Ico a b \ {a} = Ioo a b
· 使用引理 `Set.subset_sdiff_singleton`：subset_sdiff_singleton (h : s subseteq t) (h
a : a ∉ s) : s subseteq t \ {a}
· 使用定理 `Set.Icc_sdiff_left`：Icc_sdiff_left : Icc a b \ {a} = Ioc a b
· 使用定理 `Set.Ioc_sdiff_right`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α},
 Set.Ioc b a \ {a} = Set.Ioo b a
-/
theorem mem_Icc_Ico_Ioc_Ioo_of_subset_of_subset {s : Set α} (ho : Ioo a b ⊆ s) (hc : s ⊆ Icc a b) :
    s ∈ ({Icc a b, Ico a b, Ioc a b, Ioo a b} : Set (Set α)) := by
  by_cases ha : a ∈ s <;> by_cases hb : b ∈ s
  · refine Or.inl (Subset.antisymm hc ?_)
    rwa [← Ico_sdiff_left, sdiff_singleton_subset_iff, insert_eq_of_mem ha, ← Icc_sdiff_right,
      sdiff_singleton_subset_iff, insert_eq_of_mem hb] at ho
  · refine Or.inr <| Or.inl <| Subset.antisymm ?_ ?_
    · rw [← Icc_sdiff_right]
      exact subset_sdiff_singleton hc hb
    · rwa [← Ico_sdiff_left, sdiff_singleton_subset_iff, insert_eq_of_mem ha] at ho
  · refine Or.inr <| Or.inr <| Or.inl <| Subset.antisymm ?_ ?_
    · rw [← Icc_sdiff_left]
      exact subset_sdiff_singleton hc ha
    · rwa [← Ioc_sdiff_right, sdiff_singleton_subset_iff, insert_eq_of_mem hb] at ho
  · refine Or.inr <| Or.inr <| Or.inr <| Subset.antisymm ?_ ho
    rw [← Ico_sdiff_left, ← Icc_sdiff_right]
    apply_rules [subset_sdiff_singleton]

@[to_dual]
/-
**Set.eq_left_or_mem_Ioo_of_mem_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：eq_left_or_mem_Ioo_of_mem_Ico {x : α} (hmem : x in Ico a b) : x = a ∨ x in
 Ioo a b
参数：hmem : x in Ico a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp_right`：∀ {b c a : Prop}, (b → c) → a ∨ b → a ∨ c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LE.le.eq_or_lt'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, b ≤
 a → a = b ∨ b < a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem eq_left_or_mem_Ioo_of_mem_Ico {x : α} (hmem : x ∈ Ico a b) : x = a ∨ x ∈ Ioo a b :=
  hmem.1.eq_or_lt'.imp_right fun h => ⟨h, hmem.2⟩

@[to_dual none]
/-
**Set.eq_endpoints_or_mem_Ioo_of_mem_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：eq_endpoints_or_mem_Ioo_of_mem_Icc {x : α} (hmem : x in Icc a b) : x = a ∨
 x = b ∨ x in Ioo a b
参数：hmem : x in Icc a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp_right`：∀ {b c a : Prop}, (b → c) → a ∨ b → a ∨ c
· 使用定理 `Set.eq_right_or_mem_Ioo_of_mem_Ioc`：∀ {α : Type u_1} [inst : PartialOrde
r α] {a b x : α}, x ∈ Set.Ioc b a → x = a ∨ x ∈ Set.Ioo b a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LE.le.eq_or_lt'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, b ≤
 a → a = b ∨ b < a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem eq_endpoints_or_mem_Ioo_of_mem_Icc {x : α} (hmem : x ∈ Icc a b) :
    x = a ∨ x = b ∨ x ∈ Ioo a b :=
  hmem.1.eq_or_lt'.imp_right fun h => eq_right_or_mem_Ioo_of_mem_Ioc ⟨h, hmem.2⟩

@[to_dual]
/-
**Set._root_.IsMin.Iic_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsMin.Iic_eq (h : IsMin a) : Iic a = {a} :=
  eq_singleton_iff_unique_mem.2 ⟨self_mem_Ici, fun _ => h.eq_of_le⟩

@[to_dual]
/-
**Set.Iic_injective** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iic_injective : Injective (Iic : α -> Set α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `eq_of_forall_le_iff`：eq_of_forall_le_iff (H : forall c, c <= a ↔ c <= b)
 : a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.ext_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ ∀ (x : α), x ∈ a ↔ x 
∈ b
-/
theorem Iic_injective : Injective (Iic : α → Set α) := fun _ _ =>
  eq_of_forall_le_iff ∘ Set.ext_iff.1

@[to_dual]
/-
**Set.Iic_inj** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iic_inj : Iic a = Iic b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Set.Iic_injective`：Iic_injective : Injective (Iic : α -> Set α)
-/
theorem Iic_inj : Iic a = Iic b ↔ a = b :=
  Iic_injective.eq_iff

@[simp, to_dual none]
/-
**Set.Icc_inter_Icc_eq_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Icc_inter_Icc_eq_singleton (hab : a <= b) (hbc : b <= c) : Icc a b inter I
cc b c = {b}
参数：hab : a <= b；hbc : b <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Ici_inter_Iic`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.I
ci a ∩ Set.Iic b = Set.Icc a b
· 使用定理 `Set.Iic_inter_Ici`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.I
ic a ∩ Set.Ici b = Set.Icc b a
· 使用定理 `Set.inter_inter_inter_comm`：inter_inter_inter_comm (s t u v : Set α) : s
 inter t inter (u inter v) = s inter u inter (t inter v)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.Icc_self`：Icc_self (a : α) : Icc a a = {a}
· 使用定理 `Set.inter_singleton_of_mem`：∀ {α : Type u_1} {s : Set α} {a : α}, a ∈ s 
→ s ∩ {a} = {a}
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Icc_inter_Icc_eq_singleton (hab : a ≤ b) (hbc : b ≤ c) : Icc a b ∩ Icc b c = {b} := by
  rw [← Ici_inter_Iic, ← Iic_inter_Ici, inter_inter_inter_comm, Iic_inter_Ici]
  simp [hab, hbc]

@[to_dual none]
/-
**Set.Icc_eq_Icc_iff** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：Icc_eq_Icc_iff {d : α} (h : a <= b) : Icc a b = Icc c d ↔ a = c ∧ b = d
参数：h : a <= b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Icc_eq_empty_iff`：Icc_eq_empty_iff : Icc a b = ∅ ↔ ¬a <= b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
-/
lemma Icc_eq_Icc_iff {d : α} (h : a ≤ b) :
    Icc a b = Icc c d ↔ a = c ∧ b = d := by
  refine ⟨fun heq ↦ ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  have h' : c ≤ d := by
    by_contra contra; rw [Icc_eq_empty_iff.mpr contra, Icc_eq_empty_iff] at heq; contradiction
  simp only [Set.ext_iff, mem_Icc] at heq
  obtain ⟨-, h₁⟩ := (heq b).mp ⟨h, le_refl _⟩
  obtain ⟨h₂, -⟩ := (heq a).mp ⟨le_refl _, h⟩
  obtain ⟨h₃, -⟩ := (heq c).mpr ⟨le_refl _, h'⟩
  obtain ⟨-, h₄⟩ := (heq d).mpr ⟨h', le_refl _⟩
  exact ⟨le_antisymm h₃ h₂, le_antisymm h₁ h₄⟩

end PartialOrder

section OrderTop

@[to_dual (attr := simp)]
/-
**Set.Ici_top** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ici_top [PartialOrder α] [OrderTop α] : Ici (⊤ : α) = {⊤}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMax.Ici_eq`：∀ {α : Type u_1} [inst : PartialOrder α] {a : α}, IsMax a 
→ Set.Ici a = {a}
· 使用定理 `isMax_top`：isMax_top : IsMax (⊤ : α)
-/
theorem Ici_top [PartialOrder α] [OrderTop α] : Ici (⊤ : α) = {⊤} :=
  isMax_top.Ici_eq

@[to_dual]
/-
**Set.Iio_top** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iio_top [PartialOrder α] [OrderTop α] : Iio (⊤ : α) = {⊤}ᶜ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
-/
theorem Iio_top [PartialOrder α] [OrderTop α] : Iio (⊤ : α) = {⊤}ᶜ :=
  ext fun _ ↦ lt_top_iff_ne_top

variable [Preorder α] [OrderTop α] {a : α}

@[to_dual]
/-
**Set.Ioi_top** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioi_top : Ioi (⊤ : α) = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMax.Ioi_eq`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, IsMax a → Se
t.Ioi a = ∅
· 使用定理 `isMax_top`：isMax_top : IsMax (⊤ : α)
-/
theorem Ioi_top : Ioi (⊤ : α) = ∅ :=
  isMax_top.Ioi_eq

@[to_dual (attr := simp)]
/-
**Set.Iic_top** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iic_top : Iic (⊤ : α) = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTop.Iic_eq`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, IsTop a → Se
t.Iic a = Set.univ
· 使用定理 `isTop_top`：isTop_top : IsTop (⊤ : α)
-/
theorem Iic_top : Iic (⊤ : α) = univ :=
  isTop_top.Iic_eq

@[to_dual (attr := simp)]
/-
**Set.Icc_top** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Icc_top : Icc a ⊤ = Ici a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Iic_top`：Iic_top : Iic (⊤ : α) = univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Icc_top : Icc a ⊤ = Ici a := by simp [← Ici_inter_Iic]

@[to_dual (attr := simp)]
/-
**Set.Ioc_top** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioc_top : Ioc a ⊤ = Ioi a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Iic_top`：Iic_top : Iic (⊤ : α) = univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Ioc_top : Ioc a ⊤ = Ioi a := by simp [← Ioi_inter_Iic]

end OrderTop

/-
**Set.Icc_bot_top** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Icc_bot_top [Preorder α] [BoundedOrder α] : Icc (⊥ : α) ⊤ = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Icc_top`：Icc_top : Icc a ⊤ = Ici a
· 使用定理 `Set.Ici_bot`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : OrderBot α],
 Set.Ici ⊥ = Set.univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Icc_bot_top [Preorder α] [BoundedOrder α] : Icc (⊥ : α) ⊤ = univ := by simp

section Lattice

section Inf

variable [SemilatticeInf α]

@[to_dual (attr := simp)]
/-
**Set.Iic_inter_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iic_inter_Iic {a b : α} : Iic a inter Iic b = Iic (a ⊓ b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Iic_inter_Iic {a b : α} : Iic a ∩ Iic b = Iic (a ⊓ b) := by
  ext x
  simp [Iic]

@[to_dual (reorder := a b) (attr := simp)]
/-
**Set.Ioc_inter_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Ioc_inter_Iic (a b c : α) : Ioc a b inter Iic c = Ioc a (b ⊓ c)
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Ioi_inter_Iic`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.I
oi a ∩ Set.Iic b = Set.Ioc a b
· 使用定理 `Set.inter_assoc`：inter_assoc (a b c : Set α) : a inter b inter c = a int
er (b inter c)
· 使用定理 `Set.Iic_inter_Iic`：Iic_inter_Iic {a b : α} : Iic a inter Iic b = Iic (a 
⊓ b)
-/
theorem Ioc_inter_Iic (a b c : α) : Ioc a b ∩ Iic c = Ioc a (b ⊓ c) := by
  rw [← Ioi_inter_Iic, ← Ioi_inter_Iic, inter_assoc, Iic_inter_Iic]

end Inf

variable [Lattice α] {a b c a₁ a₂ b₁ b₂ : α}

@[to_dual self]
/-
**Set.Icc_inter_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Icc_inter_Icc : Icc a₁ b₁ inter Icc a₂ b₂ = Icc (a₁ ⊔ a₂) (b₁ ⊓ b₂)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Ici_inter_Iic`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, Set.I
ci a ∩ Set.Iic b = Set.Icc a b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.Ici_inter_Ici`：∀ {α : Type u_1} [inst : SemilatticeSup α] {a b : α},
 Set.Ici a ∩ Set.Ici b = Set.Ici (a ⊔ b)
· 使用定理 `Set.Iic_inter_Iic`：Iic_inter_Iic {a b : α} : Iic a inter Iic b = Iic (a 
⊓ b)
· 使用定理 `Lean.Data.AC.Context.eq_of_norm`：∀ {α : Sort u_1} (ctx : Data.AC.Context
 α) (a b : Data.AC.Expr),   (Data.AC.norm ctx a == Data.AC.norm ctx b) = true → 
Data.AC.eval α ctx a …
-/
theorem Icc_inter_Icc : Icc a₁ b₁ ∩ Icc a₂ b₂ = Icc (a₁ ⊔ a₂) (b₁ ⊓ b₂) := by
  simp only [Ici_inter_Iic.symm, Ici_inter_Ici.symm, Iic_inter_Iic.symm]; ac_rfl

end Lattice

/-! ### Closed intervals in `α × β` -/

section Prod

variable {β : Type*} [Preorder α] [Preorder β]

@[to_dual (attr := simp)]
/-
**Set.Iic_prod_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iic_prod_Iic (a : α) (b : β) : Iic a ×ˢ Iic b = Iic (a, b)
参数：a : α；b : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Iic_prod_Iic (a : α) (b : β) : Iic a ×ˢ Iic b = Iic (a, b) :=
  rfl

@[to_dual]
/-
**Set.Iic_prod_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Iic_prod_eq (a : α × β) : Iic a = Iic a.1 ×ˢ Iic a.2
参数：a : α × β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Iic_prod_eq (a : α × β) : Iic a = Iic a.1 ×ˢ Iic a.2 :=
  rfl

@[simp, to_dual self]
/-
**Set.Icc_prod_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Icc_prod_Icc (a₁ a₂ : α) (b₁ b₂ : β) : Icc a₁ a₂ ×ˢ Icc b₁ b₂ = Icc (a₁, b
₁) (a₂, b₂)
参数：a₁ a₂ : α；b₁ b₂ : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Icc_prod_Icc (a₁ a₂ : α) (b₁ b₂ : β) : Icc a₁ a₂ ×ˢ Icc b₁ b₂ = Icc (a₁, b₁) (a₂, b₂) := by
  ext ⟨x, y⟩
  simp [and_assoc, and_left_comm]

@[to_dual self]
/-
**Set.Icc_prod_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Icc_prod_eq (a b : α × β) : Icc a b = Icc a.1 b.1 ×ˢ Icc a.2 b.2
参数：a b : α × β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Icc_prod_Icc`：Icc_prod_Icc (a₁ a₂ : α) (b₁ b₂ : β) : Icc a₁ a₂ ×ˢ Ic
c b₁ b₂ = Icc (a₁, b₁) (a₂, b₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Prod.mk.eta`：∀ {α : Type u_1} {β : Type u_2} {p : α × β}, (p.1, p.2) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Icc_prod_eq (a b : α × β) : Icc a b = Icc a.1 b.1 ×ˢ Icc a.2 b.2 := by simp

end Prod

/-! ### Lemmas about intervals in dense orders -/

section Dense

variable (α) [Preorder α] [DenselyOrdered α] {x y : α}

@[to_dual] -- TODO: `to_dual` only works with the `mem_Ioo.mpr` in the proof.
/-
**Set.** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NoMinOrder (Ioo x y) :=
  ⟨fun ⟨a, ha⟩ => by
    rcases exists_between ha.1 with ⟨b, hb₁, hb₂⟩
    exact ⟨⟨b, mem_Ioo.mpr ⟨hb₁, hb₂.trans ha.2⟩⟩, hb₂⟩⟩

@[to_dual] -- TODO: `to_dual` only works with the `mem_Ioc.mpr` in the proof.
/-
**Set.** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NoMinOrder (Ioc x y) :=
  ⟨fun ⟨a, ha⟩ => by
    rcases exists_between ha.1 with ⟨b, hb₁, hb₂⟩
    exact ⟨⟨b, mem_Ioc.mpr ⟨hb₁, hb₂.le.trans ha.2⟩⟩, hb₂⟩⟩

@[to_dual]
/-
**Set.** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NoMinOrder (Ioi x) :=
  ⟨fun ⟨a, ha⟩ => by
    rcases exists_between ha with ⟨b, hb₁, hb₂⟩
    exact ⟨⟨b, hb₁⟩, hb₂⟩⟩

end Dense

/-! ### Intervals in `Prop` -/

/-
**Set.Iic_False** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Set.Iic False = {False}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
### Intervals in `Prop`
-/
@[simp] lemma Iic_False : Iic False = {False} := by aesop
/-
**Set.Iic_True** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Set.Iic True = Set.univ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
### Intervals in `Prop`
-/
@[simp] lemma Iic_True : Iic True = univ := by aesop
/-
**Set.Ici_False** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Set.Ici False = Set.univ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
### Intervals in `Prop`
-/
@[simp] lemma Ici_False : Ici False = univ := by aesop
/-
**Set.Ici_True** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Set.Ici True = {True}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
### Intervals in `Prop`
-/
@[simp] lemma Ici_True : Ici True = {True} := by aesop
/-
**Set.Iio_False** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：Iio_False : Iio False = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsMin.Iio_eq`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, IsMin a → Se
t.Iio a = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
### Intervals in `Prop`
-/
lemma Iio_False : Iio False = ∅ := by aesop
/-
**Set.Iio_True** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Set.Iio True = {False}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma Iio_True : Iio True = {False} := by aesop (add simp [Ioi, lt_iff_le_not_ge])
/-
**Set.Ioi_False** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：Set.Ioi False = {True}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma Ioi_False : Ioi False = {True} := by aesop (add simp [Ioi, lt_iff_le_not_ge])
/-
**Set.Ioi_True** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：Ioi_True : Ioi True = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsMax.Ioi_eq`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, IsMax a → Se
t.Ioi a = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Ioi_True : Ioi True = ∅ := by aesop

end Set

