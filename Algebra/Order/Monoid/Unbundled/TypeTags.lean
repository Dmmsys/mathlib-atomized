/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Order.BoundedOrder.Basic

/-! # Ordered monoid structures on `Multiplicative α` and `Additive α`. -/

public section

variable {α : Type*}

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LE α] : LE (Multiplicative α) :=
  inferInstanceAs <| LE α
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LE α] : LE (Additive α) :=
  inferInstanceAs <| LE α
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LT α] : LT (Multiplicative α) :=
  inferInstanceAs <| LT α
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LT α] : LT (Additive α) :=
  inferInstanceAs <| LT α
/-
**Multiplicative.preorder** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Multiplicative.preorder [Preorder α] : Preorder (Multiplicative α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Multiplicative.preorder [Preorder α] : Preorder (Multiplicative α) :=
  inferInstanceAs <| Preorder α
/-
**Additive.preorder** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Additive.preorder [Preorder α] : Preorder (Additive α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Additive.preorder [Preorder α] : Preorder (Additive α) :=
  inferInstanceAs <| Preorder α
/-
**Multiplicative.partialOrder** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Multiplicative.partialOrder [PartialOrder α] : PartialOrder (Multiplicativ
e α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Multiplicative.partialOrder [PartialOrder α] : PartialOrder (Multiplicative α) :=
  inferInstanceAs <| PartialOrder α
/-
**Additive.partialOrder** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Additive.partialOrder [PartialOrder α] : PartialOrder (Additive α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Additive.partialOrder [PartialOrder α] : PartialOrder (Additive α) :=
  inferInstanceAs <| PartialOrder α
/-
**Multiplicative.linearOrder** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Multiplicative.linearOrder [LinearOrder α] : LinearOrder (Multiplicative α
)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Multiplicative.linearOrder [LinearOrder α] : LinearOrder (Multiplicative α) :=
  inferInstanceAs <| LinearOrder α
/-
**Additive.linearOrder** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Additive.linearOrder [LinearOrder α] : LinearOrder (Additive α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Additive.linearOrder [LinearOrder α] : LinearOrder (Additive α) :=
  inferInstanceAs <| LinearOrder α
/-
**Multiplicative.orderBot** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Multiplicative.orderBot [LE α] [OrderBot α] : OrderBot (Multiplicative α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Multiplicative.orderBot [LE α] [OrderBot α] : OrderBot (Multiplicative α) :=
  inferInstanceAs <| OrderBot α
/-
**Additive.orderBot** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Additive.orderBot [LE α] [OrderBot α] : OrderBot (Additive α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Additive.orderBot [LE α] [OrderBot α] : OrderBot (Additive α) :=
  inferInstanceAs <| OrderBot α
/-
**Multiplicative.orderTop** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Multiplicative.orderTop [LE α] [OrderTop α] : OrderTop (Multiplicative α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Multiplicative.orderTop [LE α] [OrderTop α] : OrderTop (Multiplicative α) :=
  inferInstanceAs <| OrderTop α
/-
**Additive.orderTop** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Additive.orderTop [LE α] [OrderTop α] : OrderTop (Additive α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Additive.orderTop [LE α] [OrderTop α] : OrderTop (Additive α) :=
  inferInstanceAs <| OrderTop α
/-
**Multiplicative.boundedOrder** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Multiplicative.boundedOrder [LE α] [BoundedOrder α] : BoundedOrder (Multip
licative α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Multiplicative.boundedOrder [LE α] [BoundedOrder α] : BoundedOrder (Multiplicative α) :=
  inferInstanceAs <| BoundedOrder α
/-
**Additive.boundedOrder** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Additive.boundedOrder [LE α] [BoundedOrder α] : BoundedOrder (Additive α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Additive.boundedOrder [LE α] [BoundedOrder α] : BoundedOrder (Additive α) :=
  inferInstanceAs <| BoundedOrder α
/-
**Multiplicative.existsMulOfLe** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Multiplicative.existsMulOfLe [Add α] [LE α] [ExistsAddOfLE α] : ExistsMulO
fLE (Multiplicative α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ExistsAddOfLE.exists_add_of_le`：∀ {α : Type u} {inst : Add α} {inst_1 : 
LE α} [self : ExistsAddOfLE α] {a b : α}, a ≤ b → ∃ c, b = a + c
-/
instance Multiplicative.existsMulOfLe [Add α] [LE α] [ExistsAddOfLE α] :
    ExistsMulOfLE (Multiplicative α) :=
  ⟨@exists_add_of_le α _ _ _⟩
/-
**Additive.existsAddOfLe** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Additive.existsAddOfLe [Mul α] [LE α] [ExistsMulOfLE α] : ExistsAddOfLE (A
dditive α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ExistsMulOfLE.exists_mul_of_le`：∀ {α : Type u} {inst : Mul α} {inst_1 : 
LE α} [self : ExistsMulOfLE α] {a b : α}, a ≤ b → ∃ c, b = a * c
-/
instance Additive.existsAddOfLe [Mul α] [LE α] [ExistsMulOfLE α] : ExistsAddOfLE (Additive α) :=
  ⟨@exists_mul_of_le α _ _ _⟩

namespace Additive
section Preorder
variable [Preorder α]

@[simp]
/-
**Additive.ofMul_le** 是 Mathlib 中的一个定理，位于命名空间 `Additive`。
形式化陈述：ofMul_le {a b : α} : ofMul a <= ofMul b ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ofMul_le {a b : α} : ofMul a ≤ ofMul b ↔ a ≤ b :=
  Iff.rfl

@[simp]
/-
**Additive.ofMul_lt** 是 Mathlib 中的一个定理，位于命名空间 `Additive`。
形式化陈述：ofMul_lt {a b : α} : ofMul a < ofMul b ↔ a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ofMul_lt {a b : α} : ofMul a < ofMul b ↔ a < b :=
  Iff.rfl

@[simp]
/-
**Additive.toMul_le** 是 Mathlib 中的一个定理，位于命名空间 `Additive`。
形式化陈述：toMul_le {a b : Additive α} : a.toMul <= b.toMul ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toMul_le {a b : Additive α} : a.toMul ≤ b.toMul ↔ a ≤ b :=
  Iff.rfl

@[simp]
/-
**Additive.toMul_lt** 是 Mathlib 中的一个定理，位于命名空间 `Additive`。
形式化陈述：toMul_lt {a b : Additive α} : a.toMul < b.toMul ↔ a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toMul_lt {a b : Additive α} : a.toMul < b.toMul ↔ a < b :=
  Iff.rfl

@[gcongr] alias ⟨_, toMul_mono⟩ := toMul_le
@[gcongr] alias ⟨_, ofMul_mono⟩ := ofMul_le
@[gcongr] alias ⟨_, toMul_strictMono⟩ := toMul_lt
@[gcongr] alias ⟨_, ofMul_strictMono⟩ := ofMul_lt

end Preorder

section OrderTop
variable [LE α] [OrderTop α]

/-
**Additive.ofMul_top** 是 Mathlib 中的一个定理，位于命名空间 `Additive`。
形式化陈述：∀ {α : Type u_1} [inst : LE α] [inst_1 : OrderTop α], Additive.ofMul ⊤ = ⊤
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofMul_top : ofMul (⊤ : α) = ⊤ := rfl
/-
**Additive.toMul_top** 是 Mathlib 中的一个定理，位于命名空间 `Additive`。
形式化陈述：∀ {α : Type u_1} [inst : LE α] [inst_1 : OrderTop α], Additive.toMul ⊤ = ⊤
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toMul_top : toMul ⊤ = (⊤ : α) := rfl
/-
**Additive.ofMul_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Additive`。
形式化陈述：∀ {α : Type u_1} [inst : LE α] [inst_1 : OrderTop α] {a : α}, Additive.ofM
ul a = ⊤ ↔ a = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma ofMul_eq_top {a : α} : ofMul a = ⊤ ↔ a = ⊤ := .rfl
/-
**Additive.toMul_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Additive`。
形式化陈述：∀ {α : Type u_1} [inst : LE α] [inst_1 : OrderTop α] {a : Additive α}, Add
itive.toMul a = ⊤ ↔ a = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma toMul_eq_top {a : Additive α} : toMul a = ⊤ ↔ a = ⊤ := .rfl

end OrderTop

section OrderBot
variable [LE α] [OrderBot α]

/-
**Additive.ofMul_bot** 是 Mathlib 中的一个定理，位于命名空间 `Additive`。
形式化陈述：∀ {α : Type u_1} [inst : LE α] [inst_1 : OrderBot α], Additive.ofMul ⊥ = ⊥
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofMul_bot : ofMul (⊥ : α) = ⊥ := rfl
/-
**Additive.toMul_bot** 是 Mathlib 中的一个定理，位于命名空间 `Additive`。
形式化陈述：∀ {α : Type u_1} [inst : LE α] [inst_1 : OrderBot α], Additive.toMul ⊥ = ⊥
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toMul_bot : toMul ⊥ = (⊥ : α) := rfl
/-
**Additive.ofMul_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Additive`。
形式化陈述：∀ {α : Type u_1} [inst : LE α] [inst_1 : OrderBot α] {a : α}, Additive.ofM
ul a = ⊥ ↔ a = ⊥
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma ofMul_eq_bot {a : α} : ofMul a = ⊥ ↔ a = ⊥ := .rfl
/-
**Additive.toMul_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Additive`。
形式化陈述：∀ {α : Type u_1} [inst : LE α] [inst_1 : OrderBot α] {a : Additive α}, Add
itive.toMul a = ⊥ ↔ a = ⊥
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma toMul_eq_bot {a : Additive α} : toMul a = ⊥ ↔ a = ⊥ := .rfl

end OrderBot
end Additive

namespace Multiplicative
section Preorder
variable [Preorder α]

@[simp]
/-
**Multiplicative.ofAdd_le** 是 Mathlib 中的一个定理，位于命名空间 `Multiplicative`。
形式化陈述：ofAdd_le {a b : α} : ofAdd a <= ofAdd b ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ofAdd_le {a b : α} : ofAdd a ≤ ofAdd b ↔ a ≤ b :=
  Iff.rfl

@[simp]
/-
**Multiplicative.ofAdd_lt** 是 Mathlib 中的一个定理，位于命名空间 `Multiplicative`。
形式化陈述：ofAdd_lt {a b : α} : ofAdd a < ofAdd b ↔ a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ofAdd_lt {a b : α} : ofAdd a < ofAdd b ↔ a < b :=
  Iff.rfl

@[simp]
/-
**Multiplicative.toAdd_le** 是 Mathlib 中的一个定理，位于命名空间 `Multiplicative`。
形式化陈述：toAdd_le {a b : Multiplicative α} : a.toAdd <= b.toAdd ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toAdd_le {a b : Multiplicative α} : a.toAdd ≤ b.toAdd ↔ a ≤ b :=
  Iff.rfl

@[simp]
/-
**Multiplicative.toAdd_lt** 是 Mathlib 中的一个定理，位于命名空间 `Multiplicative`。
形式化陈述：toAdd_lt {a b : Multiplicative α} : a.toAdd < b.toAdd ↔ a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toAdd_lt {a b : Multiplicative α} : a.toAdd < b.toAdd ↔ a < b :=
  Iff.rfl

@[gcongr] alias ⟨_, toAdd_mono⟩ := toAdd_le
@[gcongr] alias ⟨_, ofAdd_mono⟩ := ofAdd_le
@[gcongr] alias ⟨_, toAdd_strictMono⟩ := toAdd_lt
@[gcongr] alias ⟨_, ofAdd_strictMono⟩ := ofAdd_lt

end Preorder

section OrderTop
variable [LE α] [OrderTop α]

/-
**Multiplicative.ofAdd_top** 是 Mathlib 中的一个定理，位于命名空间 `Multiplicative`。
形式化陈述：∀ {α : Type u_1} [inst : LE α] [inst_1 : OrderTop α], Multiplicative.ofAdd
 ⊤ = ⊤
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofAdd_top : ofAdd (⊤ : α) = ⊤ := rfl
/-
**Multiplicative.toAdd_top** 是 Mathlib 中的一个定理，位于命名空间 `Multiplicative`。
形式化陈述：∀ {α : Type u_1} [inst : LE α] [inst_1 : OrderTop α], Multiplicative.toAdd
 ⊤ = ⊤
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toAdd_top : toAdd ⊤ = (⊤ : α) := rfl
/-
**Multiplicative.ofAdd_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Multiplicative`。
形式化陈述：∀ {α : Type u_1} [inst : LE α] [inst_1 : OrderTop α] {a : α}, Multiplicati
ve.ofAdd a = ⊤ ↔ a = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma ofAdd_eq_top {a : α} : ofAdd a = ⊤ ↔ a = ⊤ := .rfl
/-
**Multiplicative.toAdd_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Multiplicative`。
形式化陈述：∀ {α : Type u_1} [inst : LE α] [inst_1 : OrderTop α] {a : Multiplicative α
}, Multiplicative.toAdd a = ⊤ ↔ a = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma toAdd_eq_top {a : Multiplicative α} : toAdd a = ⊤ ↔ a = ⊤ := .rfl

end OrderTop

section OrderBot
variable [LE α] [OrderBot α]

/-
**Multiplicative.ofAdd_bot** 是 Mathlib 中的一个定理，位于命名空间 `Multiplicative`。
形式化陈述：∀ {α : Type u_1} [inst : LE α] [inst_1 : OrderBot α], Multiplicative.ofAdd
 ⊥ = ⊥
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofAdd_bot : ofAdd (⊥ : α) = ⊥ := rfl
/-
**Multiplicative.toAdd_bot** 是 Mathlib 中的一个定理，位于命名空间 `Multiplicative`。
形式化陈述：∀ {α : Type u_1} [inst : LE α] [inst_1 : OrderBot α], Multiplicative.toAdd
 ⊥ = ⊥
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toAdd_bot : toAdd ⊥ = (⊥ : α) := rfl
/-
**Multiplicative.ofAdd_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Multiplicative`。
形式化陈述：∀ {α : Type u_1} [inst : LE α] [inst_1 : OrderBot α] {a : α}, Multiplicati
ve.ofAdd a = ⊥ ↔ a = ⊥
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma ofAdd_eq_bot {a : α} : ofAdd a = ⊥ ↔ a = ⊥ := .rfl
/-
**Multiplicative.toAdd_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Multiplicative`。
形式化陈述：∀ {α : Type u_1} [inst : LE α] [inst_1 : OrderBot α] {a : Multiplicative α
}, Multiplicative.toAdd a = ⊥ ↔ a = ⊥
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma toAdd_eq_bot {a : Multiplicative α} : toAdd a = ⊥ ↔ a = ⊥ := .rfl

end OrderBot

end Multiplicative

