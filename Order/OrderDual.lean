/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro
-/
module

public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Basic

/-!
# Order dual

This file defines `OrderDual α`, a type synonym reversing the meaning of all inequalities,
with notation `αᵒᵈ`.

## Notation

`αᵒᵈ` is notation for `OrderDual α`.

## Implementation notes

One should not abuse definitional equality between `α` and `αᵒᵈ`. Instead, explicit
coercions should be inserted:
* `OrderDual.toDual : α → αᵒᵈ` and `OrderDual.ofDual : αᵒᵈ → α`
-/

@[expose] public section

assert_not_exists Lex

variable {α : Type*}

/-- Type synonym to equip a type with the dual order: `≤` means `≥` and `<` means `>`. `αᵒᵈ` is
notation for `OrderDual α`. -/
/-
**OrderDual** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：OrderDual (α : Type*) : Type _
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Type synonym to equip a type with the dual order: `≤` means `≥` and `<` means `>
`. `αᵒᵈ` is
notation for `OrderDual α`.
-/
def OrderDual (α : Type*) : Type _ :=
  α

@[inherit_doc]
notation:max α "ᵒᵈ" => OrderDual α

namespace OrderDual

/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (α : Type*) [h : Nonempty α] : Nonempty αᵒᵈ :=
  h
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (α : Type*) [h : Subsingleton α] : Subsingleton αᵒᵈ :=
  h
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (α : Type*) [h : LE α] : LE αᵒᵈ :=
  ⟨fun a b ↦ h.le b a⟩
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (α : Type*) [h : LT α] : LT αᵒᵈ :=
  ⟨fun a b ↦ h.lt b a⟩
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (α : Type*) [h : Ord α] : Ord αᵒᵈ :=
  ⟨fun a b ↦ h.compare b a⟩

@[to_dual]
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (α : Type*) [h : Min α] : Max αᵒᵈ :=
  ⟨fun a b ↦ h.min a b⟩
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LE α] [T : IsTrans α LE.le] : IsTrans αᵒᵈ LE.le where
  trans _ _ _ hab hbc := T.trans _ _ _ hbc hab
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LT α] [T : IsTrans α LT.lt] : IsTrans αᵒᵈ LT.lt where
  trans _ _ _ hab hbc := T.trans _ _ _ hbc hab
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LT α] [T : @Std.Trichotomous α LT.lt] : @Std.Trichotomous αᵒᵈ LT.lt where
  trichotomous a b := by rw [eq_comm]; exact T.trichotomous b a
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (α : Type*) [Preorder α] : Preorder αᵒᵈ where
  le_refl _ := le_refl _
  le_trans _ _ _ hab hbc := hbc.trans hab
  lt_iff_le_not_ge _ _ := lt_iff_le_not_ge
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (α : Type*) [PartialOrder α] : PartialOrder αᵒᵈ where
  le_antisymm a b hab hba := @le_antisymm α _ a b hba hab
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (α : Type*) [DecidableEq α] : DecidableEq αᵒᵈ := ‹DecidableEq α›
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (α : Type*) [LT α] [h : DecidableLT α] : DecidableLT (αᵒᵈ) :=
  fun a b ↦ h b a
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (α : Type*) [LE α] [h : DecidableLE α] : DecidableLE (αᵒᵈ) :=
  fun a b ↦ h b a

set_option backward.isDefEq.respectTransparency false in
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (α : Type*) [LinearOrder α] : LinearOrder αᵒᵈ where
  le_total a b := le_total (α := α) b a
  min_def := max_def' (α := α)
  max_def := min_def' (α := α)
  toDecidableLE := inferInstance
  toDecidableLT := inferInstance
  toDecidableEq := inferInstance
  compare_eq_compareOfLessAndEq a b := by
    simp only [compare, LinearOrder.compare_eq_compareOfLessAndEq, compareOfLessAndEq, eq_comm]
    rfl

set_option linter.style.setOption false in
set_option backward.inferInstanceAs.wrap.reuseSubInstances false in  -- otherwise we get an identity!
/-- The opposite linear order to a given linear order -/
@[instance_reducible, deprecated "This declaration shouldn't have existed" (since := "2026-04-08")]
/-
**OrderDual._root_.LinearOrder.swap** 是 Mathlib 中的一个定义，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The opposite linear order to a given linear order
-/
def _root_.LinearOrder.swap (α : Type*) (_ : LinearOrder α) : LinearOrder α :=
  inferInstanceAs <| LinearOrder (OrderDual α)
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [h : Inhabited α] : Inhabited αᵒᵈ := ⟨h.default⟩
/-
**OrderDual.Ord.dual_dual** 是 Mathlib 中的一个定理，位于命名空间 `OrderDual.Ord`。
形式化陈述：∀ (α : Type u_2) [H : Ord α], OrderDual.instOrd αᵒᵈ = H
参数：α : Type u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ord.dual_dual (α : Type*) [H : Ord α] : OrderDual.instOrd αᵒᵈ = H :=
  rfl
/-
**OrderDual.Preorder.dual_dual** 是 Mathlib 中的一个定理，位于命名空间 `OrderDual.Preorder`。
形式化陈述：∀ (α : Type u_2) [H : Preorder α], OrderDual.instPreorder αᵒᵈ = H
参数：α : Type u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Preorder.dual_dual (α : Type*) [H : Preorder α] : OrderDual.instPreorder αᵒᵈ = H :=
  rfl
/-
**OrderDual.instPartialOrder.dual_dual** 是 Mathlib 中的一个定理，位于命名空间 `OrderDual.inst
PartialOrder`。
形式化陈述：∀ (α : Type u_2) [H : PartialOrder α], OrderDual.instPartialOrder αᵒᵈ = H
参数：α : Type u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem instPartialOrder.dual_dual (α : Type*) [H : PartialOrder α] :
    OrderDual.instPartialOrder αᵒᵈ = H :=
  rfl
/-
**OrderDual.instLinearOrder.dual_dual** 是 Mathlib 中的一个定理，位于命名空间 `OrderDual.instL
inearOrder`。
形式化陈述：∀ (α : Type u_2) [H : LinearOrder α], OrderDual.instLinearOrder αᵒᵈ = H
参数：α : Type u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem instLinearOrder.dual_dual (α : Type*) [H : LinearOrder α] :
    OrderDual.instLinearOrder αᵒᵈ = H :=
  rfl
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [h : Nontrivial α] : Nontrivial αᵒᵈ := h
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [h : Unique α] : Unique αᵒᵈ where
  uniq := h.uniq

/-- `toDual` is the identity function to the `OrderDual` of a linear order. -/
/-
**OrderDual.toDual** 是 Mathlib 中的一个定义，位于命名空间 `OrderDual`。
形式化陈述：toDual : α ≃ αᵒᵈ
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
`toDual` is the identity function to the `OrderDual` of a linear order.
-/
def toDual : α ≃ αᵒᵈ :=
  Equiv.refl _

/-- `ofDual` is the identity function from the `OrderDual` of a linear order. -/
/-
**OrderDual.ofDual** 是 Mathlib 中的一个定义，位于命名空间 `OrderDual`。
形式化陈述：ofDual : αᵒᵈ ≃ α
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
`ofDual` is the identity function from the `OrderDual` of a linear order.
-/
def ofDual : αᵒᵈ ≃ α :=
  Equiv.refl _
/-
**OrderDual.toDual_symm_eq** 是 Mathlib 中的一个定理，位于命名空间 `OrderDual`。
形式化陈述：∀ {α : Type u_1}, OrderDual.toDual.symm = OrderDual.ofDual
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
@[simp] theorem toDual_symm_eq : (@toDual α).symm = ofDual := rfl
/-
**OrderDual.ofDual_symm_eq** 是 Mathlib 中的一个定理，位于命名空间 `OrderDual`。
形式化陈述：∀ {α : Type u_1}, OrderDual.ofDual.symm = OrderDual.toDual
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
@[simp] theorem ofDual_symm_eq : (@ofDual α).symm = toDual := rfl
/-
**OrderDual.toDual_ofDual** 是 Mathlib 中的一个定理，位于命名空间 `OrderDual`。
形式化陈述：∀ {α : Type u_1} (a : αᵒᵈ), OrderDual.toDual (OrderDual.ofDual a) = a
参数：a : αᵒᵈ；OrderDual.ofDual a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toDual_ofDual (a : αᵒᵈ) : toDual (ofDual a) = a := rfl
/-
**OrderDual.ofDual_toDual** 是 Mathlib 中的一个定理，位于命名空间 `OrderDual`。
形式化陈述：∀ {α : Type u_1} (a : α), OrderDual.ofDual (OrderDual.toDual a) = a
参数：a : α；OrderDual.toDual a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem ofDual_toDual (a : α) : ofDual (toDual a) = a := rfl
/-
**OrderDual.toDual_trans_ofDual** 是 Mathlib 中的一个定理，位于命名空间 `OrderDual`。
形式化陈述：∀ {α : Type u_1}, OrderDual.toDual.trans OrderDual.ofDual = Equiv.refl α
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
-/
@[simp] theorem toDual_trans_ofDual : (toDual (α := α)).trans ofDual = Equiv.refl _ := rfl
/-
**OrderDual.ofDual_trans_toDual** 是 Mathlib 中的一个定理，位于命名空间 `OrderDual`。
形式化陈述：∀ {α : Type u_1}, OrderDual.ofDual.trans OrderDual.toDual = Equiv.refl αᵒᵈ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
-/
@[simp] theorem ofDual_trans_toDual : (ofDual (α := α)).trans toDual = Equiv.refl _ := rfl
/-
**OrderDual.toDual_comp_ofDual** 是 Mathlib 中的一个定理，位于命名空间 `OrderDual`。
形式化陈述：∀ {α : Type u_1}, ⇑OrderDual.toDual ∘ ⇑OrderDual.ofDual = id
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toDual_comp_ofDual : (toDual (α := α)) ∘ ofDual = id := rfl
/-
**OrderDual.ofDual_comp_toDual** 是 Mathlib 中的一个定理，位于命名空间 `OrderDual`。
形式化陈述：∀ {α : Type u_1}, ⇑OrderDual.ofDual ∘ ⇑OrderDual.toDual = id
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem ofDual_comp_toDual : (ofDual (α := α)) ∘ toDual = id := rfl
/-
**OrderDual.toDual_inj** 是 Mathlib 中的一个定理，位于命名空间 `OrderDual`。
形式化陈述：toDual_inj {a b : α} : toDual a = toDual b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem toDual_inj {a b : α} : toDual a = toDual b ↔ a = b := by simp
/-
**OrderDual.ofDual_inj** 是 Mathlib 中的一个定理，位于命名空间 `OrderDual`。
形式化陈述：ofDual_inj {a b : αᵒᵈ} : ofDual a = ofDual b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ofDual_inj {a b : αᵒᵈ} : ofDual a = ofDual b ↔ a = b := by simp
/-
**OrderDual.ext** 是 Mathlib 中的一个定理，位于命名空间 `OrderDual`。
形式化陈述：∀ {α : Type u_1} {a b : αᵒᵈ}, OrderDual.ofDual a = OrderDual.ofDual b → a 
= b
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[ext] lemma ext {a b : αᵒᵈ} (h : ofDual a = ofDual b) : a = b := h

@[to_dual self, simp]
/-
**OrderDual.toDual_le_toDual** 是 Mathlib 中的一个定理，位于命名空间 `OrderDual`。
形式化陈述：toDual_le_toDual [LE α] {a b : α} : toDual a <= toDual b ↔ b <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toDual_le_toDual [LE α] {a b : α} : toDual a ≤ toDual b ↔ b ≤ a := .rfl

@[to_dual self, simp]
/-
**OrderDual.toDual_lt_toDual** 是 Mathlib 中的一个定理，位于命名空间 `OrderDual`。
形式化陈述：toDual_lt_toDual [LT α] {a b : α} : toDual a < toDual b ↔ b < a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toDual_lt_toDual [LT α] {a b : α} : toDual a < toDual b ↔ b < a := .rfl

@[to_dual self, simp]
/-
**OrderDual.ofDual_le_ofDual** 是 Mathlib 中的一个定理，位于命名空间 `OrderDual`。
形式化陈述：ofDual_le_ofDual [LE α] {a b : αᵒᵈ} : ofDual a <= ofDual b ↔ b <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ofDual_le_ofDual [LE α] {a b : αᵒᵈ} : ofDual a ≤ ofDual b ↔ b ≤ a := .rfl

@[to_dual self, simp]
/-
**OrderDual.ofDual_lt_ofDual** 是 Mathlib 中的一个定理，位于命名空间 `OrderDual`。
形式化陈述：ofDual_lt_ofDual [LT α] {a b : αᵒᵈ} : ofDual a < ofDual b ↔ b < a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ofDual_lt_ofDual [LT α] {a b : αᵒᵈ} : ofDual a < ofDual b ↔ b < a := .rfl

@[to_dual toDual_le]
/-
**OrderDual.le_toDual** 是 Mathlib 中的一个定理，位于命名空间 `OrderDual`。
形式化陈述：le_toDual [LE α] {a : αᵒᵈ} {b : α} : a <= toDual b ↔ b <= ofDual a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_toDual [LE α] {a : αᵒᵈ} {b : α} : a ≤ toDual b ↔ b ≤ ofDual a := .rfl

@[to_dual toDual_lt]
/-
**OrderDual.lt_toDual** 是 Mathlib 中的一个定理，位于命名空间 `OrderDual`。
形式化陈述：lt_toDual [LT α] {a : αᵒᵈ} {b : α} : a < toDual b ↔ b < ofDual a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lt_toDual [LT α] {a : αᵒᵈ} {b : α} : a < toDual b ↔ b < ofDual a := .rfl

/-- Recursor for `αᵒᵈ`. -/
@[elab_as_elim]
/-
**OrderDual.rec** 是 Mathlib 中的一个定义，位于命名空间 `OrderDual`。
形式化陈述：{α : Type u_1} → {motive : αᵒᵈ → Sort u_2} → ((a : α) → motive (OrderDual.
toDual a)) → (a : αᵒᵈ) → motive a
参数：(a : α) → motive (OrderDual.toDual a)；a : αᵒᵈ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Recursor for `αᵒᵈ`.
-/
protected def rec {motive : αᵒᵈ → Sort*} (toDual : ∀ a : α, motive (toDual a)) :
    ∀ a : αᵒᵈ, motive a := toDual
/-
**OrderDual.** 是 Mathlib 中的一个定理，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] protected theorem «forall» {p : αᵒᵈ → Prop} : (∀ a, p a) ↔ ∀ a, p (toDual a) := .rfl
/-
**OrderDual.** 是 Mathlib 中的一个定理，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] protected theorem «exists» {p : αᵒᵈ → Prop} : (∃ a, p a) ↔ ∃ a, p (toDual a) := .rfl

@[to_dual self] alias ⟨_, _root_.LE.le.dual⟩ := toDual_le_toDual
@[to_dual self] alias ⟨_, _root_.LT.lt.dual⟩ := toDual_lt_toDual
@[to_dual self] alias ⟨_, _root_.LE.le.ofDual⟩ := ofDual_le_ofDual
@[to_dual self] alias ⟨_, _root_.LT.lt.ofDual⟩ := ofDual_lt_ofDual

end OrderDual

/-! ### `DenselyOrdered` for `OrderDual` -/

/-
**OrderDual.denselyOrdered** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：OrderDual.denselyOrdered (α : Type*) [LT α] [h : DenselyOrdered α] : Dense
lyOrdered αᵒᵈ
参数：α : Type*。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `And.symm`：∀ {a b : Prop}, a ∧ b → b ∧ a
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂

--- 原说明 ---
### `DenselyOrdered` for `OrderDual`
-/
instance OrderDual.denselyOrdered (α : Type*) [LT α] [h : DenselyOrdered α] :
    DenselyOrdered αᵒᵈ :=
  ⟨fun _ _ ha ↦ (@exists_between α _ h _ _ ha).imp fun _ ↦ And.symm⟩

@[simp]
/-
**denselyOrdered_orderDual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：denselyOrdered_orderDual [LT α] : DenselyOrdered αᵒᵈ ↔ DenselyOrdered α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
-/
theorem denselyOrdered_orderDual [LT α] : DenselyOrdered αᵒᵈ ↔ DenselyOrdered α :=
  ⟨by convert! @OrderDual.denselyOrdered αᵒᵈ _, @OrderDual.denselyOrdered α _⟩

/-! ### Pushing order definitions through `Equiv` -/

namespace Equiv

variable {β : Type*} (e : α ≃ β)

/-- Transfer `Top` across an `Equiv`. -/
/-
**Equiv.top** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → α ≃ β → [Top β] → Top α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Transfer `Top` across an `Equiv`.
-/
protected abbrev top [Top β] : Top α where
  top := e.symm ⊤
/-
**Equiv.top_def** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：top_def [Top β] : letI
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma top_def [Top β] :
    letI := e.top
    ⊤ = e.symm ⊤ := rfl

/-- Transfer `Bot` across an `Equiv`. -/
/-
**Equiv.bot** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → α ≃ β → [Bot β] → Bot α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Transfer `Bot` across an `Equiv`.
-/
protected abbrev bot [Bot β] : Bot α where
  bot := e.symm ⊥
/-
**Equiv.bot_def** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：bot_def [Bot β] : letI
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma bot_def [Bot β] :
    letI := e.bot
    ⊥ = e.symm ⊥ := rfl

/-- Transfer `Compl` across an `Equiv`. -/
/-
**Equiv.compl** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → α ≃ β → [Compl β] → Compl α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Transfer `Compl` across an `Equiv`.
-/
protected abbrev compl [Compl β] : Compl α where
  compl a := e.symm (e a)ᶜ
/-
**Equiv.compl_def** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：compl_def [Compl β] (a : α) : letI
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma compl_def [Compl β] (a : α) :
    letI := e.compl
    aᶜ = e.symm (e a)ᶜ := rfl

/-- Transfer `SDiff` across an `Equiv`. -/
/-
**Equiv.sdiff** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → α ≃ β → [SDiff β] → SDiff α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Transfer `SDiff` across an `Equiv`.
-/
protected abbrev sdiff [SDiff β] : SDiff α where
  sdiff a b := e.symm (e a \ e b)
/-
**Equiv.sdiff_def** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：sdiff_def [SDiff β] (a b : α) : letI
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sdiff_def [SDiff β] (a b : α) :
    letI := e.sdiff
    a \ b = e.symm (e a \ e b) := rfl

/-- Transfer `HImp` across an `Equiv`. -/
/-
**Equiv.himp** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → α ≃ β → [HImp β] → HImp α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Transfer `HImp` across an `Equiv`.
-/
protected abbrev himp [HImp β] : HImp α where
  himp a b := e.symm (e a ⇨ e b)
/-
**Equiv.himp_def** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：himp_def [HImp β] (a b : α) : letI
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma himp_def [HImp β] (a b : α) :
    letI := e.himp
    a ⇨ b = e.symm (e a ⇨ e b) := rfl

/-- Transfer `HNot` across an `Equiv`. -/
/-
**Equiv.hnot** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → α ≃ β → [HNot β] → HNot α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Transfer `HNot` across an `Equiv`.
-/
protected abbrev hnot [HNot β] : HNot α where
  hnot a := e.symm (￢e a)
/-
**Equiv.hnot_def** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：hnot_def [HNot β] (a : α) : letI
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hnot_def [HNot β] (a : α) :
    letI := e.hnot
    ￢a = e.symm (￢e a) := rfl

end Equiv

