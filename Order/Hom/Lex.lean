/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Data.Prod.Lex
public import Mathlib.Data.Sum.Order
public import Mathlib.Order.Hom.Set
public import Mathlib.Order.RelIso.Set

/-!
# Lexicographic order and order isomorphisms

## Main declarations

* `OrderIso.sumLexIioIci` and `OrderIso.sumLexIicIoi`: if `α` is a linear order and `x : α`,
  then `α` is order isomorphic to both `Iio x ⊕ₗ Ici x` and `Iic x ⊕ₗ Ioi x`.
* `Prod.Lex.prodUnique` and `Prod.Lex.uniqueProd`: `α ×ₗ β` is order isomorphic to one side if the
  other side is `Unique`.
-/

@[expose] public section

open Set

variable {α : Type*}

/-! ### Relation isomorphism -/

namespace RelIso

variable {r : α → α → Prop} {x y : α} [IsTrans α r] [Std.Trichotomous r] [DecidableRel r]

variable (r x) in
/-- A relation is isomorphic to the lexicographic sum of elements less than `x` and elements not
less than `x`. -/
/-
**RelIso.sumLexComplLeft** 是 Mathlib 中的一个定义，位于命名空间 `RelIso`。
形式化陈述：sumLexComplLeft : Sum.Lex (Subrel r (r · x)) (Subrel r (¬ r · x)) ≃r r whe
re toEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A relation is isomorphic to the lexicographic sum of elements less than `x` and 
elements not
less than `x`.
-/
def sumLexComplLeft : Sum.Lex (Subrel r (r · x)) (Subrel r (¬ r · x)) ≃r r where
  toEquiv := .sumCompl (r · x)
  map_rel_iff' := by
    rintro (⟨a, ha⟩ | ⟨a, ha⟩) (⟨b, hb⟩ | ⟨b, hb⟩)
    · simp
    · simpa using trans_trichotomous_right ha hb
    · simpa using fun h ↦ ha <| trans h hb
    · simp

@[simp]
/-
**RelIso.sumLexComplLeft_apply** 是 Mathlib 中的一个定理，位于命名空间 `RelIso`。
形式化陈述：sumLexComplLeft_apply (a) : sumLexComplLeft r x a = Equiv.sumCompl (r · x)
 a
参数：a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sumLexComplLeft_apply (a) : sumLexComplLeft r x a = Equiv.sumCompl (r · x) a :=
  rfl

@[simp]
/-
**RelIso.sumLexComplLeft_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `RelIso`。
形式化陈述：sumLexComplLeft_symm_apply (a) : sumLexComplLeft r x a = Equiv.sumCompl (r
 · x) a
参数：a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sumLexComplLeft_symm_apply (a) : sumLexComplLeft r x a = Equiv.sumCompl (r · x) a :=
  rfl

variable (r x) in
/-- A relation is isomorphic to the lexicographic sum of elements not greater than `x` and elements
greater than `x`. -/
/-
**RelIso.sumLexComplRight** 是 Mathlib 中的一个定义，位于命名空间 `RelIso`。
形式化陈述：sumLexComplRight : Sum.Lex (Subrel r (¬ r x ·)) (Subrel r (r x)) ≃r r wher
e toEquiv
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
A relation is isomorphic to the lexicographic sum of elements not greater than `
x` and elements
greater than `x`.
-/
def sumLexComplRight : Sum.Lex (Subrel r (¬ r x ·)) (Subrel r (r x)) ≃r r where
  toEquiv := (Equiv.sumComm _ _).trans <| .sumCompl (r x)
  map_rel_iff' := by
    rintro (⟨a, ha⟩ | ⟨a, ha⟩) (⟨b, hb⟩ | ⟨b, hb⟩)
    · simp
    · simpa using trans_trichotomous_left ha hb
    · simpa using fun h ↦ hb <| trans ha h
    · simp

@[simp]
/-
**RelIso.sumLexComplRight_apply** 是 Mathlib 中的一个定理，位于命名空间 `RelIso`。
形式化陈述：sumLexComplRight_apply (a) : sumLexComplRight r x a = Equiv.sumCompl (r x)
 a.swap
参数：a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sumLexComplRight_apply (a) : sumLexComplRight r x a = Equiv.sumCompl (r x) a.swap :=
  rfl

@[simp]
/-
**RelIso.sumLexComplRight_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `RelIso`。
形式化陈述：sumLexComplRight_symm_apply (a) : sumLexComplRight r x a = Equiv.sumCompl 
(r x) a.swap
参数：a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sumLexComplRight_symm_apply (a) : sumLexComplRight r x a = Equiv.sumCompl (r x) a.swap :=
  rfl

end RelIso

/-! ### Order isomorphism -/

namespace OrderIso

variable [LinearOrder α] {x y : α}

variable (x) in
/-- A linear order is isomorphic to the lexicographic sum of elements less than `x` and elements
greater or equal to `x`. -/
/-
**OrderIso.sumLexIioIci** 是 Mathlib 中的一个定义，位于命名空间 `OrderIso`。
形式化陈述：sumLexIioIci : Iio x oplusₗ Ici x ≃o α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A linear order is isomorphic to the lexicographic sum of elements less than `x` 
and elements
greater or equal to `x`.
-/
def sumLexIioIci : Iio x ⊕ₗ Ici x ≃o α :=
  (sumLexCongr (refl _) (setCongr (Ici x) {y | ¬ y < x} (by ext; simp))).trans <|
    ofRelIsoLT (RelIso.sumLexComplLeft (· < ·) x)

@[simp]
/-
**OrderIso.sumLexIioIci_apply_inl** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：sumLexIioIci_apply_inl (a : Iio x) : sumLexIioIci x (toLex <| Sum.inl a) =
 a
参数：a : Iio x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sumLexIioIci_apply_inl (a : Iio x) : sumLexIioIci x (toLex <| Sum.inl a) = a :=
  rfl

@[simp]
/-
**OrderIso.sumLexIioIci_apply_inr** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：sumLexIioIci_apply_inr (a : Ici x) : sumLexIioIci x (toLex <| Sum.inr a) =
 a
参数：a : Ici x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sumLexIioIci_apply_inr (a : Ici x) : sumLexIioIci x (toLex <| Sum.inr a) = a :=
  rfl
/-
**OrderIso.sumLexIioIci_symm_apply_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：sumLexIioIci_symm_apply_of_lt (h : y < x) : (sumLexIioIci x).symm y = toLe
x (Sum.inl ⟨y, h⟩)
参数：h : y < x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderIso.symm_apply_eq`：symm_apply_eq (e : α ≃o β) {x : α} {y : β} : e.s
ymm y = x ↔ y = e x
· 使用定理 `OrderIso.sumLexIioIci_apply_inl`：sumLexIioIci_apply_inl (a : Iio x) : su
mLexIioIci x (toLex <| Sum.inl a) = a
-/
theorem sumLexIioIci_symm_apply_of_lt (h : y < x) :
    (sumLexIioIci x).symm y = toLex (Sum.inl ⟨y, h⟩) := by
  rw [symm_apply_eq, sumLexIioIci_apply_inl]
/-
**OrderIso.sumLexIioIci_symm_apply_of_ge** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：sumLexIioIci_symm_apply_of_ge {y : α} (h : x <= y) : (sumLexIioIci x).symm
 y = toLex (Sum.inr ⟨y, h⟩)
参数：h : x <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderIso.symm_apply_eq`：symm_apply_eq (e : α ≃o β) {x : α} {y : β} : e.s
ymm y = x ↔ y = e x
· 使用定理 `OrderIso.sumLexIioIci_apply_inr`：sumLexIioIci_apply_inr (a : Ici x) : su
mLexIioIci x (toLex <| Sum.inr a) = a
-/
theorem sumLexIioIci_symm_apply_of_ge {y : α} (h : x ≤ y) :
    (sumLexIioIci x).symm y = toLex (Sum.inr ⟨y, h⟩) := by
  rw [symm_apply_eq, sumLexIioIci_apply_inr]

@[simp]
/-
**OrderIso.sumLexIioIci_symm_apply_Iio** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：sumLexIioIci_symm_apply_Iio (a : Iio x) : (sumLexIioIci x).symm a = toLex 
(Sum.inl a)
参数：a : Iio x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.sumLexIioIci_symm_apply_of_lt`：sumLexIioIci_symm_apply_of_lt (h
 : y < x) : (sumLexIioIci x).symm y = toLex (Sum.inl ⟨y, h⟩)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem sumLexIioIci_symm_apply_Iio (a : Iio x) : (sumLexIioIci x).symm a = toLex (Sum.inl a) :=
  sumLexIioIci_symm_apply_of_lt a.2

@[simp]
/-
**OrderIso.sumLexIioIci_symm_apply_Ici** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：sumLexIioIci_symm_apply_Ici (a : Ici x) : (sumLexIioIci x).symm a = toLex 
(Sum.inr a)
参数：a : Ici x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.sumLexIioIci_symm_apply_of_ge`：sumLexIioIci_symm_apply_of_ge {y
 : α} (h : x <= y) : (sumLexIioIci x).symm y = toLex (Sum.inr ⟨y, h⟩)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem sumLexIioIci_symm_apply_Ici (a : Ici x) : (sumLexIioIci x).symm a = toLex (Sum.inr a) :=
  sumLexIioIci_symm_apply_of_ge a.2

variable (x) in
/-- A linear order is isomorphic to the lexicographic sum of elements less or equal to `x` and
elements greater than `x`. -/
/-
**OrderIso.sumLexIicIoi** 是 Mathlib 中的一个定义，位于命名空间 `OrderIso`。
形式化陈述：sumLexIicIoi : Iic x oplusₗ Ioi x ≃o α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A linear order is isomorphic to the lexicographic sum of elements less or equal 
to `x` and
elements greater than `x`.
-/
def sumLexIicIoi : Iic x ⊕ₗ Ioi x ≃o α :=
  (sumLexCongr (setCongr (Iic x) {y | ¬ x < y} (by ext; simp)) (refl _)).trans <|
    ofRelIsoLT (RelIso.sumLexComplRight (· < ·) x)

@[simp]
/-
**OrderIso.sumLexIicIoi_apply_inl** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：sumLexIicIoi_apply_inl (a : Iic x) : sumLexIicIoi x (toLex <| Sum.inl a) =
 a
参数：a : Iic x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sumLexIicIoi_apply_inl (a : Iic x) : sumLexIicIoi x (toLex <| Sum.inl a) = a :=
  rfl

@[simp]
/-
**OrderIso.sumLexIicIoi_apply_inr** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：sumLexIicIoi_apply_inr (a : Ioi x) : sumLexIicIoi x (toLex <| Sum.inr a) =
 a
参数：a : Ioi x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sumLexIicIoi_apply_inr (a : Ioi x) : sumLexIicIoi x (toLex <| Sum.inr a) = a :=
  rfl
/-
**OrderIso.sumLexIicIoi_symm_apply_of_le** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：sumLexIicIoi_symm_apply_of_le (h : y <= x) : (sumLexIicIoi x).symm y = toL
ex (Sum.inl ⟨y, h⟩)
参数：h : y <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderIso.symm_apply_eq`：symm_apply_eq (e : α ≃o β) {x : α} {y : β} : e.s
ymm y = x ↔ y = e x
· 使用定理 `OrderIso.sumLexIicIoi_apply_inl`：sumLexIicIoi_apply_inl (a : Iic x) : su
mLexIicIoi x (toLex <| Sum.inl a) = a
-/
theorem sumLexIicIoi_symm_apply_of_le (h : y ≤ x) :
    (sumLexIicIoi x).symm y = toLex (Sum.inl ⟨y, h⟩) := by
  rw [symm_apply_eq, sumLexIicIoi_apply_inl]
/-
**OrderIso.sumLexIicIoi_symm_apply_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：sumLexIicIoi_symm_apply_of_lt {y : α} (h : x < y) : (sumLexIicIoi x).symm 
y = toLex (Sum.inr ⟨y, h⟩)
参数：h : x < y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderIso.symm_apply_eq`：symm_apply_eq (e : α ≃o β) {x : α} {y : β} : e.s
ymm y = x ↔ y = e x
· 使用定理 `OrderIso.sumLexIicIoi_apply_inr`：sumLexIicIoi_apply_inr (a : Ioi x) : su
mLexIicIoi x (toLex <| Sum.inr a) = a
-/
theorem sumLexIicIoi_symm_apply_of_lt {y : α} (h : x < y) :
    (sumLexIicIoi x).symm y = toLex (Sum.inr ⟨y, h⟩) := by
  rw [symm_apply_eq, sumLexIicIoi_apply_inr]

@[simp]
/-
**OrderIso.sumLexIicIoi_symm_apply_Iic** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：sumLexIicIoi_symm_apply_Iic (a : Iic x) : (sumLexIicIoi x).symm a = Sum.in
l a
参数：a : Iic x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.sumLexIicIoi_symm_apply_of_le`：sumLexIicIoi_symm_apply_of_le (h
 : y <= x) : (sumLexIicIoi x).symm y = toLex (Sum.inl ⟨y, h⟩)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem sumLexIicIoi_symm_apply_Iic (a : Iic x) : (sumLexIicIoi x).symm a = Sum.inl a :=
  sumLexIicIoi_symm_apply_of_le a.2

@[simp]
/-
**OrderIso.sumLexIicIoi_symm_apply_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：sumLexIicIoi_symm_apply_Ioi (a : Ioi x) : (sumLexIicIoi x).symm a = Sum.in
r a
参数：a : Ioi x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.sumLexIicIoi_symm_apply_of_lt`：sumLexIicIoi_symm_apply_of_lt {y
 : α} (h : x < y) : (sumLexIicIoi x).symm y = toLex (Sum.inr ⟨y, h⟩)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem sumLexIicIoi_symm_apply_Ioi (a : Ioi x) : (sumLexIicIoi x).symm a = Sum.inr a :=
  sumLexIicIoi_symm_apply_of_lt a.2

end OrderIso

/-! ### Degenerate products -/

namespace Prod.Lex
variable (α β : Type*)

set_option backward.isDefEq.respectTransparency.types false in
/-- Lexicographic product type with `Unique` type on the right is `OrderIso` to the left. -/
/-
**Prod.Lex.prodUnique** 是 Mathlib 中的一个定义，位于命名空间 `Prod.Lex`。
形式化陈述：prodUnique [PartialOrder α] [Preorder β] [Unique β] : α ×ₗ β ≃o α where to
Fun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lexicographic product type with `Unique` type on the right is `OrderIso` to the 
left.
-/
def prodUnique [PartialOrder α] [Preorder β] [Unique β] : α ×ₗ β ≃o α where
  toFun x := (ofLex x).1
  invFun x := toLex (x, default)
  left_inv x := x.rec fun (a, b) ↦ by simpa using Unique.default_eq b
  right_inv x := by simp
  map_rel_iff' {a b} := a.rec fun a ↦ b.rec fun b ↦ by
    simpa [Prod.Lex.toLex_le_toLex] using le_iff_lt_or_eq

variable {α β} in
@[simp]
/-
**Prod.Lex.prodUnique_apply** 是 Mathlib 中的一个定理，位于命名空间 `Prod.Lex`。
形式化陈述：prodUnique_apply [PartialOrder α] [Preorder β] [Unique β] (x : α ×ₗ β) : p
rodUnique α β x = (ofLex x).1
参数：x : α ×ₗ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prodUnique_apply [PartialOrder α] [Preorder β] [Unique β] (x : α ×ₗ β) :
    prodUnique α β x = (ofLex x).1 := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Lexicographic product type with `Unique` type on the left is `OrderIso` to the right. -/
/-
**Prod.Lex.uniqueProd** 是 Mathlib 中的一个定义，位于命名空间 `Prod.Lex`。
形式化陈述：uniqueProd [Preorder α] [Unique α] [LE β] : α ×ₗ β ≃o β where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lexicographic product type with `Unique` type on the left is `OrderIso` to the r
ight.
-/
def uniqueProd [Preorder α] [Unique α] [LE β] : α ×ₗ β ≃o β where
  toFun x := (ofLex x).2
  invFun x := toLex (default, x)
  left_inv x := x.rec fun (a, b) ↦ by simpa using Unique.default_eq a
  right_inv x := by simp
  map_rel_iff' {a b} := a.rec fun a ↦ b.rec fun b ↦ by
    have heq : a.1 = b.1 := Subsingleton.allEq _ _
    simp [Prod.Lex.toLex_le_toLex, heq]

variable {α β} in
@[simp]
/-
**Prod.Lex.uniqueProd_apply** 是 Mathlib 中的一个定理，位于命名空间 `Prod.Lex`。
形式化陈述：uniqueProd_apply [Preorder α] [Unique α] [LE β] (x : α ×ₗ β) : uniqueProd 
α β x = (ofLex x).2
参数：x : α ×ₗ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem uniqueProd_apply [Preorder α] [Unique α] [LE β] (x : α ×ₗ β) :
    uniqueProd α β x = (ofLex x).2 := rfl

/-- `Equiv.prodAssoc` promoted to an order isomorphism of lexicographic products. -/
@[simps!]
/-
**Prod.Lex.prodLexAssoc** 是 Mathlib 中的一个定义，位于命名空间 `Prod.Lex`。
形式化陈述：prodLexAssoc (α β γ : Type*) [Preorder α] [Preorder β] [Preorder γ] : (α ×
ₗ β) ×ₗ γ ≃o α ×ₗ β ×ₗ γ where toEquiv
参数：α β γ : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
`Equiv.prodAssoc` promoted to an order isomorphism of lexicographic products.
-/
def prodLexAssoc (α β γ : Type*)
    [Preorder α] [Preorder β] [Preorder γ] : (α ×ₗ β) ×ₗ γ ≃o α ×ₗ β ×ₗ γ where
  toEquiv := .trans ofLex <| .trans (.prodCongr ofLex <| .refl _) <|
      .trans (.prodAssoc α β γ) <| .trans (.prodCongr (.refl _) toLex) <| toLex
  map_rel_iff' := by
    simp only [Prod.Lex.le_iff, Prod.Lex.lt_iff, Equiv.trans_apply, Equiv.prodCongr_apply,
      Equiv.prodAssoc_apply]
    grind [EmbeddingLike.apply_eq_iff_eq, ofLex_toLex]

/-- `Equiv.sumProdDistrib` promoted to an order isomorphism of lexicographic products.

Right distributivity doesn't hold. A counterexample is `ℕ ×ₗ (Unit ⊕ₗ Unit) ≃o ℕ`
which is not isomorphic to `ℕ ×ₗ Unit ⊕ₗ ℕ ×ₗ Unit ≃o ℕ ⊕ₗ ℕ`. -/
@[simps!]
/-
**Prod.Lex.sumLexProdLexDistrib** 是 Mathlib 中的一个定义，位于命名空间 `Prod.Lex`。
形式化陈述：sumLexProdLexDistrib (α β γ : Type*) [Preorder α] [Preorder β] [Preorder γ
] : (α oplusₗ β) ×ₗ γ ≃o α ×ₗ γ oplusₗ β ×ₗ γ where toEquiv
参数：α β γ : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
`Equiv.sumProdDistrib` promoted to an order isomorphism of lexicographic product
s.

Right distributivity doesn't hold. A counterexample is `ℕ ×ₗ (Unit ⊕ₗ Unit) ≃o ℕ
`
which is not isomorphic to `ℕ ×ₗ Unit ⊕ₗ ℕ ×ₗ Unit ≃o ℕ ⊕ₗ ℕ`.
-/
def sumLexProdLexDistrib (α β γ : Type*)
    [Preorder α] [Preorder β] [Preorder γ] : (α ⊕ₗ β) ×ₗ γ ≃o α ×ₗ γ ⊕ₗ β ×ₗ γ where
  toEquiv := .trans ofLex <| .trans (.prodCongr ofLex <| .refl _) <|
    .trans (.sumProdDistrib α β γ) <| .trans (.sumCongr toLex toLex) toLex
  map_rel_iff' := by simp [Prod.Lex.le_iff]

/-- `Equiv.prodCongr` promoted to an order isomorphism between lexicographic products. -/
@[simps! apply]
/-
**Prod.Lex.prodLexCongr** 是 Mathlib 中的一个定义，位于命名空间 `Prod.Lex`。
形式化陈述：prodLexCongr {α β γ δ : Type*} [Preorder α] [Preorder β] [Preorder γ] [Pre
order δ] (ea : α ≃o β) (eb : γ ≃o δ) : α ×ₗ γ ≃o β ×ₗ δ where toEquiv
参数：ea : α ≃o β；eb : γ ≃o δ。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
`Equiv.prodCongr` promoted to an order isomorphism between lexicographic product
s.
-/
def prodLexCongr {α β γ δ : Type*} [Preorder α] [Preorder β]
    [Preorder γ] [Preorder δ] (ea : α ≃o β) (eb : γ ≃o δ) : α ×ₗ γ ≃o β ×ₗ δ where
  toEquiv := ofLex.trans ((Equiv.prodCongr ea eb).trans toLex)
  map_rel_iff' := by simp [Prod.Lex.le_iff]

end Prod.Lex

