/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Order.Hom.Monoid
public import Mathlib.Data.Prod.Lex
public import Mathlib.Order.Prod.Lex.Hom

/-!
# Order homomorphisms for products of ordered monoids

This file defines order homomorphisms for products of ordered monoids, for both the plain product
and the lexicographic product.

The product of ordered monoids `α × β` is an ordered monoid itself with both natural inclusions
and projections, making it the coproduct as well.

## TODO

Create the "OrdCommMon" category.

-/

@[expose] public section

namespace MonoidHom

variable {α β : Type*} [Monoid α] [Preorder α] [Monoid β] [Preorder β]

@[to_additive]
/-
**MonoidHom.inl_mono** 是 Mathlib 中的一个引理，位于命名空间 `MonoidHom`。
形式化陈述：inl_mono : Monotone (MonoidHom.inl α β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
lemma inl_mono : Monotone (MonoidHom.inl α β) :=
  fun _ _ ↦ by simp

@[to_additive]
/-
**MonoidHom.inl_strictMono** 是 Mathlib 中的一个引理，位于命名空间 `MonoidHom`。
形式化陈述：inl_strictMono : StrictMono (MonoidHom.inl α β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
-/
lemma inl_strictMono : StrictMono (MonoidHom.inl α β) :=
  fun _ _ ↦ by simp

@[to_additive]
/-
**MonoidHom.inr_mono** 是 Mathlib 中的一个引理，位于命名空间 `MonoidHom`。
形式化陈述：inr_mono : Monotone (MonoidHom.inr α β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
lemma inr_mono : Monotone (MonoidHom.inr α β) :=
  fun _ _ ↦ by simp

@[to_additive]
/-
**MonoidHom.inr_strictMono** 是 Mathlib 中的一个引理，位于命名空间 `MonoidHom`。
形式化陈述：inr_strictMono : StrictMono (MonoidHom.inr α β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
-/
lemma inr_strictMono : StrictMono (MonoidHom.inr α β) :=
  fun _ _ ↦ by simp

@[to_additive]
/-
**MonoidHom.fst_mono** 是 Mathlib 中的一个引理，位于命名空间 `MonoidHom`。
形式化陈述：fst_mono : Monotone (MonoidHom.fst α β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma fst_mono : Monotone (MonoidHom.fst α β) :=
  fun _ _ ↦ by simp +contextual [Prod.le_def]

@[to_additive]
/-
**MonoidHom.snd_mono** 是 Mathlib 中的一个引理，位于命名空间 `MonoidHom`。
形式化陈述：snd_mono : Monotone (MonoidHom.snd α β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma snd_mono : Monotone (MonoidHom.snd α β) :=
  fun _ _ ↦ by simp +contextual [Prod.le_def]

end MonoidHom

namespace OrderMonoidHom

variable (α β : Type*) [Monoid α] [PartialOrder α] [Monoid β] [Preorder β]

/-- Given ordered monoids M, N, the natural inclusion ordered homomorphism from M to M × N. -/
@[to_additive (attr := simps!) /-- Given ordered additive monoids M, N, the natural inclusion
ordered homomorphism from M to M × N. -/]
/-
**OrderMonoidHom.inl** 是 Mathlib 中的一个定义，位于命名空间 `OrderMonoidHom`。
形式化陈述：inl : α ->*o α × β where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def inl : α →*o α × β where
  __ := MonoidHom.inl _ _
  monotone' := MonoidHom.inl_mono

/-- Given ordered monoids M, N, the natural inclusion ordered homomorphism from N to M × N. -/
@[to_additive (attr := simps!) /-- Given ordered additive monoids M, N, the natural inclusion
ordered homomorphism from N to M × N. -/]
/-
**OrderMonoidHom.inr** 是 Mathlib 中的一个定义，位于命名空间 `OrderMonoidHom`。
形式化陈述：inr : β ->*o α × β where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def inr : β →*o α × β where
  __ := MonoidHom.inr _ _
  monotone' := MonoidHom.inr_mono

/-- Given ordered monoids M, N, the natural projection ordered homomorphism from M × N to M. -/
@[to_additive (attr := simps!) /-- Given ordered additive monoids M, N, the natural projection
ordered homomorphism from M × N to M. -/]
/-
**OrderMonoidHom.fst** 是 Mathlib 中的一个定义，位于命名空间 `OrderMonoidHom`。
形式化陈述：fst : α × β ->*o α where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def fst : α × β →*o α where
  __ := MonoidHom.fst _ _
  monotone' := MonoidHom.fst_mono

/-- Given ordered monoids M, N, the natural projection ordered homomorphism from M × N to N. -/
@[to_additive (attr := simps!) /-- Given ordered additive monoids M, N, the natural projection
ordered homomorphism from M × N to N. -/]
/-
**OrderMonoidHom.snd** 是 Mathlib 中的一个定义，位于命名空间 `OrderMonoidHom`。
形式化陈述：snd : α × β ->*o β where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def snd : α × β →*o β where
  __ := MonoidHom.snd _ _
  monotone' := MonoidHom.snd_mono

/-- Given ordered monoids M, N, the natural inclusion ordered homomorphism from M to the
lexicographic M ×ₗ N. -/
@[to_additive (attr := simps!) /-- Given ordered additive monoids M, N, the natural inclusion
ordered homomorphism from M to the lexicographic M ×ₗ N. -/]
/-
**OrderMonoidHom.inl** 是 Mathlib 中的一个定义，位于命名空间 `OrderMonoidHom`。
形式化陈述：inl : α ->*o α × β where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def inlₗ : α →*o α ×ₗ β where
  __ := (Prod.Lex.toLexOrderHom).comp (inl α β)
  map_one' := rfl
  map_mul' := by simp [← toLex_mul]

/-- Given ordered monoids M, N, the natural inclusion ordered homomorphism from N to the
lexicographic M ×ₗ N. -/
@[to_additive (attr := simps!) /-- Given ordered additive monoids M, N, the natural inclusion
ordered homomorphism from N to the lexicographic M ×ₗ N. -/]
/-
**OrderMonoidHom.inr** 是 Mathlib 中的一个定义，位于命名空间 `OrderMonoidHom`。
形式化陈述：inr : β ->*o α × β where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def inrₗ : β →*o (α ×ₗ β) where
  __ := Prod.Lex.toLexOrderHom.comp (inr α β)
  map_one' := rfl
  map_mul' := by simp [← toLex_mul]

/-- Given ordered monoids M, N, the natural projection ordered homomorphism from the
lexicographic M ×ₗ N to M. -/
@[to_additive (attr := simps!) /-- Given ordered additive monoids M, N, the natural projection
ordered homomorphism from the lexicographic M ×ₗ N to M. -/]
/-
**OrderMonoidHom.fst** 是 Mathlib 中的一个定义，位于命名空间 `OrderMonoidHom`。
形式化陈述：fst : α × β ->*o α where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def fstₗ : (α ×ₗ β) →*o α where
  toFun p := (ofLex p).fst
  map_one' := rfl
  map_mul' := by simp
  monotone' := Prod.Lex.monotone_fst_ofLex

@[to_additive (attr := simp)]
/-
**OrderMonoidHom.fst_comp_inl** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidHom`。
形式化陈述：fst_comp_inl : (fst α β).comp (inl α β) = .id α
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_comp_inl : (fst α β).comp (inl α β) = .id α :=
  rfl

@[to_additive (attr := simp)]
/-
**OrderMonoidHom.fst** 是 Mathlib 中的一个定义，位于命名空间 `OrderMonoidHom`。
形式化陈述：fst : α × β ->*o α where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fstₗ_comp_inlₗ : (fstₗ α β).comp (inlₗ α β) = .id α :=
  rfl

@[to_additive (attr := simp)]
/-
**OrderMonoidHom.snd_comp_inl** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidHom`。
形式化陈述：snd_comp_inl : (snd α β).comp (inl α β) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_comp_inl : (snd α β).comp (inl α β) = 1 :=
  rfl

@[to_additive (attr := simp)]
/-
**OrderMonoidHom.fst_comp_inr** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidHom`。
形式化陈述：fst_comp_inr : (fst α β).comp (inr α β) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_comp_inr : (fst α β).comp (inr α β) = 1 :=
  rfl

@[to_additive (attr := simp)]
/-
**OrderMonoidHom.snd_comp_inr** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidHom`。
形式化陈述：snd_comp_inr : (snd α β).comp (inr α β) = .id β
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_comp_inr : (snd α β).comp (inr α β) = .id β :=
  rfl

@[to_additive]
/-
**OrderMonoidHom.inl_mul_inr_eq_mk** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidHom`。
形式化陈述：inl_mul_inr_eq_mk (m : α) (n : β) : inl α β m * inr α β n = (m, n)
参数：m : α；n : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `OrderMonoidHom.inl_apply`：∀ (α : Type u_1) (β : Type u_2) [inst : Monoid
 α] [inst_1 : PartialOrder α] [inst_2 : Monoid β] [inst_3 : Preorder β]   (x : α
), (OrderMonoi…
· 使用定理 `OrderMonoidHom.inr_apply`：∀ (α : Type u_1) (β : Type u_2) [inst : Monoid
 α] [inst_1 : PartialOrder α] [inst_2 : Monoid β] [inst_3 : Preorder β]   (y : β
), (OrderMonoi…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inl_mul_inr_eq_mk (m : α) (n : β) : inl α β m * inr α β n = (m, n) := by
  simp

@[to_additive]
/-
**OrderMonoidHom.inl** 是 Mathlib 中的一个定义，位于命名空间 `OrderMonoidHom`。
形式化陈述：inl : α ->*o α × β where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inlₗ_mul_inrₗ_eq_toLex (m : α) (n : β) : inlₗ α β m * inrₗ α β n = toLex (m, n) := by
  simp [← toLex_mul]

variable {α β}

@[to_additive]
/-
**OrderMonoidHom.commute_inl_inr** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidHom`。
形式化陈述：commute_inl_inr (m : α) (n : β) : Commute (inl α β m) (inr α β n)
参数：m : α；n : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.prod`：Commute.prod {x y : M × N} (hm : Commute x.1 y.1) (hn : Co
mmute x.2 y.2) : Commute x y
· 使用定理 `Commute.one_right`：one_right (a : M) : Commute a 1
· 使用定理 `Commute.one_left`：one_left (a : M) : Commute 1 a
-/
theorem commute_inl_inr (m : α) (n : β) : Commute (inl α β m) (inr α β n) :=
  Commute.prod (.one_right m) (.one_left n)

@[to_additive]
/-
**OrderMonoidHom.commute_inl** 是 Mathlib 中的一个定理，位于命名空间 `OrderMonoidHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem commute_inlₗ_inrₗ (m : α) (n : β) : Commute (inlₗ α β m) (inrₗ α β n) :=
  Commute.prod (.one_right m) (.one_left n)

end OrderMonoidHom

