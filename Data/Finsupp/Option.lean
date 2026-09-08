/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Algebra.Module.Defs

/-!
# Operations on `Finsupp`s with an `Option` domain

Similar to how `Finsupp.cons` and `Finsupp.tail` construct
an object of type `Fin (n + 1) →₀ M` from a map `Fin n →₀ M` and vice versa,
we define `Finsupp.optionElim` and `Finsupp.some`
to construct `Option α →₀ M` from a map α →₀ M, and vice versa.

As functions, these behave as `Option.elim'`, and as an application of `some` hence the names.

We prove a variety of API lemmas, see `Mathlib/Data/Finsupp/Fin.lean` for comparison.

## Main declarations

* `Finsupp.some`: restrict a finitely supported function on `Option α` to a finitely supported
  function on `α`.
* `Finsupp.optionElim`: extend a finitely supported function on `α`
  to a finitely supported function on `Option α`, provided a default value for `none`.

## Implementation notes

This file is a `noncomputable theory` and uses classical logic throughout.

-/

@[expose] public section


noncomputable section

open Finset Function

variable {α M N R : Type*}

namespace Finsupp

section Option

section Zero

variable [Zero M]

/-- Restrict a finitely supported function on `Option α` to a finitely supported function on `α`. -/
/-
**Finsupp.some** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：some (f : Option α ->₀ M) : α ->₀ M
参数：f : Option α ->₀ M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrict a finitely supported function on `Option α` to a finitely supported fun
ction on `α`.
-/
def some (f : Option α →₀ M) : α →₀ M :=
  f.comapDomain Option.some fun _ => by simp

@[simp]
/-
**Finsupp.some_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：some_apply (f : Option α ->₀ M) (a : α) : f.some a = f (Option.some a)
参数：f : Option α ->₀ M；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem some_apply (f : Option α →₀ M) (a : α) : f.some a = f (Option.some a) :=
  rfl

@[simp]
/-
**Finsupp.some_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：some_zero : (0 : Option α ->₀ M).some = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem some_zero : (0 : Option α →₀ M).some = 0 := by
  ext
  simp

end Zero

@[simp]
/-
**Finsupp.some_add** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：some_add [AddZeroClass M] (f g : Option α ->₀ M) : (f + g).some = f.some +
 g.some
参数：f g : Option α ->₀ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem some_add [AddZeroClass M] (f g : Option α →₀ M) : (f + g).some = f.some + g.some := by
  ext
  simp

section Zero

variable [Zero M]

@[simp]
/-
**Finsupp.some_single_none** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：some_single_none (m : M) : (single none m : Option α ->₀ M).some = 0
参数：m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.single_eq_of_ne`：single_eq_of_ne (h : a' != a) : (single a b : α
 ->₀ M) a' = 0
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem some_single_none (m : M) : (single none m : Option α →₀ M).some = 0 := by
  ext
  simp

@[simp]
/-
**Finsupp.some_single_some** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：some_single_some (a : α) (m : M) : (single (Option.some a) m : Option α ->
₀ M).some = single a m
参数：a : α；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem some_single_some (a : α) (m : M) :
    (single (Option.some a) m : Option α →₀ M).some = single a m := by
  classical
    ext b
    simp [single_apply]
/-
**Finsupp.some_embDomain_some** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：∀ {α : Type u_1} {M : Type u_2} [inst : Zero M] (f : α →₀ M), (Finsupp.emb
Domain Function.Embedding.some f).some = f
参数：f : α →₀ M；Finsupp.embDomain Function.Embedding.some f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.some_apply`：some_apply (f : Option α ->₀ M) (a : α) : f.some a =
 f (Option.some a)
· 使用定理 `Finsupp.embDomain_apply_self`：embDomain_apply_self (f : α ↪ β) (v : α ->
₀ M) (a : α) : embDomain f v (f a) = v a
-/
@[simp] lemma some_embDomain_some (f : α →₀ M) : (f.embDomain .some).some = f := by
  ext; rw [some_apply]; exact embDomain_apply_self _ _ _
/-
**Finsupp.embDomain_some_none** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：∀ {α : Type u_1} {M : Type u_2} [inst : Zero M] (f : α →₀ M), (Finsupp.emb
Domain Function.Embedding.some f) none = 0
参数：f : α →₀ M；Finsupp.embDomain Function.Embedding.some f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.embDomain_of_notMem_range`：embDomain_of_notMem_range (f : α ↪ β)
 (v : α ->₀ M) (a : β) (h : a ∉ Set.range f) : embDomain f v a = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.Embedding.some_apply`：∀ {α : Type u_1}, ⇑Function.Embedding.som
e = some
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
@[simp] lemma embDomain_some_none (f : α →₀ M) : f.embDomain .some .none = 0 :=
  embDomain_of_notMem_range _ _ _ (by simp)

@[simp]
/-
**Finsupp.embDomain_some_some** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：embDomain_some_some (f : α ->₀ M) (x) : f.embDomain .some (.some x) = f x
参数：f : α ->₀ M；x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Finsupp.embDomain_apply_self`：embDomain_apply_self (f : α ↪ β) (v : α ->
₀ M) (a : α) : embDomain f v (f a) = v a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem embDomain_some_some (f : α →₀ M) (x) : f.embDomain .some (.some x) = f x := by
  simp [← Function.Embedding.some_apply]

@[simp]
/-
**Finsupp.some_update_none** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：some_update_none (f : Option α ->₀ M) (a : M) : (f.update none a).some = f
.some
参数：f : Option α ->₀ M；a : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem some_update_none (f : Option α →₀ M) (a : M) :
    (f.update none a).some = f.some := by
  ext
  simp [Finsupp.update]

/-- `Finsupp`s from `Option` are equivalent to
pairs of an element and a `Finsupp` on the original type. -/
@[simps]
noncomputable
/-
**Finsupp.optionEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：optionEquiv : (Option α ->₀ M) ≃ M × (α ->₀ M) where toFun P
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def optionEquiv : (Option α →₀ M) ≃ M × (α →₀ M) where
  toFun P := (P none, P.some)
  invFun P := (P.2.embDomain .some).update none P.1
  left_inv P := by ext (_ | a) <;> simp [Finsupp.update]
  right_inv P := by ext <;> simp [Finsupp.update]

/--
Extend a finitely supported function on `α` to a finitely supported function on `Option α`,
provided a default value for `none`.
-/
/-
**Finsupp.optionElim** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：optionElim (y : M) (f : α ->₀ M) : Option α ->₀ M
参数：y : M；f : α ->₀ M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extend a finitely supported function on `α` to a finitely supported function on 
`Option α`,
provided a default value for `none`.
-/
def optionElim (y : M) (f : α →₀ M) : Option α →₀ M :=
  optionEquiv.invFun (y, f)
/-
**Finsupp.optionElim_apply_none** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：optionElim_apply_none (y : M) (f : α ->₀ M) : f.optionElim y none = y
参数：y : M；f : α ->₀ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.optionEquiv_symm_apply`：∀ {α : Type u_1} {M : Type u_2} [inst : 
Zero M] (P : M × (α →₀ M)),   Finsupp.optionEquiv.symm P = (Finsupp.embDomain Fu
nction.Embedding.som…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Finsupp.coe_update`：coe_update [DecidableEq α] : (f.update a b : α -> M)
 = Function.update f a b
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma optionElim_apply_none (y : M) (f : α →₀ M) : f.optionElim y none = y := by
  classical
  simp [optionElim]
/-
**Finsupp.optionElim_apply_some** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：optionElim_apply_some (y : M) (f : α ->₀ M) (x : α) : f.optionElim y (Opti
on.some x) = f x
参数：y : M；f : α ->₀ M；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.optionEquiv_symm_apply`：∀ {α : Type u_1} {M : Type u_2} [inst : 
Zero M] (P : M × (α →₀ M)),   Finsupp.optionEquiv.symm P = (Finsupp.embDomain Fu
nction.Embedding.som…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Finsupp.coe_update`：coe_update [DecidableEq α] : (f.update a b : α -> M)
 = Function.update f a b
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finsupp.embDomain_some_some`：embDomain_some_some (f : α ->₀ M) (x) : f.e
mbDomain .some (.some x) = f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma optionElim_apply_some (y : M) (f : α →₀ M) (x : α) :
    f.optionElim y (Option.some x) = f x := by
  classical
  simp [optionElim]

@[simp]
/-
**Finsupp.optionElim_apply_eq_elim** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：optionElim_apply_eq_elim (y : M) (f : α ->₀ M) (a : Option α) : f.optionEl
im y a = a.elim y f
参数：y : M；f : α ->₀ M；a : Option α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finsupp.optionElim_apply_none`：optionElim_apply_none (y : M) (f : α ->₀ 
M) : f.optionElim y none = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finsupp.optionElim_apply_some`：optionElim_apply_some (y : M) (f : α ->₀ 
M) (x : α) : f.optionElim y (Option.some x) = f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma optionElim_apply_eq_elim (y : M) (f : α →₀ M) (a : Option α) :
    f.optionElim y a = a.elim y f := by
  cases a with
  | none => exact optionElim_apply_none y f
  | some x => simp only [optionElim_apply_some, Option.elim_some]
/-
**Finsupp.optionElim_eq_elim'** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：optionElim_eq_elim' (y : M) (f : α ->₀ M) (a : Option α) : optionElim y f 
a = Option.elim' y f a
参数：y : M；f : α ->₀ M；a : Option α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Option.elim'`：elim'_update {α : Type*} {β : Type*} [DecidableEq α] (f : 
β) (g : α -> β) (a : α) (x : β) : Option.elim' f (update g a x) = update (Option
.e…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finsupp.optionElim_apply_eq_elim`：optionElim_apply_eq_elim (y : M) (f : 
α ->₀ M) (a : Option α) : f.optionElim y a = a.elim y f
· 使用定理 `Option.elim'_eq_elim`：∀ {α : Type u_3} {β : Type u_4} (b : β) (f : α → β
) (a : Option α), Option.elim' b f a = a.elim b f
-/
lemma optionElim_eq_elim' (y : M) (f : α →₀ M) (a : Option α) :
    optionElim y f a = Option.elim' y f a := by
  rw [optionElim_apply_eq_elim, Option.elim'_eq_elim]

@[simp]
/-
**Finsupp.some_optionElim** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：some_optionElim (y : M) (f : α ->₀ M) : (f.optionElim y).some = f
参数：y : M；f : α ->₀ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finsupp.optionElim_apply_eq_elim`：optionElim_apply_eq_elim (y : M) (f : 
α ->₀ M) (a : Option α) : f.optionElim y a = a.elim y f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma some_optionElim (y : M) (f : α →₀ M) : (f.optionElim y).some = f := by
  ext
  simp

@[simp]
/-
**Finsupp.optionElim_some** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：optionElim_some (f : Option α ->₀ M) : f.some.optionElim (f none) = f
参数：f : Option α ->₀ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finsupp.optionElim_apply_none`：optionElim_apply_none (y : M) (f : α ->₀ 
M) : f.optionElim y none = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Finsupp.optionElim_apply_eq_elim`：optionElim_apply_eq_elim (y : M) (f : 
α ->₀ M) (a : Option α) : f.optionElim y a = a.elim y f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma optionElim_some (f : Option α →₀ M) : f.some.optionElim (f none) = f := by
  ext a
  cases a
  · rw [optionElim_apply_none]
  · simp

@[simp]
/-
**Finsupp.optionElim_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：optionElim_zero (y : M) : (0 : α ->₀ M).optionElim y = single none y
参数：y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finsupp.optionElim_apply_eq_elim`：optionElim_apply_eq_elim (y : M) (f : 
α ->₀ M) (a : Option α) : f.optionElim y a = a.elim y f
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.single_eq_of_ne`：single_eq_of_ne (h : a' != a) : (single a b : α
 ->₀ M) a' = 0
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem optionElim_zero (y : M) : (0 : α →₀ M).optionElim y = single none y := by
  ext a
  cases a
  · simp
  · simp
/-
**Finsupp.optionElim_ne_zero_of_left** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：optionElim_ne_zero_of_left (y : M) (f : α ->₀ M) (h : y != 0) : f.optionEl
im y != 0
参数：y : M；f : α ->₀ M；h : y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Finsupp.optionElim_apply_eq_elim`：optionElim_apply_eq_elim (y : M) (f : 
α ->₀ M) (a : Option α) : f.optionElim y a = a.elim y f
-/
theorem optionElim_ne_zero_of_left (y : M) (f : α →₀ M) (h : y ≠ 0) : f.optionElim y ≠ 0 := by
  contrapose h with c
  have : f.optionElim y none = (0 : Option α →₀ M) none := by
    rw [c]
  simp only [optionElim_apply_eq_elim, Option.elim_none, coe_zero, Pi.zero_apply] at this
  exact this
/-
**Finsupp.optionElim_ne_zero_of_right** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：optionElim_ne_zero_of_right (y : M) (f : α ->₀ M) (h : f != 0) : f.optionE
lim y != 0
参数：y : M；f : α ->₀ M；h : f != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Finsupp.optionElim_apply_eq_elim`：optionElim_apply_eq_elim (y : M) (f : 
α ->₀ M) (a : Option α) : f.optionElim y a = a.elim y f
-/
theorem optionElim_ne_zero_of_right (y : M) (f : α →₀ M) (h : f ≠ 0) : f.optionElim y ≠ 0 := by
  contrapose h with c
  ext a
  have : f.optionElim y (Option.some a) = (0 : Option α →₀ M) (Option.some a) := by
    rw [c]
  simp only [optionElim_apply_eq_elim, Option.elim_some, coe_zero, Pi.zero_apply] at this
  exact this
/-
**Finsupp.optionElim_ne_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：optionElim_ne_zero_iff (y : M) (f : α ->₀ M) : f.optionElim y != 0 ↔ f != 
0 ∨ y != 0
参数：y : M；f : α ->₀ M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.optionElim_zero`：optionElim_zero (y : M) : (0 : α ->₀ M).optionE
lim y = single none y
· 使用定理 `Finsupp.single_zero`：single_zero (a : α) : (single a 0 : α ->₀ M) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.optionElim_ne_zero_of_right`：optionElim_ne_zero_of_right (y : M)
 (f : α ->₀ M) (h : f != 0) : f.optionElim y != 0
· 使用定理 `Finsupp.optionElim_ne_zero_of_left`：optionElim_ne_zero_of_left (y : M) (
f : α ->₀ M) (h : y != 0) : f.optionElim y != 0
-/
theorem optionElim_ne_zero_iff (y : M) (f : α →₀ M) :
    f.optionElim y ≠ 0 ↔ f ≠ 0 ∨ y ≠ 0 := by
  constructor
  · intro h
    contrapose! h
    rcases h with ⟨rfl, rfl⟩
    rw [optionElim_zero, single_zero]
  · intro h
    cases h with
    | inl h => exact optionElim_ne_zero_of_right y f h
    | inr h => exact optionElim_ne_zero_of_left y f h
/-
**Finsupp.eq_option_embedding_update_none_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp
`。
形式化陈述：eq_option_embedding_update_none_iff {n : Option α ->₀ M} {m : α ->₀ M} {i 
: M} : n = (embDomain Embedding.some m).update none i ↔ n none = i ∧ n.some = m
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
· 使用定理 `Prod.ext_iff`：∀ {α : Type u} {β : Type v} {x y : α × β}, x = y ↔ x.1 = y
.1 ∧ x.2 = y.2
-/
theorem eq_option_embedding_update_none_iff {n : Option α →₀ M} {m : α →₀ M} {i : M} :
    n = (embDomain Embedding.some m).update none i ↔ n none = i ∧ n.some = m :=
  (optionEquiv.eq_symm_apply (x := (_, _))).trans Prod.ext_iff

end Zero

@[to_additive]
/-
**Finsupp.prod_option_index** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：prod_option_index [AddZeroClass M] [CommMonoid N] (f : Option α ->₀ M) (b 
: Option α -> M -> N) (h_zero : forall o, b o 0 = 1) (h_add : forall o m₁ m₂, b 
o (m₁ + m₂) = b o m₁ * b o m₂) : f.prod b = b none (f none) * f.some.prod fun a 
=> b (Option.some a)
参数：f : Option α ->₀ M；b : Option α -> M -> N；h_zero : forall o, b o 0 = 1；h_add 
: forall o m₁ m₂, b o (m₁ + m₂) = b o m₁ * b o m₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finsupp.induction_linear`：induction_linear {motive : (ι ->₀ M) -> Prop} 
(f : ι ->₀ M) (zero : motive 0) (add : forall f g : ι ->₀ M, motive f -> motive 
g -> motive (f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.some_zero`：some_zero : (0 : Option α ->₀ M).some = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finsupp.prod_add_index`：prod_add_index [DecidableEq α] [AddZeroClass M] 
[CommMonoid N] {f g : α ->₀ M} {h : α -> M -> N} (h_zero : forall a in f.support
 union g.sup…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finsupp.some_add`：some_add [AddZeroClass M] (f g : Option α ->₀ M) : (f 
+ g).some = f.some + g.some
· 使用定理 `mul_mul_mul_comm`：mul_mul_mul_comm (a b c d : G) : a * b * (c * d) = a *
 c * (b * d)
· 使用定理 `Finsupp.prod_single_index`：prod_single_index {a : α} {b : M} {h : α -> M
 -> N} (h_zero : h a 0 = 1) : (single a b).prod h = h a b
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `Finsupp.some_single_none`：some_single_none (m : M) : (single none m : Op
tion α ->₀ M).some = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.single_eq_of_ne`：single_eq_of_ne (h : a' != a) : (single a b : α
 ->₀ M) a' = 0
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finsupp.some_single_some`：some_single_some (a : α) (m : M) : (single (Op
tion.some a) m : Option α ->₀ M).some = single a m
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem prod_option_index [AddZeroClass M] [CommMonoid N] (f : Option α →₀ M)
    (b : Option α → M → N) (h_zero : ∀ o, b o 0 = 1)
    (h_add : ∀ o m₁ m₂, b o (m₁ + m₂) = b o m₁ * b o m₂) :
    f.prod b = b none (f none) * f.some.prod fun a => b (Option.some a) := by
  classical
    induction f using induction_linear with
    | zero => simp [some_zero, h_zero]
    | add f₁ f₂ h₁ h₂ =>
      rw [Finsupp.prod_add_index, h₁, h₂, some_add, Finsupp.prod_add_index]
      · simp only [h_add, Pi.add_apply, Finsupp.coe_add]
        rw [mul_mul_mul_comm]
      all_goals simp [h_zero, h_add]
    | single a m => cases a <;> simp [h_zero]
/-
**Finsupp.sum_option_index_smul** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：sum_option_index_smul [Semiring R] [AddCommMonoid M] [Module R M] (f : Opt
ion α ->₀ R) (b : Option α -> M) : (f.sum fun o r => r • b o) = f none • b none 
+ f.some.sum fun a r => r • b (Option.some a)
参数：f : Option α ->₀ R；b : Option α -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.sum_option_index`：∀ {α : Type u_1} {M : Type u_2} {N : Type u_3}
 [inst : AddZeroClass M] [inst_1 : AddCommMonoid N] (f : Option α →₀ M)   (b : O
ption α → M → …
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
-/
theorem sum_option_index_smul [Semiring R] [AddCommMonoid M] [Module R M] (f : Option α →₀ R)
    (b : Option α → M) :
    (f.sum fun o r => r • b o) = f none • b none + f.some.sum fun a r => r • b (Option.some a) :=
  f.sum_option_index _ (fun _ => zero_smul _ _) fun _ _ _ => add_smul _ _ _

@[simp]
/-
**Finsupp.optionElim_add** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：optionElim_add [AddZeroClass M] (a b : α ->₀ M) (i j : M) : (a + b).option
Elim (i + j) = a.optionElim i + b.optionElim j
参数：a b : α ->₀ M；i j : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finsupp.optionElim_apply_eq_elim`：optionElim_apply_eq_elim (y : M) (f : 
α ->₀ M) (a : Option α) : f.optionElim y a = a.elim y f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma optionElim_add [AddZeroClass M] (a b : α →₀ M) (i j : M) :
    (a + b).optionElim (i + j) = a.optionElim i + b.optionElim j := by
  ext x; cases x <;> simp

end Option

end Finsupp

