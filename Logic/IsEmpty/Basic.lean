/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Logic.Function.Basic
public import Mathlib.Logic.IsEmpty.Defs
public import Mathlib.Logic.Relator

/-!
In this file we prove some basic properties about the typeclass `IsEmpty`.
-/

public section

variable {α β γ : Sort*}

@[simp, push]
/-
**not_nonempty_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_nonempty_iff : ¬Nonempty α ↔ IsEmpty α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.elim`：∀ {α : Sort u} {p : Prop}, Nonempty α → (∀ (a : α), p) → 
p
-/
theorem not_nonempty_iff : ¬Nonempty α ↔ IsEmpty α :=
  ⟨fun h ↦ ⟨fun x ↦ h ⟨x⟩⟩, fun h1 h2 ↦ h2.elim h1.elim⟩

@[simp, push]
/-
**not_isEmpty_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_isEmpty_iff : ¬IsEmpty α ↔ Nonempty α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_iff_comm`：not_iff_comm : (¬a ↔ b) ↔ (¬b ↔ a)
· 使用定理 `not_nonempty_iff`：not_nonempty_iff : ¬Nonempty α ↔ IsEmpty α
-/
theorem not_isEmpty_iff : ¬IsEmpty α ↔ Nonempty α :=
  not_iff_comm.mp not_nonempty_iff

@[simp]
/-
**isEmpty_Prop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isEmpty_Prop {p : Prop} : IsEmpty p ↔ ¬p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isEmpty_Prop {p : Prop} : IsEmpty p ↔ ¬p := by
  simp only [← not_nonempty_iff, nonempty_prop]

@[simp]
/-
**isEmpty_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isEmpty_pi {π : α -> Sort*} : IsEmpty (forall a, π a) ↔ exists a, IsEmpty 
(π a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isEmpty_pi {π : α → Sort*} : IsEmpty (∀ a, π a) ↔ ∃ a, IsEmpty (π a) := by
  simp only [← not_nonempty_iff, Classical.nonempty_pi, not_forall]
/-
**isEmpty_fun** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isEmpty_fun : IsEmpty (α -> β) ↔ Nonempty α ∧ IsEmpty β
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isEmpty_pi`：isEmpty_pi {π : α -> Sort*} : IsEmpty (forall a, π a) ↔ exis
ts a, IsEmpty (π a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `exists_true_iff_nonempty`：exists_true_iff_nonempty {α : Sort*} : (exists
 _ : α, True) ↔ Nonempty α
· 使用定理 `exists_and_right`：∀ {α : Sort u_1} {p : α → Prop} {b : Prop}, (∃ x, p x 
∧ b) ↔ (∃ x, p x) ∧ b
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isEmpty_fun : IsEmpty (α → β) ↔ Nonempty α ∧ IsEmpty β := by
  rw [isEmpty_pi, ← exists_true_iff_nonempty, ← exists_and_right, true_and]

@[simp]
/-
**nonempty_fun** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nonempty_fun : Nonempty (α -> β) ↔ IsEmpty α ∨ Nonempty β
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_or`：∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q
· 使用定理 `not_nonempty_iff`：not_nonempty_iff : ¬Nonempty α ↔ IsEmpty α
· 使用定理 `isEmpty_fun`：isEmpty_fun : IsEmpty (α -> β) ↔ Nonempty α ∧ IsEmpty β
· 使用定理 `not_isEmpty_iff`：not_isEmpty_iff : ¬IsEmpty α ↔ Nonempty α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem nonempty_fun : Nonempty (α → β) ↔ IsEmpty α ∨ Nonempty β :=
  not_iff_not.mp <| by rw [not_or, not_nonempty_iff, not_nonempty_iff, isEmpty_fun, not_isEmpty_iff]

@[simp]
/-
**isEmpty_sigma** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isEmpty_sigma {α} {E : α -> Type*} : IsEmpty (Sigma E) ↔ forall a, IsEmpty
 (E a)
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
theorem isEmpty_sigma {α} {E : α → Type*} : IsEmpty (Sigma E) ↔ ∀ a, IsEmpty (E a) := by
  simp only [← not_nonempty_iff, nonempty_sigma, not_exists]

@[simp]
/-
**isEmpty_psigma** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isEmpty_psigma {α} {E : α -> Sort*} : IsEmpty (PSigma E) ↔ forall a, IsEmp
ty (E a)
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
theorem isEmpty_psigma {α} {E : α → Sort*} : IsEmpty (PSigma E) ↔ ∀ a, IsEmpty (E a) := by
  simp only [← not_nonempty_iff, nonempty_psigma, not_exists]
/-
**isEmpty_subtype** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isEmpty_subtype (p : α -> Prop) : IsEmpty (Subtype p) ↔ forall x, ¬p x
参数：p : α -> Prop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isEmpty_subtype (p : α → Prop) : IsEmpty (Subtype p) ↔ ∀ x, ¬p x := by
  simp only [← not_nonempty_iff, nonempty_subtype, not_exists]

@[simp]
/-
**isEmpty_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isEmpty_prod {α β : Type*} : IsEmpty (α × β) ↔ IsEmpty α ∨ IsEmpty β
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
theorem isEmpty_prod {α β : Type*} : IsEmpty (α × β) ↔ IsEmpty α ∨ IsEmpty β := by
  simp only [← not_nonempty_iff, nonempty_prod, not_and_or]

@[simp]
/-
**isEmpty_pprod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isEmpty_pprod : IsEmpty (PProd α β) ↔ IsEmpty α ∨ IsEmpty β
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
theorem isEmpty_pprod : IsEmpty (PProd α β) ↔ IsEmpty α ∨ IsEmpty β := by
  simp only [← not_nonempty_iff, nonempty_pprod, not_and_or]

@[simp]
/-
**isEmpty_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isEmpty_sum {α β} : IsEmpty (α oplus β) ↔ IsEmpty α ∧ IsEmpty β
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
theorem isEmpty_sum {α β} : IsEmpty (α ⊕ β) ↔ IsEmpty α ∧ IsEmpty β := by
  simp only [← not_nonempty_iff, nonempty_sum, not_or]

@[simp]
/-
**isEmpty_psum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isEmpty_psum {α β} : IsEmpty (α oplus' β) ↔ IsEmpty α ∧ IsEmpty β
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
theorem isEmpty_psum {α β} : IsEmpty (α ⊕' β) ↔ IsEmpty α ∧ IsEmpty β := by
  simp only [← not_nonempty_iff, nonempty_psum, not_or]

@[simp]
/-
**isEmpty_ulift** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isEmpty_ulift {α} : IsEmpty (ULift α) ↔ IsEmpty α
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
theorem isEmpty_ulift {α} : IsEmpty (ULift α) ↔ IsEmpty α := by
  simp only [← not_nonempty_iff, nonempty_ulift]

@[simp]
/-
**isEmpty_plift** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isEmpty_plift {α} : IsEmpty (PLift α) ↔ IsEmpty α
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
theorem isEmpty_plift {α} : IsEmpty (PLift α) ↔ IsEmpty α := by
  simp only [← not_nonempty_iff, nonempty_plift]
/-
**wellFounded_of_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：wellFounded_of_isEmpty {α} [IsEmpty α] (r : α -> α -> Prop) : WellFounded 
r
参数：r : α -> α -> Prop。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem wellFounded_of_isEmpty {α} [IsEmpty α] (r : α → α → Prop) : WellFounded r :=
  ⟨isEmptyElim⟩

variable (α)
/-
**isEmpty_or_nonempty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_isEmpty_iff`：not_isEmpty_iff : ¬IsEmpty α ↔ Nonempty α
-/
theorem isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α :=
  (em <| IsEmpty α).elim Or.inl <| Or.inr ∘ not_isEmpty_iff.mp

@[simp]
/-
**not_isEmpty_of_nonempty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_isEmpty_of_nonempty [h : Nonempty α] : ¬IsEmpty α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_isEmpty_iff`：not_isEmpty_iff : ¬IsEmpty α ↔ Nonempty α
-/
theorem not_isEmpty_of_nonempty [h : Nonempty α] : ¬IsEmpty α :=
  not_isEmpty_iff.mpr h

variable {α}
/-
**Function.extend_of_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.extend_of_isEmpty [IsEmpty α] (f : α -> β) (g : α -> γ) (h : β ->
 γ) : Function.extend f g h = h
参数：f : α -> β；g : α -> γ；h : β -> γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.extend_apply'`：extend_apply' (g : α -> γ) (e' : β -> γ) (b : β)
 (hb : ¬exists a, f a = b) : extend f g e' b = e' b
-/
theorem Function.extend_of_isEmpty [IsEmpty α] (f : α → β) (g : α → γ) (h : β → γ) :
    Function.extend f g h = h :=
  funext fun _ ↦ (Function.extend_apply' _ _ _) fun ⟨a, _⟩ ↦ isEmptyElim a

open Relator

variable {α β : Type*} (R : α → β → Prop)

@[simp]
/-
**leftTotal_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：leftTotal_empty [IsEmpty α] : LeftTotal R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem leftTotal_empty [IsEmpty α] : LeftTotal R := by
  simp only [LeftTotal, IsEmpty.forall_iff]
/-
**leftTotal_iff_isEmpty_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：leftTotal_iff_isEmpty_left [IsEmpty β] : LeftTotal R ↔ IsEmpty α
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
theorem leftTotal_iff_isEmpty_left [IsEmpty β] : LeftTotal R ↔ IsEmpty α := by
  simp only [LeftTotal, IsEmpty.exists_iff, isEmpty_iff]

@[simp]
/-
**rightTotal_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rightTotal_empty [IsEmpty β] : RightTotal R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem rightTotal_empty [IsEmpty β] : RightTotal R := by
  simp only [RightTotal, IsEmpty.forall_iff]
/-
**rightTotal_iff_isEmpty_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rightTotal_iff_isEmpty_right [IsEmpty α] : RightTotal R ↔ IsEmpty β
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
theorem rightTotal_iff_isEmpty_right [IsEmpty α] : RightTotal R ↔ IsEmpty β := by
  simp only [RightTotal, IsEmpty.exists_iff, isEmpty_iff]

@[simp]
/-
**biTotal_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：biTotal_empty [IsEmpty α] [IsEmpty β] : BiTotal R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `leftTotal_empty`：leftTotal_empty [IsEmpty α] : LeftTotal R
· 使用定理 `rightTotal_empty`：rightTotal_empty [IsEmpty β] : RightTotal R
-/
theorem biTotal_empty [IsEmpty α] [IsEmpty β] : BiTotal R :=
  ⟨leftTotal_empty R, rightTotal_empty R⟩
/-
**biTotal_iff_isEmpty_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：biTotal_iff_isEmpty_right [IsEmpty α] : BiTotal R ↔ IsEmpty β
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem biTotal_iff_isEmpty_right [IsEmpty α] : BiTotal R ↔ IsEmpty β := by
  simp only [BiTotal, leftTotal_empty, rightTotal_iff_isEmpty_right, true_and]
/-
**biTotal_iff_isEmpty_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：biTotal_iff_isEmpty_left [IsEmpty β] : BiTotal R ↔ IsEmpty α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem biTotal_iff_isEmpty_left [IsEmpty β] : BiTotal R ↔ IsEmpty α := by
  simp only [BiTotal, leftTotal_iff_isEmpty_left, rightTotal_empty, and_true]
/-
**Function.Surjective.of_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.Surjective.of_isEmpty [IsEmpty β] (f : α -> β) : f.Surjective
参数：f : α -> β。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Function.Surjective.of_isEmpty [IsEmpty β] (f : α → β) : f.Surjective := IsEmpty.elim ‹_›
/-
**Function.surjective_iff_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.surjective_iff_isEmpty [IsEmpty α] (f : α -> β) : f.Surjective ↔ 
IsEmpty β
参数：f : α -> β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.isEmpty`：Function.Surjective.isEmpty [IsEmpty α] {f 
: α -> β} (hf : f.Surjective) : IsEmpty β
· 使用定理 `Function.Surjective.of_isEmpty`：Function.Surjective.of_isEmpty [IsEmpty 
β] (f : α -> β) : f.Surjective
-/
theorem Function.surjective_iff_isEmpty [IsEmpty α] (f : α → β) : f.Surjective ↔ IsEmpty β :=
  ⟨Surjective.isEmpty, fun _ ↦ .of_isEmpty f⟩
/-
**Function.Bijective.of_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.Bijective.of_isEmpty (f : α -> β) [IsEmpty β] : f.Bijective
参数：f : α -> β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.isEmpty`：∀ {α : Sort u} {β : Sort v} [IsEmpty β] (f : α → β), I
sEmpty α
· 使用定理 `Function.injective_of_subsingleton`：∀ {α : Sort u_1} {β : Sort u_2} [Sub
singleton α] (f : α → β), Function.Injective f
· 使用定理 `IsEmpty.instSubsingleton`：∀ {α : Sort u} [IsEmpty α], Subsingleton α
· 使用定理 `Function.Surjective.of_isEmpty`：Function.Surjective.of_isEmpty [IsEmpty 
β] (f : α -> β) : f.Surjective
-/
theorem Function.Bijective.of_isEmpty (f : α → β) [IsEmpty β] : f.Bijective :=
  have := f.isEmpty
  ⟨injective_of_subsingleton f, .of_isEmpty f⟩
/-
**Function.not_surjective_of_isEmpty_of_nonempty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.not_surjective_of_isEmpty_of_nonempty [IsEmpty α] [Nonempty β] (f
 : α -> β) : ¬f.Surjective
参数：f : α -> β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_isEmpty_of_nonempty`：not_isEmpty_of_nonempty [h : Nonempty α] : ¬IsE
mpty α
· 使用定理 `Function.Surjective.isEmpty`：Function.Surjective.isEmpty [IsEmpty α] {f 
: α -> β} (hf : f.Surjective) : IsEmpty β
-/
theorem Function.not_surjective_of_isEmpty_of_nonempty [IsEmpty α] [Nonempty β] (f : α → β) :
    ¬f.Surjective :=
  (not_isEmpty_of_nonempty β ·.isEmpty)
