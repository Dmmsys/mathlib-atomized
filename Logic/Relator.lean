/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Logic.Function.Defs

/-!
# Relator for functions, pairs, sums, and lists.
-/

@[expose] public section

namespace Relator
universe u₁ u₂ v₁ v₂

/- TODO(johoelzl):
* should we introduce relators of datatypes as recursive function or as inductive
  predicate? For now we stick to the recursor approach.
* relation lift for datatypes, Π, Σ, set, and subtype types
* proof composition and identity laws
* implement method to derive relators from datatype
-/

section

variable {α : Sort u₁} {β : Sort u₂} {γ : Sort v₁} {δ : Sort v₂}
variable (R : α → β → Prop) (S : γ → δ → Prop)

/-- The binary relations `R : α → β → Prop` and `S : γ → δ → Prop` induce a binary
relation on functions `LiftFun : (α → γ) → (β → δ) → Prop`. -/
/-
**Relator.LiftFun** 是 Mathlib 中的一个定义，位于命名空间 `Relator`。
形式化陈述：LiftFun (f : α -> γ) (g : β -> δ) : Prop
参数：f : α -> γ；g : β -> δ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The binary relations `R : α → β → Prop` and `S : γ → δ → Prop` induce a binary
relation on functions `LiftFun : (α → γ) → (β → δ) → Prop`.
-/
def LiftFun (f : α → γ) (g : β → δ) : Prop :=
  ∀ ⦃a b⦄, R a b → S (f a) (g b)

/-- `(R ⇒ S) f g` means `LiftFun R S f g`. -/
scoped infixr:40 " ⇒ " => LiftFun

end

section

variable {α : Sort u₁} {β : Sort u₂} (R : α → β → Prop)

/-- A relation is "right total" if every element appears on the right. -/
/-
**Relator.RightTotal** 是 Mathlib 中的一个定义，位于命名空间 `Relator`。
形式化陈述：RightTotal : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A relation is "right total" if every element appears on the right.
-/
def RightTotal : Prop := ∀ b, ∃ a, R a b

/-- A relation is "left total" if every element appears on the left. -/
/-
**Relator.LeftTotal** 是 Mathlib 中的一个定义，位于命名空间 `Relator`。
形式化陈述：LeftTotal : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A relation is "left total" if every element appears on the left.
-/
def LeftTotal : Prop := ∀ a, ∃ b, R a b

/-- A relation is "bi-total" if it is both right total and left total. -/
/-
**Relator.BiTotal** 是 Mathlib 中的一个定义，位于命名空间 `Relator`。
形式化陈述：BiTotal : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A relation is "bi-total" if it is both right total and left total.
-/
def BiTotal : Prop := LeftTotal R ∧ RightTotal R

/-- A relation is "left unique" if every element on the right is paired with at
most one element on the left. -/
/-
**Relator.LeftUnique** 是 Mathlib 中的一个定义，位于命名空间 `Relator`。
形式化陈述：LeftUnique : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A relation is "left unique" if every element on the right is paired with at
most one element on the left.
-/
def LeftUnique : Prop := ∀ ⦃a b c⦄, R a c → R b c → a = b

/-- A relation is "right unique" if every element on the left is paired with at
most one element on the right. -/
/-
**Relator.RightUnique** 是 Mathlib 中的一个定义，位于命名空间 `Relator`。
形式化陈述：RightUnique : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A relation is "right unique" if every element on the left is paired with at
most one element on the right.
-/
def RightUnique : Prop := ∀ ⦃a b c⦄, R a b → R a c → b = c

/-- A relation is "bi-unique" if it is both left unique and right unique. -/
/-
**Relator.BiUnique** 是 Mathlib 中的一个定义，位于命名空间 `Relator`。
形式化陈述：BiUnique : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A relation is "bi-unique" if it is both left unique and right unique.
-/
def BiUnique : Prop := LeftUnique R ∧ RightUnique R

variable {R}
/-
**Relator.RightTotal.rel_forall** 是 Mathlib 中的一个定理，位于命名空间 `Relator.RightTotal`。
形式化陈述：∀ {α : Sort u₁} {β : Sort u₂} {R : α → β → Prop},   Relator.RightTotal R →
     Relator.LiftFun (Relator.LiftFun R fun x1 x2 => ∀ (a : x1), x2) (fun x1 x2 
=> ∀ (a : x1), x2)       (fun p => (i : α) → p i) fun q => ∀ (i : β), q i
参数：Relator.LiftFun R fun x1 x2 => ∀ (a : x1), x2；fun x1 x2 => ∀ (a : x1), x2；fun
 p => (i : α) → p i；i : β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
-/
lemma RightTotal.rel_forall (h : RightTotal R) :
    ((R ⇒ (· → ·)) ⇒ (· → ·)) (fun p => ∀ i, p i) (fun q => ∀ i, q i) :=
  fun _ _ Hrel H b => Exists.elim (h b) (fun _ Rab => Hrel Rab (H _))
/-
**Relator.LeftTotal.rel_exists** 是 Mathlib 中的一个定理，位于命名空间 `Relator.LeftTotal`。
形式化陈述：∀ {α : Sort u₁} {β : Sort u₂} {R : α → β → Prop},   Relator.LeftTotal R → 
    Relator.LiftFun (Relator.LiftFun R fun x1 x2 => x1 → x2) (fun x1 x2 => x1 → 
x2) (fun p => ∃ i, p i) fun q =>       ∃ i, q i
参数：Relator.LiftFun R fun x1 x2 => x1 → x2；fun x1 x2 => x1 → x2；fun p => ∃ i, p i
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
-/
lemma LeftTotal.rel_exists (h : LeftTotal R) :
    ((R ⇒ (· → ·)) ⇒ (· → ·)) (fun p => ∃ i, p i) (fun q => ∃ i, q i) :=
  fun _ _ Hrel ⟨a, pa⟩ => (h a).imp fun _ Rab => Hrel Rab pa
/-
**Relator.BiTotal.rel_forall** 是 Mathlib 中的一个定理，位于命名空间 `Relator.BiTotal`。
形式化陈述：∀ {α : Sort u₁} {β : Sort u₂} {R : α → β → Prop},   Relator.BiTotal R → Re
lator.LiftFun (Relator.LiftFun R Iff) Iff (fun p => ∀ (i : α), p i) fun q => ∀ (
i : β), q i
参数：Relator.LiftFun R Iff；fun p => ∀ (i : α), p i；i : β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
lemma BiTotal.rel_forall (h : BiTotal R) :
    ((R ⇒ Iff) ⇒ Iff) (fun p => ∀ i, p i) (fun q => ∀ i, q i) :=
  fun _ _ Hrel =>
    ⟨fun H b => Exists.elim (h.right b) (fun _ Rab => (Hrel Rab).mp (H _)),
      fun H a => Exists.elim (h.left a) (fun _ Rab => (Hrel Rab).mpr (H _))⟩
/-
**Relator.BiTotal.rel_exists** 是 Mathlib 中的一个定理，位于命名空间 `Relator.BiTotal`。
形式化陈述：∀ {α : Sort u₁} {β : Sort u₂} {R : α → β → Prop},   Relator.BiTotal R → Re
lator.LiftFun (Relator.LiftFun R Iff) Iff (fun p => ∃ i, p i) fun q => ∃ i, q i
参数：Relator.LiftFun R Iff；fun p => ∃ i, p i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma BiTotal.rel_exists (h : BiTotal R) :
    ((R ⇒ Iff) ⇒ Iff) (fun p => ∃ i, p i) (fun q => ∃ i, q i) :=
  fun _ _ Hrel =>
    ⟨fun ⟨a, pa⟩ => (h.left a).imp fun _ Rab => (Hrel Rab).1 pa,
      fun ⟨b, qb⟩ => (h.right b).imp fun _ Rab => (Hrel Rab).2 qb⟩
/-
**Relator.left_unique_of_rel_eq** 是 Mathlib 中的一个引理，位于命名空间 `Relator`。
形式化陈述：left_unique_of_rel_eq {eq' : β -> β -> Prop} (he : (R ⇒ (R ⇒ Iff)) Eq eq')
 : LeftUnique R
参数：he : (R ⇒ (R ⇒ Iff)) Eq eq'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
lemma left_unique_of_rel_eq {eq' : β → β → Prop} (he : (R ⇒ (R ⇒ Iff)) Eq eq') : LeftUnique R :=
  fun a b c (ac : R a c) (bc : R b c) => (he ac bc).mpr ((he bc bc).mp rfl)

end

/-
**Relator.rel_imp** 是 Mathlib 中的一个引理，位于命名空间 `Relator`。
形式化陈述：rel_imp : (Iff ⇒ (Iff ⇒ Iff)) (· -> ·) (· -> ·)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `imp_congr`：∀ {a b c d : Prop}, (a ↔ c) → (b ↔ d) → (a → b ↔ c → d)
-/
lemma rel_imp : (Iff ⇒ (Iff ⇒ Iff)) (· → ·) (· → ·) :=
  fun _ _ h _ _ l => imp_congr h l
/-
**Relator.rel_not** 是 Mathlib 中的一个引理，位于命名空间 `Relator`。
形式化陈述：rel_not : (Iff ⇒ Iff) Not Not
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
-/
lemma rel_not : (Iff ⇒ Iff) Not Not :=
  fun _ _ h => not_congr h
/-
**Relator.bi_total_eq** 是 Mathlib 中的一个引理，位于命名空间 `Relator`。
形式化陈述：bi_total_eq {α : Type u₁} : Relator.BiTotal (@Eq α)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma bi_total_eq {α : Type u₁} : Relator.BiTotal (@Eq α) :=
  { left := fun a => ⟨a, rfl⟩, right := fun a => ⟨a, rfl⟩ }

variable {α : Type*} {β : Type*} {γ : Type*}
variable {r : α → β → Prop}
/-
**Relator.LeftUnique.flip** 是 Mathlib 中的一个定理，位于命名空间 `Relator.LeftUnique`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {r : α → β → Prop}, Relator.LeftUnique r →
 Relator.RightUnique (flip r)
参数：flip r。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma LeftUnique.flip (h : LeftUnique r) : RightUnique (flip r) :=
  fun _ _ _ h₁ h₂ => h h₁ h₂
/-
**Relator.rel_and** 是 Mathlib 中的一个引理，位于命名空间 `Relator`。
形式化陈述：rel_and : ((· ↔ ·) ⇒ (· ↔ ·) ⇒ (· ↔ ·)) (· ∧ ·) (· ∧ ·)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
-/
lemma rel_and : ((· ↔ ·) ⇒ (· ↔ ·) ⇒ (· ↔ ·)) (· ∧ ·) (· ∧ ·) :=
  fun _ _ h₁ _ _ h₂ => and_congr h₁ h₂
/-
**Relator.rel_or** 是 Mathlib 中的一个引理，位于命名空间 `Relator`。
形式化陈述：rel_or : ((· ↔ ·) ⇒ (· ↔ ·) ⇒ (· ↔ ·)) (· ∨ ·) (· ∨ ·)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `or_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∨ b ↔ c ∨ d)
-/
lemma rel_or : ((· ↔ ·) ⇒ (· ↔ ·) ⇒ (· ↔ ·)) (· ∨ ·) (· ∨ ·) :=
  fun _ _ h₁ _ _ h₂ => or_congr h₁ h₂
/-
**Relator.rel_iff** 是 Mathlib 中的一个引理，位于命名空间 `Relator`。
形式化陈述：rel_iff : ((· ↔ ·) ⇒ (· ↔ ·) ⇒ (· ↔ ·)) (· ↔ ·) (· ↔ ·)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iff_congr`：∀ {p₁ p₂ q₁ q₂ : Prop}, (p₁ ↔ p₂) → (q₁ ↔ q₂) → ((p₁ ↔ q₁) ↔ 
(p₂ ↔ q₂))
-/
lemma rel_iff : ((· ↔ ·) ⇒ (· ↔ ·) ⇒ (· ↔ ·)) (· ↔ ·) (· ↔ ·) :=
  fun _ _ h₁ _ _ h₂ => iff_congr h₁ h₂
/-
**Relator.rel_eq** 是 Mathlib 中的一个引理，位于命名空间 `Relator`。
形式化陈述：rel_eq {r : α -> β -> Prop} (hr : BiUnique r) : (r ⇒ r ⇒ (· ↔ ·)) (· = ·) 
(· = ·)
参数：hr : BiUnique r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma rel_eq {r : α → β → Prop} (hr : BiUnique r) : (r ⇒ r ⇒ (· ↔ ·)) (· = ·) (· = ·) :=
  fun _ _ h₁ _ _ h₂ => ⟨fun h => hr.right h₁ <| h.symm ▸ h₂, fun h => hr.left h₁ <| h.symm ▸ h₂⟩

open Function

variable {r₁₁ : α → α → Prop} {r₁₂ : α → β → Prop} {r₂₁ : β → α → Prop}
  {r₂₃ : β → γ → Prop} {r₁₃ : α → γ → Prop}

namespace LeftTotal

/-
**Relator.LeftTotal.refl** 是 Mathlib 中的一个定理，位于命名空间 `Relator.LeftTotal`。
形式化陈述：∀ {α : Type u_1} {r₁₁ : α → α → Prop}, (∀ (a : α), r₁₁ a a) → Relator.Left
Total r₁₁
参数：∀ (a : α), r₁₁ a a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma refl (hr : ∀ a : α, r₁₁ a a) :
    LeftTotal r₁₁ :=
  fun a ↦ ⟨a, hr _⟩
/-
**Relator.LeftTotal.symm** 是 Mathlib 中的一个定理，位于命名空间 `Relator.LeftTotal`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {r₁₂ : α → β → Prop} {r₂₁ : β → α → Prop},
   (∀ (a : α) (b : β), r₁₂ a b → r₂₁ b a) → Relator.LeftTotal r₁₂ → Relator.Righ
tTotal r₂₁
参数：∀ (a : α) (b : β), r₁₂ a b → r₂₁ b a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
-/
protected lemma symm (hr : ∀ (a : α) (b : β), r₁₂ a b → r₂₁ b a) :
    LeftTotal r₁₂ → RightTotal r₂₁ :=
  fun h a ↦ (h a).imp (fun _ ↦ hr _ _)
/-
**Relator.LeftTotal.trans** 是 Mathlib 中的一个定理，位于命名空间 `Relator.LeftTotal`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {r₁₂ : α → β → Prop} {r₂₃ :
 β → γ → Prop} {r₁₃ : α → γ → Prop},   (∀ (a : α) (b : β) (c : γ), r₁₂ a b → r₂₃
 b c → r₁₃ a c) →     Relator.LeftTotal r₁₂ → Relator.LeftTotal r₂₃ → Relator.Le
ftTotal r₁₃
参数：∀ (a : α) (b : β) (c : γ), r₁₂ a b → r₂₃ b c → r₁₃ a c。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma trans (hr : ∀ (a : α) (b : β) (c : γ), r₁₂ a b → r₂₃ b c → r₁₃ a c) :
    LeftTotal r₁₂ → LeftTotal r₂₃ → LeftTotal r₁₃ :=
  fun h₁ h₂ a ↦ let ⟨b, hab⟩ := h₁ a; let ⟨c, hbc⟩ := h₂ b; ⟨c, hr _ _ _ hab hbc⟩

end LeftTotal

namespace RightTotal

/-
**Relator.RightTotal.refl** 是 Mathlib 中的一个定理，位于命名空间 `Relator.RightTotal`。
形式化陈述：∀ {α : Type u_1} {r₁₁ : α → α → Prop}, (∀ (a : α), r₁₁ a a) → Relator.Righ
tTotal r₁₁
参数：∀ (a : α), r₁₁ a a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relator.LeftTotal.refl`：∀ {α : Type u_1} {r₁₁ : α → α → Prop}, (∀ (a : α
), r₁₁ a a) → Relator.LeftTotal r₁₁
-/
protected lemma refl (hr : ∀ a : α, r₁₁ a a) : RightTotal r₁₁ :=
  LeftTotal.refl hr
/-
**Relator.RightTotal.symm** 是 Mathlib 中的一个定理，位于命名空间 `Relator.RightTotal`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {r₁₂ : α → β → Prop} {r₂₁ : β → α → Prop},
   (∀ (a : α) (b : β), r₁₂ a b → r₂₁ b a) → Relator.RightTotal r₁₂ → Relator.Lef
tTotal r₂₁
参数：∀ (a : α) (b : β), r₁₂ a b → r₂₁ b a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relator.LeftTotal.symm`：∀ {α : Type u_1} {β : Type u_2} {r₁₂ : α → β → P
rop} {r₂₁ : β → α → Prop},   (∀ (a : α) (b : β), r₁₂ a b → r₂₁ b a) → Relator.Le
ftTotal r₁₂ …
-/
protected lemma symm (hr : ∀ (a : α) (b : β), r₁₂ a b → r₂₁ b a) :
    RightTotal r₁₂ → LeftTotal r₂₁ :=
  LeftTotal.symm (fun _ _ ↦ hr _ _)
/-
**Relator.RightTotal.trans** 是 Mathlib 中的一个定理，位于命名空间 `Relator.RightTotal`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {r₁₂ : α → β → Prop} {r₂₃ :
 β → γ → Prop} {r₁₃ : α → γ → Prop},   (∀ (a : α) (b : β) (c : γ), r₁₂ a b → r₂₃
 b c → r₁₃ a c) →     Relator.RightTotal r₁₂ → Relator.RightTotal r₂₃ → Relator.
RightTotal r₁₃
参数：∀ (a : α) (b : β) (c : γ), r₁₂ a b → r₂₃ b c → r₁₃ a c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relator.LeftTotal.trans`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} 
{r₁₂ : α → β → Prop} {r₂₃ : β → γ → Prop} {r₁₃ : α → γ → Prop},   (∀ (a : α) (b 
: β) (c : γ),…
-/
protected lemma trans (hr : ∀ (a : α) (b : β) (c : γ), r₁₂ a b → r₂₃ b c → r₁₃ a c) :
    RightTotal r₁₂ → RightTotal r₂₃ → RightTotal r₁₃ :=
  swap <| LeftTotal.trans (fun _ _ _ ↦ swap <| hr _ _ _)

end RightTotal

namespace BiTotal

/-
**Relator.BiTotal.refl** 是 Mathlib 中的一个定理，位于命名空间 `Relator.BiTotal`。
形式化陈述：∀ {α : Type u_1} {r₁₁ : α → α → Prop}, (∀ (a : α), r₁₁ a a) → Relator.BiTo
tal r₁₁
参数：∀ (a : α), r₁₁ a a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relator.LeftTotal.refl`：∀ {α : Type u_1} {r₁₁ : α → α → Prop}, (∀ (a : α
), r₁₁ a a) → Relator.LeftTotal r₁₁
· 使用定理 `Relator.RightTotal.refl`：∀ {α : Type u_1} {r₁₁ : α → α → Prop}, (∀ (a : 
α), r₁₁ a a) → Relator.RightTotal r₁₁
-/
protected lemma refl (hr : ∀ a : α, r₁₁ a a) :
    BiTotal r₁₁ :=
  ⟨LeftTotal.refl hr, RightTotal.refl hr⟩
/-
**Relator.BiTotal.symm** 是 Mathlib 中的一个定理，位于命名空间 `Relator.BiTotal`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {r₁₂ : α → β → Prop} {r₂₁ : β → α → Prop},
   (∀ (a : α) (b : β), r₁₂ a b → r₂₁ b a) → Relator.BiTotal r₁₂ → Relator.BiTota
l r₂₁
参数：∀ (a : α) (b : β), r₁₂ a b → r₂₁ b a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relator.RightTotal.symm`：∀ {α : Type u_1} {β : Type u_2} {r₁₂ : α → β → 
Prop} {r₂₁ : β → α → Prop},   (∀ (a : α) (b : β), r₁₂ a b → r₂₁ b a) → Relator.R
ightTotal r₁₂…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Relator.LeftTotal.symm`：∀ {α : Type u_1} {β : Type u_2} {r₁₂ : α → β → P
rop} {r₂₁ : β → α → Prop},   (∀ (a : α) (b : β), r₁₂ a b → r₂₁ b a) → Relator.Le
ftTotal r₁₂ …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
protected lemma symm (hr : ∀ (a : α) (b : β), r₁₂ a b → r₂₁ b a) :
    BiTotal r₁₂ → BiTotal r₂₁ :=
  fun h ↦ ⟨h.2.symm hr, h.1.symm hr⟩
/-
**Relator.BiTotal.trans** 是 Mathlib 中的一个定理，位于命名空间 `Relator.BiTotal`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {r₁₂ : α → β → Prop} {r₂₃ :
 β → γ → Prop} {r₁₃ : α → γ → Prop},   (∀ (a : α) (b : β) (c : γ), r₁₂ a b → r₂₃
 b c → r₁₃ a c) →     Relator.BiTotal r₁₂ → Relator.BiTotal r₂₃ → Relator.BiTota
l r₁₃
参数：∀ (a : α) (b : β) (c : γ), r₁₂ a b → r₂₃ b c → r₁₃ a c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relator.LeftTotal.trans`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} 
{r₁₂ : α → β → Prop} {r₂₃ : β → γ → Prop} {r₁₃ : α → γ → Prop},   (∀ (a : α) (b 
: β) (c : γ),…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Relator.RightTotal.trans`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3}
 {r₁₂ : α → β → Prop} {r₂₃ : β → γ → Prop} {r₁₃ : α → γ → Prop},   (∀ (a : α) (b
 : β) (c : γ),…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
protected lemma trans (hr : ∀ (a : α) (b : β) (c : γ), r₁₂ a b → r₂₃ b c → r₁₃ a c) :
    BiTotal r₁₂ → BiTotal r₂₃ → BiTotal r₁₃ :=
  fun h₁ h₂ ↦ ⟨h₁.1.trans hr h₂.1, h₁.2.trans hr h₂.2⟩

end BiTotal

end Relator

