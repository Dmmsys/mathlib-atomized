/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Lean.PrettyPrinter.Delaborator.Builtins
public import Mathlib.Logic.Function.Defs
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.Inhabit
public import Batteries.Tactic.Trans

import Mathlib.Tactic.Attr.Register

/-!
# Extra facts about `Prod`

This file proves various simple lemmas about `Prod`.
It also defines better delaborators for product projections.
-/

@[expose] public section

variable {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}

namespace Prod

/-
**Prod.swap_eq_iff_eq_swap** 是 Mathlib 中的一个引理，位于命名空间 `Prod`。
形式化陈述：swap_eq_iff_eq_swap {x : α × β} {y : β × α} : x.swap = y ↔ x = y.swap
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma swap_eq_iff_eq_swap {x : α × β} {y : β × α} : x.swap = y ↔ x = y.swap := by grind
/-
**Prod.mk.injArrow** 是 Mathlib 中的一个定义，位于命名空间 `Prod.mk`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} →     {x₁ : α} → {y₁ : β} → {x₂ : α} → {
y₂ : β} → (x₁, y₁) = (x₂, y₂) → ⦃P : Sort u_5⦄ → (x₁ = x₂ → y₁ = y₂ → P) → P
参数：x₁, y₁；x₂, y₂。
该定义给出了一个带前提的构造。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mk.injArrow {x₁ : α} {y₁ : β} {x₂ : α} {y₂ : β} :
    (x₁, y₁) = (x₂, y₂) → ∀ ⦃P : Sort*⦄, (x₁ = x₂ → y₁ = y₂ → P) → P := by
  intros h P w
  cases h
  exact w rfl rfl

@[simp]
/-
**Prod.mk.eta** 是 Mathlib 中的一个定理，位于命名空间 `Prod.mk`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {p : α × β}, (p.1, p.2) = p
参数：p.1, p.2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk.eta : ∀ {p : α × β}, (p.1, p.2) = p
  | (_, _) => rfl
/-
**Prod.forall'** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：forall' {p : α -> β -> Prop} : (forall x : α × β, p x.1 x.2) ↔ forall a b,
 p a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.forall`：∀ {α : Type u_1} {β : Type u_2} {p : α × β → Prop}, (∀ (x :
 α × β), p x) ↔ ∀ (a : α) (b : β), p (a, b)
-/
theorem forall' {p : α → β → Prop} : (∀ x : α × β, p x.1 x.2) ↔ ∀ a b, p a b :=
  Prod.forall
/-
**Prod.exists'** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：exists' {p : α -> β -> Prop} : (exists x : α × β, p x.1 x.2) ↔ exists a b,
 p a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.exists`：∀ {α : Type u_1} {β : Type u_2} {p : α × β → Prop}, (∃ x, p
 x) ↔ ∃ a b, p (a, b)
-/
theorem exists' {p : α → β → Prop} : (∃ x : α × β, p x.1 x.2) ↔ ∃ a b, p a b :=
  Prod.exists

@[simp]
/-
**Prod.snd_comp_mk** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：snd_comp_mk (x : α) : Prod.snd ∘ (Prod.mk x : β -> α × β) = id
参数：x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_comp_mk (x : α) : Prod.snd ∘ (Prod.mk x : β → α × β) = id :=
  rfl

@[simp]
/-
**Prod.fst_comp_mk** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：fst_comp_mk (x : α) : Prod.fst ∘ (Prod.mk x : β -> α × β) = Function.const
 β x
参数：x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_comp_mk (x : α) : Prod.fst ∘ (Prod.mk x : β → α × β) = Function.const β x :=
  rfl

attribute [mfld_simps] map_apply

-- This was previously a `simp` lemma, but no longer is on the basis that it destructures the pair.
--  See `map_apply`, `map_fst`, and `map_snd` for slightly weaker lemmas in the `simp` set.
/-
**Prod.map_apply'** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：map_apply' (f : α -> γ) (g : β -> δ) (p : α × β) : map f g p = (f p.1, g p
.2)
参数：f : α -> γ；g : β -> δ；p : α × β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_apply' (f : α → γ) (g : β → δ) (p : α × β) : map f g p = (f p.1, g p.2) :=
  rfl
/-
**Prod.map_fst'** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：map_fst' (f : α -> γ) (g : β -> δ) : Prod.fst ∘ map f g = f ∘ Prod.fst
参数：f : α -> γ；g : β -> δ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Prod.map_fst`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u
_4} (f : α → β) (g : γ → δ) (x : α × γ),   (Prod.map f g x).1 = f x.1
-/
theorem map_fst' (f : α → γ) (g : β → δ) : Prod.fst ∘ map f g = f ∘ Prod.fst :=
  funext <| map_fst f g
/-
**Prod.map_snd'** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：map_snd' (f : α -> γ) (g : β -> δ) : Prod.snd ∘ map f g = g ∘ Prod.snd
参数：f : α -> γ；g : β -> δ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Prod.map_snd`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u
_4} (f : α → β) (g : γ → δ) (x : α × γ),   (Prod.map f g x).2 = g x.2
-/
theorem map_snd' (f : α → γ) (g : β → δ) : Prod.snd ∘ map f g = g ∘ Prod.snd :=
  funext <| map_snd f g
/-
**Prod.mk_inj** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：mk_inj {a₁ a₂ : α} {b₁ b₂ : β} : (a₁, b₁) = (a₂, b₂) ↔ a₁ = a₂ ∧ b₁ = b₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mk_inj {a₁ a₂ : α} {b₁ b₂ : β} : (a₁, b₁) = (a₂, b₂) ↔ a₁ = a₂ ∧ b₁ = b₂ := by simp
/-
**Prod.mk_right_injective** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：mk_right_injective {α β : Type*} (a : α) : (mk a : β -> α × β).Injective
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
theorem mk_right_injective {α β : Type*} (a : α) : (mk a : β → α × β).Injective := by
  intro b₁ b₂ h
  simpa only [true_and, Prod.mk_inj, eq_self_iff_true] using h
/-
**Prod.mk_left_injective** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：mk_left_injective {α β : Type*} (b : β) : (fun a => mk a b : α -> α × β).I
njective
参数：b : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
theorem mk_left_injective {α β : Type*} (b : β) : (fun a ↦ mk a b : α → α × β).Injective := by
  intro b₁ b₂ h
  simpa only [and_true, eq_self_iff_true, mk_inj] using h
/-
**Prod.mk_right_inj** 是 Mathlib 中的一个引理，位于命名空间 `Prod`。
形式化陈述：mk_right_inj {a : α} {b₁ b₂ : β} : (a, b₁) = (a, b₂) ↔ b₁ = b₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Prod.mk_right_injective`：mk_right_injective {α β : Type*} (a : α) : (mk 
a : β -> α × β).Injective
-/
lemma mk_right_inj {a : α} {b₁ b₂ : β} : (a, b₁) = (a, b₂) ↔ b₁ = b₂ :=
    (mk_right_injective _).eq_iff
/-
**Prod.mk_left_inj** 是 Mathlib 中的一个引理，位于命名空间 `Prod`。
形式化陈述：mk_left_inj {a₁ a₂ : α} {b : β} : (a₁, b) = (a₂, b) ↔ a₁ = a₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Prod.mk_left_injective`：mk_left_injective {α β : Type*} (b : β) : (fun a
 => mk a b : α -> α × β).Injective
-/
lemma mk_left_inj {a₁ a₂ : α} {b : β} : (a₁, b) = (a₂, b) ↔ a₁ = a₂ := (mk_left_injective _).eq_iff
/-
**Prod.map_def** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：map_def {f : α -> γ} {g : β -> δ} : Prod.map f g = fun p : α × β => (f p.1
, g p.2)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `Prod.map_fst`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u
_4} (f : α → β) (g : γ → δ) (x : α × γ),   (Prod.map f g x).1 = f x.1
· 使用定理 `Prod.map_snd`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u
_4} (f : α → β) (g : γ → δ) (x : α × γ),   (Prod.map f g x).2 = g x.2
-/
theorem map_def {f : α → γ} {g : β → δ} : Prod.map f g = fun p : α × β ↦ (f p.1, g p.2) :=
  funext fun p ↦ Prod.ext (map_fst f g p) (map_snd f g p)
/-
**Prod.id_prod** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：id_prod : (fun p : α × β => (p.1, p.2)) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_prod : (fun p : α × β ↦ (p.1, p.2)) = id :=
  rfl

@[simp]
/-
**Prod.map_iterate** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：map_iterate (f : α -> α) (g : β -> β) (n : Nat) : (Prod.map f g)^[n] = Pro
d.map f^[n] g^[n]
参数：f : α -> α；g : β -> β；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem map_iterate (f : α → α) (g : β → β) (n : ℕ) :
    (Prod.map f g)^[n] = Prod.map f^[n] g^[n] := by induction n <;> simp [*, Prod.map_comp_map]
/-
**Prod.fst_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：fst_surjective [h : Nonempty β] : Function.Surjective (@fst α β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.elim`：∀ {α : Sort u} {p : Prop}, Nonempty α → (∀ (a : α), p) → 
p
-/
theorem fst_surjective [h : Nonempty β] : Function.Surjective (@fst α β) :=
  fun x ↦ h.elim fun y ↦ ⟨⟨x, y⟩, rfl⟩
/-
**Prod.snd_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：snd_surjective [h : Nonempty α] : Function.Surjective (@snd α β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.elim`：∀ {α : Sort u} {p : Prop}, Nonempty α → (∀ (a : α), p) → 
p
-/
theorem snd_surjective [h : Nonempty α] : Function.Surjective (@snd α β) :=
  fun y ↦ h.elim fun x ↦ ⟨⟨x, y⟩, rfl⟩
/-
**Prod.fst_injective** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：fst_injective [Subsingleton β] : Function.Injective (@fst α β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem fst_injective [Subsingleton β] : Function.Injective (@fst α β) :=
  fun _ _ h ↦ Prod.ext h (Subsingleton.elim _ _)
/-
**Prod.snd_injective** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：snd_injective [Subsingleton α] : Function.Injective (@snd α β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem snd_injective [Subsingleton α] : Function.Injective (@snd α β) :=
  fun _ _ h ↦ Prod.ext (Subsingleton.elim _ _) h

@[simp]
/-
**Prod.swap_leftInverse** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：swap_leftInverse : Function.LeftInverse (@swap α β) swap
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.swap_swap`：∀ {α : Type u_1} {β : Type u_2} (x : α × β), x.swap.swap
 = x
-/
theorem swap_leftInverse : Function.LeftInverse (@swap α β) swap :=
  swap_swap

@[simp]
/-
**Prod.swap_rightInverse** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：swap_rightInverse : Function.RightInverse (@swap α β) swap
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.swap_swap`：∀ {α : Type u_1} {β : Type u_2} (x : α × β), x.swap.swap
 = x
-/
theorem swap_rightInverse : Function.RightInverse (@swap α β) swap :=
  swap_swap
/-
**Prod.swap_injective** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：swap_injective : Function.Injective (@swap α β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {g : β →
 α} {f : α → β}, Function.LeftInverse g f → Function.Injective f
· 使用定理 `Prod.swap_leftInverse`：swap_leftInverse : Function.LeftInverse (@swap α 
β) swap
-/
theorem swap_injective : Function.Injective (@swap α β) :=
  swap_leftInverse.injective
/-
**Prod.swap_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：swap_surjective : Function.Surjective (@swap α β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β} {g : β → α}, Function.LeftInverse f g → Function.Surjective f
· 使用定理 `Prod.swap_leftInverse`：swap_leftInverse : Function.LeftInverse (@swap α 
β) swap
-/
theorem swap_surjective : Function.Surjective (@swap α β) :=
  swap_leftInverse.surjective
/-
**Prod.swap_bijective** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：swap_bijective : Function.Bijective (@swap α β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.swap_injective`：swap_injective : Function.Injective (@swap α β)
· 使用定理 `Prod.swap_surjective`：swap_surjective : Function.Surjective (@swap α β)
-/
theorem swap_bijective : Function.Bijective (@swap α β) :=
  ⟨swap_injective, swap_surjective⟩
/-
**Prod._root_.Function.Semiconj.swap_map** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Function.Semiconj.swap_map (f : α → α) (g : β → β) :
    Function.Semiconj swap (map f g) (map g f) :=
  Function.semiconj_iff_comp_eq.2 (map_comp_swap g f).symm
/-
**Prod.eq_iff_fst_eq_snd_eq** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {p q : α × β}, p = q ↔ p.1 = q.1 ∧ p.2 = q
.2
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem eq_iff_fst_eq_snd_eq : ∀ {p q : α × β}, p = q ↔ p.1 = q.1 ∧ p.2 = q.2
  | ⟨p₁, p₂⟩, ⟨q₁, q₂⟩ => by simp
/-
**Prod.fst_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {p : α × β} {x : α}, p.1 = x ↔ p = (x, p.2
)
参数：x, p.2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem fst_eq_iff : ∀ {p : α × β} {x : α}, p.1 = x ↔ p = (x, p.2)
  | ⟨a, b⟩, x => by simp
/-
**Prod.snd_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {p : α × β} {x : β}, p.2 = x ↔ p = (p.1, x
)
参数：p.1, x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem snd_eq_iff : ∀ {p : α × β} {x : β}, p.2 = x ↔ p = (p.1, x)
  | ⟨a, b⟩, x => by simp

variable {r : α → α → Prop} {s : β → β → Prop} {x y : α × β}
/-
**Prod.lex_iff** 是 Mathlib 中的一个引理，位于命名空间 `Prod`。
形式化陈述：lex_iff : Prod.Lex r s x y ↔ r x.1 y.1 ∨ x.1 = y.1 ∧ s x.2 y.2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.lex_def`：∀ {α : Type u} {β : Type v} {r : α → α → Prop} {s : β → β 
→ Prop} {p q : α × β},   Prod.Lex r s p q ↔ r p.1 q.1 ∨ p.1 = q.1 ∧ s p.2 q.2
-/
lemma lex_iff : Prod.Lex r s x y ↔ r x.1 y.1 ∨ x.1 = y.1 ∧ s x.2 y.2 := lex_def
/-
**Prod.Lex.decidable** 是 Mathlib 中的一个定义，位于命名空间 `Prod.Lex`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} →     [DecidableEq α] →       (r : α → α
 → Prop) → (s : β → β → Prop) → [DecidableRel r] → [DecidableRel s] → DecidableR
el (Prod.Lex r s)
参数：r : α → α → Prop；s : β → β → Prop；Prod.Lex r s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Lex.decidable [DecidableEq α]
    (r : α → α → Prop) (s : β → β → Prop) [DecidableRel r] [DecidableRel s] :
    DecidableRel (Prod.Lex r s) :=
  fun _ _ ↦ decidable_of_decidable_of_iff lex_def.symm

@[refl]
/-
**Prod.Lex.refl_left** 是 Mathlib 中的一个定理，位于命名空间 `Prod.Lex`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (r : α → α → Prop) (s : β → β → Prop) [Std
.Refl r] (x : α × β), Prod.Lex r s x x
参数：r : α → α → Prop；s : β → β → Prop；x : α × β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `refl`：refl [Std.Refl r] (a : α) : a ≺ a
-/
theorem Lex.refl_left (r : α → α → Prop) (s : β → β → Prop) [Std.Refl r] : ∀ x, Prod.Lex r s x x
  | (_, _) => Lex.left _ _ (refl _)
/-
**Prod.** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {r : α → α → Prop} {s : β → β → Prop} [Std.Refl r] : Std.Refl (Prod.Lex r s) :=
  ⟨Lex.refl_left _ _⟩

@[refl]
/-
**Prod.Lex.refl_right** 是 Mathlib 中的一个定理，位于命名空间 `Prod.Lex`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (r : α → α → Prop) (s : β → β → Prop) [Std
.Refl s] (x : α × β), Prod.Lex r s x x
参数：r : α → α → Prop；s : β → β → Prop；x : α × β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `refl`：refl [Std.Refl r] (a : α) : a ≺ a
-/
theorem Lex.refl_right (r : α → α → Prop) (s : β → β → Prop) [Std.Refl s] : ∀ x, Prod.Lex r s x x
  | (_, _) => Lex.right _ (refl _)
/-
**Prod.** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {r : α → α → Prop} {s : β → β → Prop} [Std.Refl s] : Std.Refl (Prod.Lex r s) :=
  ⟨Lex.refl_right _ _⟩
/-
**Prod.** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Std.Irrefl r] [Std.Irrefl s] : Std.Irrefl (Prod.Lex r s) :=
  ⟨by rintro ⟨i, a⟩ (⟨_, _, h⟩ | ⟨_, h⟩) <;> exact irrefl _ h⟩

set_option linter.style.whitespace false in -- manual alignment is not recognised
@[trans]
/-
**Prod.Lex.trans** 是 Mathlib 中的一个定理，位于命名空间 `Prod.Lex`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} [IsT
rans α r] [IsTrans β s] {x y z : α × β},   Prod.Lex r s x y → Prod.Lex r s y z →
 Prod.Lex r s x z
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
-/
theorem Lex.trans {r : α → α → Prop} {s : β → β → Prop} [IsTrans α r] [IsTrans β s] :
    ∀ {x y z : α × β}, Prod.Lex r s x y → Prod.Lex r s y z → Prod.Lex r s x z
  | (_, _), (_, _), (_, _), left  _ _ hxy₁, left  _ _ hyz₁ => left  _ _ (_root_.trans hxy₁ hyz₁)
  | (_, _), (_, _), (_, _), left  _ _ hxy₁, right _ _      => left  _ _ hxy₁
  | (_, _), (_, _), (_, _), right _ _,      left  _ _ hyz₁ => left  _ _ hyz₁
  | (_, _), (_, _), (_, _), right _ hxy₂,   right _ hyz₂   => right _ (_root_.trans hxy₂ hyz₂)
/-
**Prod.** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {r : α → α → Prop} {s : β → β → Prop} [IsTrans α r] [IsTrans β s] :
    IsTrans (α × β) (Prod.Lex r s) :=
  ⟨fun _ _ _ ↦ Lex.trans⟩
/-
**Prod.** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {r : α → α → Prop} {s : β → β → Prop} [IsStrictOrder α r] [Std.Antisymm s] :
    Std.Antisymm (Prod.Lex r s) :=
  ⟨fun x₁ x₂ h₁₂ h₂₁ ↦
    match x₁, x₂, h₁₂, h₂₁ with
    | (a, _), (_, _), .left  _ _ hr₁, .left  _ _ hr₂ => (irrefl a (_root_.trans hr₁ hr₂)).elim
    | (_, _), (_, _), .left  _ _ hr₁, .right _ _     => (irrefl _ hr₁).elim
    | (_, _), (_, _), .right _ _,     .left  _ _ hr₂ => (irrefl _ hr₂).elim
    | (_, _), (_, _), .right _ hs₁,   .right _ hs₂   => antisymm hs₁ hs₂ ▸ rfl⟩
/-
**Prod.total_left** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：total_left {r : α -> α -> Prop} {s : β -> β -> Prop} [Std.Total r] : Std.T
otal (Prod.Lex r s)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `Std.Total.total`：∀ {α : Sort u} {r : α → α → Prop} [self : Std.Total r] 
(a b : α), r a b ∨ r b a
-/
instance total_left {r : α → α → Prop} {s : β → β → Prop} [Std.Total r] :
    Std.Total (Prod.Lex r s) :=
  ⟨fun ⟨a₁, _⟩ ⟨a₂, _⟩ ↦ (Std.Total.total a₁ a₂).imp (Lex.left _ _) (Lex.left _ _)⟩
/-
**Prod.total_right** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：total_right {r : α -> α -> Prop} {s : β -> β -> Prop} [Std.Trichotomous r]
 [Std.Total s] : Std.Total (Prod.Lex r s)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `trichotomous_of`：trichotomous_of [Std.Trichotomous r] : forall a b : α, 
a ≺ b ∨ a = b ∨ b ≺ a
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用引理 `total_of`：total_of [Std.Total r] (a b : α) : a ≺ b ∨ b ≺ a
-/
instance total_right {r : α → α → Prop} {s : β → β → Prop} [Std.Trichotomous r] [Std.Total s] :
    Std.Total (Prod.Lex r s) :=
  ⟨fun ⟨i, a⟩ ⟨j, b⟩ ↦ by
    obtain hij | rfl | hji := trichotomous_of r i j
    · exact Or.inl (.left _ _ hij)
    · exact (total_of s a b).imp (.right _) (.right _)
    · exact Or.inr (.left _ _ hji) ⟩
/-
**Prod.trichotomous** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：trichotomous [Std.Trichotomous r] [Std.Trichotomous s] : Std.Trichotomous 
(Prod.Lex r s)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Std.trichotomous_of_rel_or_eq_or_rel_swap`：∀ {α : Sort u_1} {r : α → α →
 Prop}, (∀ {a b : α}, r a b ∨ a = b ∨ r b a) → Std.Trichotomous r
· 使用引理 `trichotomous_of`：trichotomous_of [Std.Trichotomous r] : forall a b : α, 
a ≺ b ∨ a = b ∨ b ≺ a
· 使用定理 `Or.imp3`：Or.imp3 {d e c f : Prop} (had : a -> d) (hbe : b -> e) (hcf : c
 -> f) : a ∨ b ∨ c -> d ∨ e ∨ f
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
instance trichotomous [Std.Trichotomous r] [Std.Trichotomous s] :
    Std.Trichotomous (Prod.Lex r s) :=
  Std.trichotomous_of_rel_or_eq_or_rel_swap <| by
    intro ⟨i, a⟩ ⟨j, b⟩
    obtain hij | rfl | hji := trichotomous_of r i j
    { exact Or.inl (Lex.left _ _ hij) }
    { exact (trichotomous_of (s) a b).imp3 (Lex.right _) (congr_arg _) (Lex.right _) }
    { exact Or.inr (Or.inr <| Lex.left _ _ hji) }
/-
**Prod.** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Std.Asymm r] [Std.Asymm s] :
    Std.Asymm (Prod.Lex r s) where
  asymm
  | (_a₁, _a₂), (_b₁, _b₂), .left _ _ h₁, .left _ _ h₂ => Std.Asymm.asymm _ _ h₂ h₁
  | (_a₁, _a₂), (_, _b₂), .left _ _ h₁, .right _ _ => Std.Asymm.asymm _ _ h₁ h₁
  | (_a₁, _a₂), (_, _b₂), .right _ _, .left _ _ h₂ => Std.Asymm.asymm _ _ h₂ h₂
  | (_a₁, _a₂), (_, _b₂), .right _ h₁, .right _ h₂ => Std.Asymm.asymm _ _ h₁ h₂

end Prod

open Prod

namespace Function

variable {f : α → γ} {g : β → δ} {f₁ : α → β} {g₁ : γ → δ} {f₂ : β → α} {g₂ : δ → γ}

/-
**Function.Injective.prodMap** 是 Mathlib 中的一个定理，位于命名空间 `Function.Injective`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} {f : α → γ} 
{g : β → δ},   Function.Injective f → Function.Injective g → Function.Injective 
(Prod.map f g)
参数：Prod.map f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem Injective.prodMap (hf : Injective f) (hg : Injective g) : Injective (map f g) :=
  fun _ _ h ↦ Prod.ext (hf <| congr_arg Prod.fst h) (hg <| congr_arg Prod.snd h)
/-
**Function.Surjective.prodMap** 是 Mathlib 中的一个定理，位于命名空间 `Function.Surjective`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} {f : α → γ} 
{g : β → δ},   Function.Surjective f → Function.Surjective g → Function.Surjecti
ve (Prod.map f g)
参数：Prod.map f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
-/
theorem Surjective.prodMap (hf : Surjective f) (hg : Surjective g) : Surjective (map f g) :=
  fun p ↦
  let ⟨x, hx⟩ := hf p.1
  let ⟨y, hy⟩ := hg p.2
  ⟨(x, y), Prod.ext hx hy⟩
/-
**Function.Bijective.prodMap** 是 Mathlib 中的一个定理，位于命名空间 `Function.Bijective`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} {f : α → γ} 
{g : β → δ},   Function.Bijective f → Function.Bijective g → Function.Bijective 
(Prod.map f g)
参数：Prod.map f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_
3} {δ : Type u_4} {f : α → γ} {g : β → δ},   Function.Injective f → Function.Inj
ective g → Funct…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Function.Surjective.prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u
_3} {δ : Type u_4} {f : α → γ} {g : β → δ},   Function.Surjective f → Function.S
urjective g → Fun…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Bijective.prodMap (hf : Bijective f) (hg : Bijective g) : Bijective (map f g) :=
  ⟨hf.1.prodMap hg.1, hf.2.prodMap hg.2⟩
/-
**Function.LeftInverse.prodMap** 是 Mathlib 中的一个定理，位于命名空间 `Function.LeftInverse`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} {f₁ : α → β}
 {g₁ : γ → δ} {f₂ : β → α} {g₂ : δ → γ},   Function.LeftInverse f₁ f₂ → Function
.LeftInverse g₁ g₂ → Function.LeftInverse (Prod.map f₁ g₁) (Prod.map f₂ g₂)
参数：Prod.map f₁ g₁；Prod.map f₂ g₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Prod.map_map`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u
_4} {ε : Type u_5} {ζ : Type u_6} (f : α → β) (f' : γ → δ)   (g : β → ε) (g' : δ
 →…
· 使用定理 `Function.LeftInverse.comp_eq_id`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β} {g : β → α}, Function.LeftInverse f g → f ∘ g = id
· 使用定理 `Prod.map_id`：∀ {α : Type u_1} {β : Type u_2}, Prod.map id id = id
· 使用定理 `id.eq_1`：∀ {α : Sort u} (a : α), id a = a
-/
theorem LeftInverse.prodMap (hf : LeftInverse f₁ f₂) (hg : LeftInverse g₁ g₂) :
    LeftInverse (map f₁ g₁) (map f₂ g₂) :=
  fun a ↦ by rw [Prod.map_map, hf.comp_eq_id, hg.comp_eq_id, map_id, id]
/-
**Function.RightInverse.prodMap** 是 Mathlib 中的一个定理，位于命名空间 `Function.RightInverse
`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} {f₁ : α → β}
 {g₁ : γ → δ} {f₂ : β → α} {g₂ : δ → γ},   Function.RightInverse f₁ f₂ → Functio
n.RightInverse g₁ g₂ → Function.RightInverse (Prod.map f₁ g₁) (Prod.map f₂ g₂)
参数：Prod.map f₁ g₁；Prod.map f₂ g₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type 
u_3} {δ : Type u_4} {f₁ : α → β} {g₁ : γ → δ} {f₂ : β → α} {g₂ : δ → γ},   Funct
ion.LeftInverse f₁…
-/
theorem RightInverse.prodMap :
    RightInverse f₁ f₂ → RightInverse g₁ g₂ → RightInverse (map f₁ g₁) (map f₂ g₂) :=
  LeftInverse.prodMap
/-
**Function.Involutive.prodMap** 是 Mathlib 中的一个定理，位于命名空间 `Function.Involutive`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → α} {g : β → β},   Function.Involu
tive f → Function.Involutive g → Function.Involutive (Prod.map f g)
参数：Prod.map f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type 
u_3} {δ : Type u_4} {f₁ : α → β} {g₁ : γ → δ} {f₂ : β → α} {g₂ : δ → γ},   Funct
ion.LeftInverse f₁…
-/
theorem Involutive.prodMap {f : α → α} {g : β → β} :
    Involutive f → Involutive g → Involutive (map f g) :=
  LeftInverse.prodMap

end Function

namespace Prod

open Function

@[simp]
/-
**Prod.map_injective** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：map_injective [Nonempty α] [Nonempty β] {f : α -> γ} {g : β -> δ} : Inject
ive (map f g) ↔ Injective f ∧ Injective g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Function.Injective.prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_
3} {δ : Type u_4} {f : α → γ} {g : β → δ},   Function.Injective f → Function.Inj
ective g → Funct…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem map_injective [Nonempty α] [Nonempty β] {f : α → γ} {g : β → δ} :
    Injective (map f g) ↔ Injective f ∧ Injective g :=
  ⟨fun h =>
    ⟨fun a₁ a₂ ha => by
      inhabit β
      injection
        @h (a₁, default) (a₂, default) (congr_arg (fun c : γ => Prod.mk c (g default)) ha :),
      fun b₁ b₂ hb => by
      inhabit α
      injection @h (default, b₁) (default, b₂) (congr_arg (Prod.mk (f default)) hb :)⟩,
    fun h => h.1.prodMap h.2⟩

@[simp]
/-
**Prod.map_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：map_surjective [Nonempty γ] [Nonempty δ] {f : α -> γ} {g : β -> δ} : Surje
ctive (map f g) ↔ Surjective f ∧ Surjective g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Function.Surjective.prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u
_3} {δ : Type u_4} {f : α → γ} {g : β → δ},   Function.Surjective f → Function.S
urjective g → Fun…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem map_surjective [Nonempty γ] [Nonempty δ] {f : α → γ} {g : β → δ} :
    Surjective (map f g) ↔ Surjective f ∧ Surjective g :=
  ⟨fun h =>
    ⟨fun c => by
      inhabit δ
      obtain ⟨⟨a, b⟩, h⟩ := h (c, default)
      exact ⟨a, congr_arg Prod.fst h⟩,
      fun d => by
      inhabit γ
      obtain ⟨⟨a, b⟩, h⟩ := h (default, d)
      exact ⟨b, congr_arg Prod.snd h⟩⟩,
    fun h => h.1.prodMap h.2⟩

@[simp]
/-
**Prod.map_bijective** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：map_bijective [Nonempty α] [Nonempty β] {f : α -> γ} {g : β -> δ} : Biject
ive (map f g) ↔ Bijective f ∧ Bijective g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.and`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `Prod.map_injective`：map_injective [Nonempty α] [Nonempty β] {f : α -> γ}
 {g : β -> δ} : Injective (map f g) ↔ Injective f ∧ Injective g
· 使用定理 `Prod.map_surjective`：map_surjective [Nonempty γ] [Nonempty δ] {f : α -> 
γ} {g : β -> δ} : Surjective (map f g) ↔ Surjective f ∧ Surjective g
· 使用定理 `and_and_and_comm`：∀ {a b c d : Prop}, (a ∧ b) ∧ c ∧ d ↔ (a ∧ c) ∧ b ∧ d
-/
theorem map_bijective [Nonempty α] [Nonempty β] {f : α → γ} {g : β → δ} :
    Bijective (map f g) ↔ Bijective f ∧ Bijective g := by
  have := Nonempty.map f ‹_›
  have := Nonempty.map g ‹_›
  exact (map_injective.and map_surjective).trans and_and_and_comm

@[simp]
/-
**Prod.map_leftInverse** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：map_leftInverse [Nonempty β] [Nonempty δ] {f₁ : α -> β} {g₁ : γ -> δ} {f₂ 
: β -> α} {g₂ : δ -> γ} : LeftInverse (map f₁ g₁) (map f₂ g₂) ↔ LeftInverse f₁ f
₂ ∧ LeftInverse g₁ g₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Function.LeftInverse.prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type 
u_3} {δ : Type u_4} {f₁ : α → β} {g₁ : γ → δ} {f₂ : β → α} {g₂ : δ → γ},   Funct
ion.LeftInverse f₁…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem map_leftInverse [Nonempty β] [Nonempty δ] {f₁ : α → β} {g₁ : γ → δ} {f₂ : β → α}
    {g₂ : δ → γ} : LeftInverse (map f₁ g₁) (map f₂ g₂) ↔ LeftInverse f₁ f₂ ∧ LeftInverse g₁ g₂ :=
  ⟨fun h =>
    ⟨fun b => by
      inhabit δ
      exact congr_arg Prod.fst (h (b, default)),
      fun d => by
      inhabit β
      exact congr_arg Prod.snd (h (default, d))⟩,
    fun h => h.1.prodMap h.2 ⟩

@[simp]
/-
**Prod.map_rightInverse** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：map_rightInverse [Nonempty α] [Nonempty γ] {f₁ : α -> β} {g₁ : γ -> δ} {f₂
 : β -> α} {g₂ : δ -> γ} : RightInverse (map f₁ g₁) (map f₂ g₂) ↔ RightInverse f
₁ f₂ ∧ RightInverse g₁ g₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.map_leftInverse`：map_leftInverse [Nonempty β] [Nonempty δ] {f₁ : α 
-> β} {g₁ : γ -> δ} {f₂ : β -> α} {g₂ : δ -> γ} : LeftInverse (map f₁ g₁) (map f
₂ g₂) ↔ Le…
-/
theorem map_rightInverse [Nonempty α] [Nonempty γ] {f₁ : α → β} {g₁ : γ → δ} {f₂ : β → α}
    {g₂ : δ → γ} : RightInverse (map f₁ g₁) (map f₂ g₂) ↔ RightInverse f₁ f₂ ∧ RightInverse g₁ g₂ :=
  map_leftInverse

@[simp]
/-
**Prod.map_involutive** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：map_involutive [Nonempty α] [Nonempty β] {f : α -> α} {g : β -> β} : Invol
utive (map f g) ↔ Involutive f ∧ Involutive g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.map_leftInverse`：map_leftInverse [Nonempty β] [Nonempty δ] {f₁ : α 
-> β} {g₁ : γ -> δ} {f₂ : β -> α} {g₂ : δ -> γ} : LeftInverse (map f₁ g₁) (map f
₂ g₂) ↔ Le…
-/
theorem map_involutive [Nonempty α] [Nonempty β] {f : α → α} {g : β → β} :
    Involutive (map f g) ↔ Involutive f ∧ Involutive g :=
  map_leftInverse

namespace PrettyPrinting
open Lean PrettyPrinter Delaborator

/--
When true, then `Prod.fst x` and `Prod.snd x` pretty print as `x.1` and `x.2`
rather than as `x.fst` and `x.snd`.
-/
meta register_option pp.numericProj.prod : Bool := {
  defValue := true
  descr := "enable pretty printing `Prod.fst x` as `x.1` and `Prod.snd x` as `x.2`."
}

/-- Tell whether pretty-printing should use numeric projection notations `.1`
and `.2` for `Prod.fst` and `Prod.snd`. -/
meta def getPPNumericProjProd (o : Options) : Bool :=
  o.get pp.numericProj.prod.name pp.numericProj.prod.defValue

/-- Delaborator for `Prod.fst x` as `x.1`. -/
@[app_delab Prod.fst]
meta def delabProdFst : Delab :=
  whenPPOption getPPNumericProjProd <|
  whenPPOption getPPFieldNotation <|
  whenNotPPOption getPPExplicit <|
  withOverApp 3 do
    let x ← SubExpr.withAppArg delab
    `($(x).1)

/-- Delaborator for `Prod.snd x` as `x.2`. -/
@[app_delab Prod.snd]
meta def delabProdSnd : Delab :=
  whenPPOption getPPNumericProjProd <|
  whenPPOption getPPFieldNotation <|
  whenNotPPOption getPPExplicit <|
  withOverApp 3 do
    let x ← SubExpr.withAppArg delab
    `($(x).2)

end PrettyPrinting

end Prod

