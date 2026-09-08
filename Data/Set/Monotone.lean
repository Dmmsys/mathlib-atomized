/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Andrew Zipperer, Haitao Zhang, Minchao Wu, Yury Kudryashov
-/
module

public import Mathlib.Data.Set.Function

/-!
# Monotone functions over sets
-/

public section

variable {α β γ : Type*}

open Equiv Equiv.Perm Function

namespace Set


/-! ### Congruence lemmas for monotonicity and antitonicity -/
section Order

variable {s : Set α} {f₁ f₂ : α → β} [Preorder α] [Preorder β]

/-
**Set._root_.MonotoneOn.congr** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MonotoneOn.congr (h₁ : MonotoneOn f₁ s) (h : s.EqOn f₁ f₂) : MonotoneOn f₂ s := by
  intro a ha b hb hab
  rw [← h ha, ← h hb]
  exact h₁ ha hb hab
/-
**Set._root_.AntitoneOn.congr** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.AntitoneOn.congr (h₁ : AntitoneOn f₁ s) (h : s.EqOn f₁ f₂) : AntitoneOn f₂ s :=
  h₁.dual_right.congr h
/-
**Set._root_.StrictMonoOn.congr** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.StrictMonoOn.congr (h₁ : StrictMonoOn f₁ s) (h : s.EqOn f₁ f₂) :
    StrictMonoOn f₂ s := by
  intro a ha b hb hab
  rw [← h ha, ← h hb]
  exact h₁ ha hb hab
/-
**Set._root_.StrictAntiOn.congr** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.StrictAntiOn.congr (h₁ : StrictAntiOn f₁ s) (h : s.EqOn f₁ f₂) : StrictAntiOn f₂ s :=
  h₁.dual_right.congr h
/-
**Set.EqOn.congr_monotoneOn** 是 Mathlib 中的一个定理，位于命名空间 `Set.EqOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ : α → β} [inst : Preord
er α] [inst_1 : Preorder β],   Set.EqOn f₁ f₂ s → (MonotoneOn f₁ s ↔ MonotoneOn 
f₂ s)
参数：MonotoneOn f₁ s ↔ MonotoneOn f₂ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonotoneOn.congr`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ : α
 → β} [inst : Preorder α] [inst_1 : Preorder β],   MonotoneOn f₁ s → Set.EqOn f₁
 f₂ s …
· 使用定理 `Set.EqOn.symm`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ : α → 
β}, Set.EqOn f₁ f₂ s → Set.EqOn f₂ f₁ s
-/
theorem EqOn.congr_monotoneOn (h : s.EqOn f₁ f₂) : MonotoneOn f₁ s ↔ MonotoneOn f₂ s :=
  ⟨fun h₁ => h₁.congr h, fun h₂ => h₂.congr h.symm⟩
/-
**Set.EqOn.congr_antitoneOn** 是 Mathlib 中的一个定理，位于命名空间 `Set.EqOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ : α → β} [inst : Preord
er α] [inst_1 : Preorder β],   Set.EqOn f₁ f₂ s → (AntitoneOn f₁ s ↔ AntitoneOn 
f₂ s)
参数：AntitoneOn f₁ s ↔ AntitoneOn f₂ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntitoneOn.congr`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ : α
 → β} [inst : Preorder α] [inst_1 : Preorder β],   AntitoneOn f₁ s → Set.EqOn f₁
 f₂ s …
· 使用定理 `Set.EqOn.symm`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ : α → 
β}, Set.EqOn f₁ f₂ s → Set.EqOn f₂ f₁ s
-/
theorem EqOn.congr_antitoneOn (h : s.EqOn f₁ f₂) : AntitoneOn f₁ s ↔ AntitoneOn f₂ s :=
  ⟨fun h₁ => h₁.congr h, fun h₂ => h₂.congr h.symm⟩
/-
**Set.EqOn.congr_strictMonoOn** 是 Mathlib 中的一个定理，位于命名空间 `Set.EqOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ : α → β} [inst : Preord
er α] [inst_1 : Preorder β],   Set.EqOn f₁ f₂ s → (StrictMonoOn f₁ s ↔ StrictMon
oOn f₂ s)
参数：StrictMonoOn f₁ s ↔ StrictMonoOn f₂ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMonoOn.congr`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ :
 α → β} [inst : Preorder α] [inst_1 : Preorder β],   StrictMonoOn f₁ s → Set.EqO
n f₁ f₂ …
· 使用定理 `Set.EqOn.symm`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ : α → 
β}, Set.EqOn f₁ f₂ s → Set.EqOn f₂ f₁ s
-/
theorem EqOn.congr_strictMonoOn (h : s.EqOn f₁ f₂) : StrictMonoOn f₁ s ↔ StrictMonoOn f₂ s :=
  ⟨fun h₁ => h₁.congr h, fun h₂ => h₂.congr h.symm⟩
/-
**Set.EqOn.congr_strictAntiOn** 是 Mathlib 中的一个定理，位于命名空间 `Set.EqOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ : α → β} [inst : Preord
er α] [inst_1 : Preorder β],   Set.EqOn f₁ f₂ s → (StrictAntiOn f₁ s ↔ StrictAnt
iOn f₂ s)
参数：StrictAntiOn f₁ s ↔ StrictAntiOn f₂ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictAntiOn.congr`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ :
 α → β} [inst : Preorder α] [inst_1 : Preorder β],   StrictAntiOn f₁ s → Set.EqO
n f₁ f₂ …
· 使用定理 `Set.EqOn.symm`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ : α → 
β}, Set.EqOn f₁ f₂ s → Set.EqOn f₂ f₁ s
-/
theorem EqOn.congr_strictAntiOn (h : s.EqOn f₁ f₂) : StrictAntiOn f₁ s ↔ StrictAntiOn f₂ s :=
  ⟨fun h₁ => h₁.congr h, fun h₂ => h₂.congr h.symm⟩

end Order

/-! ### Monotonicity lemmas -/
section Mono

variable {s s₂ : Set α} {f : α → β} [Preorder α] [Preorder β]

/-
**Set._root_.MonotoneOn.mono** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MonotoneOn.mono (h : MonotoneOn f s) (h' : s₂ ⊆ s) : MonotoneOn f s₂ :=
  fun _ hx _ hy => h (h' hx) (h' hy)
/-
**Set._root_.AntitoneOn.mono** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.AntitoneOn.mono (h : AntitoneOn f s) (h' : s₂ ⊆ s) : AntitoneOn f s₂ :=
  fun _ hx _ hy => h (h' hx) (h' hy)
/-
**Set._root_.StrictMonoOn.mono** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.StrictMonoOn.mono (h : StrictMonoOn f s) (h' : s₂ ⊆ s) : StrictMonoOn f s₂ :=
  fun _ hx _ hy => h (h' hx) (h' hy)
/-
**Set._root_.StrictAntiOn.mono** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.StrictAntiOn.mono (h : StrictAntiOn f s) (h' : s₂ ⊆ s) : StrictAntiOn f s₂ :=
  fun _ hx _ hy => h (h' hx) (h' hy)
/-
**Set._root_.MonotoneOn.monotone** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem _root_.MonotoneOn.monotone (h : MonotoneOn f s) :
    Monotone (f ∘ Subtype.val : s → β) :=
  fun x y hle => h x.coe_prop y.coe_prop hle
/-
**Set._root_.AntitoneOn.monotone** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem _root_.AntitoneOn.monotone (h : AntitoneOn f s) :
    Antitone (f ∘ Subtype.val : s → β) :=
  fun x y hle => h x.coe_prop y.coe_prop hle
/-
**Set._root_.StrictMonoOn.strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem _root_.StrictMonoOn.strictMono (h : StrictMonoOn f s) :
    StrictMono (f ∘ Subtype.val : s → β) :=
  fun x y hlt => h x.coe_prop y.coe_prop hlt
/-
**Set._root_.StrictAntiOn.strictAnti** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem _root_.StrictAntiOn.strictAnti (h : StrictAntiOn f s) :
    StrictAnti (f ∘ Subtype.val : s → β) :=
  fun x y hlt => h x.coe_prop y.coe_prop hlt
/-
**Set.monotoneOn_insert_iff** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：monotoneOn_insert_iff {a : α} : MonotoneOn f (insert a s) ↔ (forall b in s
, b <= a -> f b <= f a) ∧ (forall b in s, a <= b -> f a <= f b) ∧ MonotoneOn f s
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma monotoneOn_insert_iff {a : α} :
    MonotoneOn f (insert a s) ↔
      (∀ b ∈ s, b ≤ a → f b ≤ f a) ∧ (∀ b ∈ s, a ≤ b → f a ≤ f b) ∧ MonotoneOn f s := by
  simp [MonotoneOn, forall_and]
/-
**Set.antitoneOn_insert_iff** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：antitoneOn_insert_iff {a : α} : AntitoneOn f (insert a s) ↔ (forall b in s
, b <= a -> f a <= f b) ∧ (forall b in s, a <= b -> f b <= f a) ∧ AntitoneOn f s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.monotoneOn_insert_iff`：monotoneOn_insert_iff {a : α} : MonotoneOn f 
(insert a s) ↔ (forall b in s, b <= a -> f b <= f a) ∧ (forall b in s, a <= b ->
 f a <= f b) ∧ …
-/
lemma antitoneOn_insert_iff {a : α} :
    AntitoneOn f (insert a s) ↔
      (∀ b ∈ s, b ≤ a → f a ≤ f b) ∧ (∀ b ∈ s, a ≤ b → f b ≤ f a) ∧ AntitoneOn f s :=
  @monotoneOn_insert_iff α βᵒᵈ _ _ _ _ _

end Mono

end Set



open Function

/-! ### Monotone -/
namespace Monotone

variable [Preorder α] [Preorder β] {f : α → β}

/-
**Monotone.domRestrict** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : Preorder β] 
{f : α → β},   Monotone f → ∀ (s : Set α), Monotone (s.domRestrict f)
参数：s : Set α；s.domRestrict f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem domRestrict (h : Monotone f) (s : Set α) : Monotone (s.domRestrict f) :=
  fun _ _ hxy => h hxy

@[deprecated (since := "2026-07-19")] alias restrict := Monotone.domRestrict
/-
**Monotone.codRestrict** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : Preorder β] 
{f : α → β},   Monotone f → ∀ {s : Set β} (hs : ∀ (x : α), f x ∈ s), Monotone (S
et.codRestrict f s hs)
参数：hs : ∀ (x : α), f x ∈ s；Set.codRestrict f s hs。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem codRestrict (h : Monotone f) {s : Set β} (hs : ∀ x, f x ∈ s) :
    Monotone (s.codRestrict f hs) :=
  h
/-
**Monotone.rangeFactorization** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : Preorder β] 
{f : α → β},   Monotone f → Monotone (Set.rangeFactorization f)
参数：Set.rangeFactorization f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem rangeFactorization (h : Monotone f) : Monotone (Set.rangeFactorization f) :=
  h

end Monotone

section strictMono

variable [Preorder α] [Preorder β] {f : α → β} {s : Set α}

@[simp]
/-
**strictMono_domRestrict** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strictMono_domRestrict : StrictMono (s.domRestrict f) ↔ StrictMonoOn f s
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem strictMono_domRestrict : StrictMono (s.domRestrict f) ↔ StrictMonoOn f s := by
  simp [Set.domRestrict, StrictMono, StrictMonoOn]

alias ⟨_root_.StrictMono.of_domRestrict, _root_.StrictMonoOn.domRestrict⟩ := strictMono_domRestrict

@[deprecated (since := "2026-07-19")] alias strictMono_restrict := strictMono_domRestrict
@[deprecated (since := "2026-07-19")]
alias _root_.StrictMono.of_restrict := _root_.StrictMono.of_domRestrict
@[deprecated (since := "2026-07-19")]
alias _root_.StrictMonoOn.restrict := _root_.StrictMonoOn.domRestrict
/-
**StrictMono.codRestrict** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictMono.codRestrict (hf : StrictMono f) {s : Set β} (hs : forall x, f x
 in s) : StrictMono (Set.codRestrict f s hs)
参数：hf : StrictMono f；hs : forall x, f x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem StrictMono.codRestrict (hf : StrictMono f)
    {s : Set β} (hs : ∀ x, f x ∈ s) : StrictMono (Set.codRestrict f s hs) :=
  hf
/-
**strictMonoOn_insert_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：strictMonoOn_insert_iff {a : α} : StrictMonoOn f (insert a s) ↔ (forall b 
in s, b < a -> f b < f a) ∧ (forall b in s, a < b -> f a < f b) ∧ StrictMonoOn f
 s
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma strictMonoOn_insert_iff {a : α} :
    StrictMonoOn f (insert a s) ↔
       (∀ b ∈ s, b < a → f b < f a) ∧ (∀ b ∈ s, a < b → f a < f b) ∧ StrictMonoOn f s := by
  simp [StrictMonoOn, forall_and]
/-
**strictAntiOn_insert_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：strictAntiOn_insert_iff {a : α} : StrictAntiOn f (insert a s) ↔ (forall b 
in s, b < a -> f a < f b) ∧ (forall b in s, a < b -> f b < f a) ∧ StrictAntiOn f
 s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `strictMonoOn_insert_iff`：strictMonoOn_insert_iff {a : α} : StrictMonoOn 
f (insert a s) ↔ (forall b in s, b < a -> f b < f a) ∧ (forall b in s, a < b -> 
f a < f b) ∧ …
-/
lemma strictAntiOn_insert_iff {a : α} :
    StrictAntiOn f (insert a s) ↔
       (∀ b ∈ s, b < a → f a < f b) ∧ (∀ b ∈ s, a < b → f b < f a) ∧ StrictAntiOn f s :=
  @strictMonoOn_insert_iff α βᵒᵈ _ _ _ _ _
/-
**strictMonoOn_insert_iff_of_forall_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：strictMonoOn_insert_iff_of_forall_le {a : α} (ha : forall x in s, x <= a) 
: StrictMonoOn f (insert a s) ↔ (forall b in s, b < a -> f b < f a) ∧ StrictMono
On f s
参数：ha : forall x in s, x <= a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `strictMonoOn_insert_iff`：strictMonoOn_insert_iff {a : α} : StrictMonoOn 
f (insert a s) ↔ (forall b in s, b < a -> f b < f a) ∧ (forall b in s, a < b -> 
f a < f b) ∧ …
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
-/
lemma strictMonoOn_insert_iff_of_forall_le {a : α} (ha : ∀ x ∈ s, x ≤ a) :
    StrictMonoOn f (insert a s) ↔ (∀ b ∈ s, b < a → f b < f a) ∧ StrictMonoOn f s := by
  rw [strictMonoOn_insert_iff]
  have : ∀ b ∈ s, a < b → f a < f b := by
    intro b hb hab
    cases (ha _ hb).not_gt hab
  tauto
/-
**strictMonoOn_insert_iff_of_forall_ge** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：strictMonoOn_insert_iff_of_forall_ge {a : α} (ha : forall x in s, a <= x) 
: StrictMonoOn f (insert a s) ↔ (forall b in s, a < b -> f a < f b) ∧ StrictMono
On f s
参数：ha : forall x in s, a <= x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `strictMonoOn_insert_iff`：strictMonoOn_insert_iff {a : α} : StrictMonoOn 
f (insert a s) ↔ (forall b in s, b < a -> f b < f a) ∧ (forall b in s, a < b -> 
f a < f b) ∧ …
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
-/
lemma strictMonoOn_insert_iff_of_forall_ge {a : α} (ha : ∀ x ∈ s, a ≤ x) :
    StrictMonoOn f (insert a s) ↔ (∀ b ∈ s, a < b → f a < f b) ∧ StrictMonoOn f s := by
  rw [strictMonoOn_insert_iff]
  have : ∀ b ∈ s, b < a → f b < f a := by
    intro b hb hab
    cases (ha _ hb).not_gt hab
  tauto
/-
**strictAntiOn_insert_iff_of_forall_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：strictAntiOn_insert_iff_of_forall_le {a : α} (ha : forall x in s, x <= a) 
: StrictAntiOn f (insert a s) ↔ (forall b in s, b < a -> f a < f b) ∧ StrictAnti
On f s
参数：ha : forall x in s, x <= a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `strictAntiOn_insert_iff`：strictAntiOn_insert_iff {a : α} : StrictAntiOn 
f (insert a s) ↔ (forall b in s, b < a -> f a < f b) ∧ (forall b in s, a < b -> 
f b < f a) ∧ …
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
-/
lemma strictAntiOn_insert_iff_of_forall_le {a : α} (ha : ∀ x ∈ s, x ≤ a) :
    StrictAntiOn f (insert a s) ↔ (∀ b ∈ s, b < a → f a < f b) ∧ StrictAntiOn f s := by
  rw [strictAntiOn_insert_iff]
  have : ∀ b ∈ s, a < b → f b < f a := by
    intro b hb hab
    cases (ha _ hb).not_gt hab
  tauto
/-
**strictAntiOn_insert_iff_of_forall_ge** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：strictAntiOn_insert_iff_of_forall_ge {a : α} (ha : forall x in s, a <= x) 
: StrictAntiOn f (insert a s) ↔ (forall b in s, a < b -> f b < f a) ∧ StrictAnti
On f s
参数：ha : forall x in s, a <= x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `strictAntiOn_insert_iff`：strictAntiOn_insert_iff {a : α} : StrictAntiOn 
f (insert a s) ↔ (forall b in s, b < a -> f a < f b) ∧ (forall b in s, a < b -> 
f b < f a) ∧ …
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
-/
lemma strictAntiOn_insert_iff_of_forall_ge {a : α} (ha : ∀ x ∈ s, a ≤ x) :
    StrictAntiOn f (insert a s) ↔ (∀ b ∈ s, a < b → f b < f a) ∧ StrictAntiOn f s := by
  rw [strictAntiOn_insert_iff]
  have : ∀ b ∈ s, b < a → f a < f b := by
    intro b hb hab
    cases (ha _ hb).not_gt hab
  tauto

end strictMono

namespace Function

open Set

/-
**Function.monotoneOn_of_rightInvOn_of_mapsTo** 是 Mathlib 中的一个定理，位于命名空间 `Functio
n`。
形式化陈述：monotoneOn_of_rightInvOn_of_mapsTo {α β : Type*} [PartialOrder α] [LinearO
rder β] {φ : β -> α} {ψ : α -> β} {t : Set β} {s : Set α} (hφ : MonotoneOn φ t) 
(φψs : Set.RightInvOn ψ φ s) (ψts : Set.MapsTo ψ s t) : MonotoneOn ψ s
参数：hφ : MonotoneOn φ t；φψs : Set.RightInvOn ψ φ s；ψts : Set.MapsTo ψ s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.RightInvOn.eq`：eq (h : RightInvOn f' f t) {y} (hy : y in t) : f (f' 
y) = y
-/
theorem monotoneOn_of_rightInvOn_of_mapsTo {α β : Type*} [PartialOrder α] [LinearOrder β]
    {φ : β → α} {ψ : α → β} {t : Set β} {s : Set α} (hφ : MonotoneOn φ t)
    (φψs : Set.RightInvOn ψ φ s) (ψts : Set.MapsTo ψ s t) : MonotoneOn ψ s := by
  rintro x xs y ys l
  rcases le_total (ψ x) (ψ y) with (ψxy | ψyx)
  · exact ψxy
  · have := hφ (ψts ys) (ψts xs) ψyx
    rw [φψs.eq ys, φψs.eq xs] at this
    induction le_antisymm l this
    exact le_refl _
/-
**Function.antitoneOn_of_rightInvOn_of_mapsTo** 是 Mathlib 中的一个定理，位于命名空间 `Functio
n`。
形式化陈述：antitoneOn_of_rightInvOn_of_mapsTo [PartialOrder α] [LinearOrder β] {φ : β
 -> α} {ψ : α -> β} {t : Set β} {s : Set α} (hφ : AntitoneOn φ t) (φψs : Set.Rig
htInvOn ψ φ s) (ψts : Set.MapsTo ψ s t) : AntitoneOn ψ s
参数：hφ : AntitoneOn φ t；φψs : Set.RightInvOn ψ φ s；ψts : Set.MapsTo ψ s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonotoneOn.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [
inst_1 : Preorder β] {f : α → β} {s : Set α},   MonotoneOn f s → AntitoneOn (⇑Or
derDual.toD…
· 使用定理 `Function.monotoneOn_of_rightInvOn_of_mapsTo`：monotoneOn_of_rightInvOn_of
_mapsTo {α β : Type*} [PartialOrder α] [LinearOrder β] {φ : β -> α} {ψ : α -> β}
 {t : Set β} {s : Set α} (hφ : Mo…
· 使用定理 `AntitoneOn.dual_left`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [i
nst_1 : Preorder β] {f : α → β} {s : Set α},   AntitoneOn f s → MonotoneOn (f ∘ 
⇑OrderDual…
-/
theorem antitoneOn_of_rightInvOn_of_mapsTo [PartialOrder α] [LinearOrder β]
    {φ : β → α} {ψ : α → β} {t : Set β} {s : Set α} (hφ : AntitoneOn φ t)
    (φψs : Set.RightInvOn ψ φ s) (ψts : Set.MapsTo ψ s t) : AntitoneOn ψ s :=
  (monotoneOn_of_rightInvOn_of_mapsTo hφ.dual_left φψs ψts).dual_right

end Function

