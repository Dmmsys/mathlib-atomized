/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.Monotone.Monovary
public import Mathlib.SetTheory.Cardinal.Order

/-!
# Interpreting monovarying functions as monotone functions

This file proves that monovarying functions to linear orders can be made simultaneously monotone by
setting the correct order on their shared indexing type.
-/

@[expose] public section

open Function Set

variable {ι ι' α β γ : Type*}

section
variable [LinearOrder α] [LinearOrder β] (f : ι → α) (g : ι → β) {s : Set ι}

/-- If `f : ι → α` and `g : ι → β` are monovarying, then `MonovaryOrder f g` is a linear order on
`ι` that makes `f` and `g` simultaneously monotone.
We define `i < j` if `f i < f j`, or if `f i = f j` and `g i < g j`, breaking ties arbitrarily. -/
/-
**MonovaryOrder** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MonovaryOrder (i j : ι) : Prop
参数：i j : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f : ι → α` and `g : ι → β` are monovarying, then `MonovaryOrder f g` is a li
near order on
`ι` that makes `f` and `g` simultaneously monotone.
We define `i < j` if `f i < f j`, or if `f i = f j` and `g i < g j`, breaking ti
es arbitrarily.
-/
def MonovaryOrder (i j : ι) : Prop :=
  Prod.Lex (· < ·) (Prod.Lex (· < ·) WellOrderingRel) (f i, g i, i) (f j, g j, j)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsStrictTotalOrder ι (MonovaryOrder f g) where
  toTrichotomous := Std.trichotomous_of_rel_or_eq_or_rel_swap fun {a b} ↦ by
    convert! trichotomous_of (Prod.Lex (· < ·) <| Prod.Lex (· < ·) WellOrderingRel) _ _
    · simp only [Prod.ext_iff, ← and_assoc, imp_and, iff_and_self]
      exact ⟨congr_arg _, congr_arg _⟩
    · infer_instance
  irrefl i := by rw [MonovaryOrder]; exact irrefl _
  trans i j k := by rw [MonovaryOrder]; exact _root_.trans

variable {f g}
/-
**monovaryOn_iff_exists_monotoneOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：monovaryOn_iff_exists_monotoneOn : MonovaryOn f g s ↔ exists (_ : LinearOr
der ι), MonotoneOn f s ∧ MonotoneOn g s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsStrictTotalOrderMonovaryOrder`：∀ {ι : Type u_1} {α : Type u_3} {β 
: Type u_4} [inst : LinearOrder α] [inst_1 : LinearOrder β] (f : ι → α) (g : ι →
 β),   IsStrictTotalOrder…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `monotoneOn_iff_forall_lt`：monotoneOn_iff_forall_lt : MonotoneOn f s ↔ fo
rall ⦃a⦄ (_ : a in s) ⦃b⦄ (_ : b in s), a < b -> f a <= f b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Prod.lex_iff`：lex_iff : Prod.Lex r s x y ↔ r x.1 y.1 ∨ x.1 = y.1 ∧ s x.2
 y.2
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `MonovaryOn.symm`：∀ {ι : Type u_1} {α : Type u_3} {β : Type u_4} [inst : 
Preorder α] [inst_1 : LinearOrder β] {f : ι → α} {g : ι → β}   {s : Set ι}, Mono
varyO…
· 使用定理 `MonotoneOn.monovaryOn`：∀ {ι : Type u_1} {α : Type u_3} {β : Type u_4} [i
nst : Preorder α] [inst_1 : Preorder β] {f : ι → α} {g : ι → β}   {s : Set ι} [i
nst_2 : Lin…
-/
lemma monovaryOn_iff_exists_monotoneOn :
    MonovaryOn f g s ↔ ∃ (_ : LinearOrder ι), MonotoneOn f s ∧ MonotoneOn g s := by
  classical
  let := linearOrderOfSTO (MonovaryOrder f g)
  refine ⟨fun hfg => ⟨‹_›, monotoneOn_iff_forall_lt.2 fun i hi j hj hij => ?_,
    monotoneOn_iff_forall_lt.2 fun i hi j hj hij => ?_⟩, ?_⟩
  · obtain h | ⟨h, -⟩ := Prod.lex_iff.1 hij <;> exact h.le
  · obtain h | ⟨-, h⟩ := Prod.lex_iff.1 hij
    · exact hfg.symm hi hj h
    obtain h | ⟨h, -⟩ := Prod.lex_iff.1 h <;> exact h.le
  · rintro ⟨_, hf, hg⟩
    exact hf.monovaryOn hg
/-
**antivaryOn_iff_exists_monotoneOn_antitoneOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：antivaryOn_iff_exists_monotoneOn_antitoneOn : AntivaryOn f g s ↔ exists (_
 : LinearOrder ι), MonotoneOn f s ∧ AntitoneOn g s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma antivaryOn_iff_exists_monotoneOn_antitoneOn :
    AntivaryOn f g s ↔ ∃ (_ : LinearOrder ι), MonotoneOn f s ∧ AntitoneOn g s := by
  simp_rw [← monovaryOn_toDual_right, monovaryOn_iff_exists_monotoneOn, monotoneOn_toDual_comp_iff]
/-
**monovaryOn_iff_exists_antitoneOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：monovaryOn_iff_exists_antitoneOn : MonovaryOn f g s ↔ exists (_ : LinearOr
der ι), AntitoneOn f s ∧ AntitoneOn g s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma monovaryOn_iff_exists_antitoneOn :
    MonovaryOn f g s ↔ ∃ (_ : LinearOrder ι), AntitoneOn f s ∧ AntitoneOn g s := by
  simp_rw [← antivaryOn_toDual_left, antivaryOn_iff_exists_monotoneOn_antitoneOn,
    monotoneOn_toDual_comp_iff]
/-
**antivaryOn_iff_exists_antitoneOn_monotoneOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：antivaryOn_iff_exists_antitoneOn_monotoneOn : AntivaryOn f g s ↔ exists (_
 : LinearOrder ι), AntitoneOn f s ∧ MonotoneOn g s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma antivaryOn_iff_exists_antitoneOn_monotoneOn :
    AntivaryOn f g s ↔ ∃ (_ : LinearOrder ι), AntitoneOn f s ∧ MonotoneOn g s := by
  simp_rw [← monovaryOn_toDual_left, monovaryOn_iff_exists_monotoneOn, monotoneOn_toDual_comp_iff]
/-
**monovary_iff_exists_monotone** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：monovary_iff_exists_monotone : Monovary f g ↔ exists (_ : LinearOrder ι), 
Monotone f ∧ Monotone g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma monovary_iff_exists_monotone :
    Monovary f g ↔ ∃ (_ : LinearOrder ι), Monotone f ∧ Monotone g := by
  simp [← monovaryOn_univ, monovaryOn_iff_exists_monotoneOn]
/-
**monovary_iff_exists_antitone** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：monovary_iff_exists_antitone : Monovary f g ↔ exists (_ : LinearOrder ι), 
Antitone f ∧ Antitone g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma monovary_iff_exists_antitone :
    Monovary f g ↔ ∃ (_ : LinearOrder ι), Antitone f ∧ Antitone g := by
  simp [← monovaryOn_univ, monovaryOn_iff_exists_antitoneOn]
/-
**antivary_iff_exists_monotone_antitone** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：antivary_iff_exists_monotone_antitone : Antivary f g ↔ exists (_ : LinearO
rder ι), Monotone f ∧ Antitone g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma antivary_iff_exists_monotone_antitone :
    Antivary f g ↔ ∃ (_ : LinearOrder ι), Monotone f ∧ Antitone g := by
  simp [← antivaryOn_univ, antivaryOn_iff_exists_monotoneOn_antitoneOn]
/-
**antivary_iff_exists_antitone_monotone** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：antivary_iff_exists_antitone_monotone : Antivary f g ↔ exists (_ : LinearO
rder ι), Antitone f ∧ Monotone g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma antivary_iff_exists_antitone_monotone :
    Antivary f g ↔ ∃ (_ : LinearOrder ι), Antitone f ∧ Monotone g := by
  simp [← antivaryOn_univ, antivaryOn_iff_exists_antitoneOn_monotoneOn]

alias ⟨MonovaryOn.exists_monotoneOn, _⟩ := monovaryOn_iff_exists_monotoneOn
alias ⟨MonovaryOn.exists_antitoneOn, _⟩ := monovaryOn_iff_exists_antitoneOn
alias ⟨AntivaryOn.exists_monotoneOn_antitoneOn, _⟩ := antivaryOn_iff_exists_monotoneOn_antitoneOn
alias ⟨AntivaryOn.exists_antitoneOn_monotoneOn, _⟩ := antivaryOn_iff_exists_antitoneOn_monotoneOn
alias ⟨Monovary.exists_monotone, _⟩ := monovary_iff_exists_monotone
alias ⟨Monovary.exists_antitone, _⟩ := monovary_iff_exists_antitone
alias ⟨Antivary.exists_monotone_antitone, _⟩ := antivary_iff_exists_monotone_antitone
alias ⟨Antivary.exists_antitone_monotone, _⟩ := antivary_iff_exists_antitone_monotone

end

