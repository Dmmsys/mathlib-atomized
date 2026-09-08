/-
Copyright (c) 2020 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Order.Group.Indicator
public import Mathlib.Analysis.Normed.Group.Basic

/-!
# Indicator function and (e)norm

This file contains a few simple lemmas about `Set.indicator`, `norm` and `enorm`.

## Tags
indicator, norm
-/

public section

open Set

section ESeminormedAddMonoid

variable {α ε : Type*} [TopologicalSpace ε] [ESeminormedAddMonoid ε]
  {s t : Set α} (f : α → ε) (a : α)

/-
**enorm_indicator_eq_indicator_enorm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：enorm_indicator_eq_indicator_enorm : ‖indicator s f a‖ₑ = indicator s (fun
 a => ‖f a‖ₑ) a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.indicator_comp_of_zero`：∀ {α : Type u_1} {M : Type u_3} {N : Type u_
4} [inst : Zero M] [inst_1 : Zero N] {s : Set α} {f : α → M} {g : M → N},   g 0 
= 0 → s.indicato…
· 使用定理 `enorm_zero`：∀ {E : Type u_8} [inst : TopologicalSpace E] [inst_1 : ESemi
normedAddMonoid E], ‖0‖ₑ = 0
-/
lemma enorm_indicator_eq_indicator_enorm :
    ‖indicator s f a‖ₑ = indicator s (fun a => ‖f a‖ₑ) a :=
  flip congr_fun a (indicator_comp_of_zero (enorm_zero (E := ε))).symm
/-
**enorm_indicator_le_of_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：enorm_indicator_le_of_subset (h : s subseteq t) (f : α -> ε) (a : α) : ‖in
dicator s f a‖ₑ <= ‖indicator t f a‖ₑ
参数：h : s subseteq t；f : α -> ε；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `enorm_indicator_eq_indicator_enorm`：enorm_indicator_eq_indicator_enorm :
 ‖indicator s f a‖ₑ = indicator s (fun a => ‖f a‖ₑ) a
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `Set.indicator_le_indicator_apply_of_subset`：∀ {α : Type u_2} {M : Type u
_3} [inst : Preorder M] [inst_1 : Zero M] {s t : Set α} {f : α → M} {a : α},   s
 ⊆ t → 0 ≤ f a → s.indicator f a…
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem enorm_indicator_le_of_subset (h : s ⊆ t) (f : α → ε) (a : α) :
    ‖indicator s f a‖ₑ ≤ ‖indicator t f a‖ₑ := by
  simp only [enorm_indicator_eq_indicator_enorm]
  grw [h]
/-
**indicator_enorm_le_enorm_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：indicator_enorm_le_enorm_self : indicator s (fun a => ‖f a‖ₑ) a <= ‖f a‖ₑ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.indicator_le_self'`：∀ {α : Type u_2} {M : Type u_3} [inst : Preorder
 M] [inst_1 : Zero M] {s : Set α} {f : α → M},   (∀ x ∉ s, 0 ≤ f x) → s.indicato
r f ≤ f
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
-/
theorem indicator_enorm_le_enorm_self : indicator s (fun a => ‖f a‖ₑ) a ≤ ‖f a‖ₑ :=
  indicator_le_self' (fun _ _ ↦ zero_le) a
/-
**enorm_indicator_le_enorm_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：enorm_indicator_le_enorm_self : ‖indicator s f a‖ₑ <= ‖f a‖ₑ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `enorm_indicator_eq_indicator_enorm`：enorm_indicator_eq_indicator_enorm :
 ‖indicator s f a‖ₑ = indicator s (fun a => ‖f a‖ₑ) a
· 使用定理 `indicator_enorm_le_enorm_self`：indicator_enorm_le_enorm_self : indicator
 s (fun a => ‖f a‖ₑ) a <= ‖f a‖ₑ
-/
theorem enorm_indicator_le_enorm_self : ‖indicator s f a‖ₑ ≤ ‖f a‖ₑ := by
  rw [enorm_indicator_eq_indicator_enorm]
  apply indicator_enorm_le_enorm_self

end ESeminormedAddMonoid

section SeminormedAddGroup

variable {α E : Type*} [SeminormedAddGroup E] {s t : Set α} (f : α → E) (a : α)

/-
**norm_indicator_eq_indicator_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_indicator_eq_indicator_norm : ‖indicator s f a‖ = indicator s (fun a 
=> ‖f a‖) a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.indicator_comp_of_zero`：∀ {α : Type u_1} {M : Type u_3} {N : Type u_
4} [inst : Zero M] [inst_1 : Zero N] {s : Set α} {f : α → M} {g : M → N},   g 0 
= 0 → s.indicato…
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
-/
theorem norm_indicator_eq_indicator_norm : ‖indicator s f a‖ = indicator s (fun a => ‖f a‖) a :=
  flip congr_fun a (indicator_comp_of_zero norm_zero).symm
/-
**nnnorm_indicator_eq_indicator_nnnorm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nnnorm_indicator_eq_indicator_nnnorm : ‖indicator s f a‖₊ = indicator s (f
un a => ‖f a‖₊) a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.indicator_comp_of_zero`：∀ {α : Type u_1} {M : Type u_3} {N : Type u_
4} [inst : Zero M] [inst_1 : Zero N] {s : Set α} {f : α → M} {g : M → N},   g 0 
= 0 → s.indicato…
· 使用定理 `nnnorm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖₊ = 0
-/
theorem nnnorm_indicator_eq_indicator_nnnorm :
    ‖indicator s f a‖₊ = indicator s (fun a => ‖f a‖₊) a :=
  flip congr_fun a (indicator_comp_of_zero nnnorm_zero).symm
/-
**norm_indicator_le_of_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_indicator_le_of_subset (h : s subseteq t) (f : α -> E) (a : α) : ‖ind
icator s f a‖ <= ‖indicator t f a‖
参数：h : s subseteq t；f : α -> E；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_indicator_eq_indicator_norm`：norm_indicator_eq_indicator_norm : ‖in
dicator s f a‖ = indicator s (fun a => ‖f a‖) a
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `Set.indicator_le_indicator_apply_of_subset`：∀ {α : Type u_2} {M : Type u
_3} [inst : Preorder M] [inst_1 : Zero M] {s t : Set α} {f : α → M} {a : α},   s
 ⊆ t → 0 ≤ f a → s.indicator f a…
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem norm_indicator_le_of_subset (h : s ⊆ t) (f : α → E) (a : α) :
    ‖indicator s f a‖ ≤ ‖indicator t f a‖ := by
  simp only [norm_indicator_eq_indicator_norm]
  grw [h]
/-
**indicator_norm_le_norm_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：indicator_norm_le_norm_self : indicator s (fun a => ‖f a‖) a <= ‖f a‖
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.indicator_le_self'`：∀ {α : Type u_2} {M : Type u_3} [inst : Preorder
 M] [inst_1 : Zero M] {s : Set α} {f : α → M},   (∀ x ∉ s, 0 ≤ f x) → s.indicato
r f ≤ f
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
-/
theorem indicator_norm_le_norm_self : indicator s (fun a => ‖f a‖) a ≤ ‖f a‖ :=
  indicator_le_self' (fun _ _ => norm_nonneg _) a
/-
**norm_indicator_le_norm_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_indicator_le_norm_self : ‖indicator s f a‖ <= ‖f a‖
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_indicator_eq_indicator_norm`：norm_indicator_eq_indicator_norm : ‖in
dicator s f a‖ = indicator s (fun a => ‖f a‖) a
· 使用定理 `indicator_norm_le_norm_self`：indicator_norm_le_norm_self : indicator s (
fun a => ‖f a‖) a <= ‖f a‖
-/
theorem norm_indicator_le_norm_self : ‖indicator s f a‖ ≤ ‖f a‖ := by
  rw [norm_indicator_eq_indicator_norm]
  apply indicator_norm_le_norm_self

end SeminormedAddGroup

