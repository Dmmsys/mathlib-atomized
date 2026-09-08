/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Data.Set.Monotone
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Extension of a monotone function from a set to the whole space

In this file we prove that if a function is monotone and is bounded on a set `s`, then it admits a
monotone extension to the whole space.
-/

public section


open Set

variable {α β : Type*} [LinearOrder α] [ConditionallyCompleteLinearOrder β] {f : α → β} {s : Set α}

/-- If a function is monotone and is bounded on a set `s`, then it admits a monotone extension to
the whole space. -/
/-
**MonotoneOn.exists_monotone_extension** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonotoneOn.exists_monotone_extension (h : MonotoneOn f s) (hl : BddBelow (
f '' s)) (hu : BddAbove (f '' s)) : exists g : α -> β, Monotone g ∧ EqOn f g s
参数：h : MonotoneOn f s；hl : BddBelow (f '' s)；hu : BddAbove (f '' s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BddAbove.mono`：BddAbove.mono ⦃s t : Set α⦄ (h : s subseteq t) : BddAbove
 t -> BddAbove s
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `Set.self_mem_Iic`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, a ∈ Set.
Iic a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Set.Nonempty.not_disjoint`：∀ {α : Type u} {s t : Set α}, (s ∩ t).Nonempt
y → ¬Disjoint s t
· 使用定理 `IsGreatest.nonempty`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α} {a
 : α}, IsGreatest s a → s.Nonempty
· 使用定理 `IsGreatest.csSup_eq`：IsGreatest.csSup_eq (H : IsGreatest s a) : sSup s =
 a
· 使用定理 `MonotoneOn.map_isGreatest`：∀ {α : Type u} {β : Type v} [inst : Preorder 
α] [inst_1 : Preorder β] {f : α → β} {t : Set α} {a : α},   MonotoneOn f t → IsG
reatest t a → I…
· 使用定理 `MonotoneOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s s₂ : Set α} {f : α →
 β} [inst : Preorder α] [inst_1 : Preorder β],   MonotoneOn f s → s₂ ⊆ s → Monot
oneOn…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Set.not_disjoint_iff_nonempty_inter`：not_disjoint_iff_nonempty_inter : ¬
 Disjoint s t ↔ (s inter t).Nonempty
· 使用定理 `le_csSup_of_le`：le_csSup_of_le (hs : BddAbove s) (hb : b in s) (h : a <=
 b) : a <= sSup s
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Disjoint.mono_left`：Disjoint.mono_left (h : a <= b) : Disjoint b c -> Di
sjoint a c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Iic_subset_Iic`：Iic_subset_Iic : Iic a subseteq Iic b ↔ a <= b
· 使用定理 `csSup_le_csSup`：csSup_le_csSup (ht : BddAbove t) (hs : s.Nonempty) (h : 
s subseteq t) : sSup s <= sSup t
· 使用定理 `Set.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set
 α}, s.Nonempty → (f '' s).Nonempty
· 使用定理 `Set.inter_subset_inter`：inter_subset_inter {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq t₁) (h₂ : s₂ subseteq t₂) : s₁ inter s₂ subseteq t₁ inter t₂
· 使用定理 `Set.Iic_subset_Iic._gcongr_3`：∀ {α : Type u_1} [inst : Preorder α] {a b 
: α}, a ≤ b → Set.Iic a ⊆ Set.Iic b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
If a function is monotone and is bounded on a set `s`, then it admits a monotone
 extension to
the whole space.
-/
theorem MonotoneOn.exists_monotone_extension (h : MonotoneOn f s) (hl : BddBelow (f '' s))
    (hu : BddAbove (f '' s)) : ∃ g : α → β, Monotone g ∧ EqOn f g s := by
  classical
    /- The extension is defined by `f x = f a` for `x ≤ a`, and `f x` is the supremum of the values
      of `f` to the left of `x` for `x ≥ a`. -/
    rcases hl with ⟨a, ha⟩
    have hu' : ∀ x, BddAbove (f '' (Iic x ∩ s)) := fun x =>
      hu.mono (image_mono inter_subset_right)
    let g : α → β := fun x => if Disjoint (Iic x) s then a else sSup (f '' (Iic x ∩ s))
    have hgs : EqOn f g s := by
      intro x hx
      simp only [g]
      have : IsGreatest (Iic x ∩ s) x := ⟨⟨self_mem_Iic, hx⟩, fun y hy => hy.1⟩
      rw [if_neg this.nonempty.not_disjoint,
        ((h.mono inter_subset_right).map_isGreatest this).csSup_eq]
    refine ⟨g, fun x y hxy => ?_, hgs⟩
    by_cases hx : Disjoint (Iic x) s <;> by_cases hy : Disjoint (Iic y) s <;>
      simp only [g, if_pos, if_neg, not_false_iff, *, refl]
    · rcases not_disjoint_iff_nonempty_inter.1 hy with ⟨z, hz⟩
      exact le_csSup_of_le (hu' _) (mem_image_of_mem _ hz) (ha <| mem_image_of_mem _ hz.2)
    · exact (hx <| hy.mono_left <| Iic_subset_Iic.2 hxy).elim
    · rw [not_disjoint_iff_nonempty_inter] at hx
      gcongr; exacts [hu' _, hx.image _]

/-- If a function is antitone and is bounded on a set `s`, then it admits an antitone extension to
the whole space. -/
/-
**AntitoneOn.exists_antitone_extension** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntitoneOn.exists_antitone_extension (h : AntitoneOn f s) (hl : BddBelow (
f '' s)) (hu : BddAbove (f '' s)) : exists g : α -> β, Antitone g ∧ EqOn f g s
参数：h : AntitoneOn f s；hl : BddBelow (f '' s)；hu : BddAbove (f '' s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonotoneOn.exists_monotone_extension`：MonotoneOn.exists_monotone_extensi
on (h : MonotoneOn f s) (hl : BddBelow (f '' s)) (hu : BddAbove (f '' s)) : exis
ts g : α -> β, Monotone g …
· 使用定理 `AntitoneOn.dual_right`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [
inst_1 : Preorder β] {f : α → β} {s : Set α},   AntitoneOn f s → MonotoneOn (⇑Or
derDual.toD…

--- 原说明 ---
If a function is antitone and is bounded on a set `s`, then it admits an antiton
e extension to
the whole space.
-/
theorem AntitoneOn.exists_antitone_extension (h : AntitoneOn f s) (hl : BddBelow (f '' s))
    (hu : BddAbove (f '' s)) : ∃ g : α → β, Antitone g ∧ EqOn f g s :=
  h.dual_right.exists_monotone_extension hu hl
