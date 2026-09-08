/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Order.Filter.TendstoCofinite

/-!
# Northcott Functions

In number theory, the height function `h` satisfies the *Northcott property* that the sets
`{a | h a ≤ b}` are finite. This file extracts this notion as a typeclass and provides some API.

## Main definitions

* `Northcott h`: A function `h : α → β` is Northcott if the sets `{a : α | h a ≤ b}` are all finite.

## Main theorems

* `Northcott.exists_min_image h s hs`: If `h` is Northcott to a linear order, then `h` has an
  absolute minimum on every nonempty set `s`.

## References

* [D. Northcott, *An inequality in the theory of arithmetic on algebraic varieties*](northcott1949)
-/

@[expose] public noncomputable section

variable {α β γ : Type*} (h : α → β) (h' : β → γ)

/-- A function `h : α → β` is Northcott if the sets `{a : α | h a ≤ b}` are all finite. -/
@[mk_iff]
/-
**Northcott** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{α : Type u_1} → {β : Type u_2} → (α → β) → [LE β] → Prop
参数：α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `h : α → β` is Northcott if the sets `{a : α | h a ≤ b}` are all fini
te.
-/
class Northcott [LE β] : Prop where
  finite_le : ∀ b, {a : α | h a ≤ b}.Finite

open Filter in
/-
**northcott_iff_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：northcott_iff_tendsto [LinearOrder β] [NoMaxOrder β] : Northcott h ↔ Tends
to h cofinite atTop
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `NoMaxOrder.exists_gt`：∀ {α : Type u_3} {inst : LT α} [self : NoMaxOrder 
α] (a : α), ∃ b, a < b
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
-/
theorem northcott_iff_tendsto [LinearOrder β] [NoMaxOrder β] :
    Northcott h ↔ Tendsto h cofinite atTop := by
  simp_rw [northcott_iff, tendsto_atTop, eventually_cofinite, not_le]
  refine ⟨fun H b ↦ (H b).subset fun x ↦ le_of_lt, fun H b ↦ ?_⟩
  obtain ⟨b', hc⟩ := exists_gt b
  exact (H b').subset fun x hx ↦ lt_of_le_of_lt hx hc

namespace Northcott

/-
**Northcott.exists_min_image** 是 Mathlib 中的一个定理，位于命名空间 `Northcott`。
形式化陈述：exists_min_image [LinearOrder β] [Northcott h] (s : Set α) (hs : s.Nonempt
y) : exists a in s, forall a' in s, h a <= h a'
参数：s : Set α；hs : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.exists_min_image`：∀ {α : Type u} {β : Type v} [inst : LinearOrder β]
 (s : Set α) (f : α → β),   s.Finite → s.Nonempty → ∃ a ∈ s, ∀ b ∈ s, f a ≤ f b
· 使用定理 `Set.Finite.inter_of_left`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ (t : 
Set α), (s ∩ t).Finite
· 使用定理 `Northcott.finite_le`：∀ {α : Type u_1} {β : Type u_2} {h : α → β} {inst :
 LE β} [self : Northcott h] (b : β), {a | h a ≤ b}.Finite
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem exists_min_image [LinearOrder β] [Northcott h] (s : Set α) (hs : s.Nonempty) :
    ∃ a ∈ s, ∀ a' ∈ s, h a ≤ h a' := by
  obtain ⟨a₁, h₁⟩ := hs
  obtain ⟨a₂, h₂, h₃⟩ := Set.exists_min_image ({a | h a ≤ h a₁} ∩ s) h
    ((finite_le (h a₁)).inter_of_left s) ⟨a₁, le_rfl, h₁⟩
  grind

/-- A composition `h' ∘ h` is Northcott when `h` is Northcott and preimages of bounded above sets
under `h'` are bounded above. -/
/-
**Northcott.comp_of_bddAbove** 是 Mathlib 中的一个引理，位于命名空间 `Northcott`。
形式化陈述：comp_of_bddAbove [Preorder β] [LE γ] [Northcott h] (H : forall c, BddAbove
 (h' ⁻¹' {x | x <= c})) : Northcott (h' ∘ h) where finite_le c
参数：H : forall c, BddAbove (h' ⁻¹' {x | x <= c})。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `bddAbove_def`：bddAbove_def : BddAbove s ↔ exists x, forall y in s, y <= 
x
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Northcott.finite_le`：∀ {α : Type u_1} {β : Type u_2} {h : α → β} {inst :
 LE β} [self : Northcott h] (b : β), {a | h a ≤ b}.Finite

--- 原说明 ---
A composition `h' ∘ h` is Northcott when `h` is Northcott and preimages of bound
ed above sets
under `h'` are bounded above.
-/
lemma comp_of_bddAbove [Preorder β] [LE γ] [Northcott h] (H : ∀ c, BddAbove (h' ⁻¹' {x | x ≤ c})) :
    Northcott (h' ∘ h) where
  finite_le c := by
    obtain ⟨b, hb⟩ := bddAbove_def.mp (H c)
    exact (finite_le (h := h) b).subset <| by grind

/-- A composition `h' ∘ h` is Northcott when `h'` is Northcott and the fibers of `h` are finite. -/
/-
**Northcott.comp_of_finite_fibers** 是 Mathlib 中的一个引理，位于命名空间 `Northcott`。
形式化陈述：comp_of_finite_fibers [LE γ] [Northcott h'] [Filter.TendstoCofinite h] : N
orthcott (h' ∘ h) where finite_le c
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.of_finite_fibers`：∀ {α : Type u} {β : Type v} (f : α → β) {s 
: Set α}, (f '' s).Finite → (∀ x ∈ f '' s, (s ∩ f ⁻¹' {x}).Finite) → s.Finite
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Northcott.finite_le`：∀ {α : Type u_1} {β : Type u_2} {h : α → β} {inst :
 LE β} [self : Northcott h] (b : β), {a | h a ≤ b}.Finite
· 使用定理 `Set.Finite.inter_of_right`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ (t :
 Set α), (t ∩ s).Finite
· 使用定理 `Filter.TendstoCofinite.finite_preimage_singleton`：∀ {α : Type u_1} {β : 
Type u_2} (f : α → β) [Filter.TendstoCofinite f] (b : β), (f ⁻¹' {b}).Finite

--- 原说明 ---
A composition `h' ∘ h` is Northcott when `h'` is Northcott and the fibers of `h`
 are finite.
-/
lemma comp_of_finite_fibers [LE γ] [Northcott h'] [Filter.TendstoCofinite h] :
    Northcott (h' ∘ h) where
  finite_le c := by
    refine Set.Finite.of_finite_fibers h ?_ fun x _ ↦
      (Filter.TendstoCofinite.finite_preimage_singleton h x).inter_of_right _
    exact (finite_le (h := h') c).subset <| by grind

end Northcott

