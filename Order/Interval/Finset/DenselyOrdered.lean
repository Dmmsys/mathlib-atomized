/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Order.Interval.Finset.Basic

/-!
# Linear locally finite orders are densely ordered iff they are trivial

## Main results
* `LocallyFiniteOrder.denselyOrdered_iff_subsingleton`:
  A linear locally finite order is densely ordered if and only if it is a subsingleton.

-/

public section

variable {X : Type*} [LinearOrder X] [LocallyFiniteOrder X]

/-
**LocallyFiniteOrder.denselyOrdered_iff_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 `
`。
形式化陈述：LocallyFiniteOrder.denselyOrdered_iff_subsingleton : DenselyOrdered X ↔ Su
bsingleton X
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_nontrivial_iff_subsingleton`：not_nontrivial_iff_subsingleton : ¬Nont
rivial α ↔ Subsingleton α
· 使用定理 `nontrivial_iff_lt`：nontrivial_iff_lt [LinearOrder α] : Nontrivial α ↔ ex
ists x y : α, x < y
· 使用定理 `not_lt_of_denselyOrdered_of_locallyFinite`：∀ {α : Type u_2} [inst : Preo
rder α] [LocallyFiniteOrder α] [DenselyOrdered α] (a b : α), ¬a < b
· 使用引理 `Subsingleton.instDenselyOrdered`：Subsingleton.instDenselyOrdered {X : Ty
pe*} [Subsingleton X] [LT X] : DenselyOrdered X
-/
lemma LocallyFiniteOrder.denselyOrdered_iff_subsingleton :
    DenselyOrdered X ↔ Subsingleton X := by
  refine ⟨fun H ↦ ?_, fun h ↦ h.instDenselyOrdered⟩
  rw [← not_nontrivial_iff_subsingleton, nontrivial_iff_lt]
  rintro ⟨a, b, hab⟩
  exact not_lt_of_denselyOrdered_of_locallyFinite a b hab
/-
**denselyOrdered_set_iff_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：denselyOrdered_set_iff_subsingleton {s : Set X} : DenselyOrdered s ↔ s.Sub
singleton
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
lemma denselyOrdered_set_iff_subsingleton {s : Set X} :
    DenselyOrdered s ↔ s.Subsingleton := by
  classical
  simp [LocallyFiniteOrder.denselyOrdered_iff_subsingleton]
/-
**WithBot.denselyOrdered_set_iff_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：WithBot.denselyOrdered_set_iff_subsingleton {s : Set (WithBot X)} : Densel
yOrdered s ↔ s.Subsingleton
参数：WithBot X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.subsingleton_coe`：subsingleton_coe (s : Set α) : Subsingleton s ↔ s.
Subsingleton
· 使用定理 `not_nontrivial_iff_subsingleton`：not_nontrivial_iff_subsingleton : ¬Nont
rivial α ↔ Subsingleton α
· 使用定理 `nontrivial_iff_lt`：nontrivial_iff_lt [LinearOrder α] : Nontrivial α ↔ ex
ists x y : α, x < y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans_le'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b < a
 → c ≤ b → c < a
· 使用定理 `WithBot.coe_unbot`：∀ {α : Type u_1} (x : WithBot α) (hx : x ≠ ⊥), ↑(x.un
bot hx) = x
· 使用引理 `WithBot.coe_lt_coe`：coe_lt_coe : (a : WithBot α) < b ↔ a < b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Subtype.coe_lt_coe`：coe_lt_coe [LT α] {p : α -> Prop} {x y : Subtype p} 
: (x : α) < y ↔ x < y
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用引理 `denselyOrdered_set_iff_subsingleton`：denselyOrdered_set_iff_subsingleton
 {s : Set X} : DenselyOrdered s ↔ s.Subsingleton
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Set.Subsingleton.denselyOrdered`：∀ {α : Type u} {s : Set α} [inst : LT α
], s.Subsingleton → DenselyOrdered ↑s
-/
lemma WithBot.denselyOrdered_set_iff_subsingleton {s : Set (WithBot X)} :
    DenselyOrdered s ↔ s.Subsingleton := by
  refine ⟨fun H ↦ ?_, fun h ↦ h.denselyOrdered⟩
  rw [← Set.subsingleton_coe, ← not_nontrivial_iff_subsingleton, nontrivial_iff_lt]
  suffices DenselyOrdered (WithBot.some ⁻¹' s) by
    rintro ⟨x, y, H⟩
    rw [_root_.denselyOrdered_set_iff_subsingleton] at this
    obtain ⟨z, hz, hz'⟩ := exists_between H
    have hz0 : (⊥ : WithBot X) < z := by simp [(Subtype.coe_lt_coe.mpr hz).trans_le']
    replace hz' : WithBot.unbot z.val hz0.ne' < WithBot.unbot y (hz0.trans hz').ne' := by
      rwa [← WithBot.coe_lt_coe, WithBot.coe_unbot, WithBot.coe_unbot]
    refine absurd (this ?_ ?_) hz'.ne <;>
    simp
  constructor
  simp only [Subtype.exists, Set.mem_preimage, Subtype.forall, Subtype.mk_lt_mk, exists_and_right,
    exists_prop]
  intro x hx y hy hxy
  have : (⟨_, hx⟩ : s) < ⟨_, hy⟩ := by simp [hxy]
  obtain ⟨z, hz, hz'⟩ := exists_between this
  simp only [← Subtype.coe_lt_coe] at hz hz'
  refine ⟨WithBot.unbot z (hz.trans_le' (by simp)).ne', ⟨?_, ?_⟩, ?_⟩
  · simp
  · rw [← WithBot.coe_lt_coe]
    simp [hz.trans_le]
  · rw [← WithBot.coe_lt_coe]
    simp [hz'.trans_le']
/-
**WithTop.denselyOrdered_set_iff_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：WithTop.denselyOrdered_set_iff_subsingleton {s : Set (WithTop X)} : Densel
yOrdered s ↔ s.Subsingleton
参数：WithTop X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Equiv.image_strictAnti`：image_strictAnti (hs : StrictAnti e) : StrictAnt
i (e.image s)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `denselyOrdered_iff_of_strictAnti`：denselyOrdered_iff_of_strictAnti {X Y 
F : Type*} [LinearOrder X] [Preorder Y] [EquivLike F X Y] (f : F) (hf : StrictAn
ti f) : DenselyOrdered…
· 使用引理 `WithBot.denselyOrdered_set_iff_subsingleton`：WithBot.denselyOrdered_set_
iff_subsingleton {s : Set (WithBot X)} : DenselyOrdered s ↔ s.Subsingleton
· 使用定理 `Function.Injective.subsingleton_image_iff`：∀ {α : Type u_1} {β : Type u_
2} {f : α → β},   Function.Injective f → ∀ {s : Set α}, (f '' s).Subsingleton ↔ 
s.Subsingleton
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma WithTop.denselyOrdered_set_iff_subsingleton {s : Set (WithTop X)} :
    DenselyOrdered s ↔ s.Subsingleton := by
  have he : StrictAnti (WithTop.toDual.image s) :=
    WithTop.toDual.image_strictAnti _ (fun ⦃a b⦄ a ↦ a)
  rw [denselyOrdered_iff_of_strictAnti _ he, WithBot.denselyOrdered_set_iff_subsingleton,
    WithTop.toDual.injective.subsingleton_image_iff]
