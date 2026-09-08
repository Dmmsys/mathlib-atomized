/-
Copyright (c) 2024 Ching-Tsun Chou, Chris Wong, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou, Chris Wong, Yaël Dillies
-/
module

public import Mathlib.Data.Finset.Density
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Nat.Choose.Cast

/-!
# The Katona circle method

This file provides tooling to use the Katona circle method, which is double-counting ways to order
`n` elements on a circle under some condition.
-/

@[expose] public section

open Fintype Finset Nat

variable {X : Type*} [Fintype X]

variable (X) in
/-- A numbering of a fintype `X` is a bijection between `X` and `Fin (card X)`. -/
/-
**Numbering** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Numbering : Type _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A numbering of a fintype `X` is a bijection between `X` and `Fin (card X)`.
-/
abbrev Numbering : Type _ := X ≃ Fin (card X)
/-
**Fintype.card_numbering** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：∀ {X : Type u_1} [inst : Fintype X] [inst_1 : DecidableEq X], Fintype.card
 (Numbering X) = (Fintype.card X).factorial
参数：Numbering X；Fintype.card X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.card_equiv`：Fintype.card_equiv [Fintype α] [Fintype β] (e : α ≃ 
β) : Fintype.card (α ≃ β) = (Fintype.card α)!
-/
@[simp] lemma Fintype.card_numbering [DecidableEq X] : card (Numbering X) = (card X)! :=
  card_equiv (equivFin _)

namespace Numbering
variable {f : Numbering X} {s t : Finset X}

/-- `IsPrefix f s` means that the elements of `s` precede the elements of `sᶜ`
in the numbering `f`. -/
/-
**Numbering.IsPrefix** 是 Mathlib 中的一个定义，位于命名空间 `Numbering`。
形式化陈述：IsPrefix (f : Numbering X) (s : Finset X)
参数：f : Numbering X；s : Finset X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsPrefix f s` means that the elements of `s` precede the elements of `sᶜ`
in the numbering `f`.
-/
def IsPrefix (f : Numbering X) (s : Finset X) := ∀ x, x ∈ s ↔ f x < #s
/-
**Numbering.IsPrefix.subset_of_card_le_card** 是 Mathlib 中的一个定理，位于命名空间 `Numbering
.IsPrefix`。
形式化陈述：∀ {X : Type u_1} [inst : Fintype X] {f : Numbering X} {s t : Finset X},   
f.IsPrefix s → f.IsPrefix t → s.card ≤ t.card → s ⊆ t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
lemma IsPrefix.subset_of_card_le_card (hs : IsPrefix f s) (ht : IsPrefix f t) (hst : #s ≤ #t) :
    s ⊆ t := fun a ha ↦ (ht a).mpr <| ((hs a).mp ha).trans_le hst

variable [DecidableEq X]
/-
**Numbering.** 是 Mathlib 中的一个实例，位于命名空间 `Numbering`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Decidable (IsPrefix f s) := inferInstanceAs <| Decidable (∀ _, _)

/-- The set of numberings of which `s` is a prefix. -/
/-
**Numbering.prefixed** 是 Mathlib 中的一个定义，位于命名空间 `Numbering`。
形式化陈述：prefixed (s : Finset X) : Finset (Numbering X)
参数：s : Finset X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of numberings of which `s` is a prefix.
-/
def prefixed (s : Finset X) : Finset (Numbering X) := {f | IsPrefix f s}
/-
**Numbering.mem_prefixed** 是 Mathlib 中的一个定理，位于命名空间 `Numbering`。
形式化陈述：∀ {X : Type u_1} [inst : Fintype X] {f : Numbering X} {s : Finset X} [inst
_1 : DecidableEq X],   f ∈ Numbering.prefixed s ↔ f.IsPrefix s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma mem_prefixed : f ∈ prefixed s ↔ IsPrefix f s := by simp [prefixed]

set_option backward.isDefEq.respectTransparency false in
/-- Decompose a numbering of which `s` is a prefix into a numbering of `s` and a numbering on `sᶜ`.
-/
/-
**Numbering.prefixedEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Numbering`。
形式化陈述：prefixedEquiv (s : Finset X) : prefixed s ≃ Numbering s × Numbering ↑(sᶜ) 
where toFun f
参数：s : Finset X。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Decompose a numbering of which `s` is a prefix into a numbering of `s` and a num
bering on `sᶜ`.
-/
def prefixedEquiv (s : Finset X) : prefixed s ≃ Numbering s × Numbering ↑(sᶜ) where
  toFun f :=
    { fst.toFun x := ⟨f.1 x, by simp [← mem_prefixed.1 f.2 x]⟩
      fst.invFun n :=
        ⟨f.1.symm ⟨n, n.2.trans_le <| by simpa using s.card_le_univ⟩, by
          rw [mem_prefixed.1 f.2]; simpa using n.2⟩
      fst.left_inv x := by simp
      fst.right_inv n := by simp
      snd.toFun x := ⟨f.1 x - #s, by
        have := (mem_prefixed.1 f.2 x).not.1 (Finset.mem_compl.1 x.2)
        simp at this ⊢
        omega⟩
      snd.invFun n :=
        ⟨f.1.symm ⟨n + #s, Nat.add_lt_of_lt_sub <| by simpa using n.2⟩, by
          rw [s.mem_compl, mem_prefixed.1 f.2]; simp⟩
      snd.left_inv := by
        rintro ⟨x, hx⟩
        rw [s.mem_compl, mem_prefixed.1 f.2, not_lt] at hx
        simp [Nat.sub_add_cancel hx]
      snd.right_inv := by rintro ⟨n, hn⟩; simp }
  invFun := fun (g, g') ↦
    { val.toFun x :=
        if hx : x ∈ s then
          g ⟨x, hx⟩ |>.castLE (Fintype.card_subtype_le _)
        else
          g' ⟨x, by simpa⟩ |>.addNat #s |>.cast (by simp [card_le_univ])
      val.invFun n :=
        if hn : n < #s then
          g.symm ⟨n, by simpa using hn⟩
        else
          g'.symm ⟨n - #s, by simp; omega⟩
      val.left_inv x := by
        by_cases hx : x ∈ s
        · have : g ⟨x, hx⟩ < #s := by simpa using (g ⟨x, hx⟩).2
          simp [hx, this]
        · simp [hx]
      val.right_inv n := by
        obtain hns | hsn := lt_or_ge n.1 #s
        · simp [hns]
        · simp [hsn.not_gt, hsn, mem_compl.1 <| Subtype.prop _]
      property := mem_prefixed.2 fun x ↦ by
        constructor
        · intro hx
          simpa [hx, -Fin.is_lt] using (g _).is_lt
        · by_cases hx : x ∈ s <;> simp [hx] }
  left_inv f := by
    ext x
    by_cases hx : x ∈ s
    · simp [hx]
    · rw [mem_prefixed.1 f.2, not_lt] at hx
      simp [hx]
  right_inv g := by simp +contextual [Prod.ext_iff, DFunLike.ext_iff]
/-
**Numbering.card_prefixed** 是 Mathlib 中的一个引理，位于命名空间 `Numbering`。
形式化陈述：card_prefixed (s : Finset X) : #(prefixed s) = (#s)! * (card X - #s)!
参数：s : Finset X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_coe`：Fintype.card_coe (s : Finset α) [Fintype s] : Fintype.
card s = #s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Fintype.card_prod`：Fintype.card_prod (α β : Type*) [Fintype α] [Fintype 
β] : Fintype.card (α × β) = Fintype.card α * Fintype.card β
· 使用定理 `Fintype.card_numbering`：∀ {X : Type u_1} [inst : Fintype X] [inst_1 : De
cidableEq X], Fintype.card (Numbering X) = (Fintype.card X).factorial
· 使用定理 `Fintype.card_congr'`：card_congr' {α β} [Fintype α] [Fintype β] (h : α = 
β) : card α = card β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fintype.card_subtype_compl`：Fintype.card_subtype_compl [Fintype α] (p : 
α -> Prop) [Fintype { x // p x }] [Fintype { x // ¬p x }] : Fintype.card { x // 
¬p x } = Fintype…
· 使用定理 `Fintype.card_congr`：card_congr {α β} [Fintype α] [Fintype β] (f : α ≃ β)
 : card α = card β
-/
lemma card_prefixed (s : Finset X) : #(prefixed s) = (#s)! * (card X - #s)! := by
  simpa [-mem_prefixed] using Fintype.card_congr (prefixedEquiv s)

@[simp]
/-
**Numbering.dens_prefixed** 是 Mathlib 中的一个引理，位于命名空间 `Numbering`。
形式化陈述：dens_prefixed (s : Finset X) : (prefixed s).dens = ((card X).choose #s : R
at>=0)⁻¹
参数：s : Finset X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Numbering.card_prefixed`：card_prefixed (s : Finset X) : #(prefixed s) = 
(#s)! * (card X - #s)!
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Fintype.card_numbering`：∀ {X : Type u_1} [inst : Fintype X] [inst_1 : De
cidableEq X], Fintype.card (Numbering X) = (Fintype.card X).factorial
· 使用定理 `Nat.cast_choose`：cast_choose {a b : Nat} (h : a <= b) : (b.choose a : K)
 = b ! / (a ! * (b - a)!)
· 使用定理 `Finset.card_le_univ`：Finset.card_le_univ [Fintype α] (s : Finset α) : #s
 <= Fintype.card α
· 使用定理 `inv_div`：inv_div : (a / b)⁻¹ = b / a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma dens_prefixed (s : Finset X) : (prefixed s).dens = ((card X).choose #s : ℚ≥0)⁻¹ := by
  simp [dens, card_prefixed, Nat.cast_choose _ s.card_le_univ]

-- TODO: This can be strengthened to an iff
/-
**Numbering.disjoint_prefixed_prefixed** 是 Mathlib 中的一个引理，位于命名空间 `Numbering`。
形式化陈述：disjoint_prefixed_prefixed (hst : ¬ s subseteq t) (hts : ¬ t subseteq s) :
 Disjoint (prefixed s) (prefixed t)
参数：hst : ¬ s subseteq t；hts : ¬ t subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.le_total`：∀ (m n : ℕ), m ≤ n ∨ n ≤ m
· 使用定理 `Numbering.IsPrefix.subset_of_card_le_card`：∀ {X : Type u_1} [inst : Fint
ype X] {f : Numbering X} {s t : Finset X},   f.IsPrefix s → f.IsPrefix t → s.car
d ≤ t.card → s ⊆ t
-/
lemma disjoint_prefixed_prefixed (hst : ¬ s ⊆ t) (hts : ¬ t ⊆ s) :
    Disjoint (prefixed s) (prefixed t) := by
  simp only [Finset.disjoint_left, mem_prefixed]
  intro f hs ht
  obtain hst' | hts' := Nat.le_total #s #t
  · exact hst <| hs.subset_of_card_le_card ht hst'
  · exact hts <| ht.subset_of_card_le_card hs hts'

end Numbering

