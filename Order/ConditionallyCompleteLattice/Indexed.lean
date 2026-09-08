/-
Copyright (c) 2018 Sébastian Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastian Gouëzel
-/
module

public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompletePartialOrder.Indexed

/-!
# Indexed sup / inf in conditionally complete lattices

This file proves lemmas about `iSup` and `iInf` for functions valued in a conditionally complete,
rather than complete, lattice. We add a prefix `c` to distinguish them from the versions for
complete lattices, giving names `ciSup_xxx` or `ciInf_xxx`.
-/

public section

-- Guard against import creep
assert_not_exists Multiset

open Function OrderDual Set

variable {α β γ : Type*} {ι : Sort*}

section

/-!
Extension of `iSup` and `iInf` from a preorder `α` to `WithTop α` and `WithBot α`
-/

variable [Preorder α]

@[simp]
/-
**WithTop.iInf_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WithTop.iInf_empty [IsEmpty ι] [InfSet α] (f : ι -> WithTop α) : ⨅ i, f i 
= ⊤
参数：f : ι -> WithTop α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iInf.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : InfSet α] (s : ι → α), iI
nf s = sInf (Set.range s)
· 使用定理 `Set.range_eq_empty`：range_eq_empty [IsEmpty ι] (f : ι -> α) : range f = 
∅
· 使用定理 `WithTop.sInf_empty`：sInf_empty [InfSet α] : sInf (∅ : Set (WithTop α)) =
 ⊤
-/
theorem WithTop.iInf_empty [IsEmpty ι] [InfSet α] (f : ι → WithTop α) :
    ⨅ i, f i = ⊤ := by rw [iInf, range_eq_empty, WithTop.sInf_empty]

@[norm_cast]
/-
**WithTop.coe_iInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WithTop.coe_iInf [Nonempty ι] [InfSet α] {f : ι -> α} (hf : BddBelow (rang
e f)) : ↑(⨅ i, f i) = (⨅ i, f i : WithTop α)
参数：hf : BddBelow (range f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iInf.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : InfSet α] (s : ι → α), iI
nf s = sInf (Set.range s)
· 使用定理 `WithTop.coe_sInf'`：WithTop.coe_sInf' [InfSet α] {s : Set α} (hs : s.None
mpty) (h's : BddBelow s) : ↑(sInf s) = (sInf ((fun (a : α) => ↑a) '' s) : WithTo
p α)
· 使用定理 `Set.range_nonempty`：range_nonempty [h : Nonempty ι] (f : ι -> α) : (rang
e f).Nonempty
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
-/
theorem WithTop.coe_iInf [Nonempty ι] [InfSet α] {f : ι → α} (hf : BddBelow (range f)) :
    ↑(⨅ i, f i) = (⨅ i, f i : WithTop α) := by
  rw [iInf, iInf, WithTop.coe_sInf' (range_nonempty f) hf, ← range_comp, Function.comp_def]

@[norm_cast]
/-
**WithTop.coe_iSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WithTop.coe_iSup [SupSet α] (f : ι -> α) (h : BddAbove (Set.range f)) : ↑(
⨆ i, f i) = (⨆ i, f i : WithTop α)
参数：f : ι -> α；h : BddAbove (Set.range f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : SupSet α] (s : ι → α), iS
up s = sSup (Set.range s)
· 使用定理 `WithTop.coe_sSup'`：coe_sSup' [SupSet α] {s : Set α} (hs : BddAbove s) : 
↑(sSup s) = (sSup ((fun (a : α) => ↑a) '' s) : WithTop α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
-/
theorem WithTop.coe_iSup [SupSet α] (f : ι → α) (h : BddAbove (Set.range f)) :
    ↑(⨆ i, f i) = (⨆ i, f i : WithTop α) := by
  rw [iSup, iSup, WithTop.coe_sSup' h, ← range_comp, Function.comp_def]

@[simp]
/-
**WithBot.ciSup_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WithBot.ciSup_empty [IsEmpty ι] [SupSet α] (f : ι -> WithBot α) : ⨆ i, f i
 = ⊥
参数：f : ι -> WithBot α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.iInf_empty`：WithTop.iInf_empty [IsEmpty ι] [InfSet α] (f : ι -> 
WithTop α) : ⨅ i, f i = ⊤
-/
theorem WithBot.ciSup_empty [IsEmpty ι] [SupSet α] (f : ι → WithBot α) :
    ⨆ i, f i = ⊥ :=
  WithTop.iInf_empty (α := αᵒᵈ) _

@[norm_cast]
/-
**WithBot.coe_iSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WithBot.coe_iSup [Nonempty ι] [SupSet α] {f : ι -> α} (hf : BddAbove (rang
e f)) : ↑(⨆ i, f i) = (⨆ i, f i : WithBot α)
参数：hf : BddAbove (range f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.coe_iInf`：WithTop.coe_iInf [Nonempty ι] [InfSet α] {f : ι -> α} 
(hf : BddBelow (range f)) : ↑(⨅ i, f i) = (⨅ i, f i : WithTop α)
-/
theorem WithBot.coe_iSup [Nonempty ι] [SupSet α] {f : ι → α} (hf : BddAbove (range f)) :
    ↑(⨆ i, f i) = (⨆ i, f i : WithBot α) :=
  WithTop.coe_iInf (α := αᵒᵈ) hf
/-
**WithBot.coe_biSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WithBot.coe_biSup {ι : Type*} {s : Set ι} (hs : s.Nonempty) {α : Type*} [C
ompleteLattice α] (f : ι -> α) : ⨆ i in s, f i = ⨆ i in s, (f i : WithBot α)
参数：hs : s.Nonempty；f : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `WithBot.coe_iSup`：WithBot.coe_iSup [Nonempty ι] [SupSet α] {f : ι -> α} 
(hf : BddAbove (range f)) : ↑(⨆ i, f i) = (⨆ i, f i : WithBot α)
· 使用定理 `OrderTop.bddAbove`：∀ {α : Type u_1} [inst : Preorder α] [OrderTop α] (s 
: Set α), BddAbove s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `iSup_le_iff`：iSup_le_iff : iSup f <= a ↔ forall i, f i <= a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_pos`：iSup_pos {p : Prop} {f : p -> α} (hp : p) : ⨆ h : p, f h = f h
p
· 使用引理 `le_biSup`：le_biSup {ι : Type*} {s : Set ι} (f : ι -> α) {i : ι} (hi : i 
in s) : f i <= ⨆ i in s, f i
· 使用定理 `iSup_neg`：iSup_neg {p : Prop} {f : p -> α} (hp : ¬p) : ⨆ h : p, f h = ⊥
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `WithBot.coe_le_coe`：coe_le_coe : (a : WithBot α) <= b ↔ a <= b
-/
theorem WithBot.coe_biSup {ι : Type*} {s : Set ι} (hs : s.Nonempty)
    {α : Type*} [CompleteLattice α] (f : ι → α) :
    ⨆ i ∈ s, f i = ⨆ i ∈ s, (f i : WithBot α) := by
  rcases hs with ⟨j, hj⟩
  have : Nonempty ι := Nonempty.intro j
  refine le_antisymm ((WithBot.coe_iSup (OrderTop.bddAbove _)).trans_le <|
    iSup_le_iff.mpr fun i ↦ ?_) <| iSup_le_iff.mpr <| fun _ ↦ iSup_le_iff.mpr <|
      fun hi ↦ WithBot.coe_le_coe.mpr (le_biSup _ hi)
  by_cases h : i ∈ s
  · simpa only [iSup_pos h] using by apply le_biSup _ h
  · simpa only [iSup_neg h] using le_trans (by simp) (le_biSup _ hj)

@[norm_cast]
/-
**WithBot.coe_iInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WithBot.coe_iInf [InfSet α] (f : ι -> α) (h : BddBelow (Set.range f)) : ↑(
⨅ i, f i) = (⨅ i, f i : WithBot α)
参数：f : ι -> α；h : BddBelow (Set.range f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.coe_iSup`：WithTop.coe_iSup [SupSet α] (f : ι -> α) (h : BddAbove
 (Set.range f)) : ↑(⨆ i, f i) = (⨆ i, f i : WithTop α)
-/
theorem WithBot.coe_iInf [InfSet α] (f : ι → α) (h : BddBelow (Set.range f)) :
    ↑(⨅ i, f i) = (⨅ i, f i : WithBot α) :=
  WithTop.coe_iSup (α := αᵒᵈ) _ h
/-
**WithBot.coe_biInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WithBot.coe_biInf {ι : Type*} {s : Set ι} {α : Type*} [CompleteLattice α] 
(f : ι -> α) : ⨅ i in s, f i = ⨅ i in s, (f i : WithBot α)
参数：f : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `biInf_le`：∀ {α : Type u_1} [inst : CompleteLattice α] {ι : Type u_8} {s 
: Set ι} (f : ι → α) {i : ι}, i ∈ s → ⨅ i ∈ s, f i ≤ f i
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `le_iInf_iff`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] 
{f : ι → α} {a : α}, a ≤ iInf f ↔ ∀ (i : ι), a ≤ f i
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iInf_pos`：∀ {α : Type u_1} [inst : CompleteLattice α] {p : Prop} {f : p 
→ α} (hp : p), ⨅ (h : p), f h = f hp
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iInf_neg`：∀ {α : Type u_1} [inst : CompleteLattice α] {p : Prop} {f : p 
→ α}, ¬p → ⨅ (h : p), f h = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithBot.coe_iInf`：WithBot.coe_iInf [InfSet α] (f : ι -> α) (h : BddBelow
 (Set.range f)) : ↑(⨅ i, f i) = (⨅ i, f i : WithBot α)
· 使用定理 `OrderBot.bddBelow`：∀ {α : Type u_1} [inst : Preorder α] [OrderBot α] (s 
: Set α), BddBelow s
-/
theorem WithBot.coe_biInf {ι : Type*} {s : Set ι} {α : Type*} [CompleteLattice α] (f : ι → α) :
    ⨅ i ∈ s, f i = ⨅ i ∈ s, (f i : WithBot α) := by
  refine le_antisymm (by simpa using fun _ ↦ biInf_le _) <|
    (le_iInf_iff.mpr fun i ↦ ?_).trans_eq (WithBot.coe_iInf _ (OrderBot.bddBelow _)).symm
  by_cases h : i ∈ s
  · simpa only [iInf_pos h] using by apply biInf_le _ h
  · simp [iInf_neg h]

end

section ConditionallyCompleteLattice

variable [ConditionallyCompleteLattice α] {a b : α}

/-
**isLUB_ciSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLUB_ciSup [Nonempty ι] {f : ι -> α} (H : BddAbove (range f)) : IsLUB (ra
nge f) (⨆ i, f i)
参数：H : BddAbove (range f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isLUB_csSup`：isLUB_csSup (hn : s.Nonempty) (hb : BddAbove s
· 使用定理 `Set.range_nonempty`：range_nonempty [h : Nonempty ι] (f : ι -> α) : (rang
e f).Nonempty
-/
theorem isLUB_ciSup [Nonempty ι] {f : ι → α} (H : BddAbove (range f)) :
    IsLUB (range f) (⨆ i, f i) :=
  isLUB_csSup (range_nonempty f) H
/-
**isLUB_ciSup_set** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLUB_ciSup_set {f : β -> α} {s : Set β} (H : BddAbove (f '' s)) (Hne : s.
Nonempty) : IsLUB (f '' s) (⨆ i : s, f i)
参数：H : BddAbove (f '' s)；Hne : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sSup_image'`：sSup_image' {s : Set β} {f : β -> α} : sSup (f '' s) = ⨆ a 
: s, f a
· 使用定理 `isLUB_csSup`：isLUB_csSup (hn : s.Nonempty) (hb : BddAbove s
· 使用定理 `Set.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set
 α}, s.Nonempty → (f '' s).Nonempty
-/
theorem isLUB_ciSup_set {f : β → α} {s : Set β} (H : BddAbove (f '' s)) (Hne : s.Nonempty) :
    IsLUB (f '' s) (⨆ i : s, f i) := by
  rw [← sSup_image']
  exact isLUB_csSup (Hne.image _) H
/-
**isGLB_ciInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isGLB_ciInf [Nonempty ι] {f : ι -> α} (H : BddBelow (range f)) : IsGLB (ra
nge f) (⨅ i, f i)
参数：H : BddBelow (range f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isGLB_csInf`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s
 : Set α},   s.Nonempty → autoParam (BddBelow s) isGLB_csInf._auto_1 → IsGLB s (
s…
· 使用定理 `Set.range_nonempty`：range_nonempty [h : Nonempty ι] (f : ι -> α) : (rang
e f).Nonempty
-/
theorem isGLB_ciInf [Nonempty ι] {f : ι → α} (H : BddBelow (range f)) :
    IsGLB (range f) (⨅ i, f i) :=
  isGLB_csInf (range_nonempty f) H
/-
**isGLB_ciInf_set** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isGLB_ciInf_set {f : β -> α} {s : Set β} (H : BddBelow (f '' s)) (Hne : s.
Nonempty) : IsGLB (f '' s) (⨅ i : s, f i)
参数：H : BddBelow (f '' s)；Hne : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isLUB_ciSup_set`：isLUB_ciSup_set {f : β -> α} {s : Set β} (H : BddAbove 
(f '' s)) (Hne : s.Nonempty) : IsLUB (f '' s) (⨆ i : s, f i)
-/
theorem isGLB_ciInf_set {f : β → α} {s : Set β} (H : BddBelow (f '' s)) (Hne : s.Nonempty) :
    IsGLB (f '' s) (⨅ i : s, f i) :=
  isLUB_ciSup_set (α := αᵒᵈ) H Hne
/-
**ciSup_le_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ciSup_le_iff [Nonempty ι] {f : ι -> α} {a : α} (hf : BddAbove (range f)) :
 iSup f <= a ↔ forall i, f i <= a
参数：hf : BddAbove (range f)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `isLUB_le_iff`：isLUB_le_iff (h : IsLUB s a) : a <= b ↔ b in upperBounds s
· 使用定理 `isLUB_ciSup`：isLUB_ciSup [Nonempty ι] {f : ι -> α} (H : BddAbove (range 
f)) : IsLUB (range f) (⨆ i, f i)
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
-/
theorem ciSup_le_iff [Nonempty ι] {f : ι → α} {a : α} (hf : BddAbove (range f)) :
    iSup f ≤ a ↔ ∀ i, f i ≤ a :=
  (isLUB_le_iff <| isLUB_ciSup hf).trans forall_mem_range
/-
**le_ciInf_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_ciInf_iff [Nonempty ι] {f : ι -> α} {a : α} (hf : BddBelow (range f)) :
 a <= iInf f ↔ forall i, a <= f i
参数：hf : BddBelow (range f)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `le_isGLB_iff`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α} {a b : α}
, IsGLB s a → (b ≤ a ↔ b ∈ lowerBounds s)
· 使用定理 `isGLB_ciInf`：isGLB_ciInf [Nonempty ι] {f : ι -> α} (H : BddBelow (range 
f)) : IsGLB (range f) (⨅ i, f i)
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
-/
theorem le_ciInf_iff [Nonempty ι] {f : ι → α} {a : α} (hf : BddBelow (range f)) :
    a ≤ iInf f ↔ ∀ i, a ≤ f i :=
  (le_isGLB_iff <| isGLB_ciInf hf).trans forall_mem_range
/-
**ciSup_set_le_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ciSup_set_le_iff {ι : Type*} {s : Set ι} {f : ι -> α} {a : α} (hs : s.None
mpty) (hf : BddAbove (f '' s)) : ⨆ i : s, f i <= a ↔ forall i in s, f i <= a
参数：hs : s.Nonempty；hf : BddAbove (f '' s)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `isLUB_le_iff`：isLUB_le_iff (h : IsLUB s a) : a <= b ↔ b in upperBounds s
· 使用定理 `isLUB_ciSup_set`：isLUB_ciSup_set {f : β -> α} {s : Set β} (H : BddAbove 
(f '' s)) (Hne : s.Nonempty) : IsLUB (f '' s) (⨆ i : s, f i)
· 使用定理 `Set.forall_mem_image`：forall_mem_image {f : α -> β} {s : Set α} {p : β -
> Prop} : (forall y in f '' s, p y) ↔ forall ⦃x⦄, x in s -> p (f x)
-/
theorem ciSup_set_le_iff {ι : Type*} {s : Set ι} {f : ι → α} {a : α} (hs : s.Nonempty)
    (hf : BddAbove (f '' s)) : ⨆ i : s, f i ≤ a ↔ ∀ i ∈ s, f i ≤ a :=
  (isLUB_le_iff <| isLUB_ciSup_set hf hs).trans forall_mem_image
/-
**le_ciInf_set_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_ciInf_set_iff {ι : Type*} {s : Set ι} {f : ι -> α} {a : α} (hs : s.None
mpty) (hf : BddBelow (f '' s)) : (a <= ⨅ i : s, f i) ↔ forall i in s, a <= f i
参数：hs : s.Nonempty；hf : BddBelow (f '' s)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `le_isGLB_iff`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α} {a b : α}
, IsGLB s a → (b ≤ a ↔ b ∈ lowerBounds s)
· 使用定理 `isGLB_ciInf_set`：isGLB_ciInf_set {f : β -> α} {s : Set β} (H : BddBelow 
(f '' s)) (Hne : s.Nonempty) : IsGLB (f '' s) (⨅ i : s, f i)
· 使用定理 `Set.forall_mem_image`：forall_mem_image {f : α -> β} {s : Set α} {p : β -
> Prop} : (forall y in f '' s, p y) ↔ forall ⦃x⦄, x in s -> p (f x)
-/
theorem le_ciInf_set_iff {ι : Type*} {s : Set ι} {f : ι → α} {a : α} (hs : s.Nonempty)
    (hf : BddBelow (f '' s)) : (a ≤ ⨅ i : s, f i) ↔ ∀ i ∈ s, a ≤ f i :=
  (le_isGLB_iff <| isGLB_ciInf_set hf hs).trans forall_mem_image
/-
**IsLUB.ciSup_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLUB.ciSup_eq [Nonempty ι] {f : ι -> α} (H : IsLUB (range f) a) : ⨆ i, f 
i = a
参数：H : IsLUB (range f) a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLUB.csSup_eq`：IsLUB.csSup_eq (H : IsLUB s a) (ne : s.Nonempty) : sSup 
s = a
· 使用定理 `Set.range_nonempty`：range_nonempty [h : Nonempty ι] (f : ι -> α) : (rang
e f).Nonempty
-/
theorem IsLUB.ciSup_eq [Nonempty ι] {f : ι → α} (H : IsLUB (range f) a) : ⨆ i, f i = a :=
  H.csSup_eq (range_nonempty f)
/-
**IsLUB.ciSup_set_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLUB.ciSup_set_eq {s : Set β} {f : β -> α} (H : IsLUB (f '' s) a) (Hne : 
s.Nonempty) : ⨆ i : s, f i = a
参数：H : IsLUB (f '' s) a；Hne : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLUB.csSup_eq`：IsLUB.csSup_eq (H : IsLUB s a) (ne : s.Nonempty) : sSup 
s = a
· 使用定理 `Set.image_eq_range`：image_eq_range (f : α -> β) (s : Set α) : f '' s = r
ange fun x : s => f x
· 使用定理 `Set.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set
 α}, s.Nonempty → (f '' s).Nonempty
-/
theorem IsLUB.ciSup_set_eq {s : Set β} {f : β → α} (H : IsLUB (f '' s) a) (Hne : s.Nonempty) :
    ⨆ i : s, f i = a :=
  IsLUB.csSup_eq (image_eq_range f s ▸ H) (image_eq_range f s ▸ Hne.image f)
/-
**IsGLB.ciInf_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsGLB.ciInf_eq [Nonempty ι] {f : ι -> α} (H : IsGLB (range f) a) : ⨅ i, f 
i = a
参数：H : IsGLB (range f) a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGLB.csInf_eq`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α]
 {s : Set α} {a : α}, IsGLB s a → s.Nonempty → sInf s = a
· 使用定理 `Set.range_nonempty`：range_nonempty [h : Nonempty ι] (f : ι -> α) : (rang
e f).Nonempty
-/
theorem IsGLB.ciInf_eq [Nonempty ι] {f : ι → α} (H : IsGLB (range f) a) : ⨅ i, f i = a :=
  H.csInf_eq (range_nonempty f)
/-
**IsGLB.ciInf_set_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsGLB.ciInf_set_eq {s : Set β} {f : β -> α} (H : IsGLB (f '' s) a) (Hne : 
s.Nonempty) : ⨅ i : s, f i = a
参数：H : IsGLB (f '' s) a；Hne : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGLB.csInf_eq`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α]
 {s : Set α} {a : α}, IsGLB s a → s.Nonempty → sInf s = a
· 使用定理 `Set.image_eq_range`：image_eq_range (f : α -> β) (s : Set α) : f '' s = r
ange fun x : s => f x
· 使用定理 `Set.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set
 α}, s.Nonempty → (f '' s).Nonempty
-/
theorem IsGLB.ciInf_set_eq {s : Set β} {f : β → α} (H : IsGLB (f '' s) a) (Hne : s.Nonempty) :
    ⨅ i : s, f i = a :=
  IsGLB.csInf_eq (image_eq_range f s ▸ H) (image_eq_range f s ▸ Hne.image f)

/-- The indexed supremum of a function is bounded above by a uniform bound -/
/-
**ciSup_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ciSup_le [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, f x <= c) : iSup
 f <= c
参数：H : forall x, f x <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `csSup_le`：csSup_le (h₁ : s.Nonempty) (h₂ : forall b in s, b <= a) : sSup
 s <= a
· 使用定理 `Set.range_nonempty`：range_nonempty [h : Nonempty ι] (f : ι -> α) : (rang
e f).Nonempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)

--- 原说明 ---
The indexed supremum of a function is bounded above by a uniform bound
-/
theorem ciSup_le [Nonempty ι] {f : ι → α} {c : α} (H : ∀ x, f x ≤ c) : iSup f ≤ c :=
  csSup_le (range_nonempty f) (by rwa [forall_mem_range])

/-- The indexed supremum of a function is bounded below by the value taken at one point -/
/-
**le_ciSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_ciSup {f : ι -> α} (H : BddAbove (range f)) (c : ι) : f c <= iSup f
参数：H : BddAbove (range f)；c : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_csSup`：le_csSup (h₁ : BddAbove s) (h₂ : a in s) : a <= sSup s
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f

--- 原说明 ---
The indexed supremum of a function is bounded below by the value taken at one po
int
-/
theorem le_ciSup {f : ι → α} (H : BddAbove (range f)) (c : ι) : f c ≤ iSup f :=
  le_csSup H (mem_range_self _)
/-
**le_ciSup_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_ciSup_of_le {f : ι -> α} (H : BddAbove (range f)) (c : ι) (h : a <= f c
) : a <= iSup f
参数：H : BddAbove (range f)；c : ι；h : a <= f c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_ciSup`：le_ciSup {f : ι -> α} (H : BddAbove (range f)) (c : ι) : f c <
= iSup f
-/
theorem le_ciSup_of_le {f : ι → α} (H : BddAbove (range f)) (c : ι) (h : a ≤ f c) : a ≤ iSup f :=
  le_trans h (le_ciSup H c)

/-- If the set of all `f i j` is bounded above, then so is the set of the supremums of every row -/
/-
**BddAbove.range_iSup_of_iUnion_range** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：BddAbove.range_iSup_of_iUnion_range {κ : ι -> Sort*} {f : forall i, κ i ->
 α} (H : BddAbove <| ⋃ i, range (f i)) : BddAbove range fun i => ⨆ j, f i j
参数：H : BddAbove <| ⋃ i, range (f i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `iSup_of_empty'`：iSup_of_empty' {α ι} [SupSet α] [IsEmpty ι] (f : ι -> α)
 : iSup f = sSup (∅ : Set α)
· 使用定理 `ciSup_le`：ciSup_le [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, f x 
<= c) : iSup f <= c
· 使用定理 `le_sup_of_le_left`：le_sup_of_le_left (h : c <= a) : c <= a ⊔ b

--- 原说明 ---
If the set of all `f i j` is bounded above, then so is the set of the supremums 
of every row
-/
theorem BddAbove.range_iSup_of_iUnion_range {κ : ι → Sort*} {f : ∀ i, κ i → α}
    (H : BddAbove <| ⋃ i, range (f i)) : BddAbove <| range fun i ↦ ⨆ j, f i j := by
  have ⟨a, h⟩ := H
  refine ⟨a ⊔ (sSup ∅), fun x ⟨i, hx⟩ ↦ hx ▸ ?_⟩
  cases isEmpty_or_nonempty <| κ i
  · exact iSup_of_empty' (f i) ▸ le_sup_right
  exact ciSup_le fun j ↦ le_sup_of_le_left <| h ⟨_, ⟨i, rfl⟩, ⟨j, rfl⟩⟩
/-
**le_ciSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_ciSup {f : ι -> α} (H : BddAbove (range f)) (c : ι) : f c <= iSup f
参数：H : BddAbove (range f)；c : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_csSup`：le_csSup (h₁ : BddAbove s) (h₂ : a in s) : a <= sSup s
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
-/
theorem le_ciSup₂ {κ : ι → Sort*} {f : ∀ i, κ i → α} (H : BddAbove <| ⋃ i, range (f i)) (i : ι)
    (j : κ i) : f i j ≤ ⨆ (i) (j), f i j :=
  le_ciSup_of_le H.range_iSup_of_iUnion_range i <|
    le_ciSup (H.mono <| subset_iUnion (range <| f ·) i) j

/-- The indexed suprema of two functions are comparable if the functions are pointwise comparable -/
@[gcongr low]
/-
**ciSup_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ciSup_mono {f g : ι -> α} (B : BddAbove (range g)) (H : forall x, f x <= g
 x) : iSup f <= iSup g
参数：B : BddAbove (range g)；H : forall x, f x <= g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_of_empty'`：iSup_of_empty' {α ι} [SupSet α] [IsEmpty ι] (f : ι -> α)
 : iSup f = sSup (∅ : Set α)
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `ciSup_le`：ciSup_le [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, f x 
<= c) : iSup f <= c
· 使用定理 `le_ciSup_of_le`：le_ciSup_of_le {f : ι -> α} (H : BddAbove (range f)) (c 
: ι) (h : a <= f c) : a <= iSup f

--- 原说明 ---
The indexed suprema of two functions are comparable if the functions are pointwi
se comparable
-/
theorem ciSup_mono {f g : ι → α} (B : BddAbove (range g)) (H : ∀ x, f x ≤ g x) :
    iSup f ≤ iSup g := by
  cases isEmpty_or_nonempty ι
  · rw [iSup_of_empty', iSup_of_empty']
  · exact ciSup_le fun x => le_ciSup_of_le B x (H x)
/-
**ciSup_sup_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ciSup_sup_eq {f g : ι -> α} (Hf : BddAbove <| range f) (Hg : BddAbove <| r
ange g) : ⨆ x, f x ⊔ g x = (⨆ x, f x) ⊔ (⨆ x, g x)
参数：Hf : BddAbove <| range f；Hg : BddAbove <| range g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_of_empty'`：iSup_of_empty' {α ι} [SupSet α] [IsEmpty ι] (f : ι -> α)
 : iSup f = sSup (∅ : Set α)
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `ciSup_le`：ciSup_le [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, f x 
<= c) : iSup f <= c
· 使用定理 `sup_le_sup`：sup_le_sup (h₁ : a <= b) (h₂ : c <= d) : a ⊔ c <= b ⊔ d
· 使用定理 `le_ciSup`：le_ciSup {f : ι -> α} (H : BddAbove (range f)) (c : ι) : f c <
= iSup f
· 使用定理 `bbdAbove_range_sup`：bbdAbove_range_sup {ι : Sort*} {α : Type*} [Semilatt
iceSup α] {f g : ι -> α} (hf : BddAbove <| range f) (hg : BddAbove <| range g) :
 BddAbov…
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `ciSup_mono`：ciSup_mono {f g : ι -> α} (B : BddAbove (range g)) (H : fora
ll x, f x <= g x) : iSup f <= iSup g
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
theorem ciSup_sup_eq {f g : ι → α} (Hf : BddAbove <| range f) (Hg : BddAbove <| range g) :
    ⨆ x, f x ⊔ g x = (⨆ x, f x) ⊔ (⨆ x, g x) := by
  cases isEmpty_or_nonempty ι
  · simp [iSup_of_empty']
  apply le_antisymm <| ciSup_le fun x ↦ sup_le_sup (le_ciSup Hf x) (le_ciSup Hg x)
  have := bbdAbove_range_sup Hf Hg
  exact sup_le (ciSup_mono this fun _ ↦ le_sup_left) (ciSup_mono this fun _ ↦ le_sup_right)
/-
**le_ciSup_set** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_ciSup_set {f : β -> α} {s : Set β} (H : BddAbove (f '' s)) {c : β} (hc 
: c in s) : f c <= ⨆ i : s, f i
参数：H : BddAbove (f '' s)；hc : c in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `le_csSup`：le_csSup (h₁ : BddAbove s) (h₂ : a in s) : a <= sSup s
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `sSup_image'`：sSup_image' {s : Set β} {f : β -> α} : sSup (f '' s) = ⨆ a 
: s, f a
-/
theorem le_ciSup_set {f : β → α} {s : Set β} (H : BddAbove (f '' s)) {c : β} (hc : c ∈ s) :
    f c ≤ ⨆ i : s, f i :=
  (le_csSup H <| mem_image_of_mem f hc).trans_eq sSup_image'

/-- The indexed infimum of two functions are comparable if the functions are pointwise comparable -/
@[gcongr low]
/-
**ciInf_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ciInf_mono {f g : ι -> α} (B : BddBelow (range f)) (H : forall x, f x <= g
 x) : iInf f <= iInf g
参数：B : BddBelow (range f)；H : forall x, f x <= g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ciSup_mono`：ciSup_mono {f g : ι -> α} (B : BddAbove (range g)) (H : fora
ll x, f x <= g x) : iSup f <= iSup g

--- 原说明 ---
The indexed infimum of two functions are comparable if the functions are pointwi
se comparable
-/
theorem ciInf_mono {f g : ι → α} (B : BddBelow (range f)) (H : ∀ x, f x ≤ g x) : iInf f ≤ iInf g :=
  ciSup_mono (α := αᵒᵈ) B H
/-
**ciInf_inf_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ciInf_inf_eq {f g : ι -> α} (Hf : BddBelow <| range f) (Hg : BddBelow <| r
ange g) : ⨅ x, f x ⊓ g x = (⨅ x, f x) ⊓ (⨅ x, g x)
参数：Hf : BddBelow <| range f；Hg : BddBelow <| range g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ciSup_sup_eq`：ciSup_sup_eq {f g : ι -> α} (Hf : BddAbove <| range f) (Hg
 : BddAbove <| range g) : ⨆ x, f x ⊔ g x = (⨆ x, f x) ⊔ (⨆ x, g x)
-/
theorem ciInf_inf_eq {f g : ι → α} (Hf : BddBelow <| range f) (Hg : BddBelow <| range g) :
    ⨅ x, f x ⊓ g x = (⨅ x, f x) ⊓ (⨅ x, g x) :=
  ciSup_sup_eq (α := αᵒᵈ) Hf Hg

/-- The indexed minimum of a function is bounded below by a uniform lower bound -/
/-
**le_ciInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_ciInf [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, c <= f x) : c <=
 iInf f
参数：H : forall x, c <= f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ciSup_le`：ciSup_le [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, f x 
<= c) : iSup f <= c

--- 原说明 ---
The indexed minimum of a function is bounded below by a uniform lower bound
-/
theorem le_ciInf [Nonempty ι] {f : ι → α} {c : α} (H : ∀ x, c ≤ f x) : c ≤ iInf f :=
  ciSup_le (α := αᵒᵈ) H

/-- The indexed infimum of a function is bounded above by the value taken at one point -/
/-
**ciInf_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ciInf_le {f : ι -> α} (H : BddBelow (range f)) (c : ι) : iInf f <= f c
参数：H : BddBelow (range f)；c : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_ciSup`：le_ciSup {f : ι -> α} (H : BddAbove (range f)) (c : ι) : f c <
= iSup f

--- 原说明 ---
The indexed infimum of a function is bounded above by the value taken at one poi
nt
-/
theorem ciInf_le {f : ι → α} (H : BddBelow (range f)) (c : ι) : iInf f ≤ f c :=
  le_ciSup (α := αᵒᵈ) H c
/-
**ciInf_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ciInf_le_of_le {f : ι -> α} (H : BddBelow (range f)) (c : ι) (h : f c <= a
) : iInf f <= a
参数：H : BddBelow (range f)；c : ι；h : f c <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_ciSup_of_le`：le_ciSup_of_le {f : ι -> α} (H : BddAbove (range f)) (c 
: ι) (h : a <= f c) : a <= iSup f
-/
theorem ciInf_le_of_le {f : ι → α} (H : BddBelow (range f)) (c : ι) (h : f c ≤ a) : iInf f ≤ a :=
  le_ciSup_of_le (α := αᵒᵈ) H c h
/-
**ciSup_mono_of_forall_exists** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ciSup_mono_of_forall_exists {ι'} [Nonempty ι] {f : ι -> α} {g : ι' -> α} (
hg : BddAbove <| range g) (h : forall i, exists i', f i <= g i') : ⨆ i, f i <= ⨆
 i', g i'
参数：hg : BddAbove <| range g；h : forall i, exists i', f i <= g i'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ciSup_le`：ciSup_le [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, f x 
<= c) : iSup f <= c
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `le_ciSup_of_le`：le_ciSup_of_le {f : ι -> α} (H : BddAbove (range f)) (c 
: ι) (h : a <= f c) : a <= iSup f
-/
theorem ciSup_mono_of_forall_exists {ι'} [Nonempty ι] {f : ι → α} {g : ι' → α}
    (hg : BddAbove <| range g) (h : ∀ i, ∃ i', f i ≤ g i') : ⨆ i, f i ≤ ⨆ i', g i' :=
  ciSup_le fun i ↦ h i |>.elim <| le_ciSup_of_le hg
/-
**ciInf_mono_of_forall_exists** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ciInf_mono_of_forall_exists {ι'} [Nonempty ι'] {f : ι -> α} {g : ι' -> α} 
(hf : BddBelow <| range f) (h : forall i', exists i, f i <= g i') : ⨅ i, f i <= 
⨅ i', g i'
参数：hf : BddBelow <| range f；h : forall i', exists i, f i <= g i'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ciSup_mono_of_forall_exists`：ciSup_mono_of_forall_exists {ι'} [Nonempty 
ι] {f : ι -> α} {g : ι' -> α} (hg : BddAbove <| range g) (h : forall i, exists i
', f i <= g i') :…
-/
theorem ciInf_mono_of_forall_exists {ι'} [Nonempty ι'] {f : ι → α} {g : ι' → α}
    (hf : BddBelow <| range f) (h : ∀ i', ∃ i, f i ≤ g i') : ⨅ i, f i ≤ ⨅ i', g i' :=
  ciSup_mono_of_forall_exists (α := αᵒᵈ) hf h

/-- If the set of all `f i j` is bounded below, then so is the set of the infimums of every row -/
/-
**BddBelow.range_iInf_of_iUnion_range** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：BddBelow.range_iInf_of_iUnion_range {κ : ι -> Sort*} {f : forall i, κ i ->
 α} (H : BddBelow <| ⋃ i, range (f i)) : BddBelow range fun i => ⨅ j, f i j
参数：H : BddBelow <| ⋃ i, range (f i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `iInf_of_isEmpty`：∀ {α : Type u_8} {ι : Sort u_9} [inst : InfSet α] [IsEm
pty ι] (f : ι → α), iInf f = sInf ∅
· 使用定理 `le_ciInf`：le_ciInf [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, c <=
 f x) : c <= iInf f
· 使用定理 `inf_le_of_left_le`：∀ {α : Type u} [inst : SemilatticeInf α] {a b c : α},
 a ≤ c → a ⊓ b ≤ c

--- 原说明 ---
If the set of all `f i j` is bounded below, then so is the set of the infimums o
f every row
-/
theorem BddBelow.range_iInf_of_iUnion_range {κ : ι → Sort*} {f : ∀ i, κ i → α}
    (H : BddBelow <| ⋃ i, range (f i)) : BddBelow <| range fun i ↦ ⨅ j, f i j := by
  have ⟨a, h⟩ := H
  refine ⟨a ⊓ (sInf ∅), fun x ⟨i, hx⟩ ↦ hx ▸ ?_⟩
  cases isEmpty_or_nonempty <| κ i
  · exact iInf_of_isEmpty (f i) ▸ inf_le_right
  exact le_ciInf fun j ↦ inf_le_of_left_le <| h ⟨_, ⟨i, rfl⟩, ⟨j, rfl⟩⟩
/-
**ciInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ciInf₂_le {κ : ι → Sort*} {f : ∀ i, κ i → α} (H : BddBelow <| ⋃ i, range (f i)) (i : ι)
    (j : κ i) : ⨅ (i) (j), f i j ≤ f i j :=
  ciInf_le_of_le H.range_iInf_of_iUnion_range i <|
    ciInf_le (H.mono <| subset_iUnion (range <| f ·) i) j
/-
**ciInf_set_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ciInf_set_le {f : β -> α} {s : Set β} (H : BddBelow (f '' s)) {c : β} (hc 
: c in s) : ⨅ i : s, f i <= f c
参数：H : BddBelow (f '' s)；hc : c in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_ciSup_set`：le_ciSup_set {f : β -> α} {s : Set β} (H : BddAbove (f '' 
s)) {c : β} (hc : c in s) : f c <= ⨆ i : s, f i
-/
theorem ciInf_set_le {f : β → α} {s : Set β} (H : BddBelow (f '' s)) {c : β} (hc : c ∈ s) :
    ⨅ i : s, f i ≤ f c :=
  le_ciSup_set (α := αᵒᵈ) H hc
/-
**ciInf_le_ciSup** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ciInf_le_ciSup [Nonempty ι] {f : ι -> α} (hf : BddBelow (range f)) (hf' : 
BddAbove (range f)) : ⨅ i, f i <= ⨆ i, f i
参数：hf : BddBelow (range f)；hf' : BddAbove (range f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `ciInf_le`：ciInf_le {f : ι -> α} (H : BddBelow (range f)) (c : ι) : iInf 
f <= f c
· 使用定理 `le_ciSup`：le_ciSup {f : ι -> α} (H : BddAbove (range f)) (c : ι) : f c <
= iSup f
-/
lemma ciInf_le_ciSup [Nonempty ι] {f : ι → α} (hf : BddBelow (range f)) (hf' : BddAbove (range f)) :
    ⨅ i, f i ≤ ⨆ i, f i :=
  (ciInf_le hf (Classical.arbitrary _)).trans <| le_ciSup hf' (Classical.arbitrary _)
/-
**ciSup_prod** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ciSup_prod {f : β × γ -> α} (hf : BddAbove (Set.range f)) : ⨆ p, f p = ⨆ b
, ⨆ c, f (b, c)
参数：hf : BddAbove (Set.range f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_of_empty'`：iSup_of_empty' {α ι} [SupSet α] [IsEmpty ι] (f : ι -> α)
 : iSup f = sSup (∅ : Set α)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ciSup_const`：ciSup_const [hι : Nonempty ι] {a : α} : ⨆ _ : ι, a = a
· 使用定理 `bddAbove_def`：bddAbove_def : BddAbove s ↔ exists x, forall y in s, y <= 
x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_range`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} {x : α}, x ∈ Se
t.range f ↔ ∃ y, f y = x
· 使用定理 `ciSup_le`：ciSup_le [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, f x 
<= c) : iSup f <= c
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用定理 `ciSup_le_iff`：ciSup_le_iff [Nonempty ι] {f : ι -> α} {a : α} (hf : BddAb
ove (range f)) : iSup f <= a ↔ forall i, f i <= a
· 使用定理 `instNonemptyProd`：∀ {α : Type u_1} {β : Type u_2} [h1 : Nonempty α] [h2 
: Nonempty β], Nonempty (α × β)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `bddAbove_iff_subset_Iic`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α
}, BddAbove s ↔ ∃ a, s ⊆ Set.Iic a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma ciSup_prod {f : β × γ → α} (hf : BddAbove (Set.range f)) :
    ⨆ p, f p = ⨆ b, ⨆ c, f (b, c) := by
  rcases isEmpty_or_nonempty β
  · simp [iSup_of_empty']
  rcases isEmpty_or_nonempty γ
  · simp [iSup_of_empty']
  have h₁ : BddAbove (Set.range fun b ↦ ⨆ c, f (b, c)) := by
    rw [bddAbove_def] at hf ⊢
    obtain ⟨B, hB⟩ := hf
    refine ⟨B, fun y hy ↦ ?_⟩
    obtain ⟨z, rfl⟩ := Set.mem_range.mp hy
    exact ciSup_le fun c ↦ by grind
  have h₂ b : BddAbove (Set.range fun c ↦ f (b, c)) := by
    rw [bddAbove_def] at hf ⊢
    obtain ⟨B, hB⟩ := hf
    exact ⟨B, by grind⟩
  refine eq_of_forall_ge_iff fun c ↦ ?_
  rw [ciSup_le_iff (bddAbove_iff_subset_Iic.mpr hf), ciSup_le_iff h₁]
  conv_rhs => enter [b]; rw [ciSup_le_iff (h₂ b)]
  simp [Prod.forall]
/-
**ciInf_prod** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ciInf_prod {f : β × γ -> α} (hf : BddBelow (Set.range f)) : ⨅ p, f p = ⨅ b
, ⨅ c, f (b, c)
参数：hf : BddBelow (Set.range f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ciSup_prod`：ciSup_prod {f : β × γ -> α} (hf : BddAbove (Set.range f)) : 
⨆ p, f p = ⨆ b, ⨆ c, f (b, c)
-/
lemma ciInf_prod {f : β × γ → α} (hf : BddBelow (Set.range f)) :
    ⨅ p, f p = ⨅ b, ⨅ c, f (b, c) :=
  ciSup_prod (α := αᵒᵈ) hf

/-- Introduction rule to prove that `b` is the supremum of `f`: it suffices to check that `b`
is larger than `f i` for all `i`, and that this is not the case of any `w<b`.
See `iSup_eq_of_forall_le_of_forall_lt_exists_gt` for a version in complete lattices. -/
/-
**ciSup_eq_of_forall_le_of_forall_lt_exists_gt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ciSup_eq_of_forall_le_of_forall_lt_exists_gt [Nonempty ι] {f : ι -> α} (h₁
 : forall i, f i <= b) (h₂ : forall w, w < b -> exists i, w < f i) : ⨆ i : ι, f 
i = b
参数：h₁ : forall i, f i <= b；h₂ : forall w, w < b -> exists i, w < f i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `csSup_eq_of_forall_le_of_forall_lt_exists_gt`：csSup_eq_of_forall_le_of_f
orall_lt_exists_gt (hs : s.Nonempty) (H : forall a in s, a <= b) (H' : forall w,
 w < b -> exists a in s, w < a) : …
· 使用定理 `Set.range_nonempty`：range_nonempty [h : Nonempty ι] (f : ι -> α) : (rang
e f).Nonempty
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
· 使用定理 `Set.exists_range_iff`：exists_range_iff {p : α -> Prop} : (exists a in ra
nge f, p a) ↔ exists i, p (f i)

--- 原说明 ---
Introduction rule to prove that `b` is the supremum of `f`: it suffices to check
 that `b`
is larger than `f i` for all `i`, and that this is not the case of any `w<b`.
See `iSup_eq_of_forall_le_of_forall_lt_exists_gt` for a version in complete latt
ices.
-/
theorem ciSup_eq_of_forall_le_of_forall_lt_exists_gt [Nonempty ι] {f : ι → α} (h₁ : ∀ i, f i ≤ b)
    (h₂ : ∀ w, w < b → ∃ i, w < f i) : ⨆ i : ι, f i = b :=
  csSup_eq_of_forall_le_of_forall_lt_exists_gt (range_nonempty f) (forall_mem_range.mpr h₁)
    fun w hw => exists_range_iff.mpr <| h₂ w hw

/-- Introduction rule to prove that `b` is the infimum of `f`: it suffices to check that `b`
is smaller than `f i` for all `i`, and that this is not the case of any `w>b`.
See `iInf_eq_of_forall_ge_of_forall_gt_exists_lt` for a version in complete lattices. -/
/-
**ciInf_eq_of_forall_ge_of_forall_gt_exists_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ciInf_eq_of_forall_ge_of_forall_gt_exists_lt [Nonempty ι] {f : ι -> α} (h₁
 : forall i, b <= f i) (h₂ : forall w, b < w -> exists i, f i < w) : ⨅ i : ι, f 
i = b
参数：h₁ : forall i, b <= f i；h₂ : forall w, b < w -> exists i, f i < w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ciSup_eq_of_forall_le_of_forall_lt_exists_gt`：ciSup_eq_of_forall_le_of_f
orall_lt_exists_gt [Nonempty ι] {f : ι -> α} (h₁ : forall i, f i <= b) (h₂ : for
all w, w < b -> exists i, w < f i)…

--- 原说明 ---
Introduction rule to prove that `b` is the infimum of `f`: it suffices to check 
that `b`
is smaller than `f i` for all `i`, and that this is not the case of any `w>b`.
See `iInf_eq_of_forall_ge_of_forall_gt_exists_lt` for a version in complete latt
ices.
-/
theorem ciInf_eq_of_forall_ge_of_forall_gt_exists_lt [Nonempty ι] {f : ι → α} (h₁ : ∀ i, b ≤ f i)
    (h₂ : ∀ w, b < w → ∃ i, f i < w) : ⨅ i : ι, f i = b :=
  ciSup_eq_of_forall_le_of_forall_lt_exists_gt (α := αᵒᵈ) h₁ h₂
/-
**Set.Iic_ciInf** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Set.Iic_ciInf [Nonempty ι] {f : ι -> α} (hf : BddBelow (range f)) : Iic (⨅
 i, f i) = ⋂ i, Iic (f i)
参数：hf : BddBelow (range f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `le_ciInf_iff`：le_ciInf_iff [Nonempty ι] {f : ι -> α} {a : α} (hf : BddBe
low (range f)) : a <= iInf f ↔ forall i, a <= f i
-/
lemma Set.Iic_ciInf [Nonempty ι] {f : ι → α} (hf : BddBelow (range f)) :
    Iic (⨅ i, f i) = ⋂ i, Iic (f i) := by
  ext
  simpa using le_ciInf_iff hf
/-
**Set.Ici_ciSup** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Set.Ici_ciSup [Nonempty ι] {f : ι -> α} (hf : BddAbove (range f)) : Ici (⨆
 i, f i) = ⋂ i, Ici (f i)
参数：hf : BddAbove (range f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.Iic_ciInf`：Set.Iic_ciInf [Nonempty ι] {f : ι -> α} (hf : BddBelow (r
ange f)) : Iic (⨅ i, f i) = ⋂ i, Iic (f i)
-/
lemma Set.Ici_ciSup [Nonempty ι] {f : ι → α} (hf : BddAbove (range f)) :
    Ici (⨆ i, f i) = ⋂ i, Ici (f i) :=
  Iic_ciInf (α := αᵒᵈ) hf
/-
**ciSup_subtype** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ciSup_subtype {p : ι -> Prop} {f : Subtype p -> α} (hf : BddAbove (Set.ran
ge f)) (hf' : sSup ∅ <= iSup f) : iSup f = ⨆ (i) (h : p i), f ⟨i, h⟩
参数：hf : BddAbove (Set.range f)；hf' : sSup ∅ <= iSup f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_of_empty'`：iSup_of_empty' {α ι} [SupSet α] [IsEmpty ι] (f : ι -> α)
 : iSup f = sSup (∅ : Set α)
· 使用引理 `cbiSup_eq_of_forall_not`：cbiSup_eq_of_forall_not {p : ι -> Prop} {f : fo
rall i, p i -> α} (hp : forall i, ¬p i) : ⨆ (i) (h : p i), f i h = sSup ∅
· 使用定理 `Exists.nonempty`：∀ {α : Sort u_1} {p : α → Prop}, (∃ x, p x) → Nonempty 
α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `nonempty_subtype`：nonempty_subtype {α} {p : α -> Prop} : Nonempty (Subty
pe p) ↔ exists a : α, p a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `ciSup_le`：ciSup_le [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, f x 
<= c) : iSup f <= c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `ciSup_unique`：ciSup_unique [Unique ι] {s : ι -> α} : ⨆ i, s i = s defaul
t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `le_ciSup`：le_ciSup {f : ι -> α} (H : BddAbove (range f)) (c : ι) : f c <
= iSup f
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `ciSup_eq_ite`：ciSup_eq_ite {p : Prop} [Decidable p] {f : p -> α} : (⨆ h 
: p, f h) = if h : p then f h else sSup (∅ : Set α)
· 使用定理 `BddAbove.mono`：BddAbove.mono ⦃s t : Set α⦄ (h : s subseteq t) : BddAbove
 t -> BddAbove s
· 使用定理 `BddAbove.union`：BddAbove.union [IsDirectedOrder α] {s t : Set α} : BddAb
ove s -> BddAbove t -> BddAbove (s union t)
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用引理 `bddAbove_singleton`：bddAbove_singleton : BddAbove ({a} : Set α)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem ciSup_subtype {p : ι → Prop} {f : Subtype p → α}
    (hf : BddAbove (Set.range f)) (hf' : sSup ∅ ≤ iSup f) :
    iSup f = ⨆ (i) (h : p i), f ⟨i, h⟩ := by
  cases isEmpty_or_nonempty (Subtype p)
  · rw [iSup_of_empty', cbiSup_eq_of_forall_not fun i h ↦ isEmptyElim (⟨i, h⟩ : Subtype p)]
  have : Nonempty ι := (nonempty_subtype.mp ‹_›).nonempty
  classical
  refine le_antisymm (ciSup_le ?_) ?_
  · intro ⟨i, h⟩
    have : f ⟨i, h⟩ = (fun i : ι ↦ ⨆ (h : p i), f ⟨i, h⟩) i := by simp [h]
    rw [this]
    refine le_ciSup (f := (fun i : ι ↦ ⨆ (h : p i), f ⟨i, h⟩)) ?_ i
    simp_rw [ciSup_eq_ite]
    refine (hf.union (bddAbove_singleton (a := sSup ∅))).mono ?_
    grind
  · refine ciSup_le fun i ↦ ?_
    simp_rw [ciSup_eq_ite]
    split_ifs
    · exact le_ciSup hf ?_
    · exact hf'
/-
**ciInf_subtype** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ciInf_subtype {p : ι -> Prop} {f : Subtype p -> α} (hf : BddBelow (Set.ran
ge f)) (hf' : iInf f <= sInf ∅) : iInf f = ⨅ (i) (h : p i), f ⟨i, h⟩
参数：hf : BddBelow (Set.range f)；hf' : iInf f <= sInf ∅。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ciSup_subtype`：ciSup_subtype {p : ι -> Prop} {f : Subtype p -> α} (hf : 
BddAbove (Set.range f)) (hf' : sSup ∅ <= iSup f) : iSup f = ⨆ (i) (h : p i), f ⟨
i, …
-/
theorem ciInf_subtype {p : ι → Prop} {f : Subtype p → α}
    (hf : BddBelow (Set.range f)) (hf' : iInf f ≤ sInf ∅) :
    iInf f = ⨅ (i) (h : p i), f ⟨i, h⟩ :=
  ciSup_subtype (α := αᵒᵈ) hf hf'
/-
**cbiSup_eq_ciSup_subtype** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cbiSup_eq_ciSup_subtype {p : ι -> Prop} {f : forall i, p i -> α} (hf : Bdd
Above (Set.range (fun i : Subtype p => f i i.prop))) (hf' : sSup ∅ <= ⨆ (i : Sub
type p), f i i.prop) : ⨆ (i) (h), f i h = ⨆ x : Subtype p, f x x.property
参数：hf : BddAbove (Set.range (fun i : Subtype p => f i i.prop))；hf' : sSup ∅ <= ⨆
 (i : Subtype p), f i i.prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `ciSup_subtype`：ciSup_subtype {p : ι -> Prop} {f : Subtype p -> α} (hf : 
BddAbove (Set.range f)) (hf' : sSup ∅ <= iSup f) : iSup f = ⨆ (i) (h : p i), f ⟨
i, …
-/
theorem cbiSup_eq_ciSup_subtype {p : ι → Prop} {f : ∀ i, p i → α}
    (hf : BddAbove (Set.range (fun i : Subtype p ↦ f i i.prop)))
    (hf' : sSup ∅ ≤ ⨆ (i : Subtype p), f i i.prop) :
    ⨆ (i) (h), f i h = ⨆ x : Subtype p, f x x.property :=
  (ciSup_subtype (f := fun x => f x.val x.property) hf hf').symm

@[deprecated (since := "2026-04-04")] alias ciSup_subtype' := cbiSup_eq_ciSup_subtype
/-
**cbiInf_eq_ciInf_subtype** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cbiInf_eq_ciInf_subtype {p : ι -> Prop} {f : forall i, p i -> α} (hf : Bdd
Below (Set.range (fun i : Subtype p => f i i.prop))) (hf' : ⨅ (i : Subtype p), f
 i i.prop <= sInf ∅) : ⨅ (i) (h), f i h = ⨅ x : Subtype p, f x x.property
参数：hf : BddBelow (Set.range (fun i : Subtype p => f i i.prop))；hf' : ⨅ (i : Subt
ype p), f i i.prop <= sInf ∅。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `ciInf_subtype`：ciInf_subtype {p : ι -> Prop} {f : Subtype p -> α} (hf : 
BddBelow (Set.range f)) (hf' : iInf f <= sInf ∅) : iInf f = ⨅ (i) (h : p i), f ⟨
i, …
-/
theorem cbiInf_eq_ciInf_subtype {p : ι → Prop} {f : ∀ i, p i → α}
    (hf : BddBelow (Set.range (fun i : Subtype p ↦ f i i.prop)))
    (hf' : ⨅ (i : Subtype p), f i i.prop ≤ sInf ∅) :
    ⨅ (i) (h), f i h = ⨅ x : Subtype p, f x x.property :=
  (ciInf_subtype (f := fun x => f x.val x.property) hf hf').symm

@[deprecated (since := "2026-04-04")] alias ciInf_subtype' := cbiInf_eq_ciInf_subtype
/-
**ciSup_subtype_fun** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ciSup_subtype_fun {ι} {s : Set ι} {f : ι -> α} (hf : BddAbove (Set.range f
un i : s => f i)) (hf' : sSup ∅ <= ⨆ i : s, f i) : ⨆ i : s, f i = ⨆ (t : ι) (_ :
 t in s), f t
参数：hf : BddAbove (Set.range fun i : s => f i)；hf' : sSup ∅ <= ⨆ i : s, f i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ciSup_subtype`：ciSup_subtype {p : ι -> Prop} {f : Subtype p -> α} (hf : 
BddAbove (Set.range f)) (hf' : sSup ∅ <= iSup f) : iSup f = ⨆ (i) (h : p i), f ⟨
i, …
-/
theorem ciSup_subtype_fun {ι} {s : Set ι} {f : ι → α}
    (hf : BddAbove (Set.range fun i : s ↦ f i)) (hf' : sSup ∅ ≤ ⨆ i : s, f i) :
    ⨆ i : s, f i = ⨆ (t : ι) (_ : t ∈ s), f t :=
  ciSup_subtype hf hf'

@[deprecated (since := "2026-04-04")] alias ciSup_subtype'' := ciSup_subtype_fun
/-
**ciInf_subtype_fun** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ciInf_subtype_fun {ι} {s : Set ι} {f : ι -> α} (hf : BddBelow (Set.range f
un i : s => f i)) (hf' : ⨅ i : s, f i <= sInf ∅) : ⨅ i : s, f i = ⨅ (t : ι) (_ :
 t in s), f t
参数：hf : BddBelow (Set.range fun i : s => f i)；hf' : ⨅ i : s, f i <= sInf ∅。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ciInf_subtype`：ciInf_subtype {p : ι -> Prop} {f : Subtype p -> α} (hf : 
BddBelow (Set.range f)) (hf' : iInf f <= sInf ∅) : iInf f = ⨅ (i) (h : p i), f ⟨
i, …
-/
theorem ciInf_subtype_fun {ι} {s : Set ι} {f : ι → α}
    (hf : BddBelow (Set.range fun i : s ↦ f i)) (hf' : ⨅ i : s, f i ≤ sInf ∅) :
    ⨅ i : s, f i = ⨅ (t : ι) (_ : t ∈ s), f t :=
  ciInf_subtype hf hf'

@[deprecated (since := "2026-04-04")] alias ciInf_subtype'' := ciInf_subtype_fun
/-
**csSup_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：csSup_image {s : Set β} {f : β -> α} (hf : BddAbove (Set.range fun i : s =
> f i)) (hf' : sSup ∅ <= ⨆ i : s, f i) : sSup (f '' s) = ⨆ a in s, f a
参数：hf : BddAbove (Set.range fun i : s => f i)；hf' : sSup ∅ <= ⨆ i : s, f i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ciSup_subtype_fun`：ciSup_subtype_fun {ι} {s : Set ι} {f : ι -> α} (hf : 
BddAbove (Set.range fun i : s => f i)) (hf' : sSup ∅ <= ⨆ i : s, f i) : ⨆ i : s,
 f i = …
· 使用定理 `iSup.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : SupSet α] (s : ι → α), iS
up s = sSup (Set.range s)
· 使用定理 `Set.image_eq_range`：image_eq_range (f : α -> β) (s : Set α) : f '' s = r
ange fun x : s => f x
-/
theorem csSup_image {s : Set β} {f : β → α}
    (hf : BddAbove (Set.range fun i : s ↦ f i)) (hf' : sSup ∅ ≤ ⨆ i : s, f i) :
    sSup (f '' s) = ⨆ a ∈ s, f a := by
  rw [← ciSup_subtype_fun hf hf', iSup, Set.image_eq_range]
/-
**csInf_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：csInf_image {s : Set β} {f : β -> α} (hf : BddBelow (Set.range fun i : s =
> f i)) (hf' : ⨅ i : s, f i <= sInf ∅) : sInf (f '' s) = ⨅ a in s, f a
参数：hf : BddBelow (Set.range fun i : s => f i)；hf' : ⨅ i : s, f i <= sInf ∅。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `csSup_image`：csSup_image {s : Set β} {f : β -> α} (hf : BddAbove (Set.ra
nge fun i : s => f i)) (hf' : sSup ∅ <= ⨆ i : s, f i) : sSup (f '' s) = ⨆ a in s
,…
-/
theorem csInf_image {s : Set β} {f : β → α}
    (hf : BddBelow (Set.range fun i : s ↦ f i)) (hf' : ⨅ i : s, f i ≤ sInf ∅) :
    sInf (f '' s) = ⨅ a ∈ s, f a :=
  csSup_image (α := αᵒᵈ) hf hf'
/-
**cbiSup_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cbiSup_id {s : Set α} (hs : BddAbove s) (h : sSup ∅ <= sSup s) : ⨆ i in s,
 i = sSup s
参数：hs : BddAbove s；h : sSup ∅ <= sSup s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `csSup_image`：csSup_image {s : Set β} {f : β -> α} (hf : BddAbove (Set.ra
nge fun i : s => f i)) (hf' : sSup ∅ <= ⨆ i : s, f i) : sSup (f '' s) = ⨆ a in s
,…
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `sSup_range`：sSup_range : sSup (range f) = iSup f
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s
-/
theorem cbiSup_id {s : Set α} (hs : BddAbove s) (h : sSup ∅ ≤ sSup s) : ⨆ i ∈ s, i = sSup s := by
  rw [← csSup_image (Subtype.range_coe ▸ hs), Set.image_id']
  · convert! h
    rw [← sSup_range, Subtype.range_coe]
/-
**cbiInf_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cbiInf_id {s : Set α} (hs : BddBelow s) (h : sInf s <= sInf ∅) : ⨅ i in s,
 i = sInf s
参数：hs : BddBelow s；h : sInf s <= sInf ∅。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `csInf_image`：csInf_image {s : Set β} {f : β -> α} (hf : BddBelow (Set.ra
nge fun i : s => f i)) (hf' : ⨅ i : s, f i <= sInf ∅) : sInf (f '' s) = ⨅ a in s
,…
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `sInf_range`：∀ {α : Type u_1} {ι : Sort u_4} [inst : InfSet α] {f : ι → α
}, sInf (Set.range f) = iInf f
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s
-/
theorem cbiInf_id {s : Set α} (hs : BddBelow s) (h : sInf s ≤ sInf ∅) : ⨅ i ∈ s, i = sInf s := by
  rw [← csInf_image (Subtype.range_coe ▸ hs), Set.image_id']
  · convert! h
    rw [← sInf_range, Subtype.range_coe]
/-
**ciSup_image** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ciSup_image {ι ι' : Type*} {s : Set ι} {f : ι -> ι'} {g : ι' -> α} (hf : B
ddAbove (Set.range fun i : s => g (f i))) (hg' : sSup ∅ <= ⨆ i : s, g (f i)) : ⨆
 i in (f '' s), g i = ⨆ x in s, g (f x)
参数：hf : BddAbove (Set.range fun i : s => g (f i))；hg' : sSup ∅ <= ⨆ i : s, g (f 
i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_empty`：image_empty (f : α -> β) : f '' ∅ = ∅
· 使用定理 `cbiSup_empty`：cbiSup_empty {f : β -> α} : ⨆ i in (∅ : Set β), f i = sSup
 ∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.Nonempty.to_subtype`：∀ {α : Type u} {s : Set α}, s.Nonempty → Nonemp
ty ↑s
· 使用定理 `ciSup_le`：ciSup_le [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, f x 
<= c) : iSup f <= c
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `le_ciSup_set`：le_ciSup_set {f : β -> α} {s : Set β} (H : BddAbove (f '' 
s)) {c : β} (hc : c in s) : f c <= ⨆ i : s, f i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `csSup_image`：csSup_image {s : Set β} {f : β -> α} (hf : BddAbove (Set.ra
nge fun i : s => f i)) (hf' : sSup ∅ <= ⨆ i : s, f i) : sSup (f '' s) = ⨆ a in s
,…
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
-/
lemma ciSup_image {ι ι' : Type*} {s : Set ι} {f : ι → ι'} {g : ι' → α}
    (hf : BddAbove (Set.range fun i : s ↦ g (f i))) (hg' : sSup ∅ ≤ ⨆ i : s, g (f i)) :
    ⨆ i ∈ (f '' s), g i = ⨆ x ∈ s, g (f x) := by
  rcases s.eq_empty_or_nonempty with (rfl | hs)
  · rw [Set.image_empty, cbiSup_empty, cbiSup_empty]
  have hg : BddAbove (Set.range fun i : f '' s ↦ g i) := by
    simpa [bddAbove_def] using hf
  have hf' : sSup ∅ ≤ ⨆ i : f '' s, g i := by
    refine hg'.trans ?_
    have : Nonempty s := Set.Nonempty.to_subtype hs
    refine ciSup_le ?_
    intro ⟨i, h⟩
    obtain ⟨t, ht⟩ : ∃ t : f '' s, g t = g (f (Subtype.mk i h)) := by
      have : f i ∈ f '' s := Set.mem_image_of_mem _ h
      exact ⟨⟨f i, this⟩, by simp⟩
    rw [← ht]
    refine le_ciSup_set ?_ t.prop
    simpa [bddAbove_def] using hf
  rw [← csSup_image hg hf', ← csSup_image hf hg', ← Set.image_comp, comp_def]
/-
**ciInf_image** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ciInf_image {ι ι' : Type*} {s : Set ι} {f : ι -> ι'} {g : ι' -> α} (hf : B
ddBelow (Set.range fun i : s => g (f i))) (hg' : ⨅ i : s, g (f i) <= sInf ∅) : ⨅
 i in (f '' s), g i = ⨅ x in s, g (f x)
参数：hf : BddBelow (Set.range fun i : s => g (f i))；hg' : ⨅ i : s, g (f i) <= sInf
 ∅。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ciSup_image`：ciSup_image {ι ι' : Type*} {s : Set ι} {f : ι -> ι'} {g : ι
' -> α} (hf : BddAbove (Set.range fun i : s => g (f i))) (hg' : sSup ∅ <= ⨆ i : 
s…
-/
lemma ciInf_image {ι ι' : Type*} {s : Set ι} {f : ι → ι'} {g : ι' → α}
    (hf : BddBelow (Set.range fun i : s ↦ g (f i))) (hg' : ⨅ i : s, g (f i) ≤ sInf ∅) :
    ⨅ i ∈ (f '' s), g i = ⨅ x ∈ s, g (f x) :=
  ciSup_image (α := αᵒᵈ) hf hg'
/-
**le_ciSup_ciSup_eq_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_ciSup_ciSup_eq_left {b : β} {f : forall x : β, x = b -> α} : f b rfl <=
 ⨆ x, ⨆ h : x = b, f x h
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_ciSup₂`：le_ciSup₂ {κ : ι -> Sort*} {f : forall i, κ i -> α} (H : BddA
bove <| ⋃ i, range (f i)) (i : ι) (j : κ i) : f i j <= ⨆ (i) (j), f i j
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem le_ciSup_ciSup_eq_left {b : β} {f : ∀ x : β, x = b → α} :
    f b rfl ≤ ⨆ x, ⨆ h : x = b, f x h := by
  refine le_ciSup₂ (f := f) ⟨f b rfl, ?_⟩ b rfl
  rintro a ⟨_, ⟨b, rfl⟩, ⟨rfl, rfl⟩⟩
  rfl
/-
**ciInf_ciInf_eq_left_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ciInf_ciInf_eq_left_le {b : β} {f : forall x : β, x = b -> α} : ⨅ x, ⨅ h :
 x = b, f x h <= f b rfl
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_ciSup_ciSup_eq_left`：le_ciSup_ciSup_eq_left {b : β} {f : forall x : β
, x = b -> α} : f b rfl <= ⨆ x, ⨆ h : x = b, f x h
-/
theorem ciInf_ciInf_eq_left_le {b : β} {f : ∀ x : β, x = b → α} :
    ⨅ x, ⨅ h : x = b, f x h ≤ f b rfl :=
  le_ciSup_ciSup_eq_left (α := αᵒᵈ)
/-
**le_ciSup_ciSup_eq_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_ciSup_ciSup_eq_right {b : β} {f : forall x : β, b = x -> α} : f b rfl <
= ⨆ x, ⨆ h : b = x, f x h
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_ciSup₂`：le_ciSup₂ {κ : ι -> Sort*} {f : forall i, κ i -> α} (H : BddA
bove <| ⋃ i, range (f i)) (i : ι) (j : κ i) : f i j <= ⨆ (i) (j), f i j
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem le_ciSup_ciSup_eq_right {b : β} {f : ∀ x : β, b = x → α} :
    f b rfl ≤ ⨆ x, ⨆ h : b = x, f x h := by
  refine le_ciSup₂ ⟨f b rfl, ?_⟩ b rfl
  rintro a ⟨_, ⟨b, rfl⟩, ⟨rfl, rfl⟩⟩
  rfl
/-
**ciInf_ciInf_eq_right_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ciInf_ciInf_eq_right_le {b : β} {f : forall x : β, b = x -> α} : ⨅ x, ⨅ h 
: b = x, f x h <= f b rfl
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_ciSup_ciSup_eq_right`：le_ciSup_ciSup_eq_right {b : β} {f : forall x :
 β, b = x -> α} : f b rfl <= ⨆ x, ⨆ h : b = x, f x h
-/
theorem ciInf_ciInf_eq_right_le {b : β} {f : ∀ x : β, b = x → α} :
    ⨅ x, ⨅ h : b = x, f x h ≤ f b rfl :=
  le_ciSup_ciSup_eq_right (α := αᵒᵈ)

/-- Note that equality need not hold: consider `ι := Bool, p := (·), α := ℤ, f := fun _ ↦ -1`,
then the LHS is `-1` but the RHS is `-1 ⊔ sSup ∅ = -1 ⊔ 0 = 0`. -/
/-
**ciSup_exists_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ciSup_exists_le {p : ι -> Prop} {f : Exists p -> α} : ⨆ ih, f ih <= ⨆ (i) 
(h), f ⟨i, h⟩
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ciSup_le`：ciSup_le [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, f x 
<= c) : iSup f <= c
· 使用定理 `le_ciSup₂`：le_ciSup₂ {κ : ι -> Sort*} {f : forall i, κ i -> α} (H : BddA
bove <| ⋃ i, range (f i)) (i : ι) (j : κ i) : f i j <= ⨆ (i) (j), f i j
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `iSup_of_empty'`：iSup_of_empty' {α ι} [SupSet α] [IsEmpty ι] (f : ι -> α)
 : iSup f = sSup (∅ : Set α)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `ciSup_const`：ciSup_const [hι : Nonempty ι] {a : α} : ⨆ _ : ι, a = a

--- 原说明 ---
Note that equality need not hold: consider `ι := Bool, p := (·), α := ℤ, f := fu
n _ ↦ -1`,
then the LHS is `-1` but the RHS is `-1 ⊔ sSup ∅ = -1 ⊔ 0 = 0`.
-/
theorem ciSup_exists_le {p : ι → Prop} {f : Exists p → α} : ⨆ ih, f ih ≤ ⨆ (i) (h), f ⟨i, h⟩ := by
  by_cases! h : Exists p
  · have : Nonempty <| Exists p := ⟨h⟩
    refine ciSup_le fun ⟨i, hi⟩ ↦ le_ciSup₂ (f := fun _ _ ↦ _) ⟨f ⟨i, hi⟩, ?_⟩ i hi
    rintro _ ⟨_, ⟨j, rfl⟩, ⟨hj, rfl⟩⟩
    rfl
  · cases isEmpty_or_nonempty ι <;>
      simp [h, iSup_of_empty', ciSup_const]
/-
**le_ciInf_exists** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_ciInf_exists {p : ι -> Prop} {f : Exists p -> α} : ⨅ (i) (h), f ⟨i, h⟩ 
<= ⨅ ih, f ih
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ciSup_exists_le`：ciSup_exists_le {p : ι -> Prop} {f : Exists p -> α} : ⨆
 ih, f ih <= ⨆ (i) (h), f ⟨i, h⟩
-/
theorem le_ciInf_exists {p : ι → Prop} {f : Exists p → α} : ⨅ (i) (h), f ⟨i, h⟩ ≤ ⨅ ih, f ih :=
  ciSup_exists_le (α := αᵒᵈ)
/-
**ciSup_and** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ciSup_and {p q : Prop} {f : p ∧ q -> α} : ⨆ ih, f ih = ⨆ (h₁) (h₂), f ⟨h₁,
 h₂⟩
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `ciSup_unique`：ciSup_unique [Unique ι] {s : ι -> α} : ⨆ i, s i = s defaul
t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `iSup_of_empty'`：iSup_of_empty' {α ι} [SupSet α] [IsEmpty ι] (f : ι -> α)
 : iSup f = sSup (∅ : Set α)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
theorem ciSup_and {p q : Prop} {f : p ∧ q → α} : ⨆ ih, f ih = ⨆ (h₁) (h₂), f ⟨h₁, h₂⟩ := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq, iSup_of_empty']
/-
**ciInf_and** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ciInf_and {p q : Prop} {f : p ∧ q -> α} : ⨅ ih, f ih = ⨅ (h₁) (h₂), f ⟨h₁,
 h₂⟩
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ciSup_and`：ciSup_and {p q : Prop} {f : p ∧ q -> α} : ⨆ ih, f ih = ⨆ (h₁)
 (h₂), f ⟨h₁, h₂⟩
-/
theorem ciInf_and {p q : Prop} {f : p ∧ q → α} : ⨅ ih, f ih = ⨅ (h₁) (h₂), f ⟨h₁, h₂⟩ :=
  ciSup_and (α := αᵒᵈ)

end ConditionallyCompleteLattice

section ConditionallyCompleteLinearOrder

variable [ConditionallyCompleteLinearOrder α] {a b : α}

/-
**ciSup_sup_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ciSup_sup_le {f g : ι -> α} : ⨆ x, f x ⊔ g x <= (⨆ x, f x) ⊔ (⨆ x, g x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ciSup_of_not_bddAbove`：ciSup_of_not_bddAbove (hf : ¬BddAbove (range f)) 
: ⨆ i, f i = sSup ∅
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `bbdAbove_range_left_of_sup`：bbdAbove_range_left_of_sup {ι : Sort*} {α : 
Type*} [SemilatticeSup α] {f g : ι -> α} (h : BddAbove <| range fun x => f x ⊔ g
 x) : BddAbove r…
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `bbdAbove_range_right_of_sup`：bbdAbove_range_right_of_sup {ι : Sort*} {α 
: Type*} [SemilatticeSup α] {f g : ι -> α} (h : BddAbove <| range fun x => f x ⊔
 g x) : BddAbove …
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `ciSup_sup_eq`：ciSup_sup_eq {f g : ι -> α} (Hf : BddAbove <| range f) (Hg
 : BddAbove <| range g) : ⨆ x, f x ⊔ g x = (⨆ x, f x) ⊔ (⨆ x, g x)
-/
theorem ciSup_sup_le {f g : ι → α} : ⨆ x, f x ⊔ g x ≤ (⨆ x, f x) ⊔ (⨆ x, g x) := by
  by_cases! hf : ¬BddAbove (range f)
  · rw [ciSup_of_not_bddAbove hf, ciSup_of_not_bddAbove <| mt bbdAbove_range_left_of_sup hf]
    exact le_sup_left
  by_cases! hg : ¬BddAbove (range g)
  · rw [ciSup_of_not_bddAbove hg, ciSup_of_not_bddAbove <| mt bbdAbove_range_right_of_sup hg]
    exact le_sup_right
  exact ciSup_sup_eq hf hg |>.le
/-
**ciInf_inf_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ciInf_inf_le {f g : ι -> α} : (⨅ x, f x) ⊓ (⨅ x, g x) <= ⨅ x, f x ⊓ g x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ciSup_sup_le`：ciSup_sup_le {f g : ι -> α} : ⨆ x, f x ⊔ g x <= (⨆ x, f x)
 ⊔ (⨆ x, g x)
-/
theorem ciInf_inf_le {f g : ι → α} : (⨅ x, f x) ⊓ (⨅ x, g x) ≤ ⨅ x, f x ⊓ g x :=
  ciSup_sup_le (α := αᵒᵈ)

/-- Indexed version of `exists_lt_of_lt_csSup`.
When `b < iSup f`, there is an element `i` such that `b < f i`.
-/
/-
**exists_lt_of_lt_ciSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_lt_of_lt_ciSup [Nonempty ι] {f : ι -> α} (h : b < iSup f) : exists 
i, b < f i
参数：h : b < iSup f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_lt_of_lt_csSup`：exists_lt_of_lt_csSup (hs : s.Nonempty) (hb : b <
 sSup s) : exists a in s, b < a
· 使用定理 `Set.range_nonempty`：range_nonempty [h : Nonempty ι] (f : ι -> α) : (rang
e f).Nonempty

--- 原说明 ---
Indexed version of `exists_lt_of_lt_csSup`.
When `b < iSup f`, there is an element `i` such that `b < f i`.
-/
theorem exists_lt_of_lt_ciSup [Nonempty ι] {f : ι → α} (h : b < iSup f) : ∃ i, b < f i :=
  let ⟨_, ⟨i, rfl⟩, h⟩ := exists_lt_of_lt_csSup (range_nonempty f) h
  ⟨i, h⟩

/-- Indexed version of `exists_lt_of_csInf_lt`.
When `iInf f < a`, there is an element `i` such that `f i < a`.
-/
/-
**exists_lt_of_ciInf_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_lt_of_ciInf_lt [Nonempty ι] {f : ι -> α} (h : iInf f < a) : exists 
i, f i < a
参数：h : iInf f < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_lt_of_lt_ciSup`：exists_lt_of_lt_ciSup [Nonempty ι] {f : ι -> α} (
h : b < iSup f) : exists i, b < f i

--- 原说明 ---
Indexed version of `exists_lt_of_csInf_lt`.
When `iInf f < a`, there is an element `i` such that `f i < a`.
-/
theorem exists_lt_of_ciInf_lt [Nonempty ι] {f : ι → α} (h : iInf f < a) : ∃ i, f i < a :=
  exists_lt_of_lt_ciSup (α := αᵒᵈ) h
/-
**lt_ciSup_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_ciSup_iff [Nonempty ι] {f : ι -> α} (hb : BddAbove (range f)) : a < iSu
p f ↔ exists i, a < f i
参数：hb : BddAbove (range f)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `lt_csSup_iff`：lt_csSup_iff (hb : BddAbove s) (hs : s.Nonempty) : a < sSu
p s ↔ exists b in s, a < b
· 使用定理 `Set.range_nonempty`：range_nonempty [h : Nonempty ι] (f : ι -> α) : (rang
e f).Nonempty
-/
theorem lt_ciSup_iff [Nonempty ι] {f : ι → α} (hb : BddAbove (range f)) :
    a < iSup f ↔ ∃ i, a < f i := by
  simpa only [mem_range, exists_exists_eq_and] using! lt_csSup_iff hb (range_nonempty _)
/-
**ciInf_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ciInf_lt_iff [Nonempty ι] {f : ι -> α} (hb : BddBelow (range f)) : iInf f 
< a ↔ exists i, f i < a
参数：hb : BddBelow (range f)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `csInf_lt_iff`：∀ {α : Type u_1} [inst : ConditionallyCompleteLinearOrder 
α] {s : Set α} {a : α},   BddBelow s → s.Nonempty → (sInf s < a ↔ ∃ b ∈ s, b < a
)
· 使用定理 `Set.range_nonempty`：range_nonempty [h : Nonempty ι] (f : ι -> α) : (rang
e f).Nonempty
-/
theorem ciInf_lt_iff [Nonempty ι] {f : ι → α} (hb : BddBelow (range f)) :
    iInf f < a ↔ ∃ i, f i < a := by
  simpa only [mem_range, exists_exists_eq_and] using! csInf_lt_iff hb (range_nonempty _)
/-
**cbiSup_of_not_bddAbove** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cbiSup_of_not_bddAbove {p : ι -> Prop} {f : forall i, p i -> α} (h : ¬BddA
bove (range fun i : Subtype p => f i i.prop)) : ⨆ (i : ι), ⨆ (h : p i), f i h = 
sSup ∅
参数：h : ¬BddAbove (range fun i : Subtype p => f i i.prop)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用引理 `ciSup_of_not_bddAbove`：ciSup_of_not_bddAbove (hf : ¬BddAbove (range f)) 
: ⨆ i, f i = sSup ∅
· 使用定理 `ciSup_pos`：ciSup_pos {p : Prop} {f : p -> α} (hp : p) : ⨆ h : p, f h = f
 hp
-/
theorem cbiSup_of_not_bddAbove {p : ι → Prop} {f : ∀ i, p i → α}
    (h : ¬BddAbove (range fun i : Subtype p ↦ f i i.prop)) :
    ⨆ (i : ι), ⨆ (h : p i), f i h = sSup ∅ :=
  ciSup_of_not_bddAbove fun ⟨u, hu⟩ ↦ h ⟨u, fun _ ⟨x, hx⟩ ↦ hx ▸ hu ⟨x, ciSup_pos x.prop⟩⟩
/-
**cbiInf_of_not_bddBelow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cbiInf_of_not_bddBelow {p : ι -> Prop} {f : forall i, p i -> α} (h : ¬BddB
elow (range fun i : Subtype p => f i i.prop)) : ⨅ (i : ι), ⨅ (h : p i), f i h = 
sInf ∅
参数：h : ¬BddBelow (range fun i : Subtype p => f i i.prop)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `ciInf_of_not_bddBelow`：∀ {α : Type u_1} {ι : Sort u_4} [inst : Condition
allyCompleteLinearOrder α] {f : ι → α},   ¬BddBelow (Set.range f) → ⨅ i, f i = s
Inf ∅
· 使用定理 `ciInf_pos`：∀ {α : Type u_1} [inst : ConditionallyCompletePartialOrderInf
 α] {p : Prop} {f : p → α} (hp : p), ⨅ (h : p), f h = f hp
-/
theorem cbiInf_of_not_bddBelow {p : ι → Prop} {f : ∀ i, p i → α}
    (h : ¬BddBelow (range fun i : Subtype p ↦ f i i.prop)) :
    ⨅ (i : ι), ⨅ (h : p i), f i h = sInf ∅ :=
  ciInf_of_not_bddBelow fun ⟨u, hu⟩ ↦ h ⟨u, fun _ ⟨x, hx⟩ ↦ hx ▸ hu ⟨x, ciInf_pos x.prop⟩⟩
/-
**cbiSup_eq_of_not_forall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cbiSup_eq_of_not_forall {p : ι -> Prop} {f : Subtype p -> α} (hp : ¬ (fora
ll i, p i)) : ⨆ (i) (h : p i), f ⟨i, h⟩ = iSup f ⊔ sSup ∅
参数：hp : ¬ (forall i, p i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ciSup_subtype`：ciSup_subtype {p : ι -> Prop} {f : Subtype p -> α} (hf : 
BddAbove (Set.range f)) (hf' : sSup ∅ <= iSup f) : iSup f = ⨆ (i) (h : p i), f ⟨
i, …
· 使用引理 `ciSup_of_not_bddAbove`：ciSup_of_not_bddAbove (hf : ¬BddAbove (range f)) 
: ⨆ i, f i = sSup ∅
· 使用定理 `cbiSup_of_not_bddAbove`：cbiSup_of_not_bddAbove {p : ι -> Prop} {f : fora
ll i, p i -> α} (h : ¬BddAbove (range fun i : Subtype p => f i i.prop)) : ⨆ (i :
 ι), ⨆ (h : …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `max_eq_right`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b →
 max a b = b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `ciSup_eq_of_forall_le_of_forall_lt_exists_gt`：ciSup_eq_of_forall_le_of_f
orall_lt_exists_gt [Nonempty ι] {f : ι -> α} (h₁ : forall i, f i <= b) (h₂ : for
all w, w < b -> exists i, w < f i)…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `ciSup_pos`：ciSup_pos {p : Prop} {f : p -> α} (hp : p) : ⨆ h : p, f h = f
 hp
· 使用定理 `le_ciSup`：le_ciSup {f : ι -> α} (H : BddAbove (range f)) (c : ι) : f c <
= iSup f
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用引理 `ciSup_neg`：ciSup_neg {p : Prop} {f : p -> α} (hp : ¬ p) : ⨆ (h : p), f h
 = sSup (∅ : Set α)
· 使用定理 `LT.lt.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a < b → b = 
c → a < c
-/
theorem cbiSup_eq_of_not_forall {p : ι → Prop} {f : Subtype p → α} (hp : ¬ (∀ i, p i)) :
    ⨆ (i) (h : p i), f ⟨i, h⟩ = iSup f ⊔ sSup ∅ := by
  rcases le_or_gt (sSup ∅) (iSup f) with le | gt
  · rw [max_eq_left le]
    by_cases bdd : BddAbove (range f)
    · rw [← ciSup_subtype bdd le]
    · rw [ciSup_of_not_bddAbove bdd, cbiSup_of_not_bddAbove bdd]
  have ⟨i, hi⟩ := not_forall.mp hp
  have : Nonempty ι := ⟨i⟩
  have bdd : BddAbove (range f) := not_not.mp fun h ↦ gt.ne (ciSup_of_not_bddAbove h)
  rw [max_eq_right gt.le]
  refine ciSup_eq_of_forall_le_of_forall_lt_exists_gt (fun j ↦ ?_) ?_
  · by_cases hj : p j
    · exact ((ciSup_pos hj).trans_le (le_ciSup bdd ⟨j, hj⟩)).trans gt.le
    · exact (ciSup_neg hj).le
  · exact fun w hw ↦ ⟨i, hw.trans_eq (ciSup_neg hi).symm⟩
/-
**cbiInf_eq_of_not_forall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cbiInf_eq_of_not_forall {p : ι -> Prop} {f : Subtype p -> α} (hp : ¬ (fora
ll i, p i)) : ⨅ (i) (h : p i), f ⟨i, h⟩ = iInf f ⊓ sInf ∅
参数：hp : ¬ (forall i, p i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `cbiSup_eq_of_not_forall`：cbiSup_eq_of_not_forall {p : ι -> Prop} {f : Su
btype p -> α} (hp : ¬ (forall i, p i)) : ⨆ (i) (h : p i), f ⟨i, h⟩ = iSup f ⊔ sS
up ∅
-/
theorem cbiInf_eq_of_not_forall {p : ι → Prop} {f : Subtype p → α} (hp : ¬ (∀ i, p i)) :
    ⨅ (i) (h : p i), f ⟨i, h⟩ = iInf f ⊓ sInf ∅ :=
  cbiSup_eq_of_not_forall (α := αᵒᵈ) hp
/-
**ciInf_eq_bot_of_bot_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ciInf_eq_bot_of_bot_mem [OrderBot α] {f : ι -> α} (hs : ⊥ in range f) : iI
nf f = ⊥
参数：hs : ⊥ in range f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `csInf_eq_bot_of_bot_mem`：∀ {α : Type u_1} [inst : ConditionallyCompleteL
inearOrder α] [inst_1 : OrderBot α] {s : Set α}, ⊥ ∈ s → sInf s = ⊥
-/
theorem ciInf_eq_bot_of_bot_mem [OrderBot α] {f : ι → α} (hs : ⊥ ∈ range f) : iInf f = ⊥ :=
  csInf_eq_bot_of_bot_mem hs
/-
**ciSup_eq_top_of_top_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ciSup_eq_top_of_top_mem [OrderTop α] {f : ι -> α} (hs : ⊤ in range f) : iS
up f = ⊤
参数：hs : ⊤ in range f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `csSup_eq_top_of_top_mem`：csSup_eq_top_of_top_mem [OrderTop α] {s : Set α
} (hs : ⊤ in s) : sSup s = ⊤
-/
theorem ciSup_eq_top_of_top_mem [OrderTop α] {f : ι → α} (hs : ⊤ ∈ range f) : iSup f = ⊤ :=
  csSup_eq_top_of_top_mem hs

@[deprecated (since := "2026-04-05")] alias ciInf_eq_top_of_top_mem := ciSup_eq_top_of_top_mem

variable [WellFoundedLT α]
/-
**ciInf_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ciInf_mem [Nonempty ι] (f : ι -> α) : iInf f in range f
参数：f : ι -> α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `csInf_mem`：csInf_mem (hs : s.Nonempty) : sInf s in s
· 使用定理 `Set.range_nonempty`：range_nonempty [h : Nonempty ι] (f : ι -> α) : (rang
e f).Nonempty
-/
theorem ciInf_mem [Nonempty ι] (f : ι → α) : iInf f ∈ range f :=
  csInf_mem (range_nonempty f)
/-
**ciInf_eq_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ciInf_eq_iff [Nonempty ι] (f : ι -> α) (n : α) : ⨅ i, (f i) = n ↔ (exists 
i, f i = n) ∧ forall i, n <= f i
参数：f : ι -> α；n : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `supSet_to_nonempty`：∀ (α : Type u_1) [SupSet α], Nonempty α
· 使用定理 `ciInf_mem`：ciInf_mem [Nonempty ι] (f : ι -> α) : iInf f in range f
· 使用定理 `ciInf_le`：ciInf_le {f : ι -> α} (H : BddBelow (range f)) (c : ι) : iInf 
f <= f c
· 使用定理 `OrderBot.bddBelow`：∀ {α : Type u_1} [inst : Preorder α] [OrderBot α] (s 
: Set α), BddBelow s
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_ciInf`：le_ciInf [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, c <=
 f x) : c <= iInf f
-/
lemma ciInf_eq_iff [Nonempty ι] (f : ι → α) (n : α) :
    ⨅ i, (f i) = n ↔ (∃ i, f i = n) ∧ ∀ i, n ≤ f i := by
  have : OrderBot α := WellFoundedLT.toOrderBot α
  constructor
  · rintro rfl
    exact ⟨ciInf_mem f, ciInf_le (OrderBot.bddBelow ..)⟩
  · rintro ⟨⟨i, rfl⟩, h⟩
    exact le_antisymm (ciInf_le (OrderBot.bddBelow ..) _) (le_ciInf h)

end ConditionallyCompleteLinearOrder

/-!
### Lemmas about a conditionally complete linear order with bottom element

In this case we have `Sup ∅ = ⊥`, so we can drop some `Nonempty`/`Set.Nonempty` assumptions.
-/


section ConditionallyCompleteLinearOrderBot

variable [ConditionallyCompleteLinearOrderBot α] {f : ι → α} {a : α}

@[simp]
/-
**ciSup_of_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ciSup_of_empty [IsEmpty ι] (f : ι -> α) : ⨆ i, f i = ⊥
参数：f : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_of_empty'`：iSup_of_empty' {α ι} [SupSet α] [IsEmpty ι] (f : ι -> α)
 : iSup f = sSup (∅ : Set α)
· 使用定理 `csSup_empty`：csSup_empty : (sSup ∅ : α) = ⊥
-/
theorem ciSup_of_empty [IsEmpty ι] (f : ι → α) : ⨆ i, f i = ⊥ := by
  rw [iSup_of_empty', csSup_empty]
/-
**ciSup_false** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ciSup_false (f : False -> α) : ⨆ i, f i = ⊥
参数：f : False -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ciSup_of_empty`：ciSup_of_empty [IsEmpty ι] (f : ι -> α) : ⨆ i, f i = ⊥
· 使用定理 `instIsEmptyFalse`：IsEmpty False
-/
theorem ciSup_false (f : False → α) : ⨆ i, f i = ⊥ :=
  ciSup_of_empty f
/-
**le_ciSup_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_ciSup_iff' {s : ι -> α} {a : α} (h : BddAbove (range s)) : a <= iSup s 
↔ forall b, (forall i, s i <= b) -> a <= b
参数：h : BddAbove (range s)。
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem le_ciSup_iff' {s : ι → α} {a : α} (h : BddAbove (range s)) :
    a ≤ iSup s ↔ ∀ b, (∀ i, s i ≤ b) → a ≤ b := by simp [iSup, h, le_csSup_iff', upperBounds]
/-
**le_ciInf_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_ciInf_iff' [Nonempty ι] {f : ι -> α} {a : α} : a <= iInf f ↔ forall i, 
a <= f i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_ciInf_iff`：le_ciInf_iff [Nonempty ι] {f : ι -> α} {a : α} (hf : BddBe
low (range f)) : a <= iInf f ↔ forall i, a <= f i
· 使用定理 `OrderBot.bddBelow`：∀ {α : Type u_1} [inst : Preorder α] [OrderBot α] (s 
: Set α), BddBelow s
-/
theorem le_ciInf_iff' [Nonempty ι] {f : ι → α} {a : α} : a ≤ iInf f ↔ ∀ i, a ≤ f i :=
  le_ciInf_iff (OrderBot.bddBelow _)
/-
**ciInf_le'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ciInf_le' (f : ι -> α) (i : ι) : iInf f <= f i
参数：f : ι -> α；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ciInf_le`：ciInf_le {f : ι -> α} (H : BddBelow (range f)) (c : ι) : iInf 
f <= f c
· 使用定理 `OrderBot.bddBelow`：∀ {α : Type u_1} [inst : Preorder α] [OrderBot α] (s 
: Set α), BddBelow s
-/
theorem ciInf_le' (f : ι → α) (i : ι) : iInf f ≤ f i := ciInf_le (OrderBot.bddBelow _) _
/-
**ciInf_le_of_le'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ciInf_le_of_le' (c : ι) : f c <= a -> iInf f <= a
参数：c : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ciInf_le_of_le`：ciInf_le_of_le {f : ι -> α} (H : BddBelow (range f)) (c 
: ι) (h : f c <= a) : iInf f <= a
· 使用定理 `OrderBot.bddBelow`：∀ {α : Type u_1} [inst : Preorder α] [OrderBot α] (s 
: Set α), BddBelow s
-/
lemma ciInf_le_of_le' (c : ι) : f c ≤ a → iInf f ≤ a := ciInf_le_of_le (OrderBot.bddBelow _) _

/-- In conditionally complete orders with a bottom element, the nonempty condition can be omitted
from `ciSup_le_iff`. -/
/-
**ciSup_le_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ciSup_le_iff' {f : ι -> α} (h : BddAbove (range f)) {a : α} : ⨆ i, f i <= 
a ↔ forall i, f i <= a
参数：h : BddAbove (range f)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `csSup_le_iff'`：csSup_le_iff' {s : Set α} (hs : BddAbove s) {a : α} : sSu
p s <= a ↔ forall x in s, x <= a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)

--- 原说明 ---
In conditionally complete orders with a bottom element, the nonempty condition c
an be omitted
from `ciSup_le_iff`.
-/
theorem ciSup_le_iff' {f : ι → α} (h : BddAbove (range f)) {a : α} :
    ⨆ i, f i ≤ a ↔ ∀ i, f i ≤ a :=
  (csSup_le_iff' h).trans forall_mem_range
/-
**ciSup_le'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ciSup_le' {f : ι -> α} {a : α} (h : forall i, f i <= a) : ⨆ i, f i <= a
参数：h : forall i, f i <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `csSup_le'`：csSup_le' {s : Set α} {a : α} (h : a in upperBounds s) : sSup
 s <= a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
-/
theorem ciSup_le' {f : ι → α} {a : α} (h : ∀ i, f i ≤ a) : ⨆ i, f i ≤ a :=
  csSup_le' <| forall_mem_range.2 h

@[simp]
/-
**ciSup_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ciSup_bot : ⨆ _ : ι, (⊥ : α) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `ciSup_le'`：ciSup_le' {f : ι -> α} {a : α} (h : forall i, f i <= a) : ⨆ i
, f i <= a
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
theorem ciSup_bot : ⨆ _ : ι, (⊥ : α) = ⊥ := le_bot_iff.mp (ciSup_le' fun _ ↦ bot_le)

/-- In conditionally complete orders with a bottom element, the nonempty condition can be omitted
from `lt_ciSup_iff`. -/
/-
**lt_ciSup_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_ciSup_iff' {f : ι -> α} (h : BddAbove (range f)) : a < iSup f ↔ exists 
i, a < f i
参数：h : BddAbove (range f)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `ciSup_le_iff'`：ciSup_le_iff' {f : ι -> α} (h : BddAbove (range f)) {a : 
α} : ⨆ i, f i <= a ↔ forall i, f i <= a

--- 原说明 ---
In conditionally complete orders with a bottom element, the nonempty condition c
an be omitted
from `lt_ciSup_iff`.
-/
theorem lt_ciSup_iff' {f : ι → α} (h : BddAbove (range f)) : a < iSup f ↔ ∃ i, a < f i := by
  simpa only [not_le, not_forall] using (ciSup_le_iff' h).not
/-
**exists_lt_of_lt_ciSup'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_lt_of_lt_ciSup' {f : ι -> α} {a : α} (h : a < ⨆ i, f i) : exists i,
 a < f i
参数：h : a < ⨆ i, f i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `ciSup_le'`：ciSup_le' {f : ι -> α} {a : α} (h : forall i, f i <= a) : ⨆ i
, f i <= a
-/
theorem exists_lt_of_lt_ciSup' {f : ι → α} {a : α} (h : a < ⨆ i, f i) : ∃ i, a < f i := by
  contrapose! h
  exact ciSup_le' h
/-
**ciSup_mono_of_forall_exists'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ciSup_mono_of_forall_exists' {ι'} {f : ι -> α} {g : ι' -> α} (hg : BddAbov
e <| range g) (h : forall i, exists i', f i <= g i') : ⨆ i, f i <= ⨆ i', g i'
参数：hg : BddAbove <| range g；h : forall i, exists i', f i <= g i'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ciSup_le'`：ciSup_le' {f : ι -> α} {a : α} (h : forall i, f i <= a) : ⨆ i
, f i <= a
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `le_ciSup_of_le`：le_ciSup_of_le {f : ι -> α} (H : BddAbove (range f)) (c 
: ι) (h : a <= f c) : a <= iSup f
-/
theorem ciSup_mono_of_forall_exists' {ι'} {f : ι → α} {g : ι' → α} (hg : BddAbove <| range g)
    (h : ∀ i, ∃ i', f i ≤ g i') : ⨆ i, f i ≤ ⨆ i', g i' :=
  ciSup_le' fun i ↦ h i |>.elim <| le_ciSup_of_le hg

@[deprecated (since := "2026-05-03")] alias ciSup_mono' := ciSup_mono_of_forall_exists'
/-
**ciSup_exists** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ciSup_exists {p : ι -> Prop} {f : Exists p -> α} : ⨆ ih, f ih = ⨆ (i) (h),
 f ⟨i, h⟩
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `ciSup_exists_le`：ciSup_exists_le {p : ι -> Prop} {f : Exists p -> α} : ⨆
 ih, f ih <= ⨆ (i) (h), f ⟨i, h⟩
· 使用定理 `ciSup_le'`：ciSup_le' {f : ι -> α} {a : α} (h : forall i, f i <= a) : ⨆ i
, f i <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `ciSup_unique`：ciSup_unique [Unique ι] {s : ι -> α} : ⨆ i, s i = s defaul
t
-/
theorem ciSup_exists {p : ι → Prop} {f : Exists p → α} : ⨆ ih, f ih = ⨆ (i) (h), f ⟨i, h⟩ := by
  refine le_antisymm ciSup_exists_le <| ciSup_le' fun i ↦ ciSup_le' fun hi ↦ ?_
  simp [show Exists p from ⟨i, hi⟩]

@[simp]
/-
**ciSup_ciSup_eq_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ciSup_ciSup_eq_left {b : β} {f : forall x : β, x = b -> α} : ⨆ x, ⨆ h : x 
= b, f x h = f b rfl
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `ciSup_le'`：ciSup_le' {f : ι -> α} {a : α} (h : forall i, f i <= a) : ⨆ i
, f i <= a
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `le_ciSup_ciSup_eq_left`：le_ciSup_ciSup_eq_left {b : β} {f : forall x : β
, x = b -> α} : f b rfl <= ⨆ x, ⨆ h : x = b, f x h
-/
theorem ciSup_ciSup_eq_left {b : β} {f : ∀ x : β, x = b → α} :
    ⨆ x, ⨆ h : x = b, f x h = f b rfl :=
  le_antisymm (ciSup_le' fun _ ↦ ciSup_le' (· ▸ le_rfl)) le_ciSup_ciSup_eq_left

@[simp]
/-
**ciSup_ciSup_eq_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ciSup_ciSup_eq_right {b : β} {f : forall x : β, b = x -> α} : ⨆ x, ⨆ h : b
 = x, f x h = f b rfl
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `ciSup_le'`：ciSup_le' {f : ι -> α} {a : α} (h : forall i, f i <= a) : ⨆ i
, f i <= a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `le_ciSup_ciSup_eq_right`：le_ciSup_ciSup_eq_right {b : β} {f : forall x :
 β, b = x -> α} : f b rfl <= ⨆ x, ⨆ h : b = x, f x h
-/
theorem ciSup_ciSup_eq_right {b : β} {f : ∀ x : β, b = x → α} :
    ⨆ x, ⨆ h : b = x, f x h = f b rfl :=
  le_antisymm (ciSup_le' fun _ ↦ ciSup_le' (· ▸ le_refl (f b rfl))) le_ciSup_ciSup_eq_right
/-
**ciSup_or'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ciSup_or' (p q : Prop) (f : p ∨ q -> α) : ⨆ (h : p ∨ q), f h = (⨆ h : p, f
 (.inl h)) ⊔ ⨆ h : q, f (.inr h)
参数：p q : Prop；f : p ∨ q -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `ciSup_unique`：ciSup_unique [Unique ι] {s : ι -> α} : ⨆ i, s i = s defaul
t
· 使用定理 `max_self`：∀ {α : Type u_1} [inst : LinearOrder α] (a : α), max a a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `ciSup_of_empty`：ciSup_of_empty [IsEmpty ι] (f : ι -> α) : ⨆ i, f i = ⊥
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
-/
lemma ciSup_or' (p q : Prop) (f : p ∨ q → α) :
    ⨆ (h : p ∨ q), f h = (⨆ h : p, f (.inl h)) ⊔ ⨆ h : q, f (.inr h) := by
  by_cases hp : p <;>
  by_cases hq : q <;>
  simp [hp, hq]

end ConditionallyCompleteLinearOrderBot

namespace GaloisConnection

variable [ConditionallyCompleteLattice α] [ConditionallyCompleteLattice β] [Nonempty ι] {l : α → β}
  {u : β → α}

/-
**GaloisConnection.l_csSup** 是 Mathlib 中的一个定理，位于命名空间 `GaloisConnection`。
形式化陈述：l_csSup (gc : GaloisConnection l u) {s : Set α} (hne : s.Nonempty) (hbdd :
 BddAbove s) : l (sSup s) = ⨆ x : s, l x
参数：gc : GaloisConnection l u；hne : s.Nonempty；hbdd : BddAbove s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLUB.ciSup_set_eq`：IsLUB.ciSup_set_eq {s : Set β} {f : β -> α} (H : IsL
UB (f '' s) a) (Hne : s.Nonempty) : ⨆ i : s, f i = a
· 使用定理 `GaloisConnection.isLUB_l_image`：isLUB_l_image {s : Set α} {a : α} (h : I
sLUB s a) : IsLUB (l '' s) (l a)
· 使用定理 `isLUB_csSup`：isLUB_csSup (hn : s.Nonempty) (hb : BddAbove s
-/
theorem l_csSup (gc : GaloisConnection l u) {s : Set α} (hne : s.Nonempty) (hbdd : BddAbove s) :
    l (sSup s) = ⨆ x : s, l x :=
  Eq.symm <| IsLUB.ciSup_set_eq (gc.isLUB_l_image <| isLUB_csSup hne hbdd) hne
/-
**GaloisConnection.l_csSup'** 是 Mathlib 中的一个定理，位于命名空间 `GaloisConnection`。
形式化陈述：l_csSup' (gc : GaloisConnection l u) {s : Set α} (hne : s.Nonempty) (hbdd 
: BddAbove s) : l (sSup s) = sSup (l '' s)
参数：gc : GaloisConnection l u；hne : s.Nonempty；hbdd : BddAbove s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GaloisConnection.l_csSup`：l_csSup (gc : GaloisConnection l u) {s : Set α
} (hne : s.Nonempty) (hbdd : BddAbove s) : l (sSup s) = ⨆ x : s, l x
· 使用定理 `sSup_image'`：sSup_image' {s : Set β} {f : β -> α} : sSup (f '' s) = ⨆ a 
: s, f a
-/
theorem l_csSup' (gc : GaloisConnection l u) {s : Set α} (hne : s.Nonempty) (hbdd : BddAbove s) :
    l (sSup s) = sSup (l '' s) := by rw [gc.l_csSup hne hbdd, sSup_image']
/-
**GaloisConnection.l_ciSup** 是 Mathlib 中的一个定理，位于命名空间 `GaloisConnection`。
形式化陈述：l_ciSup (gc : GaloisConnection l u) {f : ι -> α} (hf : BddAbove (range f))
 : l (⨆ i, f i) = ⨆ i, l (f i)
参数：gc : GaloisConnection l u；hf : BddAbove (range f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : SupSet α] (s : ι → α), iS
up s = sSup (Set.range s)
· 使用定理 `GaloisConnection.l_csSup`：l_csSup (gc : GaloisConnection l u) {s : Set α
} (hne : s.Nonempty) (hbdd : BddAbove s) : l (sSup s) = ⨆ x : s, l x
· 使用定理 `Set.range_nonempty`：range_nonempty [h : Nonempty ι] (f : ι -> α) : (rang
e f).Nonempty
· 使用定理 `iSup_range'`：iSup_range' (g : β -> α) (f : ι -> β) : ⨆ b : range f, g b 
= ⨆ i, g (f i)
-/
theorem l_ciSup (gc : GaloisConnection l u) {f : ι → α} (hf : BddAbove (range f)) :
    l (⨆ i, f i) = ⨆ i, l (f i) := by rw [iSup, gc.l_csSup (range_nonempty _) hf, iSup_range']
/-
**GaloisConnection.l_ciSup_set** 是 Mathlib 中的一个定理，位于命名空间 `GaloisConnection`。
形式化陈述：l_ciSup_set (gc : GaloisConnection l u) {s : Set γ} {f : γ -> α} (hf : Bdd
Above (f '' s)) (hne : s.Nonempty) : l (⨆ i : s, f i) = ⨆ i : s, l (f i)
参数：gc : GaloisConnection l u；hf : BddAbove (f '' s)；hne : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.to_subtype`：∀ {α : Type u} {s : Set α}, s.Nonempty → Nonemp
ty ↑s
· 使用定理 `GaloisConnection.l_ciSup`：l_ciSup (gc : GaloisConnection l u) {f : ι -> 
α} (hf : BddAbove (range f)) : l (⨆ i, f i) = ⨆ i, l (f i)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_eq_range`：image_eq_range (f : α -> β) (s : Set α) : f '' s = r
ange fun x : s => f x
-/
theorem l_ciSup_set (gc : GaloisConnection l u) {s : Set γ} {f : γ → α} (hf : BddAbove (f '' s))
    (hne : s.Nonempty) : l (⨆ i : s, f i) = ⨆ i : s, l (f i) := by
  have := hne.to_subtype
  rw [image_eq_range] at hf
  exact gc.l_ciSup hf
/-
**GaloisConnection.u_csInf** 是 Mathlib 中的一个定理，位于命名空间 `GaloisConnection`。
形式化陈述：u_csInf (gc : GaloisConnection l u) {s : Set β} (hne : s.Nonempty) (hbdd :
 BddBelow s) : u (sInf s) = ⨅ x : s, u x
参数：gc : GaloisConnection l u；hne : s.Nonempty；hbdd : BddBelow s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_csSup`：l_csSup (gc : GaloisConnection l u) {s : Set α
} (hne : s.Nonempty) (hbdd : BddAbove s) : l (sSup s) = ⨆ x : s, l x
· 使用定理 `GaloisConnection.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [
inst_1 : Preorder β] {l : α → β} {u : β → α},   GaloisConnection l u →     Galoi
sConnection…
-/
theorem u_csInf (gc : GaloisConnection l u) {s : Set β} (hne : s.Nonempty) (hbdd : BddBelow s) :
    u (sInf s) = ⨅ x : s, u x :=
  gc.dual.l_csSup hne hbdd
/-
**GaloisConnection.u_csInf'** 是 Mathlib 中的一个定理，位于命名空间 `GaloisConnection`。
形式化陈述：u_csInf' (gc : GaloisConnection l u) {s : Set β} (hne : s.Nonempty) (hbdd 
: BddBelow s) : u (sInf s) = sInf (u '' s)
参数：gc : GaloisConnection l u；hne : s.Nonempty；hbdd : BddBelow s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_csSup'`：l_csSup' (gc : GaloisConnection l u) {s : Set
 α} (hne : s.Nonempty) (hbdd : BddAbove s) : l (sSup s) = sSup (l '' s)
· 使用定理 `GaloisConnection.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [
inst_1 : Preorder β] {l : α → β} {u : β → α},   GaloisConnection l u →     Galoi
sConnection…
-/
theorem u_csInf' (gc : GaloisConnection l u) {s : Set β} (hne : s.Nonempty) (hbdd : BddBelow s) :
    u (sInf s) = sInf (u '' s) :=
  gc.dual.l_csSup' hne hbdd
/-
**GaloisConnection.u_ciInf** 是 Mathlib 中的一个定理，位于命名空间 `GaloisConnection`。
形式化陈述：u_ciInf (gc : GaloisConnection l u) {f : ι -> β} (hf : BddBelow (range f))
 : u (⨅ i, f i) = ⨅ i, u (f i)
参数：gc : GaloisConnection l u；hf : BddBelow (range f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_ciSup`：l_ciSup (gc : GaloisConnection l u) {f : ι -> 
α} (hf : BddAbove (range f)) : l (⨆ i, f i) = ⨆ i, l (f i)
· 使用定理 `GaloisConnection.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [
inst_1 : Preorder β] {l : α → β} {u : β → α},   GaloisConnection l u →     Galoi
sConnection…
-/
theorem u_ciInf (gc : GaloisConnection l u) {f : ι → β} (hf : BddBelow (range f)) :
    u (⨅ i, f i) = ⨅ i, u (f i) :=
  gc.dual.l_ciSup hf
/-
**GaloisConnection.u_ciInf_set** 是 Mathlib 中的一个定理，位于命名空间 `GaloisConnection`。
形式化陈述：u_ciInf_set (gc : GaloisConnection l u) {s : Set γ} {f : γ -> β} (hf : Bdd
Below (f '' s)) (hne : s.Nonempty) : u (⨅ i : s, f i) = ⨅ i : s, u (f i)
参数：gc : GaloisConnection l u；hf : BddBelow (f '' s)；hne : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_ciSup_set`：l_ciSup_set (gc : GaloisConnection l u) {s
 : Set γ} {f : γ -> α} (hf : BddAbove (f '' s)) (hne : s.Nonempty) : l (⨆ i : s,
 f i) = ⨆ i : s, l…
· 使用定理 `GaloisConnection.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [
inst_1 : Preorder β] {l : α → β} {u : β → α},   GaloisConnection l u →     Galoi
sConnection…
-/
theorem u_ciInf_set (gc : GaloisConnection l u) {s : Set γ} {f : γ → β} (hf : BddBelow (f '' s))
    (hne : s.Nonempty) : u (⨅ i : s, f i) = ⨅ i : s, u (f i) :=
  gc.dual.l_ciSup_set hf hne

end GaloisConnection

namespace OrderIso

section ConditionallyCompleteLattice
variable [ConditionallyCompleteLattice α] [ConditionallyCompleteLattice β] [Nonempty ι]

/-
**OrderIso.map_csSup** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：map_csSup (e : α ≃o β) {s : Set α} (hne : s.Nonempty) (hbdd : BddAbove s) 
: e (sSup s) = ⨆ x : s, e x
参数：e : α ≃o β；hne : s.Nonempty；hbdd : BddAbove s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_csSup`：l_csSup (gc : GaloisConnection l u) {s : Set α
} (hne : s.Nonempty) (hbdd : BddAbove s) : l (sSup s) = ⨆ x : s, l x
· 使用引理 `OrderIso.to_galoisConnection`：to_galoisConnection (e : α ≃o β) : GaloisC
onnection e e.symm
-/
theorem map_csSup (e : α ≃o β) {s : Set α} (hne : s.Nonempty) (hbdd : BddAbove s) :
    e (sSup s) = ⨆ x : s, e x :=
  e.to_galoisConnection.l_csSup hne hbdd
/-
**OrderIso.map_csSup'** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：map_csSup' (e : α ≃o β) {s : Set α} (hne : s.Nonempty) (hbdd : BddAbove s)
 : e (sSup s) = sSup (e '' s)
参数：e : α ≃o β；hne : s.Nonempty；hbdd : BddAbove s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_csSup'`：l_csSup' (gc : GaloisConnection l u) {s : Set
 α} (hne : s.Nonempty) (hbdd : BddAbove s) : l (sSup s) = sSup (l '' s)
· 使用引理 `OrderIso.to_galoisConnection`：to_galoisConnection (e : α ≃o β) : GaloisC
onnection e e.symm
-/
theorem map_csSup' (e : α ≃o β) {s : Set α} (hne : s.Nonempty) (hbdd : BddAbove s) :
    e (sSup s) = sSup (e '' s) :=
  e.to_galoisConnection.l_csSup' hne hbdd
/-
**OrderIso.map_ciSup** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：map_ciSup (e : α ≃o β) {f : ι -> α} (hf : BddAbove (range f)) : e (⨆ i, f 
i) = ⨆ i, e (f i)
参数：e : α ≃o β；hf : BddAbove (range f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_ciSup`：l_ciSup (gc : GaloisConnection l u) {f : ι -> 
α} (hf : BddAbove (range f)) : l (⨆ i, f i) = ⨆ i, l (f i)
· 使用引理 `OrderIso.to_galoisConnection`：to_galoisConnection (e : α ≃o β) : GaloisC
onnection e e.symm
-/
theorem map_ciSup (e : α ≃o β) {f : ι → α} (hf : BddAbove (range f)) :
    e (⨆ i, f i) = ⨆ i, e (f i) :=
  e.to_galoisConnection.l_ciSup hf
/-
**OrderIso.map_ciSup_set** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：map_ciSup_set (e : α ≃o β) {s : Set γ} {f : γ -> α} (hf : BddAbove (f '' s
)) (hne : s.Nonempty) : e (⨆ i : s, f i) = ⨆ i : s, e (f i)
参数：e : α ≃o β；hf : BddAbove (f '' s)；hne : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_ciSup_set`：l_ciSup_set (gc : GaloisConnection l u) {s
 : Set γ} {f : γ -> α} (hf : BddAbove (f '' s)) (hne : s.Nonempty) : l (⨆ i : s,
 f i) = ⨆ i : s, l…
· 使用引理 `OrderIso.to_galoisConnection`：to_galoisConnection (e : α ≃o β) : GaloisC
onnection e e.symm
-/
theorem map_ciSup_set (e : α ≃o β) {s : Set γ} {f : γ → α} (hf : BddAbove (f '' s))
    (hne : s.Nonempty) : e (⨆ i : s, f i) = ⨆ i : s, e (f i) :=
  e.to_galoisConnection.l_ciSup_set hf hne
/-
**OrderIso.map_csInf** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：map_csInf (e : α ≃o β) {s : Set α} (hne : s.Nonempty) (hbdd : BddBelow s) 
: e (sInf s) = ⨅ x : s, e x
参数：e : α ≃o β；hne : s.Nonempty；hbdd : BddBelow s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_csSup`：map_csSup (e : α ≃o β) {s : Set α} (hne : s.Nonempty
) (hbdd : BddAbove s) : e (sSup s) = ⨆ x : s, e x
-/
theorem map_csInf (e : α ≃o β) {s : Set α} (hne : s.Nonempty) (hbdd : BddBelow s) :
    e (sInf s) = ⨅ x : s, e x :=
  e.dual.map_csSup hne hbdd
/-
**OrderIso.map_csInf'** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：map_csInf' (e : α ≃o β) {s : Set α} (hne : s.Nonempty) (hbdd : BddBelow s)
 : e (sInf s) = sInf (e '' s)
参数：e : α ≃o β；hne : s.Nonempty；hbdd : BddBelow s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_csSup'`：map_csSup' (e : α ≃o β) {s : Set α} (hne : s.Nonemp
ty) (hbdd : BddAbove s) : e (sSup s) = sSup (e '' s)
-/
theorem map_csInf' (e : α ≃o β) {s : Set α} (hne : s.Nonempty) (hbdd : BddBelow s) :
    e (sInf s) = sInf (e '' s) :=
  e.dual.map_csSup' hne hbdd
/-
**OrderIso.map_ciInf** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：map_ciInf (e : α ≃o β) {f : ι -> α} (hf : BddBelow (range f)) : e (⨅ i, f 
i) = ⨅ i, e (f i)
参数：e : α ≃o β；hf : BddBelow (range f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_ciSup`：map_ciSup (e : α ≃o β) {f : ι -> α} (hf : BddAbove (
range f)) : e (⨆ i, f i) = ⨆ i, e (f i)
-/
theorem map_ciInf (e : α ≃o β) {f : ι → α} (hf : BddBelow (range f)) :
    e (⨅ i, f i) = ⨅ i, e (f i) :=
  e.dual.map_ciSup hf
/-
**OrderIso.map_ciInf_set** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：map_ciInf_set (e : α ≃o β) {s : Set γ} {f : γ -> α} (hf : BddBelow (f '' s
)) (hne : s.Nonempty) : e (⨅ i : s, f i) = ⨅ i : s, e (f i)
参数：e : α ≃o β；hf : BddBelow (f '' s)；hne : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_ciSup_set`：map_ciSup_set (e : α ≃o β) {s : Set γ} {f : γ ->
 α} (hf : BddAbove (f '' s)) (hne : s.Nonempty) : e (⨆ i : s, f i) = ⨆ i : s, e 
(f i)
-/
theorem map_ciInf_set (e : α ≃o β) {s : Set γ} {f : γ → α} (hf : BddBelow (f '' s))
    (hne : s.Nonempty) : e (⨅ i : s, f i) = ⨅ i : s, e (f i) :=
  e.dual.map_ciSup_set hf hne

end ConditionallyCompleteLattice

section ConditionallyCompleteLinearOrderBot
variable [ConditionallyCompleteLinearOrderBot α] [ConditionallyCompleteLinearOrderBot β]

@[simp]
/-
**OrderIso.map_ciSup'** 是 Mathlib 中的一个引理，位于命名空间 `OrderIso`。
形式化陈述：map_ciSup' (e : α ≃o β) (f : ι -> α) : e (⨆ i, f i) = ⨆ i, e (f i)
参数：e : α ≃o β；f : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ciSup_of_empty`：ciSup_of_empty [IsEmpty ι] (f : ι -> α) : ⨆ i, f i = ⊥
· 使用定理 `OrderIso.map_bot`：OrderIso.map_bot [LE α] [PartialOrder β] [OrderBot α] 
[OrderBot β] (f : α ≃o β) : f ⊥ = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `OrderIso.map_ciSup`：map_ciSup (e : α ≃o β) {f : ι -> α} (hf : BddAbove (
range f)) : e (⨆ i, f i) = ⨆ i, e (f i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `OrderIso.surjective`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst
_1 : LE β] (e : α ≃o β), Function.Surjective ⇑e
· 使用引理 `ciSup_of_not_bddAbove`：ciSup_of_not_bddAbove (hf : ¬BddAbove (range f)) 
: ⨆ i, f i = sSup ∅
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `csSup_empty`：csSup_empty : (sSup ∅ : α) = ⊥
-/
lemma map_ciSup' (e : α ≃o β) (f : ι → α) : e (⨆ i, f i) = ⨆ i, e (f i) := by
  cases isEmpty_or_nonempty ι
  · simp [map_bot]
  by_cases hf : BddAbove (range f)
  · exact e.map_ciSup hf
  · have hfe : ¬ BddAbove (range fun i ↦ e (f i)) := by
      simpa [Set.Nonempty, BddAbove, upperBounds, e.surjective.forall] using hf
    simp [map_bot, hf, hfe]

end ConditionallyCompleteLinearOrderBot
end OrderIso

section WithTopBot

namespace WithTop
variable [ConditionallyCompleteLinearOrderBot α] {f : ι → α}

/-
**WithTop.iSup_coe_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `WithTop`。
形式化陈述：iSup_coe_eq_top : ⨆ x, (f x : WithTop α) = ⊤ ↔ ¬BddAbove (range f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_eq_top`：iSup_eq_top : iSup f = ⊤ ↔ forall b < ⊤, exists i, b < f i
· 使用定理 `not_bddAbove_iff`：not_bddAbove_iff {α : Type*} [LinearOrder α] {s : Set 
α} : ¬BddAbove s ↔ forall x, exists y in s, x < y
· 使用定理 `WithTop.coe_lt_top`：∀ {α : Type u_1} [inst : LT α] (a : α), ↑a < ⊤
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `WithTop.coe_lt_coe`：∀ {α : Type u_1} {a b : α} [inst : LT α], ↑b < ↑a ↔ 
b < a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `WithTop.coe_untop`：∀ {α : Type u_1} (x : WithTop α) (hx : x ≠ ⊤), ↑(x.un
top hx) = x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
lemma iSup_coe_eq_top : ⨆ x, (f x : WithTop α) = ⊤ ↔ ¬BddAbove (range f) := by
  rw [iSup_eq_top, not_bddAbove_iff]
  refine ⟨fun hf r => ?_, fun hf a ha => ?_⟩
  · rcases hf r (WithTop.coe_lt_top r) with ⟨i, hi⟩
    exact ⟨f i, ⟨i, rfl⟩, WithTop.coe_lt_coe.mp hi⟩
  · rcases hf (a.untop ha.ne) with ⟨-, ⟨i, rfl⟩, hi⟩
    exact ⟨i, by simpa only [WithTop.coe_untop _ ha.ne] using WithTop.coe_lt_coe.mpr hi⟩
/-
**WithTop.iSup_coe_lt_top** 是 Mathlib 中的一个引理，位于命名空间 `WithTop`。
形式化陈述：iSup_coe_lt_top : ⨆ x, (f x : WithTop α) < ⊤ ↔ BddAbove (range f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
· 使用定理 `Iff.not_left`：Iff.not_left (h : a ↔ ¬b) : ¬a ↔ b
· 使用引理 `WithTop.iSup_coe_eq_top`：iSup_coe_eq_top : ⨆ x, (f x : WithTop α) = ⊤ ↔ 
¬BddAbove (range f)
-/
lemma iSup_coe_lt_top : ⨆ x, (f x : WithTop α) < ⊤ ↔ BddAbove (range f) :=
  lt_top_iff_ne_top.trans iSup_coe_eq_top.not_left
/-
**WithTop.iInf_coe_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `WithTop`。
形式化陈述：iInf_coe_eq_top : ⨅ x, (f x : WithTop α) = ⊤ ↔ IsEmpty ι
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
lemma iInf_coe_eq_top : ⨅ x, (f x : WithTop α) = ⊤ ↔ IsEmpty ι := by simp [isEmpty_iff]
/-
**WithTop.iInf_coe_lt_top** 是 Mathlib 中的一个引理，位于命名空间 `WithTop`。
形式化陈述：iInf_coe_lt_top : ⨅ i, (f i : WithTop α) < ⊤ ↔ Nonempty ι
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用引理 `WithTop.iInf_coe_eq_top`：iInf_coe_eq_top : ⨅ x, (f x : WithTop α) = ⊤ ↔ 
IsEmpty ι
· 使用定理 `not_isEmpty_iff`：not_isEmpty_iff : ¬IsEmpty α ↔ Nonempty α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma iInf_coe_lt_top : ⨅ i, (f i : WithTop α) < ⊤ ↔ Nonempty ι := by
  rw [lt_top_iff_ne_top, Ne, iInf_coe_eq_top, not_isEmpty_iff]

end WithTop

end WithTopBot

