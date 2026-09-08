/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Data.Set.Lattice
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Order.ConditionallyCompletePartialOrder.Basic

/-!
# Theory of conditionally complete lattices

A conditionally complete lattice is a lattice in which every non-empty bounded subset `s`
has a least upper bound and a greatest lower bound, denoted below by `sSup s` and `sInf s`.
Typical examples are `ℝ`, `ℕ`, and `ℤ` with their usual orders.

The theory is very comparable to the theory of complete lattices, except that suitable
boundedness and nonemptiness assumptions have to be added to most statements.
We express these using the `BddAbove` and `BddBelow` predicates, which we use to prove
most useful properties of `sSup` and `sInf` in conditionally complete lattices.

To differentiate the statements between complete lattices and conditionally complete
lattices, we prefix `sInf` and `sSup` in the statements by `c`, giving `csInf` and `csSup`.
For instance, `sInf_le` is a statement in complete lattices ensuring `sInf s ≤ x`,
while `csInf_le` is the same statement in conditionally complete lattices
with an additional assumption that `s` is bounded below.
-/

@[expose] public section

-- Guard against import creep
assert_not_exists Multiset

open Function OrderDual Set

variable {α β γ : Type*} {ι : Sort*}

section LE

namespace WithTop

/-!
Extension of `sSup` and `sInf` from a preorder `α` to `WithTop α` and `WithBot α`
-/

variable [LE α]

open scoped Classical in
@[to_dual]
/-
**WithTop.** 是 Mathlib 中的一个实例，位于命名空间 `WithTop`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [SupSet α] : SupSet (WithTop α) :=
  ⟨fun S =>
    if ⊤ ∈ S then ⊤ else if BddAbove ((fun (a : α) ↦ ↑a) ⁻¹' S : Set α) then
      ↑(sSup ((fun (a : α) ↦ (a : WithTop α)) ⁻¹' S : Set α)) else ⊤⟩

open scoped Classical in
@[to_dual]
/-
**WithTop.instInfSet** 是 Mathlib 中的一个实例，位于命名空间 `WithTop`。
形式化陈述：instInfSet [InfSet α] : InfSet (WithTop α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance instInfSet [InfSet α] : InfSet (WithTop α) :=
  ⟨fun S => if S ⊆ {⊤} ∨ ¬BddBelow S then ⊤ else ↑(sInf ((fun (a : α) ↦ ↑a) ⁻¹' S : Set α))⟩

@[to_dual]
/-
**WithTop.sSup_eq** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：sSup_eq [SupSet α] {s : Set (WithTop α)} (hs : ⊤ ∉ s) (hs' : BddAbove ((↑)
 ⁻¹' s : Set α)) : sSup s = ↑(sSup ((↑) ⁻¹' s) : α)
参数：WithTop α；hs : ⊤ ∉ s；hs' : BddAbove ((↑) ⁻¹' s : Set α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem sSup_eq [SupSet α] {s : Set (WithTop α)} (hs : ⊤ ∉ s)
    (hs' : BddAbove ((↑) ⁻¹' s : Set α)) : sSup s = ↑(sSup ((↑) ⁻¹' s) : α) :=
  (if_neg hs).trans <| if_pos hs'

@[to_dual]
/-
**WithTop.sInf_eq** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：sInf_eq [InfSet α] {s : Set (WithTop α)} (hs : ¬s subseteq {⊤}) (h's : Bdd
Below s) : sInf s = ↑(sInf ((↑) ⁻¹' s) : α)
参数：WithTop α；hs : ¬s subseteq {⊤}；h's : BddBelow s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem sInf_eq [InfSet α] {s : Set (WithTop α)} (hs : ¬s ⊆ {⊤}) (h's : BddBelow s) :
    sInf s = ↑(sInf ((↑) ⁻¹' s) : α) :=
  if_neg <| by simp [hs, h's]

@[to_dual (attr := simp)]
/-
**WithTop.sInf_empty** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：sInf_empty [InfSet α] : sInf (∅ : Set (WithTop α)) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
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
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
theorem sInf_empty [InfSet α] : sInf (∅ : Set (WithTop α)) = ⊤ :=
  if_pos <| by simp

@[to_dual (attr := simp)]
/-
**WithTop.sInf_singleton_top** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：sInf_singleton_top [InfSet α] : sInf ({⊤} : Set (WithTop α)) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `subset_rfl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorde
r α] {a : α}, a ⊆ a
-/
theorem sInf_singleton_top [InfSet α] : sInf ({⊤} : Set (WithTop α)) = ⊤ :=
  if_pos <| .inl subset_rfl

@[to_dual (attr := simp)]
/-
**WithTop.sSup_of_top_mem** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：sSup_of_top_mem [SupSet α] {s : Set (WithTop α)} (h : ⊤ in s) : sSup s = ⊤
参数：WithTop α；h : ⊤ in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem sSup_of_top_mem [SupSet α] {s : Set (WithTop α)} (h : ⊤ ∈ s) : sSup s = ⊤ :=
  if_pos h

@[to_dual]
/-
**WithTop.sSup_singleton_top** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：sSup_singleton_top [SupSet α] : sSup ({⊤} : Set (WithTop α)) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithTop.sSup_of_top_mem`：sSup_of_top_mem [SupSet α] {s : Set (WithTop α)
} (h : ⊤ in s) : sSup s = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sSup_singleton_top [SupSet α] : sSup ({⊤} : Set (WithTop α)) = ⊤ := by
  simp

@[to_dual]
/-
**WithTop.sSup_of_not_bddAbove** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：sSup_of_not_bddAbove [SupSet α] {s : Set (WithTop α)} (h : ¬BddAbove ((↑) 
⁻¹' s : Set α)) : sSup s = ⊤
参数：WithTop α；h : ¬BddAbove ((↑) ⁻¹' s : Set α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.sSup_of_top_mem`：sSup_of_top_mem [SupSet α] {s : Set (WithTop α)
} (h : ⊤ in s) : sSup s = ⊤
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem sSup_of_not_bddAbove [SupSet α] {s : Set (WithTop α)}
    (h : ¬BddAbove ((↑) ⁻¹' s : Set α)) : sSup s = ⊤ := by
  by_cases hmem : ⊤ ∈ s
  · exact sSup_of_top_mem hmem
  · exact if_neg hmem |>.trans <| if_neg h

@[to_dual (attr := simp)]
/-
**WithTop.sInf_of_not_bddBelow** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：sInf_of_not_bddBelow [InfSet α] {s : Set (WithTop α)} (h : ¬BddBelow s) : 
sInf s = ⊤
参数：WithTop α；h : ¬BddBelow s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem sInf_of_not_bddBelow [InfSet α] {s : Set (WithTop α)} (h : ¬BddBelow s) :
    sInf s = ⊤ :=
  if_pos <| .inr h

@[to_dual (attr := norm_cast)]
/-
**WithTop.coe_sSup'** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：coe_sSup' [SupSet α] {s : Set α} (hs : BddAbove s) : ↑(sSup s) = (sSup ((f
un (a : α) => ↑a) '' s) : WithTop α)
参数：hs : BddAbove s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
· 使用定理 `Option.some_injective`：some_injective (α : Type*) : Function.Injective (
@some α)
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem coe_sSup' [SupSet α] {s : Set α} (hs : BddAbove s) :
    ↑(sSup s) = (sSup ((fun (a : α) ↦ ↑a) '' s) : WithTop α) := by
  classical
  change _ = ite _ _ _
  rw [if_neg, preimage_image_eq, if_pos hs]
  · exact Option.some_injective _
  · rintro ⟨x, _, ⟨⟩⟩

@[to_dual]
/-
**WithTop.sSup_empty** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：sSup_empty (α : Type*) [CompleteLattice α] : (sSup ∅ : WithTop α) = ⊥
参数：α : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithTop.sSup_eq`：sSup_eq [SupSet α] {s : Set (WithTop α)} (hs : ⊤ ∉ s) (
hs' : BddAbove ((↑) ⁻¹' s : Set α)) : sSup s = ↑(sSup ((↑) ⁻¹' s) : α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `OrderTop.bddAbove`：∀ {α : Type u_1} [inst : Preorder α] [OrderTop α] (s 
: Set α), BddAbove s
· 使用定理 `Set.preimage_empty`：preimage_empty : f ⁻¹' ∅ = ∅
· 使用定理 `sSup_empty`：sSup_empty : sSup ∅ = (⊥ : α)
· 使用定理 `WithTop.coe_bot`：∀ {α : Type u_1} [inst : Bot α], ↑⊥ = ⊥
-/
theorem sSup_empty (α : Type*) [CompleteLattice α] : (sSup ∅ : WithTop α) = ⊥ := by
  rw [sSup_eq (by simp) (OrderTop.bddAbove _), Set.preimage_empty, _root_.sSup_empty, coe_bot]

end WithTop

end LE

section Preorder

variable [Preorder α]

@[to_dual (attr := norm_cast)]
/-
**WithTop.coe_sInf'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WithTop.coe_sInf' [InfSet α] {s : Set α} (hs : s.Nonempty) (h's : BddBelow
 s) : ↑(sInf s) = (sInf ((fun (a : α) => ↑a) '' s) : WithTop α)
参数：hs : s.Nonempty；h's : BddBelow s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Monotone.map_bddBelow`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [
inst_1 : Preorder β] {f : α → β},   Monotone f → ∀ {s : Set α}, BddBelow s → Bdd
Below (f ''…
· 使用定理 `WithTop.coe_mono`：∀ {α : Type u_1} [inst : Preorder α], Monotone fun a =
> ↑a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
· 使用定理 `Option.some_injective`：some_injective (α : Type*) : Function.Injective (
@some α)
-/
theorem WithTop.coe_sInf' [InfSet α] {s : Set α} (hs : s.Nonempty)
    (h's : BddBelow s) : ↑(sInf s) = (sInf ((fun (a : α) ↦ ↑a) '' s) : WithTop α) := by
  classical
  obtain ⟨x, hx⟩ := hs
  change _ = ite _ _ _
  split_ifs with h
  · rcases h with h1 | h2
    · cases h1 (mem_image_of_mem _ hx)
    · exact (h2 (Monotone.map_bddBelow coe_mono h's)).elim
  · rw [preimage_image_eq]
    exact Option.some_injective _

end Preorder

/-
**ConditionallyCompleteLinearOrder.toLinearOrder** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ConditionallyCompleteLinearOrder.toLinearOrder [h : ConditionallyCompleteL
inearOrder α] : LinearOrder α where min_def a b
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ConditionallyCompleteLinearOrder.le_total`：∀ {α : Type u_5} [self : Cond
itionallyCompleteLinearOrder α] (a b : α), a ≤ b ∨ b ≤ a
· 使用定理 `ConditionallyCompleteLinearOrder.compare_eq_compareOfLessAndEq`：∀ {α : T
ype u_5} [self : ConditionallyCompleteLinearOrder α] (a b : α), compare a b = co
mpareOfLessAndEq a b
-/
instance ConditionallyCompleteLinearOrder.toLinearOrder [h : ConditionallyCompleteLinearOrder α] :
    LinearOrder α where
  min_def a b := by
    by_cases hab : a = b
    · simp [hab]
    · rcases ConditionallyCompleteLinearOrder.le_total a b with (h₁ | h₂)
      · simp [h₁]
      · simp [show ¬(a ≤ b) from fun h => hab (le_antisymm h h₂), h₂]
  max_def a b := by
    by_cases hab : a = b
    · simp [hab]
    · rcases ConditionallyCompleteLinearOrder.le_total a b with (h₁ | h₂)
      · simp [h₁]
      · simp [show ¬(a ≤ b) from fun h => hab (le_antisymm h h₂), h₂]
  __ := h

-- see Note [lower instance priority]
attribute [instance 100] ConditionallyCompleteLinearOrderBot.toOrderBot

-- see Note [lower instance priority]
/-- A complete lattice is a conditionally complete lattice, as there are no restrictions
on the properties of sInf and sSup in a complete lattice. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A complete lattice is a conditionally complete lattice, as there are no restrict
ions
on the properties of sInf and sSup in a complete lattice.
-/
instance (priority := 100) CompleteLattice.toConditionallyCompleteLattice [CompleteLattice α] :
    ConditionallyCompleteLattice α where
  isLUB_csSup _ _ _ := isLUB_sSup _
  isGLB_csInf _ _ _ := isGLB_sInf _

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) CompleteLinearOrder.toConditionallyCompleteLinearOrderBot {α : Type*}
    [h : CompleteLinearOrder α] : ConditionallyCompleteLinearOrderBot α where
  csSup_empty := sSup_empty
  csSup_of_not_bddAbove := fun s H ↦ (H (OrderTop.bddAbove s)).elim
  csInf_of_not_bddBelow := fun s H ↦ (H (OrderBot.bddBelow s)).elim
  __ := CompleteLattice.toConditionallyCompleteLattice
  __ := h

namespace OrderDual

/-
**OrderDual.instConditionallyCompleteLattice** 是 Mathlib 中的一个实例，位于命名空间 `OrderDua
l`。
形式化陈述：instConditionallyCompleteLattice (α : Type*) [ConditionallyCompleteLattice
 α] : ConditionallyCompleteLattice αᵒᵈ where isLUB_csSup
参数：α : Type*。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ConditionallyCompleteLattice.isGLB_csInf`：∀ {α : Type u_5} [self : Condi
tionallyCompleteLattice α] (s : Set α), s.Nonempty → BddBelow s → IsGLB s (sInf 
s)
· 使用定理 `ConditionallyCompleteLattice.isLUB_csSup`：∀ {α : Type u_5} [self : Condi
tionallyCompleteLattice α] (s : Set α), s.Nonempty → BddAbove s → IsLUB s (sSup 
s)
-/
instance instConditionallyCompleteLattice (α : Type*) [ConditionallyCompleteLattice α] :
    ConditionallyCompleteLattice αᵒᵈ where
  isLUB_csSup := ConditionallyCompleteLattice.isGLB_csInf (α := α)
  isGLB_csInf := ConditionallyCompleteLattice.isLUB_csSup (α := α)
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (α : Type*) [ConditionallyCompleteLinearOrder α] :
    ConditionallyCompleteLinearOrder αᵒᵈ where
  csSup_of_not_bddAbove := ConditionallyCompleteLinearOrder.csInf_of_not_bddBelow (α := α)
  csInf_of_not_bddBelow := ConditionallyCompleteLinearOrder.csSup_of_not_bddAbove (α := α)
  __ := OrderDual.instConditionallyCompleteLattice α
  __ := OrderDual.instLinearOrder α

end OrderDual

section ConditionallyCompleteLattice

variable [ConditionallyCompleteLattice α] {s t : Set α} {a b : α}

@[to_dual]
/-
**isLUB_csSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLUB_csSup (hn : s.Nonempty) (hb : BddAbove s
参数：hn : s.Nonempty。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConditionallyCompleteLattice.isLUB_csSup`：∀ {α : Type u_5} [self : Condi
tionallyCompleteLattice α] (s : Set α), s.Nonempty → BddAbove s → IsLUB s (sSup 
s)
-/
theorem isLUB_csSup (hn : s.Nonempty) (hb : BddAbove s := by bddDefault) : IsLUB s (sSup s) :=
  ConditionallyCompleteLattice.isLUB_csSup _ hn hb

@[to_dual csInf_le]
/-
**le_csSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_csSup (h₁ : BddAbove s) (h₂ : a in s) : a <= sSup s
参数：h₁ : BddAbove s；h₂ : a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `isLUB_csSup`：isLUB_csSup (hn : s.Nonempty) (hb : BddAbove s
· 使用定理 `Set.nonempty_of_mem`：nonempty_of_mem {x} (h : x in s) : s.Nonempty
-/
theorem le_csSup (h₁ : BddAbove s) (h₂ : a ∈ s) : a ≤ sSup s :=
  (isLUB_csSup (nonempty_of_mem h₂) h₁).1 h₂

@[to_dual le_csInf]
/-
**csSup_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：csSup_le (h₁ : s.Nonempty) (h₂ : forall b in s, b <= a) : sSup s <= a
参数：h₁ : s.Nonempty；h₂ : forall b in s, b <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `isLUB_csSup`：isLUB_csSup (hn : s.Nonempty) (hb : BddAbove s
-/
theorem csSup_le (h₁ : s.Nonempty) (h₂ : ∀ b ∈ s, b ≤ a) : sSup s ≤ a :=
  (isLUB_csSup h₁ ⟨a, h₂⟩).2 h₂

@[to_dual csInf_le_of_le]
/-
**le_csSup_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_csSup_of_le (hs : BddAbove s) (hb : b in s) (h : a <= b) : a <= sSup s
参数：hs : BddAbove s；hb : b in s；h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_csSup`：le_csSup (h₁ : BddAbove s) (h₂ : a in s) : a <= sSup s
-/
theorem le_csSup_of_le (hs : BddAbove s) (hb : b ∈ s) (h : a ≤ b) : a ≤ sSup s :=
  le_trans h (le_csSup hs hb)

@[to_dual (attr := gcongr low)]
/-
**csSup_le_csSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：csSup_le_csSup (ht : BddAbove t) (hs : s.Nonempty) (h : s subseteq t) : sS
up s <= sSup t
参数：ht : BddAbove t；hs : s.Nonempty；h : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `csSup_le`：csSup_le (h₁ : s.Nonempty) (h₂ : forall b in s, b <= a) : sSup
 s <= a
· 使用定理 `le_csSup`：le_csSup (h₁ : BddAbove s) (h₂ : a in s) : a <= sSup s
-/
theorem csSup_le_csSup (ht : BddAbove t) (hs : s.Nonempty) (h : s ⊆ t) : sSup s ≤ sSup t :=
  csSup_le hs fun _ ha => le_csSup ht (h ha)

@[to_dual csInf_le_iff]
/-
**le_csSup_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_csSup_iff (h : BddAbove s) (hs : s.Nonempty) : a <= sSup s ↔ forall b i
n upperBounds s, a <= b
参数：h : BddAbove s；hs : s.Nonempty。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `csSup_le`：csSup_le (h₁ : s.Nonempty) (h₂ : forall b in s, b <= a) : sSup
 s <= a
· 使用定理 `le_csSup`：le_csSup (h₁ : BddAbove s) (h₂ : a in s) : a <= sSup s
-/
theorem le_csSup_iff (h : BddAbove s) (hs : s.Nonempty) : a ≤ sSup s ↔ ∀ b ∈ upperBounds s, a ≤ b :=
  ⟨fun h _ hb => le_trans h (csSup_le hs hb), fun hb => hb _ fun _ => le_csSup h⟩

@[to_dual]
/-
**IsLUB.csSup_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLUB.csSup_eq (H : IsLUB s a) (ne : s.Nonempty) : sSup s = a
参数：H : IsLUB s a；ne : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLUB.unique`：IsLUB.unique (Ha : IsLUB s a) (Hb : IsLUB s b) : a = b
· 使用定理 `isLUB_csSup`：isLUB_csSup (hn : s.Nonempty) (hb : BddAbove s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem IsLUB.csSup_eq (H : IsLUB s a) (ne : s.Nonempty) : sSup s = a :=
  (isLUB_csSup ne ⟨a, H.1⟩).unique H
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) ConditionallyCompleteLattice.toConditionallyCompletePartialOrder :
    ConditionallyCompletePartialOrder α where
  isGLB_csInf_of_directed _ _ := isGLB_csInf _
  isLUB_csSup_of_directed _ _ := isLUB_csSup _
/-
**subset_Icc_csInf_csSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subset_Icc_csInf_csSup (hb : BddBelow s) (ha : BddAbove s) : s subseteq Ic
c (sInf s) (sSup s)
参数：hb : BddBelow s；ha : BddAbove s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `csInf_le`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s : 
Set α} {a : α}, BddBelow s → a ∈ s → sInf s ≤ a
· 使用定理 `le_csSup`：le_csSup (h₁ : BddAbove s) (h₂ : a in s) : a <= sSup s
-/
theorem subset_Icc_csInf_csSup (hb : BddBelow s) (ha : BddAbove s) : s ⊆ Icc (sInf s) (sSup s) :=
  fun _ hx => ⟨csInf_le hb hx, le_csSup ha hx⟩

@[to_dual le_csInf_iff]
/-
**csSup_le_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：csSup_le_iff (hb : BddAbove s) (hs : s.Nonempty) : sSup s <= a ↔ forall b 
in s, b <= a
参数：hb : BddAbove s；hs : s.Nonempty。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isLUB_le_iff`：isLUB_le_iff (h : IsLUB s a) : a <= b ↔ b in upperBounds s
· 使用定理 `isLUB_csSup`：isLUB_csSup (hn : s.Nonempty) (hb : BddAbove s
-/
theorem csSup_le_iff (hb : BddAbove s) (hs : s.Nonempty) : sSup s ≤ a ↔ ∀ b ∈ s, b ≤ a :=
  isLUB_le_iff (isLUB_csSup hs hb)

@[to_dual]
/-
**csSup_lowerBounds_eq_csInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：csSup_lowerBounds_eq_csInf {s : Set α} (h : BddBelow s) (hs : s.Nonempty) 
: sSup (lowerBounds s) = sInf s
参数：h : BddBelow s；hs : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLUB.unique`：IsLUB.unique (Ha : IsLUB s a) (Hb : IsLUB s b) : a = b
· 使用定理 `isLUB_csSup`：isLUB_csSup (hn : s.Nonempty) (hb : BddAbove s
· 使用定理 `Set.Nonempty.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Nonempty → t.
Nonempty
· 使用定理 `IsGreatest.isLUB`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α} {a : 
α}, IsGreatest s a → IsLUB s a
· 使用定理 `isGLB_csInf`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s
 : Set α},   s.Nonempty → autoParam (BddBelow s) isGLB_csInf._auto_1 → IsGLB s (
s…
-/
theorem csSup_lowerBounds_eq_csInf {s : Set α} (h : BddBelow s) (hs : s.Nonempty) :
    sSup (lowerBounds s) = sInf s :=
  (isLUB_csSup h <| hs.mono fun _ hx _ hy => hy hx).unique (isGLB_csInf hs h).isLUB

@[to_dual]
/-
**csSup_lowerBounds_range** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：csSup_lowerBounds_range [Nonempty β] {f : β -> α} (hf : BddBelow (range f)
) : sSup (lowerBounds (range f)) = ⨅ i, f i
参数：hf : BddBelow (range f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `csSup_lowerBounds_eq_csInf`：csSup_lowerBounds_eq_csInf {s : Set α} (h : 
BddBelow s) (hs : s.Nonempty) : sSup (lowerBounds s) = sInf s
· 使用定理 `Set.range_nonempty`：range_nonempty [h : Nonempty ι] (f : ι -> α) : (rang
e f).Nonempty
-/
theorem csSup_lowerBounds_range [Nonempty β] {f : β → α} (hf : BddBelow (range f)) :
    sSup (lowerBounds (range f)) = ⨅ i, f i :=
  csSup_lowerBounds_eq_csInf hf <| range_nonempty _

@[to_dual notMem_of_csSup_lt]
/-
**notMem_of_lt_csInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：notMem_of_lt_csInf {x : α} {s : Set α} (h : x < sInf s) (hs : BddBelow s) 
: x ∉ s
参数：h : x < sInf s；hs : BddBelow s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `csInf_le`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s : 
Set α} {a : α}, BddBelow s → a ∈ s → sInf s ≤ a
-/
theorem notMem_of_lt_csInf {x : α} {s : Set α} (h : x < sInf s) (hs : BddBelow s) : x ∉ s :=
  fun hx => lt_irrefl _ (h.trans_le (csInf_le hs hx))

/-- Introduction rule to prove that `b` is the supremum of `s`: it suffices to check that `b`
is larger than all elements of `s`, and that this is not the case of any `w<b`.
See `sSup_eq_of_forall_le_of_forall_lt_exists_gt` for a version in complete lattices. -/
@[to_dual csInf_eq_of_forall_ge_of_forall_gt_exists_lt
/-- Introduction rule to prove that `b` is the infimum of `s`: it suffices to check that `b`
is smaller than all elements of `s`, and that this is not the case of any `w>b`.
See `sInf_eq_of_forall_ge_of_forall_gt_exists_lt` for a version in complete lattices. -/]
/-
**csSup_eq_of_forall_le_of_forall_lt_exists_gt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：csSup_eq_of_forall_le_of_forall_lt_exists_gt (hs : s.Nonempty) (H : forall
 a in s, a <= b) (H' : forall w, w < b -> exists a in s, w < a) : sSup s = b
参数：hs : s.Nonempty；H : forall a in s, a <= b；H' : forall w, w < b -> exists a in
 s, w < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_le_of_not_lt`：eq_of_le_of_not_lt (h₁ : a <= b) (h₂ : ¬a < b) : a =
 b
· 使用定理 `csSup_le`：csSup_le (h₁ : s.Nonempty) (h₂ : forall b in s, b <= a) : sSup
 s <= a
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `le_csSup`：le_csSup (h₁ : BddAbove s) (h₂ : a in s) : a <= sSup s
-/
theorem csSup_eq_of_forall_le_of_forall_lt_exists_gt (hs : s.Nonempty) (H : ∀ a ∈ s, a ≤ b)
    (H' : ∀ w, w < b → ∃ a ∈ s, w < a) : sSup s = b :=
  (eq_of_le_of_not_lt (csSup_le hs H)) fun hb =>
    let ⟨_, ha, ha'⟩ := H' _ hb
    lt_irrefl _ <| ha'.trans_le <| le_csSup ⟨b, H⟩ ha

/-- `b < sSup s` when there is an element `a` in `s` with `b < a`, when `s` is bounded above.
This is essentially an iff, except that the assumptions for the two implications are
slightly different (one needs boundedness above for one direction, nonemptiness and linear
order for the other one), so we formulate separately the two implications, contrary to
the `CompleteLattice` case. -/
@[to_dual csInf_lt_of_lt
/-- `sInf s < b` when there is an element `a` in `s` with `a < b`, when `s` is bounded below.
This is essentially an iff, except that the assumptions for the two implications are
slightly different (one needs boundedness below for one direction, nonemptiness and linear
order for the other one), so we formulate separately the two implications, contrary to
the `CompleteLattice` case. -/]
/-
**lt_csSup_of_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_csSup_of_lt (hs : BddAbove s) (ha : a in s) (h : b < a) : b < sSup s
参数：hs : BddAbove s；ha : a in s；h : b < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `le_csSup`：le_csSup (h₁ : BddAbove s) (h₂ : a in s) : a <= sSup s
-/
theorem lt_csSup_of_lt (hs : BddAbove s) (ha : a ∈ s) (h : b < a) : b < sSup s :=
  lt_of_lt_of_le h (le_csSup hs ha)

/-- If all elements of a nonempty set `s` are less than or equal to all elements
of a nonempty set `t`, then there exists an element between these sets. -/
@[to_dual none]
/-
**exists_between_of_forall_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_between_of_forall_le (sne : s.Nonempty) (tne : t.Nonempty) (hst : f
orall x in s, forall y in t, x <= y) : (upperBounds s inter lowerBounds t).Nonem
pty
参数：sne : s.Nonempty；tne : t.Nonempty；hst : forall x in s, forall y in t, x <= y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_csInf`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s : 
Set α} {a : α}, s.Nonempty → (∀ b ∈ s, a ≤ b) → a ≤ sInf s
· 使用定理 `csInf_le`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s : 
Set α} {a : α}, BddBelow s → a ∈ s → sInf s ≤ a
· 使用定理 `Set.Nonempty.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Nonempty → t.
Nonempty

--- 原说明 ---
If all elements of a nonempty set `s` are less than or equal to all elements
of a nonempty set `t`, then there exists an element between these sets.
-/
theorem exists_between_of_forall_le (sne : s.Nonempty) (tne : t.Nonempty)
    (hst : ∀ x ∈ s, ∀ y ∈ t, x ≤ y) : (upperBounds s ∩ lowerBounds t).Nonempty :=
  ⟨sInf t, fun x hx => le_csInf tne <| hst x hx, fun _ hy => csInf_le (sne.mono hst) hy⟩

@[to_dual]
/-
**csSup_pair** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：csSup_pair (a b : α) : sSup {a, b} = a ⊔ b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLUB.csSup_eq`：IsLUB.csSup_eq (H : IsLUB s a) (ne : s.Nonempty) : sSup 
s = a
· 使用定理 `isLUB_pair`：isLUB_pair [SemilatticeSup γ] {a b : γ} : IsLUB {a, b} (a ⊔ 
b)
· 使用定理 `Set.insert_nonempty`：insert_nonempty (a : α) (s : Set α) : (insert a s).
Nonempty
-/
theorem csSup_pair (a b : α) : sSup {a, b} = a ⊔ b :=
  (@isLUB_pair _ _ a b).csSup_eq (insert_nonempty _ _)

/-- If a set is bounded below and above, and nonempty, its infimum is less than or equal to
its supremum. -/
@[to_dual self (reorder := hb ha)]
/-
**csInf_le_csSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：csInf_le_csSup (ne : s.Nonempty) (hb : BddBelow s
参数：ne : s.Nonempty。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isGLB_le_isLUB`：isGLB_le_isLUB (ha : IsGLB s a) (hb : IsLUB s b) (hs : s
.Nonempty) : a <= b
· 使用定理 `isGLB_csInf`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s
 : Set α},   s.Nonempty → autoParam (BddBelow s) isGLB_csInf._auto_1 → IsGLB s (
s…
· 使用定理 `isLUB_csSup`：isLUB_csSup (hn : s.Nonempty) (hb : BddAbove s

--- 原说明 ---
If a set is bounded below and above, and nonempty, its infimum is less than or e
qual to
its supremum.
-/
theorem csInf_le_csSup (ne : s.Nonempty) (hb : BddBelow s := by bddDefault)
    (ha : BddAbove s := by bddDefault) : sInf s ≤ sSup s :=
  isGLB_le_isLUB (isGLB_csInf ne hb) (isLUB_csSup ne ha) ne
/-
**csInf_le_csSup_of_nonempty_inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：csInf_le_csSup_of_nonempty_inter (h : (s inter t).Nonempty) (hs : BddBelow
 s
参数：h : (s inter t).Nonempty。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isGLB_le_isLUB_of_nonempty_inter`：isGLB_le_isLUB_of_nonempty_inter (h : 
(s inter s').Nonempty) (ha : IsGLB s a) (hb : IsLUB s' b) : a <= b
· 使用定理 `isGLB_csInf`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s
 : Set α},   s.Nonempty → autoParam (BddBelow s) isGLB_csInf._auto_1 → IsGLB s (
s…
· 使用定理 `Set.Nonempty.left`：∀ {α : Type u} {s t : Set α}, (s ∩ t).Nonempty → s.No
nempty
· 使用定理 `isLUB_csSup`：isLUB_csSup (hn : s.Nonempty) (hb : BddAbove s
· 使用定理 `Set.Nonempty.right`：∀ {α : Type u} {s t : Set α}, (s ∩ t).Nonempty → t.N
onempty
-/
theorem csInf_le_csSup_of_nonempty_inter (h : (s ∩ t).Nonempty) (hs : BddBelow s := by bddDefault)
    (ht : BddAbove t := by bddDefault) : sInf s ≤ sSup t :=
  isGLB_le_isLUB_of_nonempty_inter h (isGLB_csInf h.left hs) (isLUB_csSup h.right ht)

/-- The `sSup` of a union of two sets is the max of the suprema of each subset, under the
assumptions that all sets are bounded above and nonempty. -/
@[to_dual
/-- The `sInf` of a union of two sets is the min of the infima of each subset, under the assumptions
that all sets are bounded below and nonempty. -/]
/-
**csSup_union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：csSup_union (hs : BddAbove s) (sne : s.Nonempty) (ht : BddAbove t) (tne : 
t.Nonempty) : sSup (s union t) = sSup s ⊔ sSup t
参数：hs : BddAbove s；sne : s.Nonempty；ht : BddAbove t；tne : t.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLUB.csSup_eq`：IsLUB.csSup_eq (H : IsLUB s a) (ne : s.Nonempty) : sSup 
s = a
· 使用定理 `IsLUB.union`：IsLUB.union [SemilatticeSup γ] {a b : γ} {s t : Set γ} (hs 
: IsLUB s a) (ht : IsLUB t b) : IsLUB (s union t) (a ⊔ b)
· 使用定理 `isLUB_csSup`：isLUB_csSup (hn : s.Nonempty) (hb : BddAbove s
· 使用定理 `Set.Nonempty.inl`：∀ {α : Type u} {s t : Set α}, s.Nonempty → (s ∪ t).Non
empty
-/
theorem csSup_union (hs : BddAbove s) (sne : s.Nonempty) (ht : BddAbove t) (tne : t.Nonempty) :
    sSup (s ∪ t) = sSup s ⊔ sSup t :=
  ((isLUB_csSup sne hs).union (isLUB_csSup tne ht)).csSup_eq sne.inl

/-- The supremum of an intersection of two sets is bounded by the minimum of the suprema of each
set, if all sets are bounded above and nonempty. -/
@[to_dual le_csInf_inter
/-- The infimum of an intersection of two sets is bounded below by the maximum of the
infima of each set, if all sets are bounded below and nonempty. -/]
/-
**csSup_inter_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：csSup_inter_le (hs : BddAbove s) (ht : BddAbove t) (hst : (s inter t).None
mpty) : sSup (s inter t) <= sSup s ⊓ sSup t
参数：hs : BddAbove s；ht : BddAbove t；hst : (s inter t).Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `csSup_le`：csSup_le (h₁ : s.Nonempty) (h₂ : forall b in s, b <= a) : sSup
 s <= a
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
· 使用定理 `le_csSup`：le_csSup (h₁ : BddAbove s) (h₂ : a in s) : a <= sSup s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem csSup_inter_le (hs : BddAbove s) (ht : BddAbove t) (hst : (s ∩ t).Nonempty) :
    sSup (s ∩ t) ≤ sSup s ⊓ sSup t :=
  (csSup_le hst) fun _ hx => le_inf (le_csSup hs hx.1) (le_csSup ht hx.2)

/-- The supremum of `insert a s` is the maximum of `a` and the supremum of `s`, if `s` is
nonempty and bounded above. -/
@[to_dual (attr := simp)
/-- The infimum of `insert a s` is the minimum of `a` and the infimum of `s`, if `s` is
nonempty and bounded below. -/]
/-
**csSup_insert** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：csSup_insert (hs : BddAbove s) (sne : s.Nonempty) : sSup (insert a s) = a 
⊔ sSup s
参数：hs : BddAbove s；sne : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLUB.csSup_eq`：IsLUB.csSup_eq (H : IsLUB s a) (ne : s.Nonempty) : sSup 
s = a
· 使用定理 `IsLUB.insert`：∀ {γ : Type u_3} [inst : SemilatticeSup γ] (a : γ) {b : γ}
 {s : Set γ}, IsLUB s b → IsLUB (insert a s) (a ⊔ b)
· 使用定理 `isLUB_csSup`：isLUB_csSup (hn : s.Nonempty) (hb : BddAbove s
· 使用定理 `Set.insert_nonempty`：insert_nonempty (a : α) (s : Set α) : (insert a s).
Nonempty
-/
theorem csSup_insert (hs : BddAbove s) (sne : s.Nonempty) : sSup (insert a s) = a ⊔ sSup s :=
  ((isLUB_csSup sne hs).insert a).csSup_eq (insert_nonempty a s)

@[to_dual (attr := simp)]
/-
**csSup_Ico** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：csSup_Ico [DenselyOrdered α] (h : a < b) : sSup (Ico a b) = b
参数：h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLUB.csSup_eq`：IsLUB.csSup_eq (H : IsLUB s a) (ne : s.Nonempty) : sSup 
s = a
· 使用定理 `isLUB_Ico`：∀ {γ : Type u_3} [inst : SemilatticeInf γ] [DenselyOrdered γ]
 {a b : γ}, b < a → IsLUB (Set.Ico b a) a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.nonempty_Ico`：nonempty_Ico : (Ico a b).Nonempty ↔ a < b
-/
theorem csSup_Ico [DenselyOrdered α] (h : a < b) : sSup (Ico a b) = b :=
  (isLUB_Ico h).csSup_eq (nonempty_Ico.2 h)

@[to_dual (attr := simp)]
/-
**csSup_Iio** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：csSup_Iio [NoMinOrder α] [DenselyOrdered α] : sSup (Iio a) = a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `csSup_eq_of_forall_le_of_forall_lt_exists_gt`：csSup_eq_of_forall_le_of_f
orall_lt_exists_gt (hs : s.Nonempty) (H : forall a in s, a <= b) (H' : forall w,
 w < b -> exists a in s, w < a) : …
· 使用定理 `Set.nonempty_Iio`：nonempty_Iio [NoMinOrder α] : (Iio a).Nonempty
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
-/
theorem csSup_Iio [NoMinOrder α] [DenselyOrdered α] : sSup (Iio a) = a :=
  csSup_eq_of_forall_le_of_forall_lt_exists_gt nonempty_Iio (fun _ => le_of_lt) fun w hw => by
    simpa [and_comm] using exists_between hw

@[to_dual (attr := simp)]
/-
**csSup_Ioo** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：csSup_Ioo [DenselyOrdered α] (h : a < b) : sSup (Ioo a b) = b
参数：h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLUB.csSup_eq`：IsLUB.csSup_eq (H : IsLUB s a) (ne : s.Nonempty) : sSup 
s = a
· 使用定理 `isLUB_Ioo`：∀ {γ : Type u_3} [inst : SemilatticeInf γ] [DenselyOrdered γ]
 {a b : γ}, b < a → IsLUB (Set.Ioo b a) a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.nonempty_Ioo`：nonempty_Ioo [DenselyOrdered α] : (Ioo a b).Nonempty ↔
 a < b
-/
theorem csSup_Ioo [DenselyOrdered α] (h : a < b) : sSup (Ioo a b) = b :=
  (isLUB_Ioo h).csSup_eq (nonempty_Ioo.2 h)

/-- Introduction rule to prove that `b` is the supremum of `s`: it suffices to check that
1) `b` is an upper bound
2) every other upper bound `b'` satisfies `b ≤ b'`. -/
/-
**csSup_eq_of_is_forall_le_of_forall_le_imp_ge** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：csSup_eq_of_is_forall_le_of_forall_le_imp_ge (hs : s.Nonempty) (h_is_ub : 
forall a in s, a <= b) (h_b_le_ub : forall ub, (forall a in s, a <= ub) -> b <= 
ub) : sSup s = b
参数：hs : s.Nonempty；h_is_ub : forall a in s, a <= b；h_b_le_ub : forall ub, (foral
l a in s, a <= ub) -> b <= ub。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `csSup_le`：csSup_le (h₁ : s.Nonempty) (h₂ : forall b in s, b <= a) : sSup
 s <= a
· 使用定理 `le_csSup`：le_csSup (h₁ : BddAbove s) (h₂ : a in s) : a <= sSup s

--- 原说明 ---
Introduction rule to prove that `b` is the supremum of `s`: it suffices to check
 that
1) `b` is an upper bound
2) every other upper bound `b'` satisfies `b ≤ b'`.
-/
theorem csSup_eq_of_is_forall_le_of_forall_le_imp_ge (hs : s.Nonempty) (h_is_ub : ∀ a ∈ s, a ≤ b)
    (h_b_le_ub : ∀ ub, (∀ a ∈ s, a ≤ ub) → b ≤ ub) : sSup s = b :=
  (csSup_le hs h_is_ub).antisymm ((h_b_le_ub _) fun _ => le_csSup ⟨b, h_is_ub⟩)

end ConditionallyCompleteLattice

/-
**Pi.conditionallyCompleteLattice** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.conditionallyCompleteLattice {ι : Type*} {α : ι -> Type*} [forall i, Co
nditionallyCompleteLattice (α i)] : ConditionallyCompleteLattice (forall i, α i)
 where isLUB_csSup _ hn hb
参数：α i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Pi.conditionallyCompleteLattice {ι : Type*} {α : ι → Type*}
    [∀ i, ConditionallyCompleteLattice (α i)] : ConditionallyCompleteLattice (∀ i, α i) where
  isLUB_csSup _ hn hb := isLUB_pi.mpr fun _ ↦ by
    rw [sSup_apply_eq_sSup_image]
    exact isLUB_csSup (image_nonempty.mpr hn) ((monotone_eval _).map_bddAbove hb)
  isGLB_csInf _ hn hb := isGLB_pi.mpr fun _ ↦ by
    rw [sInf_apply_eq_sInf_image]
    exact isGLB_csInf (image_nonempty.mpr hn) ((monotone_eval _).map_bddBelow hb)

section ConditionallyCompleteLinearOrder

variable [ConditionallyCompleteLinearOrder α] {f : ι → α} {s : Set α} {a b : α}

/-- When `b < sSup s`, there is an element `a` in `s` with `b < a`, if `s` is nonempty and the order
is a linear order. -/
@[to_dual exists_lt_of_csInf_lt
/-- When `sInf s < b`, there is an element `a` in `s` with `a < b`, if `s` is nonempty and the order
is a linear order. -/]
/-
**exists_lt_of_lt_csSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_lt_of_lt_csSup (hs : s.Nonempty) (hb : b < sSup s) : exists a in s,
 b < a
参数：hs : s.Nonempty；hb : b < sSup s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `csSup_le`：csSup_le (h₁ : s.Nonempty) (h₂ : forall b in s, b <= a) : sSup
 s <= a
-/
theorem exists_lt_of_lt_csSup (hs : s.Nonempty) (hb : b < sSup s) : ∃ a ∈ s, b < a := by
  contrapose! hb
  exact csSup_le hs hb

@[to_dual csInf_lt_iff]
/-
**lt_csSup_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_csSup_iff (hb : BddAbove s) (hs : s.Nonempty) : a < sSup s ↔ exists b i
n s, a < b
参数：hb : BddAbove s；hs : s.Nonempty。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_isLUB_iff`：lt_isLUB_iff (h : IsLUB s a) : b < a ↔ exists c in s, b < 
c
· 使用定理 `isLUB_csSup`：isLUB_csSup (hn : s.Nonempty) (hb : BddAbove s
-/
theorem lt_csSup_iff (hb : BddAbove s) (hs : s.Nonempty) : a < sSup s ↔ ∃ b ∈ s, a < b :=
  lt_isLUB_iff <| isLUB_csSup hs hb

@[to_dual (attr := simp)]
/-
**csSup_of_not_bddAbove** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：csSup_of_not_bddAbove (hs : ¬BddAbove s) : sSup s = sSup ∅
参数：hs : ¬BddAbove s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConditionallyCompleteLinearOrder.csSup_of_not_bddAbove`：∀ {α : Type u_5}
 [self : ConditionallyCompleteLinearOrder α] (s : Set α), ¬BddAbove s → sSup s =
 sSup ∅
-/
lemma csSup_of_not_bddAbove (hs : ¬BddAbove s) : sSup s = sSup ∅ :=
  ConditionallyCompleteLinearOrder.csSup_of_not_bddAbove s hs

@[to_dual (attr := simp)]
/-
**ciSup_of_not_bddAbove** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ciSup_of_not_bddAbove (hf : ¬BddAbove (range f)) : ⨆ i, f i = sSup ∅
参数：hf : ¬BddAbove (range f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `csSup_of_not_bddAbove`：csSup_of_not_bddAbove (hs : ¬BddAbove s) : sSup s
 = sSup ∅
-/
lemma ciSup_of_not_bddAbove (hf : ¬BddAbove (range f)) : ⨆ i, f i = sSup ∅ :=
  csSup_of_not_bddAbove hf

@[to_dual]
/-
**csSup_eq_univ_of_not_bddAbove** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：csSup_eq_univ_of_not_bddAbove (hs : ¬BddAbove s) : sSup s = sSup univ
参数：hs : ¬BddAbove s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `csSup_of_not_bddAbove`：csSup_of_not_bddAbove (hs : ¬BddAbove s) : sSup s
 = sSup ∅
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `BddAbove.mono`：BddAbove.mono ⦃s t : Set α⦄ (h : s subseteq t) : BddAbove
 t -> BddAbove s
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
lemma csSup_eq_univ_of_not_bddAbove (hs : ¬BddAbove s) : sSup s = sSup univ := by
  rw [csSup_of_not_bddAbove hs, csSup_of_not_bddAbove (s := univ)]
  contrapose hs
  exact hs.mono (subset_univ _)

@[to_dual]
/-
**ciSup_eq_univ_of_not_bddAbove** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ciSup_eq_univ_of_not_bddAbove (hf : ¬BddAbove (range f)) : ⨆ i, f i = sSup
 univ
参数：hf : ¬BddAbove (range f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `csSup_eq_univ_of_not_bddAbove`：csSup_eq_univ_of_not_bddAbove (hs : ¬BddA
bove s) : sSup s = sSup univ
-/
lemma ciSup_eq_univ_of_not_bddAbove (hf : ¬BddAbove (range f)) : ⨆ i, f i = sSup univ :=
  csSup_eq_univ_of_not_bddAbove hf

/-- When every element of a set `s` is bounded by an element of a set `t`, and conversely, then
`s` and `t` have the same supremum. This holds even when the sets may be empty or unbounded. -/
@[to_dual
/-- When every element of a set `s` is bounded by an element of a set `t`, and conversely, then
`s` and `t` have the same infimum. This holds even when the sets may be empty or unbounded. -/]
/-
**csSup_eq_csSup_of_forall_exists_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：csSup_eq_csSup_of_forall_exists_le {s t : Set α} (hs : forall x in s, exis
ts y in t, x <= y) (ht : forall y in t, exists x in s, y <= x) : sSup s = sSup t
参数：hs : forall x in s, exists y in t, x <= y；ht : forall y in t, exists x in s, 
y <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `Set.eq_empty_of_forall_notMem`：eq_empty_of_forall_notMem (h : forall x, 
x ∉ s) : s = ∅
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `supSet_to_nonempty`：∀ (α : Type u_1) [SupSet α], Nonempty α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `csSup_le`：csSup_le (h₁ : s.Nonempty) (h₂ : forall b in s, b <= a) : sSup
 s <= a
· 使用定理 `le_csSup`：le_csSup (h₁ : BddAbove s) (h₂ : a in s) : a <= sSup s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `csSup_of_not_bddAbove`：csSup_of_not_bddAbove (hs : ¬BddAbove s) : sSup s
 = sSup ∅
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_or`：∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem csSup_eq_csSup_of_forall_exists_le {s t : Set α}
    (hs : ∀ x ∈ s, ∃ y ∈ t, x ≤ y) (ht : ∀ y ∈ t, ∃ x ∈ s, y ≤ x) :
    sSup s = sSup t := by
  rcases eq_empty_or_nonempty s with rfl | s_ne
  · have : t = ∅ := eq_empty_of_forall_notMem (fun y yt ↦ by simpa using ht y yt)
    rw [this]
  rcases eq_empty_or_nonempty t with rfl | t_ne
  · have : s = ∅ := eq_empty_of_forall_notMem (fun x xs ↦ by simpa using hs x xs)
    rw [this]
  by_cases B : BddAbove s ∨ BddAbove t
  · have Bs : BddAbove s := by
      rcases B with hB | ⟨b, hb⟩
      · exact hB
      · refine ⟨b, fun x hx ↦ ?_⟩
        rcases hs x hx with ⟨y, hy, hxy⟩
        exact hxy.trans (hb hy)
    have Bt : BddAbove t := by
      rcases B with ⟨b, hb⟩ | hB
      · refine ⟨b, fun y hy ↦ ?_⟩
        rcases ht y hy with ⟨x, hx, hyx⟩
        exact hyx.trans (hb hx)
      · exact hB
    apply le_antisymm
    · apply csSup_le s_ne (fun x hx ↦ ?_)
      rcases hs x hx with ⟨y, yt, hxy⟩
      exact hxy.trans (le_csSup Bt yt)
    · apply csSup_le t_ne (fun y hy ↦ ?_)
      rcases ht y hy with ⟨x, xs, hyx⟩
      exact hyx.trans (le_csSup Bs xs)
  · simp [csSup_of_not_bddAbove, (not_or.1 B).1, (not_or.1 B).2]

@[to_dual le_csInf_union]
/-
**csSup_union_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：csSup_union_le (s t : Set α) : sSup (s union t) <= sSup s ⊔ sSup t
参数：s t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.empty_union`：empty_union (a : Set α) : ∅ union a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.union_empty`：union_empty (a : Set α) : a union ∅ = a
-/
theorem csSup_union_le (s t : Set α) : sSup (s ∪ t) ≤ sSup s ⊔ sSup t := by
  rcases s.eq_empty_or_nonempty with (rfl | hs)
  · simp
  rcases t.eq_empty_or_nonempty with (rfl | ht)
  · simp
  by_cases BddAbove (s ∪ t) <;>
    grind [csSup_union, bddAbove_union, csSup_of_not_bddAbove]

@[to_dual]
/-
**sSup_iUnion_Iic** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sSup_iUnion_Iic (f : ι -> α) : sSup (⋃ (i : ι), Iic (f i)) = ⨆ i, f i
参数：f : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `csSup_eq_csSup_of_forall_exists_le`：csSup_eq_csSup_of_forall_exists_le {
s t : Set α} (hs : forall x in s, exists y in t, x <= y) (ht : forall y in t, ex
ists x in s, y <= x) : s…
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Set.mem_iUnion_of_mem`：mem_iUnion_of_mem {s : ι -> Set α} {a : α} (i : ι
) (ha : a in s i) : a in ⋃ i, s i
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma sSup_iUnion_Iic (f : ι → α) : sSup (⋃ (i : ι), Iic (f i)) = ⨆ i, f i := by
  apply csSup_eq_csSup_of_forall_exists_le
  · rintro x ⟨-, ⟨i, rfl⟩, hi⟩
    exact ⟨f i, mem_range_self _, hi⟩
  · rintro x ⟨i, rfl⟩
    exact ⟨f i, mem_iUnion_of_mem i le_rfl, le_rfl⟩

@[to_dual]
/-
**csSup_eq_top_of_top_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：csSup_eq_top_of_top_mem [OrderTop α] {s : Set α} (hs : ⊤ in s) : sSup s = 
⊤
参数：hs : ⊤ in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `le_csSup`：le_csSup (h₁ : BddAbove s) (h₂ : a in s) : a <= sSup s
· 使用定理 `OrderTop.bddAbove`：∀ {α : Type u_1} [inst : Preorder α] [OrderTop α] (s 
: Set α), BddAbove s
-/
theorem csSup_eq_top_of_top_mem [OrderTop α] {s : Set α} (hs : ⊤ ∈ s) : sSup s = ⊤ :=
  eq_top_iff.2 <| le_csSup (OrderTop.bddAbove s) hs

open Function

variable [WellFoundedLT α]
/-
**sInf_eq_argmin_on** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sInf_eq_argmin_on (hs : s.Nonempty) : sInf s = argminOn id s hs
参数：hs : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLeast.csInf_eq`：∀ {α : Type u_1} [inst : ConditionallyCompletePartialO
rderInf α] {s : Set α} {a : α}, IsLeast s a → sInf s = a
· 使用定理 `Function.argminOn_mem`：argminOn_mem (s : Set α) (hs : s.Nonempty) : argm
inOn f s hs in s
· 使用定理 `Function.argminOn_le`：argminOn_le (s : Set α) {a : α} (ha : a in s) : f 
(argminOn f s ⟨a, ha⟩) <= f a
-/
theorem sInf_eq_argmin_on (hs : s.Nonempty) : sInf s = argminOn id s hs :=
  IsLeast.csInf_eq ⟨argminOn_mem _ _ _, fun _ ha => argminOn_le id _ ha⟩
/-
**isLeast_csInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLeast_csInf (hs : s.Nonempty) : IsLeast s (sInf s)
参数：hs : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sInf_eq_argmin_on`：sInf_eq_argmin_on (hs : s.Nonempty) : sInf s = argmin
On id s hs
· 使用定理 `Function.argminOn_mem`：argminOn_mem (s : Set α) (hs : s.Nonempty) : argm
inOn f s hs in s
· 使用定理 `Function.argminOn_le`：argminOn_le (s : Set α) {a : α} (ha : a in s) : f 
(argminOn f s ⟨a, ha⟩) <= f a
-/
theorem isLeast_csInf (hs : s.Nonempty) : IsLeast s (sInf s) := by
  rw [sInf_eq_argmin_on hs]
  exact ⟨argminOn_mem _ _ _, fun a ha => argminOn_le id _ ha⟩
/-
**le_csInf_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_csInf_iff' (hs : s.Nonempty) : b <= sInf s ↔ b in lowerBounds s
参数：hs : s.Nonempty。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_isGLB_iff`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α} {a b : α}
, IsGLB s a → (b ≤ a ↔ b ∈ lowerBounds s)
· 使用定理 `IsLeast.isGLB`：IsLeast.isGLB (h : IsLeast s a) : IsGLB s a
· 使用定理 `isLeast_csInf`：isLeast_csInf (hs : s.Nonempty) : IsLeast s (sInf s)
-/
theorem le_csInf_iff' (hs : s.Nonempty) : b ≤ sInf s ↔ b ∈ lowerBounds s :=
  le_isGLB_iff (isLeast_csInf hs).isGLB
/-
**csInf_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：csInf_mem (hs : s.Nonempty) : sInf s in s
参数：hs : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `isLeast_csInf`：isLeast_csInf (hs : s.Nonempty) : IsLeast s (sInf s)
-/
theorem csInf_mem (hs : s.Nonempty) : sInf s ∈ s :=
  (isLeast_csInf hs).1
/-
**csInf_eq_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：csInf_eq_iff (hs : s.Nonempty) (n : α) : sInf s = n ↔ n in s ∧ forall a in
 s, n <= a
参数：hs : s.Nonempty；n : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `supSet_to_nonempty`：∀ (α : Type u_1) [SupSet α], Nonempty α
· 使用定理 `csInf_mem`：csInf_mem (hs : s.Nonempty) : sInf s in s
· 使用定理 `csInf_le`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s : 
Set α} {a : α}, BddBelow s → a ∈ s → sInf s ≤ a
· 使用定理 `OrderBot.bddBelow`：∀ {α : Type u_1} [inst : Preorder α] [OrderBot α] (s 
: Set α), BddBelow s
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_csInf`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s : 
Set α} {a : α}, s.Nonempty → (∀ b ∈ s, a ≤ b) → a ≤ sInf s
-/
lemma csInf_eq_iff (hs : s.Nonempty) (n : α) :
     sInf s = n ↔ n ∈ s ∧ ∀ a ∈ s, n ≤ a := by
  have : OrderBot α := WellFoundedLT.toOrderBot α
  constructor
  · intro rfl
    exact ⟨csInf_mem hs, fun _ ↦ csInf_le (OrderBot.bddBelow s)⟩
  · intro ⟨hn, hle⟩
    exact le_antisymm (csInf_le (OrderBot.bddBelow s) hn) (le_csInf hs hle)
/-
**MonotoneOn.map_csInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonotoneOn.map_csInf {β : Type*} [ConditionallyCompleteLattice β] {f : α -
> β} (hf : MonotoneOn f s) (hs : s.Nonempty) : f (sInf s) = sInf (f '' s)
参数：hf : MonotoneOn f s；hs : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLeast.csInf_eq`：∀ {α : Type u_1} [inst : ConditionallyCompletePartialO
rderInf α] {s : Set α} {a : α}, IsLeast s a → sInf s = a
· 使用定理 `MonotoneOn.map_isLeast`：map_isLeast (Hf : MonotoneOn f t) (Ha : IsLeast 
t a) : IsLeast (f '' t) (f a)
· 使用定理 `isLeast_csInf`：isLeast_csInf (hs : s.Nonempty) : IsLeast s (sInf s)
-/
theorem MonotoneOn.map_csInf {β : Type*} [ConditionallyCompleteLattice β] {f : α → β}
    (hf : MonotoneOn f s) (hs : s.Nonempty) : f (sInf s) = sInf (f '' s) :=
  (hf.map_isLeast (isLeast_csInf hs)).csInf_eq.symm
/-
**Monotone.map_csInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.map_csInf {β : Type*} [ConditionallyCompleteLattice β] {f : α -> 
β} (hf : Monotone f) (hs : s.Nonempty) : f (sInf s) = sInf (f '' s)
参数：hf : Monotone f；hs : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLeast.csInf_eq`：∀ {α : Type u_1} [inst : ConditionallyCompletePartialO
rderInf α] {s : Set α} {a : α}, IsLeast s a → sInf s = a
· 使用定理 `Monotone.map_isLeast`：map_isLeast (Ha : IsLeast s a) : IsLeast (f '' s) 
(f a)
· 使用定理 `isLeast_csInf`：isLeast_csInf (hs : s.Nonempty) : IsLeast s (sInf s)
-/
theorem Monotone.map_csInf {β : Type*} [ConditionallyCompleteLattice β] {f : α → β}
    (hf : Monotone f) (hs : s.Nonempty) : f (sInf s) = sInf (f '' s) :=
  (hf.map_isLeast (isLeast_csInf hs)).csInf_eq.symm

end ConditionallyCompleteLinearOrder

/-!
### Lemmas about a conditionally complete linear order with bottom element

In this case we have `Sup ∅ = ⊥`, so we can drop some `Nonempty`/`Set.Nonempty` assumptions.
-/


section ConditionallyCompleteLinearOrderBot

@[simp]
/-
**csInf_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：csInf_univ [ConditionallyCompleteLattice α] [OrderBot α] : sInf (univ : Se
t α) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLeast.csInf_eq`：∀ {α : Type u_1} [inst : ConditionallyCompletePartialO
rderInf α] {s : Set α} {a : α}, IsLeast s a → sInf s = a
· 使用定理 `isLeast_univ`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : OrderBot α]
, IsLeast Set.univ ⊥
-/
theorem csInf_univ [ConditionallyCompleteLattice α] [OrderBot α] : sInf (univ : Set α) = ⊥ :=
  isLeast_univ.csInf_eq

variable [ConditionallyCompleteLinearOrderBot α] {s : Set α} {a : α}

@[simp]
/-
**csSup_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：csSup_empty : (sSup ∅ : α) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConditionallyCompleteLinearOrderBot.csSup_empty`：∀ {α : Type u_5} [self 
: ConditionallyCompleteLinearOrderBot α], sSup ∅ = ⊥
-/
theorem csSup_empty : (sSup ∅ : α) = ⊥ :=
  ConditionallyCompleteLinearOrderBot.csSup_empty
/-
**isLUB_csSup'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLUB_csSup' {s : Set α} (hs : BddAbove s) : IsLUB s (sSup s)
参数：hs : BddAbove s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `csSup_empty`：csSup_empty : (sSup ∅ : α) = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isLUB_csSup`：isLUB_csSup (hn : s.Nonempty) (hb : BddAbove s
-/
theorem isLUB_csSup' {s : Set α} (hs : BddAbove s) : IsLUB s (sSup s) := by
  rcases eq_empty_or_nonempty s with (rfl | hne)
  · simp only [csSup_empty, isLUB_empty]
  · exact isLUB_csSup hne hs

/-- In conditionally complete orders with a bottom element, the nonempty condition can be omitted
from `csSup_le_iff`. -/
/-
**csSup_le_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：csSup_le_iff' {s : Set α} (hs : BddAbove s) {a : α} : sSup s <= a ↔ forall
 x in s, x <= a
参数：hs : BddAbove s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isLUB_le_iff`：isLUB_le_iff (h : IsLUB s a) : a <= b ↔ b in upperBounds s
· 使用定理 `isLUB_csSup'`：isLUB_csSup' {s : Set α} (hs : BddAbove s) : IsLUB s (sSup
 s)

--- 原说明 ---
In conditionally complete orders with a bottom element, the nonempty condition c
an be omitted
from `csSup_le_iff`.
-/
theorem csSup_le_iff' {s : Set α} (hs : BddAbove s) {a : α} : sSup s ≤ a ↔ ∀ x ∈ s, x ≤ a :=
  isLUB_le_iff (isLUB_csSup' hs)
/-
**csSup_le'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：csSup_le' {s : Set α} {a : α} (h : a in upperBounds s) : sSup s <= a
参数：h : a in upperBounds s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `csSup_le_iff'`：csSup_le_iff' {s : Set α} (hs : BddAbove s) {a : α} : sSu
p s <= a ↔ forall x in s, x <= a
-/
theorem csSup_le' {s : Set α} {a : α} (h : a ∈ upperBounds s) : sSup s ≤ a :=
  (csSup_le_iff' ⟨a, h⟩).2 h

/-- In conditionally complete orders with a bottom element, the nonempty condition can be omitted
from `lt_csSup_iff`. -/
/-
**lt_csSup_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lt_csSup_iff' (hb : BddAbove s) : a < sSup s ↔ exists b in s, a < b
参数：hb : BddAbove s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `csSup_le_iff'`：csSup_le_iff' {s : Set α} (hs : BddAbove s) {a : α} : sSu
p s <= a ↔ forall x in s, x <= a

--- 原说明 ---
In conditionally complete orders with a bottom element, the nonempty condition c
an be omitted
from `lt_csSup_iff`.
-/
theorem lt_csSup_iff' (hb : BddAbove s) : a < sSup s ↔ ∃ b ∈ s, a < b := by
  simpa only [not_le, not_forall₂, exists_prop] using (csSup_le_iff' hb).not
/-
**le_csSup_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_csSup_iff' {s : Set α} {a : α} (h : BddAbove s) : a <= sSup s ↔ forall 
b, b in upperBounds s -> a <= b
参数：h : BddAbove s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `csSup_le'`：csSup_le' {s : Set α} {a : α} (h : a in upperBounds s) : sSup
 s <= a
· 使用定理 `le_csSup`：le_csSup (h₁ : BddAbove s) (h₂ : a in s) : a <= sSup s
-/
theorem le_csSup_iff' {s : Set α} {a : α} (h : BddAbove s) :
    a ≤ sSup s ↔ ∀ b, b ∈ upperBounds s → a ≤ b :=
  ⟨fun h _ hb => le_trans h (csSup_le' hb), fun hb => hb _ fun _ => le_csSup h⟩
/-
**le_csInf_iff''** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_csInf_iff'' {s : Set α} {a : α} (ne : s.Nonempty) : a <= sInf s ↔ foral
l b : α, b in s -> a <= b
参数：ne : s.Nonempty。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_csInf_iff`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {
s : Set α} {a : α},   BddBelow s → s.Nonempty → (a ≤ sInf s ↔ ∀ b ∈ s, a ≤ b)
· 使用定理 `OrderBot.bddBelow`：∀ {α : Type u_1} [inst : Preorder α] [OrderBot α] (s 
: Set α), BddBelow s
-/
theorem le_csInf_iff'' {s : Set α} {a : α} (ne : s.Nonempty) :
    a ≤ sInf s ↔ ∀ b : α, b ∈ s → a ≤ b :=
  le_csInf_iff (OrderBot.bddBelow _) ne
/-
**csInf_le'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：csInf_le' (h : a in s) : sInf s <= a
参数：h : a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `csInf_le`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s : 
Set α} {a : α}, BddBelow s → a ∈ s → sInf s ≤ a
· 使用定理 `OrderBot.bddBelow`：∀ {α : Type u_1} [inst : Preorder α] [OrderBot α] (s 
: Set α), BddBelow s
-/
theorem csInf_le' (h : a ∈ s) : sInf s ≤ a := csInf_le (OrderBot.bddBelow _) h
/-
**exists_lt_of_lt_csSup'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_lt_of_lt_csSup' {s : Set α} {a : α} (h : a < sSup s) : exists b in 
s, a < b
参数：h : a < sSup s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `csSup_le'`：csSup_le' {s : Set α} {a : α} (h : a in upperBounds s) : sSup
 s <= a
-/
theorem exists_lt_of_lt_csSup' {s : Set α} {a : α} (h : a < sSup s) : ∃ b ∈ s, a < b := by
  contrapose! h
  exact csSup_le' h
/-
**notMem_of_lt_csInf'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：notMem_of_lt_csInf' {x : α} {s : Set α} (h : x < sInf s) : x ∉ s
参数：h : x < sInf s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `notMem_of_lt_csInf`：notMem_of_lt_csInf {x : α} {s : Set α} (h : x < sInf
 s) (hs : BddBelow s) : x ∉ s
· 使用定理 `OrderBot.bddBelow`：∀ {α : Type u_1} [inst : Preorder α] [OrderBot α] (s 
: Set α), BddBelow s
-/
theorem notMem_of_lt_csInf' {x : α} {s : Set α} (h : x < sInf s) : x ∉ s :=
  notMem_of_lt_csInf h (OrderBot.bddBelow s)

@[gcongr mid]
/-
**csInf_le_csInf'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：csInf_le_csInf' {s t : Set α} (h₁ : t.Nonempty) (h₂ : t subseteq s) : sInf
 s <= sInf t
参数：h₁ : t.Nonempty；h₂ : t subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `csInf_le_csInf`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α]
 {s t : Set α},   BddBelow t → s.Nonempty → s ⊆ t → sInf t ≤ sInf s
· 使用定理 `OrderBot.bddBelow`：∀ {α : Type u_1} [inst : Preorder α] [OrderBot α] (s 
: Set α), BddBelow s
-/
theorem csInf_le_csInf' {s t : Set α} (h₁ : t.Nonempty) (h₂ : t ⊆ s) : sInf s ≤ sInf t :=
  csInf_le_csInf (OrderBot.bddBelow s) h₁ h₂

@[gcongr mid]
/-
**csSup_le_csSup'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：csSup_le_csSup' {s t : Set α} (h₁ : BddAbove t) (h₂ : s subseteq t) : sSup
 s <= sSup t
参数：h₁ : BddAbove t；h₂ : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `csSup_empty`：csSup_empty : (sSup ∅ : α) = ⊥
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `csSup_le_csSup`：csSup_le_csSup (ht : BddAbove t) (hs : s.Nonempty) (h : 
s subseteq t) : sSup s <= sSup t
-/
theorem csSup_le_csSup' {s t : Set α} (h₁ : BddAbove t) (h₂ : s ⊆ t) : sSup s ≤ sSup t := by
  rcases eq_empty_or_nonempty s with rfl | h
  · rw [csSup_empty]
    exact bot_le
  · exact csSup_le_csSup h₁ h h₂

variable {t : Set α}
/-
**csSup_union'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：csSup_union' (hs : BddAbove s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.empty_union`：empty_union (a : Set α) : ∅ union a = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `csSup_empty`：csSup_empty : (sSup ∅ : α) = ⊥
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLUB.csSup_eq`：IsLUB.csSup_eq (H : IsLUB s a) (ne : s.Nonempty) : sSup 
s = a
· 使用定理 `IsLUB.union`：IsLUB.union [SemilatticeSup γ] {a b : γ} {s t : Set γ} (hs 
: IsLUB s a) (ht : IsLUB t b) : IsLUB (s union t) (a ⊔ b)
· 使用定理 `isLUB_csSup'`：isLUB_csSup' {s : Set α} (hs : BddAbove s) : IsLUB s (sSup
 s)
· 使用定理 `Set.Nonempty.inl`：∀ {α : Type u} {s t : Set α}, s.Nonempty → (s ∪ t).Non
empty
-/
theorem csSup_union' (hs : BddAbove s := by bddDefault) (ht : BddAbove t := by bddDefault) :
    sSup (s ∪ t) = sSup s ⊔ sSup t := by
  rcases s.eq_empty_or_nonempty with (rfl | hne)
  · simp
  exact (isLUB_csSup' hs |>.union <| isLUB_csSup' ht).csSup_eq hne.inl
/-
**csSup_inter_le'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：csSup_inter_le' (hs : BddAbove s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `csSup_le'`：csSup_le' {s : Set α} {a : α} (h : a in upperBounds s) : sSup
 s <= a
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
· 使用定理 `le_csSup`：le_csSup (h₁ : BddAbove s) (h₂ : a in s) : a <= sSup s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem csSup_inter_le' (hs : BddAbove s := by bddDefault) (ht : BddAbove t := by bddDefault) :
    sSup (s ∩ t) ≤ sSup s ⊓ sSup t :=
  csSup_le' fun _ hx ↦ le_inf (le_csSup hs hx.left) (le_csSup ht hx.right)
/-
**csSup_insert'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：csSup_insert' (hs : BddAbove s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLUB.csSup_eq`：IsLUB.csSup_eq (H : IsLUB s a) (ne : s.Nonempty) : sSup 
s = a
· 使用定理 `IsLUB.insert`：∀ {γ : Type u_3} [inst : SemilatticeSup γ] (a : γ) {b : γ}
 {s : Set γ}, IsLUB s b → IsLUB (insert a s) (a ⊔ b)
· 使用定理 `isLUB_csSup'`：isLUB_csSup' {s : Set α} (hs : BddAbove s) : IsLUB s (sSup
 s)
· 使用定理 `Set.insert_nonempty`：insert_nonempty (a : α) (s : Set α) : (insert a s).
Nonempty
-/
theorem csSup_insert' (hs : BddAbove s := by bddDefault) : sSup (insert a s) = a ⊔ sSup s :=
  isLUB_csSup' hs |>.insert a |>.csSup_eq <| insert_nonempty a s

end ConditionallyCompleteLinearOrderBot

namespace WithTop

variable [ConditionallyCompleteLinearOrderBot α]

/-- The `sSup` of a non-empty set is its least upper bound for a conditionally
complete lattice with a top. -/
@[to_dual]
/-
**WithTop.isLUB_sSup'** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：isLUB_sSup' {β : Type*} [ConditionallyCompleteLattice β] {s : Set (WithTop
 β)} (hs : s.Nonempty) : IsLUB s (sSup s)
参数：WithTop β；hs : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `WithTop.coe_le_coe`：∀ {α : Type u_1} {a b : α} [inst : LE α], ↑b ≤ ↑a ↔ 
b ≤ a
· 使用定理 `le_csSup`：le_csSup (h₁ : BddAbove s) (h₂ : a in s) : a <= sSup s
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `WithTop.not_top_le_coe`：∀ {α : Type u_1} [inst : LE α] (a : α), ¬⊤ ≤ ↑a
· 使用定理 `csSup_le`：csSup_le (h₁ : s.Nonempty) (h₂ : forall b in s, b <= a) : sSup
 s <= a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b

--- 原说明 ---
The `sSup` of a non-empty set is its least upper bound for a conditionally
complete lattice with a top.
-/
theorem isLUB_sSup' {β : Type*} [ConditionallyCompleteLattice β] {s : Set (WithTop β)}
    (hs : s.Nonempty) : IsLUB s (sSup s) := by
  classical
  constructor
  · change ite _ _ _ ∈ _
    split_ifs with h₁ h₂
    · intro _ _
      exact le_top
    · rintro (⟨⟩ | a) ha
      · contradiction
      apply coe_le_coe.2
      exact le_csSup h₂ ha
    · intro _ _
      exact le_top
  · change ite _ _ _ ∈ _
    split_ifs with h₁ h₂
    · rintro (⟨⟩ | a) ha
      · exact le_rfl
      · exact False.elim (not_top_le_coe a (ha h₁))
    · rintro (⟨⟩ | b) hb
      · exact le_top
      refine coe_le_coe.2 (csSup_le ?_ ?_)
      · rcases hs with ⟨⟨⟩ | b, hb⟩
        · exact absurd hb h₁
        · exact ⟨b, hb⟩
      · intro a ha
        exact coe_le_coe.1 (hb ha)
    · rintro (⟨⟩ | b) hb
      · exact le_rfl
      · exfalso
        apply h₂
        use b
        intro a ha
        exact coe_le_coe.1 (hb ha)
/-
**WithTop.isLUB_sSup** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：isLUB_sSup (s : Set (WithTop α)) : IsLUB s (sSup s)
参数：s : Set (WithTop α)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `bot_nonempty`：∀ (α : Type u_1) [Bot α], Nonempty α
· 使用定理 `csSup_empty`：csSup_empty : (sSup ∅ : α) = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithTop.isLUB_sSup'`：isLUB_sSup' {β : Type*} [ConditionallyCompleteLatti
ce β] {s : Set (WithTop β)} (hs : s.Nonempty) : IsLUB s (sSup s)
-/
theorem isLUB_sSup (s : Set (WithTop α)) : IsLUB s (sSup s) := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp [sSup]
  · exact isLUB_sSup' hs

/-- The `sInf` of a bounded-below set is its greatest lower bound for a conditionally
complete lattice with a top. -/
@[to_dual]
/-
**WithTop.isGLB_sInf'** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：isGLB_sInf' {β : Type*} [ConditionallyCompleteLattice β] {s : Set (WithTop
 β)} (hs : BddBelow s) : IsGLB s (sInf s)
参数：WithTop β；hs : BddBelow s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `WithTop.coe_le_coe`：∀ {α : Type u_1} {a b : α} [inst : LE α], ↑b ≤ ↑a ↔ 
b ≤ a
· 使用定理 `csInf_le`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s : 
Set α} {a : α}, BddBelow s → a ∈ s → sInf s ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_csInf`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s : 
Set α} {a : α}, s.Nonempty → (∀ b ∈ s, a ≤ b) → a ≤ sInf s
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `Set.not_nonempty_iff_eq_empty`：not_nonempty_iff_eq_empty : ¬s.Nonempty ↔
 s = ∅

--- 原说明 ---
The `sInf` of a bounded-below set is its greatest lower bound for a conditionall
y
complete lattice with a top.
-/
theorem isGLB_sInf' {β : Type*} [ConditionallyCompleteLattice β] {s : Set (WithTop β)}
    (hs : BddBelow s) : IsGLB s (sInf s) := by
  classical
  constructor
  · change ite _ _ _ ∈ _
    simp only [hs, not_true_eq_false, or_false]
    split_ifs with h
    · intro a ha
      exact top_le_iff.2 (Set.mem_singleton_iff.1 (h ha))
    · rintro (⟨⟩ | a) ha
      · exact le_top
      refine coe_le_coe.2 (csInf_le ?_ ha)
      rcases hs with ⟨⟨⟩ | b, hb⟩
      · exfalso
        apply h
        intro c hc
        rw [mem_singleton_iff, ← top_le_iff]
        exact hb hc
      use b
      intro c hc
      exact coe_le_coe.1 (hb hc)
  · change ite _ _ _ ∈ _
    simp only [hs, not_true_eq_false, or_false]
    split_ifs with h
    · intro _ _
      exact le_top
    · rintro (⟨⟩ | a) ha
      · exfalso
        apply h
        intro b hb
        exact Set.mem_singleton_iff.2 (top_le_iff.1 (ha hb))
      · refine coe_le_coe.2 (le_csInf ?_ ?_)
        · classical
            contrapose! h
            rintro (⟨⟩ | a) ha
            · exact mem_singleton ⊤
            · exact (not_nonempty_iff_eq_empty.2 h ⟨a, ha⟩).elim
        · intro b hb
          rw [← coe_le_coe]
          exact ha hb
/-
**WithTop.isGLB_sInf** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：isGLB_sInf (s : Set (WithTop α)) : IsGLB s (sInf s)
参数：s : Set (WithTop α)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.isGLB_sInf'`：isGLB_sInf' {β : Type*} [ConditionallyCompleteLatti
ce β] {s : Set (WithTop β)} (hs : BddBelow s) : IsGLB s (sInf s)
· 使用定理 `OrderBot.bddBelow`：∀ {α : Type u_1} [inst : Preorder α] [OrderBot α] (s 
: Set α), BddBelow s
-/
theorem isGLB_sInf (s : Set (WithTop α)) : IsGLB s (sInf s) := by
  by_cases hs : BddBelow s
  · exact isGLB_sInf' hs
  · exact isGLB_sInf' (OrderBot.bddBelow _)
/-
**WithTop.** 是 Mathlib 中的一个实例，位于命名空间 `WithTop`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : CompleteLinearOrder (WithTop α) where
  __ := linearOrder
  __ := linearOrder.toBiheytingAlgebra
  isLUB_sSup := isLUB_sSup
  isGLB_sInf := isGLB_sInf

/-- A version of `WithTop.coe_sSup'` with a more convenient but less general statement. -/
@[norm_cast]
/-
**WithTop.coe_sSup** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：coe_sSup {s : Set α} (hb : BddAbove s) : ↑(sSup s) = (⨆ a in s, ↑a : WithT
op α)
参数：hb : BddAbove s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithTop.coe_sSup'`：coe_sSup' [SupSet α] {s : Set α} (hs : BddAbove s) : 
↑(sSup s) = (sSup ((fun (a : α) => ↑a) '' s) : WithTop α)
· 使用定理 `sSup_image`：sSup_image {s : Set β} {f : β -> α} : sSup (f '' s) = ⨆ a in
 s, f a

--- 原说明 ---
A version of `WithTop.coe_sSup'` with a more convenient but less general stateme
nt.
-/
theorem coe_sSup {s : Set α} (hb : BddAbove s) : ↑(sSup s) = (⨆ a ∈ s, ↑a : WithTop α) := by
  rw [coe_sSup' hb, sSup_image]

/-- A version of `WithTop.coe_sInf'` with a more convenient but less general statement. -/
@[norm_cast]
/-
**WithTop.coe_sInf** 是 Mathlib 中的一个定理，位于命名空间 `WithTop`。
形式化陈述：coe_sInf {s : Set α} (hs : s.Nonempty) (h's : BddBelow s) : ↑(sInf s) = (⨅
 a in s, ↑a : WithTop α)
参数：hs : s.Nonempty；h's : BddBelow s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithTop.coe_sInf'`：WithTop.coe_sInf' [InfSet α] {s : Set α} (hs : s.None
mpty) (h's : BddBelow s) : ↑(sInf s) = (sInf ((fun (a : α) => ↑a) '' s) : WithTo
p α)
· 使用定理 `sInf_image`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLattice α] {
s : Set β} {f : β → α}, sInf (f '' s) = ⨅ a ∈ s, f a

--- 原说明 ---
A version of `WithTop.coe_sInf'` with a more convenient but less general stateme
nt.
-/
theorem coe_sInf {s : Set α} (hs : s.Nonempty) (h's : BddBelow s) :
    ↑(sInf s) = (⨅ a ∈ s, ↑a : WithTop α) := by
  rw [coe_sInf' hs h's, sInf_image]

end WithTop

namespace Monotone

variable [ConditionallyCompleteLattice β]

section Preorder

variable [Preorder α] {f : α → β} (h_mono : Monotone f)
include h_mono

/-! A monotone function into a conditionally complete lattice preserves the ordering properties of
`sSup` and `sInf`. -/

@[to_dual csInf_image_le]
/-
**Monotone.le_csSup_image** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：le_csSup_image {s : Set α} {c : α} (hcs : c in s) (h_bdd : BddAbove s) : f
 c <= sSup (f '' s)
参数：hcs : c in s；h_bdd : BddAbove s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_csSup`：le_csSup (h₁ : BddAbove s) (h₂ : a in s) : a <= sSup s
· 使用定理 `Monotone.map_bddAbove`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [
inst_1 : Preorder β] {f : α → β},   Monotone f → ∀ {s : Set α}, BddAbove s → Bdd
Above (f ''…
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a

--- 原说明 ---
A monotone function into a conditionally complete lattice preserves the ordering
 properties of
`sSup` and `sInf`.
-/
theorem le_csSup_image {s : Set α} {c : α} (hcs : c ∈ s) (h_bdd : BddAbove s) :
    f c ≤ sSup (f '' s) :=
  le_csSup (map_bddAbove h_mono h_bdd) (mem_image_of_mem f hcs)

@[to_dual le_csInf_image]
/-
**Monotone.csSup_image_le** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：csSup_image_le {s : Set α} (hs : s.Nonempty) {B : α} (hB : B in upperBound
s s) : sSup (f '' s) <= f B
参数：hs : s.Nonempty；hB : B in upperBounds s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `csSup_le`：csSup_le (h₁ : s.Nonempty) (h₂ : forall b in s, b <= a) : sSup
 s <= a
· 使用定理 `Set.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set
 α}, s.Nonempty → (f '' s).Nonempty
· 使用定理 `Monotone.mem_upperBounds_image`：mem_upperBounds_image (Ha : a in upperBo
unds s) : f a in upperBounds (f '' s)
-/
theorem csSup_image_le {s : Set α} (hs : s.Nonempty) {B : α} (hB : B ∈ upperBounds s) :
    sSup (f '' s) ≤ f B :=
  csSup_le (Nonempty.image f hs) (h_mono.mem_upperBounds_image hB)

end Preorder

section ConditionallyCompleteLattice

variable [ConditionallyCompleteLattice α]
variable {f : α → β} {s : Set α} (hs : s.Nonempty) (hf : Monotone f)
include hs hf

@[to_dual map_csInf_le_csInf_image]
/-
**Monotone.csSup_image_le_map_csSup** 是 Mathlib 中的一个定理，位于命名空间 `Monotone`。
形式化陈述：csSup_image_le_map_csSup (hbdd : BddAbove s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.csSup_image_le`：csSup_image_le {s : Set α} (hs : s.Nonempty) {B
 : α} (hB : B in upperBounds s) : sSup (f '' s) <= f B
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `isLUB_csSup`：isLUB_csSup (hn : s.Nonempty) (hb : BddAbove s
-/
theorem csSup_image_le_map_csSup (hbdd : BddAbove s := by bddDefault) :
    sSup (f '' s) ≤ f (sSup s) :=
  csSup_image_le hf hs <| isLUB_csSup hs hbdd |>.left

end ConditionallyCompleteLattice

end Monotone

@[to_dual]
/-
**MonotoneOn.csInf_eq_of_subset_of_forall_exists_le** 是 Mathlib 中的一个引理，位于命名空间 ``
。
形式化陈述：MonotoneOn.csInf_eq_of_subset_of_forall_exists_le [Preorder α] [Conditiona
llyCompleteLattice β] {f : α -> β} {s t : Set α} (ht : BddBelow (f '' t)) (hf : 
MonotoneOn f t) (hst : s subseteq t) (h : forall y in t, exists x in s, x <= y) 
: sInf (f '' s) = sInf (f '' t)
参数：ht : BddBelow (f '' t)；hf : MonotoneOn f t；hst : s subseteq t；h : forall y in
 t, exists x in s, x <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_csInf`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s : 
Set α} {a : α}, s.Nonempty → (∀ b ∈ s, a ≤ b) → a ≤ sInf s
· 使用定理 `Set.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set
 α}, s.Nonempty → (f '' s).Nonempty
· 使用定理 `Set.Nonempty.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Nonempty → t.
Nonempty
· 使用定理 `csInf_le_of_le`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α]
 {s : Set α} {a b : α}, BddBelow s → b ∈ s → b ≤ a → sInf s ≤ a
· 使用定理 `BddBelow.mono`：∀ {α : Type u_1} [inst : Preorder α] ⦃s t : Set α⦄, s ⊆ t
 → BddBelow t → BddBelow s
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `csInf_le_csInf`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α]
 {s t : Set α},   BddBelow t → s.Nonempty → s ⊆ t → sInf t ≤ sInf s
-/
lemma MonotoneOn.csInf_eq_of_subset_of_forall_exists_le
    [Preorder α] [ConditionallyCompleteLattice β] {f : α → β}
    {s t : Set α} (ht : BddBelow (f '' t)) (hf : MonotoneOn f t)
    (hst : s ⊆ t) (h : ∀ y ∈ t, ∃ x ∈ s, x ≤ y) :
    sInf (f '' s) = sInf (f '' t) := by
  obtain rfl | hs := Set.eq_empty_or_nonempty s
  · obtain rfl : t = ∅ := by simpa [Set.eq_empty_iff_forall_notMem] using h
    rfl
  refine le_antisymm ?_ (by gcongr; exacts [ht, hs.image f])
  refine le_csInf ((hs.mono hst).image f) ?_
  simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  intro a ha
  obtain ⟨x, hxs, hxa⟩ := h a ha
  exact csInf_le_of_le (ht.mono (image_mono hst)) ⟨x, hxs, rfl⟩ (hf (hst hxs) ha hxa)

@[to_dual]
/-
**MonotoneOn.sInf_image_Icc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MonotoneOn.sInf_image_Icc [Preorder α] [ConditionallyCompleteLattice β] {f
 : α -> β} {a b : α} (hab : a <= b) (h' : MonotoneOn f (Icc a b)) : sInf (f '' I
cc a b) = f a
参数：hab : a <= b；h' : MonotoneOn f (Icc a b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGLB.csInf_eq`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α]
 {s : Set α} {a : α}, IsGLB s a → s.Nonempty → sInf s = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isGLB_iff_le_iff`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α} {a : 
α}, IsGLB s a ↔ ∀ (b : α), b ≤ a ↔ b ∈ lowerBounds s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.left_mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ∈ Se
t.Icc a b ↔ a ≤ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set
 α}, s.Nonempty → (f '' s).Nonempty
· 使用定理 `Set.nonempty_Icc`：nonempty_Icc : (Icc a b).Nonempty ↔ a <= b
-/
theorem MonotoneOn.sInf_image_Icc [Preorder α] [ConditionallyCompleteLattice β]
    {f : α → β} {a b : α} (hab : a ≤ b)
    (h' : MonotoneOn f (Icc a b)) : sInf (f '' Icc a b) = f a := by
  refine IsGLB.csInf_eq ?_ ((nonempty_Icc.mpr hab).image f)
  refine isGLB_iff_le_iff.mpr (fun b' ↦ ⟨?_, ?_⟩)
  · intro hb'
    rintro _ ⟨x, hx, rfl⟩
    exact hb'.trans <| h' (left_mem_Icc.mpr hab) hx hx.1
  · exact fun hb' ↦ hb' ⟨a, by simp [hab]⟩

@[to_dual]
/-
**AntitoneOn.sInf_image_Icc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AntitoneOn.sInf_image_Icc [Preorder α] [ConditionallyCompleteLattice β] {f
 : α -> β} {a b : α} (hab : a <= b) (h' : AntitoneOn f (Icc a b)) : sInf (f '' I
cc a b) = f b
参数：hab : a <= b；h' : AntitoneOn f (Icc a b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Icc_toDual`：Icc_toDual : Icc (toDual a) (toDual b) = ofDual ⁻¹' Icc 
b a
· 使用定理 `MonotoneOn.sInf_image_Icc`：MonotoneOn.sInf_image_Icc [Preorder α] [Condi
tionallyCompleteLattice β] {f : α -> β} {a b : α} (hab : a <= b) (h' : MonotoneO
n f (Icc a b)) …
· 使用定理 `AntitoneOn.dual_left`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [i
nst_1 : Preorder β] {f : α → β} {s : Set α},   AntitoneOn f s → MonotoneOn (f ∘ 
⇑OrderDual…
-/
theorem AntitoneOn.sInf_image_Icc [Preorder α] [ConditionallyCompleteLattice β]
    {f : α → β} {a b : α} (hab : a ≤ b)
    (h' : AntitoneOn f (Icc a b)) : sInf (f '' Icc a b) = f b := by
  have : Icc a b = Icc (α := αᵒᵈ) (toDual b) (toDual a) := by rw [Icc_toDual]; rfl
  rw [this] at h' ⊢
  exact h'.dual_left.sInf_image_Icc (α := αᵒᵈ) hab

/-!
### Supremum/infimum of `Set.image2`

A collection of lemmas showing what happens to the suprema/infima of `s` and `t` when mapped under
a binary function whose partial evaluations are lower/upper adjoints of Galois connections.
-/

section

variable [ConditionallyCompleteLattice α] [ConditionallyCompleteLattice β]
  [ConditionallyCompleteLattice γ] {s : Set α} {t : Set β}

variable {l u : α → β → γ} {l₁ u₁ : β → γ → α} {l₂ u₂ : α → γ → β}
to_dual_name_hint L U, L₁ U₁, L₂ U₂

@[to_dual]
/-
**csSup_image2_eq_csSup_csSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：csSup_image2_eq_csSup_csSup (h₁ : forall b, GaloisConnection (swap l b) (u
₁ b)) (h₂ : forall a, GaloisConnection (l a) (u₂ a)) (hs₀ : s.Nonempty) (hs₁ : B
ddAbove s) (ht₀ : t.Nonempty) (ht₁ : BddAbove t) : sSup (image2 l s t) = l (sSup
 s) (sSup t)
参数：h₁ : forall b, GaloisConnection (swap l b) (u₁ b)；h₂ : forall a, GaloisConnec
tion (l a) (u₂ a)；hs₀ : s.Nonempty；hs₁ : BddAbove s；ht₀ : t.Nonempty；ht₁ : BddAb
ove t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLUB.csSup_eq`：IsLUB.csSup_eq (H : IsLUB s a) (ne : s.Nonempty) : sSup 
s = a
· 使用定理 `isLUB_image2_of_isLUB_isLUB`：isLUB_image2_of_isLUB_isLUB (h₁ : forall b,
 GaloisConnection (swap l b) (u₁ b)) (h₂ : forall a, GaloisConnection (l a) (u₂ 
a)) (ha₀ : IsLUB …
· 使用定理 `isLUB_csSup`：isLUB_csSup (hn : s.Nonempty) (hb : BddAbove s
· 使用定理 `Set.Nonempty.image2`：∀ {α : Type u_1} {β : Type u_3} {γ : Type u_5} {f :
 α → β → γ} {s : Set α} {t : Set β},   s.Nonempty → t.Nonempty → (Set.image2 f s
 t).Nonem…
-/
theorem csSup_image2_eq_csSup_csSup (h₁ : ∀ b, GaloisConnection (swap l b) (u₁ b))
    (h₂ : ∀ a, GaloisConnection (l a) (u₂ a)) (hs₀ : s.Nonempty) (hs₁ : BddAbove s)
    (ht₀ : t.Nonempty) (ht₁ : BddAbove t) : sSup (image2 l s t) = l (sSup s) (sSup t) :=
  isLUB_image2_of_isLUB_isLUB h₁ h₂ (isLUB_csSup hs₀ hs₁) (isLUB_csSup ht₀ ht₁)
    |>.csSup_eq (hs₀.image2 ht₀)

@[to_dual]
/-
**csSup_image2_eq_csSup_csInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：csSup_image2_eq_csSup_csInf (h₁ : forall b, GaloisConnection (swap l b) (u
₁ b)) (h₂ : forall a, GaloisConnection (l a ∘ ofDual) (toDual ∘ u₂ a)) : s.Nonem
pty -> BddAbove s -> t.Nonempty -> BddBelow t -> sSup (image2 l s t) = l (sSup s
) (sInf t)
参数：h₁ : forall b, GaloisConnection (swap l b) (u₁ b)；h₂ : forall a, GaloisConnec
tion (l a ∘ ofDual) (toDual ∘ u₂ a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `csSup_image2_eq_csSup_csSup`：csSup_image2_eq_csSup_csSup (h₁ : forall b,
 GaloisConnection (swap l b) (u₁ b)) (h₂ : forall a, GaloisConnection (l a) (u₂ 
a)) (hs₀ : s.None…
-/
theorem csSup_image2_eq_csSup_csInf (h₁ : ∀ b, GaloisConnection (swap l b) (u₁ b))
    (h₂ : ∀ a, GaloisConnection (l a ∘ ofDual) (toDual ∘ u₂ a)) :
    s.Nonempty → BddAbove s → t.Nonempty → BddBelow t → sSup (image2 l s t) = l (sSup s) (sInf t) :=
  csSup_image2_eq_csSup_csSup (β := βᵒᵈ) h₁ h₂

@[to_dual]
/-
**csSup_image2_eq_csInf_csSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：csSup_image2_eq_csInf_csSup (h₁ : forall b, GaloisConnection (swap l b ∘ o
fDual) (toDual ∘ u₁ b)) (h₂ : forall a, GaloisConnection (l a) (u₂ a)) : s.Nonem
pty -> BddBelow s -> t.Nonempty -> BddAbove t -> sSup (image2 l s t) = l (sInf s
) (sSup t)
参数：h₁ : forall b, GaloisConnection (swap l b ∘ ofDual) (toDual ∘ u₁ b)；h₂ : fora
ll a, GaloisConnection (l a) (u₂ a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `csSup_image2_eq_csSup_csSup`：csSup_image2_eq_csSup_csSup (h₁ : forall b,
 GaloisConnection (swap l b) (u₁ b)) (h₂ : forall a, GaloisConnection (l a) (u₂ 
a)) (hs₀ : s.None…
-/
theorem csSup_image2_eq_csInf_csSup (h₁ : ∀ b, GaloisConnection (swap l b ∘ ofDual) (toDual ∘ u₁ b))
    (h₂ : ∀ a, GaloisConnection (l a) (u₂ a)) :
    s.Nonempty → BddBelow s → t.Nonempty → BddAbove t → sSup (image2 l s t) = l (sInf s) (sSup t) :=
  csSup_image2_eq_csSup_csSup (α := αᵒᵈ) h₁ h₂

@[to_dual]
/-
**csSup_image2_eq_csInf_csInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：csSup_image2_eq_csInf_csInf (h₁ : forall b, GaloisConnection (swap l b ∘ o
fDual) (toDual ∘ u₁ b)) (h₂ : forall a, GaloisConnection (l a ∘ ofDual) (toDual 
∘ u₂ a)) : s.Nonempty -> BddBelow s -> t.Nonempty -> BddBelow t -> sSup (image2 
l s t) = l (sInf s) (sInf t)
参数：h₁ : forall b, GaloisConnection (swap l b ∘ ofDual) (toDual ∘ u₁ b)；h₂ : fora
ll a, GaloisConnection (l a ∘ ofDual) (toDual ∘ u₂ a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `csSup_image2_eq_csSup_csSup`：csSup_image2_eq_csSup_csSup (h₁ : forall b,
 GaloisConnection (swap l b) (u₁ b)) (h₂ : forall a, GaloisConnection (l a) (u₂ 
a)) (hs₀ : s.None…
-/
theorem csSup_image2_eq_csInf_csInf (h₁ : ∀ b, GaloisConnection (swap l b ∘ ofDual) (toDual ∘ u₁ b))
    (h₂ : ∀ a, GaloisConnection (l a ∘ ofDual) (toDual ∘ u₂ a)) :
    s.Nonempty → BddBelow s → t.Nonempty → BddBelow t → sSup (image2 l s t) = l (sInf s) (sInf t) :=
  csSup_image2_eq_csSup_csSup (α := αᵒᵈ) (β := βᵒᵈ) h₁ h₂

end

section WithTopBot

/-!
### Complete lattice structure on `WithTop (WithBot α)`

If `α` is a `ConditionallyCompleteLattice`, then we show that `WithTop α` and `WithBot α`
also inherit the structure of conditionally complete lattices. Furthermore, we show
that `WithTop (WithBot α)` and `WithBot (WithTop α)` naturally inherit the structure of a
complete lattice. Note that for `α` a conditionally complete lattice, `sSup` and `sInf` both return
junk values for sets which are empty or unbounded. The extension of `sSup` to `WithTop α` fixes
the unboundedness problem and the extension to `WithBot α` fixes the problem with
the empty set.

This result can be used to show that the extended reals `[-∞, ∞]` are a complete linear order.
-/


/-- Adding a top element to a conditionally complete lattice
gives a conditionally complete lattice -/
@[to_dual
/-- Adding a bottom element to a conditionally complete lattice
gives a conditionally complete lattice -/]
/-
**WithTop.conditionallyCompleteLattice** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：WithTop.conditionallyCompleteLattice {α : Type*} [ConditionallyCompleteLat
tice α] : ConditionallyCompleteLattice (WithTop α) where isLUB_csSup _ hS _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.isLUB_sSup'`：isLUB_sSup' {β : Type*} [ConditionallyCompleteLatti
ce β] {s : Set (WithTop β)} (hs : s.Nonempty) : IsLUB s (sSup s)
· 使用定理 `WithTop.isGLB_sInf'`：isGLB_sInf' {β : Type*} [ConditionallyCompleteLatti
ce β] {s : Set (WithTop β)} (hs : BddBelow s) : IsGLB s (sInf s)
-/
noncomputable instance WithTop.conditionallyCompleteLattice {α : Type*}
    [ConditionallyCompleteLattice α] : ConditionallyCompleteLattice (WithTop α) where
  isLUB_csSup _ hS _ := WithTop.isLUB_sSup' hS
  isGLB_csInf _ _ hS := WithTop.isGLB_sInf' hS

@[to_dual]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [CompleteLattice α] : CompleteLattice (WithTop α) where
  isLUB_sSup s := ⟨fun _ ↦ le_csSup (OrderTop.bddAbove _), fun _ has ↦
    s.eq_empty_or_nonempty.elim (by simp [·, WithTop.sSup_empty]) (csSup_le · has)⟩
  isGLB_sInf s := ⟨fun _ ↦ csInf_le (OrderBot.bddBelow _), fun _ hsa ↦
    s.eq_empty_or_nonempty.elim (by simp [·]) (le_csInf · hsa)⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [CompleteLinearOrder α] : CompleteLinearOrder (WithBot α) where
  __ := WithBot.linearOrder
  __ := WithBot.linearOrder.toBiheytingAlgebra
  __ := show CompleteLattice (WithBot α) from inferInstance
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [ConditionallyCompleteLinearOrder α] :
    ConditionallyCompleteLinearOrder (WithTop α) where
  le_total
  toDecidableLE := inferInstance
  toDecidableEq := inferInstance
  toDecidableLT := inferInstance
  csSup_of_not_bddAbove s := absurd <| OrderTop.bddAbove s
  csInf_of_not_bddBelow s h := by simp [h]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [ConditionallyCompleteLinearOrder α] :
    ConditionallyCompleteLinearOrderBot (WithBot α) where
  le_total
  toDecidableLE := inferInstance
  toDecidableEq := inferInstance
  toDecidableLT := inferInstance
  csSup_of_not_bddAbove s h := by simp [h]
  csInf_of_not_bddBelow s := absurd <| OrderBot.bddBelow s
  csSup_empty := WithBot.sSup_empty

open scoped Classical in
@[to_dual WithBot.WithTop.completeLattice]
/-
**WithTop.WithBot.completeLattice** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：WithTop.WithBot.completeLattice {α : Type*} [ConditionallyCompleteLattice 
α] : CompleteLattice (WithTop (WithBot α)) where isLUB_sSup S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance WithTop.WithBot.completeLattice {α : Type*}
    [ConditionallyCompleteLattice α] : CompleteLattice (WithTop (WithBot α)) where
  isLUB_sSup S := ⟨fun a haS ↦ (WithTop.isLUB_sSup' ⟨a, haS⟩).1 haS, fun a ha ↦ by
    rcases S.eq_empty_or_nonempty with h | h
    · change ite _ _ _ ≤ a
      simp [h]
    · exact (WithTop.isLUB_sSup' h).2 ha⟩
  isGLB_sInf S := ⟨fun a haS ↦
    show ite _ _ _ ≤ a by
      simp only [OrderBot.bddBelow, not_true_eq_false, or_false]
      split_ifs with h₁
      · cases a
        · exact le_rfl
        cases h₁ haS
      · cases a
        · exact le_top
        · apply WithTop.coe_le_coe.2
          refine csInf_le ?_ haS
          use ⊥
          intro b _
          exact bot_le,
    fun a haS ↦ (WithTop.isGLB_sInf' ⟨a, haS⟩).2 haS⟩
/-
**WithBot.WithTop.completeLinearOrder** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：WithBot.WithTop.completeLinearOrder {α : Type*} [ConditionallyCompleteLine
arOrder α] : CompleteLinearOrder (WithBot (WithTop α)) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance WithBot.WithTop.completeLinearOrder {α : Type*}
    [ConditionallyCompleteLinearOrder α] : CompleteLinearOrder (WithBot (WithTop α)) where
  __ := completeLattice
  __ := linearOrder
  __ := linearOrder.toBiheytingAlgebra

end WithTopBot

