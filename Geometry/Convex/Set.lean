/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.Prod

import Mathlib.Data.Fintype.Order

/-!
# Convex sets

This file defines convex sets in a convex space.

## Implementation notes

To support non-field coefficients, for `s` to be convex we require that all finitary convex
combinations of points of `s` lie in `s`, instead of merely binary ones as is customary.

Since its body is an implementation detail, the predicate `IsConvexSet` is unexposed.
-/

open Finsupp Set

public noncomputable section

namespace Convexity
variable {ι I R K X Y : Type*}

section Semiring
variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] [ConvexSpace R X] [ConvexSpace R Y]
  {f : X → Y} {w : StdSimplex R X} {s t : Set X} {x y : X}

variable (R s) in
/-- A set `s` in a convex space is convex if all convex combinations of points in `s` lie themselves
in `s`.

When the scalars form a field, this is equivalent to the definition in terms of binary combinations.
See `IsConvexSet.of_convexCombPair_mem`. -/
/-
**Convexity.IsConvexSet** 是 Mathlib 中的一个定义，位于命名空间 `Convexity`。
形式化陈述：IsConvexSet : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set `s` in a convex space is convex if all convex combinations of points in `s
` lie themselves
in `s`.

When the scalars form a field, this is equivalent to the definition in terms of 
binary combinations.
See `IsConvexSet.of_convexCombPair_mem`.
-/
def IsConvexSet : Prop := ∀ ⦃w : StdSimplex R X⦄, ↑w.weights.support ⊆ s → w.sConvexComb ∈ s
/-
**Convexity.IsConvexSet.of_sConvexComb_mem** 是 Mathlib 中的一个定理，位于命名空间 `Convexity.
IsConvexSet`。
形式化陈述：∀ {R : Type u_3} {X : Type u_5} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : IsStrictOrderedRing R]   [inst_3 : Convexity.ConvexSpace R X] {s :
 Set X},   (∀ (w : Convexity.StdSimplex R X), ↑w.weights.support ⊆ s → Convexity
.sConvexComb w ∈ s) → Convexity.IsConvexSet R s
参数：∀ (w : Convexity.StdSimplex R X), ↑w.weights.support ⊆ s → Convexity.sConvexC
omb w ∈ s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsConvexSet.of_sConvexComb_mem
    (hs : ∀ w : StdSimplex R X, ↑w.weights.support ⊆ s → w.sConvexComb ∈ s) : IsConvexSet R s :=
  hs
/-
**Convexity.IsConvexSet.sConvexComb_mem** 是 Mathlib 中的一个定理，位于命名空间 `Convexity.IsC
onvexSet`。
形式化陈述：∀ {R : Type u_3} {X : Type u_5} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : IsStrictOrderedRing R]   [inst_3 : Convexity.ConvexSpace R X] {w :
 Convexity.StdSimplex R X} {s : Set X},   Convexity.IsConvexSet R s → ↑w.weights
.support ⊆ s → Convexity.sConvexComb w ∈ s
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsConvexSet.sConvexComb_mem (hs : IsConvexSet R s) (hw : ↑w.weights.support ⊆ s) :
    w.sConvexComb ∈ s := hs hw
/-
**Convexity.IsConvexSet.iConvexComb_mem** 是 Mathlib 中的一个定理，位于命名空间 `Convexity.IsC
onvexSet`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_3} {X : Type u_5} [inst : Semiring R] [inst_1
 : PartialOrder R]   [inst_2 : IsStrictOrderedRing R] [inst_3 : Convexity.Convex
Space R X] {s : Set X},   Convexity.IsConvexSet R s →     ∀ {w : Convexity.StdSi
mplex R ι} {f : ι → X}, (∀ (i : ι), w.weights i ≠ 0 → f i ∈ s) → Convexity.iConv
exComb w f ∈ s
参数：∀ (i : ι), w.weights i ≠ 0 → f i ∈ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Convexity.StdSimplex.weights_map`：∀ {R : Type u} [inst : PartialOrder R]
 [inst_1 : Semiring R] [inst_2 : IsStrictOrderedRing R] {M : Type v} {N : Type w
}   (g : M → N) (f : C…
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `Finset.coe_subset._gcongr_2`：∀ {α : Type u_1} {s₁ s₂ : Finset α}, s₁ ⊆ s
₂ → ↑s₁ ⊆ ↑s₂
· 使用定理 `Finsupp.mapDomain_support`：mapDomain_support [DecidableEq β] {f : α -> β
} {s : α ->₀ M} : (s.mapDomain f).support subseteq s.support.image f
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma IsConvexSet.iConvexComb_mem (hs : IsConvexSet R s) {w : StdSimplex R ι} {f : ι → X}
    (hf : ∀ i, w.weights i ≠ 0 → f i ∈ s) : w.iConvexComb f ∈ s := by
  classical
  refine hs ?_
  grw [StdSimplex.weights_map, mapDomain_support]
  simpa [subset_def]
/-
**Convexity.IsConvexSet.convexCombPair_mem** 是 Mathlib 中的一个定理，位于命名空间 `Convexity.
IsConvexSet`。
形式化陈述：∀ {R : Type u_3} {X : Type u_5} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : IsStrictOrderedRing R]   [inst_3 : Convexity.ConvexSpace R X] {s :
 Set X} {x y : X},   Convexity.IsConvexSet R s →     x ∈ s →       y ∈ s → ∀ {a 
b : R} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1), Convexity.convexCombPair a b
 ha hb hab x y ∈ s
参数：ha : 0 ≤ a；hb : 0 ≤ b；hab : a + b = 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convexity.IsConvexSet.sConvexComb_mem`：∀ {R : Type u_3} {X : Type u_5} [
inst : Semiring R] [inst_1 : PartialOrder R] [inst_2 : IsStrictOrderedRing R]   
[inst_3 : Convexity.ConvexS…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Convexity.StdSimplex.weights_duple`：∀ {R : Type u} [inst : PartialOrder 
R] [inst_1 : Semiring R] {M : Type u_9} [inst_2 : IsStrictOrderedRing R] (x y : 
M)   {s t : R} (hs : 0 ≤…
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `Finset.coe_subset._gcongr_2`：∀ {α : Type u_1} {s₁ s₂ : Finset α}, s₁ ⊆ s
₂ → ↑s₁ ⊆ ↑s₂
· 使用引理 `Finsupp.support_add`：support_add [DecidableEq ι] : (g₁ + g₂).support sub
seteq g₁.support union g₂.support
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Finset.union_subset_union`：union_subset_union (hsu : s subseteq u) (htv 
: t subseteq v) : s union t subseteq u union v
· 使用定理 `Finsupp.support_single_subset`：support_single_subset : (single a b).supp
ort subseteq {a}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma IsConvexSet.convexCombPair_mem (hs : IsConvexSet R s) (hx : x ∈ s) (hy : y ∈ s)
    {a b : R} (ha hb hab) : convexCombPair a b ha hb hab x y ∈ s := by
  classical
  refine hs.sConvexComb_mem ?_
  grw [StdSimplex.weights_duple, support_add, support_single_subset, support_single_subset]
  simp [*, insert_subset_iff]
/-
**Convexity.IsConvexSet.empty** 是 Mathlib 中的一个定理，位于命名空间 `Convexity.IsConvexSet`。
形式化陈述：∀ {R : Type u_3} {X : Type u_5} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : IsStrictOrderedRing R]   [inst_3 : Convexity.ConvexSpace R X], Con
vexity.IsConvexSet R ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] protected lemma IsConvexSet.empty : IsConvexSet R (∅ : Set X) := by simp [IsConvexSet]
/-
**Convexity.IsConvexSet.univ** 是 Mathlib 中的一个定理，位于命名空间 `Convexity.IsConvexSet`。
形式化陈述：∀ {R : Type u_3} {X : Type u_5} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : IsStrictOrderedRing R]   [inst_3 : Convexity.ConvexSpace R X], Con
vexity.IsConvexSet R Set.univ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] protected lemma IsConvexSet.univ : IsConvexSet R (.univ : Set X) := by simp [IsConvexSet]
/-
**Convexity.IsConvexSet.singleton** 是 Mathlib 中的一个定理，位于命名空间 `Convexity.IsConvexS
et`。
形式化陈述：∀ {R : Type u_3} {X : Type u_5} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : IsStrictOrderedRing R]   [inst_3 : Convexity.ConvexSpace R X] {x :
 X}, Convexity.IsConvexSet R {x}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Convexity.ConvexSpace.sConvexComb_single`：∀ {R : Type u} {M : Type v} {i
nst₁ : PartialOrder R} {inst₂ : Semiring R} {inst₃ : IsStrictOrderedRing R}   [s
elf : Convexity.ConvexSpace R …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] protected lemma IsConvexSet.singleton : IsConvexSet R {x} := by
  simp [IsConvexSet, -subset_singleton_iff, Finset.coe_subset_singleton]
/-
**Convexity.IsConvexSet.of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Convexity.IsC
onvexSet`。
形式化陈述：∀ {R : Type u_3} {X : Type u_5} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : IsStrictOrderedRing R]   [inst_3 : Convexity.ConvexSpace R X] {s :
 Set X}, s.Subsingleton → Convexity.IsConvexSet R s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subsingleton.eq_empty_or_singleton`：∀ {α : Type u} {s : Set α}, s.Su
bsingleton → s = ∅ ∨ ∃ x, s = {x}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma IsConvexSet.of_subsingleton (hs : s.Subsingleton) : IsConvexSet R s := by
  obtain rfl | ⟨x, rfl⟩ := hs.eq_empty_or_singleton <;> simp
/-
**Convexity.IsConvexSet.inter** 是 Mathlib 中的一个定理，位于命名空间 `Convexity.IsConvexSet`。
形式化陈述：∀ {R : Type u_3} {X : Type u_5} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : IsStrictOrderedRing R]   [inst_3 : Convexity.ConvexSpace R X] {s t
 : Set X},   Convexity.IsConvexSet R s → Convexity.IsConvexSet R t → Convexity.I
sConvexSet R (s ∩ t)
参数：s ∩ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Convexity.IsConvexSet.sConvexComb_mem`：∀ {R : Type u_3} {X : Type u_5} [
inst : Semiring R] [inst_1 : PartialOrder R] [inst_2 : IsStrictOrderedRing R]   
[inst_3 : Convexity.ConvexS…
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
protected lemma IsConvexSet.inter (hs : IsConvexSet R s) (ht : IsConvexSet R t) :
    IsConvexSet R (s ∩ t) := by
  simp +contextual [IsConvexSet, hs.sConvexComb_mem, ht.sConvexComb_mem]
/-
**Convexity.IsConvexSet.sInter** 是 Mathlib 中的一个定理，位于命名空间 `Convexity.IsConvexSet`
。
形式化陈述：∀ {R : Type u_3} {X : Type u_5} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : IsStrictOrderedRing R]   [inst_3 : Convexity.ConvexSpace R X] {S :
 Set (Set X)},   (∀ s ∈ S, Convexity.IsConvexSet R s) → Convexity.IsConvexSet R 
(⋂₀ S)
参数：Set X；∀ s ∈ S, Convexity.IsConvexSet R s；⋂₀ S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Convexity.IsConvexSet.sConvexComb_mem`：∀ {R : Type u_3} {X : Type u_5} [
inst : Semiring R] [inst_1 : PartialOrder R] [inst_2 : IsStrictOrderedRing R]   
[inst_3 : Convexity.ConvexS…
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
protected lemma IsConvexSet.sInter {S : Set (Set X)} (hS : ∀ s ∈ S, IsConvexSet R s) :
    IsConvexSet R (⋂₀ S) := by simp +contextual [IsConvexSet, (hS _ _).sConvexComb_mem]
/-
**Convexity.IsConvexSet.iInter** 是 Mathlib 中的一个定理，位于命名空间 `Convexity.IsConvexSet`
。
形式化陈述：∀ {R : Type u_3} {X : Type u_5} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : IsStrictOrderedRing R]   [inst_3 : Convexity.ConvexSpace R X] {ι :
 Sort u_7} {s : ι → Set X},   (∀ (i : ι), Convexity.IsConvexSet R (s i)) → Conve
xity.IsConvexSet R (⋂ i, s i)
参数：∀ (i : ι), Convexity.IsConvexSet R (s i)；⋂ i, s i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Convexity.IsConvexSet.sConvexComb_mem`：∀ {R : Type u_3} {X : Type u_5} [
inst : Semiring R] [inst_1 : PartialOrder R] [inst_2 : IsStrictOrderedRing R]   
[inst_3 : Convexity.ConvexS…
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
protected lemma IsConvexSet.iInter {ι : Sort*} {s : ι → Set X} (hs : ∀ i, IsConvexSet R (s i)) :
    IsConvexSet R (⋂ i, s i) := by simp +contextual [IsConvexSet, (hs _).sConvexComb_mem]
/-
**Convexity.IsConvexSet.iInter** 是 Mathlib 中的一个定理，位于命名空间 `Convexity.IsConvexSet`
。
形式化陈述：∀ {R : Type u_3} {X : Type u_5} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : IsStrictOrderedRing R]   [inst_3 : Convexity.ConvexSpace R X] {ι :
 Sort u_7} {s : ι → Set X},   (∀ (i : ι), Convexity.IsConvexSet R (s i)) → Conve
xity.IsConvexSet R (⋂ i, s i)
参数：∀ (i : ι), Convexity.IsConvexSet R (s i)；⋂ i, s i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Convexity.IsConvexSet.sConvexComb_mem`：∀ {R : Type u_3} {X : Type u_5} [
inst : Semiring R] [inst_1 : PartialOrder R] [inst_2 : IsStrictOrderedRing R]   
[inst_3 : Convexity.ConvexS…
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma IsConvexSet.iInter₂ {ι : Sort*} {κ : ι → Sort*} {s : ∀ i, κ i → Set X}
    (h : ∀ i j, IsConvexSet R (s i j)) : IsConvexSet R (⋂ (i) (j), s i j) :=
  .iInter fun i ↦ .iInter <| h i
/-
**Convexity.IsConvexSet.sUnion** 是 Mathlib 中的一个定理，位于命名空间 `Convexity.IsConvexSet`
。
形式化陈述：∀ {R : Type u_3} {X : Type u_5} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : IsStrictOrderedRing R]   [inst_3 : Convexity.ConvexSpace R X] {S :
 Set (Set X)},   DirectedOn (fun x1 x2 => x1 ⊆ x2) S → (∀ s ∈ S, Convexity.IsCon
vexSet R s) → Convexity.IsConvexSet R (⋃₀ S)
参数：Set X；fun x1 x2 => x1 ⊆ x2；∀ s ∈ S, Convexity.IsConvexSet R s；⋃₀ S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sUnion_empty`：sUnion_empty : ⋃₀ ∅ = (∅ : Set α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DirectedOn.exists_mem_subset_of_finite_of_subset_sUnion`：DirectedOn.exis
ts_mem_subset_of_finite_of_subset_sUnion {α : Type*} {c : Set (Set α)} (hn : c.N
onempty) (hc : DirectedOn (· subseteq ·) c) {…
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `Set.mem_sUnion_of_mem`：mem_sUnion_of_mem {x : α} {t : Set α} {S : Set (S
et α)} (hx : x in t) (ht : t in S) : x in ⋃₀ S
-/
protected lemma IsConvexSet.sUnion {S : Set (Set X)} (hS : DirectedOn (· ⊆ ·) S)
    (hS' : ∀ s ∈ S, IsConvexSet R s) : IsConvexSet R (⋃₀ S) := by
  obtain rfl | hS'' := S.eq_empty_or_nonempty
  · simp
  rintro w hw
  obtain ⟨s, hsS, hws⟩ :=
    hS.exists_mem_subset_of_finite_of_subset_sUnion hS'' w.weights.support.finite_toSet hw
  exact mem_sUnion_of_mem (hS' s hsS hws) hsS
/-
**Convexity.IsConvexSet.iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Convexity.IsConvexSet`
。
形式化陈述：∀ {R : Type u_3} {X : Type u_5} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : IsStrictOrderedRing R]   [inst_3 : Convexity.ConvexSpace R X] {ι :
 Sort u_7} {s : ι → Set X},   Directed (fun x1 x2 => x1 ⊆ x2) s → (∀ (i : ι), Co
nvexity.IsConvexSet R (s i)) → Convexity.IsConvexSet R (⋃ i, s i)
参数：fun x1 x2 => x1 ⊆ x2；∀ (i : ι), Convexity.IsConvexSet R (s i)；⋃ i, s i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convexity.IsConvexSet.sUnion`：∀ {R : Type u_3} {X : Type u_5} [inst : Se
miring R] [inst_1 : PartialOrder R] [inst_2 : IsStrictOrderedRing R]   [inst_3 :
 Convexity.ConvexS…
· 使用定理 `Directed.directedOn_range`：∀ {α : Type u_1} {ι : Sort u_3} {r : α → α → 
Prop} {f : ι → α}, Directed r f → DirectedOn r (Set.range f)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
protected lemma IsConvexSet.iUnion {ι : Sort*} {s : ι → Set X} (hs : Directed (· ⊆ ·) s)
    (hs' : ∀ i, IsConvexSet R (s i)) : IsConvexSet R (⋃ i, s i) :=
  .sUnion hs.directedOn_range <| by simpa
/-
**Convexity.IsConvexSet.preimage** 是 Mathlib 中的一个定理，位于命名空间 `Convexity.IsConvexSe
t`。
形式化陈述：∀ {R : Type u_3} {X : Type u_5} {Y : Type u_6} [inst : Semiring R] [inst_1
 : PartialOrder R]   [inst_2 : IsStrictOrderedRing R] [inst_3 : Convexity.Convex
Space R X] [inst_4 : Convexity.ConvexSpace R Y] {f : X → Y}   {s : Set Y}, Conve
xity.IsAffineMap R f → Convexity.IsConvexSet R s → Convexity.IsConvexSet R (f ⁻¹
' s)
参数：f ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Convexity.IsAffineMap.map_sConvexComb`：∀ {R : Type u_1} {M : Type u_3} {
N : Type u_4} [inst : PartialOrder R] [inst_1 : Semiring R]   [inst_2 : IsStrict
OrderedRing R] [inst_3 : Co…
· 使用定理 `Convexity.IsConvexSet.iConvexComb_mem`：∀ {ι : Type u_1} {R : Type u_3} {
X : Type u_5} [inst : Semiring R] [inst_1 : PartialOrder R]   [inst_2 : IsStrict
OrderedRing R] [inst_3 : Co…
-/
protected lemma IsConvexSet.preimage {s : Set Y} (hf : IsAffineMap R f) (hs : IsConvexSet R s) :
    IsConvexSet R (f ⁻¹' s) := by
  rintro w hw
  simp only [mem_preimage, hf.map_sConvexComb, sConvexComb_map]
  exact hs.iConvexComb_mem fun x hx ↦ hw <| by simpa
/-
**Convexity.IsConvexSet.image** 是 Mathlib 中的一个定理，位于命名空间 `Convexity.IsConvexSet`。
形式化陈述：∀ {R : Type u_3} {X : Type u_5} {Y : Type u_6} [inst : Semiring R] [inst_1
 : PartialOrder R]   [inst_2 : IsStrictOrderedRing R] [inst_3 : Convexity.Convex
Space R X] [inst_4 : Convexity.ConvexSpace R Y] {f : X → Y}   {s : Set X}, Conve
xity.IsAffineMap R f → Convexity.IsConvexSet R s → Convexity.IsConvexSet R (f ''
 s)
参数：f '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.exists_subset_injOn_image_eq_of_surjOn`：exists_subset_injOn_image
_eq_of_surjOn [DecidableEq β] {f : α -> β} (s : Set α) (t : Finset β) (hfs : s.S
urjOn f t) : exists u : Finset α, ↑…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.sum_onFinset`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [i
nst : Zero M] [inst_1 : AddCommMonoid N] (s : Finset α) (f : α → M)   (hf : ∀ (a
 : α), f a…
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_ite_mem`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s t : Finset ι) (f : ι → M),   (∑ i ∈ s, if i ∈ t
 then f …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.inter_self`：inter_self (s : Finset α) : s inter s = s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_image`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_4} [inst :
 AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι]   {s : Finset κ} {g : κ →
 ι}, S…
· 使用定理 `Convexity.StdSimplex.total`：∀ {R : Type u} [inst : LE R] [inst_1 : AddCo
mmMonoid R] [inst_2 : One R] {M : Type v} (self : Convexity.StdSimplex R M),   (
self.weights.sum…
· 使用定理 `Convexity.IsConvexSet.sConvexComb_mem`：∀ {R : Type u_3} {X : Type u_5} [
inst : Semiring R] [inst_1 : PartialOrder R] [inst_2 : IsStrictOrderedRing R]   
[inst_3 : Convexity.ConvexS…
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `Finset.coe_subset._gcongr_2`：∀ {α : Type u_1} {s₁ s₂ : Finset α}, s₁ ⊆ s
₂ → ↑s₁ ⊆ ↑s₂
· 使用定理 `Finsupp.support_onFinset_subset`：support_onFinset_subset {s : Finset α} 
{f : α -> M} {hf} : (onFinset s f hf).support subseteq s
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Convexity.IsAffineMap.map_sConvexComb`：∀ {R : Type u_1} {M : Type u_3} {
N : Type u_4} [inst : PartialOrder R] [inst_1 : Semiring R]   [inst_2 : IsStrict
OrderedRing R] [inst_3 : Co…
· 使用定理 `Convexity.StdSimplex.ext`：∀ {R : Type u} [inst : PartialOrder R] [inst_1
 : Semiring R] {M : Type u_9} {f g : Convexity.StdSimplex R M},   f.weights = g.
weights → f = …
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `Convexity.StdSimplex.weights_map`：∀ {R : Type u} [inst : PartialOrder R]
 [inst_1 : Semiring R] [inst_2 : IsStrictOrderedRing R] {M : Type v} {N : Type w
}   (g : M → N) (f : C…
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
（共 34 条，此处仅展示前 30 条）
-/
protected lemma IsConvexSet.image (hf : IsAffineMap R f) (hs : IsConvexSet R s) :
    IsConvexSet R (f '' s) := by
  classical
  rintro w hw
  obtain ⟨u, hus, hfu, huw⟩ := Finset.exists_subset_injOn_image_eq_of_surjOn _ _ hw
  refine ⟨sConvexComb {
      weights := .onFinset u (fun x ↦ if x ∈ u then w.weights (f x) else 0) <| by simp +contextual
      nonneg x := by simp; split <;> simp
      total := by
        simp only [implies_true, sum_onFinset, Finset.sum_ite_mem, Finset.inter_self,
        ← Finset.sum_image hfu, huw]
        exact w.total
    }, hs.sConvexComb_mem <| by grw [support_onFinset_subset, hus], ?_⟩
  rw [hf.map_sConvexComb]
  congr
  ext y
  rw [StdSimplex.weights_map]
  by_cases hy : y ∈ w.weights.support
  · rw [← huw, Finset.mem_image] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    convert mapDomain_apply' _ _ support_onFinset_subset hfu hx
    exact (if_pos hx).symm
  · rw [mapDomain_of_not_mem_image_support (by simp [← huw] at ⊢ hy; tauto)]
    simp_all

/-- A convex subset of a convex space is a convex space. -/
@[expose, implicit_reducible]
/-
**Convexity.ConvexSpace.subtype** 是 Mathlib 中的一个定义，位于命名空间 `Convexity.ConvexSpace
`。
形式化陈述：{R : Type u_3} →   {X : Type u_5} →     [inst : Semiring R] →       [inst_
1 : PartialOrder R] →         [inst_2 : IsStrictOrderedRing R] →           [inst
_3 : Convexity.ConvexSpace R X] → (s : Set X) → Convexity.IsConvexSet R s → Conv
exity.ConvexSpace R ↑s
参数：s : Set X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A convex subset of a convex space is a convex space.
-/
def ConvexSpace.subtype (s : Set X) (hs : IsConvexSet R s) : ConvexSpace R s := .mk
  (fun w ↦ ⟨w.iConvexComb (↑), hs.iConvexComb_mem <| by simp⟩)
  (fun x ↦ by simp)
  (fun w ↦ by ext; simp [iConvexComb_assoc])
/-
**Convexity.isAffineMap_subtypeVal** 是 Mathlib 中的一个引理，位于命名空间 `Convexity`。
形式化陈述：isAffineMap_subtypeVal (s : Set X) (hs : IsConvexSet R s) : letI : ConvexS
pace R s
参数：s : Set X；hs : IsConvexSet R s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isAffineMap_subtypeVal (s : Set X) (hs : IsConvexSet R s) :
    letI : ConvexSpace R s := .subtype s hs
    IsAffineMap R ((↑) : s → X) :=
  letI : ConvexSpace R s := .subtype s hs
  ⟨fun _ ↦ rfl⟩

@[simp]
/-
**Convexity.subtypeVal_sConvexComb** 是 Mathlib 中的一个引理，位于命名空间 `Convexity`。
形式化陈述：subtypeVal_sConvexComb (s : Set X) (hs : IsConvexSet R s) (w : StdSimplex 
R s) : letI : ConvexSpace R s
参数：s : Set X；hs : IsConvexSet R s；w : StdSimplex R s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma subtypeVal_sConvexComb (s : Set X) (hs : IsConvexSet R s) (w : StdSimplex R s) :
    letI : ConvexSpace R s := .subtype s hs
    (w.sConvexComb : X) = w.iConvexComb (↑) := rfl

@[simp]
/-
**Convexity.subtypeVal_iConvexComb** 是 Mathlib 中的一个引理，位于命名空间 `Convexity`。
形式化陈述：subtypeVal_iConvexComb (s : Set X) (hs : IsConvexSet R s) (w : StdSimplex 
R I) (f : I -> s) : letI : ConvexSpace R s
参数：s : Set X；hs : IsConvexSet R s；w : StdSimplex R I；f : I -> s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convexity.IsAffineMap.map_iConvexComb`：∀ {R : Type u_1} {M : Type u_3} {
N : Type u_4} {I : Type u_6} [inst : PartialOrder R] [inst_1 : Semiring R]   [in
st_2 : IsStrictOrderedRing …
· 使用引理 `Convexity.isAffineMap_subtypeVal`：isAffineMap_subtypeVal (s : Set X) (hs
 : IsConvexSet R s) : letI : ConvexSpace R s
-/
lemma subtypeVal_iConvexComb (s : Set X) (hs : IsConvexSet R s) (w : StdSimplex R I) (f : I → s) :
    letI : ConvexSpace R s := .subtype s hs
    (↑(w.iConvexComb f) : X) = w.iConvexComb (fun i ↦ (f i).val) :=
  letI : ConvexSpace R s := .subtype s hs
  (isAffineMap_subtypeVal ..).map_iConvexComb ..

@[simp]
/-
**Convexity.subtypeVal_convexCombPair** 是 Mathlib 中的一个引理，位于命名空间 `Convexity`。
形式化陈述：subtypeVal_convexCombPair (s : Set X) (hs : IsConvexSet R s) (a b : R) (ha
 hb hab) (x y : s) : letI : ConvexSpace R s
参数：s : Set X；hs : IsConvexSet R s；a b : R；ha hb hab；x y : s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convexity.IsAffineMap.map_convexCombPair`：∀ {R : Type u_1} {M : Type u_3
} {N : Type u_4} [inst : PartialOrder R] [inst_1 : Semiring R]   [inst_2 : IsStr
ictOrderedRing R] [inst_3 : Co…
· 使用引理 `Convexity.isAffineMap_subtypeVal`：isAffineMap_subtypeVal (s : Set X) (hs
 : IsConvexSet R s) : letI : ConvexSpace R s
-/
lemma subtypeVal_convexCombPair (s : Set X) (hs : IsConvexSet R s) (a b : R) (ha hb hab) (x y : s) :
    letI : ConvexSpace R s := .subtype s hs
    (↑(convexCombPair a b ha hb hab x y) : X) = convexCombPair a b ha hb hab x.val y.val :=
  letI : ConvexSpace R s := .subtype s hs
  (isAffineMap_subtypeVal ..).map_convexCombPair ..
/-
**Convexity.IsConvexSet.prod** 是 Mathlib 中的一个定理，位于命名空间 `Convexity.IsConvexSet`。
形式化陈述：∀ {R : Type u_3} {X : Type u_5} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : IsStrictOrderedRing R]   [inst_3 : Convexity.ConvexSpace R X] {s :
 Set X} {Y : Type u_7} [inst_4 : Convexity.ConvexSpace R Y] {t : Set Y},   Conve
xity.IsConvexSet R s → Convexity.IsConvexSet R t → Convexity.IsConvexSet R (s ×ˢ
 t)
参数：s ×ˢ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Convexity.StdSimplex.weights_map`：∀ {R : Type u} [inst : PartialOrder R]
 [inst_1 : Semiring R] [inst_2 : IsStrictOrderedRing R] {M : Type v} {N : Type w
}   (g : M → N) (f : C…
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `Finset.coe_subset._gcongr_2`：∀ {α : Type u_1} {s₁ s₂ : Finset α}, s₁ ⊆ s
₂ → ↑s₁ ⊆ ↑s₂
· 使用定理 `Finsupp.mapDomain_support`：mapDomain_support [DecidableEq β] {f : α -> β
} {s : α ->₀ M} : (s.mapDomain f).support subseteq s.support.image f
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Set.fst_image_prod_subset`：fst_image_prod_subset (s : Set α) (t : Set β)
 : Prod.fst '' s ×ˢ t subseteq s
· 使用定理 `Set.snd_image_prod_subset`：snd_image_prod_subset (s : Set α) (t : Set β)
 : Prod.snd '' s ×ˢ t subseteq t
-/
protected lemma IsConvexSet.prod {Y : Type*} [ConvexSpace R Y] {t : Set Y}
    (hs : IsConvexSet R s) (ht : IsConvexSet R t) : IsConvexSet R (s ×ˢ t) := by
  classical
  rintro w hw
  refine ⟨hs ?_, ht ?_⟩
  · grw [StdSimplex.weights_map, mapDomain_support, Finset.coe_image, hw, fst_image_prod_subset]
  · grw [StdSimplex.weights_map, mapDomain_support, Finset.coe_image, hw, snd_image_prod_subset]
/-
**Convexity.IsConvexSet.pi** 是 Mathlib 中的一个定理，位于命名空间 `Convexity.IsConvexSet`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_3} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : IsStrictOrderedRing R]   {X : ι → Type u_7} [inst_3 : (i : ι) → Co
nvexity.ConvexSpace R (X i)] {s : Set ι} {t : (i : ι) → Set (X i)},   (∀ i ∈ s, 
Convexity.IsConvexSet R (t i)) → Convexity.IsConvexSet R (s.pi t)
参数：i : ι；X i；i : ι；X i；∀ i ∈ s, Convexity.IsConvexSet R (t i)；s.pi t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Convexity.StdSimplex.weights_map`：∀ {R : Type u} [inst : PartialOrder R]
 [inst_1 : Semiring R] [inst_2 : IsStrictOrderedRing R] {M : Type v} {N : Type w
}   (g : M → N) (f : C…
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `Finset.coe_subset._gcongr_2`：∀ {α : Type u_1} {s₁ s₂ : Finset α}, s₁ ⊆ s
₂ → ↑s₁ ⊆ ↑s₂
· 使用定理 `Finsupp.mapDomain_support`：mapDomain_support [DecidableEq β] {f : α -> β
} {s : α ->₀ M} : (s.mapDomain f).support subseteq s.support.image f
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Set.eval_image_pi_subset`：eval_image_pi_subset (hs : i in s) : eval i ''
 s.pi t subseteq t i
-/
protected lemma IsConvexSet.pi {X : ι → Type*} [∀ i, ConvexSpace R (X i)] {s : Set ι}
    {t : ∀ i, Set (X i)} (ht : ∀ i ∈ s, IsConvexSet R (t i)) : IsConvexSet R (s.pi t) := by
  classical
  refine fun w hw i hi ↦ ht i hi ?_
  grw [StdSimplex.weights_map, mapDomain_support, Finset.coe_image, hw, eval_image_pi_subset hi]

end Semiring

section Field
variable [Field K] [LinearOrder K] [IsStrictOrderedRing K] [ConvexSpace K X] {w : StdSimplex K X}
  {s t : Set X} {x y : X}

set_option backward.isDefEq.respectTransparency.types false in
/-- Convexity of a set can be checked via binary combinations if the scalars form a field. -/
/-
**Convexity.IsConvexSet.of_convexCombPair_mem** 是 Mathlib 中的一个定理，位于命名空间 `Convexi
ty.IsConvexSet`。
形式化陈述：∀ {K : Type u_4} {X : Type u_5} [inst : Field K] [inst_1 : LinearOrder K] 
[inst_2 : IsStrictOrderedRing K]   [inst_3 : Convexity.ConvexSpace K X] {s : Set
 X},   (∀ (a b : K) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1),       ∀ x ∈ s, 
∀ y ∈ s, Convexity.convexCombPair a b ha hb hab x y ∈ s) →     Convexity.IsConve
xSet K s
参数：∀ (a b : K) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1),       ∀ x ∈ s, ∀ y ∈
 s, Convexity.convexCombPair a b ha hb hab x y ∈ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Convexity.StdSimplex.support_weights_nonempty`：support_weights_nonempty 
[Nontrivial R] (w : StdSimplex R M) : w.weights.support.Nonempty
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Finset.Nonempty.cons_induction`：∀ {α : Type u_3} {motive : (s : Finset α
) → s.Nonempty → Prop},   (∀ (a : α), motive {a} ⋯) →     (∀ (a : α) (s : Finset
 α) (h : a ∉ s) (hs …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Convexity.ConvexSpace.sConvexComb_single`：∀ {R : Type u} {M : Type v} {i
nst₁ : PartialOrder R} {inst₂ : Semiring R} {inst₃ : IsStrictOrderedRing R}   [s
elf : Convexity.ConvexSpace R …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Convexity.StdSimplex.weights_single`：∀ {R : Type u} [inst : PartialOrder
 R] [inst_1 : Semiring R] {M : Type u_9} [inst_2 : IsStrictOrderedRing R] (x : M
),   (Convexity.StdSimple…
· 使用定理 `Finsupp.support_single`：∀ {α : Type u_1} {M : Type u_5} [inst : Zero M] 
{b : M} (a : α), b ≠ 0 → (fun₀ | a => b).support = {a}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.cons_eq_insert`：cons_eq_insert (a s h) : @cons α a s h = insert a
 s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Convexity.StdSimplex.convexCombPair_restrict_restrict_compl`：convexCombP
air_restrict_restrict_compl (w : StdSimplex K I) (s : Set I) (hs hs') [Decidable
Pred (· in s)] : convexCombPair ((w.weights.filte…
· 使用定理 `Finsupp.filter.congr_simp`：∀ {α : Type u_1} {M : Type u_5} [inst : Zero 
M] (p p_1 : α → Prop),   p = p_1 →     ∀ {inst_1 : DecidablePred p} [inst_2 : De
cidablePred p_1…
· 使用定理 `Convexity.convexCombPair.congr_simp`：∀ {R : Type u_1} {M : Type u_3} [in
st : PartialOrder R] [inst_1 : Semiring R] [inst_2 : IsStrictOrderedRing R]   [i
nst_3 : Convexity.ConvexS…
· 使用定理 `Convexity.StdSimplex.restrict_singleton`：∀ {X : Type u_2} {K : Type u_8}
 [inst : Semifield K] [inst_1 : LinearOrder K] [inst_2 : IsStrictOrderedRing K] 
  [IsDomain K] (w : Convexity…
· 使用定理 `Field.isDomain`：∀ {K : Type u_1} [inst : Field K], IsDomain K
· 使用引理 `Convexity.sConvexComb_convexCombPair`：sConvexComb_convexCombPair (s t : 
R) (hs ht hst) (w w' : StdSimplex R M) : (convexCombPair s t hs ht hst w w').sCo
nvexComb = convexCombPair …
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
Convexity of a set can be checked via binary combinations if the scalars form a 
field.
-/
lemma IsConvexSet.of_convexCombPair_mem
    (hs : ∀ a b : K, ∀ ha hb hab, ∀ x ∈ s, ∀ y ∈ s, convexCombPair a b ha hb hab x y ∈ s) :
    IsConvexSet K s := by
  classical
  rintro w hw
  set t := w.weights.support with hsw
  have ht : t.Nonempty := w.support_weights_nonempty
  clear_value t
  induction ht using Finset.Nonempty.cons_induction generalizing w with
  | singleton x => simp_all [eq_comm]
  | cons x t hx ht ih =>
  have hwx : w.weights x ≠ 0 := by simpa using congr(x ∈ $hsw)
  have hwx' : ∃ y ≠ x, w.weights y ≠ 0 := by
    obtain ⟨y, hy⟩ := ht
    exact ⟨y, ne_of_mem_of_not_mem hy hx, by simpa [hy] using congr(y ∈ $hsw)⟩
  rw [← w.convexCombPair_restrict_restrict_compl {x} (by simpa) hwx']
  simp only [mem_singleton_iff, StdSimplex.restrict_singleton, sConvexComb_convexCombPair,
    sConvexComb_single]
  exact hs _ _ _ _ _ _ (hw <| by simp) _ <| ih (by grw [← hw, ← Finset.subset_cons])
    (by simp [← hsw]; grind)

end Field
end Convexity

