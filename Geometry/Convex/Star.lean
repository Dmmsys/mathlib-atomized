/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Geometry.Convex.Set

/-!
# Star-convex sets

This file defines star-convex sets in a convex space.

A set is star-convex at `x` if every segment from `x` to a point in the set is contained in the set.

This is the prototypical example of a contractible set in homotopy theory (by scaling every point
towards `x`), but has wider uses.

Note that this has nothing to do with star rings, `Star` and co.

## Implementation notes

Instead of saying that a set is star-convex, we say a set is star-convex *at a point*. This has the
advantage of allowing us to talk about convexity as being "everywhere star-convexity" and of making
the union of star-convex sets be star-convex.

Incidentally, this choice means we don't need to assume a set is nonempty for it to be star-convex.
Concretely, the empty set is star-convex at every point.
-/

open Finsupp Set

public section

namespace Convexity
variable {R X Y : Type*} {ι : Sort*} {κ : ι → Sort*}

section Semiring
variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] [ConvexSpace R X] [ConvexSpace R Y]
  {f : X → Y} {w : StdSimplex R X} {x : X} {s t : Set X} {y : X}

variable (R x s) in
/-- A set `s` is star-convex at a point `x` if every segment from `x` to a point in `s` is
contained in `s`.

TODO: Replace `StarConvex` with this predicate. -/
@[expose]
/-
**Convexity.IsStarConvexSet** 是 Mathlib 中的一个定义，位于命名空间 `Convexity`。
形式化陈述：IsStarConvexSet : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set `s` is star-convex at a point `x` if every segment from `x` to a point in 
`s` is
contained in `s`.

TODO: Replace `StarConvex` with this predicate.
-/
def IsStarConvexSet : Prop :=
  ∀ ⦃y⦄, y ∈ s → ∀ ⦃a b : R⦄ ha hb hab, convexCombPair a b ha hb hab x y ∈ s
/-
**Convexity.IsStarConvexSet.empty** 是 Mathlib 中的一个定理，位于命名空间 `Convexity.IsStarCon
vexSet`。
形式化陈述：∀ {R : Type u_1} {X : Type u_2} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : IsStrictOrderedRing R]   [inst_3 : Convexity.ConvexSpace R X] {x :
 X}, Convexity.IsStarConvexSet R x ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] protected lemma IsStarConvexSet.empty : IsStarConvexSet R x ∅ := by simp [IsStarConvexSet]

@[simp]
/-
**Convexity.IsStarConvexSet.univ** 是 Mathlib 中的一个定理，位于命名空间 `Convexity.IsStarConv
exSet`。
形式化陈述：∀ {R : Type u_1} {X : Type u_2} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : IsStrictOrderedRing R]   [inst_3 : Convexity.ConvexSpace R X] {x :
 X}, Convexity.IsStarConvexSet R x Set.univ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
protected lemma IsStarConvexSet.univ : IsStarConvexSet R x .univ := by simp [IsStarConvexSet]
/-
**Convexity.IsStarConvexSet.singleton** 是 Mathlib 中的一个定理，位于命名空间 `Convexity.IsSta
rConvexSet`。
形式化陈述：∀ {R : Type u_1} {X : Type u_2} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : IsStrictOrderedRing R]   [inst_3 : Convexity.ConvexSpace R X] {x :
 X}, Convexity.IsStarConvexSet R x {x}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Convexity.convexCombPair_same`：convexCombPair_same {x : M} : convexCombP
air s t hs ht h x x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] protected lemma IsStarConvexSet.singleton : IsStarConvexSet R x {x} := by
  simp [IsStarConvexSet]

@[grind ←]
/-
**Convexity.IsStarConvexSet.inter** 是 Mathlib 中的一个定理，位于命名空间 `Convexity.IsStarCon
vexSet`。
形式化陈述：∀ {R : Type u_1} {X : Type u_2} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : IsStrictOrderedRing R]   [inst_3 : Convexity.ConvexSpace R X] {x :
 X} {s t : Set X},   Convexity.IsStarConvexSet R x s → Convexity.IsStarConvexSet
 R x t → Convexity.IsStarConvexSet R x (s ∩ t)
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
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
protected lemma IsStarConvexSet.inter (hs : IsStarConvexSet R x s) (ht : IsStarConvexSet R x t) :
    IsStarConvexSet R x (s ∩ t) := by simp +contextual [IsStarConvexSet, hs _, ht _]

@[grind ←]
/-
**Convexity.IsStarConvexSet.union** 是 Mathlib 中的一个定理，位于命名空间 `Convexity.IsStarCon
vexSet`。
形式化陈述：∀ {R : Type u_1} {X : Type u_2} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : IsStrictOrderedRing R]   [inst_3 : Convexity.ConvexSpace R X] {x :
 X} {s t : Set X},   Convexity.IsStarConvexSet R x s → Convexity.IsStarConvexSet
 R x t → Convexity.IsStarConvexSet R x (s ∪ t)
参数：s ∪ t。
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
protected lemma IsStarConvexSet.union (hs : IsStarConvexSet R x s) (ht : IsStarConvexSet R x t) :
    IsStarConvexSet R x (s ∪ t) := by simp +contextual [IsStarConvexSet, hs _, ht _, or_imp]

@[grind ←]
/-
**Convexity.IsStarConvexSet.sInter** 是 Mathlib 中的一个定理，位于命名空间 `Convexity.IsStarCo
nvexSet`。
形式化陈述：∀ {R : Type u_1} {X : Type u_2} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : IsStrictOrderedRing R]   [inst_3 : Convexity.ConvexSpace R X] {x :
 X} {S : Set (Set X)},   (∀ s ∈ S, Convexity.IsStarConvexSet R x s) → Convexity.
IsStarConvexSet R x (⋂₀ S)
参数：Set X；∀ s ∈ S, Convexity.IsStarConvexSet R x s；⋂₀ S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
protected lemma IsStarConvexSet.sInter {S : Set (Set X)} (hS : ∀ s ∈ S, IsStarConvexSet R x s) :
    IsStarConvexSet R x (⋂₀ S) := by simp +contextual [IsStarConvexSet, hS _ _ _]

@[grind ←]
/-
**Convexity.IsStarConvexSet.iInter** 是 Mathlib 中的一个定理，位于命名空间 `Convexity.IsStarCo
nvexSet`。
形式化陈述：∀ {R : Type u_1} {X : Type u_2} {ι : Sort u_4} [inst : Semiring R] [inst_1
 : PartialOrder R]   [inst_2 : IsStrictOrderedRing R] [inst_3 : Convexity.Convex
Space R X] {x : X} {s : ι → Set X},   (∀ (i : ι), Convexity.IsStarConvexSet R x 
(s i)) → Convexity.IsStarConvexSet R x (⋂ i, s i)
参数：∀ (i : ι), Convexity.IsStarConvexSet R x (s i)；⋂ i, s i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
protected lemma IsStarConvexSet.iInter {s : ι → Set X} (hs : ∀ i, IsStarConvexSet R x (s i)) :
    IsStarConvexSet R x (⋂ i, s i) := by simp +contextual [IsStarConvexSet, hs _ _]
/-
**Convexity.IsStarConvexSet.iInter** 是 Mathlib 中的一个定理，位于命名空间 `Convexity.IsStarCo
nvexSet`。
形式化陈述：∀ {R : Type u_1} {X : Type u_2} {ι : Sort u_4} [inst : Semiring R] [inst_1
 : PartialOrder R]   [inst_2 : IsStrictOrderedRing R] [inst_3 : Convexity.Convex
Space R X] {x : X} {s : ι → Set X},   (∀ (i : ι), Convexity.IsStarConvexSet R x 
(s i)) → Convexity.IsStarConvexSet R x (⋂ i, s i)
参数：∀ (i : ι), Convexity.IsStarConvexSet R x (s i)；⋂ i, s i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma IsStarConvexSet.iInter₂ {s : ∀ i, κ i → Set X} (h : ∀ i j, IsStarConvexSet R x (s i j)) :
    IsStarConvexSet R x (⋂ i, ⋂ j, s i j) := .iInter fun i ↦ .iInter <| h i

@[grind ←]
/-
**Convexity.IsStarConvexSet.sUnion** 是 Mathlib 中的一个定理，位于命名空间 `Convexity.IsStarCo
nvexSet`。
形式化陈述：∀ {R : Type u_1} {X : Type u_2} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : IsStrictOrderedRing R]   [inst_3 : Convexity.ConvexSpace R X] {x :
 X} {S : Set (Set X)},   (∀ s ∈ S, Convexity.IsStarConvexSet R x s) → Convexity.
IsStarConvexSet R x (⋃₀ S)
参数：Set X；∀ s ∈ S, Convexity.IsStarConvexSet R x s；⋃₀ S。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma IsStarConvexSet.sUnion {S : Set (Set X)} (hS : ∀ s ∈ S, IsStarConvexSet R x s) :
    IsStarConvexSet R x (⋃₀ S) := by
  rintro y ⟨s, hs, hy⟩ a ha b hb hab; exact ⟨s, hs, hS _ hs hy _ ..⟩

@[grind ←]
/-
**Convexity.IsStarConvexSet.iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Convexity.IsStarCo
nvexSet`。
形式化陈述：∀ {R : Type u_1} {X : Type u_2} {ι : Sort u_4} [inst : Semiring R] [inst_1
 : PartialOrder R]   [inst_2 : IsStrictOrderedRing R] [inst_3 : Convexity.Convex
Space R X] {x : X} {s : ι → Set X},   (∀ (i : ι), Convexity.IsStarConvexSet R x 
(s i)) → Convexity.IsStarConvexSet R x (⋃ i, s i)
参数：∀ (i : ι), Convexity.IsStarConvexSet R x (s i)；⋃ i, s i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convexity.IsStarConvexSet.sUnion`：∀ {R : Type u_1} {X : Type u_2} [inst 
: Semiring R] [inst_1 : PartialOrder R] [inst_2 : IsStrictOrderedRing R]   [inst
_3 : Convexity.ConvexS…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
protected lemma IsStarConvexSet.iUnion {s : ι → Set X} (hs : ∀ i, IsStarConvexSet R x (s i)) :
    IsStarConvexSet R x (⋃ i, s i) := .sUnion <| by simpa
/-
**Convexity.IsStarConvexSet.iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Convexity.IsStarCo
nvexSet`。
形式化陈述：∀ {R : Type u_1} {X : Type u_2} {ι : Sort u_4} [inst : Semiring R] [inst_1
 : PartialOrder R]   [inst_2 : IsStrictOrderedRing R] [inst_3 : Convexity.Convex
Space R X] {x : X} {s : ι → Set X},   (∀ (i : ι), Convexity.IsStarConvexSet R x 
(s i)) → Convexity.IsStarConvexSet R x (⋃ i, s i)
参数：∀ (i : ι), Convexity.IsStarConvexSet R x (s i)；⋃ i, s i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convexity.IsStarConvexSet.sUnion`：∀ {R : Type u_1} {X : Type u_2} [inst 
: Semiring R] [inst_1 : PartialOrder R] [inst_2 : IsStrictOrderedRing R]   [inst
_3 : Convexity.ConvexS…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
protected lemma IsStarConvexSet.iUnion₂ {s : ∀ i, κ i → Set X}
    (h : ∀ i j, IsStarConvexSet R x (s i j)) : IsStarConvexSet R x (⋃ i, ⋃ j, s i j) :=
  .iUnion fun i ↦ .iUnion <| h i
/-
**Convexity.IsConvexSet.isStarConvexSet** 是 Mathlib 中的一个定理，位于命名空间 `Convexity.IsC
onvexSet`。
形式化陈述：∀ {R : Type u_1} {X : Type u_2} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : IsStrictOrderedRing R]   [inst_3 : Convexity.ConvexSpace R X] {x :
 X} {s : Set X},   Convexity.IsConvexSet R s → x ∈ s → Convexity.IsStarConvexSet
 R x s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convexity.IsConvexSet.convexCombPair_mem`：∀ {R : Type u_3} {X : Type u_5
} [inst : Semiring R] [inst_1 : PartialOrder R] [inst_2 : IsStrictOrderedRing R]
   [inst_3 : Convexity.ConvexS…
-/
lemma IsConvexSet.isStarConvexSet (hs : IsConvexSet R s) (hx : x ∈ s) : IsStarConvexSet R x s :=
  fun _y hy _a _b _ha _hb _hab ↦ hs.convexCombPair_mem hx hy ..
/-
**Convexity.IsStarConvexSet.mem** 是 Mathlib 中的一个定理，位于命名空间 `Convexity.IsStarConve
xSet`。
形式化陈述：∀ {R : Type u_1} {X : Type u_2} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : IsStrictOrderedRing R]   [inst_3 : Convexity.ConvexSpace R X] {x :
 X} {s : Set X}, Convexity.IsStarConvexSet R x s → s.Nonempty → x ∈ s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Convexity.convexCombPair_one`：convexCombPair_one {x y : M} : convexCombP
air (1 : R) 0 (by simp) (by simp) (by simp) x y = x
-/
lemma IsStarConvexSet.mem (hs : IsStarConvexSet R x s) (hs₀ : s.Nonempty) : x ∈ s := by
  obtain ⟨y, hy⟩ := hs₀; simpa using hs hy zero_le_one le_rfl (add_zero _)

@[grind ←]
/-
**Convexity.IsStarConvexSet.preimage** 是 Mathlib 中的一个定理，位于命名空间 `Convexity.IsStar
ConvexSet`。
形式化陈述：∀ {R : Type u_1} {X : Type u_2} {Y : Type u_3} [inst : Semiring R] [inst_1
 : PartialOrder R]   [inst_2 : IsStrictOrderedRing R] [inst_3 : Convexity.Convex
Space R X] [inst_4 : Convexity.ConvexSpace R Y] {f : X → Y}   {x : X} {s : Set Y
},   Convexity.IsAffineMap R f → Convexity.IsStarConvexSet R (f x) s → Convexity
.IsStarConvexSet R x (f ⁻¹' s)
参数：f x；f ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Convexity.IsAffineMap.map_convexCombPair`：∀ {R : Type u_1} {M : Type u_3
} {N : Type u_4} [inst : PartialOrder R] [inst_1 : Semiring R]   [inst_2 : IsStr
ictOrderedRing R] [inst_3 : Co…
-/
protected lemma IsStarConvexSet.preimage {s : Set Y} (hf : IsAffineMap R f)
    (hs : IsStarConvexSet R (f x) s) : IsStarConvexSet R x (f ⁻¹' s) :=
  fun y hy a b ha hb hab ↦ by simpa [mem_preimage, hf.map_convexCombPair] using hs hy _ ..

@[grind <=]
/-
**Convexity.IsStarConvexSet.image** 是 Mathlib 中的一个定理，位于命名空间 `Convexity.IsStarCon
vexSet`。
形式化陈述：∀ {R : Type u_1} {X : Type u_2} {Y : Type u_3} [inst : Semiring R] [inst_1
 : PartialOrder R]   [inst_2 : IsStrictOrderedRing R] [inst_3 : Convexity.Convex
Space R X] [inst_4 : Convexity.ConvexSpace R Y] {f : X → Y}   {x : X} {s : Set X
},   Convexity.IsAffineMap R f → Convexity.IsStarConvexSet R x s → Convexity.IsS
tarConvexSet R (f x) (f '' s)
参数：f x；f '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convexity.IsAffineMap.map_convexCombPair`：∀ {R : Type u_1} {M : Type u_3
} {N : Type u_4} [inst : PartialOrder R] [inst_1 : Semiring R]   [inst_2 : IsStr
ictOrderedRing R] [inst_3 : Co…
-/
protected lemma IsStarConvexSet.image (hf : IsAffineMap R f) (hs : IsStarConvexSet R x s) :
    IsStarConvexSet R (f x) (f '' s) := by
  rintro _ ⟨y, hy, rfl⟩ a b ha hb hab; exact ⟨_, hs hy _ .., hf.map_convexCombPair ..⟩

@[grind ←]
/-
**Convexity.IsStarConvexSet.prod** 是 Mathlib 中的一个定理，位于命名空间 `Convexity.IsStarConv
exSet`。
形式化陈述：∀ {R : Type u_1} {X : Type u_2} {Y : Type u_3} [inst : Semiring R] [inst_1
 : PartialOrder R]   [inst_2 : IsStrictOrderedRing R] [inst_3 : Convexity.Convex
Space R X] [inst_4 : Convexity.ConvexSpace R Y] {x : X}   {s : Set X} {t : Set Y
} {y : Y},   Convexity.IsStarConvexSet R x s → Convexity.IsStarConvexSet R y t →
 Convexity.IsStarConvexSet R (x, y) (s ×ˢ t)
参数：x, y；s ×ˢ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Prod.fst_convexCombPair`：fst_convexCombPair (a b : R) (ha hb hab) (x y :
 X × Y) : (convexCombPair a b ha hb hab x y).fst = convexCombPair a b ha hb hab 
x.fst y.fst
· 使用引理 `Prod.snd_convexCombPair`：snd_convexCombPair (a b : R) (ha hb hab) (x y :
 X × Y) : (convexCombPair a b ha hb hab x y).snd = convexCombPair a b ha hb hab 
x.snd y.snd
-/
protected lemma IsStarConvexSet.prod {t : Set Y} {y : Y} (hs : IsStarConvexSet R x s)
    (ht : IsStarConvexSet R y t) : IsStarConvexSet R (x, y) (s ×ˢ t) := by
  rintro ⟨w, z⟩ ⟨hw, hz⟩ a b ha hb hab; exact ⟨by simpa using hs hw _ .., by simpa using ht hz _ ..⟩

@[grind ←]
/-
**Convexity.IsStarConvexSet.pi** 是 Mathlib 中的一个定理，位于命名空间 `Convexity.IsStarConvex
Set`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : PartialOrder R] [inst_2 : I
sStrictOrderedRing R] {ι : Type u_6}   {X : ι → Type u_7} [inst_3 : (i : ι) → Co
nvexity.ConvexSpace R (X i)] {s : Set ι} {x : (i : ι) → X i}   {t : (i : ι) → Se
t (X i)}, (∀ i ∈ s, Convexity.IsStarConvexSet R (x i) (t i)) → Convexity.IsStarC
onvexSet R x (s.pi t)
参数：i : ι；X i；i : ι；i : ι；X i；∀ i ∈ s, Convexity.IsStarConvexSet R (x i) (t i)；s.
pi t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Pi.convexCombPair_apply`：convexCombPair_apply (a b : R) (ha hb hab) (f g
 : forall i, X i) (i : ι) : convexCombPair a b ha hb hab f g i = convexCombPair 
a b ha hb hab…
-/
protected lemma IsStarConvexSet.pi {ι : Type*} {X : ι → Type*} [∀ i, ConvexSpace R (X i)]
    {s : Set ι} {x : ∀ i, X i} {t : ∀ i, Set (X i)} (ht : ∀ i ∈ s, IsStarConvexSet R (x i) (t i)) :
    IsStarConvexSet R x (s.pi t) :=
  fun y hy a b ha hb hab i hi ↦ by simpa using ht _ hi (hy _ hi) _ ..

end Semiring
end Convexity

