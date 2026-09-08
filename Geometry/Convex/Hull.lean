/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Geometry.Convex.Set
public import Mathlib.Order.Closure

/-!
# Convex hull

This file defines the convex hull of a set in a convex space. `convexHull R s` is the smallest
convex set containing `s`. In order theory speak, this is a closure operator.
-/

public section

open Set

namespace Convexity
variable {R X Y : Type*} [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] [ConvexSpace R X]
  [ConvexSpace R Y] {C s t : Set X} {x y : X}

variable (R) in
/-- The convex hull of a set `s` is the minimal convex set that includes `s`. -/
/-
**Convexity.convexHull** 是 Mathlib 中的一个定义，位于命名空间 `Convexity`。
形式化陈述：convexHull : ClosureOperator (Set X)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Convexity.IsConvexSet.sInter`：∀ {R : Type u_3} {X : Type u_5} [inst : Se
miring R] [inst_1 : PartialOrder R] [inst_2 : IsStrictOrderedRing R]   [inst_3 :
 Convexity.ConvexS…

--- 原说明 ---
The convex hull of a set `s` is the minimal convex set that includes `s`.
-/
def convexHull : ClosureOperator (Set X) :=
  .ofCompletePred (IsConvexSet R) (fun _ ↦ .sInter)

set_option backward.isDefEq.respectTransparency.types false in
/-
**Convexity.subset_convexHull_iff** 是 Mathlib 中的一个引理，位于命名空间 `Convexity`。
形式化陈述：subset_convexHull_iff : t subseteq convexHull R s ↔ forall C, s subseteq C
 -> IsConvexSet R C -> t subseteq C
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Convexity.IsConvexSet.sInter`：∀ {R : Type u_3} {X : Type u_5} [inst : Se
miring R] [inst_1 : PartialOrder R] [inst_2 : IsStrictOrderedRing R]   [inst_3 :
 Convexity.ConvexS…
· 使用定理 `ClosureOperator.ofCompletePred_apply`：∀ {α : Type u_1} [inst : CompleteL
attice α] (p : α → Prop) (hsinf : ∀ (s : Set α), (∀ a ∈ s, p a) → p (sInf s)) (a
 : α),   (ClosureOperator.…
· 使用定理 `Set.iInter_subtype`：iInter_subtype (p : α -> Prop) (s : { x // p x } -> 
Set β) : ⋂ x : { x // p x }, s x = ⋂ (x) (hx : p x), s ⟨x, hx⟩
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iInter_and`：iInter_and {p q : Prop} (s : p ∧ q -> Set α) : ⋂ h, s h 
= ⋂ (hp) (hq), s ⟨hp, hq⟩
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma subset_convexHull_iff : t ⊆ convexHull R s ↔ ∀ C, s ⊆ C → IsConvexSet R C → t ⊆ C := by
  simp [convexHull, iInter_subtype, iInter_and]
/-
**Convexity.subset_convexHull_self** 是 Mathlib 中的一个定理，位于命名空间 `Convexity`。
形式化陈述：∀ {R : Type u_1} {X : Type u_2} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : IsStrictOrderedRing R]   [inst_3 : Convexity.ConvexSpace R X] {s :
 Set X}, s ⊆ (Convexity.convexHull R) s
参数：Convexity.convexHull R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosureOperator.le_closure`：le_closure (x : α) : x <= c x
-/
@[simp] lemma subset_convexHull_self : s ⊆ convexHull R s := ClosureOperator.le_closure _ s
/-
**Convexity.IsConvexSet.convexHull** 是 Mathlib 中的一个定理，位于命名空间 `Convexity.IsConvex
Set`。
形式化陈述：∀ {R : Type u_1} {X : Type u_2} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : IsStrictOrderedRing R]   [inst_3 : Convexity.ConvexSpace R X] {s :
 Set X}, Convexity.IsConvexSet R ((Convexity.convexHull R) s)
参数：(Convexity.convexHull R) s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosureOperator.isClosed_closure`：∀ {α : Type u_1} [inst : Preorder α] (
c : ClosureOperator α) (x : α), c.IsClosed (c x)
· 使用定理 `Convexity.IsConvexSet.sInter`：∀ {R : Type u_3} {X : Type u_5} [inst : Se
miring R] [inst_1 : PartialOrder R] [inst_2 : IsStrictOrderedRing R]   [inst_3 :
 Convexity.ConvexS…
-/
protected lemma IsConvexSet.convexHull : IsConvexSet R (convexHull R s) :=
  ClosureOperator.isClosed_closure (.ofCompletePred (IsConvexSet R) _) s

set_option backward.isDefEq.respectTransparency.types false in
/-
**Convexity.convexHull_eq_iInter** 是 Mathlib 中的一个引理，位于命名空间 `Convexity`。
形式化陈述：convexHull_eq_iInter : convexHull R s = ⋂ (t : Set X) (_ : s subseteq t) (
_ : IsConvexSet R t), t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Convexity.IsConvexSet.sInter`：∀ {R : Type u_3} {X : Type u_5} [inst : Se
miring R] [inst_1 : PartialOrder R] [inst_2 : IsStrictOrderedRing R]   [inst_3 :
 Convexity.ConvexS…
· 使用定理 `ClosureOperator.ofCompletePred_apply`：∀ {α : Type u_1} [inst : CompleteL
attice α] (p : α → Prop) (hsinf : ∀ (s : Set α), (∀ a ∈ s, p a) → p (sInf s)) (a
 : α),   (ClosureOperator.…
· 使用定理 `Set.iInter_subtype`：iInter_subtype (p : α -> Prop) (s : { x // p x } -> 
Set β) : ⋂ x : { x // p x }, s x = ⋂ (x) (hx : p x), s ⟨x, hx⟩
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iInter_and`：iInter_and {p q : Prop} (s : p ∧ q -> Set α) : ⋂ h, s h 
= ⋂ (hp) (hq), s ⟨hp, hq⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma convexHull_eq_iInter :
    convexHull R s = ⋂ (t : Set X) (_ : s ⊆ t) (_ : IsConvexSet R t), t := by
  simp [convexHull, iInter_subtype, iInter_and]
/-
**Convexity.mem_convexHull_iff** 是 Mathlib 中的一个引理，位于命名空间 `Convexity`。
形式化陈述：mem_convexHull_iff : x in convexHull R s ↔ forall t, s subseteq t -> IsCon
vexSet R t -> x in t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Convexity.convexHull_eq_iInter`：convexHull_eq_iInter : convexHull R s = 
⋂ (t : Set X) (_ : s subseteq t) (_ : IsConvexSet R t), t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_convexHull_iff : x ∈ convexHull R s ↔ ∀ t, s ⊆ t → IsConvexSet R t → x ∈ t := by
  simp_rw [convexHull_eq_iInter, mem_iInter]
/-
**Convexity.convexHull_min** 是 Mathlib 中的一个引理，位于命名空间 `Convexity`。
形式化陈述：convexHull_min : s subseteq C -> IsConvexSet R C -> convexHull R s subsete
q C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ClosureOperator.closure_min`：closure_min (hxy : x <= y) (hy : c.IsClosed
 y) : c x <= y
· 使用定理 `Convexity.IsConvexSet.sInter`：∀ {R : Type u_3} {X : Type u_5} [inst : Se
miring R] [inst_1 : PartialOrder R] [inst_2 : IsStrictOrderedRing R]   [inst_3 :
 Convexity.ConvexS…
-/
lemma convexHull_min : s ⊆ C → IsConvexSet R C → convexHull R s ⊆ C :=
  (ClosureOperator.ofCompletePred (IsConvexSet R) _).closure_min
/-
**Convexity.IsConvexSet.convexHull_subset_iff** 是 Mathlib 中的一个定理，位于命名空间 `Convexi
ty.IsConvexSet`。
形式化陈述：∀ {R : Type u_1} {X : Type u_2} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : IsStrictOrderedRing R]   [inst_3 : Convexity.ConvexSpace R X] {C s
 : Set X},   Convexity.IsConvexSet R C → ((Convexity.convexHull R) s ⊆ C ↔ s ⊆ C
)
参数：(Convexity.convexHull R) s ⊆ C ↔ s ⊆ C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosureOperator.IsClosed.closure_le_iff`：∀ {α : Type u_1} [inst : Preord
er α] {c : ClosureOperator α} {x y : α}, c.IsClosed y → (c x ≤ y ↔ x ≤ y)
-/
lemma IsConvexSet.convexHull_subset_iff (hC : IsConvexSet R C) : convexHull R s ⊆ C ↔ s ⊆ C :=
  ClosureOperator.IsClosed.closure_le_iff hC

@[gcongr]
/-
**Convexity.convexHull_mono** 是 Mathlib 中的一个引理，位于命名空间 `Convexity`。
形式化陈述：convexHull_mono (hst : s subseteq t) : convexHull R s subseteq convexHull 
R t
参数：hst : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosureOperator.monotone`：monotone : Monotone c
-/
lemma convexHull_mono (hst : s ⊆ t) : convexHull R s ⊆ convexHull R t :=
  ClosureOperator.monotone _ hst
/-
**Convexity.convexHull_eq_self** 是 Mathlib 中的一个引理，位于命名空间 `Convexity`。
形式化陈述：convexHull_eq_self : convexHull R C = C ↔ IsConvexSet R C
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `ClosureOperator.isClosed_iff`：∀ {α : Type u_1} [inst : Preorder α] (self
 : ClosureOperator α) {x : α}, self.IsClosed x ↔ self.toFun x = x
-/
lemma convexHull_eq_self : convexHull R C = C ↔ IsConvexSet R C :=
  (ClosureOperator.isClosed_iff _).symm
/-
**Convexity.convexHull_subset_self** 是 Mathlib 中的一个引理，位于命名空间 `Convexity`。
形式化陈述：convexHull_subset_self : convexHull R C subseteq C ↔ IsConvexSet R C
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma convexHull_subset_self : convexHull R C ⊆ C ↔ IsConvexSet R C := by
  simp [← convexHull_eq_self, subset_antisymm_iff]

protected alias ⟨_, IsConvexSet.convexHull_eq_self⟩ := convexHull_eq_self

variable (R) in
/-
**Convexity.convexHull_empty** 是 Mathlib 中的一个定理，位于命名空间 `Convexity`。
形式化陈述：∀ (R : Type u_1) {X : Type u_2} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : IsStrictOrderedRing R]   [inst_3 : Convexity.ConvexSpace R X], (Co
nvexity.convexHull R) ∅ = ∅
参数：R : Type u_1；Convexity.convexHull R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convexity.IsConvexSet.convexHull_eq_self`：∀ {R : Type u_1} {X : Type u_2
} [inst : Semiring R] [inst_1 : PartialOrder R] [inst_2 : IsStrictOrderedRing R]
   [inst_3 : Convexity.ConvexS…
· 使用定理 `Convexity.IsConvexSet.empty`：∀ {R : Type u_3} {X : Type u_5} [inst : Sem
iring R] [inst_1 : PartialOrder R] [inst_2 : IsStrictOrderedRing R]   [inst_3 : 
Convexity.ConvexS…
-/
@[simp] lemma convexHull_empty : convexHull R (∅ : Set X) = ∅ :=
  IsConvexSet.empty.convexHull_eq_self
/-
**Convexity.convexHull_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Convexity`。
形式化陈述：∀ {R : Type u_1} {X : Type u_2} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : IsStrictOrderedRing R]   [inst_3 : Convexity.ConvexSpace R X] {s :
 Set X}, (Convexity.convexHull R) s = ∅ ↔ s = ∅
参数：Convexity.convexHull R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Convexity.IsConvexSet.convexHull_subset_iff`：∀ {R : Type u_1} {X : Type 
u_2} [inst : Semiring R] [inst_1 : PartialOrder R] [inst_2 : IsStrictOrderedRing
 R]   [inst_3 : Convexity.ConvexS…
· 使用定理 `Convexity.IsConvexSet.empty`：∀ {R : Type u_3} {X : Type u_5} [inst : Sem
iring R] [inst_1 : PartialOrder R] [inst_2 : IsStrictOrderedRing R]   [inst_3 : 
Convexity.ConvexS…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma convexHull_eq_empty : convexHull R s = ∅ ↔ s = ∅ := by
  simp [← subset_empty_iff, IsConvexSet.empty.convexHull_subset_iff]
/-
**Convexity.convexHull_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Convexity`。
形式化陈述：∀ {R : Type u_1} {X : Type u_2} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : IsStrictOrderedRing R]   [inst_3 : Convexity.ConvexSpace R X] {s :
 Set X}, ((Convexity.convexHull R) s).Nonempty ↔ s.Nonempty
参数：(Convexity.convexHull R) s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma convexHull_nonempty : (convexHull R s).Nonempty ↔ s.Nonempty := by
  simp [nonempty_iff_ne_empty]

protected alias ⟨_, Set.Nonempty.convexHull'⟩ := convexHull_nonempty

variable (R x) in
/-
**Convexity.convexHull_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Convexity`。
形式化陈述：∀ (R : Type u_1) {X : Type u_2} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : IsStrictOrderedRing R]   [inst_3 : Convexity.ConvexSpace R X] (x :
 X), (Convexity.convexHull R) {x} = {x}
参数：R : Type u_1；x : X；Convexity.convexHull R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convexity.IsConvexSet.convexHull_eq_self`：∀ {R : Type u_1} {X : Type u_2
} [inst : Semiring R] [inst_1 : PartialOrder R] [inst_2 : IsStrictOrderedRing R]
   [inst_3 : Convexity.ConvexS…
· 使用定理 `Convexity.IsConvexSet.singleton`：∀ {R : Type u_3} {X : Type u_5} [inst :
 Semiring R] [inst_1 : PartialOrder R] [inst_2 : IsStrictOrderedRing R]   [inst_
3 : Convexity.ConvexS…
-/
@[simp] lemma convexHull_singleton : convexHull R {x} = {x} :=
  IsConvexSet.singleton.convexHull_eq_self
/-
**Convexity.convexHull_univ** 是 Mathlib 中的一个定理，位于命名空间 `Convexity`。
形式化陈述：∀ {R : Type u_1} {X : Type u_2} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : IsStrictOrderedRing R]   [inst_3 : Convexity.ConvexSpace R X], (Co
nvexity.convexHull R) Set.univ = Set.univ
参数：Convexity.convexHull R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convexity.IsConvexSet.convexHull_eq_self`：∀ {R : Type u_1} {X : Type u_2
} [inst : Semiring R] [inst_1 : PartialOrder R] [inst_2 : IsStrictOrderedRing R]
   [inst_3 : Convexity.ConvexS…
· 使用定理 `Convexity.IsConvexSet.univ`：∀ {R : Type u_3} {X : Type u_5} [inst : Semi
ring R] [inst_1 : PartialOrder R] [inst_2 : IsStrictOrderedRing R]   [inst_3 : C
onvexity.ConvexS…
-/
@[simp] lemma convexHull_univ : convexHull R (univ : Set X) = univ :=
  IsConvexSet.univ.convexHull_eq_self
/-
**Convexity.convexHull_eq_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Convexity`。
形式化陈述：∀ {R : Type u_1} {X : Type u_2} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : IsStrictOrderedRing R]   [inst_3 : Convexity.ConvexSpace R X] {s :
 Set X} {x : X}, (Convexity.convexHull R) s = {x} ↔ s = {x}
参数：Convexity.convexHull R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Nonempty.subset_singleton_iff`：∀ {α : Type u_1} {s : Set α} {a : α},
 s.Nonempty → (s ⊆ {a} ↔ s = {a})
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Convexity.convexHull_empty`：∀ (R : Type u_1) {X : Type u_2} [inst : Semi
ring R] [inst_1 : PartialOrder R] [inst_2 : IsStrictOrderedRing R]   [inst_3 : C
onvexity.ConvexS…
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Convexity.subset_convexHull_self`：∀ {R : Type u_1} {X : Type u_2} [inst 
: Semiring R] [inst_1 : PartialOrder R] [inst_2 : IsStrictOrderedRing R]   [inst
_3 : Convexity.ConvexS…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Convexity.convexHull_singleton`：∀ (R : Type u_1) {X : Type u_2} [inst : 
Semiring R] [inst_1 : PartialOrder R] [inst_2 : IsStrictOrderedRing R]   [inst_3
 : Convexity.ConvexS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma convexHull_eq_singleton : convexHull R s = {x} ↔ s = {x} where
  mp hs := by
    rw [← Set.Nonempty.subset_singleton_iff, ← hs]
    · exact subset_convexHull_self
    · by_contra! hs
      simp_all [eq_comm (a := ∅)]
  mpr hs := by simp [hs]

variable (R s t) in
@[simp]
/-
**Convexity.convexHull_convexHull_union** 是 Mathlib 中的一个引理，位于命名空间 `Convexity`。
形式化陈述：convexHull_convexHull_union : convexHull R (convexHull R s union t) = conv
exHull R (s union t)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosureOperator.closure_sup_closure_left`：closure_sup_closure_left (x y 
: α) : c (c x ⊔ y) = c (x ⊔ y)
-/
lemma convexHull_convexHull_union :
    convexHull R (convexHull R s ∪ t) = convexHull R (s ∪ t) :=
  ClosureOperator.closure_sup_closure_left ..

variable (R s t) in
@[simp]
/-
**Convexity.convexHull_union_convexHull** 是 Mathlib 中的一个引理，位于命名空间 `Convexity`。
形式化陈述：convexHull_union_convexHull : convexHull R (s union convexHull R t) = conv
exHull R (s union t)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosureOperator.closure_sup_closure_right`：closure_sup_closure_right (x 
y : α) : c (x ⊔ c y) = c (x ⊔ y)
-/
lemma convexHull_union_convexHull :
    convexHull R (s ∪ convexHull R t) = convexHull R (s ∪ t) :=
  ClosureOperator.closure_sup_closure_right ..
/-
**Convexity.IsConvexSet.sdiff_singleton_iff_notMem_convexHull** 是 Mathlib 中的一个定理
，位于命名空间 `Convexity.IsConvexSet`。
形式化陈述：∀ {R : Type u_1} {X : Type u_2} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : IsStrictOrderedRing R]   [inst_3 : Convexity.ConvexSpace R X] {s :
 Set X} {x : X},   Convexity.IsConvexSet R s → (Convexity.IsConvexSet R (s \ {x}
) ↔ x ∉ (Convexity.convexHull R) (s \ {x}))
参数：Convexity.IsConvexSet R (s \ {x}) ↔ x ∉ (Convexity.convexHull R) (s \ {x})。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Convexity.IsConvexSet.convexHull_eq_self`：∀ {R : Type u_1} {X : Type u_2
} [inst : Semiring R] [inst_1 : PartialOrder R] [inst_2 : IsStrictOrderedRing R]
   [inst_3 : Convexity.ConvexS…
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Convexity.convexHull_subset_self`：convexHull_subset_self : convexHull R 
C subseteq C ↔ IsConvexSet R C
· 使用引理 `Convexity.convexHull_min`：convexHull_min : s subseteq C -> IsConvexSet R
 C -> convexHull R s subseteq C
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
-/
lemma IsConvexSet.sdiff_singleton_iff_notMem_convexHull (hs : IsConvexSet R s) :
    IsConvexSet R (s \ {x}) ↔ x ∉ convexHull R (s \ {x}) where
  mp hsx hx := by
    rw [hsx.convexHull_eq_self] at hx
    exact hx.2 (mem_singleton _)
  mpr hx := by
    rw [← convexHull_subset_self]
    rintro y hy
    exact ⟨convexHull_min sdiff_subset hs hy, by rintro rfl; exact hx hy⟩
/-
**Convexity.IsAffineMap.image_convexHull** 是 Mathlib 中的一个定理，位于命名空间 `Convexity.Is
AffineMap`。
形式化陈述：∀ {R : Type u_1} {X : Type u_2} {Y : Type u_3} [inst : Semiring R] [inst_1
 : PartialOrder R]   [inst_2 : IsStrictOrderedRing R] [inst_3 : Convexity.Convex
Space R X] [inst_4 : Convexity.ConvexSpace R Y]   {f : X → Y},   Convexity.IsAff
ineMap R f → ∀ (s : Set X), f '' (Convexity.convexHull R) s = (Convexity.convexH
ull R) (f '' s)
参数：s : Set X；Convexity.convexHull R；Convexity.convexHull R；f '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `subset_antisymm_iff`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst 
: PartialOrder α] {a b : α}, a = b ↔ a ⊆ b ∧ b ⊆ a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `Convexity.IsConvexSet.convexHull_subset_iff`：∀ {R : Type u_1} {X : Type 
u_2} [inst : Semiring R] [inst_1 : PartialOrder R] [inst_2 : IsStrictOrderedRing
 R]   [inst_3 : Convexity.ConvexS…
· 使用定理 `Convexity.IsConvexSet.preimage`：∀ {R : Type u_3} {X : Type u_5} {Y : Typ
e u_6} [inst : Semiring R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOrdered
Ring R] [inst_3 : Co…
· 使用定理 `Convexity.IsConvexSet.convexHull`：∀ {R : Type u_1} {X : Type u_2} [inst 
: Semiring R] [inst_1 : PartialOrder R] [inst_2 : IsStrictOrderedRing R]   [inst
_3 : Convexity.ConvexS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Convexity.IsConvexSet.image`：∀ {R : Type u_3} {X : Type u_5} {Y : Type u
_6} [inst : Semiring R] [inst_1 : PartialOrder R]   [inst_2 : IsStrictOrderedRin
g R] [inst_3 : Co…
· 使用定理 `Convexity.subset_convexHull_self`：∀ {R : Type u_1} {X : Type u_2} [inst 
: Semiring R] [inst_1 : PartialOrder R] [inst_2 : IsStrictOrderedRing R]   [inst
_3 : Convexity.ConvexS…
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
-/
lemma IsAffineMap.image_convexHull {f : X → Y} (hf : IsAffineMap R f) (s : Set X) :
    f '' convexHull R s = convexHull R (f '' s) := by
  rw [subset_antisymm_iff,
    image_subset_iff, (IsConvexSet.convexHull.preimage hf).convexHull_subset_iff,
    ← image_subset_iff, (IsConvexSet.convexHull.image hf).convexHull_subset_iff]
  exact ⟨subset_convexHull_self, image_mono subset_convexHull_self⟩

end Convexity

