/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Yaël Dillies
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Order.Closure

/-!
# Convex hull

This file defines the convex hull of a set `s` in a module. `convexHull 𝕜 s` is the smallest convex
set containing `s`. In order theory speak, this is a closure operator.

## Implementation notes

`convexHull` is defined as a closure operator. This gives access to the `ClosureOperator` API
while the impact on writing code is minimal as `convexHull 𝕜 s` is automatically elaborated as
`(convexHull 𝕜) s`.
-/

@[expose] public section


open Set

open scoped Pointwise

variable {𝕜 E F : Type*}

section convexHull

section OrderedSemiring

variable [Semiring 𝕜] [PartialOrder 𝕜]

section AddCommMonoid

variable (𝕜)
variable [AddCommMonoid E] [AddCommMonoid F] [Module 𝕜 E] [Module 𝕜 F]

/-- The convex hull of a set `s` is the minimal convex set that includes `s`. -/
@[simps! isClosed]
/-
**convexHull** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：convexHull : ClosureOperator (Set E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The convex hull of a set `s` is the minimal convex set that includes `s`.
-/
def convexHull : ClosureOperator (Set E) := .ofCompletePred (Convex 𝕜) fun _ ↦ convex_sInter

variable (s : Set E)
/-
**subset_convexHull** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subset_convexHull : s subseteq convexHull 𝕜 s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosureOperator.le_closure`：le_closure (x : α) : x <= c x
-/
theorem subset_convexHull : s ⊆ convexHull 𝕜 s :=
  (convexHull 𝕜).le_closure s
/-
**convex_convexHull** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convex_convexHull : Convex 𝕜 (convexHull 𝕜 s)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosureOperator.isClosed_closure`：∀ {α : Type u_1} [inst : Preorder α] (
c : ClosureOperator α) (x : α), c.IsClosed (c x)
-/
theorem convex_convexHull : Convex 𝕜 (convexHull 𝕜 s) := (convexHull 𝕜).isClosed_closure s

set_option backward.isDefEq.respectTransparency false in
/-
**convexHull_eq_iInter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convexHull_eq_iInter : convexHull 𝕜 s = ⋂ (t : Set E) (_ : s subseteq t) (
_ : Convex 𝕜 t), t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
theorem convexHull_eq_iInter : convexHull 𝕜 s = ⋂ (t : Set E) (_ : s ⊆ t) (_ : Convex 𝕜 t), t := by
  simp [convexHull, iInter_subtype, iInter_and]

variable {𝕜 s} {t : Set E} {x y : E}
/-
**mem_convexHull_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_convexHull_iff : x in convexHull 𝕜 s ↔ forall t, s subseteq t -> Conve
x 𝕜 t -> x in t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `convexHull_eq_iInter`：convexHull_eq_iInter : convexHull 𝕜 s = ⋂ (t : Set
 E) (_ : s subseteq t) (_ : Convex 𝕜 t), t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_convexHull_iff : x ∈ convexHull 𝕜 s ↔ ∀ t, s ⊆ t → Convex 𝕜 t → x ∈ t := by
  simp_rw [convexHull_eq_iInter, mem_iInter]
/-
**convexHull_min** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convexHull_min : s subseteq t -> Convex 𝕜 t -> convexHull 𝕜 s subseteq t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ClosureOperator.closure_min`：closure_min (hxy : x <= y) (hy : c.IsClosed
 y) : c x <= y
-/
theorem convexHull_min : s ⊆ t → Convex 𝕜 t → convexHull 𝕜 s ⊆ t := (convexHull 𝕜).closure_min
/-
**Convex.convexHull_subset_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.convexHull_subset_iff (ht : Convex 𝕜 t) : convexHull 𝕜 s subseteq t
 ↔ s subseteq t
参数：ht : Convex 𝕜 t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosureOperator.IsClosed.closure_le_iff`：∀ {α : Type u_1} [inst : Preord
er α] {c : ClosureOperator α} {x y : α}, c.IsClosed y → (c x ≤ y ↔ x ≤ y)
-/
theorem Convex.convexHull_subset_iff (ht : Convex 𝕜 t) : convexHull 𝕜 s ⊆ t ↔ s ⊆ t :=
  (show (convexHull 𝕜).IsClosed t from ht).closure_le_iff

@[mono, gcongr]
/-
**convexHull_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convexHull_mono (hst : s subseteq t) : convexHull 𝕜 s subseteq convexHull 
𝕜 t
参数：hst : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosureOperator.monotone`：monotone : Monotone c
-/
theorem convexHull_mono (hst : s ⊆ t) : convexHull 𝕜 s ⊆ convexHull 𝕜 t :=
  (convexHull 𝕜).monotone hst
/-
**convexHull_eq_self** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：convexHull_eq_self : convexHull 𝕜 s = s ↔ Convex 𝕜 s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `ClosureOperator.isClosed_iff`：∀ {α : Type u_1} [inst : Preorder α] (self
 : ClosureOperator α) {x : α}, self.IsClosed x ↔ self.toFun x = x
-/
lemma convexHull_eq_self : convexHull 𝕜 s = s ↔ Convex 𝕜 s := (convexHull 𝕜).isClosed_iff.symm

alias ⟨_, Convex.convexHull_eq⟩ := convexHull_eq_self

@[simp]
/-
**convexHull_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convexHull_univ : convexHull 𝕜 (univ : Set E) = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosureOperator.closure_top`：closure_top : c ⊤ = ⊤
-/
theorem convexHull_univ : convexHull 𝕜 (univ : Set E) = univ :=
  ClosureOperator.closure_top (convexHull 𝕜)

@[simp]
/-
**convexHull_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convexHull_empty : convexHull 𝕜 (∅ : Set E) = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.convexHull_eq`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : Semiring 𝕜
] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : _root_.Module
 𝕜 E] {s :…
· 使用定理 `convex_empty`：convex_empty : Convex 𝕜 (∅ : Set E)
-/
theorem convexHull_empty : convexHull 𝕜 (∅ : Set E) = ∅ :=
  convex_empty.convexHull_eq

@[simp]
/-
**convexHull_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convexHull_eq_empty : convexHull 𝕜 s = ∅ ↔ s = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.subset_empty_iff`：subset_empty_iff {s : Set α} : s subseteq ∅ ↔ s = 
∅
· 使用定理 `subset_convexHull`：subset_convexHull : s subseteq convexHull 𝕜 s
· 使用定理 `convexHull_empty`：convexHull_empty : convexHull 𝕜 (∅ : Set E) = ∅
-/
theorem convexHull_eq_empty : convexHull 𝕜 s = ∅ ↔ s = ∅ := by
  constructor
  · intro h
    rw [← Set.subset_empty_iff, ← h]
    exact subset_convexHull 𝕜 _
  · rintro rfl
    exact convexHull_empty

@[simp]
/-
**convexHull_nonempty_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convexHull_nonempty_iff : (convexHull 𝕜 s).Nonempty ↔ s.Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `convexHull_eq_empty`：convexHull_eq_empty : convexHull 𝕜 s = ∅ ↔ s = ∅
-/
theorem convexHull_nonempty_iff : (convexHull 𝕜 s).Nonempty ↔ s.Nonempty := by
  rw [nonempty_iff_ne_empty, nonempty_iff_ne_empty, Ne, Ne]
  exact not_congr convexHull_eq_empty

protected alias ⟨_, Set.Nonempty.convexHull⟩ := convexHull_nonempty_iff
/-
**segment_subset_convexHull** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：segment_subset_convexHull (hx : x in s) (hy : y in s) : segment 𝕜 x y subs
eteq convexHull 𝕜 s
参数：hx : x in s；hy : y in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.segment_subset`：Convex.segment_subset (h : Convex 𝕜 s) {x y : E} 
(hx : x in s) (hy : y in s) : [x -[𝕜] y] subseteq s
· 使用定理 `convex_convexHull`：convex_convexHull : Convex 𝕜 (convexHull 𝕜 s)
· 使用定理 `subset_convexHull`：subset_convexHull : s subseteq convexHull 𝕜 s
-/
theorem segment_subset_convexHull (hx : x ∈ s) (hy : y ∈ s) : segment 𝕜 x y ⊆ convexHull 𝕜 s :=
  (convex_convexHull _ _).segment_subset (subset_convexHull _ _ hx) (subset_convexHull _ _ hy)

@[simp]
/-
**convexHull_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convexHull_singleton (x : E) : convexHull 𝕜 ({x} : Set E) = {x}
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.convexHull_eq`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : Semiring 𝕜
] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : _root_.Module
 𝕜 E] {s :…
· 使用定理 `convex_singleton`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : Semiring 𝕜] [i
nst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : _root_.Module 𝕜 E
] (c :…
-/
theorem convexHull_singleton (x : E) : convexHull 𝕜 ({x} : Set E) = {x} :=
  (convex_singleton x).convexHull_eq
/-
**convexHull_eq_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : Semiring 𝕜] [inst_1 : PartialOrder
 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : _root_.Module 𝕜 E] {s : Set E} {x : E
}, (convexHull 𝕜) s = {x} ↔ s = {x}
参数：convexHull 𝕜。
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
· 使用定理 `convexHull_empty`：convexHull_empty : convexHull 𝕜 (∅ : Set E) = ∅
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `subset_convexHull`：subset_convexHull : s subseteq convexHull 𝕜 s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `convexHull_singleton`：convexHull_singleton (x : E) : convexHull 𝕜 ({x} :
 Set E) = {x}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma convexHull_eq_singleton : convexHull 𝕜 s = {x} ↔ s = {x} where
  mp hs := by
    rw [← Set.Nonempty.subset_singleton_iff, ← hs]
    · exact subset_convexHull ..
    · by_contra! hs
      simp_all [eq_comm (a := ∅)]
  mpr hs := by simp [hs]

@[simp]
/-
**convexHull_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convexHull_zero : convexHull 𝕜 (0 : Set E) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `convexHull_singleton`：convexHull_singleton (x : E) : convexHull 𝕜 ({x} :
 Set E) = {x}
-/
theorem convexHull_zero : convexHull 𝕜 (0 : Set E) = 0 :=
  convexHull_singleton 0
/-
**convexHull_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : Semiring 𝕜] [inst_1 : PartialOrder
 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : _root_.Module 𝕜 E] {s : Set E}, (conv
exHull 𝕜) s = 0 ↔ s = 0
参数：convexHull 𝕜。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `convexHull_eq_singleton`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : Semirin
g 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : _root_.Mod
ule 𝕜 E] {s :…
-/
@[simp] lemma convexHull_eq_zero : convexHull 𝕜 s = 0 ↔ s = 0 := convexHull_eq_singleton

@[simp]
/-
**convexHull_pair** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convexHull_pair [IsOrderedRing 𝕜] (x y : E) : convexHull 𝕜 {x, y} = segmen
t 𝕜 x y
参数：x y : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `convexHull_min`：convexHull_min : s subseteq t -> Convex 𝕜 t -> convexHul
l 𝕜 s subseteq t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.insert_subset_iff`：insert_subset_iff : insert a s subseteq t ↔ a in 
t ∧ s subseteq t
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `left_mem_segment`：left_mem_segment (x y : E) : x in [x -[𝕜] y]
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `right_mem_segment`：right_mem_segment (x y : E) : y in [x -[𝕜] y]
· 使用定理 `convex_segment`：convex_segment [IsOrderedRing 𝕜] (x y : E) : Convex 𝕜 [x
 -[𝕜] y]
· 使用定理 `segment_subset_convexHull`：segment_subset_convexHull (hx : x in s) (hy :
 y in s) : segment 𝕜 x y subseteq convexHull 𝕜 s
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
-/
theorem convexHull_pair [IsOrderedRing 𝕜] (x y : E) : convexHull 𝕜 {x, y} = segment 𝕜 x y := by
  refine (convexHull_min ?_ <| convex_segment _ _).antisymm
    (segment_subset_convexHull (mem_insert _ _) <| subset_insert _ _ <| mem_singleton _)
  rw [insert_subset_iff, singleton_subset_iff]
  exact ⟨left_mem_segment _ _ _, right_mem_segment _ _ _⟩
/-
**convexHull_convexHull_union_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convexHull_convexHull_union_left (s t : Set E) : convexHull 𝕜 (convexHull 
𝕜 s union t) = convexHull 𝕜 (s union t)
参数：s t : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosureOperator.closure_sup_closure_left`：closure_sup_closure_left (x y 
: α) : c (c x ⊔ y) = c (x ⊔ y)
-/
theorem convexHull_convexHull_union_left (s t : Set E) :
    convexHull 𝕜 (convexHull 𝕜 s ∪ t) = convexHull 𝕜 (s ∪ t) :=
  ClosureOperator.closure_sup_closure_left _ _ _
/-
**convexHull_convexHull_union_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convexHull_convexHull_union_right (s t : Set E) : convexHull 𝕜 (s union co
nvexHull 𝕜 t) = convexHull 𝕜 (s union t)
参数：s t : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosureOperator.closure_sup_closure_right`：closure_sup_closure_right (x 
y : α) : c (x ⊔ c y) = c (x ⊔ y)
-/
theorem convexHull_convexHull_union_right (s t : Set E) :
    convexHull 𝕜 (s ∪ convexHull 𝕜 t) = convexHull 𝕜 (s ∪ t) :=
  ClosureOperator.closure_sup_closure_right _ _ _
/-
**Convex.convex_remove_iff_notMem_convexHull_remove** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：Convex.convex_remove_iff_notMem_convexHull_remove {s : Set E} (hs : Convex
 𝕜 s) (x : E) : Convex 𝕜 (s \ {x}) ↔ x ∉ convexHull 𝕜 (s \ {x})
参数：hs : Convex 𝕜 s；x : E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Convex.convexHull_eq`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : Semiring 𝕜
] [inst_1 : PartialOrder 𝕜] [inst_2 : AddCommMonoid E]   [inst_3 : _root_.Module
 𝕜 E] {s :…
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `subset_convexHull`：subset_convexHull : s subseteq convexHull 𝕜 s
· 使用定理 `convexHull_min`：convexHull_min : s subseteq t -> Convex 𝕜 t -> convexHul
l 𝕜 s subseteq t
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `convex_convexHull`：convex_convexHull : Convex 𝕜 (convexHull 𝕜 s)
-/
theorem Convex.convex_remove_iff_notMem_convexHull_remove {s : Set E} (hs : Convex 𝕜 s) (x : E) :
    Convex 𝕜 (s \ {x}) ↔ x ∉ convexHull 𝕜 (s \ {x}) := by
  constructor
  · rintro hsx hx
    rw [hsx.convexHull_eq] at hx
    exact hx.2 (mem_singleton _)
  rintro hx
  suffices h : s \ {x} = convexHull 𝕜 (s \ {x}) by
    rw [h]
    exact convex_convexHull 𝕜 _
  exact
    Subset.antisymm (subset_convexHull 𝕜 _) fun y hy =>
      ⟨convexHull_min sdiff_subset hs hy, by
        rintro (rfl : y = x)
        exact hx hy⟩
/-
**IsLinearMap.image_convexHull** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLinearMap.image_convexHull {f : E -> F} (hf : IsLinearMap 𝕜 f) (s : Set 
E) : f '' convexHull 𝕜 s = convexHull 𝕜 (f '' s)
参数：hf : IsLinearMap 𝕜 f；s : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `convexHull_min`：convexHull_min : s subseteq t -> Convex 𝕜 t -> convexHul
l 𝕜 s subseteq t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `subset_convexHull`：subset_convexHull : s subseteq convexHull 𝕜 s
· 使用定理 `Convex.is_linear_preimage`：Convex.is_linear_preimage {s : Set F} (hs : C
onvex 𝕜 s) {f : E -> F} (hf : IsLinearMap 𝕜 f) : Convex 𝕜 (f ⁻¹' s)
· 使用定理 `convex_convexHull`：convex_convexHull : Convex 𝕜 (convexHull 𝕜 s)
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Convex.is_linear_image`：Convex.is_linear_image (hs : Convex 𝕜 s) {f : E 
-> F} (hf : IsLinearMap 𝕜 f) : Convex 𝕜 (f '' s)
-/
theorem IsLinearMap.image_convexHull {f : E → F} (hf : IsLinearMap 𝕜 f) (s : Set E) :
    f '' convexHull 𝕜 s = convexHull 𝕜 (f '' s) :=
  Set.Subset.antisymm
    (image_subset_iff.2 <|
      convexHull_min (image_subset_iff.1 <| subset_convexHull 𝕜 _)
        ((convex_convexHull 𝕜 _).is_linear_preimage hf))
    (convexHull_min (image_mono (subset_convexHull 𝕜 s)) <|
      (convex_convexHull 𝕜 s).is_linear_image hf)
/-
**LinearMap.image_convexHull** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.image_convexHull (f : E ->ₗ[𝕜] F) (s : Set E) : f '' convexHull 
𝕜 s = convexHull 𝕜 (f '' s)
参数：f : E ->ₗ[𝕜] F；s : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLinearMap.image_convexHull`：IsLinearMap.image_convexHull {f : E -> F} 
(hf : IsLinearMap 𝕜 f) (s : Set E) : f '' convexHull 𝕜 s = convexHull 𝕜 (f '' s)
· 使用定理 `LinearMap.isLinear`：isLinear : IsLinearMap R fₗ
-/
theorem LinearMap.image_convexHull (f : E →ₗ[𝕜] F) (s : Set E) :
    f '' convexHull 𝕜 s = convexHull 𝕜 (f '' s) :=
  f.isLinear.image_convexHull s
/-
**convexHull_add_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convexHull_add_subset {s t : Set E} : convexHull 𝕜 (s + t) subseteq convex
Hull 𝕜 s + convexHull 𝕜 t
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `convexHull_min`：convexHull_min : s subseteq t -> Convex 𝕜 t -> convexHul
l 𝕜 s subseteq t
· 使用定理 `Set.add_subset_add`：∀ {α : Type u_2} [inst : Add α] {s₁ s₂ t₁ t₂ : Set α
}, s₁ ⊆ t₁ → s₂ ⊆ t₂ → s₁ + s₂ ⊆ t₁ + t₂
· 使用定理 `subset_convexHull`：subset_convexHull : s subseteq convexHull 𝕜 s
· 使用定理 `Convex.add`：Convex.add {t : Set E} (hs : Convex 𝕜 s) (ht : Convex 𝕜 t) :
 Convex 𝕜 (s + t)
· 使用定理 `convex_convexHull`：convex_convexHull : Convex 𝕜 (convexHull 𝕜 s)
-/
theorem convexHull_add_subset {s t : Set E} :
    convexHull 𝕜 (s + t) ⊆ convexHull 𝕜 s + convexHull 𝕜 t :=
  convexHull_min (add_subset_add (subset_convexHull _ _) (subset_convexHull _ _))
    (Convex.add (convex_convexHull 𝕜 s) (convex_convexHull 𝕜 t))

end AddCommMonoid

end OrderedSemiring

section CommSemiring

variable [CommSemiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [Module 𝕜 E]

/-
**convexHull_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convexHull_smul (a : 𝕜) (s : Set E) : convexHull 𝕜 (a • s) = a • convexHul
l 𝕜 s
参数：a : 𝕜；s : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.image_convexHull`：LinearMap.image_convexHull (f : E ->ₗ[𝕜] F) 
(s : Set E) : f '' convexHull 𝕜 s = convexHull 𝕜 (f '' s)
-/
theorem convexHull_smul (a : 𝕜) (s : Set E) : convexHull 𝕜 (a • s) = a • convexHull 𝕜 s :=
  (LinearMap.lsmul _ _ a).image_convexHull _ |>.symm

end CommSemiring

section OrderedRing

variable [Ring 𝕜] [PartialOrder 𝕜]

section AddCommGroup

variable [AddCommGroup E] [AddCommGroup F] [Module 𝕜 E] [Module 𝕜 F]

/-
**AffineMap.image_convexHull** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AffineMap.image_convexHull (f : E ->ᵃ[𝕜] F) (s : Set E) : f '' convexHull 
𝕜 s = convexHull 𝕜 (f '' s)
参数：f : E ->ᵃ[𝕜] F；s : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `convexHull_min`：convexHull_min : s subseteq t -> Convex 𝕜 t -> convexHul
l 𝕜 s subseteq t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `subset_convexHull`：subset_convexHull : s subseteq convexHull 𝕜 s
· 使用定理 `Convex.affine_preimage`：Convex.affine_preimage (f : E ->ᵃ[𝕜] F) {s : Set
 F} (hs : Convex 𝕜 s) : Convex 𝕜 (f ⁻¹' s)
· 使用定理 `convex_convexHull`：convex_convexHull : Convex 𝕜 (convexHull 𝕜 s)
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Convex.affine_image`：Convex.affine_image (f : E ->ᵃ[𝕜] F) (hs : Convex 𝕜
 s) : Convex 𝕜 (f '' s)
-/
theorem AffineMap.image_convexHull (f : E →ᵃ[𝕜] F) (s : Set E) :
    f '' convexHull 𝕜 s = convexHull 𝕜 (f '' s) := by
  apply Set.Subset.antisymm
  · rw [Set.image_subset_iff]
    refine convexHull_min ?_ ((convex_convexHull 𝕜 (f '' s)).affine_preimage f)
    rw [← Set.image_subset_iff]
    exact subset_convexHull 𝕜 (f '' s)
  · exact convexHull_min (Set.image_mono (subset_convexHull 𝕜 s))
      ((convex_convexHull 𝕜 s).affine_image f)
/-
**convexHull_subset_affineSpan** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convexHull_subset_affineSpan (s : Set E) : convexHull 𝕜 s subseteq (affine
Span 𝕜 s : Set E)
参数：s : Set E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `convexHull_min`：convexHull_min : s subseteq t -> Convex 𝕜 t -> convexHul
l 𝕜 s subseteq t
· 使用定理 `subset_affineSpan`：subset_affineSpan (s : Set P) : s subseteq affineSpan
 k s
· 使用定理 `AffineSubspace.convex`：AffineSubspace.convex (Q : AffineSubspace 𝕜 E) : 
Convex 𝕜 (Q : Set E)
-/
theorem convexHull_subset_affineSpan (s : Set E) : convexHull 𝕜 s ⊆ (affineSpan 𝕜 s : Set E) :=
  convexHull_min (subset_affineSpan 𝕜 s) (affineSpan 𝕜 s).convex

@[simp]
/-
**affineSpan_convexHull** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：affineSpan_convexHull (s : Set E) : affineSpan 𝕜 (convexHull 𝕜 s) = affine
Span 𝕜 s
参数：s : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `affineSpan_le`：∀ {k : Type u_1} {V : Type u_2} {P : Type u_3} [inst : Ri
ng k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [S : AddTorsor V 
P] …
· 使用定理 `convexHull_subset_affineSpan`：convexHull_subset_affineSpan (s : Set E) :
 convexHull 𝕜 s subseteq (affineSpan 𝕜 s : Set E)
· 使用定理 `affineSpan_mono`：affineSpan_mono {s₁ s₂ : Set P} (h : s₁ subseteq s₂) : 
affineSpan k s₁ <= affineSpan k s₂
· 使用定理 `subset_convexHull`：subset_convexHull : s subseteq convexHull 𝕜 s
-/
theorem affineSpan_convexHull (s : Set E) : affineSpan 𝕜 (convexHull 𝕜 s) = affineSpan 𝕜 s := by
  refine le_antisymm ?_ (affineSpan_mono 𝕜 (subset_convexHull 𝕜 s))
  rw [affineSpan_le]
  exact convexHull_subset_affineSpan s
/-
**convexHull_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：convexHull_neg (s : Set E) : convexHull 𝕜 (-s) = -convexHull 𝕜 s
参数：s : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineMap.image_convexHull`：AffineMap.image_convexHull (f : E ->ᵃ[𝕜] F) 
(s : Set E) : f '' convexHull 𝕜 s = convexHull 𝕜 (f '' s)
-/
theorem convexHull_neg (s : Set E) : convexHull 𝕜 (-s) = -convexHull 𝕜 s := by
  simp_rw [← image_neg_eq_neg]
  exact AffineMap.image_convexHull (-1) _ |>.symm
/-
**convexHull_vadd** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：convexHull_vadd (x : E) (s : Set E) : convexHull 𝕜 (x +ᵥ s) = x +ᵥ convexH
ull 𝕜 s
参数：x : E；s : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineMap.image_convexHull`：AffineMap.image_convexHull (f : E ->ᵃ[𝕜] F) 
(s : Set E) : f '' convexHull 𝕜 s = convexHull 𝕜 (f '' s)
-/
lemma convexHull_vadd (x : E) (s : Set E) : convexHull 𝕜 (x +ᵥ s) = x +ᵥ convexHull 𝕜 s :=
  (AffineEquiv.constVAdd 𝕜 _ x).toAffineMap.image_convexHull s |>.symm

end AddCommGroup

end OrderedRing

end convexHull

