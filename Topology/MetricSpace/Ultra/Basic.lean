/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.Clopen

/-!
## Ultrametric spaces

This file defines ultrametric spaces, implemented as a mixin on the `Dist`,
so that it can apply on pseudometric spaces as well.

## Main definitions

* `IsUltrametricDist X`: Annotates `dist : X → X → ℝ` as respecting the ultrametric inequality
  of `dist(x, z) ≤ max {dist(x,y), dist(y,z)}`

## Implementation details

The mixin could have been defined as a hypothesis to be carried around, instead of relying on
typeclass synthesis. However, since we declare a (pseudo)metric space on a type using
typeclass arguments, one can declare the ultrametricity at the same time.
For example, one could say `[Norm K] [Fact (IsNonarchimedean (norm : K → ℝ))]`,

The file imports a later file in the hierarchy of pseudometric spaces, since
`Metric.isClosed_closedBall` and `Metric.isClosed_sphere` is proven in a later file
using more conceptual results.

TODO: Generalize to ultrametric uniformities

## Tags

ultrametric, nonarchimedean
-/

public section

variable {X : Type*}

/-- The `dist : X → X → ℝ` respects the ultrametric inequality
of `dist(x, z) ≤ max (dist(x,y)) (dist(y,z))`. -/
/-
**IsUltrametricDist** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(X : Type u_2) → [Dist X] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `dist : X → X → ℝ` respects the ultrametric inequality
of `dist(x, z) ≤ max (dist(x,y)) (dist(y,z))`.
-/
class IsUltrametricDist (X : Type*) [Dist X] : Prop where
  dist_triangle_max : ∀ x y z : X, dist x z ≤ max (dist x y) (dist y z)

open Metric

variable [PseudoMetricSpace X] [IsUltrametricDist X] (x y z : X) (r s : ℝ)
/-
**dist_triangle_max** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：dist_triangle_max : dist x z <= max (dist x y) (dist y z)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUltrametricDist.dist_triangle_max`：∀ {X : Type u_2} {inst : Dist X} [s
elf : IsUltrametricDist X] (x y z : X), dist x z ≤ max (dist x y) (dist y z)
-/
lemma dist_triangle_max : dist x z ≤ max (dist x y) (dist y z) :=
  IsUltrametricDist.dist_triangle_max x y z

namespace IsUltrametricDist

/-- All triangles are isosceles in an ultrametric space. -/
/-
**IsUltrametricDist.dist_eq_max_of_dist_ne_dist** 是 Mathlib 中的一个引理，位于命名空间 `IsUlt
rametricDist`。
形式化陈述：dist_eq_max_of_dist_ne_dist (h : dist x y != dist y z) : dist x z = max (d
ist x y) (dist y z)
参数：h : dist x y != dist y z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `IsUltrametricDist.dist_triangle_max`：∀ {X : Type u_2} {inst : Dist X} [s
elf : IsUltrametricDist X] (x y z : X), dist x z ≤ max (dist x y) (dist y z)
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `max_eq_right`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b →
 max a b = b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_max_iff`：le_max_iff : a <= max b c ↔ a <= b ∨ a <= c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a

--- 原说明 ---
All triangles are isosceles in an ultrametric space.
-/
lemma dist_eq_max_of_dist_ne_dist (h : dist x y ≠ dist y z) :
    dist x z = max (dist x y) (dist y z) := by
  apply le_antisymm (dist_triangle_max x y z)
  rcases h.lt_or_gt with h | h
  · rw [max_eq_right h.le]
    apply (le_max_iff.mp <| dist_triangle_max y x z).resolve_left
    simpa only [not_le, dist_comm x y] using h
  · rw [max_eq_left h.le, dist_comm x y, dist_comm x z]
    apply (le_max_iff.mp <| dist_triangle_max y z x).resolve_left
    simpa only [not_le, dist_comm x y] using h
/-
**IsUltrametricDist.subtype** 是 Mathlib 中的一个实例，位于命名空间 `IsUltrametricDist`。
形式化陈述：subtype (p : X -> Prop) : IsUltrametricDist (Subtype p)
参数：p : X -> Prop。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUltrametricDist.dist_triangle_max`：∀ {X : Type u_2} {inst : Dist X} [s
elf : IsUltrametricDist X] (x y z : X), dist x z ≤ max (dist x y) (dist y z)
-/
instance subtype (p : X → Prop) : IsUltrametricDist (Subtype p) :=
  ⟨fun _ _ _ ↦ by simpa [Subtype.dist_eq] using dist_triangle_max _ _ _⟩
/-
**IsUltrametricDist.ball_eq_of_mem** 是 Mathlib 中的一个引理，位于命名空间 `IsUltrametricDist`
。
形式化陈述：ball_eq_of_mem {x y : X} {r : Real} (h : y in ball x r) : ball x r = ball 
y r
参数：h : y in ball x r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `IsUltrametricDist.dist_triangle_max`：∀ {X : Type u_2} {inst : Dist X} [s
elf : IsUltrametricDist X] (x y z : X), dist x z ≤ max (dist x y) (dist y z)
· 使用定理 `max_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, b < a → c <
 a → max b c < a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
-/
lemma ball_eq_of_mem {x y : X} {r : ℝ} (h : y ∈ ball x r) : ball x r = ball y r := by
  ext a
  simp_rw [mem_ball] at h ⊢
  constructor <;> intro h' <;>
  exact (dist_triangle_max _ _ _).trans_lt (max_lt h' (dist_comm x _ ▸ h))
/-
**IsUltrametricDist.ball_subset_trichotomy** 是 Mathlib 中的一个引理，位于命名空间 `IsUltramet
ricDist`。
形式化陈述：ball_subset_trichotomy : ball x r subseteq ball y s ∨ ball y s subseteq ba
ll x r ∨ Disjoint (ball x r) (ball y s)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_inter_iff`：mem_inter_iff (x : α) (a b : Set α) : x in a inter b 
↔ x in a ∧ x in b
· 使用定理 `Set.Nonempty.some_mem`：∀ {α : Type u} {s : Set α} (h : s.Nonempty), h.so
me ∈ s
· 使用定理 `Metric.ball_subset_ball`：ball_subset_ball (h : ε₁ <= ε₂) : ball x ε₁ sub
seteq ball x ε₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `IsUltrametricDist.ball_eq_of_mem`：ball_eq_of_mem {x y : X} {r : Real} (h
 : y in ball x r) : ball x r = ball y r
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
· 使用引理 `Set.disjoint_or_nonempty_inter`：disjoint_or_nonempty_inter (s t : Set α)
 : Disjoint s t ∨ (s inter t).Nonempty
· 使用定理 `disjoint_comm`：disjoint_comm : Disjoint a b ↔ Disjoint b a
· 使用定理 `or_assoc`：∀ {a b c : Prop}, (a ∨ b) ∨ c ↔ a ∨ b ∨ c
· 使用定理 `or_comm`：∀ {a b : Prop}, a ∨ b ↔ b ∨ a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma ball_subset_trichotomy :
    ball x r ⊆ ball y s ∨ ball y s ⊆ ball x r ∨ Disjoint (ball x r) (ball y s) := by
  wlog! hrs : r ≤ s generalizing x y r s
  · rw [disjoint_comm, ← or_assoc, or_comm (b := (_ : Set X) ⊆ _), or_assoc]
    exact this y x s r hrs.le
  · refine Set.disjoint_or_nonempty_inter (ball x r) (ball y s) |>.symm.imp (fun h ↦ ?_) (Or.inr ·)
    obtain ⟨hxz, hyz⟩ := (Set.mem_inter_iff _ _ _).mp h.some_mem
    have hx := ball_subset_ball hrs (x := x)
    rwa [ball_eq_of_mem hyz |>.trans (ball_eq_of_mem <| hx hxz).symm]
/-
**IsUltrametricDist.ball_eq_or_disjoint** 是 Mathlib 中的一个引理，位于命名空间 `IsUltrametric
Dist`。
形式化陈述：ball_eq_or_disjoint : ball x r = ball y r ∨ Disjoint (ball x r) (ball y r)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用引理 `IsUltrametricDist.ball_eq_of_mem`：ball_eq_of_mem {x y : X} {r : Real} (h
 : y in ball x r) : ball x r = ball y r
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.Nonempty.some_mem`：∀ {α : Type u} {s : Set α} (h : s.Nonempty), h.so
me ∈ s
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
· 使用引理 `Set.disjoint_or_nonempty_inter`：disjoint_or_nonempty_inter (s t : Set α)
 : Disjoint s t ∨ (s inter t).Nonempty
-/
lemma ball_eq_or_disjoint :
    ball x r = ball y r ∨ Disjoint (ball x r) (ball y r) := by
  refine Set.disjoint_or_nonempty_inter (ball x r) (ball y r) |>.symm.imp (fun h ↦ ?_) id
  have h₁ := ball_eq_of_mem <| Set.inter_subset_left h.some_mem
  have h₂ := ball_eq_of_mem <| Set.inter_subset_right h.some_mem
  exact h₁.trans h₂.symm
/-
**IsUltrametricDist.closedBall_eq_of_mem** 是 Mathlib 中的一个引理，位于命名空间 `IsUltrametri
cDist`。
形式化陈述：closedBall_eq_of_mem {x y : X} {r : Real} (h : y in closedBall x r) : clos
edBall x r = closedBall y r
参数：h : y in closedBall x r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `IsUltrametricDist.dist_triangle_max`：∀ {X : Type u_2} {inst : Dist X} [s
elf : IsUltrametricDist X] (x y z : X), dist x z ≤ max (dist x y) (dist y z)
· 使用定理 `max_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a ≤ c → b ≤
 c → max a b ≤ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
-/
lemma closedBall_eq_of_mem {x y : X} {r : ℝ} (h : y ∈ closedBall x r) :
    closedBall x r = closedBall y r := by
  ext
  simp_rw [mem_closedBall] at h ⊢
  constructor <;> intro h' <;>
  exact (dist_triangle_max _ _ _).trans (max_le h' (dist_comm x _ ▸ h))
/-
**IsUltrametricDist.closedBall_subset_trichotomy** 是 Mathlib 中的一个引理，位于命名空间 `IsUl
trametricDist`。
形式化陈述：closedBall_subset_trichotomy : closedBall x r subseteq closedBall y s ∨ cl
osedBall y s subseteq closedBall x r ∨ Disjoint (closedBall x r) (closedBall y s
)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_inter_iff`：mem_inter_iff (x : α) (a b : Set α) : x in a inter b 
↔ x in a ∧ x in b
· 使用定理 `Set.Nonempty.some_mem`：∀ {α : Type u} {s : Set α} (h : s.Nonempty), h.so
me ∈ s
· 使用定理 `Metric.closedBall_subset_closedBall`：closedBall_subset_closedBall (h : ε
₁ <= ε₂) : closedBall x ε₁ subseteq closedBall x ε₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `IsUltrametricDist.closedBall_eq_of_mem`：closedBall_eq_of_mem {x y : X} {
r : Real} (h : y in closedBall x r) : closedBall x r = closedBall y r
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
· 使用引理 `Set.disjoint_or_nonempty_inter`：disjoint_or_nonempty_inter (s t : Set α)
 : Disjoint s t ∨ (s inter t).Nonempty
· 使用定理 `disjoint_comm`：disjoint_comm : Disjoint a b ↔ Disjoint b a
· 使用定理 `or_assoc`：∀ {a b c : Prop}, (a ∨ b) ∨ c ↔ a ∨ b ∨ c
· 使用定理 `or_comm`：∀ {a b : Prop}, a ∨ b ↔ b ∨ a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma closedBall_subset_trichotomy :
    closedBall x r ⊆ closedBall y s ∨ closedBall y s ⊆ closedBall x r ∨
    Disjoint (closedBall x r) (closedBall y s) := by
  wlog! hrs : r ≤ s generalizing x y r s
  · rw [disjoint_comm, ← or_assoc, or_comm (b := (_ : Set X) ⊆ _), or_assoc]
    exact this y x s r hrs.le
  · refine Set.disjoint_or_nonempty_inter (closedBall x r) (closedBall y s) |>.symm.imp
      (fun h ↦ ?_) (Or.inr ·)
    obtain ⟨hxz, hyz⟩ := (Set.mem_inter_iff _ _ _).mp h.some_mem
    have hx := closedBall_subset_closedBall hrs (x := x)
    rwa [closedBall_eq_of_mem hyz |>.trans (closedBall_eq_of_mem <| hx hxz).symm]
/-
**IsUltrametricDist.isClosed_ball** 是 Mathlib 中的一个引理，位于命名空间 `IsUltrametricDist`。
形式化陈述：isClosed_ball (x : X) (r : Real) : IsClosed (ball x r)
参数：x : X；r : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.ball_eq_empty`：ball_eq_empty : ball x ε = ∅ ↔ ε <= 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isOpen_compl_iff`：∀ {X : Type u} {s : Set X} [inst : TopologicalSpace X]
, IsOpen sᶜ ↔ IsClosed s
· 使用定理 `Metric.isOpen_iff`：isOpen_iff : IsOpen s ↔ forall x in s, exists ε > 0, 
ball x ε subseteq s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `IsUltrametricDist.ball_eq_or_disjoint`：ball_eq_or_disjoint : ball x r = 
ball y r ∨ Disjoint (ball x r) (ball y r)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma isClosed_ball (x : X) (r : ℝ) : IsClosed (ball x r) := by
  cases le_or_gt r 0 with
  | inl hr =>
    simp [ball_eq_empty.mpr hr]
  | inr h =>
    rw [← isOpen_compl_iff, isOpen_iff]
    push _ ∈ _
    intro y hy
    cases ball_eq_or_disjoint x y r with
    | inl hd =>
      rw [hd] at hy
      simp [h.not_ge] at hy
    | inr hd =>
      use r
      simp [h, le_compl_iff_disjoint_left, hd]
/-
**IsUltrametricDist.isClopen_ball** 是 Mathlib 中的一个引理，位于命名空间 `IsUltrametricDist`。
形式化陈述：isClopen_ball : IsClopen (ball x r)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsUltrametricDist.isClosed_ball`：isClosed_ball (x : X) (r : Real) : IsCl
osed (ball x r)
· 使用定理 `Metric.isOpen_ball`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x : α} 
{ε : ℝ}, IsOpen (Metric.ball x ε)
-/
lemma isClopen_ball : IsClopen (ball x r) := ⟨isClosed_ball x r, isOpen_ball⟩
/-
**IsUltrametricDist.frontier_ball_eq_empty** 是 Mathlib 中的一个引理，位于命名空间 `IsUltramet
ricDist`。
形式化陈述：frontier_ball_eq_empty : frontier (ball x r) = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isClopen_iff_frontier_eq_empty`：isClopen_iff_frontier_eq_empty : IsClope
n s ↔ frontier s = ∅
· 使用引理 `IsUltrametricDist.isClopen_ball`：isClopen_ball : IsClopen (ball x r)
-/
lemma frontier_ball_eq_empty : frontier (ball x r) = ∅ :=
  isClopen_iff_frontier_eq_empty.mp (isClopen_ball x r)
/-
**IsUltrametricDist.closedBall_eq_or_disjoint** 是 Mathlib 中的一个引理，位于命名空间 `IsUltra
metricDist`。
形式化陈述：closedBall_eq_or_disjoint : closedBall x r = closedBall y r ∨ Disjoint (cl
osedBall x r) (closedBall y r)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用引理 `IsUltrametricDist.closedBall_eq_of_mem`：closedBall_eq_of_mem {x y : X} {
r : Real} (h : y in closedBall x r) : closedBall x r = closedBall y r
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.Nonempty.some_mem`：∀ {α : Type u} {s : Set α} (h : s.Nonempty), h.so
me ∈ s
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
· 使用引理 `Set.disjoint_or_nonempty_inter`：disjoint_or_nonempty_inter (s t : Set α)
 : Disjoint s t ∨ (s inter t).Nonempty
-/
lemma closedBall_eq_or_disjoint :
    closedBall x r = closedBall y r ∨ Disjoint (closedBall x r) (closedBall y r) := by
  refine Set.disjoint_or_nonempty_inter (closedBall x r) (closedBall y r) |>.symm.imp
    (fun h ↦ ?_) id
  have h₁ := closedBall_eq_of_mem <| Set.inter_subset_left h.some_mem
  have h₂ := closedBall_eq_of_mem <| Set.inter_subset_right h.some_mem
  exact h₁.trans h₂.symm
/-
**IsUltrametricDist.isOpen_closedBall** 是 Mathlib 中的一个引理，位于命名空间 `IsUltrametricDi
st`。
形式化陈述：isOpen_closedBall {r : Real} (hr : r != 0) : IsOpen (closedBall x r)
参数：hr : r != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_or_gt_of_ne`：lt_or_gt_of_ne (h : a != b) : a < b ∨ b < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.closedBall_eq_empty`：closedBall_eq_empty : closedBall x ε = ∅ ↔ ε
 < 0
· 使用定理 `Metric.isOpen_iff`：isOpen_iff : IsOpen s ↔ forall x in s, exists ε > 0, 
ball x ε subseteq s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `IsUltrametricDist.closedBall_eq_or_disjoint`：closedBall_eq_or_disjoint :
 closedBall x r = closedBall y r ∨ Disjoint (closedBall x r) (closedBall y r)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用引理 `IsUltrametricDist.closedBall_eq_of_mem`：closedBall_eq_of_mem {x y : X} {
r : Real} (h : y in closedBall x r) : closedBall x r = closedBall y r
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 < a
-/
lemma isOpen_closedBall {r : ℝ} (hr : r ≠ 0) : IsOpen (closedBall x r) := by
  cases lt_or_gt_of_ne hr with
  | inl h =>
    simp [closedBall_eq_empty.mpr h]
  | inr h =>
    rw [isOpen_iff]
    simp only [gt_iff_lt]
    intro y hy
    cases closedBall_eq_or_disjoint x y r with
    | inl hd =>
      use r
      simp [h, hd, ball_subset_closedBall]
    | inr hd =>
      simp [closedBall_eq_of_mem hy, h.not_gt] at hd
/-
**IsUltrametricDist.isClopen_closedBall** 是 Mathlib 中的一个引理，位于命名空间 `IsUltrametric
Dist`。
形式化陈述：isClopen_closedBall {r : Real} (hr : r != 0) : IsClopen (closedBall x r)
参数：hr : r != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Metric.isClosed_closedBall`：isClosed_closedBall : IsClosed (closedBall x
 ε)
· 使用引理 `IsUltrametricDist.isOpen_closedBall`：isOpen_closedBall {r : Real} (hr : 
r != 0) : IsOpen (closedBall x r)
-/
lemma isClopen_closedBall {r : ℝ} (hr : r ≠ 0) : IsClopen (closedBall x r) :=
  ⟨Metric.isClosed_closedBall, isOpen_closedBall x hr⟩
/-
**IsUltrametricDist.frontier_closedBall_eq_empty** 是 Mathlib 中的一个引理，位于命名空间 `IsUl
trametricDist`。
形式化陈述：frontier_closedBall_eq_empty {r : Real} (hr : r != 0) : frontier (closedBa
ll x r) = ∅
参数：hr : r != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isClopen_iff_frontier_eq_empty`：isClopen_iff_frontier_eq_empty : IsClope
n s ↔ frontier s = ∅
· 使用引理 `IsUltrametricDist.isClopen_closedBall`：isClopen_closedBall {r : Real} (h
r : r != 0) : IsClopen (closedBall x r)
-/
lemma frontier_closedBall_eq_empty {r : ℝ} (hr : r ≠ 0) : frontier (closedBall x r) = ∅ :=
  isClopen_iff_frontier_eq_empty.mp (isClopen_closedBall x hr)
/-
**IsUltrametricDist.isOpen_sphere** 是 Mathlib 中的一个引理，位于命名空间 `IsUltrametricDist`。
形式化陈述：isOpen_sphere {r : Real} (hr : r != 0) : IsOpen (sphere x r)
参数：hr : r != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Metric.closedBall_sdiff_ball`：closedBall_sdiff_ball : closedBall x ε \ b
all x ε = sphere x ε
· 使用定理 `sdiff_eq`：sdiff_eq : x \ y = x ⊓ yᶜ
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
· 使用引理 `IsUltrametricDist.isOpen_closedBall`：isOpen_closedBall {r : Real} (hr : 
r != 0) : IsOpen (closedBall x r)
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用引理 `IsUltrametricDist.isClosed_ball`：isClosed_ball (x : X) (r : Real) : IsCl
osed (ball x r)
-/
lemma isOpen_sphere {r : ℝ} (hr : r ≠ 0) : IsOpen (sphere x r) := by
  rw [← closedBall_sdiff_ball, sdiff_eq]
  exact (isOpen_closedBall x hr).inter (isClosed_ball x r).isOpen_compl
/-
**IsUltrametricDist.isClopen_sphere** 是 Mathlib 中的一个引理，位于命名空间 `IsUltrametricDist
`。
形式化陈述：isClopen_sphere {r : Real} (hr : r != 0) : IsClopen (sphere x r)
参数：hr : r != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Metric.isClosed_sphere`：isClosed_sphere : IsClosed (sphere x ε)
· 使用引理 `IsUltrametricDist.isOpen_sphere`：isOpen_sphere {r : Real} (hr : r != 0) 
: IsOpen (sphere x r)
-/
lemma isClopen_sphere {r : ℝ} (hr : r ≠ 0) : IsClopen (sphere x r) :=
  ⟨Metric.isClosed_sphere, isOpen_sphere x hr⟩

end IsUltrametricDist

