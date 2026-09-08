/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
module

public import Mathlib.Algebra.Order.Group.Pointwise.Interval
public import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-!
# Lemmas about distances between points in intervals in `ℝ`.
-/

public section

open Bornology Filter Metric Set
open scoped NNReal Topology

namespace Real

variable {ι : Type*}

/-
**Real.dist_left_le_of_mem_uIcc** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：dist_left_le_of_mem_uIcc {x y z : Real} (h : y in uIcc x z) : dist x y <= 
dist x z
参数：h : y in uIcc x z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `Set.abs_sub_left_of_mem_uIcc`：abs_sub_left_of_mem_uIcc (h : c in [[a, b]
]) : |c - a| <= |b - a|
-/
lemma dist_left_le_of_mem_uIcc {x y z : ℝ} (h : y ∈ uIcc x z) : dist x y ≤ dist x z := by
  simpa only [dist_comm x] using! abs_sub_left_of_mem_uIcc h
/-
**Real.dist_right_le_of_mem_uIcc** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：dist_right_le_of_mem_uIcc {x y z : Real} (h : y in uIcc x z) : dist y z <=
 dist x z
参数：h : y in uIcc x z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `Set.abs_sub_right_of_mem_uIcc`：abs_sub_right_of_mem_uIcc (h : c in [[a, 
b]]) : |b - c| <= |b - a|
-/
lemma dist_right_le_of_mem_uIcc {x y z : ℝ} (h : y ∈ uIcc x z) : dist y z ≤ dist x z := by
  simpa only [dist_comm _ z] using! abs_sub_right_of_mem_uIcc h
/-
**Real.dist_le_of_mem_uIcc** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：dist_le_of_mem_uIcc {x y x' y' : Real} (hx : x in uIcc x' y') (hy : y in u
Icc x' y') : dist x y <= dist x' y'
参数：hx : x in uIcc x' y'；hy : y in uIcc x' y'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.abs_sub_le_of_uIcc_subset_uIcc`：abs_sub_le_of_uIcc_subset_uIcc (h : 
[[c, d]] subseteq [[a, b]]) : |d - c| <= |b - a|
· 使用引理 `Set.uIcc_subset_uIcc`：uIcc_subset_uIcc (h₁ : a₁ in [[a₂, b₂]]) (h₂ : b₁ 
in [[a₂, b₂]]) : [[a₁, b₁]] subseteq [[a₂, b₂]]
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.uIcc_comm`：uIcc_comm (a b : α) : [[a, b]] = [[b, a]]
-/
lemma dist_le_of_mem_uIcc {x y x' y' : ℝ} (hx : x ∈ uIcc x' y') (hy : y ∈ uIcc x' y') :
    dist x y ≤ dist x' y' :=
  abs_sub_le_of_uIcc_subset_uIcc <| uIcc_subset_uIcc (by rwa [uIcc_comm]) (by rwa [uIcc_comm])
/-
**Real.dist_le_of_mem_Icc** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：dist_le_of_mem_Icc {x y x' y' : Real} (hx : x in Icc x' y') (hy : y in Icc
 x' y') : dist x y <= y' - x'
参数：hx : x in Icc x' y'；hy : y in Icc x' y'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `abs_of_nonpos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], a ≤ 0 → |a| = -a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_nonpos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, a - b ≤ 0 ↔ a ≤ b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用引理 `Real.dist_le_of_mem_uIcc`：dist_le_of_mem_uIcc {x y x' y' : Real} (hx : x
 in uIcc x' y') (hy : y in uIcc x' y') : dist x y <= dist x' y'
· 使用引理 `Set.Icc_subset_uIcc`：Icc_subset_uIcc : Icc a b subseteq [[a, b]]
-/
lemma dist_le_of_mem_Icc {x y x' y' : ℝ} (hx : x ∈ Icc x' y') (hy : y ∈ Icc x' y') :
    dist x y ≤ y' - x' := by
  simpa only [Real.dist_eq, abs_of_nonpos (sub_nonpos.2 <| hx.1.trans hx.2), neg_sub] using
    Real.dist_le_of_mem_uIcc (Icc_subset_uIcc hx) (Icc_subset_uIcc hy)
/-
**Real.dist_le_of_mem_Icc_01** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：dist_le_of_mem_Icc_01 {x y : Real} (hx : x in Icc (0 : Real) 1) (hy : y in
 Icc (0 : Real) 1) : dist x y <= 1
参数：hx : x in Icc (0 : Real) 1；hy : y in Icc (0 : Real) 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用引理 `Real.dist_le_of_mem_Icc`：dist_le_of_mem_Icc {x y x' y' : Real} (hx : x i
n Icc x' y') (hy : y in Icc x' y') : dist x y <= y' - x'
-/
lemma dist_le_of_mem_Icc_01 {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    dist x y ≤ 1 := by simpa only [sub_zero] using Real.dist_le_of_mem_Icc hx hy

variable [Fintype ι] {x y x' y' : ι → ℝ}
/-
**Real.dist_le_of_mem_pi_Icc** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：dist_le_of_mem_pi_Icc (hx : x in Icc x' y') (hy : y in Icc x' y') : dist x
 y <= dist x' y'
参数：hx : x in Icc x' y'；hy : y in Icc x' y'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `dist_pi_le_iff`：dist_pi_le_iff {f g : forall b, X b} {r : Real} (hr : 0 
<= r) : dist f g <= r ↔ forall b, dist (f b) (g b) <= r
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Real.dist_le_of_mem_uIcc`：dist_le_of_mem_uIcc {x y x' y' : Real} (hx : x
 in uIcc x' y') (hy : y in uIcc x' y') : dist x y <= dist x' y'
· 使用引理 `Set.Icc_subset_uIcc`：Icc_subset_uIcc : Icc a b subseteq [[a, b]]
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `dist_le_pi_dist`：dist_le_pi_dist (f g : forall b, X b) (b : β) : dist (f
 b) (g b) <= dist f g
-/
lemma dist_le_of_mem_pi_Icc (hx : x ∈ Icc x' y') (hy : y ∈ Icc x' y') : dist x y ≤ dist x' y' := by
  refine (dist_pi_le_iff dist_nonneg).2 fun b =>
    (Real.dist_le_of_mem_uIcc ?_ ?_).trans (dist_le_pi_dist x' y' b) <;> refine Icc_subset_uIcc ?_
  exacts [⟨hx.1 _, hx.2 _⟩, ⟨hy.1 _, hy.2 _⟩]

end Real

