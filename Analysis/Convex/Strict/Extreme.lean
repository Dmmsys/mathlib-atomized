/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Analysis.Convex.StrictConvexSpace

import Mathlib.Algebra.CharP.Invertible

/-! # Extreme points of (strictly convex) sets

This file collects some results of extreme points of (strictly convex) sets.

## Main results
* `disjoint_interior_extremePoints`: the interior and extreme points of a set in a
  nontrivial topological vector space are disjoint.
* `StrictConvex.sdiff_interior_subset_extremePoints`:
  when `C` is a strictly convex set then `C \ interior C ⊆ extremePoints 𝕜 C`.
* `StrictConvex.extremePoints_eq_sdiff_interior`: the extreme points of a strictly convex set `S`
  in nontrivial normed space is exactly `S \ interior S`.

Corollaries of the above is that, in a nontrivial normed space, the extreme points of the
closed ball is contained in the sphere (see `extremePoints_closedBall_subset_sphere`).
And in a nontrivial strictly convex space, the extreme points of the closed ball is exactly the
sphere (see `StrictConvexSpace.extremePoints_closedBall_eq_sphere`). -/

public section

open Set Metric

open Filter in
open scoped Topology in
/-
**disjoint_interior_extremePoints** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjoint_interior_extremePoints {E : Type*} [AddCommGroup E] [Module Real 
E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul Real E] [Nontr
ivial E] (S : Set E) : Disjoint (interior S) (extremePoints Real S)
参数：S : Set E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.disjoint_iff`：∀ {α : Type u} {s t : Set α}, Disjoint s t ↔ s ∩ t ⊆ ∅
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Filter.tendsto_inf_left`：tendsto_inf_left {f : α -> β} {x₁ x₂ : Filter α
} {y : Filter β} (h : Tendsto f x₁ y) : Tendsto f (x₁ ⊓ x₂) y
· 使用定理 `Continuous.tendsto'`：Continuous.tendsto' (hf : Continuous f) (x : X) (y 
: Y) (h : f x = y) : Tendsto f (𝓝 x) (𝓝 y)
· 使用定理 `continuous_sub_left`：∀ {G : Type w} [inst : TopologicalSpace G] [inst_1 
: Sub G] [ContinuousSub G] (a : G), Continuous fun x => a - x
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_interior_iff_mem_nhds`：mem_interior_iff_mem_nhds : x in interior s ↔
 s in 𝓝 x
· 使用定理 `continuous_const_add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst
_1 : Add M] [SeparatelyContinuousAdd M] (m : M),   Continuous fun x => m + x
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `eventually_mem_nhdsWithin`：eventually_mem_nhdsWithin {a : α} {s : Set α}
 : forallᶠ x in 𝓝[s] a, x in s
· 使用定理 `mem_openSegment_sub_add`：mem_openSegment_sub_add [Invertible (2 : 𝕜)] (x
 y : E) : x in openSegment 𝕜 (x - y) (x + y)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem disjoint_interior_extremePoints {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [Nontrivial E]
    (S : Set E) : Disjoint (interior S) (extremePoints ℝ S) := by
  refine Set.disjoint_iff.mpr fun x ⟨x_int, x_ext⟩ ↦ ?_
  rw [mem_interior_iff_mem_nhds] at x_int
  have h₁ : ∀ᶠ v in 𝓝[≠] 0, x - v ∈ S :=
    (tendsto_inf_left <| (continuous_sub_left _).tendsto' _ _ (sub_zero _)).eventually x_int
  have h₂ : ∀ᶠ v in 𝓝[≠] 0, x + v ∈ S :=
    (tendsto_inf_left <| (continuous_const_add _).tendsto' _ _ (add_zero _)).eventually x_int
  obtain ⟨v, ⟨hv₁, hv₂⟩, (v_ne : v ≠ 0)⟩ := h₁.and h₂ |>.and eventually_mem_nhdsWithin |>.exists
  have key : x ∈ openSegment ℝ (x - v) (x + v) := mem_openSegment_sub_add _ _
  grind only [x_ext.2 hv₁ hv₂ key]
/-
**StrictConvex.sdiff_interior_subset_extremePoints** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictConvex.sdiff_interior_subset_extremePoints {𝕜 A : Type*} [Semiring 𝕜
] [PartialOrder 𝕜] [AddCommMonoid A] [Module 𝕜 A] [TopologicalSpace A] {C : Set 
A} (hc : StrictConvex 𝕜 C) : C \ interior C subseteq extremePoints 𝕜 C
参数：hc : StrictConvex 𝕜 C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
-/
lemma StrictConvex.sdiff_interior_subset_extremePoints {𝕜 A : Type*} [Semiring 𝕜]
    [PartialOrder 𝕜] [AddCommMonoid A] [Module 𝕜 A] [TopologicalSpace A] {C : Set A}
    (hc : StrictConvex 𝕜 C) : C \ interior C ⊆ extremePoints 𝕜 C := by
  refine fun x hx ↦ ⟨hx.1, fun y hy z hz ⟨a, b, ha, hb, hab, hxab⟩ ↦ ?_⟩
  have hyz : y = z := by
    by_contra
    exact hx.2 <| hxab ▸ hc hy hz this ha hb hab
  rwa [← hyz, ← add_smul, hab, one_smul] at hxab

@[deprecated (since := "2026-06-03")]
alias StrictConvex.diff_interior_subset_extremePoints :=
  StrictConvex.sdiff_interior_subset_extremePoints

section Normed
variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]

/-- In a nontrivial normed space, the extreme points of the closed ball is contained in
the sphere. -/
/-
**extremePoints_closedBall_subset_sphere** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：extremePoints_closedBall_subset_sphere [Nontrivial A] {x : A} {r : Real} :
 extremePoints Real (closedBall x r) subseteq sphere x r
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Metric.closedBall_sdiff_ball`：closedBall_sdiff_ball : closedBall x ε \ b
all x ε = sphere x ε
· 使用引理 `Set.subset_sdiff`：subset_sdiff : s subseteq t \ u ↔ s subseteq t ∧ Disjo
int s u
· 使用定理 `interior_closedBall'`：interior_closedBall' (x : E) (r : Real) : interior
 (closedBall x r) = ball x r
· 使用定理 `extremePoints_subset`：extremePoints_subset : A.extremePoints 𝕜 subseteq 
A
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `disjoint_interior_extremePoints`：disjoint_interior_extremePoints {E : Ty
pe*} [AddCommGroup E] [Module Real E] [TopologicalSpace E] [IsTopologicalAddGrou
p E] [ContinuousSMul …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …

--- 原说明 ---
In a nontrivial normed space, the extreme points of the closed ball is contained
 in
the sphere.
-/
theorem extremePoints_closedBall_subset_sphere [Nontrivial A] {x : A} {r : ℝ} :
    extremePoints ℝ (closedBall x r) ⊆ sphere x r := by
  rw [← closedBall_sdiff_ball, subset_sdiff, ← interior_closedBall' _]
  exact ⟨extremePoints_subset, disjoint_interior_extremePoints _ |>.symm⟩
/-
**StrictConvex.extremePoints_eq_sdiff_interior** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConvex.extremePoints_eq_sdiff_interior [Nontrivial A] {S : Set A} (h
S : StrictConvex Real S) : extremePoints Real S = S \ interior S
参数：hS : StrictConvex Real S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `antisymm`：antisymm [Std.Antisymm r] : a ≺ b -> b ≺ a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.subset_sdiff`：subset_sdiff : s subseteq t \ u ↔ s subseteq t ∧ Disjo
int s u
· 使用定理 `extremePoints_subset`：extremePoints_subset : A.extremePoints 𝕜 subseteq 
A
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `disjoint_interior_extremePoints`：disjoint_interior_extremePoints {E : Ty
pe*} [AddCommGroup E] [Module Real E] [TopologicalSpace E] [IsTopologicalAddGrou
p E] [ContinuousSMul …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用引理 `StrictConvex.sdiff_interior_subset_extremePoints`：StrictConvex.sdiff_int
erior_subset_extremePoints {𝕜 A : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [AddCommM
onoid A] [Module 𝕜 A] [TopologicalSpac…
-/
theorem StrictConvex.extremePoints_eq_sdiff_interior [Nontrivial A] {S : Set A}
    (hS : StrictConvex ℝ S) : extremePoints ℝ S = S \ interior S :=
  antisymm (subset_sdiff.mpr ⟨extremePoints_subset, disjoint_interior_extremePoints _ |>.symm⟩)
    hS.sdiff_interior_subset_extremePoints

@[deprecated (since := "2026-06-03")]
alias StrictConvex.extremePoints_eq_diff_interior := StrictConvex.extremePoints_eq_sdiff_interior

/-- In a strictly convex space, the sphere is contained in the extreme points of the closed ball
when the radius is nonzero.
In a nontrivial space, they are equal, see `extremePoints_closedBall_eq_sphere`. -/
/-
**StrictConvexSpace.sphere_subset_extremePoints_closedBall** 是 Mathlib 中的一个引理，位于
命名空间 ``。
形式化陈述：StrictConvexSpace.sphere_subset_extremePoints_closedBall [StrictConvexSpac
e Real A] (a : A) {r : Real} (hr : r != 0) : sphere a r subseteq extremePoints R
eal (closedBall a r)
参数：a : A；hr : r != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StrictConvex.sdiff_interior_subset_extremePoints`：StrictConvex.sdiff_int
erior_subset_extremePoints {𝕜 A : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [AddCommM
onoid A] [Module 𝕜 A] [TopologicalSpac…
· 使用定理 `strictConvex_closedBall`：strictConvex_closedBall [StrictConvexSpace 𝕜 E]
 (x : E) (r : Real) : StrictConvex 𝕜 (closedBall x r)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Metric.closure_closedBall`：closure_closedBall : closure (closedBall x ε)
 = closedBall x ε
· 使用定理 `frontier.eq_1`：∀ {X : Type u} [inst : TopologicalSpace X] (s : Set X), f
rontier s = closure s \ interior s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `frontier_closedBall`：frontier_closedBall (x : E) {r : Real} (hr : r != 0
) : frontier (closedBall x r) = sphere x r

--- 原说明 ---
In a strictly convex space, the sphere is contained in the extreme points of the
 closed ball
when the radius is nonzero.
In a nontrivial space, they are equal, see `extremePoints_closedBall_eq_sphere`.
-/
lemma StrictConvexSpace.sphere_subset_extremePoints_closedBall [StrictConvexSpace ℝ A]
    (a : A) {r : ℝ} (hr : r ≠ 0) : sphere a r ⊆ extremePoints ℝ (closedBall a r) := fun _ hx ↦ by
  rw [← frontier_closedBall _ hr, frontier, closure_closedBall] at hx
  exact (_root_.strictConvex_closedBall ℝ _ _).sdiff_interior_subset_extremePoints hx
/-
**StrictConvexSpace.extremePoints_closedBall_eq_sphere** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：StrictConvexSpace.extremePoints_closedBall_eq_sphere [Nontrivial A] {x : A
} {r : Real} [StrictConvexSpace Real A] : extremePoints Real (closedBall x r) = 
sphere x r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StrictConvex.extremePoints_eq_sdiff_interior`：StrictConvex.extremePoints
_eq_sdiff_interior [Nontrivial A] {S : Set A} (hS : StrictConvex Real S) : extre
mePoints Real S = S \ interior S
· 使用定理 `strictConvex_closedBall`：strictConvex_closedBall [StrictConvexSpace 𝕜 E]
 (x : E) (r : Real) : StrictConvex 𝕜 (closedBall x r)
· 使用定理 `interior_closedBall'`：interior_closedBall' (x : E) (r : Real) : interior
 (closedBall x r) = ball x r
· 使用定理 `Metric.closedBall_sdiff_ball`：closedBall_sdiff_ball : closedBall x ε \ b
all x ε = sphere x ε
-/
theorem StrictConvexSpace.extremePoints_closedBall_eq_sphere [Nontrivial A] {x : A} {r : ℝ}
    [StrictConvexSpace ℝ A] : extremePoints ℝ (closedBall x r) = sphere x r := by
  rw [(_root_.strictConvex_closedBall ℝ x r).extremePoints_eq_sdiff_interior, interior_closedBall',
    closedBall_sdiff_ball]

end Normed

/-
**Set.extremePoints_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {a b : ℝ}, a ≤ b → Set.extremePoints ℝ (Set.Icc a b) = {a, b}
参数：Set.Icc a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.Icc_eq_closedBall`：Real.Icc_eq_closedBall (x y : Real) : Icc x y = 
closedBall ((x + y) / 2) ((y - x) / 2)
· 使用定理 `StrictConvexSpace.extremePoints_closedBall_eq_sphere`：StrictConvexSpace.
extremePoints_closedBall_eq_sphere [Nontrivial A] {x : A} {r : Real} [StrictConv
exSpace Real A] : extremePoints Real (clos…
-/
@[simp] lemma Set.extremePoints_Icc {a b : ℝ} (hab : a ≤ b) :
    extremePoints ℝ (Icc a b) = {a, b} := by
  rw [Real.Icc_eq_closedBall, StrictConvexSpace.extremePoints_closedBall_eq_sphere]
  grind [Real.sphere_eq_pair]
