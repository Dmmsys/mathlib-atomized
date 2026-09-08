/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
module

public import Mathlib.Topology.Order.Bornology
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.MetricSpace.Cauchy
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.EMetricSpace.Diam

/-!
## Boundedness in (pseudo)-metric spaces

This file contains one definition, and various results on boundedness in pseudo-metric spaces.
* `Metric.diam s` : The `iSup` of the distances of members of `s`.
  Defined in terms of `ediam`, for better handling of the case when it should be infinite.

* `isBounded_iff_subset_closedBall`: a non-empty set is bounded if and only if
  it is included in some closed ball
* describing the cobounded filter, relating to the cocompact filter
* `IsCompact.isBounded`: compact sets are bounded
* `TotallyBounded.isBounded`: totally bounded sets are bounded
* `isCompact_iff_isClosed_bounded`, the **Heine–Borel theorem**:
  in a proper space, a set is compact if and only if it is closed and bounded.
* `cobounded_eq_cocompact`: in a proper space, cobounded and compact sets are the same
  diameter of a subset, and its relation to boundedness

## Tags

metric, pseudometric space, bounded, diameter, Heine-Borel theorem
-/

@[expose] public section

assert_not_exists Module.Basis

open Set Filter Bornology
open scoped ENNReal Uniformity Topology Pointwise

universe u v w

variable {α : Type u} {β : Type v} {X ι : Type*}

section UniformSpace
variable [UniformSpace α] [Preorder α] [CompactIccSpace α]

/-
**totallyBounded_Icc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：totallyBounded_Icc (a b : α) : TotallyBounded (Icc a b)
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.totallyBounded`：∀ {α : Type u} [uniformSpace : UniformSpace α]
 {s : Set α}, IsCompact s → TotallyBounded s
· 使用定理 `CompactIccSpace.isCompact_Icc`：∀ {α : Type u_1} {inst : TopologicalSpace
 α} {inst_1 : Preorder α} [self : CompactIccSpace α] {a b : α},   IsCompact (Set
.Icc a b)
-/
lemma totallyBounded_Icc (a b : α) : TotallyBounded (Icc a b) :=
  isCompact_Icc.totallyBounded
/-
**totallyBounded_Ico** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：totallyBounded_Ico (a b : α) : TotallyBounded (Ico a b)
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TotallyBounded.subset`：TotallyBounded.subset {s₁ s₂ : Set α} (hs : s₁ su
bseteq s₂) (h : TotallyBounded s₂) : TotallyBounded s₁
· 使用定理 `Set.Ico_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ico b a ⊆ Set.Icc b a
· 使用引理 `totallyBounded_Icc`：totallyBounded_Icc (a b : α) : TotallyBounded (Icc a
 b)
-/
lemma totallyBounded_Ico (a b : α) : TotallyBounded (Ico a b) :=
  (totallyBounded_Icc a b).subset Ico_subset_Icc_self
/-
**totallyBounded_Ioc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：totallyBounded_Ioc (a b : α) : TotallyBounded (Ioc a b)
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TotallyBounded.subset`：TotallyBounded.subset {s₁ s₂ : Set α} (hs : s₁ su
bseteq s₂) (h : TotallyBounded s₂) : TotallyBounded s₁
· 使用定理 `Set.Ioc_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc a b ⊆ Set.Icc a b
· 使用引理 `totallyBounded_Icc`：totallyBounded_Icc (a b : α) : TotallyBounded (Icc a
 b)
-/
lemma totallyBounded_Ioc (a b : α) : TotallyBounded (Ioc a b) :=
  (totallyBounded_Icc a b).subset Ioc_subset_Icc_self
/-
**totallyBounded_Ioo** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：totallyBounded_Ioo (a b : α) : TotallyBounded (Ioo a b)
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TotallyBounded.subset`：TotallyBounded.subset {s₁ s₂ : Set α} (hs : s₁ su
bseteq s₂) (h : TotallyBounded s₂) : TotallyBounded s₁
· 使用定理 `Set.Ioo_subset_Icc_self`：Ioo_subset_Icc_self : Ioo a b subseteq Icc a b
· 使用引理 `totallyBounded_Icc`：totallyBounded_Icc (a b : α) : TotallyBounded (Icc a
 b)
-/
lemma totallyBounded_Ioo (a b : α) : TotallyBounded (Ioo a b) :=
  (totallyBounded_Icc a b).subset Ioo_subset_Icc_self

end UniformSpace

namespace Metric

section Bounded

variable {x : α} {s t : Set α} {r : ℝ}
variable [PseudoMetricSpace α]

/-- Closed balls are bounded -/
/-
**Metric.isBounded_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：isBounded_closedBall : IsBounded (closedBall x r)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.isBounded_iff`：isBounded_iff {s : Set α} : IsBounded s ↔ exists C
 : Real, forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> dist x y <= C
· 使用定理 `dist_triangle_right`：dist_triangle_right (x y z : α) : dist x y <= dist 
x z + dist y z
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…

--- 原说明 ---
Closed balls are bounded
-/
theorem isBounded_closedBall : IsBounded (closedBall x r) :=
  isBounded_iff.2 ⟨r + r, fun y hy z hz =>
    calc dist y z ≤ dist y x + dist z x := dist_triangle_right _ _ _
    _ ≤ r + r := add_le_add hy hz⟩

/-- Open balls are bounded -/
/-
**Metric.isBounded_ball** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：isBounded_ball : IsBounded (ball x r)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bornology.IsBounded.subset`：∀ {α : Type u_2} {x : Bornology α} {s t : Se
t α}, Bornology.IsBounded t → s ⊆ t → Bornology.IsBounded s
· 使用定理 `Metric.isBounded_closedBall`：isBounded_closedBall : IsBounded (closedBal
l x r)
· 使用定理 `Metric.ball_subset_closedBall`：ball_subset_closedBall : ball x ε subsete
q closedBall x ε

--- 原说明 ---
Open balls are bounded
-/
theorem isBounded_ball : IsBounded (ball x r) :=
  isBounded_closedBall.subset ball_subset_closedBall

/-- Every open set in a metric space is a countable union of bounded open sets. -/
/-
**Metric.eq_countable_union_of_isBounded_of_isOpen** 是 Mathlib 中的一个定理，位于命名空间 `Me
tric`。
形式化陈述：eq_countable_union_of_isBounded_of_isOpen {U : Set α} (hU : IsOpen U) : ex
ists f : Nat -> Set α, Monotone f ∧ ⋃ i, f i = U ∧ forall i, IsBounded (f i) ∧ I
sOpen (f i)
参数：hU : IsOpen U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `monotone_const`：monotone_const [Preorder α] [Preorder β] {c : β} : Monot
one fun _ : α => c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.iUnion_empty`：iUnion_empty : (⋃ _ : ι, ∅ : Set α) = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inter_subset_inter_right`：inter_subset_inter_right {s t : Set α} (u 
: Set α) (H : s subseteq t) : u inter s subseteq u inter t
· 使用定理 `Metric.ball_subset_ball`：ball_subset_ball (h : ε₁ <= ε₂) : ball x ε₁ sub
seteq ball x ε₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Metric.iUnion_ball_nat`：iUnion_ball_nat (x : α) : ⋃ n : Nat, ball x n = 
univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `Bornology.IsBounded.subset`：∀ {α : Type u_2} {x : Bornology α} {s t : Se
t α}, Bornology.IsBounded t → s ⊆ t → Bornology.IsBounded s
· 使用定理 `Metric.isBounded_ball`：isBounded_ball : IsBounded (ball x r)
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
· 使用定理 `Metric.isOpen_ball`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x : α} 
{ε : ℝ}, IsOpen (Metric.ball x ε)

--- 原说明 ---
Every open set in a metric space is a countable union of bounded open sets.
-/
theorem eq_countable_union_of_isBounded_of_isOpen {U : Set α} (hU : IsOpen U) :
    ∃ f : ℕ → Set α, Monotone f ∧ ⋃ i, f i = U ∧ ∀ i, IsBounded (f i) ∧ IsOpen (f i) := by
  obtain rfl | ⟨x, -⟩ := U.eq_empty_or_nonempty
  · exact ⟨fun i ↦ ∅, monotone_const, by simp_all⟩
  refine ⟨fun i ↦ U ∩ ball x i, fun i j hij ↦ ?_, ?_, fun i ↦ ⟨?_, hU.inter isOpen_ball⟩⟩
  · exact inter_subset_inter_right _ (ball_subset_ball (Nat.cast_le.2 hij))
  · simp [← inter_iUnion]
  · exact isBounded_ball.subset inter_subset_right

/-- Spheres are bounded -/
/-
**Metric.isBounded_sphere** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：isBounded_sphere : IsBounded (sphere x r)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bornology.IsBounded.subset`：∀ {α : Type u_2} {x : Bornology α} {s t : Se
t α}, Bornology.IsBounded t → s ⊆ t → Bornology.IsBounded s
· 使用定理 `Metric.isBounded_closedBall`：isBounded_closedBall : IsBounded (closedBal
l x r)
· 使用定理 `Metric.sphere_subset_closedBall`：sphere_subset_closedBall : sphere x ε s
ubseteq closedBall x ε

--- 原说明 ---
Spheres are bounded
-/
theorem isBounded_sphere : IsBounded (sphere x r) :=
  isBounded_closedBall.subset sphere_subset_closedBall

/-- Given a point, a bounded subset is included in some ball around this point -/
/-
**Metric.isBounded_iff_subset_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：isBounded_iff_subset_closedBall (c : α) : IsBounded s ↔ exists r, s subset
eq closedBall c r
参数：c : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.isBounded_iff`：isBounded_iff {s : Set α} : IsBounded s ↔ exists C
 : Real, forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> dist x y <= C
· 使用定理 `Bornology.IsBounded.insert`：∀ {α : Type u_2} {x : Bornology α} {s : Set 
α}, Bornology.IsBounded s → ∀ (x_1 : α), Bornology.IsBounded (insert x_1 s)
· 使用定理 `Bornology.IsBounded.subset`：∀ {α : Type u_2} {x : Bornology α} {s t : Se
t α}, Bornology.IsBounded t → s ⊆ t → Bornology.IsBounded s
· 使用定理 `Metric.isBounded_closedBall`：isBounded_closedBall : IsBounded (closedBal
l x r)

--- 原说明 ---
Given a point, a bounded subset is included in some ball around this point
-/
theorem isBounded_iff_subset_closedBall (c : α) : IsBounded s ↔ ∃ r, s ⊆ closedBall c r :=
  ⟨fun h ↦ (isBounded_iff.1 (h.insert c)).imp fun _r hr _x hx ↦ hr (.inr hx) (mem_insert _ _),
    fun ⟨_r, hr⟩ ↦ isBounded_closedBall.subset hr⟩
/-
**Metric._root_.Bornology.IsBounded.subset_closedBall** 是 Mathlib 中的一个定理，位于命名空间 
`Metric`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Bornology.IsBounded.subset_closedBall (h : IsBounded s) (c : α) :
    ∃ r, s ⊆ closedBall c r :=
  (isBounded_iff_subset_closedBall c).1 h
/-
**Metric._root_.Bornology.IsBounded.subset_ball_lt** 是 Mathlib 中的一个定理，位于命名空间 `Me
tric`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Bornology.IsBounded.subset_ball_lt (h : IsBounded s) (a : ℝ) (c : α) :
    ∃ r, a < r ∧ s ⊆ ball c r :=
  let ⟨r, hr⟩ := h.subset_closedBall c
  ⟨max r a + 1, (le_max_right _ _).trans_lt (lt_add_one _), hr.trans <| closedBall_subset_ball <|
    (le_max_left _ _).trans_lt (lt_add_one _)⟩
/-
**Metric._root_.Bornology.IsBounded.subset_ball** 是 Mathlib 中的一个定理，位于命名空间 `Metri
c`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Bornology.IsBounded.subset_ball (h : IsBounded s) (c : α) : ∃ r, s ⊆ ball c r :=
  (h.subset_ball_lt 0 c).imp fun _ ↦ And.right
/-
**Metric.isBounded_iff_subset_ball** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：isBounded_iff_subset_ball (c : α) : IsBounded s ↔ exists r, s subseteq bal
l c r
参数：c : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bornology.IsBounded.subset_ball`：∀ {α : Type u} {s : Set α} [inst : Pseu
doMetricSpace α], Bornology.IsBounded s → ∀ (c : α), ∃ r, s ⊆ Metric.ball c r
· 使用定理 `Bornology.IsBounded.subset`：∀ {α : Type u_2} {x : Bornology α} {s t : Se
t α}, Bornology.IsBounded t → s ⊆ t → Bornology.IsBounded s
· 使用定理 `Metric.isBounded_ball`：isBounded_ball : IsBounded (ball x r)
-/
theorem isBounded_iff_subset_ball (c : α) : IsBounded s ↔ ∃ r, s ⊆ ball c r :=
  ⟨(IsBounded.subset_ball · c), fun ⟨_r, hr⟩ ↦ isBounded_ball.subset hr⟩
/-
**Metric._root_.Bornology.IsBounded.subset_closedBall_lt** 是 Mathlib 中的一个定理，位于命名
空间 `Metric`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Bornology.IsBounded.subset_closedBall_lt (h : IsBounded s) (a : ℝ) (c : α) :
    ∃ r, a < r ∧ s ⊆ closedBall c r :=
  let ⟨r, har, hr⟩ := h.subset_ball_lt a c
  ⟨r, har, hr.trans ball_subset_closedBall⟩
/-
**Metric.isBounded_closure_of_isBounded** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：isBounded_closure_of_isBounded (h : IsBounded s) : IsBounded (closure s)
参数：h : IsBounded s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.isBounded_iff`：isBounded_iff {s : Set α} : IsBounded s ↔ exists C
 : Real, forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> dist x y <= C
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsClosed.closure_subset`：IsClosed.closure_subset (hs : IsClosed s) : clo
sure s subseteq s
· 使用定理 `isClosed_Iic`：isClosed_Iic : IsClosed (Iic a)
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `map_mem_closure₂`：map_mem_closure₂ {f : X -> Y -> Z} {x : X} {y : Y} {s 
: Set X} {t : Set Y} {u : Set Z} (hf : Continuous (uncurry f)) (hx : x in closur
e s) (…
· 使用引理 `continuous_dist`：continuous_dist : Continuous fun p : α × α => dist p.1 
p.2
-/
theorem isBounded_closure_of_isBounded (h : IsBounded s) : IsBounded (closure s) :=
  let ⟨C, h⟩ := isBounded_iff.1 h
  isBounded_iff.2 ⟨C, fun _a ha _b hb => isClosed_Iic.closure_subset <|
    map_mem_closure₂ continuous_dist ha hb h⟩
/-
**Metric._root_.Bornology.IsBounded.closure** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem _root_.Bornology.IsBounded.closure (h : IsBounded s) : IsBounded (closure s) :=
  isBounded_closure_of_isBounded h

@[simp]
/-
**Metric.isBounded_closure_iff** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：isBounded_closure_iff : IsBounded (closure s) ↔ IsBounded s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bornology.IsBounded.subset`：∀ {α : Type u_2} {x : Bornology α} {s t : Se
t α}, Bornology.IsBounded t → s ⊆ t → Bornology.IsBounded s
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Bornology.IsBounded.closure`：∀ {α : Type u} {s : Set α} [inst : PseudoMe
tricSpace α], Bornology.IsBounded s → Bornology.IsBounded (closure s)
-/
theorem isBounded_closure_iff : IsBounded (closure s) ↔ IsBounded s :=
  ⟨fun h => h.subset subset_closure, fun h => h.closure⟩
/-
**Metric.hasBasis_nhds_isOpen_isBounded** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：hasBasis_nhds_isOpen_isBounded (x : α) : (𝓝 x).HasBasis (fun a => x in a ∧
 IsOpen a ∧ Bornology.IsBounded a) id
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.HasBasis.restrict`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α}
 {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ {q : ι → Prop}, (∀ (i : ι)
, p i → ∃ j, p…
· 使用定理 `nhds_basis_opens`：nhds_basis_opens (x : X) : (𝓝 x).HasBasis (fun s : Set
 X => x in s ∧ IsOpen s) fun s => s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Bornology.IsBounded.subset`：∀ {α : Type u_2} {x : Bornology α} {s t : Se
t α}, Bornology.IsBounded t → s ⊆ t → Bornology.IsBounded s
· 使用定理 `Metric.isBounded_ball`：isBounded_ball : IsBounded (ball x r)
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
-/
theorem hasBasis_nhds_isOpen_isBounded (x : α) :
    (𝓝 x).HasBasis (fun a ↦ x ∈ a ∧ IsOpen a ∧ Bornology.IsBounded a) id := by
  simp_rw [← and_assoc]
  apply (nhds_basis_opens x).restrict fun s hs ↦ ?_
  exact ⟨s ∩ Metric.ball x 1,
    by aesop (add safe apply IsOpen.inter),
    by simpa using Metric.isBounded_ball.subset Set.inter_subset_right⟩
/-
**Metric.hasBasis_cobounded_compl_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：hasBasis_cobounded_compl_closedBall (c : α) : (cobounded α).HasBasis (fun 
_ => True) (fun r => (closedBall c r)ᶜ)
参数：c : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `compl_surjective`：compl_surjective : Function.Surjective (compl : α -> α
)
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Metric.isBounded_iff_subset_closedBall`：isBounded_iff_subset_closedBall 
(c : α) : IsBounded s ↔ exists r, s subseteq closedBall c r
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem hasBasis_cobounded_compl_closedBall (c : α) :
    (cobounded α).HasBasis (fun _ ↦ True) (fun r ↦ (closedBall c r)ᶜ) :=
  ⟨compl_surjective.forall.2 fun _ ↦ (isBounded_iff_subset_closedBall c).trans <| by simp⟩
/-
**Metric.hasAntitoneBasis_cobounded_compl_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `
Metric`。
形式化陈述：hasAntitoneBasis_cobounded_compl_closedBall (c : α) : (cobounded α).HasAnt
itoneBasis (fun r => (closedBall c r)ᶜ)
参数：c : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.hasBasis_cobounded_compl_closedBall`：hasBasis_cobounded_compl_clo
sedBall (c : α) : (cobounded α).HasBasis (fun _ => True) (fun r => (closedBall c
 r)ᶜ)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
-/
theorem hasAntitoneBasis_cobounded_compl_closedBall (c : α) :
    (cobounded α).HasAntitoneBasis (fun r ↦ (closedBall c r)ᶜ) :=
  ⟨Metric.hasBasis_cobounded_compl_closedBall _, fun _ _ hr _ ↦ by simpa using hr.trans_lt⟩
/-
**Metric.hasBasis_cobounded_compl_ball** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：hasBasis_cobounded_compl_ball (c : α) : (cobounded α).HasBasis (fun _ => T
rue) (fun r => (ball c r)ᶜ)
参数：c : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `compl_surjective`：compl_surjective : Function.Surjective (compl : α -> α
)
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Metric.isBounded_iff_subset_ball`：isBounded_iff_subset_ball (c : α) : Is
Bounded s ↔ exists r, s subseteq ball c r
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem hasBasis_cobounded_compl_ball (c : α) :
    (cobounded α).HasBasis (fun _ ↦ True) (fun r ↦ (ball c r)ᶜ) :=
  ⟨compl_surjective.forall.2 fun _ ↦ (isBounded_iff_subset_ball c).trans <| by simp⟩
/-
**Metric.hasAntitoneBasis_cobounded_compl_ball** 是 Mathlib 中的一个定理，位于命名空间 `Metric
`。
形式化陈述：hasAntitoneBasis_cobounded_compl_ball (c : α) : (cobounded α).HasAntitoneB
asis (fun r => (ball c r)ᶜ)
参数：c : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.hasBasis_cobounded_compl_ball`：hasBasis_cobounded_compl_ball (c :
 α) : (cobounded α).HasBasis (fun _ => True) (fun r => (ball c r)ᶜ)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem hasAntitoneBasis_cobounded_compl_ball (c : α) :
    (cobounded α).HasAntitoneBasis (fun r ↦ (ball c r)ᶜ) :=
  ⟨Metric.hasBasis_cobounded_compl_ball _, fun _ _ hr _ ↦ by simpa using hr.trans⟩

@[simp]
/-
**Metric.comap_dist_right_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：comap_dist_right_atTop (c : α) : comap (dist · c) atTop = cobounded α
参数：c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.eq_of_same_basis`：∀ {α : Type u_1} {ι : Sort u_4} {l l' 
: Filter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → l'.HasBasis p s →
 l = l'
· 使用定理 `Filter.HasBasis.comap`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l
 : Filter α} {p : ι → Prop} {s : ι → Set α} (f : β → α),   l.HasBasis p s → (Fil
ter.comap f…
· 使用定理 `Filter.atTop_basis`：atTop_basis [Nonempty α] : (@atTop α _).HasBasis (fu
n _ => True) Ici
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Metric.hasBasis_cobounded_compl_ball`：hasBasis_cobounded_compl_ball (c :
 α) : (cobounded α).HasBasis (fun _ => True) (fun r => (ball c r)ᶜ)
-/
theorem comap_dist_right_atTop (c : α) : comap (dist · c) atTop = cobounded α :=
  (atTop_basis.comap _).eq_of_same_basis <| by
    simpa only [compl_def, mem_ball, not_lt] using! hasBasis_cobounded_compl_ball c

@[simp]
/-
**Metric.comap_dist_left_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：comap_dist_left_atTop (c : α) : comap (dist c) atTop = cobounded α
参数：c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `Metric.comap_dist_right_atTop`：comap_dist_right_atTop (c : α) : comap (d
ist · c) atTop = cobounded α
-/
theorem comap_dist_left_atTop (c : α) : comap (dist c) atTop = cobounded α := by
  simpa only [dist_comm _ c] using comap_dist_right_atTop c

@[simp]
/-
**Metric.tendsto_dist_right_atTop_iff** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：tendsto_dist_right_atTop_iff (c : α) {f : β -> α} {l : Filter β} : Tendsto
 (fun x => dist (f x) c) l atTop ↔ Tendsto f l (cobounded α)
参数：c : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Metric.comap_dist_right_atTop`：comap_dist_right_atTop (c : α) : comap (d
ist · c) atTop = cobounded α
· 使用定理 `Filter.tendsto_comap_iff`：tendsto_comap_iff {f : α -> β} {g : β -> γ} {a
 : Filter α} {c : Filter γ} : Tendsto f a (c.comap g) ↔ Tendsto (g ∘ f) a c
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem tendsto_dist_right_atTop_iff (c : α) {f : β → α} {l : Filter β} :
    Tendsto (fun x ↦ dist (f x) c) l atTop ↔ Tendsto f l (cobounded α) := by
  rw [← comap_dist_right_atTop c, tendsto_comap_iff, Function.comp_def]

@[simp]
/-
**Metric.tendsto_dist_left_atTop_iff** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：tendsto_dist_left_atTop_iff (c : α) {f : β -> α} {l : Filter β} : Tendsto 
(fun x => dist c (f x)) l atTop ↔ Tendsto f l (cobounded α)
参数：c : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem tendsto_dist_left_atTop_iff (c : α) {f : β → α} {l : Filter β} :
    Tendsto (fun x ↦ dist c (f x)) l atTop ↔ Tendsto f l (cobounded α) := by
  simp only [dist_comm c, tendsto_dist_right_atTop_iff]
/-
**Metric.tendsto_dist_right_cobounded_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：tendsto_dist_right_cobounded_atTop (c : α) : Tendsto (dist · c) (cobounded
 α) atTop
参数：c : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_iff_comap`：tendsto_iff_comap {f : α -> β} {l₁ : Filter α}
 {l₂ : Filter β} : Tendsto f l₁ l₂ ↔ l₁ <= l₂.comap f
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Metric.comap_dist_right_atTop`：comap_dist_right_atTop (c : α) : comap (d
ist · c) atTop = cobounded α
-/
theorem tendsto_dist_right_cobounded_atTop (c : α) : Tendsto (dist · c) (cobounded α) atTop :=
  tendsto_iff_comap.2 (comap_dist_right_atTop c).ge
/-
**Metric.tendsto_dist_left_cobounded_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：tendsto_dist_left_cobounded_atTop (c : α) : Tendsto (dist c) (cobounded α)
 atTop
参数：c : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_iff_comap`：tendsto_iff_comap {f : α -> β} {l₁ : Filter α}
 {l₂ : Filter β} : Tendsto f l₁ l₂ ↔ l₁ <= l₂.comap f
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Metric.comap_dist_left_atTop`：comap_dist_left_atTop (c : α) : comap (dis
t c) atTop = cobounded α
-/
theorem tendsto_dist_left_cobounded_atTop (c : α) : Tendsto (dist c) (cobounded α) atTop :=
  tendsto_iff_comap.2 (comap_dist_left_atTop c).ge

/-- A totally bounded set is bounded -/
/-
**Metric._root_.TotallyBounded.isBounded** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A totally bounded set is bounded
-/
theorem _root_.TotallyBounded.isBounded {s : Set α} (h : TotallyBounded s) : IsBounded s :=
  -- We cover the totally bounded set by finitely many balls of radius 1,
  -- and then argue that a finite union of bounded sets is bounded
  let ⟨_t, fint, subs⟩ := (totallyBounded_iff.mp h) 1 zero_lt_one
  ((isBounded_biUnion fint).2 fun _ _ => isBounded_ball).subset subs

/-- A compact set is bounded -/
@[aesop 50% apply, grind ←]
/-
**Metric._root_.IsCompact.isBounded** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A compact set is bounded
-/
theorem _root_.IsCompact.isBounded {s : Set α} (h : IsCompact s) : IsBounded s :=
  -- A compact set is totally bounded, thus bounded
  h.totallyBounded.isBounded
/-
**Metric.** 是 Mathlib 中的一个实例，位于命名空间 `Metric`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) [CompactSpace α] : BoundedSpace α := ⟨isCompact_univ.isBounded⟩
/-
**Metric.cobounded_le_cocompact** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：cobounded_le_cocompact : cobounded α <= cocompact α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.HasBasis.ge_iff`：∀ {α : Type u_1} {ι' : Sort u_5} {l l' : Filter 
α} {p' : ι' → Prop} {s' : ι' → Set α},   l'.HasBasis p' s' → (l ≤ l' ↔ ∀ (i' : ι
'), p' i' → …
· 使用定理 `Filter.hasBasis_cocompact`：hasBasis_cocompact : (cocompact X).HasBasis I
sCompact compl
· 使用定理 `IsCompact.isBounded`：∀ {α : Type u} [inst : PseudoMetricSpace α] {s : Se
t α}, IsCompact s → Bornology.IsBounded s
-/
theorem cobounded_le_cocompact : cobounded α ≤ cocompact α :=
  hasBasis_cocompact.ge_iff.2 fun _s hs ↦ hs.isBounded
/-
**Metric.isCobounded_iff_closedBall_compl_subset** 是 Mathlib 中的一个定理，位于命名空间 `Metr
ic`。
形式化陈述：isCobounded_iff_closedBall_compl_subset {s : Set α} (c : α) : IsCobounded 
s ↔ exists (r : Real), (Metric.closedBall c r)ᶜ subseteq s
参数：c : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Bornology.isBounded_compl_iff`：isBounded_compl_iff : IsBounded sᶜ ↔ IsCo
bounded s
· 使用定理 `Metric.isBounded_iff_subset_closedBall`：isBounded_iff_subset_closedBall 
(c : α) : IsBounded s ↔ exists r, s subseteq closedBall c r
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `Set.compl_subset_comm`：compl_subset_comm : sᶜ subseteq t ↔ tᶜ subseteq s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isCobounded_iff_closedBall_compl_subset {s : Set α} (c : α) :
    IsCobounded s ↔ ∃ (r : ℝ), (Metric.closedBall c r)ᶜ ⊆ s := by
  rw [← isBounded_compl_iff, isBounded_iff_subset_closedBall c]
  apply exists_congr
  intro r
  rw [compl_subset_comm]
/-
**Metric._root_.Bornology.IsCobounded.closedBall_compl_subset** 是 Mathlib 中的一个定理
，位于命名空间 `Metric`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Bornology.IsCobounded.closedBall_compl_subset {s : Set α} (hs : IsCobounded s)
    (c : α) : ∃ (r : ℝ), (Metric.closedBall c r)ᶜ ⊆ s :=
  (isCobounded_iff_closedBall_compl_subset c).mp hs
/-
**Metric.closedBall_compl_subset_of_mem_cocompact** 是 Mathlib 中的一个定理，位于命名空间 `Met
ric`。
形式化陈述：closedBall_compl_subset_of_mem_cocompact {s : Set α} (hs : s in cocompact 
α) (c : α) : exists (r : Real), (Metric.closedBall c r)ᶜ subseteq s
参数：hs : s in cocompact α；c : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bornology.IsCobounded.closedBall_compl_subset`：∀ {α : Type u} [inst : Ps
eudoMetricSpace α] {s : Set α},   Bornology.IsCobounded s → ∀ (c : α), ∃ r, (Met
ric.closedBall c r)ᶜ ⊆ s
· 使用定理 `Metric.cobounded_le_cocompact`：cobounded_le_cocompact : cobounded α <= c
ocompact α
-/
theorem closedBall_compl_subset_of_mem_cocompact {s : Set α} (hs : s ∈ cocompact α) (c : α) :
    ∃ (r : ℝ), (Metric.closedBall c r)ᶜ ⊆ s :=
  IsCobounded.closedBall_compl_subset (cobounded_le_cocompact hs) c
/-
**Metric.mem_cocompact_of_closedBall_compl_subset** 是 Mathlib 中的一个定理，位于命名空间 `Met
ric`。
形式化陈述：mem_cocompact_of_closedBall_compl_subset [ProperSpace α] (c : α) (h : exis
ts r, (closedBall c r)ᶜ subseteq s) : s in cocompact α
参数：c : α；h : exists r, (closedBall c r)ᶜ subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.mem_cocompact`：mem_cocompact : s in cocompact X ↔ exists t, IsCom
pact t ∧ tᶜ subseteq s
· 使用定理 `ProperSpace.isCompact_closedBall`：∀ {α : Type u} {inst : PseudoMetricSpa
ce α} [self : ProperSpace α] (x : α) (r : ℝ), IsCompact (Metric.closedBall x r)
-/
theorem mem_cocompact_of_closedBall_compl_subset [ProperSpace α] (c : α)
    (h : ∃ r, (closedBall c r)ᶜ ⊆ s) : s ∈ cocompact α := by
  rcases h with ⟨r, h⟩
  rw [Filter.mem_cocompact]
  exact ⟨closedBall c r, isCompact_closedBall c r, h⟩
/-
**Metric.mem_cocompact_iff_closedBall_compl_subset** 是 Mathlib 中的一个定理，位于命名空间 `Me
tric`。
形式化陈述：mem_cocompact_iff_closedBall_compl_subset [ProperSpace α] (c : α) : s in c
ocompact α ↔ exists r, (closedBall c r)ᶜ subseteq s
参数：c : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.closedBall_compl_subset_of_mem_cocompact`：closedBall_compl_subset
_of_mem_cocompact {s : Set α} (hs : s in cocompact α) (c : α) : exists (r : Real
), (Metric.closedBall c r)ᶜ subseteq …
· 使用定理 `Metric.mem_cocompact_of_closedBall_compl_subset`：mem_cocompact_of_closed
Ball_compl_subset [ProperSpace α] (c : α) (h : exists r, (closedBall c r)ᶜ subse
teq s) : s in cocompact α
-/
theorem mem_cocompact_iff_closedBall_compl_subset [ProperSpace α] (c : α) :
    s ∈ cocompact α ↔ ∃ r, (closedBall c r)ᶜ ⊆ s :=
  ⟨(closedBall_compl_subset_of_mem_cocompact · _), mem_cocompact_of_closedBall_compl_subset _⟩

/-- Characterization of the boundedness of the range of a function -/
/-
**Metric.isBounded_range_iff** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：isBounded_range_iff {f : β -> α} : IsBounded (range f) ↔ exists C, forall 
x y, dist (f x) (f y) <= C
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Metric.isBounded_iff`：isBounded_iff {s : Set α} : IsBounded s ↔ exists C
 : Real, forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> dist x y <= C
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Characterization of the boundedness of the range of a function
-/
theorem isBounded_range_iff {f : β → α} : IsBounded (range f) ↔ ∃ C, ∀ x y, dist (f x) (f y) ≤ C :=
  isBounded_iff.trans <| by simp only [forall_mem_range]
/-
**Metric.isBounded_image_iff** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：isBounded_image_iff {f : β -> α} {s : Set β} : IsBounded (f '' s) ↔ exists
 C, forall x in s, forall y in s, dist (f x) (f y) <= C
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Metric.isBounded_iff`：isBounded_iff {s : Set α} : IsBounded s ↔ exists C
 : Real, forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> dist x y <= C
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isBounded_image_iff {f : β → α} {s : Set β} :
    IsBounded (f '' s) ↔ ∃ C, ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) ≤ C :=
  isBounded_iff.trans <| by simp only [forall_mem_image]
/-
**Metric.isBounded_range_of_tendsto_cofinite_uniformity** 是 Mathlib 中的一个定理，位于命名空
间 `Metric`。
形式化陈述：isBounded_range_of_tendsto_cofinite_uniformity {f : β -> α} (hf : Tendsto 
(Prod.map f f) (.cofinite ×ˢ .cofinite) (𝓤 α)) : IsBounded (range f)
参数：hf : Tendsto (Prod.map f f) (.cofinite ×ˢ .cofinite) (𝓤 α)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.tendsto_iff`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u
_4} {ι' : Sort u_5} {la : Filter α} {pa : ι → Prop} {sa : ι → Set α}   {lb : Fil
ter β} {pb : ι' →…
· 使用定理 `Filter.HasBasis.prod_self`：∀ {α : Type u_1} {ι : Sort u_4} {la : Filter 
α} {pa : ι → Prop} {sa : ι → Set α},   la.HasBasis pa sa → (la ×ˢ la).HasBasis p
a fun i => sa i…
· 使用定理 `Filter.hasBasis_cofinite`：hasBasis_cofinite : HasBasis cofinite (fun s :
 Set α => s.Finite) compl
· 使用定理 `Metric.uniformity_basis_dist`：uniformity_basis_dist : (𝓤 α).HasBasis (fu
n ε : Real => 0 < ε) fun ε => { p : α × α | dist p.1 p.2 < ε }
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_union_image_compl_eq_range`：image_union_image_compl_eq_range (
f : α -> β) : f '' s union f '' sᶜ = range f
· 使用定理 `Bornology.IsBounded.union`：∀ {α : Type u_2} {x : Bornology α} {s t : Set
 α},   Bornology.IsBounded s → Bornology.IsBounded t → Bornology.IsBounded (s ∪ 
t)
· 使用定理 `Set.Finite.isBounded`：Set.Finite.isBounded [Bornology α] {s : Set α} (hs
 : s.Finite) : IsBounded s
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.isBounded_image_iff`：isBounded_image_iff {f : β -> α} {s : Set β}
 : IsBounded (f '' s) ↔ exists C, forall x in s, forall y in s, dist (f x) (f y)
 <= C
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem isBounded_range_of_tendsto_cofinite_uniformity {f : β → α}
    (hf : Tendsto (Prod.map f f) (.cofinite ×ˢ .cofinite) (𝓤 α)) : IsBounded (range f) := by
  rcases (hasBasis_cofinite.prod_self.tendsto_iff uniformity_basis_dist).1 hf 1 zero_lt_one with
    ⟨s, hsf, hs1⟩
  rw [← image_union_image_compl_eq_range]
  refine (hsf.image f).isBounded.union (isBounded_image_iff.2 ⟨1, fun x hx y hy ↦ ?_⟩)
  exact le_of_lt (hs1 (x, y) ⟨hx, hy⟩)
/-
**Metric.isBounded_range_of_cauchy_map_cofinite** 是 Mathlib 中的一个定理，位于命名空间 `Metri
c`。
形式化陈述：isBounded_range_of_cauchy_map_cofinite {f : β -> α} (hf : Cauchy (map f co
finite)) : IsBounded (range f)
参数：hf : Cauchy (map f cofinite)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.isBounded_range_of_tendsto_cofinite_uniformity`：isBounded_range_o
f_tendsto_cofinite_uniformity {f : β -> α} (hf : Tendsto (Prod.map f f) (.cofini
te ×ˢ .cofinite) (𝓤 α)) : IsBounded (range …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `cauchy_map_iff`：cauchy_map_iff {l : Filter β} {f : β -> α} : Cauchy (l.m
ap f) ↔ NeBot l ∧ Tendsto (fun p : β × β => (f p.1, f p.2)) (l ×ˢ l) (𝓤 α)
-/
theorem isBounded_range_of_cauchy_map_cofinite {f : β → α} (hf : Cauchy (map f cofinite)) :
    IsBounded (range f) :=
  isBounded_range_of_tendsto_cofinite_uniformity <| (cauchy_map_iff.1 hf).2
/-
**Metric._root_.CauchySeq.isBounded_range** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.CauchySeq.isBounded_range {f : ℕ → α} (hf : CauchySeq f) : IsBounded (range f) :=
  isBounded_range_of_cauchy_map_cofinite <| by rwa [Nat.cofinite_eq_atTop]
/-
**Metric.isBounded_range_of_tendsto_cofinite** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：isBounded_range_of_tendsto_cofinite {f : β -> α} {a : α} (hf : Tendsto f c
ofinite (𝓝 a)) : IsBounded (range f)
参数：hf : Tendsto f cofinite (𝓝 a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.isBounded_range_of_tendsto_cofinite_uniformity`：isBounded_range_o
f_tendsto_cofinite_uniformity {f : β -> α} (hf : Tendsto (Prod.map f f) (.cofini
te ×ˢ .cofinite) (𝓤 α)) : IsBounded (range …
· 使用定理 `Filter.Tendsto.mono_right`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
x : Filter α} {y z : Filter β},   Filter.Tendsto f x y → y ≤ z → Filter.Tendsto 
f x z
· 使用定理 `Filter.Tendsto.prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {
δ : Type u_6} {f : α → γ} {g : β → δ} {a : Filter α} {b : Filter β}   {c : Filte
r γ} {d : Fi…
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
· 使用定理 `nhds_le_uniformity`：nhds_le_uniformity (x : α) : 𝓝 (x, x) <= 𝓤 α
-/
theorem isBounded_range_of_tendsto_cofinite {f : β → α} {a : α} (hf : Tendsto f cofinite (𝓝 a)) :
    IsBounded (range f) :=
  isBounded_range_of_tendsto_cofinite_uniformity <|
    (hf.prodMap hf).mono_right <| nhds_prod_eq.symm.trans_le (nhds_le_uniformity a)

/-- In a compact space, all sets are bounded -/
/-
**Metric.isBounded_of_compactSpace** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：isBounded_of_compactSpace [CompactSpace α] : IsBounded s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bornology.IsBounded.subset`：∀ {α : Type u_2} {x : Bornology α} {s t : Se
t α}, Bornology.IsBounded t → s ⊆ t → Bornology.IsBounded s
· 使用定理 `IsCompact.isBounded`：∀ {α : Type u} [inst : PseudoMetricSpace α] {s : Se
t α}, IsCompact s → Bornology.IsBounded s
· 使用定理 `isCompact_univ`：isCompact_univ [h : CompactSpace X] : IsCompact (univ : 
Set X)
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ

--- 原说明 ---
In a compact space, all sets are bounded
-/
theorem isBounded_of_compactSpace [CompactSpace α] : IsBounded s :=
  isCompact_univ.isBounded.subset (subset_univ _)
/-
**Metric.isBounded_range_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：isBounded_range_of_tendsto (u : Nat -> α) {x : α} (hu : Tendsto u atTop (𝓝
 x)) : IsBounded (range u)
参数：u : Nat -> α；hu : Tendsto u atTop (𝓝 x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CauchySeq.isBounded_range`：∀ {α : Type u} [inst : PseudoMetricSpace α] {
f : ℕ → α}, CauchySeq f → Bornology.IsBounded (Set.range f)
· 使用定理 `Filter.Tendsto.cauchySeq`：Filter.Tendsto.cauchySeq [SemilatticeSup β] [N
onempty β] {f : β -> α} {x} (hx : Tendsto f atTop (𝓝 x)) : CauchySeq f
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem isBounded_range_of_tendsto (u : ℕ → α) {x : α} (hu : Tendsto u atTop (𝓝 x)) :
    IsBounded (range u) :=
  hu.cauchySeq.isBounded_range
/-
**Metric.disjoint_nhds_cobounded** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：disjoint_nhds_cobounded (x : α) : Disjoint (𝓝 x) (cobounded α)
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.disjoint_of_disjoint_of_mem`：disjoint_of_disjoint_of_mem {f g : F
ilter α} {s t : Set α} (h : Disjoint s t) (hs : s in f) (ht : t in g) : Disjoint
 f g
· 使用定理 `disjoint_compl_right`：disjoint_compl_right : Disjoint a aᶜ
· 使用定理 `Metric.ball_mem_nhds`：ball_mem_nhds (x : α) {ε : Real} (ε0 : 0 < ε) : ba
ll x ε in 𝓝 x
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Metric.isBounded_ball`：isBounded_ball : IsBounded (ball x r)
-/
theorem disjoint_nhds_cobounded (x : α) : Disjoint (𝓝 x) (cobounded α) :=
  disjoint_of_disjoint_of_mem disjoint_compl_right (ball_mem_nhds _ one_pos) isBounded_ball
/-
**Metric.disjoint_cobounded_nhds** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：disjoint_cobounded_nhds (x : α) : Disjoint (cobounded α) (𝓝 x)
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `Metric.disjoint_nhds_cobounded`：disjoint_nhds_cobounded (x : α) : Disjoi
nt (𝓝 x) (cobounded α)
-/
theorem disjoint_cobounded_nhds (x : α) : Disjoint (cobounded α) (𝓝 x) :=
  (disjoint_nhds_cobounded x).symm
/-
**Metric.disjoint_nhdsSet_cobounded** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：disjoint_nhdsSet_cobounded {s : Set α} (hs : IsCompact s) : Disjoint (𝓝ˢ s
) (cobounded α)
参数：hs : IsCompact s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsCompact.disjoint_nhdsSet_left`：IsCompact.disjoint_nhdsSet_left {l : Fi
lter X} (hs : IsCompact s) : Disjoint (𝓝ˢ s) l ↔ forall x in s, Disjoint (𝓝 x) l
· 使用定理 `Metric.disjoint_nhds_cobounded`：disjoint_nhds_cobounded (x : α) : Disjoi
nt (𝓝 x) (cobounded α)
-/
theorem disjoint_nhdsSet_cobounded {s : Set α} (hs : IsCompact s) : Disjoint (𝓝ˢ s) (cobounded α) :=
  hs.disjoint_nhdsSet_left.2 fun _ _ ↦ disjoint_nhds_cobounded _
/-
**Metric.disjoint_cobounded_nhdsSet** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：disjoint_cobounded_nhdsSet {s : Set α} (hs : IsCompact s) : Disjoint (cobo
unded α) (𝓝ˢ s)
参数：hs : IsCompact s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `Metric.disjoint_nhdsSet_cobounded`：disjoint_nhdsSet_cobounded {s : Set α
} (hs : IsCompact s) : Disjoint (𝓝ˢ s) (cobounded α)
-/
theorem disjoint_cobounded_nhdsSet {s : Set α} (hs : IsCompact s) : Disjoint (cobounded α) (𝓝ˢ s) :=
  (disjoint_nhdsSet_cobounded hs).symm
/-
**Metric.exists_isBounded_image_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：exists_isBounded_image_of_tendsto {α β : Type*} [PseudoMetricSpace β] {l :
 Filter α} {f : α -> β} {x : β} (hf : Tendsto f l (𝓝 x)) : exists s in l, IsBoun
ded (f '' s)
参数：hf : Tendsto f l (𝓝 x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.disjoint_iff_left`：∀ {α : Type u_1} {ι : Sort u_4} {l l'
 : Filter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → (Disjoint l l' ↔
 ∃ i, p i ∧ (s i)ᶜ ∈ l'…
· 使用定理 `Filter.HasBasis.map`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l :
 Filter α} {p : ι → Prop} {s : ι → Set α} (f : α → β),   l.HasBasis p s → (Filte
r.map f l…
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
· 使用定理 `Disjoint.mono_left`：Disjoint.mono_left (h : a <= b) : Disjoint b c -> Di
sjoint a c
· 使用定理 `Metric.disjoint_nhds_cobounded`：disjoint_nhds_cobounded (x : α) : Disjoi
nt (𝓝 x) (cobounded α)
-/
theorem exists_isBounded_image_of_tendsto {α β : Type*} [PseudoMetricSpace β]
    {l : Filter α} {f : α → β} {x : β} (hf : Tendsto f l (𝓝 x)) :
    ∃ s ∈ l, IsBounded (f '' s) :=
  (l.basis_sets.map f).disjoint_iff_left.mp <| (disjoint_nhds_cobounded x).mono_left hf

/-- If a function is continuous within a set `s` at every point of a compact set `k`, then it is
bounded on some open neighborhood of `k` in `s`. -/
/-
**Metric.exists_isOpen_isBounded_image_inter_of_isCompact_of_forall_continuousWi
thinAt** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：exists_isOpen_isBounded_image_inter_of_isCompact_of_forall_continuousWithi
nAt [TopologicalSpace β] {k s : Set β} {f : β -> α} (hk : IsCompact k) (hf : for
all x in k, ContinuousWithinAt f s x) : exists t, k subseteq t ∧ IsOpen t ∧ IsBo
unded (f '' (t inter s))
参数：hk : IsCompact k；hf : forall x in k, ContinuousWithinAt f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `disjoint_assoc`：disjoint_assoc : Disjoint (a ⊓ b) c ↔ Disjoint a (b ⊓ c)
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `IsCompact.disjoint_nhdsSet_left`：IsCompact.disjoint_nhdsSet_left {l : Fi
lter X} (hs : IsCompact s) : Disjoint (𝓝ˢ s) l ↔ forall x in s, Disjoint (𝓝 x) l
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `disjoint_left_comm`：disjoint_left_comm : Disjoint a (b ⊓ c) ↔ Disjoint b
 (a ⊓ c)
· 使用定理 `Filter.Tendsto.disjoint`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {la
₁ la₂ : Filter α} {lb₁ lb₂ : Filter β},   Filter.Tendsto f la₁ lb₁ → Disjoint lb
₁ lb₂ → Filte…
· 使用定理 `Filter.tendsto_comap`：tendsto_comap {f : α -> β} {x : Filter β} : Tendst
o f (comap f x) x
· 使用定理 `Metric.disjoint_cobounded_nhds`：disjoint_cobounded_nhds (x : α) : Disjoi
nt (cobounded α) (𝓝 x)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.disjoint_iff`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort
 u_5} {l l' : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : 
ι' → Set α},   l.H…
· 使用定理 `Filter.HasBasis.inf_principal`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filt
er α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ (s' : Set α), (l ⊓ Fi
lter.principal s').…
· 使用定理 `hasBasis_nhdsSet`：hasBasis_nhdsSet (s : Set X) : (𝓝ˢ s).HasBasis (fun U 
=> IsOpen U ∧ s subseteq U) fun U => U
· 使用定理 `Filter.HasBasis.comap`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l
 : Filter α} {p : ι → Prop} {s : ι → Set α} (f : β → α),   l.HasBasis p s → (Fil
ter.comap f…
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
· 使用定理 `Bornology.IsBounded.subset`：∀ {α : Type u_2} {x : Bornology α} {s t : Se
t α}, Bornology.IsBounded t → s ⊆ t → Bornology.IsBounded s
· 使用定理 `Bornology.isBounded_compl_iff`：isBounded_compl_iff : IsBounded sᶜ ↔ IsCo
bounded s
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `Set.preimage_compl`：preimage_compl {s : Set β} : f ⁻¹' sᶜ = (f ⁻¹' s)ᶜ
· 使用引理 `Set.subset_compl_iff_disjoint_right`：subset_compl_iff_disjoint_right : s
 subseteq tᶜ ↔ Disjoint s t

--- 原说明 ---
If a function is continuous within a set `s` at every point of a compact set `k`
, then it is
bounded on some open neighborhood of `k` in `s`.
-/
theorem exists_isOpen_isBounded_image_inter_of_isCompact_of_forall_continuousWithinAt
    [TopologicalSpace β] {k s : Set β} {f : β → α} (hk : IsCompact k)
    (hf : ∀ x ∈ k, ContinuousWithinAt f s x) :
    ∃ t, k ⊆ t ∧ IsOpen t ∧ IsBounded (f '' (t ∩ s)) := by
  have : Disjoint (𝓝ˢ k ⊓ 𝓟 s) (comap f (cobounded α)) := by
    rw [disjoint_assoc, inf_comm, hk.disjoint_nhdsSet_left]
    exact fun x hx ↦ disjoint_left_comm.2 <|
      tendsto_comap.disjoint (disjoint_cobounded_nhds _) (hf x hx)
  rcases ((((hasBasis_nhdsSet _).inf_principal _)).disjoint_iff ((basis_sets _).comap _)).1 this
    with ⟨U, ⟨hUo, hkU⟩, t, ht, hd⟩
  refine ⟨U, hkU, hUo, (isBounded_compl_iff.2 ht).subset ?_⟩
  rwa [image_subset_iff, preimage_compl, subset_compl_iff_disjoint_right]

/-- If a function is continuous at every point of a compact set `k`, then it is bounded on
some open neighborhood of `k`. -/
/-
**Metric.exists_isOpen_isBounded_image_of_isCompact_of_forall_continuousAt** 是 M
athlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：exists_isOpen_isBounded_image_of_isCompact_of_forall_continuousAt [Topolog
icalSpace β] {k : Set β} {f : β -> α} (hk : IsCompact k) (hf : forall x in k, Co
ntinuousAt f x) : exists t, k subseteq t ∧ IsOpen t ∧ IsBounded (f '' t)
参数：hk : IsCompact k；hf : forall x in k, ContinuousAt f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `Metric.exists_isOpen_isBounded_image_inter_of_isCompact_of_forall_contin
uousWithinAt`：exists_isOpen_isBounded_image_inter_of_isCompact_of_forall_continu
ousWithinAt [TopologicalSpace β] {k s : Set β} {f : β -> α} (hk : IsCompac…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)

--- 原说明 ---
If a function is continuous at every point of a compact set `k`, then it is boun
ded on
some open neighborhood of `k`.
-/
theorem exists_isOpen_isBounded_image_of_isCompact_of_forall_continuousAt [TopologicalSpace β]
    {k : Set β} {f : β → α} (hk : IsCompact k) (hf : ∀ x ∈ k, ContinuousAt f x) :
    ∃ t, k ⊆ t ∧ IsOpen t ∧ IsBounded (f '' t) := by
  simp_rw [← continuousWithinAt_univ] at hf
  simpa only [inter_univ] using
    exists_isOpen_isBounded_image_inter_of_isCompact_of_forall_continuousWithinAt hk hf

/-- If a function is continuous on a set `s` containing a compact set `k`, then it is bounded on
some open neighborhood of `k` in `s`. -/
/-
**Metric.exists_isOpen_isBounded_image_inter_of_isCompact_of_continuousOn** 是 Ma
thlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：exists_isOpen_isBounded_image_inter_of_isCompact_of_continuousOn [Topologi
calSpace β] {k s : Set β} {f : β -> α} (hk : IsCompact k) (hks : k subseteq s) (
hf : ContinuousOn f s) : exists t, k subseteq t ∧ IsOpen t ∧ IsBounded (f '' (t 
inter s))
参数：hk : IsCompact k；hks : k subseteq s；hf : ContinuousOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.exists_isOpen_isBounded_image_inter_of_isCompact_of_forall_contin
uousWithinAt`：exists_isOpen_isBounded_image_inter_of_isCompact_of_forall_continu
ousWithinAt [TopologicalSpace β] {k s : Set β} {f : β -> α} (hk : IsCompac…

--- 原说明 ---
If a function is continuous on a set `s` containing a compact set `k`, then it i
s bounded on
some open neighborhood of `k` in `s`.
-/
theorem exists_isOpen_isBounded_image_inter_of_isCompact_of_continuousOn [TopologicalSpace β]
    {k s : Set β} {f : β → α} (hk : IsCompact k) (hks : k ⊆ s) (hf : ContinuousOn f s) :
    ∃ t, k ⊆ t ∧ IsOpen t ∧ IsBounded (f '' (t ∩ s)) :=
  exists_isOpen_isBounded_image_inter_of_isCompact_of_forall_continuousWithinAt hk fun x hx =>
    hf x (hks hx)

/-- If a function is continuous on a neighborhood of a compact set `k`, then it is bounded on
some open neighborhood of `k`. -/
/-
**Metric.exists_isOpen_isBounded_image_of_isCompact_of_continuousOn** 是 Mathlib 
中的一个定理，位于命名空间 `Metric`。
形式化陈述：exists_isOpen_isBounded_image_of_isCompact_of_continuousOn [TopologicalSpa
ce β] {k s : Set β} {f : β -> α} (hk : IsCompact k) (hs : IsOpen s) (hks : k sub
seteq s) (hf : ContinuousOn f s) : exists t, k subseteq t ∧ IsOpen t ∧ IsBounded
 (f '' t)
参数：hk : IsCompact k；hs : IsOpen s；hks : k subseteq s；hf : ContinuousOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.exists_isOpen_isBounded_image_of_isCompact_of_forall_continuousAt
`：exists_isOpen_isBounded_image_of_isCompact_of_forall_continuousAt [Topological
Space β] {k : Set β} {f : β -> α} (hk : IsCompact k) (hf : for…
· 使用定理 `ContinuousOn.continuousAt`：ContinuousOn.continuousAt (h : ContinuousOn f
 s) (hx : s in 𝓝 x) : ContinuousAt f x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x

--- 原说明 ---
If a function is continuous on a neighborhood of a compact set `k`, then it is b
ounded on
some open neighborhood of `k`.
-/
theorem exists_isOpen_isBounded_image_of_isCompact_of_continuousOn [TopologicalSpace β]
    {k s : Set β} {f : β → α} (hk : IsCompact k) (hs : IsOpen s) (hks : k ⊆ s)
    (hf : ContinuousOn f s) : ∃ t, k ⊆ t ∧ IsOpen t ∧ IsBounded (f '' t) :=
  exists_isOpen_isBounded_image_of_isCompact_of_forall_continuousAt hk fun _x hx =>
    hf.continuousAt (hs.mem_nhds (hks hx))

/-- The **Heine–Borel theorem**: In a proper space, a closed bounded set is compact. -/
/-
**Metric.isCompact_of_isClosed_isBounded** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：isCompact_of_isClosed_isBounded [ProperSpace α] (hc : IsClosed s) (hb : Is
Bounded s) : IsCompact s
参数：hc : IsClosed s；hb : IsBounded s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `isCompact_empty`：isCompact_empty : IsCompact (∅ : Set X)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Bornology.IsBounded.subset_closedBall`：∀ {α : Type u} {s : Set α} [inst 
: PseudoMetricSpace α],   Bornology.IsBounded s → ∀ (c : α), ∃ r, s ⊆ Metric.clo
sedBall c r
· 使用定理 `IsCompact.of_isClosed_subset`：IsCompact.of_isClosed_subset (hs : IsCompa
ct s) (ht : IsClosed t) (h : t subseteq s) : IsCompact t
· 使用定理 `ProperSpace.isCompact_closedBall`：∀ {α : Type u} {inst : PseudoMetricSpa
ce α} [self : ProperSpace α] (x : α) (r : ℝ), IsCompact (Metric.closedBall x r)

--- 原说明 ---
The **Heine–Borel theorem**: In a proper space, a closed bounded set is compact.
-/
theorem isCompact_of_isClosed_isBounded [ProperSpace α] (hc : IsClosed s) (hb : IsBounded s) :
    IsCompact s := by
  rcases eq_empty_or_nonempty s with (rfl | ⟨x, -⟩)
  · exact isCompact_empty
  · rcases hb.subset_closedBall x with ⟨r, hr⟩
    exact (isCompact_closedBall x r).of_isClosed_subset hc hr

/-- The **Heine–Borel theorem**: In a proper space, the closure of a bounded set is compact. -/
/-
**Metric._root_.Bornology.IsBounded.isCompact_closure** 是 Mathlib 中的一个定理，位于命名空间 
`Metric`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The **Heine–Borel theorem**: In a proper space, the closure of a bounded set is 
compact.
-/
theorem _root_.Bornology.IsBounded.isCompact_closure [ProperSpace α] (h : IsBounded s) :
    IsCompact (closure s) :=
  isCompact_of_isClosed_isBounded isClosed_closure h.closure

/-- The **Heine–Borel theorem**:
In a proper metric space, a set is compact if and only if it is closed and bounded. -/
@[wikidata Q253214]
/-
**Metric.isCompact_iff_isClosed_bounded** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：isCompact_iff_isClosed_bounded {α : Type*} {s : Set α} [MetricSpace α] [Pr
operSpace α] : IsCompact s ↔ IsClosed s ∧ IsBounded s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.isClosed`：IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsC
ompact s) : IsClosed s
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.toMetrizableSpace`：∀ {X : Type u_
2} [inst : TopologicalSpace X] [T0Space X] [h : TopologicalSpace.PseudoMetrizabl
eSpace X],   TopologicalSpace.MetrizableSpace …
· 使用定理 `MetricSpace.instT0Space`：∀ {γ : Type w} [inst : MetricSpace γ], T0Space 
γ
· 使用定理 `UniformSpace.pseudoMetrizableSpace`：∀ {X : Type u_5} [u : UniformSpace X
] [hu : (uniformity X).IsCountablyGenerated],   TopologicalSpace.PseudoMetrizabl
eSpace X
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `IsCompact.isBounded`：∀ {α : Type u} [inst : PseudoMetricSpace α] {s : Se
t α}, IsCompact s → Bornology.IsBounded s
· 使用定理 `Metric.isCompact_of_isClosed_isBounded`：isCompact_of_isClosed_isBounded 
[ProperSpace α] (hc : IsClosed s) (hb : IsBounded s) : IsCompact s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
The **Heine–Borel theorem**:
In a proper metric space, a set is compact if and only if it is closed and bound
ed.
-/
theorem isCompact_iff_isClosed_bounded {α : Type*} {s : Set α} [MetricSpace α] [ProperSpace α] :
    IsCompact s ↔ IsClosed s ∧ IsBounded s :=
  ⟨fun h => ⟨h.isClosed, h.isBounded⟩, fun h => isCompact_of_isClosed_isBounded h.1 h.2⟩
/-
**Metric.compactSpace_iff_isBounded_univ** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：compactSpace_iff_isBounded_univ [ProperSpace α] : CompactSpace α ↔ IsBound
ed (univ : Set α)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.isBounded_of_compactSpace`：isBounded_of_compactSpace [CompactSpac
e α] : IsBounded s
· 使用定理 `Metric.isCompact_of_isClosed_isBounded`：isCompact_of_isClosed_isBounded 
[ProperSpace α] (hc : IsClosed s) (hb : IsBounded s) : IsCompact s
· 使用定理 `isClosed_univ`：isClosed_univ : IsClosed (univ : Set X)
-/
theorem compactSpace_iff_isBounded_univ [ProperSpace α] :
    CompactSpace α ↔ IsBounded (univ : Set α) :=
  ⟨@isBounded_of_compactSpace α _ _, fun hb => ⟨isCompact_of_isClosed_isBounded isClosed_univ hb⟩⟩

section CompactIccSpace

variable [Preorder α] [CompactIccSpace α]

/-
**Metric.isBounded_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：isBounded_Icc (a b : α) : IsBounded (Icc a b)
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TotallyBounded.isBounded`：∀ {α : Type u} [inst : PseudoMetricSpace α] {s
 : Set α}, TotallyBounded s → Bornology.IsBounded s
· 使用引理 `totallyBounded_Icc`：totallyBounded_Icc (a b : α) : TotallyBounded (Icc a
 b)
-/
theorem isBounded_Icc (a b : α) : IsBounded (Icc a b) :=
  (totallyBounded_Icc a b).isBounded
/-
**Metric.isBounded_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：isBounded_Ico (a b : α) : IsBounded (Ico a b)
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TotallyBounded.isBounded`：∀ {α : Type u} [inst : PseudoMetricSpace α] {s
 : Set α}, TotallyBounded s → Bornology.IsBounded s
· 使用引理 `totallyBounded_Ico`：totallyBounded_Ico (a b : α) : TotallyBounded (Ico a
 b)
-/
theorem isBounded_Ico (a b : α) : IsBounded (Ico a b) :=
  (totallyBounded_Ico a b).isBounded
/-
**Metric.isBounded_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：isBounded_Ioc (a b : α) : IsBounded (Ioc a b)
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TotallyBounded.isBounded`：∀ {α : Type u} [inst : PseudoMetricSpace α] {s
 : Set α}, TotallyBounded s → Bornology.IsBounded s
· 使用引理 `totallyBounded_Ioc`：totallyBounded_Ioc (a b : α) : TotallyBounded (Ioc a
 b)
-/
theorem isBounded_Ioc (a b : α) : IsBounded (Ioc a b) :=
  (totallyBounded_Ioc a b).isBounded
/-
**Metric.isBounded_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：isBounded_Ioo (a b : α) : IsBounded (Ioo a b)
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TotallyBounded.isBounded`：∀ {α : Type u} [inst : PseudoMetricSpace α] {s
 : Set α}, TotallyBounded s → Bornology.IsBounded s
· 使用引理 `totallyBounded_Ioo`：totallyBounded_Ioo (a b : α) : TotallyBounded (Ioo a
 b)
-/
theorem isBounded_Ioo (a b : α) : IsBounded (Ioo a b) :=
  (totallyBounded_Ioo a b).isBounded

/-- In a pseudometric space with a conditionally complete linear order such that the order and the
metric structure give the same topology, any order-bounded set is metric-bounded. -/
/-
**Metric.isBounded_of_bddAbove_of_bddBelow** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：isBounded_of_bddAbove_of_bddBelow {s : Set α} (h₁ : BddAbove s) (h₂ : BddB
elow s) : IsBounded s
参数：h₁ : BddAbove s；h₂ : BddBelow s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bornology.IsBounded.subset`：∀ {α : Type u_2} {x : Bornology α} {s t : Se
t α}, Bornology.IsBounded t → s ⊆ t → Bornology.IsBounded s
· 使用定理 `Metric.isBounded_Icc`：isBounded_Icc (a b : α) : IsBounded (Icc a b)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
cc a b ↔ a ≤ x ∧ x ≤ b

--- 原说明 ---
In a pseudometric space with a conditionally complete linear order such that the
 order and the
metric structure give the same topology, any order-bounded set is metric-bounded
.
-/
theorem isBounded_of_bddAbove_of_bddBelow {s : Set α} (h₁ : BddAbove s) (h₂ : BddBelow s) :
    IsBounded s :=
  let ⟨u, hu⟩ := h₁
  let ⟨l, hl⟩ := h₂
  (isBounded_Icc l u).subset (fun _x hx => mem_Icc.mpr ⟨hl hx, hu hx⟩)

open Metric in
/-
**Metric._root_.IsOrderBornology.of_isCompactIcc** 是 Mathlib 中的一个引理，位于命名空间 `Metr
ic`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.IsOrderBornology.of_isCompactIcc (x : α)
    (bddBelow_ball : ∀ r, BddBelow (closedBall x r))
    (bddAbove_ball : ∀ r, BddAbove (closedBall x r)) : IsOrderBornology α where
  isBounded_iff_bddBelow_bddAbove s := by
    refine ⟨?_, fun hs ↦ Metric.isBounded_of_bddAbove_of_bddBelow hs.2 hs.1⟩
    rw [Metric.isBounded_iff_subset_closedBall x]
    rintro ⟨r, hr⟩
    exact ⟨(bddBelow_ball _).mono hr, (bddAbove_ball _).mono hr⟩

end CompactIccSpace

section CompactIccSpace_abs

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] [PseudoMetricSpace α]
  [CompactIccSpace α]

/-
**Metric.isBounded_of_abs_le** 是 Mathlib 中的一个引理，位于命名空间 `Metric`。
形式化陈述：isBounded_of_abs_le (C : α) : Bornology.IsBounded {x : α | |x| <= C}
参数：C : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Metric.isBounded_Icc`：isBounded_Icc (a b : α) : IsBounded (Icc a b)
-/
lemma isBounded_of_abs_le (C : α) : Bornology.IsBounded {x : α | |x| ≤ C} := by
  convert! Metric.isBounded_Icc (-C) C
  ext1 x
  simp [abs_le]
/-
**Metric.isBounded_of_abs_lt** 是 Mathlib 中的一个引理，位于命名空间 `Metric`。
形式化陈述：isBounded_of_abs_lt (C : α) : Bornology.IsBounded {x : α | |x| < C}
参数：C : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Metric.isBounded_Ioo`：isBounded_Ioo (a b : α) : IsBounded (Ioo a b)
-/
lemma isBounded_of_abs_lt (C : α) : Bornology.IsBounded {x : α | |x| < C} := by
  convert! Metric.isBounded_Ioo (-C) C
  ext1 x
  simp [abs_lt]

end CompactIccSpace_abs

end Bounded

section Diam

variable {s : Set α} {x y z : α}

section PseudoMetricSpace
variable [PseudoMetricSpace α]

/-- The diameter of a set in a metric space. To get controllable behavior even when the diameter
should be infinite, we express it in terms of the `ediam` -/
/-
**Metric.diam** 是 Mathlib 中的一个定义，位于命名空间 `Metric`。
形式化陈述：diam (s : Set α) : Real
参数：s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The diameter of a set in a metric space. To get controllable behavior even when 
the diameter
should be infinite, we express it in terms of the `ediam`
-/
noncomputable def diam (s : Set α) : ℝ :=
  ENNReal.toReal (ediam s)

/-- The diameter of a set is always nonnegative -/
/-
**Metric.diam_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：diam_nonneg : 0 <= diam s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.toReal_nonneg`：∀ {a : ENNReal}, 0 ≤ a.toReal

--- 原说明 ---
The diameter of a set is always nonnegative
-/
theorem diam_nonneg : 0 ≤ diam s :=
  ENNReal.toReal_nonneg
/-
**Metric.diam_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：diam_subsingleton (hs : s.Subsingleton) : diam s = 0
参数：hs : s.Subsingleton。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.ediam_subsingleton`：ediam_subsingleton (hs : s.Subsingleton) : ed
iam s = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem diam_subsingleton (hs : s.Subsingleton) : diam s = 0 := by
  simp [diam, ediam_subsingleton hs]

/-- The empty set has zero diameter -/
@[simp]
/-
**Metric.diam_empty** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：diam_empty : diam (∅ : Set α) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.diam_subsingleton`：diam_subsingleton (hs : s.Subsingleton) : diam
 s = 0
· 使用定理 `Set.subsingleton_empty`：subsingleton_empty : (∅ : Set α).Subsingleton

--- 原说明 ---
The empty set has zero diameter
-/
theorem diam_empty : diam (∅ : Set α) = 0 :=
  diam_subsingleton subsingleton_empty

/-- A singleton has zero diameter -/
@[simp]
/-
**Metric.diam_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：diam_singleton : diam ({x} : Set α) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.diam_subsingleton`：diam_subsingleton (hs : s.Subsingleton) : diam
 s = 0
· 使用定理 `Set.subsingleton_singleton`：subsingleton_singleton {a} : ({a} : Set α).S
ubsingleton

--- 原说明 ---
A singleton has zero diameter
-/
theorem diam_singleton : diam ({x} : Set α) = 0 :=
  diam_subsingleton subsingleton_singleton

@[to_additive (attr := simp)]
/-
**Metric.diam_one** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：diam_one [One α] : diam (1 : Set α) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.diam_singleton`：diam_singleton : diam ({x} : Set α) = 0
-/
theorem diam_one [One α] : diam (1 : Set α) = 0 :=
  diam_singleton

-- Does not work as a simp-lemma, since {x, y} reduces to (insert y {x})
/-
**Metric.diam_pair** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：diam_pair : diam ({x, y} : Set α) = dist x y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.ediam_pair`：ediam_pair : ediam {x, y} = edist x y
· 使用定理 `dist_edist`：dist_edist (x y : α) : dist x y = (edist x y).toReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem diam_pair : diam ({x, y} : Set α) = dist x y := by
  simp only [diam, ediam_pair, dist_edist]

-- Does not work as a simp-lemma, since {x, y, z} reduces to (insert z (insert y {x}))
/-
**Metric.diam_triple** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：diam_triple : diam ({x, y, z} : Set α) = max (max (dist x y) (dist x z)) (
dist y z)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.ediam_triple`：ediam_triple : ediam {x, y, z} = max (max (edist x 
y) (edist x z)) (edist y z)
· 使用定理 `dist_edist`：dist_edist (x y : α) : dist x y = (edist x y).toReal
· 使用定理 `ENNReal.toReal_max`：toReal_max (hr : a != ∞) (hp : b != ∞) : ENNReal.toR
eal (max a b) = max (ENNReal.toReal a) (ENNReal.toReal b)
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `max_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, b < a → c <
 a → max b c < a
· 使用定理 `edist_lt_top`：edist_lt_top {α : Type*} [PseudoMetricSpace α] (x y : α) :
 edist x y < ⊤
-/
theorem diam_triple :
    diam ({x, y, z} : Set α) = max (max (dist x y) (dist x z)) (dist y z) := by
  simp only [diam, ediam_triple, dist_edist]
  rw [ENNReal.toReal_max, ENNReal.toReal_max] <;> apply_rules [ne_of_lt, edist_lt_top, max_lt]

/-- If the distance between any two points in a set is bounded by some constant `C`,
then `ENNReal.ofReal C` bounds the emetric diameter of this set. -/
/-
**Metric.ediam_le_of_forall_dist_le** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：ediam_le_of_forall_dist_le {C : Real} (h : forall x in s, forall y in s, d
ist x y <= C) : ediam s <= ENNReal.ofReal C
参数：h : forall x in s, forall y in s, dist x y <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.ediam_le`：ediam_le {d : Real>=0∞} (h : forall x in s, forall y in
 s, edist x y <= d) : ediam s <= d
· 使用定理 `ENNReal.ofReal_le_ofReal`：ofReal_le_ofReal {p q : Real} (h : p <= q) : E
NNReal.ofReal p <= ENNReal.ofReal q
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `edist_dist`：edist_dist (x y : α) : edist x y = ENNReal.ofReal (dist x y)

--- 原说明 ---
If the distance between any two points in a set is bounded by some constant `C`,
then `ENNReal.ofReal C` bounds the emetric diameter of this set.
-/
theorem ediam_le_of_forall_dist_le {C : ℝ} (h : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ C) :
    ediam s ≤ ENNReal.ofReal C :=
  ediam_le fun x hx y hy => (edist_dist x y).symm ▸ ENNReal.ofReal_le_ofReal (h x hx y hy)

/-- If the distance between any two points in a set is bounded by some non-negative constant,
this constant bounds the diameter. -/
/-
**Metric.diam_le_of_forall_dist_le** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：diam_le_of_forall_dist_le {C : Real} (h₀ : 0 <= C) (h : forall x in s, for
all y in s, dist x y <= C) : diam s <= C
参数：h₀ : 0 <= C；h : forall x in s, forall y in s, dist x y <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.toReal_le_of_le_ofReal`：toReal_le_of_le_ofReal {a : Real>=0∞} {b
 : Real} (hb : 0 <= b) (h : a <= ENNReal.ofReal b) : ENNReal.toReal a <= b
· 使用定理 `Metric.ediam_le_of_forall_dist_le`：ediam_le_of_forall_dist_le {C : Real}
 (h : forall x in s, forall y in s, dist x y <= C) : ediam s <= ENNReal.ofReal C

--- 原说明 ---
If the distance between any two points in a set is bounded by some non-negative 
constant,
this constant bounds the diameter.
-/
theorem diam_le_of_forall_dist_le {C : ℝ} (h₀ : 0 ≤ C) (h : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ C) :
    diam s ≤ C :=
  ENNReal.toReal_le_of_le_ofReal h₀ (ediam_le_of_forall_dist_le h)

/-- If the distance between any two points in a nonempty set is bounded by some constant,
this constant bounds the diameter. -/
/-
**Metric.diam_le_of_forall_dist_le_of_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Metric
`。
形式化陈述：diam_le_of_forall_dist_le_of_nonempty (hs : s.Nonempty) {C : Real} (h : fo
rall x in s, forall y in s, dist x y <= C) : diam s <= C
参数：hs : s.Nonempty；h : forall x in s, forall y in s, dist x y <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `Metric.diam_le_of_forall_dist_le`：diam_le_of_forall_dist_le {C : Real} (
h₀ : 0 <= C) (h : forall x in s, forall y in s, dist x y <= C) : diam s <= C

--- 原说明 ---
If the distance between any two points in a nonempty set is bounded by some cons
tant,
this constant bounds the diameter.
-/
theorem diam_le_of_forall_dist_le_of_nonempty (hs : s.Nonempty) {C : ℝ}
    (h : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ C) : diam s ≤ C :=
  have h₀ : 0 ≤ C :=
    let ⟨x, hx⟩ := hs
    le_trans dist_nonneg (h x hx x hx)
  diam_le_of_forall_dist_le h₀ h

/-- The distance between two points in a set is controlled by the diameter of the set. -/
/-
**Metric.dist_le_diam_of_mem'** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：dist_le_diam_of_mem' (h : ediam s != ⊤) (hx : x in s) (hy : y in s) : dist
 x y <= diam s
参数：h : ediam s != ⊤；hx : x in s；hy : y in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.diam.eq_1`：∀ {α : Type u} [inst : PseudoMetricSpace α] (s : Set α
), Metric.diam s = (Metric.ediam s).toReal
· 使用定理 `dist_edist`：dist_edist (x y : α) : dist x y = (edist x y).toReal
· 使用定理 `ENNReal.toReal_mono`：toReal_mono (hb : b != ∞) (h : a <= b) : a.toReal <
= b.toReal
· 使用定理 `Metric.edist_le_ediam_of_mem`：edist_le_ediam_of_mem (hx : x in s) (hy : 
y in s) : edist x y <= ediam s

--- 原说明 ---
The distance between two points in a set is controlled by the diameter of the se
t.
-/
theorem dist_le_diam_of_mem' (h : ediam s ≠ ⊤) (hx : x ∈ s) (hy : y ∈ s) :
    dist x y ≤ diam s := by
  rw [diam, dist_edist]
  exact ENNReal.toReal_mono h <| edist_le_ediam_of_mem hx hy

/-- Characterize the boundedness of a set in terms of the finiteness of its emetric.diameter. -/
/-
**Metric.isBounded_iff_ediam_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：isBounded_iff_ediam_ne_top : IsBounded s ↔ ediam s != ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Metric.isBounded_iff`：isBounded_iff {s : Set α} : IsBounded s ↔ exists C
 : Real, forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> dist x y <= C
· 使用定理 `ne_top_of_le_ne_top`：ne_top_of_le_ne_top (hb : b != ⊤) (hab : a <= b) : 
a != ⊤
· 使用定理 `ENNReal.ofReal_ne_top`：ofReal_ne_top {r : Real} : ENNReal.ofReal r != ∞
· 使用定理 `Metric.ediam_le_of_forall_dist_le`：ediam_le_of_forall_dist_le {C : Real}
 (h : forall x in s, forall y in s, dist x y <= C) : ediam s <= ENNReal.ofReal C
· 使用定理 `Metric.dist_le_diam_of_mem'`：dist_le_diam_of_mem' (h : ediam s != ⊤) (hx
 : x in s) (hy : y in s) : dist x y <= diam s

--- 原说明 ---
Characterize the boundedness of a set in terms of the finiteness of its emetric.
diameter.
-/
theorem isBounded_iff_ediam_ne_top : IsBounded s ↔ ediam s ≠ ⊤ :=
  isBounded_iff.trans <| Iff.intro
    (fun ⟨_C, hC⟩ => ne_top_of_le_ne_top ENNReal.ofReal_ne_top <| ediam_le_of_forall_dist_le hC)
    fun h => ⟨diam s, fun _x hx _y hy => dist_le_diam_of_mem' h hx hy⟩

alias ⟨_root_.Bornology.IsBounded.ediam_ne_top, _⟩ := isBounded_iff_ediam_ne_top
/-
**Metric.ediam_eq_top_iff_unbounded** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：ediam_eq_top_iff_unbounded : ediam s = ⊤ ↔ ¬IsBounded s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Iff.not_left`：Iff.not_left (h : a ↔ ¬b) : ¬a ↔ b
· 使用定理 `Metric.isBounded_iff_ediam_ne_top`：isBounded_iff_ediam_ne_top : IsBounde
d s ↔ ediam s != ⊤
-/
theorem ediam_eq_top_iff_unbounded : ediam s = ⊤ ↔ ¬IsBounded s :=
  isBounded_iff_ediam_ne_top.not_left.symm
/-
**Metric.ediam_univ_eq_top_iff_noncompact** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：ediam_univ_eq_top_iff_noncompact [ProperSpace α] : ediam (univ : Set α) = 
∞ ↔ NoncompactSpace α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_compactSpace_iff`：not_compactSpace_iff : ¬CompactSpace X ↔ Noncompac
tSpace X
· 使用定理 `Metric.compactSpace_iff_isBounded_univ`：compactSpace_iff_isBounded_univ 
[ProperSpace α] : CompactSpace α ↔ IsBounded (univ : Set α)
· 使用定理 `Metric.isBounded_iff_ediam_ne_top`：isBounded_iff_ediam_ne_top : IsBounde
d s ↔ ediam s != ⊤
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ediam_univ_eq_top_iff_noncompact [ProperSpace α] :
    ediam (univ : Set α) = ∞ ↔ NoncompactSpace α := by
  rw [← not_compactSpace_iff, compactSpace_iff_isBounded_univ, isBounded_iff_ediam_ne_top,
    Classical.not_not]

@[simp]
/-
**Metric.ediam_univ_of_noncompact** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：ediam_univ_of_noncompact [ProperSpace α] [NoncompactSpace α] : ediam (univ
 : Set α) = ∞
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.ediam_univ_eq_top_iff_noncompact`：ediam_univ_eq_top_iff_noncompac
t [ProperSpace α] : ediam (univ : Set α) = ∞ ↔ NoncompactSpace α
-/
theorem ediam_univ_of_noncompact [ProperSpace α] [NoncompactSpace α] :
    ediam (univ : Set α) = ∞ :=
  ediam_univ_eq_top_iff_noncompact.mpr ‹_›

@[simp]
/-
**Metric.diam_univ_of_noncompact** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：diam_univ_of_noncompact [ProperSpace α] [NoncompactSpace α] : diam (univ :
 Set α) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.ediam_univ_of_noncompact`：ediam_univ_of_noncompact [ProperSpace α
] [NoncompactSpace α] : ediam (univ : Set α) = ∞
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem diam_univ_of_noncompact [ProperSpace α] [NoncompactSpace α] : diam (univ : Set α) = 0 := by
  simp [diam]

/-- The distance between two points in a set is controlled by the diameter of the set. -/
/-
**Metric.dist_le_diam_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：dist_le_diam_of_mem (h : IsBounded s) (hx : x in s) (hy : y in s) : dist x
 y <= diam s
参数：h : IsBounded s；hx : x in s；hy : y in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.dist_le_diam_of_mem'`：dist_le_diam_of_mem' (h : ediam s != ⊤) (hx
 : x in s) (hy : y in s) : dist x y <= diam s
· 使用定理 `Bornology.IsBounded.ediam_ne_top`：∀ {α : Type u} {s : Set α} [inst : Pse
udoMetricSpace α], Bornology.IsBounded s → Metric.ediam s ≠ ⊤

--- 原说明 ---
The distance between two points in a set is controlled by the diameter of the se
t.
-/
theorem dist_le_diam_of_mem (h : IsBounded s) (hx : x ∈ s) (hy : y ∈ s) : dist x y ≤ diam s :=
  dist_le_diam_of_mem' h.ediam_ne_top hx hy
/-
**Metric.ediam_of_unbounded** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：ediam_of_unbounded (h : ¬IsBounded s) : ediam s = ∞
参数：h : ¬IsBounded s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.ediam_eq_top_iff_unbounded`：ediam_eq_top_iff_unbounded : ediam s 
= ⊤ ↔ ¬IsBounded s
-/
theorem ediam_of_unbounded (h : ¬IsBounded s) : ediam s = ∞ := ediam_eq_top_iff_unbounded.2 h

/-- An unbounded set has zero diameter. If you would prefer to get the value ∞, use `ediam`.
This lemma makes it possible to avoid side conditions in some situations -/
/-
**Metric.diam_eq_zero_of_unbounded** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：diam_eq_zero_of_unbounded (h : ¬IsBounded s) : diam s = 0
参数：h : ¬IsBounded s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.diam.eq_1`：∀ {α : Type u} [inst : PseudoMetricSpace α] (s : Set α
), Metric.diam s = (Metric.ediam s).toReal
· 使用定理 `Metric.ediam_of_unbounded`：ediam_of_unbounded (h : ¬IsBounded s) : ediam
 s = ∞
· 使用定理 `ENNReal.toReal_top`：⊤.toReal = 0

--- 原说明 ---
An unbounded set has zero diameter. If you would prefer to get the value ∞, use 
`ediam`.
This lemma makes it possible to avoid side conditions in some situations
-/
theorem diam_eq_zero_of_unbounded (h : ¬IsBounded s) : diam s = 0 := by
  rw [diam, ediam_of_unbounded h, ENNReal.toReal_top]

/-- If `s ⊆ t`, then the diameter of `s` is bounded by that of `t`, provided `t` is bounded. -/
/-
**Metric.diam_mono** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：diam_mono {s t : Set α} (h : s subseteq t) (ht : IsBounded t) : diam s <= 
diam t
参数：h : s subseteq t；ht : IsBounded t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.toReal_mono`：toReal_mono (hb : b != ∞) (h : a <= b) : a.toReal <
= b.toReal
· 使用定理 `Bornology.IsBounded.ediam_ne_top`：∀ {α : Type u} {s : Set α} [inst : Pse
udoMetricSpace α], Bornology.IsBounded s → Metric.ediam s ≠ ⊤
· 使用定理 `Metric.ediam_mono`：ediam_mono (h : s subseteq t) : ediam s <= ediam t

--- 原说明 ---
If `s ⊆ t`, then the diameter of `s` is bounded by that of `t`, provided `t` is 
bounded.
-/
theorem diam_mono {s t : Set α} (h : s ⊆ t) (ht : IsBounded t) : diam s ≤ diam t :=
  ENNReal.toReal_mono ht.ediam_ne_top <| ediam_mono h

/-- The diameter of a union is controlled by the sum of the diameters, and the distance between
any two points in each of the sets. This lemma is true without any side condition, since it is
obviously true if `s ∪ t` is unbounded. -/
/-
**Metric.diam_union** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：diam_union {t : Set α} (xs : x in s) (yt : y in t) : diam (s union t) <= d
iam s + dist x y + diam t
参数：xs : x in s；yt : y in t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_edist`：dist_edist (x y : α) : dist x y = (edist x y).toReal
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `ENNReal.toReal_le_add'`：toReal_le_add' (hle : a <= b + c) (hb : b = ∞ ->
 a = ∞) (hc : c = ∞ -> a = ∞) : a.toReal <= b.toReal + c.toReal
· 使用定理 `Metric.ediam_union_le_add_edist`：ediam_union_le_add_edist (xs : x in s) 
(yt : y in t) : ediam (s union t) <= ediam s + edist x y + ediam t
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用定理 `Metric.ediam_mono`：ediam_mono (h : s subseteq t) : ediam s <= ediam t
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `ENNReal.toReal_add_le`：toReal_add_le : (a + b).toReal <= a.toReal + b.to
Real

--- 原说明 ---
The diameter of a union is controlled by the sum of the diameters, and the dista
nce between
any two points in each of the sets. This lemma is true without any side conditio
n, since it is
obviously true if `s ∪ t` is unbounded.
-/
theorem diam_union {t : Set α} (xs : x ∈ s) (yt : y ∈ t) :
    diam (s ∪ t) ≤ diam s + dist x y + diam t := by
  simp only [diam, dist_edist]
  grw [ENNReal.toReal_le_add' (ediam_union_le_add_edist xs yt), ENNReal.toReal_add_le]
  · simp only [ENNReal.add_eq_top, edist_ne_top, or_false]
    exact fun h ↦ top_unique <| h ▸ ediam_mono subset_union_left
  · exact fun h ↦ top_unique <| h ▸ ediam_mono subset_union_right

/-- If two sets intersect, the diameter of the union is bounded by the sum of the diameters. -/
/-
**Metric.diam_union'** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：diam_union' {t : Set α} (h : (s inter t).Nonempty) : diam (s union t) <= d
iam s + diam t
参数：h : (s inter t).Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Metric.diam_union`：diam_union {t : Set α} (xs : x in s) (yt : y in t) : 
diam (s union t) <= diam s + dist x y + diam t

--- 原说明 ---
If two sets intersect, the diameter of the union is bounded by the sum of the di
ameters.
-/
theorem diam_union' {t : Set α} (h : (s ∩ t).Nonempty) : diam (s ∪ t) ≤ diam s + diam t := by
  rcases h with ⟨x, ⟨xs, xt⟩⟩
  simpa using diam_union xs xt
/-
**Metric.diam_le_of_subset_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：diam_le_of_subset_closedBall {r : Real} (hr : 0 <= r) (h : s subseteq clos
edBall x r) : diam s <= 2 * r
参数：hr : 0 <= r；h : s subseteq closedBall x r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.diam_le_of_forall_dist_le`：diam_le_of_forall_dist_le {C : Real} (
h₀ : 0 <= C) (h : forall x in s, forall y in s, dist x y <= C) : diam s <= C
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用引理 `zero_le_two`：zero_le_two [Preorder α] [ZeroLEOneClass α] [AddLeftMono α]
 : (0 : α) <= 2
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `dist_triangle_right`：dist_triangle_right (x y z : α) : dist x y <= dist 
x z + dist y z
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_two`：mul_two (n : α) : n * 2 = n + n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem diam_le_of_subset_closedBall {r : ℝ} (hr : 0 ≤ r) (h : s ⊆ closedBall x r) :
    diam s ≤ 2 * r :=
  diam_le_of_forall_dist_le (mul_nonneg zero_le_two hr) fun a ha b hb =>
    calc
      dist a b ≤ dist a x + dist b x := dist_triangle_right _ _ _
      _ ≤ r + r := add_le_add (h ha) (h hb)
      _ = 2 * r := by simp [mul_two, mul_comm]

/-- The diameter of a closed ball of radius `r` is at most `2 r`. -/
/-
**Metric.diam_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：diam_closedBall {r : Real} (h : 0 <= r) : diam (closedBall x r) <= 2 * r
参数：h : 0 <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.diam_le_of_subset_closedBall`：diam_le_of_subset_closedBall {r : R
eal} (hr : 0 <= r) (h : s subseteq closedBall x r) : diam s <= 2 * r
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s

--- 原说明 ---
The diameter of a closed ball of radius `r` is at most `2 r`.
-/
theorem diam_closedBall {r : ℝ} (h : 0 ≤ r) : diam (closedBall x r) ≤ 2 * r :=
  diam_le_of_subset_closedBall h Subset.rfl

/-- The diameter of a ball of radius `r` is at most `2 r`. -/
/-
**Metric.diam_ball** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：diam_ball {r : Real} (h : 0 <= r) : diam (ball x r) <= 2 * r
参数：h : 0 <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.diam_le_of_subset_closedBall`：diam_le_of_subset_closedBall {r : R
eal} (hr : 0 <= r) (h : s subseteq closedBall x r) : diam s <= 2 * r
· 使用定理 `Metric.ball_subset_closedBall`：ball_subset_closedBall : ball x ε subsete
q closedBall x ε

--- 原说明 ---
The diameter of a ball of radius `r` is at most `2 r`.
-/
theorem diam_ball {r : ℝ} (h : 0 ≤ r) : diam (ball x r) ≤ 2 * r :=
  diam_le_of_subset_closedBall h ball_subset_closedBall

/-- If a family of complete sets with diameter tending to `0` is such that each finite intersection
is nonempty, then the total intersection is also nonempty. -/
/-
**Metric._root_.IsComplete.nonempty_iInter_of_nonempty_biInter** 是 Mathlib 中的一个定
理，位于命名空间 `Metric`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a family of complete sets with diameter tending to `0` is such that each fini
te intersection
is nonempty, then the total intersection is also nonempty.
-/
theorem _root_.IsComplete.nonempty_iInter_of_nonempty_biInter {s : ℕ → Set α}
    (h0 : IsComplete (s 0)) (hs : ∀ n, IsClosed (s n)) (h's : ∀ n, IsBounded (s n))
    (h : ∀ N, (⋂ n ≤ N, s n).Nonempty) (h' : Tendsto (fun n => diam (s n)) atTop (𝓝 0)) :
    (⋂ n, s n).Nonempty := by
  let u N := (h N).some
  have I : ∀ n N, n ≤ N → u N ∈ s n := by
    intro n N hn
    apply mem_of_subset_of_mem _ (h N).choose_spec
    intro x hx
    simp only [mem_iInter] at hx
    exact hx n hn
  have : CauchySeq u := by
    apply cauchySeq_of_le_tendsto_0 _ _ h'
    intro m n N hm hn
    exact dist_le_diam_of_mem (h's N) (I _ _ hm) (I _ _ hn)
  obtain ⟨x, -, xlim⟩ : ∃ x ∈ s 0, Tendsto (fun n : ℕ => u n) atTop (𝓝 x) :=
    cauchySeq_tendsto_of_isComplete h0 (fun n => I 0 n zero_le) this
  refine ⟨x, mem_iInter.2 fun n => ?_⟩
  apply (hs n).mem_of_tendsto xlim
  filter_upwards [Ici_mem_atTop n] with p hp
  exact I n p hp

/-- In a complete space, if a family of closed sets with diameter tending to `0` is such that each
finite intersection is nonempty, then the total intersection is also nonempty. -/
/-
**Metric.nonempty_iInter_of_nonempty_biInter** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：nonempty_iInter_of_nonempty_biInter [CompleteSpace α] {s : Nat -> Set α} (
hs : forall n, IsClosed (s n)) (h's : forall n, IsBounded (s n)) (h : forall N, 
(⋂ n <= N, s n).Nonempty) (h' : Tendsto (fun n => diam (s n)) atTop (𝓝 0)) : (⋂ 
n, s n).Nonempty
参数：hs : forall n, IsClosed (s n)；h's : forall n, IsBounded (s n)；h : forall N, (
⋂ n <= N, s n).Nonempty；h' : Tendsto (fun n => diam (s n)) atTop (𝓝 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsComplete.nonempty_iInter_of_nonempty_biInter`：∀ {α : Type u} [inst : P
seudoMetricSpace α] {s : ℕ → Set α},   IsComplete (s 0) →     (∀ (n : ℕ), IsClos
ed (s n)) →       (∀ (n : ℕ), Bornol…
· 使用定理 `IsClosed.isComplete`：IsClosed.isComplete [CompleteSpace α] {s : Set α} (
h : IsClosed s) : IsComplete s

--- 原说明 ---
In a complete space, if a family of closed sets with diameter tending to `0` is 
such that each
finite intersection is nonempty, then the total intersection is also nonempty.
-/
theorem nonempty_iInter_of_nonempty_biInter [CompleteSpace α] {s : ℕ → Set α}
    (hs : ∀ n, IsClosed (s n)) (h's : ∀ n, IsBounded (s n)) (h : ∀ N, (⋂ n ≤ N, s n).Nonempty)
    (h' : Tendsto (fun n => diam (s n)) atTop (𝓝 0)) : (⋂ n, s n).Nonempty :=
  (hs 0).isComplete.nonempty_iInter_of_nonempty_biInter hs h's h h'

end PseudoMetricSpace

section MetricSpace

/-
**Metric.diam_pos** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：diam_pos [MetricSpace α] (hs1 : s.Nontrivial) (hs2 : IsBounded s) : 0 < di
am s
参数：hs1 : s.Nontrivial；hs2 : IsBounded s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `dist_pos`：dist_pos {x y : γ} : 0 < dist x y ↔ x != y
· 使用定理 `Metric.dist_le_diam_of_mem`：dist_le_diam_of_mem (h : IsBounded s) (hx : 
x in s) (hy : y in s) : dist x y <= diam s
-/
theorem diam_pos [MetricSpace α] (hs1 : s.Nontrivial) (hs2 : IsBounded s) : 0 < diam s := by
  rcases hs1 with ⟨x, hx, y, hy, hxy⟩
  exact (dist_pos.mpr hxy).trans_le <| Metric.dist_le_diam_of_mem hs2 hx hy

end MetricSpace

end Diam

end Metric

namespace Mathlib.Meta.Positivity

open Lean Meta Qq Function

/-- Extension for the `positivity` tactic: the diameter of a set is always nonnegative. -/
@[positivity Metric.diam _]
meta def evalDiam : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@Metric.diam _ $inst $s) =>
    assertInstancesCommute
    pure (.nonnegative q(Metric.diam_nonneg))
  | _, _, _ => throwError "not ‖ · ‖"

end Mathlib.Meta.Positivity

section

open Metric

variable [PseudoMetricSpace α]

/-
**Metric.cobounded_eq_cocompact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Metric.cobounded_eq_cocompact [ProperSpace α] : cobounded α = cocompact α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bornology.cobounded_eq_bot`：cobounded_eq_bot : cobounded α = ⊥
· 使用定理 `Metric.instBoundedSpaceOfCompactSpace`：∀ {α : Type u} [inst : PseudoMetr
icSpace α] [CompactSpace α], BoundedSpace α
· 使用定理 `instCompactSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Indiscrete
Topology X], CompactSpace X
· 使用定理 `instIndiscreteTopologyOfSubsingleton`：∀ {α : Type u} [inst : Topological
Space α] [Subsingleton α], IndiscreteTopology α
· 使用定理 `Filter.cocompact_eq_bot`：Filter.cocompact_eq_bot [CompactSpace X] : Filt
er.cocompact X = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Metric.cobounded_le_cocompact`：cobounded_le_cocompact : cobounded α <= c
ocompact α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `Filter.HasBasis.ge_iff`：∀ {α : Type u_1} {ι' : Sort u_5} {l l' : Filter 
α} {p' : ι' → Prop} {s' : ι' → Set α},   l'.HasBasis p' s' → (l ≤ l' ↔ ∀ (i' : ι
'), p' i' → …
· 使用定理 `Metric.hasBasis_cobounded_compl_closedBall`：hasBasis_cobounded_compl_clo
sedBall (c : α) : (cobounded α).HasBasis (fun _ => True) (fun r => (closedBall c
 r)ᶜ)
· 使用定理 `IsCompact.compl_mem_cocompact`：∀ {X : Type u} [inst : TopologicalSpace X
] {s : Set X}, IsCompact s → sᶜ ∈ Filter.cocompact X
· 使用定理 `ProperSpace.isCompact_closedBall`：∀ {α : Type u} {inst : PseudoMetricSpa
ce α} [self : ProperSpace α] (x : α) (r : ℝ), IsCompact (Metric.closedBall x r)
-/
theorem Metric.cobounded_eq_cocompact [ProperSpace α] : cobounded α = cocompact α := by
  nontriviality α; inhabit α
  exact cobounded_le_cocompact.antisymm <| (hasBasis_cobounded_compl_closedBall default).ge_iff.2
    fun _ _ ↦ (isCompact_closedBall _ _).compl_mem_cocompact
/-
**tendsto_dist_right_cocompact_atTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_dist_right_cocompact_atTop [ProperSpace α] (x : α) : Tendsto (dist
 · x) (cocompact α) atTop
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `Metric.tendsto_dist_right_cobounded_atTop`：tendsto_dist_right_cobounded_
atTop (c : α) : Tendsto (dist · c) (cobounded α) atTop
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Metric.cobounded_eq_cocompact`：Metric.cobounded_eq_cocompact [ProperSpac
e α] : cobounded α = cocompact α
-/
theorem tendsto_dist_right_cocompact_atTop [ProperSpace α] (x : α) :
    Tendsto (dist · x) (cocompact α) atTop :=
  (tendsto_dist_right_cobounded_atTop x).mono_left cobounded_eq_cocompact.ge
/-
**tendsto_dist_left_cocompact_atTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_dist_left_cocompact_atTop [ProperSpace α] (x : α) : Tendsto (dist 
x) (cocompact α) atTop
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `Metric.tendsto_dist_left_cobounded_atTop`：tendsto_dist_left_cobounded_at
Top (c : α) : Tendsto (dist c) (cobounded α) atTop
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Metric.cobounded_eq_cocompact`：Metric.cobounded_eq_cocompact [ProperSpac
e α] : cobounded α = cocompact α
-/
theorem tendsto_dist_left_cocompact_atTop [ProperSpace α] (x : α) :
    Tendsto (dist x) (cocompact α) atTop :=
  (tendsto_dist_left_cobounded_atTop x).mono_left cobounded_eq_cocompact.ge
/-
**comap_dist_left_atTop_eq_cocompact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：comap_dist_left_atTop_eq_cocompact [ProperSpace α] (x : α) : comap (dist x
) atTop = cocompact α
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.comap_dist_left_atTop`：comap_dist_left_atTop (c : α) : comap (dis
t c) atTop = cobounded α
· 使用定理 `Metric.cobounded_eq_cocompact`：Metric.cobounded_eq_cocompact [ProperSpac
e α] : cobounded α = cocompact α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comap_dist_left_atTop_eq_cocompact [ProperSpace α] (x : α) :
    comap (dist x) atTop = cocompact α := by simp [cobounded_eq_cocompact]
/-
**tendsto_cocompact_of_tendsto_dist_comp_atTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_cocompact_of_tendsto_dist_comp_atTop {f : β -> α} {l : Filter β} (
x : α) (h : Tendsto (fun y => dist (f y) x) l atTop) : Tendsto f l (cocompact α)
参数：x : α；h : Tendsto (fun y => dist (f y) x) l atTop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.mono_right`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
x : Filter α} {y z : Filter β},   Filter.Tendsto f x y → y ≤ z → Filter.Tendsto 
f x z
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.tendsto_dist_right_atTop_iff`：tendsto_dist_right_atTop_iff (c : α
) {f : β -> α} {l : Filter β} : Tendsto (fun x => dist (f x) c) l atTop ↔ Tendst
o f l (cobounded α)
· 使用定理 `Metric.cobounded_le_cocompact`：cobounded_le_cocompact : cobounded α <= c
ocompact α
-/
theorem tendsto_cocompact_of_tendsto_dist_comp_atTop {f : β → α} {l : Filter β} (x : α)
    (h : Tendsto (fun y => dist (f y) x) l atTop) : Tendsto f l (cocompact α) :=
  ((tendsto_dist_right_atTop_iff _).1 h).mono_right cobounded_le_cocompact
/-
**Metric.finite_isBounded_inter_isClosed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Metric.finite_isBounded_inter_isClosed [ProperSpace α] {K s : Set α} (hsd 
: IsDiscrete s) (hK : IsBounded K) (hs : IsClosed s) : Set.Finite (K inter s)
参数：hsd : IsDiscrete s；hK : IsBounded K；hs : IsClosed s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `IsCompact.finite`：IsCompact.finite (hs : IsCompact s) (hs' : IsDiscrete 
s) : s.Finite
· 使用定理 `IsCompact.inter_right`：IsCompact.inter_right (hs : IsCompact s) (ht : Is
Closed t) : IsCompact (s inter t)
· 使用定理 `Bornology.IsBounded.isCompact_closure`：∀ {α : Type u} {s : Set α} [inst 
: PseudoMetricSpace α] [ProperSpace α], Bornology.IsBounded s → IsCompact (closu
re s)
· 使用引理 `IsDiscrete.mono`：IsDiscrete.mono {t : Set X} (hs : IsDiscrete s) (hst : 
t subseteq s) : IsDiscrete t
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `Set.inter_subset_inter_left`：inter_subset_inter_left {s t : Set α} (u : 
Set α) (H : s subseteq t) : s inter u subseteq t inter u
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
theorem Metric.finite_isBounded_inter_isClosed [ProperSpace α] {K s : Set α} (hsd : IsDiscrete s)
    (hK : IsBounded K) (hs : IsClosed s) : Set.Finite (K ∩ s) := by
  refine (IsCompact.finite ?_ ?_).subset (Set.inter_subset_inter_left s subset_closure)
  · exact hK.isCompact_closure.inter_right hs
  · exact hsd.mono Set.inter_subset_right

end

namespace Continuous

variable {α β : Type*} [LinearOrder α] [TopologicalSpace α] [OrderClosedTopology α]
  [PseudoMetricSpace β] [ProperSpace β]

/-- A version of the **Extreme Value Theorem**: if the set where a continuous function `f`
into a linearly ordered space takes values `≤ f x₀` is bounded for some `x₀`,
then `f` has a global minimum (under suitable topological assumptions).

This is a convenient combination of `Continuous.exists_forall_le'` and
`Metric.isCompact_of_isClosed_isBounded`. -/
/-
**Continuous.exists_forall_le_of_isBounded** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
`。
形式化陈述：exists_forall_le_of_isBounded {f : β -> α} (hf : Continuous f) (x₀ : β) (h
 : Bornology.IsBounded {x : β | f x <= f x₀}) : exists x, forall y, f x <= f y
参数：hf : Continuous f；x₀ : β；h : Bornology.IsBounded {x : β | f x <= f x₀}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.exists_forall_le'`：Continuous.exists_forall_le' [ClosedIicTop
ology α] {f : β -> α} (hf : Continuous f) (x₀ : β) (h : forallᶠ x in cocompact β
, f x₀ <= f x) : e…
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.mem_cocompact'`：mem_cocompact' : s in cocompact X ↔ exists t, IsC
ompact t ∧ sᶜ subseteq t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Metric.isCompact_of_isClosed_isBounded`：isCompact_of_isClosed_isBounded 
[ProperSpace α] (hc : IsClosed s) (hb : IsBounded s) : IsCompact s
· 使用定理 `isClosed_le`：isClosed_le [TopologicalSpace β] {f g : β -> α} (hf : Conti
nuous f) (hg : Continuous g) : IsClosed { b | f b <= g b }
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b

--- 原说明 ---
A version of the **Extreme Value Theorem**: if the set where a continuous functi
on `f`
into a linearly ordered space takes values `≤ f x₀` is bounded for some `x₀`,
then `f` has a global minimum (under suitable topological assumptions).

This is a convenient combination of `Continuous.exists_forall_le'` and
`Metric.isCompact_of_isClosed_isBounded`.
-/
theorem exists_forall_le_of_isBounded {f : β → α} (hf : Continuous f) (x₀ : β)
    (h : Bornology.IsBounded {x : β | f x ≤ f x₀}) :
    ∃ x, ∀ y, f x ≤ f y := by
  refine hf.exists_forall_le' (x₀ := x₀) ?_
  have hU : {x : β | f x₀ < f x} ∈ Filter.cocompact β := by
    refine Filter.mem_cocompact'.mpr ⟨_, ?_, fun ⦃_⦄ a ↦ a⟩
    simp only [Set.compl_ofPred, not_lt]
    exact Metric.isCompact_of_isClosed_isBounded (isClosed_le (by fun_prop) (by fun_prop)) h
  filter_upwards [hU] with x hx using hx.le

/-- A version of the **Extreme Value Theorem**: if the set where a continuous function `f`
into a linearly ordered space takes values `≥ f x₀` is bounded for some `x₀`,
then `f` has a global maximum (under suitable topological assumptions).

This is a convenient combination of `Continuous.exists_forall_ge'` and
`Metric.isCompact_of_isClosed_isBounded`. -/
/-
**Continuous.exists_forall_ge_of_isBounded** 是 Mathlib 中的一个定理，位于命名空间 `Continuous
`。
形式化陈述：exists_forall_ge_of_isBounded {f : β -> α} (hf : Continuous f) (x₀ : β) (h
 : Bornology.IsBounded {x : β | f x₀ <= f x}) : exists x, forall y, f y <= f x
参数：hf : Continuous f；x₀ : β；h : Bornology.IsBounded {x : β | f x₀ <= f x}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.exists_forall_le_of_isBounded`：exists_forall_le_of_isBounded 
{f : β -> α} (hf : Continuous f) (x₀ : β) (h : Bornology.IsBounded {x : β | f x 
<= f x₀}) : exists x, forall y…
· 使用定理 `instOrderClosedTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpac
e α] [inst_1 : Preorder α] [t : OrderClosedTopology α], OrderClosedTopology αᵒᵈ

--- 原说明 ---
A version of the **Extreme Value Theorem**: if the set where a continuous functi
on `f`
into a linearly ordered space takes values `≥ f x₀` is bounded for some `x₀`,
then `f` has a global maximum (under suitable topological assumptions).

This is a convenient combination of `Continuous.exists_forall_ge'` and
`Metric.isCompact_of_isClosed_isBounded`.
-/
theorem exists_forall_ge_of_isBounded {f : β → α} (hf : Continuous f) (x₀ : β)
    (h : Bornology.IsBounded {x : β | f x₀ ≤ f x}) :
    ∃ x, ∀ y, f y ≤ f x :=
  hf.exists_forall_le_of_isBounded (α := αᵒᵈ) x₀ h

end Continuous

