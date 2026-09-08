/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Constructions
public import Mathlib.Topology.Order.DenselyOrdered
public import Mathlib.Topology.UniformSpace.Compact

/-!
# Extra lemmas about pseudo-metric spaces
-/

public section

open Bornology Filter Metric Set
open scoped NNReal Topology

variable {ι α : Type*} [PseudoMetricSpace α]

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OrderTopology ℝ :=
  orderTopology_of_nhds_abs fun x => by
    simp only [nhds_basis_ball.eq_biInf, ball, Real.dist_eq, abs_sub_comm]
/-
**Real.singleton_eq_inter_Icc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Real.singleton_eq_inter_Icc (b : Real) : {b} = ⋂ (r > 0), Icc (b - r) (b +
 r)
参数：b : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.Icc_eq_closedBall`：Real.Icc_eq_closedBall (x y : Real) : Icc x y = 
closedBall ((x + y) / 2) ((y - x) / 2)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_add_add_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b c : G)
, a - c + (b + c) = a + b
· 使用定理 `add_self_div_two`：∀ {K : Type u_1} [inst : DivisionSemiring K] [NeZero 2
] (a : K), (a + a) / 2 = a
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `add_sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b c : G)
, a + b - (a - c) = b + c
· 使用定理 `biInter_basis_nhds`：biInter_basis_nhds [T1Space X] {ι : Sort*} {p : ι ->
 Prop} {s : ι -> Set X} {x : X} (h : (𝓝 x).HasBasis p s) : ⋂ (i) (_ : p i), s i 
= {x}
· 使用定理 `Metric.nhds_basis_closedBall`：nhds_basis_closedBall : (𝓝 x).HasBasis (fu
n ε : Real => 0 < ε) (closedBall x)
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `OrderClosedTopology.to_t2Space`：∀ {α : Type u} [inst : TopologicalSpace 
α] [inst_1 : PartialOrder α] [t : OrderClosedTopology α], T2Space α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Real.singleton_eq_inter_Icc (b : ℝ) : {b} = ⋂ (r > 0), Icc (b - r) (b + r) := by
  simp [Icc_eq_closedBall, biInter_basis_nhds Metric.nhds_basis_closedBall]

/-- Special case of the sandwich lemma; see `tendsto_of_tendsto_of_tendsto_of_le_of_le'` for the
general case. -/
/-
**squeeze_zero'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：squeeze_zero' {α} {f g : α -> Real} {t₀ : Filter α} (hf : forallᶠ t in t₀,
 0 <= f t) (hft : forallᶠ t in t₀, f t <= g t) (g0 : Tendsto g t₀ (𝓝 0)) : Tends
to f t₀ (𝓝 0)
参数：hf : forallᶠ t in t₀, 0 <= f t；hft : forallᶠ t in t₀, f t <= g t；g0 : Tendsto
 g t₀ (𝓝 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_of_tendsto_of_tendsto_of_le_of_le'`：tendsto_of_tendsto_of_tendst
o_of_le_of_le' [OrderTopology α] {f g h : β -> α} {b : Filter β} {a : α} (hg : T
endsto g b (𝓝 a)) (hh : Tendsto …
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)

--- 原说明 ---
Special case of the sandwich lemma; see `tendsto_of_tendsto_of_tendsto_of_le_of_
le'` for the
general case.
-/
lemma squeeze_zero' {α} {f g : α → ℝ} {t₀ : Filter α} (hf : ∀ᶠ t in t₀, 0 ≤ f t)
    (hft : ∀ᶠ t in t₀, f t ≤ g t) (g0 : Tendsto g t₀ (𝓝 0)) : Tendsto f t₀ (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds g0 hf hft

/-- Special case of the sandwich lemma; see `tendsto_of_tendsto_of_tendsto_of_le_of_le`
and `tendsto_of_tendsto_of_tendsto_of_le_of_le'` for the general case. -/
/-
**squeeze_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：squeeze_zero {α} {f g : α -> Real} {t₀ : Filter α} (hf : forall t, 0 <= f 
t) (hft : forall t, f t <= g t) (g0 : Tendsto g t₀ (𝓝 0)) : Tendsto f t₀ (𝓝 0)
参数：hf : forall t, 0 <= f t；hft : forall t, f t <= g t；g0 : Tendsto g t₀ (𝓝 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `squeeze_zero'`：squeeze_zero' {α} {f g : α -> Real} {t₀ : Filter α} (hf :
 forallᶠ t in t₀, 0 <= f t) (hft : forallᶠ t in t₀, f t <= g t) (g0 : Tendsto g 
t₀ …
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x

--- 原说明 ---
Special case of the sandwich lemma; see `tendsto_of_tendsto_of_tendsto_of_le_of_
le`
and `tendsto_of_tendsto_of_tendsto_of_le_of_le'` for the general case.
-/
lemma squeeze_zero {α} {f g : α → ℝ} {t₀ : Filter α} (hf : ∀ t, 0 ≤ f t) (hft : ∀ t, f t ≤ g t)
    (g0 : Tendsto g t₀ (𝓝 0)) : Tendsto f t₀ (𝓝 0) :=
  squeeze_zero' (Eventually.of_forall hf) (Eventually.of_forall hft) g0

/-- If `u` is a neighborhood of `x`, then for small enough `r`, the closed ball
`Metric.closedBall x r` is contained in `u`. -/
/-
**eventually_closedBall_subset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eventually_closedBall_subset {x : α} {u : Set α} (hu : u in 𝓝 x) : forallᶠ
 r in 𝓝 (0 : Real), closedBall x r subseteq u
参数：hu : u in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Metric.nhds_basis_closedBall`：nhds_basis_closedBall : (𝓝 x).HasBasis (fu
n ε : Real => 0 < ε) (closedBall x)
· 使用定理 `Iic_mem_nhds`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Linea
rOrder α] [ClosedIciTopology α] {a b : α},   b < a → Set.Iic a ∈ nhds b
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Metric.closedBall_subset_closedBall`：closedBall_subset_closedBall (h : ε
₁ <= ε₂) : closedBall x ε₁ subseteq closedBall x ε₂

--- 原说明 ---
If `u` is a neighborhood of `x`, then for small enough `r`, the closed ball
`Metric.closedBall x r` is contained in `u`.
-/
lemma eventually_closedBall_subset {x : α} {u : Set α} (hu : u ∈ 𝓝 x) :
    ∀ᶠ r in 𝓝 (0 : ℝ), closedBall x r ⊆ u := by
  obtain ⟨ε, εpos, hε⟩ : ∃ ε, 0 < ε ∧ closedBall x ε ⊆ u := nhds_basis_closedBall.mem_iff.1 hu
  have : Iic ε ∈ 𝓝 (0 : ℝ) := Iic_mem_nhds εpos
  filter_upwards [this] with _ hr using Subset.trans (closedBall_subset_closedBall hr) hε
/-
**tendsto_closedBall_smallSets** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tendsto_closedBall_smallSets (x : α) : Tendsto (closedBall x) (𝓝 0) (𝓝 x).
smallSets
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_smallSets_iff`：tendsto_smallSets_iff {f : α -> Set β} : T
endsto f la lb.smallSets ↔ forall t in lb, forallᶠ x in la, f x subseteq t
· 使用引理 `eventually_closedBall_subset`：eventually_closedBall_subset {x : α} {u : 
Set α} (hu : u in 𝓝 x) : forallᶠ r in 𝓝 (0 : Real), closedBall x r subseteq u
-/
lemma tendsto_closedBall_smallSets (x : α) : Tendsto (closedBall x) (𝓝 0) (𝓝 x).smallSets :=
  tendsto_smallSets_iff.2 fun _ ↦ eventually_closedBall_subset

/-- If `u` is a neighborhood of `x`, then for small enough `r`, the open ball
`Metric.ball x r` is contained in `u`. -/
/-
**eventually_ball_subset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eventually_ball_subset {x : α} {u : Set α} (hu : u in 𝓝 x) : forallᶠ r in 
𝓝 (0 : Real), ball x r subseteq u
参数：hu : u in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用引理 `eventually_closedBall_subset`：eventually_closedBall_subset {x : α} {u : 
Set α} (hu : u in 𝓝 x) : forallᶠ r in 𝓝 (0 : Real), closedBall x r subseteq u
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Metric.ball_subset_closedBall`：ball_subset_closedBall : ball x ε subsete
q closedBall x ε

--- 原说明 ---
If `u` is a neighborhood of `x`, then for small enough `r`, the open ball
`Metric.ball x r` is contained in `u`.
-/
lemma eventually_ball_subset {x : α} {u : Set α} (hu : u ∈ 𝓝 x) : ∀ᶠ r in 𝓝 (0 : ℝ), ball x r ⊆ u :=
  (eventually_closedBall_subset hu).mono fun _r hr ↦ ball_subset_closedBall.trans hr

namespace Metric
variable {x y z : α} {ε ε₁ ε₂ : ℝ} {s : Set α}

/-
**Metric.isClosed_closedBall** 是 Mathlib 中的一个引理，位于命名空间 `Metric`。
形式化陈述：isClosed_closedBall : IsClosed (closedBall x ε)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_le`：isClosed_le [TopologicalSpace β] {f g : β -> α} (hf : Conti
nuous f) (hg : Continuous g) : IsClosed { b | f b <= g b }
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Continuous.dist`：∀ {α : Type u_1} {β : Type u_2} [inst : PseudoMetricSpa
ce α] [inst_1 : TopologicalSpace β] {f g : β → α},   Continuous f → Continuous g
 → Co…
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
-/
lemma isClosed_closedBall : IsClosed (closedBall x ε) := isClosed_le (by fun_prop) continuous_const
/-
**Metric.isClosed_sphere** 是 Mathlib 中的一个引理，位于命名空间 `Metric`。
形式化陈述：isClosed_sphere : IsClosed (sphere x ε)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_eq`：isClosed_eq [T2Space X] {f g : Y -> X} (hf : Continuous f) 
(hg : Continuous g) : IsClosed { y : Y | f y = g y }
· 使用定理 `OrderClosedTopology.to_t2Space`：∀ {α : Type u} [inst : TopologicalSpace 
α] [inst_1 : PartialOrder α] [t : OrderClosedTopology α], T2Space α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Continuous.dist`：∀ {α : Type u_1} {β : Type u_2} [inst : PseudoMetricSpa
ce α] [inst_1 : TopologicalSpace β] {f g : β → α},   Continuous f → Continuous g
 → Co…
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
-/
lemma isClosed_sphere : IsClosed (sphere x ε) := isClosed_eq (by fun_prop) continuous_const

@[simp]
/-
**Metric.closure_closedBall** 是 Mathlib 中的一个引理，位于命名空间 `Metric`。
形式化陈述：closure_closedBall : closure (closedBall x ε) = closedBall x ε
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用引理 `Metric.isClosed_closedBall`：isClosed_closedBall : IsClosed (closedBall x
 ε)
-/
lemma closure_closedBall : closure (closedBall x ε) = closedBall x ε :=
  isClosed_closedBall.closure_eq

@[simp]
/-
**Metric.closure_sphere** 是 Mathlib 中的一个引理，位于命名空间 `Metric`。
形式化陈述：closure_sphere : closure (sphere x ε) = sphere x ε
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用引理 `Metric.isClosed_sphere`：isClosed_sphere : IsClosed (sphere x ε)
-/
lemma closure_sphere : closure (sphere x ε) = sphere x ε :=
  isClosed_sphere.closure_eq
/-
**Metric.closure_ball_subset_closedBall** 是 Mathlib 中的一个引理，位于命名空间 `Metric`。
形式化陈述：closure_ball_subset_closedBall : closure (ball x ε) subseteq closedBall x 
ε
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
· 使用定理 `Metric.ball_subset_closedBall`：ball_subset_closedBall : ball x ε subsete
q closedBall x ε
· 使用引理 `Metric.isClosed_closedBall`：isClosed_closedBall : IsClosed (closedBall x
 ε)
-/
lemma closure_ball_subset_closedBall : closure (ball x ε) ⊆ closedBall x ε :=
  closure_minimal ball_subset_closedBall isClosed_closedBall
/-
**Metric.frontier_ball_subset_sphere** 是 Mathlib 中的一个引理，位于命名空间 `Metric`。
形式化陈述：frontier_ball_subset_sphere : frontier (ball x ε) subseteq sphere x ε
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `frontier_lt_subset_eq`：frontier_lt_subset_eq (hf : Continuous f) (hg : C
ontinuous g) : frontier { b | f b < g b } subseteq { b | f b = g b }
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Continuous.dist`：∀ {α : Type u_1} {β : Type u_2} [inst : PseudoMetricSpa
ce α] [inst_1 : TopologicalSpace β] {f g : β → α},   Continuous f → Continuous g
 → Co…
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
-/
lemma frontier_ball_subset_sphere : frontier (ball x ε) ⊆ sphere x ε :=
  frontier_lt_subset_eq (by fun_prop) continuous_const
/-
**Metric.frontier_closedBall_subset_sphere** 是 Mathlib 中的一个引理，位于命名空间 `Metric`。
形式化陈述：frontier_closedBall_subset_sphere : frontier (closedBall x ε) subseteq sph
ere x ε
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `frontier_le_subset_eq`：frontier_le_subset_eq (hf : Continuous f) (hg : C
ontinuous g) : frontier { b | f b <= g b } subseteq { b | f b = g b }
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Continuous.dist`：∀ {α : Type u_1} {β : Type u_2} [inst : PseudoMetricSpa
ce α] [inst_1 : TopologicalSpace β] {f g : β → α},   Continuous f → Continuous g
 → Co…
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
-/
lemma frontier_closedBall_subset_sphere : frontier (closedBall x ε) ⊆ sphere x ε :=
  frontier_le_subset_eq (by fun_prop) continuous_const
/-
**Metric.closedBall_zero'** 是 Mathlib 中的一个引理，位于命名空间 `Metric`。
形式化陈述：closedBall_zero' (x : α) : closedBall x 0 = closure {x}
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.mem_closure_iff`：mem_closure_iff {s : Set α} {a : α} : a in closu
re s ↔ forall ε > 0, exists b in s, dist a b < ε
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.mem_closedBall`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x y 
: α} {ε : ℝ}, y ∈ Metric.closedBall x ε ↔ dist y x ≤ ε
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
· 使用引理 `Metric.isClosed_closedBall`：isClosed_closedBall : IsClosed (closedBall x
 ε)
-/
lemma closedBall_zero' (x : α) : closedBall x 0 = closure {x} :=
  Subset.antisymm
    (fun _y hy =>
      mem_closure_iff.2 fun _ε ε0 => ⟨x, mem_singleton x, (mem_closedBall.1 hy).trans_lt ε0⟩)
    (closure_minimal (singleton_subset_iff.2 (dist_self x).le) isClosed_closedBall)
/-
**Metric.eventually_isCompact_closedBall** 是 Mathlib 中的一个引理，位于命名空间 `Metric`。
形式化陈述：eventually_isCompact_closedBall [WeaklyLocallyCompactSpace α] (x : α) : fo
rallᶠ r in 𝓝 (0 : Real), IsCompact (closedBall x r)
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WeaklyLocallyCompactSpace.exists_compact_mem_nhds`：∀ {X : Type u_3} {ins
t : TopologicalSpace X} [self : WeaklyLocallyCompactSpace X] (x : X), ∃ s, IsCom
pact s ∧ s ∈ nhds x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用引理 `eventually_closedBall_subset`：eventually_closedBall_subset {x : α} {u : 
Set α} (hu : u in 𝓝 x) : forallᶠ r in 𝓝 (0 : Real), closedBall x r subseteq u
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `IsCompact.of_isClosed_subset`：IsCompact.of_isClosed_subset (hs : IsCompa
ct s) (ht : IsClosed t) (h : t subseteq s) : IsCompact t
· 使用引理 `Metric.isClosed_closedBall`：isClosed_closedBall : IsClosed (closedBall x
 ε)
-/
lemma eventually_isCompact_closedBall [WeaklyLocallyCompactSpace α] (x : α) :
    ∀ᶠ r in 𝓝 (0 : ℝ), IsCompact (closedBall x r) := by
  rcases exists_compact_mem_nhds x with ⟨s, s_compact, hs⟩
  filter_upwards [eventually_closedBall_subset hs] with r hr
  exact IsCompact.of_isClosed_subset s_compact isClosed_closedBall hr
/-
**Metric.exists_isCompact_closedBall** 是 Mathlib 中的一个引理，位于命名空间 `Metric`。
形式化陈述：exists_isCompact_closedBall [WeaklyLocallyCompactSpace α] (x : α) : exists
 r, 0 < r ∧ IsCompact (closedBall x r)
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eventually_nhdsWithin_of_eventually_nhds`：eventually_nhdsWithin_of_event
ually_nhds {s : Set α} {a : α} {p : α -> Prop} (h : forallᶠ x in 𝓝 a, p x) : for
allᶠ x in 𝓝[s] a, p x
· 使用引理 `Metric.eventually_isCompact_closedBall`：eventually_isCompact_closedBall 
[WeaklyLocallyCompactSpace α] (x : α) : forallᶠ r in 𝓝 (0 : Real), IsCompact (cl
osedBall x r)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
-/
lemma exists_isCompact_closedBall [WeaklyLocallyCompactSpace α] (x : α) :
    ∃ r, 0 < r ∧ IsCompact (closedBall x r) := by
  have : ∀ᶠ r in 𝓝[>] 0, IsCompact (closedBall x r) :=
    eventually_nhdsWithin_of_eventually_nhds (eventually_isCompact_closedBall x)
  simpa only [and_comm] using (this.and self_mem_nhdsWithin).exists
/-
**Metric.biInter_gt_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：biInter_gt_closedBall (x : α) (r : Real) : ⋂ r' > r, closedBall x r' = clo
sedBall x r
参数：x : α；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem biInter_gt_closedBall (x : α) (r : ℝ) : ⋂ r' > r, closedBall x r' = closedBall x r := by
  ext
  simp [forall_gt_imp_ge_iff_le_of_dense]
/-
**Metric.biInter_gt_ball** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：biInter_gt_ball (x : α) (r : Real) : ⋂ r' > r, ball x r' = closedBall x r
参数：x : α；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem biInter_gt_ball (x : α) (r : ℝ) : ⋂ r' > r, ball x r' = closedBall x r := by
  ext
  simp [forall_gt_iff_le]
/-
**Metric.biUnion_lt_ball** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：biUnion_lt_ball (x : α) (r : Real) : ⋃ r' < r, ball x r' = ball x r
参数：x : α；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem biUnion_lt_ball (x : α) (r : ℝ) : ⋃ r' < r, ball x r' = ball x r := by
  ext
  rw [← not_iff_not]
  simp [forall_lt_imp_le_iff_le_of_dense]
/-
**Metric.biUnion_lt_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：biUnion_lt_closedBall (x : α) (r : Real) : ⋃ r' < r, closedBall x r' = bal
l x r
参数：x : α；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem biUnion_lt_closedBall (x : α) (r : ℝ) : ⋃ r' < r, closedBall x r' = ball x r := by
  ext
  rw [← not_iff_not]
  simp [forall_lt_iff_le]

end Metric

/-
**lebesgue_number_lemma_of_metric** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lebesgue_number_lemma_of_metric {s : Set α} {ι : Sort*} {c : ι -> Set α} (
hs : IsCompact s) (hc₁ : forall i, IsOpen (c i)) (hc₂ : s subseteq ⋃ i, c i) : e
xists δ > 0, forall x in s, exists i, ball x δ subseteq c i
参数：hs : IsCompact s；hc₁ : forall i, IsOpen (c i)；hc₂ : s subseteq ⋃ i, c i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `Filter.HasBasis.lebesgue_number_lemma`：∀ {α : Type ua} [inst : UniformSp
ace α] {K : Set α} {ι' : Sort u_2} {ι : Sort u_3} {p : ι' → Prop}   {V : ι' → Se
t (α × α)} {U : ι → Set α},…
· 使用定理 `Metric.uniformity_basis_dist`：uniformity_basis_dist : (𝓤 α).HasBasis (fu
n ε : Real => 0 < ε) fun ε => { p : α × α | dist p.1 p.2 < ε }
-/
theorem lebesgue_number_lemma_of_metric {s : Set α} {ι : Sort*} {c : ι → Set α} (hs : IsCompact s)
    (hc₁ : ∀ i, IsOpen (c i)) (hc₂ : s ⊆ ⋃ i, c i) : ∃ δ > 0, ∀ x ∈ s, ∃ i, ball x δ ⊆ c i := by
  simpa only [ball, UniformSpace.ball, preimage_ofPred_eq, dist_comm]
    using uniformity_basis_dist.lebesgue_number_lemma hs hc₁ hc₂
/-
**lebesgue_number_lemma_of_metric_sUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lebesgue_number_lemma_of_metric_sUnion {s : Set α} {c : Set (Set α)} (hs :
 IsCompact s) (hc₁ : forall t in c, IsOpen t) (hc₂ : s subseteq ⋃₀ c) : exists δ
 > 0, forall x in s, exists t in c, ball x δ subseteq t
参数：Set α；hs : IsCompact s；hc₁ : forall t in c, IsOpen t；hc₂ : s subseteq ⋃₀ c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `lebesgue_number_lemma_of_metric`：lebesgue_number_lemma_of_metric {s : Se
t α} {ι : Sort*} {c : ι -> Set α} (hs : IsCompact s) (hc₁ : forall i, IsOpen (c 
i)) (hc₂ : s subseteq…
· 使用定理 `Set.sUnion_eq_iUnion`：sUnion_eq_iUnion {s : Set (Set α)} : ⋃₀ s = ⋃ i : 
s, i
-/
theorem lebesgue_number_lemma_of_metric_sUnion {s : Set α} {c : Set (Set α)} (hs : IsCompact s)
    (hc₁ : ∀ t ∈ c, IsOpen t) (hc₂ : s ⊆ ⋃₀ c) : ∃ δ > 0, ∀ x ∈ s, ∃ t ∈ c, ball x δ ⊆ t := by
  rw [sUnion_eq_iUnion] at hc₂; simpa using lebesgue_number_lemma_of_metric hs (by simpa) hc₂
