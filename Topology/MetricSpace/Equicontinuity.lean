/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Topology.UniformSpace.Equicontinuity
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Equicontinuity in metric spaces

This file contains various facts about (uniform) equicontinuity in metric spaces. Most
importantly, we prove the usual characterization of equicontinuity of `F` at `x₀` in the case of
(pseudo) metric spaces: `∀ ε > 0, ∃ δ > 0, ∀ x, dist x x₀ < δ → ∀ i, dist (F i x₀) (F i x) < ε`,
and we prove that functions sharing a common (local or global) continuity modulus are
(locally or uniformly) equicontinuous.

## Main statements

* `Metric.equicontinuousAt_iff`: characterization of equicontinuity for families of functions
  between (pseudo) metric spaces.
* `Metric.equicontinuousAt_of_continuity_modulus`: convenient way to prove equicontinuity at a
  point of a family of functions to a (pseudo) metric space by showing that they share a common
  *local* continuity modulus.
* `Metric.uniformEquicontinuous_of_continuity_modulus`: convenient way to prove uniform
  equicontinuity of a family of functions to a (pseudo) metric space by showing that they share a
  common *global* continuity modulus.

## Tags

equicontinuity, continuity modulus
-/

public section


open Filter Topology Uniformity

variable {α β ι : Type*} [PseudoMetricSpace α]

namespace Metric

/-- Characterization of equicontinuity for families of functions taking values in a (pseudo) metric
space. -/
/-
**Metric.equicontinuousAt_iff_right** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：equicontinuousAt_iff_right {ι : Type*} [TopologicalSpace β] {F : ι -> β ->
 α} {x₀ : β} : EquicontinuousAt F x₀ ↔ forall ε > 0, forallᶠ x in 𝓝 x₀, forall i
, dist (F i x₀) (F i x) < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.equicontinuousAt_iff_right`：Filter.HasBasis.equicontinuo
usAt_iff_right {p : κ -> Prop} {s : κ -> Set (α × α)} {F : ι -> X -> α} {x₀ : X}
 (hα : (𝓤 α).HasBasis p s) : Equ…
· 使用定理 `Metric.uniformity_basis_dist`：uniformity_basis_dist : (𝓤 α).HasBasis (fu
n ε : Real => 0 < ε) fun ε => { p : α × α | dist p.1 p.2 < ε }

--- 原说明 ---
Characterization of equicontinuity for families of functions taking values in a 
(pseudo) metric
space.
-/
theorem equicontinuousAt_iff_right {ι : Type*} [TopologicalSpace β] {F : ι → β → α} {x₀ : β} :
    EquicontinuousAt F x₀ ↔ ∀ ε > 0, ∀ᶠ x in 𝓝 x₀, ∀ i, dist (F i x₀) (F i x) < ε :=
  uniformity_basis_dist.equicontinuousAt_iff_right

/-- Characterization of equicontinuity for families of functions between (pseudo) metric spaces. -/
/-
**Metric.equicontinuousAt_iff** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：equicontinuousAt_iff {ι : Type*} [PseudoMetricSpace β] {F : ι -> β -> α} {
x₀ : β} : EquicontinuousAt F x₀ ↔ forall ε > 0, exists δ > 0, forall x, dist x x
₀ < δ -> forall i, dist (F i x₀) (F i x) < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.equicontinuousAt_iff`：Filter.HasBasis.equicontinuousAt_i
ff {κ₁ κ₂ : Type*} {p₁ : κ₁ -> Prop} {s₁ : κ₁ -> Set X} {p₂ : κ₂ -> Prop} {s₂ : 
κ₂ -> Set (α × α)} {F : ι …
· 使用定理 `Metric.nhds_basis_ball`：nhds_basis_ball : (𝓝 x).HasBasis (0 < ·) (ball x
)
· 使用定理 `Metric.uniformity_basis_dist`：uniformity_basis_dist : (𝓤 α).HasBasis (fu
n ε : Real => 0 < ε) fun ε => { p : α × α | dist p.1 p.2 < ε }

--- 原说明 ---
Characterization of equicontinuity for families of functions between (pseudo) me
tric spaces.
-/
theorem equicontinuousAt_iff {ι : Type*} [PseudoMetricSpace β] {F : ι → β → α} {x₀ : β} :
    EquicontinuousAt F x₀ ↔ ∀ ε > 0, ∃ δ > 0, ∀ x, dist x x₀ < δ → ∀ i, dist (F i x₀) (F i x) < ε :=
  nhds_basis_ball.equicontinuousAt_iff uniformity_basis_dist

/-- Reformulation of `equicontinuousAt_iff_pair` for families of functions taking values in a
(pseudo) metric space. -/
/-
**Metric.equicontinuousAt_iff_pair** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : PseudoMetricSpace α] {ι : Type u_4
} [inst_1 : TopologicalSpace β]   {F : ι → β → α} {x₀ : β},   EquicontinuousAt F
 x₀ ↔ ∀ ε > 0, ∃ U ∈ nhds x₀, ∀ x ∈ U, ∀ x' ∈ U, ∀ (i : ι), dist (F i x) (F i x'
) < ε
参数：i : ι；F i x；F i x'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `equicontinuousAt_iff_pair`：equicontinuousAt_iff_pair {F : ι -> X -> α} {
x₀ : X} : EquicontinuousAt F x₀ ↔ forall U in 𝓤 α, exists V in 𝓝 x₀, forall x in
 V, forall y in…
· 使用定理 `Metric.dist_mem_uniformity`：dist_mem_uniformity {ε : Real} (ε0 : 0 < ε) 
: { p : α × α | dist p.1 p.2 < ε } in 𝓤 α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.mem_uniformity_dist`：mem_uniformity_dist {s : Set (α × α)} : s in
 𝓤 α ↔ exists ε > 0, forall ⦃a b : α⦄, dist a b < ε -> (a, b) in s
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `And.imp_right`：∀ {a b c : Prop}, (a → b) → c ∧ a → c ∧ b

--- 原说明 ---
Reformulation of `equicontinuousAt_iff_pair` for families of functions taking va
lues in a
(pseudo) metric space.
-/
protected theorem equicontinuousAt_iff_pair {ι : Type*} [TopologicalSpace β] {F : ι → β → α}
    {x₀ : β} :
    EquicontinuousAt F x₀ ↔
      ∀ ε > 0, ∃ U ∈ 𝓝 x₀, ∀ x ∈ U, ∀ x' ∈ U, ∀ i, dist (F i x) (F i x') < ε := by
  rw [equicontinuousAt_iff_pair]
  constructor <;> intro H
  · intro ε hε
    exact H _ (dist_mem_uniformity hε)
  · intro U hU
    rcases mem_uniformity_dist.mp hU with ⟨ε, hε, hεU⟩
    refine Exists.imp (fun V => And.imp_right fun h => ?_) (H _ hε)
    exact fun x hx x' hx' i => hεU (h _ hx _ hx' i)

/-- Characterization of uniform equicontinuity for families of functions taking values in a
(pseudo) metric space. -/
/-
**Metric.uniformEquicontinuous_iff_right** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：uniformEquicontinuous_iff_right {ι : Type*} [UniformSpace β] {F : ι -> β -
> α} : UniformEquicontinuous F ↔ forall ε > 0, forallᶠ xy : β × β in 𝓤 β, forall
 i, dist (F i xy.1) (F i xy.2) < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.uniformEquicontinuous_iff_right`：Filter.HasBasis.uniform
Equicontinuous_iff_right {p : κ -> Prop} {s : κ -> Set (α × α)} {F : ι -> β -> α
} (hα : (𝓤 α).HasBasis p s) : Uniform…
· 使用定理 `Metric.uniformity_basis_dist`：uniformity_basis_dist : (𝓤 α).HasBasis (fu
n ε : Real => 0 < ε) fun ε => { p : α × α | dist p.1 p.2 < ε }

--- 原说明 ---
Characterization of uniform equicontinuity for families of functions taking valu
es in a
(pseudo) metric space.
-/
theorem uniformEquicontinuous_iff_right {ι : Type*} [UniformSpace β] {F : ι → β → α} :
    UniformEquicontinuous F ↔ ∀ ε > 0, ∀ᶠ xy : β × β in 𝓤 β, ∀ i, dist (F i xy.1) (F i xy.2) < ε :=
  uniformity_basis_dist.uniformEquicontinuous_iff_right

/-- Characterization of uniform equicontinuity for families of functions between
(pseudo) metric spaces. -/
/-
**Metric.uniformEquicontinuous_iff** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：uniformEquicontinuous_iff {ι : Type*} [PseudoMetricSpace β] {F : ι -> β ->
 α} : UniformEquicontinuous F ↔ forall ε > 0, exists δ > 0, forall x y, dist x y
 < δ -> forall i, dist (F i x) (F i y) < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.uniformEquicontinuous_iff`：Filter.HasBasis.uniformEquico
ntinuous_iff {κ₁ κ₂ : Type*} {p₁ : κ₁ -> Prop} {s₁ : κ₁ -> Set (β × β)} {p₂ : κ₂
 -> Prop} {s₂ : κ₂ -> Set (α × …
· 使用定理 `Metric.uniformity_basis_dist`：uniformity_basis_dist : (𝓤 α).HasBasis (fu
n ε : Real => 0 < ε) fun ε => { p : α × α | dist p.1 p.2 < ε }

--- 原说明 ---
Characterization of uniform equicontinuity for families of functions between
(pseudo) metric spaces.
-/
theorem uniformEquicontinuous_iff {ι : Type*} [PseudoMetricSpace β] {F : ι → β → α} :
    UniformEquicontinuous F ↔
      ∀ ε > 0, ∃ δ > 0, ∀ x y, dist x y < δ → ∀ i, dist (F i x) (F i y) < ε :=
  uniformity_basis_dist.uniformEquicontinuous_iff uniformity_basis_dist

/-- For a family of functions to a (pseudo) metric spaces, a convenient way to prove
equicontinuity at a point is to show that all of the functions share a common *local* continuity
modulus. -/
/-
**Metric.equicontinuousAt_of_continuity_modulus** 是 Mathlib 中的一个定理，位于命名空间 `Metri
c`。
形式化陈述：equicontinuousAt_of_continuity_modulus {ι : Type*} [TopologicalSpace β] {x
₀ : β} (b : β -> Real) (b_lim : Tendsto b (𝓝 x₀) (𝓝 0)) (F : ι -> β -> α) (H : f
orallᶠ x in 𝓝 x₀, forall i, dist (F i x₀) (F i x) <= b x) : EquicontinuousAt F x
₀
参数：b : β -> Real；b_lim : Tendsto b (𝓝 x₀) (𝓝 0)；F : ι -> β -> α；H : forallᶠ x in
 𝓝 x₀, forall i, dist (F i x₀) (F i x) <= b x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.equicontinuousAt_iff_right`：equicontinuousAt_iff_right {ι : Type*
} [TopologicalSpace β] {F : ι -> β -> α} {x₀ : β} : EquicontinuousAt F x₀ ↔ fora
ll ε > 0, forallᶠ x in …
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Iio_mem_nhds`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Linea
rOrder α] [ClosedIciTopology α] {a b : α},   b < a → Set.Iio a ∈ nhds b
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c

--- 原说明 ---
For a family of functions to a (pseudo) metric spaces, a convenient way to prove
equicontinuity at a point is to show that all of the functions share a common *l
ocal* continuity
modulus.
-/
theorem equicontinuousAt_of_continuity_modulus {ι : Type*} [TopologicalSpace β] {x₀ : β}
    (b : β → ℝ) (b_lim : Tendsto b (𝓝 x₀) (𝓝 0)) (F : ι → β → α)
    (H : ∀ᶠ x in 𝓝 x₀, ∀ i, dist (F i x₀) (F i x) ≤ b x) : EquicontinuousAt F x₀ := by
  rw [Metric.equicontinuousAt_iff_right]
  intro ε ε0
  filter_upwards [b_lim (Iio_mem_nhds ε0), H] using fun x hx₁ hx₂ i => (hx₂ i).trans_lt hx₁

/-- For a family of functions between (pseudo) metric spaces, a convenient way to prove
uniform equicontinuity is to show that all of the functions share a common *global* continuity
modulus. -/
/-
**Metric.uniformEquicontinuous_of_continuity_modulus** 是 Mathlib 中的一个定理，位于命名空间 `
Metric`。
形式化陈述：uniformEquicontinuous_of_continuity_modulus {ι : Type*} [PseudoMetricSpace
 β] (b : Real -> Real) (b_lim : Tendsto b (𝓝 0) (𝓝 0)) (F : ι -> β -> α) (H : fo
rall (x y : β) (i), dist (F i x) (F i y) <= b (dist x y)) : UniformEquicontinuou
s F
参数：b : Real -> Real；b_lim : Tendsto b (𝓝 0) (𝓝 0)；F : ι -> β -> α；H : forall (x 
y : β) (i), dist (F i x) (F i y) <= b (dist x y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.uniformEquicontinuous_iff`：uniformEquicontinuous_iff {ι : Type*} 
[PseudoMetricSpace β] {F : ι -> β -> α} : UniformEquicontinuous F ↔ forall ε > 0
, exists δ > 0, forall…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.tendsto_nhds_nhds`：tendsto_nhds_nhds [PseudoMetricSpace β] {f : α
 -> β} {a b} : Tendsto f (𝓝 a) (𝓝 b) ↔ forall ε > 0, exists δ > 0, forall ⦃x : α
⦄, dist x a < …
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
· 使用定理 `AddGroup.toOrderedSub`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LE
 α] [AddRightMono α], OrderedSub α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `abs_dist`：∀ {α : Type u} [inst : PseudoMetricSpace α] {a b : α}, |dist a
 b| = dist a b

--- 原说明 ---
For a family of functions between (pseudo) metric spaces, a convenient way to pr
ove
uniform equicontinuity is to show that all of the functions share a common *glob
al* continuity
modulus.
-/
theorem uniformEquicontinuous_of_continuity_modulus {ι : Type*} [PseudoMetricSpace β] (b : ℝ → ℝ)
    (b_lim : Tendsto b (𝓝 0) (𝓝 0)) (F : ι → β → α)
    (H : ∀ (x y : β) (i), dist (F i x) (F i y) ≤ b (dist x y)) : UniformEquicontinuous F := by
  rw [Metric.uniformEquicontinuous_iff]
  intro ε ε0
  rcases tendsto_nhds_nhds.1 b_lim ε ε0 with ⟨δ, δ0, hδ⟩
  refine ⟨δ, δ0, fun x y hxy i => ?_⟩
  calc
    dist (F i x) (F i y) ≤ b (dist x y) := H x y i
    _ ≤ |b (dist x y)| := le_abs_self _
    _ = dist (b (dist x y)) 0 := by simp [Real.dist_eq]
    _ < ε := hδ (by simpa only [Real.dist_eq, tsub_zero, abs_dist] using hxy)

/-- For a family of functions between (pseudo) metric spaces, a convenient way to prove
equicontinuity is to show that all of the functions share a common *global* continuity modulus. -/
/-
**Metric.equicontinuous_of_continuity_modulus** 是 Mathlib 中的一个定理，位于命名空间 `Metric`
。
形式化陈述：equicontinuous_of_continuity_modulus {ι : Type*} [PseudoMetricSpace β] (b 
: Real -> Real) (b_lim : Tendsto b (𝓝 0) (𝓝 0)) (F : ι -> β -> α) (H : forall (x
 y : β) (i), dist (F i x) (F i y) <= b (dist x y)) : Equicontinuous F
参数：b : Real -> Real；b_lim : Tendsto b (𝓝 0) (𝓝 0)；F : ι -> β -> α；H : forall (x 
y : β) (i), dist (F i x) (F i y) <= b (dist x y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformEquicontinuous.equicontinuous`：UniformEquicontinuous.equicontinuo
us {F : ι -> β -> α} (h : UniformEquicontinuous F) : Equicontinuous F
· 使用定理 `Metric.uniformEquicontinuous_of_continuity_modulus`：uniformEquicontinuou
s_of_continuity_modulus {ι : Type*} [PseudoMetricSpace β] (b : Real -> Real) (b_
lim : Tendsto b (𝓝 0) (𝓝 0)) (F : ι -> β…

--- 原说明 ---
For a family of functions between (pseudo) metric spaces, a convenient way to pr
ove
equicontinuity is to show that all of the functions share a common *global* cont
inuity modulus.
-/
theorem equicontinuous_of_continuity_modulus {ι : Type*} [PseudoMetricSpace β] (b : ℝ → ℝ)
    (b_lim : Tendsto b (𝓝 0) (𝓝 0)) (F : ι → β → α)
    (H : ∀ (x y : β) (i), dist (F i x) (F i y) ≤ b (dist x y)) : Equicontinuous F :=
  (uniformEquicontinuous_of_continuity_modulus b b_lim F H).equicontinuous

end Metric

