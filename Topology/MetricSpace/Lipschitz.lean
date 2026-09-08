/-
Copyright (c) 2018 Rohan Mitta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Mitta, Kevin Buzzard, Alistair Tucker, Johannes Hölzl, Yury Kudryashov
-/
module

public import Mathlib.Order.Interval.Set.ProjIcc
public import Mathlib.Topology.Bornology.Hom
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Bounded

/-!
# Lipschitz continuous functions

A map `f : α → β` between two (extended) metric spaces is called *Lipschitz continuous*
with constant `K ≥ 0` if for all `x, y` we have `edist (f x) (f y) ≤ K * edist x y`.
For a metric space, the latter inequality is equivalent to `dist (f x) (f y) ≤ K * dist x y`.
There is also a version asserting this inequality only for `x` and `y` in some set `s`.
Finally, `f : α → β` is called *locally Lipschitz continuous* if each `x : α` has a neighbourhood
on which `f` is Lipschitz continuous (with some constant).

In this file we specialize various facts about Lipschitz continuous maps
to the case of (pseudo) metric spaces.

## Implementation notes

The parameter `K` has type `ℝ≥0`. This way we avoid conjunction in the definition and have
coercions both to `ℝ` and `ℝ≥0∞`. Constructors whose names end with `'` take `K : ℝ` as an
argument, and return `LipschitzWith (Real.toNNReal K) f`.
-/

@[expose] public section

assert_not_exists Module.Basis Ideal ContinuousMul

universe u v w x

open Filter Function Set Topology NNReal ENNReal Bornology

variable {α : Type u} {β : Type v} {γ : Type w} {ι : Type x}

/-
**lipschitzWith_iff_dist_le_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lipschitzWith_iff_dist_le_mul [PseudoMetricSpace α] [PseudoMetricSpace β] 
{K : Real>=0} {f : α -> β} : LipschitzWith K f ↔ forall x y, dist (f x) (f y) <=
 K * dist x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `edist_nndist`：edist_nndist (x y : α) : edist x y = nndist x y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lipschitzWith_iff_dist_le_mul [PseudoMetricSpace α] [PseudoMetricSpace β] {K : ℝ≥0}
    {f : α → β} : LipschitzWith K f ↔ ∀ x y, dist (f x) (f y) ≤ K * dist x y := by
  simp only [LipschitzWith, edist_nndist, dist_nndist]
  norm_cast

alias ⟨LipschitzWith.dist_le_mul, LipschitzWith.of_dist_le_mul⟩ := lipschitzWith_iff_dist_le_mul
/-
**lipschitzOnWith_iff_dist_le_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lipschitzOnWith_iff_dist_le_mul [PseudoMetricSpace α] [PseudoMetricSpace β
] {K : Real>=0} {s : Set α} {f : α -> β} : LipschitzOnWith K f s ↔ forall x in s
, forall y in s, dist (f x) (f y) <= K * dist x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `edist_nndist`：edist_nndist (x y : α) : edist x y = nndist x y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lipschitzOnWith_iff_dist_le_mul [PseudoMetricSpace α] [PseudoMetricSpace β] {K : ℝ≥0}
    {s : Set α} {f : α → β} :
    LipschitzOnWith K f s ↔ ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) ≤ K * dist x y := by
  simp only [LipschitzOnWith, edist_nndist, dist_nndist]
  norm_cast

alias ⟨LipschitzOnWith.dist_le_mul, LipschitzOnWith.of_dist_le_mul⟩ :=
  lipschitzOnWith_iff_dist_le_mul

namespace LipschitzWith

section Metric

variable [PseudoMetricSpace α] [PseudoMetricSpace β] [PseudoMetricSpace γ] {K : ℝ≥0} {f : α → β}
  {x y : α} {r : ℝ}

/-
**LipschitzWith.of_dist_le'** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : PseudoMetricSpace α] [inst_1 : PseudoM
etricSpace β] {f : α → β} {K : ℝ},   (∀ (x y : α), dist (f x) (f y) ≤ K * dist x
 y) → LipschitzWith K.toNNReal f
参数：∀ (x y : α), dist (f x) (f y) ≤ K * dist x y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.of_dist_le_mul`：∀ {α : Type u} {β : Type v} [inst : Pseudo
MetricSpace α] [inst_1 : PseudoMetricSpace β] {K : NNReal} {f : α → β},   (∀ (x 
y : α), dist (f x)…
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `Real.le_coe_toNNReal`：∀ (r : ℝ), r ≤ ↑r.toNNReal
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
-/
protected theorem of_dist_le' {K : ℝ} (h : ∀ x y, dist (f x) (f y) ≤ K * dist x y) :
    LipschitzWith (Real.toNNReal K) f :=
  of_dist_le_mul fun x y =>
    le_trans (h x y) <| by gcongr; apply Real.le_coe_toNNReal
/-
**LipschitzWith.mk_one** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : PseudoMetricSpace α] [inst_1 : PseudoM
etricSpace β] {f : α → β},   (∀ (x y : α), dist (f x) (f y) ≤ dist x y) → Lipsch
itzWith 1 f
参数：∀ (x y : α), dist (f x) (f y) ≤ dist x y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.of_dist_le_mul`：∀ {α : Type u} {β : Type v} [inst : Pseudo
MetricSpace α] [inst_1 : PseudoMetricSpace β] {K : NNReal} {f : α → β},   (∀ (x 
y : α), dist (f x)…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
protected theorem mk_one (h : ∀ x y, dist (f x) (f y) ≤ dist x y) : LipschitzWith 1 f :=
  of_dist_le_mul <| by simpa only [NNReal.coe_one, one_mul] using h

/-- For functions to `ℝ`, it suffices to prove `f x ≤ f y + K * dist x y`; this version
doesn't assume `0≤K`. -/
/-
**LipschitzWith.of_le_add_mul'** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：∀ {α : Type u} [inst : PseudoMetricSpace α] {f : α → ℝ} (K : ℝ),   (∀ (x y
 : α), f x ≤ f y + K * dist x y) → LipschitzWith K.toNNReal f
参数：K : ℝ；∀ (x y : α), f x ≤ f y + K * dist x y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_le_iff_le_add'`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : LE 
α] [AddLeftMono α] {a b c : α}, a - b ≤ c ↔ a ≤ b + c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LipschitzWith.of_dist_le'`：∀ {α : Type u} {β : Type v} [inst : PseudoMet
ricSpace α] [inst_1 : PseudoMetricSpace β] {f : α → β} {K : ℝ},   (∀ (x y : α), 
dist (f x) (f y…
· 使用定理 `abs_sub_le_iff`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : Linea
rOrder G] [IsOrderedAddMonoid G] {a b c : G},   |a - b| ≤ c ↔ a - b ≤ c ∧ b - a 
≤ c
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x

--- 原说明 ---
For functions to `ℝ`, it suffices to prove `f x ≤ f y + K * dist x y`; this vers
ion
doesn't assume `0≤K`.
-/
protected theorem of_le_add_mul' {f : α → ℝ} (K : ℝ) (h : ∀ x y, f x ≤ f y + K * dist x y) :
    LipschitzWith (Real.toNNReal K) f :=
  have I : ∀ x y, f x - f y ≤ K * dist x y := fun x y => sub_le_iff_le_add'.2 (h x y)
  LipschitzWith.of_dist_le' fun x y => abs_sub_le_iff.2 ⟨I x y, dist_comm y x ▸ I y x⟩

/-- For functions to `ℝ`, it suffices to prove `f x ≤ f y + K * dist x y`; this version
assumes `0≤K`. -/
/-
**LipschitzWith.of_le_add_mul** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：∀ {α : Type u} [inst : PseudoMetricSpace α] {f : α → ℝ} (K : NNReal),   (∀
 (x y : α), f x ≤ f y + ↑K * dist x y) → LipschitzWith K f
参数：K : NNReal；∀ (x y : α), f x ≤ f y + ↑K * dist x y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.toNNReal_coe`：∀ {r : NNReal}, (↑r).toNNReal = r
· 使用定理 `LipschitzWith.of_le_add_mul'`：∀ {α : Type u} [inst : PseudoMetricSpace α
] {f : α → ℝ} (K : ℝ),   (∀ (x y : α), f x ≤ f y + K * dist x y) → LipschitzWith
 K.toNNReal f

--- 原说明 ---
For functions to `ℝ`, it suffices to prove `f x ≤ f y + K * dist x y`; this vers
ion
assumes `0≤K`.
-/
protected theorem of_le_add_mul {f : α → ℝ} (K : ℝ≥0) (h : ∀ x y, f x ≤ f y + K * dist x y) :
    LipschitzWith K f := by simpa only [Real.toNNReal_coe] using LipschitzWith.of_le_add_mul' K h
/-
**LipschitzWith.of_le_add** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：∀ {α : Type u} [inst : PseudoMetricSpace α] {f : α → ℝ}, (∀ (x y : α), f x
 ≤ f y + dist x y) → LipschitzWith 1 f
参数：∀ (x y : α), f x ≤ f y + dist x y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.of_le_add_mul`：∀ {α : Type u} [inst : PseudoMetricSpace α]
 {f : α → ℝ} (K : NNReal),   (∀ (x y : α), f x ≤ f y + ↑K * dist x y) → Lipschit
zWith K f
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
protected theorem of_le_add {f : α → ℝ} (h : ∀ x y, f x ≤ f y + dist x y) : LipschitzWith 1 f :=
  LipschitzWith.of_le_add_mul 1 <| by simpa only [NNReal.coe_one, one_mul]
/-
**LipschitzWith.le_add_mul** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：∀ {α : Type u} [inst : PseudoMetricSpace α] {f : α → ℝ} {K : NNReal},   Li
pschitzWith K f → ∀ (x y : α), f x ≤ f y + ↑K * dist x y
参数：x y : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_le_iff_le_add'`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : LE 
α] [AddLeftMono α] {a b c : α}, a - b ≤ c ↔ a ≤ b + c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|
· 使用定理 `LipschitzWith.dist_le_mul`：∀ {α : Type u} {β : Type v} [inst : PseudoMet
ricSpace α] [inst_1 : PseudoMetricSpace β] {K : NNReal} {f : α → β},   Lipschitz
With K f → ∀ (x…
-/
protected theorem le_add_mul {f : α → ℝ} {K : ℝ≥0} (h : LipschitzWith K f) (x y) :
    f x ≤ f y + K * dist x y :=
  sub_le_iff_le_add'.1 <| le_trans (le_abs_self _) <| h.dist_le_mul x y
/-
**LipschitzWith.iff_le_add_mul** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：∀ {α : Type u} [inst : PseudoMetricSpace α] {f : α → ℝ} {K : NNReal},   Li
pschitzWith K f ↔ ∀ (x y : α), f x ≤ f y + ↑K * dist x y
参数：x y : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.le_add_mul`：∀ {α : Type u} [inst : PseudoMetricSpace α] {f
 : α → ℝ} {K : NNReal},   LipschitzWith K f → ∀ (x y : α), f x ≤ f y + ↑K * dist
 x y
· 使用定理 `LipschitzWith.of_le_add_mul`：∀ {α : Type u} [inst : PseudoMetricSpace α]
 {f : α → ℝ} (K : NNReal),   (∀ (x y : α), f x ≤ f y + ↑K * dist x y) → Lipschit
zWith K f
-/
protected theorem iff_le_add_mul {f : α → ℝ} {K : ℝ≥0} :
    LipschitzWith K f ↔ ∀ x y, f x ≤ f y + K * dist x y :=
  ⟨LipschitzWith.le_add_mul, LipschitzWith.of_le_add_mul K⟩
/-
**LipschitzWith.nndist_le** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：nndist_le (hf : LipschitzWith K f) (x y : α) : nndist (f x) (f y) <= K * n
ndist x y
参数：hf : LipschitzWith K f；x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.dist_le_mul`：∀ {α : Type u} {β : Type v} [inst : PseudoMet
ricSpace α] [inst_1 : PseudoMetricSpace β] {K : NNReal} {f : α → β},   Lipschitz
With K f → ∀ (x…
-/
theorem nndist_le (hf : LipschitzWith K f) (x y : α) : nndist (f x) (f y) ≤ K * nndist x y :=
  hf.dist_le_mul x y
/-
**LipschitzWith.dist_le_mul_of_le** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：dist_le_mul_of_le (hf : LipschitzWith K f) (hr : dist x y <= r) : dist (f 
x) (f y) <= K * r
参数：hf : LipschitzWith K f；hr : dist x y <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LipschitzWith.dist_le_mul`：∀ {α : Type u} {β : Type v} [inst : PseudoMet
ricSpace α] [inst_1 : PseudoMetricSpace β] {K : NNReal} {f : α → β},   Lipschitz
With K f → ∀ (x…
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
-/
theorem dist_le_mul_of_le (hf : LipschitzWith K f) (hr : dist x y ≤ r) : dist (f x) (f y) ≤ K * r :=
  (hf.dist_le_mul x y).trans <| by gcongr
/-
**LipschitzWith.mapsTo_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：mapsTo_closedBall (hf : LipschitzWith K f) (x : α) (r : Real) : MapsTo f (
Metric.closedBall x r) (Metric.closedBall (f x) (K * r))
参数：hf : LipschitzWith K f；x : α；r : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.dist_le_mul_of_le`：dist_le_mul_of_le (hf : LipschitzWith K
 f) (hr : dist x y <= r) : dist (f x) (f y) <= K * r
-/
theorem mapsTo_closedBall (hf : LipschitzWith K f) (x : α) (r : ℝ) :
    MapsTo f (Metric.closedBall x r) (Metric.closedBall (f x) (K * r)) := fun _y hy =>
  hf.dist_le_mul_of_le hy
/-
**LipschitzWith.dist_lt_mul_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：dist_lt_mul_of_lt (hf : LipschitzWith K f) (hK : K != 0) (hr : dist x y < 
r) : dist (f x) (f y) < K * r
参数：hf : LipschitzWith K f；hK : K != 0；hr : dist x y < r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `LipschitzWith.dist_le_mul`：∀ {α : Type u} {β : Type v} [inst : PseudoMet
ricSpace α] [inst_1 : PseudoMetricSpace β] {K : NNReal} {f : α → β},   Lipschitz
With K f → ∀ (x…
· 使用定理 `mul_lt_mul_of_pos_left`：mul_lt_mul_of_pos_left [PosMulStrictMono α] (hbc
 : b < c) (ha : 0 < a) : a * b < a * c
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Mathlib.Meta.Positivity.nnreal_coe_pos`：∀ {r : NNReal}, 0 < r → 0 < ↑r
· 使用定理 `lt_of_le_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `NNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd NNReal
-/
theorem dist_lt_mul_of_lt (hf : LipschitzWith K f) (hK : K ≠ 0) (hr : dist x y < r) :
    dist (f x) (f y) < K * r :=
  (hf.dist_le_mul x y).trans_lt <| by gcongr
/-
**LipschitzWith.mapsTo_ball** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：mapsTo_ball (hf : LipschitzWith K f) (hK : K != 0) (x : α) (r : Real) : Ma
psTo f (Metric.ball x r) (Metric.ball (f x) (K * r))
参数：hf : LipschitzWith K f；hK : K != 0；x : α；r : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.dist_lt_mul_of_lt`：dist_lt_mul_of_lt (hf : LipschitzWith K
 f) (hK : K != 0) (hr : dist x y < r) : dist (f x) (f y) < K * r
-/
theorem mapsTo_ball (hf : LipschitzWith K f) (hK : K ≠ 0) (x : α) (r : ℝ) :
    MapsTo f (Metric.ball x r) (Metric.ball (f x) (K * r)) := fun _y hy =>
  hf.dist_lt_mul_of_lt hK hy

/-- A Lipschitz continuous map is a locally bounded map. -/
/-
**LipschitzWith.toLocallyBoundedMap** 是 Mathlib 中的一个定义，位于命名空间 `LipschitzWith`。
形式化陈述：toLocallyBoundedMap (f : α -> β) (hf : LipschitzWith K f) : LocallyBounded
Map α β
参数：f : α -> β；hf : LipschitzWith K f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Lipschitz continuous map is a locally bounded map.
-/
def toLocallyBoundedMap (f : α → β) (hf : LipschitzWith K f) : LocallyBoundedMap α β :=
  LocallyBoundedMap.ofMapBounded f fun _s hs =>
    let ⟨C, hC⟩ := Metric.isBounded_iff.1 hs
    Metric.isBounded_iff.2 ⟨K * C, forall_mem_image.2 fun _x hx => forall_mem_image.2 fun _y hy =>
      hf.dist_le_mul_of_le (hC hx hy)⟩

@[simp]
/-
**LipschitzWith.coe_toLocallyBoundedMap** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith
`。
形式化陈述：coe_toLocallyBoundedMap (hf : LipschitzWith K f) : ⇑(hf.toLocallyBoundedMa
p f) = f
参数：hf : LipschitzWith K f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toLocallyBoundedMap (hf : LipschitzWith K f) : ⇑(hf.toLocallyBoundedMap f) = f :=
  rfl
/-
**LipschitzWith.comap_cobounded_le** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：comap_cobounded_le (hf : LipschitzWith K f) : comap f (Bornology.cobounded
 β) <= Bornology.cobounded α
参数：hf : LipschitzWith K f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LocallyBoundedMap.comap_cobounded_le'`：∀ {α : Type u_6} {β : Type u_7} [
inst : Bornology α] [inst_1 : Bornology β] (self : LocallyBoundedMap α β),   Fil
ter.comap self.toFun (Borno…
-/
theorem comap_cobounded_le (hf : LipschitzWith K f) :
    comap f (Bornology.cobounded β) ≤ Bornology.cobounded α :=
  (hf.toLocallyBoundedMap f).2

/-- The image of a bounded set under a Lipschitz map is bounded. -/
/-
**LipschitzWith.isBounded_image** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：isBounded_image (hf : LipschitzWith K f) {s : Set α} (hs : IsBounded s) : 
IsBounded (f '' s)
参数：hf : LipschitzWith K f；hs : IsBounded s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bornology.IsBounded.image`：Bornology.IsBounded.image [Bornology α] [Born
ology β] [LocallyBoundedMapClass F α β] (f : F) {s : Set α} (hs : IsBounded s) :
 IsBounded (f '…
· 使用定理 `LocallyBoundedMap.instLocallyBoundedMapClass`：∀ {α : Type u_2} {β : Type
 u_3} [inst : Bornology α] [inst_1 : Bornology β],   LocallyBoundedMapClass (Loc
allyBoundedMap α β) α β

--- 原说明 ---
The image of a bounded set under a Lipschitz map is bounded.
-/
theorem isBounded_image (hf : LipschitzWith K f) {s : Set α} (hs : IsBounded s) :
    IsBounded (f '' s) :=
  hs.image (toLocallyBoundedMap f hf)
/-
**LipschitzWith.diam_image_le** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：diam_image_le (hf : LipschitzWith K f) (s : Set α) (hs : IsBounded s) : Me
tric.diam (f '' s) <= K * Metric.diam s
参数：hf : LipschitzWith K f；s : Set α；hs : IsBounded s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.diam_le_of_forall_dist_le`：diam_le_of_forall_dist_le {C : Real} (
h₀ : 0 <= C) (h : forall x in s, forall y in s, dist x y <= C) : diam s <= C
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `Metric.diam_nonneg`：diam_nonneg : 0 <= diam s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_image`：forall_mem_image {f : α -> β} {s : Set α} {p : β -
> Prop} : (forall y in f '' s, p y) ↔ forall ⦃x⦄, x in s -> p (f x)
· 使用定理 `LipschitzWith.dist_le_mul_of_le`：dist_le_mul_of_le (hf : LipschitzWith K
 f) (hr : dist x y <= r) : dist (f x) (f y) <= K * r
· 使用定理 `Metric.dist_le_diam_of_mem`：dist_le_diam_of_mem (h : IsBounded s) (hx : 
x in s) (hy : y in s) : dist x y <= diam s
-/
theorem diam_image_le (hf : LipschitzWith K f) (s : Set α) (hs : IsBounded s) :
    Metric.diam (f '' s) ≤ K * Metric.diam s :=
  Metric.diam_le_of_forall_dist_le (mul_nonneg K.coe_nonneg Metric.diam_nonneg) <|
    forall_mem_image.2 fun _x hx =>
      forall_mem_image.2 fun _y hy => hf.dist_le_mul_of_le <| Metric.dist_le_diam_of_mem hs hx hy
/-
**LipschitzWith.dist_left** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：∀ {α : Type u} [inst : PseudoMetricSpace α] (y : α), LipschitzWith 1 fun x
 => dist x y
参数：y : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.mk_one`：∀ {α : Type u} {β : Type v} [inst : PseudoMetricSp
ace α] [inst_1 : PseudoMetricSpace β] {f : α → β},   (∀ (x y : α), dist (f x) (f
 y) ≤ dist…
· 使用定理 `dist_dist_dist_le_left`：dist_dist_dist_le_left (x y z : α) : dist (dist 
x z) (dist y z) <= dist x y
-/
protected theorem dist_left (y : α) : LipschitzWith 1 (dist · y) :=
  LipschitzWith.mk_one fun _ _ => dist_dist_dist_le_left _ _ _
/-
**LipschitzWith.dist_right** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：∀ {α : Type u} [inst : PseudoMetricSpace α] (x : α), LipschitzWith 1 (dist
 x)
参数：x : α；dist x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.of_le_add`：∀ {α : Type u} [inst : PseudoMetricSpace α] {f 
: α → ℝ}, (∀ (x y : α), f x ≤ f y + dist x y) → LipschitzWith 1 f
· 使用定理 `dist_triangle_right`：dist_triangle_right (x y z : α) : dist x y <= dist 
x z + dist y z
-/
protected theorem dist_right (x : α) : LipschitzWith 1 (dist x) :=
  LipschitzWith.of_le_add fun _ _ => dist_triangle_right _ _ _
/-
**LipschitzWith.dist** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：∀ {α : Type u} [inst : PseudoMetricSpace α], LipschitzWith 2 (Function.unc
urry dist)
参数：Function.uncurry dist。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_add_one_eq_two`：one_add_one_eq_two [AddMonoidWithOne R] : 1 + 1 = (2
 : R)
· 使用定理 `LipschitzWith.uncurry`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : 
PseudoEMetricSpace α] [inst_1 : PseudoEMetricSpace β]   [inst_2 : PseudoEMetricS
pace γ] {f …
· 使用定理 `LipschitzWith.dist_left`：∀ {α : Type u} [inst : PseudoMetricSpace α] (y 
: α), LipschitzWith 1 fun x => dist x y
· 使用定理 `LipschitzWith.dist_right`：∀ {α : Type u} [inst : PseudoMetricSpace α] (x
 : α), LipschitzWith 1 (dist x)
-/
protected theorem dist : LipschitzWith 2 (Function.uncurry <| @dist α _) := by
  rw [← one_add_one_eq_two]
  exact LipschitzWith.uncurry LipschitzWith.dist_left LipschitzWith.dist_right
/-
**LipschitzWith.dist_iterate_succ_le_geometric** 是 Mathlib 中的一个定理，位于命名空间 `Lipsch
itzWith`。
形式化陈述：dist_iterate_succ_le_geometric {f : α -> α} (hf : LipschitzWith K f) (x n)
 : dist (f^[n] x) (f^[n + 1] x) <= dist x (f x) * (K : Real) ^ n
参数：hf : LipschitzWith K f；x n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.iterate_succ`：iterate_succ (n : Nat) : f^[n.succ] = f^[n] ∘ f
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `LipschitzWith.dist_le_mul`：∀ {α : Type u} {β : Type v} [inst : PseudoMet
ricSpace α] [inst_1 : PseudoMetricSpace β] {K : NNReal} {f : α → β},   Lipschitz
With K f → ∀ (x…
· 使用定理 `LipschitzWith.iterate`：∀ {α : Type u} [inst : PseudoEMetricSpace α] {K :
 NNReal} {f : α → α},   LipschitzWith K f → ∀ (n : ℕ), LipschitzWith (K ^ n) f^[
n]
-/
theorem dist_iterate_succ_le_geometric {f : α → α} (hf : LipschitzWith K f) (x n) :
    dist (f^[n] x) (f^[n + 1] x) ≤ dist x (f x) * (K : ℝ) ^ n := by
  rw [iterate_succ, mul_comm]
  simpa only [NNReal.coe_pow] using! (hf.iterate n).dist_le_mul x (f x)
/-
**LipschitzWith._root_.lipschitzWith_max** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWit
h`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.lipschitzWith_max : LipschitzWith 1 fun p : ℝ × ℝ => max p.1 p.2 :=
  LipschitzWith.of_le_add fun _ _ => sub_le_iff_le_add'.1 <|
    (le_abs_self _).trans (abs_max_sub_max_le_max _ _ _ _)
/-
**LipschitzWith._root_.lipschitzWith_min** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWit
h`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.lipschitzWith_min : LipschitzWith 1 fun p : ℝ × ℝ => min p.1 p.2 :=
  LipschitzWith.of_le_add fun _ _ => sub_le_iff_le_add'.1 <|
    (le_abs_self _).trans (abs_min_sub_min_le_max _ _ _ _)
/-
**LipschitzWith._root_.Real.lipschitzWith_toNNReal** 是 Mathlib 中的一个引理，位于命名空间 `Li
pschitzWith`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Real.lipschitzWith_toNNReal : LipschitzWith 1 Real.toNNReal := by
  refine lipschitzWith_iff_dist_le_mul.mpr (fun x y ↦ ?_)
  simpa only [NNReal.coe_one, dist_prod_same_right, one_mul, Real.dist_eq] using!
    lipschitzWith_iff_dist_le_mul.mp lipschitzWith_max (x, 0) (y, 0)

/-- The set of functions which are 1-Lipschitz on a metric space separates points. -/
/-
**LipschitzWith._root_.Set.separatesPoints_lipschitzWith_one** 是 Mathlib 中的一个定理，
位于命名空间 `LipschitzWith`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of functions which are 1-Lipschitz on a metric space separates points.
-/
theorem _root_.Set.separatesPoints_lipschitzWith_one (E : Type*) [MetricSpace E] :
    { f : E → ℝ | LipschitzWith 1 f }.SeparatesPoints :=
  fun _ y _ ↦ ⟨(dist · y), by simp [LipschitzWith.dist_left], by simpa⟩

end Metric

section EMetric

variable [PseudoEMetricSpace α] {f g : α → ℝ} {Kf Kg : ℝ≥0}

/-
**LipschitzWith.max** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：∀ {α : Type u} [inst : PseudoEMetricSpace α] {f g : α → ℝ} {Kf Kg : NNReal
},   LipschitzWith Kf f → LipschitzWith Kg g → LipschitzWith (max Kf Kg) fun x =
> max (f x) (g x)
参数：max Kf Kg；f x；g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `LipschitzWith.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Pse
udoEMetricSpace α] [inst_1 : PseudoEMetricSpace β]   [inst_2 : PseudoEMetricSpac
e γ] {Kf…
· 使用定理 `lipschitzWith_max`：LipschitzWith 1 fun p => max p.1 p.2
· 使用定理 `LipschitzWith.prodMk`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : P
seudoEMetricSpace α] [inst_1 : PseudoEMetricSpace β]   [inst_2 : PseudoEMetricSp
ace γ] {f …
-/
protected theorem max (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g) :
    LipschitzWith (max Kf Kg) fun x => max (f x) (g x) := by
  simpa only [(· ∘ ·), one_mul] using! lipschitzWith_max.comp (hf.prodMk hg)
/-
**LipschitzWith.min** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：∀ {α : Type u} [inst : PseudoEMetricSpace α] {f g : α → ℝ} {Kf Kg : NNReal
},   LipschitzWith Kf f → LipschitzWith Kg g → LipschitzWith (max Kf Kg) fun x =
> min (f x) (g x)
参数：max Kf Kg；f x；g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `LipschitzWith.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Pse
udoEMetricSpace α] [inst_1 : PseudoEMetricSpace β]   [inst_2 : PseudoEMetricSpac
e γ] {Kf…
· 使用定理 `lipschitzWith_min`：LipschitzWith 1 fun p => min p.1 p.2
· 使用定理 `LipschitzWith.prodMk`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : P
seudoEMetricSpace α] [inst_1 : PseudoEMetricSpace β]   [inst_2 : PseudoEMetricSp
ace γ] {f …
-/
protected theorem min (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g) :
    LipschitzWith (max Kf Kg) fun x => min (f x) (g x) := by
  simpa only [(· ∘ ·), one_mul] using! lipschitzWith_min.comp (hf.prodMk hg)
/-
**LipschitzWith.max_const** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：max_const (hf : LipschitzWith Kf f) (a : Real) : LipschitzWith Kf fun x =>
 max (f x) a
参数：hf : LipschitzWith Kf f；a : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `LipschitzWith.max`：∀ {α : Type u} [inst : PseudoEMetricSpace α] {f g : α
 → ℝ} {Kf Kg : NNReal},   LipschitzWith Kf f → LipschitzWith Kg g → LipschitzWit
h (max …
· 使用定理 `LipschitzWith.const`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSp
ace α] [inst_1 : PseudoEMetricSpace β] (b : β),   LipschitzWith 0 fun x => b
-/
theorem max_const (hf : LipschitzWith Kf f) (a : ℝ) : LipschitzWith Kf fun x => max (f x) a := by
  simpa using hf.max (LipschitzWith.const a)
/-
**LipschitzWith.const_max** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：const_max (hf : LipschitzWith Kf f) (a : Real) : LipschitzWith Kf fun x =>
 max a (f x)
参数：hf : LipschitzWith Kf f；a : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `max_comm`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), max a b = m
ax b a
· 使用定理 `LipschitzWith.max_const`：max_const (hf : LipschitzWith Kf f) (a : Real) 
: LipschitzWith Kf fun x => max (f x) a
-/
theorem const_max (hf : LipschitzWith Kf f) (a : ℝ) : LipschitzWith Kf fun x => max a (f x) := by
  simpa only [max_comm] using hf.max_const a
/-
**LipschitzWith.min_const** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：min_const (hf : LipschitzWith Kf f) (a : Real) : LipschitzWith Kf fun x =>
 min (f x) a
参数：hf : LipschitzWith Kf f；a : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `LipschitzWith.min`：∀ {α : Type u} [inst : PseudoEMetricSpace α] {f g : α
 → ℝ} {Kf Kg : NNReal},   LipschitzWith Kf f → LipschitzWith Kg g → LipschitzWit
h (max …
· 使用定理 `LipschitzWith.const`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSp
ace α] [inst_1 : PseudoEMetricSpace β] (b : β),   LipschitzWith 0 fun x => b
-/
theorem min_const (hf : LipschitzWith Kf f) (a : ℝ) : LipschitzWith Kf fun x => min (f x) a := by
  simpa using hf.min (LipschitzWith.const a)
/-
**LipschitzWith.const_min** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：const_min (hf : LipschitzWith Kf f) (a : Real) : LipschitzWith Kf fun x =>
 min a (f x)
参数：hf : LipschitzWith Kf f；a : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `min_comm`：min_comm (a b : α) : min a b = min b a
· 使用定理 `LipschitzWith.min_const`：min_const (hf : LipschitzWith Kf f) (a : Real) 
: LipschitzWith Kf fun x => min (f x) a
-/
theorem const_min (hf : LipschitzWith Kf f) (a : ℝ) : LipschitzWith Kf fun x => min a (f x) := by
  simpa only [min_comm] using hf.min_const a

end EMetric

/-
**LipschitzWith.projIcc** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzWith`。
形式化陈述：∀ {a b : ℝ} (h : a ≤ b), LipschitzWith 1 (Set.projIcc a b h)
参数：h : a ≤ b；Set.projIcc a b h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.subtype_mk`：subtype_mk (hf : LipschitzWith K f) {p : β -> 
Prop} (hp : forall x, p (f x)) : LipschitzWith K (fun x => ⟨f x, hp x⟩ : α -> { 
y // p y })
· 使用定理 `LipschitzWith.const_max`：const_max (hf : LipschitzWith Kf f) (a : Real) 
: LipschitzWith Kf fun x => max a (f x)
· 使用定理 `LipschitzWith.const_min`：const_min (hf : LipschitzWith Kf f) (a : Real) 
: LipschitzWith Kf fun x => min a (f x)
· 使用定理 `LipschitzWith.id`：∀ {α : Type u} [inst : PseudoEMetricSpace α], Lipschit
zWith 1 id
-/
protected theorem projIcc {a b : ℝ} (h : a ≤ b) : LipschitzWith 1 (projIcc a b h) :=
  ((LipschitzWith.id.const_min _).const_max _).subtype_mk _

end LipschitzWith

/-- The preimage of a proper space under a Lipschitz proper map is proper. -/
/-
**LipschitzWith.properSpace** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LipschitzWith.properSpace {X Y : Type*} [PseudoMetricSpace X] [PseudoMetri
cSpace Y] [ProperSpace Y] {f : X -> Y} (hf : IsProperMap f) {K : Real>=0} (hf' :
 LipschitzWith K f) : ProperSpace X
参数：hf : IsProperMap f；hf' : LipschitzWith K f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.of_isClosed_subset`：IsCompact.of_isClosed_subset (hs : IsCompa
ct s) (ht : IsClosed t) (h : t subseteq s) : IsCompact t
· 使用引理 `IsProperMap.isCompact_preimage`：IsProperMap.isCompact_preimage (h : IsPr
operMap f) {K : Set Y} (hK : IsCompact K) : IsCompact (f ⁻¹' K)
· 使用定理 `ProperSpace.isCompact_closedBall`：∀ {α : Type u} {inst : PseudoMetricSpa
ce α} [self : ProperSpace α] (x : α) (r : ℝ), IsCompact (Metric.closedBall x r)
· 使用引理 `Metric.isClosed_closedBall`：isClosed_closedBall : IsClosed (closedBall x
 ε)
· 使用定理 `Set.MapsTo.subset_preimage`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} 
{t : Set β} {f : α → β}, Set.MapsTo f s t → s ⊆ f ⁻¹' t
· 使用定理 `LipschitzWith.mapsTo_closedBall`：mapsTo_closedBall (hf : LipschitzWith K
 f) (x : α) (r : Real) : MapsTo f (Metric.closedBall x r) (Metric.closedBall (f 
x) (K * r))

--- 原说明 ---
The preimage of a proper space under a Lipschitz proper map is proper.
-/
lemma LipschitzWith.properSpace {X Y : Type*} [PseudoMetricSpace X]
    [PseudoMetricSpace Y] [ProperSpace Y] {f : X → Y} (hf : IsProperMap f)
    {K : ℝ≥0} (hf' : LipschitzWith K f) : ProperSpace X :=
  ⟨fun x r ↦ (hf.isCompact_preimage (isCompact_closedBall (f x) (K * r))).of_isClosed_subset
    Metric.isClosed_closedBall (hf'.mapsTo_closedBall x r).subset_preimage⟩

namespace LipschitzOnWith

section Metric

variable [PseudoMetricSpace α] [PseudoMetricSpace β] [PseudoMetricSpace γ]
variable {K : ℝ≥0} {s : Set α} {f : α → β}

/-
**LipschitzOnWith.of_dist_le'** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzOnWith`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : PseudoMetricSpace α] [inst_1 : PseudoM
etricSpace β] {s : Set α} {f : α → β} {K : ℝ},   (∀ x ∈ s, ∀ y ∈ s, dist (f x) (
f y) ≤ K * dist x y) → LipschitzOnWith K.toNNReal f s
参数：∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) ≤ K * dist x y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzOnWith.of_dist_le_mul`：∀ {α : Type u} {β : Type v} [inst : Pseu
doMetricSpace α] [inst_1 : PseudoMetricSpace β] {K : NNReal} {s : Set α}   {f : 
α → β}, (∀ x ∈ s, ∀ …
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `Real.le_coe_toNNReal`：∀ (r : ℝ), r ≤ ↑r.toNNReal
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
-/
protected theorem of_dist_le' {K : ℝ} (h : ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) ≤ K * dist x y) :
    LipschitzOnWith (Real.toNNReal K) f s :=
  of_dist_le_mul fun x hx y hy =>
    le_trans (h x hx y hy) <| by gcongr; apply Real.le_coe_toNNReal
/-
**LipschitzOnWith.mk_one** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzOnWith`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : PseudoMetricSpace α] [inst_1 : PseudoM
etricSpace β] {s : Set α} {f : α → β},   (∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) ≤ d
ist x y) → LipschitzOnWith 1 f s
参数：∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) ≤ dist x y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzOnWith.of_dist_le_mul`：∀ {α : Type u} {β : Type v} [inst : Pseu
doMetricSpace α] [inst_1 : PseudoMetricSpace β] {K : NNReal} {s : Set α}   {f : 
α → β}, (∀ x ∈ s, ∀ …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
protected theorem mk_one (h : ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) ≤ dist x y) :
    LipschitzOnWith 1 f s :=
  of_dist_le_mul <| by simpa only [NNReal.coe_one, one_mul] using h

/-- For functions to `ℝ`, it suffices to prove `f x ≤ f y + K * dist x y`; this version
doesn't assume `0≤K`. -/
/-
**LipschitzOnWith.of_le_add_mul'** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzOnWith`。
形式化陈述：∀ {α : Type u} [inst : PseudoMetricSpace α] {s : Set α} {f : α → ℝ} (K : ℝ
),   (∀ x ∈ s, ∀ y ∈ s, f x ≤ f y + K * dist x y) → LipschitzOnWith K.toNNReal f
 s
参数：K : ℝ；∀ x ∈ s, ∀ y ∈ s, f x ≤ f y + K * dist x y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_le_iff_le_add'`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : LE 
α] [AddLeftMono α] {a b c : α}, a - b ≤ c ↔ a ≤ b + c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LipschitzOnWith.of_dist_le'`：∀ {α : Type u} {β : Type v} [inst : PseudoM
etricSpace α] [inst_1 : PseudoMetricSpace β] {s : Set α} {f : α → β} {K : ℝ},   
(∀ x ∈ s, ∀ y ∈ s…
· 使用定理 `abs_sub_le_iff`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : Linea
rOrder G] [IsOrderedAddMonoid G] {a b c : G},   |a - b| ≤ c ↔ a - b ≤ c ∧ b - a 
≤ c
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x

--- 原说明 ---
For functions to `ℝ`, it suffices to prove `f x ≤ f y + K * dist x y`; this vers
ion
doesn't assume `0≤K`.
-/
protected theorem of_le_add_mul' {f : α → ℝ} (K : ℝ)
    (h : ∀ x ∈ s, ∀ y ∈ s, f x ≤ f y + K * dist x y) : LipschitzOnWith (Real.toNNReal K) f s :=
  have I : ∀ x ∈ s, ∀ y ∈ s, f x - f y ≤ K * dist x y := fun x hx y hy =>
    sub_le_iff_le_add'.2 (h x hx y hy)
  LipschitzOnWith.of_dist_le' fun x hx y hy =>
    abs_sub_le_iff.2 ⟨I x hx y hy, dist_comm y x ▸ I y hy x hx⟩

/-- For functions to `ℝ`, it suffices to prove `f x ≤ f y + K * dist x y`; this version
assumes `0≤K`. -/
/-
**LipschitzOnWith.of_le_add_mul** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzOnWith`。
形式化陈述：∀ {α : Type u} [inst : PseudoMetricSpace α] {s : Set α} {f : α → ℝ} (K : N
NReal),   (∀ x ∈ s, ∀ y ∈ s, f x ≤ f y + ↑K * dist x y) → LipschitzOnWith K f s
参数：K : NNReal；∀ x ∈ s, ∀ y ∈ s, f x ≤ f y + ↑K * dist x y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.toNNReal_coe`：∀ {r : NNReal}, (↑r).toNNReal = r
· 使用定理 `LipschitzOnWith.of_le_add_mul'`：∀ {α : Type u} [inst : PseudoMetricSpace
 α] {s : Set α} {f : α → ℝ} (K : ℝ),   (∀ x ∈ s, ∀ y ∈ s, f x ≤ f y + K * dist x
 y) → LipschitzOnWit…

--- 原说明 ---
For functions to `ℝ`, it suffices to prove `f x ≤ f y + K * dist x y`; this vers
ion
assumes `0≤K`.
-/
protected theorem of_le_add_mul {f : α → ℝ} (K : ℝ≥0)
    (h : ∀ x ∈ s, ∀ y ∈ s, f x ≤ f y + K * dist x y) : LipschitzOnWith K f s := by
  simpa only [Real.toNNReal_coe] using LipschitzOnWith.of_le_add_mul' K h
/-
**LipschitzOnWith.of_le_add** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzOnWith`。
形式化陈述：∀ {α : Type u} [inst : PseudoMetricSpace α] {s : Set α} {f : α → ℝ},   (∀ 
x ∈ s, ∀ y ∈ s, f x ≤ f y + dist x y) → LipschitzOnWith 1 f s
参数：∀ x ∈ s, ∀ y ∈ s, f x ≤ f y + dist x y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzOnWith.of_le_add_mul`：∀ {α : Type u} [inst : PseudoMetricSpace 
α] {s : Set α} {f : α → ℝ} (K : NNReal),   (∀ x ∈ s, ∀ y ∈ s, f x ≤ f y + ↑K * d
ist x y) → Lipschit…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
protected theorem of_le_add {f : α → ℝ} (h : ∀ x ∈ s, ∀ y ∈ s, f x ≤ f y + dist x y) :
    LipschitzOnWith 1 f s :=
  LipschitzOnWith.of_le_add_mul 1 <| by simpa only [NNReal.coe_one, one_mul]
/-
**LipschitzOnWith.le_add_mul** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzOnWith`。
形式化陈述：∀ {α : Type u} [inst : PseudoMetricSpace α] {s : Set α} {f : α → ℝ} {K : N
NReal},   LipschitzOnWith K f s → ∀ {x : α}, x ∈ s → ∀ {y : α}, y ∈ s → f x ≤ f 
y + ↑K * dist x y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_le_iff_le_add'`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : LE 
α] [AddLeftMono α] {a b c : α}, a - b ≤ c ↔ a ≤ b + c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|
· 使用定理 `LipschitzOnWith.dist_le_mul`：∀ {α : Type u} {β : Type v} [inst : PseudoM
etricSpace α] [inst_1 : PseudoMetricSpace β] {K : NNReal} {s : Set α}   {f : α →
 β}, LipschitzOnW…
-/
protected theorem le_add_mul {f : α → ℝ} {K : ℝ≥0} (h : LipschitzOnWith K f s) {x : α} (hx : x ∈ s)
    {y : α} (hy : y ∈ s) : f x ≤ f y + K * dist x y :=
  sub_le_iff_le_add'.1 <| le_trans (le_abs_self _) <| h.dist_le_mul x hx y hy
/-
**LipschitzOnWith.iff_le_add_mul** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzOnWith`。
形式化陈述：∀ {α : Type u} [inst : PseudoMetricSpace α] {s : Set α} {f : α → ℝ} {K : N
NReal},   LipschitzOnWith K f s ↔ ∀ x ∈ s, ∀ y ∈ s, f x ≤ f y + ↑K * dist x y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzOnWith.le_add_mul`：∀ {α : Type u} [inst : PseudoMetricSpace α] 
{s : Set α} {f : α → ℝ} {K : NNReal},   LipschitzOnWith K f s → ∀ {x : α}, x ∈ s
 → ∀ {y : α}, y …
· 使用定理 `LipschitzOnWith.of_le_add_mul`：∀ {α : Type u} [inst : PseudoMetricSpace 
α] {s : Set α} {f : α → ℝ} (K : NNReal),   (∀ x ∈ s, ∀ y ∈ s, f x ≤ f y + ↑K * d
ist x y) → Lipschit…
-/
protected theorem iff_le_add_mul {f : α → ℝ} {K : ℝ≥0} :
    LipschitzOnWith K f s ↔ ∀ x ∈ s, ∀ y ∈ s, f x ≤ f y + K * dist x y :=
  ⟨LipschitzOnWith.le_add_mul, LipschitzOnWith.of_le_add_mul K⟩
/-
**LipschitzOnWith.isBounded_image2** 是 Mathlib 中的一个定理，位于命名空间 `LipschitzOnWith`。
形式化陈述：isBounded_image2 (f : α -> β -> γ) {K₁ K₂ : Real>=0} {s : Set α} {t : Set 
β} (hs : Bornology.IsBounded s) (ht : Bornology.IsBounded t) (hf₁ : forall b in 
t, LipschitzOnWith K₁ (fun a => f a b) s) (hf₂ : forall a in s, LipschitzOnWith 
K₂ (f a) t) : Bornology.IsBounded (Set.image2 f s t)
参数：f : α -> β -> γ；hs : Bornology.IsBounded s；ht : Bornology.IsBounded t；hf₁ : f
orall b in t, LipschitzOnWith K₁ (fun a => f a b) s；hf₂ : forall a in s, Lipschi
tzOnWith K₂ (f a) t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.isBounded_iff_ediam_ne_top`：isBounded_iff_ediam_ne_top : IsBounde
d s ↔ ediam s != ⊤
· 使用定理 `ne_top_of_le_ne_top`：ne_top_of_le_ne_top (hb : b != ⊤) (hab : a <= b) : 
a != ⊤
· 使用定理 `ENNReal.add_ne_top`：add_ne_top : a + b != ∞ ↔ a != ∞ ∧ b != ∞
· 使用定理 `ENNReal.mul_ne_top`：mul_ne_top : a != ∞ -> b != ∞ -> a * b != ∞
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
· 使用定理 `Bornology.IsBounded.ediam_ne_top`：∀ {α : Type u} {s : Set α} [inst : Pse
udoMetricSpace α], Bornology.IsBounded s → Metric.ediam s ≠ ⊤
· 使用定理 `LipschitzOnWith.ediam_image2_le`：ediam_image2_le (f : α -> β -> γ) {K₁ K
₂ : Real>=0} (s : Set α) (t : Set β) (hf₁ : forall b in t, LipschitzOnWith K₁ (f
 · b) s) (hf₂ : foral…
-/
theorem isBounded_image2 (f : α → β → γ) {K₁ K₂ : ℝ≥0} {s : Set α} {t : Set β}
    (hs : Bornology.IsBounded s) (ht : Bornology.IsBounded t)
    (hf₁ : ∀ b ∈ t, LipschitzOnWith K₁ (fun a => f a b) s)
    (hf₂ : ∀ a ∈ s, LipschitzOnWith K₂ (f a) t) : Bornology.IsBounded (Set.image2 f s t) :=
  Metric.isBounded_iff_ediam_ne_top.2 <|
    ne_top_of_le_ne_top
      (ENNReal.add_ne_top.mpr
        ⟨ENNReal.mul_ne_top ENNReal.coe_ne_top hs.ediam_ne_top,
          ENNReal.mul_ne_top ENNReal.coe_ne_top ht.ediam_ne_top⟩)
      (ediam_image2_le _ _ _ hf₁ hf₂)

end Metric

end LipschitzOnWith

namespace LocallyLipschitz

section Real

variable [PseudoEMetricSpace α] {f g : α → ℝ}

/-- The minimum of locally Lipschitz functions is locally Lipschitz. -/
/-
**LocallyLipschitz.min** 是 Mathlib 中的一个定理，位于命名空间 `LocallyLipschitz`。
形式化陈述：∀ {α : Type u} [inst : PseudoEMetricSpace α] {f g : α → ℝ},   LocallyLipsc
hitz f → LocallyLipschitz g → LocallyLipschitz fun x => min (f x) (g x)
参数：f x；g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LocallyLipschitz.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : 
PseudoEMetricSpace α] [inst_1 : PseudoEMetricSpace β]   [inst_2 : PseudoEMetricS
pace γ] {f …
· 使用定理 `LipschitzWith.locallyLipschitz`：∀ {α : Type u} {β : Type v} [inst : Pseu
doEMetricSpace α] [inst_1 : PseudoEMetricSpace β] {f : α → β} {K : NNReal},   Li
pschitzWith K f → Lo…
· 使用定理 `lipschitzWith_min`：LipschitzWith 1 fun p => min p.1 p.2
· 使用定理 `LocallyLipschitz.prodMk`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst 
: PseudoEMetricSpace α] [inst_1 : PseudoEMetricSpace β]   [inst_2 : PseudoEMetri
cSpace γ] {f …

--- 原说明 ---
The minimum of locally Lipschitz functions is locally Lipschitz.
-/
protected lemma min (hf : LocallyLipschitz f) (hg : LocallyLipschitz g) :
    LocallyLipschitz (fun x => min (f x) (g x)) :=
  lipschitzWith_min.locallyLipschitz.comp (hf.prodMk hg)

/-- The maximum of locally Lipschitz functions is locally Lipschitz. -/
/-
**LocallyLipschitz.max** 是 Mathlib 中的一个定理，位于命名空间 `LocallyLipschitz`。
形式化陈述：∀ {α : Type u} [inst : PseudoEMetricSpace α] {f g : α → ℝ},   LocallyLipsc
hitz f → LocallyLipschitz g → LocallyLipschitz fun x => max (f x) (g x)
参数：f x；g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LocallyLipschitz.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : 
PseudoEMetricSpace α] [inst_1 : PseudoEMetricSpace β]   [inst_2 : PseudoEMetricS
pace γ] {f …
· 使用定理 `LipschitzWith.locallyLipschitz`：∀ {α : Type u} {β : Type v} [inst : Pseu
doEMetricSpace α] [inst_1 : PseudoEMetricSpace β] {f : α → β} {K : NNReal},   Li
pschitzWith K f → Lo…
· 使用定理 `lipschitzWith_max`：LipschitzWith 1 fun p => max p.1 p.2
· 使用定理 `LocallyLipschitz.prodMk`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst 
: PseudoEMetricSpace α] [inst_1 : PseudoEMetricSpace β]   [inst_2 : PseudoEMetri
cSpace γ] {f …

--- 原说明 ---
The maximum of locally Lipschitz functions is locally Lipschitz.
-/
protected lemma max (hf : LocallyLipschitz f) (hg : LocallyLipschitz g) :
    LocallyLipschitz (fun x => max (f x) (g x)) :=
  lipschitzWith_max.locallyLipschitz.comp (hf.prodMk hg)
/-
**LocallyLipschitz.max_const** 是 Mathlib 中的一个定理，位于命名空间 `LocallyLipschitz`。
形式化陈述：max_const (hf : LocallyLipschitz f) (a : Real) : LocallyLipschitz fun x =>
 max (f x) a
参数：hf : LocallyLipschitz f；a : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LocallyLipschitz.max`：∀ {α : Type u} [inst : PseudoEMetricSpace α] {f g 
: α → ℝ},   LocallyLipschitz f → LocallyLipschitz g → LocallyLipschitz fun x => 
max (f x) …
· 使用定理 `LocallyLipschitz.const`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetri
cSpace α] [inst_1 : PseudoEMetricSpace β] (b : β),   LocallyLipschitz fun x => b
-/
theorem max_const (hf : LocallyLipschitz f) (a : ℝ) : LocallyLipschitz fun x => max (f x) a :=
  hf.max (LocallyLipschitz.const a)
/-
**LocallyLipschitz.const_max** 是 Mathlib 中的一个定理，位于命名空间 `LocallyLipschitz`。
形式化陈述：const_max (hf : LocallyLipschitz f) (a : Real) : LocallyLipschitz fun x =>
 max a (f x)
参数：hf : LocallyLipschitz f；a : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `max_comm`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), max a b = m
ax b a
· 使用定理 `LocallyLipschitz.max_const`：max_const (hf : LocallyLipschitz f) (a : Rea
l) : LocallyLipschitz fun x => max (f x) a
-/
theorem const_max (hf : LocallyLipschitz f) (a : ℝ) : LocallyLipschitz fun x => max a (f x) := by
  simpa [max_comm] using (hf.max_const a)
/-
**LocallyLipschitz.min_const** 是 Mathlib 中的一个定理，位于命名空间 `LocallyLipschitz`。
形式化陈述：min_const (hf : LocallyLipschitz f) (a : Real) : LocallyLipschitz fun x =>
 min (f x) a
参数：hf : LocallyLipschitz f；a : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LocallyLipschitz.min`：∀ {α : Type u} [inst : PseudoEMetricSpace α] {f g 
: α → ℝ},   LocallyLipschitz f → LocallyLipschitz g → LocallyLipschitz fun x => 
min (f x) …
· 使用定理 `LocallyLipschitz.const`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetri
cSpace α] [inst_1 : PseudoEMetricSpace β] (b : β),   LocallyLipschitz fun x => b
-/
theorem min_const (hf : LocallyLipschitz f) (a : ℝ) : LocallyLipschitz fun x => min (f x) a :=
  hf.min (LocallyLipschitz.const a)
/-
**LocallyLipschitz.const_min** 是 Mathlib 中的一个定理，位于命名空间 `LocallyLipschitz`。
形式化陈述：const_min (hf : LocallyLipschitz f) (a : Real) : LocallyLipschitz fun x =>
 min a (f x)
参数：hf : LocallyLipschitz f；a : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `min_comm`：min_comm (a b : α) : min a b = min b a
· 使用定理 `LocallyLipschitz.min_const`：min_const (hf : LocallyLipschitz f) (a : Rea
l) : LocallyLipschitz fun x => min (f x) a
-/
theorem const_min (hf : LocallyLipschitz f) (a : ℝ) : LocallyLipschitz fun x => min a (f x) := by
  simpa [min_comm] using (hf.min_const a)

end Real
end LocallyLipschitz

open Metric

variable [PseudoMetricSpace α] [PseudoMetricSpace β] {f : α → β}

/-- A function `f : α → ℝ` which is `K`-Lipschitz on a subset `s` admits a `K`-Lipschitz extension
to the whole space. -/
/-
**LipschitzOnWith.extend_real** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LipschitzOnWith.extend_real {f : α -> Real} {s : Set α} {K : Real>=0} (hf 
: LipschitzOnWith K f s) : exists g : α -> Real, LipschitzWith K g ∧ EqOn f g s
参数：hf : LipschitzOnWith K f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `LipschitzWith.weaken`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricS
pace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   LipschitzWit
h K f → ∀ …
· 使用定理 `LipschitzWith.const`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSp
ace α] [inst_1 : PseudoEMetricSpace β] (b : β),   LipschitzWith 0 fun x => b
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Set.eqOn_empty`：eqOn_empty (f₁ f₂ : α -> β) : EqOn f₁ f₂ ∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_le_iff_le_add`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [A
ddRightMono α] {a b c : α}, a - c ≤ b ↔ a ≤ b + c
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `LipschitzOnWith.le_add_mul`：∀ {α : Type u} [inst : PseudoMetricSpace α] 
{s : Set α} {f : α → ℝ} {K : NNReal},   LipschitzOnWith K f s → ∀ {x : α}, x ∈ s
 → ∀ {y : α}, y …
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `dist_triangle_left`：dist_triangle_left (x y z : α) : dist x y <= dist z 
x + dist z y
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_ciInf`：le_ciInf [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, c <=
 f x) : c <= iInf f
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
A function `f : α → ℝ` which is `K`-Lipschitz on a subset `s` admits a `K`-Lipsc
hitz extension
to the whole space.
-/
theorem LipschitzOnWith.extend_real {f : α → ℝ} {s : Set α} {K : ℝ≥0} (hf : LipschitzOnWith K f s) :
    ∃ g : α → ℝ, LipschitzWith K g ∧ EqOn f g s := by
  /- An extension is given by `g y = Inf {f x + K * dist y x | x ∈ s}`. Taking `x = y`, one has
    `g y ≤ f y` for `y ∈ s`, and the other inequality holds because `f` is `K`-Lipschitz, so that it
    cannot counterbalance the growth of `K * dist y x`. One readily checks from the formula that
    the extended function is also `K`-Lipschitz. -/
  rcases eq_empty_or_nonempty s with (rfl | hs)
  · exact ⟨fun _ => 0, (LipschitzWith.const _).weaken zero_le, eqOn_empty _ _⟩
  have : Nonempty s := by simp only [hs, nonempty_coe_sort]
  let g := fun y : α => iInf fun x : s => f x + K * dist y x
  have B : ∀ y : α, BddBelow (range fun x : s => f x + K * dist y x) := fun y => by
    rcases hs with ⟨z, hz⟩
    refine ⟨f z - K * dist y z, ?_⟩
    rintro w ⟨t, rfl⟩
    dsimp
    rw [sub_le_iff_le_add, add_assoc, ← mul_add, add_comm (dist y t)]
    calc
      f z ≤ f t + K * dist z t := hf.le_add_mul hz t.2
      _ ≤ f t + K * (dist y z + dist y t) := by gcongr; apply dist_triangle_left
  have E : EqOn f g s := fun x hx => by
    refine le_antisymm (le_ciInf fun y => hf.le_add_mul hx y.2) ?_
    simpa only [add_zero, Subtype.coe_mk, mul_zero, dist_self] using ciInf_le (B x) ⟨x, hx⟩
  refine ⟨g, LipschitzWith.of_le_add_mul K fun x y => ?_, E⟩
  rw [← sub_le_iff_le_add]
  refine le_ciInf fun z => ?_
  rw [sub_le_iff_le_add]
  calc
    g x ≤ f z + K * dist x z := ciInf_le (B x) _
    _ ≤ f z + K * dist y z + K * dist x y := by
      rw [add_assoc, ← mul_add, add_comm (dist y z)]
      gcongr
      apply dist_triangle

/-- A function `f : α → (ι → ℝ)` which is `K`-Lipschitz on a subset `s` admits a `K`-Lipschitz
extension to the whole space. The same result for the space `ℓ^∞ (ι, ℝ)` over a possibly infinite
type `ι` is implemented in `LipschitzOnWith.extend_lp_infty`. -/
/-
**LipschitzOnWith.extend_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LipschitzOnWith.extend_pi [Fintype ι] {f : α -> ι -> Real} {s : Set α} {K 
: Real>=0} (hf : LipschitzOnWith K f s) : exists g : α -> ι -> Real, LipschitzWi
th K g ∧ EqOn f g s
参数：hf : LipschitzOnWith K f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzOnWith.of_dist_le_mul`：∀ {α : Type u} {β : Type v} [inst : Pseu
doMetricSpace α] [inst_1 : PseudoMetricSpace β] {K : NNReal} {s : Set α}   {f : 
α → β}, (∀ x ∈ s, ∀ …
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `dist_le_pi_dist`：dist_le_pi_dist (f g : forall b, X b) (b : β) : dist (f
 b) (g b) <= dist f g
· 使用定理 `LipschitzOnWith.dist_le_mul`：∀ {α : Type u} {β : Type v} [inst : PseudoM
etricSpace α] [inst_1 : PseudoMetricSpace β] {K : NNReal} {s : Set α}   {f : α →
 β}, LipschitzOnW…
· 使用定理 `LipschitzOnWith.extend_real`：LipschitzOnWith.extend_real {f : α -> Real}
 {s : Set α} {K : Real>=0} (hf : LipschitzOnWith K f s) : exists g : α -> Real, 
LipschitzWith K g…
· 使用定理 `LipschitzWith.of_dist_le_mul`：∀ {α : Type u} {β : Type v} [inst : Pseudo
MetricSpace α] [inst_1 : PseudoMetricSpace β] {K : NNReal} {f : α → β},   (∀ (x 
y : α), dist (f x)…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `dist_pi_le_iff`：dist_pi_le_iff {f g : forall b, X b} {r : Real} (hr : 0 
<= r) : dist f g <= r ↔ forall b, dist (f b) (g b) <= r
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `LipschitzWith.dist_le_mul`：∀ {α : Type u} {β : Type v} [inst : PseudoMet
ricSpace α] [inst_1 : PseudoMetricSpace β] {K : NNReal} {f : α → β},   Lipschitz
With K f → ∀ (x…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
A function `f : α → (ι → ℝ)` which is `K`-Lipschitz on a subset `s` admits a `K`
-Lipschitz
extension to the whole space. The same result for the space `ℓ^∞ (ι, ℝ)` over a 
possibly infinite
type `ι` is implemented in `LipschitzOnWith.extend_lp_infty`.
-/
theorem LipschitzOnWith.extend_pi [Fintype ι] {f : α → ι → ℝ} {s : Set α}
    {K : ℝ≥0} (hf : LipschitzOnWith K f s) : ∃ g : α → ι → ℝ, LipschitzWith K g ∧ EqOn f g s := by
  have : ∀ i, ∃ g : α → ℝ, LipschitzWith K g ∧ EqOn (fun x => f x i) g s := fun i => by
    have : LipschitzOnWith K (fun x : α => f x i) s :=
      LipschitzOnWith.of_dist_le_mul fun x hx y hy =>
        (dist_le_pi_dist _ _ i).trans (hf.dist_le_mul x hx y hy)
    exact this.extend_real
  choose g hg using this
  refine ⟨fun x i => g i x, LipschitzWith.of_dist_le_mul fun x y => ?_, fun x hx ↦ ?_⟩
  · exact (dist_pi_le_iff (mul_nonneg K.2 dist_nonneg)).2 fun i => (hg i).1.dist_le_mul x y
  · ext1 i
    exact (hg i).2 hx
