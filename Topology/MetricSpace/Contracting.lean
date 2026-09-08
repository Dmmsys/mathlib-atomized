/-
Copyright (c) 2019 Rohan Mitta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Mitta, Kevin Buzzard, Alistair Tucker, Johannes Hölzl, Yury Kudryashov
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Setoid.Basic
public import Mathlib.Dynamics.FixedPoints.Topology
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Contracting maps

A Lipschitz continuous self-map with Lipschitz constant `K < 1` is called a *contracting map*.
In this file we prove the Banach fixed point theorem, some explicit estimates on the rate
of convergence, and some properties of the map sending a contracting map to its fixed point.

## Main definitions

* `ContractingWith K f` : a Lipschitz continuous self-map with `K < 1`;
* `efixedPoint` : given a contracting map `f` on a complete emetric space and a point `x`
  such that `edist x (f x) ≠ ∞`, `efixedPoint f hf x hx` is the unique fixed point of `f`
  in `Metric.eball x ∞`;
* `fixedPoint` : the unique fixed point of a contracting map on a complete nonempty metric space.

## Tags

contracting map, fixed point, Banach fixed point theorem
-/

@[expose] public section

open NNReal Topology ENNReal Filter Function

variable {α : Type*}

/-- A map is said to be `ContractingWith K`, if `K < 1` and `f` is `LipschitzWith K`. -/
/-
**ContractingWith** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ContractingWith [EMetricSpace α] (K : Real>=0) (f : α -> α)
参数：K : Real>=0；f : α -> α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A map is said to be `ContractingWith K`, if `K < 1` and `f` is `LipschitzWith K`
.
-/
def ContractingWith [EMetricSpace α] (K : ℝ≥0) (f : α → α) :=
  K < 1 ∧ LipschitzWith K f

namespace ContractingWith

variable [EMetricSpace α] {K : ℝ≥0} {f : α → α}

open EMetric Set

/-
**ContractingWith.toLipschitzWith** 是 Mathlib 中的一个定理，位于命名空间 `ContractingWith`。
形式化陈述：toLipschitzWith (hf : ContractingWith K f) : LipschitzWith K f
参数：hf : ContractingWith K f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem toLipschitzWith (hf : ContractingWith K f) : LipschitzWith K f := hf.2
/-
**ContractingWith.one_sub_K_pos'** 是 Mathlib 中的一个定理，位于命名空间 `ContractingWith`。
形式化陈述：one_sub_K_pos' (hf : ContractingWith K f) : (0 : Real>=0∞) < 1 - K
参数：hf : ContractingWith K f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem one_sub_K_pos' (hf : ContractingWith K f) : (0 : ℝ≥0∞) < 1 - K := by simp [hf.1]
/-
**ContractingWith.one_sub_K_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `ContractingWith`。
形式化陈述：one_sub_K_ne_zero (hf : ContractingWith K f) : (1 : Real>=0∞) - K != 0
参数：hf : ContractingWith K f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `ContractingWith.one_sub_K_pos'`：one_sub_K_pos' (hf : ContractingWith K f
) : (0 : Real>=0∞) < 1 - K
-/
theorem one_sub_K_ne_zero (hf : ContractingWith K f) : (1 : ℝ≥0∞) - K ≠ 0 :=
  ne_of_gt hf.one_sub_K_pos'
/-
**ContractingWith.one_sub_K_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `ContractingWith`。
形式化陈述：one_sub_K_ne_top : (1 : Real>=0∞) - K != ∞
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
-/
theorem one_sub_K_ne_top : (1 : ℝ≥0∞) - K ≠ ∞ := by
  norm_cast
  exact ENNReal.coe_ne_top
/-
**ContractingWith.edist_inequality** 是 Mathlib 中的一个定理，位于命名空间 `ContractingWith`。
形式化陈述：edist_inequality (hf : ContractingWith K f) {x y} (h : edist x y != ∞) : e
dist x y <= (edist x (f x) + edist y (f y)) / (1 - K)
参数：hf : ContractingWith K f；h : edist x y != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `edist_triangle4`：edist_triangle4 (x y z t : α) : edist x t <= edist x y 
+ edist y z + edist z t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PseudoEMetricSpace.edist_comm`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x y : α), edist x y = edist y x
· 使用定理 `add_right_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G)
, a + b + c = a + c + b
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ENNReal.le_div_iff_mul_le`：∀ {a b c : ENNReal}, b ≠ 0 ∨ c ≠ 0 → b ≠ ⊤ ∨ 
c ≠ ⊤ → (a ≤ c / b ↔ a * b ≤ c)
· 使用定理 `ContractingWith.one_sub_K_ne_zero`：one_sub_K_ne_zero (hf : ContractingWi
th K f) : (1 : Real>=0∞) - K != 0
· 使用定理 `ContractingWith.one_sub_K_ne_top`：one_sub_K_ne_top : (1 : Real>=0∞) - K 
!= ∞
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `ENNReal.sub_mul`：∀ {a b c : ENNReal}, (0 < b → b < a → c ≠ ⊤) → (a - b) 
* c = a * c - b * c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `tsub_le_iff_right`：tsub_le_iff_right [LE α] [Add α] [Sub α] [OrderedSub 
α] {a b c : α} : a - b <= c ↔ a <= c + b
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
-/
theorem edist_inequality (hf : ContractingWith K f) {x y} (h : edist x y ≠ ∞) :
    edist x y ≤ (edist x (f x) + edist y (f y)) / (1 - K) :=
  suffices edist x y ≤ edist x (f x) + edist y (f y) + K * edist x y by
    rwa [ENNReal.le_div_iff_mul_le (Or.inl hf.one_sub_K_ne_zero) (Or.inl one_sub_K_ne_top),
      mul_comm, ENNReal.sub_mul fun _ _ ↦ h, one_mul, tsub_le_iff_right]
  calc
    edist x y ≤ edist x (f x) + edist (f x) (f y) + edist (f y) y := edist_triangle4 _ _ _ _
    _ = edist x (f x) + edist y (f y) + edist (f x) (f y) := by rw [edist_comm y, add_right_comm]
    _ ≤ edist x (f x) + edist y (f y) + K * edist x y := add_le_add le_rfl (hf.2 _ _)
/-
**ContractingWith.edist_le_of_fixedPoint** 是 Mathlib 中的一个定理，位于命名空间 `ContractingW
ith`。
形式化陈述：edist_le_of_fixedPoint (hf : ContractingWith K f) {x y} (h : edist x y != 
∞) (hy : IsFixedPt f y) : edist x y <= edist x (f x) / (1 - K)
参数：hf : ContractingWith K f；h : edist x y != ∞；hy : IsFixedPt f y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Function.IsFixedPt.eq`：∀ {α : Type u₁} {f : α → α} {x : α}, Function.IsF
ixedPt f x → f x = x
· 使用定理 `PseudoEMetricSpace.edist_self`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x : α), edist x x = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `ContractingWith.edist_inequality`：edist_inequality (hf : ContractingWith
 K f) {x y} (h : edist x y != ∞) : edist x y <= (edist x (f x) + edist y (f y)) 
/ (1 - K)
-/
theorem edist_le_of_fixedPoint (hf : ContractingWith K f) {x y} (h : edist x y ≠ ∞)
    (hy : IsFixedPt f y) : edist x y ≤ edist x (f x) / (1 - K) := by
  simpa only [hy.eq, edist_self, add_zero] using hf.edist_inequality h
/-
**ContractingWith.eq_or_edist_eq_top_of_fixedPoints** 是 Mathlib 中的一个定理，位于命名空间 `C
ontractingWith`。
形式化陈述：eq_or_edist_eq_top_of_fixedPoints (hf : ContractingWith K f) {x y} (hx : I
sFixedPt f x) (hy : IsFixedPt f y) : x = y ∨ edist x y = ∞
参数：hf : ContractingWith K f；hx : IsFixedPt f x；hy : IsFixedPt f y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_right`：∀ {a b : Prop}, a ∨ b ↔ ¬b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `edist_le_zero`：edist_le_zero {x y : γ} : edist x y <= 0 ↔ x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.IsFixedPt.eq`：∀ {α : Type u₁} {f : α → α} {x : α}, Function.IsF
ixedPt f x → f x = x
· 使用定理 `PseudoEMetricSpace.edist_self`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x : α), edist x x = 0
· 使用定理 `ENNReal.zero_div`：∀ {a : ENNReal}, 0 / a = 0
· 使用定理 `ContractingWith.edist_le_of_fixedPoint`：edist_le_of_fixedPoint (hf : Con
tractingWith K f) {x y} (h : edist x y != ∞) (hy : IsFixedPt f y) : edist x y <=
 edist x (f x) / (1 - K)
-/
theorem eq_or_edist_eq_top_of_fixedPoints (hf : ContractingWith K f) {x y} (hx : IsFixedPt f x)
    (hy : IsFixedPt f y) : x = y ∨ edist x y = ∞ := by
  refine or_iff_not_imp_right.2 fun h ↦ edist_le_zero.1 ?_
  simpa only [hx.eq, edist_self, add_zero, ENNReal.zero_div] using hf.edist_le_of_fixedPoint h hy

/-- If a map `f` is `ContractingWith K`, and `s` is a forward-invariant set, then
restriction of `f` to `s` is `ContractingWith K` as well. -/
/-
**ContractingWith.restrict** 是 Mathlib 中的一个定理，位于命名空间 `ContractingWith`。
形式化陈述：restrict (hf : ContractingWith K f) {s : Set α} (hs : MapsTo f s s) : Cont
ractingWith K (hs.restrict f s s)
参数：hf : ContractingWith K f；hs : MapsTo f s s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
If a map `f` is `ContractingWith K`, and `s` is a forward-invariant set, then
restriction of `f` to `s` is `ContractingWith K` as well.
-/
theorem restrict (hf : ContractingWith K f) {s : Set α} (hs : MapsTo f s s) :
    ContractingWith K (hs.restrict f s s) :=
  ⟨hf.1, fun x y ↦ hf.2 x y⟩

section
variable [CompleteSpace α]

/-- Banach fixed-point theorem, contraction mapping theorem, `EMetricSpace` version.
A contracting map on a complete metric space has a fixed point.
We include more conclusions in this theorem to avoid proving them again later.

The main API for this theorem are the functions `efixedPoint` and `fixedPoint`,
and lemmas about these functions. -/
@[wikidata Q220680]
/-
**ContractingWith.exists_fixedPoint** 是 Mathlib 中的一个定理，位于命名空间 `ContractingWith`。
形式化陈述：exists_fixedPoint (hf : ContractingWith K f) (x : α) (hx : edist x (f x) !
= ∞) : exists y, IsFixedPt f y ∧ Tendsto (fun n => f^[n] x) atTop (𝓝 y) ∧ forall
 n : Nat, edist (f^[n] x) y <= edist x (f x) * (K : Real>=0∞) ^ n / (1 - K)
参数：hf : ContractingWith K f；x : α；hx : edist x (f x) != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `cauchySeq_of_edist_le_geometric`：cauchySeq_of_edist_le_geometric : Cauch
ySeq f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_lt_one_iff`：coe_lt_one_iff : (↑p : Real>=0∞) < 1 ↔ p < 1
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LipschitzWith.edist_iterate_succ_le_geometric`：edist_iterate_succ_le_geo
metric {f : α -> α} (hf : LipschitzWith K f) (x n) : edist (f^[n] x) (f^[n + 1] 
x) <= edist x (f x) * (K : Real>=0∞…
· 使用定理 `ContractingWith.toLipschitzWith`：toLipschitzWith (hf : ContractingWith K
 f) : LipschitzWith K f
· 使用定理 `cauchySeq_tendsto_of_complete`：cauchySeq_tendsto_of_complete [Preorder β
] [CompleteSpace α] {u : β -> α} (H : CauchySeq u) : exists x, Tendsto u atTop (
𝓝 x)
· 使用定理 `isFixedPt_of_tendsto_iterate`：isFixedPt_of_tendsto_iterate {x y : α} (hy
 : Tendsto (fun n => f^[n] x) atTop (𝓝 y)) (hf : ContinuousAt f y) : IsFixedPt f
 y
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `LipschitzWith.continuous`：∀ {α : Type u} {β : Type v} [inst : PseudoEMet
ricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   Lipschit
zWith K f → Co…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `edist_le_of_edist_le_geometric_of_tendsto`：edist_le_of_edist_le_geometri
c_of_tendsto {a : α} (ha : Tendsto f atTop (𝓝 a)) (n : Nat) : edist (f n) a <= C
 * r ^ n / (1 - r)

--- 原说明 ---
Banach fixed-point theorem, contraction mapping theorem, `EMetricSpace` version.
A contracting map on a complete metric space has a fixed point.
We include more conclusions in this theorem to avoid proving them again later.

The main API for this theorem are the functions `efixedPoint` and `fixedPoint`,
and lemmas about these functions.
-/
theorem exists_fixedPoint (hf : ContractingWith K f) (x : α) (hx : edist x (f x) ≠ ∞) :
    ∃ y, IsFixedPt f y ∧ Tendsto (fun n ↦ f^[n] x) atTop (𝓝 y) ∧
      ∀ n : ℕ, edist (f^[n] x) y ≤ edist x (f x) * (K : ℝ≥0∞) ^ n / (1 - K) :=
  have : CauchySeq fun n ↦ f^[n] x :=
    cauchySeq_of_edist_le_geometric K (edist x (f x)) (ENNReal.coe_lt_one_iff.2 hf.1) hx
      (hf.toLipschitzWith.edist_iterate_succ_le_geometric x)
  let ⟨y, hy⟩ := cauchySeq_tendsto_of_complete this
  ⟨y, isFixedPt_of_tendsto_iterate hy hf.2.continuous.continuousAt, hy,
    edist_le_of_edist_le_geometric_of_tendsto K (edist x (f x))
      (hf.toLipschitzWith.edist_iterate_succ_le_geometric x) hy⟩

variable (f) in
-- avoid `efixedPoint _` in pretty printer
/-- Let `x` be a point of a complete emetric space. Suppose that `f` is a contracting map,
and `edist x (f x) ≠ ∞`. Then `efixedPoint` is the unique fixed point of `f`
in `Metric.eball x ∞`. -/
/-
**ContractingWith.efixedPoint** 是 Mathlib 中的一个定义，位于命名空间 `ContractingWith`。
形式化陈述：efixedPoint (hf : ContractingWith K f) (x : α) (hx : edist x (f x) != ∞) :
 α
参数：hf : ContractingWith K f；x : α；hx : edist x (f x) != ∞。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ContractingWith.exists_fixedPoint`：exists_fixedPoint (hf : ContractingWi
th K f) (x : α) (hx : edist x (f x) != ∞) : exists y, IsFixedPt f y ∧ Tendsto (f
un n => f^[n] x) atTop …

--- 原说明 ---
Let `x` be a point of a complete emetric space. Suppose that `f` is a contractin
g map,
and `edist x (f x) ≠ ∞`. Then `efixedPoint` is the unique fixed point of `f`
in `Metric.eball x ∞`.
-/
noncomputable def efixedPoint (hf : ContractingWith K f) (x : α) (hx : edist x (f x) ≠ ∞) : α :=
  Classical.choose <| hf.exists_fixedPoint x hx
/-
**ContractingWith.efixedPoint_isFixedPt** 是 Mathlib 中的一个定理，位于命名空间 `ContractingWi
th`。
形式化陈述：efixedPoint_isFixedPt (hf : ContractingWith K f) {x : α} (hx : edist x (f 
x) != ∞) : IsFixedPt f (efixedPoint f hf x hx)
参数：hf : ContractingWith K f；hx : edist x (f x) != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ContractingWith.exists_fixedPoint`：exists_fixedPoint (hf : ContractingWi
th K f) (x : α) (hx : edist x (f x) != ∞) : exists y, IsFixedPt f y ∧ Tendsto (f
un n => f^[n] x) atTop …
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem efixedPoint_isFixedPt (hf : ContractingWith K f) {x : α} (hx : edist x (f x) ≠ ∞) :
    IsFixedPt f (efixedPoint f hf x hx) :=
  (Classical.choose_spec <| hf.exists_fixedPoint x hx).1
/-
**ContractingWith.tendsto_iterate_efixedPoint** 是 Mathlib 中的一个定理，位于命名空间 `Contrac
tingWith`。
形式化陈述：tendsto_iterate_efixedPoint (hf : ContractingWith K f) {x : α} (hx : edist
 x (f x) != ∞) : Tendsto (fun n => f^[n] x) atTop (𝓝 <| efixedPoint f hf x hx)
参数：hf : ContractingWith K f；hx : edist x (f x) != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ContractingWith.exists_fixedPoint`：exists_fixedPoint (hf : ContractingWi
th K f) (x : α) (hx : edist x (f x) != ∞) : exists y, IsFixedPt f y ∧ Tendsto (f
un n => f^[n] x) atTop …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem tendsto_iterate_efixedPoint (hf : ContractingWith K f) {x : α} (hx : edist x (f x) ≠ ∞) :
    Tendsto (fun n ↦ f^[n] x) atTop (𝓝 <| efixedPoint f hf x hx) :=
  (Classical.choose_spec <| hf.exists_fixedPoint x hx).2.1
/-
**ContractingWith.apriori_edist_iterate_efixedPoint_le** 是 Mathlib 中的一个定理，位于命名空间
 `ContractingWith`。
形式化陈述：apriori_edist_iterate_efixedPoint_le (hf : ContractingWith K f) {x : α} (h
x : edist x (f x) != ∞) (n : Nat) : edist (f^[n] x) (efixedPoint f hf x hx) <= e
dist x (f x) * (K : Real>=0∞) ^ n / (1 - K)
参数：hf : ContractingWith K f；hx : edist x (f x) != ∞；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ContractingWith.exists_fixedPoint`：exists_fixedPoint (hf : ContractingWi
th K f) (x : α) (hx : edist x (f x) != ∞) : exists y, IsFixedPt f y ∧ Tendsto (f
un n => f^[n] x) atTop …
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem apriori_edist_iterate_efixedPoint_le (hf : ContractingWith K f) {x : α}
    (hx : edist x (f x) ≠ ∞) (n : ℕ) :
    edist (f^[n] x) (efixedPoint f hf x hx) ≤ edist x (f x) * (K : ℝ≥0∞) ^ n / (1 - K) :=
  (Classical.choose_spec <| hf.exists_fixedPoint x hx).2.2 n
/-
**ContractingWith.edist_efixedPoint_le** 是 Mathlib 中的一个定理，位于命名空间 `ContractingWit
h`。
形式化陈述：edist_efixedPoint_le (hf : ContractingWith K f) {x : α} (hx : edist x (f x
) != ∞) : edist x (efixedPoint f hf x hx) <= edist x (f x) / (1 - K)
参数：hf : ContractingWith K f；hx : edist x (f x) != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ContractingWith.apriori_edist_iterate_efixedPoint_le`：apriori_edist_iter
ate_efixedPoint_le (hf : ContractingWith K f) {x : α} (hx : edist x (f x) != ∞) 
(n : Nat) : edist (f^[n] x) (efixedPoint f…
-/
theorem edist_efixedPoint_le (hf : ContractingWith K f) {x : α} (hx : edist x (f x) ≠ ∞) :
    edist x (efixedPoint f hf x hx) ≤ edist x (f x) / (1 - K) := by
  convert! hf.apriori_edist_iterate_efixedPoint_le hx 0
  simp only [pow_zero, mul_one]
/-
**ContractingWith.edist_efixedPoint_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `Contractin
gWith`。
形式化陈述：edist_efixedPoint_lt_top (hf : ContractingWith K f) {x : α} (hx : edist x 
(f x) != ∞) : edist x (efixedPoint f hf x hx) < ∞
参数：hf : ContractingWith K f；hx : edist x (f x) != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `ContractingWith.edist_efixedPoint_le`：edist_efixedPoint_le (hf : Contrac
tingWith K f) {x : α} (hx : edist x (f x) != ∞) : edist x (efixedPoint f hf x hx
) <= edist x (f x) / (1 - …
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `ENNReal.mul_ne_top`：mul_ne_top : a != ∞ -> b != ∞ -> a * b != ∞
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.inv_ne_top`：inv_ne_top : a⁻¹ != ∞ ↔ a != 0
· 使用定理 `ContractingWith.one_sub_K_ne_zero`：one_sub_K_ne_zero (hf : ContractingWi
th K f) : (1 : Real>=0∞) - K != 0
-/
theorem edist_efixedPoint_lt_top (hf : ContractingWith K f) {x : α} (hx : edist x (f x) ≠ ∞) :
    edist x (efixedPoint f hf x hx) < ∞ :=
  (hf.edist_efixedPoint_le hx).trans_lt
    (ENNReal.mul_ne_top hx <| ENNReal.inv_ne_top.2 hf.one_sub_K_ne_zero).lt_top
/-
**ContractingWith.efixedPoint_eq_of_edist_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `Cont
ractingWith`。
形式化陈述：efixedPoint_eq_of_edist_lt_top (hf : ContractingWith K f) {x : α} (hx : ed
ist x (f x) != ∞) {y : α} (hy : edist y (f y) != ∞) (h : edist x y != ∞) : efixe
dPoint f hf x hx = efixedPoint f hf y hy
参数：hf : ContractingWith K f；hx : edist x (f x) != ∞；hy : edist y (f y) != ∞；h : 
edist x y != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `ContractingWith.eq_or_edist_eq_top_of_fixedPoints`：eq_or_edist_eq_top_of
_fixedPoints (hf : ContractingWith K f) {x y} (hx : IsFixedPt f x) (hy : IsFixed
Pt f y) : x = y ∨ edist x y = ∞
· 使用定理 `ContractingWith.efixedPoint_isFixedPt`：efixedPoint_isFixedPt (hf : Contr
actingWith K f) {x : α} (hx : edist x (f x) != ∞) : IsFixedPt f (efixedPoint f h
f x hx)
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `Setoid.trans'`：trans' (r : Setoid α) : forall {x y z}, r x y -> r y z ->
 r x z
· 使用定理 `Setoid.symm'`：symm' (r : Setoid α) : forall {x y}, r x y -> r y x
· 使用定理 `ContractingWith.edist_efixedPoint_lt_top`：edist_efixedPoint_lt_top (hf :
 ContractingWith K f) {x : α} (hx : edist x (f x) != ∞) : edist x (efixedPoint f
 hf x hx) < ∞
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
-/
theorem efixedPoint_eq_of_edist_lt_top (hf : ContractingWith K f) {x : α} (hx : edist x (f x) ≠ ∞)
    {y : α} (hy : edist y (f y) ≠ ∞) (h : edist x y ≠ ∞) :
    efixedPoint f hf x hx = efixedPoint f hf y hy := by
  refine (hf.eq_or_edist_eq_top_of_fixedPoints ?_ ?_).elim id fun h' ↦ False.elim (ne_of_lt ?_ h')
    <;> try apply efixedPoint_isFixedPt
  change Metric.edistLtTopSetoid _ _
  trans x
  · apply Setoid.symm'
    exact hf.edist_efixedPoint_lt_top hx
  trans y
  exacts [lt_top_iff_ne_top.2 h, hf.edist_efixedPoint_lt_top hy]

end

/-- Banach fixed-point theorem for maps contracting on a complete subset. -/
/-
**ContractingWith.exists_fixedPoint'** 是 Mathlib 中的一个定理，位于命名空间 `ContractingWith`
。
形式化陈述：exists_fixedPoint' {s : Set α} (hsc : IsComplete s) (hsf : MapsTo f s s) (
hf : ContractingWith K <| hsf.restrict f s s) {x : α} (hxs : x in s) (hx : edist
 x (f x) != ∞) : exists y in s, IsFixedPt f y ∧ Tendsto (fun n => f^[n] x) atTop
 (𝓝 y) ∧ forall n : Nat, edist (f^[n] x) y <= edist x (f x) * (K : Real>=0∞) ^ n
 / (1 - K)
参数：hsc : IsComplete s；hsf : MapsTo f s s；hf : ContractingWith K <| hsf.restrict 
f s s；hxs : x in s；hx : edist x (f x) != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsComplete.completeSpace_coe`：∀ {α : Type u} [inst : UniformSpace α] {s 
: Set α}, IsComplete s → CompleteSpace ↑s
· 使用定理 `ContractingWith.exists_fixedPoint`：exists_fixedPoint (hf : ContractingWi
th K f) (x : α) (hx : edist x (f x) != ∞) : exists y, IsFixedPt f y ∧ Tendsto (f
un n => f^[n] x) atTop …
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.MapsTo.iterate`：∀ {α : Type u_1} {f : α → α} {s : Set α}, Set.MapsTo
 f s s → ∀ (n : ℕ), Set.MapsTo f^[n] s s
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Set.MapsTo.iterate_restrict`：∀ {α : Type u_1} {f : α → α} {s : Set α} (h
 : Set.MapsTo f s s) (n : ℕ),   (Set.MapsTo.restrict f s s h)^[n] = Set.MapsTo.r
estrict f^[n] s s…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)

--- 原说明 ---
Banach fixed-point theorem for maps contracting on a complete subset.
-/
theorem exists_fixedPoint' {s : Set α} (hsc : IsComplete s) (hsf : MapsTo f s s)
    (hf : ContractingWith K <| hsf.restrict f s s) {x : α} (hxs : x ∈ s) (hx : edist x (f x) ≠ ∞) :
    ∃ y ∈ s, IsFixedPt f y ∧ Tendsto (fun n ↦ f^[n] x) atTop (𝓝 y) ∧
      ∀ n : ℕ, edist (f^[n] x) y ≤ edist x (f x) * (K : ℝ≥0∞) ^ n / (1 - K) := by
  have := hsc.completeSpace_coe
  rcases hf.exists_fixedPoint ⟨x, hxs⟩ hx with ⟨y, hfy, h_tendsto, hle⟩
  refine ⟨y, y.2, Subtype.ext_iff.1 hfy, ?_, fun n ↦ ?_⟩
  · convert! (continuous_subtype_val.tendsto _).comp h_tendsto
    simp only [(· ∘ ·), MapsTo.iterate_restrict, MapsTo.val_restrict_apply]
  · convert! hle n
    rw [MapsTo.iterate_restrict]
    rfl

variable (f) in
-- avoid `efixedPoint _` in pretty printer
/-- Let `s` be a complete forward-invariant set of a self-map `f`. If `f` contracts on `s`
and `x ∈ s` satisfies `edist x (f x) ≠ ∞`, then `efixedPoint'` is the unique fixed point
of the restriction of `f` to `s ∩ Metric.eball x ∞`. -/
/-
**ContractingWith.efixedPoint'** 是 Mathlib 中的一个定义，位于命名空间 `ContractingWith`。
形式化陈述：efixedPoint' {s : Set α} (hsc : IsComplete s) (hsf : MapsTo f s s) (hf : C
ontractingWith K <| hsf.restrict f s s) (x : α) (hxs : x in s) (hx : edist x (f 
x) != ∞) : α
参数：hsc : IsComplete s；hsf : MapsTo f s s；hf : ContractingWith K <| hsf.restrict 
f s s；x : α；hxs : x in s；hx : edist x (f x) != ∞。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ContractingWith.exists_fixedPoint'`：exists_fixedPoint' {s : Set α} (hsc 
: IsComplete s) (hsf : MapsTo f s s) (hf : ContractingWith K <| hsf.restrict f s
 s) {x : α} (hxs : x in …

--- 原说明 ---
Let `s` be a complete forward-invariant set of a self-map `f`. If `f` contracts 
on `s`
and `x ∈ s` satisfies `edist x (f x) ≠ ∞`, then `efixedPoint'` is the unique fix
ed point
of the restriction of `f` to `s ∩ Metric.eball x ∞`.
-/
noncomputable def efixedPoint' {s : Set α} (hsc : IsComplete s) (hsf : MapsTo f s s)
    (hf : ContractingWith K <| hsf.restrict f s s) (x : α) (hxs : x ∈ s) (hx : edist x (f x) ≠ ∞) :
    α :=
  Classical.choose <| hf.exists_fixedPoint' hsc hsf hxs hx
/-
**ContractingWith.efixedPoint_mem'** 是 Mathlib 中的一个定理，位于命名空间 `ContractingWith`。
形式化陈述：efixedPoint_mem' {s : Set α} (hsc : IsComplete s) (hsf : MapsTo f s s) (hf
 : ContractingWith K <| hsf.restrict f s s) {x : α} (hxs : x in s) (hx : edist x
 (f x) != ∞) : efixedPoint' f hsc hsf hf x hxs hx in s
参数：hsc : IsComplete s；hsf : MapsTo f s s；hf : ContractingWith K <| hsf.restrict 
f s s；hxs : x in s；hx : edist x (f x) != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ContractingWith.exists_fixedPoint'`：exists_fixedPoint' {s : Set α} (hsc 
: IsComplete s) (hsf : MapsTo f s s) (hf : ContractingWith K <| hsf.restrict f s
 s) {x : α} (hxs : x in …
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem efixedPoint_mem' {s : Set α} (hsc : IsComplete s) (hsf : MapsTo f s s)
    (hf : ContractingWith K <| hsf.restrict f s s) {x : α} (hxs : x ∈ s) (hx : edist x (f x) ≠ ∞) :
    efixedPoint' f hsc hsf hf x hxs hx ∈ s :=
  (Classical.choose_spec <| hf.exists_fixedPoint' hsc hsf hxs hx).1
/-
**ContractingWith.efixedPoint_isFixedPt'** 是 Mathlib 中的一个定理，位于命名空间 `ContractingW
ith`。
形式化陈述：efixedPoint_isFixedPt' {s : Set α} (hsc : IsComplete s) (hsf : MapsTo f s 
s) (hf : ContractingWith K <| hsf.restrict f s s) {x : α} (hxs : x in s) (hx : e
dist x (f x) != ∞) : IsFixedPt f (efixedPoint' f hsc hsf hf x hxs hx)
参数：hsc : IsComplete s；hsf : MapsTo f s s；hf : ContractingWith K <| hsf.restrict 
f s s；hxs : x in s；hx : edist x (f x) != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ContractingWith.exists_fixedPoint'`：exists_fixedPoint' {s : Set α} (hsc 
: IsComplete s) (hsf : MapsTo f s s) (hf : ContractingWith K <| hsf.restrict f s
 s) {x : α} (hxs : x in …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem efixedPoint_isFixedPt' {s : Set α} (hsc : IsComplete s) (hsf : MapsTo f s s)
    (hf : ContractingWith K <| hsf.restrict f s s) {x : α} (hxs : x ∈ s) (hx : edist x (f x) ≠ ∞) :
    IsFixedPt f (efixedPoint' f hsc hsf hf x hxs hx) :=
  (Classical.choose_spec <| hf.exists_fixedPoint' hsc hsf hxs hx).2.1
/-
**ContractingWith.tendsto_iterate_efixedPoint'** 是 Mathlib 中的一个定理，位于命名空间 `Contra
ctingWith`。
形式化陈述：tendsto_iterate_efixedPoint' {s : Set α} (hsc : IsComplete s) (hsf : MapsT
o f s s) (hf : ContractingWith K <| hsf.restrict f s s) {x : α} (hxs : x in s) (
hx : edist x (f x) != ∞) : Tendsto (fun n => f^[n] x) atTop (𝓝 <| efixedPoint' f
 hsc hsf hf x hxs hx)
参数：hsc : IsComplete s；hsf : MapsTo f s s；hf : ContractingWith K <| hsf.restrict 
f s s；hxs : x in s；hx : edist x (f x) != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ContractingWith.exists_fixedPoint'`：exists_fixedPoint' {s : Set α} (hsc 
: IsComplete s) (hsf : MapsTo f s s) (hf : ContractingWith K <| hsf.restrict f s
 s) {x : α} (hxs : x in …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem tendsto_iterate_efixedPoint' {s : Set α} (hsc : IsComplete s) (hsf : MapsTo f s s)
    (hf : ContractingWith K <| hsf.restrict f s s) {x : α} (hxs : x ∈ s) (hx : edist x (f x) ≠ ∞) :
    Tendsto (fun n ↦ f^[n] x) atTop (𝓝 <| efixedPoint' f hsc hsf hf x hxs hx) :=
  (Classical.choose_spec <| hf.exists_fixedPoint' hsc hsf hxs hx).2.2.1
/-
**ContractingWith.apriori_edist_iterate_efixedPoint_le'** 是 Mathlib 中的一个定理，位于命名空
间 `ContractingWith`。
形式化陈述：apriori_edist_iterate_efixedPoint_le' {s : Set α} (hsc : IsComplete s) (hs
f : MapsTo f s s) (hf : ContractingWith K <| hsf.restrict f s s) {x : α} (hxs : 
x in s) (hx : edist x (f x) != ∞) (n : Nat) : edist (f^[n] x) (efixedPoint' f hs
c hsf hf x hxs hx) <= edist x (f x) * (K : Real>=0∞) ^ n / (1 - K)
参数：hsc : IsComplete s；hsf : MapsTo f s s；hf : ContractingWith K <| hsf.restrict 
f s s；hxs : x in s；hx : edist x (f x) != ∞；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ContractingWith.exists_fixedPoint'`：exists_fixedPoint' {s : Set α} (hsc 
: IsComplete s) (hsf : MapsTo f s s) (hf : ContractingWith K <| hsf.restrict f s
 s) {x : α} (hxs : x in …
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem apriori_edist_iterate_efixedPoint_le' {s : Set α} (hsc : IsComplete s) (hsf : MapsTo f s s)
    (hf : ContractingWith K <| hsf.restrict f s s) {x : α} (hxs : x ∈ s) (hx : edist x (f x) ≠ ∞)
    (n : ℕ) :
    edist (f^[n] x) (efixedPoint' f hsc hsf hf x hxs hx) ≤
      edist x (f x) * (K : ℝ≥0∞) ^ n / (1 - K) :=
  (Classical.choose_spec <| hf.exists_fixedPoint' hsc hsf hxs hx).2.2.2 n
/-
**ContractingWith.edist_efixedPoint_le'** 是 Mathlib 中的一个定理，位于命名空间 `ContractingWi
th`。
形式化陈述：edist_efixedPoint_le' {s : Set α} (hsc : IsComplete s) (hsf : MapsTo f s s
) (hf : ContractingWith K <| hsf.restrict f s s) {x : α} (hxs : x in s) (hx : ed
ist x (f x) != ∞) : edist x (efixedPoint' f hsc hsf hf x hxs hx) <= edist x (f x
) / (1 - K)
参数：hsc : IsComplete s；hsf : MapsTo f s s；hf : ContractingWith K <| hsf.restrict 
f s s；hxs : x in s；hx : edist x (f x) != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `ContractingWith.apriori_edist_iterate_efixedPoint_le'`：apriori_edist_ite
rate_efixedPoint_le' {s : Set α} (hsc : IsComplete s) (hsf : MapsTo f s s) (hf :
 ContractingWith K <| hsf.restrict f s s) {…
-/
theorem edist_efixedPoint_le' {s : Set α} (hsc : IsComplete s) (hsf : MapsTo f s s)
    (hf : ContractingWith K <| hsf.restrict f s s) {x : α} (hxs : x ∈ s) (hx : edist x (f x) ≠ ∞) :
    edist x (efixedPoint' f hsc hsf hf x hxs hx) ≤ edist x (f x) / (1 - K) := by
  convert! hf.apriori_edist_iterate_efixedPoint_le' hsc hsf hxs hx 0
  rw [pow_zero, mul_one]
/-
**ContractingWith.edist_efixedPoint_lt_top'** 是 Mathlib 中的一个定理，位于命名空间 `Contracti
ngWith`。
形式化陈述：edist_efixedPoint_lt_top' {s : Set α} (hsc : IsComplete s) (hsf : MapsTo f
 s s) (hf : ContractingWith K <| hsf.restrict f s s) {x : α} (hxs : x in s) (hx 
: edist x (f x) != ∞) : edist x (efixedPoint' f hsc hsf hf x hxs hx) < ∞
参数：hsc : IsComplete s；hsf : MapsTo f s s；hf : ContractingWith K <| hsf.restrict 
f s s；hxs : x in s；hx : edist x (f x) != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `ContractingWith.edist_efixedPoint_le'`：edist_efixedPoint_le' {s : Set α}
 (hsc : IsComplete s) (hsf : MapsTo f s s) (hf : ContractingWith K <| hsf.restri
ct f s s) {x : α} (hxs : x …
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `ENNReal.mul_ne_top`：mul_ne_top : a != ∞ -> b != ∞ -> a * b != ∞
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.inv_ne_top`：inv_ne_top : a⁻¹ != ∞ ↔ a != 0
· 使用定理 `ContractingWith.one_sub_K_ne_zero`：one_sub_K_ne_zero (hf : ContractingWi
th K f) : (1 : Real>=0∞) - K != 0
-/
theorem edist_efixedPoint_lt_top' {s : Set α} (hsc : IsComplete s) (hsf : MapsTo f s s)
    (hf : ContractingWith K <| hsf.restrict f s s) {x : α} (hxs : x ∈ s) (hx : edist x (f x) ≠ ∞) :
    edist x (efixedPoint' f hsc hsf hf x hxs hx) < ∞ :=
  (hf.edist_efixedPoint_le' hsc hsf hxs hx).trans_lt
    (ENNReal.mul_ne_top hx <| ENNReal.inv_ne_top.2 hf.one_sub_K_ne_zero).lt_top

/-- If a globally contracting map `f` has two complete forward-invariant sets `s`, `t`,
and `x ∈ s` is at a finite distance from `y ∈ t`, then the `efixedPoint'` constructed by `x`
is the same as the `efixedPoint'` constructed by `y`.

This lemma takes additional arguments stating that `f` contracts on `s` and `t` because this way
it can be used to prove the desired equality with non-trivial proofs of these facts. -/
/-
**ContractingWith.efixedPoint_eq_of_edist_lt_top'** 是 Mathlib 中的一个定理，位于命名空间 `Con
tractingWith`。
形式化陈述：efixedPoint_eq_of_edist_lt_top' (hf : ContractingWith K f) {s : Set α} (hs
c : IsComplete s) (hsf : MapsTo f s s) (hfs : ContractingWith K <| hsf.restrict 
f s s) {x : α} (hxs : x in s) (hx : edist x (f x) != ∞) {t : Set α} (htc : IsCom
plete t) (htf : MapsTo f t t) (hft : ContractingWith K <| htf.restrict f t t) {y
 : α} (hyt : y in t) (hy : edist y (f y) != ∞) (hxy : edist x y != ∞) : efixedPo
int' f hsc hsf hfs x hxs hx = efixedPoint' f htc htf hft y hyt hy
参数：hf : ContractingWith K f；hsc : IsComplete s；hsf : MapsTo f s s；hfs : Contract
ingWith K <| hsf.restrict f s s；hxs : x in s；hx : edist x (f x) != ∞；htc : IsCom
plete t；htf : MapsTo f t t；hft : ContractingWith K <| htf.restrict f t t；hyt : y
 in t；hy : edist y (f y) != ∞；hxy : edist x y != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `ContractingWith.eq_or_edist_eq_top_of_fixedPoints`：eq_or_edist_eq_top_of
_fixedPoints (hf : ContractingWith K f) {x y} (hx : IsFixedPt f x) (hy : IsFixed
Pt f y) : x = y ∨ edist x y = ∞
· 使用定理 `ContractingWith.efixedPoint_isFixedPt'`：efixedPoint_isFixedPt' {s : Set 
α} (hsc : IsComplete s) (hsf : MapsTo f s s) (hf : ContractingWith K <| hsf.rest
rict f s s) {x : α} (hxs : x…
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `Setoid.trans'`：trans' (r : Setoid α) : forall {x y z}, r x y -> r y z ->
 r x z
· 使用定理 `Setoid.symm'`：symm' (r : Setoid α) : forall {x y}, r x y -> r y x
· 使用定理 `ContractingWith.edist_efixedPoint_lt_top'`：edist_efixedPoint_lt_top' {s 
: Set α} (hsc : IsComplete s) (hsf : MapsTo f s s) (hf : ContractingWith K <| hs
f.restrict f s s) {x : α} (hxs …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤

--- 原说明 ---
If a globally contracting map `f` has two complete forward-invariant sets `s`, `
t`,
and `x ∈ s` is at a finite distance from `y ∈ t`, then the `efixedPoint'` constr
ucted by `x`
is the same as the `efixedPoint'` constructed by `y`.

This lemma takes additional arguments stating that `f` contracts on `s` and `t` 
because this way
it can be used to prove the desired equality with non-trivial proofs of these fa
cts.
-/
theorem efixedPoint_eq_of_edist_lt_top' (hf : ContractingWith K f) {s : Set α} (hsc : IsComplete s)
    (hsf : MapsTo f s s) (hfs : ContractingWith K <| hsf.restrict f s s) {x : α} (hxs : x ∈ s)
    (hx : edist x (f x) ≠ ∞) {t : Set α} (htc : IsComplete t) (htf : MapsTo f t t)
    (hft : ContractingWith K <| htf.restrict f t t) {y : α} (hyt : y ∈ t) (hy : edist y (f y) ≠ ∞)
    (hxy : edist x y ≠ ∞) :
    efixedPoint' f hsc hsf hfs x hxs hx = efixedPoint' f htc htf hft y hyt hy := by
  refine (hf.eq_or_edist_eq_top_of_fixedPoints ?_ ?_).elim id fun h' ↦ False.elim (ne_of_lt ?_ h')
    <;> try apply efixedPoint_isFixedPt'
  change Metric.edistLtTopSetoid _ _
  trans x
  · apply Setoid.symm'
    apply edist_efixedPoint_lt_top'
  trans y
  · exact lt_top_iff_ne_top.2 hxy
  · apply edist_efixedPoint_lt_top'

end ContractingWith

namespace ContractingWith

variable [MetricSpace α] {K : ℝ≥0} {f : α → α}

/-
**ContractingWith.one_sub_K_pos** 是 Mathlib 中的一个定理，位于命名空间 `ContractingWith`。
形式化陈述：one_sub_K_pos (hf : ContractingWith K f) : (0 : Real) < 1 - K
参数：hf : ContractingWith K f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, 0 < a - b ↔ b < a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem one_sub_K_pos (hf : ContractingWith K f) : (0 : ℝ) < 1 - K :=
  sub_pos.2 hf.1

section
variable (hf : ContractingWith K f)
include hf

/-
**ContractingWith.dist_le_mul** 是 Mathlib 中的一个定理，位于命名空间 `ContractingWith`。
形式化陈述：dist_le_mul (x y : α) : dist (f x) (f y) <= K * dist x y
参数：x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.dist_le_mul`：∀ {α : Type u} {β : Type v} [inst : PseudoMet
ricSpace α] [inst_1 : PseudoMetricSpace β] {K : NNReal} {f : α → β},   Lipschitz
With K f → ∀ (x…
· 使用定理 `ContractingWith.toLipschitzWith`：toLipschitzWith (hf : ContractingWith K
 f) : LipschitzWith K f
-/
theorem dist_le_mul (x y : α) : dist (f x) (f y) ≤ K * dist x y :=
  hf.toLipschitzWith.dist_le_mul x y
/-
**ContractingWith.dist_inequality** 是 Mathlib 中的一个定理，位于命名空间 `ContractingWith`。
形式化陈述：dist_inequality (x y) : dist x y <= (dist x (f x) + dist y (f y)) / (1 - K
)
参数：x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dist_triangle4_right`：dist_triangle4_right (x₁ y₁ x₂ y₂ : α) : dist x₁ y
₁ <= dist x₁ x₂ + dist y₁ y₂ + dist x₂ y₂
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `ContractingWith.dist_le_mul`：dist_le_mul (x y : α) : dist (f x) (f y) <=
 K * dist x y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `le_div_iff₀`：le_div_iff₀ (hc : 0 < c) : a <= b / c ↔ a * c <= b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `ContractingWith.one_sub_K_pos`：one_sub_K_pos (hf : ContractingWith K f) 
: (0 : Real) < 1 - K
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `sub_le_iff_le_add`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [A
ddRightMono α] {a b c : α}, a - c ≤ b ↔ a ≤ b + c
-/
theorem dist_inequality (x y) : dist x y ≤ (dist x (f x) + dist y (f y)) / (1 - K) :=
  suffices dist x y ≤ dist x (f x) + dist y (f y) + K * dist x y by
    rwa [le_div_iff₀ hf.one_sub_K_pos, mul_comm, _root_.sub_mul, one_mul, sub_le_iff_le_add]
  calc
    dist x y ≤ dist x (f x) + dist y (f y) + dist (f x) (f y) := dist_triangle4_right _ _ _ _
    _ ≤ dist x (f x) + dist y (f y) + K * dist x y := by grw [hf.dist_le_mul]
/-
**ContractingWith.dist_le_of_fixedPoint** 是 Mathlib 中的一个定理，位于命名空间 `ContractingWi
th`。
形式化陈述：dist_le_of_fixedPoint (x) {y} (hy : IsFixedPt f y) : dist x y <= dist x (f
 x) / (1 - K)
参数：x；hy : IsFixedPt f y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Function.IsFixedPt.eq`：∀ {α : Type u₁} {f : α → α} {x : α}, Function.IsF
ixedPt f x → f x = x
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `ContractingWith.dist_inequality`：dist_inequality (x y) : dist x y <= (di
st x (f x) + dist y (f y)) / (1 - K)
-/
theorem dist_le_of_fixedPoint (x) {y} (hy : IsFixedPt f y) : dist x y ≤ dist x (f x) / (1 - K) := by
  simpa only [hy.eq, dist_self, add_zero] using hf.dist_inequality x y
/-
**ContractingWith.fixedPoint_unique'** 是 Mathlib 中的一个定理，位于命名空间 `ContractingWith`
。
形式化陈述：fixedPoint_unique' {x y} (hx : IsFixedPt f x) (hy : IsFixedPt f y) : x = y
参数：hx : IsFixedPt f x；hy : IsFixedPt f y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `ContractingWith.eq_or_edist_eq_top_of_fixedPoints`：eq_or_edist_eq_top_of
_fixedPoints (hf : ContractingWith K f) {x y} (hx : IsFixedPt f x) (hy : IsFixed
Pt f y) : x = y ∨ edist x y = ∞
· 使用定理 `edist_ne_top`：edist_ne_top (x y : α) : edist x y != ⊤
-/
theorem fixedPoint_unique' {x y} (hx : IsFixedPt f x) (hy : IsFixedPt f y) : x = y :=
  (hf.eq_or_edist_eq_top_of_fixedPoints hx hy).resolve_right (edist_ne_top _ _)

/-- Let `f` be a contracting map with constant `K`; let `g` be another map uniformly
`C`-close to `f`. If `x` and `y` are their fixed points, then `dist x y ≤ C / (1 - K)`. -/
/-
**ContractingWith.dist_fixedPoint_fixedPoint_of_dist_le'** 是 Mathlib 中的一个定理，位于命名
空间 `ContractingWith`。
形式化陈述：dist_fixedPoint_fixedPoint_of_dist_le' (g : α -> α) {x y} (hx : IsFixedPt 
f x) (hy : IsFixedPt g y) {C} (hfg : forall z, dist (f z) (g z) <= C) : dist x y
 <= C / (1 - K)
参数：g : α -> α；hx : IsFixedPt f x；hy : IsFixedPt g y；hfg : forall z, dist (f z) (
g z) <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `ContractingWith.dist_le_of_fixedPoint`：dist_le_of_fixedPoint (x) {y} (hy
 : IsFixedPt f y) : dist x y <= dist x (f x) / (1 - K)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.IsFixedPt.eq`：∀ {α : Type u₁} {f : α → α} {x : α}, Function.IsF
ixedPt f x → f x = x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `div_le_div_iff_of_pos_right`：div_le_div_iff_of_pos_right (hc : 0 < c) : 
a / c <= b / c ↔ a <= b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `ContractingWith.one_sub_K_pos`：one_sub_K_pos (hf : ContractingWith K f) 
: (0 : Real) < 1 - K

--- 原说明 ---
Let `f` be a contracting map with constant `K`; let `g` be another map uniformly
`C`-close to `f`. If `x` and `y` are their fixed points, then `dist x y ≤ C / (1
 - K)`.
-/
theorem dist_fixedPoint_fixedPoint_of_dist_le' (g : α → α) {x y} (hx : IsFixedPt f x)
    (hy : IsFixedPt g y) {C} (hfg : ∀ z, dist (f z) (g z) ≤ C) : dist x y ≤ C / (1 - K) :=
  calc
    dist x y = dist y x := dist_comm x y
    _ ≤ dist y (f y) / (1 - K) := hf.dist_le_of_fixedPoint y hx
    _ = dist (f y) (g y) / (1 - K) := by rw [hy.eq, dist_comm]
    _ ≤ C / (1 - K) := (div_le_div_iff_of_pos_right hf.one_sub_K_pos).2 (hfg y)

variable [Nonempty α] [CompleteSpace α]

variable (f) in
/-- The unique fixed point of a contracting map in a nonempty complete metric space. -/
/-
**ContractingWith.fixedPoint** 是 Mathlib 中的一个定义，位于命名空间 `ContractingWith`。
形式化陈述：fixedPoint : α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unique fixed point of a contracting map in a nonempty complete metric space.
-/
noncomputable def fixedPoint : α :=
  efixedPoint f hf _ (edist_ne_top (Classical.choice ‹Nonempty α›) _)

/-- The point provided by `ContractingWith.fixedPoint` is actually a fixed point. -/
/-
**ContractingWith.fixedPoint_isFixedPt** 是 Mathlib 中的一个定理，位于命名空间 `ContractingWit
h`。
形式化陈述：fixedPoint_isFixedPt : IsFixedPt f (fixedPoint f hf)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContractingWith.efixedPoint_isFixedPt`：efixedPoint_isFixedPt (hf : Contr
actingWith K f) {x : α} (hx : edist x (f x) != ∞) : IsFixedPt f (efixedPoint f h
f x hx)

--- 原说明 ---
The point provided by `ContractingWith.fixedPoint` is actually a fixed point.
-/
theorem fixedPoint_isFixedPt : IsFixedPt f (fixedPoint f hf) :=
  hf.efixedPoint_isFixedPt _
/-
**ContractingWith.fixedPoint_unique** 是 Mathlib 中的一个定理，位于命名空间 `ContractingWith`。
形式化陈述：fixedPoint_unique {x} (hx : IsFixedPt f x) : x = fixedPoint f hf
参数：hx : IsFixedPt f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContractingWith.fixedPoint_unique'`：fixedPoint_unique' {x y} (hx : IsFix
edPt f x) (hy : IsFixedPt f y) : x = y
· 使用定理 `ContractingWith.fixedPoint_isFixedPt`：fixedPoint_isFixedPt : IsFixedPt f
 (fixedPoint f hf)
-/
theorem fixedPoint_unique {x} (hx : IsFixedPt f x) : x = fixedPoint f hf :=
  hf.fixedPoint_unique' hx hf.fixedPoint_isFixedPt
/-
**ContractingWith.dist_fixedPoint_le** 是 Mathlib 中的一个定理，位于命名空间 `ContractingWith`
。
形式化陈述：dist_fixedPoint_le (x) : dist x (fixedPoint f hf) <= dist x (f x) / (1 - K
)
参数：x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContractingWith.dist_le_of_fixedPoint`：dist_le_of_fixedPoint (x) {y} (hy
 : IsFixedPt f y) : dist x y <= dist x (f x) / (1 - K)
· 使用定理 `ContractingWith.fixedPoint_isFixedPt`：fixedPoint_isFixedPt : IsFixedPt f
 (fixedPoint f hf)
-/
theorem dist_fixedPoint_le (x) : dist x (fixedPoint f hf) ≤ dist x (f x) / (1 - K) :=
  hf.dist_le_of_fixedPoint x hf.fixedPoint_isFixedPt

/-- A posteriori estimates on the convergence of iterates to the fixed point. -/
/-
**ContractingWith.aposteriori_dist_iterate_fixedPoint_le** 是 Mathlib 中的一个定理，位于命名
空间 `ContractingWith`。
形式化陈述：aposteriori_dist_iterate_fixedPoint_le (x n) : dist (f^[n] x) (fixedPoint 
f hf) <= dist (f^[n] x) (f^[n + 1] x) / (1 - K)
参数：x n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.iterate_succ'`：iterate_succ' (n : Nat) : f^[n.succ] = f ∘ f^[n]
· 使用定理 `ContractingWith.dist_fixedPoint_le`：dist_fixedPoint_le (x) : dist x (fix
edPoint f hf) <= dist x (f x) / (1 - K)

--- 原说明 ---
A posteriori estimates on the convergence of iterates to the fixed point.
-/
theorem aposteriori_dist_iterate_fixedPoint_le (x n) :
    dist (f^[n] x) (fixedPoint f hf) ≤ dist (f^[n] x) (f^[n + 1] x) / (1 - K) := by
  rw [iterate_succ']
  apply hf.dist_fixedPoint_le
/-
**ContractingWith.apriori_dist_iterate_fixedPoint_le** 是 Mathlib 中的一个定理，位于命名空间 `
ContractingWith`。
形式化陈述：apriori_dist_iterate_fixedPoint_le (x n) : dist (f^[n] x) (fixedPoint f hf
) <= dist x (f x) * (K : Real) ^ n / (1 - K)
参数：x n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContractingWith.aposteriori_dist_iterate_fixedPoint_le`：aposteriori_dist
_iterate_fixedPoint_le (x n) : dist (f^[n] x) (fixedPoint f hf) <= dist (f^[n] x
) (f^[n + 1] x) / (1 - K)
· 使用引理 `div_le_div_of_nonneg_right`：div_le_div_of_nonneg_right (hab : a <= b) (h
c : 0 <= c) : a / c <= b / c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `LipschitzWith.dist_iterate_succ_le_geometric`：dist_iterate_succ_le_geome
tric {f : α -> α} (hf : LipschitzWith K f) (x n) : dist (f^[n] x) (f^[n + 1] x) 
<= dist x (f x) * (K : Real) ^ n
· 使用定理 `ContractingWith.toLipschitzWith`：toLipschitzWith (hf : ContractingWith K
 f) : LipschitzWith K f
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `ContractingWith.one_sub_K_pos`：one_sub_K_pos (hf : ContractingWith K f) 
: (0 : Real) < 1 - K
-/
theorem apriori_dist_iterate_fixedPoint_le (x n) :
    dist (f^[n] x) (fixedPoint f hf) ≤ dist x (f x) * (K : ℝ) ^ n / (1 - K) :=
  calc
    _ ≤ dist (f^[n] x) (f^[n + 1] x) / (1 - K) := hf.aposteriori_dist_iterate_fixedPoint_le x n
    _ ≤ _ := by
      gcongr; exacts [hf.one_sub_K_pos.le, hf.toLipschitzWith.dist_iterate_succ_le_geometric x n]
/-
**ContractingWith.tendsto_iterate_fixedPoint** 是 Mathlib 中的一个定理，位于命名空间 `Contract
ingWith`。
形式化陈述：tendsto_iterate_fixedPoint (x) : Tendsto (fun n => f^[n] x) atTop (𝓝 <| fi
xedPoint f hf)
参数：x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `edist_ne_top`：edist_ne_top (x y : α) : edist x y != ⊤
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContractingWith.fixedPoint_unique`：fixedPoint_unique {x} (hx : IsFixedPt
 f x) : x = fixedPoint f hf
· 使用定理 `ContractingWith.efixedPoint_isFixedPt`：efixedPoint_isFixedPt (hf : Contr
actingWith K f) {x : α} (hx : edist x (f x) != ∞) : IsFixedPt f (efixedPoint f h
f x hx)
· 使用定理 `ContractingWith.tendsto_iterate_efixedPoint`：tendsto_iterate_efixedPoint
 (hf : ContractingWith K f) {x : α} (hx : edist x (f x) != ∞) : Tendsto (fun n =
> f^[n] x) atTop (𝓝 <| efixedPoin…
-/
theorem tendsto_iterate_fixedPoint (x) :
    Tendsto (fun n ↦ f^[n] x) atTop (𝓝 <| fixedPoint f hf) := by
  convert! tendsto_iterate_efixedPoint hf (edist_ne_top x _)
  refine (fixedPoint_unique _ ?_).symm
  apply efixedPoint_isFixedPt
/-
**ContractingWith.fixedPoint_lipschitz_in_map** 是 Mathlib 中的一个定理，位于命名空间 `Contrac
tingWith`。
形式化陈述：fixedPoint_lipschitz_in_map {g : α -> α} (hg : ContractingWith K g) {C} (h
fg : forall z, dist (f z) (g z) <= C) : dist (fixedPoint f hf) (fixedPoint g hg)
 <= C / (1 - K)
参数：hg : ContractingWith K g；hfg : forall z, dist (f z) (g z) <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContractingWith.dist_fixedPoint_fixedPoint_of_dist_le'`：dist_fixedPoint_
fixedPoint_of_dist_le' (g : α -> α) {x y} (hx : IsFixedPt f x) (hy : IsFixedPt g
 y) {C} (hfg : forall z, dist (f z) (g z) <=…
· 使用定理 `ContractingWith.fixedPoint_isFixedPt`：fixedPoint_isFixedPt : IsFixedPt f
 (fixedPoint f hf)
-/
theorem fixedPoint_lipschitz_in_map {g : α → α} (hg : ContractingWith K g) {C}
    (hfg : ∀ z, dist (f z) (g z) ≤ C) : dist (fixedPoint f hf) (fixedPoint g hg) ≤ C / (1 - K) :=
  hf.dist_fixedPoint_fixedPoint_of_dist_le' g hf.fixedPoint_isFixedPt hg.fixedPoint_isFixedPt hfg

end

variable [Nonempty α] [CompleteSpace α]

/-- If a map `f` has a contracting iterate `f^[n]`, then the fixed point of `f^[n]` is also a fixed
point of `f`. -/
/-
**ContractingWith.isFixedPt_fixedPoint_iterate** 是 Mathlib 中的一个定理，位于命名空间 `Contra
ctingWith`。
形式化陈述：isFixedPt_fixedPoint_iterate {n : Nat} (hf : ContractingWith K f^[n]) : Is
FixedPt f (hf.fixedPoint f^[n])
参数：hf : ContractingWith K f^[n]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContractingWith.fixedPoint_isFixedPt`：fixedPoint_isFixedPt : IsFixedPt f
 (fixedPoint f hf)
· 使用定理 `LipschitzWith.dist_le_mul`：∀ {α : Type u} {β : Type v} [inst : PseudoMet
ricSpace α] [inst_1 : PseudoMetricSpace β] {K : NNReal} {f : α → β},   Lipschitz
With K f → ∀ (x…
· 使用定理 `ContractingWith.toLipschitzWith`：toLipschitzWith (hf : ContractingWith K
 f) : LipschitzWith K f
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_lt_mul_of_pos_right`：mul_lt_mul_of_pos_right [MulPosStrictMono α] (h
bc : b < c) (ha : 0 < a) : b * a < c * a
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NNReal.coe_lt_one`：∀ {r : NNReal}, ↑r < 1 ↔ r < 1
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `dist_pos`：dist_pos {x y : γ} : 0 < dist x y ↔ x != y
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Function.iterate_succ_apply'`：iterate_succ_apply' (n : Nat) (x : α) : f^
[n.succ] x = f (f^[n] x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.iterate_succ_apply`：iterate_succ_apply (n : Nat) (x : α) : f^[n
.succ] x = f^[n] (f x)

--- 原说明 ---
If a map `f` has a contracting iterate `f^[n]`, then the fixed point of `f^[n]` 
is also a fixed
point of `f`.
-/
theorem isFixedPt_fixedPoint_iterate {n : ℕ} (hf : ContractingWith K f^[n]) :
    IsFixedPt f (hf.fixedPoint f^[n]) := by
  set x := hf.fixedPoint f^[n]
  have hx : f^[n] x = x := hf.fixedPoint_isFixedPt
  have := hf.toLipschitzWith.dist_le_mul x (f x)
  rw [← iterate_succ_apply, iterate_succ_apply', hx] at this
  contrapose! this
  simpa using mul_lt_mul_of_pos_right (NNReal.coe_lt_one.2 hf.left) <| dist_pos.2 (Ne.symm this)

end ContractingWith

