/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.MetricSpace.IsometricSMul
public import Mathlib.Tactic.Finiteness

/-!
# Hausdorff distance

The Hausdorff distance on subsets of a metric (or emetric) space.

Given two subsets `s` and `t` of a metric space, their Hausdorff distance is the smallest `d`
such that any point of `s` is within `d` of a point in `t`, and conversely. This quantity
is often infinite (think of `s` bounded and `t` unbounded), and therefore better
expressed in the setting of emetric spaces.

## Main definitions

This file introduces:
* `Metric.infEDist x s`, the infimum edistance of a point `x` to a set `s` in an emetric space
* `Metric.hausdorffEDist s t`, the Hausdorff edistance of two sets in an emetric space
* Versions of these notions on metric spaces, called respectively `Metric.infDist`
  and `Metric.hausdorffDist`

## Main results
* `infEDist_closure`: the edistance to a set and its closure coincide
* `Metric.mem_closure_iff_infEDist_zero`: a point `x` belongs to the closure of `s` iff
  `infEDist x s = 0`
* `IsCompact.exists_infEDist_eq_edist`: if `s` is compact and non-empty, there exists a point `y`
  which attains this edistance
* `IsOpen.exists_iUnion_isClosed`: every open set `U` can be written as the increasing union
  of countably many closed subsets of `U`

* `hausdorffEDist_closure`: replacing a set by its closure does not change the Hausdorff edistance
* `hausdorffEDist_zero_iff_closure_eq_closure`: two sets have Hausdorff edistance zero
  iff their closures coincide
* the Hausdorff edistance is symmetric and satisfies the triangle inequality
* in particular, closed sets in an emetric space are an emetric space
  (this is shown in `EMetricSpace.Closeds.emetricSpace`)

* versions of these notions on metric spaces
* `hausdorffEDist_ne_top_of_nonempty_of_bounded`: if two sets in a metric space
  are nonempty and bounded in a metric space, they are at finite Hausdorff edistance.

## Tags
metric space, Hausdorff distance
-/

@[expose] public section


noncomputable section

open NNReal ENNReal Topology Set Filter Pointwise Bornology

universe u v w

variable {ι : Sort*} {α : Type u} {β : Type v}

namespace Metric

section InfEDist

variable [PseudoEMetricSpace α] [PseudoEMetricSpace β] {x y : α} {s t : Set α} {Φ : α → β}

/-! ### Distance of a point to a set as a function into `ℝ≥0∞`. -/

/-- The minimal edistance of a point to a set -/
/-
**Metric.infEDist** 是 Mathlib 中的一个定义，位于命名空间 `Metric`。
形式化陈述：infEDist (x : α) (s : Set α) : Real>=0∞
参数：x : α；s : Set α。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The minimal edistance of a point to a set
-/
def infEDist (x : α) (s : Set α) : ℝ≥0∞ :=
  ⨅ y ∈ s, edist x y

@[simp]
/-
**Metric.infEDist_empty** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：infEDist_empty : infEDist x ∅ = ∞
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_emptyset`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLattice α
] {f : β → α}, ⨅ x ∈ ∅, f x = ⊤
-/
theorem infEDist_empty : infEDist x ∅ = ∞ :=
  iInf_emptyset
/-
**Metric.le_infEDist** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：le_infEDist {d} : d <= infEDist x s ↔ forall y in s, d <= edist x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem le_infEDist {d} : d ≤ infEDist x s ↔ ∀ y ∈ s, d ≤ edist x y := by
  simp only [infEDist, le_iInf_iff]

/-- The edist to a union is the minimum of the edists -/
@[simp]
/-
**Metric.infEDist_union** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：infEDist_union : infEDist x (s union t) = infEDist x s ⊓ infEDist x t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_union`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLattice α] {
f : β → α} {s t : Set β},   ⨅ x ∈ s ∪ t, f x = (⨅ x ∈ s, f x) ⊓ ⨅ x ∈ t, f x

--- 原说明 ---
The edist to a union is the minimum of the edists
-/
theorem infEDist_union : infEDist x (s ∪ t) = infEDist x s ⊓ infEDist x t :=
  iInf_union

@[simp]
/-
**Metric.infEDist_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：infEDist_iUnion (f : ι -> Set α) (x : α) : infEDist x (⋃ i, f i) = ⨅ i, in
fEDist x (f i)
参数：f : ι -> Set α；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_iUnion`：iInf_iUnion (s : ι -> Set α) (f : α -> β) : ⨅ a in ⋃ i, s i
, f a = ⨅ (i) (a in s i), f a
-/
theorem infEDist_iUnion (f : ι → Set α) (x : α) : infEDist x (⋃ i, f i) = ⨅ i, infEDist x (f i) :=
  iInf_iUnion f _
/-
**Metric.infEDist_biUnion** 是 Mathlib 中的一个引理，位于命名空间 `Metric`。
形式化陈述：infEDist_biUnion {ι : Type*} (f : ι -> Set α) (I : Set ι) (x : α) : infEDi
st x (⋃ i in I, f i) = ⨅ i in I, infEDist x (f i)
参数：f : ι -> Set α；I : Set ι；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.infEDist_iUnion`：infEDist_iUnion (f : ι -> Set α) (x : α) : infED
ist x (⋃ i, f i) = ⨅ i, infEDist x (f i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma infEDist_biUnion {ι : Type*} (f : ι → Set α) (I : Set ι) (x : α) :
    infEDist x (⋃ i ∈ I, f i) = ⨅ i ∈ I, infEDist x (f i) := by simp only [infEDist_iUnion]

/-- The edist to a singleton is the edistance to the single point of this singleton -/
@[simp]
/-
**Metric.infEDist_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：infEDist_singleton : infEDist x {y} = edist x y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_singleton`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLattice 
α] {f : β → α} {b : β}, ⨅ x ∈ {b}, f x = f b

--- 原说明 ---
The edist to a singleton is the edistance to the single point of this singleton
-/
theorem infEDist_singleton : infEDist x {y} = edist x y :=
  iInf_singleton

/-- The edist to a set is bounded above by the edist to any of its points -/
/-
**Metric.infEDist_le_edist_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：infEDist_le_edist_of_mem (h : y in s) : infEDist x s <= edist x y
参数：h : y in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf₂_le`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : Com
pleteLattice α] {f : (i : ι) → κ i → α} (i : ι) (j : κ i),   ⨅ i, ⨅ j, f i j ≤…

--- 原说明 ---
The edist to a set is bounded above by the edist to any of its points
-/
theorem infEDist_le_edist_of_mem (h : y ∈ s) : infEDist x s ≤ edist x y :=
  iInf₂_le y h

/-- If a point `x` belongs to `s`, then its edist to `s` vanishes -/
/-
**Metric.infEDist_zero_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：infEDist_zero_of_mem (h : x in s) : infEDist x s = 0
参数：h : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Metric.infEDist_le_edist_of_mem`：infEDist_le_edist_of_mem (h : y in s) :
 infEDist x s <= edist x y
· 使用定理 `PseudoEMetricSpace.edist_self`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x : α), edist x x = 0

--- 原说明 ---
If a point `x` belongs to `s`, then its edist to `s` vanishes
-/
theorem infEDist_zero_of_mem (h : x ∈ s) : infEDist x s = 0 :=
  nonpos_iff_eq_zero.1 <| @edist_self _ _ x ▸ infEDist_le_edist_of_mem h

/-- The edist is antitone with respect to inclusion. -/
@[gcongr]
/-
**Metric.infEDist_anti** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：infEDist_anti (h : s subseteq t) : infEDist x t <= infEDist x s
参数：h : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_le_iInf_of_subset`：∀ {α : Type u_1} {β : Type u_2} [inst : Complete
Lattice α] {f : β → α} {s t : Set β},   s ⊆ t → ⨅ x ∈ t, f x ≤ ⨅ x ∈ s, f x

--- 原说明 ---
The edist is antitone with respect to inclusion.
-/
theorem infEDist_anti (h : s ⊆ t) : infEDist x t ≤ infEDist x s :=
  iInf_le_iInf_of_subset h

/-- The edist to a set is `< r` iff there exists a point in the set at edistance `< r` -/
/-
**Metric.infEDist_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：infEDist_lt_iff {r : Real>=0∞} : infEDist x s < r ↔ exists y in s, edist x
 y < r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The edist to a set is `< r` iff there exists a point in the set at edistance `< 
r`
-/
theorem infEDist_lt_iff {r : ℝ≥0∞} : infEDist x s < r ↔ ∃ y ∈ s, edist x y < r := by
  simp_rw [infEDist, iInf_lt_iff, exists_prop]

/-- The edist of `x` to `s` is bounded by the sum of the edist of `y` to `s` and
the edist from `x` to `y` -/
/-
**Metric.infEDist_le_infEDist_add_edist** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：infEDist_le_infEDist_add_edist : infEDist x s <= infEDist y s + edist x y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf₂_mono`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : C
ompleteLattice α] {f g : (i : ι) → κ i → α},   (∀ (i : ι) (j : κ i), g i j ≤ f i
…
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `PseudoEMetricSpace.edist_triangle`：∀ {α : Type u} [self : PseudoEMetricS
pace α] (x y z : α), edist x z ≤ edist x y + edist y z
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.iInf_add`：iInf_add : iInf f + a = ⨅ i, f i + a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The edist of `x` to `s` is bounded by the sum of the edist of `y` to `s` and
the edist from `x` to `y`
-/
theorem infEDist_le_infEDist_add_edist : infEDist x s ≤ infEDist y s + edist x y :=
  calc
    ⨅ z ∈ s, edist x z ≤ ⨅ z ∈ s, edist y z + edist x y :=
      iInf₂_mono fun _ _ => (edist_triangle _ _ _).trans_eq (add_comm _ _)
    _ = (⨅ z ∈ s, edist y z) + edist x y := by simp only [ENNReal.iInf_add]
/-
**Metric.infEDist_le_edist_add_infEDist** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：infEDist_le_edist_add_infEDist : infEDist x s <= edist x y + infEDist y s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Metric.infEDist_le_infEDist_add_edist`：infEDist_le_infEDist_add_edist : 
infEDist x s <= infEDist y s + edist x y
-/
theorem infEDist_le_edist_add_infEDist : infEDist x s ≤ edist x y + infEDist y s := by
  rw [add_comm]
  exact infEDist_le_infEDist_add_edist
/-
**Metric.edist_le_infEDist_add_ediam** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：edist_le_infEDist_add_ediam (hy : y in s) : edist x y <= infEDist x s + Me
tric.ediam s
参数：hy : y in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ENNReal.iInf_add`：iInf_add : iInf f + a = ⨅ i, f i + a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `le_iInf₂`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : Com
pleteLattice α] {a : α} {f : (i : ι) → κ i → α},   (∀ (i : ι) (j : κ i), a ≤ f…
· 使用定理 `PseudoEMetricSpace.edist_triangle`：∀ {α : Type u} [self : PseudoEMetricS
pace α] (x y z : α), edist x z ≤ edist x y + edist y z
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Metric.edist_le_ediam_of_mem`：edist_le_ediam_of_mem (hx : x in s) (hy : 
y in s) : edist x y <= ediam s
-/
theorem edist_le_infEDist_add_ediam (hy : y ∈ s) : edist x y ≤ infEDist x s + Metric.ediam s := by
  simp_rw [infEDist, ENNReal.iInf_add]
  refine le_iInf₂ fun i hi => ?_
  calc
    edist x y ≤ edist x i + edist i y := edist_triangle _ _ _
    _ ≤ edist x i + Metric.ediam s := add_le_add le_rfl (Metric.edist_le_ediam_of_mem hi hy)

/-- The edist to a set depends continuously on the point -/
@[continuity, fun_prop]
/-
**Metric.continuous_infEDist** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：continuous_infEDist : Continuous fun x => infEDist x s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_of_le_add_edist`：continuous_of_le_add_edist {f : α -> Real>=0
∞} (C : Real>=0∞) (hC : C != ∞) (h : forall x y, f x <= f y + C * edist x y) : C
ontinuous f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a

--- 原说明 ---
The edist to a set depends continuously on the point
-/
theorem continuous_infEDist : Continuous fun x => infEDist x s :=
  continuous_of_le_add_edist 1 (by simp) <| by
    simp only [one_mul, infEDist_le_infEDist_add_edist, forall₂_true_iff]

/-- The edist to a set and to its closure coincide -/
/-
**Metric.infEDist_closure** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：infEDist_closure : infEDist x (closure s) = infEDist x s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Metric.infEDist_anti`：infEDist_anti (h : s subseteq t) : infEDist x t <=
 infEDist x s
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `ENNReal.le_of_forall_pos_le_add`：le_of_forall_pos_le_add (h : forall ε :
 Real>=0, 0 < ε -> b < ∞ -> a <= b + ε) : a <= b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `ENNReal.lt_add_right`：lt_add_right (ha : a != ∞) (hb : b != 0) : a < a +
 b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.infEDist_lt_iff`：infEDist_lt_iff {r : Real>=0∞} : infEDist x s < 
r ↔ exists y in s, edist x y < r
· 使用定理 `EMetric.mem_closure_iff`：mem_closure_iff : x in closure s ↔ forall ε > 0
, exists y in s, edist x y < ε
· 使用定理 `Metric.infEDist_le_edist_of_mem`：infEDist_le_edist_of_mem (h : y in s) :
 infEDist x s <= edist x y
· 使用定理 `PseudoEMetricSpace.edist_triangle`：∀ {α : Type u} [self : PseudoEMetricS
pace α] (x y z : α), edist x z ≤ edist x y + edist y z
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `ENNReal.add_halves`：∀ (a : ENNReal), a / 2 + a / 2 = a

--- 原说明 ---
The edist to a set and to its closure coincide
-/
theorem infEDist_closure : infEDist x (closure s) = infEDist x s := by
  refine le_antisymm (infEDist_anti subset_closure) ?_
  refine ENNReal.le_of_forall_pos_le_add fun ε εpos h => ?_
  have ε0 : 0 < (ε / 2 : ℝ≥0∞) := by simpa [pos_iff_ne_zero] using εpos
  have : infEDist x (closure s) < infEDist x (closure s) + ε / 2 :=
    ENNReal.lt_add_right h.ne ε0.ne'
  obtain ⟨y : α, ycs : y ∈ closure s, hy : edist x y < infEDist x (closure s) + ↑ε / 2⟩ :=
    infEDist_lt_iff.mp this
  obtain ⟨z : α, zs : z ∈ s, dyz : edist y z < ↑ε / 2⟩ := EMetric.mem_closure_iff.1 ycs (ε / 2) ε0
  calc
    infEDist x s ≤ edist x z := infEDist_le_edist_of_mem zs
    _ ≤ edist x y + edist y z := edist_triangle _ _ _
    _ ≤ infEDist x (closure s) + ε / 2 + ε / 2 := add_le_add (le_of_lt hy) (le_of_lt dyz)
    _ = infEDist x (closure s) + ↑ε := by rw [add_assoc, ENNReal.add_halves]

/-- A point belongs to the closure of `s` iff its infimum edistance to this set vanishes -/
/-
**Metric.mem_closure_iff_infEDist_zero** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：mem_closure_iff_infEDist_zero : x in closure s ↔ infEDist x s = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Metric.infEDist_closure`：infEDist_closure : infEDist x (closure s) = inf
EDist x s
· 使用定理 `Metric.infEDist_zero_of_mem`：infEDist_zero_of_mem (h : x in s) : infEDis
t x s = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `EMetric.mem_closure_iff`：mem_closure_iff : x in closure s ↔ forall ε > 0
, exists y in s, edist x y < ε
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.infEDist_lt_iff`：infEDist_lt_iff {r : Real>=0∞} : infEDist x s < 
r ↔ exists y in s, edist x y < r

--- 原说明 ---
A point belongs to the closure of `s` iff its infimum edistance to this set vani
shes
-/
theorem mem_closure_iff_infEDist_zero : x ∈ closure s ↔ infEDist x s = 0 :=
  ⟨fun h => by
    rw [← infEDist_closure]
    exact infEDist_zero_of_mem h,
   fun h =>
    EMetric.mem_closure_iff.2 fun ε εpos => infEDist_lt_iff.mp <| by rwa [h]⟩

/-- Given a closed set `s`, a point belongs to `s` iff its infimum edistance to this set vanishes -/
/-
**Metric.mem_iff_infEDist_zero_of_closed** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：mem_iff_infEDist_zero_of_closed (h : IsClosed s) : x in s ↔ infEDist x s =
 0
参数：h : IsClosed s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Metric.mem_closure_iff_infEDist_zero`：mem_closure_iff_infEDist_zero : x 
in closure s ↔ infEDist x s = 0
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Given a closed set `s`, a point belongs to `s` iff its infimum edistance to this
 set vanishes
-/
theorem mem_iff_infEDist_zero_of_closed (h : IsClosed s) : x ∈ s ↔ infEDist x s = 0 := by
  rw [← mem_closure_iff_infEDist_zero, h.closure_eq]

/-- The infimum edistance of a point to a set is positive if and only if the point is not in the
closure of the set. -/
/-
**Metric.infEDist_pos_iff_notMem_closure** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：infEDist_pos_iff_notMem_closure {x : α} {E : Set α} : 0 < infEDist x E ↔ x
 ∉ closure E
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.mem_closure_iff_infEDist_zero`：mem_closure_iff_infEDist_zero : x 
in closure s ↔ infEDist x s = 0
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
The infimum edistance of a point to a set is positive if and only if the point i
s not in the
closure of the set.
-/
theorem infEDist_pos_iff_notMem_closure {x : α} {E : Set α} :
    0 < infEDist x E ↔ x ∉ closure E := by
  rw [mem_closure_iff_infEDist_zero, pos_iff_ne_zero]
/-
**Metric.infEDist_closure_pos_iff_notMem_closure** 是 Mathlib 中的一个定理，位于命名空间 `Metr
ic`。
形式化陈述：infEDist_closure_pos_iff_notMem_closure {x : α} {E : Set α} : 0 < infEDist
 x (closure E) ↔ x ∉ closure E
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.infEDist_closure`：infEDist_closure : infEDist x (closure s) = inf
EDist x s
· 使用定理 `Metric.infEDist_pos_iff_notMem_closure`：infEDist_pos_iff_notMem_closure 
{x : α} {E : Set α} : 0 < infEDist x E ↔ x ∉ closure E
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem infEDist_closure_pos_iff_notMem_closure {x : α} {E : Set α} :
    0 < infEDist x (closure E) ↔ x ∉ closure E := by
  rw [infEDist_closure, infEDist_pos_iff_notMem_closure]
/-
**Metric.exists_real_pos_lt_infEDist_of_notMem_closure** 是 Mathlib 中的一个定理，位于命名空间
 `Metric`。
形式化陈述：exists_real_pos_lt_infEDist_of_notMem_closure {x : α} {E : Set α} (h : x ∉
 closure E) : exists ε : Real, 0 < ε ∧ ENNReal.ofReal ε < infEDist x E
参数：h : x ∉ closure E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.lt_iff_exists_real_btwn`：lt_iff_exists_real_btwn : a < b ↔ exist
s r : Real, 0 <= r ∧ a < ENNReal.ofReal r ∧ (ENNReal.ofReal r : Real>=0∞) < b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Metric.infEDist_pos_iff_notMem_closure`：infEDist_pos_iff_notMem_closure 
{x : α} {E : Set α} : 0 < infEDist x E ↔ x ∉ closure E
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.ofReal_pos`：ofReal_pos {p : Real} : 0 < ENNReal.ofReal p ↔ 0 < p
-/
theorem exists_real_pos_lt_infEDist_of_notMem_closure {x : α} {E : Set α} (h : x ∉ closure E) :
    ∃ ε : ℝ, 0 < ε ∧ ENNReal.ofReal ε < infEDist x E := by
  rw [← infEDist_pos_iff_notMem_closure, ENNReal.lt_iff_exists_real_btwn] at h
  rcases h with ⟨ε, ⟨_, ⟨ε_pos, ε_lt⟩⟩⟩
  exact ⟨ε, ⟨ENNReal.ofReal_pos.mp ε_pos, ε_lt⟩⟩
/-
**Metric.disjoint_closedEBall_of_lt_infEDist** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：disjoint_closedEBall_of_lt_infEDist {r : Real>=0∞} (h : r < infEDist x s) 
: Disjoint (Metric.closedEBall x r) s
参数：h : r < infEDist x s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `Metric.infEDist_le_edist_of_mem`：infEDist_le_edist_of_mem (h : y in s) :
 infEDist x s <= edist x y
· 使用定理 `PseudoEMetricSpace.edist_comm`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x y : α), edist x y = edist y x
· 使用定理 `Metric.mem_closedEBall`：∀ {α : Type u} [inst : PseudoEMetricSpace α] {x 
y : α} {ε : ENNReal}, y ∈ Metric.closedEBall x ε ↔ edist y x ≤ ε
-/
theorem disjoint_closedEBall_of_lt_infEDist {r : ℝ≥0∞} (h : r < infEDist x s) :
    Disjoint (Metric.closedEBall x r) s := by
  rw [disjoint_left]
  intro y hy h'y
  apply lt_irrefl (infEDist x s)
  calc
    infEDist x s ≤ edist x y := infEDist_le_edist_of_mem h'y
    _ ≤ r := by rwa [Metric.mem_closedEBall, edist_comm] at hy
    _ < infEDist x s := h

/-- The infimum edistance is invariant under isometries -/
/-
**Metric.infEDist_image** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：infEDist_image (hΦ : Isometry Φ) : infEDist (Φ x) (Φ '' t) = infEDist x t
参数：hΦ : Isometry Φ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iInf_image`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLattice α] {
γ : Type u_8} {f : β → γ} {g : γ → α} {t : Set β},   ⨅ c ∈ f '' t, g c = ⨅ b ∈ t
…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Isometry.edist_eq`：edist_eq (hf : Isometry f) (x y : α) : edist (f x) (f
 y) = edist x y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The infimum edistance is invariant under isometries
-/
theorem infEDist_image (hΦ : Isometry Φ) : infEDist (Φ x) (Φ '' t) = infEDist x t := by
  simp only [infEDist, iInf_image, hΦ.edist_eq]

@[to_additive (attr := simp)]
/-
**Metric.infEDist_smul** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：infEDist_smul {M} [SMul M α] [IsIsometricSMul M α] (c : M) (x : α) (s : Se
t α) : infEDist (c • x) (c • s) = infEDist x s
参数：c : M；x : α；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.infEDist_image`：infEDist_image (hΦ : Isometry Φ) : infEDist (Φ x)
 (Φ '' t) = infEDist x t
· 使用定理 `IsIsometricSMul.isometry_smul`：∀ {M : Type u} (X : Type w) {inst : Pseud
oEMetricSpace X} {inst_1 : SMul M X} [self : IsIsometricSMul M X] (c : M),   Iso
metry fun x => c • …
-/
theorem infEDist_smul {M} [SMul M α] [IsIsometricSMul M α] (c : M) (x : α) (s : Set α) :
    infEDist (c • x) (c • s) = infEDist x s :=
  infEDist_image (isometry_smul _ _)
/-
**Metric._root_.IsOpen.exists_iUnion_isClosed** 是 Mathlib 中的一个定理，位于命名空间 `Metric`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsOpen.exists_iUnion_isClosed {U : Set α} (hU : IsOpen U) :
    ∃ F : ℕ → Set α, (∀ n, IsClosed (F n)) ∧ (∀ n, F n ⊆ U) ∧ ⋃ n, F n = U ∧ Monotone F := by
  obtain ⟨a, a_pos, a_lt_one⟩ : ∃ a : ℝ≥0∞, 0 < a ∧ a < 1 := exists_between zero_lt_one
  let F := fun n : ℕ => (fun x => infEDist x Uᶜ) ⁻¹' Ici (a ^ n)
  have F_subset : ∀ n, F n ⊆ U := fun n x hx ↦ by
    by_contra h
    have : infEDist x Uᶜ ≠ 0 := ((ENNReal.pow_pos a_pos _).trans_le hx).ne'
    exact this (infEDist_zero_of_mem h)
  refine ⟨F, fun n => IsClosed.preimage continuous_infEDist isClosed_Ici, F_subset, ?_, ?_⟩
  · show ⋃ n, F n = U
    refine Subset.antisymm (by simp only [iUnion_subset_iff, F_subset, forall_const]) fun x hx => ?_
    have : x ∉ Uᶜ := by simpa using hx
    rw [mem_iff_infEDist_zero_of_closed hU.isClosed_compl] at this
    have B : 0 < infEDist x Uᶜ := by simpa [pos_iff_ne_zero] using this
    have : Filter.Tendsto (fun n => a ^ n) atTop (𝓝 0) :=
      ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one a_lt_one
    rcases ((tendsto_order.1 this).2 _ B).exists with ⟨n, hn⟩
    simp only [mem_iUnion]
    exact ⟨n, hn.le⟩
  show Monotone F
  intro m n hmn x hx
  simp only [F, mem_Ici, mem_preimage] at hx ⊢
  apply le_trans (pow_le_pow_right_of_le_one' a_lt_one.le hmn) hx
/-
**Metric._root_.IsCompact.exists_infEDist_eq_edist** 是 Mathlib 中的一个定理，位于命名空间 `Me
tric`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsCompact.exists_infEDist_eq_edist (hs : IsCompact s) (hne : s.Nonempty) (x : α) :
    ∃ y ∈ s, infEDist x s = edist x y := by
  have A : Continuous fun y => edist x y := by fun_prop
  obtain ⟨y, ys, hy⟩ := hs.exists_isMinOn hne A.continuousOn
  exact ⟨y, ys, le_antisymm (infEDist_le_edist_of_mem ys) (by rwa [le_infEDist])⟩
/-
**Metric.exists_pos_forall_lt_edist** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：exists_pos_forall_lt_edist (hs : IsCompact s) (ht : IsClosed t) (hst : Dis
joint s t) : exists r : Real>=0, 0 < r ∧ forall x in s, forall y in t, (r : Real
>=0∞) < edist x y
参数：hs : IsCompact s；ht : IsClosed t；hst : Disjoint s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FloorSemiring.instZeroLEOneClass`：∀ {α : Type u_2} [inst : Semiring α] [
inst_1 : PartialOrder α] [FloorSemiring α], ZeroLEOneClass α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsCompact.exists_isMinOn`：IsCompact.exists_isMinOn [ClosedIicTopology α]
 {s : Set β} (hs : IsCompact s) (ne_s : s.Nonempty) {f : β -> α} (hf : Continuou
sOn f s) : exi…
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Metric.continuous_infEDist`：continuous_infEDist : Continuous fun x => in
fEDist x s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Disjoint.le_bot`：Disjoint.le_bot : Disjoint a b -> a ⊓ b <= ⊥
· 使用定理 `Metric.mem_iff_infEDist_zero_of_closed`：mem_iff_infEDist_zero_of_closed 
(h : IsClosed s) : x in s ↔ infEDist x s = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.lt_iff_exists_nnreal_btwn`：lt_iff_exists_nnreal_btwn : a < b ↔ e
xists r : Real>=0, a < r ∧ (r : Real>=0∞) < b
· 使用定理 `ENNReal.coe_pos`：∀ {r : NNReal}, 0 < ↑r ↔ 0 < r
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Metric.le_infEDist`：le_infEDist {d} : d <= infEDist x s ↔ forall y in s,
 d <= edist x y
-/
theorem exists_pos_forall_lt_edist (hs : IsCompact s) (ht : IsClosed t) (hst : Disjoint s t) :
    ∃ r : ℝ≥0, 0 < r ∧ ∀ x ∈ s, ∀ y ∈ t, (r : ℝ≥0∞) < edist x y := by
  rcases s.eq_empty_or_nonempty with (rfl | hne)
  · use 1
    simp
  obtain ⟨x, hx, h⟩ := hs.exists_isMinOn hne continuous_infEDist.continuousOn
  have : 0 < infEDist x t :=
    pos_iff_ne_zero.2 fun H => hst.le_bot ⟨hx, (mem_iff_infEDist_zero_of_closed ht).mpr H⟩
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 this with ⟨r, h₀, hr⟩
  exact ⟨r, ENNReal.coe_pos.mp h₀, fun y hy z hz => hr.trans_le <| le_infEDist.1 (h hy) z hz⟩
/-
**Metric.infEDist_prod** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：infEDist_prod (x : α × β) (s : Set α) (t : Set β) : infEDist x (s ×ˢ t) = 
max (infEDist x.1 s) (infEDist x.2 t)
参数：x : α × β；s : Set α；t : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iInf_prod`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : Comple
teLattice α] {f : β × γ → α}, ⨅ x, f x = ⨅ i, ⨅ j, f (i, j)
· 使用定理 `iInf_and`：∀ {α : Type u_1} [inst : CompleteLattice α] {p q : Prop} {s : 
p ∧ q → α}, iInf s = ⨅ (h₁ : p), ⨅ (h₂ : q), s ⋯
· 使用定理 `iInf_sup_eq`：∀ {α : Type u} {ι : Sort w} [inst : Order.Coframe α] (f : ι
 → α) (a : α), (⨅ i, f i) ⊔ a = ⨅ i, f i ⊔ a
· 使用定理 `sup_iInf_eq`：∀ {α : Type u} {ι : Sort w} [inst : Order.Coframe α] (a : α
) (f : ι → α), a ⊔ ⨅ i, f i = ⨅ i, a ⊔ f i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem infEDist_prod (x : α × β) (s : Set α) (t : Set β) :
    infEDist x (s ×ˢ t) = max (infEDist x.1 s) (infEDist x.2 t) := by
  simp_rw +singlePass [infEDist, Prod.edist_eq, iInf_prod, Set.mem_prod, iInf_and, iInf_sup_eq,
    sup_iInf_eq, iInf_sup_eq, sup_iInf_eq]

end InfEDist

/-! ### The Hausdorff distance as a function into `ℝ≥0∞`. -/

/-- The Hausdorff edistance between two sets is the smallest `r` such that each set
is contained in the `r`-neighborhood of the other one -/
irreducible_def hausdorffEDist {α : Type u} [PseudoEMetricSpace α] (s t : Set α) : ℝ≥0∞ :=
  (⨆ x ∈ s, infEDist x t) ⊔ ⨆ y ∈ t, infEDist y s

section HausdorffEDist

variable [PseudoEMetricSpace α] [PseudoEMetricSpace β] {x y : α} {s t u : Set α} {Φ : α → β}

/-- The Hausdorff edistance of a set to itself vanishes. -/
@[simp]
/-
**Metric.hausdorffEDist_self** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：hausdorffEDist_self : hausdorffEDist s s = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.hausdorffEDist_def`：∀ {α : Type u_2} [inst : PseudoEMetricSpace α
] (s t : Set α),   Metric.hausdorffEDist s t = max (⨆ x ∈ s, Metric.infEDist x t
) (⨆ y ∈ t, Met…
· 使用定理 `sup_idem`：sup_idem (a : α) : a ⊔ a = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Metric.infEDist_zero_of_mem`：infEDist_zero_of_mem (h : x in s) : infEDis
t x s = 0

--- 原说明 ---
The Hausdorff edistance of a set to itself vanishes.
-/
theorem hausdorffEDist_self : hausdorffEDist s s = 0 := by
  simp only [hausdorffEDist_def, sup_idem, ENNReal.iSup_eq_zero]
  exact fun x hx => infEDist_zero_of_mem hx

/-- The Hausdorff edistances of `s` to `t` and of `t` to `s` coincide. -/
/-
**Metric.hausdorffEDist_comm** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：hausdorffEDist_comm : hausdorffEDist s t = hausdorffEDist t s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.hausdorffEDist_def`：∀ {α : Type u_2} [inst : PseudoEMetricSpace α
] (s t : Set α),   Metric.hausdorffEDist s t = max (⨆ x ∈ s, Metric.infEDist x t
) (⨆ y ∈ t, Met…
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a

--- 原说明 ---
The Hausdorff edistances of `s` to `t` and of `t` to `s` coincide.
-/
theorem hausdorffEDist_comm : hausdorffEDist s t = hausdorffEDist t s := by
  simp only [hausdorffEDist_def]; apply sup_comm

/-- Bounding the Hausdorff edistance by bounding the edistance of any point
in each set to the other set -/
/-
**Metric.hausdorffEDist_le_of_infEDist** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：hausdorffEDist_le_of_infEDist {r : Real>=0∞} (H1 : forall x in s, infEDist
 x t <= r) (H2 : forall x in t, infEDist x s <= r) : hausdorffEDist s t <= r
参数：H1 : forall x in s, infEDist x t <= r；H2 : forall x in t, infEDist x s <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.hausdorffEDist_def`：∀ {α : Type u_2} [inst : PseudoEMetricSpace α
] (s t : Set α),   Metric.hausdorffEDist s t = max (⨆ x ∈ s, Metric.infEDist x t
) (⨆ y ∈ t, Met…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a

--- 原说明 ---
Bounding the Hausdorff edistance by bounding the edistance of any point
in each set to the other set
-/
theorem hausdorffEDist_le_of_infEDist {r : ℝ≥0∞} (H1 : ∀ x ∈ s, infEDist x t ≤ r)
    (H2 : ∀ x ∈ t, infEDist x s ≤ r) : hausdorffEDist s t ≤ r := by
  simp only [hausdorffEDist_def, sup_le_iff, iSup_le_iff]
  exact ⟨H1, H2⟩

/-- Bounding the Hausdorff edistance by exhibiting, for any point in each set,
another point in the other set at controlled distance -/
/-
**Metric.hausdorffEDist_le_of_mem_edist** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：hausdorffEDist_le_of_mem_edist {r : Real>=0∞} (H1 : forall x in s, exists 
y in t, edist x y <= r) (H2 : forall x in t, exists y in s, edist x y <= r) : ha
usdorffEDist s t <= r
参数：H1 : forall x in s, exists y in t, edist x y <= r；H2 : forall x in t, exists 
y in s, edist x y <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.hausdorffEDist_le_of_infEDist`：hausdorffEDist_le_of_infEDist {r :
 Real>=0∞} (H1 : forall x in s, infEDist x t <= r) (H2 : forall x in t, infEDist
 x s <= r) : hausdorffEDis…
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Metric.infEDist_le_edist_of_mem`：infEDist_le_edist_of_mem (h : y in s) :
 infEDist x s <= edist x y

--- 原说明 ---
Bounding the Hausdorff edistance by exhibiting, for any point in each set,
another point in the other set at controlled distance
-/
theorem hausdorffEDist_le_of_mem_edist {r : ℝ≥0∞} (H1 : ∀ x ∈ s, ∃ y ∈ t, edist x y ≤ r)
    (H2 : ∀ x ∈ t, ∃ y ∈ s, edist x y ≤ r) : hausdorffEDist s t ≤ r := by
  refine hausdorffEDist_le_of_infEDist (fun x xs ↦ ?_) (fun x xt ↦ ?_)
  · rcases H1 x xs with ⟨y, yt, hy⟩
    exact le_trans (infEDist_le_edist_of_mem yt) hy
  · rcases H2 x xt with ⟨y, ys, hy⟩
    exact le_trans (infEDist_le_edist_of_mem ys) hy

/-- The distance to a set is controlled by the Hausdorff distance. -/
/-
**Metric.infEDist_le_hausdorffEDist_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：infEDist_le_hausdorffEDist_of_mem (h : x in s) : infEDist x t <= hausdorff
EDist s t
参数：h : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.hausdorffEDist_def`：∀ {α : Type u_2} [inst : PseudoEMetricSpace α
] (s t : Set α),   Metric.hausdorffEDist s t = max (⨆ x ∈ s, Metric.infEDist x t
) (⨆ y ∈ t, Met…
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_iSup₂`：le_iSup₂ {f : forall i, κ i -> α} (i : ι) (j : κ i) : f i j <=
 ⨆ (i) (j), f i j
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b

--- 原说明 ---
The distance to a set is controlled by the Hausdorff distance.
-/
theorem infEDist_le_hausdorffEDist_of_mem (h : x ∈ s) : infEDist x t ≤ hausdorffEDist s t := by
  rw [hausdorffEDist_def]
  refine le_trans ?_ le_sup_left
  exact le_iSup₂ (α := ℝ≥0∞) x h

/-- If the Hausdorff distance is `< r`, then any point in one of the sets has
a corresponding point at distance `< r` in the other set. -/
/-
**Metric.exists_edist_lt_of_hausdorffEDist_lt** 是 Mathlib 中的一个定理，位于命名空间 `Metric`
。
形式化陈述：exists_edist_lt_of_hausdorffEDist_lt {r : Real>=0∞} (h : x in s) (H : haus
dorffEDist s t < r) : exists y in t, edist x y < r
参数：h : x in s；H : hausdorffEDist s t < r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.infEDist_lt_iff`：infEDist_lt_iff {r : Real>=0∞} : infEDist x s < 
r ↔ exists y in s, edist x y < r
· 使用定理 `Metric.infEDist_le_hausdorffEDist_of_mem`：infEDist_le_hausdorffEDist_of_
mem (h : x in s) : infEDist x t <= hausdorffEDist s t

--- 原说明 ---
If the Hausdorff distance is `< r`, then any point in one of the sets has
a corresponding point at distance `< r` in the other set.
-/
theorem exists_edist_lt_of_hausdorffEDist_lt {r : ℝ≥0∞} (h : x ∈ s) (H : hausdorffEDist s t < r) :
    ∃ y ∈ t, edist x y < r :=
  infEDist_lt_iff.mp <|
    calc
      infEDist x t ≤ hausdorffEDist s t := infEDist_le_hausdorffEDist_of_mem h
      _ < r := H

/-- The distance from `x` to `s` or `t` is controlled in terms of the Hausdorff distance
between `s` and `t`. -/
/-
**Metric.infEDist_le_infEDist_add_hausdorffEDist** 是 Mathlib 中的一个定理，位于命名空间 `Metr
ic`。
形式化陈述：infEDist_le_infEDist_add_hausdorffEDist : infEDist x t <= infEDist x s + h
ausdorffEDist s t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.le_of_forall_pos_le_add`：le_of_forall_pos_le_add (h : forall ε :
 Real>=0, 0 < ε -> b < ∞ -> a <= b + ε) : a <= b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `ENNReal.lt_add_right`：lt_add_right (ha : a != ∞) (hb : b != 0) : a < a +
 b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.add_lt_top`：∀ {a b : ENNReal}, a + b < ⊤ ↔ a < ⊤ ∧ b < ⊤
· 使用定理 `Metric.infEDist_lt_iff`：infEDist_lt_iff {r : Real>=0∞} : infEDist x s < 
r ↔ exists y in s, edist x y < r
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Metric.exists_edist_lt_of_hausdorffEDist_lt`：exists_edist_lt_of_hausdorf
fEDist_lt {r : Real>=0∞} (h : x in s) (H : hausdorffEDist s t < r) : exists y in
 t, edist x y < r
· 使用定理 `Metric.infEDist_le_edist_of_mem`：infEDist_le_edist_of_mem (h : y in s) :
 infEDist x s <= edist x y
· 使用定理 `PseudoEMetricSpace.edist_triangle`：∀ {α : Type u} [self : PseudoEMetricS
pace α] (x y z : α), edist x z ≤ edist x y + edist y z
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `add_add_add_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c d 
: G), a + b + (c + d) = a + c + (b + d)
· 使用定理 `ENNReal.add_halves`：∀ (a : ENNReal), a / 2 + a / 2 = a

--- 原说明 ---
The distance from `x` to `s` or `t` is controlled in terms of the Hausdorff dist
ance
between `s` and `t`.
-/
theorem infEDist_le_infEDist_add_hausdorffEDist :
    infEDist x t ≤ infEDist x s + hausdorffEDist s t :=
  ENNReal.le_of_forall_pos_le_add fun ε εpos h => by
    have ε0 : (ε / 2 : ℝ≥0∞) ≠ 0 := by simpa [pos_iff_ne_zero] using εpos
    have : infEDist x s < infEDist x s + ε / 2 :=
      ENNReal.lt_add_right (ENNReal.add_lt_top.1 h).1.ne ε0
    obtain ⟨y : α, ys : y ∈ s, dxy : edist x y < infEDist x s + ↑ε / 2⟩ := infEDist_lt_iff.mp this
    have : hausdorffEDist s t < hausdorffEDist s t + ε / 2 :=
      ENNReal.lt_add_right (ENNReal.add_lt_top.1 h).2.ne ε0
    obtain ⟨z : α, zt : z ∈ t, dyz : edist y z < hausdorffEDist s t + ↑ε / 2⟩ :=
      exists_edist_lt_of_hausdorffEDist_lt ys this
    calc
      infEDist x t ≤ edist x z := infEDist_le_edist_of_mem zt
      _ ≤ edist x y + edist y z := edist_triangle _ _ _
      _ ≤ infEDist x s + ε / 2 + (hausdorffEDist s t + ε / 2) := add_le_add dxy.le dyz.le
      _ = infEDist x s + hausdorffEDist s t + ε := by
        rw [add_add_add_comm, ENNReal.add_halves]

/-- The Hausdorff edistance is invariant under isometries. -/
/-
**Metric.hausdorffEDist_image** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：hausdorffEDist_image (h : Isometry Φ) : hausdorffEDist (Φ '' s) (Φ '' t) =
 hausdorffEDist s t
参数：h : Isometry Φ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.hausdorffEDist_def`：∀ {α : Type u_2} [inst : PseudoEMetricSpace α
] (s t : Set α),   Metric.hausdorffEDist s t = max (⨆ x ∈ s, Metric.infEDist x t
) (⨆ y ∈ t, Met…
· 使用定理 `iSup_image`：iSup_image {γ} {f : β -> γ} {g : γ -> α} {t : Set β} : ⨆ c i
n f '' t, g c = ⨆ b in t, g (f b)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Metric.infEDist_image`：infEDist_image (hΦ : Isometry Φ) : infEDist (Φ x)
 (Φ '' t) = infEDist x t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The Hausdorff edistance is invariant under isometries.
-/
theorem hausdorffEDist_image (h : Isometry Φ) :
    hausdorffEDist (Φ '' s) (Φ '' t) = hausdorffEDist s t := by
  simp only [hausdorffEDist_def, iSup_image, infEDist_image h]

/-- The Hausdorff distance is controlled by the diameter of the union. -/
/-
**Metric.hausdorffEDist_le_ediam** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：hausdorffEDist_le_ediam (hs : s.Nonempty) (ht : t.Nonempty) : hausdorffEDi
st s t <= Metric.ediam (s union t)
参数：hs : s.Nonempty；ht : t.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.hausdorffEDist_le_of_mem_edist`：hausdorffEDist_le_of_mem_edist {r
 : Real>=0∞} (H1 : forall x in s, exists y in t, edist x y <= r) (H2 : forall x 
in t, exists y in s, edist …
· 使用定理 `Metric.edist_le_ediam_of_mem`：edist_le_ediam_of_mem (hx : x in s) (hy : 
y in s) : edist x y <= ediam s
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t

--- 原说明 ---
The Hausdorff distance is controlled by the diameter of the union.
-/
theorem hausdorffEDist_le_ediam (hs : s.Nonempty) (ht : t.Nonempty) :
    hausdorffEDist s t ≤ Metric.ediam (s ∪ t) := by
  rcases hs with ⟨x, xs⟩
  rcases ht with ⟨y, yt⟩
  refine hausdorffEDist_le_of_mem_edist ?_ ?_
  · intro z hz
    exact ⟨y, yt, Metric.edist_le_ediam_of_mem (subset_union_left hz) (subset_union_right yt)⟩
  · intro z hz
    exact ⟨x, xs, Metric.edist_le_ediam_of_mem (subset_union_right hz) (subset_union_left xs)⟩

/-- The Hausdorff distance satisfies the triangle inequality. -/
/-
**Metric.hausdorffEDist_triangle** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：hausdorffEDist_triangle : hausdorffEDist s u <= hausdorffEDist s t + hausd
orffEDist t u
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.hausdorffEDist_def`：∀ {α : Type u_2} [inst : PseudoEMetricSpace α
] (s t : Set α),   Metric.hausdorffEDist s t = max (⨆ x ∈ s, Metric.infEDist x t
) (⨆ y ∈ t, Met…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Metric.infEDist_le_infEDist_add_hausdorffEDist`：infEDist_le_infEDist_add
_hausdorffEDist : infEDist x t <= infEDist x s + hausdorffEDist s t
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Metric.infEDist_le_hausdorffEDist_of_mem`：infEDist_le_hausdorffEDist_of_
mem (h : x in s) : infEDist x t <= hausdorffEDist s t
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Metric.hausdorffEDist_comm`：hausdorffEDist_comm : hausdorffEDist s t = h
ausdorffEDist t s
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The Hausdorff distance satisfies the triangle inequality.
-/
theorem hausdorffEDist_triangle : hausdorffEDist s u ≤ hausdorffEDist s t + hausdorffEDist t u := by
  rw [hausdorffEDist_def]
  simp only [sup_le_iff, iSup_le_iff]
  constructor
  · change ∀ x ∈ s, infEDist x u ≤ hausdorffEDist s t + hausdorffEDist t u
    exact fun x xs =>
      calc
        infEDist x u ≤ infEDist x t + hausdorffEDist t u :=
          infEDist_le_infEDist_add_hausdorffEDist
        _ ≤ hausdorffEDist s t + hausdorffEDist t u := by grw [infEDist_le_hausdorffEDist_of_mem xs]
  · change ∀ x ∈ u, infEDist x s ≤ hausdorffEDist s t + hausdorffEDist t u
    exact fun x xu =>
      calc
        infEDist x s ≤ infEDist x t + hausdorffEDist t s :=
          infEDist_le_infEDist_add_hausdorffEDist
        _ ≤ hausdorffEDist u t + hausdorffEDist t s := by grw [infEDist_le_hausdorffEDist_of_mem xu]
        _ = hausdorffEDist s t + hausdorffEDist t u := by simp [hausdorffEDist_comm, add_comm]

/-- Two sets are at zero Hausdorff edistance if and only if they have the same closure. -/
/-
**Metric.hausdorffEDist_zero_iff_closure_eq_closure** 是 Mathlib 中的一个定理，位于命名空间 `M
etric`。
形式化陈述：hausdorffEDist_zero_iff_closure_eq_closure : hausdorffEDist s t = 0 ↔ clos
ure s = closure t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Metric.hausdorffEDist_def`：∀ {α : Type u_2} [inst : PseudoEMetricSpace α
] (s t : Set α),   Metric.hausdorffEDist s t = max (⨆ x ∈ s, Metric.infEDist x t
) (⨆ y ∈ t, Met…
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsClosed.closure_subset_iff`：IsClosed.closure_subset_iff (h₁ : IsClosed 
t) : closure s subseteq t ↔ s subseteq t
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Two sets are at zero Hausdorff edistance if and only if they have the same closu
re.
-/
theorem hausdorffEDist_zero_iff_closure_eq_closure :
    hausdorffEDist s t = 0 ↔ closure s = closure t := by
  simp [hausdorffEDist_def, ← subset_def, ← mem_closure_iff_infEDist_zero,
    subset_antisymm_iff, isClosed_closure.closure_subset_iff]

/-- The Hausdorff edistance between a set and its closure vanishes. -/
@[simp]
/-
**Metric.hausdorffEDist_self_closure** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：hausdorffEDist_self_closure : hausdorffEDist s (closure s) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.hausdorffEDist_zero_iff_closure_eq_closure`：hausdorffEDist_zero_i
ff_closure_eq_closure : hausdorffEDist s t = 0 ↔ closure s = closure t
· 使用定理 `closure_closure`：closure_closure : closure (closure s) = closure s

--- 原说明 ---
The Hausdorff edistance between a set and its closure vanishes.
-/
theorem hausdorffEDist_self_closure : hausdorffEDist s (closure s) = 0 := by
  rw [hausdorffEDist_zero_iff_closure_eq_closure, closure_closure]

/-- Replacing a set by its closure does not change the Hausdorff edistance. -/
@[simp]
/-
**Metric.hausdorffEDist_closure_left** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：hausdorffEDist_closure_left : hausdorffEDist (closure s) t = hausdorffEDis
t s t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Metric.hausdorffEDist_triangle`：hausdorffEDist_triangle : hausdorffEDist
 s u <= hausdorffEDist s t + hausdorffEDist t u
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.hausdorffEDist_comm`：hausdorffEDist_comm : hausdorffEDist s t = h
ausdorffEDist t s
· 使用定理 `Metric.hausdorffEDist_self_closure`：hausdorffEDist_self_closure : hausdo
rffEDist s (closure s) = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Replacing a set by its closure does not change the Hausdorff edistance.
-/
theorem hausdorffEDist_closure_left : hausdorffEDist (closure s) t = hausdorffEDist s t := by
  refine le_antisymm ?_ ?_
  · calc
      _ ≤ hausdorffEDist (closure s) s + hausdorffEDist s t := hausdorffEDist_triangle
      _ = hausdorffEDist s t := by simp [hausdorffEDist_comm]
  · calc
      _ ≤ hausdorffEDist s (closure s) + hausdorffEDist (closure s) t := hausdorffEDist_triangle
      _ = hausdorffEDist (closure s) t := by simp

/-- Replacing a set by its closure does not change the Hausdorff edistance. -/
@[simp]
/-
**Metric.hausdorffEDist_closure_right** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：hausdorffEDist_closure_right : hausdorffEDist s (closure t) = hausdorffEDi
st s t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.hausdorffEDist_comm`：hausdorffEDist_comm : hausdorffEDist s t = h
ausdorffEDist t s
· 使用定理 `Metric.hausdorffEDist_closure_left`：hausdorffEDist_closure_left : hausdo
rffEDist (closure s) t = hausdorffEDist s t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Replacing a set by its closure does not change the Hausdorff edistance.
-/
theorem hausdorffEDist_closure_right : hausdorffEDist s (closure t) = hausdorffEDist s t := by
  simp [@hausdorffEDist_comm _ _ s _]

/-- The Hausdorff edistance between sets or their closures is the same. -/
/-
**Metric.hausdorffEDist_closure** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：hausdorffEDist_closure : hausdorffEDist (closure s) (closure t) = hausdorf
fEDist s t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.hausdorffEDist_closure_right`：hausdorffEDist_closure_right : haus
dorffEDist s (closure t) = hausdorffEDist s t
· 使用定理 `Metric.hausdorffEDist_closure_left`：hausdorffEDist_closure_left : hausdo
rffEDist (closure s) t = hausdorffEDist s t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The Hausdorff edistance between sets or their closures is the same.
-/
theorem hausdorffEDist_closure : hausdorffEDist (closure s) (closure t) = hausdorffEDist s t := by
  simp

/-- Two closed sets are at zero Hausdorff edistance if and only if they coincide. -/
/-
**Metric._root_.IsClosed.hausdorffEDist_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Metr
ic`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two closed sets are at zero Hausdorff edistance if and only if they coincide.
-/
theorem _root_.IsClosed.hausdorffEDist_zero_iff (hs : IsClosed s) (ht : IsClosed t) :
    hausdorffEDist s t = 0 ↔ s = t := by
  rw [hausdorffEDist_zero_iff_closure_eq_closure, hs.closure_eq, ht.closure_eq]

/-- The Hausdorff edistance to the empty set is infinite. -/
/-
**Metric.hausdorffEDist_empty** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：hausdorffEDist_empty (ne : s.Nonempty) : hausdorffEDist s ∅ = ∞
参数：ne : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.infEDist_le_hausdorffEDist_of_mem`：infEDist_le_hausdorffEDist_of_
mem (h : x in s) : infEDist x t <= hausdorffEDist s t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.infEDist_empty`：infEDist_empty : infEDist x ∅ = ∞

--- 原说明 ---
The Hausdorff edistance to the empty set is infinite.
-/
theorem hausdorffEDist_empty (ne : s.Nonempty) : hausdorffEDist s ∅ = ∞ := by
  rcases ne with ⟨x, xs⟩
  have : infEDist x ∅ ≤ hausdorffEDist s ∅ := infEDist_le_hausdorffEDist_of_mem xs
  simpa using this

/-- If a set is at finite Hausdorff edistance of a nonempty set, it is nonempty. -/
/-
**Metric.nonempty_of_hausdorffEDist_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：nonempty_of_hausdorffEDist_ne_top (hs : s.Nonempty) (fin : hausdorffEDist 
s t != ⊤) : t.Nonempty
参数：hs : s.Nonempty；fin : hausdorffEDist s t != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `Metric.hausdorffEDist_empty`：hausdorffEDist_empty (ne : s.Nonempty) : ha
usdorffEDist s ∅ = ∞
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If a set is at finite Hausdorff edistance of a nonempty set, it is nonempty.
-/
theorem nonempty_of_hausdorffEDist_ne_top (hs : s.Nonempty) (fin : hausdorffEDist s t ≠ ⊤) :
    t.Nonempty :=
  t.eq_empty_or_nonempty.resolve_left fun ht ↦ fin (ht.symm ▸ hausdorffEDist_empty hs)
/-
**Metric.empty_or_nonempty_of_hausdorffEDist_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `M
etric`。
形式化陈述：empty_or_nonempty_of_hausdorffEDist_ne_top (fin : hausdorffEDist s t != ⊤)
 : (s = ∅ ∧ t = ∅) ∨ (s.Nonempty ∧ t.Nonempty)
参数：fin : hausdorffEDist s t != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Metric.nonempty_of_hausdorffEDist_ne_top`：nonempty_of_hausdorffEDist_ne_
top (hs : s.Nonempty) (fin : hausdorffEDist s t != ⊤) : t.Nonempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.hausdorffEDist_comm`：hausdorffEDist_comm : hausdorffEDist s t = h
ausdorffEDist t s
-/
theorem empty_or_nonempty_of_hausdorffEDist_ne_top (fin : hausdorffEDist s t ≠ ⊤) :
    (s = ∅ ∧ t = ∅) ∨ (s.Nonempty ∧ t.Nonempty) := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · rcases t.eq_empty_or_nonempty with rfl | ht
    · exact Or.inl ⟨rfl, rfl⟩
    · rw [hausdorffEDist_comm] at fin
      exact Or.inr ⟨nonempty_of_hausdorffEDist_ne_top ht fin, ht⟩
  · exact Or.inr ⟨hs, nonempty_of_hausdorffEDist_ne_top hs fin⟩

@[simp]
/-
**Metric.hausdorffEDist_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：hausdorffEDist_singleton : hausdorffEDist {x} {y} = edist x y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.hausdorffEDist_def`：∀ {α : Type u_2} [inst : PseudoEMetricSpace α
] (s t : Set α),   Metric.hausdorffEDist s t = max (⨆ x ∈ s, Metric.infEDist x t
) (⨆ y ∈ t, Met…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iSup_singleton`：iSup_singleton {f : β -> α} {b : β} : ⨆ x in (singleton 
b : Set β), f x = f b
· 使用定理 `Metric.infEDist_singleton`：infEDist_singleton : infEDist x {y} = edist x
 y
· 使用定理 `PseudoEMetricSpace.edist_comm`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x y : α), edist x y = edist y x
· 使用定理 `max_self`：∀ {α : Type u_1} [inst : LinearOrder α] (a : α), max a a = a
-/
theorem hausdorffEDist_singleton : hausdorffEDist {x} {y} = edist x y := by
  simp_rw [hausdorffEDist, iSup_singleton, infEDist_singleton]
  nth_rw 2 [edist_comm]
  exact max_self _
/-
**Metric.hausdorffEDist_iUnion_le** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：hausdorffEDist_iUnion_le {ι : Sort*} {s t : ι -> Set α} : hausdorffEDist (
⋃ i, s i) (⋃ i, t i) <= ⨆ i, hausdorffEDist (s i) (t i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.hausdorffEDist_def`：∀ {α : Type u_2} [inst : PseudoEMetricSpace α
] (s t : Set α),   Metric.hausdorffEDist s t = max (⨆ x ∈ s, Metric.infEDist x t
) (⨆ y ∈ t, Met…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iSup_iUnion`：iSup_iUnion (s : ι -> Set α) (f : α -> β) : ⨆ a in ⋃ i, s i
, f a = ⨆ (i) (a in s i), f a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Metric.infEDist_iUnion`：infEDist_iUnion (f : ι -> Set α) (x : α) : infED
ist x (⋃ i, f i) = ⨅ i, infEDist x (f i)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i
· 使用定理 `le_iSup_of_le`：le_iSup_of_le (i : ι) (h : a <= f i) : a <= iSup f
· 使用定理 `le_max_of_le_left`：le_max_of_le_left : a <= b -> a <= max b c
· 使用定理 `le_iSup₂_of_le`：le_iSup₂_of_le {f : forall i, κ i -> α} (i : ι) (j : κ i
) (h : a <= f i j) : a <= ⨆ (i) (j), f i j
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `le_max_of_le_right`：le_max_of_le_right : a <= c -> a <= max b c
-/
theorem hausdorffEDist_iUnion_le {ι : Sort*} {s t : ι → Set α} :
    hausdorffEDist (⋃ i, s i) (⋃ i, t i) ≤ ⨆ i, hausdorffEDist (s i) (t i) := by
  simp_rw [hausdorffEDist, max_le_iff, iSup_iUnion, iSup_le_iff, infEDist_iUnion]
  constructor <;> refine fun i x hx => (iInf_le _ i).trans <| le_iSup_of_le i ?_
  · exact le_max_of_le_left <| le_iSup₂_of_le x hx le_rfl
  · exact le_max_of_le_right <| le_iSup₂_of_le x hx le_rfl
/-
**Metric.hausdorffEDist_union_le** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：hausdorffEDist_union_le {s₁ s₂ t₁ t₂ : Set α} : hausdorffEDist (s₁ union s
₂) (t₁ union t₂) <= max (hausdorffEDist s₁ t₁) (hausdorffEDist s₂ t₂)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.union_eq_iUnion`：union_eq_iUnion {s₁ s₂ : Set α} : s₁ union s₂ = ⋃ b
 : Bool, cond b s₁ s₂
· 使用定理 `sup_eq_iSup`：sup_eq_iSup (x y : α) : x ⊔ y = ⨆ b : Bool, cond b x y
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Metric.hausdorffEDist_iUnion_le`：hausdorffEDist_iUnion_le {ι : Sort*} {s
 t : ι -> Set α} : hausdorffEDist (⋃ i, s i) (⋃ i, t i) <= ⨆ i, hausdorffEDist (
s i) (t i)
-/
theorem hausdorffEDist_union_le {s₁ s₂ t₁ t₂ : Set α} :
    hausdorffEDist (s₁ ∪ s₂) (t₁ ∪ t₂) ≤ max (hausdorffEDist s₁ t₁) (hausdorffEDist s₂ t₂) := by
  simp_rw [union_eq_iUnion, sup_eq_iSup]
  convert! hausdorffEDist_iUnion_le with (_ | _)
/-
**Metric.hausdorffEDist_prod_le** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：hausdorffEDist_prod_le {s₁ t₁ : Set α} {s₂ t₂ : Set β} : hausdorffEDist (s
₁ ×ˢ s₂) (t₁ ×ˢ t₂) <= max (hausdorffEDist s₁ t₁) (hausdorffEDist s₂ t₂)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_forall_ge`：∀ {α : Type u_2} [inst : Preorder α] {a b : α}, (∀ (c :
 α), a ≤ c → b ≤ c) → b ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.hausdorffEDist_def`：∀ {α : Type u_2} [inst : PseudoEMetricSpace α
] (s t : Set α),   Metric.hausdorffEDist s t = max (⨆ x ∈ s, Metric.infEDist x t
) (⨆ y ∈ t, Met…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Metric.infEDist_prod`：infEDist_prod (x : α × β) (s : Set α) (t : Set β) 
: infEDist x (s ×ˢ t) = max (infEDist x.1 s) (infEDist x.2 t)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem hausdorffEDist_prod_le {s₁ t₁ : Set α} {s₂ t₂ : Set β} :
    hausdorffEDist (s₁ ×ˢ s₂) (t₁ ×ˢ t₂) ≤ max (hausdorffEDist s₁ t₁) (hausdorffEDist s₂ t₂) := by
  refine le_of_forall_ge fun _ _ => ?_
  simp_all only [hausdorffEDist, infEDist_prod, max_le_iff, iSup_le_iff, mem_prod, true_and,
    implies_true]

end HausdorffEDist -- section

end Metric -- namespace

namespace EMetric

open Metric

@[deprecated (since := "2026-01-08")]
noncomputable alias infEdist := infEDist

@[deprecated (since := "2026-01-08")]
alias infEdist_empty := infEDist_empty

@[deprecated (since := "2026-01-08")] alias le_infEdist := le_infEDist
@[deprecated (since := "2026-01-08")] alias infEdist_union := infEDist_union
@[deprecated (since := "2026-01-08")] alias infEdist_iUnion := infEDist_iUnion
@[deprecated (since := "2026-01-08")] alias infEdist_biUnion := infEDist_biUnion
@[deprecated (since := "2026-01-08")] alias infEdist_singleton := infEDist_singleton
@[deprecated (since := "2026-01-08")] alias infEdist_le_edist_of_mem := infEDist_le_edist_of_mem
@[deprecated (since := "2026-01-08")] alias infEdist_zero_of_mem := infEDist_zero_of_mem
@[deprecated (since := "2026-01-08")] alias infEdist_anti := infEDist_anti
@[deprecated (since := "2026-01-08")] alias infEdist_lt_iff := infEDist_lt_iff

@[deprecated (since := "2026-01-08")]
alias infEdist_le_infEdist_add_edist := infEDist_le_infEDist_add_edist

@[deprecated (since := "2026-01-08")]
alias infEdist_le_edist_add_infEdist := infEDist_le_edist_add_infEDist

@[deprecated (since := "2026-01-08")]
alias edist_le_infEdist_add_ediam := edist_le_infEDist_add_ediam

@[deprecated (since := "2026-01-08")] alias continuous_infEdist := continuous_infEDist
@[deprecated (since := "2026-01-08")] alias infEdist_closure := infEDist_closure

@[deprecated (since := "2026-01-08")]
alias mem_closure_iff_infEdist_zero := mem_closure_iff_infEDist_zero

@[deprecated (since := "2026-01-08")]
alias mem_iff_infEdist_zero_of_closed := mem_iff_infEDist_zero_of_closed

@[deprecated (since := "2026-01-08")]
alias infEdist_pos_iff_notMem_closure := infEDist_pos_iff_notMem_closure

@[deprecated (since := "2026-01-08")]
alias infEdist_closure_pos_iff_notMem_closure := infEDist_closure_pos_iff_notMem_closure

@[deprecated (since := "2026-01-08")]
alias exists_real_pos_lt_infEdist_of_notMem_closure := exists_real_pos_lt_infEDist_of_notMem_closure

@[deprecated (since := "2026-01-08")]
alias disjoint_closedBall_of_lt_infEdist := disjoint_closedEBall_of_lt_infEDist

@[deprecated (since := "2026-01-08")] alias infEdist_image := infEDist_image
@[deprecated (since := "2026-01-08")] alias infEdist_vadd := infEDist_vadd
@[to_additive existing, deprecated (since := "2026-01-08")] alias infEdist_smul := infEDist_smul

@[deprecated (since := "2026-01-08")]
alias _root_.IsCompact.exists_infEdist_eq_edist := _root_.IsCompact.exists_infEDist_eq_edist

@[deprecated (since := "2026-01-08")] alias exists_pos_forall_lt_edist := exists_pos_forall_lt_edist
@[deprecated (since := "2026-01-08")] alias infEdist_prod := infEDist_prod

@[deprecated (since := "2026-01-08")] noncomputable alias hausdorffEdist := hausdorffEDist
@[deprecated (since := "2026-01-08")] alias hausdorffEdist_def := hausdorffEDist_def
@[deprecated (since := "2026-01-08")] alias hausdorffEdist_self := hausdorffEDist_self
@[deprecated (since := "2026-01-08")] alias hausdorffEdist_comm := hausdorffEDist_comm

@[deprecated (since := "2026-01-08")]
alias hausdorffEdist_le_of_infEdist := hausdorffEDist_le_of_infEDist

@[deprecated (since := "2026-01-08")]
alias hausdorffEdist_le_of_mem_edist := hausdorffEDist_le_of_mem_edist

@[deprecated (since := "2026-01-08")]
alias infEdist_le_hausdorffEdist_of_mem := infEDist_le_hausdorffEDist_of_mem

@[deprecated (since := "2026-01-08")]
alias exists_edist_lt_of_hausdorffEdist_lt := exists_edist_lt_of_hausdorffEDist_lt

@[deprecated (since := "2026-01-08")]
alias infEdist_le_infEdist_add_hausdorffEdist := infEDist_le_infEDist_add_hausdorffEDist

@[deprecated (since := "2026-01-08")] alias hausdorffEdist_image := hausdorffEDist_image
@[deprecated (since := "2026-01-08")] alias hausdorffEdist_le_ediam := hausdorffEDist_le_ediam
@[deprecated (since := "2026-01-08")] alias hausdorffEdist_triangle := hausdorffEDist_triangle

@[deprecated (since := "2026-01-08")]
alias hausdorffEdist_zero_iff_closure_eq_closure := hausdorffEDist_zero_iff_closure_eq_closure

@[deprecated (since := "2026-01-08")]
alias hausdorffEdist_self_closure := hausdorffEDist_self_closure

@[deprecated (since := "2026-01-08")] alias hausdorffEdist_closure₁ := hausdorffEDist_closure_left
@[deprecated (since := "2026-01-08")] alias hausdorffEdist_closure₂ := hausdorffEDist_closure_right
@[deprecated (since := "2026-01-08")] alias hausdorffEdist_closure := hausdorffEDist_closure

@[deprecated (since := "2026-01-08")]
alias hausdorffEdist_zero_iff_eq_of_closed := IsClosed.hausdorffEDist_zero_iff

@[deprecated (since := "2026-01-08")] alias hausdorffEdist_empty := hausdorffEDist_empty

@[deprecated (since := "2026-01-08")]
alias nonempty_of_hausdorffEdist_ne_top := nonempty_of_hausdorffEDist_ne_top

@[deprecated (since := "2026-01-08")]
alias empty_or_nonempty_of_hausdorffEdist_ne_top := empty_or_nonempty_of_hausdorffEDist_ne_top

@[deprecated (since := "2026-01-08")] alias hausdorffEdist_singleton := hausdorffEDist_singleton
@[deprecated (since := "2026-01-08")] alias hausdorffEdist_iUnion_le := hausdorffEDist_iUnion_le
@[deprecated (since := "2026-01-08")] alias hausdorffEdist_union_le := hausdorffEDist_union_le
@[deprecated (since := "2026-01-08")] alias hausdorffEdist_prod_le := hausdorffEDist_prod_le

end EMetric

/-! Now, we turn to the same notions in metric spaces. To avoid the difficulties related to
`sInf` and `sSup` on `ℝ` (which is only conditionally complete), we use the notions in `ℝ≥0∞`
formulated in terms of the edistance, and coerce them to `ℝ`.
Then their properties follow readily from the corresponding properties in `ℝ≥0∞`,
modulo some tedious rewriting of inequalities from one to the other. -/

namespace Metric

section

variable [PseudoMetricSpace α] [PseudoMetricSpace β] {s t u : Set α} {x y : α} {Φ : α → β}

/-! ### Distance of a point to a set as a function into `ℝ`. -/

/-- The minimal distance of a point to a set -/
/-
**Metric.infDist** 是 Mathlib 中的一个定义，位于命名空间 `Metric`。
形式化陈述：infDist (x : α) (s : Set α) : Real
参数：x : α；s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The minimal distance of a point to a set
-/
def infDist (x : α) (s : Set α) : ℝ :=
  ENNReal.toReal (infEDist x s)
/-
**Metric.infDist_eq_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：infDist_eq_iInf : infDist x s = ⨅ y : s, dist x y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.infDist.eq_1`：∀ {α : Type u} [inst : PseudoMetricSpace α] (x : α)
 (s : Set α), Metric.infDist x s = (Metric.infEDist x s).toReal
· 使用定理 `Metric.infEDist.eq_1`：∀ {α : Type u} [inst : PseudoEMetricSpace α] (x : 
α) (s : Set α), Metric.infEDist x s = ⨅ y ∈ s, edist x y
· 使用定理 `iInf_subtype'`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] {p : ι → Prop} {f : (i : ι) → p i → α},   ⨅ i, ⨅ (h : p i), f i h = ⨅ x, f ↑x 
⋯
· 使用定理 `ENNReal.toReal_iInf`：toReal_iInf (hf : forall i, f i != ∞) : (iInf f).to
Real = ⨅ i, (f i).toReal
· 使用定理 `edist_ne_top`：edist_ne_top (x y : α) : edist x y != ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dist_edist`：dist_edist (x y : α) : dist x y = (edist x y).toReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem infDist_eq_iInf : infDist x s = ⨅ y : s, dist x y := by
  rw [infDist, infEDist, iInf_subtype', ENNReal.toReal_iInf]
  · simp only [dist_edist]
  · finiteness

/-- The minimal distance is always nonnegative -/
/-
**Metric.infDist_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：infDist_nonneg : 0 <= infDist x s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.toReal_nonneg`：∀ {a : ENNReal}, 0 ≤ a.toReal

--- 原说明 ---
The minimal distance is always nonnegative
-/
theorem infDist_nonneg : 0 ≤ infDist x s := toReal_nonneg

/-- The minimal distance to the empty set is 0 (if you want to have the more reasonable
value `∞` instead, use `Metric.infEDist`, which takes values in `ℝ≥0∞`) -/
@[simp]
/-
**Metric.infDist_empty** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：infDist_empty : infDist x ∅ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.infEDist_empty`：infEDist_empty : infEDist x ∅ = ∞
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The minimal distance to the empty set is 0 (if you want to have the more reasona
ble
value `∞` instead, use `Metric.infEDist`, which takes values in `ℝ≥0∞`)
-/
theorem infDist_empty : infDist x ∅ = 0 := by simp [infDist]
/-
**Metric.isGLB_infDist** 是 Mathlib 中的一个引理，位于命名空间 `Metric`。
形式化陈述：isGLB_infDist (hs : s.Nonempty) : IsGLB ((dist x ·) '' s) (infDist x s)
参数：hs : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.infDist_eq_iInf`：infDist_eq_iInf : infDist x s = ⨅ y : s, dist x 
y
· 使用定理 `sInf_image'`：∀ {α : Type u_1} {β : Type u_2} [inst : InfSet α] {s : Set 
β} {f : β → α}, sInf (f '' s) = ⨅ a, f ↑a
· 使用定理 `isGLB_csInf`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s
 : Set α},   s.Nonempty → autoParam (BddBelow s) isGLB_csInf._auto_1 → IsGLB s (
s…
· 使用定理 `Set.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set
 α}, s.Nonempty → (f '' s).Nonempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma isGLB_infDist (hs : s.Nonempty) : IsGLB ((dist x ·) '' s) (infDist x s) := by
  simpa [infDist_eq_iInf, sInf_image']
    using isGLB_csInf (hs.image _) ⟨0, by simp [lowerBounds]⟩

/-- In a metric space, the minimal edistance to a nonempty set is finite. -/
/-
**Metric.infEDist_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：infEDist_ne_top (h : s.Nonempty) : infEDist x s != ∞
参数：h : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_top_of_le_ne_top`：ne_top_of_le_ne_top (hb : b != ⊤) (hab : a <= b) : 
a != ⊤
· 使用定理 `edist_ne_top`：edist_ne_top (x y : α) : edist x y != ⊤
· 使用定理 `Metric.infEDist_le_edist_of_mem`：infEDist_le_edist_of_mem (h : y in s) :
 infEDist x s <= edist x y

--- 原说明 ---
In a metric space, the minimal edistance to a nonempty set is finite.
-/
theorem infEDist_ne_top (h : s.Nonempty) : infEDist x s ≠ ∞ := by
  rcases h with ⟨y, hy⟩
  exact ne_top_of_le_ne_top (edist_ne_top _ _) (infEDist_le_edist_of_mem hy)

@[deprecated (since := "2026-01-08")]
alias infEdist_ne_top := infEDist_ne_top

@[simp]
/-
**Metric.infEDist_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：infEDist_eq_top_iff : infEDist x s = ∞ ↔ s = ∅
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Metric.infEDist_empty`：infEDist_empty : infEDist x ∅ = ∞
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem infEDist_eq_top_iff : infEDist x s = ∞ ↔ s = ∅ := by
  rcases s.eq_empty_or_nonempty with rfl | hs <;> simp [*, Nonempty.ne_empty, infEDist_ne_top]

@[deprecated (since := "2026-01-08")]
alias infEdist_eq_top_iff := infEDist_eq_top_iff

/-- The minimal distance of a point to a set containing it vanishes. -/
/-
**Metric.infDist_zero_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：infDist_zero_of_mem (h : x in s) : infDist x s = 0
参数：h : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.infEDist_zero_of_mem`：infEDist_zero_of_mem (h : x in s) : infEDis
t x s = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The minimal distance of a point to a set containing it vanishes.
-/
theorem infDist_zero_of_mem (h : x ∈ s) : infDist x s = 0 := by
  simp [infEDist_zero_of_mem h, infDist]

/-- The minimal distance to a singleton is the distance to the unique point in this singleton. -/
@[simp]
/-
**Metric.infDist_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：infDist_singleton : infDist x {y} = dist x y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.infEDist_singleton`：infEDist_singleton : infEDist x {y} = edist x
 y
· 使用定理 `dist_edist`：dist_edist (x y : α) : dist x y = (edist x y).toReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The minimal distance to a singleton is the distance to the unique point in this 
singleton.
-/
theorem infDist_singleton : infDist x {y} = dist x y := by simp [infDist, dist_edist]

/-- The minimal distance to a set is bounded by the distance to any point in this set. -/
/-
**Metric.infDist_le_dist_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：infDist_le_dist_of_mem (h : y in s) : infDist x s <= dist x y
参数：h : y in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_edist`：dist_edist (x y : α) : dist x y = (edist x y).toReal
· 使用定理 `Metric.infDist.eq_1`：∀ {α : Type u} [inst : PseudoMetricSpace α] (x : α)
 (s : Set α), Metric.infDist x s = (Metric.infEDist x s).toReal
· 使用定理 `ENNReal.toReal_mono`：toReal_mono (hb : b != ∞) (h : a <= b) : a.toReal <
= b.toReal
· 使用定理 `edist_ne_top`：edist_ne_top (x y : α) : edist x y != ⊤
· 使用定理 `Metric.infEDist_le_edist_of_mem`：infEDist_le_edist_of_mem (h : y in s) :
 infEDist x s <= edist x y

--- 原说明 ---
The minimal distance to a set is bounded by the distance to any point in this se
t.
-/
theorem infDist_le_dist_of_mem (h : y ∈ s) : infDist x s ≤ dist x y := by
  rw [dist_edist, infDist]
  exact ENNReal.toReal_mono (edist_ne_top _ _) (infEDist_le_edist_of_mem h)

/-- The minimal distance is monotone with respect to inclusion. -/
/-
**Metric.infDist_le_infDist_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：infDist_le_infDist_of_subset (h : s subseteq t) (hs : s.Nonempty) : infDis
t x t <= infDist x s
参数：h : s subseteq t；hs : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.toReal_mono`：toReal_mono (hb : b != ∞) (h : a <= b) : a.toReal <
= b.toReal
· 使用定理 `Metric.infEDist_ne_top`：infEDist_ne_top (h : s.Nonempty) : infEDist x s 
!= ∞
· 使用定理 `Metric.infEDist_anti`：infEDist_anti (h : s subseteq t) : infEDist x t <=
 infEDist x s

--- 原说明 ---
The minimal distance is monotone with respect to inclusion.
-/
theorem infDist_le_infDist_of_subset (h : s ⊆ t) (hs : s.Nonempty) : infDist x t ≤ infDist x s :=
  ENNReal.toReal_mono (infEDist_ne_top hs) (infEDist_anti h)
/-
**Metric.le_infDist** 是 Mathlib 中的一个引理，位于命名空间 `Metric`。
形式化陈述：le_infDist {r : Real} (hs : s.Nonempty) : r <= infDist x s ↔ forall ⦃y⦄, y
 in s -> r <= dist x y
参数：hs : s.Nonempty。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.ofReal_le_iff_le_toReal`：ofReal_le_iff_le_toReal {a : Real} {b :
 Real>=0∞} (hb : b != ∞) : ENNReal.ofReal a <= b ↔ a <= ENNReal.toReal b
· 使用定理 `Metric.infEDist_ne_top`：infEDist_ne_top (h : s.Nonempty) : infEDist x s 
!= ∞
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `edist_ne_top`：edist_ne_top (x y : α) : edist x y != ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma le_infDist {r : ℝ} (hs : s.Nonempty) : r ≤ infDist x s ↔ ∀ ⦃y⦄, y ∈ s → r ≤ dist x y := by
  simp_rw [infDist, ← ENNReal.ofReal_le_iff_le_toReal (infEDist_ne_top hs), le_infEDist,
    ENNReal.ofReal_le_iff_le_toReal (edist_ne_top _ _), ← dist_edist]

/-- The minimal distance to a set `s` is `< r` iff there exists a point in `s` at distance `< r`. -/
/-
**Metric.infDist_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：infDist_lt_iff {r : Real} (hs : s.Nonempty) : infDist x s < r ↔ exists y i
n s, dist x y < r
参数：hs : s.Nonempty。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Metric.le_infDist`：le_infDist {r : Real} (hs : s.Nonempty) : r <= infDis
t x s ↔ forall ⦃y⦄, y in s -> r <= dist x y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The minimal distance to a set `s` is `< r` iff there exists a point in `s` at di
stance `< r`.
-/
theorem infDist_lt_iff {r : ℝ} (hs : s.Nonempty) : infDist x s < r ↔ ∃ y ∈ s, dist x y < r := by
  simp [← not_le, le_infDist hs]

/-- The minimal distance from `x` to `s` is bounded by the distance from `y` to `s`, modulo
the distance between `x` and `y`. -/
/-
**Metric.infDist_le_infDist_add_dist** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：infDist_le_infDist_add_dist : infDist x s <= infDist y s + dist x y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.infDist.eq_1`：∀ {α : Type u} [inst : PseudoMetricSpace α] (x : α)
 (s : Set α), Metric.infDist x s = (Metric.infEDist x s).toReal
· 使用定理 `dist_edist`：dist_edist (x y : α) : dist x y = (edist x y).toReal
· 使用定理 `ENNReal.toReal_le_add'`：toReal_le_add' (hle : a <= b + c) (hb : b = ∞ ->
 a = ∞) (hc : c = ∞ -> a = ∞) : a.toReal <= b.toReal + c.toReal
· 使用定理 `Metric.infEDist_le_infEDist_add_edist`：infEDist_le_infEDist_add_edist : 
infEDist x s <= infEDist y s + edist x y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `edist_ne_top`：edist_ne_top (x y : α) : edist x y != ⊤

--- 原说明 ---
The minimal distance from `x` to `s` is bounded by the distance from `y` to `s`,
 modulo
the distance between `x` and `y`.
-/
theorem infDist_le_infDist_add_dist : infDist x s ≤ infDist y s + dist x y := by
  rw [infDist, infDist, dist_edist]
  refine ENNReal.toReal_le_add' infEDist_le_infEDist_add_edist ?_ (flip absurd (edist_ne_top _ _))
  simp only [infEDist_eq_top_iff, imp_self]
/-
**Metric.notMem_of_dist_lt_infDist** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：notMem_of_dist_lt_infDist (h : dist x y < infDist x s) : y ∉ s
参数：h : dist x y < infDist x s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Metric.infDist_le_dist_of_mem`：infDist_le_dist_of_mem (h : y in s) : inf
Dist x s <= dist x y
-/
theorem notMem_of_dist_lt_infDist (h : dist x y < infDist x s) : y ∉ s := fun hy =>
  h.not_ge <| infDist_le_dist_of_mem hy
/-
**Metric.disjoint_ball_infDist** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：disjoint_ball_infDist : Disjoint (ball x (infDist x s)) s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `Metric.notMem_of_dist_lt_infDist`：notMem_of_dist_lt_infDist (h : dist x 
y < infDist x s) : y ∉ s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.mem_ball'`：mem_ball' : y in ball x ε ↔ dist x y < ε
-/
theorem disjoint_ball_infDist : Disjoint (ball x (infDist x s)) s :=
  disjoint_left.2 fun _y hy => notMem_of_dist_lt_infDist <| mem_ball'.1 hy
/-
**Metric.ball_infDist_subset_compl** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：ball_infDist_subset_compl : ball x (infDist x s) subseteq sᶜ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.subset_compl_right`：∀ {α : Type u_1} {s t : Set α}, Disjoint s 
t → s ⊆ tᶜ
· 使用定理 `Metric.disjoint_ball_infDist`：disjoint_ball_infDist : Disjoint (ball x (
infDist x s)) s
-/
theorem ball_infDist_subset_compl : ball x (infDist x s) ⊆ sᶜ :=
  (disjoint_ball_infDist (s := s)).subset_compl_right
/-
**Metric.ball_infDist_compl_subset** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：ball_infDist_compl_subset : ball x (infDist x sᶜ) subseteq s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Metric.ball_infDist_subset_compl`：ball_infDist_subset_compl : ball x (in
fDist x s) subseteq sᶜ
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
-/
theorem ball_infDist_compl_subset : ball x (infDist x sᶜ) ⊆ s :=
  ball_infDist_subset_compl.trans_eq (compl_compl s)
/-
**Metric.disjoint_closedBall_of_lt_infDist** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：disjoint_closedBall_of_lt_infDist {r : Real} (h : r < infDist x s) : Disjo
int (closedBall x r) s
参数：h : r < infDist x s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.mono_left`：Disjoint.mono_left (h : a <= b) : Disjoint b c -> Di
sjoint a c
· 使用定理 `Metric.closedBall_subset_ball`：closedBall_subset_ball (h : ε₁ < ε₂) : cl
osedBall x ε₁ subseteq ball x ε₂
· 使用定理 `Metric.disjoint_ball_infDist`：disjoint_ball_infDist : Disjoint (ball x (
infDist x s)) s
-/
theorem disjoint_closedBall_of_lt_infDist {r : ℝ} (h : r < infDist x s) :
    Disjoint (closedBall x r) s :=
  disjoint_ball_infDist.mono_left <| closedBall_subset_ball h
/-
**Metric.dist_le_infDist_add_diam** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：dist_le_infDist_add_diam (hs : IsBounded s) (hy : y in s) : dist x y <= in
fDist x s + diam s
参数：hs : IsBounded s；hy : y in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.infDist.eq_1`：∀ {α : Type u} [inst : PseudoMetricSpace α] (x : α)
 (s : Set α), Metric.infDist x s = (Metric.infEDist x s).toReal
· 使用定理 `Metric.diam.eq_1`：∀ {α : Type u} [inst : PseudoMetricSpace α] (s : Set α
), Metric.diam s = (Metric.ediam s).toReal
· 使用定理 `dist_edist`：dist_edist (x y : α) : dist x y = (edist x y).toReal
· 使用定理 `ENNReal.toReal_le_add`：toReal_le_add (hle : a <= b + c) (hb : b != ∞) (h
c : c != ∞) : a.toReal <= b.toReal + c.toReal
· 使用定理 `Metric.edist_le_infEDist_add_ediam`：edist_le_infEDist_add_ediam (hy : y 
in s) : edist x y <= infEDist x s + Metric.ediam s
· 使用定理 `Metric.infEDist_ne_top`：infEDist_ne_top (h : s.Nonempty) : infEDist x s 
!= ∞
· 使用定理 `Bornology.IsBounded.ediam_ne_top`：∀ {α : Type u} {s : Set α} [inst : Pse
udoMetricSpace α], Bornology.IsBounded s → Metric.ediam s ≠ ⊤
-/
theorem dist_le_infDist_add_diam (hs : IsBounded s) (hy : y ∈ s) :
    dist x y ≤ infDist x s + diam s := by
  rw [infDist, diam, dist_edist]
  exact toReal_le_add (edist_le_infEDist_add_ediam hy) (infEDist_ne_top ⟨y, hy⟩) hs.ediam_ne_top

variable (s)

/-- The minimal distance to a set is Lipschitz in point with constant 1 -/
/-
**Metric.lipschitz_infDist_pt** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：lipschitz_infDist_pt : LipschitzWith 1 (infDist · s)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.of_le_add`：∀ {α : Type u} [inst : PseudoMetricSpace α] {f 
: α → ℝ}, (∀ (x y : α), f x ≤ f y + dist x y) → LipschitzWith 1 f
· 使用定理 `Metric.infDist_le_infDist_add_dist`：infDist_le_infDist_add_dist : infDis
t x s <= infDist y s + dist x y

--- 原说明 ---
The minimal distance to a set is Lipschitz in point with constant 1
-/
theorem lipschitz_infDist_pt : LipschitzWith 1 (infDist · s) :=
  LipschitzWith.of_le_add fun _ _ => infDist_le_infDist_add_dist

/-- The minimal distance to a set is uniformly continuous in point -/
/-
**Metric.uniformContinuous_infDist_pt** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：uniformContinuous_infDist_pt : UniformContinuous (infDist · s)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.uniformContinuous`：∀ {α : Type u} {β : Type v} [inst : Pse
udoEMetricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   L
ipschitzWith K f → Un…
· 使用定理 `Metric.lipschitz_infDist_pt`：lipschitz_infDist_pt : LipschitzWith 1 (inf
Dist · s)

--- 原说明 ---
The minimal distance to a set is uniformly continuous in point
-/
theorem uniformContinuous_infDist_pt : UniformContinuous (infDist · s) :=
  (lipschitz_infDist_pt s).uniformContinuous

/-- The minimal distance to a set is continuous in point -/
@[continuity, fun_prop]
/-
**Metric.continuous_infDist_pt** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：continuous_infDist_pt : Continuous (infDist · s)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.continuous`：UniformContinuous.continuous (hf : Uniform
Continuous f) : Continuous f
· 使用定理 `Metric.uniformContinuous_infDist_pt`：uniformContinuous_infDist_pt : Unif
ormContinuous (infDist · s)

--- 原说明 ---
The minimal distance to a set is continuous in point
-/
theorem continuous_infDist_pt : Continuous (infDist · s) :=
  (uniformContinuous_infDist_pt s).continuous

variable {s}

/-- The minimal distances to a set and its closure coincide. -/
/-
**Metric.infDist_closure** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：infDist_closure : infDist x (closure s) = infDist x s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.infEDist_closure`：infEDist_closure : infEDist x (closure s) = inf
EDist x s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The minimal distances to a set and its closure coincide.
-/
theorem infDist_closure : infDist x (closure s) = infDist x s := by
  simp [infDist, infEDist_closure]

/-- If a point belongs to the closure of `s`, then its infimum distance to `s` equals zero.
The converse is true provided that `s` is nonempty, see `Metric.mem_closure_iff_infDist_zero`. -/
/-
**Metric.infDist_zero_of_mem_closure** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：infDist_zero_of_mem_closure (hx : x in closure s) : infDist x s = 0
参数：hx : x in closure s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Metric.infDist_closure`：infDist_closure : infDist x (closure s) = infDis
t x s
· 使用定理 `Metric.infDist_zero_of_mem`：infDist_zero_of_mem (h : x in s) : infDist x
 s = 0

--- 原说明 ---
If a point belongs to the closure of `s`, then its infimum distance to `s` equal
s zero.
The converse is true provided that `s` is nonempty, see `Metric.mem_closure_iff_
infDist_zero`.
-/
theorem infDist_zero_of_mem_closure (hx : x ∈ closure s) : infDist x s = 0 := by
  rw [← infDist_closure]
  exact infDist_zero_of_mem hx

/-- A point belongs to the closure of `s` iff its infimum distance to this set vanishes. -/
/-
**Metric.mem_closure_iff_infDist_zero** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：mem_closure_iff_infDist_zero (h : s.Nonempty) : x in closure s ↔ infDist x
 s = 0
参数：h : s.Nonempty。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Metric.infEDist_ne_top`：infEDist_ne_top (h : s.Nonempty) : infEDist x s 
!= ∞
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A point belongs to the closure of `s` iff its infimum distance to this set vanis
hes.
-/
theorem mem_closure_iff_infDist_zero (h : s.Nonempty) : x ∈ closure s ↔ infDist x s = 0 := by
  simp [mem_closure_iff_infEDist_zero, infDist, ENNReal.toReal_eq_zero_iff, infEDist_ne_top h]
/-
**Metric.infDist_pos_iff_notMem_closure** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：infDist_pos_iff_notMem_closure (hs : s.Nonempty) : x ∉ closure s ↔ 0 < inf
Dist x s
参数：hs : s.Nonempty。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Metric.mem_closure_iff_infDist_zero`：mem_closure_iff_infDist_zero (h : s
.Nonempty) : x in closure s ↔ infDist x s = 0
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `LE.le.lt_iff_ne'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, b 
≤ a → (b < a ↔ a ≠ b)
· 使用定理 `Metric.infDist_nonneg`：infDist_nonneg : 0 <= infDist x s
-/
theorem infDist_pos_iff_notMem_closure (hs : s.Nonempty) :
    x ∉ closure s ↔ 0 < infDist x s :=
  (mem_closure_iff_infDist_zero hs).not.trans infDist_nonneg.lt_iff_ne'.symm

/-- Given a closed set `s`, a point belongs to `s` iff its infimum distance to this set vanishes -/
/-
**Metric._root_.IsClosed.mem_iff_infDist_zero** 是 Mathlib 中的一个定理，位于命名空间 `Metric`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a closed set `s`, a point belongs to `s` iff its infimum distance to this 
set vanishes
-/
theorem _root_.IsClosed.mem_iff_infDist_zero (h : IsClosed s) (hs : s.Nonempty) :
    x ∈ s ↔ infDist x s = 0 := by rw [← mem_closure_iff_infDist_zero hs, h.closure_eq]

/-- Given a closed set `s`, a point belongs to `s` iff its infimum distance to this set vanishes. -/
/-
**Metric._root_.IsClosed.notMem_iff_infDist_pos** 是 Mathlib 中的一个定理，位于命名空间 `Metri
c`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a closed set `s`, a point belongs to `s` iff its infimum distance to this 
set vanishes.
-/
theorem _root_.IsClosed.notMem_iff_infDist_pos (h : IsClosed s) (hs : s.Nonempty) :
    x ∉ s ↔ 0 < infDist x s := by
  simp [h.mem_iff_infDist_zero hs, infDist_nonneg.lt_iff_ne']
/-
**Metric.continuousAt_inv_infDist_pt** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：continuousAt_inv_infDist_pt (h : x ∉ closure s) : ContinuousAt (fun x => (
infDist x s)⁻¹) x
参数：h : x ∉ closure s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Metric.infDist_empty`：infDist_empty : infDist x ∅ = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousAt.inv₀`：∀ {α : Type u_1} {G₀ : Type u_3} [inst : Zero G₀] [in
st_1 : Inv G₀] [inst_2 : TopologicalSpace G₀] [ContinuousInv₀ G₀]   {f : α → G₀}
 {a : α…
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
· 使用定理 `instIsTopologicalDivisionRingReal`：IsTopologicalDivisionRing ℝ
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `Metric.continuous_infDist_pt`：continuous_infDist_pt : Continuous (infDis
t · s)
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Metric.mem_closure_iff_infDist_zero`：mem_closure_iff_infDist_zero (h : s
.Nonempty) : x in closure s ↔ infDist x s = 0
-/
theorem continuousAt_inv_infDist_pt (h : x ∉ closure s) :
    ContinuousAt (fun x ↦ (infDist x s)⁻¹) x := by
  rcases s.eq_empty_or_nonempty with (rfl | hs)
  · simp only [infDist_empty, continuousAt_const]
  · refine (continuous_infDist_pt s).continuousAt.inv₀ ?_
    rwa [Ne, ← mem_closure_iff_infDist_zero hs]

/-- The infimum distance is invariant under isometries. -/
/-
**Metric.infDist_image** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：infDist_image (hΦ : Isometry Φ) : infDist (Φ x) (Φ '' t) = infDist x t
参数：hΦ : Isometry Φ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.infEDist_image`：infEDist_image (hΦ : Isometry Φ) : infEDist (Φ x)
 (Φ '' t) = infEDist x t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The infimum distance is invariant under isometries.
-/
theorem infDist_image (hΦ : Isometry Φ) : infDist (Φ x) (Φ '' t) = infDist x t := by
  simp [infDist, infEDist_image hΦ]
/-
**Metric.infDist_inter_closedBall_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：infDist_inter_closedBall_of_mem (h : y in s) : infDist x (s inter closedBa
ll x (dist y x)) = infDist x s
参数：h : y in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.mem_closedBall`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x y 
: α} {ε : ℝ}, y ∈ Metric.closedBall x ε ↔ dist y x ≤ ε
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Metric.infDist_lt_iff`：infDist_lt_iff {r : Real} (hs : s.Nonempty) : inf
Dist x s < r ↔ exists y in s, dist x y < r
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Metric.infDist_le_dist_of_mem`：infDist_le_dist_of_mem (h : y in s) : inf
Dist x s <= dist x y
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `Metric.infDist_le_infDist_of_subset`：infDist_le_infDist_of_subset (h : s
 subseteq t) (hs : s.Nonempty) : infDist x t <= infDist x s
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
-/
theorem infDist_inter_closedBall_of_mem (h : y ∈ s) :
    infDist x (s ∩ closedBall x (dist y x)) = infDist x s := by
  replace h : y ∈ s ∩ closedBall x (dist y x) := ⟨h, mem_closedBall.2 le_rfl⟩
  refine le_antisymm ?_ (infDist_le_infDist_of_subset inter_subset_left ⟨y, h⟩)
  refine not_lt.1 fun hlt => ?_
  rcases (infDist_lt_iff ⟨y, h.1⟩).mp hlt with ⟨z, hzs, hz⟩
  rcases le_or_gt (dist z x) (dist y x) with hle | hlt
  · exact hz.not_ge (infDist_le_dist_of_mem ⟨hzs, hle⟩)
  · rw [dist_comm z, dist_comm y] at hlt
    exact (hlt.trans hz).not_ge (infDist_le_dist_of_mem h)
/-
**Metric._root_.IsCompact.exists_infDist_eq_dist** 是 Mathlib 中的一个定理，位于命名空间 `Metr
ic`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsCompact.exists_infDist_eq_dist (h : IsCompact s) (hne : s.Nonempty) (x : α) :
    ∃ y ∈ s, infDist x s = dist x y :=
  let ⟨y, hys, hy⟩ := h.exists_infEDist_eq_edist hne x
  ⟨y, hys, by rw [infDist, dist_edist, hy]⟩
/-
**Metric._root_.IsClosed.exists_infDist_eq_dist** 是 Mathlib 中的一个定理，位于命名空间 `Metri
c`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsClosed.exists_infDist_eq_dist [ProperSpace α] (h : IsClosed s) (hne : s.Nonempty)
    (x : α) : ∃ y ∈ s, infDist x s = dist x y := by
  rcases hne with ⟨z, hz⟩
  rw [← infDist_inter_closedBall_of_mem hz]
  set t := s ∩ closedBall x (dist z x)
  have htc : IsCompact t := (isCompact_closedBall x (dist z x)).inter_left h
  have htne : t.Nonempty := ⟨z, hz, mem_closedBall.2 le_rfl⟩
  obtain ⟨y, ⟨hys, -⟩, hyd⟩ : ∃ y ∈ t, infDist x t = dist x y := htc.exists_infDist_eq_dist htne x
  exact ⟨y, hys, hyd⟩
/-
**Metric.exists_mem_closure_infDist_eq_dist** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：exists_mem_closure_infDist_eq_dist [ProperSpace α] (hne : s.Nonempty) (x :
 α) : exists y in closure s, infDist x s = dist x y
参数：hne : s.Nonempty；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Metric.infDist_closure`：infDist_closure : infDist x (closure s) = infDis
t x s
· 使用定理 `IsClosed.exists_infDist_eq_dist`：∀ {α : Type u} [inst : PseudoMetricSpac
e α] {s : Set α} [ProperSpace α],   IsClosed s → s.Nonempty → ∀ (x : α), ∃ y ∈ s
, Metric.infDist x s …
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `Set.Nonempty.closure`：∀ {X : Type u} [inst : TopologicalSpace X] {s : Se
t X}, s.Nonempty → (closure s).Nonempty
-/
theorem exists_mem_closure_infDist_eq_dist [ProperSpace α] (hne : s.Nonempty) (x : α) :
    ∃ y ∈ closure s, infDist x s = dist x y := by
  simpa only [infDist_closure] using isClosed_closure.exists_infDist_eq_dist hne.closure x

/-! ### Distance of a point to a set as a function into `ℝ≥0`. -/

/-- The minimal distance of a point to a set as a `ℝ≥0` -/
/-
**Metric.infNndist** 是 Mathlib 中的一个定义，位于命名空间 `Metric`。
形式化陈述：infNndist (x : α) (s : Set α) : Real>=0
参数：x : α；s : Set α。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The minimal distance of a point to a set as a `ℝ≥0`
-/
def infNndist (x : α) (s : Set α) : ℝ≥0 :=
  ENNReal.toNNReal (infEDist x s)

@[simp]
/-
**Metric.coe_infNndist** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：coe_infNndist : (infNndist x s : Real) = infDist x s
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_infNndist : (infNndist x s : ℝ) = infDist x s :=
  rfl

/-- The minimal distance to a set (as `ℝ≥0`) is Lipschitz in point with constant 1 -/
/-
**Metric.lipschitz_infNndist_pt** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：lipschitz_infNndist_pt (s : Set α) : LipschitzWith 1 fun x => infNndist x 
s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.of_le_add`：∀ {α : Type u} [inst : PseudoMetricSpace α] {f 
: α → ℝ}, (∀ (x y : α), f x ≤ f y + dist x y) → LipschitzWith 1 f
· 使用定理 `Metric.infDist_le_infDist_add_dist`：infDist_le_infDist_add_dist : infDis
t x s <= infDist y s + dist x y

--- 原说明 ---
The minimal distance to a set (as `ℝ≥0`) is Lipschitz in point with constant 1
-/
theorem lipschitz_infNndist_pt (s : Set α) : LipschitzWith 1 fun x => infNndist x s :=
  LipschitzWith.of_le_add fun _ _ => infDist_le_infDist_add_dist

/-- The minimal distance to a set (as `ℝ≥0`) is uniformly continuous in point -/
/-
**Metric.uniformContinuous_infNndist_pt** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：uniformContinuous_infNndist_pt (s : Set α) : UniformContinuous fun x => in
fNndist x s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.uniformContinuous`：∀ {α : Type u} {β : Type v} [inst : Pse
udoEMetricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   L
ipschitzWith K f → Un…
· 使用定理 `Metric.lipschitz_infNndist_pt`：lipschitz_infNndist_pt (s : Set α) : Lips
chitzWith 1 fun x => infNndist x s

--- 原说明 ---
The minimal distance to a set (as `ℝ≥0`) is uniformly continuous in point
-/
theorem uniformContinuous_infNndist_pt (s : Set α) : UniformContinuous fun x => infNndist x s :=
  (lipschitz_infNndist_pt s).uniformContinuous

/-- The minimal distance to a set (as `ℝ≥0`) is continuous in point -/
@[continuity, fun_prop]
/-
**Metric.continuous_infNndist_pt** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：continuous_infNndist_pt (s : Set α) : Continuous fun x => infNndist x s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.continuous`：UniformContinuous.continuous (hf : Uniform
Continuous f) : Continuous f
· 使用定理 `Metric.uniformContinuous_infNndist_pt`：uniformContinuous_infNndist_pt (s
 : Set α) : UniformContinuous fun x => infNndist x s

--- 原说明 ---
The minimal distance to a set (as `ℝ≥0`) is continuous in point
-/
theorem continuous_infNndist_pt (s : Set α) : Continuous fun x => infNndist x s :=
  (uniformContinuous_infNndist_pt s).continuous

/-! ### The Hausdorff distance as a function into `ℝ`. -/

/-- The Hausdorff distance between two sets is the smallest nonnegative `r` such that each set is
included in the `r`-neighborhood of the other. If there is no such `r`, it is defined to
be `0`, arbitrarily. -/
/-
**Metric.hausdorffDist** 是 Mathlib 中的一个定义，位于命名空间 `Metric`。
形式化陈述：hausdorffDist (s t : Set α) : Real
参数：s t : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Hausdorff distance between two sets is the smallest nonnegative `r` such tha
t each set is
included in the `r`-neighborhood of the other. If there is no such `r`, it is de
fined to
be `0`, arbitrarily.
-/
def hausdorffDist (s t : Set α) : ℝ :=
  ENNReal.toReal (hausdorffEDist s t)

/-- The Hausdorff distance is nonnegative. -/
/-
**Metric.hausdorffDist_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：hausdorffDist_nonneg : 0 <= hausdorffDist s t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p

--- 原说明 ---
The Hausdorff distance is nonnegative.
-/
theorem hausdorffDist_nonneg : 0 ≤ hausdorffDist s t := by simp [hausdorffDist]

/-- If two sets are nonempty and bounded in a metric space, they are at finite Hausdorff
edistance. -/
/-
**Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded** 是 Mathlib 中的一个定理，位于命名空间 
`Metric`。
形式化陈述：hausdorffEDist_ne_top_of_nonempty_of_bounded (hs : s.Nonempty) (ht : t.Non
empty) (bs : IsBounded s) (bt : IsBounded t) : hausdorffEDist s t != ⊤
参数：hs : s.Nonempty；ht : t.Nonempty；bs : IsBounded s；bt : IsBounded t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bornology.IsBounded.subset_closedBall`：∀ {α : Type u} {s : Set α} [inst 
: PseudoMetricSpace α],   Bornology.IsBounded s → ∀ (c : α), ∃ r, s ⊆ Metric.clo
sedBall c r
· 使用定理 `Metric.hausdorffEDist_le_of_mem_edist`：hausdorffEDist_le_of_mem_edist {r
 : Real>=0∞} (H1 : forall x in s, exists y in t, edist x y <= r) (H2 : forall x 
in t, exists y in s, edist …
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `edist_dist`：edist_dist (x y : α) : edist x y = ENNReal.ofReal (dist x y)
· 使用定理 `ENNReal.ofReal_le_ofReal_iff`：ofReal_le_ofReal_iff {p q : Real} (h : 0 <
= q) : ENNReal.ofReal p <= ENNReal.ofReal q ↔ p <= q
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `ne_top_of_le_ne_top`：ne_top_of_le_ne_top (hb : b != ⊤) (hab : a <= b) : 
a != ⊤
· 使用定理 `ENNReal.ofReal_ne_top`：ofReal_ne_top {r : Real} : ENNReal.ofReal r != ∞

--- 原说明 ---
If two sets are nonempty and bounded in a metric space, they are at finite Hausd
orff
edistance.
-/
theorem hausdorffEDist_ne_top_of_nonempty_of_bounded (hs : s.Nonempty) (ht : t.Nonempty)
    (bs : IsBounded s) (bt : IsBounded t) : hausdorffEDist s t ≠ ⊤ := by
  rcases hs with ⟨cs, hcs⟩
  rcases ht with ⟨ct, hct⟩
  rcases bs.subset_closedBall ct with ⟨rs, hrs⟩
  rcases bt.subset_closedBall cs with ⟨rt, hrt⟩
  have : hausdorffEDist s t ≤ ENNReal.ofReal (max rs rt) := by
    apply hausdorffEDist_le_of_mem_edist
    · intro x xs
      exists ct, hct
      have : dist x ct ≤ max rs rt := le_trans (hrs xs) (le_max_left _ _)
      rwa [edist_dist, ENNReal.ofReal_le_ofReal_iff]
      exact le_trans dist_nonneg this
    · intro x xt
      exists cs, hcs
      have : dist x cs ≤ max rs rt := le_trans (hrt xt) (le_max_right _ _)
      rwa [edist_dist, ENNReal.ofReal_le_ofReal_iff]
      exact le_trans dist_nonneg this
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top this

@[deprecated (since := "2026-01-08")]
alias hausdorffEdist_ne_top_of_nonempty_of_bounded := hausdorffEDist_ne_top_of_nonempty_of_bounded

/-- The Hausdorff distance between a set and itself is zero. -/
@[simp]
/-
**Metric.hausdorffDist_self_zero** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：hausdorffDist_self_zero : hausdorffDist s s = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.hausdorffEDist_self`：hausdorffEDist_self : hausdorffEDist s s = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The Hausdorff distance between a set and itself is zero.
-/
theorem hausdorffDist_self_zero : hausdorffDist s s = 0 := by simp [hausdorffDist]

/-- The Hausdorff distances from `s` to `t` and from `t` to `s` coincide. -/
/-
**Metric.hausdorffDist_comm** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：hausdorffDist_comm : hausdorffDist s t = hausdorffDist t s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.hausdorffEDist_comm`：hausdorffEDist_comm : hausdorffEDist s t = h
ausdorffEDist t s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The Hausdorff distances from `s` to `t` and from `t` to `s` coincide.
-/
theorem hausdorffDist_comm : hausdorffDist s t = hausdorffDist t s := by
  simp [hausdorffDist, hausdorffEDist_comm]

/-- The Hausdorff distance to the empty set vanishes (if you want to have the more reasonable
value `∞` instead, use `Metric.hausdorffEDist`, which takes values in `ℝ≥0∞`). -/
@[simp]
/-
**Metric.hausdorffDist_empty** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：hausdorffDist_empty : hausdorffDist s ∅ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.hausdorffDist_self_zero`：hausdorffDist_self_zero : hausdorffDist 
s s = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Metric.hausdorffEDist_empty`：hausdorffEDist_empty (ne : s.Nonempty) : ha
usdorffEDist s ∅ = ∞

--- 原说明 ---
The Hausdorff distance to the empty set vanishes (if you want to have the more r
easonable
value `∞` instead, use `Metric.hausdorffEDist`, which takes values in `ℝ≥0∞`).
-/
theorem hausdorffDist_empty : hausdorffDist s ∅ = 0 := by
  rcases s.eq_empty_or_nonempty with h | h
  · simp [h]
  · simp [hausdorffDist, hausdorffEDist_empty h]

/-- The Hausdorff distance to the empty set vanishes (if you want to have the more reasonable
value `∞` instead, use `Metric.hausdorffEDist`, which takes values in `ℝ≥0∞`). -/
@[simp]
/-
**Metric.hausdorffDist_empty'** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：hausdorffDist_empty' : hausdorffDist ∅ s = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.hausdorffDist_comm`：hausdorffDist_comm : hausdorffDist s t = haus
dorffDist t s
· 使用定理 `Metric.hausdorffDist_empty`：hausdorffDist_empty : hausdorffDist s ∅ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The Hausdorff distance to the empty set vanishes (if you want to have the more r
easonable
value `∞` instead, use `Metric.hausdorffEDist`, which takes values in `ℝ≥0∞`).
-/
theorem hausdorffDist_empty' : hausdorffDist ∅ s = 0 := by simp [hausdorffDist_comm]

/-- Bounding the Hausdorff distance by bounding the distance of any point
in each set to the other set -/
/-
**Metric.hausdorffDist_le_of_infDist** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：hausdorffDist_le_of_infDist {r : Real} (hr : 0 <= r) (H1 : forall x in s, 
infDist x t <= r) (H2 : forall x in t, infDist x s <= r) : hausdorffDist s t <= 
r
参数：hr : 0 <= r；H1 : forall x in s, infDist x t <= r；H2 : forall x in t, infDist 
x s <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.hausdorffDist_empty'`：hausdorffDist_empty' : hausdorffDist ∅ s = 
0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Metric.hausdorffDist_empty`：hausdorffDist_empty : hausdorffDist s ∅ = 0
· 使用定理 `Metric.hausdorffEDist_le_of_infEDist`：hausdorffEDist_le_of_infEDist {r :
 Real>=0∞} (H1 : forall x in s, infEDist x t <= r) (H2 : forall x in t, infEDist
 x s <= r) : hausdorffEDis…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `ENNReal.le_ofReal_iff_toReal_le`：le_ofReal_iff_toReal_le {a : Real>=0∞} 
{b : Real} (ha : a != ∞) (hb : 0 <= b) : a <= ENNReal.ofReal b ↔ ENNReal.toReal 
a <= b
· 使用定理 `Metric.infEDist_ne_top`：infEDist_ne_top (h : s.Nonempty) : infEDist x s 
!= ∞
· 使用定理 `ENNReal.toReal_le_of_le_ofReal`：toReal_le_of_le_ofReal {a : Real>=0∞} {b
 : Real} (hb : 0 <= b) (h : a <= ENNReal.ofReal b) : ENNReal.toReal a <= b

--- 原说明 ---
Bounding the Hausdorff distance by bounding the distance of any point
in each set to the other set
-/
theorem hausdorffDist_le_of_infDist {r : ℝ} (hr : 0 ≤ r) (H1 : ∀ x ∈ s, infDist x t ≤ r)
    (H2 : ∀ x ∈ t, infDist x s ≤ r) : hausdorffDist s t ≤ r := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · rwa [hausdorffDist_empty']
  rcases t.eq_empty_or_nonempty with rfl | ht
  · rwa [hausdorffDist_empty]
  have : hausdorffEDist s t ≤ ENNReal.ofReal r := by
    apply hausdorffEDist_le_of_infEDist _ _
    · simpa only [infDist, ← ENNReal.le_ofReal_iff_toReal_le (infEDist_ne_top ht) hr] using H1
    · simpa only [infDist, ← ENNReal.le_ofReal_iff_toReal_le (infEDist_ne_top hs) hr] using H2
  exact ENNReal.toReal_le_of_le_ofReal hr this

/-- Bounding the Hausdorff distance by exhibiting, for any point in each set,
another point in the other set at controlled distance -/
/-
**Metric.hausdorffDist_le_of_mem_dist** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：hausdorffDist_le_of_mem_dist {r : Real} (hr : 0 <= r) (H1 : forall x in s,
 exists y in t, dist x y <= r) (H2 : forall x in t, exists y in s, dist x y <= r
) : hausdorffDist s t <= r
参数：hr : 0 <= r；H1 : forall x in s, exists y in t, dist x y <= r；H2 : forall x in
 t, exists y in s, dist x y <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.hausdorffDist_le_of_infDist`：hausdorffDist_le_of_infDist {r : Rea
l} (hr : 0 <= r) (H1 : forall x in s, infDist x t <= r) (H2 : forall x in t, inf
Dist x s <= r) : hausdor…
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Metric.infDist_le_dist_of_mem`：infDist_le_dist_of_mem (h : y in s) : inf
Dist x s <= dist x y

--- 原说明 ---
Bounding the Hausdorff distance by exhibiting, for any point in each set,
another point in the other set at controlled distance
-/
theorem hausdorffDist_le_of_mem_dist {r : ℝ} (hr : 0 ≤ r) (H1 : ∀ x ∈ s, ∃ y ∈ t, dist x y ≤ r)
    (H2 : ∀ x ∈ t, ∃ y ∈ s, dist x y ≤ r) : hausdorffDist s t ≤ r := by
  apply hausdorffDist_le_of_infDist hr
  · intro x xs
    rcases H1 x xs with ⟨y, yt, hy⟩
    exact le_trans (infDist_le_dist_of_mem yt) hy
  · intro x xt
    rcases H2 x xt with ⟨y, ys, hy⟩
    exact le_trans (infDist_le_dist_of_mem ys) hy

/-- The Hausdorff distance is controlled by the diameter of the union. -/
/-
**Metric.hausdorffDist_le_diam** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：hausdorffDist_le_diam (hs : s.Nonempty) (bs : IsBounded s) (ht : t.Nonempt
y) (bt : IsBounded t) : hausdorffDist s t <= diam (s union t)
参数：hs : s.Nonempty；bs : IsBounded s；ht : t.Nonempty；bt : IsBounded t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.hausdorffDist_le_of_mem_dist`：hausdorffDist_le_of_mem_dist {r : R
eal} (hr : 0 <= r) (H1 : forall x in s, exists y in t, dist x y <= r) (H2 : fora
ll x in t, exists y in s,…
· 使用定理 `Metric.diam_nonneg`：diam_nonneg : 0 <= diam s
· 使用定理 `Metric.dist_le_diam_of_mem`：dist_le_diam_of_mem (h : IsBounded s) (hx : 
x in s) (hy : y in s) : dist x y <= diam s
· 使用定理 `Bornology.IsBounded.union`：∀ {α : Type u_2} {x : Bornology α} {s t : Set
 α},   Bornology.IsBounded s → Bornology.IsBounded t → Bornology.IsBounded (s ∪ 
t)
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t

--- 原说明 ---
The Hausdorff distance is controlled by the diameter of the union.
-/
theorem hausdorffDist_le_diam (hs : s.Nonempty) (bs : IsBounded s) (ht : t.Nonempty)
    (bt : IsBounded t) : hausdorffDist s t ≤ diam (s ∪ t) := by
  rcases hs with ⟨x, xs⟩
  rcases ht with ⟨y, yt⟩
  refine hausdorffDist_le_of_mem_dist diam_nonneg ?_ ?_
  · exact fun z hz => ⟨y, yt, dist_le_diam_of_mem (bs.union bt) (subset_union_left hz)
      (subset_union_right yt)⟩
  · exact fun z hz => ⟨x, xs, dist_le_diam_of_mem (bs.union bt) (subset_union_right hz)
      (subset_union_left xs)⟩

/-- The distance to a set is controlled by the Hausdorff distance. -/
/-
**Metric.infDist_le_hausdorffDist_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：infDist_le_hausdorffDist_of_mem (hx : x in s) (fin : hausdorffEDist s t !=
 ⊤) : infDist x t <= hausdorffDist s t
参数：hx : x in s；fin : hausdorffEDist s t != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.toReal_mono`：toReal_mono (hb : b != ∞) (h : a <= b) : a.toReal <
= b.toReal
· 使用定理 `Metric.infEDist_le_hausdorffEDist_of_mem`：infEDist_le_hausdorffEDist_of_
mem (h : x in s) : infEDist x t <= hausdorffEDist s t

--- 原说明 ---
The distance to a set is controlled by the Hausdorff distance.
-/
theorem infDist_le_hausdorffDist_of_mem (hx : x ∈ s) (fin : hausdorffEDist s t ≠ ⊤) :
    infDist x t ≤ hausdorffDist s t :=
  toReal_mono fin (infEDist_le_hausdorffEDist_of_mem hx)

/-- If the Hausdorff distance is `< r`, any point in one of the sets is at distance
`< r` of a point in the other set. -/
/-
**Metric.exists_dist_lt_of_hausdorffDist_lt** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：exists_dist_lt_of_hausdorffDist_lt {r : Real} (h : x in s) (H : hausdorffD
ist s t < r) (fin : hausdorffEDist s t != ⊤) : exists y in t, dist x y < r
参数：h : x in s；H : hausdorffDist s t < r；fin : hausdorffEDist s t != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Metric.hausdorffDist_nonneg`：hausdorffDist_nonneg : 0 <= hausdorffDist s
 t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.toReal_lt_toReal`：toReal_lt_toReal (ha : a != ∞) (hb : b != ∞) :
 a.toReal < b.toReal ↔ a < b
· 使用定理 `ENNReal.ofReal_ne_top`：ofReal_ne_top {r : Real} : ENNReal.ofReal r != ∞
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.toReal_ofReal`：toReal_ofReal {r : Real} (h : 0 <= r) : (ENNReal.
ofReal r).toReal = r
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Metric.hausdorffDist.eq_1`：∀ {α : Type u} [inst : PseudoMetricSpace α] (
s t : Set α), Metric.hausdorffDist s t = (Metric.hausdorffEDist s t).toReal
· 使用定理 `Metric.exists_edist_lt_of_hausdorffEDist_lt`：exists_edist_lt_of_hausdorf
fEDist_lt {r : Real>=0∞} (h : x in s) (H : hausdorffEDist s t < r) : exists y in
 t, edist x y < r
· 使用定理 `ENNReal.ofReal_lt_ofReal_iff`：ofReal_lt_ofReal_iff {p q : Real} (h : 0 <
 q) : ENNReal.ofReal p < ENNReal.ofReal q ↔ p < q
· 使用定理 `edist_dist`：edist_dist (x y : α) : edist x y = ENNReal.ofReal (dist x y)

--- 原说明 ---
If the Hausdorff distance is `< r`, any point in one of the sets is at distance
`< r` of a point in the other set.
-/
theorem exists_dist_lt_of_hausdorffDist_lt {r : ℝ} (h : x ∈ s) (H : hausdorffDist s t < r)
    (fin : hausdorffEDist s t ≠ ⊤) : ∃ y ∈ t, dist x y < r := by
  have r0 : 0 < r := lt_of_le_of_lt hausdorffDist_nonneg H
  have : hausdorffEDist s t < ENNReal.ofReal r := by
    rwa [hausdorffDist, ← ENNReal.toReal_ofReal (le_of_lt r0),
      ENNReal.toReal_lt_toReal fin ENNReal.ofReal_ne_top] at H
  rcases exists_edist_lt_of_hausdorffEDist_lt h this with ⟨y, hy, yr⟩
  rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff r0] at yr
  exact ⟨y, hy, yr⟩

/-- If the Hausdorff distance is `< r`, any point in one of the sets is at distance
`< r` of a point in the other set. -/
/-
**Metric.exists_dist_lt_of_hausdorffDist_lt'** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：exists_dist_lt_of_hausdorffDist_lt' {r : Real} (h : y in t) (H : hausdorff
Dist s t < r) (fin : hausdorffEDist s t != ⊤) : exists x in s, dist x y < r
参数：h : y in t；H : hausdorffDist s t < r；fin : hausdorffEDist s t != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `Metric.exists_dist_lt_of_hausdorffDist_lt`：exists_dist_lt_of_hausdorffDi
st_lt {r : Real} (h : x in s) (H : hausdorffDist s t < r) (fin : hausdorffEDist 
s t != ⊤) : exists y in t, dist…
· 使用定理 `Metric.hausdorffDist_comm`：hausdorffDist_comm : hausdorffDist s t = haus
dorffDist t s
· 使用定理 `Metric.hausdorffEDist_comm`：hausdorffEDist_comm : hausdorffEDist s t = h
ausdorffEDist t s

--- 原说明 ---
If the Hausdorff distance is `< r`, any point in one of the sets is at distance
`< r` of a point in the other set.
-/
theorem exists_dist_lt_of_hausdorffDist_lt' {r : ℝ} (h : y ∈ t) (H : hausdorffDist s t < r)
    (fin : hausdorffEDist s t ≠ ⊤) : ∃ x ∈ s, dist x y < r := by
  rw [hausdorffDist_comm] at H
  rw [hausdorffEDist_comm] at fin
  simpa [dist_comm] using exists_dist_lt_of_hausdorffDist_lt h H fin

/-- The infimum distance to `s` and `t` are the same, up to the Hausdorff distance
between `s` and `t` -/
/-
**Metric.infDist_le_infDist_add_hausdorffDist** 是 Mathlib 中的一个定理，位于命名空间 `Metric`
。
形式化陈述：infDist_le_infDist_add_hausdorffDist (fin : hausdorffEDist s t != ⊤) : inf
Dist x t <= infDist x s + hausdorffDist s t
参数：fin : hausdorffEDist s t != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.toReal_le_add'`：toReal_le_add' (hle : a <= b + c) (hb : b = ∞ ->
 a = ∞) (hc : c = ∞ -> a = ∞) : a.toReal <= b.toReal + c.toReal
· 使用定理 `Metric.infEDist_le_infEDist_add_hausdorffEDist`：infEDist_le_infEDist_add
_hausdorffEDist : infEDist x t <= infEDist x s + hausdorffEDist s t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.infEDist_eq_top_iff`：infEDist_eq_top_iff : infEDist x s = ∞ ↔ s =
 ∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.not_nonempty_iff_eq_empty`：not_nonempty_iff_eq_empty : ¬s.Nonempty ↔
 s = ∅
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Metric.nonempty_of_hausdorffEDist_ne_top`：nonempty_of_hausdorffEDist_ne_
top (hs : s.Nonempty) (fin : hausdorffEDist s t != ⊤) : t.Nonempty
· 使用定理 `Metric.hausdorffEDist_comm`：hausdorffEDist_comm : hausdorffEDist s t = h
ausdorffEDist t s

--- 原说明 ---
The infimum distance to `s` and `t` are the same, up to the Hausdorff distance
between `s` and `t`
-/
theorem infDist_le_infDist_add_hausdorffDist (fin : hausdorffEDist s t ≠ ⊤) :
    infDist x t ≤ infDist x s + hausdorffDist s t := by
  refine toReal_le_add' infEDist_le_infEDist_add_hausdorffEDist (fun h ↦ ?_) (flip absurd fin)
  rw [infEDist_eq_top_iff, ← not_nonempty_iff_eq_empty] at h ⊢
  rw [hausdorffEDist_comm] at fin
  exact mt (nonempty_of_hausdorffEDist_ne_top · fin) h

/-- The Hausdorff distance is invariant under isometries. -/
/-
**Metric.hausdorffDist_image** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：hausdorffDist_image (h : Isometry Φ) : hausdorffDist (Φ '' s) (Φ '' t) = h
ausdorffDist s t
参数：h : Isometry Φ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.hausdorffEDist_image`：hausdorffEDist_image (h : Isometry Φ) : hau
sdorffEDist (Φ '' s) (Φ '' t) = hausdorffEDist s t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The Hausdorff distance is invariant under isometries.
-/
theorem hausdorffDist_image (h : Isometry Φ) :
    hausdorffDist (Φ '' s) (Φ '' t) = hausdorffDist s t := by
  simp [hausdorffDist, hausdorffEDist_image h]

/-- The Hausdorff distance satisfies the triangle inequality. -/
/-
**Metric.hausdorffDist_triangle** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：hausdorffDist_triangle (fin : hausdorffEDist s t != ⊤) : hausdorffDist s u
 <= hausdorffDist s t + hausdorffDist t u
参数：fin : hausdorffEDist s t != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.toReal_le_add'`：toReal_le_add' (hle : a <= b + c) (hb : b = ∞ ->
 a = ∞) (hc : c = ∞ -> a = ∞) : a.toReal <= b.toReal + c.toReal
· 使用定理 `Metric.hausdorffEDist_triangle`：hausdorffEDist_triangle : hausdorffEDist
 s u <= hausdorffEDist s t + hausdorffEDist t u
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_imp_not`：not_imp_not : ¬a -> ¬b ↔ b -> a
· 使用定理 `ne_top_of_le_ne_top`：ne_top_of_le_ne_top (hb : b != ⊤) (hab : a <= b) : 
a != ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.add_ne_top`：add_ne_top : a + b != ∞ ↔ a != ∞ ∧ b != ∞
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.hausdorffEDist_comm`：hausdorffEDist_comm : hausdorffEDist s t = h
ausdorffEDist t s

--- 原说明 ---
The Hausdorff distance satisfies the triangle inequality.
-/
theorem hausdorffDist_triangle (fin : hausdorffEDist s t ≠ ⊤) :
    hausdorffDist s u ≤ hausdorffDist s t + hausdorffDist t u := by
  refine toReal_le_add' hausdorffEDist_triangle (flip absurd fin) (not_imp_not.1 fun h ↦ ?_)
  rw [hausdorffEDist_comm] at fin
  exact ne_top_of_le_ne_top (add_ne_top.2 ⟨fin, h⟩) hausdorffEDist_triangle

/-- The Hausdorff distance satisfies the triangle inequality. -/
/-
**Metric.hausdorffDist_triangle'** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：hausdorffDist_triangle' (fin : hausdorffEDist t u != ⊤) : hausdorffDist s 
u <= hausdorffDist s t + hausdorffDist t u
参数：fin : hausdorffEDist t u != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.hausdorffDist_triangle`：hausdorffDist_triangle (fin : hausdorffED
ist s t != ⊤) : hausdorffDist s u <= hausdorffDist s t + hausdorffDist t u
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.hausdorffEDist_comm`：hausdorffEDist_comm : hausdorffEDist s t = h
ausdorffEDist t s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Metric.hausdorffDist_comm`：hausdorffDist_comm : hausdorffDist s t = haus
dorffDist t s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a

--- 原说明 ---
The Hausdorff distance satisfies the triangle inequality.
-/
theorem hausdorffDist_triangle' (fin : hausdorffEDist t u ≠ ⊤) :
    hausdorffDist s u ≤ hausdorffDist s t + hausdorffDist t u := by
  rw [hausdorffEDist_comm] at fin
  have I : hausdorffDist u s ≤ hausdorffDist u t + hausdorffDist t s :=
    hausdorffDist_triangle fin
  simpa [add_comm, hausdorffDist_comm] using I

/-- The Hausdorff distance between a set and its closure vanishes. -/
@[simp]
/-
**Metric.hausdorffDist_self_closure** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：hausdorffDist_self_closure : hausdorffDist s (closure s) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.hausdorffEDist_self_closure`：hausdorffEDist_self_closure : hausdo
rffEDist s (closure s) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The Hausdorff distance between a set and its closure vanishes.
-/
theorem hausdorffDist_self_closure : hausdorffDist s (closure s) = 0 := by simp [hausdorffDist]

/-- Replacing a set by its closure does not change the Hausdorff distance. -/
@[simp]
/-
**Metric.hausdorffDist_closure** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：hausdorffDist_closure : hausdorffDist (closure s) (closure t) = hausdorffD
ist s t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.hausdorffEDist_closure_right`：hausdorffEDist_closure_right : haus
dorffEDist s (closure t) = hausdorffEDist s t
· 使用定理 `Metric.hausdorffEDist_closure_left`：hausdorffEDist_closure_left : hausdo
rffEDist (closure s) t = hausdorffEDist s t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Replacing a set by its closure does not change the Hausdorff distance.
-/
theorem hausdorffDist_closure₁ : hausdorffDist (closure s) t = hausdorffDist s t := by
  simp [hausdorffDist]

/-- Replacing a set by its closure does not change the Hausdorff distance. -/
@[simp]
/-
**Metric.hausdorffDist_closure** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：hausdorffDist_closure : hausdorffDist (closure s) (closure t) = hausdorffD
ist s t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.hausdorffEDist_closure_right`：hausdorffEDist_closure_right : haus
dorffEDist s (closure t) = hausdorffEDist s t
· 使用定理 `Metric.hausdorffEDist_closure_left`：hausdorffEDist_closure_left : hausdo
rffEDist (closure s) t = hausdorffEDist s t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Replacing a set by its closure does not change the Hausdorff distance.
-/
theorem hausdorffDist_closure₂ : hausdorffDist s (closure t) = hausdorffDist s t := by
  simp [hausdorffDist]

/-- The Hausdorff distances between two sets and their closures coincide. -/
/-
**Metric.hausdorffDist_closure** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：hausdorffDist_closure : hausdorffDist (closure s) (closure t) = hausdorffD
ist s t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.hausdorffEDist_closure_right`：hausdorffEDist_closure_right : haus
dorffEDist s (closure t) = hausdorffEDist s t
· 使用定理 `Metric.hausdorffEDist_closure_left`：hausdorffEDist_closure_left : hausdo
rffEDist (closure s) t = hausdorffEDist s t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The Hausdorff distances between two sets and their closures coincide.
-/
theorem hausdorffDist_closure : hausdorffDist (closure s) (closure t) = hausdorffDist s t := by
  simp [hausdorffDist]

/-- Two sets are at zero Hausdorff distance if and only if they have the same closures. -/
/-
**Metric.hausdorffDist_zero_iff_closure_eq_closure** 是 Mathlib 中的一个定理，位于命名空间 `Me
tric`。
形式化陈述：hausdorffDist_zero_iff_closure_eq_closure (fin : hausdorffEDist s t != ⊤) 
: hausdorffDist s t = 0 ↔ closure s = closure t
参数：fin : hausdorffEDist s t != ⊤。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Two sets are at zero Hausdorff distance if and only if they have the same closur
es.
-/
theorem hausdorffDist_zero_iff_closure_eq_closure (fin : hausdorffEDist s t ≠ ⊤) :
    hausdorffDist s t = 0 ↔ closure s = closure t := by
  simp [← hausdorffEDist_zero_iff_closure_eq_closure, hausdorffDist,
    ENNReal.toReal_eq_zero_iff, fin]

/-- Two closed sets are at zero Hausdorff distance if and only if they coincide. -/
/-
**Metric._root_.IsClosed.hausdorffDist_zero_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 `Me
tric`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two closed sets are at zero Hausdorff distance if and only if they coincide.
-/
theorem _root_.IsClosed.hausdorffDist_zero_iff_eq (hs : IsClosed s) (ht : IsClosed t)
    (fin : hausdorffEDist s t ≠ ⊤) : hausdorffDist s t = 0 ↔ s = t := by
  simp [← _root_.IsClosed.hausdorffEDist_zero_iff hs ht, hausdorffDist, ENNReal.toReal_eq_zero_iff,
    fin]

@[simp]
/-
**Metric.hausdorffDist_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：hausdorffDist_singleton : hausdorffDist {x} {y} = dist x y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.hausdorffDist.eq_1`：∀ {α : Type u} [inst : PseudoMetricSpace α] (
s t : Set α), Metric.hausdorffDist s t = (Metric.hausdorffEDist s t).toReal
· 使用定理 `Metric.hausdorffEDist_singleton`：hausdorffEDist_singleton : hausdorffEDi
st {x} {y} = edist x y
· 使用定理 `dist_edist`：dist_edist (x y : α) : dist x y = (edist x y).toReal
-/
theorem hausdorffDist_singleton : hausdorffDist {x} {y} = dist x y := by
  rw [hausdorffDist, hausdorffEDist_singleton, dist_edist]

end

end Metric

