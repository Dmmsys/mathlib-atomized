/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
module

public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Thickenings in pseudo-metric spaces

## Main definitions
* `Metric.thickening δ s`, the open thickening by radius `δ` of a set `s` in a pseudo emetric space.
* `Metric.cthickening δ s`, the closed thickening by radius `δ` of a set `s` in a pseudo emetric
  space.

## Main results
* `Disjoint.exists_thickenings`: two disjoint sets admit disjoint thickenings
* `Disjoint.exists_cthickenings`: two disjoint sets admit disjoint closed thickenings
* `IsCompact.exists_cthickening_subset_open`: if `s` is compact, `t` is open and `s ⊆ t`,
  some `cthickening` of `s` is contained in `t`.

* `Metric.hasBasis_nhdsSet_cthickening`: the `cthickening`s of a compact set `K` form a basis
  of the neighbourhoods of `K`
* `Metric.closure_eq_iInter_cthickening'`: the closure of a set equals the intersection
  of its closed thickenings of positive radii accumulating at zero.
  The same holds for open thickenings.
* `IsCompact.cthickening_eq_biUnion_closedBall`: if `s` is compact, `cthickening δ s` is the union
  of `closedBall`s of radius `δ` around `x : E`.

-/

@[expose] public section

noncomputable section
open NNReal ENNReal Topology Set Filter Bornology

universe u v w

variable {ι : Sort*} {α : Type u}

namespace Metric

section Thickening

variable [PseudoEMetricSpace α] {δ : ℝ} {s : Set α} {x : α}

/-- The (open) `δ`-thickening `Metric.thickening δ E` of a subset `E` in a pseudo emetric space
consists of those points that are at distance less than `δ` from some point of `E`. -/
/-
**Metric.thickening** 是 Mathlib 中的一个定义，位于命名空间 `Metric`。
形式化陈述：thickening (δ : Real) (E : Set α) : Set α
参数：δ : Real；E : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (open) `δ`-thickening `Metric.thickening δ E` of a subset `E` in a pseudo em
etric space
consists of those points that are at distance less than `δ` from some point of `
E`.
-/
def thickening (δ : ℝ) (E : Set α) : Set α :=
  { x : α | infEDist x E < ENNReal.ofReal δ }
/-
**Metric.mem_thickening_iff_infEDist_lt** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：mem_thickening_iff_infEDist_lt : x in thickening δ s ↔ infEDist x s < ENNR
eal.ofReal δ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_thickening_iff_infEDist_lt : x ∈ thickening δ s ↔ infEDist x s < ENNReal.ofReal δ :=
  Iff.rfl

@[deprecated (since := "2026-01-08")]
alias mem_thickening_iff_infEdist_lt := mem_thickening_iff_infEDist_lt

/-- An exterior point of a subset `E` (i.e., a point outside the closure of `E`) is not in the
(open) `δ`-thickening of `E` for small enough positive `δ`. -/
/-
**Metric.eventually_notMem_thickening_of_infEDist_pos** 是 Mathlib 中的一个引理，位于命名空间 
`Metric`。
形式化陈述：eventually_notMem_thickening_of_infEDist_pos {E : Set α} {x : α} (h : x ∉ 
closure E) : forallᶠ δ in 𝓝 (0 : Real), x ∉ Metric.thickening δ E
参数：h : x ∉ closure E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.exists_real_pos_lt_infEDist_of_notMem_closure`：exists_real_pos_lt
_infEDist_of_notMem_closure {x : α} {E : Set α} (h : x ∉ closure E) : exists ε :
 Real, 0 < ε ∧ ENNReal.ofReal ε < infEDist…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `eventually_lt_nhds`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 :
 LinearOrder α] [ClosedIciTopology α] {a b : α},   a < b → ∀ᶠ (x : α) in nhds a,
 x < b
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `ENNReal.ofReal_le_ofReal`：ofReal_le_ofReal {p q : Real} (h : p <= q) : E
NNReal.ofReal p <= ENNReal.ofReal q
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b

--- 原说明 ---
An exterior point of a subset `E` (i.e., a point outside the closure of `E`) is 
not in the
(open) `δ`-thickening of `E` for small enough positive `δ`.
-/
lemma eventually_notMem_thickening_of_infEDist_pos {E : Set α} {x : α} (h : x ∉ closure E) :
    ∀ᶠ δ in 𝓝 (0 : ℝ), x ∉ Metric.thickening δ E := by
  obtain ⟨ε, ⟨ε_pos, ε_lt⟩⟩ := exists_real_pos_lt_infEDist_of_notMem_closure h
  filter_upwards [eventually_lt_nhds ε_pos] with δ hδ
  simp only [thickening, mem_ofPred_eq, not_lt]
  exact (ENNReal.ofReal_le_ofReal hδ.le).trans ε_lt.le

@[deprecated (since := "2026-01-08")]
alias eventually_notMem_thickening_of_infEdist_pos :=
  eventually_notMem_thickening_of_infEDist_pos

/-- The (open) thickening equals the preimage of an open interval under `Metric.infEDist`. -/
/-
**Metric.thickening_eq_preimage_infEDist** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：thickening_eq_preimage_infEDist (δ : Real) (E : Set α) : thickening δ E = 
(infEDist · E) ⁻¹' Iio (ENNReal.ofReal δ)
参数：δ : Real；E : Set α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (open) thickening equals the preimage of an open interval under `Metric.infE
Dist`.
-/
theorem thickening_eq_preimage_infEDist (δ : ℝ) (E : Set α) :
    thickening δ E = (infEDist · E) ⁻¹' Iio (ENNReal.ofReal δ) :=
  rfl

@[deprecated (since := "2026-01-08")]
alias thickening_eq_preimage_infEdist := thickening_eq_preimage_infEDist

/-- The (open) thickening is an open set. -/
/-
**Metric.isOpen_thickening** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：isOpen_thickening {δ : Real} {E : Set α} : IsOpen (thickening δ E)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.isOpen_preimage`：∀ {X : Type u} {Y : Type v} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Continuous f → ∀ (s : S
et Y), IsOpen s …
· 使用定理 `Metric.continuous_infEDist`：continuous_infEDist : Continuous fun x => in
fEDist x s
· 使用定理 `isOpen_Iio`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : LinearO
rder α] [ClosedIciTopology α] {a : α}, IsOpen (Set.Iio a)
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal

--- 原说明 ---
The (open) thickening is an open set.
-/
theorem isOpen_thickening {δ : ℝ} {E : Set α} : IsOpen (thickening δ E) :=
  Continuous.isOpen_preimage continuous_infEDist _ isOpen_Iio

/-- The (open) thickening of the empty set is empty. -/
@[simp]
/-
**Metric.thickening_empty** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：thickening_empty (δ : Real) : thickening δ (∅ : Set α) = ∅
参数：δ : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Metric.infEDist_empty`：infEDist_empty : infEDist x ∅ = ∞
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The (open) thickening of the empty set is empty.
-/
theorem thickening_empty (δ : ℝ) : thickening δ (∅ : Set α) = ∅ := by
  simp only [thickening, ofPred_false, infEDist_empty, not_top_lt]
/-
**Metric.thickening_of_nonpos** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：thickening_of_nonpos (hδ : δ <= 0) (s : Set α) : thickening δ s = ∅
参数：hδ : δ <= 0；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_of_forall_notMem`：eq_empty_of_forall_notMem (h : forall x, 
x ∉ s) : s = ∅
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `ENNReal.ofReal_of_nonpos`：∀ {p : ℝ}, p ≤ 0 → ENNReal.ofReal p = 0
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
theorem thickening_of_nonpos (hδ : δ ≤ 0) (s : Set α) : thickening δ s = ∅ :=
  eq_empty_of_forall_notMem fun _ => ((ENNReal.ofReal_of_nonpos hδ).trans_le bot_le).not_gt

/-- The (open) thickening `Metric.thickening δ E` of a fixed subset `E` is an increasing function of
the thickening radius `δ`. -/
@[gcongr]
/-
**Metric.thickening_mono** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：thickening_mono {δ₁ δ₂ : Real} (hle : δ₁ <= δ₂) (E : Set α) : thickening δ
₁ E subseteq thickening δ₂ E
参数：hle : δ₁ <= δ₂；E : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
· 使用定理 `Set.Iio_subset_Iio`：Iio_subset_Iio (h : a <= b) : Iio a subseteq Iio b
· 使用定理 `ENNReal.ofReal_le_ofReal`：ofReal_le_ofReal {p q : Real} (h : p <= q) : E
NNReal.ofReal p <= ENNReal.ofReal q

--- 原说明 ---
The (open) thickening `Metric.thickening δ E` of a fixed subset `E` is an increa
sing function of
the thickening radius `δ`.
-/
theorem thickening_mono {δ₁ δ₂ : ℝ} (hle : δ₁ ≤ δ₂) (E : Set α) :
    thickening δ₁ E ⊆ thickening δ₂ E :=
  preimage_mono (Iio_subset_Iio (ENNReal.ofReal_le_ofReal hle))

/-- The (open) thickening `Metric.thickening δ E` with a fixed thickening radius `δ` is
an increasing function of the subset `E`. -/
/-
**Metric.thickening_subset_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：thickening_subset_of_subset (δ : Real) {E₁ E₂ : Set α} (h : E₁ subseteq E₂
) : thickening δ E₁ subseteq thickening δ E₂
参数：δ : Real；h : E₁ subseteq E₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Metric.infEDist_anti`：infEDist_anti (h : s subseteq t) : infEDist x t <=
 infEDist x s

--- 原说明 ---
The (open) thickening `Metric.thickening δ E` with a fixed thickening radius `δ`
 is
an increasing function of the subset `E`.
-/
theorem thickening_subset_of_subset (δ : ℝ) {E₁ E₂ : Set α} (h : E₁ ⊆ E₂) :
    thickening δ E₁ ⊆ thickening δ E₂ := fun _ hx => lt_of_le_of_lt (infEDist_anti h) hx
/-
**Metric.mem_thickening_iff_exists_edist_lt** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：mem_thickening_iff_exists_edist_lt {δ : Real} (E : Set α) (x : α) : x in t
hickening δ E ↔ exists z in E, edist x z < ENNReal.ofReal δ
参数：E : Set α；x : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.infEDist_lt_iff`：infEDist_lt_iff {r : Real>=0∞} : infEDist x s < 
r ↔ exists y in s, edist x y < r
-/
theorem mem_thickening_iff_exists_edist_lt {δ : ℝ} (E : Set α) (x : α) :
    x ∈ thickening δ E ↔ ∃ z ∈ E, edist x z < ENNReal.ofReal δ :=
  infEDist_lt_iff

/-- The frontier of the (open) thickening of a set is contained in an `Metric.infEDist` level
set. -/
/-
**Metric.frontier_thickening_subset** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：frontier_thickening_subset (E : Set α) {δ : Real} : frontier (thickening δ
 E) subseteq { x : α | infEDist x E = ENNReal.ofReal δ }
参数：E : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `frontier_lt_subset_eq`：frontier_lt_subset_eq (hf : Continuous f) (hg : C
ontinuous g) : frontier { b | f b < g b } subseteq { b | f b = g b }
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `Metric.continuous_infEDist`：continuous_infEDist : Continuous fun x => in
fEDist x s
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)

--- 原说明 ---
The frontier of the (open) thickening of a set is contained in an `Metric.infEDi
st` level
set.
-/
theorem frontier_thickening_subset (E : Set α) {δ : ℝ} :
    frontier (thickening δ E) ⊆ { x : α | infEDist x E = ENNReal.ofReal δ } :=
  frontier_lt_subset_eq continuous_infEDist continuous_const

open scoped Function in -- required for scoped `on` notation
/-
**Metric.frontier_thickening_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：frontier_thickening_disjoint (A : Set α) : Pairwise (Disjoint on fun r : R
eal => frontier (thickening r A))
参数：A : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pairwise_disjoint_on`：pairwise_disjoint_on [PartialOrder α] [OrderBot α]
 [LinearOrder ι] (f : ι -> α) : Pairwise (Disjoint on f) ↔ forall ⦃m n⦄, m < n -
> Disjoint…
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.thickening_of_nonpos`：thickening_of_nonpos (hδ : δ <= 0) (s : Set
 α) : thickening δ s = ∅
· 使用定理 `frontier_empty`：frontier_empty : frontier (∅ : Set X) = ∅
· 使用定理 `Disjoint.mono`：Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.s
upport <= f.support) (hg : y.support <= g.support) : Disjoint x y
· 使用定理 `Metric.frontier_thickening_subset`：frontier_thickening_subset (E : Set α
) {δ : Real} : frontier (thickening δ E) subseteq { x : α | infEDist x E = ENNRe
al.ofReal δ }
· 使用定理 `Disjoint.preimage`：Disjoint.preimage (f : α -> β) {s t : Set β} (h : Dis
joint s t) : Disjoint (f ⁻¹' s) (f ⁻¹' t)
· 使用引理 `Set.disjoint_singleton`：disjoint_singleton : Disjoint ({a} : Set α) {b} 
↔ a != b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `ENNReal.toReal_ofReal`：toReal_ofReal {r : Real} (h : 0 <= r) : (ENNReal.
ofReal r).toReal = r
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem frontier_thickening_disjoint (A : Set α) :
    Pairwise (Disjoint on fun r : ℝ => frontier (thickening r A)) := by
  refine (pairwise_disjoint_on _).2 fun r₁ r₂ hr => ?_
  rcases le_total r₁ 0 with h₁ | h₁
  · simp [thickening_of_nonpos h₁]
  refine ((disjoint_singleton.2 fun h => hr.ne ?_).preimage _).mono (frontier_thickening_subset _)
    (frontier_thickening_subset _)
  apply_fun ENNReal.toReal at h
  rwa [ENNReal.toReal_ofReal h₁, ENNReal.toReal_ofReal (h₁.trans hr.le)] at h

/-- Any set is contained in the complement of the δ-thickening of the complement of its
δ-thickening. -/
/-
**Metric.subset_compl_thickening_compl_thickening_self** 是 Mathlib 中的一个引理，位于命名空间
 `Metric`。
形式化陈述：subset_compl_thickening_compl_thickening_self (δ : Real) (E : Set α) : E s
ubseteq (thickening δ (thickening δ E)ᶜ)ᶜ
参数：δ : Real；E : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.le_infEDist`：le_infEDist {d} : d <= infEDist x s ↔ forall y in s,
 d <= edist x y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PseudoEMetricSpace.edist_comm`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x y : α), edist x y = edist y x
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Metric.infEDist_le_edist_of_mem`：infEDist_le_edist_of_mem (h : y in s) :
 infEDist x s <= edist x y

--- 原说明 ---
Any set is contained in the complement of the δ-thickening of the complement of 
its
δ-thickening.
-/
lemma subset_compl_thickening_compl_thickening_self (δ : ℝ) (E : Set α) :
    E ⊆ (thickening δ (thickening δ E)ᶜ)ᶜ := by
  intro x x_in_E
  simp only [thickening, mem_compl_iff, mem_ofPred_eq, not_lt]
  apply le_infEDist.mpr fun y hy ↦ ?_
  simp only [mem_compl_iff, mem_ofPred_eq, not_lt] at hy
  simpa only [edist_comm] using le_trans hy <| Metric.infEDist_le_edist_of_mem x_in_E

/-- The δ-thickening of the complement of the δ-thickening of a set is contained in the complement
of the set. -/
/-
**Metric.thickening_compl_thickening_self_subset_compl** 是 Mathlib 中的一个引理，位于命名空间
 `Metric`。
形式化陈述：thickening_compl_thickening_self_subset_compl (δ : Real) (E : Set α) : thi
ckening δ (thickening δ E)ᶜ subseteq Eᶜ
参数：δ : Real；E : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.compl_subset_compl`：compl_subset_compl : sᶜ subseteq tᶜ ↔ t subseteq
 s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用引理 `Metric.subset_compl_thickening_compl_thickening_self`：subset_compl_thick
ening_compl_thickening_self (δ : Real) (E : Set α) : E subseteq (thickening δ (t
hickening δ E)ᶜ)ᶜ

--- 原说明 ---
The δ-thickening of the complement of the δ-thickening of a set is contained in 
the complement
of the set.
-/
lemma thickening_compl_thickening_self_subset_compl (δ : ℝ) (E : Set α) :
    thickening δ (thickening δ E)ᶜ ⊆ Eᶜ := by
  apply compl_subset_compl.mp
  simpa only [compl_compl] using subset_compl_thickening_compl_thickening_self δ E

variable {X : Type u} [PseudoMetricSpace X]
/-
**Metric.mem_thickening_iff_infDist_lt** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：mem_thickening_iff_infDist_lt {E : Set X} {x : X} (h : E.Nonempty) : x in 
thickening δ E ↔ infDist x E < δ
参数：h : E.Nonempty。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.lt_ofReal_iff_toReal_lt`：lt_ofReal_iff_toReal_lt {a : Real>=0∞} 
{b : Real} (ha : a != ∞) : a < ENNReal.ofReal b ↔ ENNReal.toReal a < b
· 使用定理 `Metric.infEDist_ne_top`：infEDist_ne_top (h : s.Nonempty) : infEDist x s 
!= ∞
-/
theorem mem_thickening_iff_infDist_lt {E : Set X} {x : X} (h : E.Nonempty) :
    x ∈ thickening δ E ↔ infDist x E < δ :=
  lt_ofReal_iff_toReal_lt (infEDist_ne_top h)

/-- A point in a metric space belongs to the (open) `δ`-thickening of a subset `E` if and only if
it is at distance less than `δ` from some point of `E`. -/
/-
**Metric.mem_thickening_iff** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：mem_thickening_iff {E : Set X} {x : X} : x in thickening δ E ↔ exists z in
 E, dist x z < δ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_edist`：dist_edist (x y : α) : dist x y = (edist x y).toReal
· 使用定理 `ENNReal.lt_ofReal_iff_toReal_lt`：lt_ofReal_iff_toReal_lt {a : Real>=0∞} 
{b : Real} (ha : a != ∞) : a < ENNReal.ofReal b ↔ ENNReal.toReal a < b
· 使用定理 `edist_ne_top`：edist_ne_top (x y : α) : edist x y != ⊤
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A point in a metric space belongs to the (open) `δ`-thickening of a subset `E` i
f and only if
it is at distance less than `δ` from some point of `E`.
-/
theorem mem_thickening_iff {E : Set X} {x : X} : x ∈ thickening δ E ↔ ∃ z ∈ E, dist x z < δ := by
  have key_iff : ∀ z : X, edist x z < ENNReal.ofReal δ ↔ dist x z < δ := fun z ↦ by
    rw [dist_edist, lt_ofReal_iff_toReal_lt (edist_ne_top _ _)]
  simp_rw [mem_thickening_iff_exists_edist_lt, key_iff]

@[simp]
/-
**Metric.thickening_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：thickening_singleton (δ : Real) (x : X) : thickening δ ({x} : Set X) = bal
l x δ
参数：δ : Real；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem thickening_singleton (δ : ℝ) (x : X) : thickening δ ({x} : Set X) = ball x δ := by
  ext
  simp [mem_thickening_iff]
/-
**Metric.ball_subset_thickening** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：ball_subset_thickening {x : X} {E : Set X} (hx : x in E) (δ : Real) : ball
 x δ subseteq thickening δ E
参数：hx : x in E；δ : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.thickening_singleton`：thickening_singleton (δ : Real) (x : X) : t
hickening δ ({x} : Set X) = ball x δ
· 使用定理 `Metric.thickening_subset_of_subset`：thickening_subset_of_subset (δ : Rea
l) {E₁ E₂ : Set α} (h : E₁ subseteq E₂) : thickening δ E₁ subseteq thickening δ 
E₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
-/
theorem ball_subset_thickening {x : X} {E : Set X} (hx : x ∈ E) (δ : ℝ) :
    ball x δ ⊆ thickening δ E :=
  Subset.trans (by simp) (thickening_subset_of_subset δ <| singleton_subset_iff.mpr hx)

/-- The (open) `δ`-thickening `Metric.thickening δ E` of a subset `E` in a metric space equals the
union of balls of radius `δ` centered at points of `E`. -/
/-
**Metric.thickening_eq_biUnion_ball** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：thickening_eq_biUnion_ball {δ : Real} {E : Set X} : thickening δ E = ⋃ x i
n E, ball x δ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Metric.mem_thickening_iff`：mem_thickening_iff {E : Set X} {x : X} : x in
 thickening δ E ↔ exists z in E, dist x z < δ

--- 原说明 ---
The (open) `δ`-thickening `Metric.thickening δ E` of a subset `E` in a metric sp
ace equals the
union of balls of radius `δ` centered at points of `E`.
-/
theorem thickening_eq_biUnion_ball {δ : ℝ} {E : Set X} : thickening δ E = ⋃ x ∈ E, ball x δ := by
  ext x
  simp only [mem_iUnion₂, exists_prop]
  exact mem_thickening_iff
/-
**Metric._root_.Bornology.IsBounded.thickening** 是 Mathlib 中的一个定理，位于命名空间 `Metric
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem _root_.Bornology.IsBounded.thickening {δ : ℝ} {E : Set X} (h : IsBounded E) :
    IsBounded (thickening δ E) := by
  rcases E.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · simp
  · refine (isBounded_iff_subset_closedBall x).2 ⟨δ + diam E, fun y hy ↦ ?_⟩
    calc
      dist y x ≤ infDist y E + diam E := dist_le_infDist_add_diam (x := y) h hx
      _ ≤ δ + diam E := by grw [(mem_thickening_iff_infDist_lt ⟨x, hx⟩).1 hy]

end Thickening

section Cthickening

variable [PseudoEMetricSpace α] {δ ε : ℝ} {s t : Set α} {x : α}

open EMetric

/-- The closed `δ`-thickening `Metric.cthickening δ E` of a subset `E` in a pseudo emetric space
consists of those points that are at infimum distance at most `δ` from `E`. -/
/-
**Metric.cthickening** 是 Mathlib 中的一个定义，位于命名空间 `Metric`。
形式化陈述：cthickening (δ : Real) (E : Set α) : Set α
参数：δ : Real；E : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The closed `δ`-thickening `Metric.cthickening δ E` of a subset `E` in a pseudo e
metric space
consists of those points that are at infimum distance at most `δ` from `E`.
-/
def cthickening (δ : ℝ) (E : Set α) : Set α :=
  { x : α | infEDist x E ≤ ENNReal.ofReal δ }

@[simp]
/-
**Metric.mem_cthickening_iff** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：mem_cthickening_iff : x in cthickening δ s ↔ infEDist x s <= ENNReal.ofRea
l δ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_cthickening_iff : x ∈ cthickening δ s ↔ infEDist x s ≤ ENNReal.ofReal δ :=
  Iff.rfl

/-- An exterior point of a subset `E` (i.e., a point outside the closure of `E`) is not in the
closed `δ`-thickening of `E` for small enough positive `δ`. -/
/-
**Metric.eventually_notMem_cthickening_of_infEDist_pos** 是 Mathlib 中的一个引理，位于命名空间
 `Metric`。
形式化陈述：eventually_notMem_cthickening_of_infEDist_pos {E : Set α} {x : α} (h : x ∉
 closure E) : forallᶠ δ in 𝓝 (0 : Real), x ∉ Metric.cthickening δ E
参数：h : x ∉ closure E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.exists_real_pos_lt_infEDist_of_notMem_closure`：exists_real_pos_lt
_infEDist_of_notMem_closure {x : α} {E : Set α} (h : x ∉ closure E) : exists ε :
 Real, 0 < ε ∧ ENNReal.ofReal ε < infEDist…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `eventually_lt_nhds`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 :
 LinearOrder α] [ClosedIciTopology α] {a b : α},   a < b → ∀ᶠ (x : α) in nhds a,
 x < b
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.ofReal_lt_ofReal_iff`：ofReal_lt_ofReal_iff {p q : Real} (h : 0 <
 q) : ENNReal.ofReal p < ENNReal.ofReal q ↔ p < q

--- 原说明 ---
An exterior point of a subset `E` (i.e., a point outside the closure of `E`) is 
not in the
closed `δ`-thickening of `E` for small enough positive `δ`.
-/
lemma eventually_notMem_cthickening_of_infEDist_pos {E : Set α} {x : α} (h : x ∉ closure E) :
    ∀ᶠ δ in 𝓝 (0 : ℝ), x ∉ Metric.cthickening δ E := by
  obtain ⟨ε, ⟨ε_pos, ε_lt⟩⟩ := exists_real_pos_lt_infEDist_of_notMem_closure h
  filter_upwards [eventually_lt_nhds ε_pos] with δ hδ
  simp only [cthickening, mem_ofPred_eq, not_le]
  exact ((ofReal_lt_ofReal_iff ε_pos).mpr hδ).trans ε_lt

@[deprecated (since := "2026-01-08")]
alias eventually_notMem_cthickening_of_infEdist_pos :=
  eventually_notMem_cthickening_of_infEDist_pos
/-
**Metric.mem_cthickening_of_edist_le** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：mem_cthickening_of_edist_le (x y : α) (δ : Real) (E : Set α) (h : y in E) 
(h' : edist x y <= ENNReal.ofReal δ) : x in cthickening δ E
参数：x y : α；δ : Real；E : Set α；h : y in E；h' : edist x y <= ENNReal.ofReal δ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Metric.infEDist_le_edist_of_mem`：infEDist_le_edist_of_mem (h : y in s) :
 infEDist x s <= edist x y
-/
theorem mem_cthickening_of_edist_le (x y : α) (δ : ℝ) (E : Set α) (h : y ∈ E)
    (h' : edist x y ≤ ENNReal.ofReal δ) : x ∈ cthickening δ E :=
  (infEDist_le_edist_of_mem h).trans h'
/-
**Metric.mem_cthickening_of_dist_le** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：mem_cthickening_of_dist_le {α : Type*} [PseudoMetricSpace α] (x y : α) (δ 
: Real) (E : Set α) (h : y in E) (h' : dist x y <= δ) : x in cthickening δ E
参数：x y : α；δ : Real；E : Set α；h : y in E；h' : dist x y <= δ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.mem_cthickening_of_edist_le`：mem_cthickening_of_edist_le (x y : α
) (δ : Real) (E : Set α) (h : y in E) (h' : edist x y <= ENNReal.ofReal δ) : x i
n cthickening δ E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `edist_dist`：edist_dist (x y : α) : edist x y = ENNReal.ofReal (dist x y)
· 使用定理 `ENNReal.ofReal_le_ofReal`：ofReal_le_ofReal {p q : Real} (h : p <= q) : E
NNReal.ofReal p <= ENNReal.ofReal q
-/
theorem mem_cthickening_of_dist_le {α : Type*} [PseudoMetricSpace α] (x y : α) (δ : ℝ) (E : Set α)
    (h : y ∈ E) (h' : dist x y ≤ δ) : x ∈ cthickening δ E := by
  apply mem_cthickening_of_edist_le x y δ E h
  rw [edist_dist]
  exact ENNReal.ofReal_le_ofReal h'
/-
**Metric.cthickening_eq_preimage_infEDist** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：cthickening_eq_preimage_infEDist (δ : Real) (E : Set α) : cthickening δ E 
= (fun x => infEDist x E) ⁻¹' Iic (ENNReal.ofReal δ)
参数：δ : Real；E : Set α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cthickening_eq_preimage_infEDist (δ : ℝ) (E : Set α) :
    cthickening δ E = (fun x => infEDist x E) ⁻¹' Iic (ENNReal.ofReal δ) :=
  rfl

@[deprecated (since := "2026-01-08")]
alias cthickening_eq_preimage_infEdist := cthickening_eq_preimage_infEDist

/-- The closed thickening is a closed set. -/
/-
**Metric.isClosed_cthickening** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：isClosed_cthickening {δ : Real} {E : Set α} : IsClosed (cthickening δ E)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `Metric.continuous_infEDist`：continuous_infEDist : Continuous fun x => in
fEDist x s
· 使用定理 `isClosed_Iic`：isClosed_Iic : IsClosed (Iic a)
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal

--- 原说明 ---
The closed thickening is a closed set.
-/
theorem isClosed_cthickening {δ : ℝ} {E : Set α} : IsClosed (cthickening δ E) :=
  IsClosed.preimage continuous_infEDist isClosed_Iic

/-- The closed thickening of the empty set is empty. -/
@[simp]
/-
**Metric.cthickening_empty** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：cthickening_empty (δ : Real) : cthickening δ (∅ : Set α) = ∅
参数：δ : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Metric.infEDist_empty`：infEDist_empty : infEDist x ∅ = ∞
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The closed thickening of the empty set is empty.
-/
theorem cthickening_empty (δ : ℝ) : cthickening δ (∅ : Set α) = ∅ := by
  simp only [cthickening, ENNReal.ofReal_ne_top, ofPred_false, infEDist_empty, top_le_iff]
/-
**Metric.cthickening_of_nonpos** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：cthickening_of_nonpos {δ : Real} (hδ : δ <= 0) (E : Set α) : cthickening δ
 E = closure E
参数：hδ : δ <= 0；E : Set α。
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
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.ofReal_eq_zero`：ofReal_eq_zero {p : Real} : ENNReal.ofReal p = 0
 ↔ p <= 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem cthickening_of_nonpos {δ : ℝ} (hδ : δ ≤ 0) (E : Set α) : cthickening δ E = closure E := by
  ext x
  simp [mem_closure_iff_infEDist_zero, cthickening, ENNReal.ofReal_eq_zero.2 hδ]

/-- The closed thickening with radius zero is the closure of the set. -/
@[simp]
/-
**Metric.cthickening_zero** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：cthickening_zero (E : Set α) : cthickening 0 E = closure E
参数：E : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.cthickening_of_nonpos`：cthickening_of_nonpos {δ : Real} (hδ : δ <
= 0) (E : Set α) : cthickening δ E = closure E
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
The closed thickening with radius zero is the closure of the set.
-/
theorem cthickening_zero (E : Set α) : cthickening 0 E = closure E :=
  cthickening_of_nonpos le_rfl E
/-
**Metric.cthickening_max_zero** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：cthickening_max_zero (δ : Real) (E : Set α) : cthickening (max 0 δ) E = ct
hickening δ E
参数：δ : Real；E : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `Metric.cthickening_of_nonpos`：cthickening_of_nonpos {δ : Real} (hδ : δ <
= 0) (E : Set α) : cthickening δ E = closure E
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
-/
theorem cthickening_max_zero (δ : ℝ) (E : Set α) : cthickening (max 0 δ) E = cthickening δ E := by
  cases le_total δ 0 <;> simp [cthickening_of_nonpos, *]

/-- The closed thickening `Metric.cthickening δ E` of a fixed subset `E` is an increasing function
of the thickening radius `δ`. -/
/-
**Metric.cthickening_mono** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：cthickening_mono {δ₁ δ₂ : Real} (hle : δ₁ <= δ₂) (E : Set α) : cthickening
 δ₁ E subseteq cthickening δ₂ E
参数：hle : δ₁ <= δ₂；E : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Iic_subset_Iic`：Iic_subset_Iic : Iic a subseteq Iic b ↔ a <= b
· 使用定理 `ENNReal.ofReal_le_ofReal`：ofReal_le_ofReal {p q : Real} (h : p <= q) : E
NNReal.ofReal p <= ENNReal.ofReal q

--- 原说明 ---
The closed thickening `Metric.cthickening δ E` of a fixed subset `E` is an incre
asing function
of the thickening radius `δ`.
-/
theorem cthickening_mono {δ₁ δ₂ : ℝ} (hle : δ₁ ≤ δ₂) (E : Set α) :
    cthickening δ₁ E ⊆ cthickening δ₂ E :=
  preimage_mono (Iic_subset_Iic.mpr (ENNReal.ofReal_le_ofReal hle))

@[simp]
/-
**Metric.cthickening_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：cthickening_singleton {α : Type*} [PseudoMetricSpace α] (x : α) {δ : Real}
 (hδ : 0 <= δ) : cthickening δ ({x} : Set α) = closedBall x δ
参数：x : α；hδ : 0 <= δ。
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
· 使用定理 `Metric.infEDist_singleton`：infEDist_singleton : infEDist x {y} = edist x
 y
· 使用定理 `edist_dist`：edist_dist (x y : α) : edist x y = ENNReal.ofReal (dist x y)
· 使用定理 `ENNReal.ofReal_le_ofReal_iff`：ofReal_le_ofReal_iff {p q : Real} (h : 0 <
= q) : ENNReal.ofReal p <= ENNReal.ofReal q ↔ p <= q
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem cthickening_singleton {α : Type*} [PseudoMetricSpace α] (x : α) {δ : ℝ} (hδ : 0 ≤ δ) :
    cthickening δ ({x} : Set α) = closedBall x δ := by
  ext y
  simp [cthickening, edist_dist, ENNReal.ofReal_le_ofReal_iff hδ]
/-
**Metric.closedBall_subset_cthickening_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Metr
ic`。
形式化陈述：closedBall_subset_cthickening_singleton {α : Type*} [PseudoMetricSpace α] 
(x : α) (δ : Real) : closedBall x δ subseteq cthickening δ ({x} : Set α)
参数：x : α；δ : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.closedBall_eq_empty`：closedBall_eq_empty : closedBall x ε = ∅ ↔ ε
 < 0
· 使用定理 `Metric.cthickening_singleton`：cthickening_singleton {α : Type*} [PseudoM
etricSpace α] (x : α) {δ : Real} (hδ : 0 <= δ) : cthickening δ ({x} : Set α) = c
losedBall x δ
-/
theorem closedBall_subset_cthickening_singleton {α : Type*} [PseudoMetricSpace α] (x : α) (δ : ℝ) :
    closedBall x δ ⊆ cthickening δ ({x} : Set α) := by
  rcases lt_or_ge δ 0 with (hδ | hδ)
  · simp only [closedBall_eq_empty.mpr hδ, empty_subset]
  · simp only [cthickening_singleton x hδ, Subset.rfl]

/-- The closed thickening `Metric.cthickening δ E` with a fixed thickening radius `δ` is
an increasing function of the subset `E`. -/
/-
**Metric.cthickening_subset_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：cthickening_subset_of_subset (δ : Real) {E₁ E₂ : Set α} (h : E₁ subseteq E
₂) : cthickening δ E₁ subseteq cthickening δ E₂
参数：δ : Real；h : E₁ subseteq E₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Metric.infEDist_anti`：infEDist_anti (h : s subseteq t) : infEDist x t <=
 infEDist x s

--- 原说明 ---
The closed thickening `Metric.cthickening δ E` with a fixed thickening radius `δ
` is
an increasing function of the subset `E`.
-/
theorem cthickening_subset_of_subset (δ : ℝ) {E₁ E₂ : Set α} (h : E₁ ⊆ E₂) :
    cthickening δ E₁ ⊆ cthickening δ E₂ := fun _ hx => le_trans (infEDist_anti h) hx
/-
**Metric.cthickening_subset_thickening** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：cthickening_subset_thickening {δ₁ : Real>=0} {δ₂ : Real} (hlt : (δ₁ : Real
) < δ₂) (E : Set α) : cthickening δ₁ E subseteq thickening δ₂ E
参数：hlt : (δ₁ : Real) < δ₂；E : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Membership.mem.out`：∀ {α : Type u} {a : α} {p : α → Prop}, a ∈ {x | p x}
 → p a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.ofReal_lt_ofReal_iff`：ofReal_lt_ofReal_iff {p q : Real} (h : 0 <
 q) : ENNReal.ofReal p < ENNReal.ofReal q ↔ p < q
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
theorem cthickening_subset_thickening {δ₁ : ℝ≥0} {δ₂ : ℝ} (hlt : (δ₁ : ℝ) < δ₂) (E : Set α) :
    cthickening δ₁ E ⊆ thickening δ₂ E := fun _ hx =>
  hx.out.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt δ₁.prop hlt)).mpr hlt)

/-- The closed thickening `Metric.cthickening δ₁ E` is contained in the open thickening
`Metric.thickening δ₂ E` if the radius of the latter is positive and larger. -/
/-
**Metric.cthickening_subset_thickening'** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：cthickening_subset_thickening' {δ₁ δ₂ : Real} (δ₂_pos : 0 < δ₂) (hlt : δ₁ 
< δ₂) (E : Set α) : cthickening δ₁ E subseteq thickening δ₂ E
参数：δ₂_pos : 0 < δ₂；hlt : δ₁ < δ₂；E : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Membership.mem.out`：∀ {α : Type u} {a : α} {p : α → Prop}, a ∈ {x | p x}
 → p a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.ofReal_lt_ofReal_iff`：ofReal_lt_ofReal_iff {p q : Real} (h : 0 <
 q) : ENNReal.ofReal p < ENNReal.ofReal q ↔ p < q

--- 原说明 ---
The closed thickening `Metric.cthickening δ₁ E` is contained in the open thicken
ing
`Metric.thickening δ₂ E` if the radius of the latter is positive and larger.
-/
theorem cthickening_subset_thickening' {δ₁ δ₂ : ℝ} (δ₂_pos : 0 < δ₂) (hlt : δ₁ < δ₂) (E : Set α) :
    cthickening δ₁ E ⊆ thickening δ₂ E := fun _ hx =>
  lt_of_le_of_lt hx.out ((ENNReal.ofReal_lt_ofReal_iff δ₂_pos).mpr hlt)

/-- The open thickening `Metric.thickening δ E` is contained in the closed thickening
`Metric.cthickening δ E` with the same radius. -/
/-
**Metric.thickening_subset_cthickening** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：thickening_subset_cthickening (δ : Real) (E : Set α) : thickening δ E subs
eteq cthickening δ E
参数：δ : Real；E : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `Metric.thickening.eq_1`：∀ {α : Type u} [inst : PseudoEMetricSpace α] (δ 
: ℝ) (E : Set α),   Metric.thickening δ E = {x | Metric.infEDist x E < ENNReal.o
fReal δ}

--- 原说明 ---
The open thickening `Metric.thickening δ E` is contained in the closed thickenin
g
`Metric.cthickening δ E` with the same radius.
-/
theorem thickening_subset_cthickening (δ : ℝ) (E : Set α) : thickening δ E ⊆ cthickening δ E := by
  intro x hx
  rw [thickening, mem_ofPred_eq] at hx
  exact hx.le
/-
**Metric.thickening_subset_cthickening_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：thickening_subset_cthickening_of_le {δ₁ δ₂ : Real} (hle : δ₁ <= δ₂) (E : S
et α) : thickening δ₁ E subseteq cthickening δ₂ E
参数：hle : δ₁ <= δ₂；E : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Metric.thickening_subset_cthickening`：thickening_subset_cthickening (δ :
 Real) (E : Set α) : thickening δ E subseteq cthickening δ E
· 使用定理 `Metric.cthickening_mono`：cthickening_mono {δ₁ δ₂ : Real} (hle : δ₁ <= δ₂
) (E : Set α) : cthickening δ₁ E subseteq cthickening δ₂ E
-/
theorem thickening_subset_cthickening_of_le {δ₁ δ₂ : ℝ} (hle : δ₁ ≤ δ₂) (E : Set α) :
    thickening δ₁ E ⊆ cthickening δ₂ E :=
  (thickening_subset_cthickening δ₁ E).trans (cthickening_mono hle E)
/-
**Metric._root_.Bornology.IsBounded.cthickening** 是 Mathlib 中的一个定理，位于命名空间 `Metri
c`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Bornology.IsBounded.cthickening {α : Type*} [PseudoMetricSpace α] {δ : ℝ} {E : Set α}
    (h : IsBounded E) : IsBounded (cthickening δ E) := by
  have : IsBounded (thickening (max (δ + 1) 1) E) := h.thickening
  apply this.subset
  exact cthickening_subset_thickening' (zero_lt_one.trans_le (le_max_right _ _))
    ((lt_add_one _).trans_le (le_max_left _ _)) _
/-
**Metric._root_.IsCompact.cthickening** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem _root_.IsCompact.cthickening
    {α : Type*} [PseudoMetricSpace α] [ProperSpace α] {s : Set α}
    (hs : IsCompact s) {r : ℝ} : IsCompact (cthickening r s) :=
  isCompact_of_isClosed_isBounded isClosed_cthickening hs.isBounded.cthickening
/-
**Metric.thickening_subset_interior_cthickening** 是 Mathlib 中的一个定理，位于命名空间 `Metri
c`。
形式化陈述：thickening_subset_interior_cthickening (δ : Real) (E : Set α) : thickening
 δ E subseteq interior (cthickening δ E)
参数：δ : Real；E : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `subset_interior_iff_isOpen`：subset_interior_iff_isOpen : s subseteq inte
rior s ↔ IsOpen s
· 使用定理 `Metric.isOpen_thickening`：isOpen_thickening {δ : Real} {E : Set α} : IsO
pen (thickening δ E)
· 使用定理 `interior_mono`：interior_mono (h : s subseteq t) : interior s subseteq in
terior t
· 使用定理 `Metric.thickening_subset_cthickening`：thickening_subset_cthickening (δ :
 Real) (E : Set α) : thickening δ E subseteq cthickening δ E
-/
theorem thickening_subset_interior_cthickening (δ : ℝ) (E : Set α) :
    thickening δ E ⊆ interior (cthickening δ E) :=
  (subset_interior_iff_isOpen.mpr isOpen_thickening).trans
    (interior_mono (thickening_subset_cthickening δ E))
/-
**Metric.closure_thickening_subset_cthickening** 是 Mathlib 中的一个定理，位于命名空间 `Metric
`。
形式化陈述：closure_thickening_subset_cthickening (δ : Real) (E : Set α) : closure (th
ickening δ E) subseteq cthickening δ E
参数：δ : Real；E : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `Metric.thickening_subset_cthickening`：thickening_subset_cthickening (δ :
 Real) (E : Set α) : thickening δ E subseteq cthickening δ E
· 使用定理 `IsClosed.closure_subset`：IsClosed.closure_subset (hs : IsClosed s) : clo
sure s subseteq s
· 使用定理 `Metric.isClosed_cthickening`：isClosed_cthickening {δ : Real} {E : Set α}
 : IsClosed (cthickening δ E)
-/
theorem closure_thickening_subset_cthickening (δ : ℝ) (E : Set α) :
    closure (thickening δ E) ⊆ cthickening δ E :=
  (closure_mono (thickening_subset_cthickening δ E)).trans isClosed_cthickening.closure_subset

/-- The closed thickening of a set contains the closure of the set. -/
/-
**Metric.closure_subset_cthickening** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：closure_subset_cthickening (δ : Real) (E : Set α) : closure E subseteq cth
ickening δ E
参数：δ : Real；E : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Metric.cthickening_of_nonpos`：cthickening_of_nonpos {δ : Real} (hδ : δ <
= 0) (E : Set α) : cthickening δ E = closure E
· 使用引理 `min_le_right`：min_le_right (a b : α) : min a b <= b
· 使用定理 `Metric.cthickening_mono`：cthickening_mono {δ₁ δ₂ : Real} (hle : δ₁ <= δ₂
) (E : Set α) : cthickening δ₁ E subseteq cthickening δ₂ E
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a

--- 原说明 ---
The closed thickening of a set contains the closure of the set.
-/
theorem closure_subset_cthickening (δ : ℝ) (E : Set α) : closure E ⊆ cthickening δ E := by
  rw [← cthickening_of_nonpos (min_le_right δ 0)]
  exact cthickening_mono (min_le_left δ 0) E

/-- The (open) thickening of a set contains the closure of the set. -/
/-
**Metric.closure_subset_thickening** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：closure_subset_thickening {δ : Real} (δ_pos : 0 < δ) (E : Set α) : closure
 E subseteq thickening δ E
参数：δ_pos : 0 < δ；E : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Metric.cthickening_zero`：cthickening_zero (E : Set α) : cthickening 0 E 
= closure E
· 使用定理 `Metric.cthickening_subset_thickening'`：cthickening_subset_thickening' {δ
₁ δ₂ : Real} (δ₂_pos : 0 < δ₂) (hlt : δ₁ < δ₂) (E : Set α) : cthickening δ₁ E su
bseteq thickening δ₂ E

--- 原说明 ---
The (open) thickening of a set contains the closure of the set.
-/
theorem closure_subset_thickening {δ : ℝ} (δ_pos : 0 < δ) (E : Set α) :
    closure E ⊆ thickening δ E := by
  rw [← cthickening_zero]
  exact cthickening_subset_thickening' δ_pos δ_pos E

/-- A set is contained in its own (open) thickening. -/
/-
**Metric.self_subset_thickening** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：self_subset_thickening {δ : Real} (δ_pos : 0 < δ) (E : Set α) : E subseteq
 thickening δ E
参数：δ_pos : 0 < δ；E : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Metric.closure_subset_thickening`：closure_subset_thickening {δ : Real} (
δ_pos : 0 < δ) (E : Set α) : closure E subseteq thickening δ E

--- 原说明 ---
A set is contained in its own (open) thickening.
-/
theorem self_subset_thickening {δ : ℝ} (δ_pos : 0 < δ) (E : Set α) : E ⊆ thickening δ E :=
  (@subset_closure _ _ E).trans (closure_subset_thickening δ_pos E)

/-- A set is contained in its own closed thickening. -/
/-
**Metric.self_subset_cthickening** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：self_subset_cthickening {δ : Real} (E : Set α) : E subseteq cthickening δ 
E
参数：E : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Metric.closure_subset_cthickening`：closure_subset_cthickening (δ : Real)
 (E : Set α) : closure E subseteq cthickening δ E

--- 原说明 ---
A set is contained in its own closed thickening.
-/
theorem self_subset_cthickening {δ : ℝ} (E : Set α) : E ⊆ cthickening δ E :=
  subset_closure.trans (closure_subset_cthickening δ E)
/-
**Metric.thickening_mem_nhdsSet** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：thickening_mem_nhdsSet (E : Set α) {δ : Real} (hδ : 0 < δ) : thickening δ 
E in 𝓝ˢ E
参数：E : Set α；hδ : 0 < δ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsOpen.mem_nhdsSet`：IsOpen.mem_nhdsSet (hU : IsOpen s) : s in 𝓝ˢ t ↔ t s
ubseteq s
· 使用定理 `Metric.isOpen_thickening`：isOpen_thickening {δ : Real} {E : Set α} : IsO
pen (thickening δ E)
· 使用定理 `Metric.self_subset_thickening`：self_subset_thickening {δ : Real} (δ_pos 
: 0 < δ) (E : Set α) : E subseteq thickening δ E
-/
theorem thickening_mem_nhdsSet (E : Set α) {δ : ℝ} (hδ : 0 < δ) : thickening δ E ∈ 𝓝ˢ E :=
  isOpen_thickening.mem_nhdsSet.2 <| self_subset_thickening hδ E
/-
**Metric.cthickening_mem_nhdsSet** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：cthickening_mem_nhdsSet (E : Set α) {δ : Real} (hδ : 0 < δ) : cthickening 
δ E in 𝓝ˢ E
参数：E : Set α；hδ : 0 < δ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Metric.thickening_mem_nhdsSet`：thickening_mem_nhdsSet (E : Set α) {δ : R
eal} (hδ : 0 < δ) : thickening δ E in 𝓝ˢ E
· 使用定理 `Metric.thickening_subset_cthickening`：thickening_subset_cthickening (δ :
 Real) (E : Set α) : thickening δ E subseteq cthickening δ E
-/
theorem cthickening_mem_nhdsSet (E : Set α) {δ : ℝ} (hδ : 0 < δ) : cthickening δ E ∈ 𝓝ˢ E :=
  mem_of_superset (thickening_mem_nhdsSet E hδ) (thickening_subset_cthickening _ _)

@[simp]
/-
**Metric.thickening_union** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：thickening_union (δ : Real) (s t : Set α) : thickening δ (s union t) = thi
ckening δ s union thickening δ t
参数：δ : Real；s t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Metric.infEDist_union`：infEDist_union : infEDist x (s union t) = infEDis
t x s ⊓ infEDist x t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem thickening_union (δ : ℝ) (s t : Set α) :
    thickening δ (s ∪ t) = thickening δ s ∪ thickening δ t := by
  simp_rw [thickening, infEDist_union, min_lt_iff, ofPred_or]

@[simp]
/-
**Metric.cthickening_union** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：cthickening_union (δ : Real) (s t : Set α) : cthickening δ (s union t) = c
thickening δ s union cthickening δ t
参数：δ : Real；s t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Metric.infEDist_union`：infEDist_union : infEDist x (s union t) = infEDis
t x s ⊓ infEDist x t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cthickening_union (δ : ℝ) (s t : Set α) :
    cthickening δ (s ∪ t) = cthickening δ s ∪ cthickening δ t := by
  simp_rw [cthickening, infEDist_union, min_le_iff, ofPred_or]

@[simp]
/-
**Metric.thickening_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：thickening_iUnion (δ : Real) (f : ι -> Set α) : thickening δ (⋃ i, f i) = 
⋃ i, thickening δ (f i)
参数：δ : Real；f : ι -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Metric.infEDist_iUnion`：infEDist_iUnion (f : ι -> Set α) (x : α) : infED
ist x (⋃ i, f i) = ⨅ i, infEDist x (f i)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.ofPred_exists`：ofPred_exists (p : ι -> β -> Prop) : { x | exists i, 
p i x } = ⋃ i, { x | p i x }
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem thickening_iUnion (δ : ℝ) (f : ι → Set α) :
    thickening δ (⋃ i, f i) = ⋃ i, thickening δ (f i) := by
  simp_rw [thickening, infEDist_iUnion, iInf_lt_iff, ofPred_exists]
/-
**Metric.thickening_biUnion** 是 Mathlib 中的一个引理，位于命名空间 `Metric`。
形式化陈述：thickening_biUnion {ι : Type*} (δ : Real) (f : ι -> Set α) (I : Set ι) : t
hickening δ (⋃ i in I, f i) = ⋃ i in I, thickening δ (f i)
参数：δ : Real；f : ι -> Set α；I : Set ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.thickening_iUnion`：thickening_iUnion (δ : Real) (f : ι -> Set α) 
: thickening δ (⋃ i, f i) = ⋃ i, thickening δ (f i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma thickening_biUnion {ι : Type*} (δ : ℝ) (f : ι → Set α) (I : Set ι) :
    thickening δ (⋃ i ∈ I, f i) = ⋃ i ∈ I, thickening δ (f i) := by simp only [thickening_iUnion]
/-
**Metric.ediam_cthickening_le** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：ediam_cthickening_le (ε : Real>=0) : ediam (cthickening ε s) <= ediam s + 
2 * ε
参数：ε : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.ediam_le`：ediam_le {d : Real>=0∞} (h : forall x in s, forall y in
 s, edist x y <= d) : ediam s <= d
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ENNReal.le_of_forall_pos_le_add`：le_of_forall_pos_le_add (h : forall ε :
 Real>=0, 0 < ε -> b < ∞ -> a <= b + ε) : a <= b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_lt_coe`：∀ {r q : NNReal}, ↑r < ↑q ↔ r < q
· 使用定理 `lt_add_of_pos_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : 
LT α] [AddLeftStrictMono α] (a : α) {b : α}, 0 < b → a < a + b
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.ofReal_coe_nnreal`：∀ {p : NNReal}, ENNReal.ofReal ↑p = ↑p
· 使用定理 `Metric.mem_cthickening_iff`：mem_cthickening_iff : x in cthickening δ s ↔
 infEDist x s <= ENNReal.ofReal δ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.infEDist_lt_iff`：infEDist_lt_iff {r : Real>=0∞} : infEDist x s < 
r ↔ exists y in s, edist x y < r
· 使用定理 `edist_triangle_right`：edist_triangle_right (x y z : α) : edist x y <= ed
ist x z + edist y z
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Metric.edist_le_infEDist_add_ediam`：edist_le_infEDist_add_ediam (hy : y 
in s) : edist x y <= infEDist x s + Metric.ediam s
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Lean.Data.AC.Context.eq_of_norm`：∀ {α : Sort u_1} (ctx : Data.AC.Context
 α) (a b : Data.AC.Expr),   (Data.AC.norm ctx a == Data.AC.norm ctx b) = true → 
Data.AC.eval α ctx a …
（共 33 条，此处仅展示前 30 条）
-/
theorem ediam_cthickening_le (ε : ℝ≥0) :
    ediam (cthickening ε s) ≤ ediam s + 2 * ε := by
  refine ediam_le fun x hx y hy => ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
  rw [mem_cthickening_iff, ENNReal.ofReal_coe_nnreal] at hx hy
  have hε : (ε : ℝ≥0∞) < ε + δ := ENNReal.coe_lt_coe.2 (lt_add_of_pos_right _ hδ)
  replace hx := hx.trans_lt hε
  obtain ⟨x', hx', hxx'⟩ := infEDist_lt_iff.mp hx
  calc
    edist x y ≤ edist x x' + edist y x' := edist_triangle_right _ _ _
    _ ≤ ε + δ + (infEDist y s + ediam s) :=
      add_le_add hxx'.le (edist_le_infEDist_add_ediam hx')
    _ ≤ ε + δ + (ε + ediam s) := by grw [hy]
    _ = _ := by rw [two_mul]; ac_rfl
/-
**Metric.ediam_thickening_le** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：ediam_thickening_le (ε : Real>=0) : ediam (thickening ε s) <= ediam s + 2 
* ε
参数：ε : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Metric.ediam_mono`：ediam_mono (h : s subseteq t) : ediam s <= ediam t
· 使用定理 `Metric.thickening_subset_cthickening`：thickening_subset_cthickening (δ :
 Real) (E : Set α) : thickening δ E subseteq cthickening δ E
· 使用定理 `Metric.ediam_cthickening_le`：ediam_cthickening_le (ε : Real>=0) : ediam 
(cthickening ε s) <= ediam s + 2 * ε
-/
theorem ediam_thickening_le (ε : ℝ≥0) : ediam (thickening ε s) ≤ ediam s + 2 * ε :=
  (ediam_mono <| thickening_subset_cthickening _ _).trans <| ediam_cthickening_le _
/-
**Metric.diam_cthickening_le** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：diam_cthickening_le {α : Type*} [PseudoMetricSpace α] (s : Set α) (hε : 0 
<= ε) : diam (cthickening ε s) <= diam s + 2 * ε
参数：s : Set α；hε : 0 <= ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `ENNReal.toReal_le_add'`：toReal_le_add' (hle : a <= b + c) (hb : b = ∞ ->
 a = ∞) (hc : c = ∞ -> a = ∞) : a.toReal <= b.toReal + c.toReal
· 使用定理 `Metric.ediam_cthickening_le`：ediam_cthickening_le (ε : Real>=0) : ediam 
(cthickening ε s) <= ediam s + 2 * ε
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用定理 `Metric.ediam_mono`：ediam_mono (h : s subseteq t) : ediam s <= ediam t
· 使用定理 `Metric.self_subset_cthickening`：self_subset_cthickening {δ : Real} (E : 
Set α) : E subseteq cthickening δ E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.toReal_mul`：toReal_mul : (a * b).toReal = a.toReal * b.toReal
· 使用定理 `ENNReal.toReal_ofNat`：∀ (n : ℕ) [inst : n.AtLeastTwo], (OfNat.ofNat n).t
oReal = OfNat.ofNat n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem diam_cthickening_le {α : Type*} [PseudoMetricSpace α] (s : Set α) (hε : 0 ≤ ε) :
    diam (cthickening ε s) ≤ diam s + 2 * ε := by
  lift ε to ℝ≥0 using hε
  refine (toReal_le_add' (ediam_cthickening_le _) ?_ ?_).trans_eq ?_
  · exact fun h ↦ top_unique <| h ▸ ediam_mono (self_subset_cthickening _)
  · simp [mul_eq_top]
  · simp [diam]
/-
**Metric.diam_thickening_le** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：diam_thickening_le {α : Type*} [PseudoMetricSpace α] (s : Set α) (hε : 0 <
= ε) : diam (thickening ε s) <= diam s + 2 * ε
参数：s : Set α；hε : 0 <= ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Metric.diam_mono`：diam_mono {s t : Set α} (h : s subseteq t) (ht : IsBou
nded t) : diam s <= diam t
· 使用定理 `Metric.thickening_subset_cthickening`：thickening_subset_cthickening (δ :
 Real) (E : Set α) : thickening δ E subseteq cthickening δ E
· 使用定理 `Bornology.IsBounded.cthickening`：∀ {α : Type u_2} [inst : PseudoMetricSp
ace α] {δ : ℝ} {E : Set α},   Bornology.IsBounded E → Bornology.IsBounded (Metri
c.cthickening δ E)
· 使用定理 `Metric.diam_cthickening_le`：diam_cthickening_le {α : Type*} [PseudoMetri
cSpace α] (s : Set α) (hε : 0 <= ε) : diam (cthickening ε s) <= diam s + 2 * ε
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.thickening_of_nonpos`：thickening_of_nonpos (hδ : δ <= 0) (s : Set
 α) : thickening δ s = ∅
· 使用定理 `Metric.diam_empty`：diam_empty : diam (∅ : Set α) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Metric.diam_eq_zero_of_unbounded`：diam_eq_zero_of_unbounded (h : ¬IsBoun
ded s) : diam s = 0
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Bornology.IsBounded.subset`：∀ {α : Type u_2} {x : Bornology α} {s t : Se
t α}, Bornology.IsBounded t → s ⊆ t → Bornology.IsBounded s
· 使用定理 `Metric.self_subset_thickening`：self_subset_thickening {δ : Real} (δ_pos 
: 0 < δ) (E : Set α) : E subseteq thickening δ E
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Right.add_pos_of_nonneg_of_pos`：∀ {α : Type u_1} [inst : AddZeroClass α]
 [inst_1 : Preorder α] [AddRightMono α] {a b : α}, 0 ≤ a → 0 < b → 0 < a + b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Metric.diam_nonneg`：diam_nonneg : 0 <= diam s
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
-/
theorem diam_thickening_le {α : Type*} [PseudoMetricSpace α] (s : Set α) (hε : 0 ≤ ε) :
    diam (thickening ε s) ≤ diam s + 2 * ε := by
  by_cases hs : IsBounded s
  · exact (diam_mono (thickening_subset_cthickening _ _) hs.cthickening).trans
      (diam_cthickening_le _ hε)
  obtain rfl | hε := hε.eq_or_lt
  · simp [thickening_of_nonpos, diam_nonneg]
  · rw [diam_eq_zero_of_unbounded (mt (IsBounded.subset · <| self_subset_thickening hε _) hs)]
    positivity

@[simp]
/-
**Metric.thickening_closure** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：thickening_closure : thickening δ (closure s) = thickening δ s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Metric.infEDist_closure`：infEDist_closure : infEDist x (closure s) = inf
EDist x s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem thickening_closure : thickening δ (closure s) = thickening δ s := by
  simp_rw [thickening, infEDist_closure]

@[simp]
/-
**Metric.cthickening_closure** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：cthickening_closure : cthickening δ (closure s) = cthickening δ s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Metric.infEDist_closure`：infEDist_closure : infEDist x (closure s) = inf
EDist x s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cthickening_closure : cthickening δ (closure s) = cthickening δ s := by
  simp_rw [cthickening, infEDist_closure]
/-
**Metric.thickening_eq_empty_iff_of_pos** 是 Mathlib 中的一个引理，位于命名空间 `Metric`。
形式化陈述：thickening_eq_empty_iff_of_pos (hε : 0 < ε) : thickening ε s = ∅ ↔ s = ∅
参数：hε : 0 < ε。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subset_eq_empty`：subset_eq_empty {s t : Set α} (h : t subseteq s) (e
 : s = ∅) : t = ∅
· 使用定理 `Metric.self_subset_thickening`：self_subset_thickening {δ : Real} (δ_pos 
: 0 < δ) (E : Set α) : E subseteq thickening δ E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.thickening_empty`：thickening_empty (δ : Real) : thickening δ (∅ :
 Set α) = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma thickening_eq_empty_iff_of_pos (hε : 0 < ε) :
    thickening ε s = ∅ ↔ s = ∅ :=
  ⟨fun h ↦ subset_eq_empty (self_subset_thickening hε _) h, by simp +contextual⟩
/-
**Metric.thickening_nonempty_iff_of_pos** 是 Mathlib 中的一个引理，位于命名空间 `Metric`。
形式化陈述：thickening_nonempty_iff_of_pos (hε : 0 < ε) : (thickening ε s).Nonempty ↔ 
s.Nonempty
参数：hε : 0 < ε。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Metric.thickening_eq_empty_iff_of_pos`：thickening_eq_empty_iff_of_pos (h
ε : 0 < ε) : thickening ε s = ∅ ↔ s = ∅
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma thickening_nonempty_iff_of_pos (hε : 0 < ε) :
    (thickening ε s).Nonempty ↔ s.Nonempty := by
  simp [nonempty_iff_ne_empty, thickening_eq_empty_iff_of_pos hε]
/-
**Metric.thickening_eq_empty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：∀ {α : Type u} [inst : PseudoEMetricSpace α] {ε : ℝ} {s : Set α}, Metric.t
hickening ε s = ∅ ↔ ε ≤ 0 ∨ s = ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Metric.thickening_of_nonpos`：thickening_of_nonpos (hδ : δ <= 0) (s : Set
 α) : thickening δ s = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma thickening_eq_empty_iff : thickening ε s = ∅ ↔ ε ≤ 0 ∨ s = ∅ := by
  obtain hε | hε := lt_or_ge 0 ε
  · simp [thickening_eq_empty_iff_of_pos, hε]
  · simp [hε, thickening_of_nonpos hε]
/-
**Metric.thickening_nonempty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：∀ {α : Type u} [inst : PseudoEMetricSpace α] {ε : ℝ} {s : Set α}, (Metric.
thickening ε s).Nonempty ↔ 0 < ε ∧ s.Nonempty
参数：Metric.thickening ε s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma thickening_nonempty_iff : (thickening ε s).Nonempty ↔ 0 < ε ∧ s.Nonempty := by
  simp [nonempty_iff_ne_empty]

open ENNReal
/-
**Metric._root_.Disjoint.exists_thickenings** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Disjoint.exists_thickenings (hst : Disjoint s t) (hs : IsCompact s)
    (ht : IsClosed t) :
    ∃ δ, 0 < δ ∧ Disjoint (thickening δ s) (thickening δ t) := by
  obtain ⟨r, hr, h⟩ := exists_pos_forall_lt_edist hs ht hst
  refine ⟨r / 2, half_pos (NNReal.coe_pos.2 hr), ?_⟩
  rw [disjoint_iff_inf_le]
  rintro z ⟨hzs, hzt⟩
  rw [mem_thickening_iff_exists_edist_lt] at hzs hzt
  rw [← NNReal.coe_two, ← NNReal.coe_div, ENNReal.ofReal_coe_nnreal] at hzs hzt
  obtain ⟨x, hx, hzx⟩ := hzs
  obtain ⟨y, hy, hzy⟩ := hzt
  refine (h x hx y hy).not_ge ?_
  calc
    edist x y ≤ edist z x + edist z y := edist_triangle_left _ _ _
    _ ≤ ↑(r / 2) + ↑(r / 2) := add_le_add hzx.le hzy.le
    _ = r := by rw [← ENNReal.coe_add, add_halves]
/-
**Metric._root_.Disjoint.exists_cthickenings** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Disjoint.exists_cthickenings (hst : Disjoint s t) (hs : IsCompact s)
    (ht : IsClosed t) :
    ∃ δ, 0 < δ ∧ Disjoint (cthickening δ s) (cthickening δ t) := by
  obtain ⟨δ, hδ, h⟩ := hst.exists_thickenings hs ht
  refine ⟨δ / 2, half_pos hδ, h.mono ?_ ?_⟩ <;>
    exact cthickening_subset_thickening' hδ (half_lt_self hδ) _

/-- If `s` is compact, `t` is open and `s ⊆ t`, some `cthickening` of `s` is contained in `t`. -/
/-
**Metric._root_.IsCompact.exists_cthickening_subset_open** 是 Mathlib 中的一个定理，位于命名
空间 `Metric`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `s` is compact, `t` is open and `s ⊆ t`, some `cthickening` of `s` is contain
ed in `t`.
-/
theorem _root_.IsCompact.exists_cthickening_subset_open (hs : IsCompact s) (ht : IsOpen t)
    (hst : s ⊆ t) :
    ∃ δ, 0 < δ ∧ cthickening δ s ⊆ t :=
  (hst.disjoint_compl_right.exists_cthickenings hs ht.isClosed_compl).imp fun _ h =>
    ⟨h.1, disjoint_compl_right_iff_subset.1 <| h.2.mono_right <| self_subset_cthickening _⟩
/-
**Metric._root_.IsCompact.exists_isCompact_cthickening** 是 Mathlib 中的一个定理，位于命名空间
 `Metric`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsCompact.exists_isCompact_cthickening [LocallyCompactSpace α] (hs : IsCompact s) :
    ∃ δ, 0 < δ ∧ IsCompact (cthickening δ s) := by
  rcases exists_compact_superset hs with ⟨K, K_compact, hK⟩
  rcases hs.exists_cthickening_subset_open isOpen_interior hK with ⟨δ, δpos, hδ⟩
  refine ⟨δ, δpos, ?_⟩
  exact K_compact.of_isClosed_subset isClosed_cthickening (hδ.trans interior_subset)
/-
**Metric._root_.IsCompact.exists_thickening_subset_open** 是 Mathlib 中的一个定理，位于命名空
间 `Metric`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsCompact.exists_thickening_subset_open (hs : IsCompact s) (ht : IsOpen t)
    (hst : s ⊆ t) : ∃ δ, 0 < δ ∧ thickening δ s ⊆ t :=
  let ⟨δ, h₀, hδ⟩ := hs.exists_cthickening_subset_open ht hst
  ⟨δ, h₀, (thickening_subset_cthickening _ _).trans hδ⟩
/-
**Metric.hasBasis_nhdsSet_thickening** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：hasBasis_nhdsSet_thickening {K : Set α} (hK : IsCompact K) : (𝓝ˢ K).HasBas
is (fun δ : Real => 0 < δ) fun δ => thickening δ K
参数：hK : IsCompact K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.to_hasBasis'`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort
 u_5} {l : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : ι' 
→ Set α},   l.HasB…
· 使用定理 `hasBasis_nhdsSet`：hasBasis_nhdsSet (s : Set X) : (𝓝ˢ s).HasBasis (fun U 
=> IsOpen U ∧ s subseteq U) fun U => U
· 使用定理 `IsCompact.exists_thickening_subset_open`：∀ {α : Type u} [inst : PseudoEM
etricSpace α] {s t : Set α},   IsCompact s → IsOpen t → s ⊆ t → ∃ δ, 0 < δ ∧ Met
ric.thickening δ s ⊆ t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Metric.thickening_mem_nhdsSet`：thickening_mem_nhdsSet (E : Set α) {δ : R
eal} (hδ : 0 < δ) : thickening δ E in 𝓝ˢ E
-/
theorem hasBasis_nhdsSet_thickening {K : Set α} (hK : IsCompact K) :
    (𝓝ˢ K).HasBasis (fun δ : ℝ => 0 < δ) fun δ => thickening δ K :=
  (hasBasis_nhdsSet K).to_hasBasis' (fun _U hU => hK.exists_thickening_subset_open hU.1 hU.2)
    fun _ => thickening_mem_nhdsSet K
/-
**Metric.hasBasis_nhdsSet_cthickening** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：hasBasis_nhdsSet_cthickening {K : Set α} (hK : IsCompact K) : (𝓝ˢ K).HasBa
sis (fun δ : Real => 0 < δ) fun δ => cthickening δ K
参数：hK : IsCompact K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.to_hasBasis'`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort
 u_5} {l : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : ι' 
→ Set α},   l.HasB…
· 使用定理 `hasBasis_nhdsSet`：hasBasis_nhdsSet (s : Set X) : (𝓝ˢ s).HasBasis (fun U 
=> IsOpen U ∧ s subseteq U) fun U => U
· 使用定理 `IsCompact.exists_cthickening_subset_open`：∀ {α : Type u} [inst : PseudoE
MetricSpace α] {s t : Set α},   IsCompact s → IsOpen t → s ⊆ t → ∃ δ, 0 < δ ∧ Me
tric.cthickening δ s ⊆ t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Metric.cthickening_mem_nhdsSet`：cthickening_mem_nhdsSet (E : Set α) {δ :
 Real} (hδ : 0 < δ) : cthickening δ E in 𝓝ˢ E
-/
theorem hasBasis_nhdsSet_cthickening {K : Set α} (hK : IsCompact K) :
    (𝓝ˢ K).HasBasis (fun δ : ℝ => 0 < δ) fun δ => cthickening δ K :=
  (hasBasis_nhdsSet K).to_hasBasis' (fun _U hU => hK.exists_cthickening_subset_open hU.1 hU.2)
    fun _ => cthickening_mem_nhdsSet K
/-
**Metric.cthickening_eq_iInter_cthickening'** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：cthickening_eq_iInter_cthickening' {δ : Real} (s : Set Real) (hsδ : s subs
eteq Ioi δ) (hs : forall ε, δ < ε -> (s inter Ioc δ ε).Nonempty) (E : Set α) : c
thickening δ E = ⋂ ε in s, cthickening ε E
参数：s : Set Real；hsδ : s subseteq Ioi δ；hs : forall ε, δ < ε -> (s inter Ioc δ ε)
.Nonempty；E : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Set.subset_iInter₂`：subset_iInter₂ {s : Set α} {t : forall i, κ i -> Set
 α} (h : forall i j, s subseteq t i j) : s subseteq ⋂ (i) (j), t i j
· 使用定理 `Metric.cthickening_mono`：cthickening_mono {δ₁ δ₂ : Real} (hle : δ₁ <= δ₂
) (E : Set α) : cthickening δ₁ E subseteq cthickening δ₂ E
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `ENNReal.le_of_forall_pos_le_add`：le_of_forall_pos_le_add (h : forall ε :
 Real>=0, 0 < ε -> b < ∞ -> a <= b + ε) : a <= b
· 使用定理 `lt_add_of_pos_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : 
LT α] [AddLeftStrictMono α] (a : α) {b : α}, 0 < b → a < a + b
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NNReal.coe_pos`：∀ {r : NNReal}, 0 < ↑r ↔ 0 < r
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `ENNReal.ofReal_le_ofReal`：ofReal_le_ofReal {p q : Real} (h : p <= q) : E
NNReal.ofReal p <= ENNReal.ofReal q
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.coe_nnreal_eq`：coe_nnreal_eq (r : Real>=0) : (r : Real>=0∞) = EN
NReal.ofReal r
· 使用定理 `ENNReal.ofReal_add_le`：ofReal_add_le {p q : Real} : ENNReal.ofReal (p + 
q) <= ENNReal.ofReal p + ENNReal.ofReal q
-/
theorem cthickening_eq_iInter_cthickening' {δ : ℝ} (s : Set ℝ) (hsδ : s ⊆ Ioi δ)
    (hs : ∀ ε, δ < ε → (s ∩ Ioc δ ε).Nonempty) (E : Set α) :
    cthickening δ E = ⋂ ε ∈ s, cthickening ε E := by
  apply Subset.antisymm
  · exact subset_iInter₂ fun _ hε => cthickening_mono (le_of_lt (hsδ hε)) E
  · unfold cthickening
    intro x hx
    simp only [mem_iInter, mem_ofPred_eq] at *
    apply ENNReal.le_of_forall_pos_le_add
    intro η η_pos _
    rcases hs (δ + η) (lt_add_of_pos_right _ (NNReal.coe_pos.mpr η_pos)) with ⟨ε, ⟨hsε, hε⟩⟩
    apply ((hx ε hsε).trans (ENNReal.ofReal_le_ofReal hε.2)).trans
    rw [ENNReal.coe_nnreal_eq η]
    exact ENNReal.ofReal_add_le
/-
**Metric.cthickening_eq_iInter_cthickening** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：cthickening_eq_iInter_cthickening {δ : Real} (E : Set α) : cthickening δ E
 = ⋂ (ε : Real) (_ : δ < ε), cthickening ε E
参数：E : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.cthickening_eq_iInter_cthickening'`：cthickening_eq_iInter_cthicke
ning' {δ : Real} (s : Set Real) (hsδ : s subseteq Ioi δ) (hs : forall ε, δ < ε -
> (s inter Ioc δ ε).Nonempty) (…
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.inter_eq_right`：∀ {α : Type u} {s t : Set α}, s ∩ t = t ↔ t ⊆ s
· 使用定理 `Set.Ioc_subset_Ioi_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc b a ⊆ Set.Ioi b
· 使用定理 `Set.nonempty_Ioc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, (Set.I
oc b a).Nonempty ↔ b < a
-/
theorem cthickening_eq_iInter_cthickening {δ : ℝ} (E : Set α) :
    cthickening δ E = ⋂ (ε : ℝ) (_ : δ < ε), cthickening ε E := by
  apply cthickening_eq_iInter_cthickening' (Ioi δ) rfl.subset
  simp_rw [inter_eq_right.mpr Ioc_subset_Ioi_self]
  exact fun _ hε => nonempty_Ioc.mpr hε
/-
**Metric.cthickening_eq_iInter_thickening'** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：cthickening_eq_iInter_thickening' {δ : Real} (δ_nn : 0 <= δ) (s : Set Real
) (hsδ : s subseteq Ioi δ) (hs : forall ε, δ < ε -> (s inter Ioc δ ε).Nonempty) 
(E : Set α) : cthickening δ E = ⋂ ε in s, thickening ε E
参数：δ_nn : 0 <= δ；s : Set Real；hsδ : s subseteq Ioi δ；hs : forall ε, δ < ε -> (s 
inter Ioc δ ε).Nonempty；E : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Set.subset_iInter₂`：subset_iInter₂ {s : Set α} {t : forall i, κ i -> Set
 α} (h : forall i j, s subseteq t i j) : s subseteq ⋂ (i) (j), t i j
· 使用定理 `Metric.cthickening_subset_thickening'`：cthickening_subset_thickening' {δ
₁ δ₂ : Real} (δ₂_pos : 0 < δ₂) (hlt : δ₁ < δ₂) (E : Set α) : cthickening δ₁ E su
bseteq thickening δ₂ E
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Metric.thickening_mono`：thickening_mono {δ₁ δ₂ : Real} (hle : δ₁ <= δ₂) 
(E : Set α) : thickening δ₁ E subseteq thickening δ₂ E
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.cthickening_eq_iInter_cthickening'`：cthickening_eq_iInter_cthicke
ning' {δ : Real} (s : Set Real) (hsδ : s subseteq Ioi δ) (hs : forall ε, δ < ε -
> (s inter Ioc δ ε).Nonempty) (…
· 使用定理 `Set.iInter₂_mono`：iInter₂_mono {s t : forall i, κ i -> Set α} (h : foral
l i j, s i j subseteq t i j) : ⋂ (i) (j), s i j subseteq ⋂ (i) (j), t i j
· 使用定理 `Metric.thickening_subset_cthickening`：thickening_subset_cthickening (δ :
 Real) (E : Set α) : thickening δ E subseteq cthickening δ E
-/
theorem cthickening_eq_iInter_thickening' {δ : ℝ} (δ_nn : 0 ≤ δ) (s : Set ℝ) (hsδ : s ⊆ Ioi δ)
    (hs : ∀ ε, δ < ε → (s ∩ Ioc δ ε).Nonempty) (E : Set α) :
    cthickening δ E = ⋂ ε ∈ s, thickening ε E := by
  refine (subset_iInter₂ fun ε hε => ?_).antisymm ?_
  · obtain ⟨ε', -, hε'⟩ := hs ε (hsδ hε)
    have ss := cthickening_subset_thickening' (lt_of_le_of_lt δ_nn hε'.1) hε'.1 E
    exact ss.trans (thickening_mono hε'.2 E)
  · rw [cthickening_eq_iInter_cthickening' s hsδ hs E]
    exact iInter₂_mono fun ε _ => thickening_subset_cthickening ε E
/-
**Metric.cthickening_eq_iInter_thickening** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：cthickening_eq_iInter_thickening {δ : Real} (δ_nn : 0 <= δ) (E : Set α) : 
cthickening δ E = ⋂ (ε : Real) (_ : δ < ε), thickening ε E
参数：δ_nn : 0 <= δ；E : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Metric.cthickening_eq_iInter_thickening'`：cthickening_eq_iInter_thickeni
ng' {δ : Real} (δ_nn : 0 <= δ) (s : Set Real) (hsδ : s subseteq Ioi δ) (hs : for
all ε, δ < ε -> (s inter Ioc δ…
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.inter_eq_right`：∀ {α : Type u} {s t : Set α}, s ∩ t = t ↔ t ⊆ s
· 使用定理 `Set.Ioc_subset_Ioi_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc b a ⊆ Set.Ioi b
· 使用定理 `Set.nonempty_Ioc`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, (Set.I
oc b a).Nonempty ↔ b < a
-/
theorem cthickening_eq_iInter_thickening {δ : ℝ} (δ_nn : 0 ≤ δ) (E : Set α) :
    cthickening δ E = ⋂ (ε : ℝ) (_ : δ < ε), thickening ε E := by
  apply cthickening_eq_iInter_thickening' δ_nn (Ioi δ) rfl.subset
  simp_rw [inter_eq_right.mpr Ioc_subset_Ioi_self]
  exact fun _ hε => nonempty_Ioc.mpr hε
/-
**Metric.cthickening_eq_iInter_thickening''** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：cthickening_eq_iInter_thickening'' (δ : Real) (E : Set α) : cthickening δ 
E = ⋂ (ε : Real) (_ : max 0 δ < ε), thickening ε E
参数：δ : Real；E : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Metric.cthickening_max_zero`：cthickening_max_zero (δ : Real) (E : Set α)
 : cthickening (max 0 δ) E = cthickening δ E
· 使用定理 `Metric.cthickening_eq_iInter_thickening`：cthickening_eq_iInter_thickenin
g {δ : Real} (δ_nn : 0 <= δ) (E : Set α) : cthickening δ E = ⋂ (ε : Real) (_ : δ
 < ε), thickening ε E
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
-/
theorem cthickening_eq_iInter_thickening'' (δ : ℝ) (E : Set α) :
    cthickening δ E = ⋂ (ε : ℝ) (_ : max 0 δ < ε), thickening ε E := by
  rw [← cthickening_max_zero, cthickening_eq_iInter_thickening]
  exact le_max_left _ _

/-- The closure of a set equals the intersection of its closed thickenings of positive radii
accumulating at zero. -/
/-
**Metric.closure_eq_iInter_cthickening'** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：closure_eq_iInter_cthickening' (E : Set α) (s : Set Real) (hs : forall ε, 
0 < ε -> (s inter Ioc 0 ε).Nonempty) : closure E = ⋂ δ in s, cthickening δ E
参数：E : Set α；s : Set Real；hs : forall ε, 0 < ε -> (s inter Ioc 0 ε).Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Metric.cthickening_zero`：cthickening_zero (E : Set α) : cthickening 0 E 
= closure E
· 使用定理 `Metric.cthickening_eq_iInter_cthickening'`：cthickening_eq_iInter_cthicke
ning' {δ : Real} (s : Set Real) (hsδ : s subseteq Ioi δ) (hs : forall ε, δ < ε -
> (s inter Ioc δ ε).Nonempty) (…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.not_subset`：not_subset : ¬s subseteq t ↔ exists a in s, a ∉ t
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Set.subset_iInter₂`：subset_iInter₂ {s : Set α} {t : forall i, κ i -> Set
 α} (h : forall i j, s subseteq t i j) : s subseteq ⋂ (i) (j), t i j
· 使用定理 `Metric.closure_subset_cthickening`：closure_subset_cthickening (δ : Real)
 (E : Set α) : closure E subseteq cthickening δ E
· 使用定理 `Metric.cthickening_of_nonpos`：cthickening_of_nonpos {δ : Real} (hδ : δ <
= 0) (E : Set α) : cthickening δ E = closure E
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Set.mem_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Ioi
 b ↔ b < x
· 使用定理 `Set.biInter_subset_of_mem`：biInter_subset_of_mem {s : Set α} {t : α -> S
et β} {x : α} (xs : x in s) : ⋂ x in s, t x subseteq t x

--- 原说明 ---
The closure of a set equals the intersection of its closed thickenings of positi
ve radii
accumulating at zero.
-/
theorem closure_eq_iInter_cthickening' (E : Set α) (s : Set ℝ)
    (hs : ∀ ε, 0 < ε → (s ∩ Ioc 0 ε).Nonempty) : closure E = ⋂ δ ∈ s, cthickening δ E := by
  by_cases hs₀ : s ⊆ Ioi 0
  · rw [← cthickening_zero]
    apply cthickening_eq_iInter_cthickening' _ hs₀ hs
  obtain ⟨δ, hδs, δ_nonpos⟩ := not_subset.mp hs₀
  rw [Set.mem_Ioi, not_lt] at δ_nonpos
  apply Subset.antisymm
  · exact subset_iInter₂ fun ε _ => closure_subset_cthickening ε E
  · rw [← cthickening_of_nonpos δ_nonpos E]
    exact biInter_subset_of_mem hδs

/-- The closure of a set equals the intersection of its closed thickenings of positive radii. -/
/-
**Metric.closure_eq_iInter_cthickening** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：closure_eq_iInter_cthickening (E : Set α) : closure E = ⋂ (δ : Real) (_ : 
0 < δ), cthickening δ E
参数：E : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Metric.cthickening_zero`：cthickening_zero (E : Set α) : cthickening 0 E 
= closure E
· 使用定理 `Metric.cthickening_eq_iInter_cthickening`：cthickening_eq_iInter_cthicken
ing {δ : Real} (E : Set α) : cthickening δ E = ⋂ (ε : Real) (_ : δ < ε), cthicke
ning ε E

--- 原说明 ---
The closure of a set equals the intersection of its closed thickenings of positi
ve radii.
-/
theorem closure_eq_iInter_cthickening (E : Set α) :
    closure E = ⋂ (δ : ℝ) (_ : 0 < δ), cthickening δ E := by
  rw [← cthickening_zero]
  exact cthickening_eq_iInter_cthickening E

/-- The closure of a set equals the intersection of its open thickenings of positive radii
accumulating at zero. -/
/-
**Metric.closure_eq_iInter_thickening'** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：closure_eq_iInter_thickening' (E : Set α) (s : Set Real) (hs₀ : s subseteq
 Ioi 0) (hs : forall ε, 0 < ε -> (s inter Ioc 0 ε).Nonempty) : closure E = ⋂ δ i
n s, thickening δ E
参数：E : Set α；s : Set Real；hs₀ : s subseteq Ioi 0；hs : forall ε, 0 < ε -> (s inte
r Ioc 0 ε).Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Metric.cthickening_zero`：cthickening_zero (E : Set α) : cthickening 0 E 
= closure E
· 使用定理 `Metric.cthickening_eq_iInter_thickening'`：cthickening_eq_iInter_thickeni
ng' {δ : Real} (δ_nn : 0 <= δ) (s : Set Real) (hsδ : s subseteq Ioi δ) (hs : for
all ε, δ < ε -> (s inter Ioc δ…
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
The closure of a set equals the intersection of its open thickenings of positive
 radii
accumulating at zero.
-/
theorem closure_eq_iInter_thickening' (E : Set α) (s : Set ℝ) (hs₀ : s ⊆ Ioi 0)
    (hs : ∀ ε, 0 < ε → (s ∩ Ioc 0 ε).Nonempty) : closure E = ⋂ δ ∈ s, thickening δ E := by
  rw [← cthickening_zero]
  apply cthickening_eq_iInter_thickening' le_rfl _ hs₀ hs

/-- The closure of a set equals the intersection of its (open) thickenings of positive radii. -/
/-
**Metric.closure_eq_iInter_thickening** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：closure_eq_iInter_thickening (E : Set α) : closure E = ⋂ (δ : Real) (_ : 0
 < δ), thickening δ E
参数：E : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Metric.cthickening_zero`：cthickening_zero (E : Set α) : cthickening 0 E 
= closure E
· 使用定理 `Metric.cthickening_eq_iInter_thickening`：cthickening_eq_iInter_thickenin
g {δ : Real} (δ_nn : 0 <= δ) (E : Set α) : cthickening δ E = ⋂ (ε : Real) (_ : δ
 < ε), thickening ε E
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a

--- 原说明 ---
The closure of a set equals the intersection of its (open) thickenings of positi
ve radii.
-/
theorem closure_eq_iInter_thickening (E : Set α) :
    closure E = ⋂ (δ : ℝ) (_ : 0 < δ), thickening δ E := by
  rw [← cthickening_zero]
  exact cthickening_eq_iInter_thickening rfl.ge E

/-- The frontier of the closed thickening of a set is contained in an `Metric.infEDist` level
set. -/
/-
**Metric.frontier_cthickening_subset** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：frontier_cthickening_subset (E : Set α) {δ : Real} : frontier (cthickening
 δ E) subseteq { x : α | infEDist x E = ENNReal.ofReal δ }
参数：E : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `frontier_le_subset_eq`：frontier_le_subset_eq (hf : Continuous f) (hg : C
ontinuous g) : frontier { b | f b <= g b } subseteq { b | f b = g b }
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `Metric.continuous_infEDist`：continuous_infEDist : Continuous fun x => in
fEDist x s
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)

--- 原说明 ---
The frontier of the closed thickening of a set is contained in an `Metric.infEDi
st` level
set.
-/
theorem frontier_cthickening_subset (E : Set α) {δ : ℝ} :
    frontier (cthickening δ E) ⊆ { x : α | infEDist x E = ENNReal.ofReal δ } :=
  frontier_le_subset_eq continuous_infEDist continuous_const

/-- The closed ball of radius `δ` centered at a point of `E` is included in the closed
thickening of `E`. -/
/-
**Metric.closedBall_subset_cthickening** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：closedBall_subset_cthickening {α : Type*} [PseudoMetricSpace α] {x : α} {E
 : Set α} (hx : x in E) (δ : Real) : closedBall x δ subseteq cthickening δ E
参数：hx : x in E；δ : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Metric.closedBall_subset_cthickening_singleton`：closedBall_subset_cthick
ening_singleton {α : Type*} [PseudoMetricSpace α] (x : α) (δ : Real) : closedBal
l x δ subseteq cthickening δ ({x} : …
· 使用定理 `Metric.cthickening_subset_of_subset`：cthickening_subset_of_subset (δ : R
eal) {E₁ E₂ : Set α} (h : E₁ subseteq E₂) : cthickening δ E₁ subseteq cthickenin
g δ E₂

--- 原说明 ---
The closed ball of radius `δ` centered at a point of `E` is included in the clos
ed
thickening of `E`.
-/
theorem closedBall_subset_cthickening {α : Type*} [PseudoMetricSpace α] {x : α} {E : Set α}
    (hx : x ∈ E) (δ : ℝ) : closedBall x δ ⊆ cthickening δ E := by
  refine (closedBall_subset_cthickening_singleton _ _).trans (cthickening_subset_of_subset _ ?_)
  simpa using hx
/-
**Metric.cthickening_subset_iUnion_closedBall_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `M
etric`。
形式化陈述：cthickening_subset_iUnion_closedBall_of_lt {α : Type*} [PseudoMetricSpace 
α] (E : Set α) {δ δ' : Real} (hδ₀ : 0 < δ') (hδδ' : δ < δ') : cthickening δ E su
bseteq ⋃ x in E, closedBall x δ'
参数：E : Set α；hδ₀ : 0 < δ'；hδδ' : δ < δ'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Metric.cthickening_subset_thickening'`：cthickening_subset_thickening' {δ
₁ δ₂ : Real} (δ₂_pos : 0 < δ₂) (hlt : δ₁ < δ₂) (E : Set α) : cthickening δ₁ E su
bseteq thickening δ₂ E
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.mem_thickening_iff`：mem_thickening_iff {E : Set X} {x : X} : x in
 thickening δ E ↔ exists z in E, dist x z < δ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_iUnion₂`：mem_iUnion₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋃ (i) (j), s i j) ↔ exists i j, x in s i j
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem cthickening_subset_iUnion_closedBall_of_lt {α : Type*} [PseudoMetricSpace α] (E : Set α)
    {δ δ' : ℝ} (hδ₀ : 0 < δ') (hδδ' : δ < δ') : cthickening δ E ⊆ ⋃ x ∈ E, closedBall x δ' := by
  refine (cthickening_subset_thickening' hδ₀ hδδ' E).trans fun x hx => ?_
  obtain ⟨y, hy₁, hy₂⟩ := mem_thickening_iff.mp hx
  exact mem_iUnion₂.mpr ⟨y, hy₁, hy₂.le⟩

/-- The closed thickening of a compact set `E` is the union of the balls `Metric.closedBall x δ`
over `x ∈ E`.

See also `Metric.cthickening_eq_biUnion_closedBall`. -/
/-
**Metric._root_.IsCompact.cthickening_eq_biUnion_closedBall** 是 Mathlib 中的一个定理，位
于命名空间 `Metric`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The closed thickening of a compact set `E` is the union of the balls `Metric.clo
sedBall x δ`
over `x ∈ E`.

See also `Metric.cthickening_eq_biUnion_closedBall`.
-/
theorem _root_.IsCompact.cthickening_eq_biUnion_closedBall {α : Type*} [PseudoMetricSpace α]
    {δ : ℝ} {E : Set α} (hE : IsCompact E) (hδ : 0 ≤ δ) :
    cthickening δ E = ⋃ x ∈ E, closedBall x δ := by
  rcases eq_empty_or_nonempty E with (rfl | hne)
  · simp only [cthickening_empty, biUnion_empty]
  refine Subset.antisymm (fun x hx ↦ ?_)
    (iUnion₂_subset fun x hx ↦ closedBall_subset_cthickening hx _)
  obtain ⟨y, yE, hy⟩ : ∃ y ∈ E, infEDist x E = edist x y := hE.exists_infEDist_eq_edist hne _
  have D1 : edist x y ≤ ENNReal.ofReal δ := (le_of_eq hy.symm).trans hx
  have D2 : dist x y ≤ δ := by
    rw [edist_dist] at D1
    exact (ENNReal.ofReal_le_ofReal_iff hδ).1 D1
  exact mem_biUnion yE D2
/-
**Metric.cthickening_eq_biUnion_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：cthickening_eq_biUnion_closedBall {α : Type*} [PseudoMetricSpace α] [Prope
rSpace α] (E : Set α) (hδ : 0 <= δ) : cthickening δ E = ⋃ x in closure E, closed
Ball x δ
参数：E : Set α；hδ : 0 <= δ。
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
· 使用定理 `Metric.cthickening_empty`：cthickening_empty (δ : Real) : cthickening δ (
∅ : Set α) = ∅
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `closure_empty`：closure_empty : closure (∅ : Set X) = ∅
· 使用定理 `Set.biUnion_empty`：biUnion_empty (s : α -> Set β) : ⋃ x in (∅ : Set α), 
s x = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Metric.cthickening_closure`：cthickening_closure : cthickening δ (closure
 s) = cthickening δ s
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `IsClosed.exists_infDist_eq_dist`：∀ {α : Type u} [inst : PseudoMetricSpac
e α] {s : Set α} [ProperSpace α],   IsClosed s → s.Nonempty → ∀ (x : α), ∃ y ∈ s
, Metric.infDist x s …
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `closure_nonempty_iff`：closure_nonempty_iff : (closure s).Nonempty ↔ s.No
nempty
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.ofReal_le_ofReal_iff`：ofReal_le_ofReal_iff {p q : Real} (h : 0 <
= q) : ENNReal.ofReal p <= ENNReal.ofReal q ↔ p <= q
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `ENNReal.ofReal_toReal_le`：ofReal_toReal_le {a : Real>=0∞} : ENNReal.ofRe
al a.toReal <= a
· 使用定理 `Set.mem_biUnion`：mem_biUnion {s : Set α} {t : α -> Set β} {x : α} {y : β
} (xs : x in s) (ytx : y in t x) : y in ⋃ x in s, t x
· 使用定理 `Set.iUnion₂_subset`：iUnion₂_subset {s : forall i, κ i -> Set α} {t : Set
 α} (h : forall i j, s i j subseteq t) : ⋃ (i) (j), s i j subseteq t
· 使用定理 `Metric.closedBall_subset_cthickening`：closedBall_subset_cthickening {α :
 Type*} [PseudoMetricSpace α] {x : α} {E : Set α} (hx : x in E) (δ : Real) : clo
sedBall x δ subseteq cthic…
-/
theorem cthickening_eq_biUnion_closedBall {α : Type*} [PseudoMetricSpace α] [ProperSpace α]
    (E : Set α) (hδ : 0 ≤ δ) : cthickening δ E = ⋃ x ∈ closure E, closedBall x δ := by
  rcases eq_empty_or_nonempty E with (rfl | hne)
  · simp only [cthickening_empty, biUnion_empty, closure_empty]
  rw [← cthickening_closure]
  refine Subset.antisymm (fun x hx ↦ ?_)
    (iUnion₂_subset fun x hx ↦ closedBall_subset_cthickening hx _)
  obtain ⟨y, yE, hy⟩ : ∃ y ∈ closure E, infDist x (closure E) = dist x y :=
    isClosed_closure.exists_infDist_eq_dist (closure_nonempty_iff.mpr hne) x
  replace hy : dist x y ≤ δ :=
    (ENNReal.ofReal_le_ofReal_iff hδ).mp
      (((congr_arg ENNReal.ofReal hy.symm).le.trans ENNReal.ofReal_toReal_le).trans hx)
  exact mem_biUnion yE hy

nonrec theorem _root_.IsClosed.cthickening_eq_biUnion_closedBall {α : Type*} [PseudoMetricSpace α]
    [ProperSpace α] {E : Set α} (hE : IsClosed E) (hδ : 0 ≤ δ) :
    cthickening δ E = ⋃ x ∈ E, closedBall x δ := by
  rw [cthickening_eq_biUnion_closedBall E hδ, hE.closure_eq]

/-- For the equality, see `infEDist_cthickening`. -/
/-
**Metric.infEDist_le_infEDist_cthickening_add** 是 Mathlib 中的一个定理，位于命名空间 `Metric`
。
形式化陈述：infEDist_le_infEDist_cthickening_add : infEDist x s <= infEDist x (cthicke
ning δ s) + ENNReal.ofReal δ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_forall_gt`：∀ {α : Type u_2} [inst : LinearOrder α] {a b : α}, (∀ (
c : α), a < c → b < c) → b ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Metric.infEDist_le_edist_add_infEDist`：infEDist_le_edist_add_infEDist : 
infEDist x s <= edist x y + infEDist y s
· 使用定理 `LT.lt.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a < b → b = 
c → a < c
· 使用定理 `ENNReal.add_lt_add_of_lt_of_le`：∀ {a b c d : ENNReal}, c ≠ ⊤ → a < b → c
 ≤ d → a + c < b + d
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `ENNReal.ofReal_lt_top`：∀ {r : ℝ}, ENNReal.ofReal r < ⊤
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_self_add`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ a + b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `lt_tsub_iff_left`：lt_tsub_iff_left : a < b - c ↔ c + a < b

--- 原说明 ---
For the equality, see `infEDist_cthickening`.
-/
theorem infEDist_le_infEDist_cthickening_add :
    infEDist x s ≤ infEDist x (cthickening δ s) + ENNReal.ofReal δ := by
  refine le_of_forall_gt fun r h => ?_
  simp_rw [← lt_tsub_iff_right, infEDist_lt_iff, mem_cthickening_iff] at h
  obtain ⟨y, hy, hxy⟩ := h
  exact infEDist_le_edist_add_infEDist.trans_lt
    ((ENNReal.add_lt_add_of_lt_of_le (hy.trans_lt ENNReal.ofReal_lt_top).ne hxy hy).trans_eq
      (tsub_add_cancel_of_le <| le_self_add.trans (lt_tsub_iff_left.1 hxy).le))

@[deprecated (since := "2026-01-08")]
alias infEdist_le_infEdist_cthickening_add := infEDist_le_infEDist_cthickening_add

/-- For the equality, see `infEDist_thickening`. -/
/-
**Metric.infEDist_le_infEDist_thickening_add** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：infEDist_le_infEDist_thickening_add : infEDist x s <= infEDist x (thickeni
ng δ s) + ENNReal.ofReal δ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Metric.infEDist_le_infEDist_cthickening_add`：infEDist_le_infEDist_cthick
ening_add : infEDist x s <= infEDist x (cthickening δ s) + ENNReal.ofReal δ
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Metric.infEDist_anti`：infEDist_anti (h : s subseteq t) : infEDist x t <=
 infEDist x s
· 使用定理 `Metric.thickening_subset_cthickening`：thickening_subset_cthickening (δ :
 Real) (E : Set α) : thickening δ E subseteq cthickening δ E
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
For the equality, see `infEDist_thickening`.
-/
theorem infEDist_le_infEDist_thickening_add :
    infEDist x s ≤ infEDist x (thickening δ s) + ENNReal.ofReal δ :=
  infEDist_le_infEDist_cthickening_add.trans <| by gcongr; exact thickening_subset_cthickening ..

@[deprecated (since := "2026-01-08")]
alias infEdist_le_infEdist_thickening_add := infEDist_le_infEDist_thickening_add

/-- For the equality, see `thickening_thickening`. -/
@[simp]
/-
**Metric.thickening_thickening_subset** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：thickening_thickening_subset (ε δ : Real) (s : Set α) : thickening ε (thic
kening δ s) subseteq thickening (ε + δ) s
参数：ε δ : Real；s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.thickening_of_nonpos`：thickening_of_nonpos (hδ : δ <= 0) (s : Set
 α) : thickening δ s = ∅
· 使用定理 `Metric.thickening_empty`：thickening_empty (δ : Real) : thickening δ (∅ :
 Set α) = ∅
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ENNReal.ofReal_add`：ofReal_add {p q : Real} (hp : 0 <= p) (hq : 0 <= q) 
: ENNReal.ofReal (p + q) = ENNReal.ofReal p + ENNReal.ofReal q
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `PseudoEMetricSpace.edist_triangle`：∀ {α : Type u} [self : PseudoEMetricS
pace α] (x y z : α), edist x z ≤ edist x y + edist y z
· 使用定理 `ENNReal.add_lt_add`：∀ {a b c d : ENNReal}, a < c → b < d → a + b < c + d

--- 原说明 ---
For the equality, see `thickening_thickening`.
-/
theorem thickening_thickening_subset (ε δ : ℝ) (s : Set α) :
    thickening ε (thickening δ s) ⊆ thickening (ε + δ) s := by
  obtain hε | hε := le_total ε 0
  · simp only [thickening_of_nonpos hε, empty_subset]
  obtain hδ | hδ := le_total δ 0
  · simp only [thickening_of_nonpos hδ, thickening_empty, empty_subset]
  intro x
  simp_rw [mem_thickening_iff_exists_edist_lt, ENNReal.ofReal_add hε hδ]
  exact fun ⟨y, ⟨z, hz, hy⟩, hx⟩ =>
    ⟨z, hz, (edist_triangle _ _ _).trans_lt <| ENNReal.add_lt_add hx hy⟩

/-- For the equality, see `thickening_cthickening`. -/
@[simp]
/-
**Metric.thickening_cthickening_subset** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：thickening_cthickening_subset (ε : Real) (hδ : 0 <= δ) (s : Set α) : thick
ening ε (cthickening δ s) subseteq thickening (ε + δ) s
参数：ε : Real；hδ : 0 <= δ；s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.thickening_of_nonpos`：thickening_of_nonpos (hδ : δ <= 0) (s : Set
 α) : thickening δ s = ∅
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ENNReal.ofReal_add`：ofReal_add {p q : Real} (hp : 0 <= p) (hq : 0 <= q) 
: ENNReal.ofReal (p + q) = ENNReal.ofReal p + ENNReal.ofReal q
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Metric.infEDist_le_edist_add_infEDist`：infEDist_le_edist_add_infEDist : 
infEDist x s <= edist x y + infEDist y s
· 使用定理 `ENNReal.add_lt_add_of_lt_of_le`：∀ {a b c d : ENNReal}, c ≠ ⊤ → a < b → c
 ≤ d → a + c < b + d
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `ENNReal.ofReal_lt_top`：∀ {r : ℝ}, ENNReal.ofReal r < ⊤

--- 原说明 ---
For the equality, see `thickening_cthickening`.
-/
theorem thickening_cthickening_subset (ε : ℝ) (hδ : 0 ≤ δ) (s : Set α) :
    thickening ε (cthickening δ s) ⊆ thickening (ε + δ) s := by
  obtain hε | hε := le_total ε 0
  · simp only [thickening_of_nonpos hε, empty_subset]
  intro x
  simp_rw [mem_thickening_iff_exists_edist_lt, mem_cthickening_iff, ← infEDist_lt_iff,
    ENNReal.ofReal_add hε hδ]
  rintro ⟨y, hy, hxy⟩
  exact infEDist_le_edist_add_infEDist.trans_lt
    (ENNReal.add_lt_add_of_lt_of_le (hy.trans_lt ENNReal.ofReal_lt_top).ne hxy hy)

/-- For the equality, see `cthickening_thickening`. -/
@[simp]
/-
**Metric.cthickening_thickening_subset** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：cthickening_thickening_subset (hε : 0 <= ε) (δ : Real) (s : Set α) : cthic
kening ε (thickening δ s) subseteq cthickening (ε + δ) s
参数：hε : 0 <= ε；δ : Real；s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.thickening_of_nonpos`：thickening_of_nonpos (hδ : δ <= 0) (s : Set
 α) : thickening δ s = ∅
· 使用定理 `Metric.cthickening_empty`：cthickening_empty (δ : Real) : cthickening δ (
∅ : Set α) = ∅
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `ENNReal.ofReal_add`：ofReal_add {p q : Real} (hp : 0 <= p) (hq : 0 <= q) 
: ENNReal.ofReal (p + q) = ENNReal.ofReal p + ENNReal.ofReal q
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Metric.infEDist_le_infEDist_thickening_add`：infEDist_le_infEDist_thicken
ing_add : infEDist x s <= infEDist x (thickening δ s) + ENNReal.ofReal δ
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
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
For the equality, see `cthickening_thickening`.
-/
theorem cthickening_thickening_subset (hε : 0 ≤ ε) (δ : ℝ) (s : Set α) :
    cthickening ε (thickening δ s) ⊆ cthickening (ε + δ) s := by
  obtain hδ | hδ := le_total δ 0
  · simp only [thickening_of_nonpos hδ, cthickening_empty, empty_subset]
  intro x
  simp_rw [mem_cthickening_iff, ENNReal.ofReal_add hε hδ]
  exact fun hx => infEDist_le_infEDist_thickening_add.trans (by grw [hx])

/-- For the equality, see `cthickening_cthickening`. -/
@[simp]
/-
**Metric.cthickening_cthickening_subset** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：cthickening_cthickening_subset (hε : 0 <= ε) (hδ : 0 <= δ) (s : Set α) : c
thickening ε (cthickening δ s) subseteq cthickening (ε + δ) s
参数：hε : 0 <= ε；hδ : 0 <= δ；s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.ofReal_add`：ofReal_add {p q : Real} (hp : 0 <= p) (hq : 0 <= q) 
: ENNReal.ofReal (p + q) = ENNReal.ofReal p + ENNReal.ofReal q
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Metric.infEDist_le_infEDist_cthickening_add`：infEDist_le_infEDist_cthick
ening_add : infEDist x s <= infEDist x (cthickening δ s) + ENNReal.ofReal δ
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
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
For the equality, see `cthickening_cthickening`.
-/
theorem cthickening_cthickening_subset (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (s : Set α) :
    cthickening ε (cthickening δ s) ⊆ cthickening (ε + δ) s := by
  intro x
  simp_rw [mem_cthickening_iff, ENNReal.ofReal_add hε hδ]
  exact fun hx => infEDist_le_infEDist_cthickening_add.trans (by grw [hx])

open scoped Function in -- required for scoped `on` notation
/-
**Metric.frontier_cthickening_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：frontier_cthickening_disjoint (A : Set α) : Pairwise (Disjoint on fun r : 
Real>=0 => frontier (cthickening r A))
参数：A : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.mono`：Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.s
upport <= f.support) (hg : y.support <= g.support) : Disjoint x y
· 使用定理 `Metric.frontier_cthickening_subset`：frontier_cthickening_subset (E : Set
 α) {δ : Real} : frontier (cthickening δ E) subseteq { x : α | infEDist x E = EN
NReal.ofReal δ }
· 使用定理 `Disjoint.preimage`：Disjoint.preimage (f : α -> β) {s t : Set β} (h : Dis
joint s t) : Disjoint (f ⁻¹' s) (f ⁻¹' t)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.disjoint_singleton`：disjoint_singleton : Disjoint ({a} : Set α) {b} 
↔ a != b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.ofReal_coe_nnreal`：∀ {p : NNReal}, ENNReal.ofReal ↑p = ↑p
-/
theorem frontier_cthickening_disjoint (A : Set α) :
    Pairwise (Disjoint on fun r : ℝ≥0 => frontier (cthickening r A)) := fun r₁ r₂ hr =>
  ((disjoint_singleton.2 <| by simpa).preimage _).mono (frontier_cthickening_subset _)
    (frontier_cthickening_subset _)

end Cthickening

section PseudoMetricSpace

variable {α β E : Type*} [PseudoMetricSpace α] {l : Filter β} {s : Set α}

/-
**Metric.thickening_ball** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：thickening_ball (x : α) (ε δ : Real) : thickening ε (ball x δ) subseteq ba
ll x (ε + δ)
参数：x : α；ε δ : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Metric.thickening_singleton`：thickening_singleton (δ : Real) (x : X) : t
hickening δ ({x} : Set X) = ball x δ
· 使用定理 `Metric.thickening_thickening_subset`：thickening_thickening_subset (ε δ :
 Real) (s : Set α) : thickening ε (thickening δ s) subseteq thickening (ε + δ) s
-/
theorem thickening_ball (x : α) (ε δ : ℝ) :
    thickening ε (ball x δ) ⊆ ball x (ε + δ) := by
  rw [← thickening_singleton, ← thickening_singleton]
  apply thickening_thickening_subset
/-
**Metric.tendsto_nhdsSet** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：tendsto_nhdsSet {f : β -> α} (hs₁ : IsCompact s) (hs₂ : Set.Nonempty s) : 
Tendsto f l (𝓝ˢ s) ↔ forall ε > 0, forallᶠ x in l, infDist (f x) s < ε
参数：hs₁ : IsCompact s；hs₂ : Set.Nonempty s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用定理 `Metric.hasBasis_nhdsSet_thickening`：hasBasis_nhdsSet_thickening {K : Set
 α} (hK : IsCompact K) : (𝓝ˢ K).HasBasis (fun δ : Real => 0 < δ) fun δ => thicke
ning δ K
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Metric.mem_thickening_iff_infDist_lt`：mem_thickening_iff_infDist_lt {E :
 Set X} {x : X} (h : E.Nonempty) : x in thickening δ E ↔ infDist x E < δ
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem tendsto_nhdsSet {f : β → α} (hs₁ : IsCompact s) (hs₂ : Set.Nonempty s) :
    Tendsto f l (𝓝ˢ s) ↔ ∀ ε > 0, ∀ᶠ x in l, infDist (f x) s < ε := by
  rw [(hasBasis_nhdsSet_thickening hs₁).tendsto_right_iff]
  congrm (∀ ε hε, ?_)
  simp [mem_thickening_iff_infDist_lt hs₂]
/-
**Metric.mem_nhdsSet_iff** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：mem_nhdsSet_iff {t : Set α} (hs : IsCompact s) : t in 𝓝ˢ s ↔ exists ε > 0,
 Metric.thickening ε s subseteq t
参数：hs : IsCompact s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Metric.hasBasis_nhdsSet_thickening`：hasBasis_nhdsSet_thickening {K : Set
 α} (hK : IsCompact K) : (𝓝ˢ K).HasBasis (fun δ : Real => 0 < δ) fun δ => thicke
ning δ K
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_nhdsSet_iff {t : Set α} (hs : IsCompact s) :
    t ∈ 𝓝ˢ s ↔ ∃ ε > 0, Metric.thickening ε s ⊆ t := by
  rw [(hasBasis_nhdsSet_thickening hs).mem_iff]

end PseudoMetricSpace

end Metric

section Clopen

open Metric

variable [PseudoEMetricSpace α] {s : Set α}

/-
**IsClopen.of_thickening_subset_self** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsClopen.of_thickening_subset_self {δ : Real} (hδ : 0 < δ) (hs : thickenin
g δ s subseteq s) : IsClopen s
参数：hδ : 0 < δ；hs : thickening δ s subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Metric.self_subset_thickening`：self_subset_thickening {δ : Real} (δ_pos 
: 0 < δ) (E : Set α) : E subseteq thickening δ E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `closure_subset_iff_isClosed`：closure_subset_iff_isClosed : closure s sub
seteq s ↔ IsClosed s
· 使用定理 `Metric.closure_eq_iInter_thickening`：closure_eq_iInter_thickening (E : S
et α) : closure E = ⋂ (δ : Real) (_ : 0 < δ), thickening δ E
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Set.iInter₂_subset`：iInter₂_subset {s : forall i, κ i -> Set α} (i : ι) 
(j : κ i) : ⋂ (i) (j), s i j subseteq s i j
· 使用定理 `Metric.isOpen_thickening`：isOpen_thickening {δ : Real} {E : Set α} : IsO
pen (thickening δ E)
-/
lemma IsClopen.of_thickening_subset_self {δ : ℝ} (hδ : 0 < δ) (hs : thickening δ s ⊆ s) :
    IsClopen s := by
  replace hs : thickening δ s = s := le_antisymm hs (self_subset_thickening hδ s)
  refine ⟨?_, hs ▸ isOpen_thickening⟩
  rw [← closure_subset_iff_isClosed, closure_eq_iInter_thickening]
  exact Set.iInter₂_subset δ hδ |>.trans_eq hs
/-
**IsClopen.of_cthickening_subset_self** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsClopen.of_cthickening_subset_self {δ : Real} (hδ : 0 < δ) (hs : cthicken
ing δ s subseteq s) : IsClopen s
参数：hδ : 0 < δ；hs : cthickening δ s subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsClopen.of_thickening_subset_self`：IsClopen.of_thickening_subset_self {
δ : Real} (hδ : 0 < δ) (hs : thickening δ s subseteq s) : IsClopen s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Metric.thickening_subset_cthickening`：thickening_subset_cthickening (δ :
 Real) (E : Set α) : thickening δ E subseteq cthickening δ E
-/
lemma IsClopen.of_cthickening_subset_self {δ : ℝ} (hδ : 0 < δ) (hs : cthickening δ s ⊆ s) :
    IsClopen s :=
  .of_thickening_subset_self hδ <| (thickening_subset_cthickening δ s).trans hs

end Clopen

open Metric in
/-
**IsCompact.exists_thickening_image_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.exists_thickening_image_subset [PseudoEMetricSpace α] {β : Type*
} [PseudoEMetricSpace β] {f : α -> β} {K : Set α} {U : Set β} (hK : IsCompact K)
 (ho : IsOpen U) (hf : forall x in K, ContinuousAt f x) (hKU : MapsTo f K U) : e
xists ε > 0, exists V in 𝓝ˢ K, thickening ε (f '' V) subseteq U
参数：hK : IsCompact K；ho : IsOpen U；hf : forall x in K, ContinuousAt f x；hKU : Map
sTo f K U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.induction_on`：IsCompact.induction_on (hs : IsCompact s) {p : S
et X -> Prop} (he : p ∅) (hmono : forall ⦃s t⦄, s subseteq t -> p t -> p s) (hun
ion : forall…
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsSet_empty`：nhdsSet_empty : 𝓝ˢ (∅ : Set X) = ⊥
· 使用定理 `Set.image_empty`：image_empty (f : α -> β) : f '' ∅ = ∅
· 使用定理 `Metric.thickening_empty`：thickening_empty (δ : Real) : thickening δ (∅ :
 Set α) = ∅
· 使用定理 `nhdsSet_mono`：nhdsSet_mono (h : s subseteq t) : 𝓝ˢ s <= 𝓝ˢ t
· 使用引理 `lt_min`：lt_min (h₁ : a < b) (h₂ : a < c) : a < min b c
· 使用定理 `union_mem_nhdsSet`：union_mem_nhdsSet (h₁ : s₁ in 𝓝ˢ t₁) (h₂ : s₂ in 𝓝ˢ t
₂) : s₁ union s₂ in 𝓝ˢ (t₁ union t₂)
· 使用定理 `Set.image_union`：image_union (f : α -> β) (s t : Set α) : f '' (s union 
t) = f '' s union f '' t
· 使用定理 `Metric.thickening_union`：thickening_union (δ : Real) (s t : Set α) : thi
ckening δ (s union t) = thickening δ s union thickening δ t
· 使用定理 `Set.union_subset_union`：union_subset_union {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq s₂) (h₂ : t₁ subseteq t₂) : s₁ union t₁ subseteq s₂ union t₂
· 使用定理 `Metric.thickening_mono`：thickening_mono {δ₁ δ₂ : Real} (hle : δ₁ <= δ₂) 
(E : Set α) : thickening δ₁ E subseteq thickening δ₂ E
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Set.union_self`：union_self (a : Set α) : a union a = a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `IsCompact.exists_thickening_subset_open`：∀ {α : Type u} [inst : PseudoEM
etricSpace α] {s t : Set α},   IsCompact s → IsOpen t → s ⊆ t → ∃ δ, 0 < δ ∧ Met
ric.thickening δ s ⊆ t
· 使用定理 `isCompact_singleton`：isCompact_singleton {x : X} : IsCompact ({x} : Set 
X)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Metric.isOpen_thickening`：isOpen_thickening {δ : Real} {E : Set α} : IsO
pen (thickening δ E)
· 使用定理 `Metric.self_subset_thickening`：self_subset_thickening {δ : Real} (δ_pos 
: 0 < δ) (E : Set α) : E subseteq thickening δ E
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
（共 43 条，此处仅展示前 30 条）
-/
theorem IsCompact.exists_thickening_image_subset
    [PseudoEMetricSpace α] {β : Type*} [PseudoEMetricSpace β]
    {f : α → β} {K : Set α} {U : Set β} (hK : IsCompact K) (ho : IsOpen U)
    (hf : ∀ x ∈ K, ContinuousAt f x) (hKU : MapsTo f K U) :
    ∃ ε > 0, ∃ V ∈ 𝓝ˢ K, thickening ε (f '' V) ⊆ U := by
  apply hK.induction_on (p := fun K ↦ ∃ ε > 0, ∃ V ∈ 𝓝ˢ K, thickening ε (f '' V) ⊆ U)
  · use 1, by positivity, ∅, by simp, by simp
  · exact fun s t hst ⟨ε, hε, V, hV, hthickening⟩ ↦ ⟨ε, hε, V, nhdsSet_mono hst hV, hthickening⟩
  · rintro s t ⟨ε₁, hε₁, V₁, hV₁, hV₁thickening⟩ ⟨ε₂, hε₂, V₂, hV₂, hV₂thickening⟩
    refine ⟨min ε₁ ε₂, by positivity, V₁ ∪ V₂, union_mem_nhdsSet hV₁ hV₂, ?_⟩
    rw [image_union, thickening_union]
    calc thickening (ε₁ ⊓ ε₂) (f '' V₁) ∪ thickening (ε₁ ⊓ ε₂) (f '' V₂)
      _ ⊆ thickening ε₁ (f '' V₁) ∪ thickening ε₂ (f '' V₂) := by gcongr <;> norm_num
      _ ⊆ U ∪ U := by gcongr
      _ = U := union_self _
  · intro x hx
    have : {f x} ⊆ U := by rw [singleton_subset_iff]; exact hKU hx
    obtain ⟨δ, hδ, hthick⟩ := (isCompact_singleton (x := f x)).exists_thickening_subset_open ho this
    let V := f ⁻¹' (thickening (δ / 2) {f x})
    have : V ∈ 𝓝 x := by
      apply hf x hx
      apply isOpen_thickening.mem_nhds
      exact (self_subset_thickening (by positivity) _) rfl
    refine ⟨K ∩ (interior V), inter_mem_nhdsWithin K (interior_mem_nhds.mpr this),
      δ / 2, by positivity, V, by rw [← subset_interior_iff_mem_nhdsSet]; simp, ?_⟩
    calc thickening (δ / 2) (f '' V)
      _ ⊆ thickening (δ / 2) (thickening (δ / 2) {f x}) :=
        thickening_subset_of_subset _ (image_preimage_subset f _)
      _ ⊆ thickening ((δ / 2) + (δ / 2)) ({f x}) :=
        thickening_thickening_subset (δ / 2) (δ / 2) {f x}
      _ ⊆ U := by simp [hthick]
