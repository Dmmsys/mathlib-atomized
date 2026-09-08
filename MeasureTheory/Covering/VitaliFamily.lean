/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous

/-!
# Vitali families

On a metric space `X` with a measure `μ`, consider for each `x : X` a family of measurable sets with
nonempty interiors, called `setsAt x`. This family is a Vitali family if it satisfies the following
property: consider a (possibly non-measurable) set `s`, and for any `x` in `s` a
subfamily `f x` of `setsAt x` containing sets of arbitrarily small diameter. Then one can extract
a disjoint subfamily covering almost all `s`.

Vitali families are provided by covering theorems such as the Besicovitch covering theorem or the
Vitali covering theorem. They make it possible to formulate general versions of theorems on
differentiations of measure that apply in both contexts.

This file gives the basic definition of Vitali families. More interesting developments of this
notion are deferred to other files:
* constructions of specific Vitali families are provided by the Besicovitch covering theorem, in
  `Besicovitch.vitaliFamily`, and by the Vitali covering theorem, in `Vitali.vitaliFamily`.
* The main theorem on differentiation of measures along a Vitali family is proved in
  `VitaliFamily.ae_tendsto_rnDeriv`.

## Main definitions

* `VitaliFamily μ` is a structure made, for each `x : X`, of a family of sets around `x`, such that
  one can extract an almost everywhere disjoint covering from any subfamily containing sets of
  arbitrarily small diameters.

Let `v` be such a Vitali family.
* `v.FineSubfamilyOn` describes the subfamilies of `v` from which one can extract almost
  everywhere disjoint coverings. This property, called
  `v.FineSubfamilyOn.exists_disjoint_covering_ae`, is essentially a restatement of the definition
  of a Vitali family. We also provide an API to use efficiently such a disjoint covering.
* `v.filterAt x` is a filter on sets of `X`, such that convergence with respect to this filter
  means convergence when sets in the Vitali family shrink towards `x`.

## References

* [Herbert Federer, Geometric Measure Theory, Chapter 2.8][Federer1996]
  (Vitali families are called Vitali relations there)
-/

@[expose] public section


open MeasureTheory Metric Set Filter TopologicalSpace MeasureTheory.Measure
open scoped Topology

variable {X : Type*} [PseudoMetricSpace X]

/-- On a metric space `X` with a measure `μ`, consider for each `x : X` a family of measurable sets
with nonempty interiors, called `setsAt x`. This family is a Vitali family if it satisfies the
following property: consider a (possibly non-measurable) set `s`, and for any `x` in `s` a
subfamily `f x` of `setsAt x` containing sets of arbitrarily small diameter. Then one can extract
a disjoint subfamily covering almost all `s`.

Vitali families are provided by covering theorems such as the Besicovitch covering theorem or the
Vitali covering theorem. They make it possible to formulate general versions of theorems on
differentiations of measure that apply in both contexts.
-/
/-
**VitaliFamily** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{X : Type u_1} → [PseudoMetricSpace X] → {m : MeasurableSpace X} → Measure
Theory.Measure X → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
On a metric space `X` with a measure `μ`, consider for each `x : X` a family of 
measurable sets
with nonempty interiors, called `setsAt x`. This family is a Vitali family if it
 satisfies the
following property: consider a (possibly non-measurable) set `s`, and for any `x
` in `s` a
subfamily `f x` of `setsAt x` containing sets of arbitrarily small diameter. The
n one can extract
a disjoint subfamily covering almost all `s`.

Vitali families are provided by covering theorems such as the Besicovitch coveri
ng theorem or the
Vitali covering theorem. They make it possible to formulate general versions of 
theorems on
differentiations of measure that apply in both contexts.
-/
structure VitaliFamily {m : MeasurableSpace X} (μ : Measure X) where
  /-- Sets of the family "centered" at a given point. -/
  setsAt : X → Set (Set X)
  /-- All sets of the family are measurable. -/
  measurableSet : ∀ x : X, ∀ s ∈ setsAt x, MeasurableSet s
  /-- All sets of the family have nonempty interior. -/
  nonempty_interior : ∀ x : X, ∀ s ∈ setsAt x, (interior s).Nonempty
  /-- For any closed ball around `x`, there exists a set of the family contained in this ball. -/
  nontrivial : ∀ (x : X), ∀ ε > (0 : ℝ), ∃ s ∈ setsAt x, s ⊆ closedBall x ε
  /-- Consider a (possibly non-measurable) set `s`,
  and for any `x` in `s` a subfamily `f x` of `setsAt x`
  containing sets of arbitrarily small diameter.
  Then one can extract a disjoint subfamily covering almost all `s`. -/
  covering : ∀ (s : Set X) (f : X → Set (Set X)),
    (∀ x ∈ s, f x ⊆ setsAt x) → (∀ x ∈ s, ∀ ε > (0 : ℝ), ∃ t ∈ f x, t ⊆ closedBall x ε) →
    ∃ t : Set (X × Set X), (∀ p ∈ t, p.1 ∈ s) ∧ (t.PairwiseDisjoint fun p ↦ p.2) ∧
      (∀ p ∈ t, p.2 ∈ f p.1) ∧ μ (s \ ⋃ p ∈ t, p.2) = 0

namespace VitaliFamily

variable {m0 : MeasurableSpace X} {μ : Measure X}

/-- A Vitali family for a measure `μ` is also a Vitali family for any measure absolutely continuous
with respect to `μ`. -/
/-
**VitaliFamily.mono** 是 Mathlib 中的一个定义，位于命名空间 `VitaliFamily`。
形式化陈述：mono (v : VitaliFamily μ) (ν : Measure X) (hν : ν ≪ μ) : VitaliFamily ν wh
ere __
参数：v : VitaliFamily μ；ν : Measure X；hν : ν ≪ μ。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `VitaliFamily.measurableSet`：∀ {X : Type u_1} [inst : PseudoMetricSpace X
] {m : MeasurableSpace X} {μ : MeasureTheory.Measure X}   (self : VitaliFamily μ
) (x : X), ∀ s ∈…
· 使用定理 `VitaliFamily.nonempty_interior`：∀ {X : Type u_1} [inst : PseudoMetricSpa
ce X] {m : MeasurableSpace X} {μ : MeasureTheory.Measure X}   (self : VitaliFami
ly μ) (x : X), ∀ s ∈…
· 使用定理 `VitaliFamily.nontrivial`：∀ {X : Type u_1} [inst : PseudoMetricSpace X] {
m : MeasurableSpace X} {μ : MeasureTheory.Measure X}   (self : VitaliFamily μ) (
x : X), ∀ ε >…

--- 原说明 ---
A Vitali family for a measure `μ` is also a Vitali family for any measure absolu
tely continuous
with respect to `μ`.
-/
def mono (v : VitaliFamily μ) (ν : Measure X) (hν : ν ≪ μ) : VitaliFamily ν where
  __ := v
  covering s f h h' :=
    let ⟨t, ts, disj, mem_f, hμ⟩ := v.covering s f h h'
    ⟨t, ts, disj, mem_f, hν hμ⟩

/-- Given a Vitali family `v` for a measure `μ`, a family `f` is a fine subfamily on a set `s` if
every point `x` in `s` belongs to arbitrarily small sets in `v.setsAt x ∩ f x`. This is precisely
the subfamilies for which the Vitali family definition ensures that one can extract a disjoint
covering of almost all `s`. -/
/-
**VitaliFamily.FineSubfamilyOn** 是 Mathlib 中的一个定义，位于命名空间 `VitaliFamily`。
形式化陈述：FineSubfamilyOn (v : VitaliFamily μ) (f : X -> Set (Set X)) (s : Set X) : 
Prop
参数：v : VitaliFamily μ；f : X -> Set (Set X)；s : Set X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a Vitali family `v` for a measure `μ`, a family `f` is a fine subfamily on
 a set `s` if
every point `x` in `s` belongs to arbitrarily small sets in `v.setsAt x ∩ f x`. 
This is precisely
the subfamilies for which the Vitali family definition ensures that one can extr
act a disjoint
covering of almost all `s`.
-/
def FineSubfamilyOn (v : VitaliFamily μ) (f : X → Set (Set X)) (s : Set X) : Prop :=
  ∀ x ∈ s, ∀ ε > 0, ∃ t ∈ v.setsAt x ∩ f x, t ⊆ closedBall x ε

namespace FineSubfamilyOn

variable {v : VitaliFamily μ} {f : X → Set (Set X)} {s : Set X} (h : v.FineSubfamilyOn f s)
include h

/-
**VitaliFamily.FineSubfamilyOn.exists_disjoint_covering_ae** 是 Mathlib 中的一个定理，位于
命名空间 `VitaliFamily.FineSubfamilyOn`。
形式化陈述：exists_disjoint_covering_ae : exists t : Set (X × Set X), (forall p : X × 
Set X, p in t -> p.1 in s) ∧ (t.PairwiseDisjoint fun p => p.2) ∧ (forall p : X ×
 Set X, p in t -> p.2 in v.setsAt p.1 inter f p.1) ∧ μ (s \ ⋃ (p : X × Set X) (_
 : p in t), p.2) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `VitaliFamily.covering`：∀ {X : Type u_1} [inst : PseudoMetricSpace X] {m 
: MeasurableSpace X} {μ : MeasureTheory.Measure X}   (self : VitaliFamily μ) (s 
: Set X) (f…
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
-/
theorem exists_disjoint_covering_ae :
    ∃ t : Set (X × Set X),
      (∀ p : X × Set X, p ∈ t → p.1 ∈ s) ∧
      (t.PairwiseDisjoint fun p => p.2) ∧
      (∀ p : X × Set X, p ∈ t → p.2 ∈ v.setsAt p.1 ∩ f p.1) ∧
      μ (s \ ⋃ (p : X × Set X) (_ : p ∈ t), p.2) = 0 :=
  v.covering s (fun x => v.setsAt x ∩ f x) (fun _ _ => inter_subset_left) h

/-- Given `h : v.FineSubfamilyOn f s`, then `h.index` is a set parametrizing a disjoint
covering of almost every `s`. -/
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/-
**VitaliFamily.FineSubfamilyOn.index** 是 Mathlib 中的一个定义，位于命名空间 `VitaliFamily.Fin
eSubfamilyOn`。
形式化陈述：{X : Type u_1} →   [inst : PseudoMetricSpace X] →     {m0 : MeasurableSpac
e X} →       {μ : MeasureTheory.Measure X} →         {v : VitaliFamily μ} → {f :
 X → Set (Set X)} → {s : Set X} → v.FineSubfamilyOn f s → Set (X × Set X)
参数：Set X；X × Set X。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `VitaliFamily.FineSubfamilyOn.exists_disjoint_covering_ae`：exists_disjoin
t_covering_ae : exists t : Set (X × Set X), (forall p : X × Set X, p in t -> p.1
 in s) ∧ (t.PairwiseDisjoint fun p => p.2) ∧ (…
-/
protected noncomputable def index : Set (X × Set X) :=
  h.exists_disjoint_covering_ae.choose

/-- Given `h : v.FineSubfamilyOn f s`, then `h.covering p` is a set in the family,
for `p ∈ h.index`, such that these sets form a disjoint covering of almost every `s`. -/
@[nolint unusedArguments]
/-
**VitaliFamily.FineSubfamilyOn.covering** 是 Mathlib 中的一个定义，位于命名空间 `VitaliFamily.
FineSubfamilyOn`。
形式化陈述：{X : Type u_1} →   [inst : PseudoMetricSpace X] →     {m0 : MeasurableSpac
e X} →       {μ : MeasureTheory.Measure X} →         {v : VitaliFamily μ} → {f :
 X → Set (Set X)} → {s : Set X} → v.FineSubfamilyOn f s → X × Set X → Set X
参数：Set X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `h : v.FineSubfamilyOn f s`, then `h.covering p` is a set in the family,
for `p ∈ h.index`, such that these sets form a disjoint covering of almost every
 `s`.
-/
protected def covering (_h : FineSubfamilyOn v f s) : X × Set X → Set X :=
  fun p => p.2
/-
**VitaliFamily.FineSubfamilyOn.index_subset** 是 Mathlib 中的一个定理，位于命名空间 `VitaliFam
ily.FineSubfamilyOn`。
形式化陈述：index_subset : forall p : X × Set X, p in h.index -> p.1 in s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `VitaliFamily.FineSubfamilyOn.exists_disjoint_covering_ae`：exists_disjoin
t_covering_ae : exists t : Set (X × Set X), (forall p : X × Set X, p in t -> p.1
 in s) ∧ (t.PairwiseDisjoint fun p => p.2) ∧ (…
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem index_subset : ∀ p : X × Set X, p ∈ h.index → p.1 ∈ s :=
  h.exists_disjoint_covering_ae.choose_spec.1
/-
**VitaliFamily.FineSubfamilyOn.covering_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Vita
liFamily.FineSubfamilyOn`。
形式化陈述：covering_disjoint : h.index.PairwiseDisjoint h.covering
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `VitaliFamily.FineSubfamilyOn.exists_disjoint_covering_ae`：exists_disjoin
t_covering_ae : exists t : Set (X × Set X), (forall p : X × Set X, p in t -> p.1
 in s) ∧ (t.PairwiseDisjoint fun p => p.2) ∧ (…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem covering_disjoint : h.index.PairwiseDisjoint h.covering :=
  h.exists_disjoint_covering_ae.choose_spec.2.1

open scoped Function in -- required for scoped `on` notation
/-
**VitaliFamily.FineSubfamilyOn.covering_disjoint_subtype** 是 Mathlib 中的一个定理，位于命名
空间 `VitaliFamily.FineSubfamilyOn`。
形式化陈述：covering_disjoint_subtype : Pairwise (Disjoint on fun x : h.index => h.cov
ering x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pairwise_subtype_iff_pairwise_set`：pairwise_subtype_iff_pairwise_set (s 
: Set α) (r : α -> α -> Prop) : (Pairwise fun (x : s) (y : s) => r x y) ↔ s.Pair
wise r
· 使用定理 `VitaliFamily.FineSubfamilyOn.covering_disjoint`：covering_disjoint : h.in
dex.PairwiseDisjoint h.covering
-/
theorem covering_disjoint_subtype : Pairwise (Disjoint on fun x : h.index => h.covering x) :=
  (pairwise_subtype_iff_pairwise_set _ _).2 h.covering_disjoint
/-
**VitaliFamily.FineSubfamilyOn.covering_mem** 是 Mathlib 中的一个定理，位于命名空间 `VitaliFam
ily.FineSubfamilyOn`。
形式化陈述：covering_mem {p : X × Set X} (hp : p in h.index) : h.covering p in f p.1
参数：hp : p in h.index。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `VitaliFamily.FineSubfamilyOn.exists_disjoint_covering_ae`：exists_disjoin
t_covering_ae : exists t : Set (X × Set X), (forall p : X × Set X, p in t -> p.1
 in s) ∧ (t.PairwiseDisjoint fun p => p.2) ∧ (…
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem covering_mem {p : X × Set X} (hp : p ∈ h.index) : h.covering p ∈ f p.1 :=
  (h.exists_disjoint_covering_ae.choose_spec.2.2.1 p hp).2
/-
**VitaliFamily.FineSubfamilyOn.covering_mem_family** 是 Mathlib 中的一个定理，位于命名空间 `Vi
taliFamily.FineSubfamilyOn`。
形式化陈述：covering_mem_family {p : X × Set X} (hp : p in h.index) : h.covering p in 
v.setsAt p.1
参数：hp : p in h.index。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `VitaliFamily.FineSubfamilyOn.exists_disjoint_covering_ae`：exists_disjoin
t_covering_ae : exists t : Set (X × Set X), (forall p : X × Set X, p in t -> p.1
 in s) ∧ (t.PairwiseDisjoint fun p => p.2) ∧ (…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem covering_mem_family {p : X × Set X} (hp : p ∈ h.index) : h.covering p ∈ v.setsAt p.1 :=
  (h.exists_disjoint_covering_ae.choose_spec.2.2.1 p hp).1
/-
**VitaliFamily.FineSubfamilyOn.measure_sdiff_biUnion** 是 Mathlib 中的一个定理，位于命名空间 `
VitaliFamily.FineSubfamilyOn`。
形式化陈述：measure_sdiff_biUnion : μ (s \ ⋃ p in h.index, h.covering p) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `VitaliFamily.FineSubfamilyOn.exists_disjoint_covering_ae`：exists_disjoin
t_covering_ae : exists t : Set (X × Set X), (forall p : X × Set X, p in t -> p.1
 in s) ∧ (t.PairwiseDisjoint fun p => p.2) ∧ (…
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem measure_sdiff_biUnion : μ (s \ ⋃ p ∈ h.index, h.covering p) = 0 :=
  h.exists_disjoint_covering_ae.choose_spec.2.2.2

@[deprecated (since := "2026-06-03")] alias measure_diff_biUnion := measure_sdiff_biUnion
/-
**VitaliFamily.FineSubfamilyOn.index_countable** 是 Mathlib 中的一个定理，位于命名空间 `Vitali
Family.FineSubfamilyOn`。
形式化陈述：index_countable [SecondCountableTopology X] : h.index.Countable
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.PairwiseDisjoint.countable_of_nonempty_interior`：∀ {α : Type u} [t :
 TopologicalSpace α] [TopologicalSpace.SeparableSpace α] {ι : Type u_2} {s : ι →
 Set α} {a : Set ι},   a.PairwiseDisjoint…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `VitaliFamily.FineSubfamilyOn.covering_disjoint`：covering_disjoint : h.in
dex.PairwiseDisjoint h.covering
· 使用定理 `VitaliFamily.nonempty_interior`：∀ {X : Type u_1} [inst : PseudoMetricSpa
ce X] {m : MeasurableSpace X} {μ : MeasureTheory.Measure X}   (self : VitaliFami
ly μ) (x : X), ∀ s ∈…
· 使用定理 `VitaliFamily.FineSubfamilyOn.covering_mem_family`：covering_mem_family {p
 : X × Set X} (hp : p in h.index) : h.covering p in v.setsAt p.1
-/
theorem index_countable [SecondCountableTopology X] : h.index.Countable :=
  h.covering_disjoint.countable_of_nonempty_interior fun _ hx =>
    v.nonempty_interior _ _ (h.covering_mem_family hx)
/-
**VitaliFamily.FineSubfamilyOn.measurableSet_u** 是 Mathlib 中的一个定理，位于命名空间 `Vitali
Family.FineSubfamilyOn`。
形式化陈述：∀ {X : Type u_1} [inst : PseudoMetricSpace X] {m0 : MeasurableSpace X} {μ 
: MeasureTheory.Measure X}   {v : VitaliFamily μ} {f : X → Set (Set X)} {s : Set
 X} (h : v.FineSubfamilyOn f s) {p : X × Set X},   p ∈ h.index → MeasurableSet (
h.covering p)
参数：Set X；h : v.FineSubfamilyOn f s；h.covering p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `VitaliFamily.measurableSet`：∀ {X : Type u_1} [inst : PseudoMetricSpace X
] {m : MeasurableSpace X} {μ : MeasureTheory.Measure X}   (self : VitaliFamily μ
) (x : X), ∀ s ∈…
· 使用定理 `VitaliFamily.FineSubfamilyOn.covering_mem_family`：covering_mem_family {p
 : X × Set X} (hp : p in h.index) : h.covering p in v.setsAt p.1
-/
protected theorem measurableSet_u {p : X × Set X} (hp : p ∈ h.index) :
    MeasurableSet (h.covering p) :=
  v.measurableSet p.1 _ (h.covering_mem_family hp)
/-
**VitaliFamily.FineSubfamilyOn.measure_le_tsum_of_absolutelyContinuous** 是 Mathl
ib 中的一个定理，位于命名空间 `VitaliFamily.FineSubfamilyOn`。
形式化陈述：measure_le_tsum_of_absolutelyContinuous [SecondCountableTopology X] {ρ : M
easure X} (hρ : ρ ≪ μ) : ρ s <= ∑' p : h.index, ρ (h.covering p)
参数：hρ : ρ ≪ μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sdiff_union_self`：sdiff_union_self {s t : Set α} : s \ t union t = s
 union t
· 使用定理 `MeasureTheory.measure_union_le`：measure_union_le (s t : Set α) : μ (s un
ion t) <= μ s + μ t
· 使用定理 `VitaliFamily.FineSubfamilyOn.measure_sdiff_biUnion`：measure_sdiff_biUnio
n : μ (s \ ⋃ p in h.index, h.covering p) = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `MeasureTheory.measure_biUnion`：measure_biUnion {s : Set β} {f : β -> Set
 α} (hs : s.Countable) (hd : s.PairwiseDisjoint f) (h : forall b in s, Measurabl
eSet (f b)) : μ (⋃ …
· 使用定理 `VitaliFamily.FineSubfamilyOn.index_countable`：index_countable [SecondCou
ntableTopology X] : h.index.Countable
· 使用定理 `VitaliFamily.FineSubfamilyOn.covering_disjoint`：covering_disjoint : h.in
dex.PairwiseDisjoint h.covering
· 使用定理 `VitaliFamily.FineSubfamilyOn.measurableSet_u`：∀ {X : Type u_1} [inst : P
seudoMetricSpace X] {m0 : MeasurableSpace X} {μ : MeasureTheory.Measure X}   {v 
: VitaliFamily μ} {f : X → Set (Se…
-/
theorem measure_le_tsum_of_absolutelyContinuous [SecondCountableTopology X] {ρ : Measure X}
    (hρ : ρ ≪ μ) : ρ s ≤ ∑' p : h.index, ρ (h.covering p) :=
  calc
    ρ s ≤ ρ ((s \ ⋃ p ∈ h.index, h.covering p) ∪ ⋃ p ∈ h.index, h.covering p) :=
      measure_mono (by simp only [subset_union_left, sdiff_union_self])
    _ ≤ ρ (s \ ⋃ p ∈ h.index, h.covering p) + ρ (⋃ p ∈ h.index, h.covering p) :=
      (measure_union_le _ _)
    _ = ∑' p : h.index, ρ (h.covering p) := by
      rw [hρ h.measure_sdiff_biUnion, zero_add,
        measure_biUnion h.index_countable h.covering_disjoint fun x hx => h.measurableSet_u hx]
/-
**VitaliFamily.FineSubfamilyOn.measure_le_tsum** 是 Mathlib 中的一个定理，位于命名空间 `Vitali
Family.FineSubfamilyOn`。
形式化陈述：measure_le_tsum [SecondCountableTopology X] : μ s <= ∑' x : h.index, μ (h.
covering x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `VitaliFamily.FineSubfamilyOn.measure_le_tsum_of_absolutelyContinuous`：me
asure_le_tsum_of_absolutelyContinuous [SecondCountableTopology X] {ρ : Measure X
} (hρ : ρ ≪ μ) : ρ s <= ∑' p : h.index, ρ (h.covering p)
· 使用定理 `MeasureTheory.Measure.AbsolutelyContinuous.rfl`：∀ {α : Type u_1} {mα : M
easurableSpace α} {μ : MeasureTheory.Measure α}, μ.AbsolutelyContinuous μ
-/
theorem measure_le_tsum [SecondCountableTopology X] : μ s ≤ ∑' x : h.index, μ (h.covering x) :=
  h.measure_le_tsum_of_absolutelyContinuous Measure.AbsolutelyContinuous.rfl

end FineSubfamilyOn

/-- One can enlarge a Vitali family by adding to the sets `f x` at `x` all sets which are not
contained in a `δ`-neighborhood on `x`. This does not change the local filter at a point, but it
can be convenient to get a nicer global behavior. -/
/-
**VitaliFamily.enlarge** 是 Mathlib 中的一个定义，位于命名空间 `VitaliFamily`。
形式化陈述：enlarge (v : VitaliFamily μ) (δ : Real) (δpos : 0 < δ) : VitaliFamily μ wh
ere setsAt x
参数：v : VitaliFamily μ；δ : Real；δpos : 0 < δ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
One can enlarge a Vitali family by adding to the sets `f x` at `x` all sets whic
h are not
contained in a `δ`-neighborhood on `x`. This does not change the local filter at
 a point, but it
can be convenient to get a nicer global behavior.
-/
def enlarge (v : VitaliFamily μ) (δ : ℝ) (δpos : 0 < δ) : VitaliFamily μ where
  setsAt x := v.setsAt x ∪ {s | MeasurableSet s ∧ (interior s).Nonempty ∧ ¬s ⊆ closedBall x δ}
  measurableSet := by
    rintro x s (hs | hs)
    exacts [v.measurableSet _ _ hs, hs.1]
  nonempty_interior := by
    rintro x s (hs | hs)
    exacts [v.nonempty_interior _ _ hs, hs.2.1]
  nontrivial := by
    intro x ε εpos
    rcases v.nontrivial x ε εpos with ⟨s, hs, h's⟩
    exact ⟨s, mem_union_left _ hs, h's⟩
  covering := by
    intro s f fset ffine
    let g : X → Set (Set X) := fun x => f x ∩ v.setsAt x
    have : ∀ x ∈ s, ∀ ε : ℝ, ε > 0 → ∃ t ∈ g x, t ⊆ closedBall x ε := by
      intro x hx ε εpos
      obtain ⟨t, tf, ht⟩ : ∃ t ∈ f x, t ⊆ closedBall x (min ε δ) :=
        ffine x hx (min ε δ) (lt_min εpos δpos)
      rcases fset x hx tf with (h't | h't)
      · exact ⟨t, ⟨tf, h't⟩, ht.trans (closedBall_subset_closedBall (min_le_left _ _))⟩
      · refine False.elim (h't.2.2 ?_)
        exact ht.trans (closedBall_subset_closedBall (min_le_right _ _))
    rcases v.covering s g (fun x _ => inter_subset_right) this with ⟨t, ts, tdisj, tg, μt⟩
    exact ⟨t, ts, tdisj, fun p hp => (tg p hp).1, μt⟩

variable (v : VitaliFamily μ)

/-- Given a vitali family `v`, then `v.filterAt x` is the filter on `Set X` made of those families
that contain all sets of `v.setsAt x` of a sufficiently small diameter. This filter makes it
possible to express limiting behavior when sets in `v.setsAt x` shrink to `x`. -/
/-
**VitaliFamily.filterAt** 是 Mathlib 中的一个定义，位于命名空间 `VitaliFamily`。
形式化陈述：filterAt (x : X) : Filter (Set X)
参数：x : X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a vitali family `v`, then `v.filterAt x` is the filter on `Set X` made of 
those families
that contain all sets of `v.setsAt x` of a sufficiently small diameter. This fil
ter makes it
possible to express limiting behavior when sets in `v.setsAt x` shrink to `x`.
-/
def filterAt (x : X) : Filter (Set X) := (𝓝 x).smallSets ⊓ 𝓟 (v.setsAt x)
/-
**VitaliFamily._root_.Filter.HasBasis.vitaliFamily** 是 Mathlib 中的一个定理，位于命名空间 `Vi
taliFamily`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Filter.HasBasis.vitaliFamily {ι : Sort*} {p : ι → Prop} {s : ι → Set X} {x : X}
    (h : (𝓝 x).HasBasis p s) : (v.filterAt x).HasBasis p (fun i ↦ {t ∈ v.setsAt x | t ⊆ s i}) := by
  simpa only [← Set.ofPred_inter_eq_sep] using! h.smallSets.inf_principal _
/-
**VitaliFamily.filterAt_basis_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `VitaliFamily
`。
形式化陈述：filterAt_basis_closedBall (x : X) : (v.filterAt x).HasBasis (0 < ·) ({t in
 v.setsAt x | t subseteq closedBall x ·})
参数：x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.vitaliFamily`：∀ {X : Type u_1} [inst : PseudoMetricSpace
 X] {m0 : MeasurableSpace X} {μ : MeasureTheory.Measure X}   (v : VitaliFamily μ
) {ι : Sort u_2} {…
· 使用定理 `Metric.nhds_basis_closedBall`：nhds_basis_closedBall : (𝓝 x).HasBasis (fu
n ε : Real => 0 < ε) (closedBall x)
-/
theorem filterAt_basis_closedBall (x : X) :
    (v.filterAt x).HasBasis (0 < ·) ({t ∈ v.setsAt x | t ⊆ closedBall x ·}) :=
  nhds_basis_closedBall.vitaliFamily v
/-
**VitaliFamily.mem_filterAt_iff** 是 Mathlib 中的一个定理，位于命名空间 `VitaliFamily`。
形式化陈述：mem_filterAt_iff {x : X} {s : Set (Set X)} : s in v.filterAt x ↔ exists ε 
> (0 : Real), forall t in v.setsAt x, t subseteq closedBall x ε -> t in s
参数：Set X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `VitaliFamily.filterAt_basis_closedBall`：filterAt_basis_closedBall (x : X
) : (v.filterAt x).HasBasis (0 < ·) ({t in v.setsAt x | t subseteq closedBall x 
·})
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_filterAt_iff {x : X} {s : Set (Set X)} :
    s ∈ v.filterAt x ↔ ∃ ε > (0 : ℝ), ∀ t ∈ v.setsAt x, t ⊆ closedBall x ε → t ∈ s := by
  simp only [(v.filterAt_basis_closedBall x).mem_iff, ← and_imp, subset_def, mem_ofPred]
/-
**VitaliFamily.filterAt_neBot** 是 Mathlib 中的一个实例，位于命名空间 `VitaliFamily`。
形式化陈述：filterAt_neBot (x : X) : (v.filterAt x).NeBot
参数：x : X。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.HasBasis.neBot_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α
} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → (l.NeBot ↔ ∀ {i : ι}, p i →
 (s i).Nonempty…
· 使用定理 `VitaliFamily.filterAt_basis_closedBall`：filterAt_basis_closedBall (x : X
) : (v.filterAt x).HasBasis (0 < ·) ({t in v.setsAt x | t subseteq closedBall x 
·})
· 使用定理 `VitaliFamily.nontrivial`：∀ {X : Type u_1} [inst : PseudoMetricSpace X] {
m : MeasurableSpace X} {μ : MeasureTheory.Measure X}   (self : VitaliFamily μ) (
x : X), ∀ ε >…
-/
instance filterAt_neBot (x : X) : (v.filterAt x).NeBot :=
  (v.filterAt_basis_closedBall x).neBot_iff.2 <| v.nontrivial _ _
/-
**VitaliFamily.eventually_filterAt_iff** 是 Mathlib 中的一个定理，位于命名空间 `VitaliFamily`。
形式化陈述：eventually_filterAt_iff {x : X} {P : Set X -> Prop} : (forallᶠ t in v.filt
erAt x, P t) ↔ exists ε > (0 : Real), forall t in v.setsAt x, t subseteq closedB
all x ε -> P t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `VitaliFamily.mem_filterAt_iff`：mem_filterAt_iff {x : X} {s : Set (Set X)
} : s in v.filterAt x ↔ exists ε > (0 : Real), forall t in v.setsAt x, t subsete
q closedBall x ε ->…
-/
theorem eventually_filterAt_iff {x : X} {P : Set X → Prop} :
    (∀ᶠ t in v.filterAt x, P t) ↔ ∃ ε > (0 : ℝ), ∀ t ∈ v.setsAt x, t ⊆ closedBall x ε → P t :=
  v.mem_filterAt_iff
/-
**VitaliFamily.tendsto_filterAt_iff** 是 Mathlib 中的一个定理，位于命名空间 `VitaliFamily`。
形式化陈述：tendsto_filterAt_iff {ι : Type*} {l : Filter ι} {f : ι -> Set X} {x : X} :
 Tendsto f l (v.filterAt x) ↔ (forallᶠ i in l, f i in v.setsAt x) ∧ forall ε > (
0 : Real), forallᶠ i in l, f i subseteq closedBall x ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用定理 `Filter.HasBasis.smallSets`：∀ {α : Type u_1} {ι : Sort u_3} {l : Filter α
} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → l.smallSets.HasBasis p fun 
i => 𝒫 s i
· 使用定理 `Metric.nhds_basis_closedBall`：nhds_basis_closedBall : (𝓝 x).HasBasis (fu
n ε : Real => 0 < ε) (closedBall x)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem tendsto_filterAt_iff {ι : Type*} {l : Filter ι} {f : ι → Set X} {x : X} :
    Tendsto f l (v.filterAt x) ↔
      (∀ᶠ i in l, f i ∈ v.setsAt x) ∧ ∀ ε > (0 : ℝ), ∀ᶠ i in l, f i ⊆ closedBall x ε := by
  simp only [filterAt, tendsto_inf, nhds_basis_closedBall.smallSets.tendsto_right_iff,
    tendsto_principal, and_comm, mem_powerset_iff]
/-
**VitaliFamily.eventually_filterAt_mem_setsAt** 是 Mathlib 中的一个定理，位于命名空间 `VitaliF
amily`。
形式化陈述：eventually_filterAt_mem_setsAt (x : X) : forallᶠ t in v.filterAt x, t in v
.setsAt x
参数：x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `VitaliFamily.tendsto_filterAt_iff`：tendsto_filterAt_iff {ι : Type*} {l :
 Filter ι} {f : ι -> Set X} {x : X} : Tendsto f l (v.filterAt x) ↔ (forallᶠ i in
 l, f i in v.setsAt x) …
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
-/
theorem eventually_filterAt_mem_setsAt (x : X) : ∀ᶠ t in v.filterAt x, t ∈ v.setsAt x :=
  (v.tendsto_filterAt_iff.mp tendsto_id).1
/-
**VitaliFamily.eventually_filterAt_subset_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `
VitaliFamily`。
形式化陈述：eventually_filterAt_subset_closedBall (x : X) {ε : Real} (hε : 0 < ε) : fo
rallᶠ t : Set X in v.filterAt x, t subseteq closedBall x ε
参数：x : X；hε : 0 < ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `VitaliFamily.tendsto_filterAt_iff`：tendsto_filterAt_iff {ι : Type*} {l :
 Filter ι} {f : ι -> Set X} {x : X} : Tendsto f l (v.filterAt x) ↔ (forallᶠ i in
 l, f i in v.setsAt x) …
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
-/
theorem eventually_filterAt_subset_closedBall (x : X) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : Set X in v.filterAt x, t ⊆ closedBall x ε :=
  (v.tendsto_filterAt_iff.mp tendsto_id).2 ε hε
/-
**VitaliFamily.eventually_filterAt_measurableSet** 是 Mathlib 中的一个定理，位于命名空间 `Vita
liFamily`。
形式化陈述：eventually_filterAt_measurableSet (x : X) : forallᶠ t in v.filterAt x, Mea
surableSet t
参数：x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `VitaliFamily.eventually_filterAt_mem_setsAt`：eventually_filterAt_mem_set
sAt (x : X) : forallᶠ t in v.filterAt x, t in v.setsAt x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `VitaliFamily.measurableSet`：∀ {X : Type u_1} [inst : PseudoMetricSpace X
] {m : MeasurableSpace X} {μ : MeasureTheory.Measure X}   (self : VitaliFamily μ
) (x : X), ∀ s ∈…
-/
theorem eventually_filterAt_measurableSet (x : X) : ∀ᶠ t in v.filterAt x, MeasurableSet t := by
  filter_upwards [v.eventually_filterAt_mem_setsAt x] with _ ha using v.measurableSet _ _ ha
/-
**VitaliFamily.frequently_filterAt_iff** 是 Mathlib 中的一个定理，位于命名空间 `VitaliFamily`。
形式化陈述：frequently_filterAt_iff {x : X} {P : Set X -> Prop} : (existsᶠ t in v.filt
erAt x, P t) ↔ forall ε > (0 : Real), exists t in v.setsAt x, t subseteq closedB
all x ε ∧ P t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.frequently_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Fil
ter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ {q : α → Prop}, (∃ᶠ 
(x : α) in l, q x) ↔…
· 使用定理 `VitaliFamily.filterAt_basis_closedBall`：filterAt_basis_closedBall (x : X
) : (v.filterAt x).HasBasis (0 < ·) ({t in v.setsAt x | t subseteq closedBall x 
·})
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem frequently_filterAt_iff {x : X} {P : Set X → Prop} :
    (∃ᶠ t in v.filterAt x, P t) ↔ ∀ ε > (0 : ℝ), ∃ t ∈ v.setsAt x, t ⊆ closedBall x ε ∧ P t := by
  simp only [(v.filterAt_basis_closedBall x).frequently_iff, ← and_assoc, subset_def, mem_ofPred]
/-
**VitaliFamily.eventually_filterAt_subset_of_nhds** 是 Mathlib 中的一个定理，位于命名空间 `Vit
aliFamily`。
形式化陈述：eventually_filterAt_subset_of_nhds {x : X} {o : Set X} (hx : o in 𝓝 x) : f
orallᶠ t in v.filterAt x, t subseteq o
参数：hx : o in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventually_smallSets_subset`：eventually_smallSets_subset {s : Set
 α} : (forallᶠ t in l.smallSets, t subseteq s) ↔ s in l
-/
theorem eventually_filterAt_subset_of_nhds {x : X} {o : Set X} (hx : o ∈ 𝓝 x) :
    ∀ᶠ t in v.filterAt x, t ⊆ o :=
  (eventually_smallSets_subset.2 hx).filter_mono inf_le_left

@[simp]
/-
**VitaliFamily.filterAt_enlarge** 是 Mathlib 中的一个定理，位于命名空间 `VitaliFamily`。
形式化陈述：filterAt_enlarge (v : VitaliFamily μ) {δ : Real} (δpos : 0 < δ) : (v.enlar
ge δ δpos).filterAt = v.filterAt
参数：v : VitaliFamily μ；δpos : 0 < δ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventually_smallSets_subset`：eventually_smallSets_subset {s : Set
 α} : (forallᶠ t in l.smallSets, t subseteq s) ↔ s in l
· 使用定理 `Metric.closedBall_mem_nhds`：closedBall_mem_nhds (x : α) {ε : Real} (ε0 :
 0 < ε) : closedBall x ε in 𝓝 x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inf_sup_left`：inf_sup_left (a b c : α) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
theorem filterAt_enlarge (v : VitaliFamily μ) {δ : ℝ} (δpos : 0 < δ) :
    (v.enlarge δ δpos).filterAt = v.filterAt := by
  ext1 x
  suffices {t | MeasurableSet t → (interior t).Nonempty → ¬t ⊆ closedBall x δ →
      t ∈ v.setsAt x} ∈ (𝓝 x).smallSets by
    simpa [VitaliFamily.filterAt, VitaliFamily.enlarge, ← sup_principal, inf_sup_left,
      mem_inf_principal]
  filter_upwards [eventually_smallSets_subset.mpr (closedBall_mem_nhds _ δpos)]
  simp +contextual
/-
**VitaliFamily.fineSubfamilyOn_iff_frequently** 是 Mathlib 中的一个定理，位于命名空间 `VitaliF
amily`。
形式化陈述：fineSubfamilyOn_iff_frequently (v : VitaliFamily μ) {f : X -> Set (Set X)}
 {s : Set X} : v.FineSubfamilyOn f s ↔ forall x in s, existsᶠ t in v.filterAt x,
 t in f x
参数：v : VitaliFamily μ；Set X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem fineSubfamilyOn_iff_frequently (v : VitaliFamily μ) {f : X → Set (Set X)} {s : Set X} :
    v.FineSubfamilyOn f s ↔ ∀ x ∈ s, ∃ᶠ t in v.filterAt x, t ∈ f x := by
  refine forall₂_congr fun x hx ↦ ?_
  simp [frequently_filterAt_iff, ← and_assoc, and_right_comm]
/-
**VitaliFamily.fineSubfamilyOn_of_frequently** 是 Mathlib 中的一个定理，位于命名空间 `VitaliFa
mily`。
形式化陈述：fineSubfamilyOn_of_frequently (v : VitaliFamily μ) (f : X -> Set (Set X)) 
(s : Set X) (h : forall x in s, existsᶠ t in v.filterAt x, t in f x) : v.FineSub
familyOn f s
参数：v : VitaliFamily μ；f : X -> Set (Set X)；s : Set X；h : forall x in s, existsᶠ 
t in v.filterAt x, t in f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `VitaliFamily.fineSubfamilyOn_iff_frequently`：fineSubfamilyOn_iff_frequen
tly (v : VitaliFamily μ) {f : X -> Set (Set X)} {s : Set X} : v.FineSubfamilyOn 
f s ↔ forall x in s, existsᶠ t in…
-/
theorem fineSubfamilyOn_of_frequently (v : VitaliFamily μ) (f : X → Set (Set X)) (s : Set X)
    (h : ∀ x ∈ s, ∃ᶠ t in v.filterAt x, t ∈ f x) : v.FineSubfamilyOn f s := by
  rwa [fineSubfamilyOn_iff_frequently]

end VitaliFamily

