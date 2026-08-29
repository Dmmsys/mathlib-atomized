/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.MeasureTheory.Measure.Map

/-!
# Absolute Continuity of Measures

We say that `μ` is absolutely continuous with respect to `ν`, or that `μ` is dominated by `ν`,
if `ν(A) = 0` implies that `μ(A) = 0`. We denote that by `μ ≪ ν`.

It is equivalent to an inequality of the almost everywhere filters of the measures:
`μ ≪ ν ↔ ae μ ≤ ae ν`.

## Main definitions

* `MeasureTheory.Measure.AbsolutelyContinuous μ ν`: `μ` is absolutely continuous with respect to `ν`

## Main statements

* `ae_le_iff_absolutelyContinuous`: `ae μ ≤ ae ν ↔ μ ≪ ν`

## Notation

* `μ ≪ ν`: `MeasureTheory.Measure.AbsolutelyContinuous μ ν`. That is: `μ` is absolutely continuous
  with respect to `ν`

-/

@[expose] public section

variable {α β δ ι R : Type*}

namespace MeasureTheory

open Set ENNReal NNReal

variable {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ μ₁ μ₂ μ₃ ν ν' : Measure α} {s t : Set α}

namespace Measure

/--
Definition of `AbsolutelyContinuous` / `AbsolutelyContinuous` 的定义

English:
definition AbsolutelyContinuous
  signature: {_m0 : MeasurableSpace α} (μ ν : Measure α)
  body: forall ⦃s : Set α⦄, ν s = 0 -> μ s = 0

@[inherit_doc MeasureTheory.Measure.AbsolutelyContinuous]
scoped[MeasureTheory] infixl:50 " ≪ " => MeasureTheory.Measure.AbsolutelyContinuous

中文:
定义 AbsolutelyContinuous
  签名: {_m0 : 可测空间 α} (μ ν : 测度 α)
  定义体: forall ⦃s : Set α⦄, ν s = 0 -> μ s = 0

@[inherit_doc MeasureTheory.Measure.AbsolutelyContinuous]
scoped[MeasureTheory] infixl:50 " ≪ " => MeasureTheory.Measure.AbsolutelyContinuous
-/
def AbsolutelyContinuous {_m0 : MeasurableSpace α} (μ ν : Measure α) : Prop :=
  forall ⦃s : Set α⦄, ν s = 0 -> μ s = 0

@[inherit_doc MeasureTheory.Measure.AbsolutelyContinuous]
scoped[MeasureTheory] infixl:50 " ≪ " => MeasureTheory.Measure.AbsolutelyContinuous

/--
theorem `absolutelyContinuous_of_le` / 定理 `absolutelyContinuous_of_le`

English:
theorem absolutelyContinuous_of_le
  given: (h : μ <= ν)
  statement: μ ≪ ν
  proof: fun s hs =>
nonpos_iff_eq_zero.1 hs ▸ le_iff'.1 h s

alias _root_.LE.le.absolutelyContinuous := absolutelyContinuous_of_le

中文:
定理 absolutelyContinuous_of_le
  条件: (h : μ <= ν)
  结论: μ ≪ ν
  证明: fun s hs =>
nonpos_iff_eq_zero.1 hs ▸ le_iff'.1 h s

alias _root_.LE.le.absolutelyContinuous := absolutelyContinuous_of_le
-/
theorem absolutelyContinuous_of_le (h : μ <= ν) : μ ≪ ν := fun s hs =>
nonpos_iff_eq_zero.1 hs ▸ le_iff'.1 h s

alias _root_.LE.le.absolutelyContinuous := absolutelyContinuous_of_le

/--
theorem `absolutelyContinuous_of_eq` / 定理 `absolutelyContinuous_of_eq`

English:
theorem absolutelyContinuous_of_eq
  given: (h : μ = ν)
  statement: μ ≪ ν
  proof: h.le.absolutelyContinuous

alias _root_.Eq.absolutelyContinuous := absolutelyContinuous_of_eq

中文:
定理 absolutelyContinuous_of_eq
  条件: (h : μ = ν)
  结论: μ ≪ ν
  证明: h.le.absolutelyContinuous

alias _root_.Eq.absolutelyContinuous := absolutelyContinuous_of_eq

Depends on / 依赖: absolutelyContinuous, h.le.absolutelyContinuous
-/
theorem absolutelyContinuous_of_eq (h : μ = ν) : μ ≪ ν :=
  h.le.absolutelyContinuous

alias _root_.Eq.absolutelyContinuous := absolutelyContinuous_of_eq

namespace AbsolutelyContinuous

/--
theorem `mk` / 定理 `mk`

English:
theorem mk
  given: (h : forall ⦃s : Set α⦄, MeasurableSet s -> ν s = 0 -> μ s = 0)
  statement: μ ≪ ν
  proof: by
  intro s hs
  rcases exists_measurable_superset_of_null hs with ⟨t, h1t, h2t, h3t⟩
  exact measure_mono_null h1t (h h2t h3t)

@[refl]

中文:
定理 mk
  条件: (h : 对任意 ⦃s : 集合 α⦄, 可测集 s -> ν s = 0 -> μ s = 0)
  结论: μ ≪ ν
  证明: by
  intro s hs
  rcases exists_measurable_superset_of_null hs with ⟨t, h1t, h2t, h3t⟩
  exact measure_mono_null h1t (h h2t h3t)

@[refl]

Depends on / 依赖: exists_measurable_superset_of_null, measure_mono_null
-/
theorem mk (h : forall ⦃s : Set α⦄, MeasurableSet s -> ν s = 0 -> μ s = 0) : μ ≪ ν := by
  intro s hs
  rcases exists_measurable_superset_of_null hs with ⟨t, h1t, h2t, h3t⟩
  exact measure_mono_null h1t (h h2t h3t)

@[refl]
/--
theorem `refl` / 定理 `refl`

English:
theorem refl
  given: {_m0 : MeasurableSpace α} (μ : Measure α)
  statement: μ ≪ μ
  proof: rfl.absolutelyContinuous

中文:
定理 refl
  条件: {_m0 : 可测空间 α} (μ : 测度 α)
  结论: μ ≪ μ
  证明: rfl.absolutelyContinuous
-/
protected theorem refl {_m0 : MeasurableSpace α} (μ : Measure α) : μ ≪ μ :=
  rfl.absolutelyContinuous

/--
theorem `rfl` / 定理 `rfl`

English:
theorem rfl
  statement: μ ≪ μ
  proof: fun _s hs => hs

中文:
定理 rfl
  结论: μ ≪ μ
  证明: fun _s hs => hs
-/
protected theorem rfl : μ ≪ μ := fun _s hs => hs

/--
Instance `instRefl` / 实例 `instRefl`

English:
instance instRefl
  signature: {_ : MeasurableSpace α}
  body: ⟨fun _ => AbsolutelyContinuous.rfl⟩

@[simp]

中文:
实例 instRefl
  签名: {_ : 可测空间 α}
  定义体: ⟨fun _ => AbsolutelyContinuous.rfl⟩

@[simp]

Depends on / 依赖: AbsolutelyContinuous, AbsolutelyContinuous.rfl
-/
instance instRefl {_ : MeasurableSpace α} : @Std.Refl (Measure α) (· ≪ ·) :=
  ⟨fun _ => AbsolutelyContinuous.rfl⟩

@[simp]
/--
lemma `zero` / 引理 `zero`

English:
lemma zero
  given: (μ : Measure α)
  statement: 0 ≪ μ
  proof: fun _ _ => by simp

@[trans]

中文:
引理 zero
  条件: (μ : 测度 α)
  结论: 0 ≪ μ
  证明: fun _ _ => by simp

@[trans]
-/
protected lemma zero (μ : Measure α) : 0 ≪ μ := fun _ _ => by simp

@[trans]
/--
theorem `trans` / 定理 `trans`

English:
theorem trans
  given: (h1 : μ₁ ≪ μ₂) (h2 : μ₂ ≪ μ₃)
  statement: μ₁ ≪ μ₃
  proof: fun _s hs => h1 h2 hs

@[gcongr, mono]

中文:
定理 trans
  条件: (h1 : μ₁ ≪ μ₂) (h2 : μ₂ ≪ μ₃)
  结论: μ₁ ≪ μ₃
  证明: fun _s hs => h1 h2 hs

@[gcongr, mono]
-/
protected theorem trans (h1 : μ₁ ≪ μ₂) (h2 : μ₂ ≪ μ₃) : μ₁ ≪ μ₃ := fun _s hs => h1 h2 hs

@[gcongr, mono]
/--
theorem `map` / 定理 `map`

English:
theorem map
  given: (h : μ ≪ ν) {f : α -> β} (hf : Measurable f)
  statement: μ.map f ≪ ν.map f
  proof: AbsolutelyContinuous.mk fun s hs => by simpa [hf, hs] using @h _

中文:
定理 map
  条件: (h : μ ≪ ν) {f : α -> β} (hf : 可测 f)
  结论: μ.map f ≪ ν.map f
  证明: AbsolutelyContinuous.mk fun s hs => by simpa [hf, hs] using @h _
-/
protected theorem map (h : μ ≪ ν) {f : α -> β} (hf : Measurable f) : μ.map f ≪ ν.map f :=
  AbsolutelyContinuous.mk fun s hs => by simpa [hf, hs] using @h _

/--
theorem `smul_left` / 定理 `smul_left`

English:
theorem smul_left
  given: [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] (h : μ ≪ ν) (c : R)
  proof: fun s hνs => by
  simp only [h hνs, smul_apply, smul_zero, ← smul_one_smul Real>=0∞ c (0 : Real>=0∞)]

中文:
定理 smul_left
  条件: [标量乘法 R 实数>=0∞] [标量塔 R 实数>=0∞ 实数>=0∞] (h : μ ≪ ν) (c : R)
  证明: fun s hνs => by
  simp only [h hνs, smul_apply, smul_zero, ← smul_one_smul Real>=0∞ c (0 : Real>=0∞)]
-/
protected theorem smul_left [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] (h : μ ≪ ν) (c : R) :
    c • μ ≪ ν := fun s hνs => by
  simp only [h hνs, smul_apply, smul_zero, ← smul_one_smul Real>=0∞ c (0 : Real>=0∞)]

/--
theorem `smul` / 定理 `smul`

English:
theorem smul
  given: [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] (h : μ ≪ ν) (c : R)
  proof: by
  intro s hνs
  rw [smul_apply]; rw [← smul_one_smul Real>=0∞]; rw [smul_eq_mul]; rw [mul_eq_zero] at hνs ⊢
  exact hνs.imp_right fun hs => h hs

中文:
定理 smul
  条件: [标量乘法 R 实数>=0∞] [标量塔 R 实数>=0∞ 实数>=0∞] (h : μ ≪ ν) (c : R)
  证明: by
  intro s hνs
  rw [smul_apply]; rw [← smul_one_smul Real>=0∞]; rw [smul_eq_mul]; rw [mul_eq_zero] at hνs ⊢
  exact hνs.imp_right fun hs => h hs
-/
protected theorem smul [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] (h : μ ≪ ν) (c : R) :
    c • μ ≪ c • ν := by
  intro s hνs
  rw [smul_apply]; rw [← smul_one_smul Real>=0∞]; rw [smul_eq_mul]; rw [mul_eq_zero] at hνs ⊢
  exact hνs.imp_right fun hs => h hs

/--
lemma `add` / 引理 `add`

English:
lemma add
  given: (h1 : μ₁ ≪ ν) (h2 : μ₂ ≪ ν')
  statement: μ₁ + μ₂ ≪ ν + ν'
  proof: by
  intro s hs
  simp only [coe_add, Pi.add_apply, add_eq_zero] at hs ⊢
  exact ⟨h1 hs.1, h2 hs.2⟩

中文:
引理 add
  条件: (h1 : μ₁ ≪ ν) (h2 : μ₂ ≪ ν')
  结论: μ₁ + μ₂ ≪ ν + ν'
  证明: by
  intro s hs
  simp only [coe_add, Pi.add_apply, add_eq_zero] at hs ⊢
  exact ⟨h1 hs.1, h2 hs.2⟩
-/
protected lemma add (h1 : μ₁ ≪ ν) (h2 : μ₂ ≪ ν') : μ₁ + μ₂ ≪ ν + ν' := by
  intro s hs
  simp only [coe_add, Pi.add_apply, add_eq_zero] at hs ⊢
  exact ⟨h1 hs.1, h2 hs.2⟩

/--
lemma `add_left_iff` / 引理 `add_left_iff`

English:
lemma add_left_iff
  given: {μ₁ μ₂ ν : Measure α}
  proof: by
  refine ⟨fun h => ?_, fun h => (h.1.add h.2).trans ?_⟩
  · have : forall s, ν s = 0 -> μ₁ s = 0 ∧ μ₂ s = 0 := by intro s hs0; simpa using h hs0
    exact ⟨fun s hs0 => (this s hs0).1, fun s hs0 => (this s hs0).2⟩
  · rw [← two_smul Real>=0]
    exact AbsolutelyContinuous.rfl.smul_left 2

中文:
引理 add_left_iff
  条件: {μ₁ μ₂ ν : 测度 α}
  证明: by
  refine ⟨fun h => ?_, fun h => (h.1.add h.2).trans ?_⟩
  · have : forall s, ν s = 0 -> μ₁ s = 0 ∧ μ₂ s = 0 := by intro s hs0; simpa using h hs0
    exact ⟨fun s hs0 => (this s hs0).1, fun s hs0 => (this s hs0).2⟩
  · rw [← two_smul Real>=0]
    exact AbsolutelyContinuous.rfl.smul_left 2

Depends on / 依赖: AbsolutelyContinuous, AbsolutelyContinuous.rfl.smul_left, smul_left, two_smul
-/
lemma add_left_iff {μ₁ μ₂ ν : Measure α} :
    μ₁ + μ₂ ≪ ν ↔ μ₁ ≪ ν ∧ μ₂ ≪ ν := by
  refine ⟨fun h => ?_, fun h => (h.1.add h.2).trans ?_⟩
  · have : forall s, ν s = 0 -> μ₁ s = 0 ∧ μ₂ s = 0 := by intro s hs0; simpa using h hs0
    exact ⟨fun s hs0 => (this s hs0).1, fun s hs0 => (this s hs0).2⟩
  · rw [← two_smul Real>=0]
    exact AbsolutelyContinuous.rfl.smul_left 2

/--
lemma `add_left` / 引理 `add_left`

English:
lemma add_left
  given: {μ₁ μ₂ ν : Measure α} (h₁ : μ₁ ≪ ν) (h₂ : μ₂ ≪ ν)
  statement: μ₁ + μ₂ ≪ ν
  proof: Measure.AbsolutelyContinuous.add_left_iff.mpr ⟨h₁, h₂⟩

中文:
引理 add_left
  条件: {μ₁ μ₂ ν : 测度 α} (h₁ : μ₁ ≪ ν) (h₂ : μ₂ ≪ ν)
  结论: μ₁ + μ₂ ≪ ν
  证明: Measure.AbsolutelyContinuous.add_left_iff.mpr ⟨h₁, h₂⟩

Depends on / 依赖: AbsolutelyContinuous, Measure, Measure.AbsolutelyContinuous.add_left_iff.mpr, add_left_iff
-/
lemma add_left {μ₁ μ₂ ν : Measure α} (h₁ : μ₁ ≪ ν) (h₂ : μ₂ ≪ ν) : μ₁ + μ₂ ≪ ν :=
  Measure.AbsolutelyContinuous.add_left_iff.mpr ⟨h₁, h₂⟩

/--
lemma `add_right` / 引理 `add_right`

English:
lemma add_right
  given: (h1 : μ ≪ ν) (ν' : Measure α)
  statement: μ ≪ ν + ν'
  proof: by
  intro s hs
  simp only [coe_add, Pi.add_apply, add_eq_zero] at hs ⊢
  exact h1 hs.1

中文:
引理 add_right
  条件: (h1 : μ ≪ ν) (ν' : 测度 α)
  结论: μ ≪ ν + ν'
  证明: by
  intro s hs
  simp only [coe_add, Pi.add_apply, add_eq_zero] at hs ⊢
  exact h1 hs.1

Depends on / 依赖: Pi.add_apply, add_apply, add_eq_zero, coe_add
-/
lemma add_right (h1 : μ ≪ ν) (ν' : Measure α) : μ ≪ ν + ν' := by
  intro s hs
  simp only [coe_add, Pi.add_apply, add_eq_zero] at hs ⊢
  exact h1 hs.1

/--
lemma `add_right'` / 引理 `add_right'`

English:
lemma add_right'
  given: (h : μ ≪ ν') (ν : Measure α)
  statement: μ ≪ ν + ν'
  proof: by
  simp [add_comm, add_right h]

中文:
引理 add_right'
  条件: (h : μ ≪ ν') (ν : 测度 α)
  结论: μ ≪ ν + ν'
  证明: by
  simp [add_comm, add_right h]

Depends on / 依赖: add_comm, add_right
-/
lemma add_right' (h : μ ≪ ν') (ν : Measure α) : μ ≪ ν + ν' := by
  simp [add_comm, add_right h]

/--
lemma `null_mono` / 引理 `null_mono`

English:
lemma null_mono
  given: {μ ν : Measure α} (hμν : μ ≪ ν) ⦃t
  statement: Set α⦄
  proof: hμν ht

中文:
引理 null_mono
  条件: {μ ν : 测度 α} (hμν : μ ≪ ν) ⦃t
  结论: 集合 α⦄
  证明: hμν ht
-/
lemma null_mono {μ ν : Measure α} (hμν : μ ≪ ν) ⦃t : Set α⦄
    (ht : ν t = 0) : μ t = 0 :=
  hμν ht

/--
lemma `pos_mono` / 引理 `pos_mono`

English:
lemma pos_mono
  given: {μ ν : Measure α} (hμν : μ ≪ ν) ⦃t
  statement: Set α⦄
  proof: by
  contrapose! ht
  simp_all [hμν.null_mono]

中文:
引理 pos_mono
  条件: {μ ν : 测度 α} (hμν : μ ≪ ν) ⦃t
  结论: 集合 α⦄
  证明: by
  contrapose! ht
  simp_all [hμν.null_mono]

Depends on / 依赖: contrapose, null_mono
-/
lemma pos_mono {μ ν : Measure α} (hμν : μ ≪ ν) ⦃t : Set α⦄
    (ht : 0 < μ t) : 0 < ν t := by
  contrapose! ht
  simp_all [hμν.null_mono]

end AbsolutelyContinuous

@[simp]
/--
lemma `absolutelyContinuous_zero_iff` / 引理 `absolutelyContinuous_zero_iff`

English:
lemma absolutelyContinuous_zero_iff
  statement: μ ≪ 0 ↔ μ = 0
  proof: ⟨fun h => measure_univ_eq_zero.mp (h rfl), fun h => h.symm ▸ AbsolutelyContinuous.zero _⟩

alias absolutelyContinuous_refl := AbsolutelyContinuous.refl
alias absolutelyContinuous_rfl := AbsolutelyContinuous.rfl

中文:
引理 absolutelyContinuous_zero_iff
  结论: μ ≪ 0 ↔ μ = 0
  证明: ⟨fun h => measure_univ_eq_zero.mp (h rfl), fun h => h.symm ▸ AbsolutelyContinuous.zero _⟩

alias absolutelyContinuous_refl := AbsolutelyContinuous.refl
alias absolutelyContinuous_rfl := AbsolutelyContinuous.rfl

Depends on / 依赖: AbsolutelyContinuous, AbsolutelyContinuous.zero, h.symm, measure_univ_eq_zero, measure_univ_eq_zero.mp
-/
lemma absolutelyContinuous_zero_iff : μ ≪ 0 ↔ μ = 0 :=
  ⟨fun h => measure_univ_eq_zero.mp (h rfl), fun h => h.symm ▸ AbsolutelyContinuous.zero _⟩

alias absolutelyContinuous_refl := AbsolutelyContinuous.refl
alias absolutelyContinuous_rfl := AbsolutelyContinuous.rfl

/--
lemma `absolutelyContinuous_sum_left` / 引理 `absolutelyContinuous_sum_left`

English:
lemma absolutelyContinuous_sum_left
  given: {μs : ι -> Measure α} (hμs : forall i, μs i ≪ ν)
  proof: AbsolutelyContinuous.mk fun s hs hs0 => by simp [sum_apply _ hs, fun i => hμs i hs0]

中文:
引理 absolutelyContinuous_sum_left
  条件: {μs : ι -> 测度 α} (hμs : 对任意 i, μs i ≪ ν)
  证明: AbsolutelyContinuous.mk fun s hs hs0 => by simp [sum_apply _ hs, fun i => hμs i hs0]

Depends on / 依赖: AbsolutelyContinuous, AbsolutelyContinuous.mk, sum_apply
-/
lemma absolutelyContinuous_sum_left {μs : ι -> Measure α} (hμs : forall i, μs i ≪ ν) :
    Measure.sum μs ≪ ν :=
  AbsolutelyContinuous.mk fun s hs hs0 => by simp [sum_apply _ hs, fun i => hμs i hs0]

/--
lemma `absolutelyContinuous_sum_right` / 引理 `absolutelyContinuous_sum_right`

English:
lemma absolutelyContinuous_sum_right
  given: {μs : ι -> Measure α} (i : ι) (hνμ : ν ≪ μs i)
  proof: by
  refine AbsolutelyContinuous.mk fun s hs hs0 => ?_
  simp only [sum_apply _ hs, ENNReal.tsum_eq_zero] at hs0
  exact hνμ (hs0 i)

中文:
引理 absolutelyContinuous_sum_right
  条件: {μs : ι -> 测度 α} (i : ι) (hνμ : ν ≪ μs i)
  证明: by
  refine AbsolutelyContinuous.mk fun s hs hs0 => ?_
  simp only [sum_apply _ hs, ENNReal.tsum_eq_zero] at hs0
  exact hνμ (hs0 i)

Depends on / 依赖: AbsolutelyContinuous, AbsolutelyContinuous.mk, ENNReal, ENNReal.tsum_eq_zero, sum_apply, tsum_eq_zero
-/
lemma absolutelyContinuous_sum_right {μs : ι -> Measure α} (i : ι) (hνμ : ν ≪ μs i) :
    ν ≪ Measure.sum μs := by
  refine AbsolutelyContinuous.mk fun s hs hs0 => ?_
  simp only [sum_apply _ hs, ENNReal.tsum_eq_zero] at hs0
  exact hνμ (hs0 i)

/--
lemma `smul_absolutelyContinuous` / 引理 `smul_absolutelyContinuous`

English:
lemma smul_absolutelyContinuous
  given: {c : Real>=0∞}
  statement: c • μ ≪ μ
  proof: .smul_left .rfl _

中文:
引理 smul_absolutelyContinuous
  条件: {c : 实数>=0∞}
  结论: c • μ ≪ μ
  证明: .smul_left .rfl _

Depends on / 依赖: smul_left
-/
lemma smul_absolutelyContinuous {c : Real>=0∞} : c • μ ≪ μ := .smul_left .rfl _

/--
theorem `absolutelyContinuous_of_le_smul` / 定理 `absolutelyContinuous_of_le_smul`

English:
theorem absolutelyContinuous_of_le_smul
  given: {μ' : Measure α} {c : Real>=0∞} (hμ'_le : μ' <= c • μ)
  proof: (Measure.absolutelyContinuous_of_le hμ'_le).trans smul_absolutelyContinuous

中文:
定理 absolutelyContinuous_of_le_smul
  条件: {μ' : 测度 α} {c : 实数>=0∞} (hμ'_le : μ' <= c • μ)
  证明: (Measure.absolutelyContinuous_of_le hμ'_le).trans smul_absolutelyContinuous

Depends on / 依赖: Measure, Measure.absolutelyContinuous_of_le, absolutelyContinuous_of_le, smul_absolutelyContinuous
-/
theorem absolutelyContinuous_of_le_smul {μ' : Measure α} {c : Real>=0∞} (hμ'_le : μ' <= c • μ) :
    μ' ≪ μ :=
  (Measure.absolutelyContinuous_of_le hμ'_le).trans smul_absolutelyContinuous

/--
lemma `absolutelyContinuous_smul` / 引理 `absolutelyContinuous_smul`

English:
lemma absolutelyContinuous_smul
  given: {c : Real>=0∞} (hc : c != 0)
  statement: μ ≪ c • μ
  proof: by
  simp [AbsolutelyContinuous, hc]

中文:
引理 absolutelyContinuous_smul
  条件: {c : 实数>=0∞} (hc : c != 0)
  结论: μ ≪ c • μ
  证明: by
  simp [AbsolutelyContinuous, hc]

Depends on / 依赖: AbsolutelyContinuous
-/
lemma absolutelyContinuous_smul {c : Real>=0∞} (hc : c != 0) : μ ≪ c • μ := by
  simp [AbsolutelyContinuous, hc]

/--
lemma `AbsolutelyContinuous.smul_right` / 引理 `AbsolutelyContinuous.smul_right`

English:
lemma AbsolutelyContinuous.smul_right
  given: (hμν : μ ≪ ν) {c : Real>=0∞} (hc : c != 0)
  statement: μ ≪ c • ν
  proof: (absolutelyContinuous_smul hc).trans (hμν.smul c)

中文:
引理 AbsolutelyContinuous.smul_right
  条件: (hμν : μ ≪ ν) {c : 实数>=0∞} (hc : c != 0)
  结论: μ ≪ c • ν
  证明: (absolutelyContinuous_smul hc).trans (hμν.smul c)

Depends on / 依赖: absolutelyContinuous_smul
-/
lemma AbsolutelyContinuous.smul_right (hμν : μ ≪ ν) {c : Real>=0∞} (hc : c != 0) : μ ≪ c • ν :=
  (absolutelyContinuous_smul hc).trans (hμν.smul c)

/--
theorem `ae_le_iff_absolutelyContinuous` / 定理 `ae_le_iff_absolutelyContinuous`

English:
theorem ae_le_iff_absolutelyContinuous
  statement: ae μ <= ae ν ↔ μ ≪ ν
  proof: ⟨fun h s => by
    rw [measure_eq_zero_iff_ae_notMem]; rw [measure_eq_zero_iff_ae_notMem]
    exact fun hs => h hs, fun h _ hs => h hs⟩

alias ⟨_root_.LE.le.absolutelyContinuous_of_ae, AbsolutelyContinuous.ae_le⟩ :=
  ae_le_iff_absolutelyContinuous

alias ae_mono' := AbsolutelyContinuous.ae_le

中文:
定理 ae_le_iff_absolutelyContinuous
  结论: ae μ <= ae ν ↔ μ ≪ ν
  证明: ⟨fun h s => by
    rw [measure_eq_zero_iff_ae_notMem]; rw [measure_eq_zero_iff_ae_notMem]
    exact fun hs => h hs, fun h _ hs => h hs⟩

alias ⟨_root_.LE.le.absolutelyContinuous_of_ae, AbsolutelyContinuous.ae_le⟩ :=
  ae_le_iff_absolutelyContinuous

alias ae_mono' := AbsolutelyContinuous.ae_le

Depends on / 依赖: measure_eq_zero_iff_ae_notMem
-/
theorem ae_le_iff_absolutelyContinuous : ae μ <= ae ν ↔ μ ≪ ν :=
  ⟨fun h s => by
    rw [measure_eq_zero_iff_ae_notMem]; rw [measure_eq_zero_iff_ae_notMem]
    exact fun hs => h hs, fun h _ hs => h hs⟩

alias ⟨_root_.LE.le.absolutelyContinuous_of_ae, AbsolutelyContinuous.ae_le⟩ :=
  ae_le_iff_absolutelyContinuous

alias ae_mono' := AbsolutelyContinuous.ae_le

/--
theorem `AbsolutelyContinuous.ae_eq` / 定理 `AbsolutelyContinuous.ae_eq`

English:
theorem AbsolutelyContinuous.ae_eq
  given: (h : μ ≪ ν) {f g : α -> δ} (h' : f =ᵐ[ν] g)
  statement: f =ᵐ[μ] g
  proof: h.ae_le h'

中文:
定理 AbsolutelyContinuous.ae_eq
  条件: (h : μ ≪ ν) {f g : α -> δ} (h' : f =ᵐ[ν] g)
  结论: f =ᵐ[μ] g
  证明: h.ae_le h'

Depends on / 依赖: ae_le, h.ae_le
-/
theorem AbsolutelyContinuous.ae_eq (h : μ ≪ ν) {f g : α -> δ} (h' : f =ᵐ[ν] g) : f =ᵐ[μ] g :=
  h.ae_le h'

end Measure

/--
theorem `AEDisjoint.of_absolutelyContinuous` / 定理 `AEDisjoint.of_absolutelyContinuous`

English:
theorem AEDisjoint.of_absolutelyContinuous
  proof: h' h

中文:
定理 AEDisjoint.of_absolutelyContinuous
  证明: h' h
-/
protected theorem AEDisjoint.of_absolutelyContinuous
    (h : AEDisjoint μ s t) {ν : Measure α} (h' : ν ≪ μ) :
    AEDisjoint ν s t := h' h

/--
theorem `AEDisjoint.of_le` / 定理 `AEDisjoint.of_le`

English:
theorem AEDisjoint.of_le
  proof: h.of_absolutelyContinuous (Measure.absolutelyContinuous_of_le h')

@[gcongr, mono]

中文:
定理 AEDisjoint.of_le
  证明: h.of_absolutelyContinuous (Measure.absolutelyContinuous_of_le h')

@[gcongr, mono]
-/
protected theorem AEDisjoint.of_le
    (h : AEDisjoint μ s t) {ν : Measure α} (h' : ν <= μ) :
    AEDisjoint ν s t :=
  h.of_absolutelyContinuous (Measure.absolutelyContinuous_of_le h')

@[gcongr, mono]
/--
theorem `ae_mono` / 定理 `ae_mono`

English:
theorem ae_mono
  given: (h : μ <= ν)
  statement: ae μ <= ae ν
  proof: h.absolutelyContinuous.ae_le

中文:
定理 ae_mono
  条件: (h : μ <= ν)
  结论: ae μ <= ae ν
  证明: h.absolutelyContinuous.ae_le

Depends on / 依赖: absolutelyContinuous, ae_le, h.absolutelyContinuous.ae_le
-/
theorem ae_mono (h : μ <= ν) : ae μ <= ae ν :=
  h.absolutelyContinuous.ae_le

end MeasureTheory

namespace MeasurableEmbedding

open MeasureTheory Measure

variable {m0 : MeasurableSpace α} {m1 : MeasurableSpace β} {f : α -> β} {μ ν : Measure α}

/--
lemma `absolutelyContinuous_map` / 引理 `absolutelyContinuous_map`

English:
lemma absolutelyContinuous_map
  given: (hf : MeasurableEmbedding f) (hμν : μ ≪ ν)
  proof: by
  intro t ht
  rw [hf.map_apply] at ht ⊢
  exact hμν ht

中文:
引理 absolutelyContinuous_map
  条件: (hf : 可测嵌入 f) (hμν : μ ≪ ν)
  证明: by
  intro t ht
  rw [hf.map_apply] at ht ⊢
  exact hμν ht

Depends on / 依赖: hf.map_apply, map_apply
-/
lemma absolutelyContinuous_map (hf : MeasurableEmbedding f) (hμν : μ ≪ ν) :
    μ.map f ≪ ν.map f := by
  intro t ht
  rw [hf.map_apply] at ht ⊢
  exact hμν ht

end MeasurableEmbedding
