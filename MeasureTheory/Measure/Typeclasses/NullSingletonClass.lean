/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.Topology.DiscreteSubset

/-!
# Measures having value zero on singletons

## TODO

Add a `NoAtoms` class defined as
`∀ s, MeasurableSet s → 0 < μ s → ∃ t ⊆ s, MeasurableSet t ∧ 0 < μ t ∧ μ t < μ s`.
This implies `NullSingletonClass` but the converse is not true.
-/

public section

namespace MeasureTheory

open Set Measure Filter TopologicalSpace

variable {α : Type*} {m0 : MeasurableSpace α} {μ : Measure α} {s : Set α}

/-- Measure `μ` has value zero on singletons. -/
/-
**MeasureTheory.NullSingletonClass** 是 Mathlib 中的一个归纳类型，位于命名空间 `MeasureTheory`。
形式化陈述：{α : Type u_1} → {m0 : MeasurableSpace α} → MeasureTheory.Measure α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Measure `μ` has value zero on singletons.
-/
class NullSingletonClass {m0 : MeasurableSpace α} (μ : Measure α) : Prop where
  measure_singleton : ∀ x, μ {x} = 0

@[deprecated (since := "2026-06-09")]
alias NoAtoms := NullSingletonClass

export MeasureTheory.NullSingletonClass (measure_singleton)

attribute [simp] measure_singleton

variable [NullSingletonClass μ]
/-
**MeasureTheory._root_.Set.Subsingleton.measure_zero** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Set.Subsingleton.measure_zero (hs : s.Subsingleton) (μ : Measure α)
    [NullSingletonClass μ] :
    μ s = 0 :=
  hs.induction_on (p := fun s => μ s = 0) measure_empty measure_singleton
/-
**MeasureTheory.Measure.restrict_singleton'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Measure`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [M
easureTheory.NullSingletonClass μ] {a : α},   μ.restrict {a} = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.NullSingletonClass.measure_singleton`：∀ {α : Type u_1} {m0
 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.NullSi
ngletonClass μ]   (x : α), μ {x} = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Measure.restrict_singleton' {a : α} : μ.restrict {a} = 0 := by
  simp only [measure_singleton, Measure.restrict_eq_zero]
/-
**MeasureTheory.Measure.restrict.instNullSingletonClass** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.Measure.restrict`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [M
easureTheory.NullSingletonClass μ]   (s : Set α), MeasureTheory.NullSingletonCla
ss (μ.restrict s)
参数：s : Set α；μ.restrict s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.exists_measurable_superset_of_null`：exists_measurable_supe
rset_of_null (h : μ s = 0) : exists t, s subseteq t ∧ MeasurableSet t ∧ μ t = 0
· 使用定理 `MeasureTheory.NullSingletonClass.measure_singleton`：∀ {α : Type u_1} {m0
 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.NullSi
ngletonClass μ]   (x : α), μ {x} = 0
· 使用定理 `MeasureTheory.measure_mono_null`：measure_mono_null (h : s subseteq t) (h
t : μ t = 0) : μ s = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
-/
instance Measure.restrict.instNullSingletonClass (s : Set α) :
    NullSingletonClass (μ.restrict s) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨t, hxt, ht1, ht2⟩ := exists_measurable_superset_of_null (measure_singleton x : μ {x} = 0)
  apply measure_mono_null hxt
  rw [Measure.restrict_apply ht1]
  apply measure_mono_null inter_subset_left ht2
/-
**MeasureTheory._root_.Set.Countable.measure_zero** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Set.Countable.measure_zero (h : s.Countable) (μ : Measure α) [NullSingletonClass μ] :
    μ s = 0 := by
  rw [← biUnion_of_singleton s, measure_biUnion_null_iff h]
  simp
/-
**MeasureTheory._root_.Set.Countable.ae_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Set.Countable.ae_notMem (h : s.Countable) (μ : Measure α) [NullSingletonClass μ] :
    ∀ᵐ x ∂μ, x ∉ s := by
  simpa only [ae_iff, Classical.not_not] using! h.measure_zero μ
/-
**MeasureTheory.Measure.ae_ne** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α) [M
easureTheory.NullSingletonClass μ] (a : α),   ∀ᵐ (x : α) ∂μ, x ≠ a
参数：μ : MeasureTheory.Measure α；a : α；x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Countable.ae_notMem`：∀ {α : Type u_1} {m0 : MeasurableSpace α} {s : 
Set α},   s.Countable → ∀ (μ : MeasureTheory.Measure α) [MeasureTheory.NullSingl
etonClass μ],…
· 使用定理 `Set.countable_singleton`：∀ {α : Type u} (a : α), {a}.Countable
-/
lemma Measure.ae_ne (μ : Measure α) [NullSingletonClass μ] (a : α) : ∀ᵐ x ∂μ, x ≠ a :=
  (countable_singleton a).ae_notMem μ
/-
**MeasureTheory._root_.Set.Countable.measure_restrict_compl** 是 Mathlib 中的一个引理，位
于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Set.Countable.measure_restrict_compl (h : s.Countable) (μ : Measure α)
    [NullSingletonClass μ] :
    μ.restrict sᶜ = μ :=
  restrict_eq_self_of_ae_mem <| h.ae_notMem μ

@[simp]
/-
**MeasureTheory.restrict_compl_singleton** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheor
y`。
形式化陈述：restrict_compl_singleton (a : α) : μ.restrict ({a}ᶜ) = μ
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Countable.measure_restrict_compl`：∀ {α : Type u_1} {m0 : MeasurableS
pace α} {s : Set α},   s.Countable → ∀ (μ : MeasureTheory.Measure α) [MeasureThe
ory.NullSingletonClass μ],…
· 使用定理 `Set.countable_singleton`：∀ {α : Type u} (a : α), {a}.Countable
-/
lemma restrict_compl_singleton (a : α) : μ.restrict ({a}ᶜ) = μ :=
  (countable_singleton _).measure_restrict_compl μ
/-
**MeasureTheory._root_.Set.Finite.measure_zero** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Set.Finite.measure_zero (h : s.Finite) (μ : Measure α) [NullSingletonClass μ] :
    μ s = 0 :=
  h.countable.measure_zero μ
/-
**MeasureTheory._root_.Finset.measure_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Finset.measure_zero (s : Finset α) (μ : Measure α) [NullSingletonClass μ] :
    μ s = 0 :=
  s.finite_toSet.measure_zero μ
/-
**MeasureTheory.insert_ae_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：insert_ae_eq_self (a : α) (s : Set α) : (insert a s : Set α) =ᵐ[μ] s
参数：a : α；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.union_ae_eq_right`：union_ae_eq_right : (s union t : Set α)
 =ᵐ[μ] t ↔ μ (s \ t) = 0
· 使用定理 `MeasureTheory.measure_mono_null`：measure_mono_null (h : s subseteq t) (h
t : μ t = 0) : μ s = 0
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `MeasureTheory.NullSingletonClass.measure_singleton`：∀ {α : Type u_1} {m0
 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.NullSi
ngletonClass μ]   (x : α), μ {x} = 0
-/
theorem insert_ae_eq_self (a : α) (s : Set α) : (insert a s : Set α) =ᵐ[μ] s :=
  union_ae_eq_right.2 <| measure_mono_null sdiff_subset (measure_singleton _)

/-
If a set has positive measure under an atomless measure, then it has an accumulation point.
-/
/-
**MeasureTheory.exists_accPt_of_nullSingletonClass** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory`。
形式化陈述：exists_accPt_of_nullSingletonClass {X : Type*} [TopologicalSpace X] [Measu
rableSpace X] {μ : Measure X} [NullSingletonClass μ] {E : Set X} [SeparableSpace
 E] (hE : 0 < μ E) : exists x, AccPt x (𝓟 E)
参数：hE : 0 < μ E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用引理 `discreteTopology_of_noAccPts`：discreteTopology_of_noAccPts {X : Type*} [
TopologicalSpace X] {E : Set X} (h : forall x in E, ¬ AccPt x (𝓟 E)) : DiscreteT
opology E
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Set.Countable.measure_zero`：∀ {α : Type u_1} {m0 : MeasurableSpace α} {s
 : Set α},   s.Countable → ∀ (μ : MeasureTheory.Measure α) [MeasureTheory.NullSi
ngletonClass μ],…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.countable_coe_iff`：countable_coe_iff {s : Set α} : Countable s ↔ s.C
ountable
· 使用定理 `TopologicalSpace.separableSpace_iff_countable`：separableSpace_iff_counta
ble [DiscreteTopology α] : SeparableSpace α ↔ Countable α

--- 原说明 ---
If a set has positive measure under an atomless measure, then it has an accumula
tion point.
-/
theorem exists_accPt_of_nullSingletonClass {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    {μ : Measure X} [NullSingletonClass μ] {E : Set X} [SeparableSpace E] (hE : 0 < μ E) :
    ∃ x, AccPt x (𝓟 E) := by
  by_contra! h
  have : DiscreteTopology E := discreteTopology_of_noAccPts fun x _ => h x
  exact hE.ne' <| (Set.countable_coe_iff.mp <| separableSpace_iff_countable.mp ‹_›).measure_zero μ

@[deprecated (since := "2026-06-09")]
alias exists_accPt_of_noAtoms := exists_accPt_of_nullSingletonClass

section

variable [PartialOrder α] {a b : α}

/-
**MeasureTheory.Iio_ae_eq_Iic** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：Iio_ae_eq_Iic : Iio a =ᵐ[μ] Iic a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Iio_ae_eq_Iic'`：Iio_ae_eq_Iic' (ha : μ {a} = 0) : Iio a =ᵐ
[μ] Iic a
· 使用定理 `MeasureTheory.NullSingletonClass.measure_singleton`：∀ {α : Type u_1} {m0
 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.NullSi
ngletonClass μ]   (x : α), μ {x} = 0
-/
theorem Iio_ae_eq_Iic : Iio a =ᵐ[μ] Iic a :=
  Iio_ae_eq_Iic' (measure_singleton a)
/-
**MeasureTheory.Ioi_ae_eq_Ici** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：Ioi_ae_eq_Ici : Ioi a =ᵐ[μ] Ici a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Ioi_ae_eq_Ici'`：Ioi_ae_eq_Ici' (ha : μ {a} = 0) : Ioi a =ᵐ
[μ] Ici a
· 使用定理 `MeasureTheory.NullSingletonClass.measure_singleton`：∀ {α : Type u_1} {m0
 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.NullSi
ngletonClass μ]   (x : α), μ {x} = 0
-/
theorem Ioi_ae_eq_Ici : Ioi a =ᵐ[μ] Ici a :=
  Ioi_ae_eq_Ici' (measure_singleton a)
/-
**MeasureTheory.Ioo_ae_eq_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：Ioo_ae_eq_Ioc : Ioo a b =ᵐ[μ] Ioc a b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Ioo_ae_eq_Ioc'`：Ioo_ae_eq_Ioc' (hb : μ {b} = 0) : Ioo a b 
=ᵐ[μ] Ioc a b
· 使用定理 `MeasureTheory.NullSingletonClass.measure_singleton`：∀ {α : Type u_1} {m0
 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.NullSi
ngletonClass μ]   (x : α), μ {x} = 0
-/
theorem Ioo_ae_eq_Ioc : Ioo a b =ᵐ[μ] Ioc a b :=
  Ioo_ae_eq_Ioc' (measure_singleton b)
/-
**MeasureTheory.Ioc_ae_eq_Icc** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：Ioc_ae_eq_Icc : Ioc a b =ᵐ[μ] Icc a b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Ioc_ae_eq_Icc'`：Ioc_ae_eq_Icc' (ha : μ {a} = 0) : Ioc a b 
=ᵐ[μ] Icc a b
· 使用定理 `MeasureTheory.NullSingletonClass.measure_singleton`：∀ {α : Type u_1} {m0
 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.NullSi
ngletonClass μ]   (x : α), μ {x} = 0
-/
theorem Ioc_ae_eq_Icc : Ioc a b =ᵐ[μ] Icc a b :=
  Ioc_ae_eq_Icc' (measure_singleton a)
/-
**MeasureTheory.Ioo_ae_eq_Ico** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：Ioo_ae_eq_Ico : Ioo a b =ᵐ[μ] Ico a b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Ioo_ae_eq_Ico'`：Ioo_ae_eq_Ico' (ha : μ {a} = 0) : Ioo a b 
=ᵐ[μ] Ico a b
· 使用定理 `MeasureTheory.NullSingletonClass.measure_singleton`：∀ {α : Type u_1} {m0
 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.NullSi
ngletonClass μ]   (x : α), μ {x} = 0
-/
theorem Ioo_ae_eq_Ico : Ioo a b =ᵐ[μ] Ico a b :=
  Ioo_ae_eq_Ico' (measure_singleton a)
/-
**MeasureTheory.Ioo_ae_eq_Icc** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：Ioo_ae_eq_Icc : Ioo a b =ᵐ[μ] Icc a b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Ioo_ae_eq_Icc'`：Ioo_ae_eq_Icc' (ha : μ {a} = 0) (hb : μ {b
} = 0) : Ioo a b =ᵐ[μ] Icc a b
· 使用定理 `MeasureTheory.NullSingletonClass.measure_singleton`：∀ {α : Type u_1} {m0
 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.NullSi
ngletonClass μ]   (x : α), μ {x} = 0
-/
theorem Ioo_ae_eq_Icc : Ioo a b =ᵐ[μ] Icc a b :=
  Ioo_ae_eq_Icc' (measure_singleton a) (measure_singleton b)
/-
**MeasureTheory.Ico_ae_eq_Icc** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：Ico_ae_eq_Icc : Ico a b =ᵐ[μ] Icc a b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Ico_ae_eq_Icc'`：Ico_ae_eq_Icc' (hb : μ {b} = 0) : Ico a b 
=ᵐ[μ] Icc a b
· 使用定理 `MeasureTheory.NullSingletonClass.measure_singleton`：∀ {α : Type u_1} {m0
 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.NullSi
ngletonClass μ]   (x : α), μ {x} = 0
-/
theorem Ico_ae_eq_Icc : Ico a b =ᵐ[μ] Icc a b :=
  Ico_ae_eq_Icc' (measure_singleton b)
/-
**MeasureTheory.Ico_ae_eq_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：Ico_ae_eq_Ioc : Ico a b =ᵐ[μ] Ioc a b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Ico_ae_eq_Ioc'`：Ico_ae_eq_Ioc' (ha : μ {a} = 0) (hb : μ {b
} = 0) : Ico a b =ᵐ[μ] Ioc a b
· 使用定理 `MeasureTheory.NullSingletonClass.measure_singleton`：∀ {α : Type u_1} {m0
 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.NullSi
ngletonClass μ]   (x : α), μ {x} = 0
-/
theorem Ico_ae_eq_Ioc : Ico a b =ᵐ[μ] Ioc a b :=
  Ico_ae_eq_Ioc' (measure_singleton a) (measure_singleton b)
/-
**MeasureTheory.restrict_Iio_eq_restrict_Iic** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：restrict_Iio_eq_restrict_Iic : μ.restrict (Iio a) = μ.restrict (Iic a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.restrict_congr_set`：restrict_congr_set (h : s =ᵐ[μ
] t) : μ.restrict s = μ.restrict t
· 使用定理 `MeasureTheory.Iio_ae_eq_Iic`：Iio_ae_eq_Iic : Iio a =ᵐ[μ] Iic a
-/
theorem restrict_Iio_eq_restrict_Iic : μ.restrict (Iio a) = μ.restrict (Iic a) :=
  restrict_congr_set Iio_ae_eq_Iic
/-
**MeasureTheory.restrict_Ioi_eq_restrict_Ici** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：restrict_Ioi_eq_restrict_Ici : μ.restrict (Ioi a) = μ.restrict (Ici a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.restrict_congr_set`：restrict_congr_set (h : s =ᵐ[μ
] t) : μ.restrict s = μ.restrict t
· 使用定理 `MeasureTheory.Ioi_ae_eq_Ici`：Ioi_ae_eq_Ici : Ioi a =ᵐ[μ] Ici a
-/
theorem restrict_Ioi_eq_restrict_Ici : μ.restrict (Ioi a) = μ.restrict (Ici a) :=
  restrict_congr_set Ioi_ae_eq_Ici
/-
**MeasureTheory.restrict_Ioo_eq_restrict_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：restrict_Ioo_eq_restrict_Ioc : μ.restrict (Ioo a b) = μ.restrict (Ioc a b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.restrict_congr_set`：restrict_congr_set (h : s =ᵐ[μ
] t) : μ.restrict s = μ.restrict t
· 使用定理 `MeasureTheory.Ioo_ae_eq_Ioc`：Ioo_ae_eq_Ioc : Ioo a b =ᵐ[μ] Ioc a b
-/
theorem restrict_Ioo_eq_restrict_Ioc : μ.restrict (Ioo a b) = μ.restrict (Ioc a b) :=
  restrict_congr_set Ioo_ae_eq_Ioc
/-
**MeasureTheory.restrict_Ioc_eq_restrict_Icc** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：restrict_Ioc_eq_restrict_Icc : μ.restrict (Ioc a b) = μ.restrict (Icc a b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.restrict_congr_set`：restrict_congr_set (h : s =ᵐ[μ
] t) : μ.restrict s = μ.restrict t
· 使用定理 `MeasureTheory.Ioc_ae_eq_Icc`：Ioc_ae_eq_Icc : Ioc a b =ᵐ[μ] Icc a b
-/
theorem restrict_Ioc_eq_restrict_Icc : μ.restrict (Ioc a b) = μ.restrict (Icc a b) :=
  restrict_congr_set Ioc_ae_eq_Icc
/-
**MeasureTheory.restrict_Ioo_eq_restrict_Ico** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：restrict_Ioo_eq_restrict_Ico : μ.restrict (Ioo a b) = μ.restrict (Ico a b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.restrict_congr_set`：restrict_congr_set (h : s =ᵐ[μ
] t) : μ.restrict s = μ.restrict t
· 使用定理 `MeasureTheory.Ioo_ae_eq_Ico`：Ioo_ae_eq_Ico : Ioo a b =ᵐ[μ] Ico a b
-/
theorem restrict_Ioo_eq_restrict_Ico : μ.restrict (Ioo a b) = μ.restrict (Ico a b) :=
  restrict_congr_set Ioo_ae_eq_Ico
/-
**MeasureTheory.restrict_Ioo_eq_restrict_Icc** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：restrict_Ioo_eq_restrict_Icc : μ.restrict (Ioo a b) = μ.restrict (Icc a b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.restrict_congr_set`：restrict_congr_set (h : s =ᵐ[μ
] t) : μ.restrict s = μ.restrict t
· 使用定理 `MeasureTheory.Ioo_ae_eq_Icc`：Ioo_ae_eq_Icc : Ioo a b =ᵐ[μ] Icc a b
-/
theorem restrict_Ioo_eq_restrict_Icc : μ.restrict (Ioo a b) = μ.restrict (Icc a b) :=
  restrict_congr_set Ioo_ae_eq_Icc
/-
**MeasureTheory.restrict_Ico_eq_restrict_Icc** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：restrict_Ico_eq_restrict_Icc : μ.restrict (Ico a b) = μ.restrict (Icc a b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.restrict_congr_set`：restrict_congr_set (h : s =ᵐ[μ
] t) : μ.restrict s = μ.restrict t
· 使用定理 `MeasureTheory.Ico_ae_eq_Icc`：Ico_ae_eq_Icc : Ico a b =ᵐ[μ] Icc a b
-/
theorem restrict_Ico_eq_restrict_Icc : μ.restrict (Ico a b) = μ.restrict (Icc a b) :=
  restrict_congr_set Ico_ae_eq_Icc
/-
**MeasureTheory.restrict_Ico_eq_restrict_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：restrict_Ico_eq_restrict_Ioc : μ.restrict (Ico a b) = μ.restrict (Ioc a b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.restrict_congr_set`：restrict_congr_set (h : s =ᵐ[μ
] t) : μ.restrict s = μ.restrict t
· 使用定理 `MeasureTheory.Ico_ae_eq_Ioc`：Ico_ae_eq_Ioc : Ico a b =ᵐ[μ] Ioc a b
-/
theorem restrict_Ico_eq_restrict_Ioc : μ.restrict (Ico a b) = μ.restrict (Ioc a b) :=
  restrict_congr_set Ico_ae_eq_Ioc

end

open Interval

open scoped Interval in
/-
**MeasureTheory.uIoc_ae_eq_interval** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：uIoc_ae_eq_interval [LinearOrder α] {a b : α} : Ι a b =ᵐ[μ] [[a, b]]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Ioc_ae_eq_Icc`：Ioc_ae_eq_Icc : Ioc a b =ᵐ[μ] Icc a b
-/
theorem uIoc_ae_eq_interval [LinearOrder α] {a b : α} : Ι a b =ᵐ[μ] [[a, b]] :=
  Ioc_ae_eq_Icc

end MeasureTheory

