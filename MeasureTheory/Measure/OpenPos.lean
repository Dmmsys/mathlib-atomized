/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Measures positive on nonempty opens

In this file we define a typeclass for measures that are positive on nonempty opens, see
`MeasureTheory.Measure.IsOpenPosMeasure`. Examples include (additive) Haar measures, as well as
measures that have positive density with respect to a Haar measure. We also prove some basic facts
about these measures.

-/

public section


open Topology ENNReal MeasureTheory

open Set Function Filter

namespace MeasureTheory

namespace Measure

section Basic

variable {X Y : Type*} [TopologicalSpace X] {m : MeasurableSpace X} [TopologicalSpace Y]
  [T2Space Y] (μ ν : Measure X)

/-- A measure is said to be `IsOpenPosMeasure` if it is positive on nonempty open sets. -/
/-
**MeasureTheory.Measure.IsOpenPosMeasure** 是 Mathlib 中的一个归纳类型，位于命名空间 `MeasureThe
ory.Measure`。
形式化陈述：{X : Type u_1} → [TopologicalSpace X] → {m : MeasurableSpace X} → MeasureT
heory.Measure X → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A measure is said to be `IsOpenPosMeasure` if it is positive on nonempty open se
ts.
-/
class IsOpenPosMeasure : Prop where
  open_pos : ∀ U : Set X, IsOpen U → U.Nonempty → μ U ≠ 0

variable [IsOpenPosMeasure μ] {s U F : Set X} {x : X}
/-
**MeasureTheory.Measure._root_.IsOpen.measure_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsOpen.measure_ne_zero (hU : IsOpen U) (hne : U.Nonempty) : μ U ≠ 0 :=
  IsOpenPosMeasure.open_pos U hU hne
/-
**MeasureTheory.Measure._root_.IsOpen.measure_pos** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsOpen.measure_pos (hU : IsOpen U) (hne : U.Nonempty) : 0 < μ U :=
  (hU.measure_ne_zero μ hne).bot_lt
/-
**MeasureTheory.Measure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) [Nonempty X] : NeZero μ :=
  ⟨measure_univ_pos.mp <| isOpen_univ.measure_pos μ univ_nonempty⟩
/-
**MeasureTheory.Measure._root_.IsOpen.measure_pos_iff** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsOpen.measure_pos_iff (hU : IsOpen U) : 0 < μ U ↔ U.Nonempty :=
  ⟨fun h => nonempty_iff_ne_empty.2 fun he => h.ne' <| he.symm ▸ measure_empty, hU.measure_pos μ⟩
/-
**MeasureTheory.Measure._root_.IsOpen.measure_eq_zero_iff** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsOpen.measure_eq_zero_iff (hU : IsOpen U) : μ U = 0 ↔ U = ∅ := by
  simpa only [not_lt, nonpos_iff_eq_zero, not_nonempty_iff_eq_empty] using
    not_congr (hU.measure_pos_iff μ)
/-
**MeasureTheory.Measure.measure_pos_of_nonempty_interior** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.Measure`。
形式化陈述：measure_pos_of_nonempty_interior (h : (interior s).Nonempty) : 0 < μ s
参数：h : (interior s).Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `IsOpen.measure_pos`：∀ {X : Type u_1} [inst : TopologicalSpace X] {m : Me
asurableSpace X} (μ : MeasureTheory.Measure X) [μ.IsOpenPosMeasure]   {U : Set X
}, IsOpe…
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
-/
theorem measure_pos_of_nonempty_interior (h : (interior s).Nonempty) : 0 < μ s :=
  (isOpen_interior.measure_pos μ h).trans_le (measure_mono interior_subset)
/-
**MeasureTheory.Measure.measure_pos_of_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.Measure`。
形式化陈述：measure_pos_of_mem_nhds (h : s in 𝓝 x) : 0 < μ s
参数：h : s in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.measure_pos_of_nonempty_interior`：measure_pos_of_n
onempty_interior (h : (interior s).Nonempty) : 0 < μ s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_interior_iff_mem_nhds`：mem_interior_iff_mem_nhds : x in interior s ↔
 s in 𝓝 x
-/
theorem measure_pos_of_mem_nhds (h : s ∈ 𝓝 x) : 0 < μ s :=
  measure_pos_of_nonempty_interior _ ⟨x, mem_interior_iff_mem_nhds.2 h⟩
/-
**MeasureTheory.Measure.isOpenPosMeasure_smul** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.Measure`。
形式化陈述：isOpenPosMeasure_smul {c : Real>=0∞} (h : c != 0) : IsOpenPosMeasure (c • 
μ)
参数：h : c != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `ENNReal.instNoZeroDivisors`：NoZeroDivisors ENNReal
· 使用定理 `IsOpen.measure_ne_zero`：∀ {X : Type u_1} [inst : TopologicalSpace X] {m 
: MeasurableSpace X} (μ : MeasureTheory.Measure X) [μ.IsOpenPosMeasure]   {U : S
et X}, IsOpe…
-/
theorem isOpenPosMeasure_smul {c : ℝ≥0∞} (h : c ≠ 0) : IsOpenPosMeasure (c • μ) :=
  ⟨fun _U Uo Une => mul_ne_zero h (Uo.measure_ne_zero μ Une)⟩

variable {μ ν}
/-
**MeasureTheory.Measure.AbsolutelyContinuous.isOpenPosMeasure** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory.Measure.AbsolutelyContinuous`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] {m : MeasurableSpace X} {μ ν 
: MeasureTheory.Measure X}   [μ.IsOpenPosMeasure], μ.AbsolutelyContinuous ν → ν.
IsOpenPosMeasure
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.measure_ne_zero`：∀ {X : Type u_1} [inst : TopologicalSpace X] {m 
: MeasurableSpace X} (μ : MeasureTheory.Measure X) [μ.IsOpenPosMeasure]   {U : S
et X}, IsOpe…
-/
protected theorem AbsolutelyContinuous.isOpenPosMeasure (h : μ ≪ ν) : IsOpenPosMeasure ν :=
  ⟨fun _U ho hne h₀ => ho.measure_ne_zero μ hne (h h₀)⟩
/-
**MeasureTheory.Measure._root_.LE.le.isOpenPosMeasure** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.LE.le.isOpenPosMeasure (h : μ ≤ ν) : IsOpenPosMeasure ν :=
  h.absolutelyContinuous.isOpenPosMeasure
/-
**MeasureTheory.Measure._root_.IsOpen.measure_zero_iff_eq_empty** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsOpen.measure_zero_iff_eq_empty (hU : IsOpen U) :
    μ U = 0 ↔ U = ∅ :=
  ⟨fun h ↦ (hU.measure_eq_zero_iff μ).mp h, fun h ↦ by simp [h]⟩
/-
**MeasureTheory.Measure._root_.IsOpen.ae_eq_empty_iff_eq** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsOpen.ae_eq_empty_iff_eq (hU : IsOpen U) :
    U =ᵐ[μ] (∅ : Set X) ↔ U = ∅ := by
  rw [ae_eq_empty, hU.measure_zero_iff_eq_empty]

/-- An open null set w.r.t. an `IsOpenPosMeasure` is empty. -/
/-
**MeasureTheory.Measure._root_.IsOpen.eq_empty_of_measure_zero** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An open null set w.r.t. an `IsOpenPosMeasure` is empty.
-/
theorem _root_.IsOpen.eq_empty_of_measure_zero (hU : IsOpen U) (h₀ : μ U = 0) : U = ∅ :=
  (hU.measure_eq_zero_iff μ).mp h₀

set_option backward.isDefEq.respectTransparency false in
/-
**MeasureTheory.Measure._root_.IsClosed.ae_eq_univ_iff_eq** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsClosed.ae_eq_univ_iff_eq (hF : IsClosed F) :
    F =ᵐ[μ] univ ↔ F = univ := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h]⟩
  rwa [ae_eq_univ, hF.isOpen_compl.measure_eq_zero_iff μ, compl_empty_iff] at h
/-
**MeasureTheory.Measure._root_.IsClosed.measure_eq_univ_iff_eq** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsClosed.measure_eq_univ_iff_eq [OpensMeasurableSpace X] [IsFiniteMeasure μ]
    (hF : IsClosed F) :
    μ F = μ univ ↔ F = univ := by
  rw [← ae_eq_univ_iff_measure_eq hF.measurableSet.nullMeasurableSet, hF.ae_eq_univ_iff_eq]
/-
**MeasureTheory.Measure._root_.IsClosed.measure_eq_one_iff_eq_univ** 是 Mathlib 中
的一个定理，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsClosed.measure_eq_one_iff_eq_univ [OpensMeasurableSpace X] [IsProbabilityMeasure μ]
    (hF : IsClosed F) :
    μ F = 1 ↔ F = univ := by
  rw [← measure_univ (μ := μ), hF.measure_eq_univ_iff_eq]

/-- A null set has empty interior. -/
/-
**MeasureTheory.Measure.interior_eq_empty_of_null** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.Measure`。
形式化陈述：interior_eq_empty_of_null (hs : μ s = 0) : interior s = ∅
参数：hs : μ s = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.eq_empty_of_measure_zero`：∀ {X : Type u_1} [inst : TopologicalSpa
ce X] {m : MeasurableSpace X} {μ : MeasureTheory.Measure X} [μ.IsOpenPosMeasure]
   {U : Set X}, IsOpe…
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `MeasureTheory.measure_mono_null`：measure_mono_null (h : s subseteq t) (h
t : μ t = 0) : μ s = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s

--- 原说明 ---
A null set has empty interior.
-/
theorem interior_eq_empty_of_null (hs : μ s = 0) : interior s = ∅ :=
  isOpen_interior.eq_empty_of_measure_zero <| measure_mono_null interior_subset hs

/-- A property satisfied almost everywhere is satisfied on a dense subset. -/
/-
**MeasureTheory.Measure.dense_of_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Mea
sure`。
形式化陈述：dense_of_ae {p : X -> Prop} (hp : forallᵐ x ∂μ, p x) : Dense {x | p x}
参数：hp : forallᵐ x ∂μ, p x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dense_iff_closure_eq`：dense_iff_closure_eq : Dense s ↔ closure s = univ
· 使用定理 `closure_eq_compl_interior_compl`：closure_eq_compl_interior_compl : closu
re s = (interior sᶜ)ᶜ
· 使用定理 `Set.compl_univ_iff`：compl_univ_iff {s : Set α} : sᶜ = univ ↔ s = ∅
· 使用定理 `MeasureTheory.Measure.interior_eq_empty_of_null`：interior_eq_empty_of_nu
ll (hs : μ s = 0) : interior s = ∅

--- 原说明 ---
A property satisfied almost everywhere is satisfied on a dense subset.
-/
theorem dense_of_ae {p : X → Prop} (hp : ∀ᵐ x ∂μ, p x) : Dense {x | p x} := by
  rw [dense_iff_closure_eq, closure_eq_compl_interior_compl, compl_univ_iff]
  exact μ.interior_eq_empty_of_null hp

/-- If two functions are a.e. equal on an open set and are continuous on this set, then they are
equal on this set. -/
/-
**MeasureTheory.Measure.eqOn_open_of_ae_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Measure`。
形式化陈述：eqOn_open_of_ae_eq {f g : X -> Y} (h : f =ᵐ[μ.restrict U] g) (hU : IsOpen 
U) (hf : ContinuousOn f U) (hg : ContinuousOn g U) : EqOn f g U
参数：h : f =ᵐ[μ.restrict U] g；hU : IsOpen U；hf : ContinuousOn f U；hg : ContinuousO
n g U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_imp_of_ae_restrict`：ae_imp_of_ae_restrict {s : Set α} {
p : α -> Prop} (h : forallᵐ x ∂μ.restrict s, p x) : forallᵐ x ∂μ, x in s -> p x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isOpen_iff_mem_nhds`：isOpen_iff_mem_nhds : IsOpen s ↔ forall x in s, s i
n 𝓝 x
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.Tendsto.prodMk_nhds`：Filter.Tendsto.prodMk_nhds {γ} {x : X} {y : 
Y} {f : Filter γ} {mx : γ -> X} {my : γ -> Y} (hx : Tendsto mx f (𝓝 x)) (hy : Te
ndsto my f (𝓝 y)…
· 使用定理 `ContinuousOn.continuousAt`：ContinuousOn.continuousAt (h : ContinuousOn f
 s) (hx : s in 𝓝 x) : ContinuousAt f x
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `isClosed_diagonal`：isClosed_diagonal [T2Space X] : IsClosed (diagonal X)
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `IsOpen.eq_empty_of_measure_zero`：∀ {X : Type u_1} [inst : TopologicalSpa
ce X] {m : MeasurableSpace X} {μ : MeasureTheory.Measure X} [μ.IsOpenPosMeasure]
   {U : Set X}, IsOpe…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a

--- 原说明 ---
If two functions are a.e. equal on an open set and are continuous on this set, t
hen they are
equal on this set.
-/
theorem eqOn_open_of_ae_eq {f g : X → Y} (h : f =ᵐ[μ.restrict U] g) (hU : IsOpen U)
    (hf : ContinuousOn f U) (hg : ContinuousOn g U) : EqOn f g U := by
  replace h := ae_imp_of_ae_restrict h
  simp only [ae_iff, Classical.not_imp] at h
  have : IsOpen (U ∩ { a | f a ≠ g a }) := by
    refine isOpen_iff_mem_nhds.mpr fun a ha => inter_mem (hU.mem_nhds ha.1) ?_
    rcases ha with ⟨ha : a ∈ U, ha' : (f a, g a) ∈ (diagonal Y)ᶜ⟩
    exact
      (hf.continuousAt (hU.mem_nhds ha)).prodMk_nhds (hg.continuousAt (hU.mem_nhds ha))
        (isClosed_diagonal.isOpen_compl.mem_nhds ha')
  replace := (this.eq_empty_of_measure_zero h).le
  exact fun x hx => Classical.not_not.1 fun h => this ⟨hx, h⟩

/-- If two continuous functions are a.e. equal, then they are equal. -/
/-
**MeasureTheory.Measure.eq_of_ae_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Mea
sure`。
形式化陈述：eq_of_ae_eq {f g : X -> Y} (h : f =ᵐ[μ] g) (hf : Continuous f) (hg : Conti
nuous g) : f = g
参数：h : f =ᵐ[μ] g；hf : Continuous f；hg : Continuous g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.eqOn_open_of_ae_eq`：eqOn_open_of_ae_eq {f g : X ->
 Y} (h : f =ᵐ[μ.restrict U] g) (hU : IsOpen U) (hf : ContinuousOn f U) (hg : Con
tinuousOn g U) : EqOn f g U
· 使用定理 `MeasureTheory.ae_restrict_of_ae`：ae_restrict_of_ae {s : Set α} {p : α ->
 Prop} (h : forallᵐ x ∂μ, p x) : forallᵐ x ∂μ.restrict s, p x
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `trivial`：True

--- 原说明 ---
If two continuous functions are a.e. equal, then they are equal.
-/
theorem eq_of_ae_eq {f g : X → Y} (h : f =ᵐ[μ] g) (hf : Continuous f) (hg : Continuous g) : f = g :=
  suffices EqOn f g univ from funext fun _ => this trivial
  eqOn_open_of_ae_eq (ae_restrict_of_ae h) isOpen_univ hf.continuousOn hg.continuousOn
/-
**MeasureTheory.Measure.eqOn_of_ae_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.M
easure`。
形式化陈述：eqOn_of_ae_eq {f g : X -> Y} (h : f =ᵐ[μ.restrict s] g) (hf : ContinuousOn
 f s) (hg : ContinuousOn g s) (hU : s subseteq closure (interior s)) : EqOn f g 
s
参数：h : f =ᵐ[μ.restrict s] g；hf : ContinuousOn f s；hg : ContinuousOn g s；hU : s s
ubseteq closure (interior s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `Set.EqOn.of_subset_closure`：Set.EqOn.of_subset_closure [T2Space Y] {s t 
: Set X} {f g : X -> Y} (h : EqOn f g s) (hf : ContinuousOn f t) (hg : Continuou
sOn g t) (hst : …
· 使用定理 `MeasureTheory.Measure.eqOn_open_of_ae_eq`：eqOn_open_of_ae_eq {f g : X ->
 Y} (h : f =ᵐ[μ.restrict U] g) (hU : IsOpen U) (hf : ContinuousOn f U) (hg : Con
tinuousOn g U) : EqOn f g U
· 使用定理 `MeasureTheory.ae_restrict_of_ae_restrict_of_subset`：ae_restrict_of_ae_re
strict_of_subset {s t : Set α} {p : α -> Prop} (hst : s subseteq t) (h : forallᵐ
 x ∂μ.restrict t, p x) : forallᵐ x ∂μ.re…
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
-/
theorem eqOn_of_ae_eq {f g : X → Y} (h : f =ᵐ[μ.restrict s] g) (hf : ContinuousOn f s)
    (hg : ContinuousOn g s) (hU : s ⊆ closure (interior s)) : EqOn f g s :=
  have : interior s ⊆ s := interior_subset
  (eqOn_open_of_ae_eq (ae_restrict_of_ae_restrict_of_subset this h) isOpen_interior (hf.mono this)
        (hg.mono this)).of_subset_closure
    hf hg this hU

variable (μ) in
/-
**MeasureTheory.Measure._root_.Continuous.ae_eq_iff_eq** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Continuous.ae_eq_iff_eq {f g : X → Y} (hf : Continuous f) (hg : Continuous g) :
    f =ᵐ[μ] g ↔ f = g :=
  ⟨fun h => eq_of_ae_eq h hf hg, fun h => h ▸ EventuallyEq.rfl⟩
/-
**MeasureTheory.Measure._root_.Continuous.isOpenPosMeasure_map** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Continuous.isOpenPosMeasure_map [OpensMeasurableSpace X]
    {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    {f : X → Z} (hf : Continuous f) (hf_surj : Function.Surjective f) :
    (Measure.map f μ).IsOpenPosMeasure := by
  refine ⟨fun U hUo hUne => ?_⟩
  rw [Measure.map_apply hf.measurable hUo.measurableSet]
  exact (hUo.preimage hf).measure_ne_zero μ (hf_surj.nonempty_preimage.mpr hUne)
/-
**MeasureTheory.Measure.IsOpenPosMeasure.comap** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.Measure.IsOpenPosMeasure`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] {m : MeasurableSpace X} [Bore
lSpace X] {Z : Type u_3}   [inst_2 : TopologicalSpace Z] {mZ : MeasurableSpace Z
} [BorelSpace Z] (μ : MeasureTheory.Measure Z)   [μ.IsOpenPosMeasure] {f : X → Z
}, Topology.IsOpenEmbedding f → (MeasureTheory.Measure.comap f μ).IsOpenPosMeasu
re
参数：μ : MeasureTheory.Measure Z；MeasureTheory.Measure.comap f μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasurableEmbedding.comap_apply`：comap_apply (μ : Measure β) (s : Set α)
 : comap f μ s = μ (f '' s)
· 使用定理 `Topology.IsOpenEmbedding.measurableEmbedding`：∀ {α : Type u_1} {β : Type
 u_2} [inst : TopologicalSpace α] [mα : MeasurableSpace α] [BorelSpace α]   [mβ 
: TopologicalSpace β] [inst_2 : Me…
· 使用定理 `MeasureTheory.Measure.IsOpenPosMeasure.open_pos`：∀ {X : Type u_1} {inst 
: TopologicalSpace X} {m : MeasurableSpace X} {μ : MeasureTheory.Measure X}   [s
elf : μ.IsOpenPosMeasure] (U : Set X)…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Topology.IsOpenEmbedding.isOpen_iff_image_isOpen`：∀ {X : Type u_1} {Y : 
Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],
   Topology.IsOpenEmbedding f → ∀ {s :…
· 使用定理 `Set.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set
 α}, s.Nonempty → (f '' s).Nonempty
-/
protected theorem IsOpenPosMeasure.comap [BorelSpace X]
    {Z : Type*} [TopologicalSpace Z] {mZ : MeasurableSpace Z} [BorelSpace Z]
    (μ : Measure Z) [IsOpenPosMeasure μ] {f : X → Z} (hf : IsOpenEmbedding f) :
    (μ.comap f).IsOpenPosMeasure where
  open_pos U hU Une := by
    rw [hf.measurableEmbedding.comap_apply]
    exact IsOpenPosMeasure.open_pos _ (hf.isOpen_iff_image_isOpen.mp hU) (Une.image f)

end Basic

section LinearOrder

variable {X Y : Type*} [TopologicalSpace X] [LinearOrder X] [OrderTopology X]
  {m : MeasurableSpace X} [TopologicalSpace Y] [T2Space Y] (μ : Measure X) [IsOpenPosMeasure μ]

/-
**MeasureTheory.Measure.measure_Ioi_pos** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.Measure`。
形式化陈述：measure_Ioi_pos [NoMaxOrder X] (a : X) : 0 < μ (Ioi a)
参数：a : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.measure_pos`：∀ {X : Type u_1} [inst : TopologicalSpace X] {m : Me
asurableSpace X} (μ : MeasureTheory.Measure X) [μ.IsOpenPosMeasure]   {U : Set X
}, IsOpe…
· 使用定理 `isOpen_Ioi`：isOpen_Ioi : IsOpen (Ioi a)
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `Set.nonempty_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {a : α} [NoMaxOrd
er α], (Set.Ioi a).Nonempty
-/
theorem measure_Ioi_pos [NoMaxOrder X] (a : X) : 0 < μ (Ioi a) :=
  isOpen_Ioi.measure_pos μ nonempty_Ioi
/-
**MeasureTheory.Measure.measure_Iio_pos** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.Measure`。
形式化陈述：measure_Iio_pos [NoMinOrder X] (a : X) : 0 < μ (Iio a)
参数：a : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.measure_pos`：∀ {X : Type u_1} [inst : TopologicalSpace X] {m : Me
asurableSpace X} (μ : MeasureTheory.Measure X) [μ.IsOpenPosMeasure]   {U : Set X
}, IsOpe…
· 使用定理 `isOpen_Iio`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : LinearO
rder α] [ClosedIciTopology α] {a : α}, IsOpen (Set.Iio a)
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `Set.nonempty_Iio`：nonempty_Iio [NoMinOrder α] : (Iio a).Nonempty
-/
theorem measure_Iio_pos [NoMinOrder X] (a : X) : 0 < μ (Iio a) :=
  isOpen_Iio.measure_pos μ nonempty_Iio
/-
**MeasureTheory.Measure.measure_Ioo_pos** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.Measure`。
形式化陈述：measure_Ioo_pos [DenselyOrdered X] {a b : X} : 0 < μ (Ioo a b) ↔ a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `IsOpen.measure_pos_iff`：∀ {X : Type u_1} [inst : TopologicalSpace X] {m 
: MeasurableSpace X} (μ : MeasureTheory.Measure X) [μ.IsOpenPosMeasure]   {U : S
et X}, IsOpe…
· 使用定理 `isOpen_Ioo`：isOpen_Ioo : IsOpen (Ioo a b)
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `Set.nonempty_Ioo`：nonempty_Ioo [DenselyOrdered α] : (Ioo a b).Nonempty ↔
 a < b
-/
theorem measure_Ioo_pos [DenselyOrdered X] {a b : X} : 0 < μ (Ioo a b) ↔ a < b :=
  (isOpen_Ioo.measure_pos_iff μ).trans nonempty_Ioo
/-
**MeasureTheory.Measure.measure_Ioo_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Measure`。
形式化陈述：measure_Ioo_eq_zero [DenselyOrdered X] {a b : X} : μ (Ioo a b) = 0 ↔ b <= 
a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `IsOpen.measure_eq_zero_iff`：∀ {X : Type u_1} [inst : TopologicalSpace X]
 {m : MeasurableSpace X} (μ : MeasureTheory.Measure X) [μ.IsOpenPosMeasure]   {U
 : Set X}, IsOpe…
· 使用定理 `isOpen_Ioo`：isOpen_Ioo : IsOpen (Ioo a b)
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `Set.Ioo_eq_empty_iff`：Ioo_eq_empty_iff [DenselyOrdered α] : Ioo a b = ∅ 
↔ ¬a < b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
-/
theorem measure_Ioo_eq_zero [DenselyOrdered X] {a b : X} : μ (Ioo a b) = 0 ↔ b ≤ a :=
  (isOpen_Ioo.measure_eq_zero_iff μ).trans (Ioo_eq_empty_iff.trans not_lt)
/-
**MeasureTheory.Measure.eqOn_Ioo_of_ae_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.Measure`。
形式化陈述：eqOn_Ioo_of_ae_eq {a b : X} {f g : X -> Y} (hfg : f =ᵐ[μ.restrict (Ioo a b
)] g) (hf : ContinuousOn f (Ioo a b)) (hg : ContinuousOn g (Ioo a b)) : EqOn f g
 (Ioo a b)
参数：hfg : f =ᵐ[μ.restrict (Ioo a b)] g；hf : ContinuousOn f (Ioo a b)；hg : Continu
ousOn g (Ioo a b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.eqOn_of_ae_eq`：eqOn_of_ae_eq {f g : X -> Y} (h : f
 =ᵐ[μ.restrict s] g) (hf : ContinuousOn f s) (hg : ContinuousOn g s) (hU : s sub
seteq closure (interior s…
· 使用定理 `Ioo_subset_closure_interior`：Ioo_subset_closure_interior : Ioo a b subse
teq closure (interior (Ioo a b))
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
-/
theorem eqOn_Ioo_of_ae_eq {a b : X} {f g : X → Y} (hfg : f =ᵐ[μ.restrict (Ioo a b)] g)
    (hf : ContinuousOn f (Ioo a b)) (hg : ContinuousOn g (Ioo a b)) : EqOn f g (Ioo a b) :=
  eqOn_of_ae_eq hfg hf hg Ioo_subset_closure_interior
/-
**MeasureTheory.Measure.eqOn_Ioc_of_ae_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.Measure`。
形式化陈述：eqOn_Ioc_of_ae_eq [DenselyOrdered X] {a b : X} {f g : X -> Y} (hfg : f =ᵐ[
μ.restrict (Ioc a b)] g) (hf : ContinuousOn f (Ioc a b)) (hg : ContinuousOn g (I
oc a b)) : EqOn f g (Ioc a b)
参数：hfg : f =ᵐ[μ.restrict (Ioc a b)] g；hf : ContinuousOn f (Ioc a b)；hg : Continu
ousOn g (Ioc a b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.eqOn_of_ae_eq`：eqOn_of_ae_eq {f g : X -> Y} (h : f
 =ᵐ[μ.restrict s] g) (hf : ContinuousOn f s) (hg : ContinuousOn g s) (hU : s sub
seteq closure (interior s…
· 使用定理 `Ioc_subset_closure_interior`：Ioc_subset_closure_interior (a b : α) : Ioc
 a b subseteq closure (interior (Ioc a b))
-/
theorem eqOn_Ioc_of_ae_eq [DenselyOrdered X] {a b : X} {f g : X → Y}
    (hfg : f =ᵐ[μ.restrict (Ioc a b)] g) (hf : ContinuousOn f (Ioc a b))
    (hg : ContinuousOn g (Ioc a b)) : EqOn f g (Ioc a b) :=
  eqOn_of_ae_eq hfg hf hg (Ioc_subset_closure_interior _ _)
/-
**MeasureTheory.Measure.eqOn_Ico_of_ae_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.Measure`。
形式化陈述：eqOn_Ico_of_ae_eq [DenselyOrdered X] {a b : X} {f g : X -> Y} (hfg : f =ᵐ[
μ.restrict (Ico a b)] g) (hf : ContinuousOn f (Ico a b)) (hg : ContinuousOn g (I
co a b)) : EqOn f g (Ico a b)
参数：hfg : f =ᵐ[μ.restrict (Ico a b)] g；hf : ContinuousOn f (Ico a b)；hg : Continu
ousOn g (Ico a b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.eqOn_of_ae_eq`：eqOn_of_ae_eq {f g : X -> Y} (h : f
 =ᵐ[μ.restrict s] g) (hf : ContinuousOn f s) (hg : ContinuousOn g s) (hU : s sub
seteq closure (interior s…
· 使用定理 `Ico_subset_closure_interior`：Ico_subset_closure_interior (a b : α) : Ico
 a b subseteq closure (interior (Ico a b))
-/
theorem eqOn_Ico_of_ae_eq [DenselyOrdered X] {a b : X} {f g : X → Y}
    (hfg : f =ᵐ[μ.restrict (Ico a b)] g) (hf : ContinuousOn f (Ico a b))
    (hg : ContinuousOn g (Ico a b)) : EqOn f g (Ico a b) :=
  eqOn_of_ae_eq hfg hf hg (Ico_subset_closure_interior _ _)
/-
**MeasureTheory.Measure.eqOn_Icc_of_ae_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.Measure`。
形式化陈述：eqOn_Icc_of_ae_eq [DenselyOrdered X] {a b : X} (hne : a != b) {f g : X -> 
Y} (hfg : f =ᵐ[μ.restrict (Icc a b)] g) (hf : ContinuousOn f (Icc a b)) (hg : Co
ntinuousOn g (Icc a b)) : EqOn f g (Icc a b)
参数：hne : a != b；hfg : f =ᵐ[μ.restrict (Icc a b)] g；hf : ContinuousOn f (Icc a b)
；hg : ContinuousOn g (Icc a b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.eqOn_of_ae_eq`：eqOn_of_ae_eq {f g : X -> Y} (h : f
 =ᵐ[μ.restrict s] g) (hf : ContinuousOn f s) (hg : ContinuousOn g s) (hU : s sub
seteq closure (interior s…
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `closure_interior_Icc`：closure_interior_Icc {a b : α} (h : a != b) : clos
ure (interior (Icc a b)) = Icc a b
-/
theorem eqOn_Icc_of_ae_eq [DenselyOrdered X] {a b : X} (hne : a ≠ b) {f g : X → Y}
    (hfg : f =ᵐ[μ.restrict (Icc a b)] g) (hf : ContinuousOn f (Icc a b))
    (hg : ContinuousOn g (Icc a b)) : EqOn f g (Icc a b) :=
  eqOn_of_ae_eq hfg hf hg (closure_interior_Icc hne).symm.subset

end LinearOrder

end Measure

end MeasureTheory

open MeasureTheory MeasureTheory.Measure

namespace Metric

variable {X : Type*} [PseudoMetricSpace X] {m : MeasurableSpace X} (μ : Measure X)
  [IsOpenPosMeasure μ]

/-
**Metric.measure_ball_pos** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：measure_ball_pos (x : X) {r : Real} (hr : 0 < r) : 0 < μ (ball x r)
参数：x : X；hr : 0 < r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.measure_pos`：∀ {X : Type u_1} [inst : TopologicalSpace X] {m : Me
asurableSpace X} (μ : MeasureTheory.Measure X) [μ.IsOpenPosMeasure]   {U : Set X
}, IsOpe…
· 使用定理 `Metric.isOpen_ball`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x : α} 
{ε : ℝ}, IsOpen (Metric.ball x ε)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.nonempty_ball`：nonempty_ball : (ball x ε).Nonempty ↔ 0 < ε
-/
theorem measure_ball_pos (x : X) {r : ℝ} (hr : 0 < r) : 0 < μ (ball x r) :=
  isOpen_ball.measure_pos μ (nonempty_ball.2 hr)

/-- See also `Metric.measure_closedBall_pos_iff`. -/
/-
**Metric.measure_closedBall_pos** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：measure_closedBall_pos (x : X) {r : Real} (hr : 0 < r) : 0 < μ (closedBall
 x r)
参数：x : X；hr : 0 < r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Metric.measure_ball_pos`：measure_ball_pos (x : X) {r : Real} (hr : 0 < r
) : 0 < μ (ball x r)
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Metric.ball_subset_closedBall`：ball_subset_closedBall : ball x ε subsete
q closedBall x ε

--- 原说明 ---
See also `Metric.measure_closedBall_pos_iff`.
-/
theorem measure_closedBall_pos (x : X) {r : ℝ} (hr : 0 < r) : 0 < μ (closedBall x r) :=
  (measure_ball_pos μ x hr).trans_le (measure_mono ball_subset_closedBall)
/-
**Metric.measure_closedBall_pos_iff** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：∀ {X : Type u_2} [inst : MetricSpace X] {m : MeasurableSpace X} (μ : Measu
reTheory.Measure X) [μ.IsOpenPosMeasure]   [MeasureTheory.NullSingletonClass μ] 
{x : X} {r : ℝ}, 0 < μ (Metric.closedBall x r) ↔ 0 < r
参数：μ : MeasureTheory.Measure X；Metric.closedBall x r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Subsingleton.measure_zero`：∀ {α : Type u_1} {m0 : MeasurableSpace α}
 {s : Set α},   s.Subsingleton → ∀ (μ : MeasureTheory.Measure α) [MeasureTheory.
NullSingletonClass …
· 使用定理 `Metric.subsingleton_closedBall`：subsingleton_closedBall (x : γ) {r : Rea
l} (hr : r <= 0) : (closedBall x r).Subsingleton
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Metric.measure_closedBall_pos`：measure_closedBall_pos (x : X) {r : Real}
 (hr : 0 < r) : 0 < μ (closedBall x r)
-/
@[simp] lemma measure_closedBall_pos_iff {X : Type*} [MetricSpace X] {m : MeasurableSpace X}
    (μ : Measure X) [IsOpenPosMeasure μ] [NullSingletonClass μ] {x : X} {r : ℝ} :
    0 < μ (closedBall x r) ↔ 0 < r := by
  refine ⟨fun h ↦ ?_, measure_closedBall_pos μ x⟩
  contrapose! h
  rw [(subsingleton_closedBall x h).measure_zero μ]

end Metric

namespace Metric

variable {X : Type*} [PseudoEMetricSpace X] {m : MeasurableSpace X} (μ : Measure X)
  [IsOpenPosMeasure μ]

/-
**Metric.measure_eball_pos** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：measure_eball_pos (x : X) {r : Real>=0∞} (hr : r != 0) : 0 < μ (eball x r)
参数：x : X；hr : r != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.measure_pos`：∀ {X : Type u_1} [inst : TopologicalSpace X] {m : Me
asurableSpace X} (μ : MeasureTheory.Measure X) [μ.IsOpenPosMeasure]   {U : Set X
}, IsOpe…
· 使用定理 `Metric.isOpen_eball`：∀ {α : Type u} [inst : PseudoEMetricSpace α] {x : α
} {ε : ENNReal}, IsOpen (Metric.eball x ε)
· 使用定理 `Metric.mem_eball_self`：mem_eball_self (h : 0 < ε) : x in eball x ε
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
-/
theorem measure_eball_pos (x : X) {r : ℝ≥0∞} (hr : r ≠ 0) : 0 < μ (eball x r) :=
  isOpen_eball.measure_pos μ ⟨x, mem_eball_self hr.bot_lt⟩
/-
**Metric.measure_closedEBall_pos** 是 Mathlib 中的一个定理，位于命名空间 `Metric`。
形式化陈述：measure_closedEBall_pos (x : X) {r : Real>=0∞} (hr : r != 0) : 0 < μ (clos
edEBall x r)
参数：x : X；hr : r != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Metric.measure_eball_pos`：measure_eball_pos (x : X) {r : Real>=0∞} (hr :
 r != 0) : 0 < μ (eball x r)
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Metric.eball_subset_closedEBall`：eball_subset_closedEBall : eball x ε su
bseteq closedEBall x ε
-/
theorem measure_closedEBall_pos (x : X) {r : ℝ≥0∞} (hr : r ≠ 0) : 0 < μ (closedEBall x r) :=
  (measure_eball_pos μ x hr).trans_le (measure_mono eball_subset_closedEBall)

end Metric

@[deprecated (since := "2026-01-24")]
alias EMetric.measure_ball_pos := Metric.measure_eball_pos

@[deprecated (since := "2026-01-24")]
alias EMetric.measure_closedBall_pos := Metric.measure_closedEBall_pos

section MeasureZero
/-! ## Meagre sets and measure zero
In general, neither of meagre and measure zero implies the other.
- The set of Liouville numbers is a Lebesgue measure zero subset of ℝ, but is not meagre.
  (In fact, its complement is meagre. See `Real.disjoint_residual_ae`.)

- The complement of the set of Liouville numbers in $[0,1]$ is meagre and has measure 1.
  For another counterexample, for all $α ∈ (0,1)$, there is a generalised Cantor set $C ⊆ [0,1]$
  of measure `α`. Cantor sets are nowhere dense (hence meagre). Taking a countable union of
  fat Cantor sets whose measure approaches 1 even yields a meagre set of measure 1.

However, with respect to a measure which is positive on non-empty open sets, *closed* measure
zero sets are nowhere dense and σ-compact measure zero sets in a Hausdorff space are meagre.
-/

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] {s : Set X}
  {μ : Measure X} [IsOpenPosMeasure μ]

/-- A *closed* measure zero subset is nowhere dense. (Closedness is required: for instance, the
rational numbers are countable (thus have measure zero), but are dense (hence not nowhere dense).)
-/
/-
**IsNowhereDense.of_isClosed_null** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsNowhereDense.of_isClosed_null (h₁s : IsClosed s) (h₂s : μ s = 0) : IsNow
hereDense s
参数：h₁s : IsClosed s；h₂s : μ s = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `IsClosed.isNowhereDense_iff`：IsClosed.isNowhereDense_iff {s : Set X} (hs
 : IsClosed s) : IsNowhereDense s ↔ interior s = ∅
· 使用定理 `MeasureTheory.Measure.interior_eq_empty_of_null`：interior_eq_empty_of_nu
ll (hs : μ s = 0) : interior s = ∅

--- 原说明 ---
A *closed* measure zero subset is nowhere dense. (Closedness is required: for in
stance, the
rational numbers are countable (thus have measure zero), but are dense (hence no
t nowhere dense).)
-/
lemma IsNowhereDense.of_isClosed_null (h₁s : IsClosed s) (h₂s : μ s = 0) :
    IsNowhereDense s := h₁s.isNowhereDense_iff.mpr (interior_eq_empty_of_null h₂s)

/-- A σ-compact measure zero subset is meagre.
(More generally, every Fσ set of measure zero is meagre.) -/
/-
**IsMeagre.of_isSigmaCompact_null** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsMeagre.of_isSigmaCompact_null [T2Space X] (h₁s : IsSigmaCompact s) (h₂s 
: μ s = 0) : IsMeagre s
参数：h₁s : IsSigmaCompact s；h₂s : μ s = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_mono_null`：measure_mono_null (h : s subseteq t) (h
t : μ t = 0) : μ s = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.subset_iUnion`：subset_iUnion : forall (s : ι -> Set β) (i : ι), s i 
subseteq ⋃ i, s i
· 使用引理 `IsNowhereDense.of_isClosed_null`：IsNowhereDense.of_isClosed_null (h₁s : 
IsClosed s) (h₂s : μ s = 0) : IsNowhereDense s
· 使用定理 `IsCompact.isClosed`：IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsC
ompact s) : IsClosed s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `isMeagre_iff_countable_union_isNowhereDense`：isMeagre_iff_countable_unio
n_isNowhereDense {s : Set X} : IsMeagre s ↔ exists S : Set (Set X), (forall t in
 S, IsNowhereDense t) ∧ S.Countab…
· 使用定理 `Set.countable_range`：countable_range [Countable ι] (f : ι -> β) : (range
 f).Countable
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
A σ-compact measure zero subset is meagre.
(More generally, every Fσ set of measure zero is meagre.)
-/
lemma IsMeagre.of_isSigmaCompact_null [T2Space X] (h₁s : IsSigmaCompact s) (h₂s : μ s = 0) :
    IsMeagre s := by
  rcases h₁s with ⟨K, hcompact, hcover⟩
  have h (n : ℕ) : IsNowhereDense (K n) := by
    have : μ (K n) = 0 := measure_mono_null (hcover ▸ subset_iUnion K n) h₂s
    exact .of_isClosed_null (hcompact n).isClosed this
  rw [isMeagre_iff_countable_union_isNowhereDense]
  exact ⟨range K, fun t ⟨n, hn⟩ ↦ hn ▸ h n, countable_range K, hcover.symm.subset⟩

end MeasureZero

